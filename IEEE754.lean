
/-
  FPUModel.lean
  =============
  IEEE 754 floating-point model for hardware verification.

  Architecture (matches diagram):

    BitVec Input(s) → Decode → DecodedFloat → Op → PreciseResult → Round → RoundedFloat → Encode → BitVec Output

  The Decode/Encode steps are format-specific (§6 F32, §8 F64).
  Everything else — exact arithmetic (§4) and rounding (§5) — is shared across all formats.

  Structure
  ─────────
  §1   Rounding modes
  §2   DecodedFloat — common "Rational Operand" representation
  §3   FPFormat — format descriptor (parameterises rounding & encoding)
  §4   Common exact arithmetic (addExact, mulExact, divExact, fmaExact, sqrtExact)
  §5   Common rounding (roundTo)
  §6   F32 — format-specific bitvector layer (decode, encode, fields, constants, comparison)
  §7   F32 — top-level composed operations (fadd, fmul, fdiv, fma, fsub)
  §8   F64 — format-specific bitvector layer
  §9   F64 — top-level composed operations
  §10  Conversions (F32 ↔ F64, F32 ↔ Int)
  §11  Verification properties
  §12  Hardware Oracle Interface (cocotb / CVDP integration)

  Representation
  ──────────────
  DecodedFloat.finite sign exp sig  ≡  (-1)^sign × sig × 2^exp   (sig : Nat, arbitrary precision)
  F32 = BitVec 32   (s=31, e=30:23, m=22:0)
  F64 = BitVec 64   (s=63, e=62:52, m=51:0)
-/

import Std.Tactic.BVDecide
open BitVec


-- ─────────────────────────────────────────────────────────────────────────────
-- §1  Rounding Modes
-- ─────────────────────────────────────────────────────────────────────────────

inductive RoundMode where
  | RNE   -- Round to Nearest, ties to Even   (IEEE default)
  | RTZ   -- Round Toward Zero                (truncation)
  | RDN   -- Round Down (toward -∞)
  | RUP   -- Round Up   (toward +∞)
  | RMM   -- Round to Nearest, ties away from zero
  | DYN   -- Dynamic rounding (placeholder)
  deriving Repr, BEq, DecidableEq

def classifyRounding (x : UInt8) : RoundMode :=
  match x with
  | 0 => .RNE
  | 1 => .RTZ
  | 2 => .RDN
  | 3 => .RUP
  | 4 => .RMM
  | _ => .DYN


-- ─────────────────────────────────────────────────────────────────────────────
-- §2  DecodedFloat — common "Rational Operand" representation
-- ─────────────────────────────────────────────────────────────────────────────

/-- Format-agnostic exact representation of a floating-point value.
    `finite sign exp sig` means (-1)^sign × sig × 2^exp, where sig : Nat (arbitrary precision).
    For a normal F32 with unbiased exponent e and 24-bit significand s:
      exp = e - 23,  sig = s  -/
inductive DecodedFloat where
  | finite (sign : Bool) (exp : Int) (sig : Nat) : DecodedFloat
  | inf    (sign : Bool) : DecodedFloat
  | nan    : DecodedFloat
  deriving Repr

namespace DecodedFloat

def isNaN   : DecodedFloat → Bool | .nan     => true | _ => false
def isInf   : DecodedFloat → Bool | .inf _   => true | _ => false
def isFinite: DecodedFloat → Bool | .finite _ _ _ => true | _ => false
def isZero  : DecodedFloat → Bool | .finite _ _ 0 => true | _ => false

def dfSign  : DecodedFloat → Bool
  | .finite s _ _ => s
  | .inf s        => s
  | .nan          => false

end DecodedFloat


-- ─────────────────────────────────────────────────────────────────────────────
-- §3  FPFormat — format descriptor
-- ─────────────────────────────────────────────────────────────────────────────

/-- Describes a binary floating-point format (IEEE 754 style). -/
structure FPFormat where
  M    : Nat   -- mantissa field bits (e.g. 23 for F32, 52 for F64)
  E    : Nat   -- exponent field bits (e.g.  8 for F32, 11 for F64)
  bias : Nat   -- exponent bias = 2^(E-1) - 1

def f32Fmt : FPFormat := { M := 23, E := 8,  bias := 127  }
def f64Fmt : FPFormat := { M := 52, E := 11, bias := 1023 }


-- ─────────────────────────────────────────────────────────────────────────────
-- §3.5  Exception Flags (IEEE 754-2019 §7)
-- ─────────────────────────────────────────────────────────────────────────────

/-- The five IEEE 754 sticky exception flags.
    Each operation returns the flags it raised; accumulation across operations
    is the caller's responsibility (OR the sets together). -/
structure ExcFlags where
  invalidOp : Bool := false  -- §7.2  invalid operands → NaN from non-NaN inputs
  divByZero : Bool := false  -- §7.3  finite nonzero ÷ 0
  overflow  : Bool := false  -- §7.4  result magnitude → ∞  (always implies inexact)
  underflow : Bool := false  -- §7.5  result tiny and inexact (always implies inexact)
  inexact   : Bool := false  -- §7.6  result was rounded
  deriving Repr, BEq

namespace ExcFlags

/-- No flags raised. -/
def empty : ExcFlags := {}

/-- Combine two flag sets (bitwise OR — sticky semantics). -/
def merge (a b : ExcFlags) : ExcFlags :=
  { invalidOp := a.invalidOp || b.invalidOp
    divByZero := a.divByZero || b.divByZero
    overflow  := a.overflow  || b.overflow
    underflow := a.underflow || b.underflow
    inexact   := a.inexact   || b.inexact }

-- Single-flag smart constructors.
-- IEEE 754 §7.4 and §7.5 require that overflow/underflow always set inexact too.
def mkInvalidOp : ExcFlags := { invalidOp := true }
def mkDivByZero : ExcFlags := { divByZero := true }
def mkOverflow  : ExcFlags := { overflow  := true, inexact := true }
def mkUnderflow : ExcFlags := { underflow := true, inexact := true }
def mkInexact   : ExcFlags := { inexact   := true }

theorem mkOverflow_inexact  : ExcFlags.mkOverflow.inexact  := by decide
theorem mkUnderflow_inexact : ExcFlags.mkUnderflow.inexact := by decide

end ExcFlags


-- ─────────────────────────────────────────────────────────────────────────────
-- §4  Common exact arithmetic
-- ─────────────────────────────────────────────────────────────────────────────
--
-- These functions operate purely on DecodedFloat values.
-- They handle IEEE special-case rules and return mathematically exact results
-- (no rounding). Call roundTo (§5) afterwards to fit a target format.
-- ─────────────────────────────────────────────────────────────────────────────

/-- Integer square root: largest q such that q² ≤ x.
    Uses Newton's method; converges in O(log log x) iterations. -/
private def intSqrt (x : Nat) : Nat :=
  if x == 0 then 0
  else
    let rec go (est : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0     => est
      | f + 1 =>
        let next := (est + x / est) / 2
        if next >= est then est else go next f
    go (1 <<< (x.log2 / 2 + 1)) 256

/-- Find the position of the highest set bit (0-indexed from LSB).
    Returns 0 if no bit ≤ maxPos is set. -/
private def findLeadingBit (v : Nat) (maxPos : Nat) : Nat :=
  let rec go (p : Nat) : Nat :=
    match p with
    | 0     => 0
    | q + 1 => if v.testBit (q + 1) then (q + 1) else go q
  go maxPos

-- ── Exact addition / subtraction ─────────────────────────────────────────────

/-- Exact addition of two DecodedFloats.
    Returns the mathematically exact result and any exception flags raised.
    Special-case rules follow IEEE 754 §6. -/
def addExact (rm : RoundMode) (a b : DecodedFloat) : DecodedFloat × ExcFlags :=
  match a, b with
  | .nan, _ | _, .nan => (.nan, ExcFlags.empty)
  -- Inf + Inf: same sign → Inf, opposite sign → NaN (invalid operation §7.2)
  | .inf sa, .inf sb  =>
      if sa == sb then (.inf sa, ExcFlags.empty)
      else (.nan, ExcFlags.mkInvalidOp)
  | .inf s, _  => (.inf s, ExcFlags.empty)
  | _, .inf s  => (.inf s, ExcFlags.empty)
  | .finite sa ea siga, .finite sb eb sigb =>
    if siga == 0 && sigb == 0 then
      (.finite (sa && sb || (sa || sb) && rm == .RDN) 0 0, ExcFlags.empty)
    else if siga == 0 then (.finite sb eb sigb, ExcFlags.empty)
    else if sigb == 0 then (.finite sa ea siga, ExcFlags.empty)
    else
      let minExp := if ea <= eb then ea else eb
      let siga'' := siga <<< (ea - minExp).toNat
      let sigb'' := sigb <<< (eb - minExp).toNat
      let (resultSign, resultSig) :=
        if sa == sb then (sa, siga'' + sigb'')
        else if siga'' >= sigb'' then (sa, siga'' - sigb'')
        else (sb, sigb'' - siga'')
      if resultSig == 0 then
        (.finite (rm == .RDN) 0 0, ExcFlags.empty)
      else
        (.finite resultSign minExp resultSig, ExcFlags.empty)

-- ── Exact multiplication ──────────────────────────────────────────────────────

/-- Exact multiplication of two DecodedFloats.
    The product significand may be up to 2×M+2 bits wide (e.g. 48 bits for F32).
    Returns the exact result and any exception flags raised. -/
def mulExact (a b : DecodedFloat) : DecodedFloat × ExcFlags :=
  match a, b with
  | .nan, _ | _, .nan => (.nan, ExcFlags.empty)
  -- Inf × 0 = NaN (invalid operation §7.2)
  | .inf _,  .finite _ _ 0 => (.nan, ExcFlags.mkInvalidOp)
  | .finite _ _ 0, .inf _  => (.nan, ExcFlags.mkInvalidOp)
  -- Inf × nonzero = Inf
  | .inf sa, .inf sb        => (.inf (sa != sb), ExcFlags.empty)
  | .inf sa, .finite sb _ _ => (.inf (sa != sb), ExcFlags.empty)
  | .finite sa _ _, .inf sb => (.inf (sa != sb), ExcFlags.empty)
  -- finite × finite (exact product)
  | .finite sa ea siga, .finite sb eb sigb =>
    (.finite (sa != sb) (ea + eb) (siga * sigb), ExcFlags.empty)

-- ── Exact division ───────────────────────────────────────────────────────────

/-- Exact division of two DecodedFloats (with sufficient precision for rounding).
    We shift the dividend left by (M+3) guard bits before integer division
    so the quotient has enough fractional bits for correct rounding.
    `M` is the mantissa width of the *output* format (passed by roundTo). -/
private def divExactWith (extraBits : Nat) (a b : DecodedFloat) : DecodedFloat × ExcFlags :=
  match a, b with
  | .nan, _ | _, .nan => (.nan, ExcFlags.empty)
  -- Inf / Inf = NaN (invalid operation §7.2)
  | .inf _,  .inf _   => (.nan, ExcFlags.mkInvalidOp)
  -- 0 / 0 = NaN (invalid operation §7.2)
  | .finite _ _ 0, .finite _ _ 0 => (.nan, ExcFlags.mkInvalidOp)
  -- Inf / finite = Inf
  | .inf sa, .finite sb _ _ => (.inf (sa != sb), ExcFlags.empty)
  -- finite / Inf = 0
  | .finite sa _ _, .inf sb  => (.finite (sa != sb) 0 0, ExcFlags.empty)
  -- finite / 0 = Inf (division by zero §7.3)
  | .finite sa _ _, .finite sb _ 0 => (.inf (sa != sb), ExcFlags.mkDivByZero)
  -- 0 / finite = 0
  | .finite sa _ 0, .finite sb _ _ => (.finite (sa != sb) 0 0, ExcFlags.empty)
  -- general case: scale dividend to get extra fractional bits for rounding
  | .finite sa ea siga, .finite sb eb sigb =>
    let sOut    := sa != sb
    let scaledA := siga <<< extraBits
    let quot    := scaledA / sigb
    let rem     := scaledA % sigb
    -- Sticky bit: if remainder nonzero, preserve it in LSB of quotient
    let quot'   := if rem != 0 then quot ||| 1 else quot
    (.finite sOut (ea - eb - extraBits) quot', ExcFlags.empty)

def divExact (a b : DecodedFloat) : DecodedFloat × ExcFlags :=
  divExactWith 60 a b   -- 60 guard bits; roundTo will normalize

-- ── Exact fused multiply-add ──────────────────────────────────────────────────

/-- TRUE fused multiply-add: compute (a × b) + c with a single rounding.
    The product is kept exact before adding c, so no intermediate rounding occurs.
    Returns the exact pre-rounding result and any exception flags raised. -/
def fmaExact (rm : RoundMode) (a b c : DecodedFloat) : DecodedFloat × ExcFlags :=
  match a, b with
  | .nan, _ | _, .nan => (.nan, ExcFlags.empty)
  -- Inf × 0 invalid regardless of c (§7.2)
  | .inf _, .finite _ _ 0 | .finite _ _ 0, .inf _ => (.nan, ExcFlags.mkInvalidOp)
  | _ , _ =>
    let (prod, pf) := mulExact a b
    let (sum,  sf) := addExact rm prod c
    (sum, pf.merge sf)


-- ── Exact square root ─────────────────────────────────────────────────────────

/-- Exact square root with IEEE 754 special-case handling (§5.4.1, §6.3, §7.2).
    For finite non-negative inputs the significand is scaled by 4^60 before
    computing the integer square root, giving 60 guard bits for correct rounding.
    A sticky bit is set when the mathematical result is irrational (q² < sigScaled)
    so that roundTo can detect inexactness.
    Returns the exact pre-rounding result and any exception flags raised. -/
def sqrtExact (a : DecodedFloat) : DecodedFloat × ExcFlags :=
  match a with
  | .nan            => (.nan, ExcFlags.empty)
  | .inf false      => (.inf false, ExcFlags.empty)     -- √(+∞) = +∞
  | .inf true       => (.nan, ExcFlags.mkInvalidOp)     -- √(-∞) = NaN (§7.2)
  | .finite s _ 0   => (.finite s 0 0, ExcFlags.empty)  -- √(±0) = ±0  (§6.3)
  | .finite true _ _ => (.nan, ExcFlags.mkInvalidOp)    -- √(negative) = NaN (§7.2)
  | .finite false e sig =>
    -- Make exponent even: if e is odd absorb one factor of 2 into sig.
    -- (Int `%` uses truncating remainder, so `-3 % 2 = -1 ≠ 0` as expected.)
    let (e', sig') :=
      if e % 2 == 0 then (e, sig) else (e - 1, sig * 2)
    -- Scale by 4^60 so the integer sqrt has 60 guard bits.
    let extraBits  : Nat := 60
    let sigScaled  := sig' <<< (2 * extraBits)
    let q          := intSqrt sigScaled
    -- If q² < sigScaled the true result is irrational; sticky bit in LSB signals this.
    let q'         := if q * q < sigScaled then q ||| 1 else q
    (.finite false (e' / 2 - (extraBits : Int)) q', ExcFlags.empty)


-- ─────────────────────────────────────────────────────────────────────────────
-- §5  Common rounding
-- ─────────────────────────────────────────────────────────────────────────────

/-- Round an exact DecodedFloat to fit within format `fmt`.
    This is the "Round" box in the diagram.
    Returns both the rounded result and the exception flags raised:
    - overflow  (§7.4): finite input rounds to Inf
    - underflow (§7.5): result is subnormal/zero AND bits were dropped
    - inexact   (§7.6): any bits were dropped during rounding -/
def roundTo (fmt : FPFormat) (rm : RoundMode) (d : DecodedFloat) : DecodedFloat × ExcFlags :=
  match d with
  | .nan    => (.nan, ExcFlags.empty)
  | .inf s  => (.inf s, ExcFlags.empty)
  | .finite s _ 0 => (.finite s 0 0, ExcFlags.empty)
  | .finite s e sig =>
    let M    := fmt.M
    let bias := (fmt.bias : Int)
    let leadPos     := findLeadingBit sig (sig.log2 + 1)
    let expUnbiased : Int := e + leadPos
    let expMax : Int := (1 <<< fmt.E) - 2
    let expMin : Int := 1 - bias
    let biasedExp : Int := expUnbiased + bias
    if biasedExp >= expMax + 1 then
      -- overflow → Inf (overflow always implies inexact)
      (.inf s, ExcFlags.mkOverflow)
    else if biasedExp < 1 then
      -- subnormal or underflow range
      let subnormShift := (M : Int) - leadPos + (1 - biasedExp)
      if subnormShift < 0 then
        -- extreme underflow: all bits lost → zero
        (.finite s 0 0, ExcFlags.mkUnderflow)
      else
        let sh      := subnormShift.toNat
        let mask    := (1 <<< sh) - 1
        let dropped := sig &&& mask
        let half    := if sh > 0 then 1 <<< (sh - 1) else 0
        let trunc   := sig >>> sh
        let roundUp := match rm with
          | .RTZ => false
          | .RUP => !s && dropped != 0
          | .RDN =>  s && dropped != 0
          | .RMM => dropped >= half
          | .RNE =>
              if   dropped > half then true
              else if dropped < half then false
              else (trunc &&& 1) == 1
          | .DYN => false
        let sigOut := if roundUp then trunc + 1 else trunc
        -- underflow is raised when any bits were dropped (result is tiny and inexact)
        let flags  := if dropped != 0 then ExcFlags.mkUnderflow else ExcFlags.empty
        if sigOut >= (1 <<< M) then
          -- rounding of subnormal carried into minimum normal
          (.finite s (expMin - M) sigOut, flags)
        else
          (.finite s (expMin - M) sigOut, flags)
    else
      -- normal range
      let shift : Int := leadPos - M
      let (sigOut, anyDropped) :=
        if shift > 0 then
          let sh      := shift.toNat
          let mask    := (1 <<< sh) - 1
          let dropped := sig &&& mask
          let half    := 1 <<< (sh - 1)
          let trunc   := sig >>> sh
          let roundUp := match rm with
            | .RTZ => false
            | .RUP => !s && dropped != 0
            | .RDN =>  s && dropped != 0
            | .RMM => dropped >= half
            | .RNE =>
                if   dropped > half then true
                else if dropped < half then false
                else (trunc &&& 1) == 1
            | .DYN => false
          (if roundUp then trunc + 1 else trunc, dropped != 0)
        else
          (sig <<< (-shift).toNat, false)
      let (biasedExpFinal, sigFinal) :=
        if sigOut >= (1 <<< (M + 1)) then
          (biasedExp + 1, sigOut >>> 1)
        else
          (biasedExp, sigOut)
      if biasedExpFinal >= expMax + 1 then
        (.inf s, ExcFlags.mkOverflow)
      else
        (.finite s (biasedExpFinal - bias - M) sigFinal,
         if anyDropped then ExcFlags.mkInexact else ExcFlags.empty)


-- ─────────────────────────────────────────────────────────────────────────────
-- §6  F32 — Format-specific bitvector layer
-- ─────────────────────────────────────────────────────────────────────────────

/-- IEEE 754 single-precision float as a 32-bit vector. -/
abbrev F32 := BitVec 32

/-- IEEE 754 double-precision float as a 64-bit vector. -/
abbrev F64 := BitVec 64

namespace F32

-- ── Constants ────────────────────────────────────────────────────────────────
def SIGN_WIDTH  : Nat := 1
def EXP_WIDTH   : Nat := 8
def MANT_WIDTH  : Nat := 23
def BIAS        : Int := 127

-- ── Field extraction ─────────────────────────────────────────────────────────

/-- Extract the sign bit (bit 31). -/
def sign (f : F32) : Bool := f.getLsbD 31

/-- Extract the raw 8-bit biased exponent (bits 30:23). -/
def expRaw (f : F32) : BitVec 8 := (f >>> 23).truncate 8

/-- Extract the 23-bit mantissa field (bits 22:0). -/
def mantissa (f : F32) : BitVec 23 := f.truncate 23

/-- Unbiased exponent as an integer. -/
def expUnbiased (f : F32) : Int := ((expRaw f).toNat : Int) - BIAS

-- ── Field construction ───────────────────────────────────────────────────────

/-- Pack sign, raw exponent, and mantissa into a Float32. -/
def pack (s : Bool) (e : BitVec 8) (m : BitVec 23) : F32 :=
  let sB : BitVec 32 := if s then 1 <<< 31 else 0
  let eB : BitVec 32 := (e.zeroExtend 32) <<< 23
  let mB : BitVec 32 := m.zeroExtend 32
  sB ||| eB ||| mB

/-- Flip the sign bit. -/
def negate (f : F32) : F32 := f ^^^ (1 <<< 31)

/-- Clear the sign bit (absolute value). -/
def abs (f : F32) : F32 := f &&& (BitVec.allOnes 32 >>> 1)

-- ── Classification ───────────────────────────────────────────────────────────

def expIsZero  (f : F32) : Bool := f.expRaw == 0
def expIsMax   (f : F32) : Bool := f.expRaw == BitVec.allOnes 8
def mantIsZero (f : F32) : Bool := f.mantissa == 0

def isZero      (f : F32) : Bool := f.expIsZero  && f.mantIsZero
def isSubnormal (f : F32) : Bool := f.expIsZero  && !f.mantIsZero
def isInf       (f : F32) : Bool := f.expIsMax   && f.mantIsZero
def isNaN       (f : F32) : Bool := f.expIsMax   && !f.mantIsZero
def isFinite    (f : F32) : Bool := !f.expIsMax
def isNormal    (f : F32) : Bool := !f.expIsZero && !f.expIsMax

def isQNaN (f : F32) : Bool := f.isNaN && f.mantissa.getLsbD 22
def isSNaN (f : F32) : Bool := f.isNaN && !f.mantissa.getLsbD 22

/-- Full 24-bit significand including implicit leading bit. -/
def significand (f : F32) : BitVec 24 :=
  let lead : BitVec 24 := if f.isNormal then 1 <<< 23 else 0
  lead ||| f.mantissa.zeroExtend 24

-- ── Special value constants ───────────────────────────────────────────────────

def posZero    : F32 := F32.pack false 0 0
def negZero    : F32 := F32.pack true  0 0
def posInf     : F32 := F32.pack false (BitVec.allOnes 8) 0
def negInf     : F32 := F32.pack true  (BitVec.allOnes 8) 0
def qNaN       : F32 := F32.pack false (BitVec.allOnes 8) (1 <<< 22)
def maxNorm    : F32 := F32.pack false (0xFE : BitVec 8) (BitVec.allOnes 23)
def minNorm    : F32 := F32.pack false (0x01 : BitVec 8) 0
def minSubnorm : F32 := F32.pack false 0 1

-- ── Comparison ───────────────────────────────────────────────────────────────

/-- IEEE 754 equality: NaN ≠ NaN, +0 = -0. -/
def feq (a b : F32) : Bool :=
  if a.isNaN || b.isNaN then false
  else if a.isZero && b.isZero then true
  else a == b

/-- IEEE 754 less-than. -/
def flt (a b : F32) : Bool :=
  if a.isNaN || b.isNaN then false
  else if a.isZero && b.isZero then false
  else
    match a.sign, b.sign with
    | true,  false => !a.isZero
    | false, true  => !b.isZero
    | false, false => a.toNat < b.toNat
    | true,  true  => a.toNat > b.toNat

def fle (a b : F32) : Bool := F32.feq a b || F32.flt a b
def fgt (a b : F32) : Bool := F32.flt b a
def fge (a b : F32) : Bool := F32.fle b a

def fmin (a b : F32) : F32 :=
  if a.isNaN then b else if b.isNaN then a
  else if F32.flt a b then a else b

def fmax (a b : F32) : F32 :=
  if a.isNaN then b else if b.isNaN then a
  else if F32.flt a b then b else a

-- ── Decode: BitVec 32 → DecodedFloat ─────────────────────────────────────────

/-- Decode a raw F32 bit pattern into a format-agnostic DecodedFloat.
    This is the "Decode" box in the diagram. -/
def decode (f : F32) : DecodedFloat :=
  if f.isNaN  then .nan
  else if f.isInf  then .inf f.sign
  else if f.isZero then .finite f.sign 0 0
  else
    -- exp stored as: value = (-1)^s × sig × 2^(unbiasedExp - 23)
    -- For normal:    unbiasedExp = expRaw - 127,  sig has leading 1 at bit 23
    -- For subnormal: unbiasedExp = 1 - 127 = -126, sig has no leading 1
    let rawExp : Int := if f.isNormal then f.expRaw.toNat else 1
    let e      : Int := rawExp - 127 - 23    -- = unbiasedExp - M
    .finite f.sign e f.significand.toNat

-- ── Encode: DecodedFloat → BitVec 32 ─────────────────────────────────────────

/-- Encode a (already-rounded) DecodedFloat into a raw F32 bit pattern.
    This is the "Encode" box in the diagram.
    The input `d` should come from `roundTo f32Fmt rm exact_result`. -/
def encode (d : DecodedFloat) : F32 :=
  match d with
  | .nan    => F32.qNaN
  | .inf s  => F32.pack s (BitVec.allOnes 8) 0
  | .finite s _ 0 => F32.pack s 0 0
  | .finite s e sig =>
    -- Find leading bit position of (already-rounded) sig
    let leadPos := findLeadingBit sig (sig.log2 + 1)
    -- Biased exponent: e = unbiasedExp - 23  →  unbiasedExp = e + leadPos - (leadPos - 23)
    -- Actually: value = sig * 2^e. The implicit-1 format needs sig normalised to [2^23, 2^24).
    -- sig is already in that range after roundTo.
    -- biasedExp = unbiasedExp + 127 = (e + 23) + 127
    -- (because e = rawUnbiasedExp - 23, so rawUnbiasedExp = e + 23,
    --  but also leadPos should be 23 for normalised; if not, adjust)
    let biasedExp : Int := e + (leadPos : Int) + 127
    if biasedExp <= 0 then
      -- subnormal result (sig has no implicit leading 1)
      -- shift sig to fill mantissa field
      let subSig := sig &&& ((1 <<< 23) - 1)
      F32.pack s 0 (subSig.toUInt32.toBitVec.truncate 23)
    else if biasedExp >= 0xFF then
      if s then F32.negInf else F32.posInf
    else
      let mant := sig &&& ((1 <<< 23) - 1)
      F32.pack s (biasedExp.toNat.toUInt8.toBitVec) (mant.toUInt32.toBitVec.truncate 23)

end F32


-- ─────────────────────────────────────────────────────────────────────────────
-- §7  F32 — Top-level composed operations
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Each operation follows the four-step pipeline from the diagram:
--   decode → exact-op → roundTo → encode
-- ─────────────────────────────────────────────────────────────────────────────

namespace F32

-- ── Flag-returning variants (primary implementations) ────────────────────────

def faddEx (rm : RoundMode) (a b : F32) : F32 × ExcFlags :=
  let (ex, ef) := addExact rm (F32.decode a) (F32.decode b)
  let (rd, rf) := roundTo f32Fmt rm ex
  (F32.encode rd, ef.merge rf)

def fmulEx (rm : RoundMode) (a b : F32) : F32 × ExcFlags :=
  let (ex, ef) := mulExact (F32.decode a) (F32.decode b)
  let (rd, rf) := roundTo f32Fmt rm ex
  (F32.encode rd, ef.merge rf)

def fdivEx (rm : RoundMode) (a b : F32) : F32 × ExcFlags :=
  let (ex, ef) := divExact (F32.decode a) (F32.decode b)
  let (rd, rf) := roundTo f32Fmt rm ex
  (F32.encode rd, ef.merge rf)

def fmaEx (rm : RoundMode) (a b c : F32) : F32 × ExcFlags :=
  let (ex, ef) := fmaExact rm (F32.decode a) (F32.decode b) (F32.decode c)
  let (rd, rf) := roundTo f32Fmt rm ex
  (F32.encode rd, ef.merge rf)

def fsqrtEx (rm : RoundMode) (a : F32) : F32 × ExcFlags :=
  let (ex, ef) := sqrtExact (F32.decode a)
  let (rd, rf) := roundTo f32Fmt rm ex
  (F32.encode rd, ef.merge rf)

-- ── Result-only aliases (backward-compatible, used by oracle) ─────────────────

def fadd  (rm : RoundMode) (a b : F32) : F32 := (F32.faddEx rm a b).1
def fsub  (rm : RoundMode) (a b : F32) : F32 := (F32.faddEx rm a b.negate).1
def fmul  (rm : RoundMode) (a b : F32) : F32 := (F32.fmulEx rm a b).1
def fdiv  (rm : RoundMode) (a b : F32) : F32 := (F32.fdivEx rm a b).1
def fma   (rm : RoundMode) (a b c : F32) : F32 := (F32.fmaEx rm a b c).1
def fsqrt (rm : RoundMode) (a : F32) : F32 := (F32.fsqrtEx rm a).1

end F32


-- ─────────────────────────────────────────────────────────────────────────────
-- §8  F64 — Format-specific bitvector layer
-- ─────────────────────────────────────────────────────────────────────────────

namespace F64

def SIGN_WIDTH  : Nat := 1
def EXP_WIDTH   : Nat := 11
def MANT_WIDTH  : Nat := 52
def BIAS        : Int := 1023

def sign     (f : F64) : Bool      := f.getLsbD 63
def expRaw   (f : F64) : BitVec 11 := (f >>> 52).truncate 11
def mantissa (f : F64) : BitVec 52 := f.truncate 52

def expUnbiased (f : F64) : Int := (f.expRaw.toNat : Int) - BIAS

def pack (s : Bool) (e : BitVec 11) (m : BitVec 52) : F64 :=
  let sB : BitVec 64 := if s then 1 <<< 63 else 0
  let eB : BitVec 64 := (e.zeroExtend 64) <<< 52
  let mB : BitVec 64 := m.zeroExtend 64
  sB ||| eB ||| mB

def expIsZero  (f : F64) : Bool := f.expRaw == 0
def expIsMax   (f : F64) : Bool := f.expRaw == BitVec.allOnes 11
def mantIsZero (f : F64) : Bool := f.mantissa == 0

def isZero      (f : F64) : Bool := f.expIsZero && f.mantIsZero
def isSubnormal (f : F64) : Bool := f.expIsZero && !f.mantIsZero
def isInf       (f : F64) : Bool := f.expIsMax  && f.mantIsZero
def isNaN       (f : F64) : Bool := f.expIsMax  && !f.mantIsZero
def isNormal    (f : F64) : Bool := !f.expIsZero && !f.expIsMax
def isFinite    (f : F64) : Bool := !f.expIsMax

def negate (f : F64) : F64 := f ^^^ (1 <<< 63)
def abs    (f : F64) : F64 := f &&& (BitVec.allOnes 64 >>> 1)

/-- Full 53-bit significand including implicit leading bit. -/
def significand (f : F64) : BitVec 53 :=
  let lead : BitVec 53 := if f.isNormal then 1 <<< 52 else 0
  lead ||| f.mantissa.zeroExtend 53

def posZero : F64 := F64.pack false 0 0
def negZero : F64 := F64.pack true  0 0
def posInf  : F64 := F64.pack false (BitVec.allOnes 11) 0
def negInf  : F64 := F64.pack true  (BitVec.allOnes 11) 0
def qNaN    : F64 := F64.pack false (BitVec.allOnes 11) (1 <<< 51)

-- ── Decode / Encode ───────────────────────────────────────────────────────────

/-- Decode a raw F64 bit pattern into a DecodedFloat. -/
def decode (f : F64) : DecodedFloat :=
  if f.isNaN  then .nan
  else if f.isInf  then .inf f.sign
  else if f.isZero then .finite f.sign 0 0
  else
    let rawExp : Int := if f.isNormal then f.expRaw.toNat else 1
    let e      : Int := rawExp - 1023 - 52
    .finite f.sign e f.significand.toNat

/-- Encode a (already-rounded) DecodedFloat into a raw F64 bit pattern. -/
def encode (d : DecodedFloat) : F64 :=
  match d with
  | .nan    => F64.qNaN
  | .inf s  => F64.pack s (BitVec.allOnes 11) 0
  | .finite s _ 0 => F64.pack s 0 0
  | .finite s e sig =>
    let leadPos   := findLeadingBit sig (sig.log2 + 1)
    let biasedExp : Int := e + (leadPos : Int) + 1023
    if biasedExp <= 0 then
      let subSig := sig &&& ((1 <<< 52) - 1)
      F64.pack s 0 (subSig.toUInt64.toBitVec.truncate 52)
    else if biasedExp >= 0x7FF then
      if s then F64.negInf else F64.posInf
    else
      let mant := sig &&& ((1 <<< 52) - 1)
      F64.pack s (biasedExp.toNat.toUInt16.toBitVec.truncate 11)
                 (mant.toUInt64.toBitVec.truncate 52)

end F64


-- ─────────────────────────────────────────────────────────────────────────────
-- §9  F64 — Top-level composed operations
-- ─────────────────────────────────────────────────────────────────────────────

namespace F64

def faddEx (rm : RoundMode) (a b : F64) : F64 × ExcFlags :=
  let (ex, ef) := addExact rm (F64.decode a) (F64.decode b)
  let (rd, rf) := roundTo f64Fmt rm ex
  (F64.encode rd, ef.merge rf)

def fmulEx (rm : RoundMode) (a b : F64) : F64 × ExcFlags :=
  let (ex, ef) := mulExact (F64.decode a) (F64.decode b)
  let (rd, rf) := roundTo f64Fmt rm ex
  (F64.encode rd, ef.merge rf)

def fdivEx (rm : RoundMode) (a b : F64) : F64 × ExcFlags :=
  let (ex, ef) := divExact (F64.decode a) (F64.decode b)
  let (rd, rf) := roundTo f64Fmt rm ex
  (F64.encode rd, ef.merge rf)

def fmaEx (rm : RoundMode) (a b c : F64) : F64 × ExcFlags :=
  let (ex, ef) := fmaExact rm (F64.decode a) (F64.decode b) (F64.decode c)
  let (rd, rf) := roundTo f64Fmt rm ex
  (F64.encode rd, ef.merge rf)

def fsqrtEx (rm : RoundMode) (a : F64) : F64 × ExcFlags :=
  let (ex, ef) := sqrtExact (F64.decode a)
  let (rd, rf) := roundTo f64Fmt rm ex
  (F64.encode rd, ef.merge rf)

def fadd  (rm : RoundMode) (a b : F64) : F64 := (F64.faddEx rm a b).1
def fsub  (rm : RoundMode) (a b : F64) : F64 := (F64.faddEx rm a b.negate).1
def fmul  (rm : RoundMode) (a b : F64) : F64 := (F64.fmulEx rm a b).1
def fdiv  (rm : RoundMode) (a b : F64) : F64 := (F64.fdivEx rm a b).1
def fma   (rm : RoundMode) (a b c : F64) : F64 := (F64.fmaEx rm a b c).1
def fsqrt (rm : RoundMode) (a : F64) : F64 := (F64.fsqrtEx rm a).1

end F64


-- ─────────────────────────────────────────────────────────────────────────────
-- §10  Conversions
-- ─────────────────────────────────────────────────────────────────────────────

namespace F32

/-- Widen Float32 to Float64 (exact, no rounding needed). -/
def toFloat64 (f : F32) : F64 :=
  if f.isNaN  then F64.qNaN
  else if f.isInf  then F64.pack f.sign (BitVec.allOnes 11) 0
  else if f.isZero then F64.pack f.sign 0 0
  else
    -- Decode then re-encode at F64 precision (exact for normal & subnormal F32)
    F64.encode (F32.decode f)

/-- Truncate Float64 to Float32 with rounding. -/
def ofFloat64 (rm : RoundMode) (f : F64) : F32 :=
  F32.encode (roundTo f32Fmt rm (F64.decode f)).1

/-- Convert 32-bit signed integer to Float32. -/
def ofInt32 (rm : RoundMode) (i : Int32) : F32 :=
  if i == 0 then F32.posZero
  else
    let sign := i < 0
    let mag  := if sign then (-i.toInt).toNat else i.toInt.toNat
    -- value = (-1)^sign * mag * 2^0
    F32.encode (roundTo f32Fmt rm (.finite sign 0 mag)).1

/-- Convert Float32 to 32-bit signed integer (truncate toward zero). -/
def toInt32 (f : F32) : Int32 :=
  if f.isNaN || f.isInf || f.isZero then 0
  else
    let e   := f.expUnbiased
    let mag := f.significand.toNat
    let int :=
      if e >= 23    then mag <<< (e - 23).toNat
      else if e < 0 then 0
      else              mag >>> (23 - e.toNat)
    if f.sign then -(int.toInt32) else int.toInt32

end F32


-- ─────────────────────────────────────────────────────────────────────────────
-- §11  Verification Properties
-- ─────────────────────────────────────────────────────────────────────────────

namespace F32

-- ── Classification properties ─────────────────────────────────────────────────

theorem classify_exclusive (f : F32) :
    (List.map (fun x => if x then 1 else 0)
      [f.isZero, f.isSubnormal, f.isNormal, f.isInf, f.isNaN]).sum = 1 := by
  simp [isZero, isSubnormal, isNormal, isInf, isNaN]
  cases h1 : f.expIsZero <;> cases h2 : f.mantIsZero <;> cases h3 : f.expIsMax <;>
  simp [expIsZero, expIsMax, mantIsZero] at *
  simp_all <;> decide
  simp_all

inductive F32Class where | zero | subnormal | normal | inf | nan

def classify (f : F32) : F32Class :=
  if f.isZero      then .zero
  else if f.isSubnormal then .subnormal
  else if f.isNormal    then .normal
  else if f.isInf       then .inf
  else .nan

theorem finite_classify (f : F32)   (hNaN : f.isNaN = false) (hInf: f.isInf = false) :
    f.isZero ∨ f.isSubnormal ∨ f.isNormal := by
  simp only [isNaN, isInf] at hNaN hInf
  simp only [isZero, isSubnormal, isNormal]
  cases h1 : f.expIsZero <;> cases h2 : f.mantIsZero <;> cases h3 : f.expIsMax <;>
  simp_all

theorem contrapositive_example (h : p → q) : ¬q → ¬p := by
  intro hnq hp
  apply hnq
  apply h
  exact hp

-- ─────────────────────────────────────────────────────────────────────────────
-- Auxiliary lemmas used across all five proofs
-- ─────────────────────────────────────────────────────────────────────────────

private theorem expZero_ne_expMax (f : F32) :
    ¬(f.expIsZero = true ∧ f.expIsMax = true) := by
  simp [expIsZero, expIsMax]
  intro h; simp [h]

private theorem isZero_false_of_isSubnormal (f : F32) (h : f.isSubnormal = true) :
    f.isZero = false := by
  simp [isZero, isSubnormal] at *
  obtain ⟨hexp, hmant⟩ := h
  simp [hexp, hmant]

private theorem isZero_false_of_isNormal (f : F32) (h : f.isNormal = true) :
    f.isZero = false := by
  simp [isZero, isNormal, expIsZero, expIsMax] at *
  obtain ⟨hne0, _⟩ := h
  cases hm : f.mantIsZero <;> simp [hne0]

private theorem isZero_false_of_isInf (f : F32) (h : f.isInf = true) :
    f.isZero = false := by
  simp [isZero, isInf, expIsZero, expIsMax] at *
  obtain ⟨left, right⟩ := h
  intro hzero
  rw [left] at hzero
  contradiction

private theorem isZero_false_of_isNaN (f : F32) (h : f.isNaN = true) :
    f.isZero = false := by
  simp [isZero, isNaN, expIsZero, expIsMax] at *
  obtain ⟨hmax, _⟩ := h
  intro hzero
  rw [hmax] at hzero
  contradiction

private theorem isSubnormal_false_of_isNormal (f : F32) (h : f.isNormal = true) :
    f.isSubnormal = false := by
  simp [isSubnormal, isNormal, expIsZero] at *
  intros h2
  obtain ⟨expraw_nz, exp_nomax⟩ := h
  contradiction

private theorem isSubnormal_false_of_isInf (f : F32) (h : f.isInf = true) :
    f.isSubnormal = false := by
  simp [isSubnormal, isInf, expIsZero, expIsMax] at *
  obtain ⟨hmax, mantissa_max⟩ := h
  intro hzero
  rw [hmax] at hzero
  contradiction

private theorem isSubnormal_false_of_isNaN (f : F32) (h : f.isNaN = true) :
    f.isSubnormal = false := by
  simp [isSubnormal, isNaN, expIsZero, expIsMax] at *
  obtain ⟨hmax, _⟩ := h
  intro hzero
  rw [hmax] at hzero
  contradiction

private theorem isNormal_false_of_isInf (f : F32) (h : f.isInf = true) :
    f.isNormal = false := by
  simp [isNormal, isInf, expIsMax] at *
  intros exp_zero
  exact h.1

private theorem isNormal_false_of_isNaN (f : F32) (h : f.isNaN = true) :
    f.isNormal = false := by
  simp [isNormal, isNaN, expIsMax] at *
  intros
  exact h.1

private theorem isInf_false_of_isNaN (f : F32) (h : f.isNaN = true) :
    f.isInf = false := by
  simp [isInf, isNaN, mantIsZero] at *
  intros
  obtain ⟨ _, mant_nonzero⟩ := h
  exact mant_nonzero


private theorem isInf_false_of_isZero (f : F32) (h : f.isZero = true) :
  f.isInf = false := by
  simp [isInf, isZero ] at *
  intros h
  rename_i h2
  simp [expIsZero,expIsMax] at *
  cases h2
  rename_i right left
  rw [right] at h
  contradiction



private theorem isInf_false_of_isNormal (f : F32) (h : f.isNormal = true) :
    f.isInf = false := by
  simp [isInf,  mantIsZero,isNormal] at *
  have ⟨exp_nz,exp_max⟩ := h
  intros h1
  simp_all

private theorem isNaN_false_of_isInf (f:F32) (h:f.isInf = true) :
  f.isNaN = false := by
  simp [isNaN,isInf] at *
  obtain ⟨expMax,mantZ⟩ := h
  intros h1
  exact mantZ

private theorem isNaN_false_of_isZero (f:F32) (h:f.isZero = true) :
  f.isNaN = false := by
  simp [isNaN,isZero] at *
  have ⟨expZero,mantZero⟩ := h
  intros h1
  exact mantZero
private theorem isNaN_false_of_isSubnormal (f:F32) (h:f.isSubnormal = true) :
  f.isNaN = false := by
  simp [isNaN]
  simp [isSubnormal] at h
  have ⟨expz,mantz⟩ := h
  intros h2
  simp [expIsZero] at expz
  simp [expIsMax] at h2
  rw [expz] at h2
  contradiction


theorem biject_class_zero (f : F32) :
    f.isZero = true ↔ classify f = .zero := by
  constructor
  · intro h
    unfold classify
    rw [h]
    simp
  · intro h
    unfold classify at h
    cases hZ : f.isZero with
    | true  =>
      -- isZero = true, done
       rfl
    | false =>
      -- isZero = false: h simplifies to nested ifs
      rw [hZ] at h
      simp at h
      -- h is now about inner ifs, all give ≠ .zero
      cases hSubN : f.isSubnormal with
      | true =>
             simp_all
      | false =>
             cases hN : f.isNormal with
             | true => simp_all
             | false =>
                     rw [hSubN, hN] at h
                     simp at h
                     cases hInf : f.isInf with
                     | true => simp_all
                     | false => simp_all



theorem biject_class_nan (f:F32) :
  f.isNaN ↔ (classify f) = .nan :=
by
constructor
· intro h
  unfold classify
  rw [isZero_false_of_isNaN, isSubnormal_false_of_isNaN, isNormal_false_of_isNaN, isInf_false_of_isNaN]
  simp
  repeat exact h
· intro h
  unfold classify at h
  cases hNan : f.isNaN with
  | true  =>
    -- isZero = true, done
     rfl
  | false =>
    cases hZ : f.isZero with
    | true =>
           simp_all
    | false =>
           cases hsN : f.isSubnormal with
           | true => simp_all
           | false =>
                   rw [hsN, hZ] at h
                   simp at h
                   cases hN : f.isNormal with
                   | true => simp_all
                   | false =>
                     rw [hN] at h
                     simp at h
                     simp_all
                     have ce_f := classify_exclusive f
                     rw [hNan,hZ,hsN,hN] at ce_f
                     simp at ce_f
                     rw [h] at ce_f
                     contradiction


theorem biject_class_inf (f:F32) :
  f.isInf ↔ (classify f) = .inf :=
by
constructor
· intro h
  unfold classify
  rw [isZero_false_of_isInf, isSubnormal_false_of_isInf, isNormal_false_of_isInf]
  simp
  repeat exact h
· intro h
  unfold classify at h
  cases hinf : f.isInf with
  | true  =>
    -- isZero = true, done
     rfl
  | false =>
    cases hZ : f.isZero with
    | true =>
           simp_all
    | false =>
           cases hsN : f.isSubnormal with
           | true => simp_all
           | false =>
                   rw [hsN, hZ] at h
                   simp at h
                   cases hN : f.isNormal with
                   | true => simp_all
                   | false =>
                     rw [hN] at h
                     simp at h
                     simp_all

theorem biject_class_normal (f:F32) :
  f.isNormal ↔ (classify f) = .normal :=
by
constructor
·
  intro h
  unfold classify
  rw [isZero_false_of_isNormal,isSubnormal_false_of_isNormal,isInf_false_of_isNormal]
  simp
  repeat exact h
·
  intro h
  unfold classify at h
  cases hz : f.isZero with
  | true =>
    simp_all
  | false =>
    cases hSn : f.isSubnormal with
    | true =>
           simp_all
    | false =>
            rw [hSn,hz] at h
            simp at h
            cases hN: f.isNormal with
            | true => simp_all
            | false =>
                rw [hN] at h
                simp at h
                cases hInf : f.isInf with
                | true => simp_all
                | false =>
                  rw [hInf] at h
                  simp at h

theorem biject_class_subn (f:F32) :
  f.isSubnormal ↔ (classify f) = .subnormal :=
by
 constructor
 ·
  intro h
  unfold classify
  rw [isZero_false_of_isSubnormal,h]
  simp
  exact h
 ·
  intro h
  unfold classify at h
  cases hz : f.isZero with
  | true =>
    simp_all
  | false =>
    cases hSn : f.isSubnormal with
    | true =>
           rw [hSn] at h
    | false =>
            rw [hSn,hz] at h
            simp at h
            cases hN: f.isNormal with
            | true => simp_all
            | false =>
                rw [hN] at h
                simp at h
                cases hInf : f.isInf with
                | true => simp_all
                | false =>
                  rw [hInf] at h
                  simp at h









-- ── Sign properties ───────────────────────────────────────────────────────────

theorem negate_sign (f : F32) : f.negate.sign = !f.sign := by
  simp [negate, sign, getLsbD]
  cases f.negate.sign with
  | true  => simp [Nat.testBit]
  | false => simp [Nat.testBit]

theorem negate_negate (f : F32) : f.negate.negate = f := by
  simp [negate]
  cases f.sign with
  | true  => rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  | false => rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem abs_sign (f : F32) : !f.abs.sign := by
  simp [F32.abs, sign, getLsbD]
  cases f.abs.sign with
  | true  => simp [Nat.testBit]
  | false => simp [Nat.testBit]

-- ── Comparison properties ─────────────────────────────────────────────────────

theorem nan_not_zero : !F32.qNaN.isZero := by native_decide
theorem posZero_isZero : F32.posZero.isZero := by native_decide
theorem negZero_isZero : F32.negZero.isZero := by native_decide
theorem posInf_isInf : F32.posInf.isInf := by native_decide

theorem feq_refl (f : F32) (hNaN : !f.isNaN) : F32.feq f f := by
  simp [feq, isNaN] at *
  cases hNaN with
  | inl  => cases f.mantIsZero with
            | true  => simp
            | false => simp; trivial
  | inr  => cases f.expIsMax with
            | true  => simp; trivial
            | false => simp

theorem feq_symm (a b : F32) : F32.feq a b = F32.feq b a := by
  simp [feq, Bool.or_comm, Bool.and_comm]
  cases a.isNaN with
  | true  => simp
  | false => cases b.isNaN with
             | true  => simp
             | false => cases a.isZero with
                        | true  => simp; rw [BEq.comm]
                        | false => simp; rw [BEq.comm]

theorem feq_trans (a b c : F32) (h1 : F32.feq a b = true) (h2 : F32.feq b c = true) :
    F32.feq a c = true := by
  cases ha : a.isNaN <;> cases hb : b.isNaN <;> cases hc : c.isNaN <;>
  cases haZ : a.isZero <;> cases hbZ : b.isZero <;> cases hcZ : c.isZero <;>
  simp_all [feq, beq_iff_eq]

theorem nan_neq_self : !F32.feq F32.qNaN F32.qNaN := by native_decide
theorem zero_eq_neg_zero : F32.feq F32.posZero F32.negZero := by native_decide

-- ── Decode/Encode round-trip sanity ──────────────────────────────────────────

theorem qNaN_is_NaN  : qNaN.isNaN    := by simp [qNaN]; decide
theorem qNaN_is_not_zero : qNaN.isZero = false := by simp [qNaN, isZero]; decide

/-- Widening F32 → F64 preserves NaN. -/
theorem f32nan_to_f64_nan (f : F32) : f.isNaN → (F32.toFloat64 f).isNaN := by
  simp [toFloat64]
  intro h1
  rw [h1]
  simp
  native_decide



/-- roundTo is a no-op on .nan (returns .nan with no flags). -/
theorem roundTo_nan (fmt : FPFormat) (rm : RoundMode) :
    roundTo fmt rm .nan = (.nan, ExcFlags.empty) := by
    simp [roundTo]

/-- roundTo is a no-op on .inf (returns same Inf with no flags). -/
theorem roundTo_inf (fmt : FPFormat) (rm : RoundMode) (s : Bool) :
    roundTo fmt rm (.inf s) = (.inf s, ExcFlags.empty) := by
    simp [roundTo]

/-- roundTo maps any exact zero to zero (regardless of exp). -/
theorem roundTo_zero (fmt : FPFormat) (rm : RoundMode) (s : Bool) (e : Int) :
    ((roundTo fmt rm (.finite s e 0)).1).isZero := by
    simp [roundTo]
    simp [DecodedFloat.isZero]

/-- Rounding a nonzero finite value preserves sign (unless the result underflows to zero). -/
theorem roundTo_sign_preserved {fmt : FPFormat} {rm : RoundMode}
    {f: DecodedFloat} (hne : sig ≠ 0)
    (hf : f.isFinite = true)
    (hres : ¬((roundTo fmt rm f).1).isZero) :
    ((roundTo fmt rm f).1).dfSign = f.dfSign := by
    simp [DecodedFloat.dfSign]
    split
    ·
      rename_i x a heq
      split
      ·
        simp [DecodedFloat.isZero] at hres
        simp [roundTo] at hres
        simp_all
        simp_all


    simp at hne
    simp at hres
    simp [roundTo]
    split
    ·
      simp
    ·
      simp

    ·
      rename_i ds sig
      by_cases hds: ds
      ·
        simp
        rw [hds]
        simp [DecodedFloat.dfSign]
      ·
        simp [DecodedFloat.dfSign]
    ·
      split
      ·
        simp [DecodedFloat.dfSign]
      ·
        split
        ·
          simp












/-- roundTo is idempotent: rounding an already-rounded value produces no new flags
    and the same result. -/
theorem roundTo_idempotent (fmt : FPFormat) (rm : RoundMode) (d : DecodedFloat) :
    roundTo fmt rm (roundTo fmt rm d).1 = ((roundTo fmt rm d).1, ExcFlags.empty) := by
    cases d
    ·
      simp [roundTo]
      split <;>
      split
      ·
        simp_all
      ·
        simp_all
      ·
        simp_all
      ·
        split 
        ·
          simp_all 
        ·
          split
          · 
            simp_all
          ·
            simp_all 
      ·
        simp_all 
      ·
        simp_all
      ·
        simp_all
      ·
        rename_i heq   
        rename_i x 
        rename_i heq1 heq d s e sig
        split at heq1
        
      ·
        simp_all





    ·
      simp [roundTo]
    ·
      simp [roundTo]
    ·





-- ── NaN / Inf propagation through addExact / mulExact ────────────────────────
-- adding nan left will result nan and no flags will be there
theorem addExact_nan_l (rm : RoundMode) (b : DecodedFloat) :
    addExact rm .nan b = (.nan, ExcFlags.empty) := by
    cases b
    ·
      simp [addExact]
    ·
      simp [addExact]
    ·
      simp [addExact]

-- adding nan in the right will result to nan and no flags will be there
theorem addExact_nan_r (rm : RoundMode) (a : DecodedFloat) :
    addExact rm a .nan = (.nan, ExcFlags.empty) := by
    cases a
    ·
      simp [addExact]
    ·
      simp [addExact]
    ·
      simp [addExact]
-- multiplication with nan on the left will result in nan and no flags will effect
theorem mulExact_nan_l (b : DecodedFloat) :
    mulExact .nan b = (.nan, ExcFlags.empty) := by
    cases b
    ·
      simp [mulExact]
    ·
      simp [mulExact]
    ·
      simp [mulExact]
-- multiplication with nan on the right will result in nan and no flags
theorem mulExact_nan_r (a : DecodedFloat) :
    mulExact a .nan = (.nan, ExcFlags.empty) := by
    cases a
    ·
      simp [mulExact]
    ·
      simp [mulExact]
    ·
      simp [mulExact]

/-- Inf + Inf of opposite sign is invalid (raises invalidOp, returns .nan). -/
theorem addExact_inf_opp (rm : RoundMode) (s : Bool) :
    addExact rm (.inf s) (.inf (!s)) = (.nan, ExcFlags.mkInvalidOp) := by
    simp [addExact]

/-- Inf + finite = Inf with no flags. -/
theorem addExact_inf_finite (rm : RoundMode) (s t : Bool) (e : Int) (sig : Nat) :
    addExact rm (.inf s) (.finite t e sig) = (.inf s, ExcFlags.empty) := by
    simp [addExact]


/-- Inf × 0 is invalid (raises invalidOp). -/
theorem mulExact_inf_zero (s t : Bool) (e : Int) :
    mulExact (.inf s) (.finite t e 0) = (.nan, ExcFlags.mkInvalidOp) := by
    simp [mulExact]

/-- Inf × nonzero = Inf (sign = XOR, no flags). -/
theorem mulExact_inf_nonzero (sa sb : Bool) (eb : Int) (sigb : Nat) (hnz : sigb ≠ 0) :
    mulExact (.inf sa) (.finite sb eb sigb) = (.inf (sa != sb), ExcFlags.empty) := by
    simp [mulExact]

/-- Finite × finite: exact product with sign = XOR, no flags. -/
theorem mulExact_finite_sign (sa sb : Bool) (ea eb : Int) (siga sigb : Nat) :
    mulExact (.finite sa ea siga) (.finite sb eb sigb) =
    (.finite (sa != sb) (ea + eb) (siga * sigb), ExcFlags.empty) := by
    simp [mulExact]


end F32
-- ─────────────────────────────────────────────────────────────────────────────
-- §11c  F32 IEEE 754 Correctness Properties
-- ─────────────────────────────────────────────────────────────────────────────
-- Each theorem corresponds to a requirement in IEEE 754-2019.
-- Proofs left as `sorry`; they should ultimately follow from §11b lemmas above.

namespace F32

-- ── A. Codec round-trip (Decode then Encode = identity) ──────────────────────

/-- Decoding a NaN bit pattern yields .nan. -/
theorem decode_nan {f : F32} (h : f.isNaN) : F32.decode f = .nan := by
  simp [decode]
  rw [h]
  simp

/-- Decoding an Inf bit pattern yields .inf with the correct sign. -/
theorem decode_inf {f : F32} (h : f.isInf) : F32.decode f = .inf f.sign := by
  simp [decode]
  rw [h]
  simp
  have h2 : ¬f.isNaN := by
    simp [isNaN]
    simp [isInf] at h
    cases h
    .
      rename_i expMax mantIsZero
      intros
      exact mantIsZero
  simp at h2
  exact h2







/-- Decoding any zero bit pattern yields a zero DecodedFloat. -/
theorem decode_isZero {f : F32} (h : f.isZero) : (F32.decode f).isZero := by
  simp [decode]
  rw [h]
  simp
  have h1 : ¬f.isNaN := by
    simp [isNaN]
    simp [isZero] at h
    intros
    cases h
    rename_i mant
    exact mant
  simp [isZero] at h
  simp [isNaN]
  split
  ·
    cases h
    rename_i right left
    rename_i h2
    cases h2
    rename_i h2right h2left
    rw [F32.expIsZero] at right
    rw [F32.expIsMax] at h2right
    simp at right
    simp [right ] at  h2right
  ·
   cases h
   rename_i right left
   rw [F32.isInf]
   rw [left]
   simp
   rw [F32.expIsMax]
   rw [F32.expIsZero] at right
   simp at right
   rw [right]
   simp [DecodedFloat.isZero]


/-- encode ∘ decode is the identity on normal F32 values (IEEE 754 bitvector layout).
    Proof: decode produces exact (sign, exp, sig) then encode reconstructs them. -/
theorem encode_decode_normal {f : F32} (h : f.isNormal) :
    F32.encode (F32.decode f) = f := by
  -- isNormal = (!expIsZero && !expIsMax)
  have hExpZero : f.expIsZero = false := by simp [isNormal] at h; exact h.1
  have hExpMax  : f.expIsMax  = false := by simp [isNormal] at h; exact h.2
  -- Derived classification facts
  have hNotNaN  : f.isNaN  = false := by simp [isNaN,  hExpMax]
  have hNotInf  : f.isInf  = false := by simp [isInf,  hExpMax]
  have hNotZero : f.isZero = false := by simp [isZero, hExpZero]
  -- Reduce decode to the normal case: rawExp = expRaw.toNat
  simp only [decode, hNotNaN, hNotInf, hNotZero, h, ite_true]
  unfold encode
  simp
  split
  ·
    simp_all
  ·
    simp_all
  ·
    rename_i d s exp heq
    simp [isZero] at hNotZero
    simp [isNaN] at hNotNaN
    simp [isInf] at hNotInf
    simp_all
    have ⟨left,mid,right⟩ := heq
    simp [expRaw] at mid
    simp_all
    simp [significand]  at right
    rw [h] at right
    simp at right
    simp [isNormal] at h
    have ⟨ hl , hr ⟩ := h
    simp [pack]

    have pack_f : (pack f.sign f.expRaw f.significand.toNat) = f := by
         simp [pack]
    cases s
    ·
      rw [← pack_f ]
      simp_all










  -- Goal: encode (.finite f.sign (↑expRaw.toNat - 127 - 23) f.significand.toNat) = f
  --
  -- Remaining proof steps (see sorry):
  --   1. significand.toNat = 2^23 + mantissa.toNat  (isNormal → leading 1 at bit 23)
  --      → significand.toNat ≠ 0
  --      → findLeadingBit significand.toNat (log2+1) = 23
  --   2. biasedExp = (expRaw.toNat - 127 - 23) + 23 + 127 = expRaw.toNat  (omega)
  --   3. expIsZero = false → expRaw.toNat ≥ 1  (biasedExp > 0)
  --      expIsMax  = false → expRaw.toNat ≤ 254  (biasedExp < 0xFF)
  --   4. significand.toNat &&& (2^23 - 1) = mantissa.toNat  (masks off the leading 1)
  --   5. pack f.sign f.expRaw f.mantissa = f  (bitvector field-reconstruction identity)
  sorry








/-- encode ∘ decode is the identity on subnormal F32 values. -/
theorem encode_decode_subnormal {f : F32} (h : f.isSubnormal) :
    F32.encode (F32.decode f) = f := by
  -- isSubnormal = (expIsZero && !mantIsZero)
  have hExpZero : f.expIsZero = true   := by simp [isSubnormal] at h; exact h.1
  have hMantNZ  : f.mantIsZero = false := by simp [isSubnormal] at h; exact h.2
  -- expIsZero=true and expIsMax=true cannot both hold (0 ≠ 0xFF for BitVec 8)
  have hExpMax  : f.expIsMax = false := by
    simp only [expIsMax, expIsZero] at *
    simp only [beq_iff_eq] at hExpZero
    simp [hExpZero]
  -- Derived classification facts
  have hNotNaN    : f.isNaN      = false := by simp [isNaN,      hExpMax]
  have hNotInf    : f.isInf      = false := by simp [isInf,      hExpMax]
  have hNotZero   : f.isZero     = false := by simp [isZero,     hExpZero, hMantNZ]
  have hNotNormal : f.isNormal   = false := by simp [isNormal,   hExpZero]
  -- Reduce decode to the subnormal case: rawExp = 1 (no leading 1)
  simp only [decode, hNotNaN, hNotInf, hNotZero, hNotNormal]
  -- Goal: encode (.finite f.sign (1 - 127 - 23) f.significand.toNat) = f
  --
  -- Remaining proof steps (see sorry):
  --   1. significand.toNat = mantissa.toNat  (isNormal = false → no leading 1)
  --   2. findLeadingBit mantissa.toNat _ ≤ 22  (mantissa : BitVec 23, bits 0..22)
  --      → biasedExp = (1 - 127 - 23) + leadPos + 127 = leadPos - 22 ≤ 0
  --   3. encode hits the subnormal branch:
  --      subSig = mantissa.toNat &&& (2^23 - 1) = mantissa.toNat
  --   4. pack f.sign 0 f.mantissa = f  (subnormal has expRaw = 0 by expIsZero = true)
  simp [encode]
  split
  ·
     simp_all
  ·
    simp_all
  ·
    simp_all
    rename_i d s exp u
    have ⟨ ul, um ,ur ⟩ := u


    simp [isSubnormal] at h
    simp [isSubnormal] at h
  ·
    split
    ·


/-- Ecoding .nan always produces a NaN bit pattern. -/
theorem encode_nan_isNaN : (F32.encode DecodedFloat.nan).isNaN := by
  simp [F32.encode]
  native_decide
/-- Encoding .inf s produces an Inf bit pattern with the same sign. -/
theorem encode_inf_isInf (s : Bool) :
    (F32.encode (.inf s)).isInf ∧ (F32.encode (.inf s)).sign = s := by
    simp [F32.encode]
    simp [pack]
    cases s
    ·
      simp
      native_decide
    ·
      simp
      native_decide

/-- Encoding a zero DecodedFloat produces a zero bit pattern. -/
theorem encode_zero_isZero (s : Bool) (e : Int) :
    (F32.encode (.finite s e 0)).isZero := by
    simp [F32.encode]
    simp [pack]
    cases s
    ·
      simp
      decide
    ·
      decide

-- ── B. NaN propagation (IEEE 754-2019 §6.2) ──────────────────────────────────
 -- adding nan in the left will result nan
theorem fadd_nan_l (rm : RoundMode) (a b : F32) (h : a.isNaN) :
    (F32.fadd rm a b).isNaN := by
    simp [F32.fadd]
    simp [faddEx]
    simp [addExact]
    split
    ·
      simp_all
      simp [roundTo]
      simp [encode]
      decide
    ·
      simp
      simp [roundTo]
      simp [encode]
      decide
    ·
      rename_i da db sa sb heqa heqb
      simp [decode] at heqa
      rw [h ] at heqa
      simp at heqa
    ·
      rename_i da db sa sb heqa heqb
      simp [decode] at sb
      rw [h] at sb
      simp_all
    ·
      rename_i da db s heq ad x
      simp
      simp [decode] at ad
      simp [h] at ad
    ·
      rename_i ad bd
      rename_i sigb eb sb
      rename_i siga ea sa
      rename_i dfa dfb
      simp [decode] at ad
      simp [h] at ad

-- adding nan on the right will result in nan
theorem fadd_nan_r (rm : RoundMode) (a b : F32) (h : b.isNaN) :
    (F32.fadd rm a b).isNaN := by
    simp [F32.fadd]
    simp [faddEx]
    simp [addExact]
    split
    ·
      simp_all
      simp [roundTo]
      simp [encode]
      decide
    ·
      simp
      simp [roundTo]
      simp [encode]
      decide
    ·
      rename_i da db sa sb heqa heqb
      simp [decode] at heqb
      rw [h ] at heqb
      simp at heqb
    ·
      rename_i da db sa sb heqa heqb
      simp [decode] at heqa
      rw [h] at heqa
      simp_all
    ·
      rename_i da db s heq ad x
      simp
      simp [decode] at heq
      simp [h] at heq
    ·
      rename_i ad bd
      rename_i sigb eb sb
      rename_i siga ea sa
      rename_i dfa dfb
      simp [decode] at bd
      simp [h] at bd






 -- multiplying nan in the left will result nan
theorem fmul_nan_l (rm : RoundMode) (a b : F32) (h : a.isNaN) :
    (F32.fmul rm a b).isNaN := by
    simp [F32.fmul ]
    simp [fmulEx]
    simp [mulExact]
    split
    {
    simp
    simp [roundTo]
    simp [encode]
    decide
    }
    {
    simp
    simp [roundTo]
    simp [encode]
    decide
    }
    {
    simp
    simp [roundTo]
    simp [encode]
    decide
    }
    {
    simp
    simp [roundTo]
    simp [encode]
    decide
    }
    {
      simp
      rename_i had hbd
      simp [decode] at had
      simp [h] at had
    }
    {
      simp
      rename_i had hbd
      simp [decode] at had
      simp [h] at had
    }
    {
      simp
      rename_i had hbd
      simp [decode] at had
      simp [h] at had
    }
    {
      simp
      rename_i had hbd
      simp [decode] at had
      simp [h] at had
    }


theorem fmul_nan_r (rm : RoundMode) (a b : F32) (h : b.isNaN) :
    (F32.fmul rm a b).isNaN := by
    simp [F32.fmul ]
    simp [fmulEx]
    simp [mulExact]
    split
    {
    simp
    simp [roundTo]
    simp [encode]
    decide
    }
    {
    simp
    simp [roundTo]
    simp [encode]
    decide
    }
    {
    simp
    simp [roundTo]
    simp [encode]
    decide
    }
    {
    simp
    simp [roundTo]
    simp [encode]
    decide
    }
    {
      simp
      rename_i had hbd
      simp [decode] at hbd
      simp [h] at hbd
    }
    {
      simp
      rename_i had hbd
      simp [decode] at hbd
      simp [h] at hbd
    }
    {
      simp
      rename_i had hbd
      simp [decode] at hbd
      simp [h] at hbd
    }
    {
      simp
      rename_i had hbd
      simp [decode] at hbd
      simp [h] at hbd
    }

theorem fdiv_nan_l (rm : RoundMode) (a b : F32) (h : a.isNaN) :
    (F32.fdiv rm a b).isNaN := by
    simp [isNaN]
    constructor <;>
    {
      simp [fdiv]
      simp [fdivEx]
      simp [decode]
      rw [ h ]
      simp
      simp [divExact]
      simp [divExactWith]
      simp [roundTo]
      simp [encode]
      native_decide
    }

theorem fdiv_nan_r (rm : RoundMode) (a b : F32) (h : b.isNaN) :
    (F32.fdiv rm a b).isNaN := by
    simp [isNaN]
    constructor <;>
    {
      simp [fdiv]
      simp [fdivEx]
      simp [decode]
      rw [ h ]
      simp
      simp [divExact]
      split
      · {
        simp [divExactWith]
        simp [roundTo]
        simp [encode]
        native_decide
      }
      · {
        split
        · {
          simp [divExactWith]
          simp [roundTo]
          simp [encode]
          native_decide
        }
        · {
          split
          · {
            simp [divExactWith]
            simp [roundTo]
            simp [encode]
            native_decide
            }
          ·
            {
            simp[divExactWith]
            simp [roundTo]
            simp [encode]
            native_decide
            }
          }
      }
    }



theorem fma_nan_a (rm : RoundMode) (a b c : F32) (h : a.isNaN) :
    (F32.fma rm a b c).isNaN := by
    simp [isNaN]
    constructor <;>
    · {
      simp [fma, fmaEx,decode]
      rw [h]
      simp_all
      simp [fmaExact]
      simp [roundTo]
      simp [encode]
      native_decide
    }


theorem fma_nan_b (rm : RoundMode) (a b c : F32) (h : b.isNaN) :
    (F32.fma rm a b c).isNaN := by
    simp [isNaN]
    constructor <;>
    sorry




theorem fma_nan_c (rm : RoundMode) (a b c : F32) (h : c.isNaN) :
    (F32.fma rm a b c).isNaN := by
    sorry

-- ── C. Invalid operations → NaN (IEEE 754-2019 §7.2) ─────────────────────────

/-- ∞ × 0 is an invalid operation; result is NaN (§7.2 case d). -/
theorem fmul_inf_zero {rm : RoundMode} {a b : F32}
    (ha : a.isInf) (hb : b.isZero) : (F32.fmul rm a b).isNaN := by
    have a_notn : a.isNaN = false := isNaN_false_of_isInf a ha
    have b_notn : b.isNaN = false := isNaN_false_of_isZero b hb
    have b_notinf : b.isInf = false := isInf_false_of_isZero b hb
    simp [isNaN]
    constructor <;>
    ·
      simp [fmul, fmulEx,decode]
      simp [a_notn , ha]
      simp [b_notn, b_notinf, hb]
      simp [mulExact]
      simp [roundTo]
      simp [encode]
      native_decide







theorem fmul_zero_inf {rm : RoundMode} {a b : F32}
    (ha : a.isZero) (hb : b.isInf) : (F32.fmul rm a b).isNaN := by
    have b_notn : b.isNaN = false := isNaN_false_of_isInf b hb
    have a_notn : a.isNaN = false := isNaN_false_of_isZero a ha
    have a_notinf : a.isInf = false := isInf_false_of_isZero a ha
    simp [isNaN]
    constructor <;>
    ·
      simp [fmul, fmulEx,decode]
      simp [a_notn , ha]
      simp [b_notn, a_notinf, hb]
      simp [mulExact]
      simp [roundTo]
      simp [encode]
      native_decide



/-- (+∞) + (−∞) is an invalid operation; result is NaN (§7.2 case f). -/
theorem fadd_inf_opp {rm : RoundMode} {a b : F32}
    (ha : a.isInf) (hb : b.isInf) (hs : a.sign ≠ b.sign) :
    (F32.fadd rm a b).isNaN := by
    have a_notn : a.isNaN = false := isNaN_false_of_isInf a ha
    have b_notn : b.isNaN = false := isNaN_false_of_isInf b hb
    have b_notz : b.isZero = false := isZero_false_of_isInf b hb

    simp [isNaN]
    constructor <;>
    ·
      simp [fadd, faddEx,decode]
      simp [a_notn , ha]
      simp [b_notn,  hb]
      simp [addExact]
      split
      ·
        simp_all
      ·
        simp [roundTo]
        simp [encode]
        native_decide


/-- 0 / 0 is an invalid operation; result is NaN (§7.2 case g). -/
theorem fdiv_zero_zero {rm : RoundMode} {a b : F32}
    (ha : a.isZero) (hb : b.isZero) : (F32.fdiv rm a b).isNaN := by
    have a_notn : a.isNaN = false := isNaN_false_of_isZero a ha
    have b_notn : b.isNaN = false := isNaN_false_of_isZero b hb
    have b_notInf : b.isInf = false := isInf_false_of_isZero b hb
    have a_notInf : a.isInf = false := isInf_false_of_isZero a ha
    simp [isNaN]
    constructor <;>
    {
    simp [fdiv, fdivEx,decode]
    simp [a_notn , ha]
    simp [b_notn,  hb, b_notInf, a_notInf]
    simp [divExact, divExactWith, roundTo, encode]
    native_decide
    }

/-- ∞ / ∞ is an invalid operation; result is NaN (§7.2 case h). -/
theorem fdiv_inf_inf {rm : RoundMode} {a b : F32}
    (ha : a.isInf) (hb : b.isInf) : (F32.fdiv rm a b).isNaN := by
    have a_notn : a.isNaN = false := isNaN_false_of_isInf a ha
    have b_notn : b.isNaN = false := isNaN_false_of_isInf b hb
    have b_notz : b.isZero = false := isZero_false_of_isInf b hb
    have a_notz : a.isZero = false := isZero_false_of_isInf a ha
    simp [isNaN]
    constructor <;>
    {
    simp [fdiv, fdivEx,decode]
    simp [a_notn , ha]
    simp [b_notn,  hb ]
    simp [divExact, divExactWith, roundTo, encode]
    native_decide
    }

/-- ∞ × 0 in fma is invalid regardless of the addend c (§7.2 case d). -/
theorem fma_inf_zero {rm : RoundMode} {a b c : F32}
    (ha : a.isInf) (hb : b.isZero) : (F32.fma rm a b c).isNaN := by sorry

-- ── D. Inf propagation (IEEE 754-2019 §6.1) ──────────────────────────────────

/-- ∞ + finite = ∞ (sign of Inf operand is preserved). -/
theorem fadd_inf_finite {rm : RoundMode} {a b : F32}
    (ha : a.isInf) (hb : b.isFinite) :
    (F32.fadd rm a b).isInf ∧ (F32.fadd rm a b).sign = a.sign := by sorry

/-- ∞ × nonzero finite = ∞ (sign = XOR of operand signs). -/
theorem fmul_inf_nonzero {rm : RoundMode} {a b : F32}
    (ha : a.isInf) (hb : b.isFinite) (hnz : ¬b.isZero) :
    (F32.fmul rm a b).isInf ∧ (F32.fmul rm a b).sign = (a.sign != b.sign) := by sorry

/-- Nonzero finite / 0 = ∞ (division by zero; §7.3). -/
theorem fdiv_nonzero_zero {rm : RoundMode} {a b : F32}
    (ha : a.isFinite) (hna : ¬a.isZero) (hb : b.isZero) :
    (F32.fdiv rm a b).isInf := by
    have b_ninf : b.isInf = false := isInf_false_of_isZero b hb
    have b_notn : b.isNaN = false := isNaN_false_of_isZero b hb
    simp [isFinite] at ha
    have a_notn : a.isNaN = false := by
                                     simp [isNaN]
                                     intros
                                     simp_all
    have a_notinf : a.isInf = false := by
                                       simp [isInf]
                                       intros
                                       simp_all

    simp [isInf]
    constructor
    · {
      simp [fdiv, fdivEx,decode, a_notn, a_notinf]
      simp_all
      simp [divExact]
      split
      · {
        simp [divExactWith]
        split
        ·
          simp [roundTo]
          simp [encode]
          native_decide
        ·
          simp [roundTo]
          simp [encode]
          native_decide
        ·
          simp [roundTo]
          simp [encode]
          native_decide
        ·
          simp [roundTo]
          simp [encode]
          native_decide
        ·
          simp [roundTo]
          simp [encode]
          bv_decide
        ·
          simp [roundTo]
          simp [encode]
          bv_decide
        ·
          simp [roundTo]
          simp [encode]
          simp_all
          rename_i h a b sa exp1 sig sb sexp x heq1 heq
          by_cases sa <;> by_cases sb <;> simp_all <;> native_decide
        ·
          rename_i h da db sa exp1 sb exp sig x heq1 heq
          by_cases sa <;> by_cases sb <;> simp_all
        ·
          rename_i h a b sa ea siga sb eb sigb x2 x1 x heq1 heq
          by_cases sa <;> by_cases sb <;> simp_all
        }
      · {
        simp [divExactWith]
        split
        ·
          simp [roundTo]
          simp [encode]
          native_decide
        ·
          simp [roundTo]
          simp [encode]
          native_decide
        ·
          simp [roundTo]
          simp [encode]
          native_decide
        ·
          simp [roundTo]
          simp [encode]
          native_decide
        ·
          rename_i h a b sa sb exp sig heq1 heq
          by_cases sa <;> by_cases sb <;> simp_all
        ·
          rename_i h a b sa exp sig sb heq1 heq
          by_cases sa <;> by_cases sb <;> simp_all
        ·
          rename_i h a b sa exp1 sig sb exp x heq1 heq
          by_cases sa <;> by_cases sb <;> simp_all  <;>
          simp [roundTo] <;>
          simp [encode] <;>
          native_decide
        ·
          rename_i heq1 heq
          rename_i sb exp sig x
          rename_i h da db sa exp
          simp [roundTo]
          simp [encode]
          by_cases sa <;> by_cases sb <;> simp_all
        ·
          rename_i   h a b sa ea siga sb eb sigb x2 x1 x  heq1 heq
          split
          ·
            simp [roundTo]
            split
            ·
              simp [encode]; native_decide
            ·
              simp [encode]
              rename_i  s heq
              by_cases hs: s
              ·
                simp [hs]
                native_decide
              ·
                simp [hs]
                native_decide
            ·
              simp [encode]
              rename_i s exp heq
              by_cases hs : s
              ·
                simp [hs]
                simp_all
              ·
                simp [hs]
                simp_all
            ·
              rename_i  heq1  heq2  h d  s  e sig  x heq
              simp at heq
              have ⟨heql,heqm,helql⟩ := heq
              split
              ·
                simp_all
              ·
                simp_all
        }
   }
   ·
   {

   }



-- ── E. Sign rules (IEEE 754-2019 §6.3) ───────────────────────────────────────

/-- The product sign is XOR of operand signs (when result is not NaN). -/
theorem fmul_sign_xor {rm : RoundMode} {a b : F32}
    (hna : ¬a.isNaN) (hnb : ¬b.isNaN)
    (hza : ¬a.isZero) (hzb : ¬b.isZero)
    (hr  : ¬(F32.fmul rm a b).isNaN) :
    (F32.fmul rm a b).sign = (a.sign != b.sign) := by sorry

/-- The quotient sign is XOR of operand signs (when result is not NaN). -/
theorem fdiv_sign_xor {rm : RoundMode} {a b : F32}
    (hna : ¬a.isNaN) (hnb : ¬b.isNaN)
    (hza : ¬a.isZero) (hzb : ¬b.isZero)
    (hr  : ¬(F32.fdiv rm a b).isNaN) :
    (F32.fdiv rm a b).sign = (a.sign != b.sign) := by sorry

/-- When both addends share the same sign, so does a nonzero result. -/
theorem fadd_same_sign {rm : RoundMode} {a b : F32} {s : Bool}
    (hna : ¬a.isNaN) (hnb : ¬b.isNaN)
    (ha : a.sign = s) (hb : b.sign = s)
    (hr  : ¬(F32.fadd rm a b).isNaN)
    (hrz : ¬(F32.fadd rm a b).isZero) :
    (F32.fadd rm a b).sign = s := by sorry

-- ── F. Commutativity (follows from addExact_comm / mulExact_comm above) ───────

/-- fadd is commutative (bit-exact result). -/
theorem fadd_comm (rm : RoundMode) (a b : F32) :
    F32.fadd rm a b = F32.fadd rm b a := by 
    simp [fadd]
    simp [faddEx]
    rw [addExact_comm] -- this is in the other file

/-- fmul is commutative (bit-exact result). -/
theorem fmul_comm (rm : RoundMode) (a b : F32) :
    F32.fmul rm a b = F32.fmul rm b a := by sorry

-- ── G. Ordering (IEEE 754-2019 §5.10, §5.11) ─────────────────────────────────

/-- flt is irreflexive: a value is never strictly less than itself. -/
theorem flt_irrefl (a : F32) : F32.flt a a = false := by 
  simp [flt]
  split <;> simp_all

/-- flt is asymmetric. -/
theorem flt_asymm {a b : F32} (h : F32.flt a b) : F32.flt b a = false := by 
  simp [flt]
  split <;> simp_all

/-- flt is transitive. -/
theorem flt_trans {a b c : F32}
    (h1 : F32.flt a b) (h2 : F32.flt b c) : F32.flt a c := by 
    simp [flt]
    split <;> simp_all

/-- NaN comparisons always return false (IEEE 754 §5.11 "unordered"). -/
theorem flt_nan_l (a b : F32) (h : a.isNaN) : F32.flt a b = false := by 
  simp [flt]
  split  <;> simp_all

theorem flt_nan_r (a b : F32) (h : b.isNaN) : F32.flt a b = false := by 
  simp [flt]
  split <;> simp_all

theorem feq_nan_l (a b : F32) (h : a.isNaN) : F32.feq a b = false := by 
  simp [feq]
  simp_all
theorem feq_nan_r (a b : F32) (h : b.isNaN) : F32.feq a b = false := by
  simp [feq]
  simp_all


-- ── H. Cancellation and additive identity ─────────────────────────────────────

/-- x − x = ±0 for any finite non-NaN (IEEE 754 cancellation). -/
theorem fsub_self_isZero (rm : RoundMode) (a : F32) (h : ¬a.isNaN) (hi : ¬a.isInf) :
    (F32.fsub rm a a).isZero := by 
  simp [fsub]
  simp [faddEx]
  simp [negate]
  

/-- +0 is a right additive identity under IEEE equality (for non-NaN a). -/
theorem fadd_posZero_r (rm : RoundMode) (a : F32) (h : ¬a.isNaN) :
    F32.feq (F32.fadd rm a F32.posZero) a := by sorry

-- ── I. FMA: true single rounding (IEEE 754-2019 §5.4.1) ──────────────────────

/-- fma is definitionally equal to the first component of fmaEx
    (result with flags discarded). The rfl proof documents the exact pipeline. -/
theorem fma_is_single_rounded (rm : RoundMode) (a b c : F32) :
    F32.fma rm a b c = (F32.fmaEx rm a b c).1 := rfl

/-- The flags raised by fmaEx are the union of those from fmaExact and roundTo.
    This is the key invariant: flags are threaded faithfully through the pipeline. -/
theorem fmaEx_flags_eq (rm : RoundMode) (a b c : F32) :
    (F32.fmaEx rm a b c).2 =
    (fmaExact rm (F32.decode a) (F32.decode b) (F32.decode c)).2.merge
    (roundTo f32Fmt rm (fmaExact rm (F32.decode a) (F32.decode b) (F32.decode c)).1).2 := by
  simp [F32.fmaEx]

/-- fma ≠ fadd ∘ fmul in general: there exist inputs where the double-rounding
    in the sequential version differs from the single-rounded fma.
    Hint: try a = b = (1 + ulp(1)/2) and c = −1. -/
theorem fma_ne_mul_then_add :
    ∃ (a b c : F32),
      F32.fma .RNE a b c ≠ F32.fadd .RNE (F32.fmul .RNE a b) c := by
      sorry

-- ── J. Square root (IEEE 754-2019 §5.4.1, §6.3, §7.2) ───────────────────────

/-- fsqrt is definitionally equal to the first component of fsqrtEx. -/
theorem fsqrt_is_single_rounded (rm : RoundMode) (a : F32) :
    F32.fsqrt rm a = (F32.fsqrtEx rm a).1 := rfl

/-- √(NaN) = NaN (NaN propagation §6.2). -/
theorem fsqrt_nan (rm : RoundMode) (a : F32) (h : a.isNaN) :
    (F32.fsqrt rm a).isNaN := by
    simp [F32.fsqrt]
    simp [fsqrtEx]
    -- simp [isNaN] at h
    -- cases h
    -- rename_i right left
    simp [decode]
    rw [h]
    simp
    simp [sqrtExact]
    simp [roundTo]
    simp [encode]
    decide



/-- √(negative finite) raises invalidOp and returns NaN (§7.2). -/
theorem fsqrt_neg_isNaN (rm : RoundMode) (a : F32)
    (hs : a.sign = true) (hf : a.isFinite) (hz : ¬a.isZero) :
    (F32.fsqrt rm a).isNaN ∧ (F32.fsqrtEx rm a).2.invalidOp := by
    simp [isNaN]
    simp [fsqrt]
    simp [fsqrtEx]
    constructor
    ·
      simp [expIsMax]
      simp [mantIsZero]
      constructor
      ·
        simp [decode]
        split
        ·
          simp [sqrtExact]
          simp [roundTo]
          simp [encode]
          simp [expRaw]
          decide
        ·
          rename_i anotNan
          split
          ·
            simp [sqrtExact]
            split
            ·
              simp
              simp [roundTo]
              simp [encode]
              decide
            ·
             simp
             simp [roundTo]
             simp [encode]
             simp [pack]
             decide
            ·
              simp
              simp [roundTo]
              simp [encode]
              decide
            ·
              simp
              simp [roundTo]
              simp [encode]
              simp [pack]
              rename_i heq
              rename_i  ainf a1 s exp
              simp at heq
            ·
              simp
              simp [roundTo]
              simp [encode]
              decide
          · {
            rename_i anotinf
            simp [sqrtExact]
            split
            {
              simp
              simp [roundTo]
              simp [encode]
              decide
            }
            {
              simp
              simp [roundTo]
              simp [encode]
              simp [pack]
              decide
            }
            {
              simp
              simp [roundTo]
              simp [encode]
              decide
            }
            {
              rename_i a1 s exp df
              simp
              simp [roundTo]
              simp [encode]
              simp [pack]
              simp_all
              have ⟨left,right⟩ := df
              cases aNorm : a.isNormal
              ·
                simp [aNorm] at right
                have ⟨rr,ll⟩ := right
                simp [isNormal] at aNorm
                decide



}




}
        }










/-- √(-∞) raises invalidOp and returns NaN (§7.2). -/
theorem fsqrt_negInf_isNaN (rm : RoundMode) :
    (F32.fsqrt rm F32.negInf).isNaN ∧ (F32.fsqrtEx rm F32.negInf).2.invalidOp := by
    have neg_inf_is_not_nan : negInf.isNaN = false := by native_decide
    have neg_inf_is_inf : negInf.isInf = true := by native_decide
    have neg_inf_not_zero : negInf.isZero = false := by native_decide
    have neg_inf_sign_true : negInf.sign = true := by native_decide
    constructor
    ·
      simp [fsqrt]
      simp [fsqrtEx]
      simp [decode]
      rw [neg_inf_is_not_nan, neg_inf_is_inf, neg_inf_not_zero,neg_inf_sign_true]
      simp
      simp [sqrtExact]
      simp [roundTo]
      simp[encode]
      decide
    ·
      simp [fsqrtEx]
      simp [decode]
      rw [neg_inf_is_not_nan, neg_inf_is_inf, neg_inf_not_zero,neg_inf_sign_true]
      simp
      simp [sqrtExact]
      simp [roundTo]
      native_decide



/-- √(+∞) = +∞ (no exception). -/
theorem fsqrt_posInf (rm : RoundMode) :
    F32.fsqrt rm F32.posInf = F32.posInf := by
    simp [fsqrt ]
    simp [fsqrtEx]
    simp [decode]
    have pos_inf_not_nan : posInf.isNaN = false := by native_decide
    have pos_inf_inf : posInf.isInf = true := by native_decide
    have pos_inf_nz : posInf.isZero = false := by native_decide
    have pos_inf_sign : posInf.sign = false := by native_decide
    rw [pos_inf_not_nan,pos_inf_inf,pos_inf_nz]
    simp
    unfold sqrtExact
    simp [pos_inf_sign]
    simp [roundTo]
    simp [encode]
    simp [pack]
    decide



/-- √(+0) = +0 (IEEE 754 §6.3). -/
theorem fsqrt_posZero (rm : RoundMode) :
    F32.fsqrt rm F32.posZero = F32.posZero := by
    have pos_zero_not_nan : posZero.isNaN = false := by native_decide
    have pos_zero_is_zero : posZero.isZero = true := by native_decide
    have pos_zero_not_inf : posZero.isInf = false := by native_decide
    have pos_zero_sign_false : posZero.sign = false := by native_decide
    simp [fsqrt]
    simp [fsqrtEx]
    simp [decode]
    rw [pos_zero_not_nan, pos_zero_is_zero, pos_zero_not_inf,pos_zero_sign_false]
    simp
    simp [sqrtExact]
    simp [roundTo]
    simp [encode]
    decide

/-- √(−0) = −0 (IEEE 754 §6.3: sign of zero is preserved). -/
theorem fsqrt_negZero (rm : RoundMode) :
    F32.fsqrt rm F32.negZero = F32.negZero := by
    have neg_zero_not_nan : negZero.isNaN = false := by native_decide
    have neg_zero_is_zero : negZero.isZero = true := by native_decide
    have neg_zero_not_inf : negZero.isInf = false := by native_decide
    have neg_zero_sign_true : negZero.sign = true := by native_decide
    simp [fsqrt]
    simp [fsqrtEx]
    simp [decode ]
    rw [neg_zero_not_nan, neg_zero_is_zero, neg_zero_not_inf, neg_zero_sign_true]
    simp
    simp [sqrtExact]
    simp [roundTo]
    simp [encode]
    decide


/-- The result of fsqrt is always non-negative when it is not NaN. -/
theorem fsqrt_nonneg (rm : RoundMode) (a : F32) (h : ¬(F32.fsqrt rm a).isNaN) (anNeg :
a.sign = false) :
    (F32.fsqrt rm a).sign = false := by
   -- simp at h
   -- simp [isNaN] at h
    cases ha : classify a
    ·
      have aZ : a.isZero = true := by
                have bj := biject_class_zero a
                have ⟨left,right⟩ := bj
                rw [ ha] at right
                simp at right
                exact right
      simp [fsqrt]
      simp [fsqrtEx]
      simp[ sqrtExact ]
      split
      .
        simp
        simp [roundTo]
        simp [encode]
        decide
      ·
        simp
        simp [roundTo]
        simp [encode]
        simp [pack]
        decide
      ·
        simp
        simp [roundTo]
        simp [encode]
        decide
      ·
        simp
        simp [roundTo]
        simp [encode]
        simp [pack]
        rename_i df s exp ad
        by_cases hs: s
        ·
          rw [hs]
          simp_all
          simp [decode] at ad
          simp_all
          have a_notNaN :a.isNaN = false :=  isNaN_false_of_isZero a aZ
          have a_notInf :a.isInf = false := isInf_false_of_isZero a aZ
          rw [a_notNaN,a_notInf] at ad
          simp_all
        ·
          simp_all
          native_decide
    ·
      simp [fsqrt]
      simp [fsqrtEx]
      simp [decode]
      split
      ·
        simp [sqrtExact]
        simp [roundTo]
        simp [encode]
        native_decide
      ·
        rename_i hnan
        simp_all
        split
        ·
          simp [sqrtExact]
          simp [roundTo]
          simp [encode]
          native_decide
        ·
          split
          ·
            simp [sqrtExact]
            simp [roundTo]
            simp [encode]
            native_decide
          ·
            simp [sqrtExact]
            simp [roundTo]
            simp [encode]
            split
            ·
              native_decide
            ·
              rename_i heq s

              by_cases heq
              ·
                simp_all
              ·
                rename_i heq
                simp at heq
                rw [heq]
                native_decide

    ·


/-- The flags from fsqrtEx are the union of those from sqrtExact and roundTo
    (same flag-threading invariant as fmaEx). -/
theorem fsqrtEx_flags_eq (rm : RoundMode) (a : F32) :
    (F32.fsqrtEx rm a).2 =
    (sqrtExact (F32.decode a)).2.merge
    (roundTo f32Fmt rm (sqrtExact (F32.decode a)).1).2 := by
  simp [F32.fsqrtEx]

end F32


-- ─────────────────────────────────────────────────────────────────────────────
-- §12  Hardware Oracle Interface
-- ─────────────────────────────────────────────────────────────────────────────
-- Exported functions called from Python via ctypes.
-- The API is intentionally identical to the previous version.

namespace F32.Oracle

@[export f32_add]
def f32_add (a b : UInt32) (round : UInt8) : UInt32 :=
  let fa : F32 := BitVec.ofNat 32 a.toNat
  let fb : F32 := BitVec.ofNat 32 b.toNat
  (F32.fadd (classifyRounding round) fa fb).toNat.toUInt32

@[export f32_mul]
def f32_mul (a b : UInt32) (round : UInt8) : UInt32 :=
  let fa : F32 := BitVec.ofNat 32 a.toNat
  let fb : F32 := BitVec.ofNat 32 b.toNat
  (F32.fmul (classifyRounding round) fa fb).toNat.toUInt32

@[export f32_fma]
def f32_fma (a b c : UInt32) (round : UInt8) : UInt32 :=
  let fa : F32 := BitVec.ofNat 32 a.toNat
  let fb : F32 := BitVec.ofNat 32 b.toNat
  let fc : F32 := BitVec.ofNat 32 c.toNat
  (F32.fma (classifyRounding round) fa fb fc).toNat.toUInt32

@[export float32_classify]
def classify (a : UInt32) : UInt8 :=
  let f : F32 := BitVec.ofNat 32 a.toNat
  if f.isNaN        then 0
  else if f.isInf   then 1
  else if f.isZero  then 2
  else if f.isSubnormal then 3
  else 4   -- normal

-- Sanity checks (evaluated at build time)
-- add
#eval (f32_add 0x3F800000 0x3F800000 0x0).toBitVec.toHex  -- 1.0+1.0 = 2.0 → "40000000"
#eval (f32_add 0x3FC00000 0x3FC00000 0x0).toBitVec.toHex  -- 1.5+1.5 = 3.0 → "40400000"
#eval (f32_add 0x1B407ccc 0x1B407CCC 0x00).toBitVec.toHex
-- mul
#eval (f32_mul 0x3F800000 0x3F800000 0x0).toBitVec.toHex  -- 1.0*1.0 = 1.0 → "3f800000"
#eval (f32_mul 0x40000000 0x40000000 0x0).toBitVec.toHex  -- 2.0*2.0 = 4.0 → "40800000"
-- fma: 2.0*3.0+4.0 = 10.0
#eval (f32_fma 0x40000000 0x40400000 0x40800000 0x0).toBitVec.toHex -- → "41200000"
-- classify
#eval classify 0x3F800000  -- normal → 4
#eval classify 0x00000000  -- zero   → 2
#eval classify 0x7F800000  -- inf    → 1
#eval classify 0x7FC00000  -- NaN    → 0
#eval classify 0x00000001  -- subnormal → 3

end F32.Oracle
