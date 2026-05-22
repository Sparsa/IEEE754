/-
  IEEE754.F32.Defs
  ================
  §6  F32 — Format-specific bitvector layer (decode, encode, fields, constants, comparison)
  §7  F32 — Top-level composed operations (fadd, fmul, fdiv, fma, fsqrt)
-/

import IEEE754.ExactOps

open BitVec

/-- IEEE 754 single-precision float as a 32-bit vector. -/
abbrev F32 := BitVec 32

namespace F32

-- ── Constants ────────────────────────────────────────────────────────────────
def SIGN_WIDTH  : Nat := 1
def EXP_WIDTH   : Nat := 8
def MANT_WIDTH  : Nat := 23
def BIAS        : Int := 127

-- ── Field extraction ─────────────────────────────────────────────────────────

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
  else if a.isZero then !b.sign
  else if b.isZero then a.sign
  else
    match a.sign, b.sign with
    | true,  false => true
    | false, true  => false
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
    let rawExp : Int := if f.isNormal then f.expRaw.toNat else 1
    let e      : Int := rawExp - 127 - 23
    .finite f.sign e f.significand.toNat

-- ── Encode: DecodedFloat → BitVec 32 ─────────────────────────────────────────

/-- Encode a (already-rounded) DecodedFloat into a raw F32 bit pattern.
    This is the "Encode" box in the diagram. -/
def encode (d : DecodedFloat) : F32 :=
  match d with
  | .nan    => F32.qNaN
  | .inf s  => F32.pack s (BitVec.allOnes 8) 0
  | .finite s _ 0 => F32.pack s 0 0
  | .finite s e sig =>
    let leadPos := findLeadingBit sig (sig.log2 + 1)
    let biasedExp : Int := e + (leadPos : Int) + 127
    if biasedExp <= 0 then
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

-- ── Result-only aliases ───────────────────────────────────────────────────────

def fadd  (rm : RoundMode) (a b : F32) : F32 := (F32.faddEx rm a b).1
def fsub  (rm : RoundMode) (a b : F32) : F32 := (F32.faddEx rm a b.negate).1
def fmul  (rm : RoundMode) (a b : F32) : F32 := (F32.fmulEx rm a b).1
def fdiv  (rm : RoundMode) (a b : F32) : F32 := (F32.fdivEx rm a b).1
def fma   (rm : RoundMode) (a b c : F32) : F32 := (F32.fmaEx rm a b c).1
def fsqrt (rm : RoundMode) (a : F32) : F32 := (F32.fsqrtEx rm a).1

end F32
