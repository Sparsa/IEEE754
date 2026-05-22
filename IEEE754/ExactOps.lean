/-
  IEEE754.ExactOps
  ================
  §4  Common exact arithmetic (addExact, mulExact, divExact, fmaExact, sqrtExact)
  §5  Common rounding (roundTo)
-/

import IEEE754.Basic

open BitVec


-- ─────────────────────────────────────────────────────────────────────────────
-- §4  Common exact arithmetic
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
def findLeadingBit (v : Nat) (maxPos : Nat) : Nat :=
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
    Returns both the rounded result and the exception flags raised. -/
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
