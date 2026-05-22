/-
  IEEE754.F64.Defs
  ================
  §8  F64 — Format-specific bitvector layer
  §9  F64 — Top-level composed operations
-/

import IEEE754.ExactOps

open BitVec

-- F64 abbrev is defined in IEEE754.F32.Defs, but we re-declare it here
-- so F64/Defs.lean is self-contained (parallel to F32/Defs.lean).
-- If both are imported together the `abbrev` is idempotent.
abbrev F64 := BitVec 64

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
