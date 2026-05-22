/-
  IEEE754.Conversions
  ===================
  §10  Conversions (F32 ↔ F64, F32 ↔ Int)
-/

import IEEE754.F32.Defs
import IEEE754.F64.Defs

open BitVec

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
