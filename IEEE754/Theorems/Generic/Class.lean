/-
  IEEE754.Theorems.Generic.Class
  ==============================
  Typeclass `IEEEFloat` for any IEEE 754 binary float format (F16, F32, F64, F128, …).

  An instance must supply:
    • `fmt`           — format descriptor (M mantissa bits, E exponent bits, bias)
    • decode / encode — round-trip between bit-patterns and DecodedFloat
    • sign / isNaN / isInf / isZero / isNormal / isSubnormal — classification
    • faddEx / fmulEx / fdivEx / fmaEx / fsqrtEx — flag-returning arithmetic
  and six core axioms that pin down how those pieces fit together.

  Every generic theorem in this directory follows from those axioms alone;
  no bit-level details about any specific format are needed.
-/

import IEEE754.ExactOps
import IEEE754.Theorems.F32.Props   -- for roundTo_sign_preserved (format-generic theorem)

open DecodedFloat

/-- A Lean type `α` carries IEEE 754 floats of the format described by `fmt`.
    Typical instances: `F32` (`f32Fmt`) and `F64` (`f64Fmt`). -/
class IEEEFloat (α : Type) where
  /-- The IEEE 754 format descriptor for this type. -/
  fmt         : FPFormat
  /-- Decode a raw bit-pattern to an exact rational or special value. -/
  decode      : α → DecodedFloat
  /-- Encode a (pre-rounded) DecodedFloat back to a raw bit-pattern. -/
  encode      : DecodedFloat → α
  /-- Extract the sign bit. -/
  sign        : α → Bool
  isNaN       : α → Bool
  isInf       : α → Bool
  isZero      : α → Bool
  isNormal    : α → Bool
  isSubnormal : α → Bool
  /-- Flag-returning arithmetic (primary implementations). -/
  faddEx  : RoundMode → α → α → α × ExcFlags
  fmulEx  : RoundMode → α → α → α × ExcFlags
  fdivEx  : RoundMode → α → α → α × ExcFlags
  fmaEx   : RoundMode → α → α → α → α × ExcFlags
  fsqrtEx : RoundMode → α → α × ExcFlags
  /-- Axiom A1: encoding preserves the dfSign of a DecodedFloat. -/
  encode_dfSign  : ∀ (df : DecodedFloat), sign (encode df) = df.dfSign
  /-- Axiom A2: for non-NaN floats the raw sign bit equals the decoded dfSign. -/
  sign_eq_dfSign : ∀ (a : α), ¬isNaN a → sign a = (decode a).dfSign
  /-- Axiom A3: isNaN iff decode produces .nan. -/
  isNaN_iff      : ∀ (a : α), isNaN a ↔ decode a = .nan
  /-- Axiom A4: faddEx = decode → addExact → roundTo → encode. -/
  faddEx_spec : ∀ (rm : RoundMode) (a b : α),
    (faddEx rm a b).1 =
      encode (roundTo fmt rm (addExact rm (decode a) (decode b)).1).1
  /-- Axiom A5: fmulEx = decode → mulExact → roundTo → encode. -/
  fmulEx_spec : ∀ (rm : RoundMode) (a b : α),
    (fmulEx rm a b).1 =
      encode (roundTo fmt rm (mulExact (decode a) (decode b)).1).1
  /-- Axiom A6: fdivEx = decode → divExact → roundTo → encode. -/
  fdivEx_spec : ∀ (rm : RoundMode) (a b : α),
    (fdivEx rm a b).1 =
      encode (roundTo fmt rm (divExact (decode a) (decode b)).1).1
  /-- Axiom A7: encoding .nan always produces a NaN bit-pattern. -/
  encode_nan_isNaN : isNaN (encode .nan) = true

namespace IEEEFloat

variable {α : Type} [IEEEFloat α]

/-- Result-only addition (exception flags dropped). -/
def fadd  (rm : RoundMode) (a b : α) : α := (faddEx rm a b).1
/-- Result-only multiplication. -/
def fmul  (rm : RoundMode) (a b : α) : α := (fmulEx rm a b).1
/-- Result-only division. -/
def fdiv  (rm : RoundMode) (a b : α) : α := (fdivEx rm a b).1
/-- Result-only square root. -/
def fsqrt (rm : RoundMode) (a : α)   : α := (fsqrtEx rm a).1

end IEEEFloat
