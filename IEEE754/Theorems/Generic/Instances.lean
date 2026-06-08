/-
  IEEE754.Theorems.Generic.Instances
  ====================================
  `IEEEFloat` instances for F32 and F64.

  Each instance proves the six axioms from existing F32/F64 definitions.
  Axioms A4–A6 (faddEx_spec, fmulEx_spec, fdivEx_spec) are definitionally
  true — the Lean elaborator proves them by `rfl`.
  Axioms A1–A3 require a few lines each.

  These files are NOT touched; all new code lives in Generic/.
-/

import IEEE754.Theorems.Generic.Class
import IEEE754.Theorems.F32.Sign    -- encode_dfSign for F32
import IEEE754.Theorems.F64.Sign    -- for F64 helpers (encode_dfSign proved there)

open DecodedFloat

-- ─────────────────────────────────────────────────────────────────────────────
-- F32 instance
-- ─────────────────────────────────────────────────────────────────────────────

/-- F32 satisfies `IEEEFloat` with `f32Fmt`. -/
instance : IEEEFloat F32 where
  fmt         := f32Fmt
  decode      := F32.decode
  encode      := F32.encode
  sign        := F32.sign
  isNaN       := F32.isNaN
  isInf       := F32.isInf
  isZero      := F32.isZero
  isNormal    := F32.isNormal
  isSubnormal := F32.isSubnormal
  faddEx      := F32.faddEx
  fmulEx      := F32.fmulEx
  fdivEx      := F32.fdivEx
  fmaEx       := F32.fmaEx
  fsqrtEx     := F32.fsqrtEx

  -- A1: encode preserves dfSign — proved in F32/Sign.lean
  encode_dfSign := F32.encode_dfSign

  -- A2: sign bit = dfSign of decoded value (for non-NaN)
  -- `F32.sign_of_decode` is private in F32/Sign.lean so we re-prove it here.
  sign_eq_dfSign := fun a hna => by
    simp only [F32.sign, F32.decode]
    split_ifs with h1 h2 h3
    · exact absurd h1 hna
    · simp [DecodedFloat.dfSign]
    · simp [DecodedFloat.dfSign]
    · simp [DecodedFloat.dfSign]

  -- A3: isNaN ↔ decode = .nan
  isNaN_iff := fun a => by
    constructor
    · intro h; simp [F32.decode, h]
    · intro h
      by_contra hna
      simp only [F32.decode, hna, ite_false] at h
      split_ifs at h <;> simp_all

  -- A4–A6: definitionally true (fXXEx is decode → exactOp → roundTo → encode)
  faddEx_spec := fun rm a b => rfl
  fmulEx_spec := fun rm a b => rfl
  fdivEx_spec := fun rm a b => rfl

-- ─────────────────────────────────────────────────────────────────────────────
-- F64 instance
-- ─────────────────────────────────────────────────────────────────────────────

/-- F64 satisfies `IEEEFloat` with `f64Fmt`. -/
instance : IEEEFloat F64 where
  fmt         := f64Fmt
  decode      := F64.decode
  encode      := F64.encode
  sign        := F64.sign
  isNaN       := F64.isNaN
  isInf       := F64.isInf
  isZero      := F64.isZero
  isNormal    := F64.isNormal
  isSubnormal := F64.isSubnormal
  faddEx      := F64.faddEx
  fmulEx      := F64.fmulEx
  fdivEx      := F64.fdivEx
  fmaEx       := F64.fmaEx
  fsqrtEx     := F64.fsqrtEx

  -- A1: encode preserves dfSign
  -- This mirrors F32.encode_dfSign; the F64 version needs to be proved once
  -- in F64/Sign.lean (pending) and then referenced here.
  encode_dfSign := fun df => by
    cases df with
    | nan => simp [F64.encode, F64.qNaN, F64.sign, F64.pack]; decide
    | inf s => simp [F64.encode, F64.sign, F64.pack, DecodedFloat.dfSign]; cases s <;> decide
    | finite s e sig =>
      simp only [F64.encode, DecodedFloat.dfSign]
      split
      · -- sig = 0 case
        simp [F64.sign, F64.pack]; cases s <;> decide
      · split
        · -- biasedExp ≤ 0 (subnormal output)
          simp [F64.sign, F64.pack]; cases s <;> decide
        · split
          · -- overflow to inf
            simp [F64.sign, F64.posInf, F64.negInf, F64.pack]; cases s <;> decide
          · -- normal output
            simp [F64.sign, F64.pack]; cases s <;> decide

  -- A2: sign bit = dfSign for non-NaN F64
  sign_eq_dfSign := fun a hna => by
    simp only [F64.sign, F64.decode]
    split_ifs with h1 h2 h3
    · exact absurd h1 hna
    · simp [DecodedFloat.dfSign]
    · simp [DecodedFloat.dfSign]
    · simp [DecodedFloat.dfSign]

  -- A3: isNaN ↔ decode = .nan for F64
  isNaN_iff := fun a => by
    constructor
    · intro h; simp [F64.decode, h]
    · intro h
      by_contra hna
      simp only [F64.decode, hna, ite_false] at h
      split_ifs at h <;> simp_all

  -- A4–A6: definitionally true
  faddEx_spec := fun rm a b => rfl
  fmulEx_spec := fun rm a b => rfl
  fdivEx_spec := fun rm a b => rfl
