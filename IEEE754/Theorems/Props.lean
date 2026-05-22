/-
  IEEE754.Theorems.Props
  ======================
  §11b  Sign/comparison properties, addExact/mulExact commutativity,
        roundTo correctness, NaN/Inf propagation through exact ops
-/

import IEEE754.Theorems.Classification
import IEEE754.Conversions

open BitVec

namespace F32

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

-- ─────────────────────────────────────────────────────────────────────────────
-- §11b  Generic DecodedFloat / rounding correctness
-- ─────────────────────────────────────────────────────────────────────────────

-- ── Commutativity of exact arithmetic ────────────────────────────────────────

theorem expb_leq_expa_imp_zero (expb expa : Int) : expb ≤ expa → (expb - expa).toNat = 0 := by
  intro h
  omega

theorem addExact_comm (rm : RoundMode) (a b : DecodedFloat) :
    addExact rm a b = addExact rm b a := by
    induction a with
    | finite signa expa siga =>
      induction b with
      | finite signb expb sigb =>
        simp [addExact]
        split
        ·{
          rename_i signa_signb_zero
          have ⟨signa_z, signb_z⟩ := signa_signb_zero
          simp [signa_z,signb_z]
          ac_rfl
        }
        ·{
          rename_i siga_sigb_and_nz
          have sigb_siba_and_nz : ¬ (sigb = 0 ∧ siga = 0) := by
            rwa [And.comm]
          simp at siga_sigb_and_nz
          simp at sigb_siba_and_nz
          split
          ·{
            rename_i siga_z
            simp_all
          }
          ·{
            simp_all
            split
            ·{ rfl }
            ·{
              split
              ·{
                simp_all
                constructor
                ·{
                  split
                  ·{
                    simp_all
                    intro hexpbleqexpa
                    omega
                  }
                  ·{
                    simp_all
                    intro
                    omega
                  }
                }
                ·{
                  rename_i signa_eq_signb sigb_nz siga_nz
                  have h1 : (if expa ≤ expb then expa else expb) = (if expb ≤ expa then expb else expa) := by
                    split
                    · split
                      · omega
                      · omega
                    · split
                      · omega
                      · omega
                  rw [h1]
                  ac_rfl
                }
              }
              ·{
                have h1 : (if expa ≤ expb then expa else expb) = (if expb ≤ expa then expb else expa) := by
                    split
                    · split
                      · omega
                      · omega
                    · split
                      · omega
                      · omega
                rename_i siganz sigbnz signa_neq_signb
                rw [eq_comm] at signa_neq_signb
                simp [signa_neq_signb]
                rw [h1]
                split
                ·{
                  simp_all
                  split
                  ·{
                    simp_all
                    split
                    ·{
                      simp_all
                      rename_i sig1 sig2 sig3
                      have siga_bit_expa_expb : siga <<< (expa - expb).toNat ≤ sigb := by
                        omega
                      simp [siga_bit_expa_expb]
                    }
                    ·{
                      rename_i sig1 sig2 sig3
                      have siga_bit_expa_expb_neq : ¬(siga <<< (expa - expb).toNat ≤ sigb) := by
                        omega
                      simp [siga_bit_expa_expb_neq]
                      intro
                      contradiction
                    }
                  }
                  ·{
                    simp_all
                    split <;>
                    ·{
                      rename_i sig1 sig2 sig3
                      have siga_bit_expa_expb_sigb : siga <<< (expa -expb).toNat ≤ sigb := by
                        omega
                      simp [siga_bit_expa_expb_sigb]
                      intro hh
                      contradiction
                    }
                  }
                }
                ·{
                  simp_all
                  split
                  ·{
                    simp_all
                    split
                    ·{
                      simp_all
                      rename_i sig1 sig2 sig3
                      have siga_leq_sigb_bit_expa_expb : siga ≤ sigb  <<< (expb - expa).toNat  := by
                        omega
                      simp [siga_leq_sigb_bit_expa_expb]
                    }
                    ·{
                      rename_i sig1 sig2 sig3
                      have siga_leq_sigb_bit_expa_expb_neq : ¬(siga ≤ sigb <<< (expb - expa).toNat) := by
                        omega
                      simp [siga_leq_sigb_bit_expa_expb_neq]
                      intro hh
                      contradiction
                    }
                  }
                  ·{
                    simp_all
                    split <;>
                    ·{
                      rename_i sig1 sig2 sig3
                      have siga_leq_siga_expa_expb : siga ≤ sigb <<< (expb -expa).toNat  := by
                        omega
                      simp [siga_leq_siga_expa_expb]
                      intro hh
                      contradiction
                    }
                  }
                }
              }
            }
          }
        }
      | inf s =>
        simp [addExact]
      | nan => simp [addExact]
    | inf s =>
      induction b with
      | finite sign exp sig  =>
        simp [addExact]
      | inf sign =>
        simp [addExact]
        by_cases hss:  s = sign
        . simp [hss]
        · simp [hss]
          rw [eq_comm]
          exact hss
      | nan =>
        simp [addExact]
    | nan =>
        induction b with
        | finite sign exp sig =>
          simp[addExact]
        | inf sign =>
          simp [addExact]
        | nan =>
          simp [addExact]


/-- mulExact is commutative: a × b = b × a (before rounding). -/
theorem mulExact_comm (a b : DecodedFloat) :
    mulExact a b = mulExact b a := by
    induction a with
    |  finite signa expa siga =>
        induction b with
        | finite signb expb sigb =>
          simp [mulExact]; constructor
          · {
            simp [bne]
            simp [Bool.beq_comm]
            }
          · {
            constructor <;>
            ac_rfl
            }
        | inf signb  =>
          simp [mulExact]
          split
          · { simp_all }
          · { simp_all }
          · { simp_all }
          · { simp_all }
          · { simp_all }
          · { simp_all }
          · { simp_all; simp [bne]; simp [Bool.beq_comm] }
          · { simp_all }
        | nan =>
          simp [mulExact]

    | inf signa =>
      simp [mulExact]
      split
      · { simp_all }
      · { simp_all }
      · { simp_all }
      · { simp_all }
      · { simp_all; simp [bne]; simp [Bool.beq_comm] }
      · { simp_all; simp [bne]; simp [Bool.beq_comm] }
      · { simp_all }
      · { simp_all }
    | nan =>
      simp [mulExact]
      split
      · { simp_all }
      · { simp_all }
      · { simp_all }
      · { simp_all }
      · { simp_all }
      · { simp_all }
      · { simp_all }
      · { simp_all }

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
private theorem ite_fst {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).1 = if p then a.1 else b.1 := by
  by_cases hp : p <;> simp [hp]

private theorem roundTo_false_dfSign (fmt : FPFormat) (rm : RoundMode)
    (d : DecodedFloat) (hs : d.dfSign = false) :
    (roundTo fmt rm d).1.dfSign = false := by
  match d with
  | .nan             => simp [roundTo, DecodedFloat.dfSign]
  | .inf false       => simp [roundTo, DecodedFloat.dfSign]
  | .inf true        => simp [DecodedFloat.dfSign] at hs
  | .finite false _ 0        => simp [roundTo, DecodedFloat.dfSign]
  | .finite false e (_ + 1) =>
    simp only [roundTo, ite_fst, DecodedFloat.dfSign]
    grind
  | .finite true _ _ => simp [DecodedFloat.dfSign] at hs

private theorem roundTo_true_dfSign (fmt : FPFormat) (rm : RoundMode)
    (d : DecodedFloat) (hs : d.dfSign = true) :
    (roundTo fmt rm d).1.dfSign = true := by
  match d with
  | .nan                    => simp [DecodedFloat.dfSign] at hs
  | .inf false              => simp [DecodedFloat.dfSign] at hs
  | .inf true               => simp [roundTo, DecodedFloat.dfSign]
  | .finite false _ 0       => simp [DecodedFloat.dfSign] at hs
  | .finite false _ (_ + 1) => simp [DecodedFloat.dfSign] at hs
  | .finite true _ _        =>
    simp only [roundTo, ite_fst, DecodedFloat.dfSign]
    grind

theorem roundTo_sign_preserved (fmt : FPFormat) (rm : RoundMode)
    (d: DecodedFloat) :
    (roundTo fmt rm d).1.dfSign = d.dfSign := by
    cases dh: d.dfSign
    ·{ apply roundTo_false_dfSign fmt rm d dh }
    ·{ apply roundTo_true_dfSign fmt rm d dh }

/-- roundTo is idempotent: rounding an already-rounded value produces no new flags
    and the same result. -/
theorem roundTo_idempotent (fmt : FPFormat) (rm : RoundMode) (d : DecodedFloat) :
    roundTo fmt rm (roundTo fmt rm d).1 = ((roundTo fmt rm d).1, ExcFlags.empty) := by
    sorry

-- ── NaN / Inf propagation through addExact / mulExact ────────────────────────

theorem addExact_nan_l (rm : RoundMode) (b : DecodedFloat) :
    addExact rm .nan b = (.nan, ExcFlags.empty) := by
    cases b
    · simp [addExact]
    · simp [addExact]
    · simp [addExact]

theorem addExact_nan_r (rm : RoundMode) (a : DecodedFloat) :
    addExact rm a .nan = (.nan, ExcFlags.empty) := by
    cases a
    · simp [addExact]
    · simp [addExact]
    · simp [addExact]

theorem mulExact_nan_l (b : DecodedFloat) :
    mulExact .nan b = (.nan, ExcFlags.empty) := by
    cases b
    · simp [mulExact]
    · simp [mulExact]
    · simp [mulExact]

theorem mulExact_nan_r (a : DecodedFloat) :
    mulExact a .nan = (.nan, ExcFlags.empty) := by
    cases a
    · simp [mulExact]
    · simp [mulExact]
    · simp [mulExact]

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
