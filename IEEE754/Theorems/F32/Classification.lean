/-
  IEEE754.Theorems.Classification
  ================================
  §11a  Classification properties, exclusivity lemmas, biject_class_* theorems
-/

import IEEE754.F32.Defs

open BitVec

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

theorem finite_classify (f : F32) (hNaN : f.isNaN = false) (hInf: f.isInf = false) :
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

theorem expZero_ne_expMax (f : F32) :
    ¬(f.expIsZero = true ∧ f.expIsMax = true) := by
  simp [expIsZero, expIsMax]
  intro h; simp [h]

theorem isZero_false_of_isSubnormal (f : F32) (h : f.isSubnormal = true) :
    f.isZero = false := by
  simp [isZero, isSubnormal] at *
  obtain ⟨hexp, hmant⟩ := h
  simp [hexp, hmant]

theorem isZero_false_of_isNormal (f : F32) (h : f.isNormal = true) :
    f.isZero = false := by
  simp [isZero, isNormal, expIsZero, expIsMax] at *
  obtain ⟨hne0, _⟩ := h
  cases hm : f.mantIsZero <;> simp [hne0]

theorem isZero_false_of_isInf (f : F32) (h : f.isInf = true) :
    f.isZero = false := by
  simp [isZero, isInf, expIsZero, expIsMax] at *
  obtain ⟨left, right⟩ := h
  intro hzero
  rw [left] at hzero
  contradiction

theorem isZero_false_of_isNaN (f : F32) (h : f.isNaN = true) :
    f.isZero = false := by
  simp [isZero, isNaN, expIsZero, expIsMax] at *
  obtain ⟨hmax, _⟩ := h
  intro hzero
  rw [hmax] at hzero
  contradiction

theorem isSubnormal_false_of_isNormal (f : F32) (h : f.isNormal = true) :
    f.isSubnormal = false := by
  simp [isSubnormal, isNormal, expIsZero] at *
  intros h2
  obtain ⟨expraw_nz, exp_nomax⟩ := h
  contradiction

theorem isSubnormal_false_of_isInf (f : F32) (h : f.isInf = true) :
    f.isSubnormal = false := by
  simp [isSubnormal, isInf, expIsZero, expIsMax] at *
  obtain ⟨hmax, mantissa_max⟩ := h
  intro hzero
  rw [hmax] at hzero
  contradiction

theorem isSubnormal_false_of_isNaN (f : F32) (h : f.isNaN = true) :
    f.isSubnormal = false := by
  simp [isSubnormal, isNaN, expIsZero, expIsMax] at *
  obtain ⟨hmax, _⟩ := h
  intro hzero
  rw [hmax] at hzero
  contradiction

theorem isNormal_false_of_isInf (f : F32) (h : f.isInf = true) :
    f.isNormal = false := by
  simp [isNormal, isInf, expIsMax] at *
  intros exp_zero
  exact h.1

theorem isNormal_false_of_isNaN (f : F32) (h : f.isNaN = true) :
    f.isNormal = false := by
  simp [isNormal, isNaN, expIsMax] at *
  intros
  exact h.1

theorem isInf_false_of_isNaN (f : F32) (h : f.isNaN = true) :
    f.isInf = false := by
  simp [isInf, isNaN, mantIsZero] at *
  intros
  obtain ⟨ _, mant_nonzero⟩ := h
  exact mant_nonzero

theorem isInf_false_of_isZero (f : F32) (h : f.isZero = true) :
  f.isInf = false := by
  simp [isInf, isZero ] at *
  intros h
  rename_i h2
  simp [expIsZero,expIsMax] at *
  cases h2
  rename_i right left
  rw [right] at h
  contradiction

theorem isInf_false_of_isFinite (f:F32) (h:f.isFinite = true) : f.isInf = false := by
  simp [isInf, isFinite, expIsMax] at *
  intro h1
  rw [h1] at h
  contradiction

theorem isInf_false_of_isNormal (f : F32) (h : f.isNormal = true) :
    f.isInf = false := by
  simp [isInf,  mantIsZero,isNormal] at *
  have ⟨exp_nz,exp_max⟩ := h
  intros h1
  simp_all

theorem isInf_false_of_isSubnormal (f:F32) (h : f.isSubnormal = true) :
  f.isInf = false := by
  simp [isInf,mantIsZero,isSubnormal] at *
  have ⟨hl,hr⟩ := h
  intros haa
  exact hr

theorem isNormal_false_of_isSubnormal (f:F32) (h: f.isSubnormal = true) :
  f.isNormal = false := by
  simp [isNormal, isSubnormal] at *
  intros hh
  have ⟨hl,hr⟩ := h
  simp_all

theorem isNaN_false_of_isInf (f:F32) (h:f.isInf = true) :
  f.isNaN = false := by
  simp [isNaN,isInf] at *
  obtain ⟨expMax,mantZ⟩ := h
  intros h1
  exact mantZ

theorem isNaN_false_of_isZero (f:F32) (h:f.isZero = true) :
  f.isNaN = false := by
  simp [isNaN,isZero] at *
  have ⟨expZero,mantZero⟩ := h
  intros h1
  exact mantZero

theorem isNaN_false_of_isSubnormal (f:F32) (h:f.isSubnormal = true) :
  f.isNaN = false := by
  simp [isNaN]
  simp [isSubnormal] at h
  have ⟨expz,mantz⟩ := h
  intros h2
  simp [expIsZero] at expz
  simp [expIsMax] at h2
  rw [expz] at h2
  contradiction

theorem isNaN_false_of_isNormal (f:F32) (h: f.isNormal = true):
  f.isNaN = false := by
  simp [isNaN]
  simp [isNormal] at h
  have ⟨hl,hr⟩ := h
  intro hh
  simp_all

theorem isNaN_false_of_isFinite (f:F32) (h: f.isFinite = true) :
  f.isNaN = false := by
  simp [isNaN, isFinite] at *
  intro h1
  simp_all


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
    | true  => rfl
    | false =>
      rw [hZ] at h
      simp at h
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
  | true  => rfl
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
  | true  => rfl
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

theorem biject_class_subnormal (f:F32) :
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

end F32
