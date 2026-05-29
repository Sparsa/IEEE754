/-
  IEEE754.Theorems.F64.Inf
  ========================
  §11D  Inf propagation (IEEE 754-2019 §6.1)
-/

import IEEE754.Theorems.F64.NaN

open BitVec

namespace F64

/-- ∞ + finite = ∞ (sign of Inf operand is preserved). -/
theorem fadd_inf_finite {rm : RoundMode} {a b : F64}
    (ha : a.isInf) (hb : b.isFinite) :
    (F64.fadd rm a b).isInf ∧ (F64.fadd rm a b).sign = a.sign := by
    have a_notn : a.isNaN = false := isNaN_false_of_isInf a ha
    have b_notn : b.isNaN = false := isNaN_false_of_isFinite b hb
    have b_notinf : b.isInf = false := isInf_false_of_isFinite b hb
    simp [isInf]
    constructor
    ·{
      simp [fadd, faddEx, decode]
      simp [a_notn, ha]
      simp [b_notn]
      simp [addExact]
      split
      · simp_all
      ·
        simp [roundTo]
        simp [encode]
        constructor
        · native_decide
        ·
          simp [mantIsZero]
          rename_i da db heq df
          simp at df
          simp_all
          by_cases b.isZero <;>
          ·{ simp_all }
      ·{
        rename_i aa bb sa sb heq1 heq2
        constructor
        ·{
          simp [b_notinf] at heq2
          by_cases (sa = sb) <;>
          ·{
            simp_all
            simp [roundTo]
            simp [encode]
            simp [expIsMax]
            simp [expRaw]
            grind
          }
        }
        ·{
          simp [b_notinf] at heq2
          by_cases (sa = sb) <;>
          ·{
            simp_all
            simp [roundTo]
            simp [encode]
            simp [mantIsZero]
            simp [mantissa]
            grind
          }
        }
      }
      ·{
        rename_i aa bb sa sb heq1 heq2
        constructor
        ·{
          simp [roundTo]; simp [encode]; simp [expIsMax]; simp [expRaw]
          simp [BitVec.setWidth]
          cases sa <;> simp [F64.pack]
        }
        ·{
          simp [roundTo]; simp [encode]; simp [mantIsZero]; simp [mantissa]
          cases sa <;> simp [F64.pack]
        }
      }
      ·{ rename_i aa bb sa sb heq1 heq2; simp at heq2 }
      ·{ rename_i aa bb sa sb heq1 heq2; simp at heq1 }
    }
    ·{
      simp [fadd, faddEx, decode]
      simp [a_notn, ha]
      simp [b_notn, b_notinf]
      by_cases hh: b.isZero <;>
       · simp [hh]
         simp [addExact]
         simp [roundTo]
         simp [encode]
         simp [sign]
         simp [pack]
         bv_decide
     }

private theorem significand_nonzero_of_not_isZero (f : F64)
    (hfin : f.isFinite = true) (hzero : f.isZero = false) :
    f.significand.toNat ≠ 0 := by
  have hexpmax : f.expIsMax = false := by
    cases h : f.expIsMax
    · rfl
    · simp [isFinite, h] at hfin
  cases hn : f.isNormal
  · -- isNormal = false; since expIsMax = false too, expIsZero must be true
    have hexpzero : f.expIsZero = true := by
      cases h : f.expIsZero
      · simp [isNormal, h, hexpmax] at hn
      · rfl
    -- isZero = false + expIsZero = true → mantIsZero = false
    have hmant : f.mantIsZero = false := by
      simp [isZero, hexpzero] at hzero; exact hzero
    -- subnormal: significand.toNat = mantissa.toNat
    have hSigEq : f.significand.toNat = f.mantissa.toNat := by
      simp [significand, hn]; omega
    rw [hSigEq]
    intro h0
    have hmant_ne : f.mantissa ≠ 0 := by
      intro h; simp [mantIsZero, h] at hmant
    exact hmant_ne (BitVec.eq_of_toNat_eq h0)
  · -- isNormal = true: significand has a leading 1-bit at position 52
    simp only [significand, hn, ite_true]
    intro h
    have hge : ((1 : BitVec 53) <<< 52).toNat ≤
        ((1 : BitVec 53) <<< 52 ||| f.mantissa.zeroExtend 53).toNat := by
      rw [BitVec.toNat_or]; exact Nat.left_le_or
    have h1 : ((1 : BitVec 53) <<< 52).toNat = 2 ^ 52 := by decide
    grind

/-- ∞ × nonzero finite = ∞ (sign = XOR of operand signs). -/
theorem fmul_inf_nonzero {rm : RoundMode} {a b : F64}
    (ha : a.isInf) (hb : b.isFinite) (hnz : ¬b.isZero) :
    (F64.fmul rm a b).isInf ∧ (F64.fmul rm a b).sign = (a.sign != b.sign) := by
  have a_notn   : a.isNaN = false  := isNaN_false_of_isInf a ha
  have b_notn   : b.isNaN = false  := isNaN_false_of_isFinite b hb
  have b_notinf : b.isInf = false  := isInf_false_of_isFinite b hb
  have hbz      : b.isZero = false := by
    cases hh : b.isZero
    · rfl
    · exact absurd hh hnz
  have hbsig    : b.significand.toNat ≠ 0 := significand_nonzero_of_not_isZero b hb hbz
  have hadec    : F64.decode a = .inf a.sign := by simp [decode, a_notn, ha]
  have hbdec    : F64.decode b = .finite b.sign
      ((if b.isNormal then (b.expRaw.toNat : Int) else 1) - 1023 - 52)
      b.significand.toNat := by simp [decode, b_notn, b_notinf, hbz]
  have hmul     : mulExact (F64.decode a) (F64.decode b) =
      (.inf (a.sign != b.sign), ExcFlags.empty) := by
    rw [hadec, hbdec]; exact F32.mulExact_inf_nonzero _ _ _ _ hbsig
  -- Reduce fmul to a concrete pack expression, then case-split the sign bit.
  have hval : F64.fmul rm a b = F64.pack (a.sign != b.sign) (BitVec.allOnes 11) 0 := by
    simp [fmul, fmulEx, hmul, roundTo, encode]
  rw [hval]
  constructor
  · cases h : (a.sign != b.sign) <;> simp [isInf, expIsMax, mantIsZero, pack] <;> decide
  · cases h : (a.sign != b.sign) <;> simp [sign, pack] <;> decide

/-- Nonzero finite / 0 = ∞ (division by zero; §7.3). -/
theorem fdiv_nonzero_zero {rm : RoundMode} {a b : F64}
    (ha : a.isFinite) (hna : ¬a.isZero) (hb : b.isZero) :
    (F64.fdiv rm a b).isInf := by
    sorry

end F64
