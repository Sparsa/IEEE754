/-
  IEEE754.Theorems.Inf
  ====================
  §11D  Inf propagation (IEEE 754-2019 §6.1)
-/

import IEEE754.Theorems.NaN

open BitVec

namespace F32

/-- ∞ + finite = ∞ (sign of Inf operand is preserved). -/
theorem fadd_inf_finite {rm : RoundMode} {a b : F32}
    (ha : a.isInf) (hb : b.isFinite) :
    (F32.fadd rm a b).isInf ∧ (F32.fadd rm a b).sign = a.sign := by
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
          cases sa <;> simp [F32.pack]
        }
        ·{
          simp [roundTo]; simp [encode]; simp [mantIsZero]; simp [mantissa]
          cases sa <;> simp [F32.pack]
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

/-- ∞ × nonzero finite = ∞ (sign = XOR of operand signs). -/
theorem fmul_inf_nonzero {rm : RoundMode} {a b : F32}
    (ha : a.isInf) (hb : b.isFinite) (hnz : ¬b.isZero) :
    (F32.fmul rm a b).isInf ∧ (F32.fmul rm a b).sign = (a.sign != b.sign) := by
    have a_notn : a.isNaN = false := isNaN_false_of_isInf a ha
    have b_notn : b.isNaN = false := isNaN_false_of_isFinite b hb
    have b_notinf : b.isInf = false := isInf_false_of_isFinite b hb
    simp [isInf]
    rw [_root_.and_assoc]
    constructor
    ·{
      simp [fmul, fmulEx, decode]
      simp [a_notn, ha]
      simp [b_notn, b_notinf]
      by_cases hh: b.isZero
      ·{
        simp [hh]
        simp [mulExact]
        simp [roundTo]
        simp [encode]
        bv_decide
      }
      ·{
        simp [hh]
        simp [mulExact]
        simp [roundTo]
        simp [encode]
        simp [pack]


      }
    }
    ·{
      constructor
      ·{
        simp [fmul]
        simp[fmulEx]
        simp [mulExact]
        split
        ·{
          rename_i heq
          simp [decode] at heq
          simp [a_notn] at heq
          simp [ha] at heq
        }
        ·{
          rename_i heq_b heq_a
          simp [decode] at heq_b
          simp [b_notn] at heq_b
          simp [b_notinf] at heq_b
          simp [hnz] at heq_b
        }
        ·{
          rename_i heq_a heq_b
          simp [decode] at heq_b
          simp [b_notn] at heq_b
          simp [b_notinf] at heq_b
          simp [hnz] at heq_b
          simp [isFinite] at hb
          contradiction
          by_cases b.isNormal
          ·{
            rename_i bn
            simp [bn] at heq_b

          }
          simp [hb] at heq_b
          simp [ha] at heq_a
          simp [roundTo]
          simp [encode]
          simp [qNaN]



        }
      }
    }

/-- Nonzero finite / 0 = ∞ (division by zero; §7.3). -/
theorem fdiv_nonzero_zero {rm : RoundMode} {a b : F32}
    (ha : a.isFinite) (hna : ¬a.isZero) (hb : b.isZero) :
    (F32.fdiv rm a b).isInf := by
    have b_ninf : b.isInf = false := isInf_false_of_isZero b hb
    have b_notn : b.isNaN = false := isNaN_false_of_isZero b hb
    simp [isFinite] at ha
    have a_notn : a.isNaN = false := by simp [isNaN]; intros; simp_all
    have a_notinf : a.isInf = false := by simp [isInf]; intros; simp_all
    simp [isInf]
    constructor
    ·{
      cases claa: (classify a)
      ·{
        have bja := biject_class_zero a
        simp_all
      }
      ·{
        have bja := biject_class_subnormal a
        have a_subn :=  bja.mpr claa
        have a_not_nan : a.isNaN = false := isNaN_false_of_isSubnormal a a_subn
        have a_not_zero : a.isZero = false := isZero_false_of_isSubnormal a a_subn
        have a_not_inf : a.isInf = false := isInf_false_of_isSubnormal a a_subn
        have a_not_normal : a.isNormal = false := isNormal_false_of_isSubnormal a a_subn
        have b_not_nan :  b.isNaN = false := isNaN_false_of_isZero b hb
        have b_not_inf :  b.isInf = false := isInf_false_of_isZero b hb
        have b_z : b.decode = .finite b.sign 0 0 := by
          simp [decode]; simp [b_not_nan, b_not_inf]; intro b_is_not_z; simp_all
        have a_sub : a.decode = .finite a.sign (0-149) a.significand.toNat := by
          simp [decode]; simp [a_not_nan]; simp [a_not_zero]; simp [a_not_inf]; simp [a_not_normal]
        simp [fdiv]; simp [fdivEx]; simp [divExact]; simp [divExactWith]
        simp [b_z]; simp [a_sub]
        split
        · { simp [roundTo]; simp [encode]; native_decide }
        · { simp [roundTo]; simp [encode]; native_decide }
        · { simp [roundTo]; simp [encode]; native_decide }
        · { simp [roundTo]; simp [encode]; native_decide }
        · {
          simp [roundTo]; simp [encode]; simp [pack]; simp [expIsMax]; simp [expRaw]
          split <;> · { native_decide }
        }
        · { contradiction }
        · {
          simp_all; simp [roundTo]; simp [encode]; simp [expIsMax]
          rename_i heq1 heq2
          have ⟨heq1l, heq1m, heq1r⟩ := heq1
          have ⟨heq2l, he12r⟩ := heq2
          simp [expRaw]; simp [pack]
          rw [eq_comm] at heq2l; rw [heq2l]
          rw [eq_comm] at heq1l; rw [heq1l]
          by_cases (a.sign = b.sign) <;> · { rename_i asign_bsign; simp [asign_bsign] }
        }
        · {
          simp [roundTo]; simp [encode]
          rename_i heq1 heq2 dfa dfb sa exp sb expb sig dd
          simp [expIsMax]; simp [expRaw]
          by_cases (sb != sa) <;> · { simp_all }
        }
        · { simp_all }
      }
      ·{
        have bja := biject_class_normal a
        have a_n :=  bja.mpr claa
        have a_not_nan : a.isNaN = false := isNaN_false_of_isNormal a a_n
        have a_not_zero : a.isZero = false := isZero_false_of_isNormal a a_n
        have a_not_inf : a.isInf = false := isInf_false_of_isNormal a a_n
        have a_not_subnormal : a.isSubnormal = false := isSubnormal_false_of_isNormal a a_n
        have b_not_nan : b.isNaN = false := isNaN_false_of_isZero b hb
        have b_not_inf : b.isInf = false := isInf_false_of_isZero b hb
        have b_z : b.decode = .finite b.sign 0 0 := by
          simp [decode]; simp [b_not_nan, b_not_inf]; intro b_is_not_z; simp_all
        simp [fdiv]; simp [fdivEx]; simp [divExact]; simp [divExactWith]
        split
        · { simp [roundTo]; simp [encode]; native_decide }
        · { simp [roundTo]; simp [encode]; native_decide }
        · { simp [roundTo]; simp [encode]; native_decide }
        · { simp [roundTo]; simp [encode]; native_decide }
        · {
          simp [roundTo]; simp [encode]; simp [pack]; simp [expIsMax]; simp [expRaw]
          split <;> · { native_decide }
        }
        · { simp [roundTo]; simp [encode]; simp_all }
        · {
          simp [roundTo]; simp [encode]; simp_all; simp [pack]
          by_cases h: (a.sign = b.sign) <;> · { simp [h]; native_decide }
        }
        · {
          simp [roundTo]; simp [encode]; simp [pack]; simp [expIsMax]; simp [expRaw]
          split <;> · { simp_all }
        }
        · {
          simp [roundTo]; simp [encode]; simp [pack]; simp [expIsMax]; simp [expRaw]
          split <;> · { simp_all }
        }
      }
      ·{
        simp [fdiv, fdivEx, decode]
        simp [a_notn, a_notinf]
        simp at hna; simp [hna]
        simp [b_notn]; simp [b_ninf]; simp [hb]
        by_cases hh : a.isNormal <;>
        ·{ simp [hh]; simp [divExact]; simp [divExactWith] }
       }
      }
    · sorry

end F32
