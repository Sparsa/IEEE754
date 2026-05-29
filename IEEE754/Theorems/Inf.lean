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

private theorem significand_nonzero_of_not_isZero (f : F32)
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
  · -- isNormal = true: significand has a leading 1-bit at position 23
    simp only [significand, hn, ite_true]
    intro h
    have hge : ((1 : BitVec 24) <<< 23).toNat ≤
        ((1 : BitVec 24) <<< 23 ||| f.mantissa.zeroExtend 24).toNat := by
      rw [BitVec.toNat_or]; exact Nat.left_le_or
    have h1 : ((1 : BitVec 24) <<< 23).toNat = 2 ^ 23 := by decide
    grind

/-- ∞ × nonzero finite = ∞ (sign = XOR of operand signs). -/
theorem fmul_inf_nonzero {rm : RoundMode} {a b : F32}
    (ha : a.isInf) (hb : b.isFinite) (hnz : ¬b.isZero) :
    (F32.fmul rm a b).isInf ∧ (F32.fmul rm a b).sign = (a.sign != b.sign) := by
  have a_notn   : a.isNaN = false  := isNaN_false_of_isInf a ha
  have b_notn   : b.isNaN = false  := isNaN_false_of_isFinite b hb
  have b_notinf : b.isInf = false  := isInf_false_of_isFinite b hb
  have hbz      : b.isZero = false := by
    cases hh : b.isZero
    · rfl
    · exact absurd hh hnz
  have hbsig    : b.significand.toNat ≠ 0 := significand_nonzero_of_not_isZero b hb hbz
  have hadec    : F32.decode a = .inf a.sign := by simp [decode, a_notn, ha]
  have hbdec    : F32.decode b = .finite b.sign
      ((if b.isNormal then (b.expRaw.toNat : Int) else 1) - 127 - 23)
      b.significand.toNat := by simp [decode, b_notn, b_notinf, hbz]
  have hmul     : mulExact (F32.decode a) (F32.decode b) =
      (.inf (a.sign != b.sign), ExcFlags.empty) := by
    rw [hadec, hbdec]; exact mulExact_inf_nonzero _ _ _ _ hbsig
  -- Reduce fmul to a concrete pack expression, then case-split the sign bit.
  have hval : F32.fmul rm a b = F32.pack (a.sign != b.sign) (BitVec.allOnes 8) 0 := by
    simp [fmul, fmulEx, hmul, roundTo, encode]
  rw [hval]
  constructor
  · cases h : (a.sign != b.sign) <;> simp [isInf, expIsMax, mantIsZero, pack] <;> decide
  · cases h : (a.sign != b.sign) <;> simp [sign, pack] <;> decide

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
          by_cases (dfa != sa) <;>
          · { simp_all }
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
          rename_i aa bb sa exp sig sb exp2 x heq heq2
          by_cases h: (sa = b.sign) <;>
          · {
              simp [h]
              native_decide
          }
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
        by_cases hh : a.isNormal
        ·{
          simp [classify] at claa
          simp [hna] at claa
          have aNSub : a.isSubnormal = false := by exact isSubnormal_false_of_isNormal a hh
          simp [aNSub] at claa
          simp [hh] at claa
        }
        ·{
          simp [hh]
          simp [divExact]
          simp [isNormal] at hh
          simp [isNaN] at a_notn
          simp [divExactWith]
          split
          ·{
            simp_all
          }
          ·{
            simp_all
          }
          ·{
            simp_all
          }
          ·{
            simp [roundTo]
            simp [encode]
            simp [qNaN]
            simp [expIsMax]
            simp [expRaw]
            simp [pack]
          }
          ·{
            simp [roundTo]
            simp [encode]
            simp [pack]
            split <;>
            ·{
              simp [expIsMax]
              simp [expRaw]
            }
          }
          ·{
            contradiction
          }
          ·{
            simp [roundTo]
            simp [encode]
            simp [expIsMax]
            simp [expRaw]
            simp [pack]
            split <;>
            ·{
              simp_all
            }

          }
          ·{
            simp [roundTo]
            simp [encode]
            simp [pack]
            split <;>
            ·{
              simp_all
            }
          }
          ·{
            simp_all
          }
        }
      }
      ·{
        simp [classify] at claa
        simp [hna] at claa
        by_cases hnn: (a.isSubnormal)
        ·{
          simp [hnn] at claa
        }
        ·{
          simp [hnn] at claa
          simp [a_notinf] at claa
          simp [fdiv]
          simp [fdivEx]
          simp [divExact]
          simp [divExactWith]
          split
          ·{
            simp [roundTo]
            simp [encode]
            simp [qNaN]
            simp [pack]
            simp [expIsMax]
            simp [expRaw]
          }
          ·{
            rename_i aa bb heq hh
            simp [decode] at heq
            simp [b_notn] at heq
            simp [b_ninf] at heq
            simp [hb] at heq
          }
          ·{
            simp [roundTo]
            simp [encode]
            simp [qNaN]
            simp [pack]
            simp [expIsMax]
            simp [expRaw]
          }
          ·{
            simp [roundTo]
            simp [encode]
            simp [qNaN]
            simp [pack]
            simp [expIsMax]
            simp [expRaw]
          }
          ·{
            simp [roundTo]
            simp [encode]
            simp [pack]
            split <;>
            ·{
              simp [expIsMax]
              simp [expRaw]
            }
          }
          ·{
            rename_i b_heq
            simp [decode] at b_heq
            simp_all
          }
          ·{
            simp [roundTo]
            simp [encode]
            simp [pack]
            split <;>
            ·{
              simp [expIsMax]
              simp [expRaw]
            }
          }
          ·{
            have classify_a:=  classify_exclusive a
            simp [hna,a_notn,a_notinf,hnn,claa] at classify_a
          }
          ·{
            have classify_a:=  classify_exclusive a
            simp [hna,a_notn,a_notinf,hnn,claa] at classify_a
          }

        }

      }
      }
    ·{
      -- Strategy: derive that a.significand.toNat ≠ 0 and b.decode = .finite b.sign 0 0,
      -- then show divExact produces .inf (not NaN), so the result is pack _ (allOnes 8) 0
      -- which has mantIsZero = true.
      have haz : a.isZero = false := by cases hh : a.isZero; rfl; exact absurd hh hna
      have a_isFinite : a.isFinite = true := by simp [isFinite, ha]
      -- hasig must be in local context so simp can discharge the side condition on
      -- divExactWith's case-7 equational lemma (sig ≠ 0)
      have hasig : a.significand.toNat ≠ 0 :=
        significand_nonzero_of_not_isZero a a_isFinite haz
      have hbdec : b.decode = .finite b.sign 0 0 := by
        simp [decode, b_notn, b_ninf]; intro h; simp_all
      have hadec : a.decode = .finite a.sign
          ((if a.isNormal then (a.expRaw.toNat : Int) else 1) - 127 - 23)
          a.significand.toNat := by
        simp [decode, a_notn, a_notinf, haz]
      have hdiv : divExact a.decode b.decode =
          (.inf (a.sign != b.sign), ExcFlags.mkDivByZero) := by
        rw [hadec, hbdec, divExact]; simp only [divExactWith]
      have hval : F32.fdiv rm a b =
          F32.pack (a.sign != b.sign) (BitVec.allOnes 8) 0 := by
        simp [fdiv, fdivEx, hdiv, roundTo, encode]
      rw [hval]
      cases h : (a.sign != b.sign) <;> simp [mantIsZero, pack] <;> decide
      }

end F32
