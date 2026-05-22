/-
  IEEE754.Theorems.NaN
  ====================
  §11B  NaN propagation (IEEE 754-2019 §6.2)
  §11C  Invalid operations → NaN (IEEE 754-2019 §7.2)
-/

import IEEE754.Theorems.Codec

open BitVec

namespace F32

-- ── B. NaN propagation (IEEE 754-2019 §6.2) ──────────────────────────────────

theorem fadd_nan_l (rm : RoundMode) (a b : F32) (h : a.isNaN) :
    (F32.fadd rm a b).isNaN := by
    simp [F32.fadd]
    simp [faddEx]
    simp [addExact]
    split
    · simp_all; simp [roundTo]; simp [encode]; decide
    · simp; simp [roundTo]; simp [encode]; decide
    · rename_i da db sa sb heqa heqb
      simp [decode] at heqa
      rw [h] at heqa
      simp at heqa
    · rename_i da db sa sb heqa heqb
      simp [decode] at sb
      rw [h] at sb
      simp_all
    · rename_i da db s heq ad x
      simp
      simp [decode] at ad
      simp [h] at ad
    · rename_i ad bd
      rename_i sigb eb sb
      rename_i siga ea sa
      rename_i dfa dfb
      simp [decode] at ad
      simp [h] at ad

theorem fadd_nan_r (rm : RoundMode) (a b : F32) (h : b.isNaN) :
    (F32.fadd rm a b).isNaN := by
    simp [F32.fadd]
    simp [faddEx]
    simp [addExact]
    split
    · simp_all; simp [roundTo]; simp [encode]; decide
    · simp; simp [roundTo]; simp [encode]; decide
    · rename_i da db sa sb heqa heqb
      simp [decode] at heqb
      rw [h] at heqb
      simp at heqb
    · rename_i da db sa sb heqa heqb
      simp [decode] at heqa
      rw [h] at heqa
      simp_all
    · rename_i da db s heq ad x
      simp
      simp [decode] at heq
      simp [h] at heq
    · rename_i ad bd
      rename_i sigb eb sb
      rename_i siga ea sa
      rename_i dfa dfb
      simp [decode] at bd
      simp [h] at bd

theorem fmul_nan_l (rm : RoundMode) (a b : F32) (h : a.isNaN) :
    (F32.fmul rm a b).isNaN := by
    simp [F32.fmul]
    simp [fmulEx]
    simp [mulExact]
    split
    { simp; simp [roundTo]; simp [encode]; decide }
    { simp; simp [roundTo]; simp [encode]; decide }
    { simp; simp [roundTo]; simp [encode]; decide }
    { simp; simp [roundTo]; simp [encode]; decide }
    { simp; rename_i had hbd; simp [decode] at had; simp [h] at had }
    { simp; rename_i had hbd; simp [decode] at had; simp [h] at had }
    { simp; rename_i had hbd; simp [decode] at had; simp [h] at had }
    { simp; rename_i had hbd; simp [decode] at had; simp [h] at had }

theorem fmul_nan_r (rm : RoundMode) (a b : F32) (h : b.isNaN) :
    (F32.fmul rm a b).isNaN := by
    simp [F32.fmul]
    simp [fmulEx]
    simp [mulExact]
    split
    { simp; simp [roundTo]; simp [encode]; decide }
    { simp; simp [roundTo]; simp [encode]; decide }
    { simp; simp [roundTo]; simp [encode]; decide }
    { simp; simp [roundTo]; simp [encode]; decide }
    { simp; rename_i had hbd; simp [decode] at hbd; simp [h] at hbd }
    { simp; rename_i had hbd; simp [decode] at hbd; simp [h] at hbd }
    { simp; rename_i had hbd; simp [decode] at hbd; simp [h] at hbd }
    { simp; rename_i had hbd; simp [decode] at hbd; simp [h] at hbd }

theorem fdiv_nan_l (rm : RoundMode) (a b : F32) (h : a.isNaN) :
    (F32.fdiv rm a b).isNaN := by
    simp [isNaN]
    constructor <;>
    {
      simp [fdiv]
      simp [fdivEx]
      simp [decode]
      rw [h]
      simp
      simp [divExact]
      simp [divExactWith]
      simp [roundTo]
      simp [encode]
      native_decide
    }

theorem fdiv_nan_r (rm : RoundMode) (a b : F32) (h : b.isNaN) :
    (F32.fdiv rm a b).isNaN := by
    simp [isNaN]
    constructor <;>
    {
      simp [fdiv]
      simp [fdivEx]
      simp [decode]
      rw [h]
      simp
      simp [divExact]
      split
      · { simp [divExactWith]; simp [roundTo]; simp [encode]; native_decide }
      · {
        split
        · { simp [divExactWith]; simp [roundTo]; simp [encode]; native_decide }
        · {
          split
          · { simp [divExactWith]; simp [roundTo]; simp [encode]; native_decide }
          · { simp [divExactWith]; simp [roundTo]; simp [encode]; native_decide }
          }
      }
    }

theorem fma_nan_a (rm : RoundMode) (a b c : F32) (h : a.isNaN) :
    (F32.fma rm a b c).isNaN := by
    simp [isNaN]
    constructor <;>
    · {
      simp [fma, fmaEx, decode]
      rw [h]
      simp_all
      simp [fmaExact]
      simp [roundTo]
      simp [encode]
      native_decide
    }

theorem fma_nan_b (rm : RoundMode) (a b c : F32) (h : b.isNaN) :
    (F32.fma rm a b c).isNaN := by
    simp [isNaN]
    constructor <;>
    · {
      simp [fma]
      simp [fmaEx]
      simp [fmaExact]
      split
      · { simp [roundTo]; simp [encode]; native_decide }
      · { simp [roundTo]; simp [encode]; native_decide }
      · { simp [roundTo]; simp [encode]; native_decide }
      · { simp [roundTo]; simp [encode]; native_decide }
      · {
        rename_i hx hx1 hx2 hx3 da db
        simp [decode] at hx3
        simp_all
      }
    }

theorem fma_nan_c (rm : RoundMode) (a b c : F32) (h : c.isNaN) :
    (F32.fma rm a b c).isNaN := by
  simp [fma]
  simp [fmaEx]
  simp [fmaExact]
  split
  · { simp [roundTo]; simp [encode]; native_decide }
  · { simp [roundTo]; simp [encode]; native_decide }
  · { simp [roundTo]; simp [encode]; native_decide }
  · { simp [roundTo]; simp [encode]; native_decide }
  · {
    rename_i hx hx1 hx2 hx3 da db
    simp [decode]
    rw [h]
    simp [decode] at hx2 hx3
    simp
    rw [addExact_comm]
    simp [addExact]
    simp [roundTo]
    simp [encode]
    native_decide
  }

-- ── C. Invalid operations → NaN (IEEE 754-2019 §7.2) ─────────────────────────

/-- ∞ × 0 is an invalid operation; result is NaN (§7.2 case d). -/
theorem fmul_inf_zero {rm : RoundMode} {a b : F32}
    (ha : a.isInf) (hb : b.isZero) : (F32.fmul rm a b).isNaN := by
    have a_notn : a.isNaN = false := isNaN_false_of_isInf a ha
    have b_notn : b.isNaN = false := isNaN_false_of_isZero b hb
    have b_notinf : b.isInf = false := isInf_false_of_isZero b hb
    simp [isNaN]
    constructor <;>
    · simp [fmul, fmulEx, decode]
      simp [a_notn, ha]
      simp [b_notn, b_notinf, hb]
      simp [mulExact]
      simp [roundTo]
      simp [encode]
      native_decide

theorem fmul_zero_inf {rm : RoundMode} {a b : F32}
    (ha : a.isZero) (hb : b.isInf) : (F32.fmul rm a b).isNaN := by
    have b_notn : b.isNaN = false := isNaN_false_of_isInf b hb
    have a_notn : a.isNaN = false := isNaN_false_of_isZero a ha
    have a_notinf : a.isInf = false := isInf_false_of_isZero a ha
    simp [isNaN]
    constructor <;>
    · simp [fmul, fmulEx, decode]
      simp [a_notn, ha]
      simp [b_notn, a_notinf, hb]
      simp [mulExact]
      simp [roundTo]
      simp [encode]
      native_decide

/-- (+∞) + (−∞) is an invalid operation; result is NaN (§7.2 case f). -/
theorem fadd_inf_opp {rm : RoundMode} {a b : F32}
    (ha : a.isInf) (hb : b.isInf) (hs : a.sign ≠ b.sign) :
    (F32.fadd rm a b).isNaN := by
    have a_notn : a.isNaN = false := isNaN_false_of_isInf a ha
    have b_notn : b.isNaN = false := isNaN_false_of_isInf b hb
    have b_notz : b.isZero = false := isZero_false_of_isInf b hb
    simp [isNaN]
    constructor <;>
    · simp [fadd, faddEx, decode]
      simp [a_notn, ha]
      simp [b_notn, hb]
      simp [addExact]
      split
      · simp_all
      · simp [roundTo]; simp [encode]; native_decide

/-- 0 / 0 is an invalid operation; result is NaN (§7.2 case g). -/
theorem fdiv_zero_zero {rm : RoundMode} {a b : F32}
    (ha : a.isZero) (hb : b.isZero) : (F32.fdiv rm a b).isNaN := by
    have a_notn : a.isNaN = false := isNaN_false_of_isZero a ha
    have b_notn : b.isNaN = false := isNaN_false_of_isZero b hb
    have b_notInf : b.isInf = false := isInf_false_of_isZero b hb
    have a_notInf : a.isInf = false := isInf_false_of_isZero a ha
    simp [isNaN]
    constructor <;>
    { simp [fdiv, fdivEx, decode]
      simp [a_notn, ha]
      simp [b_notn, hb, b_notInf, a_notInf]
      simp [divExact, divExactWith, roundTo, encode]
      native_decide }

/-- ∞ / ∞ is an invalid operation; result is NaN (§7.2 case h). -/
theorem fdiv_inf_inf {rm : RoundMode} {a b : F32}
    (ha : a.isInf) (hb : b.isInf) : (F32.fdiv rm a b).isNaN := by
    have a_notn : a.isNaN = false := isNaN_false_of_isInf a ha
    have b_notn : b.isNaN = false := isNaN_false_of_isInf b hb
    have b_notz : b.isZero = false := isZero_false_of_isInf b hb
    have a_notz : a.isZero = false := isZero_false_of_isInf a ha
    simp [isNaN]
    constructor <;>
    { simp [fdiv, fdivEx, decode]
      simp [a_notn, ha]
      simp [b_notn, hb]
      simp [divExact, divExactWith, roundTo, encode]
      native_decide }

/-- ∞ × 0 in fma is invalid regardless of the addend c (§7.2 case d). -/
theorem fma_inf_zero {rm : RoundMode} {a b c : F32}
    (ha : a.isInf) (hb : b.isZero) : (F32.fma rm a b c).isNaN := by
    have a_notn : a.isNaN = false := isNaN_false_of_isInf a ha
    have b_notn : b.isNaN = false := isNaN_false_of_isZero b hb
    have b_notinf : b.isInf = false := isInf_false_of_isZero b hb
    simp [isNaN]
    constructor <;>
    { simp [fma, fmaEx, fmaExact, decode]
      simp [a_notn, ha]
      simp [b_notn, b_notinf, hb]
      simp [roundTo, encode]
      native_decide }

end F32
