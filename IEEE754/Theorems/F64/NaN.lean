/-
  IEEE754.Theorems.F64.NaN
  ========================
  §11B  NaN propagation (IEEE 754-2019 §6.2)
  §11C  Invalid operations → NaN (IEEE 754-2019 §7.2)
-/

import IEEE754.Theorems.F64.Codec

open BitVec

namespace F64

-- ── B. NaN propagation (IEEE 754-2019 §6.2) ──────────────────────────────────

theorem fadd_nan_l (rm : RoundMode) (a b : F64) (h : a.isNaN) :
    (F64.fadd rm a b).isNaN := by
    simp [F64.fadd]
    simp [faddEx]
    simp [addExact]
    split
    · simp_all; simp [roundTo]; simp [encode]; native_decide
    · simp; simp [roundTo]; simp [encode]; native_decide
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

theorem fadd_nan_r (rm : RoundMode) (a b : F64) (h : b.isNaN) :
    (F64.fadd rm a b).isNaN := by
    simp [F64.fadd]
    simp [faddEx]
    simp [addExact]
    split
    · simp_all; simp [roundTo]; simp [encode]; native_decide
    · simp; simp [roundTo]; simp [encode]; native_decide
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

theorem fmul_nan_l (rm : RoundMode) (a b : F64) (h : a.isNaN) :
    (F64.fmul rm a b).isNaN := by
    simp [F64.fmul]
    simp [fmulEx]
    simp [mulExact]
    split
    { simp; simp [roundTo]; simp [encode]; native_decide }
    { simp; simp [roundTo]; simp [encode]; native_decide }
    { simp; simp [roundTo]; simp [encode]; native_decide }
    { simp; simp [roundTo]; simp [encode]; native_decide }
    { simp; rename_i had hbd; simp [decode] at had; simp [h] at had }
    { simp; rename_i had hbd; simp [decode] at had; simp [h] at had }

theorem fmul_nan_r (rm : RoundMode) (a b : F64) (h : b.isNaN) :
    (F64.fmul rm a b).isNaN := by
    simp [F64.fmul]
    simp [fmulEx]
    simp [mulExact]
    split
    { simp; simp [roundTo]; simp [encode]; native_decide }
    { simp; simp [roundTo]; simp [encode]; native_decide }
    { simp; simp [roundTo]; simp [encode]; native_decide }
    { simp; simp [roundTo]; simp [encode]; native_decide }
    { simp; rename_i had hbd; simp [decode] at hbd; simp [h] at hbd }
    { simp; rename_i had hbd; simp [decode] at hbd; simp [h] at hbd }

theorem fdiv_nan_l (rm : RoundMode) (a b : F64) (h : a.isNaN) :
    (F64.fdiv rm a b).isNaN := by
    simp [F64.fdiv, fdivEx, divExact, divExactWith]
    split
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · rename_i ad bd; simp [decode] at ad; simp [h] at ad

theorem fdiv_nan_r (rm : RoundMode) (a b : F64) (h : b.isNaN) :
    (F64.fdiv rm a b).isNaN := by
    simp [F64.fdiv, fdivEx, divExact, divExactWith]
    split
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · rename_i ad bd; simp [decode] at bd; simp [h] at bd

theorem fma_nan_a (rm : RoundMode) (a b c : F64) (h : a.isNaN) :
    (F64.fma rm a b c).isNaN := by
    simp [fma, fmaEx, fmaExact, mulExact]
    split
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp; rename_i had hbd; simp [decode] at had; simp [h] at had
    · simp; rename_i had hbd; simp [decode] at had; simp [h] at had

theorem fma_nan_b (rm : RoundMode) (a b c : F64) (h : b.isNaN) :
    (F64.fma rm a b c).isNaN := by
    simp [fma, fmaEx, fmaExact, mulExact]
    split
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · simp; rename_i had hbd; simp [decode] at hbd; simp [h] at hbd
    · simp; rename_i had hbd; simp [decode] at hbd; simp [h] at hbd

theorem fma_nan_c (rm : RoundMode) (a b c : F64) (h : c.isNaN) :
    (F64.fma rm a b c).isNaN := by
    simp [fma, fmaEx, fmaExact, mulExact, addExact]
    split
    · simp [roundTo]; simp [encode]; native_decide
    · simp [roundTo]; simp [encode]; native_decide
    · rename_i da db sa sb dca dcb
      simp [decode] at dca
      rw [h] at dca; simp at dca
    · rename_i da db sa sb dca dcb
      simp [decode] at dcb
      rw [h] at dcb; simp_all
    · rename_i da db s heq ad x
      simp
      simp [decode] at ad
      simp [h] at ad
    · rename_i ad bd
      rename_i sigb eb sb siga ea sa dfa dfb
      simp [decode] at bd
      simp [h] at bd

-- ── C. Invalid operations → NaN (IEEE 754-2019 §7.2) ─────────────────────────

theorem fmul_inf_zero (rm : RoundMode) (a b : F64) (ha : a.isInf) (hb : b.isZero) :
    (F64.fmul rm a b).isNaN := by
    simp [fmul, fmulEx, mulExact, decode]
    simp [isNaN_false_of_isInf a ha, ha, isNaN_false_of_isZero b hb, hb,
          isInf_false_of_isZero b hb]
    simp [roundTo, encode]; native_decide

theorem fmul_zero_inf (rm : RoundMode) (a b : F64) (ha : a.isZero) (hb : b.isInf) :
    (F64.fmul rm a b).isNaN := by
    simp [fmul, fmulEx, mulExact, decode]
    simp [isNaN_false_of_isInf b hb, hb, isNaN_false_of_isZero a ha, ha,
          isInf_false_of_isZero a ha]
    simp [roundTo, encode]; native_decide

theorem fadd_inf_opp (rm : RoundMode) (a b : F64)
    (ha : a.isInf) (hb : b.isInf) (hs : a.sign ≠ b.sign) :
    (F64.fadd rm a b).isNaN := by
    simp [fadd, faddEx, addExact, decode]
    simp [isNaN_false_of_isInf a ha, ha, isNaN_false_of_isInf b hb, hb]
    cases h : (a.sign == b.sign)
    · simp [Bool.beq_false_iff] at h; contradiction
    · simp [roundTo, encode]; native_decide

theorem fdiv_zero_zero (rm : RoundMode) (a b : F64) (ha : a.isZero) (hb : b.isZero) :
    (F64.fdiv rm a b).isNaN := by
    simp [fdiv, fdivEx, divExact, divExactWith, decode]
    simp [isNaN_false_of_isZero a ha, ha, isNaN_false_of_isZero b hb, hb,
          isInf_false_of_isZero a ha, isInf_false_of_isZero b hb]
    simp [roundTo, encode]; native_decide

theorem fdiv_inf_inf (rm : RoundMode) (a b : F64) (ha : a.isInf) (hb : b.isInf) :
    (F64.fdiv rm a b).isNaN := by
    simp [fdiv, fdivEx, divExact, divExactWith, decode]
    simp [isNaN_false_of_isInf a ha, ha, isNaN_false_of_isInf b hb, hb]
    simp [roundTo, encode]; native_decide

theorem fma_inf_zero (rm : RoundMode) (a b c : F64) (ha : a.isInf) (hb : b.isZero) :
    (F64.fma rm a b c).isNaN := by
    simp [fma, fmaEx, fmaExact, mulExact, decode]
    simp [isNaN_false_of_isInf a ha, ha, isNaN_false_of_isZero b hb, hb,
          isInf_false_of_isZero b hb]
    simp [roundTo, encode]; native_decide

end F64
