/-
  IEEE754.Theorems.F64.Sign
  =========================
  §11E  Sign rules (IEEE 754-2019 §6.3)
  §11F  Commutativity (fadd_comm, fmul_comm)
  §11G  Ordering (flt_*, feq_*)
  §11H  Cancellation and additive identity
  §11I  FMA: true single rounding
  §11J  Square root
-/

import IEEE754.Theorems.F64.Inf

open BitVec

namespace F64

-- ── E. Sign rules (IEEE 754-2019 §6.3) ───────────────────────────────────────

/-- The product sign is XOR of operand signs (when result is not NaN). -/
theorem fmul_sign_xor {rm : RoundMode} {a b : F64}
    (hna : ¬a.isNaN) (hnb : ¬b.isNaN)
    (hza : ¬a.isZero) (hzb : ¬b.isZero)
    (hr  : ¬(F64.fmul rm a b).isNaN) :
    (F64.fmul rm a b).sign = (a.sign != b.sign) := by
    simp [fmul]; simp [fmulEx]; simp [mulExact]
    split
    · { simp [roundTo]; simp [encode]; simp_all; rename_i heq; simp [sign] }
    · { simp_all; simp [roundTo]; simp [encode] }
    · { simp_all; simp [roundTo]; simp [encode] }
    · { simp [roundTo]; simp [encode] }
    · { simp [roundTo]; simp [encode]; simp [pack] }
    · { simp_all }

/-- The quotient sign is XOR of operand signs (when result is not NaN). -/
theorem fdiv_sign_xor {rm : RoundMode} {a b : F64}
    (hna : ¬a.isNaN) (hnb : ¬b.isNaN)
    (hza : ¬a.isZero) (hzb : ¬b.isZero)
    (hr  : ¬(F64.fdiv rm a b).isNaN) :
    (F64.fdiv rm a b).sign = (a.sign != b.sign) := by
    simp [fdiv]; simp [fdivEx]; simp [divExact]; simp [divExactWith]
    split
    · {
      simp [roundTo]; simp [encode]; simp_all; rename_i heq
      simp [sign]; simp [decode] at heq; simp [hna] at heq; simp [hza] at heq
      simp [qNaN]; simp [pack]
    }
    · { simp_all; simp [roundTo]; simp [encode]; simp [qNaN]; simp [sign]; simp [pack] }
    · { simp [roundTo]; simp [encode]; simp [qNaN]; simp_all; simp [sign]; simp [pack] }
    · { simp [roundTo]; simp [encode]; simp [qNaN]; simp_all; simp [sign]; simp [pack] }
    · {
      simp [roundTo]; simp [encode]; simp_all; simp [sign]; simp [pack]
      split <;> · { simp_all }
    }

-- ── F. Commutativity ──────────────────────────────────────────────────────────

/-- fadd is commutative (bit-exact result). -/
theorem fadd_comm (rm : RoundMode) (a b : F64) :
    F64.fadd rm a b = F64.fadd rm b a := by
    simp [fadd]; simp [faddEx]
    rw [F32.addExact_comm]

/-- fmul is commutative (bit-exact result). -/
theorem fmul_comm (rm : RoundMode) (a b : F64) :
    F64.fmul rm a b = F64.fmul rm b a := by
    simp [fmul]; simp [fmulEx]
    rw [F32.mulExact_comm]

-- ── G. Ordering (IEEE 754-2019 §5.10, §5.11) ─────────────────────────────────

/-- flt is irreflexive. -/
theorem flt_irrefl (a : F64) : F64.flt a a = false := by
  simp [flt]
  split <;> simp_all
  split
  · simp_all
  · simp_all
  · intro hh; rfl
  · simp_all

/-- flt is asymmetric. -/
theorem flt_asymm {a b : F64} (h : F64.flt a b) : F64.flt b a = false := by
  simp [flt] at *
  split at h <;> split <;> simp_all <;>
  split
  · simp_all
  · rfl
  · simp_all; exact Nat.le_of_lt h.2
  · simp_all; exact Nat.le_of_lt h.2

/-- flt is transitive. -/
theorem flt_trans {a b c : F64}
    (h1 : F64.flt a b) (h2 : F64.flt b c) : F64.flt a c := by
    simp [F64.flt] at *
    have ⟨h1r, h1m, h1l⟩ := h1
    have ⟨h2r, h2m, h2l⟩ := h2
    sorry

/-- NaN comparisons always return false (IEEE 754 §5.11 "unordered"). -/
theorem flt_nan_l (a b : F64) (h : a.isNaN) : F64.flt a b = false := by
  simp [flt]; split <;> simp_all

theorem flt_nan_r (a b : F64) (h : b.isNaN) : F64.flt a b = false := by
  simp [flt]; split <;> simp_all

theorem feq_nan_l (a b : F64) (h : a.isNaN) : F64.feq a b = false := by
  simp [feq]; simp_all

theorem feq_nan_r (a b : F64) (h : b.isNaN) : F64.feq a b = false := by
  simp [feq]; simp_all

-- ── H. Cancellation and additive identity ─────────────────────────────────────

private theorem negate_mantissa (f : F64) : f.negate.mantissa = f.mantissa := by
  simp only [negate, mantissa, BitVec.truncate_eq_setWidth, BitVec.setWidth_xor]
  have : ((1 <<< 63 : BitVec 64)).setWidth 52 = 0 := by decide
  simp [this]

private theorem negate_expRaw' (f : F64) : f.negate.expRaw = f.expRaw := by
  simp only [negate, expRaw, BitVec.truncate_eq_setWidth,
             BitVec.ushiftRight_xor_distrib, BitVec.setWidth_xor]
  have : (((1 <<< 63 : BitVec 64)) >>> 52).setWidth 11 = 0 := by decide
  simp [this]

private theorem negate_isNaN' (f : F64) : f.negate.isNaN = f.isNaN := by
  simp [isNaN, expIsMax, mantIsZero, negate_expRaw', negate_mantissa]

private theorem negate_isInf' (f : F64) : f.negate.isInf = f.isInf := by
  simp [isInf, expIsMax, mantIsZero, negate_expRaw', negate_mantissa]

private theorem negate_isZero' (f : F64) : f.negate.isZero = f.isZero := by
  simp [isZero, expIsZero, mantIsZero, negate_expRaw', negate_mantissa]

private theorem negate_isNormal' (f : F64) : f.negate.isNormal = f.isNormal := by
  simp [isNormal, expIsZero, expIsMax, negate_expRaw']

private theorem negate_significand' (f : F64) : f.negate.significand = f.significand := by
  simp [significand, negate_isNormal', negate_mantissa]

private theorem negate_sign (f : F64) : f.negate.sign = !f.sign := by
  simp [negate, sign, getLsbD]
  cases f.negate.sign with
  | true  => simp [Nat.testBit]
  | false => simp [Nat.testBit]

private theorem addExact_opp_cancel (rm : RoundMode) (s : Bool) (e : Int) (sig : Nat) :
    ∃ s', (addExact rm (.finite s e sig) (.finite (!s) e sig)).1 = .finite s' 0 0 := by
  by_cases h0 : sig = 0
  · subst h0
    exact ⟨s && !s || (s || !s) && (rm == .RDN), by simp [addExact]⟩
  · refine ⟨rm == .RDN, ?_⟩
    have hb : (sig == 0) = false := by simpa using h0
    have hne : (s == !s) = false := by cases s <;> rfl
    have hdiff : (e - e : Int).toNat = 0 := by omega
    simp only [addExact, hb, Bool.false_and, Bool.and_false, ite_false,
               if_pos (le_refl e), hdiff, Nat.shiftLeft_zero, hne,
               ge_iff_le, le_refl, ite_true, Nat.sub_self,
               show (0 : Nat) == 0 = true from rfl]

/-- x − x = ±0 for any finite non-NaN non-Inf F64. -/
theorem fsub_self_isZero (rm : RoundMode) (a : F64) (h : ¬a.isNaN) (hi : ¬a.isInf) :
    (F64.fsub rm a a).isZero := by
  have hNaN : a.isNaN = false := by simpa using h
  have hInf : a.isInf = false := by simpa using hi
  have hn_isNaN : a.negate.isNaN = false := (negate_isNaN' a).trans hNaN
  have hn_isInf : a.negate.isInf = false := (negate_isInf' a).trans hInf
  cases hZ : a.isZero
  · obtain ⟨s₀, hadd⟩ := addExact_opp_cancel rm a.sign
        ((if a.isNormal then (a.expRaw.toNat : Int) else 1) - 1023 - 52) a.significand.toNat
    have hdec : F64.decode a = .finite a.sign
        ((if a.isNormal then (a.expRaw.toNat : Int) else 1) - 1023 - 52) a.significand.toNat := by
      simp [decode, hNaN, hInf, hZ]
    have hdecn : F64.decode a.negate = .finite (!a.sign)
        ((if a.isNormal then (a.expRaw.toNat : Int) else 1) - 1023 - 52) a.significand.toNat := by
      simp [decode, hn_isNaN, hn_isInf, (negate_isZero' a).trans hZ,
            negate_sign, negate_isNormal', negate_expRaw', negate_significand']
    have hfadd : (F64.faddEx rm a a.negate).1 = F64.encode (.finite s₀ 0 0) := by
      simp only [faddEx, hdec, hdecn, hadd, roundTo]
    simp only [fsub, hfadd]
    exact encode_zero_isZero s₀ 0
  · obtain ⟨s₀, hadd⟩ := addExact_opp_cancel rm a.sign 0 0
    have hdec : F64.decode a = .finite a.sign 0 0 := by simp [decode, hNaN, hInf, hZ]
    have hdecn : F64.decode a.negate = .finite (!a.sign) 0 0 := by
      simp [decode, hn_isNaN, hn_isInf, (negate_isZero' a).trans hZ, negate_sign]
    have hfadd : (F64.faddEx rm a a.negate).1 = F64.encode (.finite s₀ 0 0) := by
      simp only [faddEx, hdec, hdecn, hadd, roundTo]
    simp only [fsub, hfadd]
    exact encode_zero_isZero s₀ 0

/-- +0 is a right additive identity under IEEE equality (for non-NaN a). -/
theorem fadd_posZero_r (rm : RoundMode) (a : F64) (h : ¬a.isNaN) :
    F64.feq (F64.fadd rm a F64.posZero) a := by
    sorry

-- ── I. FMA: true single rounding ──────────────────────────────────────────────

theorem fma_is_single_rounded (rm : RoundMode) (a b c : F64) :
    F64.fma rm a b c = (F64.fmaEx rm a b c).1 := rfl

theorem fmaEx_flags_eq (rm : RoundMode) (a b c : F64) :
    (F64.fmaEx rm a b c).2 =
    (fmaExact rm (F64.decode a) (F64.decode b) (F64.decode c)).2.merge
    (roundTo f64Fmt rm (fmaExact rm (F64.decode a) (F64.decode b) (F64.decode c)).1).2 := by
  simp [F64.fmaEx]

theorem fma_ne_mul_then_add :
    ∃ (a b c : F64),
      F64.fma .RNE a b c ≠ F64.fadd .RNE (F64.fmul .RNE a b) c := by
  sorry  -- requires finding specific F64 bit patterns

-- ── J. Square root ────────────────────────────────────────────────────────────

theorem fsqrt_is_single_rounded (rm : RoundMode) (a : F64) :
    F64.fsqrt rm a = (F64.fsqrtEx rm a).1 := rfl

/-- √(NaN) = NaN (NaN propagation §6.2). -/
theorem fsqrt_nan (rm : RoundMode) (a : F64) (h : a.isNaN) :
    (F64.fsqrt rm a).isNaN := by
    simp [F64.fsqrt]; simp [fsqrtEx]; simp [decode]
    rw [h]; simp; simp [sqrtExact]; simp [roundTo]; simp [encode]; native_decide

/-- √(-∞) raises invalidOp and returns NaN (§7.2). -/
theorem fsqrt_negInf_isNaN (rm : RoundMode) :
    (F64.fsqrt rm F64.negInf).isNaN ∧ (F64.fsqrtEx rm F64.negInf).2.invalidOp := by
    have neg_inf_is_not_nan : negInf.isNaN = false := by native_decide
    have neg_inf_is_inf : negInf.isInf = true := by native_decide
    have neg_inf_not_zero : negInf.isZero = false := by native_decide
    have neg_inf_sign_true : negInf.sign = true := by native_decide
    constructor
    · simp [fsqrt]; simp [fsqrtEx]; simp [decode]
      rw [neg_inf_is_not_nan, neg_inf_is_inf, neg_inf_not_zero, neg_inf_sign_true]
      simp; simp [sqrtExact]; simp [roundTo]; simp [encode]; native_decide
    · simp [fsqrtEx]; simp [decode]
      rw [neg_inf_is_not_nan, neg_inf_is_inf, neg_inf_not_zero, neg_inf_sign_true]
      simp; simp [sqrtExact]; simp [roundTo]; native_decide

/-- √(+∞) = +∞ (no exception). -/
theorem fsqrt_posInf (rm : RoundMode) :
    F64.fsqrt rm F64.posInf = F64.posInf := by
    simp [fsqrt]; simp [fsqrtEx]; simp [decode]
    have pos_inf_not_nan : posInf.isNaN = false := by native_decide
    have pos_inf_inf : posInf.isInf = true := by native_decide
    have pos_inf_nz : posInf.isZero = false := by native_decide
    have pos_inf_sign : posInf.sign = false := by native_decide
    rw [pos_inf_not_nan, pos_inf_inf, pos_inf_nz]; simp
    unfold sqrtExact; simp [pos_inf_sign]; simp [roundTo]; simp [encode]
    simp [pack]; native_decide

/-- √(+0) = +0 (IEEE 754 §6.3). -/
theorem fsqrt_posZero (rm : RoundMode) :
    F64.fsqrt rm F64.posZero = F64.posZero := by
    have pos_zero_not_nan : posZero.isNaN = false := by native_decide
    have pos_zero_is_zero : posZero.isZero = true := by native_decide
    have pos_zero_not_inf : posZero.isInf = false := by native_decide
    have pos_zero_sign_false : posZero.sign = false := by native_decide
    simp [fsqrt]; simp [fsqrtEx]; simp [decode]
    rw [pos_zero_not_nan, pos_zero_is_zero, pos_zero_not_inf, pos_zero_sign_false]
    simp; simp [sqrtExact]; simp [roundTo]; simp [encode]; native_decide

/-- √(−0) = −0 (IEEE 754 §6.3: sign of zero is preserved). -/
theorem fsqrt_negZero (rm : RoundMode) :
    F64.fsqrt rm F64.negZero = F64.negZero := by
    have neg_zero_not_nan : negZero.isNaN = false := by native_decide
    have neg_zero_is_zero : negZero.isZero = true := by native_decide
    have neg_zero_not_inf : negZero.isInf = false := by native_decide
    have neg_zero_sign_true : negZero.sign = true := by native_decide
    simp [fsqrt]; simp [fsqrtEx]; simp [decode]
    rw [neg_zero_not_nan, neg_zero_is_zero, neg_zero_not_inf, neg_zero_sign_true]
    simp; simp [sqrtExact]; simp [roundTo]; simp [encode]; native_decide

-- ── Sign-preservation helpers for fsqrt_nonneg ───────────────────────────────

private theorem pack_sign_false (e : BitVec 11) (m : BitVec 52) :
    (F64.pack false e m).sign = false := by simp [pack, sign]

private theorem pack_sign_true (e : BitVec 11) (m : BitVec 52) :
    (F64.pack true e m).sign = true := by simp [pack, sign]

private theorem pack_sign (s : Bool) (e : BitVec 11) (m : BitVec 52) :
    (F64.pack s e m).sign = s := by
  cases s
  · exact pack_sign_false e m
  · exact pack_sign_true e m

private theorem sqrtExact_false_dfSign (e : Int) (sig : Nat) :
    (sqrtExact (.finite false e sig)).1.dfSign = false := by
  match sig with
  | 0     => simp [sqrtExact, DecodedFloat.dfSign]
  | _ + 1 => simp [sqrtExact, DecodedFloat.dfSign]

private theorem encode_false_sign (d : DecodedFloat) (hs : d.dfSign = false) :
    (F64.encode d).sign = false := by
  match d with
  | .nan             => simp [encode, qNaN, pack, sign]
  | .inf false       => simp [encode]; exact pack_sign_false _ _
  | .inf true        => simp [DecodedFloat.dfSign] at hs
  | .finite false _ 0        => simp [encode]; exact pack_sign_false _ _
  | .finite false e (_ + 1) =>
    simp only [encode]
    split
    · exact pack_sign_false _ _
    · split
      · simp [posInf, pack, sign]
      · exact pack_sign_false _ _
  | .finite true _ _ => simp [DecodedFloat.dfSign] at hs

/-- The result of fsqrt is always non-negative when the input is non-negative. -/
theorem fsqrt_nonneg (rm : RoundMode) (a : F64) (h : ¬(F64.fsqrt rm a).isNaN)
    (anNeg : a.sign = false) :
    (F64.fsqrt rm a).sign = false := by
  have hnan : a.isNaN = false := by
    by_contra hnn
    push_neg at hnn; simp at h
    simp [fsqrt] at h; simp [fsqrtEx] at h; simp [sqrtExact] at h
    have adnan : a.decode = DecodedFloat.nan := by simp [decode, hnn]
    simp [adnan] at h; simp [roundTo] at h; simp [encode] at h
    simp [qNaN] at h; simp [pack] at h; simp [isNaN] at h
    simp [expIsMax, mantIsZero] at h; simp [expRaw] at h; simp [mantissa] at h
  simp only [F64.fsqrt, fsqrtEx]
  have decode_sign : (decode a).dfSign = false := by
    simp only [decode, hnan, anNeg]
    split <;> simp [DecodedFloat.dfSign]
    grind
  have sqrt_sign : (sqrtExact (decode a)).1.dfSign = false := by
    cases hinf : a.isInf with
    | true =>
      simp only [decode, hnan, hinf, anNeg, ↓reduceIte, sqrtExact, DecodedFloat.dfSign]
      grind
    | false =>
      cases hzero : a.isZero with
      | true =>
        simp only [decode, hnan, hinf, hzero, anNeg, ↓reduceIte, sqrtExact, DecodedFloat.dfSign]
        grind
      | false =>
        simp only [decode, hnan, hinf, hzero, anNeg]
        exact sqrtExact_false_dfSign _ _
  exact encode_false_sign _
    (F32.roundTo_false_dfSign f64Fmt rm (sqrtExact (decode a)).1 sqrt_sign)

theorem fsqrtEx_flags_eq (rm : RoundMode) (a : F64) :
    (F64.fsqrtEx rm a).2 =
    (sqrtExact (F64.decode a)).2.merge
    (roundTo f64Fmt rm (sqrtExact (F64.decode a)).1).2 := by
  simp [F64.fsqrtEx]

end F64
