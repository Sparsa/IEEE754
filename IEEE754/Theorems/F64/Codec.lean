/-
  IEEE754.Theorems.F64.Codec
  ==========================
  §11c  F64 IEEE 754 Correctness — Codec round-trip (Decode ∘ Encode = id)
-/

import IEEE754.Theorems.F32.Props
import IEEE754.Theorems.F32.Codec
import IEEE754.Theorems.F64.Classification

open BitVec

namespace F64

-- ── Basic decode properties ───────────────────────────────────────────────────

/-- Decoding a NaN bit pattern yields .nan. -/
theorem decode_nan {f : F64} (h : f.isNaN) : F64.decode f = .nan := by
  simp [decode]; rw [h]; simp

/-- Decoding an Inf bit pattern yields .inf with the correct sign. -/
theorem decode_inf {f : F64} (h : f.isInf) : F64.decode f = .inf f.sign := by
  simp [decode]; rw [h]; simp
  have h2 : ¬f.isNaN := by
    simp [isNaN]; simp [isInf] at h; cases h; rename_i expMax mantIsZero; intros; exact mantIsZero
  simp at h2; exact h2

/-- Decoding any zero bit pattern yields a zero DecodedFloat. -/
theorem decode_isZero {f : F64} (h : f.isZero) : (F64.decode f).isZero := by
  simp [decode]; rw [h]; simp
  have h1 : ¬f.isNaN := by
    simp [isNaN]; simp [isZero] at h; intros; cases h; rename_i mant; exact mant
  simp [isZero] at h; simp [isNaN]
  split
  · cases h; rename_i right left; rename_i h2; cases h2; rename_i h2right h2left
    rw [F64.expIsZero] at right; rw [F64.expIsMax] at h2right
    simp at right; simp [right] at h2right
  · cases h; rename_i right left
    rw [F64.isInf]; rw [left]; simp
    rw [F64.expIsMax]; rw [F64.expIsZero] at right
    simp at right; rw [right]; simp [DecodedFloat.isZero]

-- ── Pack round-trip ───────────────────────────────────────────────────────────

set_option maxRecDepth 4096 in
private theorem pack_sign_expRaw_mantissa (f : F64) :
    F64.pack f.sign f.expRaw f.mantissa = f := by
  simp only [F64.pack, F64.sign, F64.expRaw, F64.mantissa]
  cases f.getLsbD 63 <;> bv_decide

-- ── Encoding special values ───────────────────────────────────────────────────

/-- Encoding .nan always produces a NaN bit pattern. -/
theorem encode_nan_isNaN : (F64.encode DecodedFloat.nan).isNaN := by
  simp [F64.encode]; native_decide

/-- Encoding .inf s produces an Inf bit pattern with the same sign. -/
theorem encode_inf_isInf (s : Bool) :
    (F64.encode (.inf s)).isInf ∧ (F64.encode (.inf s)).sign = s := by
  simp [F64.encode, pack]
  cases s <;> simp <;> native_decide

/-- Encoding a zero DecodedFloat produces a zero bit pattern. -/
theorem encode_zero_isZero (s : Bool) (e : Int) :
    (F64.encode (.finite s e 0)).isZero := by
  simp [F64.encode]; cases s <;> decide

-- ── Codec round-trip ──────────────────────────────────────────────────────────

/-- encode ∘ decode is the identity on normal F64 values. -/
theorem encode_decode_normal {f : F64} (h : f.isNormal) :
    F64.encode (F64.decode f) = f := by
  have hExpZero : f.expIsZero = false := by simp [isNormal] at h; exact h.1
  have hExpMax  : f.expIsMax  = false := by simp [isNormal] at h; exact h.2
  have hNotNaN  : f.isNaN  = false := by simp [isNaN,  hExpMax]
  have hNotInf  : f.isInf  = false := by simp [isInf,  hExpMax]
  have hNotZero : f.isZero = false := by simp [isZero, hExpZero]
  have hMantLt  : f.mantissa.toNat < 2^52 := f.mantissa.isLt
  simp [decode, hNotNaN, hNotInf, hNotZero, h, encode]
  split
  · contradiction
  · contradiction
  · simp_all
    rename_i d s exp mm
    have ⟨sign, base, sig⟩ := mm
    rw [← sign]; simp [significand, h] at sig
    have : 4503599627370496 ||| f.mantissa.toNat % 9007199254740992 ≠ 0 := by grind
    contradiction
  · simp_all
    rename_i heqq
    have ⟨heqql, heqqm, heqqr⟩ := heqq
    simp_all
    split
    · -- biasedExp ≤ 0: impossible since expRaw ≥ 1 for normal
      rename_i sig2 x2 ee2
      have hExpNZ : f.expRaw.toNat ≥ 1 := by
        have : f.expRaw.toNat ≠ 0 := by
          intro heq
          simp [F64.expIsZero] at hExpZero
          exact hExpZero (BitVec.eq_of_toNat_eq heq)
        omega
      have hsigLo : 2^52 ≤ sig2 := by
        rw [← heqqr]; simp [F64.significand, F64.mantissa, h]
        have hhh : (BitVec.toNat f) % 4503599627370496 % 9007199254740992 =
                   BitVec.toNat f % 4503599627370496 := by omega
        simp [hhh]; exact Nat.left_le_or
      have hlog52 : sig2.log2 = 52 := by
        apply Nat.le_antisymm
        · have : sig2 < 2^53 := by rw [← heqqr]; exact f.significand.isLt
          have := Nat.log2_lt (by omega) |>.mpr this; omega
        · exact (Nat.le_log2 (by omega)).mpr hsigLo
      have ss2 : findLeadingBit sig2 (sig2.log2 + 1) = sig2.log2 :=
        F32.findLeadingBit_range (Nat.log2_self_le x2) Nat.lt_log2_self
      rw [ss2, hlog52, ← heqqm] at ee2; omega
    · -- normal branch: prove round-trip
      rename_i sig2 s hh
      have hsigLo : 2^52 ≤ sig2 := by
        rw [← heqqr]; simp [F64.significand, F64.mantissa, h]
        have hhh : (BitVec.toNat f) % 4503599627370496 % 9007199254740992 =
                   BitVec.toNat f % 4503599627370496 := by omega
        simp [hhh]; exact Nat.left_le_or
      have hsigHi : sig2 < 2^53 := by rw [← heqqr]; exact f.significand.isLt
      have hlog52 : sig2.log2 = 52 := by
        apply Nat.le_antisymm
        · have := Nat.log2_lt (by omega) |>.mpr hsigHi; omega
        · exact (Nat.le_log2 (by omega)).mpr hsigLo
      have hExpMaxN : f.expRaw.toNat ≤ 2046 := by
        have : f.expRaw.toNat ≠ 2047 := by
          intro heq; simp [F64.expIsMax, F64.expRaw] at hExpMax
          have h2047 : 2047 = (2047#11).toNat := by decide
          rw [h2047] at heq; exact hExpMax (BitVec.eq_of_toNat_eq (by simp [heq]))
        have := f.expRaw.isLt; omega
      have ss2 : findLeadingBit sig2 (sig2.log2 + 1) = sig2.log2 :=
        F32.findLeadingBit_range (Nat.log2_self_le hh) Nat.lt_log2_self
      rw [ss2]
      rename_i dd ss ee
      have hhi : ¬(0x7FF ≤ ee + ↑sig2.log2 + 1023) := by
        rw [hlog52, ← heqqm]; omega
      simp only [hhi, ↓reduceIte]
      have hexpEnc : setWidth 11 (UInt16.ofNat (ee + ↑sig2.log2 + 1023).toNat).toBitVec = f.expRaw := by
        apply BitVec.eq_of_toNat_eq
        simp [UInt16.ofNat]
        rw [← heqqm]; simp [hlog52]; omega
      have hsig_cast : setWidth 52 (UInt64.ofNat sig2).toBitVec = (sig2 : BitVec 52) := by
        apply BitVec.eq_of_toNat_eq
        simp [UInt64.ofNat]
      have hmantEnc : setWidth 52 (UInt64.ofNat sig2).toBitVec &&& 4503599627370495#52 = f.mantissa := by
        rw [hsig_cast, ← heqqr]; simp [significand, h]
        have fman_52 : f.mantissa.toNat % 9007199254740992 = f.mantissa.toNat := by omega
        simp [fman_52]
        have allones_52 : 4503599627370495#52 = allOnes 52 := by decide
        rw [allones_52, BitVec.and_allOnes]
      rw [hexpEnc, hmantEnc, ← heqql]
      exact pack_sign_expRaw_mantissa f

/-- encode ∘ decode is the identity on subnormal F64 values. -/
theorem encode_decode_subnormal {f : F64} (h : f.isSubnormal) :
    F64.encode (F64.decode f) = f := by
  have hExpZero   : f.expIsZero  = true  := by simp [isSubnormal] at h; exact h.1
  have hMantNZ    : f.mantIsZero = false := by simp [isSubnormal] at h; exact h.2
  have hExpMax    : f.expIsMax   = false := by
    simp only [expIsMax, expIsZero] at *; simp only [beq_iff_eq] at hExpZero; simp [hExpZero]
  have hNotNaN    : f.isNaN      = false := by simp [isNaN,    hExpMax]
  have hNotInf    : f.isInf      = false := by simp [isInf,    hExpMax]
  have hNotZero   : f.isZero     = false := by simp [isZero,   hExpZero, hMantNZ]
  have hNotNormal : f.isNormal   = false := by simp [isNormal, hExpZero]
  have hExpRaw0   : f.expRaw = 0 := by
    simp only [expIsZero, beq_iff_eq] at hExpZero; exact hExpZero
  have hMantLt  : f.mantissa.toNat < 2^52 := f.mantissa.isLt
  have hSigEq   : f.significand.toNat = f.mantissa.toNat := by
    simp [significand, hNotNormal]; omega
  have hSigNZ   : f.significand.toNat ≠ 0 := by
    rw [hSigEq]; intro h0
    have hm0 : f.mantissa = 0 := BitVec.eq_of_toNat_eq h0
    simp [mantIsZero, hm0] at hMantNZ
  have hSigLt   : f.significand.toNat < 2^52 := hSigEq ▸ hMantLt
  have hLeadLe  : findLeadingBit f.significand.toNat (f.significand.toNat.log2 + 1) ≤ 51 := by
    apply Nat.le_trans (F32.findLeadingBit_le _)
    have hlog : f.significand.toNat.log2 < 52 := by rw [Nat.log2_lt hSigNZ]; exact hSigLt
    omega
  have hBiasLe  : (1 - 1023 - 52 : Int) +
      ↑(findLeadingBit f.significand.toNat (f.significand.toNat.log2 + 1)) + 1023 ≤ 0 := by
    omega
  have hAndMask : f.significand.toNat &&& ((1 <<< 52) - 1) = f.significand.toNat := by
    rw [hSigEq]
    have hmask : (1 <<< 52 : Nat) - 1 = (BitVec.allOnes 52).toNat := by native_decide
    have hbv   : f.mantissa &&& BitVec.allOnes 52 = f.mantissa := by simp [allOnes]; bv_decide
    rw [hmask, ← BitVec.toNat_and, hbv]
  have hTrunc : (f.mantissa.toNat.toUInt64.toBitVec.truncate 52) = f.mantissa :=
    BitVec.eq_of_toNat_eq (by
      simp [UInt64.ofNat]
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show f.mantissa.toNat < 2^64 by omega),
          Nat.mod_eq_of_lt hMantLt])
  simp only [decode, hNotNaN, hNotInf, hNotZero, hNotNormal, encode]
  split
  · simp_all
  · simp_all
  · exfalso; simp [significand, hNotNormal] at hSigNZ; simp_all
  · simp_all
    rw [← hExpRaw0]
    rename_i x heq
    have ⟨l, m, r⟩ := heq
    rw [← l]
    rw [Nat.and_comm] at hAndMask
    have h_mant : f.mantissa &&& 4503599627370495#52 = f.mantissa := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, r]
      have h_mask : (4503599627370495#52).toNat = 4503599627370495 := by rfl
      rw [h_mask, Nat.and_comm]; exact hAndMask
    rw [h_mant]
    exact pack_sign_expRaw_mantissa f

end F64
