/-
  IEEE754.Theorems.Codec
  ======================
  §11c  F32 IEEE 754 Correctness — Codec round-trip (Decode ∘ Encode = id)
        encode_decode_normal, encode_decode_subnormal, and related helpers
-/

import IEEE754.Theorems.Props
import IEEE754.Theorems.Classification

open BitVec

namespace F32

-- ── A. Codec round-trip (Decode then Encode = identity) ──────────────────────

/-- Decoding a NaN bit pattern yields .nan. -/
theorem decode_nan {f : F32} (h : f.isNaN) : F32.decode f = .nan := by
  simp [decode]
  rw [h]
  simp

/-- Decoding an Inf bit pattern yields .inf with the correct sign. -/
theorem decode_inf {f : F32} (h : f.isInf) : F32.decode f = .inf f.sign := by
  simp [decode]
  rw [h]
  simp
  have h2 : ¬f.isNaN := by
    simp [isNaN]
    simp [isInf] at h
    cases h
    . rename_i expMax mantIsZero
      intros
      exact mantIsZero
  simp at h2
  exact h2

/-- Decoding any zero bit pattern yields a zero DecodedFloat. -/
theorem decode_isZero {f : F32} (h : f.isZero) : (F32.decode f).isZero := by
  simp [decode]
  rw [h]
  simp
  have h1 : ¬f.isNaN := by
    simp [isNaN]
    simp [isZero] at h
    intros
    cases h
    rename_i mant
    exact mant
  simp [isZero] at h
  simp [isNaN]
  split
  ·
    cases h
    rename_i right left
    rename_i h2
    cases h2
    rename_i h2right h2left
    rw [F32.expIsZero] at right
    rw [F32.expIsMax] at h2right
    simp at right
    simp [right ] at  h2right
  ·
   cases h
   rename_i right left
   rw [F32.isInf]
   rw [left]
   simp
   rw [F32.expIsMax]
   rw [F32.expIsZero] at right
   simp at right
   rw [right]
   simp [DecodedFloat.isZero]

-- ── Helpers for encode_decode_normal ─────────────────────────────────────────
theorem two_pow (a : Nat) : a = 2^n → a.log2 = n := by
  intro h
  rw [h]
  rw [Nat.log2_two_pow]

theorem findLeadingBit_go_le (v p : Nat) : findLeadingBit.go v p ≤ p := by
  induction p with
  | zero => unfold findLeadingBit.go; simp
  | succ q ih =>
    unfold findLeadingBit.go
    split
    · omega
    · omega

theorem findLeadingBit_le (v : Nat) :
    findLeadingBit v (v.log2 + 1) ≤ v.log2 := by
  unfold findLeadingBit findLeadingBit.go
  have hbit : v.testBit (v.log2 + 1) = false := by
    rw [Nat.testBit_lt_two_pow Nat.lt_log2_self]  -- testBit is false above the highest bit
  simp [hbit]
  exact findLeadingBit_go_le v v.log2

/-- Reconstructing a 32-bit float from its (sign, expRaw, mantissa) fields gives back
    the original value: the three fields are disjoint and cover all 32 bits. -/
private theorem mantissa_index (f:F32) (i:Nat) (h: i< 23) : f.mantissa[i] = f[i] := by
  simp [F32.mantissa, BitVec.getLsbD ]
  rfl





example {i n:Nat} (m: BitVec n) (h:i < n) :
  m[i] = m.getLsbD i := by exact?

--have hii: (2147483648#32)[i] = (2147483648#32).getLsbD i := by
--    exact Eq.symm (BitVec.getLsbD_eq_getElem h)

theorem sign_bit_getLsbD_false {i : Nat} (h : i < 31) :
    (2147483648#32)[i]= false := by
  simp [← BitVec.getLsbD_eq_getElem]
  simp [BitVec.getLsbD_ofNat]
  rw [show (2147483648 : Nat) = 1 <<< 31 from by decide]
  rw [Nat.testBit_shiftLeft]
  intro
  simp
  intro
  simp [Nat.testBit]
  omega

theorem pack_sign_expRaw_mantissa (f : F32) :
    F32.pack f.sign f.expRaw f.mantissa = f := by
  simp only [F32.pack, F32.sign, F32.expRaw, F32.mantissa]
  split
  ·{
    simp_all
    apply eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.getLsbD_setWidth]
    simp [hi]
    by_cases h23 : i < 23
    ·{
      simp [h23]
      -- only 31'th bit is true rest is false
      have h_l_31 : i < 31 := by omega
      have hi_23 :  (2147483648#32)[i] = false := by  exact  sign_bit_getLsbD_false h_l_31
      simp_all
    }
    ·{
      simp_all
      by_cases h32 : i = 31
      ·{
        simp_all
      }
      ·{
        have h23' : ¬ (i < 23) := by simp_all
        simp [h23']
        simp_all
        have h2332 : i - 23 < 32 := by
          by_cases h233 : i > 23
          ·{
            simp_all
            omega
          }
          ·{
            simp_all
          }
        simp[h2332]
        --- only 31th bit is true rest is false, and h32 tells us that i != 31
        have h_l_31 : i < 31 := by omega
        have hi_31 : ((2147483648#32)[i] = false) := by exact sign_bit_getLsbD_false h_l_31
        simp [hi_31]
        intro
        omega
      }
    }
  }
  ·{
    simp_all
    apply eq_of_getLsbD_eq
    intro i hi
    simp_all
    by_cases h23 : i < 23
    ·{
      simp [h23]
    }
    ·{
      simp [h23]
      simp at h23
      simp_all
      by_cases h31 : i = 31
      ·{
        simp_all
      }
      ·{
        intro
        omega
      }

    }

  }


/-- findLeadingBit of any n in [2^k, 2^(k+1)) equals k. -/
private theorem findLeadingBit_range {n k : Nat} (hge : 2^k ≤ n) (hlt : n < 2^(k+1)) :
    findLeadingBit n (n.log2 + 1) = k := by
  have hlog : n.log2 = k := (Nat.log2_eq_iff (by omega)).mpr ⟨hge, hlt⟩
  rw [hlog]
  have hhi : n.testBit (k + 1) = false := Nat.testBit_lt_two_pow hlt
  have hlo : n.testBit k = true  :=
    Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hge hlt
  induction k with
  | zero =>
    simp [findLeadingBit]
    simp [findLeadingBit.go]
    simp_all
  | succ x ih =>
    simp [findLeadingBit]
    simp [findLeadingBit.go]
    simp [hhi]
    intro xi
    rw [xi] at hlo
    contradiction





/-- Nat → UInt8 → BitVec 8: toNat recovers n when n < 256. -/
private theorem nat_toUInt8_toBitVec_toNat {n : Nat} (h : n < 256) :
    n.toUInt8.toBitVec.toNat = n := by
  have : n.toUInt8.toBitVec = BitVec.ofNat 8 n := rfl
  rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Nat → UInt32 → BitVec 32 → truncate 23: toNat recovers n when n < 2^23. -/
private theorem nat_toUInt32_trunc23_toNat {n : Nat} (h : n < 2^23) :
    (n.toUInt32.toBitVec.truncate 23).toNat = n := by
  have step1 : n.toUInt32.toBitVec = BitVec.ofNat 32 n := rfl
  simp only [step1, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
             BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2^32 by omega),
             Nat.mod_eq_of_lt h]

 -- 2^ 23 ||| f.mantissa.toNat = 2 ^ 23 + f.mantissa.toNat



--- encode_decode_normal
theorem encode_decode_normal {f : F32} (h : f.isNormal) :
    F32.encode (F32.decode f) = f := by
  have hExpZero : f.expIsZero = false := by simp [isNormal] at h; exact h.1
  have hExpMax  : f.expIsMax  = false := by simp [isNormal] at h; exact h.2
  have hNotNaN  : f.isNaN  = false := by simp [isNaN,  hExpMax]
  have hNotInf  : f.isInf  = false := by simp [isInf,  hExpMax]
  have hNotZero : f.isZero = false := by simp [isZero, hExpZero]
  have hNotsub  : f.isSubnormal = false := by exact isSubnormal_false_of_isNormal f h
  have hMantLt  : f.mantissa.toNat < 2^23 := f.mantissa.isLt
  have exp_23 : 8388608 = 2^ 23 := by decide
  have exp_24 : 16777216 = 2^ 24 := by decide
  simp [decode]
  simp [hNotNaN,hNotInf,hNotZero,h]
  simp [encode]
  split
  ·{
    contradiction
  }
  ·{
    contradiction
  }
  ·{
    simp_all
    rename_i d s exp mm
    have ⟨ sign, base,sig⟩ := mm
    rw [← sign]
    simp [significand] at sig
    simp [h] at sig
    have sig_g0 : 8388608 ||| f.mantissa.toNat % 16777216 ≠ 0 := by grind
    contradiction
  }
  ·{
    simp_all
    rename_i heqq
    have ⟨heqql,heqqm,heqqr ⟩ := heqq
    simp_all
    split
    ·{
      have allones_23 : 8388607#23 = allOnes 23 := by decide
      -- rw [allones_23]
      simp [← heqqr]
      simp [significand]
      simp [h]
      have mant:  f.mantissa.toNat % 16777216 = f.mantissa.toNat := by omega
      rw [mant]
      have set: (setWidth 23 (UInt32.ofNat f.mantissa.toNat).toBitVec )= f.mantissa := by
        apply BitVec.eq_of_toNat_eq
        simp [ UInt32.ofNat]
      rw[set]
      rw [allones_23]
      rw [BitVec.and_allOnes]
      rw [← heqql]
      simp [expIsZero] at hExpZero
      rename_i sig2 x2 ee2
      have hg3 : 2^(sig2.log2) ≤ sig2 := by refine Nat.log2_self_le x2
      have hg4 : sig2 < 2^(sig2.log2 + 1) := by  exact Nat.lt_log2_self
      have ss2 : findLeadingBit sig2 (sig2.log2+ 1) = sig2.log2 := by
        exact findLeadingBit_range hg3 hg4
      rw [ss2] at ee2
      exfalso
      have hsigLo : 2^23 ≤ sig2 := by
        rw [← heqqr]
        simp [F32.significand, F32.mantissa] at hMantLt ⊢
        simp [h]

        have hhh: (BitVec.toNat f) % 8388608 % 16777216 = BitVec.toNat f % 8388608 := by omega
        simp [hhh]
        exact Nat.left_le_or
      have hlog23 : sig2.log2 = 23 := by
        apply Nat.le_antisymm
        · have : sig2 < 2^24 := by rw [← heqqr]; exact f.significand.isLt
          have := Nat.log2_lt (by omega) |>.mpr this
          omega
        ·
            refine (Nat.le_log2 ?_).mpr hsigLo
            omega
      have hexpNZ : f.expRaw.toNat ≥ 1 := by
        have : f.expRaw.toNat ≠ 0 := by
          intro heq
          exact hExpZero (BitVec.eq_of_toNat_eq (by simp [heq]))
        omega
      rw [hlog23, ← heqqm] at ee2

      omega  -- ee2 becomes expRaw ≤ 0 but expRaw ≥ 1
    }
    ·{
      rename_i sig2 s hh
      have hg3 : 2^(sig2.log2) ≤ sig2 := by refine Nat.log2_self_le s
      have hg4 : sig2 < 2^(sig2.log2 + 1) := by  exact Nat.lt_log2_self
      have ss2 : findLeadingBit sig2 (sig2.log2+ 1) = sig2.log2 := by
        exact findLeadingBit_range hg3 hg4
      rw [ss2]
      rw [ss2] at hh
      simp at hh
      have set: (setWidth 23 (UInt32.ofNat sig2).toBitVec )= sig2 := by
        apply BitVec.eq_of_toNat_eq
        simp [ UInt32.ofNat]
      rw [set]
      have allones_23 : 8388607#23 = allOnes 23 := by decide
      --rw [allones_23]
      --simp [BitVec.and_allOnes]
      -- sig2.log2 = 23 since significand is a normal 24-bit value with leading bit
      have hsigLo : 2^23 ≤ sig2 := by
        rw [← heqqr]
        simp [F32.significand, F32.mantissa] at hMantLt ⊢
        simp [h]

        have hhh: (BitVec.toNat f) % 8388608 % 16777216 = BitVec.toNat f % 8388608 := by omega
        simp [hhh]
        exact Nat.left_le_or
      have hsigHi : sig2 < 2^24 := by rw [← heqqr]; exact f.significand.isLt
      have hlog23 : sig2.log2 = 23 := by
        apply Nat.le_antisymm
        · have : sig2 < 2^24 := by rw [← heqqr]; exact f.significand.isLt
          have := Nat.log2_lt (by omega) |>.mpr this
          omega
        ·
            refine (Nat.le_log2 ?_).mpr hsigLo
            omega

      -- Rule out overflow branch
      have hExpMaxN : f.expRaw.toNat ≤ 254 := by
        have : f.expRaw.toNat ≠ 255 := by
          intro heq
          simp [F32.expIsMax, F32.expRaw] at hExpMax
          have h255: 255  = (255#8).toNat := by decide
          rw [h255] at heq
          have ff : f.expRaw = 255#8 := by grind
          exact hExpMax ff
        have := f.expRaw.isLt; omega
      rename_i dd ss ee
      have hhi : ¬(255 ≤ ee + ↑sig2.log2 + 127) := by
        rw [hlog23, ← heqqm]; omega
      simp only [hhi, ↓reduceIte]
      -- Goal: pack s✝ (UInt8.ofNat (e✝ + sig2.log2 + 127).toNat).toBitVec (sig2 &&& 8388607#23) = f

      -- Exponent round-trips: e✝ + 23 + 127 = expRaw
      have hexpEnc : (UInt8.ofNat (ee + ↑sig2.log2 + 127).toNat).toBitVec = f.expRaw := by
        apply BitVec.eq_of_toNat_eq
        simp [UInt8.ofNat]
        rw [← heqqm]
        simp [hlog23]
        omega
      -- Mantissa: sig2 &&& 8388607#23 = f.mantissa
      have hmantEnc : (↑sig2 : BitVec 23) &&& 8388607#23 = f.mantissa := by

       -- apply BitVec.eq_of_toNat_eq

        -- simp [BitVec.toNat_and]
        rw [← heqqr]
        simp [significand]
        simp [h]
        have fman_23 : f.mantissa.toNat % 16777216 = f.mantissa.toNat := by omega
        simp [fman_23]
        rw [allones_23]
        rw [BitVec.and_allOnes]

      rw [hexpEnc, hmantEnc, ← heqql]
      apply pack_sign_expRaw_mantissa

    }
  }

example (n m : Nat) : (n ||| m % n)  = n+ m % n := by apply?
example (n k: Nat) : n % 2^k = n &&& (2^k -1) := by exact?
example (n k : Nat) (h: 2^k ≤ n ) : k ≤ n.log2 := by apply?
example (n k : Nat) : n ≤ n ||| k % n := by exact?
example {n k : Nat} (h:k < n) : k%n = k := by exact?
example {n: Nat} : 2^(n.log2) ≤ n := by apply?
example {n:Nat} : n < 2^(n.log2+1) := by apply?
example {k n : Nat} (Hn : n < 2^k) :  n % 2^k ||| 2^k  =  n%2^k  + 2^k := by apply?
-- ── findLeadingBit auxiliary lemmas ──────────────────────────────────────────

theorem BitVec.toNat_log2_le (a : BitVec n) : a.toNat.log2 ≤ n := by
  have hlt := a.isLt
  rcases Nat.eq_zero_or_pos a.toNat with h | h
  · simp [h]
  · have : a.toNat.log2 < n + 1 := by
      have h2 : a.toNat ≠ 0 := by omega
      rw [Nat.log2_lt h2]
      omega
    omega

-- ── encode_decode_subnormal ───────────────────────────────────────────────────

/-- encode ∘ decode is the identity on subnormal F32 values. -/
theorem encode_decode_subnormal {f : F32} (h : f.isSubnormal) :
    F32.encode (F32.decode f) = f := by
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
  -- Numeric bounds
  have hMantLt  : f.mantissa.toNat < 2^23 := f.mantissa.isLt
  have hSigEq   : f.significand.toNat = f.mantissa.toNat := by
    simp [significand, hNotNormal]
    omega
  have hSigNZ   : f.significand.toNat ≠ 0 := by
    rw [hSigEq]; intro h0
    have hm0 : f.mantissa = 0 := BitVec.eq_of_toNat_eq h0
    simp [mantIsZero, hm0] at hMantNZ
  have hSigLt   : f.significand.toNat < 2^23 := hSigEq ▸ hMantLt
  -- leadPos ≤ 22 → biasedExp = leadPos - 22 ≤ 0
  have hLeadLe : findLeadingBit f.significand.toNat (f.significand.toNat.log2 + 1) ≤ 22 := by
    apply Nat.le_trans (findLeadingBit_le _)
    have hlog : f.significand.toNat.log2 < 23 := by rw [Nat.log2_lt hSigNZ]; exact hSigLt
    omega
  have hBiasLe : (1 - 127 - 23 : Int) +
      ↑(findLeadingBit f.significand.toNat (f.significand.toNat.log2 + 1)) + 127 ≤ 0 := by
    have hle : findLeadingBit f.significand.toNat (f.significand.toNat.log2 + 1) ≤ 22 := hLeadLe
    omega
  -- AND-mask identity: sig &&& (2^23-1) = sig
  have hAndMask : f.significand.toNat &&& ((1 <<< 23) - 1) = f.significand.toNat := by
    rw [hSigEq]
    have hmask : (1 <<< 23 : Nat) - 1 = (BitVec.allOnes 23).toNat := by native_decide
    have hbv : f.mantissa &&& BitVec.allOnes 23 = f.mantissa := by
      simp [allOnes] ; bv_decide
    rw [hmask]
    rw [← BitVec.toNat_and]
    rw [hbv]
  -- Truncate identity
  have hTrunc : (f.mantissa.toNat.toUInt32.toBitVec.truncate 23) = f.mantissa :=
    BitVec.eq_of_toNat_eq (nat_toUInt32_trunc23_toNat hMantLt)
  -- Reduce decode
  simp only [decode, hNotNaN, hNotInf, hNotZero, hNotNormal]
  -- Reduce encode and case-split
  simp only [encode]
  split
  · simp_all  -- .nan: contradiction
  · simp_all  -- .inf: contradiction
  · -- .finite s _ 0: sig=0 contradicts hSigNZ
    exfalso; simp [significand, hNotNormal] at hSigNZ
    simp_all
  · -- .finite s e sig (sig ≠ 0): the biasedExp ≤ 0 branch is the only valid one
    simp_all
    rw [ ← hExpRaw0]
    rename_i x heq
    have ⟨l,m,r⟩ := heq
    rw [← l]
    rw [Nat.and_comm] at hAndMask
    have h_mant : f.mantissa &&& 8388607#23 = f.mantissa := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and]
      rw [r]
      have h_mask : (8388607#23).toNat = 8388607 := by rfl
      rw [h_mask, Nat.and_comm]
      exact hAndMask
    rw [h_mant]
    exact pack_sign_expRaw_mantissa f


-- ── Encoding special values ───────────────────────────────────────────────────

/-- Encoding .nan always produces a NaN bit pattern. -/
theorem encode_nan_isNaN : (F32.encode DecodedFloat.nan).isNaN := by
  simp [F32.encode]
  native_decide

/-- Encoding .inf s produces an Inf bit pattern with the same sign. -/
theorem encode_inf_isInf (s : Bool) :
    (F32.encode (.inf s)).isInf ∧ (F32.encode (.inf s)).sign = s := by
    simp [F32.encode]
    simp [pack]
    cases s
    · simp; native_decide
    · simp; native_decide

/-- Encoding a zero DecodedFloat produces a zero bit pattern. -/
theorem encode_zero_isZero (s : Bool) (e : Int) :
    (F32.encode (.finite s e 0)).isZero := by
    simp [F32.encode]
    simp [pack]
    cases s
    · simp; decide
    · decide

end F32
