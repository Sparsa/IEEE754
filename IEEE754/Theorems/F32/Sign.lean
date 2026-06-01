/-
  IEEE754.Theorems.Sign
  =====================
  §11E  Sign rules (IEEE 754-2019 §6.3)
  §11F  Commutativity (fadd_comm, fmul_comm)
  §11G  Ordering (flt_*, feq_*)
  §11H  Cancellation and additive identity
  §11I  FMA: true single rounding
  §11J  Square root
-/

import IEEE754.Theorems.F32.Inf

open BitVec

namespace F32

-- ── E. Sign rules (IEEE 754-2019 §6.3) ───────────────────────────────────────

/-- The product sign is XOR of operand signs (when result is not NaN). -/

--#set_option maxHeartbeats 2000000
theorem fmul_sign_xor {rm : RoundMode} {a b : F32}
    (hna : ¬a.isNaN) (hnb : ¬b.isNaN)
    (hza : ¬a.isZero) (hzb : ¬b.isZero)
    (hr  : ¬(F32.fmul rm a b).isNaN) :
    (F32.fmul rm a b).sign = (a.sign != b.sign) := by
    simp [fmul]
    simp [fmulEx]
    simp [mulExact]
    split
    ·{
      rename_i aheq
      simp [decode] at aheq
      simp_all
      by_cases h_inf : a.isInf <;>
      ·{
        simp [h_inf] at aheq
      }
    }
    ·{
      rename_i bheq aheq
      simp_all
      simp [decode] at bheq
      simp [hnb] at bheq
      by_cases h_inf : b.isInf
      ·{
        simp [h_inf] at bheq
      }
      ·{
        simp [h_inf] at bheq
        simp [hzb] at bheq
      }
    }
    ·{
      have fmul_nan : (fmul rm a b).isNaN := by
        simp [fmul]
        simp [fmulEx]
        simp [mulExact]
        simp_all
        simp [roundTo]
        simp [encode]
        simp [isNaN]
        simp [qNaN]
        simp [pack]
        simp [expIsMax]
        simp [expRaw]
        simp [mantIsZero]
        simp [mantissa]
      contradiction
    }
    ·{
      have fmul_nan : (fmul rm a b).isNaN := by
        simp [fmul]
        simp [fmulEx]
        simp [mulExact]
        simp_all
        simp [roundTo]
        simp [encode]
        simp [isNaN]
        simp [qNaN]
        simp [pack]
        simp [expIsMax]
        simp [expRaw]
        simp [mantIsZero]
        simp [mantissa]
      contradiction
    }
    ·{
      simp [roundTo]
      simp [encode]
      simp [pack]
      split
      ·{
        simp_all
        rename_i heq_a heq_b ab
        simp [decode] at heq_b heq_a
        simp [hnb] at heq_b heq_a
        rw [← ab] at heq_b heq_a
        simp [hzb] at heq_b heq_a
        simp [sign]
        simp [sign] at heq_b heq_a
        by_cases binf: b.isInf <;> by_cases ainf : a.isInf <;>
        ·{
          simp_all
        }
      }
      ·{
        simp_all
        rename_i heq_a heq_b ab
        simp [decode] at heq_b heq_a
        simp [hnb] at heq_b heq_a
        simp [hzb] at heq_b heq_a
        simp [sign]
        simp [sign] at heq_b heq_a
        by_cases binf: b.isInf <;> by_cases ainf : a.isInf <;>
        ·{
          simp_all
        }
      }
    }
    ·{
      simp [roundTo]
      simp [encode]
      simp [pack]
      split
      ·{
        simp_all
        rename_i heq_a heq_b ab
        simp [decode] at heq_b heq_a
        simp [hnb] at heq_b heq_a
        rw [← ab] at heq_b heq_a
        simp [hzb] at heq_b heq_a
        simp [sign]
        simp [sign] at heq_b heq_a
        by_cases binf: b.isInf <;> by_cases ainf : a.isInf <;>
        ·{
          simp_all
        }
      }
      ·{
        simp_all
        rename_i heq_a heq_b ab
        simp [decode] at heq_b heq_a
        simp [hnb] at heq_b heq_a
        simp [hzb] at heq_b heq_a
        simp [sign]
        simp [sign] at heq_b heq_a
        by_cases binf: b.isInf <;> by_cases ainf : a.isInf <;>
        ·{
          simp_all
        }
      }
    }
    ·{
      simp [roundTo]
      simp [encode]
      simp [pack]
      split
      ·{
        simp_all
        rename_i heq_a heq_b ab
        simp [decode] at heq_b heq_a
        simp [hnb] at heq_b heq_a
        rw [← ab] at heq_b heq_a
        simp [hzb] at heq_b heq_a
        simp [sign]
        simp [sign] at heq_b heq_a
        by_cases binf: b.isInf <;> by_cases ainf : a.isInf <;>
        ·{
          simp_all
        }
      }
      ·{
        simp_all
        rename_i heq_a heq_b ab
        simp [decode] at heq_b heq_a
        simp [hnb] at heq_b heq_a
        simp [hzb] at heq_b heq_a
        simp [sign]
        simp [sign] at heq_b heq_a
        by_cases binf: b.isInf <;> by_cases ainf : a.isInf <;>
        ·{
          simp_all
        }
      }
    }
    ·{
      simp [roundTo]
      simp [encode]
      simp [pack]
      split
      ·{
        simp_all
        rename_i heq_a heq_b ab
        simp [decode] at heq_b heq_a
        simp [hnb] at heq_b heq_a
        simp [hzb] at heq_b heq_a
        simp [sign]
        simp [sign] at heq_b heq_a
        by_cases binf: b.isInf <;> by_cases ainf : a.isInf <;>
        ·{
          grind
        }
      }
      ·{

        rename_i heq_a heq_b df ss lf
        simp [decode] at heq_b heq_a
        simp [hnb] at heq_b heq_a
        simp [hzb] at heq_b heq_a
        simp [sign]
        simp [sign] at heq_b heq_a
        by_cases binf: b.isInf <;> by_cases ainf : a.isInf
        ·{
          grind
        }
        ·{
          grind
        }
        ·{
          grind
        }
        ·{


          simp [binf] at heq_b
          simp [ainf] at heq_a
          simp [hza] at heq_a
          simp [hna] at heq_a
          rename_i dfa dfb dfas dfae dfasig dfbs dfbe dfbsig
          by_cases signab : (dfas = dfbs)
          ·{
            simp [signab] at lf
            split at lf
            ·{ simp_all }
            ·{ simp_all }
            ·{ simp_all }
            ·{
              rename_i d s e sig x sp
              have hge : 2^(sig.log2) ≤ sig := by apply Nat.log2_self_le; omega
              have hlt : sig < 2^(sig.log2+1) := Nat.lt_log2_self
              have flb : findLeadingBit sig (sig.log2 + 1) = sig.log2 := findLeadingBit_range hge hlt
              simp [flb] at lf
              cases dfas <;> cases dfbs <;> simp_all
            }
            ·{ simp_all }
            ·{ simp_all }
          }
          ·{
            split at lf
            ·{ simp_all }
            ·{ simp_all }
            ·{ simp_all }
            ·{
              rename_i d s e sig x sp
              have hge : 2^(sig.log2) ≤ sig := by apply Nat.log2_self_le; omega
              have hlt : sig < 2^(sig.log2+1) := Nat.lt_log2_self
              have flb : findLeadingBit sig (sig.log2 + 1) = sig.log2 := findLeadingBit_range hge hlt
              simp [flb] at lf
              cases dfas <;> cases dfbs <;> simp_all
            }
            ·{ simp_all }
            ·{ simp_all }
          }

        }
      }
    }
-- ── Sign-preservation helpers (shared by fdiv_sign_xor and fsqrt_nonneg) ────────

private theorem pack_sign_false (e : BitVec 8) (m : BitVec 23) :
    (F32.pack false e m).sign = false := by simp [pack, sign]

private theorem pack_sign_true (e : BitVec 8) (m : BitVec 23) :
    (F32.pack true e m).sign = true := by simp [pack, sign]

private theorem pack_sign (s : Bool) (e : BitVec 8) (m : BitVec 23) :
    (F32.pack s e m).sign = s := by
  cases s
  · exact pack_sign_false e m
  · exact pack_sign_true e m

private theorem encode_false_sign (d : DecodedFloat) (hs : d.dfSign = false) :
    (F32.encode d).sign = false := by
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

private theorem encode_true_sign (d : DecodedFloat) (hs : d.dfSign = true) :
    (F32.encode d).sign = true := by
  match d with
  | .nan              => simp [DecodedFloat.dfSign] at hs
  | .inf false        => simp [DecodedFloat.dfSign] at hs
  | .inf true         => simp [encode]; exact pack_sign_true _ _
  | .finite false _ _ => simp [DecodedFloat.dfSign] at hs
  | .finite true _ 0  => simp [encode]; exact pack_sign_true _ _
  | .finite true e (_ + 1) =>
    simp only [encode]
    split
    · exact pack_sign_true _ _
    · split
      · simp [negInf, pack, sign]
      · exact pack_sign_true _ _

/-- The quotient sign is XOR of operand signs (when result is not NaN). -/
theorem fdiv_sign_xor {rm : RoundMode} {a b : F32}
    (hna : ¬a.isNaN) (hnb : ¬b.isNaN)
    (hza : ¬a.isZero) (hzb : ¬b.isZero)
    (hr  : ¬(F32.fdiv rm a b).isNaN) :
    (F32.fdiv rm a b).sign = (a.sign != b.sign) := by
    simp [fdiv]; simp [fdivEx]; simp [divExact]; simp [divExactWith]
    split
    ·{
      simp [roundTo]; simp [encode]; simp_all; rename_i heq
      simp [sign]; simp [decode] at heq; simp [hna] at heq; simp [hza] at heq
      simp [qNaN]; simp [pack]
      by_cases hinf: a.isInf <;>
      ·{
        simp [hinf] at heq
      }
    }
    ·{
      simp_all
      simp [roundTo]
      simp [encode]
      simp [qNaN]
      simp [sign]
      simp [pack]
      rename_i heq_b heq_a
      simp [decode] at heq_b
      simp [hnb] at heq_b
      simp [hzb] at heq_b
      by_cases hinfb : b.isInf <;>
      ·{
        simp [hinfb] at heq_b
      }
    }
    ·{
      rename_i heq_a heq_b
      have hcontra: (fdiv rm a b).isNaN = true := by
        simp[fdiv]; simp [fdivEx]; simp [divExact]; simp [divExactWith]; simp [heq_a,heq_b]; simp [roundTo]; simp [encode]; native_decide
      contradiction
    }
    ·{
      rename_i heq_a heq_b
      have hcontra: (fdiv rm a b).isNaN = true := by
        simp[fdiv]; simp [fdivEx]; simp [divExact]; simp [divExactWith]; simp [heq_a,heq_b]; simp [roundTo]; simp [encode]; native_decide
      contradiction
    }
    ·{
      rename_i heq_a heq_b
      rename_i exp sig
      rename_i aa bb sa sb
      simp [decode] at heq_a
      simp [decode] at heq_b
      simp [hna] at heq_a
      simp [hnb] at heq_b
      simp [hza] at heq_a
      simp [hzb] at heq_b
      by_cases hinfa : a.isInf <;> by_cases hinfb : b.isInf
      ·{
        simp [hinfa] at heq_a
        simp [hinfb] at heq_b
      }
      ·{
        simp [hinfa] at heq_a
        simp [hinfb] at heq_b
        obtain ⟨sig, _, _ ⟩ := heq_b
        by_cases sigab : (sa ≠ sb)
        ·{
          simp [roundTo]
          simp [encode]
          rw [heq_a,sig]
          simp [sign]
          simp [pack]
          simp [sigab]
        }
        ·{
          simp [roundTo]
          simp [encode]
          rw [heq_a,sig]
          simp [sign]
          simp [pack]
          simp at sigab
          simp_all
        }
      }
      ·{
        simp [hinfa] at heq_a
      }
      ·{
        simp [hinfa] at heq_a
      }
    }
    ·{
      rename_i heq_a heq_b
      rename_i exp sig
      rename_i aa bb sa sb
      simp [decode] at heq_a
      simp [decode] at heq_b
      simp [hna] at heq_a
      simp [hnb] at heq_b
      simp [hza] at heq_a
      simp [hzb] at heq_b
      by_cases hinfa : a.isInf <;> by_cases hinfb : b.isInf
      ·{
        simp [hinfa] at heq_a
      }
      ·{
        simp [hinfa] at heq_a
      }
      ·{
        simp [hinfa] at heq_a
        simp [hinfb] at heq_b
        obtain ⟨asign,_,_⟩ := heq_a
        simp [roundTo]
        simp [encode]
        simp [heq_b, asign]
        simp [pack, sign]
        by_cases signeq : sa = sig <;>
        ·{
          simp [signeq]
        }
      }
      ·{
        simp [hinfa] at heq_a
        simp [hinfb] at heq_b
      }
    }
    ·{
      rename_i heq_a heq_b
      rename_i exp x
      rename_i aa bb sa sb
      rename_i dfa dfb
      simp [decode] at heq_a heq_b
      simp [hna] at heq_a
      simp [hnb] at heq_b
      simp [hza] at heq_a
      simp [hzb] at heq_b
      by_cases hinfa : a.isInf <;> by_cases hinfb : b.isInf
      ·{
        simp [hinfa] at heq_a
      }
      ·{
        simp [hinfa] at heq_a
      }
      ·{
        simp [hinfa] at heq_a
        simp [hinfb] at heq_b
      }
      ·{
        simp [hinfa] at heq_a
        simp [hinfb] at heq_b
        obtain ⟨sigaa, _ , _ ⟩ := heq_a
        obtain ⟨sigbb, _ , _ ⟩ := heq_b
        simp [sigaa,sigbb]
        simp [roundTo]
        simp [encode]
        simp [pack]
        simp [sign]
        by_cases signeq : aa = sb <;>
        ·{
          simp [signeq]
        }
      }
    }
    ·{
      rename_i heq_a heq_b
      rename_i exp x
      rename_i aa bb sa sb
      rename_i dfa dfb
      simp [decode] at heq_a heq_b
      simp [hna] at heq_a
      simp [hnb] at heq_b
      simp [hza] at heq_a
      simp [hzb] at heq_b
      by_cases hinfa : a.isInf <;> by_cases hinfb : b.isInf
      ·{
        simp [hinfa] at heq_a
      }
      ·{
        simp [hinfa] at heq_a
      }
      ·{
        simp [hinfa] at heq_a
        simp [hinfb] at heq_b
      }
      ·{
        simp [hinfa] at heq_a
        simp [hinfb] at heq_b
        obtain ⟨sigaa, _ , _ ⟩ := heq_a
        obtain ⟨sigbb, _ , _ ⟩ := heq_b
        simp [sigaa,sigbb]
        simp [roundTo]
        simp [encode]
        simp [pack]
        by_cases signeq : aa = sa
        ·{
          simp [signeq]
          simp [sign]
        }
        ·{
          simp [signeq]
          simp [sign]
          exact signeq
        }
      }
    }
    ·{
      rename_i heq_a heq_b
      rename_i x1 x2 x3
      rename_i sa ea siga
      rename_i sb eb sigb
      rename_i dfa dfb
      simp [decode] at heq_a heq_b
      simp [hna] at heq_a
      simp [hnb] at heq_b
      simp [hza] at heq_a
      simp [hzb] at heq_b
      by_cases hinfa : a.isInf <;> by_cases hinfb : b.isInf
      ·{
        simp [hinfa] at heq_a
      }
      ·{
        simp [hinfa] at heq_a
      }
      ·{
        simp [hinfa] at heq_a
        simp [hinfb] at heq_b
      }
      ·{
        simp [hinfa] at heq_a
        simp [hinfb] at heq_b
        obtain ⟨sigaa, _ , _ ⟩ := heq_a
        obtain ⟨sigbb, _ , _ ⟩ := heq_b
        simp [sigaa,sigbb]
        by_cases signeq : sb = sa
        ·{
          have hbne : (sb != sa) = false := by simp [signeq]
          rw [hbne]
          apply encode_false_sign
          split <;>
          ·{
            apply roundTo_sign_preserved
          }
        }
        ·{
          have hbne : (sb != sa) = true := by cases sa <;> cases sb <;> simp_all
          rw [hbne]
          apply encode_true_sign
          apply roundTo_sign_preserved
        }
      }
    }

/-- When both addends share the same sign, so does a nonzero result. -/
theorem fadd_same_sign {rm : RoundMode} {a b : F32} {s : Bool}
    (hna : ¬a.isNaN) (hnb : ¬b.isNaN)
    (ha : a.sign = s) (hb : b.sign = s)
    (hr  : ¬(F32.fadd rm a b).isNaN)
    (hrz : ¬(F32.fadd rm a b).isZero) :
    (F32.fadd rm a b).sign = s := by
    have ha_dfSign : (F32.decode a).dfSign = s := by
      simp [F32.decode, hna, ha]
      split
      ·{
        simp [DecodedFloat.dfSign]
      }
      ·{
        split <;>
        ·{
          simp [DecodedFloat.dfSign]
        }
      }
    have hb_dfSign : (F32.decode b).dfSign = s := by
      simp [F32.decode, hnb, hb]
      split
      ·{
        simp [DecodedFloat.dfSign]
      }
      ·{
        split <;>
        ·{
          simp [DecodedFloat.dfSign]
        }
      }

    simp [F32.fadd, F32.faddEx, addExact]
    cases hda : F32.decode a
    ·{
      simp [F32.decode, hna] at hda


    }
    · rename_i sa
      cases hdb : F32.decode b
      · simp [F32.decode, hnb] at hdb
      · rename_i sb
        have hsa : sa = s := by simpa [hda] using ha_dfSign
        have hsb : sb = s := by simpa [hdb] using hb_dfSign
        simp [hda, hdb, addExact, roundTo, encode, sign, hsa, hsb]
        split <;> simp
      · rename_i sb eb sigb
        have hsa : sa = s := by simpa [hda] using ha_dfSign
        simp [hda, hdb, addExact, roundTo, encode, sign, hsa]
    · rename_i sa ea siga
      cases hdb : F32.decode b
      · simp [F32.decode, hnb] at hdb
      · rename_i sb
        have hsb : sb = s := by simpa [hdb] using hb_dfSign
        simp [hda, hdb, addExact, roundTo, encode, sign, hsb]
      · rename_i sb eb sigb
        have hsa : sa = s := by simpa [hda] using ha_dfSign
        have hsb : sb = s := by simpa [hdb] using hb_dfSign
        simp [addExact, hda, hdb, hsa, hsb]
        split
        · have hres_zero : (F32.fadd rm a b).isZero := by
            simp [F32.fadd, F32.faddEx, hda, hdb, hsa, hsb, addExact, roundTo, encode, isZero, pack]
          exact absurd hres_zero hrz
        · split
          · simp [roundTo, encode, sign, hsb, pack]
          · split
            · simp [roundTo, encode, sign, hsa, pack]
            · split
              · have hres_zero : (F32.fadd rm a b).isZero := by
                  simp [F32.fadd, F32.faddEx, hda, hdb, hsa, hsb, addExact, roundTo, encode, isZero, pack]
                exact absurd hres_zero hrz
              · simp [roundTo, encode, sign, hsa, hsb, pack]

-- ── F. Commutativity ──────────────────────────────────────────────────────────

/-- fadd is commutative (bit-exact result). -/
theorem fadd_comm (rm : RoundMode) (a b : F32) :
    F32.fadd rm a b = F32.fadd rm b a := by
    simp [fadd]; simp [faddEx]
    rw [addExact_comm]

/-- fmul is commutative (bit-exact result). -/
theorem fmul_comm (rm : RoundMode) (a b : F32) :
    F32.fmul rm a b = F32.fmul rm b a := by
    simp [fmul]; simp [fmulEx]
    rw [mulExact_comm]

-- ── G. Ordering (IEEE 754-2019 §5.10, §5.11) ─────────────────────────────────

/-- flt is irreflexive. -/
theorem flt_irrefl (a : F32) : F32.flt a a = false := by
  simp [flt]
  split <;> simp_all
  split
  · simp_all
  · simp_all
  · intro hh; rfl
  · simp_all

/-- flt is asymmetric. -/
theorem flt_asymm {a b : F32} (h : F32.flt a b) : F32.flt b a = false := by
  simp [flt] at *
  split at h <;> split <;> simp_all <;>
  split
  · simp_all
  · rfl
  · simp_all; exact Nat.le_of_lt h.2
  · simp_all; exact Nat.le_of_lt h.2

/-- flt is transitive. -/
theorem flt_trans {a b c : F32}
    (h1 : F32.flt a b) (h2 : F32.flt b c) : F32.flt a c := by
    simp [flt]
    simp [flt ] at h1
    simp [flt] at h2
    obtain ⟨ h1l,h1m,h1r ⟩ := h1
    obtain ⟨ h2l,h2m,h2r ⟩ := h2
    constructor
    ·{
      obtain ⟨hll₁,_⟩ := h1l
      obtain ⟨_,hll₂⟩ := h2l
      apply And.intro hll₁ hll₂
    }
    ·{
      constructor
      ·{
        grind
      }
      ·{
        grind
      }
    }

/-- NaN comparisons always return false (IEEE 754 §5.11 "unordered"). -/
theorem flt_nan_l (a b : F32) (h : a.isNaN) : F32.flt a b = false := by
  simp [flt]; split <;> simp_all

theorem flt_nan_r (a b : F32) (h : b.isNaN) : F32.flt a b = false := by
  simp [flt]; split <;> simp_all

theorem feq_nan_l (a b : F32) (h : a.isNaN) : F32.feq a b = false := by
  simp [feq]; simp_all

theorem feq_nan_r (a b : F32) (h : b.isNaN) : F32.feq a b = false := by
  simp [feq]; simp_all

-- ── H. Cancellation and additive identity ─────────────────────────────────────

private theorem negate_mantissa (f : F32) : f.negate.mantissa = f.mantissa := by
  simp only [negate, mantissa, BitVec.truncate_eq_setWidth, BitVec.setWidth_xor]
  have : ((1 <<< 31 : BitVec 32)).setWidth 23 = 0 := by decide
  simp [this]

private theorem negate_expRaw' (f : F32) : f.negate.expRaw = f.expRaw := by
  simp only [negate, expRaw, BitVec.truncate_eq_setWidth,
             BitVec.ushiftRight_xor_distrib, BitVec.setWidth_xor]
  have : (((1 <<< 31 : BitVec 32)) >>> 23).setWidth 8 = 0 := by decide
  simp [this]

private theorem negate_isNaN' (f : F32) : f.negate.isNaN = f.isNaN := by
  simp [isNaN, expIsMax, mantIsZero, negate_expRaw', negate_mantissa]

private theorem negate_isInf' (f : F32) : f.negate.isInf = f.isInf := by
  simp [isInf, expIsMax, mantIsZero, negate_expRaw', negate_mantissa]

private theorem negate_isZero' (f : F32) : f.negate.isZero = f.isZero := by
  simp [isZero, expIsZero, mantIsZero, negate_expRaw', negate_mantissa]

private theorem negate_isNormal' (f : F32) : f.negate.isNormal = f.isNormal := by
  simp [isNormal, expIsZero, expIsMax, negate_expRaw']

private theorem negate_significand' (f : F32) : f.negate.significand = f.significand := by
  simp [significand, negate_isNormal', negate_mantissa]

private theorem addExact_opp_cancel (rm : RoundMode) (s : Bool) (e : Int) (sig : Nat) :
    ∃ s', (addExact rm (.finite s e sig) (.finite (!s) e sig)).1 = .finite s' 0 0 := by
  by_cases h0 : sig = 0
  ·{
    subst h0
    exact ⟨s && !s || (s || !s) && (rm == .RDN), by simp [addExact]⟩
  }
  ·{
    refine ⟨rm == .RDN, ?_⟩
    have hb : (sig == 0) = false := by simpa using h0
    have hne : (s == !s) = false := by cases s <;> rfl
    have hdiff : (e - e : Int).toNat = 0 := by omega
    simp only [addExact, hb,  Bool.and_false ]
    simp
  }
/-- x − x = ±0 for any finite non-NaN (IEEE 754 cancellation). -/
theorem fsub_self_isZero (rm : RoundMode) (a : F32) (h : ¬a.isNaN) (hi : ¬a.isInf) :
    (F32.fsub rm a a).isZero := by
  have hNaN : a.isNaN = false := by simpa using h
  have hInf : a.isInf = false := by simpa using hi
  have hn_isNaN : a.negate.isNaN = false := (negate_isNaN' a).trans hNaN
  have hn_isInf : a.negate.isInf = false := (negate_isInf' a).trans hInf
  cases hZ : a.isZero
  · obtain ⟨s₀, hadd⟩ := addExact_opp_cancel rm a.sign
        ((if a.isNormal then (a.expRaw.toNat : Int) else 1) - 127 - 23) a.significand.toNat
    have hdec : F32.decode a = .finite a.sign
        ((if a.isNormal then (a.expRaw.toNat : Int) else 1) - 127 - 23) a.significand.toNat := by
      simp [decode, hNaN, hInf, hZ]
    have hdecn : F32.decode a.negate = .finite (!a.sign)
        ((if a.isNormal then (a.expRaw.toNat : Int) else 1) - 127 - 23) a.significand.toNat := by
      simp [decode, hn_isNaN, hn_isInf, (negate_isZero' a).trans hZ,
            negate_sign, negate_isNormal', negate_expRaw', negate_significand']
    have hfadd : (F32.faddEx rm a a.negate).1 = F32.encode (.finite s₀ 0 0) := by
      simp only [faddEx, hdec, hdecn, hadd, roundTo]
    simp only [fsub, hfadd]
    exact encode_zero_isZero s₀ 0
  · obtain ⟨s₀, hadd⟩ := addExact_opp_cancel rm a.sign 0 0
    have hdec : F32.decode a = .finite a.sign 0 0 := by simp [decode, hNaN, hInf, hZ]
    have hdecn : F32.decode a.negate = .finite (!a.sign) 0 0 := by
      simp [decode, hn_isNaN, hn_isInf, (negate_isZero' a).trans hZ, negate_sign]
    have hfadd : (F32.faddEx rm a a.negate).1 = F32.encode (.finite s₀ 0 0) := by
      simp only [faddEx, hdec, hdecn, hadd, roundTo]
    simp only [fsub, hfadd]
    exact encode_zero_isZero s₀ 0

/-- +0 is a right additive identity under IEEE equality (for non-NaN a). -/
theorem fadd_posZero_r (rm : RoundMode) (a : F32) (h : ¬a.isNaN) :
    F32.feq (F32.fadd rm a F32.posZero) a := by
    cases ha: classify a
    · -- zero
      have haz : a.isZero = true := (biject_class_zero _).mpr ha
      have hnan : a.isNaN = false := isNaN_false_of_isZero a haz
      have hinf : a.isInf = false := isInf_false_of_isZero a  haz
      have hnanpos : posZero.isNaN = false := by native_decide
      have hzeropos : posZero.isZero = true := by native_decide
      have hsignpos : posZero.sign = false := by native_decide
      simp [feq, fadd, faddEx, addExact, decode, hnan, haz, hinf, hnanpos, hzeropos, hsignpos, roundTo, encode, isZero, pack]
    · -- subnormal
      have hsub : a.isSubnormal = true := (biject_class_subnormal _).mpr ha
      have hnan : a.isNaN = false := isNaN_false_of_isSubnormal a hsub
      have hzero : a.isZero = false := isZero_false_of_isSubnormal a hsub
      have hinf : a.isInf = false := isInf_false_of_isSubnormal a hsub
      have hnorm : a.isNormal = false := isNormal_false_of_isSubnormal a hsub
      have hnanpos : posZero.isNaN = false := by native_decide
      have hzeropos : posZero.isZero = true := by native_decide
      have hsignpos : posZero.sign = false := by native_decide
      have h_fadd_eq_a : F32.fadd rm a posZero = a := by
        simp [fadd, faddEx, addExact, decode, hnan, hzero, hinf, hnanpos, hzeropos, hsignpos, roundTo, encode]
        simp_all
        simpa using encode_decode_subnormal hsub
      simp [feq, h_fadd_eq_a, h]
    · -- normal
      have hnorm : a.isNormal = true := (biject_class_normal _).mpr ha
      have hnan : a.isNaN = false := isNaN_false_of_isNormal a hnorm
      have hzero : a.isZero = false := isZero_false_of_isNormal a hnorm
      have hinf : a.isInf = false := isInf_false_of_isNormal a hnorm
      have hnanpos : posZero.isNaN = false := by native_decide
      have hzeropos : posZero.isZero = true := by native_decide
      have hsignpos : posZero.sign = false := by native_decide
      have h_fadd_eq_a : F32.fadd rm a posZero = a := by
        simp [fadd, faddEx, addExact, decode, hnan, hzero, hinf, hnorm, hnanpos, hzeropos, hsignpos, roundTo, encode]
        simpa using encode_decode_normal hnorm
      simp [feq, h_fadd_eq_a, h]
    · -- inf
      have hinf : a.isInf = true := (biject_class_inf _).mpr ha
      have hnan : a.isNaN = false := isNaN_false_of_isInf a hinf
      have hzero : a.isZero = false := isZero_false_of_isInf a hinf
      have hnanpos : posZero.isNaN = false := by native_decide
      have hzeropos : posZero.isZero = true := by native_decide
      have hsignpos : posZero.sign = false := by native_decide
      have h_fadd_eq_a : F32.fadd rm a posZero = a := by
        simp [fadd, faddEx, addExact, decode, hnan, hinf, hzero, hnanpos, hzeropos, hsignpos, roundTo, encode]
        have h_emax : a.expIsMax := by
          have := hinf; simp [isInf] at this; exact this.1
        have h_mzero : a.mantIsZero := by
          have := hinf; simp [isInf] at this; exact this.2
        have hexp : a.expRaw = expMax 8 23 := by
          simpa [expIsMax] using h_emax
        have hman : a.mantissa = 0 := by
          simpa [mantIsZero] using h_mzero
        simp [hexp, hman, F32.pack_sign_expRaw_mantissa]
      simp [feq, h_fadd_eq_a, h]
    · -- nan → impossible
      exfalso; exact h ((biject_class_nan _).mpr ha)

-- ── I. FMA: true single rounding ──────────────────────────────────────────────

theorem fma_is_single_rounded (rm : RoundMode) (a b c : F32) :
    F32.fma rm a b c = (F32.fmaEx rm a b c).1 := rfl

theorem fmaEx_flags_eq (rm : RoundMode) (a b c : F32) :
    (F32.fmaEx rm a b c).2 =
    (fmaExact rm (F32.decode a) (F32.decode b) (F32.decode c)).2.merge
    (roundTo f32Fmt rm (fmaExact rm (F32.decode a) (F32.decode b) (F32.decode c)).1).2 := by
  simp [F32.fmaEx]

theorem fma_ne_mul_then_add :
    ∃ (a b c : F32),
      F32.fma .RNE a b c ≠ F32.fadd .RNE (F32.fmul .RNE a b) c :=
  ⟨0x45800800, 0x45800800, 0xCB801000, by native_decide⟩

-- ── J. Square root ────────────────────────────────────────────────────────────

theorem fsqrt_is_single_rounded (rm : RoundMode) (a : F32) :
    F32.fsqrt rm a = (F32.fsqrtEx rm a).1 := rfl

/-- √(NaN) = NaN (NaN propagation §6.2). -/
theorem fsqrt_nan (rm : RoundMode) (a : F32) (h : a.isNaN) :
    (F32.fsqrt rm a).isNaN := by
    simp [F32.fsqrt]; simp [fsqrtEx]; simp [decode]
    rw [h]; simp; simp [sqrtExact]; simp [roundTo]; simp [encode]; decide

theorem bit_vec_mod_power (a: BitVec n) : a.toNat % 2^n = 0 → a.toNat = 0 := by
  intro h
  have h0 : a.toNat < 2^n := isLt a
  have hzero : a.toNat = 0 := by rwa [Nat.mod_eq_of_lt h0] at h
  exact hzero

/-- √(negative finite) raises invalidOp and returns NaN (§7.2). -/
theorem fsqrt_neg_isNaN (rm : RoundMode) (a : F32)
    (hs : a.sign = true) (hf : a.isFinite) (hz : ¬a.isZero) :
    (F32.fsqrt rm a).isNaN ∧ (F32.fsqrtEx rm a).2.invalidOp := by
  have hZ   : a.isZero  = false := by simpa using hz
  have hNaN : a.isNaN   = false := isNaN_false_of_isFinite a hf
  have hInf : a.isInf   = false := isInf_false_of_isFinite a hf
  have hdec : F32.decode a = .finite true
      ((if a.isNormal then (a.expRaw.toNat : Int) else 1) - 127 - 23)
      a.significand.toNat := by
    simp [F32.decode, hNaN, hInf, hZ, hs]
  have hsig : a.significand.toNat ≠ 0 := by
    rcases finite_classify a hNaN hInf with h | h | h
    · simp [hZ] at h
    · have hExpZ    : a.expIsZero  = true  := by simp [isSubnormal] at h; exact h.1
      have hMantNZ  : a.mantIsZero = false := by simp [isSubnormal] at h; exact h.2
      have hNotNorm : a.isNormal   = false := by simp [isNormal, hExpZ]
      simp [F32.mantIsZero] at hMantNZ
      intro h0
      simp only [F32.significand, hNotNorm] at h0
      apply hMantNZ
      apply BitVec.eq_of_toNat_eq
      have hext : (a.mantissa.zeroExtend 24).toNat = a.mantissa.toNat :=
        BitVec.toNat_setWidth_of_le (by omega)
      simp at h0
      have pow_24 : 2^24 = 16777216 := by decide
      rw [← pow_24] at h0
      have a_man_zero : a.mantissa.toNat = 0 := by
        rw [← hext] at h0
        exact bit_vec_mod_power (zeroExtend 24 a.mantissa) h0
      simp; exact a_man_zero
    · have hNorm : a.isNormal = true := h
      intro h0
      simp only [F32.significand, hNorm, if_true] at h0
      have h_lbit : Nat.testBit ((1 : BitVec 24) <<< 23).toNat 23 = true := by decide
      have hbit : Nat.testBit
          (((1 : BitVec 24) <<< 23).toNat ||| (a.mantissa.zeroExtend 24).toNat) 23 = true := by
        rw [Nat.testBit_or, h_lbit]; simp
      have hge : ((1 : BitVec 24) <<< 23).toNat ||| (a.mantissa.zeroExtend 24).toNat ≥ 2^23 :=
        Nat.ge_two_pow_of_testBit hbit
      rw [BitVec.toNat_or] at h0
      grind
  have hsqrt : sqrtExact (F32.decode a) = (.nan, ExcFlags.mkInvalidOp) := by
    rw [hdec]
    match h0 : a.significand.toNat with
    | 0     => exact absurd h0 hsig
    | _ + 1 => simp [sqrtExact]
  constructor
  · simp only [F32.fsqrt, F32.fsqrtEx, hsqrt, roundTo]; exact encode_nan_isNaN
  · simp only [F32.fsqrtEx, hsqrt, roundTo]; decide

/-- √(-∞) raises invalidOp and returns NaN (§7.2). -/
theorem fsqrt_negInf_isNaN (rm : RoundMode) :
    (F32.fsqrt rm F32.negInf).isNaN ∧ (F32.fsqrtEx rm F32.negInf).2.invalidOp := by
    have neg_inf_is_not_nan : negInf.isNaN = false := by native_decide
    have neg_inf_is_inf : negInf.isInf = true := by native_decide
    have neg_inf_not_zero : negInf.isZero = false := by native_decide
    have neg_inf_sign_true : negInf.sign = true := by native_decide
    constructor
    · simp [fsqrt]; simp [fsqrtEx]; simp [decode]
      rw [neg_inf_is_not_nan, neg_inf_is_inf, neg_inf_not_zero, neg_inf_sign_true]
      simp; simp [sqrtExact]; simp [roundTo]; simp [encode]; decide
    · simp [fsqrtEx]; simp [decode]
      rw [neg_inf_is_not_nan, neg_inf_is_inf, neg_inf_not_zero, neg_inf_sign_true]
      simp; simp [sqrtExact]; simp [roundTo]; native_decide

/-- √(+∞) = +∞ (no exception). -/
theorem fsqrt_posInf (rm : RoundMode) :
    F32.fsqrt rm F32.posInf = F32.posInf := by
    simp [fsqrt]; simp [fsqrtEx]; simp [decode]
    have pos_inf_not_nan : posInf.isNaN = false := by native_decide
    have pos_inf_inf : posInf.isInf = true := by native_decide
    have pos_inf_nz : posInf.isZero = false := by native_decide
    have pos_inf_sign : posInf.sign = false := by native_decide
    rw [pos_inf_not_nan, pos_inf_inf, pos_inf_nz]; simp
    unfold sqrtExact; simp [pos_inf_sign]; simp [roundTo]; simp [encode]; simp [pack]; decide

/-- √(+0) = +0 (IEEE 754 §6.3). -/
theorem fsqrt_posZero (rm : RoundMode) :
    F32.fsqrt rm F32.posZero = F32.posZero := by
    have pos_zero_not_nan : posZero.isNaN = false := by native_decide
    have pos_zero_is_zero : posZero.isZero = true := by native_decide
    have pos_zero_not_inf : posZero.isInf = false := by native_decide
    have pos_zero_sign_false : posZero.sign = false := by native_decide
    simp [fsqrt]; simp [fsqrtEx]; simp [decode]
    rw [pos_zero_not_nan, pos_zero_is_zero, pos_zero_not_inf, pos_zero_sign_false]
    simp; simp [sqrtExact]; simp [roundTo]; simp [encode]; decide

/-- √(−0) = −0 (IEEE 754 §6.3: sign of zero is preserved). -/
theorem fsqrt_negZero (rm : RoundMode) :
    F32.fsqrt rm F32.negZero = F32.negZero := by
    have neg_zero_not_nan : negZero.isNaN = false := by native_decide
    have neg_zero_is_zero : negZero.isZero = true := by native_decide
    have neg_zero_not_inf : negZero.isInf = false := by native_decide
    have neg_zero_sign_true : negZero.sign = true := by native_decide
    simp [fsqrt]; simp [fsqrtEx]; simp [decode]
    rw [neg_zero_not_nan, neg_zero_is_zero, neg_zero_not_inf, neg_zero_sign_true]
    simp; simp [sqrtExact]; simp [roundTo]; simp [encode]; decide

private theorem sqrtExact_false_dfSign (e : Int) (sig : Nat) :
    (sqrtExact (.finite false e sig)).1.dfSign = false := by
  match sig with
  | 0     => simp [sqrtExact, DecodedFloat.dfSign]
  | _ + 1 => simp [sqrtExact, DecodedFloat.dfSign]

/-- The result of fsqrt is always non-negative when it is not NaN. -/
theorem fsqrt_nonneg (rm : RoundMode) (a : F32) (h : ¬(F32.fsqrt rm a).isNaN) (anNeg :
a.sign = false) :
    (F32.fsqrt rm a).sign = false := by
  have hnan : a.isNaN = false := by
    by_contra hnn
    push_neg at hnn
    simp at h
    simp [fsqrt] at h; simp [fsqrtEx] at h; simp [sqrtExact] at h
    have adnan: a.decode = DecodedFloat.nan := by simp [decode, hnn]
    simp [adnan] at h; simp [roundTo] at h; simp [encode] at h
    simp [qNaN] at h; simp [pack] at h; simp [isNaN] at h
    simp [expIsMax, mantIsZero] at h; simp [expRaw] at h; simp [mantissa] at h
  simp only [F32.fsqrt, fsqrtEx]
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
    (roundTo_false_dfSign f32Fmt rm (sqrtExact (decode a)).1 sqrt_sign)

theorem fsqrtEx_flags_eq (rm : RoundMode) (a : F32) :
    (F32.fsqrtEx rm a).2 =
    (sqrtExact (F32.decode a)).2.merge
    (roundTo f32Fmt rm (sqrtExact (F32.decode a)).1).2 := by
  simp [F32.fsqrtEx]

end F32
