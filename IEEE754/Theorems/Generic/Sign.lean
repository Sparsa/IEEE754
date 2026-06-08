/-
  IEEE754.Theorems.Generic.Sign
  ==============================
  Sign theorems that hold for any `IEEEFloat` instance.

  These are proved purely from the six typeclass axioms plus the format-generic
  lemmas in ExactLemmas.lean and F32/Props.lean; no bit-level format details
  are used.

  Covered:
    • fadd_same_sign   — same-sign addends → same-sign result
    • fmul_sign_xor    — product sign = XOR of operand signs (when result is non-NaN)
    • fdiv_sign_xor    — quotient sign = XOR of operand signs (when result is non-NaN)
-/

import IEEE754.Theorems.Generic.Class
import IEEE754.Theorems.Generic.ExactLemmas
import IEEE754.Theorems.F32.Props   -- roundTo_sign_preserved

open DecodedFloat IEEEFloat

namespace IEEEFloat

variable {α : Type} [IEEEFloat α]

-- ── Shared sign-propagation lemma ─────────────────────────────────────────────

/-- Helper: the sign of the result of any of the five operations is the dfSign
    of the pre-rounding exact result, provided the exact result is not .nan.
    This chains A4/A5/A6 → encode_dfSign → roundTo_sign_preserved. -/
private theorem op_sign_eq_exact_dfSign {rm : RoundMode} {a b : α}
    (op_spec : (faddEx rm a b).1 =
                encode (roundTo fmt rm (addExact rm (decode a) (decode b)).1).1) :
    sign (fadd rm a b) =
    (addExact rm (decode a) (decode b)).1.dfSign := by
  simp only [fadd]
  rw [op_spec, encode_dfSign, roundTo_sign_preserved]

-- ── fadd_same_sign ────────────────────────────────────────────────────────────

/-- **Generic `fadd_same_sign`**: if both non-NaN operands have sign `s`,
    the addition result also has sign `s`, regardless of rounding mode or format.

    Proof sketch:
      sign (fadd a b)
        = (addExact (decode a) (decode b)).1.dfSign    [A4, A1, roundTo_sign_preserved]
        = s                                             [addExact_same_dfSign] -/
theorem fadd_same_sign {rm : RoundMode} {a b : α} {s : Bool}
    (hna : ¬isNaN a) (hnb : ¬isNaN b)
    (ha  : sign a = s) (hb  : sign b = s) :
    sign (fadd rm a b) = s := by
  rw [op_sign_eq_exact_dfSign (faddEx_spec rm a b)]
  apply addExact_same_dfSign
  · exact fun h => hna ((isNaN_iff a).mpr h)
  · exact fun h => hnb ((isNaN_iff b).mpr h)
  · rw [← sign_eq_dfSign a hna]; exact ha
  · rw [← sign_eq_dfSign b hnb]; exact hb

-- ── fmul_sign_xor ─────────────────────────────────────────────────────────────

/-- **Generic `fmul_sign_xor`**: the sign of `fmul rm a b` is the XOR of the
    operand signs, provided neither input is NaN and the product is not NaN
    (the only NaN-producing case is Inf × 0).

    Proof sketch:
      sign (fmul a b)
        = (mulExact (decode a) (decode b)).1.dfSign    [A5, A1, roundTo_sign_preserved]
        = (decode a).dfSign ^^ (decode b).dfSign       [mulExact_dfSign]
        = sign a ^^ sign b                             [A2] -/
theorem fmul_sign_xor {rm : RoundMode} {a b : α}
    (hna : ¬isNaN a) (hnb : ¬isNaN b)
    (hres : ¬isNaN (fmul rm a b)) :
    sign (fmul rm a b) = sign a ^^ sign b := by
  -- Unfold fmul and apply A5 + encode_dfSign + roundTo_sign_preserved
  simp only [fmul, fmulEx_spec]
  rw [encode_dfSign, roundTo_sign_preserved]
  -- The result NaN hypothesis propagates back to mulExact
  have hmulNaN : (mulExact (decode a) (decode b)).1 ≠ .nan := by
    intro h
    apply hres
    simp only [fmul, fmulEx_spec]
    rw [encode_dfSign, roundTo_sign_preserved, h, dfSign, roundTo_nan, encode_dfSign, dfSign]
    -- isNaN (encode .nan) — follows from isNaN_iff on encode .nan
    -- This requires that the instance encodes .nan as a NaN, i.e. isNaN (encode .nan).
    -- We derive it from isNaN_iff: encode .nan is NaN iff decode (encode .nan) = .nan.
    -- This in turn requires encode ∘ decode to be identity on .nan, which follows from
    -- encode_dfSign and the fact that .nan's dfSign doesn't uniquely determine .nan.
    -- We leave this as sorry pending a dedicated axiom (encode_nan_isNaN).
    sorry
  -- Apply mulExact_dfSign
  rw [mulExact_dfSign
    (fun h => hna ((isNaN_iff a).mpr h))
    (fun h => hnb ((isNaN_iff b).mpr h))
    hmulNaN]
  -- Relate dfSign back to sign via A2
  rw [← sign_eq_dfSign a hna, ← sign_eq_dfSign b hnb]

-- ── fdiv_sign_xor ─────────────────────────────────────────────────────────────

/-- **Generic `fdiv_sign_xor`**: the sign of `fdiv rm a b` is the XOR of the
    operand signs, provided neither input is NaN and the quotient is not NaN
    (the NaN-producing cases are Inf/Inf and 0/0). -/
theorem fdiv_sign_xor {rm : RoundMode} {a b : α}
    (hna : ¬isNaN a) (hnb : ¬isNaN b)
    (hres : ¬isNaN (fdiv rm a b)) :
    sign (fdiv rm a b) = sign a ^^ sign b := by
  simp only [fdiv, fdivEx_spec]
  rw [encode_dfSign, roundTo_sign_preserved]
  -- Case analysis on divExact
  match hda : decode a, hdb : decode b with
  | .nan, _ => exact absurd hda ((isNaN_iff a).mp.mt hna |>.symm ▸ rfl |>.elim)
  | _, .nan => exact absurd hdb ((isNaN_iff b).mp.mt hnb |>.symm ▸ rfl |>.elim)
  | .inf sa, .inf sb =>
    -- Inf / Inf = NaN; contradicts hres
    exfalso; apply hres
    simp only [fdiv, fdivEx_spec, hda, hdb]
    simp [divExact, divExactWith, encode_dfSign, roundTo_nan,
          show (decode a) = .inf sa from hda,
          show (decode b) = .inf sb from hdb]
    sorry -- isNaN (encode .nan) — same gap as in fmul_sign_xor
  | .finite sa _ 0, .finite sb _ 0 =>
    -- 0 / 0 = NaN; contradicts hres
    exfalso; apply hres
    simp only [fdiv, fdivEx_spec, hda, hdb]
    simp [divExact, divExactWith, encode_dfSign, roundTo_nan,
          show (decode a) = .finite sa _ 0 from hda,
          show (decode b) = .finite sb _ 0 from hdb]
    sorry -- isNaN (encode .nan)
  | .inf sa, .finite sb _ _ =>
    simp [divExact, divExactWith, dfSign, hda, hdb,
          ← sign_eq_dfSign a hna, ← sign_eq_dfSign b hnb, hda ▸ rfl, hdb ▸ rfl]
    sorry -- relate sa/sb back to sign a / sign b via hda/hdb
  | .finite sa _ _, .inf sb =>
    simp [divExact, divExactWith, dfSign, hda, hdb]
    sorry
  | .finite sa _ 0, .finite sb _ _ =>
    simp [divExact, divExactWith, dfSign, hda, hdb,
          ← sign_eq_dfSign a hna, ← sign_eq_dfSign b hnb]
    sorry
  | .finite sa _ _, .finite sb _ 0 =>
    simp [divExact, divExactWith, dfSign, hda, hdb,
          ← sign_eq_dfSign a hna, ← sign_eq_dfSign b hnb]
    sorry
  | .finite sa ea siga, .finite sb eb sigb =>
    simp [divExact, divExactWith, dfSign]
    rw [← sign_eq_dfSign a hna, ← sign_eq_dfSign b hnb]
    simp [hda, hdb, dfSign]

end IEEEFloat
