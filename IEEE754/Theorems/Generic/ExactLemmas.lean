/-
  IEEE754.Theorems.Generic.ExactLemmas
  =====================================
  Format-agnostic lemmas about addExact / mulExact / divExact operating on
  DecodedFloat.  These fill gaps in F32/Props.lean that are needed by the
  generic sign theorems but are not format-specific.
-/

import IEEE754.ExactOps
import IEEE754.Theorems.F32.Props

open DecodedFloat

-- ── addExact sign preservation ────────────────────────────────────────────────

/-- Same-sign infinities add to the same-sign infinity. -/
theorem addExact_inf_same (rm : RoundMode) (s : Bool) :
    addExact rm (.inf s) (.inf s) = (.inf s, ExcFlags.empty) := by
  simp [addExact]

/-- If both (non-NaN) operands have `dfSign = s`, the addExact result does too.

    Key cases:
    * inf + inf (same sign) → inf (same sign)  [not covered by addExact_inf_opp]
    * inf + finite           → inf (same sign)
    * finite + finite, both zero               → sign determined by RDN rule, equals s
    * finite + finite, one zero                → other operand's sign = s
    * finite + finite, both nonzero, same sign → significands add, result > 0, sign = s -/
theorem addExact_same_dfSign {rm : RoundMode} {da db : DecodedFloat} {s : Bool}
    (hna : da ≠ .nan) (hnb : db ≠ .nan)
    (hsa : da.dfSign = s) (hsb : db.dfSign = s) :
    (addExact rm da db).1.dfSign = s := by
  match da, db with
  | .nan, _    => exact absurd rfl hna
  | _,    .nan => exact absurd rfl hnb
  | .inf sa, .inf sb =>
    simp only [dfSign] at hsa hsb; subst hsa; subst hsb
    simp [addExact, dfSign]
  | .inf sa, .finite _ _ _ =>
    simp only [dfSign] at hsa; subst hsa
    simp [addExact, dfSign]
  | .finite _ _ _, .inf sb =>
    simp only [dfSign] at hsb; subst hsb
    simp [addExact, dfSign]
  | .finite sa ea siga, .finite sb eb sigb =>
    simp only [dfSign] at hsa hsb; subst hsa; subst hsb
    -- Unfold addExact to its if-then-else body.
    simp only [addExact]
    by_cases h00 : siga = 0 ∧ sigb = 0
    · -- Both zero: result sign is `s && s || (s || s) && (rm = RDN)` which reduces to s.
      obtain ⟨rfl, rfl⟩ := h00
      simp only [beq_self_eq_true, Bool.and_true, Bool.true_and, ite_true, dfSign]
      cases s <;> simp
    · push_neg at h00
      by_cases h1 : siga = 0
      · -- a = 0, b ≠ 0: result is (.finite s eb sigb), dfSign = s.
        have h2 : sigb ≠ 0 := h00 h1
        simp only [show (siga == 0 && sigb == 0 : Bool) = false from by simp [h1, h2],
                   show (siga == 0 : Bool) = true from by simp [h1],
                   ite_false, ite_true, dfSign]
      · by_cases h2 : sigb = 0
        · -- a ≠ 0, b = 0: result is (.finite s ea siga), dfSign = s.
          simp only [show (siga == 0 && sigb == 0 : Bool) = false from by simp [h1],
                     show (siga == 0 : Bool) = false from by simp [h1],
                     show (sigb == 0 : Bool) = true from by simp [h2],
                     ite_false, ite_true, dfSign]
        · -- Both nonzero, same sign s.
          -- sa == sb = s == s = true, so resultSign = s and resultSig = siga'' + sigb''.
          -- siga'', sigb'' ≥ 1 (left-shifts of positive naturals), so resultSig > 0.
          simp only [show (siga == 0 && sigb == 0 : Bool) = false from by simp [h1, h2],
                     show (siga == 0 : Bool) = false from by simp [h1],
                     show (sigb == 0 : Bool) = false from by simp [h2],
                     show (s == s : Bool) = true from beq_self_eq_true s,
                     ite_false, ite_true]
          -- After simp, the goal involves:
          --   if siga'' + sigb'' == 0 then (.finite (rm=RDN) 0 0).dfSign = s
          --   else                         (.finite s _ _).dfSign = s
          -- We show the first branch is unreachable: siga'' + sigb'' > 0.
          have hposa : 0 < siga <<< (ea - (if ea ≤ eb then ea else eb)).toNat := by
            apply Nat.shiftLeft_pos; omega
          have hposb : 0 < sigb <<< (eb - (if ea ≤ eb then ea else eb)).toNat := by
            apply Nat.shiftLeft_pos; omega
          simp only [show (siga <<< _ + sigb <<< _ == 0 : Bool) = false from by
                       simp [Nat.ne_of_gt (by omega)],
                     ite_false, dfSign]

-- ── mulExact sign preservation ────────────────────────────────────────────────

/-- The dfSign of mulExact is XOR of the two operands' dfSigns,
    provided neither operand is NaN and the product is not NaN (i.e. not Inf×0). -/
theorem mulExact_dfSign {da db : DecodedFloat}
    (hna : da ≠ .nan) (hnb : db ≠ .nan)
    (hnnaN : (mulExact da db).1 ≠ .nan) :
    (mulExact da db).1.dfSign = da.dfSign ^^ db.dfSign := by
  match da, db with
  | .nan, _    => exact absurd rfl hna
  | _,    .nan => exact absurd rfl hnb
  | .inf sa, .inf sb        => simp [mulExact, dfSign]
  | .inf sa, .finite sb _ 0 => simp [mulExact] at hnnaN
  | .inf sa, .finite sb _ _ => simp [mulExact, dfSign]
  | .finite sa _ 0, .inf sb => simp [mulExact] at hnnaN
  | .finite sa _ _, .inf sb => simp [mulExact, dfSign]
  | .finite sa ea siga, .finite sb eb sigb =>
    simp [mulExact, dfSign]

-- ── divExact sign preservation ────────────────────────────────────────────────

/-- The dfSign of divExact is XOR of the two operands' dfSigns,
    provided neither operand is NaN and the quotient is not NaN.
    The NaN-producing cases are Inf/Inf and 0/0 — excluded by `hnnaN`. -/
theorem divExact_dfSign {da db : DecodedFloat}
    (hna : da ≠ .nan) (hnb : db ≠ .nan)
    (hnnaN : (divExact da db).1 ≠ .nan) :
    (divExact da db).1.dfSign = da.dfSign ^^ db.dfSign := by
  match da, db with
  | .nan, _    => exact absurd rfl hna
  | _,    .nan => exact absurd rfl hnb
  | .inf sa, .inf sb =>
    simp [divExact, divExactWith] at hnnaN
  | .inf sa, .finite sb _ _ =>
    simp [divExact, divExactWith, dfSign]
  | .finite sa _ _, .inf sb =>
    simp [divExact, divExactWith, dfSign]
  | .finite sa ea siga, .finite sb eb sigb =>
    by_cases h1 : siga = 0 <;> by_cases h2 : sigb = 0
    · -- 0/0 → NaN, contradicts hnnaN
      subst h1; subst h2; simp [divExact, divExactWith] at hnnaN
    · -- 0/nonzero → (.finite (sa != sb) 0 0)
      subst h1; simp [divExact, divExactWith, h2, dfSign]
    · -- nonzero/0 → (.inf (sa != sb))
      subst h2; simp [divExact, divExactWith, h1, dfSign]
    · -- nonzero/nonzero → sign = sa XOR sb
      simp [divExact, divExactWith, h1, h2, dfSign]
