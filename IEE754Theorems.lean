import IEEE754.IEEE754
-- ─────────────────────────────────────────────────────────────────────────────
-- §11 (continued): Generic DecodedFloat / rounding correctness
-- ─────────────────────────────────────────────────────────────────────────────
-- These theorems are format-independent: they characterise the common arithmetic
-- core (§4) and the rounding box (§5).  Proofs of format-specific properties
-- (§11c below) should reduce to these.

-- ── Commutativity of exact arithmetic ────────────────────────────────────────

/-- addExact is commutative: a + b = b + a (before rounding). -/
theorem addExact_comm (rm : RoundMode) (a b : DecodedFloat) :
    addExact rm a b = addExact rm b a := by
    simp [addExact]
    cases a with
    | nan => cases b with
              | nan => simp
              | inf => simp
              | _ => simp

    | inf => cases b with
              | nan => simp
              | inf => simp
                       split
                       ·
                          rename_i h1
                          rename_i h2
                          rw [h1]
                          simp
                       ·
                          rename_i h1
                          simp_all
                          rw [eq_comm]
                          exact h1
              | _ => simp
    | _ => cases b with
           | nan => simp
           | inf => simp
           | _ => simp
                  split
                  ·
                    rename_i sig_z_sig1_z
                    rename_i sign exp sig
                    rename_i sign1 exp1 sig1
                    cases sign1 <;> cases sign <;> simp <;>
                    { cases sig_z_sig1_z
                      rename_i right left
                      intros h1
                      rw [left,right]
                      simp
                      omega
                    }
                  ·
                    rename_i n_sig_z_sig1_z
                    rename_i sign exp sig
                    rename_i sign1 exp1 sig1
                    split
                    ·
                      rename_i sig1z
                      rw [sig1z] at n_sig_z_sig1_z
                      simp_all
                    ·
                      rename_i sig1nz
                      simp_all
                      split
                      ·
                        rfl
                      ·
                        split
                        ·
                          rename_i sign1_eq_sign
                          rw [eq_comm] at sign1_eq_sign
                          simp [sign1_eq_sign]
                          simp_all
                          constructor
                          · -- DecodedFloat equality: min(exp,exp1) = min(exp1,exp)
                            by_cases h_le : exp ≤ exp1
                            · rw [if_pos h_le]
                              by_cases h_le2 : exp1 ≤ exp
                              · have heq : exp = exp1 := le_antisymm h_le h_le2
                                subst heq
                                simp [Nat.add_comm]
                              · rw [if_neg h_le2]
                                simp only [Int.sub_self, Int.toNat_zero, Nat.shiftLeft_zero]
                                rw [Nat.add_comm]
                            · have h_lt : exp1 < exp := by omega
                              rw [if_neg h_le, if_pos (by omega : exp1 ≤ exp)]
                              simp only [Int.sub_self, Int.toNat_zero, Nat.shiftLeft_zero]
                              rw [Nat.add_comm]
                          · native_decide
                        · -- sa ≠ sb: subtraction branches commute
                          rename_i h_ne
                          by_cases h_le : exp ≤ exp1
                          · rw [if_pos h_le]
                            by_cases h_le2 : exp1 ≤ exp
                            · -- exp = exp1; A = sig, B = sig1, A' = sig1, B' = sig
                              have heq : exp = exp1 := le_antisymm h_le h_le2
                              subst heq
                              simp only [Int.sub_self, Int.toNat_zero, Nat.shiftLeft_zero,
                                         ↓reduceIte]
                              rcases Nat.lt_trichotomy sig sig1 with h | rfl | h
                              · rw [if_neg (by omega : ¬sig ≥ sig1),
                                    if_pos (by omega : sig1 ≥ sig)]
                              · simp [Nat.sub_self]
                              · rw [if_pos (by omega : sig ≥ sig1),
                                    if_neg (by omega : ¬sig1 ≥ sig)]
                            · -- exp < exp1; both minExps = exp
                              rw [if_neg h_le2]
                              simp only [Int.sub_self, Int.toNat_zero, Nat.shiftLeft_zero]
                              rcases Nat.lt_trichotomy sig (sig1 <<< (exp1 - exp).toNat) with h | rfl | h
                              · rw [if_neg (by omega : ¬sig ≥ sig1 <<< (exp1 - exp).toNat),
                                    if_pos (by omega : sig1 <<< (exp1 - exp).toNat ≥ sig)]
                              · simp [Nat.sub_self]
                              · rw [if_pos (by omega : sig ≥ sig1 <<< (exp1 - exp).toNat),
                                    if_neg (by omega : ¬sig1 <<< (exp1 - exp).toNat ≥ sig)]
                          · -- exp > exp1; both minExps = exp1
                            have h_lt : exp1 < exp := by omega
                            rw [if_neg h_le, if_pos (by omega : exp1 ≤ exp)]
                            simp only [Int.sub_self, Int.toNat_zero, Nat.shiftLeft_zero]
                            rcases Nat.lt_trichotomy (sig <<< (exp - exp1).toNat) sig1 with h | rfl | h
                            · rw [if_neg (by omega : ¬sig <<< (exp - exp1).toNat ≥ sig1),
                                  if_pos (by omega : sig1 ≥ sig <<< (exp - exp1).toNat)]
                            · simp [Nat.sub_self]
                            · rw [if_pos (by omega : sig <<< (exp - exp1).toNat ≥ sig1),
                                  if_neg (by omega : ¬sig1 ≥ sig <<< (exp - exp1).toNat)]













/-- mulExact is commutative: a × b = b × a (before rounding). -/
theorem mulExact_comm (a b : DecodedFloat) :
    mulExact a b = mulExact b a := by
    simp [mulExact]
    cases a with
    | nan => cases b with
              | nan => simp
              | inf => simp
              | _ => simp
    | inf => cases b with
              | nan => simp
              | inf => simp
                       rename_i sign1 sign
                       cases sign1 <;> cases sign <;> simp
              | _ => rename_i sig exp
                     rename_i sign sign1
                     congr
                     ·



-- ── roundTo: special-value fixed points ──────────────────────────────────────


