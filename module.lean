-- Calculate mod (2^32)-1 = 4294967295
import Paperproof

def BIT := 32
def MODULO:Nat := 2^BIT - 1
#eval MODULO
def mod_orig (a : Nat) :=
  a % MODULO
#eval mod_orig 55
def mod_fast (input:Nat) :=
  let MOD := (input >>> BIT) + (input &&& MODULO)
  if MOD ≥ MODULO then MOD - MODULO else MOD

#eval 0xffffffff = 2^32-1
example (a : Nat) : a >>> 32 = a / 2^32 := by exact?
example (a b : Nat) : b * a /b = a := by apply?

example (n m k : Nat) : (n * m + k) % m = k % m := by exact?
theorem mod_pred (a b : Nat) (hb : 1 < b) :
    a % (b - 1) = (a / b + a % b) % (b - 1) := by
    have h1 : a / b * (b - 1) + a / b = a / b * b := by
      cases b with
        | zero => simp
        | succ n =>
          simp [Nat.mul_succ]
    have hdiv := Nat.div_add_mod a b
    have h2 : a / b * b + a % b = a := by
      rw [Nat.mul_comm]
      exact hdiv

    have k : a = a / b * (b - 1) + (a / b + a % b) := by
      omega

    have hmul : a / b * (b - 1) = a / b * b - a / b := by
      rw [Nat.mul_sub_one]
    have goal : a % (b - 1) = (a / b + a % b) % (b - 1) := by
      have lhs : a % (b - 1) = (a / b * (b - 1) + (a / b + a % b)) % (b - 1) := by
        rw [← k]
      rw [lhs]
      exact Nat.mul_add_mod_self_right (a/b) (b-1) (a/b + a%b)
    exact goal


theorem check_equality (a : Nat) (h : a <  2^33) :
    mod_orig a = mod_fast a := by
  simp only [mod_orig, mod_fast, MODULO, BIT]
  have hsr : a >>> 32 = a / 4294967296 := by
    have := Nat.shiftRight_eq_div_pow a 32
    simp [show (2:Nat)^32 = 4294967296 from by native_decide] at this
    exact this
  have hmod : a &&& 4294967295 = a % 4294967296 := by
    have := Nat.and_two_pow_sub_one_eq_mod a 33
    simp [show (2:Nat)^32 - 1 = 4294967295 from by native_decide] at this
    exact this
  have hi_bound : a / 4294967296 ≤ 4294967294 := by
    apply Nat.div_le_of_le_mul
    simp [show 2^33 =  8589934592 from by native_decide] at h
    omega
  have lo_bound : a % 4294967296 ≤ 4294967295 := by
    have := Nat.mod_lt a (show 0 < 4294967296 by native_decide)
    omega
  have sum_bound : a / 4294967296 + a % 4294967296 < 2 * 4294967295 := by
    omega
  have key : a % 4294967295 = (a / 4294967296 + a % 4294967296) % 4294967295 := by
    have := mod_pred a 4294967296 (by native_decide)
    simp [show (4294967296 : Nat) - 1 = 4294967295 from by native_decide] at this
    exact this
  rw [hsr, hmod, key]
  simp only [show (2:Nat)^32 - 1 = 4294967295 from by native_decide]
  by_cases hc : a / 4294967296 + a % 4294967296 ≥ 4294967295
  · rw [if_pos hc]
    omega
  · rw [if_neg hc]
    omega

--// See https://homepage.divms.uiowa.edu/~jones/bcd/mod.shtml#exmod3
--uint64_t mod_fast(uint64_t input) {
--//    return ( (input/(MODULO+1)) + (input % (MODULO+1)) ) % MODULO;
--    return (input>>32) + (input & 0xffffffff);
--} (edited)
