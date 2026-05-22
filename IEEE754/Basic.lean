/-
  IEEE754.Basic
  =============
  §1  Rounding Modes
  §2  DecodedFloat — common "Rational Operand" representation
  §3  FPFormat — format descriptor
  §3.5 ExcFlags — IEEE 754-2019 §7 exception flags
-/

import Std.Tactic.BVDecide
open BitVec


-- ─────────────────────────────────────────────────────────────────────────────
-- §1  Rounding Modes
-- ─────────────────────────────────────────────────────────────────────────────

inductive RoundMode where
  | RNE   -- Round to Nearest, ties to Even   (IEEE default)
  | RTZ   -- Round Toward Zero                (truncation)
  | RDN   -- Round Down (toward -∞)
  | RUP   -- Round Up   (toward +∞)
  | RMM   -- Round to Nearest, ties away from zero
  | DYN   -- Dynamic rounding (placeholder)
  deriving Repr, BEq, DecidableEq

def classifyRounding (x : UInt8) : RoundMode :=
  match x with
  | 0 => .RNE
  | 1 => .RTZ
  | 2 => .RDN
  | 3 => .RUP
  | 4 => .RMM
  | _ => .DYN


-- ─────────────────────────────────────────────────────────────────────────────
-- §2  DecodedFloat — common "Rational Operand" representation
-- ─────────────────────────────────────────────────────────────────────────────

/-- Format-agnostic exact representation of a floating-point value.
    `finite sign exp sig` means (-1)^sign × sig × 2^exp, where sig : Nat (arbitrary precision).
    For a normal F32 with unbiased exponent e and 24-bit significand s:
      exp = e - 23,  sig = s  -/
inductive DecodedFloat where
  | finite (sign : Bool) (exp : Int) (sig : Nat) : DecodedFloat
  | inf    (sign : Bool) : DecodedFloat
  | nan    : DecodedFloat
  deriving Repr

namespace DecodedFloat

def isNaN   : DecodedFloat → Bool | .nan     => true | _ => false
def isInf   : DecodedFloat → Bool | .inf _   => true | _ => false
def isFinite: DecodedFloat → Bool | .finite _ _ _ => true | _ => false
def isZero  : DecodedFloat → Bool | .finite _ _ 0 => true | _ => false

def dfSign  : DecodedFloat → Bool
  | .finite s _ _ => s
  | .inf s        => s
  | .nan          => false

end DecodedFloat


-- ─────────────────────────────────────────────────────────────────────────────
-- §3  FPFormat — format descriptor
-- ─────────────────────────────────────────────────────────────────────────────

/-- Describes a binary floating-point format (IEEE 754 style). -/
structure FPFormat where
  M    : Nat   -- mantissa field bits (e.g. 23 for F32, 52 for F64)
  E    : Nat   -- exponent field bits (e.g.  8 for F32, 11 for F64)
  bias : Nat   -- exponent bias = 2^(E-1) - 1

def f32Fmt : FPFormat := { M := 23, E := 8,  bias := 127  }
def f64Fmt : FPFormat := { M := 52, E := 11, bias := 1023 }


-- ─────────────────────────────────────────────────────────────────────────────
-- §3.5  Exception Flags (IEEE 754-2019 §7)
-- ─────────────────────────────────────────────────────────────────────────────

/-- The five IEEE 754 sticky exception flags.
    Each operation returns the flags it raised; accumulation across operations
    is the caller's responsibility (OR the sets together). -/
structure ExcFlags where
  invalidOp : Bool := false  -- §7.2  invalid operands → NaN from non-NaN inputs
  divByZero : Bool := false  -- §7.3  finite nonzero ÷ 0
  overflow  : Bool := false  -- §7.4  result magnitude → ∞  (always implies inexact)
  underflow : Bool := false  -- §7.5  result tiny and inexact (always implies inexact)
  inexact   : Bool := false  -- §7.6  result was rounded
  deriving Repr, BEq

namespace ExcFlags

/-- No flags raised. -/
def empty : ExcFlags := {}

/-- Combine two flag sets (bitwise OR — sticky semantics). -/
def merge (a b : ExcFlags) : ExcFlags :=
  { invalidOp := a.invalidOp || b.invalidOp
    divByZero := a.divByZero || b.divByZero
    overflow  := a.overflow  || b.overflow
    underflow := a.underflow || b.underflow
    inexact   := a.inexact   || b.inexact }

-- Single-flag smart constructors.
-- IEEE 754 §7.4 and §7.5 require that overflow/underflow always set inexact too.
def mkInvalidOp : ExcFlags := { invalidOp := true }
def mkDivByZero : ExcFlags := { divByZero := true }
def mkOverflow  : ExcFlags := { overflow  := true, inexact := true }
def mkUnderflow : ExcFlags := { underflow := true, inexact := true }
def mkInexact   : ExcFlags := { inexact   := true }

theorem mkOverflow_inexact  : ExcFlags.mkOverflow.inexact  := by decide
theorem mkUnderflow_inexact : ExcFlags.mkUnderflow.inexact := by decide

end ExcFlags
