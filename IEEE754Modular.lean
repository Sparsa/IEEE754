/-
  IEEE754Modular.lean
  ===================
  Top-level entry point for the modular IEEE 754 formalization.

  Import hierarchy:
    Basic → ExactOps → F32/Defs, F64/Defs → Conversions
    F32/Defs → Theorems/Classification → Props → Codec
                → NaN → Inf → Sign (contains G–J)
    F32/Defs → Oracle
-/

import IEEE754.Basic
import IEEE754.ExactOps
import IEEE754.F32.Defs
import IEEE754.F64.Defs
import IEEE754.Conversions
import IEEE754.Theorems.Classification
import IEEE754.Theorems.Props
import IEEE754.Theorems.Codec
import IEEE754.Theorems.NaN
import IEEE754.Theorems.Inf
import IEEE754.Theorems.Sign
import IEEE754.Oracle
