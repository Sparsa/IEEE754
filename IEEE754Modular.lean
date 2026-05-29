/-
  IEEE754Modular.lean
  ===================
  Top-level entry point for the modular IEEE 754 formalization.

  Import hierarchy:
    Basic → ExactOps → F32/Defs, F64/Defs → Conversions
    F32/Defs → Theorems/Classification → Props → Codec
                → NaN → Inf → Sign (contains G–J)
    F64/Defs → Theorems/F64/Classification → F64/Codec
                → F64/NaN → F64/Inf → F64/Sign
    F32/Defs → Oracle
-/

import IEEE754.Basic
import IEEE754.ExactOps
import IEEE754.F32.Defs
import IEEE754.F64.Defs
import IEEE754.Conversions
-- F32 theorem chain
import IEEE754.Theorems.F32.Classification
import IEEE754.Theorems.F32.Props
import IEEE754.Theorems.F32.Codec
import IEEE754.Theorems.F32.NaN
import IEEE754.Theorems.F32.Inf
import IEEE754.Theorems.F32.Sign
-- F64 theorem chain
import IEEE754.Theorems.F64.Classification
import IEEE754.Theorems.F64.Codec
import IEEE754.Theorems.F64.NaN
import IEEE754.Theorems.F64.Inf
import IEEE754.Theorems.F64.Sign
import IEEE754.Oracle
