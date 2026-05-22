/-
  IEEE754.Oracle
  ==============
  §12  Hardware Oracle Interface (cocotb / CVDP integration)
  Exported functions called from Python via ctypes.
-/

import IEEE754.F32.Defs

open BitVec

namespace F32.Oracle

@[export f32_add]
def f32_add (a b : UInt32) (round : UInt8) : UInt32 :=
  let fa : F32 := BitVec.ofNat 32 a.toNat
  let fb : F32 := BitVec.ofNat 32 b.toNat
  (F32.fadd (classifyRounding round) fa fb).toNat.toUInt32

@[export f32_mul]
def f32_mul (a b : UInt32) (round : UInt8) : UInt32 :=
  let fa : F32 := BitVec.ofNat 32 a.toNat
  let fb : F32 := BitVec.ofNat 32 b.toNat
  (F32.fmul (classifyRounding round) fa fb).toNat.toUInt32

@[export f32_fma]
def f32_fma (a b c : UInt32) (round : UInt8) : UInt32 :=
  let fa : F32 := BitVec.ofNat 32 a.toNat
  let fb : F32 := BitVec.ofNat 32 b.toNat
  let fc : F32 := BitVec.ofNat 32 c.toNat
  (F32.fma (classifyRounding round) fa fb fc).toNat.toUInt32

@[export float32_classify]
def classify (a : UInt32) : UInt8 :=
  let f : F32 := BitVec.ofNat 32 a.toNat
  if f.isNaN        then 0
  else if f.isInf   then 1
  else if f.isZero  then 2
  else if f.isSubnormal then 3
  else 4   -- normal

-- Sanity checks (evaluated at build time)
#eval (f32_add 0x3F800000 0x3F800000 0x0).toBitVec.toHex  -- 1.0+1.0 = 2.0 → "40000000"
#eval (f32_add 0x3FC00000 0x3FC00000 0x0).toBitVec.toHex  -- 1.5+1.5 = 3.0 → "40400000"
#eval (f32_add 0x1B407ccc 0x1B407CCC 0x00).toBitVec.toHex
#eval (f32_mul 0x3F800000 0x3F800000 0x0).toBitVec.toHex  -- 1.0*1.0 = 1.0 → "3f800000"
#eval (f32_mul 0x40000000 0x40000000 0x0).toBitVec.toHex  -- 2.0*2.0 = 4.0 → "40800000"
#eval (f32_fma 0x40000000 0x40400000 0x40800000 0x0).toBitVec.toHex -- 2.0*3.0+4.0=10.0 → "41200000"
#eval classify 0x3F800000  -- normal → 4
#eval classify 0x00000000  -- zero   → 2
#eval classify 0x7F800000  -- inf    → 1
#eval classify 0x7FC00000  -- NaN    → 0
#eval classify 0x00000001  -- subnormal → 3

end F32.Oracle
