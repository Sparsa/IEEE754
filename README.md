# IEEE 754-2019 Formal Verification in Lean 4

A machine-checked formalization of the IEEE 754-2019 binary floating-point standard, targeting 32-bit (`F32`) and 64-bit (`F64`) formats. The library provides verified implementations of all five arithmetic operations (add, subtract, multiply, divide, fused multiply-add) and square root, plus a hardware oracle interface for co-simulation with RTL designs via Python/ctypes.

---

## Table of Contents

1. [Overview](#overview)
2. [Architecture](#architecture)
3. [DecodedFloat — the rational operand representation](#decodedfloat)
4. [Rounding Modes](#rounding-modes)
5. [File Structure](#file-structure)
6. [Module Reference](#module-reference)
7. [Theorem Index](#theorem-index)
8. [Build Instructions](#build-instructions)
9. [Hardware Oracle Interface](#hardware-oracle-interface)
10. [Proof Status](#proof-status)
11. [Dependencies](#dependencies)

---

## Overview

The library formalizes the full IEEE 754-2019 computational model:

- **Formats**: binary32 (`F32 = BitVec 32`) and binary64 (`F64 = BitVec 64`)
- **Operations**: `fadd`, `fsub`, `fmul`, `fdiv`, `fma`, `fsqrt`
- **Rounding**: all five directed modes plus RNE and RMM
- **Special values**: ±0, ±∞, quiet NaN, signaling NaN
- **Exceptions**: IEEE §7 invalid operation, division by zero, overflow, underflow, inexact
- **Theorems**: NaN propagation, Inf arithmetic, sign rules, commutativity, codec round-trips, single-rounding guarantees

The approach follows the **decode → exact-op → round → encode** pipeline, which matches the hardware implementation strategy used in verified processor designs.

---

## Architecture

```
  F32/F64 bit-vector
       │
       ▼
   decode()          ← BitVec 32/64 → DecodedFloat
       │
       ▼
  exact arithmetic   ← addExact / mulExact / divExact / fmaExact / sqrtExact
  (arbitrary precision, no rounding)
       │
       ▼
   roundTo fmt rm    ← IEEE rounding with ExcFlags
       │
       ▼
   encode fmt        ← DecodedFloat → BitVec
       │
       ▼
  F32/F64 bit-vector
```

### Key Types

| Type | Kind | Description |
|------|------|-------------|
| `F32` | `abbrev` | `BitVec 32` — 32-bit IEEE float |
| `F64` | `abbrev` | `BitVec 64` — 64-bit IEEE float |
| `DecodedFloat` | `inductive` | Format-agnostic exact representation |
| `FPFormat` | `structure` | Format descriptor (`M`, `E`, `bias`) |
| `RoundMode` | `inductive` | 6 rounding modes |
| `ExcFlags` | `structure` | 5 IEEE exception sticky flags |

---

## DecodedFloat

`DecodedFloat` is the central intermediate representation shared by all arithmetic operations:

```lean
inductive DecodedFloat where
  | finite (sign : Bool) (exp : Int) (sig : Nat) : DecodedFloat
  | inf    (sign : Bool) : DecodedFloat
  | nan    : DecodedFloat
```

The value of `finite sign exp sig` is `(-1)^sign × sig × 2^exp`, where `sig` is an arbitrary-precision natural number. For a normal F32 with biased exponent `e` and 24-bit significand `s`:

```
exp = (e : Int) - 127 - 23
sig = 2^23 + mantissa_field
```

For a subnormal F32 (biased exponent = 0):

```
exp = 1 - 127 - 23 = -149
sig = mantissa_field   (no implicit leading 1)
```

`DecodedFloat` also carries helpers: `isNaN`, `isInf`, `isFinite`, `isZero`, `dfSign`.

---

## Rounding Modes

| Constructor | IEEE Name | Description |
|-------------|-----------|-------------|
| `RNE` | roundTiesToEven | Nearest, ties to even (IEEE default) |
| `RTZ` | roundTowardZero | Truncation |
| `RDN` | roundTowardNegativeInfinity | Floor |
| `RUP` | roundTowardPositiveInfinity | Ceiling |
| `RMM` | roundTiesToAway | Nearest, ties away from zero |
| `DYN` | — | Dynamic placeholder (treated as RNE) |

`classifyRounding : UInt8 → RoundMode` maps RISC-V `frm` field encodings (0–4) to modes.

---

## File Structure

The project ships two parallel targets:

### Monolithic target: `IEEE754`

```
IEEE754.lean            (3568 lines — original, untouched)
```

### Modular target: `IEEE754Modular`

```
IEEE754Modular.lean           ← top-level entry point
IEEE754/
├── Basic.lean                §1–3.5   types and flags
├── ExactOps.lean             §4–5     exact arithmetic and rounding
├── F32/
│   └── Defs.lean             §6–7     F32 fields, codec, all f* operations
├── F64/
│   └── Defs.lean             §8–9     F64 fields, codec, all f* operations
├── Conversions.lean          §10      F32↔F64, F32↔Int32
├── Oracle.lean               §12      @[export] functions for Python ctypes
└── Theorems/
    ├── F32/
    │   ├── Classification.lean   §11a     exclusivity lemmas, F32Class
    │   ├── Props.lean            §11b     algebraic properties, roundTo lemmas
    │   ├── Codec.lean            §11c     encode/decode round-trip theorems ✅
    │   ├── NaN.lean              §11B–C   NaN propagation and invalid-op cases
    │   ├── Inf.lean              §11D     Inf arithmetic theorems ✅
    │   └── Sign.lean             §11E–J   sign rules, order, FMA, sqrt theorems
    └── F64/
        ├── Classification.lean   §11a     exclusivity lemmas, F64Class ✅
        ├── Props.lean            (re-uses F32 format-agnostic lemmas)
        ├── Codec.lean            §11c     encode/decode round-trip theorems ✅
        ├── NaN.lean              §11B–C   NaN propagation and invalid-op cases ✅
        ├── Inf.lean              §11D     Inf arithmetic theorems (fdiv sorry)
        └── Sign.lean             §11E–J   sign rules, fsub, fsqrt (flt_trans sorry)
```

### Import dependency graph

```
Basic
  └── ExactOps
        ├── F32/Defs ──────────────────────────────── Oracle
        │     └── Theorems/F32/Classification
        │                    └── Props (+ Conversions)
        │                          └── Codec
        │                                └── NaN
        │                                      └── Inf
        │                                            └── Sign
        └── F64/Defs
              ├── Conversions (+ F32/Defs)
              └── Theorems/F64/Classification
                             └── Codec (imports F32/Props)
                                   └── NaN
                                         └── Inf
                                               └── Sign
```

---

## Module Reference

### `IEEE754.Basic` — §1–3.5

**Types defined:**

- `RoundMode` — 6-constructor inductive
- `classifyRounding : UInt8 → RoundMode` — RISC-V frm encoding
- `DecodedFloat` — `.finite sign exp sig | .inf sign | .nan`
- `DecodedFloat.{isNaN, isInf, isFinite, isZero, dfSign}` — predicates and sign accessor
- `FPFormat` — `{ M E bias : Nat }`
- `f32Fmt : FPFormat` — `{ M := 23, E := 8, bias := 127 }`
- `f64Fmt : FPFormat` — `{ M := 52, E := 11, bias := 1023 }`
- `ExcFlags` — `{ invalidOp divByZero overflow underflow inexact : Bool }`
- `ExcFlags.{empty, merge, mkInvalidOp, mkDivByZero, mkOverflow, mkUnderflow, mkInexact}`

---

### `IEEE754.ExactOps` — §4–5

**Helpers:**

- `intSqrt : Nat → Nat` *(private)* — Newton's method integer square root (O(log log x) iterations)
- `findLeadingBit : Nat → Nat → Nat` — position of the highest set bit (exported; used in `Theorems/Codec.lean`)

**Exact arithmetic (return `DecodedFloat × ExcFlags`):**

| Function | Description |
|----------|-------------|
| `addExact` | Exact addition/subtraction; handles all special cases per IEEE §6 |
| `mulExact` | Exact multiplication; sign = XOR, exp = sum, sig = product |
| `divExact` / `divExactWith` | Exact division; detects divide-by-zero and infinite cases |
| `fmaExact` | Fused multiply-add: one exact result, single-rounding guarantee |
| `sqrtExact` | Square root via integer sqrt on scaled significand (scaled by 4⁶⁰ for guard bits) |

**Rounding:**

- `roundTo : FPFormat → RoundMode → DecodedFloat × ExcFlags → DecodedFloat × ExcFlags`
  Implements IEEE Table 4 rounding to the given format, producing the correctly-rounded result and accumulating exception flags.

---

### `IEEE754.F32.Defs` — §6–7

**Type abbreviation:** `abbrev F32 := BitVec 32`

**Field accessors** (all `def`, operate on the bit-vector directly):

| Accessor | Bits | Description |
|----------|------|-------------|
| `sign` | 31 | Sign bit |
| `expRaw` | 30:23 | Raw 8-bit biased exponent |
| `mantissa` | 22:0 | 23-bit mantissa field |
| `significand` | — | `mantissa` with implicit leading bit prepended (24-bit) |

**Classification predicates:** `isNaN`, `isInf`, `isZero`, `isSubnormal`, `isNormal`, `isFinite`

**Special constants:** `posZero`, `negZero`, `posInf`, `negInf`, `qNaN`, `sNaN`, `maxNormal`, `minNormal`, `minSubnormal`

**Codec:**

- `F32.decode : F32 → DecodedFloat` — bit-vector → `DecodedFloat`
- `F32.encode : FPFormat → DecodedFloat → F32` — `DecodedFloat` → bit-vector (calls `roundTo`)
- `F32.pack : Bool → UInt8 → UInt32 → F32` — assemble from (sign, expRaw, mantissa)

**Comparison:** `feq`, `flt`, `fle`, `fgt`, `fge`, `fmin`, `fmax` — IEEE 754 totalOrder and minNum/maxNum

**Arithmetic wrappers:**

| Low-level (`*Ex`) | High-level | Description |
|-------------------|------------|-------------|
| `faddEx` | `fadd` | Addition |
| `fmulEx` | `fmul` | Multiplication |
| `fdivEx` | `fdiv` | Division |
| `fmaEx` | `fma` | Fused multiply-add |
| `fsqrtEx` | `fsqrt` | Square root |
| — | `fsub` | Subtraction (negates second operand) |

The `Ex` variants return `F32 × ExcFlags`; the top-level variants discard flags (or accept a flags accumulator).

---

### `IEEE754.F64.Defs` — §8–9

Mirrors `F32.Defs` for 64-bit floats. `abbrev F64 := BitVec 64`. Field positions:

| Accessor | Bits |
|----------|------|
| `sign` | 63 |
| `expRaw` | 62:52 |
| `mantissa` | 51:0 |

All arithmetic operations (`fadd`, `fmul`, `fdiv`, `fma`, `fsqrt`, `fsub`) and codec functions are defined under `namespace F64` using `f64Fmt`.

---

### `IEEE754.Conversions` — §10

| Function | Type | Description |
|----------|------|-------------|
| `F32.toFloat64` | `F32 → F64` | Lossless widening |
| `F32.ofFloat64` | `RoundMode → F64 → F32` | Narrowing with rounding |
| `F32.ofInt32` | `RoundMode → Int32 → F32` | Integer-to-float conversion |
| `F32.toInt32` | `RoundMode → F32 → Int32` | Float-to-integer (IEEE §5.8) |

---

### `IEEE754.Theorems.Classification` — §11a

**Classifier:**

```lean
inductive F32Class where
  | zero | subnormal | normal | inf | nan
```

`classify : F32 → F32Class` maps every bit-vector to exactly one class.

**Partition lemmas** (all proved):

| Theorem | Statement |
|---------|-----------|
| `classify_exclusive` | Every float belongs to exactly one class (proven as a list-sum = 1) |
| `finite_classify` | `¬isNaN → ¬isInf → isZero ∨ isSubnormal ∨ isNormal` |

**Exclusivity lemmas** (all proved, used throughout the theorem chain):

- `isZero_false_of_{isSubnormal, isNormal, isInf, isNaN}`
- `isSubnormal_false_of_{isZero, isNormal, isInf, isNaN}`
- `isNormal_false_of_{isZero, isSubnormal, isInf, isNaN}`
- `isInf_false_of_{isZero, isSubnormal, isNormal, isNaN, isFinite}`
- `isNaN_false_of_{isZero, isSubnormal, isNormal, isInf, isFinite}`

**Bijectivity lemmas:** `biject_class_{zero, nan, inf, normal, subnormal}` — each proves `classify f = .C ↔ f.isC`.

---

### `IEEE754.Theorems.Props` — §11b

Selected properties:

| Theorem | Statement |
|---------|-----------|
| `negate_sign` | `(-f).sign = !f.sign` |
| `negate_negate` | `- -f = f` |
| `abs_sign` | `f.abs.sign = false` |
| `feq_refl` | `¬f.isNaN → f.feq f = true` |
| `feq_symm` | `f.feq g = g.feq f` |
| `nan_neq_self` | `f.isNaN → f.feq f = false` |
| `zero_eq_neg_zero` | `posZero.feq negZero = true` |
| `addExact_comm` | `addExact rm a b = addExact rm b a` |
| `mulExact_comm` | `mulExact a b = mulExact b a` |
| `roundTo_sign_preserved` | rounding preserves the sign of finite values |
| `addExact_nan_l/r` | NaN absorbs in addExact |
| `mulExact_nan_l/r` | NaN absorbs in mulExact |
| `addExact_inf_opp` | `∞ + (-∞) = NaN` |
| `addExact_inf_finite` | `∞ + finite = ∞` |
| `mulExact_inf_zero` | `∞ × 0 = NaN` (invalid operation) |
| `mulExact_inf_nonzero` | `∞ × nonzero = ∞` |
| `mulExact_finite_sign` | sign of product of two finite values |
| `isNormalForm` | predicate characterising fixed points of `roundTo`: nan/inf/zero(e=0)/normal-range finites |
| `roundTo_idempotent` | `isNormalForm fmt d → roundTo fmt rm d = (d, ExcFlags.empty)` ✅ |

---

### `IEEE754.Theorems.Codec` — §11c ✅

Round-trip theorems between `F32` and `DecodedFloat` — **all fully proved**:

| Theorem | Statement |
|---------|-----------|
| `decode_nan` | `f.isNaN → f.decode = .nan` |
| `decode_inf` | `f.isInf → f.decode = .inf f.sign` |
| `decode_isZero` | `f.isZero → (f.decode).isZero` |
| `encode_decode_normal` | For normal `f`: `encode f32Fmt (decode f) = f` |
| `encode_decode_subnormal` | For subnormal `f`: `encode f32Fmt (decode f) = f` |
| `encode_nan_isNaN` | `(encode fmt .nan).isNaN` |
| `encode_inf_isInf` | `(encode fmt (.inf s)).isInf` |
| `encode_zero_isZero` | `(encode fmt (.finite s 0 0)).isZero` |

Private helper lemmas proven along the way: `pack_sign_expRaw_mantissa`, `findLeadingBit_range`, `findLeadingBit_le`, `nat_toUInt8_toBitVec_toNat`, `nat_toUInt32_trunc23_toNat`.

---

### `IEEE754.Theorems.NaN` — §11B–C

NaN propagation (IEEE 754-2019 §6.2):

| Theorem | Statement |
|---------|-----------|
| `fadd_nan_l` / `fadd_nan_r` | `a.isNaN → (fadd rm a b).isNaN` |
| `fmul_nan_l` / `fmul_nan_r` | `a.isNaN → (fmul rm a b).isNaN` |
| `fdiv_nan_l` / `fdiv_nan_r` | `a.isNaN → (fdiv rm a b).isNaN` |
| `fma_nan_a` / `fma_nan_b` / `fma_nan_c` | any NaN input → `fma` result is NaN |

Invalid operations → NaN (IEEE 754-2019 §7.2):

| Theorem | Statement |
|---------|-----------|
| `fmul_inf_zero` | `a.isInf → b.isZero → (fmul rm a b).isNaN` |
| `fmul_zero_inf` | `a.isZero → b.isInf → (fmul rm a b).isNaN` |
| `fadd_inf_opp` | `a.isInf → b.isInf → a.sign ≠ b.sign → (fadd rm a b).isNaN` |
| `fdiv_zero_zero` | `a.isZero → b.isZero → (fdiv rm a b).isNaN` |
| `fdiv_inf_inf` | `a.isInf → b.isInf → (fdiv rm a b).isNaN` |
| `fma_inf_zero` | `a.isInf → b.isZero → (fma rm a b c).isNaN` |

---

### `IEEE754.Theorems.Inf` — §11D

Infinity arithmetic (IEEE 754-2019 §6.1):

| Theorem | Statement |
|---------|-----------|
| `fadd_inf_finite` | `a.isInf → b.isFinite → (fadd rm a b).isInf ∧ sign preserved` |
| `fmul_inf_nonzero` | `a.isInf → b.isFinite → ¬b.isZero → (fmul rm a b).isInf ∧ sign = XOR` |
| `fdiv_nonzero_zero` | `a.isFinite → ¬a.isZero → b.isZero → (fdiv rm a b).isInf` |

---

### `IEEE754.Theorems.Sign` — §11E–J

**E. Sign rules (IEEE 754-2019 §6.3):**

| Theorem | Statement |
|---------|-----------|
| `fmul_sign_xor` | `(fmul rm a b).sign = (a.sign != b.sign)` (when result not NaN) |
| `fdiv_sign_xor` | `(fdiv rm a b).sign = (a.sign != b.sign)` (when result not NaN) |
| `fadd_same_sign` | Same-sign addends → same-sign non-NaN result |

**F. Commutativity:**

| Theorem | Statement |
|---------|-----------|
| `fadd_comm` | `fadd rm a b = fadd rm b a` |
| `fmul_comm` | `fmul rm a b = fmul rm b a` |

**G. Ordering (IEEE 754-2019 §5.11):**

| Theorem | Statement |
|---------|-----------|
| `flt_irrefl` | `flt a a = false` |
| `flt_asymm` | `flt a b = true → flt b a = false` |
| `flt_trans` | `flt a b → flt b c → flt a c` *(sorry)* |
| `flt_nan_l` / `flt_nan_r` | NaN comparisons return false |
| `feq_nan_l` / `feq_nan_r` | NaN equalities return false |

**H. Cancellation / additive identity:**

| Theorem | Statement |
|---------|-----------|
| `addExact_opp_cancel` | `addExact rm f (-f) = (finite sign 0 0, empty)` |
| `fsub_self_isZero` | `¬f.isNaN → (fsub rm f f).isZero` |
| `fadd_posZero_r` | `fadd rm f posZero = f` for non-NaN *(sorry)* |

**I. FMA: true single rounding (IEEE 754-2019 §5.4.1):**

| Theorem | Statement |
|---------|-----------|
| `fma_is_single_rounded` | `fma` performs a single correctly-rounded operation |
| `fmaEx_flags_eq` | exception flags from `fmaEx` match `fma` |
| `fma_ne_mul_then_add` | `fma` result may differ from `fmul` then `fadd` |

**J. Square root (IEEE 754-2019 §5.4.1):**

| Theorem | Statement |
|---------|-----------|
| `fsqrt_nan` | `f.isNaN → (fsqrt rm f).isNaN` |
| `fsqrt_neg_isNaN` | negative finite → `fsqrt` returns NaN |
| `fsqrt_negInf_isNaN` | `fsqrt(-∞)` is NaN |
| `fsqrt_posInf` | `fsqrt(+∞) = +∞` |
| `fsqrt_posZero` | `fsqrt(+0) = +0` |
| `fsqrt_negZero` | `fsqrt(-0) = -0` |
| `fsqrt_nonneg` | `¬f.isNaN → ¬f.isNegative → ¬(fsqrt rm f).isNaN` |
| `sqrtExact_false_dfSign` | `sqrtExact` always returns non-negative sign |

---

### `IEEE754.Oracle` — §12

Exported C-callable functions for hardware co-simulation (Python/ctypes, cocotb, CVDP):

**F32 (`namespace F32.Oracle`):**

```lean
@[export f32_add]          def f32_add  (a b : UInt32) (round : UInt8) : UInt32
@[export f32_sub]          def f32_sub  (a b : UInt32) (round : UInt8) : UInt32
@[export f32_mul]          def f32_mul  (a b : UInt32) (round : UInt8) : UInt32
@[export f32_div]          def f32_div  (a b : UInt32) (round : UInt8) : UInt32
@[export f32_fma]          def f32_fma  (a b c : UInt32) (round : UInt8) : UInt32
@[export f32_sqrt]         def f32_sqrt (a : UInt32) (round : UInt8) : UInt32
@[export float32_classify] def classify (a : UInt32) : UInt8
```

**F64 (`namespace F64.Oracle`):**

```lean
@[export f64_add]          def f64_add  (a b : UInt64) (round : UInt8) : UInt64
@[export f64_sub]          def f64_sub  (a b : UInt64) (round : UInt8) : UInt64
@[export f64_mul]          def f64_mul  (a b : UInt64) (round : UInt8) : UInt64
@[export f64_div]          def f64_div  (a b : UInt64) (round : UInt8) : UInt64
@[export f64_fma]          def f64_fma  (a b c : UInt64) (round : UInt8) : UInt64
@[export f64_sqrt]         def f64_sqrt (a : UInt64) (round : UInt8) : UInt64
@[export float64_classify] def classify (a : UInt64) : UInt8
```

`classify` returns: 0 = NaN, 1 = Inf, 2 = Zero, 3 = Subnormal, 4 = Normal.

Compile with `lake build IEEE754Modular` and load the shared library with:

```python
import ctypes
lib = ctypes.CDLL("./build/lib/libIEEE754Modular.so")

# F32: arguments and return value are UInt32 (c_uint32)
lib.f32_add.restype  = ctypes.c_uint32
lib.f32_add.argtypes = [ctypes.c_uint32, ctypes.c_uint32, ctypes.c_uint8]
result = lib.f32_add(0x3F800000, 0x3F800000, 0)  # 1.0 + 1.0 = 2.0

# F64: arguments and return value are UInt64 (c_uint64)
lib.f64_add.restype  = ctypes.c_uint64
lib.f64_add.argtypes = [ctypes.c_uint64, ctypes.c_uint64, ctypes.c_uint8]
result = lib.f64_add(0x3FF0000000000000, 0x3FF0000000000000, 0)  # 1.0 + 1.0 = 2.0
```

---

## Build Instructions

### Prerequisites

- [Lean 4](https://github.com/leanprover/lean4) (stable toolchain — see `lean-toolchain`)
- [Lake](https://github.com/leanprover/lake) (bundled with Lean)

> **No Mathlib dependency.** The only external import is `Std.Tactic.BVDecide`, which ships with Lean's standard library.

### Build

```bash
# Build the monolithic target (original IEEE754.lean)
lake build IEEE754

# Build the modular target
lake build IEEE754Modular

# Build both
lake build

# Check a single file
lake env lean IEEE754/Theorems/F32/Sign.lean
lake env lean IEEE754/Theorems/F64/Sign.lean
```

### Run Oracle sanity checks

The `Oracle.lean` file contains `#eval` expressions that run at build time:

```
F32:
  1.0  + 1.0  = 2.0  → 40000000
  1.5  + 1.5  = 3.0  → 40400000
  1.0  × 1.0  = 1.0  → 3f800000
  2.0  × 2.0  = 4.0  → 40800000
  2.0×3.0+4.0 = 10.0 → 41200000
  classify(1.0)       = 4 (normal)
  classify(+0)        = 2 (zero)
  classify(+∞)        = 1 (inf)
  classify(NaN)       = 0 (nan)
  classify(min_sub)   = 3 (subnormal)

F64:
  1.0  + 1.0  = 2.0  → 4000000000000000
  1.5  + 1.5  = 3.0  → 4008000000000000
  2.0  × 2.0  = 4.0  → 4010000000000000
  2.0×3.0+4.0 = 10.0 → 4024000000000000
  classify(1.0)       = 4 (normal)
  classify(+0)        = 2 (zero)
  classify(+∞)        = 1 (inf)
  classify(NaN)       = 0 (nan)
  classify(min_sub)   = 3 (subnormal)
```

---

## Hardware Oracle Interface

The `F32.Oracle` and `F64.Oracle` namespaces expose C-callable functions via Lean's `@[export]` attribute. After building the shared library, use them from Python like:

```python
import ctypes, struct

lib = ctypes.CDLL("./build/lib/libIEEE754.so")
lib.f32_add.restype = ctypes.c_uint32

def f32_bits(x: float) -> int:
    return struct.unpack("I", struct.pack("f", x))[0]

def bits_f32(b: int) -> float:
    return struct.unpack("f", struct.pack("I", b))[0]

a = f32_bits(1.5)
b = f32_bits(1.5)
result = lib.f32_add(a, b, 0)   # RNE
print(bits_f32(result))          # 3.0
```

Rounding mode encoding for the `round` parameter:

| Value | Mode |
|-------|------|
| 0 | RNE (roundTiesToEven) |
| 1 | RTZ (truncate) |
| 2 | RDN (floor) |
| 3 | RUP (ceiling) |
| 4 | RMM (roundTiesToAway) |

---

## Proof Status

Open `sorry`s — work in progress:

| Location | Theorem | What's missing |
|----------|---------|----------------|
| `Theorems/F32/Sign.lean` | `flt_trans` | Full transitivity case analysis |
| `Theorems/F32/Sign.lean` | `fadd_posZero_r` | Identity law `fadd rm f posZero = f` (multiple branches) |
| `Theorems/F64/Inf.lean` | `fdiv_nonzero_zero` | Case analysis over F64 classification (mirrors F32 proof) |
| `Theorems/F64/Sign.lean` | `flt_trans` | Full transitivity case analysis |
| `Theorems/F64/Sign.lean` | `fadd_posZero_r` | Identity law `fadd rm f posZero = f` (multiple branches) |
| `Theorems/F64/Sign.lean` | `fma_ne_mul_then_add` | Requires finding specific F64 bit patterns |

Recently closed:

| Location | Theorem | Closed |
|----------|---------|--------|
| `Theorems/F32/Codec.lean` | `encode_decode_normal` | ✅ |
| `Theorems/F32/Codec.lean` | `encode_decode_subnormal` | ✅ |
| `Theorems/F32/Props.lean` | `roundTo_idempotent` | ✅ proved via `isNormalForm` fixed-point characterisation |
| `Theorems/F32/Inf.lean` | `fmul_inf_nonzero` | ✅ sign = XOR via `mulExact_inf_nonzero` + pack case-split |
| `Theorems/F32/Inf.lean` | `fdiv_nonzero_zero` | ✅ both conjuncts; `mantIsZero` via `significand_nonzero_of_not_isZero` |
| `Theorems/F64/` | entire F64 theorem chain | ✅ Classification, Codec, NaN, Inf (partial), Sign (partial) |

All other theorems are fully proved using `bv_decide`, `bv_omega`, `native_decide`, `simp`, `omega`, and `grind`.

---

## Dependencies

| Dependency | Notes |
|------------|-------|
| Lean 4 | Stable toolchain — see `lean-toolchain` |
| `Std.Tactic.BVDecide` | Ships with Lean's standard library; the **only** external import |

No Mathlib dependency.

---

## Repository Layout

```
IEEE754/
├── .gitignore
├── README.md
├── lakefile.toml              ← Lake build config (two lib targets)
├── lake-manifest.json         ← pinned dependency versions
├── lean-toolchain             ← pinned Lean version
├── LICENSE
├── IEEE754.lean               ← monolithic original (§1–§12, untouched)
├── IEEE754Modular.lean        ← modular entry point
└── IEEE754/
    ├── Basic.lean             ← §1–3.5  types, flags, FPFormat
    ├── ExactOps.lean          ← §4–5    exact arithmetic + roundTo
    ├── Conversions.lean       ← §10     F32↔F64, F32↔Int32
    ├── Oracle.lean            ← §12     @[export] C-callable functions (F32 + F64)
    ├── F32/
    │   └── Defs.lean          ← §6–7    F32 fields, codec, arithmetic ops
    ├── F64/
    │   └── Defs.lean          ← §8–9    F64 fields, codec, arithmetic ops
    └── Theorems/
        ├── F32/
        │   ├── Classification.lean  ← §11a  exclusivity lemmas, F32Class
        │   ├── Props.lean           ← §11b  algebraic properties, roundTo lemmas
        │   ├── Codec.lean           ← §11c  encode/decode round-trip ✅
        │   ├── NaN.lean             ← §11B–C NaN propagation + invalid-op
        │   ├── Inf.lean             ← §11D  Inf arithmetic ✅
        │   └── Sign.lean            ← §11E–J sign rules, ordering, FMA, sqrt
        └── F64/
            ├── Classification.lean  ← §11a  exclusivity lemmas, F64Class ✅
            ├── Codec.lean           ← §11c  encode/decode round-trip ✅
            ├── NaN.lean             ← §11B–C NaN propagation + invalid-op ✅
            ├── Inf.lean             ← §11D  Inf arithmetic (fdiv sorry)
            └── Sign.lean            ← §11E–J sign rules, ordering, FMA, sqrt
```
