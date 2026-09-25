# Performance log

Numbers are ns/op on Apple Silicon, Lean v4.35.0-rc3 (`lake build`, default -O3 C), Julia 1.13 with
Grassmann 0.8.46. Record new measurements at the bottom with date and commit.

## 2026-09-24: storage / kernel spike (R3 full geometric product, Float)

| variant | ns/op |
|---|---|
| Julia `Multivector*Multivector` (ℝ3) | 19.8 |
| Julia `Spinor*Spinor` (ℝ3) | 15.8 |
| Lean: structure with 8 unboxed `Float` fields, unrolled | 13–15 |
| Lean: `FloatArray`, unrolled by hand | 24–29 |
| Lean: unrolled, generic over α via a storage class, specialized at Float | **26** |
| Lean: elaboration-time codegen (`gen_mul`), generic over α, @Float | **23** |
| Lean: generic struct with boxed fields, unrolled | 53 |
| Lean: boxed `Array Float`, unrolled | 61 |
| Lean: `FloatArray` table loop | 190–290 |
| Lean: flat term-list loop (`USize`, `uget`) | 400+ |
| Lean: boxed `Array Float` loop | 510–870 |

| full product, larger n | Julia | Lean codegen @Float |
|---|---|---|
| n = 5 (32×32) | 152 | 250 |
| n = 6 (64×64) | 8244 | 1189 |

Elaboration + compile cost of the generated kernels: n=3,4,5 together ≈1.3 s; n=6 ≈7 s.

Conclusions baked into DESIGN.md:
* Unrolling is mandatory; loops are 10–40× slower in compiled Lean.
* One generic kernel source serves every coefficient type. Specialization at Float yields unboxed code.
* Boxing costs ≈2×, so Float storage is `FloatArray`.
* `for … break` with `let mut` Floats boxes every Float through `ForInStep`. Measured 8× slower on a
  Mandelbrot escape loop (446 ms vs 54 ms with a tail-recursive loop). Hot Float loops must be tail-recursive.

## 2026-09-24: Julia's own scalar kernels (`JuliaBase.Math`, `lake exe bench math`)

ns per call, 10⁷ calls over a sweep of arguments, results folded into an accumulator (Julia: the
same loop, `@elapsed`, after warm-up).

| function | libm (`Float.exp`, …) | `JuliaBase` (Julia's kernel in Lean) | Julia 1.13 |
|---|---|---|---|
| `exp` | 1.8 | 6.6 | 2.6 |
| `log` | 2.0 | 8.2 | 3.1 |
| `expm1` | — | 12.4 | 3.5 |
| `log1p` | — | 9.3 | 3.3 |
| `x^2.5` | 4.7 | 22.1 | 8.6 |
| `x^7` (`pow_body`) | — | 9.0 | 2.9 |

* **Float literals can cost microseconds.** `0.9394130628134757` elaborates to
  `Float.ofScientific 9394130628134757 true 16`; the code generator normally hoists that into a
  closed term, but after inlining into a branch where the `Bool` argument is already a variable
  it leaves the call in place, and `Float.ofScientific` takes a bignum path for 17-digit mantissas
  or exponents past `10^22`. The first port of the kernels ran `F64.log` at 3 µs (exp 180 ns);
  decoding the constants at elaboration time (`f64!`/`f32!`, `JuliaBase.FloatLit`) brought it to
  8 ns. Grep the generated C for `l_Float_ofScientific` outside `_init_` functions to find
  others (`JuliaBase/Complex.lean` has about 50).
* `Int`/`Nat` arithmetic with `2 ^ 64`-style constants cost ~40 ns per conversion; the kernels use
  `Int64`/`UInt64` (`>>>` on `Int64` is arithmetic, as Julia's `>>`).
* Turning off closed-term extraction (`compiler.extract_closed false`) inlines the `f64!` bit
  patterns as immediates but is not faster: the remaining cost is the out-of-line
  `lean_float_to_bits`/`lean_float_of_bits` calls (`bl` in the disassembly), five or so per `exp`.
  Unboxed `FloatArray` tables save two of them (7.3 → 6.6 ns).
