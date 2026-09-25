import Bench.Harness
import Grassmann

/-!
# `forms`: linear algebra of Grassmann elements

Julia twin: `oracle/bench/forms.jl` (Grassmann 0.8.46 `TensorOperator`s built from the same
SplitMix64 entries, column-major). ns per operation over a ring of `K = 64` random
operators of `ℝⁿ` (`n = 3, 4, 5, 6`: entries uniform in `[-1, 1)`, `+3` on the diagonal so
every operator is well conditioned; `exp` on entries in `[-1/2, 1/2)`), every coefficient of
every result summed into the checksum:

* `n=k/T*x`, `n=k/T*U`, `n=k/det`, `n=k/inv`, `n=k/exp`, `n=k/adjugate`, `n=k/solve` (Julia
  `value(T) \ v`, Cramer's rule), `n=k/characteristic`, `n=k/eigvals`, `n=k/outermorphism`,
  `n=k/O*M` (an outermorphism on a multivector), `n=k/compound2` (`Λ²T`), `n=k/eigen` (values
  and vectors; checksum `Σ re λ + Σ im λ + Σ |vᵢⱼ|`), `n=k/roots` (of the characteristic
  polynomial: companion eigenvalues for `n ≥ 5`), `n=k/vandermonde` (of a point list),
  `n=k/volume` (`|det T|/(n-1)!`);
* `dyadic/A\b` and `dyadic/bundle A\b`: the one performance figure the Julia docs publish
  (`docs/src/tutorials/dyadic-tensors.md:54-75`): `A\(v1+2v2+3v3+4v4+5v5)` for a `5 × 5`
  operator (72 ns there) and over a bundle of 10 000 operators (0.81 ms there).
-/

namespace Bench.Forms

open _root_.Grassmann DirectSum StaticVectors AbstractTensors Bench JuliaBase

/-- Ring size. -/
def K : Nat := 64

/-- `3.0`. -/
def f3 : Float := f64! 3.0

/-- `0.5`. -/
def fhalf : Float := f64! 0.5

/-- The sum of every coefficient (so no output of a result is dead code). -/
@[inline] def tot {n : Nat} (v : Values Float n) : Float := v.data.foldl (· + ·) 0

/-- The sum of the entries of an operator. -/
@[inline] def totOp {V W : TensorBundle} {ld lc : Layout} (T : TensorOperator V ld W lc Float) : Float :=
  tot T.mat.v

/-- `K` operators of `ℝⁿ` from a flat array of `K·n²` entries, column-major (`(i, j)` at
`k·n² + j·n + i`), `shift` added on the diagonal. -/
def ops (n : Nat) (xs : FloatArray) (shift : Float) : Array (Endomorphism (TensorBundle.euclidean n) (.chain 1) Float) :=
  (Array.range K).map fun k =>
    TensorOperator.ofFn fun i j =>
      let x := xs.get! (k * n * n + j.1 * n + i.1)
      if i.1 = j.1 then x + shift else x

/-- `K` vectors of `ℝⁿ`. -/
def vecs (n : Nat) (xs : FloatArray) : Array (Chain (TensorBundle.euclidean n) 1 Float) :=
  (Array.range K).map fun k => ⟨Values.ofFn fun i => xs.get! (k * n + i.1)⟩

/-- `K` multivectors of `ℝⁿ`. -/
def mvs (n : Nat) (xs : FloatArray) : Array (Multivector (TensorBundle.euclidean n) Float) :=
  (Array.range K).map fun k => ⟨Values.ofFn fun i => xs.get! (k * (1 <<< n) + i.1)⟩

/-- `Σ_k f(as[k])` over the ring. -/
@[specialize] def sum1 {X : Type} (f : X → Float) (as : Array X) (k : Nat) (acc : Float) : Float :=
  if h : k < as.size then sum1 f as (k + 1) (acc + f as[k]) else acc
termination_by as.size - k

/-- `Σ_k f(as[k], bs[k])` over the ring. -/
@[specialize] def sum2 {X Y : Type} (f : X → Y → Float) (as : Array X) (bs : Array Y) (k : Nat) (acc : Float) :
    Float :=
  if h : k < as.size then
    if h' : k < bs.size then sum2 f as bs (k + 1) (acc + f as[k] bs[k]) else acc
  else acc
termination_by as.size - k

/-- The eigenvalue sum `Σ re + Σ im` of a spectrum. -/
@[inline] def specSum {n : Nat} : Forms.Spectrum n → Float
  | .real v => tot v
  | .complex v => v.toList.foldl (fun acc z => acc + z.re + z.im) 0

/-- The eigen-decomposition's sign/phase-free checksum: `Σ re λ + Σ im λ + Σ |v_ij|` (the
eigenvectors are unit columns whose sign or phase differs between LAPACK and EISPACK). -/
def eigenSum {V : TensorBundle} : TensorOperator.EigenResult V → Float
  | .real S => tot S.vals + S.vecs.mat.v.data.foldl (fun acc x => acc + x.abs) 0
  | .complex S =>
    S.vals.toList.foldl (fun acc z => acc + z.re + z.im) 0 +
      S.vecs.mat.v.toList.foldl (fun acc z => acc + JuliaBase.F64.hypot z.re z.im) 0

/-- The cases of `ℝⁿ` (inlined at each literal `n`, as user code at a fixed dimension). -/
@[inline] def dimCases (n : Nat) (seed : UInt64) : BenchM Unit := do
  let p := s!"K={K}"
  let Ts := ops n (randFloats (K * n * n) seed (-1) 1) f3
  let Us := ops n (randFloats (K * n * n) (seed + 1) (-1) 1) f3
  let Es := ops n (randFloats (K * n * n) (seed + 2) (-fhalf) fhalf) 0
  let xs := vecs n (randFloats (K * n) (seed + 3) (-1) 1)
  let Ms := mvs n (randFloats (K * (1 <<< n)) (seed + 4) (-1) 1)
  let Os := Ts.map fun T => T.outermorphism
  let key := fun (s : String) => s!"n={n}/{s}"
  bench (key "T*x") (ops := K) (param := p) fun s =>
    sum2 (fun T x => tot (T * x : Chain _ 1 Float).v) (blackBox s Ts) xs 0 0
  bench (key "T*U") (ops := K) (param := p) fun s =>
    sum2 (fun T U => totOp (T * U)) (blackBox s Ts) Us 0 0
  bench (key "det") (ops := K) (param := p) fun s => sum1 (fun T => T.det) (blackBox s Ts) 0 0
  bench (key "inv") (ops := K) (param := p) fun s => sum1 (fun T => totOp T.inv) (blackBox s Ts) 0 0
  bench (key "exp") (ops := K) (param := p) fun s => sum1 (fun T => totOp T.exp) (blackBox s Es) 0 0
  bench (key "adjugate") (ops := K) (param := p) fun s => sum1 (fun T => totOp T.adjugate) (blackBox s Ts) 0 0
  bench (key "solve") (ops := K) (param := p) fun s =>
    sum2 (fun T x => tot (T.solve x).v) (blackBox s Ts) xs 0 0
  bench (key "characteristic") (ops := K) (param := p) fun s =>
    sum1 (fun T => tot T.characteristic.v) (blackBox s Ts) 0 0
  bench (key "eigvals") (ops := K) (param := p) fun s => sum1 (fun T => specSum T.eigvals) (blackBox s Ts) 0 0
  bench (key "outermorphism") (ops := K) (param := p) fun s =>
    sum1 (fun T => (T.outermorphism.blocks.foldl (fun acc b => acc + tot b.mat.v) 0)) (blackBox s Ts) 0 0
  bench (key "O*M") (ops := K) (param := p) fun s =>
    sum2 (fun O M => tot (O * M : Multivector _ Float).v) (blackBox s Os) Ms 0 0
  bench (key "compound2") (ops := K) (param := p) fun s => sum1 (fun T => totOp (T.compound 2)) (blackBox s Ts) 0 0
  bench (key "eigen") (ops := K) (param := p) fun s => sum1 (fun T => eigenSum T.eigen) (blackBox s Ts) 0 0
  bench (key "roots") (ops := K) (param := p) fun s =>
    sum1 (fun T => specSum (Forms.monicroots T.characteristic.v)) (blackBox s Ts) 0 0
  bench (key "vandermonde") (ops := K) (param := p) fun s =>
    sum1 (fun (x : Chain _ 1 Float) => totOp (Forms.vandermonde x.v)) (blackBox s xs) 0 0
  bench (key "volume") (ops := K) (param := p) fun s => sum1 (fun T => T.volume) (blackBox s Ts) 0 0

/-- The documented Cramer solve (`dyadic-tensors.md:54-75`): `A \ b` with
`b = v1+2v2+3v3+4v4+5v5` for a ring of `5 × 5` operators, and over a bundle of 10 000. -/
def dyadicCases : BenchM Unit := do
  let n := 5
  let Ts := ops n (randFloats (K * n * n) 0xD1AD (-1) 1) f3
  let b : Chain (TensorBundle.euclidean 5) 1 Float := ⟨Values.ofFn fun i => i.1.toUInt64.toFloat + 1⟩
  bench "dyadic/A\\b" (ops := K) (param := s!"K={K}") fun s =>
    sum1 (fun T => tot (T.solve b).v) (blackBox s Ts) 0 0
  let m ← size 10000 100
  let bundle := (Array.range (m / K + 1)).foldl (fun acc _ => acc ++ Ts) #[] |>.extract 0 m
  bench "dyadic/bundle A\\b" (ops := m) (param := s!"m={m}") fun s =>
    sum1 (fun T => tot (T.solve b).v) (blackBox s bundle) 0 0

/-- The suite. -/
def suite : Suite := ⟨"forms", do
  dimCases 3 0xF003
  dimCases 4 0xF004
  dimCases 5 0xF005
  dimCases 6 0xF006
  dyadicCases⟩

end Bench.Forms
