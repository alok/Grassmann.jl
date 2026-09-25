/-
Dimension counts (Julia `AbstractTensors.mdims`, `tdims`, `gdims`, AT:161-181).

`gdims n g` is the binomial coefficient, defined by the multiplicative
recurrence `C(n, k+1) = C(n, k)·(n-k)/(k+1)` with **structural** recursion on
`k`, so the kernel evaluates it with its GMP-accelerated `Nat.mul`/`Nat.div`
(Pascal's recursion would be exponential under `decide`). It is `0` for
`k > n` automatically, which is Julia's `binomial(n, k)` convention
(`gdims(4,5) == 0`).
-/

namespace AbstractTensors

/-- Binomial coefficient `n choose k` (Julia `Base.binomial`, AT:181 `gdims(N,G)`),
multiplicative and structural in `k`. -/
def gdims (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => gdims n k * (n - k) / (k + 1)

/-- Julia `tdims(n) = 1 << n`: the dimension `2ⁿ` of the full algebra (AT:170-172). -/
def tdims (n : Nat) : Nat := 2 ^ n

/-- Julia `mdims(M::Int) = M` (AT:163). Tensor types go through
`TensorAlgebra.mdims` (`AbstractTensors.Ops`). -/
def mdimsNat (n : Nat) : Nat := n

/-- `Σ_{g ≤ k} gdims n g`, structural in `k`. -/
def gdimsSum (n : Nat) : Nat → Nat
  | 0 => gdims n 0
  | k + 1 => gdimsSum n k + gdims n (k + 1)

example : gdims 4 2 = 6 := by decide
example : gdims 4 5 = 0 := by decide
example : gdims 3 3 = 1 := by decide
example : gdims 0 0 = 1 := by decide
example : gdims 20 10 = 184756 := by decide
example : gdims 64 32 = 1832624140942590534 := by decide
example : tdims 3 = 8 := by decide

/-- `Σ_g gdims n g = tdims n` (the grade decomposition of the full algebra),
checked by the kernel for every `n ≤ 12`. -/
theorem gdimsSum_eq_tdims : ∀ n, n ≤ 12 → gdimsSum n n = tdims n := by decide

/-- `gdims n g = gdims n (n - g)` (complement casts), checked for `n ≤ 12`. -/
theorem gdims_symm_small : ∀ n, n ≤ 12 → ∀ g, g ≤ n → gdims n g = gdims n (n - g) := by decide

end AbstractTensors
