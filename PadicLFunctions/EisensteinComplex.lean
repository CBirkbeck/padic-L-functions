/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import PadicLFunctions.EisensteinFamily
import PadicLFunctions.KubotaLeopoldt.ZetaValuesComplex

/-!
# The q-expansion of the p-stabilised Eisenstein series (RJW §8, complex side)

RJW TeX 2367–2394: the normalised Eisenstein series
`E_k = ζ(1−k)/2 + Σ_{n≥1} σ_{k−1}(n)qⁿ` and its p-stabilisation
`E_k^{(p)}(z) = E_k(z) − p^{k−1}E_k(pz)`, whose q-expansion is the
"easy check" `E_k^{(p)} = (1−p^{k−1})ζ(1−k)/2 + Σ σ^p_{k−1}(n)qⁿ`
(TeX 2391). Mathlib supplies the level-1 q-expansion
(`EisensteinSeries.q_expansion_bernoulli`, `E_qExpansion_coeff`) in the
constant-term-1 normalisation; RJW's `E_k` is `(ζ(1−k)/2)·E` via
`riemannZeta_neg_nat_eq_bernoulli`/`zetaNeg_eq_riemannZeta`.

Deferred (plan.md §8): the Γ₀(p)-modularity of `E_k^{(p)}` (a remark in the
source, TeX 2394, no proof given) — mathlib has no level-raising/`V_p`
operator.
-/

open Complex EisensteinSeries UpperHalfPlane

open scoped MatrixGroups Real

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]

section sigmaArithmetic

/-- For `p ∤ n` the prime-to-`p` divisor sum is the full divisor sum:
`σ^p_k(n) = σ_k(n)`. -/
theorem sigmaP_eq_of_not_dvd {n : ℕ} (hn : ¬ (p : ℕ) ∣ n) (k : ℕ) :
    sigmaP p k n = ArithmeticFunction.sigma k n := by sorry

/-- For `p ∣ n` (RJW's "easy check", TeX 2390–2393, subtraction-free form):
`σ^p_k(n) + p^k·σ_k(n/p) = σ_k(n)` — the divisors of `n` split into the
prime-to-`p` ones and `p` times the divisors of `n/p`. -/
theorem sigmaP_add_pow_mul_sigma_div {n : ℕ} (hn : (p : ℕ) ∣ n) (hn0 : n ≠ 0)
    (k : ℕ) :
    sigmaP p k n + p ^ k * ArithmeticFunction.sigma k (n / p)
      = ArithmeticFunction.sigma k n := by sorry

end sigmaArithmetic

section stabilisation

/-- The point `p·z` of the upper half-plane (positive real scaling). -/
noncomputable def pScale (z : ℍ) : ℍ :=
  ⟨(p : ℂ) * z, by sorry⟩

/-- RJW's normalisation of the Eisenstein series (TeX 2371):
`E_k = ζ(1−k)/2 + Σ_{n≥1}σ_{k−1}(n)qⁿ`, i.e. `(ζ(1−k)/2)·E` for mathlib's
constant-term-1 normalised `ModularForm.E`. -/
noncomputable def rjwEisenstein {k : ℕ} (hk : 3 ≤ k) : ℍ → ℂ := fun z =>
  (((zetaNeg (k - 1) : ℚ) : ℂ) / 2) * ModularForm.E hk z

/-- **RJW TeX 2387–2393** (the p-stabilisation and its q-expansion): for even
`k ≥ 4` and every `z ∈ ℍ`, the series `Σ_n stabilisedCoeff(k,n)·qⁿ` with
`q = e^{2πiz}` sums to `E_k^{(p)}(z) = E_k(z) − p^{k−1}E_k(pz)` (in RJW's
normalisation). The coefficients: constant term `(1−p^{k−1})ζ(1−k)/2`,
`n`-th term `σ^p_{k−1}(n)`. -/
theorem hasSum_stabilisedEisenstein {k : ℕ} (hk : 4 ≤ k) (hk2 : Even k)
    (z : ℍ) :
    HasSum
      (fun n : ℕ => ((stabilisedCoeff p k n : ℚ) : ℂ)
        * Complex.exp (2 * Real.pi * Complex.I * (z : ℂ)) ^ n)
      (rjwEisenstein (k := k) (by omega) z
        - (p : ℂ) ^ (k - 1) * rjwEisenstein (k := k) (by omega) (pScale p z)) := by
  sorry

end stabilisation

end PadicLFunctions
