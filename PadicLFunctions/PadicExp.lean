/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Coefficients
import PadicLFunctions.Interpolation.Branches

/-!
# The p-adic exponential and logarithm (RJW Lem 5.14)

`exp(x) = ∑ x^n/n!` converges on the open ball `‖x‖ < p^{−1/(p−1)}` of a
nonarchimedean complete normed `ℚ_[p]`-algebra field (Legendre:
`v_p(n!) = (n − s_p(n))/(p−1)`), and is an isometry there; for odd `p` the
ball contains `pℤ_p`. The logarithm `log(1+y) = ∑ (−1)^{n+1} y^n/n` converges
for `‖y‖ < 1` and inverts `exp` on the matched balls. This realises RJW
Lemma 5.14 (TeX 1892–1897, citing Cassels §12; cross-reference Washington,
*Introduction to Cyclotomic Fields* §5.1) **as stated**: for `s ∈ ℤ_p` and
`x ∈ 1 + pℤ_p`, `x^s := exp(s·log x)` — and this agrees with the character
construction `PadicInt.onePAdicPow` by uniqueness of continuous characters.

Decomposition: `.mathlib-quality/decomposition.md` §5, cluster R5.E
(E1–E5; user-requested at board approval 2026-06-10).
-/

open Filter Topology

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
  [IsUltrametricDist L] [CompleteSpace L]

/-- E1: in a complete ultrametric normed field, a family is summable iff it
tends to `0` along the cofinite filter. -/
theorem summable_iff_tendsto_cofinite_zero {ι : Type*} (f : ι → L) :
    Summable f ↔ Tendsto f Filter.cofinite (𝓝 0) := by sorry

/-- E2: the norm of `n!` in `ℚ_[p]`, via Legendre's formula
`v_p(n!) ≤ (n−1)/(p−1)` — stated rpow-free as
`p^{-(n−1)} ≤ ‖n!‖^{p−1}`. -/
theorem norm_factorial_le {n : ℕ} (hn : 1 ≤ n) :
    (p : ℝ) ^ (-((n : ℤ) - 1)) ≤ ‖(n.factorial : ℚ_[p])‖ ^ (p - 1) := by sorry

/-- Membership in the open convergence ball `‖x‖ < p^{−1/(p−1)}` of the
`p`-adic exponential, stated rpow-free: `‖x‖^{p−1} < p⁻¹`. -/
def InExpBall (p : ℕ) {L : Type*} [NormedField L] (x : L) : Prop :=
  ‖x‖ ^ (p - 1) < (p : ℝ)⁻¹

/-- E3: the `p`-adic exponential, defined as a junk-total function (the series
`∑ x^n/n!`, meaningful on `‖x‖ < expRadius p`). -/
noncomputable def padicExp (x : L) : L := ∑' n : ℕ, (n.factorial : ℚ_[p])⁻¹ • x ^ n

@[simp] theorem padicExp_zero : padicExp p (0 : L) = 1 := by sorry

/-- E3: `exp` is an isometry on the open ball `‖x‖ < p^{−1/(p−1)}` — every
term beyond the linear one is strictly smaller (strictness needs the OPEN
ball; decomposition E3 attack [3]). -/
theorem norm_padicExp_sub_padicExp {x y : L} (hx : InExpBall p x)
    (hy : InExpBall p y) :
    ‖padicExp p x - padicExp p y‖ = ‖x - y‖ := by sorry

theorem norm_padicExp_sub_one {x : L} (hx : InExpBall p x) :
    ‖padicExp p x - 1‖ = ‖x‖ := by sorry

/-- E3: the functional equation `exp(x+y) = exp(x)·exp(y)` on the ball
(double-series rearrangement; unconditional/ultrametric Fubini via
`Summable.tsum_prod`, NOT norm-summable Cauchy products). -/
theorem padicExp_add {x y : L} (hx : InExpBall p x) (hy : InExpBall p y) :
    padicExp p (x + y) = padicExp p x * padicExp p y := by sorry

/-- E4: the `p`-adic logarithm `log(x) = ∑ (−1)^{n+1}(x−1)^n/n`, junk-total
(meaningful for `‖x − 1‖ < 1`). -/
noncomputable def padicLog (x : L) : L :=
  ∑' n : ℕ, (-1 : L) ^ n * (((n : ℚ_[p]) + 1)⁻¹ • (x - 1) ^ (n + 1))

@[simp] theorem padicLog_one : padicLog p (1 : L) = 0 := by sorry

theorem norm_padicLog {x : L} (hx : InExpBall p (x - 1)) :
    ‖padicLog p x‖ = ‖x - 1‖ := by sorry

/-- E4: `exp` inverts `log` on the matched balls (series composition with
ultrametric Fubini; Washington Prop 5.3 route — decomposition E4). -/
theorem padicExp_padicLog {x : L} (hx : InExpBall p (x - 1)) :
    padicExp p (padicLog p x) = x := by sorry

theorem padicLog_padicExp {x : L} (hx : InExpBall p x) :
    padicLog p (padicExp p x) = x := by sorry

theorem padicLog_mul {x y : L} (hx : InExpBall p (x - 1))
    (hy : InExpBall p (y - 1)) :
    padicLog p (x * y) = padicLog p x + padicLog p y := by sorry

section pZp

/-- **RJW Lemma 5.14, first half** (TeX 1892–1893): "The p-adic exponential
map converges on `pℤ_p`" — for odd `p`, `pℤ_[p]` lies in the convergence ball
(`‖x‖ ≤ p⁻¹ < p^{−1/(p−1)}`). Stated on `ℤ_[p]` (the `L = ℚ_[p]`-instance
restricted to integers; `exp` of a multiple of `p` is again integral by the
isometry). -/
theorem padicExp_converges_on_pZp (hp2 : p ≠ 2) {x : ℤ_[p]}
    (hx : x ∈ Ideal.span {(p : ℤ_[p])}) :
    Summable fun n : ℕ => (n.factorial : ℚ_[p])⁻¹ • ((x : ℚ_[p]) ^ n) := by sorry

/-- The integral exponential on `pℤ_p` (odd `p`), valued in `1 + pℤ_p`. -/
noncomputable def pZpExp (x : ℤ_[p]) : ℤ_[p] := sorry

theorem pZpExp_sub_one_mem (hp2 : p ≠ 2) {x : ℤ_[p]}
    (hx : x ∈ Ideal.span {(p : ℤ_[p])}) :
    pZpExp p x - 1 ∈ Ideal.span {(p : ℤ_[p])} := by sorry

/-- The integral logarithm on `1 + pℤ_p` (odd `p`), valued in `pℤ_p`. -/
noncomputable def pZpLog (x : ℤ_[p]) : ℤ_[p] := sorry

theorem pZpLog_mem (hp2 : p ≠ 2) {x : ℤ_[p]}
    (hx : x - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    pZpLog p x ∈ Ideal.span {(p : ℤ_[p])} := by sorry

/-- **RJW Lemma 5.14, second half** (TeX 1893–1894): "for any `s ∈ ℤ_p`, the
function `1+pℤ_p → ℤ_p` given by `x ↦ x^s := exp(s·log(x))` is well-defined"
— and it agrees with the character construction `PadicInt.onePAdicPow`
(uniqueness of continuous additive characters with a given value at `1`;
decomposition E5). -/
theorem padicExp_smul_padicLog_eq_onePAdicPow (hp2 : p ≠ 2) {x : ℤ_[p]}
    (hx : x - 1 ∈ Ideal.span {(p : ℤ_[p])}) (s : ℤ_[p]) :
    pZpExp p (s * pZpLog p x) = PadicInt.onePAdicPow p x hx s := by sorry

end pZp

end PadicLFunctions
