/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Coleman.Tower

/-!
# Evaluation of `ℤ_p`-power series at the uniformisers `π_n` (RJW §9)

The evaluation-at-`π_n` layer of the Coleman map. A power series
`f ∈ ℤ_p⟦T⟧` is, in RJW §9, identified with the rigid-analytic function
`z ↦ f(z)` on the open unit ball `B(0,1) ⊂ ℂ_p` (TeX 2528–2532); its values
at the points `π_n = ξ_{p^n} − 1 ∈ B(0,1)` package the local data. We realise
this evaluation as the project's `seriesEval` (replan R10.3): the coefficients
of `f` are pushed into `ℂ_p` along `ℤ_p ↪ ℚ_p ↪ ℂ_p` and `seriesEval` sums the
resulting convergent series at `π_n`.

The deliverables (T904):

* `evalPi f n = f(π_n)` and its convergence (`summable_evalPi`, `n ≥ 1`);
* the ring-homomorphism behaviour of `f ↦ f(π_n)` at each fixed level
  (`evalPi_add`, `evalPi_sub`, `evalPi_mul`, `evalPi_one`, `evalPi_X`,
  `evalPi_pow`);
* integrality `f(π_n) ∈ 𝒪_n` (`evalPi_mem_O`);
* the `φ`-equivariance `φ(f)(π_{n+1}) = f(π_n)` (`evalPi_phi`, RJW eq. (φ-π_n),
  TeX 2647–2649) — the engine of the inverse-limit compatibility.

The single-level interpolation lemma "every norm-one `u ∈ 𝒪_n` is `f(π_n)` for
a unit `f`" (RJW TeX 2538–2547) is *deferred to* `[T904b]`: its honest
dependency is the absolute monogenicity `𝒪_n = ℤ_p[π_n]` (in flight as T903b),
from which the greedy `π_n`-adic-digit construction reads off the unit `f`.
-/

open PowerSeries
open scoped IntermediateField

namespace PadicLFunctions

namespace Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## The coefficient map `ℤ_p → ℂ_p` and `seriesEval`-shaped helpers -/

/-- The coefficient inclusion `ℤ_p → ℂ_p`, `ℤ_p ↪ ℚ_p ↪ ℂ_p` (the §7 `M`-pattern,
`(algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom`). Power-series evaluation
at `π_n` pushes a `ℤ_p`-series forward along `toCp` before summing in `ℂ_p`. -/
noncomputable def toCp : ℤ_[p] →+* ℂ_[p] :=
  (algebraMap ℚ_[p] ℂ_[p]).comp (PadicInt.Coe.ringHom)

/-- `toCp` is isometric on the unit ball: `‖toCp x‖ = ‖x‖` (the `ℚ_p ↪ ℂ_p`
extension is isometric, `PadicComplex.norm_extends'`, and `ℤ_p ↪ ℚ_p` preserves
the norm by definition). -/
theorem norm_toCp (x : ℤ_[p]) : ‖toCp p x‖ = ‖x‖ := by
  rw [toCp, RingHom.comp_apply, PadicInt.Coe.ringHom_apply, norm_algebraMap', PadicInt.norm_def]

/-- The pushed-forward coefficients are integral: `‖coeff k (map toCp f)‖ ≤ 1`
(`toCp` is isometric and `‖coeff k f‖ ≤ 1` in `ℤ_p`). -/
theorem norm_coeff_map_le_one (f : PowerSeries ℤ_[p]) (k : ℕ) :
    ‖coeff k (PowerSeries.map (toCp p) f)‖ ≤ 1 := by
  rw [PowerSeries.coeff_map, norm_toCp]
  exact PadicInt.norm_le_one _

/-- **Evaluation at `π_n`** (RJW §9, TeX 2528–2532): the value `f(π_n)` of a
`ℤ_p`-power series at the uniformiser `π_n ∈ B(0,1) ⊂ ℂ_p`, realised as the
`seriesEval` of the pushed-forward series `map toCp f`. -/
noncomputable def evalPi (f : PowerSeries ℤ_[p]) (n : ℕ) : ℂ_[p] :=
  seriesEval (PowerSeries.map (toCp p) f) (pi p n)

/-- The evaluation series converges for `n ≥ 1`: integral coefficients summed at
`‖π_n‖ < 1` (`summable_seriesEval_of_norm_coeff_le_one`). -/
theorem summable_evalPi (f : PowerSeries ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) :
    Summable fun k => coeff k (PowerSeries.map (toCp p) f) * pi p n ^ k :=
  summable_seriesEval_of_norm_coeff_le_one (norm_coeff_map_le_one p f)
    (norm_pi_lt_one p hn)

/-! ## Ring-homomorphism behaviour of `f ↦ f(π_n)` at each level

For each fixed `n ≥ 1`, `f ↦ f(π_n)` is a ring homomorphism `ℤ_p⟦T⟧ → ℂ_p`:
`map toCp` is a ring hom and `seriesEval` is additive/multiplicative on series
whose evaluations converge (which they do, at `‖π_n‖ < 1`, by `summable_evalPi`).
-/

/-- `(f + g)(π_n) = f(π_n) + g(π_n)` for `n ≥ 1`. -/
theorem evalPi_add (f g : PowerSeries ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) :
    evalPi p (f + g) n = evalPi p f n + evalPi p g n := by
  rw [evalPi, evalPi, evalPi, map_add,
    seriesEval_add (summable_evalPi p f hn) (summable_evalPi p g hn)]

/-- `(f − g)(π_n) = f(π_n) − g(π_n)` for `n ≥ 1`. -/
theorem evalPi_sub (f g : PowerSeries ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) :
    evalPi p (f - g) n = evalPi p f n - evalPi p g n := by
  rw [evalPi, evalPi, evalPi, map_sub,
    seriesEval_sub (summable_evalPi p f hn) (summable_evalPi p g hn)]

/-- `(f · g)(π_n) = f(π_n) · g(π_n)` for `n ≥ 1` (nonarchimedean Cauchy product). -/
theorem evalPi_mul (f g : PowerSeries ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) :
    evalPi p (f * g) n = evalPi p f n * evalPi p g n := by
  rw [evalPi, evalPi, evalPi, map_mul,
    seriesEval_mul (summable_evalPi p f hn) (summable_evalPi p g hn)]

/-- `(1)(π_n) = 1` (`map toCp 1 = 1`, `seriesEval (C 1) = 1`). -/
@[simp]
theorem evalPi_one (n : ℕ) : evalPi p (1 : PowerSeries ℤ_[p]) n = 1 := by
  rw [evalPi, map_one, show (1 : PowerSeries ℂ_[p]) = PowerSeries.C (1 : ℂ_[p]) from
    (map_one _).symm, seriesEval_C]

/-- `(X)(π_n) = π_n` (the monomial `X` peels to its single nonzero term). -/
@[simp]
theorem evalPi_X (n : ℕ) : evalPi p (PowerSeries.X : PowerSeries ℤ_[p]) n = pi p n := by
  rw [evalPi, PowerSeries.map_X, seriesEval, tsum_eq_single 1 fun k hk => by
    rw [PowerSeries.coeff_X, if_neg hk, zero_mul],
    PowerSeries.coeff_one_X, one_mul, pow_one]

/-- `(f^k)(π_n) = f(π_n)^k` for `n ≥ 1` (induction via `evalPi_mul`). -/
theorem evalPi_pow (f : PowerSeries ℤ_[p]) (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    evalPi p (f ^ k) n = evalPi p f n ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, evalPi_one]
  | succ m ih => rw [pow_succ, pow_succ, evalPi_mul p _ f hn, ih]

/-! ## Integrality `f(π_n) ∈ 𝒪_n` -/

/-- `K_n` is finite-dimensional over `ℚ_p` (`ξ_{p^n}` is integral, being a root of
unity, so `ℚ_p(ξ_{p^n})` is a finite extension). Re-derived locally via
`adjoin.finiteDimensional` (the Tower instance is private). -/
private theorem finiteDimensional_K (n : ℕ) : FiniteDimensional ℚ_[p] (K p n) := by
  have hint : IsIntegral ℚ_[p] (zetaSys p n) :=
    ((zetaSys_primitiveRoot p n).isIntegral (pow_pos hp.out.pos n)).tower_top
  exact IntermediateField.adjoin.finiteDimensional hint

/-- `K_n` is closed in `ℂ_p`: a finite-dimensional `ℚ_p`-subspace of a normed space
over the complete field `ℚ_p` is complete, hence closed
(`Submodule.closed_of_finiteDimensional` on `(K_n).toSubmodule`). -/
private theorem isClosed_K (n : ℕ) : IsClosed (X := ℂ_[p]) (K p n : Set ℂ_[p]) := by
  haveI : FiniteDimensional ℚ_[p] (K p n).toSubmodule := finiteDimensional_K p n
  exact (K p n).toSubmodule.closed_of_finiteDimensional

/-- The partial sums of the evaluation series lie in `K_n`: each coefficient is an
`algebraMap ℚ_[p] ℂ_[p]`-image (hence in the `ℚ_p`-intermediate-field `K_n`), each
`π_n^k ∈ K_n`, and `K_n` is closed under finite sums and products. -/
private theorem evalPi_partialSum_mem_K (f : PowerSeries ℤ_[p]) (n m : ℕ) :
    (∑ k ∈ Finset.range m, coeff k (PowerSeries.map (toCp p) f) * pi p n ^ k) ∈ K p n := by
  refine sum_mem fun k _ => mul_mem ?_ (pow_mem (pi_mem_K p n) k)
  rw [PowerSeries.coeff_map, toCp, RingHom.comp_apply]
  exact IntermediateField.algebraMap_mem (K p n) _

/-- **Integrality** (RJW §9): `f(π_n) ∈ 𝒪_n` for `n ≥ 1`. Two halves:
`‖f(π_n)‖ ≤ 1` (ultrametric `tsum` bound, each term `‖coeff_k · π_n^k‖ ≤ 1`) and
`f(π_n) ∈ K_n` (limit of the `K_n`-valued partial sums, `K_n` being closed). -/
theorem evalPi_mem_O (f : PowerSeries ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) :
    evalPi p f n ∈ O p n := by
  rw [O, Subring.mem_inf]
  refine ⟨?_, ?_⟩
  · -- `f(π_n) ∈ K_n`: limit of `K_n`-valued partial sums in the closed set `K_n`
    refine (isClosed_K p n).mem_of_tendsto
      ((summable_evalPi p f hn).hasSum.tendsto_sum_nat) ?_
    exact Filter.Eventually.of_forall fun m => evalPi_partialSum_mem_K p f n m
  · -- `‖f(π_n)‖ ≤ 1`: ultrametric bound on the `tsum`
    rw [evalPi, seriesEval]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le fun k => ?_
    rw [norm_mul, norm_pow]
    calc ‖coeff k (PowerSeries.map (toCp p) f)‖ * ‖pi p n‖ ^ k
        ≤ 1 * 1 :=
          mul_le_mul (norm_coeff_map_le_one p f k)
            (pow_le_one₀ (norm_nonneg _) (norm_pi_lt_one p hn).le) (by positivity) zero_le_one
      _ = 1 := by rw [one_mul]

/-! ## The `φ`-equivariance `φ(f)(π_{n+1}) = f(π_n)` -/

/-- The value identity behind the `φ`-step: `(1 + π_{n+1})^p − 1 = π_n`.
`1 + π_{n+1} = ξ_{p^{n+1}}` (uniformiser definition), `ξ_{p^{n+1}}^p = ξ_{p^n}`
(the compatible system, `zetaSys_pow_p`), so the value is `ξ_{p^n} − 1 = π_n`. -/
private theorem one_add_pi_pow_sub_one (n : ℕ) :
    (1 + pi p (n + 1)) ^ p - 1 = pi p n := by
  rw [pi, pi, show (1 : ℂ_[p]) + (zetaSys p (n + 1) - 1) = zetaSys p (n + 1) by ring,
    zetaSys_pow_p]

/-- **`φ`-equivariance** (RJW eq. (φ-π_n), TeX 2647–2649): `φ(f)(π_{n+1}) = f(π_n)`,
where `φ : ℤ_p⟦T⟧ → ℤ_p⟦T⟧` is the Frobenius substitution `f ↦ f((1+T)^p − 1)`
(`phiSeries`). This is the engine of the inverse-limit compatibility of the
Coleman map.

Proof: `map toCp` commutes with `φ` (`map_phiSeries`), so the LHS is the `seriesEval`
of `φ(map toCp f)` at `π_{n+1}`; the `K`-native `φ`-bridge
(`seriesEval_phi_of_summable_prod`) rewrites this as the evaluation of `map toCp f`
at `(1 + π_{n+1})^p − 1 = π_n` (`one_add_pi_pow_sub_one`), which is `f(π_n)`. -/
theorem evalPi_phi (f : PowerSeries ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) :
    evalPi p (phiSeries p f) (n + 1) = evalPi p f n := by
  have hnf := norm_coeff_map_le_one p f
  have hzlt : ‖pi p (n + 1)‖ < 1 := norm_pi_lt_one p (by omega)
  rw [evalPi, map_phiSeries,
    seriesEval_phi_of_summable_prod p (PowerSeries.map (toCp p) f) (pi p (n + 1))
      (summable_prod_of_norm_coeff_le_one p hnf hzlt),
    one_add_pi_pow_sub_one]
  rfl

end Coleman

end PadicLFunctions
