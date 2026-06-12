/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Coleman.Tower
import PadicLFunctions.Coleman.NormOperator
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

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
  TeX 2647–2649) — the engine of the inverse-limit compatibility;
* the **uniqueness** of the interpolating series (`evalPi_injective`, RJW
  lem:unique-coleman, TeX 2635–2642): a `ℤ_p`-power series is determined by its
  values `f(π_n)` for `n ≥ 1`. The argument is the source's Weierstrass one — a
  nonzero `f − g` is `p^m · u(T) · r(T)` with `u` a unit and `r` a distinguished
  polynomial (so finitely many zeros in `B(0,1)`), while the `π_n` are infinitely
  many distinct points, forcing `f = g`.

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

/-! ## Uniqueness of the interpolating series (RJW lem:unique-coleman, TeX 2635–2642)

A `ℤ_p`-power series is determined by its values at the `π_n`, `n ≥ 1`. Following
the source: a nonzero `d := f − g` factors as `p^m · u(T) · r(T)` with `u` a unit
and `r` a distinguished polynomial (Weierstrass preparation), so its zeros in
`B(0,1) ⊂ ℂ_p` are those of the polynomial `r`, finitely many; the `π_n` form an
infinite sequence of distinct points (distinct norms), so `d(π_n) = 0` for all
`n ≥ 1` forces `d = 0`. -/

/-- `(C a)(π_n) = toCp(a)` — the constant series evaluates to its (pushed-forward)
constant (`map_C` then `seriesEval_C`; no convergence needed). -/
@[simp]
theorem evalPi_C (a : ℤ_[p]) (n : ℕ) : evalPi p (PowerSeries.C a) n = toCp p a := by
  rw [evalPi, PowerSeries.map_C, seriesEval_C]

/-- The polynomial-evaluation bridge: for a *polynomial* `q : ℤ_p[X]` coerced to a
power series, `q(π_n)` (i.e. `evalPi`) is the genuine `Polynomial.eval` of the
pushed-forward polynomial `q.map toCp` at `π_n` — the convergent `tsum` collapses
to the finite sum over `range (natDegree + 1)`, with no convergence input needed. -/
private theorem evalPi_coe_polynomial (q : Polynomial ℤ_[p]) (n : ℕ) :
    evalPi p (q : PowerSeries ℤ_[p]) n = (q.map (toCp p)).eval (pi p n) := by
  rw [evalPi, ← Polynomial.polynomial_map_coe]
  set r := q.map (toCp p) with hr
  rw [seriesEval, tsum_eq_sum (s := Finset.range (r.natDegree + 1)) fun k hk => by
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt
      (by simp only [Finset.mem_range, not_lt] at hk; omega), zero_mul],
    Polynomial.eval_eq_sum_range (pi p n)]
  exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.coeff_coe]

/-- The uniformisers have *distinct norms*, hence are pairwise distinct: `n ↦ ‖π_n‖`
is injective on `n ≥ 1`. If `‖π_n‖ = ‖π_m‖` with `n < m`, then (both raised to the
strictly larger totient `φ(p^m)`) `‖π_n‖^{φ(p^m)} = p⁻¹ = ‖π_n‖^{φ(p^n)}` while
`0 < ‖π_n‖ < 1` makes the larger exponent strictly smaller — a contradiction
(`norm_pi_pow_totient` + strict monotonicity of `φ` on `p`-powers). -/
private theorem pi_norm_injective {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hnm : ‖pi p n‖ = ‖pi p m‖) : n = m := by
  by_contra hne
  wlog hlt : n < m generalizing n m
  · exact this hm hn hnm.symm (Ne.symm hne) (by omega)
  have hx0 : 0 < ‖pi p n‖ := norm_pos_iff.2 (pi_ne_zero p hn)
  have hn1 : ‖pi p n‖ ^ Nat.totient (p ^ n) = (p : ℝ)⁻¹ := norm_pi_pow_totient p hn
  have hm1 : ‖pi p n‖ ^ Nat.totient (p ^ m) = (p : ℝ)⁻¹ := by
    rw [hnm]; exact norm_pi_pow_totient p hm
  have htot : Nat.totient (p ^ n) < Nat.totient (p ^ m) := by
    rw [Nat.totient_prime_pow hp.out hn, Nat.totient_prime_pow hp.out (by omega : 0 < m)]
    exact (Nat.mul_lt_mul_right (by have := hp.out.two_le; omega : 0 < p - 1)).2
      (Nat.pow_lt_pow_right hp.out.one_lt (by omega))
  have hcontra := pow_lt_pow_right_of_lt_one₀ hx0 (norm_pi_lt_one p hn) htot
  rw [hn1, hm1] at hcontra
  exact lt_irrefl _ hcontra

/-- **`p`-power normalisation**: a nonzero `d ∈ ℤ_p⟦T⟧` is `C(p^m) · d'` for some
`m` and some `d'` with a coefficient *not* divisible by `p` (so `d' mod p ≠ 0`,
the hypothesis Weierstrass preparation needs). Here `m` is the minimal `p`-adic
valuation over the nonzero coefficients of `d`; coefficient-wise division by `p^m`
(via the dvd-witnesses, `Classical.choice`) gives `d'`, and the coefficient
realising the minimum is a unit times `p^0`, hence not divisible by `p`. -/
private theorem exists_C_pow_mul (d : PowerSeries ℤ_[p]) (hd : d ≠ 0) :
    ∃ (m : ℕ) (d' : PowerSeries ℤ_[p]),
      d = PowerSeries.C ((p : ℤ_[p]) ^ m) * d' ∧ ∃ k, ¬ (p : ℤ_[p]) ∣ coeff k d' := by
  have hex : ∃ k, coeff k d ≠ 0 := by
    by_contra h; simp only [ne_eq, not_exists, not_not] at h; exact hd (PowerSeries.ext h)
  set S : Set ℕ := {v | ∃ k, coeff k d ≠ 0 ∧ (coeff k d).valuation = v} with hS
  have hSne : S.Nonempty := by
    obtain ⟨k, hk⟩ := hex; exact ⟨(coeff k d).valuation, k, hk, rfl⟩
  set m := sInf S with hm
  obtain ⟨k₀, hk₀ne, hk₀val⟩ := Nat.sInf_mem hSne
  have hsp : ∀ (x : ℤ_[p]) (j : ℕ), (p : ℤ_[p]) ^ j ∣ x ↔
      x ∈ (Ideal.span {(p : ℤ_[p]) ^ j} : Ideal ℤ_[p]) :=
    fun _ _ => Ideal.mem_span_singleton.symm
  have hdvd : ∀ k, (p : ℤ_[p]) ^ m ∣ coeff k d := by
    intro k
    by_cases hk : coeff k d = 0
    · rw [hk]; exact dvd_zero _
    · rw [hsp, PadicInt.mem_span_pow_iff_le_valuation _ hk]; exact Nat.sInf_le ⟨k, hk, rfl⟩
  classical
  refine ⟨m, PowerSeries.mk fun k => (hdvd k).choose, PowerSeries.ext fun k => ?_, k₀, ?_⟩
  · rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← (hdvd k).choose_spec]
  · intro hdvd'
    obtain ⟨c, hc⟩ := hdvd'
    rw [PowerSeries.coeff_mk] at hc
    have hkey : coeff k₀ d = (p : ℤ_[p]) ^ (m + 1) * c := by
      rw [(hdvd k₀).choose_spec, hc, pow_succ]; ring
    have hval : m + 1 ≤ (coeff k₀ d).valuation := by
      rw [← PadicInt.mem_span_pow_iff_le_valuation _ hk₀ne, ← hsp]; exact ⟨c, hkey⟩
    omega

/-- **Uniqueness of the interpolating series** (RJW lem:unique-coleman, TeX 2635–2642):
a `ℤ_p`-power series is determined by its values at the uniformisers `π_n`, `n ≥ 1`.

Proof (the source's Weierstrass argument, TeX 2641): suppose `d := f − g ≠ 0`. By
`evalPi`-linearity (`evalPi_sub`) `d(π_n) = 0` for all `n ≥ 1`. Normalise
`d = C(p^m) · d'` with `d' mod p ≠ 0` (`exists_C_pow_mul`), then apply mathlib's
Weierstrass preparation (`exists_isWeierstrassFactorization`, available since `ℤ_p`
is a complete local ring with maximal ideal `(p)`) to factor `d' = r · u` with `r`
a distinguished (monic) polynomial and `u` a unit. Evaluating at `π_n`: the
constant `toCp(p^m) ≠ 0` and the unit value `u(π_n) ≠ 0` peel off, so the mapped
polynomial `r.map toCp ∈ ℂ_p[X]` (nonzero, being monic) vanishes at every `π_n`.
But the `π_n` (`n ≥ 1`) are infinitely many distinct points (`pi_norm_injective`),
so the polynomial has infinitely many roots, hence is zero — contradiction. -/
theorem evalPi_injective {f g : PowerSeries ℤ_[p]}
    (h : ∀ n, 1 ≤ n → evalPi p f n = evalPi p g n) : f = g := by
  by_contra hfg
  set d := f - g with hd_def
  have hd : d ≠ 0 := sub_ne_zero.2 hfg
  have hzero : ∀ n, 1 ≤ n → evalPi p d n = 0 := fun n hn => by
    rw [hd_def, evalPi_sub p f g hn, h n hn, sub_self]
  obtain ⟨m, d', hdC, k₀, hk₀⟩ := exists_C_pow_mul p d hd
  -- `d' mod p ≠ 0`: the coefficient not divisible by `p` survives the residue map
  have hres : PowerSeries.map (IsLocalRing.residue ℤ_[p]) d' ≠ 0 := by
    intro hz; apply hk₀
    have hc0 : coeff k₀ (PowerSeries.map (IsLocalRing.residue ℤ_[p]) d') = 0 := by rw [hz]; simp
    rwa [PowerSeries.coeff_map, IsLocalRing.residue_eq_zero_iff,
      PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hc0
  -- Weierstrass preparation: `d' = r · u`, `r` distinguished (monic), `u` a unit
  obtain ⟨r, u, H⟩ := PowerSeries.exists_isWeierstrassFactorization hres
  set r' := r.map (toCp p) with hr'
  have hr'ne : r' ≠ 0 := (H.isDistinguishedAt.monic.map (toCp p)).ne_zero
  -- the mapped polynomial vanishes at every `π_n`, `n ≥ 1`
  have hrooteval : ∀ n, 1 ≤ n → r'.eval (pi p n) = 0 := by
    intro n hn
    have hdfact : d = PowerSeries.C ((p : ℤ_[p]) ^ m) * ((r : PowerSeries ℤ_[p]) * u) := by
      rw [hdC, H.eq_mul]
    have heval : evalPi p d n
        = toCp p ((p : ℤ_[p]) ^ m) * (evalPi p (r : PowerSeries ℤ_[p]) n * evalPi p u n) := by
      rw [hdfact, evalPi_mul p _ _ hn, evalPi_C p, evalPi_mul p (r : PowerSeries ℤ_[p]) u hn]
    rw [hzero n hn] at heval
    have hpm : toCp p ((p : ℤ_[p]) ^ m) ≠ 0 := by
      rw [map_pow, map_natCast]; exact pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
    -- `u(π_n) ≠ 0`: `u(π_n) · u⁻¹(π_n) = 1` (`u` a unit)
    have hun : evalPi p u n ≠ 0 := by
      obtain ⟨v, hv⟩ := H.isUnit
      have hvv : (v : PowerSeries ℤ_[p]) * (↑v⁻¹ : PowerSeries ℤ_[p]) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hinv : evalPi p u n * evalPi p (↑v⁻¹ : PowerSeries ℤ_[p]) n = 1 := by
        rw [← evalPi_mul p u _ hn, ← hv, hvv, evalPi_one]
      intro h0; rw [h0, zero_mul] at hinv; exact one_ne_zero hinv.symm
    have hr0 : evalPi p (r : PowerSeries ℤ_[p]) n = 0 := by
      rcases mul_eq_zero.1 heval.symm with h1 | h2
      · exact absurd h1 hpm
      · exact (mul_eq_zero.1 h2).resolve_right hun
    rwa [evalPi_coe_polynomial p r] at hr0
  -- infinitely many distinct roots `π_{n+1}` force `r' = 0`, contradiction
  refine hr'ne (Polynomial.eq_zero_of_infinite_isRoot _
    (Set.infinite_of_injective_forall_mem (f := fun n : ℕ => pi p (n + 1)) ?_ ?_))
  · intro a b hab
    have heq := pi_norm_injective p (by omega : 1 ≤ a + 1) (by omega : 1 ≤ b + 1)
      (congrArg norm hab)
    omega
  · intro n; exact hrooteval (n + 1) (by omega)

/-! ## The evaluation/norm commuting square (T907, RJW lem:norm power series vs units)

RJW TeX 2673–2692: the diagram
```
ℤ_p⟦T⟧^×  --f ↦ f(π_{n+1})-->  𝒰_{n+1}
   |𝒩                              |N_{n+1,n}
   v                               v
ℤ_p⟦T⟧^×  --f ↦ f(π_n)------->  𝒰_n
```
commutes: `evalPi (𝒩 f) n = N_{n+1,n}(evalPi f (n+1))`. The source proves this via
the `μ_p`-product formula (not a formal identity over `ℤ_p`, replan R10.4); we take
the **determinant route** of R10.4 instead, with no Galois theory: applying the ring
hom `f ↦ f(π_{n+1})` to the *formal* digit identity
`f·(1+T)^j = Σ_i φ(M_ij)·(1+T)^i` (where `M = digitMatrix f`) and using the
`φ`-equivariance `(φ g)(π_{n+1}) = g(π_n)` (`evalPi_phi`) shows the matrix
`(evalPi (M_ij) n)_{ij}` is the matrix of multiplication-by-`y` (`y := evalPi f (n+1)`)
in the integral basis `(ξ_{n+1}^i)_{i<p}` of `𝒪_{n+1}/𝒪_n` (T903b). Hence
`N_{n+1,n}(y) = det = evalPi (det (digitMatrix f)) n = evalPi (𝒩 f) n`. No `p` odd
hypothesis is needed (the sign-bearing `levelNorm_zetaSys_pow_sub_one` is bypassed). -/

variable {p}

/-- The evaluation `f ↦ f(π_n)` bundled as a ring homomorphism `ℤ_p⟦T⟧ →+* ℂ_p`
for `n ≥ 1` (fields from the `evalPi_add`/`evalPi_mul`/`evalPi_one` pack). Bundling
is what lets `RingHom.map_det` and `map_sum` transport `det`/`Σ` through evaluation. -/
noncomputable def evalPiHom {n : ℕ} (hn : 1 ≤ n) : PowerSeries ℤ_[p] →+* ℂ_[p] where
  toFun f := evalPi p f n
  map_one' := evalPi_one p n
  map_mul' f g := evalPi_mul p f g hn
  map_zero' := by rw [evalPi, map_zero]; simp [seriesEval]
  map_add' f g := evalPi_add p f g hn

@[simp]
theorem evalPiHom_apply {n : ℕ} (hn : 1 ≤ n) (f : PowerSeries ℤ_[p]) :
    evalPiHom hn f = evalPi p f n := rfl

/-- `(1+T)^i` evaluates to `(1+π_n)^i = ξ_n^i` at `π_n` for `n ≥ 1`. -/
theorem evalPi_one_add_X_pow (i : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    evalPi p ((1 + PowerSeries.X) ^ i : PowerSeries ℤ_[p]) n = zetaSys p n ^ i := by
  rw [evalPi_pow p _ i hn, evalPi_add p _ _ hn, evalPi_one, evalPi_X,
    show (1 : ℂ_[p]) + pi p n = zetaSys p n from by rw [pi]; ring]

/-- **The evaluated digit identity** (T907 crux): applying `f ↦ f(π_{n+1})` to the
formal column identity `digitMatrix_col_isDigitDecomp` and using `φ`-equivariance
`(φ g)(π_{n+1}) = g(π_n)` (`evalPi_phi`) gives, with `y := evalPi f (n+1)`,
`y · ξ_{n+1}^j = Σ_i (evalPi (M_ij) n)·ξ_{n+1}^i`. This says the matrix
`(evalPi (M_ij) n)_{ij}` is the matrix of multiplication-by-`y` in the
`ξ_{n+1}`-power basis of `K_{n+1}/K_n`. -/
theorem evalPi_digitMatrix_col (f : PowerSeries ℤ_[p]) (j : Fin p) {n : ℕ} (hn : 1 ≤ n) :
    evalPi p f (n + 1) * zetaSys p (n + 1) ^ (j : ℕ)
      = ∑ i : Fin p, evalPi p ((digitMatrix f) i j) n * zetaSys p (n + 1) ^ (i : ℕ) := by
  have hsucc : 1 ≤ n + 1 := Nat.le_succ_of_le hn
  have hkey := congrArg (evalPiHom (p := p) hsucc) (digitMatrix_col_isDigitDecomp f j)
  rw [map_mul, map_sum, evalPiHom_apply, evalPiHom_apply,
    evalPi_one_add_X_pow (j : ℕ) hsucc] at hkey
  rw [hkey]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, evalPiHom_apply, evalPiHom_apply, evalPi_one_add_X_pow (i : ℕ) hsucc,
    evalPi_phi p _ hn, mul_comm]

/-! ### The `ξ_{n+1}`-power basis of `K_{n+1}/K_n` and `levelNorm` as a determinant

The uniformiser/root powers `(ξ_{n+1}^i)_{i<p}` are `K_n`-linearly independent
(`O_succ_digits_unique`, T903b) and there are `p = [K_{n+1}:K_n]` of them
(`finrank_K_succ`), so they form a `K_n`-basis of `K_{n+1}`
(`basisOfLinearIndependentOfCardEqFinrank`). Against this basis `levelNorm`
(`= Algebra.norm`) is the determinant of the multiplication matrix, whose entries
(by the evaluated digit identity `evalPi_digitMatrix_col` + `O_succ_digits_unique`)
are exactly the `evalPi`-images of `digitMatrix`. -/

/-- The `ξ_{n+1}^i ∈ extendScalars (K_n ≤ K_{n+1})` (`i < p`), as the basis vectors. -/
private noncomputable def zetaPow {n : ℕ} (i : Fin p) :
    IntermediateField.extendScalars (K_le_succ p n) :=
  ⟨zetaSys p (n + 1) ^ (i : ℕ),
    (IntermediateField.mem_extendScalars (K_le_succ p n)).2
      (pow_mem (zetaSys_mem_K p (n + 1)) _)⟩

@[simp]
private theorem zetaPow_coe {n : ℕ} (i : Fin p) :
    ((zetaPow (p := p) (n := n) i : IntermediateField.extendScalars (K_le_succ p n)) : ℂ_[p])
      = zetaSys p (n + 1) ^ (i : ℕ) := rfl

/-- `K_n`-linear independence of the `ξ_{n+1}`-powers (the uniqueness half of T903b,
`O_succ_digits_unique`, repackaged as `LinearIndependent`). -/
private theorem linearIndependent_zetaPow {n : ℕ} (hn : 1 ≤ n) :
    LinearIndependent (K p n) (zetaPow (p := p) (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro e he i
  -- the `ℂ_p`-projection of the relation, with `K_n`-coefficients
  have hproj : ∑ k : Fin p, ((e k : K p n) : ℂ_[p]) * zetaSys p (n + 1) ^ (k : ℕ) = 0 := by
    have := congrArg (Subtype.val) he
    rw [IntermediateField.coe_sum, ZeroMemClass.coe_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [IntermediateField.coe_smul, zetaPow_coe]; rfl
  have hzero := O_succ_digits_unique p hn (c := fun k => ((e k : K p n) : ℂ_[p]))
    (c' := fun _ => 0) (fun k => (e k).2) (fun _ => zero_mem _)
    (by simpa using hproj)
  have := congrFun hzero i
  simpa using Subtype.ext this

set_option synthInstance.maxHeartbeats 1000000 in
-- the module/basis synthesis through the nested `IntermediateField (K p n) (extendScalars …)`
-- layer (a second `IntermediateField` over `K p n`) exceeds the default budget
/-- The `ξ_{n+1}`-power `K_n`-basis of `K_{n+1}` (a `LinearIndependent` family of the
right cardinality `p = [K_{n+1}:K_n]`, `finrank_K_succ`). -/
private noncomputable def zetaBasis {n : ℕ} (hn : 1 ≤ n) :
    Module.Basis (Fin p) (K p n) (IntermediateField.extendScalars (K_le_succ p n)) :=
  have : Nonempty (Fin p) := ⟨⟨0, hp.out.pos⟩⟩
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_zetaPow (p := p) hn)
    (by rw [Fintype.card_fin, finrank_K_succ p hn])

set_option synthInstance.maxHeartbeats 1000000 in
-- nested `IntermediateField (K p n) (extendScalars …)` instance synthesis (see `zetaBasis`)
@[simp]
private theorem zetaBasis_apply {n : ℕ} (hn : 1 ≤ n) (i : Fin p) :
    zetaBasis (p := p) hn i = zetaPow (p := p) (n := n) i := by
  rw [zetaBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- `evalPi f (n+1) ∈ K_{n+1}`, packaged as an element of `extendScalars`. -/
private noncomputable def evalPiES (f : PowerSeries ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) :
    IntermediateField.extendScalars (K_le_succ p n) :=
  ⟨evalPi p f (n + 1), (IntermediateField.mem_extendScalars (K_le_succ p n)).2
    (Subring.mem_inf.1 (evalPi_mem_O p f (Nat.le_succ_of_le hn))).1⟩

set_option synthInstance.maxHeartbeats 1000000 in
-- nested `IntermediateField (K p n) (extendScalars …)` instance synthesis (see `zetaBasis`)
/-- The matrix-entry identification (T907 crux): the multiplication-by-`evalPi f (n+1)`
matrix in the `ξ_{n+1}`-power basis has entries (coerced to `ℂ_p`) exactly the
`evalPi`-images `evalPi ((digitMatrix f)_{ij}) n`. This is the evaluated digit
identity (`evalPi_digitMatrix_col`) read through `Basis.repr_sum_self` and
`O_succ_digits_unique` (the `K_n`-coordinates are unique). -/
private theorem leftMulMatrix_zetaBasis_coe (f : PowerSeries ℤ_[p]) {n : ℕ} (hn : 1 ≤ n)
    (i j : Fin p) :
    ((Algebra.leftMulMatrix (zetaBasis (p := p) hn) (evalPiES f hn) i j : K p n) : ℂ_[p])
      = evalPi p ((digitMatrix f) i j) n := by
  -- the `K_n`-element `a_ij := evalPi (M_ij) n` (integral, hence in `K_n`)
  set a : Fin p → K p n := fun i => ⟨evalPi p ((digitMatrix f) i j) n,
    (Subring.mem_inf.1 (evalPi_mem_O p _ hn)).1⟩ with ha
  -- `yes · b_j = Σ_i a_i • b_i` in extendScalars (project to ℂ_p and use the eval identity)
  have hmul : evalPiES f hn * zetaBasis (p := p) hn j
      = ∑ i : Fin p, a i • zetaBasis (p := p) hn i := by
    apply Subtype.ext
    rw [IntermediateField.coe_sum, IntermediateField.coe_mul, zetaBasis_apply, zetaPow_coe]
    change evalPi p f (n + 1) * zetaSys p (n + 1) ^ (j : ℕ) = _
    rw [evalPi_digitMatrix_col f j hn]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [IntermediateField.coe_smul, zetaBasis_apply, zetaPow_coe, ha]; rfl
  rw [Algebra.leftMulMatrix_eq_repr_mul, hmul, (zetaBasis (p := p) hn).repr_sum_self]

set_option synthInstance.maxHeartbeats 1000000 in
-- nested `IntermediateField (K p n) (extendScalars …)` instance synthesis (see `zetaBasis`)
/-- **The evaluation/norm commuting square** (T907, RJW lem:norm power series vs units,
TeX 2673–2692): for `n ≥ 1`,
`evalPi (𝒩 f) n = N_{n+1,n}(evalPi f (n+1))` — i.e. evaluating the norm operator at
`π_n` equals the level-norm of the value at `π_{n+1}`. The determinant route (R10.4):
`evalPi (𝒩 f) n = evalPi (det (digitMatrix f)) n = det ((evalPiHom).mapMatrix M)`
(`RingHom.map_det`); the mapped matrix is (entrywise, by `leftMulMatrix_zetaBasis_coe`)
the `K_n ↪ ℂ_p`-image of the multiplication-by-`evalPi f (n+1)` matrix in the
`ξ_{n+1}`-power basis, whose determinant is `Algebra.norm (= levelNorm)`. No `p`-odd
hypothesis is needed. -/
theorem evalPi_normOp (f : PowerSeries ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) :
    evalPi p (normOp f) n = levelNorm p n (evalPi p f (n + 1)) := by
  have hmem : evalPi p f (n + 1) ∈ K p (n + 1) :=
    (Subring.mem_inf.1 (evalPi_mem_O p f (Nat.le_succ_of_le hn))).1
  -- the mapped matrices agree entrywise
  have hmat : (evalPiHom (p := p) hn).mapMatrix (digitMatrix f)
      = ((K p n).val.toRingHom).mapMatrix
          (Algebra.leftMulMatrix (zetaBasis (p := p) hn) (evalPiES f hn)) := by
    ext i j
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply,
      evalPiHom_apply]
    exact (leftMulMatrix_zetaBasis_coe f hn i j).symm
  rw [normOp_eq_det, ← evalPiHom_apply hn, RingHom.map_det, hmat, ← RingHom.map_det,
    ← Algebra.norm_eq_matrix_det (zetaBasis (p := p) hn) (evalPiES f hn)]
  rw [levelNorm_apply p n hmem]
  rfl

end Coleman

end PadicLFunctions
