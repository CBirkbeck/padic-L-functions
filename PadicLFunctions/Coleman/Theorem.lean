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

* the **single-level interpolation** lemma (`exists_evalPi_eq`, RJW TeX 2538–2547,
  T904b): every norm-one `u ∈ 𝒪_n` is `f(π_n)` for a unit `f ∈ ℤ_p⟦T⟧^×`. The
  source's greedy `π_n`-adic-digit construction: the residue step
  `∀ x ∈ 𝒪_n, ∃ a : ℤ_p, ‖x − a‖ ≤ ‖π_n‖` (total ramification ⟹ residue field
  `𝔽_p`) is realised here via the orthogonal `ℚ_p`-power expansion at the
  uniformiser (`K_n = ℚ_p(π_n)`, `{π_n^i}_{i<φ(p^n)}` orthogonal), then a
  `Nat.rec` digit recursion `f = Σ a_k T^k` with telescoping convergence
  `‖u − Σ_{j<m} a_j π_n^j‖ ≤ ‖π_n‖^m → 0`; `f` is a unit since `‖a_0‖ = ‖u‖ = 1`.
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

/-! ## Single-level interpolation (RJW TeX 2538–2547, T904b)

Every norm-one `u ∈ 𝒪_n` is the value `f(π_n)` of a unit power series. The source's
greedy `π_n`-adic-digit construction (TeX 2542–2547): choose `a_0 ∈ ℤ_p` with
`a_0 ≡ u mod π_n`, then `a_1 ∈ ℤ_p` with `a_1 ≡ (u − a_0)/π_n mod π_n`, and so on;
`f(T) = Σ a_k T^k`. The crux is the **residue step** `∀ x ∈ 𝒪_n, ∃ a : ℤ_p,
‖x − a‖ ≤ ‖π_n‖` (`K_{n}/ℚ_p` is totally ramified, so `𝒪_n/(π_n) ≅ 𝔽_p` and `ℤ_p`
surjects onto it), which we realise via the orthogonal `ℚ_p`-power-basis expansion at
the uniformiser: `K_n = ℚ_p(π_n)`, the powers `{π_n^i}_{i<φ(p^n)}` are an orthogonal
basis (`‖Σ q_i π_n^i‖ = max_i ‖q_i‖·‖π_n‖^i`, the term norms being pairwise distinct
since `‖q_i‖ ∈ p^ℤ` and `‖π_n‖^{φ(p^n)} = p⁻¹` pin the exponent `i` mod `φ(p^n)`);
`‖x‖ ≤ 1` then forces the constant coefficient `q_0 ∈ ℤ_p` and the tail
`Σ_{i≥1} q_i π_n^i` to have norm `≤ ‖π_n‖`. -/

/-- The remainder of the greedy step stays in `𝒪_n`: if `r ∈ 𝒪_n` and `a : ℤ_p`
satisfies `‖r − a‖ ≤ ‖π_n‖`, then `(r − a)/π_n ∈ 𝒪_n` (`K_n`-membership since `K_n`
is a field and `π_n ≠ 0`; `‖·‖ ≤ 1` since `‖r − a‖ ≤ ‖π_n‖`). -/
private theorem quot_mem_O {n : ℕ} (hn : 1 ≤ n) {r : ℂ_[p]} (hr : r ∈ O p n) (a : ℤ_[p])
    (hres : ‖r - toCp p a‖ ≤ ‖pi p n‖) : (r - toCp p a) / pi p n ∈ O p n := by
  rw [O, Subring.mem_inf]
  have hrK : r ∈ K p n := (Subring.mem_inf.1 hr).1
  have htoCpaK : toCp p a ∈ K p n := by
    rw [toCp, RingHom.comp_apply, PadicInt.Coe.ringHom_apply]
    exact IntermediateField.algebraMap_mem (K p n) _
  refine ⟨(K p n).div_mem (sub_mem hrK htoCpaK) (pi_mem_K p n), ?_⟩
  change ‖(r - toCp p a) / pi p n‖ ≤ 1
  rw [norm_div, div_le_one (by rw [norm_pos_iff]; exact pi_ne_zero p hn)]
  exact hres

/-- A single term `‖q‖·‖π_n‖^i` of the orthogonal expansion (`q : ℚ_p`, `1 ≤ i < φ(p^n)`)
that is `≤ 1` is in fact `≤ ‖π_n‖`. Raising to the totient `M = φ(p^n)` and using
`‖q‖ = p^{-v}` (`v ∈ ℤ`) and `‖π_n‖^M = p⁻¹`, the inequality reads `Mv + i ≥ 0`; since
`1 ≤ i < M` this forces `v ≥ 0`, hence `Mv + i ≥ 1`, i.e. `‖q‖·‖π_n‖^i ≤ ‖π_n‖`. -/
private theorem term_norm_le_pi {n : ℕ} (hn : 1 ≤ n) (q : ℚ_[p]) {i : ℕ}
    (hi1 : 1 ≤ i) (hiM : i < Nat.totient (p ^ n)) (hle : ‖q‖ * ‖pi p n‖ ^ i ≤ 1) :
    ‖q‖ * ‖pi p n‖ ^ i ≤ ‖pi p n‖ := by
  set M := Nat.totient (p ^ n) with hM
  have hMpos : 0 < M := Nat.totient_pos.2 (pow_pos hp.out.pos n)
  have hqpM : ‖pi p n‖ ^ M = (p : ℝ)⁻¹ := norm_pi_pow_totient p hn
  have hpgt1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hqpos : 0 < ‖pi p n‖ := norm_pos_iff.2 (pi_ne_zero p hn)
  rcases eq_or_ne q 0 with hq0 | hq0
  · rw [hq0, norm_zero, zero_mul]; exact hqpos.le
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ‖q‖ = (p:ℝ) ^ k := ⟨-q.valuation, Padic.norm_eq_zpow_neg_valuation hq0⟩
  have hpos : (0:ℝ) ≤ ‖q‖ * ‖pi p n‖ ^ i := by positivity
  have hraiseM : (‖q‖ * ‖pi p n‖ ^ i) ^ M ≤ 1 := by
    calc (‖q‖ * ‖pi p n‖ ^ i) ^ M ≤ 1 ^ M := pow_le_pow_left₀ hpos hle M
      _ = 1 := one_pow _
  rw [mul_pow] at hraiseM
  have hqM : ‖q‖ ^ M = (p:ℝ) ^ (k * M) := by rw [hk, ← zpow_natCast ((p:ℝ)^k) M, ← zpow_mul]
  have hpiM : (‖pi p n‖ ^ i) ^ M = (p:ℝ) ^ (-(i:ℤ)) := by
    rw [← pow_mul, mul_comm i M, pow_mul, hqpM, ← zpow_natCast ((p:ℝ)⁻¹) i, inv_zpow, ← zpow_neg]
  rw [hqM, hpiM, ← zpow_add₀ hp0.ne'] at hraiseM
  have hle0 : k * M + (-(i:ℤ)) ≤ 0 := by
    by_contra h; push Not at h
    exact absurd hraiseM (not_le.2 (one_lt_zpow₀ hpgt1 (by omega)))
  have hkle : k ≤ 0 := by nlinarith [hle0, (by exact_mod_cast hMpos : (0:ℤ) < M), hiM]
  have hexp_le : k * M + (-(i:ℤ)) ≤ -1 := by
    nlinarith [hkle, (by exact_mod_cast hMpos : (0:ℤ) < M), hi1]
  have hterm_M : (‖q‖ * ‖pi p n‖ ^ i) ^ M ≤ ‖pi p n‖ ^ M := by
    rw [mul_pow, hqM, hpiM, ← zpow_add₀ hp0.ne', hqpM, show ((p:ℝ)⁻¹) = (p:ℝ) ^ (-1 : ℤ) by
      rw [zpow_neg_one]]
    exact zpow_le_zpow_right₀ hpgt1.le hexp_le
  exact le_of_pow_le_pow_left₀ hMpos.ne' hqpos.le hterm_M

/-- Two distinct terms of the orthogonal expansion with nonzero `ℚ_p`-coefficients have
*distinct* norms (the orthogonality input). Raising to `M = φ(p^n)`, `‖q_a‖·‖π_n‖^a` and
`‖q_b‖·‖π_n‖^b` become `p^{M v_a − a}` and `p^{M v_b − b}`; equality forces
`(v_a − v_b)·M = a − b`, impossible for `a ≠ b` with `|a − b| < M`. -/
private theorem term_norm_distinct {n : ℕ} (hn : 1 ≤ n) {qa qb : ℚ_[p]} {a b : ℕ}
    (ha : a < Nat.totient (p ^ n)) (hb : b < Nat.totient (p ^ n)) (hab : a ≠ b)
    (hqa : qa ≠ 0) (hqb : qb ≠ 0) :
    ‖qa‖ * ‖pi p n‖ ^ a ≠ ‖qb‖ * ‖pi p n‖ ^ b := by
  set M := Nat.totient (p ^ n) with hM
  have hMpos : 0 < M := Nat.totient_pos.2 (pow_pos hp.out.pos n)
  have hqpM : ‖pi p n‖ ^ M = (p : ℝ)⁻¹ := norm_pi_pow_totient p hn
  have hpgt1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  intro heqn
  have hraise : (‖qa‖ * ‖pi p n‖ ^ a) ^ M = (‖qb‖ * ‖pi p n‖ ^ b) ^ M := by rw [heqn]
  rw [mul_pow, mul_pow] at hraise
  obtain ⟨ka, hka⟩ : ∃ k : ℤ, ‖qa‖ = (p:ℝ) ^ k :=
    ⟨-qa.valuation, Padic.norm_eq_zpow_neg_valuation hqa⟩
  obtain ⟨kb, hkb⟩ : ∃ k : ℤ, ‖qb‖ = (p:ℝ) ^ k :=
    ⟨-qb.valuation, Padic.norm_eq_zpow_neg_valuation hqb⟩
  have hqaM : ‖qa‖ ^ M = (p : ℝ) ^ (ka * M) := by
    rw [hka, ← zpow_natCast ((p : ℝ) ^ ka) M, ← zpow_mul]
  have hqbM : ‖qb‖ ^ M = (p : ℝ) ^ (kb * M) := by
    rw [hkb, ← zpow_natCast ((p : ℝ) ^ kb) M, ← zpow_mul]
  have hpaa : (‖pi p n‖ ^ a) ^ M = (p : ℝ) ^ (-(a : ℤ)) := by
    rw [← pow_mul, mul_comm a M, pow_mul, hqpM, ← zpow_natCast ((p : ℝ)⁻¹) a, inv_zpow, ← zpow_neg]
  have hpbb : (‖pi p n‖ ^ b) ^ M = (p : ℝ) ^ (-(b : ℤ)) := by
    rw [← pow_mul, mul_comm b M, pow_mul, hqpM, ← zpow_natCast ((p : ℝ)⁻¹) b, inv_zpow, ← zpow_neg]
  rw [hqaM, hpaa, hqbM, hpbb, ← zpow_add₀ hp0.ne', ← zpow_add₀ hp0.ne'] at hraise
  have hexp : ka * M + (-(a : ℤ)) = kb * M + (-(b : ℤ)) :=
    zpow_right_injective₀ hp0 (ne_of_gt hpgt1) hraise
  have hfactor : (ka - kb) * M = (a : ℤ) - b := by ring_nf; linarith [hexp]
  have hMz : (0 : ℤ) < M := by exact_mod_cast hMpos
  have hbnd : |((a:ℤ) - b)| < M := by rw [abs_lt]; omega
  rcases eq_or_ne (ka - kb) 0 with h0 | h0
  · rw [h0, zero_mul] at hfactor; omega
  · exfalso
    have hge : (M : ℤ) ≤ |(ka - kb) * M| := by
      rw [abs_mul, abs_of_pos hMz]
      calc (M : ℤ) = 1 * M := (one_mul _).symm
        _ ≤ |ka - kb| * M := mul_le_mul_of_nonneg_right (Int.one_le_abs h0) hMz.le
    rw [hfactor] at hge; omega

set_option synthInstance.maxHeartbeats 1000000 in
-- the `adjoin.powerBasis`/`Basis.sum_repr` computation runs through the
-- `IntermediateField.adjoin ℚ_[p] {π_n}` power-basis layer; instance synthesis and the
-- power-basis term elaboration exceed the defaults
set_option maxHeartbeats 1000000 in
/-- **The residue step** (RJW TeX 2542–2547): every `x ∈ 𝒪_n` is `≡ a mod π_n·𝒪_n`
for some `a : ℤ_p` — i.e. `‖x − a‖ ≤ ‖π_n‖`. Total ramification gives `𝒪_n/(π_n) ≅ 𝔽_p`
and `ℤ_p ↠ 𝔽_p`; we realise this through the orthogonal `ℚ_p`-power expansion at the
uniformiser. Writing `x = ∑_{i<φ(p^n)} q_i π_n^i` against the power basis of
`K_n = ℚ_p(π_n)` (`q_i ∈ ℚ_p`), the terms have pairwise distinct norms
(`term_norm_distinct`), so orthogonality gives `‖x‖ = max_i ‖q_i π_n^i‖`; from `‖x‖ ≤ 1`
the constant coefficient has `‖q_0‖ ≤ 1` (so `a := q_0 ∈ ℤ_p`) and each higher term has
norm `≤ ‖π_n‖` (`term_norm_le_pi`), whence `‖x − a‖ = ‖∑_{i≥1} q_i π_n^i‖ ≤ ‖π_n‖`. -/
private theorem exists_residue_pi {n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]} (hx : x ∈ K p n)
    (hxnorm : ‖x‖ ≤ 1) :
    ∃ a : ℤ_[p], ‖x - toCp p a‖ ≤ ‖pi p n‖ := by
  classical
  have hKeq : ℚ_[p]⟮pi p n⟯ = K p n := by
    rw [K]; apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact sub_mem (IntermediateField.mem_adjoin_simple_self _ _) (one_mem _)
    · rw [IntermediateField.adjoin_le_iff]; intro y hy
      rw [Set.mem_singleton_iff] at hy; subst hy
      rw [show zetaSys p n = pi p n + 1 by rw [pi]; ring]
      exact add_mem (IntermediateField.mem_adjoin_simple_self _ _) (one_mem _)
  have hint : IsIntegral ℚ_[p] (pi p n) := by
    rw [pi]; exact (((zetaSys_primitiveRoot p n).isIntegral (pow_pos hp.out.pos n)).tower_top).sub
      isIntegral_one
  set pb := IntermediateField.adjoin.powerBasis hint with hpb
  set xes : ℚ_[p]⟮pi p n⟯ := ⟨x, hKeq ▸ hx⟩ with hxes
  set q : Fin pb.dim → ℚ_[p] := fun i => pb.basis.repr xes i with hq
  have hgen : (pb.gen : ℂ_[p]) = pi p n := by rw [hpb, IntermediateField.adjoin.powerBasis_gen]; rfl
  have hdim : pb.dim = Nat.totient (p ^ n) := by
    rw [hpb, IntermediateField.adjoin.powerBasis_dim, ← IntermediateField.adjoin.finrank hint,
      show Module.finrank ℚ_[p] ℚ_[p]⟮pi p n⟯ = Module.finrank ℚ_[p] (K p n) from by rw [hKeq],
      finrank_K]
  have hdimpos : 0 < pb.dim := by rw [hdim]; exact Nat.totient_pos.2 (pow_pos hp.out.pos n)
  have hbasis_coe :
      ∀ i : Fin pb.dim, ((pb.basis i : ℚ_[p]⟮pi p n⟯) : ℂ_[p]) = (pi p n) ^ (i:ℕ) := by
    intro i
    rw [PowerBasis.coe_basis,
      show ((pb.gen ^ (i:ℕ) : ℚ_[p]⟮pi p n⟯) : ℂ_[p]) = ((pb.gen : ℂ_[p])) ^ (i:ℕ) from by
        push_cast; ring, hgen]
  set tm : Fin pb.dim → ℂ_[p] := fun i => algebraMap ℚ_[p] ℂ_[p] (q i) * (pi p n) ^ (i:ℕ) with htm
  have htmval : ∀ i, tm i = algebraMap ℚ_[p] ℂ_[p] (q i) * (pi p n) ^ (i:ℕ) := fun i => rfl
  have hexp : x = ∑ i : Fin pb.dim, tm i := by
    have hco : (xes : ℂ_[p]) = ∑ i : Fin pb.dim, ((q i • pb.basis i : ℚ_[p]⟮pi p n⟯) : ℂ_[p]) := by
      conv_lhs => rw [← pb.basis.sum_repr xes]
      rw [IntermediateField.coe_sum]
    rw [show (xes : ℂ_[p]) = x from rfl] at hco
    rw [hco]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [IntermediateField.coe_smul, hbasis_coe i, Algebra.smul_def]
  have hnormtm : ∀ i, ‖tm i‖ = ‖q i‖ * ‖pi p n‖ ^ (i:ℕ) := by
    intro i; rw [htm]; simp [norm_mul, norm_pow, norm_algebraMap']
  have htm_ne : ∀ i, tm i ≠ 0 → q i ≠ 0 := by
    intro i h hqi; exact h (by rw [htm]; simp [hqi])
  have hdistinct : ∀ a b : Fin pb.dim, a ≠ b → tm a ≠ 0 → tm b ≠ 0 → ‖tm a‖ ≠ ‖tm b‖ := by
    intro a b hab hta htb
    rw [hnormtm, hnormtm]
    exact term_norm_distinct p hn (hdim ▸ a.2) (hdim ▸ b.2)
      (fun h => hab (Fin.ext h)) (htm_ne a hta) (htm_ne b htb)
  -- orthogonality: each term is bounded by the norm of the whole sum
  have hperterm : ∀ (g : Fin pb.dim → ℂ_[p]),
      (∀ a b, a ≠ b → g a ≠ 0 → g b ≠ 0 → ‖g a‖ ≠ ‖g b‖) → ∀ j, ‖g j‖ ≤ ‖∑ i, g i‖ := by
    intro g hgd j
    set S : Finset (Fin pb.dim) := Finset.univ.filter (fun jj => g jj ≠ 0) with hS
    have hsumS : ∑ jj, g jj = ∑ jj ∈ S, g jj := by
      rw [hS]; symm; exact Finset.sum_filter_of_ne (fun jj _ hne => hne)
    rcases eq_or_ne (g j) 0 with hgj | hgj
    · rw [hgj, norm_zero]; positivity
    · have hjS : j ∈ S := by rw [hS]; simp [hgj]
      have hSne : S.Nonempty := ⟨j, hjS⟩
      have hpw : (↑S : Set (Fin pb.dim)).Pairwise (fun a b => ‖g a‖ ≠ ‖g b‖) := by
        intro a ha b hb hab
        rw [hS, Finset.coe_filter] at ha hb
        exact hgd a b hab ha.2 hb.2
      rw [hsumS, IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne hSne hpw]
      exact Finset.le_sup' (fun jj => ‖g jj‖) hjS
  have hterm_le_one : ∀ i, ‖tm i‖ ≤ 1 :=
    fun i => le_trans (by rw [hexp]; exact hperterm tm hdistinct i) hxnorm
  -- the constant coefficient `q 0`, which is in `ℤ_p`, is the residue `a`
  set i0 : Fin pb.dim := ⟨0, hdimpos⟩ with hi0
  have hq0le : ‖q i0‖ ≤ 1 := by
    have h := hterm_le_one i0
    rw [hnormtm, show ((i0:ℕ)) = 0 from rfl, pow_zero, mul_one] at h
    exact h
  set a : ℤ_[p] := ⟨q i0, hq0le⟩ with ha
  have htm0 : tm i0 = toCp p a := by
    rw [htmval, show ((i0:ℕ)) = 0 from rfl, pow_zero, mul_one, toCp, RingHom.comp_apply,
      PadicInt.Coe.ringHom_apply]
  have hsub : x - toCp p a = ∑ i ∈ Finset.univ.erase i0, tm i := by
    rw [hexp, ← htm0, Finset.sum_erase_eq_sub (Finset.mem_univ i0)]
  -- the tail `∑_{i ≥ 1}` is bounded by `‖π_n‖` termwise
  refine ⟨a, ?_⟩
  rw [hsub]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun i hi => ?_)
  rw [Finset.mem_erase] at hi
  have hi1 : 1 ≤ (i:ℕ) := by
    rcases Nat.eq_zero_or_pos (i:ℕ) with h0 | h0
    · exact absurd (Fin.ext (by rw [h0, hi0])) hi.1
    · exact h0
  rw [hnormtm]
  exact term_norm_le_pi p hn (q i) hi1 (hdim ▸ i.2) (by rw [← hnormtm]; exact hterm_le_one i)

/-- **Single-level interpolation** (RJW TeX 2538–2547, T904b): every norm-one
`u ∈ 𝒪_n` is the value `f(π_n)` of a unit power series `f ∈ ℤ_p⟦T⟧^×`.

Proof (the source's greedy `π_n`-adic digits): define the remainder/digit recursion
`r_0 = u`, `a_k = ` the `ℤ_p`-residue of `r_k` (`exists_residue_pi`), `r_{k+1} =
(r_k − a_k)/π_n ∈ 𝒪_n` (`quot_mem_O`); set `f = Σ_k a_k T^k`. The telescoping identity
`u − Σ_{j<m} a_j π_n^j = π_n^m · r_m` with `‖r_m‖ ≤ 1` gives `‖u − S_m‖ ≤ ‖π_n‖^m → 0`,
so the partial sums `S_m` converge to `u`; they also converge to `f(π_n) = evalPi f n`
(partial sums of the defining `tsum`), so `evalPi f n = u` by uniqueness of limits. As
`‖u‖ = 1 > ‖π_n‖ ≥ ‖u − a_0‖`, the ultrametric isoceles step gives `‖a_0‖ = ‖u‖ = 1`,
so `a_0 = constantCoeff f` is a `ℤ_p`-unit and `f ∈ ℤ_p⟦T⟧^×`. -/
theorem exists_evalPi_eq {n : ℕ} (hn : 1 ≤ n) {u : ℂ_[p]} (hu : u ∈ O p n)
    (hnorm : ‖u‖ = 1) :
    ∃ f : PowerSeries ℤ_[p], IsUnit f ∧ evalPi p f n = u := by
  classical
  have hpine : pi p n ≠ 0 := pi_ne_zero p hn
  -- the residue oracle from the residue step
  set oracle : ∀ x : ℂ_[p], x ∈ O p n → ℤ_[p] := fun x hx =>
    (exists_residue_pi p hn (Subring.mem_inf.1 hx).1 (Subring.mem_inf.1 hx).2).choose with horacle
  have oracle_spec : ∀ x (hx : x ∈ O p n), ‖x - toCp p (oracle x hx)‖ ≤ ‖pi p n‖ := fun x hx =>
    (exists_residue_pi p hn (Subring.mem_inf.1 hx).1 (Subring.mem_inf.1 hx).2).choose_spec
  -- the remainder/digit recursion, carrying `r_k ∈ 𝒪_n`
  set seq : ℕ → {x : ℂ_[p] // x ∈ O p n} := fun k =>
    Nat.rec (⟨u, hu⟩ : {x : ℂ_[p] // x ∈ O p n})
      (fun _ rk => ⟨(rk.1 - toCp p (oracle rk.1 rk.2)) / pi p n,
        quot_mem_O p hn rk.2 (oracle rk.1 rk.2) (oracle_spec rk.1 rk.2)⟩) k with hseq
  set a : ℕ → ℤ_[p] := fun k => oracle (seq k).1 (seq k).2 with ha
  have hseq_succ : ∀ k, (seq (k+1)).1 = ((seq k).1 - toCp p (a k)) / pi p n := fun k => rfl
  -- telescoping `u − ∑_{j<m} a_j π_n^j = π_n^m · r_m`
  have htel : ∀ m, u - ∑ j ∈ Finset.range m, toCp p (a j) * pi p n ^ j
      = pi p n ^ m * (seq m).1 := by
    intro m
    induction m with
    | zero => simp [hseq]
    | succ k ih =>
      have hpk : (pi p n)^k * (seq (k+1)).1 * pi p n
          = pi p n ^ k * ((seq k).1 - toCp p (a k)) := by
        rw [hseq_succ k]; field_simp
      rw [Finset.sum_range_succ, pow_succ]
      linear_combination ih - hpk
  refine ⟨PowerSeries.mk a, ?_, ?_⟩
  · -- `f` is a unit: `‖a_0‖ = ‖u‖ = 1` (ultrametric isoceles), so `constantCoeff f` is a unit
    have h1 := htel 1
    rw [Finset.sum_range_one, pow_zero, mul_one, pow_one] at h1
    have hlt : ‖u - toCp p (a 0)‖ < 1 := by
      rw [h1, norm_mul]
      calc ‖pi p n‖ * ‖(seq 1).1‖ ≤ ‖pi p n‖ * 1 :=
            mul_le_mul_of_nonneg_left (Subring.mem_inf.1 (seq 1).2).2 (norm_nonneg _)
        _ = ‖pi p n‖ := mul_one _
        _ < 1 := norm_pi_lt_one p hn
    have hne : ‖u - toCp p (a 0)‖ ≠ ‖u‖ := by rw [hnorm]; exact ne_of_lt hlt
    have hkey : ‖toCp p (a 0)‖ = 1 := by
      have h2 : ‖-(u - toCp p (a 0)) + u‖ = max ‖-(u - toCp p (a 0))‖ ‖u‖ :=
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact hne)
      rw [show -(u - toCp p (a 0)) + u = toCp p (a 0) from by ring, norm_neg, hnorm,
        max_eq_right hlt.le] at h2
      exact h2
    rw [norm_toCp] at hkey
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_mk]
    exact PadicInt.isUnit_iff.2 hkey
  · -- `evalPi f n = u`: the partial sums `S_m` tend to both `u` and `f(π_n)`
    set f : PowerSeries ℤ_[p] := PowerSeries.mk a with hf
    have hcoeff : ∀ k, coeff k (PowerSeries.map (toCp p) f) = toCp p (a k) := by
      intro k; rw [PowerSeries.coeff_map, hf, PowerSeries.coeff_mk]
    have hsum := (summable_evalPi p f hn).hasSum.tendsto_sum_nat
    have hzero : Filter.Tendsto (fun m => u - ∑ j ∈ Finset.range m,
        coeff j (PowerSeries.map (toCp p) f) * pi p n ^ j) Filter.atTop (nhds 0) := by
      have hbound : Filter.Tendsto (fun m => ‖pi p n‖ ^ m) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_pi_lt_one p hn)
      rw [NormedAddGroup.tendsto_nhds_zero]
      rw [NormedAddGroup.tendsto_nhds_zero] at hbound
      intro ε hε
      filter_upwards [hbound ε hε] with m hm
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hm
      rw [show (u - ∑ j ∈ Finset.range m, coeff j (PowerSeries.map (toCp p) f) * pi p n ^ j)
          = u - ∑ j ∈ Finset.range m, toCp p (a j) * pi p n ^ j from by
        rw [Finset.sum_congr rfl (fun j _ => by rw [hcoeff j])], htel m]
      calc ‖pi p n ^ m * (seq m).1‖ = ‖pi p n‖ ^ m * ‖(seq m).1‖ := by rw [norm_mul, norm_pow]
        _ ≤ ‖pi p n‖ ^ m * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact (Subring.mem_inf.1 (seq m).2).2
        _ = ‖pi p n‖ ^ m := by rw [mul_one]
        _ < ε := hm
    have hSu : Filter.Tendsto (fun m => ∑ j ∈ Finset.range m,
        coeff j (PowerSeries.map (toCp p) f) * pi p n ^ j) Filter.atTop (nhds u) := by
      have := hzero.const_sub u
      simpa using this
    rw [evalPi, seriesEval]
    exact tendsto_nhds_unique hsum hSu

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
