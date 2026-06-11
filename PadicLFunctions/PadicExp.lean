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

/-- An ultrametric normed field is a nonarchimedean (topological) ring — the
ring upgrade of mathlib's `IsUltrametricDist.nonarchimedeanAddGroup`
(MATHLIB-PR candidate). -/
instance : NonarchimedeanRing L where
  toIsTopologicalRing := inferInstance
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

omit [NormedAlgebra ℚ_[p] L] in
/-- E1: in a complete ultrametric normed field, a family is summable iff it
tends to `0` along the cofinite filter. -/
theorem summable_iff_tendsto_cofinite_zero {ι : Type*} (f : ι → L) :
    Summable f ↔ Tendsto f Filter.cofinite (𝓝 0) :=
  NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f

/-- E2: the norm of `n!` in `ℚ_[p]`, via Legendre's formula
`v_p(n!) ≤ (n−1)/(p−1)` — stated rpow-free as
`p^{-(n−1)} ≤ ‖n!‖^{p−1}`. -/
theorem norm_factorial_le {n : ℕ} (hn : 1 ≤ n) :
    (p : ℝ) ^ (-((n : ℤ) - 1)) ≤ ‖(n.factorial : ℚ_[p])‖ ^ (p - 1) := by
  have hf0 : (n.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  rw [Padic.norm_eq_zpow_neg_valuation hf0, Padic.valuation_natCast,
    ← zpow_natCast _ (p - 1), ← zpow_mul]
  refine zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_lt.le) ?_
  have hlt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : n ≠ 0)
  have hcast : ((p - 1 : ℕ) : ℤ) * (padicValNat p n.factorial : ℤ) < (n : ℤ) := by
    exact_mod_cast hlt
  linarith [hcast]

/-- Membership in the open convergence ball `‖x‖ < p^{−1/(p−1)}` of the
`p`-adic exponential, stated rpow-free: `‖x‖^{p−1} < p⁻¹`. -/
def InExpBall (p : ℕ) {L : Type*} [NormedField L] (x : L) : Prop :=
  ‖x‖ ^ (p - 1) < (p : ℝ)⁻¹

/-- The inverted Legendre bound: `‖n!‖^{-(p−1)} ≤ p^{n−1}` for `n ≥ 1`. -/
theorem norm_factorial_inv_pow_le {n : ℕ} (hn : 1 ≤ n) :
    (‖(n.factorial : ℚ_[p])‖ ^ (p - 1))⁻¹ ≤ (p : ℝ) ^ (n - 1) := by
  rw [show ((p : ℝ)) ^ (n - 1) = (((p : ℝ)) ^ (-((n : ℤ) - 1)))⁻¹ from by
    rw [← zpow_neg, neg_neg, show ((n : ℤ) - 1) = ((n - 1 : ℕ) : ℤ) from by
      omega, zpow_natCast]]
  exact inv_anti₀ (zpow_pos (by exact_mod_cast hp.out.pos) _)
    (norm_factorial_le p hn)

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- The exponential terms decay geometrically at the `(p−1)`-th power level:
`‖(n!)⁻¹•x^n‖^{p−1} ≤ ‖x‖^{p−1}·(p‖x‖^{p−1})^{n−1}` for `n ≥ 1` (Legendre
through `norm_factorial_le`; rpow-free). -/
theorem norm_factorial_inv_smul_pow_le (x : L) {n : ℕ} (hn : 1 ≤ n) :
    ‖(n.factorial : ℚ_[p])⁻¹ • x ^ n‖ ^ (p - 1)
      ≤ ‖x‖ ^ (p - 1) * ((p : ℝ) * ‖x‖ ^ (p - 1)) ^ (n - 1) := by
  rw [norm_smul, norm_inv, norm_pow, mul_pow, inv_pow]
  have hfac := norm_factorial_inv_pow_le p hn
  calc (‖(n.factorial : ℚ_[p])‖ ^ (p - 1))⁻¹ * (‖x‖ ^ n) ^ (p - 1)
      ≤ (p : ℝ) ^ (n - 1) * (‖x‖ ^ n) ^ (p - 1) :=
        mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = ‖x‖ ^ (p - 1) * ((p : ℝ) * ‖x‖ ^ (p - 1)) ^ (n - 1) := by
        rw [mul_pow, ← pow_mul, ← pow_mul,
          show n * (p - 1) = (p - 1) + (n - 1) * (p - 1) from by
            cases n with
            | zero => omega
            | succ m => rw [Nat.add_sub_cancel, Nat.succ_mul, Nat.add_comm],
          pow_add, pow_mul]
        ring

/-- On the open ball, the exponential terms are summable (E1 + the geometric
bound). -/
theorem summable_padicExp_terms {x : L} (hx : InExpBall p x) :
    Summable fun n : ℕ => (n.factorial : ℚ_[p])⁻¹ • x ^ n := by
  rw [summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop,
    tendsto_zero_iff_norm_tendsto_zero]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hT0 : 0 ≤ (p : ℝ) * ‖x‖ ^ (p - 1) := by positivity
  have hT1 : (p : ℝ) * ‖x‖ ^ (p - 1) < 1 :=
    calc (p : ℝ) * ‖x‖ ^ (p - 1) < (p : ℝ) * (p : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_left hx hp0
      _ = 1 := mul_inv_cancel₀ hp0.ne'
  have hpow : Tendsto (fun n : ℕ => ‖x‖ ^ (p - 1) * ((p : ℝ) * ‖x‖ ^ (p - 1)) ^ n)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hT0 hT1).const_mul
      (‖x‖ ^ (p - 1))
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε1 : 0 < min ε 1 := lt_min hε one_pos
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hpow ((min ε 1) ^ (p - 1))
    (pow_pos hε1 _)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hsmall := hN (n - 1) (by omega)
  rw [Real.dist_eq, sub_zero] at hsmall ⊢
  rw [abs_of_nonneg (by positivity)] at hsmall ⊢
  have hlt : ‖(n.factorial : ℚ_[p])⁻¹ • x ^ n‖ ^ (p - 1) < (min ε 1) ^ (p - 1) :=
    lt_of_le_of_lt (norm_factorial_inv_smul_pow_le p x (by omega)) hsmall
  exact lt_of_lt_of_le
    (lt_of_pow_lt_pow_left₀ _ hε1.le hlt) (min_le_left _ _)

/-- E3: the `p`-adic exponential, defined as a junk-total function (the series
`∑ x^n/n!`, meaningful on `‖x‖ < expRadius p`). -/
noncomputable def padicExp (x : L) : L := ∑' n : ℕ, (n.factorial : ℚ_[p])⁻¹ • x ^ n

omit [IsUltrametricDist L] [CompleteSpace L] in
@[simp] theorem padicExp_zero : padicExp p (0 : L) = 1 := by
  rw [padicExp, tsum_eq_single 0 fun n hn => by simp [zero_pow hn]]
  simp

omit [CompleteSpace L] in
/-- The tail terms of the difference series are strictly dominated by the
linear term: `‖(m!)⁻¹•(x^m − y^m)‖ < ‖x − y‖` for `m ≥ 2` on the open ball
(strictness needs the OPEN ball; decomposition E3 attack [3]). -/
theorem norm_factorial_inv_smul_pow_sub_lt {x y : L} (hx : InExpBall p x)
    (hy : InExpBall p y) (hxy : x ≠ y) {m : ℕ} (hm : 2 ≤ m) :
    ‖(m.factorial : ℚ_[p])⁻¹ • x ^ m - (m.factorial : ℚ_[p])⁻¹ • y ^ m‖
      < ‖x - y‖ := by
  have hp1 : 0 < p - 1 := by have := hp.out.one_lt; omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hd0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  set r : ℝ := max ‖x‖ ‖y‖ with hr
  have hr0 : 0 ≤ r := le_trans (norm_nonneg x) (le_max_left _ _)
  have hrp : r ^ (p - 1) < (p : ℝ)⁻¹ := by
    rcases max_cases ‖x‖ ‖y‖ with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [hr, h1]
    exacts [hx, hy]
  have hT1 : (p : ℝ) * r ^ (p - 1) < 1 :=
    calc (p : ℝ) * r ^ (p - 1) < (p : ℝ) * (p : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_left hrp hp0
      _ = 1 := mul_inv_cancel₀ hp0.ne'
  -- the geometric-sum bound `‖x^m − y^m‖ ≤ ‖x − y‖·r^{m−1}`
  have hgeom : ‖x ^ m - y ^ m‖ ≤ ‖x - y‖ * r ^ (m - 1) := by
    rw [← geom_sum₂_mul, mul_comm]
    rw [show ‖x - y‖ * r ^ (m - 1)
        = ‖x - y‖ * ‖∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)‖
          + ‖x - y‖ * (r ^ (m - 1)
            - ‖∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)‖) from by ring]
    refine le_add_of_le_of_nonneg (norm_mul_le _ _) ?_
    refine mul_nonneg hd0.le (sub_nonneg.mpr ?_)
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖x‖ ^ i * ‖y‖ ^ (m - 1 - i)
        ≤ r ^ i * r ^ (m - 1 - i) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) _)
            (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _)
            (by positivity) (by positivity)
      _ = r ^ (m - 1) := by
          rw [← pow_add]
          congr 1
          have := Finset.mem_range.mp hi
          omega
  -- power-level strict comparison
  have hpow : ‖(m.factorial : ℚ_[p])⁻¹ • x ^ m
        - (m.factorial : ℚ_[p])⁻¹ • y ^ m‖ ^ (p - 1)
      < ‖x - y‖ ^ (p - 1) := by
    rw [← smul_sub, norm_smul, norm_inv, mul_pow, inv_pow]
    calc (‖(m.factorial : ℚ_[p])‖ ^ (p - 1))⁻¹ * ‖x ^ m - y ^ m‖ ^ (p - 1)
        ≤ (p : ℝ) ^ (m - 1) * (‖x - y‖ * r ^ (m - 1)) ^ (p - 1) := by
          refine mul_le_mul (norm_factorial_inv_pow_le p (by omega)) ?_
            (by positivity) (by positivity)
          exact pow_le_pow_left₀ (norm_nonneg _) hgeom _
      _ = ‖x - y‖ ^ (p - 1) * ((p : ℝ) * r ^ (p - 1)) ^ (m - 1) := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm (m - 1) (p - 1),
            pow_mul]
          ring
      _ ≤ ‖x - y‖ ^ (p - 1) * ((p : ℝ) * r ^ (p - 1)) ^ 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_of_le_one (by positivity) hT1.le (by omega)
      _ < ‖x - y‖ ^ (p - 1) := by
          rw [pow_one]
          exact mul_lt_of_lt_one_right (by positivity) hT1
  exact lt_of_pow_lt_pow_left₀ _ hd0.le hpow

/-- E3: `exp` is an isometry on the open ball `‖x‖ < p^{−1/(p−1)}` — every
term beyond the linear one is strictly smaller (strictness needs the OPEN
ball; decomposition E3 attack [3]). -/
theorem norm_padicExp_sub_padicExp {x y : L} (hx : InExpBall p x)
    (hy : InExpBall p y) :
    ‖padicExp p x - padicExp p y‖ = ‖x - y‖ := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  have hd0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hsx := summable_padicExp_terms p hx
  have hsy := summable_padicExp_terms p hy
  have hsd : Summable fun n : ℕ => (n.factorial : ℚ_[p])⁻¹ • x ^ n
      - (n.factorial : ℚ_[p])⁻¹ • y ^ n := hsx.sub hsy
  have hdiff : padicExp p x - padicExp p y
      = ∑' n : ℕ, ((n.factorial : ℚ_[p])⁻¹ • x ^ n
          - (n.factorial : ℚ_[p])⁻¹ • y ^ n) := (hsx.tsum_sub hsy).symm
  rw [hdiff, hsd.tsum_eq_zero_add,
    ((summable_nat_add_iff 1).mpr hsd).tsum_eq_zero_add]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
    sub_self, zero_add, Nat.factorial_one, pow_one]
  -- the tail is strictly dominated
  have htail : ‖∑' n : ℕ, ((((n + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹
        • x ^ (n + 1 + 1)
      - (((n + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹ • y ^ (n + 1 + 1))‖
      < ‖x - y‖ := by
    -- pointwise strict + uniform bound via the vanishing tail
    have hterm : ∀ n : ℕ, ‖(((n + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹
          • x ^ (n + 1 + 1)
        - (((n + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹ • y ^ (n + 1 + 1)‖
        < ‖x - y‖ := fun n =>
      norm_factorial_inv_smul_pow_sub_lt p hx hy hxy (by omega)
    have htend : Tendsto (fun n : ℕ => ‖(((n + 1 + 1 : ℕ).factorial
          : ℚ_[p]))⁻¹ • x ^ (n + 1 + 1)
        - (((n + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹ • y ^ (n + 1 + 1)‖)
        atTop (𝓝 0) := by
      have h2 : Summable fun n : ℕ => (((n + 1 + 1 : ℕ).factorial
            : ℚ_[p]))⁻¹ • x ^ (n + 1 + 1)
          - (((n + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹ • y ^ (n + 1 + 1) :=
        (summable_nat_add_iff 1).mpr ((summable_nat_add_iff 1).mpr hsd)
      simpa using h2.tendsto_atTop_zero.norm
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (htend.eventually_lt_const (half_pos hd0))
    set C : ℝ := max ((Finset.range (N + 1)).sup' (by simp)
        fun n => ‖(((n + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹ • x ^ (n + 1 + 1)
          - (((n + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹ • y ^ (n + 1 + 1)‖)
      (‖x - y‖ / 2) with hC
    have hCd : C < ‖x - y‖ := by
      rw [hC]
      refine max_lt ((Finset.sup'_lt_iff _).mpr fun n _ => hterm n) ?_
      linarith
    refine lt_of_le_of_lt (IsUltrametricDist.norm_tsum_le_of_forall_le
      fun n => ?_) hCd
    rcases le_or_gt n N with hn | hn
    · have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
      exact le_trans (Finset.le_sup'
        (fun k => ‖(((k + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹ • x ^ (k + 1 + 1)
          - (((k + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹ • y ^ (k + 1 + 1)‖) hmem)
        (le_max_left _ _)
    · exact le_trans (hN n hn.le).le (le_max_right _ _)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (by exact fun h => absurd (h ▸ htail) (lt_irrefl _) : ‖x - y‖ ≠ ‖_‖)]
  exact max_eq_left htail.le

theorem norm_padicExp_sub_one {x : L} (hx : InExpBall p x) :
    ‖padicExp p x - 1‖ = ‖x‖ := by
  have h0 : InExpBall p (0 : L) := by
    rw [InExpBall, norm_zero, zero_pow (by have := hp.out.one_lt; omega)]
    exact inv_pos.mpr (by exact_mod_cast hp.out.pos)
  simpa using norm_padicExp_sub_padicExp p hx h0

/-- E3: the functional equation `exp(x+y) = exp(x)·exp(y)` on the ball
(double-series rearrangement; unconditional/nonarchimedean summability of the
product family via `HasSum.mul_of_nonarchimedean` + the antidiagonal Cauchy
formula — NOT norm-summable Cauchy products). -/
theorem padicExp_add {x y : L} (hx : InExpBall p x) (hy : InExpBall p y) :
    padicExp p (x + y) = padicExp p x * padicExp p y := by
  have hsx := summable_padicExp_terms p hx
  have hsy := summable_padicExp_terms p hy
  have hprod : Summable fun ij : ℕ × ℕ =>
      ((ij.1.factorial : ℚ_[p])⁻¹ • x ^ ij.1)
        * ((ij.2.factorial : ℚ_[p])⁻¹ • y ^ ij.2) :=
    (hsx.hasSum.mul_of_nonarchimedean hsy.hasSum).summable
  rw [padicExp, padicExp, padicExp,
    hsx.tsum_mul_tsum_eq_tsum_sum_antidiagonal hsy hprod]
  refine tsum_congr fun n => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l => ((k.factorial : ℚ_[p])⁻¹ • x ^ k)
        * ((l.factorial : ℚ_[p])⁻¹ • y ^ l)),
    add_pow, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hchoose : ((n.factorial : ℚ_[p]))⁻¹ * (n.choose k : ℚ_[p])
      = (k.factorial : ℚ_[p])⁻¹ * ((n - k).factorial : ℚ_[p])⁻¹ := by
    have hfk : (k.factorial : ℚ_[p]) ≠ 0 :=
      Nat.cast_ne_zero.2 k.factorial_ne_zero
    have hfnk : ((n - k).factorial : ℚ_[p]) ≠ 0 :=
      Nat.cast_ne_zero.2 (n - k).factorial_ne_zero
    have hfn : (n.factorial : ℚ_[p]) ≠ 0 :=
      Nat.cast_ne_zero.2 n.factorial_ne_zero
    have hid : ((n.choose k : ℚ_[p])) * (k.factorial : ℚ_[p])
        * ((n - k).factorial : ℚ_[p]) = (n.factorial : ℚ_[p]) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℚ_[p])
        (Nat.choose_mul_factorial_mul_factorial hkn)
    field_simp
    linear_combination hid
  rw [smul_mul_smul_comm,
    show (x ^ k * y ^ (n - k) * (n.choose k : L))
      = (n.choose k : ℚ_[p]) • (x ^ k * y ^ (n - k)) from by
      rw [Algebra.smul_def, map_natCast, mul_comm],
    smul_smul, hchoose]

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
