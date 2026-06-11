/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.PadicExp

/-!
# The extended (Iwasawa-branch) p-adic logarithm (RJW §6, decomposition W6a)

RJW Thm 6.1(ii) (TeX 1992–1995) evaluates `log_p` at the elements
`1 − ε_N^c`, which lie OUTSIDE the convergence ball of `padicLog`. This file
extends the logarithm to the rational-valuation domain: `x` with
`x^m = p^k·y` for some `m > 0`, `k : ℤ` and `y` in the open exponential
ball, setting `extLog x := m⁻¹·padicLog y` (junk value `0` outside;
Iwasawa's branch `log_p(p) = 0`). Construction cross-reference: Washington,
*Introduction to Cyclotomic Fields*, §5.1. The domain-membership engine for
the theorem's arguments is `extLogDomain_of_integral_norm_one`: a norm-one
element integral over `ℤ` has a power within distance `p⁻¹` of `1`
(pigeonhole in the finite ring `ℤ[z]/p`), and `p`-power iteration then
lands inside the exponential ball.

Decomposition: `.mathlib-quality/decomposition.md` R6, cluster W6a.
-/

open Filter Topology

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
  [IsUltrametricDist L] [CompleteSpace L]

omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L] in
/-- Members of the exponential ball have norm less than one. -/
theorem norm_lt_one_of_inExpBall {w : L} (hw : InExpBall p w) : ‖w‖ < 1 := by
  by_contra h
  push Not at h
  exact absurd hw (not_lt.mpr (le_trans
    (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le))
    (one_le_pow₀ h)))

omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L] in
/-- W6a-a1: the translated exponential ball `1 + B` is closed under
multiplication (ultrametric). -/
theorem mul_mem_expBall {y z : L} (hy : InExpBall p (y - 1))
    (hz : InExpBall p (z - 1)) : InExpBall p (y * z - 1) := by
  have key : ‖y * z - 1‖ ≤ max ‖y - 1‖ ‖z - 1‖ := by
    have hdecomp : y * z - 1 = (y - 1) * z + (z - 1) := by ring
    rw [hdecomp]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _)
      (max_le_max ?_ le_rfl)
    rw [norm_mul]
    have hz1 : ‖z‖ ≤ 1 := by
      have hzz : (z - 1) + 1 = z := by ring
      calc ‖z‖ = ‖(z - 1) + 1‖ := by rw [hzz]
        _ ≤ max ‖z - 1‖ ‖(1 : L)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ 1 := by
            rw [norm_one]
            exact max_le (norm_lt_one_of_inExpBall p hz).le le_rfl
    calc ‖y - 1‖ * ‖z‖ ≤ ‖y - 1‖ * 1 :=
          mul_le_mul_of_nonneg_left hz1 (norm_nonneg _)
      _ = ‖y - 1‖ := mul_one _
  calc ‖y * z - 1‖ ^ (p - 1) ≤ (max ‖y - 1‖ ‖z - 1‖) ^ (p - 1) :=
        pow_le_pow_left₀ (norm_nonneg _) key _
    _ < (p : ℝ)⁻¹ := by
        rcases max_cases ‖y - 1‖ ‖z - 1‖ with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
        exacts [hy, hz]

omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L] in
/-- The exponential ball is closed under powers. -/
theorem pow_mem_expBall {y : L} (hy : InExpBall p (y - 1)) (n : ℕ) :
    InExpBall p (y ^ n - 1) := by
  induction n with
  | zero =>
    rw [pow_zero, sub_self, InExpBall, norm_zero,
      zero_pow (by have := hp.out.one_lt; omega)]
    exact inv_pos.mpr (by exact_mod_cast hp.out.pos)
  | succ k ih =>
    rw [pow_succ]
    exact mul_mem_expBall p ih hy

/-- W6a-a2: the logarithm of a power on the ball. -/
theorem padicLog_pow {y : L} (hy : InExpBall p (y - 1)) (n : ℕ) :
    padicLog p (y ^ n) = n • padicLog p y := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, padicLog_mul p (pow_mem_expBall p hy k) hy, ih, succ_nsmul]

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- The `p`-adic norm of `p` in `L`. -/
theorem norm_natCast_p : ‖((p : ℕ) : L)‖ = (p : ℝ)⁻¹ := by
  rw [show ((p : ℕ) : L) = algebraMap ℚ_[p] L ((p : ℕ) : ℚ_[p]) from
      (map_natCast _ p).symm,
    norm_algebraMap', Padic.norm_p]

omit [CompleteSpace L] in
/-- W6a-a3: one `p`-th-power step contracts towards `1`
(`p ∣ (p choose i)` for `0 < i < p`). -/
theorem norm_pow_p_sub_one_le {w : L} (hw : ‖w - 1‖ < 1) :
    ‖w ^ p - 1‖ ≤ max (‖w - 1‖ ^ p) ((p : ℝ)⁻¹ * ‖w - 1‖) := by
  set t : L := w - 1 with ht
  have hexp : w ^ p - 1
      = ∑ i ∈ Finset.range p, t ^ (i + 1) * (p.choose (i + 1) : L) := by
    have hwt : w ^ p = (t + 1) ^ p := by rw [ht]; ring_nf
    rw [hwt, add_pow, Finset.sum_range_succ']
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right,
      Nat.cast_one]
    ring
  rw [hexp]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (le_max_of_le_left (by positivity)) fun i hi => ?_
  rw [norm_mul, norm_pow]
  rcases eq_or_ne (i + 1) p with hip | hip
  · -- top term `t^p`
    rw [hip, Nat.choose_self, Nat.cast_one, norm_one, mul_one]
    exact le_max_left _ _
  · -- interior terms carry `p ∣ choose`
    have hlt : i + 1 < p := lt_of_le_of_ne (Finset.mem_range.mp hi) hip
    obtain ⟨m, hm⟩ := hp.out.dvd_choose_self (Nat.succ_ne_zero i) hlt
    refine le_max_of_le_right ?_
    calc ‖t‖ ^ (i + 1) * ‖((p.choose (i + 1) : ℕ) : L)‖
        ≤ ‖t‖ * (p : ℝ)⁻¹ := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _)
          · exact pow_le_of_le_one (norm_nonneg _) hw.le (Nat.succ_ne_zero i)
          · rw [hm, Nat.cast_mul, norm_mul,
              norm_natCast_p p]
            calc (p : ℝ)⁻¹ * ‖((m : ℕ) : L)‖ ≤ (p : ℝ)⁻¹ * 1 := by
                  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  exact IsUltrametricDist.norm_natCast_le_one L m
              _ = (p : ℝ)⁻¹ := mul_one _
      _ = (p : ℝ)⁻¹ * ‖t‖ := mul_comm _ _

omit [CompleteSpace L] in
/-- W6a-a4: from the open unit ball, some `p`-power iterate lands in the
exponential ball (geometric contraction with ratio
`max (‖w−1‖^(p−1)) p⁻¹ < 1`). -/
theorem exists_pPow_pow_inExpBall {w : L} (hw : ‖w - 1‖ < 1) :
    ∃ j : ℕ, InExpBall p (w ^ p ^ j - 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  set t0 : ℝ := max (‖w - 1‖ ^ (p - 1)) (p : ℝ)⁻¹ with ht0
  have ht00 : 0 ≤ t0 := le_max_of_le_right (by positivity)
  have ht01 : t0 < 1 := max_lt
    (pow_lt_one₀ (norm_nonneg _) hw (by have := hp.out.one_lt; omega))
    (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))
  have hdecay : ∀ j : ℕ, ‖w ^ p ^ j - 1‖ ≤ t0 ^ j * ‖w - 1‖ := by
    intro j
    induction j with
    | zero => simp
    | succ k ih =>
      have hrw : ‖w ^ p ^ k - 1‖ ≤ ‖w - 1‖ := le_trans ih
        (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ht00 ht01.le))
      have hk1 : ‖w ^ p ^ k - 1‖ < 1 := lt_of_le_of_lt hrw hw
      have hstep := norm_pow_p_sub_one_le p hk1
      rw [← pow_mul, ← pow_succ] at hstep
      have hbound : max (‖w ^ p ^ k - 1‖ ^ p) ((p : ℝ)⁻¹ * ‖w ^ p ^ k - 1‖)
          ≤ t0 * ‖w ^ p ^ k - 1‖ := by
        refine max_le ?_
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
        calc ‖w ^ p ^ k - 1‖ ^ p
            = ‖w ^ p ^ k - 1‖ ^ (p - 1) * ‖w ^ p ^ k - 1‖ := by
              rw [← pow_succ]
              congr 1
              have := hp.out.one_le
              omega
          _ ≤ t0 * ‖w ^ p ^ k - 1‖ :=
              mul_le_mul_of_nonneg_right
                (le_trans (pow_le_pow_left₀ (norm_nonneg _) hrw _)
                  (le_max_left _ _)) (norm_nonneg _)
      refine le_trans hstep (le_trans hbound ?_)
      calc t0 * ‖w ^ p ^ k - 1‖ ≤ t0 * (t0 ^ k * ‖w - 1‖) :=
            mul_le_mul_of_nonneg_left ih ht00
        _ = t0 ^ (k + 1) * ‖w - 1‖ := by ring
  have hgeo : Filter.Tendsto
      (fun j : ℕ => (t0 ^ j * ‖w - 1‖) ^ (p - 1)) Filter.atTop (nhds 0) := by
    have hfun : (fun j : ℕ => (t0 ^ j * ‖w - 1‖) ^ (p - 1))
        = fun j => ‖w - 1‖ ^ (p - 1) * ((t0 ^ (p - 1)) ^ j) := by
      funext j
      rw [mul_pow, ← pow_mul, mul_comm j (p - 1), pow_mul]
      ring
    rw [hfun]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (pow_lt_one₀ ht00 ht01 (by have := hp.out.one_lt; omega))).const_mul
      (‖w - 1‖ ^ (p - 1))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hgeo ((p : ℝ)⁻¹) (inv_pos.mpr hp0)
  refine ⟨N, ?_⟩
  have hsmall := hN N le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hsmall
  change ‖w ^ p ^ N - 1‖ ^ (p - 1) < (p : ℝ)⁻¹
  calc ‖w ^ p ^ N - 1‖ ^ (p - 1) ≤ (t0 ^ N * ‖w - 1‖) ^ (p - 1) :=
        pow_le_pow_left₀ (norm_nonneg _) (hdecay N) _
    _ < (p : ℝ)⁻¹ := hsmall

/-- W6a-a5 (pigeonhole): a norm-one element integral over `ℤ` has a power
within `p⁻¹` of `1` — `ℤ[z]/p` is finite, so `z^i(z^m − 1) ∈ p·ℤ[z]` for
some `i, m`, and `‖z^i‖ = 1` cancels. -/
theorem exists_pow_sub_one_norm_le {z : L} (hz : IsIntegral ℤ z)
    (hz1 : ‖z‖ = 1) : ∃ m : ℕ, 0 < m ∧ ‖z ^ m - 1‖ ≤ (p : ℝ)⁻¹ := by sorry

/-- The domain of the extended logarithm: rational-valuation elements, i.e.
`x^m = p^k·y` with `y` in the translated exponential ball. -/
def ExtLogDomain (x : L) : Prop :=
  ∃ (m : ℕ) (k : ℤ) (y : L), 0 < m ∧ x ^ m = (p : L) ^ k * y
    ∧ InExpBall p (y - 1)

open Classical in
/-- W6a-a6: the extended (Iwasawa-branch, `log_p p = 0`) logarithm,
junk-total: `extLog x = m⁻¹ • padicLog y` for a witness `x^m = p^k·y`,
and `0` off the domain. -/
noncomputable def extLog (x : L) : L :=
  if h : ExtLogDomain p x
  then ((h.choose : ℚ_[p]))⁻¹
    • padicLog p h.choose_spec.choose_spec.choose
  else 0

/-- W6a-a7 (well-definedness): every witness computes `extLog`. -/
theorem extLog_eq_of_witness {x : L} {m : ℕ} {k : ℤ} {y : L} (hm : 0 < m)
    (hxy : x ^ m = (p : L) ^ k * y) (hy : InExpBall p (y - 1)) :
    extLog p x = ((m : ℚ_[p]))⁻¹ • padicLog p y := by sorry

/-- W6a-a8: `extLog` agrees with `padicLog` on the ball. -/
theorem extLog_eq_padicLog {x : L} (hx : InExpBall p (x - 1)) :
    extLog p x = padicLog p x := by sorry

/-- W6a-a9: additivity on the domain. -/
theorem extLog_mul {x y : L} (hx : ExtLogDomain p x) (hy : ExtLogDomain p y) :
    extLog p (x * y) = extLog p x + extLog p y := by sorry

/-- W6a-a10: roots of unity have extended logarithm `0`. -/
theorem extLog_eq_zero_of_pow_eq_one {x : L} {n : ℕ} (hn : 0 < n)
    (hx : x ^ n = 1) : extLog p x = 0 := by sorry

/-- W6a-a10 (continued): `log_p(x) = log_p(−x)` (RJW's final step,
TeX 2150). -/
theorem extLog_neg {x : L} (hx : ExtLogDomain p x) :
    extLog p (-x) = extLog p x := by sorry

/-- W6a-a11 (the domain engine): norm-one elements integral over `ℤ` lie in
the extended-log domain — covers all the arguments `1 − ε_N^c` of RJW
Thm 6.1(ii) for tame conductor `D > 1`. -/
theorem extLogDomain_of_integral_norm_one {z : L} (hz : IsIntegral ℤ z)
    (hz1 : ‖z‖ = 1) : ExtLogDomain p z := by sorry

end PadicLFunctions
