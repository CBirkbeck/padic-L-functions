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

open Complex EisensteinSeries

open UpperHalfPlane hiding I

open scoped MatrixGroups Real ArithmeticFunction.sigma

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]

section sigmaArithmetic

omit hp in
/-- For `p ∤ n` the prime-to-`p` divisor sum is the full divisor sum:
`σ^p_k(n) = σ_k(n)`. -/
theorem sigmaP_eq_of_not_dvd {n : ℕ} (hn : ¬ (p : ℕ) ∣ n) (k : ℕ) :
    sigmaP p k n = ArithmeticFunction.sigma k n := by
  rw [sigmaP, ArithmeticFunction.sigma_apply]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  refine Finset.filter_true_of_mem fun d hd hpd => hn ?_
  exact hpd.trans ((Nat.mem_divisors.1 hd).1)

/-- For `p ∣ n` (RJW's "easy check", TeX 2390–2393, subtraction-free form):
`σ^p_k(n) + p^k·σ_k(n/p) = σ_k(n)` — the divisors of `n` split into the
prime-to-`p` ones and `p` times the divisors of `n/p`. -/
theorem sigmaP_add_pow_mul_sigma_div {n : ℕ} (hn : (p : ℕ) ∣ n) (hn0 : n ≠ 0)
    (k : ℕ) :
    sigmaP p k n + p ^ k * ArithmeticFunction.sigma k (n / p)
      = ArithmeticFunction.sigma k n := by
  have hp0 : 0 < p := hp.out.pos
  -- The `p`-divisible divisors of `n` are `p·e` for `e` a divisor of `n/p`.
  have hcompl :
      ∑ d ∈ n.divisors.filter (fun d => (p : ℕ) ∣ d), d ^ k
        = p ^ k * ArithmeticFunction.sigma k (n / p) := by
    rw [ArithmeticFunction.sigma_apply, Finset.mul_sum]
    refine Finset.sum_nbij' (fun d => d / p) (fun e => p * e) ?_ ?_ ?_ ?_ ?_
    · -- `d ∣ n, p ∣ d ⟹ d/p ∣ n/p`
      intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdn, _⟩, c, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left _ hp0, Nat.mem_divisors]
      refine ⟨(mul_dvd_mul_iff_left (by exact_mod_cast hp0.ne')).1 ?_,
        Nat.div_ne_zero_iff.mpr ⟨hp0.ne', Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hn⟩⟩
      rwa [Nat.mul_div_cancel' hn]
    · -- `e ∣ n/p ⟹ p·e ∣ n`
      intro e he
      rw [Nat.mem_divisors] at he
      rw [Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨?_, hn0⟩, Dvd.intro e rfl⟩
      calc p * e ∣ p * (n / p) := mul_dvd_mul_left p he.1
        _ = n := Nat.mul_div_cancel' hn
    · -- left inverse: `d/p ↦ p·(d/p) = d`
      intro d hd
      rw [Finset.mem_filter] at hd
      exact Nat.mul_div_cancel' hd.2
    · -- right inverse: `p·e ↦ (p·e)/p = e`
      intro e _
      exact Nat.mul_div_cancel_left e hp0
    · -- values: `d ^ k = p ^ k * (d/p) ^ k` on the `p`-divisible divisors
      intro d hd
      rw [Finset.mem_filter] at hd
      rw [← mul_pow, Nat.mul_div_cancel' hd.2]
  rw [sigmaP, ← hcompl, ArithmeticFunction.sigma_apply]
  exact Finset.sum_filter_not_add_sum_filter n.divisors (fun d => (p : ℕ) ∣ d) (fun d => d ^ k)

end sigmaArithmetic

section stabilisation

/-- The point `p·z` of the upper half-plane (positive real scaling). -/
noncomputable def pScale (z : ℍ) : ℍ :=
  ⟨(p : ℂ) * z, by
    rw [Complex.mul_im, Complex.natCast_im, Complex.natCast_re, zero_mul, add_zero,
      UpperHalfPlane.coe_im]
    exact mul_pos (Nat.cast_pos.mpr hp.out.pos) z.im_pos⟩

/-- RJW's normalisation of the Eisenstein series (TeX 2371):
`E_k = ζ(1−k)/2 + Σ_{n≥1}σ_{k−1}(n)qⁿ`, i.e. `(ζ(1−k)/2)·E` for mathlib's
constant-term-1 normalised `ModularForm.E`. -/
noncomputable def rjwEisenstein {k : ℕ} (hk : 3 ≤ k) : ℍ → ℂ := fun z =>
  (((zetaNeg (k - 1) : ℚ) : ℂ) / 2) * ModularForm.E hk z

/-- For even `k ≥ 4` the Bernoulli number `B_k` is non-zero. The explicit formula
`riemannZeta_two_mul_nat` writes `ζ(k)` as a product of non-zero constants and `B_k`;
since `ζ(k) ≠ 0` for `k > 1`, `B_k ≠ 0`. -/
private lemma bernoulli_ne_zero_of_even {k : ℕ} (hk : 4 ≤ k) (hk2 : Even k) :
    bernoulli k ≠ 0 := by
  intro hB
  obtain ⟨m, hm2⟩ := hk2
  have hmk : k = 2 * m := by omega
  have hm : m ≠ 0 := by omega
  have hB' : bernoulli (2 * m) = 0 := hmk ▸ hB
  have hz : riemannZeta (2 * m) = 0 := by
    rw [riemannZeta_two_mul_nat hm, hB']; simp
  refine riemannZeta_ne_zero_of_one_lt_re (s := ((2 * m : ℕ) : ℂ)) ?_ (by exact_mod_cast hz)
  rw [Complex.natCast_re]
  exact_mod_cast by omega

/-- Summability of the divisor-sum q-expansion series `∑ σ_{k-1}(n) qⁿ`
(reproduces mathlib's private `EisensteinSeries.summable_sigma_mul_cexp_pow`). -/
private lemma summable_sigma_cexp {k : ℕ} (hk : 1 ≤ k) (τ : ℍ) :
    Summable fun n : ℕ ↦ (σ (k - 1) n : ℂ) * Complex.exp (2 * π * I * τ) ^ n := by
  apply Summable.of_norm_bounded
    (summable_norm_pow_mul_geometric_of_norm_lt_one k
      (UpperHalfPlane.norm_exp_two_pi_I_lt_one τ))
  intro n
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  gcongr
  exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ (k - 1) n).trans_eq (by congr 1; omega)

/-- The ℂ-side normalisation identity: scaling mathlib's `1 − (2k/B_k)∑` shape by
`C := ζ(1−k)/2` turns the leading `−C·(2k/B_k)` into `+1`, because
`ζ(1−k) = (−1)^{k−1}B_k/k = −B_k/k` for even `k`. -/
private lemma rjw_normalisation {k : ℕ} (hk : 4 ≤ k) (hk2 : Even k) :
    -((((zetaNeg (k - 1) : ℚ) : ℂ) / 2) * (2 * k / bernoulli k)) = 1 := by
  have hBne : (bernoulli k : ℂ) ≠ 0 := by
    exact_mod_cast bernoulli_ne_zero_of_even hk hk2
  have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hzc : ((zetaNeg (k - 1) : ℚ) : ℂ) = -(bernoulli k / k) := by
    have hodd : Odd (k - 1) := by
      obtain ⟨m, hm⟩ := hk2; exact ⟨m - 1, by omega⟩
    have hcast : ((k - 1 : ℕ) : ℂ) + 1 = (k : ℂ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]; push_cast; ring
    rw [zetaNeg, show k - 1 + 1 = k by omega, hodd.neg_one_pow]
    push_cast
    rw [hcast]
    ring
  rw [hzc]
  field_simp

/-- The per-point ℕ-indexed q-expansion of RJW's normalised Eisenstein series:
`E_k(τ) = ζ(1−k)/2 + Σ_{n≥1} σ_{k−1}(n)·qⁿ`, packaged as a `HasSum` with the
constant term folded into the `n = 0` summand (`q⁰ = 1`). -/
private lemma hasSum_rjwEisenstein {k : ℕ} (hk : 4 ≤ k) (hk2 : Even k) (τ : ℍ) :
    HasSum
      (fun n : ℕ => (if n = 0 then ((zetaNeg (k - 1) : ℚ) : ℂ) / 2
          else (σ (k - 1) n : ℂ)) * Complex.exp (2 * π * I * τ) ^ n)
      (rjwEisenstein (k := k) (by omega) τ) := by
  set C : ℂ := ((zetaNeg (k - 1) : ℚ) : ℂ) / 2 with hC
  -- summability of the shifted (`n+1`) series
  have hS : Summable fun n : ℕ ↦
      (σ (k - 1) (n + 1) : ℂ) * Complex.exp (2 * π * I * τ) ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_sigma_cexp (by omega) τ)
  -- the body, after shifting by 1 and peeling the constant term
  rw [← hasSum_nat_add_iff' 1]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Finset.range_one,
    Finset.sum_singleton, pow_zero, mul_one]
  -- the value of `E_k(τ) − C` as `C·(2k/B_k)·∑ σ qⁿ` rewritten via the normalisation
  have hnorm : C * (2 * k / bernoulli k) = -(1 : ℂ) := by
    have h := rjw_normalisation hk hk2
    rw [← hC] at h
    linear_combination -h
  have hval : rjwEisenstein (k := k) (by omega) τ - C
      = ∑' n : ℕ, (σ (k - 1) (n + 1) : ℂ) * Complex.exp (2 * π * I * τ) ^ (n + 1) := by
    have hqe := EisensteinSeries.q_expansion_bernoulli (k := k) (by omega) hk2 τ
    simp_rw [zpow_natCast] at hqe
    set S : ℂ := ∑' n : ℕ+, (σ (k - 1) n : ℂ) * Complex.exp (2 * π * I * τ) ^ (n : ℕ)
      with hSdef
    rw [← tsum_pnat_eq_tsum_succ
        (f := fun n ↦ (σ (k - 1) n : ℂ) * Complex.exp (2 * π * I * τ) ^ n),
      rjwEisenstein, hqe, ← hC, ← hSdef]
    linear_combination (-S) * hnorm
  rw [hval]
  exact hS.hasSum

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
  have hp0 : 0 < p := hp.out.pos
  have hpne : (p : ℕ) ≠ 0 := hp0.ne'
  set q : ℂ := Complex.exp (2 * π * I * (z : ℂ)) with hq
  -- the per-point coefficient function for `rjwEisenstein`
  set b : ℕ → ℂ := fun n => if n = 0 then ((zetaNeg (k - 1) : ℚ) : ℂ) / 2
      else (σ (k - 1) n : ℂ) with hb
  -- Step B at `z`
  have hSz : HasSum (fun n : ℕ => b n * q ^ n) (rjwEisenstein (k := k) (by omega) z) :=
    hasSum_rjwEisenstein hk hk2 z
  -- the q-parameter at `p·z` is `qᵖ`
  have hqp : Complex.exp (2 * π * I * ((pScale p z : ℂ))) = q ^ p := by
    rw [show ((pScale p z : ℂ)) = (p : ℂ) * (z : ℂ) from rfl,
      show 2 * π * I * ((p : ℂ) * (z : ℂ)) = (p : ℂ) * (2 * π * I * (z : ℂ)) by ring,
      Complex.exp_nat_mul]
  -- Step B at `p·z`, in terms of `qᵖ`
  have hSpz0 : HasSum (fun n : ℕ => b n * (q ^ p) ^ n)
      (rjwEisenstein (k := k) (by omega) (pScale p z)) := by
    have := hasSum_rjwEisenstein hk hk2 (pScale p z)
    rwa [hqp] at this
  -- the stabilisation summand on multiples of `p`, extended by zero
  set g : ℕ → ℂ := fun m => if p ∣ m then b (m / p) * q ^ m else 0 with hg
  -- the injection `n ↦ p·n`
  have hinj : Function.Injective (fun n : ℕ => p * n) := mul_right_injective₀ hpne
  -- off the range of `p·(·)`: `¬ p ∣ m`, so `g m = 0`
  have hgoff : ∀ m, m ∉ Set.range (fun n : ℕ => p * n) → g m = 0 := by
    intro m hm
    simp only [hg]
    rw [if_neg]
    intro hdvd
    obtain ⟨c, rfl⟩ := hdvd
    exact hm ⟨c, rfl⟩
  -- `g ∘ (p·) = fun n => b n · (qᵖ)ⁿ`
  have hcomp : (g ∘ fun n : ℕ => p * n) = fun n : ℕ => b n * (q ^ p) ^ n := by
    funext n
    simp only [hg, Function.comp_apply]
    rw [Nat.mul_div_cancel_left _ hp0, if_pos (Dvd.intro n rfl), ← pow_mul, mul_comm p n]
  -- Step C: reindex `hSpz0` to `g` over the multiples of `p`
  have hSpz : HasSum g (rjwEisenstein (k := k) (by omega) (pScale p z)) := by
    rw [← Function.Injective.hasSum_iff (f := g) hinj hgoff, hcomp]
    exact hSpz0
  -- Step D: subtract the scaled `p·z` series from the `z` series
  have hD := hSz.sub (hSpz.mul_left ((p : ℂ) ^ (k - 1)))
  -- the stabilised summand equals the subtracted summand, pointwise
  have hfun : (fun n : ℕ => ((stabilisedCoeff p k n : ℚ) : ℂ) * q ^ n)
      = fun n : ℕ => b n * q ^ n - (p : ℂ) ^ (k - 1) * g n := by
    funext n
    simp only [hg]
    rcases eq_or_ne n 0 with rfl | hn0
    · -- constant term
      simp only [hb, stabilisedCoeff, if_pos rfl, dvd_zero, Nat.zero_div, pow_zero, mul_one]
      push_cast
      ring
    · rcases (em ((p : ℕ) ∣ n)) with hdvd | hndvd
      · -- `p ∣ n`: use the σ-splitting identity
        have hsplit := sigmaP_add_pow_mul_sigma_div p hdvd hn0 (k - 1)
        have hcast : ((sigmaP p (k - 1) n : ℚ) : ℂ)
            = (σ (k - 1) n : ℂ) - (p : ℂ) ^ (k - 1) * (σ (k - 1) (n / p) : ℂ) := by
          have := congrArg (fun m : ℕ => (m : ℂ)) hsplit
          push_cast at this ⊢
          linear_combination this
        have hdivne : n / p ≠ 0 :=
          Nat.div_ne_zero_iff.mpr ⟨hpne, Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd⟩
        simp only [hb, stabilisedCoeff, if_neg hn0, if_pos hdvd, if_neg hdivne]
        rw [hcast]
        ring
      · -- `p ∤ n`: prime-to-`p` sum equals full sum, the `p·z` term drops out
        simp only [hb, stabilisedCoeff, if_neg hn0, if_neg hndvd]
        rw [sigmaP_eq_of_not_dvd p hndvd (k - 1)]
        push_cast
        ring
  rw [hfun]
  exact hD

end stabilisation

end PadicLFunctions
