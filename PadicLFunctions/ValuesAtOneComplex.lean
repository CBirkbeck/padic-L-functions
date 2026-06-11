/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Interpolation.GenBernoulliComplex

/-!
# The classical value L(θ,1) (RJW §6.1, Thm 6.1(i), decomposition C6)

RJW Thm 6.1(i) (TeX 1989–1991), following Washington Thm 4.9: for `θ`
non-trivial of conductor `N` and `ε` a primitive `N`-th root of unity,
`L(θ,1) = −G(θ⁻¹)⁻¹ Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·log(1−ε^c)`. Complex-analysis
quarantine file (the §4 `ZetaValuesComplex` pattern), stated against
mathlib's `DirichletCharacter.LFunction` per the mathlib-linking directive.

Decomposition: `.mathlib-quality/decomposition.md` R6, cluster C6.
-/

open Complex DirichletCharacter

namespace PadicLFunctions

namespace ValuesAtOneComplex

variable {N : ℕ} [NeZero N]

/-- C6-c4: Gauss sums factor over coprime levels (CRT): for `θ` the
product of `η` (level `D`) and `χ` (level `M`) at level `DM` and the
**split** additive character `ε = εD·εM`, `G(θ) = G(η)·G(χ)` — stated over
a general domain, shared by the complex (i) and `p`-adic (ii) assemblies.

Statement aligned at execution (T609): the skeleton carried twist factors
`χ(D)·η(M)`, copied from the *standard* CRT formula
`τ(χ) = χ_D(M)·χ_M(D)·τ(χ_D)·τ(χ_M)` which holds for the **standard**
additive character `e^{2πi·/DM}` (where `1/DM` does not split additively
under CRT). Here the additive character is literally `(εD·εM)^x = εD^x·εM^x`,
which **does** split: `(εD·εM)^(a.val) = εD^((a : ZMod D).val)·εM^((a : ZMod M).val)`.
With the split character the reindex `a ↦ ((a : ZMod D), (a : ZMod M))`
factors the Gauss sum cleanly with **no** twist (verified on paper from the
CRT bijection, as the planning note required). The twist factors are
therefore removed. The pointwise identity
`θ a = η (a : ZMod D)·χ (a : ZMod M)` holds for all `a` (both sides vanish
on non-units by the unit-CRT dichotomy). -/
theorem gaussSum_mul_coprime {R : Type*} [CommRing R] [IsDomain R]
    {D M : ℕ} [NeZero D] [NeZero M] (hco : Nat.Coprime D M)
    (η : DirichletCharacter R D) (χ : DirichletCharacter R M)
    {θ : DirichletCharacter R (D * M)}
    (hθ : θ = DirichletCharacter.changeLevel (Dvd.intro _ rfl) η
      * DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ)
    {εD εM : R} (hεD : IsPrimitiveRoot εD D) (hεM : IsPrimitiveRoot εM M) :
    gaussSum θ (AddChar.zmodChar (D * M)
        (show (εD * εM) ^ (D * M) = 1 from by
          rw [mul_pow, pow_mul, hεD.pow_eq_one, one_pow, one_mul,
            mul_comm D M, pow_mul, hεM.pow_eq_one, one_pow]))
      = gaussSum η (AddChar.zmodChar D hεD.pow_eq_one)
        * gaussSum χ (AddChar.zmodChar M hεM.pow_eq_one) := by
  classical
  -- the CRT ring isomorphism `ZMod (D*M) ≃+* ZMod D × ZMod M`.
  set e := ZMod.chineseRemainder hco with he
  set ψ := AddChar.zmodChar (D * M)
    (show (εD * εM) ^ (D * M) = 1 from by
      rw [mul_pow, pow_mul, hεD.pow_eq_one, one_pow, one_mul,
        mul_comm D M, pow_mul, hεM.pow_eq_one, one_pow]) with hψ
  set ψD := AddChar.zmodChar D hεD.pow_eq_one with hψD
  set ψM := AddChar.zmodChar M hεM.pow_eq_one with hψM
  -- The forward CRT map is the pair of canonical casts.
  have hfst : ∀ a : ZMod (D * M), (e a).1 = (ZMod.cast a : ZMod D) := fun a => Prod.fst_zmod_cast a
  have hsnd : ∀ a : ZMod (D * M), (e a).2 = (ZMod.cast a : ZMod M) := fun a => Prod.snd_zmod_cast a
  -- The product character factors pointwise (both sides vanish on non-units).
  have hθfac : ∀ a : ZMod (D * M),
      θ a = η (ZMod.cast a : ZMod D) * χ (ZMod.cast a : ZMod M) := by
    intro a
    rw [hθ, MulChar.mul_apply]
    by_cases ha : IsUnit a
    · -- `a` a unit: each `changeLevel` evaluates by casting (`changeLevel_eq_cast_of_dvd`).
      obtain ⟨u, rfl⟩ := ha
      rw [changeLevel_eq_cast_of_dvd, changeLevel_eq_cast_of_dvd]
    · -- `a` a non-unit: by unit-CRT one of the casts is a non-unit, killing the RHS.
      rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha, zero_mul]
      have hunit : ¬ (IsUnit (ZMod.cast a : ZMod D) ∧ IsUnit (ZMod.cast a : ZMod M)) := by
        rw [← hfst a, ← hsnd a, ← Prod.isUnit_iff,
          MulEquiv.isUnit_map (f := e) (x := a)]
        exact ha
      rw [not_and_or] at hunit
      rcases hunit with h | h
      · rw [MulChar.map_nonunit _ h, zero_mul]
      · rw [MulChar.map_nonunit _ h, mul_zero]
  -- The split additive character factors pointwise: `(εD εM)^a.val = εD^a.val · εM^a.val`,
  -- and `cast a = (a.val : ZMod D)`, so `ψD (cast a) = εD^a.val` via `zmodChar_apply'`.
  have hψfac : ∀ a : ZMod (D * M),
      ψ a = ψD (ZMod.cast a : ZMod D) * ψM (ZMod.cast a : ZMod M) := by
    intro a
    have hcD : (ZMod.cast a : ZMod D) = ((a.val : ℕ) : ZMod D) := (ZMod.natCast_val a).symm
    have hcM : (ZMod.cast a : ZMod M) = ((a.val : ℕ) : ZMod M) := (ZMod.natCast_val a).symm
    rw [hψ, hψD, hψM, AddChar.zmodChar_apply, hcD, hcM, AddChar.zmodChar_apply',
      AddChar.zmodChar_apply', mul_pow]
  -- Reindex the Gauss sum along the CRT bijection and factor the double sum.
  rw [gaussSum]
  -- rewrite each summand as `g (e a)` with `g (b, c) = η b · χ c · (ψD b · ψM c)`.
  have hsummand : ∀ a : ZMod (D * M), θ a * ψ a
      = (fun p : ZMod D × ZMod M => η p.1 * χ p.2 * (ψD p.1 * ψM p.2)) (e.toEquiv a) := by
    intro a
    rw [hθfac, hψfac]
    simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, hfst, hsnd]
  simp_rw [hsummand]
  rw [Equiv.sum_comp e.toEquiv
      (fun p : ZMod D × ZMod M => η p.1 * χ p.2 * (ψD p.1 * ψM p.2)),
    ← Finset.univ_product_univ, Finset.sum_product, gaussSum, gaussSum,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- C6-c2 (boundary Taylor value): for `z` on the unit circle, `z ≠ 1`,
the logarithm series converges at the boundary —
`Σ_{n≥1} zⁿ/n = −log(1−z)`, as a limit of partial sums.

Statement aligned at execution (T610): the skeleton stated this as a
`HasSum`, which is **false** — on the unit circle `‖zⁿ⁺¹/(n+1)‖ = 1/(n+1)`
is not summable (`Real.not_summable_one_div_natCast`), so over `ℂ`
(`summable_norm_iff`, finite-dimensional) the family is not `Summable`
and `HasSum _ L` fails for every `L`. The series is only *conditionally*
convergent off `z = 1`, so the honest statement is the convergence of the
partial sums (`Tendsto … atTop`). Recorded in `b2_log.jsonl` (T610).
Proof route: Dirichlet's test gives a Cauchy partial-sum sequence; Abel's
limit theorem (`Complex.tendsto_tsum_powerSeries_nhdsWithin_lt`) identifies
the boundary limit with the radial interior limit, which is
`-log (1 - xz)` by the open-disc Taylor series
(`Complex.hasSum_taylorSeries_neg_log`); continuity of `Complex.log` off
the branch cut (`1 - z ∈ slitPlane` since `Re (1 - z) > 0`) closes it. -/
theorem tendsto_sum_pow_div_eq_neg_log {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ (n + 1) / (n + 1))
      Filter.atTop (nhds (-Complex.log (1 - z))) := by
  classical
  -- `z ≠ 1` on the unit circle forces `Re z < 1`, so `1 - z` lies in the slit plane.
  have hzlt : z.re < 1 := by
    have hle : z.re ≤ 1 := by simpa [hz] using Complex.re_le_norm z
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · refine absurd (Complex.ext h ?_) hz1
      have hns : z.re * z.re + z.im * z.im = 1 := by
        have := Complex.normSq_eq_norm_sq z
        rw [Complex.normSq_apply] at this
        rw [hz] at this; simpa using this
      have him : z.im * z.im = 0 := by nlinarith [hns, h]
      simpa using (mul_self_eq_zero.mp him)
  -- the coefficient sequence `a k = z ^ k / k` (with `a 0 = 0`).
  set a : ℕ → ℂ := fun k => z ^ k / k with ha
  have hz0 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr fun h => hz1 h.symm
  have hpos : 0 < ‖1 - z‖ := norm_pos_iff.mpr hz0
  -- Partial sums of `z ^ (k+1)` are bounded (geometric, `z ≠ 1`).
  have hbound : ∀ n, ‖∑ i ∈ Finset.range n, z ^ (i + 1)‖ ≤ 2 / ‖1 - z‖ := by
    intro n
    have hsplit : ∑ i ∈ Finset.range n, z ^ (i + 1) = z * ∑ i ∈ Finset.range n, z ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, geom_sum_eq hz1 n, norm_mul, norm_div]
    have hzn : ‖z ^ n - 1‖ ≤ 2 := by
      calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num
    have hzm1 : ‖z - 1‖ = ‖1 - z‖ := by rw [← norm_neg, neg_sub]
    rw [hzm1, hz, one_mul, div_le_div_iff_of_pos_right hpos]
    exact hzn
  -- Dirichlet's test: the target partial sums `S n = ∑_{i<n} z^(i+1)/(i+1)` are Cauchy.
  -- (The summand is `(1/(i+1)) • z^(i+1)`: antitone `1/(i+1) → 0`, bounded geometric factor.)
  have hSeq : (fun n => ∑ i ∈ Finset.range n, z ^ (i + 1) / (i + 1))
      = fun n => ∑ i ∈ Finset.range n,
          (fun k : ℕ => (1 : ℝ) / (k + 1)) i • (fun k => z ^ (k + 1)) i := by
    funext n
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Complex.real_smul, one_div, Complex.ofReal_inv, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one]
    rw [div_eq_inv_mul]
  have hcauchy : CauchySeq fun n => ∑ i ∈ Finset.range n, z ^ (i + 1) / (i + 1) := by
    rw [hSeq]
    refine Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded
      (b := 2 / ‖1 - z‖) (fun m n hmn => ?_) ?_ hbound
    · refine one_div_le_one_div_of_le (by positivity) ?_
      exact_mod_cast Nat.add_le_add_right hmn 1
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- hence the target partial sums converge to some `l`; it suffices to identify `l`.
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  suffices hll : l = -Complex.log (1 - z) by rw [← hll]; exact hl
  -- the `a`-partial sums `∑_{k<n} a k` tend to the same `l` (reindex: drops the `k=0` term).
  have hla : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, a k) Filter.atTop (nhds l) := by
    have hreindex : ∀ n, ∑ k ∈ Finset.range (n + 1), a k
        = ∑ i ∈ Finset.range n, z ^ (i + 1) / (i + 1) := by
      intro n
      rw [Finset.sum_range_succ']
      simp only [ha, pow_zero, Nat.cast_zero, div_zero, add_zero]
      exact Finset.sum_congr rfl fun i _ => by push_cast; ring
    have htail : Filter.Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), a k)
        Filter.atTop (nhds l) := by simpa only [hreindex] using hl
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp htail
  -- Abel's limit theorem identifies the radial interior limit with `l`.
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hla
  -- continuity of `log` off the branch cut: `-log (1 - x z) → -log (1 - z)`.
  have hmem : (1 : ℂ) - z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hcont : Filter.Tendsto (fun x : ℝ => -Complex.log (1 - (x : ℂ) * z))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (-Complex.log (1 - z))) := by
    have h1 : Filter.Tendsto (fun x : ℝ => (1 : ℂ) - (x : ℂ) * z)
        (nhdsWithin 1 (Set.Iio 1)) (nhds (1 - z)) := by
      have hc : Continuous (fun x : ℝ => (1 : ℂ) - (x : ℂ) * z) := by fun_prop
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    exact (h1.clog hmem).neg
  -- glue: rewrite `habel` (over `(𝓝[<] 1).map ofReal`) along the interior identity.
  have habel' : Filter.Tendsto (fun x : ℝ => -Complex.log (1 - (x : ℂ) * z))
      (nhdsWithin 1 (Set.Iio 1)) (nhds l) := by
    rw [Filter.tendsto_map'_iff] at habel
    refine habel.congr' ?_
    -- eventually `0 < x < 1`, where the interior Taylor series gives the identity.
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))] with x hx hx0
    have hx1 : x < 1 := Set.mem_Iio.mp hx
    have hxz : ‖(x : ℂ) * z‖ < 1 := by
      rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact hx1
    have heq := (Complex.hasSum_taylorSeries_neg_log hxz).tsum_eq
    simp only [Function.comp_apply]
    rw [← heq]
    refine tsum_congr fun n => ?_
    simp only [ha]
    rw [mul_pow]; ring
  -- the two limits of the same net agree, so `l = -log (1 - z)`.
  exact tendsto_nhds_unique habel' hcont

/-- C6-c1 (eq:classical 6.1, TeX 2030–2038): the Gauss-sum/Fourier
rearrangement of the L-series for `Re s > 1`. -/
theorem LSeries_eq_gaussSum_inv_mul_sum {θ : DirichletCharacter ℂ N}
    (hθ : θ.IsPrimitive) (hθ1 : θ ≠ 1) {ε : ℂ}
    (hε : IsPrimitiveRoot ε N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => θ n) s
      = (gaussSum θ⁻¹ (AddChar.zmodChar N hε.pow_eq_one))⁻¹
        * ∑ c : (ZMod N)ˣ, θ⁻¹ (c : ZMod N)
          * LSeries (fun n => ε ^ (n * ((c : ZMod N)).val)) s := by sorry

/-- **RJW Theorem 6.1(i)** (`s=1 theorem`(i), TeX 1989–1991): "We have
`L(θ,1) = −G(θ⁻¹)⁻¹ Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·log(1−ε_N^c)`." -/
theorem LFunction_one_eq {θ : DirichletCharacter ℂ N} (hθ : θ.IsPrimitive)
    (hθ1 : θ ≠ 1) {ε : ℂ} (hε : IsPrimitiveRoot ε N) :
    LFunction θ 1
      = -(gaussSum θ⁻¹ (AddChar.zmodChar N hε.pow_eq_one))⁻¹
        * ∑ c : (ZMod N)ˣ, θ⁻¹ (c : ZMod N)
          * Complex.log (1 - ε ^ ((c : ZMod N)).val) := by sorry

end ValuesAtOneComplex

end PadicLFunctions
