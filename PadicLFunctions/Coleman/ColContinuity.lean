/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.IwasawaProof.FundamentalSequence
import PadicLFunctions.IwasawaProof.Generators

/-!
# Continuity of the Coleman map (RJW §13 / IMC analytic core)

This file builds the topology/continuity layer needed to cross from the dense
`ℤ_p[𝒢]`-span of Dirac scalars to the full `Λ(𝒢)` action, closing the §12.5 image
computation `Col '' 𝒞_{∞,1} = I(𝒢)ζ_p`.

## Main constructions

* `PadicMeasure.instTopologicalSpace`: the weak-* topology on `Λ = C(X,ℤ_[p]) →ₗ ℤ_[p]`
  (pointwise convergence: `μ_j → μ` iff `μ_j f → μ f` for every `f`), as the topology
  induced by `DFunLike.coe` from the product topology on `C(X,ℤ_[p]) → ℤ_[p]`.
* `Continuous (evalPi · n)`: evaluation at `π_n` is coefficientwise-continuous on
  `ℤ_p⟦T⟧` (the `PowerSeries.WithPiTopology`).
* `Continuous (colemanPipe p)`: the post-`colemanSeries` pipeline
  `g ↦ unitsCmul invCM ((mahler⁻¹ (dlog g)).comp extendByZero)` is weak-* continuous
  on the `𝒩`-fixed units `𝒲ˣ` (where `Ring.inverse` is continuous via the
  compact-Hausdorff homeomorphism trick), and `Col u = colemanPipe (colemanSeries u)`.
-/

open PadicLFunctions PadicLFunctions.Coleman
open scoped PowerSeries.WithPiTopology fwdDiff

noncomputable section

/-! ## The weak-* topology on `PadicMeasure` -/

namespace PadicMeasure

variable (p : ℕ) [hp : Fact p.Prime]
variable {X : Type*} [TopologicalSpace X]

/-- The weak-* topology on `Λ(X) = C(X,ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`: the coarsest topology making
every evaluation `μ ↦ μ f` continuous, i.e. the topology of pointwise convergence on
functionals. Induced from the product topology on `C(X,ℤ_[p]) → ℤ_[p]` by the coercion. -/
instance instTopologicalSpace : TopologicalSpace (PadicMeasure p X) :=
  TopologicalSpace.induced (DFunLike.coe) inferInstance

/-- Evaluation `μ ↦ μ f` is weak-* continuous. -/
theorem continuous_eval (f : C(X, ℤ_[p])) :
    Continuous (fun μ : PadicMeasure p X => μ f) :=
  (continuous_apply f).comp continuous_induced_dom

/-- A net/map into `PadicMeasure` is continuous iff every evaluation is. -/
theorem continuous_iff_eval {Y : Type*} [TopologicalSpace Y] (g : Y → PadicMeasure p X) :
    Continuous g ↔ ∀ f : C(X, ℤ_[p]), Continuous (fun y => g y f) := by
  rw [continuous_induced_rng, continuous_pi_iff]
  rfl

/-- `PadicMeasure p X` is Hausdorff (weak-*): two measures equal at every `f` are equal. -/
instance instT2Space : T2Space (PadicMeasure p X) := by
  refine ⟨fun μ ν hμν => ?_⟩
  have hinj : Function.Injective (DFunLike.coe : PadicMeasure p X → (C(X, ℤ_[p]) → ℤ_[p])) :=
    DFunLike.coe_injective
  exact separated_by_continuous continuous_induced_dom (fun h => hμν (hinj h))

/-- Right multiplication `s ↦ s * ν` is weak-* continuous on `Λ(ℤ_p^×)`: by the convolution
formula `(s * ν) f = s (innerInt ν (f.comp mulCM₂))`, it is the (continuous) evaluation of `s`
at the *fixed* function `innerInt ν (f.comp mulCM₂)` (independent of `s`). -/
theorem continuous_mul_right (ν : PadicMeasure p ℤ_[p]ˣ) :
    Continuous (fun s : PadicMeasure p ℤ_[p]ˣ => s * ν) := by
  rw [continuous_iff_eval]
  intro f
  simpa only [PadicMeasure.units_mul_apply] using
    continuous_eval p (PadicMeasure.innerInt p ν (f.comp (PadicMeasure.unitsMulCM₂ p)))

/-- Scalar multiplication `c ↦ c • μ` (for a fixed measure `μ`) is weak-* continuous in the
scalar `c : ℤ_[p]`: `(c • μ) f = c * (μ f)` is continuous in `c`. -/
theorem continuous_smul_scalar (μ : PadicMeasure p X) :
    Continuous (fun c : ℤ_[p] => c • μ) := by
  rw [continuous_iff_eval]
  intro f
  simp only [LinearMap.smul_apply, smul_eq_mul]
  exact continuous_id.mul continuous_const

/-- **A closed additive subgroup of `Λ` is a `ℤ_[p]`-submodule.** Since `ℕ ↪ ℤ_[p]` is dense
and `c ↦ c • x` is weak-* continuous, `ℤ_[p] • x = closure(ℤ • x) ⊆ H` for `x ∈ H` closed. -/
theorem smul_mem_of_isClosed_subgroup {H : AddSubgroup (PadicMeasure p X)}
    (hH : IsClosed (H : Set (PadicMeasure p X))) (c : ℤ_[p]) {x : PadicMeasure p X}
    (hx : x ∈ H) : c • x ∈ H := by
  -- `ℕ • x ⊆ H`, `ℕ ↪ ℤ_[p]` dense, `c ↦ c • x` continuous ⟹ `c • x ∈ closure H = H`
  have hnat : ∀ k : ℕ, (k : ℤ_[p]) • x ∈ H := by
    intro k
    rw [Nat.cast_smul_eq_nsmul ℤ_[p] k x]
    exact nsmul_mem hx k
  have hmem : c • x ∈ closure (H : Set (PadicMeasure p X)) := by
    have hsub : ((fun c : ℤ_[p] => c • x) '' Set.range (Nat.cast : ℕ → ℤ_[p]))
        ⊆ (H : Set (PadicMeasure p X)) := by
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩; exact hnat k
    have hrange : Set.range (fun c : ℤ_[p] => c • x)
        ⊆ closure ((fun c : ℤ_[p] => c • x) '' Set.range (Nat.cast : ℕ → ℤ_[p])) := by
      have h1 : Set.range (fun c : ℤ_[p] => c • x)
          = (fun c : ℤ_[p] => c • x) '' closure (Set.range (Nat.cast : ℕ → ℤ_[p])) := by
        rw [PadicInt.denseRange_natCast.closure_range, Set.image_univ]
      rw [h1]
      exact image_closure_subset_closure_image (continuous_smul_scalar p x)
    exact closure_mono hsub (hrange ⟨c, rfl⟩)
  rwa [hH.closure_eq] at hmem

/-! ### Density of the Dirac span (weak-*) -/

/-- The level-`n` Dirac approximation of a measure on `ℤ_p^×`:
`D_n(μ) = ∑_{g ∈ (ℤ/p^n)ˣ} μ(𝟙_{g\text{-fibre}}) · [rep g]`, a `ℤ_[p]`-combination of
Dirac masses agreeing with `μ` on every level-`n` indicator. -/
def approxDirac (μ : PadicMeasure p ℤ_[p]ˣ) (n : ℕ) : PadicMeasure p ℤ_[p]ˣ :=
  if hn : 0 < n then
    ∑ g : (ZMod (p ^ n))ˣ, μ (levelChar p n g) •
      dirac p ((unitsToZModPow_surjective p n hn g).choose)
  else 0

/-- `D_n(μ)` agrees with `μ` on the level-`n` indicators: `D_n(μ)(𝟙_h) = μ(𝟙_h)`. -/
theorem approxDirac_levelChar {μ : PadicMeasure p ℤ_[p]ˣ} {n : ℕ} (hn : 0 < n)
    (h : (ZMod (p ^ n))ˣ) : approxDirac p μ n (levelChar p n h) = μ (levelChar p n h) := by
  classical
  rw [approxDirac, dif_pos hn]
  rw [show (∑ g : (ZMod (p ^ n))ˣ, μ (levelChar p n g) •
        dirac p ((unitsToZModPow_surjective p n hn g).choose)) (levelChar p n h)
      = ∑ g : (ZMod (p ^ n))ˣ, μ (levelChar p n g) *
          (dirac p ((unitsToZModPow_surjective p n hn g).choose)) (levelChar p n h) from by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun g _ => by rw [LinearMap.smul_apply, smul_eq_mul]]
  rw [Finset.sum_eq_single h]
  · rw [dirac_apply, levelChar_apply_eq p (unitsToZModPow_surjective p n hn h).choose_spec, mul_one]
  · intro g _ hgh
    rw [dirac_apply, levelChar_apply_ne p ?_, mul_zero]
    rw [(unitsToZModPow_surjective p n hn g).choose_spec]; exact hgh
  · exact fun hh => absurd (Finset.mem_univ _) hh

/-- `D_n(μ)` agrees with `μ` on any locally constant function `g` that factors through level
`n` (i.e. constant on level-`n` fibres). -/
theorem approxDirac_apply_eq {μ : PadicMeasure p ℤ_[p]ˣ} {n : ℕ} (hn : 0 < n)
    {g : LocallyConstant ℤ_[p]ˣ ℤ_[p]}
    (hfac : ∀ u v : ℤ_[p]ˣ, unitsToZModPow p n u = unitsToZModPow p n v → g u = g v) :
    approxDirac p μ n (g : C(ℤ_[p]ˣ, ℤ_[p])) = μ (g : C(ℤ_[p]ˣ, ℤ_[p])) := by
  classical
  -- `g = ∑_c g(rep c) • 𝟙_c` (level-`n` indicator decomposition, cf. `levelMap_jointly_injective`)
  have hg : (g : C(ℤ_[p]ˣ, ℤ_[p]))
      = ∑ c : (ZMod (p ^ n))ˣ,
          g ((unitsToZModPow_surjective p n hn c).choose) • levelChar p n c := by
    ext u
    rw [show (∑ c : (ZMod (p ^ n))ˣ,
        g ((unitsToZModPow_surjective p n hn c).choose) • levelChar p n c) u
        = ∑ c : (ZMod (p ^ n))ˣ,
          g ((unitsToZModPow_surjective p n hn c).choose) * levelChar p n c u from by
      simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
        Pi.smul_apply, smul_eq_mul]]
    rw [Finset.sum_eq_single (unitsToZModPow p n u)]
    · rw [levelChar_apply_eq p rfl, mul_one]
      exact (hfac _ u ((unitsToZModPow_surjective p n hn _).choose_spec)).symm
    · intro c _ hcu
      rw [levelChar_apply_ne p fun hc => hcu hc.symm, mul_zero]
    · exact fun hu => absurd (Finset.mem_univ _) hu
  rw [hg, map_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, map_smul, approxDirac_levelChar p hn c]

/-- **The Dirac span is weak-* dense**: the level-`n` Dirac approximations converge to `μ`,
`D_n(μ) f → μ f` for every test `f`. Given `ε`, approximate `f` by an lc `g` (`‖f-g‖ ≤ ε`)
factoring through some level `N`; for `n ≥ N`, `D_n(μ)` agrees with `μ` on `g`, so
`‖D_n(μ) f - μ f‖ ≤ ‖f - g‖ ≤ ε` by the operator bound `‖·f‖ ≤ ‖f‖`. -/
theorem tendsto_approxDirac (μ : PadicMeasure p ℤ_[p]ˣ) :
    Filter.Tendsto (fun n => approxDirac p μ n) Filter.atTop (nhds μ) := by
  rw [nhds_induced, Filter.tendsto_comap_iff, tendsto_pi_nhds]
  intro f
  change Filter.Tendsto (fun n => approxDirac p μ n f) Filter.atTop (nhds (μ f))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg⟩ := exists_locallyConstant_norm_sub_le p f (half_pos hε)
  have hgε : ‖f - (g : C(ℤ_[p]ˣ, ℤ_[p]))‖ < ε := lt_of_le_of_lt hg (by linarith)
  obtain ⟨N, hN, hfac⟩ := exists_level_factorization p g
  refine ⟨N, fun n hn => ?_⟩
  have hnpos : 0 < n := lt_of_lt_of_le hN hn
  -- `g` factors through level `n ≥ N`
  have hfacn : ∀ u v : ℤ_[p]ˣ, unitsToZModPow p n u = unitsToZModPow p n v → g u = g v := by
    intro u v huv
    exact hfac u v (by rw [unitsToZModPow_le p hn u, unitsToZModPow_le p hn v, huv])
  have hgeq : approxDirac p μ n (g : C(ℤ_[p]ˣ, ℤ_[p])) = μ (g : C(ℤ_[p]ˣ, ℤ_[p])) :=
    approxDirac_apply_eq p hnpos hfacn
  -- `D_n(μ) f − μ f = D_n(μ)(f − g) + μ(g − f)`
  have hsplit : approxDirac p μ n f - μ f
      = approxDirac p μ n (f - (g : C(ℤ_[p]ˣ, ℤ_[p]))) + μ ((g : C(ℤ_[p]ˣ, ℤ_[p])) - f) := by
    rw [map_sub, map_sub, hgeq]; ring
  rw [dist_eq_norm, hsplit]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
  rw [max_lt_iff]
  refine ⟨lt_of_le_of_lt (norm_apply_le p _ _) hgε, ?_⟩
  refine lt_of_le_of_lt (norm_apply_le p _ _) ?_
  rw [show (g : C(ℤ_[p]ˣ, ℤ_[p])) - f = -(f - (g : C(ℤ_[p]ˣ, ℤ_[p]))) from by ring, norm_neg]
  exact hgε

/-- **Closure-crossing for a principal ideal**: if `H` is a *closed* additive subgroup of
`Λ(ℤ_p^×)` containing `[a] · ν` for every group element `a ∈ ℤ_p^×`, then it contains the whole
principal ideal `r · ν` (`r ∈ Λ`). The Dirac span is weak-* dense (`tendsto_approxDirac`) and
`s ↦ s · ν` is continuous (`continuous_mul_right`), so `D_n(r) · ν → r · ν` with each
`D_n(r) · ν ∈ H` (a finite `ℤ_[p]`-combination of `[a] · ν`, using `H` `ℤ_[p]`-stable as a
closed subgroup), hence `r · ν ∈ closure H = H`. -/
theorem mul_mem_of_dirac_mul_mem {H : AddSubgroup (PadicMeasure p ℤ_[p]ˣ)}
    (hH : IsClosed (H : Set (PadicMeasure p ℤ_[p]ˣ))) {ν : PadicMeasure p ℤ_[p]ˣ}
    (hν : ∀ a : ℤ_[p]ˣ, dirac p a * ν ∈ H) (r : PadicMeasure p ℤ_[p]ˣ) :
    r * ν ∈ H := by
  classical
  -- each `D_n(r) · ν ∈ H`
  have hstep : ∀ n, approxDirac p r n * ν ∈ H := by
    intro n
    rw [approxDirac]
    by_cases hn : 0 < n
    · rw [dif_pos hn, Finset.sum_mul]
      refine AddSubgroup.sum_mem _ fun g _ => ?_
      rw [smul_mul_assoc]
      exact smul_mem_of_isClosed_subgroup p hH _ (hν _)
    · rw [dif_neg hn, zero_mul]; exact zero_mem _
  -- `D_n(r) · ν → r · ν`
  have htend : Filter.Tendsto (fun n => approxDirac p r n * ν) Filter.atTop (nhds (r * ν)) :=
    ((continuous_mul_right p ν).tendsto r).comp (tendsto_approxDirac p r)
  have hmem : r * ν ∈ closure (H : Set (PadicMeasure p ℤ_[p]ˣ)) :=
    mem_closure_of_tendsto htend (Filter.Eventually.of_forall hstep)
  rwa [hH.closure_eq, SetLike.mem_coe] at hmem

/-! ### Compactness of `Λ(ℤ_p^×)` and closedness of the ζ-ideal -/

/-- The coercion `DFunLike.coe : Λ(ℤ_p^×) → (C(ℤ_p^×,ℤ_[p]) → ℤ_[p])` has *closed* range:
its image is exactly the functionals satisfying additivity and `ℤ_[p]`-homogeneity, two
closed conditions (each is an intersection of equalities of weak-* continuous evaluations). -/
theorem isClosed_range_coe :
    IsClosed (Set.range (DFunLike.coe :
      PadicMeasure p ℤ_[p]ˣ → (C(ℤ_[p]ˣ, ℤ_[p]) → ℤ_[p]))) := by
  have hset : Set.range (DFunLike.coe :
        PadicMeasure p ℤ_[p]ˣ → (C(ℤ_[p]ˣ, ℤ_[p]) → ℤ_[p]))
      = {F | (∀ a b, F (a + b) = F a + F b)} ∩ {F | ∀ (c : ℤ_[p]) a, F (c • a) = c • F a} := by
    ext F
    simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨μ, rfl⟩; exact ⟨fun a b => map_add μ a b, fun c a => map_smul μ c a⟩
    · rintro ⟨hadd, hsmul⟩; exact ⟨{ toFun := F, map_add' := hadd, map_smul' := hsmul }, rfl⟩
  rw [hset]
  apply IsClosed.inter
  · rw [Set.setOf_forall]; refine isClosed_iInter fun a => ?_
    rw [Set.setOf_forall]; refine isClosed_iInter fun b => ?_
    exact isClosed_eq (continuous_apply (a + b)) ((continuous_apply a).add (continuous_apply b))
  · rw [Set.setOf_forall]; refine isClosed_iInter fun c => ?_
    rw [Set.setOf_forall]; refine isClosed_iInter fun a => ?_
    exact isClosed_eq (continuous_apply (c • a)) ((continuous_apply a).const_smul c)

/-- **`Λ(ℤ_p^×)` is weak-* compact** (a p-adic Banach–Alaoglu). The coercion is inducing onto
the compact product `∏_f ℤ_[p]` (Tychonoff: `ℤ_[p]` compact) with *closed* range
(`isClosed_range_coe`), so `Λ(ℤ_p^×)` is a closed subspace of a compact space. -/
instance instCompactSpace : CompactSpace (PadicMeasure p ℤ_[p]ˣ) := by
  rw [← isCompact_univ_iff]
  have hind : Topology.IsInducing
      (DFunLike.coe : PadicMeasure p ℤ_[p]ˣ → _) := ⟨rfl⟩
  rw [hind.isCompact_iff, Set.image_univ]
  exact (isClosed_range_coe p).isCompact

/-- **Every principal ideal `(ν)` of `Λ(ℤ_p^×)` is weak-* closed**: it is the image of the
compact space `Λ` under the continuous map `r ↦ r·ν` (`continuous_mul_right`), hence compact,
hence closed (`Λ` is Hausdorff). -/
theorem isClosed_span_singleton (ν : PadicMeasure p ℤ_[p]ˣ) :
    IsClosed ((Ideal.span {ν} : Ideal (PadicMeasure p ℤ_[p]ˣ)) :
      Set (PadicMeasure p ℤ_[p]ˣ)) := by
  have hrange : ((Ideal.span {ν} : Ideal (PadicMeasure p ℤ_[p]ˣ)) :
        Set (PadicMeasure p ℤ_[p]ˣ)) = Set.range (fun r => r * ν) := by
    ext x
    simp only [SetLike.mem_coe, Ideal.mem_span_singleton, Set.mem_range]
    exact ⟨fun ⟨r, hr⟩ => ⟨r, by rw [hr, mul_comm]⟩, fun ⟨r, hr⟩ => ⟨r, by rw [← hr, mul_comm]⟩⟩
  rw [hrange, ← Set.image_univ]
  exact (isCompact_univ.image (continuous_mul_right p ν)).isClosed

/-- **`I(𝒢)ζ_p` is weak-* closed.** By the principal description `I(𝒢)ζ_p = (zetaNum a₀)`
(`zetaIdeal_eq_span`, the `([a₀]−1)·ζ_p`-witness at the topological generator `a₀`), it is a
principal ideal, hence closed by `isClosed_span_singleton` (compactness of `Λ`). This supplies
the *closedness* half of the `⊆` direction of the §12.5 image computation — independently of the
image identity itself, so it is not circular. -/
theorem isClosed_zetaIdeal (hp2 : p ≠ 2) :
    IsClosed ((zetaIdeal p hp2 : Ideal (PadicMeasure p ℤ_[p]ˣ)) :
      Set (PadicMeasure p ℤ_[p]ˣ)) := by
  have hb_gen : ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n
        (exists_nat_topological_generator p hp2).choose_spec.choose) = ⊤ :=
    (exists_nat_topological_generator p hp2).choose_spec.choose_spec.2.2
  have hνeq : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p)
        (dirac p (exists_nat_topological_generator p hp2).choose_spec.choose - 1)
        * padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p)
          (zetaNum p (exists_nat_topological_generator p hp2).choose) := by
    rw [padicZeta]; exact IsLocalization.mk'_spec' (QuotientField p) _ _
  rw [zetaIdeal_eq_span p hp2 hb_gen hνeq]
  exact isClosed_span_singleton p _

end PadicMeasure

/-! ## Continuity of evaluation at `π_n` -/

namespace PadicLFunctions.Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-- `PowerSeries ℤ_[p]` with the coefficientwise topology is (sequentially) metrizable, so
continuity equals sequential continuity (it is the countable product `(Unit →₀ ℕ) → ℤ_[p]`
of the metric space `ℤ_[p]`). -/
instance : SequentialSpace (PowerSeries ℤ_[p]) :=
  inferInstanceAs (SequentialSpace ((Unit →₀ ℕ) → ℤ_[p]))

/-- **Evaluation at `π_n` is continuous** (`n ≥ 1`): `f ↦ f(π_n)` is sequentially continuous
on `ℤ_p⟦T⟧` (`tendsto_evalPi_of_tendsto`), and `ℤ_p⟦T⟧` is sequential, so it is continuous. -/
theorem continuous_evalPi {n : ℕ} (hn : 1 ≤ n) :
    Continuous (fun f : PowerSeries ℤ_[p] => evalPi p f n) := by
  refine SeqContinuous.continuous (fun {g h} hg => ?_)
  exact tendsto_evalPi_of_tendsto p hg hn

/-! ## Continuity of the measure-side pipeline `ofPowerSeries`/`Col` -/

/-- **`g ↦ (μ_g)(ψ)` is coefficientwise-continuous** for a fixed test function `ψ`:
`(ofPowerSeries g)(ψ) = ∑'_n Δⁿψ(0) · gₙ` is a uniform limit (in `g`) of its finite partial
sums `S_N(g) = ∑_{n<N} Δⁿψ(0) · gₙ` (each continuous, the tail `≤ sup_{n≥N}‖Δⁿψ(0)‖ → 0`
uniformly since `‖gₙ‖ ≤ 1`), hence continuous. -/
theorem continuous_ofPowerSeries_apply (ψ : C(ℤ_[p], ℤ_[p])) :
    Continuous (fun g : PowerSeries ℤ_[p] => PadicMeasure.ofPowerSeries p g ψ) := by
  -- the tail bound `‖∑'_{n≥N} Δⁿψ(0)·gₙ‖ ≤ sup_{n≥N} ‖Δⁿψ(0)‖` and `Δⁿψ(0) → 0`
  have hΔ : Filter.Tendsto (fun n => ‖Δ_[1]^[n] (⇑ψ) 0‖) Filter.atTop (nhds 0) := by
    have h := PadicInt.fwdDiff_tendsto_zero ψ
    rw [tendsto_zero_iff_norm_tendsto_zero] at h
    exact h
  refine continuous_of_uniform_approx_of_continuous (fun U hU => ?_)
  -- reduce the uniformity `U` to a metric ball of radius `ε`
  rw [Metric.mem_uniformity_dist] at hU
  obtain ⟨ε, hε, hball⟩ := hU
  -- choose `N` with `‖Δⁿψ(0)‖ < ε/2` for `n ≥ N`
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop).1 hΔ (ε / 2) (half_pos hε)
  refine ⟨fun g => ∑ n ∈ Finset.range N, Δ_[1]^[n] (⇑ψ) 0 * PowerSeries.coeff n g, ?_, ?_⟩
  · exact continuous_finsetSum _ fun n _ =>
      continuous_const.mul (PowerSeries.WithPiTopology.continuous_coeff ℤ_[p] n)
  · intro g
    refine hball ?_
    rw [dist_eq_norm]
    have hsummable : Summable fun n => Δ_[1]^[n] (⇑ψ) 0 * PowerSeries.coeff n g := by
      refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
      rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _)
        (fun n => (?_ : ‖Δ_[1]^[n] (⇑ψ) 0 * PowerSeries.coeff n g‖ ≤ ‖Δ_[1]^[n] (⇑ψ) 0‖)) hΔ
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
    -- `ofPowerSeries g ψ − S_N(g) = ∑'_{n} Δ^{n+N}ψ(0)·g_{n+N}`
    have hdiff : PadicMeasure.ofPowerSeries p g ψ
          - ∑ n ∈ Finset.range N, Δ_[1]^[n] (⇑ψ) 0 * PowerSeries.coeff n g
        = ∑' n, (Δ_[1]^[n + N] (⇑ψ) 0 * PowerSeries.coeff (n + N) g) := by
      have hval : PadicMeasure.ofPowerSeries p g ψ
          = ∑' n, Δ_[1]^[n] (⇑ψ) 0 * PowerSeries.coeff n g := rfl
      rw [hval, ← (hsummable.sum_add_tsum_nat_add N)]; ring
    rw [hdiff]
    -- the tail norm is `≤ ε/2 < ε`
    refine lt_of_le_of_lt (IsUltrametricDist.norm_tsum_le_of_forall_le (C := ε / 2)
      (fun n => ?_)) (by linarith)
    rw [norm_mul]
    have hterm : ‖Δ_[1]^[n + N] (⇑ψ) 0‖ < ε / 2 := by
      have h := hN (n + N) (by omega)
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h
    refine le_of_lt (lt_of_le_of_lt ?_ hterm)
    exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)

/-- **The measure-side Coleman pipeline, paired form**: from a series `f` and its inverse
`finv` (kept as a separate argument to sidestep the discontinuity of `Ring.inverse`), the
measure `x⁻¹ · Res_{ℤ_p^×}(𝒜⁻¹((1+T)·f′·finv))` — i.e. `Col` with `Ring.inverse f` replaced by
the supplied `finv`. When `finv = Ring.inverse f` this is exactly `Col` of the corresponding
unit system (`colemanPipe2_eq_Col`). -/
def colemanPipe2 (f finv : PowerSeries ℤ_[p]) : PadicMeasure p ℤ_[p]ˣ :=
  PadicMeasure.unitsCmul p (PadicMeasure.invCM p)
    (((PadicMeasure.mahlerLinearEquiv p).symm
        ((1 + PowerSeries.X) * PowerSeries.derivativeFun f * finv)).comp
      (PadicMeasure.extendByZero p))

/-- `Col u = colemanPipe2 (colemanSeries u) (Ring.inverse (colemanSeries u))`: the pipeline at
`(f, finv) = (colemanSeries u, (colemanSeries u)⁻¹)` is `Col u`, since `dlog f =
(1+T)·f′·(Ring.inverse f)` by definition. -/
theorem colemanPipe2_eq_Col (u : NormCompatUnits p) :
    colemanPipe2 p (colemanSeries p u) (Ring.inverse (colemanSeries p u)) = Col p u := rfl

/-- **The paired pipeline is jointly continuous** `(f, finv) ↦ colemanPipe2 f finv`. For a fixed
test function `φ`, `(colemanPipe2 f finv)(φ) = (ofPowerSeries ((1+T)·f′·finv))(ψ)` with `ψ =
extendByZero(invCM·φ)` fixed; this is continuous in the series `(1+T)·f′·finv`
(`continuous_ofPowerSeries_apply`), which is continuous in `(f, finv)` (coefficientwise:
`derivativeFun` and `*` are continuous on the topological ring `ℤ_p⟦T⟧`). -/
theorem continuous_colemanPipe2 :
    Continuous (Function.uncurry (colemanPipe2 p)) := by
  rw [PadicMeasure.continuous_iff_eval]
  intro φ
  -- the inner power series `(f, finv) ↦ (1+X)·f′·finv` is continuous
  have hseries : Continuous (fun q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] =>
      (1 + PowerSeries.X) * PowerSeries.derivativeFun q.1 * q.2) := by
    refine (continuous_const.mul ?_).mul continuous_snd
    refine continuous_of_coeff _ (fun n => ?_)
    simp only [PowerSeries.coeff_derivativeFun]
    exact (PowerSeries.WithPiTopology.continuous_coeff ℤ_[p] (n + 1)).comp continuous_fst |>.mul
      continuous_const
  -- the evaluation factors through `ofPowerSeries (·)(ψ)` at the fixed `ψ`
  have hval : (fun q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] =>
        Function.uncurry (colemanPipe2 p) q φ)
      = fun q => PadicMeasure.ofPowerSeries p
          ((1 + PowerSeries.X) * PowerSeries.derivativeFun q.1 * q.2)
          ((PadicMeasure.extendByZero p (PadicMeasure.invCM p * φ))) := by
    funext q
    rfl
  rw [hval]
  exact (continuous_ofPowerSeries_apply p _).comp hseries

/-! ## Closedness of the cyclotomic-closure value sets and of `Col '' 𝒞_{∞,1}` -/

/-- `K p n` is closed in `ℂ_[p]` (re-derived; the `Theorem.lean` version is private): a
finite-dimensional `ℚ_[p]`-subspace of a normed space over the complete `ℚ_[p]` is complete,
hence closed. -/
theorem isClosed_KCp (n : ℕ) : IsClosed (X := ℂ_[p]) (K p n : Set ℂ_[p]) := by
  haveI : FiniteDimensional ℚ_[p] (K p n).toSubmodule := by
    have hint : IsIntegral ℚ_[p] (zetaSys p n) :=
      ((zetaSys_primitiveRoot p n).isIntegral (pow_pos hp.out.pos n)).tower_top
    exact IntermediateField.adjoin.finiteDimensional hint
  exact (K p n).toSubmodule.closed_of_finiteDimensional

/-- `O p n` is closed in `ℂ_[p]` (`K p n` closed ∩ the closed unit ball). -/
theorem isClosed_OCp (n : ℕ) : IsClosed (X := ℂ_[p]) (O p n : Set ℂ_[p]) := by
  have h : (O p n : Set ℂ_[p]) = (K p n : Set ℂ_[p]) ∩ {x : ℂ_[p] | ‖x‖ ≤ 1} := rfl
  rw [h]
  exact (isClosed_KCp p n).inter (isClosed_le continuous_norm continuous_const)

/-- `localUnits p n` is closed in `ℂ_[p]ˣ`: both `(u : ℂ_[p]) ∈ O p n` and
`(u⁻¹ : ℂ_[p]) ∈ O p n` are closed conditions (`val`/`inv∘val` continuous, `O p n` closed). -/
theorem isClosed_localUnits (n : ℕ) :
    IsClosed (localUnits p n : Set ℂ_[p]ˣ) := by
  have h : (localUnits p n : Set ℂ_[p]ˣ)
      = (fun u : ℂ_[p]ˣ => (u : ℂ_[p])) ⁻¹' (O p n : Set ℂ_[p])
        ∩ (fun u : ℂ_[p]ˣ => ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) ⁻¹' (O p n : Set ℂ_[p]) := rfl
  rw [h]
  refine ((isClosed_OCp p n).preimage Units.continuous_val).inter
    ((isClosed_OCp p n).preimage ?_)
  exact Units.continuous_val.comp continuous_inv

/-- `localUnitsOne p n` is closed in `ℂ_[p]ˣ`: `localUnits` closed ∩ the closed condition
`‖(u:ℂ_[p]) − 1‖ < 1` (an ultrametric ball, hence clopen). -/
theorem isClosed_localUnitsOne (n : ℕ) :
    IsClosed (localUnitsOne p n : Set ℂ_[p]ˣ) := by
  have h : (localUnitsOne p n : Set ℂ_[p]ˣ)
      = (localUnits p n : Set ℂ_[p]ˣ)
        ∩ {u : ℂ_[p]ˣ | ‖(u : ℂ_[p]) - 1‖ < 1} := rfl
  rw [h]
  refine (isClosed_localUnits p n).inter ?_
  -- `{u | ‖val u − 1‖ < 1}` is the preimage of the clopen ultrametric ball `B(1,1) ⊆ ℂ_[p]`
  have hclopen : IsClosed {x : ℂ_[p] | ‖x - 1‖ < 1} := by
    have heq : {x : ℂ_[p] | ‖x - 1‖ < 1} = Metric.ball (1 : ℂ_[p]) 1 := by
      ext x; rw [Set.mem_setOf_eq, Metric.mem_ball, dist_eq_norm]
    rw [heq]
    exact IsUltrametricDist.isClosed_ball (1 : ℂ_[p]) 1
  have hpre : {u : ℂ_[p]ˣ | ‖(u : ℂ_[p]) - 1‖ < 1}
      = (fun u : ℂ_[p]ˣ => (u : ℂ_[p])) ⁻¹' {x : ℂ_[p] | ‖x - 1‖ < 1} := rfl
  rw [hpre]
  exact hclopen.preimage Units.continuous_val

/-- `cycloClosureOne p n` is closed in `ℂ_[p]ˣ`: the intersection of the (closed) topological
closure of the cyclotomic units with the closed `localUnits`/`localUnitsOne`. -/
theorem isClosed_cycloClosureOne (n : ℕ) :
    IsClosed (cycloClosureOne p n : Set ℂ_[p]ˣ) := by
  have h : (cycloClosureOne p n : Set ℂ_[p]ˣ)
      = ((cycloUnits p n).topologicalClosure : Set ℂ_[p]ˣ)
        ∩ (localUnits p n : Set ℂ_[p]ˣ) ∩ (localUnitsOne p n : Set ℂ_[p]ˣ) := by
    rw [cycloClosureOne, cycloClosure]; rfl
  rw [h]
  exact ((Subgroup.isClosed_topologicalClosure _).inter (isClosed_localUnits p n)).inter
    (isClosed_localUnitsOne p n)

/-- **The value set `C_n := val '' 𝒞_{n,1}` is closed in `ℂ_[p]`.** `Units.val` is a topological
embedding (ℂ_[p] is a normed field, `Units.isEmbedding_val₀`), `𝒞_{n,1}` is closed in `ℂ_[p]ˣ`,
and `𝒞_{n,1} ⊆ localUnitsOne` lands in the *clopen* ball `B(1,1)`, so the image cannot
accumulate at `0`: any limit `y ∈ closure C_n ⊆ B(1,1)` is a unit `val u` with `u ∈ closure 𝒞 =
𝒞`. -/
theorem isClosed_val_cycloClosureOne (n : ℕ) :
    IsClosed ((fun u : ℂ_[p]ˣ => (u : ℂ_[p])) '' (cycloClosureOne p n : Set ℂ_[p]ˣ)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro x y hx hxy
  -- each `x k = val (u k)` with `u k ∈ 𝒞_{n,1}`
  choose u hu hux using hx
  -- `‖y − 1‖ < 1` (the clopen ball `B(1,1)` is closed and contains every `x k`)
  have hyball : ‖y - 1‖ < 1 := by
    have hxball : ∀ k, ‖x k - 1‖ < 1 := by
      intro k
      rw [← hux k]
      have hmem : u k ∈ localUnitsOne p n := by
        have h := hu k
        rw [SetLike.mem_coe, cycloClosureOne, Subgroup.mem_inf] at h
        exact h.2
      exact ((mem_localUnitsOne_iff p).1 hmem).2
    have hball : IsClosed {z : ℂ_[p] | ‖z - 1‖ < 1} := by
      have heq : {z : ℂ_[p] | ‖z - 1‖ < 1} = Metric.ball (1 : ℂ_[p]) 1 := by
        ext z; rw [Set.mem_setOf_eq, Metric.mem_ball, dist_eq_norm]
      rw [heq]; exact IsUltrametricDist.isClosed_ball (1 : ℂ_[p]) 1
    exact hball.mem_of_tendsto hxy (Filter.Eventually.of_forall hxball)
  -- `‖y‖ = 1`, so `y ≠ 0` is a unit
  have hy0 : y ≠ 0 := by
    intro h
    rw [h] at hyball
    simp only [zero_sub, norm_neg, norm_one] at hyball
    exact lt_irrefl 1 hyball
  have hyunit : IsUnit y := isUnit_iff_ne_zero.2 hy0
  -- `u k → y.unit` in `ℂ_[p]ˣ` (`val` is a topological embedding) and `𝒞_{n,1}` is seq-closed
  have hutend : Filter.Tendsto u Filter.atTop (nhds hyunit.unit) := by
    rw [Units.isEmbedding_val₀.tendsto_nhds_iff]
    have hval : (fun k => ((u k : ℂ_[p]ˣ) : ℂ_[p])) = x := funext hux
    have hyval : ((hyunit.unit : ℂ_[p]ˣ) : ℂ_[p]) = y := IsUnit.unit_spec hyunit
    rw [show ((Units.val : ℂ_[p]ˣ → ℂ_[p]) ∘ u) = x from hval, hyval]
    exact hxy
  have hyu : hyunit.unit ∈ cycloClosureOne p n :=
    (isClosed_cycloClosureOne p n).isSeqClosed hu hutend
  exact ⟨hyunit.unit, hyu, IsUnit.unit_spec hyunit⟩

/-- The compact set of Coleman-series pairs realising `𝒞_{∞,1}`: pairs `(f, finv)` with
`f · finv = 1`, `f` `𝒩`-fixed, and `f(π_n) ∈ C_n := val '' 𝒞_{n,1}` for all `n ≥ 1`. -/
def colemanPairSet : Set (PowerSeries ℤ_[p] × PowerSeries ℤ_[p]) :=
  {q | q.1 * q.2 = 1 ∧ normOp q.1 = q.1 ∧
    ∀ n, 1 ≤ n → evalPi p q.1 n
      ∈ (fun u : ℂ_[p]ˣ => (u : ℂ_[p])) '' (cycloClosureOne p n : Set ℂ_[p]ˣ)}

/-- `colemanPairSet` is closed in `ℤ_p⟦T⟧ × ℤ_p⟦T⟧` (hence compact). The three conditions are
closed: `f·finv = 1` (continuous `*` into the T2 ring, `{1}` closed); `𝒩 f = f` (`normOp`
continuous); each `f(π_n) ∈ C_n` (`evalPi (·) n` continuous, `C_n` closed
`isClosed_val_cycloClosureOne`). -/
theorem isCompact_colemanPairSet : IsCompact (colemanPairSet p) := by
  refine IsClosed.isCompact ?_
  rw [show colemanPairSet p
      = {q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] | q.1 * q.2 = 1}
        ∩ {q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] | normOp q.1 = q.1}
        ∩ {q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] | ∀ n, 1 ≤ n →
            evalPi p q.1 n ∈ (fun u : ℂ_[p]ˣ => (u : ℂ_[p])) ''
              (cycloClosureOne p n : Set ℂ_[p]ˣ)} from by
    ext q; simp only [colemanPairSet, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto]
  have h1 : IsClosed {q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] | q.1 * q.2 = 1} :=
    isClosed_eq (continuous_fst.mul continuous_snd) continuous_const
  have h2 : IsClosed {q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] | normOp q.1 = q.1} :=
    isClosed_eq ((normOp_continuous p).comp continuous_fst) continuous_fst
  have h3 : IsClosed {q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] | ∀ n, 1 ≤ n →
      evalPi p q.1 n ∈ (fun u : ℂ_[p]ˣ => (u : ℂ_[p])) '' (cycloClosureOne p n : Set ℂ_[p]ˣ)} := by
    rw [show {q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] | ∀ n, 1 ≤ n →
        evalPi p q.1 n ∈ (fun u : ℂ_[p]ˣ => (u : ℂ_[p])) '' (cycloClosureOne p n : Set ℂ_[p]ˣ)}
        = ⋂ n, ⋂ (_ : 1 ≤ n), {q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] |
            evalPi p q.1 n ∈ (fun u : ℂ_[p]ˣ => (u : ℂ_[p])) ''
              (cycloClosureOne p n : Set ℂ_[p]ˣ)} from by
      ext q; simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    refine isClosed_iInter fun n => isClosed_iInter fun hn => ?_
    exact (isClosed_val_cycloClosureOne p n).preimage ((continuous_evalPi p hn).comp continuous_fst)
  exact (h1.inter h2).inter h3

/-- **`Col '' 𝒞_{∞,1} = colemanPipe2 '' colemanPairSet`.** For `c ∈ 𝒞_{∞,1}`, the pair
`(colemanSeries c, (colemanSeries c)⁻¹)` lies in `colemanPairSet` and maps to `Col c`.
Conversely, any `(f, finv) ∈ colemanPairSet` has `f` a `𝒩`-fixed unit (`f·finv = 1`) and
`f(π_n) ∈ C_n`, so `invColeman f ∈ 𝒞_{∞,1}` with `colemanSeries (invColeman f) = f` and
`finv = Ring.inverse f`, giving `colemanPipe2 f finv = Col (invColeman f)`. -/
theorem col_image_eq_pipe_image :
    Col p '' (cycloTower1 p : Set (NormCompatUnits p))
      = Function.uncurry (colemanPipe2 p) '' colemanPairSet p := by
  apply Set.eq_of_subset_of_subset
  · -- `⊆`: `c ↦ (colemanSeries c, (colemanSeries c)⁻¹)`
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨(colemanSeries p c, Ring.inverse (colemanSeries p c)), ⟨?_, ?_, ?_⟩, ?_⟩
    · exact Ring.mul_inverse_cancel _ (colemanSeries_isUnit p c)
    · exact normOp_colemanSeries p c
    · intro n hn
      refine ⟨c.elems n, hc n hn, ?_⟩
      exact (evalPi_colemanSeries p c hn).symm
    · exact colemanPipe2_eq_Col p c
  · -- `⊇`: `(f, finv) ↦ invColeman f`
    rintro _ ⟨⟨f, finv⟩, ⟨hfinv, hN, hC⟩, rfl⟩
    have hfunit : IsUnit f := IsUnit.of_mul_eq_one finv hfinv
    have hfinveq : finv = Ring.inverse f := by
      have hinv : Ring.inverse f * f = 1 := Ring.inverse_mul_cancel f hfunit
      calc finv = (Ring.inverse f * f) * finv := by rw [hinv, one_mul]
        _ = Ring.inverse f * (f * finv) := by rw [mul_assoc]
        _ = Ring.inverse f := by rw [hfinv, mul_one]
    set c := invColeman p f hfunit hN with hc
    have hcs : colemanSeries p c = f := colemanSeries_invColeman p f hfunit hN
    -- `c ∈ 𝒞_{∞,1}`: each `c.elems n ∈ 𝒞_{n,1}`
    have hccyclo : c ∈ cycloTower1 p := by
      intro n hn
      obtain ⟨w, hw, hwval⟩ := hC n hn
      -- `(c.elems n : ℂ_[p]) = evalPi (colemanSeries c) n = evalPi f n = val w`
      have hcval : ((c.elems n : ℂ_[p]ˣ) : ℂ_[p]) = (w : ℂ_[p]) := by
        rw [← evalPi_colemanSeries p c hn, hcs]; exact hwval.symm
      rw [show c.elems n = w from Units.ext hcval]
      exact hw
    refine ⟨c, hccyclo, ?_⟩
    rw [Function.uncurry_apply_pair, hfinveq, ← hcs, colemanPipe2_eq_Col]

/-- **`Col '' 𝒞_{∞,1}` is compact** (continuous image of the compact `colemanPairSet`), hence
closed in the weak-* topology on `Λ(ℤ_p^×)`. -/
theorem isCompact_col_image :
    IsCompact (Col p '' (cycloTower1 p : Set (NormCompatUnits p))) := by
  rw [col_image_eq_pipe_image]
  exact (isCompact_colemanPairSet p).image (continuous_colemanPipe2 p)

theorem isClosed_col_image :
    IsClosed (Col p '' (cycloTower1 p : Set (NormCompatUnits p))) :=
  (isCompact_col_image p).isClosed

end PadicLFunctions.Coleman
