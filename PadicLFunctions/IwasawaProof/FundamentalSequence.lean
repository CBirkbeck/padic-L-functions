/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.IwasawaProof.LogDerivative
import PadicLFunctions.IwasawaProof.Equivariance

/-!
# The fundamental exact sequence (RJW §12.2.2, TeX 3382–3441) — E12.3

`def:Zp(1)`, `lem:rest zp*` (already partly in `LogDerivative`), and `thm:fund exact seq`:
`0 → ℤ_p(1) → 𝒰_{∞,1} →[Col] Λ(𝒢) → ℤ_p(1) → 0` as `Λ(𝒢)`-modules. Skeleton.
-/

open PadicLFunctions PadicLFunctions.Coleman

noncomputable section

namespace PadicLFunctions.Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-- The cyclotomic generator `ξ_n` is a `1`-unit for `n ≥ 1`: `‖ξ_n − 1‖ < 1`
(`ξ_n − 1 = π_n` is the uniformiser, `norm_pi_lt_one`). -/
private theorem norm_zetaSys_sub_one_lt_one {n : ℕ} (hn : 1 ≤ n) :
    ‖zetaSys p n - 1‖ < 1 := by
  have := norm_pi_lt_one p hn; rwa [pi] at this

/-- **RJW def:Zp(1) (TeX 3407–3409)**: `ℤ_p(1) = {(ξ_n^a)_n : a ∈ ℤ_p} ⊂ 𝒰_∞`, the
integral Tate twist, realised as a subgroup of the unit tower. A system `u ∈ 𝒰_∞` lies
in `ℤ_p(1)` iff there is a single `a ∈ ℤ_p` with `u_n = ξ_n^a` (`zpPow`) for every
`n ≥ 1` (the level-`0` component is unconstrained, matching `compat`/`colemanSeries`).
The subgroup laws are the character laws of `zpPow` in the exponent: `a + b` for the
product, `0` for the identity, `−a` for the inverse. -/
def ZpOne : Subgroup (NormCompatUnits p) where
  carrier :=
    {u | ∃ a : ℤ_[p], ∀ n, 1 ≤ n → ((u.elems n : ℂ_[p]ˣ) : ℂ_[p]) = zpPow p (zetaSys p n) a}
  mul_mem' := by
    rintro u v ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, fun n hn => ?_⟩
    have hval : ((((u * v).elems n) : ℂ_[p]ˣ) : ℂ_[p])
        = ((u.elems n : ℂ_[p]ˣ) : ℂ_[p]) * ((v.elems n : ℂ_[p]ˣ) : ℂ_[p]) := by
      change (((u.elems n * v.elems n : ℂ_[p]ˣ)) : ℂ_[p]) = _
      rw [Units.val_mul]
    rw [hval, ha n hn, hb n hn, zpPow_add p (norm_zetaSys_sub_one_lt_one p hn)]
  one_mem' := by
    refine ⟨0, fun n hn => ?_⟩
    have h1 : ‖(1 : ℂ_[p]) - 1‖ < 1 := by simp
    rw [show (((1 : NormCompatUnits p).elems n : ℂ_[p]ˣ) : ℂ_[p]) = 1 from rfl,
      show (0 : ℤ_[p]) = ((0 : ℕ) : ℤ_[p]) by norm_cast,
      zpPow_natCast p (norm_zetaSys_sub_one_lt_one p hn), pow_zero]
  inv_mem' := by
    rintro u ⟨a, ha⟩
    refine ⟨-a, fun n hn => ?_⟩
    have hz1 : ‖zetaSys p n - 1‖ < 1 := norm_zetaSys_sub_one_lt_one p hn
    have hval : (((u⁻¹).elems n : ℂ_[p]ˣ) : ℂ_[p]) = (((u.elems n : ℂ_[p]ˣ) : ℂ_[p]))⁻¹ := by
      change (((u.elems n)⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = _
      rw [Units.val_inv_eq_inv_val]
    have hmul : zpPow p (zetaSys p n) a * zpPow p (zetaSys p n) (-a) = 1 := by
      rw [← zpPow_add p hz1, add_neg_cancel,
        show (0 : ℤ_[p]) = ((0 : ℕ) : ℤ_[p]) by norm_cast, zpPow_natCast p hz1, pow_zero]
    rw [hval, ha n hn]
    exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hmul)).symm

/-- **RJW thm:fund exact seq (TeX 3411–3418), left-exactness**: the kernel of `Col` on
`𝒰_{∞,1}` is `ℤ_p(1)`.

OBSTACLE (one documented `sorry`, T-E12.3a). The proof pulls the kernel of the composite
`Col = (x⁻¹·) ∘ Res_{ℤ_p^×} ∘ 𝒜⁻¹ ∘ ∂log ∘ colemanSeries` back through each arrow:
* `∂log` (`rem:ker Δ`, `dlog_eq_zero_normOp_fixed`) and the `(1−φ)`/restriction step
  identify the kernel with the constants, lifting to the `ℤ_p`-factor `ℤ_p(1)`
  (RJW TeX 3429–3431);
* the realising identity is `colemanSeries u = binomialSeries a` for `u ∈ ZpOne p`
  with parameter `a` (then `∂log(binomialSeries a) = C a`, a constant, whose Mahler
  inverse `𝒜⁻¹(C a)` is supported at `0 ∉ ℤ_p^×`, so `Res_{ℤ_p^×} = 0`, giving the
  reverse inclusion `ZpOne ⊆ ker Col`).

Two pieces of infrastructure are genuinely absent / inaccessible here and block both
inclusions:
1. `colemanSeries u = binomialSeries a` needs `normOp (binomialSeries a) = binomialSeries a`
   (the `𝒩`-fixedness of the formal `(1+T)^a`), which in turn needs the
   coefficientwise-continuity chain `normOp_continuous`/`digitMatrix_continuous`/
   `phiSeries_continuous`/`continuous_of_coeff` — all currently `private` to
   `LogDerivative.lean` — plus the `WithPiTopology`-continuity of
   `a ↦ binomialSeries a` (provable from mathlib `PadicInt.continuous_choose`, but not
   yet exposed). The `seriesEval (map toCp (binomialSeries a)) (π_n) = zpPow ξ_n a`
   evaluation is likewise only available as the `private` `seriesEval_map_binomialSeries`
   in `GaloisAction.lean`.
2. The forward inclusion `ker Col ⊆ ZpOne` additionally requires the measure-side
   identification `Res_{ℤ_p^×}(𝒜⁻¹ F) = 0 ↔ F ∈ ker ψ_series` — i.e. the bridge
   `PadicMeasure.psi ↔ psiSeries` under `mahlerLinearEquiv` (the analogue of the
   `MeasureR` `mahlerTransform_psi`, which exists only for `MeasureR`, not for the
   `ℤ_[p]`-valued `PadicMeasure`). Without it the `(1−φ)`-cokernel/`ψ`-kernel pullback
   of `thm:log der` cannot be transported to the measure side.

These belong to a dedicated infrastructure pass (expose the `LogDerivative`/`GaloisAction`
continuity + binomial layer; build `PadicMeasure.mahlerTransform_psi`). Deferred. -/
theorem mem_ker_Col_iff_mem_ZpOne {u : NormCompatUnits p} (hu : u ∈ unitsTower1 p) :
    Col p u = 0 ↔ u ∈ ZpOne p := sorry

/-- **RJW thm:fund exact seq, right-exactness / cokernel**: the image of `Col` on
`𝒰_{∞,1}` is the kernel of the `χ`-moment `μ ↦ ∫_𝒢 χ·μ = μ(x)` (cokernel `ℤ_p(1)`).

OBSTACLE (T-E12.3b). Same root cause as `mem_ker_Col_iff_mem_ZpOne` (1)–(2): the cokernel
side reads `image(Col) = ker(χ-moment)` off the diagram
`ℤ_p⟦T⟧^{ψ=id} →[1−φ] ℤ_p⟦T⟧^{ψ=0} → ℤ_p` (`lem:rest zp*`, `exists_one_sub_phi_eq`)
together with surjectivity of `∂log` onto `ψ=id` (`dlog_surjective_onto_psiId`, available).
Solvability of `Col u = μ` is then equivalent to `μ` killing the `χ`-moment
`μ(unitsPowCM p 1)`. Transporting this to the measure side again needs the
`PadicMeasure.psi ↔ psiSeries` Mahler bridge (absent for `PadicMeasure`; only the
`MeasureR` form `mahlerTransform_psi` exists) and the `private` `GaloisAction` Mahler/`∂log`
binomial layer. The forward `image ⊆ ker` direction does have a measure-only shortcut
(`Col u (unitsPowCM 1) = (𝒜⁻¹(∂log f_u)).comp extendByZero (1)`, total mass on `ℤ_p^×` of a
`ψ=0`-restricted measure, which vanishes), but the converse `ker ⊆ image` is the genuine
surjectivity statement blocked above. Deferred to the same infrastructure pass. -/
theorem range_Col_eq_ker_chiMoment (μ : PadicMeasure p ℤ_[p]ˣ) :
    (∃ u ∈ unitsTower1 p, Col p u = μ) ↔ μ (PadicMeasure.unitsPowCM p 1) = 0 := sorry

end PadicLFunctions.Coleman
