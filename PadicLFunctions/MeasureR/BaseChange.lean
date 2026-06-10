/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.MeasureR.UnitsRing

/-!
# Base change of p-adic measures along `ℤ_p → integerRing K`

The bridge between the `ℤ_p`-layer (`PadicMeasure`, §3/§4) and the
coefficient-general layer (`MeasureR`, the §5 widening): a measure
`μ ∈ Λ(ℤ_p)` extends to `Λ_R(ℤ_p)` by mapping its Mahler transform
coefficientwise through the algebra map (decomposition W4 — "the
scalar-extension map is the power-series inclusion under Mahler").

The characterising property is `baseChange_algCM`: on functions of the form
`algebraMap ∘ f` with `f` a `ℤ_p`-valued continuous function, the extended
measure integrates to the image of the original integral. Naturality with
respect to the toolbox operators follows by checking on locally constant
functions (`ext_locallyConstant`).
-/

open scoped fwdDiff
open PowerSeries

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

noncomputable section

namespace MeasureR

/-- Base change `Λ(ℤ_p) → Λ_R(ℤ_p)`: coefficientwise inclusion of Mahler
transforms (decomposition W4). -/
def baseChange : PadicMeasure p ℤ_[p] →+* MeasureR K ℤ_[p] :=
  ((mahlerRingEquiv p K).symm.toRingHom.comp
    ((PowerSeries.map (algebraMap ℤ_[p] (integerRing K))).comp
      (PadicMeasure.mahlerRingEquiv p).toRingHom))

variable {p K}

@[simp]
lemma mahlerTransform_baseChange (μ : PadicMeasure p ℤ_[p]) :
    mahlerTransform p K (baseChange p K μ)
      = PowerSeries.map (algebraMap ℤ_[p] (integerRing K))
          (PadicMeasure.mahlerTransform p μ) := by
  have h := (mahlerRingEquiv p K).apply_symm_apply
    (PowerSeries.map (algebraMap ℤ_[p] (integerRing K))
      (PadicMeasure.mahlerTransform p μ))
  exact h

/-- `baseChange` sends Dirac measures to Dirac measures. -/
@[simp]
lemma baseChange_dirac (a : ℤ_[p]) :
    baseChange p K (PadicMeasure.dirac p a) = dirac K ℤ_[p] a := by
  apply mahlerTransform_injective
  rw [mahlerTransform_baseChange, PadicMeasure.mahlerTransform_dirac,
    mahlerTransform_dirac]

variable (K)

/-- The `R`-valued inclusion of a `ℤ_p`-valued continuous function. -/
def algCM (f : C(ℤ_[p], ℤ_[p])) : C(ℤ_[p], integerRing K) :=
  ⟨fun x => algebraMap ℤ_[p] (integerRing K) (f x),
    ((integerRing.isometry_algebraMap p K).continuous).comp (map_continuous f)⟩

omit [CompleteSpace K] in
@[simp]
lemma algCM_apply (f : C(ℤ_[p], ℤ_[p])) (x : ℤ_[p]) :
    algCM K f x = algebraMap ℤ_[p] (integerRing K) (f x) := rfl

omit [CompleteSpace K] in
lemma algCM_mahler (n : ℕ) : algCM K (mahler n) = mahlerCM p K n := rfl

variable {K}

/-- **The characterising property of base change**: integrating the inclusion
of a `ℤ_p`-valued function gives the inclusion of the integral. -/
theorem baseChange_algCM (μ : PadicMeasure p ℤ_[p]) (f : C(ℤ_[p], ℤ_[p])) :
    baseChange p K μ (algCM K f)
      = algebraMap ℤ_[p] (integerRing K) (μ f) := by
  rw [apply_eq_tsum (baseChange p K μ) (algCM K f),
    PadicMeasure.apply_eq_tsum p μ f]
  have hΔ : ∀ n, Δ_[1]^[n] (⇑(algCM K f)) 0
      = algebraMap ℤ_[p] (integerRing K) (Δ_[1]^[n] (⇑f) 0) := by
    intro n
    rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp []
  have hcoeff : ∀ n, baseChange p K μ (mahlerCM p K n)
      = algebraMap ℤ_[p] (integerRing K) (μ (mahler n)) := by
    intro n
    rw [← coeff_mahlerTransform, mahlerTransform_baseChange, PowerSeries.coeff_map,
      PadicMeasure.coeff_mahlerTransform]
  have hsum : Summable fun n =>
      Δ_[1]^[n] (⇑f) 0 * PadicMeasure.mahlerCoeff p μ n := by
    have h := (PadicInt.hasSum_mahler f).map μ.toAddMonoidHom (PadicMeasure.continuous p μ)
    have h2 := h.summable
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply, LinearMap.toAddMonoidHom_coe]
    rw [show (PadicInt.mahlerTerm (Δ_[1]^[n] (⇑f) 0) n : C(ℤ_[p], ℤ_[p]))
        = (Δ_[1]^[n] (⇑f) 0) • mahler n from ContinuousMap.ext fun x => by
      simp [PadicInt.mahlerTerm_apply, smul_eq_mul, mul_comm], map_smul, smul_eq_mul]
    rfl
  calc ∑' n, Δ_[1]^[n] (⇑(algCM K f)) 0 * baseChange p K μ (mahlerCM p K n)
      = ∑' n, algebraMap ℤ_[p] (integerRing K)
          (Δ_[1]^[n] (⇑f) 0 * PadicMeasure.mahlerCoeff p μ n) := by
        refine tsum_congr fun n => ?_
        rw [hΔ n, hcoeff n, map_mul]
        rfl
    _ = algebraMap ℤ_[p] (integerRing K)
          (∑' n, Δ_[1]^[n] (⇑f) 0 * PadicMeasure.mahlerCoeff p μ n) :=
        (hsum.map_tsum (algebraMap ℤ_[p] (integerRing K))
          (integerRing.isometry_algebraMap p K).continuous).symm

end MeasureR

end

end PadicLFunctions
