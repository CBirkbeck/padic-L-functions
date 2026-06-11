/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.MeasureR.Toolbox

/-!
# The formal ψ-operator on power series (RJW §6, decomposition W6b)

The trace operator `ψ` exists in the project at the measure level
(`PadicLFunctions.MeasureR.psi`, the coefficient-free digit shift). This
file builds its FORMAL power-series avatar: every `F ∈ R⟦T⟧` decomposes
uniquely into `p` digits `F = Σ_{i<p} (1+T)^i · φ(F_i)` along
`φG := G((1+T)^p − 1)`, and `ψF := F₀`. The deferred `Eqphipsi` formula
(`(φ∘ψ)F = p⁻¹ Σ_{ξ∈μ_p} F((1+T)ξ−1)`, plan.md "Deferred") is realised in
the only form that is meaningful for unbounded series — as the CONVERGENT
EVALUATION identity at `T = 0` (`psiSeries_eval_zero`): the substitution
`T ↦ (1+T)ξ − 1` has non-nilpotent constant term for `ξ ≠ 1`, so the
formal-series form is ill-posed (recorded replan, decomposition R6).

Decomposition: `.mathlib-quality/decomposition.md` R6, cluster W6b.
-/

open PowerSeries

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]

section digits

variable {R : Type*} [CommRing R]

/-- The formal Frobenius-substitution `φ : F(T) ↦ F((1+T)^p − 1)` (the
series-side of the measure operator `phi`). -/
noncomputable def phiSeries (F : PowerSeries R) : PowerSeries R :=
  F.subst ((1 + PowerSeries.X) ^ p - 1)

/-- W6b-b1: the digit decomposition — every power series is uniquely
`Σ_{i<p} (1+T)^i·φ(G_i)` (triangular in the base-`p` digit bijection
`i + p·j ↔ ℕ` of leading terms). -/
theorem existsUnique_digits (F : PowerSeries R) :
    ∃! G : Fin p → PowerSeries R,
      F = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (G i) := by
  sorry

/-- W6b-b2: the formal trace operator `ψ` — the `0`-th digit. -/
noncomputable def psiSeries (F : PowerSeries R) : PowerSeries R :=
  (existsUnique_digits p F).exists.choose 0

theorem psiSeries_phi (G : PowerSeries R) :
    psiSeries p (phiSeries p G) = G := by sorry

@[simp]
theorem psiSeries_C (a : R) :
    psiSeries p (PowerSeries.C a) = PowerSeries.C a := by sorry

theorem psiSeries_add (F G : PowerSeries R) :
    psiSeries p (F + G) = psiSeries p F + psiSeries p G := by sorry

theorem psiSeries_C_mul (a : R) (F : PowerSeries R) :
    psiSeries p (PowerSeries.C a * F)
      = PowerSeries.C a * psiSeries p F := by sorry

/-- W6b-b3 (with the `∂φ = p·φ∂` sub-step): the commutation
`ψ∂ = p·∂ψ` for `∂ = (1+T)d/dT`. -/
theorem psiSeries_one_add_mul_derivative (F : PowerSeries R) :
    psiSeries p ((1 + PowerSeries.X) * PowerSeries.derivativeFun F)
      = (p : R) • ((1 + PowerSeries.X)
        * PowerSeries.derivativeFun (psiSeries p F)) := by sorry

/-- W6b-b8: `ψ` commutes with coefficient maps. -/
theorem psiSeries_map {S : Type*} [CommRing S] (f : R →+* S)
    (F : PowerSeries R) :
    psiSeries p (PowerSeries.map f F)
      = PowerSeries.map f (psiSeries p F) := by sorry

end digits

section bridge

variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

/-- W6b-b4: the formal `ψ` is the series-side of the measure-level `ψ`
through the Mahler transform. -/
theorem mahlerTransform_psi (μ : MeasureR K ℤ_[p]) :
    MeasureR.mahlerTransform p K (MeasureR.psi p K μ)
      = psiSeries p (MeasureR.mahlerTransform p K μ) := by sorry

variable {K}

/-- W6b-b5: junk-total evaluation of a `K`-coefficient power series
(meaningful when the terms are summable). -/
noncomputable def seriesEval (F : PowerSeries K) (z : K) : K :=
  ∑' n : ℕ, PowerSeries.coeff n F * z ^ n

@[simp]
theorem seriesEval_zero_arg (F : PowerSeries K) :
    seriesEval F (0 : K) = PowerSeries.constantCoeff F := by sorry

/-- W6b-b5 (continued): evaluating `φG` collapses the substitution —
`(φG)(z) = G((1+z)^p − 1)` under summability. -/
theorem seriesEval_phi (G : PowerSeries K) (z : K)
    (hsum : Summable fun n : ℕ =>
      PowerSeries.coeff n G * ((1 + z) ^ p - 1) ^ n) :
    seriesEval (phiSeries p G) z = seriesEval G ((1 + z) ^ p - 1) := by sorry

/-- W6b-b6 (the realised `Eqphipsi`, evaluation form at `T = 0`): with
`ξ` a primitive `p`-th root of unity and the series convergent at the
points `ξ^i − 1`,
`p·(ψF)(0) = Σ_{i<p} F(ξ^i − 1)` (evaluate the digit decomposition at
`ξ^i − 1`, where `(1+(ξ^i−1))^p − 1 = 0` collapses the `φ`-layer; then
`Σ_i ξ^{ij} = p·[j ≡ 0]` orthogonality). -/
theorem psiSeries_eval_zero {ξ : K} (hξ : IsPrimitiveRoot ξ p)
    (F : PowerSeries K)
    (hconv : ∀ i : Fin p, Summable fun n : ℕ =>
      PowerSeries.coeff n F * (ξ ^ (i : ℕ) - 1) ^ n) :
    (p : K) * PowerSeries.constantCoeff (psiSeries p F)
      = ∑ i : Fin p, seriesEval F (ξ ^ (i : ℕ) - 1) := by sorry

/-- W6b-b7: the kernel of `∂ = (1+T)d/dT` is the constants
(char-zero coefficients). -/
theorem eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero
    {F : PowerSeries K}
    (h : (1 + PowerSeries.X) * PowerSeries.derivativeFun F = 0) :
    F = PowerSeries.C (PowerSeries.constantCoeff F) := by sorry

end bridge

end PadicLFunctions
