import PadicLFunctions.Measure.Basic
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# The Mahler (Amice) transform

Following RJW (arXiv:2309.15692) §3.4: to a measure `μ` on `ℤ_p` we attach the power
series `𝓐_μ(T) = ∫ (1+T)^x dμ(x) = ∑_n (∫ binom(x,n) dμ) Tⁿ ∈ ℤ_p[[T]]`, and prove this
is a bijection — RJW Thm. 3.20 (`thm:mahler`), as a linear equivalence here; the ring
isomorphism is assembled in `PadicLFunctions.Measure.Convolution`.

The analytic input (RJW Thm. 3.13, Mahler's theorem) is entirely in mathlib:
`PadicInt.hasSum_mahler`, `PadicInt.fwdDiff_tendsto_zero`, `mahler`, `mahlerSeries`.

## Main definitions

* `PadicMeasure.mahlerCoeff μ n`: the `n`-th Mahler coefficient `∫ binom(x,n) dμ`.
* `PadicMeasure.mahlerTransform μ`: the Amice transform `𝓐_μ ∈ ℤ_p[[T]]`.
* `PadicMeasure.ofPowerSeries g`: the inverse, `φ ↦ ∑' n, Δⁿφ(0) * g_n`.
* `PadicMeasure.mahlerLinearEquiv`: RJW Thm. 3.20 as a `ℤ_[p]`-linear equivalence.
-/

open scoped fwdDiff
open PowerSeries

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

namespace PadicMeasure

/-- The `n`-th *Mahler coefficient* of a measure: `∫_{ℤ_p} binom(x,n) dμ(x)`.

Source: RJW Def. 3.15 (TeX lines 962–965), coefficient form. -/
noncomputable def mahlerCoeff (μ : PadicMeasure p ℤ_[p]) (n : ℕ) : ℤ_[p] :=
  μ (mahler n)

/-- The *Mahler transform* (or *Amice transform*) of a measure on `ℤ_p`:
`𝓐_μ(T) = ∑_{n ≥ 0} (∫ binom(x,n) dμ) Tⁿ ∈ ℤ_p[[T]]`.

Source: RJW Def. 3.15 (TeX lines 962–965). -/
noncomputable def mahlerTransform (μ : PadicMeasure p ℤ_[p]) : PowerSeries ℤ_[p] :=
  PowerSeries.mk (mahlerCoeff p μ)

@[simp]
lemma coeff_mahlerTransform (μ : PadicMeasure p ℤ_[p]) (n : ℕ) :
    PowerSeries.coeff n (mahlerTransform p μ) = μ (mahler n) := by
  simp [mahlerTransform, mahlerCoeff]

/-- The Mahler transform is `ℤ_[p]`-linear. -/
noncomputable def mahlerTransformₗ : PadicMeasure p ℤ_[p] →ₗ[ℤ_[p]] PowerSeries ℤ_[p] where
  toFun := mahlerTransform p
  map_add' _ _ := by ext n; simp [mahlerTransform, mahlerCoeff]
  map_smul' _ _ := by ext n; simp [mahlerTransform, mahlerCoeff]

/-- **Evaluation formula**: integrating `φ` against `μ` is pairing the Mahler
coefficients of `φ` with those of `μ`: `μ φ = ∑' n, Δⁿφ(0) * (∫ binom(x,n) dμ)`.
This is the content of "any measure is uniquely determined by the values
`∫ binom(x,n) dμ`" in the source's proof.

Source: RJW Thm. 3.20, proof, first display (TeX lines 995–998). -/
theorem apply_eq_tsum (μ : PadicMeasure p ℤ_[p]) (f : C(ℤ_[p], ℤ_[p])) :
    μ f = ∑' n, Δ_[1]^[n] (⇑f) 0 * mahlerCoeff p μ n := by
  sorry

/-- The Mahler transform of the Dirac measure `δ_a` is `(1+T)^a` (the binomial series).

Source: RJW Ex. 3.16 (TeX lines 968–973). -/
@[simp]
theorem mahlerTransform_dirac (a : ℤ_[p]) :
    mahlerTransform p (dirac p a) = binomialSeries ℤ_[p] a := by
  sorry

/-- The Mahler transform is injective: a measure killing every `binom(·,n)` is zero.

Source: RJW Thm. 3.20, proof ("uniquely determined", TeX lines 995–998). -/
theorem mahlerTransform_injective : Function.Injective (mahlerTransform p) := by
  sorry

/-- The measure `μ_g` attached to a power series `g`: `φ ↦ ∑' n, Δⁿφ(0) * g_n`.
The series converges because `Δⁿφ(0) → 0` (mathlib's `PadicInt.fwdDiff_tendsto_zero`)
and `ℤ_p` is a complete nonarchimedean ring.

Source: RJW Thm. 3.20, proof, converse direction (TeX lines 1000–1004). -/
noncomputable def ofPowerSeries (g : PowerSeries ℤ_[p]) : PadicMeasure p ℤ_[p] where
  toFun f := ∑' n, Δ_[1]^[n] (⇑f) 0 * PowerSeries.coeff n g
  map_add' _ _ := by sorry
  map_smul' _ _ := by sorry

/-- The Mahler coefficients of `ofPowerSeries g` recover `g`: `∫ binom(x,k) dμ_g = g_k`.
Uses `Δⁿ(binom(·,k))(0) = δ_{nk}`, i.e. `mahler k = mahlerSeries (Pi.single k 1)`.

Source: RJW Thm. 3.20, proof: "Visibly we have 𝓐_{μ_g} = g" (TeX line 1004). -/
@[simp]
theorem mahlerTransform_ofPowerSeries (g : PowerSeries ℤ_[p]) :
    mahlerTransform p (ofPowerSeries p g) = g := by
  sorry

/-- **RJW Theorem 3.20 (`thm:mahler`), linear part**: the Mahler transform is a
`ℤ_[p]`-linear equivalence `ℳ(ℤ_p, ℤ_p) ≃ ℤ_p[[T]]`. (Upgraded to a ring isomorphism
in `PadicLFunctions.Measure.Convolution`.) -/
noncomputable def mahlerLinearEquiv : PadicMeasure p ℤ_[p] ≃ₗ[ℤ_[p]] PowerSeries ℤ_[p] :=
  { mahlerTransformₗ p with
    invFun := ofPowerSeries p
    left_inv := by
      intro μ
      sorry
    right_inv := by
      intro g
      sorry }

@[simp]
lemma mahlerLinearEquiv_apply (μ : PadicMeasure p ℤ_[p]) :
    mahlerLinearEquiv p μ = mahlerTransform p μ := rfl

@[simp]
lemma mahlerLinearEquiv_symm_apply (g : PowerSeries ℤ_[p]) :
    (mahlerLinearEquiv p).symm g = ofPowerSeries p g := rfl

end PadicMeasure
