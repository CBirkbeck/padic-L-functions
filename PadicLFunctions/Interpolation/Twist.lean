/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.MeasureR.BaseChange
import PadicLFunctions.Interpolation.Characters

/-!
# Twisting measures by Dirichlet characters (RJW §5.1)

The twist `μ_χ` of a measure by a Dirichlet character of `p`-power conductor
(RJW eq:twist by chi, TeX 1637–1640), the twist by a continuous additive
character (the `z`-twist of §3.5, TeX 1084–1090), and the cleared forms of
the restriction formula (`EqRestrictionFormula`, TeX 1126–1131) and of the
Mahler transform of the twist (RJW Lem 5.4, TeX 1675–1678). Denominators are
cleared per the recorded replan note R5-CLEAR (`.mathlib-quality/
decomposition.md` §5).
-/

open scoped fwdDiff
open PowerSeries

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

noncomputable section

namespace MeasureR

/-- L5.1.2: the twist of a measure by a continuous `R`-valued function
(specialised to characters): `(twist g μ)(f) = μ(g·f)` — RJW eq:twist by chi
(TeX 1637–1640) reads `∫ f dμ_χ = ∫ χ f dμ`. -/
def twist (g : C(ℤ_[p], integerRing K)) (μ : MeasureR K ℤ_[p]) : MeasureR K ℤ_[p] :=
  cmul p K g μ

variable {p K}

@[simp]
lemma twist_apply (g f : C(ℤ_[p], integerRing K)) (μ : MeasureR K ℤ_[p]) :
    twist p K g μ f = μ (g * f) := rfl

/-- Twisted moments: `∫ x^k d(twist g μ) = ∫ g(x)·x^k dμ`. -/
lemma twist_powCM (g : C(ℤ_[p], integerRing K)) (μ : MeasureR K ℤ_[p]) (k : ℕ) :
    twist p K g μ (powCM p K k) = μ (g * powCM p K k) := rfl

/-- A continuous additive character of `ℤ_p`, as a continuous map (mathlib's
`addChar_of_value_at_one` with its continuity lemma). -/
def charCM (r : integerRing K)
    (hr : Filter.Tendsto (r ^ ·) Filter.atTop (nhds 0)) : C(ℤ_[p], integerRing K) :=
  ⟨⇑(PadicInt.addChar_of_value_at_one r hr),
    PadicInt.continuous_addChar_of_value_at_one hr⟩

variable (p K)

/-- The fibres of reduction mod `p^n` are clopen. -/
lemma isClopen_toZModPow_fiber (n : ℕ) (b : ZMod (p ^ n)) :
    IsClopen {x : ℤ_[p] | PadicInt.toZModPow n x = b} := by sorry

/-- L5.1.3 (integral form, at the use site of Thm 5.1): for `n ≥ 1`, a
`χ`-twisted integral over `ℤ_p` equals the integral over `ℤ_p^×` — i.e.
restriction to the units does not change the twist (RJW TeX 1641: "as `χ` is
supported on `ℤ_p^×`, the twisted measure `μ_χ` is automatically supported on
`ℤ_p^×` as well"; TeX 1752–1753). -/
theorem twist_res_units {n : ℕ} (hn : 1 ≤ n) (χ : DirichletCharacter (integerRing K) (p ^ n))
    (μ : MeasureR K ℤ_[p]) :
    res p K (PadicMeasure.isClopen_units p) (twist p K χ.toContinuousMapZp μ)
      = twist p K χ.toContinuousMapZp μ := by sorry

variable {p K}

/-- L5.1.6: the `z`-twist transform formula, coefficientwise form (recorded
fallback of the decomposition's eval₂ form — both routes recorded at L5.1.6
attack [3]): the Mahler coefficients of the twist of `μ` by the character
`κ_r = (1+r)^x` (mathlib `PadicInt.addChar_of_value_at_one`) are
`∑_{m} binom(n+m choose stuff)`-convolutions; equivalently, for every `n`,
`𝓐(κ_r·μ)_n = ∑' m, (coeff of the expansion) — here stated in the form the
§5.1 proofs consume: the twisted transform evaluated through `(1+T)(1+r)−1`.

Source (TeX 1084–1090): "the measure `z^x μ` has Mahler transform
`𝓐_μ((1+T)z − 1)`". -/
theorem mahlerTransform_charTwist (r : integerRing K)
    (hr : Filter.Tendsto (r ^ ·) Filter.atTop (nhds 0)) (μ : MeasureR K ℤ_[p]) (n : ℕ) :
    PowerSeries.coeff n (mahlerTransform p K (twist p K (charCM r hr) μ))
      = ∑' m, PowerSeries.coeff n
            (((1 + PowerSeries.X) * (PowerSeries.C (1 + r)) - 1) ^ m)
          * μ (mahlerCM p K m) := by sorry

/-- L5.1.7 (`EqRestrictionFormula`, cleared per R5-CLEAR): for a primitive
`p^n`-th root of unity `ζ` and `b : ZMod (p^n)`,
`p^n · Res_{b+p^nℤ_p}(μ) = ∑_{c} ζ^{-bc} · (κ_{ζ^c−1}-twist of μ)` as
measures.

Source (verbatim, TeX 1126–1131): the display `EqRestrictionFormula`,
multiplied through by `p^n`. -/
theorem res_class_eq_sum_twists {n : ℕ} (hn : 1 ≤ n) {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ (p ^ n)) (b : ZMod (p ^ n)) (μ : MeasureR K ℤ_[p]) :
    ((p : ℕ) ^ n : integerRing K) •
        res p K (isClopen_toZModPow_fiber p n b) μ
      = ∑ c ∈ Finset.range (p ^ n),
          ζ ^ (c * (p ^ n - (b.val % p ^ n))) •
            twist p K (charCM (ζ ^ c - 1) (by sorry)) μ := by
  sorry

/-- L5.1.8 (RJW Lem 5.4, cleared — statement form pinned by the planning
trace at decomposition L5.1.8 attack [2]): for `χ` primitive mod `p^n`
(`n ≥ 1`) and `ζ` a primitive `p^n`-th root of unity,
`G(χ⁻¹) · 𝓐(μ_χ) = ∑_{c units} χ⁻¹(c) · 𝓐(κ_{ζ^c−1}·μ)`.

Source (verbatim, TeX 1675–1678): "The Mahler transform of `μ_χ` is
`𝓐_{μ_χ}(T) = (1/G(χ⁻¹)) ∑_c χ(c)⁻¹ 𝓐_μ((1+T)ε^c − 1)`" — multiplied
through by the Gauss sum. -/
theorem mahler_twist_formula {n : ℕ} (hn : 1 ≤ n)
    {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ (p ^ n)) (μ : MeasureR K ℤ_[p]) :
    gaussSum χ⁻¹ (AddChar.zmodChar (p ^ n) (hζ.pow_eq_one)) •
        twist p K χ.toContinuousMapZp μ
      = ∑ c ∈ Finset.range (p ^ n),
          χ⁻¹ (c : ZMod (p ^ n)) •
            twist p K (charCM (ζ ^ c - 1) (by sorry)) μ := by
  sorry

end MeasureR

end

end PadicLFunctions
