/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.KubotaLeopoldt.ZetaP

/-!
# The p-adic family of Eisenstein series (RJW §8, TeX 2361–2446)

The Part-I closer: the Kubota–Leopoldt pseudo-measure interpolates the
*constant* coefficients of the p-stabilised Eisenstein series
`E_k^{(p)} = E_k − p^{k−1}E_k(p·)`, and the non-constant coefficients are
interpolated by elementary divisor-sums of Dirac measures. Bundling
coefficientwise gives the Λ-adic Eisenstein family
`𝐄 = Σ A_n qⁿ ∈ Q(ℤ_p^×)⟦q⟧` (RJW Theorem at TeX 2399):
`A₀ = x·ζ_p/2` and `A_n = Σ_{0<d∣n, p∤d} δ_d`, with
`∫_{ℤ_p^×} x^{k−1}·𝐄 = E_k^{(p)}` for even `k ≥ 4`.

Two deviations from the letter of the source, both recorded:
* **Erratum #11** (`.mathlib-quality/errata.md`): the notes claim "(a) A₀ is
  a pseudo-measure"; with the notes' own Def 3.34 this is false — the pole
  of `x·ζ_p` sits at the character `x⁻¹`, not at the trivial character. We
  prove the corrected claim `(g·[g]−[1])·A₀ ∈ Λ(ℤ_p^×)` for all `g`
  (decomposition replan R8.1).
* The x-twist `τ : [g] ↦ g·[g]` is realised as a ring automorphism of the
  convolution algebra by a pure moments check against the zero-divisor
  lemma (replan R8.2) — no Amice-transform theory is needed.

The complex side (the q-expansion of `E_k^{(p)}` and the σ^p-arithmetic)
lives in `PadicLFunctions/EisensteinComplex.lean`; the two sides meet in
the rational coefficient sequence `stabilisedCoeff` defined here.
-/

open PowerSeries

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]

section diracDivisors

/-- `2` is a unit of `ℤ_p` for odd `p` (its valuation is `0`). -/
theorem isUnit_two_padicInt (hp2 : p ≠ 2) : IsUnit (2 : ℤ_[p]) := by sorry

open Classical in
/-- The unit of `ℤ_p^×` attached to a natural number `d` coprime to `p`
(junk value `1` when `p ∣ d`). RJW TeX 2376: "viewing `d` as an element of
`ℤ_p^×`". -/
noncomputable def unitOfNat (d : ℕ) : ℤ_[p]ˣ :=
  if h : IsUnit ((d : ℕ) : ℤ_[p]) then h.unit else 1

theorem unitOfNat_coe {d : ℕ} (hd : ¬ (p : ℕ) ∣ d) :
    ((unitOfNat p d : ℤ_[p]ˣ) : ℤ_[p]) = (d : ℤ_[p]) := by sorry

/-- R8: the prime-to-`p` divisor power sum
`σ^p_k(n) = Σ_{0<d∣n, p∤d} d^k` (RJW TeX 2393). -/
def sigmaP (k n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors.filter (fun d => ¬ (p : ℕ) ∣ d), d ^ k

/-- R8: the divisor-sum measure `A_n = Σ_{0<d∣n, p∤d} δ_d ∈ Λ(ℤ_p^×)`
(RJW TeX 2411). `A_0 = 0` (the family's constant coefficient is instead the
twisted pseudo-measure `twistedZetaHalf`). -/
noncomputable def divisorMeasure (n : ℕ) : PadicMeasure p ℤ_[p]ˣ :=
  ∑ d ∈ n.divisors.filter (fun d => ¬ (p : ℕ) ∣ d),
    PadicMeasure.dirac p (unitOfNat p d)

/-- R8 (RJW TeX 2413): `∫_{ℤ_p^×} x^k · A_n = σ^p_k(n)` — the Dirac measures
evaluate, `∫ x^k δ_d = d^k`. -/
theorem divisorMeasure_moment (n k : ℕ) :
    divisorMeasure p n (PadicMeasure.unitsPowCM p k)
      = ((sigmaP p k n : ℕ) : ℤ_[p]) := by sorry

end diracDivisors

section twist

/-- R8 (replan R8.2): the x-twist `τ : Λ(ℤ_p^×) → Λ(ℤ_p^×)`,
`(τμ)(f) = μ(x·f)` — on Diracs `[g] ↦ g·[g]` — as a ring automorphism of
the convolution algebra. Multiplicativity is a moments check
(`units_mul_apply_unitsPowCM` + the zero-divisor lemma); the inverse is the
twist by `x⁻¹`. -/
noncomputable def unitsTwist : PadicMeasure p ℤ_[p]ˣ ≃+* PadicMeasure p ℤ_[p]ˣ where
  toFun := PadicMeasure.unitsCmul p (PadicMeasure.unitsPowCM p 1)
  invFun := PadicMeasure.unitsCmul p (PadicMeasure.invCM p)
  left_inv := by sorry
  right_inv := by sorry
  map_mul' := by sorry
  map_add' := by sorry

/-- The twist shifts moments by one: `∫x^k·(τμ) = ∫x^{k+1}·μ`. -/
theorem unitsTwist_moment (μ : PadicMeasure p ℤ_[p]ˣ) (k : ℕ) :
    unitsTwist p μ (PadicMeasure.unitsPowCM p k)
      = μ (PadicMeasure.unitsPowCM p (k + 1)) := by sorry

/-- The twist sends Diracs to scaled Diracs: `τ(δ_g) = g·δ_g`. -/
theorem unitsTwist_dirac (g : ℤ_[p]ˣ) :
    unitsTwist p (PadicMeasure.dirac p g)
      = (g : ℤ_[p]) • PadicMeasure.dirac p g := by sorry

/-- A ring automorphism maps the non-zero-divisors onto the
non-zero-divisors. -/
theorem map_nonZeroDivisors_unitsTwist :
    (nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ)).map
        (unitsTwist p).toMonoidHom
      = nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ) := by sorry

/-- R8: the x-twist extended to the total fraction ring `Q(ℤ_p^×)`. -/
noncomputable def quotientTwist :
    PadicMeasure.QuotientField p ≃+* PadicMeasure.QuotientField p :=
  IsLocalization.ringEquivOfRingEquiv
    (PadicMeasure.QuotientField p) (PadicMeasure.QuotientField p)
    (unitsTwist p) (map_nonZeroDivisors_unitsTwist p)

/-- The extended twist restricts to the measure-twist on `Λ(ℤ_p^×)`. -/
theorem quotientTwist_algebraMap (μ : PadicMeasure p ℤ_[p]ˣ) :
    quotientTwist p (algebraMap _ (PadicMeasure.QuotientField p) μ)
      = algebraMap _ _ (unitsTwist p μ) := by sorry

end twist

section family

/-- R8 (RJW TeX 2410): the constant coefficient `A₀ = x·ζ_p/2` of the
Eisenstein family — the x-twist of the Kubota–Leopoldt pseudo-measure,
halved (`2` is a unit of `ℤ_p` for odd `p`). -/
noncomputable def twistedZetaHalf (hp2 : p ≠ 2) : PadicMeasure.QuotientField p :=
  algebraMap _ (PadicMeasure.QuotientField p)
      ((((isUnit_two_padicInt p hp2).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
        • (1 : PadicMeasure p ℤ_[p]ˣ))
    * quotientTwist p (PadicMeasure.padicZeta p hp2)

/-- R8 (replan R8.1, **erratum #11**): the corrected form of RJW TeX 2403(a).
The notes claim `A₀ = x·ζ_p/2` is a pseudo-measure; with Def 3.34 this is
false (the pole of `x·ζ_p` sits at the character `x⁻¹`, not at the trivial
character — see `.mathlib-quality/errata.md` #11). What holds, and what the
family needs, is the x-twisted analogue: `(g·[g] − [1])·A₀ ∈ Λ(ℤ_p^×)` for
every `g`. -/
theorem twistedZetaHalf_isTwistedPseudoMeasure (hp2 : p ≠ 2) (g : ℤ_[p]ˣ) :
    ∃ ν : PadicMeasure p ℤ_[p]ˣ,
      algebraMap _ (PadicMeasure.QuotientField p)
          ((g : ℤ_[p]) • PadicMeasure.dirac p g - 1)
        * twistedZetaHalf p hp2 = algebraMap _ _ ν := by sorry

/-- R8 (RJW TeX 2412 "A₀ interpolates the constant term"): the moments of
`A₀ = x·ζ_p/2` in the witness encoding — any witness `ν` of
`(b·[b]−[1])·A₀ ∈ Λ` has
`∫x^{k−1}·ν = (b^k−1)·(1−p^{k−1})·ζ(1−k)/2`, the constant coefficient of
`E_k^{(p)}` scaled by the twisted-denominator factor `b^k−1`. -/
theorem twistedZetaHalf_moments (hp2 : p ≠ 2) (b : ℤ_[p]ˣ) {k : ℕ}
    (hk : 4 ≤ k) (ν : PadicMeasure p ℤ_[p]ˣ)
    (hν : algebraMap _ (PadicMeasure.QuotientField p)
          ((b : ℤ_[p]) • PadicMeasure.dirac p b - 1)
        * twistedZetaHalf p hp2 = algebraMap _ _ ν) :
    ((ν (PadicMeasure.unitsPowCM p (k - 1)) : ℤ_[p]) : ℚ_[p])
      = ((b : ℚ_[p]) ^ k - 1) * (1 - (p : ℚ_[p]) ^ (k - 1))
          * ((zetaNeg (k - 1) : ℚ) : ℚ_[p]) / 2 := by sorry

/-- R8 (RJW TeX 2379–2383): the function `k ↦ p^k` can never be interpolated
by a measure on `ℤ_p^×` — `p^{k_n} → 0` along any `p`-adically convergent
strictly increasing sequence of exponents, while the moments of a measure
are `p`-adically continuous in the exponent. Notably `p = 2` is allowed. -/
theorem noMeasure_interpolates_pPow :
    ¬ ∃ θ : PadicMeasure p ℤ_[p]ˣ, ∀ k : ℕ, 0 < k →
      θ (PadicMeasure.unitsPowCM p k) = (p : ℤ_[p]) ^ k := by sorry

/-- R8: the rational coefficient sequence of the p-stabilised Eisenstein
series `E_k^{(p)}` (RJW TeX 2391): constant term `(1−p^{k−1})·ζ(1−k)/2`,
`n`-th term `σ^p_{k−1}(n)`. This is the pivot between the p-adic family
(`eisensteinFamily_interpolation`) and the complex q-expansion
(`hasSum_stabilisedEisenstein` in `EisensteinComplex.lean`). -/
def stabilisedCoeff (k : ℕ) : ℕ → ℚ := fun n =>
  if n = 0 then (1 - (p : ℚ) ^ (k - 1)) * zetaNeg (k - 1) / 2
  else sigmaP p (k - 1) n

/-- R8 (RJW TeX 2399–2400): the Λ-adic Eisenstein family
`𝐄 = Σ_{n≥0} A_n qⁿ ∈ Q(ℤ_p^×)⟦q⟧`: constant coefficient `A₀ = x·ζ_p/2`,
higher coefficients the divisor-sum measures `A_n`. -/
noncomputable def eisensteinFamily (hp2 : p ≠ 2) :
    PowerSeries (PadicMeasure.QuotientField p) :=
  PowerSeries.mk fun n =>
    if n = 0 then twistedZetaHalf p hp2
    else algebraMap _ _ (divisorMeasure p n)

/-- **RJW §8 Theorem (TeX 2399–2407), p-adic half**: the coefficientwise
interpolation `∫_{ℤ_p^×} x^{k−1}·𝐄 = E_k^{(p)}` for `k ≥ 4` — the `n`-th
moment of the family equals the `n`-th coefficient `stabilisedCoeff p k n`
of the p-stabilised Eisenstein series, with the constant coefficient in the
pseudo-measure witness encoding. (Evenness of `k` is not needed on the
p-adic side; it enters only in the complex identification of
`stabilisedCoeff` with the q-expansion of `E_k^{(p)}`, which is
`hasSum_stabilisedEisenstein` in `EisensteinComplex.lean`.) -/
theorem eisensteinFamily_interpolation (hp2 : p ≠ 2) {k : ℕ} (hk : 4 ≤ k) :
    (∀ (b : ℤ_[p]ˣ) (ν : PadicMeasure p ℤ_[p]ˣ),
      algebraMap _ (PadicMeasure.QuotientField p)
            ((b : ℤ_[p]) • PadicMeasure.dirac p b - 1)
          * PowerSeries.constantCoeff (eisensteinFamily p hp2)
        = algebraMap _ _ ν →
      ((ν (PadicMeasure.unitsPowCM p (k - 1)) : ℤ_[p]) : ℚ_[p])
        = ((b : ℚ_[p]) ^ k - 1) * ((stabilisedCoeff p k 0 : ℚ) : ℚ_[p]))
    ∧ ∀ n : ℕ, n ≠ 0 →
      PowerSeries.coeff n (eisensteinFamily p hp2)
          = algebraMap _ _ (divisorMeasure p n)
        ∧ ((divisorMeasure p n (PadicMeasure.unitsPowCM p (k - 1)) : ℤ_[p])
              : ℚ_[p])
          = ((stabilisedCoeff p k n : ℚ) : ℚ_[p]) := by sorry

end family

end PadicLFunctions
