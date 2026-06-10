/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Interpolation.Twist
import PadicLFunctions.Interpolation.GenBernoulli
import PadicLFunctions.KubotaLeopoldt.ZetaP

/-!
# Interpolation at characters of p-power conductor (RJW Thm 5.1)

The χ-twisted moments of the §4 measures, and **RJW Theorem 5.1**
(`thm:tame conductor`, TeX 1619–1622): for `χ` primitive of conductor `p^n`
(`n ≥ 1`) and `k > 0`, `∫_{ℤ_p^×} χ(x)x^k · ζ_p = L(χ, 1−k)`. The value is
the generalised-Bernoulli expression `LvalNeg` (the analytic comparison is
quarantined in `GenBernoulliComplex.lean`); the ζ_p-pairing follows the §4
witness encoding of `PadicMeasure.kubotaLeopoldt`, with the §4 measures
crossing into the `R`-layer through `baseChange ∘ iota`.
-/

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

noncomputable section

namespace MeasureR

variable {p K}

/-- The `K`-valued character induced by an `integerRing K`-valued one. -/
def toFieldChar {N : ℕ} (χ : DirichletCharacter (integerRing K) N) :
    DirichletCharacter K N :=
  χ.ringHomComp (integerRing K).subtype

/-- L5.1.10: the χ-twisted moments of the base-changed `μ_a` (RJW
eq:special value theorem 1, TeX 1727–1730, uniform `LvalNeg` form): for `χ`
primitive mod `p^n` (`n ≥ 1`), `a` coprime to `p`, `k : ℕ`,
`∫ χ(x)x^k dμ_a = −(1 − χ(a)·a^{k+1})·L(χ,−k)`. -/
theorem twist_muA_moments {n : ℕ} (hn : 1 ≤ n)
    {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    {a : ℕ} (hpa : ¬ (p : ℕ) ∣ a) (k : ℕ) :
    ((twist p K χ.toContinuousMapZp
        (baseChange p K (PadicMeasure.muA p a)) (powCM p K k) : integerRing K) : K)
      = -(1 - (χ (a : ZMod (p ^ n)) : K) * (a : K) ^ (k + 1))
          * LvalNeg (toFieldChar χ) k := by sorry

/-- **RJW Theorem 5.1**, θ-form — the source's own engine (TeX 1757–1761:
"`∫_{ℤ_p^×}χ(x)x^k · x^{-1}μ_a = −(1−χ(a)a^k)L(χ,1−k)`"): the χ-twisted
`k`-th moment of the base change of the §4 unit-side measure
`zetaNum a = x⁻¹·Res_{ℤ_p^×}(μ_a)` is `−(1−χ(a)a^k)·L(χ,1−k)`. -/
theorem tame_conductor_theta {n : ℕ} (hn : 1 ≤ n)
    {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    {a : ℕ} (hpa : ¬ (p : ℕ) ∣ a) {k : ℕ} (hk : 0 < k) :
    ((baseChange p K (PadicMeasure.iota p (PadicMeasure.zetaNum p a))
        (χ.toContinuousMapZp * powCM p K k) : integerRing K) : K)
      = -(1 - (χ (a : ZMod (p ^ n)) : K) * (a : K) ^ k)
          * LvalNeg (toFieldChar χ) (k - 1) := by sorry

/-- **RJW Theorem 5.1** (`thm:tame conductor`, TeX 1619–1622), witness form
mirroring `PadicMeasure.kubotaLeopoldt`'s encoding: for every unit `b` and
every measure-witness `ν` of `([b]−[1])·ζ_p`, the χ-twisted `k`-th moment of
`ν` (base-changed) equals `(χ(b)·b^k − 1)·L(χ, 1−k)`.

"Let χ be a (primitive) Dirichlet character of conductor `p^n` ... Then, for
`k > 0`, we have `∫_{ℤ_p^×}χ(x)x^k · ζ_p = L(χ,1−k)`." -/
theorem tame_conductor {n : ℕ} (hn : 1 ≤ n) (hp2 : p ≠ 2)
    {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    {k : ℕ} (hk : 0 < k) (b : ℤ_[p]ˣ) (ν : PadicMeasure p ℤ_[p]ˣ)
    (hν : algebraMap _ (PadicMeasure.QuotientField p) (PadicMeasure.dirac p b - 1)
        * PadicMeasure.padicZeta p hp2 = algebraMap _ _ ν) :
    ((baseChange p K (PadicMeasure.iota p ν)
        (χ.toContinuousMapZp * powCM p K k) : integerRing K) : K)
      = ((χ (PadicInt.toZModPow n (b : ℤ_[p])) : K)
            * algebraMap ℚ_[p] K (((b : ℤ_[p]) : ℚ_[p]) ^ k) - 1)
          * LvalNeg (toFieldChar χ) (k - 1) := by sorry

end MeasureR

end

end PadicLFunctions
