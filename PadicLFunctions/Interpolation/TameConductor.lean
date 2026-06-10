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

/-- T509 step (iii), the per-`c` identity (†c): the `κ_{ζ^c−1}`-twisted base
change of `μ_a` has its Mahler transform characterised by the
`substAffine`-transport of §4's `F_a`-identity:
`(ζ^{ca}(1+T)^a − 1)·𝓐(κ_{ζ^c−1}·(μ_a)_K) = S_c(geomSum a) − a`. -/
lemma charTwist_muA_mahler_identity {ζ : integerRing K} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ N)) (c : ℕ) {a : ℕ} (hpa : ¬ (p : ℕ) ∣ a) :
    (PowerSeries.C (ζ ^ (c * a)) * (1 + PowerSeries.X) ^ a - 1)
        * mahlerTransform p K (twist p K
            (charCM (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c))
            (baseChange p K (PadicMeasure.muA p a)))
      = substAffine (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c)
          (PowerSeries.map (algebraMap ℤ_[p] (integerRing K))
            (PadicMeasure.geomSum p a))
        - (a : PowerSeries (integerRing K)) := by
  rw [mahlerTransform_charTwist_eq_substAffine, mahlerTransform_baseChange,
    PadicMeasure.mahlerTransform_muA]
  have h4 := congrArg (PowerSeries.map (algebraMap ℤ_[p] (integerRing K)))
    (PadicMeasure.one_add_X_pow_sub_one_mul_Fa p hpa)
  simp only [map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.map_X,
    map_natCast] at h4
  have h5 := congrArg
    (substAffine (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c)) h4
  simp only [map_mul, map_sub, map_pow, map_one, map_natCast,
    substAffine_one_add_X] at h5
  rw [show (1 + (ζ ^ c - 1) : integerRing K) = ζ ^ c by ring, mul_pow, ← map_pow,
    ← pow_mul] at h5
  exact h5

/-- The `substAffine (ζ^c−1)`-image of the base-changed geometric sum:
`S_c(Σ_{i<a}(1+X)^i) = Σ_{i<a} ζ^{ci}·(1+X)^i`. -/
lemma substAffine_map_geomSum {ζ : integerRing K} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ N)) (c : ℕ) (a : ℕ) :
    substAffine (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c)
        (PowerSeries.map (algebraMap ℤ_[p] (integerRing K))
          (PadicMeasure.geomSum p a))
      = ∑ i ∈ Finset.range a,
          PowerSeries.C (ζ ^ (c * i)) * (1 + PowerSeries.X) ^ i := by
  rw [PadicMeasure.geomSum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, map_add, map_one, PowerSeries.map_X, map_pow, substAffine_one_add_X,
    show (1 + (ζ ^ c - 1) : integerRing K) = ζ ^ c by ring, mul_pow, ← map_pow,
    ← pow_mul]

/-- T509 step (iv), the t-side identity (‡c): substituting `T = e^t − 1` into
the `K`-valued (†c): `(ζ^{ca}·e^{at} − 1)·H_c = Σ_{i<a} ζ^{ci}·e^{it} − a`,
with `H_c` the exp-substituted `K`-valued transform of the twisted measure. -/
lemma charTwist_muA_exp_identity {ζ : integerRing K} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ N)) (c : ℕ) {a : ℕ} (hpa : ¬ (p : ℕ) ∣ a) :
    (PowerSeries.C ((ζ : K) ^ (c * a)) * PowerSeries.rescale (a : K)
          (PowerSeries.exp K) - 1)
        * (PowerSeries.map (integerRing K).subtype
            (mahlerTransform p K (twist p K
              (charCM (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c))
              (baseChange p K (PadicMeasure.muA p a))))).subst
            (PowerSeries.exp K - 1)
      = (∑ i ∈ Finset.range a,
          PowerSeries.C ((ζ : K) ^ (c * i)) * PowerSeries.rescale (i : K)
            (PowerSeries.exp K))
        - (a : PowerSeries K) := by
  have hg : PowerSeries.HasSubst (PowerSeries.exp K - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have hX : (PowerSeries.substAlgHom hg) (PowerSeries.X : PowerSeries K)
      = PowerSeries.exp K - 1 := by
    rw [show ⇑(PowerSeries.substAlgHom hg)
        = PowerSeries.subst (PowerSeries.exp K - 1) from
      PowerSeries.coe_substAlgHom hg]
    exact PowerSeries.subst_X hg
  have hK := congrArg (PowerSeries.map (integerRing K).subtype)
    (charTwist_muA_mahler_identity hζ c hpa)
  rw [substAffine_map_geomSum hζ c a] at hK
  simp only [map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.map_X,
    map_sum, map_natCast, PowerSeries.map_C, Subring.coe_subtype] at hK
  have hC : ∀ x : K, (PowerSeries.substAlgHom hg) (PowerSeries.C x)
      = PowerSeries.C x := fun x => (PowerSeries.substAlgHom hg).commutes x
  have hsub := congrArg (PowerSeries.substAlgHom hg) hK
  simp only [map_mul, map_sub, map_pow, map_add, map_one, map_sum, map_natCast,
    hX, hC, show (1 : PowerSeries K) + (PowerSeries.exp K - 1) = PowerSeries.exp K
      by ring,
    PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.coe_substAlgHom hg] at hsub
  simpa only [map_pow] using hsub

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
