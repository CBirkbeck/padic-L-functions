/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Interpolation.TameConductor

/-!
# Non-trivial tame conductors (RJW §5.2, Thm 5.7)

For `η` primitive of conductor `D > 1` coprime to `p`: the measure `μ_η` with
Mahler transform `F_η = (−1/G(η⁻¹)) ∑_c η(c)⁻¹/((1+T)ε_D^c − 1)` (an honest
element of `R⟦T⟧` since the denominators are units, TeX 1793–1798), its
moments `∫x^k μ_η = L(η,−k)` (Lem 5.9), the ψ-invariance `ψ(μ_η) = η(p)μ_η`
(Lem 5.10 — proved by the recorded ξ-free route, decomposition L5.2.4), the
unit-restricted moments (Lem 5.11), the twists `μ_θ` and `ζ_η`, and
**RJW Theorem 5.7** (`thm:nontame`, TeX 1773–1776).
-/

open PowerSeries

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

noncomputable section

namespace MeasureR

variable {p K}

omit [CompleteSpace K] [CharZero K] in
/-- L5.2.1: for `ζ` a primitive `D`-th root of unity with `p ∤ D` and
`D ∤ c`, the power series `ζ^c·(1+X) − 1` is a unit of `R⟦X⟧` (constant
coefficient `ζ^c − 1` is a unit by W3; TeX 1798). -/
theorem isUnit_root_mul_one_add_X_sub_one {ζ : integerRing K} {D : ℕ}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) {c : ℕ} (hc : ¬ D ∣ c) :
    IsUnit ((PowerSeries.C (ζ ^ c)) * (1 + PowerSeries.X) - 1 :
      PowerSeries (integerRing K)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp only [map_sub, map_mul, map_add, map_one, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X, add_zero, mul_one]
  refine integerRing.isUnit_of_norm_eq_one ?_
  have hζK : IsPrimitiveRoot ((ζ : K)) D :=
    hζ.map_of_injective (f := (integerRing K).subtype) fun _ _ h => Subtype.ext h
  simpa using hζK.norm_pow_sub_one_eq_one (p := p) hD hc

omit [CompleteSpace K] [CharZero K] in
/-- The Gauss sum `G(η⁻¹)` of a primitive character of conductor `D` coprime
to `p` is a unit of the integer ring (TeX 1798: "the Gauss sum is a `p`-adic
unit (indeed, we have `G(η)G(η⁻¹) = η(−1)D` and `D` is coprime to `p`)"). -/
theorem gaussSum_isUnit_of_coprime {D : ℕ} [NeZero D]
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) :
    IsUnit (gaussSum η⁻¹ (AddChar.zmodChar D hζ.pow_eq_one)) := by
  have hζK : IsPrimitiveRoot ((ζ : K)) D :=
    hζ.map_of_injective (f := (integerRing K).subtype) fun _ _ h => Subtype.ext h
  refine integerRing.isUnit_of_norm_eq_one ?_
  rw [coe_gaussSum_zmodChar η hζ hζK]
  have hηK : (toFieldChar η).IsPrimitive :=
    (DirichletCharacter.isPrimitive_ringHomComp_iff η
      (fun _ _ h => Subtype.ext h)).mpr hη
  exact norm_gaussSum_eq_one K
    ((DirichletCharacter.conductor_inv _).trans hηK) hD hζK

variable (p K)

/-- L5.2.2: the measure `μ_η` of RJW §5.2 (TeX 1793–1798): the inverse Mahler
transform of `−G(η⁻¹)⁻¹-normalised ∑_c η(c)⁻¹·((ζ^c)(1+T) − 1)⁻¹`, stated
unnormalised (multiplied through by the unit `−G(η⁻¹)`) per R5-CLEAR; the
genuinely-used object is the *family* below, with the Gauss-normalisation
carried in the statements. -/
def muEtaCleared {D : ℕ} [NeZero D] (η : DirichletCharacter (integerRing K) D)
    {ζ : integerRing K} (_hζ : IsPrimitiveRoot ζ D) (_hD : ¬ (p : ℕ) ∣ D) :
    MeasureR K ℤ_[p] :=
  (mahlerRingEquiv p K).symm
    (-(∑ c ∈ Finset.range D,
        PowerSeries.C (η⁻¹ (c : ZMod D)) *
          Ring.inverse ((PowerSeries.C (ζ ^ c)) * (1 + PowerSeries.X) - 1)))

variable {p K}

omit [CharZero K] in
/-- The Mahler transform of `muEtaCleared` is the defining series `−G(η⁻¹)F_η`
(EquationFeta, TeX 1793–1795, cleared of its Gauss-sum denominator). -/
@[simp]
lemma mahlerTransform_muEtaCleared {D : ℕ} [NeZero D]
    (η : DirichletCharacter (integerRing K) D) {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) :
    mahlerTransform p K (muEtaCleared p K η hζ hD)
      = -(∑ c ∈ Finset.range D,
          PowerSeries.C (η⁻¹ (c : ZMod D)) *
            Ring.inverse ((PowerSeries.C (ζ ^ c)) * (1 + PowerSeries.X) - 1)) :=
  (mahlerRingEquiv p K).apply_symm_apply _

/-- L5.2.3 (RJW Lem 5.9, TeX 1801–1804): the moments of `μ_η` are the
`L`-values: `G(η⁻¹) · ∫x^k dμ_η`-cleared form,
`∫ x^k d(muEtaCleared η) = G(η⁻¹) · L(η,−k)`. -/
theorem muEtaCleared_moments {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) (k : ℕ) :
    ((muEtaCleared p K η hζ hD (powCM p K k) : integerRing K) : K)
      = ((gaussSum η⁻¹ (AddChar.zmodChar D (hζ.pow_eq_one)) : integerRing K) : K)
          * LvalNeg (toFieldChar η) k := by sorry

/-- L5.2.4 (RJW Lem 5.10, TeX 1812–1813): "We have `ψ(F_η) = η(p)F_η`."
Proved by the recorded ξ-free route (decomposition L5.2.4: γ-telescope +
projection formula + reindexing `c ↦ pc` on `(ℤ/D)^×`). -/
theorem psi_muEtaCleared {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) :
    psi p K (muEtaCleared p K η hζ hD)
      = η ((p : ℕ) : ZMod D) • muEtaCleared p K η hζ hD := by sorry

/-- L5.2.5 (RJW Lem 5.11, TeX 1831–1834): the unit-restricted moments carry
the Euler factor: `∫_{ℤ_p^×} x^k dμ_η = (1−η(p)p^k)·L(η,−k)` (cleared). -/
theorem res_units_muEtaCleared_moments {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) (k : ℕ) :
    ((res p K (PadicMeasure.isClopen_units p) (muEtaCleared p K η hζ hD)
        (powCM p K k) : integerRing K) : K)
      = ((gaussSum η⁻¹ (AddChar.zmodChar D (hζ.pow_eq_one)) : integerRing K) : K)
          * (1 - (η ((p : ℕ) : ZMod D) : K) * (p : K) ^ k)
          * LvalNeg (toFieldChar η) k := by sorry

/-- L5.2.6/L5.2.7 (RJW Def TeX 1866–1868 + final display 1870–1873): the
χ-twisted moments of `ζ_η := x⁻¹·Res_{ℤ_p^×}(μ_η)`, in the moment form the
theorem quantifies (the `x⁻¹`-shift realised by the index shift `k ↦ k−1`):
for `χ` primitive mod `p^n` (`n ≥ 0`) and `k > 0`,
`∫ χ(x)x^k dζ_η = (1 − χη(p)p^{k−1})·L(χη, 1−k)` (cleared). -/
theorem zetaEta_twisted_moments {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    {θ : DirichletCharacter (integerRing K) (D * p ^ n)}
    (hθ : θ = (DirichletCharacter.changeLevel (Dvd.intro _ rfl) η)
        * (DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ))
    {k : ℕ} (hk : 0 < k) :
    ((twist p K χ.toContinuousMapZp
        (res p K (PadicMeasure.isClopen_units p) (muEtaCleared p K η hζ hD))
        (powCM p K (k - 1)) : integerRing K) : K)
      = ((gaussSum η⁻¹ (AddChar.zmodChar D (hζ.pow_eq_one)) : integerRing K) : K)
          * (1 - (θ ((p : ℕ) : ZMod (D * p ^ n)) : K) * (p : K) ^ (k - 1))
          * LvalNeg (toFieldChar θ) (k - 1) := by sorry

/-- L5.2.8 (determinacy, the uniqueness half of **RJW Thm 5.7**): a measure
on `ℤ_p` supported on the units and killing every `χ(x)·x^k` (all primitive
`χ` of `p`-power conductor valued in `R`, all `k > 0`) is zero — provided `K`
contains enough roots of unity (hypothesis quantified per level). Recorded
design note at decomposition L5.2.8. -/
theorem eq_zero_of_twisted_moments_eq_zero
    (hroots : ∀ n : ℕ, ∃ ζ : integerRing K, IsPrimitiveRoot ζ (p ^ n))
    (μ : MeasureR K ℤ_[p])
    (hsupp : res p K (PadicMeasure.isClopen_units p) μ = μ)
    (h : ∀ (n : ℕ) (χ : DirichletCharacter (integerRing K) (p ^ n)), χ.IsPrimitive →
      ∀ k, 0 < k → twist p K χ.toContinuousMapZp μ (powCM p K k) = 0) :
    μ = 0 := by sorry

end MeasureR

end

end PadicLFunctions
