/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.ExtLog
import PadicLFunctions.Interpolation.LpFunction
import PadicLFunctions.MeasureR.FormalPsi

/-!
# The p-adic value L_p(θ,1) (RJW §6.2, Thm 6.1(ii), decomposition P6)

**RJW Theorem 6.1(ii)** (Leopoldt; `s=1 theorem`(ii), TeX 1992–1995):
`L_p(θ,1) = −(1−θ(p)p⁻¹)·G(θ⁻¹)⁻¹·Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·log_p(1−ε_N^c)`,
for `θ = χη` non-trivial, `η` primitive of tame conductor `D > 1` prime to
`p`, `χ` of conductor `p^n` (the §5.2 standing hypotheses; the pure
`p`-power case `D = 1` is deferred — decomposition R6, replan 4).

Route (distribution-free; recorded replans R6 1–3): the antiderivative
`F̃_θ` is an EXPLICIT power series over `K` (TeX 2076–2080 expansion, with
`extLog`-constant terms); `∂F̃_θ = F_θ` is a formal identity; the Mahler
transform of the genuine measure `ρ_θ = x⁻¹·Res_{ℤ_p^×}(μ_θ)` equals
`F̃_θ − φψF̃_θ` by matching `∂` and pinning the constant in `ker ψ`; and the
value `(ψF̃_θ)(0)` is computed by the evaluated `Eqphipsi`
(`psiSeries_eval_zero`) with the `μ_p`-collapse
`Σ_ξ log_p(ξw−1) = log_p(w^p−1)` and the `c ↦ pc` bookkeeping
(automorphism for `n = 0`; primitive-character fiber sums for `n ≥ 1`).

Decomposition: `.mathlib-quality/decomposition.md` R6, cluster P6.
-/

open PowerSeries

namespace PadicLFunctions

namespace MeasureR

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

/-- P6-p1: the per-root logarithmic series
`log((1+T)u − 1) = extLog(u−1) + Σ_{n≥1} ((−1)^{n−1}/n)(u/(u−1))ⁿ Tⁿ`
(TeX 2076–2080), as an explicit `K`-coefficient power series. -/
noncomputable def logSeriesAt (u : K) : PowerSeries K :=
  PowerSeries.mk fun n =>
    if n = 0 then extLog p (u - 1)
    else (-1 : K) ^ (n - 1) * ((n : K))⁻¹ * (u / (u - 1)) ^ n

/-- P6-p1 (continued): the explicit antiderivative `F̃_θ` of RJW TeX ~2070
(stated G-cleared, per the §5 clearing conventions — replan R6.5). -/
noncomputable def Ftilde {N : ℕ} [NeZero N] (θ : DirichletCharacter K N)
    {ε : K} (_hε : IsPrimitiveRoot ε N) : PowerSeries K :=
  -∑ c ∈ Finset.range N,
    PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c)

variable {p K}

/-- P6-p9: the theorem's arguments are norm-one units: `‖1 − ε_N^c‖ = 1`
for `c ∈ (ℤ/N)ˣ` when the tame part `D > 1` (cyclotomic-product argument
`Π_c (1−ε_D^c) = Φ_D(1)` of norm one; each factor `≤ 1` forces each `= 1`).
Stated for the tame root itself; the mixed-root variants are derived in the
assembly. -/
theorem norm_one_sub_pow_eq_one {D : ℕ} [NeZero D] (hD1 : 1 < D)
    (hD : ¬ (p : ℕ) ∣ D) {ε : K} (hε : IsPrimitiveRoot ε D) {c : ℕ}
    (hc : ¬ D ∣ c) : ‖1 - ε ^ c‖ = 1 := by sorry

/-- P6-p2: the formal logarithmic derivative
`∂(logSeriesAt u) = 1 + ((1+T)·u − 1)⁻¹` for `u − 1` a unit
(TeX 2102–2105). -/
theorem one_add_mul_derivative_logSeriesAt {u : K} (hu : IsUnit (u - 1)) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun (logSeriesAt p K u)
      = 1 + Ring.inverse ((1 + PowerSeries.X) * PowerSeries.C u - 1) := by
  sorry

/-- P6-p3: `∂F̃_θ = F_θ` — the constant terms cancel by
`Σ_c θ⁻¹(c) = 0` for `θ ≠ 1` (TeX 2100–2110, Lem 6.3 first half in the
formal route). -/
theorem one_add_mul_derivative_Ftilde {N : ℕ} [NeZero N] (hN : 1 < N)
    {θ : DirichletCharacter K N} (hθ1 : θ ≠ 1) {ε : K}
    (hε : IsPrimitiveRoot ε N)
    (hunit : ∀ c ∈ Finset.range N, ¬ N ∣ c → IsUnit (ε ^ c - 1)) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun (Ftilde p K θ hε)
      = -∑ c ∈ Finset.range N, PowerSeries.C (θ⁻¹ ((c : ZMod N)))
          * Ring.inverse ((1 + PowerSeries.X) * PowerSeries.C (ε ^ c) - 1) := by
  sorry

variable (p K)

/-- P6-p4: the genuine measure `ρ_θ = x⁻¹·Res_{ℤ_p^×}(μ_θ)` on `ℤ_p`
(the §5 `zetaEtaCleared` pattern applied to the `χ`-twisted `μ̃_η`,
pushed forward along the unit inclusion). -/
noncomputable def rhoTheta {D : ℕ} [NeZero D]
    (η : DirichletCharacter (integerRing K) D) {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} (χ : DirichletCharacter (integerRing K) (p ^ n)) :
    MeasureR K ℤ_[p] :=
  iota p K
    ((twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)).comp
      ((extendByZero p K).comp
        (LinearMap.mulLeft (integerRing K) (invUnitsCM p K))))

variable {p K}

/-- P6-p5: `ρ_θ` is supported on the units, so `ψ(ρ_θ) = 0`. -/
theorem psi_rhoTheta {D : ℕ} [NeZero D]
    {η : DirichletCharacter (integerRing K) D} {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} (χ : DirichletCharacter (integerRing K) (p ^ n)) :
    MeasureR.psi p K (rhoTheta p K η hζ hD χ) = 0 := by sorry

/-- P6-p5 (continued): `∂𝓐(ρ_θ) = (1−φψ)F_θ` over `K` — multiplication by
`x` recovers `Res_{ℤ_p^×}(μ_θ)` and `Res = 1 − φ∘ψ`
(Lem 6.3's second half in the formal route; the right-hand side is `p3`'s
explicit series). -/
theorem one_add_mul_derivative_mahlerK_rhoTheta {D : ℕ} [NeZero D]
    (hD1 : 1 < D) {η : DirichletCharacter (integerRing K) D}
    (hη : η.IsPrimitive) {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D)
    (hD : ¬ (p : ℕ) ∣ D) {n : ℕ}
    (χ : DirichletCharacter (integerRing K) (p ^ n)) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun
        (mahlerK p K (rhoTheta p K η hζ hD χ))
      = mahlerK p K (res p K (PadicMeasure.isClopen_units p)
          (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD))) := by
  sorry

/-- P6-p6' (the constant pin, c₀-design — replan R6.6; Lem 6.3 made
distribution-free WITHOUT field-level `ψ`): the cleared mass identity
`p·𝓐_ρ(0)·G = p·F̃(0) − Σ_{i<p} F̃(ξ^i−1)`. Internally: `W := C G⁻¹·F̃ −
𝓐_ρ` has `∂W = φ(B)` for the bounded `B = G⁻¹-cleared 𝓐(ψ-part)`, so
`W = φC + c₀` (antiderivative + ker ∂); evaluating at `0` and at the
`ξ^i − 1` (where `φ`-images collapse and `Σ 𝓐_ρ(ξ^i−1) = p·𝓐_{ψρ}(0) = 0`
by `sum_seriesEval_mahlerK` + `psi_rhoTheta`) pins `c₀`. -/
theorem p_mul_constantCoeff_mahlerK_rhoTheta {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} {χ : DirichletCharacter (integerRing K) (p ^ n)}
    (hχ : χ.IsPrimitive)
    {θK : DirichletCharacter K (D * p ^ n)} (hN : 1 < D * p ^ n)
    (hθ1 : θK ≠ 1)
    (hθK : θK = toFieldChar (DirichletCharacter.changeLevel (Dvd.intro _ rfl) η
      * DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ))
    {ε : K} (hε : IsPrimitiveRoot ε (D * p ^ n)) {ξ : K}
    (hξ : IsPrimitiveRoot ξ p)
    {G : K} (hG : IsUnit G)
    (hGtwist : mahlerK p K (twist p K χ.toContinuousMapZp
        (muEtaCleared p K η hζ hD))
      = PowerSeries.C G⁻¹ * (-∑ c ∈ Finset.range (D * p ^ n),
          PowerSeries.C (θK⁻¹ ((c : ZMod (D * p ^ n))))
            * Ring.inverse ((1 + PowerSeries.X)
              * PowerSeries.C (ε ^ c) - 1))) :
    (p : K) * PowerSeries.constantCoeff
        (mahlerK p K (rhoTheta p K η hζ hD χ))
      = G⁻¹ * ((p : K) * PowerSeries.constantCoeff (Ftilde p K θK hε)
        - ∑ i : Fin p, seriesEval (Ftilde p K θK hε) (ξ ^ (i : ℕ) - 1)) := by
  sorry

/-- P6-p7' (the evaluated trace, ψ-free form — replan R6.6):
`Σ_{i<p} F̃(ξ^i−1) = θ(p)·F̃(0)` — for `n = 0` by the `c ↦ pc` automorphism
and the `μ_p`-collapse `Σ_ξ extLog(ξw−1) = extLog(w^p−1)`; for `n ≥ 1`
both sides vanish (`θ(p) = 0`; primitive-character fiber sums —
replan R6.3). -/
theorem sum_seriesEval_Ftilde {N : ℕ} [NeZero N] (hN : 1 < N)
    {θ : DirichletCharacter K N} (hprim : θ.IsPrimitive) (hθ1 : θ ≠ 1)
    {ε : K} (hε : IsPrimitiveRoot ε N) {ξ : K}
    (hξ : IsPrimitiveRoot ξ p)
    (hdom : ∀ c ∈ Finset.range N, ¬ N ∣ c → ExtLogDomain p (ε ^ c - 1)) :
    ∑ i : Fin p, seriesEval (Ftilde p K θ hε) (ξ ^ (i : ℕ) - 1)
      = θ ((p : ZMod N)) * PowerSeries.constantCoeff (Ftilde p K θ hε) := by
  sorry

/-- **RJW Theorem 6.1(ii)** (Leopoldt; `s=1 theorem`(ii), TeX 1992–1995):
"We have `L_p(θ,1) = −(1 − θ(p)p⁻¹)·G(θ⁻¹)⁻¹·
Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·log_p(1−ε_N^c)`." Stated for tame conductor `D > 1`
(replan R6.4; the §5.2 standing hypotheses), with `log_p` the extended
logarithm `extLog` and the Gauss factor through the §5 clearing plus the
coprime factorisation (C6-c4). -/
theorem LpFunction_one {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} {χ : DirichletCharacter (integerRing K) (p ^ n)}
    (hχ : χ.IsPrimitive)
    {θK : DirichletCharacter K (D * p ^ n)} (hθ1 : θK ≠ 1)
    (hθK : θK = toFieldChar (DirichletCharacter.changeLevel (Dvd.intro _ rfl) η
      * DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ))
    (hprim : θK.IsPrimitive)
    {ε : K} (hε : IsPrimitiveRoot ε (D * p ^ n)) {ξ : K}
    (hξ : IsPrimitiveRoot ξ p)
    {G : K} (hG : IsUnit G)
    (hGval : G = (gaussSum θK⁻¹ (AddChar.zmodChar (D * p ^ n)
      hε.pow_eq_one))) :
    LpFunction p K η hζ hD χ 1
      = -(1 - θK ((p : ZMod (D * p ^ n))) * (p : K)⁻¹) * G⁻¹
        * ∑ c ∈ Finset.range (D * p ^ n),
            θK⁻¹ ((c : ZMod (D * p ^ n))) * extLog p (1 - ε ^ c) := by
  sorry

end MeasureR

end PadicLFunctions
