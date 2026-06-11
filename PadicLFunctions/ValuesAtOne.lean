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

omit [CompleteSpace K] [CharZero K] in
/-- P6-p9: the theorem's arguments are norm-one units: `‖1 − ε_N^c‖ = 1`
for `c ∈ (ℤ/N)ˣ` when the tame part `D > 1` (cyclotomic-product argument
`Π_c (1−ε_D^c) = Φ_D(1)` of norm one; each factor `≤ 1` forces each `= 1`).
Stated for the tame root itself; the mixed-root variants are derived in the
assembly. -/
theorem norm_one_sub_pow_eq_one {D : ℕ} [NeZero D] (_hD1 : 1 < D)
    (hD : ¬ (p : ℕ) ∣ D) {ε : K} (hε : IsPrimitiveRoot ε D) {c : ℕ}
    (hc : ¬ D ∣ c) : ‖1 - ε ^ c‖ = 1 := by
  rw [← norm_neg, neg_sub]
  exact hε.norm_pow_sub_one_eq_one (p := p) hD hc

/-- A unit's `Ring.inverse` is the unique right inverse. -/
private theorem ring_inverse_eq_of_mul_eq_one {M₀ : Type*} [MonoidWithZero M₀]
    {a b : M₀} (ha : IsUnit a) (h : a * b = 1) : Ring.inverse a = b := by
  calc Ring.inverse a = Ring.inverse a * (a * b) := by rw [h, mul_one]
    _ = Ring.inverse a * a * b := by rw [mul_assoc]
    _ = b := by rw [Ring.inverse_mul_cancel a ha, one_mul]

/-- The geometric-series inverse `(1 + C b·T)⁻¹ = Σ_n (−b)ⁿ Tⁿ` over any
commutative ring (telescoping coefficient identity, decomposition R6 P6-p2). -/
private theorem one_add_C_mul_X_mul_geom {R : Type*} [CommRing R] (b : R) :
    (1 + PowerSeries.C b * PowerSeries.X) * (PowerSeries.mk fun n => (-b) ^ n) = 1 := by
  ext n
  rw [add_mul, one_mul, map_add]
  cases n with
  | zero =>
    rw [PowerSeries.coeff_mk, pow_zero, mul_comm (PowerSeries.C b) PowerSeries.X, mul_assoc,
      PowerSeries.coeff_zero_X_mul, add_zero, PowerSeries.coeff_one, if_pos rfl]
  | succ m =>
    rw [PowerSeries.coeff_mk, mul_comm (PowerSeries.C b) PowerSeries.X, mul_assoc,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m)]
    ring

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- P6-p2: the formal logarithmic derivative
`∂(logSeriesAt u) = 1 + ((1+T)·u − 1)⁻¹` for `u − 1` a unit
(TeX 2102–2105). Route (decomposition R6 P6-p2): factor
`(1+T)·u − 1 = C(u−1)·(1 + C(u/(u−1))·T)`, invert the geometric factor, then
match coefficients (`derivativeFun` raises the index and the `(1+T)`-multiply
splits adjacent coefficients). -/
theorem one_add_mul_derivative_logSeriesAt {u : K} (hu : IsUnit (u - 1)) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun (logSeriesAt p K u)
      = 1 + Ring.inverse ((1 + PowerSeries.X) * PowerSeries.C u - 1) := by
  have hune : (u - 1) ≠ 0 := hu.ne_zero
  set a : K := u / (u - 1) with ha
  have hCmul : PowerSeries.C (u - 1) * PowerSeries.C a = PowerSeries.C u := by
    rw [← map_mul]; congr 1; rw [ha]; field_simp
  have hfactor : (1 + PowerSeries.X) * PowerSeries.C u - 1
      = PowerSeries.C (u - 1) * (1 + PowerSeries.C a * PowerSeries.X) := by
    have hexp : PowerSeries.C (u - 1) * (1 + PowerSeries.C a * PowerSeries.X)
        = PowerSeries.C (u - 1)
          + (PowerSeries.C (u - 1) * PowerSeries.C a) * PowerSeries.X := by ring
    rw [hexp, hCmul, map_sub, map_one]; ring
  have hCunit : IsUnit (PowerSeries.C (u - 1) : PowerSeries K) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C]; exact hu
  have hgeomunit : IsUnit (1 + PowerSeries.C a * PowerSeries.X : PowerSeries K) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_add, map_one,
      map_mul, PowerSeries.constantCoeff_X, mul_zero, add_zero]; exact isUnit_one
  have hinv : Ring.inverse ((1 + PowerSeries.X) * PowerSeries.C u - 1)
      = PowerSeries.C (u - 1)⁻¹ * (PowerSeries.mk fun n => (-a) ^ n) := by
    refine ring_inverse_eq_of_mul_eq_one (hfactor ▸ hCunit.mul hgeomunit) ?_
    rw [hfactor]
    calc PowerSeries.C (u - 1) * (1 + PowerSeries.C a * PowerSeries.X)
          * (PowerSeries.C (u - 1)⁻¹ * (PowerSeries.mk fun n => (-a) ^ n))
        = (PowerSeries.C (u - 1) * PowerSeries.C (u - 1)⁻¹)
          * ((1 + PowerSeries.C a * PowerSeries.X)
            * (PowerSeries.mk fun n => (-a) ^ n)) := by ring
      _ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hune, map_one, one_add_C_mul_X_mul_geom, mul_one]
  rw [hinv]
  ext n
  rw [map_add, PowerSeries.coeff_one]
  have hsplit : ((1 : PowerSeries K) + PowerSeries.X)
        * PowerSeries.derivativeFun (logSeriesAt p K u)
      = PowerSeries.derivativeFun (logSeriesAt p K u)
        + PowerSeries.X * PowerSeries.derivativeFun (logSeriesAt p K u) := by ring
  have h1a : (1 : K) - a = -(u - 1)⁻¹ := by
    rw [ha, eq_neg_iff_add_eq_zero]; field_simp; ring
  cases n with
  | zero =>
    rw [if_pos rfl, hsplit, map_add, PowerSeries.coeff_zero_X_mul, add_zero,
      PowerSeries.coeff_derivativeFun, logSeriesAt, PowerSeries.coeff_mk,
      if_neg (Nat.succ_ne_zero 0), PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ha]
    simp only [pow_zero, pow_one, mul_one, Nat.cast_zero, zero_add, Nat.cast_one]
    field_simp
    ring
  | succ m =>
    rw [if_neg (Nat.succ_ne_zero m), zero_add, hsplit, map_add,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivativeFun,
      PowerSeries.coeff_derivativeFun, logSeriesAt, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero (m + 1)), if_neg (Nat.succ_ne_zero m),
      PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    simp only [Nat.add_sub_cancel]
    have hm1 : ((m : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    have hm2 : ((m : K) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + 1)
    push_cast
    rw [mul_assoc _ (((m : K) + 1 + 1)⁻¹) (a ^ (m + 1 + 1)),
      mul_comm (((m : K) + 1 + 1)⁻¹) (a ^ (m + 1 + 1)), ← mul_assoc,
      mul_assoc _ (((m : K) + 1 + 1)⁻¹), inv_mul_cancel₀ hm2, mul_one,
      mul_assoc _ (((m : K) + 1)⁻¹) (a ^ (m + 1)),
      mul_comm (((m : K) + 1)⁻¹) (a ^ (m + 1)), ← mul_assoc,
      mul_assoc _ (((m : K) + 1)⁻¹), inv_mul_cancel₀ hm1, mul_one,
      show (-a) ^ (m + 1) = (-1) ^ (m + 1) * a ^ (m + 1) by rw [← neg_one_mul, mul_pow]]
    linear_combination ((-1 : K) ^ m * a ^ (m + 1)) * h1a

omit [IsUltrametricDist K] [CompleteSpace K] in
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
  haveI : Fact (1 < N) := ⟨hN⟩
  -- push `∂` through the negated sum (the `C`-coefficients pull out by linearity)
  have hder : PowerSeries.derivativeFun (Ftilde p K θ hε)
      = -∑ c ∈ Finset.range N, PowerSeries.C (θ⁻¹ ((c : ZMod N)))
          * PowerSeries.derivativeFun (logSeriesAt p K (ε ^ c)) := by
    rw [Ftilde, show PowerSeries.derivativeFun (-∑ c ∈ Finset.range N,
          PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c))
        = d⁄dX K (-∑ c ∈ Finset.range N,
          PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c)) from rfl,
      map_neg, map_sum, neg_inj]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show (d⁄dX K) (PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c))
        = PowerSeries.derivativeFun (PowerSeries.C (θ⁻¹ ((c : ZMod N)))
            * logSeriesAt p K (ε ^ c)) from rfl,
      show PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c)
        = (θ⁻¹ ((c : ZMod N))) • logSeriesAt p K (ε ^ c) from
      (PowerSeries.smul_eq_C_mul _ _).symm,
      PowerSeries.derivativeFun_smul, PowerSeries.smul_eq_C_mul]
  rw [hder, mul_neg, Finset.mul_sum]
  -- per term: `c = 0` is killed by `θ⁻¹ 0 = 0`; for `c ≠ 0`, apply P6-p2
  rw [show (∑ c ∈ Finset.range N, (1 + PowerSeries.X)
        * (PowerSeries.C (θ⁻¹ ((c : ZMod N)))
          * PowerSeries.derivativeFun (logSeriesAt p K (ε ^ c))))
      = ∑ c ∈ Finset.range N, (PowerSeries.C (θ⁻¹ ((c : ZMod N)))
          + PowerSeries.C (θ⁻¹ ((c : ZMod N)))
            * Ring.inverse ((1 + PowerSeries.X) * PowerSeries.C (ε ^ c) - 1)) from by
    refine Finset.sum_congr rfl fun c hc => ?_
    by_cases hdvd : N ∣ c
    · have hc0 : c = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (Finset.mem_range.mp hc)
      have hθ0 : θ⁻¹ ((c : ZMod N)) = 0 := by
        rw [hc0, Nat.cast_zero]
        exact MulChar.map_nonunit _ (by rw [isUnit_zero_iff]; exact one_ne_zero ∘ Eq.symm)
      rw [hθ0, map_zero, zero_mul, mul_zero, zero_add, zero_mul]
    · have hu := hunit c hc hdvd
      rw [show (1 + PowerSeries.X) * (PowerSeries.C (θ⁻¹ ((c : ZMod N)))
            * PowerSeries.derivativeFun (logSeriesAt p K (ε ^ c)))
          = PowerSeries.C (θ⁻¹ ((c : ZMod N)))
            * ((1 + PowerSeries.X) * PowerSeries.derivativeFun
              (logSeriesAt p K (ε ^ c))) from by ring,
        one_add_mul_derivative_logSeriesAt hu, mul_add, mul_one]]
  -- the constant `1`-terms sum to `C(Σ_c θ⁻¹(c)) = C 0 = 0` (nontrivial character)
  rw [Finset.sum_add_distrib]
  have hsum0 : (∑ c ∈ Finset.range N, PowerSeries.C (θ⁻¹ ((c : ZMod N))))
      = (0 : PowerSeries K) := by
    rw [← map_sum]
    have hreindex : ∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N))
        = ∑ x : ZMod N, θ⁻¹ x := by
      refine Finset.sum_nbij' (fun c => ((c : ℕ) : ZMod N)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
      · intro c _; exact Finset.mem_univ _
      · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
      · intro c hc; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hc)
      · intro x _; exact ZMod.natCast_zmod_val x
      · intro c _; rfl
    rw [hreindex, MulChar.sum_eq_zero_of_ne_one (inv_ne_one.mpr hθ1), map_zero]
  rw [hsum0, zero_add]

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

omit [CharZero K] in
/-- P6-p5: `ρ_θ` is supported on the units, so `ψ(ρ_θ) = 0`. -/
theorem psi_rhoTheta {D : ℕ} [NeZero D]
    {η : DirichletCharacter (integerRing K) D} {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} (χ : DirichletCharacter (integerRing K) (p ^ n)) :
    MeasureR.psi p K (rhoTheta p K η hζ hD χ) = 0 :=
  -- `ρ_θ` is in the image of `ι`, whose range is `ker ψ` (RJW Rem 3.33)
  (mem_range_iota_iff (rhoTheta p K η hζ hD χ)).mp ⟨_, rfl⟩

/-- `PowerSeries.map` commutes with `derivativeFun` (coefficient-wise: both
raise the index and scale by `n+1`, which the ring hom preserves). -/
private theorem map_derivativeFun {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : PowerSeries R) :
    PowerSeries.map f (PowerSeries.derivativeFun F)
      = PowerSeries.derivativeFun (PowerSeries.map f F) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivativeFun,
    PowerSeries.coeff_derivativeFun, PowerSeries.coeff_map, map_mul, map_add,
    map_natCast, map_one]

/-- `PowerSeries.map` commutes with the operator `∂ = (1+T)d/dT`. -/
private theorem map_one_add_mul_derivativeFun {R S : Type*} [CommRing R]
    [CommRing S] (f : R →+* S) (F : PowerSeries R) :
    PowerSeries.map f ((1 + PowerSeries.X) * PowerSeries.derivativeFun F)
      = (1 + PowerSeries.X) * PowerSeries.derivativeFun (PowerSeries.map f F) := by
  rw [map_mul, map_add, map_one, PowerSeries.map_X, map_derivativeFun]

omit [CharZero K] in
/-- P6-p5 (continued): `∂𝓐(ρ_θ) = (1−φψ)F_θ` over `K` — multiplication by
`x` recovers `Res_{ℤ_p^×}(μ_θ)` and `Res = 1 − φ∘ψ`
(Lem 6.3's second half in the formal route; the right-hand side is `p3`'s
explicit series). -/
theorem one_add_mul_derivative_mahlerK_rhoTheta {D : ℕ} [NeZero D]
    (_hD1 : 1 < D) {η : DirichletCharacter (integerRing K) D}
    (_hη : η.IsPrimitive) {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D)
    (hD : ¬ (p : ℕ) ∣ D) {n : ℕ}
    (χ : DirichletCharacter (integerRing K) (p ^ n)) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun
        (mahlerK p K (rhoTheta p K η hζ hD χ))
      = mahlerK p K (res p K (PadicMeasure.isClopen_units p)
          (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD))) := by
  -- the measure-level multiplication-by-`x` identity: `x·ρ_θ = Res_{ℤ_p^×}(μ_θ)`
  -- (the `x⁻¹` in `ρ_θ` cancels against the `x`-monomial on the units)
  have hmeas : cmul p K (mahlerCM p K 1) (rhoTheta p K η hζ hD χ)
      = res p K (PadicMeasure.isClopen_units p)
          (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)) := by
    refine LinearMap.ext fun f => ?_
    rw [cmul_apply, rhoTheta, iota, pushforward_apply]
    change (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD))
        (extendByZero p K (invUnitsCM p K
          * ((mahlerCM p K 1 * f).comp (PadicMeasure.unitsValCM p)))) = _
    rw [show invUnitsCM p K * ((mahlerCM p K 1 * f).comp (PadicMeasure.unitsValCM p))
        = f.comp (PadicMeasure.unitsValCM p) from ?_, extendByZero_comp_unitsVal]
    · rfl
    · refine ContinuousMap.ext fun u => ?_
      simp only [ContinuousMap.mul_apply, ContinuousMap.comp_apply, invUnitsCM_apply,
        mahlerCM_apply, PadicMeasure.unitsValCM, ContinuousMap.coe_mk]
      rw [mahler_apply, Ring.choose_one_right, ← mul_assoc, ← map_mul]
      rw [show PadicMeasure.invCM p u * (u : ℤ_[p]) = 1 from ?_, map_one, one_mul]
      change ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (u : ℤ_[p]) = 1
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  -- transport through `mahlerK` via `𝓐_{xμ} = ∂𝓐_μ` and `map`-commutation with `∂`
  rw [← hmeas]
  simp only [mahlerK]
  rw [mahlerTransform_cmul_X,
    show del K (mahlerTransform p K (rhoTheta p K η hζ hD χ))
      = (1 + PowerSeries.X)
        * PowerSeries.derivativeFun (mahlerTransform p K (rhoTheta p K η hζ hD χ)) from rfl,
    map_one_add_mul_derivativeFun]

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
