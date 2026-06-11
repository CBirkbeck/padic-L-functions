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

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
include hp in
/-- `‖(n : K)⁻¹‖ ≤ n` for `n ≥ 1`: the norm of `(n : K)` is `p^{−v_p(n)}`, whose
inverse is `p^{v_p(n)} = ordProj[p] n ≤ n`. The polynomial-growth bound for the
`1/n`-coefficients of `logSeriesAt` / `F̃`. -/
private theorem norm_natCast_inv_le {n : ℕ} (hn : 1 ≤ n) : ‖((n : K))⁻¹‖ ≤ (n : ℝ) := by
  have hn0 : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hnK : ((n : K)) = algebraMap ℚ_[p] K (n : ℚ_[p]) := (map_natCast _ n).symm
  have hnorm : ‖((n : K))⁻¹‖ = ((p ^ padicValNat p n : ℕ) : ℝ) := by
    rw [norm_inv, hnK, norm_algebraMap', Padic.norm_eq_zpow_neg_valuation hn0,
      Padic.valuation_natCast, ← zpow_neg, neg_neg, zpow_natCast]
    push_cast; ring
  rw [hnorm, ← Nat.factorization_def n hp.out]
  exact_mod_cast Nat.ordProj_le p (by omega)

/-! #### The boundary `p`-adic logarithm (T618 / Washington §5.1)

`padicLog`'s `p`-power law `padicLog (z^p) = p·padicLog z` and multiplicativity are
proven in `PadicExp` only INSIDE the exponential ball `‖z−1‖^{p−1} < p⁻¹`. The
arguments `1 − ε_N^c`, `ξ^i − 1` of RJW Thm 6.1(ii) sit on the boundary
`‖·‖^{p−1} = p⁻¹` of that ball. This block extends those facts to the WHOLE open unit
ball `‖z−1‖ < 1` by aligning the convergent `padicLog` series with the formal
`formalLog` and pushing `phiSeries_formalLog : φ formalLog = p·formalLog` through the
`seriesEval` bridge. Decomposition R6.6, ticket T618. -/

omit [CompleteSpace K] [CharZero K] in
/-- T618: the open unit ball `‖x − 1‖ < 1` is closed under powers (ultrametric). -/
theorem boundary_norm_pow_sub_one_lt_one {x : K} (hx : ‖x - 1‖ < 1) (n : ℕ) : ‖x ^ n - 1‖ < 1 := by
  induction n with
  | zero => rw [pow_zero, sub_self, norm_zero]; exact one_pos
  | succ k ih =>
    have hbd : ‖x ^ (k + 1) - 1‖ ≤ max ‖x ^ k - 1‖ ‖x - 1‖ := by
      rw [show x ^ (k + 1) - 1 = (x ^ k - 1) * x + (x - 1) from by rw [pow_succ]; ring]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ le_rfl)
      have hx1 : ‖x‖ ≤ 1 := by
        calc ‖x‖ = ‖(x - 1) + 1‖ := by rw [sub_add_cancel]
          _ ≤ max ‖x - 1‖ ‖(1 : K)‖ := IsUltrametricDist.norm_add_le_max _ _
          _ ≤ 1 := by rw [norm_one]; exact max_le hx.le le_rfl
      rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hx1
    exact lt_of_le_of_lt hbd (max_lt ih hx)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
include hp in
/-- T618: the coefficients of `formalLog` are linearly bounded `‖coeff n‖ ≤ n + 1`
(the `1/n`-factor has norm `≤ n`). Drives summability of `seriesEval (formalLog K) z`
for `‖z‖ < 1`. -/
private theorem norm_coeff_formalLog_le (n : ℕ) :
    ‖PowerSeries.coeff n (formalLog K)‖ ≤ (n : ℝ) + 1 := by
  cases n with
  | zero => rw [coeff_zero_formalLog, norm_zero]; positivity
  | succ m =>
    rw [coeff_succ_formalLog, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖((m : K) + 1)⁻¹‖ = ‖(((m + 1 : ℕ) : K))⁻¹‖ := by rw [Nat.cast_succ]
      _ ≤ ((m + 1 : ℕ) : ℝ) := norm_natCast_inv_le (p := p) (K := K) (by omega)
      _ ≤ (↑(m + 1) : ℝ) + 1 := by push_cast; linarith

omit [CharZero K] in
include hp in
/-- T618: `seriesEval (formalLog K) z` converges for `‖z‖ < 1` (linear-growth
coefficients). -/
private theorem summable_seriesEval_formalLog {z : K} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => PowerSeries.coeff n (formalLog K) * z ^ n :=
  summable_seriesEval_of_norm_coeff_le_linear (C := 1)
    (fun n => by simpa using norm_coeff_formalLog_le (p := p) n) hz

omit [CharZero K] in
include hp in
/-- T618 (the eval-alignment): for `‖z − 1‖ < 1`, `seriesEval (formalLog K) (z − 1) =
padicLog p z`. Reindex by one (`coeff 0 = 0`) and match the scalar `((n:ℚ_[p])+1)⁻¹`
against `((n:K)+1)⁻¹` through `algebraMap`. -/
theorem seriesEval_formalLog {z : K} (hz : ‖z - 1‖ < 1) :
    seriesEval (formalLog K) (z - 1) = padicLog p z := by
  have hsum := summable_seriesEval_formalLog (p := p) hz
  rw [seriesEval, hsum.tsum_eq_zero_add, coeff_zero_formalLog, zero_mul, zero_add, padicLog]
  refine tsum_congr fun n => ?_
  rw [coeff_succ_formalLog, Algebra.smul_def,
    show algebraMap ℚ_[p] K ((n : ℚ_[p]) + 1)⁻¹ = ((n : K) + 1)⁻¹ from by
      rw [map_inv₀, map_add, map_natCast, map_one]]
  ring

omit [CharZero K] in
include hp in
/-- T618: `padicLog p (z^p) = (p : K) • padicLog p z` for `‖z − 1‖ < 1` — the
boundary `p`-power law. Evaluate `phiSeries_formalLog` at `z − 1` through the
`seriesEval` bridge: `padicLog (z^p) = seriesEval formalLog (z^p − 1) =
seriesEval (φ formalLog) (z − 1) = seriesEval (p·formalLog) (z − 1) =
p·padicLog z`. -/
theorem padicLog_pow_p_of_norm_lt_one {z : K} (hz : ‖z - 1‖ < 1) :
    padicLog p (z ^ p) = (p : K) • padicLog p z := by
  have hzp1 : ‖z ^ p - 1‖ < 1 := boundary_norm_pow_sub_one_lt_one hz p
  have h1z : (1 : K) + (z - 1) = z := by ring
  have hzp1' : ‖(1 + (z - 1)) ^ p - 1‖ < 1 := by rw [h1z]; exact hzp1
  have hprodsum := summable_prod_of_norm_coeff_le_linear (p := p) (G := formalLog K) (C := 1)
    (fun n => by simpa using norm_coeff_formalLog_le (p := p) n) hz
  -- evaluate `φ formalLog` at `z − 1`, two ways
  have hbridge : seriesEval (phiSeries p (formalLog K)) (z - 1) = padicLog p (z ^ p) := by
    rw [seriesEval_phi_of_summable_prod p (formalLog K) (z - 1) hprodsum,
      ← seriesEval, seriesEval_formalLog (p := p) hzp1', h1z]
  rw [← hbridge, phiSeries_formalLog, PowerSeries.smul_eq_C_mul, seriesEval_C_mul,
    seriesEval_formalLog (p := p) hz, smul_eq_mul]

omit [CharZero K] in
include hp in
/-- T618: `padicLog p (z ^ (p ^ N)) = (p ^ N : K) • padicLog p z` for `‖z − 1‖ < 1`
(iterate the `p`-power law; each intermediate `z ^ (p ^ i)` stays in the unit ball). -/
theorem padicLog_pow_pPow_of_norm_lt_one {z : K} (hz : ‖z - 1‖ < 1) (N : ℕ) :
    padicLog p (z ^ (p ^ N)) = ((p : K) ^ N) • padicLog p z := by
  induction N with
  | zero => rw [pow_zero, pow_one, pow_zero, one_smul]
  | succ M ih =>
    rw [pow_succ, pow_mul, padicLog_pow_p_of_norm_lt_one (p := p)
        (boundary_norm_pow_sub_one_lt_one hz (p ^ M)), ih, smul_smul, pow_succ, mul_comm]

omit [CharZero K] in
include hp in
/-- T618: multiplicativity of `padicLog` on the WHOLE open unit ball
`‖x − 1‖, ‖y − 1‖ < 1` (descend to the exp ball: choose `N` with `x^{p^N}`, `y^{p^N}`,
`(xy)^{p^N}` all in the ball — `exists_pPow_pow_inExpBall` thrice with `N := max` — apply
the exp-ball `padicLog_mul` at level `p^N` and cancel the `p^N`-scalar). -/
theorem padicLog_mul_of_norm_lt_one {x y : K} (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) :
    padicLog p (x * y) = padicLog p x + padicLog p y := by
  have hxy : ‖x * y - 1‖ < 1 := by
    rw [show x * y - 1 = (x - 1) * y + (y - 1) from by ring]
    have hy1 : ‖y‖ ≤ 1 := by
      calc ‖y‖ = ‖(y - 1) + 1‖ := by rw [sub_add_cancel]
        _ ≤ max ‖y - 1‖ ‖(1 : K)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ 1 := by rw [norm_one]; exact max_le hy.le le_rfl
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt
      (by rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hy1) hx) hy)
  -- a single `p^N` lands all three in the exp ball
  obtain ⟨jx, hjx⟩ := exists_pPow_pow_inExpBall (p := p) hx
  obtain ⟨jy, hjy⟩ := exists_pPow_pow_inExpBall (p := p) hy
  obtain ⟨jxy, hjxy⟩ := exists_pPow_pow_inExpBall (p := p) hxy
  -- the exp ball is closed under further `p`-powering
  have hpow_ball : ∀ {w : K} {j : ℕ} (d : ℕ), InExpBall p (w ^ p ^ j - 1) →
      InExpBall p (w ^ p ^ (j + d) - 1) := by
    intro w j d hwj
    rw [pow_add, pow_mul]
    exact pow_mem_expBall (p := p) hwj (p ^ d)
  set N : ℕ := max (max jx jy) jxy with hN
  have hbx : InExpBall p (x ^ p ^ N - 1) := by
    rw [hN, show max (max jx jy) jxy = jx + (max (max jx jy) jxy - jx) from by omega]
    exact hpow_ball _ hjx
  have hby : InExpBall p (y ^ p ^ N - 1) := by
    rw [hN, show max (max jx jy) jxy = jy + (max (max jx jy) jxy - jy) from by omega]
    exact hpow_ball _ hjy
  have hbxy : InExpBall p (x ^ p ^ N * y ^ p ^ N - 1) := by
    rw [← mul_pow, hN, show max (max jx jy) jxy = jxy + (max (max jx jy) jxy - jxy) from by omega]
    exact hpow_ball _ hjxy
  -- the exp-ball identity at level `p^N`, transported back through the `p^N`-power law
  have hkey : padicLog p ((x * y) ^ p ^ N) = padicLog p (x ^ p ^ N) + padicLog p (y ^ p ^ N) := by
    rw [mul_pow, padicLog_mul (p := p) hbx hby]
  rw [padicLog_pow_pPow_of_norm_lt_one (p := p) hxy,
    padicLog_pow_pPow_of_norm_lt_one (p := p) hx,
    padicLog_pow_pPow_of_norm_lt_one (p := p) hy, ← smul_add] at hkey
  have hpN : ((p : K) ^ N) ≠ 0 := pow_ne_zero _ (natCast_p_ne_zero (L := K) p)
  exact smul_right_injective K hpN hkey

omit [CharZero K] in
include hp in
/-- T618: `padicLog p (x ^ n) = n • padicLog p x` on the whole open unit ball
(induction via `padicLog_mul_of_norm_lt_one`). -/
theorem padicLog_pow_of_norm_lt_one {x : K} (hx : ‖x - 1‖ < 1) (n : ℕ) :
    padicLog p (x ^ n) = n • padicLog p x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, padicLog_mul_of_norm_lt_one (p := p)
        (boundary_norm_pow_sub_one_lt_one hx k) hx, ih, succ_nsmul]

omit [CharZero K] in
include hp in
/-- T618: `extLog p x = padicLog p x` on the whole open unit ball `‖x − 1‖ < 1`. The
witness `(p^j, 0, x^{p^j})` (with `x^{p^j}` in the exp ball, `exists_pPow_pow_inExpBall`)
computes `extLog`, and the `p^j`-power law cancels the `(p^j)⁻¹`-scalar. -/
theorem extLog_eq_padicLog_of_norm_lt_one {x : K} (hx : ‖x - 1‖ < 1) :
    extLog p x = padicLog p x := by
  obtain ⟨j, hj⟩ := exists_pPow_pow_inExpBall (p := p) hx
  have hpne : ((p ^ j : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (pow_pos hp.out.pos j).ne'
  rw [extLog_eq_of_witness (p := p) (m := p ^ j) (k := 0) (y := x ^ p ^ j)
      (pow_pos hp.out.pos j) (by rw [zpow_zero, one_mul]) hj,
    padicLog_pow_pPow_of_norm_lt_one (p := p) hx,
    -- rewrite the `K`-scalar `(p:K)^j` as the `ℚ_[p]`-scalar `((p^j:ℕ):ℚ_[p])`
    show ((p : K) ^ j) • padicLog p x = ((p ^ j : ℕ) : ℚ_[p]) • padicLog p x from by
      rw [smul_eq_mul, Algebra.smul_def, map_natCast]; push_cast; ring,
    smul_smul, inv_mul_cancel₀ hpne, one_smul]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Character values into `K` have norm `≤ 1` (units map to roots of unity of
norm one, non-units to `0`). -/
private theorem norm_dirichletChar_le_one {N : ℕ} [NeZero N] (ψ : DirichletCharacter K N)
    (c : ZMod N) : ‖ψ c‖ ≤ 1 := by
  rcases eq_or_ne (ψ c) 0 with h0 | h0
  · rw [h0, norm_zero]; exact zero_le_one
  · have hu : IsUnit c := by by_contra hu; exact h0 (ψ.map_nonunit hu)
    obtain ⟨u, rfl⟩ := hu
    have hpow : ψ (u : ZMod N) ^ Nat.totient N = 1 := by
      rw [← map_pow, show ((u : ZMod N)) ^ Nat.totient N
          = ((u ^ Nat.totient N : (ZMod N)ˣ) : ZMod N) from
        (Units.val_pow_eq_pow_val u (Nat.totient N)).symm, ZMod.pow_totient, Units.val_one,
        map_one]
    exact le_of_eq (PadicLFunctions.norm_eq_one_of_pow_eq_one (L := K) hpow
      (Nat.totient_pos.2 (NeZero.pos N)).ne')

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `Ring.inverse (1 + X) = ∑ (−1)ⁿ Xⁿ`, hence has integral coefficients. -/
private theorem norm_coeff_inverse_one_add_X_le_one (n : ℕ) :
    ‖PowerSeries.coeff n (Ring.inverse (1 + PowerSeries.X : PowerSeries K))‖ ≤ 1 := by
  have hunit : IsUnit (1 + PowerSeries.X : PowerSeries K) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_add, PowerSeries.constantCoeff_one,
      PowerSeries.constantCoeff_X, add_zero]; exact isUnit_one
  have hgeom : (1 + PowerSeries.X : PowerSeries K)
      * (PowerSeries.mk fun n => (-1) ^ n) = 1 := by
    have := one_add_C_mul_X_mul_geom (R := K) 1
    rwa [map_one, one_mul,
      show (fun n => (-(1 : K)) ^ n) = fun n => (-1 : K) ^ n from rfl] at this
  rw [ring_inverse_eq_of_mul_eq_one hunit hgeom, PowerSeries.coeff_mk, norm_pow, norm_neg,
    norm_one, one_pow]

omit [CompleteSpace K] [CharZero K] in
include hp in
/-- Bounded antiderivative (c₀-design): when `B` has integral coefficients, the
antiderivative `C` (from the coefficient-wise division) has linearly-bounded
coefficients `‖coeff m C‖ ≤ p·(m+1)` — the `(p(m+1))⁻¹`-factor has polynomial
norm. Feeds the convergence of `seriesEval (φ C₁)` in the constant pin. -/
private theorem exists_antideriv_bounded (B : PowerSeries K)
    (hB : ∀ n, ‖PowerSeries.coeff n B‖ ≤ 1) :
    ∃ C : PowerSeries K, PowerSeries.constantCoeff C = 0
      ∧ (p : K) • ((1 + PowerSeries.X) * PowerSeries.derivativeFun C) = B
      ∧ ∀ m, ‖PowerSeries.coeff m C‖ ≤ (p : ℝ) * ((m : ℝ) + 1) := by
  haveI := charZero_of_qpAlgebra (M := K) p
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hunit : IsUnit (1 + PowerSeries.X : PowerSeries K) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_add, PowerSeries.constantCoeff_one,
      PowerSeries.constantCoeff_X, add_zero]; exact isUnit_one
  set E : PowerSeries K := (p : K)⁻¹ • (B * Ring.inverse (1 + PowerSeries.X)) with hE
  have hpinv : ‖((p : K))⁻¹‖ ≤ (p : ℝ) := norm_natCast_inv_le (p := p) (K := K) hp.out.one_le
  -- `‖coeff k E‖ ≤ p`  (integral product scaled by `(p:K)⁻¹` of norm `p`)
  have hEbd : ∀ k, ‖PowerSeries.coeff k E‖ ≤ (p : ℝ) := by
    intro k
    rw [hE, map_smul, smul_eq_mul, norm_mul]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (by rw [mul_one]; exact hpinv)
    rw [PowerSeries.coeff_mul]
    rcases (Finset.antidiagonal k).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, norm_zero]; exact zero_le_one
    obtain ⟨ab, -, hab⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
      (fun ab => PowerSeries.coeff ab.1 B
        * PowerSeries.coeff ab.2 (Ring.inverse (1 + PowerSeries.X)))
    refine hab.trans ?_
    rw [norm_mul]
    exact mul_le_one₀ (hB ab.1) (norm_nonneg _) (norm_coeff_inverse_one_add_X_le_one ab.2)
  refine ⟨PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) E / n, ?_, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, if_pos rfl]
  · have hDC : PowerSeries.derivativeFun
        (PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) E / n) = E := by
      refine PowerSeries.ext fun n => ?_
      rw [PowerSeries.coeff_derivativeFun, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n),
        Nat.add_sub_cancel]
      have hne : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      rw [Nat.cast_succ, div_mul_cancel₀ _ hne]
    rw [hDC, hE, mul_smul_comm, smul_smul, mul_inv_cancel₀ hp0, one_smul,
      mul_comm (1 + PowerSeries.X), mul_assoc, Ring.inverse_mul_cancel _ hunit, mul_one]
  · intro m
    rw [PowerSeries.coeff_mk]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [if_pos rfl, norm_zero]; positivity
    · rw [if_neg (by omega : m ≠ 0), div_eq_mul_inv, norm_mul]
      calc ‖PowerSeries.coeff (m - 1) E‖ * ‖((m : K))⁻¹‖
          ≤ (p : ℝ) * (m : ℝ) :=
            mul_le_mul (hEbd _) (norm_natCast_inv_le (p := p) (K := K) hm) (norm_nonneg _)
              (by positivity)
        _ ≤ (p : ℝ) * ((m : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)

omit [CompleteSpace K] [CharZero K] in
include hp in
/-- For a norm-one argument `‖u − 1‖ = 1` (so `‖u‖ = 1`), the positive-degree
coefficients of `logSeriesAt u` are bounded linearly: `‖coeff n (logSeriesAt u)‖ ≤ n`
for `n ≥ 1` (the `1/n`-factor has norm `≤ n` and `‖u/(u−1)‖ = 1`). -/
private theorem norm_coeff_logSeriesAt_le_of_norm_one {u : K} (hu1 : ‖u - 1‖ = 1)
    {n : ℕ} (hn : 1 ≤ n) : ‖PowerSeries.coeff n (logSeriesAt p K u)‖ ≤ (n : ℝ) := by
  -- `‖u‖ ≤ 1`: `u = (u−1) + 1`, both summands of norm `≤ 1`
  have hunorm : ‖u‖ ≤ 1 := by
    calc ‖u‖ = ‖(u - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ max ‖u - 1‖ ‖(1 : K)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := by rw [hu1, norm_one, max_self]
  rw [logSeriesAt, PowerSeries.coeff_mk, if_neg (by omega : n ≠ 0)]
  have hratio : ‖u / (u - 1)‖ ≤ 1 := by rw [norm_div, hu1, div_one]; exact hunorm
  calc ‖(-1 : K) ^ (n - 1) * ((n : K))⁻¹ * (u / (u - 1)) ^ n‖
      = ‖((n : K))⁻¹‖ * ‖u / (u - 1)‖ ^ n := by
        rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    _ ≤ ‖((n : K))⁻¹‖ * 1 := by
        refine mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hratio) (norm_nonneg _)
    _ = ‖((n : K))⁻¹‖ := mul_one _
    _ ≤ (n : ℝ) := norm_natCast_inv_le (p := p) (K := K) hn

omit [CharZero K] in
include hp in
/-- Lem 6.2 as a coefficient bound: with the contributing roots of norm one,
`‖coeff n F̃‖ ≤ C·(n+1)` for a uniform `C` (the positive-degree coefficients are
linearly bounded; the constant term is absorbed). Hence `seriesEval F̃ z` converges
for `‖z‖ < 1`. -/
private theorem summable_seriesEval_Ftilde {N : ℕ} [NeZero N] (hN : 1 < N)
    {θ : DirichletCharacter K N} {ε : K} (hε : IsPrimitiveRoot ε N)
    (hnorm : ∀ c ∈ Finset.range N, ¬ N ∣ c → ‖ε ^ c - 1‖ = 1)
    {z : K} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => PowerSeries.coeff n (Ftilde p K θ hε) * z ^ n := by
  haveI : Fact (1 < N) := ⟨hN⟩
  -- linear bound `‖coeff n F̃‖ ≤ C·(n+1)` with `C := max ‖coeff 0 F̃‖ 1`
  set C : ℝ := max ‖PowerSeries.constantCoeff (Ftilde p K θ hε)‖ 1 with hC
  refine summable_seriesEval_of_norm_coeff_le_linear (C := C) (fun n => ?_) hz
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- constant term: `‖coeff 0 F̃‖ ≤ C ≤ C·1`
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, Nat.cast_zero]
    calc ‖PowerSeries.constantCoeff (Ftilde p K θ hε)‖ ≤ C := le_max_left _ _
      _ = C * ((0 : ℝ) + 1) := by ring
  · -- positive degree: ultrametric `‖Σ_c term_c‖ ≤ max_c ‖term_c‖ ≤ n ≤ C·(n+1)`
    rw [Ftilde, map_neg, norm_neg, map_sum]
    have hbd : ‖∑ c ∈ Finset.range N, PowerSeries.coeff n
          (PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c))‖ ≤ (n : ℝ) := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun c hc => ?_
      rw [PowerSeries.coeff_C_mul, norm_mul]
      by_cases hcd : N ∣ c
      · -- `θ⁻¹(c) = 0` (non-unit `c`); whole term vanishes
        have hc0 : c = 0 := Nat.eq_zero_of_dvd_of_lt hcd (Finset.mem_range.mp hc)
        rw [hc0, Nat.cast_zero,
          show (θ⁻¹) (0 : ZMod N) = 0 from MulChar.map_nonunit _
            (by rw [isUnit_zero_iff]; exact one_ne_zero ∘ Eq.symm), norm_zero, zero_mul]
        positivity
      · calc ‖θ⁻¹ ((c : ZMod N))‖ * ‖PowerSeries.coeff n (logSeriesAt p K (ε ^ c))‖
            ≤ 1 * (n : ℝ) :=
              mul_le_mul (norm_dirichletChar_le_one _ _)
                (norm_coeff_logSeriesAt_le_of_norm_one (u := ε ^ c) (hnorm c hc hcd) hn)
                (norm_nonneg _) zero_le_one
          _ = (n : ℝ) := one_mul _
    refine le_trans hbd (le_trans ?_ (le_mul_of_one_le_left (by positivity) (le_max_right _ _)))
    linarith

set_option maxHeartbeats 800000 in
-- The c₀-design proof chains many `rw`s over `PowerSeries.coeff`/`derivativeFun`
-- through the heavy `rhoTheta`/`twist` measure terms; the elaboration is heartbeat-heavy.
/-- P6-p6' (the constant pin, c₀-design — replan R6.6; Lem 6.3 made
distribution-free WITHOUT field-level `ψ`): the cleared mass identity
`p·𝓐_ρ(0)·G = p·F̃(0) − Σ_{i<p} F̃(ξ^i−1)`. Internally: `W := C G⁻¹·F̃ −
𝓐_ρ` has `∂W = φ(B)` for the bounded `B = G⁻¹-cleared 𝓐(ψ-part)`, so
`W = φC + c₀` (antiderivative + ker ∂); evaluating at `0` and at the
`ξ^i − 1` (where `φ`-images collapse and `Σ 𝓐_ρ(ξ^i−1) = p·𝓐_{ψρ}(0) = 0`
by `sum_seriesEval_mahlerK` + `psi_rhoTheta`) pins `c₀`.

**Statement-fix (replan R6.6, recorded 2026-06-11):** the original frozen
skeleton omitted the norm hypothesis `hnorm`. It is needed twice: (i) to
discharge the `IsUnit (ε^c − 1)` side-condition of
`one_add_mul_derivative_Ftilde`, and (ii) to bound `‖coeff n F̃‖` linearly so
the evaluations `seriesEval F̃ (ξ^i − 1)` converge (Lem 6.2's `ℛ⁺`-membership,
realised as a coefficient bound). For the contributing `c` (units mod
`D·p^n`) the tame part `D > 1` forces `‖ε^c − 1‖ = 1` (RJW's cyclotomic-product
fact, T612 `norm_one_sub_pow_eq_one`); `hnorm` packages this and is discharged
identically in `LpFunction_one`. -/
theorem p_mul_constantCoeff_mahlerK_rhoTheta {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} {χ : DirichletCharacter (integerRing K) (p ^ n)}
    (_hχ : χ.IsPrimitive)
    {θK : DirichletCharacter K (D * p ^ n)} (hN : 1 < D * p ^ n)
    (hθ1 : θK ≠ 1)
    (_hθK : θK = toFieldChar (DirichletCharacter.changeLevel (Dvd.intro _ rfl) η
      * DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ))
    {ε : K} (hε : IsPrimitiveRoot ε (D * p ^ n)) {ξ : K}
    (hξ : IsPrimitiveRoot ξ p)
    (hnorm : ∀ c ∈ Finset.range (D * p ^ n), ¬ (D * p ^ n) ∣ c → ‖ε ^ c - 1‖ = 1)
    {G : K} (_hG : IsUnit G)
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
  haveI : Fact (1 < D * p ^ n) := ⟨hN⟩
  -- abbreviations for the power-series objects (NOT the heavy measure terms, which
  -- `set` would expensively abstract through `rhoTheta`/`twist`/`muEtaCleared`)
  -- the unit hypothesis for `one_add_mul_derivative_Ftilde`, from `hnorm`
  have hunit : ∀ c ∈ Finset.range (D * p ^ n), ¬ (D * p ^ n) ∣ c → IsUnit (ε ^ c - 1) :=
    fun c hc hcd => isUnit_iff_ne_zero.2 (by
      rw [← norm_pos_iff, hnorm c hc hcd]; exact one_pos)
  -- the `ψ`-part `K`-series `B` (integral coefficients) and the antiderivative `C₁`
  obtain ⟨C₁, hC₁0, hC₁, hC₁bd⟩ := exists_antideriv_bounded (p := p)
    (mahlerK p K (MeasureR.psi p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD))))
    (norm_coeff_mahlerK_le_one _ _)
  -- `(1+X)·∂(C G⁻¹·F̃) = mahlerK tw`  (proven `∂F̃` + `hGtwist`, with `C`-scalar pulled out)
  have hCFder : (1 + PowerSeries.X) * PowerSeries.derivativeFun
        (PowerSeries.C G⁻¹ * Ftilde p K θK hε)
      = mahlerK p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)) := by
    rw [show PowerSeries.derivativeFun (PowerSeries.C G⁻¹ * Ftilde p K θK hε)
          = PowerSeries.C G⁻¹ * PowerSeries.derivativeFun (Ftilde p K θK hε) from by
        rw [show PowerSeries.C G⁻¹ * Ftilde p K θK hε = G⁻¹ • Ftilde p K θK hε from
          (PowerSeries.smul_eq_C_mul _ _).symm, PowerSeries.derivativeFun_smul,
          PowerSeries.smul_eq_C_mul],
      show (1 + PowerSeries.X) * (PowerSeries.C G⁻¹ * PowerSeries.derivativeFun (Ftilde p K θK hε))
          = PowerSeries.C G⁻¹
            * ((1 + PowerSeries.X) * PowerSeries.derivativeFun (Ftilde p K θK hε)) from by ring,
      one_add_mul_derivative_Ftilde hN hθ1 hε hunit, hGtwist]
  -- `(1+X)·∂(𝓐_ρ) = mahlerK tw − φ B`  (Res = 1 − φψ, transported)
  have hAder : (1 + PowerSeries.X) * PowerSeries.derivativeFun
        (mahlerK p K (rhoTheta p K η hζ hD χ))
      = mahlerK p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD))
        - phiSeries p (mahlerK p K
          (MeasureR.psi p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)))) := by
    rw [one_add_mul_derivative_mahlerK_rhoTheta hD1 hη hζ hD χ, res_units_eq, mahlerK_sub,
      mahlerK_phi]
  -- the W-equation: `(1+X)·∂W = φ B` where `W := C G⁻¹·F̃ − 𝓐_ρ`
  have hWder : (1 + PowerSeries.X) * PowerSeries.derivativeFun
        (PowerSeries.C G⁻¹ * Ftilde p K θK hε - mahlerK p K (rhoTheta p K η hζ hD χ))
      = phiSeries p (mahlerK p K
          (MeasureR.psi p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)))) := by
    rw [show PowerSeries.derivativeFun
          (PowerSeries.C G⁻¹ * Ftilde p K θK hε - mahlerK p K (rhoTheta p K η hζ hD χ))
        = PowerSeries.derivativeFun (PowerSeries.C G⁻¹ * Ftilde p K θK hε)
          - PowerSeries.derivativeFun (mahlerK p K (rhoTheta p K η hζ hD χ)) from
        map_sub (PowerSeries.derivative K) _ _,
      mul_sub, hCFder, hAder]
    ring
  -- `(1+X)·∂(φ C₁) = φ B`  (∂φ = p·φ∂ + scalar pull-through)
  have hphiC₁der : (1 + PowerSeries.X) * PowerSeries.derivativeFun (phiSeries p C₁)
      = phiSeries p (mahlerK p K
          (MeasureR.psi p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)))) := by
    rw [one_add_mul_derivative_phiSeries,
      show (p : K) • phiSeries p ((1 + PowerSeries.X) * PowerSeries.derivativeFun C₁)
        = phiSeries p ((p : K) • ((1 + PowerSeries.X) * PowerSeries.derivativeFun C₁)) from by
        rw [PowerSeries.smul_eq_C_mul, ← phiSeries_C_mul, ← PowerSeries.smul_eq_C_mul], hC₁]
  -- `W − φ C₁` is `∂`-killed, hence the constant `C c₀`; set `c₀ := constantCoeff(W − φC₁)`
  have hker : (1 + PowerSeries.X) * PowerSeries.derivativeFun
      ((PowerSeries.C G⁻¹ * Ftilde p K θK hε - mahlerK p K (rhoTheta p K η hζ hD χ))
        - phiSeries p C₁) = 0 := by
    rw [show PowerSeries.derivativeFun
          ((PowerSeries.C G⁻¹ * Ftilde p K θK hε - mahlerK p K (rhoTheta p K η hζ hD χ))
            - phiSeries p C₁)
        = PowerSeries.derivativeFun
            (PowerSeries.C G⁻¹ * Ftilde p K θK hε - mahlerK p K (rhoTheta p K η hζ hD χ))
          - PowerSeries.derivativeFun (phiSeries p C₁) from
        map_sub (PowerSeries.derivative K) _ _,
      mul_sub, hWder, hphiC₁der, sub_self]
  have hWeq := eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero (p := p) hker
  set c₀ := PowerSeries.constantCoeff
    ((PowerSeries.C G⁻¹ * Ftilde p K θK hε - mahlerK p K (rhoTheta p K η hζ hD χ))
      - phiSeries p C₁) with hc₀def
  -- so `W = φ C₁ + C c₀`
  have hWval : PowerSeries.C G⁻¹ * Ftilde p K θK hε - mahlerK p K (rhoTheta p K η hζ hD χ)
      = phiSeries p C₁ + PowerSeries.C c₀ := by rw [← hWeq]; ring
  -- `‖z_j‖ < 1` and `(1 + z_j)^p = 1` for `z_j = ξ^j − 1`
  have hzlt : ∀ j : Fin p, ‖ξ ^ (j : ℕ) - 1‖ < 1 := by
    intro j
    rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hjpos
    · rw [hj0, pow_zero, sub_self, norm_zero]; exact one_pos
    · have hcop : (j : ℕ).Coprime p :=
        Nat.coprime_comm.mp (hp.out.coprime_iff_not_dvd.mpr fun hdvd =>
          absurd (Nat.le_of_dvd hjpos hdvd) (by omega : ¬ p ≤ (j : ℕ)))
      exact (by rw [pow_one] at *; exact hξ.pow_of_coprime (j : ℕ) hcop :
        IsPrimitiveRoot (ξ ^ (j : ℕ)) (p ^ 1)).norm_sub_one_lt (p := p) le_rfl
  have hzp : ∀ j : Fin p, (1 + (ξ ^ (j : ℕ) - 1)) ^ p = 1 := fun j => by
    rw [show (1 : K) + (ξ ^ (j : ℕ) - 1) = ξ ^ (j : ℕ) by ring, ← pow_mul, mul_comm, pow_mul,
      hξ.pow_eq_one, one_pow]
  -- summability facts at `z_j = ξ^j − 1`
  have hsumF : ∀ j : Fin p, Summable fun m : ℕ =>
      PowerSeries.coeff m (Ftilde p K θK hε) * (ξ ^ (j : ℕ) - 1) ^ m := fun j =>
    summable_seriesEval_Ftilde (θ := θK) hN hε hnorm (hzlt j)
  have hsumA : ∀ j : Fin p, Summable fun m : ℕ =>
      PowerSeries.coeff m (mahlerK p K (rhoTheta p K η hζ hD χ)) * (ξ ^ (j : ℕ) - 1) ^ m :=
    fun j => summable_seriesEval_of_norm_coeff_le_one (norm_coeff_mahlerK_le_one _ _) (hzlt j)
  have hsumCF : ∀ j : Fin p, Summable fun m : ℕ =>
      PowerSeries.coeff m (PowerSeries.C G⁻¹ * Ftilde p K θK hε) * (ξ ^ (j : ℕ) - 1) ^ m :=
    fun j => ((hsumF j).mul_left G⁻¹).congr fun m => by rw [PowerSeries.coeff_C_mul, mul_assoc]
  -- the constant series `C c₀` evaluates summably (finite support)
  have hsumCc₀ : ∀ j : Fin p, Summable fun m : ℕ =>
      PowerSeries.coeff m (PowerSeries.C c₀) * (ξ ^ (j : ℕ) - 1) ^ m := fun j =>
    summable_of_ne_finset_zero (s := {0}) fun m hm => by
      rw [PowerSeries.coeff_C, if_neg (by simpa using hm), zero_mul]
  have hsumphiC₁ : ∀ j : Fin p, Summable fun m : ℕ =>
      PowerSeries.coeff m (phiSeries p C₁) * (ξ ^ (j : ℕ) - 1) ^ m := fun j =>
    summable_seriesEval_of_norm_coeff_le_linear (C := (p : ℝ))
      (norm_coeff_phiSeries_le_linear p (C := (p : ℝ)) (by positivity) hC₁bd) (hzlt j)
  -- evaluating `W = φ C₁ + C c₀` at each `z_j` gives `c₀`; on the other side
  -- `seriesEval W z_j = G⁻¹·F̃(z_j) − 𝓐_ρ(z_j)`. Sum over `j`.
  have hsumW : ∑ j : Fin p, (G⁻¹ * seriesEval (Ftilde p K θK hε) (ξ ^ (j : ℕ) - 1)
        - seriesEval (mahlerK p K (rhoTheta p K η hζ hD χ)) (ξ ^ (j : ℕ) - 1))
      = (p : K) * c₀ := by
    rw [show (∑ j : Fin p, (G⁻¹ * seriesEval (Ftilde p K θK hε) (ξ ^ (j : ℕ) - 1)
          - seriesEval (mahlerK p K (rhoTheta p K η hζ hD χ)) (ξ ^ (j : ℕ) - 1)))
        = ∑ j : Fin p, seriesEval
            (PowerSeries.C G⁻¹ * Ftilde p K θK hε
              - mahlerK p K (rhoTheta p K η hζ hD χ)) (ξ ^ (j : ℕ) - 1) from
      Finset.sum_congr rfl fun j _ => by
        rw [seriesEval_sub (hsumCF j) (hsumA j), seriesEval_C_mul]]
    rw [show (∑ j : Fin p, seriesEval
            (PowerSeries.C G⁻¹ * Ftilde p K θK hε
              - mahlerK p K (rhoTheta p K η hζ hD χ)) (ξ ^ (j : ℕ) - 1))
        = ∑ _j : Fin p, c₀ from Finset.sum_congr rfl fun j _ => by
      rw [hWval, seriesEval_add (hsumphiC₁ j) (hsumCc₀ j),
        seriesEval_phi_at_root_of_summable p
          (summable_prod_of_norm_coeff_le_linear p (C := (p : ℝ)) hC₁bd (hzlt j)) (hzp j),
        hC₁0, seriesEval_C, zero_add]]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the `𝓐_ρ`-sum vanishes: `Σ_j 𝓐_ρ(z_j) = p·constantCoeff (mahlerK (ψρ)) = 0`
  have hAsum : ∑ j : Fin p, seriesEval (mahlerK p K (rhoTheta p K η hζ hD χ)) (ξ ^ (j : ℕ) - 1)
      = 0 := by
    rw [sum_seriesEval_mahlerK (p := p) hξ (rhoTheta p K η hζ hD χ), psi_rhoTheta hζ hD χ]
    simp [mahlerK]
  -- `p·c₀ = G⁻¹·Σ_j F̃(z_j)`
  have hexpand : (p : K) * c₀ = G⁻¹ * ∑ j : Fin p, seriesEval (Ftilde p K θK hε) (ξ ^ (j : ℕ) - 1)
      := by rw [← hsumW, Finset.sum_sub_distrib, ← Finset.mul_sum, hAsum, sub_zero]
  -- `c₀ = G⁻¹·constantCoeff F̃ − constantCoeff 𝓐_ρ` (evaluate `W = φC₁ + C c₀` at `0`)
  have hcWexp : c₀ = G⁻¹ * PowerSeries.constantCoeff (Ftilde p K θK hε)
      - PowerSeries.constantCoeff (mahlerK p K (rhoTheta p K η hζ hD χ)) := by
    have : c₀ = PowerSeries.constantCoeff
        (PowerSeries.C G⁻¹ * Ftilde p K θK hε - mahlerK p K (rhoTheta p K η hζ hD χ)) := by
      rw [hWval, map_add, constantCoeff_phiSeries, hC₁0, zero_add, PowerSeries.constantCoeff_C]
    rw [this, map_sub, map_mul, PowerSeries.constantCoeff_C]
  -- assemble the displayed identity
  have h1 : (p : K) * c₀ = (p : K) * (G⁻¹ * PowerSeries.constantCoeff (Ftilde p K θK hε))
      - (p : K) * PowerSeries.constantCoeff (mahlerK p K (rhoTheta p K η hζ hD χ)) := by
    rw [hcWexp]; ring
  rw [hexpand] at h1
  linear_combination h1

/-! #### Helpers for the evaluated trace `sum_seriesEval_Ftilde` (T616, RJW TeX 2113–2155)

The route (decomposition R6 P6-p7 + replans R6.3/R6.6): a per-term resummation
`seriesEval (logSeriesAt (ε^c)) (ξ^i − 1) = extLog(ξ^i·ε^c − 1)` (split constant +
tail, the tail being `padicLog` of `1 + ε^c(ξ^i−1)/(ε^c−1)` via the T618 layer), the
`μ_p`-collapse `Σ_{i<p} extLog(ξ^i·ε^c − 1) = extLog(ε^{pc} − 1)`
(`IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul` + `extLog_prod`), and the `c ↦ pc`
bookkeeping (automorphism for `¬p∣N`; primitive-character fiber sums for `p∣N`). -/

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- A root of unity is integral over `ℤ` (it satisfies the monic `Xⁿ − C 1`). -/
private theorem isIntegral_of_pow_eq_one {x : K} {n : ℕ} (hn : 0 < n) (hx : x ^ n = 1) :
    IsIntegral ℤ x :=
  ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [hx]⟩

omit [CompleteSpace K] [CharZero K] in
/-- The shifted root `ξ^i·ε^c − 1` has norm one (`‖ε^c − 1‖ = 1` and the isoceles
`‖ξ^i ε^c − ε^c‖ = ‖ξ^i − 1‖ < 1 = ‖ε^c − 1‖`). -/
private theorem norm_pow_mul_pow_sub_one_eq_one {ε ξ : K} {N : ℕ} (hN0 : 0 < N)
    (hε : IsPrimitiveRoot ε N) {c i : ℕ}
    (hc1 : ‖ε ^ c - 1‖ = 1) (hil : ‖ξ ^ i - 1‖ < 1) :
    ‖ξ ^ i * ε ^ c - 1‖ = 1 := by
  have hεc1 : ‖ε ^ c‖ = 1 :=
    norm_eq_one_of_pow_eq_one (L := K) (m := N)
      (by rw [← pow_mul, mul_comm, pow_mul, hε.pow_eq_one, one_pow]) hN0.ne'
  have hlt : ‖ξ ^ i * ε ^ c - ε ^ c‖ < ‖ε ^ c - 1‖ := by
    rw [show ξ ^ i * ε ^ c - ε ^ c = (ξ ^ i - 1) * ε ^ c from by ring, norm_mul, hεc1,
      mul_one, hc1]; exact hil
  have hkey := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt hlt)
  rw [show (ξ ^ i * ε ^ c - ε ^ c) + (ε ^ c - 1) = ξ ^ i * ε ^ c - 1 from by ring,
    max_eq_right hlt.le, hc1] at hkey
  exact hkey

omit [CompleteSpace K] [CharZero K] in
include hp in
/-- T616 step 3 (domain engine): the shifted root `ξ^i·ε^c − 1` lies in the extended-log
domain — it is integral (a root of unity minus `1`) and has norm one. -/
private theorem extLogDomain_pow_mul_pow_sub_one {ε ξ : K} {N : ℕ} (hN0 : 0 < N)
    (hε : IsPrimitiveRoot ε N) (hξ : IsPrimitiveRoot ξ p) {c i : ℕ}
    (hc1 : ‖ε ^ c - 1‖ = 1) (hil : ‖ξ ^ i - 1‖ < 1) :
    ExtLogDomain p (ξ ^ i * ε ^ c - 1) :=
  extLogDomain_of_integral_norm_one p
    ((((isIntegral_of_pow_eq_one (n := p) hp.out.pos hξ.pow_eq_one).pow i).mul
      ((isIntegral_of_pow_eq_one (n := N) hN0 hε.pow_eq_one).pow c)).sub isIntegral_one)
    (norm_pow_mul_pow_sub_one_eq_one hN0 hε hc1 hil)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The positive-degree coefficients of `logSeriesAt u` factor through `formalLog`:
`coeff (n+1) (logSeriesAt u) = coeff (n+1) (formalLog) · (u/(u−1))^{n+1}`. -/
private theorem coeff_succ_logSeriesAt (u : K) (n : ℕ) :
    PowerSeries.coeff (n + 1) (logSeriesAt p K u)
      = PowerSeries.coeff (n + 1) (formalLog K) * (u / (u - 1)) ^ (n + 1) := by
  rw [logSeriesAt, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n), coeff_succ_formalLog,
    Nat.add_sub_cancel, Nat.cast_succ]

omit [CharZero K] in
include hp in
/-- Summability of `seriesEval (logSeriesAt u) z` for `‖u − 1‖ = 1`, `‖z‖ < 1` (the
positive coefficients are `≤ n`; the constant `extLog(u−1)` is absorbed into `C`). -/
private theorem summable_seriesEval_logSeriesAt {u z : K} (hu1 : ‖u - 1‖ = 1) (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => PowerSeries.coeff n (logSeriesAt p K u) * z ^ n := by
  set C : ℝ := max ‖extLog p (u - 1)‖ 1 with hC
  refine summable_seriesEval_of_norm_coeff_le_linear (C := C) (fun n => ?_) hz
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [logSeriesAt, PowerSeries.coeff_mk, if_pos rfl, Nat.cast_zero]
    calc ‖extLog p (u - 1)‖ ≤ C := le_max_left _ _
      _ = C * ((0 : ℝ) + 1) := by ring
  · refine le_trans (norm_coeff_logSeriesAt_le_of_norm_one (p := p) hu1 hn) ?_
    calc (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
      _ ≤ C * ((n : ℝ) + 1) := le_mul_of_one_le_left (by positivity) (le_max_right _ _)

omit [CharZero K] in
include hp in
/-- T616 step 1 (the per-term resummation, half a): for `‖u − 1‖ = 1` and `‖z‖ < 1`,
`seriesEval (logSeriesAt u) z = extLog(u − 1) + padicLog (1 + u·z/(u−1))`. Split the
constant coefficient `extLog(u−1)` off and identify the tail with `seriesEval (formalLog)
(u·z/(u−1)) = padicLog (1 + u·z/(u−1))` (T618 eval-alignment). -/
private theorem seriesEval_logSeriesAt_of_norm {u z : K} (hu1 : ‖u - 1‖ = 1) (hz : ‖z‖ < 1) :
    seriesEval (logSeriesAt p K u) z
      = extLog p (u - 1) + padicLog p (1 + u * z / (u - 1)) := by
  -- `‖u‖ = 1`, so `‖w‖ = ‖u·z/(u−1)‖ = ‖z‖ < 1`
  have hunorm : ‖u‖ ≤ 1 := by
    calc ‖u‖ = ‖(u - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ max ‖u - 1‖ ‖(1 : K)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := by rw [hu1, norm_one, max_self]
  have hwnorm : ‖u * z / (u - 1)‖ < 1 := by
    rw [norm_div, hu1, div_one, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hunorm) hz
  have hsum := summable_seriesEval_logSeriesAt (p := p) hu1 hz
  have hcoeff0 : PowerSeries.coeff 0 (logSeriesAt p K u) = extLog p (u - 1) := by
    rw [logSeriesAt, PowerSeries.coeff_mk, if_pos rfl]
  -- the `padicLog`/`formalLog` tail at `w := u·z/(u−1)`
  have htail : padicLog p (1 + u * z / (u - 1))
      = seriesEval (formalLog K) (u * z / (u - 1)) := by
    rw [← seriesEval_formalLog (p := p)
      (show ‖(1 + u * z / (u - 1)) - 1‖ < 1 from by rw [add_sub_cancel_left]; exact hwnorm),
      add_sub_cancel_left]
  rw [seriesEval, hsum.tsum_eq_zero_add, hcoeff0, pow_zero, mul_one, htail, seriesEval,
    (summable_seriesEval_formalLog (p := p) hwnorm).tsum_eq_zero_add, coeff_zero_formalLog,
    zero_mul, zero_add]
  refine congrArg _ (tsum_congr fun n => ?_)
  rw [coeff_succ_logSeriesAt, coeff_succ_formalLog,
    show u * z / (u - 1) = (u / (u - 1)) * z from by ring, mul_pow]
  ring

omit [CompleteSpace K] [CharZero K] in
include hp in
/-- T616: any element of the open unit ball `‖x − 1‖ < 1` lies in the extended-log
domain (a `p`-power iterate lands in the exp ball; `exists_pPow_pow_inExpBall`). -/
private theorem extLogDomain_of_norm_sub_one_lt_one {x : K} (hx : ‖x - 1‖ < 1) :
    ExtLogDomain p x := by
  obtain ⟨j, hj⟩ := exists_pPow_pow_inExpBall (p := p) hx
  exact ⟨p ^ j, 0, x ^ p ^ j, pow_pos hp.out.pos j, by rw [zpow_zero, one_mul], hj⟩

omit [CharZero K] in
include hp in
/-- T616 step 1 (the per-term identity): for `‖ε^c − 1‖ = 1` and `‖ξ^i − 1‖ < 1`
(with `ε` integral over `ℤ`), `seriesEval (logSeriesAt (ε^c)) (ξ^i − 1) =
extLog(ξ^i·ε^c − 1)`. Combine the resummation (`seriesEval_logSeriesAt_of_norm`) with
the factorisation `ξ^i·ε^c − 1 = (ε^c − 1)·(1 + ε^c(ξ^i−1)/(ε^c−1))` and
`extLog_mul`/`extLog_eq_padicLog`. -/
private theorem seriesEval_logSeriesAt_eq_extLog {ε ξ : K} (hεint : IsIntegral ℤ ε) {c i : ℕ}
    (hc1 : ‖ε ^ c - 1‖ = 1) (hil : ‖ξ ^ i - 1‖ < 1) :
    seriesEval (logSeriesAt p K (ε ^ c)) (ξ ^ i - 1) = extLog p (ξ ^ i * ε ^ c - 1) := by
  set u : K := ε ^ c with hu
  set z : K := ξ ^ i - 1 with hz
  have hune : (u - 1) ≠ 0 := by rw [← norm_pos_iff, hu, hc1]; exact one_pos
  -- `‖u‖ = 1`, `‖w‖ = ‖u z/(u−1)‖ = ‖z‖ < 1`
  have hunorm : ‖u‖ ≤ 1 := by
    calc ‖u‖ = ‖(u - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ max ‖u - 1‖ ‖(1 : K)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := by rw [hu, hc1, norm_one, max_self]
  have hwnorm : ‖u * z / (u - 1)‖ < 1 := by
    rw [norm_div, hu, hc1, div_one, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hunorm) hil
  have hwsub : ‖(1 + u * z / (u - 1)) - 1‖ < 1 := by rw [add_sub_cancel_left]; exact hwnorm
  -- the factorisation `ξ^i ε^c − 1 = (u − 1)·(1 + u z/(u−1))`
  have hfac : ξ ^ i * ε ^ c - 1 = (u - 1) * (1 + u * z / (u - 1)) := by
    rw [← hu, show ξ ^ i = z + 1 from by rw [hz]; ring]
    field_simp
    ring
  rw [seriesEval_logSeriesAt_of_norm (p := p) hc1 hil, hfac,
    extLog_mul p (extLogDomain_of_integral_norm_one p
      ((hεint.pow c).sub isIntegral_one) (by rw [← hu]; exact hc1))
      (extLogDomain_of_norm_sub_one_lt_one (p := p) hwsub),
    extLog_eq_padicLog_of_norm_lt_one (p := p) hwsub]

omit [CharZero K] in
include hp in
/-- A `±1` sign is invisible to `extLog`: `extLog((−1)^m · x) = extLog x`
(induction via `extLog_neg`). -/
private theorem extLog_neg_one_pow_mul {x : K} (hx : ExtLogDomain p x) (m : ℕ) :
    extLog p ((-1 : K) ^ m * x) = extLog p x := by
  induction m with
  | zero => rw [pow_zero, one_mul]
  | succ k ih =>
    have hdom : ExtLogDomain p ((-1 : K) ^ k * x) :=
      ExtLogDomain.mul p
        (extLogDomain_of_integral_norm_one p ((IsIntegral.neg isIntegral_one).pow k)
          (by rw [norm_pow, norm_neg, norm_one, one_pow])) hx
    rw [pow_succ, show (-1 : K) ^ k * (-1) * x = -((-1) ^ k * x) from by ring,
      extLog_neg p hdom, ih]

omit [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
include hp in
/-- Reindex a `Fin p`-sum over the powers of a primitive `p`-th root as a sum over
`nthRootsFinset p 1` (`i ↦ ξ^i` is a bijection). -/
private theorem sum_fin_pow_eq_sum_nthRootsFinset {ξ : K} (hξ : IsPrimitiveRoot ξ p)
    (f : K → K) :
    ∑ i : Fin p, f (ξ ^ (i : ℕ)) = ∑ ζ ∈ Polynomial.nthRootsFinset p (1 : K), f ζ := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine Finset.sum_nbij (fun i => ξ ^ (i : ℕ))
    (fun i _ => (Polynomial.mem_nthRootsFinset hp.out.pos (1 : K)).mpr (by
      rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]))
    (fun a _ b _ hab => Fin.ext (hξ.pow_inj a.2 b.2 hab)) (fun ζ hζ => ?_) (fun i _ => rfl)
  -- surjectivity: every `ζ ∈ nthRootsFinset p 1` is `ξ^i` for some `i < p`
  obtain ⟨i, hik, rfl⟩ := hξ.eq_pow_of_pow_eq_one
    ((Polynomial.mem_nthRootsFinset hp.out.pos (1 : K)).mp hζ)
  exact ⟨⟨i, hik⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩

omit [CharZero K] in
include hp in
/-- T616 step 3 (the `μ_p`-collapse): for a primitive `p`-th root `ξ`, an `‖·‖ = 1`
unit `ε^c` (`ε` integral over `ℤ`) with `‖ξ^i − 1‖ < 1`,
`Σ_{i<p} extLog(ξ^i·ε^c − 1) = extLog(ε^{pc} − 1)`. Uses the product identity
`∏_{i<p}(ξ^i·Y − 1) = (−1)^{p+1}·(Y^p − 1)`
(`IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul`), `extLog_prod`, and the sign-stripping
`extLog_neg_one_pow_mul`. -/
private theorem sum_extLog_pow_mul_collapse {ε ξ : K} {N : ℕ} (hN0 : 0 < N)
    (hε : IsPrimitiveRoot ε N) (hεint : IsIntegral ℤ ε) (hξ : IsPrimitiveRoot ξ p) {c : ℕ}
    (hc1 : ‖ε ^ c - 1‖ = 1) (hil : ∀ i : Fin p, ‖ξ ^ (i : ℕ) - 1‖ < 1) :
    ∑ i : Fin p, extLog p (ξ ^ (i : ℕ) * ε ^ c - 1) = extLog p (ε ^ (p * c) - 1) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  -- each factor `ξ^i ε^c − 1` is in the extended-log domain
  have hdomζ : ∀ ζ ∈ Polynomial.nthRootsFinset p (1 : K),
      ExtLogDomain p (ζ * ε ^ c - 1) := by
    intro ζ hζmem
    obtain ⟨i, hik, rfl⟩ := hξ.eq_pow_of_pow_eq_one
      ((Polynomial.mem_nthRootsFinset hp.out.pos (1 : K)).mp hζmem)
    exact extLogDomain_pow_mul_pow_sub_one hN0 hε hξ hc1 (hil ⟨i, hik⟩)
  -- the `μ_p` product identity: `∏_ζ (ζ·ε^c − 1) = (−1)^p·(1 − ε^{pc})`
  have hprodId : ∏ ζ ∈ Polynomial.nthRootsFinset p (1 : K), (ζ * ε ^ c - 1)
      = (-1 : K) ^ p * (1 - (ε ^ c) ^ p) := by
    rw [show (1 : K) - (ε ^ c) ^ p = (1 : K) ^ p - (ε ^ c) ^ p from by rw [one_pow],
      hξ.pow_sub_pow_eq_prod_sub_mul (x := 1) (y := ε ^ c) hp.out.pos,
      show (-1 : K) ^ p = ∏ _ζ ∈ Polynomial.nthRootsFinset p (1 : K), (-1 : K) from by
        rw [Finset.prod_const, hξ.card_nthRootsFinset],
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun ζ _ => by ring
  -- `‖ε^{pc} − 1‖ = ‖(ε^c)^p − 1‖ = 1` (product of the norm-one factors `ξ^i ε^c − 1`)
  have hnorm_pc : ‖(ε ^ c) ^ p - 1‖ = 1 := by
    have hnormprod : ‖∏ ζ ∈ Polynomial.nthRootsFinset p (1 : K), (ζ * ε ^ c - 1)‖ = 1 := by
      rw [norm_prod, Finset.prod_eq_one fun ζ hζmem => ?_]
      obtain ⟨i, hik, rfl⟩ := hξ.eq_pow_of_pow_eq_one
        ((Polynomial.mem_nthRootsFinset hp.out.pos (1 : K)).mp hζmem)
      exact norm_pow_mul_pow_sub_one_eq_one hN0 hε hc1 (hil ⟨i, hik⟩)
    rw [hprodId, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      show (1 : K) - (ε ^ c) ^ p = -((ε ^ c) ^ p - 1) from by ring, norm_neg] at hnormprod
    exact hnormprod
  rw [sum_fin_pow_eq_sum_nthRootsFinset hξ (fun ζ => extLog p (ζ * ε ^ c - 1)),
    ← extLog_prod p _ _ hdomζ, hprodId,
    show (-1 : K) ^ p * (1 - (ε ^ c) ^ p) = (-1 : K) ^ (p + 1) * ((ε ^ c) ^ p - 1) from by
      rw [pow_succ]; ring,
    extLog_neg_one_pow_mul (extLogDomain_of_integral_norm_one p
      (((hεint.pow c).pow p).sub isIntegral_one) hnorm_pc),
    ← pow_mul, mul_comm c p]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- T616 step 4 (the `p∣N` primitive-character fiber sum, replan R6.3): for a primitive
`ψ : DirichletCharacter K N` and `M ∣ N` with `ψ` NOT factoring through `M`, the sum of
`ψ` over any residue fibre `{c : ZMod N | c ≡ r mod M}` vanishes. Proof: pick a unit
`v ≡ 1 mod M` with `ψ v ≠ 1` (failure of factoring), and note `c ↦ v·c` permutes the
fibre (it fixes residues mod M), so `S = ψ(v)·S`, forcing `S = 0`. -/
private theorem sum_dirichlet_fiber_eq_zero {N M : ℕ} [NeZero N] (hMN : M ∣ N)
    {ψ : DirichletCharacter K N} (hψ : ¬ ψ.FactorsThrough M) (r : ZMod M) :
    ∑ c ∈ Finset.univ.filter (fun c : ZMod N => ZMod.castHom hMN (ZMod M) c = r), ψ c = 0 := by
  classical
  -- a unit `v ≡ 1 mod M` (i.e. in `ker (unitsMap hMN)`) with `ψ v ≠ 1`
  obtain ⟨v, hvker, hvψ⟩ : ∃ v : (ZMod N)ˣ, ZMod.unitsMap hMN v = 1 ∧ ψ.toUnitHom v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hψ ((DirichletCharacter.factorsThrough_iff_ker_unitsMap hMN).mpr fun v hv => by
      rw [MonoidHom.mem_ker]; exact hcon v (by rwa [MonoidHom.mem_ker] at hv))
  -- `castHom hMN (v : ZMod N) = 1`
  have hvcast : ZMod.castHom hMN (ZMod M) (v : ZMod N) = 1 := by
    have := congrArg (Units.val) hvker
    rwa [ZMod.unitsMap_val, Units.val_one] at this
  -- `ψ (v : ZMod N) ≠ 1`
  have hvψ' : ψ ((v : ZMod N)) ≠ 1 := by
    rw [← MulChar.coe_toUnitHom ψ v, Ne, Units.val_eq_one]; exact hvψ
  -- `castHom hMN (v⁻¹ : ZMod N) = 1` too
  have hvcastinv : ZMod.castHom hMN (ZMod M) ((v⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := by
    have hinv : ZMod.unitsMap hMN v⁻¹ = 1 := by rw [map_inv, hvker, inv_one]
    have := congrArg Units.val hinv
    rwa [ZMod.unitsMap_val, Units.val_one] at this
  set S := ∑ c ∈ Finset.univ.filter (fun c : ZMod N => ZMod.castHom hMN (ZMod M) c = r), ψ c with hS
  -- `c ↦ v·c` permutes the fibre, twisting the sum by `ψ v`
  have hperm : S = ψ ((v : ZMod N)) * S := by
    rw [hS, Finset.mul_sum]
    refine (Finset.sum_nbij' (fun c => (v : ZMod N) * c) (fun c => (v⁻¹ : (ZMod N)ˣ) * c)
      ?_ ?_ ?_ ?_ ?_).symm
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      rw [map_mul, hvcast, one_mul]; exact hc
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      rw [map_mul, hvcastinv, one_mul]; exact hc
    · intro c _; rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    · intro c _; rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    · intro c _; rw [map_mul]
  -- `(1 − ψ v)·S = 0` with `ψ v ≠ 1`
  have : (1 - ψ ((v : ZMod N))) * S = 0 := by rw [sub_mul, one_mul, ← hperm]; ring
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h).symm hvψ'
  · exact h

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
include hp in
/-- T616 step 4 (the `c ↦ pc` bookkeeping, both cases — replans R6.3): for primitive
`θ` of level `N > 1` and a primitive `N`-th root `ε`,
`Σ_{c<N} θ⁻¹(c)·extLog(ε^{pc} − 1) = θ(p)·Σ_{c<N} θ⁻¹(c)·extLog(ε^c − 1)`. The function
`extLog(ε^a − 1)` is `ε`-cyclic so reindexes over `ZMod N`; for `¬p∣N` the unit `p`
substitutes (`c ↦ pc`, `θ⁻¹(p⁻¹) = θ(p)`); for `p∣N` both sides vanish — `θ(p) = 0`
and the `LHS` groups along the `p`-to-`1` map into fibres killed by
`sum_dirichlet_fiber_eq_zero` (primitivity of `θ⁻¹`). -/
private theorem sum_theta_inv_mul_extLog_pc {N : ℕ} [NeZero N] (hN : 1 < N)
    {θ : DirichletCharacter K N} (hprim : θ.IsPrimitive) {ε : K} (hε : IsPrimitiveRoot ε N) :
    ∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N)) * extLog p (ε ^ (p * c) - 1)
      = θ ((p : ZMod N)) * ∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N)) * extLog p (ε ^ c - 1) := by
  classical
  haveI : Fact (1 < N) := ⟨hN⟩
  -- `g a := extLog(ε^{a.val} − 1)` on `ZMod N`; `ε` is cyclic so `ε^k = ε^{(k:ZMod N).val}`
  set g : ZMod N → K := fun a => extLog p (ε ^ a.val - 1) with hgdef
  have hcyc : ∀ k : ℕ, ε ^ k = ε ^ ((k : ZMod N)).val := fun k => by
    conv_lhs => rw [← Nat.div_add_mod k N, pow_add, pow_mul, hε.pow_eq_one, one_pow, one_mul]
    rw [ZMod.val_natCast]
  -- reindex both `range N` sums over `ZMod N`, identifying `extLog(ε^c − 1) = g c`
  have hreindex : ∀ f : ZMod N → K, ∑ c ∈ Finset.range N, f ((c : ZMod N))
      = ∑ a : ZMod N, f a := fun f =>
    Finset.sum_nbij' (fun c => ((c : ℕ) : ZMod N)) (fun a => a.val)
      (fun c _ => Finset.mem_univ _) (fun a _ => Finset.mem_range.mpr (ZMod.val_lt a))
      (fun c hc => ZMod.val_natCast_of_lt (Finset.mem_range.mp hc))
      (fun a _ => ZMod.natCast_zmod_val a) (fun c _ => rfl)
  have hLHS : ∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N)) * extLog p (ε ^ (p * c) - 1)
      = ∑ a : ZMod N, θ⁻¹ a * g (((p : ℕ) : ZMod N) * a) := by
    rw [← hreindex (fun a => θ⁻¹ a * g (((p : ℕ) : ZMod N) * a))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hgdef]
    simp only
    rw [show ((p : ℕ) : ZMod N) * ((c : ℕ) : ZMod N) = ((p * c : ℕ) : ZMod N) from by
      push_cast; ring]
    rw [← hcyc (p * c)]
  have hRHS : ∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N)) * extLog p (ε ^ c - 1)
      = ∑ a : ZMod N, θ⁻¹ a * g a := by
    rw [← hreindex (fun a => θ⁻¹ a * g a)]
    exact Finset.sum_congr rfl fun c _ => by rw [hgdef]; simp only; rw [← hcyc c]
  rw [hLHS, hRHS]
  by_cases hpN : (p : ℕ) ∣ N
  · -- `p ∣ N`: both sides vanish
    have hpnu : ¬ IsUnit ((p : ℕ) : ZMod N) := by
      rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd hp.out]; exact fun h => h hpN
    rw [θ.map_nonunit hpnu, zero_mul]
    -- group the `a`-sum along the `p`-to-`1` map `a ↦ p·a` (fibres mod `N/p`)
    obtain ⟨M, rfl⟩ := hpN
    have hM0 : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h | h
      · rw [h, mul_zero] at hN; omega
      · exact h
    haveI : NeZero M := ⟨hM0.ne'⟩
    have hMdvd : M ∣ p * M := dvd_mul_left M p
    -- `θ⁻¹` does not factor through `M = N/p < N` (else conductor ≤ M < N)
    have hnotft : ¬ (θ⁻¹).FactorsThrough M := by
      intro hft
      have hcond : (θ⁻¹).conductor ≤ M :=
        Nat.sInf_le ⟨hft.dvd, hft.χ₀, hft.eq_changeLevel⟩
      rw [DirichletCharacter.conductor_inv, hprim] at hcond
      have hMlt : M < p * M := by nlinarith [hp.out.one_lt, hM0]
      omega
    -- `p·a` depends only on `a mod M` (the `p`-multiple kills the `M`-difference)
    have hpconst : ∀ a : ZMod (p * M), ((p : ℕ) : ZMod (p * M)) * a
        = ((p : ℕ) : ZMod (p * M)) * ((ZMod.castHom hMdvd (ZMod M) a).val : ZMod (p * M)) := by
      intro a
      rw [show ((p : ℕ) : ZMod (p * M)) * a = ((p * a.val : ℕ) : ZMod (p * M)) from by
          rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id],
        show ((p : ℕ) : ZMod (p * M)) * ((ZMod.castHom hMdvd (ZMod M) a).val : ZMod (p * M))
          = ((p * (ZMod.castHom hMdvd (ZMod M) a).val : ℕ) : ZMod (p * M)) from by
          rw [Nat.cast_mul],
        ZMod.natCast_eq_natCast_iff]
      -- `p·a.val ≡ p·(cast_M a).val [MOD p·M]` since `a.val ≡ (cast_M a).val [MOD M]`
      have hmod : a.val ≡ (ZMod.castHom hMdvd (ZMod M) a).val [MOD M] := by
        have hval : (ZMod.castHom hMdvd (ZMod M) a).val = a.val % M := by
          rw [ZMod.castHom_apply, ← ZMod.natCast_val a, ZMod.val_natCast]
        rw [hval]; exact (Nat.mod_modEq a.val M).symm
      exact hmod.mul_left' p
    -- `g (p·a)` is constant on each fibre `{a : cast_M a = r}`; sum over fibres of `θ⁻¹`
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun a : ZMod (p * M) => ZMod.castHom hMdvd (ZMod M) a)
      (fun a _ => Finset.mem_univ _)]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [show (∑ a ∈ Finset.univ.filter (fun a => ZMod.castHom hMdvd (ZMod M) a = r),
          θ⁻¹ a * g (((p : ℕ) : ZMod (p * M)) * a))
        = (∑ a ∈ Finset.univ.filter (fun a => ZMod.castHom hMdvd (ZMod M) a = r), θ⁻¹ a)
          * g (((p : ℕ) : ZMod (p * M)) * ((r.val : ZMod (p * M)))) from ?_,
      sum_dirichlet_fiber_eq_zero hMdvd hnotft r, zero_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [hpconst a, ha]
  · -- `¬p∣N`: `p` is a unit; substitute `a ↦ p·a`
    obtain ⟨u, hpu⟩ : IsUnit ((p : ℕ) : ZMod N) :=
      (ZMod.isUnit_iff_coprime p N).mpr ((hp.out.coprime_iff_not_dvd).mpr hpN)
    have hθθinv : θ ((p : ℕ) : ZMod N) * θ⁻¹ ((p : ℕ) : ZMod N) = 1 := by
      rw [← MulChar.mul_apply, mul_inv_cancel θ, MulChar.one_apply (hpu ▸ u.isUnit)]
    rw [Finset.mul_sum]
    refine Finset.sum_nbij' (fun a => ((p : ℕ) : ZMod N) * a)
      (fun a => ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * a) (fun a _ => Finset.mem_univ _)
      (fun a _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro a _; rw [← hpu, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    · intro a _; rw [← hpu, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    · intro a _
      -- `f a = θ⁻¹(a)·g(p·a)` equals `g'(p·a) = θ(p)·(θ⁻¹(p·a)·g(p·a))`
      rw [map_mul, ← mul_assoc, ← mul_assoc, hθθinv, one_mul]

omit [CharZero K] in
/-- P6-p7' (the evaluated trace, ψ-free form — replan R6.6):
`Σ_{i<p} F̃(ξ^i−1) = θ(p)·F̃(0)` — for `n = 0` by the `c ↦ pc` automorphism
and the `μ_p`-collapse `Σ_ξ extLog(ξw−1) = extLog(w^p−1)`; for `n ≥ 1`
both sides vanish (`θ(p) = 0`; primitive-character fiber sums —
replan R6.3).

**Statement-fix (replan R6.6, recorded 2026-06-11 in `b2_log.jsonl`):** the
frozen `hdom : ∀ c, ¬N∣c → ExtLogDomain (ε^c − 1)` is too weak — the per-term
identity needs the SHIFTED arguments `ξ^i·ε^c − 1` to lie in the extended-log
domain, which does not follow from `hdom` in the ramified case (`ε^c` reducing
to `1`). It is replaced by the norm-one hypothesis
`hnorm : ∀ c, ¬N∣c → ‖ε^c − 1‖ = 1`, from which every shifted domain follows
(`‖ξ^i ε^c − 1‖ = 1` by ultrametric isoceles + roots-of-unity integrality, then
`extLogDomain_of_integral_norm_one`). `LpFunction_one` discharges `hnorm` from
the tame `D > 1` cyclotomic-product fact (T612 `norm_one_sub_pow_eq_one`),
preserving its provability.

The analytic prerequisite (boundary `p`-adic-log multiplicativity
`extLog (1 + w) = padicLog (1 + w)` for `‖w‖ < 1`, since the arguments `ξ^i − 1`,
`i ≠ 0`, sit on the exp-ball boundary `‖·‖^{p−1} = p⁻¹`) is supplied by the T618
layer (`extLog_eq_padicLog_of_norm_lt_one` / `padicLog_pow_p_of_norm_lt_one`,
above). The proof assembles: the per-term identity
`seriesEval (logSeriesAt (ε^c)) (ξ^i − 1) = extLog(ξ^i·ε^c − 1)`
(`seriesEval_logSeriesAt_eq_extLog`); the `μ_p`-collapse
`Σ_{i<p} extLog(ξ^i·ε^c − 1) = extLog(ε^{pc} − 1)` (`sum_extLog_pow_mul_collapse`);
and the `c ↦ pc` bookkeeping `Σ_c θ⁻¹(c)·extLog(ε^{pc} − 1) = θ(p)·Σ_c θ⁻¹(c)·
extLog(ε^c − 1)` (`sum_theta_inv_mul_extLog_pc`: automorphism for `¬p∣N`,
primitive-character fiber sums for `p∣N`). -/
theorem sum_seriesEval_Ftilde {N : ℕ} [NeZero N] (hN : 1 < N)
    {θ : DirichletCharacter K N} (hprim : θ.IsPrimitive) (_hθ1 : θ ≠ 1)
    {ε : K} (hε : IsPrimitiveRoot ε N) {ξ : K}
    (hξ : IsPrimitiveRoot ξ p)
    (hnorm : ∀ c ∈ Finset.range N, ¬ N ∣ c → ‖ε ^ c - 1‖ = 1) :
    ∑ i : Fin p, seriesEval (Ftilde p K θ hε) (ξ ^ (i : ℕ) - 1)
      = θ ((p : ZMod N)) * PowerSeries.constantCoeff (Ftilde p K θ hε) := by
  haveI : Fact (1 < N) := ⟨hN⟩
  have hεint : IsIntegral ℤ ε := isIntegral_of_pow_eq_one (NeZero.pos N) hε.pow_eq_one
  -- `θ⁻¹ c = 0` exactly when `N ∣ c` (in `range N`, that is `c = 0`)
  have hθ0 : ∀ c ∈ Finset.range N, N ∣ c → θ⁻¹ ((c : ZMod N)) = 0 := fun c hc hcd => by
    rw [show ((c : ℕ) : ZMod N) = 0 from by
      rw [Nat.eq_zero_of_dvd_of_lt hcd (Finset.mem_range.mp hc), Nat.cast_zero]]
    exact MulChar.map_nonunit _ (by rw [isUnit_zero_iff]; exact one_ne_zero ∘ Eq.symm)
  -- `‖ξ^i − 1‖ < 1` for every `i : Fin p`
  have hzlt : ∀ i : Fin p, ‖ξ ^ (i : ℕ) - 1‖ < 1 := by
    intro i
    rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hipos
    · rw [hi0, pow_zero, sub_self, norm_zero]; exact one_pos
    · have hcop : (i : ℕ).Coprime p :=
        Nat.coprime_comm.mp (hp.out.coprime_iff_not_dvd.mpr fun hdvd =>
          absurd (Nat.le_of_dvd hipos hdvd) (by omega : ¬ p ≤ (i : ℕ)))
      exact (by rw [pow_one] at *; exact hξ.pow_of_coprime (i : ℕ) hcop :
        IsPrimitiveRoot (ξ ^ (i : ℕ)) (p ^ 1)).norm_sub_one_lt (p := p) le_rfl
  -- Step A: `seriesEval F̃ (ξ^i − 1) = −Σ_c θ⁻¹(c)·extLog(ξ^i·ε^c − 1)`
  have hstepA : ∀ i : Fin p, seriesEval (Ftilde p K θ hε) (ξ ^ (i : ℕ) - 1)
      = -∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N)) * extLog p (ξ ^ (i : ℕ) * ε ^ c - 1) := by
    intro i
    rw [Ftilde, seriesEval_neg]
    refine congrArg Neg.neg ?_
    -- expand `seriesEval (Σ_c C(θ⁻¹c)·logSeriesAt) (ξ^i−1) = Σ_c θ⁻¹(c)·seriesEval(logSeriesAt)`
    rw [seriesEval,
      show (∑' n : ℕ, PowerSeries.coeff n (∑ c ∈ Finset.range N,
            PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c)) * (ξ ^ (i : ℕ) - 1) ^ n)
        = ∑' n : ℕ, ∑ c ∈ Finset.range N, PowerSeries.coeff n
            (PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c)) * (ξ ^ (i : ℕ) - 1) ^ n
        from tsum_congr fun n => by rw [map_sum, Finset.sum_mul]]
    rw [Summable.tsum_finsetSum fun c hc => ?_]
    · refine Finset.sum_congr rfl fun c hc => ?_
      by_cases hcd : N ∣ c
      · rw [hθ0 c hc hcd]
        simp only [zero_mul, map_zero, tsum_zero]
      · rw [show (∑' n : ℕ, PowerSeries.coeff n
              (PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c))
                * (ξ ^ (i : ℕ) - 1) ^ n)
            = θ⁻¹ ((c : ZMod N)) * seriesEval (logSeriesAt p K (ε ^ c)) (ξ ^ (i : ℕ) - 1) from by
          rw [seriesEval, ← (summable_seriesEval_logSeriesAt (p := p) (hnorm c hc hcd)
            (hzlt i)).tsum_mul_left]
          exact tsum_congr fun n => by rw [PowerSeries.coeff_C_mul, mul_assoc],
          seriesEval_logSeriesAt_eq_extLog (p := p) hεint (hnorm c hc hcd) (hzlt i)]
    · -- summability of each `c`-term at `ξ^i − 1`
      by_cases hcd : N ∣ c
      · refine (summable_of_ne_finset_zero (s := ∅) fun n _ => ?_)
        rw [PowerSeries.coeff_C_mul, hθ0 c hc hcd, zero_mul, zero_mul]
      · exact ((summable_seriesEval_logSeriesAt (p := p) (hnorm c hc hcd)
          (hzlt i)).mul_left (θ⁻¹ ((c : ZMod N)))).congr fun n => by
            rw [PowerSeries.coeff_C_mul, mul_assoc]
  -- Step B: sum Step A over `i`, swap, apply the `μ_p`-collapse per `c`
  rw [Finset.sum_congr rfl fun i _ => hstepA i]
  -- `Σ_i (−Σ_c ...) = −Σ_c (Σ_i ...)`  then the `μ_p`-collapse on the inner `i`-sum
  rw [show (∑ i : Fin p, -∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N))
            * extLog p (ξ ^ (i : ℕ) * ε ^ c - 1))
        = -∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N))
            * ∑ i : Fin p, extLog p (ξ ^ (i : ℕ) * ε ^ c - 1) from by
      calc (∑ i : Fin p, -∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N))
              * extLog p (ξ ^ (i : ℕ) * ε ^ c - 1))
          = -∑ i : Fin p, ∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N))
              * extLog p (ξ ^ (i : ℕ) * ε ^ c - 1) := by rw [← Finset.sum_neg_distrib]
        _ = -∑ c ∈ Finset.range N, ∑ i : Fin p, θ⁻¹ ((c : ZMod N))
              * extLog p (ξ ^ (i : ℕ) * ε ^ c - 1) := by rw [Finset.sum_comm]
        _ = -∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N))
              * ∑ i : Fin p, extLog p (ξ ^ (i : ℕ) * ε ^ c - 1) := by
            refine congrArg Neg.neg (Finset.sum_congr rfl fun c _ => ?_)
            rw [Finset.mul_sum]]
  -- collapse `Σ_i extLog(ξ^i ε^c − 1) = extLog(ε^{pc} − 1)` per contributing `c`
  rw [show (∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N))
            * ∑ i : Fin p, extLog p (ξ ^ (i : ℕ) * ε ^ c - 1))
        = ∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N)) * extLog p (ε ^ (p * c) - 1) from
    Finset.sum_congr rfl fun c hc => by
      by_cases hcd : N ∣ c
      · rw [hθ0 c hc hcd, zero_mul, zero_mul]
      · rw [sum_extLog_pow_mul_collapse (p := p) (NeZero.pos N) hε hεint hξ
          (hnorm c hc hcd) hzlt]]
  -- the `c ↦ pc` bookkeeping + the constant-coefficient identity
  rw [sum_theta_inv_mul_extLog_pc (p := p) hN hprim hε,
    show PowerSeries.constantCoeff (Ftilde p K θ hε)
        = -∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N)) * extLog p (ε ^ c - 1) from ?_]
  · ring
  · -- `constantCoeff F̃ = −Σ_c θ⁻¹(c)·extLog(ε^c − 1)` (coeff 0 of `logSeriesAt = extLog(ε^c−1)`)
    rw [Ftilde, map_neg, map_sum, neg_inj]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, PowerSeries.constantCoeff_C, logSeriesAt,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, if_pos rfl]

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
