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

omit [hp : Fact p.Prime] in
/-- The substitution series `(1+T)^p − 1` always has constant coefficient `0`,
so `φ = subst` is well-defined over any `CommRing`. -/
lemma hasSubst_one_add_X_pow_sub_one :
    PowerSeries.HasSubst ((1 + PowerSeries.X) ^ p - 1 : PowerSeries R) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)

omit [hp : Fact p.Prime] in
@[simp]
lemma phiSeries_zero : phiSeries p (0 : PowerSeries R) = 0 := by
  rw [phiSeries, ← PowerSeries.coe_substAlgHom (hasSubst_one_add_X_pow_sub_one p), map_zero]

/-- The digit-decomposition predicate: `G` is a family of `p` digits for `F`
along `φ`, i.e. `F = Σ_{i<p} (1+T)^i·φ(G_i)`. -/
def IsDigitDecomp (F : PowerSeries R) (G : Fin p → PowerSeries R) : Prop :=
  F = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (G i)

/-- W6b-b2: the formal trace operator `ψ` — the `0`-th digit of the
(unique, over an integral base such as `integerRing K`) digit decomposition.

**Replan R6 W6b-b1' (statement defect, recorded 2026-06-11, `.mathlib-quality/
b2_log.jsonl`):** the digit decomposition `F = Σ_{i<p} (1+T)^i·φ(G_i)` is the
`p`-adically-*integral* structure. Over a `CommRing` in which `p` is invertible
it is FALSE: `(1+T)^p − 1` then has unit linear coefficient, so `φ` is a
substitution by an order-`1` series with unit leading term, hence bijective
(`PowerSeries.substInvOfIsUnit`), and the digits are wildly non-unique
(counterexample `R = ℚ`, `p = 2`: `T` has an `S`-expansion). The
existence-uniqueness theorem `existsUnique_digits` is therefore proved over
`integerRing K` (where `S ≡ T^p mod p` is distinguished); see the bridge
section. Here `psiSeries` is junk-totalised over a general `CommRing R` (`0`
when no unique decomposition exists) so the `K`-coefficient users
(`ValuesAtOne.lean`) keep type-checking. -/
noncomputable def psiSeries (F : PowerSeries R) : PowerSeries R :=
  open Classical in
  if h : ∃! G : Fin p → PowerSeries R, IsDigitDecomp p F G then h.exists.choose 0
  else 0

/-- Whenever `F` has a unique digit decomposition, `psiSeries` is its `0`-th
digit (general `CommRing` version; the `∃!` hypothesis selects the integral
locus). -/
theorem psiSeries_eq_of_unique {F : PowerSeries R} {G : Fin p → PowerSeries R}
    (hex : ∃! G : Fin p → PowerSeries R, IsDigitDecomp p F G)
    (hG : IsDigitDecomp p F G) :
    psiSeries p F = G 0 := by
  rw [psiSeries, dif_pos hex, hex.unique hex.exists.choose_spec hG]

omit [hp : Fact p.Prime] in
/-- `map f` commutes with `φ` (substitution into `(1+T)^p − 1`, which is fixed
by `map f`). -/
lemma map_phiSeries {S : Type*} [CommRing S] (f : R →+* S) (G : PowerSeries R) :
    PowerSeries.map f (phiSeries p G) = phiSeries p (PowerSeries.map f G) := by
  have hmap : PowerSeries.map f ((1 + PowerSeries.X) ^ p - 1 : PowerSeries R)
      = (1 + PowerSeries.X) ^ p - 1 := by
    simp [map_sub, map_pow, map_add]
  have hcoeffB : ∀ (m d : ℕ),
      PowerSeries.coeff m (((1 + PowerSeries.X) ^ p - 1 : PowerSeries S) ^ d)
        = f (PowerSeries.coeff m (((1 + PowerSeries.X) ^ p - 1 : PowerSeries R) ^ d)) :=
    fun m d => by rw [← hmap, ← map_pow, PowerSeries.coeff_map]
  have hvanishR : ∀ (m d : ℕ), m < d →
      PowerSeries.coeff m (((1 + PowerSeries.X) ^ p - 1 : PowerSeries R) ^ d) = 0 :=
    fun m d hmd => PowerSeries.X_pow_dvd_iff.1
      (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 (by simp)) d) m hmd
  have hvanishS : ∀ (m d : ℕ), m < d →
      PowerSeries.coeff m (((1 + PowerSeries.X) ^ p - 1 : PowerSeries S) ^ d) = 0 :=
    fun m d hmd => PowerSeries.X_pow_dvd_iff.1
      (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 (by simp)) d) m hmd
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, phiSeries, phiSeries,
    PowerSeries.coeff_subst' (hasSubst_one_add_X_pow_sub_one p),
    PowerSeries.coeff_subst' (hasSubst_one_add_X_pow_sub_one p),
    finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (n + 1)) (by
      intro d hd
      simp only [Function.mem_support] at hd
      by_contra hmem
      simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hmem
      exact hd (by rw [hvanishR _ _ (by omega), smul_zero])),
    finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (n + 1)) (by
      intro d hd
      simp only [Function.mem_support] at hd
      by_contra hmem
      simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hmem
      exact hd (by rw [hvanishS _ _ (by omega), smul_zero])),
    map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [PowerSeries.coeff_map, hcoeffB, smul_eq_mul, smul_eq_mul, map_mul]

omit [hp : Fact p.Prime] in
/-- `map f` sends a digit decomposition of `F` to one of `map f F`. -/
lemma isDigitDecomp_map {S : Type*} [CommRing S] (f : R →+* S)
    {F : PowerSeries R} {G : Fin p → PowerSeries R} (hG : IsDigitDecomp p F G) :
    IsDigitDecomp p (PowerSeries.map f F) (fun i => PowerSeries.map f (G i)) := by
  rw [IsDigitDecomp, hG, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_add, map_one, PowerSeries.map_X, map_phiSeries]

/-- W6b-b3' (realigned, replan R6.6): the `∂φ = p·φ∂` commutation for
`∂ = (1+T)d/dT` — the only derivative fact the c₀-design needs (the
field-level `ψ∂`-form is meaningless since `psiSeries` is junk over
fields). -/
theorem one_add_mul_derivative_phiSeries (F : PowerSeries R) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun (phiSeries p F)
      = (p : R) • phiSeries p
          ((1 + PowerSeries.X) * PowerSeries.derivativeFun F) := by sorry

end digits

section integral

/-!
### The digit decomposition over `integerRing K` (W6b-b1, integral form)

**Replan R6 W6b-b1'** (recorded `.mathlib-quality/b2_log.jsonl`, 2026-06-11):
the digit decomposition is the `p`-adically-integral statement (false over a
ring where `p` is invertible — see `psiSeries`). It is proved here over
`R := integerRing K` by transporting the measure-level `p`-residue
decomposition through the ring isomorphism `mahlerRingEquiv` (RJW Thm 3.20):
`(1+T)^i ↔ δ_i`, `φ ↔ MeasureR.phi`, so
`F = Σ_{i<p} (1+T)^i·φ(G_i)  ↔  μ = Σ_{i<p} δ_i * MeasureR.phi(ν_i)`, and the
latter is the residue-class digit decomposition built from `MeasureR.phi_psi`
(`φψ = Res_{pℤ_p}`) and the partition `ℤ_p = ⊔_{i<p} (i + pℤ_p)`.
-/

variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

open MeasureR

/-- `δ_a * μ` is the translate `y ↦ μ(f(a + ·))` (convolution by a Dirac is a
pushforward along addition). -/
lemma dirac_mul_eq_pushforward (a : ℤ_[p]) (μ : MeasureR K ℤ_[p]) :
    dirac K ℤ_[p] a * μ
      = pushforward K ℤ_[p] ℤ_[p] ⟨fun y => a + y, by fun_prop⟩ μ := by
  refine LinearMap.ext fun f => ?_
  rw [mul_apply, dirac_apply, convInner_apply, pushforward_apply]

omit [CompleteSpace K] in
/-- The series-side of `MeasureR.phi`: `𝓐_{φμ} = phiSeries 𝓐_μ` (R-level
Eq. (3.9), the `integerRing K` analogue of `mahlerTransform_phi`). -/
theorem mahlerTransform_phi (μ : MeasureR K ℤ_[p]) :
    mahlerTransform p K (MeasureR.phi p K μ)
      = phiSeries p (mahlerTransform p K μ) := by
  let B : PowerSeries (integerRing K) := (1 + PowerSeries.X) ^ p - 1
  let BZ : PowerSeries ℤ_[p] := (1 + PowerSeries.X) ^ p - 1
  have hconst : PowerSeries.constantCoeff B = 0 := by simp [B]
  have hsub : PowerSeries.HasSubst B := PowerSeries.HasSubst.of_constantCoeff_zero' hconst
  have hvanish : ∀ {m d : ℕ}, m < d → PowerSeries.coeff m (BZ ^ d) = 0 := fun {m d} hmd =>
    PowerSeries.X_pow_dvd_iff.1
      (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 (by simp [BZ])) d) m hmd
  -- `B` is the `algebraMap`-image of `BZ`
  have hBmap : B = PowerSeries.map (algebraMap ℤ_[p] (integerRing K)) BZ := by
    change (1 + PowerSeries.X) ^ p - 1
      = PowerSeries.map (algebraMap ℤ_[p] (integerRing K)) ((1 + PowerSeries.X) ^ p - 1)
    simp [map_sub, map_pow, map_add]
  have hcoeffB : ∀ (m d : ℕ), PowerSeries.coeff m (B ^ d)
      = algebraMap ℤ_[p] (integerRing K) (PowerSeries.coeff m (BZ ^ d)) := fun m d => by
    rw [hBmap, ← map_pow, PowerSeries.coeff_map]
  refine PowerSeries.ext fun n => ?_
  rw [phiSeries, PowerSeries.coeff_subst' hsub,
    finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (n + 1)) (by
      intro d hd
      simp only [Function.mem_support] at hd
      by_contra hmem
      simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hmem
      exact hd (by rw [hcoeffB, hvanish (by omega), map_zero, smul_zero]))]
  -- the `ℤ_p`-level Chu–Vandermonde for `mahler n (p * k)`
  have key : ∀ k : ℕ, mahler n ((p : ℤ_[p]) * (k : ℤ_[p]))
      = ∑ d ∈ Finset.range (n + 1),
          PowerSeries.coeff n (BZ ^ d) * ((k.choose d : ℕ) : ℤ_[p]) := by
    intro k
    have lhs_eq : mahler n ((p : ℤ_[p]) * (k : ℤ_[p]))
        = PowerSeries.coeff n ((BZ + 1) ^ k) := by
      have hpk : ((p : ℤ_[p]) * (k : ℤ_[p])) = ((p * k : ℕ) : ℤ_[p]) := by push_cast; ring
      have hb1 : (BZ + 1 : PowerSeries ℤ_[p]) = (1 + PowerSeries.X) ^ p := by
        change ((1 + PowerSeries.X) ^ p - 1) + 1 = (1 + PowerSeries.X) ^ p
        rw [sub_add_cancel]
      rw [hpk, mahler_natCast_eq, hb1, ← pow_mul, ← binomialSeries_nat (R := ℤ_[p]),
        binomialSeries_coeff, Ring.choose_natCast, smul_eq_mul, mul_one]
    have expand : PowerSeries.coeff n ((BZ + 1) ^ k)
        = ∑ d ∈ Finset.range (k + 1),
            PowerSeries.coeff n (BZ ^ d) * ((k.choose d : ℕ) : ℤ_[p]) := by
      rw [add_pow, map_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [one_pow, mul_one, ← map_natCast (PowerSeries.C (R := ℤ_[p])) (k.choose d),
        PowerSeries.coeff_mul_C]
    rw [lhs_eq, expand]
    rcases le_total k n with hkn | hnk
    · refine Finset.sum_subset (by intro d hd; simp only [Finset.mem_range] at *; omega)
        (fun d hd hnd => ?_)
      simp only [Finset.mem_range, not_lt] at hnd
      simp only [Finset.mem_range] at hd
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
    · refine (Finset.sum_subset (by intro d hd; simp only [Finset.mem_range] at *; omega)
        (fun d hd hnd => ?_)).symm
      simp only [Finset.mem_range, not_lt] at hnd
      rw [hvanish (by omega), zero_mul]
  -- transport the function identity through the algebra map
  have hfun : (mahlerCM p K n).comp (PadicMeasure.mulCM p (p : ℤ_[p]))
      = ∑ d ∈ Finset.range (n + 1),
          (PowerSeries.coeff n (B ^ d)) • (mahlerCM p K d) := by
    apply ContinuousMap.coe_injective
    refine PadicInt.denseRange_natCast.equalizer (map_continuous _) (map_continuous _)
      (funext fun k => ?_)
    change algebraMap ℤ_[p] (integerRing K) (mahler n ((p : ℤ_[p]) * (k : ℤ_[p]))) = _
    rw [key k, map_sum, Function.comp_apply, ContinuousMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [ContinuousMap.coe_smul, Pi.smul_apply, mahlerCM_apply, mahler_natCast_eq,
      smul_eq_mul, hcoeffB, map_mul, map_natCast]
  rw [coeff_mahlerTransform]
  change μ ((mahlerCM p K n).comp (PadicMeasure.mulCM p (p : ℤ_[p]))) = _
  rw [hfun, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, smul_eq_mul, coeff_mahlerTransform, smul_eq_mul, mul_comm]

omit [CompleteSpace K] in
/-- `𝓐_{δ_i} = (1+T)^i`. -/
lemma mahlerTransform_dirac_natCast (i : ℕ) :
    mahlerTransform p K (dirac K ℤ_[p] ((i : ℕ) : ℤ_[p]))
      = (1 + PowerSeries.X) ^ i := by
  rw [mahlerTransform_dirac, binomialSeries_nat, map_pow, map_add, map_one,
    PowerSeries.map_X]

/-- A translate of a `φ`-image by a unit is supported off `pℤ_p`, hence killed
by `ψ`: `ψ(δ_a * φν) = 0` when `‖a‖ = 1`. -/
lemma psi_dirac_mul_phi_eq_zero {a : ℤ_[p]} (ha : ‖a‖ = 1) (ν : MeasureR K ℤ_[p]) :
    MeasureR.psi p K (dirac K ℤ_[p] a * MeasureR.phi p K ν) = 0 := by
  refine LinearMap.ext fun f => ?_
  rw [show MeasureR.psi p K (dirac K ℤ_[p] a * MeasureR.phi p K ν) f
      = (dirac K ℤ_[p] a * MeasureR.phi p K ν)
          (charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p)
            * f.comp (PadicMeasure.shiftDiv p)) from rfl,
    mul_apply, dirac_apply, convInner_apply]
  rw [LinearMap.zero_apply, MeasureR.phi, pushforward_apply]
  rw [show ((charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p)
        * f.comp (PadicMeasure.shiftDiv p)).comp
          ⟨fun y => a + y, by fun_prop⟩).comp (PadicMeasure.mulCM p (p : ℤ_[p]))
      = (0 : C(ℤ_[p], integerRing K)) from ?_, map_zero]
  refine ContinuousMap.ext fun z => ?_
  simp only [ContinuousMap.comp_apply, ContinuousMap.mul_apply, charFnCM_apply,
    PadicMeasure.mulCM, ContinuousMap.coe_mk, ContinuousMap.coe_zero, Pi.zero_apply]
  have hnotmem : (a + (p : ℤ_[p]) * z) ∉ {y : ℤ_[p] | ‖y‖ < 1} := by
    simp only [Set.mem_setOf_eq, not_lt]
    have hpz : ‖(p : ℤ_[p]) * z‖ < 1 := PadicMeasure.mem_pZp_of_mul p
    by_contra hlt
    push Not at hlt
    have hane : ‖a‖ ≤ max ‖a + (p : ℤ_[p]) * z‖ ‖(p : ℤ_[p]) * z‖ := by
      calc ‖a‖ = ‖(a + (p : ℤ_[p]) * z) + -((p : ℤ_[p]) * z)‖ := by
            rw [add_neg_cancel_right]
        _ ≤ max ‖a + (p : ℤ_[p]) * z‖ ‖-((p : ℤ_[p]) * z)‖ :=
            IsUltrametricDist.norm_add_le_max _ _
        _ = max ‖a + (p : ℤ_[p]) * z‖ ‖(p : ℤ_[p]) * z‖ := by rw [norm_neg]
    rw [ha] at hane
    exact absurd (hane.trans_lt (max_lt hlt hpz)) (lt_irrefl _)
  rw [Set.indicator_of_notMem hnotmem, zero_mul]

/-- The unit-translate norm fact for digits: `‖(i:ℤ_[p]) − (j:ℤ_[p])‖ = 1` for
distinct `i, j < p`. -/
lemma norm_natCast_sub_natCast_eq_one {i j : ℕ} (hi : i < p) (hj : j < p)
    (hij : i ≠ j) : ‖((i : ℕ) : ℤ_[p]) - ((j : ℕ) : ℤ_[p])‖ = 1 := by
  have hkey : ∀ m : ℕ, 0 < m → m < p → ‖((m : ℕ) : ℤ_[p])‖ = 1 :=
      fun m hm0 hmp => by
    rw [PadicInt.norm_natCast_eq_one_iff, hp.out.coprime_iff_not_dvd]
    exact fun hdvd => absurd (Nat.le_of_dvd hm0 hdvd) (by omega)
  rcases le_total j i with hle | hle
  · have hsub : ((i : ℕ) : ℤ_[p]) - ((j : ℕ) : ℤ_[p]) = ((i - j : ℕ) : ℤ_[p]) := by
      rw [Nat.cast_sub hle]
    rw [hsub]
    exact hkey (i - j) (by omega) (by omega)
  · have hsub : ((i : ℕ) : ℤ_[p]) - ((j : ℕ) : ℤ_[p]) = -(((j - i : ℕ) : ℤ_[p])) := by
      rw [Nat.cast_sub hle]; ring
    rw [hsub, norm_neg]
    exact hkey (j - i) (by omega) (by omega)

omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
/-- The residue partition `ℤ_p = ⊔_{i<p} (i + pℤ_p)`, coefficient form: for each
`y`, exactly one digit `i < p` lies in the same residue, so the indicator sum is
`1`. -/
lemma sum_charFn_pZp_sub_natCast (y : ℤ_[p]) :
    ∑ i : Fin p, (charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p)
        (y - ((i : ℕ) : ℤ_[p]))) = 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  -- the unique digit in `Fin p`
  set c : Fin p := ⟨(PadicInt.toZModPow 1 y).val,
    by simpa [pow_one] using ZMod.val_lt (PadicInt.toZModPow 1 y)⟩ with hc
  -- the membership criterion `y - i ∈ pℤ_p` holds exactly for `i = c`
  have hcrit : ∀ i : Fin p,
      (y - ((i : ℕ) : ℤ_[p])) ∈ {z : ℤ_[p] | ‖z‖ < 1} ↔ i = c := by
    intro i
    have hdvd_ker : (p : ℤ_[p]) ∣ (y - ((i : ℕ) : ℤ_[p]))
        ↔ PadicInt.toZModPow 1 (y - ((i : ℕ) : ℤ_[p])) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one, Ideal.mem_span_singleton]
    rw [Set.mem_setOf_eq, PadicInt.norm_lt_one_iff_dvd, hdvd_ker,
      map_sub, sub_eq_zero, map_natCast]
    have hival : ((i : ℕ) : ZMod (p ^ 1)).val = (i : ℕ) :=
      ZMod.val_natCast_of_lt (by rw [pow_one]; exact i.2)
    constructor
    · intro h
      refine Fin.ext ?_
      rw [hc, ← hival, ← h]
    · intro h
      have hi : (i : ℕ) = (PadicInt.toZModPow 1 y).val := by rw [h, hc]
      rw [hi, ZMod.natCast_val, ZMod.cast_id]
  have hiff : ∀ i : Fin p,
      (charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p) (y - ((i : ℕ) : ℤ_[p])))
        = if i = c then (1 : integerRing K) else 0 := by
    intro i
    rw [charFnCM_apply]
    by_cases hmem : (y - ((i : ℕ) : ℤ_[p])) ∈ {z : ℤ_[p] | ‖z‖ < 1}
    · rw [Set.indicator_of_mem hmem, Pi.one_apply, if_pos ((hcrit i).1 hmem)]
    · rw [Set.indicator_of_notMem hmem, if_neg (fun h => hmem ((hcrit i).2 h))]
  simp_rw [hiff]
  rw [Finset.sum_ite_eq' Finset.univ c (fun _ => (1 : integerRing K))]
  simp

/-- Digit extraction: `ψ(δ_{-j} * Σ_i δ_i φ(ν_i)) = ν_j` (the `i = j` term gives
`ψφ = id`; the others are unit-translates killed by `ψ`). -/
lemma psi_dirac_neg_mul_sum (ν : Fin p → MeasureR K ℤ_[p]) (j : Fin p) :
    MeasureR.psi p K (dirac K ℤ_[p] (-((j : ℕ) : ℤ_[p]))
        * ∑ i : Fin p, dirac K ℤ_[p] ((i : ℕ) : ℤ_[p]) * MeasureR.phi p K (ν i))
      = ν j := by
  rw [Finset.mul_sum, MeasureR.psi_sum]
  rw [Finset.sum_eq_single j]
  · rw [← mul_assoc, dirac_mul_dirac, neg_add_cancel, ← MeasureR.one_def, one_mul,
      MeasureR.psi_phi]
  · intro i _ hij
    rw [← mul_assoc, dirac_mul_dirac]
    refine psi_dirac_mul_phi_eq_zero p K ?_ (ν i)
    rw [show -((j : ℕ) : ℤ_[p]) + ((i : ℕ) : ℤ_[p])
        = ((i : ℕ) : ℤ_[p]) - ((j : ℕ) : ℤ_[p]) by ring]
    exact norm_natCast_sub_natCast_eq_one p i.2 j.2 (fun h => hij (Fin.ext h))
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- The measure-level `p`-residue digit decomposition: every measure is
uniquely `Σ_{i<p} δ_i * φ(ν_i)`. -/
theorem existsUnique_measure_digits (μ : MeasureR K ℤ_[p]) :
    ∃! ν : Fin p → MeasureR K ℤ_[p],
      μ = ∑ i : Fin p,
        dirac K ℤ_[p] ((i : ℕ) : ℤ_[p]) * MeasureR.phi p K (ν i) := by
  refine ⟨fun j => MeasureR.psi p K (dirac K ℤ_[p] (-((j : ℕ) : ℤ_[p])) * μ), ?_, ?_⟩
  · -- existence
    refine LinearMap.ext fun f => ?_
    -- the digit-`i` reconstruction function `y ↦ 1_{pℤ_p}(y - i)·f(y)`
    set hfun : Fin p → C(ℤ_[p], integerRing K) := fun i =>
      (charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p)).comp
          ⟨fun y => y - ((i : ℕ) : ℤ_[p]), by fun_prop⟩ * f with hhfun
    -- each term `(δ_i * φ(ψ(δ_{-i}μ))) f = μ(hfun i)` via `φψ = Res_{pℤ_p}`
    have hterm : ∀ i : Fin p,
        (dirac K ℤ_[p] ((i : ℕ) : ℤ_[p]) * MeasureR.phi p K (MeasureR.psi p K
            (dirac K ℤ_[p] (-((i : ℕ) : ℤ_[p])) * μ))) f
          = μ (hfun i) := by
      intro i
      rw [MeasureR.phi_psi, dirac_mul_eq_pushforward, pushforward_apply,
        MeasureR.res, cmul_apply, dirac_mul_eq_pushforward, pushforward_apply]
      refine congrArg μ (ContinuousMap.ext fun y => ?_)
      simp only [hhfun, ContinuousMap.mul_apply, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk, charFnCM_apply]
      rw [show -((i : ℕ) : ℤ_[p]) + y = y - ((i : ℕ) : ℤ_[p]) by ring,
        show ((i : ℕ) : ℤ_[p]) + (y - ((i : ℕ) : ℤ_[p])) = y by ring]
    rw [LinearMap.coe_sum, Finset.sum_apply]
    simp_rw [hterm]
    rw [← map_sum]
    refine congrArg μ (ContinuousMap.ext fun y => ?_)
    rw [ContinuousMap.coe_sum, Finset.sum_apply]
    simp only [hhfun, ContinuousMap.mul_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk]
    rw [← Finset.sum_mul,
      show ∑ i : Fin p, (charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p)
          (y - ((i : ℕ) : ℤ_[p]))) = 1 from sum_charFn_pZp_sub_natCast p K y, one_mul]
  · -- uniqueness
    intro ν hν
    funext j
    rw [hν]
    exact (psi_dirac_neg_mul_sum p K ν j).symm

omit [CompleteSpace K] in
/-- `𝓐` is additive over finite sums (the linear-map form, repackaged). -/
private lemma mahlerTransform_sum {ι : Type*} (s : Finset ι)
    (m : ι → MeasureR K ℤ_[p]) :
    mahlerTransform p K (∑ i ∈ s, m i) = ∑ i ∈ s, mahlerTransform p K (m i) :=
  map_sum (mahlerTransformₗ p K) m s

/-- The Mahler transform intertwines the measure-level and series-level digit
decompositions: `𝓐_{Σ δ_i φ(ν_i)} = Σ (1+T)^i · phiSeries(𝓐_{ν_i})`. -/
lemma mahlerTransform_sum_dirac_mul_phi (ν : Fin p → MeasureR K ℤ_[p]) :
    mahlerTransform p K (∑ i : Fin p,
        dirac K ℤ_[p] ((i : ℕ) : ℤ_[p]) * MeasureR.phi p K (ν i))
      = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
          * phiSeries p (mahlerTransform p K (ν i)) := by
  rw [mahlerTransform_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mahlerTransform_mul, mahlerTransform_dirac_natCast, mahlerTransform_phi]

/-- W6b-b1 (integral form): the digit decomposition over `integerRing K`. The
frozen general-`CommRing` statement is false (replan R6 W6b-b1'); this is the
`p`-adically-integral theorem feeding `psiSeries`. -/
theorem existsUnique_digits (F : PowerSeries (integerRing K)) :
    ∃! G : Fin p → PowerSeries (integerRing K), IsDigitDecomp p F G := by
  obtain ⟨ν, hν, hνuniq⟩ := existsUnique_measure_digits p K (ofPowerSeries p K F)
  refine ⟨fun i => mahlerTransform p K (ν i), ?_, ?_⟩
  · -- the transported family is a digit decomposition of `F`
    change F = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
        * phiSeries p (mahlerTransform p K (ν i))
    rw [← mahlerTransform_sum_dirac_mul_phi, ← hν, mahlerTransform_ofPowerSeries]
  · -- uniqueness, pulled back to the measure level
    intro G hG
    have hmeas : ofPowerSeries p K F
        = ∑ i : Fin p, dirac K ℤ_[p] ((i : ℕ) : ℤ_[p])
            * MeasureR.phi p K (ofPowerSeries p K (G i)) := by
      apply mahlerTransform_injective
      rw [mahlerTransform_ofPowerSeries, mahlerTransform_sum_dirac_mul_phi]
      simp_rw [mahlerTransform_ofPowerSeries]
      exact hG
    have hνeq := hνuniq (fun i => ofPowerSeries p K (G i)) hmeas
    funext i
    rw [show G i = mahlerTransform p K (ofPowerSeries p K (G i)) from
      (mahlerTransform_ofPowerSeries (G i)).symm, ← congrFun hνeq i]

/-- Over `integerRing K`, `psiSeries` is the `0`-th digit of *any* digit
decomposition (they all agree by `existsUnique_digits`). -/
theorem psiSeries_eq_of_isDigitDecomp {F : PowerSeries (integerRing K)}
    {G : Fin p → PowerSeries (integerRing K)} (hG : IsDigitDecomp p F G) :
    psiSeries p F = G 0 :=
  psiSeries_eq_of_unique p (existsUnique_digits p K F) hG

/-- The canonical digit family of `phiSeries p G`: `(G, 0, …, 0)`. -/
theorem psiSeries_phi (G : PowerSeries (integerRing K)) :
    psiSeries p (phiSeries p G) = G := by
  refine psiSeries_eq_of_isDigitDecomp p K
    (G := fun i => if i = 0 then G else 0) ?_
  change phiSeries p G = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
      * phiSeries p (if i = 0 then G else 0)
  rw [Finset.sum_eq_single (0 : Fin p)]
  · simp
  · intro i _ hi0
    rw [if_neg hi0, phiSeries_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin p)) h

omit [hp : Fact p.Prime] [CompleteSpace K] in
/-- `φ(C a) = C a`. -/
lemma phiSeries_C (a : integerRing K) :
    phiSeries p (PowerSeries.C a) = PowerSeries.C a := by
  rw [phiSeries]; exact PowerSeries.subst_C a

@[simp]
theorem psiSeries_C (a : integerRing K) :
    psiSeries p (PowerSeries.C a) = PowerSeries.C a := by
  conv_lhs => rw [← phiSeries_C p K a]
  rw [psiSeries_phi]

theorem psiSeries_add (F G : PowerSeries (integerRing K)) :
    psiSeries p (F + G) = psiSeries p F + psiSeries p G := by
  obtain ⟨GF, hGF, -⟩ := existsUnique_digits p K F
  obtain ⟨GG, hGG, -⟩ := existsUnique_digits p K G
  rw [psiSeries_eq_of_isDigitDecomp p K hGF, psiSeries_eq_of_isDigitDecomp p K hGG]
  refine psiSeries_eq_of_isDigitDecomp p K (G := fun i => GF i + GG i) ?_
  change F + G = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
      * phiSeries p (GF i + GG i)
  rw [hGF, hGG, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [phiSeries, phiSeries, phiSeries,
    PowerSeries.subst_add (hasSubst_one_add_X_pow_sub_one p), mul_add]

theorem psiSeries_C_mul (a : integerRing K) (F : PowerSeries (integerRing K)) :
    psiSeries p (PowerSeries.C a * F)
      = PowerSeries.C a * psiSeries p F := by
  obtain ⟨GF, hGF, -⟩ := existsUnique_digits p K F
  rw [psiSeries_eq_of_isDigitDecomp p K hGF]
  refine psiSeries_eq_of_isDigitDecomp p K (G := fun i => PowerSeries.C a * GF i) ?_
  change PowerSeries.C a * F = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
      * phiSeries p (PowerSeries.C a * GF i)
  rw [hGF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [phiSeries, phiSeries,
    PowerSeries.subst_mul (hasSubst_one_add_X_pow_sub_one p),
    show ((PowerSeries.C a).subst ((1 + PowerSeries.X) ^ p - 1)
        : PowerSeries (integerRing K)) = PowerSeries.C a from PowerSeries.subst_C a]
  ring

/-- W6b-b8: `ψ` commutes with coefficient maps (out of `integerRing K`), on
the locus where the image again has a unique digit decomposition (always the
case when `S` is itself such an integral coefficient ring; the hypothesis
makes the statement sound over the junk-totalised `psiSeries` — replan R6
W6b-b1'). -/
theorem psiSeries_map {S : Type*} [CommRing S] (f : integerRing K →+* S)
    (F : PowerSeries (integerRing K))
    (hS : ∃! G : Fin p → PowerSeries S, IsDigitDecomp p (PowerSeries.map f F) G) :
    psiSeries p (PowerSeries.map f F)
      = PowerSeries.map f (psiSeries p F) := by
  obtain ⟨GF, hGF, -⟩ := existsUnique_digits p K F
  rw [psiSeries_eq_of_isDigitDecomp p K hGF,
    psiSeries_eq_of_unique p hS (isDigitDecomp_map p f hGF)]

end integral

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

variable (K) in
/-- The `K`-mapped Mahler transform (the NonTame `map subtype` idiom; home
moved here from ValuesAtOne at the R6.6 realignment). -/
noncomputable def mahlerK (μ : MeasureR K ℤ_[p]) : PowerSeries K :=
  PowerSeries.map (integerRing K).subtype (MeasureR.mahlerTransform p K μ)

/-- W6b-b6' (the realised `Eqphipsi`, evaluation form at `T = 0`, stated at
the INTEGRAL level where the digit decomposition is honest — replan R6.6):
with `ξ` a primitive `p`-th root of unity,
`Σ_{i<p} 𝓐_μ(ξ^i − 1) = p·𝓐_{ψμ}(0)` (evaluate the measure-level digit
decomposition at `ξ^i − 1`, where `(1+(ξ^i−1))^p − 1 = 0` collapses the
`φ`-layer; then `Σ_i ξ^{ij} = p·[j ≡ 0]` orthogonality; summability is
automatic from the bounded integral coefficients and `‖ξ^i − 1‖ < 1`). -/
theorem sum_seriesEval_mahlerK {ξ : K} (hξ : IsPrimitiveRoot ξ p)
    (μ : MeasureR K ℤ_[p]) :
    ∑ i : Fin p, seriesEval (mahlerK p K μ) (ξ ^ (i : ℕ) - 1)
      = (p : K) * PowerSeries.constantCoeff
          (mahlerK p K (MeasureR.psi p K μ)) := by sorry

/-- The formal antiderivative over `K` (char 0): every series is
`p·∂C` for a `C` vanishing at `0` (coefficient-wise division; replan
R6.6 — the c₀-design's existence half). -/
theorem exists_antideriv (B : PowerSeries K) :
    ∃ C : PowerSeries K, PowerSeries.constantCoeff C = 0
      ∧ (p : K) • ((1 + PowerSeries.X) * PowerSeries.derivativeFun C)
        = B := by sorry

/-- W6b-b7: the kernel of `∂ = (1+T)d/dT` is the constants
(char-zero coefficients). -/
theorem eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero
    {F : PowerSeries K}
    (h : (1 + PowerSeries.X) * PowerSeries.derivativeFun F = 0) :
    F = PowerSeries.C (PowerSeries.constantCoeff F) := by sorry

end bridge

end PadicLFunctions
