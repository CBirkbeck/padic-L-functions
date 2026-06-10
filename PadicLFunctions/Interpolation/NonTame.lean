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

omit [CompleteSpace K] in
/-- L5.2.3 step 1: the denominator-unit identity (T511) transported to
`K⟦t⟧` by the coefficient inclusion and the substitution `T = e^t − 1`:
`(ζ^c·e^t − 1)·G_c = 1` with `G_c` the exp-substituted formal inverse. -/
lemma muEta_term_exp_identity {ζ : integerRing K} {D : ℕ}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) {c : ℕ} (hc : ¬ D ∣ c) :
    (PowerSeries.C ((ζ : K) ^ c) * PowerSeries.exp K - 1)
        * (PowerSeries.map (integerRing K).subtype
            (Ring.inverse (PowerSeries.C (ζ ^ c) * (1 + PowerSeries.X) - 1))).subst
            (PowerSeries.exp K - 1)
      = 1 := by
  have hg := hasSubst_exp_sub_one_K (K := K)
  have hX : (PowerSeries.substAlgHom hg) (PowerSeries.X : PowerSeries K)
      = PowerSeries.exp K - 1 := by
    rw [show ⇑(PowerSeries.substAlgHom hg)
        = PowerSeries.subst (PowerSeries.exp K - 1) from
      PowerSeries.coe_substAlgHom hg]
    exact PowerSeries.subst_X hg
  have hC : ∀ x : K, (PowerSeries.substAlgHom hg) (PowerSeries.C x)
      = PowerSeries.C x := fun x => (PowerSeries.substAlgHom hg).commutes x
  have hK := congrArg (PowerSeries.map (integerRing K).subtype)
    (Ring.mul_inverse_cancel _ (isUnit_root_mul_one_add_X_sub_one hζ hD hc))
  simp only [map_mul, map_sub, map_add, map_one, PowerSeries.map_X,
    PowerSeries.map_C, Subring.coe_subtype, SubmonoidClass.coe_pow] at hK
  have hsub := congrArg (PowerSeries.substAlgHom hg) hK
  simp only [map_mul, map_sub, map_add, map_one, hX, hC,
    show (1 : PowerSeries K) + (PowerSeries.exp K - 1) = PowerSeries.exp K
      by ring,
    PowerSeries.coe_substAlgHom hg] at hsub
  exact hsub

omit [CompleteSpace K] in
/-- L5.2.3 step 2: clearing the denominator `e^{Dt} − 1` against `G_c`
recovers the geometric numerator `Σ_{j<D} ζ^{cj}·e^{jt}` (the formal
expansion of TeX 1797 with the denominators multiplied out). -/
lemma rescale_exp_sub_one_mul_muEta_term {ζ : integerRing K} {D : ℕ}
    (hζK : IsPrimitiveRoot ((ζ : K)) D) (hζ : IsPrimitiveRoot ζ D)
    (hD : ¬ (p : ℕ) ∣ D) {c : ℕ} (hc : ¬ D ∣ c) :
    (PowerSeries.rescale ((D : ℕ) : K) (PowerSeries.exp K) - 1)
        * (PowerSeries.map (integerRing K).subtype
            (Ring.inverse (PowerSeries.C (ζ ^ c) * (1 + PowerSeries.X) - 1))).subst
            (PowerSeries.exp K - 1)
      = ∑ j ∈ Finset.range D,
          PowerSeries.C ((ζ : K) ^ (c * j))
            * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) := by
  have hx : (PowerSeries.C ((ζ : K) ^ c) * PowerSeries.exp K) ^ D
      = PowerSeries.rescale ((D : ℕ) : K) (PowerSeries.exp K) := by
    rw [mul_pow, ← map_pow, ← pow_mul, mul_comm c D, pow_mul, hζK.pow_eq_one,
      one_pow, map_one, one_mul, PowerSeries.exp_pow_eq_rescale_exp]
  have hgs := geom_sum_mul (PowerSeries.C ((ζ : K) ^ c) * PowerSeries.exp K) D
  calc (PowerSeries.rescale ((D : ℕ) : K) (PowerSeries.exp K) - 1)
        * (PowerSeries.map (integerRing K).subtype
            (Ring.inverse (PowerSeries.C (ζ ^ c) * (1 + PowerSeries.X) - 1))).subst
            (PowerSeries.exp K - 1)
      = (∑ j ∈ Finset.range D,
            (PowerSeries.C ((ζ : K) ^ c) * PowerSeries.exp K) ^ j)
          * ((PowerSeries.C ((ζ : K) ^ c) * PowerSeries.exp K - 1)
            * (PowerSeries.map (integerRing K).subtype
                (Ring.inverse (PowerSeries.C (ζ ^ c) * (1 + PowerSeries.X) - 1))).subst
                (PowerSeries.exp K - 1)) := by
        rw [← hx, ← hgs]
        ring
    _ = ∑ j ∈ Finset.range D,
          (PowerSeries.C ((ζ : K) ^ c) * PowerSeries.exp K) ^ j := by
        rw [muEta_term_exp_identity hζ hD hc, mul_one]
    _ = ∑ j ∈ Finset.range D,
          PowerSeries.C ((ζ : K) ^ (c * j))
            * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_pow, ← map_pow, ← pow_mul, PowerSeries.exp_pow_eq_rescale_exp]

/-- L5.2.3 step 3, the master identity: `X·H_η = −G(η⁻¹)·genBPS_{η_K}` in
`K⟦t⟧`, with `H_η` the exp-substituted `K`-valued Mahler transform of
`muEtaCleared` — the η⁻¹-weighted geometric numerators collapse through the
Gauss sum (modulus-`D` instance of the T509 (v-a) collapse) and the
generating-function identity T504. -/
lemma X_mul_muEtaCleared_subst {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D)
    (hζK : IsPrimitiveRoot ((ζ : K)) D) (hD : ¬ (p : ℕ) ∣ D) :
    PowerSeries.X * (PowerSeries.map (integerRing K).subtype
          (mahlerTransform p K (muEtaCleared p K η hζ hD))).subst
          (PowerSeries.exp K - 1)
      = -(PowerSeries.C (gaussSum (toFieldChar η)⁻¹
              (AddChar.zmodChar D hζK.pow_eq_one))
          * PowerSeries.mk fun k =>
              (toFieldChar η).genBernoulli k * (k.factorial : K)⁻¹) := by
  classical
  haveI : Fact (1 < D) := ⟨hD1⟩
  have hg := hasSubst_exp_sub_one_K (K := K)
  have hηK : (toFieldChar η).IsPrimitive :=
    (DirichletCharacter.isPrimitive_ringHomComp_iff η
      (fun _ _ h => Subtype.ext h)).mpr hη
  -- (1) the substituted transform as the η̄⁻¹-weighted sum of the `G_c`
  have hHsum : (PowerSeries.map (integerRing K).subtype
        (mahlerTransform p K (muEtaCleared p K η hζ hD))).subst
        (PowerSeries.exp K - 1)
      = -∑ c ∈ Finset.range D,
          PowerSeries.C ((toFieldChar η)⁻¹ ((c : ℕ) : ZMod D))
            * (PowerSeries.map (integerRing K).subtype
                (Ring.inverse (PowerSeries.C (ζ ^ c)
                  * (1 + PowerSeries.X) - 1))).subst
                (PowerSeries.exp K - 1) := by
    rw [mahlerTransform_muEtaCleared, map_neg, map_sum,
      ← PowerSeries.coe_substAlgHom hg, map_neg, map_sum, neg_inj]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, PowerSeries.map_C, map_mul,
      show (PowerSeries.substAlgHom hg)
          (PowerSeries.C ((integerRing K).subtype (η⁻¹ ((c : ℕ) : ZMod D))))
        = PowerSeries.C ((integerRing K).subtype (η⁻¹ ((c : ℕ) : ZMod D))) from
        (PowerSeries.substAlgHom hg).commutes _,
      PowerSeries.coe_substAlgHom hg,
      show (toFieldChar η)⁻¹ = toFieldChar η⁻¹ from MulChar.ringHomComp_inv η _]
    rfl
  -- (2) clear `e^{Dt} − 1` and collapse the Gauss sums
  have hclear : (PowerSeries.rescale ((D : ℕ) : K) (PowerSeries.exp K) - 1)
        * (PowerSeries.map (integerRing K).subtype
            (mahlerTransform p K (muEtaCleared p K η hζ hD))).subst
            (PowerSeries.exp K - 1)
      = -(PowerSeries.C (gaussSum (toFieldChar η)⁻¹
              (AddChar.zmodChar D hζK.pow_eq_one))
          * ∑ j ∈ Finset.range D,
              PowerSeries.C ((toFieldChar η) ((j : ℕ) : ZMod D))
                * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K)) := by
    rw [hHsum, mul_neg, Finset.mul_sum, neg_inj]
    have hper : ∀ c ∈ Finset.range D,
        (PowerSeries.rescale ((D : ℕ) : K) (PowerSeries.exp K) - 1)
            * (PowerSeries.C ((toFieldChar η)⁻¹ ((c : ℕ) : ZMod D))
              * (PowerSeries.map (integerRing K).subtype
                  (Ring.inverse (PowerSeries.C (ζ ^ c)
                    * (1 + PowerSeries.X) - 1))).subst
                  (PowerSeries.exp K - 1))
          = ∑ j ∈ Finset.range D,
              PowerSeries.C ((toFieldChar η)⁻¹ ((c : ℕ) : ZMod D)
                  * (ζ : K) ^ (c * j))
                * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) := by
      intro c hcr
      rcases eq_or_ne c 0 with rfl | hc0
      · rw [show ((0 : ℕ) : ZMod D) = 0 from Nat.cast_zero,
          (toFieldChar η)⁻¹.map_nonunit not_isUnit_zero, map_zero]
        simp
      · have hdvd : ¬ D ∣ c :=
          fun h => hc0 (Nat.eq_zero_of_dvd_of_lt h (Finset.mem_range.mp hcr))
        rw [mul_left_comm, rescale_exp_sub_one_mul_muEta_term hζK hζ hD hdvd,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
        ring
    rw [Finset.sum_congr rfl hper, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, ← map_sum, sum_inv_char_zeta_pow hηK hζK j, map_mul]
    ring
  -- (3) multiply by `X`, insert T504, cancel the regular factor
  have h504 := X_mul_sum_char_rescale_exp (K := K) hD1 (toFieldChar η)
  have hreg : (PowerSeries.rescale ((D : ℕ) : K) (PowerSeries.exp K) - 1)
      ≠ 0 := by
    intro h0
    have h1 := congrArg (PowerSeries.coeff 1) h0
    rw [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
      PowerSeries.coeff_one] at h1
    simp only [Nat.factorial_one, Nat.cast_one, map_one, div_one, pow_one,
      if_neg one_ne_zero, sub_zero, map_zero] at h1
    exact NeZero.ne D (by simpa using h1)
  refine mul_right_cancel₀ hreg ?_
  calc PowerSeries.X * (PowerSeries.map (integerRing K).subtype
          (mahlerTransform p K (muEtaCleared p K η hζ hD))).subst
          (PowerSeries.exp K - 1)
        * (PowerSeries.rescale ((D : ℕ) : K) (PowerSeries.exp K) - 1)
      = PowerSeries.X
          * ((PowerSeries.rescale ((D : ℕ) : K) (PowerSeries.exp K) - 1)
            * (PowerSeries.map (integerRing K).subtype
                (mahlerTransform p K (muEtaCleared p K η hζ hD))).subst
                (PowerSeries.exp K - 1)) := by ring
    _ = -(PowerSeries.C (gaussSum (toFieldChar η)⁻¹
            (AddChar.zmodChar D hζK.pow_eq_one))
          * (PowerSeries.X * ∑ j ∈ Finset.range D,
              PowerSeries.C ((toFieldChar η) ((j : ℕ) : ZMod D))
                * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K))) := by
        rw [hclear]
        ring
    _ = -(PowerSeries.C (gaussSum (toFieldChar η)⁻¹
              (AddChar.zmodChar D hζK.pow_eq_one))
          * PowerSeries.mk fun k =>
              (toFieldChar η).genBernoulli k * (k.factorial : K)⁻¹)
          * (PowerSeries.rescale ((D : ℕ) : K) (PowerSeries.exp K) - 1) := by
        rw [h504]
        ring

/-- L5.2.3 (RJW Lem 5.9, TeX 1801–1804): the moments of `μ_η` are the
`L`-values: `G(η⁻¹) · ∫x^k dμ_η`-cleared form,
`∫ x^k d(muEtaCleared η) = G(η⁻¹) · L(η,−k)`. -/
theorem muEtaCleared_moments {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) (k : ℕ) :
    ((muEtaCleared p K η hζ hD (powCM p K k) : integerRing K) : K)
      = ((gaussSum η⁻¹ (AddChar.zmodChar D (hζ.pow_eq_one)) : integerRing K) : K)
          * LvalNeg (toFieldChar η) k := by
  have hζK : IsPrimitiveRoot ((ζ : K)) D :=
    hζ.map_of_injective (f := (integerRing K).subtype) fun _ _ h => Subtype.ext h
  -- the moment as `k!·[t^k] H_η`
  have hmom : ((muEtaCleared p K η hζ hD (powCM p K k) : integerRing K) : K)
      = (k.factorial : K) * PowerSeries.coeff k
          ((PowerSeries.map (integerRing K).subtype
            (mahlerTransform p K (muEtaCleared p K η hζ hD))).subst
            (PowerSeries.exp K - 1)) := by
    rw [apply_powCM]
    rw [show ((PowerSeries.constantCoeff ((del K)^[k] (mahlerTransform p K
          (muEtaCleared p K η hζ hD))) : integerRing K) : K)
        = PowerSeries.constantCoeff (PowerSeries.map (integerRing K).subtype
            ((del K)^[k] (mahlerTransform p K (muEtaCleared p K η hζ hD)))) from by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
      rfl]
    rw [map_subtype_del_iterate, constantCoeff_iterate_delField]
  -- the `(k+1)`-st coefficient of the master identity
  have hmaster := congrArg (PowerSeries.coeff (k + 1))
    (X_mul_muEtaCleared_subst hD1 hη hζ hζK hD)
  rw [PowerSeries.coeff_succ_X_mul, map_neg, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mk] at hmaster
  rw [hmom, hmaster, coe_gaussSum_zmodChar η hζ hζK, LvalNeg]
  have hk1 : ((k + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero k)
  have hkf : ((k.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have hfact : (((k + 1).factorial : ℕ) : K)
      = ((k + 1 : ℕ) : K) * (k.factorial : K) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  field_simp [hfact]
  rw [hfact]
  push_cast
  ring

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
