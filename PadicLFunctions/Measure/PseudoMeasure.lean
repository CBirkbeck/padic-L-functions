import PadicLFunctions.Measure.UnitsZp
import PadicLFunctions.Measure.Fubini
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# The convolution algebra Λ(ℤ_p^×) and pseudo-measures

RJW (arXiv:2309.15692) §3.6 (`sec:pseudo-measures`). The group `ℤ_p^×` is multiplicative,
so the convolution product on `ℳ(ℤ_p^×, ℤ_p)` uses the *multiplicative* structure
(RJW Rem. 3.33, Eq. (3.11) `eq:convolution`):

  `∫ f d(μ ⋆ λ) = ∫ (∫ f(xy) dμ(x)) dλ(y)`.

Pseudo-measures (RJW Def. 3.34) live in the total fraction ring `Q(ℤ_p^×)` of
`Λ(ℤ_p^×)`. The key results are the zero-divisor lemma (RJW Lem. 3.36,
`lem:zero divisor`) and the description of the augmentation ideal as the principal
ideal `([a]−[1])` for a topological generator `a` (RJW Def. 3.37 + Lem. 3.38,
`lem:pseudo-measure existence`), whose source proof goes through the finite levels
`𝒪_L[(ℤ/p^n)^×]` and passes to the inverse limit; the finite levels are implemented
by `PadicMeasure.levelMap` below.

Throughout this file `p` is odd where stated (the source's standing assumption from §4
onwards; `(ℤ/p^n)^×` cyclic requires it).
-/

open scoped fwdDiff
open PowerSeries

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

namespace PadicMeasure

/-- Multiplication on `ℤ_[p]ˣ` as a single continuous map. -/
def unitsMulCM₂ : C(ℤ_[p]ˣ × ℤ_[p]ˣ, ℤ_[p]ˣ) := ⟨fun q => q.1 * q.2, continuous_mul⟩

/-- Convolution of measures on the multiplicative group `ℤ_p^×`:
`∫ f d(μ ⋆ ν) = ∫ (∫ f(xy) dν(y)) dμ(x)`.

Source: RJW Eq. (3.11) (`eq:convolution`, TeX lines 1173–1175). -/
noncomputable def unitsConv (μ ν : PadicMeasure p ℤ_[p]ˣ) : PadicMeasure p ℤ_[p]ˣ where
  toFun f := μ (innerInt p ν (f.comp (unitsMulCM₂ p)))
  map_add' f g := by rw [ContinuousMap.add_comp, innerInt_add, map_add]
  map_smul' c f := by rw [ContinuousMap.smul_comp, innerInt_smul, map_smul, RingHom.id_apply]

noncomputable instance : Mul (PadicMeasure p ℤ_[p]ˣ) := ⟨unitsConv p⟩

noncomputable instance : One (PadicMeasure p ℤ_[p]ˣ) := ⟨dirac p 1⟩

lemma units_mul_def (μ ν : PadicMeasure p ℤ_[p]ˣ) : μ * ν = unitsConv p μ ν := rfl

@[simp]
lemma units_mul_apply (μ ν : PadicMeasure p ℤ_[p]ˣ) (f : C(ℤ_[p]ˣ, ℤ_[p])) :
    (μ * ν) f = μ (innerInt p ν (f.comp (unitsMulCM₂ p))) := rfl

lemma units_one_def : (1 : PadicMeasure p ℤ_[p]ˣ) = dirac p 1 := rfl

/-- The Iwasawa algebra `Λ(ℤ_p^×) = ℳ(ℤ_p^×, ℤ_p)` as a commutative ring under
convolution. Commutativity is the Fubini swap (`integral_swap`); associativity is the
triple-integral computation.

Source: RJW Rem. 3.11 ("One checks that this does give an algebra structure") +
Rem. 3.33. -/
noncomputable instance : CommRing (PadicMeasure p ℤ_[p]ˣ) where
  mul_assoc a b c := by
    refine LinearMap.ext fun f => ?_
    show a (innerInt p b ((innerInt p c (f.comp (unitsMulCM₂ p))).comp (unitsMulCM₂ p)))
      = a (innerInt p (unitsConv p b c) (f.comp (unitsMulCM₂ p)))
    congr 1
    ext x
    show b _ = b _
    congr 1
    ext y
    show c _ = c _
    congr 1
    ext z
    show f (x * y * z) = f (x * (y * z))
    rw [mul_assoc]
  one_mul a := by
    refine LinearMap.ext fun f => ?_
    show a ((f.comp (unitsMulCM₂ p)).curry 1) = a f
    congr 1
    ext y
    show f (1 * y) = f y
    rw [one_mul]
  mul_one a := by
    refine LinearMap.ext fun f => ?_
    show a (innerInt p (dirac p 1) (f.comp (unitsMulCM₂ p))) = a f
    congr 1
    ext x
    show f (x * 1) = f x
    rw [mul_one]
  left_distrib a b c := by
    refine LinearMap.ext fun f => ?_
    show a (innerInt p (b + c) (f.comp (unitsMulCM₂ p))) = _
    rw [innerInt_measure_add, map_add]
    rfl
  right_distrib a b c := by
    refine LinearMap.ext fun f => ?_
    show (a + b) (innerInt p c (f.comp (unitsMulCM₂ p))) = _
    rw [LinearMap.add_apply]
    rfl
  zero_mul a := LinearMap.ext fun f => rfl
  mul_zero a := by
    refine LinearMap.ext fun f => ?_
    show a (innerInt p (0 : PadicMeasure p ℤ_[p]ˣ) (f.comp (unitsMulCM₂ p))) = 0
    rw [innerInt_measure_zero, map_zero]
  mul_comm a b := by
    refine LinearMap.ext fun f => ?_
    show a (innerInt p b (f.comp (unitsMulCM₂ p))) = b (innerInt p a (f.comp (unitsMulCM₂ p)))
    rw [integral_swap]
    congr 1
    ext y
    show a _ = a _
    congr 1
    ext x
    show f (x * y) = f (y * x)
    rw [mul_comm]

@[simp]
theorem units_dirac_mul_dirac (u v : ℤ_[p]ˣ) :
    (dirac p u : PadicMeasure p ℤ_[p]ˣ) * dirac p v = dirac p (u * v) :=
  LinearMap.ext fun f => rfl

section degree

/-- The degree (augmentation) map `Λ(ℤ_p^×) → ℤ_p`, `μ ↦ ∫_{ℤ_p^×} 1 dμ`.

Source: RJW Def. 3.37 (`DefAugmentationIdealFiniteLevel`, TeX lines 1245–1253); the
inverse-limit degree map is evaluation at the constant function `1`. -/
noncomputable def deg : PadicMeasure p ℤ_[p]ˣ →+* ℤ_[p] where
  toFun μ := μ 1
  map_one' := by
    show (1 : C(ℤ_[p]ˣ, ℤ_[p])) 1 = 1
    rfl
  map_mul' μ ν := by
    show μ (innerInt p ν ((1 : C(ℤ_[p]ˣ, ℤ_[p])).comp (unitsMulCM₂ p))) = μ 1 * ν 1
    have h1 : innerInt p ν ((1 : C(ℤ_[p]ˣ, ℤ_[p])).comp (unitsMulCM₂ p))
        = ν 1 • (1 : C(ℤ_[p]ˣ, ℤ_[p])) := by
      ext x
      show ν _ = _
      have hc : ((1 : C(ℤ_[p]ˣ, ℤ_[p])).comp (unitsMulCM₂ p)).curry x
          = (1 : C(ℤ_[p]ˣ, ℤ_[p])) := ContinuousMap.ext fun y => rfl
      rw [hc]
      simp [smul_eq_mul]
    rw [h1, map_smul, smul_eq_mul, mul_comm]
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The augmentation ideal `I(ℤ_p^×) = ker(deg)`. Source: RJW Def. 3.37. -/
noncomputable def augmentationIdeal : Ideal (PadicMeasure p ℤ_[p]ˣ) :=
  RingHom.ker (deg p)

end degree

section finiteLevel

/-- Reduction `ℤ_p^× → (ℤ/p^n)^×` (units functor applied to `PadicInt.toZModPow`). -/
noncomputable def unitsToZModPow (n : ℕ) : ℤ_[p]ˣ →* (ZMod (p ^ n))ˣ :=
  Units.map (PadicInt.toZModPow n).toMonoidHom

@[simp]
lemma unitsToZModPow_coe (n : ℕ) (u : ℤ_[p]ˣ) :
    ((unitsToZModPow p n u : (ZMod (p ^ n))ˣ) : ZMod (p ^ n))
      = PadicInt.toZModPow n (u : ℤ_[p]) := rfl

/-- Residue discs mod `p^n` are clopen in `ℤ_p` (open and with open complement). -/
lemma isClopen_toZModPow_fiber (n : ℕ) (a : ZMod (p ^ n)) :
    IsClopen {z : ℤ_[p] | PadicInt.toZModPow n z = a} := by
  classical
  refine ⟨?_, isOpen_toZModPow_fiber p n a⟩
  rw [← isOpen_compl_iff]
  have hcompl : {z : ℤ_[p] | PadicInt.toZModPow n z = a}ᶜ
      = ⋃ b ∈ Finset.univ.erase a, {z : ℤ_[p] | PadicInt.toZModPow n z = b} := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_erase,
      Finset.mem_univ, and_true, exists_prop]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨b, hb, hzb⟩ => hzb ▸ hb⟩
  rw [hcompl]
  exact isOpen_biUnion fun b _ => isOpen_toZModPow_fiber p n b

/-- The fibre of `unitsToZModPow n` over a residue `g` is clopen in `ℤ_p^×`. -/
lemma isClopen_unitsToZModPow_fiber (n : ℕ) (g : (ZMod (p ^ n))ˣ) :
    IsClopen (unitsToZModPow p n ⁻¹' {g}) := by
  have hset : unitsToZModPow p n ⁻¹' {g}
      = (Units.val) ⁻¹' {z : ℤ_[p] | PadicInt.toZModPow n z = (g : ZMod (p ^ n))} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact ⟨fun h => by rw [← h]; rfl, fun h => Units.ext h⟩
  rw [hset]
  exact (isClopen_toZModPow_fiber p n _).preimage Units.continuous_val

/-- The indicator of a level-`n` residue disc, as a continuous map on `ℤ_p^×`. -/
noncomputable def levelChar (n : ℕ) (g : (ZMod (p ^ n))ˣ) : C(ℤ_[p]ˣ, ℤ_[p]) :=
  (LocallyConstant.charFn ℤ_[p] (isClopen_unitsToZModPow_fiber p n g) : C(ℤ_[p]ˣ, ℤ_[p]))

lemma levelChar_apply_eq {n : ℕ} {g : (ZMod (p ^ n))ˣ} {u : ℤ_[p]ˣ}
    (h : unitsToZModPow p n u = g) : levelChar p n g u = 1 := by
  simp only [levelChar, LocallyConstant.coe_continuousMap, LocallyConstant.coe_charFn]
  rw [Set.indicator_of_mem (show u ∈ unitsToZModPow p n ⁻¹' {g} from h), Pi.one_apply]

lemma levelChar_apply_ne {n : ℕ} {g : (ZMod (p ^ n))ˣ} {u : ℤ_[p]ˣ}
    (h : unitsToZModPow p n u ≠ g) : levelChar p n g u = 0 := by
  simp only [levelChar, LocallyConstant.coe_continuousMap, LocallyConstant.coe_charFn]
  rw [Set.indicator_of_notMem (show u ∉ unitsToZModPow p n ⁻¹' {g} from h)]

/-- The finite-level map `Λ(ℤ_p^×) → ℤ_p[(ℤ/p^n)^×]` sending a measure to
`∑_{g} μ(𝟙_{g\text{-fibre}}) · [g]`. These are the maps whose inverse limit is the
Iwasawa algebra; we use them (rather than the full limit) for RJW Lem. 3.38.

Source: RJW TeX lines 888–892 (the map `μ ↦ λ_H = ∑ μ(aH)[a]`). -/
noncomputable def levelMap (n : ℕ) :
    PadicMeasure p ℤ_[p]ˣ →+* MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ where
  toFun μ := ∑ g : (ZMod (p ^ n))ˣ, MonoidAlgebra.single g (μ (levelChar p n g))
  map_one' := by
    classical
    rw [MonoidAlgebra.one_def, Finset.sum_eq_single (1 : (ZMod (p ^ n))ˣ)]
    · rw [show ((1 : PadicMeasure p ℤ_[p]ˣ)) (levelChar p n 1) = 1 from by
        rw [units_one_def, dirac_apply, levelChar_apply_eq p (map_one (unitsToZModPow p n))]]
    · intro g _ hg
      rw [show ((1 : PadicMeasure p ℤ_[p]ˣ)) (levelChar p n g) = 0 from by
          rw [units_one_def, dirac_apply,
            levelChar_apply_ne p (by rw [map_one]; exact fun h => hg h.symm)],
        MonoidAlgebra.single_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  map_mul' μ ν := by
    classical
    -- the inner integral of a level indicator is again a level indicator
    have hcurry : ∀ (c : (ZMod (p ^ n))ˣ) (x : ℤ_[p]ˣ),
        ((levelChar p n c).comp (unitsMulCM₂ p)).curry x
          = levelChar p n ((unitsToZModPow p n x)⁻¹ * c) := by
      intro c x
      ext y
      show levelChar p n c (x * y) = _
      by_cases hy : unitsToZModPow p n y = (unitsToZModPow p n x)⁻¹ * c
      · rw [levelChar_apply_eq p (by rw [map_mul, hy, mul_inv_cancel_left]),
          levelChar_apply_eq p hy]
      · rw [levelChar_apply_ne p (fun hxy => hy ?_), levelChar_apply_ne p hy]
        rw [map_mul] at hxy
        rw [← hxy, inv_mul_cancel_left]
    -- hence the convolution against a level indicator is a finite sum
    have hconv : ∀ c : (ZMod (p ^ n))ˣ,
        (μ * ν) (levelChar p n c)
          = ∑ a : (ZMod (p ^ n))ˣ, μ (levelChar p n a) * ν (levelChar p n (a⁻¹ * c)) := by
      intro c
      rw [units_mul_apply]
      have hfn : innerInt p ν ((levelChar p n c).comp (unitsMulCM₂ p))
          = ∑ a : (ZMod (p ^ n))ˣ,
              ν (levelChar p n (a⁻¹ * c)) • levelChar p n a := by
        ext x
        rw [innerInt_apply, hcurry c x]
        rw [show (∑ a : (ZMod (p ^ n))ˣ,
            ν (levelChar p n (a⁻¹ * c)) • levelChar p n a) x
            = ∑ a : (ZMod (p ^ n))ˣ,
              ν (levelChar p n (a⁻¹ * c)) * levelChar p n a x from by
          simp [Finset.sum_apply]]
        rw [Finset.sum_eq_single (unitsToZModPow p n x)]
        · rw [levelChar_apply_eq p rfl, mul_one]
        · intro a _ ha
          rw [levelChar_apply_ne p (fun h => ha h.symm), mul_zero]
        · exact fun h => absurd (Finset.mem_univ _) h
      rw [hfn, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    -- expand the product of the two finite sums and reindex
    rw [show (∑ g : (ZMod (p ^ n))ˣ, MonoidAlgebra.single g (μ (levelChar p n g))) *
        (∑ h : (ZMod (p ^ n))ˣ, MonoidAlgebra.single h (ν (levelChar p n h)))
        = ∑ g : (ZMod (p ^ n))ˣ, ∑ h : (ZMod (p ^ n))ˣ,
            MonoidAlgebra.single (g * h) (μ (levelChar p n g) * ν (levelChar p n h)) from by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ =>
        MonoidAlgebra.single_mul_single g h _ _]
    calc ∑ c : (ZMod (p ^ n))ˣ, MonoidAlgebra.single c ((μ * ν) (levelChar p n c))
        = ∑ c : (ZMod (p ^ n))ˣ, ∑ a : (ZMod (p ^ n))ˣ,
            MonoidAlgebra.single c
              (μ (levelChar p n a) * ν (levelChar p n (a⁻¹ * c))) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [hconv c]
          exact map_sum (Finsupp.singleAddHom c) _ _
      _ = ∑ a : (ZMod (p ^ n))ˣ, ∑ c : (ZMod (p ^ n))ˣ,
            MonoidAlgebra.single c
              (μ (levelChar p n a) * ν (levelChar p n (a⁻¹ * c))) := Finset.sum_comm
      _ = ∑ g : (ZMod (p ^ n))ˣ, ∑ h : (ZMod (p ^ n))ˣ,
            MonoidAlgebra.single (g * h)
              (μ (levelChar p n g) * ν (levelChar p n h)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          refine (Fintype.sum_equiv (Equiv.mulLeft g)
            (fun h => MonoidAlgebra.single (g * h)
              (μ (levelChar p n g) * ν (levelChar p n h)))
            (fun c => MonoidAlgebra.single c
              (μ (levelChar p n g) * ν (levelChar p n (g⁻¹ * c)))) (fun h => ?_)).symm
          rw [show (Equiv.mulLeft g) h = g * h from rfl, inv_mul_cancel_left]
  map_zero' := by
    classical
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [LinearMap.zero_apply, MonoidAlgebra.single_zero]
  map_add' μ ν := by
    classical
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun g _ => by
      rw [LinearMap.add_apply, MonoidAlgebra.single_add]

/-- The finite-level maps are jointly injective: a measure vanishing on every
finite-level indicator is zero (locally constant functions on `ℤ_p^×` factor through
some level). Source: RJW Rem. 3.8 + Prop. 3.10 (inverse-limit description). -/
theorem levelMap_jointly_injective (μ : PadicMeasure p ℤ_[p]ˣ)
    (h : ∀ n, levelMap p n μ = 0) : μ = 0 := by
  sorry

end finiteLevel

section zeroDivisor

/-- The function `x ↦ x^k` on `ℤ_p^×`, as a continuous map to `ℤ_p`. -/
def unitsPowCM (k : ℕ) : C(ℤ_[p]ˣ, ℤ_[p]) :=
  ⟨fun u => (u : ℤ_[p]) ^ k, (Units.continuous_val.pow k)⟩

/-- **RJW Lem. 3.36(i) (`lem:zero divisor`)**: a measure on `ℤ_p^×` with
`∫ x^k dμ = 0` for all `k > 0` is zero. Source proof (TeX lines 1228–1229): the Mahler
transform of `ιμ` is constant (binomial polynomials with `n ≥ 1` have no constant
term), and `ψ` fixes constants while killing `ιμ`; hence `𝓐_{ιμ} = 0`. -/
theorem eq_zero_of_forall_unitsPowCM_eq_zero (μ : PadicMeasure p ℤ_[p]ˣ)
    (h : ∀ k, 0 < k → μ (unitsPowCM p k) = 0) : μ = 0 := by
  -- Step 1: the positive Mahler coefficients of `ι μ` vanish
  have hcoeff : ∀ n : ℕ, 0 < n → (iota p μ) (mahler n) = 0 := by
    intro n hn
    obtain ⟨q, hq⟩ : (Polynomial.X : Polynomial ℤ_[p]) ∣ descPochhammer ℤ_[p] n := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero, descPochhammer_eval_zero]
      simp [hn.ne']
    have hbridge : ∀ x : ℤ_[p],
        (descPochhammer ℤ_[p] n).eval x = (descPochhammer ℤ n).smeval x := by
      intro x
      rw [← descPochhammer_map (Int.castRingHom ℤ_[p]) n, Polynomial.eval_map,
        Polynomial.eval₂_eq_sum, Polynomial.smeval_eq_sum, Polynomial.sum_def,
        Polynomial.sum_def]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.smul_pow, zsmul_eq_mul]
      rfl
    have hfun : (n.factorial • mahler n : C(ℤ_[p], ℤ_[p]))
        = ⟨fun x => (descPochhammer ℤ_[p] n).eval x, (descPochhammer ℤ_[p] n).continuous⟩ := by
      ext x
      show n.factorial • mahler n x = (descPochhammer ℤ_[p] n).eval x
      rw [mahler_apply, hbridge x, Ring.descPochhammer_eq_factorial_smul_choose]
    have hint : (iota p μ) (n.factorial • mahler n) = 0 := by
      rw [hfun]
      show μ ((⟨fun x => (descPochhammer ℤ_[p] n).eval x,
        (descPochhammer ℤ_[p] n).continuous⟩ : C(ℤ_[p], ℤ_[p])).comp (unitsValCM p)) = 0
      have hcomp : ((⟨fun x => (descPochhammer ℤ_[p] n).eval x,
            (descPochhammer ℤ_[p] n).continuous⟩ : C(ℤ_[p], ℤ_[p])).comp (unitsValCM p))
          = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • unitsPowCM p (i + 1) := by
        ext u
        simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, unitsValCM,
          ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply,
          smul_eq_mul, unitsPowCM]
        rw [hq, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_eq_sum_range,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hcomp, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, h (i + 1) (Nat.succ_pos i), smul_zero]
    rw [map_nsmul] at hint
    refine nsmul_right_injective (M := ℤ_[p]) (Nat.factorial_ne_zero n) ?_
    show n.factorial • ((iota p μ) (mahler n)) = n.factorial • (0 : ℤ_[p])
    rw [hint, smul_zero]
  -- Step 2: `𝓐(ιμ)` is constant, so `ιμ` is a multiple of `δ₀`
  set c₀ := (iota p μ) (mahler 0) with hc₀
  have hμδ : iota p μ = c₀ • dirac p 0 := by
    apply mahlerTransform_injective p
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [coeff_mahlerTransform, coeff_mahlerTransform, LinearMap.smul_apply, dirac_apply,
        mahler_apply, Ring.choose_zero_right, smul_eq_mul, mul_one, hc₀]
    · rw [coeff_mahlerTransform, coeff_mahlerTransform, hcoeff n hn, LinearMap.smul_apply,
        dirac_apply, mahler_apply,
        show (0 : ℤ_[p]) = ((0 : ℕ) : ℤ_[p]) from by norm_num, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt hn, Nat.cast_zero, smul_zero]
  -- Step 3: `ψ` kills `ιμ` but fixes multiples of `δ₀`
  have hψ : psi p (iota p μ) = 0 := by
    rw [← isSupportedOn_units_iff_psi_eq_zero]
    exact res_iota p μ
  have hψδ : psi p ((c₀ • dirac p 0 : PadicMeasure p ℤ_[p])) = c₀ • dirac p 0 := by
    have hsd : shiftDiv p 0 = 0 := by
      have hdig : digit p (0 : ℤ_[p]) = 0 := by
        rw [digit, map_zero, ZMod.val_zero, Nat.cast_zero]
      refine Subtype.ext ?_
      show (((0 : ℤ_[p]) : ℚ_[p]) - (digit p (0 : ℤ_[p]) : ℚ_[p])) / (p : ℚ_[p])
          = ((0 : ℤ_[p]) : ℚ_[p])
      rw [hdig]
      simp
    refine LinearMap.ext fun f => ?_
    show (c₀ • dirac p 0)
        ((LocallyConstant.charFn ℤ_[p] (isClopen_pZp p) : C(ℤ_[p], ℤ_[p])) *
          f.comp (shiftDiv p)) = (c₀ • dirac p 0) f
    rw [LinearMap.smul_apply, LinearMap.smul_apply, dirac_apply, dirac_apply]
    congr 1
    show (LocallyConstant.charFn ℤ_[p] (isClopen_pZp p) : C(ℤ_[p], ℤ_[p])) 0 *
        f (shiftDiv p 0) = f 0
    have h0mem : (0 : ℤ_[p]) ∈ {x : ℤ_[p] | ‖x‖ < 1} := by
      simp [Set.mem_setOf_eq]
    rw [hsd]
    simp only [LocallyConstant.coe_continuousMap, LocallyConstant.coe_charFn]
    rw [Set.indicator_of_mem h0mem, Pi.one_apply, one_mul]
  rw [hμδ, hψδ] at hψ
  have hc0 : c₀ = 0 := by
    have heval := LinearMap.congr_fun hψ (1 : C(ℤ_[p], ℤ_[p]))
    simpa using heval
  rw [hc0, zero_smul] at hμδ
  exact iota_injective p (hμδ.trans (map_zero (iota p)).symm)

/-- Power moments are multiplicative for the convolution product:
`∫(xy)^k = (∫x^k)(∫y^k)` (RJW TeX line 1233). -/
lemma units_mul_apply_unitsPowCM (μ ν : PadicMeasure p ℤ_[p]ˣ) (k : ℕ) :
    (μ * ν) (unitsPowCM p k) = μ (unitsPowCM p k) * ν (unitsPowCM p k) := by
  rw [units_mul_apply]
  have hfn : innerInt p ν ((unitsPowCM p k).comp (unitsMulCM₂ p))
      = ν (unitsPowCM p k) • unitsPowCM p k := by
    ext x
    rw [innerInt_apply]
    have hcurry : ((unitsPowCM p k).comp (unitsMulCM₂ p)).curry x
        = ((x : ℤ_[p]) ^ k) • unitsPowCM p k := by
      ext y
      show ((x * y : ℤ_[p]ˣ) : ℤ_[p]) ^ k = _
      simp only [Units.val_mul, mul_pow, ContinuousMap.smul_apply, unitsPowCM,
        ContinuousMap.coe_mk, smul_eq_mul]
    rw [hcurry, map_smul, smul_eq_mul]
    show ((x : ℤ_[p])) ^ k * ν (unitsPowCM p k)
        = (ν (unitsPowCM p k) • unitsPowCM p k) x
    simp only [ContinuousMap.smul_apply, unitsPowCM, ContinuousMap.coe_mk, smul_eq_mul]
    rw [mul_comm]
  rw [hfn, map_smul, smul_eq_mul, mul_comm]

/-- **RJW Lem. 3.36(ii)**: a measure on `ℤ_p^×` with `∫ x^k dμ ≠ 0` for all `k > 0`
is not a zero divisor. Source proof (TeX lines 1232–1234): `∫ (xy)^k d(μ⋆λ) =
(∫ x^k dμ)(∫ y^k dλ)`, then apply (i). -/
theorem mem_nonZeroDivisors_of_forall_unitsPowCM_ne_zero (μ : PadicMeasure p ℤ_[p]ˣ)
    (h : ∀ k, 0 < k → μ (unitsPowCM p k) ≠ 0) :
    μ ∈ nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ) := by
  rw [mem_nonZeroDivisors_iff]
  have key : ∀ ν, ν * μ = 0 → ν = 0 := by
    intro ν hν
    apply eq_zero_of_forall_unitsPowCM_eq_zero
    intro k hk
    have heval := LinearMap.congr_fun hν (unitsPowCM p k)
    rw [units_mul_apply_unitsPowCM, LinearMap.zero_apply] at heval
    exact (mul_eq_zero.1 heval).resolve_right (h k hk)
  exact ⟨fun ν hν => key ν (by rwa [mul_comm] at hν), key⟩

end zeroDivisor

section pseudoMeasure

/-- The total ring of fractions `Q(ℤ_p^×)` of the Iwasawa algebra `Λ(ℤ_p^×)`.
Source: RJW Def. 3.34 ("let `Q(G)` denote the ring of fractions"). -/
noncomputable abbrev QuotientField :=
  FractionRing (PadicMeasure p ℤ_[p]ˣ)

/-- A *pseudo-measure* on `ℤ_p^×`: an element `λ` of `Q(ℤ_p^×)` with
`([g]−[1])·λ ∈ Λ(ℤ_p^×)` for all `g`.

Source: RJW Def. 3.34 (TeX lines 1185–1191). -/
def IsPseudoMeasure (q : QuotientField p) : Prop :=
  ∀ g : ℤ_[p]ˣ, ∃ ν : PadicMeasure p ℤ_[p]ˣ,
    algebraMap _ (QuotientField p) (dirac p g - 1) * q = algebraMap _ _ ν

/-- Measures are pseudo-measures. -/
theorem isPseudoMeasure_algebraMap (μ : PadicMeasure p ℤ_[p]ˣ) :
    IsPseudoMeasure p (algebraMap _ _ μ) := fun g =>
  ⟨(dirac p g - 1) * μ, by rw [map_mul]⟩

/-- **RJW Lem. 3.36(iii)**: a pseudo-measure all of whose moments `∫ x^k` (`k > 0`)
vanish is zero. The moments of a pseudo-measure `q` are encoded via any `g` with
`g^k ≠ 1`: `∫x^k q := (g^k − 1)^{-1} ∫x^k (([g]−[1])q)`. Here we state it via the
witnessing measures directly. Source: TeX lines 1236–1240. -/
theorem pseudoMeasure_eq_zero_of_moments {a : ℤ_[p]ˣ}
    (ha : ∀ k, 0 < k → (a : ℤ_[p]) ^ k ≠ 1) (q : QuotientField p)
    (hq : IsPseudoMeasure p q)
    (h : ∀ (k : ℕ), 0 < k → ∀ ν : PadicMeasure p ℤ_[p]ˣ,
      algebraMap _ (QuotientField p) (dirac p a - 1) * q = algebraMap _ _ ν →
        ν (unitsPowCM p k) = 0) :
    q = 0 := by
  sorry

end pseudoMeasure

section augmentation

/-- For odd `p` there is a *topological generator* of `ℤ_p^×`: an `a` whose image
generates `(ℤ/p^n)^×` for every `n`. The hypothesis `p ≠ 2` is essential:
`(ZMod 8)ˣ` is not cyclic. Source: RJW Lem. 3.38 ("take `a` to be a primitive
root modulo `p` such that `a^{p−1} ≢ 1 mod p²`"; the proof opens "As p is odd");
uses mathlib's `isCyclic_units_of_prime_pow`. -/
theorem exists_topological_generator (hp2 : p ≠ 2) :
    ∃ a : ℤ_[p]ˣ, ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n a) = ⊤ := by
  sorry

/-- For a topological generator `a`, the augmentation ideal is principal, generated by
`[a] − [1]`: at each finite level the augmentation ideal of the (cyclic) group ring
`ℤ_p[(ℤ/p^n)^×]` is generated by `[ā]−[1]`; compatibility and a compactness argument
pass this to the limit. Source: RJW Lem. 3.38, proof (TeX lines 1264–1282). -/
theorem augmentationIdeal_eq_span {a : ℤ_[p]ˣ}
    (ha : ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n a) = ⊤) :
    augmentationIdeal p = Ideal.span {(dirac p a - 1 : PadicMeasure p ℤ_[p]ˣ)} := by
  sorry

/-- **RJW Lem. 3.38 (`lem:pseudo-measure existence`)**: for a topological generator `a`
and any measure `μ`, the quotient `μ/([a]−[1])` is a pseudo-measure. -/
theorem isPseudoMeasure_mk' {a : ℤ_[p]ˣ}
    (ha : ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n a) = ⊤)
    (hreg : (dirac p a - 1 : PadicMeasure p ℤ_[p]ˣ) ∈
      nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ))
    (μ : PadicMeasure p ℤ_[p]ˣ) :
    IsPseudoMeasure p
      (IsLocalization.mk' (QuotientField p) μ ⟨_, hreg⟩) := by
  sorry

/-- `[a]−[1]` is a non-zero-divisor for a topological generator `a` (its moments are
`a^k − 1 ≠ 0`). Source: RJW TeX line 1240 ("But `[a]−[1]` satisfies the condition of
part (ii)") together with the remark after Lem. 3.38. -/
theorem dirac_sub_one_mem_nonZeroDivisors {a : ℤ_[p]ˣ}
    (ha : ∀ k, 0 < k → (a : ℤ_[p]) ^ k ≠ 1) :
    (dirac p a - 1 : PadicMeasure p ℤ_[p]ˣ) ∈
      nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ) := by
  sorry

/-- Every pseudo-measure has the shape `μ/([a]−[1])`. Source: RJW TeX lines 1284–1285
("Note moreover that *all* pseudo-measures have this shape"). -/
theorem isPseudoMeasure_iff_exists {a : ℤ_[p]ˣ}
    (ha : ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n a) = ⊤)
    (hreg : (dirac p a - 1 : PadicMeasure p ℤ_[p]ˣ) ∈
      nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ))
    (q : QuotientField p) :
    IsPseudoMeasure p q ↔
      ∃ μ : PadicMeasure p ℤ_[p]ˣ, q = IsLocalization.mk' (QuotientField p) μ ⟨_, hreg⟩ := by
  sorry

end augmentation

end PadicMeasure
