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

/-- Left translation by `u` on `ℤ_[p]ˣ` as a continuous map (multiplicative). -/
def unitsMulCM (u : ℤ_[p]ˣ) : C(ℤ_[p]ˣ, ℤ_[p]ˣ) := ⟨fun v => u * v, by sorry⟩

/-- Convolution of measures on the multiplicative group `ℤ_p^×`:
`∫ f d(μ ⋆ ν) = ∫ (∫ f(xy) dν(y)) dμ(x)`.

Source: RJW Eq. (3.11) (`eq:convolution`, TeX lines 1173–1175). -/
noncomputable def unitsConv (μ ν : PadicMeasure p ℤ_[p]ˣ) : PadicMeasure p ℤ_[p]ˣ where
  toFun f := μ ⟨fun x => ν (f.comp (unitsMulCM p x)), by sorry⟩
  map_add' _ _ := by sorry
  map_smul' _ _ := by sorry

noncomputable instance : Mul (PadicMeasure p ℤ_[p]ˣ) := ⟨unitsConv p⟩

noncomputable instance : One (PadicMeasure p ℤ_[p]ˣ) := ⟨dirac p 1⟩

lemma units_mul_def (μ ν : PadicMeasure p ℤ_[p]ˣ) : μ * ν = unitsConv p μ ν := rfl

lemma units_one_def : (1 : PadicMeasure p ℤ_[p]ˣ) = dirac p 1 := rfl

/-- The Iwasawa algebra `Λ(ℤ_p^×) = ℳ(ℤ_p^×, ℤ_p)` as a commutative ring under
convolution. Commutativity and associativity follow from the Fubini-type swap for
functionals on `C(ℤ_p^× × ℤ_p^×, ℤ_p)`, proved on locally constant functions (which
decompose into clopen boxes) and extended by density.

Source: RJW Rem. 3.11 ("One checks that this does give an algebra structure") +
Rem. 3.33. -/
noncomputable instance : CommRing (PadicMeasure p ℤ_[p]ˣ) where
  mul_assoc _ _ _ := by sorry
  one_mul _ := by sorry
  mul_one _ := by sorry
  left_distrib _ _ _ := by sorry
  right_distrib _ _ _ := by sorry
  zero_mul _ := by sorry
  mul_zero _ := by sorry
  mul_comm _ _ := by sorry

@[simp]
theorem units_dirac_mul_dirac (u v : ℤ_[p]ˣ) :
    (dirac p u : PadicMeasure p ℤ_[p]ˣ) * dirac p v = dirac p (u * v) := by
  sorry

section degree

/-- The degree (augmentation) map `Λ(ℤ_p^×) → ℤ_p`, `μ ↦ ∫_{ℤ_p^×} 1 dμ`.

Source: RJW Def. 3.37 (`DefAugmentationIdealFiniteLevel`, TeX lines 1245–1253); the
inverse-limit degree map is evaluation at the constant function `1`. -/
noncomputable def deg : PadicMeasure p ℤ_[p]ˣ →+* ℤ_[p] where
  toFun μ := μ 1
  map_one' := by sorry
  map_mul' _ _ := by sorry
  map_zero' := by sorry
  map_add' _ _ := by sorry

/-- The augmentation ideal `I(ℤ_p^×) = ker(deg)`. Source: RJW Def. 3.37. -/
noncomputable def augmentationIdeal : Ideal (PadicMeasure p ℤ_[p]ˣ) :=
  RingHom.ker (deg p)

end degree

section finiteLevel

instance (n : ℕ) : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩

/-- Reduction `ℤ_p^× → (ℤ/p^n)^×` (units functor applied to `PadicInt.toZModPow`). -/
noncomputable def unitsToZModPow (n : ℕ) : ℤ_[p]ˣ →* (ZMod (p ^ n))ˣ :=
  Units.map (PadicInt.toZModPow n).toMonoidHom

/-- The fibre of `unitsToZModPow n` over a residue `g` is clopen in `ℤ_p^×`. -/
lemma isClopen_unitsToZModPow_fiber (n : ℕ) (g : (ZMod (p ^ n))ˣ) :
    IsClopen (unitsToZModPow p n ⁻¹' {g}) := by
  sorry

/-- The finite-level map `Λ(ℤ_p^×) → ℤ_p[(ℤ/p^n)^×]` sending a measure to
`∑_{g} μ(𝟙_{g\text{-fibre}}) · [g]`. These are the maps whose inverse limit is the
Iwasawa algebra; we use them (rather than the full limit) for RJW Lem. 3.38.

Source: RJW TeX lines 888–892 (the map `μ ↦ λ_H = ∑ μ(aH)[a]`). -/
noncomputable def levelMap (n : ℕ) :
    PadicMeasure p ℤ_[p]ˣ →+* MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ where
  toFun μ :=
    ∑ g : (ZMod (p ^ n))ˣ,
      MonoidAlgebra.single g
        (μ (LocallyConstant.charFn ℤ_[p] (isClopen_unitsToZModPow_fiber p n g) :
          C(ℤ_[p]ˣ, ℤ_[p])))
  map_one' := by sorry
  map_mul' _ _ := by sorry
  map_zero' := by sorry
  map_add' _ _ := by sorry

/-- The finite-level maps are jointly injective: a measure vanishing on every
finite-level indicator is zero (locally constant functions on `ℤ_p^×` factor through
some level). Source: RJW Rem. 3.8 + Prop. 3.10 (inverse-limit description). -/
theorem levelMap_jointly_injective (μ : PadicMeasure p ℤ_[p]ˣ)
    (h : ∀ n, levelMap p n μ = 0) : μ = 0 := by
  sorry

end finiteLevel

section zeroDivisor

/-- The function `x ↦ x^k` on `ℤ_p^×`, as a continuous map to `ℤ_p`. -/
def unitsPowCM (k : ℕ) : C(ℤ_[p]ˣ, ℤ_[p]) := ⟨fun u => (u : ℤ_[p]) ^ k, by sorry⟩

/-- **RJW Lem. 3.36(i) (`lem:zero divisor`)**: a measure on `ℤ_p^×` with
`∫ x^k dμ = 0` for all `k > 0` is zero. Source proof (TeX lines 1228–1229): the Mahler
transform of `ιμ` is constant (binomial polynomials with `n ≥ 1` have no constant
term), and `ψ` fixes constants while killing `ιμ`; hence `𝓐_{ιμ} = 0`. -/
theorem eq_zero_of_forall_unitsPowCM_eq_zero (μ : PadicMeasure p ℤ_[p]ˣ)
    (h : ∀ k, 0 < k → μ (unitsPowCM p k) = 0) : μ = 0 := by
  sorry

/-- **RJW Lem. 3.36(ii)**: a measure on `ℤ_p^×` with `∫ x^k dμ ≠ 0` for all `k > 0`
is not a zero divisor. Source proof (TeX lines 1232–1234): `∫ (xy)^k d(μ⋆λ) =
(∫ x^k dμ)(∫ y^k dλ)`, then apply (i). -/
theorem mem_nonZeroDivisors_of_forall_unitsPowCM_ne_zero (μ : PadicMeasure p ℤ_[p]ˣ)
    (h : ∀ k, 0 < k → μ (unitsPowCM p k) ≠ 0) :
    μ ∈ nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ) := by
  sorry

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
    IsPseudoMeasure p (algebraMap _ _ μ) := by
  sorry

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
