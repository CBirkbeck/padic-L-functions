import PadicLFunctions.Measure.PseudoMeasure
import PadicLFunctions.EisensteinFamily
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The ±-decomposition of Λ(𝒢) and the plus quotient Λ(𝒢⁺)

RJW (arXiv:2309.15692) §11.1 (`sec:measures on galois groups`, TeX 2964–3042). Per the
notes' own identification (TeX 2970: "From now on, we will let Λ(𝒢) be the space of
measures on 𝒢, which we identify with Λ(ℤ_p^×) via the cyclotomic character"), the
Galois group 𝒢 is `ℤ_[p]ˣ`, complex conjugation `c` is `(-1 : ℤ_[p]ˣ)`, and
`𝒢⁺ = 𝒢/⟨c⟩` is the quotient group `GPlus p = ℤ_[p]ˣ ⧸ zpowers (-1)`
(decomposition replan R11.1).

## Main declarations

* `PadicMeasure.invariants`/`antiInvariants` + `isCompl_invariants_antiInvariants`:
  the general ±-eigenspace splitting for an involution of a module with `2` invertible
  (RJW Lem. `lem:decompose plus minus`, TeX 2994–3002; not in mathlib — PR candidate).
* `PadicMeasure.cAct`: the action of `c` on `Λ(ℤ_p^×)` (convolution by `dirac (-1)`),
  `plusPart`/`minusPart`, and the instance of the decomposition lemma.
* `PadicMeasure.mem_plusPart_iff_forall_odd_moment`: the odd-moment membership
  criterion (RJW TeX 3019–3029; p-general in the c-invariance phrasing).
* `PadicMeasure.GPlus` and the pushforward `projPlus : Λ(𝒢) →+* Λ(𝒢⁺)`,
  the even-part section `plusSection`, and the isomorphism Λ(𝒢)⁺ ≅ Λ(𝒢⁺)
  (RJW TeX 3006–3015; functional-route proof, replan R11.2).
-/

open scoped fwdDiff

noncomputable section

namespace PadicMeasure

/-! ## The general ±-decomposition (RJW Lem. `lem:decompose plus minus`) -/

section involution

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The `+1`-eigenspace (invariants) of an endomorphism `σ : M →ₗ[R] M`. -/
def invariants (σ : M →ₗ[R] M) : Submodule R M :=
  LinearMap.ker (σ - LinearMap.id)

/-- The `−1`-eigenspace (anti-invariants) of an endomorphism `σ : M →ₗ[R] M`. -/
def antiInvariants (σ : M →ₗ[R] M) : Submodule R M :=
  LinearMap.ker (σ + LinearMap.id)

lemma mem_invariants_iff {σ : M →ₗ[R] M} {x : M} : x ∈ invariants σ ↔ σ x = x := by
  sorry

lemma mem_antiInvariants_iff {σ : M →ₗ[R] M} {x : M} :
    x ∈ antiInvariants σ ↔ σ x = -x := by
  sorry

/-- **RJW Lem. `lem:decompose plus minus` (TeX 2994–3002)**: for an involution `σ` of an
`R`-module `M` with `2` invertible in `R`, the module decomposes as the internal direct
sum of the `±1`-eigenspaces, via the idempotents `(1 ± σ)/2`. (The source states this
for a module with a continuous 𝒢-action; only the action of `c` is used, i.e. exactly
an involution.) Not in mathlib (verified absent); PR candidate. -/
theorem isCompl_invariants_antiInvariants [Invertible (2 : R)] (σ : M →ₗ[R] M)
    (hσ : σ ∘ₗ σ = LinearMap.id) :
    IsCompl (invariants σ) (antiInvariants σ) := by
  sorry

/-- The plus-projection formula: `(x + σx)/2` lands in the invariants. -/
theorem smul_add_apply_mem_invariants [Invertible (2 : R)] (σ : M →ₗ[R] M)
    (hσ : σ ∘ₗ σ = LinearMap.id) (x : M) :
    (⅟(2 : R)) • (x + σ x) ∈ invariants σ := by
  sorry

/-- The minus-projection formula: `(x − σx)/2` lands in the anti-invariants. -/
theorem smul_sub_apply_mem_antiInvariants [Invertible (2 : R)] (σ : M →ₗ[R] M)
    (hσ : σ ∘ₗ σ = LinearMap.id) (x : M) :
    (⅟(2 : R)) • (x - σ x) ∈ antiInvariants σ := by
  sorry

end involution

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## ℤ_p-bilinearity of the convolution product

The `SMulCommClass`/`IsScalarTower` instances making `Λ(ℤ_p^×)` an honest
ℤ_[p]-algebra-like object (the gap noted at the §8 pass). -/

instance : SMulCommClass ℤ_[p] (PadicMeasure p ℤ_[p]ˣ) (PadicMeasure p ℤ_[p]ˣ) := by
  sorry

instance : IsScalarTower ℤ_[p] (PadicMeasure p ℤ_[p]ˣ) (PadicMeasure p ℤ_[p]ˣ) := by
  sorry

/-! ## The c-action on Λ(𝒢) (c = complex conjugation = −1 ∈ ℤ_p^× under χ) -/

/-- The action of complex conjugation on `Λ(𝒢) = Λ(ℤ_p^×)`: convolution by the Dirac
measure at `c = -1` (under the cyclotomic identification, RJW TeX 2970/2992). -/
def cAct : PadicMeasure p ℤ_[p]ˣ →ₗ[ℤ_[p]] PadicMeasure p ℤ_[p]ˣ :=
  LinearMap.mulLeft ℤ_[p] (dirac p (-1 : ℤ_[p]ˣ))

@[simp]
lemma cAct_apply (μ : PadicMeasure p ℤ_[p]ˣ) :
    cAct p μ = dirac p (-1 : ℤ_[p]ˣ) * μ := by
  sorry

/-- `c` is an involution: `[−1]·[−1] = [1]`. -/
theorem cAct_involutive : cAct p ∘ₗ cAct p = LinearMap.id := by
  sorry

/-- `Λ(𝒢)⁺`: the c-invariant measures (the image of the idempotent `(1+c)/2`).
Under the identification of RJW TeX 3017 this *is* `Λ(𝒢⁺)` viewed inside `Λ(𝒢)`. -/
def plusPart : Submodule ℤ_[p] (PadicMeasure p ℤ_[p]ˣ) :=
  invariants (cAct p)

/-- `Λ(𝒢)⁻`: the c-anti-invariant measures. -/
def minusPart : Submodule ℤ_[p] (PadicMeasure p ℤ_[p]ˣ) :=
  antiInvariants (cAct p)

lemma mem_plusPart_iff {μ : PadicMeasure p ℤ_[p]ˣ} :
    μ ∈ plusPart p ↔ dirac p (-1 : ℤ_[p]ˣ) * μ = μ := by
  sorry

lemma mem_minusPart_iff {μ : PadicMeasure p ℤ_[p]ˣ} :
    μ ∈ minusPart p ↔ dirac p (-1 : ℤ_[p]ˣ) * μ = -μ := by
  sorry

/-- `plusPart` is closed under multiplication by arbitrary measures (it is the ideal
`e⁺Λ(𝒢)`). -/
theorem mul_mem_plusPart {μ ν : PadicMeasure p ℤ_[p]ˣ} (hμ : μ ∈ plusPart p) :
    ν * μ ∈ plusPart p := by
  sorry

/-- **RJW Lem. `lem:decompose plus minus` for Λ(𝒢)** (TeX 3004: "We are assuming that
`p` is odd, so Λ(𝒢) ≅ Λ(𝒢)⁺ ⊕ Λ(𝒢)⁻"). -/
theorem isCompl_plusPart_minusPart (hp2 : p ≠ 2) :
    IsCompl (plusPart p) (minusPart p) := by
  sorry

/-! ## The odd-moment criterion (RJW TeX 3019–3029) -/

/-- Moments of the c-translate: `∫ x^k d([−1]·μ) = (−1)^k ∫ x^k dμ`
(the computation `χ(c) = −1` of the source's proof, TeX 3026–3028). -/
theorem cAct_apply_unitsPowCM (μ : PadicMeasure p ℤ_[p]ˣ) (k : ℕ) :
    (dirac p (-1 : ℤ_[p]ˣ) * μ) (unitsPowCM p k) = (-1) ^ k * μ (unitsPowCM p k) := by
  sorry

/-- **RJW §11.1, third lemma (TeX 3019–3029)**: `μ ∈ Λ(𝒢⁺)` (= c-invariance, by the
TeX 3017 identification) if and only if all odd moments `∫_𝒢 χ(x)^k·μ`, `k ≥ 1` odd,
vanish. This direction-pair is p-general (`ℤ_[p]` has characteristic zero); the
*decomposition* interpretation needs `p ≠ 2`. -/
theorem mem_plusPart_iff_forall_odd_moment {μ : PadicMeasure p ℤ_[p]ˣ} :
    μ ∈ plusPart p ↔ ∀ k : ℕ, Odd k → μ (unitsPowCM p k) = 0 := by
  sorry

/-! ## The quotient group 𝒢⁺ = ℤ_p^×/{±1} and Λ(𝒢⁺) -/

/-- `𝒢⁺ = 𝒢/⟨c⟩`, identified through the cyclotomic character with `ℤ_p^×/{±1}`
(RJW TeX 2992). The quotient of the compact group `ℤ_[p]ˣ` by the closed (finite)
subgroup `{±1}`; mathlib provides the compact topological-group structure, and the
generalised convolution algebra (`PadicMeasure.conv`, replan R11.5) provides the ring
structure on its measures. -/
abbrev GPlus := ℤ_[p]ˣ ⧸ Subgroup.zpowers (-1 : ℤ_[p]ˣ)

/-- The quotient projection `𝒢 → 𝒢⁺` as a continuous map. -/
def quotientMk : C(ℤ_[p]ˣ, GPlus p) :=
  ⟨QuotientGroup.mk, continuous_quotient_mk'⟩

/-- The pushforward `π_* : Λ(𝒢) → Λ(𝒢⁺)` along the quotient projection — the
"natural surjection" of RJW TeX 3012, as the inverse-limit-free measure-functional
incarnation. Ring-hom because `mk` is a (continuous) monoid hom. -/
def projPlus : PadicMeasure p ℤ_[p]ˣ →+* PadicMeasure p (GPlus p) where
  toFun := pushforward p (quotientMk p)
  map_one' := by sorry
  map_mul' := by sorry
  map_zero' := by sorry
  map_add' := by sorry

@[simp]
lemma projPlus_apply (μ : PadicMeasure p ℤ_[p]ˣ) (f : C(GPlus p, ℤ_[p])) :
    projPlus p μ f = μ (f.comp (quotientMk p)) := by
  sorry

@[simp]
lemma projPlus_dirac (u : ℤ_[p]ˣ) :
    projPlus p (dirac p u) = dirac p (QuotientGroup.mk u : GPlus p) := by
  sorry

/-- The augmentation commutes with the projection: `deg⁺ ∘ π_* = deg`. -/
theorem deg_projPlus (μ : PadicMeasure p ℤ_[p]ˣ) :
    deg p (projPlus p μ) = deg p μ := by
  sorry

/-! ## The even-part section and the isomorphism Λ(𝒢)⁺ ≅ Λ(𝒢⁺) -/

/-- Translation by `−1` on `ℤ_[p]ˣ`, as a continuous map (the `c`-translation of
function arguments). -/
def negTranslate : C(ℤ_[p]ˣ, ℤ_[p]ˣ) :=
  ⟨fun u => -u, by sorry⟩

/-- The even part of a continuous function on `𝒢`: `f ↦ (f + f∘c)/2` (`p ≠ 2`). -/
def evenPart (hp2 : p ≠ 2) (f : C(ℤ_[p]ˣ, ℤ_[p])) : C(ℤ_[p]ˣ, ℤ_[p]) :=
  (((PadicLFunctions.isUnit_two_padicInt p hp2).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
    • (f + f.comp (negTranslate p))

/-- An even continuous function on `𝒢` descends to a continuous function on `𝒢⁺`
(soundness: the `{±1}`-cosets are `{u, −u}`; continuity: `mk` is a quotient map). -/
def descendEven (g : C(ℤ_[p]ˣ, ℤ_[p])) (hg : ∀ u : ℤ_[p]ˣ, g (-u) = g u) :
    C(GPlus p, ℤ_[p]) :=
  ⟨fun x => Quotient.liftOn' x g (by sorry), by sorry⟩

@[simp]
lemma descendEven_mk (g : C(ℤ_[p]ˣ, ℤ_[p])) (hg : ∀ u : ℤ_[p]ˣ, g (-u) = g u)
    (u : ℤ_[p]ˣ) :
    descendEven p g hg (QuotientGroup.mk u) = g u := by
  sorry

lemma evenPart_even (hp2 : p ≠ 2) (f : C(ℤ_[p]ˣ, ℤ_[p])) (u : ℤ_[p]ˣ) :
    evenPart p hp2 f (-u) = evenPart p hp2 f u := by
  sorry

/-- The even-part section `σ : Λ(𝒢⁺) → Λ(𝒢)`: `(σν)(f) := ν(descend((f + f∘c)/2))`.
This is the functional-analytic replacement (replan R11.2) for the source's
finite-level inverse of the natural surjection. -/
def plusSection (hp2 : p ≠ 2) :
    PadicMeasure p (GPlus p) →ₗ[ℤ_[p]] PadicMeasure p ℤ_[p]ˣ where
  toFun ν :=
    { toFun := fun f => ν (descendEven p (evenPart p hp2 f) (evenPart_even p hp2 f))
      map_add' := by sorry
      map_smul' := by sorry }
  map_add' := by sorry
  map_smul' := by sorry

/-- The section lands in the plus part. -/
theorem plusSection_mem_plusPart (hp2 : p ≠ 2) (ν : PadicMeasure p (GPlus p)) :
    plusSection p hp2 ν ∈ plusPart p := by
  sorry

/-- `π_* ∘ σ = id`: the section is a right inverse (hence `π_*` is surjective). -/
theorem projPlus_plusSection (hp2 : p ≠ 2) (ν : PadicMeasure p (GPlus p)) :
    projPlus p (plusSection p hp2 ν) = ν := by
  sorry

/-- `σ ∘ π_* = id` on the plus part: a c-invariant measure is determined by its
pushforward (the injectivity half of RJW TeX 3006–3015). -/
theorem plusSection_projPlus (hp2 : p ≠ 2) {μ : PadicMeasure p ℤ_[p]ˣ}
    (hμ : μ ∈ plusPart p) :
    plusSection p hp2 (projPlus p μ) = μ := by
  sorry

theorem projPlus_surjective (hp2 : p ≠ 2) :
    Function.Surjective (projPlus p) := by
  sorry

/-- **RJW §11.1, second lemma (TeX 3006–3015)**: the natural isomorphism
`Λ(𝒢)⁺ ≅ Λ(𝒢⁺)`, realised by `π_*` restricted to the plus part, with inverse the
even-part section. (Multiplicativity is `projPlus.map_mul` on representatives.) -/
def plusEquiv (hp2 : p ≠ 2) :
    plusPart p ≃ₗ[ℤ_[p]] PadicMeasure p (GPlus p) :=
  LinearEquiv.ofLinear
    (pushforward p (quotientMk p) ∘ₗ (plusPart p).subtype)
    ((plusSection p hp2).codRestrict (plusPart p) (plusSection_mem_plusPart p hp2))
    (by sorry)
    (by sorry)

/-- The kernel of `π_*` is the minus part… -/
theorem projPlus_eq_zero_iff (hp2 : p ≠ 2) {μ : PadicMeasure p ℤ_[p]ˣ} :
    projPlus p μ = 0 ↔ μ ∈ minusPart p := by
  sorry

/-- …equivalently the principal ideal `([−1] − [1])·Λ(𝒢)` (so
`Λ(𝒢⁺) ≅ Λ(𝒢)/([−1]−[1])` — the ring-quotient picture used for transporting the
augmentation-ideal results). -/
theorem ker_projPlus (hp2 : p ≠ 2) :
    RingHom.ker (projPlus p)
      = Ideal.span {(dirac p (-1 : ℤ_[p]ˣ) - 1 : PadicMeasure p ℤ_[p]ˣ)} := by
  sorry

end PadicMeasure
