import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.MetricSpace.Ultra.ContinuousMaps

/-!
# p-adic measures on a compact space

Following Rodrigues Jacinto–Williams, *An introduction to p-adic L-functions*
(arXiv:2309.15692) §3.2, we define the space of `ℤ_[p]`-valued p-adic measures on a
topological space `X` as the space of `ℤ_[p]`-linear functionals on `C(X, ℤ_[p])`.

The source (Def. 3.6, `def:measures`) defines `L`-valued measures as the *continuous*
dual of `C(G, L)` and singles out the `𝒪_L`-valued ones; over `ℤ_[p]`, continuity of an
`ℤ_[p]`-linear functional is automatic (`PadicMeasure.norm_apply_le`,
`PadicMeasure.continuous`), so no continuity hypothesis is needed in the definition.
This file is the `𝒪 = ℤ_[p]` case; the general coefficient case is deferred to the §5
development pass (see `.mathlib-quality/plan.md`, Generality Decisions).

## Main definitions

* `PadicMeasure p X`: `ℤ_[p]`-valued measures on `X`.
* `PadicMeasure.dirac`: the Dirac measure at a point (source Ex. 3.7, `ex:dirac`).
* `PadicMeasure.pushforward`: pushforward along a continuous map; specialises to the
  `σ_a`, `φ` operators and the embedding `Λ(ℤ_p^×) ↪ Λ(ℤ_p)` later.

## Main results

* `PadicMeasure.norm_apply_le` / `PadicMeasure.continuous`: automatic boundedness and
  continuity (source: footnote to Def. 3.6 — boundedness ⟺ continuity).
* `PadicMeasure.exists_locallyConstant_norm_sub_le`: density of locally constant
  functions (source: Rem. 3.8, `rem:locally constant`, lines 782–802).
* `PadicMeasure.ext_locallyConstant`: a measure is determined by its values on locally
  constant functions (source: Eq. (3.1), `eq:restrict measures`).
-/

open scoped fwdDiff

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

/-- The space of `ℤ_[p]`-valued *p-adic measures* on a topological space `X`: `ℤ_[p]`-linear
functionals on the continuous functions `C(X, ℤ_[p])`. Over `ℤ_[p]` every linear functional
is automatically bounded (norm ≤ 1) and continuous, so this agrees with the continuous
dual used in the source.

Source: RJW Def. 3.6 (`def:measures`, TeX line 760) together with the `𝒪_L`-valued
convention of line 765. -/
abbrev PadicMeasure (X : Type*) [TopologicalSpace X] :=
  C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]

namespace PadicMeasure

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

section basic

/-- The *Dirac measure* at `x : X`: the functional `φ ↦ φ x`.

Source: RJW Ex. 3.7 (`ex:dirac`, TeX lines 774–779). -/
def dirac (x : X) : PadicMeasure p X where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma dirac_apply (x : X) (f : C(X, ℤ_[p])) : dirac p x f = f x := rfl

/-- Precomposition with a continuous map `m : C(X, Y)`, as a linear map
`C(Y, ℤ_[p]) →ₗ[ℤ_[p]] C(X, ℤ_[p])`. Auxiliary for `PadicMeasure.pushforward`. -/
def compRight (m : C(X, Y)) : C(Y, ℤ_[p]) →ₗ[ℤ_[p]] C(X, ℤ_[p]) where
  toFun f := f.comp m
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
lemma compRight_apply (m : C(X, Y)) (f : C(Y, ℤ_[p])) : compRight p m f = f.comp m := rfl

/-- The *pushforward* of a measure along a continuous map `m : C(X, Y)`:
`(pushforward m μ) f = ∫ f ∘ m dμ`. Specialises to `σ_a` and `φ` (RJW §3.5.4) and to
the embedding `Λ(ℤ_p^×) → Λ(ℤ_p)` (RJW Rem. 3.33). -/
def pushforward (m : C(X, Y)) : PadicMeasure p X →ₗ[ℤ_[p]] PadicMeasure p Y where
  toFun μ := μ.comp (compRight p m)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma pushforward_apply (m : C(X, Y)) (μ : PadicMeasure p X) (f : C(Y, ℤ_[p])) :
    pushforward p m μ f = μ (f.comp m) := rfl

@[simp]
lemma pushforward_dirac (m : C(X, Y)) (x : X) :
    pushforward p m (dirac p x) = dirac p (m x) := rfl

end basic

section compact

variable [CompactSpace X]

/-- Every `ℤ_[p]`-linear functional on `C(X, ℤ_[p])` is bounded with norm at most `1`:
if `‖f‖ ≤ p^{-m}` then `f = p^m • g` for a continuous `g`, so `‖μ f‖ ≤ p^{-m}`.

Source: RJW Def. 3.6, footnote (boundedness of measures; TeX line 759), combined with
the `𝒪_L`-valuedness convention of line 765. -/
theorem norm_apply_le (μ : PadicMeasure p X) (f : C(X, ℤ_[p])) : ‖μ f‖ ≤ ‖f‖ := by
  sorry

/-- Measures are automatically continuous (the source's "measures are continuous (or
equivalently, bounded)", TeX line 765). -/
theorem continuous (μ : PadicMeasure p X) : Continuous μ := by
  sorry

/-- **Density of locally constant functions**: any continuous `f : X → ℤ_[p]` on a
compact space is uniformly approximated by locally constant functions. The preimages of
the (clopen) balls of radius `ε` form a clopen cover; pass to a finite subcover,
disjointify, and pick values.

Source: RJW Rem. 3.8 (`rem:locally constant`, TeX lines 782–791): "any continuous
function `φ ∈ 𝒞(G, 𝒪_L)` can be p-adically approximated by its locally constant
truncations". Not in mathlib (verified absent); PR candidate. -/
theorem exists_locallyConstant_norm_sub_le (f : C(X, ℤ_[p])) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : LocallyConstant X ℤ_[p], ‖f - (g : C(X, ℤ_[p]))‖ ≤ ε := by
  sorry

/-- A measure is determined by its values on locally constant functions.

Source: RJW Eq. (3.1) (`eq:restrict measures`, TeX lines 787–799): restriction defines
an isomorphism `ℳ(G, 𝒪_L) ≅ ℳ^lc(G, 𝒪_L)`; injectivity is this statement. -/
theorem ext_locallyConstant {μ ν : PadicMeasure p X}
    (h : ∀ g : LocallyConstant X ℤ_[p], μ (g : C(X, ℤ_[p])) = ν (g : C(X, ℤ_[p]))) :
    μ = ν := by
  sorry

end compact

end PadicMeasure
