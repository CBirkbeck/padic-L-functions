import PadicLFunctions.Measure.Basic
import Mathlib.Topology.CompactOpen

/-!
# A Fubini theorem for p-adic measures

The swap `∫∫ F(x,y) dμ(x) dν(y) = ∫∫ F(x,y) dν(y) dμ(x)` for `ℤ_[p]`-valued measures
on compact totally disconnected spaces. This is the engine behind commutativity and
associativity of convolution on `Λ(ℤ_p^×)` (RJW Rem. 3.11: "One checks that this does
give an algebra structure" — the check, on locally constant functions, is a finite
exchange of sums; density does the rest).

Strategy (mirrors RJW Rem. 3.8's reduction to locally constant functions):
1. On a product of compact totally disconnected (profinite) spaces, every locally
   constant function is a finite `ℤ_[p]`-combination of indicators of clopen boxes
   `U × V` (`locallyConstant_prod_mem_span_boxes`).
2. For box indicators the double integrals are both `μ(𝟙_U)·ν(𝟙_V)`; linearity gives
   the swap for locally constant `F`.
3. Both sides are continuous in `F` (`PadicMeasure.norm_apply_le`), so density of
   locally constant functions (`exists_locallyConstant_norm_sub_le`) concludes.
-/

open scoped fwdDiff

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

namespace PadicMeasure

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The inner integral: `x ↦ ∫ F(x, y) dν(y)`, as a continuous map. -/
noncomputable def innerInt [CompactSpace Y] (ν : PadicMeasure p Y) (F : C(X × Y, ℤ_[p])) :
    C(X, ℤ_[p]) :=
  ⟨fun x => ν (F.curry x), by sorry⟩

@[simp]
lemma innerInt_apply [CompactSpace Y] (ν : PadicMeasure p Y) (F : C(X × Y, ℤ_[p])) (x : X) :
    innerInt p ν F x = ν (F.curry x) := rfl

/-- On a product of compact totally disconnected Hausdorff spaces, every locally
constant `ℤ_[p]`-valued function is a finite `ℤ_[p]`-linear combination of indicators
of clopen boxes `U × V`. (Refine the level sets into a finite grid of clopen boxes,
using that clopen boxes form a basis of the product of two profinite spaces.) -/
theorem locallyConstant_prod_mem_span_boxes
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y]
    (F : LocallyConstant (X × Y) ℤ_[p]) :
    (F : C(X × Y, ℤ_[p])) ∈ Submodule.span ℤ_[p]
      {h : C(X × Y, ℤ_[p]) | ∃ (U : Set X) (V : Set Y) (hU : IsClopen U) (hV : IsClopen V),
        h = ((LocallyConstant.charFn ℤ_[p] hU : C(X, ℤ_[p])).comp ⟨Prod.fst, by fun_prop⟩) *
            ((LocallyConstant.charFn ℤ_[p] hV : C(Y, ℤ_[p])).comp ⟨Prod.snd, by fun_prop⟩)} := by
  sorry

/-- **Fubini for p-adic measures**: the two iterated integrals of
`F ∈ C(X × Y, ℤ_[p])` against measures `μ` on `X` and `ν` on `Y` agree:
`∫_X (∫_Y F(x,y) dν) dμ = ∫_Y (∫_X F(x,y) dμ) dν`.

Source: this is the "one checks" of RJW Rem. 3.11 (TeX line 910), reduced to locally
constant functions exactly as in RJW Rem. 3.8. -/
theorem integral_swap
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y]
    (μ : PadicMeasure p X) (ν : PadicMeasure p Y) (F : C(X × Y, ℤ_[p])) :
    μ (innerInt p ν F) =
      ν (innerInt p μ (F.comp ⟨Prod.swap, continuous_swap⟩)) := by
  sorry

end PadicMeasure
