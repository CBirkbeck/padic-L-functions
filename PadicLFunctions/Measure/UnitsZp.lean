import PadicLFunctions.Measure.Toolbox

/-!
# Measures on ℤ_p^×

RJW (arXiv:2309.15692) §3.5.4–3.5.5: the space `Λ(ℤ_p^×) = ℳ(ℤ_p^×, ℤ_p)` of measures
on the units, its embedding `ι : Λ(ℤ_p^×) ↪ Λ(ℤ_p)`, and the identification of its
image with `ker ψ` (RJW Rem. 3.33, `not subalgebra`, TeX lines 1169–1176).

We work with the units type `ℤ_[p]ˣ` (with its standard topology from
`Topology.Algebra.Constructions`); the coercion `Units.val` is a closed embedding with
clopen range `{x | IsUnit x} = {x | ‖x‖ = 1}`.
-/

open scoped fwdDiff

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

namespace PadicMeasure

/-- `ℤ_[p]ˣ` is compact: it embeds as a closed subset of `ℤ_[p] × ℤ_[p]`
(via `u ↦ (u, u⁻¹)`, with closed image `{(a,b) | a*b = 1}`). Not in mathlib
(verified absent). -/
instance : CompactSpace ℤ_[p]ˣ := by
  sorry

/-- The coercion `ℤ_[p]ˣ → ℤ_[p]` as a continuous map. -/
def unitsValCM : C(ℤ_[p]ˣ, ℤ_[p]) := ⟨fun u => (u : ℤ_[p]), by sorry⟩

open Classical in
/-- Extension by zero: a continuous function on `ℤ_p^×` extends to `ℤ_p` by `0` outside
the (clopen) units. Auxiliary for surjectivity of restriction and injectivity of `ι`. -/
noncomputable def extendByZero : C(ℤ_[p]ˣ, ℤ_[p]) →ₗ[ℤ_[p]] C(ℤ_[p], ℤ_[p]) where
  toFun g := ⟨fun x => if h : IsUnit x then g h.unit else 0, by sorry⟩
  map_add' _ _ := by sorry
  map_smul' _ _ := by sorry

@[simp]
lemma extendByZero_coe_unit (g : C(ℤ_[p]ˣ, ℤ_[p])) (u : ℤ_[p]ˣ) :
    extendByZero p g (u : ℤ_[p]) = g u := by
  sorry

/-- The embedding `ι : Λ(ℤ_p^×) → Λ(ℤ_p)`: `∫_{ℤ_p} φ d(ιμ) = ∫_{ℤ_p^×} φ|_{ℤ_p^×} dμ`.

Source: RJW Rem. 3.33 (TeX lines 1170–1171). -/
noncomputable def iota : PadicMeasure p ℤ_[p]ˣ →ₗ[ℤ_[p]] PadicMeasure p ℤ_[p] :=
  pushforward p (unitsValCM p)

/-- `ι` is injective (restriction `C(ℤ_p, ℤ_p) → C(ℤ_p^×, ℤ_p)` is surjective, via
extension by zero). Source: RJW Rem. 3.33: "we can identify `Λ(ℤ_p^×)` with its
image". -/
theorem iota_injective : Function.Injective (iota p) := by
  sorry

/-- `Res_{ℤ_p^×} ∘ ι = ι`: the image of `ι` consists of measures supported on the
units. Source: RJW Rem. 3.33 ("`Res_{ℤ_p^×} ∘ ι` is the identity on `Λ(ℤ_p^×)`"). -/
theorem res_iota (μ : PadicMeasure p ℤ_[p]ˣ) :
    res p (isClopen_units p) (iota p μ) = iota p μ := by
  sorry

/-- **The image of `ι` is `ker ψ`**: `μ ∈ range ι ↔ ψ(μ) = 0`.

Source: RJW Rem. 3.33 (TeX lines 1171–1172): "By Corollary 3.32, a measure
`μ ∈ Λ(ℤ_p)` lies in `Λ(ℤ_p^×)` if and only if `ψ(μ) = 0`." -/
theorem mem_range_iota_iff (μ : PadicMeasure p ℤ_[p]) :
    μ ∈ Set.range (iota p) ↔ psi p μ = 0 := by
  sorry

end PadicMeasure
