/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Coleman.Map
import PadicLFunctions.Iwasawa.LocalUnits
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# The Galois action on the cyclotomic tower (RJW §12.1, TeX 3182–3243) — E12.1

The linchpin of §12: an action of `𝒢 = ℤ_[p]ˣ` (via the cyclotomic character) on the
tower `𝒰_∞ = NormCompatUnits p`, by `σ_a(ξ_n) = ξ_n^{a mod p^n}`, and the
`𝒢`-equivariance of the Coleman map. mathlib supplies the ABSTRACT iso
`IsCyclotomicExtension.autEquivPow : (K_n ≃ₐ[ℚ_p] K_n) ≃* (ZMod (p^n))ˣ` (Tower.lean's
`isCyclotomicExtension_K` enables it over `ℚ_[p]`); the work here is realising the action
on the concrete fixed-`ξ` `ℂ_[p]`-tower, compatibly across levels and commuting with
`levelNorm`.

Skeleton (`/develop` §12): the constructions `galAut`/`galNCU`/`galSeries` are stated with
`sorry` bodies so the downstream equivariance statements elaborate; the E12.1 execution
ticket fills them (its first step: make Tower's `isCyclotomicExtension_K` public, then
`galAut p a n := (IsCyclotomicExtension.autEquivPow (K p n) (cyclotomic_irreducible_Qp …)).symm
(unitsToZModPow p n a)`).
-/

open PadicLFunctions PadicLFunctions.Coleman

noncomputable section

namespace PadicLFunctions.Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-- `σ_a` at level `n`: the automorphism of `K_n` sending `ξ_n ↦ ξ_n^{a mod p^n}`
(RJW TeX 3190). Constructed from `IsCyclotomicExtension.autEquivPow`. -/
def galAut (a : ℤ_[p]ˣ) (n : ℕ) : (K p n) ≃ₐ[ℚ_[p]] (K p n) := sorry

/-- `σ_a(ξ_n) = ξ_n^{(a mod p^n)}` (the defining cyclotomic-character property,
`IsPrimitiveRoot.autToPow_spec`). -/
theorem galAut_zetaSys (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) :
    (galAut p a n ⟨zetaSys p n, zetaSys_mem_K p n⟩ : ℂ_[p])
      = zetaSys p n ^ ((PadicMeasure.unitsToZModPow p n a : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)).val :=
  sorry

/-- Tower compatibility: `σ_a` at level `n+1` restricts to `σ_a` at level `n`
(uniqueness of the automorphism realising the character value). -/
theorem galAut_compat (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]} (hx : x ∈ K p n) :
    (galAut p a (n + 1) ⟨x, (K_le_succ p n) hx⟩ : ℂ_[p])
      = (galAut p a n ⟨x, hx⟩ : ℂ_[p]) := sorry

/-- The relative norm is Galois-equivariant: `N_{n+1,n} ∘ σ_a = σ_a ∘ N_{n+1,n}`
(conjugation-invariance of `Algebra.norm`). -/
theorem levelNorm_galAut (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]}
    (hx : x ∈ K p (n + 1)) :
    levelNorm p n (galAut p a (n + 1) ⟨x, hx⟩ : ℂ_[p])
      = (galAut p a n ⟨levelNorm p n x, levelNorm_mem p n hx⟩ : ℂ_[p]) := sorry

/-- The `𝒢`-action `σ_a` on the norm-compatible unit tower `𝒰_∞` (RJW TeX 3201–3204):
levelwise application of `galAut`, well-defined by `galAut_compat` + `levelNorm_galAut`. -/
def galNCU (a : ℤ_[p]ˣ) (u : NormCompatUnits p) : NormCompatUnits p := sorry

/-- `σ_a` on power series: `f ↦ f((1+T)^a − 1)` (RJW TeX 3206). -/
def galSeries (a : ℤ_[p]ˣ) (f : PowerSeries ℤ_[p]) : PowerSeries ℤ_[p] := sorry

/-- The Coleman series intertwines the two actions: `f_{σ_a u} = σ_a f_u`
(RJW TeX 3210–3216, via interpolation + `coleman_existsUnique` uniqueness). -/
theorem colemanSeries_galNCU (a : ℤ_[p]ˣ) (u : NormCompatUnits p) :
    colemanSeries p (galNCU p a u) = galSeries p a (colemanSeries p u) := sorry

/-- **RJW §12.1 Proposition (TeX 3193–3236)**: the Coleman map is `𝒢`-equivariant.
Here `σ_a` acts on `Λ(ℤ_[p]ˣ)` by the pushforward along multiplication by `a`. -/
theorem Col_galNCU (a : ℤ_[p]ˣ) (u : NormCompatUnits p) :
    Col p (galNCU p a u)
      -- statement-shape placeholder; E12.1 finalises the σ_a-on-measures form
      = PadicMeasure.unitsCmul p 1 (Col p u) := sorry

end PadicLFunctions.Coleman
