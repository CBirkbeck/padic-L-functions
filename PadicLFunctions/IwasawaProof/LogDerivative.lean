/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Coleman.Map

/-!
# The logarithmic derivative: the Coleman–Coates–Wiles exact sequence (RJW §12.2.1) — E12.2

`thm:log der` (TeX 3280–3379): the short exact sequence
`0 → μ_{p−1} → (ℤ_p⟦T⟧^×)^{𝒩=id} →[Δ] ℤ_p⟦T⟧^{ψ=id} → 0`. This is the hardest
mathematics in Part II; `lem:B mod p 2` (the explicit `𝔽_p⟦T⟧` construction) is, per the
authors, "the most delicate and technical part". The kernel `μ_{p−1}` is `rem:ker Δ`
(constants `𝒩`-fixed force `f^p = f`); surjectivity reduces mod `p` (`lem:log der red
mod p`, successive approximation + `ℤ_p⟦T⟧^×` compactness from §10) to `A = B`
(`lem:A mod p` + `lem:B mod p`).

Skeleton (`/develop` §12): the series `ψ`-subspaces are stated as `Submodule`s with
`sorry` proof-fields; the theorem and its source sub-lemmas are stated with `sorry`.
-/

open PadicLFunctions PadicLFunctions.Coleman PowerSeries

noncomputable section

namespace PadicLFunctions.Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `ψ = id` subspace of `ℤ_p⟦T⟧` (RJW `ℤ_p⟦T⟧^{ψ=id}`), via the series trace
operator `psiSeries`. -/
def psiIdSeries : Submodule ℤ_[p] (PowerSeries ℤ_[p]) where
  carrier := {F | psiSeries p F = F}
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry

/-- The `ψ = 0` subspace of `ℤ_p⟦T⟧` (RJW `ℤ_p⟦T⟧^{ψ=0}`). -/
def psiZeroSeries : Submodule ℤ_[p] (PowerSeries ℤ_[p]) where
  carrier := {F | psiSeries p F = 0}
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry

/-- `Δ ∘ φ = p · φ ∘ Δ` on power series (RJW TeX 3301, "easy to see from the
definitions") — the engine of `lem:log der 1`. Stated for the additive `del = ∂`
(`PadicMeasure.del`). -/
theorem del_phiHom (f : PowerSeries ℤ_[p]) :
    PadicMeasure.del p (phiHom p f)
      = (p : PowerSeries ℤ_[p]) * phiHom p (PadicMeasure.del p f) := sorry

/-- **RJW lem:log der 1 (TeX 3292–3306)**: `Δ(𝒲) ⊆ ℤ_p⟦T⟧^{ψ=id}`, where
`𝒲 = (ℤ_p⟦T⟧^×)^{𝒩=id}`. -/
theorem dlog_mem_psiIdSeries {f : PowerSeries ℤ_[p]} (hf : IsUnit f) (hN : normOp f = f) :
    dlog p f ∈ psiIdSeries p := sorry

/-- **RJW lem:A mod p (TeX 3337–3343)**: `𝒲 mod p = 𝔽_p⟦T⟧^×` — every unit power
series over `𝔽_p` lifts to a `𝒩`-fixed unit (via `𝒩^k`-convergence, the mod-`p^k`
continuity of `normOp`). Stated as the lift existence. -/
theorem exists_normOp_fixed_lift (f : PowerSeries ℤ_[p]) (hf : IsUnit f) :
    ∃ g : PowerSeries ℤ_[p], IsUnit g ∧ normOp g = g ∧
      PadicLFunctions.Coleman.ModEqPow p 1 g f := sorry

/-- **RJW lem:B mod p 2 (TeX 3359–3373) — "the most delicate and technical part"**: the
`𝔽_p⟦T⟧` decomposition underlying surjectivity mod `p`. Stated over `ZMod p` power
series. The E12.2 execution ticket expands this into its inductive construction (the
expected Tier-A spawn point). -/
theorem fp_series_eq_dlog_add_frobC (g : PowerSeries (ZMod p)) :
    ∃ (a : PowerSeries (ZMod p)) (c : PowerSeries (ZMod p)),
      IsUnit a ∧ c ∈ Set.range (phiSeries p (R := ZMod p)) := sorry

/-- **RJW thm:log der (TeX 3280–3285) — the Coleman–Coates–Wiles short exact sequence.**
Surjectivity half: every `ψ`-fixed series is the logarithmic derivative of a `𝒩`-fixed
unit. (The kernel half is `rem:ker Δ`: `μ_{p−1}`.) -/
theorem dlog_surjective_onto_psiId {F : PowerSeries ℤ_[p]} (hF : F ∈ psiIdSeries p) :
    ∃ g : PowerSeries ℤ_[p], IsUnit g ∧ normOp g = g ∧ dlog p g = F := sorry

/-- The kernel of `Δ = ∂log` on `𝒩`-fixed units is `μ_{p−1}` (RJW rem:ker Δ, TeX
3176–3178): a constant `𝒩`-fixed unit `f` satisfies `f^p = f`. Stated as: `dlog g = 0`
and `𝒩 g = g` ⟹ `g` is a `(p−1)`-th root of unity (constant). -/
theorem dlog_eq_zero_normOp_fixed {g : PowerSeries ℤ_[p]} (hg : IsUnit g)
    (hN : normOp g = g) (hd : dlog p g = 0) :
    ∃ c : ℤ_[p], c ^ p = c ∧ g = PowerSeries.C c := sorry

/-- **RJW lem:rest zp* (TeX 3387–3391)**: the exactness
`0 → ℤ_p → ℤ_p⟦T⟧^{ψ=id} →[1−φ] ℤ_p⟦T⟧^{ψ=0} → ℤ_p → 0`. Surjectivity of `eval₀`
half (`1+T ↦ 1`) + kernel-`ℤ_p` half. -/
theorem one_sub_phi_psiId_mem_psiZero {F : PowerSeries ℤ_[p]} (hF : F ∈ psiIdSeries p) :
    F - phiHom p F ∈ psiZeroSeries p := sorry

theorem exists_one_sub_phi_eq {F : PowerSeries ℤ_[p]} (hF : F ∈ psiZeroSeries p)
    (h0 : constantCoeff F = 0) :
    ∃ G ∈ psiIdSeries p, G - phiHom p G = F := sorry

end PadicLFunctions.Coleman
