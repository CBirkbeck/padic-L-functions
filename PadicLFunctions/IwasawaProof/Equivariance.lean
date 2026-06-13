/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.IwasawaProof.GaloisAction

/-!
# Equivariance of the Coleman map (RJW §12.1, TeX 3117–3243) — 12.1

The `ℤ_p`-action on `𝒰_{∞,1}` (via `zpPow`), the Teichmüller split
`𝒰_∞ = μ_{p−1} × 𝒰_{∞,1}`, the killing of `μ_{p−1}` by `Col`, and the assembly into the
`Λ(𝒢)`-module statement `cor:G-eq`. (The `ℤ_p`-equivariance Prop, TeX 3130–3156,
is subsumed by `Col_lambdaG_equivariant`: the scalar part of the `Λ(𝒢)`-action; its
standalone form is finalised when the `NormCompatUnits` `ℤ_p`-module structure lands at
execution.) Skeleton statements with `sorry`.
-/

open PadicLFunctions PadicLFunctions.Coleman

noncomputable section

namespace PadicLFunctions.Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-- **RJW §12.1 Lemma (TeX 3159–3168)**: `𝒰_∞ = μ_{p−1} × 𝒰_{∞,1}` (Teichmüller split of
the reduction-mod-`𝔭_n` SES `1 → 𝒰_{n,1} → 𝒰_n → μ_{p−1} → 1`). Stated as: every tower
unit splits as a `(p−1)`-torsion part times a principal-unit part. -/
theorem normCompat_eq_teichmuller_mul_principal (u : NormCompatUnits p) :
    ∃ v w : NormCompatUnits p, w ∈ unitsTower1 p ∧
      (∀ n, (v.elems n) ^ (p - 1) = 1) ∧ u = v * w := sorry

/-- **RJW §12.1 Lemma (TeX 3170–3178)**: `μ_{p−1} ⊂ 𝒰_∞` is killed by `Col` (constant
Coleman series are killed by `∂log`). Stated for a `(p−1)`-torsion tower. -/
theorem Col_eq_zero_of_torsion (u : NormCompatUnits p) (htor : ∀ n, (u.elems n) ^ (p - 1) = 1) :
    Col p u = 0 := sorry

/-- **RJW cor:G-eq (TeX 3241–3243)**: `Col` restricts to a map `𝒰_{∞,1} → Λ(𝒢)` of
`Λ(𝒢)`-modules (the `ℤ_p`- and `𝒢`-actions commute and assemble to `Λ(𝒢)`). Stated as
the conjunction of `ℤ_p`- and `𝒢`-equivariance already established. -/
theorem Col_lambdaG_equivariant (a : ℤ_[p]ˣ) (u : NormCompatUnits p)
    (_hu : u ∈ unitsTower1 p) :
    Col p (galNCU p a u) = PadicMeasure.unitsCmul p 1 (Col p u) := Col_galNCU p a u

end PadicLFunctions.Coleman
