/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.IwasawaProof.LogDerivative
import PadicLFunctions.IwasawaProof.Equivariance

/-!
# The fundamental exact sequence (RJW §12.2.2, TeX 3382–3441) — E12.3

`def:Zp(1)`, `lem:rest zp*` (already partly in `LogDerivative`), and `thm:fund exact seq`:
`0 → ℤ_p(1) → 𝒰_{∞,1} →[Col] Λ(𝒢) → ℤ_p(1) → 0` as `Λ(𝒢)`-modules. Skeleton.
-/

open PadicLFunctions PadicLFunctions.Coleman

noncomputable section

namespace PadicLFunctions.Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-- **RJW def:Zp(1) (TeX 3407–3409)**: `ℤ_p(1) = {(ξ_n^a)_n : a ∈ ℤ_p} ⊂ 𝒰_∞`, the
integral Tate twist, realised as a subgroup of the unit tower (`zpPow` on `ξ_n`). -/
def ZpOne : Subgroup (NormCompatUnits p) := sorry

/-- **RJW thm:fund exact seq (TeX 3411–3418), left-exactness**: the kernel of `Col` on
`𝒰_{∞,1}` is `ℤ_p(1)`. -/
theorem mem_ker_Col_iff_mem_ZpOne {u : NormCompatUnits p} (hu : u ∈ unitsTower1 p) :
    Col p u = 0 ↔ u ∈ ZpOne p := sorry

/-- **RJW thm:fund exact seq, right-exactness / cokernel**: the image of `Col` on
`𝒰_{∞,1}` is the kernel of the `χ`-moment `μ ↦ ∫_𝒢 χ·μ = μ(x)` (cokernel `ℤ_p(1)`). -/
theorem range_Col_eq_ker_chiMoment (μ : PadicMeasure p ℤ_[p]ˣ) :
    (∃ u ∈ unitsTower1 p, Col p u = μ) ↔ μ (PadicMeasure.unitsPowCM p 1) = 0 := sorry

end PadicLFunctions.Coleman
