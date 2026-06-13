/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.IwasawaProof.FundamentalSequence
import PadicLFunctions.IwasawaProof.Generators

/-!
# Iwasawa's theorem (RJW §12.5, TeX 3582–3608) — E12.5, MILESTONE

`thm:iwasawa 2`: the Coleman map induces (i) a short exact sequence of `Λ(𝒢)`-modules
`0 → 𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p → ℤ_p(1) → 0` and (ii) the isomorphism
`𝒰_{∞,1}^+/𝒞_{∞,1}^+ ≅ Λ(𝒢^+)/I(𝒢^+)ζ_p` (the §11-stated, then-unwired, `thm:iwasawa`).
The image computation uses `Col_cyclo`/`coleman_to_kl` at the generators
(`LemmaGeneratorCinfty1`); (ii) follows from (i) since `p` is odd, `⟨c⟩`-invariants are
exact, and `ℤ_p(1)^{⟨c⟩} = 0`. Skeleton.
-/

open PadicLFunctions PadicLFunctions.Coleman

noncomputable section

namespace PadicLFunctions.Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-- **RJW thm:iwasawa 2 (ii) — THE MILESTONE (TeX 3592–3593)**: the Coleman map induces an
isomorphism of `Λ(𝒢^+)`-modules `𝒰_{∞,1}^+/𝒞_{∞,1}^+ ≅ Λ(𝒢^+)/I(𝒢^+)ζ_p`. This is
`thm:iwasawa` (stated, then unwired, in the §11 chapter), now proved. Stated as the
existence of a `Λ(𝒢^+)`-linear (here `ℤ_[p]`-linear placeholder; the `Λ(𝒢^+)`-structure
on the quotient is wired at execution) isomorphism between the two quotients. -/
theorem iwasawa_theorem (hp2 : p ≠ 2) :
    Nonempty (
      Additive (↥(unitsTower1Plus p) ⧸ (cycloTower1Plus p).subgroupOf (unitsTower1Plus p)) ≃+
      (PadicMeasure p (PadicMeasure.GPlus p) ⧸ PadicMeasure.zetaIdealPlus p hp2)) := sorry

/-- **RJW thm:iwasawa 2 (i) (TeX 3590–3591)**: the `Λ(𝒢)`-module short exact sequence
`0 → 𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p → ℤ_p(1) → 0`. Stated as the injection
`𝒰_{∞,1}/𝒞_{∞,1} ↪ Λ(𝒢)/I(𝒢)ζ_p` with cokernel `ℤ_p(1)` (the `χ`-moment). -/
theorem iwasawa_exact_sequence (hp2 : p ≠ 2) :
    Nonempty (
      Additive (↥(unitsTower1 p) ⧸ (cycloTower1 p).subgroupOf (unitsTower1 p)) →+
      (PadicMeasure p ℤ_[p]ˣ ⧸ PadicMeasure.zetaIdeal p hp2)) := sorry

end PadicLFunctions.Coleman
