/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import PadicLFunctions.Interpolation.GenBernoulli

/-!
# The complex bridge: `L(χ, −k) = −B_{k+1,χ}/(k+1)`

Quarantined complex-analytic comparison (the §5 analogue of
`ZetaValuesComplex.lean`): mathlib's analytically-continued Dirichlet
L-function agrees at negative integers with the generalised Bernoulli values
used by the `p`-adic statements. mathlib defines
`DirichletCharacter.LFunction χ s = N^{−s} ∑_j χ(j)·hurwitzZeta (j/N) s`, so
this follows from `hurwitzZeta_neg_nat` (Bernoulli-polynomial values of the
Hurwitz zeta function). PR candidate.

Source: RJW Lem 5.5 / Lem 5.9 (TeX 1702–1740, 1801–1807), whose proofs go
through the §2 Mellin theory; the value identity itself is classical
(Washington Thm 4.2).
-/

namespace PadicLFunctions

open DirichletCharacter

/-- L5.2.9: values of the (analytically continued) Dirichlet L-function at
negative integers, via generalised Bernoulli numbers. -/
theorem LFunction_neg_nat {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ) :
    LFunction χ (-(k : ℂ)) = -(χ.genBernoulli (k + 1)) / (k + 1) := by sorry

end PadicLFunctions
