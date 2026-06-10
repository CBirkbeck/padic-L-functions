/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Topology.LocallyConstant.Basic
import PadicLFunctions.Coefficients

/-!
# Dirichlet characters as functions on `ℤ_p`, and Gauss sums (RJW §5.1)

A Dirichlet character `χ` of conductor `p^n` is "seen as a locally constant
character of `ℤ_p^×`" (RJW Thm 5.1, TeX 1620) — concretely, the function
`x ↦ χ (toZModPow n x)`, which vanishes on `pℤ_p` for `n ≥ 1`. Gauss sums
(RJW Def 5.2, TeX 1647–1651) are mathlib's `gaussSum χ e` at the additive
character attached to a primitive `p^n`-th root of unity; Rem 5.3(ii) is
mathlib's `gaussSum_mulShift_of_isPrimitive`, and Rem 5.3(i) at non-prime
level is `gaussSum_mul_gaussSum_inv` below (L5.1.5, a mathlib gap).
-/

open scoped Classical

namespace PadicLFunctions

variable {p : ℕ} [hp : Fact p.Prime]

section toContinuousMap

variable {R : Type*} [NormedCommRing R] {n : ℕ}

/-- L5.1.1: a Dirichlet character mod `p^n` as a continuous (indeed locally
constant) function `ℤ_[p] → R`, via reduction mod `p^n`. For `n ≥ 1` it
vanishes on `pℤ_[p]` (the character kills non-units).

Source (TeX 1620): "(seen as a locally constant character of `ℤ_p^×`, cf.
§`sec:dirichlet ideles`)". -/
noncomputable def _root_.DirichletCharacter.toContinuousMapZp
    (χ : DirichletCharacter R (p ^ n)) : C(ℤ_[p], R) :=
  ⟨fun x => χ (PadicInt.toZModPow n x), by sorry⟩

@[simp]
lemma DirichletCharacter.toContinuousMapZp_apply
    (χ : DirichletCharacter R (p ^ n)) (x : ℤ_[p]) :
    χ.toContinuousMapZp x = χ (PadicInt.toZModPow n x) := rfl

/-- For `n ≥ 1`, the function vanishes on `pℤ_[p]` (non-units reduce to
non-units mod `p^n`). Source: TeX 1752 "Since `χ` is 0 on `pℤ_p`". -/
lemma DirichletCharacter.toContinuousMapZp_eq_zero
    (χ : DirichletCharacter R (p ^ n)) (hn : 1 ≤ n) {x : ℤ_[p]}
    (hx : ¬IsUnit x) : χ.toContinuousMapZp x = 0 := by sorry

/-- Multiplicativity (both sides vanish off the units). -/
lemma DirichletCharacter.toContinuousMapZp_mul
    (χ : DirichletCharacter R (p ^ n)) (hn : 1 ≤ n) (x y : ℤ_[p]) :
    χ.toContinuousMapZp (x * y)
      = χ.toContinuousMapZp x * χ.toContinuousMapZp y := by sorry

lemma DirichletCharacter.isLocallyConstant_toContinuousMapZp
    (χ : DirichletCharacter R (p ^ n)) :
    IsLocallyConstant (χ.toContinuousMapZp : ℤ_[p] → R) := by sorry

/-- The values of a Dirichlet character (in a normed ring, ultrametric not
needed) have norm at most one: they are roots of unity or zero. -/
lemma DirichletCharacter.norm_toContinuousMapZp_le
    [NormOneClass R] [IsUltrametricDist R]
    (χ : DirichletCharacter R (p ^ n)) (x : ℤ_[p]) :
    ‖χ.toContinuousMapZp x‖ ≤ 1 := by sorry

end toContinuousMap

section gaussSum

variable {N : ℕ} [NeZero N] {R : Type*} [CommRing R] [IsDomain R]

/-- L5.1.5 (Rem 5.3(i) at general level; mathlib has the prime/field case
only): for `χ` a primitive Dirichlet character mod `N` and `e` a primitive
additive character of `ZMod N` into a domain,
`G(χ, e) · G(χ⁻¹, e⁻¹) = N`.

Source (TeX 1656, Rem 5.3(i)): "G(χ) G(χ⁻¹) = χ(−1) p^n" — the displayed
form equals this one after `e⁻¹ = e.mulShift (−1)` and Rem 5.3(ii) absorb
`χ(−1)`. Route (DS05 §4.3-style, 4 finite sums): expand `G(χ⁻¹, e⁻¹)`,
rewrite each summand by `gaussSum_mulShift_of_isPrimitive`, swap sums, and
collapse with primitive-character orthogonality `∑_b e(b·c) = N·δ_{c,0}`. -/
theorem gaussSum_mul_gaussSum_inv {χ : DirichletCharacter R N}
    (hχ : χ.IsPrimitive) {e : AddChar (ZMod N) R} (he : e.IsPrimitive) :
    gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = (N : R) := by sorry

end gaussSum

section gaussSumNorm

variable (L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L]
  [IsUltrametricDist L] [CompleteSpace L]

/-- For `η` primitive of conductor `D` coprime to `p` (and a primitive `D`-th
root of unity `ζ` in `L`), the Gauss sum has norm one — in particular it is a
unit of the integer ring.

Source (TeX 1798): "the Gauss sum is a `p`-adic unit (indeed, we have
`G(η)G(η⁻¹) = η(−1)D` and `D` is coprime to `p`)". Route: `‖G‖ ≤ 1` by the
ultrametric triangle inequality (root-of-unity values), and
`gaussSum_mul_gaussSum_inv` with `‖D‖ = 1` forces equality. -/
theorem norm_gaussSum_eq_one {D : ℕ} [NeZero D] {η : DirichletCharacter L D}
    (hη : η.IsPrimitive) (hD : ¬ (p : ℕ) ∣ D) {ζ : L}
    (hζ : IsPrimitiveRoot ζ D) :
    ‖gaussSum η (AddChar.zmodChar D (hζ.pow_eq_one))‖ = 1 := by sorry

end gaussSumNorm

end PadicLFunctions
