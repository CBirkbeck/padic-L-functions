/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Coleman.Theorem
import Mathlib.NumberTheory.Padics.AddChar

/-!
# Local unit groups of the cyclotomic tower (RJW §9, TeX 2471–2505)

The §9 notation that comes due at §11 (plan.md deferral): the local unit groups
`𝒰_n = 𝒪_{K_n}^×` and the principal units `𝒰_{n,1} = {u ∈ 𝒰_n : u ≡ 1 mod 𝔭_n}`
as subgroups of `ℂ_[p]ˣ` (the tower lives inside `ℂ_p`, decomposition R10.1/R11.7);
the `+`-subfield `K_n⁺ = ℚ_p(ξ + ξ⁻¹)` and the `⁺`-variants; the `ℤ_p`-power
structure `u^a` on principal units (RJW TeX 2494–2496: "`u^a = Σ (a choose k)(u−1)^k`
converges"); the group structure on the norm-compatible systems `𝒰_∞`
(`NormCompatUnits`, upgraded from `Mul`/`One` to `CommGroup`); and the towers
`𝒰_{∞,1} = lim←_{n≥1} 𝒰_{n,1}` and `𝒰⁺_{∞,1}` (RJW TeX 2503–2505).

The congruence `u ≡ 1 (mod 𝔭_n)` is rendered as `‖u − 1‖ < 1` (replan R11.6:
`𝔭_n` is the open unit ball of the unit-ball ring `O_n`). The `ℤ_p`-power is
mathlib's `PadicInt.addChar_of_value_at_one` applied to `r = u − 1` — literally the
source's binomial series.
-/

open scoped IntermediateField

namespace PadicLFunctions

namespace Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## The unit groups 𝒰_n and 𝒰_{n,1} (RJW TeX 2474, 2494) -/

/-- `𝒰_n = 𝒪_{K_n}^×`: the units of the integer ring of `K_n`, as a subgroup of
`ℂ_[p]ˣ` (a unit together with its inverse lies in `O_n`). RJW TeX 2474. -/
def localUnits (n : ℕ) : Subgroup ℂ_[p]ˣ where
  carrier := {u | (u : ℂ_[p]) ∈ O p n ∧ ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ∈ O p n}
  mul_mem' {u v} hu hv := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact mul_mem hu.1 hv.1
    · rw [mul_inv_rev, Units.val_mul]
      exact mul_mem hv.2 hu.2
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_one]; exact one_mem _
    · rw [inv_one, Units.val_one]; exact one_mem _
  inv_mem' {u} hu := by
    refine ⟨hu.2, ?_⟩
    rw [inv_inv]; exact hu.1

lemma mem_localUnits_iff {n : ℕ} {u : ℂ_[p]ˣ} :
    u ∈ localUnits p n
      ↔ (u : ℂ_[p]) ∈ O p n ∧ ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ∈ O p n :=
  Iff.rfl

/-- Units of `O_n` have norm exactly `1` (and conversely for elements of `K_n`). -/
lemma norm_eq_one_of_mem_localUnits {n : ℕ} {u : ℂ_[p]ˣ} (hu : u ∈ localUnits p n) :
    ‖(u : ℂ_[p])‖ = 1 := by
  have hu1 : ‖(u : ℂ_[p])‖ ≤ 1 := (Subring.mem_inf.1 hu.1).2
  have hu2 : ‖((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ ≤ 1 := (Subring.mem_inf.1 hu.2).2
  have hprod : ‖(u : ℂ_[p])‖ * ‖((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
    rw [← norm_mul, Units.mul_inv, norm_one]
  nlinarith [norm_nonneg (u : ℂ_[p]), norm_nonneg ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])]

/-- `𝒰_{n,1} = {u ∈ 𝒰_n : u ≡ 1 (mod 𝔭_n)}`: the principal units, with the
congruence rendered as `‖u − 1‖ < 1` (replan R11.6). RJW Eq. (`eq:U1`), TeX 2494. -/
def localUnitsOne (n : ℕ) : Subgroup ℂ_[p]ˣ where
  carrier := {u | u ∈ localUnits p n ∧ ‖(u : ℂ_[p]) - 1‖ < 1}
  mul_mem' {u v} hu hv := by
    refine ⟨mul_mem hu.1 hv.1, ?_⟩
    -- `uv − 1 = u·(v − 1) + (u − 1)`, dominated by the max of the two norms `< 1`
    have hkey : (↑(u * v) : ℂ_[p]) - 1 = (u : ℂ_[p]) * ((v : ℂ_[p]) - 1) + ((u : ℂ_[p]) - 1) := by
      rw [Units.val_mul]; ring
    rw [hkey]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hu.2)
    rw [norm_mul, norm_eq_one_of_mem_localUnits p hu.1, one_mul]
    exact hv.2
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    rw [Units.val_one, sub_self, norm_zero]
    exact one_pos
  inv_mem' {u} hu := by
    refine ⟨(localUnits p n).inv_mem hu.1, ?_⟩
    -- `u⁻¹ − 1 = u⁻¹·(1 − u)`, and `‖u⁻¹‖ = 1`, so the norm equals `‖u − 1‖ < 1`
    have hu0 : (u : ℂ_[p]) ≠ 0 := u.ne_zero
    have hkey : ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) - 1
        = ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (1 - (u : ℂ_[p])) := by
      rw [Units.val_inv_eq_inv_val]
      field_simp
    rw [hkey, norm_mul,
      norm_eq_one_of_mem_localUnits p ((localUnits p n).inv_mem hu.1), one_mul, norm_sub_rev]
    exact hu.2

lemma mem_localUnitsOne_iff {n : ℕ} {u : ℂ_[p]ˣ} :
    u ∈ localUnitsOne p n ↔ u ∈ localUnits p n ∧ ‖(u : ℂ_[p]) - 1‖ < 1 :=
  Iff.rfl

/-! ## The maximal totally real subfield K_n⁺ and the ⁺-variants (RJW TeX 2473–2475) -/

/-- `K_n⁺ = ℚ_p(ξ_{p^n} + ξ_{p^n}⁻¹)`: the "+"-subfield, rendered by its standard
concrete generator (the fixed points of `ξ ↦ ξ⁻¹`; the Galois characterisation is
§12 material). RJW TeX 2473. -/
noncomputable def KPlus (n : ℕ) : IntermediateField ℚ_[p] ℂ_[p] :=
  ℚ_[p]⟮zetaSys p n + (zetaSys p n)⁻¹⟯

lemma KPlus_le_K (n : ℕ) : KPlus p n ≤ K p n := by
  rw [KPlus, IntermediateField.adjoin_simple_le_iff]
  exact add_mem (zetaSys_mem_K p n) ((K p n).inv_mem (zetaSys_mem_K p n))

/-- `𝒰_n⁺ = 𝒪_{K_n⁺}^×`, realised as the `K_n⁺`-valued local units (a unit of `O_n`
lying in `K_n⁺` is a unit of `𝒪_{K_n⁺}`). RJW TeX 2474 with the X⁺-convention of
TeX 2498. -/
noncomputable def localUnitsPlus (n : ℕ) : Subgroup ℂ_[p]ˣ where
  carrier := {u | u ∈ localUnits p n ∧ (u : ℂ_[p]) ∈ KPlus p n}
  mul_mem' {u v} hu hv := by
    refine ⟨mul_mem hu.1 hv.1, ?_⟩
    rw [Units.val_mul]
    exact mul_mem hu.2 hv.2
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    rw [Units.val_one]
    exact one_mem _
  inv_mem' {u} hu := by
    refine ⟨(localUnits p n).inv_mem hu.1, ?_⟩
    rw [Units.val_inv_eq_inv_val]
    exact (KPlus p n).inv_mem hu.2

/-- `𝒰⁺_{n,1} = 𝒰_{n,1} ∩ 𝒰_n⁺` (RJW TeX 2494). -/
noncomputable def localUnitsOnePlus (n : ℕ) : Subgroup ℂ_[p]ˣ :=
  localUnitsOne p n ⊓ localUnitsPlus p n

/-! ## The ℤ_p-power structure on principal units (RJW TeX 2494–2496)

"The subsets `𝒰_{n,1}` and `𝒰⁺_{n,1}` are important as they have the structure of
`ℤ_p`-modules (indeed, if `u ∈ 𝒰_{n,1}` … and `a ∈ ℤ_p`, then
`u^a = Σ_{k≥0} (a choose k)(u−1)^k` converges)." -/

/-- The `ℤ_p`-power `y^a` of a `1`-unit `y` of `ℂ_[p]` (junk value `1` when
`‖y − 1‖ ≥ 1`): mathlib's continuous additive character `a ↦ (1 + (y−1))^a`
(`PadicInt.addChar_of_value_at_one`) — the source's binomial series. The instance
pack (`Algebra ℤ_[p] ℂ_[p]` etc.) is part of the implementing ticket. -/
noncomputable def zpPow (y : ℂ_[p]) (a : ℤ_[p]) : ℂ_[p] := by
  sorry

/-- On natural exponents, `zpPow` is the usual power (the source's
"`u^a` extends `u^k`"). -/
theorem zpPow_natCast {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) (k : ℕ) :
    zpPow p y (k : ℤ_[p]) = y ^ k := by
  sorry

/-- The character law `y^{a+b} = y^a·y^b`. -/
theorem zpPow_add {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) (a b : ℤ_[p]) :
    zpPow p y (a + b) = zpPow p y a * zpPow p y b := by
  sorry

/-- The power law `(y^a)^b = y^{ab}` (so the action is a `ℤ_[p]`-module action). -/
theorem zpPow_mul {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) (a b : ℤ_[p]) :
    zpPow p y (a * b) = zpPow p (zpPow p y a) b := by
  sorry

/-- `zpPow` stays in the `1`-unit ball: `‖y^a − 1‖ ≤ ‖y − 1‖ < 1`. -/
theorem norm_zpPow_sub_one_lt_one {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) (a : ℤ_[p]) :
    ‖zpPow p y a - 1‖ < 1 := by
  sorry

/-- Principal units are stable under `ℤ_p`-powers: membership in `𝒰_{n,1}` is
preserved (the limit stays in the closed subfield `K_n` and in the unit ball). -/
theorem zpPow_mem_localUnitsOne {n : ℕ} {u : ℂ_[p]ˣ} (hu : u ∈ localUnitsOne p n)
    (a : ℤ_[p]) :
    ∃ v : ℂ_[p]ˣ, (v : ℂ_[p]) = zpPow p (u : ℂ_[p]) a ∧ v ∈ localUnitsOne p n := by
  sorry

/-- **RJW TeX 2494–2496**: the `ℤ_p`-module structure on the (additivised)
principal-unit group `𝒰_{n,1}`. -/
noncomputable instance localUnitsOneModule (n : ℕ) :
    Module ℤ_[p] (Additive (localUnitsOne p n)) := by
  sorry

/-! ## The group 𝒰_∞ and the towers 𝒰_{∞,1}, 𝒰⁺_{∞,1} (RJW TeX 2503–2505) -/

namespace NormCompatUnits

variable {p}

/-- The inverse of a norm-compatible system: pointwise inverses (norm
compatibility from multiplicativity of the level norm). -/
noncomputable def inv (u : NormCompatUnits p) : NormCompatUnits p where
  elems n := (u.elems n)⁻¹
  mem n := by sorry
  inv_mem n := by sorry
  compat n hn := by sorry

noncomputable instance : Inv (NormCompatUnits p) := ⟨inv⟩

/-- `𝒰_∞` is a commutative group (RJW TeX 2503: the inverse limit of the unit
*groups*; the existing structure carried only `Mul`/`One`). -/
noncomputable instance : CommGroup (NormCompatUnits p) where
  mul_assoc := by sorry
  one_mul := by sorry
  mul_one := by sorry
  inv_mul_cancel := by sorry
  mul_comm := by sorry

end NormCompatUnits

/-- `𝒰_{∞,1} = lim←_{n≥1} 𝒰_{n,1}`: the norm-compatible systems through the
principal units (RJW Eq. (`eq:Uinfty 1`), TeX 2503; the `n ≥ 1` convention matches
the `compat` field's). -/
def unitsTower1 : Subgroup (NormCompatUnits p) where
  carrier := {u | ∀ n, 1 ≤ n → u.elems n ∈ localUnitsOne p n}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry

/-- `𝒰⁺_{∞,1} = lim←_{n≥1} 𝒰⁺_{n,1}` (RJW TeX 2504). -/
noncomputable def unitsTower1Plus : Subgroup (NormCompatUnits p) where
  carrier := {u | ∀ n, 1 ≤ n → u.elems n ∈ localUnitsOnePlus p n}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry

lemma unitsTower1Plus_le_unitsTower1 : unitsTower1Plus p ≤ unitsTower1 p := by
  sorry

end Coleman

end PadicLFunctions
