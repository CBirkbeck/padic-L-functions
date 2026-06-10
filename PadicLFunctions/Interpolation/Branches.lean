/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.NumberTheory.Padics.AddChar
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Teichmuller
import PadicLFunctions.KubotaLeopoldt.ZetaP

/-!
# Branches of the p-adic zeta function (RJW §5.3, TeX 1885–1979)

For odd `p`, the unit group decomposes as `ℤ_p^× ≅ μ_{p−1} × (1+pℤ_p)` via the
Teichmüller character `ω` and `⟨x⟩ := ω(x)⁻¹x` (RJW Def 5.15). For
`y ∈ 1+pℤ_p` and `s ∈ ℤ_p` the power `y^s` is the unique continuous character
`s ↦ y^s` with value `y` at `1` — built on mathlib's
`PadicInt.addChar_of_value_at_one` (the source defines it as `exp(s·log x)`,
Lem 5.14; `p`-adic exp/log are not yet in mathlib, and the two definitions
agree by uniqueness of continuous characters — recorded replan, decomposition
L5.3.3). The `i`-th branch of the Kubota–Leopoldt `p`-adic L-function is
`ζ_{p,i}(s) = ∫_{ℤ_p^×} ω(x)^i⟨x⟩^{1−s}·ζ_p` (Def 5.16) with interpolation
`ζ_{p,i}(1−k) = (1−p^{k−1})ζ(1−k)` for `k ≡ i mod (p−1)` (Thm 5.17).
-/

open Filter Topology

namespace PadicInt

variable (p : ℕ) [hp : Fact p.Prime]

section teichmuller

open IsLocalRing

/-- `ℤ_[p] ⧸ maximalIdeal ℤ_[p] ≃+* ZMod p`: mathlib's `PadicInt.residueField`
(whose codomain `IsLocalRing.ResidueField ℤ_[p]` is definitionally this
quotient), restated on the raw quotient to avoid typeclass-resolution friction
through the wrapper. -/
noncomputable def maximalIdealQuotientEquivZMod :
    ℤ_[p] ⧸ maximalIdeal ℤ_[p] ≃+* ZMod p :=
  PadicInt.residueField

instance : CharP (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) p :=
  charP_of_injective_ringHom (f := (maximalIdealQuotientEquivZMod p).symm.toRingHom)
    (maximalIdealQuotientEquivZMod p).symm.injective p

instance : Finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) :=
  Finite.of_equiv _ (maximalIdealQuotientEquivZMod p).symm.toEquiv

/-- L5.3.1 (residue form): the Teichmüller map `ω : ZMod p →*₀ ℤ_[p]`, sending
a nonzero residue to the unique `(p−1)`-th root of unity reducing to it, and
`0` to `0`. Built from mathlib's `Perfection.teichmuller₀` through the
identification of `ZMod p` with (the perfection of) the residue field of
`ℤ_[p]`; mathlib's construction is the adic limit of `p^n`-th powers of lifts
— RJW Def 5.15's `lim_n x^{p^n}`. -/
noncomputable def teichmullerZMod : ZMod p →*₀ ℤ_[p] :=
  (Perfection.teichmuller₀ p (maximalIdeal ℤ_[p])).comp <|
    ((PerfectionMap.id p (ℤ_[p] ⧸ maximalIdeal ℤ_[p])).equiv.toRingHom.toMonoidWithZeroHom).comp
      (maximalIdealQuotientEquivZMod p).symm.toRingHom.toMonoidWithZeroHom

/-- `ω(a) ≡ a (mod p)`: the Teichmüller lift is a section of reduction. -/
@[simp]
lemma toZMod_teichmullerZMod (a : ZMod p) : toZMod (teichmullerZMod p a) = a := by
  change toZMod
    (Perfection.teichmuller₀ p (maximalIdeal ℤ_[p])
      ((PerfectionMap.id p (ℤ_[p] ⧸ maximalIdeal ℤ_[p])).equiv
        ((maximalIdealQuotientEquivZMod p).symm a))) = a
  rw [PadicInt.toZMod_eq_residueField_comp_residue, RingHom.comp_apply]
  change PadicInt.residueField (Ideal.Quotient.mk _ _) = a
  rw [Perfection.mk_teichmuller₀, PerfectionMap.comp_equiv]
  exact (maximalIdealQuotientEquivZMod p).apply_symm_apply a

lemma teichmullerZMod_pow_card_sub_one {a : ZMod p} (ha : a ≠ 0) :
    teichmullerZMod p a ^ (p - 1) = 1 := by
  rw [← map_pow, ZMod.pow_card_sub_one_eq_one ha, map_one]

/-- L5.3.1: the Teichmüller lift `ω(x) ∈ ℤ_[p]` of the reduction of `x` mod `p`
(RJW Def 5.15: "ω(x) ≔ Teichmüller lift of the reduction modulo p of x");
through `teichmullerZMod` this is the limit `lim_n x^{p^n}` of the source. -/
noncomputable def teichmullerFun (x : ℤ_[p]) : ℤ_[p] := teichmullerZMod p (toZMod x)

@[simp]
lemma teichmullerFun_pow_card_sub_one (x : ℤ_[p]ˣ) :
    teichmullerFun p (x : ℤ_[p]) ^ (p - 1) = 1 := by
  haveI : Fact (1 < p) := ⟨hp.1.one_lt⟩
  exact teichmullerZMod_pow_card_sub_one p (x.isUnit.map toZMod).ne_zero

lemma teichmullerFun_sub_self_mem (x : ℤ_[p]) :
    teichmullerFun p x - x ∈ Ideal.span {(p : ℤ_[p])} := by
  rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub,
    teichmullerFun, toZMod_teichmullerZMod, sub_self]

lemma teichmullerFun_mul (x y : ℤ_[p]) :
    teichmullerFun p (x * y) = teichmullerFun p x * teichmullerFun p y := by
  simp [teichmullerFun]

/-- `ω` is locally constant: it only depends on `x mod p`. -/
lemma teichmullerFun_eq_of_sub_mem {x y : ℤ_[p]}
    (h : x - y ∈ Ideal.span {(p : ℤ_[p])}) :
    teichmullerFun p x = teichmullerFun p y := by
  have hxy : toZMod x = toZMod y := by
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZMod,
      PadicInt.maximalIdeal_eq_span_p]
    exact h
  rw [teichmullerFun, teichmullerFun, hxy]

/-- `ω(x)` is a unit for `x` a unit. -/
lemma isUnit_teichmullerFun (x : ℤ_[p]ˣ) :
    IsUnit (teichmullerFun p (x : ℤ_[p])) :=
  IsUnit.of_pow_eq_one (teichmullerFun_pow_card_sub_one p x)
    (Nat.sub_ne_zero_of_lt hp.1.one_lt)

/-- L5.3.1 (packaged): the Teichmüller character `ω : ℤ_[p]ˣ →* ℤ_[p]ˣ`. -/
noncomputable def teichmuller : ℤ_[p]ˣ →* ℤ_[p]ˣ where
  toFun x := (isUnit_teichmullerFun p x).unit
  map_one' := by
    ext
    simp [teichmullerFun]
  map_mul' x y := by
    ext
    simp [teichmullerFun_mul]

@[simp]
lemma teichmuller_coe (x : ℤ_[p]ˣ) :
    (teichmuller p x : ℤ_[p]) = teichmullerFun p (x : ℤ_[p]) := rfl

end teichmuller

section angleBracket

/-- L5.3.2: the projection `⟨·⟩ : ℤ_[p]ˣ → 1 + pℤ_[p]`, `⟨x⟩ = ω(x)⁻¹·x`
(RJW Def 5.15). Valued in units; the `1 + pℤ_p` membership is the lemma
below. -/
noncomputable def angleUnit (x : ℤ_[p]ˣ) : ℤ_[p]ˣ := (teichmuller p x)⁻¹ * x

lemma angleUnit_sub_one_mem (x : ℤ_[p]ˣ) :
    (angleUnit p x : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p])} := by sorry

lemma angleUnit_mul (x y : ℤ_[p]ˣ) :
    angleUnit p (x * y) = angleUnit p x * angleUnit p y := by sorry

/-- The decomposition `x = ω(x)·⟨x⟩` (RJW Def 5.15: "If `x ∈ ℤ_p^×`, then we
can write `x = ω(x)⟨x⟩`"). -/
lemma teichmuller_mul_angleUnit (x : ℤ_[p]ˣ) :
    teichmuller p x * angleUnit p x = x := by sorry

/-- Uniqueness of the decomposition: an element of `μ_{p−1} ∩ (1+pℤ_p)` is `1`.
For `p = 2` this is degenerate-but-true (`p − 1 = 1`); the substantive odd-`p`
case rests on `(1+pℤ_p)` being torsion-free, where `p ≠ 2` is essential
(RJW TeX 1900: "Recall that we assume `p` to be odd"). -/
lemma eq_one_of_pow_card_sub_one {u : ℤ_[p]ˣ} (hu : u ^ (p - 1) = 1)
    (hmem : (u : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p])}) : u = 1 := by sorry

end angleBracket

section onePAdicPow

/-- L5.3.3: for `y ∈ 1 + pℤ_p` (witnessed by `hy`), the power function
`s ↦ y^s : ℤ_[p] → ℤ_[p]` — the unique continuous additive character with
value `y` at `1` (mathlib `PadicInt.addChar_of_value_at_one`).

Source (Lem 5.14, TeX 1892–1894) defines `x^s := exp(s·log x)`; the two agree
by uniqueness of continuous characters (recorded replan L5.3.3 — the exp/log
development is not in mathlib). -/
noncomputable def onePAdicPow (y : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    AddChar ℤ_[p] ℤ_[p] := sorry

@[simp]
lemma onePAdicPow_natCast (y : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])})
    (k : ℕ) : onePAdicPow p y hy (k : ℤ_[p]) = y ^ k := by sorry

lemma onePAdicPow_sub_one_mem (y : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])})
    (s : ℤ_[p]) :
    onePAdicPow p y hy s - 1 ∈ Ideal.span {(p : ℤ_[p])} := by sorry

lemma continuous_onePAdicPow (y : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    Continuous (onePAdicPow p y hy) := by sorry

/-- Multiplicativity in the base. -/
lemma onePAdicPow_mul_base (y z : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])})
    (hz : z - 1 ∈ Ideal.span {(p : ℤ_[p])}) (s : ℤ_[p]) :
    onePAdicPow p (y * z)
        (by simpa using sorry)
        s
      = onePAdicPow p y hy s * onePAdicPow p z hz s := by sorry

end onePAdicPow

end PadicInt

namespace PadicLFunctions

open PadicInt

variable (p : ℕ) [hp : Fact p.Prime]

/-- L5.3.4: the continuous character `x ↦ ω(x)^i·⟨x⟩^s` on `ℤ_[p]ˣ`, as a
continuous map into `ℤ_[p]` (RJW TeX 1907–1910). -/
noncomputable def branchChar (i : ℕ) (s : ℤ_[p]) : C(ℤ_[p]ˣ, ℤ_[p]) :=
  ⟨fun x => (teichmuller p x : ℤ_[p]) ^ i
      * onePAdicPow p (angleUnit p x : ℤ_[p]) (angleUnit_sub_one_mem p x) s,
    by sorry⟩

/-- On the congruence class `k ≡ i mod (p−1)`, the branch character at the
integer `s = k` is `x^k` (RJW TeX 1919: "the character `x^k` can be written in
the form `ω(x)^i⟨x⟩^k` if and only if `k ≡ i mod (p−1)`"; we need the "if").
`PadicMeasure.unitsPowCM` is §4's `x^k`-on-units. -/
lemma branchChar_natCast {i k : ℕ} (hik : (k : ZMod (p - 1)) = (i : ZMod (p - 1))) :
    branchChar p i (k : ℤ_[p]) = PadicMeasure.unitsPowCM p k := by sorry

/-- L5.3.5/L5.3.6: the `i`-th branch of the Kubota–Leopoldt `p`-adic
L-function: `ζ_{p,i}(s) = ∫_{ℤ_p^×} ω(x)^i⟨x⟩^{1−s}·ζ_p`
(RJW Def 5.16, TeX 1912–1918), realised through the pseudo-measure pairing at
the §4 topological generator (junk value where the pairing degenerates, i.e.
at the pole `(i,s) = (0,1)` — RJW's "meromorphic"). -/
noncomputable def zetaPBranch (hp2 : p ≠ 2) (i : ℕ) (s : ℤ_[p]) : ℚ_[p] := sorry

/-- **RJW Theorem 5.17** (`thm:kubota leopoldt analytic`, TeX 1921–1924):
"For all `k ≥ 1` with `k ≡ i mod (p−1)`, we have
`ζ_{p,i}(1−k) = (1−p^{k−1})ζ(1−k)`." The right-hand side is §4's rational
`zetaNeg (k−1)` (the same value object as `PadicMeasure.kubotaLeopoldt`). -/
theorem zetaPBranch_interpolation (hp2 : p ≠ 2) {i k : ℕ} (hk : 0 < k)
    (hik : (k : ZMod (p - 1)) = (i : ZMod (p - 1))) :
    zetaPBranch p hp2 i ((1 : ℤ_[p]) - (k : ℤ_[p]))
      = (1 - (p : ℚ_[p]) ^ ((k : ℤ) - 1)) * ((zetaNeg (k - 1) : ℚ) : ℚ_[p]) := by sorry

end PadicLFunctions
