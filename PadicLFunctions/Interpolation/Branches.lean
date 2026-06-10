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
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
    ((PerfectionMap.id p
        (ℤ_[p] ⧸ maximalIdeal ℤ_[p])).equiv.toRingHom.toMonoidWithZeroHom).comp
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

/-- `ℤ_p` contains a primitive `(p−1)`-th root of unity: the Teichmüller lift
of a generator of `(ZMod p)ˣ` (the prime-to-`p` part of the roots of unity
needed for character orthogonality in the §5.2 determinacy). -/
theorem exists_primitiveRoot_card_sub_one :
    ∃ ζ : ℤ_[p], IsPrimitiveRoot ζ (p - 1) := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
  refine ⟨teichmullerZMod p ((g : ZMod p)), ?_, fun l hl => ?_⟩
  · exact teichmullerZMod_pow_card_sub_one p g.ne_zero
  · have htoZ : (g : ZMod p) ^ l = 1 := by
      have h := congrArg (toZMod (p := p)) hl
      rwa [map_pow, toZMod_teichmullerZMod, map_one] at h
    have hgl : g ^ l = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, htoZ, Units.val_one])
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hgl

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
    (angleUnit p x : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p])} := by
  have key : (angleUnit p x : ℤ_[p]) - 1
      = (((teichmuller p x)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
          * ((x : ℤ_[p]) - teichmullerFun p (x : ℤ_[p])) := by
    rw [← teichmuller_coe, mul_sub, Units.inv_mul, angleUnit, Units.val_mul]
  rw [key, ← neg_sub, mul_neg]
  exact neg_mem (Ideal.mul_mem_left _ _ (teichmullerFun_sub_self_mem p _))

lemma angleUnit_mul (x y : ℤ_[p]ˣ) :
    angleUnit p (x * y) = angleUnit p x * angleUnit p y := by
  simp only [angleUnit, map_mul]
  rw [mul_inv_rev, mul_comm (teichmuller p y)⁻¹ (teichmuller p x)⁻¹]
  exact mul_mul_mul_comm (teichmuller p x)⁻¹ (teichmuller p y)⁻¹ x y

/-- The decomposition `x = ω(x)·⟨x⟩` (RJW Def 5.15: "If `x ∈ ℤ_p^×`, then we
can write `x = ω(x)⟨x⟩`"). -/
lemma teichmuller_mul_angleUnit (x : ℤ_[p]ˣ) :
    teichmuller p x * angleUnit p x = x := mul_inv_cancel_left _ _

end angleBracket

section onePAdicPow

/-- Elements of `1 + pℤ_p` are topologically unipotent: `(y−1)^n → 0`. -/
lemma tendsto_pow_atTop_nhds_zero_of_mem_span {w : ℤ_[p]}
    (hw : w ∈ Ideal.span {(p : ℤ_[p])}) :
    Filter.Tendsto (w ^ ·) Filter.atTop (nhds 0) := by
  have h1 : ‖w‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ)) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow w 1).mpr (by simpa using hw)
  have h2 : (p : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
    rw [zpow_neg, Nat.cast_one, zpow_one, inv_lt_one_iff₀]
    exact .inr (by exact_mod_cast hp.1.one_lt)
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (h1.trans_lt h2)

/-- The ideal `pℤ_p` is closed (it is the closed ball of radius `p⁻¹`). -/
lemma isClosed_span_p : IsClosed {x : ℤ_[p] | x ∈ Ideal.span {(p : ℤ_[p])}} := by
  have hset : {x : ℤ_[p] | x ∈ Ideal.span {(p : ℤ_[p])}}
      = {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ))} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [PadicInt.norm_le_pow_iff_mem_span_pow x 1, pow_one]
  rw [hset]
  exact isClosed_le continuous_norm continuous_const

/-- L5.3.3: for `y ∈ 1 + pℤ_p` (witnessed by `hy`), the power function
`s ↦ y^s : ℤ_[p] → ℤ_[p]` — the unique continuous additive character with
value `y` at `1` (mathlib `PadicInt.addChar_of_value_at_one`).

Source (Lem 5.14, TeX 1892–1894) defines `x^s := exp(s·log x)`; the two agree
by uniqueness of continuous characters (recorded replan L5.3.3 — the exp/log
development is not in mathlib). -/
noncomputable def onePAdicPow (y : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    AddChar ℤ_[p] ℤ_[p] :=
  PadicInt.addChar_of_value_at_one (y - 1)
    (tendsto_pow_atTop_nhds_zero_of_mem_span p hy)

@[simp]
lemma onePAdicPow_apply_one (y : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    onePAdicPow p y hy 1 = y := by
  rw [show onePAdicPow p y hy = PadicInt.addChar_of_value_at_one (y - 1)
      (tendsto_pow_atTop_nhds_zero_of_mem_span p hy) from rfl,
    PadicInt.addChar_of_value_at_one_def]
  ring

@[simp]
lemma onePAdicPow_natCast (y : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])})
    (k : ℕ) : onePAdicPow p y hy (k : ℤ_[p]) = y ^ k := by
  rw [show ((k : ℤ_[p])) = k • (1 : ℤ_[p]) from (nsmul_one k).symm,
    AddChar.map_nsmul_eq_pow, onePAdicPow_apply_one]

lemma continuous_onePAdicPow (y : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    Continuous (onePAdicPow p y hy) :=
  PadicInt.continuous_addChar_of_value_at_one _

lemma onePAdicPow_sub_one_mem (y : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])})
    (s : ℤ_[p]) :
    onePAdicPow p y hy s - 1 ∈ Ideal.span {(p : ℤ_[p])} := by
  have hclosed : IsClosed {x : ℤ_[p] |
      onePAdicPow p y hy x - 1 ∈ Ideal.span {(p : ℤ_[p])}} :=
    (isClosed_span_p p).preimage
      ((continuous_onePAdicPow p y hy).sub continuous_const)
  have hnat : Set.range ((↑) : ℕ → ℤ_[p]) ⊆ {x : ℤ_[p] |
      onePAdicPow p y hy x - 1 ∈ Ideal.span {(p : ℤ_[p])}} := by
    rintro _ ⟨k, rfl⟩
    have hq : Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p])}) y = 1 := by
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hy
    simp only [Set.mem_setOf_eq, onePAdicPow_natCast]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, hq, one_pow,
      sub_self]
  have huniv : Set.univ ⊆ {x : ℤ_[p] |
      onePAdicPow p y hy x - 1 ∈ Ideal.span {(p : ℤ_[p])}} := by
    rw [← (PadicInt.denseRange_natCast (p := p)).closure_eq]
    exact closure_minimal hnat hclosed
  exact huniv (Set.mem_univ s)

/-- `y·z − 1 ∈ pℤ_p` whenever `y − 1, z − 1 ∈ pℤ_p`: `1 + pℤ_p` is closed
under multiplication. -/
lemma mul_sub_one_mem {y z : ℤ_[p]} (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])})
    (hz : z - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    y * z - 1 ∈ Ideal.span {(p : ℤ_[p])} := by
  have key : y * z - 1 = (y - 1) * z + (z - 1) := by ring
  rw [key]
  exact add_mem (Ideal.mul_mem_right _ _ hy) hz

/-- Multiplicativity in the base. -/
lemma onePAdicPow_mul_base (y z : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])})
    (hz : z - 1 ∈ Ideal.span {(p : ℤ_[p])}) (s : ℤ_[p]) :
    onePAdicPow p (y * z) (mul_sub_one_mem p hy hz) s
      = onePAdicPow p y hy s * onePAdicPow p z hz s := by
  have hcont : Continuous (onePAdicPow p y hy * onePAdicPow p z hz) :=
    ((continuous_onePAdicPow p y hy).mul (continuous_onePAdicPow p z hz)).congr
      fun a => (AddChar.mul_apply _ _ _).symm
  have heq : onePAdicPow p y hy * onePAdicPow p z hz
      = onePAdicPow p (y * z) (mul_sub_one_mem p hy hz) := by
    refine PadicInt.eq_addChar_of_value_at_one _ hcont ?_
    rw [AddChar.mul_apply, onePAdicPow_apply_one, onePAdicPow_apply_one]
    ring
  have hs := DFunLike.congr_fun heq s
  rw [AddChar.mul_apply] at hs
  exact hs.symm

/-- Uniqueness of the decomposition: an element of `μ_{p−1} ∩ (1+pℤ_p)` is `1`.
For `p = 2` this is degenerate-but-true (`p − 1 = 1`); the substantive odd-`p`
case rests on `(1+pℤ_p)` being torsion-free for prime-to-`p` exponents
(RJW TeX 1900: "Recall that we assume `p` to be odd"). Proved through the
character `s ↦ u^s`: `u^{(p−1)s}` is the trivial character by uniqueness, and
evaluating at `(p−1)⁻¹` gives `u = 1`. -/
lemma eq_one_of_pow_card_sub_one {u : ℤ_[p]ˣ} (hu : u ^ (p - 1) = 1)
    (hmem : (u : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p])}) : u = 1 := by
  haveI : Fact (1 < p) := ⟨hp.1.one_lt⟩
  -- `p − 1` is a unit of `ℤ_p` (its residue is `−1 ≠ 0`)
  have hc : IsUnit ((p - 1 : ℕ) : ℤ_[p]) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker,
      map_natCast, Nat.cast_sub hp.1.one_le, ZMod.natCast_self, zero_sub, Nat.cast_one]
    simp
  obtain ⟨c, hc'⟩ := hc
  -- the character `s ↦ u^{(p−1)s}` is trivial…
  have h0 : Filter.Tendsto ((0 : ℤ_[p]) ^ ·) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by simp)
  have hshift : Continuous ((onePAdicPow p (u : ℤ_[p]) hmem).mulShift
      ((p - 1 : ℕ) : ℤ_[p])) :=
    ((continuous_onePAdicPow p _ hmem).comp (continuous_const.mul continuous_id)).congr
      fun a => AddChar.mulShift_apply.symm
  have hlam : (onePAdicPow p (u : ℤ_[p]) hmem).mulShift ((p - 1 : ℕ) : ℤ_[p])
      = PadicInt.addChar_of_value_at_one 0 h0 := by
    refine PadicInt.eq_addChar_of_value_at_one _ hshift ?_
    rw [AddChar.mulShift_apply, mul_one, onePAdicPow_natCast,
      ← Units.val_pow_eq_pow_val, hu, Units.val_one, add_zero]
  have htriv : (1 : AddChar ℤ_[p] ℤ_[p]) = PadicInt.addChar_of_value_at_one 0 h0 := by
    refine PadicInt.eq_addChar_of_value_at_one _ ?_ (by rw [AddChar.one_apply, add_zero])
    exact continuous_const.congr fun a => (AddChar.one_apply _).symm
  -- …so evaluating it at `(p−1)⁻¹` gives `u = u^{(p−1)(p−1)⁻¹} = 1`
  have heval := DFunLike.congr_fun (hlam.trans htriv.symm) ((c⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
  rw [AddChar.mulShift_apply, ← hc', Units.mul_inv, onePAdicPow_apply_one,
    AddChar.one_apply] at heval
  exact Units.ext (by rw [heval, Units.val_one])

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
