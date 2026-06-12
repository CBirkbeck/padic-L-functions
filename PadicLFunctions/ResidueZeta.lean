/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.Basic
import PadicLFunctions.Interpolation.Branches
import PadicLFunctions.ValuesAtOne

/-!
# The residue of ζ_p at s = 1 (RJW §7, TeX 2181–2360)

**RJW Theorem 7.1** (`thm:residue`, TeX 2187–2194): for `i ∈ {1,…,p−1}`,
(i) if `i ≠ p−1` then `ζ_{p,i}` is analytic at `s = 1` (here: continuous —
the denominator never vanishes), and (ii) `ζ_{p,p−1}` has a simple pole at
`s = 1` with residue `1 − p⁻¹` (here: the topological limit
`lim_{s→1, s≠1} (s−1)·ζ_{p,p−1}(s) = 1 − p⁻¹`).

Route (decomposition R7; replans recorded there): `zetaPBranch` is
literally RJW's Eqtmp2 quotient, so the work is (a) the denominator
analysis through the T523 exp/log bridge (`g(s) = ⟨a⟩^{1−s} − 1`,
`(s−1)⁻¹g(s) → −log⟨a⟩`), (b) continuity of the numerator pairing via the
`p^m`-congruence Lipschitz bound, and (c) the mass
`∫x⁻¹μ_a = −(1−p⁻¹)·log_p(a)` by the §6 c₀-design applied to the explicit
antiderivative `F̃_a = log(T/(1+T) · (1+T)^a/((1+T)^a−1))` (TeX 2268),
with the `ξ ∈ μ_p`-machinery run in a field `K ⊇ ℚ_p(μ_p)` (ℂ_p) and
descended by injectivity. RJW's Lemma 7.4 (`ℛ⁺`-membership) is not needed
on this route.
-/

open PowerSeries

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]

section expTail

variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
  [IsUltrametricDist L] [CompleteSpace L]

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- Per-term quadratic bound: for `n ≥ 2`, the `n`-th exponential term is
`≤ p·‖w‖²` on the convergence ball (compared at the `(p−1)`-power level). -/
private lemma norm_factorial_inv_smul_pow_le_quad {w : L} (hw : InExpBall p w)
    {n : ℕ} (hn : 2 ≤ n) :
    ‖(n.factorial : ℚ_[p])⁻¹ • w ^ n‖ ≤ (p : ℝ) * ‖w‖ ^ 2 := by
  have hp1 : 0 < p - 1 := by have := hp.out.one_lt; omega
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hT0 : 0 ≤ (p : ℝ) * ‖w‖ ^ (p - 1) := by positivity
  have hT1 : (p : ℝ) * ‖w‖ ^ (p - 1) < 1 :=
    calc (p : ℝ) * ‖w‖ ^ (p - 1) < (p : ℝ) * (p : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_left hw hppos
      _ = 1 := mul_inv_cancel₀ hppos.ne'
  -- power-level comparison `‖term‖^{p−1} ≤ (p·‖w‖²)^{p−1}`
  have hpow : ‖(n.factorial : ℚ_[p])⁻¹ • w ^ n‖ ^ (p - 1)
      ≤ ((p : ℝ) * ‖w‖ ^ 2) ^ (p - 1) := by
    calc ‖(n.factorial : ℚ_[p])⁻¹ • w ^ n‖ ^ (p - 1)
        ≤ ‖w‖ ^ (p - 1) * ((p : ℝ) * ‖w‖ ^ (p - 1)) ^ (n - 1) :=
          norm_factorial_inv_smul_pow_le p w (by omega)
      _ = ‖w‖ ^ (p - 1)
            * (((p : ℝ) * ‖w‖ ^ (p - 1)) ^ (n - 2)
              * ((p : ℝ) * ‖w‖ ^ (p - 1))) := by
          rw [← pow_succ, show n - 2 + 1 = n - 1 from by omega]
      _ ≤ ‖w‖ ^ (p - 1) * (1 * ((p : ℝ) * ‖w‖ ^ (p - 1))) := by
          gcongr
          exact pow_le_one₀ hT0 hT1.le
      _ = (p : ℝ) * (‖w‖ ^ (p - 1)) ^ 2 := by ring
      _ ≤ (p : ℝ) ^ (p - 1) * (‖w‖ ^ (p - 1)) ^ 2 := by
          gcongr
          · exact le_self_pow₀ (by exact_mod_cast hp.out.one_le) (by omega)
      _ = ((p : ℝ) * ‖w‖ ^ 2) ^ (p - 1) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 2 (p - 1)]
  exact le_of_pow_le_pow_left₀ (by omega) (by positivity) hpow

/-- R7.1a: the quadratic tail of the exponential —
`‖exp w − 1 − w‖ ≤ p·‖w‖²` on the convergence ball (the `n ≥ 2` terms at
the `(p−1)`-power level). -/
theorem norm_padicExp_sub_one_sub_self_le {w : L} (hw : InExpBall p w) :
    ‖padicExp p w - 1 - w‖ ≤ (p : ℝ) * ‖w‖ ^ 2 := by
  have hsd := summable_padicExp_terms p hw
  -- peel the `n = 0` and `n = 1` terms
  have hdiff : padicExp p w - 1 - w
      = ∑' n : ℕ, ((n + 1 + 1 : ℕ).factorial : ℚ_[p])⁻¹ • w ^ (n + 1 + 1) := by
    rw [padicExp, hsd.tsum_eq_zero_add,
      ((summable_nat_add_iff 1).mpr hsd).tsum_eq_zero_add]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
      zero_add, Nat.factorial_one, pow_one]
    ring
  rw [hdiff]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le
    fun n => norm_factorial_inv_smul_pow_le_quad p hw (by omega)

end expTail

section character

/-- R7.1b: the character is a norm isometry in the exponent —
`‖y^t − 1‖ = ‖t‖·‖y−1‖` for `y ∈ 1+pℤ_p` (via the T523 exp/log bridge:
`y^t = exp(t·log y)` and `‖exp w − 1‖ = ‖w‖`, `‖log y‖ = ‖y−1‖`). -/
theorem norm_onePAdicPow_sub_one (hp2 : p ≠ 2) {y : ℤ_[p]}
    (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) (t : ℤ_[p]) :
    ‖(PadicInt.onePAdicPow p y hy t : ℤ_[p]) - 1‖ = ‖t‖ * ‖y - 1‖ := by
  set ℓ : ℤ_[p] := pZpLog p y with hℓ
  have hℓmem : ℓ ∈ Ideal.span {(p : ℤ_[p])} := pZpLog_mem p hp2 hy
  have htℓmem : t * ℓ ∈ Ideal.span {(p : ℤ_[p])} := Ideal.mul_mem_left _ _ hℓmem
  -- the bridge `y^t = exp(t·log y)`
  rw [← padicExp_smul_padicLog_eq_onePAdicPow p hp2 hy t, ← hℓ,
    PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one,
    pZpExp_coe p hp2 htℓmem,
    norm_padicExp_sub_one (L := ℚ_[p]) p (inExpBall_of_mem_span p hp2 htℓmem),
    PadicInt.coe_mul, norm_mul, ← PadicInt.norm_def, ← PadicInt.norm_def]
  -- `‖log y‖ = ‖y − 1‖`
  congr 1
  have hball : InExpBall p ((y : ℚ_[p]) - 1) := by
    rw [show ((y : ℚ_[p]) - 1) = ((y - 1 : ℤ_[p]) : ℚ_[p]) by
      rw [PadicInt.coe_sub, PadicInt.coe_one]]
    exact inExpBall_of_mem_span p hp2 hy
  rw [hℓ, PadicInt.norm_def, pZpLog_coe p hp2 hy, norm_padicLog (L := ℚ_[p]) p hball,
    ← PadicInt.coe_one, ← PadicInt.coe_sub, ← PadicInt.norm_def]

/-- R7.2a: the Teichmüller value of a topological generator is a primitive
`(p−1)`-th root of unity (its reduction generates `(ZMod p)ˣ`). -/
theorem teichmuller_isPrimitiveRoot {u : ℤ_[p]ˣ}
    (hgen : ∀ n : ℕ, Subgroup.zpowers (PadicMeasure.unitsToZModPow p n u)
      = ⊤) :
    IsPrimitiveRoot (PadicInt.teichmuller p u) (p - 1) := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  rw [IsPrimitiveRoot.iff_orderOf]
  -- `ω(u)^{p−1} = 1`, so `orderOf ω(u) ∣ p−1`
  have hpow : (PadicInt.teichmuller p u) ^ (p - 1) = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, PadicInt.teichmuller_coe,
      PadicInt.teichmullerFun_pow_card_sub_one, Units.val_one])
  have hdvd1 : orderOf (PadicInt.teichmuller p u) ∣ p - 1 :=
    orderOf_dvd_of_pow_eq_one hpow
  -- the level-1 reduction `g := unitsToZModPow p 1 u` generates, so `orderOf g = p−1`
  have ho1 : orderOf (PadicMeasure.unitsToZModPow p 1 u) = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers fun x => hgen 1 ▸ Subgroup.mem_top x,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one,
      Nat.totient_prime hp.out]
  -- `ω(u)` reduces to the same residue as `u` mod `p`, so `g = unitsToZModPow p 1 ω(u)`
  have hred : PadicMeasure.unitsToZModPow p 1 (PadicInt.teichmuller p u)
      = PadicMeasure.unitsToZModPow p 1 u := by
    refine Units.ext ?_
    rw [PadicMeasure.unitsToZModPow_coe, PadicMeasure.unitsToZModPow_coe,
      PadicInt.teichmuller_coe, ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker,
      PadicInt.ker_toZModPow, pow_one]
    exact PadicInt.teichmullerFun_sub_self_mem p u
  -- hence `(p−1) = orderOf g ∣ orderOf ω(u)`
  have hdvd2 : p - 1 ∣ orderOf (PadicInt.teichmuller p u) := by
    rw [← ho1, ← hred]
    exact orderOf_map_dvd _ _
  exact Nat.dvd_antisymm hdvd1 hdvd2

/-- For `0 < i < p−1` the reduction `ω(u)^i ≢ 1 mod p`, so `‖ω(u)^i − 1‖ = 1`
(the Teichmüller value has exact order `p−1` by `teichmuller_isPrimitiveRoot`). -/
private lemma norm_teichmuller_pow_sub_one_eq_one {u : ℤ_[p]ˣ}
    (hgen : ∀ n : ℕ, Subgroup.zpowers (PadicMeasure.unitsToZModPow p n u) = ⊤)
    {i : ℕ} (hi0 : 0 < i) (hi : i < p - 1) :
    ‖(PadicInt.teichmuller p u : ℤ_[p]) ^ i - 1‖ = 1 := by
  -- `(toZMod u)^i ≠ 1` (else `(p−1) ∣ i`, impossible for `0 < i < p−1`)
  have hred : PadicInt.toZMod ((PadicInt.teichmuller p u : ℤ_[p]) ^ i) ≠ 1 := by
    rw [map_pow, PadicInt.teichmuller_coe, PadicInt.teichmullerFun,
      PadicInt.toZMod_teichmullerZMod]
    intro h
    -- lift `(toZMod u)^i = 1` back to the units level through the section ω
    have hu1 : (PadicInt.teichmuller p u) ^ i = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, PadicInt.teichmuller_coe,
        PadicInt.teichmullerFun, ← map_pow, h, map_one, Units.val_one])
    have hdvd : p - 1 ∣ i := by
      rw [(teichmuller_isPrimitiveRoot p hgen).eq_orderOf]
      exact orderOf_dvd_of_pow_eq_one hu1
    exact absurd (Nat.le_of_dvd hi0 hdvd) (by omega)
  -- nonzero reduction ⟺ norm one
  have hnotdvd : ¬ ((p : ℤ_[p]) ∣ ((PadicInt.teichmuller p u : ℤ_[p]) ^ i - 1)) := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
    exact hred
  have hlt : ¬ (‖(PadicInt.teichmuller p u : ℤ_[p]) ^ i - 1‖ < 1) :=
    fun h => hnotdvd ((PadicInt.norm_lt_one_iff_dvd _).mp h)
  exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp hlt)

/-- R7.2b: for `0 < i < p−1` the branch denominator never vanishes —
`‖ω(u)^i − 1‖ = 1` beats `‖⟨u⟩^{1−s} − 1‖ < 1` (ultrametric isoceles);
this is RJW's Lemma 7.2(i) strengthened from `s = 1` to all `s`. -/
theorem branch_denom_ne_zero {u : ℤ_[p]ˣ}
    (hgen : ∀ n : ℕ, Subgroup.zpowers (PadicMeasure.unitsToZModPow p n u)
      = ⊤)
    {i : ℕ} (hi0 : 0 < i) (hi : i < p - 1) (s : ℤ_[p]) :
    (((branchChar p i s u : ℤ_[p])) : ℚ_[p]) - 1 ≠ 0 := by
  set ω : ℤ_[p] := (PadicInt.teichmuller p u : ℤ_[p]) with hω
  set A : ℤ_[p] := PadicInt.onePAdicPow p (PadicInt.angleUnit p u : ℤ_[p])
    (PadicInt.angleUnit_sub_one_mem p u) s with hA
  -- the value `V = ω^i·A`
  have hV : (branchChar p i s u : ℤ_[p]) = ω ^ i * A := by
    rw [branchChar_apply]
  -- `‖ω^i − 1‖ = 1`
  have hωi : ‖ω ^ i - 1‖ = 1 := norm_teichmuller_pow_sub_one_eq_one p hgen hi0 hi
  -- `‖A − 1‖ < 1`
  have hAlt : ‖A - 1‖ < 1 := by
    have hmem : A - 1 ∈ Ideal.span {(p : ℤ_[p])} :=
      PadicInt.onePAdicPow_sub_one_mem p _ _ s
    exact (PadicInt.norm_lt_one_iff_dvd _).mpr (Ideal.mem_span_singleton.mp hmem)
  -- `‖ω^i‖ = 1`
  have hωnorm : ‖ω ^ i‖ = 1 := by
    rw [hω, ← Units.val_pow_eq_pow_val]
    exact PadicInt.norm_units _
  -- isoceles: `‖V − 1‖ = max ‖ω^i·A − ω^i‖ ‖ω^i − 1‖ = 1`
  have hlt : ‖ω ^ i * A - ω ^ i‖ < ‖ω ^ i - 1‖ := by
    rw [show ω ^ i * A - ω ^ i = ω ^ i * (A - 1) from by ring, norm_mul, hωnorm,
      one_mul, hωi]
    exact hAlt
  have hkey := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt hlt)
  rw [show ω ^ i * A - ω ^ i + (ω ^ i - 1) = ω ^ i * A - 1 from by ring,
    max_eq_right hlt.le, hωi] at hkey
  -- `‖V − 1‖ = 1 ≠ 0`, so `V − 1 ≠ 0` in `ℤ_[p]`, hence the `ℚ_[p]`-coercion
  have hVsub : (branchChar p i s u : ℤ_[p]) - 1 ≠ 0 := by
    rw [hV]
    refine fun h => one_ne_zero (?_ : (1 : ℝ) = 0)
    rw [← hkey, h, norm_zero]
  rw [show (((branchChar p i s u : ℤ_[p])) : ℚ_[p]) - 1
      = (((branchChar p i s u : ℤ_[p]) - 1 : ℤ_[p]) : ℚ_[p]) by
    rw [PadicInt.coe_sub, PadicInt.coe_one]]
  rwa [Ne, PadicInt.coe_eq_zero]

/-- R7.2c (RJW Lemma 7.2(ii), TeX 2224–2226): the denominator has a simple
zero at `s = 1` with derivative `−log_p⟨a⟩`:
`(s−1)⁻¹·(⟨a⟩^{1−s} − 1) → −log_p⟨a⟩` as `s → 1`, `s ≠ 1`. -/
theorem tendsto_branch_denom_div (hp2 : p ≠ 2) {u : ℤ_[p]ˣ} :
    Filter.Tendsto (fun s : ℤ_[p] => ((s : ℚ_[p]) - 1)⁻¹
        * ((((branchChar p (p - 1) (1 - s) u : ℤ_[p])) : ℚ_[p]) - 1))
      (nhdsWithin 1 {s | s ≠ 1})
      (nhds (-((pZpLog p ((PadicInt.angleUnit p u : ℤ_[p]))) : ℚ_[p]))) := by
  set L : ℤ_[p] := pZpLog p (PadicInt.angleUnit p u : ℤ_[p]) with hL
  set Lq : ℚ_[p] := (L : ℚ_[p]) with hLq
  have hLmem : L ∈ Ideal.span {(p : ℤ_[p])} :=
    pZpLog_mem p hp2 (PadicInt.angleUnit_sub_one_mem p u)
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  -- the branch value `branchChar p (p−1) (1−s) u = exp((1−s)·L)`, coerced
  have hpow1 : (PadicInt.teichmuller p u : ℤ_[p]) ^ (p - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val,
      show (PadicInt.teichmuller p u) ^ (p - 1) = 1 from
        Units.ext (by rw [Units.val_pow_eq_pow_val, PadicInt.teichmuller_coe,
          PadicInt.teichmullerFun_pow_card_sub_one, Units.val_one]),
      Units.val_one]
  have hval : ∀ s : ℤ_[p], (((branchChar p (p - 1) (1 - s) u : ℤ_[p])) : ℚ_[p])
      = padicExp p ((((1 - s) * L : ℤ_[p])) : ℚ_[p]) := by
    intro s
    have hmem : (1 - s) * L ∈ Ideal.span {(p : ℤ_[p])} :=
      Ideal.mul_mem_left _ _ hLmem
    rw [branchChar_apply, hpow1, one_mul,
      ← padicExp_smul_padicLog_eq_onePAdicPow p hp2
        (PadicInt.angleUnit_sub_one_mem p u) (1 - s),
      pZpExp_coe p hp2 hmem]
  -- the squeezing function `a(s) = p·‖Lq‖²·‖s−1‖ → 0`
  have hcoe : Filter.Tendsto (fun s : ℤ_[p] => ‖(s : ℚ_[p]) - 1‖)
      (nhds (1 : ℤ_[p])) (nhds 0) := by
    have hc : Continuous (fun s : ℤ_[p] => ‖(s : ℚ_[p]) - 1‖) :=
      continuous_norm.comp (continuous_subtype_val.sub continuous_const)
    have h2 := hc.tendsto (1 : ℤ_[p])
    simpa only [PadicInt.coe_one, sub_self, norm_zero] using h2
  have ha : Filter.Tendsto (fun s : ℤ_[p] => (p : ℝ) * ‖Lq‖ ^ 2 * ‖(s : ℚ_[p]) - 1‖)
      (nhdsWithin 1 {s | s ≠ 1}) (nhds 0) := by
    have h0 : Filter.Tendsto (fun s : ℤ_[p] => ‖(s : ℚ_[p]) - 1‖)
        (nhdsWithin (1 : ℤ_[p]) {s | s ≠ 1}) (nhds 0) :=
      hcoe.mono_left nhdsWithin_le_nhds
    have := h0.const_mul ((p : ℝ) * ‖Lq‖ ^ 2)
    simpa using this
  -- pointwise bound on `{s ≠ 1}`
  have hbound : ∀ᶠ s : ℤ_[p] in nhdsWithin 1 {s | s ≠ 1},
      ‖(((s : ℚ_[p]) - 1)⁻¹
          * ((((branchChar p (p - 1) (1 - s) u : ℤ_[p])) : ℚ_[p]) - 1)) - (-Lq)‖
        ≤ (p : ℝ) * ‖Lq‖ ^ 2 * ‖(s : ℚ_[p]) - 1‖ := by
    refine eventually_nhdsWithin_of_forall fun s hs => ?_
    have hs1 : (s : ℚ_[p]) - 1 ≠ 0 := by
      rw [show ((s : ℚ_[p]) - 1) = ((s - 1 : ℤ_[p]) : ℚ_[p]) by
        rw [PadicInt.coe_sub, PadicInt.coe_one], Ne, PadicInt.coe_eq_zero,
        sub_eq_zero]
      exact hs
    have hsn : ‖(s : ℚ_[p]) - 1‖ ≠ 0 := norm_ne_zero_iff.mpr hs1
    set w : ℚ_[p] := ((((1 - s) * L : ℤ_[p])) : ℚ_[p]) with hw
    have hwval : w = -((s : ℚ_[p]) - 1) * Lq := by
      rw [hw, PadicInt.coe_mul, PadicInt.coe_sub, PadicInt.coe_one, ← hLq]; ring
    have hwnorm : ‖w‖ = ‖(s : ℚ_[p]) - 1‖ * ‖Lq‖ := by
      rw [hwval, norm_mul, norm_neg]
    have hwball : InExpBall p w :=
      inExpBall_of_mem_span p hp2 (Ideal.mul_mem_left _ _ hLmem)
    have hwinv : ((s : ℚ_[p]) - 1)⁻¹ * w = -Lq := by
      rw [hwval]; field_simp
    -- the shifted difference is `(s−1)⁻¹·(exp w − 1 − w)`
    have hid : (((s : ℚ_[p]) - 1)⁻¹
        * ((((branchChar p (p - 1) (1 - s) u : ℤ_[p])) : ℚ_[p]) - 1)) - (-Lq)
        = ((s : ℚ_[p]) - 1)⁻¹ * (padicExp p w - 1 - w) := by
      rw [hval s, ← hw]
      linear_combination hwinv
    rw [hid, norm_mul, norm_inv]
    calc ‖(s : ℚ_[p]) - 1‖⁻¹ * ‖padicExp p w - 1 - w‖
        ≤ ‖(s : ℚ_[p]) - 1‖⁻¹ * ((p : ℝ) * ‖w‖ ^ 2) := by
          gcongr
          exact norm_padicExp_sub_one_sub_self_le p hwball
      _ = (p : ℝ) * ‖Lq‖ ^ 2 * ‖(s : ℚ_[p]) - 1‖ := by
          rw [hwnorm, mul_pow]
          field_simp
  -- squeeze
  have hsq : Filter.Tendsto (fun s : ℤ_[p] => (((s : ℚ_[p]) - 1)⁻¹
        * ((((branchChar p (p - 1) (1 - s) u : ℤ_[p])) : ℚ_[p]) - 1)) - (-Lq))
      (nhdsWithin 1 {s | s ≠ 1}) (nhds 0) :=
    squeeze_zero_norm' hbound ha
  have := hsq.add (tendsto_const_nhds (x := -Lq))
  simpa using this

/-- Exponent-congruence (the `p = 2`-valid analogue of `norm_onePAdicPow_sub_one`):
if `t ∈ p^k·ℤ_p` then `y^t ≡ 1 mod p^k`. Route: `t = p^k·c`, so
`y^t = (y^c)^{p^k}` and `dvd_sub_pow_of_dvd_sub` lifts `p ∣ y^c − 1` to
`p^{k+1} ∣ (y^c)^{p^k} − 1`. -/
private lemma onePAdicPow_sub_one_mem_span_pow {y : ℤ_[p]}
    (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) (k : ℕ) {t : ℤ_[p]}
    (ht : t ∈ Ideal.span {(p : ℤ_[p]) ^ k}) :
    PadicInt.onePAdicPow p y hy t - 1 ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
  -- `t = p^k · c`
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ht
  -- `y^t = (y^c)^{p^k}` via `κ(n • a) = κ(a)^n` (`p^k·c = (p^k : ℕ) • c`)
  have hsmul : (p : ℤ_[p]) ^ k * c = (p ^ k : ℕ) • c := by
    rw [nsmul_eq_mul, Nat.cast_pow]
  have hpow : PadicInt.onePAdicPow p y hy ((p : ℤ_[p]) ^ k * c)
      = (PadicInt.onePAdicPow p y hy c) ^ (p ^ k) := by
    rw [hsmul, AddChar.map_nsmul_eq_pow]
  rw [hpow]
  -- `p ∣ y^c − 1`
  have hdvd1 : (p : ℤ_[p]) ∣ PadicInt.onePAdicPow p y hy c - 1 :=
    Ideal.mem_span_singleton.mp (PadicInt.onePAdicPow_sub_one_mem p y hy c)
  -- `p^{k+1} ∣ (y^c)^{p^k} − 1`, weaken to `p^k`
  have hsharp : ((p : ℤ_[p]) ^ (k + 1)) ∣
      (PadicInt.onePAdicPow p y hy c) ^ p ^ k - (1 : ℤ_[p]) ^ p ^ k :=
    dvd_sub_pow_of_dvd_sub hdvd1 k
  rw [one_pow] at hsharp
  exact Ideal.mem_span_singleton.mpr
    (dvd_trans (pow_dvd_pow _ (Nat.le_succ k)) hsharp)

/-- The `p = 2`-valid weak isometry: `‖y^t − 1‖ ≤ ‖t‖` for `y ∈ 1 + pℤ_p` and
every `t` (the sharp `‖y^t − 1‖ = ‖t‖·‖y − 1‖` of `norm_onePAdicPow_sub_one`
needs `p ≠ 2`; this one-sided bound holds for all `p`). -/
private lemma norm_onePAdicPow_sub_one_le {y : ℤ_[p]}
    (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) (t : ℤ_[p]) :
    ‖(PadicInt.onePAdicPow p y hy t : ℤ_[p]) - 1‖ ≤ ‖t‖ := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [show PadicInt.onePAdicPow p y hy 0 = 1 from AddChar.map_zero_eq_one _,
      sub_self, norm_zero]
  -- `‖t‖ = p^{-val t}`, so `t ∈ span{p^{val t}}`
  set k : ℕ := t.valuation with hk
  have htmem : t ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_eq_zpow_neg_valuation ht]
  have hmem := onePAdicPow_sub_one_mem_span_pow p hy k htmem
  rw [PadicInt.norm_eq_zpow_neg_valuation ht]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow _ k).mpr hmem

/-- R7.3a: the numerator pairing is continuous in `s` (the `p^m`-congruence
route: `s ≡ s' mod p^m ⟹ ⟨x⟩^{1−s} ≡ ⟨x⟩^{1−s'} mod p^m` uniformly in
`x`, through `onePAdicPow_sub_one_mem_pow`; then the measure norm bound).
Notably `p = 2` is allowed here. -/
theorem continuous_zetaNum_branch_pairing (m i : ℕ) :
    Continuous (fun s : ℤ_[p] =>
      (((PadicMeasure.zetaNum p m (branchChar p i (1 - s)) : ℤ_[p]))
        : ℚ_[p])) := by
  -- pointwise sup-norm bound `‖branchChar (1−s) x − branchChar (1−s') x‖ ≤ ‖s − s'‖`
  have hptbound : ∀ (s s' : ℤ_[p]) (x : ℤ_[p]ˣ),
      ‖(branchChar p i (1 - s) x : ℤ_[p]) - branchChar p i (1 - s') x‖ ≤ ‖s - s'‖ := by
    intro s s' x
    set ω : ℤ_[p] := (PadicInt.teichmuller p x : ℤ_[p]) with hω
    set κ : AddChar ℤ_[p] ℤ_[p] := PadicInt.onePAdicPow p (PadicInt.angleUnit p x : ℤ_[p])
      (PadicInt.angleUnit_sub_one_mem p x) with hκ
    -- `branchChar (1−s) x = ω^i · κ(1−s)` and `κ(1−s) = κ(1−s')·κ(s'−s)`
    have hadd : κ (1 - s) = κ (1 - s') * κ (s' - s) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    have hdiff : (branchChar p i (1 - s) x : ℤ_[p]) - branchChar p i (1 - s') x
        = ω ^ i * κ (1 - s') * (κ (s' - s) - 1) := by
      rw [branchChar_apply, branchChar_apply, ← hω, ← hκ, hadd]; ring
    rw [hdiff]
    -- norms: `‖ω^i‖ ≤ 1`, `‖κ(1−s')‖ ≤ 1`, `‖κ(s'−s) − 1‖ ≤ ‖s'−s‖ = ‖s − s'‖`
    have hω1 : ‖ω ^ i‖ ≤ 1 := PadicInt.norm_le_one _
    have hκ1 : ‖κ (1 - s')‖ ≤ 1 := PadicInt.norm_le_one _
    have hκd : ‖κ (s' - s) - 1‖ ≤ ‖s' - s‖ :=
      norm_onePAdicPow_sub_one_le p (PadicInt.angleUnit_sub_one_mem p x) (s' - s)
    calc ‖ω ^ i * κ (1 - s') * (κ (s' - s) - 1)‖
        = ‖ω ^ i‖ * ‖κ (1 - s')‖ * ‖κ (s' - s) - 1‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * 1 * ‖s' - s‖ := by gcongr
      _ = ‖s - s'‖ := by rw [one_mul, one_mul, norm_sub_rev]
  -- the `ℤ_[p]`-valued pairing is `1`-Lipschitz, hence continuous
  have hLip : LipschitzWith 1 (fun s : ℤ_[p] =>
      (PadicMeasure.zetaNum p m (branchChar p i (1 - s)) : ℤ_[p])) := by
    refine LipschitzWith.of_dist_le_mul fun s s' => ?_
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
    refine le_trans (PadicMeasure.norm_apply_le p _ _) ?_
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
    rw [ContinuousMap.coe_sub, Pi.sub_apply]
    exact hptbound s s' x
  exact continuous_subtype_val.comp hLip.continuous

/-- **RJW Theorem 7.1(i)** (TeX 2189–2190): for `0 < i < p−1` the branch
`ζ_{p,i}` is continuous ("analytic") at `s = 1` — indeed everywhere, but
we state the source's claim. -/
theorem continuousAt_zetaPBranch (hp2 : p ≠ 2) {i : ℕ} (hi0 : 0 < i)
    (hi : i < p - 1) : ContinuousAt (zetaPBranch p hp2 i) 1 := by
  classical
  obtain ⟨-, -, hgen⟩ :=
    (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose_spec
  set m := (PadicMeasure.exists_nat_topological_generator p hp2).choose
  set u := (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose
  -- the denominator `s ↦ ⟨u⟩^{1−s}·ω^i − 1` is continuous (`onePAdicPow` in the exponent)
  have hden_cont : Continuous (fun s : ℤ_[p] =>
      (((branchChar p i (1 - s) u : ℤ_[p])) : ℚ_[p]) - 1) := by
    refine (continuous_subtype_val.comp ?_).sub continuous_const
    have hfun : (fun s : ℤ_[p] => (branchChar p i (1 - s) u : ℤ_[p]))
        = fun s : ℤ_[p] => (PadicInt.teichmuller p u : ℤ_[p]) ^ i
          * PadicInt.onePAdicPow p (PadicInt.angleUnit p u : ℤ_[p])
              (PadicInt.angleUnit_sub_one_mem p u) (1 - s) := by
      funext s; rw [branchChar_apply]
    rw [hfun]
    exact continuous_const.mul ((PadicInt.continuous_onePAdicPow p _ _).comp
      (continuous_const.sub continuous_id))
  -- the denominator is nonzero at `s = 1`
  have hden_ne : (((branchChar p i (1 - 1) u : ℤ_[p])) : ℚ_[p]) - 1 ≠ 0 :=
    branch_denom_ne_zero p hgen hi0 hi (1 - 1)
  -- assemble: `(denom)⁻¹ · numerator`
  unfold zetaPBranch
  exact (hden_cont.continuousAt.inv₀ hden_ne).mul
    (continuous_zetaNum_branch_pairing p m i).continuousAt

end character

section mass

variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

/-- R7.4a: the unit factor `u_a` of `(1+T)^a − 1 = a·T·u_a`
(`u_a = Σ_n a⁻¹·C(a, n+1)·Tⁿ`, constant term `1`; TeX 2296–2300). -/
noncomputable def uA (a : ℕ) : PowerSeries K :=
  PowerSeries.mk fun n => ((a : K))⁻¹ * (a.choose (n + 1))

/-- R7.4b: RJW's antiderivative `F̃_a = log(T/(1+T) · (1+T)^a/((1+T)^a−1))`
(TeX 2268), realised through the factorisation
`F̃_a = −log_p(a) − log(u_a) + (a−1)·log(1+T)` (TeX eq:tilde F_a 2 +
eq:F_a tilde): the formal compositions are legal (`u_a − 1` has constant
term `0`). -/
noncomputable def FtildeA (a : ℕ) : PowerSeries K :=
  PowerSeries.C (-(extLog p ((a : K))))
    - (formalLog (K := K)).subst (uA K a - 1)
    + ((a - 1 : ℕ)) • formalLog (K := K)

/-- R7.4c: the constant coefficient is `−log_p(a)` (TeX eq:F_a(0)). -/
theorem constantCoeff_FtildeA {a : ℕ} :
    PowerSeries.constantCoeff (FtildeA p K a)
      = -(extLog p ((a : K))) := by sorry

/-- R7.4d (RJW Lemma 7.3, TeX 2271–2279): `∂F̃_a = F_a` formally. -/
theorem one_add_mul_derivative_FtildeA {a : ℕ} (ha0 : a ≠ 0) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun (FtildeA p K a)
      = PowerSeries.map ((algebraMap ℚ_[p] K).comp (PadicInt.Coe.ringHom))
          (PadicMeasure.Fa p a) := by
  sorry

/-- R7.5a: the §4 numerator measure `x⁻¹·Res_{ℤ_p^×}(μ_a)` (=
`PadicMeasure.zetaNum`), pushed to `ℤ_p` and base-changed to `K`. -/
noncomputable def rhoA (a : ℕ) : MeasureR K ℤ_[p] :=
  MeasureR.baseChange p K (PadicMeasure.iota p (PadicMeasure.zetaNum p a))

/-- R7.5b: `ρ_a` is supported on the units. -/
theorem psi_rhoA (a : ℕ) : MeasureR.psi p K (rhoA p K a) = 0 := by sorry

/-- R7.5c: multiplication by `x` recovers `Res_{ℤ_p^×}(μ_a)` —
`∂𝓐(ρ_a) = 𝓐(Res_{units}(μ_a))` over `K` (Lemma 6.3's pattern, T614). -/
theorem one_add_mul_derivative_mahlerK_rhoA (a : ℕ) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun
        (mahlerK p K (rhoA p K a))
      = mahlerK p K (MeasureR.res p K
          (PadicMeasure.isClopen_units p)
          (MeasureR.baseChange p K (PadicMeasure.muA p a))) := by sorry

/-- R7.6a (the c₀-pin, T615-pattern — no Gauss clearing this time):
`p·𝓐(ρ_a)(0) = p·F̃_a(0) − Σ_{i<p} F̃_a(ξ^i − 1)`. -/
theorem p_mul_constantCoeff_mahlerK_rhoA {a : ℕ} (ha : ¬ (p : ℕ) ∣ a)
    (ha0 : a ≠ 0) {ξ : K} (hξ : IsPrimitiveRoot ξ p) :
    (p : K) * PowerSeries.constantCoeff
        (mahlerK p K (rhoA p K a))
      = (p : K) * PowerSeries.constantCoeff (FtildeA p K a)
        - ∑ i : Fin p, seriesEval (FtildeA p K a)
            (ξ ^ (i : ℕ) - 1) := by sorry

/-- R7.6b (RJW Lemma 7.5's trace, TeX 2330–2349): the evaluated `μ_p`-sum
collapses — `Σ_{i<p} F̃_a(ξ^i − 1) = −log_p(a)` (the `{ξ^a} = μ_p`
reindex for `p ∤ a` and `Π_ξ(Xξ−1) = X^p−1`). -/
theorem sum_seriesEval_FtildeA (hp2 : p ≠ 2) {a : ℕ} (ha : ¬ (p : ℕ) ∣ a)
    (ha0 : a ≠ 0) {ξ : K} (hξ : IsPrimitiveRoot ξ p) :
    ∑ i : Fin p, seriesEval (FtildeA p K a) (ξ ^ (i : ℕ) - 1)
      = -(extLog p ((a : K))) := by sorry

/-- R7.6c (RJW Lemma 7.5, TeX 2320): the mass of `x⁻¹·Res(μ_a)` —
`((1−φψ)F̃_a)(0) = −(1−p⁻¹)·log_p(a)`, in the c₀-design form. -/
theorem constantCoeff_mahlerK_rhoA (hp2 : p ≠ 2) {a : ℕ}
    (ha : ¬ (p : ℕ) ∣ a) (ha0 : a ≠ 0) {ξ : K}
    (hξ : IsPrimitiveRoot ξ p) :
    PowerSeries.constantCoeff (mahlerK p K (rhoA p K a))
      = -(1 - (p : K)⁻¹) * extLog p ((a : K)) := by sorry

end mass

section descent

/-- R7.7 (eq:zeta p residue 2 + Lemma 7.5, descended to `ℚ_p`): the total
mass of the §4 numerator measure —
`∫_{ℤ_p^×} x⁻¹·μ_a = −(1−p⁻¹)·log_p(a)` (computed in `ℂ_p` and pulled
back along the injective structure map). -/
theorem zetaNum_one (hp2 : p ≠ 2) {a : ℕ} (ha : ¬ (p : ℕ) ∣ a)
    (ha0 : a ≠ 0) :
    (((PadicMeasure.zetaNum p a (1 : C(ℤ_[p]ˣ, ℤ_[p]))) : ℤ_[p]) : ℚ_[p])
      = -(1 - (p : ℚ_[p])⁻¹) * extLog p (((a : ℕ) : ℚ_[p])) := by sorry

/-- **RJW Theorem 7.1(ii)** (`thm:residue`, TeX 2191–2192): "The function
`ζ_{p,p−1}` has a simple pole at `s = 1` with residue `1 − p⁻¹`" — as the
topological limit `lim_{s→1, s≠1} (s−1)·ζ_{p,p−1}(s) = 1 − p⁻¹`. -/
theorem tendsto_sub_one_mul_zetaPBranch (hp2 : p ≠ 2) :
    Filter.Tendsto
      (fun s : ℤ_[p] => ((s : ℚ_[p]) - 1) * zetaPBranch p hp2 (p - 1) s)
      (nhdsWithin 1 {s | s ≠ 1})
      (nhds (1 - (p : ℚ_[p])⁻¹)) := by sorry

end descent

end PadicLFunctions
