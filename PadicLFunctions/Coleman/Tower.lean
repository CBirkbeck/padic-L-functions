/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.ResidueZeta
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# The cyclotomic tower over ℚ_p (RJW §9, TeX 2466–2511)

The local objects of Part II: a fixed compatible system `ξ_{p^n}` of
primitive `p^n`-th roots of unity (`ξ_{p^{n+1}}^p = ξ_{p^n}`), the tower
`K_n = ℚ_p(μ_{p^n})`, the uniformisers `π_n = ξ_{p^n} − 1`, the integer
rings `O_n` and their unit groups `𝒰_n`, and (at the `𝒰_∞`-ticket) the
norm-inverse-limit `𝒰_∞ = lim_n 𝒰_n`.

Design (decomposition R10.1): the tower lives *inside* `ℂ_p` — matching
the source's own framing of the `π_n` as points of the open unit ball
`B(0,1) ⊂ ℂ_p` (TeX 2528–2532) — so `K_n` is an
`IntermediateField ℚ_[p] ℂ_[p]`, the integer ring is the norm-ball, and
power-series evaluation at `π_n` is the project's `seriesEval`. The
degree ladder `[K_n : ℚ_p] = φ(p^n)` comes from Eisenstein-ness of
`Φ_{p^n}(T+1)` over `ℤ_p` (R10.2); the norm collapse
`N_{n+1,n}(ξ^b_{p^{n+1}} − 1) = ξ^b_{p^n} − 1` (TeX 2581–2585) is the
engine for both the cyclotomic units and the evaluation/norm commuting
square.
-/

open PowerSeries Polynomial

namespace PadicLFunctions

namespace Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-- The single tower step: from a primitive `p^n`-th root `z` we extract a
primitive `p^{n+1}`-th root `w` with `w^p = z`. For `n = 0` (`z = 1`) we take
a genuine primitive `p`-th root (`HasEnoughRootsOfUnity`, available from
`IsAlgClosed` + char `0`); for `n ≥ 1` any `p`-th root of `z` works — alg.
closure gives one, and an order count (`Nat.dvd_prime_pow`) pins its order
to `p^{n+1}`. -/
private theorem primitiveRoot_pow_succ :
    ∀ {n : ℕ} {z : ℂ_[p]}, IsPrimitiveRoot z (p ^ n) →
      ∃ w : ℂ_[p], IsPrimitiveRoot w (p ^ (n + 1)) ∧ w ^ p = z := by
  haveI : NeZero (p : ℂ_[p]) := ⟨(Nat.cast_ne_zero (R := ℂ_[p])).mpr hp.out.ne_zero⟩
  rintro (_ | n) z hz
  · -- `n = 0`: `z = 1`, take a genuine primitive `p`-th root
    obtain ⟨w, hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[p] p
    have hz1 : z = 1 := by simpa using hz.pow_eq_one
    exact ⟨w, by simpa using hw, by rw [hz1, hw.pow_eq_one]⟩
  · -- `n + 1`: any `p`-th root `w` of `z` has order exactly `p^{n+2}`
    obtain ⟨w, hwz⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ_[p]) z (n := p) hp.out.pos
    refine ⟨w, ?_, hwz⟩
    rw [IsPrimitiveRoot.iff_orderOf]
    -- `w^{p^{n+2}} = z^{p^{n+1}} = 1`, so `orderOf w ∣ p^{n+2}`
    have hpow : w ^ p ^ (n + 1 + 1) = 1 := by
      rw [pow_succ', pow_mul, hwz, hz.pow_eq_one]
    have hdvd : orderOf w ∣ p ^ (n + 1 + 1) := orderOf_dvd_of_pow_eq_one hpow
    obtain ⟨k, hkle, hk⟩ := (Nat.dvd_prime_pow hp.out).1 hdvd
    -- if `k ≤ n+1` then `z^{p^n} = w^{p^{n+1}} = 1`, contradicting `hz`
    rcases eq_or_lt_of_le hkle with hkeq | hklt
    · rw [hk, hkeq]
    · exfalso
      have hkle' : k ≤ n + 1 := Nat.lt_succ_iff.1 hklt
      have hwpn : w ^ p ^ (n + 1) = 1 :=
        orderOf_dvd_iff_pow_eq_one.1 (hk ▸ pow_dvd_pow p hkle')
      refine hz.pow_ne_one_of_pos_of_lt (l := p ^ n) (pow_pos hp.out.pos n).ne'
        (pow_lt_pow_right₀ hp.out.one_lt n.lt_succ_self) ?_
      rw [pow_succ', pow_mul, hwz] at hwpn
      exact hwpn

/-- R9: a compatible system of primitive `p^n`-th roots of unity in `ℂ_p`
exists (`ξ_0 = 1`; each `ξ_{n+1}` is a `p`-th root of `ξ_n`, primitive of
order `p^{n+1}`): ℕ-recursion + `IsAlgClosed` roots. RJW TeX 2507: "We fix
once and for all a compatible system of roots of unity `(ξ_{p^n})_n`". -/
theorem exists_compatible_primitiveRoot :
    ∃ ξ : ℕ → ℂ_[p],
      (∀ n, IsPrimitiveRoot (ξ n) (p ^ n)) ∧ ∀ n, ξ (n + 1) ^ p = ξ n := by
  -- build the system as a chain of subtypes `{z // IsPrimitiveRoot z (p^n)}`
  let chain : ∀ n, {z : ℂ_[p] // IsPrimitiveRoot z (p ^ n)} := fun n =>
    Nat.rec ⟨1, by simp⟩ (fun _ zn => ⟨(primitiveRoot_pow_succ p zn.2).choose,
      (primitiveRoot_pow_succ p zn.2).choose_spec.1⟩) n
  refine ⟨fun n => (chain n).1, fun n => (chain n).2, fun n => ?_⟩
  exact (primitiveRoot_pow_succ p (chain n).2).choose_spec.2

/-- The fixed compatible system `n ↦ ξ_{p^n}` (RJW TeX 2507). -/
noncomputable def zetaSys : ℕ → ℂ_[p] :=
  (exists_compatible_primitiveRoot p).choose

theorem zetaSys_primitiveRoot (n : ℕ) :
    IsPrimitiveRoot (zetaSys p n) (p ^ n) :=
  (exists_compatible_primitiveRoot p).choose_spec.1 n

theorem zetaSys_pow_p (n : ℕ) : zetaSys p (n + 1) ^ p = zetaSys p n :=
  (exists_compatible_primitiveRoot p).choose_spec.2 n

/-- R9: the local cyclotomic field `K_n = ℚ_p(μ_{p^n})`, realised inside
`ℂ_p` as `ℚ_p(ξ_{p^n})` (RJW TeX 2473). -/
noncomputable def K (n : ℕ) : IntermediateField ℚ_[p] ℂ_[p] :=
  IntermediateField.adjoin ℚ_[p] {zetaSys p n}

/-- R9: the uniformiser `π_n = ξ_{p^n} − 1` of `K_n` (RJW TeX 2507). -/
noncomputable def pi (n : ℕ) : ℂ_[p] := zetaSys p n - 1

theorem zetaSys_mem_K (n : ℕ) : zetaSys p n ∈ K p n :=
  IntermediateField.subset_adjoin ℚ_[p] {zetaSys p n} (Set.mem_singleton _)

theorem pi_mem_K (n : ℕ) : pi p n ∈ K p n :=
  sub_mem (zetaSys_mem_K p n) (one_mem _)

theorem K_le_succ (n : ℕ) : K p n ≤ K p (n + 1) := by
  refine IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 ?_)
  rw [← zetaSys_pow_p p n]
  exact pow_mem (zetaSys_mem_K p (n + 1)) p

/-- The `(p^{n+1})`-th cyclotomic polynomial is irreducible over `ℤ_p`: the
translate `Φ_{p^{n+1}}(T+1)` is Eisenstein at `(p)` (transported from `ℤ` via
`cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt`), hence irreducible, and the
`T ↦ T+1` automorphism (`algEquivAevalXAddC`) carries that back to `Φ_{p^{n+1}}`.
RJW TeX 2475. -/
private theorem cyclotomic_irreducible_Zp (n : ℕ) :
    Irreducible (cyclotomic (p ^ (n + 1)) ℤ_[p]) := by
  set φ := algebraMap ℤ ℤ_[p] with hφ
  have hdne : ((X : ℤ_[p][X]) + 1).natDegree ≠ 0 := by
    rw [show ((X : ℤ_[p][X]) + 1) = (X : ℤ_[p][X]) + Polynomial.C 1 by simp, natDegree_X_add_C]
    exact one_ne_zero
  have hmonicZ : ((cyclotomic (p ^ (n + 1)) ℤ).comp ((X : ℤ[X]) + 1)).Monic := by
    refine (cyclotomic.monic _ ℤ).comp (monic_X_add_C 1) ?_
    rw [show ((X : ℤ[X]) + 1) = (X : ℤ[X]) + Polynomial.C 1 by simp, natDegree_X_add_C]
    exact one_ne_zero
  have hmonicZp : ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp ((X : ℤ_[p][X]) + 1)).Monic :=
    (cyclotomic.monic _ ℤ_[p]).comp (monic_X_add_C 1) hdne
  have hmapeq : (cyclotomic (p ^ (n + 1)) ℤ_[p]).comp ((X : ℤ_[p][X]) + 1)
      = ((cyclotomic (p ^ (n + 1)) ℤ).comp ((X : ℤ[X]) + 1)).map φ := by
    rw [Polynomial.map_comp, map_cyclotomic, Polynomial.map_add, Polynomial.map_X,
      Polynomial.map_one]
  have hdeg : ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp ((X : ℤ_[p][X]) + 1)).natDegree
      = ((cyclotomic (p ^ (n + 1)) ℤ).comp ((X : ℤ[X]) + 1)).natDegree := by
    rw [hmapeq, hmonicZ.natDegree_map]
  have hZ := cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n
  have hpspan : (Ideal.span {(p : ℤ_[p])}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)]
    exact_mod_cast (PadicInt.irreducible_p (p := p)).prime
  have himg : ∀ z : ℤ, z ∈ Ideal.span {(p : ℤ)} → φ z ∈ Ideal.span {(p : ℤ_[p])} := by
    intro z hz
    rw [Ideal.mem_span_singleton] at hz ⊢
    obtain ⟨k, rfl⟩ := hz
    exact ⟨φ k, by simp [hφ, mul_comm]⟩
  have hEis : ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp ((X : ℤ_[p][X]) + 1)).IsEisensteinAt
      (Ideal.span {(p : ℤ_[p])}) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmapeq, (hmonicZ.map φ).leadingCoeff, Ideal.mem_span_singleton]
      intro h
      exact hpspan.ne_top (Ideal.eq_top_of_isUnit_mem _
        (Ideal.mem_span_singleton.2 (dvd_refl _)) (isUnit_of_dvd_one h))
    · intro i hi
      rw [hmapeq, Polynomial.coeff_map]
      exact himg _ (hZ.mem (hdeg ▸ hi))
    · rw [hmapeq, Polynomial.coeff_map]
      have h0 : ((cyclotomic (p ^ (n + 1)) ℤ).comp ((X : ℤ[X]) + 1)).coeff 0 = (p : ℤ) := by
        rw [coeff_zero_eq_eval_zero, eval_comp]; simp [eval_one_cyclotomic_prime_pow]
      rw [h0, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      intro h
      have hdvd : ((p : ℤ_[p])) ^ 2 ∣ (p : ℤ_[p]) := by simpa using h
      have hpne : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
      rw [pow_two] at hdvd
      obtain ⟨c, hc⟩ := hdvd
      have h1 : (p : ℤ_[p]) * 1 = (p : ℤ_[p]) * ((p : ℤ_[p]) * c) := by
        rw [mul_one]; linear_combination hc
      have h2 : (1 : ℤ_[p]) = (p : ℤ_[p]) * c := mul_left_cancel₀ hpne h1
      exact (PadicInt.irreducible_p (p := p)).not_isUnit (IsUnit.of_mul_eq_one c h2.symm)
  have hcomp_irr : Irreducible ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp ((X : ℤ_[p][X]) + 1)) := by
    refine hEis.irreducible hpspan hmonicZp.isPrimitive ?_
    rw [hdeg, natDegree_comp, natDegree_cyclotomic,
      show ((X : ℤ[X]) + 1).natDegree = 1 by
        rw [show ((X : ℤ[X]) + 1) = (X : ℤ[X]) + Polynomial.C 1 by simp, natDegree_X_add_C],
      mul_one]
    exact Nat.totient_pos.2 (pow_pos hp.out.pos _)
  have hmap : (algEquivAevalXAddC (1 : ℤ_[p])) (cyclotomic (p ^ (n + 1)) ℤ_[p])
      = (cyclotomic (p ^ (n + 1)) ℤ_[p]).comp ((X : ℤ_[p][X]) + 1) := by
    rw [algEquivAevalXAddC_apply, comp_eq_aeval, map_one]
  exact (MulEquiv.irreducible_iff (algEquivAevalXAddC (1 : ℤ_[p])).toMulEquiv).mp
    (hmap ▸ hcomp_irr)

/-- `Φ_{p^n}` is irreducible over `ℚ_p` for `n ≥ 1` — Gauss's lemma transfers the
`ℤ_p`-irreducibility (`ℤ_p` is an integrally closed domain with fraction field
`ℚ_p`). This is the key input for the degree ladder and the cyclotomic-extension
structure of `K_n`. -/
private theorem cyclotomic_irreducible_Qp {n : ℕ} (hn : 1 ≤ n) :
    Irreducible (cyclotomic (p ^ n) ℚ_[p]) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← map_cyclotomic (p ^ (m + 1)) (algebraMap ℤ_[p] ℚ_[p])]
  exact (Monic.irreducible_iff_irreducible_map_fraction_map
    (cyclotomic.monic _ ℤ_[p])).mp (cyclotomic_irreducible_Zp p m)

/-- `K_n = ℚ_p(ξ_{p^n})` is a cyclotomic extension of `ℚ_p`: `ξ_{p^n}` is a
primitive `p^n`-th root of unity adjoined to `ℚ_p`. (Built from the single-element
algebraicity of `ξ_{p^n}` since `ℂ_p` is not algebraic over `ℚ_p`.) -/
private instance isCyclotomicExtension_K {n : ℕ} [NeZero (p ^ n)] :
    IsCyclotomicExtension {p ^ n} ℚ_[p] (K p n) := by
  have hζ := zetaSys_primitiveRoot p n
  have hint : IsIntegral ℚ_[p] (zetaSys p n) :=
    (hζ.isIntegral (pow_pos hp.out.pos n)).tower_top
  change IsCyclotomicExtension {p ^ n} ℚ_[p] (K p n).toSubalgebra
  rw [K, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension ℚ_[p]

/-- R10.2 (degree ladder): `[K_n : ℚ_p] = φ(p^n)` — irreducibility of
`Φ_{p^n}` over `ℚ_p` via Eisenstein at `(p)` after `T ↦ T+1`
(RJW TeX 2475: "totally ramified … of degree `(p−1)p^{n−1}`"). -/
theorem finrank_K (n : ℕ) :
    Module.finrank ℚ_[p] (K p n) = Nat.totient (p ^ n) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [pow_zero, Nat.totient_one]
    have h1 : zetaSys p 0 = 1 := by simpa using (zetaSys_primitiveRoot p 0).pow_eq_one
    rw [K, h1, IntermediateField.adjoin_one]
    exact IntermediateField.finrank_bot
  · haveI : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos n).ne'⟩
    exact IsCyclotomicExtension.finrank (K p n) (cyclotomic_irreducible_Qp p (by omega))

/-- The norm of a primitive `p^n`-th root of unity in `ℂ_p` is `1`
(`‖ξ‖^{p^n} = 1` forces `‖ξ‖ = 1`). -/
private theorem norm_primitiveRoot_eq_one {n : ℕ} {ξ : ℂ_[p]}
    (hξ : IsPrimitiveRoot ξ (p ^ n)) : ‖ξ‖ = 1 := by
  have h1 : ‖ξ‖ ^ (p ^ n) = 1 := by rw [← norm_pow, hξ.pow_eq_one, norm_one]
  have hne : p ^ n ≠ 0 := (pow_pos hp.out.pos n).ne'
  refine le_antisymm ?_ ?_
  · by_contra h; rw [not_le] at h; exact absurd h1 (one_lt_pow₀ h hne).ne'
  · by_contra h; rw [not_le] at h; exact absurd h1 (pow_lt_one₀ (norm_nonneg ξ) h hne).ne

/-- For a norm-one element `ξ` of `ℂ_p`, `‖ξ^c − 1‖ ≤ ‖ξ − 1‖`: factor
`ξ^c − 1 = (∑_{i<c} ξ^i)(ξ − 1)` and bound the geometric factor by `1`
(ultrametric sum of norm-one terms). -/
private theorem norm_pow_sub_one_le {ξ : ℂ_[p]} (hξ1 : ‖ξ‖ = 1) (c : ℕ) :
    ‖ξ ^ c - 1‖ ≤ ‖ξ - 1‖ := by
  rw [show ξ ^ c - 1 = (∑ i ∈ Finset.range c, ξ ^ i) * (ξ - 1) from (geom_sum_mul ξ c).symm,
    norm_mul]
  have hgeom : ‖∑ i ∈ Finset.range c, ξ ^ i‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
      (fun i _ => by rw [norm_pow, hξ1, one_pow])
  nlinarith [norm_nonneg (ξ - 1), hgeom]

/-- Any two primitive `p^n`-th roots of unity `ξ, η` in `ℂ_p` satisfy
`‖ξ − 1‖ = ‖η − 1‖`: each is a power of the other (same cyclic group), so
`norm_pow_sub_one_le` gives both inequalities. This is the engine for the
`π_n`-norm: all conjugates of `π_n` have the same norm. -/
private theorem norm_sub_one_eq {n : ℕ} {ξ η : ℂ_[p]}
    (hξ : IsPrimitiveRoot ξ (p ^ n)) (hη : IsPrimitiveRoot η (p ^ n)) :
    ‖ξ - 1‖ = ‖η - 1‖ := by
  haveI : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos n).ne'⟩
  obtain ⟨i, _, hi⟩ := hξ.eq_pow_of_pow_eq_one hη.pow_eq_one
  obtain ⟨j, _, hj⟩ := hη.eq_pow_of_pow_eq_one hξ.pow_eq_one
  refine le_antisymm ?_ ?_
  · rw [← hj]; exact norm_pow_sub_one_le p (norm_primitiveRoot_eq_one p hη) j
  · rw [← hi]; exact norm_pow_sub_one_le p (norm_primitiveRoot_eq_one p hξ) i

/-- Every root `r` of `Φ_{p^n}` in `ℂ_p` is a primitive `p^n`-th root, so
`‖r − 1‖ = ‖π_n‖`. -/
private theorem norm_root_sub_one_eq {n : ℕ} (r : ℂ_[p])
    (hr : r ∈ (cyclotomic (p ^ n) ℂ_[p]).roots) : ‖r - 1‖ = ‖pi p n‖ := by
  haveI : NeZero ((p ^ n : ℕ) : ℂ_[p]) := by
    refine ⟨?_⟩; rw [Nat.cast_pow]; exact pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  rw [mem_roots (cyclotomic_ne_zero _ _)] at hr
  rw [pi]
  exact norm_sub_one_eq p (isRoot_cyclotomic_iff.mp hr) (zetaSys_primitiveRoot p n)

/-- R10.2: the norm of the uniformiser, rpow-free form:
`‖π_n‖^{φ(p^n)} = p⁻¹` for `n ≥ 1` (the Eisenstein constant term:
`N_{K_n/ℚ_p}(π_n) = ±Φ_{p^n}(1) = ±p`, and the spectral norm is
Galois-invariant). In particular `0 < ‖π_n‖ < 1`.

The proof works directly in `ℂ_p`: `g := Φ_{p^n}(T+1)` is monic and splits, its
roots are `{η − 1 : η ∈ μ_{p^n}^×}` each of norm `‖π_n‖` (`norm_root_sub_one_eq`),
its constant term is `Φ_{p^n}(1) = p`, and Vieta gives
`p = ±∏ roots`, so `‖π_n‖^{φ(p^n)} = ‖∏ roots‖ = ‖p‖ = p⁻¹`. -/
theorem norm_pi_pow_totient {n : ℕ} (hn : 1 ≤ n) :
    ‖pi p n‖ ^ Nat.totient (p ^ n) = (p : ℝ)⁻¹ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  haveI : NeZero ((p ^ (m + 1) : ℕ) : ℂ_[p]) := by
    refine ⟨?_⟩; rw [Nat.cast_pow]; exact pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  set g : ℂ_[p][X] := (cyclotomic (p ^ (m + 1)) ℂ_[p]).comp ((X : ℂ_[p][X]) + 1) with hg
  have hgmonic : g.Monic := by
    rw [hg]; refine (cyclotomic.monic _ ℂ_[p]).comp (monic_X_add_C 1) ?_
    rw [show ((X : ℂ_[p][X]) + 1) = (X : ℂ_[p][X]) + Polynomial.C 1 by simp, natDegree_X_add_C]
    exact one_ne_zero
  have hgsplits : g.Splits := IsAlgClosed.splits g
  have hgdeg : g.natDegree = Nat.totient (p ^ (m + 1)) := by
    rw [hg, natDegree_comp, natDegree_cyclotomic,
      show ((X : ℂ_[p][X]) + 1).natDegree = 1 by
        rw [show ((X : ℂ_[p][X]) + 1) = (X : ℂ_[p][X]) + Polynomial.C 1 by simp, natDegree_X_add_C],
      mul_one]
  have hgc0 : g.coeff 0 = (p : ℂ_[p]) := by
    rw [hg, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_one, zero_add,
      eval_one_cyclotomic_prime_pow]
  have hgroots : g.roots = (cyclotomic (p ^ (m + 1)) ℂ_[p]).roots.map (· - 1) := by
    rw [hg]; simpa using roots_comp_C_mul_X_add_C (cyclotomic (p ^ (m + 1)) ℂ_[p]) 1 1 isUnit_one
  have hcard : Multiset.card (cyclotomic (p ^ (m + 1)) ℂ_[p]).roots
      = Nat.totient (p ^ (m + 1)) := by
    have hcr : Multiset.card g.roots = g.natDegree := splits_iff_card_roots.mp hgsplits
    rw [hgroots, Multiset.card_map] at hcr; rw [hcr, hgdeg]
  have hprodnorm : ‖g.roots.prod‖ = ‖pi p (m + 1)‖ ^ Nat.totient (p ^ (m + 1)) := by
    rw [hgroots, show ‖((cyclotomic (p ^ (m + 1)) ℂ_[p]).roots.map (· - 1)).prod‖
        = (((cyclotomic (p ^ (m + 1)) ℂ_[p]).roots.map (· - 1)).map (‖·‖)).prod from
      map_multiset_prod (normHom (α := ℂ_[p])).toMonoidHom _, Multiset.map_map,
      show (((cyclotomic (p ^ (m + 1)) ℂ_[p]).roots).map ((‖·‖) ∘ (· - 1)))
          = (cyclotomic (p ^ (m + 1)) ℂ_[p]).roots.map (fun _ => ‖pi p (m + 1)‖) from
        Multiset.map_congr rfl (fun r hr => norm_root_sub_one_eq p r hr),
      Multiset.map_const', Multiset.prod_replicate, hcard]
  have hcoeff_prod : g.coeff 0 = (-1) ^ g.natDegree * g.roots.prod :=
    hgsplits.coeff_zero_eq_prod_roots_of_monic hgmonic
  have hpnorm : ‖g.roots.prod‖ = (p : ℝ)⁻¹ := by
    have heq : ‖g.coeff 0‖ = ‖g.roots.prod‖ := by
      rw [hcoeff_prod, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [← heq, hgc0,
      show ((p : ℂ_[p])) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) by rw [map_natCast],
      norm_algebraMap', Padic.norm_p]
  rw [← hprodnorm, hpnorm]

theorem norm_pi_lt_one {n : ℕ} (hn : 1 ≤ n) : ‖pi p n‖ < 1 :=
  (zetaSys_primitiveRoot p n).norm_sub_one_lt hn

theorem pi_ne_zero {n : ℕ} (hn : 1 ≤ n) : pi p n ≠ 0 := by
  rw [pi, sub_ne_zero]
  exact (zetaSys_primitiveRoot p n).ne_one (one_lt_pow₀ hp.out.one_lt (by omega))

/-- R9: the integer ring `O_n = O_{K_n}` — the norm-unit-ball of `K_n`
(equivalently the integral closure of `ℤ_p`; the identification is the
Eisenstein-monogenicity ticket). RJW TeX 2474. -/
noncomputable def O (n : ℕ) : Subring ℂ_[p] :=
  (K p n).toSubring ⊓ integerRing ℂ_[p]

theorem pi_mem_O {n : ℕ} (hn : 1 ≤ n) : pi p n ∈ O p n := by
  rw [O, Subring.mem_inf]
  exact ⟨pi_mem_K p n, (norm_pi_lt_one p hn).le⟩

set_option synthInstance.maxHeartbeats 400000 in
-- the `Module.finrank_mul_finrank` tower needs `Module.Free (K p n) (extendScalars …)`,
-- whose synthesis through the `IntermediateField.extendScalars` layer exceeds the default
/-- R10.2 (tower step): the minimal polynomial of `ξ_{p^{n+1}}` over `K_n`
is `X^p − ξ_{p^n}` (RJW TeX 2685: "the minimal polynomial of `ξ_{p^{n+1}}`
over `K_n` is `X^p − ξ_{p^n}`"). Stated as the two halves that downstream
proofs consume: the degree of the tower step is `p`, and `ξ_{p^{n+1}}` is
a root of `X^p − ξ_{p^n}` (the latter is `zetaSys_pow_p`).

Statement note (T902): n ≥ 1 added — the first step of the tower has degree
p − 1 = φ(p), not p. -/
theorem finrank_K_succ {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank (K p n) (IntermediateField.extendScalars (K_le_succ p n))
      = p := by
  haveI : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos n).ne'⟩
  haveI : NeZero (p ^ (n + 1)) := ⟨(pow_pos hp.out.pos (n + 1)).ne'⟩
  have htower := Module.finrank_mul_finrank ℚ_[p] (K p n)
    (IntermediateField.extendScalars (K_le_succ p n))
  have htop : Module.finrank ℚ_[p] (IntermediateField.extendScalars (K_le_succ p n))
      = Nat.totient (p ^ (n + 1)) := finrank_K p (n + 1)
  rw [finrank_K p n, htop] at htower
  have hratio : Nat.totient (p ^ (n + 1)) = p * Nat.totient (p ^ n) := by
    rw [Nat.totient_prime_pow hp.out (by omega : 0 < n + 1),
      Nat.totient_prime_pow hp.out hn, Nat.add_sub_cancel]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, ← mul_assoc, ← pow_succ']
  rw [hratio] at htower
  exact (Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.2 (pow_pos hp.out.pos n))
    (by linarith [htower])).symm

end Coleman

end PadicLFunctions
