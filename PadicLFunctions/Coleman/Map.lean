/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Coleman.Tower
import PadicLFunctions.KubotaLeopoldt.MuA

/-!
# The cyclotomic units and the Coleman map input layer (RJW §10.2, TeX 2572–2628)

This file builds the *cyclotomic units* of the local tower `K_n = ℚ_p(μ_{p^n})`
and the two power-series identities that feed the Coleman-map computation of the
`p`-adic `ζ`-function.

* `cycloUnit a n = (ξ_{p^n}^a − 1)/(ξ_{p^n} − 1)` — the element `c_n(a)` of
  RJW TeX 2573. For `a` coprime to `p` it is a unit of `𝒪_n` of norm `1`
  (`cycloUnit_mem_O`, `norm_cycloUnit`): numerator and denominator are both
  conjugates `η − 1` of the uniformiser `π_n` (each a primitive `p^n`-th root
  minus one), so they have equal `ℂ_p`-norm.
* `cyclo a ha hp2 : NormCompatUnits` — the *packaged tower* `c(a) = (c_n(a))_n`
  (RJW TeX 2577), a norm-compatible system of units. Level `0` is set to `1`
  (the `n = 0` value `(1^a−1)/(1−1) = 0/0` is not a unit, and the
  `NormCompatUnits.compat` field only constrains `n ≥ 1`); the norm
  compatibility `N_{n+1,n}(c_{n+1}(a)) = c_n(a)` is the tower engine
  `levelNorm_zetaSys_pow_sub_one` applied twice (RJW TeX 2581–2585).
* `one_add_mul_derivative_log_geomSum` — the cleared form of
  `∂log f_{c(a)} = (a−1) − F_a` (RJW prop:coleman zetap, TeX 2595–2608), where
  `f_{c(a)} = geomSum a = ((1+T)^a−1)/T`: `(1+T)·(geomSum a)′ = ((a−1)−F_a)·geomSum a`.
* `res_derivative_log_geomSum` — the residue relation
  `Res_{ℤ_p^×}(μ_{(a−1)−F_a}) = −Res_{ℤ_p^×}(μ_a)` (RJW lem:relate cyclo to mua,
  TeX 2611–2624), realised at the measure level: the constant series `a−1` has
  zero residue (it is the Mahler transform of `(a−1)·δ_0`, and `0 ∉ ℤ_p^×`).
-/

open PowerSeries

namespace PadicLFunctions

namespace Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## Norm of the cyclotomic numerator and denominator

RJW TeX 2573–2576. Both `ξ_{p^n}^a − 1` and `ξ_{p^n} − 1` are of the form
`η − 1` with `η` a primitive `p^n`-th root of unity (`a` coprime to `p`), hence
have equal `ℂ_p`-norm. The three lemmas below reproduce the (private) Tower
helpers `norm_primitiveRoot_eq_one`/`norm_pow_sub_one_le`/`norm_sub_one_eq`. -/

/-- The norm of a primitive `p^n`-th root of unity in `ℂ_p` is `1`
(`‖ξ‖^{p^n} = 1` forces `‖ξ‖ = 1`). (Reproduced from `Tower`'s private helper.) -/
private theorem norm_primitiveRoot_eq_one {n : ℕ} {ξ : ℂ_[p]}
    (hξ : IsPrimitiveRoot ξ (p ^ n)) : ‖ξ‖ = 1 := by
  have h1 : ‖ξ‖ ^ (p ^ n) = 1 := by rw [← norm_pow, hξ.pow_eq_one, norm_one]
  have hne : p ^ n ≠ 0 := (pow_pos hp.out.pos n).ne'
  refine le_antisymm ?_ ?_
  · by_contra h; rw [not_le] at h; exact absurd h1 (one_lt_pow₀ h hne).ne'
  · by_contra h; rw [not_le] at h; exact absurd h1 (pow_lt_one₀ (norm_nonneg ξ) h hne).ne

/-- For a norm-one element `ξ` of `ℂ_p`, `‖ξ^c − 1‖ ≤ ‖ξ − 1‖`: factor
`ξ^c − 1 = (∑_{i<c} ξ^i)(ξ − 1)` and bound the geometric factor by `1`
(ultrametric sum of norm-one terms). (Reproduced from `Tower`.) -/
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
`norm_pow_sub_one_le` gives both inequalities. (Reproduced from `Tower`.) -/
private theorem norm_sub_one_eq {n : ℕ} {ξ η : ℂ_[p]}
    (hξ : IsPrimitiveRoot ξ (p ^ n)) (hη : IsPrimitiveRoot η (p ^ n)) :
    ‖ξ - 1‖ = ‖η - 1‖ := by
  haveI : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos n).ne'⟩
  obtain ⟨i, _, hi⟩ := hξ.eq_pow_of_pow_eq_one hη.pow_eq_one
  obtain ⟨j, _, hj⟩ := hη.eq_pow_of_pow_eq_one hξ.pow_eq_one
  refine le_antisymm ?_ ?_
  · rw [← hj]; exact norm_pow_sub_one_le p (norm_primitiveRoot_eq_one p hη) j
  · rw [← hi]; exact norm_pow_sub_one_le p (norm_primitiveRoot_eq_one p hξ) i

/-- `ξ_{p^n}^a` is a primitive `p^n`-th root of unity when `a` is coprime to `p`
(equivalently to `p^n`). The numerator generator of `cycloUnit p a n`. -/
private theorem zetaSys_pow_primitiveRoot {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (n : ℕ) :
    IsPrimitiveRoot (zetaSys p n ^ a) (p ^ n) :=
  (zetaSys_primitiveRoot p n).pow_of_coprime a
    (Nat.Coprime.pow_right _ (hp.out.coprime_iff_not_dvd.2 ha).symm)

/-- **The numerator and denominator of `c_n(a)` have equal norm** (RJW TeX 2573):
`‖ξ_{p^n}^a − 1‖ = ‖ξ_{p^n} − 1‖`. Both are `η − 1` for a primitive `p^n`-th
root `η`, so `norm_sub_one_eq` applies. -/
private theorem norm_zetaSys_pow_sub_one_eq {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (n : ℕ) :
    ‖zetaSys p n ^ a - 1‖ = ‖zetaSys p n - 1‖ :=
  norm_sub_one_eq p (zetaSys_pow_primitiveRoot p ha n) (zetaSys_primitiveRoot p n)

/-! ## The cyclotomic unit `c_n(a)` (RJW TeX 2573) -/

/-- **RJW TeX 2573**: the cyclotomic unit `c_n(a) = (ξ_{p^n}^a − 1)/(ξ_{p^n} − 1)`
of the local field `K_n`. (At level `0` it is the junk value `0/0 = 0`; the
packaged tower `cyclo` overrides level `0` by `1`.) -/
noncomputable def cycloUnit (a n : ℕ) : ℂ_[p] :=
  (zetaSys p n ^ a - 1) / (zetaSys p n - 1)

/-- `c_n(a) ∈ K_n`: both `ξ_{p^n}^a − 1` and `ξ_{p^n} − 1` lie in `K_n`, and `K_n`
is a field (`IntermediateField.div_mem`). -/
theorem cycloUnit_mem_K (a : ℕ) {n : ℕ} (_hn : 1 ≤ n) : cycloUnit p a n ∈ K p n := by
  rw [cycloUnit]
  exact (K p n).div_mem
    (sub_mem (pow_mem (zetaSys_mem_K p n) a) (one_mem _))
    (sub_mem (zetaSys_mem_K p n) (one_mem _))

/-- The denominator `ξ_{p^n} − 1` of `c_n(a)` is nonzero for `n ≥ 1`. -/
private theorem zetaSys_sub_one_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    zetaSys p n - 1 ≠ 0 :=
  sub_ne_zero_of_ne
    ((zetaSys_primitiveRoot p n).ne_one (one_lt_pow₀ hp.out.one_lt (by omega)))

/-- `c_n(a)` has norm `1` (RJW TeX 2573): numerator and denominator are conjugate
uniformisers of equal norm (`norm_zetaSys_pow_sub_one_eq`). -/
theorem norm_cycloUnit {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) {n : ℕ} (hn : 1 ≤ n) :
    ‖cycloUnit p a n‖ = 1 := by
  rw [cycloUnit, norm_div, norm_zetaSys_pow_sub_one_eq p ha n,
    div_self (norm_ne_zero_iff.mpr (zetaSys_sub_one_ne_zero p hn))]

/-- `c_n(a)` is nonzero (its norm is `1`). -/
theorem cycloUnit_ne_zero {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) {n : ℕ} (hn : 1 ≤ n) :
    cycloUnit p a n ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_cycloUnit p ha hn]; exact one_ne_zero)

/-- **RJW TeX 2573**: `c_n(a) ∈ 𝒪_n` — it lies in `K_n` and has norm `1 ≤ 1`. -/
theorem cycloUnit_mem_O {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) {n : ℕ} (hn : 1 ≤ n) :
    cycloUnit p a n ∈ O p n := by
  rw [O, Subring.mem_inf]
  exact ⟨cycloUnit_mem_K p a hn, show ‖cycloUnit p a n‖ ≤ 1 from
    (norm_cycloUnit p ha hn).le⟩

/-- `c_n(a)⁻¹ = (ξ_{p^n} − 1)/(ξ_{p^n}^a − 1) ∈ 𝒪_n` — the same argument with
numerator and denominator swapped (norm `1`, in `K_n`). -/
theorem inv_cycloUnit_mem_O {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) {n : ℕ} (hn : 1 ≤ n) :
    (cycloUnit p a n)⁻¹ ∈ O p n := by
  rw [O, Subring.mem_inf]
  refine ⟨(K p n).inv_mem (cycloUnit_mem_K p a hn), show ‖(cycloUnit p a n)⁻¹‖ ≤ 1 from ?_⟩
  rw [norm_inv, norm_cycloUnit p ha hn, inv_one]

/-! ## The packaged cyclotomic-unit tower `c(a)` (RJW TeX 2577) -/

/-- The level norm of an inverse in `K_{n+1}`: for `x ∈ K_{n+1}` with
`levelNorm p n x ≠ 0`, `levelNorm p n x⁻¹ = (levelNorm p n x)⁻¹`. From
multiplicativity `levelNorm x · levelNorm x⁻¹ = levelNorm 1 = 1` (`x⁻¹ ∈ K_{n+1}`
as `K_{n+1}` is a field). -/
private theorem levelNorm_inv {n : ℕ} {x : ℂ_[p]} (hx : x ∈ K p (n + 1))
    (hx0 : x ≠ 0) :
    levelNorm p n x⁻¹ = (levelNorm p n x)⁻¹ := by
  have hxinv : x⁻¹ ∈ K p (n + 1) := (K p (n + 1)).inv_mem hx
  have hmul : levelNorm p n x * levelNorm p n x⁻¹ = 1 := by
    rw [← levelNorm_mul p n hx hxinv, mul_inv_cancel₀ hx0, levelNorm_one]
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hmul)

/-- The level norm of a quotient in `K_{n+1}`: for `x, y ∈ K_{n+1}` with
`y ≠ 0`, `levelNorm p n (x/y) = levelNorm p n x / levelNorm p n y`. -/
private theorem levelNorm_div {n : ℕ} {x y : ℂ_[p]} (hx : x ∈ K p (n + 1))
    (hy : y ∈ K p (n + 1)) (hy0 : y ≠ 0) :
    levelNorm p n (x / y) = levelNorm p n x / levelNorm p n y := by
  rw [div_eq_mul_inv, levelNorm_mul p n hx ((K p (n + 1)).inv_mem hy),
    levelNorm_inv p hy hy0, div_eq_mul_inv]

/-- **Norm compatibility of the cyclotomic units** (RJW TeX 2581–2585):
`N_{n+1,n}(c_{n+1}(a)) = c_n(a)` for `n ≥ 1`. Apply the norm collapse
`levelNorm_zetaSys_pow_sub_one` to the numerator (`b = a`) and to the denominator
(`b = 1`, i.e. `levelNorm_pi`), then take the quotient. -/
theorem levelNorm_cycloUnit {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 1 ≤ n) : levelNorm p n (cycloUnit p a (n + 1)) = cycloUnit p a n := by
  have hnumK : zetaSys p (n + 1) ^ a - 1 ∈ K p (n + 1) :=
    sub_mem (pow_mem (zetaSys_mem_K p (n + 1)) a) (one_mem _)
  have hdenK : zetaSys p (n + 1) - 1 ∈ K p (n + 1) :=
    sub_mem (zetaSys_mem_K p (n + 1)) (one_mem _)
  -- the denominator's level norm is `π_n = ξ_n − 1`, via `levelNorm_pi`
  have hden : levelNorm p n (zetaSys p (n + 1) - 1) = zetaSys p n - 1 := by
    have h := levelNorm_pi p hn hp2
    rwa [pi, pi] at h
  rw [cycloUnit, levelNorm_div p hnumK hdenK (zetaSys_sub_one_ne_zero p (by omega)),
    levelNorm_zetaSys_pow_sub_one p hn hp2 ha, hden, cycloUnit]

/-- **RJW TeX 2577**: the packaged cyclotomic-unit tower `c(a) = (c_n(a))_n` as a
norm-compatible system of units `NormCompatUnits`. Level `0` is set to `1` (the
formal value `(1^a−1)/(1−1)` is not a unit, and `NormCompatUnits.compat` is only
imposed for `n ≥ 1`); for `n ≥ 1` the unit is `c_n(a)` (norm `1`, in `𝒪_n`, with
inverse in `𝒪_n`), and norm compatibility is `levelNorm_cycloUnit`. -/
noncomputable def cyclo {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (hp2 : p ≠ 2) :
    NormCompatUnits p where
  elems n :=
    if hn : 1 ≤ n then Units.mk0 (cycloUnit p a n) (cycloUnit_ne_zero p ha hn) else 1
  mem n := by
    by_cases hn : 1 ≤ n
    · rw [dif_pos hn, Units.val_mk0]; exact cycloUnit_mem_O p ha hn
    · rw [dif_neg hn]; exact one_mem _
  inv_mem n := by
    by_cases hn : 1 ≤ n
    · rw [dif_pos hn,
        show ((Units.mk0 (cycloUnit p a n) (cycloUnit_ne_zero p ha hn))⁻¹ : ℂ_[p])
          = (cycloUnit p a n)⁻¹ from rfl]
      exact inv_cycloUnit_mem_O p ha hn
    · rw [dif_neg hn, show (((1 : ℂ_[p]ˣ) : ℂ_[p]))⁻¹ = 1 from by rw [Units.val_one, inv_one]]
      exact one_mem _
  compat n hn := by
    have hn1 : 1 ≤ n + 1 := by omega
    rw [dif_pos hn1, dif_pos hn, Units.val_mk0, Units.val_mk0]
    exact levelNorm_cycloUnit p ha hp2 hn
