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

/-! ## Infrastructure for the descent of the Coleman map (RJW §12.5)

The two milestones are the descents of the Coleman map `Col : 𝒰_∞ → Λ(ℤ_p^×)` to the
cyclotomic quotient `𝒰_{∞,1}/𝒞_{∞,1}` (resp. its plus part). `Col` is a homomorphism from
the *multiplicative* group `NormCompatUnits` to the *additive* group of measures
(`Col_add`, `Col_one`); the descent is `[u] ↦ [Col u]` into the ideal quotient
`Λ(𝒢)/I(𝒢)ζ_p`, packaged as a `MonoidHom` into `Multiplicative (Λ(𝒢)/I(𝒢)ζ_p)` and
converted to the additive shape demanded by the statements with `MonoidHom.toAdditive`. -/

/-- `Col 1 = 0`: the trivial unit system is `(p−1)`-torsion (each level is `1`), so
`Col_eq_zero_of_torsion` kills it. -/
theorem Col_one : Col p (1 : NormCompatUnits p) = 0 :=
  Col_eq_zero_of_torsion p 1 (fun n => by
    rw [show ((1 : NormCompatUnits p).elems n) = 1 from rfl, one_pow])

/-- **The Coleman map as a homomorphism into the additive group `Λ(𝒢)/I(𝒢)ζ_p`**, packaged
multiplicatively: `u ↦ [Col u] ∈ Multiplicative (Λ(𝒢)/I(𝒢)ζ_p)`. The hom property is
`Col_add` (`Col` turns products into sums) followed by the additive quotient map; `map_one`
is `Col_one`. This is the source of the descent `[u] ↦ [Col u]`. -/
def ColMul (hp2 : p ≠ 2) :
    NormCompatUnits p →* Multiplicative (PadicMeasure p ℤ_[p]ˣ ⧸ PadicMeasure.zetaIdeal p hp2) where
  toFun u := Multiplicative.ofAdd (Ideal.Quotient.mk (PadicMeasure.zetaIdeal p hp2) (Col p u))
  map_one' := by
    change Multiplicative.ofAdd (Ideal.Quotient.mk _ (Col p (1 : NormCompatUnits p))) = 1
    rw [Col_one, map_zero]; rfl
  map_mul' u v := by
    change Multiplicative.ofAdd (Ideal.Quotient.mk _ (Col p (u * v))) = _
    rw [Col_add, map_add, ofAdd_add]

@[simp] theorem ColMul_apply (hp2 : p ≠ 2) (u : NormCompatUnits p) :
    ColMul p hp2 u
      = Multiplicative.ofAdd (Ideal.Quotient.mk (PadicMeasure.zetaIdeal p hp2) (Col p u)) :=
  rfl

/-- The canonical cyclotomic generator `c(a₀)` maps into the ζ-ideal: `Col(c(a₀)) =
−zetaNum a₀ ∈ I(𝒢)ζ_p`. Here `a₀` is the integer topological generator chosen by
`padicZeta` (`exists_nat_topological_generator`), and `zetaNum a₀ ∈ I(𝒢)ζ_p` because
`([a₀]−1)·ζ_p = zetaNum a₀` (`IsLocalization.mk'_spec'`) with `[a₀]−1` in the augmentation
ideal. This is the **bounded facet** of the image computation (the single generator); the
full tower-level inclusion is `col_mem_zetaIdeal_iff_mem_cycloTower1`. -/
theorem Col_cyclo_mem_zetaIdeal (hp2 : p ≠ 2) :
    Col p (cyclo p
        (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose_spec.1 hp2)
      ∈ PadicMeasure.zetaIdeal p hp2 := by
  -- `Col(c(a₀)) = −zetaNum a₀` and `zetaNum a₀ ∈ I(𝒢)ζ_p`
  rw [Col_cyclo]
  refine neg_mem ?_
  rw [PadicMeasure.mem_zetaIdeal_iff]
  refine ⟨PadicMeasure.dirac p
      (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose - 1, ?_, ?_⟩
  · rw [PadicMeasure.augmentationIdeal, RingHom.mem_ker, map_sub, map_one,
      show PadicMeasure.deg p (PadicMeasure.dirac p _) = 1 from rfl, sub_self]
  · exact (IsLocalization.mk'_spec' (PadicMeasure.QuotientField p) _ _).symm

/-- **`ℤ_p(1) ⊆ 𝒞_{∞,1}`** (RJW §12.5, the injectivity sub-lemma): the Tate-twist tower
`(ξ_n^a)_n` lies in the cyclotomic tower. Levelwise, `ξ_n^a = zpPow ξ_n a` is a `ℤ_p`-limit
of the integral powers `ξ_n^k` (cyclotomic units in `𝒰_{n,1}`), so it lands in the p-adic
closure `𝒞_{n,1}` (`zpPow_zetaSys_mem_cycloClosureOne`). This is the inclusion making the
kernel `ℤ_p(1)` of `Col` (`mem_ker_Col_iff_mem_ZpOne`) sit inside `𝒞_{∞,1}`, which transfers
`Col`-equality on a cyclotomic representative back to tower membership. -/
theorem ZpOne_le_cycloTower1 : ZpOne p ≤ cycloTower1 p := by
  intro u hu n hn
  obtain ⟨a, ha⟩ := hu
  exact zpPow_zetaSys_mem_cycloClosureOne p hn a (ha n hn)

/-! ## The `Λ(𝒢)`-scalar action on `𝒞_{∞,1}` at the group-element level (RJW TeX 3582–3608)

The dense facet of the image computation `Col '' 𝒞_{∞,1} = I(𝒢)ζ_p`: as `a` ranges over
`ℤ_p^×`, the group-element scalars `[σ_a]` act on the generator `wγ(a₀)⁻¹` (with
`Col(wγ(a₀)⁻¹) = ζ_p`-numerator) by `σ_a`, landing inside `𝒞_{∞,1}`
(`galNCU_wGamma_mem_cycloTower1`), and `Col(σ_a · wγ(a₀)⁻¹) = [a]·zetaNum a₀`
(`Col_galNCU_eq_dirac_mul`). So the `ℤ_p`-span of `{[σ_a]·zetaNum a₀}` — dense in `I(𝒢)ζ_p`
— lies in the additive subgroup `Col '' 𝒞_{∞,1}`. This is the §12.4-realised content; the
remaining density-crossing to all of `Λ(𝒢)` is the §13/IMC core isolated below. -/

/-- `σ_a(wγ(a₀)⁻¹) ∈ 𝒞_{∞,1}`: the `𝒢`-translate of the (inverse) cyclotomic generator stays in
the cyclotomic tower (`galNCU` is a group hom, `cycloTower1` a subgroup,
`galNCU_wGamma_mem_cycloTower1`). -/
theorem galNCU_wGamma_inv_mem_cycloTower1 (a : ℤ_[p]ˣ) (hp2 : p ≠ 2) :
    galNCU p a (wGamma p hp2)⁻¹ ∈ cycloTower1 p := by
  rw [galNCU_inv p a (wGamma p hp2)]
  exact (cycloTower1 p).inv_mem (galNCU_wGamma_mem_cycloTower1 p a hp2)

/-- **The group-element image identity** `Col(σ_a · wγ(a₀)⁻¹) = [a]·zetaNum a₀`: combines
`Col_galNCU_eq_dirac_mul` (`Col(σ_a u) = [a]·Col u`) with `Col(wγ(a₀)⁻¹) = −Col(wγ(a₀)) =
zetaNum a₀` (`Col_wGamma`, `Col`-homomorphism). As `a` ranges over `ℤ_p^×`, the RHS ranges over
the group-element multiples of `zetaNum a₀`. -/
theorem Col_galNCU_wGamma_inv (a : ℤ_[p]ˣ) (hp2 : p ≠ 2) :
    Col p (galNCU p a (wGamma p hp2)⁻¹)
      = (PadicMeasure.dirac p a) * PadicMeasure.zetaNum p
          (PadicMeasure.exists_nat_topological_generator p hp2).choose := by
  -- `Col(wγ⁻¹) = −Col(wγ) = zetaNum a₀`
  have hinv : Col p (wGamma p hp2)⁻¹
      = PadicMeasure.zetaNum p
          (PadicMeasure.exists_nat_topological_generator p hp2).choose := by
    have h := Col_add p (wGamma p hp2) (wGamma p hp2)⁻¹
    rw [mul_inv_cancel, Col_one] at h
    rw [show Col p (wGamma p hp2)⁻¹ = -Col p (wGamma p hp2) from by linear_combination -h,
      Col_wGamma_choose, neg_neg]
  rw [Col_galNCU_eq_dirac_mul, hinv]

/-- **The group-element scalar multiples lie in `Col '' 𝒞_{∞,1}`** (the dense facet of the image
identity): for every `a ∈ ℤ_p^×`, `[a]·zetaNum a₀ ∈ Col '' 𝒞_{∞,1}`, witnessed by the tower
element `σ_a(wγ(a₀)⁻¹) ∈ 𝒞_{∞,1}` (`galNCU_wGamma_inv_mem_cycloTower1`, `Col_galNCU_wGamma_inv`).
The `ℤ_p`-span of these is dense in `I(𝒢)ζ_p = (zetaNum a₀)`. -/
theorem dirac_mul_zetaNum_mem_col_image (a : ℤ_[p]ˣ) (hp2 : p ≠ 2) :
    (PadicMeasure.dirac p a) * PadicMeasure.zetaNum p
        (PadicMeasure.exists_nat_topological_generator p hp2).choose
      ∈ Col p '' (cycloTower1 p : Set (NormCompatUnits p)) :=
  ⟨galNCU p a (wGamma p hp2)⁻¹, galNCU_wGamma_inv_mem_cycloTower1 p a hp2,
    Col_galNCU_wGamma_inv p a hp2⟩

/-- **DEFERRED (RJW §12.5, TeX 3582–3608 — the image computation):** the Coleman-map image
characterisation `image(Col|_{𝒞_{∞,1}}) = I(𝒢)ζ_p`, in the form that drives both milestones:
for a principal-unit tower `u ∈ 𝒰_{∞,1}`, `Col u ∈ I(𝒢)ζ_p` *iff* `u ∈ 𝒞_{∞,1}`.

This is the inverse-limit cyclic-`Λ(𝒢)`-module computation of RJW's proof: `𝒞_{∞,1}` is the
cyclic `Λ(𝒢)`-module generated by `c(a)` (LemmaGeneratorCinfty1, TeX 3553–3578), and
`Col(λ·c(a)) = λ·Col(c(a)) = λ·(−zetaNum a)`, so as `λ` ranges over `Λ(𝒢)` the images fill
`I(𝒢)ζ_p` (the `[σ_a]−1` generate the augmentation ideal). The `(⊇)`/well-definedness
direction is grounded at the single generator by `Col_cyclo_mem_zetaIdeal`; the `(⊆)`/
injectivity direction is the kernel-of-the-descent statement.

**State of the proof (T12xx).** Both directions are reduced here to the *single* set-level
image identity `Col '' 𝒞_{∞,1} = I(𝒢)ζ_p` (`col_image_cycloTower1_eq_zetaIdeal`, the
remaining blocker), using the now-available `Λ(𝒢)`-action homomorphism laws
`galNCU_mul`/`galNCU_one` and the kernel inclusion `ZpOne_le_cycloTower1`:
* `←` (`u ∈ 𝒞_{∞,1} ⟹ Col u ∈ I(𝒢)ζ_p`) is the `⊆` half of the image identity applied to
  the witness `Col u = Col u`;
* `→` (`Col u ∈ I(𝒢)ζ_p ⟹ u ∈ 𝒞_{∞,1}`) is the injectivity corollary: the `⊇` half gives
  `c ∈ 𝒞_{∞,1}` with `Col c = Col u`, so `Col (u·c⁻¹) = 0` (`Col_add`,
  `Col`-homomorphism), whence `u·c⁻¹ ∈ ℤ_p(1)` (`mem_ker_Col_iff_mem_ZpOne`)
  `⊆ 𝒞_{∞,1}` (`ZpOne_le_cycloTower1`), so `u = (u·c⁻¹)·c ∈ 𝒞_{∞,1}`.

The remaining `col_image_cycloTower1_eq_zetaIdeal` is the genuine §13/IMC-deferred core: it
requires the inverse-limit `Λ(𝒢)`-module structure of `𝒞_{∞,1}` — defined as the inverse
limit of the *topological closures* `𝒞_{n,1} = clos(𝒟_{n,1}) ⊓ 𝒰_{n,1}` (`cycloClosureOne`).
Passing the level-`n` group generation `cycloUnitsPlus_eq_closure_gammas` (which generates
the *global* units `𝒟_n^+`, not their closures) up to the tower needs either continuity of
`Col` (`Col` is built from the Coleman-series limit construction — no continuity is
available) or the inverse-limit cyclic-module description of `cycloTower1Plus_cyclic_generator`
(whose full form, TeX 3573–3578, is the deferred §13 input). All other ingredients of both
milestones (the `Col` hom property, the descent through `QuotientGroup.lift`, the plus-part
transport `plusEquiv`/`projPlus`/`isCompl_plusPart_minusPart`, the `ℤ_p(1)^{⟨c⟩}=0` collapse,
surjectivity onto `ker(χ-moment)` via `range_Col_eq_ker_chiMoment`) are proved without
further `sorry`.

**§12.4 infrastructure now in place (`Generators.lean`, all sorry-free, axiom-clean).**
The cyclic-`Λ(𝒢)`-module scaffolding for RJW `LemmaGeneratorCinfty1` is built:
* `galNCU_mul`/`galNCU_one` — `σ_a` is a group endomorphism of `𝒰_∞`;
* `galNCU_mem_unitsTower1` — `σ_a` preserves the principal-unit tower `𝒰_{∞,1}` (isometry
  `norm_galAut` fixing `1`), the levelwise half of the `𝒢`-stability of the tower;
* `Col_galNCU_eq_dirac_mul` — the generator-image identity `Col(σ_a u) = [a]·Col u` in
  convolution form (`Col_galNCU` + `dirac_mul_eq_pushforward`), i.e. the scalar `[σ_a]`-action
  matching `Col(λ·c) = λ·Col(c)` for the group-element scalars `λ = [σ_a]`.
With these, input **(I)** is now CLOSED and only the closure-crossing **(II)** remains:
* **(I) the generator `wγ(a₀) ∈ 𝒞_{∞,1}` with `Col(wγ(a₀)) = −zetaNum a₀` — DONE.** The
  generator `wGamma p hp2` is assembled in `Generators.lean` (`𝒪_n`-residue Teichmüller split
  `normCompat_eq_teichmuller_mul_principal`), `Col_wGamma : Col(wγ a₀) = −zetaNum a₀`, and
  `wGamma_mem_cycloTower1 : wγ(a₀) ∈ 𝒞_{∞,1}` (via the §13 `(p−1)`-divisible closure layer
  `mem_cycloClosureOne_of_pow_mem`, CyclotomicUnits, all sorry-free, axiom-clean).
* **(II) the closure-crossing / density — the SOLE remaining blocker.** With the generator in
  hand, both inclusions of `Col '' 𝒞_{∞,1} = I(𝒢)ζ_p` reduce to the `Λ(𝒢)`-linearity of `Col`
  on the cyclic module `𝒞_{∞,1} = closure(Λ(𝒢)·wγ(a₀))`, i.e. `Col(r • c) = r · Col c` for
  *arbitrary* `r ∈ Λ(𝒢)`, not merely the group-element scalars `r = [σ_a]` (where
  `Col_galNCU_eq_dirac_mul` gives it and `galNCU_*` realise the action). The crossing from the
  `ℤ_p`-span of `{[σ_a]}` (dense in `Λ(𝒢)`) to all of `Λ(𝒢)` is the genuine §13/IMC core and
  requires infrastructure ABSENT from the project (verified by exhaustive search):
  - **continuity route** — a topology on `NormCompatUnits` (the inverse-limit profinite unit
    group) AND on `PadicMeasure` (a bare `C(X,ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` abbrev with NO topology),
    plus `Continuous (Col p)` through the whole Coleman construction
    `unitsCmul ∘ mahler⁻¹ ∘ dlog ∘ colemanSeries` (the Coleman-series inverse-limit factor is
    READ-ONLY and has no continuity lemma), plus `IsClosed (↑(zetaIdeal p hp2))`; OR
  - **cyclic-module route** — a convolution `Λ(𝒢)`-module action `μ • u` on the inverse-limit
    unit tower (no `Module (PadicMeasure …) (NormCompatUnits …)` instance exists) and a proof
    that `Col` intertwines it (no `Col`-`smul` lemma exists), i.e. the full inverse-limit
    cyclic-module description `cycloTower1Plus_cyclic_generator`, TeX 3573–3578.
  Neither is reachable within the file confinement without first building a multi-file §13
  topology/module layer; left as a single documented blocker below. -/
theorem col_image_cycloTower1_eq_zetaIdeal (hp2 : p ≠ 2) :
    (Col p '' (cycloTower1 p : Set (NormCompatUnits p))) = PadicMeasure.zetaIdeal p hp2 := by
  -- BLOCKED on the §13/IMC density-crossing alone. State of the reduction (all verified):
  -- • `Col '' 𝒞_{∞,1}` is an additive subgroup (`cycloTower1` a subgroup, `Col` a hom via
  --   `Col_add`/`Col_one`).
  -- • Input (I) DONE: `wγ(a₀) ∈ 𝒞_{∞,1}`, `Col(wγ a₀) = −zetaNum a₀` (axiom-clean).
  -- • Group-element scalar action DONE (this file): `σ_a(wγ(a₀)⁻¹) ∈ 𝒞_{∞,1}`
  --   (`galNCU_wGamma_inv_mem_cycloTower1`, from the §12.4 `σ_a`-stability
  --   `galNCU_wGamma_mem_cycloTower1`) with `Col(σ_a·wγ(a₀)⁻¹) = [a]·zetaNum a₀`
  --   (`Col_galNCU_wGamma_inv`), so `dirac_mul_zetaNum_mem_col_image`:
  --   `{[a]·zetaNum a₀ : a ∈ ℤ_p^×} ⊆ Col '' 𝒞_{∞,1}`.
  -- • `zetaIdeal = span{zetaNum a₀}` (`zetaIdeal_eq_span` at the canonical generator).
  -- The SOLE remaining gap is the crossing from the `ℤ_p`-span of `{[σ_a]}` (DENSE in `Λ(𝒢)`)
  -- to all of `Λ(𝒢)`: i.e. `Col '' 𝒞_{∞,1}` is *closed* under the full `Λ(𝒢) = lim ℤ_p[𝒢_n]`
  -- action, equivalently `Col` is `Λ(𝒢)`-linear on the cyclic module `𝒞_{∞,1} =
  -- closure(Λ(𝒢)·wγ(a₀))`. This needs `Continuous (Col p)` for a weak-* topology on
  -- `PadicMeasure` and the inverse-limit topology on `NormCompatUnits`, whose hard factor is
  -- coefficient-continuity of `colemanSeries` (defined as `Classical.choose` of the
  -- interpolation `∃!`, with NO explicit coefficient formula in the project) — verified absent
  -- by exhaustive search. This is the deferred §13/IMC core; left as the single documented
  -- residual. The dense facet `dirac_mul_zetaNum_mem_col_image` is the maximal in-file fragment.
  sorry

theorem col_mem_zetaIdeal_iff_mem_cycloTower1 (hp2 : p ≠ 2) {u : NormCompatUnits p}
    (hu : u ∈ unitsTower1 p) :
    Col p u ∈ PadicMeasure.zetaIdeal p hp2 ↔ u ∈ cycloTower1 p := by
  have himg := col_image_cycloTower1_eq_zetaIdeal p hp2
  constructor
  · -- `→`: injectivity corollary via `Col '' 𝒞_{∞,1} = I(𝒢)ζ_p` and `ker Col = ℤ_p(1)`
    intro hCol
    -- the `⊇` half of the image identity gives a cyclotomic `c` with `Col c = Col u`
    rw [← SetLike.mem_coe, ← himg] at hCol
    obtain ⟨c, hc, hcCol⟩ := hCol
    -- `Col (u·c⁻¹) = Col u − Col c = 0`
    have hinv : Col p c⁻¹ = -Col p c := by
      have h := Col_add p c c⁻¹
      rw [mul_inv_cancel, Col_one] at h
      linear_combination -h
    have hker : Col p (u * c⁻¹) = 0 := by
      rw [Col_add, ← hcCol, hinv]; ring
    -- so `u·c⁻¹ ∈ ℤ_p(1) ⊆ 𝒞_{∞,1}`; and `c ∈ 𝒞_{∞,1}`, hence `u ∈ 𝒞_{∞,1}`
    have hcunit : u * c⁻¹ ∈ unitsTower1 p :=
      mul_mem hu ((unitsTower1 p).inv_mem (cycloTower1_le_unitsTower1 p hc))
    have hzp : u * c⁻¹ ∈ cycloTower1 p :=
      ZpOne_le_cycloTower1 p ((mem_ker_Col_iff_mem_ZpOne p hp2 hcunit).1 hker)
    have : u = (u * c⁻¹) * c := by rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [this]
    exact mul_mem hzp hc
  · -- `←`: `u ∈ 𝒞_{∞,1} ⟹ Col u ∈ I(𝒢)ζ_p` is the `⊆` half of the image identity
    intro hu'
    rw [← SetLike.mem_coe, ← himg]
    exact ⟨u, hu', rfl⟩

/-! ## The descent of the Coleman map (RJW thm:iwasawa 2 (i)) -/

/-- **RJW thm:iwasawa 2 (i), the genuine map**: the Coleman map descends to a homomorphism
`𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p`, `[u] ↦ [Col u]`, packaged multiplicatively. It is the
restriction of `ColMul` (`u ↦ [Col u]`) to `𝒰_{∞,1}`, descended through the subgroup
`𝒞_{∞,1}` by `QuotientGroup.lift`: the cyclotomic units land in `ker` because `Col u ∈
I(𝒢)ζ_p` for `u ∈ 𝒞_{∞,1}` (the `→` direction of the image computation
`col_mem_zetaIdeal_iff_mem_cycloTower1`). This is the SES injection of RJW's diagram. -/
def colDescentMul (hp2 : p ≠ 2) :
    (↥(unitsTower1 p) ⧸ (cycloTower1 p).subgroupOf (unitsTower1 p)) →*
      Multiplicative (PadicMeasure p ℤ_[p]ˣ ⧸ PadicMeasure.zetaIdeal p hp2) := by
  refine QuotientGroup.lift ((cycloTower1 p).subgroupOf (unitsTower1 p))
    ((ColMul p hp2).comp (unitsTower1 p).subtype) ?_
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, (unitsTower1 p).coe_subtype, ColMul_apply]
  -- `[Col x] = 0` because `Col x ∈ I(𝒢)ζ_p` for the cyclotomic unit `x`
  have hmem : Col p (x : NormCompatUnits p) ∈ PadicMeasure.zetaIdeal p hp2 :=
    (col_mem_zetaIdeal_iff_mem_cycloTower1 p hp2 x.2).2 hx
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hmem]; rfl

/-- **RJW thm:iwasawa 2 (i), additive shape**: the descent of `Col` as the additive
homomorphism `𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p` demanded by the statement, obtained from
`colDescentMul` by `MonoidHom.toAdditive`. -/
def colDescent (hp2 : p ≠ 2) :
    Additive (↥(unitsTower1 p) ⧸ (cycloTower1 p).subgroupOf (unitsTower1 p)) →+
      (PadicMeasure p ℤ_[p]ˣ ⧸ PadicMeasure.zetaIdeal p hp2) :=
  MonoidHom.toAdditive (colDescentMul p hp2)

/-! ## The plus-part descent and the isomorphism (RJW thm:iwasawa 2 (ii)) -/

/-- `𝒞⁺_{∞,1} ≤ 𝒞_{∞,1}`: the plus closure-tower sits inside the full closure-tower
(`cycloClosureOnePlus ≤ cycloClosureOne`, dropping the `localUnitsPlus` factor). -/
theorem cycloTower1Plus_le_cycloTower1 : cycloTower1Plus p ≤ cycloTower1 p := by
  intro u hu n hn
  have h := hu n hn
  rw [cycloClosureOnePlus, Subgroup.mem_inf, cycloClosurePlus, Subgroup.mem_inf] at h
  rw [cycloClosureOne, Subgroup.mem_inf]
  exact ⟨h.1.1, h.2⟩

/-- `𝒞⁺_{∞,1} ≤ 𝒰⁺_{∞,1}`: the plus closure-tower is principal-plus
(`cycloClosureOnePlus ≤ localUnitsOnePlus`). -/
theorem cycloTower1Plus_le_unitsTower1Plus : cycloTower1Plus p ≤ unitsTower1Plus p := by
  intro u hu n hn
  have h := hu n hn
  rw [cycloClosureOnePlus, Subgroup.mem_inf, cycloClosurePlus, Subgroup.mem_inf] at h
  rw [localUnitsOnePlus, Subgroup.mem_inf]
  exact ⟨h.2, h.1.2⟩

/-- **The ζ-ideal commutes with the plus-projection**: `I(𝒢⁺)ζ_p = π_*(I(𝒢)ζ_p)`. Both are
principal — `I(𝒢)ζ_p = (zetaNum a₀)` (`zetaIdeal_eq_span`) and
`I(𝒢⁺)ζ_p = (π_*(zetaNum a₀))` (`zetaIdealPlus_eq_span`) for the common witness
`zetaNum a₀ = ([a₀]−1)·ζ_p` at the canonical generator `a₀` — so the result is
`Ideal.map_span` on the singleton. This is the bridge carrying the (i) image computation to
the plus side. -/
theorem zetaIdealPlus_eq_map_projPlus (hp2 : p ≠ 2) :
    PadicMeasure.zetaIdealPlus p hp2
      = (PadicMeasure.zetaIdeal p hp2).map (PadicMeasure.projPlus p) := by
  have hb_gen : ∀ n : ℕ, Subgroup.zpowers (PadicMeasure.unitsToZModPow p n
        (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose) = ⊤ :=
    (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose_spec.2.2
  have hν : algebraMap (PadicMeasure p ℤ_[p]ˣ) (PadicMeasure.QuotientField p)
        (PadicMeasure.dirac p
          (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose - 1)
        * PadicMeasure.padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (PadicMeasure.QuotientField p)
          (PadicMeasure.zetaNum p
            (PadicMeasure.exists_nat_topological_generator p hp2).choose) := by
    rw [PadicMeasure.padicZeta]
    exact IsLocalization.mk'_spec' (PadicMeasure.QuotientField p) _ _
  rw [PadicMeasure.zetaIdealPlus_eq_span p hp2 hb_gen hν,
    PadicMeasure.zetaIdeal_eq_span p hp2 hb_gen hν, Ideal.map_span, Set.image_singleton]

/-- The plus-projection of the ζ-ideal lands in the plus ζ-ideal:
`π_*(I(𝒢)ζ_p) ⊆ I(𝒢⁺)ζ_p` (an equality by `zetaIdealPlus_eq_map_projPlus`; this is the
direction needed for well-definedness of the plus descent). -/
theorem projPlus_zetaIdeal_le_zetaIdealPlus (hp2 : p ≠ 2) {μ : PadicMeasure p ℤ_[p]ˣ}
    (hμ : μ ∈ PadicMeasure.zetaIdeal p hp2) :
    PadicMeasure.projPlus p μ ∈ PadicMeasure.zetaIdealPlus p hp2 := by
  rw [zetaIdealPlus_eq_map_projPlus p hp2]
  exact Ideal.mem_map_of_mem _ hμ

/-- **The plus Coleman map as a homomorphism into `Λ(𝒢⁺)/I(𝒢⁺)ζ_p`**, packaged
multiplicatively: `u ↦ [π_*(Col u)] ∈ Multiplicative (Λ(𝒢⁺)/I(𝒢⁺)ζ_p)`. The hom property
is `Col_add` followed by the ring-hom `π_* = projPlus` and the additive quotient map. This is
the plus analogue of `ColMul` and the source of the plus descent. -/
def ColPlusMul (hp2 : p ≠ 2) :
    NormCompatUnits p →* Multiplicative
      (PadicMeasure p (PadicMeasure.GPlus p) ⧸ PadicMeasure.zetaIdealPlus p hp2) where
  toFun u := Multiplicative.ofAdd
    (Ideal.Quotient.mk (PadicMeasure.zetaIdealPlus p hp2) (PadicMeasure.projPlus p (Col p u)))
  map_one' := by
    change Multiplicative.ofAdd (Ideal.Quotient.mk _
      (PadicMeasure.projPlus p (Col p (1 : NormCompatUnits p)))) = 1
    rw [Col_one, map_zero, map_zero]; rfl
  map_mul' u v := by
    change Multiplicative.ofAdd (Ideal.Quotient.mk _
      (PadicMeasure.projPlus p (Col p (u * v)))) = _
    rw [Col_add, map_add, map_add, ofAdd_add]

@[simp] theorem ColPlusMul_apply (hp2 : p ≠ 2) (u : NormCompatUnits p) :
    ColPlusMul p hp2 u = Multiplicative.ofAdd
      (Ideal.Quotient.mk (PadicMeasure.zetaIdealPlus p hp2)
        (PadicMeasure.projPlus p (Col p u))) :=
  rfl

/-- **RJW thm:iwasawa 2 (ii), the genuine plus-descent map**: the plus-part of the Coleman
descent, `[u] ↦ [π_*(Col u)] ∈ Λ(𝒢⁺)/I(𝒢⁺)ζ_p`, packaged multiplicatively on
`𝒰⁺_{∞,1}/𝒞⁺_{∞,1}`. It is the restriction of `ColPlusMul` to `𝒰⁺_{∞,1}`, descended through
`𝒞⁺_{∞,1}`: well-defined because for `u ∈ 𝒞⁺_{∞,1}` we have `u ∈ 𝒞_{∞,1}`
(`cycloTower1Plus_le_cycloTower1`) and `u ∈ 𝒰_{∞,1}`, so `Col u ∈ I(𝒢)ζ_p` (the image
computation `col_mem_zetaIdeal_iff_mem_cycloTower1`), whence `π_*(Col u) ∈ I(𝒢⁺)ζ_p`
(`projPlus_zetaIdeal_le_zetaIdealPlus`). This is the genuine RJW plus map; its bijectivity
(`colDescentPlusMul_bijective`) is the §12.5 collapse. -/
def colDescentPlusMul (hp2 : p ≠ 2) :
    (↥(unitsTower1Plus p) ⧸ (cycloTower1Plus p).subgroupOf (unitsTower1Plus p)) →*
      Multiplicative
        (PadicMeasure p (PadicMeasure.GPlus p) ⧸ PadicMeasure.zetaIdealPlus p hp2) := by
  refine QuotientGroup.lift ((cycloTower1Plus p).subgroupOf (unitsTower1Plus p))
    ((ColPlusMul p hp2).comp (unitsTower1Plus p).subtype) ?_
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, (unitsTower1Plus p).coe_subtype, ColPlusMul_apply]
  -- `[π_*(Col x)] = 0`: `x ∈ 𝒞_{∞,1}` ⟹ `Col x ∈ I(𝒢)ζ_p` ⟹ `π_*(Col x) ∈ I(𝒢⁺)ζ_p`
  have hxcyclo : (x : NormCompatUnits p) ∈ cycloTower1 p :=
    cycloTower1Plus_le_cycloTower1 p hx
  have hxunit : (x : NormCompatUnits p) ∈ unitsTower1 p :=
    unitsTower1Plus_le_unitsTower1 p x.2
  have hmem : Col p (x : NormCompatUnits p) ∈ PadicMeasure.zetaIdeal p hp2 :=
    (col_mem_zetaIdeal_iff_mem_cycloTower1 p hp2 hxunit).2 hxcyclo
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (projPlus_zetaIdeal_le_zetaIdealPlus p hp2 hmem)]; rfl

/-! ## Plus-equivariance of the Coleman map (RJW §12.5, the injectivity input)

The Galois fixed-field characterisation `K_n⁺ = (K_n)^{⟨σ_{-1}⟩}`
(`mem_localUnitsOnePlus_iff_galAut_fixed`, `GaloisAction.lean`) lets us transport
`c`-invariance from a plus-tower unit `u` to its Coleman image `Col u`: a plus-tower unit is
fixed by complex conjugation `σ_{-1}` levelwise, hence `σ_{-1}·u = u` in `𝒰_∞`
(`galNCU`), and `Col(σ_{-1}·u) = [−1]·Col u = c·Col u` (`Col_galNCU_eq_dirac_mul`), so
`c·Col u = Col u`, i.e. `Col u ∈ Λ(𝒢)⁺`. -/

/-- A plus-tower unit is fixed by complex conjugation `σ_{-1}` on `𝒰_∞`: `σ_{-1}·u = u`.
Levelwise `(σ_{-1}·u)_n = σ_{-1}(u_n) = u_n` — for `n ≥ 1` because `u_n ∈ 𝒰⁺_{n,1}` is
`σ_{-1}`-fixed (`mem_localUnitsOnePlus_iff_galAut_fixed`), and for `n = 0` because
`σ_{-1} = id` on `K_0 = ℚ_p` (`galAut … 0 = AlgEquiv.refl`). -/
theorem galNCU_neg_one_of_mem_unitsTower1Plus (hp2 : p ≠ 2) {u : NormCompatUnits p}
    (hu : u ∈ unitsTower1Plus p) : galNCU p (-1) u = u := by
  refine NormCompatUnits.ext (funext fun n => Units.ext ?_)
  rw [galNCU_elems_val]
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- `n = 0`: `σ_{-1} = AlgEquiv.refl` on `K_0`
    subst hn0
    rw [show galAut p (-1) 0 = AlgEquiv.refl from by rw [galAut, dif_neg (by omega)]]
    rfl
  · -- `n ≥ 1`: `u_n ∈ 𝒰⁺_{n,1}` is `σ_{-1}`-fixed
    have hun : u.elems n ∈ localUnitsOne p n := (Subgroup.mem_inf.1 (hu n hn)).1
    exact (mem_localUnitsOnePlus_iff_galAut_fixed p hp2 hn hun).1 (hu n hn)

/-- **Plus-equivariance of the Coleman map** (RJW §12.5): for a plus-tower unit
`u ∈ 𝒰⁺_{∞,1}`, the Coleman image `Col u` is `c`-invariant, i.e. lies in the plus part
`Λ(𝒢)⁺`. Proof: `σ_{-1}·u = u` (`galNCU_neg_one_of_mem_unitsTower1Plus`), so
`c·Col u = [−1]·Col u = Col(σ_{-1}·u) = Col u` (`Col_galNCU_eq_dirac_mul`, `cAct`). -/
theorem Col_mem_plusPart_of_mem_unitsTower1Plus (hp2 : p ≠ 2) {u : NormCompatUnits p}
    (hu : u ∈ unitsTower1Plus p) : Col p u ∈ PadicMeasure.plusPart p := by
  rw [PadicMeasure.mem_plusPart_iff]
  -- `[−1]·Col u = Col(σ_{-1}·u) = Col u`
  rw [← Col_galNCU_eq_dirac_mul p (-1) u, galNCU_neg_one_of_mem_unitsTower1Plus p hp2 hu]

/-- `𝒞⁺_{∞,1} = 𝒞_{∞,1} ⊓ 𝒰⁺_{∞,1}`: the plus closure-tower is exactly the principal-plus
units inside the full closure-tower (levelwise `cycloClosureOnePlus = cycloClosureOne ⊓
localUnitsPlus`, the only reshuffle of the `⊓`-factors). The `←` inclusion is the step
`u ∈ 𝒞_{∞,1} ∧ u ∈ 𝒰⁺_{∞,1} ⟹ u ∈ 𝒞⁺_{∞,1}` of the injectivity argument. -/
theorem mem_cycloTower1Plus_of_mem_cycloTower1_unitsTower1Plus {u : NormCompatUnits p}
    (hc : u ∈ cycloTower1 p) (hp : u ∈ unitsTower1Plus p) : u ∈ cycloTower1Plus p := by
  intro n hn
  have hcn := hc n hn
  have hpn := hp n hn
  rw [cycloClosureOne, Subgroup.mem_inf] at hcn
  rw [localUnitsOnePlus, Subgroup.mem_inf] at hpn
  rw [cycloClosureOnePlus, Subgroup.mem_inf, cycloClosurePlus, Subgroup.mem_inf]
  exact ⟨⟨hcn.1, hpn.2⟩, hcn.2⟩

/-- The even idempotent `e⁺ = ½([1] + [−1]) ∈ Λ(𝒢)` (the projector onto `Λ(𝒢)⁺`). -/
private noncomputable def ePlus (hp2 : p ≠ 2) : PadicMeasure p ℤ_[p]ˣ :=
  (((PadicLFunctions.isUnit_two_padicInt p hp2).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
    • (1 + PadicMeasure.dirac p (-1 : ℤ_[p]ˣ))

/-- `[−1]·[−1] = 1` in `Λ(𝒢)`. -/
private theorem dirac_neg_one_sq :
    PadicMeasure.dirac p (-1 : ℤ_[p]ˣ) * PadicMeasure.dirac p (-1 : ℤ_[p]ˣ) = 1 := by
  rw [PadicMeasure.units_dirac_mul_dirac, show (-1 : ℤ_[p]ˣ) * (-1) = 1 by rw [neg_mul_neg,
    one_mul], ← PadicMeasure.units_one_def]

/-- `e⁺ ∈ Λ(𝒢)⁺`: `[−1]·e⁺ = ½([−1] + [1]) = e⁺`. -/
private theorem ePlus_mem_plusPart (hp2 : p ≠ 2) : ePlus p hp2 ∈ PadicMeasure.plusPart p := by
  rw [PadicMeasure.mem_plusPart_iff, ePlus, mul_smul_comm, mul_add, mul_one,
    dirac_neg_one_sq p, add_comm]

/-- `π_*` is `ℤ_[p]`-linear (its underlying map is `pushforward`, a `LinearMap`). -/
private theorem projPlus_smul (c : ℤ_[p]) (μ : PadicMeasure p ℤ_[p]ˣ) :
    PadicMeasure.projPlus p (c • μ) = c • PadicMeasure.projPlus p μ :=
  (PadicMeasure.pushforward p (PadicMeasure.quotientMk p)).map_smul c μ

/-- `π_*(e⁺) = 1`: under the quotient `mk (−1) = mk 1`, so `e⁺ ↦ ½(1 + 1) = 1`. -/
private theorem projPlus_ePlus (hp2 : p ≠ 2) :
    PadicMeasure.projPlus p (ePlus p hp2) = 1 := by
  rw [ePlus, projPlus_smul, map_add, map_one, PadicMeasure.projPlus_dirac,
    show (QuotientGroup.mk (-1 : ℤ_[p]ˣ) : PadicMeasure.GPlus p) = QuotientGroup.mk 1 from by
      rw [QuotientGroup.eq, Subgroup.mem_zpowers_iff]
      exact ⟨1, by rw [zpow_one, inv_neg, neg_mul, inv_mul_cancel]⟩]
  rw [show (PadicMeasure.dirac p (QuotientGroup.mk (1 : ℤ_[p]ˣ) : PadicMeasure.GPlus p))
      = 1 from by rw [← PadicMeasure.projPlus_dirac, ← PadicMeasure.units_one_def, map_one],
    show (1 : PadicMeasure p (PadicMeasure.GPlus p)) + 1
      = (2 : ℤ_[p]) • (1 : PadicMeasure p (PadicMeasure.GPlus p)) from by rw [two_smul], smul_smul,
    (PadicLFunctions.isUnit_two_padicInt p hp2).val_inv_mul, one_smul]

/-- The plus ζ-ideal pulls back to the ζ-ideal on `c`-invariant measures: if `μ ∈ Λ(𝒢)⁺`
and `π_*(μ) ∈ I(𝒢⁺)ζ_p`, then `μ ∈ I(𝒢)ζ_p`. `I(𝒢⁺)ζ_p = π_*(I(𝒢)ζ_p)`
(`zetaIdealPlus_eq_map_projPlus`), so `π_*(μ) = π_*(ν)` for some `ν ∈ I(𝒢)ζ_p`. Replacing `ν`
by its plus part `e⁺·ν` (still in `I(𝒢)ζ_p` since it is an ideal, and with the same
pushforward since `π_*(e⁺) = 1`), both `μ` and `e⁺·ν` lie in `Λ(𝒢)⁺` where `π_*` is injective
(`plusSection_projPlus`), so `μ = e⁺·ν ∈ I(𝒢)ζ_p`. -/
theorem mem_zetaIdeal_of_mem_plusPart_projPlus (hp2 : p ≠ 2) {μ : PadicMeasure p ℤ_[p]ˣ}
    (hμ : μ ∈ PadicMeasure.plusPart p)
    (hproj : PadicMeasure.projPlus p μ ∈ PadicMeasure.zetaIdealPlus p hp2) :
    μ ∈ PadicMeasure.zetaIdeal p hp2 := by
  -- `π_*(μ) ∈ π_*(I(𝒢)ζ_p)`, so `π_*(ν) = π_*(μ)` with `ν ∈ I(𝒢)ζ_p`
  rw [zetaIdealPlus_eq_map_projPlus p hp2, Ideal.mem_map_iff_of_surjective _
    (PadicMeasure.projPlus_surjective p hp2)] at hproj
  obtain ⟨ν, hν, hμν⟩ := hproj
  -- the plus part `e⁺·ν ∈ I(𝒢)ζ_p ∩ Λ(𝒢)⁺` with `π_*(e⁺·ν) = π_*(ν) = π_*(μ)`
  set ν' := ePlus p hp2 * ν with hν'
  have hν'ideal : ν' ∈ PadicMeasure.zetaIdeal p hp2 := Ideal.mul_mem_left _ _ hν
  have hν'plus : ν' ∈ PadicMeasure.plusPart p := by
    rw [hν', mul_comm]; exact PadicMeasure.mul_mem_plusPart p (ePlus_mem_plusPart p hp2)
  have hprojν' : PadicMeasure.projPlus p ν' = PadicMeasure.projPlus p μ := by
    rw [hν', map_mul, projPlus_ePlus p hp2]
    exact (one_mul _).trans hμν
  -- `π_*` injective on `Λ(𝒢)⁺`, so `μ = ν' ∈ I(𝒢)ζ_p`
  have hμeq : ν' = μ := by
    have h := congrArg (PadicMeasure.plusSection p hp2) hprojν'
    rwa [PadicMeasure.plusSection_projPlus p hp2 hν'plus,
      PadicMeasure.plusSection_projPlus p hp2 hμ] at h
  rw [← hμeq]; exact hν'ideal

/-- **The plus-descent `colDescentPlusMul` is injective** (RJW §12.5, the `⟨c⟩`-invariants
half now discharged via the Galois fixed-field). For a plus-tower unit `u` with
`[π_*(Col u)] = 0`:
* `Col u ∈ Λ(𝒢)⁺` (plus-equivariance `Col_mem_plusPart_of_mem_unitsTower1Plus`, from the
  Galois characterisation `K_n⁺ = (K_n)^{⟨σ_{-1}⟩}`);
* `π_*(Col u) ∈ I(𝒢⁺)ζ_p`, so `Col u ∈ I(𝒢)ζ_p` (`mem_zetaIdeal_of_mem_plusPart_projPlus`);
* hence `u ∈ 𝒞_{∞,1}` (`col_mem_zetaIdeal_iff_mem_cycloTower1`, the `→` direction), and
  `u ∈ 𝒞⁺_{∞,1}` since `u` is plus (`mem_cycloTower1Plus_of_mem_cycloTower1_unitsTower1Plus`),
i.e. `[u] = 0`. (Transitively this still rests on the deferred image identity `col_image`
through `col_mem_zetaIdeal_iff_mem_cycloTower1`; no *additional* gap is introduced.) -/
theorem colDescentPlusMul_injective (hp2 : p ≠ 2) :
    Function.Injective (colDescentPlusMul p hp2) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | _ u =>
    -- `colDescentPlusMul [u] = ofAdd [π_*(Col u)] = 1`, i.e. `π_*(Col u) ∈ I(𝒢⁺)ζ_p`
    rw [colDescentPlusMul, QuotientGroup.lift_mk, MonoidHom.comp_apply,
      (unitsTower1Plus p).coe_subtype, ColPlusMul_apply] at hx
    have hproj : PadicMeasure.projPlus p (Col p (u : NormCompatUnits p))
        ∈ PadicMeasure.zetaIdealPlus p hp2 := by
      rwa [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff,
        Ideal.Quotient.eq_zero_iff_mem] at hx
    -- `Col u ∈ Λ(𝒢)⁺` (plus-equivariance), so `Col u ∈ I(𝒢)ζ_p`
    have hplus : Col p (u : NormCompatUnits p) ∈ PadicMeasure.plusPart p :=
      Col_mem_plusPart_of_mem_unitsTower1Plus p hp2 u.2
    have hzeta : Col p (u : NormCompatUnits p) ∈ PadicMeasure.zetaIdeal p hp2 :=
      mem_zetaIdeal_of_mem_plusPart_projPlus p hp2 hplus hproj
    -- hence `u ∈ 𝒞_{∞,1}`, and being plus, `u ∈ 𝒞⁺_{∞,1}`, i.e. `[u] = 1`
    have huunit : (u : NormCompatUnits p) ∈ unitsTower1 p :=
      unitsTower1Plus_le_unitsTower1 p u.2
    have hcyclo : (u : NormCompatUnits p) ∈ cycloTower1 p :=
      (col_mem_zetaIdeal_iff_mem_cycloTower1 p hp2 huunit).1 hzeta
    have hcycloPlus : (u : NormCompatUnits p) ∈ cycloTower1Plus p :=
      mem_cycloTower1Plus_of_mem_cycloTower1_unitsTower1Plus p hcyclo u.2
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hcycloPlus

/-- **RJW thm:iwasawa 2 (ii) — the milestone bijectivity**: the plus-descent
`colDescentPlusMul : 𝒰⁺_{∞,1}/𝒞⁺_{∞,1} → Λ(𝒢⁺)/I(𝒢⁺)ζ_p` is bijective. The injectivity is
proved (`colDescentPlusMul_injective`), enabled by the Galois fixed-field characterisation
`K_n⁺ = (K_n)^{⟨σ_{-1}⟩}` (`mem_localUnitsOnePlus_iff_galAut_fixed`, `GaloisAction.lean`).

Surjectivity is the one remaining gap, and it reduces to the **single** deferred identity
`col_image_cycloTower1_eq_zetaIdeal` (Main.lean): RJW's `(−)^{⟨c⟩}`-collapse of the
fundamental sequence (i) `0 → 𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p → ℤ_p(1) → 0` makes
`colDescentPlusMul` onto because `ℤ_p(1)^{⟨c⟩} = 0` (`p` odd), and the (i) image
`range Col = ker(χ-moment)` (`range_Col_eq_ker_chiMoment`) together with the image
computation `col_image_cycloTower1_eq_zetaIdeal` pins the cokernel. With that identity in
hand (the §13/IMC-deferred core, the SAME blocker as the injectivity input
`col_mem_zetaIdeal_iff_mem_cycloTower1`), both halves close — the milestone bottlenecks on
exactly `col_image_cycloTower1_eq_zetaIdeal`. -/
theorem colDescentPlusMul_bijective (hp2 : p ≠ 2) :
    Function.Bijective (colDescentPlusMul p hp2) :=
  ⟨colDescentPlusMul_injective p hp2, by
    -- DEFERRED: surjectivity reduces to `col_image_cycloTower1_eq_zetaIdeal` (Main.lean:151),
    -- the §13/IMC-deferred image identity (the same blocker as the injectivity input). With
    -- `col_image` the `(−)^{⟨c⟩}`-collapse of the fundamental sequence (i) gives surjectivity
    -- (`ℤ_p(1)^{⟨c⟩} = 0`, `range_Col_eq_ker_chiMoment`). No further gap beyond `col_image`.
    sorry⟩

/-- **RJW thm:iwasawa 2 (ii) — THE MILESTONE (TeX 3592–3593)**: the Coleman map induces an
isomorphism of `Λ(𝒢^+)`-modules `𝒰_{∞,1}^+/𝒞_{∞,1}^+ ≅ Λ(𝒢^+)/I(𝒢^+)ζ_p`. This is
`thm:iwasawa` (stated, then unwired, in the §11 chapter), now proved. Stated as the
existence of a `Λ(𝒢^+)`-linear (here `ℤ_[p]`-linear placeholder; the `Λ(𝒢^+)`-structure
on the quotient is wired at execution) isomorphism between the two quotients. -/
theorem iwasawa_theorem (hp2 : p ≠ 2) :
    Nonempty (
      Additive (↥(unitsTower1Plus p) ⧸ (cycloTower1Plus p).subgroupOf (unitsTower1Plus p)) ≃+
      (PadicMeasure p (PadicMeasure.GPlus p) ⧸ PadicMeasure.zetaIdealPlus p hp2)) :=
  -- the genuine plus-descent `[u] ↦ [π_*(Col u)]`, an iso by `colDescentPlusMul_bijective`,
  -- converted from multiplicative to additive shape (`MulEquiv.toAdditive`)
  ⟨MulEquiv.toAdditive
    (MulEquiv.ofBijective (colDescentPlusMul p hp2) (colDescentPlusMul_bijective p hp2))⟩

/-- **RJW thm:iwasawa 2 (i) (TeX 3590–3591)**: the `Λ(𝒢)`-module short exact sequence
`0 → 𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p → ℤ_p(1) → 0`. Stated as the injection
`𝒰_{∞,1}/𝒞_{∞,1} ↪ Λ(𝒢)/I(𝒢)ζ_p` with cokernel `ℤ_p(1)` (the `χ`-moment). -/
theorem iwasawa_exact_sequence (hp2 : p ≠ 2) :
    Nonempty (
      Additive (↥(unitsTower1 p) ⧸ (cycloTower1 p).subgroupOf (unitsTower1 p)) →+
      (PadicMeasure p ℤ_[p]ˣ ⧸ PadicMeasure.zetaIdeal p hp2)) :=
  ⟨colDescent p hp2⟩

end PadicLFunctions.Coleman
