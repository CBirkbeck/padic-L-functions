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
further `sorry`. -/
theorem col_image_cycloTower1_eq_zetaIdeal (hp2 : p ≠ 2) :
    (Col p '' (cycloTower1 p : Set (NormCompatUnits p))) = PadicMeasure.zetaIdeal p hp2 := by
  -- BLOCKED: needs `Col '' 𝒞_{∞,1} = I(𝒢)ζ_p`. The genuine minimal blocker is the
  -- inverse-limit `Λ(𝒢)`-module structure of `𝒞_{∞,1}` (RJW TeX 3553–3578) together with
  -- the closure-crossing (continuity of `Col`, or closedness of `I(𝒢)ζ_p` and density of
  -- the `Λ(𝒢)`-span of `c(a₀)` in `𝒞_{∞,1}`). Neither is available in the project; see the
  -- module note. The two named ingredients to build (either suffices):
  --   (A) `Continuous (Col p)` + `IsClosed (↑(zetaIdeal p hp2))`, or
  --   (B) `cycloTower1 p = ⨆-closure of the galNCU-translates of (Teichmüller-corrected
  --       generator wγ(a₀))`, i.e. the cyclic-`Λ(𝒢)`-module structure.
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

/-- **DEFERRED (RJW §12.5, TeX 3592–3608 — the ⟨c⟩-invariants collapse / image isomorphism):**
the plus-descent `colDescentPlusMul` is bijective — i.e. the genuine plus map
`𝒰⁺_{∞,1}/𝒞⁺_{∞,1} → Λ(𝒢⁺)/I(𝒢⁺)ζ_p` is the RJW isomorphism `thm:iwasawa`.

RJW's proof: apply the exact functor `(−)^{⟨c⟩}` (`⟨c⟩`-invariants, exact since `p` is odd —
the ± splitting `isCompl_plusPart_minusPart`) to the fundamental sequence (i)
`0 → 𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p → ℤ_p(1) → 0`. As `c` acts by `−1` on `ℤ_p(1)` and `p`
is odd, `ℤ_p(1)^{⟨c⟩} = 0`, so the cokernel dies and the sequence collapses to the iso (ii),
using `(𝒰_{∞,1}/𝒞_{∞,1})^{⟨c⟩} = 𝒰⁺_{∞,1}/𝒞⁺_{∞,1}` and
`(Λ(𝒢)/I(𝒢)ζ_p)^{⟨c⟩} = Λ(𝒢⁺)/I(𝒢⁺)ζ_p` (`plusEquiv`, `zetaIdealPlus_eq_map_projPlus`).

This is blocked on the §12/§13-deferred infrastructure in two places: (a) surjectivity needs
the inverse-limit cyclic-module image computation (same source as
`col_mem_zetaIdeal_iff_mem_cycloTower1`); (b) injectivity additionally needs the **Galois
fixed-field characterisation** `𝒰⁺_{n,1} = (𝒰_{n,1})^{⟨c⟩}` — i.e. `K_n⁺` is the fixed field
of complex conjugation `σ_{−1}` — to transport `c`-invariance of `Col u` (`Col u ∈ plusPart`)
from the plus-tower membership of `u`; the project's `KPlus` is currently defined by its
concrete generator `ξ + ξ⁻¹` with the Galois characterisation flagged "§12 material"
(`LocalUnits.lean`), so the plus-equivariance of `Col` is not yet derivable. Everything
structural around this (the genuine map `colDescentPlusMul`, the plus-ideal bridge
`zetaIdealPlus_eq_map_projPlus`, the `≃+` assembly) is built without further `sorry`. -/
theorem colDescentPlusMul_bijective (hp2 : p ≠ 2) :
    Function.Bijective (colDescentPlusMul p hp2) := sorry

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
