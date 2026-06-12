import PadicLFunctions.Iwasawa.PlusPart
import PadicLFunctions.KubotaLeopoldt.ZetaP

/-!
# ζ_p as a pseudo-measure on 𝒢⁺ and the ideal I(𝒢)ζ_p

RJW (arXiv:2309.15692) §11.1 corollary + §11.2 (TeX 2992, 3033–3059), on the
identified Galois side (replan R11.1; `𝒢⁺ = GPlus p`).

## Main declarations

* `PadicMeasure.odd_moment_factor_eq_zero` + `padicZeta_odd_moment_eq_zero`: the
  interpolated odd moments of ζ_p vanish — at `k = 1` via the Euler factor `1 − p⁰ = 0`,
  at odd `k ≥ 3` via `B_k = 0` (TeX 2992; **erratum #13**: the source's proof line
  "ζ(1−k) = 0 for odd k ≥ 1" fails at `k = 1`).
* `PadicMeasure.dirac_neg_one_sub_one_mul_padicZeta`: c-invariance
  `([−1]−[1])·ζ_p = 0` — the descent input.
* `PadicMeasure.padicZetaPlus` + `isPlusPseudoMeasure_padicZetaPlus`: **the corollary
  of RJW TeX 3033** — ζ_p descends to a pseudo-measure on 𝒢⁺.
* `PadicMeasure.zetaIdeal`/`zetaIdealPlus`: the ideals `I(𝒢)ζ_p` and `I(𝒢⁺)ζ_p`
  (**RJW Proposition, TeX 3052–3057**), with their `Ideal.span` descriptions via the
  principality of the augmentation ideals.
-/

noncomputable section

namespace PadicMeasure

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## Odd moments of ζ_p vanish (TeX 2992 + the corrected TeX 3038 argument) -/

/-- The interpolation factor `(1 − p^{k−1})·ζ(1−k)` vanishes for every odd `k ≥ 1`:
at `k = 1` the Euler factor is `1 − p⁰ = 0` (ζ(0) = −1/2 itself does NOT vanish —
erratum #13); at odd `k ≥ 3`, `ζ(1−k) = −B_k/k = 0` (`bernoulli_eq_zero_of_odd`). -/
theorem odd_moment_factor_eq_zero {k : ℕ} (hk : Odd k) :
    (1 - (p : ℚ_[p]) ^ (k - 1)) * ((zetaNeg (k - 1) : ℚ) : ℚ_[p]) = 0 := by
  sorry

/-- The odd moments of every witness `([b]−[1])·ζ_p` vanish: this is the precise
content of TeX 2992 "ζ_p vanishes at the characters χ^k for odd k" — including
`k = 1`, which the membership criterion requires. -/
theorem padicZeta_odd_moment_eq_zero (hp2 : p ≠ 2) (b : ℤ_[p]ˣ) {k : ℕ} (hk : Odd k)
    (ν : PadicMeasure p ℤ_[p]ˣ)
    (hν : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p b - 1) * padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν) :
    ν (unitsPowCM p k) = 0 := by
  sorry

/-! ## c-invariance of ζ_p -/

/-- **The descent input**: `([−1]−[1])·ζ_p = 0` in `Q(𝒢)`, i.e. ζ_p is invariant
under complex conjugation. (The `b = −1` witness has *all* moments zero: even ones by
`(−1)^k − 1 = 0`, odd ones by `padicZeta_odd_moment_eq_zero`.) -/
theorem dirac_neg_one_sub_one_mul_padicZeta (hp2 : p ≠ 2) :
    algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p (-1 : ℤ_[p]ˣ) - 1)
        * padicZeta p hp2
      = 0 := by
  sorry

/-- Witness symmetry: the witnesses of `([g]−[1])·ζ_p` and `([−g]−[1])·ζ_p`
coincide — the well-definedness of pushing witnesses to `𝒢⁺`. -/
theorem padicZeta_witness_neg (hp2 : p ≠ 2) (g : ℤ_[p]ˣ)
    {ν ν' : PadicMeasure p ℤ_[p]ˣ}
    (hν : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p g - 1) * padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν)
    (hν' : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p (-g) - 1)
        * padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν') :
    ν = ν' := by
  sorry

/-! ## ζ_p as a pseudo-measure on 𝒢⁺ (RJW corollary, TeX 3033–3039) -/

/-- The total fraction ring `Q(𝒢⁺)` of the Iwasawa algebra `Λ(𝒢⁺)`. -/
abbrev QuotientFieldPlus := FractionRing (PadicMeasure p (GPlus p))

/-- The structure map `Λ(𝒢⁺) → Q(𝒢⁺)`, named once (the raw `algebraMap` keeps an
unresolved instance metavariable inside `def`-bodies over the quotient group — a
known elaboration-order trap; naming it sidesteps the postponement). -/
def toQPlus : PadicMeasure p (GPlus p) →+* QuotientFieldPlus p :=
  algebraMap _ _

/-- A *pseudo-measure on `𝒢⁺`* (RJW Def. 3.34 applied to `G = 𝒢⁺`). -/
def IsPlusPseudoMeasure (q : QuotientFieldPlus p) : Prop :=
  ∀ g : GPlus p, ∃ ν : PadicMeasure p (GPlus p),
    toQPlus p (dirac p g - 1) * q = toQPlus p ν

/-- Regularity transports along the projection: if `[a]−[1]` is a non-zero-divisor in
`Λ(𝒢)`, then `[ā]−[1]` is one in `Λ(𝒢⁺)` (lift along the even-part section, land in
`Λ⁺ ⊓ ker π_* = 0`, conclude on the 𝒢-side). No 𝒢⁺-moment theory needed. -/
theorem dirac_mk_sub_one_mem_nonZeroDivisors (hp2 : p ≠ 2) {a : ℤ_[p]ˣ}
    (ha : (dirac p a - 1 : PadicMeasure p ℤ_[p]ˣ)
      ∈ nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ)) :
    (dirac p (QuotientGroup.mk a : GPlus p) - 1 : PadicMeasure p (GPlus p))
      ∈ nonZeroDivisors (PadicMeasure p (GPlus p)) := by
  sorry

/-- **ζ_p as a pseudo-measure on 𝒢⁺** (the object of RJW's corollary, TeX 3033):
`ζ_p⁺ := π_*(x⁻¹ Res μ_a) / ([ā]−[1])`, for the same packed integer topological
generator `a` as `padicZeta`. -/
def padicZetaPlus (hp2 : p ≠ 2) : QuotientFieldPlus p :=
  IsLocalization.mk' (QuotientFieldPlus p)
    (projPlus p (zetaNum p (exists_nat_topological_generator p hp2).choose))
    (⟨dirac p (QuotientGroup.mk
        ((exists_nat_topological_generator p hp2).choose_spec.choose) : GPlus p) - 1,
      by sorry⟩ : nonZeroDivisors (PadicMeasure p (GPlus p)))

/-- Compatibility of the descents: pushing a 𝒢-side witness forward gives the
𝒢⁺-side witness at the image group element — "ζ_p descends". -/
theorem projPlus_padicZeta_witness (hp2 : p ≠ 2) (g : ℤ_[p]ˣ)
    {ν : PadicMeasure p ℤ_[p]ˣ}
    (hν : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p g - 1) * padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν) :
    toQPlus p (dirac p (QuotientGroup.mk g : GPlus p) - 1) * padicZetaPlus p hp2
      = toQPlus p (projPlus p ν) := by
  sorry

/-- **RJW §11.1, Corollary (TeX 3033–3039)**: the p-adic zeta function is a
pseudo-measure on `𝒢⁺`. -/
theorem isPlusPseudoMeasure_padicZetaPlus (hp2 : p ≠ 2) :
    IsPlusPseudoMeasure p (padicZetaPlus p hp2) := by
  sorry

/-! ## The ideal generated by ζ_p (RJW §11.2, TeX 3043–3059) -/

/-- **`I(𝒢)ζ_p`** (RJW Proposition, TeX 3052): the set of measures of the form
`λ·ζ_p` with `λ` in the augmentation ideal — an ideal of `Λ(𝒢)` by the
pseudo-measure property (the ideal axioms hold directly; the `Ideal.span`
description below is the computational form). -/
def zetaIdeal (hp2 : p ≠ 2) : Ideal (PadicMeasure p ℤ_[p]ˣ) where
  carrier := {x | ∃ l ∈ augmentationIdeal p (G := ℤ_[p]ˣ),
    algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) x
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) l * padicZeta p hp2}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

lemma mem_zetaIdeal_iff (hp2 : p ≠ 2) {x : PadicMeasure p ℤ_[p]ˣ} :
    x ∈ zetaIdeal p hp2 ↔ ∃ l ∈ augmentationIdeal p (G := ℤ_[p]ˣ),
      algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) x
        = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) l * padicZeta p hp2 := by
  sorry

/-- The computational description: `I(𝒢)ζ_p` is the principal ideal generated by any
witness of `([b]−[1])·ζ_p` at a topological generator `b` (via the principality
`augmentationIdeal_eq_span`). -/
theorem zetaIdeal_eq_span (hp2 : p ≠ 2) {b : ℤ_[p]ˣ}
    (hb : ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n b) = ⊤)
    {ν : PadicMeasure p ℤ_[p]ˣ}
    (hν : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p b - 1) * padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν) :
    zetaIdeal p hp2 = Ideal.span {ν} := by
  sorry

/-- The image `ā` of a topological generator generates the augmentation ideal of
`Λ(𝒢⁺)`: `I(𝒢⁺) = ([ā]−[1])·Λ(𝒢⁺)` (transport of `augmentationIdeal_eq_span`
along the surjection `π_*`, using `deg⁺ ∘ π_* = deg`). -/
theorem augmentationIdealPlus_eq_span (hp2 : p ≠ 2) {a : ℤ_[p]ˣ}
    (ha : ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n a) = ⊤) :
    augmentationIdeal p (G := GPlus p)
      = Ideal.span {(dirac p (QuotientGroup.mk a : GPlus p) - 1 :
          PadicMeasure p (GPlus p))} := by
  sorry

/-- **`I(𝒢⁺)ζ_p`** (RJW Proposition, TeX 3052, plus half): the corresponding ideal
of `Λ(𝒢⁺)` — the right-hand side of Iwasawa's theorem (`thm:iwasawa`, stated on the
§12 board). -/
def zetaIdealPlus (hp2 : p ≠ 2) : Ideal (PadicMeasure p (GPlus p)) where
  carrier := {x | ∃ l ∈ augmentationIdeal p (G := GPlus p),
    toQPlus p x = toQPlus p l * padicZetaPlus p hp2}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

lemma mem_zetaIdealPlus_iff (hp2 : p ≠ 2) {x : PadicMeasure p (GPlus p)} :
    x ∈ zetaIdealPlus p hp2 ↔ ∃ l ∈ augmentationIdeal p (G := GPlus p),
      toQPlus p x = toQPlus p l * padicZetaPlus p hp2 := by
  sorry

theorem zetaIdealPlus_eq_span (hp2 : p ≠ 2) {a : ℤ_[p]ˣ}
    (ha : ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n a) = ⊤)
    {ν : PadicMeasure p ℤ_[p]ˣ}
    (hν : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p a - 1) * padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν) :
    zetaIdealPlus p hp2 = Ideal.span {projPlus p ν} := by
  sorry

end PadicMeasure
