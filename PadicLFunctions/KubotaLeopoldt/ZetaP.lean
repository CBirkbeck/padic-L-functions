import PadicLFunctions.KubotaLeopoldt.MuA

/-!
# The Kubota–Leopoldt p-adic L-function (RJW §4.3 and Thm. 4.1)

The restriction of `μ_a` to `ℤ_p^×` (as a measure on `ℤ_p^×`, via precomposition with
`extendByZero`), the multiplication-by-`x⁻¹` rescaling (RJW eq. 4.11,
`eq:mult by xinverse`), and the p-adic zeta function

`ζ_p = (x⁻¹ Res_{ℤ_p^×} μ_a) / ([a] − [1]) ∈ Q(ℤ_p^×)`  (RJW Def. 4.10, `DefZetap`)

for `a` an *integer* topological generator of `ℤ_p^×` (the source takes its `a`
simultaneously integral — §4.1 — and a topological generator — Def. 4.10; an integer
primitive root mod `p²` generates `(ℤ/p^n)^×` for every `n`, which is
`exists_nat_topological_generator`).

Main result (RJW Thm. 4.1, `thm:kubota leopoldt theorem`): `ζ_p` is the unique
pseudo-measure on `ℤ_p^×` with `∫_{ℤ_p^×} x^k ζ_p = (1−p^{k−1}) ζ(1−k)` for all
`k > 0` — stated via the witnessing measures of `([b]−[1])·ζ_p`, the same moment
encoding as `pseudoMeasure_eq_zero_of_moments`.
-/

noncomputable section

open PowerSeries

namespace PadicMeasure

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## `μ_a` as a measure on `ℤ_p^×` -/

/-- The restriction of `μ_a` to `ℤ_p^×`, as a measure on `ℤ_p^×`: precomposition
with extension-by-zero. Satisfies `ι (muAUnits a) = Res_{ℤ_p^×}(μ_a)`
(`iota_muAUnits`). Source: RJW §4.2/§4.3 transition. -/
def muAUnits (a : ℕ) : PadicMeasure p ℤ_[p]ˣ :=
  (muA p a).comp (extendByZero p)

lemma iota_muAUnits (a : ℕ) :
    iota p (muAUnits p a) = res p (isClopen_units p) (muA p a) := by
  sorry

lemma muAUnits_apply_unitsPowCM (a k : ℕ) :
    muAUnits p a (unitsPowCM p k)
      = res p (isClopen_units p) (muA p a) (powCM p k) := by
  sorry

/-! ## Multiplication by `x⁻¹` (RJW eq. 4.11) -/

lemma continuous_units_inv_val :
    Continuous fun u : ℤ_[p]ˣ => ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
  sorry

/-- The continuous function `x ↦ x⁻¹` on `ℤ_p^×` (valued in `ℤ_p`). -/
def invCM : C(ℤ_[p]ˣ, ℤ_[p]) :=
  ⟨_, continuous_units_inv_val p⟩

/-- Multiplication of a measure on `ℤ_p^×` by a continuous function (the analogue of
`cmul` on `ℤ_p`). RJW eq. 4.11: `∫ f · (g·μ) := ∫ g·f · μ`. -/
def unitsCmul (g : C(ℤ_[p]ˣ, ℤ_[p])) (μ : PadicMeasure p ℤ_[p]ˣ) :
    PadicMeasure p ℤ_[p]ˣ :=
  μ.comp (LinearMap.mulLeft ℤ_[p] g)

@[simp]
lemma unitsCmul_apply (g f : C(ℤ_[p]ˣ, ℤ_[p])) (μ : PadicMeasure p ℤ_[p]ˣ) :
    unitsCmul p g μ f = μ (g * f) := by
  sorry

/-- The numerator `x⁻¹ · Res_{ℤ_p^×}(μ_a)` of the p-adic zeta function
(RJW Def. 4.10). -/
def zetaNum (a : ℕ) : PadicMeasure p ℤ_[p]ˣ :=
  unitsCmul p (invCM p) (muAUnits p a)

lemma zetaNum_apply_unitsPowCM (a : ℕ) {k : ℕ} (hk : 0 < k) :
    zetaNum p a (unitsPowCM p k) = muAUnits p a (unitsPowCM p (k - 1)) := by
  sorry

/-- RJW TeX line 1561: `∫_{ℤ_p^×} x^k · x⁻¹μ_a = (−1)^k (a^k−1)(1−p^{k−1}) ζ(1−k)`. -/
theorem zetaNum_moments {a : ℕ} (hpa : ¬ p ∣ a) {k : ℕ} (hk : 0 < k) :
    ((zetaNum p a (unitsPowCM p k) : ℤ_[p]) : ℚ_[p])
      = (-1) ^ k * ((a : ℚ_[p]) ^ k - 1) * (1 - (p : ℚ_[p]) ^ (k - 1))
          * ((zetaNeg (k - 1) : ℚ) : ℚ_[p]) := by
  sorry

/-! ## Integer topological generators -/

/-- A topological generator of `ℤ_p^×` is torsion-free: `a^k ≠ 1` for `k > 0`
(the order of its image in `(ℤ/p^n)^×` grows without bound). -/
theorem topGen_pow_ne_one {a : ℤ_[p]ˣ}
    (ha : ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n a) = ⊤) :
    ∀ k, 0 < k → (a : ℤ_[p]) ^ k ≠ 1 := by
  sorry

/-- For odd `p` there is an *integer* topological generator of `ℤ_p^×`: an integer
that is a primitive root mod `p²` generates `(ℤ/p^n)^×` for every `n`. RJW takes
such an `a` implicitly (its `a` is an integer in §4.1 and a topological generator in
Def. 4.10). -/
theorem exists_nat_topological_generator (hp2 : p ≠ 2) :
    ∃ (m : ℕ) (u : ℤ_[p]ˣ), ¬ p ∣ m ∧ (u : ℤ_[p]) = (m : ℤ_[p]) ∧
      ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n u) = ⊤ := by
  sorry

/-! ## The p-adic zeta function (RJW Def. 4.10, Prop. 4.11, Thm. 4.1) -/

/-- **RJW Def. 4.10 (`DefZetap`)**: the p-adic zeta function
`ζ_p = (x⁻¹ Res_{ℤ_p^×} μ_a) / ([a] − [1]) ∈ Q(ℤ_p^×)`, for (a choice of) an integer
topological generator `a` of `ℤ_p^×`. -/
def padicZeta (hp2 : p ≠ 2) : QuotientField p :=
  IsLocalization.mk' (QuotientField p)
    (zetaNum p (exists_nat_topological_generator p hp2).choose)
    ⟨dirac p (exists_nat_topological_generator p hp2).choose_spec.choose - 1,
      dirac_sub_one_mem_nonZeroDivisors p
        (topGen_pow_ne_one p
          (exists_nat_topological_generator p hp2).choose_spec.choose_spec.2.2)⟩

lemma IsPseudoMeasure.sub {q₁ q₂ : QuotientField p}
    (h₁ : IsPseudoMeasure p q₁) (h₂ : IsPseudoMeasure p q₂) :
    IsPseudoMeasure p (q₁ - q₂) := by
  sorry

/-- **RJW Prop. 4.11 (`PropInterpolation2`), first half**: `ζ_p` is a pseudo-measure. -/
theorem padicZeta_isPseudoMeasure (hp2 : p ≠ 2) :
    IsPseudoMeasure p (padicZeta p hp2) := by
  sorry

/-- **RJW Prop. 4.11 (`PropInterpolation2`), interpolation**: every witness `ν` of
`([b]−[1])·ζ_p ∈ Λ(ℤ_p^×)` has moments
`∫ x^k ν = (b^k−1)(1−p^{k−1}) ζ(1−k)` — i.e. `∫_{ℤ_p^×} x^k ζ_p = (1−p^{k−1})ζ(1−k)`
in the pseudo-measure moment encoding. -/
theorem padicZeta_moments (hp2 : p ≠ 2) (b : ℤ_[p]ˣ) {k : ℕ} (hk : 0 < k)
    (ν : PadicMeasure p ℤ_[p]ˣ)
    (hν : algebraMap _ (QuotientField p) (dirac p b - 1) * padicZeta p hp2
      = algebraMap _ _ ν) :
    ((ν (unitsPowCM p k) : ℤ_[p]) : ℚ_[p])
      = ((b : ℚ_[p]) ^ k - 1) * (1 - (p : ℚ_[p]) ^ (k - 1))
          * ((zetaNeg (k - 1) : ℚ) : ℚ_[p]) := by
  sorry

/-- **RJW Thm. 4.1 (`thm:kubota leopoldt theorem`)**: there is a unique pseudo-measure
`ζ_p` on `ℤ_p^×` with `∫_{ℤ_p^×} x^k ζ_p = (1−p^{k−1}) ζ(1−k)` for all `k > 0`
(moments encoded via the witnesses of `([b]−[1])·ζ_p`). -/
theorem kubotaLeopoldt (hp2 : p ≠ 2) :
    ∃! q : QuotientField p, IsPseudoMeasure p q ∧
      ∀ (b : ℤ_[p]ˣ) (k : ℕ), 0 < k → ∀ ν : PadicMeasure p ℤ_[p]ˣ,
        algebraMap _ (QuotientField p) (dirac p b - 1) * q = algebraMap _ _ ν →
          ((ν (unitsPowCM p k) : ℤ_[p]) : ℚ_[p])
            = ((b : ℚ_[p]) ^ k - 1) * (1 - (p : ℚ_[p]) ^ (k - 1))
                * ((zetaNeg (k - 1) : ℚ) : ℚ_[p]) := by
  sorry

end PadicMeasure
