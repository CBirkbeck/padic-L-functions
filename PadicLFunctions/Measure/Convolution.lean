import PadicLFunctions.Measure.MahlerTransform

/-!
# The convolution algebra structure on measures on ℤ_p

RJW (arXiv:2309.15692) §3.3: the Iwasawa algebra structure on `ℳ(ℤ_p, ℤ_p)`. The source
obtains the ring structure "by transport of structure" (Rem. 3.11,
`RemarkConvolution`, TeX line 908) and describes it by the convolution formula

  `∫ φ d(μ*λ) = ∫ (∫ φ(x+y) dλ(y)) dμ(x)`,

leaving "one checks that this does give an algebra structure" to the reader. We follow
the source exactly: the multiplication is *defined* by transporting the power-series
multiplication along `mahlerLinearEquiv`, and the convolution formula is the theorem
`PadicMeasure.mul_apply`, proved on the Mahler basis via the Chu–Vandermonde identity
(`add_choose_eq`) and density.

## Main results

* `instCommRing : CommRing (PadicMeasure p ℤ_[p])` — the Iwasawa algebra `Λ(ℤ_p)`.
* `PadicMeasure.mahlerRingEquiv : PadicMeasure p ℤ_[p] ≃+* ℤ_p[[T]]` — RJW Thm. 3.20.
* `PadicMeasure.mul_apply` — the convolution formula (RJW Rem. 3.11).
* `PadicMeasure.dirac_mul_dirac` — `δ_a * δ_b = δ_{a+b}` (`[a]·[b] = [a+b]`).
-/

open scoped fwdDiff
open PowerSeries

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

namespace PadicMeasure

/-- Multiplication of measures on `ℤ_p`, transported from `ℤ_p[[T]]` along the Mahler
transform. RJW Rem. 3.11: "by transport of structure we obtain such a structure on
`ℳ(ℤ_p, 𝒪_L)`". The convolution description is `PadicMeasure.mul_apply`. -/
noncomputable instance : Mul (PadicMeasure p ℤ_[p]) :=
  ⟨fun μ ν => (mahlerLinearEquiv p).symm (mahlerLinearEquiv p μ * mahlerLinearEquiv p ν)⟩

/-- The unit measure: `δ_0` (whose Mahler transform is `(1+T)^0 = 1`). -/
noncomputable instance : One (PadicMeasure p ℤ_[p]) := ⟨dirac p 0⟩

lemma mul_def (μ ν : PadicMeasure p ℤ_[p]) :
    μ * ν = (mahlerLinearEquiv p).symm (mahlerLinearEquiv p μ * mahlerLinearEquiv p ν) :=
  rfl

lemma one_def : (1 : PadicMeasure p ℤ_[p]) = dirac p 0 := rfl

/-- The Mahler transform is multiplicative: `𝓐_{μ·ν} = 𝓐_μ · 𝓐_ν`. -/
@[simp]
theorem mahlerTransform_mul (μ ν : PadicMeasure p ℤ_[p]) :
    mahlerTransform p (μ * ν) = mahlerTransform p μ * mahlerTransform p ν := by
  sorry

/-- `𝓐_{δ_0} = 1`. -/
@[simp]
theorem mahlerTransform_one : mahlerTransform p (1 : PadicMeasure p ℤ_[p]) = 1 := by
  sorry

/-- The Iwasawa algebra `Λ(ℤ_p) = ℳ(ℤ_p, ℤ_p)` as a commutative ring.

Source: RJW Rem. 3.11 (`RemarkConvolution`, TeX lines 907–911); ring laws are inherited
from `ℤ_p[[T]]` through the Mahler bijection. -/
noncomputable instance : CommRing (PadicMeasure p ℤ_[p]) where
  mul_assoc _ _ _ := by sorry
  one_mul _ := by sorry
  mul_one _ := by sorry
  left_distrib _ _ _ := by sorry
  right_distrib _ _ _ := by sorry
  zero_mul _ := by sorry
  mul_zero _ := by sorry
  mul_comm _ _ := by sorry

/-- **RJW Theorem 3.20 (`thm:mahler`)**: the Mahler transform is an isomorphism of
`ℤ_[p]`-algebras `ℳ(ℤ_p, 𝒪_L) ≅ 𝒪_L[[T]]` (here `𝒪 = ℤ_p`). -/
noncomputable def mahlerRingEquiv : PadicMeasure p ℤ_[p] ≃+* PowerSeries ℤ_[p] :=
  { mahlerLinearEquiv p with
    map_mul' := by sorry }

/-- **The convolution formula** (RJW Rem. 3.11, TeX line 909):
`∫ φ d(μ*ν) = ∫ (∫ φ(x+y) dν(y)) dμ(x)`. Proved by checking on the Mahler basis
(Chu–Vandermonde: `binom(x+y, n) = ∑_{i+j=n} binom(x,i)·binom(y,j)`,
mathlib's `add_choose_eq`) and extending by linearity, continuity and density. -/
theorem mul_apply (μ ν : PadicMeasure p ℤ_[p]) (f : C(ℤ_[p], ℤ_[p])) :
    (μ * ν) f =
      μ ⟨fun x => ν (f.comp ⟨fun y => x + y, by fun_prop⟩), by sorry⟩ := by
  sorry

/-- `δ_a * δ_b = δ_{a+b}`: in Iwasawa-algebra notation, `[a]·[b] = [a+b]`.

Source: RJW Ex. 3.12 + Ex. 3.16 (Dirac measures correspond to group elements `[a]`,
and `(1+T)^a (1+T)^b = (1+T)^{a+b}` — mathlib's `binomialSeries_add`). -/
@[simp]
theorem dirac_mul_dirac (a b : ℤ_[p]) :
    dirac p a * dirac p b = dirac p (a + b) := by
  sorry

end PadicMeasure
