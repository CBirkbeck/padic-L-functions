import PadicLFunctions.Measure.Convolution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# The measure-theoretic toolbox

RJW (arXiv:2309.15692) §3.5 (`sec:toolbox`): the standard operations on measures on
`ℤ_p` and their effect on Mahler transforms. Everything here stays over `ℤ_p`
coefficients; the two formulas requiring `p`-power roots of unity
(`EqRestrictionFormula`, `Eqphipsi`) are deferred to the §5 pass (see plan.md).

## Contents (with source labels)

* multiplication by a continuous function; by `x` — `∂ = (1+T)d/dT` (Lem. 3.24,
  `LemmaMultiplicationbyx`); evaluation `∫ xᵏ dμ = (∂ᵏ𝓐_μ)(0)` (Cor. 3.25,
  `cor:eval at x^k`).
* restriction to clopen subsets (§3.5.3).
* the `ℤ_p^×`-action `σ_a`, the operators `φ`, `ψ` (§3.5.5, `SubSectionphipsi`):
  `ψ ∘ φ = id`, `φ ∘ ψ = Res_{pℤ_p}`, `Res_{ℤ_p^×} = 1 − φψ` (Eq. `res to Zp`), and
  `μ` supported on `ℤ_p^×` ⟺ `ψ(μ) = 0` (Cor. 3.32, `CorollarySupportedZpet`).
-/

open scoped fwdDiff
open PowerSeries

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

namespace PadicMeasure

section cmul

/-- Multiplication of a measure by a continuous function: `(g·μ)(f) = μ(gf)`.

Source: RJW §3.5.2 (TeX lines 1086–1089). -/
def cmul (g : C(ℤ_[p], ℤ_[p])) (μ : PadicMeasure p ℤ_[p]) : PadicMeasure p ℤ_[p] :=
  μ.comp (LinearMap.mulLeft ℤ_[p] g)

@[simp]
lemma cmul_apply (g f : C(ℤ_[p], ℤ_[p])) (μ : PadicMeasure p ℤ_[p]) :
    cmul p g μ f = μ (g * f) := rfl

/-- The operator `∂ = (1+T) d/dT` on power series. Source: RJW Lem. 3.24. -/
noncomputable def del (F : PowerSeries ℤ_[p]) : PowerSeries ℤ_[p] :=
  (1 + PowerSeries.X) * F.derivativeFun

/-- Multiplication by `x` on measures corresponds to `∂` on Mahler transforms:
`𝓐_{xμ} = ∂ 𝓐_μ`. Proof: `x·binom(x,n) = (n+1)·binom(x,n+1) + n·binom(x,n)`.

Source: RJW Lem. 3.24 (`LemmaMultiplicationbyx`, TeX lines 1066–1075). -/
theorem mahlerTransform_cmul_X (μ : PadicMeasure p ℤ_[p]) :
    mahlerTransform p (cmul p (ContinuousMap.id ℤ_[p]) μ) = del p (mahlerTransform p μ) := by
  sorry

/-- The monomial `x ↦ x^k` as a continuous map. -/
def powCM (k : ℕ) : C(ℤ_[p], ℤ_[p]) := ⟨fun x => x ^ k, by fun_prop⟩

/-- `∫_{ℤ_p} xᵏ dμ = (∂ᵏ 𝓐_μ)(0)`.

Source: RJW Cor. 3.25 (`cor:eval at x^k`, TeX lines 1079–1082). -/
theorem apply_powCM (μ : PadicMeasure p ℤ_[p]) (k : ℕ) :
    μ (powCM p k) = PowerSeries.constantCoeff ((del p)^[k] (mahlerTransform p μ)) := by
  sorry

end cmul

section res

/-- Restriction of a measure to a clopen subset `U ⊆ ℤ_p`:
`(Res_U μ)(f) = μ(𝟙_U · f)`, viewed as a measure on `ℤ_p`.

Source: RJW §3.5.3 (TeX lines 1100–1103). -/
noncomputable def res {U : Set ℤ_[p]} (hU : IsClopen U) (μ : PadicMeasure p ℤ_[p]) :
    PadicMeasure p ℤ_[p] :=
  cmul p (LocallyConstant.charFn ℤ_[p] hU : C(ℤ_[p], ℤ_[p])) μ

/-- A measure is *supported on* a clopen `U` if `Res_U μ = μ` (RJW TeX line 1108). -/
def IsSupportedOn {U : Set ℤ_[p]} (hU : IsClopen U) (μ : PadicMeasure p ℤ_[p]) : Prop :=
  res p hU μ = μ

/-- Restriction is additive over a disjoint clopen decomposition.

Source: RJW §3.5.4 (TeX line 1129): "we can write X ... as a disjoint union". -/
theorem res_union {U V : Set ℤ_[p]} (hU : IsClopen U) (hV : IsClopen V)
    (hUV : Disjoint U V) (μ : PadicMeasure p ℤ_[p]) :
    res p (hU.union hV) μ = res p hU μ + res p hV μ := by
  sorry

end res

section phipsi

/-- Multiplication by a fixed `a : ℤ_[p]` as a continuous self-map of `ℤ_[p]`. -/
def mulCM (a : ℤ_[p]) : C(ℤ_[p], ℤ_[p]) := ⟨fun x => a * x, by fun_prop⟩

/-- The `ℤ_p^×`-action on measures: `∫ f d(σ_a μ) = ∫ f(ax) dμ`.

Source: RJW §3.5.5 (TeX lines 1135–1136). -/
noncomputable def sigma (a : ℤ_[p]ˣ) : PadicMeasure p ℤ_[p] →ₗ[ℤ_[p]] PadicMeasure p ℤ_[p] :=
  pushforward p (mulCM p (a : ℤ_[p]))

/-- The operator `φ` ("`σ_p`"): `∫ f d(φμ) = ∫ f(px) dμ`.

Source: RJW §3.5.5 (TeX lines 1141–1142). -/
noncomputable def phi : PadicMeasure p ℤ_[p] →ₗ[ℤ_[p]] PadicMeasure p ℤ_[p] :=
  pushforward p (mulCM p (p : ℤ_[p]))

/-- `𝓐_{σ_a μ} = 𝓐_μ((1+T)^a − 1)`: the `ℤ_p^×`-action on power series is substitution
into the binomial series. (Constant coefficient of `(1+T)^a − 1` is `0`, so mathlib's
algebraic `PowerSeries.subst` applies.)

Source: RJW §3.5.5 (TeX line 1138). -/
theorem mahlerTransform_sigma (a : ℤ_[p]ˣ) (μ : PadicMeasure p ℤ_[p]) :
    mahlerTransform p (sigma p a μ) =
      PowerSeries.subst (binomialSeries ℤ_[p] (a : ℤ_[p]) - 1) (mahlerTransform p μ) := by
  sorry

/-- `𝓐_{φ(μ)} = 𝓐_μ((1+T)^p − 1)` — Eq. (3.9) (`eq:varphi power series`).

Source: RJW TeX lines 1144–1146. -/
theorem mahlerTransform_phi (μ : PadicMeasure p ℤ_[p]) :
    mahlerTransform p (phi p μ) =
      PowerSeries.subst ((1 + PowerSeries.X) ^ p - 1) (mahlerTransform p μ) := by
  sorry

/-- The canonical "digit shift" `x ↦ (x − [x mod p])/p` as a continuous map, where
`[x mod p]` is the canonical lift `PadicInt.appr x 1`. Satisfies `shiftDiv (p*x) = x`.
Auxiliary for the `ψ` operator. -/
noncomputable def shiftDiv : C(ℤ_[p], ℤ_[p]) where
  toFun x := ⟨((x : ℚ_[p]) - (x.appr 1 : ℚ_[p])) / (p : ℚ_[p]), by sorry⟩
  continuous_toFun := by sorry

@[simp]
lemma shiftDiv_mul (x : ℤ_[p]) : shiftDiv p ((p : ℤ_[p]) * x) = x := by
  sorry

/-- `pℤ_p ⊆ ℤ_p` is clopen (it is the closed ball of radius `1/p`). -/
lemma isClopen_pZp : IsClopen {x : ℤ_[p] | ‖x‖ < 1} := by
  sorry

/-- The operator `ψ`: `∫ f d(ψμ) = ∫_{pℤ_p} f(p⁻¹x) dμ`.

Source: RJW §3.5.5 (TeX lines 1147–1148). -/
noncomputable def psi (μ : PadicMeasure p ℤ_[p]) : PadicMeasure p ℤ_[p] where
  toFun f :=
    μ ((LocallyConstant.charFn ℤ_[p] (isClopen_pZp p) : C(ℤ_[p], ℤ_[p])) *
      f.comp (shiftDiv p))
  map_add' _ _ := by sorry
  map_smul' _ _ := by sorry

/-- `ψ ∘ φ = id`. Source: RJW TeX lines 1149–1150, first display. -/
@[simp]
theorem psi_phi (μ : PadicMeasure p ℤ_[p]) : psi p (phi p μ) = μ := by
  sorry

/-- `φ ∘ ψ = Res_{pℤ_p}`. Source: RJW TeX lines 1149–1151, second display. -/
theorem phi_psi (μ : PadicMeasure p ℤ_[p]) :
    phi p (psi p μ) = res p (isClopen_pZp p) μ := by
  sorry

/-- `ℤ_p^× ⊆ ℤ_p` (the units, i.e. `‖x‖ = 1`) is clopen. -/
lemma isClopen_units : IsClopen {x : ℤ_[p] | IsUnit x} := by
  sorry

/-- `Res_{ℤ_p^×} = 1 − φ∘ψ` — Eq. (3.10) (`res to Zp`).

Source: RJW TeX lines 1152–1154. -/
theorem res_units_eq (μ : PadicMeasure p ℤ_[p]) :
    res p (isClopen_units p) μ = μ - phi p (psi p μ) := by
  sorry

/-- **RJW Cor. 3.32 (`CorollarySupportedZpet`)**: a measure is supported on `ℤ_p^×` if
and only if `ψ(μ) = 0`. (Source proof uses injectivity of `φ`, which here follows from
`ψ ∘ φ = id`; TeX lines 1161–1167.) -/
theorem isSupportedOn_units_iff_psi_eq_zero (μ : PadicMeasure p ℤ_[p]) :
    IsSupportedOn p (isClopen_units p) μ ↔ psi p μ = 0 := by
  sorry

end phipsi

end PadicMeasure
