/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
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

/-- R7.1a: the quadratic tail of the exponential —
`‖exp w − 1 − w‖ ≤ p·‖w‖²` on the convergence ball (the `n ≥ 2` terms at
the `(p−1)`-power level). -/
theorem norm_padicExp_sub_one_sub_self_le {w : L} (hw : InExpBall p w) :
    ‖padicExp p w - 1 - w‖ ≤ (p : ℝ) * ‖w‖ ^ 2 := by sorry

end expTail

section character

/-- R7.1b: the character is a norm isometry in the exponent —
`‖y^t − 1‖ = ‖t‖·‖y−1‖` for `y ∈ 1+pℤ_p` (via the T523 exp/log bridge:
`y^t = exp(t·log y)` and `‖exp w − 1‖ = ‖w‖`, `‖log y‖ = ‖y−1‖`). -/
theorem norm_onePAdicPow_sub_one (hp2 : p ≠ 2) {y : ℤ_[p]}
    (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) (t : ℤ_[p]) :
    ‖(PadicInt.onePAdicPow p y hy t : ℤ_[p]) - 1‖ = ‖t‖ * ‖y - 1‖ := by
  sorry

/-- R7.2a: the Teichmüller value of a topological generator is a primitive
`(p−1)`-th root of unity (its reduction generates `(ZMod p)ˣ`). -/
theorem teichmuller_isPrimitiveRoot {u : ℤ_[p]ˣ}
    (hgen : ∀ n : ℕ, Subgroup.zpowers (PadicMeasure.unitsToZModPow p n u)
      = ⊤) :
    IsPrimitiveRoot (PadicInt.teichmuller p u) (p - 1) := by sorry

/-- R7.2b: for `0 < i < p−1` the branch denominator never vanishes —
`‖ω(u)^i − 1‖ = 1` beats `‖⟨u⟩^{1−s} − 1‖ < 1` (ultrametric isoceles);
this is RJW's Lemma 7.2(i) strengthened from `s = 1` to all `s`. -/
theorem branch_denom_ne_zero {u : ℤ_[p]ˣ}
    (hgen : ∀ n : ℕ, Subgroup.zpowers (PadicMeasure.unitsToZModPow p n u)
      = ⊤)
    {i : ℕ} (hi0 : 0 < i) (hi : i < p - 1) (s : ℤ_[p]) :
    (((branchChar p i s u : ℤ_[p])) : ℚ_[p]) - 1 ≠ 0 := by sorry

/-- R7.2c (RJW Lemma 7.2(ii), TeX 2224–2226): the denominator has a simple
zero at `s = 1` with derivative `−log_p⟨a⟩`:
`(s−1)⁻¹·(⟨a⟩^{1−s} − 1) → −log_p⟨a⟩` as `s → 1`, `s ≠ 1`. -/
theorem tendsto_branch_denom_div (hp2 : p ≠ 2) {u : ℤ_[p]ˣ} :
    Filter.Tendsto (fun s : ℤ_[p] => ((s : ℚ_[p]) - 1)⁻¹
        * ((((branchChar p (p - 1) (1 - s) u : ℤ_[p])) : ℚ_[p]) - 1))
      (nhdsWithin 1 {s | s ≠ 1})
      (nhds (-((pZpLog p ((PadicInt.angleUnit p u : ℤ_[p]))) : ℚ_[p]))) := by sorry

/-- R7.3a: the numerator pairing is continuous in `s` (the `p^m`-congruence
route: `s ≡ s' mod p^m ⟹ ⟨x⟩^{1−s} ≡ ⟨x⟩^{1−s'} mod p^m` uniformly in
`x`, through `onePAdicPow_sub_one_mem_pow`; then the measure norm bound).
Notably `p = 2` is allowed here. -/
theorem continuous_zetaNum_branch_pairing (m i : ℕ) :
    Continuous (fun s : ℤ_[p] =>
      (((PadicMeasure.zetaNum p m (branchChar p i (1 - s)) : ℤ_[p]))
        : ℚ_[p])) := by sorry

/-- **RJW Theorem 7.1(i)** (TeX 2189–2190): for `0 < i < p−1` the branch
`ζ_{p,i}` is continuous ("analytic") at `s = 1` — indeed everywhere, but
we state the source's claim. -/
theorem continuousAt_zetaPBranch (hp2 : p ≠ 2) {i : ℕ} (hi0 : 0 < i)
    (hi : i < p - 1) : ContinuousAt (zetaPBranch p hp2 i) 1 := by sorry

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
