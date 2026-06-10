import PadicLFunctions.Measure.PseudoMeasure
import PadicLFunctions.KubotaLeopoldt.ZetaValues
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# The measures `μ_a` (RJW §4.1–§4.2)

For `a` coprime to `p`, the power series
`F_a(T) = 1/T − a/((1+T)^a − 1) ∈ ℤ_p⟦T⟧` (RJW Prop. 4.4, `PropFaT`) is realised here
through its characterising identity `((1+T)^a − 1)·F_a = (Σ_{i<a}(1+T)^i) − a`: the
factor `(1+T)^a − 1 = T·geomSum` with `geomSum = Σ_{i<a}(1+T)^i` a unit (constant
coefficient `a`), so `F_a := ((geomSum − a)/T)·geomSum⁻¹`.

`μ_a` is the measure with Mahler transform `F_a` (RJW Def. 4.5). Its moments are
`∫ x^k dμ_a = (−1)^k (1−a^{k+1}) ζ(−k)` (RJW Prop. 4.6), proved via the substitution
`T = e^t − 1` and the Bernoulli generating function (RJW Lem. 4.2/4.3, realised
algebraically over `ℚ_p⟦t⟧` — see `X_mul_subst_exp_Fa`).

`ψ(μ_a) = μ_a` (RJW Lem. 4.7, `LemmaPsiInvariant`): the source argues through the
roots-of-unity formula for `φ∘ψ`; here we use the equivalent ξ-free route via the
projection formula `ψ(φν·μ) = ν·ψμ` and the finite Dirac-sum identity
`([a]−[0])·μ_a = Σ_{i<a}[i] − a·[0]` (replan recorded in the §4 ticket board).

Restricting to `ℤ_p^×` then removes the Euler factor:
`∫_{ℤ_p^×} x^k dμ_a = (−1)^k (1−p^k)(1−a^{k+1}) ζ(−k)` (RJW Prop. 4.8).
-/

noncomputable section

open PowerSeries

namespace PadicInt

/-- A natural number not divisible by `p` is a unit of `ℤ_p`. -/
lemma isUnit_natCast_of_not_dvd {p : ℕ} [hp : Fact p.Prime] {a : ℕ} (hpa : ¬ p ∣ a) :
    IsUnit (a : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hpa ?_)
  exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd (a : ℤ)).1 (by simpa using h)

end PadicInt

namespace PadicMeasure

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## The power series `F_a` and the measure `μ_a` (RJW §4.1) -/

/-- The geometric sum `Σ_{i<a} (1+T)^i ∈ ℤ_p⟦T⟧`, the cofactor in
`(1+T)^a − 1 = T · geomSum a`. Source: RJW Prop. 4.4 (TeX lines 1488–1494). -/
def geomSum (a : ℕ) : PowerSeries ℤ_[p] :=
  ∑ i ∈ Finset.range a, (1 + X) ^ i

@[simp]
lemma constantCoeff_geomSum (a : ℕ) : constantCoeff (geomSum p a) = (a : ℤ_[p]) := by
  simp [geomSum]

lemma geomSum_mul_X (a : ℕ) : geomSum p a * X = (1 + X) ^ a - 1 := by
  have h := geom_sum_mul (1 + X : PowerSeries ℤ_[p]) a
  rw [add_sub_cancel_left] at h
  exact h

lemma isUnit_geomSum {a : ℕ} (hpa : ¬ p ∣ a) : IsUnit (geomSum p a) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_geomSum]
  exact PadicInt.isUnit_natCast_of_not_dvd hpa

/-- The numerator `(geomSum a − a)/T` of `F_a`. -/
def FaNum (a : ℕ) : PowerSeries ℤ_[p] :=
  PowerSeries.mk fun n => coeff (n + 1) (geomSum p a)

lemma X_mul_FaNum (a : ℕ) :
    X * FaNum p a = geomSum p a - (a : PowerSeries ℤ_[p]) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul, map_sub, ← map_natCast (PowerSeries.C (R := ℤ_[p])) a,
      PowerSeries.coeff_C]
    simp [FaNum]

/-- **RJW Prop. 4.4 (`PropFaT`)**: the power series
`F_a = 1/T − a/((1+T)^a−1) ∈ ℤ_p⟦T⟧`, realised as `((geomSum a − a)/T)·geomSum a⁻¹`.
Junk value (`0` denominator-inverse) when `p ∣ a`. -/
def Fa (a : ℕ) : PowerSeries ℤ_[p] :=
  FaNum p a * Ring.inverse (geomSum p a)

lemma geomSum_mul_Fa {a : ℕ} (hpa : ¬ p ∣ a) :
    geomSum p a * Fa p a = FaNum p a := by
  rw [Fa, ← mul_assoc, mul_comm (geomSum p a) (FaNum p a), mul_assoc,
    Ring.mul_inverse_cancel _ (isUnit_geomSum p hpa), mul_one]

/-- The characterising identity `((1+T)^a − 1)·F_a = geomSum a − a`, the formal
content of `F_a = 1/T − a/((1+T)^a−1)`. Source: RJW Lem. 4.3 (TeX line 1475). -/
lemma one_add_X_pow_sub_one_mul_Fa {a : ℕ} (hpa : ¬ p ∣ a) :
    ((1 + X) ^ a - 1) * Fa p a = geomSum p a - (a : PowerSeries ℤ_[p]) := by
  rw [← geomSum_mul_X, mul_comm (geomSum p a) X, mul_assoc, geomSum_mul_Fa p hpa,
    X_mul_FaNum]

/-- **RJW Def. 4.5 (`DefinitionMeasuremua`)**: the measure `μ_a` on `ℤ_p` whose Mahler
transform is `F_a`. -/
def muA (a : ℕ) : PadicMeasure p ℤ_[p] :=
  (mahlerLinearEquiv p).symm (Fa p a)

@[simp]
lemma mahlerTransform_muA (a : ℕ) : mahlerTransform p (muA p a) = Fa p a :=
  (mahlerLinearEquiv p).apply_symm_apply (Fa p a)

@[simp]
lemma mahlerTransform_sub (μ ν : PadicMeasure p ℤ_[p]) :
    mahlerTransform p (μ - ν) = mahlerTransform p μ - mahlerTransform p ν :=
  map_sub (mahlerTransformₗ p) μ ν

@[simp]
lemma mahlerTransform_smul (c : ℤ_[p]) (μ : PadicMeasure p ℤ_[p]) :
    mahlerTransform p (c • μ) = c • mahlerTransform p μ :=
  map_smul (mahlerTransformₗ p) c μ

/-- The convolution form of the characterising identity:
`([a] − [0])·μ_a = Σ_{i<a} [i] − a·[0]` in `Λ(ℤ_p)`. (mathlib's `binomialSeries_nat`
identifies `𝓐(δ_a) = (1+T)^a`.) -/
lemma dirac_natCast_sub_one_mul_muA {a : ℕ} (hpa : ¬ p ∣ a) :
    (dirac p ((a : ℕ) : ℤ_[p]) - 1) * muA p a
      = (∑ i ∈ Finset.range a, dirac p ((i : ℕ) : ℤ_[p])) - (a : ℤ_[p]) • 1 := by
  have hsum : mahlerTransform p (∑ i ∈ Finset.range a, dirac p ((i : ℕ) : ℤ_[p]))
      = geomSum p a := by
    rw [show mahlerTransform p (∑ i ∈ Finset.range a, dirac p ((i : ℕ) : ℤ_[p]))
        = mahlerTransformₗ p (∑ i ∈ Finset.range a, dirac p ((i : ℕ) : ℤ_[p])) from rfl,
      map_sum, geomSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show mahlerTransformₗ p (dirac p ((i : ℕ) : ℤ_[p]))
        = mahlerTransform p (dirac p ((i : ℕ) : ℤ_[p])) from rfl,
      mahlerTransform_dirac, binomialSeries_nat]
  apply mahlerTransform_injective p
  rw [mahlerTransform_mul, mahlerTransform_sub, mahlerTransform_one, mahlerTransform_dirac,
    binomialSeries_nat, mahlerTransform_muA, one_add_X_pow_sub_one_mul_Fa p hpa,
    mahlerTransform_sub, mahlerTransform_smul, mahlerTransform_one, hsum,
    PowerSeries.smul_eq_C_mul, mul_one, ← map_natCast (PowerSeries.C (R := ℤ_[p])) a]

/-- `Λ(ℤ_p)` is a domain (transport along `mahlerRingEquiv` from `ℤ_p⟦T⟧`). -/
instance instIsDomain : IsDomain (PadicMeasure p ℤ_[p]) :=
  MulEquiv.isDomain (PowerSeries ℤ_[p]) (mahlerRingEquiv p).toMulEquiv

lemma dirac_natCast_sub_one_ne_zero {a : ℕ} (ha : a ≠ 0) :
    (dirac p ((a : ℕ) : ℤ_[p]) - 1 : PadicMeasure p ℤ_[p]) ≠ 0 := by
  intro h
  have h2 := congrArg (mahlerTransform p) h
  rw [mahlerTransform_sub, mahlerTransform_one, mahlerTransform_dirac, mahlerTransform_zero,
    binomialSeries_nat, sub_eq_zero] at h2
  have h3 := congrArg (PowerSeries.coeff 1) h2
  rw [show ((1 : PowerSeries ℤ_[p]) + X) ^ a = ((1 + Polynomial.X : Polynomial ℤ_[p]) ^ a :
      Polynomial ℤ_[p]).toPowerSeries by push_cast [Polynomial.coe_one, Polynomial.coe_X]; ring]
    at h3
  rw [Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow] at h3
  simp at h3
  omega

/-! ## Moments of `μ_a`: the Bernoulli computation (RJW Lem. 4.2/4.3, Prop. 4.6)

The substitution `e^t = T+1` turning `∂ = (1+T)d/dT` into `d/dt` (RJW Lem. 4.3) is
realised by `PowerSeries.subst (exp ℚ_p − 1)`; the value `f_a^{(k)}(0)` is then read
off from the Bernoulli generating function `B(t)·(e^t−1) = t` via
`t·f_a(t) = B(t) − B(at)`. -/

/-- `∂ = (1+T) d/dT` over `ℚ_p`. (To be merged with `PadicMeasure.del` when the
latter is generalised to arbitrary commutative rings — cleanup note in tickets.) -/
def delQ (G : PowerSeries ℚ_[p]) : PowerSeries ℚ_[p] :=
  (1 + X) * PowerSeries.derivativeFun G

lemma map_del (F : PowerSeries ℤ_[p]) :
    PowerSeries.map PadicInt.Coe.ringHom (del p F)
      = delQ p (PowerSeries.map PadicInt.Coe.ringHom F) := by
  sorry

lemma hasSubst_exp_sub_one : HasSubst (exp ℚ_[p] - 1) := by
  sorry

/-- Chain rule for the substitution `T = e^t − 1`: `d/dt (F(e^t−1)) = (∂F)(e^t−1)`.
Source: RJW Lem. 4.3 ("the derivative `d/dt` becomes the operator `∂`"). -/
lemma derivativeFun_subst_exp (F : PowerSeries ℚ_[p]) :
    PowerSeries.derivativeFun (F.subst (exp ℚ_[p] - 1))
      = (delQ p F).subst (exp ℚ_[p] - 1) := by
  sorry

lemma constantCoeff_subst_exp (F : PowerSeries ℚ_[p]) :
    constantCoeff (F.subst (exp ℚ_[p] - 1)) = constantCoeff F := by
  sorry

lemma constantCoeff_iterate_derivativeFun (k : ℕ) (G : PowerSeries ℚ_[p]) :
    constantCoeff (PowerSeries.derivativeFun^[k] G)
      = (k.factorial : ℚ_[p]) * coeff k G := by
  sorry

/-- `(∂^k F)(0) = k! · [t^k](F(e^t−1))`: evaluating iterated `∂` at `0` extracts
Taylor coefficients after the exponential substitution (RJW eq. between Lem. 4.3
and Prop. 4.6). -/
lemma constantCoeff_iterate_delQ (k : ℕ) (F : PowerSeries ℚ_[p]) :
    constantCoeff ((delQ p)^[k] F)
      = (k.factorial : ℚ_[p]) * coeff k (F.subst (exp ℚ_[p] - 1)) := by
  sorry

/-- The Bernoulli evaluation `t·f_a(t) = B(t) − B(at)` where `B` is the Bernoulli
generating function and `f_a = F_a(e^t−1)`: the algebraic content of RJW Lem. 4.2
(`f_a^{(k)}(0) = (−1)^k(1−a^{k+1})ζ(−k)`). -/
lemma X_mul_subst_exp_Fa {a : ℕ} (hpa : ¬ p ∣ a) :
    X * (PowerSeries.map PadicInt.Coe.ringHom (Fa p a)).subst (exp ℚ_[p] - 1)
      = bernoulliPowerSeries ℚ_[p] - rescale (a : ℚ_[p]) (bernoulliPowerSeries ℚ_[p]) := by
  sorry

/-- **RJW Prop. 4.6**: `∫_{ℤ_p} x^k dμ_a = (−1)^k (1 − a^{k+1}) ζ(−k)` in `ℚ_p`. -/
theorem muA_apply_powCM {a : ℕ} (hpa : ¬ p ∣ a) (k : ℕ) :
    ((muA p a (powCM p k) : ℤ_[p]) : ℚ_[p])
      = (-1) ^ k * (1 - (a : ℚ_[p]) ^ (k + 1)) * ((zetaNeg k : ℚ) : ℚ_[p]) := by
  sorry

/-! ## `ψ`-invariance of `μ_a` (RJW Lem. 4.7) -/

/-- Projection formula: `ψ(φ(ν)·μ) = ν·ψ(μ)` in `Λ(ℤ_p)`. The ξ-free engine for
RJW Lem. 4.7 (replan note: replaces the source's roots-of-unity partial-fraction
computation, TeX lines 1517–1524). -/
theorem psi_phi_mul (ν μ : PadicMeasure p ℤ_[p]) :
    psi p (phi p ν * μ) = ν * psi p μ := by
  sorry

@[simp]
lemma phi_dirac (x : ℤ_[p]) : phi p (dirac p x) = dirac p ((p : ℤ_[p]) * x) := by
  sorry

@[simp]
lemma psi_dirac_mul (x : ℤ_[p]) : psi p (dirac p ((p : ℤ_[p]) * x)) = dirac p x := by
  sorry

lemma psi_dirac_of_isUnit {x : ℤ_[p]} (hx : IsUnit x) : psi p (dirac p x) = 0 := by
  sorry

lemma psi_add (μ ν : PadicMeasure p ℤ_[p]) : psi p (μ + ν) = psi p μ + psi p ν := by
  sorry

lemma psi_smul (c : ℤ_[p]) (μ : PadicMeasure p ℤ_[p]) : psi p (c • μ) = c • psi p μ := by
  sorry

lemma psi_sum {ι : Type*} (s : Finset ι) (f : ι → PadicMeasure p ℤ_[p]) :
    psi p (∑ i ∈ s, f i) = ∑ i ∈ s, psi p (f i) := by
  sorry

/-- **RJW Lem. 4.7 (`LemmaPsiInvariant`)**: `ψ(μ_a) = μ_a`. -/
theorem psi_muA {a : ℕ} (hpa : ¬ p ∣ a) : psi p (muA p a) = muA p a := by
  sorry

/-! ## Restriction to `ℤ_p^×` (RJW §4.2) -/

lemma phi_apply_powCM (μ : PadicMeasure p ℤ_[p]) (k : ℕ) :
    phi p μ (powCM p k) = (p : ℤ_[p]) ^ k * μ (powCM p k) := by
  sorry

/-- **RJW Prop. 4.8 (`PropInterpolation1`)**: restricting to `ℤ_p^×` removes the
Euler factor at `p`:
`∫_{ℤ_p^×} x^k dμ_a = (−1)^k (1−p^k)(1−a^{k+1}) ζ(−k)`. -/
theorem res_units_muA_apply_powCM {a : ℕ} (hpa : ¬ p ∣ a) (k : ℕ) :
    ((res p (isClopen_units p) (muA p a) (powCM p k) : ℤ_[p]) : ℚ_[p])
      = (-1) ^ k * (1 - (p : ℚ_[p]) ^ k) * (1 - (a : ℚ_[p]) ^ (k + 1))
          * ((zetaNeg k : ℚ) : ℚ_[p]) := by
  sorry

end PadicMeasure
