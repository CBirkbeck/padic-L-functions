/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.PadicExp

/-!
# The extended (Iwasawa-branch) p-adic logarithm (RJW §6, decomposition W6a)

RJW Thm 6.1(ii) (TeX 1992–1995) evaluates `log_p` at the elements
`1 − ε_N^c`, which lie OUTSIDE the convergence ball of `padicLog`. This file
extends the logarithm to the rational-valuation domain: `x` with
`x^m = p^k·y` for some `m > 0`, `k : ℤ` and `y` in the open exponential
ball, setting `extLog x := m⁻¹·padicLog y` (junk value `0` outside;
Iwasawa's branch `log_p(p) = 0`). Construction cross-reference: Washington,
*Introduction to Cyclotomic Fields*, §5.1. The domain-membership engine for
the theorem's arguments is `extLogDomain_of_integral_norm_one`: a norm-one
element integral over `ℤ` has a power within distance `p⁻¹` of `1`
(pigeonhole in the finite ring `ℤ[z]/p`), and `p`-power iteration then
lands inside the exponential ball.

Decomposition: `.mathlib-quality/decomposition.md` R6, cluster W6a.
-/

open Filter Topology

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
  [IsUltrametricDist L] [CompleteSpace L]

/-- W6a-a1: the translated exponential ball `1 + B` is closed under
multiplication (ultrametric). -/
theorem mul_mem_expBall {y z : L} (hy : InExpBall p (y - 1))
    (hz : InExpBall p (z - 1)) : InExpBall p (y * z - 1) := by sorry

/-- W6a-a2: the logarithm of a power on the ball. -/
theorem padicLog_pow {y : L} (hy : InExpBall p (y - 1)) (n : ℕ) :
    padicLog p (y ^ n) = n • padicLog p y := by sorry

/-- W6a-a3: one `p`-th-power step contracts towards `1`
(`p ∣ (p choose i)` for `0 < i < p`). -/
theorem norm_pow_p_sub_one_le {w : L} (hw : ‖w - 1‖ < 1) :
    ‖w ^ p - 1‖ ≤ max (‖w - 1‖ ^ p) ((p : ℝ)⁻¹ * ‖w - 1‖) := by sorry

/-- W6a-a4: from the open unit ball, some `p`-power iterate lands in the
exponential ball (geometric contraction with ratio
`max (‖w−1‖^(p−1)) p⁻¹ < 1`). -/
theorem exists_pPow_pow_inExpBall {w : L} (hw : ‖w - 1‖ < 1) :
    ∃ j : ℕ, InExpBall p (w ^ p ^ j - 1) := by sorry

/-- W6a-a5 (pigeonhole): a norm-one element integral over `ℤ` has a power
within `p⁻¹` of `1` — `ℤ[z]/p` is finite, so `z^i(z^m − 1) ∈ p·ℤ[z]` for
some `i, m`, and `‖z^i‖ = 1` cancels. -/
theorem exists_pow_sub_one_norm_le {z : L} (hz : IsIntegral ℤ z)
    (hz1 : ‖z‖ = 1) : ∃ m : ℕ, 0 < m ∧ ‖z ^ m - 1‖ ≤ (p : ℝ)⁻¹ := by sorry

/-- The domain of the extended logarithm: rational-valuation elements, i.e.
`x^m = p^k·y` with `y` in the translated exponential ball. -/
def ExtLogDomain (x : L) : Prop :=
  ∃ (m : ℕ) (k : ℤ) (y : L), 0 < m ∧ x ^ m = (p : L) ^ k * y
    ∧ InExpBall p (y - 1)

open Classical in
/-- W6a-a6: the extended (Iwasawa-branch, `log_p p = 0`) logarithm,
junk-total: `extLog x = m⁻¹ • padicLog y` for a witness `x^m = p^k·y`,
and `0` off the domain. -/
noncomputable def extLog (x : L) : L :=
  if h : ExtLogDomain p x
  then ((h.choose : ℚ_[p]))⁻¹
    • padicLog p h.choose_spec.choose_spec.choose
  else 0

/-- W6a-a7 (well-definedness): every witness computes `extLog`. -/
theorem extLog_eq_of_witness {x : L} {m : ℕ} {k : ℤ} {y : L} (hm : 0 < m)
    (hxy : x ^ m = (p : L) ^ k * y) (hy : InExpBall p (y - 1)) :
    extLog p x = ((m : ℚ_[p]))⁻¹ • padicLog p y := by sorry

/-- W6a-a8: `extLog` agrees with `padicLog` on the ball. -/
theorem extLog_eq_padicLog {x : L} (hx : InExpBall p (x - 1)) :
    extLog p x = padicLog p x := by sorry

/-- W6a-a9: additivity on the domain. -/
theorem extLog_mul {x y : L} (hx : ExtLogDomain p x) (hy : ExtLogDomain p y) :
    extLog p (x * y) = extLog p x + extLog p y := by sorry

/-- W6a-a10: roots of unity have extended logarithm `0`. -/
theorem extLog_eq_zero_of_pow_eq_one {x : L} {n : ℕ} (hn : 0 < n)
    (hx : x ^ n = 1) : extLog p x = 0 := by sorry

/-- W6a-a10 (continued): `log_p(x) = log_p(−x)` (RJW's final step,
TeX 2150). -/
theorem extLog_neg {x : L} (hx : ExtLogDomain p x) :
    extLog p (-x) = extLog p x := by sorry

/-- W6a-a11 (the domain engine): norm-one elements integral over `ℤ` lie in
the extended-log domain — covers all the arguments `1 − ε_N^c` of RJW
Thm 6.1(ii) for tame conductor `D > 1`. -/
theorem extLogDomain_of_integral_norm_one {z : L} (hz : IsIntegral ℤ z)
    (hz1 : ‖z‖ = 1) : ExtLogDomain p z := by sorry

end PadicLFunctions
