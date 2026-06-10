/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.Padics.AddChar
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Coefficient rings for §5: the integer ring of a nonarchimedean field

RJW fix once and for all a finite extension `L/ℚ_p` with ring of integers `𝒪_L`
(§3.1, TeX 680–690; the requirement becomes essential in §5, TeX 1781: "the
relevant Iwasawa algebra is defined over a (fixed) finite extension L/Q_p
containing the values of η"). We work with the maximal natural generality the
§3 measure theory supports: a normed field `L` that is a nonarchimedean complete
normed `ℚ_[p]`-algebra, and its norm-unit ball `integerRing L`. Finite
extensions of `ℚ_p` and `ℂ_p` are both instances.

Main declarations:
* `PadicLFunctions.integerRing L` — the unit ball `{x : L | ‖x‖ ≤ 1}` as a
  subring (W1 in `.mathlib-quality/decomposition.md` §5).
* `IsPrimitiveRoot.norm_sub_one_lt` — `‖ζ − 1‖ < 1` for `ζ` a primitive
  `p^n`-th root of unity (W2); hence `ζ − 1` is topologically nilpotent.
* `IsPrimitiveRoot.norm_pow_sub_one_eq_one` — `‖ζ^c − 1‖ = 1` for `ζ` a
  primitive `D`-th root, `p ∤ D`, `D ∤ c` (W3; TeX 1798).
-/

open Filter Topology

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L]
  [IsUltrametricDist L] [CompleteSpace L]

/-- The integer ring (norm-unit ball) of a nonarchimedean normed field. For a
finite extension `L/ℚ_p` this is `𝒪_L` (RJW §3.1, TeX 690). -/
def integerRing : Subring L where
  carrier := {x : L | ‖x‖ ≤ 1}
  mul_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry

namespace integerRing

instance : IsUltrametricDist (integerRing L) := by sorry

instance : CompleteSpace (integerRing L) := by sorry

/-- `ℤ_[p]` maps into the unit ball: `‖algebraMap ℚ_[p] L x‖ = ‖x‖ ≤ 1`. -/
instance : Algebra ℤ_[p] (integerRing L) := by sorry

/-- The norm topology on the integer ring is linear: the balls
`{x | ‖x‖ ≤ ε}` are ideals (ultrametric + multiplicative norm). Needed for
`PowerSeries.eval₂`-substitution into `(integerRing L)⟦T⟧` (L5.1.6a). -/
instance : IsLinearTopology (integerRing L) (integerRing L) := by sorry

end integerRing

variable {p L}

/-- W2: a primitive `p^n`-th root of unity satisfies `‖ζ − 1‖ < 1`; in
particular `ζ − 1` is topologically nilpotent and `x ↦ ζ^x` extends to a
continuous additive character of `ℤ_[p]` (mathlib
`PadicInt.addChar_of_value_at_one`). Classical; cf. RJW's use of `μ_{p^n}`
throughout §5.1 (TeX 1647–1692). -/
theorem _root_.IsPrimitiveRoot.norm_sub_one_lt {ζ : L} {n : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ n)) (hn : 1 ≤ n) : ‖ζ - 1‖ < 1 := by sorry

/-- W2': hence `ζ - 1` is topologically nilpotent (powers tend to `0`). -/
theorem _root_.IsPrimitiveRoot.tendsto_pow_sub_one {ζ : L} {n : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ n)) (hn : 1 ≤ n) :
    Tendsto ((ζ - 1) ^ ·) atTop (𝓝 0) := by sorry

/-- W3: for `ζ` a primitive `D`-th root of unity with `p ∤ D` and `D ∤ c`,
the element `ζ^c − 1` has norm one (hence is a unit of the integer ring).

Source (TeX 1798): "and `ε_D^c − 1 ∈ 𝒪_L^×` (since it has norm dividing
`D`)". -/
theorem _root_.IsPrimitiveRoot.norm_pow_sub_one_eq_one {ζ : L} {D : ℕ}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) {c : ℕ} (hc : ¬ D ∣ c) :
    ‖ζ ^ c - 1‖ = 1 := by sorry

end PadicLFunctions
