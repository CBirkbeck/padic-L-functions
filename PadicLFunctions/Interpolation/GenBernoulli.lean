/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import PadicLFunctions.KubotaLeopoldt.ZetaValues

/-!
# Generalised Bernoulli numbers (the L-values of RJW §5)

RJW route the special values `L(χ, −k)` through the complex Mellin theory
(Lem 5.5/5.9 via `thm:l-function`, §2). As in §4 (where `ζ(1−k)` was the
rational `zetaNeg` and the complex comparison was quarantined), the `p`-adic
statements use the *generalised Bernoulli numbers* `B_{k,χ}` as the canonical
value, following the cross-reference Washington, *Introduction to Cyclotomic
Fields* §4.1–4.2 ("B_{n,χ}" and Thm 4.2: `L(1−n, χ) = −B_{n,χ}/n`); the
complex bridge is `GenBernoulliComplex.lean`.

`B_{k,χ} := N^{k−1} ∑_{a=1}^{N} χ(a)·B_k(a/N)` for `χ` mod `N` (Washington
Prop 4.1's polynomial form; the `a`-range `1..N` matters — it makes the
trivial-character case reduce to `B_k(1) = bernoulli' k`).
-/

open Finset

namespace PadicLFunctions

variable {L : Type*} [Field L] [CharZero L] {N : ℕ} [NeZero N]

/-- L5.1.9: the generalised Bernoulli number `B_{k,χ} ∈ L` of a Dirichlet
character `χ` mod `N` valued in a characteristic-zero field:
`B_{k,χ} = N^{k−1} ∑_{a=1}^{N} χ(a)·B_k(a/N)`
(Bernoulli-polynomial form; Washington §4.1, Prop 4.1). -/
noncomputable def _root_.DirichletCharacter.genBernoulli
    (χ : DirichletCharacter L N) (k : ℕ) : L :=
  (N : L) ^ ((k : ℤ) - 1) *
    ∑ a ∈ range N, χ (a + 1 : ℕ) *
      Polynomial.eval (((a : L) + 1) / (N : L)) ((Polynomial.bernoulli k).map (algebraMap ℚ L))

/-- The L-value `L(χ, −k)` in its `p`-adic incarnation:
`LvalNeg χ k = −B_{k+1,χ}/(k+1)` (Washington Thm 4.2). -/
noncomputable def LvalNeg (χ : DirichletCharacter L N) (k : ℕ) : L :=
  -(χ.genBernoulli (k + 1)) / (k + 1)

/-- At the trivial character mod 1, the generalised Bernoulli numbers are the
`bernoulli'` numbers (`B_k(1) = bernoulli' k`), so `LvalNeg` matches §4's
`zetaNeg`-route values: `ζ(−k) = −B'_{k+1}/(k+1)`. -/
theorem genBernoulli_one (k : ℕ) :
    (1 : DirichletCharacter L 1).genBernoulli k = (bernoulli' k : ℚ) • (1 : L) := by sorry

/-- L5.1.11 (parity vanishing): `B_{k,χ} = 0` when `χ(−1) ≠ (−1)^k` —
except in the degenerate trivial-character case `k = 1`.

Source (TeX 1744–1746): "we recover the well-known fact that `L(χ,−k) = 0`
if `χ(−1)(−1)^k = 1`" (shifted by one index here). Route: the involution
`a ↦ N − a` on the defining sum plus `B_k(1−x) = (−1)^k B_k(x)`. -/
theorem genBernoulli_eq_zero (χ : DirichletCharacter L N) {k : ℕ}
    (h : χ (-1) ≠ (-1 : L) ^ k) (hk : χ ≠ 1 ∨ k ≠ 1) :
    χ.genBernoulli k = 0 := by sorry

section generatingFunction

open PowerSeries

/-- L5.1.10a: the generating-function characterisation of `B_{k,χ}` (cleared
form): `(∑_k B_{k,χ} t^k/k!) · (e^{Nt} − 1) = ∑_{a=1}^{N} χ(a)·t·e^{at}`,
an identity in `L⟦t⟧` (Washington §4.1's defining identity, equivalent to the
polynomial definition above by the Bernoulli-polynomial generating function).
This is the §5 analogue of mathlib's `bernoulliPowerSeries_mul_exp_sub_one`
and drives the moment computations (T030–T033 pattern). -/
theorem genBernoulliPowerSeries_mul (χ : DirichletCharacter L N) :
    (PowerSeries.mk fun k => χ.genBernoulli k * (k.factorial : L)⁻¹) *
        (rescale (N : L) (exp L) - 1)
      = ∑ a ∈ range N, χ (a + 1 : ℕ) • (X * rescale ((a : L) + 1) (exp L)) := by sorry

/-- L5.1.10c: the cyclotomic product `∏_{c<M} (ζ^c·Y − 1) = Y^M − 1` for `ζ` a
primitive `M`-th root of unity (used to clear the denominators of `F_{χ,a}`
at `Y = 1+X`; the `p`-power instance of W3's product argument). -/
theorem prod_primitiveRoot_mul_sub_one {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} {M : ℕ} (hζ : IsPrimitiveRoot ζ M) (Y : R) :
    ∏ c ∈ range M, (ζ ^ c * Y - 1) = Y ^ M - 1 := by sorry

end generatingFunction

end PadicLFunctions
