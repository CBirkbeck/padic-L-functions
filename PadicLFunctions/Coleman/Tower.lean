/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.ResidueZeta

/-!
# The cyclotomic tower over ℚ_p (RJW §9, TeX 2466–2511)

The local objects of Part II: a fixed compatible system `ξ_{p^n}` of
primitive `p^n`-th roots of unity (`ξ_{p^{n+1}}^p = ξ_{p^n}`), the tower
`K_n = ℚ_p(μ_{p^n})`, the uniformisers `π_n = ξ_{p^n} − 1`, the integer
rings `O_n` and their unit groups `𝒰_n`, and (at the `𝒰_∞`-ticket) the
norm-inverse-limit `𝒰_∞ = lim_n 𝒰_n`.

Design (decomposition R10.1): the tower lives *inside* `ℂ_p` — matching
the source's own framing of the `π_n` as points of the open unit ball
`B(0,1) ⊂ ℂ_p` (TeX 2528–2532) — so `K_n` is an
`IntermediateField ℚ_[p] ℂ_[p]`, the integer ring is the norm-ball, and
power-series evaluation at `π_n` is the project's `seriesEval`. The
degree ladder `[K_n : ℚ_p] = φ(p^n)` comes from Eisenstein-ness of
`Φ_{p^n}(T+1)` over `ℤ_p` (R10.2); the norm collapse
`N_{n+1,n}(ξ^b_{p^{n+1}} − 1) = ξ^b_{p^n} − 1` (TeX 2581–2585) is the
engine for both the cyclotomic units and the evaluation/norm commuting
square.
-/

open PowerSeries

namespace PadicLFunctions

namespace Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-- R9: a compatible system of primitive `p^n`-th roots of unity in `ℂ_p`
exists (`ξ_0 = 1`; each `ξ_{n+1}` is a `p`-th root of `ξ_n`, primitive of
order `p^{n+1}`): ℕ-recursion + `IsAlgClosed` roots. RJW TeX 2507: "We fix
once and for all a compatible system of roots of unity `(ξ_{p^n})_n`". -/
theorem exists_compatible_primitiveRoot :
    ∃ ξ : ℕ → ℂ_[p],
      (∀ n, IsPrimitiveRoot (ξ n) (p ^ n)) ∧ ∀ n, ξ (n + 1) ^ p = ξ n := by
  sorry

/-- The fixed compatible system `n ↦ ξ_{p^n}` (RJW TeX 2507). -/
noncomputable def zetaSys : ℕ → ℂ_[p] :=
  (exists_compatible_primitiveRoot p).choose

theorem zetaSys_primitiveRoot (n : ℕ) :
    IsPrimitiveRoot (zetaSys p n) (p ^ n) :=
  (exists_compatible_primitiveRoot p).choose_spec.1 n

theorem zetaSys_pow_p (n : ℕ) : zetaSys p (n + 1) ^ p = zetaSys p n :=
  (exists_compatible_primitiveRoot p).choose_spec.2 n

/-- R9: the local cyclotomic field `K_n = ℚ_p(μ_{p^n})`, realised inside
`ℂ_p` as `ℚ_p(ξ_{p^n})` (RJW TeX 2473). -/
noncomputable def K (n : ℕ) : IntermediateField ℚ_[p] ℂ_[p] :=
  IntermediateField.adjoin ℚ_[p] {zetaSys p n}

/-- R9: the uniformiser `π_n = ξ_{p^n} − 1` of `K_n` (RJW TeX 2507). -/
noncomputable def pi (n : ℕ) : ℂ_[p] := zetaSys p n - 1

theorem zetaSys_mem_K (n : ℕ) : zetaSys p n ∈ K p n := by sorry

theorem pi_mem_K (n : ℕ) : pi p n ∈ K p n := by sorry

theorem K_le_succ (n : ℕ) : K p n ≤ K p (n + 1) := by sorry

/-- R10.2 (degree ladder): `[K_n : ℚ_p] = φ(p^n)` — irreducibility of
`Φ_{p^n}` over `ℚ_p` via Eisenstein at `(p)` after `T ↦ T+1`
(RJW TeX 2475: "totally ramified … of degree `(p−1)p^{n−1}`"). -/
theorem finrank_K (n : ℕ) :
    Module.finrank ℚ_[p] (K p n) = Nat.totient (p ^ n) := by sorry

/-- R10.2: the norm of the uniformiser, rpow-free form:
`‖π_n‖^{φ(p^n)} = p⁻¹` for `n ≥ 1` (the Eisenstein constant term:
`N_{K_n/ℚ_p}(π_n) = ±Φ_{p^n}(1) = ±p`, and the spectral norm is
Galois-invariant). In particular `0 < ‖π_n‖ < 1`. -/
theorem norm_pi_pow_totient {n : ℕ} (hn : 1 ≤ n) :
    ‖pi p n‖ ^ Nat.totient (p ^ n) = (p : ℝ)⁻¹ := by sorry

theorem norm_pi_lt_one {n : ℕ} (hn : 1 ≤ n) : ‖pi p n‖ < 1 := by sorry

theorem pi_ne_zero {n : ℕ} (hn : 1 ≤ n) : pi p n ≠ 0 := by sorry

/-- R9: the integer ring `O_n = O_{K_n}` — the norm-unit-ball of `K_n`
(equivalently the integral closure of `ℤ_p`; the identification is the
Eisenstein-monogenicity ticket). RJW TeX 2474. -/
noncomputable def O (n : ℕ) : Subring ℂ_[p] :=
  (K p n).toSubring ⊓ integerRing ℂ_[p]

theorem pi_mem_O {n : ℕ} (hn : 1 ≤ n) : pi p n ∈ O p n := by sorry

/-- R10.2 (tower step): the minimal polynomial of `ξ_{p^{n+1}}` over `K_n`
is `X^p − ξ_{p^n}` (RJW TeX 2685: "the minimal polynomial of `ξ_{p^{n+1}}`
over `K_n` is `X^p − ξ_{p^n}`"). Stated as the two halves that downstream
proofs consume: the degree of the tower step is `p`, and `ξ_{p^{n+1}}` is
a root of `X^p − ξ_{p^n}` (the latter is `zetaSys_pow_p`). -/
theorem finrank_K_succ (n : ℕ) :
    Module.finrank (K p n) (IntermediateField.extendScalars (K_le_succ p n))
      = p := by sorry

end Coleman

end PadicLFunctions
