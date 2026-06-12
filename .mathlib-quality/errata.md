# Errata and formalisation notes for RJW (arXiv:2309.15692)

Mistakes, typos, and glossed gaps in Rodrigues Jacinto–Williams, *An
introduction to p-adic L-functions*, found while formalising. Line numbers
refer to `.mathlib-quality/references/2309.15692-padic-L-functions.tex`.
Maintained as found (standing rule, CLAUDE.md). Three severity classes:
**typo** (wrong as printed, fix obvious), **gap** (statement or proof needs
an argument/hypothesis the notes don't supply), **subtlety** (correct as
mathematics, but the implicit framework hides real content that
formalisation had to make explicit).

## Typos

1. **TeX 2009 (§6.1, proof of Thm 6.1(i))** — typo. The opening display
   reads `L(θ,s) = Σ_{a ∈ (ℤ/Nℤ)ˣ} θ(a) Σ_{n ≡ a mod D} n^{−s}`; the inner
   congruence should be **mod N**, not mod D (D is the tame conductor of
   §6.2; the indicator computed two lines later is correctly mod N).

2. **TeX 2122 (§6.2, proof of Thm 6.1(ii), case split)** — off-by-one. The
   two cases are stated as "First assume that **n > 1**, so that χ ≠ 1" and
   "Now assume n = 0"; the case n = 1 is skipped as printed. The first case
   should read **n ≥ 1** (the argument is verbatim the same).

3. **TeX 1952 (§5.3, proof of Thm 5.19)** — dropped ω⁻¹. The first line of
   the aligned display reads `∫_{ℤ_p^×} χ(x)⟨x⟩^{k−1}·μ_η = ∫ χω^{−k}(x)
   x^{k−1}·μ_η`; by eq:alternative (TeX 1987) the left-hand side should be
   `∫ χω^{−1}(x)⟨x⟩^{k−1}·μ_η` — exactly the quantity the preceding
   sentence computes.

4. **TeX 1934 (§5.3, remark after Def 5.18)** — LaTeX glitch: `\begin{remark}
   \item An equivalent definition is …` has an `\item` with no enclosing
   list environment.

5. **TeX 2146 (§6.2, case n = 0)** — wording: "the assignment c ↦ c' = pc
   defines an automorphism of (ℤ/Nℤ)ˣ". Multiplication by p is a bijection
   of the unit set (and an automorphism of the additive group), but not a
   group automorphism of (ℤ/Nℤ)ˣ. Only bijectivity is used.

## Gaps

6. **Thm 6.1(ii) at tame conductor D = 1 (TeX 1987–1995 vs §5.2 standing
   hypotheses)** — scope gap. The theorem is stated for every non-trivial
   θ = χη, but the proof routes through μ_η/F_η, whose construction
   (TeX 1793–1798) carries §5.2's standing assumption **D > 1** ("η has
   conductor D, where D > 1"): at D = 1 the defining series has denominators
   `(1+T)ε_D^c − 1` with ε_D = 1, i.e. `T`, which is not invertible, and the
   correct object is the χ-twist of the *pseudo-measure* ζ_p. The pure
   p-power-conductor case needs its own (short) argument the notes don't
   give. Formalisation: `LpFunction_one` is stated for D > 1 (replan R6.4);
   D = 1 deferred.

7. **TeX 2040–2044 (§6.1, evaluation at s = 1)** — convergence gloss. "we
   may consider the Taylor series expansion −log(1−ε^c) = Σ ε^{nc}/n.
   Substituting this into (eq. 6.1), we see the series converges at s = 1
   to the required result." The series is only **conditionally** convergent
   on the unit circle, the substitution is at the boundary of the halfplane
   of convergence, and identifying `lim_{s→1⁺} Σ ε^{nc} n^{−s}` with
   `Σ ε^{nc}/n` requires an Abel-type limit theorem for Dirichlet series
   (which mathlib lacked; formalised as `tendsto_LSeries_pow_boundary`).
   Standard, but a genuine analytic step, not a substitution.

## Subtleties surfaced by formalisation

8. **Eqphipsi on unbounded series (used at TeX 2128–2134)** — the formula
   `(φ∘ψ)F = p⁻¹ Σ_{ξ∈μ_p} F((1+T)ξ−1)` is applied to F̃_θ ∈ ℛ⁺. As a
   *formal* power-series identity the right side is ill-formed (the
   substitution T ↦ (1+T)ξ−1 has non-nilpotent constant term ξ−1 for
   ξ ≠ 1); it is an identity of rigid-analytic functions on the open disc.
   Formalisation realises it as a convergent-evaluation statement
   (`sum_seriesEval_mahlerK`, decomposition replan R6.6).

9. **The ψ/digit decomposition is integral (relevant to §3.5.5 and the §6
   use of ψ on F̃_θ)** — the unique decomposition `F = Σ_{i<p} (1+T)^i·
   φ(F_i)` underlying ψ holds over ℤ_p-type (p-adically complete integral)
   coefficient rings but is **false** over a field containing 1/p: there
   `(1+T)^p − 1` has unit linear coefficient, φ is bijective, and digits
   are wildly non-unique (counterexample over ℚ, p = 2, recorded in
   b2_log.jsonl T605). The notes never need the field-coefficient version,
   but any reading of ψ as "defined on all of K⟦T⟧" is wrong; the §6
   computation must (and, reorganised, does) run through integral or
   evaluated forms only.

10. **RJW Thm 5.17's "in particular" (TeX 1927, remark after the theorem)**
    — "ζ_{p,i} is identically zero whenever i is odd" follows from the
    interpolation formula *plus* density of the interpolation points *plus*
    continuity of ζ_{p,i} in s; the notes present it as immediate. (Prose
    remark only; recorded in the blueprint node note.)

---
*Add new entries as found; cite TeX line numbers and, where applicable, the
b2_log.jsonl entry and the Lean declaration that resolves the issue.*
