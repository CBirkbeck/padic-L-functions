# Development Plan: §3 Measures and Iwasawa algebras (arXiv:2309.15692)

## Goal

Formalise the measure-theoretic foundations of the Kubota–Leopoldt construction,
§3.2–3.6 of Rodrigues Jacinto–Williams (RJW), *An introduction to p-adic
L-functions* (source TeX: `.mathlib-quality/references/2309.15692-padic-L-functions.tex`,
lines 671–1287). Headline targets, in Lean form:

1. `PadicMeasure p X := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` for `X` compact, with automatic
   continuity/boundedness (RJW Def 3.6 `def:measures` + the O_L-integrality convention).
2. `mahlerRingEquiv : PadicMeasure p ℤ_[p] ≃+* PowerSeries ℤ_[p]` — the Mahler/Amice
   transform as a ring isomorphism (RJW Thm 3.20 `thm:mahler`).
3. The measure-theoretic toolbox (RJW §3.5): multiplication by `x` ↔ `(1+T)d/dT`,
   restriction to clopens, `σ_a`, `φ`, `ψ`, `ψ∘φ = id`, `φ∘ψ = Res_{pℤ_p}`,
   `Res_{ℤ_p^×} = 1 − φψ`, and `supported on ℤ_p^× ↔ ψ = 0` (RJW Cor 3.32).
4. Pseudo-measures on `ℤ_p^×` (RJW §3.6): convolution ring `Λ(ℤ_p^×)`, the
   zero-divisor lemma (RJW Lem 3.36 `lem:zero divisor`), augmentation ideal, and
   `μ/([a]−[1])` is a pseudo-measure (RJW Lem 3.38 `lem:pseudo-measure existence`).

## References

- [RJW] = arXiv:2309.15692v2, §3 (lines 671–1439 of the TeX). All source quotes in
  `decomposition.md` cite TeX line numbers from this file.
- [Colmez] Colmez, *Fonctions d'une variable p-adique* (RJW's own reference for §3;
  mathlib's `MahlerBasis.lean` also follows it). Not needed directly — mathlib covers
  the analytic input.

## Mathlib Inventory (all names verified by reading the source in `.lake/packages/mathlib`)

| Concept | Mathlib status | Our action |
|---|---|---|
| ℤ_p, ℚ_p, completeness, `denseRange_natCast`, `isUnit_iff`, `toZModPow`, `ker_toZModPow`, `appr` | `NumberTheory.Padics.{PadicIntegers,RingHoms}` | USE |
| Mahler basis `mahler k : C(ℤ_[p], ℤ_[p])`, `hasSum_mahler`, `fwdDiff_tendsto_zero`, `mahlerSeries`, `fwdDiff_mahlerSeries`, `mahlerEquiv`, `norm_mahler_eq` | `NumberTheory.Padics.MahlerBasis` | USE (this is RJW Thm 3.13 in full) |
| `Δ_[h]` forward differences | `Algebra.Group.ForwardDiff` | USE |
| `BinomialRing ℤ_[p]`, `Ring.choose`, Chu–Vandermonde `add_choose_eq` (line 519), `descPochhammer_eq_factorial_smul_choose` (line 390) | `RingTheory.Binomial` | USE |
| `(1+X)^r` as `PowerSeries.binomialSeries`, `binomialSeries_add`, `binomialSeries_coeff` | `RingTheory.PowerSeries.Binomial` | USE |
| `PowerSeries.subst`, `substAlgHom`, `HasSubst.of_constantCoeff_zero'` | `RingTheory.PowerSeries.Substitution` | USE for σ_a, φ (const coeff 0 ✓) |
| `PowerSeries.derivativeFun` | `RingTheory.PowerSeries.Derivative` | USE for `∂ = (1+T)d/dT` |
| Sup-norm ring structure on `C(X, R)`, X compact; `ContinuousMap.isUltrametricDist` | `Topology.ContinuousMap.Compact`, `Topology.MetricSpace.Ultra.ContinuousMaps` | USE |
| `ContinuousMap.curry` | `Topology.CompactOpen` (line 419) | USE for convolution |
| `LocallyConstant`, `charFn` (clopen indicator) | `Topology.LocallyConstant.{Basic,Algebra}` | USE |
| Density of locally constant in `C(X, ℤ_[p])`, X compact | **MISSING** | DEFINE+PROVE (leaf L1.4; RJW proves it at lines 782–802) |
| p-adic measures, Amice/Mahler transform of measures, convolution algebra, Iwasawa algebra, pseudo-measures | **MISSING** (no `Amice`/Iwasawa-algebra/Kubota–Leopoldt hits) | THE PROJECT |
| `CompactSpace ℤ_[p]ˣ` | **MISSING** (Units topology exists in `Topology.Algebra.Constructions`) | PROVE (leaf L5.1) |
| `IsCyclic (ZMod (p^n))ˣ`, p odd | `RingTheory.ZMod.UnitsCyclic` `isCyclic_units_of_prime_pow` (line 198) | USE |
| `MonoidAlgebra` over comm ring/group | `Algebra.MonoidAlgebra.*` | USE for finite levels |
| Nested compact intersection | `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` | USE for the inverse-limit step of Lem 3.38 |
| `FractionRing` (localisation at non-zero-divisors) | `RingTheory.Localization` | USE for Q(ℤ_p^×) |

## File Structure (build order)

- `PadicLFunctions/Measure/Basic.lean` — `PadicMeasure`, auto-continuity, Dirac,
  pushforward along continuous maps, locally-constant density + ext.
- `PadicLFunctions/Measure/MahlerTransform.lean` — `mahlerCoeff`, `mahlerTransform`,
  evaluation formula, injectivity, inverse, `mahlerLinearEquiv`, `𝓐(δ_a) = (1+T)^a`.
- `PadicLFunctions/Measure/Convolution.lean` — `CommRing (PadicMeasure p ℤ_[p])` by
  transport along `mahlerLinearEquiv` (RJW line 908 "by transport of structure"),
  `mahlerRingEquiv`, the convolution formula `mul_apply` (Chu–Vandermonde), Diracs.
- `PadicLFunctions/Measure/Toolbox.lean` — mult-by-x ↔ ∂, eval at x^k, Res, σ_a, φ, ψ
  and all identities of RJW §3.5 that stay over ℤ_p.
- `PadicLFunctions/Measure/UnitsZp.lean` — `CompactSpace ℤ_[p]ˣ`, val is closed
  embedding with clopen range, extension-by-zero, ι : Λ(ℤ_p^×) ↪ Λ(ℤ_p), image = ker ψ.
- `PadicLFunctions/Measure/PseudoMeasure.lean` — convolution ring on `Λ(ℤ_p^×)`
  (Fubini-for-duals via locally-constant box decomposition), degree map, augmentation
  ideal, finite-level maps, zero-divisor lemma, pseudo-measures, RJW Lem 3.38.

## Dependency Graph

```
Basic ──→ MahlerTransform ──→ Convolution ──→ Toolbox ──→ UnitsZp ──→ PseudoMeasure
  └──────────────(density, pushforward used throughout)─────────────────┘
```

## Generality Decisions

1. **Coefficients = ℤ_p (not O_L) in this pass.** RJW fixes a finite `L/ℚ_p` once, but
   every object through §4 (the measures `μ_a`, θ_a, ζ_p) is ℤ_p-valued; larger
   coefficients are first *needed* in §5 (Dirichlet characters of conductor p^n, Gauss
   sums). Decision: develop §3 over ℤ_p; run a dedicated generalisation pass
   (`/generalise`) to `𝒪_L` when the §5 /develop pass starts. Risk recorded: the
   statements have been designed so the generalisation is parameter-insertion, not
   redesign (the Mahler input `mahlerEquiv` is already stated for general normed
   ℤ_[p]-modules `E`).
2. **`X` arbitrary (compact) where possible.** `PadicMeasure p X` is defined for any
   topological `X`; compactness is assumed per-lemma. This matches RJW's remark (line
   768–770) that the definitions apply to any subset of `G`.
3. **Ring structure on Λ(ℤ_p) by transport** along the Mahler equivalence — RJW's own
   words (line 908: "by transport of structure"); the convolution integral formula is
   the "one checks" theorem, proved on the Mahler basis via Chu–Vandermonde + density.
4. **Λ(ℤ_p^×) by direct convolution** (the group is multiplicative, so no `to_additive`
   gymnastics; ℤ_p never needs the direct convolution definition).

## Deferred (recorded so nothing is silently dropped)

| Item | Source | Why deferred | Where it lands |
|---|---|---|---|
| §3.1 Banach prelims (valuations, orthonormal bases, dual topologies) | lines 680–744 | mathlib's normed-space + `mahlerEquiv` supply everything these anchor; RJW says §3.1 "may be skipped" | not formalised; blueprint nodes stay prose |
| `M(G,O) ≅ projlim O[G/H]` for profinite G + Iwasawa-algebra-as-limit (Props 3.9/3.10) | lines 850–921 | not needed for §4–5: Λ(ℤ_p) ≅ ℤ_p[[T]] is proved directly (the source's own thm:mahler proof); finite-LEVEL maps (not the full limit) suffice for Lem 3.38 | Part II pass (§11, measures on Galois groups) |
| Additive-functions-on-clopens description (Rem 3.7/3.8) | lines 782–829 | only its locally-constant-density ingredient is needed now (L1.4); the clopen-additive-function equivalence is pulled in by the Part II pass | Part II pass; density leaf done NOW |
| z-twist power-series formula `𝓐(z^x μ) = 𝓐μ((1+T)z−1)` and ξ-restriction formulas `EqRestrictionFormula`/`Eqphipsi` | lines 1084–1158 | substitution at non-nilpotent constant term + coefficients in ℤ_p[μ_{p^n}] ⊄ ℤ_p: both need the O_L pass. All §3–4 identities that *use* them have ξ-free measure-side proofs (planned as such) | §5 interpolation pass |
| §3.7 locally analytic functions/distributions | lines 1287–1439 | RJW: "may be safely skipped on a first reading"; first used in §6–7 | §6–7 pass |

## ChatGPT validation

`ask_chatgpt_math` not available in this session — skipped per the skill.

## §4 addendum (2026-06-10) — Kubota–Leopoldt

### Mathlib inventory (§4-specific, all grep-verified at file:line)
| Concept | Mathlib status | Our action |
|---------|---------------|------------|
| Bernoulli gen. function | `bernoulliPowerSeries_mul_exp_sub_one` (Bernoulli.lean:273) | USE |
| `B_odd = 0` | `bernoulli_eq_zero_of_odd` (:217) | USE |
| `ζ(−n)` complex | `riemannZeta_neg_nat_eq_bernoulli` (HurwitzZetaValues) | USE (bridge file only) |
| `exp`, `e^{at}` | `PowerSeries.exp`, `exp_pow_eq_rescale_exp` (Exp.lean:153) | USE |
| Chain rule for subst | `PowerSeries.derivative_subst` (Derivative.lean:184) | USE |
| `constantCoeff_subst` | Substitution.lean:244 | USE |
| PS unit ⟺ const unit | `isUnit_iff_constantCoeff` (Inverse.lean:111) | USE |
| ℕ coprime p unit in ℤ_p | not found | DEFINE `PadicInt.isUnit_natCast_of_not_dvd` (PR candidate) |
| Λ(ℤ_p) domain | — | DEFINE instance via `mahlerRingEquiv` transport |
| projection formula ψ(φν·μ)=ν·ψμ | — | DEFINE (`psi_phi_mul`) |
| integer top. generator | — | DEFINE `exists_nat_topological_generator` (Washington §3 classical) |

### §4 design decisions
- **ζ-values**: `zetaNeg k := (−1)^k bernoulli (k+1)/(k+1) : ℚ` (TeX 1455's own
  formula); all interpolation in ℚ_p via `Rat.cast`; complex bridge quarantined in
  `ZetaValuesComplex.lean`. `kl-values-of-zeta` blueprint node unwired until §2
  Mellin theory.
- **F_a**: defined by clearing denominators — `Fa := ((geomSum−a)/X)·Ring.inverse
  geomSum`, characterised by `((1+X)^a−1)·Fa = geomSum − a`. Junk-total defs,
  `hpa : ¬ p ∣ a` on lemmas.
- **ψ-invariance replan** (T034): source's ξ/μ_p-proof replaced by projection
  formula + finite Dirac identities (decomposition R3 block) — keeps the deferred
  O_L/ξ cluster deferred.
- **delQ debt**: ℚ_p-clone of `del`; merge by generalising `del` to `CommRing R`
  in a cleanup pass (do not churn §3 mid-section).
- **a : ℕ** parametrisation for μ_a (source: "integer coprime to p"); the
  topological-generator integrality gloss of Def 4.10 is made explicit
  (`exists_nat_topological_generator`, p ≠ 2).

### Deferred (unchanged from §3 + one §4 note)
- ξ/roots-of-unity `Eqphipsi`, O_L coefficients → §5 pass (T034's replan keeps
  this deferral intact).
- §2 Mellin/L(f_a,s) analytic continuation → §2 chapter pass
  (`kl-values-of-zeta` wiring blocked on it).
