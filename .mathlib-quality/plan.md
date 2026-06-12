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

## §5 addendum (2026-06-10) — Interpolation at Dirichlet characters (TeX 1610–1979)

### Mathlib survey B + §5-specific (all grep-verified at file:line in the pinned mathlib)

| Concept | Mathlib status | Our action |
|---------|---------------|------------|
| `DirichletCharacter R N`, `conductor`, `IsPrimitive`, `changeLevel`, `primitiveCharacter`, `Even/Odd`, `FactorsThrough` | `NumberTheory/DirichletCharacter/Basic.lean` (221–301, 418–427) | USE |
| Gauss sum `gaussSum χ ψ` | `NumberTheory/GaussSum.lean:72` | USE |
| Rem 5.3(ii) `G(χ) = χ(a)Σχ(c)ε^{ac}` | `gaussSum_mulShift` (GaussSum.lean:76), **`gaussSum_mulShift_of_isPrimitive`** (DirichletCharacter/GaussSum.lean:57 — all `a`, incl. non-units) | USE |
| Rem 5.3(i) `G(χ)G(χ⁻¹) = χ(−1)p^n` | only field-level `gaussSum_mul_gaussSum_eq_card` (GaussSum.lean:145; `ZMod p^n` is not a field for n ≥ 2) | **DEFINE+PROVE at general level N for primitive χ** (PR candidate; route: Ramanujan-sum/unit-sum split, ingredients `AddChar.sum_mulShift`-style all present) |
| Dirichlet L-function (analytic continuation) | `DirichletCharacter.LFunction` = `ZMod.LFunction` = Hurwitz combination (DirichletContinuation.lean:61, ZMod.lean:83) | USE (complex bridge only) |
| Hurwitz zeta at −k via Bernoulli polynomials | `hurwitzZeta_neg_nat` (HurwitzZetaValues.lean:189) | USE → derive `L(χ,−k) = −B_{k+1,χ}/(k+1)` complex-side (quarantined bridge file, ZetaValuesComplex-pattern) |
| Generalised Bernoulli numbers `B_{k,χ}` | **MISSING** | DEFINE in the coefficient field via `Polynomial.bernoulli` (BernoulliPolynomials.lean), with API |
| Mahler basis for general coefficients | `PadicInt.mahlerEquiv : C(ℤ_[p], E) ≃ₗᵢ[ℤ_[p]] C₀(ℕ, E)`, E any `[NormedAddCommGroup] [Module ℤ_[p]] [IsBoundedSMul] [IsUltrametricDist] [CompleteSpace]` (MahlerBasis.lean:356) | USE — this is the O_L-widening input; §3 dual-side arguments re-run verbatim |
| Continuous additive characters of ℤ_p / `(1+r)^x` | **`PadicInt.addChar_of_value_at_one`, `continuousAddCharEquiv`** for complete ultrametric normed ℤ_[p]-algebras (Padics/AddChar.lean:59,102) | USE — gives ξ-characters `x ↦ ξ^x` AND `⟨x⟩^s` (§5.3) for free |
| Topological power-series substitution `F((1+T)ξ−1)` | `PowerSeries.eval₂/aeval`, `HasEval = IsTopologicallyNilpotent` (PowerSeries/Evaluation.lean), needs `IsLinearTopology S S` + complete | USE for ξ-formulas if/where the paper route is taken (instance plumbing on `O_L⟦T⟧` w/ `WithPiTopology` to verify); measure-side ξ-free replans otherwise |
| ℂ_p, Q̄_p | `PadicComplex`, `PadicAlgCl` + `𝓞_ℂ_[p]` (Padics/Complex.lean) | available as ambient for root-of-unity systems |
| p-adic exp/log (Lem 5.14) | **MISSING** (no p-adic exp/log in mathlib) | REPLAN: `⟨x⟩^s` via `addChar_of_value_at_one` (binomial/character route, no exp); Lem 5.14's exp statement stays a prose node (or own API-gap cluster if user wants it literal) |
| Teichmüller ω | `Perfection.teichmuller` (RingTheory/Teichmuller.lean, perfection-based — extraction friction for ℤ_p) | DEFINE directly (`ω(x) = lim x^{p^n}`, Cauchy by Fermat+binomial; small API: value-roots-of-unity, ≡ x mod p, multiplicative, section of reduction) |
| Valuations | `ValuativeRel` (RingTheory/Valuation/ValuativeRel/Basic.lean:74) + Padics instances | blueprint-link only (§3.1 prelims) |
| measure-side Mahler/Amice | still **MISSING** in mathlib (no overlap with §3) | project stays novel |

### §5 design decisions (Generality)
1. **Coefficient widening (rule-6 break, planned cluster):** parametrise
   `PadicLFunctions/Measure/*` by a coefficient ring `R` with exactly the
   `mahlerEquiv`/`Padics.AddChar` typeclass set — `[NormedCommRing R]
   [Algebra ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R]` (+ `NormMulClass R`,
   `IsDomain R` per-lemma where needed); ℤ_p-specific proofs (T001-style
   norm-attainment) re-attacked at decomposition. §4 files stay instantiated at
   `R := ℤ_[p]` — no churn. The paper's "fixed finite L/ℚ_p, coefficients O_L"
   instantiates R := 𝓞_L; scalar-extension Λ_{ℤ_p}(X) → Λ_R(X) is the power-series
   coefficient-inclusion under Mahler.
2. **χ valued in the coefficients:** `χ : DirichletCharacter L (p^n)` with L the
   p-adic coefficient field (NOT ℂ) — B_{k,χ} ∈ L directly; complex statements
   quarantined in a bridge file via an L ↪ ℂ embedding (ZetaValuesComplex pattern).
3. **Twist μ_χ defined measure-side** (∫f·μ_χ = ∫χ̃f·μ, χ̃ the locally constant
   zero-extension through `toZModPow`) — no roots of unity in the definition; the
   ξ-expression for 𝓐_{μ_χ} (Lem 5.4 / EqRestrictionFormula) is then a theorem.
4. **ξ-machinery vs ξ-free**: paper route preferred (user directive); where the
   paper's computation passes through objects our Λ lacks (Laurent 1/T) or needs
   μ_{p^n} ⊂ L hypotheses a statement doesn't, the T034 projection-formula pattern
   (`psi_phi_mul` + Dirac telescopes, e.g. ψ(F_η) = η(p)F_η via the geometric
   factorisation ((1+T)^pε^{pc}−1) = ((1+T)ε^c−1)·Σ_{j<p}((1+T)ε^c)^j) is the
   recorded replan. Decided leaf-by-leaf in decomposition.md with quotes.
5. **§5.3**: ω by direct limit construction; `⟨x⟩^s` via `addChar_of_value_at_one`;
   ζ_{p,i}/L_p(θ,s) as functions on ℤ_p (analyticity deferred with §3.7 to §6–7);
   p odd structural throughout (μ_{p−1}×(1+pℤ_p) decomposition).

### flt-regular-bernoulli survey (user request, 2026-06-10)

Surveyed `~/Documents/GitHub/flt-regular-bernoulli` (the user's own Kummer-criterion
project, `BernoulliRegular/`, 0 sorries, axiom-clean) for portable Bernoulli results.

| Their asset | Content | Decision |
|---|---|---|
| `Characters.lean` (~340 LOC) | `teichmuller p : ZMod p →*₀ ℤ_[p]` via mathlib `Perfection.teichmuller₀` + `PadicInt.residueField`; API: `toZMod_teichmuller` (ω(a) ≡ a mod p), `teichmuller_pow_sub_one`, `isUnit_teichmuller`, `teichmuller_injective`, `teichmuller_pow_card` (Frobenius-fixed), mod-p² congruence, `teichmullerChar : DirichletCharacter ℤ_[p] p`, `orderOf_teichmullerChar = p−1`, `HasEnoughRootsOfUnity ℤ_[p] (p−1)`, `IsCyclic (DirichletCharacter ℤ_[p] p)`, parity lemmas (`teichmullerChar_odd`, `_pow_even_iff`) | **PORT for T517** (supersedes the survey-table row "DEFINE directly" and design decision 5's "ω by direct limit construction"). Source-faithful: mathlib's `Perfection.teichmullerFun` IS the limit-of-`p^n`-th-powers-of-lifts construction (`teichmullerAux`), i.e. RJW Def 5.15's `lim x^{p^n}` route, packaged through the perfection of the residue field. Both `Mathlib.RingTheory.Teichmuller` (`teichmuller₀`, `mk_teichmuller₀`) and `PadicInt.residueField` exist in our pin — verified. Port shape: `PadicInt.teichmullerZMod : ZMod p →*₀ ℤ_[p]`, then skeleton `teichmullerFun p x := teichmullerZMod p (toZMod x)`; all 6 skeleton sorries follow from the ported API. Their `module`/`public import` syntax stripped to plain imports; `BernoulliRegular` namespace → `PadicInt`. |
| `BernoulliGeneralized.lean` (622 LOC) | `BernoulliGen` (ZMod-sum, ℕ-sub convention — agrees with our `genBernoulli` for **nontrivial** χ; differs at trivial χ where ours matches Washington/`bernoulli'`); `natCast_mul_BernoulliGen_one_of_ne_one` (N·B₁,χ = Σ χ(a)·a.val); `teichmullerCharQp := (teichmullerChar p).ringHomComp PadicInt.Coe.ringHom` + order lemmas; `bernoulliGen_teichmuller_inverse_eq_p_sub_one_div_p_add_padicInt` (B₁,ω⁻¹ = (p−1)/p + p-integral); von Staudt–Clausen cluster (`bernoulli_mem_padicInt_of_lt_sub_one`, `prime_not_dvd_bernoulli_den_of_lt_sub_one`, `bernoulli_pSubOne_add_inv_p_mem_padicInt`) | **Reference for T520 + §6/§7** (not ported now). `teichmullerCharQp`'s `ringHomComp` pattern is T520's ω-as-Dirichlet-character sub-leaf verbatim. von Staudt–Clausen + B₁,ω⁻¹-pole computation become relevant at §6 (L_p(1,χ) / residue) and §7 (Kummer congruences). Convention bridge needed if porting B-lemmas: our range-sum vs their ZMod-sum (equal for nontrivial χ — T503's `hsum_eq` bijection is the bridge). |
| `LValueAtOne/` (~1900 LOC, ℂ-valued, mod p) | `odd_LFunction_zero_eq_neg_BernoulliGen_one` (L(0,χ) = −B₁,χ, odd χ mod p — the k=1 odd case of our T505); `odd/even_LFunction_one_eq_*Rhs` (L(1,χ) formulas: iπτ(χ)/p-sum for odd, τ(χ)/p·Σχ⁻¹(a)log-style for even) | **Proof-precedent for T505 and §6 planning** (not ported — ℂ-routes via sinZeta/Hurwitz functional equation; our T505 wants the direct Hurwitz-at-negative-integers route at general level N, all k). The even L(1,χ) shape is the archimedean counterpart of RJW Thm 6.2's L_p(1,χ) — consult their Even.lean decomposition when planning §6. |
| `GaussSumProduct/` (ℂ, mod p) | `(∏_{χ odd} τ(χ))² = (−p)^{|X⁻|}`, Legendre-sign, root-number pairing | Skip — h⁻-class-number-formula specific; our Gauss-sum needs (product formula at general level N) already proven in Characters.lean (T502). |
| `Reflection.lean` + stack | Kummer-pairing/Spiegelungssatz/Stickelberger/class-group machinery | Skip — Kummer's criterion infrastructure, outside RJW §5–§15 scope. |

---

# §6 pre-plan addendum (2026-06-11, /develop resume-mode scoping pass)

## Section map (read in full this session)
§6 "The values at s = 1" = TeX 1980–2180. One headline result:
**Theorem 6.1** (`s=1 theorem`, TeX 1987–1995), θ non-trivial of conductor N,
ε_N a primitive N-th root of unity:
- (i) classical: L(θ,1) = −(1/G(θ⁻¹))·Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·log(1−ε_N^c)
  — proof §6.1 (TeX 2007–2045), Washington Thm 4.9 route: Fourier/Gauss-sum
  expansion (eq:classical 6.1) + Taylor series of −log(1−z) + convergence
  at s = 1. Parity refinement remark (TeX 2046–2053) is prose.
- (ii) p-adic (Leopoldt): L_p(θ,1) = −(1−θ(p)p⁻¹)(1/G(θ⁻¹))·Σ θ⁻¹(c)·log_p(1−ε_N^c)
  — proof §6.2 (TeX 2055–2155) via F̃_θ (the log-antiderivative of F_θ),
  Lemma 6.2 (`lem:bounded power series`: F̃_θ ∈ ℛ⁺), thm:mahler la
  (locally analytic distributions), Lemma 6.3 (`lem:mu theta'`: x·μ̃_θ = μ_θ),
  then (1−φ∘ψ)-evaluation at 0 with two cases (n ≥ 1: χ kills pℤ_p;
  n = 0: Eqphipsi ξ-sum + c ↦ pc Frobenius trick).
Closing remarks (Coleman polylogarithms Thm s=k, Perrin-Riou): PROSE-ONLY,
out of scope (record as deferred, like the §5 Mellin nodes).

## The three deferred clusters that come due (and what we actually need)

1. **Extended p-adic logarithm (Iwasawa branch)** — REQUIRED for the
   statement of (ii): the arguments 1−ε_N^c have ‖(1−ε_N^c)−1‖ = 1, outside
   padicLog's ball. Not in mathlib (surveyed). Washington §5.1 construction.
   Needed API (over the §5 ambient K): `extLog : K → K` (junk-total) with
   (a) agreement with padicLog on the ball, (b) additivity on the relevant
   multiplicative domain, (c) log of roots of unity = 0 (torsion),
   (d) log_p(x) = log_p(−x), (e) the values at 1−ε^c needed by the proof.
   Design note: for the theorem we can avoid a fully general Kˣ-log by
   defining extLog via "x^m ∈ p^k·(ball) for some m, k" (rational-valuation
   elements) with a well-definedness lemma — the arguments 1−ε_N^c qualify
   (algebraic). Generality decision to be made at decompose time.

2. **Eqphipsi / formal ψ on power series** — the deferred ξ-machinery
   (plan.md "Deferred"). §6.2's case n = 0 uses
   (φ∘ψ)F = p⁻¹·Σ_{ξ∈μ_p} F((1+T)ξ−1) literally. Two sub-pieces:
   (a) a FORMAL ψ-operator on R⟦T⟧ (the digit decomposition
   F = Σ_{i<p} (1+T)^i·φ(F_i), ψF := F_0 — ξ-free, mirrors the project's
   measure-level digit-shift ψ), with ψ∘φ = id, ψ(constants) = constants,
   compatibility with the measure-level ψ through mahlerRingEquiv;
   (b) Eqphipsi itself as a lemma (needs μ_p ⊂ K hypothesis, the §5
   hε-pattern; ∏_{ξ∈μ_p}(Yξ−1) = Y^p−1).

3. **Locally analytic distributions (ℛ⁺, thm:mahler la)** — RJW's route
   makes x⁻¹·μ_θ rigorous as a distribution. **WE CAN AVOID THIS ENTIRELY**
   (recorded route-discovery, to be adversarially tested at decompose time):
   - Our L_p(θ,1) is ALREADY a genuine measure pairing: LpFunction at s = 1
     pairs ζ_η-cleared (= x⁻¹·Res μ̃_η by construction, the §5
     zetaEtaCleared) against χ̃·⟨x⟩⁰ = χ̃. No distribution needed for the
     statement.
   - For the VALUE: let ρ := the (cleared, χ-twisted) x⁻¹Res(μ_θ)-measure
     pushed to ℤ_p (iota). Then L_p(θ,1)·(clearing) = 𝓐_ρ(0) (mass).
     ∂𝓐_ρ = 𝓐_{x·ρ} = 𝓐_{Res μ_θ} = (1−φψ)F_θ = ∂((1−φψ)F̃_θ) — wait, at the
     FORMAL level: both 𝓐_ρ and G₀ := (1−φψ)F̃_θ are ∂-antiderivatives of
     (1−φψ)F_θ, hence differ by a constant C (ker ∂ = constants).
   - **C = 0 by the ψ-kernel argument**: ρ is supported on the units, so
     ψ(𝓐_ρ) = 0 (project: isSupportedOn_units_iff_psi_eq_zero + the
     formal-ψ bridge); ψ(G₀) = ψF̃ − ψφψF̃ = 0 (ψφ = id, formal); and
     ψ(C) = C for constants. Subtract: C = 0. Hence 𝓐_ρ(0) = G₀(0) and the
     two-case computation of (φψF̃)(0) (TeX 2115–2155) finishes exactly as
     in the source — all at the level of FORMAL power series in K⟦T⟧
     (F̃_θ has unbounded coefficients but lives in K⟦T⟧; no ℛ⁺ topology,
     no distribution Mahler correspondence, no thm:mahler la).
   - F̃_θ is then just an EXPLICIT power series (constant term
     Σθ⁻¹(c)·extLog(ε^c−1)-shaped, higher coefficients the log-expansion of
     TeX 2076–2080), with ∂F̃_θ = F_θ a finite per-c formal-derivative
     computation + Σ_c θ⁻¹(c) = 0.
   This replaces RJW's §3.7-dependent argument with a replan-note-eligible
   Lean-friendlier route; the SOURCE's statements (Lem 6.2/6.3) become:
   Lem 6.2 → the explicit coefficient formula for F̃_θ (its ℛ⁺-membership is
   not needed and is recorded as deferred prose); Lem 6.3 → the ∂F̃ = F_θ
   identity + the ψ-kernel constant-pin (the "x·μ̃ = μ" content at the level
   we use it). Faithfulness: statement of Thm 6.1(ii) UNCHANGED; the route
   is a recorded replan (rule 5 pattern, cf. T018/T026/L5.3.3).

## Mathlib survey status (1c, partial — full survey at decompose time)
- Complex Dirichlet L: mathlib has LSeries/Dirichlet + DirichletContinuation
  (functional equation `IsPrimitive.completedLFunction_one_sub`),
  HurwitzZetaValues, ZMod.LFunction. The exact log(1−ε^c)-formula at s = 1
  is NOT obviously present — expect to build it from `LSeries` of the
  twisted-coefficient function + Taylor/Abel summation; survey area B
  (special values) must be COMPLETED at decompose time (it never ran).
- Locally analytic distributions / Amice: absent (grep clean) — moot if the
  distribution-free route survives the adversarial pass.
- Extended/Iwasawa log: absent.
- μ_p-products (∏(Yξ−1) = Y^p−1 etc.): standard `X_pow_sub_one_eq_prod`
  machinery present (RootsOfUnity).

## Proposed cluster structure (sizing vs TeX line counts; ticket-grade
decomposition to be produced by the Phase-1e pass)
- W6a extLog cluster (~5–7 leaves; Washington §5.1 ~1 page) — independent.
- W6b formal-ψ/digit + Eqphipsi cluster (~4–6 leaves; the §3 deferral) —
  independent.
- C6 complex value (i) (~4–6 leaves; TeX 2007–2045 ≈ 39 lines + mathlib
  LSeries glue) — independent of W6a/W6b.
- P6 p-adic value (ii) (~6–9 leaves; TeX 2055–2155 ≈ 100 lines): F̃_θ def +
  ∂F̃ = F_θ + ψ-kernel pin + the two-case (φψF̃)(0) + assembly into
  LpFunction-at-1. Depends on W6a, W6b, §5 stack.
- Blueprint: new §6 chapter nodes (Thm 6.1 (i)/(ii), Lem 6.2/6.3 with the
  replan prose notes, Coleman/PR remarks as unwired prose).

## Open scope questions for the user (pre-decompose)
1. Approve the distribution-free route for (ii) (recorded replan; ℛ⁺/§3.7
   stays deferred until the notes force it — likely §8 Eisenstein family /
   later Coleman-map sections)?
2. extLog generality: pragmatic rational-valuation domain (enough for
   Thm 6.1) vs full Iwasawa log on Kˣ (more work, PR-shaped)?
3. Complex side (i): formalise against mathlib's LFunction (preferred,
   mathlib-linking directive) — accept that the bridge LSeries↔our LvalNeg
   conventions may add a leaf or two?

---

# §7 pre-plan addendum (2026-06-12, /develop pass)

## Section map (read in full this session)
§7 "The residue of ζ_p at s = 1" = TeX 2181–2360. One headline:
**Theorem 7.1** (`thm:residue`, TeX 2187–2194): (i) ζ_{p,i} analytic at
s = 1 for i ≠ p−1; (ii) ζ_{p,p−1} has a simple pole at s = 1 with residue
1 − p⁻¹. Proof: Eqtmp2 (TeX 2199–2215) writes ζ_{p,i}(s) as the
pseudo-measure quotient with denominator g_{a,i}(s) = ω(a)^i⟨a⟩^{1−s} − 1
— EXACTLY our `zetaPBranch` definition (T519), so Eqtmp2 is definitional
for us. Lemma 7.2 (`lem:g p-1`): g-vanishing analysis + the limit
(s−1)⁻¹g_{a,p−1}(s) → −log_p(a). Then eq:zeta-p-residue reduces (ii) to
the mass ∫x⁻¹μ_a = ((1−φψ)F̃_a)(0) with F̃_a := log(T/(1+T)·(1+T)^a/((1+T)^a−1))
(Lemmas 7.3–7.5, TeX 2266–2352): ∂F̃_a = F_a, ℛ⁺-membership (Lemma 7.4 —
SKIPPED by our distribution-free route, as Lem 6.2 was), and the
φψ-evaluation via the Eqphipsi ξ-sum with {ξ^a} = μ_p and
∏(Xξ−1) = X^p−1, giving ((1−φψ)F̃_a)(0) = −(1−p⁻¹)log_p(a).

## Key reuse (the §5/§6 investment pays)
- "analytic/pole/limit" statements: topological limits in ℤ_p-variable;
  (ii) as `Tendsto (fun s => (s−1)·zetaPBranch p hp2 (p−1) s) (𝓝[≠] 1)
  (𝓝 (1−p⁻¹))` — K-FREE final statement (the log_p(a)'s cancel).
- Lemma 7.2's limit: through the T523 exp/log bridge —
  ⟨a⟩^{1−s} − 1 = pZpExp((1−s)·pZpLog⟨a⟩) − 1, then the exp-derivative-at-0
  (‖exp w − 1 − w‖ ≤ p‖w‖², new small lemma) + ‖exp w − 1‖ = ‖w‖. Also
  yields the Lipschitz bound ‖y^t − 1‖ = ‖t‖·‖y − 1‖ (p odd) powering the
  continuity of s ↦ zetaPBranch (Thm (i)).
- The mass computation: the c₀-design VERBATIM (T615-pattern):
  ρ_a := baseChange of the §4 numerator measure (zetaNum p a is already
  x⁻¹·Res(μ_a) on units!), ψρ_a = 0, ∂𝓐ρ_a = (1−φψ)F_a-series, the
  antiderivative/ker-∂ pin, ξ-point evaluation via sum_seriesEval_mahlerK.
- F̃_a explicit: F̃_a = [−extLog(a) + log(1+T·h)-series] + (a−1)•formalLog
  with the §4 PropFaT-style h-series; a := the ℕ-generator
  (exists_nat_topological_generator) so all binomials are integral.
- ξ-field: the machinery needs μ_p ⊂ K; final statements are ℚ_p-level —
  compute in K and descend by injectivity. K := ℂ_[p] (mathlib
  `PadicComplex`: NormedField/IsUltrametricDist/CharZero instances exist;
  CompleteSpace from completion; NormedAlgebra ℚ_[p] — verify at
  execution; primitive p-th root from PadicAlgCl mapped in). SURVEY-GATED
  leaf; fallback: SplittingField + spectralNorm instances.

## New file: PadicLFunctions/ResidueZeta.lean (imports Branches +
ValuesAtOne); generic exp-facts may migrate to PadicExp.lean at a later
cleanup (placement note).

## Open risks
- ℂ_[p]-instance pack completeness (NormedAlgebra ℚ_[p] ℂ_[p] +
  CompleteSpace + the root) — survey-gated T707a.
- The §4 PadicMeasure-units ↔ MeasureR-K bridge for zetaNum (baseChange is
  on ℤ_p-measures; compose with the Measure-level iota).
- {ξ^a} = μ_p needs gcd(a,p) = 1 — the §4 generator a is coprime to p
  (topological generator of ℤ_p^× reduces to a generator mod p; extract
  from the T037 machinery).

## §7 COMPLETE (2026-06-12, /beastmode)
All of T701–T708 + 3 cleanups done in one session; project-wide ZERO
sorries, axioms standard, blueprint Residue chapter wired + site rendered.
Risk outcomes: ℂ_[p]-pack complete in mathlib (no fallback needed; ξ via
`HasEnoughRootsOfUnity.exists_primitiveRoot`); the zetaNum bridge ran
through ℤ_p-level cmul + `baseChange_cmul`/`baseChange_res` (no new
naturality lemma); the {ξ^a}-reindex was replaced by a product collapse
(Finset.prod_nbij' over ZMod p + Fermat + `extLog_eq_of_witness`), avoiding
ExtLogDomain(ξ^i−1) entirely. Statement fixes (b2-logged, T704): ∂F̃_a = F_a
needs ¬p∣a (Fa junk at p∣a); constantCoeff_FtildeA needs a ≠ 0. New
reusable infrastructure: the K-level seriesEval∘subst bridge
(`seriesEval_subst_formalLog`) — FormalPsi-placement candidate
(CLEANUP-FINAL). Next: §8 (Iwasawa's theorem / μ-invariant chapters per
the blueprint roadmap) or the deferred D = 1 case of Thm 6.1(ii).

# §8 pre-plan addendum (2026-06-12, /develop pass)

## Section map (read in full this session)
§8 "The p-adic family of Eisenstein series" = TeX 2361–2446, the Part-I
closer. One Definition (p-stabilisation E_k^{(p)} := E_k − p^{k−1}E_k(p·),
TeX 2387), one impossibility gloss (no measure interpolates k ↦ p^k,
TeX 2379–2383), one Theorem (TeX 2399–2416): the Λ-adic family
𝐄 = Σ A_n qⁿ ∈ Q(ℤ_p^×)⟦q⟧ with A₀ = xζ_p/2, A_n = Σ_{d∣n, p∤d} δ_d, and
∫x^{k−1}·𝐄 = E_k^{(p)} coefficientwise for even k ≥ 4. The notes' proof is
8 lines: §4's interpolation does all the work.

## Key facts and reuse
- Convolution ring Λ(ℤ_p^×) = `PadicMeasure p ℤ_[p]ˣ` (CommRing instance,
  PseudoMeasure.lean), `QuotientField`, `IsPseudoMeasure`, `padicZeta`,
  `padicZeta_moments` (witness-encoded), `dirac_sub_one_mem_nonZeroDivisors`,
  the zero-divisor lemma `eq_zero_of_forall_unitsPowCM_eq_zero`, and
  `units_mul_apply_unitsPowCM` ((μ*ν)(x^k) = μ(x^k)ν(x^k)) — everything
  the family needs is §3.6/§4 infrastructure.
- The x-twist τ = unitsCmul (unitsPowCM 1) is a ring automorphism by a
  pure moments check (decomposition R8.2) — no new analysis.
- **Erratum #11 (errata.md)**: TeX 2403's "(a) A₀ is a pseudo-measure" is
  false with Def 3.34 — the pole of xζ_p is at the character x⁻¹.
  Formalised in the corrected twisted form (g[g]−[1])·A₀ ∈ Λ (replan R8.1).
- Complex side: mathlib HAS the level-1 Eisenstein q-expansion
  (`EisensteinSeries.E`, `E_qExpansion_coeff`, `q_expansion_bernoulli` —
  Mathlib/NumberTheory/ModularForms/EisensteinSeries/QExpansion.lean) with
  the constant-1 normalisation; RJW's E_k = (ζ(1−k)/2)·E. Stabilised
  q-expansion proved as a HasSum statement (replan R8.3); the
  σ^p-arithmetic σ^p_{k−1}(n) = σ_{k−1}(n) − p^{k−1}σ_{k−1}(n/p) is a
  divisor-sum reindex against mathlib's `ArithmeticFunction.sigma`.
- Impossibility (TeX 2379) via uniform Euler congruence x^{φ(p^{n+1})} ≡ 1
  mod p^{n+1} (the §7 unitsToZModPow/ker_toZModPow patterns) +
  `norm_apply_le`.

## Files
- `PadicLFunctions/EisensteinFamily.lean` — p-adic side (imports ZetaP;
  light). Twist, A_n, A₀, family, milestone theorem, impossibility.
- `PadicLFunctions/EisensteinComplex.lean` — complex side (imports mathlib
  EisensteinSeries.QExpansion + our ZetaValuesComplex; heavy mathlib
  imports kept out of the p-adic file). σ^p arithmetic + stabilised HasSum.

## Deferred (§8)
- ~~**Γ₀(p)-modularity of E_k^{(p)}**~~ — **UN-DEFERRED 2026-06-12** (user
  directive): the strong-multiplicity-one project
  (CBirkbeck/LeanModularForms, branch hecke-ring) supplies the
  level-raising operator `modularFormLevelRaise` (Miyake §4.6 Lem 4.6.1);
  the repo now requires it (lakefile.toml pin 720d950b + two
  mathlib-skew compat fixes, to be upstreamed at CLEANUP-82). Ticket T808.
- Remarks 1–3 (TeX 2431–2446: Λ-adic forms colloquium, weight space 𝒲,
  Hida/Coleman families) — prose only, no mathematical content to
  formalise; blueprint prose covers them.

## Generality
ℤ_p-coefficients throughout (standing rule 6); the family lives over
`QuotientField p` exactly as the source's Q(ℤ_p^×)⟦q⟧. p = 2 excluded
where ζ_p enters (hp2 standing); the Dirac/divisor-measure layer and the
impossibility lemma are p-general.

## §8 COMPLETE (2026-06-12, /beastmode) — PART I COMPLETE
All of T801–T808 + 3 cleanups done in one session; project-wide ZERO
sorries, axioms standard, blueprint Eisenstein chapter wired + site
rendered. The Λ-adic family theorem (`eisensteinFamily_interpolation`) is
the milestone; the erratum-#11-corrected A₀-claims
(`twistedZetaHalf_isTwistedPseudoMeasure`/`_moments`) carry the notes'
"(a)"; the q-expansion (`hasSum_stabilisedEisenstein`) and the
Γ₀(p)-modularity (`stabilisedEisenstein`, via the un-deferral) carry the
complex side. New external dependency: CBirkbeck/LeanModularForms at
branch compat/padic-mathlib-431 (= hecke-ring 720d950 + 4 mechanical
mathlib-skew fixes, pushed upstream 84b03fb) supplying the level-raising
operator. With §§3–8 done, Part I of RJW is fully formalised. Next:
Part II (§§9–11: the Coleman map, Iwasawa's theorem, the Main
Conjecture — blueprint chapters exist) or the deferred D = 1 case of
Thm 6.1(ii), or CLEANUP-FINAL in a tooled session.

# §9–§10 pre-plan addendum (2026-06-12, /develop pass) — PART II OPENS

## Section map
§9 (TeX 2466–2511): Part-II notation — only the LOCAL tower
(K_n = ℚ_p(μ_{p^n}), 𝒰_n, π_n, norm-limits 𝒰_∞) is §10-load-bearing;
global/Galois objects ride the §11 pass. §10 (TeX 2512–2948): Coleman's
theorem (𝒰_∞ ≅ (ℤ_p⟦T⟧^×)^{𝒩=id}, u ↦ f_u with f_u(π_n) = u_n), the
cyclotomic units c(a) with f_{c(a)} = ((1+T)^a−1)/T and
∂log f_{c(a)} = a−1−F_a, the Coleman map Col, and
**ζ_p = Col(c(a))/θ_a** (thm:coleman to kl) — the arithmetic
reconstruction of the Kubota–Leopoldt pseudo-measure. §10.5
(Euler systems/Perrin-Riou): prose-only, deferred.

## Design (decomposition R10.1–R10.8)
The tower lives inside ℂ_[p] (PadicComplex — the §7/§8 investment):
fixed compatible ξ-system by recursion + IsAlgClosed; K n :=
ℚ_p⟮ξ n⟯ IntermediateField; O n := norm-unit-ball; degree ladder by
Eisenstein (Φ_{p^n}(T+1) Eisenstein at p over ℤ_[p]); evaluation
f(π_n) := our seriesEval (§6–§8 layer; mathlib's new
PowerSeries.eval₂ as fallback); 𝒩 := φ⁻¹∘(det in the PROVEN digit
basis (1+T)^i of ℤ_p⟦T⟧ over φ(ℤ_p⟦T⟧)) — no field-norm theory, no
illegal μ_p-substitution (the Eqphipsi subtlety); commuting square by
RingHom.map_det; compactness of ℤ_p⟦T⟧^× by Pi-topology + Tychonoff +
metrizability; uniqueness by mathlib's NEW Weierstrass preparation.

## Files
- `PadicLFunctions/Coleman/Tower.lean` — ξ-system, K/O/π/𝒰, degree
  ladder, element norms (X^p−ξ_n collapse), 𝒰_∞.
- `PadicLFunctions/Coleman/NormOperator.lean` — digit-basis algebra,
  𝒩, ψ-trace relation, continuity lemmas, compactness.
- `PadicLFunctions/Coleman/Theorem.lean` — eval-at-π_n, single-level
  lemma, Weierstrass uniqueness, commuting square, R, surjectivity,
  Coleman's theorem (both forms).
- `PadicLFunctions/Coleman/Map.lean` — cyclotomic units, ∂log-bridge
  to F_a, Col, thm:coleman to kl.

## Deferred (§9–§10)
- §10.5 Kummer/Euler systems/Perrin-Riou (TeX 2847–2948): prose-only
  in source ("may be skipped"); blueprint ColemanMap chapter prose
  covers it; no Lean.
- §9's global tower (F_n, 𝒱_n), +-subfields, 𝒢 ≅ ℤ_p^×: §11 pass.
- 𝒰_{n,1}-structure (ℤ_p-module): §11 pass (not §10-load-bearing).

## Standing deferred queue (status 2026-06-12)
- D = 1 case of Thm 6.1(ii): queued as board ticket T-D61 (a
  /develop --decompose planning ticket — the notes' own gap, errata #6;
  the §8 twist machinery is the expected key).
- CLEANUP-FINAL: still blocked on a lean-lsp-MCP-tooled session.
- LeanModularForms compat branch: tidied + repinned (bc83277) — CLOSED.
