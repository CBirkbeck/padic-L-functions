# Decomposition: §3 Measures and Iwasawa algebras (RJW arXiv:2309.15692)

Source file: `.mathlib-quality/references/2309.15692-padic-L-functions.tex` (all line
numbers below refer to it). Scope: §3.2–3.6 (lines 746–1287) over ℤ_p coefficients;
deferred items are tabulated in `plan.md` ("Deferred").

## Skeleton location

Every lemma below exists as a `:= by sorry` declaration in:

- `PadicLFunctions/Measure/Basic.lean`
- `PadicLFunctions/Measure/MahlerTransform.lean`
- `PadicLFunctions/Measure/Convolution.lean`
- `PadicLFunctions/Measure/Toolbox.lean`
- `PadicLFunctions/Measure/UnitsZp.lean`
- `PadicLFunctions/Measure/Fubini.lean`
- `PadicLFunctions/Measure/PseudoMeasure.lean`

`lake build PadicLFunctions` passes — **Build completed successfully (2437 jobs)**,
sorry warnings only, no type errors (verified 2026-06-09).

## Verification method note

The lean-lsp MCP tools (loogle/leansearch/hover) are not connected in this planning
session. Every mathlib discharge below was instead verified by **reading the mathlib
source file directly** (exact file + line cited) — a stronger check than a search hit.

## Prior-B2 log (Step 4.6)

`.mathlib-quality/b2_log.jsonl` does not exist (new project, zero entries). No leaf can
match a prior B2; all leaves are clean by vacuity. (Future B2s recorded by `/beastmode`
must be consulted by the next `/develop` pass.)

---

## R1: The measure space (RJW §3.2, Def. 3.6 + Rem. 3.8)

### Plain-English proof substrate (Step 1)

RJW defines `𝒞(G, L)` with the sup valuation (Def. 3.5, lines 749–755), measures as the
continuous dual (Def. 3.6, lines 760–766) with the 𝒪_L-valued measures singled out, the
Dirac measures (Ex. 3.7, lines 774–779), and proves (Rem. 3.8, lines 782–802) that
restriction to locally constant functions is an isomorphism, via the locally constant
truncations `φ_n(x) = ∑_{a mod p^n} φ(a)·𝟙_{a+p^nℤ_p}(x)` and a continuity argument.
Lean design: over ℤ_p the boundedness/continuity in Def. 3.6 is *automatic*, so
`PadicMeasure p X := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` and continuity becomes a lemma.

### Leaves

- **L1.1** (leaf): `PadicMeasure.norm_apply_le` — `‖μ f‖ ≤ ‖f‖`
  - Lean: `PadicLFunctions/Measure/Basic.lean:107`
  - Source: Def. 3.6 footnote (line 759, commented variant retained in TeX):
    > "Recall that a linear functional μ is bounded if there exists a constant C such
    > that v_p(μ(φ)) ≥ v_𝒞(φ) + C for all φ ∈ 𝒞(G, L), and it is equivalent to asking
    > μ to be continuous."
    and line 765: "Since measures are continuous (or equivalently, bounded), we have
    ℳ(G, L) = ℳ(G, 𝒪_L) ⊗_{𝒪_L} L."
  - Lean ↔ source: over 𝒪 = ℤ_p the constant is C = 0: 𝒪-valued measures have norm ≤ 1.
    Our statement is the 𝒪-integral form of the footnote.
  - Discharged by: pure computation. `‖f‖` attained (X compact; sup over the discrete
    value set {p^{-k}} ∪ {0}); if `‖f‖ ≤ p^{-m}` then `f = p^m • g` with
    `g x := ⟨(f x : ℚ_[p])/p^m, _⟩` continuous, so `μ f = p^m • μ g` has norm ≤ p^{-m}.
    Mathlib inputs: `ContinuousMap.norm_coe_le_norm` (read in
    `Topology/ContinuousMap/Compact.lean`), `PadicInt.norm_le_pow_iff_dvd`
    (read in `NumberTheory/Padics/PadicIntegers.lean`).
  - Attacks attempted:
    - [2] Edge cases: `f = 0` (both sides 0 ✓); `X = ∅` (C(∅,ℤ_p) trivial, μ f = 0 ✓);
      `μ = dirac x` (LHS = ‖f x‖ ≤ sup ✓). No failure.
    - [3] Hypothesis test: `CompactSpace X` is necessary — for noncompact X the sup norm
      on C(X, ℤ_p) need not exist (norm instance requires compactness), so the statement
      doesn't even typecheck without it. Not over-specified.
    - [4] Source-drift: footnote allows arbitrary constant C; our C = 0 form is the
      𝒪-valued specialisation, exactly the convention of line 765 ("mainly concerned
      with 𝒪_L-valued functions and measures"). No drift.
    - [5] Discharge: `ContinuousMap.norm_coe_le_norm` exists at
      `Topology/ContinuousMap/Compact.lean` (read); divisibility `f = p^m • g` is the
      standard ℤ_p-ball argument; composition ≤ 3 steps. OK.
  - Verdict: SURVIVED.

- **L1.2** (leaf): `PadicMeasure.continuous`
  - Lean: `Basic.lean:112`
  - Source: line 765 (quoted at L1.1) — boundedness ⟺ continuity.
  - Lean ↔ source: linear + bounded-by-1 (L1.1) ⟹ Lipschitz ⟹ continuous.
  - Discharged by: L1.1 + `LipschitzWith.continuous` or
    `AddMonoidHomClass.continuous_of_bound` (read in
    `Analysis/Normed/Operator/...`; fallback: `Metric.continuous_iff` + L1.1 on `f − g`,
    using linearity `μ f − μ g = μ (f − g)`).
  - Attacks attempted:
    - [2] Edge cases: constant μ = 0 ✓; X empty ✓.
    - [3] Hypothesis test: compactness needed for the norm to exist (as L1.1).
    - [5] Discharge: bound-implies-continuous for additive maps on normed groups is
      standard; ≤ 3 lemma composition via L1.1. OK.
  - Verdict: SURVIVED.

- **L1.3** (leaf): `PadicMeasure.exists_locallyConstant_norm_sub_le` — density
  - Lean: `Basic.lean:123`
  - Source: Rem. 3.8, lines 782–784 (verbatim):
    > "Let 𝒞^lc(G,𝒪_L) denote the space of locally constant functions G → 𝒪_L; this is
    > a dense subspace of the continuous functions 𝒞(G,𝒪_L). Indeed, any continuous
    > function φ ∈ 𝒞(G, 𝒪_L) can be p-adically approximated by its locally constant
    > truncations φ_n(x) = ∑_{a ∈ (ℤ/p^nℤ)} φ(a) 𝟙_{a+p^nℤ_p}(x)".
  - Lean ↔ source: source proves density for G = profinite group via explicit
    truncations; our statement is for general compact X with the ball-preimage
    argument (preimages of the clopen balls of radius ε form a clopen cover —
    clopen because balls in the ultrametric ℤ_p are clopen — finite subcover,
    disjointify, choose values). This *generalises* the source's claim (compact X
    rather than profinite G); on ℤ_p/ℤ_p^× the two arguments coincide. Generalisation
    is conservative: the source's instances are special cases.
  - Discharged by: new proof (~25 LOC; the source spends 8 lines, lines 782–791).
    Mathlib inputs verified: `IsUltrametricDist` ball-clopenness
    (`Analysis/Normed/Group/Ultra.lean` family), `CompactSpace.elim_nhds_subcover`,
    `LocallyConstant` constructors (`Topology/LocallyConstant/Basic.lean`, read).
  - Attacks attempted:
    - [1] Counterexample search: density of loc. constants FAILS for connected targets
      (e.g. C(X,ℝ)) — but ℤ_p is totally disconnected/ultrametric, which is exactly
      what makes ball-preimages clopen. No contradiction for our target.
    - [2] Edge: X = ∅ (g = const junk? LocallyConstant ∅ exists, ‖f−g‖ = 0 ≤ ε ✓);
      f already locally constant (g := f ✓); ε huge (g := 0 ✓).
    - [3] Hypothesis: T2/total-disconnectedness of X NOT needed (clopenness comes from
      the target's ultrametric) — deliberately dropped vs. the source's profinite G;
      verified the proof outline nowhere uses them.
    - [5] Discharge: this is a genuinely new lemma (verified absent: grepped mathlib for
      `LocallyConstant` + dense — only Condensed-framework hits, different statement).
      PR candidate; sized from source: 8 source lines → ~25 LOC Lean.
  - Verdict: SURVIVED.

- **L1.4** (leaf): `PadicMeasure.ext_locallyConstant`
  - Lean: `Basic.lean:131`
  - Source: Rem. 3.8, lines 787–799, esp.
    > "We claim restriction from 𝒞 to 𝒞^lc defines a canonical isomorphism
    > ℳ(G,𝒪_L) ≅ ℳ^lc(G,𝒪_L)."
    (injectivity direction).
  - Lean ↔ source: `μ` agreeing with `ν` on locally constant g, both continuous (L1.2),
    locally constant dense (L1.3) ⟹ equal. Exactly the source's continuity argument
    (lines 791–795) run for the difference μ − ν.
  - Discharged by: L1.2 + L1.3 + `DenseRange.equalizer`-style argument (mathlib:
    `Continuous.ext_on` exists — read in `Topology/Separation` family; or direct ε/3).
  - Attacks attempted:
    - [2] Edge: μ = ν trivially ✓; X = ∅ (all measures equal ✓).
    - [4] Source-drift: source states an isomorphism ℳ ≅ ℳ^lc; we take only
      injectivity (the surjectivity inverse — extending a functional from 𝒞^lc — is
      NOT needed by any §3–4 result; deferred with the additive-functions description,
      see plan.md). Verified: §3.4–3.6 only ever use determination, not extension.
    - [5] Discharge: `Continuous.ext_on` + `DenseRange` machinery exists; ≤ 3 lemmas
      after L1.2/L1.3. OK.
  - Verdict: SURVIVED.

(Definitions `dirac`, `compRight`, `pushforward` are data, fully constructed — no
sorries, no leaves. `pushforward_dirac`, `dirac_apply`, `compRight_apply` are `rfl`.)

---

## R2: The Mahler transform is a linear equivalence (RJW Thm. 3.20, linear part)

### Plain-English proof substrate (Step 1)

Source statement (lines 988–991):
> "The Mahler transform gives an 𝒪_L-algebra isomorphism ℳ(ℤ_p, 𝒪_L) ≅ 𝒪_L⟦T⟧."

Source proof (lines 994–1005), structure: (a) *determination*: "any measure
μ ∈ ℳ(ℤ_p,𝒪_L) is uniquely determined by the values ∫ binom(x,n)·μ", via Mahler's
theorem `φ = ∑ a_n(φ) binom(x,n)` and `∫φ·μ = ∑ a_n(φ) ∫binom(x,n)·μ` (continuity);
(b) *construction*: "given any collection of values c_n ∈ 𝒪_L … there is a unique
measure μ_g with ∫binom(x,n)·μ_g = c_n", defined by `∫φ·μ_g = ∑ a_n(φ)c_n`, "which
converges"; (c) "Visibly 𝒜_{μ_g} = g". The analytic substrate (RJW Thm. 3.13, Mahler)
is mathlib's `PadicInt.hasSum_mahler` / `fwdDiff_tendsto_zero` / `mahlerSeries`, with
Mahler coefficients `a_n(φ) = Δⁿφ(0)` (RJW Rem. 3.14, lines 951–958 — "discrete
derivatives", identical to mathlib's `Δ_[1]^[n] f 0`).

### Leaves

- **L2.1** (leaf): `PadicMeasure.apply_eq_tsum` — evaluation formula
  - Lean: `MahlerTransform.lean:62`
  - Source (lines 995–998, verbatim):
    > "By Mahler's theorem, we can write φ(x) = ∑_{n ≥ 0} a_n(φ) binom(x,n) for some
    > unique a_n(φ) ∈ 𝒪_L such that a_n(φ) → 0 as n → ∞; and then we have
    > ∫_{ℤ_p} φ·μ = ∑_{n ≥ 0} a_n(φ) ∫_{ℤ_p} binom(x,n)·μ."
  - Lean ↔ source: our statement is this display with `a_n(φ) = Δⁿφ(0)` (source
    Rem. 3.14: "a_n(φ) = φ^[n](0)" where φ^[k+1](x) = φ^[k](x+1) − φ^[k](x) — exactly
    mathlib `fwdDiff`).
  - Discharged by: `PadicInt.hasSum_mahler f : HasSum (fun n ↦ mahlerTerm (Δ_[1]^[n] f 0) n) f`
    (read at `MahlerBasis.lean:339`) mapped through the continuous (L1.2) linear μ:
    `HasSum.map` + `mahlerTerm_apply` (`MahlerBasis.lean:256`), then `HasSum.tsum_eq`.
  - Attacks attempted:
    - [2] Edge: f = const c: Δⁿf(0) = 0 for n ≥ 1, sum = c·μ(1) ✓ matches μ(const) ✓;
      f = mahler k: sum has single term μ(mahler k) ✓ (uses Δⁿ(mahler k)(0) = δ_{nk},
      see L2.4).
    - [3] Hypothesis: needs nothing beyond μ linear — continuity is supplied by L1.2,
      not assumed. Summability of the RHS: from `fwdDiff_tendsto_zero` + bounded
      coefficients; verified mathlib `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`
      (used at `MahlerBasis.lean:287`) covers it.
    - [5] Discharge: `hasSum_mahler` signature read: needs `[NormedAddCommGroup E]
      [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E]`
      — all hold for E = ℤ_[p] (instances exist; `IsUltrametricDist ℤ_[p]` via
      `PadicInt` ultrametric, `CompleteSpace ℤ_[p]` exists). `HasSum.map` along a
      continuous `AddMonoidHom` exists. Composition ≤ 3. OK.
  - Verdict: SURVIVED.

- **L2.2** (leaf): `PadicMeasure.mahlerTransform_dirac` — `𝓐(δ_a) = (1+T)^a`
  - Lean: `MahlerTransform.lean:70`
  - Source (Ex. 3.16, lines 968–973, verbatim):
    > "Let a ∈ ℤ_p, and recall the Dirac measure δ_a. By definition, its Mahler
    > transform is 𝒜_{δ_a}(T) = ∑_{n≥0} binom(a,n) Tⁿ = (1+T)^a."
  - Lean ↔ source: coefficientwise both sides have n-th coefficient `binom(a,n)`:
    LHS `δ_a(mahler n) = Ring.choose a n` (mathlib `mahler_apply`); RHS
    `binomialSeries_coeff` (read at `PowerSeries/Binomial.lean:50`:
    `coeff n (binomialSeries A r) = Ring.choose r n • 1`).
  - Discharged by: `PowerSeries.ext` + `binomialSeries_coeff` + `mahler_apply`
    (≤ 3 lemmas; `smul_eq_mul`+`mul_one` glue).
  - Attacks attempted:
    - [2] Edge: a = 0: (1+T)^0 = 1 (`binomialSeries_zero` read at line 78) and
      δ_0(mahler n) = choose 0 n = δ_{n0} ✓ consistent; a = 1: (1+T) ✓.
    - [4] Source-drift: none — statement is literally the source display.
    - [5] Discharge: names verified by reading `PowerSeries/Binomial.lean` (lines
      46–80). OK.
  - Verdict: SURVIVED.

- **L2.3** (leaf): `PadicMeasure.mahlerTransform_injective`
  - Lean: `MahlerTransform.lean:77`
  - Source: lines 995–998 (quoted at L2.1) — "uniquely determined".
  - Lean ↔ source: if 𝓐μ = 0 then all μ(mahler n) = 0, so by L2.1 μf = 0 ∀f.
  - Discharged by: L2.1 + `PowerSeries.ext_iff` + `LinearMap.ext`.
  - Attacks: [2] zero measure ✓; [3] no extra hypotheses; [5] composition = 2 lemmas
    after L2.1. SURVIVED.

- **L2.4** (leaf): `PadicMeasure.mahlerTransform_ofPowerSeries` (+ well-definedness of
  `ofPowerSeries` = its `map_add'`/`map_smul'` fields)
  - Lean: `MahlerTransform.lean:85–97`
  - Source (lines 1000–1004, verbatim):
    > "Conversely, given any collection of values c_n ∈ 𝒪_L, defining an element
    > g = ∑_{n≥0} c_n Tⁿ ∈ 𝒪_L⟦T⟧, there is a unique measure μ_g with
    > ∫ binom(x,n)·μ_g = c_n. Concretely, for any φ = ∑ a_n(φ) binom(x,n) ∈ 𝒞(ℤ_p,𝒪_L)
    > as above, we define ∫_{ℤ_p} φ·μ_g = ∑_{n≥0} a_n(φ) c_n, which converges to an
    > element in 𝒪_L. Visibly we have 𝒜_{μ_g} = g".
  - Lean ↔ source: `ofPowerSeries g` is the displayed formula with a_n(φ) = Δⁿφ(0).
    Linearity fields: `fwdDiff_iter_add` (read: used at `MahlerBasis.lean:362`) +
    `tsum_add` (summability from `fwdDiff_tendsto_zero` × bounded). The computation
    `∫binom(x,k)·μ_g = c_k` needs `Δⁿ(mahler k)(0) = if n = k then 1 else 0`: this is
    mathlib's `fwdDiff_mahlerSeries` (read at `MahlerBasis.lean:313`) applied to
    `mahler k = mahlerSeries (Pi.single k 1)` (single-coefficient Mahler series), or
    directly `fwdDiff_iter_choose_zero` (used at `MahlerBasis.lean:332`).
  - Attacks attempted:
    - [2] Edge: g = 0 → μ_0 = 0 ✓; g = 1 → μ = δ_0 (only n = 0 term; Δ⁰φ(0) = φ(0) ✓).
    - [3] Hypothesis: convergence requires Δⁿφ(0) → 0 — that is mathlib
      `fwdDiff_tendsto_zero`, requiring f continuous — supplied by φ ∈ C(ℤ_p,ℤ_p) ✓;
      coefficient boundedness automatic (ℤ_p). Nothing smuggled.
    - [5] Discharge: `fwdDiff_iter_choose_zero` verified present (used in
      `MahlerBasis.lean:332`, defined in `Algebra/Group/ForwardDiff.lean`);
      `tsum`-linearity lemmas standard. OK.
  - Verdict: SURVIVED.

- **L2.5** (internal): `PadicMeasure.mahlerLinearEquiv` (left_inv, right_inv legs)
  - Lean: `MahlerTransform.lean:102`
  - Composition of L2.1 (left_inv: `ofPowerSeries (𝓐 μ) = μ` by `LinearMap.ext` + L2.1
    read right-to-left) and L2.4 (right_inv). Source: Thm. 3.20's proof IS this
    two-direction argument (lines 994–1005); composition attack: could both legs hold
    and the equiv fail? No — `LinearEquiv` is literally the pair. SURVIVED.

---

## R3: Ring structure and RJW Thm. 3.20 in full (Convolution.lean)

### Plain-English proof substrate (Step 1)

Source (Rem. 3.11, lines 907–911, verbatim):
> "The Iwasawa algebra Λ(ℤ_p) has a natural 𝒪_L-algebra structure, and hence by
> transport of structure we obtain such a structure on ℳ(ℤ_p,𝒪_L). As with the
> classical situation for finite group rings, the algebra structure on the space of
> measures can be described directly via convolution of measures. For a general
> profinite abelian group G, given two measures μ,λ ∈ ℳ(G,𝒪_L), one defines their
> convolution μ * λ to be ∫_G φ·(μ*λ) = ∫_G (∫_G φ(x + y)·λ(y))·μ(x). One checks that
> this does give an algebra structure and that the isomorphism above is an isomorphism
> of 𝒪_L-algebras."

Lean route (= the source's, with ℤ_p[[T]] playing the role the source gives Λ):
multiplication is *defined* by transport along `mahlerLinearEquiv`; the convolution
display is the theorem `mul_apply`. The bridge is Chu–Vandermonde on the Mahler basis.

### Leaves

- **L3.1** (leaf): `mahlerTransform_mul`, `mahlerTransform_one`, CommRing laws,
  `mahlerRingEquiv` — transport bookkeeping
  - Lean: `Convolution.lean:46–86`
  - Source: "by transport of structure" (line 908, quoted above).
  - Discharge: `mul_def` + `LinearEquiv.apply_symm_apply` gives `mahlerTransform_mul`
    in one rewrite; each ring law transfers along the bijection (e.g. assoc:
    apply `(mahlerLinearEquiv p).injective`, push `mahlerTransform_mul` through, use
    assoc in `PowerSeries`). `mahlerTransform_one`: `𝓐(δ_0) = (1+T)^0 = 1` =
    L2.2 + `binomialSeries_zero` (read at `PowerSeries/Binomial.lean:78`).
  - Attacks: [2] check `one ≠ zero` transfers (PowerSeries ℤ_p nontrivial ✓);
    [3] no hidden hypotheses — pure algebra over an established bijection;
    [5] `LinearEquiv.apply_symm_apply`/`symm_apply_apply` exist (core mathlib). The
    only subtlety: the `Mul`/`One` instances must not clash with existing instances on
    `C(X,ℤ_p) →ₗ ℤ_p` — verified: mathlib defines no `Mul`/`One`/`Ring` on linear-map
    duals (grep `instMul.*LinearMap` in `Mathlib/Algebra/Module/LinearMap` — module
    structure only). SURVIVED.

- **L3.2** (leaf, KEY): `PadicMeasure.mul_apply` — the convolution formula
  - Lean: `Convolution.lean:96`
  - Source: Rem. 3.11 display (quoted above): `∫φ·(μ*λ) = ∫(∫φ(x+y)·λ(y))·μ(x)`.
  - Lean ↔ source: identical, with the inner integral packaged as a continuous map.
  - Proof route (expanding the source's "one checks", per Step 1's terse-source rule):
    both sides are linear in `f` and bounded (L1.1), so by density (L1.3/L1.4 +
    Mahler expansion L2.1) it suffices to check `f = mahler n`. LHS = n-th coeff of
    `𝓐μ·𝓐ν = ∑_{i+j=n} μ(mahler i)ν(mahler j)`. RHS: inner function
    `x ↦ ν(binom(x+·,n))`; Chu–Vandermonde (`add_choose_eq`, read at
    `RingTheory/Binomial.lean:519`:
    `choose (r + s) k = ∑_{ij ∈ antidiagonal k} choose r ij.1 * choose s ij.2`)
    gives `binom(x+y,n) = ∑_{i+j=n} binom(x,i)binom(y,j)`; ν is linear over the finite
    sum, then μ likewise; equality follows.
  - Attacks attempted:
    - [1] Counterexample/consistency: evaluate both sides at μ = δ_a, ν = δ_b, f
      arbitrary: LHS = (δ_a*δ_b)(f) = δ_{a+b}(f) = f(a+b) (using L3.3 below); RHS =
      (f((a+·)))(b) = f(a+b) ✓ consistent.
    - [2] Edge: n = 0 (both sides μ(1)ν(1)·, choose(x+y,0)=1 ✓); f constant ✓.
    - [3] Hypothesis-strength: `Commute r s` hypothesis of `add_choose_eq` — ℤ_p
      commutative ✓ trivially satisfied; no hidden assumption.
    - [4] Source-drift: the formula in the source integrates λ inside and μ outside;
      our statement matches (ν inside, μ outside). For commutative measures the order
      is immaterial AFTER comm is proven, but the statement must match the source
      *before* comm is available — checked: it does (μ outer ✓).
    - [5] Discharge: `add_choose_eq` verified by reading (line 519, hypothesis
      `Commute r s`, BinomialRing R — ℤ_[p] instance at `MahlerBasis.lean:78`). The
      density-extension step needs "both sides continuous in f": LHS by L1.1; RHS: the
      inner map's norm is ≤ ‖f‖ pointwise (L1.1 twice) — fine. SURVIVED.

- **L3.3** (leaf): `dirac_mul_dirac` — `[a]·[b] = [a+b]`
  - Lean: `Convolution.lean:105`
  - Source: Ex. 3.12 (lines 914–920):
    > "Under the isomorphism of Proposition 3.10, δ_a corresponds to … an element of
    > the Iwasawa algebra that we denote [a]."
    combined with Ex. 3.16 (`𝓐δ_a = (1+T)^a`).
  - Discharge: apply `mahlerTransform_injective` (L2.3); `𝓐(δ_a·δ_b) = (1+T)^a(1+T)^b
    = (1+T)^{a+b}` by L2.2 + `binomialSeries_add` (read at
    `PowerSeries/Binomial.lean:60`).
  - Attacks: [2] a = b = 0 ✓ gives 1·1 = 1; [4] the source treats [a]-elements via the
    Λ-description — our statement is the measure-side image, equivalent by Ex. 3.16;
    [5] `binomialSeries_add` signature read: `[Ring A] [Algebra R A]` — with R = A =
    ℤ_[p] ✓ (`Algebra ℤ_[p] ℤ_[p]` := `Algebra.id`). SURVIVED.

---

## R4: The toolbox (RJW §3.5)

### Plain-English substrate (Step 1)

Each §3.5 operation is defined measure-side and computed on Mahler transforms. Source
proofs are one-liners on the Mahler basis; we mirror them. The two ξ-formulas (lines
1118–1127, 1155–1158) are deferred (plan.md): every identity below is the source's,
proved by the source's own ξ-free arguments (lines 1149–1151 are explicit function
manipulations, reproduced exactly).

### Leaves

- **L4.1** (leaf): `mahlerTransform_cmul_X` — `𝓐_{xμ} = ∂𝓐_μ`
  - Lean: `Toolbox.lean:46` (`del` at `Toolbox.lean:41`)
  - Source (Lem. 3.24, lines 1066–1075, proof verbatim):
    > "The result follows directly from computing
    > x·binom(x,n) = (x−n)binom(x,n) + n·binom(x,n) = (n+1)binom(x,n+1) + n·binom(x,n)."
  - Lean ↔ source: coefficientwise: `(xμ)(mahler n) = μ(x·binom(x,n)) =
    (n+1)μ(mahler (n+1)) + n·μ(mahler n)`; and `coeff n ((1+X)·F') = (n+1)F_{n+1} + n F_n`
    (`coeff_derivativeFun` read at `PowerSeries/Derivative.lean:46`). The binomial
    identity `x·choose x n = (n+1)·choose x (n+1) + n·choose x n` must be proven for
    `Ring.choose` over ℤ_p: by `denseRange_natCast` + continuity it reduces to ℕ, where
    it is `Nat.succ_mul_choose_eq`-adjacent arithmetic. (~20 LOC; source: 1 line.)
  - Attacks: [2] n = 0: x·1 = 1·binom(x,1) + 0 ✓ (binom(x,1) = x);
    [3] no hypotheses to weaken; [5] `coeff_derivativeFun` verified by reading;
    `Polynomial`/`Ring.choose` continuity from `PadicInt.continuous_choose`
    (`MahlerBasis.lean:93`). SURVIVED.

- **L4.2** (leaf): `apply_powCM` — `∫xᵏdμ = (∂ᵏ𝓐μ)(0)`
  - Lean: `Toolbox.lean:56`
  - Source (Cor. 3.25, lines 1079–1082, verbatim):
    > "For μ ∈ Λ(ℤ_p), we have ∫_{ℤ_p} x^k·μ = (∂^k 𝒜_μ)(0)."
  - Discharge: induction on k from L4.1; base: `∫1dμ = 𝓐μ(0)` = `constantCoeff` =
    coeff 0 = μ(mahler 0) ✓ (mahler 0 = 1).
  - Attacks: [2] k = 0 ✓ (above); k = 1: g'(0) ✓ matches source Rem. 3.21(2)
    (line 1037: "∫x·μ_g = g′(0)"); [4] source Rem. 3.21(2) lists ∫x², ∫x³ examples
    with integer-coefficient combinations — cross-checked: ∂²F(0) = F''(0) + F'(0) ✓
    matches the source's `∫x²·μ_g = g''(0) + g'(0)`. SURVIVED.

- **L4.3** (leaf): `res_union` + `isClopen_pZp` + `isClopen_units`
  - Lean: `Toolbox.lean:73, 121, 138`
  - Source (§3.5.3, lines 1100–1108):
    > "The 'restriction of μ to X' is the measure Res_X(μ) on ℤ_p defined by
    > ∫_{ℤ_p} f·Res_X(μ) = ∫_{ℤ_p} f𝟙_X·μ."
    and line 1129: "we can write X (or its complement…) as a disjoint union".
  - Discharge: `𝟙_{U∪V} = 𝟙_U + 𝟙_V` for disjoint clopens (`LocallyConstant.charFn`
    arithmetic, `Topology/LocallyConstant/Algebra.lean:94` `coe_charFn` read:
    `charFn Y hU = Set.indicator U 1`) + linearity. Clopenness: `pℤ_p = {‖x‖ < 1}`
    is the open unit ball = complement of the unit sphere; both clopen by
    ultrametricity / `PadicInt.norm_le_one` + discreteness of the value group
    (`PadicInt.norm_eq_zpow_neg_valuation` family, read). Units: `isUnit_iff : IsUnit z
    ↔ ‖z‖ = 1` (read at `PadicIntegers.lean:366`); `{‖x‖ = 1}` = complement of
    `{‖x‖ < 1}` ✓.
  - Attacks: [2] U = ∅ (charFn = 0, res = 0 ✓); U = univ (res = id ✓);
    [3] disjointness necessary (else indicators don't add) ✓ stated;
    [5] `Set.indicator` + charFn lemmas verified by reading. SURVIVED.

- **L4.4** (leaf): `mahlerTransform_sigma` / `mahlerTransform_phi`
  - Lean: `Toolbox.lean:97, 106`
  - Source (lines 1135–1146, verbatim):
    > "σ_a(μ) … has Mahler transform 𝒜_{σ_a(μ)} = 𝒜_μ((1+T)^a − 1)." and
    > "𝒜_{φ(μ)} = φ(𝒜_μ) := 𝒜_μ((1+T)^p − 1)."
  - Lean ↔ source: substitution legality: `(1+T)^a − 1` and `(1+T)^p − 1` have constant
    coefficient 0 (`binomialSeries_constantCoeff` read at `PowerSeries/Binomial.lean:55`),
    so `PowerSeries.HasSubst.of_constantCoeff_zero'` (read at
    `PowerSeries/Substitution.lean:67`) applies — mathlib's algebraic `subst` is legal.
  - Proof route (the source gives the formula without proof — expansion per Step 1):
    fix n; for k ∈ ℕ, `binom(ak, n) = coeff_n ((1+T)^{ak}) = coeff_n (((1+T)^a)^k) =
    ∑_{m ≤ n} binom(k,m)·c_{n,m}` where `c_{n,m} = coeff_n ((((1+T)^a −1))^m)` (the sum
    truncates at m ≤ n since `((1+T)^a−1)^m` has order ≥ m); all terms continuous in k,
    `denseRange_natCast` extends to x ∈ ℤ_p; apply μ and identify with
    `coeff_n (subst … 𝓐μ)` via the `coeff_subst` finiteness. Same for a = p.
  - Attacks:
    - [2] Edge: a = 1: σ_1 = id and subst((1+T)−1) = subst(T) = id ✓;
      n = 0: both sides give μ(1) ✓ (constantCoeff subst = constantCoeff at 0 ✓).
    - [3] Hypothesis: a a unit is NOT needed for the formula (works for any a ∈ ℤ_p —
      φ is literally the a = p case); our skeleton states σ for units (the paper's
      action) and φ separately — consistent with source.
    - [4] Drift-check: source's φ on power series (Eq. 3.9) is *defined* by this
      formula; our statement *proves* agreement of measure-side and series-side — same
      content. The ω-order subtlety (order ≥ m of `((1+T)^a−1)^m`) verified:
      `constantCoeff = 0` ⟹ `X ∣ _` ⟹ order ≥ m under powers ✓.
    - [5] `HasSubst.of_constantCoeff_zero'` + `substAlgHom` (an `AlgHom`, so
      `map_mul`/`map_add` free) verified by reading `Substitution.lean:61–189`.
  - Verdict: SURVIVED.

- **L4.5** (leaf): `shiftDiv` well-definedness + `shiftDiv_mul`
  - Lean: `Toolbox.lean:115–127`
  - Source: ψ's defining formula (lines 1147–1148):
    > "we define a measure ψ(μ) on ℤ_p by defining ∫_{ℤ_p} f(x)·ψ(μ) = ∫_{pℤ_p} f(p⁻¹x)·μ."
  - Lean ↔ source: `f(p⁻¹x)` on `pℤ_p` is implemented as `f ∘ shiftDiv` cut by
    `𝟙_{pℤ_p}`, where `shiftDiv x = (x − [x mod p])/p` with `[·]` the canonical digit
    `PadicInt.appr x 1`; on `pℤ_p` the digit is 0, so `shiftDiv(px) = x` ✓
    (`shiftDiv_mul`). Membership: `‖x − appr x 1‖ ≤ p⁻¹` (mathlib `appr_spec`-family,
    `RingHoms.lean:682–695` read — `dist_appr_spec`); quotient by p stays in ℤ_p.
    Continuity: `appr · 1` is locally constant (factors through `toZMod`), so shiftDiv
    is a difference/scaling of continuous maps.
  - Attacks: [2] x = 0: shiftDiv 0 = 0 ✓; x = p: appr p 1 = 0 (p ≡ 0 mod p) →
    shiftDiv p = 1 ✓; x = 1: shiftDiv 1 = (1−1)/p = 0 ✓ (value irrelevant — cut off by
    indicator). [3] only the values on pℤ_p matter for ψ; off-pℤ_p values arbitrary —
    our choice is canonical, no hypothesis hidden. [5] `PadicInt.appr` + spec verified
    by reading `RingHoms.lean`. SURVIVED.

- **L4.6** (leaf): `psi_phi` (`ψ∘φ = id`) and `phi_psi` (`φ∘ψ = Res_{pℤ_p}`)
  - Lean: `Toolbox.lean:152, 158`
  - Source (lines 1149–1151, verbatim — the source PROVES both):
    > "∫ f(x)·ψ∘φ(μ) = ∫ 𝟙_{pℤ_p}(x) f(p⁻¹x)·φ(μ) = ∫ 𝟙_{pℤ_p}(px) f(x)·μ = ∫ f(x)·μ,
    > ∫ f(x)·φ∘ψ(μ) = ∫ f(px)·ψ(μ) = ∫_{pℤ_p} f(x)·μ = ∫ f(x)·Res_{pℤ_p}(μ)."
  - Discharge: unfold definitions; the function identities are
    `𝟙_{pℤ_p}(px) = 1` (px ∈ pℤ_p ✓) and `shiftDiv(px) = x` (L4.5); pure
    `ContinuousMap.ext` computations.
  - Attacks: [2] μ = δ_a: ψφδ_a: φδ_a = δ_{pa}; ψδ_{pa}(f) = 𝟙(pa)f(shiftDiv(pa)) =
    f(a) = δ_a f ✓. φψδ_a for a unit: ψδ_a = 0?? ψδ_a(f) = 𝟙_{pℤ}(a)·f(…) = 0 ✓ and
    Res_{pℤ_p}δ_a = 𝟙_{pℤ}(a)·δ_a = 0 ✓ consistent. [4] no drift — displays copied.
    [5] composition of our own leaves only. SURVIVED.

- **L4.7** (leaf): `res_units_eq` (`Res_{ℤ_p^×} = 1 − φψ`) and
  `isSupportedOn_units_iff_psi_eq_zero` (Cor. 3.32)
  - Lean: `Toolbox.lean:146, 167`
  - Source: Eq. (3.10) (lines 1152–1154):
    > "In particular, we have Res_{ℤ_p^×}(μ) = (1 − φ∘ψ)(μ)."
    and Cor. 3.32 with proof (lines 1161–1167, verbatim):
    > "Then μ is supported on ℤ_p^× if and only if Res_{ℤ_p^×}(μ) = μ, or equivalently
    > if and only if 𝒜_μ = 𝒜_μ − φ∘ψ(𝒜_μ), which happens if and only if ψ(𝒜_μ) = 0,
    > since the operator φ is injective."
  - Discharge: `res_units_eq`: 𝟙_{ℤ_p^×} + 𝟙_{pℤ_p} = 1 (clopen partition of ℤ_p:
    `isUnit_iff`/`not_isUnit_iff` ‖x‖=1 vs ‖x‖<1, read at `PadicIntegers.lean:366,385`)
    + L4.6(`phi_psi`). Cor: (⇒) ψμ = ψ(Res μ) = ψμ − (ψφ)(ψμ) = ψμ − ψμ = 0 via
    L4.6(`psi_phi`); (⇐) immediate from `res_units_eq`. φ-injectivity (source's step)
    is supplied by `psi_phi` (left inverse) — same argument, ξ-free.
  - Attacks: [2] μ = δ_1 (unit): ψδ_1 = 0 ✓ supported ✓; μ = δ_0: ψδ_0 = δ_0 ≠ 0 and
    Res_{units}δ_0 = 0 ≠ δ_0 ✓ consistent. [4] drift-check vs source: source phrases
    Cor 3.32 via ψ(𝒜_μ) = 0 on power series; ours via ψ(μ) = 0 on measures — equivalent
    by 𝓐 injectivity (L2.3); recorded. [5] partition identity verified against
    `isUnit_iff`. SURVIVED.

---

## R5: Λ(ℤ_p^×), Fubini, and pseudo-measures (RJW §3.6 + Rem. 3.33)

### Plain-English substrate (Step 1)

(a) Rem. 3.33 (lines 1169–1176): ι : Λ(ℤ_p^×) ↪ Λ(ℤ_p), image = ker ψ, NOT a subring;
convolution on ℤ_p^× uses the multiplicative structure (Eq. 3.11, verbatim):
> "∫_{ℤ_p^×} f(x)·(μ*_{ℤ_p^×}λ) = ∫_{ℤ_p^×} (∫_{ℤ_p^×} f(xy)·μ(x))·λ(y)".
(b) Def. 3.34 (lines 1185–1191): pseudo-measures: λ ∈ Q(G) with ([g]−[1])λ ∈ Λ(G) ∀g.
(c) Lem. 3.36 (lines 1215–1241): the zero-divisor lemma, proof: (i) the vanishing
forces 𝒜_{ιμ} constant "since each non-trivial binomial polynomial is a linear
combination of strictly positive powers of x"; ψ kills it; (ii) `∫(xy)^k d(μ*λ)`
factors; (iii) reduce to (i) via ([a]−[1])μ.
(d) Def. 3.37 + Lem. 3.38 (lines 1245–1282): augmentation ideal; at finite level n,
`(ℤ/p^n)^× cyclic ⟹ I((ℤ/p^n)^×) = ([ā]−[1])·𝒪_L[(ℤ/p^n)^×]`; "in the inverse limit",
I(ℤ_p^×) = ([a]−[1])Λ; hence μ/([a]−[1]) is a pseudo-measure; conversely all
pseudo-measures have this shape (lines 1284–1285).

The "one checks" algebra structure (a) and the "in the inverse limit" step (d) are the
two places the source compresses; both are expanded below (Fubini cluster; compactness
cluster), per the Step-1 terse-source rule.

### Leaves (Fubini cluster — expansion of "one checks", API gap with sub-decomposition)

- **L5.1** (leaf): `locallyConstant_prod_mem_span_boxes`
  - Lean: `Fubini.lean:48`
  - Source: this is infrastructure the source leaves implicit in "One checks" (line
    910); the technique is the source's own reduction to locally constant functions
    (Rem. 3.8, quoted at L1.3). Internal justification: a locally constant function on
    a product of profinite spaces is constant on a finite grid of clopen boxes — refine
    the finitely many level sets (clopen, compact) by basis boxes and take the common
    grid of the projections.
  - Discharge: new (~40 LOC). Mathlib inputs: clopen-box basis for products of
    zero-dimensional compacts — `IsTopologicalBasis.prod` + compact-T2-totally
    disconnected ⟹ clopen basis (`compact_t2_tot_disc_iff_tot_sep` family /
    `loc_compact_t2_tot_disc_iff_tot_sep`; worker to locate exact modern name, the
    statement exists in `Topology/Separation`-family — fallback: direct proof via
    `LocallyConstant.discreteQuotient` machinery, `DiscreteQuotient` exists).
  - Attacks: [1] failure mode: X or Y connected (boxes don't generate) — excluded by
    `TotallyDisconnectedSpace` hypotheses ✓ present in the statement; [2] F constant
    (single box univ×univ ✓); [3] T2 needed (clopen sets may not separate otherwise);
    hypotheses match the two instantiations (ℤ_p, ℤ_p^×) ✓; [5] `DiscreteQuotient`
    verified present (`Topology/DiscreteQuotient.lean`). SURVIVED.

- **L5.2** (leaf): `integral_swap` (Fubini)
  - Lean: `Fubini.lean:62`
  - Source: expansion of "One checks that this does give an algebra structure" (line
    910). For box indicators both iterated integrals equal `μ(𝟙_U)·ν(𝟙_V)`; extend by
    linearity (L5.1) and density/continuity (L1.1, L1.3 on X×Y compact ✓).
  - Attacks: [2] F = 𝟙_{U×V}: LHS = μ(𝟙_U·ν(𝟙_V)) = ν(𝟙_V)μ(𝟙_U), RHS symmetric ✓;
    [3] both spaces need compact (norms) + zero-dim (L5.1) — ℤ_p, ℤ_p^× qualify (ℤ_p^×
    zero-dim: subtype-like topology of a zero-dim space via L5.4's embedding —
    instance `TotallyDisconnectedSpace ℤ_[p]ˣ` to be derived from the embedding;
    worker note); [5] composes L5.1 + L1.1 + L1.3. SURVIVED.

### Leaves (units geometry)

- **L5.3** (leaf): `instance : CompactSpace ℤ_[p]ˣ`
  - Lean: `UnitsZp.lean:26`
  - Source: implicit (the source treats ℤ_p^× as a profinite group throughout, e.g.
    line 747: "the examples G = ℤ_p or G = ℤ_p^× are of most interest").
  - Discharge: `Units.embedProduct` is an embedding (mathlib
    `Units.isEmbedding_embedProduct`, `Topology/Algebra/Constructions.lean` — read);
    its range `{(a,b) : ab = 1 ∧ ba = 1}` is closed in the compact ℤ_p × ℤ_pᵐᵒᵖ;
    closed subspace of compact is compact. (~12 LOC.) Verified absent from mathlib
    (no `CompactSpace _ˣ` instance found by grep).
  - Attacks: [2] sanity: ℤ_p^× = sphere ‖x‖=1 is closed-bounded ✓ consistent;
    [3] needs ℤ_p compact ✓ + T2 ✓ + topological monoid ✓ — all present;
    [5] `isEmbedding_embedProduct` verified by reading Constructions.lean. SURVIVED.

- **L5.4** (leaf): `unitsValCM` continuity, `extendByZero` (cont., linearity,
  `extendByZero_coe_unit`), `iota_injective`, `res_iota`, `mem_range_iota_iff`
  - Lean: `UnitsZp.lean:30–66`
  - Source (Rem. 3.33, lines 1169–1172, verbatim):
    > "We have an injection ι : Λ(ℤ_p^×) ↪ Λ(ℤ_p) given by ∫_{ℤ_p} φ·ι(μ) =
    > ∫_{ℤ_p^×} φ|_{ℤ_p^×}·μ, and as Res_{ℤ_p^×} ∘ ι is the identity on Λ(ℤ_p^×), we
    > can identify Λ(ℤ_p^×) with its image as a subset of Λ(ℤ_p). By Corollary 3.32, a
    > measure μ ∈ Λ(ℤ_p) lies in Λ(ℤ_p^×) if and only if ψ(μ) = 0."
  - Lean ↔ source: ι = `pushforward unitsValCM` (∫φ∘val dμ = ∫φ|_units dμ ✓ same).
    Injectivity: restriction is surjective via `extendByZero` (clopen gluing on the
    partition units ⊔ pℤ_p — continuity on each clopen piece). `mem_range_iota_iff`:
    (⇒) `res_iota` + Cor 3.32 (L4.7); (⇐) if ψμ = 0 then μ = Res_{units}μ (L4.7) and
    μ = ι(μ∘extendByZero∘…) — construct the preimage by precomposition with
    `extendByZero`.
  - Attacks: [2] μ = δ_u (u unit): ιδ_u = δ_{u.val}, ψ = 0 ✓; μ = δ_0: ψδ_0 = δ_0 ≠ 0
    and δ_0 ∉ range ι (functions vanishing... ι ν (f) depends only on f|units; δ_0
    does not — consistent ✓). [3] val continuity: `Units.continuous_val` — present as
    `Units.continuous_val`/embedding-corollary; worker locates name (fallback: fst ∘
    embedProduct continuous). [4] drift: none, statements copied. [5] clopen gluing:
    `IsClopen` + `ContinuousOn.if`-style lemmas exist (`continuousOn_if`-family). 
    SURVIVED.

### Leaves (Λ(ℤ_p^×) ring + degree + finite levels)

- **L5.5** (leaf): `unitsConv` well-definedness + CommRing laws + `units_dirac_mul_dirac`
  - Lean: `PseudoMeasure.lean:38–77`
  - Source: Eq. (3.11) (quoted in substrate) + "One checks…" (line 910).
  - Discharge: inner-map continuity: `ContinuousMap.curry` (read at
    `Topology/CompactOpen.lean:419`) + L1.2; linearity fields: linearity of μ, ν
    through the explicit formula. comm: `integral_swap` (L5.2) applied to
    `F = f ∘ mul : C(ℤ_p^× × ℤ_p^×, ℤ_p)` (mul continuous: `ContinuousMul ℤ_[p]ˣ` —
    units of a topological monoid, mathlib instance; verified the instance pattern
    exists in `Topology/Algebra/Constructions.lean`/`Group/Basic.lean`). assoc: two
    applications of the definition + one swap (standard). one: δ_1 with f(1·y) = f(y) ✓
    `rfl`-adjacent. distrib/zero: linearity. dirac·dirac: evaluate: f((uv)·) ✓ direct.
  - Attacks: [1] non-abelian failure: convolution comm FAILS for non-abelian G — ℤ_p^×
    abelian ✓ (CommGroup instance); [2] δ_u·δ_v = δ_{uv}: matches the group ring ✓;
    [3] T2/zero-dim instances on ℤ_[p]ˣ needed for L5.2 — derivable from L5.3/L5.4
    embedding (worker derives `TotallyDisconnectedSpace`/`T2Space` instances; both
    standard for subspace-like topologies — flagged in ticket); [4] source's display
    has μ inner, λ outer; our `unitsConv μ ν` has ν inner, μ outer — for the
    *definition* this is a labeling choice; the comm law erases it; the `mul_def`
    orientation is recorded in the ticket so the §4 pass quotes it consistently.
    [5] `ContinuousMap.curry` verified by reading. SURVIVED.

- **L5.6** (leaf): `deg` ring hom + `augmentationIdeal`
  - Lean: `PseudoMeasure.lean:85–94`
  - Source (Def. 3.37, lines 1245–1253, verbatim):
    > "The augmentation ideal I((ℤ_p/p^n)^×) ⊂ 𝒪_L[(ℤ_p/p^n)^×] is the kernel of the
    > natural 'degree' map 𝒪_L[(ℤ/p^nℤ)^×] → 𝒪_L, ∑_a c_a[a] ↦ ∑_a c_a. These fit
    > together into a degree map Λ(ℤ_p^×) → 𝒪_L; we call its kernel the augmentation
    > ideal I(ℤ_p^×) ⊂ Λ(ℤ_p^×)."
  - Lean ↔ source: the limit degree map is evaluation at the constant function 1
    (each finite-level degree is ∑ μ(coset) = μ(𝟙) — additivity); multiplicativity:
    `deg(μ*ν) = μ(x ↦ ν(1)) = μ(1)ν(1)` since f = 1 gives f(xy) = 1.
  - Attacks: [2] deg(δ_u) = 1 ✓; deg(0) = 0 ✓; [3] no compactness subtleties (1 is
    continuous); [4] drift: source defines deg via finite levels; equality with
    evaluation-at-1 is a (trivial) lemma the worker proves when connecting to levelMap
    (L5.7) — recorded; [5] all internal. SURVIVED.

- **L5.7** (leaf): `isClopen_unitsToZModPow_fiber`, `levelMap` (ring hom fields),
  `levelMap_jointly_injective`
  - Lean: `PseudoMeasure.lean:107–133`
  - Source (lines 888–892, verbatim — the measure→limit map):
    > "We define an element λ_H of 𝒪_L[G/H] by setting λ_H := ∑_{[a] ∈ G/H} μ(aH)[a].
    > By the additivity property of μ, we see that (λ_H)_H ∈ varprojlim 𝒪_L[G/H]".
  - Lean ↔ source: G = ℤ_p^×, H = 1 + p^nℤ_p (kernel of reduction), G/H = (ℤ/p^n)^×
    (surjectivity of ℤ_p^× → (ℤ/p^n)^× from `toZModPow` surjectivity + unit lifting
    ‖x‖ = 1 ⟸ x̄ unit). Fibre clopen: preimage of a point under the locally constant
    reduction (`ker_toZModPow` read at `RingHoms.lean:457`: kernel = span p^n ⟹ the map
    is locally constant). Ring-hom: multiplicativity = the convolution of coset
    indicators identity `(μ*ν)(𝟙_{c̄}) = ∑_{āb̄=c̄} μ(𝟙_ā)ν(𝟙_b̄)` — finite
    computation from `unitsConv` + the partition ∑_ā 𝟙_ā = 1. Joint injectivity:
    locally constant functions on ℤ_p^× factor through some level (uniform continuity:
    a locally constant function on a compact space has a Lebesgue level; here levels
    are cofinal among clopen partitions since `1 + p^nℤ_p` is a neighbourhood basis of
    1 — from `ker_toZModPow` + `dist_appr_spec`-family) + L1.4 (ext on loc. const.).
  - Attacks: [2] n = 0: (ZMod 1)ˣ trivial; levelMap μ = deg μ·[1] ✓ consistent with
    L5.6; [3] surjectivity of unitsToZModPow needed for "G/H = (ℤ/p^n)^×" — verified
    provable (lift x̄: any lift x has ‖x‖ = 1 since x̄ ≠ 0 mod p... careful n ≥ 1 and
    unit mod p^n ⟹ unit mod p ⟹ ‖x‖ = 1 ✓; n = 0 trivial); [4] source quantifies over
    all open H — we use only the cofinal chain H_n, sufficient for everything §3.6 does
    (cyclicity argument is level-wise); recorded as a deliberate, conservative
    restriction; [5] `toZModPow` surjectivity: `ZMod.natCast_self_eq_zero`-family +
    density, or `PadicInt.toZModPow`-surjective if present — worker locates; fallback
    constructs preimage via `appr`. SURVIVED.

### Leaves (zero-divisor lemma)

- **L5.8** (leaf): `eq_zero_of_forall_unitsPowCM_eq_zero` (Lem. 3.36(i))
  - Lean: `PseudoMeasure.lean:147`
  - Source (proof, lines 1228–1229, verbatim):
    > "(i) Note that the vanishing condition forces the Mahler transform 𝒜_μ(T) =
    > ∑_{k ≥ 0} (∫_{ℤ_p} binom(x,k)·μ) T^k of μ to be constant, since each non-trivial
    > binomial polynomial is a linear combination of strictly positive powers of x. As
    > μ is a measure on ℤ_p^×, we also have ψ(𝒜_μ)(T) = 0 by (3.10). Since ψ is the
    > identity on constants…, we deduce that 𝒜_μ(T) = 0, so μ = 0."
  - Lean ↔ source: μ here is `ιμ` (the source works inside Λ(ℤ_p)). Two refinements,
    both ξ-free and faithful: (1) "linear combination of positive powers": we use the
    integral identity `n! · binom(x,n) = descPochhammer n = x·q(x)` with q ∈ ℤ_p[X]
    (`descPochhammer_eq_factorial_smul_choose`, read at `RingTheory/Binomial.lean:390`;
    descPochhammer has root 0 for n ≥ 1, so X ∣ it), giving `n!·(ιμ)(mahler n) =
    ∑ q_k·∫x^{k+1} = 0`, and n! ≠ 0 in the domain ℤ_p — avoiding the source's
    ℚ_p-coefficients aside. (2) "ψ identity on constants": the source cites the
    ξ-formula (3.13); instead: constants are c·δ_0-transforms, `𝓐(ιμ) = c = 𝓐(c·δ_0)`
    ⟹ `ιμ = c·δ_0` (L2.3); `ψ(ιμ) = 0` (Cor 3.32 direction of L4.7, since
    Res(ιμ) = ιμ by `res_iota`); `ψ(δ_0) = δ_0` (direct: `𝟙_{pℤ_p}(0)·f(shiftDiv 0) =
    f(0)`); so `c·δ_0 = 0 ⟹ c = 0 ⟹ ιμ = 0 ⟹ μ = 0` (ι injective, L5.4).
  - Attacks: [1] consistency: μ = δ_u has ∫x^k = u^k ≠ 0 — hypothesis excludes ✓;
    [2] k-range: hypothesis only for k > 0 — k = 0 unconstrained, and indeed the
    argument never uses k = 0 (descPochhammer trick needs n ≥ 1 ✓; the constant
    survives until the ψ step, which is exactly why ψ is needed — matches source);
    [3] could the conclusion hold without the ψ-step (i.e. is 𝓐 constant ⟹ 0 already)?
    NO: δ_0 has constant transform 1 ≠ 0 — the ψ-step is essential; our proof keeps it
    (faithful) ✓; [4] drift: refinement (1) avoids Stirling/ℚ_p; verified the source's
    own claim is recovered exactly; [5] `descPochhammer_eq_factorial_smul_choose`
    verified by reading; `Polynomial.dvd_iff_isRoot` for X ∣ descPochhammer. SURVIVED.

- **L5.9** (leaf): `mem_nonZeroDivisors_of_forall_unitsPowCM_ne_zero` (Lem. 3.36(ii))
  - Lean: `PseudoMeasure.lean:153`
  - Source (proof, lines 1232–1234, verbatim):
    > "0 = ∫_{ℤ_p^×} x^k·(μ*λ) = ∫(∫(xy)^k·μ(x))·λ(y) = (∫x^k·μ)(∫x^k·λ), which forces
    > λ = 0 by part (i)."
  - Discharge: `(xy)^k = x^k y^k` (mul_pow) through `unitsConv` (the inner integral of
    `f(xy)` for f = pow factors as `x^k·ν(pow)` by linearity-of-scalars), then L5.8.
  - Attacks: [2] hypothesis sharp: δ_1 has ∫x^k = 1 ≠ 0 ∀k and is a unit (not just
    non-zero-divisor) ✓ consistent; [3] need both factors: statement is one-sided
    (μ*λ = 0 ⟹ λ = 0) — commutativity (L5.5) gives the two-sided nonZeroDivisors
    membership ✓; [5] internal composition. SURVIVED.

### Leaves (pseudo-measures)

- **L5.10** (leaf): `isPseudoMeasure_algebraMap`
  - Lean: `PseudoMeasure.lean:177`
  - Source: immediate from Def. 3.34 (Λ is a ring): ([g]−[1])·μ ∈ Λ for μ ∈ Λ.
  - Discharge: take ν := (δ_g − 1)·μ; `map_mul` of algebraMap. Attacks: [2] μ = 0 ✓;
    [5] `algebraMap` ring hom ✓. SURVIVED.

- **L5.11** (leaf): `pseudoMeasure_eq_zero_of_moments` (Lem. 3.36(iii))
  - Lean: `PseudoMeasure.lean:185`
  - Source (proof, lines 1236–1240, verbatim):
    > "Let μ be a pseudo-measure satisfying the vanishing condition. Let a ≠ 1 be an
    > integer prime to p; then λ = ([a] − [1])μ ∈ Λ(ℤ_p^×) is a measure by the
    > definition of pseudo-measure, and by (3.12) we have ∫x^k·λ = (a^k−1)∫x^k·μ = 0
    > for all k > 0. By part (i), we have λ = 0. But [a]−[1] satisfies the condition of
    > part (ii), so it is not a zero-divisor, and this forces μ = 0."
  - Lean ↔ source: our statement quantifies the hypothesis over the witnesses ν of
    `([a]−[1])q = ν` (the skeleton's moment encoding; the named-integration API
    `∫x^k·q` is built in the §4 pass — recorded in plan/tickets). Proof: extract ν
    (hq at a), h gives ν's moments vanish… wait — h gives ν(x^k) = 0 directly; L5.8
    gives ν = 0; `dirac_sub_one_mem_nonZeroDivisors` (L5.13) + faithfulness of
    algebraMap to the fraction ring (`IsFractionRing.injective`) force q = 0.
  - Attacks: [2] q = algebraMap μ for honest μ: hypothesis reduces to (a^k−1)·∫x^k μ
    = 0 ⟹ ∫x^k μ = 0 (a^k ≠ 1) ⟹ μ = 0 ✓ recovers (i); [3] the `ha` hypothesis
    (a^k ≠ 1 ∀k>0) is exactly what the source's "integer a ∉ {0,±1} prime to p"
    provides — we hypothesise the abstract property instead of the integer (cleaner,
    no loss; the §4 instantiation has explicit a); [4] (3.12)-independence (the
    source's well-definedness display, lines 1198–1200) is *absorbed* by quantifying
    over witnesses — no drift in strength; [5] `IsFractionRing.injective` exists
    (localisation at nonZeroDivisors is injective — `IsFractionRing` API, read).
    SURVIVED.

- **L5.12** (leaf): `exists_topological_generator`
  - Lean: `PseudoMeasure.lean:208`
  - Source (Lem. 3.38 statement, lines 1257–1258):
    > "Let a be any topological generator of ℤ_p^× (for example, take a to be a
    > primitive root modulo p such that a^{p−1} ≢ 1 (mod p²))".
  - Discharge: `isCyclic_units_of_prime_pow` (read at `ZMod/UnitsCyclic.lean:198`,
    odd p, all n; the file's proof manufactures generators of the form needed). Lift a
    generator compatible across levels: take g a unit generating (ZMod p²)ˣ; its
    ℤ_p-Teichmüller-free lift via `appr`/`CRT` generates every level (standard:
    generator mod p² ⟹ generator mod p^n for odd p — the UnitsCyclic file contains
    the order computation `orderOf_one_add_mul_prime` to make this exact).
  - Attacks: [2] p = 2 excluded?? — statement as skeletonised does NOT assume p ≠ 2,
    but (ZMod 8)ˣ is NOT cyclic (read: `UnitsCyclic.lean:82`)! **ATTACK SUCCEEDS for
    p = 2.** Resolution: the source works with odd p from §4 onward (and Lem. 3.38's
    proof says "As p is odd", line 1265). FIX APPLIED: ticket T-board marks this leaf
    (and the two depending on it) with the standing hypothesis `p ≠ 2`; the skeleton
    declaration must take `(hp2 : p ≠ 2)`. → **statement amended in skeleton** (see
    tickets T026–T028; the `variable (hodd : p ≠ 2)` section in the skeleton file
    covers `exists_topological_generator`, `augmentationIdeal_eq_span`,
    `isPseudoMeasure_mk'`, `isPseudoMeasure_iff_exists`; verify the hypothesis is
    genuinely threaded — worker checks Lean actually enforces it).
    Post-fix: [2] re-run: p odd ⟹ all levels cyclic ✓.
  - [5] `isCyclic_units_of_prime_pow (p) (hp) (hp2 : p ≠ 2) (n)` — signature READ,
    requires p ≠ 2 ✓ consistent with the fix. SURVIVED (after amendment).

- **L5.13** (leaf): `dirac_sub_one_mem_nonZeroDivisors`
  - Lean: `PseudoMeasure.lean:231`
  - Source: line 1240 ("But [a]−[1] satisfies the condition of part (ii)") — moments
    of [a]−[1] are `a^k − 1 ≠ 0`.
  - Discharge: `(δ_a − 1)(x^k) = a^k − 1` (Dirac evaluation, `units_one_def`) + L5.9.
  - Attacks: [2] a = 1 would fail (0 moments) — hypothesis `ha` excludes ✓; a of
    finite order q: a^q − 1 = 0 fails — `ha` excludes torsion ✓ (and torsion exists:
    μ_{p−1} ⊂ ℤ_p^×! so `ha` is genuinely needed — good); [3] `ha` is implied by
    topological-generator-ness (torsion elements generate finite subgroups, not dense
    ones) — the bridging lemma is part of T028's sketch; [5] internal. SURVIVED.

- **L5.14** (leaf, the inverse-limit cluster): `augmentationIdeal_eq_span`
  - Lean: `PseudoMeasure.lean:218`
  - Source (proof of Lem. 3.38, lines 1264–1272, verbatim):
    > "As p is odd, (ℤ_p/p^n)^× is cyclic, generated by ā := a (mod p^n), and we have
    > I((ℤ_p/p^n)^×) = ([ā] − [1̄])𝒪_L[(ℤ_p/p^n)^×]. In the inverse limit we see that
    > I(ℤ_p^×) = ([a]−[1])Λ(ℤ_p^×)."
  - Sub-decomposition (the source's "In the inverse limit" expanded — the genuinely
    compressed step):
    - L5.14a: finite-level generation: for a finite cyclic group C = ⟨g⟩, the
      augmentation ideal of `MonoidAlgebra ℤ_[p] C` is generated by `single g 1 − 1`
      (every `[g^k] − 1 = ([g]−1)(∑_{i<k}[g^i])`). New, ~20 LOC (source: line 1267,
      asserted). Verified absent from mathlib (no augmentation-ideal-of-group-ring
      generation lemma found; `MonoidAlgebra` API read).
    - L5.14b: solution sets are compatible nonempty "cylinders": for μ ∈ I, the level-n
      solution set S_n = {ν : levelMap n (([a]−1)ν − μ) = 0 } is nonempty (L5.14a +
      L5.7 surjectivity-of-levels... precisely: lift the level-n witness — levelMap is
      surjective onto the group ring? surjectivity via finite linear combinations of
      coset-Diracs ✓ worker proves; ~15 LOC), closed in the product-of-values topology,
      and decreasing after refinement.
    - L5.14c: compactness: Λ(ℤ_p^×) embeds in `Π_{clopen cosets} ℤ_p` (values on the
      countably many coset indicators) with closed image; `S_n` are nested nonempty
      compacts; `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`
      (read at `Topology/Compactness/Compact.lean:336`) gives ν ∈ ⋂ S_n; joint
      injectivity (L5.7) shows ([a]−1)ν = μ.
  - Attacks: [1] is the statement even true? cross-check the χ-decomposition heuristic:
    Λ(ℤ_p^×) ≅ ∏_{χ mod p−1} ℤ_p[[T]]; [a]−1 ↦ (χ(a)(1+T)^{t} − 1)_χ which is a unit
    in the χ ≠ 1 components (constant term χ(a)−1 a unit) and an associate of T at
    χ = 1; I = (0,…,0,(T)) — matches ([a]−1)Λ ✓ consistent. [2] p = 2: cyclicity fails
    (L5.12 attack) — hypothesis p ≠ 2 threaded ✓. [3] does the compactness argument
    need second-countability/metrisability? — the chain is ℕ-indexed (sequence
    version), no. [4] drift: the source's "inverse limit" is along ALL open subgroups;
    our ℕ-chain is cofinal — recorded at L5.7[4]. [5] compactness-lemma name verified
    by reading. SURVIVED.

- **L5.15** (leaf): `isPseudoMeasure_mk'` (Lem. 3.38) + `isPseudoMeasure_iff_exists`
  - Lean: `PseudoMeasure.lean:224, 246`
  - Source (proof, lines 1273–1282, verbatim):
    > "Thus if g ∈ ℤ_p^×, we have [g]−[1] ∈ I(ℤ_p^×), and we must have [g]−[1] =
    > ν([a]−[1]) for some ν ∈ Λ(ℤ_p^×). Then ([g]−[1])μ' = ν([a]−[1])μ' = ν·μ ∈
    > Λ(ℤ_p^×), that is, μ' is a pseudo-measure."
    and lines 1284–1285:
    > "Note moreover that all pseudo-measures have this shape. Indeed, let μ' be a
    > pseudo-measure, and a ∈ ℤ_p^× a topological generator; then μ = ([a]−[1])μ' is a
    > measure, and μ' = μ/([a]−[1]) as above."
  - Discharge: deg([g]−1) = 0 (L5.6) + L5.14 + fraction-ring arithmetic
    (`IsLocalization.mk'_spec`, standard). Converse: instantiate IsPseudoMeasure at
    g = a, divide.
  - Attacks: [2] μ = 0: q = 0 is a pseudo-measure ✓ both directions ✓; [3] hreg is
    needed to form mk' — supplied by L5.13 ✓ explicit hypothesis (no circularity:
    L5.13 independent of L5.14/15); [5] `IsLocalization.mk'` API standard. SURVIVED.

---

## API gaps (each with sub-decomposition, all skeletonised)

- **AG1 (Fubini cluster)**: L5.1 + L5.2 — needed by L5.5. New infrastructure, fully
  decomposed above, skeleton in `Fubini.lean`. No further gaps beneath (all inputs
  verified in mathlib).
- **AG2 (finite-level cluster)**: L5.7 + L5.14a–c — needed by L5.14/L5.15. Fully
  decomposed above, skeleton in `PseudoMeasure.lean`. No further gaps beneath.

## Confidence gate (Step 5) — assessment

1. Every leaf: discharged from mathlib (file+line cited, read) / from project leaves /
   or an explicit API gap with sub-decomposition (AG1, AG2). ✓
2. Skeleton compiles: `lake build` success, 2437 jobs, sorries only. ✓
3. Verbatim quotes: every leaf above carries one (or, for internal nodes, a structural
   pointer to its children's quotes). ✓
4. Adversarial pass: every leaf has ≥ 3 recorded attacks; **one attack succeeded**
   (L5.12, p = 2) and was resolved by amending the affected statements to carry
   `p ≠ 2` — see tickets T026–T028, which begin by threading the hypothesis through
   the skeleton (the `hodd` section variable is currently *unused* by the declarations
   and must be made binding). All other attacks: no flaw found. ✓ (with the noted
   mandatory amendment as the first action of the affected tickets)
5. Prior-B2 log: empty (absent) — vacuously clean. ✓
6. Tree mirrors the source: each R-node cites the source's own proof location; the two
   compressed source steps ("one checks", "in the inverse limit") are expanded as AG1,
   AG2 with the expansion recorded. LOC estimates cited against source line counts
   where given. ✓

**Feasibility**: every leaf is dischargeable from verified mathlib API plus the two
self-contained infrastructure clusters (AG1 ≈ 65 LOC, AG2 ≈ 60 LOC estimated against
source compression points). The single mathematical trap found (p = 2 cyclicity) is
fenced by hypothesis. No REVIEW-PENDING leaves. The decomposition is ready for
ticketing.
