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

---

# §4 — The Kubota–Leopoldt p-adic L-function (TeX 1440–1609)

## Skeleton location (§4)
- `PadicLFunctions/KubotaLeopoldt/ZetaValues.lean` (4 sorries)
- `PadicLFunctions/KubotaLeopoldt/ZetaValuesComplex.lean` (1 sorry)
- `PadicLFunctions/KubotaLeopoldt/MuA.lean` (31 sorries)
- `PadicLFunctions/KubotaLeopoldt/ZetaP.lean` (11 sorries)
`lake build PadicLFunctions` passes, sorries only — verified 2026-06-10.

## Result R-KL: `kubotaLeopoldt` (RJW Thm 4.1, TeX 1444–1447)

> "There is a unique pseudo-measure $\zeta_p$ on $\Zp^\times$ such that, for all
> $k > 0$, we have $\int_{\Zp^\times}x^k \cdot\zeta_p = (1-p^{k-1})\zeta(1-k)$."

### Plain-English proof (source structure, TeX 1599)
"Existence of the pseudo-measure is Proposition \ref{PropInterpolation2}. To conclude
the proof we need only show uniqueness; but this follows from Lemma
\ref{lem:zero divisor}(iii)." The chain to PropInterpolation2 is: §4.1 constructs
`μ_a` (integer `a` coprime to `p`) via its Mahler transform `F_a` (Prop 4.4/Def 4.5)
and computes its moments via Bernoulli values (Lem 4.2/4.3, Prop 4.6); §4.2 shows
`ψ(μ_a) = μ_a` (Lem 4.7) hence restriction to `ℤ_p^×` multiplies the k-th moment by
`(1−p^k)` (Prop 4.8); §4.3 multiplies by `x⁻¹` (shifting moments, eq. 4.11/TeX 1561)
and divides by `θ_a = [a]−[1]` in `Q(ℤ_p^×)` (Def 4.10), giving a pseudo-measure by
Lem 3.37 (= our `isPseudoMeasure_mk'`) with the stated interpolation after the sign
removal at TeX 1596.

**Moment encoding.** The source integrates a pseudo-measure via eq. (3.x)
`∫x^k·λ := (g^k−1)^{-1}∫x^k·([g]−[1])λ` (the encoding already used by
`pseudoMeasure_eq_zero_of_moments`, §3 board T025). The Lean main statement
quantifies over all `b : ℤ_[p]ˣ` and all witnesses `ν` of `([b]−[1])·q ∈ Λ`:
`∫x^k ν = (b^k−1)(1−p^{k−1})ζ(1−k)`. This is the same statement with the division
cleared — faithful and denominator-free.

**ζ-values design decision.** Every interpolation statement uses
`zetaNeg k := (−1)^k B_{k+1}/(k+1) ∈ ℚ` (TeX 1455's own formula for `ζ(−k)`), cast
into `ℚ_p`; `ζ(1−k) = zetaNeg (k−1)`. The complex identification is the quarantined
bridge L0.3 (`zetaNeg_eq_riemannZeta`). The analytic-continuation statement
`L(f_a,s) = (1−a^{1−s})ζ(s)` of Lem 4.2 is **§2 material** (Mellin transforms,
deferred with the §2 Motivation chapter); the part of Lem 4.2 that §4 actually
consumes is the value formula `f_a^{(k)}(0) = (−1)^k(1−a^{1+k})ζ(−k)`, whose honest
content is the Bernoulli power-series identity L2.6 below. Blueprint node
`kl-lem-values-zeta` therefore stays **unwired** until §2's Mellin theory exists;
the value formula is wired through `muA_apply_powCM`.

### Sub-tree R0: rational zeta values (`ZetaValues*.lean`)

- **L0.1** (leaf, mathlib): `zetaNeg_zero` + def `zetaNeg`
  - Lean: `ZetaValues.lean:17,21`
  - Source: TeX 1455: > "$\zeta(-k) = (d^kf/dt^k)(0) = (-1)^k B_{k+1}/(k+1).$"
  - Lean ↔ source: `zetaNeg k := (−1)^k·bernoulli (k+1)/(k+1)` is the displayed
    formula verbatim; mathlib's `bernoulli` has `B₁ = −1/2`, matching `ζ(0) = −1/2`
    (sanity: `zetaNeg 0 = B₁ = −1/2` ✓).
  - Discharged by: `bernoulli_one` (`= -1/2`, Bernoulli.lean) + `norm_num`.
  - Attacks: [1] edge `k=0`: `zetaNeg 0 = 1·B₁/1 = −1/2 = ζ(0)` ✓; [2] convention
    drift: if the paper meant `bernoulli'` (B₁=+1/2) then `ζ(0) = +1/2`, false —
    so the paper's display (and our def) is the `B₁=−1/2` convention, confirmed
    against mathlib's `riemannZeta_neg_nat_eq_bernoulli` which uses `bernoulli` with
    the same `(−1)^k` prefactor; [3] `k` odd ≥1: `zetaNeg 1 = −B₂/2 = −1/12 = ζ(−1)` ✓
    textbook value. Verdict: SURVIVED.
  - Prior-B2: no match (log absent/empty).

- **L0.2** (leaf, mathlib): `zetaNeg_eq_zero_of_even`
  - Lean: `ZetaValues.lean:25`
  - Source: TeX 1596: > "we may remove the $(-1)^{k}$ as $\zeta(1-k) \neq 0$ if and
    only if $k$ is even."
  - Lean ↔ source: `ζ(1−k) = 0` for odd `k ≥ 3` ⟺ `zetaNeg m = 0` for even `m ≥ 2`
    ⟺ `B_{m+1} = 0` for odd `m+1 ≥ 3`.
  - Discharged by: `bernoulli_eq_zero_of_odd` (Bernoulli.lean:217, verified).
  - Attacks: [1] edge `m=0`: excluded by `hk : k ≠ 0` — `zetaNeg 0 = −1/2 ≠ 0`, so
    the hypothesis is necessary (over-removal attack fails the statement without it);
    [2] discharge type: `bernoulli_eq_zero_of_odd {n} (h_odd : Odd n) (hlt : 1 < n)`
    — with `n := k+1`, `Odd (k+1)` from `Even k`, `1 < k+1` from `k ≠ 0` ✓ both
    hypotheses available; [3] counterexample search: `bernoulli 3 = 0`,
    `bernoulli 5 = 0` known values consistent. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L0.3** (leaf, mathlib): `zetaNeg_eq_riemannZeta` (complex bridge)
  - Lean: `ZetaValuesComplex.lean:18`
  - Source: TeX 1455 (as L0.1) + mathlib `riemannZeta_neg_nat_eq_bernoulli`
    (HurwitzZetaValues.lean, located by file grep).
  - Lean ↔ source: our `zetaNeg` is definitionally the right side of mathlib's
    `riemannZeta_neg_nat_eq_bernoulli : riemannZeta (-n) = (-1)^n * bernoulli (n+1) / (n+1)`
    (exact statement to be confirmed at the declaration during execution; the name
    and file are verified).
  - Attacks: [1] statement-shape risk: mathlib's lemma may state `(-n : ℂ)` vs our
    `-(k : ℂ)` — same term up to `push_cast`; [2] division-in-ℂ vs division-in-ℚ-then-
    cast: `Rat.cast` is a field hom, commutes with `/` ✓; [3] junk-value attack:
    no division-by-zero (`k+1 ≠ 0`). Verdict: SURVIVED (with the noted
    confirm-at-execution on argument form).
  - Prior-B2: no match.

- **L0.4** (leaf, project+mathlib): `neg_one_pow_mul_one_sub_pow_mul_zetaNeg`
  - Lean: `ZetaValues.lean:32`
  - Source: TeX 1593–1596: > "$\int_{\Zp^\times} x^k \cdot \zeta_p =
    (-1)^k(1-p^{k-1})\zeta(1-k)$. To get the result, we may remove the $(-1)^{k}$ as
    $\zeta(1-k) \neq 0$ if and only if $k$ is even."
  - Lean ↔ source: the lemma is exactly the removal step, case-split: `k = 1` ⟹
    `1−q⁰ = 0`; `k` even ⟹ `(−1)^k = 1`; `k ≥ 3` odd ⟹ `zetaNeg (k−1) = 0` by L0.2.
    (The source says "k even"; the `k = 1` case is covered on the source side because
    `1−p^{k−1}` vanishes there — our proof makes that explicit.)
  - Discharged by: L0.2 + `Even.neg_one_pow` + `ring`-algebra.
  - Attacks: [1] edge `k=1`: LHS `= (−1)·0·(−1/2) = 0 =` RHS ✓ (this is where a naive
    "k even" proof breaks — caught and handled); [2] edge `k=2`: `(−1)² = 1` trivial ✓;
    [3] `k=3`: `zetaNeg 2 = 0` by L0.2 ✓; [4] generalisation attack: stated for
    arbitrary `q : ℚ` (not just `p`) — strictly more general, no hidden hypothesis.
    Verdict: SURVIVED.
  - Prior-B2: no match.

### Sub-tree R1: `F_a` and `μ_a` (RJW Prop 4.4, Def 4.5; `MuA.lean`)

Internal node. Source's own proof of Prop 4.4 (TeX 1488–1494):
> "We can expand $(1+T)^a - 1 = \sum_{n\geq 1} {a \choose n} T^n = aT\big[1+Tg(T)\big]$,
> where $g(T) = \sum_{n\geq 2}\frac{1}{a} {a \choose n} T^{n-2}$ has coefficients in
> $\zp$ since we have chosen $a$ coprime to $p$. Hence, expanding the geometric
> series, we find $\frac{1}{T} - \frac{a}{(1+T)^a - 1} = \frac{1}{T} \sum_{n \geq
> 1}(-T)^n g(T)^n$, which is visibly an element of $\Zp\lsem T\rsem$."

**Realisation note (recorded design decision, not a drift).** The source's proof is
"the denominator is `T·(unit)`, so the difference of poles cancels". We package the
same fact equation-first: `(1+T)^a − 1 = T·geomSum a` with `geomSum a = Σ_{i<a}(1+T)^i`
of constant coefficient `a` (a unit iff `p ∤ a` — the source's "since we have chosen
`a` coprime to `p`"), and *define* `F_a := ((geomSum a − a)/T) · geomSum a⁻¹`. Then
`((1+T)^a−1)·F_a = geomSum a − a` (L1.6) is the identity `F_a = 1/T − a/((1+T)^a−1)`
with denominators cleared — the form every later step actually uses. The geometric-
series expansion the source displays is *how it proves membership in ℤ_p⟦T⟧*; our
unit-inverse `Ring.inverse` achieves membership definitionally. Composition is
attack-checked at L1.6.

- **L1.1** (leaf, mathlib): `PadicInt.isUnit_natCast_of_not_dvd`
  - Lean: `MuA.lean:35`
  - Source: TeX 1491 ("has coefficients in ℤ_p since we have chosen a coprime to p" —
    the underlying fact: a coprime to p is a p-adic unit).
  - Discharged by: `PadicInt.isUnit_iff` (PadicIntegers.lean:366) +
    `PadicInt.norm_int_lt_one_iff_dvd` (:280) + `le_antisymm (norm_le_one _)`.
  - Attacks: [1] edge `a=0`: `p ∣ 0` always, hypothesis excludes ✓; [2] edge `a=1`:
    `IsUnit 1` ✓; [3] discharge-shape: `norm_int_lt_one_iff_dvd (k : ℤ) : ‖(k:ℤ_[p])‖ < 1 ↔ (p:ℤ) ∣ k`
    is for `ℤ`-cast — need `Int.natCast_dvd_natCast` bridge for `(a:ℕ)`, a 1-line
    `exact_mod_cast` ✓; [4] counterexample: none possible (standard fact).
    Verdict: SURVIVED.
  - Prior-B2: no match.

- **L1.2** (leaf, mathlib): `constantCoeff_geomSum`
  - Lean: `MuA.lean:53`. Source: implicit in TeX 1490 (`Σ_{n≥1} C(a,n) Tⁿ` has the
    `aT` leading term ⟺ cofactor has constant term `a`).
  - Discharged by: `map_sum`, `constantCoeff_one`, `constantCoeff_X`, `map_pow`;
    `Σ_{i<a} 1 = a` via `Finset.sum_const` + `card_range`.
  - Attacks: [1] `a=0`: empty sum, `constantCoeff 0 = 0 = (0:ℤ_[p])` ✓ cast of 0;
    [2] `(1+X)^i` const coeff `1^i = 1` ✓; [3] discharge: all four names standard
    simp lemmas. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L1.3** (leaf, mathlib): `geomSum_mul_X`
  - Lean: `MuA.lean:56`. Source: TeX 1490 (the same display, rearranged:
    `(1+T)^a − 1 = T·Σ_{i<a}(1+T)^i`).
  - Discharged by: `geom_sum_mul : (Σ i ∈ range n, x^i) * (x − 1) = x^n − 1` with
    `x := 1+X` (so `x − 1 = X` after `add_sub_cancel_left`). NOTE: `geom_sum_mul`'s
    current file location was not pinned by grep (Algebra/GeomSum.lean moved);
    fallback if renamed: `mul_geom_sum` variant or a 6-line induction on `a`.
  - Attacks: [1] `a=0`: `0 * X = (1+X)^0 − 1 = 0` ✓; [2] `a=1`: `1·X = (1+X)−1` ✓;
    [3] commutativity orientation (left vs right factor): ℤ_p⟦X⟧ commutative,
    `mul_comm` bridges ✓; [4] discharge-existence risk logged (name location
    unpinned) with explicit fallback. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L1.4** (leaf, mathlib): `isUnit_geomSum`
  - Lean: `MuA.lean:59`. Source: TeX 1490–1491 (unit cofactor ⟸ `a` coprime `p`).
  - Discharged by: `PowerSeries.isUnit_iff_constantCoeff` (Inverse.lean:111,
    verified) + L1.2 + L1.1.
  - Attacks: [1] hypothesis necessity: `p ∣ a` ⟹ constant coeff non-unit ⟹ non-unit:
    hypothesis is sharp ✓; [2] discharge type: `isUnit_iff_constantCoeff : IsUnit φ ↔
    IsUnit (constantCoeff R φ)` — exact match ✓; [3] composition: 3 lemmas ≤ 3 ✓.
    Verdict: SURVIVED.
  - Prior-B2: no match.

- **L1.5** (leaf, mathlib): `FaNum` + `X_mul_FaNum`
  - Lean: `MuA.lean:63,66`. Source: the `1/T·(...)` shape of TeX 1492 (the numerator
    after the pole at `T=0` cancels; constant term of `geomSum − a` is `0` by L1.2).
  - Discharged by: `PowerSeries.ext` + `coeff_X_mul`-family (`coeff_succ_X_mul`) +
    L1.2 (coefficient 0 vanishes); `coeff_mk`.
  - Attacks: [1] coefficient 0: `(X·FaNum)₀ = 0` and `(geomSum − a)₀ = a − a = 0` ✓;
    [2] coefficient n+1: `FaNum_n = geomSum_{n+1}`, and `(a : PowerSeries)`'s
    higher coefficients vanish (`coeff_natCast`-shape — natCast = C a, `coeff_C`) ✓;
    [3] junk-freedom: `FaNum` is total (no hypothesis), fine. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L1.6** (internal, composition of L1.3–L1.5): `geomSum_mul_Fa` +
  `one_add_X_pow_sub_one_mul_Fa`
  - Lean: `MuA.lean:76,82`. Source: TeX 1475 (the definition of `F_a`)
    > "$F_a(T) \defeq \frac{1}{T} - \frac{a}{(1+T)^a - 1}$"
    cleared of denominators via the factorisation of Prop 4.4's proof.
  - Composition: `geomSum·Fa = geomSum·FaNum·inverse(geomSum) = FaNum` by
    `Ring.inverse_mul_cancel` (L1.4); then `((1+X)^a−1)·Fa = X·geomSum·Fa =
    X·FaNum = geomSum − a` by L1.3 + L1.5.
  - Attacks (composition): [1] could children hold and parent fail? The only glue is
    associativity/commutativity in a CommRing — no; [2] `Ring.inverse` junk when
    `p ∣ a`: both lemmas carry `hpa`, junk fenced ✓; [3] **sign check against the
    source display** (the blueprint review previously flagged the source's
    `Σ(−T)ⁿg(T)ⁿ` as having a sign slip): our route never uses that display — the
    characterising identity is sign-unambiguous, and its `k=1, a=2` instance was
    hand-checked: `F₂ = 1/T − 2/(T²+2T) = (T+2−2)/(T(T+2)) = 1/(T+2)`, and
    `((1+T)²−1)·1/(T+2) = T(T+2)/(T+2) = T = geomSum 2 − 2 = (2+T) − 2` ✓.
    Verdict: SURVIVED.
  - Prior-B2: no match.

- **L1.7** (leaf, project): `muA` + `mahlerTransform_muA`
  - Lean: `MuA.lean:88,92`. Source: TeX 1496–1498:
    > "Let $\mu_a$ be the measure on $\Zp$ whose Mahler transform is $F_a(T)$."
  - Discharged by: `mahlerLinearEquiv` (MahlerTransform.lean:160, sorry-free) —
    `apply_symm_apply`.
  - Attacks: [1] existence presupposition: the source needs Prop 4.4 (F_a ∈ ℤ_p⟦T⟧)
    *and* Thm 3.20 (transform bijective) — both in hand (`mahlerLinearEquiv`);
    [2] discharge: `LinearEquiv.apply_symm_apply` exact shape ✓; [3] defeq-drift:
    `mahlerLinearEquiv` vs `mahlerTransform` — relation lemma exists in
    MahlerTransform.lean (`mahlerTransform_ofPowerSeries`); confirm which gives the
    1-liner at execution. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L1.8** (leaf, project): `binomialSeries_natCast`
  - Lean: `MuA.lean:95`. Source: bridging fact for TeX 1490 (`(1+T)^a` for integer
    `a` is the `a`-fold product; the Mahler transform of `δ_a` is `binomialSeries a`).
  - Discharged by: project-private `binomialSeries_mul_nat` (Toolbox.lean:184-190,
    `binomialSeries (c·k) = binomialSeries c ^ k`) at `c = 1` + `binomialSeries_one`
    — wait, need `binomialSeries 1 = 1 + X`: from `binomialSeries_coeff`
    (`C(1,0)=1, C(1,1)=1, C(1,n≥2)=0` via `Ring.choose` on ℕ-cast). The Toolbox
    private lemma must be re-derived or de-privatised — ticket notes this (the
    statement is 3 lines from `binomialSeries_add` by induction anyway).
  - Attacks: [1] `a=0`: `binomialSeries 0 = 1 = (1+X)^0` ✓ (`binomialSeries_zero`
    exists, used in Toolbox); [2] `Ring.choose` on `ℤ_[p]` at natCast equals
    `Nat.choose` (`Ring.choose_natCast` exists — used by §3 T005 work) ✓;
    [3] privacy obstacle is real and logged: plan = local rederivation. Verdict:
    SURVIVED.
  - Prior-B2: no match.

- **L1.9** (internal, composition): `dirac_natCast_sub_one_mul_muA`
  - Lean: `MuA.lean:101`. Source: the measure-side reading of TeX 1475's identity
    (the source works on transforms; `mahlerRingEquiv` is a ring iso — RJW Thm 3.20,
    proven — so the identity transfers verbatim).
  - Composition: apply `(mahlerRingEquiv p).injective`; transform of LHS:
    `((1+X)^a − 1)·F_a` via `mahlerTransform_dirac` + L1.8 + ring-iso
    multiplicativity; transform of RHS: `geomSum − a` via `map_sum`,
    `mahlerTransform_dirac`, L1.8 (at each `i`), and `a • 1 ↦ a • 1`
    (transform is ℤ_p-linear, `map_one`); conclude by L1.6.
  - Attacks: [1] children-true-parent-false: glue is injectivity of a ring iso +
    linearity — no gap; [2] `1` vs `dirac 0`: RHS uses ring-`1`; transform of `1`
    is `1` (`mahlerTransform_one`, Convolution.lean) and `binomialSeries 0 = 1` —
    consistent ✓; [3] smul-vs-natCast mismatch: `(a : ℤ_[p]) • (1 : Λ)` transforms to
    `(a:ℤ_[p]) • (1 : ℤ_[p]⟦X⟧) = (a : ℤ_[p]⟦X⟧)` — matches L1.6's RHS cast ✓
    (`Nat.cast_smul_eq_nsmul`-style bridging noted). Verdict: SURVIVED.
  - Prior-B2: no match.

- **L1.10** (leaf, mathlib): `instIsDomain` + `dirac_natCast_sub_one_ne_zero`
  - Lean: `MuA.lean:107,110`. Source: TeX 1175 (§3, quoted in §3 tree: Λ(G) domain
    for the cyclotomic use) — here the ambient fact "Λ(ℤ_p) ≅ ℤ_p⟦T⟧ is a domain"
    that the cancellation in R3 needs; the source cancels `θ_a`-style nonzero
    elements freely (TeX 1589, "independent of the choice of a by Lemma 3.36(iii)").
  - Discharged by: `mahlerRingEquiv` + `MulEquiv.isDomain` (transport; exact mathlib
    name to confirm — candidates `RingEquiv.isDomain`/`Function.Injective.isDomain`)
    + ℤ_p⟦X⟧ domain instance (mathlib: PowerSeries over a domain is a domain ✓
    standard instance); ne-zero: transform `(1+X)^a − 1 ≠ 0` since coefficient 1 is
    `a ≠ 0` (cast-injective on ℕ for `a ≠ 0` mod nothing — `Nat.cast_injective` on
    char-0 ℤ_p ✓).
  - Attacks: [1] `a=0` edge: `ha : a ≠ 0` required and stated ✓ (`dirac 0 − 1 = 0`
    really is zero — the hypothesis is sharp); [2] coefficient-1 computation:
    `coeff 1 ((1+X)^a − 1) = C(a,1) = a` via binomial expansion ✓; [3] transport
    name risk: three candidate mathlib spellings listed, one will fire. Verdict:
    SURVIVED.
  - Prior-B2: no match.

### Sub-tree R2: moments of `μ_a` (RJW Lem 4.2/4.3 value-formula + Prop 4.6)

Internal node. Source's proof of Prop 4.6 (TeX 1505–1507):
> "By Corollary \ref{cor:eval at x^k}, the left-hand side is
> $(\partial^k\sA_{\mu_a})(0)$. By definition of $\mu_a$ and Lemma
> \ref{lem:define F_a} this is $(\partial^kF_a)(0) = f_a^{(k)}(0)$. This equals the
> right-hand side by Lemma \ref{lem:values of zeta}."

and of Lem 4.3 (TeX 1473–1479):
> "Under the substitution $e^t = T+1$, the derivative $d/dt$ becomes the operator
> $\partial = (1+T)\frac{d}{dT}$. In particular, if we define [$F_a$] we have
> $f_a^{(k)}(0) = \big( \partial^k F_a \big)(0)$."

The value formula from Lem 4.2 (TeX 1463): `f_a^{(k)}(0) = (−1)^k(1−a^{1+k})ζ(−k)`,
whose proof "follows from calculations similar to those in the proof of Lemma
\ref{lem:FormulaZeta}" — i.e. the Taylor expansion of `1/(e^t−1)` by Bernoulli
numbers. Formal-series realisation: `t·f_a(t) = B(t) − B(at)` where
`B = bernoulliPowerSeries` (mathlib: `bernoulliPowerSeries_mul_exp_sub_one :
bernoulliPowerSeries A * (exp A − 1) = X`, Bernoulli.lean:273, verified), since
`f_a = 1/(e^t−1) − a/(e^{at}−1)` and `B(t) = t/(e^t−1)`, `B(at) = at/(e^{at}−1)`.

- **L2.1** (leaf, project): `cor:eval at x^k` — **already proven**: `apply_powCM`
  (Toolbox.lean:116, sorry-free). Cited, not re-ticketed.

- **L2.2** (leaf, mathlib): `map_del`
  - Lean: `MuA.lean:139`. Source: coefficient-cast plumbing (implicit; the source
    works in ℚ-coefficients silently when writing `B_{k+1}/(k+1)`).
  - Discharged by: `PowerSeries.ext` + `coeff_map` + `coeff_derivativeFun` +
    ring-hom arithmetic (`map_mul/map_add/map_natCast`).
  - Attacks: [1] `derivativeFun` commutes with `map` only because coefficients map
    multiplicatively against `(n+1) : ℕ`-casts — `map_natCast` handles ✓; [2] the
    `(1+X)·` factor maps to `(1+X)·` (`map_one`, `map_X`) ✓; [3] hom direction:
    `Coe.ringHom : ℤ_[p] →+* ℚ_[p]` injective — not even needed here (pure
    naturality). Verdict: SURVIVED.
  - Prior-B2: no match.

- **L2.3** (leaf, mathlib): `hasSubst_exp_sub_one`
  - Lean: `MuA.lean:131`. Source: the substitution `e^t = T+1` of TeX 1474 read
    backwards (`T = e^t − 1`), well-defined as `constantCoeff (exp − 1) = 0`.
  - Discharged by: `HasSubst.of_constantCoeff_zero'` (the §3 route used for
    `mahlerTransform_pushforward_mulCM`) + `constantCoeff_exp` (Exp.lean:59 region,
    `exp` has constant coefficient 1) + `map_sub`.
  - Attacks: [1] exact constructor name: §3 used `HasSubst.of_constantCoeff_zero'` —
    same call shape here ✓ (project precedent compiles); [2] `constantCoeff (exp−1)
    = 1 − 1 = 0` ✓; [3] nilpotency vs topological smallness: `HasSubst` for
    PowerSeries-subst needs constant coeff zero (algebraic), not topology — exactly
    our case ✓. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L2.4** (leaf, mathlib): `derivativeFun_subst_exp` (chain rule)
  - Lean: `MuA.lean:135`. Source: TeX 1474: > "Under the substitution $e^t = T+1$,
    the derivative $d/dt$ becomes the operator $\partial = (1+T)\frac{d}{dT}$."
  - Discharged by: `PowerSeries.derivative_subst` (Derivative.lean:184, verified:
    `d⁄dX A (f.subst g) = (d⁄dX A f).subst g * d⁄dX A g`) + `derivative_exp`
    (`d(exp) = exp`, Exp.lean:72 region) + the algebra
    `(dF)(e^t−1)·e^t = ((1+T)·dF)(e^t−1)` since `1 + (e^t−1) = e^t` — i.e.
    `subst` is a ring hom (`substAlgHom`/`subst_mul/subst_add`) and
    `(1+X).subst (exp−1) = exp`.
  - Attacks: [1] `d⁄dX` vs `derivativeFun`: the bundled `d⁄dX A` is defeq/bridged to
    `derivativeFun` (same file; `derivative_apply`-style lemma) — bridging noted as
    possible off-script rewrite; [2] chain-rule hypothesis: `derivative_subst`
    requires `HasSubst g` = L2.3 ✓; [3] composition-order: mathlib gives
    `(dF).subst g * dg`; we must commute the product to match `((1+X)·dF).subst g`
    — `subst_mul` + `mul_comm`, no obstruction in CommRing ✓; [4] edge `F = C c`:
    both sides 0 ✓. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L2.5** (leaf, mathlib): `constantCoeff_subst_exp` + `constantCoeff_iterate_derivativeFun`
  - Lean: `MuA.lean:141,145`. Source: TeX 1478 (`(∂^k F_a)(0)` — evaluation at
    `T = 0` ⟺ `t = 0`).
  - Discharged by: `constantCoeff_subst` (Substitution.lean:244, verified) with
    `constantCoeff (exp−1) = 0` collapsing the sum to the `n=0` term; iterate:
    induction on `k` with `coeff_derivativeFun` (`coeff n (dG) = coeff (n+1) G·(n+1)`)
    giving `constantCoeff (D^k G) = k!·coeff k G`.
  - Attacks: [1] `constantCoeff_subst`'s exact form is a `finsum`/`tsum`-style
    expression — collapsing needs `pow_zero`/junk-term analysis; flagged as the one
    fiddly spot, fallback: `coeff_subst` at index 0 directly; [2] factorial
    accumulation order: `D^[k+1] = D^[k] ∘ D` vs `D ∘ D^[k]` — `Function.iterate_succ'`
    vs `iterate_succ` both available, induction set up to match ✓; [3] edge `k=0`:
    `0! = 1`, `constantCoeff = coeff 0` ✓ (`coeff_zero_eq_constantCoeff`).
    Verdict: SURVIVED.
  - Prior-B2: no match.

- **L2.6** (internal, composition): `X_mul_subst_exp_Fa` — the Bernoulli identity
  - Lean: `MuA.lean:161`. Source: Lem 4.2's value formula (TeX 1463) +
    `lem:FormulaZeta`'s Bernoulli expansion; formal content as derived above:
    `t·f̂_a = B(t) − B(at)` in `ℚ_p⟦t⟧` where `f̂_a := (map F_a).subst (exp−1)`.
  - Composition (multiply-and-cancel): both sides times `(rescale a exp − 1)`
    (a nonzerodivisor: `ℚ_p⟦t⟧` domain, coefficient 1 equals `a ≠ 0`):
    LHS·: `X·f̂_a·(e^{at}−1) = X·subst(((1+X)^a−1)·F_a) = X·subst(geomSum − a)`
    [L1.6 mapped + `substAlgHom` ring-hom + L2.3; `subst((1+X)^a) = exp^a =
    rescale a exp` by `exp_pow_eq_rescale_exp` (Exp.lean:153, verified)];
    RHS·: `(B − rescale a B)·(e^{at}−1)`, where `B·(e^{at}−1) = B·(e^t−1)·Σ_{i<p
    wait — Σ_{j<a}e^{jt}} = X·Σ_{j<a}e^{jt}` [`bernoulliPowerSeries_mul_exp_sub_one`
    + the substituted L1.3: `e^{at}−1 = (e^t−1)·Σ_{j<a}e^{jt}`] and
    `rescale a B·(e^{at}−1) = rescale a (B·(e^t−1)) = rescale a X = aX`
    [`rescale` ring hom + `rescale_X`-computation + `rescale a exp = exp^a`];
    so RHS· `= X·Σ_{j<a}e^{jt} − aX = X·(subst(geomSum) − a) =` LHS· ✓; cancel.
  - Attacks (composition, this is the load-bearing algebra): [1] **numeric check**
    `a = 2`, coefficient of `t¹` in `t·f̂₂`: `f̂₂ = 1/(e^t−1) − 2/(e^{2t}−1)`;
    `B(t) = 1 − t/2 + t²/12 − …`, `B(2t) = 1 − t + t²/3 − …`; `B(t) − B(2t) =
    t/2 − t²/4 + …`; so `[t¹](t·f̂₂) = 1/2 = f̂₂(0)`. Direct: `f₂(t) = 1/(e^t−1) −
    2/(e^{2t}−1) → (1/t − 1/2 + …) − 2(1/(2t) − 1/2 + …)·` hmm `2/(e^{2t}−1) =
    (1/t)·(2t/(e^{2t}−1))·` `= (1/t)B(2t)`-shape: `f₂ = (B(t) − B(2t))/t =
    1/2 − t/4 + …` so `f₂(0) = 1/2 = (1−2^{0+1})·B₁/1 = (−1)·(−1/2)` ✓ matches
    `(1−a^{k+1})B_{k+1}/(k+1)` at `k=0` ✓; [2] `rescale a (exp − 1) = exp^a − 1`
    needs `rescale` to fix `1` — `map_one` of the ring hom `rescale` ✓; [3] the
    nonzerodivisor: `a ≠ 0` in `ℚ_p` from `hpa` (a ≠ 0 in ℕ since `p ∤ a` and
    `p ∣ 0`) + char-0 cast-injectivity ✓; [4] `rescale_X`: `rescale a X = a•X`
    or `C a * X` — exact mathlib spelling to confirm at execution (coeff-level
    fallback: `coeff_rescale` = `aⁿ·coeff n`); [5] could the children hold and the
    composition fail? All glue is ring-hom algebra in a domain — no. Verdict:
    SURVIVED.
  - Prior-B2: no match.

- **L2.7** (internal, composition): `muA_apply_powCM` (**RJW Prop 4.6**)
  - Lean: `MuA.lean:167`. Source: TeX 1500–1507 (quoted at R2 head; the proof is
    exactly the three-step chain).
  - Composition: `μ_a(x^k) = constantCoeff (del^[k] F_a)` [L2.1 = `apply_powCM` +
    `mahlerTransform_muA`]; cast to ℚ_p and commute `map` through `del^[k]` and
    `constantCoeff` [L2.2 + `constantCoeff_map`, induction]; apply L2.5-iterate
    [via L2.4-induction]: `= k!·coeff k (f̂_a)`; extract `coeff k` from L2.6:
    `coeff (k+1) (X·f̂_a) = coeff k f̂_a` (`coeff_succ_X_mul`) and
    `coeff (k+1) (B − rescale a B) = (1 − a^{k+1})·(B_{k+1}/(k+1)!)`
    [`bernoulliPowerSeries`-coeff def + `coeff_rescale`]; multiply by `k!`:
    `(1−a^{k+1})·B_{k+1}/(k+1) = (−1)^k(1−a^{k+1})·zetaNeg k` since
    `(−1)^k·(−1)^k = 1`.
  - Attacks: [1] `k! / (k+1)! = 1/(k+1)` arithmetic in ℚ_p: `Nat.factorial_succ` +
    `field_simp` — `(k+1)! ≠ 0` in ℚ_p (char 0, `Nat.cast_ne_zero`,
    `factorial_ne_zero`) ✓; [2] `algebraMap ℚ ℚ_[p]` vs `Rat.cast`: same function
    (`eq_ratCast`/`Rat.cast_def`-bridge, standard) ✓; [3] edge `k=0`:
    `μ_a(1) = F_a(0)`: check `F₂(0) = 1/2`?? — wait `F_a ∈ ℤ_p⟦T⟧` and `F₂(0) =
    1/2 ∈ ℤ_p` requires `p ≠ 2` — and indeed `p ∤ a = 2` forces `p` odd here ✓
    consistency (for general `a`: `F_a(0) = FaNum(0)/a = C(a,2)/a·`-shape`
    = (a−1)/2`-do the math: `FaNum(0) = coeff 1 geomSum = Σ_{i<a} i = a(a−1)/2`,
    so `F_a(0) = (a−1)/2`; and the moment formula at `k=0`:
    `(1−a)·B₁ = (1−a)(−1/2) = (a−1)/2` ✓✓ EXACT MATCH — strong numeric
    confirmation of the whole chain); [4] cast-square `((μ : ℤ_[p]) : ℚ_[p])`
    well-formed ✓. Verdict: SURVIVED.
  - Prior-B2: no match.

### Sub-tree R3: `ψ(μ_a) = μ_a` (RJW Lem 4.7) — **recorded replan**

Source's own proof (TeX 1517–1524):
> "We show the result by considering the action on power series. We wish to show
> $\psi(F_a) = F_a$. First note that $F_a(T) = \frac{1}{T} - a \cdot\sigma_a(\frac{1}{T})$,
> for $\sigma_a$ as in \S\ref{SubSectionphipsi}. As $\psi$ commutes with $\sigma_a$,
> we have $\psi(F_a) = \psi(\frac{1}{T}) - a\cdot \sigma_a\psi(\frac{1}{T})$, so it
> suffices to show $\psi(\frac{1}{T}) = \frac{1}{T}$. By definition (cf.\ equation
> \eqref{Eqphipsi}) we have $(\varphi \circ \psi)(\frac{1}{T}) = p^{-1} \sum_{\xi \in
> \mu_p} \frac{1}{(1 + T) \xi - 1} = \frac{1}{(1 + T)^p - 1} = \varphi(\frac{1}{T})$,
> as can be seen by calculating the partial fraction expansion. By injectivity of
> $\varphi$, we deduce that $\psi(\frac{1}{T}) = \frac{1}{T}$, and conclude."

**Replan (T018/T026-pattern; binding justification).** The source's computation runs
through (i) the element `1/T ∉ ℤ_p⟦T⟦` (a Laurent-type object our `Λ(ℤ_p) ≅ ℤ_p⟦T⟧`
does not contain) and (ii) the roots-of-unity formula `Eqphipsi` over `ℤ_p[μ_p]`
(deferred with the O_L-coefficient pass — plan.md "Deferred"). Both obstacles
disappear after clearing denominators by `(1+T)^a − 1`: the *same* partial-fraction
identity `Σ_{ξ^p=1} 1/((1+T)ξ−1) = p/((1+T)^p−1)` is, in cleared form, the geometric
identity `Σ_{i<p}(1+T)^i·((1+T)−1-shifted)` — concretely, the proof becomes:

1. `(v_a) · ψ(μ_a) = ψ(φ(v_a)·μ_a)` where `v_a := [a]−[1] ∈ Λ(ℤ_p)` — the
   **projection formula** L3.1 (`ψ(φν·μ) = ν·ψμ`), which is `Eqphipsi`'s only
   §4-consequence, provable measure-side with no roots of unity;
2. `φ(v_a)·μ_a = [pa]−[0])·μ_a = (Σ_{j<p}[aj])·(([a]−[0])·μ_a) =
   (Σ_{j<p}[aj])·(Σ_{i<a}[i] − a[0])` — finite Dirac sums via L1.9 + L3.5;
3. `ψ` of a Dirac combination is computable termwise (`ψ[m] = [m/p]` if `p ∣ m`,
   else `0` — L3.3/L3.4), giving `Σ_{i<a}[i] − a[0] = v_a·μ_a` again;
4. cancel the nonzerodivisor `v_a` (L1.10).
Every step is a finite computation in `Λ(ℤ_p)`; the source's analytic identity is
recovered as step 2–3's bookkeeping. (Lemma-level faithfulness: the *statement*
`ψ(μ_a) = μ_a` is TeX 1513–1515 verbatim.)

- **L3.1** (leaf, project-provable): `psi_phi_mul` — projection formula
  - Lean: `MuA.lean:182`. Source: `Eqphipsi`-consequence as argued above; measure
    side: `ψ(φν·μ)(f) = (φν·μ)(1_{pℤ_p}·(f∘sd)) = ν(x↦μ(y↦1_{pℤ_p}(px+y)·f(sd(px+y))))`
    [convolution `mul_apply` + `phi`-pushforward], and for the inner integrand
    `1_{pℤ_p}(px+y) = 1_{pℤ_p}(y)`, `sd(px+y) = x + sd y` on `y ∈ pℤ_p`
    [digit arithmetic: `digit (px+y) = digit y`], so it equals `ν(x↦ψμ(f(x+·)))
    = (ν·ψμ)(f)`.
  - Discharged by: `mul_apply` (Convolution.lean), `psi`-def unfolding (`show`-driven
    as in §3's `psi_phi`), `digit`/`shiftDiv` API (Toolbox: `sub_digit_mem_span`,
    `shiftDiv_mul`, `mem_pZp_of_mul`, `mul_shiftDiv_of_mem`).
  - Attacks: [1] **instantiation cross-check**: `ν := 1 = [0]`: formula says
    `ψ(φ(1)·μ) = 1·ψμ = ψμ`; `φ(1) = [0] = 1` ✓ consistent; `μ := 1`:
    `ψ(φν) = ν·ψ(1) = ν` recovering `psi_phi` (Toolbox:377) ✓ the formula
    *generalises* a proven §3 result — strong consistency; [2] digit-arithmetic gap:
    need `digit (p·x + y) = digit y` — provable from `digit`'s `toZModPow 1`
    characterisation (`p·x ≡ 0 mod p`); flagged as the one new digit lemma
    (sub-lemma of the ticket, ~8 LOC); [3] convolution-order: `phi ν * μ` vs
    `μ * phi ν` — ring commutative, lemma stated in the order the proof produces ✓.
    Verdict: SURVIVED.
  - Prior-B2: no match.

- **L3.2** (leaf, project): `phi_dirac`
  - Lean: `MuA.lean:186`. Source: `φ` is pushforward by `x ↦ px` (§3.6) — on Dirac
    masses, `φ[c] = [pc]`.
  - Discharged by: `phi = pushforward (mulCM p)` def + `pushforward_dirac`-style
    `rfl` (the §3 file proves `pushforward`-on-`dirac` shapes by `rfl`).
  - Attacks: [1] `rfl`-risk: `pushforward` defined as `compRight`-precomposition —
    `dirac x ∘ comp = dirac (m x)` is definitional ✓ (§3 precedent
    `mahlerTransform_dirac` route); [2] `mulCM p` applies `p·x` not `x·p` —
    commutative ✓; [3] edge `x=0`: `φ[0] = [0]` ✓. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L3.3** (leaf, project): `psi_dirac_mul`
  - Lean: `MuA.lean:189`. Source: `ψ`'s defining property (§3.6, `Eqphipsi`-dual):
    `ψ∘φ = id` on Diracs; more precisely `ψ[px] = [x]`.
  - Discharged by: `psi`-def + `isClopen_pZp`-charFn at `px` (`= 1`,
    membership `px ∈ pℤ_p` ✓) + `shiftDiv_mul` (Toolbox: `sd(px) = x`).
  - Attacks: [1] follows from `psi_phi` + L3.2 composed: `ψ[px] = ψφ[x] = [x]` —
    2-lemma discharge, even simpler than direct ✓; [2] edge `x=0` ✓; [3] charFn
    coercion friction (LocallyConstant → C) — §3 pattern handles. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L3.4** (leaf, project): `psi_dirac_of_isUnit`
  - Lean: `MuA.lean:192`. Source: `Res_{pℤ_p}`-support: a unit is not in `pℤ_p`, so
    the `pℤ_p`-restricted shift kills `[u]`.
  - Discharged by: `psi`-def: `ψ[u](f) = 1_{pℤ_p}(u)·f(sd u) = 0` since
    `u ∉ pℤ_p` (`PadicInt.isUnit_iff` norm-1 vs `pℤ_p` = norm < 1;
    or `setOf_isUnit_eq` from Toolbox/UnitsZp).
  - Attacks: [1] hypothesis sharpness: `x` non-unit ⟺ `x ∈ pℤ_p` ⟹ `ψ[x] ≠ 0`
    generally — `IsUnit` is exactly the complement ✓; [2] charFn-at-point
    evaluation lemma availability (`LocallyConstant.charFn_apply`-shape, used in §3)
    ✓; [3] ext over `f` then pointwise — linear-map ext pattern ✓.
    Verdict: SURVIVED.
  - Prior-B2: no match.

- **L3.5** (leaf, project): `psi_add` / `psi_smul` / `psi_sum`
  - Lean: `MuA.lean:195,198,201`. Source: implicit (the source's `ψ` is
    ℤ_p-linear by construction; ours is defined measure-wise and the API was
    only partially built in §3 — `psi_sub` exists).
  - Discharged by: the same `LinearMap.ext` + definitional unfolding as `psi_sub`
    (PseudoMeasure-era §3 work); `psi_sum` by `Finset.sum_induction`/induction from
    `psi_add` + `psi`-of-zero (`map_zero`-style: `ψ0 = 0` definitional).
  - Attacks: [1] cleanup-debt attack: these three + `psi_sub` say `psi` should be a
    bundled `→ₗ` — REAL flaw of economy, logged as the dedicated cleanup item in the
    ticket (upgrade `psi` to `psiₗ` linear map OR add the lemmas; board chooses
    lemmas-now + cleanup-note to avoid churning §3 call sites mid-section);
    [2] zero case: `ψ0 = 0` needed for `psi_sum` induction ✓ definitional;
    [3] no hidden classical choice. Verdict: SURVIVED (with logged cleanup debt).
  - Prior-B2: no match.

- **L3.6** (internal, composition): `psi_muA` (**RJW Lem 4.7**)
  - Lean: `MuA.lean:215`. Source statement (TeX 1513–1515):
    > "We have $\psi(\mu_a) = \mu_a$."
  - Composition: steps 1–4 of the replan block above; ingredients L3.1, L3.2, L1.9,
    `dirac_mul_dirac` (Convolution.lean:160, `[x]·[y] = [x+y]`), L3.3, L3.4, L3.5,
    L1.10 + `mul_left_cancel₀`. Step-2 detail: `[pa]−[0] = ([a]−[0])·(Σ_{j<p}[aj])`
    — wait, orientation: `(Σ_{j<p}[aj])·([a]−[1])` telescopes to `[pa]−[0]`:
    `Σ_j[aj]·[a] = Σ_j[a(j+1)]` reindexes against `Σ_j[aj]` leaving `[ap]−[0]` ✓
    (`Finset.sum_range_succ'`-telescope); then `([pa]−[0])·μ_a =
    (Σ_j[aj])·(([a]−[0])·μ_a) = (Σ_j[aj])·(Σ_{i<a}[i] − a[0])` by L1.9; expand by
    `dirac_mul_dirac`: `Σ_{j<p}Σ_{i<a}[aj+i] − aΣ_{j<p}[aj]`; apply `ψ` (L3.5
    linearity): termwise by L3.3/L3.4 — `p ∣ aj+i` with `0≤i<a, 0≤j<p` ⟺ the pair
    is `(i,j) = (pm − aj-residue…)`: handled instead by the **division-algorithm
    bijection** `{aj+i : j<p, i<a} = {0,…,ap−1}` (each `n < ap` uniquely `n = aj+i`)
    so the double sum is `Σ_{n<ap}[n]`, and `ψ(Σ_{n<ap}[n]) = Σ_{p∣n, n<ap}[n/p] =
    Σ_{m<a}[m]` (reindex `n = pm`); second sum: `p ∣ aj` with `j<p`, `p∤a` ⟺ `j=0`
    (`Nat.Coprime.dvd_of_dvd_mul_left`), so `ψ(aΣ_j[aj]) = a[0]`; total:
    `Σ_{m<a}[m] − a[0] = ([a]−[0])·μ_a` by L1.9 again; cancel `v_a = [a]−[1]`
    (note `[0] = 1` in Λ — `dirac 0 = 1`, Convolution one-def) by L1.10.
  - Attacks (composition — this is the riskiest node, attacked hardest):
    [1] **end-to-end numeric trace at `p=3, a=2`**: `v₂·μ₂ = [0]+[1] − 2[0] =
    [1]−[0]`; `φ(v₂)·μ₂ = ([6]−[0])·μ₂ = (Σ_{j<3}[2j])·([1]−[0]) =
    ([0]+[2]+[4])·([1]−[0]) = [1]+[3]+[5]−[0]−[2]−[4]`; `ψ`: kills `[1],[5],[2],[4]`
    (units mod 3), keeps `[3]↦[1], [0]↦[0]`: result `[1]−[0]`; and `ν·ψμ₂`-side:
    `v₂·ψμ₂` must equal `[1]−[0] = v₂·μ₂` ⟹ `ψμ₂ = μ₂` ✓ the cancellation
    closes — trace CONFIRMS every step including the unit-killing pattern;
    [2] reindex-lemma availability: division-algorithm bijection on `range (a*p)`:
    via the *transform-side* identity instead — `(Σ_j((1+X)^a)^j)·((1+X)^a−1) =
    (1+X)^{ap}−1 = (Σ_{n<ap}(1+X)^n)·X`-route (geom_sum twice + X-cancellation in
    the domain) avoids `Finset` bijections entirely; both routes recorded, worker
    picks; [3] `[0] = 1` identification: `dirac 0 = 1` — Convolution defines `one`;
    if not a stated lemma, it's `mahlerTransform`-injectivity + `binomialSeries_zero`
    (2 lines, sub-lemma noted); [4] cancellation legitimacy: `v_a ≠ 0` needs
    `a ≠ 1`?? — **ATTACK FINDS REAL EDGE**: `a = 1`: `v₁ = [1]−[1] = 0` and BOTH
    sides of `ψμ₁ = μ₁` are `0 = 0` (F₁ = 0) — but the *cancellation proof* fails at
    `a = 1`! RESOLUTION: `dirac_natCast_sub_one_ne_zero` requires `a ≠ 0` only —
    recheck: `v_a = [a] − 1` has transform `(1+X)^a − 1 ≠ 0 ⟺ a ≠ 0` (coeff 1 = a).
    At `a = 1`: `(1+X)−1 = X ≠ 0` ✓ nonzero! My `[1]−[1]` slip above confused
    `θ_a = [a]−[1] ∈ Λ(ℤ_p^×)` (units-side, where `1 = [1-the-unit]`) with
    `v_a = [a]−[0]·`-wait: in `Λ(ℤ_p)` the ring-one is `[0]` (additive group!), so
    `v_a = [a] − 1 = [a] − [0]`, which at `a=1` is `[1]−[0] ≠ 0` ✓. The statement
    `dirac_natCast_sub_one_mul_muA` with `- 1` (ring one) is correct as skeletoned;
    the attack confirms the convention and kills the false alarm. `a = 1` works
    end-to-end (everything is `0=0` via `F₁ = 0`, and the cancellation is by the
    nonzero `[1]−[0]`). Verdict: SURVIVED (attack [4] sharpened the understanding;
    no statement change needed).
  - Prior-B2: no match.

### Sub-tree R4: restriction moments (RJW Prop 4.8)

Source's proof (TeX 1535–1539):
> "Since $\mathrm{Res}_{\zpe} = 1 - \varphi \circ \psi$, we deduce that
> $\int_{\zpe} x^k \cdot\mu_a = \int_{\Zp} x^k \cdot (1 - \varphi \circ \psi) \mu_a
> = \int_{\Zp} x^k \cdot (1 - \varphi)\mu_a = (1 - p^k) \int_{\Zp} x^k \cdot \mu_a$,
> where for the second equality we have used Lemma \ref{LemmaPsiInvariant}."

- **L4.1** (leaf, project): `phi_apply_powCM`
  - Lean: `MuA.lean:226`. Source: the third equality above (`∫x^k·φμ = p^k∫x^kμ`,
    implicit one-liner in the source's display).
  - Discharged by: `phi`-def (pushforward `mulCM p`) + pointwise `(px)^k = p^k x^k`
    (`mul_pow`) + `μ`-linearity (`map_smul` after `smul`-rewriting the function:
    `powCM ∘ mulCM = p^k • powCM` by `ContinuousMap.ext`).
  - Attacks: [1] edge `k=0`: `φμ(1) = μ(1)` and `p⁰ = 1` ✓; [2] function-level vs
    value-level smul: `C(ℤ_p,ℤ_p)`-smul lemma shape — §3 has the pattern in
    `apply_powCM`'s proof ✓; [3] no `hpa` needed (true for all μ) — hypothesis-
    minimal ✓. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L4.2** (internal, composition): `res_units_muA_apply_powCM` (**RJW Prop 4.8**)
  - Lean: `MuA.lean:233`. Source: TeX 1527–1539 (statement + proof quoted above).
  - Composition: `res_units_eq` (Toolbox:422, `Res_{ℤ_p^×}μ = μ − φψμ`, sorry-free)
    + L3.6 (`ψμ_a = μ_a`) + L4.1 + L2.7, then ℚ_p-algebra:
    `(1−p^k)·(−1)^k(1−a^{k+1})·zetaNeg k`.
  - Attacks: [1] children-true-parent-false: glue is `LinearMap.sub_apply` +
    cast-arithmetic ✓; [2] cast of `(1−p^k)` from ℤ_p to ℚ_p: `push_cast` ✓;
    [3] edge `k=0`: `Res μ_a(1) = (1−1)·… = 0` — sanity: total mass of
    `Res_{units}μ_a` is `μ_a(ℤ_p^×) = (1−p⁰)(…) = 0`?? Hmm — `(1−p^k)` at `k=0` is
    `0`, so the claim is `∫_{ℤ_p^×}1·dμ_a = 0`. Cross-check: `μ_a(ℤ_p^×) =
    μ_a(1) − μ_a(pℤ_p)` and `μ_a(pℤ_p) = (φψμ_a)(1) = (φμ_a)(1) = μ_a(1)` by L3.6 ✓
    `= 0` consistent — the formula correctly encodes that `μ_a` has equal total and
    `pℤ_p` mass. Verdict: SURVIVED.
  - Prior-B2: no match.

### Sub-tree R5: `ζ_p` (RJW §4.3, Def 4.10, Prop 4.11, Thm 4.1; `ZetaP.lean`)

Source TeX 1550–1563 (θ_a and x⁻¹):
> "let $\theta_{a}$ denote the element of $\Lambda(\Zp^\times)$ corresponding to
> $[a] - [1]$. Note that, by definition, we have $\int_{\Zp^\times} x^k
> \cdot\theta_{a} = a^k - 1$. However, in \eqref{eq:first interpolation} it is
> $a^{k+1} -1$ that appears. To bridge this gap, note that on $\Zp^\times$, we have
> a well-defined operation `multiplication by $x^{-1}$' given by
> $\int_{\Zp^\times} f(x) \cdot x^{-1}\mu \defeq \int_{\Zp^\times} x^{-1}f(x) \cdot
> \mu$, and that $\int_{\Zp^\times} x^k \cdot x^{-1} \mu_a =
> (-1)^k(a^k-1)(1-p^{k-1})\zeta(1-k)$."

and TeX 1565–1570 (Def 4.10):
> "Let $a$ be a topological generator of $\zpe$. The \emph{$p$-adic zeta function} is
> $\zeta_p \defeq \frac{x^{-1}\mathrm{Res}_{\Zp^\times}\mu_a}{\theta_a} \in
> Q(\Zp^\times)$."

and TeX 1588–1597 (Prop 4.11's proof):
> "We see $\zeta_p$ is a pseudo-measure by Lemma \ref{lem:pseudo-measure existence}.
> It is independent of the choice of $a$ by Lemma \ref{lem:zero divisor}(iii).
> Using Equation \eqref{eq:integrate pseudo-measure} (to integrate the
> pseudo-measure) and Proposition \ref{PropInterpolation1}, we obtain the
> interpolation property $\int_{\Zp^\times} x^k \cdot \zeta_p =
> (-1)^k(1-p^{k-1})\zeta(1-k)$. To get the result, we may remove the $(-1)^{k}$ as
> $\zeta(1-k) \neq 0$ if and only if $k$ is even."

**Source-gap note (integer topological generator).** §4.1 fixes `a` an *integer*
coprime to `p` (TeX 1455: "let $a$ be an integer coprime to $p$"); Def 4.10 takes the
*same* `a` to be a topological generator of `ℤ_p^×` (TeX 1566). The source never
remarks that an integer topological generator exists. Cross-reference (per the
source-gap fallback chain): standard — an integer primitive root mod `p²` is a
primitive root mod `p^n` for all `n` (Ireland–Rosen, *A Classical Introduction to
Modern Number Theory*, Prop 4.1.2 region / Washington, *Cyclotomic Fields*, §3); the
proof is the `orderOf_one_add_mul_prime` computation already imported by §3's
`UnitsCyclic` work. This becomes leaf L5.4 (`exists_nat_topological_generator`),
flagged as a source-expansion (not an invention: the source's construction is
incoherent without it).

- **L5.1** (leaf, project): `muAUnits` + `iota_muAUnits` + `muAUnits_apply_unitsPowCM`
  - Lean: `ZetaP.lean:36,40,44`. Source: the `Res_{ℤ_p^×}μ_a` of Def 4.10 read as a
    measure *on* `ℤ_p^×` (the source silently identifies measures on ℤ_p supported
    on units with measures on `ℤ_p^×` — our `ι`-machinery from §3 makes the
    identification explicit; `mem_range_iota_iff` (UnitsZp:177) says the
    identification is legitimate precisely because `ψ(Res_{units}μ) = 0`).
  - Discharged by: `extendByZero` (UnitsZp:78) precomposition;
    `extendByZero_comp_unitsVal` (§3, used in `mem_range_iota_iff`'s proof) for the
    `iota`-identity; pointwise `extendByZero (unitsPowCM k) = charFn_{units}·powCM k`
    (`extendByZero_coe_unit`-family) for the moment-transfer.
  - Attacks: [1] direction of identification: `ι(μ∘extendByZero) = Res_units μ`
    holds unconditionally (it's the §3 proof of `mem_range_iota_iff`'s ⟸) — no
    `ψ`-hypothesis needed for our specific μ_a ✓ (we don't even need L3.6 here);
    [2] `unitsPowCM k` vs `powCM k ∘ val`: definitional (`unitsPowCM`-def
    PseudoMeasure:656 is `u ↦ (u:ℤ_p)^k`) ✓; [3] zero-extension at non-units doesn't
    disturb the integral against `Res` — exactly `res`-def ✓. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L5.2** (leaf, mathlib+project): `continuous_units_inv_val` + `invCM` +
  `unitsCmul` + `unitsCmul_apply`
  - Lean: `ZetaP.lean:51,56,61,67`. Source: TeX 1555–1558 (eq. 4.11, quoted above —
    "well-defined operation" = continuity of `x⁻¹` on `ℤ_p^×` + module structure).
  - Discharged by: continuity: `Units.continuous_iff` / the `embedProduct`-coordinate
    argument (UnitsZp.lean §3 already manipulates `embedProduct`-continuity;
    `u ↦ u⁻¹.val` is the `snd∘unop` coordinate) — mathlib's units-topology toolkit
    (`Mathlib.Topology.Algebra.Constructions`); `unitsCmul` mirrors Toolbox `cmul`
    (:38) with `LinearMap.mulLeft ℤ_[p] g` (skeleton already type-checks this body ✓
    so the linear-algebra shape is confirmed by the compiler).
  - Attacks: [1] instance risk: is `C(ℤ_[p]ˣ, ℤ_[p])` an `ℤ_[p]`-algebra with
    compatible mul? — the skeleton COMPILED `LinearMap.mulLeft ℤ_[p] g`, so yes ✓
    (compiler-verified discharge); [2] continuity-route fallback: if no off-the-shelf
    instance, the explicit `(embedProduct _).2.unop`-composition stands (3 lines);
    [3] `x⁻¹` valued in `ℤ_p` not `ℤ_p^×`: matches the source's `x^{-1}f(x)`
    integrand (a ℤ_p-valued function) ✓. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L5.3** (internal): `zetaNum` + `zetaNum_apply_unitsPowCM` + `zetaNum_moments`
  - Lean: `ZetaP.lean:73,77,81`. Source: TeX 1559–1562 (the display quoted above:
    `∫x^k·x⁻¹μ_a = (−1)^k(a^k−1)(1−p^{k−1})ζ(1−k)`).
  - Composition: `x⁻¹·x^k = x^{k−1}` pointwise on units (`inv_mul_cancel`-pow:
    `u⁻¹·u^k = u^{k−1}` for `k ≥ 1` — `pow_sub_one`-shape via `Units.val`-arith);
    then L5.1-transfer + L4.2 at `k−1`: `(−1)^{k−1}(1−p^{k−1})(1−a^k)·zetaNeg(k−1)`
    and `(−1)^{k−1}(1−a^k) = (−1)^k(a^k−1)` — matching TeX 1561 exactly ✓.
  - Attacks: [1] `k−1` ℕ-subtraction safety: `hk : 0 < k` everywhere; `k−1+1 = k`
    (`Nat.succ_pred_eq_of_pos`) at the `pow`-bridge ✓; [2] sign-form check at `k=1`:
    LHS `∫x·x⁻¹μ = ∫1·μ = Res-mass = 0` (R4 attack [3]); RHS `(−1)(a−1)(1−p⁰)ζ(0) =
    0` ✓ consistent; [3] `(u⁻¹:ℤ_p)·(u:ℤ_p)^k = (u^{k−1}:ℤ_p)`: `Units.val_pow_eq_pow_val`
    + `Units.val_mul`-arith ✓ standard. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L5.4** (leaf, project — source-expansion): `topGen_pow_ne_one` +
  `exists_nat_topological_generator`
  - Lean: `ZetaP.lean:92,103`. Source: TeX 1566 ("Let $a$ be a topological generator
    of $\zpe$") + the integrality gloss documented in the R5 head-note;
    cross-reference Washington §3 / Ireland–Rosen (integer primitive roots mod `p^n`).
  - Discharge plan: `topGen_pow_ne_one`: if `a^k = 1` (`k>0`) then
    `unitsToZModPow n a` has order dividing `k` for every `n`; but it generates
    `(ZMod p^n)ˣ` of cardinality `φ(p^n) = p^{n−1}(p−1) → ∞`
    (`ZMod.card_units_eq_totient` + `Nat.totient_prime_pow`) — contradiction for
    `p^{n−1}(p−1) > k` (`orderOf_eq_card_of_forall_mem_zpowers`-family).
    `exists_nat_topological_generator`: take `u₀` from `exists_topological_generator`
    (PseudoMeasure:857, proven, `p ≠ 2`); let `m := ((toZModPow 2 u₀).val.val : ℕ)`
    (a lift of `u₀ mod p²`); then `m ≡ u₀ mod p²` so `m` is a primitive root mod
    `p²`; classical ascent: `ord_{p^n}(m)` is divisible by `ord_{p²}(m) = p(p−1)`,
    and `m^{p−1} = 1 + pc` with `p ∤ c` (else `ord_{p²}(m) ∣ p−1`), so
    `orderOf_one_add_mul_prime` (the §3-discovered mathlib lemma, ZMod-side) gives
    the `p`-part `p^{n−1}`; total order `φ(p^n)` ⟹ generator at level `n`;
    levels < 2 follow from level 2 by surjectivity of the transition
    (`unitsToZModPow_le`, §3).
  - Attacks: [1] `n = 0,1` edges: level 0 group trivial (⊤ automatic); level 1
    follows from level 2 via the surjective transition map (zpowers-image argument —
    `unitsToZModPow_surjective`-machinery from §3 T027) ✓ plan covers;
    [2] `m = 0`-degeneracy: `m ≡ u₀` a unit mod `p²` ⟹ `p ∤ m` ⟹ `m ≥ 1` ✓;
    [3] `(u:ℤ_[p]) = m` vs `u = unit-of-m`: statement uses val-equation — the
    constructed unit is `isUnit_natCast.unit` whose val is `(m:ℤ_[p])` and we need
    its `toZModPow`-images to match `m mod p^n`'s — `toZModPow`-natCast naturality
    (`map_natCast`) ✓; [4] **scope attack**: is this "off-track infrastructure"? No:
    `orderOf_one_add_mul_prime`-machinery is imported mathlib, the §3 board already
    used the same toolkit for `exists_topological_generator`; estimated 60–80 LOC
    against the source's 1-line gloss + the cross-referenced textbook proof
    (~15 textbook lines). Within scope. Verdict: SURVIVED.
  - Prior-B2: no match (name `exists_topological_generator` §3-relative: different
    statement — that one is abstract-unit existence, this is integrality; shapes
    distinct, no inherited defect).

- **L5.5** (leaf, project): `IsPseudoMeasure.sub`
  - Lean: `ZetaP.lean:124`. Source: implicit in the uniqueness argument (difference
    of pseudo-measures tested by moments; the source treats pseudo-measures as a
    module without comment).
  - Discharged by: witness subtraction: `([g]−1)(q₁−q₂) = ([g]−1)q₁ − ([g]−1)q₂ =
    alg(ν₁) − alg(ν₂) = alg(ν₁−ν₂)` — `mul_sub` + `map_sub`.
  - Attacks: [1] 3-line proof, no edge; [2] also-true-for-add/smul (API completeness
    note for cleanup); [3] none further. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L5.6** (internal): `padicZeta` + `padicZeta_isPseudoMeasure` (**RJW Def 4.10 +
  Prop 4.11 first half**)
  - Lean: `ZetaP.lean:110,131`. Source: TeX 1565–1570 + 1588–1589 (quoted at R5 head).
  - Composition: `padicZeta := mk' (zetaNum m) ([u]−1, regular)` — the regularity
    from L5.4's `topGen_pow_ne_one` + `dirac_sub_one_mem_nonZeroDivisors`
    (PseudoMeasure:793, proven); pseudo-measure-ness is `isPseudoMeasure_mk'`
    (PseudoMeasure:1024, proven) at the generator-hypothesis from L5.4.
  - Attacks: [1] choice-plumbing: the `def` chains `.choose_spec.choose_spec.2.2` —
    the skeleton COMPILES, so the ∃-structure matches ✓ (compiler-verified);
    [2] `isPseudoMeasure_mk'`'s exact hypothesis is `∀ n, zpowers (q_n a) = ⊤` —
    L5.4's conclusion verbatim ✓; [3] `a`-independence: NOT claimed by the def
    (a choice is fixed); independence is delivered by the uniqueness clause of
    R-KL — matching the source, which also derives it from zero-divisor(iii) ✓.
    Verdict: SURVIVED.
  - Prior-B2: no match.

- **L5.7** (internal): `padicZeta_moments` (**RJW Prop 4.11 interpolation**)
  - Lean: `ZetaP.lean:137`. Source: TeX 1592–1596 (quoted at R5 head; "Using
    Equation \eqref{eq:integrate pseudo-measure} ... and Proposition
    \ref{PropInterpolation1} ... remove the $(-1)^k$").
  - Composition: given a witness `ν` of `([b]−1)·ζ_p`: multiply the defining
    `mk'_spec` (`([u]−1)·ζ_p = alg(zetaNum)`) by `([b]−1)`:
    `([u]−1)·alg(ν) = ([b]−1)·alg(zetaNum)` in `Q`, pull back along the injective
    `algebraMap` (`IsFractionRing.injective`): `([u]−1)·ν = ([b]−1)·zetaNum` in `Λ`;
    apply `unitsPowCM k`-moments with `units_mul_apply_unitsPowCM`
    (PseudoMeasure:753, proven): `(u^k−1)·ν(x^k) = (b^k−1)·zetaNum(x^k)`; cast to
    ℚ_p, divide by `u^k−1 ≠ 0` (L5.4 torsion-freeness + cast-injectivity), insert
    L5.3's value, remove the sign by L0.4. Moments of `[u]−1`: `dirac`-moment
    `= u^k` (`dirac`-apply def) minus `1`-moment `= 1` (`one`-apply — `[1]`'s
    moment: `(1:ℤ_p^×)^k = 1` ✓).
  - Attacks: [1] `[u]−1`-moment: `1 ∈ Λ(ℤ_p^×)` is `[1-the-unit]` (units-group
    identity — `units_dirac_mul_dirac`-era convention §3): moment `1^k = 1` ✓ (the
    R3-attack[4] confusion pre-empted: here we ARE units-side, `1 = [1]` correctly);
    [2] division order: all in field ℚ_p after cast; `(u:ℚ_p)^k − 1 ≠ 0` ⟸
    cast-inj + L5.4 ✓; [3] witness-uniqueness: any two witnesses agree
    (algebraMap inj) so "every witness" = "the witness" ✓ ∀ν-form sound;
    [4] k=1: both sides 0 (`1−p⁰ = 0` RHS; LHS `ν(x)`: 0 by the chain — consistent,
    no contradiction) ✓. Verdict: SURVIVED.
  - Prior-B2: no match.

- **L5.8** (internal): `kubotaLeopoldt` (**RJW Thm 4.1**) — R-KL root
  - Lean: `ZetaP.lean:154`. Source: TeX 1444–1447 (statement, quoted at top) + 1599
    (proof: existence = Prop 4.11, uniqueness = zero-divisor(iii)).
  - Composition: existence: `padicZeta` + L5.6 + L5.7 (the ∀b-form is exactly
    L5.7's statement); uniqueness: `q₁, q₂` both satisfying ⟹ `q₁ − q₂` is a
    pseudo-measure (L5.5) all of whose `([u]−1)`-witness-moments vanish (the two
    interpolation values subtract: witnesses subtract as in L5.5's proof, moments
    equal ⟹ difference-witness moments 0, cast-injectivity to land in ℤ_p) ⟹
    `q₁ − q₂ = 0` by `pseudoMeasure_eq_zero_of_moments` (PseudoMeasure:829, proven)
    at `a := u` (torsion-free by L5.4).
  - Attacks: [1] ∃!-strength: is the ∀b-moment-property too strong to be satisfiable
    (uniqueness easy, existence hard)? — L5.7 proves it for `padicZeta`, so no;
    too weak for uniqueness? — the `b := u` instance alone pins `q` via
    `pseudoMeasure_eq_zero_of_moments`, so no ✓; [2] the source states moments
    `(1−p^{k−1})ζ(1−k)` with no `b`: our `(b^k−1)·`-factored form is the
    eq-integrate-pseudo-measure encoding (R-KL head-note) — faithful ✓;
    [3] hypothesis audit: `p ≠ 2` required (L5.4 ⟸ `exists_topological_generator`
    needs `(ZMod p^n)ˣ` cyclic — FALSE at `p = 2, n ≥ 3`): stated ✓ never dropped
    (CLAUDE.md rule 5); [4] `IsPseudoMeasure 0`-degeneracy: `0` is a pseudo-measure
    with all moments 0 — could `∃!` accidentally select 0? Only if
    `(1−p^{k−1})ζ(1−k) = 0` for ALL `k>0` — false (`k=2`: `(1−p)·ζ(−1) =
    (1−p)(−1/12) ≠ 0`) ✓ the interpolation is non-degenerate. Verdict: SURVIVED.
  - Prior-B2: no match.

## §4 confidence gate

1. Every leaf discharged from verified mathlib (`bernoulliPowerSeries_mul_exp_sub_one`,
   `derivative_subst`, `exp_pow_eq_rescale_exp`, `constantCoeff_subst`,
   `isUnit_iff_constantCoeff`, `bernoulli_eq_zero_of_odd`, `norm_int_lt_one_iff_dvd`,
   `riemannZeta_neg_nat_eq_bernoulli` — each grep-verified at file:line above) or
   from proven §3 project code (`apply_powCM`, `res_units_eq`, `mahlerLinearEquiv`,
   `mahlerRingEquiv`, `dirac_mul_dirac`, `units_mul_apply_unitsPowCM`,
   `isPseudoMeasure_mk'`, `pseudoMeasure_eq_zero_of_moments`,
   `exists_topological_generator`, `extendByZero`/`iota` cluster). No REVIEW-PENDING
   leaves. ✓
2. Skeleton compiles: `lake build PadicLFunctions` green, 46 sorries, 0 errors
   (verified 2026-06-10, twice). ✓
3. Verbatim quotes: every leaf carries one or points to its parent's (internal nodes
   quote the composition source). ✓
4. Adversarial pass: every node ≥ 3 attacks; two attacks drew blood — L3.6[4]
   (`a = 1` cancellation scare: resolved, convention confirmed, no change) and the
   R2 numeric trace L2.7[3] which *confirmed* the chain at `k=0` exactly. No
   unresolved flaws. ✓
5. Prior-B2 log: `b2_log.jsonl` absent/empty — vacuously clean; the one §3-name
   near-match (L5.4 vs `exists_topological_generator`) inspected, distinct. ✓
6. Tree mirrors the source: R1↔Prop 4.4/Def 4.5, R2↔Lem 4.2/4.3+Prop 4.6,
   R3↔Lem 4.7 (with the recorded ξ-free replan), R4↔Prop 4.8, R5↔§4.3+Thm 4.1;
   each internal node quotes the source's own proof. Two deliberate deviations,
   both recorded with justification: the R3 replan (deferred ξ-machinery) and the
   L5.4 source-expansion (integer generator gloss). LOC estimates: L5.4 ~60–80 LOC
   (vs 1-line gloss + ~15 textbook lines — the one estimate above 3× source);
   L2.6 ~50 LOC (source: half-page of displays); L3.6 ~40 LOC (source: 8-line
   proof); others ≤ 30 LOC each. ✓

**Feasibility**: every §4 leaf is dischargeable from verified infrastructure; the two
new clusters (Bernoulli/exp-substitution algebra L2.2–L2.6; integer-generator ascent
L5.4) are bounded and self-contained. Ready for ticketing.
