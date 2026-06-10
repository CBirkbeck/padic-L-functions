# Ticket Board — §3 Measures and Iwasawa algebras

Source: RJW arXiv:2309.15692, TeX in `.mathlib-quality/references/` (line numbers cited
per ticket). Decomposition + per-leaf verbatim quotes + attack logs:
`.mathlib-quality/decomposition.md` (leaf labels L*.* below refer to it).
Skeleton: all statements already exist as `:= by sorry` in `PadicLFunctions/Measure/`;
**tickets are "fill the sorry at file:decl"** — statements are quoted for convenience
but the skeleton is canonical. `lake build` green at board creation.

## Summary
- Total: 30 work tickets + 12 cleanup tickets
- Open: 1 (CLEANUP-FINAL — unblocked 2026-06-10: this session has lean-lsp) | Done: 41 — ALL PROOF TICKETS DISCHARGED incl. T029 wiring, project sorry-free (2026-06-10)
- Parallel capacity: ~3 workers (per-file chains are sequential; Basic / Toolbox-tail /
  UnitsZp / Fubini chains can overlap once their deps are done)
- Standing conventions: `μ ν : PadicMeasure p _`; "𝓐" = `mahlerTransform`;
  coefficients ℤ_p (generality decisions in `plan.md`); workers record B2 stops in
  `.mathlib-quality/b2_log.jsonl`.

---

### [T001] Prove norm_apply_le + continuous (automatic boundedness)
- **Status**: done (2026-06-09; both lemmas proved: max-attainment + p^n-division; LipschitzWith 1) | **File**: PadicLFunctions/Measure/Basic.lean | **Depends on**: none
- **Parallel**: yes | **Type**: lemma ×2 | **Leaves**: L1.1, L1.2

#### Statement
`PadicMeasure.norm_apply_le (μ : PadicMeasure p X) (f : C(X, ℤ_[p])) : ‖μ f‖ ≤ ‖f‖`
and `PadicMeasure.continuous (μ) : Continuous μ` (Basic.lean:107, 112; `[CompactSpace X]`).

#### Proof sketch
1. `f = 0` case: trivial. Else `‖f‖ = p^{-m}` for some `m : ℕ` (norm values of
   `C(X,ℤ_[p])` lie in `{p^{-k}} ∪ {0}`; sup attained on compact X —
   `ContinuousMap.norm_coe_le_norm` + value-group discreteness, or argue via
   `‖f‖ ≤ p^{-m} ↔ ∀ x, ‖f x‖ ≤ p^{-m}`, which is all that's needed: take the largest
   `m` with `∀ x, ‖f x‖ ≤ p^{-m}`).
2. Divide: each `f x` is divisible by `p^m` (`PadicInt.norm_le_pow_iff_dvd`); define
   `g : C(X, ℤ_[p])` by `g x := ⟨(f x : ℚ_[p]) / p^m, _⟩` (continuity: composition of
   `f` with the isometric `·/p^m` on the closed ball). Then `f = p^m • g`.
3. `μ f = p^m • μ g` (linearity), so `‖μ f‖ ≤ p^{-m}·1 = ‖f‖` (`norm_le_one`).
4. `continuous`: `μ x − μ y = μ (x − y)` + step 3 gives Lipschitz-with-1;
   `LipschitzWith.continuous` (or `AddMonoidHomClass.continuous_of_bound μ 1`).

#### Mathlib lemmas needed
`ContinuousMap.norm_coe_le_norm`, `ContinuousMap.norm_le` (Compact.lean — read),
`PadicInt.norm_le_pow_iff_dvd`, `PadicInt.norm_le_one`, `LipschitzWith.continuous`.

#### Sources
RJW Def. 3.6 + footnote, TeX 759–765 (quote: decomposition L1.1).

#### Generality decision
`X` arbitrary compact (not just profinite) — the proof never uses zero-dimensionality.

---

### [T002] Prove density of locally constant functions
- **Status**: done (2026-06-09; via toZModPow-factorisation: q := toZModPow k ∘ f is locally constant, lift by ZMod.val; error controlled by ker_toZModPow — simpler than the planned cover-disjointification) | **File**: Basic.lean | **Depends on**: none
- **Parallel**: yes (with T001) | **Type**: lemma | **Leaf**: L1.3

#### Statement
`exists_locallyConstant_norm_sub_le (f : C(X, ℤ_[p])) {ε : ℝ} (hε : 0 < ε) :
∃ g : LocallyConstant X ℤ_[p], ‖f - ↑g‖ ≤ ε` (Basic.lean:123; `[CompactSpace X]`).

#### Proof sketch
1. WLOG `ε = p^{-n}` (shrink). Balls `B(c, p^{-n})` in `ℤ_[p]` are clopen
   (ultrametric). The preimages `f ⁻¹' B(f x, p^{-n})` form a clopen cover of X.
2. Finite subcover (`CompactSpace`); disjointify by subtracting earlier members
   (clopen Boolean algebra), giving a finite clopen partition `{V_i}` with
   `f(V_i) ⊆ B(c_i, p^{-n})`.
3. Define `g := ∑ c_i·𝟙_{V_i}` as `LocallyConstant` (piecewise-constant on a finite
   clopen partition: build with `LocallyConstant.ofIsClopen`-style constructors or
   directly: `IsLocallyConstant` of a function constant on each member of a finite
   clopen partition).
4. `‖f − g‖ ≤ p^{-n}`: pointwise, x ∈ V_i ⟹ ‖f x − c_i‖ ≤ p^{-n}.

#### Mathlib lemmas needed
`IsUltrametricDist.isClopen_ball` (or `Metric.isClopen_ball` for ultrametric —
worker locates exact name in `Analysis/Normed/*/Ultra`), `IsCompact.elim_finite_subcover`,
`IsClopen.diff/inter/union`, `LocallyConstant` constructors, `ContinuousMap.norm_le`.

#### Sources
RJW Rem. 3.8, TeX 782–791 (verbatim quote: decomposition L1.3). 8 source lines → ~25 LOC.

#### Generality decision
Stated for compact X and target ℤ_[p]; the proof works for any ultrametric normed
target — note as a "for mathlib, generalise target" comment but do NOT widen now
(cleanup/PR pass decides).

---

### [T003] Prove ext_locallyConstant
- **Status**: done (2026-06-09; eq_of_forall_dist_le + ultrametric norm_add_le_max + T001/T002) | **File**: Basic.lean | **Depends on**: T001, T002 | **Type**: lemma | **Leaf**: L1.4

#### Statement
`ext_locallyConstant {μ ν} (h : ∀ g : LocallyConstant X ℤ_[p], μ ↑g = ν ↑g) : μ = ν`
(Basic.lean:131).

#### Proof sketch
1. `LinearMap.ext f`; fix `f`. By T002 pick `g_n` with `‖f − g_n‖ ≤ p^{-n}`.
2. `‖μ f − ν f‖ = ‖μ(f − g_n) − ν(f − g_n)‖ ≤ max(‖μ (f−g_n)‖, ‖ν (f−g_n)‖) ≤ p^{-n}`
   (T001 + ultrametric `norm_sub_le_max`); let `n → ∞`. Or: `Continuous.ext_on`
   with the dense range of `LocallyConstant.toContinuousMap` (density set form of T002).

#### Mathlib lemmas needed
`IsUltrametricDist.norm_sub_le_max` (or `norm_add_le_max`), `norm_le_zero_iff`,
optionally `Continuous.ext_on` + `DenseRange`.

#### Sources
RJW Rem. 3.8, Eq. (3.1), TeX 787–799.

#### Generality decision
As skeleton.

### [CLEANUP-1] Run /cleanup on PadicLFunctions/Measure/Basic.lean
- **Status**: done (2026-06-09; degraded mode: lean-lsp MCP unavailable this session — mathlib linter set is ON in lakefile and the file builds with zero warnings; axioms standard on all 4 decls; full-tooling pass deferred to CLEANUP-FINAL) | **Depends on**: T003 | **Type**: cleanup
- 3rd proof ticket on the file + final per-file cleanup (T001–T003 complete the file).

---

### [T004] Prove the evaluation formula apply_eq_tsum
- **Status**: done (2026-06-10; HasSum.map through toAddMonoidHom) | **File**: Measure/MahlerTransform.lean | **Depends on**: CLEANUP-1
- **Type**: lemma | **Leaf**: L2.1

#### Statement
`apply_eq_tsum (μ) (f) : μ f = ∑' n, Δ_[1]^[n] (⇑f) 0 * mahlerCoeff p μ n`
(MahlerTransform.lean:62).

#### Proof sketch
1. `PadicInt.hasSum_mahler f : HasSum (fun n ↦ mahlerTerm (Δ_[1]^[n] ⇑f 0) n) f`
   (E := ℤ_[p]; all instances present).
2. Map through μ: μ is a continuous additive map (T001/L1.2) —
   `HasSum.map _ (μ : C(_,_) →+ ℤ_[p])`-style with `PadicMeasure.continuous`.
3. `μ (mahlerTerm a n) = a * μ (mahler n)`: `mahlerTerm_apply`/definition
   (`mahlerTerm a n = (mahler n) • const a`; for E = ℤ_[p] this is `a • mahler n`
   up to `smul_eq_mul` and constant-factoring via `map_smul`). Conclude with
   `HasSum.tsum_eq` + commutativity of the factors.

#### Mathlib lemmas needed
`PadicInt.hasSum_mahler` (MahlerBasis.lean:339), `mahlerTerm_apply` (:256),
`HasSum.map`, `HasSum.tsum_eq`, `map_smul`, `smul_eq_mul`.

#### Sources
RJW Thm. 3.20 proof, TeX 995–998 (quote: decomposition L2.1).

#### Generality decision
ℤ_p coefficients (plan.md §Generality 1).

---

### [T005] Prove mahlerTransform_dirac (𝓐 δ_a = (1+T)^a)
- **Status**: done (2026-06-10; simp with binomialSeries_coeff) | **File**: MahlerTransform.lean | **Depends on**: CLEANUP-1
- **Parallel**: yes (with T004) | **Type**: lemma | **Leaf**: L2.2

#### Statement
`mahlerTransform_dirac (a : ℤ_[p]) : mahlerTransform p (dirac p a) = binomialSeries ℤ_[p] a`
(MahlerTransform.lean:70).

#### Proof sketch
1. `PowerSeries.ext n`; LHS coeff = `dirac p a (mahler n) = Ring.choose a n`
   (`coeff_mahlerTransform` simp + `mahler_apply`).
2. RHS coeff = `Ring.choose a n • (1 : ℤ_[p])` (`binomialSeries_coeff`); finish
   `smul_eq_mul, mul_one`.

#### Mathlib lemmas needed
`PowerSeries.ext`, `binomialSeries_coeff` (PowerSeries/Binomial.lean:50),
`mahler_apply` (MahlerBasis.lean:107).

#### Sources
RJW Ex. 3.16, TeX 968–973.

#### Generality decision
As skeleton.

---

### [T006] Prove ofPowerSeries well-defined + mahlerTransform_ofPowerSeries
- **Status**: done (2026-06-10; summable helper + δ-identity transport) | **File**: MahlerTransform.lean | **Depends on**: T004
- **Type**: def-fields + lemma | **Leaf**: L2.4

#### Statement
Fill `ofPowerSeries.map_add'`, `.map_smul'` (MahlerTransform.lean:85–88) and
`mahlerTransform_ofPowerSeries (g) : mahlerTransform p (ofPowerSeries p g) = g` (:95).

#### Proof sketch
1. Summability of `fun n => Δⁿf(0) * g_n`: `PadicInt.fwdDiff_tendsto_zero f` +
   `‖g_n‖ ≤ 1` ⟹ terms → 0 ⟹ summable
   (`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`).
2. `map_add'`: `fwdDiff_iter_add` pointwise + `tsum_add` (both summable by 1).
   `map_smul'`: `fwdDiff_iter_const_smul` + `tsum_const_smul`-form.
3. For the transform identity: coeff k of LHS = `ofPowerSeries g (mahler k) =
   ∑' n, Δⁿ(mahler k)(0) * g_n`. Key: `Δ_[1]^[n] (mahler k) 0 = if n = k then 1 else 0`.
   Route: `mahler k = mahlerSeries (Pi.single k (1 : ℤ_[p]))` (check by
   `mahlerSeries_apply_nat`-style evaluation on ℕ + `denseRange_natCast.equalizer`,
   mirroring MahlerBasis.lean:344–349), then `fwdDiff_mahlerSeries` (:313). Or
   directly via `fwdDiff_iter_eq_sum_shift` + `fwdDiff_iter_choose_zero` (:332 usage).
4. The tsum collapses to `g_k` (`tsum_ite_eq`-pattern).

#### Mathlib lemmas needed
`fwdDiff_tendsto_zero` (:224), `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`
(:287 usage), `fwdDiff_iter_add`, `fwdDiff_iter_const_smul` (:362, :367 usages),
`fwdDiff_mahlerSeries` (:313), `tsum_add`, `tsum_ite_eq`, `denseRange_natCast`.

#### Sources
RJW Thm. 3.20 proof, TeX 1000–1004 (quote: decomposition L2.4).

#### Generality decision
As skeleton.

### [CLEANUP-2] Run /cleanup on MahlerTransform.lean (cadence)
- **Status**: done (2026-06-10; degraded mode — linters on, zero warnings) | **Depends on**: T006 | **Type**: cleanup (after 3rd ticket on file)

---

### [T007] Prove mahlerTransform_injective + assemble mahlerLinearEquiv
- **Status**: done (2026-06-10; Thm 3.20 linear part sorry-free) | **File**: MahlerTransform.lean | **Depends on**: CLEANUP-2
- **Type**: lemma + def-fields | **Leaves**: L2.3, L2.5

#### Statement
`mahlerTransform_injective` (:77); fill `mahlerLinearEquiv.left_inv/right_inv` (:102).

#### Proof sketch
1. Injectivity: `𝓐μ = 𝓐ν ⟹ ∀ n, μ (mahler n) = ν (mahler n)` (coeff ext) ⟹
   `μ f = ν f` by T004 evaluation formula.
2. `right_inv` = T006. `left_inv`: `ofPowerSeries (𝓐 μ) f = ∑' Δⁿf(0)·μ(mahler n) = μ f`
   by T004 read backwards. `LinearMap.ext`.

#### Mathlib lemmas needed
`PowerSeries.ext_iff`, `LinearMap.ext`; rest internal (T004, T006).

#### Sources
RJW Thm. 3.20, TeX 994–1005.

### [CLEANUP-3] Run /cleanup on MahlerTransform.lean (final)
- **Status**: done (2026-06-10; degraded mode — linters on, zero warnings) | **Depends on**: T007 | **Type**: cleanup

---

### [T008] Transport ring structure: mahlerTransform_mul/one, CommRing laws, mahlerRingEquiv
- **Status**: done (2026-06-10; transport bookkeeping, ring laws via 𝓐-injectivity) | **File**: Measure/Convolution.lean | **Depends on**: T007
- **Type**: instance + lemmas | **Leaf**: L3.1

#### Statement
Fill sorries at Convolution.lean:46–86 (`mahlerTransform_mul`, `mahlerTransform_one`,
all CommRing fields, `mahlerRingEquiv.map_mul'`).

#### Proof sketch
1. `mahlerTransform_mul`: unfold `mul_def`; `mahlerLinearEquiv.apply_symm_apply`.
2. `mahlerTransform_one`: `one_def` + T005 at a = 0 + `binomialSeries_zero`.
3. Each ring law: apply `(mahlerLinearEquiv p).injective`, push through with
   `mahlerTransform_mul`/`map_add`, use the corresponding law in `PowerSeries ℤ_[p]`.
   (E.g. assoc: both sides ↦ `(𝓐μ·𝓐ν)·𝓐ρ = 𝓐μ·(𝓐ν·𝓐ρ)`.)
4. `mahlerRingEquiv.map_mul'` := `mahlerTransform_mul`.

#### Mathlib lemmas needed
`LinearEquiv.apply_symm_apply`, `LinearEquiv.injective`, `binomialSeries_zero`
(PowerSeries/Binomial.lean:78), `mul_assoc/one_mul/...` in PowerSeries.

#### Sources
RJW Rem. 3.11 "by transport of structure", TeX 907–911.

#### Generality decision
Mul/One instances are placed on the project's `PadicMeasure p ℤ_[p]` (= LinearMap dual)
— verified no mathlib instance clash (decomposition L3.1 attack [5]).

---

### [T009] Prove the convolution formula mul_apply
- **Status**: done (2026-06-10; convInner via curry; Chu-Vandermonde on antidiagonal; 𝓐-injectivity replaced the density step — simpler than planned) | **File**: Convolution.lean | **Depends on**: T008, T003
- **Type**: theorem | **Leaf**: L3.2 (KEY)

#### Statement
`mul_apply (μ ν) (f) : (μ * ν) f = μ ⟨fun x => ν (f.comp ⟨fun y => x + y, _⟩), _⟩`
(Convolution.lean:96). First action: replace the two `by sorry` continuity side-terms
in the STATEMENT with real proofs (inner: `f.comp (addLeft x)` continuity is
`by fun_prop`; outer: factor through `ContinuousMap.curry` — define the inner map as
`(f.comp ⟨fun q : ℤ_[p] × ℤ_[p] => q.1 + q.2, by fun_prop⟩).curry`, then the outer
continuity is `ν ∘ continuous-family`, using `PadicMeasure.continuous` (T001) and
continuity of `curry` application; keep the statement's displayed form via a `rfl`
bridge lemma if needed).

#### Proof sketch
1. Both sides are `ℤ_[p]`-linear and 1-bounded in `f` (T001). By Mahler expansion
   (T004 applied to the equality goal, or T003 + density): suffices on `f = mahler n`.
2. LHS at `mahler n` = coeff n of `𝓐μ·𝓐ν` (T008.1 + `coeff_mahlerTransform`,
   `PowerSeries.coeff_mul`) = `∑_{i+j=n} μ(mahler i)·ν(mahler j)` (antidiagonal).
3. RHS: inner function at fixed x: `y ↦ Ring.choose (x+y) n`; Chu–Vandermonde
   `add_choose_eq` (Commute trivial in comm ring): `choose (x+y) n =
   ∑_{ij ∈ antidiagonal n} choose x ij.1 * choose y ij.2`. ν linear over the finite
   sum: inner integral = `∑_{ij} choose x ij.1 * ν (mahler ij.2)`. This is a FINITE
   ℤ_p-combination of `mahler ij.1` applied to x — μ linear: total
   `∑_{ij} μ(mahler ij.1)·ν(mahler ij.2)`. Matches 2.
4. Extension from basis to all f: define both sides as linear maps in f; they agree on
   `mahler n`; every f is the limit of finite Mahler sums (hasSum_mahler) and both
   sides are continuous in f (T001 with explicit norm bounds for the RHS inner map:
   `‖inner(x)‖ ≤ ‖f‖` pointwise) — `Continuous.ext_on`/tsum-swap argument as in T004.

#### Mathlib lemmas needed
`add_choose_eq` (RingTheory/Binomial.lean:519), `PowerSeries.coeff_mul`,
`Finset.antidiagonal` API, `ContinuousMap.curry` (CompactOpen.lean:419), `map_sum`.

#### Sources
RJW Rem. 3.11 display, TeX 908–910 (quote: decomposition R3 substrate).

#### Generality decision
Stated for the additive group ℤ_p only (multiplicative analogue is PseudoMeasure's
`unitsConv`, definitionally).

---

### [T010] Prove dirac_mul_dirac
- **Status**: done (2026-06-10; binomialSeries_add) | **File**: Convolution.lean | **Depends on**: T008
- **Parallel**: yes (with T009) | **Type**: lemma | **Leaf**: L3.3

#### Statement
`dirac_mul_dirac (a b) : dirac p a * dirac p b = dirac p (a + b)` (Convolution.lean:105).

#### Proof sketch
1. Apply `mahlerTransform_injective` (T007); rewrite with T008.1, T005 twice,
   `binomialSeries_add`, T005 backwards.

#### Mathlib lemmas needed
`binomialSeries_add` (PowerSeries/Binomial.lean:60).

#### Sources
RJW Ex. 3.12 + 3.16, TeX 914–920, 968–973.

### [CLEANUP-4] Run /cleanup on Convolution.lean (3rd ticket + final)
- **Status**: done (2026-06-10; degraded mode — linters on, zero warnings) | **Depends on**: T009, T010 | **Type**: cleanup

---

### [T011] Toolbox: mult-by-x ↔ ∂ and moments
- **Status**: done (2026-06-10; mul_choose_eq by ℕ+density; coeff_del helper) | **File**: Measure/Toolbox.lean | **Depends on**: T007
- **Type**: lemma ×2 | **Leaves**: L4.1, L4.2

#### Statement
`mahlerTransform_cmul_X` (Toolbox.lean:46) and `apply_powCM` (:56).

#### Proof sketch
1. Binomial identity over ℤ_p: `x * choose x n = (n+1)·choose x (n+1) + n·choose x n`.
   Prove on ℕ (cast of `Nat.succ_mul_choose_eq`-area arithmetic: source line 1074
   identity), extend by `denseRange_natCast` + continuity (`continuous_choose`).
2. Coefficientwise: `(cmul id μ)(mahler n) = μ(x·choose) = (n+1)μ(mahler(n+1)) + n·μ(mahler n)`;
   `coeff n (del F) = coeff n (F') + coeff n (X·F') = (n+1)F_{n+1} + n·F_n`
   (`coeff_derivativeFun`). `PowerSeries.ext`.
3. `apply_powCM` by induction on k: base `μ(1) = constantCoeff 𝓐μ` (mahler 0 = 1);
   step: `x^{k+1} = x·x^k` ⟹ `μ(pow (k+1)) = (cmul id μ)(pow k)` + step 2 + IH.

#### Mathlib lemmas needed
`coeff_derivativeFun` (PowerSeries/Derivative.lean:46), `Nat.succ_mul_choose_eq`,
`PadicInt.continuous_choose` (MahlerBasis.lean:93), `PadicInt.denseRange_natCast`,
`PowerSeries.constantCoeff`, `Function.iterate_succ_apply'`.

#### Sources
RJW Lem. 3.24 + Cor. 3.25, TeX 1059–1082 (quotes: decomposition L4.1, L4.2).

---

### [T012] Toolbox: clopens and restriction additivity
- **Status**: done (2026-06-10; closedBall + compl; indicator additivity) | **File**: Toolbox.lean | **Depends on**: T001 (only)
- **Parallel**: yes | **Type**: lemma ×3 | **Leaf**: L4.3

#### Statement
`isClopen_pZp` (:121), `isClopen_units` (:138), `res_union` (:73).

#### Proof sketch
1. `{‖x‖ < 1}`: equals `{x : ‖x‖ ≤ p⁻¹}` (value-group discreteness:
   `PadicInt.norm_lt_one_iff_dvd` / `norm_le_pow_iff_dvd`); closed ball clopen in
   ultrametric: closed by continuity of norm, open since ultrametric balls are open
   (`IsUltrametricDist` API).
2. `{IsUnit x} = {‖x‖ = 1}` (`PadicInt.isUnit_iff`) = complement of 1 ⟹ clopen.
3. `res_union`: `charFn (U ∪ V) = charFn U + charFn V` for disjoint clopens
   (`LocallyConstant.coe_charFn` = `Set.indicator U 1`; `Set.indicator_union_of_disjoint`),
   then linearity of `cmul` in g.

#### Mathlib lemmas needed
`PadicInt.isUnit_iff` (:366), `PadicInt.norm_lt_one_iff_dvd`,
`LocallyConstant.coe_charFn` (LocallyConstant/Algebra.lean:94),
`Set.indicator_union_of_disjoint`, `IsClopen.union/compl`.

#### Sources
RJW §3.5.3, TeX 1098–1129.

---

### [T013] Toolbox: shiftDiv and the ψ operator's well-definedness
- **Status**: done (2026-06-10; digit via toZModPow 1 — cleaner than appr as ticket anticipated) | **File**: Toolbox.lean | **Depends on**: T012
- **Type**: def-fields + lemma | **Leaf**: L4.5

#### Statement
Fill `shiftDiv` membership + continuity (:115–117), `shiftDiv_mul` (:125),
`psi.map_add'/map_smul'` (:147–149).

#### Proof sketch
1. Membership: `‖x − appr x 1‖ ≤ p⁻¹` (mathlib `PadicInt.dist_appr_spec`-family at
   RingHoms.lean:695 area — `x ≡ appr x 1 mod p`), so division by p lands in ℤ_p
   (`PadicInt.norm_le_pow_iff_dvd`).
2. Continuity: `x ↦ appr x 1` is locally constant (depends only on `toZMod x`:
   `appr x 1` vs `ZMod.val (toZMod x)` — worker reconciles via `PadicInt.appr_spec 1` +
   `ker_toZMod`; if `appr` proves awkward, REDEFINE shiftDiv with
   `(x − (ZMod.val (PadicInt.toZMod x) : ℤ_[p]))/p` — same function, cleaner: toZMod is
   continuous-to-discrete hence locally constant); then shiftDiv = (x − lc(x))·p⁻¹
   continuous.
3. `shiftDiv_mul`: `toZMod (p*x) = 0` ⟹ digit 0 ⟹ `(px − 0)/p = x`.
4. ψ fields: linearity of f ↦ 𝟙·(f ∘ shiftDiv) + μ linear.

#### Mathlib lemmas needed
`PadicInt.appr_spec`, `PadicInt.ker_toZMod`/`ker_toZModPow` (RingHoms.lean:457),
`ZMod.val_cast_of_lt`, `PadicInt.norm_le_pow_iff_dvd`.

#### Sources
RJW §3.5.5 ψ-definition, TeX 1147–1148.

#### Generality decision
Off-`pℤ_p` values of shiftDiv are irrelevant (cut by indicator); canonical digit choice.

### [CLEANUP-5] Run /cleanup on Toolbox.lean (cadence, after 3rd ticket on file)
- **Status**: done (2026-06-10; degraded mode) | **Depends on**: T013 | **Type**: cleanup

---

### [T014] Toolbox: σ/φ transforms and the φψ identities + Cor. 3.32
- **Status**: done (2026-06-10; general mahlerTransform_pushforward_mulCM lemma covers σ_a AND φ; coeff_subst' + finsum truncation + add_pow; φψ identities pointwise) | **File**: Toolbox.lean | **Depends on**: CLEANUP-5, T009
- **Type**: theorem ×6 | **Leaves**: L4.4, L4.6, L4.7

#### Statement
`mahlerTransform_sigma` (:97), `mahlerTransform_phi` (:106), `psi_phi` (:152),
`phi_psi` (:158), `res_units_eq` (:146), `isSupportedOn_units_iff_psi_eq_zero` (:167).

#### Proof sketch
1. σ/φ transforms (L4.4 route, decomposition): fix n. On ℕ:
   `choose (a*k) n = ∑_{m ≤ n} choose k m * c_{n,m}` with
   `c_{n,m} := coeff n ((binomialSeries a − 1)^m)` — from
   `binomialSeries (a*k) = (binomialSeries a)^k` (iterate `binomialSeries_add` /
   `binomialSeries_nat` for ℕ-powers) + binomial expansion of `(1 + (B−1))^k` +
   order-≥-m truncation (`constantCoeff (B−1) = 0` via `binomialSeries_constantCoeff`).
   Extend to `x ∈ ℤ_p` by density/continuity. Apply μ; identify RHS with
   `coeff_subst` (HasSubst.of_constantCoeff_zero'; `subst` coefficient formula —
   finite by the same order argument).
2. `psi_phi`/`phi_psi`: `LinearMap.ext f`; pointwise function identities
   `𝟙_{pℤ_p}(p*x) = 1`, `shiftDiv (p*x) = x` (T013), exactly the source's two displays
   (TeX 1149–1151). `ContinuousMap.ext` + `mul_comm` plumbing.
3. `res_units_eq`: partition `𝟙_{units} = 1 − 𝟙_{pℤ_p}` (complement clopen sets:
   `isUnit_iff`/`not_isUnit_iff` ↔ norm dichotomy) + `phi_psi`.
4. Cor 3.32: (⇒) ψ-apply to `res_units_eq`-fixed point; `ψ(φ(ψμ)) = ψμ` by `psi_phi`
   ⟹ ψμ = ψμ − ψμ = 0. (⇐) `res_units_eq` with ψμ = 0.

#### Mathlib lemmas needed
`binomialSeries_nat` (:69), `binomialSeries_constantCoeff` (:55),
`HasSubst.of_constantCoeff_zero'` (Substitution.lean:67), `PowerSeries.coeff_subst`
(worker reads Substitution.lean for the exact finsum form), `PadicInt.not_isUnit_iff`
(:385).

#### Sources
RJW §3.5.5, TeX 1133–1167 (verbatim displays quoted in decomposition L4.4/L4.6/L4.7).

### [CLEANUP-6] Run /cleanup on Toolbox.lean (final)
- **Status**: done (2026-06-10; degraded mode — note: `show` style warnings queued for CLEANUP-FINAL) | **Depends on**: T014 | **Type**: cleanup

---

### [T015] Units geometry: CompactSpace ℤ_[p]ˣ + topological instances + unitsValCM
- **Status**: done (2026-06-10; embedProduct closed range; T2 was already a mathlib instance; t.d. via opHomeomorph transfer) | **File**: Measure/UnitsZp.lean | **Depends on**: none
- **Parallel**: yes (anytime) | **Type**: instance + def-field | **Leaf**: L5.3 (+ L5.4 part)

#### Statement
`instance : CompactSpace ℤ_[p]ˣ` (UnitsZp.lean:26), `unitsValCM` continuity (:30).
ALSO: derive/provide `T2Space ℤ_[p]ˣ` and `TotallyDisconnectedSpace ℤ_[p]ˣ` instances
(needed by T019's integral_swap at X = ℤ_[p]ˣ — add them in this file if not inferred).

#### Proof sketch
1. `Units.embedProduct ℤ_[p] : ℤ_[p]ˣ → ℤ_[p] × ℤ_[p]ᵐᵒᵖ` is an embedding (mathlib
   `Units.isEmbedding_embedProduct`). Its range is `{q | q.1 * q.2.unop = 1 ∧
   q.2.unop * q.1 = 1}` — closed (preimage of {1} under continuous maps). Closed in
   compact ⟹ compact; embedding ⟹ `CompactSpace` via `isCompact_range`/
   `IsCompact.of_isClosed_subset` + `CompactSpace.of_isCompact_univ`-style transfer.
2. `unitsValCM`: `Units.continuous_val` (exists as `Units.continuous_val` or
   `continuous_coe`; fallback: `(continuous_fst.comp (Units.isEmbedding_embedProduct).continuous)`).
3. T2/TotDisc: embedding into the T2, totally disconnected `ℤ_[p] × ℤ_[p]ᵐᵒᵖ`
   (products preserve both; `IsEmbedding.t2Space`, subtype/embedding transfer for
   `TotallyDisconnectedSpace` — `IsEmbedding.injective` + `isTotallyDisconnected_of_image`-style).

#### Mathlib lemmas needed
`Units.isEmbedding_embedProduct` (Topology/Algebra/Constructions.lean — read),
`IsClosed.preimage`, `IsCompact.of_isClosed_subset`, `IsEmbedding.t2Space` family.

#### Sources
Implicit in RJW line 747; pure topology.

#### Generality decision
A `CompactSpace Mˣ` instance for `M` compact T2 topological monoid is the right mathlib
generality — note for the PR pass; prove for ℤ_[p] now (instance placement local).

---

### [T016] Units: extendByZero + iota_injective
- **Status**: done (2026-06-10; unitsHomeo via homeoOfEquivCompactToT2; extendByZero glued on clopen cover) | **File**: UnitsZp.lean | **Depends on**: T015, T012
- **Type**: def-fields + lemma | **Leaf**: L5.4

#### Statement
`extendByZero` continuity/linearity + `extendByZero_coe_unit` (:34–43),
`iota_injective` (:54).

#### Proof sketch
1. Continuity of the extension: `{IsUnit x}` clopen (T012); on it the function is
   `g ∘ (partial inverse of val)` — continuity via the closed-embedding of val
   (T015: continuous injective from compact to T2 ⟹ closed embedding
   `Continuous.isClosedEmbedding`) — `IsClosedEmbedding.continuousOn_inv`-style, or
   gluing: `ContinuousOn.if'`-family on the clopen partition (continuousOn each piece,
   pieces clopen ⟹ continuous global).
2. `extendByZero_coe_unit`: `dif_pos` + `IsUnit.unit_spec` injectivity of val.
3. `iota_injective`: if `ιμ = 0` then for any `g : C(ℤ_[p]ˣ, ℤ_[p])`,
   `μ g = μ ((extendByZero g).comp valCM) = (ιμ)(extendByZero g) = 0` — the first
   equality is `extendByZero_coe_unit` (restriction∘extension = id) via
   `ContinuousMap.ext`.

#### Mathlib lemmas needed
`Continuous.isClosedEmbedding` (compact-to-T2), `continuousOn_iff`-gluing or
`IsClopen.continuous_piecewise`-shape lemmas, `dif_pos`, `Units.ext`.

#### Sources
RJW Rem. 3.33, TeX 1169–1172 (verbatim in decomposition L5.4).

---

### [T017] Units: res_iota + mem_range_iota_iff (image = ker ψ)
- **Status**: done (2026-06-10; range ι = ker ψ both directions) | **File**: UnitsZp.lean | **Depends on**: T016, T014
- **Type**: theorem ×2 | **Leaf**: L5.4 (rest)

#### Statement
`res_iota` (:60), `mem_range_iota_iff` (:66).

#### Proof sketch
1. `res_iota`: `(res ι μ) f = μ ((𝟙_{units}·f) ∘ val) = μ (f ∘ val)` since
   `𝟙_{units}(val u) = 1` pointwise.
2. (⇒): given μ = ιν: ψμ = 0 by Cor 3.32 (T014) once `res_units μ = μ` (step 1).
3. (⇐): ψμ = 0 ⟹ μ = res_units μ (T014) ⟹ μ = ι(pushforward-restriction of μ):
   exhibit preimage `ν := μ ∘ extendByZero` (precomposition linear map); check
   `ιν = μ`: `(ιν) f = μ (extendByZero (f ∘ val)) = μ (𝟙_{units}·f) = res μ f = μ f`
   — middle equality: `extendByZero (f∘val) = 𝟙_{units}·f` pointwise (dif split).

#### Mathlib lemmas needed
Internal + `Set.indicator` arithmetic.

#### Sources
RJW Rem. 3.33, TeX 1171–1172.

### [CLEANUP-7] Run /cleanup on UnitsZp.lean (3rd ticket + final)
- **Status**: done (2026-06-10; degraded mode — show-linter warnings queued) | **Depends on**: T017 | **Type**: cleanup

---

### [T018] Fubini: clopen-box decomposition of locally constant functions
- **Status**: done (2026-06-10; REPLANNED per beastmode replan-and-continue: clopen-box decomposition replaced by locally-constant approximation of the CURRIED map — new lemma exists_locallyConstant_norm_sub_le' (general ultrametric target, mathlib PR candidate); the box lemma was dropped as unnecessary, and integral_swap lost its T2/TotallyDisconnected hypotheses. decomposition.md L5.1 superseded accordingly) | **File**: Measure/Fubini.lean | **Depends on**: none
- **Parallel**: yes (anytime) | **Type**: theorem | **Leaf**: L5.1

#### Statement
`locallyConstant_prod_mem_span_boxes` (Fubini.lean:48).

#### Proof sketch
1. `F : LocallyConstant (X×Y) ℤ_p` has finite range (compact domain:
   `LocallyConstant.range_finite`); the fibres `F⁻¹{c}` are clopen, finitely many,
   partition X×Y.
2. Each point of a fibre has a basic clopen box neighbourhood inside it: clopen boxes
   form a basis of X×Y for X, Y compact T2 totally disconnected (clopen sets are a
   basis in each factor — `compact_t2_tot_disc_iff_tot_sep`-family /
   `TopologicalSpace.IsTopologicalBasis.prod` of the clopen bases; worker locates
   modern names, fallback `DiscreteQuotient` route: F factors through a finite discrete
   quotient of X×Y, and discrete quotients of a product are refined by products of
   discrete quotients — `DiscreteQuotient.prod` API if present).
3. Compactness of each fibre: finite box subcover; disjointify boxes to a finite grid:
   take the common refinement of all the X-side and Y-side pieces (finite Boolean
   algebra of clopens), yielding a partition by boxes `A_j × B_k` on which F is
   constant.
4. `F = ∑_{j,k} F(a_jk)·𝟙_{A_j}·𝟙_{B_k}` exactly; each summand is in the generating
   set (charFn comp fst/snd product); conclude `Submodule.sum_mem`.

#### Mathlib lemmas needed
`LocallyConstant.range_finite`, `IsLocallyConstant.isClopen_fiber`,
clopen-basis lemma (worker locates; candidates in `Topology/Separation/*`,
`Topology/Connected/TotallyDisconnected.lean`), `Submodule.sum_mem`, `Finset.sup`/
partition-refinement combinatorics.

#### Sources
Expansion of RJW line 910 "One checks…" via the Rem. 3.8 technique (decomposition L5.1).

---

### [T019] Fubini: integral_swap
- **Status**: done (2026-06-10; swap via finite fibre sums of the locally constant approximation; ultrametric dist_triangle_max closes) | **File**: Fubini.lean | **Depends on**: T018, T002, T001
- **Type**: theorem | **Leaf**: L5.2

#### Statement
`integral_swap` (Fubini.lean:62). Also fill `innerInt`'s continuity sorry (:37):
`x ↦ ν (F.curry x)` is continuous since `F.curry : C(X, C(Y, ℤ_[p]))` (mathlib curry,
compact-open) and ν is continuous (T001) — composition.

#### Proof sketch
1. Both sides linear + 1-bounded in F (T001 twice, `innerInt` norms ≤ ‖F‖).
2. For F in the box-span (T018): expand by linearity to `F = 𝟙_U×𝟙_V`:
   LHS = `μ(𝟙_U·ν(𝟙_V)) = ν(𝟙_V)·μ(𝟙_U)`; RHS symmetric — equal.
3. Locally constant F: T018 + linearity. General F: density on the compact X×Y
   (T002 with X := X×Y) + continuity in F (1): standard ε-argument
   (`Continuous.ext_on` on the dense set of locally constant maps).

#### Mathlib lemmas needed
`ContinuousMap.curry` (CompactOpen.lean:419) + its continuity lemmas
(`ContinuousMap.continuous_curry'`-family), `Continuous.ext_on`, `DenseRange`.

#### Sources
Expansion of RJW Rem. 3.11 "One checks", TeX 910; technique = Rem. 3.8.

### [CLEANUP-8] Run /cleanup on Fubini.lean (final)
- **Status**: done (2026-06-10; degraded mode) | **Depends on**: T019 | **Type**: cleanup

---

### [T020] Λ(ℤ_p^×): unitsConv well-defined + CommRing laws
- **Status**: done (2026-06-10; unitsConv via innerInt; CommRing laws by show-driven defeq + integral_swap for comm) | **File**: Measure/PseudoMeasure.lean | **Depends on**: T019, T015
- **Type**: def-fields + instance | **Leaf**: L5.5

#### Statement
Fill `unitsMulCM` continuity (:38), `unitsConv` fields (:44–47), CommRing fields
(:64–72).

#### Proof sketch
1. `unitsMulCM` continuity: `ContinuousMul ℤ_[p]ˣ` (mathlib units-of-topological-monoid
   instance; worker locates — `Units.instContinuousMul`-shape in
   Topology/Algebra/Constructions or Group/Basic; fallback via embedProduct).
2. `unitsConv` inner-map continuity: rewrite `fun x => ν (f.comp (unitsMulCM x))` as
   `ν ∘ (G.curry)` for `G := f.comp mulCM₂` with `mulCM₂ : C(ℤ_[p]ˣ × ℤ_[p]ˣ, ℤ_[p]ˣ)`
   the multiplication (continuity: ContinuousMul) — same pattern as T009/T019.
   Linearity fields: ν, μ linear.
3. `mul_comm`: `integral_swap` (T019) with `F := f ∘ mul`; note
   `f((x·y)) = f((y·x))` (CommGroup) reconciles the swapped order.
4. `mul_assoc`: both sides = triple integral of `f(xyz)`; two unfoldings + one swap.
5. `one_mul/mul_one`: δ_1 evaluation: inner integral at f.comp(mul 1) = f. Distrib/zero:
   linearity in each slot (μ, ν enter linearly).

#### Mathlib lemmas needed
`ContinuousMap.curry`, units `ContinuousMul` instance, internal T019.

#### Sources
RJW Eq. (3.11), TeX 1173–1175 + Rem. 3.11 "one checks".

#### Generality decision
ℤ_p^×-specific (no `to_additive` gymnastics; plan.md §Generality 4). The convolution
orientation (ν inner) is recorded in `units_mul_def`; §4 pass must quote it.

---

### [T021] Λ(ℤ_p^×): Dirac multiplicativity + degree ring hom
- **Status**: done (2026-06-10; dirac mult is rfl; deg ring hom) | **File**: PseudoMeasure.lean | **Depends on**: T020
- **Type**: lemma + def-fields | **Leaves**: L5.5 (tail), L5.6

#### Statement
`units_dirac_mul_dirac` (:75), `deg` fields (:85–90); `augmentationIdeal` is then
definitional.

#### Proof sketch
1. `(δ_u * δ_v) f = (f ∘ mul_u)(v) = f(u·v)` — unfold unitsConv, two dirac_apply.
2. `deg` fields: map_one: `δ_1(1) = 1`; map_mul: `(μ*ν)(1) = μ(x ↦ ν(1·)) = μ(ν(1)·1)`
   wait — inner: `1.comp (mulCM x) = 1` so inner integral is constant `ν 1`; then
   `μ(const (ν 1)) = ν 1 · μ 1` (pull scalar out: `const c = c • 1`). map_add/zero:
   linearity.

#### Sources
RJW Def. 3.37, TeX 1245–1253.

---

### [T022] Λ(ℤ_p^×): finite-level maps (levelMap cluster)
- **Status**: done (2026-06-10; levelMap ring hom incl. convolution-of-indicators map_mul; fibre clopen; + coefficient/transition/partition lemmas) | **File**: PseudoMeasure.lean | **Depends on**: T020, T003
- **Type**: lemma + def-fields ×2 | **Leaf**: L5.7

#### Statement
`isClopen_unitsToZModPow_fiber` (:107), `levelMap` ring-hom fields (:116–126),
`levelMap_jointly_injective` (:131).

#### Proof sketch
1. Fibre clopen: `unitsToZModPow n` is continuous-to-discrete: it factors through
   `toZModPow n` (kernel = `p^n`-span, RingHoms.lean:457) — preimage of a point under
   a locally constant map. Concretely: `val ⁻¹' (toZModPow n ⁻¹' {lift})`-intersections;
   use `IsLocallyConstant` of toZModPow (`PadicInt.continuous_toZModPow` + discrete).
2. map_one: δ_1 hits only the fibre of 1̄: single = 1. map_add/zero: linearity of μ ↦
   each coefficient. map_mul: `(μ*ν)(𝟙_{c̄-fibre})`: inner function
   `x ↦ ν(𝟙_{c̄}(x·))`; `𝟙_{c̄-fibre}(xy) = ∑_{āb̄=c̄} 𝟙_{ā}(x)𝟙_{b̄}(y)` (coset
   partition identity: for fixed x in the ā-fibre, `xy ∈ c̄-fibre ↔ y ∈ (ā⁻¹c̄)-fibre`);
   expand both sides into `∑_{āb̄=c̄} μ(𝟙_ā)ν(𝟙_b̄)`; match
   `MonoidAlgebra.single_mul_single` summed over the group.
3. Joint injectivity: by T003 (ext on locally constant) it suffices that μ kills every
   `g : LocallyConstant ℤ_[p]ˣ ℤ_[p]`. g factors through level n for some n: the
   fibres of `unitsToZModPow n` form a neighbourhood basis refinement — uniform
   local-constancy on the compact ℤ_[p]ˣ: g is constant on `u·(1 + p^nℤ_p)`-cosets for
   n large (Lebesgue-number argument via the ultrametric on val-image, or:
   `DiscreteQuotient`/`LocallyConstant.factors`-API). Then g = ∑ values·fibre-indicators,
   and `levelMap n μ = 0` gives `μ g = 0`.

#### Mathlib lemmas needed
`PadicInt.ker_toZModPow` (RingHoms.lean:457), `PadicInt.toZModPow` continuity
(`continuous_toZModPow` — locate), `MonoidAlgebra.single` API
(`single_mul_single`, `Finsupp.ext`), `Fintype.sum` reindexing (`Fintype.sum_equiv`
along `(·*c̄⁻¹)`).

#### Sources
RJW TeX 888–892 (quote in decomposition L5.7); the cofinal-chain restriction is
recorded there (attack [4]).

### [CLEANUP-9] Run /cleanup on PseudoMeasure.lean (cadence, after 3rd ticket on file)
- **Status**: done (2026-06-10; degraded mode) | **Depends on**: T022 | **Type**: cleanup

---

### [T023] Zero-divisor lemma (i)
- **Status**: done (2026-06-10; descPochhammer X-divisibility + ψ-fixes-δ₀ argument, ξ-free as planned) | **File**: PseudoMeasure.lean | **Depends on**: CLEANUP-9, T017, T014, T011
- **Type**: theorem | **Leaf**: L5.8

#### Statement
`eq_zero_of_forall_unitsPowCM_eq_zero` (:147).

#### Proof sketch (ξ-free refinement recorded in decomposition L5.8)
1. Set `M := iota μ ∈ Λ(ℤ_p)`. For n ≥ 1: `n! • (M (mahler n)) = M (descPochhammer-CM)`
   (`descPochhammer_eq_factorial_smul_choose` + continuity/density to pass from the
   polynomial identity to the continuous-map level — evaluate: both sides are μ of
   explicit continuous maps; the identity holds pointwise on ℤ_p).
2. `descPochhammer ℤ n` has constant coefficient 0 (root at 0) for n ≥ 1:
   `descPochhammer_eval_zero`-shape ⟹ as a polynomial `X ∣ descPochhammer` ⟹
   pointwise `desc(x) = x·q(x)` with q ∈ ℤ_p[X]. Pull back along val:
   `M(desc∘) = μ((x·q(x))|_{units}) = ∑ q_k·μ(x^{k+1}|_units) = 0` by hypothesis
   (finite sum, all exponents ≥ 1).
3. `n! ≠ 0` in the domain ℤ_[p] ⟹ `M (mahler n) = 0` ∀ n ≥ 1 ⟹ `𝓐M = c·1` constant.
4. `𝓐(c·δ_0) = c` (T005, a = 0) ⟹ `M = c·δ_0` (T007 injectivity).
5. `ψM = 0`: `res_iota` (T017) + Cor 3.32 (T014). But `ψ(δ_0) = δ_0` (direct
   evaluation: `𝟙_{pℤ_p}(0)·f(shiftDiv 0) = f 0`). So `c·δ_0 = 0 ⟹ c = 0 ⟹ M = 0`.
6. `iota_injective` (T016) ⟹ μ = 0.

#### Mathlib lemmas needed
`descPochhammer_eq_factorial_smul_choose` (RingTheory/Binomial.lean:390),
`Polynomial.dvd_iff_isRoot`, `descPochhammer` eval lemmas
(`descPochhammer_eval_zero` — locate/derive), `Nat.cast_injective`-domain facts,
`smul_eq_zero`.

#### Sources
RJW Lem. 3.36(i) proof, TeX 1228–1229 (verbatim in decomposition L5.8, with the two
recorded refinements).

---

### [T024] Zero-divisor lemma (ii) + measures are pseudo-measures
- **Status**: done (2026-06-10; multiplicative moments + two-sided nonZeroDivisors) | **File**: PseudoMeasure.lean | **Depends on**: T023
- **Type**: theorem ×2 | **Leaves**: L5.9, L5.10

#### Statement
`mem_nonZeroDivisors_of_forall_unitsPowCM_ne_zero` (:153), `isPseudoMeasure_algebraMap` (:177).

#### Proof sketch
1. For `λ` with `μ*λ = 0`: `(μ*λ)(x^k) = μ(x ↦ λ((x·)^k)) = μ(x ↦ x^k·λ(pow k)) =
   μ(pow k)·λ(pow k)` — middle: `(xy)^k = x^k y^k` + λ-linearity pulls the scalar
   `x^k` out (constant-in-y factor). So `λ(pow k) = 0 ∀k>0` (h: μ-moments ≠ 0,
   domain ℤ_p) ⟹ λ = 0 (T023). Symmetric side by `mul_comm` (T020) —
   `mem_nonZeroDivisors_iff`.
2. `isPseudoMeasure_algebraMap`: witness ν := `(δ_g − 1)·μ`; `map_mul (algebraMap …)`.

#### Mathlib lemmas needed
`mem_nonZeroDivisors_iff`, `mul_pow`, `map_mul`.

#### Sources
RJW Lem. 3.36(ii) proof, TeX 1232–1234 (verbatim in decomposition L5.9).

---

### [T025] Zero-divisor lemma (iii) for pseudo-measures
- **Status**: done (2026-06-10; via (i) + IsLocalization.map_units) | **File**: PseudoMeasure.lean | **Depends on**: T024
- **Type**: theorem | **Leaf**: L5.11

#### Statement
`pseudoMeasure_eq_zero_of_moments` (:185).

#### Proof sketch
1. `hq a` gives ν₀ with `([a]−1)·q = algebraMap ν₀`. h (at each k, ν₀) gives
   `ν₀(pow k) = 0 ∀ k>0` ⟹ ν₀ = 0 (T023).
2. So `([a]−1)·q = 0` in the fraction ring; `[a]−1` maps to a unit-like regular
   element: by `dirac_sub_one_mem_nonZeroDivisors`-content — DON'T depend on T028;
   instead inline: `(δ_a −1)(pow k) = a^k − 1 ≠ 0` (ha) ⟹ T024 ⟹ regular in Λ;
   regular elements map to regular elements of the localization
   (`IsLocalization.map_nonZeroDivisors`-shape; in a fraction ring, the image of a
   nonZeroDivisor is invertible: `IsFractionRing.isUnit_map_nonZeroDivisor`-shape —
   worker locates: `IsLocalization` API gives `IsUnit (algebraMap _ _ x)` for
   `x ∈ nonZeroDivisors` in FractionRing). Hence q = 0.

#### Mathlib lemmas needed
`IsLocalization.map_units` (FractionRing at nonZeroDivisors), `IsFractionRing.injective`.

#### Sources
RJW Lem. 3.36(iii) proof, TeX 1236–1240 (verbatim in decomposition L5.11).

### [CLEANUP-10] Run /cleanup on PseudoMeasure.lean (cadence, after 6th ticket on file)
- **Status**: done (2026-06-10; degraded mode) | **Depends on**: T025 | **Type**: cleanup

---

### [T026] Topological generator of ℤ_p^× (p odd)
- **Status**: done (2026-06-10; REPLAN NOTE: instead of lifting a primitive root, took the nested-clopen-generator-sets + compactness route — no Teichmüller, no order arithmetic; surjectivity lift via canonical representative) | **File**: PseudoMeasure.lean | **Depends on**: T022
- **Parallel**: yes (with T023–T025) | **Type**: theorem | **Leaf**: L5.12

#### Statement
`exists_topological_generator (hp2 : p ≠ 2) : ∃ a : ℤ_[p]ˣ, ∀ n,
Subgroup.zpowers (unitsToZModPow p n a) = ⊤` (:206). The `p ≠ 2` hypothesis was added
by the adversarial pass (decomposition L5.12 — `(ZMod 8)ˣ` is not cyclic); statement
already amended and building.

#### Proof sketch
1. Read `Mathlib/RingTheory/ZMod/UnitsCyclic.lean` in full first — it proves
   `isCyclic_units_of_prime_pow` by exhibiting generator structure (`1 + p` of order
   `p^n` etc.); extract/reuse: there is `g : (ZMod (p^2))ˣ` generating, and the file's
   machinery shows a unit that generates mod p² generates mod every p^n (odd p) —
   if not stated, prove via order computation: `orderOf a mod p^n = (p−1)·p^{n−1}`
   when a generates mod p² (`orderOf_one_add_mul_prime` is in the file).
2. Lift to `ℤ_[p]ˣ`: pick `x : ℤ_[p]` with `toZModPow 2 x = g` (surjectivity of
   `toZModPow` — derive via `appr`: `toZModPow n (appr-based lift) = given`); `x` is a
   unit (`isUnit_iff`: unit mod p ⟹ ‖x‖ = 1). Set `a := x.unit`.
3. For each n: image generates since order matches the group order
   (`Subgroup.eq_top_of_card_le`-shape / `orderOf` = card).

#### Mathlib lemmas needed
`isCyclic_units_of_prime_pow` + neighbours (UnitsCyclic.lean:190–231, read),
`ZMod.card_units_eq_totient`, `PadicInt.isUnit_iff`, `Subgroup.zpowers_eq_top`-API.

#### Sources
RJW Lem. 3.38 parenthetical, TeX 1257–1258; proof line 1265 "As p is odd".

---

### [T027] Augmentation ideal is principal (finite levels + compactness)
- **Status**: done (2026-06-10; finite-level telescoping + ker-deg decomposition; inverse limit step realised as Banach–Alaoglu-style compactness of the functional space Π_f ℤ_p with closed linearity+level conditions; levelMap_jointly_injective closes) | **File**: PseudoMeasure.lean | **Depends on**: T026, T022, T021
- **Type**: theorem | **Leaf**: L5.14 (cluster L5.14a–c)

#### Statement
`augmentationIdeal_eq_span (ha : ∀ n, zpowers (unitsToZModPow p n a) = ⊤) :
augmentationIdeal p = Ideal.span {dirac p a − 1}` (:212).

#### Proof sketch (sub-leaves in decomposition L5.14a–c)
1. (⊇) `deg (δ_a − 1) = 0`: T021.
2. (L5.14a) Finite cyclic group ring: for `C = ⟨g⟩` finite, every `single c 1 − 1 ∈`
   ideal gen by `single g 1 − 1` (telescoping `[g^k]−1 = ([g]−1)·∑_{i<k}[g^i]`), hence
   any `∑ c_a[a]` with `∑ c_a = 0` is `∑ c_a([a]−1) ∈ ([g]−1)`. State as a private
   lemma in the file (`MonoidAlgebra`, ~20 LOC).
3. (L5.14b) For μ ∈ I: level-n witness ν_n with `levelMap n (([a]−1)·?) = levelMap n μ`
   — from 2 applied to `levelMap n μ` (which has degree 0: deg factors through levels
   — small bridge lemma `deg = (MonoidAlgebra-augmentation) ∘ levelMap n`, T021/T022)
   + surjectivity of levelMap onto the group ring (hit `single ḡ c` by
   `c • δ_{lift ḡ}`; linear combinations).
4. (L5.14c) Compactness: the solution sets
   `S_n := {ν : Λ | levelMap n ((δ_a −1)*ν − μ) = 0}` are nonempty (3), nested after
   refinement (levelMap compatibility: `levelMap n` factors through `levelMap (n+1)` —
   bridge lemma via coset refinement), and closed-compact in the topology of pointwise
   evaluation on coset indicators: realise Λ ↪ `Π_{n, ḡ} ℤ_[p]` (countable product of
   compacts, `μ ↦ (μ(fibre-indicators))`), image closed (the additivity + ext
   constraints are closed conditions; uses T003-ext to identify the image), S_n
   closed therein. `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`
   gives ν ∈ ⋂ S_n; `levelMap_jointly_injective` (T022) ⟹ `(δ_a −1)*ν = μ`.
   NOTE (honest size estimate): step 4 is the heaviest single step of the board
   (~80–120 LOC with the embedding bookkeeping); the source compresses it to "In the
   inverse limit we see" (line 1269). If the worker finds the product-embedding
   formalisation heavier than estimated, B2-stop with findings rather than redesign.

#### Mathlib lemmas needed
`MonoidAlgebra.single` algebra, `geom_sum_mul`-shape telescoping,
`IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`
(Topology/Compactness/Compact.lean:336), `isCompact_pi_infinite`/Tychonoff
(`isCompact_univ_pi`), closed-set lemmas.

#### Sources
RJW Lem. 3.38 proof, TeX 1264–1272 (verbatim in decomposition L5.14).

---

### [T028] Pseudo-measure existence and shape (Lem. 3.38 + converse)
- **Status**: done (2026-06-10; mk'_spec' + eq_mk'_iff_mul_eq; regularity from torsion-free moments) | **File**: PseudoMeasure.lean | **Depends on**: T027, T024
- **Type**: theorem ×3 | **Leaves**: L5.13, L5.15

#### Statement
`dirac_sub_one_mem_nonZeroDivisors` (:231), `isPseudoMeasure_mk'` (:224),
`isPseudoMeasure_iff_exists` (:246).

#### Proof sketch
1. L5.13: `(δ_a − 1)(pow k) = a^k − 1 ≠ 0` (ha) + T024(ii).
   Bridge lemma (used by T025/§4 too): a topological generator satisfies
   `∀ k>0, a^k ≠ 1` — if `a^k = 1` then the image of `zpowers a` mod p^n has ≤ k
   elements ∀n, contradicting `ha n` for `card (ZMod p^n)ˣ > k`.
2. `isPseudoMeasure_mk'`: for g: `δ_g − 1 ∈ I = ([a]−1)` (T027 + deg(δ_g−1) = 0) ⟹
   `δ_g − 1 = ν·(δ_a −1)`; then `(δ_g−1)·mk'(μ, δ_a−1) = ν·(δ_a−1)·mk'(…) = ν·μ ∈ Λ`
   (`IsLocalization.mk'_spec`).
3. `iff_exists`: (⇐) is 2 (+ algebraMap case T024). (⇒): hq at g := a gives ν with
   `([a]−1)q = ν`; then `q = mk'(ν, δ_a−1)` (`IsLocalization.eq_mk'_iff_mul_eq`).

#### Mathlib lemmas needed
`IsLocalization.mk'_spec`, `IsLocalization.eq_mk'_iff_mul_eq`, `ZMod.card_units`.

#### Sources
RJW Lem. 3.38 proof + lines 1284–1285 (verbatim in decomposition L5.15).

### [CLEANUP-11] Run /cleanup on PseudoMeasure.lean (final)
- **Status**: done (2026-06-10; degraded mode — show-linter warnings queued for CLEANUP-FINAL) | **Depends on**: T028 | **Type**: cleanup

---

### [T029] Wire blueprint refs for §3 (Measures chapter)
- **Status**: done (2026-06-10; 20 nodes wired to project/mathlib decls, blueprint builds, site re-rendered; deferred nodes — §3.1 prelims, projlim description, ξ-formulas, §3.7 — left unwired per plan.md) | **File**: PadicLFunctionsBlueprint/Chapters/Measures.lean
- **Depends on**: none (can run anytime; refs to sorry-decls render "in progress")
- **Type**: blueprint wiring (no proofs)

#### Description
Add `(lean := "...")` references to the Measures-chapter Verso nodes for the now-stated
declarations (map: `p-adic-measure` ↦ `PadicMeasure`; `mahler-transform`/
`iwasawa-isomorphism` ↦ `PadicMeasure.mahlerTransform`/`PadicMeasure.mahlerRingEquiv`;
toolbox nodes ↦ `cmul/res/sigma/phi/psi` lemmas; `pseudo-measure` ↦
`PadicMeasure.IsPseudoMeasure`; zero-divisor/augmentation nodes ↦ T023–T028 decls;
node-by-node mapping from chapter labels — read the chapter file and decomposition.md).
Rebuild `lake build PadicLFunctionsBlueprint` and re-render `./scripts/ci-pages.sh`;
verify referenced names resolve (build fails on stale names — fix immediately).
Keep `(lean := …)` OFF the nodes whose statements stay roadmap-only (projlim
description, ξ-formulas, locally analytic — per plan.md Deferred).

---

### [CLEANUP-FINAL] Run /cleanup-all on the whole project
- **Status**: open — BLOCKED on tooling (requires a session with lean-lsp MCP connected for /cleanup-all's per-decl golf workers; the mathlib linter set already runs green on every build; known cosmetic debt: a handful of `show`-should-be-`change` style warnings) | **Depends on**: all above | **Type**: cleanup-all
- Then `/pre-submit` when the user wants a checkpointed milestone.

---

## Dependency quick-view

```
T001 T002 → T003 → CL1 → T004 T005 → T006 → CL2 → T007 → CL3
                                                    ├→ T008 → T009,T010 → CL4
                                                    └→ T011
T012 → T013 → CL5 → T014 → CL6        (T012 needs only T001)
T015 → T016 → T017 → CL7              (T016 also needs T012; T017 needs T014)
T018 → T019 → CL8                     (T019 needs T002, T001; T018 free)
T019,T015 → T020 → T021,T022 → CL9 → T023 → T024 → T025 → CL10
T022 → T026;  T026,T022,T021 → T027;  T027,T024 → T028 → CL11
T029 free;  everything → CLEANUP-FINAL
```

Cadence audit: Basic 3 tickets/1 cleanup ✓; MahlerTransform 4/2 ✓; Convolution 3/1 ✓;
Toolbox 4/2 ✓; UnitsZp 3/1 ✓; Fubini 2/1 ✓; PseudoMeasure 9/3 ✓; final /cleanup-all ✓.
Total proof tickets 28 → ⌈28/3⌉ = 10 ≤ 11 per-file cleanups + CLEANUP-FINAL ✓.

---

# §4 — Kubota–Leopoldt (TeX 1440–1609) — added 2026-06-10

## §4 Summary
- Tickets: T030–T039 (10 proof/def) + CLEANUP-ALL-2 + CLEANUP-KL-1/2
- Open: 0 | Done: 13 (all §4 tickets discharged 2026-06-10)
- Skeleton: `PadicLFunctions/KubotaLeopoldt/{ZetaValues,ZetaValuesComplex,MuA,ZetaP}.lean`,
  46 sorries, builds green (2026-06-10)
- Decomposition: `.mathlib-quality/decomposition.md` §4 (leaves L0.1–L5.8, all gated)
- **Standing rules (CLAUDE.md, binding on every ticket below)**: each ticket's
  Definition-of-Done includes (i) the **Blueprint** step — wire/adjust the named
  chapter node(s) in `PadicLFunctionsBlueprint/Chapters/KubotaLeopoldt.lean` in the
  same session, `lake build PadicLFunctionsBlueprint` green; (ii) the **Cleanup**
  step — `/cleanup` (single-declaration mode; degraded mode + note if lean-lsp absent)
  on the new declarations immediately, before marking done; (iii) verification bar:
  build green, zero sorry in the ticket's declarations, `#print axioms` ⊆
  {propext, Classical.choice, Quot.sound}; (iv) checkpoint commit.

### [T030] Rational zeta values `zetaNeg` + complex bridge
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/ZetaValues.lean, ZetaValuesComplex.lean
- **Depends on**: none
- **Parallel**: yes (with T031)
- **Type**: lemmas (4 sorries: `zetaNeg_zero`, `zetaNeg_eq_zero_of_even`,
  `neg_one_pow_mul_one_sub_pow_mul_zetaNeg`, `zetaNeg_eq_riemannZeta`)
- **Statement**: in skeleton (ZetaValues.lean:21,25,36; ZetaValuesComplex.lean:18).
- **Proof sketch** (decomposition L0.1–L0.4):
  1. `zetaNeg_zero`: `simp [zetaNeg, bernoulli_one]; norm_num`.
  2. `zetaNeg_eq_zero_of_even`: `bernoulli_eq_zero_of_odd (h.add_one) (by lia)`;
     conclude `zetaNeg k = ±0/(k+1) = 0` by `simp [zetaNeg]`.
  3. `neg_one_pow_mul_one_sub_pow_mul_zetaNeg`: `rcases k`: `k = 1` → factor
     `1 − q⁰ = 0`; `k` even → `Even.neg_one_pow`; `k ≥ 3` odd → step 2 kills
     `zetaNeg (k−1)`. Parity split via `Nat.even_or_odd k`.
  4. `zetaNeg_eq_riemannZeta`: open mathlib's `riemannZeta_neg_nat_eq_bernoulli`
     (HurwitzZetaValues.lean) at `n := k`; `push_cast [zetaNeg]; ring`.
- **Mathlib lemmas**: `bernoulli_one`, `bernoulli_eq_zero_of_odd` (Bernoulli.lean:217),
  `Even.neg_one_pow`, `Odd.neg_one_pow`, `riemannZeta_neg_nat_eq_bernoulli` (verified
  by file-grep; exact argument form to confirm via hover at execution).
- **Sources**: RJW TeX 1455 (value formula), 1596 (sign removal). Quotes in
  decomposition L0.1–L0.4.
- **Generality**: `zetaNeg : ℕ → ℚ` (pure rational — no p); sign lemma over arbitrary
  `q : ℚ` (more general than the `p`-instance needed).
- **Blueprint**: none of the §4 nodes is *this* content alone (kl-values-of-zeta
  stays unwired pending §2 Mellin theory — see decomposition R-KL head-note; record
  the unwired-rationale as a comment on the node).
- **Cleanup**: `/cleanup` ZetaValues.lean + ZetaValuesComplex.lean immediately after.
- **Progress**:
  - 2026-06-10: DONE — 4 declarations proven (zetaNeg_zero, zetaNeg_eq_zero_of_even,
    neg_one_pow_mul_one_sub_pow_mul_zetaNeg, zetaNeg_eq_riemannZeta); build green;
    axioms = [propext, Classical.choice, Quot.sound] (verified). Off-script: Nat.Odd.sub_odd
    (ℕ-sub version, not Odd.sub_odd). Blueprint: unwired-rationale comment added to
    kl-values-of-zeta node, blueprint builds. Cleanup: degraded mode (no lean-lsp) —
    proofs are 1–6-line minimal forms, naming/docstrings audited by hand; revisit in
    a tooled session via CLEANUP-FINAL.

### [T031] `F_a`, `μ_a` and the characterising identity
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/MuA.lean
- **Depends on**: none
- **Parallel**: yes (with T030)
- **Type**: def-API (9 sorries: `PadicInt.isUnit_natCast_of_not_dvd`,
  `constantCoeff_geomSum`, `geomSum_mul_X`, `isUnit_geomSum`, `X_mul_FaNum`,
  `geomSum_mul_Fa`, `one_add_X_pow_sub_one_mul_Fa`, `mahlerTransform_muA`,
  `binomialSeries_natCast`)
- **Statement**: in skeleton (MuA.lean:35–95).
- **Proof sketch** (decomposition L1.1–L1.8):
  1. `isUnit_natCast_of_not_dvd`: `PadicInt.isUnit_iff.2`; `‖(a:ℤ_[p])‖ = 1` from
     `le_antisymm (norm_le_one _)` + `not_lt.2` of `norm_int_lt_one_iff_dvd`
     (`exact_mod_cast` ℕ→ℤ dvd).
  2. `constantCoeff_geomSum`: `simp [geomSum, map_sum, map_pow]`;
     `Finset.sum_const`, `card_range`.
  3. `geomSum_mul_X`: `geom_sum_mul` at `x := 1+X`; rewrite `1+X−1 = X` by
     `add_sub_cancel_left`. (If `geom_sum_mul` has moved/renamed: 6-line induction
     fallback recorded in decomposition L1.3.)
  4. `isUnit_geomSum`: `isUnit_iff_constantCoeff.2` ∘ steps 1–2.
  5. `X_mul_FaNum`: `PowerSeries.ext`; case `0`: both sides 0 (step 2);
     case `n+1`: `coeff_succ_X_mul`, `coeff_mk`; RHS natCast-coeff via
     `PowerSeries.coeff_natCast`-shape (or `Nat.cast` = `C a`: `coeff_C`).
  6. `geomSum_mul_Fa`: `Fa`-def; `mul_left_comm` + `Ring.inverse_mul_cancel`
     (step 4).
  7. `one_add_X_pow_sub_one_mul_Fa`: rw ← step 3; `mul_assoc`-shuffle to
     `X·(geomSum·Fa)`; steps 6 then 5.
  8. `mahlerTransform_muA`: `muA`-def + `LinearEquiv.apply_symm_apply` (relate
     `mahlerLinearEquiv` to `mahlerTransform` — they coincide per
     MahlerTransform.lean:160's construction; `mahlerTransform_ofPowerSeries` if
     needed).
  9. `binomialSeries_natCast`: induction on `a`: `binomialSeries_zero`,
     `binomialSeries_add` (+1 case via `binomialSeries 1 = 1 + X`:
     `PowerSeries.ext`, `binomialSeries_coeff`, `Ring.choose_natCast`/
     `Ring.choose_one_right`-computation; or de-privatise/replicate Toolbox's
     `binomialSeries_mul_nat` at `c := 1`).
- **Mathlib lemmas**: `PadicInt.isUnit_iff` (:366), `PadicInt.norm_int_lt_one_iff_dvd`
  (:280), `PadicInt.norm_le_one`, `geom_sum_mul`, `PowerSeries.isUnit_iff_constantCoeff`
  (Inverse.lean:111), `Ring.inverse_mul_cancel`, `coeff_succ_X_mul`, `coeff_mk`,
  `binomialSeries_zero/add/coeff`.
- **Sources**: RJW Prop 4.4 proof (TeX 1488–1494), Lem 4.3 (TeX 1475). Quotes +
  realisation note: decomposition R1 head.
- **Generality**: `a : ℕ` (source: integer coprime to p; ℕ suffices — negative
  integers never used in §4); defs total (junk via `Ring.inverse`), lemmas carry
  `hpa : ¬ p ∣ a`.
- **Blueprint**: wire `kl-Fa-in-Zp` → `PadicMeasure.one_add_X_pow_sub_one_mul_Fa`
  (+ prose note: membership is by construction, the identity is the content);
  wire `measure-mu-a` → `PadicMeasure.muA`. Blueprint build green.
- **Cleanup**: `/cleanup` the nine declarations immediately after.
- **Progress**:
  - 2026-06-10: DONE — 8 declarations proven (isUnit_natCast_of_not_dvd,
    constantCoeff_geomSum, geomSum_mul_X, isUnit_geomSum, X_mul_FaNum, geomSum_mul_Fa,
    one_add_X_pow_sub_one_mul_Fa, mahlerTransform_muA). `binomialSeries_natCast`
    DELETED from skeleton — mathlib already has it as `binomialSeries_nat` (simp,
    Binomial.lean:69); T032's sketch updated to use the mathlib name. Off-script:
    add_sub_cancel_left via have+rw (simp would not fire it); natCast-coeff handled
    via ← map_natCast C then coeff_C (simp re-reverses map_natCast — rw before simp).
    Axioms standard (3 spot-checked). Blueprint: kl-Fa-in-Zp + measure-mu-a wired,
    builds green. Cleanup: degraded mode — proofs 1–6 lines, hand-audited.

### [T032] Dirac-sum identity + `Λ(ℤ_p)` is a domain
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/MuA.lean
- **Depends on**: T031
- **Parallel**: yes (with T033 after T031)
- **Type**: lemmas (3 sorries: `dirac_natCast_sub_one_mul_muA`, `instIsDomain`,
  `dirac_natCast_sub_one_ne_zero`)
- **Statement**: in skeleton (MuA.lean:101–110).
- **Proof sketch** (decomposition L1.9–L1.10):
  1. `instIsDomain`: transport `IsDomain ℤ_[p]⟦X⟧` (mathlib instance over a domain)
     along `(mahlerRingEquiv p).symm` — `RingEquiv.isDomain`-spelling (candidates:
     `MulEquiv.isDomain`, `Function.Injective.isDomain` via `.injective` +
     `.toRingHom`).
  2. `dirac_natCast_sub_one_mul_muA`: apply `(mahlerRingEquiv p).injective`;
     `map_mul/map_sub/map_sum/map_one`; `mahlerTransform_dirac` +
     `binomialSeries_natCast` (T031) turn LHS-transform into
     `((1+X)^a−1)·Fa` = `one_add_X_pow_sub_one_mul_Fa`; RHS-transform:
     `Σ(1+X)^i − a•1 = geomSum − natCast` (smul-to-natCast bridge:
     `Nat.cast_smul_eq_nsmul`/`nsmul_eq_mul`). NB `mahlerRingEquiv` vs
     `mahlerTransform` bridge lemma exists in Convolution.lean.
  3. `dirac_natCast_sub_one_ne_zero`: transform `= (1+X)^a − 1 ≠ 0` since
     `coeff 1 = a ≠ 0` (`coeff_one` of pow via `add_pow`-coeff or
     `Polynomial`-free route: `coeff 1 ((1+X)^a) = a` by induction or
     `binomialSeries_natCast` + `binomialSeries_coeff` at 1: `Ring.choose a 1 = a`).
- **Mathlib lemmas**: PowerSeries `instIsDomain` (over `IsDomain R`),
  `RingEquiv.isDomain` (or variant), `Nat.cast_injective` (char-0 `ℤ_[p]`),
  `binomialSeries_coeff`, `Ring.choose_one_right`.
- **Sources**: decomposition L1.9 (composition note), TeX 1475/1490.
- **Generality**: `IsDomain` instance is global (not §4-scoped) — place near the top
  of MuA.lean; consider migrating to Convolution.lean at cleanup (note for /cleanup).
- **Blueprint**: no node (infrastructure).
- **Cleanup**: `/cleanup` immediately; flag the instance's final home.
- **Progress**:
  - 2026-06-10: DONE — dirac_natCast_sub_one_mul_muA (via mahlerTransform_injective +
    new simp lemmas mahlerTransform_sub/smul, map_sum through mahlerTransformₗ with
    rfl-coe bridges), instIsDomain (MulEquiv.isDomain via mahlerRingEquiv.toMulEquiv),
    dirac_natCast_sub_one_ne_zero (coeff-1 of (1+X)^a = a via Polynomial.coeff_one_add_X_pow
    through toPowerSeries). Axioms standard (3/3). ne_zero proof avoided
    binomialSeries_coeff (Ring.choose-free route). Cleanup: degraded mode; flag —
    mahlerTransform_sub/smul belong in Convolution.lean at next tooled cleanup.

### [T033] Bernoulli moments: `∫x^k dμ_a = (−1)^k(1−a^{k+1})ζ(−k)`
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/MuA.lean
- **Depends on**: T030, T031
- **Parallel**: yes (with T032, T034 modulo deps)
- **Type**: theorem cluster (8 sorries: `map_del`, `hasSubst_exp_sub_one`,
  `derivativeFun_subst_exp`, `constantCoeff_subst_exp`,
  `constantCoeff_iterate_derivativeFun`, `constantCoeff_iterate_delQ`,
  `X_mul_subst_exp_Fa`, `muA_apply_powCM`)
- **Statement**: in skeleton (MuA.lean:131–171).
- **Proof sketch** (decomposition L2.2–L2.7; the full multiply-and-cancel plan for
  `X_mul_subst_exp_Fa` is in L2.6 — follow it step by step):
  1. `map_del`: `PowerSeries.ext n`; `coeff_map`, `coeff_derivativeFun`,
     `one_add_mul`-expansion both sides; `map_natCast`.
  2. `hasSubst_exp_sub_one`: `HasSubst.of_constantCoeff_zero'` (§3 precedent in
     Toolbox `mahlerTransform_pushforward_mulCM`); `constantCoeff_exp`, `map_sub`.
  3. `derivativeFun_subst_exp`: `derivative_subst` (Derivative.lean:184) + bridge
     `d⁄dX ↔ derivativeFun`; `derivative_exp`; algebra: `(dF)∘g·exp =
     ((1+X)·dF)∘g` via `subst_mul`-homomorphy + `(1+X)∘g = exp` (`subst_add`,
     `subst_one`? — use `map_add` of `substAlgHom`).
  4. `constantCoeff_subst_exp`: `constantCoeff_subst` (Substitution.lean:244);
     constant-coeff-zero kills all `n ≥ 1` terms (`pow`-of-zero-constantCoeff);
     fallback: `coeff_subst` at 0.
  5. `constantCoeff_iterate_derivativeFun`: induction on k;
     `Function.iterate_succ_apply'`; `coeff_derivativeFun`;
     `Nat.factorial_succ`; `push_cast; ring`.
  6. `constantCoeff_iterate_delQ`: induction on k via 3+4+5: `constCoeff(delQ^[k]F)
     = constCoeff(D^[k](F∘(e−1)))` (commute one delQ out per step), then 5.
  7. `X_mul_subst_exp_Fa`: multiply-and-cancel by `(rescale a exp − 1)` per
     decomposition L2.6: LHS·: subst the T031 identity
     `one_add_X_pow_sub_one_mul_Fa` through `exp−1` (`substAlgHom`-ring-hom,
     `exp_pow_eq_rescale_exp` for `subst((1+X)^a) = rescale a exp`); RHS·:
     `bernoulliPowerSeries_mul_exp_sub_one` + substituted `geomSum_mul_X`
     (`e^{at}−1 = (e^t−1)·Σ_{j<a}e^{jt}`) + `rescale`-ring-hom
     (`rescale a X = C a·X`-form, `coeff_rescale` fallback); cancel by
     `mul_right_cancel₀` in the domain `ℚ_p⟦X⟧` (`rescale a exp − 1 ≠ 0`:
     coeff 1 = `a ≠ 0`, char-0 cast).
  8. `muA_apply_powCM`: `apply_powCM` (§3) + `mahlerTransform_muA` (T031); cast;
     commute map through iterates (1 + `constantCoeff_map`, induction); step 6;
     extract `coeff (k+1)` of step 7 (`coeff_succ_X_mul`); `bernoulliPowerSeries`
     coeff + `coeff_rescale`; `k!/(k+1)! = (k+1)⁻¹` (`Nat.factorial_succ`,
     `field_simp`); fold `zetaNeg` (`(−1)^{2k} = 1`: `neg_one_pow_mul_self`-style,
     `pow_mul_pow_eq...` — `ring` after `zetaNeg`-unfold; `Rat.cast`-homomorphy).
  Numeric anchors verified in decomposition (L2.6 attack [1]: `a=2` coefficient;
  L2.7 attack [3]: `k=0` gives `F_a(0) = (a−1)/2` both routes).
- **Mathlib lemmas**: `bernoulliPowerSeries_mul_exp_sub_one` (Bernoulli.lean:273),
  `bernoulliPowerSeries`-def (:270), `PowerSeries.derivative_subst` (:184),
  `PowerSeries.derivative_exp`, `constantCoeff_exp`, `coeff_exp`,
  `exp_pow_eq_rescale_exp` (Exp.lean:153), `constantCoeff_subst` (:244),
  `coeff_rescale`, `rescale` ring-hom (`map_one/map_sub`), `coeff_derivativeFun`,
  `coeff_succ_X_mul`, `Nat.factorial_succ`, `Rat.cast`-field-hom simp set.
- **Sources**: RJW Lem 4.2 (TeX 1459–1464, value part), Lem 4.3 (TeX 1473–1479),
  Prop 4.6 (TeX 1500–1507) — quotes in decomposition R2.
- **Generality**: ℚ_p-coefficients via `PadicInt.Coe.ringHom`-map; `delQ` is a
  *temporary* ℚ_p-clone of `del` — **cleanup debt**: merge by generalising
  `PadicMeasure.del` to `CommRing R` in a dedicated pass (recorded; do NOT churn §3
  call sites mid-ticket).
- **Blueprint**: wire `kl-mua-interpolation` → `PadicMeasure.muA_apply_powCM`;
  wire `kl-define-Fa` → `PadicMeasure.constantCoeff_iterate_delQ` (the
  `f_a^{(k)}(0) = (∂^k F_a)(0)` content; prose note that the substitution is
  realised by `PowerSeries.subst (exp−1)`); `kl-values-of-zeta` stays unwired
  (Mellin half is §2) — add the rationale comment.
- **Cleanup**: `/cleanup` the eight declarations immediately after.
- **Progress**:
  - 2026-06-10: DONE — 9 declarations (added map_derivativeFun helper): map_del,
    hasSubst_exp_sub_one, derivativeFun_subst_exp (calc via derivative_subst — NB
    mathlib's takes A *explicitly*: `derivative_subst ℚ_[p] hg`), constantCoeff_subst_exp
    (finsum_eq_single at 0, Mv/PS-constantCoeff rfl-bridge), constantCoeff_iterate_
    derivativeFun + _delQ (inductions), X_mul_subst_exp_Fa (multiply-and-cancel by
    rescale a exp − 1, per decomposition L2.6 plan — worked exactly as planned),
    muA_apply_powCM (final algebra: parity cases on (−1)^k + field_simp + push_cast +
    ring; algebraMap-vs-Nat-cast needed map_add in the distribution simp). Axioms
    standard (3 spot-checked incl. the theorem). Blueprint: kl-mua-interpolation →
    muA_apply_powCM, kl-define-Fa → constantCoeff_iterate_delQ; builds green.
    Cleanup: degraded mode — delQ-merge debt re-flagged for tooled pass.

### [T034] ψ-invariance: projection formula + `ψ(μ_a) = μ_a`
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/MuA.lean
- **Depends on**: T031, T032
- **Parallel**: yes (with T033)
- **Type**: theorem cluster (9 sorries: `psi_phi_mul`, `phi_dirac`, `psi_dirac_mul`,
  `psi_dirac_of_isUnit`, `psi_add`, `psi_smul`, `psi_sum`, `psi_muA`)
- **Statement**: in skeleton (MuA.lean:182–215).
- **Proof sketch** (decomposition R3 — **recorded replan**: the source's
  ξ/roots-of-unity proof (TeX 1517–1524) is replaced by the equivalent elementary
  computation; justification block in decomposition R3 head):
  1. `psi_phi_mul`: `LinearMap.ext f`; `show`-unfold both sides (§3 `psi_phi`
     pattern); `mul_apply` (Convolution); inner integrand: for `y ∈ pℤ_p`,
     `charFn(px+y) = charFn(y)` and `sd(px+y) = x + sd y` — new digit sub-lemma
     `digit (p·x + y) = digit y` (~8 LOC from `digit`'s `toZModPow 1`
     characterisation, `map_add`, `p·x ↦ 0`); reassemble as `(ν * psi μ) f`.
  2. `phi_dirac`: `rfl`-grade (pushforward of dirac, §3 pattern).
  3. `psi_dirac_mul`: via `psi_phi` + 2 (`ψ[px] = ψφ[x] = [x]`).
  4. `psi_dirac_of_isUnit`: `LinearMap.ext`; charFn vanishes off `pℤ_p`; unit ∉
     `pℤ_p` (`PadicInt.isUnit_iff`, `setOf_isUnit_eq`/norm-argument).
  5. `psi_add/psi_smul/psi_sum`: definitional `LinearMap.ext` unfolds (the
     integrand map `f ↦ charFn·(f∘sd)` is linear in μ); `psi_sum` by
     `Finset.sum_induction` from add + `ψ0 = 0`. **Cleanup debt noted**: psi
     should become a bundled linear map in a later pass.
  6. `psi_muA`: per decomposition L3.6: (a) `v_a·ψμ_a = ψ(φ(v_a)·μ_a)` [1 + 2];
     (b) telescope `(Σ_{j<p}[aj])·([a]−1) = [ap]−1` (`dirac_mul_dirac`,
     `Finset.sum_range_succ'`); (c) expand `([ap]−1)·μ_a` via T032's identity
     left-multiplied by `Σ_j[aj]`; transform-side geom-sum route for the
     double-product (decomposition L3.6 attack [2]: both routes recorded);
     (d) apply ψ termwise (3,4,5): `p ∣ aj+i`-bookkeeping or transform-side
     X-cancellation; result `Σ_{i<a}[i] − a•1`; (e) rewrite back via T032 =
     `v_a·μ_a`; (f) `mul_left_cancel₀` (T032 ne-zero + IsDomain).
     End-to-end numeric trace at `p=3, a=2` in decomposition L3.6 attack [1].
- **Mathlib lemmas**: `Finset.sum_range_succ'`, `Nat.Coprime.dvd_of_dvd_mul_left`
  (j=0 isolation), `mul_left_cancel₀`; rest is §3 project API (`mul_apply`,
  `dirac_mul_dirac`, `shiftDiv_mul`, `mem_pZp_of_mul`, charFn lemmas).
- **Sources**: RJW Lem 4.7 statement (TeX 1513–1515, verbatim in decomposition);
  source proof TeX 1517–1524 (quoted; replaced — replan block).
- **Generality**: projection formula stated for all ν, μ (maximal); dirac lemmas
  pointwise-general.
- **Blueprint**: wire `kl-psi-invariant` → `PadicMeasure.psi_muA`; add a prose
  remark to the node recording the ξ-free route (per CLAUDE.md rule 5).
- **Cleanup**: `/cleanup` immediately after; flag psi-bundling debt.
- **Progress**:
  - 2026-06-10: DONE — 11 declarations (8 planned + psi_zero, dirac_zero_eq_one,
    psi_dirac_natCast, + SMulCommClass ℤ_[p] Λ Λ instance which the smul-mul algebra
    needed). psi_phi_mul exactly per decomposition L3.1 (digit arithmetic via
    y = p·sd(y) substitution — no new digit lemma needed; ∉-case by ultrametric
    sandwich). psi_muA per the replanned route: telescope + transform-side geom
    product (X-cancellation, no Finset reindex for the product; the ψ-side reindex
    via Finset.sum_nbij'). rw-gotcha: dirac identity rewrote both sides at once.
    Axioms standard. Blueprint: kl-psi-invariant → psi_muA wired + ξ-free note
    already in file docstring; builds. Cleanup: degraded — psi-bundling debt
    re-flagged (psi_zero/add/smul/sum are all rfl-grade: psi should be a LinearMap
    in a tooled pass).

### [T035] Restriction to `ℤ_p^×`: Euler factor removed
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/MuA.lean
- **Depends on**: T033, T034
- **Parallel**: no
- **Type**: theorem (2 sorries: `phi_apply_powCM`, `res_units_muA_apply_powCM`)
- **Statement**: in skeleton (MuA.lean:226–233).
- **Proof sketch** (decomposition L4.1–L4.2; source proof TeX 1535–1539 quoted there):
  1. `phi_apply_powCM`: `show`-unfold pushforward; `powCM ∘ mulCM p = p^k • powCM`
     by `ContinuousMap.ext` + `mul_pow`; `map_smul`.
  2. `res_units_muA_apply_powCM`: `res_units_eq` (§3) → `μ_a − φψμ_a`;
     `psi_muA` (T034) → `μ_a − φμ_a`; `LinearMap.sub_apply`; step 1;
     `muA_apply_powCM` (T033); `push_cast; ring`.
- **Mathlib lemmas**: `mul_pow`, `map_smul`, `push_cast` set.
- **Sources**: RJW Prop 4.8 (TeX 1527–1539).
- **Generality**: step 1 for arbitrary μ (not just μ_a).
- **Blueprint**: wire `kl-restriction-interpolation` →
  `PadicMeasure.res_units_muA_apply_powCM`.
- **Cleanup**: `/cleanup` immediately; this closes MuA.lean → run the **final
  per-file cleanup** for MuA.lean here (= CLEANUP-KL-1 folded in; verify whole-file
  lint).
- **Progress**:
  - 2026-06-10: DONE first try — phi_apply_powCM (pushforward show + smul-fun ext),
    res_units_muA_apply_powCM (res_units_eq + psi_muA + push_cast + T033 + ring).
    **MuA.lean now sorry-free** (RJW §4.1–§4.2 complete: Prop 4.4/Def 4.5/Prop 4.6/
    Lem 4.7/Prop 4.8). Axioms standard. Blueprint: kl-restriction-interpolation →
    res_units_muA_apply_powCM, builds. Final per-file cleanup: degraded pass — build
    warnings clean except one flexible-simp lint note (line ~259, simp at h1 in
    X_mul_subst_exp_Fa's hreg) queued for tooled CLEANUP-FINAL; naming + docstrings
    hand-audited; no long-proof gate breach (psi_muA ~95 lines but structured by
    haves mirroring the decomposition tree).

### [T036] Units-side transfer + `x⁻¹`-twist `zetaNum`
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/ZetaP.lean
- **Depends on**: T035
- **Parallel**: yes (with T037)
- **Type**: def-API (6 sorries: `iota_muAUnits`, `muAUnits_apply_unitsPowCM`,
  `continuous_units_inv_val`, `unitsCmul_apply`, `zetaNum_apply_unitsPowCM`,
  `zetaNum_moments`)
- **Statement**: in skeleton (ZetaP.lean:40–88).
- **Proof sketch** (decomposition L5.1–L5.3):
  1. `iota_muAUnits`: `LinearMap.ext`; both sides `μ_a`-applied; pointwise
     `extendByZero f ∘ no — (extendByZero (f.comp unitsValCM-style))`:
     reuse §3 `extendByZero_comp_unitsVal` / the `mem_range_iota_iff` ⟸-direction
     computation verbatim (UnitsZp.lean:177 proof body is the template).
  2. `muAUnits_apply_unitsPowCM`: pointwise `extendByZero (unitsPowCM k) =
     charFn_units · powCM k` (`ContinuousMap.ext u`; unit-case
     `extendByZero_coe_unit`, non-unit case both sides 0); then `res`-def.
  3. `continuous_units_inv_val`: `Units.continuous_iff`-toolkit
     (Mathlib.Topology.Algebra.Constructions) or explicit: `u ↦ u⁻¹.val` is
     `MulOpposite.unop ∘ Prod.snd ∘ embedProduct`, each continuous (§3 UnitsZp
     embedProduct machinery).
  4. `unitsCmul_apply`: `rfl`-grade (`LinearMap.mulLeft`-apply).
  5. `zetaNum_apply_unitsPowCM`: 4 + pointwise `invCM·unitsPowCM k =
     unitsPowCM (k−1)`: `ContinuousMap.ext u`; `(u⁻¹:ℤ_p)·(u:ℤ_p)^k`:
     `Units.val`-arith — `← Units.val_pow_eq_pow_val`, `← Units.val_mul`,
     `inv_mul_eq_iff`/`pow_sub_one_mul`-shape with `Nat.succ_pred_eq_of_pos hk`.
  6. `zetaNum_moments`: 5 + 2 + T035 at `k−1`; sign-shuffle
     `(−1)^{k−1}(1−a^k) = (−1)^k(a^k−1)` by `ring`-after-`Nat.succ_pred` cast
     handling (`Odd/Even` not needed — `(−1)^{k−1}·(−1) = (−1)^k` via
     `pow_succ` on `k−1+1 = k`).
- **Mathlib lemmas**: `Units.continuous_iff` (or `Units.embedProduct`-route),
  `Units.val_pow_eq_pow_val`, `Units.val_mul`, `Nat.succ_pred_eq_of_pos`,
  `pow_succ`.
- **Sources**: RJW TeX 1555–1562 (eq 4.11 + the `x⁻¹μ_a`-moment display; quoted in
  decomposition R5/L5.3).
- **Generality**: `unitsCmul` for arbitrary `g` (the general eq-4.11 operation, not
  just `x⁻¹`).
- **Blueprint**: wire `kl-theta-a` → `PadicMeasure.unitsCmul` with prose adjusted:
  the node's θ_a is `dirac p a − 1` (§3 objects, augmentation generator); its new
  content anchor is the well-defined `x⁻¹`-multiplication (eq 4.11). Keep faithful
  per CLAUDE.md rule 2; do not over-claim.
- **Cleanup**: `/cleanup` immediately after.
- **Progress**:

### [T037] Integer topological generator (p odd)
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/ZetaP.lean
- **Depends on**: none (uses §3 only)
- **Parallel**: yes (with T030–T036)
- **Type**: theorem (2 sorries: `topGen_pow_ne_one`, `exists_nat_topological_generator`)
- **Statement**: in skeleton (ZetaP.lean:92–103).
- **Proof sketch** (decomposition L5.4; **source-expansion**, cross-ref
  Washington/Ireland–Rosen — the source's Def 4.10 takes an integer top-generator
  implicitly):
  1. `topGen_pow_ne_one`: suppose `a^k = 1`, `k > 0`. Then
     `(unitsToZModPow p n a)^k = 1` ∀n (`map_pow`, `map_one` — note
     `unitsToZModPow` is a `MonoidHom`, and `a^k = 1` in `ℤ_[p]` lifts to units:
     `Units.ext`-style: `(a^k : ℤ_[p]ˣ) = 1` from val-injectivity). So
     `orderOf (q_n a) ∣ k`; but `zpowers (q_n a) = ⊤` ⟹ `orderOf (q_n a) =
     card (ZMod p^n)ˣ = φ(p^n)` (`orderOf_eq_card_of_forall_mem_zpowers`,
     `ZMod.card_units_eq_totient`); `φ(p^n) = p^{n-1}(p−1)` unbounded
     (`Nat.totient_prime_pow`) — pick `n` with `φ(p^n) > k`, contradiction with
     `orderOf ∣ k` (`Nat.le_of_dvd`).
  2. `exists_nat_topological_generator`: obtain `u₀` (§3
     `exists_topological_generator hp2`). Set `m := (toZModPow 2 u₀).val.val`-lift
     (the ℕ-rep of `u₀ mod p²`); `u := (PadicInt.isUnit_natCast_of_not_dvd …).unit`.
     (a) `q_2 u = q_2 u₀` (natCast-naturality `map_natCast` of `toZModPow`,
     `ZMod.natCast_val`-round-trip); hence `m` generates level 2.
     (b) `m^{p−1} ≡ 1 mod p` (level-1 Fermat from level-2 generation pushed down
     `unitsToZModPow_le`) and `m^{p−1} = 1 + p·c` with `p ∤ c` — else order at
     level 2 divides `p−1 < φ(p²)` contradicting (a)
     (`ZMod.unitOfCoprime`-arithmetic; extract `c` over ℤ/ℕ).
     (c) level n: `orderOf (q_n u)` is divisible by `p−1` (push down to level 1,
     order there is `p−1`) and by `p^{n−1}` (`orderOf_one_add_mul_prime` applied
     to `(m:ZMod p^n)^{p−1} = 1 + p·c`-image, `p ∤ c`); `lcm = φ(p^n)` ⟹
     `zpowers = ⊤` (`orderOf_eq_card_iff`-direction /
     `Subgroup.eq_top_of_card_le`-style with `orderOf_dvd_card`).
     (d) levels 0,1: from level 2 by transition-surjectivity
     (`unitsToZModPow_le` + `Subgroup.map`-zpowers-⊤ pushforward; level 0 trivial
     group). §3's `exists_topological_generator` proof structure (PseudoMeasure:857)
     is the template for the level-bookkeeping.
- **Mathlib lemmas**: `orderOf_eq_card_of_forall_mem_zpowers`,
  `ZMod.card_units_eq_totient`, `Nat.totient_prime_pow`, `orderOf_one_add_mul_prime`
  (ZMod-side, located during §3 work), `Nat.le_of_dvd`, `Nat.lcm_dvd`/`dvd`-algebra,
  `ZMod.natCast_val`, `map_natCast`.
- **Sources**: RJW TeX 1566 (the gloss) + decomposition R5 head-note
  (cross-references). LOC ~60–80 (the board's largest single leaf — bounded,
  toolkit proven in §3 T026).
- **Generality**: stated for this p (no further generality available — p=2 false).
- **Blueprint**: no §4 node (supporting lemma); mention in `kubota-leopoldt`
  def-node prose when T038 wires it.
- **Cleanup**: `/cleanup` immediately after.
- **Progress**:
  - 2026-06-10: DONE — topGen_pow_ne_one (level-(k+1) order vs totient growth;
    Nat.card vs Fintype.card bridge needed) and exists_nat_topological_generator
    (~110 LOC: integer lift of u₀ mod p² via ZMod.natCast_rightInverse; p∤m by the
    p²∣p contradiction; descent along surjective unitsMap via MonoidHom.map_zpowers +
    Subgroup.map_top_of_surjective; Fermat split m^{p−1} = 1+pc with p∤c from the
    level-2 order p(p−1); ascent: orderOf bounds via ZMod.orderOf_one_add_mul_prime
    (n = n'+1 destructuring to align types) + coprime lcm + eq_top_of_card_eq).
    Names found: ZMod.natCast_eq_zero_iff (not the old natCast_zmod_…), orderOf_units,
    Nat.card_zpowers. Axioms standard. Cleanup: degraded.

### [T038] `ζ_p`: definition, pseudo-measure property, interpolation
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/ZetaP.lean
- **Depends on**: T036, T037
- **Parallel**: no
- **Type**: def + theorems (3 sorries: `IsPseudoMeasure.sub`,
  `padicZeta_isPseudoMeasure`, `padicZeta_moments`)
- **Statement**: in skeleton (ZetaP.lean:110–151). `padicZeta` def already compiles.
- **Proof sketch** (decomposition L5.5–L5.7):
  1. `IsPseudoMeasure.sub`: `intro g`; witnesses `ν₁, ν₂`; `⟨ν₁ − ν₂, by
     rw [map_sub, mul_sub, hν₁, hν₂]⟩`.
  2. `padicZeta_isPseudoMeasure`: unfold `padicZeta`; `isPseudoMeasure_mk'` (§3,
     PseudoMeasure:1024) at the `choose_spec` generator-property.
  3. `padicZeta_moments`: from `IsLocalization.mk'_spec`:
     `([u]−1)·ζ_p = alg(zetaNum m)`; multiply `hν` by `alg([u]−1)` and the spec by
     `alg([b]−1)`; equate, pull back along `IsFractionRing.injective`
     (`NoZeroDivisors` ✓): `([u]−1)·ν = ([b]−1)·zetaNum m` in Λ;
     `units_mul_apply_unitsPowCM` (§3 :753) + dirac/one moments
     (`dirac`-apply `= u^k`; `1`-apply `= 1`):
     `(u^k−1)·ν(x^k) = (b^k−1)·zetaNum(x^k)`; cast to ℚ_p; divide by
     `(u^k−1) ≠ 0` (T037 `topGen_pow_ne_one` + `PadicInt.coe_injective`-cast,
     `sub_ne_zero`); insert `zetaNum_moments` (T036); sign removal:
     `neg_one_pow_mul_one_sub_pow_mul_zetaNeg` (T030) after `push_cast`
     (the ℚ-lemma casts to ℚ_p: `Rat.cast`-hom on the identity).
- **Mathlib lemmas**: `IsLocalization.mk'_spec`, `IsFractionRing.injective`,
  `sub_ne_zero`, field algebra (`div_eq_iff`, `mul_comm`-shuffles).
- **Sources**: RJW Def 4.10 (TeX 1565–1570), Prop 4.11 + proof (TeX 1581–1597) —
  quotes in decomposition R5.
- **Generality**: `padicZeta_moments` quantifies over ALL `b` and ALL witnesses
  (the strongest faithful form; gives a-independence content of zero-divisor(iii)
  for free at T039).
- **Blueprint**: wire `kubota-leopoldt` (def-node) → `PadicMeasure.padicZeta`
  (prose: mention the fixed integer-generator choice + L5.4);
  wire `kl-zetap-interpolation` → `PadicMeasure.padicZeta_moments`.
- **Cleanup**: `/cleanup` immediately after.
- **Progress**:
  - 2026-06-10: DONE — IsPseudoMeasure.sub (mul_sub then ← map_sub: order matters),
    padicZeta_isPseudoMeasure (exact isPseudoMeasure_mk' at the choice-spec),
    padicZeta_moments (mk'_spec' for the defining relation; witness pullback via
    IsFractionRing.injective; moments via units_mul_apply_unitsPowCM + dirac_apply
    rfl + units_one_def; division by u^k−1 via Subtype.coe_injective-torsion-freeness;
    final algebra: linear_combination (b^k−1)(u^k−1)·hsign — rw [← hsign] fails on
    associativity, linear_combination is the right tool). Axioms standard.
    Blueprint: kubota-leopoldt → padicZeta, kl-zetap-interpolation →
    padicZeta_moments; builds green. Cleanup: degraded.

### [CLEANUP-ALL-2] Pre-milestone `/cleanup-all` (§4)
- **Status**: done (2026-06-10, degraded mode — no lean-lsp). Swept all four
  KubotaLeopoldt files + §3: fixed the `finsum_eq_finsetSum_of_support_subset`
  deprecation in Toolbox.lean; remaining warnings are the standing cosmetic
  `show`-linter items (§3-pattern, queued for tooled CLEANUP-FINAL) + one
  flexible-simp note (MuA.lean:260) queued likewise. Blueprint re-render deferred
  to post-T039 (single render).
- **Depends on**: T030–T038
- **Type**: cleanup
- **Description**: project-wide cleanup before the §4 milestone theorem, per the
  cadence rule. Sweep the four KubotaLeopoldt files + any §3 files touched
  (Toolbox if psi-lemmas land there); verify linter set; re-render blueprint site
  (`./scripts/ci-pages.sh`).

### [T039] **MILESTONE** — Kubota–Leopoldt: existence and uniqueness
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/ZetaP.lean
- **Depends on**: T038, CLEANUP-ALL-2
- **Parallel**: no
- **Type**: theorem (1 sorry: `kubotaLeopoldt`)
- **Statement**: in skeleton (ZetaP.lean:154).
- **Proof sketch** (decomposition L5.8; source TeX 1599):
  1. Existence: `⟨padicZeta p hp2, ⟨padicZeta_isPseudoMeasure …, fun b k hk ν hν =>
     padicZeta_moments …⟩, ?uniq⟩`.
  2. Uniqueness: `q` with the property; show `q = padicZeta`: set `d := q −
     padicZeta`; `IsPseudoMeasure.sub` (T038); apply
     `pseudoMeasure_eq_zero_of_moments` (§3 :829) at `a := u` (the T037 generator,
     torsion-free via `topGen_pow_ne_one`): given a witness `ν` of `([u]−1)·d`,
     produce witnesses `ν₁` of `([u]−1)q` (from `hq.2`-side: `q`'s
     IsPseudoMeasure at `u`) and `ν₂ := ν₁ − ν` for padicZeta — or symmetrically;
     both interpolation values equal (the property at `b := u`) ⟹
     `ν(x^k)`-cast `= 0` ⟹ `ν(x^k) = 0` (`PadicInt`-cast injective +
     `Rat`-cast arith); conclude `d = 0`; `sub_eq_zero`.
     (Witness bookkeeping: `alg([u]−1)·d = alg(ν)` with `alg` injective makes all
     witness-identifications unique — `IsFractionRing.injective` once.)
- **Mathlib lemmas**: `sub_eq_zero`, `ExistsUnique`-intro shape; rest §3/§4 project.
- **Sources**: RJW Thm 4.1 (TeX 1444–1447) + proof line (TeX 1599) — quoted at
  decomposition R-KL head.
- **Generality**: statement quantifies moments over all `b` (decomposition R-KL
  "moment encoding" note).
- **Blueprint**: wire `kl-existence-uniqueness` → `PadicMeasure.kubotaLeopoldt`.
  This completes the §4 chapter except `kl-values-of-zeta` (unwired, §2-pending —
  rationale comment in place from T033). Re-render site.
- **Cleanup**: `/cleanup` immediately after (= final per-file cleanup for
  ZetaP.lean, CLEANUP-KL-2 folded in). Then update CLEANUP-FINAL's scope to include
  the §4 files.
- **Progress**:
  - 2026-06-10: **DONE — RJW Theorem 4.1 proven.** Existence: padicZeta +
    padicZeta_isPseudoMeasure + padicZeta_moments. Uniqueness: difference is a
    pseudo-measure (IsPseudoMeasure.sub) with vanishing witness-moments (witness
    split via IsFractionRing.injective; both interpolations at b := u subtract to 0;
    Subtype.coe_injective with a beta-reducing `show` for the ℤ_p-level conclusion),
    killed by pseudoMeasure_eq_zero_of_moments at the integer generator.
    `lake build PadicLFunctions` green, ZERO sorries project-wide,
    #print axioms kubotaLeopoldt = [propext, Classical.choice, Quot.sound].
    Blueprint: kl-existence-uniqueness → kubotaLeopoldt wired; chapter now 10/11
    nodes green (kl-values-of-zeta deliberately unwired pending §2 Mellin theory);
    site re-rendered (ci-pages OK). Final per-file cleanup ZetaP.lean: degraded
    pass done (show-linter cosmetics queued for tooled CLEANUP-FINAL).

### CLEANUP-FINAL scope note (updated 2026-06-10)
CLEANUP-FINAL (§3 board) now covers the §4 files too:
PadicLFunctions/KubotaLeopoldt/{ZetaValues,ZetaValuesComplex,MuA,ZetaP}.lean.
Queued degraded-mode items: show-linter cosmetics (project-wide pattern),
flexible-simp at MuA.lean:260, psi-bundling (psi → LinearMap), delQ/del merge
(generalise del to CommRing), mahlerTransform_sub/smul → Convolution.lean,
instIsDomain + SMulCommClass placement review. Blocked on a lean-lsp-tooled session.

## §4 dependency quick-view

```
T030 (zeta values)──────────────┐
T031 (F_a, μ_a)──┬─ T032 (dirac/domain) ─┬─ T034 (ψ) ─┐
                 └─ T033 (moments) ←T030 ┘            ├─ T035 (Res moments)
T037 (integer generator) [independent]                │
T036 (units/x⁻¹) ←─────────────────────────────────────┘
T038 (ζ_p) ← T036, T037
CLEANUP-ALL-2 ← T030..T038
T039 MILESTONE ← T038, CLEANUP-ALL-2
```
Parallel capacity: 3 workers at peak (T030/T031/T037 start immediately).
Cleanup cadence: per-ticket immediate cleanup (standing rule) ⊇ 3-ticket cadence;
final per-file cleanups folded into T035 (MuA.lean) and T039 (ZetaP.lean);
CLEANUP-ALL-2 guards the milestone; CLEANUP-FINAL (§3 board) extended to §4 files.

---

# §5 — Interpolation at Dirichlet characters (TeX 1610–1979) — added 2026-06-10

## §5 Summary
- Tickets: TW1–TW6 (widening) + T501–T523 (§5 proper + exp/log cluster,
  user-added at board approval) + cleanups per cadence
- Open: all | Done: 0
- Decomposition: `.mathlib-quality/decomposition.md` §5 (W*, L5.1.*, L5.2.*, L5.3.*;
  gate PASSED 2026-06-10 with 3 recorded replan/design notes: R5-CLEAR,
  L5.2.4-route, L5.2.8/L5.3.3 statement designs)
- Skeleton: `Coefficients.lean` + `Interpolation/{Characters,GenBernoulli,
  GenBernoulliComplex,Branches}.lean` skeletonised NOW; the Λ_R-dependent
  statements (Twist/TameConductor/NonTame) are skeletonised by TW6 (refactor
  exception, decomposition §5 "Skeleton location")
- Coefficients: `L` normed field, `[NormedAlgebra ℚ_[p] L] [IsUltrametricDist L]
  [CompleteSpace L]`, `R := integerRing L` (plan.md §5 design decision 1)
- **Standing rules (CLAUDE.md) bind every ticket**: blueprint node wiring in-session
  (chapter: `Interpolation.lean`; node labels listed per ticket), /cleanup
  (FULL tooled mode — lean-lsp present) before done, axioms ⊆ standard, checkpoint
  commit + push.
- **Parallel capacity**: 3 chains independent at the start — (A) TW-chain,
  (B) T501/T503/T504/T505 (Gauss/Bernoulli, no W dependency), (C) T517/T518
  (Branches, no W dependency). §5.1/§5.2 assembly tickets need (A).

### [TW1] Coefficients: integerRing + instances + root-of-unity norms
- **Status**: done (2026-06-10T17:05Z)
- **Progress**: 2026-06-10: all 8 skeleton sorries discharged. W1 integerRing +
  4 instances (ultrametric/complete/Algebra ℤ_[p]/IsLinearTopology via ballIdeal +
  mk_of_hasBasis'); helper norm_natCast_self_lt_one; W2 norm_sub_one_lt
  (binomial + Nat.Prime.dvd_choose_pow + exists_norm_finsetSum_le_of_nonempty);
  W2' tendsto; W3 norm_pow_sub_one_eq_one (prod_one_sub_pow_eq_order +
  Padic.norm_natCast_eq_one_iff + erase-product argument). VERIFICATION: zero
  diagnostics; #print axioms = {propext, Classical.choice, Quot.sound} on both
  headline theorems (lean_verify); lake build green project-wide (3517 jobs).
  CLEANUP: tooled-inline at authoring (zero linter warnings incl. show/push_neg/
  longLine/unusedSectionVars all fixed; import order corrected); formal 10-phase
  file pass runs at CLEANUP-W1 per board placement. Mathlib-gap notes: no
  norm-unit-ball subring in mathlib (integerRing is a PR candidate, as are W2/W3). | **File**: PadicLFunctions/Coefficients.lean | **Depends on**: none
- **Parallel**: yes (chain A head) | **Type**: def + instances + lemmas
- **Statement**: fill the skeleton sorries at Coefficients.lean (integerRing
  subring fields; IsUltrametricDist/CompleteSpace/Algebra ℤ_[p]/IsLinearTopology
  instances; `IsPrimitiveRoot.norm_sub_one_lt`, `.tendsto_pow_sub_one`,
  `.norm_pow_sub_one_eq_one`).
- **Proof sketch**: decomposition W1/W2/W3 + L5.1.6a entries (routes + attack
  logs there). W1 closure: `IsUltrametricDist.norm_add_le_max` (mathlib, exact
  name verify via lean_local_search) + `norm_mul_le`. Completeness:
  `IsClosed.completeSpace_coe` on the closed ball. Algebra: `‖algebraMap ℚ_[p] L
  q‖ = ‖q‖` from `NormedAlgebra` (norm_algebraMap') restricted to ℤ_[p].
  IsLinearTopology: `IsLinearTopology.mk_of_hasBasis`-style with the ideal basis
  `{x | ‖x‖ ≤ ε}` (ideals by ultrametric + ‖unit-ball·x‖ ≤ ‖x‖). W2: binomial
  expansion of (1+x)^{p^n} = 1 + Kummer `Nat.Prime.dvd_choose` (mathlib name:
  `Nat.Prime.dvd_choose_pow`?? verify) + norm contradiction. W3: evaluate
  `∏_{0<j<D}(X − ζ^j)` at 1 via `IsPrimitiveRoot` cyclotomic-product lemmas
  (search `IsPrimitiveRoot` `geom_sum`/`prod_X_sub`-family) ⟹ ∏(1−ζ^j) = D;
  norms multiply (NormedField), all ≤ 1, ‖D‖ = 1 (p ∤ D + algebra-norm).
- **Mathlib lemmas**: `IsUltrametricDist.norm_add_le_max`(-shape),
  `IsClosed.completeSpace_coe`, `norm_algebraMap'`, `Nat.Prime.dvd_choose`
  (Kummer-direction), `IsPrimitiveRoot.pow_eq_one`, cyclotomic product (verify
  candidates: `IsPrimitiveRoot.prod_one_sub_pow`-shape; fallback 8-line direct).
- **Sources**: RJW TeX 690 (O_L), 1798 (W3 verbatim quote in decomposition);
  Washington §1 for W2 (classical).
- **Generality**: maximal — any nonarch complete normed ℚ_[p]-algebra field;
  no finiteness over ℚ_p (plan.md §5 decision 1).
- **Blueprint**: none yet (infrastructure; Measures-chapter prose already wired).
- **Sizing**: W1 ~60 LOC, W2 ~25, W3 ~20, instances ~40 (source spans cited in
  decomposition; the instance pack has no source-lines — infrastructure).

### [TW2] Widen Measure/Basic.lean to coefficient ring R
- **Status**: done (2026-06-10T17:45Z)
- **REPLAN NOTE (route, 2026-06-10T17:20Z)**: in-place parameter swap rejected
  after measurement: ~420 call sites, and `ℤ_[p]` is definitionally-but-not-
  syntactically `↥(integerRing ℚ_[p])` (PadicInt is its own subtype with its own
  instance tower) — an in-place swap breaks every §4 call site with instance-
  diamond repairs, violating the "§4 unaffected" DoD. ROUTE: parallel general
  layer `PadicLFunctions/MeasureR/*.lean` over `(K : NormedField, ultrametric,
  complete; R := integerRing K)` mirroring Measure/* — the ambient field makes
  the W-r1 division/continuity argument work exactly as in the ℤ_p case; §3/§4
  stay frozen; TW6's baseChange bridges `PadicMeasure p X → MeasureR ℚ_[p]-…`
  via the TW1 algebra map. TW2 := MeasureR/Basic.lean; TW3–TW5 scope updated
  to the corresponding MeasureR files. plan.md "parameter-insertion" promise
  superseded by this recorded note (same lemmas+proof routes, new placement).
- **Progress**: 2026-06-10: MeasureR/Basic.lean complete, zero sorries —
  `MeasureR K X` (abbrev, LinearMap-transparent like §3), dirac/compRight/
  pushforward + simp API, `norm_apply_le` (field-division route per W-r1:
  attained sup + divide-by-scalar in K, integrality from ball-valuedness),
  `continuous`, `ext_locallyConstant` (reuses §3 Fubini general approximation
  lemma per W-r2). VERIFICATION: zero diagnostics; axioms standard
  (lean_verify on norm_apply_le); lake build green (3518 jobs). CLEANUP:
  tooled-inline at authoring (abbrev-not-def lesson recorded; rfl-bridge for
  subtype-norm). Formal file pass at CLEANUP-W1. | **File**: Measure/Basic.lean | **Depends on**: TW1 | **Type**: refactor
- **Contract**: re-parametrise `PadicMeasure p X := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`
  to `PadicMeasure R X := C(X, R) →ₗ[R] R` over
  `variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]`
  + per-lemma extras; keep an `abbrev`/notation so §3/§4 ℤ_[p]-call-sites stay
  green (`PadicMeasure p X` ↦ instantiation at `R := ℤ_[p]`; choose the spelling
  that minimises §4 churn — worker decides, records). `norm_apply_le` per
  decomposition W-r1 (division-by-attained-value; needs the codomain-ball
  argument — for abstract R state as `‖μ f‖ ≤ ‖f‖` PROVABLE when R is a ball
  ring: take the hypothesis spelling `[NormMulClass R]` + norm-≤-1-of-values…
  worker follows W-r1's resolution: values in R have ‖·‖ ≤ ?? — for abstract R
  the values are R itself: the W-r1 proof shape needs `‖μ g‖ ≤ 1`-from-
  R-valuedness only when R IS the ball of L. State the lemma over
  `integerRing L` directly if the abstract form fights — both forms recorded,
  decomposition W-r1). Density: rebase on Fubini.lean's
  `exists_locallyConstant_norm_sub_le'` (W-r2).
- **DoD**: `lake build PadicLFunctions` green project-wide, zero sorries in file,
  axioms standard, §4 unaffected, /cleanup, checkpoint commit.
- **Sources**: RJW Def 3.6 TeX 755–765 (§3 tree quotes).

### [TW3] Widen MahlerTransform.lean + Convolution.lean
- **Status**: done (2026-06-10T18:35Z)
- **Progress**: 2026-06-10: MeasureR/MahlerTransform.lean + MeasureR/Convolution.lean
  complete, ZERO sorries. mahlerCM basis through the isometric algebra map (new
  Coefficients lemmas: norm_algebraMap_eq, isometry_algebraMap, IsBoundedSMul);
  full Thm 3.20 over R: mahlerLinearEquiv + CommRing transport + mahlerRingEquiv +
  mul_apply (Chu-Vandermonde via algebraMap, congrArg-Subtype.val bridges) +
  dirac_mul_dirac. mahlerTransform_dirac restated as mapped binomialSeries
  (avoids BinomialRing on R — recorded). De-privated
  PadicMeasure.fwdDiff_iter_mahler_zero. VERIFICATION: zero diagnostics both
  files; axioms standard (lean_verify mul_apply); lake build green (3520).
  CLEANUP: tooled-inline at authoring; formal pass at CLEANUP-W1. | **Depends on**: TW2 | **Type**: refactor
- **Contract**: W-r3 — mathlib `mahlerEquiv` is already E-general; re-parametrise
  `mahlerCoeff/mahlerTransform/ofPowerSeries/mahlerLinearEquiv/mahlerRingEquiv`
  and the convolution transport to R. Re-check each `PadicInt.*`-specific call
  site (decomposition W-r3 attack note); `binomialSeries` acts through
  `algebraMap ℤ_[p] R`.
- **DoD**: as TW2.

### [CLEANUP-W1] /cleanup on Coefficients.lean + Basic.lean + MahlerTransform.lean + Convolution.lean
- **Status**: done (2026-06-10T18:50Z) | **Depends on**: TW3 | **Type**: cleanup (cadence: 3 tickets)
- **Progress**: scope = the new W-layer (Coefficients + MeasureR/{Basic,
  MahlerTransform,Convolution}). Full-severity diagnostic audit via lean-lsp:
  9 findings (1 unused simp arg, 4 show-changed-goal -> change, 4 unused
  section vars -> omit) — all fixed; build green, new files zero-warning.
  Per-decl golf was applied inline at authoring (same session, live linter);
  worker-per-decl ceremony recorded as not-redispatched for just-authored
  lint-clean decls (deviation note; the §3-files' standing show-warnings
  remain CLEANUP-FINAL scope).

### [TW4] Widen Toolbox.lean + UnitsZp.lean + Fubini.lean
- **Status**: done (2026-06-10T19:40Z)
- **Progress**: MeasureR/{Toolbox,UnitsZp,Fubini}.lean complete, ZERO sorries.
  Toolbox: cmul/del/powCM + mahlerTransform_cmul_X + apply_powCM (Cor 3.25
  over R; reuses de-privated PadicMeasure.mul_choose_eq through algebraMap),
  charFnCM (moved to Basic, p-FREE — mathlib charFn is value-ring-parametric,
  design improvement over the algebraMap detour), res/IsSupportedOn,
  sigma/phi/psi + psi_phi/phi_psi/res_units_eq/Cor 3.32 (space-side digit/
  shiftDiv/clopens reused from §3 — zero duplication). UnitsZp: extendByZero,
  iota, iota_injective, res_iota, mem_range_iota_iff (= ker ψ). Fubini:
  innerInt + integral_swap (the §3 approximation argument verbatim over R).
  VERIFICATION: zero diagnostics all files; axioms standard (lean_verify
  integral_swap); lake build green project-wide. CLEANUP: tooled-inline;
  formal pass folded into CLEANUP-W2. | **Depends on**: CLEANUP-W1 | **Type**: refactor
- **Contract**: W-r4 — space-side constructions re-parametrise mechanically
  (res/σ/φ/ψ/shiftDiv, units geometry, integral_swap). The §4-needed toolbox
  lemmas (φ-moment scaling, psi_phi_mul-projection formula in MuA.lean —
  actually relocate-or-widen: psi_phi_mul lives in MuA.lean (§4); widen its
  STATEMENT to R here or in TW5, worker picks placement, records).
- **DoD**: as TW2.

### [TW5] Widen PseudoMeasure.lean's Λ(ℤ_p^×)-ring section; §4 call-site repair
- **Status**: done (2026-06-10T20:10Z)
- **Progress**: MeasureR/UnitsRing.lean complete, ZERO sorries: unitsConv +
  CommRing (comm via integral_swap, assoc via triple-integral changes with
  Subtype.val bridges), units_dirac_mul_dirac, deg ring hom. innerInt API
  (add/smul/measure_add/measure_zero) added to MeasureR/Fubini. §4 call-site
  repair: NOT NEEDED under the parallel-layer route (§4 untouched — the
  route's purpose). Pseudo-measure theory stays ℤ_p per scope note.
  psi_phi_mul widening deferred to T513 (per TW4's "worker picks placement"
  note — T513 is its only §5 consumer). VERIFICATION: zero diagnostics,
  axioms standard, build green. | **Depends on**: TW4 | **Type**: refactor
- **Contract**: the units-convolution ring (unitsConv, CommRing laws, diracs,
  degree) over R; the pseudo-measure/zero-divisor/augmentation/QuotientField
  sections STAY at ℤ_[p] (decomposition W-r4 scope note). All §4 files compile
  unchanged-or-mechanically-repaired (W-r5).
- **DoD**: as TW2 + `#print axioms PadicMeasure.kubotaLeopoldt` still standard.

### [TW6] baseChange + skeletonise Λ_R-dependent §5 statements
- **Status**: done (2026-06-10T21:05Z)
- **Progress**: MeasureR/BaseChange.lean SORRY-FREE: baseChange ring hom
  (transform-side coefficient inclusion), mahlerTransform_baseChange,
  baseChange_dirac, algCM + baseChange_algCM (the characterising property,
  via tsum-mapping through the isometric algebra map). Naturality lemmas
  (psi/res/twist-compat) deferred to their §5 consumers per the loc-const
  strategy recorded in this ticket's notes. SKELETON GATE: Interpolation/
  {Twist,TameConductor,NonTame}.lean created with the Λ_R-dependent
  statements (16 sorries; charCM helper; toFieldChar bridge; statements per
  decomposition with the L5.1.8-trace-pinned form, R5-CLEAR clearing, and
  the L5.2.8 determinacy design). Support: CharZero-of-ℚ_p-algebra lemma;
  isClopen_toZModPow_fiber skeleton. Build green project-wide. W-CLUSTER
  CRITICAL PATH COMPLETE — all three §5 chains unblocked. | **Depends on**: TW5 | **Type**: def + skeleton gate
- **Statement** (key new decl): `PadicMeasure.baseChange : PadicMeasure p X →
  PadicMeasureR R X`-shape (W4: transform-side coefficient inclusion for
  X = ℤ_p; density-extension for general profinite X; ring hom on Λ(ℤ_p);
  `baseChange_dirac`, naturality w.r.t. res/φ/ψ/twist as API lemmas).
  THEN: create `Interpolation/Twist.lean`, `Interpolation/TameConductor.lean`,
  `Interpolation/NonTame.lean` with ALL the Λ_R-dependent leaf statements from
  decomposition §5 (L5.1.2/3/6/7/8/10/12, L5.2.1–L5.2.8) as `:= by sorry`,
  imports wired into PadicLFunctions.lean; `lake build` green (THE deferred
  Step-2.5 gate — decomposition "Refactor-cluster exception").
- **DoD**: build green (sorries allowed in the three new files ONLY), /cleanup
  on baseChange, commit.

### [CLEANUP-W2] /cleanup-all-lite on the widened Measure/* (final per-file)
- **Status**: open | **Depends on**: TW6 | **Type**: cleanup (final per-file ×6)

### [T501] Gauss sums: product formula at general level + norm-one
- **Status**: open | **File**: Interpolation/Characters.lean | **Depends on**: none
- **Parallel**: yes (chain B head) | **Type**: lemmas (mathlib-PR candidates)
- **Statement**: skeleton `gaussSum_mul_gaussSum_inv` (L5.1.5),
  `norm_gaussSum_eq_one`, + any zmodChar-primitivity bridge sub-lemmas needed.
- **Proof sketch**: decomposition L5.1.5 (the 4-sum collapse; attack-verified);
  norm-one via ≤1 (ultrametric sum of root-of-unity terms — values χ(c)ζ^c with
  ‖·‖ ≤ 1… careful: χ values in L: roots of unity have norm 1 — NormedField +
  finite order ⟹ ‖χ(c)‖ = 1; sub-lemma) then product = ±D with ‖D‖ = 1 splits.
- **Mathlib lemmas**: `gaussSum_mulShift_of_isPrimitive`,
  `gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive`, `AddChar.sum_mulShift`-
  orthogonality ingredient (verify generality — field proof's `sum_mulShift`),
  `ZMod.zmodChar`, `IsPrimitiveRoot.pow_eq_one`.
- **Sources**: Rem 5.3 TeX 1653–1659 (verbatim in decomposition L5.1.4); DS05
  §4.3 (cross-ref); TeX 1798 for norm-one.
- **Generality**: general level N, domain target; norm-form over the §5 L.
- **Blueprint**: wire `interp-gauss-sum` → mathlib `gaussSum` and
  `interp-gauss-sum-properties` → the pair {mathlib mulShift lemma,
  `PadicLFunctions.gaussSum_mul_gaussSum_inv`} per the new linking policy.
- **Sizing**: L5.1.5 ~35 LOC (source proof 6 lines, TeX 1685–1691-adjacent);
  norm lemma ~20.

### [T502] χ as a locally constant function on ℤ_p
- **Status**: open | **File**: Interpolation/Characters.lean | **Depends on**: none
- **Parallel**: yes | **Type**: def API
- **Statement**: skeleton `DirichletCharacter.toContinuousMapZp` continuity +
  4 API sorries (L5.1.1).
- **Proof sketch**: decomposition L5.1.1 (toZModPow fibres clopen — §3
  Basic.lean pattern `isLocallyConstant_toZModPow_val`; vanishing via
  `MulChar.map_nonunit` + unit-reduction bridge `PadicInt.isUnit_toZModPow_iff`-
  shape (verify; else 6-line norm argument)).
- **Mathlib lemmas**: `MulChar.map_nonunit`, `IsLocallyConstant.continuous`,
  `ZMod.isUnit_iff`-family.
- **Sources**: TeX 1620 (quote at L5.1.1).
- **Blueprint**: contributes to `interp-twist` prose (wired at T506).
- **Sizing**: ~50 LOC total (5 lemmas).

### [T503] genBernoulli: trivial character + parity + cyclotomic product
- **Status**: open | **File**: Interpolation/GenBernoulli.lean | **Depends on**: none
- **Parallel**: yes | **Type**: lemmas
- **Statement**: skeleton `genBernoulli_one`, `genBernoulli_eq_zero`,
  `prod_primitiveRoot_mul_sub_one` (L5.1.9/L5.1.11/L5.1.10c).
- **Proof sketch**: decomposition entries (a-range 1..N pinned; involution
  c ↦ N−c + `bernoulli_eval_one_sub`; product via `IsPrimitiveRoot`).
- **Mathlib lemmas**: `Polynomial.bernoulli_eval_one_sub` (verify name),
  `Polynomial.bernoulli_eval_one`, `bernoulli'`-bridges,
  `IsPrimitiveRoot.prod_X_sub_pow`-family (verify; else direct).
- **Sources**: Washington §4.1 Prop 4.1 (cross-ref recorded); TeX 1744–1746.
- **Blueprint**: none directly (value infrastructure).
- **Sizing**: ~30+35+20 LOC.

### [T504] genBernoulli generating function (L5.1.10a)
- **Status**: open | **File**: GenBernoulli.lean | **Depends on**: T503 | **Type**: lemma
- **Statement**: skeleton `genBernoulliPowerSeries_mul`.
- **Proof sketch**: decomposition L5.1.10a — expand both sides; mathlib
  `bernoulliPowerSeries_mul_exp_sub_one` per-a after rescale-bookkeeping
  (`exp_pow_eq_rescale_exp`, `rescale_comp`-laws); T031's clearing pattern.
- **Mathlib lemmas**: `bernoulliPowerSeries_mul_exp_sub_one`,
  `PowerSeries.exp`, `rescale`, `Polynomial.bernoulli_generating_function`-
  variant (exact mathlib relating bernoulli POLYNOMIALS: `Polynomial.sum_range_pow`-
  family — survey at execution; the §4 T031–T033 files are the template).
- **Sources**: Washington §4.1 defining identity (cross-ref recorded).
- **Sizing**: source's manipulation ~10 lines ⟹ ~80 LOC Lean (T031 analogue
  ran ~70).

### [T505] Complex bridge: L(χ,−k) = −B_{k+1,χ}/(k+1)
- **Status**: open | **File**: GenBernoulliComplex.lean | **Depends on**: T503
- **Parallel**: yes | **Type**: theorem (quarantined complex; PR candidate)
- **Statement**: skeleton `LFunction_neg_nat`.
- **Proof sketch**: unfold `DirichletCharacter.LFunction` = `ZMod.LFunction` =
  `N^{−s}Σ_j χ(j)·hurwitzZeta(j/N)`; at s = −k apply `hurwitzZeta_neg_nat`
  (j/N ∈ [0,1]); collect into genBernoulli's polynomial sum (a-range shift
  0..N−1 ↦ 1..N: j = 0 term has χ(0) = 0 for N > 1; N = 1 separately via
  `riemannZeta_neg_nat_eq_bernoulli'` + `LFunction_modOne_eq`).
- **Mathlib lemmas**: `hurwitzZeta_neg_nat`, `ZMod.toAddCircle`-coercions,
  `riemannZeta_neg_nat_eq_bernoulli'`, `DirichletCharacter.LFunction`.
- **Sources**: TeX 1702–1740 (Lem 5.5 — its L-value content), Washington Thm 4.2.
- **Blueprint**: wire `interp-dirichlet-integral`'s VALUE half? — NO: that node
  states the full Mellin lemma (complex f_{χ,a}); stays unwired with rationale
  (§2-Mellin pending, kl-values-of-zeta pattern). This theorem is the §5
  analogue of `zetaNeg`'s complex bridge — wire INTO the chapter where the
  L-values are introduced via a remark node if present (worker checks chapter).
- **Sizing**: ~60 LOC.

### [T506] Twist by χ + z-twist transform formula
- **Status**: open | **File**: Interpolation/Twist.lean (TW6 skeleton) | **Depends on**: TW6, T502
- **Type**: def + lemmas
- **Statement** (from TW6 skeleton; signatures fixed there per decomposition
  L5.1.2/L5.1.6): `PadicMeasure.twist`, `twist_apply`, `twist_powCM`,
  `twist_res_units`-integral-form (L5.1.3), `mahlerTransform_charTwist`
  (L5.1.6, eval₂ form).
- **Proof sketch**: decomposition L5.1.2/3/6 (Dirac sanity + coefficientwise
  Chu–Vandermonde; the §3 T009/T014 proof patterns; eval₂ instance stack from
  TW1's IsLinearTopology).
- **Mathlib lemmas**: `PowerSeries.eval₂`/`aeval` + `WithPiTopology` instances;
  `PadicInt.addChar_of_value_at_one` + `mahlerSeries`-API.
- **Sources**: TeX 1637–1641 (verbatim at L5.1.2), TeX 1084–1090 (z-twist).
- **Blueprint**: wire `interp-twist` → `PadicMeasure.twist`.
- **Sizing**: twist API ~40; charTwist ~90 (T014 ran ~80).

### [T507] Cleared restriction formula (EqRestrictionFormula)
- **Status**: open | **File**: Twist.lean | **Depends on**: T506 | **Type**: lemma
- **Statement**: `res_class_eq_sum_twists` (L5.1.7, p^n-cleared, measure-side).
- **Proof sketch**: decomposition L5.1.7 (orthogonality pointwise + integrate;
  geometric-sum-zero from primitive root).
- **Mathlib lemmas**: `IsPrimitiveRoot`-geom-sum (verify
  `IsPrimitiveRoot.geom_sum_eq_zero`), §3 charFn/indicator API.
- **Sources**: TeX 1126–1131 (verbatim at L5.1.7) + R5-CLEAR note.
- **Blueprint**: the §3 Measures-chapter node for the restriction formula
  (`meas-restriction-formula`-label — worker locates) gets wired NOW (it was
  the §3 deferred ξ-node) with the cleared-form prose note.
- **Sizing**: ~70 LOC (source proof 8 lines, TeX 1117–1131).

### [T508] Mahler transform of the χ-twist (RJW Lem 5.4, cleared)
- **Status**: open | **File**: Twist.lean | **Depends on**: T507, T501 | **Type**: lemma
- **Statement**: `mahler_twist_formula` per L5.1.8 — statement form pinned by
  the planning trace (G(χ⁻¹)-cleared, NO extra sign; see L5.1.8 attack [2]).
- **Proof sketch**: decomposition L5.1.8 composition (χ̃-decomposition →
  L5.1.7 → swap → Gauss (ii) → (i)).
- **Sources**: TeX 1675–1692 (verbatim quote + the source's 3-display algebra).
- **Blueprint**: wire `interp-mahler-twist` (prose note: cleared form).
- **Sizing**: source proof 12 lines ⟹ ~110 LOC.

### [CLEANUP-51] /cleanup on Twist.lean (cadence: 3 tickets)
- **Status**: open | **Depends on**: T508 | **Type**: cleanup

### [T509] Moments of the twisted measure (F_{χ,a}-values)
- **Status**: open | **File**: Interpolation/TameConductor.lean (+GenBernoulli) | **Depends on**: CLEANUP-51, T504
- **Type**: theorem cluster
- **Statement**: `twistMuA_moments` per L5.1.10 (uniform formula via LvalNeg)
  + sub-leaves 10b (twisted F_a-expansion, cleared via 10c-product).
- **Proof sketch**: decomposition L5.1.10 (T033-pattern over L; generating
  function T504; parity wiring L5.1.11; planning-time value-trace at p=3
  recorded — re-derive k=2 as the ticket's acceptance regression).
- **Sources**: TeX 1694–1700, 1727–1730 (eq:special value theorem 1).
- **Blueprint**: wire `interp-dirichlet-integral` only if its node restates the
  VALUE identity — else leave + rationale (Mellin half §2-pending); worker
  reads the node and decides per rule 2, records.
- **Sizing**: the big one — source spans TeX 1694–1740 ⟹ ~200 LOC across 3
  declarations.

### [T510] **MILESTONE: RJW Theorem 5.1** — ∫χ(x)x^k·ζ_p = L(χ,1−k)
- **Status**: open | **File**: TameConductor.lean | **Depends on**: CLEANUP-ALL-3
- **Type**: theorem
- **Statement**: witness-quantified form mirroring `kubotaLeopoldt`'s encoding
  (TW6 skeleton): for χ primitive mod p^n (n ≥ 1), p ≠ 2, k > 0, the
  θ_a-form `∫χ̃x^k d(θ_a)_R = −(1−χ(a)a^k)·LvalNeg χ (k−1)` and the
  ζ_p-pairing corollary (decomposition L5.1.12).
- **Proof sketch**: L5.1.12 composition (units-restriction + L5.1.10 + x⁻¹
  shift T036-pattern + baseChange naturality).
- **Sources**: TeX 1619–1622 (headline, verbatim at R5.1) + proof 1751–1765.
- **Blueprint**: wire `interpolation-property` (the chapter's Thm 5.1 node) →
  the new theorem; re-render site.
- **Sizing**: source proof 14 lines ⟹ ~120 LOC.

### [CLEANUP-ALL-3] Pre-milestone /cleanup-all
- **Status**: open | **Depends on**: T509 | **Type**: cleanup-all (before T510)

### [T511] F_η and μ_η (conductor D coprime to p)
- **Status**: open | **File**: Interpolation/NonTame.lean (TW6 skeleton) | **Depends on**: TW6, T501
- **Type**: def + lemmas
- **Statement**: `etaDenomUnit` (L5.2.1), `muEta` + transform characterisation
  (L5.2.2; G(η⁻¹)-unit via T501's norm lemma).
- **Sources**: TeX 1793–1798 (verbatim at L5.2.2).
- **Blueprint**: wire `interp-mu-eta`.
- **Sizing**: ~70 LOC.

### [T512] Moments of μ_η (Lem 5.9, p-adic half)
- **Status**: open | **File**: NonTame.lean | **Depends on**: T511, T504 | **Type**: lemma
- **Statement**: `muEta_moments` (L5.2.3): ∫x^k μ_η = LvalNeg η k.
- **Sources**: TeX 1801–1807 (verbatim at L5.2.3).
- **Blueprint**: wire `interp-eta-mellin`'s value half per node text (worker
  reads node; Mellin-statement half stays prose with rationale if present).
- **Sizing**: ~90 LOC (rides T504/T509 machinery at modulus D).

### [T513] ψ-invariance: ψ(μ_η) = η(p)·μ_η (Lem 5.10)
- **Status**: open | **File**: NonTame.lean | **Depends on**: T511 | **Type**: lemma
- **Statement**: `psi_muEta` (L5.2.4).
- **Proof sketch**: the **recorded ξ-free replan** (decomposition L5.2.4:
  γ-telescope + projection formula + (ℤ/D)ˣ reindex; end-to-end trace at
  p=3, D=4 recorded — statement verbatim TeX 1812–1813, route deviation
  recorded mirroring R3/T034).
- **Mathlib lemmas**: project `psi_phi_mul` (widened, TW4/TW5), §4 Dirac-ψ
  lemmas (widened), `ZMod.unitOfCoprime`-reindex machinery.
- **Sources**: TeX 1812–1827.
- **Blueprint**: wire the chapter's ψ-invariance node (locate label; prose
  note: proof via the cleared trace identity).
- **Sizing**: source proof 10 lines ⟹ ~110 LOC.

### [CLEANUP-52] /cleanup on NonTame.lean (cadence: 3 tickets on file)
- **Status**: open | **Depends on**: T513 | **Type**: cleanup

### [T514] Restriction to units: (1−η(p)p^k)-moments (Lem 5.11)
- **Status**: open | **File**: NonTame.lean | **Depends on**: CLEANUP-52, T512 | **Type**: lemma
- **Statement**: `res_units_muEta_moments` (L5.2.5).
- **Sources**: TeX 1831–1843 (verbatim at L5.2.5; T035-pattern).
- **Sizing**: ~50 LOC.

### [T515] μ_θ, its moments and restriction; ζ_η and its interpolation
- **Status**: open | **File**: NonTame.lean | **Depends on**: T514, T508 | **Type**: cluster
- **Statement**: `muTheta` (:= twist χ̃ μ_η) + Lem 5.12 cleared transform +
  moments + Res-formula (L5.2.6 — ROUTE per the corrected attack: ψ-of-twist
  via support for n ≥ 1, L5.2.4 for n = 0); `zetaEta` + final display
  (L5.2.7).
- **Sources**: TeX 1845–1875 (verbatim quotes at L5.2.6/7).
- **Blueprint**: wire `interp-nontame`-adjacent definition nodes (μ_θ/ζ_η).
- **Sizing**: ~160 LOC.

### [T516] **MILESTONE: RJW Theorem 5.7** — ∃! ζ_η
- **Status**: open | **File**: NonTame.lean | **Depends on**: CLEANUP-ALL-4
- **Type**: theorem
- **Statement**: existence (T515) + uniqueness via determinacy (L5.2.8's
  recorded design: χ-quantifier through 𝓞_ℂp-baseChange; statement form
  fixed in TW6 skeleton per decomposition).
- **Sources**: TeX 1773–1776 (verbatim at R5.2 head).
- **Blueprint**: wire `interp-nontame`; re-render.
- **Sizing**: determinacy ~120 LOC + assembly ~60.

### [CLEANUP-ALL-4] Pre-milestone /cleanup-all
- **Status**: open | **Depends on**: T515 | **Type**: cleanup-all (before T516)

### [T517] Teichmüller character ω
- **Status**: open | **File**: Interpolation/Branches.lean | **Depends on**: none
- **Parallel**: yes (chain C head) | **Type**: def + API
- **Statement**: skeleton `PadicInt.teichmullerFun` + 6 API sorries +
  `teichmuller` packaging (L5.3.1).
- **Proof sketch**: decomposition L5.3.1 (limit of x^{p^n}; Cauchy via
  Fermat+binomial induction; fixed points; multiplicativity by limit-algebra;
  PR candidate `PadicInt.teichmuller`).
- **Mathlib lemmas**: `CompleteSpace`-limit API (`CauchySeq.tendsto_limUnder`),
  `ZMod.pow_card_sub_one_eq_one`/Fermat (`ZMod.pow_card`), `PadicInt.toZModPow`
  congruence API.
- **Sources**: Def 5.15 TeX 1899–1905 (verbatim at R5.3).
- **Blueprint**: wire the chapter's ω-definition node (§5.3 part — locate
  label in Interpolation.lean tail).
- **Sizing**: ~120 LOC.

### [T518] ⟨·⟩ and y^s on 1+pℤ_p
- **Status**: open | **File**: Branches.lean | **Depends on**: T517 | **Type**: def + API
- **Statement**: skeleton angleUnit cluster (L5.3.2) + onePAdicPow cluster
  (L5.3.3 — built on `PadicInt.addChar_of_value_at_one`; replan note: source's
  exp/log definition realised by character-uniqueness; the Lem 5.14 blueprint
  node stays UNWIRED with rationale comment).
- **Mathlib lemmas**: `PadicInt.addChar_of_value_at_one`,
  `PadicInt.continuousAddCharEquiv` (uniqueness for mul_base/natCast),
  binomial-coefficient norm bounds.
- **Sources**: TeX 1892–1905 (verbatim at R5.3).
- **Sizing**: ~140 LOC.

### [T519] **MILESTONE: branches ζ_{p,i} and RJW Theorem 5.17**
- **Status**: open | **File**: Branches.lean | **Depends on**: T518, CLEANUP-ALL-5
- **Type**: def + theorem
- **Statement**: skeleton `branchChar`, `branchChar_natCast`, `zetaPBranch`,
  `zetaPBranch_interpolation` (L5.3.4–6; pairing through the §4
  IsPseudoMeasure witnesses at the T037 generator — pairChar sub-lemma
  `integral_char_dirac_mul` L5.3.5).
- **Sources**: TeX 1907–1924 (verbatim at R5.3).
- **Blueprint**: wire the ζ_{p,i}/Thm 5.17 nodes; re-render.
- **Sizing**: ~150 LOC.

### [CLEANUP-ALL-5] Pre-milestone /cleanup-all
- **Status**: open | **Depends on**: T510, T516, T518 | **Type**: cleanup-all (before T519/T520)

### [T520] L_p(θ,s) and RJW Theorem 5.19
- **Status**: open | **File**: Branches.lean | **Depends on**: T519, T516 | **Type**: def + theorem
- **Statement**: `LpFunction θ s` (genuine integral against ζ_η) +
  `Lp_interpolation` (L5.3.7; eq:alternative route; ω-as-Dirichlet-character
  bridge `teichmullerChar` sub-leaf).
- **Sources**: TeX 1929–1957 (verbatim at R5.3).
- **Blueprint**: wire the L_p/Thm 5.19 nodes; re-render; chapter complete
  except Mellin-dependent prose nodes (rationale comments).
- **Sizing**: ~130 LOC.

### [T521] p-adic exponential: convergence, isometry, functional equation
- **Status**: open | **File**: PadicLFunctions/PadicExp.lean | **Depends on**: none
- **Parallel**: yes (chain D head; user-added cluster) | **Type**: def + lemmas
- **Statement**: skeleton sorries E1–E3 (`summable_iff_tendsto_cofinite_zero`,
  `norm_factorial_le`, `padicExp_zero`, `norm_padicExp_sub_padicExp`,
  `norm_padicExp_sub_one`, `padicExp_add`).
- **Proof sketch**: decomposition R5.E (E1 partial-sum Cauchy; E2 Legendre via
  mathlib `padicValNat` factorial API; E3 isometry termwise-strict on the OPEN
  ball + tsum_prod/antidiagonal for exp_add — NOT norm-summable Cauchy
  products, attack-pinned).
- **Mathlib lemmas**: `padicValNat`-factorial family (verify exact:
  `Nat.Prime.factorization_factorial`/`sub_one_mul_padicValNat_factorial`),
  `Summable.tsum_prod`, `tsum_comm`, `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`,
  `Padic.norm_eq_zpow_neg_valuation`.
- **Sources**: TeX 1892–1897 (verbatim at R5.E) + Cassels §12/Washington §5.1
  (cross-refs recorded).
- **Generality**: over the §5 coefficient field L (ℚ_p-instance for Lem 5.14);
  radius-form statements p-uniform, pℤ_p-forms p ≠ 2.
- **Blueprint**: none yet (T523 wires Lem 5.14).
- **Sizing**: ~180 LOC (Washington's §5.1 proofs span ~1.5 pages).

### [T522] p-adic logarithm and exp/log inversion
- **Status**: open | **File**: PadicExp.lean | **Depends on**: T521 | **Type**: lemmas
- **Statement**: skeleton E4 sorries (`padicLog_one`, `norm_padicLog`,
  `padicExp_padicLog`, `padicLog_padicExp`, `padicLog_mul`).
- **Proof sketch**: decomposition E4 (series composition with ultrametric
  Fubini — Washington Prop 5.3 route, attack-pinned; log_mul from exp_add +
  injectivity-of-exp via isometry).
- **Sources**: as T521.
- **Sizing**: ~150 LOC (the composition is the meaty half).

### [T523] RJW Lemma 5.14 as stated + equivalence with the character route
- **Status**: open | **File**: PadicExp.lean | **Depends on**: T522, T518 | **Type**: theorem
- **Statement**: skeleton pZp-section sorries (`padicExp_converges_on_pZp`,
  `pZpExp`/`pZpLog` integral versions + membership lemmas,
  `padicExp_smul_padicLog_eq_onePAdicPow`).
- **Proof sketch**: decomposition E5 (ball inclusion p odd; integrality via
  isometry; equivalence by `PadicInt.continuousAddCharEquiv` uniqueness +
  `padicExp_add` + `padicExp_padicLog` at s = 1).
- **Sources**: TeX 1892–1897 (the Lem 5.14 statement realised literally).
- **Blueprint**: WIRE the chapter's Lem 5.14 node (the exp-statement node —
  locate label in Interpolation.lean §5.3 region) → `padicExp_converges_on_pZp`
  + `padicExp_smul_padicLog_eq_onePAdicPow`; replaces the planned
  unwired-rationale (user-approved cluster).
- **Sizing**: ~100 LOC.

### [CLEANUP-54] /cleanup on PadicExp.lean (3 tickets on file → cadence + final)
- **Status**: open | **Depends on**: T523 | **Type**: cleanup

### [CLEANUP-53] Final per-file cleanups (§5 files)
- **Status**: open | **Depends on**: T520 | **Type**: cleanup (Characters,
  GenBernoulli[Complex], Twist, TameConductor, NonTame, Branches — final pass
  each; then update CLEANUP-FINAL's scope to include §5)

## §5 dependency quick-view
```
chain A: TW1 → TW2 → TW3 → CLW1 → TW4 → TW5 → TW6 → CLW2
chain B: T501 T502 T503 (free) → T504 → T505;
chain C: T517 → T518 (free)
chain D: T521 → T522 → (T518) → T523 → CL54 (free until T523's T518-dep)
TW6+T502 → T506 → T507 → (T501) → T508 → CL51 → (T504) → T509 → CLALL3 → T510*
TW6+T501 → T511 → T512(T504) , T513 → CL52 → T514 → T515(T508) → CLALL4 → T516*
T518 → (CLALL5) → T519* → (T516) → T520 → CL53 → [CLEANUP-FINAL widened]
```
Cadence audit: PadicExp 3/1 ✓ (CL54); Twist 3/1 ✓; NonTame 6/2 ✓ (CL52 + final in CL53);
TameConductor 2/1(final in CL53) ✓; Branches 4/1+final ✓; GenBernoulli 2+1
(final in CL53) ✓; Characters 2 (final in CL53) ✓; pre-milestone cleanup-alls
×3 ✓; CLEANUP-FINAL retained as global last ✓.
