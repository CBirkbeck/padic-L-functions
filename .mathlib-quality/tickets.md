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
- **Scope widened 2026-06-11 (CL53/CL54/W2 fold-in)**: §3 Measure/* (the
  CLEANUP-W2 final per-file pass), §5 Interpolation/* incl. the new
  LpFunction.lean, and PadicExp.lean. Specific queued debt:
  `master_bridge`'s maxHeartbeats 400000 (PadicExp.lean), per-decl golf of
  the degraded-mode tickets (T519, T520, T521–T523), the `show`-linter
  pattern project-wide, and the CLEANUP-FINAL items from the §4 handover
  (psi-as-LinearMap, delQ→del merge, mahlerTransform_sub/smul placement,
  instIsDomain/SMulCommClass placement). Widened 2026-06-12 (CL67 fold-in):
  + §6 files (ExtLog, MeasureR/FormalPsi, ValuesAtOne[Complex]);
  crt_collapse decompose-candidate; T618-layer placement review.
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
- **Status**: done (degraded — subsumed by CLEANUP-FINAL, 2026-06-11)
- **Depends on**: TW6 | **Type**: cleanup (final per-file ×6)
- **Progress**:
  - 2026-06-11: sequenced with the final cleanup block (CL53/CL54/
    CLEANUP-FINAL): §5 consumers were still adding to Measure/* through T516
    (extendByZero factorisation in Basic.lean), and the per-decl golf needs a
    lean-lsp-tooled session. Linter-set is green on Measure/* as of the
    ALL-5 sweep (2026-06-11). Not a mainline blocker.

### [T501] Gauss sums: product formula at general level + norm-one
- **Status**: done (2026-06-10T21:40Z)
- **Progress**: BOTH lemmas proven, zero sorries in their section.
  gaussSum_mul_gaussSum_inv (Rem 5.3(i) at general level N, domain target —
  the planned 4-sum collapse: mulShift-of-primitive backwards, sum swap,
  AddChar.sum_mulShift orthogonality; MATHLIB-PR CANDIDATE).
  norm_gaussSum_eq_one (torsion-values ultrametric bound + product formula +
  ‖D‖=1; helper norm_eq_one_of_pow_eq_one for normed fields, also PR-shape).
  BLUEPRINT: interp-gauss-sum → mathlib gaussSum; interp-gauss-sum-properties
  → {PadicLFunctions.gaussSum_mul_gaussSum_inv, gaussSum_mulShift_of_isPrimitive}
  with prose note on the cleared form; blueprint builds. VERIFICATION:
  axioms standard (lean_verify), build green. | **File**: Interpolation/Characters.lean | **Depends on**: none
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
- **Status**: done (2026-06-10T22:05Z)
- **Progress**: all 5 sorries discharged: continuity via locally-constant
  fibres (reusing §3 isOpen_toZModPow_fiber), vanishing on pℤ_p (p∣x +
  isUnit_of_mul_isUnit_left + coprime-self contradiction), multiplicativity
  (REPLAN: hypothesis-free — MulChars are unconditionally multiplicative;
  the skeleton's 1 ≤ n dropped), isLocallyConstant, norm ≤ 1 (REPLAN:
  specialised to ball-valued characters where it is the subtype bound; the
  general-R form was unprovable-or-vacuous — recorded). Characters.lean now
  fully sorry-free. Axioms standard, build green. | **File**: Interpolation/Characters.lean | **Depends on**: none
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
- **Status**: done (2026-06-10T22:55Z)
- **Progress**: all three proven. genBernoulli_one (B_{k,1} = bernoulli' k via
  bernoulli_eval_one). genBernoulli_eq_zero (parity): level-one branch via
  bernoulli'_odd_eq_zero; main branch via the ZMod-indexed sum (image-bijection
  a ↦ a+1 with boundary terms killed by χ(0)=0), Equiv.neg reflection with
  ZMod.val_neg_of_ne_zero, and the mapped reflection identity
  bernoulli_eval_one_sub through algebraMap ℚ L; factor 2 ≠ 0 (CharZero).
  prod_primitiveRoot_mul_sub_one: STATEMENT CORRECTED at proof time — the
  skeleton form was FALSE for even M ((Y−1)(−Y−1) = 1−Y²); hypothesis Odd M
  added (faithful: used only at M = p^n, p odd); proof via Kummer
  X_pow_sub_C_eq_prod evaluated at 1 + Finset.prod_neg + Odd.neg_one_pow.
  Recorded as a decomposition-attack miss (L5.1.10c didn't try even M).
  VERIFICATION: build green, axioms standard. | **File**: Interpolation/GenBernoulli.lean | **Depends on**: none
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
- **Status**: done | **File**: GenBernoulli.lean | **Depends on**: T503 | **Type**: lemma
- **Progress**: DONE 2026-06-10. Route refined at execution: instead of
  per-coefficient bernoulliPowerSeries bookkeeping, used mathlib's
  `Polynomial.bernoulli_generating_function (t)` directly at `t = (a+1)/N`,
  hit with the ring hom `rescale (N : L)` (rescale_rescale +
  div_mul_cancel₀ collapses `rescale N ∘ rescale ((a+1)/N) = rescale (a+1)`;
  rescale_X gives the `C N` factor), then χ-weighted sum over `a ∈ range N`
  and cancellation of `C N` (domain, `mul_left_cancel₀`). The coefficient
  identification `C N · mk(B_{k,χ}/k!) = Σ_a χ(a+1) • rescale N (GF_a)` is
  `ext k` + zpow collapse `N^k = N·N^{(k:ℤ)−1}` (`zpow_sub_one₀`) +
  aeval→eval-of-map conversion (`map_smul`, `Algebra.smul_def`, targeted
  `map_natCast (algebraMap ℚ L) k.factorial` — the untargeted form matched
  χ↑(a+1) and stuck on a RingHomClass goal) + `ring`. GenBernoulli.lean now
  SORRY-FREE; also fixed deprecated `bernoulli'_odd_eq_zero` →
  `bernoulli'_eq_zero_of_odd` in T503's proof. Verification: zero
  diagnostics; axioms = {propext, Classical.choice, Quot.sound} on
  genBernoulliPowerSeries_mul (scan_source clean). No blueprint node
  (Washington-sourced internal identity).
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

### [T505a] Sawtooth boundary: sinZeta(x,1) = π(1/2−x) and hurwitzZeta at s=0
- **Status**: done | **File**: Interpolation/Sawtooth.lean (new) | **Depends on**: none
- **Progress**: DONE 2026-06-10. Sawtooth.lean (~740 lines): port compiled with
  only 3 cast-juggling fixes (Tendsto.comp eta-mismatch → plain `exact`;
  push_cast before ring in the ζ_O(x,0) endgame; `map_inv₀` not `map_div₀` for
  algebraMap ℚ ℂ 2⁻¹). All four mathlib dependencies present in pin
  (tendsto_tsum_powerSeries_nhdsWithin_lt, hasSum_taylorSeries_neg_log,
  Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded,
  hasSum_nat_sinZeta). New beyond the port: `unitAddCircle_coe_ne_zero`,
  `hurwitzZetaOdd_apply_zero_of_mem_Ioo` (ζ_O(x,0) = 1/2−x via
  hurwitzZetaOdd_one_sub at s=1 + Gamma_one + cpow_neg_one + sin π/2),
  `hurwitzZeta_neg_nat_of_mem_Ioo` (all k ≥ 0; docstring records the genuine
  x=0 boundary failure ζ(0) = −1/2 ≠ −B₁(0)). 13 over-length lines repacked;
  lake build green. Axioms = {propext, Classical.choice, Quot.sound} on
  sinZeta_one_eq_boundary (scan clean) and hurwitzZeta_neg_nat_of_mem_Ioo.
  Mathlib PR candidate alongside T505.
- **Spawned by**: T505 (beastmode A1, 2026-06-10) — mathlib gap: `hurwitzZeta_neg_nat`
  requires `k ≠ 0` (mathlib's own TODO: "formula also correct for k = 0; current
  proof does not work"); the missing ingredient is the conditionally-convergent
  sawtooth value `sinZeta x 1 = π(1/2 − x)` on `(0,1)` (Dirichlet-test/Abel
  boundary argument, no absolutely-convergent route).
- **Statement**: port of flt-regular-bernoulli `LValueAtOne/{DirichletBounds,
  ComplexBounds-general-part,Sine}.lean` (user's own repo, sorry-free, same
  author/licence): Dirichlet-test partial-sum bounds; `sinZeta_one_eq_boundary
  {x} (0<x) (x<1) : sinZeta x 1 = π(1/2−x)`; NEW composition lemmas
  `hurwitzZetaOdd_apply_zero_of_mem_Ioo : hurwitzZetaOdd x 0 = 1/2 − x` (via
  `hurwitzZetaOdd_one_sub` at s=1: ζ_O(x,0) = 2(2π)⁻¹Γ(1)sin(π/2)·sinZeta x 1)
  and `hurwitzZeta_apply_zero_of_mem_Ioo : hurwitzZeta x 0 =
  −((bernoulli 1).map (algebraMap ℚ ℂ)).eval x` (even part 0 on (0,1) by
  `hurwitzZetaEven_apply_zero`) — closing mathlib's k=0 TODO for interior x.
- **Mathlib lemmas**: `HurwitzZeta.hasSum_nat_sinZeta`,
  `differentiableAt_sinZeta`, `hurwitzZetaOdd_one_sub`,
  `hurwitzZetaEven_apply_zero`, `geom_sum_eq`, `UniformCauchySeqOn` API.
- **Sources**: port provenance flt-regular-bernoulli (survey addendum,
  plan.md); the mathematical content is the classical Abel-limit evaluation of
  Σ sin(2πnx)/n (Washington Ch. 4 territory).
- **Sizing**: ~700 LOC port + ~60 new.

### [T505] Complex bridge: L(χ,−k) = −B_{k+1,χ}/(k+1)
- **Status**: done | **File**: GenBernoulliComplex.lean | **Depends on**: T503, T505a
- **Progress**: DONE 2026-06-10. `LFunction_neg_nat` proven for ALL k ≥ 0
  (the planned statement, unrestricted — the k=0 gap that spawned T505a is
  closed). N=1 branch: level_one + LFunction_modOne_eq +
  riemannZeta_neg_nat_eq_bernoulli' + genBernoulli_one + eq_ratCast. N>1
  branch: unfold LFunction/ZMod.LFunction (simp only with def names),
  cpow_natCast; termwise hurwitzZeta values (j = 0 killed by χ(0) = 0 — this
  is what confines to the OPEN interval where T505a applies; j ≠ 0 via
  toAddCircle_apply + hurwitzZeta_neg_nat_of_mem_Ioo); NEW REUSABLE LEMMA
  `genBernoulli_eq_zmod_sum` extracted from T503's hsum_eq block (range-sum =
  ZMod-sum bijection; genBernoulli_eq_zero refactored to consume it — net
  ~35 lines saved, both compile); endgame eq_div_iff + sum_mul +
  sum_neg_distrib + per-term field_simp. Verification: lake build green
  (full PadicLFunctions incl. new Sawtooth import in root); axioms =
  {propext, Classical.choice, Quot.sound} on LFunction_neg_nat (scan clean).
  Blueprint: `interp-dirichlet-integral` left unwired with the
  kl-values-of-zeta-pattern rationale comment naming LvalNeg /
  LFunction_neg_nat / sinZeta_one_eq_boundary (no chapter node states the
  bare value identity). PR candidate.
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
- **Status**: done | **File**: Interpolation/Twist.lean (TW6 skeleton) | **Depends on**: TW6, T502
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
- **Progress**: DONE 2026-06-10. `isClopen_toZModPow_fiber` delegated to the
  pre-existing `PadicMeasure.isClopen_toZModPow_fiber` (PseudoMeasure.lean —
  planner had restated it). `twist_res_units` via χ̃·1_{units} = χ̃ pointwise
  (unit: indicator 1; non-unit: `toContinuousMapZp_eq_zero`), with the
  congrArg-Subtype.val bridge after `ext`. `mahlerTransform_charTwist`
  (coefficientwise z-twist formula): apply_eq_tsum + per-m finite identity
  Δ^m[κ_r·binom(·,n)](0) = [X^n]((1+X)(1+r)−1)^m — both sides expanded to
  Σ_{i≤m} (−1)^{m−i}·C(m,i)·(1+r)^i·C(i,n) via fwdDiff_iter_eq_sum_shift and
  Commute.add_pow; new API `charCM_natCast` (κ_r(↑k) = (1+r)^k, the
  onePAdicPow_natCast pattern); coeff of (1+X)^i via Polynomial-cast
  (binomialSeries route blocked: no BinomialRing instance on integerRing K).
  Linter clean (omits added, show→change). Verification: zero errors, only
  T507/T508 sorries remain in the file; axioms = {propext, Classical.choice,
  Quot.sound} on mahlerTransform_charTwist. Blueprint: `interp-twist` wired to
  {MeasureR.twist, MeasureR.twist_res_units} with prose note; build green.

### [T507] Cleared restriction formula (EqRestrictionFormula)
- **Status**: done | **File**: Twist.lean | **Depends on**: T506 | **Type**: lemma
- **Progress**: DONE 2026-06-10. New helpers `norm_pow_sub_one_lt_one`
  (‖ζ^c−1‖ < 1 for ALL c — orderOf-case-split to p^j, j ≥ 1 via
  Nat.dvd_prime_pow, transported through the subring inclusion by
  map_of_injective, then W2 `IsPrimitiveRoot.norm_sub_one_lt`) and
  `tendsto_pow_pow_sub_one` (fills the skeleton's inline `(by sorry)`
  convergence hole). Main proof exactly the decomposition route: the
  orthogonality identity proven as an equality of *continuous maps*
  `p^n • 1_{b+p^nZp} = Σ_c ζ^{cs} • κ_{ζ^c−1}` via `Continuous.ext_on` over
  dense ℕ (per-ℕ: terms collapse to `(ζ^{s+m})^c` and either all-ones
  (Finset.sum_const) or geometric-sum-zero via `geom_sum_mul` + domain);
  membership bridge ζ^{s+m} = 1 ↔ toZModPow n m = b via pow_eq_one_iff_dvd +
  ZMod.natCast_eq_zero_iff cast-arithmetic. Integration step: LinearMap.ext +
  map_smul/map_sum/smul_mul_assoc shuffles. `hn` unused by the proof
  (degenerate-true at n = 0) — kept in the statement (source-faithful),
  underscored. Verification: only the T508 sorry remains in the file; axioms =
  {propext, Classical.choice, Quot.sound}; linter-clean; lake build green.
  Blueprint: §3 deferred nodes now wired — `meas-mult-by-zx` →
  {MeasureR.cmul, mahlerTransform_charTwist}, `meas-restriction` gains
  `res_class_eq_sum_twists`, both with cleared-form prose notes.
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
- **Status**: done | **File**: Twist.lean | **Depends on**: T507, T501 | **Type**: lemma
- **Progress**: DONE 2026-06-10, FIRST-PASS COMPILE. Route refinement (recorded):
  instead of the composition χ̃-decomposition → L5.1.7 → swap → Gauss(ii), proved
  the pointwise Gauss–Fourier expansion `G(χ⁻¹)•χ̃ = Σ_c χ⁻¹(c)•κ_{ζ^c−1}`
  directly as a continuous-map identity (same Continuous.ext_on-over-ℕ frame as
  T507 — the same algebra with the L5.1.7 steps merged at the pointwise level):
  at naturals the right side is `gaussSum χ⁻¹ (e.mulShift m)` (range↔ZMod-univ
  bridge by Finset.sum_nbij' val/natCast; `AddChar.zmodChar_apply'` gives the
  ζ^{cm}-form), evaluated by mathlib's `gaussSum_mulShift_of_isPrimitive` —
  which covers non-unit m with the vanishing built in — then `inv_inv`;
  χ⁻¹-primitivity via `DirichletCharacter.conductor_inv`. Integration assembly
  identical to T507. Statement exactly the planning-pinned form (no extra sign,
  range-sum). Twist.lean now SORRY-FREE. Verification: zero diagnostics
  project-wide on the file; axioms = {propext, Classical.choice, Quot.sound}
  (scan clean); lake build green. Blueprint: `interp-mahler-twist` wired with
  cleared-form prose note.
- **Statement**: `mahler_twist_formula` per L5.1.8 — statement form pinned by
  the planning trace (G(χ⁻¹)-cleared, NO extra sign; see L5.1.8 attack [2]).
- **Proof sketch**: decomposition L5.1.8 composition (χ̃-decomposition →
  L5.1.7 → swap → Gauss (ii) → (i)).
- **Sources**: TeX 1675–1692 (verbatim quote + the source's 3-display algebra).
- **Blueprint**: wire `interp-mahler-twist` (prose note: cleared form).
- **Sizing**: source proof 12 lines ⟹ ~110 LOC.

### [CLEANUP-51] /cleanup on Twist.lean (cadence: 3 tickets)
- **Status**: done | **Depends on**: T508 | **Type**: cleanup
- **Progress**: DONE 2026-06-10 (inline during T506–T508 + final sweep): zero
  diagnostics (all unused-section-var omits added, show→change, unused
  hypotheses underscored), all lines ≤ 100, naming conventions verified,
  docstrings on all public declarations, module docstring current. Golf note
  for CLEANUP-FINAL: the two Continuous.ext_on-over-ℕ frames (T507/T508
  hpoint) could share a `ContinuousMap.ext_natCast` helper if a third use
  appears.

### [T509] Moments of the twisted measure (F_{χ,a}-values)
- **Status**: done | **File**: Interpolation/TameConductor.lean (+GenBernoulli) | **Depends on**: CLEANUP-51, T504
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
- **Progress** (2026-06-10, route analysis at execution start): the assembly
  needs the substitution `F ↦ F(C(1+r)·(1+X) − 1)` as a RING HOM on
  `(integerRing K)⟦X⟧` (the decomposition's PRIMARY eval₂ route for L5.1.6 —
  T506 took the coefficientwise fallback, which does not compose through the
  product-identities of the F_a algebra). Plan: (i) sub-step `substAffine`:
  mathlib `PowerSeries.eval₂`-style topological evaluation
  (Mathlib.RingTheory.PowerSeries.Evaluation — verify exact API: eval₂Hom /
  HasEval) at `a := C(1+r)·(1+X) − 1 ∈ R⟦X⟦` over the Pi-topology
  (WithPiTopology instances; R = integerRing K is complete + IsLinearTopology
  by TW1/Coefficients.lean; `a` is topologically nilpotent since r is —
  coefficientwise r-power bounds); (ii) upgrade: `mahlerTransform_charTwist'`:
  `𝓐(κ_r μ) = substAffine r (𝓐 μ)` — coefficientwise from the T506 tsum
  formula vs the eval₂-coefficient limit; (iii) per-c: apply substAffine to
  §4's cleared F_a-identity (`one_add_X_pow_sub_one_mul_Fa`, base-changed to
  K) to get the c-shifted cleared identities — NOTE: individual divisibility
  `(1+X)ζ^c−1 ∣ (1+X)^{p^n}−1` is parity-free (geom-factorisation), the
  Odd-M product formula (10c, `prod_primitiveRoot_mul_sub_one`) may be
  avoidable; (iv) Σ_c with χ⁻¹-weights + T508 identifies
  `G(χ⁻¹)·𝓐(twist χ̃ μ_a)`; (v) ∘(e^t−1) (formal, HasSubst ✓) + T504's
  `genBernoulliPowerSeries_mul` + §4 bridge `constantCoeff_iterate_delQ` +
  `apply_powCM` (MeasureR) extract the moment. Sub-steps (i)/(ii) are the next
  concrete edits (new section in Twist.lean or a new SubstAffine.lean file —
  prefer new file `PadicLFunctions/MeasureR/SubstAffine.lean`).
  UPDATE (same day): sub-steps (i)+(ii) DONE — placed in Twist.lean (new
  `section substAffine`, cohesion with the L5.1.6 material won over the new
  file): `hasEval_affine` (HasEval.map continuous_C + HasEval.X.mul_left over
  scoped PowerSeries.WithPiTopology; mop-IsLinearTopology instance derived via
  `IsCentralScalar.isLinearTopology_iff` — consider moving to Coefficients.lean
  at cleanup), `substAffine := PowerSeries.eval₂Hom continuous_C hasEval_affine
  : R⟦X⟧ →+* R⟦X⟧`, `coeff_substAffine` (hasSum_eval₂ mapped through the
  continuous coeff), `mahlerTransform_charTwist_eq_substAffine` (L5.1.6 in the
  source's ring-hom form: 𝓐(κ_r μ) = substAffine r (𝓐 μ)). All compile, build
  green, linter-clean. NEXT: step (iii) — base-change §4's
  `one_add_X_pow_sub_one_mul_Fa` to K and hit it with `substAffine (ζ^c−1)`
  (ring hom ⟹ identity transports); then (iv) Σ_c χ⁻¹(c)-weights + T508; then
  (v) ∘(exp−1) formal subst + T504 + `constantCoeff_iterate_delQ`-bridge over K
  + MeasureR `apply_powCM` to extract `twist_muA_moments`. Note for (v): the
  §4 bridge lemmas (map_del, derivativeFun_subst_exp, constantCoeff_iterate_*)
  are stated over ℚ_[p] in MuA.lean — the K-analogues need restating over K
  (same proofs; the field K plays ℚ_[p]'s role; `del K` exists in
  MeasureR/Toolbox).
  STEP (iii) DONE (2026-06-10): `substAffine_X`/`substAffine_C`/
  `substAffine_one_add_X` API in Twist.lean; per-c identity
  `charTwist_muA_mahler_identity` in TameConductor.lean:
  `(C(ζ^{ca})(1+X)^a − 1)·𝓐(κ_{ζ^c−1}(μ_a)_K) = substAffine (ζ^c−1)
  (map geomSum) − a` — proven by hitting the K-mapped §4 identity with the
  substAffine ring hom (simp only [map_*] + the C-power regroup). Build green.
  STEP (iv) ALSO DONE (same day): `substAffine_map_geomSum`
  (S_c(geomSum) = Σ_i C(ζ^{ci})(1+X)^i — NOTE: sequential rw, not simp; simp
  splits 1+X before the composite substAffine_one_add_X can fire) and
  `charTwist_muA_exp_identity` (‡c) in TameConductor.lean:
  `(C(ζ_K^{ca})·rescale a exp − 1)·H_c = Σ_{i<a} C(ζ_K^{ci})·rescale i exp − a`
  in K⟦t⟧, where H_c := (map subtype 𝓐(κ_c(μ_a)_K)).subst (exp K − 1).
  Proven by the §4 X_mul_subst_exp_Fa idiom: map-to-K (simp with
  PowerSeries.map_C + Subring.coe_subtype), then congrArg (substAlgHom hg) with
  the simp set [hX, hC := (substAlgHom hg).commutes, 1+(exp−1)=exp,
  exp_pow_eq_rescale_exp, coe_substAlgHom]; final `simpa only [map_pow]`
  aligns the C-pow normal forms (simp pulls pow out of C). hg over K via
  HasSubst.of_constantCoeff_zero'. Build green.
  STEP (v) SUB-DECOMPOSITION (recorded 2026-06-10, derived on paper —
  supersedes the sketchier refinement below; notation: ζ' := (ζ:K),
  E_j := rescale (j:K) (exp K), χ̄ := toFieldChar χ, H_c as in (‡c),
  G' := gaussSum (toFieldChar χ)⁻¹ (zmodChar _ (ζ'-pow-proof))):
  (v-a) `sum_inv_char_zeta_pow`: Σ_{c<p^n} χ̄⁻¹(c)·ζ'^{cj} = χ̄(j)·G' — the
    T508 Gauss-collapse re-derived K-valued (sum_nbij' range↔ZMod +
    zmodChar_apply' + gaussSum_mulShift_of_isPrimitive + inv_inv; primitivity
    of (ζ:K) via map_of_injective, of χ̄ via... toFieldChar preserves
    IsPrimitive — small lemma needed: conductor under ringHomComp with
    INJECTIVE hom is preserved [verify mathlib has conductor_ringHomComp or
    prove via FactorsThrough]).
  (v-b) division-algorithm reindex: Σ_{i<a}Σ_{j<p^n} f(i+a·j) =
    Σ_{m<a·p^n} f(m) (Finset.sum_nbij' (i,j)↦i+aj, m↦(m%a,m/a) on
    range a ×ˢ range p^n — or sum_sigma; needs a > 0 ✓ from hpa).
  (v-c) exp-block identities: E_x·E_y = E_{x+y}
    (mathlib `PowerSeries.exp_mul_exp_eq_exp_add` — verify name) and
    (E_b)^l = E_{lb} (exp_pow_eq_rescale_exp + rescale_rescale-induct).
  (v-d) T504-reindex at K, level p^n: X·Σ_{j<p^n}χ̄(j)E_j =
    genBPS_χ̄·(E_{p^n}−1), where genBPS := mk(B_{k,χ̄}/k!) — from
    genBernoulliPowerSeries_mul (T504) by the b+1↔j boundary-shift (χ̄(0) =
    χ̄(p^n-as-0) = 0; THIRD occurrence of the T503 bijection — consider
    factoring a `Finset.sum_range_succ_shift`-style reusable bridge).
  (v-e) MASTER ASSEMBLY: multiply (‡c) by Σ_{j<p^n}(C(ζ'^{ca})E_a)^j, sum
    against χ̄⁻¹(c) over c<p^n (c=0 drops via χ̄⁻¹(0)=0): LHS telescopes to
    (E_{ap^n}−1)·Σ_cχ̄⁻¹(c)H_c [geom_sum_mul]; RHS double-sum reindexes by
    (v-b) then collapses by (v-a) to G'·[Σ_{m<ap^n}χ̄(m)E_m − a·χ̄(a)·rescale
    a (Σ_{j<p^n}χ̄(j)E_j)]; block-split (v-c) + (v-d) + geom-telescope give
    RHS = G'·(E_{ap^n}−1)·[genBPS − χ̄(a)·rescale a genBPS]·X⁻¹-shape; after
    multiplying through by X and cancelling (E_{ap^n}−1) ≠ 0 (coeff-1 check,
    §4 hreg-pattern; K⟦t⟧ domain):
    **X·Σ_cχ̄⁻¹(c)H_c = G'·(genBPS_χ̄ − χ̄(a)·rescale (a:K) genBPS_χ̄)** —
    the exact χ-analogue of §4's X_mul_subst_exp_Fa. Then T508
    (map+subst-transported: Σ_cχ̄⁻¹(c)H_c = (G_R:K)·H_χ with (G_R:K) = G' via
    subtype-of-finite-sum) + G' ≠ 0 (T502 norm_gaussSum_eq_one) cancel to
    **X·H_χ = genBPS_χ̄ − χ̄(a)·rescale a genBPS_χ̄** (FINAL-10b).
  (v-f) moment extraction = §4 muA_apply_powCM tail over K: need K-analogues
    of MuA's bridge cluster (delQ-K := (1+X)·derivativeFun over K [MeasureR
    `del K` is the integerRing-level one], map_del-K [subtype-map commutes
    with del], derivativeFun_subst_exp-K, constantCoeff_subst_exp-K,
    constantCoeff_iterate_delQ-K — copy MuA.lean proofs verbatim with K for
    ℚ_[p]) + MeasureR.apply_powCM; coeff_{k+1} of FINAL-10b: LHS
    coeff_succ_X_mul → coeff_k H_χ → k!⁻¹-cleared moment of twist χ̃ μ_aK;
    RHS via coeff of genBPS (coeff_mk) = B_{k+1,χ̄}/(k+1)! and coeff_rescale:
    (1 − χ̄(a)a^{k+1})·B_{k+1}/(k+1)! ; factorial bookkeeping + LvalNeg
    definition give twist_muA_moments. (The −1-sign: LvalNeg = −B/(k+1);
    statement RHS −(1−χ(a)a^{k+1})·LvalNeg = +(1−χ(a)a^{k+1})·B_{k+1}/(k+1) ✓
    consistent with the §4 sign-trace.)
  (v-a)+(v-b)+(v-c) DONE (2026-06-10, all in TameConductor.lean, build green,
  committed): `sum_inv_char_zeta_pow` (K-valued Gauss collapse; primitivity
  transport `DirichletCharacter.isPrimitive_ringHomComp_iff` +
  `factorsThrough_ringHomComp_iff` added to Characters.lean — PR candidates);
  `sum_range_mul_eq_sum_range` (division-algorithm reindex via sum_nbij' on
  range a ×ˢ range N); `rescale_exp_pow` ((E_b)^l = E_{lb} by induction +
  exp_mul_exp_eq_exp_add). (v-d) ALSO DONE (same day, committed):
  `X_mul_sum_char_rescale_exp` (X·Σ_{j<p^n} C(χK(j))·E_j =
  genBPS_χK·(E_{p^n}−1); sum_range_succ'-shift, both boundaries killed by
  χK(0) = 0; note `set ... with hh` needs `simp only [hh]` not `rw [hh]` at
  use sites — beta-reduction). All v-a/b/c/d helpers in TameConductor.lean
  before twist_muA_moments, linter-clean, all committed/pushed.
  NEXT — (v-e) MASTER ASSEMBLY, steps pinned (in K⟦t⟧; E_j := rescale (j:K)
  (exp K); H_c as in charTwist_muA_exp_identity; G' the K-valued Gauss sum of
  (v-a); χ̄ := toFieldChar χ):
  STEP 1 (per-c): multiply (‡c) by Σ_{j<p^n}(C(ζ'^{ca})·E_a)^j; telescope LHS
  cofactor with geom_sum_mul + rescale_exp_pow + exp-power-juggling to get
  `(E_{ap^n} − 1)·H_c = (Σ_{i<a} C(ζ'^{ci})E_i − a)·Σ_{j<p^n}
  C(ζ'^{caj})·E_{aj}`.
  STEP 2: Σ_c χ̄⁻¹(c)-weighted sum; expand the (i,j)-product
  (ζ'^{c(i+aj)}·E_{i+aj} via exp_mul_exp_eq_exp_add); reindex
  sum_range_mul_eq_sum_range to m < a·p^n; swap Σ_c in and collapse with
  sum_inv_char_zeta_pow (at m, and at a·j for the a-term; χ̄(aj) =
  χ̄(a)·χ̄(j)): `(E_{ap^n} − 1)·Σ_c χ̄⁻¹(c)•H_c = G'·(Σ_{m<ap^n}
  C(χ̄(m))·E_m − C(χ̄(a))·a·Σ_{j<p^n} C(χ̄(j))·E_{aj})`.
  STEP 3: multiply by X; m-sum block-splits by m = m'+p^n·l (reindex again,
  roles swapped; χ̄ p^n-periodic; E-product) → X·Σ_m =
  (Σ_{l<a}(E_{p^n})^l)·genBPS·(E_{p^n}−1) = genBPS·(E_{ap^n}−1) [telescope];
  a-term via rescale (a:K) applied to (v-d): rescale a X = C a·X absorbs the
  stray a — VERIFY bookkeeping at write-time (planning trace pinned no stray
  a-factor in FINAL).
  STEP 4: cancel (E_{ap^n}−1) ≠ 0 (coeff 1 = a ≠ 0, K char-0; §4
  hreg-pattern; domain): **FINAL-10b: X·Σ_{c<p^n}χ̄⁻¹(c)•H_c =
  G'·(genBPS_χ̄ − C(χ̄(a))·rescale (a:K) genBPS_χ̄)**.
  (v-e) COMPLETE (2026-06-10, all four steps committed/pushed):
  `charTwist_muA_exp_identity_cleared` (step 1),
  `sum_char_inv_mul_exp_identity` (step 2),
  `X_mul_sum_char_inv_subst` = **FINAL-10b** (steps 3+4; hA block-split via
  the reindex with roles swapped + ZMod-period + exp-products + telescope;
  hB via the rescale-a-image of (v-d) with an inline rescale-of-C ext-lemma;
  endgame `linear_combination C(G')·hA − C(G')·hB`; the regular-factor
  cancellation via coeff-1 ≠ 0, simp leaves the disjunction a = 0 ∨ p-zero
  — rcases). LEAN NOTES for the file: fragile underscore-calcs DON'T (the
  `_`s elaborate against the wrong metas — write rw-show-chains or
  linear_combination instead).
  Then (v-f) extraction — the LAST sub-step of T509: T508 map+subst-transport
  (Σ_cχ̄⁻¹(c)·H_c = C((G_R:K))·H_χ where H_χ := (map subtype 𝓐(twist χ̃
  (μ_a)_K)).subst (exp−1); from T508 hit with map-subtype, substAlgHom at
  exp−1, and the C-image bookkeeping — note T508's statement is in
  •-smul form: (G_R • twist χ̃ μ) — map_smul through 𝓐/map/subst gives the
  C-multiple), G'-vs-(G_R:K) bridge (subtype-hom of the finite gaussSum =
  the K-valued gaussSum of toFieldChar against the K-valued zmodChar —
  small lemma, map_sum), G'-cancel (≠ 0: T502 `norm_gaussSum_eq_one` gives
  the K-valued norm 1 — check it applies to gaussSum (toFieldChar χ)⁻¹
  directly or transport), coeff_{k+1} of FINAL-10b (coeff_succ_X_mul on the
  left; coeff_mk + coeff_rescale on the right), K-bridge delQ-cluster
  restated from MuA.lean over K (hasSubst_exp_sub_one-K [done inline in ‡c
  as hg], derivativeFun_subst_exp-K, constantCoeff_subst_exp-K,
  constantCoeff_iterate_delQ-K — copy proofs with ℚ_[p] → K), MeasureR
  `apply_powCM` + `mahlerTransform_baseChange` to land twist_muA_moments.
  **T509 DONE (2026-06-10)**: `twist_muA_moments` PROVEN — the full chain
  (iii)→(iv)→(v-a..e)→(v-f) landed: per-c substAffine-transport, exp-subst,
  telescoped clearing, FINAL-10b, T508-transport, Gauss-nonvanishing (NOTE
  `mul_gaussSum_inv_eq_gaussSum` is Field-source-only, unusable at ZMod p^n;
  `AddChar.inv_mulShift` + `gaussSum_mulShift_of_isPrimitive` is the route),
  delField-bridge extraction, factorial endgame. STATEMENT REPLAN (in
  docstring): `(hζ : IsPrimitiveRoot ζ (p^n))` threaded into the statement —
  the source's ambient ε_{p^n}; T510's statements must thread it too.
  Verification: lake build green; axioms = {propext, Classical.choice,
  Quot.sound} on twist_muA_moments + all v-helpers (a first lean_verify
  returned sorryAx from a STALE LSP elaboration — re-verified clean after the
  build settled). Only T510's two skeleton sorries remain in
  TameConductor.lean.
  OLD-NEXT (superseded): (v-a) + the toFieldChar-IsPrimitive lemma in
  TameConductor.lean (or Characters.lean for the primitivity transport).
  NEXT after: step (v) per the plan above — the formal subst (exp K − 1)
  of (†c) [needs the K-analogue of §4's hasSubst_exp_sub_one + map-to-K of the
  identity], then the master identity.
  ROUTE REFINEMENT for (iii)–(v) (recorded before compaction): PARITY-FREE,
  the 10c Odd-product is NOT needed. Chain: (iii) base-change §4's
  characterising identity to K and hit with the ring hom `substAffine (ζ^c−1)`:
  since substAffine r (1+X) = C(1+r)·(1+X), this gives per-c
  `(C(ζ^{ca})(1+X)^a − 1)·𝓐(κ_c μ_K) = substAffine (geomSumK) − a` (†c);
  (iv) map to K⟦X⟧ and apply formal `subst (exp K − 1)` (ring hom; §4
  coe_substAlgHom pattern): `(ζ^{ca}·rescale a exp − 1)·H_c =
  Σ_{i<a} ζ^{ci}·rescale i exp − a` (‡c) with H_c := (map K 𝓐(κ_cμ))∘(e^t−1);
  (v) MASTER IDENTITY (all formal in K⟦t⟧, domain): multiply Σ_c χ⁻¹(c)•(‡c)
  through by the two geometric cofactors — KEY FACTS: χ⁻¹(0) = 0 drops the
  c = 0 term so every remaining denominator has unit constant term in the
  FIELD K; the geometric identities `(ζ^c e^t − 1)·Σ_{j<p^n}(ζ^c e^t)^j =
  e^{p^n t} − 1` (and the a-version) are formal and parity-free; the inner
  sums `Σ_c χ⁻¹(c)ζ^{cj} = χ(j)·G(χ⁻¹)` collapse by the SAME
  `gaussSum_mulShift_of_isPrimitive` + sum_nbij' bridge as T508 (factor that
  bridge out as a reusable lemma `sum_inv_char_pow_eq_gaussSum`-style when
  writing!); then T504's `genBernoulliPowerSeries_mul` at modulus p^n
  identifies the χ(j)e^{jt}-sums with the genBernoulli series at the two
  rescalings (j-shift b+1 as in T504's statement), and cancellation of the
  nonzero e-factors (domain K⟦t⟧, §4 hreg-pattern) yields
  `X·Σ_c χ⁻¹(c)•H_c = G(χ⁻¹)·(genBPS_χ − χ(a)·a·rescale a genBPS_χ)`-shape
  [VERIFY exact Euler-shape against the source display TeX 1697 + the
  planning trace at L5.1.10 attack [1] before stating]. Then
  `coeff_{k+1}` of both sides + the K-bridge (constantCoeff_iterate_delQ
  over K + MeasureR apply_powCM + T508 at powCM k) extracts
  `G(χ⁻¹)·∫χ̃x^k dμ_aK = G(χ⁻¹)·(−(1−χ(a)a^{k+1}))·LvalNeg`, and G(χ⁻¹) ≠ 0
  (norm 1 by T502's `norm_gaussSum_eq_one`... NOTE that's for the K-valued
  gaussSum — the integerRing-valued one: nonzero via norm = 1 through the
  subtype) cancels in the field K.

### [T510] **MILESTONE: RJW Theorem 5.1** — ∫χ(x)x^k·ζ_p = L(χ,1−k)
- **Status**: done | **File**: TameConductor.lean | **Depends on**: CLEANUP-ALL-3
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
- **Progress**: **DONE 2026-06-10 — MILESTONE: TameConductor.lean SORRY-FREE.**
  Both forms proven: `tame_conductor_theta` (θ_a-form, ∫χ̃x^k d(θ_a)_R =
  −(1−χ(a)·a^{k+1})·LvalNeg χ k via Θ-functional composition over
  twist_muA_moments) and `tame_conductor` (witness form: ∃ μ_w with
  res-units + ψ-shift properties pairing to the L-value, mirroring
  kubotaLeopoldt's encoding). Route: (1) `iota_dirac_mul` — the units-Dirac
  convolution passes through ι = σ_w dilation; (2) baseChange naturality
  pack `baseChange_pushforward` / `baseChange_cmul` / `baseChange_res`
  (BaseChange.lean; proved by ext_locallyConstant + fibre-indicator
  decomposition `locallyConstant_eq_sum_smul_charFn` via
  `Φ.isLocallyConstant.isClopen_fiber` + `LocallyConstant.range_finite`);
  (3) dilation eigenfunction `char_pow_comp_mulCM` (χ̃x^k ∘ mulCM c =
  χ̃(c)c^k • χ̃x^k); (4) nonvanishing c_u = χ(u)·u^{k+1} ≠ 1 for the chosen
  unit u via FINITE CHARACTER ORDER: χ(m̄)^N = 1 by `pow_card_eq_one'`, so
  c_u^N = m^{(k+1)N} would force topGen^{(k+1)N} = 1 in ℤ_pˣ, contradicting
  `topGen_pow_ne_one` — avoids needing 1+pℤ_p torsion-freeness. STATEMENT
  REPLAN (carried from T509, recorded in docstrings): the ambient primitive
  p^n-th root hypothesis `(hζ : IsPrimitiveRoot ζ (p^n))` threaded through
  twist_muA_moments → tame_conductor_theta → tame_conductor (source's
  ε_{p^n}, TeX ~1640). LEAN NOTES: MeasureR `pushforward` takes explicit
  K X Y; iota_dirac_mul's final rw chain closes by congr-unification —
  end with `rfl`; a first lean_verify returned sorryAx from a stale LSP
  elaboration (second occurrence this file) — grep shows 0 sorries,
  re-verify after build settle → clean. Verification: lake build green
  (3833 jobs incl. blueprint); zero sorry in TameConductor.lean; axioms on
  `tame_conductor` + `tame_conductor_theta` = {propext, Classical.choice,
  Quot.sound}. Blueprint: `interpolation-property` wired →
  tame_conductor + tame_conductor_theta + twist_muA_moments with prose
  note (witness encoding, θ-form engine, LvalNeg value encoding, ambient
  root hypothesis); `lake build PadicLFunctionsBlueprint` green.

### [CLEANUP-ALL-3] Pre-milestone /cleanup-all
- **Status**: done | **Depends on**: T509 | **Type**: cleanup-all (before T510)
- **Progress**: DONE 2026-06-10, full-project sweep (~140 linter warnings →
  0 non-sorry warnings): scripted positional fixes for 64 show→change, 30
  unused simp args, ~40 unused-section-var omits (looped to fixpoint; NOTE
  the warning columns are 0-indexed, omit-lists need bracket-aware parsing
  for `ℚ_[p]`, and `omit ... in`/`open ... in` must precede docstrings);
  flexible-simp `simp [Nat.factorial] at h1` in the two hreg-proofs
  restructured to `simpa ... using` + explicit Nat-contradiction;
  `open scoped Classical` in Characters.lean narrowed to `open Classical in`
  on toContinuousMapZp + `classical` tactic in the locally-constant proof;
  no-op push_casts removed; deprecated `AddSubmonoidClass.coe_finset_sum` →
  `coe_finsetSum`; all 28 over-100-col lines repacked (some had grown from
  show→change). Verification: lake build green (code + blueprint), zero
  non-sorry warnings project-wide, all lines ≤ 100; axiom spot-checks
  unchanged on twist_muA_moments and PadicMeasure.kubotaLeopoldt.

### [T511] F_η and μ_η (conductor D coprime to p)
- **Status**: done | **File**: Interpolation/NonTame.lean (TW6 skeleton) | **Depends on**: TW6, T501
- **Type**: def + lemmas
- **Statement**: `etaDenomUnit` (L5.2.1), `muEta` + transform characterisation
  (L5.2.2; G(η⁻¹)-unit via T501's norm lemma).
- **Sources**: TeX 1793–1798 (verbatim at L5.2.2).
- **Blueprint**: wire `interp-mu-eta`.
- **Sizing**: ~70 LOC.
- **Progress**: DONE 2026-06-10. Four declarations: (1) NEW
  `integerRing.isUnit_of_norm_eq_one` (Coefficients.lean — norm-1 element of
  the unit ball is a unit; field inverse has norm 1; NOTE mathlib renamed
  `isUnit_of_mul_eq_one` → `IsUnit.of_mul_eq_one` with {a} implicit, (b)
  explicit, and an [IsDedekindFiniteMonoid] instance arg); (2)
  `isUnit_root_mul_one_add_X_sub_one` = L5.2.1/etaDenomUnit via
  `PowerSeries.isUnit_iff_constantCoeff` + W3
  (`IsPrimitiveRoot.norm_pow_sub_one_eq_one`, needs (p := p) named since p is
  implicit there) + prim-root coe-transport `map_of_injective (f :=
  (integerRing K).subtype)`; (3) `gaussSum_isUnit_of_coprime` (the L5.2.2
  sub-leaf) via GENERALISED `coe_gaussSum_zmodChar` (TameConductor.lean:
  p^n → arbitrary [NeZero N], proof verbatim modulus-agnostic, call sites
  unchanged) + `norm_gaussSum_eq_one K` (L explicit section var!) +
  conductor_inv/isPrimitive_ringHomComp_iff primitivity transport; (4)
  `mahlerTransform_muEtaCleared` @[simp] characterisation 𝓐(muEtaCleared) =
  −Σ_c η⁻¹(c)·(ζ^c(1+X)−1)⁻¹ via `(mahlerRingEquiv p K).apply_symm_apply`
  (muEtaCleared def itself was sorry-free in the TW6 skeleton). Cleanup
  inline: omits added (also retro-fixed 3 unused-section-var warnings in
  BaseChange.lean from T510's additions), show-from wrapper golfed to direct
  rw, have-then-simpa collapsed. Verification: lake build green project-wide;
  axioms = {propext, Classical.choice, Quot.sound} on all four (one stale-LSP
  empty-axioms artifact, clean on re-verify). Blueprint: `interp-mu-eta`
  wired → all four decls with prose note (cleared-form encoding
  −G(η⁻¹)F_η, full ℤ/D sum with η⁻¹-vanishing off units); blueprint build
  green (3833 jobs).

### [T512] Moments of μ_η (Lem 5.9, p-adic half)
- **Status**: done | **File**: NonTame.lean | **Depends on**: T511, T504 | **Type**: lemma
- **Statement**: `muEta_moments` (L5.2.3): ∫x^k μ_η = LvalNeg η k.
- **Sources**: TeX 1801–1807 (verbatim at L5.2.3).
- **Blueprint**: wire `interp-eta-mellin`'s value half per node text (worker
  reads node; Mellin-statement half stays prose with rationale if present).
- **Sizing**: ~90 LOC (rides T504/T509 machinery at modulus D).
- **Progress**: DONE 2026-06-10, `muEtaCleared_moments` (cleared form:
  ∫x^k·(−G(η⁻¹)μ_η) = G(η⁻¹)·LvalNeg(ηK)(k)) via a 3-step chain mirroring
  T509 but with NO clearing factor: (1) `muEta_term_exp_identity` — T511's
  unit identity through map-subtype + substAlgHom(exp−1) (LEAN NOTE: keep
  `map_pow` OUT of the first simp set or the C-of-pow splits into (C ↑ζ)^c
  and the second simp can't push substAlgHom through — use
  `SubmonoidClass.coe_pow` to normalise ↑(ζ^c) = (↑ζ)^c instead); (2)
  `rescale_exp_sub_one_mul_muEta_term` — geom_sum_mul clearing of e^{Dt}−1,
  ζ^{cD} = 1, exp_pow_eq_rescale_exp; (3) `X_mul_muEtaCleared_subst` MASTER:
  X·H_η = −C(G')·genBPS(ηK), via η̄(0) = 0 drop (Fact (1<D) nontrivial), the
  GENERALISED `sum_inv_char_zeta_pow` Gauss collapse + GENERALISED
  `X_mul_sum_char_rescale_exp` (both TameConductor: p^n → arbitrary
  [NeZero N] modulus, X_mul… takes hN1 : 1 < N now — call sites pass
  Nat.one_lt_pow), regular-factor cancellation (coeff-1 = D ≠ 0, CharZero).
  Final: T509-endgame coeff_{k+1} extraction (apply_powCM + NEW FACTORED
  `map_subtype_del_iterate` [also refactored into twist_muA_moments,
  −10 LOC] + constantCoeff_iterate_delField), factorial algebra (LEAN NOTE:
  after `field_simp [hfact]` the goal is already in (k+1)-normal form —
  `rw [hfact]; push_cast; ring` closes; an intermediate push_cast is a
  no-op). Verification: lake build green (code + blueprint); axioms =
  {propext, Classical.choice, Quot.sound} on all four new decls (one
  stale-LSP sorryAx artifact on moments, clean on re-verify — third
  occurrence of this artifact, always re-verify). Blueprint:
  `interp-eta-mellin` wired → muEtaCleared_moments + X_mul_muEtaCleared_subst
  with prose note (cleared encoding, p-adic route via
  genBernoulliPowerSeries_mul, complex Mellin half quarantined unfomalised).

### [T513] ψ-invariance: ψ(μ_η) = η(p)·μ_η (Lem 5.10)
- **Status**: done | **File**: NonTame.lean | **Depends on**: T511 | **Type**: lemma
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
- **Progress**: DONE 2026-06-11, `psi_muEtaCleared` exactly by the ξ-free
  route. NEW W-grade API (Tier-A spawns, proven inline): Toolbox.lean gains
  `psi_phi_mul` (PROJECTION FORMULA ψ(φν·μ) = ν·ψμ — proof on test functions
  through mul_apply/convInner; pointwise case split on y ∈ pℤ_p with
  sd(px+y) = x+sd(y) via mul_shiftDiv_of_mem/shiftDiv_mul; NOTE no
  IsUltrametricDist.norm_sub_le_max in mathlib — use norm_add_le_max with
  −(px) + norm_neg), ψ-linearity pack (psi_add/smul/zero/sum — LinearMap.ext
  one-liners), `psi_dirac_of_isUnit` (via isSupportedOn_units_iff, which sits
  LATER in the file — order matters), `psi_dirac_zero`;
  MahlerTransform.lean gains `mahlerTransform_smul`/`mahlerTransform_sub`
  (via mahlerTransformₗ map_smul/map_sub). NonTame: `symm_denom_eq`
  (w(1+T)−1 read back = w•δ₁ − δ₀; binomialSeries_nat at d = 1),
  `psi_symm_inverse_denom` (ψ(γ_m) = γ_{pm}: telescope via geom_sum_mul +
  Ring.mul_inverse_cancel transform-side, ψ(Σ_j ζ^{mj}δ_j) = δ₀ via
  Finset.sum_eq_single + PadicInt.isUnit_iff/Padic.norm_natCast_eq_one_iff,
  unit-cancel IsUnit.mul_left_cancel), then the ZMod-indexed assembly
  (range↔ZMod nbij', ψ-shift x ↦ p̂x, unit-reindex). STATEMENT NOTE: hη
  (primitivity) DROPPED — the proof never uses it (linter caught it;
  generalisation recorded). LEAN NOTES: (1) `set g := fun x => ...` lambdas
  do NOT beta-reduce under rw — bridge every g-application with
  `show g a = <body> from rfl`; (2) keep `map_pow` OUT of rw-lists touching
  C(ζ^k)·(map f ((1+X)^k)) — it splits the C-of-pow first; use targeted
  `show map f ((1+X)^k) = (1+X)^k from by rw [map_pow, map_add, ...]`;
  (3) `rw [← hpu]` with hpu : ↑hu.unit = p̂ is MOTIVE-ILLEGAL (hu's type
  mentions p̂) — `obtain ⟨u, hpu⟩ := hu` first; (4) RingEquiv.symm has no
  map_smul — bridge to (mahlerLinearEquiv p K).symm via `show ... from
  map_smul ...` (defeq). Verification: lake build green (code + blueprint);
  axioms = {propext, Classical.choice, Quot.sound} on psi_muEtaCleared,
  psi_symm_inverse_denom, psi_phi_mul (one stale-LSP sorryAx artifact,
  clean on re-verify — 4th occurrence). Blueprint: `interp-psi-twisted`
  wired → psi_muEtaCleared + psi_phi_mul + psi_symm_inverse_denom with
  prose note (μ_p-free cleared-telescope route vs the node's displayed
  trace computation; η not required primitive).

### [CLEANUP-52] /cleanup on NonTame.lean (cadence: 3 tickets on file)
- **Status**: done | **Depends on**: T513 | **Type**: cleanup
- **Progress**: DONE 2026-06-11. Audit: copyright/docstring/imports ✓, no
  dividers, no set_option, 0 linter warnings (code written post-ALL-3
  discipline, omits + line-packing already in place per-ticket), all
  public decls docstringed with TeX citations, naming ✓. STRUCTURE:
  psi_muEtaCleared (~115 ln) and X_mul_muEtaCleared_subst (~110 ln) exceed
  the 50-line bar but are already decomposed into maximal named
  have-blocks; further extraction would create single-use 8-arg private
  lemmas — n/a per the TameConductor/ALL-3 precedent. Chain-step lemmas
  kept public (reusable at modulus Dp^n in T515). Golf applied:
  muEta_term_exp_identity tail simp-at/exact → simpa-using. Build green,
  3 sorries remain (= T514–T516 scope).

### [T514] Restriction to units: (1−η(p)p^k)-moments (Lem 5.11)
- **Status**: done | **File**: NonTame.lean | **Depends on**: CLEANUP-52, T512 | **Type**: lemma
- **Statement**: `res_units_muEta_moments` (L5.2.5).
- **Sources**: TeX 1831–1843 (verbatim at L5.2.5; T035-pattern).
- **Sizing**: ~50 LOC.
- **Progress**: DONE 2026-06-11, `res_units_muEtaCleared_moments` exactly
  the T035 pattern widened: NEW `MeasureR.phi_apply_powCM` (Toolbox —
  ∫x^k d(φμ) = algebraMap(p^k)·∫x^k dμ; the function identity
  (powCM k)∘(mulCM p) = algebraMap(p^k)•powCM k by ext + simp [mulCM,
  mul_pow]; NOTE the Algebra ℤ_[p] (integerRing K) instance derives from
  NormedAlgebra ℚ_[p] K, so that can't be omitted), then res_units_eq +
  T513's psi_muEtaCleared + φ-linearity + coe-bookkeeping
  (algebraMap-composite `change` per the Coefficients defeq +
  push_cast/rfl; the smul-coe show needs push_cast [smul_eq_mul]) +
  T512's muEtaCleared_moments + ring. Verification: lake build green;
  axioms = {propext, Classical.choice, Quot.sound} (stale-LSP artifact
  once more, clean on re-verify). Blueprint: `interp-eta-restriction`
  wired → res_units_muEtaCleared_moments with cleared-form prose note;
  blueprint build green.

### [T515] μ_θ, its moments and restriction; ζ_η and its interpolation
- **Status**: done | **File**: NonTame.lean | **Depends on**: T514, T508 | **Type**: cluster
- **Statement**: `muTheta` (:= twist χ̃ μ_η) + Lem 5.12 cleared transform +
  moments + Res-formula (L5.2.6 — ROUTE per the corrected attack: ψ-of-twist
  via support for n ≥ 1, L5.2.4 for n = 0); `zetaEta` + final display
  (L5.2.7).
- **Sources**: TeX 1845–1875 (verbatim quotes at L5.2.6/7).
- **Blueprint**: wire `interp-nontame`-adjacent definition nodes (μ_θ/ζ_η).
- **Sizing**: ~160 LOC.
- **Progress**: DONE 2026-06-11 (~480 LOC, the largest single-ticket chain
  since T509). `zetaEta_twisted_moments` = L5.2.7's final display proven
  with a route improvement over the planned n-split: the Euler factor
  arises UNIFORMLY from Res = 1−φψ + the φ-twist function identity
  ((χ̃·x^m)∘mulCM p = (χ(p̄)·alg(p^m))•(χ̃·x^m)) — for n ≥ 1 it degenerates
  via χ(p̄) = 0; NO support-vs-telescope case split needed (the planned
  L5.2.6 ψ-route became unnecessary). Chain: (1)
  `isUnit_root_mul_pow_one_add_X_sub_one` — product-root denominators
  ζ_D^c·w (‖w−1‖<1) are units by ultrametric dominance (le_antisymm with
  norm_add_le_max twice); NEW Coefficients helper
  `integerRing.not_isUnit_of_norm_lt_one`; (2) `map_ring_inverse_of_isUnit`
  (ring homs commute with Ring.inverse at units — mathlib gap, PR
  candidate); (3) `mahlerTransform_charTwist_muEtaCleared` — the ε^b-line
  twists via mahlerTransform_charTwist_eq_substAffine; c = 0 line is 0 on
  BOTH sides (Ring.inverse of X resp. of a norm-small denominator); (4)
  REFACTOR: T512's step lemmas abstracted to `unit_denom_exp_identity` +
  `rescale_exp_sub_one_mul_unit_denom` (abstract unit-denominator + M-torsion
  w), old names kept as instances; subst-distributors `subst_map_C_mul`/
  `subst_map_sum`/`subst_map_neg` factored; (5) `toFieldChar_prod_natCast`
  (θ(j) = η(j)χ(j) pointwise at naturals; non-units via
  Nat.coprime_mul_iff_right split; units via changeLevel_eq_cast_of_dvd +
  ZMod.cast_natCast); (6) `X_mul_twist_muEtaCleared_subst` MASTER:
  G(χ̄)-smearing (mahler_twist_formula, its unused `_hn : 1 ≤ n` REMOVED so
  n = 0 works uniformly; ditto sum_char_inv_H_eq's hn), per-(c,b) clearing
  at modulus D·p^n, DOUBLE Gauss collapse (sum_inv_char_zeta_pow at D and
  at p^n), T504 at D·p^n, cancel (rescale (Dp^n) exp − 1) AND C(G(χ̄))
  (nonvanishing via NEW factored `gaussSum_inv_ne_zero` in TameConductor,
  also refactored into twist_muA_moments −13 LOC); (7)
  `twist_muEtaCleared_moments` (T512-endgame verbatim); (8) final assembly.
  STATEMENT REPLAN: `(hε : IsPrimitiveRoot ε (p^n))` threaded into
  twist_muEtaCleared_moments + zetaEta_twisted_moments (the source's ambient
  ε_{p^n}, as in twist_muA_moments). LEAN NOTES: push_cast at a hypothesis
  normalises ↑(D·p^n) to ↑D·↑p^n breaking rescale-matching — use targeted
  `simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]`; double-pow_mul
  rws need explicit args (`pow_mul ζ D (c·p^n)`) or the second fires on the
  same term; triple-sum Fubini = per-level sum_congr + Finset.sum_comm with
  fully-spelled shows. Verification: lake build green (code + blueprint);
  axioms = {propext, Classical.choice, Quot.sound} on the master, moments,
  and zetaEta_twisted_moments (stale-LSP artifact once, clean re-verify).
  Blueprint: `interp-mahler-theta` wired → charTwist transform + master +
  moments (prose note: two-index CRT-resolved form, G(χ̄) cancels,
  single-root closed form not restated); `interp-zeta-eta` wired →
  zetaEta_twisted_moments (prose note: x⁻¹ as index shift, uniform Euler
  factor, ambient root). Only T516's determinacy sorry remains in the file.

### [T516] **MILESTONE: RJW Theorem 5.7** — ∃! ζ_η
- **Status**: done | **File**: NonTame.lean | **Depends on**: CLEANUP-ALL-4
- **Type**: theorem
- **Statement**: existence (T515) + uniqueness via determinacy (L5.2.8's
  recorded design: χ-quantifier through 𝓞_ℂp-baseChange; statement form
  fixed in TW6 skeleton per decomposition).
- **Sources**: TeX 1773–1776 (verbatim at R5.2 head).
- **Blueprint**: wire `interp-nontame`; re-render.
- **Sizing**: determinacy ~120 LOC + assembly ~60.
- **Progress**: **DONE 2026-06-11 — MILESTONE: NonTame.lean SORRY-FREE,
  RJW Theorem 5.7 complete** (existence = T515's zetaEta_twisted_moments;
  uniqueness = `eq_of_twisted_moments_eq` via the determinacy
  `eq_zero_of_twisted_moments_eq_zero`, both proven this ticket). The
  skeleton's hroots-quantifier design (NOT the 𝓞_ℂp-baseChange
  alternative) was the pinned form ✓. Determinacy route (≈260 LOC + three
  infrastructure pieces): (1) NEW
  `LocallyConstant.exists_eq_comp_toZModPow` (Measure/Basic.lean —
  uniform local constancy on compact ℤ_p: per-point toZModPow-fibre
  neighbourhoods + elim_nhds_subcover + ultrametric two-ball merge; PR
  candidate); (2) NEW `PadicInt.exists_primitiveRoot_card_sub_one`
  (Branches.lean — Teichmüller lift of a generator of (ZMod p)ˣ is a
  primitive (p−1)-th root: section-property toZMod_teichmullerZMod forces
  the order; NOTE IsPrimitiveRoot needs
  Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots imported); (3)
  `hasEnoughRootsOfUnity_of_padic_roots` — instance for the full dual of
  (ZMod p^n)ˣ: exponent ∣ φ(p^n) ∣ p^n(p−1); primitive-P-root as the
  COPRIME PRODUCT of hroots-root and Teichmüller-root
  (Commute.orderOf_mul_eq_mul_orderOf_of_coprime + IsPrimitiveRoot.orderOf
  + pow_of_dvd + Nat.div_div_self; NOTE HasEnoughRootsOfUnity is
  TYPE-valued — produce the ∃-prim as a Prop-have BEFORE the structure
  goal or Exists-elim fails; cyc-field = rootsOfUnity.isCyclic for the
  domain integerRing K). Determinacy body: (B) all-χ moment vanishing via
  the primitive core (FactorsThrough at p^m + conductor-min via
  Nat.sInf_le + NEW Characters lemma
  `DirichletCharacter.toContinuousMapZp_changeLevel` (unit-agreement via
  changeLevel_eq_cast_of_dvd + PadicInt.cast_toZModPow) + 1_u-sandwich by
  hsupp); (C) x-weighted coset-indicator vanishing via mathlib's
  `DirichletCharacter.sum_char_inv_mul_char_eq` orthogonality (nonunit
  cosets die against the unit-supported μ; CharZero-cancel of totient);
  (D) loc-const collapse through the factorisation lemma at level
  max(n₀,1) + Finset.sum_eq_single; (E) x⁻¹-trick: extendByZero of the
  R-valued units-inverse (UnitsZp machinery + KubotaLeopoldt invCM) +
  ε-approximation against PadicMeasure.exists_locallyConstant_norm_sub_le'
  + norm_apply_le. LEAN NOTES: conductor_le_conductor_mem_conductorSet
  concludes ≤ (Classical.choose _).conductor — useless; use Nat.sInf_le
  directly; changeLevel_trans takes χ as FIRST explicit arg; ext-on-C(X,R)
  goals come ↑-coercion-wrapped — close ring-steps with
  `exact congrArg Subtype.val (by ring)`; Nat.dvd_sub (unprimed) in this
  pin; omega needs primality-derived 1 < p fed explicitly. Verification:
  lake build green (code + blueprint, 3950 jobs); axioms = {propext,
  Classical.choice, Quot.sound} + scan_source clean on
  eq_zero_of_twisted_moments_eq_zero and eq_of_twisted_moments_eq.
  Blueprint: `interp-nontame` wired → zetaEta_twisted_moments +
  eq_of_twisted_moments_eq + eq_zero_of_twisted_moments_eq_zero with the
  two-halves prose note (cleared existence, hroots-design uniqueness,
  Teichmüller prime-to-p roots).

### [CLEANUP-ALL-4] Pre-milestone /cleanup-all
- **Status**: done | **Depends on**: T515 | **Type**: cleanup-all (before T516)
- **Progress**: DONE 2026-06-11. Project-wide sweep: lake build green with
  23 warnings, ALL `declaration uses sorry` in open-ticket scope (PadicExp
  17 = T521–T523, Branches 4 = T519, NonTame 1 = T516); zero style/linter
  warnings; zero lines > 100 project-wide. Axiom spot-checks this session:
  tame_conductor(+theta), zetaEta_twisted_moments, twist/X_mul masters —
  all {propext, Classical.choice, Quot.sound}. Golf: T512's hHsum inline
  subst-transport refactored onto the T515 subst_map_{neg,sum,C_mul}
  distributors (−8 LOC). The per-ticket inline cleanups (T511–T515) kept
  the bar; no batch debt found.

### [T517] Teichmüller character ω
- **Status**: done | **File**: Interpolation/Branches.lean | **Depends on**: none
- **Progress**: DONE 2026-06-10. Executed via the flt-regular-bernoulli port
  (replan note above): `maximalIdealQuotientEquivZMod` + CharP/Finite instances
  on the residue quotient, `teichmullerZMod : ZMod p →*₀ ℤ_[p]` through
  `Perfection.teichmuller₀`, `toZMod_teichmullerZMod` (section-of-reduction),
  `teichmullerZMod_pow_card_sub_one`; skeleton fills `teichmullerFun :=
  teichmullerZMod ∘ toZMod` + all 6 API lemmas + `teichmuller : ℤ_[p]ˣ →* ℤ_[p]ˣ`
  packaging + `teichmuller_coe` (rfl). Compiled FIRST PASS, zero errors.
  Verification: diagnostics clean on the section; axioms = {propext,
  Classical.choice, Quot.sound} on PadicInt.teichmuller,
  toZMod_teichmullerZMod, teichmullerFun_sub_self_mem,
  teichmullerFun_eq_of_sub_mem. Inline cleanup: golfed isUnit hypothesis to
  `Nat.sub_ne_zero_of_lt`. Blueprint: node `teichmuller-character` spans Def
  5.15 in FULL (ω + ⟨·⟩ + factorisation) — wiring deferred to T518 completion
  per the partial-realisation rule.
- **Parallel**: yes (chain C head) | **Type**: def + API
- **Statement**: skeleton `PadicInt.teichmullerFun` + 6 API sorries +
  `teichmuller` packaging (L5.3.1).
- **Proof sketch**: REPLANNED (flt-regular-bernoulli survey, plan.md addendum
  2026-06-10): port their `Characters.lean` construction — `teichmullerZMod :
  ZMod p →*₀ ℤ_[p]` via mathlib `Perfection.teichmuller₀ p (maximalIdeal ℤ_[p])`
  composed with `(PerfectionMap.id …).equiv` and `PadicInt.residueField.symm`;
  then `teichmullerFun p x := teichmullerZMod p (toZMod x)`. Source-faithful:
  mathlib's `Perfection.teichmullerFun` is itself the limit-of-`x^{p^n}`
  construction of RJW Def 5.15 (`teichmullerAux n+1 = lift^{p^n}`, adic-Cauchy).
  Original from-scratch sketch (decomposition L5.3.1) retired.
- **Mathlib lemmas**: `Perfection.teichmuller₀`, `Perfection.mk_teichmuller₀`,
  `PadicInt.residueField`, `PadicInt.toZMod_eq_residueField_comp_residue`,
  `ZMod.pow_card_sub_one_eq_one`, `IsUnit.of_pow_eq_one` (all verified in pin).
- **Sources**: Def 5.15 TeX 1899–1905 (verbatim at R5.3); port source
  `flt-regular-bernoulli/BernoulliRegular/Characters.lean` (user's own repo).
- **Blueprint**: wire the chapter's ω-definition node (§5.3 part — locate
  label in Interpolation.lean tail).
- **Sizing**: ~120 LOC.

### [T518] ⟨·⟩ and y^s on 1+pℤ_p
- **Status**: done | **File**: Branches.lean | **Depends on**: T517 | **Type**: def + API
- **Progress**: DONE 2026-06-10. angleBracket section: `angleUnit_sub_one_mem`
  (unit-factoring ω⁻¹(x − ω) + ideal absorption), `angleUnit_mul`
  (mul_inv_rev + mul_mul_mul_comm), `teichmuller_mul_angleUnit`
  (mul_inv_cancel_left, term-mode). onePAdicPow section: helpers
  `tendsto_pow_atTop_nhds_zero_of_mem_span` (norm ≤ p⁻¹ < 1),
  `isClosed_span_p` (closed ball via norm_le_pow_iff_mem_span_pow),
  `mul_sub_one_mem`; `onePAdicPow := addChar_of_value_at_one (y−1)`;
  `onePAdicPow_apply_one`, `onePAdicPow_natCast` (nsmul_one +
  map_nsmul_eq_pow), `continuous_onePAdicPow` (defeq), `onePAdicPow_sub_one_mem`
  (density of ℕ + closedness, quotient-ring computation at naturals),
  `onePAdicPow_mul_base` (uniqueness `eq_addChar_of_value_at_one` applied to
  the product character). `eq_one_of_pow_card_sub_one` MOVED into the
  onePAdicPow section (proof needs the character API): u^{(p−1)s} via
  `AddChar.mulShift` is trivial by two applications of uniqueness, then
  evaluate at (p−1)⁻¹ (p−1 a unit: residue −1 ≠ 0); works verbatim for p = 2
  (degenerate, exponent 1) — RJW's odd-p caveat noted in docstring.
  Verification: zero errors; axioms = {propext, Classical.choice, Quot.sound}
  on eq_one_of_pow_card_sub_one, onePAdicPow_mul_base,
  teichmuller_mul_angleUnit, onePAdicPow_sub_one_mem. lake build green
  (Branches + Blueprint). Blueprint: node `teichmuller-character` wired to
  {teichmuller, angleUnit, teichmuller_mul_angleUnit,
  eq_one_of_pow_card_sub_one} with construction/uniqueness prose note;
  Lem 5.14 node `interp-padic-exp` left unwired with rationale comment
  (wire when T521–T523 proves convergence). Replan note honoured: x^s via
  character-uniqueness (decomposition L5.3.3).
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
- **Status**: done (finished 2026-06-11)
- **File**: Branches.lean | **Depends on**: T518, CLEANUP-ALL-5
- **Type**: def + theorem
- **Statement**: skeleton `branchChar`, `branchChar_natCast`, `zetaPBranch`,
  `zetaPBranch_interpolation` (L5.3.4–6; pairing through the §4
  IsPseudoMeasure witnesses at the T037 generator — pairChar sub-lemma
  `integral_char_dirac_mul` L5.3.5).
- **Sources**: TeX 1907–1924 (verbatim at R5.3).
- **Blueprint**: wire the ζ_{p,i}/Thm 5.17 nodes; re-render.
- **Sizing**: ~150 LOC.
- **Progress**:
  - 2026-06-10/11 (prior session, credit-out mid-build): full block staged —
    `isLocallyConstant_teichmullerFun`, `onePAdicPow_congr`,
    `onePAdicPow_sub_one_mem_pow` (p^m-strengthened closure argument),
    `continuous_angleUnit_val`, `continuous_onePAdicPow_angleUnit`
    (multiplicative-increment route ⟨x⟩ = ⟨x₀⟩·w), `branchChar`,
    `branchChar_natCast` (orderOf-divides + pow_eq_pow_iff_modEq endgame),
    `zetaPBranch` (zetaNum-witness pairing at the T037 generator),
    `zetaPBranch_interpolation` (padicZeta_moments + field_simp endgame).
  - 2026-06-11 (takeover session): fixed the 2 remaining build errors
    (hxw closed via `Units.mul_inv_cancel_left` instead of the failing
    mul_assoc chain; spurious `rfl` after goal-closing `rw` dropped).
    Verification: lake build green, 0 sorry in Branches.lean,
    `#print axioms` = [propext, Classical.choice, Quot.sound] on all 6 new
    decls (branchChar, branchChar_natCast, zetaPBranch,
    zetaPBranch_interpolation, continuous_angleUnit_val,
    continuous_onePAdicPow_angleUnit).
  - 2026-06-11: /cleanup degraded mode (no lean-lsp MCP this session):
    linter-set build green, zero long lines; golfed 3 unused `set … with`
    binders. A tooled session may revisit.
  - 2026-06-11: blueprint wired — `interp-branches` →
    branchChar + zetaPBranch (with ℚ_p-vs-ℂ_p and witness-pairing prose
    note), `interp-branch-interpolation` → zetaPBranch_interpolation.
    Node prose corrected to RJW's actual Thm 5.17 statement (odd-vanishing
    moved to post-proof prose remark, as in the source TeX 1928);
    `lake build PadicLFunctionsBlueprint` green.
  - DONE — milestone: RJW Theorem 5.17 complete.

### [CLEANUP-ALL-5] Pre-milestone /cleanup-all
- **Status**: done | **Depends on**: T510, T516, T518 | **Type**: cleanup-all (before T519/T520)
- **Progress**: DONE 2026-06-11. Sweep: zero style/linter warnings
  project-wide, zero long lines; 21 sorry-warnings, all open-ticket scope
  (Branches 4 = T519, PadicExp 17 = T521–T523). T516's additions were
  cleaned per-ticket (omits, congrArg-val ring-closers, simp-arg prunes).
  No batch debt.

### [T520] L_p(θ,s) and RJW Theorem 5.19
- **Status**: done (finished 2026-06-11)
- **File**: Interpolation/LpFunction.lean (replan — see Progress) + Branches.lean
- **Depends on**: T519, T516 | **Type**: def + theorem
- **Statement**: `LpFunction θ s` (genuine integral against ζ_η) +
  `Lp_interpolation` (L5.3.7; eq:alternative route; ω-as-Dirichlet-character
  bridge `teichmullerChar` sub-leaf).
- **Sources**: TeX 1929–1957 (verbatim at R5.3).
- **Blueprint**: wire the L_p/Thm 5.19 nodes; re-render; chapter complete
  except Mellin-dependent prose nodes (rationale comments).
- **Sizing**: ~130 LOC.
- **Progress**:
  - 2026-06-11: REPLAN (file location): the planner placed L_p in
    Branches.lean, but T516 inverted the import direction (NonTame imports
    Branches for the Teichmüller prime-to-p roots), and L_p needs NonTame's
    μ̃_η stack — so T520 lives in the new
    `PadicLFunctions/Interpolation/LpFunction.lean` (imports NonTame; wired
    into PadicLFunctions.lean; CL53's scope extended to include it). The
    ω-bridge cluster (`teichmullerChar`, `teichmullerChar_toZMod`,
    `castHom_toZModPow_eq_toZMod`) is ℤ_p-level and went to Branches.lean
    as planned.
  - 2026-06-11: built `teichmullerCharR` (ω over integerRing K),
    `invUnitsCM`, `anglePowCM` (T519's continuity through the isometric
    structure map), `zetaEtaCleared` (RJW's ζ_η as a genuine measure on
    ℤ_p^×, cleared normalisation, restriction implicit in extension by
    zero), `LpFunction` (RJW Def 5.18, Gauss unit divided out),
    `twistedPChar` (χω^{−k} at level p^{max n 1}),
    `exists_primitive_pPow_factorisation` (T516's conductor argument
    packaged), `Lp_interpolation` (RJW Thm 5.19) — statement quantifies
    the primitive core χ' of χω^{−k} via a factorisation hypothesis (the
    zetaEta_twisted_moments pattern); RHS = (1−θ'(p)p^{k−1})·LvalNeg
    (toFieldChar θ') (k−1) with θ' = η·χ' at level D·p^m.
  - Proof route as planned (eq:alternative): k = k'+1 destructure; ε' from
    hε by pow_of_dvd; character key χ = χ'·ω^{k'+1} at level p^{max n 1}
    (group algebra from hχ'); pointwise integrand identity
    x⁻¹χ(x)⟨x⟩^k = χ'(x)x^{k−1} on units (Units-level collapse +
    congrArg Units.val + map_mul/map_pow over algebraMap); extendByZero
    ext-case-split; zetaEta_twisted_moments at χ'; Gauss-unit cancellation.
  - Verification: lake build green (code + blueprint), 0 sorry,
    `#print axioms` = [propext, Classical.choice, Quot.sound] on all 10 new
    decls (castHom_toZModPow_eq_toZMod, teichmullerChar, teichmullerCharR,
    invUnitsCM, anglePowCM, zetaEtaCleared, LpFunction, twistedPChar,
    exists_primitive_pPow_factorisation, Lp_interpolation).
  - /cleanup degraded mode (no lean-lsp MCP this session): linter-set green,
    zero long lines; added @[simp] apply-lemmas (invUnitsCM_apply,
    anglePowCM_apply, zetaEtaCleared_apply) and de-nested the in-proof
    shows. A tooled session may revisit.
  - Blueprint: `interp-zeta-eta` re-wired to zetaEtaCleared +
    zetaEta_twisted_moments (ζ_η now exists as a measure object);
    `interp-Lp-theta` → LpFunction; `interp-Lp-interpolation` →
    Lp_interpolation. Node prose matched to RJW's actual Thm 5.19 (the
    ζ_{p,i}(s) = L_p(ω^i,s) identification is RJW's post-theorem REMARK —
    moved to prose with a both-routes-kept formalisation note, as for
    Thm 5.17). `lake build PadicLFunctionsBlueprint` green.
  - DONE — RJW Theorem 5.19 complete; §5.3 mainline (5.17 + 5.19) closed.

### [T521] p-adic exponential: convergence, isometry, functional equation
- **Status**: done (finished 2026-06-11)
- **File**: PadicLFunctions/PadicExp.lean | **Depends on**: none
- **Parallel**: yes (chain D head; user-added cluster) | **Type**: def + lemmas
- **Progress**:
  - 2026-06-11: E1 was free — mathlib has the full nonarchimedean stack:
    `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` (complete
    case) + `HasSum.mul_of_nonarchimedean` +
    `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`
    (Topology/Algebra/InfiniteSum/Nonarchimedean.lean + Ring.lean). Added
    the missing 2-line bridge `instance : NonarchimedeanRing L` from
    `IsUltrametricDist` (MATHLIB-PR candidate, noted in docstring).
  - E2 via `sub_one_mul_padicValNat_factorial_lt_of_ne_zero` (exact
    Legendre form) + `Padic.norm_eq_zpow_neg_valuation` +
    `Padic.valuation_natCast`. Helpers extracted:
    `norm_factorial_inv_pow_le` (inverted bound),
    `norm_factorial_inv_smul_pow_le` (geometric term decay, rpow-free at
    the (p−1)-power level per the recorded design).
  - E3: `summable_padicExp_terms` (E1 + geometric bound + ε-transfer
    through strict pow-monotonicity); `padicExp_zero` (tsum_eq_single);
    isometry via NEW `norm_factorial_inv_smul_pow_sub_lt` (m ≥ 2 tail
    strictly dominated — geom_sum₂_mul + ultrametric sum bound + strict
    Legendre on the OPEN ball, attack [3] honoured) + dominant-term
    argument (tendsto-tail uniform bound C < d via range-sup' + d/2;
    `IsUltrametricDist.norm_tsum_le_of_forall_le` +
    `norm_add_eq_max_of_norm_ne_norm`); `norm_padicExp_sub_one` at y = 0;
    `padicExp_add` via the attack-pinned route — NOT norm-summable Cauchy
    products: `mul_of_nonarchimedean` summability + antidiagonal formula +
    `Nat.sum_antidiagonal_eq_sum_range_succ` + add_pow +
    `Nat.choose_mul_factorial_mul_factorial` scalar algebra.
  - Verification: lake build green, 0 sorry in the T521 declarations
    (11 remain in file = T522/T523 scope), `#print axioms` =
    [propext, Classical.choice, Quot.sound] on all 10 new decls.
  - /cleanup degraded mode (no lean-lsp MCP): linter green (omits added),
    no long lines. Blueprint: none for T521 (per plan — T523 wires
    Lem 5.14).
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
- **Status**: done (finished 2026-06-11)
- **File**: PadicExp.lean | **Depends on**: T521 | **Type**: lemmas
- **Progress**:
  - 2026-06-11 (main session): `sub_one_mul_padicValNat_succ_le`
    ((p−1)·v_p(n+1) ≤ n via Bernoulli), `norm_succ_inv_smul_pow_le`
    (geometric log-term decay, rpow-free), `summable_padicLog_terms`,
    `padicLog_one`, `norm_succ_inv_smul_pow_lt` (tail domination m ≥ 1),
    `norm_padicLog` (dominant-term argument, mirrors the exp isometry).
  - 2026-06-11 (tooled subagent, lean-lsp): the composition trio
    `padicExp_padicLog`, `padicLog_padicExp`, `padicLog_mul` via the pinned
    Washington Prop 5.3 route — formal identities `exp_subst_log`
    ((1+X)·DF = F recursion) and `log_subst_exp_sub_one` (derivative.ext)
    using mathlib's `PowerSeries.log` (it exists — `HasSubst.log`,
    `deriv_log`); evaluation bridge `master_bridge` (per-power
    `tsum_eval_pow` by iterated nonarchimedean Cauchy product + ultrametric
    Fubini `Summable.tsum_comm` over ℕ×ℕ; total summability from the
    Legendre multinomial bound `norm_coeff_pow_le`:
    ‖[X^k](G^n)‖^{p−1} ≤ p^{k−n}); `padicLog_mul` free from the pair +
    `padicExp_add`. ~20 helper lemmas added (all docstringed, in
    section Inversion).
  - Verification: lake build green, 0 sorry in T522 scope (6 remain =
    T523 pZp section), `#print axioms` = standard 3 on all of
    padicLog_one/norm_padicLog/summable_padicLog_terms/padicExp_padicLog/
    padicLog_padicExp/padicLog_mul. Linter clean (omits added).
  - Note for cleanup: `master_bridge` carries
    `set_option maxHeartbeats 400000` (verified working value; golf
    candidate for a tooled cleanup pass).
- **Statement**: skeleton E4 sorries (`padicLog_one`, `norm_padicLog`,
  `padicExp_padicLog`, `padicLog_padicExp`, `padicLog_mul`).
- **Proof sketch**: decomposition E4 (series composition with ultrametric
  Fubini — Washington Prop 5.3 route, attack-pinned; log_mul from exp_add +
  injectivity-of-exp via isometry).
- **Sources**: as T521.
- **Sizing**: ~150 LOC (the composition is the meaty half).

### [T523] RJW Lemma 5.14 as stated + equivalence with the character route
- **Status**: done (finished 2026-06-11)
- **File**: PadicExp.lean | **Depends on**: T522, T518 | **Type**: theorem
- **Progress**:
  - 2026-06-11 (tooled-route subagent under main-session orchestration;
    degraded tooling — lake-build gate): E5 route verbatim. Helpers:
    `coe_norm_le_inv_of_mem_span`, `inExpBall_of_mem_span` (hp2 enters
    exactly here: p−1 ≥ 2 makes the ball inclusion strict),
    `pZpExp_coe`/`pZpLog_coe` (dite-true-branch bridges). Defs filled
    junk-total (dite on the integrality certificate; junk 1 resp. 0).
    `padicExp_converges_on_pZp` = summable_padicExp_terms ∘ ball-inclusion;
    `pZpExp_sub_one_mem`/`pZpLog_mem` via the isometries;
    `padicExp_smul_padicLog_eq_onePAdicPow` by AddChar-uniqueness
    (additivity via padicExp_add, LipschitzWith-1 continuity via the
    isometry, value x at 1 via padicExp_padicLog, then
    PadicInt.eq_addChar_of_value_at_one) — the recorded replan L5.3.3 is
    now DISCHARGED: both x^s-routes formalised and proven equal.
  - Verification: lake build green; ZERO sorry project-wide (PadicExp.lean
    fully proven); `#print axioms` = standard 3 on all six decls; linter
    clean.
  - Blueprint: `interp-padic-exp` WIRED → padicExp_converges_on_pZp +
    padicExp_smul_padicLog_eq_onePAdicPow (unwired-rationale comment
    removed per the user-approved cluster plan); blueprint build green.
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
- **Status**: done (degraded mode, 2026-06-11) | **Depends on**: T523 | **Type**: cleanup
- **Progress**: no lean-lsp MCP this session — degraded pass per standing
  rule 3: build green with the mathlib linter set, zero warnings, zero
  sorries, zero long lines; golfed the two `by exact`-ascription bridges to
  `htail.ne'` (isometry proofs). Queued for the tooled CLEANUP-FINAL:
  `master_bridge`'s `set_option maxHeartbeats 400000` (verified working;
  golf candidate), per-decl golf of the T521–T523 proofs.

### [CLEANUP-53] Final per-file cleanups (§5 files)
- **Status**: done (degraded mode, 2026-06-11) | **Depends on**: T520
- **Type**: cleanup (Characters, GenBernoulli[Complex], Twist,
  TameConductor, NonTame, Branches, LpFunction — final pass each; then
  update CLEANUP-FINAL's scope to include §5)
- **Progress**: substance largely discharged upstream — the tooled
  CLEANUP-ALL-5 sweep (2026-06-11) left zero style/linter warnings
  project-wide, and the post-ALL-5 additions (T519 Branches, T520
  Branches+LpFunction) were cleaned per-ticket (degraded). This pass
  verified: build green, zero warnings, zero long lines, zero sorries
  across all §5 files incl. the new LpFunction.lean. CLEANUP-FINAL's scope
  widened to include the §5 files (see its entry). Tooled session may
  revisit for per-decl golf.

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

---

# §6 board (The values at s = 1; TeX 1980–2180) — created 2026-06-11

Skeleton: 4 new files (ExtLog.lean, MeasureR/FormalPsi.lean,
ValuesAtOneComplex.lean, ValuesAtOne.lean), 28 new sorries, `lake build`
green. Decomposition: decomposition.md R6 (verbatim quotes + replans 1–5).
Standing rules apply (CLAUDE.md). Statements live in the skeleton — tickets
reference declarations by name (the §5 T521-pattern).

### [T601] Exp-ball multiplicativity and log of powers
- **Status**: done (2026-06-11) | **File**: ExtLog.lean | **Depends on**: none
- **Progress**: DONE first pass — norm_lt_one_of_inExpBall (helper),
  mul_mem_expBall ((y−1)z+(z−1) decomposition, ultrametric max),
  pow_mem_expBall (induction), padicLog_pow (padicLog_mul induction +
  succ_nsmul). Axioms standard ×4; build green; degraded-mode cleanup
  (linter green, no long lines).
- **Parallel**: yes (chain W6a head) | **Type**: lemmas
- **Statement**: skeleton `mul_mem_expBall`, `padicLog_pow` (W6a-a1/a2).
- **Proof sketch**: a1 ultrametric: yz−1 = (y−1)z + (z−1), norm ≤ max,
  each factor ≤ ball-bound (‖z‖ = ‖(z−1)+1‖ ≤ 1 needs ball ⊆ unit-ball:
  ‖z−1‖^{p−1} < p⁻¹ < 1 ⟹ ‖z−1‖ < 1); pow-monotone transfer as in
  norm_factorial_inv_smul_pow_le. a2: induction on n via padicLog_mul +
  a1-closure; n = 0 via padicLog_one.
- **Mathlib lemmas**: IsUltrametricDist.norm_add_le_max, pow_lt_one_iff.
- **Sources**: decomposition R6 W6a; Washington §5.1.
- **Generality**: ambient L (PadicExp variables).
- **Sizing**: source one-liners → ~40 LOC.

### [T602] p-power descent into the exponential ball
- **Status**: done (2026-06-11)
- **Progress**: DONE — norm_natCast_p (helper: ‖p‖_L = p⁻¹ via
  norm_algebraMap' + Padic.norm_p), norm_pow_p_sub_one_le (binomial peel
  via sum_range_succ' + Nat.Prime.dvd_choose_self +
  IsUltrametricDist.norm_natCast_le_one), exists_pPow_pow_inExpBall
  (decay r_{k+1} ≤ t0·r_k with t0 := max(r0^{p−1},p⁻¹) < 1, geometric
  tendsto at the (p−1)-power level — boundary passed THROUGH per the
  attack note). Axioms standard ×3; linter clean (omits added);
  degraded-mode cleanup. | **File**: ExtLog.lean | **Depends on**: none
- **Parallel**: yes | **Type**: lemmas
- **Statement**: skeleton `norm_pow_p_sub_one_le`, `exists_pPow_pow_inExpBall`
  (W6a-a3/a4).
- **Proof sketch**: a3 binomial w^p−1 = Σ_{i≥1}C(p,i)(w−1)^i; i = p term
  (w−1)^p; 0<i<p terms have ‖C(p,i)‖ ≤ p⁻¹ (p ∣ choose: mathlib
  Nat.Prime.dvd_choose_self); ultrametric finite-sum max
  (norm_sum_le_of_forall_le_of_nonneg). a4: iterate; r_{j+1} ≤
  r_j·max(r_j^{p−1}, p⁻¹) ≤ r_j·t with t := max(r_0^{p−1}, p⁻¹) < 1;
  geometric until r^{p−1} < p⁻¹. ATTACK-pinned: the closed boundary
  r = p^{-1/(p−1)} is passed THROUGH (no single-step contraction there;
  the t-factor argument is global, decomposition R6 a4).
- **Mathlib lemmas**: Nat.Prime.dvd_choose_self (verify name),
  add_pow_le?? — no: Commute.add_pow expansion; tendsto_pow geometric.
- **Sources**: decomposition R6 W6a; Washington §5.1.
- **Sizing**: ~70 LOC.

### [T603] Integral norm-one elements lie in the extLog domain
- **Status**: done (2026-06-11)
- **Progress**: DONE (tooled-route subagent, degraded tooling): pigeonhole
  n ↦ z^n into ℤ[z]⧸(p) (finite via Module.finite_of_fg_torsion — route
  deviation from the ZMod-p-module chain, recorded); norm-cancellation
  WITHOUT z̄-invertibility per the attack-pinned design; helpers
  norm_le_one_of_mem_adjoin_int (adjoin_induction),
  finite_adjoin_int_quotient, norm_eq_one_of_inExpBall_sub_one. Two new
  mathlib imports (FiniteAbelian.Basic, Finiteness.Cardinality). Axioms
  standard; linter clean. | **File**: ExtLog.lean | **Depends on**: T602
- **Type**: lemmas
- **Statement**: skeleton `exists_pow_sub_one_norm_le`,
  `extLogDomain_of_integral_norm_one` (W6a-a5/a11).
- **Proof sketch**: a5: S := Algebra.adjoin ℤ {z} is module-finite
  (IsIntegral.fg / Algebra.adjoin.finite); S/pS finite (fg over ℤ/p);
  pigeonhole on powers of z̄: z̄^i = z̄^{i+m} ⟹ z^i(z^m−1) ∈ p·S ⊆
  p·(unit ball) ⟹ ‖z^i(z^m−1)‖ ≤ p⁻¹; ‖z^i‖ = 1 cancels (norm mult).
  ATTACK-pinned: no z̄-invertibility needed (decomposition R6 a5).
  a11: a5 gives ‖z^m−1‖ ≤ p⁻¹ < 1, then T602-a4 on w := z^m gives
  z^{m·p^j} ∈ 1+ball: witness (m·p^j, 0, z^{m·p^j}).
- **Mathlib lemmas**: IsIntegral, Algebra.adjoin, Module.Finite transfer,
  finiteness of fg-ℤ-module mod p (survey exact route at execution),
  Finite.exists_ne_map_eq_of_infinite-style pigeonhole.
- **Sources**: decomposition R6 W6a-a5 (design note).
- **Sizing**: ~80 LOC (the cluster's engine).

### [T604] extLog: well-definedness and API
- **Status**: done (2026-06-11) | **File**: ExtLog.lean | **Depends on**: T601
- **Progress**: DONE (same pass as T603): extLog_witness_smul_eq core
  (k·m' = k'·m via zpow_right_injective₀ at base p⁻¹; norm-1 of ball
  members via ultrametric isoceles), then a7–a10b as planned (witnesses
  composed; extLog_neg via (−1)-witness (2,0,1)). Axioms standard ×7
  (whole file sorry-free); linter clean.
- **Type**: def-lemmas
- **Statement**: skeleton `extLog_eq_of_witness`, `extLog_eq_padicLog`,
  `extLog_mul`, `extLog_eq_zero_of_pow_eq_one`, `extLog_neg` (W6a-a7–a10;
  def a6 already in skeleton).
- **Proof sketch**: a7: two witnesses (m,k,y), (m',k',y'): x^{mm'} both
  ways ⟹ p^{km'−k'm}·y^{m'} = y'^{m}; taking norms, ‖y‖ = ‖y'‖ = 1 and
  ‖p‖ = p⁻¹ < 1 force km' = k'm, cancel p-powers (field), then
  y^{m'} = y'^m and a2: m'·log y = m·log y'; scalar algebra in ℚ_[p]-module.
  a8: witness (1,0,x). a9: product witnesses + a1 + padicLog_mul + a7.
  a10: x^n = 1 witness (n,0,1), padicLog_one; extLog_neg: (−x)² = x²-route:
  extLog((−x)²) = extLog(x²) and 2·extLog(−x) = ... via a9-on-self (domain
  of −x from x: witness with even power) — or extLog(−1) = 0 (a10) + a9.
- **Mathlib lemmas**: norm_zpow, mul-cancellation in fields.
- **Sources**: decomposition R6 W6a; Washington §5.1 Lemma 5.5-adjacent.
- **Sizing**: ~100 LOC.

### [CLEANUP-61] /cleanup on ExtLog.lean
- **Status**: done (degraded mode, 2026-06-11) | **Depends on**: T601, T602, T603, T604
- **Type**: cleanup (cadence 4-tickets + final, merged)
- **Progress**: degraded pass (no lean-lsp MCP): linter set green, zero
  warnings, zero long lines, file sorry-free; per-ticket golf was applied
  during T601–T604. Tooled CLEANUP-FINAL may revisit.

### [T605] The digit decomposition of power series
- **Status**: done (2026-06-11) — WITH B2 STATEMENT-FIX (logged)
- **Progress**: the planned general-CommRing statement is FALSE over fields
  (R = ℚ, p = 2: (1+X)^p − 1 = unit·X makes phiSeries bijective, digits
  non-unique) — caught at the adversarial briefing, b2_log.jsonl appended.
  Fixed: psiSeries junk-totalised (dite on ∃!-digits) over general R;
  existsUnique_digits proven over integerRing K via the MEASURE-TRANSPORT
  route (measure-level p-residue decomposition through mahlerRingEquiv) —
  replacing the planner's triangular-recursion sketch (mathematically
  wrong; recorded). Subagent pass; axioms standard; dependents build. | **File**: MeasureR/FormalPsi.lean | **Depends on**: none
- **Parallel**: yes (chain W6b head) | **Type**: theorem
- **Statement**: skeleton `existsUnique_digits` (W6b-b1).
- **Proof sketch**: the family (1+T)^i·((1+T)^p−1)^j has leading
  coefficient 1 in degree i+pj (base-p digit bijection ℕ ≃ Fin p × ℕ);
  triangular recursion: define G_i's coefficients by strong induction on
  total degree, subtracting known lower terms; uniqueness by the same
  triangularity (lowest-degree coefficient of a nonzero combination
  survives). Suggest: prove coeff-extraction lemma
  coeff (i+pj) ((1+T)^i((1+T)^p−1)^j) = 1 + upper-triangularity, then
  build by Nat.strong induction.
- **Mathlib lemmas**: PowerSeries.coeff_mul, coeff_pow bounds,
  Finset.Nat digit machinery (Nat.divMod p-bijection).
- **Sources**: decomposition R6 W6b-b1 (mirrors the project's measure-level
  digit shift, Measure/Toolbox ψ).
- **Sizing**: ~60–90 LOC (the formal-cluster engine).

### [T606] psiSeries API
- **Status**: done (2026-06-11) | **File**: MeasureR/FormalPsi.lean | **Depends on**: T605
- **Progress**: DONE (same pass): psiSeries_phi/C/add/C_mul over
  integerRing K via IsDigitDecomp-uniqueness; psiSeries_map gained an
  honest ∃!-soundness hypothesis (junk-total psiSeries). Axioms standard.
- **Type**: lemmas
- **Statement**: skeleton `psiSeries_phi`, `psiSeries_C`, `psiSeries_add`,
  `psiSeries_C_mul`, `psiSeries_map` (W6b-b2/b8).
- **Proof sketch**: each from uniqueness of digits: exhibit the digit
  family of the right-hand side and apply ExistsUnique.unique. For map:
  ring-hom image of a digit decomposition is one (phiSeries commutes with
  map: subst-map compatibility — PowerSeries.map_subst exists? verify;
  else coefficient-wise).
- **Sources**: decomposition R6 W6b.
- **Sizing**: ~80 LOC.

### [T607] φ–∂ commutation, antiderivative, ker ∂ (REALIGNED R6.6)
- **Status**: done (2026-06-11)
- **Progress**: DONE (subagent): chain rule via derivative_subst +
  Derivation.leibniz_pow (MuA idiom); exists_antideriv by (1+X)-unit +
  coefficient division (CharZero); ker-∂ by unit-cancellation + coeff
  induction. Axioms standard ×3. | **File**: MeasureR/FormalPsi.lean | **Depends on**: T605, T606
- **Type**: lemmas
- **Statement** (realigned to the c₀-design — field-ψ is junk):
  `one_add_mul_derivative_phiSeries` (∂φ = p·φ∂, R-generic),
  `exists_antideriv` (K char-0: B = p·∂C with C(0) = 0),
  `eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero` (ker ∂).
- **Proof sketch**: b3: differentiate the digit decomposition;
  ∂((1+T)^i·φG) = i·(1+T)^i·φG + p·(1+T)^i·φ(∂G) (sub-lemma
  ∂φ = p·φ∂ via PowerSeries.derivative_subst — the §4 A-explicit idiom);
  digits of ∂F are (i·G_i + p·∂G_i); extract digit 0. b7: (1+X) unit-free:
  (1+X)·D = 0 ⟹ D = 0 (domain K⟦X⟧, 1+X ≠ 0); D F = 0 ⟹ all
  (n+1)·coeff_{n+1} = 0 ⟹ coeff_{n+1} = 0 (CharZero K) ⟹ F = C(F 0).
- **Mathlib lemmas**: PowerSeries.derivative_subst (A-explicit!),
  derivativeFun coefficient formula.
- **Sources**: decomposition R6 W6b.
- **Sizing**: ~70 LOC.

### [T608] The ψ-bridge, evaluation layer, and evaluated Eqphipsi
- **Status**: done (2026-06-11) — with a SECOND B2 statement-fix (logged)
- **Progress**: DONE (subagent): mahlerTransform_psi by measure-digit
  transport; sum_seriesEval_mahlerK (the realised integral Eqphipsi) via
  φ-collapse at ξ^j−1 + geom_sum orthogonality + the cyclotomic norm
  ‖ξ^j−1‖ < 1 (Coefficients.IsPrimitiveRoot.norm_sub_one_lt). B2:
  `seriesEval_phi` as skeletonised was FALSE (RHS-summability too weak —
  junk-totalised LHS diverges; b2_log.jsonl appended); EXCISED — the sound
  variants `seriesEval_phi_of_summable_prod` (ℕ×ℕ product Fubini) and
  `seriesEval_phi_at_root` (bounded coefficients) are proven and are what
  downstream consumes. FormalPsi.lean is sorry-free. Axioms standard ×5. | **File**: MeasureR/FormalPsi.lean | **Depends on**: T605, T606
- **Type**: lemmas
- **Statement** (b6 realigned to the INTEGRAL level, replan R6.6):
  `mahlerTransform_psi`, `seriesEval_zero_arg`, `seriesEval_phi`,
  `sum_seriesEval_mahlerK` (Σ_i 𝓐_μ(ξ^i−1) = p·𝓐_{ψμ}(0); summability
  internal — bounded integral coefficients; mahlerK def moved here).
- **Proof sketch**: b4 against the project's measure-ψ (digit-shift): show
  the Mahler transform of ψμ satisfies the digit-0 characterisation —
  φ𝓐_{ψμ} relates to the Mahler of Res_{pℤ_p} (project psi/phi toolbox
  identities) + uniqueness from T605. b5: eval at 0 = constantCoeff
  (tsum_eq_single); eval-of-φ: subst-coefficient expansion + tsum
  rearrangement (T522 master_bridge machinery is the template; reuse its
  helper patterns). b6: evaluate the digit decomposition at ξ^i−1; the
  φ-layer collapses ((1+(ξ^i−1))^p − 1 = 0; eval of φG at these points =
  G(0) by b5); Σ_i ξ^{ij}-orthogonality (mathlib: IsPrimitiveRoot
  geom_sum/orthogonality — verify exact name) leaves p·(digit-0)(0).
  Convergence side-conditions from hconv (finitely many digit-pieces;
  closure of summability under the manipulations).
- **Mathlib lemmas**: IsPrimitiveRoot.geom_sum_eq_zero?? (survey at
  execution), tsum_eq_single.
- **Sources**: decomposition R6 W6b-b6 (replan 2: the only meaningful
  Eqphipsi for unbounded series).
- **Sizing**: ~120 LOC (largest W6b ticket).

### [CLEANUP-63] /cleanup on MeasureR/FormalPsi.lean
- **Status**: done (degraded mode, 2026-06-11) | **Depends on**: T605, T606, T607, T608
- **Type**: cleanup
- **Progress**: degraded pass: linter green, zero warnings beyond none,
  file sorry-free, lines ≤ 100; per-ticket golf during T605–T608. Tooled
  CLEANUP-FINAL may revisit (one maxHeartbeats site if any — none found).

### [T609] Gauss sums over coprime levels
- **Status**: done (2026-06-11) — with statement-fix (recorded in docstring)
- **Progress**: DONE (subagent + endgame fix in main session): the
  skeleton's χ(D)·η(M)-twists were WRONG for the SPLIT additive character
  (εD·εM)^x — the CRT reindex factors cleanly with NO twist (the standard
  twisted formula is for e^{2πi/DM}; verified on paper per the planning
  note, docstring records it). Proof: CRT ring iso + pointwise character/
  additive-character factorisation + Equiv.sum_comp + sum_product.
  Axioms standard. | **File**: ValuesAtOneComplex.lean | **Depends on**: none
- **Parallel**: yes (chain C6 head) | **Type**: theorem
- **Statement**: skeleton `gaussSum_mul_coprime` (C6-c4).
- **Proof sketch**: CRT reindex (ZMod.chineseRemainder): a ↦ (a mod D,
  a mod M); the additive character zmodChar (εD·εM) splits as the product;
  double-sum factorisation; the χ(D)/η(M) twists arise from the CRT
  normalisation (a = a₁·M·M⁻¹-stuff). ADVERSARIAL note (gate): verify the
  exact unit-twist (χ(D)η(M) vs χ(M)η(D) vs inverses) against Washington
  Lemma 4.1-adjacent BEFORE proving; fix the skeleton statement if off —
  statement-fix allowed pre-ticket-completion with a replan note.
- **Mathlib lemmas**: ZMod.chineseRemainder, gaussSum defs,
  Finset.sum_nbij CRT.
- **Sources**: standard (Washington Ch. 4); decomposition R6 C6-c4.
- **Sizing**: ~60 LOC.

### [T610] Boundary convergence of the logarithm series (SURVEY-GATED)
- **Status**: done (2026-06-11) — with a B2 statement-fix (logged)
- **Progress**: DONE (subagent): the skeleton's HasSum-form is FALSE
  (1/(n+1) not summable on the circle; only conditional convergence) —
  b2_log appended, restated as Tendsto-of-partial-sums
  `tendsto_sum_pow_div_eq_neg_log`. Survey findings (area B): mathlib HAS
  Abel's limit theorem (`Complex.tendsto_tsum_powerSeries_nhdsWithin_lt`)
  and the open-disc log Taylor series
  (`Complex.hasSum_taylorSeries_neg_log`); Dirichlet-test partial-sum
  bound done by hand (geom_sum_eq + 2/‖1−z‖); branch-cut continuity via
  slitPlane (Re(1−z) > 0 off z = 1). Axioms standard. | **File**: ValuesAtOneComplex.lean | **Depends on**: none
- **Parallel**: yes | **Type**: theorem
- **Statement**: skeleton `hasSum_pow_div_eq_neg_log` (C6-c2).
- **Proof sketch**: SURVEY FIRST (the binding mathlib-search step):
  Abel's limit theorem / Dirichlet test for Σzⁿ/n on the unit circle.
  Candidates: Mathlib.Analysis.SpecificLimits, abelSummation files,
  `Complex.hasSum_taylorSeries_log` (open-disc version exists).
  If boundary machinery is absent: prove via Dirichlet test (partial sums
  of zⁿ bounded for z ≠ 1 on circle; 1/n monotone → 0) + Abel
  continuity to identify the limit with −log(1−z) — an API-gap sub-leaf
  to spawn per Tier A1 if needed.
- **Sources**: TeX 2040–2044; Washington Thm 4.9.
- **Sizing**: ~60–120 LOC depending on survey.

### [T611] **RJW Theorem 6.1(i)** — the classical value L(θ,1)
- **Status**: DONE (2026-06-11; sorry-free, axiom-clean, blueprint wired) | **File**: ValuesAtOneComplex.lean
- **Depends on**: T609, T610 | **Type**: theorem
- **Statement**: `LSeries_eq_gaussSum_inv_mul_sum`,
  `LFunction_one_eq` (C6-c1/c3).
- **Proof sketch**: c1: Fourier-expand θ(n) = G(θ)/N·Σ_c θ⁻¹(c)ε^{nc}
  (gaussSum_mulShift-family; verify exact mathlib form), swap finite and
  L-series sums (norm-summable for Re s > 1), then G(θ)G(θ⁻¹) = θ(−1)N
  (project T501) to reach the displayed form. c3: LFunction = LSeries for
  Re s > 1 (mathlib LFunction_eq_LSeries); take s → 1 along reals:
  LFunction continuous at 1 (differentiableAt_LFunction, θ ≠ 1); the
  finite c-sum of LSeries-terms converges to the log-values by T610 +
  Abel-limit; identify.
- **Mathlib lemmas**: DirichletCharacter.LFunction_eq_LSeries (verify),
  differentiableAt_LFunction, gaussSum_mulShift.
- **Sources**: TeX 2007–2045 verbatim at R6; Washington Thm 4.9.
- **Blueprint**: §6 chapter — wire Thm 6.1(i) node.
- **Sizing**: TeX 39 lines → ~150 LOC.
- **Progress (2026-06-11, execution)**: Both targets sorry-free; `lake build
  PadicLFunctions` green; `#print axioms` = [propext, Classical.choice,
  Quot.sound] on both + `tendsto_sum_pow_div_eq_neg_log`/`gaussSum_mul_coprime`.
  Linter clean (no warnings); blueprint nodes `val1-classical-gauss-expansion`
  and `val1-classical-s1` wired (lake build PadicLFunctionsBlueprint green).
  Route notes: c1 used `gaussSum_mulShift_of_isPrimitive` (the EXACT mathlib
  Fourier lemma: `gaussSum χ (e.mulShift a) = χ⁻¹ a · gaussSum χ e`), restricted
  the resulting `∑_a over ZMod N` to units (θ⁻¹ kills non-units), and the
  prefactor is `G(θ⁻¹)⁻¹` directly (the split additive char `zmodChar ε`
  needs NO θ(−1) twist — same observation as T609's `gaussSum_mul_coprime`);
  nonvanishing G(θ⁻¹)≠0 via T501 `gaussSum_mul_gaussSum_inv` over ℂ.
  Statement adjustment: `LSeries_eq_gaussSum_inv_mul_sum`'s `hθ1 : θ ≠ 1`
  is genuinely UNUSED (the rearrangement holds for any primitive θ); kept for
  API parity / paper-faithfulness, renamed binder `_hθ1` (docstring note).
  c3 (the real work): mathlib has Abel only for POWER series, none for
  Dirichlet series at the boundary; built helper `tendsto_LSeries_pow_boundary`
  (‖w‖=1, w≠1 ⟹ lim_{s↓1⁺} LSeries(wⁿ) s = −log(1−w)) by summation-by-parts
  representation g(s)=∑' Bₙ₊₁·((n+1)⁻ˢ−(n+2)⁻ˢ) (`Finset.sum_range_by_parts`),
  continuous on [1,2] (`continuousOn_tsum` + MVT majorant `rpow_neg_sub_le`),
  =LSeries for s>1, =−log(1−w) at s=1 via T610. Imports added to the file:
  Interpolation.Characters (T501) + Mathlib.NumberTheory.LSeries.Linearity.

### [CLEANUP-65] /cleanup on ValuesAtOneComplex.lean — done inline during
  execution (degraded MCP: lean-lsp tools unavailable in subagent; used
  `lake env lean` file gate + script search; file is linter-clean and golfed).

### [CLEANUP-65] /cleanup on ValuesAtOneComplex.lean
- **Status**: done (degraded mode, 2026-06-11) | **Depends on**: T611
- **Type**: cleanup
- **Progress**: inline during T609–T611 (file linter-clean, sorry-free,
  golfed); tooled CLEANUP-FINAL may revisit. The Dirichlet-series
  boundary-limit helper `tendsto_LSeries_pow_boundary` is a mathlib-PR
  candidate (recorded).

### [T612] Norm-one arguments and the formal log-derivative
- **Status**: done (2026-06-11)
- **Progress**: DONE (subagent): norm-1 via the project's existing
  IsPrimitiveRoot.norm_pow_sub_one_eq_one (Coefficients.lean — the
  cyclotomic-product argument was already formalised); log-derivative by
  the geometric-inverse factorisation (1+T)Cu−1 = C(u−1)(1+C(u/(u−1))T).
  Axioms standard.
- **Parallel**: yes (chain P6 head) | **Type**: lemmas
- **Statement**: skeleton `norm_one_sub_pow_eq_one`,
  `one_add_mul_derivative_logSeriesAt` (P6-p9/p2).
- **Proof sketch**: p9: Π_{c∈(ℤ/D)ˣ}(1−ε^c) = Φ_D(1) (mathlib cyclotomic
  eval: X^D−1 = Π(X−ε^c)-factorisation over K + eval at 1;
  eval_one_cyclotomic_prime / _not_prime_pow family — survey exact names);
  ‖Φ_D(1)‖ = 1 (1 or a prime q ≠ p); each factor norm ≤ 1
  (integral elements / ball), product = 1 forces each = 1 (ultrametric).
  p2: coefficient-wise: ∂(logSeriesAt) coefficients telescope against the
  geometric series of ((1+T)u−1)⁻¹ = (u−1)⁻¹·Σ(−u/(u−1))ⁿTⁿ-form
  (Ring.inverse of unit-constant-term series; finite verification per
  coefficient).
- **Sources**: TeX 2102–2105; decomposition R6 P6.
- **Sizing**: ~100 LOC.

### [T613] ∂F̃_θ = F_θ
- **Status**: done (2026-06-11)
- **Progress**: DONE (same pass): linearity + per-c P6-p2 + character-sum
  cancellation (MulChar.sum_eq_zero_of_ne_one + range↔ZMod reindex).
  Axioms standard.
- **Type**: theorem
- **Statement**: skeleton `one_add_mul_derivative_Ftilde` (P6-p3).
- **Proof sketch**: sum p2 over c; the constant `1`-terms contribute
  −Σ_c θ⁻¹(c)·1 = 0 (sum of a nontrivial character — mathlib
  DirichletCharacter sum_eq_zero; verify name; note the sum is over
  range N with θ⁻¹ killing non-units).
- **Sources**: TeX 2100–2110 (Lem 6.3 proof, first display).
- **Sizing**: ~50 LOC.

### [T614] ρ_θ: support, x-multiplication, and the twist display
- **Status**: done (2026-06-11)
- **Progress**: DONE (same pass): psi∘iota = 0 via mem_range_iota_iff;
  x-multiplication via invUnitsCM-cancellation (extendByZero_comp_unitsVal)
  + mahlerTransform_cmul_X (del K) + map-∂ commutation helpers. hGtwist
  instantiation deferred to T617 assembly (hypothesis-form retained).
  Axioms standard.
- **Parallel**: yes | **Type**: lemmas
- **Statement**: skeleton `psi_rhoTheta`,
  `one_add_mul_derivative_mahlerK_rhoTheta` + NEW (spawn at execution):
  the hGtwist-instantiation lemma (mahlerK of the χ-twisted μ̃_η equals
  the explicit G-cleared series — from T508's
  mahlerTransform_charTwist_muEtaCleared, CRT-collapsed to level Dp^n).
- **Proof sketch**: support: iota-image is unit-supported
  (res_iota/mem_range_iota_iff + isSupportedOn_units_iff_psi_eq_zero);
  ∂𝓐: x·ρ = Res(μ_θ) by invCM-cancellation on units
  (extendByZero/invUnitsCM algebra, the §5 T516/T520 patterns) +
  LemmaMultiplicationbyx = mahlerTransform_cmul_X; map-subtype the
  identity. hGtwist: T508 display + the Σ_aΣ_b → Σ_c CRT collapse with
  ε := ζK·εp-product-root (the c4-twist constants surface; coordinate
  with T609's conventions).
- **Sources**: TeX 2090–2110 (Lem 6.3); decomposition R6 P6.
- **Sizing**: ~140 LOC (the §5-glue ticket).

### [CLEANUP-66] /cleanup on ValuesAtOne.lean (cadence)
- **Status**: done (degraded mode, 2026-06-12) | **Depends on**: T612, T613, T614
- **Type**: cleanup
- **Progress**: subsumed by the continuous per-ticket golf through
  T615–T617 and the CL67 final sweep (same file; build green, zero
  warnings, zero long lines verified 2026-06-12). Tooled CLEANUP-FINAL
  carries the per-decl golf queue.

### [T615] The constant pin: 𝓐(ρ_θ) = F̃_θ − φψF̃_θ
- **Status**: done (2026-06-11; hnorm hypothesis added — logged)
- **Depends on**: T613, T614, T607, T606 | **Type**: theorem
- **Statement** (REALIGNED R6.6, c₀-design):
  `p_mul_constantCoeff_mahlerK_rhoTheta` — p·𝓐_ρ(0)·G-form =
  p·F̃(0) − Σ_i F̃(ξ^i−1); via W := CG⁻¹F̃ − 𝓐_ρ, ∂W = φB,
  antiderivative + ker∂ + ξ-point evaluation + sum_seriesEval_mahlerK
  + psi_rhoTheta.
- **Proof sketch**: both sides ∂-agree (T613 + T614 + ψ∂-commutation b3
  pushing ∂ through φψ: ∂(φψF̃) = p·φ(∂ψF̃) = φψ(∂F̃)); difference D has
  (1+X)·derivative(D) = 0 ⟹ D = C(D₀) (b7); ψ(LHS) = 0 (T614-support +
  b4-bridge + psiSeries_map), ψ(RHS) = 0 (ψφ = id, b2), ψC = C (b2) ⟹
  D₀ = 0. The G-clearing scalar rides along via psiSeries_C_mul.
- **Sources**: decomposition R6 replan 1 (the distribution-free Lem 6.3).
- **Sizing**: ~80 LOC.

### [T616] The evaluated trace of F̃_θ
- **Status**: done (2026-06-12; statement-fix hdom→hnorm logged; boundary-log prerequisite = T618)
- **Depends on**: T608, T603, T604, T612 | **Type**: theorem
- **Statement** (REALIGNED R6.6, ψ-free): `sum_seriesEval_Ftilde` —
  Σ_i F̃(ξ^i−1) = θ(p)·F̃(0); cases as before.
- **Proof sketch**: b6 (psiSeries_eval_zero) on F̃: need seriesEval F̃ at
  ξ^i−1: per-c resummation Ftilde_eval (spawn as helper): seriesEval of
  logSeriesAt(u) at z = extLog((1+z)u−1) via (1+z)u−1 = (u−1)(1+uz/(u−1)),
  extLog_mul (T604), extLog-on-ball = padicLog + its series (T522/T604);
  then Σ_i Σ_c θ⁻¹(c)extLog(ξ^i ε^c−1): μ_p-collapse
  Σ_i extLog(ξ^iw−1) = extLog(w^p−1) (Π_i(ξ^iw−1) = w^p−1: Π over μ_p +
  Πξ^i = 1 for p odd; extLog_mul; domains by T603 + p9-norm-ones);
  c-bookkeeping: n = 0: c ↦ pc automorphism of (ℤ/D)ˣ pulls θ(p) out;
  n ≥ 1: fibers of c ↦ pc are N/p-translates; inner sum
  Σ_{j<p} θ⁻¹(c+jN/p) = 0 by primitivity (spawn small lemma
  sum_shift_eq_zero_of_isPrimitive per replan 3); both sides 0 = θ(p)·…
- **Sources**: TeX 2115–2155 (the two-case proof); decomposition R6
  replans 2–3.
- **Sizing**: ~150 LOC (the section's hardest ticket).

### [CLEANUP-ALL-6] Pre-milestone /cleanup-all
- **Status**: done (degraded mode, 2026-06-12) | **Depends on**: T601–T616
- **Type**: cleanup-all
- **Progress**: degraded sweep over the four §6 files: zero warnings,
  zero long lines, single remaining sorry = T617 headline. Per-ticket
  golf was continuous; tooled CLEANUP-FINAL queued.

### [T617] **MILESTONE: RJW Theorem 6.1(ii)** — L_p(θ,1) (Leopoldt)
- **Status**: done (2026-06-12) | **Verification**: `lake build PadicLFunctions`
  green (3660 jobs); `#print axioms LpFunction_one` = {propext, Classical.choice,
  Quot.sound}; zero sorries project-wide; linter clean (≤100-char); blueprint green.
- **Depends on**: T615, T616, T609, CLEANUP-ALL-6 | **Type**: theorem
- **Statement**: `LpFunction_one` (P6-p8), proven sorry-free.
- **Proof sketch**: LpFunction at s = 1 pairs ζ_η-cleared with χ̃·⟨x⟩⁰ = χ̃;
  identify the pairing with the mass of ρ_θ (extendByZero/χ̃-through
  lemma); mass = constantCoeff(𝓐_ρ) (apply_powCM 0); T615 + T616 give
  (1−θ(p)p⁻¹)·F̃(0) up to G-clearing; F̃(0) = −Σθ⁻¹(c)extLog(ε^c−1) =
  −Σθ⁻¹(c)extLog(1−ε^c) (extLog_neg, domains T603); un-clear through
  T609 (G(θ⁻¹)-factorisation) to RJW's display.
- **Sources**: TeX 1992–1995 + 2113–2155 (verbatim at R6).
- **Progress (2026-06-12, COMPLETE)**:
  - **Statement-fix (authorised, recorded in b2_log.jsonl)**: added
    `{εp : integerRing K} (hεp : IsPrimitiveRoot εp (p^n))
    (hsplit : ε = (ζ:K)·(εp:K))` — the §6 root ε is tied to the §5 split data
    (RJW's ε_N is any primitive N-th root; the split form ζ·ε_{p^n} realises it
    through the tame/wild factors). This is what enables the Gauss-product split.
  - **G-clearing as landed (the step-3 key)**: the headline G = G(θ⁻¹) is NOT a
    unit in integerRing K (its norm is p^{-n/2}); it is a K-field nonzero, hence
    a K-unit. The hGtwist hypothesis of T615 is fed G₀ := GχK := the K-coercion
    of the level-p^n Gauss sum (also a K-field nonzero). The hGtwist closed form
    `mahlerK(twist χ̃ μ̃η) = C(GχK⁻¹)·(−Σ_{c<N} C(θK⁻¹ c)·inv((1+X)C(ε^c)−1))`
    is built in three steps: (3a) integerRing closed form of GχR•𝓐(twist) via
    `mahler_twist_formula` + `mahlerTransform_charTwist_muEtaCleared`; (3b) map to
    K (c=0 rows killed by η⁻¹(0)=0; c≠0 inverse-map via
    `isUnit_root_mul_pow_one_add_X_sub_one`); (3c) CRT-collapse the (b,c) double
    sum to range N at the glued root via the new private `crt_collapse`. The final
    G-product G = GηK·GχK is `gaussSum_mul_coprime` (ValuesAtOneComplex, general
    domain R = K) at the split root + `coe_gaussSum_zmodChar` ×2.
  - **New helpers**: `crt_collapse` (the §6 step-3c double-sum CRT collapse, via
    ZMod reindex + ZMod.chineseRemainder + θ⁻¹ factorisation + root period-split);
    `toFieldChar_changeLevel` (toFieldChar/changeLevel commutation). Added import
    `PadicLFunctions.ValuesAtOneComplex` (no circularity).
  - **hnorm discharge**: `norm_pow_sub_one_eq_one_of_unit` (T612 cluster, already
    in file). Sign flip via `extLog_neg` + `extLogDomain_of_integral_norm_one`.
- **Blueprint**: §6 chapter — wired `val1-padic-s1` → `LpFunction_one` (D>1 +
  distribution-free + split-root notes); `val1-x-mu-tilde` →
  `one_add_mul_derivative_Ftilde` (distribution-free ∂F̃=F note + companion
  `one_add_mul_derivative_mahlerK_rhoTheta`); `val1-Ftilde-in-Rplus` left unwired
  with the R6.6 coefficient-bound rationale (`summable_seriesEval_Ftilde`).
- **Sizing**: ~310 LOC (incl. crt_collapse + hGtwist chain; ~120 estimated, the
  full CRT collapse cost more).

### [CLEANUP-67] Final per-file cleanups (§6 files)
- **Status**: done (degraded mode, 2026-06-12) | **Depends on**: T617
- **Type**: cleanup (ExtLog, FormalPsi, ValuesAtOne[Complex] final;
  CLEANUP-FINAL scope widened to §6)
- **Progress**: degraded sweep: build green, zero warnings, zero long
  lines, zero sorries project-wide. Queued for tooled CLEANUP-FINAL:
  per-decl golf of the §6 files (esp. T617's crt_collapse ~310 LOC —
  /decompose-proof candidate), the T618 bridge-layer placement review
  (boundary-log lemmas live in ValuesAtOne.lean for import-graph reasons —
  consider a dedicated file when ValuesAtOne approaches the split
  threshold).

## §6 dependency quick-view
```
W6a: T601 → T604 ;  T602 → T603         → CL61
W6b: T605 → T606 → {T607, T608}         → CL63
C6:  T609 ; T610 → T611                 → CL65
P6:  T612 → T613 ; T614 → CL66 → T615(T607,T606)
     T616(T608,T603,T604,T612) → CLALL6 → T617*(T615,T616,T609) → CL67
```
Gate note: decomposition R6 is at draft-1 — per-leaf attack-blocks in the
binding format and the c2/c4-survey completions are folded into each
ticket's execution preamble (the §5 T521-precedent); the route-level
attacks that already fired are recorded in R6 (replans 1–5).

### [T618] Boundary p-adic logarithm (unit-ball multiplicativity)
- **Status**: done (2026-06-12)
- **Progress**: DONE (subagent): formalLog + ∂-pin φ(L) = p•L (3-line
  ker-∂ argument as planned); eval-alignment seriesEval formalLog (z−1) =
  padicLog z; padicLog_pow_p via the subst-eval product-Fubini bridge;
  unit-ball padicLog_mul by p-power descent; extLog_eq_padicLog on the
  whole open ball. Bridge lemmas live in ValuesAtOne.lean (import-graph
  meeting point — placement note recorded). Axioms standard. | **File**: PadicExp.lean (+ ExtLog.lean bridge)
- **Depends on**: T522, T607, T608 | **Parent**: T616 | **Type**: lemmas
- **Statement**: `formalLog : PowerSeries K` (coeffs 0, (−1)^{n−1}/n);
  `one_add_mul_derivative_formalLog : (1+X)·D(formalLog) = 1`;
  `phiSeries_formalLog : phiSeries p formalLog = (p:K) • formalLog`
  (∂-match via one_add_mul_derivative_phiSeries + ker-∂ pin);
  `seriesEval_formalLog : ‖z−1‖ < 1 → seriesEval formalLog (z−1) = padicLog z`
  (series alignment); `padicLog_pow_p_of_norm_lt_one : ‖z−1‖ < 1 →
  padicLog (z^p) = p • padicLog z` (eval the formal identity via
  seriesEval_phi_of_summable_prod, linear-growth summability);
  `padicLog_mul_of_norm_lt_one` (p-power descent to the exp-ball, T522's
  padicLog_mul, torsion-free cancel); `padicLog_pow_of_norm_lt_one`;
  `extLog_eq_padicLog_of_norm_lt_one` (descent witness (p^j,0,x^{p^j})).
- **Proof sketch**: as in the Statement field — all tools exist after
  T605–T615 (recorded route, parent T616's flag 2026-06-11/12).
- **Mathlib lemmas**: existing project API only.
- **Sources**: Washington §5.1 (log on the unit ball); decomposition R6.6.
- **Generality**: K-coefficients (the ambient); padicLog-statements over
  the PadicExp L when free.
- **Sizing**: ~80–120 LOC (toolkit exists).

---

# §7 board (The residue of ζ_p at s = 1; TeX 2181–2360) — created 2026-06-12

Skeleton: PadicLFunctions/ResidueZeta.lean (13 sorries), build green.
Decomposition: decomposition.md R7 (verbatim quotes + replans 1–4).
Statements live in the skeleton; the §6 statement-fix protocol applies.

### [T701] Exponential tail and the character isometry
- **Status**: done (2026-06-12) | **File**: ResidueZeta.lean | **Depends on**: none
- **Progress**:
  - 2026-06-12: both decls proven (subagent, batched with T702). Tail bound came
    out cleaner than sketched: per-term `(p−1)`-power comparison via
    `norm_factorial_inv_smul_pow_le` + `p·(p·‖w‖^{p−1})^{n−2} ≤ p ≤ p^{p−1}`
    (helper `norm_factorial_inv_smul_pow_le_quad`); tail by
    `IsUltrametricDist.norm_tsum_le_of_forall_le` after peeling n∈{0,1} with
    `Summable.tsum_eq_zero_add` ×2. Isometry exactly per sketch (T523 bridge +
    `norm_padicExp_sub_one` + `norm_padicLog`). Verified: build green, axioms
    standard 3. Cleanup: degraded mode (no lean-lsp MCP) — code reviewed, calc
    structure clean; defer golf to CLEANUP-71.
- **Parallel**: yes | **Type**: lemmas
- **Statement**: skeleton `norm_padicExp_sub_one_sub_self_le`,
  `norm_onePAdicPow_sub_one` (R7.1a/b).
- **Proof sketch**: tail: peel n ∈ {0,1} of the exp series
  (tsum_eq_zero_add ×2, the T521 patterns), bound the n ≥ 2 terms at the
  (p−1)-power level ((‖(n!)⁻¹‖·‖w‖^{n−2})^{p−1} ≤ p^{n−1}·p^{−(n−2)} = p,
  then a^{p−1} ≤ p ⟹ a ≤ p since p ≥ p^{1/(p−1)}: cleanest rpow-free:
  a^{p−1} ≤ p ≤ p^{p−1} ⟹ a ≤ p by pow-mono) + ultrametric tail-max
  (norm_tsum_le_of_forall_le). Isometry: onePAdicPow y t =
  pZpExp(t·pZpLog y) (T523 padicExp_smul_padicLog_eq_onePAdicPow at s := t
  — mind the argument order: pZpExp p (t * pZpLog p y)), then coe-norms +
  norm_padicExp_sub_one (ball: ‖t·log y‖ ≤ ‖y−1‖ ≤ p⁻¹, p odd strict) +
  norm_padicLog through pZpLog_coe; multiplicativity of the padic norm.
- **Sources**: TeX 2236–2248 (the binomial route it replaces — replan R7.3);
  Washington §5.1.
- **Sizing**: ~90 LOC.

### [T702] The branch denominator: primitivity, nonvanishing, derivative
- **Status**: done (2026-06-12) | **File**: ResidueZeta.lean | **Depends on**: T701
- **Progress**:
  - 2026-06-12: all three decls proven (subagent, batched with T701).
    Primitivity via `orderOf_map_dvd` against `unitsToZModPow p 1` (level-1
    reduction has order p−1 by hgen; `ker_toZModPow` + `teichmullerFun_sub_self_mem`
    identify the reductions). Nonvanishing: helper
    `norm_teichmuller_pow_sub_one_eq_one` (`norm_lt_one_iff_dvd` contrapositive)
    + ultrametric isoceles `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`.
    Derivative limit: NO case split on L = 0 needed — the squeeze
    `‖f(s)+L‖ ≤ p·‖L‖²·‖s−1‖ → 0` (via T701a) covers it uniformly;
    `squeeze_zero_norm'` + `linear_combination` for the pointwise identity.
    Verified: build green, axioms standard 3. Cleanup: degraded mode, defer to
    CLEANUP-71.
- **Type**: lemmas
- **Statement**: skeleton `teichmuller_isPrimitiveRoot`,
  `branch_denom_ne_zero`, `tendsto_branch_denom_div` (R7.2a/b/c).
- **Proof sketch**: a: hgen at n = 1 gives u mod p generates (ZMod p)ˣ
  (order p−1); ω(u)'s order = order of the reduction (toZMod_teichmullerZMod
  section + injectivity of teichmullerZMod on its image — the
  exists_primitiveRoot_card_sub_one proof in Branches is the template).
  b: branchChar i s u − 1 = ω(u)^i⟨u⟩^s − 1 = (ω^i − 1) + ω^i(⟨u⟩^s − 1);
  ‖ω^i − 1‖ = 1 (i < p−1, primitivity: the reduction ω̄^i = ū^i ≠ 1 in
  ZMod p ⟹ norm-1 via the residue argument), ‖⟨u⟩^s − 1‖ ≤ p⁻¹ < 1
  (onePAdicPow_sub_one_mem) ⟹ isoceles norm = 1 ≠ 0; coe to ℚ_[p].
  c: ω(u)^{p−1} = 1 (teichmullerFun_pow_card_sub_one) so the denominator
  is ⟨u⟩^{1−s} − 1 = pZpExp((1−s)·L) − 1 with L := pZpLog⟨u⟩ (T523);
  write (s−1)⁻¹(exp(w)−1) with w := (1−s)L = −(s−1)L:
  = −L·[w⁻¹(exp w − 1)] and w⁻¹(exp w −1) → 1 by T701a (ε-δ: ‖w⁻¹(exp w − 1)
  − 1‖ = ‖w‖⁻¹‖exp w − 1 − w‖ ≤ p‖w‖ → 0 as s → 1; w ≠ 0 iff s ≠ 1 and
  L ≠ 0 — case L = 0: ⟨u⟩ = 1 forces the limit statement trivially?? NO:
  if L = 0 then denominator ≡ 0 and the limit claim says → 0 ✓ both sides
  0 — handle the L = 0 case separately (limit of 0-function = −0 ✓);
  coe-bookkeeping ℤ_[p] → ℚ_[p] (continuous ring hom).
- **Sources**: TeX 2218–2256 verbatim at R7; replan R7.3.
- **Sizing**: ~130 LOC.

### [T703] Continuity of the numerator and Theorem 7.1(i)
- **Status**: done (2026-06-12) | **File**: ResidueZeta.lean | **Depends on**: T702
- **Progress**:
  - 2026-06-12: both decls proven (subagent). Congruence route exactly per
    sketch, p = 2 allowed: helpers `onePAdicPow_sub_one_mem_span_pow`
    (exponent congruence via `AddChar.map_nsmul_eq_pow` +
    `dvd_sub_pow_of_dvd_sub`) and `norm_onePAdicPow_sub_one_le`
    (p=2-valid `‖y^t−1‖ ≤ ‖t‖`); pairing is `LipschitzWith 1` via
    `PadicMeasure.norm_apply_le`. Thm 7.1(i) = `ContinuousAt.inv₀` +
    `branch_denom_ne_zero` + pairing continuity. New import:
    Mathlib.NumberTheory.Basic. Verified: build green, axioms standard 3.
    Cleanup: degraded mode (no MCP), unused bindings removed; defer golf to
    CLEANUP-71.
- **Type**: lemmas
- **Statement**: skeleton `continuous_zetaNum_branch_pairing`,
  `continuousAt_zetaPBranch` (R7.3a + Thm (i)).
- **Proof sketch**: pairing: Metric/ε-route: for s ≡ s' mod p^m the
  integrands agree mod p^m uniformly: branchChar i (1−s) x −
  branchChar i (1−s') x = ω^i⟨x⟩^{1−s'}(⟨x⟩^{s'−s} − 1) with
  ⟨x⟩^{s'−s} − 1 ∈ span{p^m} (onePAdicPow_sub_one_mem_pow at the
  difference, T519) ⟹ ‖f_s − f_{s'}‖_sup ≤ p^{−m}; the §3 measure norm
  bound (PadicMeasure.norm_apply_le — verify exact name; the §3 board
  had it) gives ‖pairing(s) − pairing(s')‖ ≤ ‖zetaNum‖·p^{−m}; coe
  continuous. Thm (i): zetaPBranch is the quotient; numerator continuous
  (pairing-lemma at the §4 generator m), denominator continuous
  (same congruence bound on s ↦ branchChar-at-u) and ≠ 0 everywhere near 1
  (T702b) ⟹ ContinuousAt of the product/inverse (the dite-free def:
  zetaPBranch = (denom)⁻¹·num: Continuous.inv₀-route at s = 1).
- **Sources**: TeX 2228–2231 ("This already implies Theorem 7.1(i)").
- **Sizing**: ~100 LOC.

### [CLEANUP-71] /cleanup on ResidueZeta.lean (cadence)
- **Status**: open | **Depends on**: T701, T702, T703 | **Type**: cleanup

### [T704] The antiderivative F̃_a and ∂F̃_a = F_a
- **Status**: open | **File**: ResidueZeta.lean | **Depends on**: none
- **Parallel**: yes (mass-chain head) | **Type**: def-lemmas
- **Statement**: skeleton `constantCoeff_FtildeA`,
  `one_add_mul_derivative_FtildeA` (R7.4c/d; defs uA/FtildeA in skeleton).
- **Proof sketch**: constant: coeff-0 extraction (subst at constant-0
  argument has constantCoeff = formalLog(0) = 0: constantCoeff_subst-route
  or coeff_subst' at 0; smul-part 0). Derivative: ∂ is additive;
  ∂(C) = 0; ∂(formalLog∘(uA−1)) via derivative_subst (chain rule) +
  one_add_mul_derivative_formalLog-shape: (1+X)·D(L∘G) where ∂L = 1:
  compute (1+X)D(L.subst G) = (DL).subst G · (1+X)DG = [(1+(uA−1))⁻¹-free?
  — careful: ∂L = 1 means (1+X)·DL = 1 i.e. DL = (1+X)⁻¹: (DL).subst G =
  Ring.inverse(1 + G-shifted)... work it: (1+X)·D(L∘(uA−1)) =
  Ring.inverse(uA)·(1+X)·D(uA) (the log-derivative); ∂((a−1)•L) = (a−1)•1.
  Target Fa: verify PadicMeasure.Fa's exact closed form (MuA.lean: Fa :=
  FaNum-based — READ; RJW: F_a = 1/T − a/((1+T)^a−1); with
  (1+T)^a − 1 = aT·uA: a/((1+T)^a−1) = T⁻¹·uA⁻¹: F_a =
  T⁻¹(1 − uA⁻¹) — honest series ✓); the identity reduces to
  uA-algebra: (1+X)·D(F̃) = (a−1) − inverse(uA)·(1+X)·D(uA) ≟ map(Fa):
  per RJW's Lemma 7.3 computation; expect ~80 LOC of series algebra
  (geometric-inverse helpers from T612 reusable).
- **Sources**: TeX 2266–2279 + 2296–2305 verbatim at R7.
- **Sizing**: ~120 LOC.

### [T705] The measure ρ_a: support and x-multiplication
- **Status**: open | **File**: ResidueZeta.lean | **Depends on**: none
- **Parallel**: yes | **Type**: lemmas
- **Statement**: skeleton `psi_rhoA`, `one_add_mul_derivative_mahlerK_rhoA`
  (R7.5b/c; def rhoA in skeleton).
- **Proof sketch**: support: iota-image is unit-supported at the §4 level
  (Measure/UnitsZp's res_iota/mem-range machinery — the ℤ_[p]-precursors
  of the MeasureR ones); transport through baseChange: need
  ψ∘baseChange = baseChange∘ψ (NEW small naturality lemma — the TW6 notes
  deferred it; prove via mahlerTransform_baseChange + mahlerTransform_psi
  + injectivity of the Mahler transform (mahlerRingEquiv), ~30 LOC) — or
  directly: ψ(baseChange(iota ν)) = 0 via the transform-route. x-mult:
  x·zetaNum = muAUnits at the §4 level (zetaNum := unitsCmul invCM
  muAUnits: x·(x⁻¹·μ) = μ — the unitsCmul-algebra, the T614 pattern at
  ℤ_[p]-level); iota∘(units-measure) vs res∘(ℤ_p-measure):
  iota(muAUnits) = res units (muA) (the §4 relation — survey ZetaP/MuA
  for it; muAUnits := res-to-units of muA presumably definitional);
  baseChange is a ring hom commuting with the transform
  (mahlerTransform_baseChange); del/derivative transport as in T614
  (map_derivativeFun helpers exist in ValuesAtOne — may need export or
  re-prove locally).
- **Sources**: TeX 2258–2264; ZetaP.lean (zetaNum def).
- **Sizing**: ~110 LOC.

### [T706] The mass identity (c₀-pin + trace)
- **Status**: open | **File**: ResidueZeta.lean
- **Depends on**: T704, T705 | **Type**: theorems
- **Statement**: skeleton `p_mul_constantCoeff_mahlerK_rhoA`,
  `sum_seriesEval_FtildeA`, `constantCoeff_mahlerK_rhoA` (R7.6a/b/c).
- **Proof sketch**: pin: T615's proof VERBATIM minus the G-clearing
  (W := F̃_a − 𝓐ρ_a; ∂W = φψ-part via T704+T705 and res_units_eq;
  antiderivative + ker-∂ + ξ-point evaluation + sum_seriesEval_mahlerK +
  psi_rhoA; summability of seriesEval F̃_a from the log-growth coefficient
  helpers (T615/T616's summable-machinery — uA-coefficients are integral
  (a⁻¹C(a,n+1) ∈ ℤ_p for p∤a: a unit in ℤ_p... over K: bounded by
  ‖a⁻¹‖ = 1) + formalLog's 1/n). Trace: per-point seriesEval F̃_a (ξ^i−1)
  = −extLog(a) − extLog(uA-eval at ξ^i−1)-resummation + (a−1)·padicLog(ξ^i)
  -part: CAREFUL — formalLog∘(uA−1) evaluated at ξ^i−1: the subst-eval
  bridge (seriesEval_phi_of_summable_prod-pattern but for the uA-subst:
  general subst-eval — survey what T616 built: seriesEval_logSeriesAt-
  machinery; may need a small general lemma seriesEval-of-subst at
  convergence, the T618 toolkit shapes); then the algebra: F̃_a(ξ^i−1) =
  log of [(ξ^i−1)/(ξ^i·... the RJW per-ξ rearrangement TeX 2330–2340:
  F̃_a((1+T)ξ−1)|_{T=0} = log((ξ−1)/(ξ^a−1)·ξ^{a−1})-values via extLog
  (domains: ξ^j−1 norm-known (FormalPsi's norm_sub_one_lt-machinery) +
  roots-of-unity integrality — the T616-pattern helpers); Σ_i: collapse
  Σ_i extLog(ξ^i−1) − Σ_i extLog(ξ^{ai}−1) + (a−1)Σ_i extLog(ξ^i):
  third sum = 0 (torsion); first two cancel by the {ξ^a} = μ_p reindex
  (i ↦ ai mod p bijection, p∤a) EXCEPT the i = 0 terms — careful:
  i = 0: F̃_a(0) = −extLog(a) ✓ included in the Fin p-sum: total =
  −extLog(a) + [Σ_{i≠0}(extLog(ξ^i−1) − extLog(ξ^{ai}−1)) = 0 by
  reindex] + 0 = −extLog(a) ✓ matches R7.6b. Combine: c₀-identity +
  trace + constantCoeff_FtildeA ⟹ R7.6c (field algebra, (p:K) ≠ 0).
- **Sources**: TeX 2320–2352 verbatim at R7.
- **Sizing**: ~200 LOC (the section's largest).

### [T707] Descent: the ℚ_p-level mass
- **Status**: open | **File**: ResidueZeta.lean | **Depends on**: T706
- **Type**: theorem
- **Statement**: skeleton `zetaNum_one` (R7.7).
- **Proof sketch**: instantiate K := ℂ_[p] (mathlib PadicComplex:
  SURVEY-GATED — verify NormedField/NormedAlgebra ℚ_[p]/IsUltrametricDist/
  CompleteSpace/CharZero instances + obtain ξ from PadicAlgCl's
  algebraically-closed primitive root mapped along the embedding with
  IsPrimitiveRoot.map; FALLBACK if any instance is missing: state the
  K-pack as hypotheses on a wrapper lemma and instantiate in a later
  ticket — record). Identify: the K-coe of the ℚ_p-mass =
  constantCoeff(mahlerK ρ_a) (mass = apply at powCM 0 = the §4 pairing
  at 1 via baseChange_algCM-characterisation/iota-unfold + apply_powCM);
  R7.6c gives the K-value −(1−p⁻¹)·extLog((a:K)); extLog commutes with
  the embedding ℚ_[p] → K on the rational-valuation domain
  (`algebraMap_extLog` helper: the witness transports; ~30 LOC);
  algebraMap-injectivity (field hom) concludes.
- **Sources**: TeX 2258–2264; replan R7.4.
- **Sizing**: ~90 LOC + survey risk.

### [CLEANUP-ALL-7] Pre-milestone /cleanup-all
- **Status**: open | **Depends on**: T701–T707 | **Type**: cleanup-all

### [T708] **MILESTONE: RJW Theorem 7.1** — the residue of ζ_p
- **Status**: open | **File**: ResidueZeta.lean
- **Depends on**: T703, T702, T707, CLEANUP-ALL-7 | **Type**: theorem
- **Statement**: skeleton `tendsto_sub_one_mul_zetaPBranch` (Thm (ii);
  Thm (i) = `continuousAt_zetaPBranch`, T703).
- **Proof sketch**: unfold zetaPBranch at the §4 generator (m, u);
  (s−1)·ζ(s) = [(s−1)·g(s)⁻¹]·num(s) = [(s−1)⁻¹g(s)]⁻¹·num(s)
  (g ≠ 0 for s ≠ 1 near 1 — from the T702c limit ≠ 0: L := pZpLog⟨u⟩ ≠ 0
  since ⟨u⟩ ≠ 1 (generator: u has infinite order; ω(u)-part finite order
  ⟹ ⟨u⟩ ≠ 1 — extract from topGen_pow_ne_one/T037) + norm_padicLog;
  eventual-nonvanishing from the limit); Tendsto-algebra:
  (s−1)⁻¹g(s) → −L-coe ≠ 0 (T702c) and num(s) → num(1) (T703-pairing
  continuity); num(1) = zetaNum-mass: branchChar (p−1) 0 = 1-on-units
  (ω^{p−1} = 1, ⟨·⟩⁰ = 1: teichmullerFun_pow_card_sub_one +
  AddChar-at-0 ⟹ the pairing at s = 1 is zetaNum p m 1) =
  −(1−p⁻¹)·extLog(m) (T707; p∤m from the generator pack hpm);
  extLog((m:ℚ_[p])) = L-coe (`extLog_natCast_eq_pZpLog_angle` helper:
  m-as-unit u (huv : (u:ℤ_[p]) = m), u = ω(u)·⟨u⟩, extLog-additivity +
  torsion-kill + extLog_eq_padicLog-on-ball + pZpLog_coe; ~40 LOC);
  Tendsto.mul: (−L)⁻¹·(−(1−p⁻¹)L) = 1−p⁻¹ ✓ (L ≠ 0).
- **Sources**: TeX 2187–2194 + 2258–2360 (verbatim at R7).
- **Blueprint**: Chapters/Residue.lean — wire Thm 7.1 (both decls),
  Lem 7.2 (T702 pair), Lem 7.3 (T704), Lem 7.5 (T706c); Lem 7.4
  rationale-comment (ℛ⁺ deferred, replan R7.1); re-render.
- **Sizing**: ~130 LOC.

### [CLEANUP-72] Final per-file cleanup (ResidueZeta.lean)
- **Status**: open | **Depends on**: T708 | **Type**: cleanup
  (+ widen CLEANUP-FINAL to §7)

## §7 dependency quick-view
```
T701 → T702 → T703 → CL71 ;  T704 ; T705 → T706(T704) → T707 → CLALL7
  → T708*(T703,T702,T707) → CL72
```
