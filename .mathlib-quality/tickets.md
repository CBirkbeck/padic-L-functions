# Ticket Board — §3 Measures and Iwasawa algebras

Source: RJW arXiv:2309.15692, TeX in `.mathlib-quality/references/` (line numbers cited
per ticket). Decomposition + per-leaf verbatim quotes + attack logs:
`.mathlib-quality/decomposition.md` (leaf labels L*.* below refer to it).
Skeleton: all statements already exist as `:= by sorry` in `PadicLFunctions/Measure/`;
**tickets are "fill the sorry at file:decl"** — statements are quoted for convenience
but the skeleton is canonical. `lake build` green at board creation.

## Summary
- Total: 30 work tickets + 12 cleanup tickets
- Open: 2 (T029, CLEANUP-FINAL) | Done: 40 — ALL PROOF TICKETS DISCHARGED, project sorry-free (2026-06-10)
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
