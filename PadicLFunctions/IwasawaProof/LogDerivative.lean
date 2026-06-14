/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Coleman.Map

/-!
# The logarithmic derivative: the Coleman–Coates–Wiles exact sequence (RJW §12.2.1) — E12.2

`thm:log der` (TeX 3280–3379): the short exact sequence
`0 → μ_{p−1} → (ℤ_p⟦T⟧^×)^{𝒩=id} →[Δ] ℤ_p⟦T⟧^{ψ=id} → 0`. This is the hardest
mathematics in Part II; `lem:B mod p 2` (the explicit `𝔽_p⟦T⟧` construction) is, per the
authors, "the most delicate and technical part". The kernel `μ_{p−1}` is `rem:ker Δ`
(constants `𝒩`-fixed force `f^p = f`); surjectivity reduces mod `p` (`lem:log der red
mod p`, successive approximation + `ℤ_p⟦T⟧^×` compactness from §10) to `A = B`
(`lem:A mod p` + `lem:B mod p`).

Status (T1203 execution). Closed sorry-free in this pass:
* the `ψ`-`Submodule` proof-fields (`psiIdSeries`, `psiZeroSeries`);
* `del_phiHom` (`Δ ∘ φ = p · φ ∘ Δ`, from `one_add_mul_derivative_phiSeries`);
* `dlog_eq_zero_normOp_fixed` (`rem:ker Δ`: `dlog g = 0`, `𝒩 g = g` ⟹ `g = C c`, `c^p = c`);
* `one_sub_phi_psiId_mem_psiZero` (forward half of `lem:rest zp*`);
* `exists_normOp_fixed_lift` (`lem:A mod p`), with its new mod-`p^k` continuity layer
  (`normOp_modEq_of_modEq`, `modEqPow_of_tendsto`, `eq_of_forall_modEqPow`);
* `exists_one_sub_phi_eq` (converse half of `lem:rest zp*`), via the coefficientwise
  `(1−pⁿ)`-recursion `solCoeff` solving `(1−φ)G = F` (`mk_solCoeff_sub_phi`);
* **`dlog_mem_psiIdSeries` (`lem:log der 1`) — now CLOSED** via the determinant/Jacobi
  route (replacing RJW's non-formal `μ_p`-product `φ(f) = ∏_η f((1+T)η−1)`, replan R10.4).
  New reusable infrastructure: `derivation_det` (Jacobi's `D(det M) = ∑_i det(M[row i↦D])`,
  built from the Leibniz `derivation_finset_prod`), `det_updateRow_eq_sum_adjugate`
  (cofactor expansion), `digitMatrix_del` (identity K:
  `(digitMatrix Δf)_{ij} = (i−j)·M_{ij} + p·Δ(M_{ij})`), `del_det_eq_smul_trace`
  (`Δ(det M) = det M • tr((M.map Δ)·N)`), `trace_D_N_zero`, and the `Δ`-Leibniz API
  (`del_mul`, `del_sum`, `del_phiSeries`, `del_one_add_X_pow`). The proof: with `M = digitMatrix f`,
  `N = M⁻¹`, `f = det M`, one gets `tr(digitMatrix(dlog f)) = 0 + p·dlog f` (identity K's
  off-diagonal trace vanishes, diagonal gives `p·dlog f`), and `tr(digitMatrix·) = p·ψ(·)`
  (`trace_digitMatrix`) plus `p`-cancellation give `ψ(dlog f) = dlog f`.

Two leaves remain (see the per-declaration obstacle notes), both entangled with the
project's deferred non-formal `Eqphipsi` (`φ∘ψ(F) = p⁻¹∑_ξ F((1+T)ξ−1)`, FormalPsi.lean):
* `fp_series_eq_dlog_add_frobC` (`lem:B mod p 2`, "the most delicate and technical part")
  — restated to the faithful `𝔽_p⟦T⟧ = Δ(𝔽_p⟦T⟧^×) + (T+1)/T·C`; needs the inductive
  `α`-filtration (`d_n=d_{np}` invariant) + the `∏(1−α_n Tⁿ)` T-adic product (mathlib hook
  `multipliable` via `order → ∞`). ~200 LOC of `𝔽_p`-combinatorics; not blocked by
  `Eqphipsi`, but also needs `dlog`-continuity for the product's log-derivative.
* `dlog_surjective_onto_psiId` (`thm:log der`) — `A = B` mod `p` + successive approximation
  `h_n = ∏ g_k^{(−1)^{k−1}p^{k−1}}` (the `dlog`-homomorphism layer `dlog_mul`/`dlog_pow`
  below is in place) + the `ℤ_p⟦T⟧^×` compactness limit (§10 substrate present; still needs
  `dlog`-continuity). The `B ⊆ A` input (`lem:B mod p`) uses the `Eqphipsi`-based
  "`ψ` fixes `(T+1)/T`" (`LemmaPsiInvariant`, TeX 1521).
-/

open PadicLFunctions PadicLFunctions.Coleman PowerSeries

noncomputable section

namespace PadicLFunctions.Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `ψ = id` subspace of `ℤ_p⟦T⟧` (RJW `ℤ_p⟦T⟧^{ψ=id}`), via the series trace
operator `psiSeries`. -/
def psiIdSeries : Submodule ℤ_[p] (PowerSeries ℤ_[p]) where
  carrier := {F | psiSeries p F = F}
  add_mem' {F G} hF hG := by
    change psiSeries p (F + G) = F + G
    rw [psiSeries_add_padicInt, hF, hG]
  zero_mem' := by
    change psiSeries p (0 : PowerSeries ℤ_[p]) = 0
    simpa using (psiSeries_add_padicInt (p := p) 0 0).symm
  smul_mem' c F hF := by
    change psiSeries p (c • F) = c • F
    rw [PowerSeries.smul_eq_C_mul, psiSeries_C_mul_padicInt, show psiSeries p F = F from hF]

/-- The `ψ = 0` subspace of `ℤ_p⟦T⟧` (RJW `ℤ_p⟦T⟧^{ψ=0}`). -/
def psiZeroSeries : Submodule ℤ_[p] (PowerSeries ℤ_[p]) where
  carrier := {F | psiSeries p F = 0}
  add_mem' {F G} hF hG := by
    change psiSeries p (F + G) = 0
    rw [psiSeries_add_padicInt, show psiSeries p F = 0 from hF,
      show psiSeries p G = 0 from hG, add_zero]
  zero_mem' := by
    change psiSeries p (0 : PowerSeries ℤ_[p]) = 0
    simpa using (psiSeries_add_padicInt (p := p) 0 0).symm
  smul_mem' c F hF := by
    change psiSeries p (c • F) = 0
    rw [PowerSeries.smul_eq_C_mul, psiSeries_C_mul_padicInt, show psiSeries p F = 0 from hF,
      mul_zero]

/-- `ψ` is subtractive over `ℤ_[p]` (from additivity). -/
theorem psiSeries_sub (F G : PowerSeries ℤ_[p]) :
    psiSeries p (F - G) = psiSeries p F - psiSeries p G := by
  have h := psiSeries_add_padicInt (p := p) (F - G) G
  rw [sub_add_cancel] at h
  rw [h]; ring

/-- `Δ ∘ φ = p · φ ∘ Δ` on power series (RJW TeX 3301, "easy to see from the
definitions") — the engine of `lem:log der 1`. Stated for the additive `del = ∂`
(`PadicMeasure.del`). -/
theorem del_phiHom (f : PowerSeries ℤ_[p]) :
    PadicMeasure.del p (phiHom p f)
      = (p : PowerSeries ℤ_[p]) * phiHom p (PadicMeasure.del p f) := by
  rw [phiHom_apply, PadicMeasure.del, PadicMeasure.del,
    one_add_mul_derivative_phiSeries, phiHom_apply, PowerSeries.smul_eq_C_mul,
    map_natCast]

/-! ### Jacobi's formula for the derivative of a determinant (for `lem:log der 1`)

RJW prove `lem:log der 1` from the `μ_p`-product `φ(f) = ∏_η f((1+T)η−1)` (replan R10.4:
*not* a formal power-series identity). The formal substitute is **Jacobi's formula**
`Δ(det M) = ∑_i det(M[row i ↦ Δ(row i)])`, derived here over `ℤ_p⟦T⟧`-matrices from the
Leibniz rule for the derivation `PowerSeries.derivative` applied to the Leibniz determinant
expansion `det M = ∑_σ ε(σ) ∏_i M_{σi,i}`. Mathlib has no determinant-derivative lemma, so
we build it. -/

/-- **Leibniz rule over a `Finset` product** for a derivation on power series:
`D(∏_{i∈s} g i) = ∑_{i∈s} (∏_{j∈s\{i}} g j) • D(g i)`. -/
private theorem derivation_finset_prod {R : Type*} [CommRing R]
    (D : Derivation R (PowerSeries R) (PowerSeries R)) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → PowerSeries R) :
    D (∏ i ∈ s, g i) = ∑ i ∈ s, (∏ j ∈ s.erase i, g j) • D (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha, Finset.smul_sum,
      Finset.erase_insert ha, add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hia : i ≠ a := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hia.symm, Finset.prod_insert
      (fun h => ha (Finset.mem_of_mem_erase h)), mul_smul]

/-- **Jacobi's formula** (row form): for a square matrix `M` over `ℤ_p⟦T⟧` and a derivation
`D`, `D(det M) = ∑_i det(M with row i differentiated)`. From `derivation_finset_prod`
applied to the Leibniz expansion `det M = ∑_σ ε(σ) ∏_i M_{σi,i}`, reorganised by the
substitution `i ↦ σ i`. -/
private theorem derivation_det {R : Type*} [CommRing R] {n : ℕ}
    (D : Derivation R (PowerSeries R) (PowerSeries R))
    (M : Matrix (Fin n) (Fin n) (PowerSeries R)) :
    D (M.det) = ∑ i, (M.updateRow i (fun j => D (M i j))).det := by
  classical
  rw [Matrix.det_apply', map_sum]
  have hLHS : ∀ σ : Equiv.Perm (Fin n),
      D (((Equiv.Perm.sign σ : ℤ) : PowerSeries R) * ∏ i, M (σ i) i)
        = ∑ i, ((Equiv.Perm.sign σ : ℤ) : PowerSeries R) *
            ((∏ k ∈ Finset.univ.erase i, M (σ k) k) * D (M (σ i) i)) := by
    intro σ
    rw [D.leibniz, Derivation.map_intCast, smul_zero, add_zero, derivation_finset_prod,
      Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [smul_eq_mul, smul_eq_mul])
  rw [Finset.sum_congr rfl (fun σ _ => hLHS σ)]
  have hRHS : ∀ i : Fin n, (M.updateRow i (fun j => D (M i j))).det
      = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : PowerSeries R) *
          ((∏ k ∈ Finset.univ.erase (σ.symm i), M (σ k) k) * D (M i (σ.symm i))) := by
    intro i
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (σ.symm i))]
    have hdiag : (M.updateRow i (fun j => D (M i j))) (σ (σ.symm i)) (σ.symm i)
        = D (M i (σ.symm i)) := by rw [Equiv.apply_symm_apply, Matrix.updateRow_self]
    rw [hdiag]
    congr 1
    refine Finset.prod_congr rfl (fun k hk => ?_)
    have hki : σ k ≠ i := fun h =>
      (Finset.ne_of_mem_erase hk) (by rw [← h, Equiv.symm_apply_apply])
    rw [Matrix.updateRow_ne hki]
  rw [Finset.sum_congr rfl (fun i _ => hRHS i)]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [← Equiv.sum_comp σ (fun i => ((Equiv.Perm.sign σ : ℤ) : PowerSeries R) *
    ((∏ k ∈ Finset.univ.erase (σ.symm i), M (σ k) k) * D (M i (σ.symm i))))]
  exact Finset.sum_congr rfl (fun i _ => by rw [Equiv.symm_apply_apply])

/-- `det(M with row `i` replaced by `v`) = ∑_j v_j · adjugate(M)_{j,i}` (cofactor/Cramer
expansion along the replaced row, via `cramer_eq_adjugate_mulVec` on the transpose). -/
private theorem det_updateRow_eq_sum_adjugate {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (i : Fin n) (v : Fin n → R) :
    (M.updateRow i v).det = ∑ j, v j * Matrix.adjugate M j i := by
  rw [← Matrix.det_transpose, ← Matrix.updateCol_transpose, ← Matrix.cramer_apply,
    Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl
    (fun j _ => by rw [mul_comm, ← Matrix.adjugate_transpose, Matrix.transpose_apply])

/-! ### `Δ = (1+T)∂` as a Leibniz operator, and the digit-matrix derivative identity

`Δ = del` is `(1+T)` times the derivation `derivativeFun`, so it satisfies a Leibniz rule
(`del_mul`) and commutes with finite sums (`del_sum`). The key new lemma is `digitMatrix_del`
(identity **K**): differentiating the column-digit identity
`f·(1+T)^j = ∑_i (1+T)^i φ((digitMatrix f)_{ij})` (`digitMatrix_col_isDigitDecomp`) and
re-extracting digits (`existsUnique_digits_padicInt`) gives
`(digitMatrix(Δf))_{ij} = (i−j)·(digitMatrix f)_{ij} + p·Δ((digitMatrix f)_{ij})`.
On the diagonal this is `p·Δ(M_{ii})`, the formal shadow of the chain-rule step
`Δ(f((1+T)η−1)) = (Δf)((1+T)η−1)` that RJW sum over `μ_p`. -/

/-- Leibniz rule for `Δ = del`: `Δ(ab) = (Δa)·b + a·(Δb)`. -/
private theorem del_mul (a b : PowerSeries ℤ_[p]) :
    PadicMeasure.del p (a * b) = PadicMeasure.del p a * b + a * PadicMeasure.del p b := by
  rw [PadicMeasure.del, PadicMeasure.del, PadicMeasure.del, derivativeFun_mul,
    smul_eq_mul, smul_eq_mul]; ring

/-- `Δ((1+T)^j) = j·(1+T)^j`. -/
private theorem del_one_add_X_pow (j : ℕ) :
    PadicMeasure.del p ((1 + PowerSeries.X) ^ j : PowerSeries ℤ_[p])
      = (j : PowerSeries ℤ_[p]) * (1 + PowerSeries.X) ^ j := by
  have hDoneX : derivativeFun (1 + PowerSeries.X : PowerSeries ℤ_[p]) = 1 := by
    rw [derivativeFun_add, derivativeFun_one, zero_add]; exact derivative_X
  rw [PadicMeasure.del]
  induction j with
  | zero => simp [derivativeFun_one]
  | succ a ih =>
    rw [pow_succ, derivativeFun_mul, hDoneX, smul_eq_mul, smul_eq_mul, mul_one]
    have hpow : (1 + PowerSeries.X) * ((1 + PowerSeries.X) ^ a
        + (1 + PowerSeries.X) * derivativeFun ((1 + PowerSeries.X : PowerSeries ℤ_[p]) ^ a))
        = (1 + PowerSeries.X) ^ (a + 1) + (1 + PowerSeries.X)
          * ((1 + PowerSeries.X) * derivativeFun ((1 + PowerSeries.X) ^ a)) := by
      rw [pow_succ]; ring
    rw [hpow, mul_left_comm (1 + PowerSeries.X) (1 + PowerSeries.X) (derivativeFun _), ih]
    push_cast; ring

/-- `Δ(φg) = p·φ(Δg)` in the additive `Δ = del` form (the `del`-shaped `del_phiHom`). -/
private theorem del_phiSeries (g : PowerSeries ℤ_[p]) :
    PadicMeasure.del p (phiSeries p g)
      = (p : PowerSeries ℤ_[p]) * phiSeries p (PadicMeasure.del p g) := by
  rw [PadicMeasure.del, PadicMeasure.del, one_add_mul_derivative_phiSeries, smul_eq_C_mul,
    map_natCast]

/-- `Δ` commutes with finite sums. -/
private theorem del_sum {ι : Type*} (s : Finset ι) (g : ι → PowerSeries ℤ_[p]) :
    PadicMeasure.del p (∑ i ∈ s, g i) = ∑ i ∈ s, PadicMeasure.del p (g i) := by
  rw [PadicMeasure.del,
    show (∑ i ∈ s, g i).derivativeFun = ∑ i ∈ s, (g i).derivativeFun from
      map_sum (PowerSeries.derivative ℤ_[p]) g s, Finset.mul_sum]
  rfl

/-- `φ(C a) = C a` over `ℤ_[p]` (φ fixes constants). -/
private theorem phiSeries_C_padicInt (a : ℤ_[p]) :
    phiSeries p (PowerSeries.C a) = PowerSeries.C a := by
  rw [phiSeries]; exact PowerSeries.subst_C a

private theorem phiSeries_add' (a b : PowerSeries ℤ_[p]) :
    phiSeries p (a + b) = phiSeries p a + phiSeries p b := by
  rw [← phiHom_apply, map_add, phiHom_apply, phiHom_apply]

private theorem phiSeries_mul' (a b : PowerSeries ℤ_[p]) :
    phiSeries p (a * b) = phiSeries p a * phiSeries p b := by
  rw [← phiHom_apply, map_mul, phiHom_apply, phiHom_apply]

/-- **Identity K** — the digit-matrix derivative: `(digitMatrix(Δf))_{ij} = (i−j)·M_{ij}
+ p·Δ(M_{ij})` for `M = digitMatrix f`. Differentiate the column-digit identity
`f·(1+T)^j = ∑_i (1+T)^i φ(M_{ij})`; the LHS Leibniz-expands to `Δf·(1+T)^j + j·f(1+T)^j`,
giving digit family `(digitMatrix(Δf))_{ij} + j·M_{ij}`, while the RHS (using `del_phiSeries`)
gives `i·M_{ij} + p·Δ(M_{ij})`; digit uniqueness equates them. -/
private theorem digitMatrix_del (f : PowerSeries ℤ_[p]) (i j : Fin p) :
    (digitMatrix (PadicMeasure.del p f)) i j
      = ((i : ℤ_[p]) - (j : ℤ_[p])) • (digitMatrix f) i j
        + (p : PowerSeries ℤ_[p]) * PadicMeasure.del p ((digitMatrix f) i j) := by
  have hdiff := congrArg (PadicMeasure.del p) (digitMatrix_col_isDigitDecomp f j)
  rw [del_mul, del_one_add_X_pow, del_sum] at hdiff
  have hsummand : ∀ k : Fin p,
      PadicMeasure.del p ((1 + PowerSeries.X) ^ (k : ℕ) * phiSeries p ((digitMatrix f) k j))
        = (1 + PowerSeries.X) ^ (k : ℕ) * phiSeries p ((k : ℤ_[p]) • (digitMatrix f) k j
            + (p : PowerSeries ℤ_[p]) * PadicMeasure.del p ((digitMatrix f) k j)) := by
    intro k
    have hpphi : phiSeries p (p : PowerSeries ℤ_[p]) = (p : PowerSeries ℤ_[p]) := by
      rw [← phiHom_apply, map_natCast]
    rw [del_mul, del_one_add_X_pow, del_phiSeries, phiSeries_add', smul_eq_C_mul,
      phiSeries_mul', phiSeries_C_padicInt, phiSeries_mul', hpphi,
      show (PowerSeries.C ((k : ℕ) : ℤ_[p]) : PowerSeries ℤ_[p]) = ((k : ℕ) : PowerSeries ℤ_[p])
        from (map_natCast (PowerSeries.C : ℤ_[p] →+* PowerSeries ℤ_[p]) k)]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hsummand k)] at hdiff
  set Dlf := digitMatrix (PadicMeasure.del p f) with hDlf
  set M := digitMatrix f with hM
  have hLHS2 : f * ((j : PowerSeries ℤ_[p]) * (1 + PowerSeries.X) ^ (j : ℕ))
      = ∑ k : Fin p, (1 + PowerSeries.X) ^ (k : ℕ) * phiSeries p ((j : ℤ_[p]) • M k j) := by
    rw [show f * ((j : PowerSeries ℤ_[p]) * (1 + PowerSeries.X) ^ (j : ℕ))
        = (j : PowerSeries ℤ_[p]) * (f * (1 + PowerSeries.X) ^ (j : ℕ)) from by ring,
      digitMatrix_col_isDigitDecomp f j, hM, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_eq_C_mul, phiSeries_mul', phiSeries_C_padicInt,
      show (PowerSeries.C ((j : ℕ) : ℤ_[p]) : PowerSeries ℤ_[p]) = ((j : ℕ) : PowerSeries ℤ_[p])
        from (map_natCast (PowerSeries.C : ℤ_[p] →+* PowerSeries ℤ_[p]) j)]
    ring
  have hLHS1 : PadicMeasure.del p f * (1 + PowerSeries.X) ^ (j : ℕ)
      = ∑ k : Fin p, (1 + PowerSeries.X) ^ (k : ℕ) * phiSeries p (Dlf k j) := by
    rw [hDlf, digitMatrix_col_isDigitDecomp (PadicMeasure.del p f) j]
  rw [hLHS1, hLHS2, ← Finset.sum_add_distrib] at hdiff
  rw [show (∑ k : Fin p, ((1 + PowerSeries.X) ^ (k : ℕ) * phiSeries p (Dlf k j)
        + (1 + PowerSeries.X) ^ (k : ℕ) * phiSeries p ((j : ℤ_[p]) • M k j)))
      = ∑ k : Fin p, (1 + PowerSeries.X) ^ (k : ℕ)
          * phiSeries p (Dlf k j + (j : ℤ_[p]) • M k j) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [phiSeries_add']; ring] at hdiff
  have hfamL : IsDigitDecomp p
      (∑ k : Fin p, (1 + PowerSeries.X) ^ (k : ℕ) * phiSeries p (Dlf k j + (j : ℤ_[p]) • M k j))
      (fun k => Dlf k j + (j : ℤ_[p]) • M k j) := rfl
  have hfamR : IsDigitDecomp p
      (∑ k : Fin p, (1 + PowerSeries.X) ^ (k : ℕ) * phiSeries p (Dlf k j + (j : ℤ_[p]) • M k j))
      (fun k => (k : ℤ_[p]) • M k j + (p : PowerSeries ℤ_[p]) * PadicMeasure.del p (M k j)) := by
    rw [hdiff]; rfl
  have huniq := (existsUnique_digits_padicInt p _).unique hfamL hfamR
  have hthis := congrFun huniq i
  rw [sub_smul]
  have hrw : Dlf i j = (i : ℤ_[p]) • M i j
      + (p : PowerSeries ℤ_[p]) * PadicMeasure.del p (M i j) - (j : ℤ_[p]) • M i j := by
    rw [eq_sub_iff_add_eq]; exact hthis
  rw [hrw]; ring

/-- `Δ` of a row pulls into a row-update: `(1+T)·det(M[row i ↦ ∂ row i]) = det(M[row i ↦ Δ row i])`
(`det_updateRow_smul`, with `Δ = (1+T)·∂`). -/
private theorem del_row_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) (PowerSeries ℤ_[p]))
    (i : Fin n) :
    ((1 + PowerSeries.X) : PowerSeries ℤ_[p])
        * (M.updateRow i (fun j => PowerSeries.derivative ℤ_[p] (M i j))).det
      = (M.updateRow i (fun j => PadicMeasure.del p (M i j))).det := by
  rw [← Matrix.det_updateRow_smul]; rfl

/-- `adjugate M = det M • N` when `N` is the (two-sided) inverse of `M`
(`adjugate_mul : adj M · M = det M • 1`, then cancel `M·N = 1`). -/
private theorem adjugate_eq_det_smul_inv {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) (PowerSeries ℤ_[p])) (hNM : N * M = 1) :
    Matrix.adjugate M = M.det • N := by
  have h : Matrix.adjugate M * (M * N)
      = (M.det • (1 : Matrix (Fin n) (Fin n) (PowerSeries ℤ_[p]))) * N := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul]
  rw [Matrix.smul_mul, Matrix.one_mul, mul_eq_one_comm.mp hNM, Matrix.mul_one] at h
  exact h

/-- **Jacobi → trace form**: `Δ(det M) = det M • trace((M.map Δ)·N)` when `N·M = 1`.
From `derivation_det`, pull `(1+T)` into each row (`del_row_smul`), expand each
`det(updateRow …)` by cofactors (`det_updateRow_eq_sum_adjugate`), and use
`adjugate M = det M • N`. -/
private theorem del_det_eq_smul_trace {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) (PowerSeries ℤ_[p])) (hNM : N * M = 1) :
    PadicMeasure.del p (M.det)
      = M.det • Matrix.trace ((M.map (PadicMeasure.del p)) * N) := by
  rw [PadicMeasure.del,
    show M.det.derivativeFun = (PowerSeries.derivative ℤ_[p]) M.det from rfl,
    derivation_det (PowerSeries.derivative ℤ_[p]) M, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i _ => del_row_smul p M i)]
  rw [Finset.sum_congr rfl (fun i _ => det_updateRow_eq_sum_adjugate M i
    (fun j => PadicMeasure.del p (M i j)))]
  rw [adjugate_eq_det_smul_inv p M N hNM]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- `digitMatrix(f⁻¹)·digitMatrix f = 1` for a unit `f` (digitMatrix is a ring hom). -/
private theorem digitMatrix_inverse_mul' {f : PowerSeries ℤ_[p]} (hf : IsUnit f) :
    digitMatrix (Ring.inverse f) * digitMatrix f = 1 := by
  rw [← digitMatrix_mul, Ring.inverse_mul_cancel _ hf, digitMatrix_one]

/-- `trace(D·N) = 0` for `D_{ij} = (i−j)•(M_{ij}·N_{ji})` when `M·N = N·M = 1`: the two
half-sums `∑ i·(M N)_{ii}` and `∑ k·(N M)_{kk}` are both `∑ i·1`, and cancel. -/
private theorem trace_D_N_zero {n : ℕ} (M N : Matrix (Fin n) (Fin n) (PowerSeries ℤ_[p]))
    (hMN : M * N = 1) (hNM : N * M = 1) :
    ∑ i : Fin n, ∑ k : Fin n,
      ((i : ℤ_[p]) - (k : ℤ_[p])) • (M i k * N k i) = 0 := by
  have hexp : ∀ i k : Fin n, ((i : ℤ_[p]) - (k : ℤ_[p])) • (M i k * N k i)
      = (i : ℤ_[p]) • (M i k * N k i) - (k : ℤ_[p]) • (M i k * N k i) :=
    fun i k => sub_smul _ _ _
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => hexp i k))]
  simp only [Finset.sum_sub_distrib]
  have hA : (∑ i : Fin n, ∑ k : Fin n, (i : ℤ_[p]) • (M i k * N k i))
      = ∑ i : Fin n, (i : ℤ_[p]) • (1 : PowerSeries ℤ_[p]) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.smul_sum]; congr 1
    have hii := congrFun (congrFun hMN i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at hii; exact hii
  have hB : (∑ i : Fin n, ∑ k : Fin n, (k : ℤ_[p]) • (M i k * N k i))
      = ∑ k : Fin n, (k : ℤ_[p]) • (1 : PowerSeries ℤ_[p]) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.smul_sum]; congr 1
    have hkk := congrFun (congrFun hNM k) k
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at hkk
    rw [← hkk]; exact Finset.sum_congr rfl (fun i _ => by rw [mul_comm])
  rw [hA, hB, sub_self]

/-- `(p : ℤ_p⟦T⟧)` is a regular element: it cancels on the left (it is `C(p)`, `p ≠ 0`). -/
private theorem mul_p_cancel {a b : PowerSeries ℤ_[p]}
    (h : (p : PowerSeries ℤ_[p]) * a = (p : PowerSeries ℤ_[p]) * b) : a = b := by
  have hp0 : (p : PowerSeries ℤ_[p]) ≠ 0 := by
    rw [show (p : PowerSeries ℤ_[p]) = PowerSeries.C (p : ℤ_[p]) from by rw [map_natCast]]
    intro hc
    exact (by exact_mod_cast hp.out.ne_zero : (p : ℤ_[p]) ≠ 0)
      (PowerSeries.C_injective (by rw [hc, map_zero]))
  exact mul_left_cancel₀ hp0 h

/-- **RJW lem:log der 1 (TeX 3292–3306)**: `Δ(𝒲) ⊆ ℤ_p⟦T⟧^{ψ=id}`, where
`𝒲 = (ℤ_p⟦T⟧^×)^{𝒩=id}`.

RJW's proof differentiates the `μ_p`-product `φ(f) = ∏_η f((1+T)η−1)` (replan R10.4: *not*
a formal power-series identity) and deduces `ψ(Δf) = Δf` by `φ`-injectivity. We give the
formal substitute via the **determinant/Jacobi route**. Write `M = digitMatrix f`,
`N = digitMatrix(f⁻¹) = M⁻¹`; the hypothesis `𝒩f = f` reads `f = det M`. Then
`digitMatrix(dlog f) = digitMatrix(Δf)·N`, and by identity K (`digitMatrix_del`),
`digitMatrix(Δf) = D + p·ΔM` with `D_{ij} = (i−j)•M_{ij}` and `ΔM` the entrywise `Δ`. Hence
`trace(digitMatrix(dlog f)) = trace(D·N) + p·trace(ΔM·N)`. The first trace vanishes
(`trace_D_N_zero`, from `MN = NM = 1`), and `Δf = f·trace(ΔM·N)` (Jacobi, `del_det_eq_smul_trace`
with `adjugate M = f•N`) gives `trace(ΔM·N) = f⁻¹·Δf = dlog f`. So
`p·ψ(dlog f) = trace(digitMatrix(dlog f)) = p·dlog f` (`trace_digitMatrix`), and cancelling `p`
(`mul_p_cancel`) yields `ψ(dlog f) = dlog f`. The diagonal `(digitMatrix(Δf))_{ii} = p·Δ(M_{ii})`
of identity K is exactly the formal shadow of RJW's chain-rule step
`Δ(f((1+T)η−1)) = (Δf)((1+T)η−1)`. -/
theorem dlog_mem_psiIdSeries {f : PowerSeries ℤ_[p]} (hf : IsUnit f) (hN : normOp f = f) :
    dlog p f ∈ psiIdSeries p := by
  change psiSeries p (dlog p f) = dlog p f
  set M := digitMatrix f with hM
  set N := digitMatrix (Ring.inverse f) with hN'
  have hNM : N * M = 1 := digitMatrix_inverse_mul' p hf
  have hMN : M * N = 1 := by
    rw [hM, hN', ← digitMatrix_mul, Ring.mul_inverse_cancel _ hf, digitMatrix_one]
  have hfdet : f = M.det := by rw [hM, ← normOp_eq_det, hN]
  have hdlog : dlog p f = PadicMeasure.del p f * Ring.inverse f := by rw [dlog, PadicMeasure.del]
  have hdm : digitMatrix (dlog p f) = digitMatrix (PadicMeasure.del p f) * N := by
    rw [hdlog, digitMatrix_mul, hN']
  have htr := trace_digitMatrix (dlog p f)
  rw [hdm] at htr
  have hKtrace : Matrix.trace (digitMatrix (PadicMeasure.del p f) * N)
      = (∑ i : Fin p, ∑ k : Fin p, ((i : ℤ_[p]) - (k : ℤ_[p])) • (M i k * N k i))
        + (p : PowerSeries ℤ_[p]) * Matrix.trace ((M.map (PadicMeasure.del p)) * N) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by
      rw [show digitMatrix (PadicMeasure.del p f) i k
          = digitMatrix (PadicMeasure.del p f) i k from rfl,
        digitMatrix_del p f i k, ← hM]))]
    rw [show (∑ i : Fin p, ∑ k : Fin p,
          (((i : ℤ_[p]) - (k : ℤ_[p])) • M i k
            + (p : PowerSeries ℤ_[p]) * PadicMeasure.del p (M i k)) * N k i)
        = (∑ i : Fin p, ∑ k : Fin p, ((i : ℤ_[p]) - (k : ℤ_[p])) • (M i k * N k i))
          + (p : PowerSeries ℤ_[p])
            * ∑ i : Fin p, ∑ k : Fin p, PadicMeasure.del p (M i k) * N k i from by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [add_mul, smul_mul_assoc]; ring]
    rfl
  rw [hKtrace, trace_D_N_zero p M N hMN hNM, zero_add] at htr
  have hdelf : PadicMeasure.del p f
      = f * Matrix.trace ((M.map (PadicMeasure.del p)) * N) := by
    rw [hfdet, del_det_eq_smul_trace p M N hNM, smul_eq_mul, ← hfdet]
  have htrΔ : Matrix.trace ((M.map (PadicMeasure.del p)) * N)
      = Ring.inverse f * PadicMeasure.del p f := by
    rw [hdelf, ← mul_assoc, Ring.inverse_mul_cancel _ hf, one_mul]
  rw [htrΔ, show Ring.inverse f * PadicMeasure.del p f = dlog p f from by rw [hdlog]; ring] at htr
  exact (mul_p_cancel p htr).symm

/-! ### Mod-`p^k` continuity of `𝒩` and limits (for `lem:A mod p`)

The substrate `NormOperator.lean` supplies the iterate congruences `normOp_iterate_modEq`
(part (iv), `𝒩^{k₂}f ≡ 𝒩^{k₁}f mod p^{k₁+1}`) and `normOp_iterate_modEq_self` (part (ii),
`𝒩^n f ≡ f mod p`). Here we add the three further facts the convergence argument needs:
`𝒩` respects `ModEqPow` (so it passes through the limit), `ModEqPow p k · c` is a closed
condition (so limits of `ModEqPow`-congruences stay congruent), and a Hausdorff fact
(`∀ k, ModEqPow p k a b → a = b`). -/

/-- `ModEqPow p k f g` iff `f, g` agree after reduction mod `p^k` (the `C`-factor form
phrased via the quotient `ℤ_[p] ⧸ (p^k)`). -/
theorem modEqPow_iff_map_quot {k : ℕ} {f g : PowerSeries ℤ_[p]} :
    ModEqPow p k f g ↔
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p]) ^ k})) f
        = PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p]) ^ k})) g := by
  rw [ModEqPow, PowerSeries.ext_iff]
  refine forall_congr' (fun m => ?_)
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, ← sub_eq_zero, ← map_sub,
    ← RingHom.mem_ker, Ideal.mk_ker, Ideal.mem_span_singleton, map_sub]

/-- `digitMatrix` respects `ModEqPow` entrywise: `a ≡ b mod p^k` gives
`(digitMatrix a)_{ij} ≡ (digitMatrix b)_{ij} mod p^k` (digitMatrix is a ring hom, and
`digitMatrix (C(p^k)·q) = C(p^k) • digitMatrix q`). -/
theorem digitMatrix_entry_modEq {k : ℕ} {a b : PowerSeries ℤ_[p]} (h : ModEqPow p k a b)
    (i j : Fin p) : ModEqPow p k ((digitMatrix a) i j) ((digitMatrix b) i j) := by
  obtain ⟨q, hq⟩ := modEqPow_iff_exists_C_mul.1 h
  have haeq : a = b + PowerSeries.C ((p : ℤ_[p]) ^ k) * q := by rw [← hq]; ring
  have hmat : digitMatrix a
      = digitMatrix b + PowerSeries.C ((p : ℤ_[p]) ^ k) • digitMatrix q := by
    rw [haeq, digitMatrix_add, digitMatrix_mul, digitMatrix_C, smul_mul_assoc, one_mul]
  refine modEqPow_iff_exists_C_mul.2 ⟨(digitMatrix q) i j, ?_⟩
  have := congrFun (congrFun (congrArg
    (fun M => (M : Matrix (Fin p) (Fin p) (PowerSeries ℤ_[p]))) hmat) i) j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this
  rw [this]; ring

/-- **`𝒩` respects `ModEqPow`** (the continuity that drives `lem:A mod p`): `a ≡ b mod p^k`
gives `𝒩 a ≡ 𝒩 b mod p^k`. Via `normOp_eq_det` and `RingHom.map_det`: the determinant of
matrices congruent mod `p^k` entrywise is congruent mod `p^k`. -/
theorem normOp_modEq_of_modEq {k : ℕ} {a b : PowerSeries ℤ_[p]} (h : ModEqPow p k a b) :
    ModEqPow p k (normOp a) (normOp b) := by
  set ρ := (Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p]) ^ k})) with hρ
  rw [modEqPow_iff_map_quot]
  have hnorm : ∀ f, PowerSeries.map ρ (normOp f) = Matrix.det
      ((PowerSeries.map ρ).mapMatrix (digitMatrix f)) := fun f => by
    rw [normOp_eq_det, ← RingHom.map_det]
  rw [hnorm, hnorm]
  congr 1
  refine Matrix.ext (fun i j => ?_)
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply]
  exact (modEqPow_iff_map_quot (p := p)).1 (digitMatrix_entry_modEq p h i j)

/-- The set `{x : ℤ_[p] | p^k ∣ x}` is closed (it is the closed norm ball `‖·‖ ≤ p^{-k}`). -/
theorem isClosed_dvd_pow (k : ℕ) : IsClosed {x : ℤ_[p] | (p : ℤ_[p]) ^ k ∣ x} := by
  have hset : {x : ℤ_[p] | (p : ℤ_[p]) ^ k ∣ x}
      = (fun x => ‖x‖) ⁻¹' (Set.Iic ((p : ℝ) ^ (-(k : ℤ)))) := by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic,
      ← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  rw [hset]
  exact isClosed_Iic.preimage continuous_norm

open scoped PowerSeries.WithPiTopology in
/-- `ModEqPow p k · c` passes through coefficientwise limits: if `gⱼ → g` and eventually
`gⱼ ≡ c mod p^k`, then `g ≡ c mod p^k`. (Each coefficient lands in the closed set
`isClosed_dvd_pow`.) -/
theorem modEqPow_of_tendsto {k : ℕ} {gj : ℕ → PowerSeries ℤ_[p]} {g c : PowerSeries ℤ_[p]}
    (hconv : Filter.Tendsto gj Filter.atTop (nhds g))
    (hmod : ∀ᶠ j in Filter.atTop, ModEqPow p k (gj j) c) :
    ModEqPow p k g c := by
  intro m
  have hcoeffconv : Filter.Tendsto (fun j => PowerSeries.coeff m (gj j - c))
      Filter.atTop (nhds (PowerSeries.coeff m (g - c))) := by
    have h1 := tendsto_coeff hconv m
    have h2 : Filter.Tendsto (fun j => PowerSeries.coeff m (gj j) - PowerSeries.coeff m c)
        Filter.atTop (nhds (PowerSeries.coeff m g - PowerSeries.coeff m c)) :=
      h1.sub tendsto_const_nhds
    simpa only [map_sub] using h2
  refine (isClosed_dvd_pow p k).mem_of_tendsto hcoeffconv ?_
  filter_upwards [hmod] with j hj using hj m

/-- `ℤ_[p]⟦T⟧` is Hausdorff for the `p`-filtration: agreement mod `p^k` for *all* `k`
forces equality (`⋂_k p^k ℤ_[p] = 0`). -/
theorem eq_of_forall_modEqPow {a b : PowerSeries ℤ_[p]} (h : ∀ k, ModEqPow p k a b) :
    a = b := by
  ext m
  rw [← sub_eq_zero, ← map_sub, ← norm_le_zero_iff]
  have hbound : ∀ k : ℕ, ‖PowerSeries.coeff m (a - b)‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := fun k => by
    have := h k m
    rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow] at this
    rwa [map_sub] at this
  have htend : Filter.Tendsto (fun k : ℕ => (p : ℝ) ^ (-(k : ℤ))) Filter.atTop (nhds 0) := by
    simp only [zpow_neg, zpow_natCast]
    exact tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hp.out.one_lt))
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds htend (fun k => hbound k)

open scoped PowerSeries.WithPiTopology in
/-- **RJW lem:A mod p (TeX 3337–3343)**: `𝒲 mod p = 𝔽_p⟦T⟧^×` — every unit power
series over `𝔽_p` lifts to a `𝒩`-fixed unit (via `𝒩^k`-convergence, the mod-`p^k`
continuity of `normOp`). Stated as the lift existence. -/
theorem exists_normOp_fixed_lift (f : PowerSeries ℤ_[p]) (hf : IsUnit f) :
    ∃ g : PowerSeries ℤ_[p], IsUnit g ∧ normOp g = g ∧
      PadicLFunctions.Coleman.ModEqPow p 1 g f := by
  -- the sequence `𝒩^[n] f` has a convergent subsequence `𝒩^[φ j] f → g` (compactness)
  obtain ⟨g, φ, hφmono, hconv⟩ := exists_subseq_tendsto (fun n => normOp^[n] f)
  have hφge : ∀ N : ℕ, ∀ᶠ j in Filter.atTop, N ≤ φ j := fun N => by
    filter_upwards [Filter.eventually_ge_atTop N] with j hj using le_trans hj (hφmono.id_le j)
  refine ⟨g, ?_, ?_, ?_⟩
  · -- `g` is a unit: limit of the units `𝒩^[φ j] f`
    refine (isClosed_isUnit (p := p)).mem_of_tendsto hconv ?_
    filter_upwards with j using normOp_iterate_isUnit hf (φ j)
  · -- `𝒩 g = g`: show `𝒩 g ≡ g mod p^{k+1}` for every `k`, then Hausdorff
    refine eq_of_forall_modEqPow p (fun k => ?_)
    have hg_k : ModEqPow p (k + 1) g (normOp^[k] f) := by
      refine modEqPow_of_tendsto p hconv ?_
      filter_upwards [hφge k] with j hj using normOp_iterate_modEq hj hf
    have hNg : ModEqPow p (k + 1) (normOp g) (normOp^[k + 1] f) := by
      have := normOp_modEq_of_modEq p hg_k
      rwa [show normOp (normOp^[k] f) = normOp^[k + 1] f from
        (Function.iterate_succ_apply' normOp k f).symm] at this
    have hstep : ModEqPow p (k + 1) (normOp^[k + 1] f) (normOp^[k] f) :=
      normOp_iterate_modEq (Nat.le_succ k) hf
    exact (hNg.trans (hstep.trans hg_k.symm)).of_le (Nat.le_succ k)
  · -- `g ≡ f mod p`: each `𝒩^[φ j] f ≡ f mod p` (part (ii)), pass to the limit
    refine modEqPow_of_tendsto p hconv ?_
    filter_upwards with j using normOp_iterate_modEq_self f (φ j)

/-! ### `lem:B mod p 2`: the topology-free coefficient construction over `𝔽_p`

The helpers below realise the `𝔽_p⟦T⟧ = Δ(𝔽_p⟦T⟧^×) + (T+1)/T·C` decomposition by a direct
coefficient recursion (no infinite product). See the theorem's docstring for the strategy. -/

/-- Over `𝔽_p`, a series supported only on multiples of `p` is a `p`-th power, hence in
`range φ` (`φ(d) = d^p`, `phiSeries_eq_pow_zmod`; the `p`-th root is the de-`expand`
`d = ∑ c_{pk} T^k`). -/
private theorem mem_range_phiSeries_of_dvd {c : PowerSeries (ZMod p)}
    (hc : ∀ n, ¬ p ∣ n → PowerSeries.coeff n c = 0) :
    c ∈ Set.range (phiSeries p (R := ZMod p)) := by
  haveI : CharP (PowerSeries (ZMod p)) p := charP_of_injective_algebraMap' (ZMod p) p
  refine ⟨PowerSeries.mk (fun k => PowerSeries.coeff (p * k) c), ?_⟩
  have hexp : phiSeries p (PowerSeries.mk (fun k => PowerSeries.coeff (p * k) c))
      = PowerSeries.expand p hp.out.pos.ne' (PowerSeries.mk (fun k => PowerSeries.coeff (p * k) c))
      := by
    have hsub : ((1 + PowerSeries.X) ^ p - 1 : PowerSeries (ZMod p)) = PowerSeries.X ^ p := by
      rw [add_pow_char, one_pow, add_sub_cancel_left]
    rw [phiSeries, hsub, PowerSeries.expand_apply]
  rw [hexp]
  ext m
  rcases em (p ∣ m) with ⟨k, rfl⟩ | hndvd
  · rw [PowerSeries.coeff_expand_mul, PowerSeries.coeff_mk]
  · rw [PowerSeries.coeff_expand p hp.out.pos.ne', if_neg hndvd, hc m hndvd]

/-- The joint coefficient recursion for `(a, w)` solving `T·a′ = a·w` over `𝔽_p` against a
target `H`: `(a_0, w_0) = (1, 0)`; for `n ≥ 1`, with `S = ∑_{j=1}^{n−1} a_{n−j}·w_j`, set
`(a_n, w_n) = (0, −S)` if `p ∣ n` and `(n⁻¹(H_n + S), H_n)` otherwise. -/
private def AWfp (H : PowerSeries (ZMod p)) : ℕ → ZMod p × ZMod p
  | n =>
    if n = 0 then (1, 0)
    else
      let S : ZMod p := ∑ k ∈ (Finset.Ico 1 n).attach,
        (AWfp H k.1).1 * (AWfp H (n - k.1)).2
      if p ∣ n then (0, -S)
      else ((n : ZMod p)⁻¹ * (PowerSeries.coeff n H + S), PowerSeries.coeff n H)
  decreasing_by
    · exact (Finset.mem_Ico.1 k.2).2
    · have := (Finset.mem_Ico.1 k.2).1; omega

/-- The `a`-coefficients (`= (AWfp H n).1`). -/
private def AfpCoe (H : PowerSeries (ZMod p)) (n : ℕ) : ZMod p := (AWfp p H n).1
/-- The `w`-coefficients (`= (AWfp H n).2`). -/
private def WfpCoe (H : PowerSeries (ZMod p)) (n : ℕ) : ZMod p := (AWfp p H n).2
/-- The partial sum `S_n = ∑_{j=1}^{n−1} a_{n−j}·w_j` driving the recursion. -/
private def SfpSum (H : PowerSeries (ZMod p)) (n : ℕ) : ZMod p :=
  ∑ k ∈ Finset.Ico 1 n, AfpCoe p H k * WfpCoe p H (n - k)

private theorem Sfp_attach_eq (H : PowerSeries (ZMod p)) (n : ℕ) :
    (∑ k ∈ (Finset.Ico 1 n).attach, (AWfp p H k.1).1 * (AWfp p H (n - k.1)).2)
      = SfpSum p H n := by
  rw [SfpSum, ← Finset.sum_attach (Finset.Ico 1 n)
    (fun k => AfpCoe p H k * WfpCoe p H (n - k))]; rfl

private theorem AWfp_dvd (H : PowerSeries (ZMod p)) {n : ℕ} (hn : n ≠ 0) (hd : p ∣ n) :
    AWfp p H n = (0, -SfpSum p H n) := by
  conv_lhs => rw [AWfp]
  rw [if_neg hn]; simp only [Sfp_attach_eq]; rw [if_pos hd]

private theorem AWfp_ndvd (H : PowerSeries (ZMod p)) {n : ℕ} (hn : n ≠ 0) (hd : ¬ p ∣ n) :
    AWfp p H n
      = ((n : ZMod p)⁻¹ * (PowerSeries.coeff n H + SfpSum p H n), PowerSeries.coeff n H) := by
  conv_lhs => rw [AWfp]
  rw [if_neg hn]; simp only [Sfp_attach_eq]; rw [if_neg hd]

private theorem AfpCoe_zero (H : PowerSeries (ZMod p)) : AfpCoe p H 0 = 1 := by
  rw [AfpCoe, AWfp, if_pos rfl]
private theorem WfpCoe_zero (H : PowerSeries (ZMod p)) : WfpCoe p H 0 = 0 := by
  rw [WfpCoe, AWfp, if_pos rfl]
private theorem WfpCoe_ndvd (H : PowerSeries (ZMod p)) {n : ℕ} (hn : n ≠ 0) (hd : ¬ p ∣ n) :
    WfpCoe p H n = PowerSeries.coeff n H := by rw [WfpCoe, AWfp_ndvd p H hn hd]
private theorem AfpCoe_ndvd (H : PowerSeries (ZMod p)) {n : ℕ} (hn : n ≠ 0) (hd : ¬ p ∣ n) :
    AfpCoe p H n = (n : ZMod p)⁻¹ * (PowerSeries.coeff n H + SfpSum p H n) := by
  rw [AfpCoe, AWfp_ndvd p H hn hd]
private theorem WfpCoe_dvd (H : PowerSeries (ZMod p)) {n : ℕ} (hn : n ≠ 0) (hd : p ∣ n) :
    WfpCoe p H n = - SfpSum p H n := by rw [WfpCoe, AWfp_dvd p H hn hd]
private theorem AfpCoe_dvd (H : PowerSeries (ZMod p)) {n : ℕ} (hn : n ≠ 0) (hd : p ∣ n) :
    AfpCoe p H n = 0 := by rw [AfpCoe, AWfp_dvd p H hn hd]

/-- `[Tⁿ](a·w) = w_n + S_n` for `n ≥ 1` (where `a = mk a_•`, `w = mk w_•`, `a_0 = 1`,
`w_0 = 0`): the convolution splits off its `j = 0` end (`a_n·w_0 = 0`) and `j = n` end
(`a_0·w_n = w_n`), the middle being `S_n`. -/
private theorem coeff_afp_mul_wfp (H : PowerSeries (ZMod p)) {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff n (PowerSeries.mk (AfpCoe p H) * PowerSeries.mk (WfpCoe p H))
      = WfpCoe p H n + SfpSum p H n := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]
  rw [Finset.sum_range_succ, Nat.sub_self, WfpCoe_zero, mul_zero, add_zero]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hn1,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.sub_zero, Finset.sum_range_one, Nat.add_zero, AfpCoe_zero, one_mul]
  rw [SfpSum]

/-- The defining identity `T·a′ = a·w` of the recursion (`a = mk a_•`, `w = mk w_•`):
coefficientwise, `n·a_n = w_n + S_n`, which the recursion makes hold in both the `p∤n`
branch (`n` invertible) and the `p∣n` branch (both sides `0`). -/
private theorem X_deriv_eq_aw (H : PowerSeries (ZMod p)) :
    PowerSeries.X * PowerSeries.derivativeFun (PowerSeries.mk (AfpCoe p H))
      = PowerSeries.mk (AfpCoe p H) * PowerSeries.mk (WfpCoe p H) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton, PowerSeries.coeff_mk, PowerSeries.coeff_mk, WfpCoe_zero, mul_zero]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivativeFun, PowerSeries.coeff_mk,
      coeff_afp_mul_wfp p H hn]
    by_cases hd : p ∣ (m + 1)
    · rw [AfpCoe_dvd p H hn hd, WfpCoe_dvd p H hn hd, zero_mul, neg_add_cancel]
    · rw [AfpCoe_ndvd p H hn hd, WfpCoe_ndvd p H hn hd]
      have hne : ((m + 1 : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]; exact hd
      rw [show ((m : ZMod p) + 1) = ((m + 1 : ℕ) : ZMod p) by push_cast; ring,
        mul_comm, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- **RJW lem:B mod p 2 (TeX 3359–3373) — "the most delicate and technical part"**: the
`𝔽_p⟦T⟧` decomposition `𝔽_p⟦T⟧ = Δ(𝔽_p⟦T⟧^×) + (T+1)/T·C` with
`C = {∑_{n≥1} a_n T^{pn}}`.

Statement note (T1203b, faithful form — statement-fix authorised). The skeleton's
existential was a placeholder (`∃ a c, IsUnit a ∧ c ∈ range φ`, vacuously true). The
faithful claim, with `Δ a = (1+T)·a′·a⁻¹` the `𝔽_p` log-derivative and the `(T+1)/T·c`
factor cleared of its `1/T` pole (`T·b = (T+1)·c`, i.e. `X·b = (1+X)·c`), is: every
`g : 𝔽_p⟦T⟧` is `Δ a + b` for a unit `a` and a `b` with `X·b = (1+X)·c`, `c ∈ φ(𝔽_p⟦T⟧)`
(so `c = ∑ a_n T^{pn} ∈ C`, using `φ(T^m) = T^{pm}` over `𝔽_p`, `phiSeries_eq_pow_zmod`).
This is the precise form `lem:B mod p` consumes: it kills the `b`-part using `ψ b = b`.

Proof note (T1203b, CLOSED). RJW's route (TeX 3366–3373) builds `α_i` so that the unit
`a = ∏(1−α_n T^n)` (a T-adic infinite product, needing `multipliable` + `Δ`-continuity)
has `Δ a = (T+1)/T·h`. We take a topology-free coefficient recursion (the same pattern as
`solCoeff`), building `a` and `w := T·a′·a⁻¹` *directly* by their coefficients rather than
as a product. Write `u = 1+T` (a unit over `𝔽_p`), `H := T·g·u⁻¹`. The map `a ↦ T·a′·a⁻¹`
sends a unit `a` with `a(0)=1` to a series `w` with `w(0)=0` whose `n`-th coefficient
satisfies `n·a_n = w_n + ∑_{j=1}^{n−1} a_{n−j}·w_j` (clear `T·a′ = a·w`). For `(n,p)=1`
the leading `n·a_n` is invertible so `a_n` is determined by a chosen `w_n`; for `p∣n` the
LHS vanishes (`n=0` in `𝔽_p`), forcing `w_n` and freeing `a_n`. So we jointly recurse
(`AWfp`): set `w_n := H_n`, `a_n := n⁻¹(H_n + S_n)` when `(n,p)=1`; `a_n := 0`,
`w_n := −S_n` when `p∣n` (`S_n` the partial sum). Then `T·a′ = a·w` (`X_deriv_eq_aw`),
`a` is a unit (`a(0)=1`), `w = T·a′·a⁻¹`, and `w` agrees with `H` off multiples of `p`, so
`c := H − w` is supported on `pℕ`, hence a `p`-th power `= φ(d)` (over `𝔽_p`,
`range φ = {p-th powers}`; `mem_range_phiSeries_of_dvd`). Finally `b := g − Δa` gives
`X·b = u·c` by `X·Δa = u·w` and `u·H = T·g`, and `g = Δa + b` trivially. No infinite
product, no `Δ`-continuity. -/
theorem fp_series_eq_dlog_add_frobC (g : PowerSeries (ZMod p)) :
    ∃ (a : PowerSeries (ZMod p)) (b : PowerSeries (ZMod p)) (c : PowerSeries (ZMod p)),
      IsUnit a ∧ c ∈ Set.range (phiSeries p (R := ZMod p)) ∧
        PowerSeries.X * b = (1 + PowerSeries.X) * c ∧
        g = (1 + PowerSeries.X) * PowerSeries.derivativeFun a * Ring.inverse a + b := by
  -- `u = 1+T` (a unit), `H = T·g·u⁻¹`, and the recursion's `a = mk a_•`, `w = mk w_•`
  have hu : IsUnit (1 + PowerSeries.X : PowerSeries (ZMod p)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  set H : PowerSeries (ZMod p) :=
    PowerSeries.X * g * Ring.inverse (1 + PowerSeries.X) with hHdef
  set a : PowerSeries (ZMod p) := PowerSeries.mk (AfpCoe p H) with hadef
  set w : PowerSeries (ZMod p) := PowerSeries.mk (WfpCoe p H) with hwdef
  -- `a` is a unit (`a(0) = 1`)
  have ha : IsUnit a := by
    rw [hadef, PowerSeries.isUnit_iff_constantCoeff,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, AfpCoe_zero]
    exact isUnit_one
  have haa : a * Ring.inverse a = 1 := Ring.mul_inverse_cancel _ ha
  have huu : (1 + PowerSeries.X : PowerSeries (ZMod p)) * Ring.inverse (1 + PowerSeries.X) = 1 :=
    Ring.mul_inverse_cancel _ hu
  -- `w = T·a′·a⁻¹` from the recursion's defining identity `T·a′ = a·w`
  have hkey : PowerSeries.X * PowerSeries.derivativeFun a = a * w := X_deriv_eq_aw p H
  have hw : w = PowerSeries.X * PowerSeries.derivativeFun a * Ring.inverse a := by
    have h2 := congrArg (· * Ring.inverse a) hkey
    rw [mul_assoc a w (Ring.inverse a), mul_comm w (Ring.inverse a), ← mul_assoc,
      mul_comm a (Ring.inverse a), Ring.inverse_mul_cancel _ ha, one_mul] at h2
    rw [← h2]
  refine ⟨a, g - (1 + PowerSeries.X) * PowerSeries.derivativeFun a * Ring.inverse a, H - w,
    ha, ?_, ?_, by ring⟩
  · -- `c = H − w ∈ range φ`: supported on multiples of `p` (agrees with `H` off `pℕ`)
    refine mem_range_phiSeries_of_dvd p (fun n hd => ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · rw [map_sub, hHdef, mul_assoc, PowerSeries.coeff_zero_X_mul, hwdef,
        PowerSeries.coeff_mk, WfpCoe_zero, sub_zero]
    · rw [map_sub, hwdef, PowerSeries.coeff_mk, WfpCoe_ndvd p H hn hd, sub_self]
  · -- `X·b = u·c`: `X·Δa = u·w` and `u·H = T·g`
    rw [hw]
    have hcancel : (1 + PowerSeries.X : PowerSeries (ZMod p)) * H = PowerSeries.X * g := by
      rw [hHdef, show (1 + PowerSeries.X : PowerSeries (ZMod p))
          * (PowerSeries.X * g * Ring.inverse (1 + PowerSeries.X))
        = PowerSeries.X * g * ((1 + PowerSeries.X) * Ring.inverse (1 + PowerSeries.X)) by ring,
        huu, mul_one]
    rw [mul_sub, mul_sub, hcancel]; ring

/-! ### `Δ = dlog` turns products into sums (for `lem:log der red mod p`)

The successive-approximation argument forms `h_n = ∏_k g_k^{±p^{k-1}}`; `Δ` of such a
product telescopes via these `dlog`-homomorphism facts. -/

/-- `Δ(gh) = Δg + Δh` for units `g, h` (the log-derivative is additive on the unit group:
`(gh)' = g'h + gh'`, divide by `gh`). -/
theorem dlog_mul {g h : PowerSeries ℤ_[p]} (hg : IsUnit g) (hh : IsUnit h) :
    dlog p (g * h) = dlog p g + dlog p h := by
  have hg' : g * Ring.inverse g = 1 := Ring.mul_inverse_cancel _ hg
  have hh' : h * Ring.inverse h = 1 := Ring.mul_inverse_cancel _ hh
  rw [dlog, dlog, dlog, derivativeFun_mul, smul_eq_mul, smul_eq_mul, Ring.mul_inverse_rev]
  rw [show (1 + PowerSeries.X) * (g * h.derivativeFun + h * g.derivativeFun)
        * (Ring.inverse h * Ring.inverse g)
      = (1 + PowerSeries.X) * g.derivativeFun * Ring.inverse g * (h * Ring.inverse h)
        + (1 + PowerSeries.X) * h.derivativeFun * Ring.inverse h * (g * Ring.inverse g) from by
        ring,
    hg', hh', mul_one, mul_one, add_comm]

/-- `Δ 1 = 0`. -/
theorem dlog_one : dlog p (1 : PowerSeries ℤ_[p]) = 0 := by
  rw [dlog, derivativeFun_one, mul_zero, zero_mul]

/-- `Δ(g⁻¹) = −Δg` for a unit `g`. -/
theorem dlog_inverse {g : PowerSeries ℤ_[p]} (hg : IsUnit g) :
    dlog p (Ring.inverse g) = - dlog p g := by
  have h := dlog_mul p hg (isUnit_ringInverse.mpr hg)
  rw [Ring.mul_inverse_cancel _ hg, dlog_one] at h
  linear_combination -h

/-- `Δ(gⁿ) = n·Δg` for a unit `g`. -/
theorem dlog_pow {g : PowerSeries ℤ_[p]} (hg : IsUnit g) (n : ℕ) :
    dlog p (g ^ n) = (n : ℤ) • dlog p g := by
  induction n with
  | zero => simp [dlog_one]
  | succ m ih => rw [pow_succ, dlog_mul p (hg.pow m) hg, ih]; push_cast; ring

/-- **RJW thm:log der (TeX 3280–3285) — the Coleman–Coates–Wiles short exact sequence.**
Surjectivity half: every `ψ`-fixed series is the logarithmic derivative of a `𝒩`-fixed
unit. (The kernel half is `rem:ker Δ`: `μ_{p−1}`.)

Roadmap and obstacle note (T1203c). RJW reduce surjectivity (`lem:log der red mod p`,
TeX 3315–3332) to the mod-`p` identity `A = B` (`A = Δ(𝒲) mod p`, `B = (ψ=id) mod p`):
* `A ⊆ B` mod `p` is `dlog_mem_psiIdSeries` (now proven) reduced mod `p`, plus
  `lem:A mod p` (`exists_normOp_fixed_lift`).
* `B ⊆ A` mod `p` (`lem:B mod p`) needs `fp_series_eq_dlog_add_frobC` (`lem:B mod p 2`,
  below) **and** the `ψ`-action computation that the `(T+1)/T·C` component is killed —
  which (TeX 3352–3356) uses `ψ(g·φ(f)) = ψ(g)·f` and "`ψ` fixes `(T+1)/T`". The latter is
  proved in RJW (`LemmaPsiInvariant`, TeX 1521) by the **partial-fraction `μ_p`-sum
  `(φ∘ψ)(1/T) = p⁻¹ ∑_ξ 1/((1+T)ξ−1)`** — an instance of the deferred non-formal
  `Eqphipsi` (FormalPsi.lean; the substitution has non-nilpotent constant term for `ξ ≠ 1`).
* The reduction itself then builds `g_i ∈ 𝒲`, `f_i ∈ (ψ=id)` with `Δ(g_i) − f_{i−1} = p f_i`,
  sets `h_n = ∏_{k=1}^n g_k^{(−1)^{k−1} p^{k−1}}` (so `Δ h_n = f_0 + (−1)^{n−1} p^n f_n`,
  via `dlog_mul`/`dlog_pow` above), and takes a convergent subsequence in the compact
  `ℤ_p⟦T⟧^×` (§10 `SeqCompactSpace`, `exists_subseq_tendsto`) with limit `h`, `Δ h = F`,
  `𝒩 h = h` (`modEqPow_of_tendsto`/`eq_of_forall_modEqPow`). This last analytic step also
  needs **continuity of `Δ = dlog`** (`(1+T)·∂·(·)⁻¹`) in the coefficientwise topology —
  continuity of `derivativeFun` and of `Ring.inverse` on units — which is not yet in the
  §10 substrate.

The blocking inputs (`fp_series_eq_dlog_add_frobC` and the `Eqphipsi`-based `ψ`-fixedness of
`(T+1)/T`) live in / depend on modules outside this file's edit scope or on the deferred
`Eqphipsi`. The `dlog`-homomorphism layer above is the reusable formal half of the
reduction. -/
theorem dlog_surjective_onto_psiId {F : PowerSeries ℤ_[p]} (hF : F ∈ psiIdSeries p) :
    ∃ g : PowerSeries ℤ_[p], IsUnit g ∧ normOp g = g ∧ dlog p g = F := sorry

/-- A power series with vanishing formal derivative is its constant coefficient. -/
private theorem eq_C_constantCoeff_of_derivativeFun_zero (g : PowerSeries ℤ_[p])
    (h : PowerSeries.derivativeFun g = 0) :
    g = PowerSeries.C (PowerSeries.constantCoeff (R := ℤ_[p]) g) := by
  ext n
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_C]
  | succ m =>
    rw [PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero m)]
    have hcoeff := congrArg (PowerSeries.coeff m) h
    rw [PowerSeries.coeff_derivativeFun, map_zero] at hcoeff
    have hne : ((m : ℤ_[p]) + 1) ≠ 0 := by
      have : ((m + 1 : ℕ) : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
      push_cast at this; exact this
    rcases mul_eq_zero.mp hcoeff with h1 | h2
    · exact h1
    · exact absurd h2 hne

/-- `𝒩(C c) = C (c^p)`: the digit matrix of a constant is the scalar `C c • 1`, so its
determinant (`= 𝒩`) is `(C c)^p = C (c^p)`. -/
theorem normOp_C (c : ℤ_[p]) : normOp (PowerSeries.C (R := ℤ_[p]) c) = PowerSeries.C (c ^ p) := by
  rw [normOp_eq_det, digitMatrix_C, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin, ← map_pow]

/-- The kernel of `Δ = ∂log` on `𝒩`-fixed units is `μ_{p−1}` (RJW rem:ker Δ, TeX
3176–3178): a constant `𝒩`-fixed unit `f` satisfies `f^p = f`. Stated as: `dlog g = 0`
and `𝒩 g = g` ⟹ `g` is a `(p−1)`-th root of unity (constant). -/
theorem dlog_eq_zero_normOp_fixed {g : PowerSeries ℤ_[p]} (hg : IsUnit g)
    (hN : normOp g = g) (hd : dlog p g = 0) :
    ∃ c : ℤ_[p], c ^ p = c ∧ g = PowerSeries.C c := by
  have hunit1 : IsUnit (1 + PowerSeries.X : PowerSeries ℤ_[p]) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  -- `dlog g = (1+X)·g'·g⁻¹ = 0`; cancel the two units `(1+X)` and `Ring.inverse g`
  have hgz : PowerSeries.derivativeFun g = 0 := by
    have hd' : (1 + PowerSeries.X) * PowerSeries.derivativeFun g * Ring.inverse g = 0 := hd
    have hmulg : (1 + PowerSeries.X) * PowerSeries.derivativeFun g
        * (Ring.inverse g * g) = 0 := by rw [← mul_assoc, hd', zero_mul]
    rw [Ring.inverse_mul_cancel _ hg, mul_one] at hmulg
    rcases hunit1.exists_left_inv with ⟨u, hu⟩
    have := congrArg (fun x => u * x) hmulg
    simp only [mul_zero, ← mul_assoc, hu, one_mul] at this
    exact this
  set c := PowerSeries.constantCoeff (R := ℤ_[p]) g with hc
  have hgC : g = PowerSeries.C c := eq_C_constantCoeff_of_derivativeFun_zero p g hgz
  refine ⟨c, ?_, hgC⟩
  -- `𝒩 g = g` and `g = C c` give `C (c^p) = C c`, hence `c^p = c`
  have : PowerSeries.C (c ^ p) = PowerSeries.C c := by rw [← normOp_C, ← hgC, hN, hgC]
  exact PowerSeries.C_injective this

/-! ### Solving `(1 − φ)G = F` coefficientwise (for the converse of `lem:rest zp*`)

RJW's converse argument constructs `G = Σ_{n≥0} φⁿ(F)` and uses `(p,T)`-adic convergence.
We instead solve `(1 − φ)G = F` by a coefficient recursion that avoids any topology: the
`n`-th coefficient of `φ G = G.subst((1+T)^p − 1)` is `Σ_{d ≤ n} G_d · [Tⁿ]((1+T)^p−1)^d`,
with the diagonal `d = n` term `pⁿ · G_n` (the substituted series has order `1`, leading
coefficient `p`). Hence `[Tⁿ]((1−φ)G) = G_n(1 − pⁿ) − Σ_{d<n} G_d·c_{n,d}`, and since
`1 − pⁿ` is a unit for `n ≥ 1` (`isUnit_one_sub_p_pow`) we may solve for `G_n` recursively
(`solCoeff`). The `n = 0` equation forces `F(0) = 0`. Then `ψ G = G` follows for free by
applying `ψ` (using `ψ φ = id` and `ψ F = 0`). -/

/-- `[T¹]((1+T)^p) = p`: from the cleared identity `(1+T)·∂((1+T)^p) = p(1+T)^p`, taking
the constant coefficient (`[T¹]f = [T⁰](∂f)`). -/
private theorem coeff_one_one_add_X_pow :
    PowerSeries.coeff 1 ((1 + PowerSeries.X : PowerSeries ℤ_[p]) ^ p) = (p : ℤ_[p]) := by
  have hDoneX : derivativeFun (1 + PowerSeries.X : PowerSeries ℤ_[p]) = 1 := by
    rw [derivativeFun_add, derivativeFun_one, zero_add]; exact derivative_X
  have key : ∀ a : ℕ, (1 + PowerSeries.X)
      * derivativeFun ((1 + PowerSeries.X : PowerSeries ℤ_[p]) ^ a)
      = (a : PowerSeries ℤ_[p]) * (1 + PowerSeries.X) ^ a := by
    intro a
    induction a with
    | zero => simp [derivativeFun_one]
    | succ a ih =>
      rw [pow_succ, derivativeFun_mul, hDoneX, smul_eq_mul, smul_eq_mul, mul_one]
      have hpow : (1 + PowerSeries.X) * ((1 + PowerSeries.X) ^ a
          + (1 + PowerSeries.X) * derivativeFun ((1 + PowerSeries.X : PowerSeries ℤ_[p]) ^ a))
          = (1 + PowerSeries.X) ^ (a + 1) + (1 + PowerSeries.X)
            * ((1 + PowerSeries.X) * derivativeFun ((1 + PowerSeries.X) ^ a)) := by
        rw [pow_succ]; ring
      rw [hpow, mul_left_comm (1 + PowerSeries.X) (1 + PowerSeries.X) (derivativeFun _), ih]
      push_cast; ring
  have h0 := congrArg (PowerSeries.coeff 0) (key p)
  rw [show (1 + PowerSeries.X : PowerSeries ℤ_[p]) * derivativeFun ((1 + PowerSeries.X) ^ p)
      = derivativeFun ((1 + PowerSeries.X) ^ p)
        + PowerSeries.X * derivativeFun ((1 + PowerSeries.X) ^ p) from by ring,
    map_add, PowerSeries.coeff_zero_X_mul, add_zero, coeff_derivativeFun,
    show (p : PowerSeries ℤ_[p]) * (1 + PowerSeries.X) ^ p
      = PowerSeries.C (p : ℤ_[p]) * (1 + PowerSeries.X) ^ p from by rw [map_natCast],
    PowerSeries.coeff_C_mul] at h0
  simp only [zero_add] at h0
  rw [show PowerSeries.coeff 0 ((1 + PowerSeries.X : PowerSeries ℤ_[p]) ^ p) = 1 from by simp,
    mul_one] at h0
  simpa using h0

/-- `[Tⁿ](((1+T)^p − 1)^d) = 0` for `n < d` (the substituted series has order `1`). -/
private theorem coeff_S_pow_vanish {d n : ℕ} (hdn : n < d) :
    PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d) = 0 := by
  obtain ⟨U, hU⟩ := (PowerSeries.X_dvd_iff
    (φ := ((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]))).2 (by simp)
  rw [hU, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

/-- `[Tⁿ](((1+T)^p − 1)^n) = pⁿ` (the leading coefficient: `((1+T)^p − 1) = pT + O(T²)`). -/
private theorem coeff_S_pow_diag {d : ℕ} :
    PowerSeries.coeff d (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d)
      = (p : ℤ_[p]) ^ d := by
  obtain ⟨U, hU⟩ := (PowerSeries.X_dvd_iff
    (φ := ((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]))).2 (by simp)
  have hU0 : PowerSeries.constantCoeff (R := ℤ_[p]) U = (p : ℤ_[p]) := by
    have h1 : PowerSeries.coeff 1 ((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p])
        = (p : ℤ_[p]) := by
      rw [map_sub, coeff_one_one_add_X_pow, PowerSeries.coeff_one, if_neg one_ne_zero, sub_zero]
    rw [hU, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff] at h1
    exact h1
  have hstep : PowerSeries.coeff d (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d)
      = PowerSeries.coeff 0 (U ^ d) := by
    rw [hU, mul_pow]
    have := PowerSeries.coeff_X_pow_mul (U ^ d) d 0
    rwa [zero_add] at this
  rw [hstep, PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hU0]

/-- `[Tⁿ](φ G) = Σ_{d ≤ n} G_d · [Tⁿ](((1+T)^p − 1)^d)` (the substitution coefficient
formula, finite because `((1+T)^p − 1)^d` has order `d`). -/
private theorem coeff_phiSeries_split (G : PowerSeries ℤ_[p]) (n : ℕ) :
    PowerSeries.coeff n (phiSeries p G)
      = ∑ d ∈ Finset.range (n + 1), (PowerSeries.coeff d G) •
          PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d) := by
  rw [phiSeries, PowerSeries.coeff_subst' (hasSubst_one_add_X_pow_sub_one p)]
  refine finsum_eq_finsetSum_of_support_subset _ (fun d hd => ?_)
  simp only [Function.mem_support] at hd
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hcon
  push Not at hcon
  exact hd (by rw [coeff_S_pow_vanish p (by omega), smul_zero])

/-- `1 − pⁿ` is a unit of `ℤ_[p]` for `n ≥ 1` (it is `1 − (maximal ideal element)`). -/
private theorem isUnit_one_sub_p_pow {n : ℕ} (hn : 1 ≤ n) : IsUnit (1 - (p : ℤ_[p]) ^ n) := by
  refine IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ?_
  rw [mem_nonunits_iff, PadicInt.isUnit_iff, norm_pow]
  have hlt : ‖(p : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  exact fun hc => absurd hc (ne_of_lt (pow_lt_one₀ (norm_nonneg _) hlt (by omega)))

/-- The recursively-defined coefficients of the solution `G` to `(1 − φ)G = F`:
`G₀ = 0`, and `Gₙ = (1 − pⁿ)⁻¹·(Fₙ + Σ_{d<n} G_d·[Tⁿ](((1+T)^p−1)^d))` for `n ≥ 1`. -/
private def solCoeff (F : PowerSeries ℤ_[p]) : ℕ → ℤ_[p]
  | n => if n = 0 then 0 else
      Ring.inverse (1 - (p : ℤ_[p]) ^ n) *
        (PowerSeries.coeff n F + ∑ d ∈ (Finset.range n).attach, (solCoeff F d.1) *
          PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d.1))
  decreasing_by exact Finset.mem_range.1 d.2

private theorem solCoeff_zero (F : PowerSeries ℤ_[p]) : solCoeff p F 0 = 0 := by
  rw [solCoeff, if_pos rfl]

private theorem solCoeff_eq (F : PowerSeries ℤ_[p]) {n : ℕ} (hn : n ≠ 0) :
    solCoeff p F n = Ring.inverse (1 - (p : ℤ_[p]) ^ n) *
        (PowerSeries.coeff n F + ∑ d ∈ Finset.range n, (solCoeff p F d) *
          PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d)) := by
  rw [solCoeff, if_neg hn]; congr 2
  rw [← Finset.sum_attach (Finset.range n) (fun d => (solCoeff p F d) *
    PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d))]

/-- The constructed series `G = mk (solCoeff F)` solves `(1 − φ)G = F` when `F(0) = 0`. -/
private theorem mk_solCoeff_sub_phi (F : PowerSeries ℤ_[p])
    (h0 : PowerSeries.constantCoeff (R := ℤ_[p]) F = 0) :
    PowerSeries.mk (solCoeff p F) - phiSeries p (PowerSeries.mk (solCoeff p F)) = F := by
  set G := PowerSeries.mk (solCoeff p F) with hG
  have hcoeffG : ∀ m, PowerSeries.coeff m G = solCoeff p F m := fun m => by rw [hG, coeff_mk]
  ext n
  rw [map_sub]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    rw [hcoeffG, solCoeff_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      constantCoeff_phiSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hcoeffG,
      solCoeff_zero, sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
  · rw [hcoeffG, coeff_phiSeries_split, Finset.sum_range_succ]
    simp only [hcoeffG, smul_eq_mul]
    rw [coeff_S_pow_diag, solCoeff_eq p F (by omega)]
    set Sigma := ∑ d ∈ Finset.range n, solCoeff p F d *
      PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d) with hSig
    set u := (1 - (p : ℤ_[p]) ^ n) with hu
    have hunit : IsUnit u := isUnit_one_sub_p_pow p (by omega)
    have hexp : Ring.inverse u * (PowerSeries.coeff n F + Sigma)
        - (Sigma + Ring.inverse u * (PowerSeries.coeff n F + Sigma) * (p : ℤ_[p]) ^ n)
        = PowerSeries.coeff n F := by
      have heq : Ring.inverse u * (PowerSeries.coeff n F + Sigma) * (1 - (p : ℤ_[p]) ^ n)
          = PowerSeries.coeff n F + Sigma := by
        rw [mul_assoc, mul_comm (PowerSeries.coeff n F + Sigma) (1 - (p : ℤ_[p]) ^ n),
          ← mul_assoc, ← hu, Ring.inverse_mul_cancel _ hunit, one_mul]
      linear_combination heq
    rw [hexp]

/-- **RJW lem:rest zp* (TeX 3387–3391)**: the exactness
`0 → ℤ_p → ℤ_p⟦T⟧^{ψ=id} →[1−φ] ℤ_p⟦T⟧^{ψ=0} → ℤ_p → 0`. Surjectivity of `eval₀`
half (`1+T ↦ 1`) + kernel-`ℤ_p` half. -/
theorem one_sub_phi_psiId_mem_psiZero {F : PowerSeries ℤ_[p]} (hF : F ∈ psiIdSeries p) :
    F - phiHom p F ∈ psiZeroSeries p := by
  have hFid : psiSeries p F = F := hF
  change psiSeries p (F - phiHom p F) = 0
  rw [psiSeries_sub, phiHom_apply, psiSeries_phi_padicInt, hFid, sub_self]

/-- The converse half of `lem:rest zp*`: every `ψ = 0` series with `F(0) = 0` is `(1−φ)G`
for some `ψ`-fixed `G`. The coefficient recursion `solCoeff` builds `G` with `(1−φ)G = F`
(`mk_solCoeff_sub_phi`); `ψ G = G` is then automatic (apply `ψ` to `G − φG = F`, using
`ψ φ = id` and `ψ F = 0`). -/
theorem exists_one_sub_phi_eq {F : PowerSeries ℤ_[p]} (hF : F ∈ psiZeroSeries p)
    (h0 : constantCoeff F = 0) :
    ∃ G ∈ psiIdSeries p, G - phiHom p G = F := by
  set G := PowerSeries.mk (solCoeff p F) with hG
  have hsub : G - phiHom p G = F := by rw [phiHom_apply]; exact mk_solCoeff_sub_phi p F h0
  refine ⟨G, ?_, hsub⟩
  -- `ψ G = G`: apply `ψ` to `G − φG = F`
  have hFz : psiSeries p F = 0 := hF
  change psiSeries p G = G
  have hψ := congrArg (psiSeries p) hsub
  rw [psiSeries_sub, phiHom_apply, psiSeries_phi_padicInt, hFz] at hψ
  -- `ψ G − G = 0`
  exact sub_eq_zero.1 hψ

end PadicLFunctions.Coleman
