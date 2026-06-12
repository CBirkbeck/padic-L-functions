/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.MeasureR.FormalPsi
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Data.Finsupp.Encodable

/-!
# The norm operator `𝒩` on `ℤ_p⟦T⟧` via the digit basis

RJW (TeX 2654–2670) introduce the norm operator `𝒩` on `ℤ_p⟦T⟧` as the relative
norm `N_{B/A}` for the degree-`p` extension of rings `A = φ(ℤ_p⟦T⟧) ⊆ ℤ_p⟦T⟧ = B`,
where `φ : G(T) ↦ G((1+T)^p − 1)` is the Frobenius substitution. Concretely
(TeX 2658, "B is free of rank p over A, obtained by adjoining a p-th root of
`(1+T)^p`") the ring `B` is free of rank `p` over the subring `A = φ(B)`, with
basis `1, (1+T), …, (1+T)^{p−1}`: this is exactly the **digit decomposition**
`F = Σ_{i<p} (1+T)^i · φ(F_i)` proven (over `integerRing K`) in
`PadicLFunctions.MeasureR.FormalPsi` (`existsUnique_digits`). We realise the
free `A`-module structure as `Module.compHom` along the φ-ring-hom `phiHom`
(carried by the type synonym `PhiAlg` so the `φ`-module structure does NOT leak
onto `PowerSeries ℤ_[p]`), and set `𝒩 := Algebra.norm` of that free rank-`p`
algebra.

**Replan R10.4** (`.mathlib-quality/decomposition.md`): RJW also give the
product formula `φ(𝒩f) = ∏_{ξ ∈ μ_p} f((1+T)ξ − 1)` (TeX 2666). This is NOT
realisable as a *formal* power-series identity: the substitution
`T ↦ (1+T)ξ − 1` has constant term `ξ − 1`, which is a non-nilpotent unit for
`ξ ≠ 1` (the same `Eqphipsi` obstruction recorded for `psiSeries` in FormalPsi).
So we expose only the determinant characterisation `normOp_eq_det` here; the
evaluated product form (over the tower fields, where `(1+T)ξ − 1` becomes
topologically nilpotent) is the commuting square of ticket T907 (Theorem.lean).

The compactness layer (TeX 2784, "such a subsequence exists, as `ℤ_p⟦T⟧^×` is
compact"; replan R10.6) lives in the final section: `ℤ_p⟦T⟧` is compact and
sequentially compact for the coefficientwise (Pi) topology, the units form a
closed subset, and coefficients are continuous — the inputs for the diagonal
extraction in Coleman's theorem (T910).

Tickets: T906 (norm operator) + T909 (compactness); decomposition R10.4/R10.6.
-/

open PowerSeries

namespace PadicLFunctions

namespace Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## The digit decomposition over `ℤ_[p]`

`FormalPsi.existsUnique_digits` is stated over `integerRing K` for a
nonarchimedean field `K`. Instantiating `K := ℚ_[p]`, the ring `integerRing ℚ_[p]`
(the norm-unit ball of `ℚ_[p]`) is `ℤ_[p]` repackaged — `PadicInt` IS the ball
subtype `{x : ℚ_[p] // ‖x‖ ≤ 1}`. We transport the decomposition along the
resulting ring isomorphism. -/

/-- The ring isomorphism `ℤ_[p] ≃+* integerRing ℚ_[p]`: both are the norm-unit
ball `{x : ℚ_[p] // ‖x‖ ≤ 1}`, so the algebra map `ℤ_[p] → integerRing ℚ_[p]`
(`Coefficients.lean`) is the identity repackaging and is bijective. -/
noncomputable def padicIntEquivIntegerRing : ℤ_[p] ≃+* integerRing ℚ_[p] :=
  RingEquiv.ofBijective (algebraMap ℤ_[p] (integerRing ℚ_[p]))
    ⟨fun x y hxy =>
        PadicInt.ext (by
          have : ((algebraMap ℤ_[p] (integerRing ℚ_[p]) x : integerRing ℚ_[p]) : ℚ_[p])
              = ((algebraMap ℤ_[p] (integerRing ℚ_[p]) y : integerRing ℚ_[p]) : ℚ_[p]) := by
            rw [hxy]
          exact this),
      fun y => ⟨⟨(y : ℚ_[p]), y.2⟩, Subtype.ext rfl⟩⟩

/-- The digit decomposition over `ℤ_[p]` itself: every `F ∈ ℤ_p⟦T⟧` is uniquely
`Σ_{i<p} (1+T)^i · φ(G_i)`. Transported from `FormalPsi.existsUnique_digits`
(over `integerRing ℚ_[p]`) along `PowerSeries.map padicIntEquivIntegerRing`. -/
theorem existsUnique_digits_padicInt (F : PowerSeries ℤ_[p]) :
    ∃! G : Fin p → PowerSeries ℤ_[p], IsDigitDecomp p F G := by
  set e := padicIntEquivIntegerRing p with he
  -- the forward and backward coefficient maps
  set me : PowerSeries ℤ_[p] →+* PowerSeries (integerRing ℚ_[p]) :=
    PowerSeries.map (e : ℤ_[p] →+* integerRing ℚ_[p]) with hme
  set me' : PowerSeries (integerRing ℚ_[p]) →+* PowerSeries ℤ_[p] :=
    PowerSeries.map (e.symm : integerRing ℚ_[p] →+* ℤ_[p]) with hme'
  have hround : ∀ G : PowerSeries ℤ_[p], me' (me G) = G := fun G =>
    PowerSeries.ext fun n => by
      rw [hme', hme, PowerSeries.coeff_map, PowerSeries.coeff_map]
      exact RingEquiv.symm_apply_apply e _
  obtain ⟨G, hG, hGuniq⟩ := existsUnique_digits p ℚ_[p] (me F)
  refine ⟨fun i => me' (G i), ?_, ?_⟩
  · have := isDigitDecomp_map p (e.symm : integerRing ℚ_[p] →+* ℤ_[p]) hG
    rwa [hround] at this
  · intro H hH
    have hmapH : IsDigitDecomp p (me F) (fun i => me (H i)) := by
      have := isDigitDecomp_map p (e : ℤ_[p] →+* integerRing ℚ_[p]) hH
      simpa [hme] using this
    have := hGuniq (fun i => me (H i)) hmapH
    funext i
    rw [show H i = me' (me (H i)) from (hround (H i)).symm, ← congrFun this i]

/-! ### The formal `ψ` over `ℤ_[p]`

`FormalPsi.psiSeries` (the `0`-th digit) is junk-totalised over a general
`CommRing`, computing honestly exactly where the digit decomposition is unique.
Over `ℤ_[p]` that locus is everything (`existsUnique_digits_padicInt`), so the
`ψ`-linearity facts (`psiSeries_phi`, `psiSeries_add`, `psiSeries_C_mul`) — proven
over `integerRing K` in FormalPsi — transport verbatim. These let `ψ` cancel the
`p^k` in `phi_injective_mod` (part (i)). -/

variable {p}

/-- Over `ℤ_[p]`, `ψ` is the `0`-th digit of any digit decomposition. -/
theorem psiSeries_eq_of_isDigitDecomp_padicInt {F : PowerSeries ℤ_[p]}
    {G : Fin p → PowerSeries ℤ_[p]} (hG : IsDigitDecomp p F G) :
    psiSeries p F = G 0 :=
  psiSeries_eq_of_unique p (existsUnique_digits_padicInt p F) hG

/-- `ψ ∘ φ = id` over `ℤ_[p]`: the digit family of `φ(G)` is `(G, 0, …, 0)`,
so its `0`-th digit is `G`. (FormalPsi `psiSeries_phi`, transported.) -/
theorem psiSeries_phi_padicInt (G : PowerSeries ℤ_[p]) :
    psiSeries p (phiSeries p G) = G := by
  refine psiSeries_eq_of_isDigitDecomp_padicInt (G := fun i => if i = 0 then G else 0) ?_
  change phiSeries p G = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
      * phiSeries p (if i = 0 then G else 0)
  rw [Finset.sum_eq_single (0 : Fin p)]
  · simp
  · intro i _ hi0
    rw [if_neg hi0, phiSeries_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin p)) h

/-- `ψ` is additive over `ℤ_[p]`. (FormalPsi `psiSeries_add`, transported.) -/
theorem psiSeries_add_padicInt (F G : PowerSeries ℤ_[p]) :
    psiSeries p (F + G) = psiSeries p F + psiSeries p G := by
  obtain ⟨GF, hGF, -⟩ := existsUnique_digits_padicInt p F
  obtain ⟨GG, hGG, -⟩ := existsUnique_digits_padicInt p G
  rw [psiSeries_eq_of_isDigitDecomp_padicInt hGF, psiSeries_eq_of_isDigitDecomp_padicInt hGG]
  refine psiSeries_eq_of_isDigitDecomp_padicInt (G := fun i => GF i + GG i) ?_
  change F + G = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (GF i + GG i)
  rw [hGF, hGG, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [phiSeries, phiSeries, phiSeries,
    PowerSeries.subst_add (hasSubst_one_add_X_pow_sub_one p), mul_add]

/-- `ψ(C a · F) = C a · ψ(F)` over `ℤ_[p]`. (FormalPsi `psiSeries_C_mul`,
transported — the form `phi_injective_mod` uses to pull `C(p^k)` through `ψ`.) -/
theorem psiSeries_C_mul_padicInt (a : ℤ_[p]) (F : PowerSeries ℤ_[p]) :
    psiSeries p (PowerSeries.C a * F) = PowerSeries.C a * psiSeries p F := by
  obtain ⟨GF, hGF, -⟩ := existsUnique_digits_padicInt p F
  rw [psiSeries_eq_of_isDigitDecomp_padicInt hGF]
  refine psiSeries_eq_of_isDigitDecomp_padicInt (G := fun i => PowerSeries.C a * GF i) ?_
  change PowerSeries.C a * F = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
      * phiSeries p (PowerSeries.C a * GF i)
  rw [hGF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [phiSeries, phiSeries,
    PowerSeries.subst_mul (hasSubst_one_add_X_pow_sub_one p),
    show ((PowerSeries.C a).subst ((1 + PowerSeries.X) ^ p - 1)
        : PowerSeries ℤ_[p]) = PowerSeries.C a from PowerSeries.subst_C a]
  ring

variable (p)

/-! ## The φ-algebra and the digit basis

The norm operator is `Algebra.norm` for the φ-algebra structure on `ℤ_p⟦T⟧`:
the ring `B = ℤ_p⟦T⟧` viewed as an algebra over the subring `A = φ(B)` via the
Frobenius `φ`. We carry this structure on a type synonym `PhiAlg` so the
`φ`-`Algebra` instance does NOT leak onto `PowerSeries ℤ_[p]` (which already has
its standard `ℤ_[p]⟦T⟧`-algebra structure). The free `A`-basis `1, …, (1+T)^{p−1}`
is the digit decomposition `existsUnique_digits_padicInt`. -/

/-- The Frobenius substitution `φ : F ↦ F((1+T)^p − 1)` as a ring homomorphism
(`FormalPsi.phiSeries` packaged via `substAlgHom.toRingHom`). -/
noncomputable def phiHom : PowerSeries ℤ_[p] →+* PowerSeries ℤ_[p] :=
  (PowerSeries.substAlgHom (hasSubst_one_add_X_pow_sub_one (R := ℤ_[p]) p)).toRingHom

@[simp]
theorem phiHom_apply (F : PowerSeries ℤ_[p]) : phiHom p F = phiSeries p F := by
  change (PowerSeries.substAlgHom (hasSubst_one_add_X_pow_sub_one (R := ℤ_[p]) p)) F
      = phiSeries p F
  rw [phiSeries, PowerSeries.coe_substAlgHom]

/-- The type synonym carrying the `φ`-`A`-module/algebra structure on `ℤ_p⟦T⟧`.
`PhiAlg p` is `PowerSeries ℤ_[p]` as a module over `A = φ(ℤ_p⟦T⟧)`; the algebra
map `ℤ_p⟦T⟧ → PhiAlg p` is `φ` (so the structure stays off the bare
`PowerSeries ℤ_[p]`). -/
def PhiAlg : Type := PowerSeries ℤ_[p]

namespace PhiAlg

noncomputable instance : CommRing (PhiAlg p) :=
  inferInstanceAs (CommRing (PowerSeries ℤ_[p]))

/-- The `φ`-algebra structure: `ℤ_p⟦T⟧` acts on `PhiAlg p` through `φ`. -/
noncomputable instance : Algebra (PowerSeries ℤ_[p]) (PhiAlg p) :=
  RingHom.toAlgebra (phiHom p)

/-- The identity repackaging `PhiAlg p ≃+* PowerSeries ℤ_[p]` (same carrier and
`CommRing`); used to move between the module language and `IsDigitDecomp`. -/
noncomputable def toPS : PhiAlg p ≃+* PowerSeries ℤ_[p] := RingEquiv.refl _

variable {p}

@[simp]
theorem toPS_apply (x : PhiAlg p) : toPS p x = x := rfl

@[simp]
theorem toPS_symm_apply (F : PowerSeries ℤ_[p]) : (toPS p).symm F = F := rfl

/-- The image of the `φ`-algebra map: `toPS (algebraMap c) = φ(c)`. -/
theorem toPS_algebraMap (c : PowerSeries ℤ_[p]) :
    toPS p (algebraMap (PowerSeries ℤ_[p]) (PhiAlg p) c) = phiSeries p c := by
  rw [RingHom.algebraMap_toAlgebra]
  change phiHom p c = phiSeries p c
  rw [phiHom_apply]

/-- The `φ`-`smul` on `PhiAlg p` is multiplication by the `φ`-image. -/
theorem smul_def (c : PowerSeries ℤ_[p]) (x : PhiAlg p) :
    toPS p (c • x) = phiSeries p c * toPS p x := by
  rw [Algebra.smul_def, map_mul, toPS_algebraMap]

end PhiAlg

variable {p}

/-- The `φ`-`A`-linear combination `∑ c i • (1+T)^i` in `PhiAlg p` is exactly the
digit expression `∑ (1+T)^i · φ(c i)`: this bridges the module language of
`Module.Basis.mk` and the predicate `IsDigitDecomp`. -/
theorem sum_smul_one_add_X_pow_eq (c : Fin p → PowerSeries ℤ_[p]) :
    PhiAlg.toPS p (∑ i : Fin p, c i • ((1 + PowerSeries.X) ^ (i : ℕ) : PhiAlg p))
      = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (c i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PhiAlg.smul_def, PhiAlg.toPS_apply]
  exact mul_comm _ _

variable (p)

/-- W6b/T906: the digit basis `1, (1+T), …, (1+T)^{p−1}` of `ℤ_p⟦T⟧` as a free
module of rank `p` over `A = φ(ℤ_p⟦T⟧)` (`PhiAlg p`). Spanning is the existence
half of `existsUnique_digits_padicInt`, linear independence is its uniqueness
half. (RJW TeX 2658: "`B` is free of rank `p` over `A`, obtained by adjoining a
`p`-th root of `(1+T)^p`".) -/
noncomputable def digitBasis : Module.Basis (Fin p) (PowerSeries ℤ_[p]) (PhiAlg p) :=
  Module.Basis.mk
    (v := fun i => ((1 + PowerSeries.X) ^ (i : ℕ) : PhiAlg p))
    (-- linear independence ← uniqueness of digits
      Fintype.linearIndependent_iffₛ.2 fun f g hfg i => by
        have hf : IsDigitDecomp p
            (PhiAlg.toPS p (∑ j : Fin p, f j • ((1 + PowerSeries.X) ^ (j : ℕ) : PhiAlg p)))
            f := sum_smul_one_add_X_pow_eq f
        have hg : IsDigitDecomp p
            (PhiAlg.toPS p (∑ j : Fin p, g j • ((1 + PowerSeries.X) ^ (j : ℕ) : PhiAlg p)))
            g := sum_smul_one_add_X_pow_eq g
        rw [hfg] at hf
        have hex := existsUnique_digits_padicInt p
          (PhiAlg.toPS p (∑ j : Fin p, g j • ((1 + PowerSeries.X) ^ (j : ℕ) : PhiAlg p)))
        exact congrFun (hex.unique hf hg) i)
    (-- spanning ← existence of digits
      (Submodule.top_le_span_range_iff_forall_exists_fun (PowerSeries ℤ_[p])).2 fun x => by
        obtain ⟨G, hG, -⟩ := existsUnique_digits_padicInt p (PhiAlg.toPS p x)
        refine ⟨G, (PhiAlg.toPS p).injective ?_⟩
        rw [sum_smul_one_add_X_pow_eq G, PhiAlg.toPS_apply]
        exact hG.symm)

@[simp]
theorem digitBasis_apply (i : Fin p) :
    digitBasis p i = ((1 + PowerSeries.X) ^ (i : ℕ) : PhiAlg p) :=
  Module.Basis.mk_apply _ _ i

/-- `PhiAlg p` is a free module over `A = φ(ℤ_p⟦T⟧)` (witnessed by `digitBasis`). -/
instance : Module.Free (PowerSeries ℤ_[p]) (PhiAlg p) :=
  Module.Free.of_basis (digitBasis p)

/-- `PhiAlg p` is module-finite (rank `p`) over `A = φ(ℤ_p⟦T⟧)`. -/
instance : Module.Finite (PowerSeries ℤ_[p]) (PhiAlg p) :=
  Module.Finite.of_basis (digitBasis p)

/-! ## The norm operator `𝒩` -/

variable {p}

/-- W6b/T906: the norm operator `𝒩 : ℤ_p⟦T⟧ → ℤ_p⟦T⟧`, defined as the relative
norm `N_{B/A}` of the free rank-`p` φ-algebra `B = ℤ_p⟦T⟧` over `A = φ(ℤ_p⟦T⟧)`
(`Algebra.norm` along `PhiAlg`). RJW TeX 2654–2660.

The norm lands in the base ring `A`, which (under the φ-iso `A ≅ ℤ_p⟦T⟧`) we
identify with `ℤ_p⟦T⟧`: no `φ⁻¹` is needed here — the source's `φ⁻¹` is an
artifact of viewing `A` as a subring of `B`, whereas `Algebra.norm` already
takes values in the abstract base. -/
noncomputable def normOp (f : PowerSeries ℤ_[p]) : PowerSeries ℤ_[p] :=
  Algebra.norm (PowerSeries ℤ_[p]) ((PhiAlg.toPS p).symm f)

/-- `𝒩` is multiplicative (the relative norm is a monoid hom). RJW TeX 2660. -/
theorem normOp_mul (f g : PowerSeries ℤ_[p]) :
    normOp (f * g) = normOp f * normOp g := by
  unfold normOp
  rw [show (PhiAlg.toPS p).symm (f * g)
      = (PhiAlg.toPS p).symm f * (PhiAlg.toPS p).symm g from map_mul _ _ _, map_mul]

/-- `𝒩 1 = 1`. -/
@[simp]
theorem normOp_one : normOp (1 : PowerSeries ℤ_[p]) = 1 := by
  unfold normOp; rw [map_one, map_one]

/-- `𝒩` sends units to units (the norm of a unit is a unit). RJW TeX 2660. -/
theorem normOp_isUnit {f : PowerSeries ℤ_[p]} (hf : IsUnit f) : IsUnit (normOp f) :=
  (hf.map (PhiAlg.toPS p).symm).map (Algebra.norm (PowerSeries ℤ_[p]))

/-- The matrix of multiplication-by-`f` in the digit basis (entries in `A`,
identified with `ℤ_p⟦T⟧`). Its determinant is `𝒩f` (`normOp_eq_det`); this is
the determinant characterisation that the evaluation/norm commuting square
(T907) transports through `evalPi`. -/
noncomputable def digitMatrix (f : PowerSeries ℤ_[p]) :
    Matrix (Fin p) (Fin p) (PowerSeries ℤ_[p]) :=
  Algebra.leftMulMatrix (digitBasis p) ((PhiAlg.toPS p).symm f)

/-- W6b/T906 (the determinant characterisation, replan R10.4): `𝒩f` is the
determinant of the multiplication-by-`f` matrix in the digit basis. (The
`μ_p`-product formula `φ(𝒩f) = ∏_ξ f((1+T)ξ−1)` is NOT a formal identity — the
substitution `(1+T)ξ−1` has non-nilpotent constant term for `ξ ≠ 1`; the
evaluated form is the commuting square of T907.) -/
theorem normOp_eq_det (f : PowerSeries ℤ_[p]) :
    normOp f = Matrix.det (digitMatrix f) := by
  unfold normOp digitMatrix
  rw [Algebra.norm_eq_matrix_det (digitBasis p)]

/-! ## Congruence mod `p^k` of power series (T908)

RJW's continuity lemmas (TeX 2726–2756; cf. CS06 Lem 2.3.1) are stated as
congruences `f ≡ g mod p^k` of power series in `ℤ_p⟦T⟧`. We make the idiom
precise as coefficientwise `p^k`-divisibility (`ModEqPow`), give it the basic
equivalence-relation + ring-compatible API, and record the equivalent
`C`-factor form `f − g = C(p^k)·h` (the form that lets `ψ` cancel `p^k` in
part (i)). Replan R10.5. -/

variable (p)

/-- T908: `f ≡ g mod p^k` for power series over `ℤ_[p]` — every coefficient of
`f − g` is divisible by `p^k`. (RJW writes `f ≡ g (mod p^k)`, TeX 2729–2736.) -/
def ModEqPow (k : ℕ) (f g : PowerSeries ℤ_[p]) : Prop :=
  ∀ m, (p : ℤ_[p]) ^ k ∣ PowerSeries.coeff m (f - g)

variable {p}

@[refl]
theorem ModEqPow.refl (k : ℕ) (f : PowerSeries ℤ_[p]) : ModEqPow p k f f := fun m => by
  rw [sub_self, map_zero]; exact dvd_zero _

theorem ModEqPow.symm {k : ℕ} {f g : PowerSeries ℤ_[p]} (h : ModEqPow p k f g) :
    ModEqPow p k g f := fun m => by
  rw [show g - f = -(f - g) from (neg_sub f g).symm, map_neg]; exact (h m).neg_right

theorem ModEqPow.trans {k : ℕ} {f g h : PowerSeries ℤ_[p]} (hfg : ModEqPow p k f g)
    (hgh : ModEqPow p k g h) : ModEqPow p k f h := fun m => by
  rw [show f - h = (f - g) + (g - h) from by ring, map_add]
  exact dvd_add (hfg m) (hgh m)

/-- The `C`-factor form: `f ≡ g mod p^k` iff `f − g = C(p^k)·h` for some `h`.
This is the form RJW's `mod p^k` congruence takes when `ψ`-linearity must
cancel the `p^k` (part (i)). -/
theorem modEqPow_iff_exists_C_mul {k : ℕ} {f g : PowerSeries ℤ_[p]} :
    ModEqPow p k f g ↔ ∃ h, f - g = PowerSeries.C ((p : ℤ_[p]) ^ k) * h := by
  constructor
  · intro hfg
    -- build the quotient series coefficientwise
    choose c hc using hfg
    refine ⟨PowerSeries.mk c, PowerSeries.ext fun m => ?_⟩
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc m]
  · rintro ⟨h, hh⟩ m
    rw [hh, PowerSeries.coeff_C_mul]
    exact Dvd.intro _ rfl

/-- `ModEqPow` is preserved under multiplication on the right by a common
factor (the multiplicative compatibility, half of the congruence ring API). -/
theorem ModEqPow.mul_right {k : ℕ} {f g : PowerSeries ℤ_[p]} (h : ModEqPow p k f g)
    (c : PowerSeries ℤ_[p]) : ModEqPow p k (f * c) (g * c) := by
  obtain ⟨q, hq⟩ := modEqPow_iff_exists_C_mul.1 h
  exact modEqPow_iff_exists_C_mul.2 ⟨q * c, by rw [← sub_mul, hq, mul_assoc]⟩

/-- Multiplicative compatibility: `f₁ ≡ g₁` and `f₂ ≡ g₂` give `f₁f₂ ≡ g₁g₂`. -/
theorem ModEqPow.mul {k : ℕ} {f₁ g₁ f₂ g₂ : PowerSeries ℤ_[p]}
    (h₁ : ModEqPow p k f₁ g₁) (h₂ : ModEqPow p k f₂ g₂) :
    ModEqPow p k (f₁ * f₂) (g₁ * g₂) := by
  refine (h₁.mul_right f₂).trans ?_
  rw [mul_comm g₁ f₂, mul_comm g₁ g₂]
  exact h₂.mul_right g₁

/-- Powers respect `ModEqPow`: `f ≡ g mod p^k` gives `f^n ≡ g^n mod p^k`. -/
theorem ModEqPow.pow {k : ℕ} {f g : PowerSeries ℤ_[p]} (h : ModEqPow p k f g) :
    ∀ n, ModEqPow p k (f ^ n) (g ^ n)
  | 0 => by simpa using ModEqPow.refl k (1 : PowerSeries ℤ_[p])
  | n + 1 => by rw [pow_succ, pow_succ]; exact (h.pow n).mul h

/-! ## The continuity lemmas (T908, RJW TeX 2726–2756)

RJW's `lem:norm continuity`. Parts (i)/(ii) are "left as an exercise
(cf. CS06 Lem 2.3.1)"; we expand them per the source-gap rule (replan R10.5).
Part (i) uses that `ψ ∘ φ = id` and `ψ` is `ℤ_[p]`-linear: a congruence
`φf ≡ 1 mod p^k` is `φ(f − 1) = C(p^k)·h`, and applying `ψ` cancels — `ψ` carries
`C(p^k)` straight through (`psiSeries_C_mul_padicInt`) and undoes `φ`. -/

/-- `phiSeries` is a ring hom over `ℤ_[p]` (it is `phiHom`), so it fixes `1` and
respects subtraction. -/
theorem phiSeries_sub (f g : PowerSeries ℤ_[p]) :
    phiSeries p (f - g) = phiSeries p f - phiSeries p g := by
  rw [← phiHom_apply, ← phiHom_apply, ← phiHom_apply, map_sub]

theorem phiSeries_one_padicInt : phiSeries p (1 : PowerSeries ℤ_[p]) = 1 := by
  rw [← phiHom_apply, map_one]

/-- T908 (i), RJW TeX 2729: if `φ(f) ≡ 1 mod p^k` then `f ≡ 1 mod p^k`. The
Frobenius `φ` is coefficientwise-injective mod `p^k`. Route: the retraction
`ψ ∘ φ = id` is `ℤ_[p]`-linear, so it cancels the `C(p^k)` factor
(`psiSeries_phi_padicInt` + `psiSeries_C_mul_padicInt`; CS06 Lem 2.3.1). -/
theorem phi_injective_mod {k : ℕ} {f : PowerSeries ℤ_[p]}
    (h : ModEqPow p k (phiSeries p f) 1) : ModEqPow p k f 1 := by
  obtain ⟨q, hq⟩ := modEqPow_iff_exists_C_mul.1 h
  -- `φ(f − 1) = φf − 1 = C(p^k)·q`; apply `ψ`
  have hφ : phiSeries p (f - 1) = PowerSeries.C ((p : ℤ_[p]) ^ k) * q := by
    rw [phiSeries_sub, phiSeries_one_padicInt, hq]
  refine modEqPow_iff_exists_C_mul.2 ⟨psiSeries p q, ?_⟩
  have := congrArg (psiSeries p) hφ
  rwa [psiSeries_phi_padicInt, psiSeries_C_mul_padicInt] at this

/-! ## Compactness of `ℤ_p⟦T⟧` and sequential extraction (T909)

For the coefficientwise (Pi) topology (`PowerSeries.WithPiTopology`), `ℤ_p⟦T⟧` is
compact (Tychonoff, `ℤ_[p]` compact) and — being a countable product of metric
spaces — sequentially compact. The units form a closed subset and coefficient
maps are continuous: exactly the inputs for the diagonal extraction in Coleman's
theorem (RJW TeX 2784, "such a subsequence exists, as `ℤ_p⟦T⟧^×` is compact";
replan R10.6). -/

open scoped PowerSeries.WithPiTopology

section Compactness

variable (p)

/-- `ℤ_p⟦T⟧` is compact for the coefficientwise topology (Tychonoff: the
underlying space is `(Unit →₀ ℕ) → ℤ_[p]`, a product of the compact `ℤ_[p]`). -/
instance instCompactSpace : CompactSpace (PowerSeries ℤ_[p]) :=
  inferInstanceAs (CompactSpace ((Unit →₀ ℕ) → ℤ_[p]))

/-- `ℤ_p⟦T⟧` is sequentially compact: the coefficient index `Unit →₀ ℕ` is
countable, so the product topology is metrizable, hence first-countable; with
compactness this gives sequential compactness. -/
instance instSeqCompactSpace : SeqCompactSpace (PowerSeries ℤ_[p]) :=
  inferInstanceAs (SeqCompactSpace ((Unit →₀ ℕ) → ℤ_[p]))

variable {p}

/-- T909: every sequence in `ℤ_p⟦T⟧` has a coefficientwise-convergent
subsequence (the extraction feeding T910's diagonal argument). -/
theorem exists_subseq_tendsto (g : ℕ → PowerSeries ℤ_[p]) :
    ∃ (f : PowerSeries ℤ_[p]) (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto (g ∘ φ) Filter.atTop (nhds f) :=
  SeqCompactSpace.tendsto_subseq g

/-- T909: coefficient maps are continuous limits — coefficientwise convergence
`gₘ → f` gives `coeff n (gₘ) → coeff n f` for every `n`. (Projection continuity
in the Pi topology; T910's diagonal argument passes limits through coefficients
with this.) -/
theorem tendsto_coeff {g : ℕ → PowerSeries ℤ_[p]} {f : PowerSeries ℤ_[p]}
    (hg : Filter.Tendsto g Filter.atTop (nhds f)) (n : ℕ) :
    Filter.Tendsto (fun m => PowerSeries.coeff n (g m)) Filter.atTop
      (nhds (PowerSeries.coeff n f)) :=
  ((WithPiTopology.continuous_coeff ℤ_[p] n).tendsto f).comp hg

/-- T909: the units of `ℤ_p⟦T⟧` form a closed subset for the coefficientwise
topology. A power series is a unit iff its constant coefficient is a unit in
`ℤ_[p]` (`PowerSeries.isUnit_iff_constantCoeff`), iff that coefficient has norm
`1` (`PadicInt.isUnit_iff`); this is the preimage of the closed set
`{‖·‖ = 1} ⊆ ℝ` under the continuous map `f ↦ ‖constantCoeff f‖`. (Limits of
units along convergent subsequences are units — used in T910.) -/
theorem isClosed_isUnit :
    IsClosed {f : PowerSeries ℤ_[p] | IsUnit f} := by
  have hset : {f : PowerSeries ℤ_[p] | IsUnit f}
      = (fun f => ‖PowerSeries.constantCoeff f‖) ⁻¹' {1} := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    rw [PowerSeries.isUnit_iff_constantCoeff, PadicInt.isUnit_iff]
  rw [hset]
  exact (isClosed_singleton (x := (1 : ℝ))).preimage
    ((WithPiTopology.continuous_constantCoeff ℤ_[p]).norm)

end Compactness

end Coleman

end PadicLFunctions
