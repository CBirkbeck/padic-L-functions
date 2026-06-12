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
