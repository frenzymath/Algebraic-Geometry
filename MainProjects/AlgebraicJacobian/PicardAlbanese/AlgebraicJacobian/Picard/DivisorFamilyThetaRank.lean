/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyTheta
import AlgebraicJacobian.Picard.InvertibleModuleTransfer

/-!
# DD-4 (Task 4, (c2)-transport) — `W(d)^{Θᵃ}` as an invertible module over the equalizer
algebra

The certificate transport for the Θ-twisted glued colength module (`informal` route of
inbox I-0192): there is **no** global isomorphism `W(d)^{Θᵃ} ≅ W(d)` (the twisted delta
is not an automorphism composed with the untwisted one), but both are modules over the
**equalizer algebra** `A_D = W(d)` — the untwisted glued module with its ring structure
— and `W(d)^{Θᵃ}` is an *invertible* `A_D`-module once the twisting cocycle pairs
against its inverse (`IsThetaPaired`, the affine-colength-scheme trivialization input).
Under that pairing input, the certificate clause (c2) transports across the twist by
the semilocal Pic-vanishing (`AlgebraicJacobian.Picard.InvertibleModuleTransfer`).

* `DivisorAdaptation.gluedSubalgebra` — `A_D`: the glued equalizer as an `R`-subalgebra
  of the chart product (the overlap-restriction arrows are algebra maps).
* `DivisorAdaptation.unitGluedSubmodule` — the `u`-twisted glued module for an arbitrary
  unit family `u` on the piece overlaps; `= gluedSubmodule` at `u = 1`
  (`unitGluedSubmodule_one`), `= thetaGluedSubmodule a` at `u = thetaOvlUnit a`
  (definitionally); componentwise products multiply the twists
  (`mul_mem_unitGluedSubmodule`).
* `DivisorAdaptation.thetaSpan`/`thetaInvSpan` — `W(d)^{Θᵃ}` and `W(d)^{Θ⁻ᵃ}` as
  `A_D`-submodules of the chart product.
* `DivisorAdaptation.IsThetaPaired` — **the pairing input**: `Θᵃ`-sections and
  `Θ⁻ᵃ`-sections of the colength scheme pair onto `1` (`thetaSpan * thetaInvSpan = 1`;
  the containment `≤ 1` is automatic, `thetaSpan_mul_thetaInvSpan_le_one`).  This is the
  H⁰-trivialization content of the affine colength scheme — the honest cohomological
  residue of the (c2)-transport, discharged by the follow-on brick.
* `DivisorAdaptation.finite_thetaGlued` / `projective_thetaGlued` /
  `rankAtStalk_thetaGlued` — **the (c2)-transport keystones**: given `IsThetaPaired` and
  the certificate, `W(d)^{Θᵃ}` is finite projective over `R` of constant rank `n` —
  exactly the inputs `divisorWindowGr` consumes
  (`AlgebraicJacobian.Picard.DivisorFamilyWindow`).
* `DivisorAdaptation.thetaSectionFst`/`thetaSectionSnd` — the two manufactured global
  sections `σ = (t₀ᵃ, 1)`, `τ = (1, t₁ᵃ)` of `W(d)^{Θᵃ}` (the chart coordinates through
  the pinned trivializations), jointly unit-componented; a pairing witness against them
  suffices (`isThetaPaired_of_sectionWitness`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file; the subalgebra/submodule instance searches under the local
`overSectionsAlgebra` instances need headroom (I-0192 hazard (a)). -/
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 80000

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} {R : Type u} [CommRing R]
  [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R π d)

/-! ## The equalizer algebra `A_D` -/

/-- **The equalizer algebra `A_D`**: the glued colength module `W(d)` is an
`R`-subalgebra of the chart product — the overlap-restriction arrows are `R`-algebra
maps, so the equalizer condition is closed under multiplication. -/
noncomputable def gluedSubalgebra : Subalgebra R A.chartProd where
  carrier := A.gluedSubmodule
  add_mem' := fun hx hy => A.gluedSubmodule.add_mem hx hy
  mul_mem' := by
    intro x y hx hy
    rw [SetLike.mem_coe, mem_gluedSubmodule_iff] at hx hy ⊢
    intro p
    rw [Pi.mul_apply, Pi.mul_apply, map_mul, map_mul, hx p, hy p]
  one_mem' := by
    rw [SetLike.mem_coe, mem_gluedSubmodule_iff]
    intro p
    rw [Pi.one_apply, Pi.one_apply, map_one, map_one]
  algebraMap_mem' := by
    intro r
    rw [SetLike.mem_coe, mem_gluedSubmodule_iff]
    intro p
    rw [Pi.algebraMap_apply, Pi.algebraMap_apply, AlgHom.commutes, AlgHom.commutes]

lemma mem_gluedSubalgebra_iff {x : A.chartProd} :
    x ∈ A.gluedSubalgebra ↔ x ∈ A.gluedSubmodule :=
  Iff.rfl

/-- The equalizer algebra and the glued module have the same carrier, `R`-linearly. -/
noncomputable def gluedSubalgebraEquiv : ↥A.gluedSubalgebra ≃ₗ[R] A.Glued where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## Unit-twisted glued modules -/

variable (u v : ∀ i j : A.index, Γ(relCurve C R, A.pieces i ⊓ A.pieces j)ˣ)

/-- The `u`-twisted right overlap arrow for an arbitrary unit family `u` on the piece
overlaps (the `thetaDeltaRight` shape). -/
noncomputable def unitDeltaRight : A.chartProd →ₗ[R] A.ovlProd :=
  LinearMap.pi (fun p : A.index × A.index =>
    LinearMap.mulLeft R (Ideal.Quotient.mk (A.ovlIdeal p.1 p.2)
        ((u p.1 p.2 :
          Γ(relCurve C R, A.pieces p.1 ⊓ A.pieces p.2)ˣ) :
          Γ(relCurve C R, A.pieces p.1 ⊓ A.pieces p.2))) ∘ₗ
      (A.toOvlRight p.1 p.2).toLinearMap ∘ₗ LinearMap.proj p.2)

/-- The `u`-twisted glued colength module. -/
noncomputable def unitGluedSubmodule : Submodule R A.chartProd :=
  LinearMap.ker (A.deltaLeft - A.unitDeltaRight u)

/-- The `u`-twisted equalizer description. -/
lemma mem_unitGluedSubmodule_iff (s : A.chartProd) :
    s ∈ A.unitGluedSubmodule u ↔ ∀ p : A.index × A.index,
      A.toOvlLeft p.1 p.2 (s p.1)
        = Ideal.Quotient.mk (A.ovlIdeal p.1 p.2)
            ((u p.1 p.2 :
              Γ(relCurve C R, A.pieces p.1 ⊓ A.pieces p.2)ˣ) :
              Γ(relCurve C R, A.pieces p.1 ⊓ A.pieces p.2))
          * A.toOvlRight p.1 p.2 (s p.2) := by
  simp only [unitGluedSubmodule, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
    funext_iff, deltaLeft, unitDeltaRight, LinearMap.pi_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply,
    LinearMap.mulLeft_apply]

/-- At the trivial unit family, the twisted glued module is the glued module. -/
lemma unitGluedSubmodule_one : A.unitGluedSubmodule 1 = A.gluedSubmodule := by
  ext s
  rw [mem_unitGluedSubmodule_iff, mem_gluedSubmodule_iff]
  refine forall_congr' fun p => ?_
  rw [Pi.one_apply, Pi.one_apply, Units.val_one, map_one, one_mul]

variable (a : ℕ)

/-- At the theta unit family, the twisted glued module is `W(d)^{Θᵃ}`. -/
lemma unitGluedSubmodule_thetaOvlUnit :
    A.unitGluedSubmodule (A.thetaOvlUnit a) = A.thetaGluedSubmodule a :=
  rfl

variable {u v}

/-- **Twists multiply**: the componentwise product of a `u`-twisted and a `v`-twisted
glued family is `(u * v)`-twisted. -/
theorem mul_mem_unitGluedSubmodule {s t : A.chartProd}
    (hs : s ∈ A.unitGluedSubmodule u) (ht : t ∈ A.unitGluedSubmodule v) :
    s * t ∈ A.unitGluedSubmodule (u * v) := by
  rw [mem_unitGluedSubmodule_iff] at hs ht ⊢
  intro p
  have h1 : (s * t) p.1 = s p.1 * t p.1 := rfl
  have h2 : (s * t) p.2 = s p.2 * t p.2 := rfl
  have h3 : (((u * v) p.1 p.2 : Γ(relCurve C R, A.pieces p.1 ⊓ A.pieces p.2)ˣ) :
      Γ(relCurve C R, A.pieces p.1 ⊓ A.pieces p.2))
      = ((u p.1 p.2 : Γ(relCurve C R, A.pieces p.1 ⊓ A.pieces p.2)ˣ) :
          Γ(relCurve C R, A.pieces p.1 ⊓ A.pieces p.2))
        * ((v p.1 p.2 : Γ(relCurve C R, A.pieces p.1 ⊓ A.pieces p.2)ˣ) :
          Γ(relCurve C R, A.pieces p.1 ⊓ A.pieces p.2)) := rfl
  rw [h1, h2, h3, map_mul, map_mul, map_mul, hs p, ht p]
  ring

variable (u) in
/-- The `u`-twisted glued module as a module over the equalizer algebra `A_D`
(componentwise multiplication by an untwisted family preserves the `u`-twisted
matching). -/
noncomputable def unitGluedOver : Submodule ↥A.gluedSubalgebra A.chartProd where
  carrier := A.unitGluedSubmodule u
  add_mem' := fun hx hy => (A.unitGluedSubmodule u).add_mem hx hy
  zero_mem' := (A.unitGluedSubmodule u).zero_mem
  smul_mem' := by
    intro c x hx
    have hc : (c : A.chartProd) ∈ A.unitGluedSubmodule 1 := by
      rw [unitGluedSubmodule_one]
      exact c.2
    have hmul := A.mul_mem_unitGluedSubmodule hc hx
    rw [one_mul] at hmul
    have hsmul : c • x = (c : A.chartProd) * x := Algebra.smul_def c x
    rw [SetLike.mem_coe, hsmul]
    exact hmul

lemma mem_unitGluedOver_iff {x : A.chartProd} :
    x ∈ A.unitGluedOver u ↔ x ∈ A.unitGluedSubmodule u :=
  Iff.rfl

/-! ## The pairing input and invertibility -/

/-- `W(d)^{Θᵃ}` as an `A_D`-submodule of the chart product. -/
noncomputable def thetaSpan : Submodule ↥A.gluedSubalgebra A.chartProd :=
  A.unitGluedOver (A.thetaOvlUnit a)

/-- `W(d)^{Θ⁻ᵃ}` (the inverse-twisted glued module) as an `A_D`-submodule. -/
noncomputable def thetaInvSpan : Submodule ↥A.gluedSubalgebra A.chartProd :=
  A.unitGluedOver (A.thetaOvlUnit a)⁻¹

lemma mem_thetaSpan_iff {x : A.chartProd} :
    x ∈ A.thetaSpan a ↔ x ∈ A.thetaGluedSubmodule a :=
  Iff.rfl

lemma mem_thetaInvSpan_iff {x : A.chartProd} :
    x ∈ A.thetaInvSpan a ↔ x ∈ A.unitGluedSubmodule (A.thetaOvlUnit a)⁻¹ :=
  Iff.rfl

/-- Products of `Θᵃ`- and `Θ⁻ᵃ`-sections are untwisted: the pairing lands in the
equalizer algebra. -/
theorem thetaSpan_mul_thetaInvSpan_le_one :
    A.thetaSpan a * A.thetaInvSpan a ≤ 1 := by
  rw [Submodule.mul_le]
  intro s hs t ht
  have hmul := A.mul_mem_unitGluedSubmodule
    (A.mem_thetaSpan_iff a |>.mp hs) (A.mem_thetaInvSpan_iff a |>.mp ht)
  rw [mul_inv_cancel, unitGluedSubmodule_one] at hmul
  rw [Submodule.one_eq_range]
  exact ⟨⟨s * t, hmul⟩, rfl⟩

/-- **The pairing input** (the honest cohomological residue of the (c2)-transport):
the `Θᵃ`- and `Θ⁻ᵃ`-twisted glued modules pair onto the full equalizer algebra — the
trivialization `1 = Σ σₗ · uₗ` of the twist on the affine colength scheme. -/
def IsThetaPaired : Prop :=
  A.thetaSpan a * A.thetaInvSpan a = 1

/-- The pairing input reduces to hitting `1`. -/
theorem isThetaPaired_of_one_mem
    (h : (1 : A.chartProd) ∈ A.thetaSpan a * A.thetaInvSpan a) :
    A.IsThetaPaired a := by
  refine le_antisymm (A.thetaSpan_mul_thetaInvSpan_le_one a) ?_
  rw [Submodule.one_eq_span]
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr h)

/-- A two-term pairing witness suffices: sections `s, t` of `W(d)^{Θᵃ}` and `u, v` of
`W(d)^{Θ⁻ᵃ}` with `s·u + t·v = 1` discharge the pairing input. -/
theorem isThetaPaired_of_witness {s t u' v' : A.chartProd}
    (hs : s ∈ A.thetaGluedSubmodule a) (ht : t ∈ A.thetaGluedSubmodule a)
    (hu : u' ∈ A.unitGluedSubmodule (A.thetaOvlUnit a)⁻¹)
    (hv : v' ∈ A.unitGluedSubmodule (A.thetaOvlUnit a)⁻¹)
    (h : s * u' + t * v' = 1) :
    A.IsThetaPaired a := by
  refine A.isThetaPaired_of_one_mem a ?_
  rw [← h]
  exact Submodule.add_mem _ (Submodule.mul_mem_mul hs hu) (Submodule.mul_mem_mul ht hv)

/-- **Invertibility of the twisted module over the equalizer algebra**: under the
pairing input, `W(d)^{Θᵃ}` is an invertible `A_D`-module (a unit of the submodule
monoid with inverse `W(d)^{Θ⁻ᵃ}`, mathlib's Picard-group vocabulary). -/
theorem invertible_thetaSpan (h : A.IsThetaPaired a) :
    Module.Invertible ↥A.gluedSubalgebra
      ↥(A.thetaSpan a : Submodule ↥A.gluedSubalgebra A.chartProd) := by
  haveI hfs : FaithfulSMul ↥A.gluedSubalgebra A.chartProd := inferInstance
  let I : (Submodule ↥A.gluedSubalgebra A.chartProd)ˣ :=
    ⟨A.thetaSpan a, A.thetaInvSpan a, h, by rw [mul_comm]; exact h⟩
  exact Module.Invertible.left (Submodule.tensorInvEquiv I)

/-! ## The (c2)-transport keystones -/

/-- The `A_D`-scalar action on `W(d)^{Θᵃ}`: componentwise multiplication in the chart
product (an untwisted family times a `Θᵃ`-twisted family is `Θᵃ`-twisted). -/
noncomputable instance : SMul ↥A.gluedSubalgebra (A.ThetaGlued a) where
  smul c x := ⟨(c : A.chartProd) * x, by
    have h := A.mul_mem_unitGluedSubmodule (u := 1) (v := A.thetaOvlUnit a)
      (show (c : A.chartProd) ∈ A.unitGluedSubmodule 1 by
        rw [unitGluedSubmodule_one]; exact c.2)
      (show (x : A.chartProd) ∈ A.unitGluedSubmodule (A.thetaOvlUnit a) from x.2)
    rw [one_mul] at h
    exact h⟩

lemma smul_thetaGlued_coe (c : ↥A.gluedSubalgebra) (x : A.ThetaGlued a) :
    ((c • x : A.ThetaGlued a) : A.chartProd) = (c : A.chartProd) * x :=
  rfl

/-- **`W(d)^{Θᵃ}` is a module over the equalizer algebra** by componentwise
multiplication. -/
noncomputable instance : Module ↥A.gluedSubalgebra (A.ThetaGlued a) :=
  Function.Injective.module ↥A.gluedSubalgebra
    ((A.thetaGluedSubmodule a).subtype.toAddMonoidHom) Subtype.val_injective
    (fun c x => by
      change ((c • x : A.ThetaGlued a) : A.chartProd) = c • (x : A.chartProd)
      rw [smul_thetaGlued_coe, Algebra.smul_def]
      rfl)

instance : IsScalarTower R ↥A.gluedSubalgebra (A.ThetaGlued a) where
  smul_assoc r c x := by
    refine Subtype.ext ?_
    have h1 : (((r • c) • x : A.ThetaGlued a) : A.chartProd)
        = ((r • c : ↥A.gluedSubalgebra) : A.chartProd) * x := rfl
    have h2 : ((r • (c • x) : A.ThetaGlued a) : A.chartProd)
        = r • ((c • x : A.ThetaGlued a) : A.chartProd) := rfl
    have h3 : ((c • x : A.ThetaGlued a) : A.chartProd) = (c : A.chartProd) * x := rfl
    have h4 : ((r • c : ↥A.gluedSubalgebra) : A.chartProd)
        = r • (c : A.chartProd) := rfl
    rw [h1, h2, h3, h4, smul_mul_assoc]

/-- The twisted `A_D`-submodule and `W(d)^{Θᵃ}` have the same carrier,
`A_D`-linearly. -/
noncomputable def thetaSpanEquiv :
    ↥(A.thetaSpan a : Submodule ↥A.gluedSubalgebra A.chartProd)
      ≃ₗ[↥A.gluedSubalgebra] A.ThetaGlued a where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' c x := by
    refine Subtype.ext ?_
    rw [smul_thetaGlued_coe]
    change (c • (x : A.chartProd)) = (c : A.chartProd) * x
    rw [Algebra.smul_def]
    rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Invertibility of `W(d)^{Θᵃ}` over the equalizer algebra**, on the consumer's
carrier. -/
theorem invertible_thetaGlued (h : A.IsThetaPaired a) :
    Module.Invertible ↥A.gluedSubalgebra (A.ThetaGlued a) :=
  haveI := A.invertible_thetaSpan a h
  Module.Invertible.congr (A.thetaSpanEquiv a)

/-- **(c2)-transport, finiteness**: under the pairing input, the Θ-twisted glued module
is a finite `R`-module. -/
theorem finite_thetaGlued (h : A.IsThetaPaired a) (hfin : Module.Finite R A.Glued) :
    Module.Finite R (A.ThetaGlued a) := by
  haveI := hfin
  haveI : Module.Finite R ↥A.gluedSubalgebra :=
    Module.Finite.equiv A.gluedSubalgebraEquiv.symm
  haveI := A.invertible_thetaGlued a h
  exact Module.Invertible.finite_trans (A := ↥A.gluedSubalgebra)

/-- **(c2)-transport, projectivity**: under the pairing input, the Θ-twisted glued
module is projective over `R`. -/
theorem projective_thetaGlued (h : A.IsThetaPaired a)
    (hproj : Module.Projective R A.Glued) :
    Module.Projective R (A.ThetaGlued a) := by
  haveI := hproj
  haveI : Module.Projective R ↥A.gluedSubalgebra :=
    Module.Projective.of_equiv A.gluedSubalgebraEquiv.symm
  haveI := A.invertible_thetaGlued a h
  exact Module.Invertible.projective_trans (A := ↥A.gluedSubalgebra)

/-- **(c2)-transport, constant rank** (the semilocal Pic-vanishing): under the pairing
input and the certificate, the Θ-twisted glued module has the same constant fibre rank
`n` as the untwisted one — the input `divisorWindowGr` consumes. -/
theorem rankAtStalk_thetaGlued {n : ℕ} (h : A.IsThetaPaired a) (hc : A.IsCertified n)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (A.ThetaGlued a) p = n := by
  haveI := hc.finite_glued
  haveI := hc.projective_glued
  haveI : Module.Finite R ↥A.gluedSubalgebra :=
    Module.Finite.equiv A.gluedSubalgebraEquiv.symm
  haveI : Module.Projective R ↥A.gluedSubalgebra :=
    Module.Projective.of_equiv A.gluedSubalgebraEquiv.symm
  haveI := A.invertible_thetaGlued a h
  rw [Module.Invertible.rankAtStalk_eq_of_module_finite (A := ↥A.gluedSubalgebra) p,
    congrFun (Module.rankAtStalk_eq_of_equiv A.gluedSubalgebraEquiv) p]
  exact hc.rankAtStalk_glued p

end DivisorAdaptation

end AlgebraicGeometry
