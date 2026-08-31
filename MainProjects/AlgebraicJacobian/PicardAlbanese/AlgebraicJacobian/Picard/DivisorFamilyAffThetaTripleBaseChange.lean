/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaTriple

/-!
# Base change from pairwise to triple theta quotients

Restriction of the intrinsic theta sheaf from a pairwise intersection to a triple
intersection is affine base change.  Passing through the intrinsic Cartier ideals gives
the corresponding statement on divisor-restricted theta quotients:

`tripleColength ⊗[ovlColength] ThetaOverlapQuotient ≃ ThetaTripleQuotient`.

This is the local equivalence used to make triple restrictions jointly injective in the
coassociativity proof.  It is valid for every triple contained in a pair and introduces no
new certificate clause.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsProper C.hom]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

attribute [local instance] thetaOverlapSectionsModule thetaTripleSectionsModule
  thetaOverlapQuotientModule thetaTripleQuotientModule

/-- The section-ring algebra from a pairwise intersection to a contained triple. -/
@[reducible]
noncomputable def overlapSectionsToTripleAlgebra (A : AffAdaptation D d)
    (p q i j l : D.index)
    (h : A.thetaTripleOpen i j l ≤ D.pieces p ⊓ D.pieces q) :
    Algebra Γ(relCurve C R, D.pieces p ⊓ D.pieces q)
      Γ(relCurve C R, A.thetaTripleOpen i j l) :=
  (relResAlgHom C R h).toRingHom.toAlgebra

/-- Triple theta sections, restricted to the pairwise section ring. -/
@[reducible]
noncomputable def thetaTripleSectionsOverlapModule (A : AffAdaptation D d) (a : ℕ)
    (p q i j l : D.index)
    (h : A.thetaTripleOpen i j l ≤ D.pieces p ⊓ D.pieces q) :
    Module Γ(relCurve C R, D.pieces p ⊓ D.pieces q)
      (A.ThetaTripleSections (π := π) a i j l) :=
  letI := A.thetaTripleSectionsModule (π := π) a i j l
  Module.compHom _ (relResAlgHom C R h).toRingHom

/-- The section-ring scalar tower on triple theta sections. -/
@[reducible]
noncomputable def thetaTripleSectionsOverlapTower (A : AffAdaptation D d) (a : ℕ)
    (p q i j l : D.index)
    (h : A.thetaTripleOpen i j l ≤ D.pieces p ⊓ D.pieces q) :
    letI : Algebra Γ(relCurve C R, D.pieces p ⊓ D.pieces q)
        Γ(relCurve C R, A.thetaTripleOpen i j l) :=
      A.overlapSectionsToTripleAlgebra p q i j l h
    letI : Module Γ(relCurve C R, D.pieces p ⊓ D.pieces q)
        (A.ThetaTripleSections (π := π) a i j l) :=
      A.thetaTripleSectionsOverlapModule (π := π) a p q i j l h
    IsScalarTower Γ(relCurve C R, D.pieces p ⊓ D.pieces q)
      Γ(relCurve C R, A.thetaTripleOpen i j l)
      (A.ThetaTripleSections (π := π) a i j l) :=
  by
    letI := A.overlapSectionsToTripleAlgebra p q i j l h
    letI := A.thetaTripleSectionsOverlapModule (π := π) a p q i j l h
    exact IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- Pair-to-triple restriction as a linear map over the pairwise section ring. -/
noncomputable def thetaOverlapSectionsToTripleLinearRing
    (A : AffAdaptation D d) (a : ℕ) (p q i j l : D.index)
    (h : A.thetaTripleOpen i j l ≤ D.pieces p ⊓ D.pieces q) :
    letI : Module Γ(relCurve C R, D.pieces p ⊓ D.pieces q)
        (A.ThetaTripleSections (π := π) a i j l) :=
      A.thetaTripleSectionsOverlapModule (π := π) a p q i j l h
    A.ThetaOverlapSections (π := π) a p q
      →ₗ[Γ(relCurve C R, D.pieces p ⊓ D.pieces q)]
        A.ThetaTripleSections (π := π) a i j l :=
  by
    letI := A.thetaTripleSectionsOverlapModule (π := π) a p q i j l h
    exact
      { toFun := A.thetaOverlapSectionsToTriple (π := π) a p q i j l h
        map_add' :=
          (A.thetaOverlapSectionsToTriple (π := π) a p q i j l h).map_add
        map_smul' :=
          (A.thetaOverlapSectionsToTriple (π := π) a p q i j l h).map_smulₛₗ }

/-- Affine restriction of theta sections from a pair to a triple is base change. -/
theorem isBaseChange_thetaOverlapSectionsToTripleLinearRing
    (A : AffAdaptation D d) (a : ℕ) (p q i j l : D.index)
    (h : A.thetaTripleOpen i j l ≤ D.pieces p ⊓ D.pieces q) :
    letI : Algebra Γ(relCurve C R, D.pieces p ⊓ D.pieces q)
        Γ(relCurve C R, A.thetaTripleOpen i j l) :=
      A.overlapSectionsToTripleAlgebra p q i j l h
    letI : Module Γ(relCurve C R, D.pieces p ⊓ D.pieces q)
        (A.ThetaTripleSections (π := π) a i j l) :=
      A.thetaTripleSectionsOverlapModule (π := π) a p q i j l h
    letI : IsScalarTower Γ(relCurve C R, D.pieces p ⊓ D.pieces q)
        Γ(relCurve C R, A.thetaTripleOpen i j l)
        (A.ThetaTripleSections (π := π) a i j l) :=
      A.thetaTripleSectionsOverlapTower (π := π) a p q i j l h
    IsBaseChange Γ(relCurve C R, A.thetaTripleOpen i j l)
      (A.thetaOverlapSectionsToTripleLinearRing (π := π) a p q i j l h) := by
  letI := A.overlapSectionsToTripleAlgebra p q i j l h
  letI := A.thetaTripleSectionsOverlapModule (π := π) a p q i j l h
  letI := A.thetaTripleSectionsOverlapTower (π := π) a p q i j l h
  let MP := A.thetaOverlapSectionsModel (π := π) a p q
  let MT := A.thetaTripleSectionsModel (π := π) a i j l
  let F := thetaChartDatum C R π a
  letI := MP.qcoh
  letI : Module Γ(relCurve C R, D.pieces p ⊓ D.pieces q)
      (F.sheaf.obj.obj (op (D.pieces p ⊓ D.pieces q))) :=
    Scheme.QcohOn.moduleOfLE (F := F.sheaf)
      (le_refl (D.pieces p ⊓ D.pieces q))
  letI := MT.qcoh
  letI : Module Γ(relCurve C R, A.thetaTripleOpen i j l)
      (F.sheaf.obj.obj (op (A.thetaTripleOpen i j l))) :=
    Scheme.QcohOn.moduleOfLE (F := F.sheaf)
      (le_refl (A.thetaTripleOpen i j l))
  have hbij := F.affineSectionsBaseChange_bijective
    (D.hasAffineOverlaps_of_isProper p q)
    (A.isAffineOpen_thetaTripleOpen i j l) h MP MT
  apply IsBaseChange.of_equiv
    (LinearEquiv.ofBijective (F.affineSectionsBaseChange h MP MT) hbij)
  intro x
  change F.affineSectionsBaseChange h MP MT (1 ⊗ₜ x) =
    A.thetaOverlapSectionsToTriple (π := π) a p q i j l h x
  rw [F.affineSectionsBaseChange_tmul, one_smul]
  rfl

/-- Tensoring triple theta sections with the triple quotient ring is the intrinsic triple
theta quotient. -/
noncomputable def thetaTripleRestrictionEquivColength
    (A : AffAdaptation D d) (a : ℕ) (i j l : D.index) :
    A.tripleColength i j l ⊗[Γ(relCurve C R, A.thetaTripleOpen i j l)]
        A.ThetaTripleSections (π := π) a i j l
      ≃ₗ[A.tripleColength i j l]
        A.ThetaTripleQuotient (π := π) a i j l := by
  let e := TensorProduct.quotTensorEquivQuotSMul
    (A.ThetaTripleSections (π := π) a i j l) (A.thetaTripleIdeal i j l)
  refine
    { __ := e.toEquiv
      map_add' := e.map_add
      map_smul' := fun c x => ?_ }
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  change e (r • x) = r • e x
  exact e.map_smul r x

/-- Quotienting triple theta sections by the intrinsic divisor ideal is base change. -/
noncomputable def thetaTripleQuotientMkLinear
    (A : AffAdaptation D d) (a : ℕ) (i j l : D.index) :
    A.ThetaTripleSections (π := π) a i j l
      →ₗ[Γ(relCurve C R, A.thetaTripleOpen i j l)]
        A.ThetaTripleQuotient (π := π) a i j l :=
  (A.thetaTripleVanishing (π := π) a i j l).mkQ

theorem isBaseChange_thetaTripleQuotientMkLinear
    (A : AffAdaptation D d) (a : ℕ) (i j l : D.index) :
    IsBaseChange (A.tripleColength i j l)
      (A.thetaTripleQuotientMkLinear (π := π) a i j l) := by
  apply IsBaseChange.of_equiv
    (A.thetaTripleRestrictionEquivColength (π := π) a i j l)
  intro x
  change TensorProduct.quotTensorEquivQuotSMul
      (A.ThetaTripleSections (π := π) a i j l) (A.thetaTripleIdeal i j l)
      (1 ⊗ₜ x) = Submodule.Quotient.mk x
  exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul _ x

/-- Restriction and reduction modulo the intrinsic triple ideal on coordinate rings. -/
noncomputable def ovlToTriple (A : AffAdaptation D d) (p q i j l : D.index)
    (h : A.thetaTripleOpen i j l ≤ D.pieces p ⊓ D.pieces q) :
    A.ovlColength p q →ₐ[R] A.tripleColength i j l :=
  Ideal.Quotient.liftₐ (A.ovlIdeal p q)
    ((Ideal.Quotient.mkₐ R (A.thetaTripleIdeal i j l)).comp (relResAlgHom C R h))
    (by
      intro r hr
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact A.relRes_mem_thetaTripleIdeal_of_mem_ovlIdeal p q i j l h r hr)

@[simp]
theorem ovlToTriple_mk (A : AffAdaptation D d) (p q i j l : D.index)
    (h : A.thetaTripleOpen i j l ≤ D.pieces p ⊓ D.pieces q)
    (r : Γ(relCurve C R, D.pieces p ⊓ D.pieces q)) :
    A.ovlToTriple p q i j l h (Ideal.Quotient.mk (A.ovlIdeal p q) r) =
      Ideal.Quotient.mk (A.thetaTripleIdeal i j l) (relResAlgHom C R h r) :=
  rfl

/-- The triple colength algebra over its first pairwise colength algebra. -/
@[reducible]
noncomputable def overlap12ToTripleAlgebra (A : AffAdaptation D d)
    (i j l : D.index) :
    Algebra (A.ovlColength i j) (A.tripleColength i j l) :=
  (A.ovlToTriple i j i j l (A.thetaTripleOpen_le_pair12 i j l)).toRingHom.toAlgebra

attribute [local instance] overlap12ToTripleAlgebra

/-- The composite algebra from the first pair's section ring to the triple colength. -/
@[reducible]
noncomputable def overlap12SectionsToTripleColengthAlgebra
    (A : AffAdaptation D d) (i j l : D.index) :
    Algebra Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.tripleColength i j l) :=
  ((A.ovlToTriple i j i j l (A.thetaTripleOpen_le_pair12 i j l)).toRingHom.comp
    (Ideal.Quotient.mk (A.ovlIdeal i j))).toAlgebra

attribute [local instance] overlap12SectionsToTripleColengthAlgebra

/-- The section-ring/pair-colength/triple-colength scalar tower. -/
@[reducible]
noncomputable def overlap12SectionsColengthTripleTower
    (A : AffAdaptation D d) (i j l : D.index) :
    IsScalarTower Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ovlColength i j) (A.tripleColength i j l) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] overlap12SectionsColengthTripleTower

/-- The triple theta quotient as a module over its first pairwise colength algebra. -/
@[reducible]
noncomputable def thetaTripleQuotientOverlap12Module
    (A : AffAdaptation D d) (a : ℕ) (i j l : D.index) :
    Module (A.ovlColength i j) (A.ThetaTripleQuotient (π := π) a i j l) :=
  Module.compHom _
    (A.ovlToTriple i j i j l (A.thetaTripleOpen_le_pair12 i j l)).toRingHom

attribute [local instance] thetaTripleQuotientOverlap12Module

/-- The same target restricted to the pairwise section ring. -/
@[reducible]
noncomputable def thetaTripleQuotientOverlap12SectionsModule
    (A : AffAdaptation D d) (a : ℕ) (i j l : D.index) :
    Module Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ThetaTripleQuotient (π := π) a i j l) :=
  Module.compHom _ (Ideal.Quotient.mk (A.ovlIdeal i j))

attribute [local instance] thetaTripleQuotientOverlap12SectionsModule

@[reducible]
noncomputable def overlap12SectionsColengthThetaTripleTower
    (A : AffAdaptation D d) (a : ℕ) (i j l : D.index) :
    IsScalarTower Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ovlColength i j) (A.ThetaTripleQuotient (π := π) a i j l) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] overlap12SectionsColengthThetaTripleTower

@[reducible]
noncomputable def overlap12TripleColengthThetaTripleTower
    (A : AffAdaptation D d) (a : ℕ) (i j l : D.index) :
    IsScalarTower (A.ovlColength i j) (A.tripleColength i j l)
      (A.ThetaTripleQuotient (π := π) a i j l) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] overlap12TripleColengthThetaTripleTower

@[reducible]
noncomputable def thetaOverlapToTriple12CompatibleSMul
    (A : AffAdaptation D d) (a : ℕ) (i j l : D.index) :
    LinearMap.CompatibleSMul
      (A.ThetaOverlapQuotient (π := π) a i j)
      (A.ThetaTripleQuotient (π := π) a i j l)
      Γ(relCurve C R, D.pieces i ⊓ D.pieces j) (A.ovlColength i j) where
  map_smul f r x := by
    change f (Ideal.Quotient.mk (A.ovlIdeal i j) r • x) =
      A.ovlToTriple i j i j l (A.thetaTripleOpen_le_pair12 i j l)
          (Ideal.Quotient.mk (A.ovlIdeal i j) r) • f x
    exact f.map_smul _ x

attribute [local instance] thetaOverlapToTriple12CompatibleSMul

/-- First-pair-to-triple restriction, linear over the pairwise colength algebra. -/
noncomputable def thetaOverlapToTriple12LinearColength
    (A : AffAdaptation D d) (a : ℕ) (i j l : D.index) :
    A.ThetaOverlapQuotient (π := π) a i j →ₗ[A.ovlColength i j]
      A.ThetaTripleQuotient (π := π) a i j l :=
  { toFun := A.thetaOverlapToTriple (π := π) a i j i j l
      (A.thetaTripleOpen_le_pair12 i j l)
    map_add' := (A.thetaOverlapToTriple (π := π) a i j i j l
      (A.thetaTripleOpen_le_pair12 i j l)).map_add
    map_smul' := fun c x => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
      change A.thetaOverlapToTriple (π := π) a i j i j l
          (A.thetaTripleOpen_le_pair12 i j l) (r • x) =
        relResAlgHom C R (A.thetaTripleOpen_le_pair12 i j l) r •
          A.thetaOverlapToTriple (π := π) a i j i j l
            (A.thetaTripleOpen_le_pair12 i j l) x
      exact (A.thetaOverlapToTriple (π := π) a i j i j l
        (A.thetaTripleOpen_le_pair12 i j l)).map_smulₛₗ r x }

/-- Restriction from the first pairwise theta quotient to the triple quotient is base
change. -/
theorem isBaseChange_thetaOverlapToTriple12LinearColength
    (A : AffAdaptation D d) (a : ℕ) (i j l : D.index) :
    IsBaseChange (A.tripleColength i j l)
      (A.thetaOverlapToTriple12LinearColength (π := π) a i j l) := by
  let h12 := A.thetaTripleOpen_le_pair12 i j l
  letI := A.overlapSectionsToTripleAlgebra i j i j l h12
  letI := A.thetaTripleSectionsOverlapModule (π := π) a i j i j l h12
  letI := A.thetaTripleSectionsOverlapTower (π := π) a i j i j l h12
  have hcomp : IsBaseChange (A.tripleColength i j l)
      (((A.thetaTripleQuotientMkLinear (π := π) a i j l).restrictScalars
          Γ(relCurve C R, D.pieces i ⊓ D.pieces j)).comp
        (A.thetaOverlapSectionsToTripleLinearRing (π := π) a i j i j l
          (A.thetaTripleOpen_le_pair12 i j l))) :=
    IsBaseChange.comp
      (A.isBaseChange_thetaOverlapSectionsToTripleLinearRing
        (π := π) a i j i j l (A.thetaTripleOpen_le_pair12 i j l))
      (A.isBaseChange_thetaTripleQuotientMkLinear (π := π) a i j l)
  have heq :
      ((A.thetaOverlapToTriple12LinearColength (π := π) a i j l).restrictScalars
          Γ(relCurve C R, D.pieces i ⊓ D.pieces j)).comp
        (A.thetaOverlapQuotientMkLinear (π := π) a i j) =
      ((A.thetaTripleQuotientMkLinear (π := π) a i j l).restrictScalars
          Γ(relCurve C R, D.pieces i ⊓ D.pieces j)).comp
        (A.thetaOverlapSectionsToTripleLinearRing (π := π) a i j i j l
          (A.thetaTripleOpen_le_pair12 i j l)) := by
    apply LinearMap.ext
    intro x
    rfl
  rw [← heq] at hcomp
  exact IsBaseChange.of_comp
    (A.isBaseChange_thetaOverlapQuotientMkLinear (π := π) a i j) hcomp

/-- The first pairwise theta quotient base-changed to the triple is the intrinsic triple
quotient. -/
noncomputable def thetaOverlap12BaseChangeToTripleEquiv
    (A : AffAdaptation D d) (a : ℕ) (i j l : D.index) :
    A.tripleColength i j l ⊗[A.ovlColength i j]
        A.ThetaOverlapQuotient (π := π) a i j
      ≃ₗ[A.tripleColength i j l]
        A.ThetaTripleQuotient (π := π) a i j l :=
  (A.isBaseChange_thetaOverlapToTriple12LinearColength (π := π) a i j l).equiv

@[simp]
theorem thetaOverlap12BaseChangeToTripleEquiv_tmul
    (A : AffAdaptation D d) (a : ℕ) (i j l : D.index)
    (c : A.tripleColength i j l)
    (x : A.ThetaOverlapQuotient (π := π) a i j) :
    A.thetaOverlap12BaseChangeToTripleEquiv (π := π) a i j l (c ⊗ₜ x) =
      c • A.thetaOverlapToTriple (π := π) a i j i j l
        (A.thetaTripleOpen_le_pair12 i j l) x :=
  IsBaseChange.equiv_tmul _ c x

end AffAdaptation

end AlgebraicGeometry
