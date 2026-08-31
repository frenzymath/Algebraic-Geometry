/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0SepClosedRepresentable
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjective
import AlgebraicJacobian.Picard.Pic0AdmissibleDivisorQuasiProjective
import AlgebraicJacobian.Picard.CompactImageQc
import AlgebraicJacobian.Picard.JacobianDataHandoff

/-!
# The separably closed Picard representer as Jacobian data

The admissible Abel chart is etale-locally surjective onto the exact representing
scheme obtained from the separably closed Picard construction.  Its quasi-compact
divisor source therefore supplies quasi-compactness of that exact carrier, which
packages into `PicRepDatum` and then `JacobianData` without changing the carrier or
its representation.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k]

noncomputable section

/-- Etale-local surjectivity of a Yoneda map is surjectivity on the underlying points. -/
theorem surjective_of_isLocallySurjective_yoneda_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : Presheaf.IsLocallySurjective Scheme.etaleTopology (yoneda.map f)) :
    Function.Surjective f.base := by
  intro y
  let s : ToType ((yoneda.obj Y).obj (op (Spec (Y.residueField y)))) :=
    Y.fromSpecResidueField y
  have hmem := h.imageSieve_mem s
  obtain ⟨cover, hcover⟩ :=
    (Scheme.mem_grothendieckTopology_iff (P := @Etale)).mp hmem
  obtain ⟨r⟩ := (inferInstance : Nonempty (PrimeSpectrum (Y.residueField y)))
  obtain ⟨i, z, hz⟩ := cover.exists_eq r
  have hi : (Presieve.ofArrows cover.X cover.f) (cover.f i) := ⟨i⟩
  obtain ⟨q, hq⟩ := hcover (cover.X i) (cover.f i) hi
  change q ≫ f = cover.f i ≫ Y.fromSpecResidueField y at hq
  refine ⟨q.base z, ?_⟩
  have hqz := congrArg (fun g : cover.X i ⟶ Y => g.base z) hq
  change f.base (q.base z) = (Y.fromSpecResidueField y).base ((cover.f i).base z) at hqz
  rw [hz, Scheme.fromSpecResidueField_apply] at hqz
  exact hqz

/-- The admissible Abel chart, viewed as a scheme morphism to the exact separably closed
Picard representing scheme. -/
noncomputable def abelToPic0SepClosedRepresenter (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] [IsSepClosed k] :
    (divRepAffAdmissibleScheme C).left ⟶ (pic0_sepClosed_representableBy (C := C)).1.left :=
  yoneda.preimage (abelSigmaChartAffAdmissible C ≫
    (representableBySigmaIso (pic0_sepClosed_representableBy (C := C)).2).inv)

/-- The Yoneda map of the represented Abel morphism is the admissible Abel chart after
identifying the exact representing carrier with its sigma extension. -/
theorem yoneda_map_abelToPic0SepClosedRepresenter (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] [IsSepClosed k] :
    yoneda.map (abelToPic0SepClosedRepresenter C) =
      abelSigmaChartAffAdmissible C ≫
        (representableBySigmaIso (pic0_sepClosed_representableBy (C := C)).2).inv :=
  yoneda.map_preimage _

/-- The Abel morphism to the exact separably closed Picard representer is etale-locally
surjective. -/
theorem isLocallySurjective_abelToPic0SepClosedRepresenter (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] [IsSepClosed k] :
    Presheaf.IsLocallySurjective Scheme.etaleTopology
      (yoneda.map (abelToPic0SepClosedRepresenter C)) := by
  rw [yoneda_map_abelToPic0SepClosedRepresenter]
  letI : Presheaf.IsLocallySurjective Scheme.etaleTopology
      (abelSigmaChartAffAdmissible C) :=
    isLocallySurjective_abelSigmaChartAffAdmissible C
  infer_instance

/-- The admissible Abel morphism is surjective on the underlying points of the exact
separably closed Picard representative. -/
theorem surjective_abelToPic0SepClosedRepresenter (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] [IsSepClosed k] :
    Function.Surjective (abelToPic0SepClosedRepresenter C).base :=
  surjective_of_isLocallySurjective_yoneda_map _
    (isLocallySurjective_abelToPic0SepClosedRepresenter C)

/-- The exact separably closed Picard representing scheme is quasi-compact over its field. -/
theorem quasiCompact_pic0SepClosedRepresenter (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] [IsSepClosed k] :
    QuasiCompact (pic0_sepClosed_representableBy (C := C)).1.hom := by
  haveI : CompactSpace (divRepAffAdmissibleScheme C).left :=
    HasAffineProperty.iff_of_isAffine.mp (quasiCompact_divRepAffAdmissibleScheme C)
  exact quasiCompact_of_surjective (abelToPic0SepClosedRepresenter C)
    (pic0_sepClosed_representableBy (C := C)).1.hom
    (surjective_abelToPic0SepClosedRepresenter C)

/-- The exact separably closed Picard representative is finitely presented over the field. -/
theorem locallyOfFinitePresentation_pic0_sepClosed_representableBy
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] [IsSepClosed k] :
    LocallyOfFinitePresentation
      (pic0_sepClosed_representableBy (C := C)).1.hom :=
  LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr
    (locallyOfFiniteType_pic0_sepClosed_representableBy (C := C))

/-- The exact separably closed Picard representing scheme is quasi-separated. -/
theorem quasiSeparatedSpace_pic0SepClosedRepresenter (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] [IsSepClosed k] :
    QuasiSeparatedSpace
      (pic0_sepClosed_representableBy (C := C)).1.left := by
  letI : LocallyOfFiniteType
      (pic0_sepClosed_representableBy (C := C)).1.hom :=
    locallyOfFiniteType_pic0_sepClosed_representableBy (C := C)
  letI : IsLocallyNoetherian
      (pic0_sepClosed_representableBy (C := C)).1.left :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pic0_sepClosed_representableBy (C := C)).1.hom
  infer_instance

/-- The separably closed representability theorem, recorded in the finite-level Picard datum
shape at the same field. -/
noncomputable def picRepDatumSepClosed (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] [IsSepClosed k] : PicRepDatum k k C where
  J := (pic0_sepClosed_representableBy (C := C)).1
  rep := (pic0_sepClosed_representableBy (C := C)).2
  lft := locallyOfFiniteType_pic0_sepClosed_representableBy (C := C)

/-- The exact separably closed Picard representative packages as Jacobian data. -/
noncomputable def jacobianDataSepClosed (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] [IsSepClosed k] : JacobianData C :=
  (picRepDatumSepClosed C).toJacobianData (quasiCompact_pic0SepClosedRepresenter C)

@[simp]
theorem picRepDatumSepClosed_J (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] [IsSepClosed k] :
    (picRepDatumSepClosed C).J = (pic0_sepClosed_representableBy (C := C)).1 :=
  rfl

@[simp]
theorem picRepDatumSepClosed_rep (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] [IsSepClosed k] :
    (picRepDatumSepClosed C).rep = (pic0_sepClosed_representableBy (C := C)).2 :=
  rfl

@[simp]
theorem jacobianDataSepClosed_J (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] [IsSepClosed k] :
    (jacobianDataSepClosed C).J = (pic0_sepClosed_representableBy (C := C)).1 :=
  rfl

@[simp]
theorem jacobianDataSepClosed_rep (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] [IsSepClosed k] :
    (jacobianDataSepClosed C).rep = (pic0_sepClosed_representableBy (C := C)).2 :=
  rfl

end

end AlgebraicGeometry
