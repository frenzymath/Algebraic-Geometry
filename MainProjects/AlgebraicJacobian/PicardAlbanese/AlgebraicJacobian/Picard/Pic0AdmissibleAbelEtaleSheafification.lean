/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelKernel
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.RegularEpi

/-!
# The admissible Abel map after big-etale sheafification

The big etale site of `Scheme.{u}` requires type-valued sheafification in `Type (u + 1)`.
This module therefore applies `ULift` to the concrete admissible Abel transformation before
sheafifying it. Subcanonicity identifies the sheafified source with the actual representable
Yoneda sheaf of `divRepAffAdmissibleScheme C`.

The target here is deliberately the etale sheafification of `pic0SigmaFunctor C`; identifying
it with the original Picard functor is a separate mathematical step. The categorical image
of the Abel map is the effective quotient of its kernel pair in the category of etale sheaves.
No Scheme representability conclusion is asserted in this module.
-/

set_option autoImplicit false

universe u v w w'

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {X : Type u} [Category.{v} X] (J : GrothendieckTopology X)

/-- Local surjectivity of a type-valued presheaf map survives a universe lift. -/
theorem isLocallySurjective_whiskerRight_ulift
    {F G : Xᵒᵖ ⥤ Type w} (f : F ⟶ G)
    [IsLocallySurjective J f] :
    IsLocallySurjective J
      (Functor.whiskerRight f uliftFunctor.{w', w}) := by
  constructor
  intro U s
  apply J.superset_covering _ (imageSieve_mem J f s.down)
  intro V i hi
  obtain ⟨t, ht⟩ := hi
  refine ⟨ULift.up t, ?_⟩
  apply ULift.ext
  exact ht

end CategoryTheory.Presheaf

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra

/-! ## Subcanonicity of the big etale site -/

/-- The big etale topology on schemes is subcanonical. -/
instance Scheme.subcanonical_etaleTopology : Scheme.etaleTopology.{u}.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_le Scheme.etaleTopology_le_proetaleTopology

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

/-! ## The sheafified concrete Abel map -/

/-- The big-etale sheafification of the universe-raised Picard Sigma presheaf. -/
noncomputable abbrev pic0SigmaEtaleSheafification :
    Sheaf Scheme.etaleTopology.{u} (Type (u + 1)) :=
  (presheafToSheaf Scheme.etaleTopology (Type (u + 1))).obj
    (pic0SigmaFunctor C ⋙ uliftFunctor.{u + 1})

/-- Subcanonicity identifies the universe-raised Yoneda sheaf of the admissible divisor
representer with the sheafification of its underlying representable presheaf. -/
noncomputable def admissibleAbelEtaleSourceIso :
    Scheme.etaleTopology.uliftYoneda.{u + 1}.obj
        (divRepAffAdmissibleScheme C).left ≅
      (presheafToSheaf Scheme.etaleTopology (Type (u + 1))).obj
        (yoneda.obj (divRepAffAdmissibleScheme C).left ⋙ uliftFunctor.{u + 1}) :=
  (asIso ((sheafificationAdjunction Scheme.etaleTopology (Type (u + 1))).counit.app
    (Scheme.etaleTopology.uliftYoneda.{u + 1}.obj
      (divRepAffAdmissibleScheme C).left))).symm

/-- The concrete admissible Abel transformation as a morphism from its representable
big-etale Yoneda source to the sheafification of the Picard Sigma presheaf. -/
noncomputable def admissibleAbelEtaleSheafMap :
    Scheme.etaleTopology.uliftYoneda.{u + 1}.obj
        (divRepAffAdmissibleScheme C).left ⟶
      pic0SigmaEtaleSheafification C :=
  (admissibleAbelEtaleSourceIso C).hom ≫
    (presheafToSheaf Scheme.etaleTopology (Type (u + 1))).map
      (Functor.whiskerRight (abelSigmaChartAffAdmissible C) uliftFunctor.{u + 1})

@[simp]
theorem admissibleAbelEtaleSourceIso_hom :
    (admissibleAbelEtaleSourceIso C).hom.hom =
      toSheafify Scheme.etaleTopology
        (yoneda.obj (divRepAffAdmissibleScheme C).left ⋙
          uliftFunctor.{u + 1}) := by
  change ((sheafToPresheaf _ _).map (inv
    ((sheafificationAdjunction _ _).counit.app
      (Scheme.etaleTopology.uliftYoneda.{u + 1}.obj
        (divRepAffAdmissibleScheme C).left)))) = _
  rw [Functor.map_inv]
  change _ = (sheafificationAdjunction Scheme.etaleTopology
    (Type (u + 1))).unit.app
      ((Scheme.etaleTopology.uliftYoneda.{u + 1}.obj
        (divRepAffAdmissibleScheme C).left).obj)
  exact (sheafificationAdjunction Scheme.etaleTopology
    (Type (u + 1))).inv_counit_map

@[simp]
theorem admissibleAbelEtaleSheafMap_app_up
    {T : Over (Spec (.of k))}
    (q : T ⟶ divRepAffAdmissibleScheme C) :
    (admissibleAbelEtaleSheafMap C).hom.app (op T.left)
        (ULift.up q.left) =
      (toSheafify Scheme.etaleTopology
        (pic0SigmaFunctor C ⋙ uliftFunctor.{u + 1})).app (op T.left)
        (ULift.up ((abelSigmaChartAffAdmissible C).app
          (op T.left) q.left)) := by
  change (((admissibleAbelEtaleSourceIso C).hom.hom ≫
    sheafifyMap Scheme.etaleTopology
      (Functor.whiskerRight (abelSigmaChartAffAdmissible C)
        uliftFunctor.{u + 1})).app _ _) = _
  rw [admissibleAbelEtaleSourceIso_hom]
  have happ := congrArg
    (fun g => g (ULift.up q.left :
      (yoneda.obj (divRepAffAdmissibleScheme C).left ⋙
        uliftFunctor.{u + 1}).obj (op T.left)))
    (NatTrans.congr_app
      (toSheafify_naturality Scheme.etaleTopology
        (Functor.whiskerRight (abelSigmaChartAffAdmissible C)
          uliftFunctor.{u + 1}))
      (op T.left))
  exact happ.symm.trans (by rfl)

/-- Two admissible divisor points have the same sheafified Abel image exactly when their raw
Abel values agree on an etale covering sieve. -/
theorem admissibleAbelEtaleSheafMap_app_eq_iff_equalizerSieve_mem
    {T : Over (Spec (.of k))}
    (q₁ q₂ : T ⟶ divRepAffAdmissibleScheme C) :
    (admissibleAbelEtaleSheafMap C).hom.app (op T.left)
        (ULift.up q₁.left) =
      (admissibleAbelEtaleSheafMap C).hom.app (op T.left)
        (ULift.up q₂.left) ↔
    Presheaf.equalizerSieve
      (F := pic0SigmaFunctor C ⋙ uliftFunctor.{u + 1})
      (ULift.up ((abelSigmaChartAffAdmissible C).app
        (op T.left) q₁.left))
      (ULift.up ((abelSigmaChartAffAdmissible C).app
        (op T.left) q₂.left)) ∈ Scheme.etaleTopology T.left := by
  rw [admissibleAbelEtaleSheafMap_app_up,
    admissibleAbelEtaleSheafMap_app_up]
  constructor
  · intro h
    exact Presheaf.equalizerSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology
        (pic0SigmaFunctor C ⋙ uliftFunctor.{u + 1})) _ _ h
  · intro h
    apply (((isSheaf_iff_isSheaf_of_type Scheme.etaleTopology
      (pic0SigmaEtaleSheafification C).obj).1
        (pic0SigmaEtaleSheafification C).property).isSeparated _ h).ext
    intro Y f hf
    simpa only [NatTrans.naturality_apply] using
      congrArg ((toSheafify Scheme.etaleTopology
        (pic0SigmaFunctor C ⋙ uliftFunctor.{u + 1})).app (op Y)) hf

/-- On every arrow into the test scheme, membership in the raw Abel kernel sieve is precisely
the concrete relative linear-equivalence condition, including the quotient by `picFromBase`. -/
theorem admissibleAbelEtaleRawKernelSieve_apply_iff_forall_picClass_div_mem_picFromBase
    {T : Over (Spec (.of k))}
    (q₁ q₂ : T ⟶ divRepAffAdmissibleScheme C)
    {Y : Scheme} (f : Y ⟶ T.left) :
    Presheaf.equalizerSieve
      (F := pic0SigmaFunctor C ⋙ uliftFunctor.{u + 1})
      (X := op T.left)
      (ULift.up ((abelSigmaChartAffAdmissible C).app
        (op T.left) q₁.left) :
          (pic0SigmaFunctor C ⋙ uliftFunctor.{u + 1}).obj (op T.left))
      (ULift.up ((abelSigmaChartAffAdmissible C).app
        (op T.left) q₂.left) :
          (pic0SigmaFunctor C ⋙ uliftFunctor.{u + 1}).obj (op T.left)) f ↔
      let T_f : Over (Spec (.of k)) := Over.mk (f ≫ T.hom)
      let e_f : T_f ⟶ T := Over.homMk f rfl
      let q₁' : T_f ⟶ divRepAffAdmissibleScheme C := e_f ≫ q₁
      let q₂' : T_f ⟶ divRepAffAdmissibleScheme C := e_f ≫ q₂
      ∀ U : T_f.left.affineOpens,
        (((divFunctorAff_admissible_representableBy C).homEquiv q₁').1 U).picClass /
            (((divFunctorAff_admissible_representableBy C).homEquiv q₂').1 U).picClass
          ∈ picFromBase C (overSpec k Γ(T_f.left, U.1)) := by
  let T_f : Over (Spec (.of k)) := Over.mk (f ≫ T.hom)
  let e_f : T_f ⟶ T := Over.homMk f rfl
  let q₁' : T_f ⟶ divRepAffAdmissibleScheme C := e_f ≫ q₁
  let q₂' : T_f ⟶ divRepAffAdmissibleScheme C := e_f ≫ q₂
  change (Presheaf.equalizerSieve
      (F := pic0SigmaFunctor C ⋙ uliftFunctor.{u + 1})
      (X := op T.left) _ _) f ↔
    ∀ U : T_f.left.affineOpens,
      (((divFunctorAff_admissible_representableBy C).homEquiv q₁').1 U).picClass /
          (((divFunctorAff_admissible_representableBy C).homEquiv q₂').1 U).picClass
        ∈ picFromBase C (overSpec k Γ(T_f.left, U.1))
  have hnat₁ := NatTrans.naturality_apply
    (abelSigmaChartAffAdmissible C) f.op q₁.left
  have hnat₂ := NatTrans.naturality_apply
    (abelSigmaChartAffAdmissible C) f.op q₂.left
  have hpull₁ :
      (pic0SigmaFunctor C).map f.op
          ((abelSigmaChartAffAdmissible C).app (op T.left) q₁.left) =
        (abelSigmaChartAffAdmissible C).app (op Y) q₁'.left := by
    exact hnat₁.symm
  have hpull₂ :
      (pic0SigmaFunctor C).map f.op
          ((abelSigmaChartAffAdmissible C).app (op T.left) q₂.left) =
        (abelSigmaChartAffAdmissible C).app (op Y) q₂'.left := by
    exact hnat₂.symm
  change ULift.up ((pic0SigmaFunctor C).map f.op
      ((abelSigmaChartAffAdmissible C).app (op T.left) q₁.left)) =
    ULift.up ((pic0SigmaFunctor C).map f.op
      ((abelSigmaChartAffAdmissible C).app (op T.left) q₂.left)) ↔ _
  rw [ULift.up_inj, hpull₁, hpull₂]
  exact
    abelSigmaChartAffAdmissible_app_left_eq_iff_forall_picClass_div_mem_picFromBase
      C q₁' q₂'

/-! ## The effective image quotient in etale sheaves -/

/-- The image sheaf of the concrete admissible Abel map. -/
noncomputable abbrev admissibleAbelEtaleImage :
    Sheaf Scheme.etaleTopology.{u} (Type (u + 1)) :=
  Sheaf.image (admissibleAbelEtaleSheafMap C)

/-- The canonical epimorphism from the admissible divisor source to the Abel image sheaf. -/
noncomputable abbrev admissibleAbelEtaleToImage :
    Scheme.etaleTopology.uliftYoneda.{u + 1}.obj
        (divRepAffAdmissibleScheme C).left ⟶
      admissibleAbelEtaleImage C :=
  Sheaf.toImage (admissibleAbelEtaleSheafMap C)

/-- The kernel pair of the map onto the Abel image is the pullback kernel pair of the original
concrete Abel sheaf map. -/
noncomputable def admissibleAbelEtaleImageKernelPair :
    IsKernelPair (admissibleAbelEtaleToImage C)
      (pullback.fst (admissibleAbelEtaleSheafMap C)
        (admissibleAbelEtaleSheafMap C))
      (pullback.snd (admissibleAbelEtaleSheafMap C)
        (admissibleAbelEtaleSheafMap C)) := by
  have hbig : IsKernelPair
      (admissibleAbelEtaleToImage C ≫
        Sheaf.imageι (admissibleAbelEtaleSheafMap C))
      (pullback.fst (admissibleAbelEtaleSheafMap C)
        (admissibleAbelEtaleSheafMap C))
      (pullback.snd (admissibleAbelEtaleSheafMap C)
        (admissibleAbelEtaleSheafMap C)) := by
    rw [Sheaf.toImage_ι]
    exact IsKernelPair.of_hasPullback (admissibleAbelEtaleSheafMap C)
  exact hbig.cancel_right_of_mono

/-- The Abel image sheaf is the effective coequalizer of the original concrete Abel kernel
pair. This is the sheaf-level quotient; representability of the relation and quotient by
schemes is a separate step. -/
noncomputable def admissibleAbelEtaleImageCoequalizer :
    IsColimit (Cofork.ofπ (admissibleAbelEtaleToImage C)
      (admissibleAbelEtaleImageKernelPair C).w) := by
  haveI : IsRegularEpi (admissibleAbelEtaleToImage C) :=
    IsRegularEpiCategory.regularEpiOfEpi _
  exact (admissibleAbelEtaleImageKernelPair C).toCoequalizer'

end AlgebraicGeometry
