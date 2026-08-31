/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.SemilinearAction
import AlgebraicJacobian.Picard.Pic0ThetaCocycle

/-!
# The semilinear Galois action on a Picard-zero representative

For an arbitrary extension `L/k`, a `k`-algebra automorphism of `L` twists the
structure map of every `L`-test.  Restricting that test back to `k` forgets the
twist.  Conjugating this observation by `pic0ThetaType` gives an action on the
Picard-zero functor over `L`; representability will transport it to the
representing scheme.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicJacobian.GaloisDescent

namespace AlgebraicGeometry

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- The structure morphism of the field-extension test functor. -/
noncomputable abbrev pic0GaloisBaseMap :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k L))

/-- Restriction of an `L`-test to a `k`-test. -/
noncomputable abbrev pic0GaloisRestrictTest :
    Over (Spec (CommRingCat.of L)) ⥤ Over (Spec (CommRingCat.of k)) :=
  Over.map (pic0GaloisBaseMap (k := k) (L := L))

/-- Every `k`-algebra automorphism of `L` is invisible after composing with
`Spec L ⟶ Spec k`. -/
theorem pic0Galois_baseAut_comp (gamma : L ≃ₐ[k] L) :
    (toSpecAut (L ≃ₐ[k] L) L gamma).hom ≫
        pic0GaloisBaseMap (k := k) (L := L) =
      pic0GaloisBaseMap (k := k) (L := L) := by
  rw [toSpecAut_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact gamma⁻¹.commutes x

/-- Twist `L`-tests by a `k`-algebra automorphism of `L`. -/
noncomputable abbrev pic0TwistTestFunctor (gamma : L ≃ₐ[k] L) :
    Over (Spec (CommRingCat.of L)) ⥤ Over (Spec (CommRingCat.of L)) :=
  Over.map (toSpecAut (L ≃ₐ[k] L) L gamma).hom

/-- Restriction to `k` identifies a twisted `L`-test with the original
restricted test. -/
noncomputable def pic0GaloisRestrictTwistIso (gamma : L ≃ₐ[k] L) :
    pic0TwistTestFunctor gamma ⋙
        pic0GaloisRestrictTest (k := k) (L := L) ≅
      pic0GaloisRestrictTest (k := k) (L := L) :=
  (Over.mapComp _ _).symm ≪≫
    Over.mapCongr _ _ (pic0Galois_baseAut_comp gamma)

@[simp]
theorem pic0GaloisRestrictTwistIso_hom_app_left
    (gamma : L ≃ₐ[k] L) (T : Over (Spec (CommRingCat.of L))) :
    ((pic0GaloisRestrictTwistIso gamma).hom.app T).left = 𝟙 T.left := by
  simp [pic0GaloisRestrictTwistIso, Over.mapComp, Over.mapCongr]

/-- A product twist is canonically the corresponding iterated twist. -/
noncomputable def pic0TwistTestFunctorMulIso (gamma tau : L ≃ₐ[k] L) :
    pic0TwistTestFunctor (gamma * tau) ≅
      pic0TwistTestFunctor tau ⋙ pic0TwistTestFunctor gamma :=
  Over.mapCongr _ _ (toSpecAut_mul_hom (L ≃ₐ[k] L) L gamma tau) ≪≫
    Over.mapComp _ _

@[simp]
theorem pic0TwistTestFunctorMulIso_hom_app_left
    (gamma tau : L ≃ₐ[k] L) (T : Over (Spec (CommRingCat.of L))) :
    ((pic0TwistTestFunctorMulIso gamma tau).hom.app T).left = 𝟙 T.left := by
  simp [pic0TwistTestFunctorMulIso, Over.mapComp, Over.mapCongr]

/-- The identity twist is the identity functor. -/
noncomputable def pic0TwistTestFunctorOneIso :
    pic0TwistTestFunctor (1 : L ≃ₐ[k] L) ≅ 𝟭 _ :=
  Over.mapCongr _ _ (by rw [map_one]; rfl) ≪≫ Over.mapId _

@[simp]
theorem pic0TwistTestFunctorOneIso_hom_app_left
    (T : Over (Spec (CommRingCat.of L))) :
    ((pic0TwistTestFunctorOneIso (k := k) (L := L)).hom.app T).left =
      𝟙 T.left := by
  simp [pic0TwistTestFunctorOneIso, Over.mapCongr, Over.mapId]

theorem pic0GaloisRestrictTwistIso_one_hom_app
    (T : Over (Spec (CommRingCat.of L))) :
    (pic0GaloisRestrictTwistIso (1 : L ≃ₐ[k] L)).hom.app T =
      (pic0GaloisRestrictTest (k := k) (L := L)).map
        ((pic0TwistTestFunctorOneIso (k := k) (L := L)).hom.app T) := by
  apply Over.OverMorphism.ext
  simp only [pic0GaloisRestrictTwistIso_hom_app_left, Over.map_map_left,
    pic0TwistTestFunctorOneIso_hom_app_left]

theorem pic0GaloisRestrictTwistIso_mul_hom_app
    (gamma tau : L ≃ₐ[k] L) (T : Over (Spec (CommRingCat.of L))) :
    (pic0GaloisRestrictTwistIso (gamma * tau)).hom.app T =
      (pic0GaloisRestrictTest (k := k) (L := L)).map
          ((pic0TwistTestFunctorMulIso gamma tau).hom.app T) ≫
        (pic0GaloisRestrictTwistIso gamma).hom.app
          ((pic0TwistTestFunctor tau).obj T) ≫
        (pic0GaloisRestrictTwistIso tau).hom.app T := by
  apply Over.OverMorphism.ext
  simp only [Over.map_obj_left, pic0GaloisRestrictTwistIso_hom_app_left,
    Over.comp_left, Over.map_map_left,
    pic0TwistTestFunctorMulIso_hom_app_left, Category.comp_id]
  rfl

section FunctorAction

variable (C : Over (Spec (CommRingCat.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-- The action on the `k`-Picard-zero functor restricted to `L`-tests. -/
noncomputable def pic0GaloisActionRestricted (gamma : L ≃ₐ[k] L) :
    (pic0TwistTestFunctor gamma).op ⋙
        ((pic0GaloisRestrictTest (k := k) (L := L)).op ⋙
          pic0TypeFunctor C) ≅
      (pic0GaloisRestrictTest (k := k) (L := L)).op ⋙
        pic0TypeFunctor C :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (NatIso.op (pic0GaloisRestrictTwistIso gamma)).symm
      (pic0TypeFunctor C)

theorem pic0GaloisActionRestricted_inv_app
    (gamma : L ≃ₐ[k] L) (T : Over (Spec (CommRingCat.of L))) :
    (pic0GaloisActionRestricted C gamma).inv.app (Opposite.op T) =
      (pic0TypeFunctor C).map
        ((pic0GaloisRestrictTwistIso gamma).hom.app T).op := by
  change _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

theorem pic0GaloisActionRestricted_one_inv_app
    (T : Over (Spec (CommRingCat.of L)))
    (x : ((pic0GaloisRestrictTest (k := k) (L := L)).op ⋙
      pic0TypeFunctor C).obj
      (Opposite.op T)) :
    (pic0GaloisActionRestricted C (1 : L ≃ₐ[k] L)).inv.app
        (Opposite.op T) x =
      (((pic0GaloisRestrictTest (k := k) (L := L)).op ⋙
        pic0TypeFunctor C).map
        ((pic0TwistTestFunctorOneIso (k := k) (L := L)).hom.app T).op) x := by
  rw [pic0GaloisActionRestricted_inv_app,
    pic0GaloisRestrictTwistIso_one_hom_app]
  rfl

private theorem pic0_map_op_comp_comp_apply
    {W X Y Z : Over (Spec (CommRingCat.of k))}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (x : (pic0TypeFunctor C).obj (Opposite.op Z)) :
    (pic0TypeFunctor C).map (f ≫ g ≫ h).op x =
      (pic0TypeFunctor C).map f.op
        ((pic0TypeFunctor C).map g.op ((pic0TypeFunctor C).map h.op x)) := by
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp]
  rfl

theorem pic0GaloisActionRestricted_mul_inv_app
    (gamma tau : L ≃ₐ[k] L) (T : Over (Spec (CommRingCat.of L)))
    (x : ((pic0GaloisRestrictTest (k := k) (L := L)).op ⋙
      pic0TypeFunctor C).obj
      (Opposite.op T)) :
    (pic0GaloisActionRestricted C (gamma * tau)).inv.app
        (Opposite.op T) x =
      (((pic0GaloisRestrictTest (k := k) (L := L)).op ⋙
        pic0TypeFunctor C).map
        ((pic0TwistTestFunctorMulIso gamma tau).hom.app T).op)
        ((pic0GaloisActionRestricted C gamma).inv.app
          (Opposite.op ((pic0TwistTestFunctor tau).obj T))
          ((pic0GaloisActionRestricted C tau).inv.app (Opposite.op T) x)) := by
  rw [pic0GaloisActionRestricted_inv_app,
    pic0GaloisActionRestricted_inv_app,
    pic0GaloisActionRestricted_inv_app]
  have h := congrArg (fun q => q.op)
    (pic0GaloisRestrictTwistIso_mul_hom_app gamma tau T)
  rw [h]
  change _ = (pic0TypeFunctor C).map
    (((pic0GaloisRestrictTest (k := k) (L := L)).map
      ((pic0TwistTestFunctorMulIso gamma tau).hom.app T)).op) _
  exact pic0_map_op_comp_comp_apply C
    ((pic0GaloisRestrictTest (k := k) (L := L)).map
      ((pic0TwistTestFunctorMulIso gamma tau).hom.app T))
    ((pic0GaloisRestrictTwistIso gamma).hom.app
      ((pic0TwistTestFunctor tau).obj T))
    ((pic0GaloisRestrictTwistIso tau).hom.app T) x

/-- The action on `pic0TypeFunctor` over `L`, obtained by conjugating the
restricted action with `pic0ThetaType`. -/
noncomputable def pic0GaloisAction (gamma : L ≃ₐ[k] L) :
    (pic0TwistTestFunctor gamma).op ⋙
        pic0TypeFunctor ((baseChange k L).obj C) ≅
      pic0TypeFunctor ((baseChange k L).obj C) :=
  Functor.isoWhiskerLeft _ (pic0ThetaType k L C) ≪≫
    pic0GaloisActionRestricted C gamma ≪≫
    (pic0ThetaType k L C).symm

theorem pic0GaloisAction_inv_app_apply
    (gamma : L ≃ₐ[k] L) (T : Over (Spec (CommRingCat.of L)))
    (x : (pic0TypeFunctor ((baseChange k L).obj C)).obj (Opposite.op T)) :
    (pic0GaloisAction C gamma).inv.app (Opposite.op T) x =
      (pic0ThetaType k L C).inv.app
        (Opposite.op ((pic0TwistTestFunctor gamma).obj T))
        ((pic0GaloisActionRestricted C gamma).inv.app (Opposite.op T)
          ((pic0ThetaType k L C).hom.app (Opposite.op T) x)) := by
  rfl

theorem pic0GaloisAction_mul_inv_app
    (gamma tau : L ≃ₐ[k] L) (T : Over (Spec (CommRingCat.of L)))
    (x : (pic0TypeFunctor ((baseChange k L).obj C)).obj (Opposite.op T)) :
    (pic0GaloisAction C (gamma * tau)).inv.app (Opposite.op T) x =
      (pic0TypeFunctor ((baseChange k L).obj C)).map
        ((pic0TwistTestFunctorMulIso gamma tau).hom.app T).op
        ((pic0GaloisAction C gamma).inv.app
          (Opposite.op ((pic0TwistTestFunctor tau).obj T))
          ((pic0GaloisAction C tau).inv.app (Opposite.op T) x)) := by
  simp only [pic0GaloisAction_inv_app_apply]
  rw [pic0GaloisActionRestricted_mul_inv_app]
  simp only [Iso.inv_hom_id_app_apply]
  exact NatTrans.naturality_apply (pic0ThetaType k L C).inv
    ((pic0TwistTestFunctorMulIso gamma tau).hom.app T).op _

theorem pic0GaloisAction_one_inv_app
    (T : Over (Spec (CommRingCat.of L)))
    (x : (pic0TypeFunctor ((baseChange k L).obj C)).obj (Opposite.op T)) :
    (pic0GaloisAction C (1 : L ≃ₐ[k] L)).inv.app (Opposite.op T) x =
      (pic0TypeFunctor ((baseChange k L).obj C)).map
        ((pic0TwistTestFunctorOneIso (k := k) (L := L)).hom.app T).op x := by
  rw [pic0GaloisAction_inv_app_apply,
    pic0GaloisActionRestricted_one_inv_app]
  rw [NatTrans.naturality_apply]
  change (pic0TypeFunctor ((baseChange k L).obj C)).map
    ((pic0TwistTestFunctorOneIso (k := k) (L := L)).hom.app T).op
      ((pic0ThetaType k L C).inv.app (Opposite.op T)
        ((pic0ThetaType k L C).hom.app (Opposite.op T) x)) = _
  rw [Iso.hom_inv_id_app_apply]

end FunctorAction

section RepresentativeAction

variable (C : Over (Spec (CommRingCat.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {J : Over (Spec (CommRingCat.of L))}
  (rep : (pic0TypeFunctor ((baseChange k L).obj C)).RepresentableBy J)

/-- The morphism from the twisted representing object to the original one,
obtained by applying the inverse functor action to the universal class. -/
noncomputable def pic0GaloisTwistMor (gamma : L ≃ₐ[k] L) :
    (pic0TwistTestFunctor gamma).obj J ⟶ J :=
  rep.homEquiv.symm
    ((pic0GaloisAction C gamma).inv.app (Opposite.op J)
      (rep.homEquiv (𝟙 J)))

@[simp]
theorem pic0Galois_homEquiv_twistMor (gamma : L ≃ₐ[k] L) :
    rep.homEquiv (pic0GaloisTwistMor C rep gamma) =
      (pic0GaloisAction C gamma).inv.app (Opposite.op J)
        (rep.homEquiv (𝟙 J)) :=
  Equiv.apply_symm_apply _ _

/-- The twist morphisms obey the field-automorphism group law in the slice. -/
theorem pic0GaloisTwistMor_mul (gamma tau : L ≃ₐ[k] L) :
    pic0GaloisTwistMor C rep (gamma * tau) =
      (pic0TwistTestFunctorMulIso gamma tau).hom.app J ≫
        (pic0TwistTestFunctor gamma).map
          (pic0GaloisTwistMor C rep tau) ≫
        pic0GaloisTwistMor C rep gamma := by
  apply rep.homEquiv.injective
  rw [pic0Galois_homEquiv_twistMor, rep.homEquiv_comp,
    rep.homEquiv_comp, pic0Galois_homEquiv_twistMor]
  change _ = (pic0TypeFunctor ((baseChange k L).obj C)).map
    ((pic0TwistTestFunctorMulIso gamma tau).hom.app J).op
      (((pic0TwistTestFunctor gamma).op ⋙
        pic0TypeFunctor ((baseChange k L).obj C)).map
          (pic0GaloisTwistMor C rep tau).op
          ((pic0GaloisAction C gamma).inv.app (Opposite.op J)
            (rep.homEquiv (𝟙 J))))
  rw [← NatTrans.naturality_apply (pic0GaloisAction C gamma).inv
    (pic0GaloisTwistMor C rep tau).op (rep.homEquiv (𝟙 J))]
  rw [← rep.homEquiv_eq, pic0Galois_homEquiv_twistMor]
  exact pic0GaloisAction_mul_inv_app C gamma tau J
    (rep.homEquiv (𝟙 J))

/-- The identity twist morphism is the canonical identity-twist comparison. -/
theorem pic0GaloisTwistMor_one :
    pic0GaloisTwistMor C rep (1 : L ≃ₐ[k] L) =
      (pic0TwistTestFunctorOneIso (k := k) (L := L)).hom.app J := by
  apply rep.homEquiv.injective
  rw [pic0Galois_homEquiv_twistMor]
  exact (pic0GaloisAction_one_inv_app C J (rep.homEquiv (𝟙 J))).trans
    (rep.homEquiv_eq
      ((pic0TwistTestFunctorOneIso (k := k) (L := L)).hom.app J)).symm

@[simp]
theorem pic0GaloisTwistMor_one_left :
    (pic0GaloisTwistMor C rep (1 : L ≃ₐ[k] L)).left = 𝟙 J.left := by
  rw [pic0GaloisTwistMor_one]
  exact pic0TwistTestFunctorOneIso_hom_app_left J

/-- On underlying schemes, twist morphisms multiply in the order used by
categorical automorphisms. -/
theorem pic0GaloisTwistMor_mul_left (gamma tau : L ≃ₐ[k] L) :
    (pic0GaloisTwistMor C rep (gamma * tau)).left =
      (pic0GaloisTwistMor C rep tau).left ≫
        (pic0GaloisTwistMor C rep gamma).left := by
  have h := congrArg Over.Hom.left
    (pic0GaloisTwistMor_mul C rep gamma tau)
  simp only [Over.comp_left, Over.map_map_left] at h
  let m : J.left ⟶ J.left :=
    ((pic0TwistTestFunctorMulIso gamma tau).hom.app J).left
  have hfixed : @Eq (J.left ⟶ J.left)
      ((pic0GaloisTwistMor C rep (gamma * tau)).left : J.left ⟶ J.left)
      ((m ≫ ((pic0GaloisTwistMor C rep tau).left : J.left ⟶ J.left)) ≫
        ((pic0GaloisTwistMor C rep gamma).left : J.left ⟶ J.left)) := h
  have hm : m = 𝟙 J.left := by
    dsimp only [m]
    exact pic0TwistTestFunctorMulIso_hom_app_left gamma tau J
  rw [hm, Category.id_comp] at hfixed
  exact hfixed

/-- The twist morphism covers the corresponding automorphism of `Spec L`.
This is the structure equation of the slice morphism itself. -/
theorem pic0GaloisTwistMor_compat (gamma : L ≃ₐ[k] L) :
    (pic0GaloisTwistMor C rep gamma).left ≫ J.hom =
      J.hom ≫ (toSpecAut (L ≃ₐ[k] L) L gamma).hom :=
  Over.w (pic0GaloisTwistMor C rep gamma)

/-- The twist at `gamma`, with the inverse-indexed twist as inverse. -/
noncomputable def pic0GaloisTwistAut (gamma : L ≃ₐ[k] L) : Aut J.left where
  hom := (pic0GaloisTwistMor C rep gamma).left
  inv := (pic0GaloisTwistMor C rep gamma⁻¹).left
  hom_inv_id := by
    have hfixed : @Eq (J.left ⟶ J.left)
        ((pic0GaloisTwistMor C rep (gamma⁻¹ * gamma)).left :
          J.left ⟶ J.left)
        (((pic0GaloisTwistMor C rep gamma).left : J.left ⟶ J.left) ≫
          ((pic0GaloisTwistMor C rep gamma⁻¹).left : J.left ⟶ J.left)) :=
      pic0GaloisTwistMor_mul_left C rep gamma⁻¹ gamma
    exact hfixed.symm.trans (by
      rw [inv_mul_cancel gamma]
      exact pic0GaloisTwistMor_one_left C rep)
  inv_hom_id := by
    have hfixed : @Eq (J.left ⟶ J.left)
        ((pic0GaloisTwistMor C rep (gamma * gamma⁻¹)).left :
          J.left ⟶ J.left)
        (((pic0GaloisTwistMor C rep gamma⁻¹).left : J.left ⟶ J.left) ≫
          ((pic0GaloisTwistMor C rep gamma).left : J.left ⟶ J.left)) :=
      pic0GaloisTwistMor_mul_left C rep gamma gamma⁻¹
    exact hfixed.symm.trans (by
      rw [mul_inv_cancel gamma]
      exact pic0GaloisTwistMor_one_left C rep)

/-- The canonical twists form an action on the underlying representing scheme.
-/
noncomputable def pic0GaloisTwistAction :
    (L ≃ₐ[k] L) →* Aut J.left :=
  MonoidHom.mk' (pic0GaloisTwistAut C rep) fun gamma tau => by
    apply Aut.ext
    exact pic0GaloisTwistMor_mul_left C rep gamma tau

/-- A representation of Picard zero over `L` canonically supplies the
semilinear action required by finite-Galois quotient descent.  No finiteness,
Galois, affine, or additional curve hypothesis is introduced. -/
noncomputable def pic0SemilinearGalActionOfRepresentableBy :
    SemilinearGalAction k L J.left J.hom where
  act := pic0GaloisTwistAction C rep
  compat gamma := pic0GaloisTwistMor_compat C rep gamma

end RepresentativeAction

end AlgebraicGeometry
