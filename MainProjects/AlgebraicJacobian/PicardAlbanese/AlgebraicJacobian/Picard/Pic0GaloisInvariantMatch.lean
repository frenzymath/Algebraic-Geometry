/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0GaloisInvariantComparison

/-!
# The finite-Galois invariance match for Picard zero

This module identifies deck invariance of a Picard-zero class with equivariance
of its representing morphism for the canonical semilinear Galois action.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite
open AlgebraicJacobian.GaloisDescent

namespace AlgebraicGeometry

noncomputable section

open Scheme Scheme.PicScheme

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-! ## The two slice presentations of a deck transformation -/

/-- The deck transformation of a base-changed test, packaged as a morphism in
the slice over `Spec L`. -/
noncomputable def pic0GalTwistMor
    (T : Over (Spec (CommRingCat.of K))) (gamma : L ≃ₐ[K] L) :
    (pic0TwistTestFunctor gamma).obj (baseTest (k' := L) T) ⟶
      baseTest (k' := L) T :=
  Over.homMk (pullbackGalMap K L T.hom gamma)
    (pullbackGalMap_snd K L T.hom gamma)

@[simp]
theorem pic0GalTwistMor_left
    (T : Over (Spec (CommRingCat.of K))) (gamma : L ≃ₐ[K] L) :
    (pic0GalTwistMor T gamma).left = pullbackGalMap K L T.hom gamma :=
  rfl

/-- Base change of a morphism of `K`-tests, regarded as a morphism of their
base changes over `Spec L`. -/
noncomputable def pic0GaloisBaseChangeMor
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T) :
    baseTest (k' := L) T' ⟶ baseTest (k' := L) T :=
  Over.homMk (pullbackBaseChange K L T.hom T'.hom a.left a.w)
    (pullbackBaseChange_snd K L T.hom T'.hom a.left a.w)

theorem pic0GaloisBaseTestMap_eq_restrict_map
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T) :
    pic0GaloisBaseTestMap (L := L) a =
      (pic0GaloisRestrictTest (k := K) (L := L)).map
        (pic0GaloisBaseChangeMor (L := L) a) :=
  rfl

/-- The inverse comparison from a twisted `L`-test to the original test is the
identity on underlying schemes. -/
theorem pic0GaloisRestrictTwistIso_inv_app_left
    (gamma : L ≃ₐ[K] L) (D : Over (Spec (CommRingCat.of L))) :
    ((pic0GaloisRestrictTwistIso gamma).inv.app D).left = 𝟙 D.left := by
  have h := congrArg Over.Hom.left
    ((pic0GaloisRestrictTwistIso gamma).hom_inv_id_app D)
  rw [Over.comp_left, pic0GaloisRestrictTwistIso_hom_app_left] at h
  have hfixed : @Eq (D.left ⟶ D.left)
      (𝟙 D.left ≫ ((pic0GaloisRestrictTwistIso gamma).inv.app D).left)
      (𝟙 D.left) := h
  rw [Category.id_comp] at hfixed
  exact hfixed

/-- The `K`-slice deck transformation indexed by `gamma⁻¹` is the restriction
of the `L`-slice deck transformation indexed by `gamma`, after the canonical
identity-underlying comparison of their sources. -/
theorem twistTest_eq_pic0GaloisRestrict_galTwistMor
    (T : Over (Spec (CommRingCat.of K))) (gamma : L ≃ₐ[K] L) :
    twistTest T gamma⁻¹ =
      (pic0GaloisRestrictTwistIso gamma).inv.app (baseTest (k' := L) T) ≫
        (pic0GaloisRestrictTest (k := K) (L := L)).map
          (pic0GalTwistMor T gamma) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, pic0GaloisRestrictTwistIso_inv_app_left,
    Over.map_map_left, pic0GalTwistMor_left]
  have hfixed : @Eq
      (Limits.pullback T.hom (specMapAlgebra K L) ⟶
        Limits.pullback T.hom (specMapAlgebra K L))
      (𝟙 _ ≫ pullbackGalMap K L T.hom gamma)
      (pullbackGalMap K L T.hom gamma) :=
    Category.id_comp _
  exact hfixed.symm

/-! ## Transporting deck invariance through theta -/

section ThetaAction

variable (C : Over (Spec (CommRingCat.of K)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

set_option maxHeartbeats 1000000 in
-- Normalizing both theta components and the restriction-twist inverse is expensive.
/-- The theta comparison carries invariance under the inverse-indexed deck
transformation to the canonical Galois-action equation. -/
theorem pic0_theta_invariant_iff_action
    (T : Over (Spec (CommRingCat.of K)))
    (y : (pic0TypeFunctor ((baseChange K L).obj C)).obj
      (op (baseTest (k' := L) T)))
    (gamma : L ≃ₐ[K] L) :
    (pic0TypeFunctor C).map (twistTest T gamma⁻¹).op
          ((pic0ThetaType K L C).hom.app
            (op (baseTest (k' := L) T)) y) =
        (pic0ThetaType K L C).hom.app
          (op (baseTest (k' := L) T)) y ↔
      (pic0TypeFunctor ((baseChange K L).obj C)).map
          (pic0GalTwistMor T gamma).op y =
        (pic0GaloisAction C gamma).inv.app
          (op (baseTest (k' := L) T)) y := by
  constructor
  · intro h
    rw [twistTest_eq_pic0GaloisRestrict_galTwistMor,
      op_comp, Functor.map_comp] at h
    have he : (pic0TypeFunctor C).map
          ((pic0GaloisRestrictTest (k := K) (L := L)).map
            (pic0GalTwistMor T gamma)).op
          ((pic0ThetaType K L C).hom.app
            (op (baseTest (k' := L) T)) y) =
        (pic0TypeFunctor C).map
          ((pic0GaloisRestrictTwistIso gamma).hom.app
            (baseTest (k' := L) T)).op
          ((pic0ThetaType K L C).hom.app
            (op (baseTest (k' := L) T)) y) := by
      calc
        _ = (pic0TypeFunctor C).map
            ((pic0GaloisRestrictTwistIso gamma).hom.app
              (baseTest (k' := L) T)).op
            ((pic0TypeFunctor C).map
              ((pic0GaloisRestrictTwistIso gamma).inv.app
                (baseTest (k' := L) T)).op
              ((pic0TypeFunctor C).map
                ((pic0GaloisRestrictTest (k := K) (L := L)).map
                  (pic0GalTwistMor T gamma)).op
                ((pic0ThetaType K L C).hom.app
                  (op (baseTest (k' := L) T)) y))) := by
            symm
            rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp,
              Iso.hom_inv_id_app]
            simpa using Functor.map_id_apply (pic0TypeFunctor C)
              (op ((pic0TwistTestFunctor gamma ⋙
                pic0GaloisRestrictTest).obj (baseTest (k' := L) T))) _
        _ = _ := congrArg ((pic0TypeFunctor C).map
          ((pic0GaloisRestrictTwistIso gamma).hom.app
            (baseTest (k' := L) T)).op) h
    apply (Iso.toEquiv ((pic0ThetaType K L C).app
      (op ((pic0TwistTestFunctor gamma).obj
        (baseTest (k' := L) T))))).injective
    change (pic0ThetaType K L C).hom.app
        (op ((pic0TwistTestFunctor gamma).obj (baseTest (k' := L) T)))
          ((pic0TypeFunctor ((baseChange K L).obj C)).map
            (pic0GalTwistMor T gamma).op y) =
      (pic0ThetaType K L C).hom.app
        (op ((pic0TwistTestFunctor gamma).obj (baseTest (k' := L) T)))
          ((pic0GaloisAction C gamma).inv.app
            (op (baseTest (k' := L) T)) y)
    rw [pic0GaloisAction_inv_app_apply, Iso.inv_hom_id_app_apply]
    rw [pic0GaloisActionRestricted_inv_app]
    rw [NatTrans.naturality_apply]
    exact he
  · intro h
    have htheta := congrArg ((pic0ThetaType K L C).hom.app
      (op ((pic0TwistTestFunctor gamma).obj
        (baseTest (k' := L) T)))) h
    have he : (pic0TypeFunctor C).map
          ((pic0GaloisRestrictTest (k := K) (L := L)).map
            (pic0GalTwistMor T gamma)).op
          ((pic0ThetaType K L C).hom.app
            (op (baseTest (k' := L) T)) y) =
        (pic0TypeFunctor C).map
          ((pic0GaloisRestrictTwistIso gamma).hom.app
            (baseTest (k' := L) T)).op
          ((pic0ThetaType K L C).hom.app
            (op (baseTest (k' := L) T)) y) := by
      calc
        _ = (pic0ThetaType K L C).hom.app
            (op ((pic0TwistTestFunctor gamma).obj
              (baseTest (k' := L) T)))
            ((pic0TypeFunctor ((baseChange K L).obj C)).map
              (pic0GalTwistMor T gamma).op y) :=
          (NatTrans.naturality_apply (pic0ThetaType K L C).hom
            (pic0GalTwistMor T gamma).op y).symm
        _ = (pic0ThetaType K L C).hom.app
            (op ((pic0TwistTestFunctor gamma).obj
              (baseTest (k' := L) T)))
            ((pic0GaloisAction C gamma).inv.app
              (op (baseTest (k' := L) T)) y) := htheta
        _ = _ := by
          rw [pic0GaloisAction_inv_app_apply, Iso.inv_hom_id_app_apply]
          rw [pic0GaloisActionRestricted_inv_app]
          rfl
    rw [twistTest_eq_pic0GaloisRestrict_galTwistMor,
      op_comp, Functor.map_comp]
    change (pic0TypeFunctor C).map
        ((pic0GaloisRestrictTwistIso gamma).inv.app
          (baseTest (k' := L) T)).op
        ((pic0TypeFunctor C).map
          ((pic0GaloisRestrictTest (k := K) (L := L)).map
            (pic0GalTwistMor T gamma)).op
          ((pic0ThetaType K L C).hom.app
            (op (baseTest (k' := L) T)) y)) =
      (pic0ThetaType K L C).hom.app
        (op (baseTest (k' := L) T)) y
    rw [he]
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp,
      Iso.inv_hom_id_app, op_id, Functor.map_id_apply]

end ThetaAction

/-! ## Equivariance as a slice square -/

section Representative

variable (C : Over (Spec (CommRingCat.of K)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {J : Over (Spec (CommRingCat.of L))}
  (rep : (pic0TypeFunctor ((baseChange K L).obj C)).RepresentableBy J)

set_option maxHeartbeats 1000000 in
-- Expanding the transported Galois action needs more than the default heartbeat budget.
/-- Equivariance for the canonical action is exactly the corresponding square
in the slice over `Spec L`. -/
theorem pic0_isEquivariant_iff_galTwistMor
    (T : Over (Spec (CommRingCat.of K)))
    (phi : baseTest (k' := L) T ⟶ J) :
    (pullbackSemilinearGalAction K L T.hom).IsEquivariant
        (pic0SemilinearGalActionOfRepresentableBy C rep) phi.left ↔
      ∀ gamma : L ≃ₐ[K] L,
        pic0GalTwistMor T gamma ≫ phi =
          (pic0TwistTestFunctor gamma).map phi ≫
            pic0GaloisTwistMor C rep gamma := by
  constructor
  · intro h gamma
    exact Over.OverMorphism.ext (h gamma)
  · intro h gamma
    exact congrArg Over.Hom.left (h gamma)

/-- After applying the representing equivalence, the equivariance square at
`gamma` is the action equation on the represented Picard-zero class. -/
theorem pic0_homEquiv_galTwistMor_iff
    (T : Over (Spec (CommRingCat.of K)))
    (phi : baseTest (k' := L) T ⟶ J) (gamma : L ≃ₐ[K] L) :
    pic0GalTwistMor T gamma ≫ phi =
        (pic0TwistTestFunctor gamma).map phi ≫
          pic0GaloisTwistMor C rep gamma ↔
      (pic0TypeFunctor ((baseChange K L).obj C)).map
          (pic0GalTwistMor T gamma).op (rep.homEquiv phi) =
        (pic0GaloisAction C gamma).inv.app
          (op (baseTest (k' := L) T)) (rep.homEquiv phi) := by
  constructor
  · intro h
    have h' := congrArg rep.homEquiv h
    rw [rep.homEquiv_comp, rep.homEquiv_comp,
      pic0Galois_homEquiv_twistMor] at h'
    have hn := NatTrans.naturality_apply (pic0GaloisAction C gamma).inv
      phi.op (rep.homEquiv (𝟙 J))
    exact h'.trans (hn.symm.trans
      (congrArg ((pic0GaloisAction C gamma).inv.app
        (op (baseTest (k' := L) T))) (rep.homEquiv_eq phi).symm))
  · intro h
    apply rep.homEquiv.injective
    rw [rep.homEquiv_comp, rep.homEquiv_comp,
      pic0Galois_homEquiv_twistMor]
    have hn := NatTrans.naturality_apply (pic0GaloisAction C gamma).inv
      phi.op (rep.homEquiv (𝟙 J))
    exact h.trans ((congrArg ((pic0GaloisAction C gamma).inv.app
      (op (baseTest (k' := L) T))) (rep.homEquiv_eq phi)).trans hn)

/-- A Picard-zero class on the restricted base-changed test is the same as a
morphism from the base-changed test to its representative. -/
noncomputable def pic0GaloisClassHomEquiv
    (T : Over (Spec (CommRingCat.of K))) :
    (pic0TypeFunctor C).obj
        (op ((restrictTest K L).obj (baseTest (k' := L) T))) ≃
      (baseTest (k' := L) T ⟶ J) :=
  (Iso.toEquiv ((pic0ThetaType K L C).app
    (op (baseTest (k' := L) T)))).symm.trans rep.homEquiv.symm

@[simp]
theorem pic0GaloisClassHomEquiv_homEquiv
    (T : Over (Spec (CommRingCat.of K)))
    (x : (pic0TypeFunctor C).obj
      (op ((restrictTest K L).obj (baseTest (k' := L) T)))) :
    rep.homEquiv (pic0GaloisClassHomEquiv C rep T x) =
      (pic0ThetaType K L C).inv.app
        (op (baseTest (k' := L) T)) x :=
  Equiv.apply_symm_apply _ _

/-- The class-to-morphism equivalence commutes with precomposition of the
base-changed test schemes. -/
theorem pic0GaloisClassHomEquiv_precomp
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : (pic0TypeFunctor C).obj
      (op ((restrictTest K L).obj (baseTest (k' := L) T)))) :
    pic0GaloisClassHomEquiv C rep T'
        ((pic0TypeFunctor C).map
          (pic0GaloisBaseTestMap (L := L) a).op x) =
      pic0GaloisBaseChangeMor (L := L) a ≫
        pic0GaloisClassHomEquiv C rep T x := by
  apply rep.homEquiv.injective
  rw [rep.homEquiv_comp, pic0GaloisClassHomEquiv_homEquiv,
    pic0GaloisClassHomEquiv_homEquiv]
  rw [pic0GaloisBaseTestMap_eq_restrict_map]
  change (pic0ThetaType K L C).inv.app
      (op (baseTest (k' := L) T'))
      ((((pic0GaloisRestrictTest (k := K) (L := L)).op ⋙
          pic0TypeFunctor C).map
        (pic0GaloisBaseChangeMor (L := L) a).op) x) = _
  rw [NatTrans.naturality_apply]

set_option maxHeartbeats 1000000 in
-- This expands the theta/action bridge once in each direction.
/-- Under `pic0GaloisClassHomEquiv`, deck invariance is exactly equivariance
for the canonical semilinear action on the representative. -/
theorem pic0GaloisClassHomEquiv_invariant_iff_isEquivariant
    (T : Over (Spec (CommRingCat.of K)))
    (x : (pic0TypeFunctor C).obj
      (op ((restrictTest K L).obj (baseTest (k' := L) T)))) :
    (∀ gamma : L ≃ₐ[K] L,
        (pic0TypeFunctor C).map (twistTest T gamma).op x = x) ↔
      (pullbackSemilinearGalAction K L T.hom).IsEquivariant
        (pic0SemilinearGalActionOfRepresentableBy C rep)
        (pic0GaloisClassHomEquiv C rep T x).left := by
  rw [pic0_isEquivariant_iff_galTwistMor]
  constructor
  · intro hx gamma
    apply (pic0_homEquiv_galTwistMor_iff C rep T
      (pic0GaloisClassHomEquiv C rep T x) gamma).mpr
    apply (pic0_theta_invariant_iff_action C T
      (rep.homEquiv (pic0GaloisClassHomEquiv C rep T x)) gamma).mp
    have hclass : (pic0ThetaType K L C).hom.app
          (op (baseTest (k' := L) T))
          (rep.homEquiv (pic0GaloisClassHomEquiv C rep T x)) = x := by
      change (pic0GaloisClassHomEquiv C rep T).symm
        (pic0GaloisClassHomEquiv C rep T x) = x
      exact Equiv.symm_apply_apply _ _
    rw [hclass]
    exact hx gamma⁻¹
  · intro hs gamma
    have haction := (pic0_homEquiv_galTwistMor_iff C rep T
      (pic0GaloisClassHomEquiv C rep T x) gamma⁻¹).mp (hs gamma⁻¹)
    have hinvariant := (pic0_theta_invariant_iff_action C T
      (rep.homEquiv (pic0GaloisClassHomEquiv C rep T x)) gamma⁻¹).mpr haction
    have hclass : (pic0ThetaType K L C).hom.app
          (op (baseTest (k' := L) T))
          (rep.homEquiv (pic0GaloisClassHomEquiv C rep T x)) = x := by
      change (pic0GaloisClassHomEquiv C rep T).symm
        (pic0GaloisClassHomEquiv C rep T x) = x
      exact Equiv.symm_apply_apply _ _
    rw [hclass] at hinvariant
    rw [inv_inv] at hinvariant
    exact hinvariant

/-- Galois-invariant Picard-zero classes are exactly equivariant morphisms to
the finite-extension representative with its canonical semilinear action. -/
noncomputable def pic0GaloisInvariantEquivGaloisEquivariantOver
    (T : Over (Spec (CommRingCat.of K))) :
    Pic0GaloisInvariant (L := L) C T ≃
      GaloisEquivariantOver
        (pic0SemilinearGalActionOfRepresentableBy C rep) T where
  toFun x :=
    let phi := pic0GaloisClassHomEquiv C rep T x.1
    { hom := phi.left
      commutes := phi.w
      equivariant :=
        (pic0GaloisClassHomEquiv_invariant_iff_isEquivariant C rep T x.1).mp x.2 }
  invFun h :=
    let phi : baseTest (k' := L) T ⟶ J := Over.homMk h.hom h.commutes
    let x := (pic0GaloisClassHomEquiv C rep T).symm phi
    ⟨x, (pic0GaloisClassHomEquiv_invariant_iff_isEquivariant C rep T x).mpr (by
      have hphi : pic0GaloisClassHomEquiv C rep T x = phi := by
        exact Equiv.apply_symm_apply _ _
      rw [hphi]
      exact h.equivariant)⟩
  left_inv x := by
    apply Subtype.ext
    let phi := pic0GaloisClassHomEquiv C rep T x.1
    have hphi : (Over.homMk phi.left phi.w : baseTest (k' := L) T ⟶ J) = phi := by
      apply Over.OverMorphism.ext
      rfl
    change (pic0GaloisClassHomEquiv C rep T).symm
      (Over.homMk phi.left phi.w) = x.1
    rw [hphi]
    exact Equiv.symm_apply_apply _ _
  right_inv h := by
    apply GaloisEquivariantOver.ext
      (pic0SemilinearGalActionOfRepresentableBy C rep)
    let phi : baseTest (k' := L) T ⟶ J := Over.homMk h.hom h.commutes
    change (pic0GaloisClassHomEquiv C rep T
      ((pic0GaloisClassHomEquiv C rep T).symm phi)).left = h.hom
    rw [Equiv.apply_symm_apply]
    rfl

@[simp]
theorem pic0GaloisInvariantEquivGaloisEquivariantOver_hom
    (T : Over (Spec (CommRingCat.of K)))
    (x : Pic0GaloisInvariant (L := L) C T) :
    (pic0GaloisInvariantEquivGaloisEquivariantOver C rep T x).hom =
      (pic0GaloisClassHomEquiv C rep T x.1).left :=
  rfl

/-- The invariant-class/equivariant-map equivalence is natural under
precomposition by arbitrary morphisms of `K`-test schemes. -/
theorem pic0GaloisInvariantEquivGaloisEquivariantOver_precomp
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : Pic0GaloisInvariant (L := L) C T) :
    pic0GaloisInvariantEquivGaloisEquivariantOver C rep T'
        (Pic0GaloisInvariant.precomp C a x) =
      GaloisEquivariantOver.precomp
        (pic0SemilinearGalActionOfRepresentableBy C rep) a
        (pic0GaloisInvariantEquivGaloisEquivariantOver C rep T x) := by
  apply GaloisEquivariantOver.ext
    (pic0SemilinearGalActionOfRepresentableBy C rep)
  change (pic0GaloisClassHomEquiv C rep T'
      ((pic0TypeFunctor C).map
        (pic0GaloisBaseTestMap (L := L) a).op x.1)).left =
    (pic0GaloisBaseChangeMor (L := L) a ≫
      pic0GaloisClassHomEquiv C rep T x.1).left
  exact congrArg Over.Hom.left
    (pic0GaloisClassHomEquiv_precomp C rep a x.1)

end Representative

end

end AlgebraicGeometry
