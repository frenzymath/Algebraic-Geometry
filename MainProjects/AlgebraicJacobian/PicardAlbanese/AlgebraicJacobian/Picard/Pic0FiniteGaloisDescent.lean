/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.GaloisQuotientOverlap
import AlgebraicJacobian.Picard.Pic0GaloisAction

/-!
# The quotient-side bridge for finite Galois descent of Picard zero

A specified finite Galois quotient represents equivariant maps after base
change.  This file records that statement in the over-category.  It is the
scheme-theoretic half of descending a representative of `pic0TypeFunctor`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits
open AlgebraicGeometry

namespace AlgebraicJacobian.GaloisDescent

/-- An equivariant map from the finite-Galois base change of an object over
`Spec K` to a semilinearly acted `L`-scheme. -/
structure GaloisEquivariantOver
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f)
    (T : Over (Spec (CommRingCat.of K))) where
  hom : pullback T.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ X
  commutes : hom ≫ f =
    pullback.snd T.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  equivariant : (pullbackSemilinearGalAction K L T.hom).IsEquivariant rho hom

namespace GaloisEquivariantOver

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
  (rho : SemilinearGalAction K L X f)

/-- Pull an equivariant map back along a morphism over `Spec K`. -/
noncomputable def precomp
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (h : GaloisEquivariantOver rho T) : GaloisEquivariantOver rho T' where
  hom := pullbackBaseChange K L T.hom T'.hom a.left a.w ≫ h.hom
  commutes := by
    rw [Category.assoc, h.commutes, pullbackBaseChange_snd]
  equivariant := SemilinearGalAction.isEquivariant_pullbackBaseChange_comp
    T.hom T'.hom rho h.equivariant a.left a.w

@[ext]
theorem ext {T : Over (Spec (CommRingCat.of K))}
    {h h' : GaloisEquivariantOver rho T} (hh : h.hom = h'.hom) : h = h' := by
  cases h
  cases h'
  cases hh
  rfl

end GaloisEquivariantOver

namespace GaloisQuotientWitness

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
  {rho : SemilinearGalAction K L X f}
  {Y : Scheme.{u}} {g : Y ⟶ Spec (CommRingCat.of K)}

/-- A finite-Galois quotient witness represents equivariant maps after base
change, with no affineness assumption on the test object. -/
noncomputable def overHomEquiv (w : GaloisQuotientWitness rho Y g)
    (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ Over.mk g) ≃ GaloisEquivariantOver rho T where
  toFun a :=
    { hom := pullbackBaseChange K L g T.hom a.left a.w ≫ w.e.hom
      commutes := by
        rw [Category.assoc, w.over, pullbackBaseChange_snd]
      equivariant := SemilinearGalAction.isEquivariant_pullbackBaseChange_comp
        g T.hom rho w.equivariant a.left a.w }
  invFun h :=
    Over.homMk
      (w.universal T.left T.hom h.hom h.commutes h.equivariant).choose.1
      (w.universal T.left T.hom h.hom h.commutes h.equivariant).choose.2
  left_inv a := by
    apply Over.OverMorphism.ext
    let h := pullbackBaseChange K L g T.hom a.left a.w ≫ w.e.hom
    let hw := w.universal T.left T.hom h
      (by
        dsimp [h]
        rw [Category.assoc, w.over, pullbackBaseChange_snd])
      (by
        dsimp [h]
        exact SemilinearGalAction.isEquivariant_pullbackBaseChange_comp
          g T.hom rho w.equivariant a.left a.w)
    have ha : pullbackBaseChange K L g T.hom a.left a.w ≫ w.e.hom = h := rfl
    have heq : hw.choose = ⟨a.left, a.w⟩ :=
      hw.unique hw.choose_spec.1 ha
    exact congrArg Subtype.val heq
  right_inv h := by
    apply GaloisEquivariantOver.ext rho
    exact (w.universal T.left T.hom h.hom h.commutes h.equivariant).choose_spec.1

/-- The quotient universal-property equivalence commutes with precomposition
in the category of schemes over `Spec K`. -/
theorem overHomEquiv_precomp (w : GaloisQuotientWitness rho Y g)
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (b : T ⟶ Over.mk g) :
    w.overHomEquiv T' (a ≫ b) =
      GaloisEquivariantOver.precomp rho a (w.overHomEquiv T b) := by
  apply GaloisEquivariantOver.ext rho
  change pullbackBaseChange K L g T'.hom (a.left ≫ b.left) _ ≫ w.e.hom =
    pullbackBaseChange K L T.hom T'.hom a.left a.w ≫
      (pullbackBaseChange K L g T.hom b.left b.w ≫ w.e.hom)
  rw [pullbackBaseChange_comp K L g T.hom T'.hom b.left b.w a.left a.w,
    Category.assoc]

end GaloisQuotientWitness

namespace StableAffineOpen

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
  (rho : SemilinearGalAction K L X f)

/-- Under the orbit-in-an-affine-open hypothesis, the glued invariant-ring
quotient represents equivariant maps after finite Galois base change. -/
noncomputable def gluedQuotientOverHomEquiv
    [FiniteDimensional K L] [IsGalois K L] [rho.OrbitsInAffineOpen]
    (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ gluedQuotientOver rho) ≃ GaloisEquivariantOver rho T :=
  (gluedGaloisQuotientWitness rho).toGaloisQuotientWitness.overHomEquiv T

/-- The glued-quotient equivalence is natural under precomposition. -/
theorem gluedQuotientOverHomEquiv_precomp
    [FiniteDimensional K L] [IsGalois K L] [rho.OrbitsInAffineOpen]
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (b : T ⟶ gluedQuotientOver rho) :
    gluedQuotientOverHomEquiv rho T' (a ≫ b) =
      GaloisEquivariantOver.precomp rho a (gluedQuotientOverHomEquiv rho T b) :=
  GaloisQuotientWitness.overHomEquiv_precomp
    (gluedGaloisQuotientWitness rho).toGaloisQuotientWitness a b

end StableAffineOpen

end AlgebraicJacobian.GaloisDescent
