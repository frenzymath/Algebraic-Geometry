/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0SepClosedRepresentable
import AlgebraicJacobian.Picard.Pic0ThetaAssembly
import AlgebraicJacobian.Picard.RepresentableByCocycle

/-!
# Transporting a Picard-zero representative through a field extension

The base-change comparison `pic0ThetaType` and the adjunction
`Over.mapPullbackAdj` transport a genuine `RepresentableBy` certificate to a
base-changed curve.  The representing object is still only determined up to
isomorphism, so the final object isomorphism is an explicit input.  Keeping
that input visible prevents this lemma from silently asserting either finite
stage descent or compatibility between independently named curves.
-/

set_option autoImplicit false

universe v v₁ u₁ u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Functor.RepresentableBy

/-! ## Object-isomorphism transport -/

/-- Move a representation along an isomorphism of representing objects. -/
noncomputable def ofObjectIso
    {C : Type u₁} [Category.{v₁, u₁} C] {F : Cᵒᵖ ⥤ Type v}
    {X Y : C} (r : F.RepresentableBy X) (e : X ≅ Y) :
    F.RepresentableBy Y where
  homEquiv := fun {Z} =>
    { toFun := fun f => r.homEquiv (f ≫ e.inv)
      invFun := fun x => r.homEquiv.symm x ≫ e.hom
      left_inv := by
        intro f
        dsimp
        rw [r.homEquiv.symm_apply_apply, Category.assoc,
          Iso.inv_hom_id, Category.comp_id]
      right_inv := by
        intro x
        dsimp
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id,
          r.homEquiv.apply_symm_apply] }
  homEquiv_comp := by
    intro Z Z' f g
    dsimp
    rw [Category.assoc, r.homEquiv_comp]

end CategoryTheory.Functor.RepresentableBy

namespace AlgebraicGeometry

noncomputable section

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-! ## Picard-zero transport -/

/-- Transport a genuine Picard-zero representing object across `k → L`.

The first step is the right-adjoint transport along
`Over.mapPullbackAdj`; `pic0ThetaType.symm` then identifies the resulting
presheaf with the degree-zero Picard functor of the base-changed curve.  The
explicit `e` is the only object-level input needed to select the requested
representing object.
-/
noncomputable def pic0RepresentableBy_of_baseChangeObjectIso
    {J : Over (Spec (.of k))}
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    {J' : Over (Spec (.of L))}
    (e :
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj J ≅ J') :
    (pic0TypeFunctor ((baseChange k L).obj C)).RepresentableBy J' := by
  let pulled :=
    CategoryTheory.Functor.RepresentableBy.ofLeftAdjoint
      (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))) rep
  let rebased := pulled.ofIso (pic0ThetaType k L C).symm
  exact CategoryTheory.Functor.RepresentableBy.ofObjectIso rebased e

end

end AlgebraicGeometry
