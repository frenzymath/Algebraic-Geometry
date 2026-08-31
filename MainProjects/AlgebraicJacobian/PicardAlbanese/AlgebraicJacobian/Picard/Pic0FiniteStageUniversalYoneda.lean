/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageUniversalClass

/-!
# The Yoneda map attached to a Picard-zero class

An element of the degree-zero Picard functor on a test object determines its
Yoneda family by pullback.  This is the small binder-free bridge used by the
finite-stage descent lane.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-! ## The class-to-Yoneda construction -/

/-- The Yoneda family induced by a degree-zero Picard class on `J`. -/
noncomputable def pic0ClassYoneda {J : Over (Spec (.of k))}
    (u : pic0Subgroup C J) : yoneda.obj J ⟶ pic0TypeFunctor C :=
  yonedaEquiv.symm u

@[simp]
theorem pic0ClassYoneda_app {J : Over (Spec (.of k))}
    (u : pic0Subgroup C J) {T : Over (Spec (.of k))} (f : T ⟶ J) :
    (pic0ClassYoneda C u).app (op T) f = pic0Map C f u := by
  calc
    (pic0ClassYoneda C u).app (op T) f =
        (pic0TypeFunctor C).map f.op u := by
      simpa [pic0ClassYoneda] using
        (yonedaEquiv_symm_app_apply (F := pic0TypeFunctor C) u (op T) f)
    _ = pic0Map C f u := by
      exact pic0TypeFunctor_map_apply (C := C) f.op u

/-! ## The pinned separably closed universal class -/

variable [IsSepClosed k]

/-- The Yoneda family attached to the pinned separably closed universal class. -/
noncomputable def pic0SepClosedClassYoneda :
    yoneda.obj (pic0_sepClosed_representableBy (C := C)).1 ⟶ pic0TypeFunctor C :=
  pic0ClassYoneda C (pic0SepClosedUniversalClass C)

@[simp]
theorem pic0SepClosedClassYoneda_app {T : Over (Spec (.of k))}
    (f : T ⟶ (pic0_sepClosed_representableBy (C := C)).1) :
    (pic0SepClosedClassYoneda C).app (op T) f =
      (pic0_sepClosed_representableBy (C := C)).2.homEquiv f := by
  rw [pic0SepClosedClassYoneda, pic0ClassYoneda_app,
    pic0SepClosedUniversalClass]
  calc
    (pic0Map C f)
        ((pic0_sepClosed_representableBy (C := C)).2.homEquiv
          (𝟙 (pic0_sepClosed_representableBy (C := C)).1)) =
        (pic0TypeFunctor C).map f.op
          ((pic0_sepClosed_representableBy (C := C)).2.homEquiv
            (𝟙 (pic0_sepClosed_representableBy (C := C)).1)) := by
      exact (pic0TypeFunctor_map_apply (C := C) f.op _).symm
    _ = (pic0_sepClosed_representableBy (C := C)).2.homEquiv
          (f ≫ 𝟙 (pic0_sepClosed_representableBy (C := C)).1) := by
      exact ((pic0_sepClosed_representableBy (C := C)).2.homEquiv_comp
        f (𝟙 (pic0_sepClosed_representableBy (C := C)).1)).symm
    _ = (pic0_sepClosed_representableBy (C := C)).2.homEquiv f := by
      rw [Category.comp_id]

end

end AlgebraicGeometry
