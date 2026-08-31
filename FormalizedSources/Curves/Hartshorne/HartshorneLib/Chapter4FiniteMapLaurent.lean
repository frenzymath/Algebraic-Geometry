/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4FiniteMapSections

/-!
# Finite section maps after a ring-coordinate change

The projective-line overlap is naturally identified with a Laurent polynomial ring.  The
finite-morphism API gives finiteness over the overlap section ring, so this file records the
small transport step across that ring equivalence.  The induced algebra structure is local to
the theorem; callers do not acquire a competing global scalar instance.
-/

set_option autoImplicit false

universe u v w

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne
namespace FiniteMapSections

variable {A : Type u} {B : Type v} {C : Type w}

/-! The proof is first stated with an arbitrary finite ring map, then specialized to scheme
sections below. -/

theorem moduleFinite_of_ringEquiv_comp
    [CommRing A] [CommRing B] [CommRing C]
    (e : A ≃+* B) (g : B →+* C) (hg : g.Finite) :
    letI : Algebra A C := (g.comp e.toRingHom).toAlgebra
    Module.Finite A C := by
  letI : Algebra A C := (g.comp e.toRingHom).toAlgebra
  rw [← RingHom.finite_algebraMap]
  exact hg.comp e.finite

/-! Applying the transport to the section map of a finite morphism is the form used by the
Laurent overlap of a finite map to `P¹`. -/

theorem moduleFinite_of_isFinite_of_ringEquiv
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    {A : Type v} [CommRing A] (U : Y.Opens) (hU : IsAffineOpen U)
    (e : A ≃+* (↑(Y.presheaf.obj (op U)) : Type u)) :
    letI : Algebra A (↑(X.presheaf.obj (op (f ⁻¹ᵁ U))) : Type u) :=
      (((f.app U).hom.comp e.toRingHom).toAlgebra)
    Module.Finite A (↑(X.presheaf.obj (op (f ⁻¹ᵁ U))) : Type u) := by
  letI : Algebra A (↑(X.presheaf.obj (op (f ⁻¹ᵁ U))) : Type u) :=
    (((f.app U).hom.comp e.toRingHom).toAlgebra)
  exact moduleFinite_of_ringEquiv_comp e (f.app U).hom (f.finite_app U hU)

end FiniteMapSections
end Hartshorne
