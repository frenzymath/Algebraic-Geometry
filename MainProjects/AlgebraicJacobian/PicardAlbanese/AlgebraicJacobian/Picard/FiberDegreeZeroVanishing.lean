/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib

/-!
# Vanishing of a finite-dimensional quotient fibre in degree zero

An epimorphism from the structure sheaf is determined by the image of its global
unit section.  Consequently, once the global sections of its target are known to
be finite-dimensional, fibre degree zero forces the target sheaf to vanish.

The finite-dimensional hypothesis is essential: without it, `Module.finrank`
returns zero for an infinite-dimensional module as well.  This module isolates
the exact algebraic endpoint that a finite-support/coherence argument must feed.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

universe u

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- If the sections over the top open are a subsingleton, then compatible
presheaf-wide sections are a subsingleton. -/
theorem sections_subsingleton_of_subsingleton_top {M : X.Modules}
    [Subsingleton Γ(M, ⊤)] : Subsingleton M.sections := by
  refine ⟨fun s t => PresheafOfModules.sections_ext s t fun U => ?_⟩
  let f : Opposite.op (⊤ : X.Opens) ⟶ U := (homOfLE le_top).op
  rw [← PresheafOfModules.sections_property s f,
    ← PresheafOfModules.sections_property t f]
  congr 1
  have hs : ∀ a b : Γ(M, ⊤), a = b := fun _ _ => Subsingleton.elim _ _
  exact hs (s.val (Opposite.op (⊤ : X.Opens)))
    (t.val (Opposite.op (⊤ : X.Opens)))

/-- An epimorphic quotient of the structure sheaf with no global sections is
the zero sheaf. -/
theorem isZero_of_epi_unit_of_subsingleton_sections {M : X.Modules}
    (q : SheafOfModules.unit X.ringCatSheaf ⟶ M) [Epi q]
    [Subsingleton Γ(M, ⊤)] : IsZero M := by
  letI : Subsingleton M.sections :=
    sections_subsingleton_of_subsingleton_top
  apply IsZero.of_epi_eq_zero q
  apply M.unitHomEquiv.injective
  exact Subsingleton.elim _ _

/-- A finite-dimensional epimorphic quotient of the structure sheaf whose
global-section dimension is zero is the zero sheaf. -/
theorem isZero_of_epi_unit_of_finrank_zero
    {k : Type u} [Field k] {M : X.Modules}
    [Module k Γ(M, ⊤)] [FiniteDimensional k Γ(M, ⊤)]
    (q : SheafOfModules.unit X.ringCatSheaf ⟶ M) [Epi q]
    (h : Module.finrank k Γ(M, ⊤) = 0) : IsZero M := by
  letI : Subsingleton Γ(M, ⊤) :=
    ⟨fun a b => (finrank_zero_iff_forall_zero.mp h a).trans
      (finrank_zero_iff_forall_zero.mp h b).symm⟩
  exact isZero_of_epi_unit_of_subsingleton_sections q

end Scheme.Modules

end AlgebraicGeometry
