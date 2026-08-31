/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.RigidityChain

/-!
# Source-shaped Form-I rigidity

The geometric rigidity engine in `RigidityChain` keeps its pointwise and
product hypotheses explicit.  This wrapper supplies those hypotheses from the
usual geometric-integrality assumptions, matching the statement used in
Mumford's Form-I argument.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace Mumford
namespace GroupScheme

open AlgebraicGeometry

variable {kbar : Type u} [Field kbar] [IsAlgClosed kbar]

/-- Form-I rigidity with the product and distinguished-point hypotheses
derived from geometric integrality. -/
theorem rigidity_lemma_unique_of_geometricallyIntegral
    {X Y Z : Over (Spec (.of kbar))}
    [IsProper X.hom]
    [GeometricallyIntegral X.hom]
    [GeometricallyIntegral Y.hom]
    [LocallyOfFiniteType Y.hom]
    [IsSeparated Z.hom]
    (f : X ⊗ Y ⟶ Z)
    (y₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ Z)
    (hf : lift (𝟙 X) (toUnit X ≫ y₀) ≫ f = toUnit X ≫ z₀) :
    ∃! g : Y ⟶ Z, f = snd X Y ≫ g := by
  letI : LocallyOfFiniteType X.hom := IsProper.toLocallyOfFiniteType
  haveI : GeometricallyIrreducible (X ⊗ Y).hom := by
    rw [Over.tensorObj_hom]
    exact GeometricallyIrreducible.comp (pullback.fst X.hom Y.hom) X.hom
  haveI : LocallyOfFiniteType (X ⊗ Y).hom := by
    rw [Over.tensorObj_hom]
    exact AlgebraicGeometry.locallyOfFiniteType_comp
      (pullback.fst X.hom Y.hom) X.hom
  letI : IsIntegral (X ⊗ Y).left :=
    isIntegral_tensorObj_left_of_geometricallyIntegral (X := X) (Y := Y)
  haveI : IsReduced (X ⊗ Y).left := inferInstance
  haveI : IrreducibleSpace X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton X.hom
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty (α := ↥X.left)) isOpen_univ.isLocallyClosed
  let x₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ X :=
    Over.homMk (pointOfClosedPoint X.hom x hx) (by simp)
  exact rigidity_lemma_unique f x₀ y₀ z₀ hf

/-- The existential factorization form used by Mumford's Form-I statement. -/
theorem rigidity_lemma_of_geometricallyIntegral
    {X Y Z : Over (Spec (.of kbar))}
    [IsProper X.hom]
    [GeometricallyIntegral X.hom]
    [GeometricallyIntegral Y.hom]
    [LocallyOfFiniteType Y.hom]
    [IsSeparated Z.hom]
    (f : X ⊗ Y ⟶ Z)
    (y₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ Z)
    (hf : lift (𝟙 X) (toUnit X ≫ y₀) ≫ f = toUnit X ≫ z₀) :
    ∃ g : Y ⟶ Z, f = snd X Y ≫ g :=
  (rigidity_lemma_unique_of_geometricallyIntegral f y₀ z₀ hf).exists

end GroupScheme
end Mumford
