/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import MilneLib.Isogeny
import MilneLib.DimensionCorollaries

/-!
# Fibre corollaries for isogenies

The arbitrary-field isogeny API gives finite fibres after extension to the
target residue field.  Properness converts that scheme-theoretic statement
back to finiteness of the underlying set-theoretic fibre.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MorphismProperty
open AlgebraicGeometry

namespace MilneLib

/-- An isogeny of abelian varieties has finite underlying fibres over every
target point, without an algebraic-closure hypothesis. -/
theorem Isogeny.finite_preimage_singleton_of_isAbelianVariety_of_arbitraryField
    {K : Type u} [Field K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (f : A ⟶ B) [IsMonHom f] (h : Isogeny f)
    (y : B.left) :
    (f.left ⁻¹' {y}).Finite := by
  letI : IsProper f.left := isProper_left_of_isAbelianVariety hA hB f
  apply (isFinite_fiberToSpecResidueField_iff_finite_preimage_singleton
    f.left y).mp
  exact Isogeny.isFinite_fiberToSpecResidueField_of_isAbelianVariety
    hA hB f h y

/- The scheme-theoretic residue-field fibres are finite over a field and hence
   have zero Krull dimension.  This keeps the geometric fibre conclusion
   separate from the still-explicit flatness hypotheses in the rank API. -/
theorem Isogeny.topologicalKrullDim_fiber_eq_zero_of_isAbelianVariety_of_arbitraryField
    {K : Type u} [Field K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (f : A ⟶ B) [IsMonHom f] (h : Isogeny f)
    (y : B.left) :
    topologicalKrullDim (f.left.fiber y) = 0 := by
  letI : Surjective f.left := h.1
  have hfib : IsFinite (f.left.fiberToSpecResidueField y) :=
    Isogeny.isFinite_fiberToSpecResidueField_of_isAbelianVariety
      hA hB f h y
  have hsurj : Surjective (f.left.fiberToSpecResidueField y) := by
    change Surjective (pullback.snd f.left (B.left.fromSpecResidueField y))
    exact MorphismProperty.pullback_snd _ _
      (inferInstance : Surjective f.left)
  exact @topologicalKrullDim_eq_zero_of_isFinite_surjective_to_field
    (B.left.residueField y) (inferInstance) (f.left.fiber y)
    (f.left.fiberToSpecResidueField y) hfib hsurj

end MilneLib
