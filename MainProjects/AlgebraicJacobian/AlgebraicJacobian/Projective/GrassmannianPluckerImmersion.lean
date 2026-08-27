/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Projective.GrassmannianPlucker
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Affine-chart immersion for the Plucker morphism

The normalized Plucker coordinates generate every affine Grassmannian chart
ring: each free matrix entry is a maximal minor up to sign. Consequently, the
map to the corresponding standard projective chart is a closed immersion, and
the local Plucker morphism is an immersion.

The global immersion still requires the target-local preimage identification
between projective standard charts and Grassmannian affine charts.
-/

open CategoryTheory Limits
open MvPolynomial HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry
namespace Grassmannian

private theorem mvPolynomial_int_surjective_of_X_mem_range
    {A σ : Type*} [Ring A] (f : A →+* MvPolynomial σ ℤ)
    (hX : ∀ n, ∃ x, f x = MvPolynomial.X n) : Function.Surjective f := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨(a : A), map_intCast f a⟩
  | add p q hp hq =>
      obtain ⟨p', rfl⟩ := hp
      obtain ⟨q', rfl⟩ := hq
      exact ⟨p' + q', map_add f p' q'⟩
  | mul_X p n hp =>
      obtain ⟨p', rfl⟩ := hp
      obtain ⟨x', hx'⟩ := hX n
      exact ⟨p' * x', by rw [map_mul, hx']⟩

set_option maxHeartbeats 800000 in
-- Cofactor witnesses elaborate through the projected glue-data index.
set_option backward.isDefEq.respectTransparency false in
/-- The ring homomorphism defining a normalized Plucker chart is surjective.
Every free matrix coordinate is the image of a projective chart coordinate,
possibly after negating that coordinate. -/
theorem pluckerChartHom_surjective (d r : ℕ) (I : PluckerIndex d r) :
    Function.Surjective
      (ProjectiveSpace.Coordinates.chartHom I
        (fun K : PluckerIndex d r => minorDet d r I.1 K.1 I.2 K.2)
        (minorDet_self d r I.1 I.2)) := by
  let f := ProjectiveSpace.Coordinates.chartHom I
    (fun K : PluckerIndex d r => minorDet d r I.1 K.1 I.2 K.2)
    (minorDet_self d r I.1 I.2)
  change Function.Surjective f
  apply mvPolynomial_int_surjective_of_X_mem_range f
  rintro ⟨p, ⟨q, hq⟩⟩
  obtain ⟨K, hK, h | h⟩ :=
    exists_minorDet_eq_free_entry d r I.1 I.2 p q hq
  · refine ⟨ProjectiveSpace.Coordinates.chartCoord I
      (⟨K, hK⟩ : PluckerIndex d r), ?_⟩
    simpa only [f, ProjectiveSpace.Coordinates.chartHom_chartCoord] using h
  · let x := ProjectiveSpace.Coordinates.chartCoord I
      (⟨K, hK⟩ : PluckerIndex d r)
    have hcoord : f x = -MvPolynomial.X (p, ⟨q, hq⟩) := by
      simpa only [f, x, ProjectiveSpace.Coordinates.chartHom_chartCoord] using h
    refine ⟨-x, ?_⟩
    calc
      f (-x) = -f x := map_neg f x
      _ = -(-MvPolynomial.X (p, ⟨q, hq⟩)) := congrArg Neg.neg hcoord
      _ = MvPolynomial.X (p, ⟨q, hq⟩) := neg_neg _

/-- The affine spectrum map underlying the normalized Plucker chart is a
closed immersion. -/
theorem pluckerChartSpecMap_isClosedImmersion (d r : ℕ)
    (I : PluckerIndex d r) :
    IsClosedImmersion
      (Spec.map (CommRingCat.ofHom
        (ProjectiveSpace.Coordinates.chartHom I
          (fun K : PluckerIndex d r => minorDet d r I.1 K.1 I.2 K.2)
          (minorDet_self d r I.1 I.2)))) :=
  IsClosedImmersion.spec_of_surjective _
    (pluckerChartHom_surjective d r I)

/-- Each normalized Plucker chart morphism is an immersion into the absolute
projective model. -/
theorem pluckerChart_isImmersion (d r : ℕ) (I : PluckerIndex d r) :
    IsImmersion (pluckerChart d r I) := by
  rw [pluckerChart, ProjectiveSpace.Coordinates.fromSpec]
  letI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom
        (ProjectiveSpace.Coordinates.chartHom I
          (fun K : PluckerIndex d r => minorDet d r I.1 K.1 I.2 K.2)
          (minorDet_self d r I.1 I.2)))) :=
    pluckerChartSpecMap_isClosedImmersion d r I
  have hfirst : IsImmersion
      (Spec.map (CommRingCat.ofHom
        (ProjectiveSpace.Coordinates.chartHom I
          (fun K : PluckerIndex d r => minorDet d r I.1 K.1 I.2 K.2)
          (minorDet_self d r I.1 I.2)))) := by
    infer_instance
  apply MorphismProperty.comp_mem @IsImmersion
  · exact hfirst
  · infer_instance

end Grassmannian
end AlgebraicGeometry
