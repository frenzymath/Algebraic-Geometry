/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Projective.GrassmannianPluckerGlobalImmersion
import AlgebraicJacobian.Picard.FiniteMorphismEmbedding

/-!
# Projectivity of the absolute Grassmannian over Spec Z

The absolute Plucker morphism lifts to relative projective space over
`Spec Z`. Its composite with the projection to the projective model over `Spec Z`
is the absolute Plucker morphism, so the lift is an immersion. Properness of
the Grassmannian structure morphism then upgrades that immersion to a closed
immersion and proves projectivity, hence H-quasi-projectivity.

The project-local definitions quantify over an arbitrary finite coordinate
type. Thus the finite type `PluckerIndex d r` is used directly, without an
irrelevant reindexing by `Fin (n + 1)`.
-/

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry
namespace Grassmannian

/-- The relative Plucker morphism into projective space over `Spec Z`. -/
noncomputable def pluckerToProjectiveSpace (d r : ℕ) :
    scheme d r ⟶ ℙ(PluckerIndex d r; Spec (CommRingCat.of ℤ)) :=
  pullback.lift (toSpecZ d r) (pluckerToProj d r) (terminal.hom_ext _ _)

/-- The relative Plucker morphism lies over the Grassmannian structure map. -/
@[reassoc (attr := simp)]
theorem pluckerToProjectiveSpace_over (d r : ℕ) :
    pluckerToProjectiveSpace d r ≫
        (ℙ(PluckerIndex d r; Spec (CommRingCat.of ℤ)) ↘
          Spec (CommRingCat.of ℤ)) =
      toSpecZ d r := by
  exact pullback.lift_fst _ _ _

/-- Projecting the relative Plucker morphism to the projective model over
`Spec Z` recovers
the absolute Plucker morphism. -/
@[reassoc (attr := simp)]
theorem pluckerToProjectiveSpace_toProjInt (d r : ℕ) :
    pluckerToProjectiveSpace d r ≫
        ProjectiveSpace.toProjInt (PluckerIndex d r) (Spec (CommRingCat.of ℤ)) =
      pluckerToProj d r := by
  exact pullback.lift_snd _ _ _

/-- The relative Plucker morphism is an immersion. -/
theorem pluckerToProjectiveSpace_isImmersion (d r : ℕ) :
    IsImmersion (pluckerToProjectiveSpace d r) := by
  haveI : IsImmersion
      (pluckerToProjectiveSpace d r ≫
        ProjectiveSpace.toProjInt (PluckerIndex d r) (Spec (CommRingCat.of ℤ))) := by
    rw [pluckerToProjectiveSpace_toProjInt]
    exact pluckerToProj_isImmersion d r
  exact IsImmersion.of_comp
    (pluckerToProjectiveSpace d r)
    (ProjectiveSpace.toProjInt (PluckerIndex d r) (Spec (CommRingCat.of ℤ)))

/-- The absolute Grassmannian is projective over `Spec Z`. -/
theorem isProjective_toSpecZ (d r : ℕ) :
    (toSpecZ d r).IsProjective := by
  exact Scheme.Hom.IsProjective.of_isProper_of_immersion
    (isProper d r)
    (pluckerToProjectiveSpace d r)
    (pluckerToProjectiveSpace_isImmersion d r)
    (pluckerToProjectiveSpace_over d r)

/-- The absolute Grassmannian is H-quasi-projective over `Spec Z`. -/
theorem isHQuasiProjective_toSpecZ (d r : ℕ) :
    (toSpecZ d r).IsHQuasiProjective :=
  (isProjective_toSpecZ d r).isHQuasiProjective

end Grassmannian
end AlgebraicGeometry
