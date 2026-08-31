/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GroupSchemeHomogeneity
import AlgebraicJacobian.Picard.ProjectiveMorphism

/-!
# Picard components through rational sections

For a global `k`-section `p` of the Picard scheme, translation carries the
identity component to the topological connected component through `p`.  This
module packages that component as an open subscheme and records its isomorphism
over `Spec k` with `Pic⁰`.

This construction is indexed only by global sections.  It does not construct
components without a rational point, a degree indexing, or a decomposition of
the full Picard scheme.
-/

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace AlgebraicGeometry
namespace Scheme
namespace PicScheme

variable {k : Type u} [Field k]
variable (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIntegral C.hom] [HasPicScheme C]

private noncomputable def sectionTranslation
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ PicScheme C) :
    PicScheme C ≅ PicScheme C :=
  CategoryTheory.GrpObj.pointTranslation (PicScheme C)
    (MonObj.one (X := PicScheme C)) p

/-- The open connected component of the Picard scheme through the global
section `p`, obtained by translating `Pic⁰`. -/
noncomputable def sectionComponentOpen
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ PicScheme C) :
    (PicScheme C).left.Opens :=
  (sectionTranslation C p).hom.left ''ᵁ
    GroupScheme.identityComponentOpens (PicScheme C)

/-- The translated open is exactly the topological connected component through
the point defined by the global section `p`. -/
theorem coe_sectionComponentOpen
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ PicScheme C) :
    (sectionComponentOpen C p : Set (PicScheme C).left) =
      connectedComponent
        ((p.left.base : ↑(Spec (.of k)) → (PicScheme C).left)
          (default : Spec (.of k))) := by
  let e : (PicScheme C).left ≃ₜ (PicScheme C).left :=
    (sectionTranslation C p).hom.left.homeomorph
  let onePoint : (PicScheme C).left :=
    (((MonObj.one (X := PicScheme C)).left.base :
      ↑(Spec (.of k)) → (PicScheme C).left) (default : Spec (.of k)))
  let pPoint : (PicScheme C).left :=
    ((p.left.base : ↑(Spec (.of k)) → (PicScheme C).left)
      (default : Spec (.of k)))
  have hp : e onePoint = pPoint := by
    change (sectionTranslation C p).hom.left.base
      (((MonObj.one (X := PicScheme C)).left.base :
        ↑(Spec (.of k)) → (PicScheme C).left) (default : Spec (.of k))) =
      ((p.left.base : ↑(Spec (.of k)) → (PicScheme C).left)
        (default : Spec (.of k)))
    simpa [sectionTranslation] using
      CategoryTheory.GrpObj.pointTranslationIso_hom_apply (PicScheme C)
        (MonObj.one (X := PicScheme C)) p (default : Spec (.of k))
  have h := e.image_connectedComponentIn (s := Set.univ) (x := onePoint)
    (Set.mem_univ onePoint)
  rw [sectionComponentOpen, Scheme.Hom.coe_image,
    GroupScheme.coe_identityComponentOpens]
  change e '' connectedComponent onePoint = connectedComponent pPoint
  simpa [connectedComponentIn_univ, hp] using h

/-- The connected component through `p`, with its structural morphism to
`Spec k`. -/
noncomputable def sectionComponentOver
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ PicScheme C) :
    Over (Spec (.of k)) :=
  Over.mk ((sectionComponentOpen C p).ι ≫ (PicScheme C).hom)

/-- Translation identifies `Pic⁰` with the connected component through the
global section `p`, as schemes over `Spec k`. -/
noncomputable def sectionComponentIso
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ PicScheme C) :
    Pic0Scheme C ≅ sectionComponentOver C p :=
  Scheme.openImageIsoOver (sectionTranslation C p)
    (GroupScheme.identityComponentOpens (PicScheme C))

end PicScheme
end Scheme
end AlgebraicGeometry
