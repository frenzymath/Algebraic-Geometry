/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorSubschemeOverlap
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Global functions on the intrinsic divisor

The structure sheaf condition identifies global functions on the intrinsic divisor with
the widened colength equalizer `AffAdaptation.gluedSubalgebra`.  The comparison is built
from the arbitrary adapted affine cover and is independent of certification.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

/-- Restrict a global function on the divisor to every adapted affine piece. -/
noncomputable def divisorGlobalToPiecesRingHom [IsProper C.hom]
    (A : AffAdaptation D d) :
    Γ(A.divisorSubscheme, ⊤) →+* A.chartProd :=
  RingHom.pi fun i =>
    (A.divisorSubschemePieceRingEquiv i).toRingHom.comp
      (A.divisorSubscheme.presheaf.map
        (homOfLE (le_top :
          A.divisorSubschemeι ⁻¹ᵁ D.pieces i ≤
            (⊤ : A.divisorSubscheme.Opens))).op).hom

lemma divisorGlobalToPiecesRingHom_apply [IsProper C.hom]
    (A : AffAdaptation D d) (s : Γ(A.divisorSubscheme, ⊤)) (i : D.index) :
    A.divisorGlobalToPiecesRingHom s i =
      A.divisorSubschemePieceRingEquiv i
        ((A.divisorSubscheme.presheaf.map
          (homOfLE (le_top :
            A.divisorSubschemeι ⁻¹ᵁ D.pieces i ≤
              (⊤ : A.divisorSubscheme.Opens))).op).hom s) :=
  rfl

/-- Piecewise restrictions of a global divisor function satisfy the existing overlap
equalizer relation. -/
lemma divisorGlobalToPieces_mem [IsProper C.hom]
    (A : AffAdaptation D d) (s : Γ(A.divisorSubscheme, ⊤)) :
    A.divisorGlobalToPiecesRingHom s ∈ A.gluedSubalgebra := by
  rw [A.mem_gluedSubalgebra_iff, A.mem_gluedSubmodule_iff]
  intro p
  let sf := fun i : D.index =>
    A.divisorSubscheme.presheaf.map
      (homOfLE (le_top :
        A.divisorSubschemeι ⁻¹ᵁ D.pieces i ≤
          (⊤ : A.divisorSubscheme.Opens))).op s
  have hcomp : TopCat.Presheaf.IsCompatible A.divisorSubscheme.presheaf
      (fun i : D.index => A.divisorSubschemeι ⁻¹ᵁ D.pieces i) sf := by
    intro i j
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← A.divisorSubscheme.presheaf.map_comp,
      ← A.divisorSubscheme.presheaf.map_comp]
    rfl
  have hleft := congrArg
    (fun f => f.hom (sf p.1))
    (A.divisorSubschemePieceIso_res_left p.1 p.2)
  have hright := congrArg
    (fun f => f.hom (sf p.2))
    (A.divisorSubschemePieceIso_res_right p.1 p.2)
  change A.toOvlLeft p.1 p.2
      ((A.divisorSubschemePieceIso p.1).hom.hom (sf p.1)) =
    A.toOvlRight p.1 p.2
      ((A.divisorSubschemePieceIso p.2).hom.hom (sf p.2))
  calc
    _ = (A.divisorSubschemeOverlapIso p.1 p.2).hom.hom
        (A.divisorSubscheme.presheaf.map
          (Opens.infLELeft
            (A.divisorSubschemeι ⁻¹ᵁ D.pieces p.1)
            (A.divisorSubschemeι ⁻¹ᵁ D.pieces p.2)).op (sf p.1)) := hleft.symm
    _ = (A.divisorSubschemeOverlapIso p.1 p.2).hom.hom
        (A.divisorSubscheme.presheaf.map
          (Opens.infLERight
            (A.divisorSubschemeι ⁻¹ᵁ D.pieces p.1)
            (A.divisorSubschemeι ⁻¹ᵁ D.pieces p.2)).op (sf p.2)) := by
      rw [hcomp p.1 p.2]
    _ = _ := hright

/-- The global restriction map, with codomain narrowed to the widened equalizer algebra. -/
noncomputable def divisorGlobalToGluedRingHom [IsProper C.hom]
    (A : AffAdaptation D d) :
    Γ(A.divisorSubscheme, ⊤) →+* ↑(gluedSubalgebra A) :=
  RingHom.codRestrict A.divisorGlobalToPiecesRingHom
    (gluedSubalgebra A) A.divisorGlobalToPieces_mem

lemma divisorGlobalToGluedRingHom_apply [IsProper C.hom]
    (A : AffAdaptation D d) (s : Γ(A.divisorSubscheme, ⊤)) (i : D.index) :
    (A.divisorGlobalToGluedRingHom s).1 i =
      A.divisorSubschemePieceRingEquiv i
        ((A.divisorSubscheme.presheaf.map
          (homOfLE (le_top :
            A.divisorSubschemeι ⁻¹ᵁ D.pieces i ≤
              (⊤ : A.divisorSubscheme.Opens))).op).hom s) :=
  rfl

/-- The inverse images of the adapted pieces cover the entire divisor subscheme. -/
theorem iSup_divisorSubscheme_preimage_pieces [IsProper C.hom]
    (A : AffAdaptation D d) :
    ⨆ i : D.index, A.divisorSubschemeι ⁻¹ᵁ D.pieces i = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨i, hi⟩ := D.exists_mem_pieces (A.divisorSubschemeι x)
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

/-- An element of the widened equalizer gives a compatible family of divisor-piece
sections through the local quotient identifications. -/
lemma divisorGluedFamily_compatible [IsProper C.hom]
    (A : AffAdaptation D d) (x : ↑(gluedSubalgebra A)) :
    TopCat.Presheaf.IsCompatible A.divisorSubscheme.presheaf
      (fun i : D.index => A.divisorSubschemeι ⁻¹ᵁ D.pieces i)
      (fun i => (A.divisorSubschemePieceIso i).inv.hom (x.1 i)) := by
  intro i j
  apply (ConcreteCategory.bijective_of_isIso
    (A.divisorSubschemeOverlapIso i j).hom).injective
  change (A.divisorSubschemeOverlapIso i j).hom.hom
      ((A.divisorSubscheme.presheaf.map
        (homOfLE (show A.divisorSubschemeι ⁻¹ᵁ (D.pieces i ⊓ D.pieces j) ≤
          A.divisorSubschemeι ⁻¹ᵁ D.pieces i by
            intro y hy
            exact hy.1)).op).hom
        ((A.divisorSubschemePieceIso i).inv.hom (x.1 i))) =
    (A.divisorSubschemeOverlapIso i j).hom.hom
      ((A.divisorSubscheme.presheaf.map
        (homOfLE (show A.divisorSubschemeι ⁻¹ᵁ (D.pieces i ⊓ D.pieces j) ≤
          A.divisorSubschemeι ⁻¹ᵁ D.pieces j by
            intro y hy
            exact hy.2)).op).hom
        ((A.divisorSubschemePieceIso j).inv.hom (x.1 j)))
  have hleft := congrArg
    (fun f => f.hom ((A.divisorSubschemePieceIso i).inv.hom (x.1 i)))
    (A.divisorSubschemePieceIso_res_left i j)
  have hright := congrArg
    (fun f => f.hom ((A.divisorSubschemePieceIso j).inv.hom (x.1 j)))
    (A.divisorSubschemePieceIso_res_right i j)
  calc
    _ = A.toOvlLeft i j
        ((A.divisorSubschemePieceIso i).hom.hom
          ((A.divisorSubschemePieceIso i).inv.hom (x.1 i))) := hleft
    _ = A.toOvlLeft i j (x.1 i) := by rw [Iso.inv_hom_id_apply]
    _ = A.toOvlRight i j (x.1 j) :=
      (A.mem_gluedSubmodule_iff x.1).mp x.2 (i, j)
    _ = A.toOvlRight i j
        ((A.divisorSubschemePieceIso j).hom.hom
          ((A.divisorSubschemePieceIso j).inv.hom (x.1 j))) := by
      rw [Iso.inv_hom_id_apply]
    _ = _ := hright.symm

/-- Every element of the widened equalizer is the family of restrictions of a global
function on the intrinsic divisor. -/
lemma divisorGlobalToGlued_surjective [IsProper C.hom]
    (A : AffAdaptation D d) :
    Function.Surjective A.divisorGlobalToGluedRingHom := by
  intro x
  let U : D.index → A.divisorSubscheme.Opens :=
    fun i => A.divisorSubschemeι ⁻¹ᵁ D.pieces i
  let sf : ∀ i, Γ(A.divisorSubscheme, U i) :=
    fun i => (A.divisorSubschemePieceIso i).inv.hom (x.1 i)
  have hcover : (⊤ : A.divisorSubscheme.Opens) ≤ ⨆ i, U i := by
    exact le_of_eq (A.iSup_divisorSubscheme_preimage_pieces).symm
  obtain ⟨s, hs, -⟩ :=
    A.divisorSubscheme.sheaf.existsUnique_gluing'
      U ⊤ (fun i => homOfLE le_top) hcover sf
        (A.divisorGluedFamily_compatible x)
  refine ⟨s, ?_⟩
  apply Subtype.ext
  funext i
  change (A.divisorSubschemePieceIso i).hom.hom
      ((A.divisorSubscheme.presheaf.map
        (homOfLE (le_top :
          U i ≤ (⊤ : A.divisorSubscheme.Opens))).op).hom s) =
    x.1 i
  have hsi := hs i
  change (A.divisorSubscheme.presheaf.map
    (homOfLE (le_top :
      U i ≤ (⊤ : A.divisorSubscheme.Opens))).op).hom s =
      (A.divisorSubschemePieceIso i).inv.hom (x.1 i) at hsi
  rw [hsi, Iso.inv_hom_id_apply]

/-- A global function on the intrinsic divisor is determined by its restrictions to the
adapted pieces. -/
lemma divisorGlobalToGlued_injective [IsProper C.hom]
    (A : AffAdaptation D d) :
    Function.Injective A.divisorGlobalToGluedRingHom := by
  intro s t hst
  let U : D.index → A.divisorSubscheme.Opens :=
    fun i => A.divisorSubschemeι ⁻¹ᵁ D.pieces i
  have hcover : (⊤ : A.divisorSubscheme.Opens) ≤ ⨆ i, U i := by
    exact le_of_eq (A.iSup_divisorSubscheme_preimage_pieces).symm
  apply A.divisorSubscheme.sheaf.eq_of_locally_eq'
    U ⊤ (fun i => homOfLE le_top) hcover
  intro i
  apply (ConcreteCategory.bijective_of_isIso
    (A.divisorSubschemePieceIso i).hom).injective
  have hi := congrArg
    (fun z : ↑(gluedSubalgebra A) => z.1 i) hst
  change (A.divisorSubschemePieceIso i).hom.hom
      ((A.divisorSubscheme.presheaf.map
        (homOfLE (le_top :
          U i ≤ (⊤ : A.divisorSubscheme.Opens))).op).hom s) =
    (A.divisorSubschemePieceIso i).hom.hom
      ((A.divisorSubscheme.presheaf.map
        (homOfLE (le_top :
          U i ≤ (⊤ : A.divisorSubscheme.Opens))).op).hom t) at hi
  exact hi

/-- Global functions on the intrinsic divisor are the widened glued equalizer algebra. -/
noncomputable def divisorGlobalSectionsEquivGlued [IsProper C.hom]
    (A : AffAdaptation D d) :
    Γ(A.divisorSubscheme, ⊤) ≃+* ↑(gluedSubalgebra A) :=
  RingEquiv.ofBijective A.divisorGlobalToGluedRingHom
    ⟨A.divisorGlobalToGlued_injective,
      A.divisorGlobalToGlued_surjective⟩

lemma divisorGlobalSectionsEquivGlued_apply [IsProper C.hom]
    (A : AffAdaptation D d) (s : Γ(A.divisorSubscheme, ⊤))
    (i : D.index) :
    (A.divisorGlobalSectionsEquivGlued s).1 i =
      A.divisorSubschemePieceRingEquiv i
        ((A.divisorSubscheme.presheaf.map
          (homOfLE (le_top :
            A.divisorSubschemeι ⁻¹ᵁ D.pieces i ≤
              (⊤ : A.divisorSubscheme.Opens))).op).hom s) :=
  rfl

end AffAdaptation

end AlgebraicGeometry
