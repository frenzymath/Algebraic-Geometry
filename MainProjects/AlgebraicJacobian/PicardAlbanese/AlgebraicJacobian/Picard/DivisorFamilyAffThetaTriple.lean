/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaCoaction

/-!
# Triple-overlap restrictions for intrinsic theta descent

Coassociativity of the theta descent coaction is the cocycle law on triple intersections.
This file constructs the common target without choosing a chart: on
`(U_i inter U_j) inter U_l` it quotients theta sections by the intrinsic Cartier ideal.
Every pairwise theta quotient restricts to this target, and the three ways of restricting
a piece section agree there.  The proofs are the sheaf identity `secRes_secRes` on quotient
generators; no containment or additional family hypothesis is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsProper C.hom]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

/-- The triple intersection, parenthesized to match the first pair of Cech indices. -/
noncomputable abbrev thetaTripleOpen (_A : AffAdaptation D d)
    (i j l : D.index) : (relCurve C R).Opens :=
  (D.pieces i ⊓ D.pieces j) ⊓ D.pieces l

/-- A triple intersection of widened affine pieces is affine. -/
theorem isAffineOpen_thetaTripleOpen (A : AffAdaptation D d)
    (i j l : D.index) : IsAffineOpen (A.thetaTripleOpen i j l) :=
  Over.isAffineOpen_inf C
    (D.hasAffineOverlaps_of_isProper i j) (D.isAffineOpen l)

/-- The triple intersection as an affine open, for the intrinsic Cartier ideal API. -/
noncomputable def thetaTripleAffineOpen (A : AffAdaptation D d)
    (i j l : D.index) : (relCurve C R).affineOpens :=
  ⟨A.thetaTripleOpen i j l, A.isAffineOpen_thetaTripleOpen i j l⟩

/-- Intrinsic theta sections on a triple intersection. -/
noncomputable abbrev ThetaTripleSections (_A : AffAdaptation D d) (a : ℕ)
    (i j l : D.index) : Type u :=
  (thetaChartDatum C R π a).sheaf.obj.obj
    (op ((D.pieces i ⊓ D.pieces j) ⊓ D.pieces l))

/-- An affine sections model on a triple intersection. -/
noncomputable def thetaTripleSectionsModel (A : AffAdaptation D d) (a : ℕ)
    (i j l : D.index) :
    (thetaChartDatum C R π a).AffineSectionsModel (A.thetaTripleOpen i j l) :=
  Classical.choice ((thetaChartDatum C R π a).nonempty_affineSectionsModel
    (A.thetaTripleOpen i j l) (A.isAffineOpen_thetaTripleOpen i j l))

/-- The section-ring action on theta sections over a triple intersection. -/
@[reducible]
noncomputable def thetaTripleSectionsModule (A : AffAdaptation D d) (a : ℕ)
    (i j l : D.index) :
    Module Γ(relCurve C R, A.thetaTripleOpen i j l)
      (A.ThetaTripleSections (π := π) a i j l) :=
  letI : Scheme.QcohOn (thetaChartDatum C R π a).sheaf
      (A.thetaTripleOpen i j l) :=
    (A.thetaTripleSectionsModel (π := π) a i j l).qcoh
  Scheme.QcohOn.moduleOfLE (F := (thetaChartDatum C R π a).sheaf)
    (le_refl (A.thetaTripleOpen i j l))

attribute [local instance] thetaOverlapSectionsModule thetaTripleSectionsModule

/-- The intrinsic Cartier ideal on a triple intersection. -/
noncomputable abbrev thetaTripleIdeal (A : AffAdaptation D d)
    (i j l : D.index) : Ideal Γ(relCurve C R, A.thetaTripleOpen i j l) :=
  A.cartierIdeal.ideal (A.thetaTripleAffineOpen i j l)

/-- Theta sections killed by the intrinsic divisor on a triple intersection. -/
@[reducible]
noncomputable def thetaTripleVanishing (A : AffAdaptation D d) (a : ℕ)
    (i j l : D.index) :
    Submodule Γ(relCurve C R, A.thetaTripleOpen i j l)
      (A.ThetaTripleSections (π := π) a i j l) :=
  A.thetaTripleIdeal i j l • ⊤

/-- Intrinsic theta sections restricted to the divisor on a triple intersection. -/
noncomputable abbrev ThetaTripleQuotient (A : AffAdaptation D d) (a : ℕ)
    (i j l : D.index) : Type u :=
  A.ThetaTripleSections (π := π) a i j l ⧸
    A.thetaTripleVanishing (π := π) a i j l

/-- The intrinsic divisor ring on a triple intersection. -/
noncomputable abbrev tripleColength (A : AffAdaptation D d)
    (i j l : D.index) : Type u :=
  Γ(relCurve C R, A.thetaTripleOpen i j l) ⧸ A.thetaTripleIdeal i j l

/-- The triple-colength action on the triple theta quotient. -/
@[reducible]
noncomputable def thetaTripleQuotientModule (A : AffAdaptation D d) (a : ℕ)
    (i j l : D.index) :
    Module (A.tripleColength i j l)
      (A.ThetaTripleQuotient (π := π) a i j l) := by
  letI := A.thetaTripleSectionsModule (π := π) a i j l
  change Module
    (Γ(relCurve C R, A.thetaTripleOpen i j l) ⧸ A.thetaTripleIdeal i j l)
    (A.ThetaTripleSections (π := π) a i j l ⧸
      A.thetaTripleIdeal i j l •
        (⊤ : Submodule Γ(relCurve C R, A.thetaTripleOpen i j l)
          (A.ThetaTripleSections (π := π) a i j l)))
  infer_instance

omit [IsProper C.hom] in
/-- The triple intersection lies in its first pairwise intersection. -/
theorem thetaTripleOpen_le_pair12 (A : AffAdaptation D d) (i j l : D.index) :
    A.thetaTripleOpen i j l ≤ D.pieces i ⊓ D.pieces j :=
  inf_le_left

omit [IsProper C.hom] in
/-- The triple intersection lies in the first/third pairwise intersection. -/
theorem thetaTripleOpen_le_pair13 (A : AffAdaptation D d) (i j l : D.index) :
    A.thetaTripleOpen i j l ≤ D.pieces i ⊓ D.pieces l := by
  intro x hx
  exact ⟨hx.1.1, hx.2⟩

omit [IsProper C.hom] in
/-- The triple intersection lies in the second/third pairwise intersection. -/
theorem thetaTripleOpen_le_pair23 (A : AffAdaptation D d) (i j l : D.index) :
    A.thetaTripleOpen i j l ≤ D.pieces j ⊓ D.pieces l := by
  intro x hx
  exact ⟨hx.1.2, hx.2⟩

/-- Restriction of theta sections from any pairwise intersection to a fixed triple
intersection. -/
noncomputable def thetaOverlapSectionsToTriple (A : AffAdaptation D d) (a : ℕ)
    (p q i j l : D.index)
    (h : A.thetaTripleOpen i j l ≤ D.pieces p ⊓ D.pieces q) :
    A.ThetaOverlapSections (π := π) a p q →ₛₗ[
      (relResAlgHom C R h).toRingHom]
      A.ThetaTripleSections (π := π) a i j l := by
  let MP := A.thetaOverlapSectionsModel (π := π) a p q
  let MT := A.thetaTripleSectionsModel (π := π) a i j l
  letI : Scheme.QcohOn (thetaChartDatum C R π a).sheaf
      (D.pieces p ⊓ D.pieces q) := MP.qcoh
  letI : Scheme.QcohOn (thetaChartDatum C R π a).sheaf
      (A.thetaTripleOpen i j l) := MT.qcoh
  refine
    { toFun := secRes (thetaChartDatum C R π a).sheaf h
      map_add' := (secRes (thetaChartDatum C R π a).sheaf h).map_add
      map_smul' := fun r s => ?_ }
  change
    secRes (thetaChartDatum C R π a).sheaf h
        (Scheme.QcohOn.qsmul (F := (thetaChartDatum C R π a).sheaf)
          (le_refl (D.pieces p ⊓ D.pieces q)) r s) =
      Scheme.QcohOn.qsmul (F := (thetaChartDatum C R π a).sheaf)
        (le_refl (A.thetaTripleOpen i j l))
        ((relResAlgHom C R h).toRingHom r)
        (secRes (thetaChartDatum C R π a).sheaf h s)
  rw [MP.qsmul_eq, MT.qsmul_eq]
  exact (gluedRes_gluedQsmul R (thetaChartDatum C R π a).pieces
      (thetaChartDatum C R π a).unit h
      (le_refl (D.pieces p ⊓ D.pieces q)) r s).trans
    (gluedQsmul_res R (thetaChartDatum C R π a).pieces
      (thetaChartDatum C R π a).unit
      (le_refl (A.thetaTripleOpen i j l)) h r
      (gluedRes R (thetaChartDatum C R π a).pieces
        (thetaChartDatum C R π a).unit h s)).symm

/-- Restriction carries the pairwise divisor ideal into the intrinsic divisor ideal on
the triple intersection. -/
theorem relRes_mem_thetaTripleIdeal_of_mem_ovlIdeal
    (A : AffAdaptation D d) (p q i j l : D.index)
    (h : A.thetaTripleOpen i j l ≤ D.pieces p ⊓ D.pieces q)
    (r : Γ(relCurve C R, D.pieces p ⊓ D.pieces q)) (hr : r ∈ A.ovlIdeal p q) :
    relResAlgHom C R h r ∈ A.thetaTripleIdeal i j l := by
  let UP : (relCurve C R).affineOpens :=
    ⟨D.pieces p ⊓ D.pieces q, D.hasAffineOverlaps_of_isProper p q⟩
  let UT := A.thetaTripleAffineOpen i j l
  have hUT : UT ≤ UP := h
  have hr' : r ∈ A.cartierIdeal.ideal UP := by
    rw [A.cartierIdeal_ideal_overlap_eq_ovlIdeal p q]
    exact hr
  have hmap := A.cartierIdeal.map_ideal hUT
  have hh : hUT = h := Subsingleton.elim _ _
  rw [hh] at hmap
  have hmraw :
      ((relCurve C R).presheaf.map (homOfLE h).op).hom r ∈
        A.cartierIdeal.ideal UT := by
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hr'
  simpa [relResAlgHom, thetaTripleIdeal, UT] using hmraw

/-- Pairwise Cartier-vanishing theta sections restrict to Cartier-vanishing sections on
the triple intersection. -/
theorem thetaOverlapSectionsToTriple_vanishing_le
    (A : AffAdaptation D d) (a : ℕ) (p q i j l : D.index)
    (h : A.thetaTripleOpen i j l ≤ D.pieces p ⊓ D.pieces q) :
    A.thetaOverlapVanishing (π := π) a p q ≤
      Submodule.comap (A.thetaOverlapSectionsToTriple (π := π) a p q i j l h)
        (A.thetaTripleVanishing (π := π) a i j l) := by
  change A.ovlIdeal p q •
      (⊤ : Submodule Γ(relCurve C R, D.pieces p ⊓ D.pieces q)
        (A.ThetaOverlapSections (π := π) a p q)) ≤ _
  rw [Submodule.smul_le]
  intro r hr s _
  change A.thetaOverlapSectionsToTriple (π := π) a p q i j l h (r • s) ∈
    A.thetaTripleIdeal i j l •
      (⊤ : Submodule Γ(relCurve C R, A.thetaTripleOpen i j l)
        (A.ThetaTripleSections (π := π) a i j l))
  rw [(A.thetaOverlapSectionsToTriple (π := π) a p q i j l h).map_smulₛₗ]
  apply Submodule.smul_mem_smul ?_ Submodule.mem_top
  exact A.relRes_mem_thetaTripleIdeal_of_mem_ovlIdeal p q i j l h r hr

/-- Restriction induced on pairwise theta quotients. -/
noncomputable def thetaOverlapToTriple (A : AffAdaptation D d) (a : ℕ)
    (p q i j l : D.index)
    (h : A.thetaTripleOpen i j l ≤ D.pieces p ⊓ D.pieces q) :
    A.ThetaOverlapQuotient (π := π) a p q →ₛₗ[(relResAlgHom C R h).toRingHom]
      A.ThetaTripleQuotient (π := π) a i j l :=
  Submodule.mapQ (A.thetaOverlapVanishing (π := π) a p q)
    (A.thetaTripleVanishing (π := π) a i j l)
    (A.thetaOverlapSectionsToTriple (π := π) a p q i j l h)
    (A.thetaOverlapSectionsToTriple_vanishing_le (π := π) a p q i j l h)

@[simp]
theorem thetaOverlapToTriple_mk (A : AffAdaptation D d) (a : ℕ)
    (p q i j l : D.index)
    (h : A.thetaTripleOpen i j l ≤ D.pieces p ⊓ D.pieces q)
    (s : A.ThetaOverlapSections (π := π) a p q) :
    A.thetaOverlapToTriple (π := π) a p q i j l h (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk (secRes (thetaChartDatum C R π a).sheaf h s) :=
  rfl

/-- Restricting a section of the first piece through either adjacent pair gives the same
class on the triple intersection. -/
theorem thetaToTriple_from_first (A : AffAdaptation D d) (a : ℕ)
    (i j l : D.index) (x : A.ThetaPieceQuotient (π := π) a i) :
    A.thetaOverlapToTriple (π := π) a i j i j l
        (A.thetaTripleOpen_le_pair12 i j l)
        (A.thetaToOverlapLeft (π := π) a i j x) =
      A.thetaOverlapToTriple (π := π) a i l i j l
        (A.thetaTripleOpen_le_pair13 i j l)
        (A.thetaToOverlapLeft (π := π) a i l x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ s =>
      rw [A.thetaToOverlapLeft_mk, A.thetaToOverlapLeft_mk,
        A.thetaOverlapToTriple_mk, A.thetaOverlapToTriple_mk,
        secRes_secRes, secRes_secRes]

/-- Restricting a section of the second piece through either adjacent pair gives the same
class on the triple intersection. -/
theorem thetaToTriple_from_second (A : AffAdaptation D d) (a : ℕ)
    (i j l : D.index) (x : A.ThetaPieceQuotient (π := π) a j) :
    A.thetaOverlapToTriple (π := π) a i j i j l
        (A.thetaTripleOpen_le_pair12 i j l)
        (A.thetaToOverlapRight (π := π) a i j x) =
      A.thetaOverlapToTriple (π := π) a j l i j l
        (A.thetaTripleOpen_le_pair23 i j l)
        (A.thetaToOverlapLeft (π := π) a j l x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ s =>
      rw [A.thetaToOverlapRight_mk, A.thetaToOverlapLeft_mk,
        A.thetaOverlapToTriple_mk, A.thetaOverlapToTriple_mk,
        secRes_secRes, secRes_secRes]

/-- Restricting a section of the third piece through either adjacent pair gives the same
class on the triple intersection. -/
theorem thetaToTriple_from_third (A : AffAdaptation D d) (a : ℕ)
    (i j l : D.index) (x : A.ThetaPieceQuotient (π := π) a l) :
    A.thetaOverlapToTriple (π := π) a i l i j l
        (A.thetaTripleOpen_le_pair13 i j l)
        (A.thetaToOverlapRight (π := π) a i l x) =
      A.thetaOverlapToTriple (π := π) a j l i j l
        (A.thetaTripleOpen_le_pair23 i j l)
        (A.thetaToOverlapRight (π := π) a j l x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ s =>
      rw [A.thetaToOverlapRight_mk, A.thetaToOverlapRight_mk,
        A.thetaOverlapToTriple_mk, A.thetaOverlapToTriple_mk,
        secRes_secRes, secRes_secRes]

end AffAdaptation

end AlgebraicGeometry
