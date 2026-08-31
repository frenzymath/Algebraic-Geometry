/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffMapAlg
import AlgebraicJacobian.Picard.DivisorFamilyAffTheta
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaRestriction
import AlgebraicJacobian.Algebra.PiInvertible
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Intrinsic theta descent on a widened divisor cover

For an arbitrary affine piece `U_j`, the restriction of `O(a Theta)` to the divisor is
the genuine module

`Gamma(U_j, O(a Theta)) / (f_j) Gamma(U_j, O(a Theta))`.

Unlike the older chart-typed theta module, this quotient does not choose a trivialization
of the line bundle on `U_j`.  Restriction to `U_i inter U_j` sends the equation-generated
submodule into the symmetric overlap ideal, so the piece quotients have two canonical
overlap maps.  Their equalizer is the intrinsic theta restriction on the widened divisor.

The construction below supplies the module that the widened equalizer algebra acts on.
It is the chart-free input for proving invertibility and identifying the result with the
cover-independent high-window quotient.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

section GluedQsmul

variable (B : Type u) [CommRing B] {X : Scheme.{u}} [X.Over (Spec (.of B))]
variable {J : Type u} (U : J -> X.Opens) (g : forall i j : J, Γ(X, U i ⊓ U j)ˣ)

/-- Componentwise multiplication is independent of whether a scalar is first restricted
to an intermediate open. -/
theorem gluedQsmul_res {V W Z : X.Opens} (hWV : W ≤ V) (hVZ : V ≤ Z)
    (r : Γ(X, Z)) (s : ↑(gluedSubmodule B U g W)) :
    gluedQsmul B U g hWV (X.resHom hVZ r) s =
      gluedQsmul B U g (hWV.trans hVZ) r s := by
  apply Subtype.ext
  funext j
  rw [gluedQsmul_coe, gluedQsmul_coe]
  simp only [Scheme.resHom_resHom]

end GluedQsmul

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsProper C.hom]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

/-- Intrinsic theta sections on the affine overlap of two widened pieces. -/
noncomputable abbrev ThetaOverlapSections (_A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) : Type u :=
  (thetaChartDatum C R π a).sheaf.obj.obj (op (D.pieces i ⊓ D.pieces j))

/-- A finite projective invertible sections model on a piece overlap.  Properness of the
curve makes the intersection of the two affine pieces affine. -/
noncomputable def thetaOverlapSectionsModel (_A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    (thetaChartDatum C R π a).AffineSectionsModel (D.pieces i ⊓ D.pieces j) :=
  Classical.choice ((thetaChartDatum C R π a).nonempty_affineSectionsModel
    (D.pieces i ⊓ D.pieces j) (D.hasAffineOverlaps_of_isProper i j))

/-- The overlap-ring action on intrinsic theta sections. -/
@[reducible]
noncomputable def thetaOverlapSectionsModule (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    Module Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ThetaOverlapSections (π := π) a i j) :=
  letI : Scheme.QcohOn (thetaChartDatum C R π a).sheaf (D.pieces i ⊓ D.pieces j) :=
    (A.thetaOverlapSectionsModel (π := π) a i j).qcoh
  Scheme.QcohOn.moduleOfLE (F := (thetaChartDatum C R π a).sheaf)
    (le_refl (D.pieces i ⊓ D.pieces j))

attribute [local instance] thetaPieceSectionsModule thetaOverlapSectionsModule

/-- The equation-generated submodule of theta sections on one piece. -/
@[reducible]
noncomputable def thetaPieceVanishing (A : AffAdaptation D d) (a : ℕ)
    (j : D.index) :
    letI : Module Γ(relCurve C R, D.pieces j)
      (A.ThetaPieceSections (π := π) a j) :=
    A.thetaPieceSectionsModule (π := π) a j
    Submodule Γ(relCurve C R, D.pieces j)
      (A.ThetaPieceSections (π := π) a j) :=
  Ideal.span {A.eqn j} • ⊤

/-- The symmetric overlap ideal acting on intrinsic theta sections. -/
@[reducible]
noncomputable def thetaOverlapVanishing (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    letI : Module Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ThetaOverlapSections (π := π) a i j) :=
    A.thetaOverlapSectionsModule (π := π) a i j
    Submodule Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ThetaOverlapSections (π := π) a i j) :=
  A.ovlIdeal i j • ⊤

/-- Intrinsic theta sections restricted to the divisor on one widened piece. -/
noncomputable abbrev ThetaPieceQuotient (A : AffAdaptation D d) (a : ℕ)
    (j : D.index) : Type u :=
  letI : Module Γ(relCurve C R, D.pieces j)
      (A.ThetaPieceSections (π := π) a j) :=
    A.thetaPieceSectionsModule (π := π) a j
  A.ThetaPieceSections (π := π) a j ⧸ A.thetaPieceVanishing (π := π) a j

/-- Intrinsic theta sections modulo both equations on a piece overlap. -/
noncomputable abbrev ThetaOverlapQuotient (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) : Type u :=
  letI : Module Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ThetaOverlapSections (π := π) a i j) :=
    A.thetaOverlapSectionsModule (π := π) a i j
  A.ThetaOverlapSections (π := π) a i j ⧸
    A.thetaOverlapVanishing (π := π) a i j

/-- Base change of intrinsic theta sections to the symmetric overlap colength algebra. -/
noncomputable abbrev ThetaOverlapRestriction (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) : Type u :=
  letI : Module Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ThetaOverlapSections (π := π) a i j) :=
    A.thetaOverlapSectionsModule (π := π) a i j
  A.ovlColength i j ⊗[Γ(relCurve C R, D.pieces i ⊓ D.pieces j)]
    A.ThetaOverlapSections (π := π) a i j

/-- Global sections of the intrinsic theta sheaf before restricting to the divisor. -/
noncomputable abbrev ThetaGlobalSections (_A : AffAdaptation D d) (a : ℕ) : Type u :=
  (thetaChartDatum C R π a).sheaf.obj.obj (op (⊤ : (relCurve C R).Opens))

/-- The tensor restriction from the previous module is canonically the intrinsic quotient
by the local equation. -/
noncomputable def thetaPieceRestrictionEquiv (A : AffAdaptation D d) (a : ℕ)
    (j : D.index) :
    letI : Module Γ(relCurve C R, D.pieces j)
        (A.ThetaPieceSections (π := π) a j) :=
      A.thetaPieceSectionsModule (π := π) a j
    A.ThetaPieceRestriction (π := π) a j ≃ₗ[Γ(relCurve C R, D.pieces j)]
      A.ThetaPieceQuotient (π := π) a j :=
  TensorProduct.quotTensorEquivQuotSMul
    (A.ThetaPieceSections (π := π) a j) (Ideal.span {A.eqn j})

/-- Restriction of intrinsic theta sections from the left piece to an overlap. -/
noncomputable def thetaSectionsToOverlapLeft (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    letI : Module Γ(relCurve C R, D.pieces i)
        (A.ThetaPieceSections (π := π) a i) :=
      A.thetaPieceSectionsModule (π := π) a i
    letI : Module Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
        (A.ThetaOverlapSections (π := π) a i j) :=
      A.thetaOverlapSectionsModule (π := π) a i j
    A.ThetaPieceSections (π := π) a i →ₛₗ[
      (relResAlgHom C R (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i)).toRingHom]
      A.ThetaOverlapSections (π := π) a i j := by
  let Mi := A.thetaPieceSectionsModel (π := π) a i
  let Mij := A.thetaOverlapSectionsModel (π := π) a i j
  letI : Scheme.QcohOn (thetaChartDatum C R π a).sheaf (D.pieces i) := Mi.qcoh
  letI : Scheme.QcohOn (thetaChartDatum C R π a).sheaf
      (D.pieces i ⊓ D.pieces j) := Mij.qcoh
  refine
    { toFun := secRes (thetaChartDatum C R π a).sheaf inf_le_left
      map_add' := (secRes (thetaChartDatum C R π a).sheaf inf_le_left).map_add
      map_smul' := fun r s => ?_ }
  change
    secRes (thetaChartDatum C R π a).sheaf inf_le_left
        (Scheme.QcohOn.qsmul (F := (thetaChartDatum C R π a).sheaf)
          (le_refl (D.pieces i)) r s) =
      Scheme.QcohOn.qsmul (F := (thetaChartDatum C R π a).sheaf)
        (le_refl (D.pieces i ⊓ D.pieces j))
        ((relResAlgHom C R inf_le_left).toRingHom r)
        (secRes (thetaChartDatum C R π a).sheaf inf_le_left s)
  rw [Mi.qsmul_eq, Mij.qsmul_eq]
  exact (gluedRes_gluedQsmul R (thetaChartDatum C R π a).pieces
      (thetaChartDatum C R π a).unit inf_le_left (le_refl (D.pieces i)) r s).trans
    (gluedQsmul_res R (thetaChartDatum C R π a).pieces
      (thetaChartDatum C R π a).unit (le_refl (D.pieces i ⊓ D.pieces j))
      inf_le_left r (gluedRes R (thetaChartDatum C R π a).pieces
        (thetaChartDatum C R π a).unit inf_le_left s)).symm

/-- Restriction of intrinsic theta sections from the right piece to an overlap. -/
noncomputable def thetaSectionsToOverlapRight (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    letI : Module Γ(relCurve C R, D.pieces j)
        (A.ThetaPieceSections (π := π) a j) :=
      A.thetaPieceSectionsModule (π := π) a j
    letI : Module Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
        (A.ThetaOverlapSections (π := π) a i j) :=
      A.thetaOverlapSectionsModule (π := π) a i j
    A.ThetaPieceSections (π := π) a j →ₛₗ[
      (relResAlgHom C R (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j)).toRingHom]
      A.ThetaOverlapSections (π := π) a i j := by
  let Mj := A.thetaPieceSectionsModel (π := π) a j
  let Mij := A.thetaOverlapSectionsModel (π := π) a i j
  letI : Scheme.QcohOn (thetaChartDatum C R π a).sheaf (D.pieces j) := Mj.qcoh
  letI : Scheme.QcohOn (thetaChartDatum C R π a).sheaf
      (D.pieces i ⊓ D.pieces j) := Mij.qcoh
  refine
    { toFun := secRes (thetaChartDatum C R π a).sheaf inf_le_right
      map_add' := (secRes (thetaChartDatum C R π a).sheaf inf_le_right).map_add
      map_smul' := fun r s => ?_ }
  change
    secRes (thetaChartDatum C R π a).sheaf inf_le_right
        (Scheme.QcohOn.qsmul (F := (thetaChartDatum C R π a).sheaf)
          (le_refl (D.pieces j)) r s) =
      Scheme.QcohOn.qsmul (F := (thetaChartDatum C R π a).sheaf)
        (le_refl (D.pieces i ⊓ D.pieces j))
        ((relResAlgHom C R inf_le_right).toRingHom r)
        (secRes (thetaChartDatum C R π a).sheaf inf_le_right s)
  rw [Mj.qsmul_eq, Mij.qsmul_eq]
  exact (gluedRes_gluedQsmul R (thetaChartDatum C R π a).pieces
      (thetaChartDatum C R π a).unit inf_le_right (le_refl (D.pieces j)) r s).trans
    (gluedQsmul_res R (thetaChartDatum C R π a).pieces
      (thetaChartDatum C R π a).unit (le_refl (D.pieces i ⊓ D.pieces j))
      inf_le_right r (gluedRes R (thetaChartDatum C R π a).pieces
        (thetaChartDatum C R π a).unit inf_le_right s)).symm

/-- The left restriction sends equation multiples into the symmetric overlap ideal. -/
theorem thetaSectionsToOverlapLeft_vanishing_le (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    A.thetaPieceVanishing (π := π) a i ≤
      Submodule.comap (A.thetaSectionsToOverlapLeft (π := π) a i j)
        (A.thetaOverlapVanishing (π := π) a i j) := by
  change Ideal.span {A.eqn i} •
      (⊤ : Submodule Γ(relCurve C R, D.pieces i) (A.ThetaPieceSections (π := π) a i)) ≤
    Submodule.comap (A.thetaSectionsToOverlapLeft (π := π) a i j)
      (A.ovlIdeal i j •
        (⊤ : Submodule Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
          (A.ThetaOverlapSections (π := π) a i j)))
  rw [Submodule.smul_le]
  intro r hr s _
  change A.thetaSectionsToOverlapLeft (π := π) a i j (r • s) ∈
    A.ovlIdeal i j •
      (⊤ : Submodule Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
        (A.ThetaOverlapSections (π := π) a i j))
  rw [(A.thetaSectionsToOverlapLeft (π := π) a i j).map_smulₛₗ]
  apply Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [Ideal.mem_span_singleton] at hr
  obtain ⟨c, rfl⟩ := hr
  rw [map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))

/-- The right restriction sends equation multiples into the symmetric overlap ideal. -/
theorem thetaSectionsToOverlapRight_vanishing_le (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    A.thetaPieceVanishing (π := π) a j ≤
      Submodule.comap (A.thetaSectionsToOverlapRight (π := π) a i j)
        (A.thetaOverlapVanishing (π := π) a i j) := by
  change Ideal.span {A.eqn j} •
      (⊤ : Submodule Γ(relCurve C R, D.pieces j) (A.ThetaPieceSections (π := π) a j)) ≤
    Submodule.comap (A.thetaSectionsToOverlapRight (π := π) a i j)
      (A.ovlIdeal i j •
        (⊤ : Submodule Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
          (A.ThetaOverlapSections (π := π) a i j)))
  rw [Submodule.smul_le]
  intro r hr s _
  change A.thetaSectionsToOverlapRight (π := π) a i j (r • s) ∈
    A.ovlIdeal i j •
      (⊤ : Submodule Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
        (A.ThetaOverlapSections (π := π) a i j))
  rw [(A.thetaSectionsToOverlapRight (π := π) a i j).map_smulₛₗ]
  apply Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [Ideal.mem_span_singleton] at hr
  obtain ⟨c, rfl⟩ := hr
  rw [map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

/-! ## The symmetric overlap ideal is principal on either side -/

omit [IsProper C.hom] in
/-- On an arbitrary affine overlap, the restricted right equation lies in the principal
ideal generated by the restricted left equation.  This is stalk-locality of a regular
principal ideal together with the cover-independent stalk ideal of `d`. -/
lemma restrictedEqnRight_mem_span_left (A : AffAdaptation D d) (i j : D.index) :
    relResAlgHom C R
        (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j) (A.eqn j) ∈
      Ideal.span {relResAlgHom C R
        (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) (A.eqn i)} := by
  refine Scheme.mem_span_singleton_of_forall_germ (fun z hz => ?_) (fun z hz => ?_)
  · have hswap : ((relCurve C R).presheaf.germ
        (D.pieces i ⊓ D.pieces j) z hz).hom
          (relResAlgHom C R inf_le_left (A.eqn i)) =
        ((relCurve C R).presheaf.germ (D.pieces i) z hz.1).hom (A.eqn i) :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hswap]
    exact A.eqn_regular i z hz.1
  · have hswapL : ((relCurve C R).presheaf.germ
        (D.pieces i ⊓ D.pieces j) z hz).hom
          (relResAlgHom C R inf_le_left (A.eqn i)) =
        ((relCurve C R).presheaf.germ (D.pieces i) z hz.1).hom (A.eqn i) :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    have hswapR : ((relCurve C R).presheaf.germ
        (D.pieces i ⊓ D.pieces j) z hz).hom
          (relResAlgHom C R inf_le_right (A.eqn j)) =
        ((relCurve C R).presheaf.germ (D.pieces j) z hz.2).hom (A.eqn j) :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hswapL, hswapR, A.germ_eqn_span_eq_stalkIdeal i hz.1,
      ← A.germ_eqn_span_eq_stalkIdeal j hz.2]
    exact Ideal.subset_span rfl

omit [IsProper C.hom] in
/-- The left equation likewise lies in the principal ideal generated by the restricted
right equation. -/
lemma restrictedEqnLeft_mem_span_right (A : AffAdaptation D d) (i j : D.index) :
    relResAlgHom C R
        (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) (A.eqn i) ∈
      Ideal.span {relResAlgHom C R
        (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j) (A.eqn j)} := by
  refine Scheme.mem_span_singleton_of_forall_germ (fun z hz => ?_) (fun z hz => ?_)
  · have hswap : ((relCurve C R).presheaf.germ
        (D.pieces i ⊓ D.pieces j) z hz).hom
          (relResAlgHom C R inf_le_right (A.eqn j)) =
        ((relCurve C R).presheaf.germ (D.pieces j) z hz.2).hom (A.eqn j) :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hswap]
    exact A.eqn_regular j z hz.2
  · have hswapL : ((relCurve C R).presheaf.germ
        (D.pieces i ⊓ D.pieces j) z hz).hom
          (relResAlgHom C R inf_le_left (A.eqn i)) =
        ((relCurve C R).presheaf.germ (D.pieces i) z hz.1).hom (A.eqn i) :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    have hswapR : ((relCurve C R).presheaf.germ
        (D.pieces i ⊓ D.pieces j) z hz).hom
          (relResAlgHom C R inf_le_right (A.eqn j)) =
        ((relCurve C R).presheaf.germ (D.pieces j) z hz.2).hom (A.eqn j) :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hswapL, hswapR, A.germ_eqn_span_eq_stalkIdeal j hz.2,
      ← A.germ_eqn_span_eq_stalkIdeal i hz.1]
    exact Ideal.subset_span rfl

omit [IsProper C.hom] in
/-- The symmetric overlap ideal is already generated by the left equation. -/
lemma ovlIdeal_eq_span_left (A : AffAdaptation D d) (i j : D.index) :
    A.ovlIdeal i j = Ideal.span {relResAlgHom C R
      (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) (A.eqn i)} := by
  apply le_antisymm
  · rw [AffAdaptation.ovlIdeal, Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Ideal.subset_span rfl
    · exact A.restrictedEqnRight_mem_span_left i j
  · apply Ideal.span_mono
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Set.mem_insert _ _

omit [IsProper C.hom] in
/-- The symmetric overlap ideal is already generated by the right equation. -/
lemma ovlIdeal_eq_span_right (A : AffAdaptation D d) (i j : D.index) :
    A.ovlIdeal i j = Ideal.span {relResAlgHom C R
      (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j) (A.eqn j)} := by
  apply le_antisymm
  · rw [AffAdaptation.ovlIdeal, Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact A.restrictedEqnLeft_mem_span_right i j
    · exact Ideal.subset_span rfl
  · apply Ideal.span_mono
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Set.mem_insert_of_mem _ rfl

/-- The induced left overlap map on divisor-restricted theta sections. -/
noncomputable def thetaToOverlapLeft (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    A.ThetaPieceQuotient (π := π) a i →ₛₗ[
      (relResAlgHom C R (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i)).toRingHom]
      A.ThetaOverlapQuotient (π := π) a i j :=
  Submodule.mapQ (A.thetaPieceVanishing (π := π) a i)
    (A.thetaOverlapVanishing (π := π) a i j)
    (A.thetaSectionsToOverlapLeft (π := π) a i j)
    (A.thetaSectionsToOverlapLeft_vanishing_le (π := π) a i j)

/-- The induced right overlap map on divisor-restricted theta sections. -/
noncomputable def thetaToOverlapRight (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    A.ThetaPieceQuotient (π := π) a j →ₛₗ[
      (relResAlgHom C R (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j)).toRingHom]
      A.ThetaOverlapQuotient (π := π) a i j :=
  Submodule.mapQ (A.thetaPieceVanishing (π := π) a j)
    (A.thetaOverlapVanishing (π := π) a i j)
    (A.thetaSectionsToOverlapRight (π := π) a i j)
    (A.thetaSectionsToOverlapRight_vanishing_le (π := π) a i j)

/-! ## The intrinsic widened equalizer -/

/-- The canonical action of the piece colength algebra on intrinsic theta sections modulo
the piece equation. -/
@[reducible]
noncomputable def thetaPieceQuotientModule (A : AffAdaptation D d) (a : ℕ)
    (j : D.index) :
    Module (A.colength j) (A.ThetaPieceQuotient (π := π) a j) := by
  letI := A.thetaPieceSectionsModule (π := π) a j
  change Module
    (Γ(relCurve C R, D.pieces j) ⧸ Ideal.span {A.eqn j})
    (A.ThetaPieceSections (π := π) a j ⧸
      Ideal.span {A.eqn j} • (⊤ : Submodule Γ(relCurve C R, D.pieces j)
        (A.ThetaPieceSections (π := π) a j)))
  infer_instance

/-- The canonical action of the overlap colength algebra on intrinsic theta sections modulo
the symmetric overlap ideal. -/
@[reducible]
noncomputable def thetaOverlapQuotientModule (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    Module (A.ovlColength i j) (A.ThetaOverlapQuotient (π := π) a i j) := by
  letI := A.thetaOverlapSectionsModule (π := π) a i j
  change Module
    (Γ(relCurve C R, D.pieces i ⊓ D.pieces j) ⧸ A.ovlIdeal i j)
    (A.ThetaOverlapSections (π := π) a i j ⧸
      A.ovlIdeal i j •
        (⊤ : Submodule Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
          (A.ThetaOverlapSections (π := π) a i j)))
  infer_instance

/-- The base-ring action on a piece quotient, obtained by restricting its section-ring
action along `R -> Gamma(U_j, O)`. -/
@[reducible]
noncomputable def thetaPieceQuotientBaseModule (A : AffAdaptation D d) (a : ℕ)
    (j : D.index) : Module R (A.ThetaPieceQuotient (π := π) a j) :=
  letI : Module Γ(relCurve C R, D.pieces j) (A.ThetaPieceQuotient (π := π) a j) :=
    inferInstance
  Module.compHom (A.ThetaPieceQuotient (π := π) a j)
    (algebraMap R Γ(relCurve C R, D.pieces j))

/-- The base-ring action on an overlap quotient, obtained by restricting its overlap-ring
action along `R -> Gamma(U_i inter U_j, O)`. -/
@[reducible]
noncomputable def thetaOverlapQuotientBaseModule (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) : Module R (A.ThetaOverlapQuotient (π := π) a i j) :=
  letI : Module Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ThetaOverlapQuotient (π := π) a i j) := inferInstance
  Module.compHom (A.ThetaOverlapQuotient (π := π) a i j)
    (algebraMap R Γ(relCurve C R, D.pieces i ⊓ D.pieces j))

attribute [local instance] thetaPieceQuotientModule thetaOverlapQuotientModule
  thetaPieceQuotientBaseModule thetaOverlapQuotientBaseModule

@[simp]
lemma thetaToOverlapLeft_mk (A : AffAdaptation D d) (a : ℕ) (i j : D.index)
    (s : A.ThetaPieceSections (π := π) a i) :
    letI : Module Γ(relCurve C R, D.pieces i)
        (A.ThetaPieceSections (π := π) a i) :=
      A.thetaPieceSectionsModule (π := π) a i
    letI : Module Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
        (A.ThetaOverlapSections (π := π) a i j) :=
      A.thetaOverlapSectionsModule (π := π) a i j
    A.thetaToOverlapLeft (π := π) a i j (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk
        (secRes (thetaChartDatum C R π a).sheaf inf_le_left s) := by
  rfl

@[simp]
lemma thetaToOverlapRight_mk (A : AffAdaptation D d) (a : ℕ) (i j : D.index)
    (s : A.ThetaPieceSections (π := π) a j) :
    letI : Module Γ(relCurve C R, D.pieces j)
        (A.ThetaPieceSections (π := π) a j) :=
      A.thetaPieceSectionsModule (π := π) a j
    letI : Module Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
        (A.ThetaOverlapSections (π := π) a i j) :=
      A.thetaOverlapSectionsModule (π := π) a i j
    A.thetaToOverlapRight (π := π) a i j (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk
        (secRes (thetaChartDatum C R π a).sheaf inf_le_right s) := by
  rfl

/-- The tensor/quotient comparison is linear over the piece colength algebra, not merely
over the ambient section ring. -/
noncomputable def thetaPieceRestrictionEquivColength (A : AffAdaptation D d) (a : ℕ)
    (j : D.index) :
    A.ThetaPieceRestriction (π := π) a j ≃ₗ[A.colength j]
      A.ThetaPieceQuotient (π := π) a j := by
  let e := A.thetaPieceRestrictionEquiv (π := π) a j
  refine
    { __ := e.toEquiv
      map_add' := e.map_add
      map_smul' := fun c x => ?_ }
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  change e (r • x) = r • e x
  exact e.map_smul r x

/-- The tensor/quotient comparison on an overlap is linear over its symmetric colength
algebra. -/
noncomputable def thetaOverlapRestrictionEquivColength (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    A.ThetaOverlapRestriction (π := π) a i j ≃ₗ[A.ovlColength i j]
      A.ThetaOverlapQuotient (π := π) a i j := by
  let e := TensorProduct.quotTensorEquivQuotSMul
    (A.ThetaOverlapSections (π := π) a i j) (A.ovlIdeal i j)
  refine
    { __ := e.toEquiv
      map_add' := e.map_add
      map_smul' := fun c x => ?_ }
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  change e (r • x) = r • e x
  exact e.map_smul r x

omit [IsProper C.hom] in
/-- The canonical quotient model on a widened piece is invertible over that piece's
colength algebra. -/
theorem invertible_thetaPieceQuotient (A : AffAdaptation D d) (a : ℕ) (j : D.index) :
    Module.Invertible (A.colength j) (A.ThetaPieceQuotient (π := π) a j) := by
  letI : Module.Invertible (A.colength j) (A.ThetaPieceRestriction (π := π) a j) :=
    A.invertible_thetaPieceRestriction (π := π) a j
  exact Module.Invertible.congr (A.thetaPieceRestrictionEquivColength (π := π) a j)

/-- Base change of the intrinsic theta line to a symmetric overlap is invertible. -/
theorem invertible_thetaOverlapRestriction (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    Module.Invertible (A.ovlColength i j) (A.ThetaOverlapRestriction (π := π) a i j) := by
  let M := A.thetaOverlapSectionsModel (π := π) a i j
  letI : Scheme.QcohOn (thetaChartDatum C R π a).sheaf
      (D.pieces i ⊓ D.pieces j) := M.qcoh
  letI : Module Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ThetaOverlapSections (π := π) a i j) :=
    A.thetaOverlapSectionsModule (π := π) a i j
  haveI : Module.Invertible Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ThetaOverlapSections (π := π) a i j) := M.invertible
  change Module.Invertible (A.ovlColength i j)
    (A.ovlColength i j ⊗[Γ(relCurve C R, D.pieces i ⊓ D.pieces j)]
      A.ThetaOverlapSections (π := π) a i j)
  infer_instance

/-- The canonical quotient model on a widened overlap is invertible over the symmetric
overlap colength algebra. -/
theorem invertible_thetaOverlapQuotient (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    Module.Invertible (A.ovlColength i j)
      (A.ThetaOverlapQuotient (π := π) a i j) := by
  letI : Module.Invertible (A.ovlColength i j)
      (A.ThetaOverlapRestriction (π := π) a i j) :=
    A.invertible_thetaOverlapRestriction (π := π) a i j
  exact Module.Invertible.congr
    (A.thetaOverlapRestrictionEquivColength (π := π) a i j)

/-- Restrict a global intrinsic theta section to one widened piece and reduce it modulo
that piece's divisor equation. -/
noncomputable def intrinsicThetaPieceEval (A : AffAdaptation D d) (a : ℕ)
    (j : D.index) :
    A.ThetaGlobalSections (π := π) a →ₗ[R]
      A.ThetaPieceQuotient (π := π) a j := by
  let Mj := A.thetaPieceSectionsModel (π := π) a j
  letI : Scheme.QcohOn (thetaChartDatum C R π a).sheaf (D.pieces j) := Mj.qcoh
  letI : Module Γ(relCurve C R, D.pieces j)
      (A.ThetaPieceSections (π := π) a j) :=
    A.thetaPieceSectionsModule (π := π) a j
  letI : IsScalarTower R Γ(relCurve C R, D.pieces j)
      (A.ThetaPieceSections (π := π) a j) :=
    isScalarTower_coeff R (thetaChartDatum C R π a).pieces
      (thetaChartDatum C R π a).unit Mj.qsmul_eq (le_refl _)
  refine
    { toFun := fun s => Submodule.Quotient.mk
        (secRes (thetaChartDatum C R π a).sheaf le_top s)
      map_add' := fun x y => by
        rw [(secRes (thetaChartDatum C R π a).sheaf le_top).map_add]
        rfl
      map_smul' := fun r x => ?_ }
  change Submodule.Quotient.mk
      (secRes (thetaChartDatum C R π a).sheaf le_top (r • x)) =
    Submodule.Quotient.mk
      ((algebraMap R Γ(relCurve C R, D.pieces j) r) •
        secRes (thetaChartDatum C R π a).sheaf le_top x)
  rw [map_smul, IsScalarTower.algebraMap_smul]

/-- The left quotient restriction, viewed over the common test algebra `R`. -/
noncomputable def thetaToOverlapLeftLinear (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    A.ThetaPieceQuotient (π := π) a i →ₗ[R]
      A.ThetaOverlapQuotient (π := π) a i j := by
  let f := A.thetaToOverlapLeft (π := π) a i j
  refine
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r x => ?_ }
  change f ((algebraMap R Γ(relCurve C R, D.pieces i) r) • x) =
    (algebraMap R Γ(relCurve C R, D.pieces i ⊓ D.pieces j) r) • f x
  rw [f.map_smulₛₗ]
  congr 1
  exact (relResAlgHom C R
    (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i)).commutes r

/-- The right quotient restriction, viewed over the common test algebra `R`. -/
noncomputable def thetaToOverlapRightLinear (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    A.ThetaPieceQuotient (π := π) a j →ₗ[R]
      A.ThetaOverlapQuotient (π := π) a i j := by
  let f := A.thetaToOverlapRight (π := π) a i j
  refine
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r x => ?_ }
  change f ((algebraMap R Γ(relCurve C R, D.pieces j) r) • x) =
    (algebraMap R Γ(relCurve C R, D.pieces i ⊓ D.pieces j) r) • f x
  rw [f.map_smulₛₗ]
  congr 1
  exact (relResAlgHom C R
    (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j)).commutes r

/-- Product of the intrinsic divisor-restricted theta modules on the widened pieces. -/
noncomputable abbrev ThetaPieceProd (A : AffAdaptation D d) (a : ℕ) : Type u :=
  ∀ j : D.index, A.ThetaPieceQuotient (π := π) a j

/-- Product of the intrinsic divisor-restricted theta modules on pairwise overlaps. -/
noncomputable abbrev ThetaOverlapProd (A : AffAdaptation D d) (a : ℕ) : Type u :=
  ∀ p : D.index × D.index, A.ThetaOverlapQuotient (π := π) a p.1 p.2

omit [IsProper C.hom] in
/-- The product of the intrinsic theta quotient modules is invertible over the product of
the piece colength algebras. -/
theorem invertible_thetaPieceProd (A : AffAdaptation D d) (a : ℕ) :
    Module.Invertible A.chartProd (A.ThetaPieceProd (π := π) a) := by
  letI : forall j, Module.Invertible (A.colength j)
      (A.ThetaPieceQuotient (π := π) a j) :=
    fun j => A.invertible_thetaPieceQuotient (π := π) a j
  exact Module.Invertible.pi
    (R := fun j => A.colength j)
    (M := fun j => A.ThetaPieceQuotient (π := π) a j)

/-- Piecewise evaluation of a global theta section on the widened divisor cover. -/
noncomputable def intrinsicThetaEvalRaw (A : AffAdaptation D d) (a : ℕ) :
    A.ThetaGlobalSections (π := π) a →ₗ[R] A.ThetaPieceProd (π := π) a :=
  LinearMap.pi fun j => A.intrinsicThetaPieceEval (π := π) a j

omit [IsProper C.hom] in
@[simp]
lemma intrinsicThetaEvalRaw_apply (A : AffAdaptation D d) (a : ℕ)
    (s : A.ThetaGlobalSections (π := π) a) (j : D.index) :
    letI : Module Γ(relCurve C R, D.pieces j)
        (A.ThetaPieceSections (π := π) a j) :=
      A.thetaPieceSectionsModule (π := π) a j
    A.intrinsicThetaEvalRaw (π := π) a s j =
      Submodule.Quotient.mk
        (secRes (thetaChartDatum C R π a).sheaf le_top s) := by
  rfl

/-- The left arrow in the intrinsic theta descent equalizer. -/
noncomputable def thetaIntrinsicDeltaLeft (A : AffAdaptation D d) (a : ℕ) :
    A.ThetaPieceProd (π := π) a →ₗ[R] A.ThetaOverlapProd (π := π) a :=
  LinearMap.pi (fun p : D.index × D.index =>
    A.thetaToOverlapLeftLinear (π := π) a p.1 p.2 ∘ₗ LinearMap.proj p.1)

/-- The right arrow in the intrinsic theta descent equalizer. -/
noncomputable def thetaIntrinsicDeltaRight (A : AffAdaptation D d) (a : ℕ) :
    A.ThetaPieceProd (π := π) a →ₗ[R] A.ThetaOverlapProd (π := π) a :=
  LinearMap.pi (fun p : D.index × D.index =>
    A.thetaToOverlapRightLinear (π := π) a p.1 p.2 ∘ₗ LinearMap.proj p.2)

/-- Intrinsic restriction of `O(a Theta)` to the divisor, obtained by descent on the
arbitrary widened affine cover. -/
noncomputable def intrinsicThetaGluedSubmodule (A : AffAdaptation D d) (a : ℕ) :
    Submodule R (A.ThetaPieceProd (π := π) a) :=
  LinearMap.ker (A.thetaIntrinsicDeltaLeft (π := π) a -
    A.thetaIntrinsicDeltaRight (π := π) a)

/-- Membership in the intrinsic theta descent module is pairwise agreement on overlaps. -/
lemma mem_intrinsicThetaGluedSubmodule_iff (A : AffAdaptation D d) (a : ℕ)
    (s : A.ThetaPieceProd (π := π) a) :
    s ∈ A.intrinsicThetaGluedSubmodule (π := π) a ↔
      ∀ p : D.index × D.index,
        A.thetaToOverlapLeft (π := π) a p.1 p.2 (s p.1) =
          A.thetaToOverlapRight (π := π) a p.1 p.2 (s p.2) := by
  simp only [intrinsicThetaGluedSubmodule, LinearMap.mem_ker, LinearMap.sub_apply,
    sub_eq_zero, funext_iff, thetaIntrinsicDeltaLeft, thetaIntrinsicDeltaRight,
    LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply,
    thetaToOverlapLeftLinear, thetaToOverlapRightLinear]
  rfl

/-- The intrinsic globally descended theta restriction, as an `R`-module type. -/
noncomputable abbrev IntrinsicThetaGlued (A : AffAdaptation D d) (a : ℕ) : Type u :=
  ↥(A.intrinsicThetaGluedSubmodule (π := π) a)

/-- Piecewise evaluation of a global theta section satisfies the intrinsic overlap
equalizer. -/
theorem intrinsicThetaEvalRaw_mem (A : AffAdaptation D d) (a : ℕ)
    (s : A.ThetaGlobalSections (π := π) a) :
    A.intrinsicThetaEvalRaw (π := π) a s ∈
      A.intrinsicThetaGluedSubmodule (π := π) a := by
  apply (A.mem_intrinsicThetaGluedSubmodule_iff (π := π) a _).mpr
  rintro ⟨i, j⟩
  rw [A.intrinsicThetaEvalRaw_apply, A.intrinsicThetaEvalRaw_apply,
    A.thetaToOverlapLeft_mk, A.thetaToOverlapRight_mk,
    secRes_secRes, secRes_secRes]

/-- The canonical evaluation from global intrinsic theta sections to their restriction on
the widened divisor. -/
noncomputable def intrinsicThetaEval (A : AffAdaptation D d) (a : ℕ) :
    A.ThetaGlobalSections (π := π) a →ₗ[R] A.IntrinsicThetaGlued (π := π) a :=
  LinearMap.codRestrict (A.intrinsicThetaGluedSubmodule (π := π) a)
    (A.intrinsicThetaEvalRaw (π := π) a) (A.intrinsicThetaEvalRaw_mem (π := π) a)

@[simp]
lemma intrinsicThetaEval_coe (A : AffAdaptation D d) (a : ℕ)
    (s : A.ThetaGlobalSections (π := π) a) :
    (A.intrinsicThetaEval (π := π) a s : A.ThetaPieceProd (π := π) a) =
      A.intrinsicThetaEvalRaw (π := π) a s :=
  rfl

/-- The canonical intrinsic evaluation in the existing two-chart presentation of global
theta sections.  Only the source presentation uses the pinned theta charts; the divisor
cover and the target remain arbitrary affine opens. -/
noncomputable def intrinsicThetaEvalRel (A : AffAdaptation D d) (a : ℕ) :
    relThetaSections C R π a →ₗ[R] A.IntrinsicThetaGlued (π := π) a :=
  (A.intrinsicThetaEval (π := π) a).comp
    (gluedTwistEquiv C R π a (⊤ : (relCurve C R).Opens)).symm.toLinearMap

/-- The left overlap map is linear for the induced map of colength algebras. -/
lemma thetaToOverlapLeft_smul (A : AffAdaptation D d) (a : ℕ) (i j : D.index)
    (c : A.colength i) (x : A.ThetaPieceQuotient (π := π) a i) :
    A.thetaToOverlapLeft (π := π) a i j (c • x) =
      A.toOvlLeft i j c • A.thetaToOverlapLeft (π := π) a i j x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  induction x using Submodule.Quotient.induction_on with
  | _ m =>
    change Submodule.Quotient.mk
        (A.thetaSectionsToOverlapLeft (π := π) a i j (r • m)) =
      Submodule.Quotient.mk
        ((relResAlgHom C R
          (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i)) r •
            A.thetaSectionsToOverlapLeft (π := π) a i j m)
    rw [(A.thetaSectionsToOverlapLeft (π := π) a i j).map_smulₛₗ]
    rfl

/-- The right overlap map is linear for the induced map of colength algebras. -/
lemma thetaToOverlapRight_smul (A : AffAdaptation D d) (a : ℕ) (i j : D.index)
    (c : A.colength j) (x : A.ThetaPieceQuotient (π := π) a j) :
    A.thetaToOverlapRight (π := π) a i j (c • x) =
      A.toOvlRight i j c • A.thetaToOverlapRight (π := π) a i j x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  induction x using Submodule.Quotient.induction_on with
  | _ m =>
    change Submodule.Quotient.mk
        (A.thetaSectionsToOverlapRight (π := π) a i j (r • m)) =
      Submodule.Quotient.mk
        ((relResAlgHom C R
          (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j)) r •
            A.thetaSectionsToOverlapRight (π := π) a i j m)
    rw [(A.thetaSectionsToOverlapRight (π := π) a i j).map_smulₛₗ]
    rfl

/-- The left quotient restriction as a semilinear map over the corresponding colength
algebra restriction.  This is the left half of the intrinsic theta descent datum. -/
noncomputable def thetaToOverlapLeftColength (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    A.ThetaPieceQuotient (π := π) a i →ₛₗ[(A.toOvlLeft i j).toRingHom]
      A.ThetaOverlapQuotient (π := π) a i j where
  toFun := A.thetaToOverlapLeft (π := π) a i j
  map_add' := (A.thetaToOverlapLeft (π := π) a i j).map_add
  map_smul' := A.thetaToOverlapLeft_smul (π := π) a i j

/-- The right quotient restriction as a semilinear map over the corresponding colength
algebra restriction.  This is the right half of the intrinsic theta descent datum. -/
noncomputable def thetaToOverlapRightColength (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    A.ThetaPieceQuotient (π := π) a j →ₛₗ[(A.toOvlRight i j).toRingHom]
      A.ThetaOverlapQuotient (π := π) a i j where
  toFun := A.thetaToOverlapRight (π := π) a i j
  map_add' := (A.thetaToOverlapRight (π := π) a i j).map_add
  map_smul' := A.thetaToOverlapRight_smul (π := π) a i j

/-- Evaluation of the widened equalizer algebra on one piece colength algebra. -/
noncomputable def gluedSubalgebraPieceMap (A : AffAdaptation D d) (j : D.index) :
    ↥(gluedSubalgebra A) →ₐ[R] A.colength j :=
  (Pi.evalAlgHom R (fun i : D.index => A.colength i) j).comp
    (gluedSubalgebra A).val

/-- A piece theta quotient is a module over the widened equalizer algebra by evaluation on
that piece. -/
@[reducible]
noncomputable def thetaPieceQuotientGluedModule (A : AffAdaptation D d) (a : ℕ)
    (j : D.index) :
    Module ↥(gluedSubalgebra A) (A.ThetaPieceQuotient (π := π) a j) :=
  letI : Module (A.colength j) (A.ThetaPieceQuotient (π := π) a j) :=
    A.thetaPieceQuotientModule (π := π) a j
  Module.compHom (A.ThetaPieceQuotient (π := π) a j)
    (A.gluedSubalgebraPieceMap j).toRingHom

attribute [local instance] thetaPieceQuotientGluedModule

/-- The intrinsic theta equalizer is stable under the widened equalizer algebra `A_D`. -/
noncomputable def intrinsicThetaGluedOver (A : AffAdaptation D d) (a : ℕ) :
    Submodule ↥(gluedSubalgebra A) (A.ThetaPieceProd (π := π) a) where
  carrier := A.intrinsicThetaGluedSubmodule (π := π) a
  add_mem' := fun hx hy => (A.intrinsicThetaGluedSubmodule (π := π) a).add_mem hx hy
  zero_mem' := (A.intrinsicThetaGluedSubmodule (π := π) a).zero_mem
  smul_mem' := by
    intro c x hx
    have hx' := (A.mem_intrinsicThetaGluedSubmodule_iff (π := π) a x).mp hx
    apply (A.mem_intrinsicThetaGluedSubmodule_iff (π := π) a (c • x)).mpr
    intro p
    change A.thetaToOverlapLeft (π := π) a p.1 p.2 (c.1 p.1 • x p.1) =
      A.thetaToOverlapRight (π := π) a p.1 p.2 (c.1 p.2 • x p.2)
    rw [A.thetaToOverlapLeft_smul, A.thetaToOverlapRight_smul]
    have hc := (A.mem_gluedSubmodule_iff (c : A.chartProd)).mp c.2
    rw [hc p, hx' p]

/-- The intrinsic globally descended theta restriction as an `A_D`-module. -/
noncomputable abbrev IntrinsicThetaGluedOver (A : AffAdaptation D d) (a : ℕ) : Type u :=
  ↥(A.intrinsicThetaGluedOver (π := π) a)

end AffAdaptation

end AlgebraicGeometry
