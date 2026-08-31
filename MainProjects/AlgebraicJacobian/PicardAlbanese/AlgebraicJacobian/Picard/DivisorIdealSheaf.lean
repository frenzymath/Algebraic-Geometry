/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorIdealSections
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaDescent
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The Cartier ideal sheaf of a widened divisor adaptation

The principal ideal on each affine piece of a widened adaptation is pushed to the ambient
relative curve, and their finite infimum is the global Cartier ideal.  The construction is
intrinsic to the arbitrary affine cover: it uses neither a chart typing nor `SwallowedBy`.
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

/-- The principal ideal sheaf cut out by the adapted equation on one affine piece. -/
noncomputable def localCartierIdeal (A : AffAdaptation D d) (j : D.index) :
    (D.pieces j : Scheme).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.span {(D.pieces j).topIso.inv.hom (A.eqn j)})

/-- The global Cartier ideal obtained by pushing the local principal ideals to the
relative curve and intersecting them. -/
noncomputable def cartierIdeal (A : AffAdaptation D d) :
    (relCurve C R).IdealSheafData :=
  iInf fun j : D.index => (A.localCartierIdeal j).map (D.pieces j).ι

/-- Inclusion of an affine piece in the relative curve is quasi-compact. -/
theorem quasiCompact_piece_ι [IsProper C.hom] (j : D.index) :
    QuasiCompact (D.pieces j).ι := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro U hU
  have hpre : IsAffineOpen ((D.pieces j).ι ⁻¹ᵁ U) := by
    apply ((D.pieces j).ι.isAffineOpen_iff_of_isOpenImmersion).mp
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact Over.isAffineOpen_inf C (D.isAffineOpen j) hU
  exact hpre.isCompact

/-- The inverse image of one adapted affine piece inside another is affine. -/
theorem isAffineOpen_piece_preimage [IsProper C.hom] (i j : D.index) :
    IsAffineOpen ((D.pieces j).ι ⁻¹ᵁ D.pieces i) := by
  apply ((D.pieces j).ι.isAffineOpen_iff_of_isOpenImmersion).mp
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact Over.isAffineOpen_inf C (D.isAffineOpen j) (D.isAffineOpen i)

private lemma topIso_inv_eq_piece_appLE {X : Scheme.{u}} (U : X.Opens) :
    U.topIso.inv = U.ι.appLE U ⊤ (by simp) := by
  simp only [Scheme.Opens.topIso_inv, Scheme.Hom.appLE,
    Scheme.Opens.ι_app, Scheme.Opens.toScheme_presheaf_map]
  rw [← Functor.map_comp]
  rfl

private lemma pieceSection_to_overlap (A : AffAdaptation D d) (i j : D.index) :
    ((IsOpenImmersion.ΓIso (D.pieces j).ι (D.pieces i)).hom.hom
      (((D.pieces j).ι.app (D.pieces i)).hom (A.eqn i))) =
      ((relCurve C R).presheaf.map
        (homOfLE (inf_le_right :
          (D.pieces j).ι.opensRange ⊓ D.pieces i ≤ D.pieces i)).op).hom
        (A.eqn i) :=
  IsOpenImmersion.app_ΓIso_hom_apply (D.pieces j).ι (D.pieces i) (A.eqn i)

private lemma localCartierIdeal_generator_to_overlap
    (A : AffAdaptation D d) (i j : D.index) :
    ((IsOpenImmersion.ΓIso (D.pieces j).ι (D.pieces i)).hom.hom
      (((D.pieces j : Scheme).presheaf.map
        (homOfLE (le_top :
          (D.pieces j).ι ⁻¹ᵁ D.pieces i ≤
            (⊤ : (D.pieces j : Scheme).Opens))).op).hom
        ((D.pieces j).topIso.inv.hom (A.eqn j)))) =
      ((relCurve C R).presheaf.map
        (homOfLE (inf_le_left :
          (D.pieces j).ι.opensRange ⊓ D.pieces i ≤
            (D.pieces j).ι.opensRange)).op).hom
        (((relCurve C R).presheaf.map
          (eqToHom (Scheme.Opens.opensRange_ι (D.pieces j))).op).hom
          (A.eqn j)) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    topIso_inv_eq_piece_appLE]
  rw [Scheme.Hom.appLE_map_assoc]
  simp only [IsOpenImmersion.ΓIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, eqToHom_op]
  rw [Scheme.Hom.appLE_appIso_inv_assoc]
  rw [← CommRingCat.comp_apply]
  congr 2
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

private lemma restrictedEqn_mem_span_on_overlap
    (A : AffAdaptation D d) (i j : D.index) :
    ((relCurve C R).presheaf.map
      (homOfLE (inf_le_right :
        (D.pieces j).ι.opensRange ⊓ D.pieces i ≤ D.pieces i)).op).hom
        (A.eqn i) ∈
      Ideal.span {
        ((relCurve C R).presheaf.map
          (homOfLE (inf_le_left :
            (D.pieces j).ι.opensRange ⊓ D.pieces i ≤
              (D.pieces j).ι.opensRange)).op).hom
          (((relCurve C R).presheaf.map
            (eqToHom (Scheme.Opens.opensRange_ι (D.pieces j))).op).hom
            (A.eqn j))} := by
  let W : (relCurve C R).Opens := (D.pieces j).ι.opensRange ⊓ D.pieces i
  let W' : (relCurve C R).Opens := D.pieces j ⊓ D.pieces i
  have hW : W = W' :=
    congrArg (fun U : (relCurve C R).Opens => U ⊓ D.pieces i)
      (Scheme.Opens.opensRange_ι (D.pieces j))
  let eW : Γ(relCurve C R, W') ≅ Γ(relCurve C R, W) :=
    (relCurve C R).presheaf.mapIso (eqToIso hW).op
  have hmapped := Ideal.mem_map_of_mem eW.hom.hom
    (A.restrictedEqnRight_mem_span_left j i)
  rw [Ideal.map_span, Set.image_singleton] at hmapped
  have hi :
      ((relCurve C R).presheaf.map
        (homOfLE (inf_le_right : W ≤ D.pieces i)).op).hom (A.eqn i) =
      eW.hom.hom (relResAlgHom C R
        (inf_le_right : W' ≤ D.pieces i) (A.eqn i)) := by
    dsimp [eW]
    simp only [Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    congr 2
  have hj :
      ((relCurve C R).presheaf.map
        (homOfLE (inf_le_left : W ≤ (D.pieces j).ι.opensRange)).op).hom
          (((relCurve C R).presheaf.map
            (eqToHom (Scheme.Opens.opensRange_ι (D.pieces j))).op).hom
            (A.eqn j)) =
      eW.hom.hom (relResAlgHom C R
        (inf_le_left : W' ≤ D.pieces j) (A.eqn j)) := by
    dsimp [eW]
    simp only [Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    congr 2
  exact hi.symm ▸ hj.symm ▸ hmapped

/-- On its defining piece, the pushed principal ideal is the ideal generated by the
adapted equation. -/
theorem localCartierIdeal_map_ideal_self [IsProper C.hom]
    (A : AffAdaptation D d) (i : D.index) :
    ((A.localCartierIdeal i).map (D.pieces i).ι).ideal
      ⟨D.pieces i, D.isAffineOpen i⟩ = Ideal.span {A.eqn i} := by
  letI : QuasiCompact (D.pieces i).ι := quasiCompact_piece_ι (D := D) i
  letI : IsIso ((D.pieces i).ι.app (D.pieces i)) :=
    Scheme.Hom.isIso_app (D.pieces i).ι (D.pieces i) (by simp)
  rw [Scheme.IdealSheafData.ideal_map _ _ _
    (isAffineOpen_piece_preimage (D := D) i i)]
  simp only [localCartierIdeal, Scheme.IdealSheafData.ofIdealTop_ideal]
  let f := ((D.pieces i).ι.app (D.pieces i)).hom
  let g := ((D.pieces i : Scheme).presheaf.map
    (homOfLE (le_top :
      (D.pieces i).ι ⁻¹ᵁ D.pieces i ≤
        (⊤ : (D.pieces i : Scheme).Opens))).op).hom
  have hfg (s : Γ(relCurve C R, D.pieces i)) :
      g ((D.pieces i).topIso.inv.hom s) = f s := by
    dsimp [f, g]
    simp only [Scheme.Opens.topIso_inv]
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  change (Ideal.map g
      (Ideal.span {(D.pieces i).topIso.inv.hom (A.eqn i)})).comap f =
    Ideal.span {A.eqn i}
  rw [Ideal.map_span, Set.image_singleton, hfg]
  have hm : Ideal.span {f (A.eqn i)} = (Ideal.span {A.eqn i}).map f := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hm]
  exact Ideal.comap_map_of_bijective f
    (ConcreteCategory.bijective_of_isIso ((D.pieces i).ι.app (D.pieces i)))

/-- Every pushed local Cartier ideal contains the principal ideal of any other adapted
piece.  This is the cross-piece compatibility needed to compute their intersection. -/
theorem span_eqn_le_localCartierIdeal_map_ideal [IsProper C.hom]
    (A : AffAdaptation D d) (i j : D.index) :
    Ideal.span {A.eqn i} ≤
      ((A.localCartierIdeal j).map (D.pieces j).ι).ideal
        ⟨D.pieces i, D.isAffineOpen i⟩ := by
  letI : QuasiCompact (D.pieces j).ι := quasiCompact_piece_ι (D := D) j
  rw [Scheme.IdealSheafData.ideal_map _ _ _
    (isAffineOpen_piece_preimage (D := D) i j)]
  simp only [localCartierIdeal, Scheme.IdealSheafData.ofIdealTop_ideal]
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap,
    Ideal.map_span, Set.image_singleton]
  let x := ((D.pieces j).ι.app (D.pieces i)).hom (A.eqn i)
  let b := ((D.pieces j : Scheme).presheaf.map
    (homOfLE (le_top :
      (D.pieces j).ι ⁻¹ᵁ D.pieces i ≤
        (⊤ : (D.pieces j : Scheme).Opens))).op).hom
    ((D.pieces j).topIso.inv.hom (A.eqn j))
  change x ∈ Ideal.span {b}
  let e := IsOpenImmersion.ΓIso (D.pieces j).ι (D.pieces i)
  have hx := pieceSection_to_overlap A i j
  have hb := localCartierIdeal_generator_to_overlap A i j
  have he : e.hom.hom x ∈ Ideal.span {e.hom.hom b} := by
    rw [hx, hb]
    exact restrictedEqn_mem_span_on_overlap A i j
  rw [Ideal.mem_span_singleton] at he ⊢
  obtain ⟨c, hc⟩ := he
  refine ⟨e.inv.hom c, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  rw [map_mul, Iso.inv_hom_id_apply, hc]

/-- The widened Cartier ideal is principal on every adapted affine piece, with the
recorded adapted equation as generator. -/
theorem cartierIdeal_ideal_eq_span_eqn [IsProper C.hom]
    (A : AffAdaptation D d) (i : D.index) :
    A.cartierIdeal.ideal ⟨D.pieces i, D.isAffineOpen i⟩ =
      Ideal.span {A.eqn i} := by
  rw [cartierIdeal, Scheme.IdealSheafData.ideal_iInf, iInf_apply]
  apply le_antisymm
  · exact (iInf_le _ i).trans_eq (A.localCartierIdeal_map_ideal_self i)
  · exact le_iInf fun j => A.span_eqn_le_localCartierIdeal_map_ideal i j

/-- The widened Cartier ideal recovers the intrinsic germwise section ideal on every
adapted affine piece. -/
theorem cartierIdeal_ideal_eq_sectionIdeal [IsProper C.hom]
    (A : AffAdaptation D d) (i : D.index) :
    A.cartierIdeal.ideal ⟨D.pieces i, D.isAffineOpen i⟩ =
      d.sectionIdeal (D.pieces i) := by
  rw [A.cartierIdeal_ideal_eq_span_eqn i]
  exact (A.sectionIdeal_eq_span_eqn i).symm

end AffAdaptation

end AlgebraicGeometry
