/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeMonoBridge
import AlgebraicJacobian.Picard.DivisorFamilyEpsNaturality

/-!
# DDR-8 — window germs read on piece-restricted sections (the `hwin` closer, part I)

The two section-level legs of the fibre-stalk transfer consumed by
`Picard/DivSchemeMonoBridgeRel.lean` (the `hwin` closer):

* **§1 the germ chain** — `span_twistGermSet_le_map_germ_fst/snd`: at a point of an
  open `W` inside a pinned chart, every member of the window germ set
  (`Scheme.twistGermSet`) is, up to the germ of the cocycle unit for the cross-chart
  germs, the germ of a `W`-restricted matching component — so the span of the germ set
  is contained in the stalk extension of the ideal of restricted components.
* **§2 the crux triangle at the pieces** — `FinCoverData.windowRes` (the window piece
  restriction) and `span_resFst/resSnd_windowBaseChange_le`: the piece restrictions of
  the PUSHED window `windowBaseChange R' N` (the G-2 `ε`-naturality normal form) are
  `piecesMap`-compared `R`-window piece restrictions — elementwise the triangle
  `resHom_relThetaWindowEquiv_cancelBaseChange_fst/snd` composed with the piece-level
  naturality `pieceSectionsMap_algebraMap`.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

/-! ## §1 The window germ set reads on piece-restricted sections -/

section GermChain

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [X.Over (Spec (.of A))]
variable {V₀ V₁ : X.Opens} {gc : Γ(X, V₀ ⊓ V₁)ˣ}

/-- Germs commute with `resHom`: the germ of a restricted section is the germ of the
section (the public form of the `GluedDivisorSheaf`-private lemma). -/
lemma germ_resHom {V W : X.Opens} (h : W ≤ V) (x : X) (hx : x ∈ W)
    (t : Γ(X, V)) :
    (X.presheaf.germ W x hx).hom (X.resHom h t) =
      (X.presheaf.germ V x (h hx)).hom t :=
  X.presheaf.germ_res_apply (homOfLE h) x hx t

/-- **The germ set reads on chart-0 restrictions**: at a point of `W ≤ ⊤ ⊓ V₀`, every
member of the window germ set is — up to the germ of the cocycle unit, for the chart-1
germs — the germ of a `W`-restricted first component.  So the span of the germ set is
contained in the extension of the ideal of restricted first components. -/
lemma span_twistGermSet_le_map_germ_fst (T : Set ↥(twistSubmodule A V₀ V₁ gc ⊤))
    {W : X.Opens} (hW : W ≤ ⊤ ⊓ V₀) (z : X) (hz : z ∈ W) :
    Ideal.span (Scheme.twistGermSet T z)
      ≤ Ideal.map (X.presheaf.germ W z hz).hom
          (Ideal.span ((fun x : ↥(twistSubmodule A V₀ V₁ gc ⊤) =>
            X.resHom hW x.val.1) '' T)) := by
  rw [Ideal.span_le]
  have hmem₁ : ∀ (x : ↥(twistSubmodule A V₀ V₁ gc ⊤)) (_ : x ∈ T),
      (X.presheaf.germ (⊤ ⊓ V₀) z (hW hz)).hom x.val.1
        ∈ Ideal.map (X.presheaf.germ W z hz).hom
            (Ideal.span ((fun x : ↥(twistSubmodule A V₀ V₁ gc ⊤) =>
              X.resHom hW x.val.1) '' T)) := by
    intro x hx
    rw [← germ_resHom hW z hz]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨x, hx, rfl⟩)
  rintro a (⟨x, hx, hz₀, rfl⟩ | ⟨x, hx, hz₁, rfl⟩)
  · exact hmem₁ x hx
  · -- chart-1 germ: invert the cocycle unit
    have hzO : z ∈ ⊤ ⊓ V₀ ⊓ V₁ := ⟨hW hz, hz₁.2⟩
    have hrel := congrArg (X.presheaf.germ (⊤ ⊓ V₀ ⊓ V₁) z hzO).hom
      ((mem_twistSubmodule_iff A V₀ V₁ gc x.val).mp x.2)
    rw [map_mul, germ_resHom, germ_resHom, germ_resHom] at hrel
    have hunit : IsUnit ((X.presheaf.germ (V₀ ⊓ V₁) z ⟨(hW hz).2, hz₁.2⟩).hom
        (gc : Γ(X, V₀ ⊓ V₁))) :=
      gc.isUnit.map (X.presheaf.germ (V₀ ⊓ V₁) z ⟨(hW hz).2, hz₁.2⟩).hom
    obtain ⟨u, hu⟩ := hunit
    have hval : (X.presheaf.germ (⊤ ⊓ V₁) z hz₁).hom x.val.2
        = ↑u⁻¹ * (X.presheaf.germ (⊤ ⊓ V₀) z (hW hz)).hom x.val.1 := by
      rw [hrel, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [hval]
    exact Ideal.mul_mem_left _ _ (hmem₁ x hx)

/-- **The germ set reads on chart-1 restrictions** (mirror of
`span_twistGermSet_le_map_germ_fst`, at a point of `W ≤ ⊤ ⊓ V₁`; the chart-0 germs pick
up the cocycle unit directly). -/
lemma span_twistGermSet_le_map_germ_snd (T : Set ↥(twistSubmodule A V₀ V₁ gc ⊤))
    {W : X.Opens} (hW : W ≤ ⊤ ⊓ V₁) (z : X) (hz : z ∈ W) :
    Ideal.span (Scheme.twistGermSet T z)
      ≤ Ideal.map (X.presheaf.germ W z hz).hom
          (Ideal.span ((fun x : ↥(twistSubmodule A V₀ V₁ gc ⊤) =>
            X.resHom hW x.val.2) '' T)) := by
  rw [Ideal.span_le]
  have hmem₁ : ∀ (x : ↥(twistSubmodule A V₀ V₁ gc ⊤)) (_ : x ∈ T),
      (X.presheaf.germ (⊤ ⊓ V₁) z (hW hz)).hom x.val.2
        ∈ Ideal.map (X.presheaf.germ W z hz).hom
            (Ideal.span ((fun x : ↥(twistSubmodule A V₀ V₁ gc ⊤) =>
              X.resHom hW x.val.2) '' T)) := by
    intro x hx
    rw [← germ_resHom hW z hz]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨x, hx, rfl⟩)
  rintro a (⟨x, hx, hz₀, rfl⟩ | ⟨x, hx, hz₁, rfl⟩)
  · -- chart-0 germ: multiply by the cocycle unit
    have hzO : z ∈ ⊤ ⊓ V₀ ⊓ V₁ := ⟨hz₀, (hW hz).2⟩
    have hrel := congrArg (X.presheaf.germ (⊤ ⊓ V₀ ⊓ V₁) z hzO).hom
      ((mem_twistSubmodule_iff A V₀ V₁ gc x.val).mp x.2)
    rw [map_mul, germ_resHom, germ_resHom, germ_resHom] at hrel
    rw [hrel]
    exact Ideal.mul_mem_left _ _ (hmem₁ x hx)
  · exact hmem₁ x hx

end GermChain

/-! ## §2 The pushed window restricts to compared piece sections -/

section PieceWindow

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable (a : ℕ)
variable (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)

/-- **The window restriction to a piece**: the chart component of a global theta section
matching the chart of the piece, restricted to the piece (`thetaPieceEval` without the
colength quotient). -/
noncomputable def FinCoverData.windowRes (D : FinCoverData C R π) :
    ∀ j : D.index, relThetaSections C R π a →ₗ[R] Γ(relCurve C R, D.pieces j)
  | .inl ℓ => relThetaResFst a (le_inf le_top (D.pieces_inl_le ℓ))
  | .inr ℓ => relThetaResSnd a (le_inf le_top (D.pieces_inr_le ℓ))

variable {R'}

omit [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π] in
/-- Piece restriction of a compared chart-0 section is the compared piece restriction
(`pieceSectionsMap_algebraMap` at the pinned chart, `algebraMap = resHom`). -/
private lemma resHom_relSectionsMap_pieces₀ (D : FinCoverData C R π) (ℓ : Fin D.m₀)
    (σ : Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀)) :
    (relCurve C R').resHom ((D.baseChange R').pieces_inl_le ℓ)
        (relSectionsMap C R R' (fiberTwoCover π).V₀ σ)
      = D.piecesMap R' (Sum.inl ℓ) ((relCurve C R).resHom (D.pieces_inl_le ℓ) σ) :=
  (pieceSectionsMap_algebraMap R' (fiberChart₀ π) (D.h₀ ℓ) σ).symm

omit [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π] in
/-- Chart-1 mirror of `resHom_relSectionsMap_pieces₀`. -/
private lemma resHom_relSectionsMap_pieces₁ (D : FinCoverData C R π) (ℓ : Fin D.m₁)
    (σ : Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₁)) :
    (relCurve C R').resHom ((D.baseChange R').pieces_inr_le ℓ)
        (relSectionsMap C R R' (fiberTwoCover π).V₁ σ)
      = D.piecesMap R' (Sum.inr ℓ) ((relCurve C R).resHom (D.pieces_inr_le ℓ) σ) :=
  (pieceSectionsMap_algebraMap R' (fiberChart₁ π) (D.h₁ ℓ) σ).symm

/-- **The pushed window's chart-0 piece restrictions are compared `R`-window piece
restrictions** (the crux triangle at the pieces): the span of the restricted first
components of the pushed window is contained in the span of the `piecesMap`-images of
the `R`-window piece restrictions. -/
lemma span_resFst_windowBaseChange_le (D : FinCoverData C R π) (ℓ : Fin D.m₀)
    (N : Submodule R (R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤))) :
    Ideal.span ((fun x : relThetaSections C R' π a =>
        (relCurve C R').resHom (le_inf le_top ((D.baseChange R').pieces_inl_le ℓ))
          x.val.1) ''
        ↑(Submodule.map (relThetaWindowEquiv C R' π a hH1).toLinearMap
            (windowBaseChange R' N)))
      ≤ Ideal.span (D.piecesMap R' (Sum.inl ℓ) ''
          ((fun x => (relCurve C R).resHom (le_inf le_top (D.pieces_inl_le ℓ))
            ((relThetaWindowEquiv C R π a hH1 x).val.1)) '' ↑N)) := by
  have main : ∀ w ∈ N.baseChange R',
      (relCurve C R').resHom (le_inf le_top ((D.baseChange R').pieces_inl_le ℓ))
        ((relThetaWindowEquiv C R' π a hH1
          (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _ w)).val.1)
      ∈ Ideal.span (D.piecesMap R' (Sum.inl ℓ) ''
          ((fun x => (relCurve C R).resHom (le_inf le_top (D.pieces_inl_le ℓ))
            ((relThetaWindowEquiv C R π a hH1 x).val.1)) '' ↑N)) := by
    intro w hw
    rw [Submodule.baseChange_eq_span] at hw
    induction hw using Submodule.span_induction with
    | mem w hmem =>
      obtain ⟨m, hm, rfl⟩ := hmem
      have key : (relCurve C R').resHom
          (le_inf le_top ((D.baseChange R').pieces_inl_le ℓ))
          ((relThetaWindowEquiv C R' π a hH1
            (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _
              ((TensorProduct.mk R R' _ 1) m))).val.1)
          = D.piecesMap R' (Sum.inl ℓ)
              ((relCurve C R).resHom (le_inf le_top (D.pieces_inl_le ℓ))
                ((relThetaWindowEquiv C R π a hH1 m).val.1)) :=
        (Scheme.resHom_resHom (le_inf le_top le_rfl)
            ((D.baseChange R').pieces_inl_le ℓ) _).symm.trans
          (((congrArg ((relCurve C R').resHom ((D.baseChange R').pieces_inl_le ℓ))
            (resHom_relThetaWindowEquiv_cancelBaseChange_fst C R R' π a hH1 m)).trans
              (resHom_relSectionsMap_pieces₀ D ℓ _)).trans
            (congrArg (D.piecesMap R' (Sum.inl ℓ))
              (Scheme.resHom_resHom (le_inf le_top le_rfl) (D.pieces_inl_le ℓ) _)))
      have hmem2 : D.piecesMap R' (Sum.inl ℓ)
          ((relCurve C R).resHom (le_inf le_top (D.pieces_inl_le ℓ))
            ((relThetaWindowEquiv C R π a hH1 m).val.1))
          ∈ Ideal.span (D.piecesMap R' (Sum.inl ℓ) ''
            ((fun x => (relCurve C R).resHom (le_inf le_top (D.pieces_inl_le ℓ))
              ((relThetaWindowEquiv C R π a hH1 x).val.1)) '' ↑N)) :=
        Ideal.subset_span ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      exact key.symm ▸ hmem2
    | zero =>
      simp only [map_zero, Submodule.coe_zero, Prod.fst_zero]
      exact (Ideal.span _).zero_mem
    | add w₁ w₂ hw₁ hw₂ h₁ h₂ =>
      simp only [map_add, Submodule.coe_add, Prod.fst_add]
      exact (Ideal.span _).add_mem h₁ h₂
    | smul c w hw h =>
      simp only [map_smul, Submodule.coe_smul, Prod.smul_fst]
      rw [resHom_smul_rel' C R' _ c _]
      exact Submodule.smul_of_tower_mem _ c h
  rw [Ideal.span_le]
  rintro _ ⟨x', hx', rfl⟩
  obtain ⟨y, hy, rfl⟩ := hx'
  rw [windowBaseChange] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact main w hw

/-- Chart-1 mirror of `span_resFst_windowBaseChange_le`. -/
lemma span_resSnd_windowBaseChange_le (D : FinCoverData C R π) (ℓ : Fin D.m₁)
    (N : Submodule R (R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤))) :
    Ideal.span ((fun x : relThetaSections C R' π a =>
        (relCurve C R').resHom (le_inf le_top ((D.baseChange R').pieces_inr_le ℓ))
          x.val.2) ''
        ↑(Submodule.map (relThetaWindowEquiv C R' π a hH1).toLinearMap
            (windowBaseChange R' N)))
      ≤ Ideal.span (D.piecesMap R' (Sum.inr ℓ) ''
          ((fun x => (relCurve C R).resHom (le_inf le_top (D.pieces_inr_le ℓ))
            ((relThetaWindowEquiv C R π a hH1 x).val.2)) '' ↑N)) := by
  have main : ∀ w ∈ N.baseChange R',
      (relCurve C R').resHom (le_inf le_top ((D.baseChange R').pieces_inr_le ℓ))
        ((relThetaWindowEquiv C R' π a hH1
          (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _ w)).val.2)
      ∈ Ideal.span (D.piecesMap R' (Sum.inr ℓ) ''
          ((fun x => (relCurve C R).resHom (le_inf le_top (D.pieces_inr_le ℓ))
            ((relThetaWindowEquiv C R π a hH1 x).val.2)) '' ↑N)) := by
    intro w hw
    rw [Submodule.baseChange_eq_span] at hw
    induction hw using Submodule.span_induction with
    | mem w hmem =>
      obtain ⟨m, hm, rfl⟩ := hmem
      have key : (relCurve C R').resHom
          (le_inf le_top ((D.baseChange R').pieces_inr_le ℓ))
          ((relThetaWindowEquiv C R' π a hH1
            (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _
              ((TensorProduct.mk R R' _ 1) m))).val.2)
          = D.piecesMap R' (Sum.inr ℓ)
              ((relCurve C R).resHom (le_inf le_top (D.pieces_inr_le ℓ))
                ((relThetaWindowEquiv C R π a hH1 m).val.2)) :=
        (Scheme.resHom_resHom (le_inf le_top le_rfl)
            ((D.baseChange R').pieces_inr_le ℓ) _).symm.trans
          (((congrArg ((relCurve C R').resHom ((D.baseChange R').pieces_inr_le ℓ))
            (resHom_relThetaWindowEquiv_cancelBaseChange_snd C R R' π a hH1 m)).trans
              (resHom_relSectionsMap_pieces₁ D ℓ _)).trans
            (congrArg (D.piecesMap R' (Sum.inr ℓ))
              (Scheme.resHom_resHom (le_inf le_top le_rfl) (D.pieces_inr_le ℓ) _)))
      have hmem2 : D.piecesMap R' (Sum.inr ℓ)
          ((relCurve C R).resHom (le_inf le_top (D.pieces_inr_le ℓ))
            ((relThetaWindowEquiv C R π a hH1 m).val.2))
          ∈ Ideal.span (D.piecesMap R' (Sum.inr ℓ) ''
            ((fun x => (relCurve C R).resHom (le_inf le_top (D.pieces_inr_le ℓ))
              ((relThetaWindowEquiv C R π a hH1 x).val.2)) '' ↑N)) :=
        Ideal.subset_span ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      exact key.symm ▸ hmem2
    | zero =>
      simp only [map_zero, Submodule.coe_zero, Prod.snd_zero]
      exact (Ideal.span _).zero_mem
    | add w₁ w₂ hw₁ hw₂ h₁ h₂ =>
      simp only [map_add, Submodule.coe_add, Prod.snd_add]
      exact (Ideal.span _).add_mem h₁ h₂
    | smul c w hw h =>
      simp only [map_smul, Submodule.coe_smul, Prod.smul_snd]
      rw [resHom_smul_rel' C R' _ c _]
      exact Submodule.smul_of_tower_mem _ c h
  rw [Ideal.span_le]
  rintro _ ⟨x', hx', rfl⟩
  obtain ⟨y, hy, rfl⟩ := hx'
  rw [windowBaseChange] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact main w hw

end PieceWindow

end AlgebraicGeometry
