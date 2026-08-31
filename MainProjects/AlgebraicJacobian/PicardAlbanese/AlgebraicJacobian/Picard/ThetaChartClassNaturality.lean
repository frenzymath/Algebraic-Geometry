/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RelCurveCollapse
import AlgebraicJacobian.Picard.DivisorFamilyMapAlg

/-!
# Naturality of the whole-chart theta class in the test ring (G-1 substrate)

The test-ring naturality of the whole-chart theta datum of
`Cohomology/RelCurveCollapse.lean`, the class-leg seam between the `R`-level G-0a
class law (`Picard/DivSchemeFibreH1.lean`) and the `k`-anchored window transport
(`RiemannRoch/WindowFieldTransport.lean`):

* `baseChange_thetaChartDatum_pieces` — the base-changed whole-chart pieces are the
  whole pinned charts of `C_R`.
* `cechPicClass_baseChange_thetaChartDatum` — the base change of the whole-chart theta
  datum along `k → R` carries the class of the `R`-level whole-chart theta datum: both
  subordinated cocycles on the canonical `R`-level pointed cover restrict the same
  `appLE`-pullback of `thetaUnit π ^ a`, chart-casewise.
* `cechPicClass_map_thetaChartDatum` — the tower corollary `k → R → R'`: the
  `relCurveMap` pullback of the `R`-level theta chart class is the class of the datum
  base-changed to `R'` from the base field (`windowTransportDatum` when `R'` is a
  field) — `cechPicClass_baseChange` twice, `relCurveMap_comp`, `CechPic.map_comp`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (π : C.left ⟶ P1 k) [IsFinite π]

/-! ## Naturality of the theta chart class in the test ring -/

section Naturality

variable (a : ℕ)

/-- The pair value of a subordinated cocycle at known piece indices, as a restricted
transition unit (value form; the `subst` normal form of `gluedSubordUnit`). -/
private lemma gluedSubordUnit_val_of_eq {X : Scheme.{u}} {J : Type u} {U : J → X.Opens}
    {g : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ} (𝒲 : X.PointedCover) (σ : X → J)
    (hσ : ∀ x : X, 𝒲.opens x ≤ U (σ x)) {x y : X} {i j : J} (hi : σ x = i)
    (hj : σ y = j) (hle : 𝒲.opens x ⊓ 𝒲.opens y ≤ U i ⊓ U j) :
    ((gluedSubordUnit g 𝒲 σ hσ x y : Γ(X, 𝒲.opens x ⊓ 𝒲.opens y)ˣ) :
        Γ(X, 𝒲.opens x ⊓ 𝒲.opens y))
      = X.resHom hle ((g i j : Γ(X, U i ⊓ U j)ˣ) : Γ(X, U i ⊓ U j)) := by
  subst hi
  subst hj
  rfl

/-- The relative-curve comparison pulls the pinned charts of `C_R` back from the pinned
charts of `C_k`. -/
private lemma relCurveMap_preimage_V₀ :
    relCurveMap C k R ⁻¹ᵁ (relCover C k (fiberTwoCover π)).V₀
      = (relCover C R (fiberTwoCover π)).V₀ :=
  relCurveMap_preimage C k R (fiberTwoCover π).V₀

private lemma relCurveMap_preimage_V₁ :
    relCurveMap C k R ⁻¹ᵁ (relCover C k (fiberTwoCover π)).V₁
      = (relCover C R (fiberTwoCover π)).V₁ :=
  relCurveMap_preimage C k R (fiberTwoCover π).V₁

/-- The pieces of the base-changed whole-chart theta datum are the whole pinned charts
of `C_R`. -/
lemma baseChange_thetaChartDatum_pieces (j : ((thetaChartDatum C k π a).baseChange R).index) :
    ((thetaChartDatum C k π a).baseChange R).pieces j
      = (thetaChartCover C R π).pieces j := by
  rcases j with j | j
  · exact ((thetaChartDatum C k π a).toBasicOpenCoverData.pieces_baseChange R
        (Sum.inl j)).trans
      ((congrArg (relCurveMap C k R ⁻¹ᵁ ·) (thetaChartCover_pieces_inl C k π j)).trans
        ((relCurveMap_preimage_V₀ C R π).trans
          (thetaChartCover_pieces_inl C R π j).symm))
  · exact ((thetaChartDatum C k π a).toBasicOpenCoverData.pieces_baseChange R
        (Sum.inr j)).trans
      ((congrArg (relCurveMap C k R ⁻¹ᵁ ·) (thetaChartCover_pieces_inr C k π j)).trans
        ((relCurveMap_preimage_V₁ C R π).trans
          (thetaChartCover_pieces_inr C R π j).symm))

/-- The relative theta cocycle, in `appLE`-of-the-theta-power normal form (any test
ring; `relThetaCocycle_val'` of `Cohomology/RelCurveCollapse.lean` generalized). -/
private lemma relThetaCocycle_val :
    ((relThetaCocycle C R π a : Γ(relCurve C R,
          (relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁)ˣ) :
        Γ(relCurve C R,
          (relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁))
      = ((fst C (overSpec k R)).left.appLE (fiberChart₀ π ⊓ fiberChart₁ π)
            ((relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁)
            (le_of_eq (relCover_inf C R (fiberTwoCover π)))).hom
          ((thetaUnit π ^ a : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)ˣ) :
            Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)) := rfl

/-- The inverse relative theta cocycle, in `appLE` normal form. -/
private lemma relThetaCocycle_inv_val :
    (((relThetaCocycle C R π a)⁻¹ : Γ(relCurve C R,
          (relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁)ˣ) :
        Γ(relCurve C R,
          (relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁))
      = ((fst C (overSpec k R)).left.appLE (fiberChart₀ π ⊓ fiberChart₁ π)
            ((relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁)
            (le_of_eq (relCover_inf C R (fiberTwoCover π)))).hom
          (((thetaUnit π ^ a)⁻¹ : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)ˣ) :
            Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)) := rfl

/-- Restriction after `appLE` composes to a single `appLE` (elementwise). -/
private lemma resHom_appLE_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : V' ≤ V) (s : Γ(Y, U)) :
    X.resHom h ((f.appLE U V e).hom s) = (f.appLE U V' (h.trans e)).hom s := by
  have hcomp : f.appLE U V e ≫ X.presheaf.map (homOfLE h).op
      = f.appLE U V' (h.trans e) := Scheme.Hom.appLE_map f e (homOfLE h).op
  exact congr($(hcomp).hom s)

/-- `appLE` after restriction composes to a single `appLE` (elementwise). -/
private lemma appLE_resHom_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U' U : Y.Opens}
    {V : X.Opens} (h : U' ≤ U) (e : V ≤ f ⁻¹ᵁ U') (s : Γ(Y, U)) :
    (f.appLE U' V e).hom (Y.resHom h s)
      = (f.appLE U V (e.trans (Scheme.Hom.preimage_mono f h))).hom s := by
  have hcomp : Y.presheaf.map (homOfLE h).op ≫ f.appLE U' V e
      = f.appLE U V (e.trans (Scheme.Hom.preimage_mono f h)) :=
    Scheme.Hom.map_appLE f e (homOfLE h).op
  exact congr($(hcomp).hom s)

/-- `appLE` after `appLE` composes to the `appLE` of the composite (elementwise). -/
private lemma appLE_appLE_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {U : Z.Opens} {V : Y.Opens} {W : X.Opens} (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V)
    (s : Γ(Z, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom s)
      = ((f ≫ g).appLE U W
          (e₂.trans ((Opens.map f.base).map (homOfLE e₁)).le)).hom s := by
  have hcomp := Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂
  exact congr($(hcomp).hom s)

/-- The overlap comparison map of a base-changed cover datum, in `appLE` normal form
(elementwise). -/
private lemma overlapMap_apply {B B' : Type u} [CommRing B] [Algebra k B] [CommRing B']
    [Algebra k B'] [Algebra B B'] [IsScalarTower k B B'] (D : BasicOpenCoverData C B π)
    (i j : D.index) (s : Γ(relCurve C B, D.pieces i ⊓ D.pieces j)) :
    D.overlapMap B' i j s
      = ((relCurveMap C B B').appLE (D.pieces i ⊓ D.pieces j)
          ((D.baseChange B').pieces i ⊓ (D.baseChange B').pieces j)
          (D.baseChange_inf_le_preimage B' i j)).hom s := rfl

/-- `appLE` is invariant under an equality of morphisms (the inclusion witness is
proof-irrelevant). -/
private lemma appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    {U : Y.Opens} {W : X.Opens} (e : W ≤ f ⁻¹ᵁ U) :
    f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h
  rfl

set_option maxHeartbeats 800000 in
-- (The four-branch unit comparison crosses the `relCurve`/product spelling seam
-- repeatedly, as in the base-field class law; the defeq checks exceed the default.)
/-- **Naturality of the theta chart class in the test ring**: the base change of the
whole-chart theta datum along `k → R` carries the class of the `R`-level whole-chart
theta datum.  Both subordinated cocycles on the canonical `R`-level pointed cover
restrict the same `appLE`-pullback of `thetaUnit π ^ a` (chart-casewise). -/
theorem cechPicClass_baseChange_thetaChartDatum :
    ((thetaChartDatum C k π a).baseChange R).cechPicClass
      = (thetaChartDatum C R π a).cechPicClass := by
  have hpieces : ∀ j, (thetaChartCover C R π).pieces j
      ≤ ((thetaChartDatum C k π a).baseChange R).pieces j :=
    fun j => (baseChange_thetaChartDatum_pieces C R π a j).ge
  have hσ : ∀ x, (thetaChartDatum C R π a).pointedCover.opens x
      ≤ ((thetaChartDatum C k π a).baseChange R).pieces
          ((thetaChartDatum C R π a).pieceIndex x) :=
    fun x => hpieces ((thetaChartDatum C R π a).pieceIndex x)
  have hco : gluedSubordCocycle ((thetaChartDatum C k π a).baseChange R).isGluingCocycle
        (thetaChartDatum C R π a).pointedCover (thetaChartDatum C R π a).pieceIndex hσ
      = gluedSubordCocycle (thetaChartDatum C R π a).isGluingCocycle
          (thetaChartDatum C R π a).pointedCover (thetaChartDatum C R π a).pieceIndex
          (fun _ => le_rfl) := by
    refine Scheme.unitsCocycle_ext fun x y => ?_
    rw [gluedSubordCocycle_evInf, gluedSubordCocycle_evInf]
    refine Units.ext ?_
    rcases hix : (thetaChartDatum C R π a).pieceIndex x with i | i <;>
      rcases hjy : (thetaChartDatum C R π a).pieceIndex y with j | j
    all_goals
      rw [gluedSubordUnit_val_of_eq _ _ hσ hix hjy
          (inf_le_inf ((hix ▸ hσ x)) ((hjy ▸ hσ y))),
        gluedSubordUnit_val_of_eq (U := (thetaChartDatum C R π a).pieces)
          (thetaChartDatum C R π a).pointedCover
          (thetaChartDatum C R π a).pieceIndex (fun _ => le_rfl) hix hjy
          (inf_le_inf (le_of_eq (congrArg (thetaChartDatum C R π a).pieces hix))
            (le_of_eq (congrArg (thetaChartDatum C R π a).pieces hjy))),
        BasicOpenCocycleDatum.baseChange_unit_coe]
    -- the four chart cases
    · -- (0,0): both sides are `1`
      rw [show Units.val ((thetaChartDatum C k π a).unit (Sum.inl i) (Sum.inl j)) = 1
          from rfl,
        map_one, map_one,
        show Units.val ((thetaChartDatum C R π a).unit (Sum.inl i) (Sum.inl j)) = 1
          from rfl,
        map_one]
    · -- (0,1): both sides restrict the theta power
      rw [show Units.val ((thetaChartDatum C k π a).unit (Sum.inl i) (Sum.inr j))
          = (relCurve C k).resHom
              (inf_le_inf (thetaChartCover_pieces_le_inl C k π i)
                  (thetaChartCover_pieces_le_inr C k π j) :
                (thetaChartDatum C k π a).pieces (Sum.inl i)
                    ⊓ (thetaChartDatum C k π a).pieces (Sum.inr j)
                  ≤ (relCover C k (fiberTwoCover π)).V₀
                    ⊓ (relCover C k (fiberTwoCover π)).V₁)
              (Units.val (relThetaCocycle C k π a)) from rfl,
        show Units.val ((thetaChartDatum C R π a).unit (Sum.inl i) (Sum.inr j))
          = (relCurve C R).resHom
              (inf_le_inf (thetaChartCover_pieces_le_inl C R π i)
                  (thetaChartCover_pieces_le_inr C R π j) :
                (thetaChartDatum C R π a).pieces (Sum.inl i)
                    ⊓ (thetaChartDatum C R π a).pieces (Sum.inr j)
                  ≤ (relCover C R (fiberTwoCover π)).V₀
                    ⊓ (relCover C R (fiberTwoCover π)).V₁)
              (Units.val (relThetaCocycle C R π a)) from rfl,
        relThetaCocycle_val, relThetaCocycle_val]
      -- collapse both sides to a single `appLE` of the theta power along `fst_R`
      rw [overlapMap_apply, appLE_resHom_apply]
      have hcomp :
          (fst C (overSpec k k)).left.appLE (fiberChart₀ π ⊓ fiberChart₁ π)
              ((relCover C k (fiberTwoCover π)).V₀ ⊓ (relCover C k (fiberTwoCover π)).V₁)
              (le_of_eq (relCover_inf C k (fiberTwoCover π)))
            ≫ (relCurveMap C k R).appLE
              ((relCover C k (fiberTwoCover π)).V₀ ⊓ (relCover C k (fiberTwoCover π)).V₁)
              (((thetaChartDatum C k π a).toBasicOpenCoverData.baseChange R).pieces
                  (Sum.inl i)
                ⊓ ((thetaChartDatum C k π a).toBasicOpenCoverData.baseChange R).pieces
                  (Sum.inr j))
              (((thetaChartDatum C k π a).toBasicOpenCoverData.baseChange_inf_le_preimage
                  R (Sum.inl i) (Sum.inr j)).trans
                (Scheme.Hom.preimage_mono (relCurveMap C k R)
                  (inf_le_inf (thetaChartCover_pieces_le_inl C k π i)
                    (thetaChartCover_pieces_le_inr C k π j))))
          = (fst C (overSpec k R)).left.appLE (fiberChart₀ π ⊓ fiberChart₁ π)
              (((thetaChartDatum C k π a).toBasicOpenCoverData.baseChange R).pieces
                  (Sum.inl i)
                ⊓ ((thetaChartDatum C k π a).toBasicOpenCoverData.baseChange R).pieces
                  (Sum.inr j))
              ((((thetaChartDatum C k π a).toBasicOpenCoverData.baseChange_inf_le_preimage
                    R (Sum.inl i) (Sum.inr j)).trans
                  (Scheme.Hom.preimage_mono (relCurveMap C k R)
                    (inf_le_inf (thetaChartCover_pieces_le_inl C k π i)
                      (thetaChartCover_pieces_le_inr C k π j)))).trans
                ((Scheme.Hom.preimage_mono (relCurveMap C k R)
                    (le_of_eq (relCover_inf C k (fiberTwoCover π)))).trans
                  (le_of_eq (relCurveMap_preimage C k R
                    (fiberChart₀ π ⊓ fiberChart₁ π))))) := by
        rw [Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_hom (relCurveMap_fst C k R) _
      have hA := congr(($hcomp).hom
        (Units.val (thetaUnit π ^ a :
          Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)ˣ)))
      rw [CommRingCat.comp_apply] at hA
      rw [Scheme.resHom_resHom]
      exact (congrArg ((relCurve C R).resHom _) hA).trans
        ((resHom_appLE_apply (fst C (overSpec k R)).left _ _ _).trans
          (resHom_appLE_apply (fst C (overSpec k R)).left _ _ _).symm)
    · -- (1,0): both sides restrict the inverse theta power
      rw [show Units.val ((thetaChartDatum C k π a).unit (Sum.inr i) (Sum.inl j))
          = (relCurve C k).resHom
              (le_inf (inf_le_right.trans (thetaChartCover_pieces_le_inl C k π j))
                  (inf_le_left.trans (thetaChartCover_pieces_le_inr C k π i)) :
                (thetaChartDatum C k π a).pieces (Sum.inr i)
                    ⊓ (thetaChartDatum C k π a).pieces (Sum.inl j)
                  ≤ (relCover C k (fiberTwoCover π)).V₀
                    ⊓ (relCover C k (fiberTwoCover π)).V₁)
              (Units.val ((relThetaCocycle C k π a)⁻¹)) from rfl,
        show Units.val ((thetaChartDatum C R π a).unit (Sum.inr i) (Sum.inl j))
          = (relCurve C R).resHom
              (le_inf (inf_le_right.trans (thetaChartCover_pieces_le_inl C R π j))
                  (inf_le_left.trans (thetaChartCover_pieces_le_inr C R π i)) :
                (thetaChartDatum C R π a).pieces (Sum.inr i)
                    ⊓ (thetaChartDatum C R π a).pieces (Sum.inl j)
                  ≤ (relCover C R (fiberTwoCover π)).V₀
                    ⊓ (relCover C R (fiberTwoCover π)).V₁)
              (Units.val ((relThetaCocycle C R π a)⁻¹)) from rfl,
        relThetaCocycle_inv_val, relThetaCocycle_inv_val]
      rw [overlapMap_apply, appLE_resHom_apply]
      have hcomp :
          (fst C (overSpec k k)).left.appLE (fiberChart₀ π ⊓ fiberChart₁ π)
              ((relCover C k (fiberTwoCover π)).V₀ ⊓ (relCover C k (fiberTwoCover π)).V₁)
              (le_of_eq (relCover_inf C k (fiberTwoCover π)))
            ≫ (relCurveMap C k R).appLE
              ((relCover C k (fiberTwoCover π)).V₀ ⊓ (relCover C k (fiberTwoCover π)).V₁)
              (((thetaChartDatum C k π a).toBasicOpenCoverData.baseChange R).pieces
                  (Sum.inr i)
                ⊓ ((thetaChartDatum C k π a).toBasicOpenCoverData.baseChange R).pieces
                  (Sum.inl j))
              (((thetaChartDatum C k π a).toBasicOpenCoverData.baseChange_inf_le_preimage
                  R (Sum.inr i) (Sum.inl j)).trans
                (Scheme.Hom.preimage_mono (relCurveMap C k R)
                  (le_inf
                    (inf_le_right.trans (thetaChartCover_pieces_le_inl C k π j))
                    (inf_le_left.trans (thetaChartCover_pieces_le_inr C k π i)))))
          = (fst C (overSpec k R)).left.appLE (fiberChart₀ π ⊓ fiberChart₁ π)
              (((thetaChartDatum C k π a).toBasicOpenCoverData.baseChange R).pieces
                  (Sum.inr i)
                ⊓ ((thetaChartDatum C k π a).toBasicOpenCoverData.baseChange R).pieces
                  (Sum.inl j))
              ((((thetaChartDatum C k π a).toBasicOpenCoverData.baseChange_inf_le_preimage
                    R (Sum.inr i) (Sum.inl j)).trans
                  (Scheme.Hom.preimage_mono (relCurveMap C k R)
                    (le_inf
                      (inf_le_right.trans (thetaChartCover_pieces_le_inl C k π j))
                      (inf_le_left.trans (thetaChartCover_pieces_le_inr C k π i))))).trans
                ((Scheme.Hom.preimage_mono (relCurveMap C k R)
                    (le_of_eq (relCover_inf C k (fiberTwoCover π)))).trans
                  (le_of_eq (relCurveMap_preimage C k R
                    (fiberChart₀ π ⊓ fiberChart₁ π))))) := by
        rw [Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_hom (relCurveMap_fst C k R) _
      have hA := congr(($hcomp).hom
        (Units.val ((thetaUnit π ^ a :
          Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)ˣ)⁻¹)))
      rw [CommRingCat.comp_apply] at hA
      rw [Scheme.resHom_resHom]
      exact (congrArg ((relCurve C R).resHom _) hA).trans
        ((resHom_appLE_apply (fst C (overSpec k R)).left _ _ _).trans
          (resHom_appLE_apply (fst C (overSpec k R)).left _ _ _).symm)
    · -- (1,1): both sides are `1`
      rw [show Units.val ((thetaChartDatum C k π a).unit (Sum.inr i) (Sum.inr j)) = 1
          from rfl,
        map_one, map_one,
        show Units.val ((thetaChartDatum C R π a).unit (Sum.inr i) (Sum.inr j)) = 1
          from rfl,
        map_one]
  calc ((thetaChartDatum C k π a).baseChange R).cechPicClass
      = Scheme.CechPic.mk (thetaChartDatum C R π a).pointedCover
          (gluedSubordCocycle ((thetaChartDatum C k π a).baseChange R).isGluingCocycle
            (thetaChartDatum C R π a).pointedCover
            (thetaChartDatum C R π a).pieceIndex hσ).class :=
        (((thetaChartDatum C k π a).baseChange R).cechPicClass_eq_mk
          (thetaChartDatum C R π a).pointedCover
          (thetaChartDatum C R π a).pieceIndex hσ).symm
    _ = (thetaChartDatum C R π a).cechPicClass := by rw [hco]; rfl

/-- **The transported theta class along a tower** `k → R → R'`: the `relCurveMap`
pullback of the `R`-level whole-chart theta class is the class of the theta datum
base-changed to `R'` from the base field (`windowTransportDatum` when `R'` is a
field). -/
theorem cechPicClass_map_thetaChartDatum
    (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R'] :
    Scheme.CechPic.map (relCurveMap C R R') ((thetaChartDatum C R π a).cechPicClass)
      = ((thetaChartDatum C k π a).baseChange R').cechPicClass := by
  rw [← cechPicClass_baseChange_thetaChartDatum C R π a,
    BasicOpenCocycleDatum.cechPicClass_baseChange R (thetaChartDatum C k π a),
    BasicOpenCocycleDatum.cechPicClass_baseChange R' (thetaChartDatum C k π a),
    ← relCurveMap_comp (R := k) (R' := R) (R'' := R'), Scheme.CechPic.map_comp]
  rfl

end Naturality

end AlgebraicGeometry
