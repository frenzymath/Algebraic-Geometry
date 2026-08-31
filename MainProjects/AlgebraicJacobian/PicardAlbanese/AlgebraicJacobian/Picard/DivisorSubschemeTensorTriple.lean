/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorSubschemeTriple

/-!
# Tensor products and triple intersections of the intrinsic divisor cover

For a certified widened adaptation, a pairwise divisor intersection and a third divisor
piece are affine opens of the affine intrinsic divisor.  Their section rings therefore
form a pushout over global divisor functions.  Transporting the square through the
intrinsic quotient identifications gives

`ovlColength i j ⊗[gluedSubalgebra A] colength l ≃ tripleColength i j l`.

The pure-tensor formulas identify the two structure maps with `ovlToTriple` and
`pieceToTripleThird`.  No chart typing or containment hypothesis is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

/-- Section rings of two affine opens in the affine intrinsic divisor form a pushout over
global sections. -/
theorem IsCertified.isPushout_divisorOpenSections [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n)
    (U V : A.divisorSubscheme.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    let W : A.divisorSubscheme.Opens := U ⊓ V
    IsPushout
      (U.ι.appLE ⊤ ⊤ (show (⊤ : (U : Scheme).Opens) ≤
        U.ι ⁻¹ᵁ (⊤ : A.divisorSubscheme.Opens) by simp))
      (V.ι.appLE ⊤ ⊤ (show (⊤ : (V : Scheme).Opens) ≤
        V.ι ⁻¹ᵁ (⊤ : A.divisorSubscheme.Opens) by simp))
      ((A.divisorSubscheme.homOfLE (show W ≤ U from inf_le_left)).appLE ⊤ ⊤
        (show (⊤ : (W : Scheme).Opens) ≤
          (A.divisorSubscheme.homOfLE (show W ≤ U from inf_le_left)) ⁻¹ᵁ
            (⊤ : (U : Scheme).Opens) by simp))
      ((A.divisorSubscheme.homOfLE (show W ≤ V from inf_le_right)).appLE ⊤ ⊤
        (show (⊤ : (W : Scheme).Opens) ≤
          (A.divisorSubscheme.homOfLE (show W ≤ V from inf_le_right)) ⁻¹ᵁ
            (⊤ : (V : Scheme).Opens) by simp)) := by
  dsimp only
  let X := A.divisorSubscheme
  let W : X.Opens := U ⊓ V
  letI : IsAffine X := A.isAffine_divisorSubscheme hc
  letI : IsAffine U := hU
  letI : IsAffine V := hV
  have H : IsPullback
      (X.homOfLE (show W ≤ U from inf_le_left))
      (X.homOfLE (show W ≤ V from inf_le_right)) U.ι V.ι :=
    isPullback_opens_inf U V
  have h := isIso_pushoutSection_of_isAffineOpen H
    (show (⊤ : (V : Scheme).Opens) ≤ V.ι ⁻¹ᵁ (⊤ : X.Opens) by simp)
    (show (⊤ : (U : Scheme).Opens) ≤ U.ι ⁻¹ᵁ (⊤ : X.Opens) by simp)
    (show (⊤ : (W : Scheme).Opens) =
      (X.homOfLE (show W ≤ U from inf_le_left)) ⁻¹ᵁ
          (⊤ : (U : Scheme).Opens) ⊓
        (X.homOfLE (show W ≤ V from inf_le_right)) ⁻¹ᵁ
          (⊤ : (V : Scheme).Opens) by simp)
    (isAffineOpen_top X) (isAffineOpen_top V) (isAffineOpen_top U)
  exact (isIso_pushoutSection_iff _ _ _ _).mp h

private theorem topIso_naturality (X : Scheme.{u}) {W U : X.Opens} (h : W ≤ U) :
    (X.homOfLE h).appTop ≫ W.topIso.hom =
      U.topIso.hom ≫ X.presheaf.map (homOfLE h).op := by
  exact X.restrictFunctorΓ.hom.naturality (homOfLE h).op

/-- The widened equalizer algebra, a pairwise colength algebra, a third piece colength
algebra, and the triple colength algebra form a pushout square. -/
theorem IsCertified.isPushout_gluedSubalgebraOverlapPieceMaps [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n)
    (i j l : D.index) :
    IsPushout
      (CommRingCat.ofHom (A.gluedSubalgebraOverlapMap i j).toRingHom)
      (CommRingCat.ofHom (A.gluedSubalgebraPieceMap l).toRingHom)
      (CommRingCat.ofHom (A.ovlToTriple i j i j l
        (A.thetaTripleOpen_le_pair12 i j l)).toRingHom)
      (CommRingCat.ofHom (A.pieceToTripleThird i j l).toRingHom) := by
  let X := A.divisorSubscheme
  let U : X.Opens := A.divisorSubschemeι ⁻¹ᵁ (D.pieces i ⊓ D.pieces j)
  let V : X.Opens := A.divisorSubschemeι ⁻¹ᵁ D.pieces l
  let W : X.Opens := U ⊓ V
  let hU : IsAffineOpen U := A.isAffineOpen_divisorPreimageAffine
    ⟨D.pieces i ⊓ D.pieces j, D.hasAffineOverlaps_of_isProper i j⟩
  let hV : IsAffineOpen V := A.isAffineOpen_divisorPiece l
  let hUtop : (⊤ : (U : Scheme).Opens) ≤ U.ι ⁻¹ᵁ (⊤ : X.Opens) := by simp
  let hVtop : (⊤ : (V : Scheme).Opens) ≤ V.ι ⁻¹ᵁ (⊤ : X.Opens) := by simp
  let hWU : (⊤ : (W : Scheme).Opens) ≤
      (X.homOfLE (show W ≤ U from inf_le_left)) ⁻¹ᵁ
        (⊤ : (U : Scheme).Opens) := by simp
  let hWV : (⊤ : (W : Scheme).Opens) ≤
      (X.homOfLE (show W ≤ V from inf_le_right)) ⁻¹ᵁ
        (⊤ : (V : Scheme).Opens) := by simp
  let e0 : Γ(X, ⊤) ≅ CommRingCat.of (gluedSubalgebra A) :=
    A.divisorGlobalSectionsEquivGlued.toCommRingCatIso
  let eU : Γ((U : Scheme), ⊤) ≅ CommRingCat.of (A.ovlColength i j) :=
    U.topIso ≪≫ A.divisorSubschemeOverlapIso i j
  let eV : Γ((V : Scheme), ⊤) ≅ CommRingCat.of (A.colength l) :=
    V.topIso ≪≫ A.divisorSubschemePieceIso l
  let eW : Γ((W : Scheme), ⊤) ≅ CommRingCat.of (A.tripleColength i j l) :=
    W.topIso ≪≫ A.divisorSubschemeTripleIso i j l
  have hresU : U.ι.appLE ⊤ ⊤ hUtop ≫ U.topIso.hom =
      X.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op := by
    rw [show U.ι.appLE ⊤ ⊤ hUtop = U.ι.appTop from Scheme.Hom.appLE_eq_app U.ι]
    simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
    rw [← X.presheaf.map_comp]
    congr 1
  have hresV : V.ι.appLE ⊤ ⊤ hVtop ≫ V.topIso.hom =
      X.presheaf.map (homOfLE (le_top : V ≤ (⊤ : X.Opens))).op := by
    rw [show V.ι.appLE ⊤ ⊤ hVtop = V.ι.appTop from Scheme.Hom.appLE_eq_app V.ι]
    simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
    rw [← X.presheaf.map_comp]
    congr 1
  have hgeo := hc.isPushout_divisorOpenSections A U V hU hV
  refine hgeo.of_iso e0 eU eV eW ?_ ?_ ?_ ?_
  · simp only [eU, e0, Iso.trans_hom]
    rw [← Category.assoc, hresU]
    apply ConcreteCategory.hom_ext
    intro s
    let si := X.presheaf.map
      (homOfLE (le_top : A.divisorSubschemeι ⁻¹ᵁ D.pieces i ≤
        (⊤ : X.Opens))).op s
    have hcomp :
        X.presheaf.map
            (homOfLE (show A.divisorSubschemeι ⁻¹ᵁ (D.pieces i ⊓ D.pieces j) ≤
              A.divisorSubschemeι ⁻¹ᵁ D.pieces i by
                intro x hx
                exact hx.1)).op si =
          X.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op s := by
      rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
      rfl
    have hleft := congrArg (fun f => f.hom si)
      (A.divisorSubschemePieceIso_res_left i j)
    change (A.divisorSubschemeOverlapIso i j).hom.hom
        (X.presheaf.map
          (homOfLE (show A.divisorSubschemeι ⁻¹ᵁ (D.pieces i ⊓ D.pieces j) ≤
            A.divisorSubschemeι ⁻¹ᵁ D.pieces i by
              intro x hx
              exact hx.1)).op si) =
      A.toOvlLeft i j ((A.divisorSubschemePieceIso i).hom.hom si) at hleft
    change (A.divisorSubschemeOverlapIso i j).hom.hom
        (X.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op s) =
      A.toOvlLeft i j ((A.divisorGlobalSectionsEquivGlued s).1 i)
    rw [← hcomp, hleft]
    exact congrArg (A.toOvlLeft i j)
      (A.divisorGlobalSectionsEquivGlued_apply s i).symm
  · simp only [eV, e0, Iso.trans_hom]
    rw [← Category.assoc, hresV]
    apply ConcreteCategory.hom_ext
    intro s
    change A.divisorSubschemePieceRingEquiv l
        ((X.presheaf.map (homOfLE (le_top : V ≤ (⊤ : X.Opens))).op).hom s) =
      (A.divisorGlobalSectionsEquivGlued s).1 l
    exact (A.divisorGlobalSectionsEquivGlued_apply s l).symm
  · simp only [eU, eW, Iso.trans_hom, Category.assoc]
    rw [show (X.homOfLE (show W ≤ U from inf_le_left)).appLE ⊤ ⊤ hWU =
      (X.homOfLE (show W ≤ U from inf_le_left)).appTop from
        Scheme.Hom.appLE_eq_app _]
    rw [← Category.assoc, topIso_naturality]
    rw [Category.assoc, A.divisorSubschemeOverlapIso_res_triple12]
  · simp only [eV, eW, Iso.trans_hom, Category.assoc]
    rw [show (X.homOfLE (show W ≤ V from inf_le_right)).appLE ⊤ ⊤ hWV =
      (X.homOfLE (show W ≤ V from inf_le_right)).appTop from
        Scheme.Hom.appLE_eq_app _]
    rw [← Category.assoc, topIso_naturality]
    rw [Category.assoc, A.divisorSubschemePieceIso_res_tripleThird]

/-- The canonical triple colength algebra over global divisor functions. -/
@[reducible]
noncomputable def gluedSubalgebraTripleAlgebra [IsProper C.hom]
    (A : AffAdaptation D d)
    (i j l : D.index) :
    Algebra (gluedSubalgebra A) (A.tripleColength i j l) :=
  ((A.ovlToTriple i j i j l (A.thetaTripleOpen_le_pair12 i j l)).comp
    (A.gluedSubalgebraOverlapMap i j)).toRingHom.toAlgebra

attribute [local instance] gluedSubalgebraTripleAlgebra

/-- A triple colength ring is the tensor product of its first overlap ring and third
piece ring over global divisor functions. -/
noncomputable def IsCertified.divisorOverlapTensorPieceTripleEquiv [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n) (i j l : D.index) :
    A.ovlColength i j ⊗[gluedSubalgebra A] A.colength l
      ≃ₐ[gluedSubalgebra A] A.tripleColength i j l := by
  let e := ((CommRingCat.isPushout_tensorProduct (gluedSubalgebra A)
    (A.ovlColength i j) (A.colength l)).isoIsPushout _ _
      (hc.isPushout_gluedSubalgebraOverlapPieceMaps A i j l)).commRingCatIsoToRingEquiv
  refine AlgEquiv.ofRingEquiv (f := e) fun c => ?_
  exact congr($((CommRingCat.isPushout_tensorProduct (gluedSubalgebra A)
    (A.ovlColength i j) (A.colength l)).inl_isoIsPushout_hom _ _
      (hc.isPushout_gluedSubalgebraOverlapPieceMaps A i j l)).hom
        ((A.gluedSubalgebraOverlapMap i j) c))

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent overlap algebra is synthesized while elaborating the pure tensor.
@[simp]
theorem IsCertified.divisorOverlapTensorPieceTripleEquiv_tmul_one [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n)
    (i j l : D.index) (x : A.ovlColength i j) :
    hc.divisorOverlapTensorPieceTripleEquiv A i j l (x ⊗ₜ 1) =
      A.ovlToTriple i j i j l (A.thetaTripleOpen_le_pair12 i j l) x := by
  exact congr($((CommRingCat.isPushout_tensorProduct (gluedSubalgebra A)
    (A.ovlColength i j) (A.colength l)).inl_isoIsPushout_hom _ _
      (hc.isPushout_gluedSubalgebraOverlapPieceMaps A i j l)).hom x)

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent overlap algebra is synthesized while elaborating the pure tensor.
@[simp]
theorem IsCertified.divisorOverlapTensorPieceTripleEquiv_one_tmul [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n)
    (i j l : D.index) (y : A.colength l) :
    hc.divisorOverlapTensorPieceTripleEquiv A i j l (1 ⊗ₜ y) =
      A.pieceToTripleThird i j l y := by
  exact congr($((CommRingCat.isPushout_tensorProduct (gluedSubalgebra A)
    (A.ovlColength i j) (A.colength l)).inr_isoIsPushout_hom _ _
      (hc.isPushout_gluedSubalgebraOverlapPieceMaps A i j l)).hom y)

set_option synthInstance.maxHeartbeats 100000 in
-- Both dependent source algebras are synthesized in the tensor-product multiplication.
@[simp]
theorem IsCertified.divisorOverlapTensorPieceTripleEquiv_tmul [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n)
    (i j l : D.index) (x : A.ovlColength i j) (y : A.colength l) :
    hc.divisorOverlapTensorPieceTripleEquiv A i j l (x ⊗ₜ y) =
      A.ovlToTriple i j i j l (A.thetaTripleOpen_le_pair12 i j l) x *
        A.pieceToTripleThird i j l y := by
  rw [show (x ⊗ₜ[gluedSubalgebra A] y) =
      (x ⊗ₜ 1) * (1 ⊗ₜ y) by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
    map_mul, hc.divisorOverlapTensorPieceTripleEquiv_tmul_one,
    hc.divisorOverlapTensorPieceTripleEquiv_one_tmul]

end AffAdaptation

end AlgebraicGeometry
