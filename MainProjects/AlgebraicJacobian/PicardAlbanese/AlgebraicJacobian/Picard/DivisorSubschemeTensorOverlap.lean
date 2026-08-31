/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.PiLocalization
import AlgebraicJacobian.Picard.DivisorSubschemeFaithfullyFlat

/-!
# The tensor square of the intrinsic divisor cover

For a certified widened adaptation, the intrinsic divisor is affine and its adapted
pieces form a finite affine open cover.  The coordinate ring of a pairwise intersection
is therefore the pushout of the two piece rings over global functions.  Transporting this
geometric pushout through the intrinsic divisor's section-ring identifications proves

`A.colength i ⊗[gluedSubalgebra A] A.colength j ≃ A.ovlColength i j`.

Taking the finite product over all pairs identifies the self-tensor square of the
faithfully flat chart algebra with the existing overlap-ring product.  Pure-tensor
formulas identify its two faces with `toOvlLeft` and `toOvlRight`; this is the ring-level
Cech interface needed by theta-module descent.  No containment, fixed-chart, or
`SwallowedBy` hypothesis is used.
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

/-- The section rings of two affine pieces of the intrinsic divisor and their intersection
form a pushout square. -/
theorem IsCertified.isPushout_divisorPieceSections [IsProper C.hom]
    (A : AffAdaptation D d) {n : Nat} (hc : A.IsCertified n)
    (i j : D.index) :
    let X := A.divisorSubscheme
    let U : X.Opens := A.divisorSubschemeι ⁻¹ᵁ D.pieces i
    let V : X.Opens := A.divisorSubschemeι ⁻¹ᵁ D.pieces j
    let W : X.Opens := U ⊓ V
    IsPushout
      (U.ι.appLE ⊤ ⊤ (show (⊤ : (U : Scheme).Opens) ≤
        U.ι ⁻¹ᵁ (⊤ : X.Opens) by simp))
      (V.ι.appLE ⊤ ⊤ (show (⊤ : (V : Scheme).Opens) ≤
        V.ι ⁻¹ᵁ (⊤ : X.Opens) by simp))
      ((X.homOfLE (show W ≤ U from inf_le_left)).appLE ⊤ ⊤
        (show (⊤ : (W : Scheme).Opens) ≤
          (X.homOfLE (show W ≤ U from inf_le_left)) ⁻¹ᵁ
            (⊤ : (U : Scheme).Opens) by simp))
      ((X.homOfLE (show W ≤ V from inf_le_right)).appLE ⊤ ⊤
        (show (⊤ : (W : Scheme).Opens) ≤
          (X.homOfLE (show W ≤ V from inf_le_right)) ⁻¹ᵁ
            (⊤ : (V : Scheme).Opens) by simp)) := by
  dsimp only
  let X := A.divisorSubscheme
  let U : X.Opens := A.divisorSubschemeι ⁻¹ᵁ D.pieces i
  let V : X.Opens := A.divisorSubschemeι ⁻¹ᵁ D.pieces j
  let W : X.Opens := U ⊓ V
  letI : IsAffine X := A.isAffine_divisorSubscheme hc
  letI : IsAffine U := A.isAffineOpen_divisorPiece i
  letI : IsAffine V := A.isAffineOpen_divisorPiece j
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

/-- The widened equalizer algebra, two piece colength algebras, and their overlap
colength algebra form the same pushout square as the corresponding section rings. -/
theorem IsCertified.isPushout_gluedSubalgebraPieceMaps [IsProper C.hom]
    (A : AffAdaptation D d) {n : Nat} (hc : A.IsCertified n)
    (i j : D.index) :
    IsPushout
      (CommRingCat.ofHom (A.gluedSubalgebraPieceMap i).toRingHom)
      (CommRingCat.ofHom (A.gluedSubalgebraPieceMap j).toRingHom)
      (CommRingCat.ofHom (A.toOvlLeft i j).toRingHom)
      (CommRingCat.ofHom (A.toOvlRight i j).toRingHom) := by
  let X := A.divisorSubscheme
  let U : X.Opens := A.divisorSubschemeι ⁻¹ᵁ D.pieces i
  let V : X.Opens := A.divisorSubschemeι ⁻¹ᵁ D.pieces j
  let W : X.Opens := U ⊓ V
  let hU : (⊤ : (U : Scheme).Opens) ≤ U.ι ⁻¹ᵁ (⊤ : X.Opens) := by simp
  let hV : (⊤ : (V : Scheme).Opens) ≤ V.ι ⁻¹ᵁ (⊤ : X.Opens) := by simp
  let hWU : (⊤ : (W : Scheme).Opens) ≤
      (X.homOfLE (show W ≤ U from inf_le_left)) ⁻¹ᵁ
        (⊤ : (U : Scheme).Opens) := by simp
  let hWV : (⊤ : (W : Scheme).Opens) ≤
      (X.homOfLE (show W ≤ V from inf_le_right)) ⁻¹ᵁ
        (⊤ : (V : Scheme).Opens) := by simp
  let e0 : Γ(X, ⊤) ≅ CommRingCat.of (gluedSubalgebra A) :=
    A.divisorGlobalSectionsEquivGlued.toCommRingCatIso
  let ei : Γ((U : Scheme), ⊤) ≅ CommRingCat.of (A.colength i) :=
    U.topIso ≪≫ A.divisorSubschemePieceIso i
  let ej : Γ((V : Scheme), ⊤) ≅ CommRingCat.of (A.colength j) :=
    V.topIso ≪≫ A.divisorSubschemePieceIso j
  let ew : Γ((W : Scheme), ⊤) ≅ CommRingCat.of (A.ovlColength i j) :=
    W.topIso ≪≫ A.divisorSubschemeOverlapIso i j
  have hresU : U.ι.appLE ⊤ ⊤ hU ≫ U.topIso.hom =
      X.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op := by
    rw [show U.ι.appLE ⊤ ⊤ hU = U.ι.appTop from Scheme.Hom.appLE_eq_app U.ι]
    simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
    rw [← X.presheaf.map_comp]
    congr 1
  have hresV : V.ι.appLE ⊤ ⊤ hV ≫ V.topIso.hom =
      X.presheaf.map (homOfLE (le_top : V ≤ (⊤ : X.Opens))).op := by
    rw [show V.ι.appLE ⊤ ⊤ hV = V.ι.appTop from Scheme.Hom.appLE_eq_app V.ι]
    simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
    rw [← X.presheaf.map_comp]
    congr 1
  have hgeo := hc.isPushout_divisorPieceSections A i j
  refine hgeo.of_iso e0 ei ej ew ?_ ?_ ?_ ?_
  · simp only [ei, e0, Iso.trans_hom]
    rw [← Category.assoc, hresU]
    apply ConcreteCategory.hom_ext
    intro s
    change A.divisorSubschemePieceRingEquiv i
        ((X.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op).hom s) =
      (A.divisorGlobalSectionsEquivGlued s).1 i
    exact (A.divisorGlobalSectionsEquivGlued_apply s i).symm
  · simp only [ej, e0, Iso.trans_hom]
    rw [← Category.assoc, hresV]
    apply ConcreteCategory.hom_ext
    intro s
    change A.divisorSubschemePieceRingEquiv j
        ((X.presheaf.map (homOfLE (le_top : V ≤ (⊤ : X.Opens))).op).hom s) =
      (A.divisorGlobalSectionsEquivGlued s).1 j
    exact (A.divisorGlobalSectionsEquivGlued_apply s j).symm
  · simp only [ei, ew, Iso.trans_hom, Category.assoc]
    rw [show (X.homOfLE (show W ≤ U from inf_le_left)).appLE ⊤ ⊤ hWU =
      (X.homOfLE (show W ≤ U from inf_le_left)).appTop from
        Scheme.Hom.appLE_eq_app _]
    rw [← Category.assoc, topIso_naturality]
    rw [Category.assoc, A.divisorSubschemePieceIso_res_left]
  · simp only [ej, ew, Iso.trans_hom, Category.assoc]
    rw [show (X.homOfLE (show W ≤ V from inf_le_right)).appLE ⊤ ⊤ hWV =
      (X.homOfLE (show W ≤ V from inf_le_right)).appTop from
        Scheme.Hom.appLE_eq_app _]
    rw [← Category.assoc, topIso_naturality]
    rw [Category.assoc, A.divisorSubschemePieceIso_res_right]

/-- The canonical algebra structure on a divisor piece over the widened equalizer
algebra. -/
@[reducible]
noncomputable instance gluedSubalgebraPieceAlgebra
    (A : AffAdaptation D d) (i : D.index) :
    Algebra (gluedSubalgebra A) (A.colength i) :=
  (A.gluedSubalgebraPieceMap i).toRingHom.toAlgebra

/-- The canonical algebra structure on a pairwise overlap over the widened equalizer
algebra, through the left piece. -/
@[reducible]
noncomputable instance gluedSubalgebraOverlapAlgebra
    (A : AffAdaptation D d) (i j : D.index) :
    Algebra (gluedSubalgebra A) (A.ovlColength i j) :=
  ((A.toOvlLeft i j).comp (A.gluedSubalgebraPieceMap i)).toRingHom.toAlgebra

/-- A pairwise overlap ring is the tensor product of its two piece rings over the
widened equalizer algebra. -/
noncomputable def IsCertified.divisorPieceTensorOverlapEquiv [IsProper C.hom]
    (A : AffAdaptation D d) {n : Nat} (hc : A.IsCertified n)
    (i j : D.index) :
    A.colength i ⊗[gluedSubalgebra A] A.colength j ≃ₐ[gluedSubalgebra A]
      A.ovlColength i j := by
  let e := ((CommRingCat.isPushout_tensorProduct (gluedSubalgebra A)
    (A.colength i) (A.colength j)).isoIsPushout _ _
      (hc.isPushout_gluedSubalgebraPieceMaps A i j)).commRingCatIsoToRingEquiv
  refine AlgEquiv.ofRingEquiv (f := e) fun c => ?_
  exact congr($((CommRingCat.isPushout_tensorProduct (gluedSubalgebra A)
    (A.colength i) (A.colength j)).inl_isoIsPushout_hom _ _
      (hc.isPushout_gluedSubalgebraPieceMaps A i j)).hom
        ((A.gluedSubalgebraPieceMap i) c))

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent piece algebra takes more than the default budget to synthesize here.
@[simp]
theorem IsCertified.divisorPieceTensorOverlapEquiv_tmul_one [IsProper C.hom]
    (A : AffAdaptation D d) {n : Nat} (hc : A.IsCertified n)
    (i j : D.index) (x : A.colength i) :
    hc.divisorPieceTensorOverlapEquiv A i j (x ⊗ₜ 1) = A.toOvlLeft i j x := by
  exact congr($((CommRingCat.isPushout_tensorProduct (gluedSubalgebra A)
    (A.colength i) (A.colength j)).inl_isoIsPushout_hom _ _
      (hc.isPushout_gluedSubalgebraPieceMaps A i j)).hom x)

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent piece algebra takes more than the default budget to synthesize here.
@[simp]
theorem IsCertified.divisorPieceTensorOverlapEquiv_one_tmul [IsProper C.hom]
    (A : AffAdaptation D d) {n : Nat} (hc : A.IsCertified n)
    (i j : D.index) (y : A.colength j) :
    hc.divisorPieceTensorOverlapEquiv A i j (1 ⊗ₜ y) = A.toOvlRight i j y := by
  exact congr($((CommRingCat.isPushout_tensorProduct (gluedSubalgebra A)
    (A.colength i) (A.colength j)).inr_isoIsPushout_hom _ _
      (hc.isPushout_gluedSubalgebraPieceMaps A i j)).hom y)

set_option synthInstance.maxHeartbeats 100000 in
-- Both dependent piece algebras are synthesized while elaborating this pure tensor.
@[simp]
theorem IsCertified.divisorPieceTensorOverlapEquiv_tmul [IsProper C.hom]
    (A : AffAdaptation D d) {n : Nat} (hc : A.IsCertified n)
    (i j : D.index) (x : A.colength i) (y : A.colength j) :
    hc.divisorPieceTensorOverlapEquiv A i j (x ⊗ₜ y) =
      A.toOvlLeft i j x * A.toOvlRight i j y := by
  rw [show (x ⊗ₜ[gluedSubalgebra A] y) =
      (x ⊗ₜ 1) * (1 ⊗ₜ y) by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
    map_mul, hc.divisorPieceTensorOverlapEquiv_tmul_one,
    hc.divisorPieceTensorOverlapEquiv_one_tmul]

/-- The tensor square of the finite faithfully flat chart algebra is the product of the
intrinsic pairwise overlap rings. -/
noncomputable def IsCertified.chartProdTensorOverlapEquiv [IsProper C.hom]
    (A : AffAdaptation D d) {n : Nat} (hc : A.IsCertified n) :
    A.chartProd ⊗[gluedSubalgebra A] A.chartProd ≃ₐ[gluedSubalgebra A]
      (forall p : D.index × D.index, A.ovlColength p.1 p.2) := by
  exact (Algebra.TensorProduct.piPiAlgEquiv (gluedSubalgebra A)
    (fun i : D.index => A.colength i)
    (fun i : D.index => A.colength i)).trans
      (AlgEquiv.piCongrRight fun p =>
        hc.divisorPieceTensorOverlapEquiv A p.1 p.2)

set_option synthInstance.maxHeartbeats 100000 in
-- The product tensor expands to all dependent pairwise piece algebras.
@[simp]
theorem IsCertified.chartProdTensorOverlapEquiv_tmul [IsProper C.hom]
    (A : AffAdaptation D d) {n : Nat} (hc : A.IsCertified n)
    (x y : A.chartProd) :
    hc.chartProdTensorOverlapEquiv A (x ⊗ₜ y) = fun p =>
      A.toOvlLeft p.1 p.2 (x p.1) * A.toOvlRight p.1 p.2 (y p.2) := by
  funext p
  simp only [IsCertified.chartProdTensorOverlapEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.piPiAlgEquiv_tmul, AlgEquiv.piCongrRight_apply]
  exact hc.divisorPieceTensorOverlapEquiv_tmul A p.1 p.2 (x p.1) (y p.2)

end AffAdaptation

end AlgebraicGeometry
