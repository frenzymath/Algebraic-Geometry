/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.TensorProductPushoutBaseChange
import AlgebraicJacobian.Descent.TensorProductPushoutData
import AlgebraicJacobian.Descent.TensorProductFiniteType
import AlgebraicJacobian.Picard.Pic0FiniteStageTransitionModels

/-!
# Triple-overlap rings in the finite-stage Picard atlas

For three charts `U`, `V`, and `W`, the literal triple intersection is presented over
the left chart by

`Gamma(U intersect V) tensor_[Gamma(U)] Gamma(U intersect W)`.

The first half of this file proves that this tensor product is the section ring of the
exact triple intersection in the separably closed Picard representer.  The second half
forms the same tensor pushout from the descended restriction maps and proves that scalar
extension commutes with this construction.

This is the object layer for the triple pullbacks in `Scheme.GlueData`.  Constructing the
cyclic `t'` maps still requires transporting the exact transition comparison through the
finite-stage model equivalences and reflecting its cocycle equation; no such gluing claim
is made here.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

/-! ## Section rings of affine opens -/

/-- If two affine opens lie in an affine open, their section rings and the section ring
of their intersection form a pushout. -/
private theorem isPushout_affineOpenSections_inf
    {X : Scheme.{u}} (W U V : X.Opens)
    (hW : IsAffineOpen W) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUW : U <= W) (hVW : V <= W) :
    let T := U ⊓ V
    IsPushout
      (X.presheaf.map (homOfLE hUW).op)
      (X.presheaf.map (homOfLE hVW).op)
      (X.presheaf.map (homOfLE (show T <= U from inf_le_left)).op)
      (X.presheaf.map (homOfLE (show T <= V from inf_le_right)).op) := by
  dsimp only
  let T := U ⊓ V
  letI : IsAffine W := hW
  letI : IsAffine U := hU
  letI : IsAffine V := hV
  have H : IsPullback
      (X.homOfLE (show T <= U from inf_le_left))
      (X.homOfLE (show T <= V from inf_le_right))
      (X.homOfLE hUW) (X.homOfLE hVW) :=
    isPullback_opens_inf_le hUW hVW
  have hi := isIso_pushoutSection_of_isAffineOpen H
    (show (⊤ : (V : Scheme).Opens) <=
      (X.homOfLE hVW) ⁻¹ᵁ (⊤ : (W : Scheme).Opens) by simp)
    (show (⊤ : (U : Scheme).Opens) <=
      (X.homOfLE hUW) ⁻¹ᵁ (⊤ : (W : Scheme).Opens) by simp)
    (show (⊤ : (T : Scheme).Opens) =
      (X.homOfLE (show T <= U from inf_le_left)) ⁻¹ᵁ
          (⊤ : (U : Scheme).Opens) ⊓
        (X.homOfLE (show T <= V from inf_le_right)) ⁻¹ᵁ
          (⊤ : (V : Scheme).Opens) by simp)
    (isAffineOpen_top W) (isAffineOpen_top V) (isAffineOpen_top U)
  have hgeo := (isIso_pushoutSection_iff _ _ _ _).mp hi
  have hnat (A B : X.Opens) (hAB : A <= B) :
      (X.homOfLE hAB).appTop ≫ A.topIso.hom =
        B.topIso.hom ≫ X.presheaf.map (homOfLE hAB).op :=
    X.restrictFunctorΓ.hom.naturality (homOfLE hAB).op
  refine hgeo.of_iso W.topIso U.topIso V.topIso T.topIso ?_ ?_ ?_ ?_
  · rw [show (X.homOfLE hUW).appLE ⊤ ⊤ _ =
      (X.homOfLE hUW).appTop from Scheme.Hom.appLE_eq_app _]
    exact hnat U W hUW
  · rw [show (X.homOfLE hVW).appLE ⊤ ⊤ _ =
      (X.homOfLE hVW).appTop from Scheme.Hom.appLE_eq_app _]
    exact hnat V W hVW
  · rw [show (X.homOfLE (show T <= U from inf_le_left)).appLE ⊤ ⊤ _ =
      (X.homOfLE (show T <= U from inf_le_left)).appTop from
        Scheme.Hom.appLE_eq_app _]
    exact hnat T U inf_le_left
  · rw [show (X.homOfLE (show T <= V from inf_le_right)).appLE ⊤ ⊤ _ =
      (X.homOfLE (show T <= V from inf_le_right)).appTop from
        Scheme.Hom.appLE_eq_app _]
    exact hnat T V inf_le_right

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

/-! ## The exact triple-overlap ring -/

/-- The literal triple intersection, expressed as the intersection of the two overlaps
which use `U` as their left chart. -/
def Pic0FiniteStageTripleOpen
    (U V W : Pic0FiniteStageChartIndex C) :
    (pic0_sepClosed_representableBy (C := C)).1.left.Opens :=
  (U.1.1 ⊓ V.1.1) ⊓ (U.1.1 ⊓ W.1.1)

/-- The literal triple intersection of three finite-stage charts is affine. -/
theorem pic0FiniteStageTripleOpen_isAffine
    (U V W : Pic0FiniteStageChartIndex C) :
    IsAffineOpen (Pic0FiniteStageTripleOpen C U V W) := by
  let J := (pic0_sepClosed_representableBy (C := C)).1
  letI : GrpObj J := (picRepDatumSepClosed C).grpObj
  haveI : IsSeparated J.hom := isSeparated_of_grpObj J
  haveI : Scheme.IsSeparated J.left := by
    constructor
    rw [← Limits.terminal.comp_from J.hom]
    infer_instance
  exact (pic0FiniteStageAffineOverlap C U V).2.inf
    (pic0FiniteStageAffineOverlap C U W).2

/-- The section ring of the literal triple intersection. -/
def Pic0FiniteStageTripleRing
    (U V W : Pic0FiniteStageChartIndex C) : Type u :=
  Γ((pic0_sepClosed_representableBy (C := C)).1.left,
    Pic0FiniteStageTripleOpen C U V W)

instance (U V W : Pic0FiniteStageChartIndex C) :
    CommRing (Pic0FiniteStageTripleRing C U V W) := by
  dsimp [Pic0FiniteStageTripleRing]
  infer_instance

noncomputable instance (U V W : Pic0FiniteStageChartIndex C) :
    Algebra k (Pic0FiniteStageTripleRing C U V W) := by
  let J := (pic0_sepClosed_representableBy (C := C)).1
  letI : J.left.Over (Spec (.of k)) := ⟨J.hom⟩
  exact (J.left.overAlgebraMap k (Pic0FiniteStageTripleOpen C U V W)).toAlgebra

/-- Restriction from the first pair-overlap to the triple intersection. -/
noncomputable def pic0FiniteStageOverlapToTripleLeft
    (U V W : Pic0FiniteStageChartIndex C) :
    Pic0FiniteStageOverlapRing C U V →ₐ[k]
      Pic0FiniteStageTripleRing C U V W := by
  let J := (pic0_sepClosed_representableBy (C := C)).1
  letI : J.left.Over (Spec (.of k)) := ⟨J.hom⟩
  exact
    { J.left.resHom
        (show Pic0FiniteStageTripleOpen C U V W <= U.1.1 ⊓ V.1.1 from inf_le_left) with
      commutes' := fun r => J.left.overAlgebraMap_apply_res k _ r }

/-- Restriction from the second pair-overlap to the triple intersection. -/
noncomputable def pic0FiniteStageOverlapToTripleRight
    (U V W : Pic0FiniteStageChartIndex C) :
    Pic0FiniteStageOverlapRing C U W →ₐ[k]
      Pic0FiniteStageTripleRing C U V W := by
  let J := (pic0_sepClosed_representableBy (C := C)).1
  letI : J.left.Over (Spec (.of k)) := ⟨J.hom⟩
  exact
    { J.left.resHom
        (show Pic0FiniteStageTripleOpen C U V W <= U.1.1 ⊓ W.1.1 from inf_le_right) with
      commutes' := fun r => J.left.overAlgebraMap_apply_res k _ r }

/-- The left-chart ring, its two pair-overlap rings, and the literal triple-intersection
ring form a pushout square. -/
theorem isPushout_pic0FiniteStageTripleRing
    (U V W : Pic0FiniteStageChartIndex C) :
    IsPushout
      (CommRingCat.ofHom (pic0FiniteStageRestrictionLeft C U V).toRingHom)
      (CommRingCat.ofHom (pic0FiniteStageRestrictionLeft C U W).toRingHom)
      (CommRingCat.ofHom (pic0FiniteStageOverlapToTripleLeft C U V W).toRingHom)
      (CommRingCat.ofHom (pic0FiniteStageOverlapToTripleRight C U V W).toRingHom) := by
  change IsPushout
    (((pic0_sepClosed_representableBy (C := C)).1.left).presheaf.map
      (homOfLE (pic0FiniteStageAffineOverlap_le_left C U V)).op)
    (((pic0_sepClosed_representableBy (C := C)).1.left).presheaf.map
      (homOfLE (pic0FiniteStageAffineOverlap_le_left C U W)).op)
    (((pic0_sepClosed_representableBy (C := C)).1.left).presheaf.map
      (homOfLE (show Pic0FiniteStageTripleOpen C U V W <= U.1.1 ⊓ V.1.1 from
        inf_le_left)).op)
    (((pic0_sepClosed_representableBy (C := C)).1.left).presheaf.map
      (homOfLE (show Pic0FiniteStageTripleOpen C U V W <= U.1.1 ⊓ W.1.1 from
        inf_le_right)).op)
  exact isPushout_affineOpenSections_inf
    U.1.1 (U.1.1 ⊓ V.1.1) (U.1.1 ⊓ W.1.1)
    U.1.2 (pic0FiniteStageAffineOverlap C U V).2
    (pic0FiniteStageAffineOverlap C U W).2 inf_le_left inf_le_left

/-- The first pair-overlap as an algebra over the left chart. -/
@[reducible]
noncomputable def pic0FiniteStageOverlapLeftAlgebra
    (U V : Pic0FiniteStageChartIndex C) :
    Algebra (Pic0FiniteStageChartRing C U) (Pic0FiniteStageOverlapRing C U V) :=
  (pic0FiniteStageRestrictionLeft C U V).toRingHom.toAlgebra

/-- The triple-intersection ring as an algebra over the left chart. -/
@[reducible]
noncomputable def pic0FiniteStageTripleLeftAlgebra
    (U V W : Pic0FiniteStageChartIndex C) :
    Algebra (Pic0FiniteStageChartRing C U) (Pic0FiniteStageTripleRing C U V W) :=
  ((pic0FiniteStageOverlapToTripleLeft C U V W).comp
    (pic0FiniteStageRestrictionLeft C U V)).toRingHom.toAlgebra

attribute [local instance] pic0FiniteStageOverlapLeftAlgebra
  pic0FiniteStageTripleLeftAlgebra

/-- The tensor pushout of the two pair-overlap rings over their left chart is the literal
triple-intersection ring. -/
noncomputable def pic0FiniteStageTripleTensorEquiv
    (U V W : Pic0FiniteStageChartIndex C) :
    Pic0FiniteStageOverlapRing C U V ⊗[Pic0FiniteStageChartRing C U]
        Pic0FiniteStageOverlapRing C U W
      ≃ₐ[Pic0FiniteStageChartRing C U] Pic0FiniteStageTripleRing C U V W := by
  let e := ((CommRingCat.isPushout_tensorProduct (Pic0FiniteStageChartRing C U)
    (Pic0FiniteStageOverlapRing C U V)
    (Pic0FiniteStageOverlapRing C U W)).isoIsPushout _ _
      (isPushout_pic0FiniteStageTripleRing C U V W)).commRingCatIsoToRingEquiv
  refine AlgEquiv.ofRingEquiv (f := e) fun c => ?_
  exact congr($((CommRingCat.isPushout_tensorProduct (Pic0FiniteStageChartRing C U)
    (Pic0FiniteStageOverlapRing C U V)
    (Pic0FiniteStageOverlapRing C U W)).inl_isoIsPushout_hom _ _
      (isPushout_pic0FiniteStageTripleRing C U V W)).hom
        ((pic0FiniteStageRestrictionLeft C U V) c))

@[simp]
theorem pic0FiniteStageTripleTensorEquiv_tmul_one
    (U V W : Pic0FiniteStageChartIndex C)
    (x : Pic0FiniteStageOverlapRing C U V) :
    pic0FiniteStageTripleTensorEquiv C U V W (x ⊗ₜ 1) =
      pic0FiniteStageOverlapToTripleLeft C U V W x := by
  exact congr($((CommRingCat.isPushout_tensorProduct (Pic0FiniteStageChartRing C U)
    (Pic0FiniteStageOverlapRing C U V)
    (Pic0FiniteStageOverlapRing C U W)).inl_isoIsPushout_hom _ _
      (isPushout_pic0FiniteStageTripleRing C U V W)).hom x)

@[simp]
theorem pic0FiniteStageTripleTensorEquiv_one_tmul
    (U V W : Pic0FiniteStageChartIndex C)
    (x : Pic0FiniteStageOverlapRing C U W) :
    pic0FiniteStageTripleTensorEquiv C U V W (1 ⊗ₜ x) =
      pic0FiniteStageOverlapToTripleRight C U V W x := by
  exact congr($((CommRingCat.isPushout_tensorProduct (Pic0FiniteStageChartRing C U)
    (Pic0FiniteStageOverlapRing C U V)
    (Pic0FiniteStageOverlapRing C U W)).inr_isoIsPushout_hom _ _
      (isPushout_pic0FiniteStageTripleRing C U V W)).hom x)

/-! ## Tensor pushouts of descended restriction maps -/

/-- The algebra structure selected by an algebra map.  Naming it keeps the two finite-stage
restriction legs definitionally stable inside their tensor pushout. -/
@[reducible]
noncomputable def pic0FiniteStageAlgebraOfMap
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) : Algebra A B :=
  f.toRingHom.toAlgebra

/-- The ground-ring algebra, source algebra, and target algebra attached to an algebra map
form a scalar tower. -/
@[reducible]
noncomputable def pic0FiniteStageTowerOfMap
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    letI : Algebra A B := pic0FiniteStageAlgebraOfMap f
    IsScalarTower R A B := by
  letI : Algebra A B := pic0FiniteStageAlgebraOfMap f
  exact IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)

/-- The tensor-pushout ring attached to two algebra maps with common source. -/
noncomputable def Pic0FiniteStageTensorPushoutRing
    {R A B₁ B₂ : Type u} [CommRing R] [CommRing A]
    [CommRing B₁] [CommRing B₂] [Algebra R A] [Algebra R B₁] [Algebra R B₂]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂) : Type u := by
  letI := pic0FiniteStageAlgebraOfMap f₁
  letI := pic0FiniteStageAlgebraOfMap f₂
  exact B₁ ⊗[A] B₂

noncomputable instance
    {R A B₁ B₂ : Type u} [CommRing R] [CommRing A]
    [CommRing B₁] [CommRing B₂] [Algebra R A] [Algebra R B₁] [Algebra R B₂]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂) :
    CommRing (Pic0FiniteStageTensorPushoutRing f₁ f₂) := by
  dsimp only [Pic0FiniteStageTensorPushoutRing]
  infer_instance

noncomputable instance
    {R A B₁ B₂ : Type u} [CommRing R] [CommRing A]
    [CommRing B₁] [CommRing B₂] [Algebra R A] [Algebra R B₁] [Algebra R B₂]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂) :
    Algebra R (Pic0FiniteStageTensorPushoutRing f₁ f₂) := by
  dsimp only [Pic0FiniteStageTensorPushoutRing]
  letI := pic0FiniteStageAlgebraOfMap f₁
  letI := pic0FiniteStageAlgebraOfMap f₂
  letI := pic0FiniteStageTowerOfMap f₁
  exact Algebra.TensorProduct.leftAlgebra

/-- A tensor pushout of two finite-type algebras is finite type over the common ground
ring. -/
theorem finiteType_pic0FiniteStageTensorPushoutRing
    {R A B₁ B₂ : Type u} [CommRing R] [CommRing A]
    [CommRing B₁] [CommRing B₂] [Algebra R A] [Algebra R B₁] [Algebra R B₂]
    [Algebra.FiniteType R B₁] [Algebra.FiniteType R B₂]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂) :
    Algebra.FiniteType R (Pic0FiniteStageTensorPushoutRing f₁ f₂) := by
  dsimp only [Pic0FiniteStageTensorPushoutRing]
  letI := pic0FiniteStageAlgebraOfMap f₁
  letI := pic0FiniteStageAlgebraOfMap f₂
  letI := pic0FiniteStageTowerOfMap f₁
  letI := pic0FiniteStageTowerOfMap f₂
  exact AlgebraicJacobian.finiteType_tensorProduct_over

/-- Scalar extension commutes with the tensor pushout attached to two algebra maps. -/
noncomputable def pic0FiniteStageTensorPushoutBaseChange
    {R K A B₁ B₂ : Type u} [CommRing R] [CommRing K]
    [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra R K] [Algebra R A] [Algebra R B₁] [Algebra R B₂]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂) :
    letI : Algebra A B₁ := pic0FiniteStageAlgebraOfMap f₁
    letI : Algebra A B₂ := pic0FiniteStageAlgebraOfMap f₂
    letI : IsScalarTower R A B₁ := pic0FiniteStageTowerOfMap f₁
    letI : IsScalarTower R A B₂ := pic0FiniteStageTowerOfMap f₂
    let g₁ := AlgebraicJacobian.scalarExtensionMap
      (M := R) (K := K) (A := A) (B := B₁)
    let g₂ := AlgebraicJacobian.scalarExtensionMap
      (M := R) (K := K) (A := A) (B := B₂)
    letI : Algebra (K ⊗[R] A) (K ⊗[R] B₁) := g₁.toRingHom.toAlgebra
    letI : Algebra (K ⊗[R] A) (K ⊗[R] B₂) := g₂.toRingHom.toAlgebra
    (K ⊗[R] (B₁ ⊗[A] B₂)) ≃ₐ[K]
      ((K ⊗[R] B₁) ⊗[K ⊗[R] A] (K ⊗[R] B₂)) := by
  letI : Algebra A B₁ := pic0FiniteStageAlgebraOfMap f₁
  letI : Algebra A B₂ := pic0FiniteStageAlgebraOfMap f₂
  letI : IsScalarTower R A B₁ := pic0FiniteStageTowerOfMap f₁
  letI : IsScalarTower R A B₂ := pic0FiniteStageTowerOfMap f₂
  -- Freeze the scalar-extension algebra witnesses once.  The old entry point
  -- reconstructs these `Algebra` instances in its dependent result type;
  -- the pinned facade keeps the carrier stable for downstream face maps.
  exact AlgebraicJacobian.tensorProductPushoutBaseChangeEquivPinned
    (M := R) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)

/-- The descended model of the coordinate ring of a chart. -/
abbrev Pic0FiniteStageChartModelRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → ℕ)
    (relation : ∀ j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (U : Pic0FiniteStageChartIndex C) : Type u :=
  Pic0FiniteStageModelRing C L n m relation M (Sum.inl U)

/-- The descended model of the coordinate ring of an ordered pair-overlap. -/
abbrev Pic0FiniteStageOverlapModelRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → ℕ)
    (relation : ∀ j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (U V : Pic0FiniteStageChartIndex C) : Type u :=
  Pic0FiniteStageModelRing C L n m relation M (Sum.inr (U, V))

/-- The descended left restriction leg selected from the simultaneous map family. -/
noncomputable abbrev pic0FiniteStageRestrictionLeftModel
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → ℕ)
    (relation : ∀ j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (mapM : ∀ q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (U V : Pic0FiniteStageChartIndex C) :
    Pic0FiniteStageChartModelRing C L n m relation M U →ₐ[M.1]
      Pic0FiniteStageOverlapModelRing C L n m relation M U V :=
  mapM (Sum.inl (Sum.inl (U, V)))

/-- The descended triple-overlap ring: the tensor pushout of the two descended overlap
rings over their common left-chart model. -/
noncomputable abbrev Pic0FiniteStageTripleModelRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → ℕ)
    (relation : ∀ j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (mapM : ∀ q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (U V W : Pic0FiniteStageChartIndex C) : Type u :=
  Pic0FiniteStageTensorPushoutRing
    (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U V)
    (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U W)

set_option maxHeartbeats 1600000 in
-- The dependent finite-presentation models elaborate through the tensor-pushout theorem.
/-- Every descended triple-overlap model is finite type over its finite-stage field. -/
theorem finiteType_pic0FiniteStageTripleModelRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → ℕ)
    (relation : ∀ j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (mapM : ∀ q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (U V W : Pic0FiniteStageChartIndex C) :
    Algebra.FiniteType M.1
      (Pic0FiniteStageTripleModelRing C L n m relation M mapM U V W) := by
  apply finiteType_pic0FiniteStageTensorPushoutRing

set_option maxHeartbeats 1600000 in
-- The dependent finite-presentation models must elaborate through both tensor factors.
/-- Scalar extension from the common finite subextension to the separably closed field
commutes with the descended triple-overlap tensor pushout. -/
noncomputable def pic0FiniteStageTripleModelBaseChange
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → ℕ)
    (relation : ∀ j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (mapM : ∀ q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (U V W : Pic0FiniteStageChartIndex C) :=
  pic0FiniteStageTensorPushoutBaseChange (K := k)
    (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U V)
    (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U W)

end

end AlgebraicGeometry
