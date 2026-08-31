/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.EffectivityPieceDescent

/-!
# Restriction canonicity of the per-piece descent classes ((C2) effectivity, brick E3)

The D2 item-3b compatibility: the per-piece descent data are natural in the piece.  For
affine pieces `V' ≤ V` and a piece trivialization `T` on `V`:

* `Over.PieceTrivialization.res` — `T` restricts to a piece trivialization on `V'`;
* `Over.pieceComparisonUnit_res` — the glued comparison unit of the restricted datum is
  the restriction of the glued unit (uniqueness of gluing);
* `Module.comparisonDescentClass_mapAlgebra` — **the base-change naturality of the
  descent extraction** (the statement pinned by E2): for `A`-algebras `S → S'`, the
  descended class of the base-changed comparison unit is the `Pic`-image of the
  descended class, through `IsDescentCocycle.baseChange`/`picClass_baseChange` along
  `S → S'` and `IsDescentCocycle.map`/`picClass_map` along
  `Algebra.TensorProduct.cancelBaseChange`;
* `Over.pieceDescentClass_res` — **the restriction canonicity**
  `M_{V'} = mapAlgebra Γ(V) Γ(V') M_V` for the restricted datum.

This is what the refinement-splice (brick E4) consumes on overlaps `V ⊓ V'` of two
pieces: both descent data restrict from the *same* global normalized comparison, so the
descended classes agree through their common restriction (D2: descents of one fixed
datum glue; abstract classes would not).
-/

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace Module

open Algebra.TensorProduct

variable (A S S' B : Type u) [CommRing A] [CommRing S] [CommRing S'] [CommRing B]
  [Algebra A S] [Algebra A S'] [Algebra A B] [Algebra S S'] [IsScalarTower A S S']

/-! ## The base-change naturality of the descent extraction -/

/-- The descent-cocycle ring identification intertwines the tensor-square base change
along `S → S'` (through `cancelBaseChange` on each factor) with `algebraMap ⊗ id` —
the elementwise core of the base-change naturality of the extraction. -/
private lemma pieceDescentEquiv_cancel_tensorSqBaseChange
    (y : (S ⊗[A] B) ⊗[S] (S ⊗[A] B)) :
    pieceDescentEquiv A S' B
        (Algebra.TensorProduct.map
          (Algebra.TensorProduct.cancelBaseChange A S S' S' B).toAlgHom
          (Algebra.TensorProduct.cancelBaseChange A S S' S' B).toAlgHom
          (Module.tensorSqBaseChange S S' (S ⊗[A] B) y))
      = Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S')
          (AlgHom.id A (B ⊗[A] B)) (pieceDescentEquiv A S B y) := by
  induction y with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m₁ m₂ =>
    induction m₁ with
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul s₁ b₁ =>
      induction m₂ with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | tmul s₂ b₂ =>
        rw [Module.tensorSqBaseChange_tmul, Algebra.TensorProduct.map_tmul]
        simp only [AlgEquiv.coe_algHom]
        rw [Algebra.TensorProduct.cancelBaseChange_tmul,
          Algebra.TensorProduct.cancelBaseChange_tmul,
          pieceDescentEquiv_tmul, pieceDescentEquiv_tmul,
          Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          IsScalarTower.coe_toAlgHom', Algebra.smul_def, Algebra.smul_def,
          mul_one, mul_one, map_mul]

/-- **Base-change naturality of the per-piece descent unit** (the statement pinned by
E2): the comparison descent unit of the base-changed comparison `algebraMap ⊗ id ∘ v`
is the image of the descent unit of `v` under the tensor-square base change along
`S → S'`, identified through `cancelBaseChange` on each factor. -/
theorem comparisonDescentUnit_baseChange (v : (S ⊗[A] (B ⊗[A] B))ˣ) :
    Units.map (Algebra.TensorProduct.map
        (Algebra.TensorProduct.cancelBaseChange A S S' S' B).toAlgHom
        (Algebra.TensorProduct.cancelBaseChange A S S' S' B).toAlgHom
        ).toRingHom.toMonoidHom
      (Units.map (Module.tensorSqBaseChange S S' (S ⊗[A] B)).toRingHom.toMonoidHom
        (Module.comparisonDescentUnit A S B v))
    = Module.comparisonDescentUnit A S' B
        (Units.map (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S')
          (AlgHom.id A (B ⊗[A] B))).toRingHom.toMonoidHom v) := by
  refine Units.ext ?_
  apply (pieceDescentEquiv A S' B).injective
  have h := pieceDescentEquiv_cancel_tensorSqBaseChange A S S' B
    ((pieceDescentEquiv A S B).symm v.val)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.trans (AlgEquiv.apply_symm_apply (pieceDescentEquiv A S' B) _).symm

variable {A S S' B}

/-- **Base-change naturality of the descended per-piece class** (D2 item 3b, the
algebra half): for `A`-algebras `S → S'` and a coherent comparison unit `v` over `S`,
the class descended over `S'` from the base-changed comparison is the
`Pic.mapAlgebra`-image of the class descended over `S`. -/
theorem comparisonDescentClass_mapAlgebra [Module.FaithfullyFlat A B]
    {v : (S ⊗[A] (B ⊗[A] B))ˣ}
    (hlmul : Algebra.TensorProduct.map (AlgHom.id S S) (Algebra.TensorProduct.lmul' A)
      v.val = 1)
    (hcoc : Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentFace₂₃ A B) v.val
          * Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentFace₁₂ A B) v.val
        = Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentFace₁₃ A B) v.val)
    (hlmul' : Algebra.TensorProduct.map (AlgHom.id S' S')
      (Algebra.TensorProduct.lmul' A)
      (Units.map (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S')
        (AlgHom.id A (B ⊗[A] B))).toRingHom.toMonoidHom v).val = 1)
    (hcoc' : Algebra.TensorProduct.map (AlgHom.id S' S') (Module.descentFace₂₃ A B)
          (Units.map (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S')
            (AlgHom.id A (B ⊗[A] B))).toRingHom.toMonoidHom v).val
        * Algebra.TensorProduct.map (AlgHom.id S' S') (Module.descentFace₁₂ A B)
            (Units.map (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S')
              (AlgHom.id A (B ⊗[A] B))).toRingHom.toMonoidHom v).val
      = Algebra.TensorProduct.map (AlgHom.id S' S') (Module.descentFace₁₃ A B)
          (Units.map (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S')
            (AlgHom.id A (B ⊗[A] B))).toRingHom.toMonoidHom v).val) :
    Module.comparisonDescentClass A S' B hlmul' hcoc'
      = CommRing.Pic.mapAlgebra S S'
          (Module.comparisonDescentClass A S B hlmul hcoc) := by
  have hu := Module.isDescentCocycle_comparisonDescentUnit A S B hlmul hcoc
  calc Module.comparisonDescentClass A S' B hlmul' hcoc'
      = ((hu.baseChange (A' := S')).map
          (Algebra.TensorProduct.cancelBaseChange A S S' S' B).toAlgHom).picClass :=
        Module.IsDescentCocycle.picClass_congr _ _
          (comparisonDescentUnit_baseChange A S S' B v).symm
    _ = (hu.baseChange (A' := S')).picClass :=
        Module.IsDescentCocycle.picClass_map _ _
    _ = CommRing.Pic.mapAlgebra S S' hu.picClass :=
        hu.picClass_baseChange

end Module

namespace AlgebraicGeometry

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]
variable (C : Over (Spec (.of k)))

set_option quotPrecheck false in
local notation "XA" => (C ⊗ overSpec k A).left
set_option quotPrecheck false in
local notation "XB" => (C ⊗ overSpec k B).left
set_option quotPrecheck false in
local notation "Xq" => (C ⊗ overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "u₁" => (C ◁ Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "u₂" => (C ◁ Over.overSpecMap (tensorInr (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "cg" => (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left
set_option quotPrecheck false in
local notation "cgq" =>
  (C ◁ Over.overSpecMap ((Algebra.ofId A (B ⊗[A] B)).restrictScalars k)).left

namespace Over

variable (σ : overSpec k A ⟶ C)

/-! ## Restriction of the piece data -/

/-- A piece trivialization restricts along `V' ≤ V`. -/
noncomputable def PieceTrivialization.res {𝒩 : (XB).PointedCover}
    {γ : (XB).unitsCocycle 𝒩} {V V' : (XA).Opens} (hWV : V' ≤ V)
    (T : PieceTrivialization C 𝒩 γ V) : PieceTrivialization C 𝒩 γ V' where
  triv b := (XB).unitsRestrict
    (inf_le_inf_left (𝒩.opens b) ((cg).preimage_mono hWV)) (T.triv b)
  triv_rel b b' := by
    have h := congrArg
      ((XB).unitsRestrict (inf_le_inf_left (𝒩.opens b ⊓ 𝒩.opens b')
        ((cg).preimage_mono hWV) :
          (𝒩.opens b ⊓ 𝒩.opens b') ⊓ (cg) ⁻¹ᵁ V' ≤ (𝒩.opens b ⊓ 𝒩.opens b') ⊓ (cg) ⁻¹ᵁ V))
      (T.triv_rel b b')
    simp only [map_mul, Scheme.unitsRestrict_unitsRestrict] at h ⊢
    exact h

@[simp]
lemma PieceTrivialization.res_triv {𝒩 : (XB).PointedCover}
    {γ : (XB).unitsCocycle 𝒩} {V V' : (XA).Opens} (hWV : V' ≤ V)
    (T : PieceTrivialization C 𝒩 γ V) (b : XB) :
    (T.res C hWV).triv b
      = (XB).unitsRestrict
          (inf_le_inf_left (𝒩.opens b) ((cg).preimage_mono hWV)) (T.triv b) :=
  rfl

/-- **The glued comparison unit is natural in the piece**: the comparison unit of the
restricted datum is the restriction of the comparison unit — uniqueness of gluing. -/
theorem pieceComparisonUnit_res {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ) {V V' : (XA).Opens} (hWV : V' ≤ V)
    (T : PieceTrivialization C 𝒩 γ V) :
    pieceComparisonUnit C σ W (T.res C hWV)
      = (Xq).unitsRestrict ((cgq).preimage_mono hWV) (pieceComparisonUnit C σ W T) := by
  refine (pieceComparisonUnit_unique C σ W (T.res C hWV) _ (fun x => ?_)).symm
  -- restrict the defining property on `V` down to the `V'`-member
  have h := congrArg
    ((Xq).unitsRestrict (inf_le_inf_left (W.cover.opens x)
      ((cgq).preimage_mono hWV) :
        W.cover.opens x ⊓ (cgq) ⁻¹ᵁ V' ≤ W.cover.opens x ⊓ (cgq) ⁻¹ᵁ V))
    (pieceComparisonUnit_spec C σ W T x)
  rw [unitsTrivTwistCochain_def] at h
  simp only [map_mul, map_inv, Scheme.unitsRestrict_unitsRestrict,
    Scheme.Hom.unitsAppLE_map] at h
  rw [unitsTrivTwistCochain_def]
  simp only [PieceTrivialization.res_triv, Scheme.unitsRestrict_unitsRestrict,
    Scheme.Hom.map_unitsAppLE]
  exact h

/-! ## Restriction canonicity of the descent classes -/

-- The base-piece `A`-algebra structure and the cover-piece `Γ(V)`-algebra structure.
attribute [local instance] Over.sectionsAlgebraA Over.pieceCoverAlgebra

/-- The restriction algebra structure on base-piece sections along `V' ≤ V`. -/
@[reducible] noncomputable def sectionsResAlgebra {V V' : (XA).Opens} (hWV : V' ≤ V) :
    Algebra Γ(XA, V) Γ(XA, V') :=
  ((XA).presheaf.map (homOfLE hWV).op).hom.toAlgebra

/-- The `A`-algebra tower of the restriction algebra structure. -/
lemma isScalarTower_sectionsRes {V V' : (XA).Opens} (hWV : V' ≤ V) :
    letI := sectionsResAlgebra C hWV
    IsScalarTower A Γ(XA, V) Γ(XA, V') := by
  letI := sectionsResAlgebra C hWV
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  exact congr($(algebraMap_sectionsA_comp_res C hWV).hom a).symm

/-- The E0 restriction map `resAlgHomA` is the algebra structure map of
`sectionsResAlgebra`. -/
lemma resAlgHomA_eq_toAlgHom {V V' : (XA).Opens} (hWV : V' ≤ V) :
    letI := sectionsResAlgebra C hWV
    haveI := isScalarTower_sectionsRes C hWV
    resAlgHomA C hWV = IsScalarTower.toAlgHom A Γ(XA, V) Γ(XA, V') := by
  letI := sectionsResAlgebra C hWV
  haveI := isScalarTower_sectionsRes C hWV
  exact AlgHom.ext fun s => rfl

/-- **The identified comparison unit is natural in the piece**: through the E0
identifications, restriction of the piece datum is `algebraMap ⊗ id` on the
descent-cocycle ring — the E0 restriction seam applied to the glued unit. -/
theorem pieceComparisonTensorUnit_res {𝒩 : (XB).PointedCover}
    {γ : (XB).unitsCocycle 𝒩} (W : NormalizedCechComparison k A B C σ 𝒩 γ)
    {V V' : (XA).Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hWV : V' ≤ V)
    (T : PieceTrivialization C 𝒩 γ V) :
    pieceComparisonTensorUnit C σ W hV' (T.res C hWV)
      = Units.map (Algebra.TensorProduct.map (resAlgHomA C hWV)
          (AlgHom.id A (B ⊗[A] B))).toRingHom.toMonoidHom
          (pieceComparisonTensorUnit C σ W hV T) := by
  refine Units.ext ?_
  rw [pieceComparisonTensorUnit_val]
  apply (Over.pieceRingEquiv (B := B ⊗[A] B) C hV').injective
  rw [pieceRingEquiv_pieceEquiv]
  have hnat := Over.pieceRingEquiv_naturality (B := B ⊗[A] B) C hV hV' hWV
    (Over.pieceEquiv (A := A) (B := B ⊗[A] B) C hV
      ((pieceComparisonUnit C σ W T) : Γ(Xq, (cgq) ⁻¹ᵁ V)))
  rw [pieceRingEquiv_pieceEquiv] at hnat
  rw [pieceComparisonUnit_res C σ W hWV T]
  exact hnat

/-- **Restriction canonicity of the descended per-piece classes** (D2 item 3b): for
affine pieces `V' ≤ V`, the class descended on `V'` from the restricted piece datum is
the `Pic.mapAlgebra`-image of the class descended on `V` — through the base-change
naturality of the descent extraction.  On an overlap of two pieces, both descent data
restrict from the same global σ-normalized comparison, so the descended classes agree
through their common restriction: this is what the refinement-splice consumes. -/
theorem pieceDescentClass_res [Module.FaithfullyFlat A B]
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ)
    {V V' : (XA).Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hWV : V' ≤ V)
    (T : PieceTrivialization C 𝒩 γ V) :
    pieceDescentClass C σ W hV' (T.res C hWV)
      = (letI := sectionsResAlgebra C hWV
         CommRing.Pic.mapAlgebra Γ(XA, V) Γ(XA, V')
           (pieceDescentClass C σ W hV T)) := by
  letI := sectionsResAlgebra C hWV
  haveI := isScalarTower_sectionsRes C hWV
  -- the restricted tensor unit is the base-changed tensor unit
  have hunit : pieceComparisonTensorUnit C σ W hV' (T.res C hWV)
      = Units.map (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom A Γ(XA, V) Γ(XA, V'))
          (AlgHom.id A (B ⊗[A] B))).toRingHom.toMonoidHom
          (pieceComparisonTensorUnit C σ W hV T) := by
    rw [pieceComparisonTensorUnit_res C σ W hV hV' hWV T,
      resAlgHomA_eq_toAlgHom C hWV]
  -- transport the hypotheses along the unit identification
  have hlmul' := pieceComparisonTensorUnit_lmul C σ W hV' (T.res C hWV)
  have hcoc' := pieceComparisonTensorUnit_cocycle C σ W hV' (T.res C hWV)
  rw [hunit] at hlmul' hcoc'
  -- the `V'`-class is the class of the base-changed unit
  have h1 : pieceDescentClass C σ W hV' (T.res C hWV)
      = Module.comparisonDescentClass A Γ(XA, V') B hlmul' hcoc' :=
    Module.IsDescentCocycle.picClass_congr _ _
      (congrArg (Module.comparisonDescentUnit A Γ(XA, V') B) hunit)
  rw [h1]
  -- conclude by the base-change naturality of the extraction
  exact Module.comparisonDescentClass_mapAlgebra
    (pieceComparisonTensorUnit_lmul C σ W hV T)
    (pieceComparisonTensorUnit_cocycle C σ W hV T) hlmul' hcoc'

end Over

end AlgebraicGeometry
