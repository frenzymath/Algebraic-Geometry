/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.EffectivityPieceClass

/-!
# The per-piece descent class ((C2) effectivity, brick E3: the tracked classes)

The diagonal triviality and coherence of the per-piece comparison unit
(`AlgebraicJacobian.Picard.EffectivityPieceClass`), transported through the master
bridge (`AlgebraicJacobian.Picard.EffectivityPieceBridge`), are exactly the
`hlmul`/`hcoc` hypotheses of the landed per-piece descent extraction
(`Module.isDescentCocycle_comparisonDescentUnit`).  This file assembles the tracked
per-piece descent datum of decision D2:

* `Over.pieceComparisonTensorUnit` — the comparison unit in the descent-cocycle ring
  `(Γ(V) ⊗[A] (B ⊗[A] B))ˣ`, with `pieceComparisonTensorUnit_lmul` and
  `pieceComparisonTensorUnit_cocycle`;
* `Over.pieceDescentClass` — **the descended per-piece class**
  `M_V ∈ CommRing.Pic Γ(V)` (`Module.comparisonDescentClass` of the transported unit);
* `Over.mapAlgebra_pieceDescentClass_eq_one` — its pullback to the cover-piece ring
  `Γ(V) ⊗[A] B ≅ Γ(cg⁻¹ V)` is trivial (D2 item 3a, provable half); and
* `Over.cechPicMap_pieceι_eq_one` — the class `L = CechPic.mk 𝒩 γ.class` restricted to
  the open subscheme `cg⁻¹ V` is trivial, cobounded by the piece trivialization (D2
  item 3a, residual half; the subscheme cobounding is proved once over abstract
  schemes, `Scheme.Hom.pullbackUnitsCocycle_isCohomologous_one`): **the recovery
  identity** `cg^* M_V = [L|_{cg⁻¹V}]` holds with both sides trivial, by construction.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace AlgebraicGeometry

/-- **A trivializing cochain on a full-preimage open cobounds the pulled cocycle**, over
abstract schemes: if `f ⁻¹ᵁ DZ = ⊤` and `t` trivializes the pair values of `γ` on the
`DZ`-trimmed opens, the `f`-pullbacks of `t` cobound `f^♯ γ` against `1` — the pulled
cocycle is cohomologous to `1`.  Applied to the open immersion of a trivializing piece,
this is the piece-restriction triviality of the descending class. -/
theorem Scheme.Hom.pullbackUnitsCocycle_isCohomologous_one {X Y : Scheme.{u}}
    (f : X ⟶ Y) (𝒩 : Y.PointedCover) (γ : Y.unitsCocycle 𝒩)
    (DZ : Y.Opens) (hD : f ⁻¹ᵁ DZ = ⊤)
    (t : ∀ z : Y, Γ(Y, 𝒩.opens z ⊓ DZ)ˣ)
    (htriv : ∀ z z' : Y,
      Y.unitsRestrict (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          (𝒩.opens z ⊓ 𝒩.opens z') ⊓ DZ ≤ 𝒩.opens z ⊓ DZ) (t z)
          * Y.unitsRestrict (inf_le_left :
              (𝒩.opens z ⊓ 𝒩.opens z') ⊓ DZ ≤ 𝒩.opens z ⊓ 𝒩.opens z')
              (Scheme.unitsEvInf γ z z')
        = Y.unitsRestrict (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
            (t z')) :
    (f.pullbackUnitsCocycle γ).IsCohomologous 1 := by
  refine (OneCocycle.isCohomologous_iff_evInf _ _).mpr
    ⟨fun p => f.unitsAppLE (𝒩.opens (f.base p) ⊓ DZ) ((𝒩.pullback f).opens p)
      (f.le_preimage_inf le_rfl (le_top.trans hD.ge)) (t (f.base p)),
     fun p p' => ?_⟩
  -- the trivializing relation, pulled back along `f` onto the pairwise overlap
  have h := congrArg
    (f.unitsAppLE ((𝒩.opens (f.base p) ⊓ 𝒩.opens (f.base p')) ⊓ DZ)
      ((𝒩.pullback f).opens p ⊓ (𝒩.pullback f).opens p')
      (f.le_preimage_inf (f.le_preimage_inf inf_le_left inf_le_right)
        (le_top.trans hD.ge)))
    (htriv (f.base p) (f.base p'))
  rw [map_mul, Scheme.Hom.map_unitsAppLE, Scheme.Hom.map_unitsAppLE,
    Scheme.Hom.map_unitsAppLE] at h
  -- the coboundary relation, in honest unit-section language; `exact` bridges the
  -- definitional gap to the presheaf-of-groups language of the `evInf` criterion
  have h' : X.unitsRestrict (inf_le_left :
        (𝒩.pullback f).opens p ⊓ (𝒩.pullback f).opens p' ≤ (𝒩.pullback f).opens p)
        (f.unitsAppLE (𝒩.opens (f.base p) ⊓ DZ) ((𝒩.pullback f).opens p)
          (f.le_preimage_inf le_rfl (le_top.trans hD.ge)) (t (f.base p)))
      * Scheme.unitsEvInf (f.pullbackUnitsCocycle γ) p p'
    = Scheme.unitsEvInf (1 : X.unitsCocycle (𝒩.pullback f)) p p'
      * X.unitsRestrict inf_le_right
          (f.unitsAppLE (𝒩.opens (f.base p') ⊓ DZ) ((𝒩.pullback f).opens p')
            (f.le_preimage_inf le_rfl (le_top.trans hD.ge)) (t (f.base p'))) := by
    rw [Scheme.Hom.unitsAppLE_map, Scheme.Hom.unitsAppLE_map,
      Scheme.one_unitsEvInf, one_mul, Scheme.Hom.pullbackUnitsCocycle_unitsEvInf]
    exact h
  exact h'

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]
variable (C : Over (Spec (.of k)))

-- product-side objects and maps
set_option quotPrecheck false in
local notation "XA" => (C ⊗ overSpec k A).left
set_option quotPrecheck false in
local notation "XB" => (C ⊗ overSpec k B).left
set_option quotPrecheck false in
local notation "Xq" => (C ⊗ overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "Δx" => (C ◁ Over.overSpecMap
  ((Algebra.TensorProduct.lmul' A (S := B)).restrictScalars k)).left
set_option quotPrecheck false in
local notation "cg" => (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left
set_option quotPrecheck false in
local notation "cgq" =>
  (C ◁ Over.overSpecMap ((Algebra.ofId A (B ⊗[A] B)).restrictScalars k)).left

namespace Over

variable (σ : overSpec k A ⟶ C)

/-! ## The transported descent datum -/

-- The base-piece `A`-algebra structure and the cover-piece `Γ(V)`-algebra structure.
attribute [local instance] Over.sectionsAlgebraA Over.pieceCoverAlgebra

/-- **The per-piece comparison unit in the descent-cocycle ring**
`(Γ(V) ⊗[A] (B ⊗[A] B))ˣ`: the glued unit transported through the E0 identification of
the double piece.  This is the comparison unit the landed per-piece descent extraction
(`Module.isDescentCocycle_comparisonDescentUnit`) consumes. -/
noncomputable def pieceComparisonTensorUnit {𝒩 : (XB).PointedCover}
    {γ : (XB).unitsCocycle 𝒩} (W : NormalizedCechComparison k A B C σ 𝒩 γ)
    {V : (XA).Opens} (hV : IsAffineOpen V) (T : PieceTrivialization C 𝒩 γ V) :
    (Γ(XA, V) ⊗[A] (B ⊗[A] B))ˣ :=
  Units.map (Over.pieceEquiv (A := A) (B := B ⊗[A] B) C hV).toAlgHom.toRingHom.toMonoidHom
    (pieceComparisonUnit C σ W T)

lemma pieceComparisonTensorUnit_val {𝒩 : (XB).PointedCover}
    {γ : (XB).unitsCocycle 𝒩} (W : NormalizedCechComparison k A B C σ 𝒩 γ)
    {V : (XA).Opens} (hV : IsAffineOpen V) (T : PieceTrivialization C 𝒩 γ V) :
    (pieceComparisonTensorUnit C σ W hV T).val
      = Over.pieceEquiv (A := A) (B := B ⊗[A] B) C hV
          ((pieceComparisonUnit C σ W T) : Γ(Xq, (cgq) ⁻¹ᵁ V)) :=
  rfl

/-- **The diagonal normalization of the transported comparison unit** — the `hlmul`
hypothesis of the per-piece descent extraction, from the diagonal triviality of the
glued unit through the master bridge at `j = lmul'`. -/
theorem pieceComparisonTensorUnit_lmul
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ)
    {V : (XA).Opens} (hV : IsAffineOpen V) (T : PieceTrivialization C 𝒩 γ V) :
    Algebra.TensorProduct.map (AlgHom.id Γ(XA, V) Γ(XA, V))
        (Algebra.TensorProduct.lmul' A)
        (pieceComparisonTensorUnit C σ W hV T).val
      = 1 := by
  rw [pieceComparisonTensorUnit_val,
    map_pieceEquiv_eq_pieceEquiv_whiskerLeft C
      (Algebra.TensorProduct.lmul' A (S := B)) hV]
  have h : (Δx).appLE ((cgq) ⁻¹ᵁ V) ((cg) ⁻¹ᵁ V)
      (coverPreimage_le_whiskerLeft C (Algebra.TensorProduct.lmul' A (S := B)) V)
      ((pieceComparisonUnit C σ W T) : Γ(Xq, (cgq) ⁻¹ᵁ V)) = 1 :=
    congrArg Units.val (pieceComparisonUnit_diagonal_eq_one C σ W T)
  rw [h, map_one]

/-- **The Amitsur cocycle identity of the transported comparison unit** — the `hcoc`
hypothesis of the per-piece descent extraction, from the coherence of the glued unit
through the master bridge at the three `descentFace`s. -/
theorem pieceComparisonTensorUnit_cocycle
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ)
    {V : (XA).Opens} (hV : IsAffineOpen V) (T : PieceTrivialization C 𝒩 γ V) :
    Algebra.TensorProduct.map (AlgHom.id Γ(XA, V) Γ(XA, V))
        (Module.descentFace₂₃ A B) (pieceComparisonTensorUnit C σ W hV T).val
      * Algebra.TensorProduct.map (AlgHom.id Γ(XA, V) Γ(XA, V))
          (Module.descentFace₁₂ A B) (pieceComparisonTensorUnit C σ W hV T).val
    = Algebra.TensorProduct.map (AlgHom.id Γ(XA, V) Γ(XA, V))
        (Module.descentFace₁₃ A B) (pieceComparisonTensorUnit C σ W hV T).val := by
  rw [pieceComparisonTensorUnit_val,
    map_pieceEquiv_eq_pieceEquiv_whiskerLeft C (Module.descentFace₂₃ A B) hV,
    map_pieceEquiv_eq_pieceEquiv_whiskerLeft C (Module.descentFace₁₂ A B) hV,
    map_pieceEquiv_eq_pieceEquiv_whiskerLeft C (Module.descentFace₁₃ A B) hV,
    ← map_mul]
  refine congrArg (Over.pieceEquiv (A := A) (B := B ⊗[A] (B ⊗[A] B)) C hV) ?_
  have h := congrArg Units.val (pieceComparisonUnit_coherent C σ W T)
  rw [Units.val_mul] at h
  exact h

/-! ## The descended per-piece class -/

variable [Module.FaithfullyFlat A B]

/-- **The descended per-piece class `M_V`** ((C2) effectivity, brick E3): the Picard
class over the base-piece ring `Γ(V)` descended from the per-piece comparison unit —
`Module.comparisonDescentClass` of the transported unit, whose `hlmul`/`hcoc`
hypotheses are the diagonal triviality and coherence established above.  The tracked
data of decision D2 is the triple (this class, the comparison unit
`pieceComparisonTensorUnit` with its defining gluing property, the trivialization `T`);
the class alone is never enough for the splice. -/
noncomputable def pieceDescentClass
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ)
    {V : (XA).Opens} (hV : IsAffineOpen V) (T : PieceTrivialization C 𝒩 γ V) :
    CommRing.Pic Γ(XA, V) :=
  Module.comparisonDescentClass A Γ(XA, V) B
    (pieceComparisonTensorUnit_lmul C σ W hV T)
    (pieceComparisonTensorUnit_cocycle C σ W hV T)

/-- **The cover-pullback of the descended per-piece class is trivial** (D2 item 3a,
provable half): `M_V` pulls back to `1` in `Pic (Γ(V) ⊗[A] B) ≅ Pic Γ(cg⁻¹ V)`. -/
theorem mapAlgebra_pieceDescentClass_eq_one
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ)
    {V : (XA).Opens} (hV : IsAffineOpen V) (T : PieceTrivialization C 𝒩 γ V) :
    CommRing.Pic.mapAlgebra Γ(XA, V) (Γ(XA, V) ⊗[A] B)
        (pieceDescentClass C σ W hV T)
      = 1 :=
  Module.mapAlgebra_comparisonDescentClass_eq_one A Γ(XA, V) B
    (pieceComparisonTensorUnit_lmul C σ W hV T)
    (pieceComparisonTensorUnit_cocycle C σ W hV T)

/-! ## The recovery identity: the piece restriction of `L` is trivial -/

omit [Module.FaithfullyFlat A B] in
/-- **The piece restriction of the descending class is trivial** (D2 item 3a, residual
half — the recovery identity at construction time): the class `L = CechPic.mk 𝒩 γ.class`
of the (C2) setting pulls back to `1` on the open subscheme `cg⁻¹ V`, cobounded by the
piece trivialization.  Together with `mapAlgebra_pieceDescentClass_eq_one` this is the
recovery `cg^* M_V = [L|_{cg⁻¹V}]`: both sides are trivial, by construction. -/
theorem cechPicMap_pieceι_eq_one {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    {V : (XA).Opens} (T : PieceTrivialization C 𝒩 γ V) :
    Scheme.CechPic.map (Scheme.Opens.ι ((cg) ⁻¹ᵁ V))
        (Scheme.CechPic.mk 𝒩 γ.class)
      = 1 := by
  rw [Scheme.CechPic.map_mk, Scheme.Hom.pullbackUnitsH1_class,
    Scheme.CechPic.mk_eq_one_iff]
  exact (OneCocycle.class_eq_iff _ 1).mpr
    (Scheme.Hom.pullbackUnitsCocycle_isCohomologous_one
      (Scheme.Opens.ι ((cg) ⁻¹ᵁ V)) 𝒩 γ ((cg) ⁻¹ᵁ V)
      (Scheme.Opens.ι_preimage_self ((cg) ⁻¹ᵁ V)) T.triv T.triv_rel)


end Over

end AlgebraicGeometry
