/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.ComparisonDiagonal
import AlgebraicJacobian.Picard.EffectivityComparisonUnit
import AlgebraicJacobian.Picard.EffectivityPieceBridge
import AlgebraicJacobian.Picard.EffectivityDescentDatum

/-!
# Normalization and coherence of the comparison unit ((C2) effectivity, brick E3)

The per-piece comparison unit `v_V ∈ Γ(X_{B⊗B}, cgq⁻¹ V)ˣ`
(`AlgebraicJacobian.Picard.EffectivityComparisonUnit`) inherits the two defining
properties of the σ-normalized comparison it is glued from:

* `Over.pieceComparisonUnit_diagonal_eq_one` — its pullback along the diagonal
  `Δ = (C ◁ Spec lmul').left` is `1`: the trivialization factors cancel along the two
  retractions `Δ ≫ u₁ = 𝟙 = Δ ≫ u₂` and the landed diagonal triviality
  (`Over.normalizedComparison_diagonal_eq_one`) kills the witness factor;
* `Over.pieceComparisonUnit_coherent` — its three coface pullbacks to the triple piece
  `Γ(X_{B⊗B⊗B}, cgcb⁻¹ V)ˣ` satisfy the Amitsur cocycle identity on the nose: the
  trivialization factors telescope through the three insertions and the landed
  coherence (`NormalizedCechComparison.coherent`) supplies the witness identity.

These are the geometric sources of the `hlmul`/`hcoc` hypotheses of the landed
per-piece descent extraction; the transport through the master bridge and the descended
class `M_V` are in `AlgebraicJacobian.Picard.EffectivityPieceDescent`.

## Kernel discipline

The trimmed Amitsur overlap is an opaque `def` with named `≤`-lemmas
(`Over.pieceAmitsurOpen`), and the three coface expansions of the glued unit are their
own (private) declarations in insertion normal form — the E1 lessons applied to the
piece towers.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace AlgebraicGeometry

/-- Telescope core for the coherence of the twisted unit: the witness identity
`T₂₃ ⋅ T₁₂ = T₁₃` and the cancellation of the middle trivialization factor. -/
private lemma trivTwist_amitsur_core {G : Type u} [CommGroup G]
    {T₂₃ T₁₂ T₁₃ ta tb tc : G} (hcoh : T₂₃ * T₁₂ = T₁₃) :
    (T₂₃ * tc * tb⁻¹) * (T₁₂ * tb * ta⁻¹) = T₁₃ * tc * ta⁻¹ := by
  calc (T₂₃ * tc * tb⁻¹) * (T₁₂ * tb * ta⁻¹)
      = T₂₃ * T₁₂ * tc * ta⁻¹ * (tb⁻¹ * tb) := by ac_rfl
    _ = T₂₃ * T₁₂ * tc * ta⁻¹ := by rw [inv_mul_cancel, mul_one]
    _ = T₁₃ * tc * ta⁻¹ := by rw [hcoh]

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
local notation "Xcb" => (C ⊗ overSpec k (B ⊗[A] (B ⊗[A] B))).left
set_option quotPrecheck false in
local notation "u₁" => (C ◁ Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "u₂" => (C ◁ Over.overSpecMap (tensorInr (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "w₁₂" =>
  (C ◁ Over.overSpecMap (tensorFace₁₂ (k := k) (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "w₁₃" =>
  (C ◁ Over.overSpecMap (tensorFace₁₃ (k := k) (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "w₂₃" =>
  (C ◁ Over.overSpecMap (tensorFace₂₃ (k := k) (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "Δx" => (C ◁ Over.overSpecMap
  ((Algebra.TensorProduct.lmul' A (S := B)).restrictScalars k)).left
-- the cover inclusions on the curve products
set_option quotPrecheck false in
local notation "cg" => (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left
set_option quotPrecheck false in
local notation "cgq" =>
  (C ◁ Over.overSpecMap ((Algebra.ofId A (B ⊗[A] B)).restrictScalars k)).left
set_option quotPrecheck false in
local notation "cgcb" =>
  (C ◁ Over.overSpecMap
    ((Algebra.ofId A (B ⊗[A] (B ⊗[A] B))).restrictScalars k)).left
-- the three insertions
set_option quotPrecheck false in
local notation "v₁" =>
  _root_.AlgebraicGeometry.Over.amitsurInsertion₁ (k := k) (A := A) (B := B) C
set_option quotPrecheck false in
local notation "v₂" =>
  _root_.AlgebraicGeometry.Over.amitsurInsertion₂ (k := k) (A := A) (B := B) C
set_option quotPrecheck false in
local notation "v₃" =>
  _root_.AlgebraicGeometry.Over.amitsurInsertion₃ (k := k) (A := A) (B := B) C

namespace Over

variable (σ : overSpec k A ⟶ C)

/-! ## Trimmed refinement bounds -/

/-- The trimmed comparison-cover member is bounded by the `u₁`-preimage of the trimmed
representing member. -/
lemma trimmed_le_inl {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ) (V : (XA).Opens) (x : Xq) :
    W.cover.opens x ⊓ (cgq) ⁻¹ᵁ V
      ≤ (u₁) ⁻¹ᵁ (𝒩.opens ((u₁).base x) ⊓ (cg) ⁻¹ᵁ V) :=
  (u₁).le_preimage_inf (inf_le_left.trans (W.le_pullbackInl x))
    (inf_le_right.trans (cgqPreimage_le_inl C V))

/-- The trimmed comparison-cover member is bounded by the `u₂`-preimage of the trimmed
representing member. -/
lemma trimmed_le_inr {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ) (V : (XA).Opens) (x : Xq) :
    W.cover.opens x ⊓ (cgq) ⁻¹ᵁ V
      ≤ (u₂) ⁻¹ᵁ (𝒩.opens ((u₂).base x) ⊓ (cg) ⁻¹ᵁ V) :=
  (u₂).le_preimage_inf (inf_le_left.trans (W.le_pullbackInr x))
    (inf_le_right.trans (cgqPreimage_le_inr C V))

/-! ## The diagonal triviality of the comparison unit -/

/-- **The diagonal pullback of the per-piece comparison unit is `1`** ((C2) effectivity,
brick E3).  The two trivialization factors of the glued unit cancel along the diagonal
retractions `Δ ≫ u₁ = 𝟙 = Δ ≫ u₂`, and the landed diagonal triviality of the
σ-normalized comparison kills the witness factor.  This is the cochain source of the
`hlmul` hypothesis of the per-piece descent extraction. -/
theorem pieceComparisonUnit_diagonal_eq_one
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ) {V : (XA).Opens}
    (T : PieceTrivialization C 𝒩 γ V) :
    (Δx).unitsAppLE ((cgq) ⁻¹ᵁ V) ((cg) ⁻¹ᵁ V)
        (coverPreimage_le_whiskerLeft C (Algebra.TensorProduct.lmul' A (S := B)) V)
        (pieceComparisonUnit C σ W T)
      = 1 := by
  refine Scheme.unitsRestrict_eq_of_locally_eq
    (W := fun b : XB => (W.cover.pullback (Δx)).opens b ⊓ (cg) ⁻¹ᵁ V)
    (fun _ => inf_le_right)
    (fun d hd => Opens.mem_iSup.mpr ⟨d, ⟨(W.cover.pullback (Δx)).mem_opens d, hd⟩⟩)
    _ 1 (fun b => ?_)
  rw [map_one, Scheme.Hom.unitsAppLE_map]
  -- the bound of the member inside the `Δ`-preimage of the trimmed double piece
  have hOD : (W.cover.pullback (Δx)).opens b ⊓ (cg) ⁻¹ᵁ V ≤ (Δx) ⁻¹ᵁ ((cgq) ⁻¹ᵁ V) :=
    inf_le_right.trans
      (coverPreimage_le_whiskerLeft C (Algebra.TensorProduct.lmul' A (S := B)) V)
  -- the identity-composite bound for the trivialization factors
  have e₀ := Scheme.Hom.le_preimage_of_comp (Δx) (u₂) (𝟙 (XB))
    (whiskerLeft_lmul'_inr C)
    (fun z => 𝒩.opens z ⊓ (cg) ⁻¹ᵁ V)
    (fun x => W.cover.opens x ⊓ (cgq) ⁻¹ᵁ V)
    (trimmed_le_inr C σ W V) b
    ((Δx).le_preimage_inf inf_le_left hOD)
  -- expand the glued unit along the diagonal
  have hexp := Scheme.Hom.unitsAppLE_glued_trivTwist (u₁) (u₂) (Δx)
    (𝟙 (XB)) (𝟙 (XB)) (whiskerLeft_lmul'_inl C) (whiskerLeft_lmul'_inr C)
    W.cover 𝒩 W.θ W.le_pullbackInl W.le_pullbackInr ((cg) ⁻¹ᵁ V) ((cgq) ⁻¹ᵁ V)
    (cgqPreimage_le_inl C V) (cgqPreimage_le_inr C V) T.triv
    (pieceComparisonUnit_spec C σ W T) b
    (inf_le_left : (W.cover.pullback (Δx)).opens b ⊓ (cg) ⁻¹ᵁ V
      ≤ (Δx) ⁻¹ᵁ W.cover.opens ((Δx).base b))
    hOD e₀ e₀
  -- the landed diagonal triviality of the witness, restricted to the member
  have hθ := congrArg
    ((XB).unitsRestrict (inf_le_left :
      (W.cover.pullback (Δx)).opens b ⊓ (cg) ⁻¹ᵁ V ≤ (W.cover.pullback (Δx)).opens b))
    (normalizedComparison_diagonal_eq_one C σ 𝒩 γ W.cover
      W.le_pullbackInl W.le_pullbackInr W.sectionTriv W.θ W.witness W.normalized b)
  rw [map_one, Scheme.Hom.unitsAppLE_map] at hθ
  exact hexp.trans (by rw [mul_inv_cancel_right]; exact hθ)

/-! ## The trimmed Amitsur overlap -/

/-- The trimmed member of the Amitsur product cover: the canonical open of the triple
piece on which the coherence of the comparison unit is checked.  An opaque `def` with
named `≤`-lemmas (the E1 kernel discipline). -/
noncomputable def pieceAmitsurOpen (𝒲 : (Xq).PointedCover) (V : (XA).Opens)
    (z : Xcb) : (Xcb).Opens :=
  (amitsurProductCover C 𝒲).opens z ⊓ (cgcb) ⁻¹ᵁ V

lemma mem_pieceAmitsurOpen (𝒲 : (Xq).PointedCover) (V : (XA).Opens) {z : Xcb}
    (hz : z ∈ (cgcb) ⁻¹ᵁ V) : z ∈ pieceAmitsurOpen C 𝒲 V z :=
  ⟨(amitsurProductCover C 𝒲).mem_opens z, hz⟩

lemma pieceAmitsurOpen_le_amitsur (𝒲 : (Xq).PointedCover) (V : (XA).Opens) (z : Xcb) :
    pieceAmitsurOpen C 𝒲 V z ≤ (amitsurProductCover C 𝒲).opens z :=
  inf_le_left

lemma pieceAmitsurOpen_le_piece (𝒲 : (Xq).PointedCover) (V : (XA).Opens) (z : Xcb) :
    pieceAmitsurOpen C 𝒲 V z ≤ (cgcb) ⁻¹ᵁ V :=
  inf_le_right

lemma pieceAmitsurOpen_le_w₂₃ (𝒲 : (Xq).PointedCover) (V : (XA).Opens) (z : Xcb) :
    pieceAmitsurOpen C 𝒲 V z ≤ (w₂₃) ⁻¹ᵁ 𝒲.opens ((w₂₃).base z) :=
  (pieceAmitsurOpen_le_amitsur C 𝒲 V z).trans (amitsurProductCover_le_w₂₃ C 𝒲 z)

lemma pieceAmitsurOpen_le_w₁₂ (𝒲 : (Xq).PointedCover) (V : (XA).Opens) (z : Xcb) :
    pieceAmitsurOpen C 𝒲 V z ≤ (w₁₂) ⁻¹ᵁ 𝒲.opens ((w₁₂).base z) :=
  (pieceAmitsurOpen_le_amitsur C 𝒲 V z).trans (amitsurProductCover_le_w₁₂ C 𝒲 z)

lemma pieceAmitsurOpen_le_w₁₃ (𝒲 : (Xq).PointedCover) (V : (XA).Opens) (z : Xcb) :
    pieceAmitsurOpen C 𝒲 V z ≤ (w₁₃) ⁻¹ᵁ 𝒲.opens ((w₁₃).base z) :=
  (pieceAmitsurOpen_le_amitsur C 𝒲 V z).trans (amitsurProductCover_le_w₁₃ C 𝒲 z)

lemma pieceAmitsurOpen_le_w₂₃_piece (𝒲 : (Xq).PointedCover) (V : (XA).Opens)
    (z : Xcb) :
    pieceAmitsurOpen C 𝒲 V z ≤ (w₂₃) ⁻¹ᵁ ((cgq) ⁻¹ᵁ V) :=
  (pieceAmitsurOpen_le_piece C 𝒲 V z).trans
    (coverPreimage_le_whiskerLeft C (Module.descentFace₂₃ A B) V)

lemma pieceAmitsurOpen_le_w₁₂_piece (𝒲 : (Xq).PointedCover) (V : (XA).Opens)
    (z : Xcb) :
    pieceAmitsurOpen C 𝒲 V z ≤ (w₁₂) ⁻¹ᵁ ((cgq) ⁻¹ᵁ V) :=
  (pieceAmitsurOpen_le_piece C 𝒲 V z).trans
    (coverPreimage_le_whiskerLeft C (Module.descentFace₁₂ A B) V)

lemma pieceAmitsurOpen_le_w₁₃_piece (𝒲 : (Xq).PointedCover) (V : (XA).Opens)
    (z : Xcb) :
    pieceAmitsurOpen C 𝒲 V z ≤ (w₁₃) ⁻¹ᵁ ((cgq) ⁻¹ᵁ V) :=
  (pieceAmitsurOpen_le_piece C 𝒲 V z).trans
    (coverPreimage_le_whiskerLeft C (Module.descentFace₁₃ A B) V)

/-- The trimmed Amitsur member is bounded by the first-insertion preimage of the
trimmed representing member. -/
lemma pieceAmitsurOpen_le_insertion₁ {𝒩 : (XB).PointedCover}
    {γ : (XB).unitsCocycle 𝒩} (W : NormalizedCechComparison k A B C σ 𝒩 γ)
    (V : (XA).Opens) (z : Xcb) :
    pieceAmitsurOpen C W.cover V z
      ≤ (v₁) ⁻¹ᵁ (𝒩.opens ((v₁).base z) ⊓ (cg) ⁻¹ᵁ V) :=
  Scheme.Hom.le_preimage_of_comp (w₁₂) (u₁) (v₁) (face₁₂_comp_inl C)
    (fun b => 𝒩.opens b ⊓ (cg) ⁻¹ᵁ V)
    (fun x => W.cover.opens x ⊓ (cgq) ⁻¹ᵁ V) (trimmed_le_inl C σ W V) z
    ((w₁₂).le_preimage_inf (pieceAmitsurOpen_le_w₁₂ C W.cover V z)
      (pieceAmitsurOpen_le_w₁₂_piece C W.cover V z))

/-- The trimmed Amitsur member is bounded by the second-insertion preimage of the
trimmed representing member. -/
lemma pieceAmitsurOpen_le_insertion₂ {𝒩 : (XB).PointedCover}
    {γ : (XB).unitsCocycle 𝒩} (W : NormalizedCechComparison k A B C σ 𝒩 γ)
    (V : (XA).Opens) (z : Xcb) :
    pieceAmitsurOpen C W.cover V z
      ≤ (v₂) ⁻¹ᵁ (𝒩.opens ((v₂).base z) ⊓ (cg) ⁻¹ᵁ V) :=
  Scheme.Hom.le_preimage_of_comp (w₂₃) (u₁) (v₂) (face₂₃_comp_inl C)
    (fun b => 𝒩.opens b ⊓ (cg) ⁻¹ᵁ V)
    (fun x => W.cover.opens x ⊓ (cgq) ⁻¹ᵁ V) (trimmed_le_inl C σ W V) z
    ((w₂₃).le_preimage_inf (pieceAmitsurOpen_le_w₂₃ C W.cover V z)
      (pieceAmitsurOpen_le_w₂₃_piece C W.cover V z))

/-- The trimmed Amitsur member is bounded by the third-insertion preimage of the
trimmed representing member. -/
lemma pieceAmitsurOpen_le_insertion₃ {𝒩 : (XB).PointedCover}
    {γ : (XB).unitsCocycle 𝒩} (W : NormalizedCechComparison k A B C σ 𝒩 γ)
    (V : (XA).Opens) (z : Xcb) :
    pieceAmitsurOpen C W.cover V z
      ≤ (v₃) ⁻¹ᵁ (𝒩.opens ((v₃).base z) ⊓ (cg) ⁻¹ᵁ V) :=
  Scheme.Hom.le_preimage_of_comp (w₂₃) (u₂) (v₃) (face₂₃_comp_inr C)
    (fun b => 𝒩.opens b ⊓ (cg) ⁻¹ᵁ V)
    (fun x => W.cover.opens x ⊓ (cgq) ⁻¹ᵁ V) (trimmed_le_inr C σ W V) z
    ((w₂₃).le_preimage_inf (pieceAmitsurOpen_le_w₂₃ C W.cover V z)
      (pieceAmitsurOpen_le_w₂₃_piece C W.cover V z))

/-! ## The three coface expansions of the comparison unit -/

/-- The `w₂₃`-coface expansion of the per-piece comparison unit, in insertion normal
form.  Split into its own declaration (the E1 pair-indexed kernel discipline). -/
private theorem pieceCoherent_exp₂₃
    {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ) {V : (XA).Opens}
    (T : PieceTrivialization C 𝒩 γ V) (z : Xcb) :
    (w₂₃).unitsAppLE ((cgq) ⁻¹ᵁ V) (pieceAmitsurOpen C W.cover V z)
        (pieceAmitsurOpen_le_w₂₃_piece C W.cover V z)
        (pieceComparisonUnit C σ W T)
      = (w₂₃).unitsAppLE (W.cover.opens ((w₂₃).base z)) (pieceAmitsurOpen C W.cover V z)
          (pieceAmitsurOpen_le_w₂₃ C W.cover V z) (W.θ ((w₂₃).base z))
        * (v₃).unitsAppLE (𝒩.opens ((v₃).base z) ⊓ (cg) ⁻¹ᵁ V)
            (pieceAmitsurOpen C W.cover V z)
            (pieceAmitsurOpen_le_insertion₃ C σ W V z) (T.triv ((v₃).base z))
        * ((v₂).unitsAppLE (𝒩.opens ((v₂).base z) ⊓ (cg) ⁻¹ᵁ V)
            (pieceAmitsurOpen C W.cover V z)
            (pieceAmitsurOpen_le_insertion₂ C σ W V z) (T.triv ((v₂).base z)))⁻¹ :=
  Scheme.Hom.unitsAppLE_glued_trivTwist (u₁) (u₂) (w₂₃) (v₂) (v₃)
    (face₂₃_comp_inl C) (face₂₃_comp_inr C)
    W.cover 𝒩 W.θ W.le_pullbackInl W.le_pullbackInr ((cg) ⁻¹ᵁ V) ((cgq) ⁻¹ᵁ V)
    (cgqPreimage_le_inl C V) (cgqPreimage_le_inr C V) T.triv
    (pieceComparisonUnit_spec C σ W T) z
    (pieceAmitsurOpen_le_w₂₃ C W.cover V z)
    (pieceAmitsurOpen_le_w₂₃_piece C W.cover V z)
    (pieceAmitsurOpen_le_insertion₃ C σ W V z)
    (pieceAmitsurOpen_le_insertion₂ C σ W V z)

/-- The `w₁₂`-coface expansion of the per-piece comparison unit, in insertion normal
form. -/
private theorem pieceCoherent_exp₁₂
    {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ) {V : (XA).Opens}
    (T : PieceTrivialization C 𝒩 γ V) (z : Xcb) :
    (w₁₂).unitsAppLE ((cgq) ⁻¹ᵁ V) (pieceAmitsurOpen C W.cover V z)
        (pieceAmitsurOpen_le_w₁₂_piece C W.cover V z)
        (pieceComparisonUnit C σ W T)
      = (w₁₂).unitsAppLE (W.cover.opens ((w₁₂).base z)) (pieceAmitsurOpen C W.cover V z)
          (pieceAmitsurOpen_le_w₁₂ C W.cover V z) (W.θ ((w₁₂).base z))
        * (v₂).unitsAppLE (𝒩.opens ((v₂).base z) ⊓ (cg) ⁻¹ᵁ V)
            (pieceAmitsurOpen C W.cover V z)
            (pieceAmitsurOpen_le_insertion₂ C σ W V z) (T.triv ((v₂).base z))
        * ((v₁).unitsAppLE (𝒩.opens ((v₁).base z) ⊓ (cg) ⁻¹ᵁ V)
            (pieceAmitsurOpen C W.cover V z)
            (pieceAmitsurOpen_le_insertion₁ C σ W V z) (T.triv ((v₁).base z)))⁻¹ :=
  Scheme.Hom.unitsAppLE_glued_trivTwist (u₁) (u₂) (w₁₂) (v₁) (v₂)
    (face₁₂_comp_inl C) (face₁₂_comp_inr C)
    W.cover 𝒩 W.θ W.le_pullbackInl W.le_pullbackInr ((cg) ⁻¹ᵁ V) ((cgq) ⁻¹ᵁ V)
    (cgqPreimage_le_inl C V) (cgqPreimage_le_inr C V) T.triv
    (pieceComparisonUnit_spec C σ W T) z
    (pieceAmitsurOpen_le_w₁₂ C W.cover V z)
    (pieceAmitsurOpen_le_w₁₂_piece C W.cover V z)
    (pieceAmitsurOpen_le_insertion₂ C σ W V z)
    (pieceAmitsurOpen_le_insertion₁ C σ W V z)

/-- The `w₁₃`-coface expansion of the per-piece comparison unit, in insertion normal
form. -/
private theorem pieceCoherent_exp₁₃
    {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ) {V : (XA).Opens}
    (T : PieceTrivialization C 𝒩 γ V) (z : Xcb) :
    (w₁₃).unitsAppLE ((cgq) ⁻¹ᵁ V) (pieceAmitsurOpen C W.cover V z)
        (pieceAmitsurOpen_le_w₁₃_piece C W.cover V z)
        (pieceComparisonUnit C σ W T)
      = (w₁₃).unitsAppLE (W.cover.opens ((w₁₃).base z)) (pieceAmitsurOpen C W.cover V z)
          (pieceAmitsurOpen_le_w₁₃ C W.cover V z) (W.θ ((w₁₃).base z))
        * (v₃).unitsAppLE (𝒩.opens ((v₃).base z) ⊓ (cg) ⁻¹ᵁ V)
            (pieceAmitsurOpen C W.cover V z)
            (pieceAmitsurOpen_le_insertion₃ C σ W V z) (T.triv ((v₃).base z))
        * ((v₁).unitsAppLE (𝒩.opens ((v₁).base z) ⊓ (cg) ⁻¹ᵁ V)
            (pieceAmitsurOpen C W.cover V z)
            (pieceAmitsurOpen_le_insertion₁ C σ W V z) (T.triv ((v₁).base z)))⁻¹ :=
  Scheme.Hom.unitsAppLE_glued_trivTwist (u₁) (u₂) (w₁₃) (v₁) (v₃)
    (face₁₃_comp_inl C) (face₁₃_comp_inr C)
    W.cover 𝒩 W.θ W.le_pullbackInl W.le_pullbackInr ((cg) ⁻¹ᵁ V) ((cgq) ⁻¹ᵁ V)
    (cgqPreimage_le_inl C V) (cgqPreimage_le_inr C V) T.triv
    (pieceComparisonUnit_spec C σ W T) z
    (pieceAmitsurOpen_le_w₁₃ C W.cover V z)
    (pieceAmitsurOpen_le_w₁₃_piece C W.cover V z)
    (pieceAmitsurOpen_le_insertion₃ C σ W V z)
    (pieceAmitsurOpen_le_insertion₁ C σ W V z)

/-! ## The coherence of the comparison unit -/

/-- **The Amitsur coherence of the per-piece comparison unit** ((C2) effectivity, brick
E3): the three coface pullbacks of `v_V` to the triple piece satisfy the cocycle
identity on the nose.  The trivialization factors telescope through the three tensor
insertions, and the landed coherence theorem (N3) supplies the witness identity.  This
is the cochain source of the `hcoc` hypothesis of the per-piece descent extraction. -/
theorem pieceComparisonUnit_coherent
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ) {V : (XA).Opens}
    (T : PieceTrivialization C 𝒩 γ V) :
    (w₂₃).unitsAppLE ((cgq) ⁻¹ᵁ V) ((cgcb) ⁻¹ᵁ V)
        (coverPreimage_le_whiskerLeft C (Module.descentFace₂₃ A B) V)
        (pieceComparisonUnit C σ W T)
      * (w₁₂).unitsAppLE ((cgq) ⁻¹ᵁ V) ((cgcb) ⁻¹ᵁ V)
          (coverPreimage_le_whiskerLeft C (Module.descentFace₁₂ A B) V)
          (pieceComparisonUnit C σ W T)
    = (w₁₃).unitsAppLE ((cgq) ⁻¹ᵁ V) ((cgcb) ⁻¹ᵁ V)
        (coverPreimage_le_whiskerLeft C (Module.descentFace₁₃ A B) V)
        (pieceComparisonUnit C σ W T) := by
  refine Scheme.unitsRestrict_eq_of_locally_eq
    (W := fun z : Xcb => pieceAmitsurOpen C W.cover V z)
    (fun z => pieceAmitsurOpen_le_piece C W.cover V z)
    (fun d hd => Opens.mem_iSup.mpr ⟨d, mem_pieceAmitsurOpen C W.cover V hd⟩)
    _ _ (fun z => ?_)
  rw [map_mul, Scheme.Hom.unitsAppLE_map, Scheme.Hom.unitsAppLE_map,
    Scheme.Hom.unitsAppLE_map]
  -- the landed coherence (N3), restricted to the trimmed member
  have hcohO := congrArg
    ((Xcb).unitsRestrict (pieceAmitsurOpen_le_amitsur C W.cover V z))
    (NormalizedCechComparison.coherent C σ W z)
  rw [map_mul, Scheme.Hom.unitsAppLE_map, Scheme.Hom.unitsAppLE_map,
    Scheme.Hom.unitsAppLE_map] at hcohO
  exact (congrArg₂ (· * ·) (pieceCoherent_exp₂₃ C σ W T z)
      (pieceCoherent_exp₁₂ C σ W T z)).trans
    ((trivTwist_amitsur_core hcohO).trans (pieceCoherent_exp₁₃ C σ W T z).symm)

end Over

end AlgebraicGeometry
