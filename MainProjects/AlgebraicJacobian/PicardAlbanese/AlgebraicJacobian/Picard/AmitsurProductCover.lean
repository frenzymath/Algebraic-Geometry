/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.NormalizedComparison

/-!
# The Amitsur product cover and the three insertions ((C2) effectivity, brick E1)

The cover-side carrier layer of the (N3) coherence argument
(`AlgebraicJacobian.Picard.ComparisonDefect` / `ComparisonCoherence`), on the curve
`X_{B⊗B⊗B}` over the triple base `Spec (B ⊗[A] (B ⊗[A] B))`:

* `AlgebraicGeometry.Over.amitsurProductCover`: the canonical common refinement of the
  three coface pullbacks of a pointed cover of the curve over `Spec (B ⊗[A] B)` — the
  curve-product mirror of `amitsurCover`; the coherence (N3) is stated on this cover.
* `AlgebraicGeometry.Over.amitsurPairOpen`: its pairwise overlap, as an opaque `def`
  with named `≤`-lemmas.
* `AlgebraicGeometry.Over.amitsurInsertion₁/₂/₃`: the three tensor-slot **insertions**
  `X_{B⊗B⊗B} ⟶ X_B` — the pairwise-coincident values of the six coface–coprojection
  composites `w ≫ u` — as opaque `def`s, with the six composite identifications
  (`face₁₂_comp_inl`, …) as named lemmas.

## Kernel discipline (the ζ2·i lesson, sharpened for the pair-indexed layer)

The composites `w ≫ u` are large morphism terms on the concrete curve towers.  The
(C1) Step-G declarations (`CoherentWitnessExists.stepG_R₂₃`, …) spell them inline and
elaborate cheaply because each declaration is **single-point**; the pair-indexed
statements of the defect gluing double every composite occurrence and did not
elaborate (`whnf`/`isDefEq` timeouts at 1.6M/4M heartbeats in a previous form of this
layer).  Here no pair-indexed statement mentions a composite at all:

* each insertion is one opaque constant, so pair statements repeat a small term;
* each composite is identified with its insertion **once**, in a small lemma
  (three are `rfl`, three are the landed simplicial coincidences
  `Over.whiskerLeft_face₁₂_inl`, …);
* the nested-versus-composite preimage conversion is paid **once, over abstract
  schemes** (`Scheme.Hom.le_preimage_inf_of_comp`), never on the concrete towers: the
  concrete composite bounds `amitsurPairOpen_le_insertion₁/₂/₃` are single
  applications.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace AlgebraicGeometry

/-- **Composite bound transfer along a factorization**, over abstract schemes.  If a
point-indexed family `W` on `Y` refines the `r`-pullback of a family `V` on `Z`, then
any open below the `φ`-preimage of a pairwise `W`-overlap is below the `t`-preimage of
the corresponding pairwise `V`-overlap, for `t = φ ≫ r`.  The nested-versus-composite
preimage conversion — a heavy definitional-equality check on concrete towers — happens
here, over small types, so concrete instantiations are single applications with no
conversion cost. -/
theorem Scheme.Hom.le_preimage_inf_of_comp {X Y Z : Scheme.{u}}
    (φ : X ⟶ Y) (r : Y ⟶ Z) (t : X ⟶ Z) (h : φ ≫ r = t)
    (V : Z → Z.Opens) (W : Y → Y.Opens)
    (hW : ∀ y : Y, W y ≤ r ⁻¹ᵁ V (r.base y))
    (x x' : X) {O : X.Opens}
    (hO : O ≤ φ ⁻¹ᵁ (W (φ.base x) ⊓ W (φ.base x'))) :
    O ≤ t ⁻¹ᵁ (V (t.base x) ⊓ V (t.base x')) := by
  subst h
  exact hO.trans (φ.preimage_mono (r.le_preimage_inf
    (inf_le_left.trans (hW (φ.base x))) (inf_le_right.trans (hW (φ.base x')))))

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]
variable (C : Over (Spec (.of k)))

-- product-side objects and maps
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
namespace Over

/-! ## The Amitsur product cover and its pairwise overlap -/

/-- The canonical common refinement of the three coface pullbacks of a pointed cover of
the curve over `Spec (B ⊗[A] B)`: the curve-product mirror of `amitsurCover`, a pointed
cover of the curve over the triple base.  The coherence (N3) is stated on this cover. -/
noncomputable def amitsurProductCover (𝒲 : (Xq).PointedCover) : (Xcb).PointedCover :=
  (𝒲.pullback (w₂₃) ⊓ 𝒲.pullback (w₁₂)) ⊓ 𝒲.pullback (w₁₃)

lemma amitsurProductCover_le_w₂₃ (𝒲 : (Xq).PointedCover) (z : Xcb) :
    (amitsurProductCover C 𝒲).opens z ≤ (w₂₃) ⁻¹ᵁ 𝒲.opens ((w₂₃).base z) :=
  inf_le_left.trans inf_le_left

lemma amitsurProductCover_le_w₁₂ (𝒲 : (Xq).PointedCover) (z : Xcb) :
    (amitsurProductCover C 𝒲).opens z ≤ (w₁₂) ⁻¹ᵁ 𝒲.opens ((w₁₂).base z) :=
  inf_le_left.trans inf_le_right

lemma amitsurProductCover_le_w₁₃ (𝒲 : (Xq).PointedCover) (z : Xcb) :
    (amitsurProductCover C 𝒲).opens z ≤ (w₁₃) ⁻¹ᵁ 𝒲.opens ((w₁₃).base z) :=
  inf_le_right

/-- The pairwise overlap of the Amitsur product cover, as an opaque `def`.  Consumers
access it through the `amitsurPairOpen_le_*` lemmas. -/
noncomputable def amitsurPairOpen (𝒲 : (Xq).PointedCover) (z z' : Xcb) : (Xcb).Opens :=
  (amitsurProductCover C 𝒲).opens z ⊓ (amitsurProductCover C 𝒲).opens z'

lemma amitsurPairOpen_le_face₂₃ (𝒲 : (Xq).PointedCover) (z z' : Xcb) :
    amitsurPairOpen C 𝒲 z z'
      ≤ (w₂₃) ⁻¹ᵁ (𝒲.opens ((w₂₃).base z) ⊓ 𝒲.opens ((w₂₃).base z')) :=
  (w₂₃).le_preimage_inf
    (inf_le_left.trans (amitsurProductCover_le_w₂₃ C 𝒲 z))
    (inf_le_right.trans (amitsurProductCover_le_w₂₃ C 𝒲 z'))

lemma amitsurPairOpen_le_face₁₂ (𝒲 : (Xq).PointedCover) (z z' : Xcb) :
    amitsurPairOpen C 𝒲 z z'
      ≤ (w₁₂) ⁻¹ᵁ (𝒲.opens ((w₁₂).base z) ⊓ 𝒲.opens ((w₁₂).base z')) :=
  (w₁₂).le_preimage_inf
    (inf_le_left.trans (amitsurProductCover_le_w₁₂ C 𝒲 z))
    (inf_le_right.trans (amitsurProductCover_le_w₁₂ C 𝒲 z'))

lemma amitsurPairOpen_le_face₁₃ (𝒲 : (Xq).PointedCover) (z z' : Xcb) :
    amitsurPairOpen C 𝒲 z z'
      ≤ (w₁₃) ⁻¹ᵁ (𝒲.opens ((w₁₃).base z) ⊓ 𝒲.opens ((w₁₃).base z')) :=
  (w₁₃).le_preimage_inf
    (inf_le_left.trans (amitsurProductCover_le_w₁₃ C 𝒲 z))
    (inf_le_right.trans (amitsurProductCover_le_w₁₃ C 𝒲 z'))

/-! ## The three insertions

The six coface–coprojection composites `w ≫ u : X_{B⊗B⊗B} ⟶ X_B` coincide pairwise
(the landed simplicial coincidences), leaving the three tensor-slot **insertions** —
the whiskered `Spec`s of `x ↦ x ⊗ 1 ⊗ 1`, `x ↦ 1 ⊗ x ⊗ 1`, `x ↦ 1 ⊗ 1 ⊗ x`.  Each is
an opaque `def`: pair-indexed statements downstream mention only these small
constants, never a composite. -/

/-- The first insertion `X_{B⊗B⊗B} ⟶ X_B` — the whiskered `Spec` of the `A`-algebra
insertion `x ↦ x ⊗ (1 ⊗ 1)` into tensor slot `1`, spelled as the composite
`w₁₂ ≫ u₁` (`= w₁₃ ≫ u₁`). -/
noncomputable def amitsurInsertion₁ : Xcb ⟶ XB := w₁₂ ≫ (u₁)

/-- The second insertion `X_{B⊗B⊗B} ⟶ X_B` — the whiskered `Spec` of the `A`-algebra
insertion `x ↦ 1 ⊗ (x ⊗ 1)` into tensor slot `2`, spelled as the composite
`w₂₃ ≫ u₁` (`= w₁₂ ≫ u₂`). -/
noncomputable def amitsurInsertion₂ : Xcb ⟶ XB := w₂₃ ≫ (u₁)

/-- The third insertion `X_{B⊗B⊗B} ⟶ X_B` — the whiskered `Spec` of the `A`-algebra
insertion `x ↦ 1 ⊗ (1 ⊗ x)` into tensor slot `3`, spelled as the composite
`w₂₃ ≫ u₂` (`= w₁₃ ≫ u₂`). -/
noncomputable def amitsurInsertion₃ : Xcb ⟶ XB := w₂₃ ≫ (u₂)

-- the three insertions, as their opaque constants
set_option quotPrecheck false in
local notation "v₁" => amitsurInsertion₁ (k := k) (A := A) (B := B) C
set_option quotPrecheck false in
local notation "v₂" => amitsurInsertion₂ (k := k) (A := A) (B := B) C
set_option quotPrecheck false in
local notation "v₃" => amitsurInsertion₃ (k := k) (A := A) (B := B) C

/-- The composite `w₁₂ ≫ u₁` is the first insertion (definitional spelling). -/
lemma face₁₂_comp_inl : w₁₂ ≫ (u₁) = v₁ := rfl

/-- The composite `w₂₃ ≫ u₁` is the second insertion (definitional spelling). -/
lemma face₂₃_comp_inl : w₂₃ ≫ (u₁) = v₂ := rfl

/-- The composite `w₂₃ ≫ u₂` is the third insertion (definitional spelling). -/
lemma face₂₃_comp_inr : w₂₃ ≫ (u₂) = v₃ := rfl

/-- The composite `w₁₂ ≫ u₂` is the second insertion, by the simplicial coincidence
`Over.whiskerLeft_face₁₂_inr`. -/
lemma face₁₂_comp_inr : w₁₂ ≫ (u₂) = v₂ :=
  (Over.whiskerLeft_face₁₂_inr (k := k) (A := A) (B := B) C).trans
    (face₂₃_comp_inl C)

/-- The composite `w₁₃ ≫ u₁` is the first insertion, by the simplicial coincidence
`Over.whiskerLeft_face₁₂_inl`. -/
lemma face₁₃_comp_inl : w₁₃ ≫ (u₁) = v₁ :=
  (Over.whiskerLeft_face₁₂_inl (k := k) (A := A) (B := B) C).symm.trans
    (face₁₂_comp_inl C)

/-- The composite `w₁₃ ≫ u₂` is the third insertion, by the simplicial coincidence
`Over.whiskerLeft_face₁₃_inr`. -/
lemma face₁₃_comp_inr : w₁₃ ≫ (u₂) = v₃ :=
  (Over.whiskerLeft_face₁₃_inr (k := k) (A := A) (B := B) C).trans
    (face₂₃_comp_inr C)

/-! ## The insertion bounds on the pairwise overlap

Each is a single application of the abstract `Scheme.Hom.le_preimage_inf_of_comp`: no
composite spelling and no preimage conversion on the concrete towers. -/

/-- The pairwise overlap is bounded by the first-insertion preimage of the
`𝒩`-overlap. -/
lemma amitsurPairOpen_le_insertion₁ (𝒩 : (XB).PointedCover) (𝒲 : (Xq).PointedCover)
    (hW₁ : ∀ x, 𝒲.opens x ≤ (u₁) ⁻¹ᵁ 𝒩.opens ((u₁).base x)) (z z' : Xcb) :
    amitsurPairOpen C 𝒲 z z'
      ≤ (v₁) ⁻¹ᵁ (𝒩.opens ((v₁).base z) ⊓ 𝒩.opens ((v₁).base z')) :=
  Scheme.Hom.le_preimage_inf_of_comp (w₁₂) (u₁) (v₁)
    (face₁₂_comp_inl C) 𝒩.opens 𝒲.opens hW₁ z z'
    (amitsurPairOpen_le_face₁₂ C 𝒲 z z')

/-- The pairwise overlap is bounded by the second-insertion preimage of the
`𝒩`-overlap. -/
lemma amitsurPairOpen_le_insertion₂ (𝒩 : (XB).PointedCover) (𝒲 : (Xq).PointedCover)
    (hW₁ : ∀ x, 𝒲.opens x ≤ (u₁) ⁻¹ᵁ 𝒩.opens ((u₁).base x)) (z z' : Xcb) :
    amitsurPairOpen C 𝒲 z z'
      ≤ (v₂) ⁻¹ᵁ (𝒩.opens ((v₂).base z) ⊓ 𝒩.opens ((v₂).base z')) :=
  Scheme.Hom.le_preimage_inf_of_comp (w₂₃) (u₁) (v₂)
    (face₂₃_comp_inl C) 𝒩.opens 𝒲.opens hW₁ z z'
    (amitsurPairOpen_le_face₂₃ C 𝒲 z z')

/-- The pairwise overlap is bounded by the third-insertion preimage of the
`𝒩`-overlap. -/
lemma amitsurPairOpen_le_insertion₃ (𝒩 : (XB).PointedCover) (𝒲 : (Xq).PointedCover)
    (hW₂ : ∀ x, 𝒲.opens x ≤ (u₂) ⁻¹ᵁ 𝒩.opens ((u₂).base x)) (z z' : Xcb) :
    amitsurPairOpen C 𝒲 z z'
      ≤ (v₃) ⁻¹ᵁ (𝒩.opens ((v₃).base z) ⊓ 𝒩.opens ((v₃).base z')) :=
  Scheme.Hom.le_preimage_inf_of_comp (w₂₃) (u₂) (v₃)
    (face₂₃_comp_inr C) 𝒩.opens 𝒲.opens hW₂ z z'
    (amitsurPairOpen_le_face₂₃ C 𝒲 z z')

end Over

end AlgebraicGeometry
