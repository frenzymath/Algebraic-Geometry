/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.AmitsurProductCover

/-!
# The Amitsur defect of a comparison cochain ((C2) effectivity, brick E1: H⁰ step)

The gluing half of the `lm:aut` coherence argument for the σ-normalized comparison: the
**Amitsur defect** `ε = (w₂₃^♯ θ₀) ⋅ (w₁₂^♯ θ₀) / (w₁₃^♯ θ₀)` of a comparison cochain
`θ₀` on the curve over `Spec (B ⊗[A] B)` — the combination of its three coface pullbacks
to the curve over the triple base `Spec (B ⊗[A] (B ⊗[A] B))` — is Čech-compatible
whenever `θ₀` cobounds the two coprojection pullbacks of the representing cocycle `γ`
(the (N1) witness relation): the three coface pullbacks of the witness relation
telescope through the three insertions `Over.amitsurInsertion₁/₂/₃`
(`AlgebraicJacobian.Picard.AmitsurProductCover`).  By the `𝒪ˣ`-sheaf axiom (ζ2·P (P1))
the defect glues to a global unit `ε̄` of `X_{B⊗B⊗B}`
(`Over.exists_glued_productDefect`) — the H⁰ step of Kleiman's `lm:aut`, with **no
geometric hypotheses**.

Following the ζ2·i kernel discipline in its pair-indexed sharpening (see the
`AmitsurProductCover` module docstring): the three pulled-back witness relations are
split into their own (private) declarations, each a single application of the rewired
abstract lemma `Scheme.Hom.unitsAppLE_coboundary_rel_comp`, and their statements are in
**insertion normal form** — every coface–coprojection composite is one of the opaque
insertion constants, so no pair-indexed statement repeats a composite tower and no
rewrite cast over the concrete curve towers ever enters a kernel-checked term.

The σ-restriction of `ε̄` and the coherence theorem (N3) are in
`AlgebraicJacobian.Picard.ComparisonCoherence`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace AlgebraicGeometry

/-- Pullback of a coboundary relation along a morphism, in composite normal form with
the output composites re-expressed along given coincidences `h₁, h₂` — the rewired form
of `Scheme.Hom.unitsAppLE_coboundary_rel`.  All spelling changes (composites, base
points, bound proofs) happen here, over abstract schemes, so the concrete
instantiations on the curve towers are single applications with no rewrite casts. -/
theorem Scheme.Hom.unitsAppLE_coboundary_rel_comp {X Y Z₁ Z₂ : Scheme.{u}}
    (φ : X ⟶ Y) (r₁ : Y ⟶ Z₁) (r₂ : Y ⟶ Z₂) (t₁ : X ⟶ Z₁) (t₂ : X ⟶ Z₂)
    {𝒞 : Y.PointedCover} (c : ∀ y : Y, Γ(Y, 𝒞.opens y)ˣ)
    (V₁ : Z₁ → Z₁ → Z₁.Opens) (V₂ : Z₂ → Z₂ → Z₂.Opens)
    (E₁ : ∀ z z', Γ(Z₁, V₁ z z')ˣ) (E₂ : ∀ z z', Γ(Z₂, V₂ z z')ˣ)
    (e₁ : ∀ y y' : Y, 𝒞.opens y ⊓ 𝒞.opens y' ≤ r₁ ⁻¹ᵁ V₁ (r₁.base y) (r₁.base y'))
    (e₂ : ∀ y y' : Y, 𝒞.opens y ⊓ 𝒞.opens y' ≤ r₂ ⁻¹ᵁ V₂ (r₂.base y) (r₂.base y'))
    (hrel : ∀ y y' : Y,
      Y.unitsRestrict (inf_le_left : 𝒞.opens y ⊓ 𝒞.opens y' ≤ 𝒞.opens y) (c y)
          * r₁.unitsAppLE (V₁ (r₁.base y) (r₁.base y')) (𝒞.opens y ⊓ 𝒞.opens y')
              (e₁ y y') (E₁ (r₁.base y) (r₁.base y'))
        = r₂.unitsAppLE (V₂ (r₂.base y) (r₂.base y')) (𝒞.opens y ⊓ 𝒞.opens y')
              (e₂ y y') (E₂ (r₂.base y) (r₂.base y'))
          * Y.unitsRestrict inf_le_right (c y'))
    (h₁ : φ ≫ r₁ = t₁) (h₂ : φ ≫ r₂ = t₂)
    (x x' : X) {O : X.Opens}
    (hO : O ≤ φ ⁻¹ᵁ (𝒞.opens (φ.base x) ⊓ 𝒞.opens (φ.base x')))
    (e₁O : O ≤ t₁ ⁻¹ᵁ V₁ (t₁.base x) (t₁.base x'))
    (e₂O : O ≤ t₂ ⁻¹ᵁ V₂ (t₂.base x) (t₂.base x')) :
    φ.unitsAppLE (𝒞.opens (φ.base x)) O (hO.trans (φ.preimage_mono inf_le_left))
        (c (φ.base x))
      * t₁.unitsAppLE (V₁ (t₁.base x) (t₁.base x')) O e₁O (E₁ (t₁.base x) (t₁.base x'))
    = t₂.unitsAppLE (V₂ (t₂.base x) (t₂.base x')) O e₂O (E₂ (t₂.base x) (t₂.base x'))
      * φ.unitsAppLE (𝒞.opens (φ.base x')) O (hO.trans (φ.preimage_mono inf_le_right))
          (c (φ.base x')) := by
  subst h₁ h₂
  exact Scheme.Hom.unitsAppLE_coboundary_rel φ r₁ r₂ c V₁ V₂ E₁ E₂ e₁ e₂ hrel x x' hO

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
-- the three insertions, as their opaque constants
set_option quotPrecheck false in
local notation "v₁" => _root_.AlgebraicGeometry.Over.amitsurInsertion₁ (k := k) (A := A) (B := B) C
set_option quotPrecheck false in
local notation "v₂" => _root_.AlgebraicGeometry.Over.amitsurInsertion₂ (k := k) (A := A) (B := B) C
set_option quotPrecheck false in
local notation "v₃" => _root_.AlgebraicGeometry.Over.amitsurInsertion₃ (k := k) (A := A) (B := B) C

namespace Over

/-- The **Amitsur defect** of a comparison cochain `θ₀` on the curve over the double
base: the combination `(w₂₃^♯ θ₀) ⋅ (w₁₂^♯ θ₀) / (w₁₃^♯ θ₀)` of its three coface
pullbacks, a unit `0`-cochain on `amitsurProductCover 𝒲`.  A comparison is coherent
precisely when its defect is `1`. -/
noncomputable def productDefectCochain (𝒲 : (Xq).PointedCover)
    (θ₀ : ∀ x : Xq, Γ(Xq, 𝒲.opens x)ˣ) (z : Xcb) :
    Γ(Xcb, (amitsurProductCover C 𝒲).opens z)ˣ :=
  (w₂₃).unitsAppLE (𝒲.opens ((w₂₃).base z)) ((amitsurProductCover C 𝒲).opens z)
      (amitsurProductCover_le_w₂₃ C 𝒲 z) (θ₀ ((w₂₃).base z))
    * (w₁₂).unitsAppLE (𝒲.opens ((w₁₂).base z)) ((amitsurProductCover C 𝒲).opens z)
      (amitsurProductCover_le_w₁₂ C 𝒲 z) (θ₀ ((w₁₂).base z))
    / (w₁₃).unitsAppLE (𝒲.opens ((w₁₃).base z)) ((amitsurProductCover C 𝒲).opens z)
      (amitsurProductCover_le_w₁₃ C 𝒲 z) (θ₀ ((w₁₃).base z))

/-- The `w₂₃`-coface pullback of the witness relation, in insertion normal form.  Split
from `Over.exists_glued_productDefect` so its proof term is kernel-checked as its own
declaration. -/
private theorem productDefect_rel₂₃
    (𝒩 : (XB).PointedCover) (γ : (XB).unitsCocycle 𝒩) (𝒲 : (Xq).PointedCover)
    (hW₁ : ∀ x, 𝒲.opens x ≤ (u₁) ⁻¹ᵁ 𝒩.opens ((u₁).base x))
    (hW₂ : ∀ x, 𝒲.opens x ≤ (u₂) ⁻¹ᵁ 𝒩.opens ((u₂).base x))
    (θ₀ : ∀ x : Xq, Γ(Xq, 𝒲.opens x)ˣ)
    (hdown : ∀ x y : Xq,
      (Xq).unitsRestrict (inf_le_left : 𝒲.opens x ⊓ 𝒲.opens y ≤ 𝒲.opens x) (θ₀ x)
          * (u₁).unitsAppLE (𝒩.opens ((u₁).base x) ⊓ 𝒩.opens ((u₁).base y))
              (𝒲.opens x ⊓ 𝒲.opens y)
              ((u₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
                (inf_le_right.trans (hW₁ y)))
              (Scheme.unitsEvInf γ ((u₁).base x) ((u₁).base y))
        = (u₂).unitsAppLE (𝒩.opens ((u₂).base x) ⊓ 𝒩.opens ((u₂).base y))
              (𝒲.opens x ⊓ 𝒲.opens y)
              ((u₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
                (inf_le_right.trans (hW₂ y)))
              (Scheme.unitsEvInf γ ((u₂).base x) ((u₂).base y))
          * (Xq).unitsRestrict inf_le_right (θ₀ y))
    (z z' : Xcb) :
    (w₂₃).unitsAppLE (𝒲.opens ((w₂₃).base z)) (amitsurPairOpen C 𝒲 z z')
        ((amitsurPairOpen_le_face₂₃ C 𝒲 z z').trans ((w₂₃).preimage_mono inf_le_left))
        (θ₀ ((w₂₃).base z))
      * (v₂).unitsAppLE (𝒩.opens ((v₂).base z) ⊓ 𝒩.opens ((v₂).base z'))
          (amitsurPairOpen C 𝒲 z z')
          (amitsurPairOpen_le_insertion₂ C 𝒩 𝒲 hW₁ z z')
          (Scheme.unitsEvInf γ ((v₂).base z) ((v₂).base z'))
    = (v₃).unitsAppLE (𝒩.opens ((v₃).base z) ⊓ 𝒩.opens ((v₃).base z'))
          (amitsurPairOpen C 𝒲 z z')
          (amitsurPairOpen_le_insertion₃ C 𝒩 𝒲 hW₂ z z')
          (Scheme.unitsEvInf γ ((v₃).base z) ((v₃).base z'))
      * (w₂₃).unitsAppLE (𝒲.opens ((w₂₃).base z')) (amitsurPairOpen C 𝒲 z z')
          ((amitsurPairOpen_le_face₂₃ C 𝒲 z z').trans
            ((w₂₃).preimage_mono inf_le_right))
          (θ₀ ((w₂₃).base z')) :=
  Scheme.Hom.unitsAppLE_coboundary_rel_comp (w₂₃) (u₁) (u₂) (v₂) (v₃) θ₀
    (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b') (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b')
    (fun b b' ↦ Scheme.unitsEvInf γ b b') (fun b b' ↦ Scheme.unitsEvInf γ b b')
    (fun x y ↦ (u₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
      (inf_le_right.trans (hW₁ y)))
    (fun x y ↦ (u₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
      (inf_le_right.trans (hW₂ y)))
    hdown (face₂₃_comp_inl C) (face₂₃_comp_inr C) z z'
    (amitsurPairOpen_le_face₂₃ C 𝒲 z z')
    (amitsurPairOpen_le_insertion₂ C 𝒩 𝒲 hW₁ z z')
    (amitsurPairOpen_le_insertion₃ C 𝒩 𝒲 hW₂ z z')

/-- The `w₁₂`-coface pullback of the witness relation, in insertion normal form: its
insertions are the first and second, the latter by the simplicial coincidence
`Over.face₁₂_comp_inr`. -/
private theorem productDefect_rel₁₂
    (𝒩 : (XB).PointedCover) (γ : (XB).unitsCocycle 𝒩) (𝒲 : (Xq).PointedCover)
    (hW₁ : ∀ x, 𝒲.opens x ≤ (u₁) ⁻¹ᵁ 𝒩.opens ((u₁).base x))
    (hW₂ : ∀ x, 𝒲.opens x ≤ (u₂) ⁻¹ᵁ 𝒩.opens ((u₂).base x))
    (θ₀ : ∀ x : Xq, Γ(Xq, 𝒲.opens x)ˣ)
    (hdown : ∀ x y : Xq,
      (Xq).unitsRestrict (inf_le_left : 𝒲.opens x ⊓ 𝒲.opens y ≤ 𝒲.opens x) (θ₀ x)
          * (u₁).unitsAppLE (𝒩.opens ((u₁).base x) ⊓ 𝒩.opens ((u₁).base y))
              (𝒲.opens x ⊓ 𝒲.opens y)
              ((u₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
                (inf_le_right.trans (hW₁ y)))
              (Scheme.unitsEvInf γ ((u₁).base x) ((u₁).base y))
        = (u₂).unitsAppLE (𝒩.opens ((u₂).base x) ⊓ 𝒩.opens ((u₂).base y))
              (𝒲.opens x ⊓ 𝒲.opens y)
              ((u₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
                (inf_le_right.trans (hW₂ y)))
              (Scheme.unitsEvInf γ ((u₂).base x) ((u₂).base y))
          * (Xq).unitsRestrict inf_le_right (θ₀ y))
    (z z' : Xcb) :
    (w₁₂).unitsAppLE (𝒲.opens ((w₁₂).base z)) (amitsurPairOpen C 𝒲 z z')
        ((amitsurPairOpen_le_face₁₂ C 𝒲 z z').trans ((w₁₂).preimage_mono inf_le_left))
        (θ₀ ((w₁₂).base z))
      * (v₁).unitsAppLE (𝒩.opens ((v₁).base z) ⊓ 𝒩.opens ((v₁).base z'))
          (amitsurPairOpen C 𝒲 z z')
          (amitsurPairOpen_le_insertion₁ C 𝒩 𝒲 hW₁ z z')
          (Scheme.unitsEvInf γ ((v₁).base z) ((v₁).base z'))
    = (v₂).unitsAppLE (𝒩.opens ((v₂).base z) ⊓ 𝒩.opens ((v₂).base z'))
          (amitsurPairOpen C 𝒲 z z')
          (amitsurPairOpen_le_insertion₂ C 𝒩 𝒲 hW₁ z z')
          (Scheme.unitsEvInf γ ((v₂).base z) ((v₂).base z'))
      * (w₁₂).unitsAppLE (𝒲.opens ((w₁₂).base z')) (amitsurPairOpen C 𝒲 z z')
          ((amitsurPairOpen_le_face₁₂ C 𝒲 z z').trans
            ((w₁₂).preimage_mono inf_le_right))
          (θ₀ ((w₁₂).base z')) :=
  Scheme.Hom.unitsAppLE_coboundary_rel_comp (w₁₂) (u₁) (u₂) (v₁) (v₂) θ₀
    (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b') (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b')
    (fun b b' ↦ Scheme.unitsEvInf γ b b') (fun b b' ↦ Scheme.unitsEvInf γ b b')
    (fun x y ↦ (u₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
      (inf_le_right.trans (hW₁ y)))
    (fun x y ↦ (u₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
      (inf_le_right.trans (hW₂ y)))
    hdown (face₁₂_comp_inl C) (face₁₂_comp_inr C) z z'
    (amitsurPairOpen_le_face₁₂ C 𝒲 z z')
    (amitsurPairOpen_le_insertion₁ C 𝒩 𝒲 hW₁ z z')
    (amitsurPairOpen_le_insertion₂ C 𝒩 𝒲 hW₁ z z')

/-- The `w₁₃`-coface pullback of the witness relation, in insertion normal form: its
insertions are the first and third, both by simplicial coincidences
(`Over.face₁₃_comp_inl`, `Over.face₁₃_comp_inr`). -/
private theorem productDefect_rel₁₃
    (𝒩 : (XB).PointedCover) (γ : (XB).unitsCocycle 𝒩) (𝒲 : (Xq).PointedCover)
    (hW₁ : ∀ x, 𝒲.opens x ≤ (u₁) ⁻¹ᵁ 𝒩.opens ((u₁).base x))
    (hW₂ : ∀ x, 𝒲.opens x ≤ (u₂) ⁻¹ᵁ 𝒩.opens ((u₂).base x))
    (θ₀ : ∀ x : Xq, Γ(Xq, 𝒲.opens x)ˣ)
    (hdown : ∀ x y : Xq,
      (Xq).unitsRestrict (inf_le_left : 𝒲.opens x ⊓ 𝒲.opens y ≤ 𝒲.opens x) (θ₀ x)
          * (u₁).unitsAppLE (𝒩.opens ((u₁).base x) ⊓ 𝒩.opens ((u₁).base y))
              (𝒲.opens x ⊓ 𝒲.opens y)
              ((u₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
                (inf_le_right.trans (hW₁ y)))
              (Scheme.unitsEvInf γ ((u₁).base x) ((u₁).base y))
        = (u₂).unitsAppLE (𝒩.opens ((u₂).base x) ⊓ 𝒩.opens ((u₂).base y))
              (𝒲.opens x ⊓ 𝒲.opens y)
              ((u₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
                (inf_le_right.trans (hW₂ y)))
              (Scheme.unitsEvInf γ ((u₂).base x) ((u₂).base y))
          * (Xq).unitsRestrict inf_le_right (θ₀ y))
    (z z' : Xcb) :
    (w₁₃).unitsAppLE (𝒲.opens ((w₁₃).base z)) (amitsurPairOpen C 𝒲 z z')
        ((amitsurPairOpen_le_face₁₃ C 𝒲 z z').trans ((w₁₃).preimage_mono inf_le_left))
        (θ₀ ((w₁₃).base z))
      * (v₁).unitsAppLE (𝒩.opens ((v₁).base z) ⊓ 𝒩.opens ((v₁).base z'))
          (amitsurPairOpen C 𝒲 z z')
          (amitsurPairOpen_le_insertion₁ C 𝒩 𝒲 hW₁ z z')
          (Scheme.unitsEvInf γ ((v₁).base z) ((v₁).base z'))
    = (v₃).unitsAppLE (𝒩.opens ((v₃).base z) ⊓ 𝒩.opens ((v₃).base z'))
          (amitsurPairOpen C 𝒲 z z')
          (amitsurPairOpen_le_insertion₃ C 𝒩 𝒲 hW₂ z z')
          (Scheme.unitsEvInf γ ((v₃).base z) ((v₃).base z'))
      * (w₁₃).unitsAppLE (𝒲.opens ((w₁₃).base z')) (amitsurPairOpen C 𝒲 z z')
          ((amitsurPairOpen_le_face₁₃ C 𝒲 z z').trans
            ((w₁₃).preimage_mono inf_le_right))
          (θ₀ ((w₁₃).base z')) :=
  Scheme.Hom.unitsAppLE_coboundary_rel_comp (w₁₃) (u₁) (u₂) (v₁) (v₃) θ₀
    (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b') (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b')
    (fun b b' ↦ Scheme.unitsEvInf γ b b') (fun b b' ↦ Scheme.unitsEvInf γ b b')
    (fun x y ↦ (u₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
      (inf_le_right.trans (hW₁ y)))
    (fun x y ↦ (u₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
      (inf_le_right.trans (hW₂ y)))
    hdown (face₁₃_comp_inl C) (face₁₃_comp_inr C) z z'
    (amitsurPairOpen_le_face₁₃ C 𝒲 z z')
    (amitsurPairOpen_le_insertion₁ C 𝒩 𝒲 hW₁ z z')
    (amitsurPairOpen_le_insertion₃ C 𝒩 𝒲 hW₂ z z')

/-- **The Amitsur defect of a witness glues to a global unit of the triple curve
product** (the H⁰ step of `lm:aut`).  If `θ₀` cobounds the two coprojection pullbacks of
`γ` (`hdown`, the (N1) shape), the three coface pullbacks of that relation telescope
through the three insertions, so the defect cochain is Čech-compatible and glues by the
`𝒪ˣ`-sheaf axiom.  No geometric hypotheses. -/
theorem exists_glued_productDefect
    (𝒩 : (XB).PointedCover) (γ : (XB).unitsCocycle 𝒩) (𝒲 : (Xq).PointedCover)
    (hW₁ : ∀ x, 𝒲.opens x ≤ (u₁) ⁻¹ᵁ 𝒩.opens ((u₁).base x))
    (hW₂ : ∀ x, 𝒲.opens x ≤ (u₂) ⁻¹ᵁ 𝒩.opens ((u₂).base x))
    (θ₀ : ∀ x : Xq, Γ(Xq, 𝒲.opens x)ˣ)
    (hdown : ∀ x y : Xq,
      (Xq).unitsRestrict (inf_le_left : 𝒲.opens x ⊓ 𝒲.opens y ≤ 𝒲.opens x) (θ₀ x)
          * (u₁).unitsAppLE (𝒩.opens ((u₁).base x) ⊓ 𝒩.opens ((u₁).base y))
              (𝒲.opens x ⊓ 𝒲.opens y)
              ((u₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
                (inf_le_right.trans (hW₁ y)))
              (Scheme.unitsEvInf γ ((u₁).base x) ((u₁).base y))
        = (u₂).unitsAppLE (𝒩.opens ((u₂).base x) ⊓ 𝒩.opens ((u₂).base y))
              (𝒲.opens x ⊓ 𝒲.opens y)
              ((u₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
                (inf_le_right.trans (hW₂ y)))
              (Scheme.unitsEvInf γ ((u₂).base x) ((u₂).base y))
          * (Xq).unitsRestrict inf_le_right (θ₀ y)) :
    ∃ εbar : Γ(Xcb, ⊤)ˣ, ∀ z : Xcb,
      (Xcb).unitsRestrict le_top εbar = productDefectCochain C 𝒲 θ₀ z := by
  apply Scheme.exists_global_unit_of_compatible (𝒰 := amitsurProductCover C 𝒲)
    (productDefectCochain C 𝒲 θ₀)
  intro z z'
  simp only [productDefectCochain, map_div, map_mul, Scheme.Hom.unitsAppLE_map]
  exact telescope_congr
    (productDefect_rel₂₃ C 𝒩 γ 𝒲 hW₁ hW₂ θ₀ hdown z z')
    (productDefect_rel₁₂ C 𝒩 γ 𝒲 hW₁ hW₂ θ₀ hdown z z')
    (productDefect_rel₁₃ C 𝒩 γ 𝒲 hW₁ hW₂ θ₀ hdown z z')

end Over

end AlgebraicGeometry
