/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Rigidification
import AlgebraicJacobian.Picard.UnitsGlobalPullback
import AlgebraicJacobian.Picard.RefinementInjectivity

/-!
# The σ-normalized comparison cochain ((C2) effectivity, brick E1: the packaging)

The heart of the (C2) effectivity campaign (`informal/c2-effectivity-assembly.md`,
decision D4): from the on-the-nose rigidified descent equation
`u₁^* L = u₂^* L` on the curve `Xq` over the double base `Spec (B ⊗[A] B)` — handed over
by the landed `Over.IsRigidified.cechPicMap_doubleInl_eq_doubleInr` — manufacture a
cochain-level comparison `θ` realizing it, normalized along the section of the projection
attached to a curve point `σ : overSpec k A ⟶ C`.  This file provides the packaging
(`AlgebraicGeometry.NormalizedCechComparison`), the section-square calculus it rests on,
and the abstract one-sided pullback lemmas its construction and consumers run on:

* `AlgebraicGeometry.Over.sectionOfPoint_left_comp_whiskerLeft` and its concrete faces
  (`sectionSq_comp_inl`, …, `sectionCb_comp_face₂₃`, `sectionOfPoint_left_comp_snd`): the
  section of the projection is natural in the base algebra, so the sections over
  `B`, `B ⊗[A] B` and `B ⊗[A] (B ⊗[A] B)` intertwine the coprojection and coface maps on
  the curve products with those on the affine bases.
* `AlgebraicGeometry.Scheme.Hom.unitsAppLE_trivializing_rel` /
  `unitsAppLE_trivializing_ratio_compat`: pullback of a one-sided trivializing relation
  `∂ρ = r^♯ E` along a morphism, and the Čech compatibility of the ratio cochain
  `φt^♯ c ⋅ (φ₂^♯ ρ / φ₁^♯ ρ)` — the one-sided companions of the (C1) coboundary calculus
  of `AlgebraicJacobian.Picard.CoherentWitness`.
* `AlgebraicGeometry.Over.normalizationCover`: the canonical pointed cover of
  `Spec (B ⊗[A] B)` on which the σ-normalization is stated.
* `AlgebraicGeometry.NormalizedCechComparison`: the packaging structure; see its
  docstring for the precise (N1)/(N2) statements (the Stage-0 design record of
  `informal/spec-c2-e1.md`).

The existence theorem is `Over.exists_normalizedCechComparison`
(`AlgebraicJacobian.Picard.NormalizedComparisonExists`); the triple-product coherence
(N3) — a *theorem* about the packaged datum, not a field — is
`NormalizedCechComparison.coherent` (`AlgebraicJacobian.Picard.ComparisonCoherence`).

## Design note (the D4 amendment, recorded)

The worksheet's D4(c) asked for a comparison whose "σ-restriction is `1`".  At the
cochain level that is not stateable: the σ-restriction of a comparison cochain is a
`0`-cochain on `Spec (B ⊗[A] B)` whose *coboundary* is the comparison of the two
coprojection pullbacks of the section-pullback `s_B^♯ γ` of the representing cocycle, and
rigidification (`hrig`) makes `s_B^♯ γ` trivial only as a *class*, not as a cocycle.  The
normalization is therefore ρ-relative: the datum carries a trivializing `0`-cochain `ρ`
of `s_B^♯ γ` (the cochain shadow of `hrig`, no refinement needed since
`Ȟ¹(𝒰) ↪ CechPic`), and (N2) states that the σ-restriction of `θ` *equals the
ρ-comparison* `q₁^♯ ρ / q₂^♯ ρ`.  Global normalization works as designed — no
classwise-per-clopen-piece amendment is needed: σ-restriction of a cochain is honest
pointwise `unitsAppLE`-pullback along the section, defined on any (possibly disconnected,
never integral) scheme, and every gluing/separation step below is the `𝒪ˣ`-sheaf axiom,
which is clopen-blind.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]
variable (C : Over (Spec (.of k)))

/-! ## The coprojections as restrictions of `A`-algebra maps

`tensorInl`/`tensorInr` are `k`-algebra maps by definition; identifying them with the
`k`-restrictions of the `A`-algebra coprojections lets the section squares below be
proved once, for an arbitrary `A`-algebra map. -/

/-- `tensorInl` is the `k`-restriction of the `A`-algebra coprojection `includeLeft`. -/
lemma tensorInl_eq_restrictScalars :
    tensorInl (A := A) (B := B)
      = (Algebra.TensorProduct.includeLeft :
          B →ₐ[A] B ⊗[A] B).restrictScalars k :=
  AlgHom.ext fun _ => rfl

/-- `tensorInr` is the `k`-restriction of the `A`-algebra coprojection `includeRight`. -/
lemma tensorInr_eq_restrictScalars :
    tensorInr (A := A) (B := B)
      = (Algebra.TensorProduct.includeRight :
          B →ₐ[A] B ⊗[A] B).restrictScalars k :=
  rfl

namespace Over

/-! ## The section squares -/

/-- **Point-level base-change compatibility**: for an `A`-algebra map `j : R →ₐ[A] R'`
(with compatible `k`-structures), restricting the canonical curve point over `R` attached
to `σ` along `Spec j` is the canonical curve point over `R'`.  The public,
arbitrary-target generalization of the cover-carrier case used by the rigidification
layer (`AlgebraicJacobian.Picard.Rigidification`). -/
lemma overSpecMap_comp_point {R R' : Type u} [CommRing R] [Algebra k R] [Algebra A R]
    [IsScalarTower k A R] [CommRing R'] [Algebra k R'] [Algebra A R']
    [IsScalarTower k A R'] (j : R →ₐ[A] R') (σ : overSpec k A ⟶ C) :
    Over.overSpecMap (j.restrictScalars k)
        ≫ (Over.overSpecMap ((Algebra.ofId A R).restrictScalars k) ≫ σ)
      = Over.overSpecMap ((Algebra.ofId A R').restrictScalars k) ≫ σ := by
  have key : (j.restrictScalars k).comp ((Algebra.ofId A R).restrictScalars k)
      = (Algebra.ofId A R').restrictScalars k := by
    refine AlgHom.ext fun a => ?_
    change j (Algebra.ofId A R a) = Algebra.ofId A R' a
    rw [Algebra.ofId_apply, Algebra.ofId_apply]
    exact j.commutes a
  rw [← Category.assoc, ← Over.overSpecMap_comp, key]

/-- **The section square over a base change**: for an `A`-algebra map `j : R →ₐ[A] R'`,
the section of the projection attached to the canonical point over `R'`, composed with
the whiskered base change `C ◁ Spec j`, is `Spec j` followed by the section attached to
the point over `R` — the `.left`-level form the unit-section calculus consumes. -/
lemma sectionOfPoint_left_comp_whiskerLeft {R R' : Type u} [CommRing R] [Algebra k R]
    [Algebra A R] [IsScalarTower k A R] [CommRing R'] [Algebra k R'] [Algebra A R']
    [IsScalarTower k A R'] (j : R →ₐ[A] R') (σ : overSpec k A ⟶ C) :
    (sectionOfPoint (Over.overSpecMap ((Algebra.ofId A R').restrictScalars k) ≫ σ)).left
        ≫ (C ◁ Over.overSpecMap (j.restrictScalars k)).left
      = (Over.overSpecMap (j.restrictScalars k)).left
        ≫ (sectionOfPoint
            (Over.overSpecMap ((Algebra.ofId A R).restrictScalars k) ≫ σ)).left := by
  rw [← Over.comp_left, ← Over.comp_left,
    sectionOfPoint_naturality (Over.overSpecMap (j.restrictScalars k)),
    overSpecMap_comp_point C j σ]

/-- **The section retracts the projection**, `.left`-level form:
`(sectionOfPoint σ').left ≫ (snd C T).left = 𝟙 T.left`. -/
lemma sectionOfPoint_left_comp_snd {T : Over (Spec (.of k))} (σ' : T ⟶ C) :
    (sectionOfPoint σ').left ≫ (snd C T).left = 𝟙 T.left := by
  rw [← Over.comp_left, sectionOfPoint_snd]
  rfl

end Over

-- Spec-side objects and maps
set_option quotPrecheck false in
local notation "SB" => (overSpec k B).left
set_option quotPrecheck false in
local notation "Sq" => (overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "Scb" => (overSpec k (B ⊗[A] (B ⊗[A] B))).left
set_option quotPrecheck false in
local notation "q₁" => (Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "q₂" => (Over.overSpecMap (tensorInr (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "f₁₂" => (Over.overSpecMap (tensorFace₁₂ (k := k) (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "f₁₃" => (Over.overSpecMap (tensorFace₁₃ (k := k) (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "f₂₃" => (Over.overSpecMap (tensorFace₂₃ (k := k) (A := A) (B := B))).left
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
-- the sections of the projections attached to the base changes of `σ`
variable (σ : overSpec k A ⟶ C)
set_option quotPrecheck false in
local notation "sB" => (Over.sectionOfPoint
  (Over.overSpecMap ((Algebra.ofId A B).restrictScalars k) ≫ σ)).left
set_option quotPrecheck false in
local notation "sq" => (Over.sectionOfPoint
  (Over.overSpecMap ((Algebra.ofId A (B ⊗[A] B)).restrictScalars k) ≫ σ)).left
set_option quotPrecheck false in
local notation "scb" => (Over.sectionOfPoint
  (Over.overSpecMap ((Algebra.ofId A (B ⊗[A] (B ⊗[A] B))).restrictScalars k) ≫ σ)).left

namespace Over

/-! ### The concrete section squares -/

/-- The section over `B ⊗[A] B` intertwines the first coprojection on the curve product
with the first coprojection on the base: `s_q ≫ u₁ = q₁ ≫ s_B`. -/
lemma sectionSq_comp_inl : sq ≫ u₁ = q₁ ≫ sB := by
  rw [tensorInl_eq_restrictScalars]
  exact sectionOfPoint_left_comp_whiskerLeft C
    (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) σ

/-- The section over `B ⊗[A] B` intertwines the second coprojection on the curve product
with the second coprojection on the base: `s_q ≫ u₂ = q₂ ≫ s_B`. -/
lemma sectionSq_comp_inr : sq ≫ u₂ = q₂ ≫ sB := by
  rw [tensorInr_eq_restrictScalars]
  exact sectionOfPoint_left_comp_whiskerLeft C
    (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) σ

/-- The section over `B ⊗[A] (B ⊗[A] B)` intertwines the `1,2`-coface on the curve
product with the `1,2`-coface on the base: `s_cb ≫ w₁₂ = f₁₂ ≫ s_q`. -/
lemma sectionCb_comp_face₁₂ : scb ≫ w₁₂ = f₁₂ ≫ sq :=
  sectionOfPoint_left_comp_whiskerLeft C (Module.descentFace₁₂ A B) σ

/-- The section over `B ⊗[A] (B ⊗[A] B)` intertwines the `1,3`-coface on the curve
product with the `1,3`-coface on the base: `s_cb ≫ w₁₃ = f₁₃ ≫ s_q`. -/
lemma sectionCb_comp_face₁₃ : scb ≫ w₁₃ = f₁₃ ≫ sq :=
  sectionOfPoint_left_comp_whiskerLeft C (Module.descentFace₁₃ A B) σ

/-- The section over `B ⊗[A] (B ⊗[A] B)` intertwines the `2,3`-coface on the curve
product with the `2,3`-coface on the base: `s_cb ≫ w₂₃ = f₂₃ ≫ s_q`. -/
lemma sectionCb_comp_face₂₃ : scb ≫ w₂₃ = f₂₃ ≫ sq :=
  sectionOfPoint_left_comp_whiskerLeft C (Module.descentFace₂₃ A B) σ

end Over

/-! ## Pullback of a trivializing relation, and the ratio compatibility -/

namespace Scheme.Hom

/-- **Pullback of a one-sided trivializing relation along a morphism of schemes.**
Suppose a unit `0`-cochain `a` on a pointed cover `𝒫` of `Y` trivializes the pullback
along `r : Y ⟶ Z` of a pair-indexed unit family `E` — the one-sided coboundary relation
`a y ⋅ (r^♯ E)(y,y') = a y'` (hypothesis `hrel`; in applications `E` is the pair
evaluation of a unit Čech cocycle).  Then for any `φ : X ⟶ Y` the pulled-back cochain
`φ^♯ a` trivializes the family pulled back along the composite `φ ≫ r`, on any open `O`
inside the pullback of the relevant overlap.  The one-sided companion of
`Scheme.Hom.unitsAppLE_coboundary_rel`. -/
theorem unitsAppLE_trivializing_rel {X Y Z : Scheme.{u}}
    (φ : X ⟶ Y) (r : Y ⟶ Z) {𝒯 : Y.PointedCover}
    (a : ∀ y : Y, Γ(Y, 𝒯.opens y)ˣ)
    (V : Z → Z → Z.Opens) (E : ∀ z z', Γ(Z, V z z')ˣ)
    (e : ∀ y y' : Y, 𝒯.opens y ⊓ 𝒯.opens y' ≤ r ⁻¹ᵁ V (r.base y) (r.base y'))
    (hrel : ∀ y y' : Y,
      Y.unitsRestrict (inf_le_left : 𝒯.opens y ⊓ 𝒯.opens y' ≤ 𝒯.opens y) (a y)
          * r.unitsAppLE (V (r.base y) (r.base y')) (𝒯.opens y ⊓ 𝒯.opens y') (e y y')
              (E (r.base y) (r.base y'))
        = Y.unitsRestrict inf_le_right (a y'))
    (x x' : X) {O : X.Opens}
    (hO : O ≤ φ ⁻¹ᵁ (𝒯.opens (φ.base x) ⊓ 𝒯.opens (φ.base x'))) :
    φ.unitsAppLE (𝒯.opens (φ.base x)) O (hO.trans (φ.preimage_mono inf_le_left))
        (a (φ.base x))
      * (φ ≫ r).unitsAppLE (V ((φ ≫ r).base x) ((φ ≫ r).base x')) O
          (hO.trans (φ.preimage_mono (e (φ.base x) (φ.base x'))))
          (E ((φ ≫ r).base x) ((φ ≫ r).base x'))
    = φ.unitsAppLE (𝒯.opens (φ.base x')) O (hO.trans (φ.preimage_mono inf_le_right))
        (a (φ.base x')) := by
  have H := congrArg
    (φ.unitsAppLE (𝒯.opens (φ.base x) ⊓ 𝒯.opens (φ.base x')) O hO)
    (hrel (φ.base x) (φ.base x'))
  rw [map_mul, Scheme.Hom.map_unitsAppLE, Scheme.Hom.map_unitsAppLE,
    Scheme.unitsAppLE_unitsAppLE] at H
  exact H

/-- **Compatibility of a ratio cochain from a coboundary relation and a trivializing
relation.**  Suppose a unit `0`-cochain `c` on a pointed cover `𝒞` of `Yc` cobounds the
comparison of a pair-indexed family `E` pulled back along `rc₁, rc₂ : Yc ⟶ Z` (`hrelc`),
and a `0`-cochain `a` on a pointed cover `𝒜` of `Ya` trivializes `E` pulled back along
`s₁ : Ya ⟶ Z` (the one-sided `hrela`).  If the pulled-back comparison composites coincide
pairwise — `φt ≫ rc₁ = φ₁ ≫ s₁` and `φt ≫ rc₂ = φ₂ ≫ s₁` — then the ratio cochain
`φt^♯ c ⋅ (φ₂^♯ a / φ₁^♯ a)` on `X` is Čech-compatible.  Stated over abstract schemes so
its proof term is kernel-checked once, over small types; the σ-defect instantiation on
the concrete curve towers is a single application.  The one-sided companion of
`Scheme.Hom.unitsAppLE_coboundary_ratio_compat`. -/
theorem unitsAppLE_trivializing_ratio_compat {X Yc Ya Z : Scheme.{u}}
    (φt : X ⟶ Yc) (φ₁ φ₂ : X ⟶ Ya)
    (rc₁ rc₂ : Yc ⟶ Z) (s₁ : Ya ⟶ Z)
    {𝒞 : Yc.PointedCover} (c : ∀ y : Yc, Γ(Yc, 𝒞.opens y)ˣ)
    {𝒜 : Ya.PointedCover} (a : ∀ y : Ya, Γ(Ya, 𝒜.opens y)ˣ)
    (V : Z → Z → Z.Opens) (E : ∀ z z', Γ(Z, V z z')ˣ)
    (ec₁ : ∀ y y' : Yc, 𝒞.opens y ⊓ 𝒞.opens y' ≤ rc₁ ⁻¹ᵁ V (rc₁.base y) (rc₁.base y'))
    (ec₂ : ∀ y y' : Yc, 𝒞.opens y ⊓ 𝒞.opens y' ≤ rc₂ ⁻¹ᵁ V (rc₂.base y) (rc₂.base y'))
    (ea : ∀ y y' : Ya, 𝒜.opens y ⊓ 𝒜.opens y' ≤ s₁ ⁻¹ᵁ V (s₁.base y) (s₁.base y'))
    (hrelc : ∀ y y' : Yc,
      Yc.unitsRestrict (inf_le_left : 𝒞.opens y ⊓ 𝒞.opens y' ≤ 𝒞.opens y) (c y)
          * rc₁.unitsAppLE (V (rc₁.base y) (rc₁.base y')) (𝒞.opens y ⊓ 𝒞.opens y')
              (ec₁ y y') (E (rc₁.base y) (rc₁.base y'))
        = rc₂.unitsAppLE (V (rc₂.base y) (rc₂.base y')) (𝒞.opens y ⊓ 𝒞.opens y')
              (ec₂ y y') (E (rc₂.base y) (rc₂.base y'))
          * Yc.unitsRestrict inf_le_right (c y'))
    (hrela : ∀ y y' : Ya,
      Ya.unitsRestrict (inf_le_left : 𝒜.opens y ⊓ 𝒜.opens y' ≤ 𝒜.opens y) (a y)
          * s₁.unitsAppLE (V (s₁.base y) (s₁.base y')) (𝒜.opens y ⊓ 𝒜.opens y')
              (ea y y') (E (s₁.base y) (s₁.base y'))
        = Ya.unitsRestrict inf_le_right (a y'))
    (hcomm₁ : φt ≫ rc₁ = φ₁ ≫ s₁) (hcomm₂ : φt ≫ rc₂ = φ₂ ≫ s₁)
    (x x' : X) {O : X.Opens}
    (hOt : O ≤ φt ⁻¹ᵁ (𝒞.opens (φt.base x) ⊓ 𝒞.opens (φt.base x')))
    (hO₁ : O ≤ φ₁ ⁻¹ᵁ (𝒜.opens (φ₁.base x) ⊓ 𝒜.opens (φ₁.base x')))
    (hO₂ : O ≤ φ₂ ⁻¹ᵁ (𝒜.opens (φ₂.base x) ⊓ 𝒜.opens (φ₂.base x'))) :
    φt.unitsAppLE (𝒞.opens (φt.base x)) O (hOt.trans (φt.preimage_mono inf_le_left))
        (c (φt.base x))
      * (φ₂.unitsAppLE (𝒜.opens (φ₂.base x)) O (hO₂.trans (φ₂.preimage_mono inf_le_left))
          (a (φ₂.base x))
        / φ₁.unitsAppLE (𝒜.opens (φ₁.base x)) O (hO₁.trans (φ₁.preimage_mono inf_le_left))
          (a (φ₁.base x)))
    = φt.unitsAppLE (𝒞.opens (φt.base x')) O (hOt.trans (φt.preimage_mono inf_le_right))
        (c (φt.base x'))
      * (φ₂.unitsAppLE (𝒜.opens (φ₂.base x')) O
          (hO₂.trans (φ₂.preimage_mono inf_le_right)) (a (φ₂.base x'))
        / φ₁.unitsAppLE (𝒜.opens (φ₁.base x')) O
          (hO₁.trans (φ₁.preimage_mono inf_le_right)) (a (φ₁.base x'))) := by
  have rt := Scheme.Hom.unitsAppLE_coboundary_rel φt rc₁ rc₂ (𝒞 := 𝒞) c
    V V E E ec₁ ec₂ hrelc x x' (O := O) hOt
  have r₁ := unitsAppLE_trivializing_rel φ₁ s₁ (𝒯 := 𝒜) a V E ea hrela x x' (O := O) hO₁
  have r₂ := unitsAppLE_trivializing_rel φ₂ s₁ (𝒯 := 𝒜) a V E ea hrela x x' (O := O) hO₂
  rw [Scheme.Hom.unitsAppLE_pair_congr_hom hcomm₁ V E x x' _,
    Scheme.Hom.unitsAppLE_pair_congr_hom hcomm₂ V E x x' _] at rt
  exact coboundary_ratio_congr rt (by rw [one_mul]; exact r₁) (by rw [one_mul]; exact r₂)

end Scheme.Hom

namespace Over

/-! ## The normalization cover and the packaging -/

/-- The canonical pointed cover of `Spec (B ⊗[A] B)` on which the σ-normalization (N2)
of a comparison cochain is stated: the comparison cover `𝒲` of the curve `Xq` pulled
back along the section `s_q`, intersected with the two coprojection pullbacks of the
section-pullback cover `𝒩.pullback s_B` of `Spec B` carrying the trivialization `ρ`.
An opaque `def`: consumers access it through the `normalizationCover_le_*` lemmas. -/
noncomputable def normalizationCover (𝒩 : (XB).PointedCover) (𝒲 : (Xq).PointedCover) :
    (Sq).PointedCover :=
  𝒲.pullback (sq)
    ⊓ ((𝒩.pullback (sB)).pullback (q₁) ⊓ (𝒩.pullback (sB)).pullback (q₂))

lemma normalizationCover_le_section (𝒩 : (XB).PointedCover) (𝒲 : (Xq).PointedCover)
    (y : Sq) :
    (normalizationCover C σ 𝒩 𝒲).opens y ≤ (sq) ⁻¹ᵁ 𝒲.opens ((sq).base y) :=
  inf_le_left

lemma normalizationCover_le_inl (𝒩 : (XB).PointedCover) (𝒲 : (Xq).PointedCover)
    (y : Sq) :
    (normalizationCover C σ 𝒩 𝒲).opens y
      ≤ (q₁) ⁻¹ᵁ (𝒩.pullback (sB)).opens ((q₁).base y) :=
  inf_le_right.trans inf_le_left

lemma normalizationCover_le_inr (𝒩 : (XB).PointedCover) (𝒲 : (Xq).PointedCover)
    (y : Sq) :
    (normalizationCover C σ 𝒩 𝒲).opens y
      ≤ (q₂) ⁻¹ᵁ (𝒩.pullback (sB)).opens ((q₂).base y) :=
  inf_le_right.trans inf_le_right

end Over

variable (k A B) in
/-- **The σ-normalized comparison datum ((C2) effectivity, brick E1 — the Stage-0
record).**  Fix a curve point `σ : overSpec k A ⟶ C` and a unit Čech cocycle `γ` on a
pointed cover `𝒩` of the curve `X_B = (C ⊗ Spec B).left`, representing the rigidified
class `L = CechPic.mk 𝒩 γ.class` of the (C2) setting.  Writing `s_B, s_q` for the
sections of the projections attached to the base changes of `σ` to `B` and `B ⊗[A] B`,
and `u₁, u₂ : X_{B⊗B} ⟶ X_B`, `q₁, q₂ : Spec (B ⊗[A] B) ⟶ Spec B` for the coprojection
maps, this packages:

* (`sectionTriv`, `sectionTriv_rel`) a trivializing `0`-cochain `ρ` of the
  section-pullback `s_B^♯ γ`, on the pullback cover `𝒩.pullback s_B` of `Spec B` itself:
  `ρ b ⋅ (s_B^♯ γ)(b,b') = ρ b'` on pairwise overlaps — the cochain shadow of the
  rigidification hypothesis `σ_B^* L = 1` (no refinement is needed:
  `Scheme.CechPic.mk_eq_one_iff`);
* (`cover`, `le_pullbackInl`, `le_pullbackInr`) a pointed cover `𝒲` of the curve
  `X_{B⊗B}` over the double base, refining both coprojection pullbacks of `𝒩` — a plain
  `PointedCover` common refinement (`Scheme.CechPic.mk_eq_mk_iff`), *not* a
  `BasicRefinement`: the basic-refinement calculus requires an affine carrier and
  `X_{B⊗B}` is a curve product; basic refinements re-enter only inside the affine pieces
  of the per-piece descent (brick E2);
* (`θ`) the comparison `0`-cochain on `𝒲`, with
* **(N1)** (`witness`): `θ x ⋅ (u₁^♯ γ)(x,y) = (u₂^♯ γ)(x,y) ⋅ θ y` on the pairwise
  overlaps of `𝒲` — `θ` cobounds the two coprojection pullbacks of `γ`, realizing the
  descent equation `u₁^* L = u₂^* L` at the cochain level; and
* **(N2)** (`normalized`): `(s_q^♯ θ)(y) ⋅ (q₂^♯ ρ)(y) = (q₁^♯ ρ)(y)` for every point
  `y` of `Spec (B ⊗[A] B)`, on the canonical cover `Over.normalizationCover` — the
  σ-restriction of `θ` *is* the ρ-comparison `q₁^♯ ρ / q₂^♯ ρ`.  This is the ρ-relative
  normalization (see the module docstring for why "σ-restriction is `1`" is not the
  correct cochain-level statement); the σ-defect `s_q^♯ θ ⋅ (q₂^♯ ρ / q₁^♯ ρ)` of the
  packaged datum is `1` on the nose.

The triple-product coherence **(N3)** — the three coface pullbacks of `θ` to the curve
over `B ⊗[A] (B ⊗[A] B)` satisfy `(w₂₃^♯ θ) ⋅ (w₁₂^♯ θ) = w₁₃^♯ θ`, in the exact face
convention of `Module.IsDescentCocycle` — is **not** a field: it is a consequence of
(N1) + (N2) for a proper, geometrically irreducible and geometrically reduced curve
(`NormalizedCechComparison.coherent`, `AlgebraicJacobian.Picard.ComparisonCoherence`),
by Kleiman's `lm:aut` argument.  Existence (`Over.exists_normalizedCechComparison`)
requires no geometric hypotheses at all beyond `hrig` and `hdesc`. -/
structure NormalizedCechComparison (𝒩 : (XB).PointedCover)
    (γ : (XB).unitsCocycle 𝒩) : Type u where
  /-- The trivializing `0`-cochain of the section-pullback of `γ`, on the pullback cover
  `𝒩.pullback s_B` of `Spec B`. -/
  sectionTriv : ∀ b : SB, Γ(SB, (𝒩.pullback (sB)).opens b)ˣ
  /-- `sectionTriv` trivializes `s_B^♯ γ`: `ρ b ⋅ (s_B^♯ γ)(b,b') = ρ b'` on pairwise
  overlaps. -/
  sectionTriv_rel : ∀ b b' : SB,
    (SB).unitsRestrict
        (inf_le_left :
          (𝒩.pullback (sB)).opens b ⊓ (𝒩.pullback (sB)).opens b'
            ≤ (𝒩.pullback (sB)).opens b) (sectionTriv b)
      * (sB).unitsAppLE (𝒩.opens ((sB).base b) ⊓ 𝒩.opens ((sB).base b'))
          ((𝒩.pullback (sB)).opens b ⊓ (𝒩.pullback (sB)).opens b')
          ((sB).le_preimage_inf inf_le_left inf_le_right)
          (Scheme.unitsEvInf γ ((sB).base b) ((sB).base b'))
    = (SB).unitsRestrict inf_le_right (sectionTriv b')
  /-- The pointed cover of the curve over the double base carrying the comparison. -/
  cover : (Xq).PointedCover
  /-- The cover refines the pullback of `𝒩` along the first coprojection. -/
  le_pullbackInl : cover ≤ 𝒩.pullback (u₁)
  /-- The cover refines the pullback of `𝒩` along the second coprojection. -/
  le_pullbackInr : cover ≤ 𝒩.pullback (u₂)
  /-- The comparison: a unit `0`-cochain on the cover. -/
  θ : ∀ x : Xq, Γ(Xq, cover.opens x)ˣ
  /-- **(N1)**: `θ` cobounds the two coprojection pullbacks of `γ`:
  `θ x ⋅ (u₁^♯ γ)(x,y) = (u₂^♯ γ)(x,y) ⋅ θ y` on the pairwise overlaps of the cover. -/
  witness : ∀ x y : Xq,
    (Xq).unitsRestrict
        (inf_le_left : cover.opens x ⊓ cover.opens y ≤ cover.opens x) (θ x)
      * (u₁).unitsAppLE (𝒩.opens ((u₁).base x) ⊓ 𝒩.opens ((u₁).base y))
          (cover.opens x ⊓ cover.opens y)
          ((u₁).le_preimage_inf (inf_le_left.trans (le_pullbackInl x))
            (inf_le_right.trans (le_pullbackInl y)))
          (Scheme.unitsEvInf γ ((u₁).base x) ((u₁).base y))
    = (u₂).unitsAppLE (𝒩.opens ((u₂).base x) ⊓ 𝒩.opens ((u₂).base y))
          (cover.opens x ⊓ cover.opens y)
          ((u₂).le_preimage_inf (inf_le_left.trans (le_pullbackInr x))
            (inf_le_right.trans (le_pullbackInr y)))
          (Scheme.unitsEvInf γ ((u₂).base x) ((u₂).base y))
      * (Xq).unitsRestrict inf_le_right (θ y)
  /-- **(N2)**: the σ-restriction of `θ` is the ρ-comparison —
  `(s_q^♯ θ)(y) ⋅ (q₂^♯ ρ)(y) = (q₁^♯ ρ)(y)` on the normalization cover. -/
  normalized : ∀ y : Sq,
    (sq).unitsAppLE (cover.opens ((sq).base y))
        ((Over.normalizationCover C σ 𝒩 cover).opens y)
        (Over.normalizationCover_le_section C σ 𝒩 cover y) (θ ((sq).base y))
      * (q₂).unitsAppLE ((𝒩.pullback (sB)).opens ((q₂).base y))
          ((Over.normalizationCover C σ 𝒩 cover).opens y)
          (Over.normalizationCover_le_inr C σ 𝒩 cover y) (sectionTriv ((q₂).base y))
    = (q₁).unitsAppLE ((𝒩.pullback (sB)).opens ((q₁).base y))
        ((Over.normalizationCover C σ 𝒩 cover).opens y)
        (Over.normalizationCover_le_inl C σ 𝒩 cover y) (sectionTriv ((q₁).base y))

end AlgebraicGeometry
