/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.AmitsurCochain

/-!
# The Amitsur-coherent Čech witness: packaging (sub-brick ζ2·i, interface half)

Sub-brick ζ2·i of the (C1) étale-separatedness assembly
(`informal/c1-etale-separatedness-assembly.md`, "global-unit correction" route) produces,
from ζ1's class equality `q₁^* N = q₂^* N` over `Spec (B ⊗[A] B)`, a Čech witness for that
equality which is moreover **Amitsur-coherent** over the triple tensor
`Spec (B ⊗[A] (B ⊗[A] B))`. This file provides the packaging and the pullback calculus the
construction (and its consumer ζ2·ii) runs on:

* `AlgebraicGeometry.CoherentCechWitness`: a pointed cover of `Spec (B ⊗[A] B)` refining
  both coprojection pullbacks of a pointed cover `𝒩` of `Spec B`, together with a unit
  `0`-cochain `θ` whose coboundary is the comparison of the two pullbacks of a unit
  cocycle `γ` on `𝒩` (`witness`), and whose three coface pullbacks to the triple tensor
  satisfy the Amitsur cocycle relation `(f₂₃^♯ θ) ⋅ (f₁₂^♯ θ) = f₁₃^♯ θ` (`coherent`).
* `AlgebraicGeometry.amitsurCover`: the canonical common refinement of the three coface
  pullbacks of a pointed cover of `Spec (B ⊗[A] B)`, on which `coherent` is stated.
* `AlgebraicGeometry.Scheme.Hom.unitsAppLE_coboundary_rel`: the workhorse — pullback of a
  unit-cochain coboundary relation along a morphism of schemes, in the `unitsAppLE`
  normal form where every term is `(composite map).unitsAppLE _ _ _ (original section)`.
* `AlgebraicGeometry.Scheme.Hom.unitsAppLE_section_congr_hom`,
  `Scheme.Hom.unitsAppLE_pair_congr_hom`: congruence in the morphism for such normal
  forms (the opens and the section are point-indexed, so the morphism equality transports
  the whole term).
* The simplicial coincidences of ζ2·P (`tensorFace₁₂_comp_tensorInl` etc.), transported
  to `Spec`-level compositions (`Over.overSpecMap_left_face₁₂_inl`, …) and to their
  curve-product lifts (`Over.whiskerLeft_face₁₂_inl`, …), plus the diagonal coincidence
  `Over.whiskerLeft_inl_ofId` — the six composites collapsing onto the three insertions
  is what makes the Amitsur telescopes in ζ2·i cancel.

The existence theorem for `CoherentCechWitness` (the actual ζ2·i construction) is in
`AlgebraicJacobian.Picard.CoherentWitnessExists`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry

/-! ## Congruence in the morphism for `unitsAppLE` normal forms -/

namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- **Congruence in the morphism, point-indexed sections.** For equal morphisms `g = g'`
and a family of unit sections `s` on point-indexed opens `V` of the target, the pullbacks
`g.unitsAppLE (V (g x)) O _ (s (g x))` and `g'.unitsAppLE (V (g' x)) O _ (s (g' x))`
agree: the morphism equality transports the source point, the open and the section
simultaneously. -/
theorem unitsAppLE_section_congr_hom {g g' : X ⟶ Y} (hg : g = g')
    (V : Y → Y.Opens) (s : ∀ y, Γ(Y, V y)ˣ) (x : X) {O : X.Opens}
    (e : O ≤ g ⁻¹ᵁ V (g.base x)) :
    g.unitsAppLE (V (g.base x)) O e (s (g.base x))
      = g'.unitsAppLE (V (g'.base x)) O (hg ▸ e) (s (g'.base x)) := by
  subst hg; rfl

/-- **Congruence in the morphism, pair-indexed sections** — the variant of
`unitsAppLE_section_congr_hom` for doubly point-indexed families, as used for the pair
evaluations `unitsEvInf γ` of a unit Čech cocycle. -/
theorem unitsAppLE_pair_congr_hom {g g' : X ⟶ Y} (hg : g = g')
    (V : Y → Y → Y.Opens) (s : ∀ y y', Γ(Y, V y y')ˣ) (x x' : X) {O : X.Opens}
    (e : O ≤ g ⁻¹ᵁ V (g.base x) (g.base x')) :
    g.unitsAppLE (V (g.base x) (g.base x')) O e (s (g.base x) (g.base x'))
      = g'.unitsAppLE (V (g'.base x) (g'.base x')) O (hg ▸ e)
          (s (g'.base x) (g'.base x')) := by
  subst hg; rfl

/-! ## Pullback of a coboundary relation -/

/-- **Pullback of a unit-cochain coboundary relation along a morphism of schemes.**
Suppose a unit `0`-cochain `c` on a pointed cover `𝒞` of `Y` cobounds the comparison of
two pair-indexed unit families `E₁, E₂` pulled back along `r₁ : Y ⟶ Z₁`, `r₂ : Y ⟶ Z₂`
(hypothesis `hrel`; in applications `Eᵢ` are the pair evaluations of unit Čech cocycles).
Then for any `φ : X ⟶ Y` the pulled-back cochain `φ^♯ c` cobounds the comparison of the
families pulled back along the composites `φ ≫ rᵢ`, on any open `O` inside the pullback
of the relevant overlap. All terms are in the `unitsAppLE` normal form
`(map).unitsAppLE _ O _ (original section)`, so composites can subsequently be rewritten
by `unitsAppLE_section_congr_hom`/`unitsAppLE_pair_congr_hom`. -/
theorem unitsAppLE_coboundary_rel {X Y Z₁ Z₂ : Scheme.{u}}
    (φ : X ⟶ Y) (r₁ : Y ⟶ Z₁) (r₂ : Y ⟶ Z₂) {𝒞 : Y.PointedCover}
    (c : ∀ y : Y, Γ(Y, 𝒞.opens y)ˣ)
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
    (x x' : X) {O : X.Opens}
    (hO : O ≤ φ ⁻¹ᵁ (𝒞.opens (φ.base x) ⊓ 𝒞.opens (φ.base x'))) :
    φ.unitsAppLE (𝒞.opens (φ.base x)) O (hO.trans (φ.preimage_mono inf_le_left))
        (c (φ.base x))
      * (φ ≫ r₁).unitsAppLE (V₁ ((φ ≫ r₁).base x) ((φ ≫ r₁).base x')) O
          (hO.trans (φ.preimage_mono (e₁ (φ.base x) (φ.base x'))))
          (E₁ ((φ ≫ r₁).base x) ((φ ≫ r₁).base x'))
    = (φ ≫ r₂).unitsAppLE (V₂ ((φ ≫ r₂).base x) ((φ ≫ r₂).base x')) O
          (hO.trans (φ.preimage_mono (e₂ (φ.base x) (φ.base x'))))
          (E₂ ((φ ≫ r₂).base x) ((φ ≫ r₂).base x'))
      * φ.unitsAppLE (𝒞.opens (φ.base x')) O (hO.trans (φ.preimage_mono inf_le_right))
          (c (φ.base x')) := by
  have H := congrArg
    (φ.unitsAppLE (𝒞.opens (φ.base x) ⊓ 𝒞.opens (φ.base x')) O hO)
    (hrel (φ.base x) (φ.base x'))
  rw [map_mul, map_mul, Scheme.Hom.map_unitsAppLE, Scheme.Hom.map_unitsAppLE,
    Scheme.unitsAppLE_unitsAppLE, Scheme.unitsAppLE_unitsAppLE] at H
  exact H

end Scheme.Hom

/-! ## The simplicial coincidences at `Spec` level and on the curve product -/

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

namespace Over

/-- **Simplicial coincidence at `Spec` level, position `1`.** The two `Spec`-side
composites landing on the insertion `x ↦ x ⊗ 1 ⊗ 1` agree:
`Spec (face₁₂) ≫ Spec (inl) = Spec (face₁₃) ≫ Spec (inl)`. -/
lemma overSpecMap_left_face₁₂_inl :
    (Over.overSpecMap (tensorFace₁₂ (k := k) (A := A) (B := B))).left
        ≫ (Over.overSpecMap (tensorInl (A := A) (B := B))).left
      = (Over.overSpecMap (tensorFace₁₃ (k := k) (A := A) (B := B))).left
        ≫ (Over.overSpecMap (tensorInl (A := A) (B := B))).left := by
  rw [← Over.comp_left, ← Over.comp_left, ← Over.overSpecMap_comp, ← Over.overSpecMap_comp,
    tensorFace₁₂_comp_tensorInl]

/-- **Simplicial coincidence at `Spec` level, position `2`**:
`Spec (face₁₂) ≫ Spec (inr) = Spec (face₂₃) ≫ Spec (inl)`. -/
lemma overSpecMap_left_face₁₂_inr :
    (Over.overSpecMap (tensorFace₁₂ (k := k) (A := A) (B := B))).left
        ≫ (Over.overSpecMap (tensorInr (A := A) (B := B))).left
      = (Over.overSpecMap (tensorFace₂₃ (k := k) (A := A) (B := B))).left
        ≫ (Over.overSpecMap (tensorInl (A := A) (B := B))).left := by
  rw [← Over.comp_left, ← Over.comp_left, ← Over.overSpecMap_comp, ← Over.overSpecMap_comp,
    tensorFace₁₂_comp_tensorInr]

/-- **Simplicial coincidence at `Spec` level, position `3`**:
`Spec (face₁₃) ≫ Spec (inr) = Spec (face₂₃) ≫ Spec (inr)`. -/
lemma overSpecMap_left_face₁₃_inr :
    (Over.overSpecMap (tensorFace₁₃ (k := k) (A := A) (B := B))).left
        ≫ (Over.overSpecMap (tensorInr (A := A) (B := B))).left
      = (Over.overSpecMap (tensorFace₂₃ (k := k) (A := A) (B := B))).left
        ≫ (Over.overSpecMap (tensorInr (A := A) (B := B))).left := by
  rw [← Over.comp_left, ← Over.comp_left, ← Over.overSpecMap_comp, ← Over.overSpecMap_comp,
    tensorFace₁₃_comp_tensorInr]

variable (C : Over (Spec (.of k)))

/-- **Simplicial coincidence on the curve product, position `1`** — the `C ◁ –` lift of
`overSpecMap_left_face₁₂_inl`. -/
lemma whiskerLeft_face₁₂_inl :
    (C ◁ Over.overSpecMap (tensorFace₁₂ (k := k) (A := A) (B := B))).left
        ≫ (C ◁ Over.overSpecMap (tensorInl (A := A) (B := B))).left
      = (C ◁ Over.overSpecMap (tensorFace₁₃ (k := k) (A := A) (B := B))).left
        ≫ (C ◁ Over.overSpecMap (tensorInl (A := A) (B := B))).left := by
  rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
    ← MonoidalCategory.whiskerLeft_comp, ← Over.overSpecMap_comp, ← Over.overSpecMap_comp,
    tensorFace₁₂_comp_tensorInl]

/-- **Simplicial coincidence on the curve product, position `2`** — the `C ◁ –` lift of
`overSpecMap_left_face₁₂_inr`. -/
lemma whiskerLeft_face₁₂_inr :
    (C ◁ Over.overSpecMap (tensorFace₁₂ (k := k) (A := A) (B := B))).left
        ≫ (C ◁ Over.overSpecMap (tensorInr (A := A) (B := B))).left
      = (C ◁ Over.overSpecMap (tensorFace₂₃ (k := k) (A := A) (B := B))).left
        ≫ (C ◁ Over.overSpecMap (tensorInl (A := A) (B := B))).left := by
  rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
    ← MonoidalCategory.whiskerLeft_comp, ← Over.overSpecMap_comp, ← Over.overSpecMap_comp,
    tensorFace₁₂_comp_tensorInr]

/-- **Simplicial coincidence on the curve product, position `3`** — the `C ◁ –` lift of
`overSpecMap_left_face₁₃_inr`. -/
lemma whiskerLeft_face₁₃_inr :
    (C ◁ Over.overSpecMap (tensorFace₁₃ (k := k) (A := A) (B := B))).left
        ≫ (C ◁ Over.overSpecMap (tensorInr (A := A) (B := B))).left
      = (C ◁ Over.overSpecMap (tensorFace₂₃ (k := k) (A := A) (B := B))).left
        ≫ (C ◁ Over.overSpecMap (tensorInr (A := A) (B := B))).left := by
  rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
    ← MonoidalCategory.whiskerLeft_comp, ← Over.overSpecMap_comp, ← Over.overSpecMap_comp,
    tensorFace₁₃_comp_tensorInr]

/-- **Diagonal coincidence on the curve product**: composed with the base inclusion
`Spec` of `ofId A B`, the two lifted coprojections agree — the `C ◁ –` lift of
`tensorInl_comp_ofId`. This is what cancels the `L`-terms in the ζ2·i comparison. -/
lemma whiskerLeft_inl_ofId :
    (C ◁ Over.overSpecMap (tensorInl (A := A) (B := B))).left
        ≫ (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left
      = (C ◁ Over.overSpecMap (tensorInr (A := A) (B := B))).left
        ≫ (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left := by
  rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
    ← MonoidalCategory.whiskerLeft_comp, ← Over.overSpecMap_comp, ← Over.overSpecMap_comp,
    tensorInl_comp_ofId]

end Over

/-! ## The packaging -/

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

/-- The canonical common refinement of the three coface pullbacks of a pointed cover of
`Spec (B ⊗[A] B)`: the pointwise intersection of the pullbacks along
`Spec (face₂₃), Spec (face₁₂), Spec (face₁₃)`, a pointed cover of the triple tensor
`Spec (B ⊗[A] (B ⊗[A] B))`. The Amitsur coherence of a `CoherentCechWitness` is stated on
this cover. -/
noncomputable def amitsurCover
    (𝒱 : ((overSpec k (B ⊗[A] B)).left).PointedCover) :
    ((overSpec k (B ⊗[A] (B ⊗[A] B))).left).PointedCover :=
  (𝒱.pullback f₂₃ ⊓ 𝒱.pullback f₁₂) ⊓ 𝒱.pullback f₁₃

variable (k A B) in
/-- **An Amitsur-coherent Čech witness (sub-brick ζ2·i).** Given a unit Čech cocycle `γ`
on a pointed cover `𝒩` of `Spec B`, this packages a pointed cover of
`Spec (B ⊗[A] B)` refining both coprojection pullbacks of `𝒩`, and a unit `0`-cochain
`θ` on it such that

* (`witness`) the coboundary of `θ` is the comparison of the two coprojection pullbacks
  `q₁^♯ γ` and `q₂^♯ γ` of `γ` — so `θ` witnesses, at cocycle level, ζ1's class equality
  `q₁^* N = q₂^* N` for `N = CechPic.mk 𝒩 γ.class`; and
* (`coherent`) the three coface pullbacks of `θ` to `Spec (B ⊗[A] (B ⊗[A] B))` satisfy
  the Amitsur relation `(f₂₃^♯ θ) ⋅ (f₁₂^♯ θ) = f₁₃^♯ θ` on the canonical common
  refinement `amitsurCover`.

The consumer ζ2·ii extracts from `θ` and trivializations of `N` the components
`v i j ∈ (S i ⊗[A] S j)ˣ` of a composite descent cocycle; `coherent` is exactly what
collapses to the descent-cocycle identity for `v`. -/
structure CoherentCechWitness (𝒩 : ((overSpec k B).left).PointedCover)
    (γ : ((overSpec k B).left).unitsCocycle 𝒩) : Type u where
  /-- The pointed cover of `Spec (B ⊗[A] B)` carrying the witness cochain. -/
  cover : ((overSpec k (B ⊗[A] B)).left).PointedCover
  /-- The cover refines the pullback of `𝒩` along the first coprojection. -/
  le_pullbackInl : cover ≤ 𝒩.pullback q₁
  /-- The cover refines the pullback of `𝒩` along the second coprojection. -/
  le_pullbackInr : cover ≤ 𝒩.pullback q₂
  /-- The witness: a unit `0`-cochain on the cover. -/
  θ : ∀ x : (overSpec k (B ⊗[A] B)).left, Γ((overSpec k (B ⊗[A] B)).left, cover.opens x)ˣ
  /-- `θ` cobounds the comparison of the two coprojection pullbacks of `γ`:
  `θ x ⋅ (q₁^♯ γ)(x,y) = (q₂^♯ γ)(x,y) ⋅ θ y` on the pairwise overlaps of the cover. -/
  witness : ∀ x y : (overSpec k (B ⊗[A] B)).left,
    ((overSpec k (B ⊗[A] B)).left).unitsRestrict
        (inf_le_left : cover.opens x ⊓ cover.opens y ≤ cover.opens x) (θ x)
      * (q₁).unitsAppLE (𝒩.opens ((q₁).base x) ⊓ 𝒩.opens ((q₁).base y))
          (cover.opens x ⊓ cover.opens y)
          ((q₁).le_preimage_inf (inf_le_left.trans (le_pullbackInl x))
            (inf_le_right.trans (le_pullbackInl y)))
          (Scheme.unitsEvInf γ ((q₁).base x) ((q₁).base y))
    = (q₂).unitsAppLE (𝒩.opens ((q₂).base x) ⊓ 𝒩.opens ((q₂).base y))
          (cover.opens x ⊓ cover.opens y)
          ((q₂).le_preimage_inf (inf_le_left.trans (le_pullbackInr x))
            (inf_le_right.trans (le_pullbackInr y)))
          (Scheme.unitsEvInf γ ((q₂).base x) ((q₂).base y))
      * ((overSpec k (B ⊗[A] B)).left).unitsRestrict inf_le_right (θ y)
  /-- Amitsur coherence: on the canonical common refinement of the three coface
  pullbacks, `(f₂₃^♯ θ) ⋅ (f₁₂^♯ θ) = f₁₃^♯ θ`. -/
  coherent : ∀ z : (overSpec k (B ⊗[A] (B ⊗[A] B))).left,
    (f₂₃).unitsAppLE (cover.opens ((f₂₃).base z)) ((amitsurCover cover).opens z)
        (inf_le_left.trans inf_le_left) (θ ((f₂₃).base z))
      * (f₁₂).unitsAppLE (cover.opens ((f₁₂).base z)) ((amitsurCover cover).opens z)
          (inf_le_left.trans inf_le_right) (θ ((f₁₂).base z))
    = (f₁₃).unitsAppLE (cover.opens ((f₁₃).base z)) ((amitsurCover cover).opens z)
        inf_le_right (θ ((f₁₃).base z))

/-! ## Commutative-group telescopes and the global-unit correction

The three cancellation patterns of the ζ2·i argument, abstracted over a commutative group
(in applications: unit groups of section rings); the pullback of global units along a
composite of scheme morphisms; the bridge recognizing a coface pullback of a `⊤`-restricted
global unit as a global-unit pullback; and, on top of all of these, the assembly of the
coherent witness itself by dividing a Čech witness cochain by a global unit that trivializes
its glued Amitsur defect. -/

/-- Telescope congruence: if three elements `a₂₃, a₁₂, a₁₃` cobound the "faces"
`E₂/E₃, E₁/E₂, E₁/E₃` against `b₂₃, b₁₂, b₁₃`, the two Amitsur combinations agree. -/
lemma telescope_congr {G : Type u} [CommGroup G]
    {a₂₃ a₁₂ a₁₃ b₂₃ b₁₂ b₁₃ E₁ E₂ E₃ : G}
    (h₂₃ : a₂₃ * E₂ = E₃ * b₂₃) (h₁₂ : a₁₂ * E₁ = E₂ * b₁₂)
    (h₁₃ : a₁₃ * E₁ = E₃ * b₁₃) :
    a₂₃ * a₁₂ / a₁₃ = b₂₃ * b₁₂ / b₁₃ := by
  rw [← div_eq_one, div_div_div_comm, mul_div_mul_comm,
    div_eq_div_iff_mul_eq_mul.mpr h₂₃, div_eq_div_iff_mul_eq_mul.mpr h₁₂,
    div_eq_div_iff_mul_eq_mul.mpr h₁₃, div_mul_div_cancel, div_self']

/-- The exact Amitsur telescope: correction factors `M₃/M₂, M₂/M₁, M₃/M₁` cancel from an
Amitsur combination. -/
lemma telescope_mul_div {G : Type u} [CommGroup G] (T₂₃ T₁₂ T₁₃ M₁ M₂ M₃ : G) :
    T₂₃ * (M₃ / M₂) * (T₁₂ * (M₂ / M₁)) / (T₁₃ * (M₃ / M₁)) = T₂₃ * T₁₂ / T₁₃ := by
  rw [mul_mul_mul_comm, mul_div_mul_comm,
    show M₃ / M₂ * (M₂ / M₁) / (M₃ / M₁) = 1 by rw [div_mul_div_cancel, div_self'],
    mul_one]

/-- Two cochains cobounding the same comparison (up to a common factor `L`) have a
compatible ratio. -/
lemma coboundary_ratio_congr {G : Type u} [CommGroup G]
    {t t' a₁ a₁' a₂ a₂' Q₁ Q₂ L : G}
    (h : t * Q₁ = Q₂ * t') (h₁ : a₁ * Q₁ = L * a₁') (h₂ : a₂ * Q₂ = L * a₂') :
    t * (a₂ / a₁) = t' * (a₂' / a₁') := by
  rw [← div_eq_one, mul_div_mul_comm, div_div_div_comm,
    div_eq_div_iff_mul_eq_mul.mpr h, div_eq_div_iff_mul_eq_mul.mpr h₂,
    div_eq_div_iff_mul_eq_mul.mpr h₁, div_div_div_cancel_left, div_mul_div_cancel,
    div_self']

/-- Dividing an Amitsur relation by an Amitsur relation of correction factors. -/
lemma div_mul_div_eq_of_mul_div {G : Type u} [CommGroup G]
    {t₂₃ t₁₂ t₁₃ c₂₃ c₁₂ c₁₃ : G} (W : t₂₃ * t₁₂ / t₁₃ = c₂₃ * c₁₂ / c₁₃) :
    t₂₃ / c₂₃ * (t₁₂ / c₁₂) = t₁₃ / c₁₃ := by
  rw [div_mul_div_comm, div_eq_div_iff_mul_eq_mul]
  exact (div_eq_div_iff_mul_eq_mul.mp W).trans (mul_comm _ _)

/-- Pullback of global units along a composite of scheme morphisms, in
`Units.map _.appTop` form. -/
lemma units_map_appTop_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (u : Γ(Z, ⊤)ˣ) :
    Units.map f.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u)
      = Units.map (f ≫ g).appTop.hom.toMonoidHom u := by
  ext
  simp only [Units.coe_map, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rfl

/-- **`unitsAppLE` of a `⊤`-restriction is the `⊤`-restriction of the `appTop`-pullback.**
Restricting a global unit `u` on `Y` to a point-indexed open `V` and pulling it back along
`f` onto `O` equals pulling `u` back along `f` on global sections (`appTop`) and restricting
to `O`. This is the workhorse for recognizing the correction factors of a coherent witness
as pullbacks of a single global unit. -/
lemma Scheme.Hom.unitsAppLE_unitsRestrict_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V : Y.Opens} {O : X.Opens} (e : O ≤ f ⁻¹ᵁ V) (u : Γ(Y, ⊤)ˣ) :
    f.unitsAppLE V O e (Y.unitsRestrict le_top u)
      = X.unitsRestrict le_top (Units.map f.appTop.hom.toMonoidHom u) := by
  apply Units.ext
  simp only [Scheme.Hom.coe_unitsAppLE, Units.coe_map, MonoidHom.coe_coe,
    ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rfl

/-- Dividing both cochains of a coboundary relation by a common central unit `c` on the
left preserves the relation: `a * P = Q * b` gives `a / c * P = Q * (b / c)`. -/
private lemma witness_div_correction {G : Type u} [CommGroup G] {a b P Q c : G}
    (h : a * P = Q * b) : a / c * P = Q * (b / c) := by
  rw [div_mul_eq_mul_div, h, mul_div_assoc]

set_option quotPrecheck false in
local notation "Sq" => (overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "Scb" => (overSpec k (B ⊗[A] (B ⊗[A] B))).left

/-- **Assembling a coherent Čech witness by the global-unit correction (sub-brick ζ2·i).**
Given a Čech witness cochain `θ₀` on a common refinement `𝒲` of the two coprojection
pullbacks of `𝒩` (the coboundary relation `hdown`), and a global unit `χ` on
`Spec (B ⊗[A] B)` whose Amitsur coboundary `∂χ = (f₂₃^♯ χ)(f₁₂^♯ χ)/(f₁₃^♯ χ)` restricts
to the glued Amitsur defect of `θ₀` (hypothesis `hdefect`), the corrected cochain
`θ := θ₀ / χ` is again a witness and is moreover Amitsur-coherent — dividing a witness by a
global unit kills the glued Amitsur defect. This packages the final step of
`Over.exists_coherentCechWitness`. -/
theorem CoherentCechWitness.nonempty_of_defect_eq_coboundary
    (𝒩 : ((overSpec k B).left).PointedCover)
    (γ : ((overSpec k B).left).unitsCocycle 𝒩)
    (𝒲 : (Sq).PointedCover)
    (hW₁ : ∀ x, 𝒲.opens x ≤ (q₁) ⁻¹ᵁ 𝒩.opens ((q₁).base x))
    (hW₂ : ∀ x, 𝒲.opens x ≤ (q₂) ⁻¹ᵁ 𝒩.opens ((q₂).base x))
    (θ₀ : ∀ x : Sq, Γ(Sq, 𝒲.opens x)ˣ)
    (hdown : ∀ x y : Sq,
      (Sq).unitsRestrict (inf_le_left : 𝒲.opens x ⊓ 𝒲.opens y ≤ 𝒲.opens x) (θ₀ x)
        * (q₁).unitsAppLE (𝒩.opens ((q₁).base x) ⊓ 𝒩.opens ((q₁).base y))
            (𝒲.opens x ⊓ 𝒲.opens y)
            ((q₁).le_preimage_inf (inf_le_left.trans (hW₁ x)) (inf_le_right.trans (hW₁ y)))
            (Scheme.unitsEvInf γ ((q₁).base x) ((q₁).base y))
      = (q₂).unitsAppLE (𝒩.opens ((q₂).base x) ⊓ 𝒩.opens ((q₂).base y))
            (𝒲.opens x ⊓ 𝒲.opens y)
            ((q₂).le_preimage_inf (inf_le_left.trans (hW₂ x)) (inf_le_right.trans (hW₂ y)))
            (Scheme.unitsEvInf γ ((q₂).base x) ((q₂).base y))
        * (Sq).unitsRestrict inf_le_right (θ₀ y))
    (χ : Γ(Sq, ⊤)ˣ)
    (hdefect : ∀ z : Scb,
      (f₂₃).unitsAppLE (𝒲.opens ((f₂₃).base z)) ((amitsurCover 𝒲).opens z)
          (inf_le_left.trans inf_le_left) (θ₀ ((f₂₃).base z))
        * (f₁₂).unitsAppLE (𝒲.opens ((f₁₂).base z)) ((amitsurCover 𝒲).opens z)
            (inf_le_left.trans inf_le_right) (θ₀ ((f₁₂).base z))
        / (f₁₃).unitsAppLE (𝒲.opens ((f₁₃).base z)) ((amitsurCover 𝒲).opens z)
            inf_le_right (θ₀ ((f₁₃).base z))
      = (Scb).unitsRestrict le_top
          (Units.map (f₂₃).appTop.hom.toMonoidHom χ
            * Units.map (f₁₂).appTop.hom.toMonoidHom χ
            / Units.map (f₁₃).appTop.hom.toMonoidHom χ)) :
    Nonempty (CoherentCechWitness k A B 𝒩 γ) := by
  refine ⟨{
    cover := 𝒲
    le_pullbackInl := hW₁
    le_pullbackInr := hW₂
    θ := fun x ↦ θ₀ x / (Sq).unitsRestrict le_top χ
    witness := ?_
    coherent := ?_ }⟩
  · intro x y
    simp only [map_div, Scheme.unitsRestrict_unitsRestrict]
    exact witness_div_correction (hdown x y)
  · intro z
    simp only [map_div, Scheme.Hom.unitsAppLE_unitsRestrict_top]
    apply div_mul_div_eq_of_mul_div
    rw [hdefect z, map_div, map_mul]

end AlgebraicGeometry
