/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.CoherentWitnessCochains
import AlgebraicJacobian.Picard.UnitsGlobalPullback

/-!
# Existence of the Amitsur-coherent Čech witness (sub-brick ζ2·i)

This file proves the coherent-witness step of the (C1) étale-separatedness assembly
(`informal/c1-etale-separatedness-assembly.md`, ζ2 "global-unit correction" route):

* `AlgebraicGeometry.Over.glued_defect_eq_amitsur_coboundary` (Step G): the glued Amitsur
  defect `ω̄` of a witness cochain equals the Amitsur coboundary of the descended
  comparison unit `χ` — checked upstairs on the curve product, where the Amitsur telescope
  of the comparison cancels exactly and the projection pullback is injective on global
  units (ζ2·P).
* `AlgebraicGeometry.Over.exists_coherentCechWitness`: in ζ1's setting — `C` proper,
  geometrically irreducible and geometrically reduced over a field `k`, a tower
  `k → A → B` of algebras, `L` a Čech Picard class on `(C ⊗ Spec A).left` and `γ` a unit
  cocycle on a pointed cover `𝒩` of `Spec B` whose class pulls back from `L`
  (`p_B^* N = (C ◁ Spec (ofId A B))^* L`) — there exists an Amitsur-coherent Čech
  witness (`AlgebraicGeometry.CoherentCechWitness`) for ζ1's class equality
  `q₁^* N = q₂^* N` over `Spec (B ⊗[A] B)`.

The construction: ζ1 and the `mk`-calculus produce a witness cochain `θ₀` on a common
refinement `𝒲` (Step A) and an upstairs witness `α` for the lift (Step D); the defect of
`θ₀` glues to a global unit `ω̄` (`Over.exists_glued_defect`, Steps B–C); the comparison
of `p₂^♯ θ₀` with the `α`-coboundary glues and descends to a global unit `χ` downstairs
(`Over.exists_comparison_unit`, Steps E–F); Step G identifies `ω̄` with the Amitsur
coboundary of `χ`; and dividing `θ₀` by `χ` yields the coherent witness
(`CoherentCechWitness.nonempty_of_defect_eq_coboundary`).
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

-- Spec-side objects and maps
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
local notation "pB" => (snd C (overSpec k B)).left
set_option quotPrecheck false in
local notation "p₂" => (snd C (overSpec k (B ⊗[A] B))).left
set_option quotPrecheck false in
local notation "p₃" => (snd C (overSpec k (B ⊗[A] (B ⊗[A] B)))).left
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
local notation "cg" =>
  (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left

/-! ## Step G: the glued defect is the Amitsur coboundary of the comparison unit -/

/-- The pointed cover of the triple-tensor curve product on which the two sides of
Step G are compared: the `amitsurCover` pulled back along the projection `p₃`,
intersected with the three `w`-face pullbacks of the comparison cover. An opaque `def`
(not an `abbrev`): its unfolding is a large cover expression which would otherwise be
duplicated into every `unitsAppLE` argument of the Step-G statements, blowing up the
kernel-checked proof terms. Consumers access it through the `stepGCover_le_*` lemmas. -/
private noncomputable def stepGCover (𝒲 : (Sq).PointedCover)
    (𝒜 : (XB).PointedCover) : (Xcb).PointedCover :=
  ((amitsurCover 𝒲).pullback (p₃))
    ⊓ (((Over.comparisonCover C 𝒲 𝒜).pullback (w₂₃)
        ⊓ (Over.comparisonCover C 𝒲 𝒜).pullback (w₁₂))
      ⊓ (Over.comparisonCover C 𝒲 𝒜).pullback (w₁₃))

private lemma stepGCover_le_proj (𝒲 : (Sq).PointedCover) (𝒜 : (XB).PointedCover)
    (x : Xcb) :
    (stepGCover C 𝒲 𝒜).opens x ≤ (p₃) ⁻¹ᵁ (amitsurCover 𝒲).opens ((p₃).base x) :=
  inf_le_left

private lemma stepGCover_le_w₂₃ (𝒲 : (Sq).PointedCover) (𝒜 : (XB).PointedCover)
    (x : Xcb) :
    (stepGCover C 𝒲 𝒜).opens x
      ≤ (w₂₃) ⁻¹ᵁ (Over.comparisonCover C 𝒲 𝒜).opens ((w₂₃).base x) :=
  inf_le_right.trans (inf_le_left.trans inf_le_left)

private lemma stepGCover_le_w₁₂ (𝒲 : (Sq).PointedCover) (𝒜 : (XB).PointedCover)
    (x : Xcb) :
    (stepGCover C 𝒲 𝒜).opens x
      ≤ (w₁₂) ⁻¹ᵁ (Over.comparisonCover C 𝒲 𝒜).opens ((w₁₂).base x) :=
  inf_le_right.trans (inf_le_left.trans inf_le_right)

private lemma stepGCover_le_w₁₃ (𝒲 : (Sq).PointedCover) (𝒜 : (XB).PointedCover)
    (x : Xcb) :
    (stepGCover C 𝒲 𝒜).opens x
      ≤ (w₁₃) ⁻¹ᵁ (Over.comparisonCover C 𝒲 𝒜).opens ((w₁₃).base x) :=
  inf_le_right.trans inf_le_right

/-- The `p₃`-pullback of the glued defect `ω̄`, in canonical `w ≫ p₂` normal form. Split
from `Over.glued_defect_eq_amitsur_coboundary` so its proof term is kernel-checked as its
own declaration. -/
private lemma stepG_LHS (𝒲 : (Sq).PointedCover) (θ₀ : ∀ x : Sq, Γ(Sq, 𝒲.opens x)ˣ)
    (𝒜 : (XB).PointedCover) (ωbar : Γ(Scb, ⊤)ˣ)
    (hωbar : ∀ z : Scb,
      (Scb).unitsRestrict le_top ωbar = Over.defectCochain 𝒲 θ₀ z)
    (x : Xcb) :
    (Xcb).unitsRestrict (le_top : (stepGCover C 𝒲 𝒜).opens x ≤ ⊤)
        (Units.map (p₃).appTop.hom.toMonoidHom ωbar)
      = (w₂₃ ≫ (p₂)).unitsAppLE (𝒲.opens ((w₂₃ ≫ (p₂)).base x))
          ((stepGCover C 𝒲 𝒜).opens x)
          ((stepGCover_le_w₂₃ C 𝒲 𝒜 x).trans
            ((w₂₃).preimage_mono inf_le_left))
          (θ₀ ((w₂₃ ≫ (p₂)).base x))
        * (w₁₂ ≫ (p₂)).unitsAppLE (𝒲.opens ((w₁₂ ≫ (p₂)).base x))
            ((stepGCover C 𝒲 𝒜).opens x)
            ((stepGCover_le_w₁₂ C 𝒲 𝒜 x).trans
              ((w₁₂).preimage_mono inf_le_left))
            (θ₀ ((w₁₂ ≫ (p₂)).base x))
        / (w₁₃ ≫ (p₂)).unitsAppLE (𝒲.opens ((w₁₃ ≫ (p₂)).base x))
            ((stepGCover C 𝒲 𝒜).opens x)
            ((stepGCover_le_w₁₃ C 𝒲 𝒜 x).trans
              ((w₁₃).preimage_mono inf_le_left))
            (θ₀ ((w₁₃ ≫ (p₂)).base x)) := by
  exact unitsAppLE_defect_pullback (p₃) (f₂₃) (f₁₂) (f₁₃)
    (w₂₃ ≫ (p₂)) (w₁₂ ≫ (p₂)) (w₁₃ ≫ (p₂)) θ₀ ωbar
    (stepGCover_le_proj C 𝒲 𝒜 x) x
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right
    (hωbar ((p₃).base x))
    (Over.snd_left_naturality C
      (Over.overSpecMap (tensorFace₂₃ (k := k) (A := A) (B := B)))).symm
    (Over.snd_left_naturality C
      (Over.overSpecMap (tensorFace₁₂ (k := k) (A := A) (B := B)))).symm
    (Over.snd_left_naturality C
      (Over.overSpecMap (tensorFace₁₃ (k := k) (A := A) (B := B)))).symm
    ((stepGCover_le_w₂₃ C 𝒲 𝒜 x).trans ((w₂₃).preimage_mono inf_le_left))
    ((stepGCover_le_w₁₂ C 𝒲 𝒜 x).trans ((w₁₂).preimage_mono inf_le_left))
    ((stepGCover_le_w₁₃ C 𝒲 𝒜 x).trans ((w₁₃).preimage_mono inf_le_left))
/-- The `w₂₃`-pullback of the descended comparison unit, in canonical three-insertions
normal form. Split from `Over.glued_defect_eq_amitsur_coboundary` for kernel checking. -/
private lemma stepG_R₂₃ (𝒲 : (Sq).PointedCover) (θ₀ : ∀ x : Sq, Γ(Sq, 𝒲.opens x)ˣ)
    (𝒜 : (XB).PointedCover) (α : ∀ v : XB, Γ(XB, 𝒜.opens v)ˣ)
    (ψ : Γ(Xq, ⊤)ˣ)
    (hψ : ∀ s : Xq,
      (Xq).unitsRestrict le_top ψ = Over.comparisonCochain C 𝒲 θ₀ 𝒜 α s)
    (x : Xcb) :
    (w₂₃).unitsAppLE ⊤ ((stepGCover C 𝒲 𝒜).opens x) le_top ψ
      = (w₂₃ ≫ (p₂)).unitsAppLE (𝒲.opens ((w₂₃ ≫ (p₂)).base x))
          ((stepGCover C 𝒲 𝒜).opens x)
          ((stepGCover_le_w₂₃ C 𝒲 𝒜 x).trans
            ((w₂₃).preimage_mono inf_le_left))
          (θ₀ ((w₂₃ ≫ (p₂)).base x))
        * ((w₂₃ ≫ (u₂)).unitsAppLE (𝒜.opens ((w₂₃ ≫ (u₂)).base x))
            ((stepGCover C 𝒲 𝒜).opens x)
            ((stepGCover_le_w₂₃ C 𝒲 𝒜 x).trans
              ((w₂₃).preimage_mono (inf_le_right.trans inf_le_right)))
            (α ((w₂₃ ≫ (u₂)).base x))
          / (w₂₃ ≫ (u₁)).unitsAppLE (𝒜.opens ((w₂₃ ≫ (u₁)).base x))
            ((stepGCover C 𝒲 𝒜).opens x)
            ((stepGCover_le_w₂₃ C 𝒲 𝒜 x).trans
              ((w₂₃).preimage_mono (inf_le_right.trans inf_le_left)))
            (α ((w₂₃ ≫ (u₁)).base x))) := by
  refine (Scheme.Hom.map_unitsAppLE (w₂₃) (stepGCover_le_w₂₃ C 𝒲 𝒜 x)
    ((homOfLE le_top).op) ψ).symm.trans ?_
  refine (congrArg
    ((w₂₃).unitsAppLE ((Over.comparisonCover C 𝒲 𝒜).opens ((w₂₃).base x))
      ((stepGCover C 𝒲 𝒜).opens x) (stepGCover_le_w₂₃ C 𝒲 𝒜 x))
    (hψ ((w₂₃).base x))).trans ?_
  exact unitsAppLE_mulRatio_comp (w₂₃) (p₂) (u₂) (u₁) θ₀ α
    (stepGCover_le_w₂₃ C 𝒲 𝒜 x) x
    inf_le_left (inf_le_right.trans inf_le_right) (inf_le_right.trans inf_le_left)

/-- The `w₁₂`-pullback of the descended comparison unit, in canonical three-insertions
normal form (the base square collapses `w₁₂ ≫ u₂` onto `w₂₃ ≫ u₁`). -/
private lemma stepG_R₁₂ (𝒲 : (Sq).PointedCover) (θ₀ : ∀ x : Sq, Γ(Sq, 𝒲.opens x)ˣ)
    (𝒜 : (XB).PointedCover) (α : ∀ v : XB, Γ(XB, 𝒜.opens v)ˣ)
    (ψ : Γ(Xq, ⊤)ˣ)
    (hψ : ∀ s : Xq,
      (Xq).unitsRestrict le_top ψ = Over.comparisonCochain C 𝒲 θ₀ 𝒜 α s)
    (x : Xcb) :
    (w₁₂).unitsAppLE ⊤ ((stepGCover C 𝒲 𝒜).opens x) le_top ψ
      = (w₁₂ ≫ (p₂)).unitsAppLE (𝒲.opens ((w₁₂ ≫ (p₂)).base x))
          ((stepGCover C 𝒲 𝒜).opens x)
          ((stepGCover_le_w₁₂ C 𝒲 𝒜 x).trans
            ((w₁₂).preimage_mono inf_le_left))
          (θ₀ ((w₁₂ ≫ (p₂)).base x))
        * ((w₂₃ ≫ (u₁)).unitsAppLE (𝒜.opens ((w₂₃ ≫ (u₁)).base x))
            ((stepGCover C 𝒲 𝒜).opens x)
            ((stepGCover_le_w₂₃ C 𝒲 𝒜 x).trans
              ((w₂₃).preimage_mono (inf_le_right.trans inf_le_left)))
            (α ((w₂₃ ≫ (u₁)).base x))
          / (w₁₂ ≫ (u₁)).unitsAppLE (𝒜.opens ((w₁₂ ≫ (u₁)).base x))
            ((stepGCover C 𝒲 𝒜).opens x)
            ((stepGCover_le_w₁₂ C 𝒲 𝒜 x).trans
              ((w₁₂).preimage_mono (inf_le_right.trans inf_le_left)))
            (α ((w₁₂ ≫ (u₁)).base x))) := by
  exact unitsAppLE_ratio_pullback (w₁₂) (p₂) (u₂) (u₁)
    (w₁₂ ≫ (p₂)) (w₂₃ ≫ (u₁)) (w₁₂ ≫ (u₁)) θ₀ α ψ
    (stepGCover_le_w₁₂ C 𝒲 𝒜 x) x
    inf_le_left (inf_le_right.trans inf_le_right) (inf_le_right.trans inf_le_left)
    (hψ ((w₁₂).base x))
    rfl
    (Over.whiskerLeft_face₁₂_inr (k := k) (A := A) (B := B) C)
    rfl
    ((stepGCover_le_w₁₂ C 𝒲 𝒜 x).trans ((w₁₂).preimage_mono inf_le_left))
    ((stepGCover_le_w₂₃ C 𝒲 𝒜 x).trans
      ((w₂₃).preimage_mono (inf_le_right.trans inf_le_left)))
    ((stepGCover_le_w₁₂ C 𝒲 𝒜 x).trans
      ((w₁₂).preimage_mono (inf_le_right.trans inf_le_left)))

/-- The `w₁₃`-pullback of the descended comparison unit, in canonical three-insertions
normal form (both `α`-terms collapse onto the `w₂₃ ≫ u₂` and `w₁₂ ≫ u₁` insertions). -/
private lemma stepG_R₁₃ (𝒲 : (Sq).PointedCover) (θ₀ : ∀ x : Sq, Γ(Sq, 𝒲.opens x)ˣ)
    (𝒜 : (XB).PointedCover) (α : ∀ v : XB, Γ(XB, 𝒜.opens v)ˣ)
    (ψ : Γ(Xq, ⊤)ˣ)
    (hψ : ∀ s : Xq,
      (Xq).unitsRestrict le_top ψ = Over.comparisonCochain C 𝒲 θ₀ 𝒜 α s)
    (x : Xcb) :
    (w₁₃).unitsAppLE ⊤ ((stepGCover C 𝒲 𝒜).opens x) le_top ψ
      = (w₁₃ ≫ (p₂)).unitsAppLE (𝒲.opens ((w₁₃ ≫ (p₂)).base x))
          ((stepGCover C 𝒲 𝒜).opens x)
          ((stepGCover_le_w₁₃ C 𝒲 𝒜 x).trans
            ((w₁₃).preimage_mono inf_le_left))
          (θ₀ ((w₁₃ ≫ (p₂)).base x))
        * ((w₂₃ ≫ (u₂)).unitsAppLE (𝒜.opens ((w₂₃ ≫ (u₂)).base x))
            ((stepGCover C 𝒲 𝒜).opens x)
            ((stepGCover_le_w₂₃ C 𝒲 𝒜 x).trans
              ((w₂₃).preimage_mono (inf_le_right.trans inf_le_right)))
            (α ((w₂₃ ≫ (u₂)).base x))
          / (w₁₂ ≫ (u₁)).unitsAppLE (𝒜.opens ((w₁₂ ≫ (u₁)).base x))
            ((stepGCover C 𝒲 𝒜).opens x)
            ((stepGCover_le_w₁₂ C 𝒲 𝒜 x).trans
              ((w₁₂).preimage_mono (inf_le_right.trans inf_le_left)))
            (α ((w₁₂ ≫ (u₁)).base x))) := by
  exact unitsAppLE_ratio_pullback (w₁₃) (p₂) (u₂) (u₁)
    (w₁₃ ≫ (p₂)) (w₂₃ ≫ (u₂)) (w₁₂ ≫ (u₁)) θ₀ α ψ
    (stepGCover_le_w₁₃ C 𝒲 𝒜 x) x
    inf_le_left (inf_le_right.trans inf_le_right) (inf_le_right.trans inf_le_left)
    (hψ ((w₁₃).base x))
    rfl
    (Over.whiskerLeft_face₁₃_inr (k := k) (A := A) (B := B) C)
    (Over.whiskerLeft_face₁₂_inl (k := k) (A := A) (B := B) C).symm
    ((stepGCover_le_w₁₃ C 𝒲 𝒜 x).trans ((w₁₃).preimage_mono inf_le_left))
    ((stepGCover_le_w₂₃ C 𝒲 𝒜 x).trans
      ((w₂₃).preimage_mono (inf_le_right.trans inf_le_right)))
    ((stepGCover_le_w₁₂ C 𝒲 𝒜 x).trans
      ((w₁₂).preimage_mono (inf_le_right.trans inf_le_left)))

/-- **Step G of ζ2·i.** If the glued Amitsur defect `ω̄` of a witness cochain `θ₀`
restricts to the defect cochain (`hωbar`), and the comparison unit `χ` pulls back on the
curve product to the comparison cochain of `θ₀` against an upstairs witness `α` (`hχ`),
then `ω̄` is the Amitsur coboundary of `χ`. Both sides are compared after pullback along
the projection `p₃` — injective on global units (ζ2·P) — where the upstairs Amitsur
telescope of the comparison cancels exactly. -/
theorem Over.glued_defect_eq_amitsur_coboundary
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    (𝒲 : (Sq).PointedCover) (θ₀ : ∀ x : Sq, Γ(Sq, 𝒲.opens x)ˣ)
    (𝒜 : (XB).PointedCover) (α : ∀ v : XB, Γ(XB, 𝒜.opens v)ˣ)
    (ωbar : Γ(Scb, ⊤)ˣ)
    (hωbar : ∀ z : Scb,
      (Scb).unitsRestrict le_top ωbar = Over.defectCochain 𝒲 θ₀ z)
    (χ : Γ(Sq, ⊤)ˣ)
    (hχ : ∀ s : Xq,
      (Xq).unitsRestrict le_top (Units.map (p₂).appTop.hom.toMonoidHom χ)
        = Over.comparisonCochain C 𝒲 θ₀ 𝒜 α s) :
    ωbar = Units.map (f₂₃).appTop.hom.toMonoidHom χ
        * Units.map (f₁₂).appTop.hom.toMonoidHom χ
        / Units.map (f₁₃).appTop.hom.toMonoidHom χ := by
  apply Over.appTop_units_injective C (B ⊗[A] (B ⊗[A] B))
  apply Scheme.global_unit_ext (𝒰 := stepGCover C 𝒲 𝒜)
  intro x
  -- the pullback of a face-pullback of `χ` along `p₃` is a `w`-pullback of the
  -- descended comparison unit
  have factor : ∀ (φS : Scb ⟶ Sq) (φX : Xcb ⟶ Xq)
      (hcomm : φX ≫ (p₂) = (p₃) ≫ φS),
      (Xcb).unitsRestrict (le_top : (stepGCover C 𝒲 𝒜).opens x ≤ ⊤)
          (Units.map (p₃).appTop.hom.toMonoidHom
            (Units.map φS.appTop.hom.toMonoidHom χ))
        = φX.unitsAppLE ⊤ ((stepGCover C 𝒲 𝒜).opens x) le_top
            (Units.map (p₂).appTop.hom.toMonoidHom χ) := by
    intro φS φX hcomm
    rw [units_map_appTop_comp, ← hcomm, ← units_map_appTop_comp,
      unitsAppLE_top_global]
  -- assemble: both sides restrict to the same Amitsur combination
  simp only [map_mul, map_div]
  exact (stepG_LHS C 𝒲 θ₀ 𝒜 ωbar hωbar x).trans
    ((telescope_mul_div _ _ _ _ _ _).symm.trans
      (congrArg₂ (· / ·)
        (congrArg₂ (· * ·)
          ((factor (f₂₃) (w₂₃) (Over.snd_left_naturality C
              (Over.overSpecMap (tensorFace₂₃ (k := k) (A := A) (B := B))))).trans
            (stepG_R₂₃ C 𝒲 θ₀ 𝒜 α _ hχ x))
          ((factor (f₁₂) (w₁₂) (Over.snd_left_naturality C
              (Over.overSpecMap (tensorFace₁₂ (k := k) (A := A) (B := B))))).trans
            (stepG_R₁₂ C 𝒲 θ₀ 𝒜 α _ hχ x)))
        ((factor (f₁₃) (w₁₃) (Over.snd_left_naturality C
            (Over.overSpecMap (tensorFace₁₃ (k := k) (A := A) (B := B))))).trans
          (stepG_R₁₃ C 𝒲 θ₀ 𝒜 α _ hχ x))).symm)

/-! ## The existence theorem -/

set_option maxHeartbeats 1600000 in
-- The instantiated cover expressions on the triple-tensor curve product are large.
/-- **Existence of the Amitsur-coherent Čech witness (sub-brick ζ2·i)** of the (C1)
étale-separatedness assembly, by the global-unit correction argument. In ζ1's setting —
if the class of `γ` on `Spec B` pulls back, on the curve product, from the class `L` on
`C ⊗ Spec A` — then ζ1's class equality `q₁^* N = q₂^* N` over `Spec (B ⊗[A] B)` admits a
witness cochain which is Amitsur-coherent over the triple tensor. -/
theorem Over.exists_coherentCechWitness
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    (L : ((C ⊗ overSpec k A).left).CechPic)
    (𝒩 : ((overSpec k B).left).PointedCover) (γ : ((overSpec k B).left).unitsCocycle 𝒩)
    (h : Scheme.CechPic.map (snd C (overSpec k B)).left (Scheme.CechPic.mk 𝒩 γ.class)
        = Scheme.CechPic.map
            (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left L) :
    Nonempty (CoherentCechWitness k A B 𝒩 γ) := by
  classical
  -- ### ζ1: the two coprojection pullbacks of `N` agree
  have hz1 := Over.cechPicMap_tensorInl_eq_tensorInr C L (Scheme.CechPic.mk 𝒩 γ.class) h
  -- ### Step A: extract a witness cochain `θ₀` on a common refinement `𝒲`
  rw [Scheme.CechPic.map_mk, Scheme.CechPic.map_mk, Scheme.Hom.pullbackUnitsH1_class,
    Scheme.Hom.pullbackUnitsH1_class] at hz1
  obtain ⟨𝒲, hW₁, hW₂, eW⟩ := Scheme.CechPic.mk_eq_mk_iff.mp hz1
  have eW' : (((q₁).pullbackUnitsCocycle γ).res fun x ↦ homOfLE (hW₁ x)).IsCohomologous
      (((q₂).pullbackUnitsCocycle γ).res fun x ↦ homOfLE (hW₂ x)) :=
    (OneCocycle.class_eq_iff _ _).mp eW
  obtain ⟨θ₀, hθ₀⟩ := (OneCocycle.isCohomologous_iff_evInf _ _).mp eW'
  -- the coboundary relation for `θ₀`, in `unitsAppLE` normal form
  have hdown : ∀ x y : Sq,
      (Sq).unitsRestrict (inf_le_left : 𝒲.opens x ⊓ 𝒲.opens y ≤ 𝒲.opens x) (θ₀ x)
        * (q₁).unitsAppLE (𝒩.opens ((q₁).base x) ⊓ 𝒩.opens ((q₁).base y))
            (𝒲.opens x ⊓ 𝒲.opens y)
            ((q₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
              (inf_le_right.trans (hW₁ y)))
            (Scheme.unitsEvInf γ ((q₁).base x) ((q₁).base y))
      = (q₂).unitsAppLE (𝒩.opens ((q₂).base x) ⊓ 𝒩.opens ((q₂).base y))
            (𝒲.opens x ⊓ 𝒲.opens y)
            ((q₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
              (inf_le_right.trans (hW₂ y)))
            (Scheme.unitsEvInf γ ((q₂).base x) ((q₂).base y))
        * (Sq).unitsRestrict inf_le_right (θ₀ y) := by
    intro x y
    have h1 : (Sq).unitsRestrict (inf_le_left : 𝒲.opens x ⊓ 𝒲.opens y ≤ 𝒲.opens x) (θ₀ x)
          * Scheme.unitsEvInf
              (((q₁).pullbackUnitsCocycle γ).res fun z ↦ homOfLE (hW₁ z)) x y
        = Scheme.unitsEvInf
              (((q₂).pullbackUnitsCocycle γ).res fun z ↦ homOfLE (hW₂ z)) x y
          * (Sq).unitsRestrict inf_le_right (θ₀ y) := hθ₀ x y
    rw [Scheme.res_unitsEvInf, Scheme.res_unitsEvInf,
      Scheme.Hom.pullbackUnitsCocycle_unitsEvInf, Scheme.Hom.pullbackUnitsCocycle_unitsEvInf,
      Scheme.Hom.unitsAppLE_map, Scheme.Hom.unitsAppLE_map] at h1
    exact h1
  -- ### Step D: the upstairs witness `α` on the curve product `X_B`
  induction L using Scheme.CechPic.ind with | _ ℒ l =>
  induction l using Quot.ind with | _ lam =>
  rw [Scheme.CechPic.map_mk, Scheme.CechPic.map_mk] at h
  obtain ⟨𝒜, hA₁, hA₂, eA⟩ := Scheme.CechPic.mk_eq_mk_iff.mp h
  have eA' : (((pB).pullbackUnitsCocycle γ).res fun v ↦ homOfLE (hA₁ v)).IsCohomologous
      (((cg).pullbackUnitsCocycle lam).res fun v ↦ homOfLE (hA₂ v)) :=
    (OneCocycle.class_eq_iff _ _).mp eA
  obtain ⟨α, hα₀⟩ := (OneCocycle.isCohomologous_iff_evInf _ _).mp eA'
  -- the coboundary relation for `α`, in `unitsAppLE` normal form
  have hup : ∀ v w : XB,
      (XB).unitsRestrict (inf_le_left : 𝒜.opens v ⊓ 𝒜.opens w ≤ 𝒜.opens v) (α v)
        * (pB).unitsAppLE (𝒩.opens ((pB).base v) ⊓ 𝒩.opens ((pB).base w))
            (𝒜.opens v ⊓ 𝒜.opens w)
            ((pB).le_preimage_inf (inf_le_left.trans (hA₁ v))
              (inf_le_right.trans (hA₁ w)))
            (Scheme.unitsEvInf γ ((pB).base v) ((pB).base w))
      = (cg).unitsAppLE (ℒ.opens ((cg).base v) ⊓ ℒ.opens ((cg).base w))
            (𝒜.opens v ⊓ 𝒜.opens w)
            ((cg).le_preimage_inf (inf_le_left.trans (hA₂ v))
              (inf_le_right.trans (hA₂ w)))
            (Scheme.unitsEvInf lam ((cg).base v) ((cg).base w))
        * (XB).unitsRestrict inf_le_right (α w) := by
    intro v w
    have h1 : (XB).unitsRestrict (inf_le_left : 𝒜.opens v ⊓ 𝒜.opens w ≤ 𝒜.opens v) (α v)
          * Scheme.unitsEvInf
              (((pB).pullbackUnitsCocycle γ).res fun z ↦ homOfLE (hA₁ z)) v w
        = Scheme.unitsEvInf
              (((cg).pullbackUnitsCocycle lam).res fun z ↦ homOfLE (hA₂ z)) v w
          * (XB).unitsRestrict inf_le_right (α w) := hα₀ v w
    rw [Scheme.res_unitsEvInf, Scheme.res_unitsEvInf,
      Scheme.Hom.pullbackUnitsCocycle_unitsEvInf, Scheme.Hom.pullbackUnitsCocycle_unitsEvInf,
      Scheme.Hom.unitsAppLE_map, Scheme.Hom.unitsAppLE_map] at h1
    exact h1
  -- ### Steps B–C: glue the Amitsur defect of `θ₀` to a global unit `ω̄`
  obtain ⟨ωbar, hωbar⟩ := Over.exists_glued_defect 𝒩 γ 𝒲 hW₁ hW₂ θ₀ hdown
  -- ### Steps E–F: glue the comparison and descend it to a global unit `χ`
  obtain ⟨χ, hχ⟩ :=
    Over.exists_comparison_unit C 𝒩 γ 𝒲 hW₁ hW₂ θ₀ hdown ℒ lam 𝒜 hA₁ hA₂ α hup
  -- ### Final assembly: `θ := θ₀ / χ` is a coherent witness (correction lemma)
  refine CoherentCechWitness.nonempty_of_defect_eq_coboundary 𝒩 γ 𝒲 hW₁ hW₂ θ₀ hdown χ
    (fun z ↦ ?_)
  change Over.defectCochain 𝒲 θ₀ z = _
  rw [← hωbar z,
    Over.glued_defect_eq_amitsur_coboundary C 𝒲 θ₀ 𝒜 α ωbar hωbar χ hχ]

end AlgebraicGeometry
