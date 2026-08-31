/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.CoherentWitness

/-!
# The defect and comparison cochains of a Čech witness (ζ2·i, Steps B–C and E–F)

Intermediate gluing steps of the coherent-witness construction
(`informal/c1-etale-separatedness-assembly.md`, ζ2 "global-unit correction" route), split
out of `Over.exists_coherentCechWitness` so that each step is elaborated and kernel-checked
as its own declaration:

* `AlgebraicGeometry.Over.defectCochain`: the Amitsur defect
  `ω := (f₂₃^♯ θ₀) ⋅ (f₁₂^♯ θ₀) / (f₁₃^♯ θ₀)` of a `0`-cochain `θ₀` on a pointed cover of
  `Spec (B ⊗[A] B)`, a unit `0`-cochain on the canonical refinement `amitsurCover` of the
  triple tensor.
* `AlgebraicGeometry.Over.exists_glued_defect` (Steps B–C): for a *witness* cochain `θ₀`
  (coboundary relation `hdown` against the two coprojection pullbacks of `γ`), the defect
  has trivial Čech coboundary — the three coface pullbacks of the defining relation
  telescope through the simplicial coincidences — so it glues to a global unit `ω̄` (P1).
* `AlgebraicGeometry.Over.comparisonCochain`: on the curve product `X_{B ⊗ B}`, the
  comparison `p₂^♯ θ₀ ⋅ (u₂^♯ α / u₁^♯ α)` of the witness with an upstairs witness `α`
  for the lift, on the canonical common refinement `comparisonCover` of the pulled-back
  covers.
* `AlgebraicGeometry.Over.exists_comparison_unit` (Steps E–F): the comparison cochain has
  trivial coboundary — the `L`-terms cancel by the diagonal coincidence — so it glues to a
  global unit of the curve product (P1) which descends through the projection to a global
  unit `χ` of `Spec (B ⊗[A] B)` (P2b).

The consumer `Over.exists_coherentCechWitness` corrects `θ₀` by `χ`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace AlgebraicGeometry

/-- **Compatibility of a ratio cochain from two coboundary relations.** Suppose a unit
`0`-cochain `c` on a pointed cover `𝒞` of `Yc` cobounds the comparison of a pair-indexed
family `EZ` pulled back along `rc₁, rc₂ : Yc ⟶ Z` (`hrelc`), and a `0`-cochain `a` on a
pointed cover `𝒜` of `Ya` cobounds the comparison of `EZ` (along `s₁ : Ya ⟶ Z`) with a
family `EW` (along `s₂ : Ya ⟶ W`) (`hrela`). If the pulled-back comparison composites
coincide pairwise — `φt ≫ rc₁ = φ₁ ≫ s₁`, `φt ≫ rc₂ = φ₂ ≫ s₁`, and the diagonal
coincidence `φ₁ ≫ s₂ = φ₂ ≫ s₂` — then the ratio cochain `φt^♯c ⋅ (φ₂^♯a / φ₁^♯a)` on `X`
is Čech-compatible: its values at any two points agree on a common open `O`. Stated over
abstract schemes so its proof term is kernel-checked once, over small types; the concrete
curve-product instantiation is a single application. -/
theorem Scheme.Hom.unitsAppLE_coboundary_ratio_compat {X Yc Ya Z W : Scheme.{u}}
    (φt : X ⟶ Yc) (φ₁ φ₂ : X ⟶ Ya)
    (rc₁ rc₂ : Yc ⟶ Z) (s₁ : Ya ⟶ Z) (s₂ : Ya ⟶ W)
    {𝒞 : Yc.PointedCover} (c : ∀ y : Yc, Γ(Yc, 𝒞.opens y)ˣ)
    {𝒜 : Ya.PointedCover} (a : ∀ y : Ya, Γ(Ya, 𝒜.opens y)ˣ)
    (VZ : Z → Z → Z.Opens) (VW : W → W → W.Opens)
    (EZ : ∀ z z', Γ(Z, VZ z z')ˣ) (EW : ∀ w w', Γ(W, VW w w')ˣ)
    (ec₁ : ∀ y y' : Yc, 𝒞.opens y ⊓ 𝒞.opens y' ≤ rc₁ ⁻¹ᵁ VZ (rc₁.base y) (rc₁.base y'))
    (ec₂ : ∀ y y' : Yc, 𝒞.opens y ⊓ 𝒞.opens y' ≤ rc₂ ⁻¹ᵁ VZ (rc₂.base y) (rc₂.base y'))
    (ea₁ : ∀ y y' : Ya, 𝒜.opens y ⊓ 𝒜.opens y' ≤ s₁ ⁻¹ᵁ VZ (s₁.base y) (s₁.base y'))
    (ea₂ : ∀ y y' : Ya, 𝒜.opens y ⊓ 𝒜.opens y' ≤ s₂ ⁻¹ᵁ VW (s₂.base y) (s₂.base y'))
    (hrelc : ∀ y y' : Yc,
      Yc.unitsRestrict (inf_le_left : 𝒞.opens y ⊓ 𝒞.opens y' ≤ 𝒞.opens y) (c y)
          * rc₁.unitsAppLE (VZ (rc₁.base y) (rc₁.base y')) (𝒞.opens y ⊓ 𝒞.opens y')
              (ec₁ y y') (EZ (rc₁.base y) (rc₁.base y'))
        = rc₂.unitsAppLE (VZ (rc₂.base y) (rc₂.base y')) (𝒞.opens y ⊓ 𝒞.opens y')
              (ec₂ y y') (EZ (rc₂.base y) (rc₂.base y'))
          * Yc.unitsRestrict inf_le_right (c y'))
    (hrela : ∀ y y' : Ya,
      Ya.unitsRestrict (inf_le_left : 𝒜.opens y ⊓ 𝒜.opens y' ≤ 𝒜.opens y) (a y)
          * s₁.unitsAppLE (VZ (s₁.base y) (s₁.base y')) (𝒜.opens y ⊓ 𝒜.opens y')
              (ea₁ y y') (EZ (s₁.base y) (s₁.base y'))
        = s₂.unitsAppLE (VW (s₂.base y) (s₂.base y')) (𝒜.opens y ⊓ 𝒜.opens y')
              (ea₂ y y') (EW (s₂.base y) (s₂.base y'))
          * Ya.unitsRestrict inf_le_right (a y'))
    (hcomm₁ : φt ≫ rc₁ = φ₁ ≫ s₁) (hcomm₂ : φt ≫ rc₂ = φ₂ ≫ s₁)
    (hdiag : φ₁ ≫ s₂ = φ₂ ≫ s₂)
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
    VZ VZ EZ EZ ec₁ ec₂ hrelc x x' (O := O) hOt
  have r₁ := Scheme.Hom.unitsAppLE_coboundary_rel φ₁ s₁ s₂ (𝒞 := 𝒜) a
    VZ VW EZ EW ea₁ ea₂ hrela x x' (O := O) hO₁
  have r₂ := Scheme.Hom.unitsAppLE_coboundary_rel φ₂ s₁ s₂ (𝒞 := 𝒜) a
    VZ VW EZ EW ea₁ ea₂ hrela x x' (O := O) hO₂
  rw [Scheme.Hom.unitsAppLE_pair_congr_hom hcomm₁ VZ EZ x x' _,
    Scheme.Hom.unitsAppLE_pair_congr_hom hcomm₂ VZ EZ x x' _] at rt
  rw [Scheme.Hom.unitsAppLE_pair_congr_hom hdiag VW EW x x' _] at r₁
  exact coboundary_ratio_congr rt r₁ r₂

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
local notation "pB" => (snd C (overSpec k B)).left
set_option quotPrecheck false in
local notation "p₂" => (snd C (overSpec k (B ⊗[A] B))).left
set_option quotPrecheck false in
local notation "u₁" => (C ◁ Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "u₂" => (C ◁ Over.overSpecMap (tensorInr (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "cg" =>
  (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left

namespace Over

/-! ## The Amitsur defect cochain and its gluing (Steps B–C) -/


/-- The **Amitsur defect** of a unit `0`-cochain `θ₀` on a pointed cover `𝒲` of
`Spec (B ⊗[A] B)`: the combination `(f₂₃^♯ θ₀) ⋅ (f₁₂^♯ θ₀) / (f₁₃^♯ θ₀)` of its three
coface pullbacks, a unit `0`-cochain on the canonical common refinement `amitsurCover 𝒲`
of the triple tensor. A witness is *Amitsur-coherent* precisely when its defect is `1`. -/
noncomputable def defectCochain (𝒲 : (Sq).PointedCover)
    (θ₀ : ∀ x : Sq, Γ(Sq, 𝒲.opens x)ˣ) (z : Scb) :
    Γ(Scb, (amitsurCover 𝒲).opens z)ˣ :=
  (f₂₃).unitsAppLE (𝒲.opens ((f₂₃).base z)) ((amitsurCover 𝒲).opens z)
      (inf_le_left.trans inf_le_left) (θ₀ ((f₂₃).base z))
    * (f₁₂).unitsAppLE (𝒲.opens ((f₁₂).base z)) ((amitsurCover 𝒲).opens z)
      (inf_le_left.trans inf_le_right) (θ₀ ((f₁₂).base z))
    / (f₁₃).unitsAppLE (𝒲.opens ((f₁₃).base z)) ((amitsurCover 𝒲).opens z)
      inf_le_right (θ₀ ((f₁₃).base z))

/-- **Steps B–C: the Amitsur defect of a witness glues to a global unit (P1).** If `θ₀`
cobounds the comparison of the two coprojection pullbacks of `γ` (`hdown`), the three
coface pullbacks of that relation telescope, so the defect cochain is Čech-compatible and
glues to a global unit `ω̄` of the triple tensor. -/
theorem exists_glued_defect
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
              ((q₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
                (inf_le_right.trans (hW₁ y)))
              (Scheme.unitsEvInf γ ((q₁).base x) ((q₁).base y))
        = (q₂).unitsAppLE (𝒩.opens ((q₂).base x) ⊓ 𝒩.opens ((q₂).base y))
              (𝒲.opens x ⊓ 𝒲.opens y)
              ((q₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
                (inf_le_right.trans (hW₂ y)))
              (Scheme.unitsEvInf γ ((q₂).base x) ((q₂).base y))
          * (Sq).unitsRestrict inf_le_right (θ₀ y)) :
    ∃ ωbar : Γ(Scb, ⊤)ˣ, ∀ z : Scb,
      (Scb).unitsRestrict le_top ωbar = defectCochain 𝒲 θ₀ z := by
  apply Scheme.exists_global_unit_of_compatible (𝒰 := amitsurCover 𝒲)
    (defectCochain 𝒲 θ₀)
  intro z z'
  -- pull the witness relation back along the three cofaces
  have r₂₃ := Scheme.Hom.unitsAppLE_coboundary_rel (f₂₃) (q₁) (q₂) (𝒞 := 𝒲) θ₀
    (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b') (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b')
    (fun b b' ↦ Scheme.unitsEvInf γ b b') (fun b b' ↦ Scheme.unitsEvInf γ b b')
    (fun x y ↦ (q₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
      (inf_le_right.trans (hW₁ y)))
    (fun x y ↦ (q₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
      (inf_le_right.trans (hW₂ y)))
    hdown z z' (O := (amitsurCover 𝒲).opens z ⊓ (amitsurCover 𝒲).opens z')
    ((f₂₃).le_preimage_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
      (inf_le_right.trans (inf_le_left.trans inf_le_left)))
  have r₁₂ := Scheme.Hom.unitsAppLE_coboundary_rel (f₁₂) (q₁) (q₂) (𝒞 := 𝒲) θ₀
    (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b') (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b')
    (fun b b' ↦ Scheme.unitsEvInf γ b b') (fun b b' ↦ Scheme.unitsEvInf γ b b')
    (fun x y ↦ (q₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
      (inf_le_right.trans (hW₁ y)))
    (fun x y ↦ (q₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
      (inf_le_right.trans (hW₂ y)))
    hdown z z' (O := (amitsurCover 𝒲).opens z ⊓ (amitsurCover 𝒲).opens z')
    ((f₁₂).le_preimage_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
      (inf_le_right.trans (inf_le_left.trans inf_le_right)))
  have r₁₃ := Scheme.Hom.unitsAppLE_coboundary_rel (f₁₃) (q₁) (q₂) (𝒞 := 𝒲) θ₀
    (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b') (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b')
    (fun b b' ↦ Scheme.unitsEvInf γ b b') (fun b b' ↦ Scheme.unitsEvInf γ b b')
    (fun x y ↦ (q₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
      (inf_le_right.trans (hW₁ y)))
    (fun x y ↦ (q₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
      (inf_le_right.trans (hW₂ y)))
    hdown z z' (O := (amitsurCover 𝒲).opens z ⊓ (amitsurCover 𝒲).opens z')
    ((f₁₃).le_preimage_inf (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_right))
  -- collapse the six composite maps onto the three insertions
  rw [Scheme.Hom.unitsAppLE_pair_congr_hom
    (Over.overSpecMap_left_face₁₂_inr (k := k) (A := A) (B := B))
    (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b') (fun b b' ↦ Scheme.unitsEvInf γ b b')
    z z' _] at r₁₂
  rw [Scheme.Hom.unitsAppLE_pair_congr_hom
    (Over.overSpecMap_left_face₁₂_inl (k := k) (A := A) (B := B)).symm
    (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b') (fun b b' ↦ Scheme.unitsEvInf γ b b')
    z z' _] at r₁₃
  rw [Scheme.Hom.unitsAppLE_pair_congr_hom
    (Over.overSpecMap_left_face₁₃_inr (k := k) (A := A) (B := B))
    (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b') (fun b b' ↦ Scheme.unitsEvInf γ b b')
    z z' _] at r₁₃
  simp only [defectCochain, map_div, map_mul, Scheme.Hom.unitsAppLE_map]
  exact telescope_congr r₂₃ r₁₂ r₁₃

/-! ## The comparison cochain and its descent to the base (Steps E–F) -/


/-- The canonical common refinement of the pulled-back covers carrying the comparison
cochain on the curve product `X_{B ⊗ B}`: the witness cover `𝒲` pulled back along the
projection `p₂`, intersected with the upstairs cover `𝒜` pulled back along the two
whiskered coprojections `u₁, u₂`. -/
noncomputable def comparisonCover (𝒲 : (Sq).PointedCover)
    (𝒜 : (XB).PointedCover) : (Xq).PointedCover :=
  (𝒲.pullback (p₂)) ⊓ (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂))


/-- The **comparison cochain** `p₂^♯ θ₀ ⋅ (u₂^♯ α / u₁^♯ α)` of a witness cochain `θ₀`
downstairs against an upstairs witness `α`, on the canonical common refinement
`comparisonCover 𝒲 𝒜`. Its coboundary triviality is Step E of the coherent-witness
construction; its glued and descended global unit is the correcting unit `χ`. -/
noncomputable def comparisonCochain (𝒲 : (Sq).PointedCover)
    (θ₀ : ∀ x : Sq, Γ(Sq, 𝒲.opens x)ˣ)
    (𝒜 : (XB).PointedCover) (α : ∀ v : XB, Γ(XB, 𝒜.opens v)ˣ) (s : Xq) :
    Γ(Xq, (comparisonCover C 𝒲 𝒜).opens s)ˣ :=
  (p₂).unitsAppLE (𝒲.opens ((p₂).base s)) ((comparisonCover C 𝒲 𝒜).opens s)
      inf_le_left (θ₀ ((p₂).base s))
    * ((u₂).unitsAppLE (𝒜.opens ((u₂).base s)) ((comparisonCover C 𝒲 𝒜).opens s)
        (inf_le_right.trans inf_le_right) (α ((u₂).base s))
      / (u₁).unitsAppLE (𝒜.opens ((u₁).base s)) ((comparisonCover C 𝒲 𝒜).opens s)
        (inf_le_right.trans inf_le_left) (α ((u₁).base s)))

set_option maxHeartbeats 1600000 in
-- The coboundary-relation instances on the curve product are large expressions.
/-- **Step E: the comparison cochain is Čech-compatible** — the `θ₀`-terms compare through
the base square and the `L`-terms cancel by the diagonal coincidence, so the cochain has
trivial coboundary. Split from `exists_comparison_unit` so that its large proof term is
kernel-checked as its own declaration. -/
theorem comparisonCochain_compat
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
              ((q₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
                (inf_le_right.trans (hW₁ y)))
              (Scheme.unitsEvInf γ ((q₁).base x) ((q₁).base y))
        = (q₂).unitsAppLE (𝒩.opens ((q₂).base x) ⊓ 𝒩.opens ((q₂).base y))
              (𝒲.opens x ⊓ 𝒲.opens y)
              ((q₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
                (inf_le_right.trans (hW₂ y)))
              (Scheme.unitsEvInf γ ((q₂).base x) ((q₂).base y))
          * (Sq).unitsRestrict inf_le_right (θ₀ y))
    (ℒ : ((C ⊗ overSpec k A).left).PointedCover)
    (lam : ((C ⊗ overSpec k A).left).unitsCocycle ℒ)
    (𝒜 : (XB).PointedCover)
    (hA₁ : ∀ v, 𝒜.opens v ≤ (pB) ⁻¹ᵁ 𝒩.opens ((pB).base v))
    (hA₂ : ∀ v, 𝒜.opens v ≤ (cg) ⁻¹ᵁ ℒ.opens ((cg).base v))
    (α : ∀ v : XB, Γ(XB, 𝒜.opens v)ˣ)
    (hup : ∀ v w : XB,
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
          * (XB).unitsRestrict inf_le_right (α w)) :
    ∀ s s' : Xq,
      (Xq).unitsRestrict (inf_le_left :
          (comparisonCover C 𝒲 𝒜).opens s ⊓ (comparisonCover C 𝒲 𝒜).opens s'
            ≤ (comparisonCover C 𝒲 𝒜).opens s) (comparisonCochain C 𝒲 θ₀ 𝒜 α s)
        = (Xq).unitsRestrict inf_le_right (comparisonCochain C 𝒲 θ₀ 𝒜 α s') := by
    intro s s'
    simp only [comparisonCochain, map_div, map_mul, Scheme.Hom.unitsAppLE_map]
    exact Scheme.Hom.unitsAppLE_coboundary_ratio_compat (p₂) (u₁) (u₂) (q₁) (q₂)
      (pB) (cg) θ₀ α
      (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b') (fun b b' ↦ ℒ.opens b ⊓ ℒ.opens b')
      (fun b b' ↦ Scheme.unitsEvInf γ b b') (fun b b' ↦ Scheme.unitsEvInf lam b b')
      (fun x y ↦ (q₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
        (inf_le_right.trans (hW₁ y)))
      (fun x y ↦ (q₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
        (inf_le_right.trans (hW₂ y)))
      (fun v w ↦ (pB).le_preimage_inf (inf_le_left.trans (hA₁ v))
        (inf_le_right.trans (hA₁ w)))
      (fun v w ↦ (cg).le_preimage_inf (inf_le_left.trans (hA₂ v))
        (inf_le_right.trans (hA₂ w)))
      hdown hup
      (Over.snd_left_naturality C (Over.overSpecMap (tensorInl (A := A) (B := B)))).symm
      (Over.snd_left_naturality C (Over.overSpecMap (tensorInr (A := A) (B := B)))).symm
      (Over.whiskerLeft_inl_ofId C)
      s s'
      ((p₂).le_preimage_inf (inf_le_left.trans inf_le_left)
        (inf_le_right.trans inf_le_left))
      ((u₁).le_preimage_inf (inf_le_left.trans (inf_le_right.trans inf_le_left))
        (inf_le_right.trans (inf_le_right.trans inf_le_left)))
      ((u₂).le_preimage_inf (inf_le_left.trans (inf_le_right.trans inf_le_right))
        (inf_le_right.trans (inf_le_right.trans inf_le_right)))

/-- **Steps E–F: the comparison cochain glues and descends to the correcting unit (P1 +
P2b).** For a witness `θ₀` downstairs (`hdown`) and a witness `α` upstairs (`hup`, against
the lift `lam` of the class `L`), the comparison cochain is Čech-compatible
(`comparisonCochain_compat`), so it glues to a global unit of the curve product, which
descends through the projection `p₂` to a global unit `χ` of `Spec (B ⊗[A] B)`. -/
theorem exists_comparison_unit
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
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
              ((q₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
                (inf_le_right.trans (hW₁ y)))
              (Scheme.unitsEvInf γ ((q₁).base x) ((q₁).base y))
        = (q₂).unitsAppLE (𝒩.opens ((q₂).base x) ⊓ 𝒩.opens ((q₂).base y))
              (𝒲.opens x ⊓ 𝒲.opens y)
              ((q₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
                (inf_le_right.trans (hW₂ y)))
              (Scheme.unitsEvInf γ ((q₂).base x) ((q₂).base y))
          * (Sq).unitsRestrict inf_le_right (θ₀ y))
    (ℒ : ((C ⊗ overSpec k A).left).PointedCover)
    (lam : ((C ⊗ overSpec k A).left).unitsCocycle ℒ)
    (𝒜 : (XB).PointedCover)
    (hA₁ : ∀ v, 𝒜.opens v ≤ (pB) ⁻¹ᵁ 𝒩.opens ((pB).base v))
    (hA₂ : ∀ v, 𝒜.opens v ≤ (cg) ⁻¹ᵁ ℒ.opens ((cg).base v))
    (α : ∀ v : XB, Γ(XB, 𝒜.opens v)ˣ)
    (hup : ∀ v w : XB,
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
          * (XB).unitsRestrict inf_le_right (α w)) :
    ∃ χ : Γ(Sq, ⊤)ˣ, ∀ s : Xq,
      (Xq).unitsRestrict le_top (Units.map (p₂).appTop.hom.toMonoidHom χ)
        = comparisonCochain C 𝒲 θ₀ 𝒜 α s := by
  obtain ⟨ψ, hψ⟩ := Scheme.exists_global_unit_of_compatible
    (𝒰 := comparisonCover C 𝒲 𝒜) (comparisonCochain C 𝒲 θ₀ 𝒜 α)
    (comparisonCochain_compat C 𝒩 γ 𝒲 hW₁ hW₂ θ₀ hdown ℒ lam 𝒜 hA₁ hA₂ α hup)
  refine ⟨(Over.unitsSndTopEquiv C (B ⊗[A] B)).symm ψ, fun s ↦ ?_⟩
  have hχ : Units.map (p₂).appTop.hom.toMonoidHom
      ((Over.unitsSndTopEquiv C (B ⊗[A] B)).symm ψ) = ψ := by
    rw [← Over.unitsSndTopEquiv_apply]
    exact (Over.unitsSndTopEquiv C (B ⊗[A] B)).apply_symm_apply ψ
  rw [hχ]
  exact hψ s

end Over

end AlgebraicGeometry
