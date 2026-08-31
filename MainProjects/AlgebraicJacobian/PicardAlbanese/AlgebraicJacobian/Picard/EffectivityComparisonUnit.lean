/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.NormalizedComparison
import AlgebraicJacobian.Picard.EffectivityPieces

/-!
# The per-piece comparison unit ((C2) effectivity, brick E3: the gluing)

The (C2) effectivity campaign descends a rigidified class `L = CechPic.mk 𝒩 γ.class` on
the curve `X_B` along the cover inclusion `cg` piece by piece over `cg`-saturated affine
pieces `V` of the base curve `X_A` (brick E0).  The per-piece descent datum of brick E2
consumes a **comparison unit**: a single global unit of the double piece
`Γ(X_{B⊗B}, cgq⁻¹ V)` (≅ `Γ(V) ⊗[A] (B ⊗[A] B)`, the descent-cocycle ring of the piece).
This file manufactures it — the ζ2·ii mirror announced by the E2 frontier:

* `AlgebraicGeometry.Over.PieceTrivialization`: a trivializing `0`-cochain `t` of the
  representing cocycle `γ` on the piece `cg⁻¹ V` — the piece-level `L`-trivialization
  datum (`t b ⋅ γ(b,b') = t b'` on the `cg⁻¹ V`-trimmed pairwise overlaps).  This is the
  cochain witness of `[L|_{cg⁻¹V}] = 1`; it is a *hypothesis* of the per-piece
  construction, discharged by the piece-selection brick downstream.
* `AlgebraicGeometry.unitsTrivTwistCochain`: over abstract schemes, the twisted values
  `θ x ⋅ (r₂^♯ t)(x) / (r₁^♯ t)(x)` on the trimmed cover `{𝒞.opens x ⊓ DY}` of the
  double piece; their coboundary vanishes — the witness relation (N1) is exactly
  cancelled by the two pullbacks of the trivializing relation
  (`unitsTrivTwistCochain_compat`) — so they glue by the `𝒪ˣ`-sheaf axiom
  (`exists_glued_unitsTrivTwist`).
* `AlgebraicGeometry.Scheme.Hom.unitsAppLE_glued_trivTwist`: pullback of the glued unit
  in composite normal form (the E1 kernel discipline: the composite merge happens once,
  over abstract schemes).
* `AlgebraicGeometry.Over.pieceComparisonUnit`: the glued **comparison unit**
  `v_V ∈ Γ(X_{B⊗B}, cgq⁻¹ V)ˣ` of a σ-normalized comparison `W` and a piece
  trivialization `T`, with its defining restriction property
  (`pieceComparisonUnit_spec`) and its uniqueness (`pieceComparisonUnit_unique`).

The diagonal normalization and Amitsur coherence of `v_V` (the E2 hypotheses `hlmul`,
`hcoc`) are established in `AlgebraicJacobian.Picard.EffectivityPieceClass`, through the
ring-identification bridge of `AlgebraicJacobian.Picard.EffectivityPieceBridge`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace AlgebraicGeometry

/-- Telescope core for the gluing compatibility of the trivialization-twisted witness:
the witness relation `a ⋅ e₁ = e₂ ⋅ b` and the two pulled trivializing relations
`p ⋅ e₁ = p'`, `q ⋅ e₂ = q'` cancel to the equality of twisted values. -/
private lemma trivTwist_ratio_core {G : Type u} [CommGroup G] {a b e₁ e₂ p p' q q' : G}
    (h : a * e₁ = e₂ * b) (h1 : p * e₁ = p') (h2 : q * e₂ = q') :
    a * q * p⁻¹ = b * q' * p'⁻¹ := by
  subst h1; subst h2
  have key : a = e₂ * b * e₁⁻¹ := by rw [eq_mul_inv_iff_mul_eq, h]
  subst key
  rw [mul_inv_rev]
  calc e₂ * b * e₁⁻¹ * q * p⁻¹
      = (e₁⁻¹ * e₁) * (e₂ * b * e₁⁻¹ * q * p⁻¹) := by rw [inv_mul_cancel, one_mul]
    _ = b * (q * e₂) * (e₁⁻¹ * (e₁ * e₁⁻¹) * p⁻¹) := by ac_rfl
    _ = b * (q * e₂) * (e₁⁻¹ * p⁻¹) := by rw [mul_inv_cancel, mul_one]

/-! ## The trivialization-twisted witness cochain, over abstract schemes

Throughout, `r₁ r₂ : Y ⟶ Z` play the two coprojections `u₁, u₂ : X_{B⊗B} ⟶ X_B` on the
curve product, `𝒞`/`c` the comparison cover/cochain `(W.cover, W.θ)`, `𝒩`/`E` the
representing cover and the pair values `unitsEvInf γ` of the representing cocycle,
`DZ` the piece `cg⁻¹ V` of `X_B`, `DY` the double piece `cgq⁻¹ V` of `X_{B⊗B}`, and
`t` the trivializing `0`-cochain of `E` on the trimmed opens `𝒩.opens z ⊓ DZ`. -/

section TrivTwist

variable {Y Z : Scheme.{u}}

/-- The **trivialization-twisted witness value** at a point `y`, on `𝒞.opens y ⊓ DY`:
`θ y ⋅ (r₂^♯ t)(y) ⋅ ((r₁^♯ t)(y))⁻¹`.  Its coboundary vanishes
(`unitsTrivTwistCochain_compat`): the coboundary `r₂^♯E / r₁^♯E` of the witness is
exactly cancelled by the coboundaries of the two pulled trivializations. -/
noncomputable def unitsTrivTwistCochain (r₁ r₂ : Y ⟶ Z)
    (𝒞 : Y.PointedCover) (𝒩 : Z.PointedCover)
    (c : ∀ y : Y, Γ(Y, 𝒞.opens y)ˣ)
    (h𝒞₁ : ∀ y, 𝒞.opens y ≤ r₁ ⁻¹ᵁ 𝒩.opens (r₁.base y))
    (h𝒞₂ : ∀ y, 𝒞.opens y ≤ r₂ ⁻¹ᵁ 𝒩.opens (r₂.base y))
    (DZ : Z.Opens) (DY : Y.Opens)
    (hDY₁ : DY ≤ r₁ ⁻¹ᵁ DZ) (hDY₂ : DY ≤ r₂ ⁻¹ᵁ DZ)
    (t : ∀ z : Z, Γ(Z, 𝒩.opens z ⊓ DZ)ˣ) (y : Y) :
    Γ(Y, 𝒞.opens y ⊓ DY)ˣ :=
  Y.unitsRestrict (inf_le_left : 𝒞.opens y ⊓ DY ≤ 𝒞.opens y) (c y)
    * r₂.unitsAppLE (𝒩.opens (r₂.base y) ⊓ DZ) (𝒞.opens y ⊓ DY)
        (r₂.le_preimage_inf (inf_le_left.trans (h𝒞₂ y)) (inf_le_right.trans hDY₂))
        (t (r₂.base y))
    * (r₁.unitsAppLE (𝒩.opens (r₁.base y) ⊓ DZ) (𝒞.opens y ⊓ DY)
        (r₁.le_preimage_inf (inf_le_left.trans (h𝒞₁ y)) (inf_le_right.trans hDY₁))
        (t (r₁.base y)))⁻¹

lemma unitsTrivTwistCochain_def (r₁ r₂ : Y ⟶ Z)
    (𝒞 : Y.PointedCover) (𝒩 : Z.PointedCover)
    (c : ∀ y : Y, Γ(Y, 𝒞.opens y)ˣ)
    (h𝒞₁ : ∀ y, 𝒞.opens y ≤ r₁ ⁻¹ᵁ 𝒩.opens (r₁.base y))
    (h𝒞₂ : ∀ y, 𝒞.opens y ≤ r₂ ⁻¹ᵁ 𝒩.opens (r₂.base y))
    (DZ : Z.Opens) (DY : Y.Opens)
    (hDY₁ : DY ≤ r₁ ⁻¹ᵁ DZ) (hDY₂ : DY ≤ r₂ ⁻¹ᵁ DZ)
    (t : ∀ z : Z, Γ(Z, 𝒩.opens z ⊓ DZ)ˣ) (y : Y) :
    unitsTrivTwistCochain r₁ r₂ 𝒞 𝒩 c h𝒞₁ h𝒞₂ DZ DY hDY₁ hDY₂ t y
      = Y.unitsRestrict (inf_le_left : 𝒞.opens y ⊓ DY ≤ 𝒞.opens y) (c y)
        * r₂.unitsAppLE (𝒩.opens (r₂.base y) ⊓ DZ) (𝒞.opens y ⊓ DY)
            (r₂.le_preimage_inf (inf_le_left.trans (h𝒞₂ y)) (inf_le_right.trans hDY₂))
            (t (r₂.base y))
        * (r₁.unitsAppLE (𝒩.opens (r₁.base y) ⊓ DZ) (𝒞.opens y ⊓ DY)
            (r₁.le_preimage_inf (inf_le_left.trans (h𝒞₁ y)) (inf_le_right.trans hDY₁))
            (t (r₁.base y)))⁻¹ :=
  rfl

/-- **The twisted values are Čech-compatible**: the witness relation (`hrel`, the (N1)
shape) restricted to the overlap is cancelled by the two pullbacks of the trivializing
relation (`htriv`). -/
theorem unitsTrivTwistCochain_compat (r₁ r₂ : Y ⟶ Z)
    (𝒞 : Y.PointedCover) (𝒩 : Z.PointedCover)
    (c : ∀ y : Y, Γ(Y, 𝒞.opens y)ˣ)
    (E : ∀ z z' : Z, Γ(Z, 𝒩.opens z ⊓ 𝒩.opens z')ˣ)
    (h𝒞₁ : ∀ y, 𝒞.opens y ≤ r₁ ⁻¹ᵁ 𝒩.opens (r₁.base y))
    (h𝒞₂ : ∀ y, 𝒞.opens y ≤ r₂ ⁻¹ᵁ 𝒩.opens (r₂.base y))
    (DZ : Z.Opens) (DY : Y.Opens)
    (hDY₁ : DY ≤ r₁ ⁻¹ᵁ DZ) (hDY₂ : DY ≤ r₂ ⁻¹ᵁ DZ)
    (t : ∀ z : Z, Γ(Z, 𝒩.opens z ⊓ DZ)ˣ)
    (hrel : ∀ x y : Y,
      Y.unitsRestrict (inf_le_left : 𝒞.opens x ⊓ 𝒞.opens y ≤ 𝒞.opens x) (c x)
          * r₁.unitsAppLE (𝒩.opens (r₁.base x) ⊓ 𝒩.opens (r₁.base y))
              (𝒞.opens x ⊓ 𝒞.opens y)
              (r₁.le_preimage_inf (inf_le_left.trans (h𝒞₁ x))
                (inf_le_right.trans (h𝒞₁ y)))
              (E (r₁.base x) (r₁.base y))
        = r₂.unitsAppLE (𝒩.opens (r₂.base x) ⊓ 𝒩.opens (r₂.base y))
              (𝒞.opens x ⊓ 𝒞.opens y)
              (r₂.le_preimage_inf (inf_le_left.trans (h𝒞₂ x))
                (inf_le_right.trans (h𝒞₂ y)))
              (E (r₂.base x) (r₂.base y))
          * Y.unitsRestrict inf_le_right (c y))
    (htriv : ∀ z z' : Z,
      Z.unitsRestrict (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          (𝒩.opens z ⊓ 𝒩.opens z') ⊓ DZ ≤ 𝒩.opens z ⊓ DZ) (t z)
          * Z.unitsRestrict (inf_le_left :
              (𝒩.opens z ⊓ 𝒩.opens z') ⊓ DZ ≤ 𝒩.opens z ⊓ 𝒩.opens z') (E z z')
        = Z.unitsRestrict (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
            (t z'))
    (y y' : Y) :
    Y.unitsRestrict (inf_le_left :
        (𝒞.opens y ⊓ DY) ⊓ (𝒞.opens y' ⊓ DY) ≤ 𝒞.opens y ⊓ DY)
        (unitsTrivTwistCochain r₁ r₂ 𝒞 𝒩 c h𝒞₁ h𝒞₂ DZ DY hDY₁ hDY₂ t y)
      = Y.unitsRestrict inf_le_right
          (unitsTrivTwistCochain r₁ r₂ 𝒞 𝒩 c h𝒞₁ h𝒞₂ DZ DY hDY₁ hDY₂ t y') := by
  set O : Y.Opens := (𝒞.opens y ⊓ DY) ⊓ (𝒞.opens y' ⊓ DY) with hO
  -- the witness relation restricted to `O`
  have h₂ := congrArg
    (Y.unitsRestrict (le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans inf_le_left) : O ≤ 𝒞.opens y ⊓ 𝒞.opens y')) (hrel y y')
  simp only [map_mul, Scheme.unitsRestrict_unitsRestrict,
    Scheme.Hom.unitsAppLE_map] at h₂
  -- the trivializing relation at `(r₁ y, r₁ y')`, pulled back along `r₁` onto `O`
  have t₁ := congrArg
    (r₁.unitsAppLE ((𝒩.opens (r₁.base y) ⊓ 𝒩.opens (r₁.base y')) ⊓ DZ) O
      (r₁.le_preimage_inf
        (r₁.le_preimage_inf ((inf_le_left.trans inf_le_left).trans (h𝒞₁ y))
          ((inf_le_right.trans inf_le_left).trans (h𝒞₁ y')))
        ((inf_le_left.trans inf_le_right).trans hDY₁)))
    (htriv (r₁.base y) (r₁.base y'))
  simp only [map_mul, Scheme.Hom.map_unitsAppLE] at t₁
  -- the trivializing relation at `(r₂ y, r₂ y')`, pulled back along `r₂` onto `O`
  have t₂ := congrArg
    (r₂.unitsAppLE ((𝒩.opens (r₂.base y) ⊓ 𝒩.opens (r₂.base y')) ⊓ DZ) O
      (r₂.le_preimage_inf
        (r₂.le_preimage_inf ((inf_le_left.trans inf_le_left).trans (h𝒞₂ y))
          ((inf_le_right.trans inf_le_left).trans (h𝒞₂ y')))
        ((inf_le_left.trans inf_le_right).trans hDY₂)))
    (htriv (r₂.base y) (r₂.base y'))
  simp only [map_mul, Scheme.Hom.map_unitsAppLE] at t₂
  -- expand the two twisted values and close with the telescope core
  rw [unitsTrivTwistCochain_def, unitsTrivTwistCochain_def]
  simp only [map_mul, map_inv, Scheme.unitsRestrict_unitsRestrict,
    Scheme.Hom.unitsAppLE_map]
  exact trivTwist_ratio_core h₂ t₁ t₂

/-- **The twisted values glue to a unit on the double piece `DY`** — the `𝒪ˣ`-sheaf
gluing over the trimmed cover `{𝒞.opens y ⊓ DY}` of `DY`. -/
theorem exists_glued_unitsTrivTwist (r₁ r₂ : Y ⟶ Z)
    (𝒞 : Y.PointedCover) (𝒩 : Z.PointedCover)
    (c : ∀ y : Y, Γ(Y, 𝒞.opens y)ˣ)
    (E : ∀ z z' : Z, Γ(Z, 𝒩.opens z ⊓ 𝒩.opens z')ˣ)
    (h𝒞₁ : ∀ y, 𝒞.opens y ≤ r₁ ⁻¹ᵁ 𝒩.opens (r₁.base y))
    (h𝒞₂ : ∀ y, 𝒞.opens y ≤ r₂ ⁻¹ᵁ 𝒩.opens (r₂.base y))
    (DZ : Z.Opens) (DY : Y.Opens)
    (hDY₁ : DY ≤ r₁ ⁻¹ᵁ DZ) (hDY₂ : DY ≤ r₂ ⁻¹ᵁ DZ)
    (t : ∀ z : Z, Γ(Z, 𝒩.opens z ⊓ DZ)ˣ)
    (hrel : ∀ x y : Y,
      Y.unitsRestrict (inf_le_left : 𝒞.opens x ⊓ 𝒞.opens y ≤ 𝒞.opens x) (c x)
          * r₁.unitsAppLE (𝒩.opens (r₁.base x) ⊓ 𝒩.opens (r₁.base y))
              (𝒞.opens x ⊓ 𝒞.opens y)
              (r₁.le_preimage_inf (inf_le_left.trans (h𝒞₁ x))
                (inf_le_right.trans (h𝒞₁ y)))
              (E (r₁.base x) (r₁.base y))
        = r₂.unitsAppLE (𝒩.opens (r₂.base x) ⊓ 𝒩.opens (r₂.base y))
              (𝒞.opens x ⊓ 𝒞.opens y)
              (r₂.le_preimage_inf (inf_le_left.trans (h𝒞₂ x))
                (inf_le_right.trans (h𝒞₂ y)))
              (E (r₂.base x) (r₂.base y))
          * Y.unitsRestrict inf_le_right (c y))
    (htriv : ∀ z z' : Z,
      Z.unitsRestrict (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          (𝒩.opens z ⊓ 𝒩.opens z') ⊓ DZ ≤ 𝒩.opens z ⊓ DZ) (t z)
          * Z.unitsRestrict (inf_le_left :
              (𝒩.opens z ⊓ 𝒩.opens z') ⊓ DZ ≤ 𝒩.opens z ⊓ 𝒩.opens z') (E z z')
        = Z.unitsRestrict (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
            (t z')) :
    ∃ v : Γ(Y, DY)ˣ, ∀ y : Y,
      Y.unitsRestrict (inf_le_right : 𝒞.opens y ⊓ DY ≤ DY) v
        = unitsTrivTwistCochain r₁ r₂ 𝒞 𝒩 c h𝒞₁ h𝒞₂ DZ DY hDY₁ hDY₂ t y :=
  Scheme.exists_unitsRestrict_eq (W := fun y : Y => 𝒞.opens y ⊓ DY)
    (fun _ => inf_le_right)
    (fun d hd => Opens.mem_iSup.mpr ⟨d, ⟨𝒞.mem_opens d, hd⟩⟩)
    (unitsTrivTwistCochain r₁ r₂ 𝒞 𝒩 c h𝒞₁ h𝒞₂ DZ DY hDY₁ hDY₂ t)
    (unitsTrivTwistCochain_compat r₁ r₂ 𝒞 𝒩 c E h𝒞₁ h𝒞₂ DZ DY hDY₁ hDY₂ t hrel htriv)

/-- **Pullback expansion of a glued twisted unit, in composite normal form**: for
`φ : X' ⟶ Y` and composites `φ ≫ r₁ = m₁`, `φ ≫ r₂ = m₂`, the `φ`-pullback of the glued
unit expands into the pulled witness value and the two `m`-pullbacks of the
trivialization — the workhorse for the diagonal normalization and the coherence of the
comparison unit.  All spelling changes happen here, over abstract schemes. -/
theorem Scheme.Hom.unitsAppLE_glued_trivTwist {X' : Scheme.{u}} (r₁ r₂ : Y ⟶ Z)
    (φ : X' ⟶ Y) (m₁ m₂ : X' ⟶ Z) (hm₁ : φ ≫ r₁ = m₁) (hm₂ : φ ≫ r₂ = m₂)
    (𝒞 : Y.PointedCover) (𝒩 : Z.PointedCover)
    (c : ∀ y : Y, Γ(Y, 𝒞.opens y)ˣ)
    (h𝒞₁ : ∀ y, 𝒞.opens y ≤ r₁ ⁻¹ᵁ 𝒩.opens (r₁.base y))
    (h𝒞₂ : ∀ y, 𝒞.opens y ≤ r₂ ⁻¹ᵁ 𝒩.opens (r₂.base y))
    (DZ : Z.Opens) (DY : Y.Opens)
    (hDY₁ : DY ≤ r₁ ⁻¹ᵁ DZ) (hDY₂ : DY ≤ r₂ ⁻¹ᵁ DZ)
    (t : ∀ z : Z, Γ(Z, 𝒩.opens z ⊓ DZ)ˣ)
    {v : Γ(Y, DY)ˣ}
    (hv : ∀ y : Y,
      Y.unitsRestrict (inf_le_right : 𝒞.opens y ⊓ DY ≤ DY) v
        = unitsTrivTwistCochain r₁ r₂ 𝒞 𝒩 c h𝒞₁ h𝒞₂ DZ DY hDY₁ hDY₂ t y)
    (x : X') {O : X'.Opens}
    (hO𝒞 : O ≤ φ ⁻¹ᵁ 𝒞.opens (φ.base x)) (hOD : O ≤ φ ⁻¹ᵁ DY)
    (e₂ : O ≤ m₂ ⁻¹ᵁ (𝒩.opens (m₂.base x) ⊓ DZ))
    (e₁ : O ≤ m₁ ⁻¹ᵁ (𝒩.opens (m₁.base x) ⊓ DZ)) :
    φ.unitsAppLE DY O hOD v
      = φ.unitsAppLE (𝒞.opens (φ.base x)) O hO𝒞 (c (φ.base x))
        * m₂.unitsAppLE (𝒩.opens (m₂.base x) ⊓ DZ) O e₂ (t (m₂.base x))
        * (m₁.unitsAppLE (𝒩.opens (m₁.base x) ⊓ DZ) O e₁ (t (m₁.base x)))⁻¹ := by
  subst hm₁ hm₂
  have h := congrArg
    (φ.unitsAppLE (𝒞.opens (φ.base x) ⊓ DY) O (φ.le_preimage_inf hO𝒞 hOD))
    (hv (φ.base x))
  rw [unitsTrivTwistCochain_def] at h
  simp only [map_mul, map_inv, Scheme.Hom.map_unitsAppLE,
    Scheme.unitsAppLE_unitsAppLE] at h
  exact h

end TrivTwist

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
local notation "u₁" => (C ◁ Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "u₂" => (C ◁ Over.overSpecMap (tensorInr (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "cg" => (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left
set_option quotPrecheck false in
local notation "cgq" =>
  (C ◁ Over.overSpecMap ((Algebra.ofId A (B ⊗[A] B)).restrictScalars k)).left

namespace Over

/-! ## The coprojections over the cover inclusions -/

/-- **The first coprojection lies over the cover inclusions**: `u₁ ≫ cg = cgq`. -/
lemma whiskerLeft_inl_comp_cover : (u₁) ≫ (cg) = (cgq) := by
  rw [← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← Over.overSpecMap_comp,
    tensorInl_comp_ofId_eq_ofId]

/-- **The second coprojection lies over the cover inclusions**: `u₂ ≫ cg = cgq`. -/
lemma whiskerLeft_inr_comp_cover : (u₂) ≫ (cg) = (cgq) := by
  rw [← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← Over.overSpecMap_comp,
    tensorInr_comp_ofId_eq_ofId]

/-- The double piece is bounded by the first-coprojection preimage of the piece. -/
lemma cgqPreimage_le_inl (V : (XA).Opens) :
    (cgq) ⁻¹ᵁ V ≤ (u₁) ⁻¹ᵁ ((cg) ⁻¹ᵁ V) :=
  le_of_eq (by rw [← Scheme.Hom.comp_preimage, whiskerLeft_inl_comp_cover])

/-- The double piece is bounded by the second-coprojection preimage of the piece. -/
lemma cgqPreimage_le_inr (V : (XA).Opens) :
    (cgq) ⁻¹ᵁ V ≤ (u₂) ⁻¹ᵁ ((cg) ⁻¹ᵁ V) :=
  le_of_eq (by rw [← Scheme.Hom.comp_preimage, whiskerLeft_inr_comp_cover])

/-! ## Piece trivializations -/

/-- **A piece trivialization** of a representing cocycle `γ` on a piece `V` of the base
curve: a trivializing `0`-cochain of `γ` on the `cg⁻¹ V`-trimmed opens of its cover —
the cochain witness that the class `CechPic.mk 𝒩 γ.class` of the (C2) setting is
trivial on the cover piece `cg⁻¹ V`.  The (C2) per-piece descent (bricks E2/E3) runs on
pieces equipped with such a datum; producing a covering family of them is the
piece-selection brick consumed by the final splice. -/
structure PieceTrivialization (𝒩 : (XB).PointedCover) (γ : (XB).unitsCocycle 𝒩)
    (V : (XA).Opens) : Type u where
  /-- The trivializing `0`-cochain on the trimmed opens `𝒩.opens b ⊓ cg⁻¹ V`. -/
  triv : ∀ b : XB, Γ(XB, 𝒩.opens b ⊓ (cg) ⁻¹ᵁ V)ˣ
  /-- `triv` trivializes `γ` on the piece: `t b ⋅ γ(b,b') = t b'` on the trimmed
  pairwise overlaps. -/
  triv_rel : ∀ b b' : XB,
    (XB).unitsRestrict (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        (𝒩.opens b ⊓ 𝒩.opens b') ⊓ (cg) ⁻¹ᵁ V ≤ 𝒩.opens b ⊓ (cg) ⁻¹ᵁ V) (triv b)
        * (XB).unitsRestrict (inf_le_left :
            (𝒩.opens b ⊓ 𝒩.opens b') ⊓ (cg) ⁻¹ᵁ V ≤ 𝒩.opens b ⊓ 𝒩.opens b')
            (Scheme.unitsEvInf γ b b')
      = (XB).unitsRestrict (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
          (triv b')

/-! ## The per-piece comparison unit -/

variable (σ : overSpec k A ⟶ C)

/-- **The per-piece comparison unit** ((C2) effectivity, brick E3): the single global
unit `v_V` of the double piece `Γ(X_{B⊗B}, cgq⁻¹ V)` glued from the values
`θ x ⋅ (u₂^♯ t)(x) / (u₁^♯ t)(x)` of the σ-normalized comparison `θ = W.θ` twisted by a
piece trivialization `t = T.triv` of the representing cocycle.  Under the E0/E2 ring
identification `Γ(X_{B⊗B}, cgq⁻¹ V) ≅ Γ(V) ⊗[A] (B ⊗[A] B)` it is the comparison unit
the per-piece descent datum of brick E2 consumes. -/
noncomputable def pieceComparisonUnit {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ) {V : (XA).Opens}
    (T : PieceTrivialization C 𝒩 γ V) :
    Γ(Xq, (cgq) ⁻¹ᵁ V)ˣ :=
  (exists_glued_unitsTrivTwist (u₁) (u₂) W.cover 𝒩 W.θ (Scheme.unitsEvInf γ)
    W.le_pullbackInl W.le_pullbackInr ((cg) ⁻¹ᵁ V) ((cgq) ⁻¹ᵁ V)
    (cgqPreimage_le_inl C V) (cgqPreimage_le_inr C V) T.triv
    W.witness T.triv_rel).choose

/-- **The defining property of the per-piece comparison unit**: on each member of the
trimmed comparison cover it restricts to the trivialization-twisted witness value. -/
lemma pieceComparisonUnit_spec {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ) {V : (XA).Opens}
    (T : PieceTrivialization C 𝒩 γ V) (x : Xq) :
    (Xq).unitsRestrict (inf_le_right : W.cover.opens x ⊓ (cgq) ⁻¹ᵁ V ≤ (cgq) ⁻¹ᵁ V)
        (pieceComparisonUnit C σ W T)
      = unitsTrivTwistCochain (u₁) (u₂) W.cover 𝒩 W.θ
          W.le_pullbackInl W.le_pullbackInr ((cg) ⁻¹ᵁ V) ((cgq) ⁻¹ᵁ V)
          (cgqPreimage_le_inl C V) (cgqPreimage_le_inr C V) T.triv x :=
  (exists_glued_unitsTrivTwist (u₁) (u₂) W.cover 𝒩 W.θ (Scheme.unitsEvInf γ)
    W.le_pullbackInl W.le_pullbackInr ((cg) ⁻¹ᵁ V) ((cgq) ⁻¹ᵁ V)
    (cgqPreimage_le_inl C V) (cgqPreimage_le_inr C V) T.triv
    W.witness T.triv_rel).choose_spec x

/-- **Uniqueness of the per-piece comparison unit**: any unit of the double piece with
the defining restriction property is the glued one — the separation half of the
`𝒪ˣ`-sheaf axiom.  This is what makes the per-piece descent data canonical (D2). -/
theorem pieceComparisonUnit_unique {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ) {V : (XA).Opens}
    (T : PieceTrivialization C 𝒩 γ V) (v : Γ(Xq, (cgq) ⁻¹ᵁ V)ˣ)
    (hv : ∀ x : Xq,
      (Xq).unitsRestrict (inf_le_right : W.cover.opens x ⊓ (cgq) ⁻¹ᵁ V ≤ (cgq) ⁻¹ᵁ V) v
        = unitsTrivTwistCochain (u₁) (u₂) W.cover 𝒩 W.θ
            W.le_pullbackInl W.le_pullbackInr ((cg) ⁻¹ᵁ V) ((cgq) ⁻¹ᵁ V)
            (cgqPreimage_le_inl C V) (cgqPreimage_le_inr C V) T.triv x) :
    v = pieceComparisonUnit C σ W T := by
  refine Scheme.unitsRestrict_eq_of_locally_eq
    (W := fun x : Xq => W.cover.opens x ⊓ (cgq) ⁻¹ᵁ V) (fun _ => inf_le_right)
    (fun d hd => Opens.mem_iSup.mpr ⟨d, ⟨W.cover.mem_opens d, hd⟩⟩) v
    (pieceComparisonUnit C σ W T) fun x => ?_
  rw [hv x, pieceComparisonUnit_spec C σ W T x]

end Over

end AlgebraicGeometry
