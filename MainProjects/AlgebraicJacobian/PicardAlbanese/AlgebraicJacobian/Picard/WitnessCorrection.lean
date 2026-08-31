/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.SpecDegeneracy
import AlgebraicJacobian.Picard.SectionsAlgebra

/-!
# The trivialization-corrected witness cochain and its gluing calculus (ζ2·ii, G5 core)

The point-indexed values `θ x` of an Amitsur-coherent Čech witness
(`AlgebraicGeometry.CoherentCechWitness`) do not glue over a basic open of the tensor
square: their coboundary is the comparison of the two pullback cocycles.  The ζ2·ii
pi-assembly therefore corrects them by cocycle values of `γ` anchored at the two
distinguished points of a trivializing basic cover — after which they do glue, and the
glued units satisfy the Amitsur cocycle identity and collapse onto the Zariski cover
cocycle on the diagonal.

This file develops that calculus over **abstract schemes** (kernel discipline: every
rewrite-heavy proof is elaborated once, over small types; the concrete instantiations on
the tensor towers in `AlgebraicJacobian.Picard.WitnessComponents` are single
applications).  Throughout, `r₁ r₂ : Y ⟶ Z` play the two coprojections
`Spec (B ⊗[A] B) ⟶ Spec B`, the pointed cover `𝒞`/cochain `c` play the witness
cover/cochain of `θ'`, `𝒩`/`γZ` the trivializing cover and unit cocycle on `Spec B`,
`a b : Z` two distinguished points (`pt i`, `pt j` of a basic refinement) and
`D : Y.Opens` the basic open `D((rᵢ ⊗ 1)(1 ⊗ rⱼ))`.

* `AlgebraicGeometry.unitsCorrCochain`: the corrected value
  `r₁^♯ γZ(a, r₁ y) ⋅ (c y)⁻¹ ⋅ r₂^♯ γZ(r₂ y, b)` on `𝒞.opens y ⊓ D`.  **Design note
  (the trivialization-correction):** the witness enters *inverted*, and the two
  correction factors are anchored `a → r₁ y` on the left and `r₂ y → b` on the right;
  this is the unique orientation for which the coboundary of the correction cancels the
  coboundary `r₂^♯γZ / r₁^♯γZ` of `θ⁻¹` (gluing), while on the diagonal — where the
  coherent witness is `1` (`unitsAppLE_eq_one_of_coherent`) — the two correction factors
  telescope to `γZ(a, b)`, the Zariski cover cocycle (G6).
* `AlgebraicGeometry.unitsCorrCochain_compat` / `exists_glued_unitsCorrCochain`: the
  corrected values agree on overlaps and glue to a unit on `D` (the `𝒪ˣ`-sheaf gluing of
  `AlgebraicJacobian.Picard.RefinementInjectivity`).
* `AlgebraicGeometry.Scheme.Hom.unitsAppLE_glued_corr`: pullback of a glued corrected
  unit along `φ : X' ⟶ Y` expands into its three factors along the composites `φ ≫ r₁`,
  `φ`, `φ ≫ r₂` — the workhorse for both identities below.
* `AlgebraicGeometry.unitsAppLE_eq_one_of_coherent`: pulling the Amitsur coherence back
  along a section `σ` of the `2,3`-coface (with `σ ≫ g₁₂ = δr`, `σ ≫ g₁₃ = 𝟙`) forces
  the `δr`-pullback of the witness to be `1`; `unitsAppLE_diag_eq_one_of_coherent`
  transports this along a common section `δ` of `r₁, r₂` — **Amitsur coherence is what
  normalizes the witness on the diagonal**.
* `AlgebraicGeometry.glued_corr_amitsur`: the glued corrected units satisfy the
  multiplicative Čech identity after pullback along three maps `g₂₃ g₁₂ g₁₃ : T ⟶ Y`
  with the simplicial coincidences — **Amitsur coherence enters the triple-product
  cocycle identity exactly here**, as the middle factor of the telescope; the correction
  factors cancel in pairs up to one diagonal value `γZ(b, b) = 1`.
* `AlgebraicGeometry.glued_corr_collapse`: along a common section `δ` of `r₁, r₂`, the
  glued corrected unit collapses onto the restricted cocycle value `γZ(a, b)`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-! ## Commutative-group telescope cores -/

/-- Telescope core for the gluing compatibility: corrected values at two points agree. -/
private lemma corr_ratio_core {G : Type u} [CommGroup G] {Ay Ay' Cy Cy' ty ty' Q₁ Q₂ : G}
    (h₁ : Ay * Q₁ = Ay') (h₂ : ty * Q₁ = Q₂ * ty') (h₃ : Q₂ * Cy' = Cy) :
    Ay * ty⁻¹ * Cy = Ay' * ty'⁻¹ * Cy' := by
  have hQ₂ : Q₂ = ty * Q₁ * ty'⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, h₂]
  subst hQ₂
  rw [← h₁, ← h₃]
  calc Ay * ty⁻¹ * (ty * Q₁ * ty'⁻¹ * Cy')
      = (ty⁻¹ * ty) * (Ay * Q₁ * ty'⁻¹ * Cy') := by ac_rfl
    _ = Ay * Q₁ * ty'⁻¹ * Cy' := by rw [inv_mul_cancel, one_mul]

/-- Telescope core for the Amitsur identity of the corrected units: the witness terms
combine by coherence, the correction factors cancel in pairs up to one diagonal value. -/
private lemma corr_amitsur_core {G : Type u} [CommGroup G] {Ea Eb Eb' Ec t₂₃ t₁₂ t₁₃ : G}
    (hcoh : t₂₃ * t₁₂ = t₁₃) (hdiag : Eb * Eb' = 1) :
    Eb * t₂₃⁻¹ * Ec * (Ea * t₁₂⁻¹ * Eb') = Ea * t₁₃⁻¹ * Ec := by
  have hb : Eb' = Eb⁻¹ := eq_inv_of_mul_eq_one_right hdiag
  subst hb
  rw [← hcoh, mul_inv_rev]
  calc Eb * t₂₃⁻¹ * Ec * (Ea * t₁₂⁻¹ * Eb⁻¹)
      = (Eb * Eb⁻¹) * (Ea * (t₁₂⁻¹ * t₂₃⁻¹) * Ec) := by ac_rfl
    _ = Ea * (t₁₂⁻¹ * t₂₃⁻¹) * Ec := by rw [mul_inv_cancel, one_mul]

/-! ## Composite-spelled pullback of a point-indexed section

`Scheme.unitsAppLE_unitsAppLE` restated with the source point, the open and the section
all spelled through the composite morphism, so that subsequent
`unitsAppLE_section_congr_hom` rewrites fire syntactically. -/

/-- Pullback along `φ` of a `g`-pullback of a point-indexed section, in composite normal
form. -/
lemma Scheme.Hom.unitsAppLE_comp_section {X' Y Z' : Scheme.{u}} (φ : X' ⟶ Y) (g : Y ⟶ Z')
    (V' : Z' → Z'.Opens) (s : ∀ z, Γ(Z', V' z)ˣ) {V : Y.Opens} {O : X'.Opens}
    (e : O ≤ φ ⁻¹ᵁ V) (x : X') (eg : V ≤ g ⁻¹ᵁ V' (g.base (φ.base x))) :
    φ.unitsAppLE V O e
        (g.unitsAppLE (V' (g.base (φ.base x))) V eg (s (g.base (φ.base x))))
      = (φ ≫ g).unitsAppLE (V' ((φ ≫ g).base x)) O
          (e.trans (φ.preimage_mono eg)) (s ((φ ≫ g).base x)) :=
  Scheme.unitsAppLE_unitsAppLE φ g eg e (s (g.base (φ.base x)))

/-! ## The corrected witness cochain and its gluing -/

section Corrected

variable {Y Z : Scheme.{u}} (r₁ r₂ : Y ⟶ Z)
variable (𝒞 : Y.PointedCover) (𝒩 : Z.PointedCover)
variable (c : ∀ y : Y, Γ(Y, 𝒞.opens y)ˣ) (γZ : Z.unitsCocycle 𝒩)
variable (h𝒞₁ : ∀ y, 𝒞.opens y ≤ r₁ ⁻¹ᵁ 𝒩.opens (r₁.base y))
variable (h𝒞₂ : ∀ y, 𝒞.opens y ≤ r₂ ⁻¹ᵁ 𝒩.opens (r₂.base y))
variable (a b : Z) (D : Y.Opens)
variable (hDa : D ≤ r₁ ⁻¹ᵁ 𝒩.opens a) (hDb : D ≤ r₂ ⁻¹ᵁ 𝒩.opens b)

/-- The **corrected witness value** at a point `y`, on `𝒞.opens y ⊓ D`:
`r₁^♯ γZ(a, r₁ y) ⋅ (c y)⁻¹ ⋅ r₂^♯ γZ(r₂ y, b)`.  See the module docstring for why this
is the unique orientation making the values glue over `D` and collapse onto `γZ(a, b)`
on the diagonal. -/
noncomputable def unitsCorrCochain (y : Y) : Γ(Y, 𝒞.opens y ⊓ D)ˣ :=
  r₁.unitsAppLE (𝒩.opens a ⊓ 𝒩.opens (r₁.base y)) (𝒞.opens y ⊓ D)
      (r₁.le_preimage_inf (inf_le_right.trans hDa) (inf_le_left.trans (h𝒞₁ y)))
      (Scheme.unitsEvInf γZ a (r₁.base y))
    * (Y.unitsRestrict (inf_le_left : 𝒞.opens y ⊓ D ≤ 𝒞.opens y) (c y))⁻¹
    * r₂.unitsAppLE (𝒩.opens (r₂.base y) ⊓ 𝒩.opens b) (𝒞.opens y ⊓ D)
      (r₂.le_preimage_inf (inf_le_left.trans (h𝒞₂ y)) (inf_le_right.trans hDb))
      (Scheme.unitsEvInf γZ (r₂.base y) b)

lemma unitsCorrCochain_def (y : Y) :
    unitsCorrCochain r₁ r₂ 𝒞 𝒩 c γZ h𝒞₁ h𝒞₂ a b D hDa hDb y
      = r₁.unitsAppLE (𝒩.opens a ⊓ 𝒩.opens (r₁.base y)) (𝒞.opens y ⊓ D)
          (r₁.le_preimage_inf (inf_le_right.trans hDa) (inf_le_left.trans (h𝒞₁ y)))
          (Scheme.unitsEvInf γZ a (r₁.base y))
        * (Y.unitsRestrict (inf_le_left : 𝒞.opens y ⊓ D ≤ 𝒞.opens y) (c y))⁻¹
        * r₂.unitsAppLE (𝒩.opens (r₂.base y) ⊓ 𝒩.opens b) (𝒞.opens y ⊓ D)
          (r₂.le_preimage_inf (inf_le_left.trans (h𝒞₂ y)) (inf_le_right.trans hDb))
          (Scheme.unitsEvInf γZ (r₂.base y) b) :=
  rfl

/-- **The corrected values are Čech-compatible**: the coboundary of the correction
factors cancels the coboundary of the inverted witness (via the witness relation `hrel`
and the cocycle identity of `γZ` pulled back along `r₁` and `r₂`). -/
theorem unitsCorrCochain_compat
    (hrel : ∀ x y : Y,
      Y.unitsRestrict (inf_le_left : 𝒞.opens x ⊓ 𝒞.opens y ≤ 𝒞.opens x) (c x)
          * r₁.unitsAppLE (𝒩.opens (r₁.base x) ⊓ 𝒩.opens (r₁.base y))
              (𝒞.opens x ⊓ 𝒞.opens y)
              (r₁.le_preimage_inf (inf_le_left.trans (h𝒞₁ x))
                (inf_le_right.trans (h𝒞₁ y)))
              (Scheme.unitsEvInf γZ (r₁.base x) (r₁.base y))
        = r₂.unitsAppLE (𝒩.opens (r₂.base x) ⊓ 𝒩.opens (r₂.base y))
              (𝒞.opens x ⊓ 𝒞.opens y)
              (r₂.le_preimage_inf (inf_le_left.trans (h𝒞₂ x))
                (inf_le_right.trans (h𝒞₂ y)))
              (Scheme.unitsEvInf γZ (r₂.base x) (r₂.base y))
          * Y.unitsRestrict inf_le_right (c y))
    (y y' : Y) :
    Y.unitsRestrict (inf_le_left :
        (𝒞.opens y ⊓ D) ⊓ (𝒞.opens y' ⊓ D) ≤ 𝒞.opens y ⊓ D)
        (unitsCorrCochain r₁ r₂ 𝒞 𝒩 c γZ h𝒞₁ h𝒞₂ a b D hDa hDb y)
      = Y.unitsRestrict inf_le_right
          (unitsCorrCochain r₁ r₂ 𝒞 𝒩 c γZ h𝒞₁ h𝒞₂ a b D hDa hDb y') := by
  set O : Y.Opens := (𝒞.opens y ⊓ D) ⊓ (𝒞.opens y' ⊓ D) with hO
  -- the witness relation restricted to `O`
  have h₂ := congrArg
    (Y.unitsRestrict (le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans inf_le_left) : O ≤ 𝒞.opens y ⊓ 𝒞.opens y')) (hrel y y')
  simp only [map_mul, Scheme.unitsRestrict_unitsRestrict,
    Scheme.Hom.unitsAppLE_map] at h₂
  -- the cocycle identity of `γZ` at `(a, r₁ y, r₁ y')`, pulled back along `r₁` onto `O`
  have t₁ := congrArg
    (r₁.unitsAppLE (𝒩.opens a ⊓ 𝒩.opens (r₁.base y) ⊓ 𝒩.opens (r₁.base y')) O
      (r₁.le_preimage_inf
        (r₁.le_preimage_inf (inf_le_left.trans (inf_le_right.trans hDa))
          (inf_le_left.trans (inf_le_left.trans (h𝒞₁ y))))
        (inf_le_right.trans (inf_le_left.trans (h𝒞₁ y')))))
    (Scheme.unitsEvInf_trans γZ a (r₁.base y) (r₁.base y'))
  simp only [map_mul, Scheme.Hom.map_unitsAppLE] at t₁
  -- the cocycle identity of `γZ` at `(r₂ y, r₂ y', b)`, pulled back along `r₂` onto `O`
  have t₂ := congrArg
    (r₂.unitsAppLE (𝒩.opens (r₂.base y) ⊓ 𝒩.opens (r₂.base y') ⊓ 𝒩.opens b) O
      (r₂.le_preimage_inf
        (r₂.le_preimage_inf (inf_le_left.trans (inf_le_left.trans (h𝒞₂ y)))
          (inf_le_right.trans (inf_le_left.trans (h𝒞₂ y'))))
        (inf_le_left.trans (inf_le_right.trans hDb))))
    (Scheme.unitsEvInf_trans γZ (r₂.base y) (r₂.base y') b)
  simp only [map_mul, Scheme.Hom.map_unitsAppLE] at t₂
  -- expand the two corrected values and close with the telescope core
  rw [unitsCorrCochain_def, unitsCorrCochain_def]
  simp only [map_mul, map_inv, Scheme.unitsRestrict_unitsRestrict,
    Scheme.Hom.unitsAppLE_map]
  exact corr_ratio_core t₁ h₂ t₂

/-- **The corrected values glue to a unit on `D`** — the `𝒪ˣ`-sheaf gluing over the
cover `{𝒞.opens y ⊓ D}` of `D`. -/
theorem exists_glued_unitsCorrCochain
    (hrel : ∀ x y : Y,
      Y.unitsRestrict (inf_le_left : 𝒞.opens x ⊓ 𝒞.opens y ≤ 𝒞.opens x) (c x)
          * r₁.unitsAppLE (𝒩.opens (r₁.base x) ⊓ 𝒩.opens (r₁.base y))
              (𝒞.opens x ⊓ 𝒞.opens y)
              (r₁.le_preimage_inf (inf_le_left.trans (h𝒞₁ x))
                (inf_le_right.trans (h𝒞₁ y)))
              (Scheme.unitsEvInf γZ (r₁.base x) (r₁.base y))
        = r₂.unitsAppLE (𝒩.opens (r₂.base x) ⊓ 𝒩.opens (r₂.base y))
              (𝒞.opens x ⊓ 𝒞.opens y)
              (r₂.le_preimage_inf (inf_le_left.trans (h𝒞₂ x))
                (inf_le_right.trans (h𝒞₂ y)))
              (Scheme.unitsEvInf γZ (r₂.base x) (r₂.base y))
          * Y.unitsRestrict inf_le_right (c y)) :
    ∃ u : Γ(Y, D)ˣ, ∀ y : Y,
      Y.unitsRestrict (inf_le_right : 𝒞.opens y ⊓ D ≤ D) u
        = unitsCorrCochain r₁ r₂ 𝒞 𝒩 c γZ h𝒞₁ h𝒞₂ a b D hDa hDb y :=
  Scheme.exists_unitsRestrict_eq (W := fun y : Y => 𝒞.opens y ⊓ D)
    (fun _ => inf_le_right)
    (fun d hd => Opens.mem_iSup.mpr ⟨d, ⟨𝒞.mem_opens d, hd⟩⟩)
    (unitsCorrCochain r₁ r₂ 𝒞 𝒩 c γZ h𝒞₁ h𝒞₂ a b D hDa hDb)
    (unitsCorrCochain_compat r₁ r₂ 𝒞 𝒩 c γZ h𝒞₁ h𝒞₂ a b D hDa hDb hrel)

/-- **Pullback expansion of a glued corrected unit**: for `φ : X' ⟶ Y` and any open `O`
inside `φ ⁻¹ᵁ (𝒞.opens (φ x) ⊓ D)`, the `φ`-pullback of a glued unit expands into its
three factors, with the correction factors pulled back along the composites `φ ≫ r₁`,
`φ ≫ r₂` — the normal form on which the simplicial coincidences can be rewritten. -/
theorem Scheme.Hom.unitsAppLE_glued_corr {X' : Scheme.{u}} (φ : X' ⟶ Y)
    {u : Γ(Y, D)ˣ}
    (hu : ∀ y : Y,
      Y.unitsRestrict (inf_le_right : 𝒞.opens y ⊓ D ≤ D) u
        = unitsCorrCochain r₁ r₂ 𝒞 𝒩 c γZ h𝒞₁ h𝒞₂ a b D hDa hDb y)
    (x : X') {O : X'.Opens}
    (hO𝒞 : O ≤ φ ⁻¹ᵁ 𝒞.opens (φ.base x)) (hOD : O ≤ φ ⁻¹ᵁ D) :
    φ.unitsAppLE D O hOD u
      = (φ ≫ r₁).unitsAppLE (𝒩.opens a ⊓ 𝒩.opens ((φ ≫ r₁).base x)) O
            ((φ.le_preimage_inf hO𝒞 hOD).trans (φ.preimage_mono
              (r₁.le_preimage_inf (inf_le_right.trans hDa)
                (inf_le_left.trans (h𝒞₁ (φ.base x))))))
            (Scheme.unitsEvInf γZ a ((φ ≫ r₁).base x))
        * (φ.unitsAppLE (𝒞.opens (φ.base x)) O hO𝒞 (c (φ.base x)))⁻¹
        * (φ ≫ r₂).unitsAppLE (𝒩.opens ((φ ≫ r₂).base x) ⊓ 𝒩.opens b) O
            ((φ.le_preimage_inf hO𝒞 hOD).trans (φ.preimage_mono
              (r₂.le_preimage_inf (inf_le_left.trans (h𝒞₂ (φ.base x)))
                (inf_le_right.trans hDb))))
            (Scheme.unitsEvInf γZ ((φ ≫ r₂).base x) b) := by
  have h := congrArg
    (φ.unitsAppLE (𝒞.opens (φ.base x) ⊓ D) O (φ.le_preimage_inf hO𝒞 hOD))
    (hu (φ.base x))
  rw [unitsCorrCochain_def] at h
  simp only [map_mul, map_inv, Scheme.Hom.map_unitsAppLE,
    Scheme.unitsAppLE_unitsAppLE] at h
  exact h

end Corrected

/-! ## Diagonal triviality of a coherent witness -/

/-- **Pulling the coherence back along a section of the `2,3`-coface kills the witness
along the degeneracy `δr`.**  For `σ : Y ⟶ T` with `σ ≫ g₂₃ = 𝟙 Y`, `σ ≫ g₁₂ = δr` and
`σ ≫ g₁₃ = 𝟙 Y`, the Amitsur relation `(g₂₃^♯ c) ⋅ (g₁₂^♯ c) = g₁₃^♯ c` pulls back to
`c ⋅ δr^♯ c = c`, so the `δr`-pullback of the witness is `1`. -/
theorem unitsAppLE_eq_one_of_coherent {T Y : Scheme.{u}}
    (g₂₃ g₁₂ g₁₃ : T ⟶ Y) (σ : Y ⟶ T) (δr : Y ⟶ Y)
    (hσ₂₃ : σ ≫ g₂₃ = 𝟙 Y) (hσ₁₂ : σ ≫ g₁₂ = δr) (hσ₁₃ : σ ≫ g₁₃ = 𝟙 Y)
    (𝒞 : Y.PointedCover) (c : ∀ y : Y, Γ(Y, 𝒞.opens y)ˣ)
    (hcoh : ∀ z : T,
      g₂₃.unitsAppLE (𝒞.opens (g₂₃.base z))
          (((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens z)
          (inf_le_left.trans inf_le_left) (c (g₂₃.base z))
        * g₁₂.unitsAppLE (𝒞.opens (g₁₂.base z))
            (((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens z)
            (inf_le_left.trans inf_le_right) (c (g₁₂.base z))
      = g₁₃.unitsAppLE (𝒞.opens (g₁₃.base z))
          (((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens z)
          inf_le_right (c (g₁₃.base z)))
    (y : Y) {O : Y.Opens}
    (hO₁ : O ≤ 𝒞.opens y) (hO₂ : O ≤ δr ⁻¹ᵁ 𝒞.opens (δr.base y)) :
    δr.unitsAppLE (𝒞.opens (δr.base y)) O hO₂ (c (δr.base y)) = 1 := by
  -- `O` sits inside the `σ`-preimage of the Amitsur cover member at `σ y`
  have e₂₃ : O ≤ (σ ≫ g₂₃) ⁻¹ᵁ 𝒞.opens ((σ ≫ g₂₃).base y) := by
    rw [hσ₂₃]; exact hO₁
  have e₁₂ : O ≤ (σ ≫ g₁₂) ⁻¹ᵁ 𝒞.opens ((σ ≫ g₁₂).base y) := by
    rw [hσ₁₂]; exact hO₂
  have e₁₃ : O ≤ (σ ≫ g₁₃) ⁻¹ᵁ 𝒞.opens ((σ ≫ g₁₃).base y) := by
    rw [hσ₁₃]; exact hO₁
  have hOσ : O ≤ σ ⁻¹ᵁ
      (((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens (σ.base y)) :=
    σ.le_preimage_inf (σ.le_preimage_inf e₂₃ e₁₂) e₁₃
  -- pull the coherence at `σ y` back onto `O` and collapse the three composites
  have h := congrArg
    (σ.unitsAppLE
      (((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens (σ.base y)) O hOσ)
    (hcoh (σ.base y))
  rw [map_mul,
    Scheme.Hom.unitsAppLE_comp_section σ g₂₃ 𝒞.opens c hOσ y
      (inf_le_left.trans inf_le_left),
    Scheme.Hom.unitsAppLE_comp_section σ g₁₂ 𝒞.opens c hOσ y
      (inf_le_left.trans inf_le_right),
    Scheme.Hom.unitsAppLE_comp_section σ g₁₃ 𝒞.opens c hOσ y inf_le_right,
    Scheme.Hom.unitsAppLE_section_congr_hom hσ₂₃ 𝒞.opens c y,
    Scheme.Hom.unitsAppLE_section_congr_hom hσ₁₂ 𝒞.opens c y,
    Scheme.Hom.unitsAppLE_section_congr_hom hσ₁₃ 𝒞.opens c y,
    Scheme.id_unitsAppLE] at h
  exact mul_left_cancel (h.trans (mul_one _).symm)

/-- Transport of `unitsAppLE_eq_one_of_coherent` along a common section `δ` of the two
coprojections: the `δ`-pullback of a coherent witness is `1`.  (`δ ≫ δr = δ` holds
whenever `δ ≫ r₁ = 𝟙` and `δr = r₁ ≫ δ`.) -/
theorem unitsAppLE_diag_eq_one_of_coherent {Y Z : Scheme.{u}}
    (δ : Z ⟶ Y) (δr : Y ⟶ Y) (hδδr : δ ≫ δr = δ)
    (𝒞 : Y.PointedCover) (c : ∀ y : Y, Γ(Y, 𝒞.opens y)ˣ)
    (hδr : ∀ (y : Y) {O : Y.Opens}, O ≤ 𝒞.opens y →
      ∀ hO₂ : O ≤ δr ⁻¹ᵁ 𝒞.opens (δr.base y),
      δr.unitsAppLE (𝒞.opens (δr.base y)) O hO₂ (c (δr.base y)) = 1)
    (v : Z) {O : Z.Opens} (hO : O ≤ δ ⁻¹ᵁ 𝒞.opens (δ.base v)) :
    δ.unitsAppLE (𝒞.opens (δ.base v)) O hO (c (δ.base v)) = 1 := by
  have h₂ : O ≤ δ ⁻¹ᵁ (δr ⁻¹ᵁ 𝒞.opens (δr.base (δ.base v))) := by
    change O ≤ (δ ≫ δr) ⁻¹ᵁ 𝒞.opens ((δ ≫ δr).base v)
    rw [hδδr]; exact hO
  have h₂' : O ≤ δ ⁻¹ᵁ
      (𝒞.opens (δ.base v) ⊓ δr ⁻¹ᵁ 𝒞.opens (δr.base (δ.base v))) :=
    δ.le_preimage_inf hO h₂
  have h := congrArg
    (δ.unitsAppLE (𝒞.opens (δ.base v) ⊓ δr ⁻¹ᵁ 𝒞.opens (δr.base (δ.base v))) O h₂')
    (hδr (δ.base v) (inf_le_left :
        𝒞.opens (δ.base v) ⊓ δr ⁻¹ᵁ 𝒞.opens (δr.base (δ.base v)) ≤ 𝒞.opens (δ.base v))
      inf_le_right)
  rw [map_one,
    Scheme.Hom.unitsAppLE_comp_section δ δr 𝒞.opens c h₂' v inf_le_right,
    Scheme.Hom.unitsAppLE_section_congr_hom hδδr 𝒞.opens c v] at h
  exact h

/-! ## The Amitsur identity and the diagonal collapse of the glued units -/

section Glued

variable {T Y Z : Scheme.{u}}
variable (g₂₃ g₁₂ g₁₃ : T ⟶ Y) (r₁ r₂ : Y ⟶ Z)
variable (𝒞 : Y.PointedCover) (𝒩 : Z.PointedCover)
variable (c : ∀ y : Y, Γ(Y, 𝒞.opens y)ˣ) (γZ : Z.unitsCocycle 𝒩)
variable (h𝒞₁ : ∀ y, 𝒞.opens y ≤ r₁ ⁻¹ᵁ 𝒩.opens (r₁.base y))
variable (h𝒞₂ : ∀ y, 𝒞.opens y ≤ r₂ ⁻¹ᵁ 𝒩.opens (r₂.base y))

/-- **The glued corrected units satisfy the Amitsur cocycle identity** (ζ2·ii, the
triple-product identity).  Given the three simplicial coincidences
`g₂₃ ≫ r₁ = g₁₂ ≫ r₂`, `g₁₃ ≫ r₁ = g₁₂ ≫ r₁`, `g₂₃ ≫ r₂ = g₁₃ ≫ r₂` and the Amitsur
coherence of the witness, the pullbacks of the three glued corrected units — for the
point pairs `(b, c')`, `(a, b)`, `(a, c')` on opens `D₂₃, D₁₂, D₁₃` — satisfy
`g₂₃^♯ u₂₃ ⋅ g₁₂^♯ u₁₂ = g₁₃^♯ u₁₃` on any `DT` inside the three preimages. -/
theorem glued_corr_amitsur
    (hc₁ : g₁₃ ≫ r₁ = g₁₂ ≫ r₁) (hc₂ : g₂₃ ≫ r₁ = g₁₂ ≫ r₂)
    (hc₃ : g₂₃ ≫ r₂ = g₁₃ ≫ r₂)
    (hcoh : ∀ z : T,
      g₂₃.unitsAppLE (𝒞.opens (g₂₃.base z))
          (((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens z)
          (inf_le_left.trans inf_le_left) (c (g₂₃.base z))
        * g₁₂.unitsAppLE (𝒞.opens (g₁₂.base z))
            (((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens z)
            (inf_le_left.trans inf_le_right) (c (g₁₂.base z))
      = g₁₃.unitsAppLE (𝒞.opens (g₁₃.base z))
          (((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens z)
          inf_le_right (c (g₁₃.base z)))
    (a b c' : Z) (D₂₃ D₁₂ D₁₃ : Y.Opens)
    (hD₂₃a : D₂₃ ≤ r₁ ⁻¹ᵁ 𝒩.opens b) (hD₂₃b : D₂₃ ≤ r₂ ⁻¹ᵁ 𝒩.opens c')
    (hD₁₂a : D₁₂ ≤ r₁ ⁻¹ᵁ 𝒩.opens a) (hD₁₂b : D₁₂ ≤ r₂ ⁻¹ᵁ 𝒩.opens b)
    (hD₁₃a : D₁₃ ≤ r₁ ⁻¹ᵁ 𝒩.opens a) (hD₁₃b : D₁₃ ≤ r₂ ⁻¹ᵁ 𝒩.opens c')
    {u₂₃ : Γ(Y, D₂₃)ˣ} {u₁₂ : Γ(Y, D₁₂)ˣ} {u₁₃ : Γ(Y, D₁₃)ˣ}
    (hu₂₃ : ∀ y : Y, Y.unitsRestrict (inf_le_right : 𝒞.opens y ⊓ D₂₃ ≤ D₂₃) u₂₃
      = unitsCorrCochain r₁ r₂ 𝒞 𝒩 c γZ h𝒞₁ h𝒞₂ b c' D₂₃ hD₂₃a hD₂₃b y)
    (hu₁₂ : ∀ y : Y, Y.unitsRestrict (inf_le_right : 𝒞.opens y ⊓ D₁₂ ≤ D₁₂) u₁₂
      = unitsCorrCochain r₁ r₂ 𝒞 𝒩 c γZ h𝒞₁ h𝒞₂ a b D₁₂ hD₁₂a hD₁₂b y)
    (hu₁₃ : ∀ y : Y, Y.unitsRestrict (inf_le_right : 𝒞.opens y ⊓ D₁₃ ≤ D₁₃) u₁₃
      = unitsCorrCochain r₁ r₂ 𝒞 𝒩 c γZ h𝒞₁ h𝒞₂ a c' D₁₃ hD₁₃a hD₁₃b y)
    {DT : T.Opens}
    (hT₂₃ : DT ≤ g₂₃ ⁻¹ᵁ D₂₃) (hT₁₂ : DT ≤ g₁₂ ⁻¹ᵁ D₁₂) (hT₁₃ : DT ≤ g₁₃ ⁻¹ᵁ D₁₃) :
    g₂₃.unitsAppLE D₂₃ DT hT₂₃ u₂₃ * g₁₂.unitsAppLE D₁₂ DT hT₁₂ u₁₂
      = g₁₃.unitsAppLE D₁₃ DT hT₁₃ u₁₃ := by
  -- separation: check the identity on each member of the cover `{𝒜 z ⊓ DT}` of `DT`
  apply Scheme.unitsRestrict_eq_of_locally_eq
    (W := fun z : T =>
      ((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens z ⊓ DT)
    (fun _ => inf_le_right)
    (fun d hd => Opens.mem_iSup.mpr
      ⟨d, ⟨((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).mem_opens d, hd⟩⟩)
  intro z
  have hz₂₃ : ((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens z ⊓ DT
      ≤ g₂₃ ⁻¹ᵁ 𝒞.opens (g₂₃.base z) :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hz₁₂ : ((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens z ⊓ DT
      ≤ g₁₂ ⁻¹ᵁ 𝒞.opens (g₁₂.base z) :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hz₁₃ : ((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens z ⊓ DT
      ≤ g₁₃ ⁻¹ᵁ 𝒞.opens (g₁₃.base z) :=
    inf_le_left.trans inf_le_right
  -- push the restriction into the product and expand the three glued units
  rw [map_mul, Scheme.Hom.unitsAppLE_map, Scheme.Hom.unitsAppLE_map,
    Scheme.Hom.unitsAppLE_map,
    Scheme.Hom.unitsAppLE_glued_corr r₁ r₂ 𝒞 𝒩 c γZ h𝒞₁ h𝒞₂ b c' D₂₃ hD₂₃a hD₂₃b g₂₃
      hu₂₃ z hz₂₃ (inf_le_right.trans hT₂₃),
    Scheme.Hom.unitsAppLE_glued_corr r₁ r₂ 𝒞 𝒩 c γZ h𝒞₁ h𝒞₂ a b D₁₂ hD₁₂a hD₁₂b g₁₂
      hu₁₂ z hz₁₂ (inf_le_right.trans hT₁₂),
    Scheme.Hom.unitsAppLE_glued_corr r₁ r₂ 𝒞 𝒩 c γZ h𝒞₁ h𝒞₂ a c' D₁₃ hD₁₃a hD₁₃b g₁₃
      hu₁₃ z hz₁₃ (inf_le_right.trans hT₁₃),
    -- collapse the six composite pullbacks onto the three insertions
    Scheme.Hom.unitsAppLE_section_congr_hom hc₂
      (fun z' => 𝒩.opens b ⊓ 𝒩.opens z') (fun z' => Scheme.unitsEvInf γZ b z') z,
    Scheme.Hom.unitsAppLE_section_congr_hom hc₃
      (fun z' => 𝒩.opens z' ⊓ 𝒩.opens c') (fun z' => Scheme.unitsEvInf γZ z' c') z,
    Scheme.Hom.unitsAppLE_section_congr_hom hc₁
      (fun z' => 𝒩.opens a ⊓ 𝒩.opens z') (fun z' => Scheme.unitsEvInf γZ a z') z]
  -- the coherence relation restricted to `O`
  have hcohO := congrArg
    (T.unitsRestrict (inf_le_left :
      ((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens z ⊓ DT
        ≤ ((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens z)) (hcoh z)
  simp only [map_mul, Scheme.Hom.unitsAppLE_map] at hcohO
  -- the paired correction factors telescope to the diagonal value `γZ(b, b) = 1`
  have hOb : ((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens z ⊓ DT
      ≤ (g₁₂ ≫ r₂) ⁻¹ᵁ 𝒩.opens b :=
    (inf_le_right.trans hT₁₂).trans (g₁₂.preimage_mono hD₁₂b)
  have hObz : ((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens z ⊓ DT
      ≤ (g₁₂ ≫ r₂) ⁻¹ᵁ 𝒩.opens ((g₁₂ ≫ r₂).base z) :=
    hz₁₂.trans (g₁₂.preimage_mono (h𝒞₂ (g₁₂.base z)))
  have td := congrArg
    ((g₁₂ ≫ r₂).unitsAppLE
      (𝒩.opens b ⊓ 𝒩.opens ((g₁₂ ≫ r₂).base z) ⊓ 𝒩.opens b)
      (((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens z ⊓ DT)
      ((g₁₂ ≫ r₂).le_preimage_inf ((g₁₂ ≫ r₂).le_preimage_inf hOb hObz) hOb))
    (Scheme.unitsEvInf_trans γZ b ((g₁₂ ≫ r₂).base z) b)
  simp only [map_mul, Scheme.Hom.map_unitsAppLE] at td
  have hone : (g₁₂ ≫ r₂).unitsAppLE (𝒩.opens b ⊓ 𝒩.opens b)
      (((𝒞.pullback g₂₃ ⊓ 𝒞.pullback g₁₂) ⊓ 𝒞.pullback g₁₃).opens z ⊓ DT)
      ((g₁₂ ≫ r₂).le_preimage_inf hOb hOb) (Scheme.unitsEvInf γZ b b) = 1 := by
    have h := Scheme.Hom.map_unitsAppLE (f := g₁₂ ≫ r₂) (V := 𝒩.opens b) hOb
      ((homOfLE (le_inf le_rfl le_rfl : 𝒩.opens b ≤ 𝒩.opens b ⊓ 𝒩.opens b)).op)
      (Scheme.unitsEvInf γZ b b)
    have hone1 : Z.unitsRestrict
        (le_inf le_rfl le_rfl : 𝒩.opens b ≤ 𝒩.opens b ⊓ 𝒩.opens b)
        (Scheme.unitsEvInf γZ b b) = 1 :=
      Scheme.unitsRestrict_unitsEvInf_self γZ b le_rfl
    rw [hone1, map_one] at h
    exact h.symm
  exact corr_amitsur_core hcohO (td.trans hone)

/-- **The glued corrected unit collapses onto the cocycle value on the diagonal**
(ζ2·ii, the G6 component identity).  Along a common section `δ` of `r₁, r₂` on which the
witness is `1`, the pullback of the glued corrected unit for the pair `(a, b)` is the
restriction of `γZ(a, b)` — the Zariski cover cocycle value. -/
theorem glued_corr_collapse (δ : Z ⟶ Y)
    (hδ₁ : δ ≫ r₁ = 𝟙 Z) (hδ₂ : δ ≫ r₂ = 𝟙 Z)
    (hθdiag : ∀ (v : Z) {O : Z.Opens} (hO : O ≤ δ ⁻¹ᵁ 𝒞.opens (δ.base v)),
      δ.unitsAppLE (𝒞.opens (δ.base v)) O hO (c (δ.base v)) = 1)
    (a b : Z) (D : Y.Opens)
    (hDa : D ≤ r₁ ⁻¹ᵁ 𝒩.opens a) (hDb : D ≤ r₂ ⁻¹ᵁ 𝒩.opens b)
    {u : Γ(Y, D)ˣ}
    (hu : ∀ y : Y, Y.unitsRestrict (inf_le_right : 𝒞.opens y ⊓ D ≤ D) u
      = unitsCorrCochain r₁ r₂ 𝒞 𝒩 c γZ h𝒞₁ h𝒞₂ a b D hDa hDb y)
    {E : Z.Opens} (hE : E ≤ δ ⁻¹ᵁ D) (hEa : E ≤ 𝒩.opens a) (hEb : E ≤ 𝒩.opens b) :
    δ.unitsAppLE D E hE u
      = Z.unitsRestrict (le_inf hEa hEb) (Scheme.unitsEvInf γZ a b) := by
  -- separation over the cover `{δ ⁻¹ᵁ 𝒞 (δ v) ⊓ E}` of `E`
  apply Scheme.unitsRestrict_eq_of_locally_eq
    (W := fun v : Z => δ ⁻¹ᵁ 𝒞.opens (δ.base v) ⊓ E)
    (fun _ => inf_le_right)
    (fun d hd => Opens.mem_iSup.mpr ⟨d, ⟨𝒞.mem_opens (δ.base d), hd⟩⟩)
  intro v
  -- `δ ⁻¹ᵁ 𝒞 (δ v) ⊓ E` sits inside the member `𝒩 v` (through `δ ≫ r₁ = 𝟙`)
  have hOv : δ ⁻¹ᵁ 𝒞.opens (δ.base v) ⊓ E ≤ 𝒩.opens v := by
    have h : δ ⁻¹ᵁ 𝒞.opens (δ.base v) ⊓ E
        ≤ (δ ≫ r₁) ⁻¹ᵁ 𝒩.opens ((δ ≫ r₁).base v) :=
      inf_le_left.trans (δ.preimage_mono (h𝒞₁ (δ.base v)))
    rw [hδ₁] at h
    exact h
  -- expand the glued unit at the point `δ v`
  rw [Scheme.Hom.unitsAppLE_map,
    Scheme.Hom.unitsAppLE_glued_corr r₁ r₂ 𝒞 𝒩 c γZ h𝒞₁ h𝒞₂ a b D hDa hDb δ hu v
      inf_le_left (inf_le_right.trans hE),
    -- the two composites are the identity
    Scheme.Hom.unitsAppLE_section_congr_hom hδ₁
      (fun z' => 𝒩.opens a ⊓ 𝒩.opens z') (fun z' => Scheme.unitsEvInf γZ a z') v,
    Scheme.Hom.unitsAppLE_section_congr_hom hδ₂
      (fun z' => 𝒩.opens z' ⊓ 𝒩.opens b) (fun z' => Scheme.unitsEvInf γZ z' b) v,
    Scheme.id_unitsAppLE, Scheme.id_unitsAppLE,
    -- the witness term is `1`
    hθdiag v inf_le_left, inv_one, mul_one,
    Scheme.unitsRestrict_unitsRestrict]
  -- the two correction factors telescope through the cocycle identity at `(a, v, b)`
  have t := congrArg
    (Z.unitsRestrict (le_inf (le_inf (inf_le_right.trans hEa) hOv)
      (inf_le_right.trans hEb) :
        δ ⁻¹ᵁ 𝒞.opens (δ.base v) ⊓ E ≤ 𝒩.opens a ⊓ 𝒩.opens v ⊓ 𝒩.opens b))
    (Scheme.unitsEvInf_trans γZ a v b)
  simp only [map_mul, Scheme.unitsRestrict_unitsRestrict] at t
  exact t

end Glued

end AlgebraicGeometry
