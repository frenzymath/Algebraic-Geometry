/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.CoherentWitness

/-!
# Pullback calculus for global units and cochain combinations

The `unitsAppLE` calculus for pulling back global units and `⋅ ⋅ /`-combinations of
cochain values along a morphism of schemes, in composite normal form:

* `AlgebraicGeometry.unitsRestrict_top_self`, `AlgebraicGeometry.unitsAppLE_top_global`:
  the `⊤`-restriction spellings of a global-unit pullback agree.
* `AlgebraicGeometry.unitsAppLE_mulDiv_comp`, `AlgebraicGeometry.unitsAppLE_mulRatio_comp`:
  pushing `unitsAppLE` through an `a ⋅ b / c` (resp. `t ⋅ (a / b)`) combination of
  pulled-back cochain values merges the compositions.
* `AlgebraicGeometry.unitsAppLE_defect_pullback`,
  `AlgebraicGeometry.unitsAppLE_ratio_pullback`: the full pullback of a glued
  Amitsur-defect (resp. comparison) identity, with the output composites re-expressed
  along given coincidences.

All lemmas are stated over abstract schemes: their (rewrite-heavy) proofs are elaborated
and kernel-checked once, over small types, so that the concrete instantiations in the
ζ2·i construction (`AlgebraicJacobian.Picard.CoherentWitnessExists`) are single
applications with small proof terms.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace AlgebraicGeometry

/-- Restriction of a global unit along `⊤ ≤ ⊤` is the identity. -/
lemma unitsRestrict_top_self {Y : Scheme.{u}} (u : Γ(Y, ⊤)ˣ) :
    Y.unitsRestrict le_top u = u := by
  apply Units.ext
  change (Y.presheaf.map (homOfLE _).op) u.val = u.val
  rw [show (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) from rfl,
    Y.presheaf.map_id]
  rfl

/-- `unitsAppLE` at `V = ⊤` is the `⊤`-restriction of the `appTop`-pullback: the
open-indexed and global spellings of pulling back a global unit agree. -/
lemma unitsAppLE_top_global {X Y : Scheme.{u}} (f : X ⟶ Y) {O : X.Opens}
    (e : O ≤ f ⁻¹ᵁ ⊤) (u : Γ(Y, ⊤)ˣ) :
    f.unitsAppLE ⊤ O e u
      = X.unitsRestrict le_top (Units.map f.appTop.hom.toMonoidHom u) := by
  conv_lhs => rw [← unitsRestrict_top_self u]
  exact Scheme.Hom.unitsAppLE_unitsRestrict_top f e u

/-- Pushing `unitsAppLE` through an `a ⋅ b / c` combination of pulled-back cochain values
merges the compositions. Stated over abstract schemes so that the (rewrite-heavy) proof is
kernel-checked once, over small types; the concrete Step-G instantiations are single
applications. -/
lemma unitsAppLE_mulDiv_comp {X Y Z : Scheme.{u}} (φ : X ⟶ Y)
    (g₂₃ g₁₂ g₁₃ : Y ⟶ Z) {𝒵 : Z.PointedCover} (θ : ∀ z : Z, Γ(Z, 𝒵.opens z)ˣ)
    {V : Y.Opens} {O : X.Opens} (e : O ≤ φ ⁻¹ᵁ V) (x : X)
    (e₂₃ : V ≤ g₂₃ ⁻¹ᵁ 𝒵.opens (g₂₃.base (φ.base x)))
    (e₁₂ : V ≤ g₁₂ ⁻¹ᵁ 𝒵.opens (g₁₂.base (φ.base x)))
    (e₁₃ : V ≤ g₁₃ ⁻¹ᵁ 𝒵.opens (g₁₃.base (φ.base x))) :
    φ.unitsAppLE V O e
        (g₂₃.unitsAppLE (𝒵.opens (g₂₃.base (φ.base x))) V e₂₃ (θ (g₂₃.base (φ.base x)))
          * g₁₂.unitsAppLE (𝒵.opens (g₁₂.base (φ.base x))) V e₁₂
              (θ (g₁₂.base (φ.base x)))
          / g₁₃.unitsAppLE (𝒵.opens (g₁₃.base (φ.base x))) V e₁₃
              (θ (g₁₃.base (φ.base x))))
      = (φ ≫ g₂₃).unitsAppLE (𝒵.opens (g₂₃.base (φ.base x))) O
            (e.trans (φ.preimage_mono e₂₃)) (θ (g₂₃.base (φ.base x)))
        * (φ ≫ g₁₂).unitsAppLE (𝒵.opens (g₁₂.base (φ.base x))) O
            (e.trans (φ.preimage_mono e₁₂)) (θ (g₁₂.base (φ.base x)))
        / (φ ≫ g₁₃).unitsAppLE (𝒵.opens (g₁₃.base (φ.base x))) O
            (e.trans (φ.preimage_mono e₁₃)) (θ (g₁₃.base (φ.base x))) := by
  simp only [map_mul, map_div, Scheme.unitsAppLE_unitsAppLE]

/-- Pushing `unitsAppLE` through a `t ⋅ (a / b)` combination of pulled-back cochain values
merges the compositions: the ratio-shaped companion of `unitsAppLE_mulDiv_comp`. -/
lemma unitsAppLE_mulRatio_comp {X Y Zc Za : Scheme.{u}} (φ : X ⟶ Y)
    (gt : Y ⟶ Zc) (g₂ g₁ : Y ⟶ Za)
    {𝒵 : Zc.PointedCover} {𝒴 : Za.PointedCover}
    (θ : ∀ z : Zc, Γ(Zc, 𝒵.opens z)ˣ) (α : ∀ z : Za, Γ(Za, 𝒴.opens z)ˣ)
    {V : Y.Opens} {O : X.Opens} (e : O ≤ φ ⁻¹ᵁ V) (x : X)
    (et : V ≤ gt ⁻¹ᵁ 𝒵.opens (gt.base (φ.base x)))
    (e₂ : V ≤ g₂ ⁻¹ᵁ 𝒴.opens (g₂.base (φ.base x)))
    (e₁ : V ≤ g₁ ⁻¹ᵁ 𝒴.opens (g₁.base (φ.base x))) :
    φ.unitsAppLE V O e
        (gt.unitsAppLE (𝒵.opens (gt.base (φ.base x))) V et (θ (gt.base (φ.base x)))
          * (g₂.unitsAppLE (𝒴.opens (g₂.base (φ.base x))) V e₂ (α (g₂.base (φ.base x)))
            / g₁.unitsAppLE (𝒴.opens (g₁.base (φ.base x))) V e₁
                (α (g₁.base (φ.base x)))))
      = (φ ≫ gt).unitsAppLE (𝒵.opens (gt.base (φ.base x))) O
            (e.trans (φ.preimage_mono et)) (θ (gt.base (φ.base x)))
        * ((φ ≫ g₂).unitsAppLE (𝒴.opens (g₂.base (φ.base x))) O
              (e.trans (φ.preimage_mono e₂)) (α (g₂.base (φ.base x)))
          / (φ ≫ g₁).unitsAppLE (𝒴.opens (g₁.base (φ.base x))) O
              (e.trans (φ.preimage_mono e₁)) (α (g₁.base (φ.base x)))) := by
  simp only [map_mul, map_div, Scheme.unitsAppLE_unitsAppLE]

/-- The `φ`-pullback of a glued defect, in composite normal form: if a global unit `W`
restricts on `V` to an `a ⋅ b / c` combination of `m`-pullbacks of a cochain `θ`, then the
`appTop`-pullback of `W` along `φ` restricts to the corresponding combination of
`t = φ ≫ m`-pullbacks. All spelling changes (composites, base points, proofs) happen here,
over abstract schemes, so the concrete instantiation is a single application. -/
lemma unitsAppLE_defect_pullback {X Y S : Scheme.{u}}
    (φ : X ⟶ Y) (m₂₃ m₁₂ m₁₃ : Y ⟶ S) (t₂₃ t₁₂ t₁₃ : X ⟶ S)
    {𝒮 : S.PointedCover} (θ : ∀ s : S, Γ(S, 𝒮.opens s)ˣ)
    (W : Γ(Y, ⊤)ˣ) {V : Y.Opens} {O : X.Opens} (e : O ≤ φ ⁻¹ᵁ V) (x : X)
    (e₂₃ : V ≤ m₂₃ ⁻¹ᵁ 𝒮.opens (m₂₃.base (φ.base x)))
    (e₁₂ : V ≤ m₁₂ ⁻¹ᵁ 𝒮.opens (m₁₂.base (φ.base x)))
    (e₁₃ : V ≤ m₁₃ ⁻¹ᵁ 𝒮.opens (m₁₃.base (φ.base x)))
    (hW : Y.unitsRestrict (le_top : V ≤ ⊤) W
        = m₂₃.unitsAppLE (𝒮.opens (m₂₃.base (φ.base x))) V e₂₃
            (θ (m₂₃.base (φ.base x)))
          * m₁₂.unitsAppLE (𝒮.opens (m₁₂.base (φ.base x))) V e₁₂
              (θ (m₁₂.base (φ.base x)))
          / m₁₃.unitsAppLE (𝒮.opens (m₁₃.base (φ.base x))) V e₁₃
              (θ (m₁₃.base (φ.base x))))
    (h₂₃ : φ ≫ m₂₃ = t₂₃) (h₁₂ : φ ≫ m₁₂ = t₁₂) (h₁₃ : φ ≫ m₁₃ = t₁₃)
    (e₂₃O : O ≤ t₂₃ ⁻¹ᵁ 𝒮.opens (t₂₃.base x))
    (e₁₂O : O ≤ t₁₂ ⁻¹ᵁ 𝒮.opens (t₁₂.base x))
    (e₁₃O : O ≤ t₁₃ ⁻¹ᵁ 𝒮.opens (t₁₃.base x)) :
    X.unitsRestrict (le_top : O ≤ ⊤) (Units.map φ.appTop.hom.toMonoidHom W)
      = t₂₃.unitsAppLE (𝒮.opens (t₂₃.base x)) O e₂₃O (θ (t₂₃.base x))
        * t₁₂.unitsAppLE (𝒮.opens (t₁₂.base x)) O e₁₂O (θ (t₁₂.base x))
        / t₁₃.unitsAppLE (𝒮.opens (t₁₃.base x)) O e₁₃O (θ (t₁₃.base x)) := by
  subst h₂₃ h₁₂ h₁₃
  refine (Scheme.Hom.unitsAppLE_unitsRestrict_top φ e W).symm.trans ?_
  refine (congrArg (φ.unitsAppLE V O e) hW).trans ?_
  exact unitsAppLE_mulDiv_comp φ m₂₃ m₁₂ m₁₃ θ e x e₂₃ e₁₂ e₁₃

/-- The `n`-pullback of a global unit whose restriction is a `t ⋅ (a / b)` comparison
combination, in composite normal form, with the output composites re-expressed along
given coincidences `ht, h₂, h₁`. The ratio-shaped companion of
`unitsAppLE_defect_pullback`. -/
lemma unitsAppLE_ratio_pullback {X Y Zc Za : Scheme.{u}}
    (n : X ⟶ Y) (gt : Y ⟶ Zc) (g₂ g₁ : Y ⟶ Za) (t : X ⟶ Zc) (a₂ a₁ : X ⟶ Za)
    {𝒵 : Zc.PointedCover} {𝒴 : Za.PointedCover}
    (θ : ∀ z : Zc, Γ(Zc, 𝒵.opens z)ˣ) (α : ∀ z : Za, Γ(Za, 𝒴.opens z)ˣ)
    (Ψ : Γ(Y, ⊤)ˣ) {V : Y.Opens} {O : X.Opens} (e : O ≤ n ⁻¹ᵁ V) (x : X)
    (et : V ≤ gt ⁻¹ᵁ 𝒵.opens (gt.base (n.base x)))
    (e₂ : V ≤ g₂ ⁻¹ᵁ 𝒴.opens (g₂.base (n.base x)))
    (e₁ : V ≤ g₁ ⁻¹ᵁ 𝒴.opens (g₁.base (n.base x)))
    (hΨ : Y.unitsRestrict (le_top : V ≤ ⊤) Ψ
        = gt.unitsAppLE (𝒵.opens (gt.base (n.base x))) V et (θ (gt.base (n.base x)))
          * (g₂.unitsAppLE (𝒴.opens (g₂.base (n.base x))) V e₂
                (α (g₂.base (n.base x)))
            / g₁.unitsAppLE (𝒴.opens (g₁.base (n.base x))) V e₁
                (α (g₁.base (n.base x)))))
    (ht : n ≫ gt = t) (h₂ : n ≫ g₂ = a₂) (h₁ : n ≫ g₁ = a₁)
    (etO : O ≤ t ⁻¹ᵁ 𝒵.opens (t.base x))
    (e₂O : O ≤ a₂ ⁻¹ᵁ 𝒴.opens (a₂.base x))
    (e₁O : O ≤ a₁ ⁻¹ᵁ 𝒴.opens (a₁.base x)) :
    n.unitsAppLE ⊤ O le_top Ψ
      = t.unitsAppLE (𝒵.opens (t.base x)) O etO (θ (t.base x))
        * (a₂.unitsAppLE (𝒴.opens (a₂.base x)) O e₂O (α (a₂.base x))
          / a₁.unitsAppLE (𝒴.opens (a₁.base x)) O e₁O (α (a₁.base x))) := by
  subst ht h₂ h₁
  refine (Scheme.Hom.map_unitsAppLE n e ((homOfLE le_top).op) Ψ).symm.trans ?_
  refine (congrArg (n.unitsAppLE V O e) hΨ).trans ?_
  exact unitsAppLE_mulRatio_comp n gt g₂ g₁ θ α e x et e₂ e₁


end AlgebraicGeometry
