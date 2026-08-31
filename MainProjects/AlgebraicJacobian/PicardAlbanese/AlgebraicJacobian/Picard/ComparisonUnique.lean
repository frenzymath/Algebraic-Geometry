/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.NormalizedComparison

/-!
# Uniqueness of the σ-normalized comparison ((C2) effectivity, brick E1: canonicity)

For a proper, geometrically irreducible and geometrically reduced curve, the comparison
cochain of a σ-normalized comparison datum is **unique**: two cochains on the same cover
satisfying (N1) against the same cocycle `γ` and (N2) against the same trivialization
`ρ` are equal (`Over.normalizedComparison_unique`).  This is the canonicity companion of
`Over.exists_normalizedCechComparison`, and the E2 convenience that makes the per-piece
descent data extracted from the packaged datum independent of all choices.

The argument is the double-base miniature of the `lm:aut` pattern used for the
coherence (N3):

* the ratio `θ / θ'` of two (N1) cochains has trivial coboundary, hence is
  Čech-compatible and glues to a global unit `χ` of the curve over `Spec (B ⊗[A] B)`
  (the `𝒪ˣ`-sheaf axiom — no hypotheses);
* the σ-restriction of `χ` is `1`: both (N2) normalizations equate the section
  pullbacks of `θ` and `θ'` to the same ρ-comparison;
* G2 (`Over.unitsAppTop_sectionOfPoint_bijective` at the affine test `B ⊗[A] B`) forces
  `χ = 1` — this is where the geometric triple enters.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace AlgebraicGeometry

/-- Two elements cobounding the same comparison have equal ratios:
from `a ⋅ P = Q ⋅ b` and `a' ⋅ P = Q ⋅ b'` conclude `a / a' = b / b'`. -/
private lemma coboundary_div_congr {G : Type u} [CommGroup G] {a a' b b' P Q : G}
    (h : a * P = Q * b) (h' : a' * P = Q * b') : a / a' = b / b' := by
  rw [div_eq_div_iff_mul_eq_mul]
  refine mul_right_cancel (b := P) ?_
  calc a * b' * P = a * P * b' := mul_right_comm a b' P
    _ = Q * b * b' := by rw [h]
    _ = Q * (b * b') := mul_assoc Q b b'
    _ = b * (Q * b') := mul_left_comm Q b b'
    _ = b * (a' * P) := by rw [h']
    _ = b * a' * P := (mul_assoc b a' P).symm

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]
variable (C : Over (Spec (.of k))) (σ : overSpec k A ⟶ C)

-- Spec-side objects and maps
set_option quotPrecheck false in
local notation "SB" => (overSpec k B).left
set_option quotPrecheck false in
local notation "Sq" => (overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "q₁" => (Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "q₂" => (Over.overSpecMap (tensorInr (A := A) (B := B))).left
-- product-side objects and maps
set_option quotPrecheck false in
local notation "XB" => (C ⊗ overSpec k B).left
set_option quotPrecheck false in
local notation "Xq" => (C ⊗ overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "u₁" => (C ◁ Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "u₂" => (C ◁ Over.overSpecMap (tensorInr (A := A) (B := B))).left
-- the sections of the projections attached to the base changes of `σ`
set_option quotPrecheck false in
local notation "sB" => (Over.sectionOfPoint
  (Over.overSpecMap ((Algebra.ofId A B).restrictScalars k) ≫ σ)).left
set_option quotPrecheck false in
local notation "sq" => (Over.sectionOfPoint
  (Over.overSpecMap ((Algebra.ofId A (B ⊗[A] B)).restrictScalars k) ≫ σ)).left

namespace Over

/-- **Uniqueness of the σ-normalized comparison.**  For a proper, geometrically
irreducible and geometrically reduced curve, two comparison cochains on the same cover
of the curve over `Spec (B ⊗[A] B)` satisfying the witness relation (N1) against the
same cocycle `γ` and the σ-normalization (N2) against the same trivialization `ρ` are
equal.  The ratio `θ / θ'` glues to a global unit with trivial σ-restriction, and G2
(Kleiman's `lm:aut` rigidity at the affine test `B ⊗[A] B`) kills it. -/
theorem normalizedComparison_unique
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    (𝒩 : (XB).PointedCover) (γ : (XB).unitsCocycle 𝒩) (𝒲 : (Xq).PointedCover)
    (hW₁ : ∀ x, 𝒲.opens x ≤ (u₁) ⁻¹ᵁ 𝒩.opens ((u₁).base x))
    (hW₂ : ∀ x, 𝒲.opens x ≤ (u₂) ⁻¹ᵁ 𝒩.opens ((u₂).base x))
    (ρ : ∀ b : SB, Γ(SB, (𝒩.pullback (sB)).opens b)ˣ)
    (θ θ' : ∀ x : Xq, Γ(Xq, 𝒲.opens x)ˣ)
    (hdown : ∀ x y : Xq,
      (Xq).unitsRestrict (inf_le_left : 𝒲.opens x ⊓ 𝒲.opens y ≤ 𝒲.opens x) (θ x)
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
          * (Xq).unitsRestrict inf_le_right (θ y))
    (hdown' : ∀ x y : Xq,
      (Xq).unitsRestrict (inf_le_left : 𝒲.opens x ⊓ 𝒲.opens y ≤ 𝒲.opens x) (θ' x)
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
          * (Xq).unitsRestrict inf_le_right (θ' y))
    (hnorm : ∀ y : Sq,
      (sq).unitsAppLE (𝒲.opens ((sq).base y))
          ((normalizationCover C σ 𝒩 𝒲).opens y)
          (normalizationCover_le_section C σ 𝒩 𝒲 y) (θ ((sq).base y))
        * (q₂).unitsAppLE ((𝒩.pullback (sB)).opens ((q₂).base y))
            ((normalizationCover C σ 𝒩 𝒲).opens y)
            (normalizationCover_le_inr C σ 𝒩 𝒲 y) (ρ ((q₂).base y))
      = (q₁).unitsAppLE ((𝒩.pullback (sB)).opens ((q₁).base y))
          ((normalizationCover C σ 𝒩 𝒲).opens y)
          (normalizationCover_le_inl C σ 𝒩 𝒲 y) (ρ ((q₁).base y)))
    (hnorm' : ∀ y : Sq,
      (sq).unitsAppLE (𝒲.opens ((sq).base y))
          ((normalizationCover C σ 𝒩 𝒲).opens y)
          (normalizationCover_le_section C σ 𝒩 𝒲 y) (θ' ((sq).base y))
        * (q₂).unitsAppLE ((𝒩.pullback (sB)).opens ((q₂).base y))
            ((normalizationCover C σ 𝒩 𝒲).opens y)
            (normalizationCover_le_inr C σ 𝒩 𝒲 y) (ρ ((q₂).base y))
      = (q₁).unitsAppLE ((𝒩.pullback (sB)).opens ((q₁).base y))
          ((normalizationCover C σ 𝒩 𝒲).opens y)
          (normalizationCover_le_inl C σ 𝒩 𝒲 y) (ρ ((q₁).base y))) :
    θ = θ' := by
  -- ### the ratio `θ / θ'` is Čech-compatible and glues to a global unit `χ`
  obtain ⟨χ, hχ⟩ := Scheme.exists_global_unit_of_compatible (𝒰 := 𝒲)
    (fun x ↦ θ x / θ' x) (fun x y ↦ by
      rw [map_div, map_div]
      exact coboundary_div_congr (hdown x y) (hdown' x y))
  -- ### the σ-restriction of `χ` is `1` — both (N2)s give the same ρ-comparison
  have hsec : Units.map (sq).appTop.hom.toMonoidHom χ = 1 := by
    refine Scheme.global_unit_ext (𝒰 := normalizationCover C σ 𝒩 𝒲) _ _ fun y ↦ ?_
    rw [map_one, ← Scheme.Hom.unitsAppLE_unitsRestrict_top (sq)
      (normalizationCover_le_section C σ 𝒩 𝒲 y) χ, hχ ((sq).base y), map_div,
      div_eq_one]
    exact mul_right_cancel ((hnorm y).trans ((hnorm' y).symm))
  -- ### G2 at the affine test `B ⊗[A] B` kills `χ`
  have hone : χ = 1 := by
    apply (Over.unitsAppTop_sectionOfPoint_bijective
      (Over.overSpecMap ((Algebra.ofId A (B ⊗[A] B)).restrictScalars k) ≫ σ)).injective
    rw [map_one, unitsAppLE_top_global, hsec, map_one]
  -- ### conclude pointwise
  funext x
  exact div_eq_one.mp
    ((map_one ((Xq).unitsRestrict (le_top : 𝒲.opens x ≤ ⊤))).symm.trans
      (((congrArg ((Xq).unitsRestrict le_top) hone).symm).trans (hχ x))).symm

end Over

end AlgebraicGeometry
