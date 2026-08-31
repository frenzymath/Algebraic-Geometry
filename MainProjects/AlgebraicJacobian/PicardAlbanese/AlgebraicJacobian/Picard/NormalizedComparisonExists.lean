/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.NormalizedComparison

/-!
# Existence of the σ-normalized comparison ((C2) effectivity, brick E1: existence)

This file constructs a `NormalizedCechComparison` from the (C2) setting's two
class-level inputs — the rigidification `hrig : σ_B^* L = 1` and the on-the-nose descent
equation `hdesc : u₁^* L = u₂^* L` on the curve over `Spec (B ⊗[A] B)` — with **no
geometric hypotheses whatsoever**: no properness, no geometric irreducibility or
reducedness, and no faithful flatness.  The construction (worksheet D4 (a)–(c)):

* **extract** (`mk`-calculus): `hdesc` yields a comparison cochain `θ₀` on a common
  refinement `𝒲` of the two coprojection pullbacks of the representing cover, and
  `hrig` yields a trivializing cochain `ρ` of the section-pullback `s_B^♯ γ` on
  `𝒩.pullback s_B` itself (`Scheme.CechPic.mk_eq_one_iff` — no refinement);
* **the σ-defect** (`AlgebraicGeometry.Over.sigmaDefectCochain`): the `0`-cochain
  `s_q^♯ θ₀ ⋅ (q₂^♯ ρ / q₁^♯ ρ)` on `Over.normalizationCover` is Čech-compatible — the
  freedom in `θ₀` measured against the ρ-comparison — so by the `𝒪ˣ`-sheaf axiom (ζ2·P
  (P1), `Scheme.exists_global_unit_of_compatible`) it glues to a global unit `δ` of
  `Spec (B ⊗[A] B)` (`Over.exists_glued_sigmaDefect`); this is where the freedom in the
  comparison is packaged as a global unit — the H⁰ statement of worksheet D4 (b);
* **normalize** (`Over.exists_normalizedCechComparison`): dividing `θ₀` by the
  projection pullback `p₂^♯ δ` preserves the witness relation (N1) and makes the
  σ-restriction *equal to the ρ-comparison* by construction — (N2) on the nose.

The disconnectedness of `Spec (B ⊗[A] B)` (étale covers produce products) is invisible
throughout: gluing is the sheaf axiom on arbitrary schemes, and no integrality or
connectedness enters anywhere.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace AlgebraicGeometry

/-- Pullback of a global unit along the identity, in `Units.map _.appTop` form. -/
lemma units_map_appTop_id {X : Scheme.{u}} (u : Γ(X, ⊤)ˣ) :
    Units.map (𝟙 X : X ⟶ X).appTop.hom.toMonoidHom u = u := by
  ext
  rw [Units.coe_map]
  change ((𝟙 X : X ⟶ X).appTop).hom u = u
  rw [Scheme.Hom.id_appTop]
  rfl

/-- Dividing the left cochain of a coboundary relation by a common unit `c` on both
sides preserves the relation: `a ⋅ P = Q ⋅ b` gives `(a/c) ⋅ P = Q ⋅ (b/c)`. -/
private lemma witness_div_global {G : Type u} [CommGroup G] {a b P Q c : G}
    (h : a * P = Q * b) : a / c * P = Q * (b / c) := by
  rw [div_mul_eq_mul_div, h, mul_div_assoc]

/-- The defect-cancellation identity of the σ-normalization:
`a / (a ⋅ (c / b)) ⋅ c = b`. -/
private lemma div_defect_mul {G : Type u} [CommGroup G] (a b c : G) :
    a / (a * (c / b)) * c = b := by
  rw [← mul_div_assoc a c b, div_div_eq_mul_div, div_mul_eq_mul_div,
    mul_right_comm a b c]
  exact mul_div_cancel_left _ b

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
local notation "p₂" => (snd C (overSpec k (B ⊗[A] B))).left
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

/-! ## The σ-defect cochain and its gluing (D4 steps (b)–(c), defect half) -/

/-- The **σ-defect cochain** of a comparison cochain `θ₀` on a cover `𝒲` of the curve
over `Spec (B ⊗[A] B)`, measured against a trivializing cochain `ρ` of the
section-pullback of the representing cocycle: the combination
`s_q^♯ θ₀ ⋅ (q₂^♯ ρ / q₁^♯ ρ)` on the normalization cover.  For a witness `θ₀` it is
Čech-compatible (`Over.exists_glued_sigmaDefect`), and a comparison satisfies (N2)
precisely when its σ-defect is `1`. -/
noncomputable def sigmaDefectCochain (𝒩 : (XB).PointedCover) (𝒲 : (Xq).PointedCover)
    (θ₀ : ∀ x : Xq, Γ(Xq, 𝒲.opens x)ˣ)
    (ρ : ∀ b : SB, Γ(SB, (𝒩.pullback (sB)).opens b)ˣ) (y : Sq) :
    Γ(Sq, (normalizationCover C σ 𝒩 𝒲).opens y)ˣ :=
  (sq).unitsAppLE (𝒲.opens ((sq).base y)) ((normalizationCover C σ 𝒩 𝒲).opens y)
      (normalizationCover_le_section C σ 𝒩 𝒲 y) (θ₀ ((sq).base y))
    * ((q₂).unitsAppLE ((𝒩.pullback (sB)).opens ((q₂).base y))
        ((normalizationCover C σ 𝒩 𝒲).opens y)
        (normalizationCover_le_inr C σ 𝒩 𝒲 y) (ρ ((q₂).base y))
      / (q₁).unitsAppLE ((𝒩.pullback (sB)).opens ((q₁).base y))
        ((normalizationCover C σ 𝒩 𝒲).opens y)
        (normalizationCover_le_inl C σ 𝒩 𝒲 y) (ρ ((q₁).base y)))

set_option maxHeartbeats 1600000 in
-- The coboundary-relation instances on the curve product are large expressions.
/-- **The σ-defect of a witness glues to a global unit of `Spec (B ⊗[A] B)`.**  If `θ₀`
cobounds the two coprojection pullbacks of `γ` (`hdown`, the (N1) shape) and `ρ`
trivializes the section pullback of `γ` (`hρ`), the σ-defect cochain is Čech-compatible
— the section squares `s_q ≫ uᵢ = qᵢ ≫ s_B` compare the two relations — and glues to a
global unit `δ` by the `𝒪ˣ`-sheaf axiom.  This is the "freedom in the comparison is a
global unit" step of worksheet D4 (b): no geometric hypotheses. -/
theorem exists_glued_sigmaDefect (𝒩 : (XB).PointedCover) (γ : (XB).unitsCocycle 𝒩)
    (𝒲 : (Xq).PointedCover)
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
    (ρ : ∀ b : SB, Γ(SB, (𝒩.pullback (sB)).opens b)ˣ)
    (hρ : ∀ b b' : SB,
      (SB).unitsRestrict
          (inf_le_left :
            (𝒩.pullback (sB)).opens b ⊓ (𝒩.pullback (sB)).opens b'
              ≤ (𝒩.pullback (sB)).opens b) (ρ b)
        * (sB).unitsAppLE (𝒩.opens ((sB).base b) ⊓ 𝒩.opens ((sB).base b'))
            ((𝒩.pullback (sB)).opens b ⊓ (𝒩.pullback (sB)).opens b')
            ((sB).le_preimage_inf inf_le_left inf_le_right)
            (Scheme.unitsEvInf γ ((sB).base b) ((sB).base b'))
        = (SB).unitsRestrict inf_le_right (ρ b')) :
    ∃ δ : Γ(Sq, ⊤)ˣ, ∀ y : Sq,
      (Sq).unitsRestrict le_top δ = sigmaDefectCochain C σ 𝒩 𝒲 θ₀ ρ y := by
  apply Scheme.exists_global_unit_of_compatible (𝒰 := normalizationCover C σ 𝒩 𝒲)
    (sigmaDefectCochain C σ 𝒩 𝒲 θ₀ ρ)
  intro y y'
  simp only [sigmaDefectCochain, map_div, map_mul, Scheme.Hom.unitsAppLE_map]
  exact Scheme.Hom.unitsAppLE_trivializing_ratio_compat (sq) (q₁) (q₂) (u₁) (u₂) (sB)
    θ₀ ρ
    (fun b b' ↦ 𝒩.opens b ⊓ 𝒩.opens b')
    (fun b b' ↦ Scheme.unitsEvInf γ b b')
    (fun x y ↦ (u₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
      (inf_le_right.trans (hW₁ y)))
    (fun x y ↦ (u₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
      (inf_le_right.trans (hW₂ y)))
    (fun b b' ↦ (sB).le_preimage_inf inf_le_left inf_le_right)
    hdown hρ
    (Over.sectionSq_comp_inl C σ) (Over.sectionSq_comp_inr C σ)
    y y'
    ((sq).le_preimage_inf
      (inf_le_left.trans (normalizationCover_le_section C σ 𝒩 𝒲 y))
      (inf_le_right.trans (normalizationCover_le_section C σ 𝒩 𝒲 y')))
    ((q₁).le_preimage_inf
      (inf_le_left.trans (normalizationCover_le_inl C σ 𝒩 𝒲 y))
      (inf_le_right.trans (normalizationCover_le_inl C σ 𝒩 𝒲 y')))
    ((q₂).le_preimage_inf
      (inf_le_left.trans (normalizationCover_le_inr C σ 𝒩 𝒲 y))
      (inf_le_right.trans (normalizationCover_le_inr C σ 𝒩 𝒲 y')))

/-! ## The existence theorem (D4 (a)–(c)) -/

/-- The **corrected comparison cochain**: a comparison `θ₀` divided by the restrictions
of a global unit `χ` of the curve over `Spec (B ⊗[A] B)` — in the construction, the
projection pullback `p₂^♯ δ` of the glued σ-defect. -/
noncomputable def correctedComparison (𝒲 : (Xq).PointedCover)
    (θ₀ : ∀ x : Xq, Γ(Xq, 𝒲.opens x)ˣ) (χ : Γ(Xq, ⊤)ˣ) (x : Xq) :
    Γ(Xq, 𝒲.opens x)ˣ :=
  θ₀ x / (Xq).unitsRestrict le_top χ

set_option maxHeartbeats 1600000 in
-- The instantiated cover expressions on the double curve product are large.
/-- **Existence of the σ-normalized comparison ((C2) effectivity, brick E1).**  In the
(C2) setting — a curve point `σ` over `A`, a unit cocycle `γ` on a pointed cover of the
curve over the étale cover `Spec B` whose class is rigidified along the base-changed
section (`hrig`) and satisfies the on-the-nose descent equation on the curve over
`Spec (B ⊗[A] B)` (`hdesc`, handed over by
`Over.IsRigidified.cechPicMap_doubleInl_eq_doubleInr`) — there exists a σ-normalized
comparison datum: a cochain realization of `hdesc` whose σ-restriction is the
ρ-comparison of a trivialization of the section pullback of `γ`.

No properness, geometric irreducibility/reducedness, or faithful flatness is needed:
the extraction is `mk`-calculus, and the normalization is the `𝒪ˣ`-sheaf axiom plus the
retraction `s_q ≫ p₂ = 𝟙`.  The geometric hypotheses enter only in the coherence
theorem `NormalizedCechComparison.coherent`
(`AlgebraicJacobian.Picard.ComparisonCoherence`). -/
theorem exists_normalizedCechComparison (𝒩 : (XB).PointedCover)
    (γ : (XB).unitsCocycle 𝒩)
    (hrig : Over.IsRigidified
      (Over.overSpecMap ((Algebra.ofId A B).restrictScalars k) ≫ σ)
      (Scheme.CechPic.mk 𝒩 γ.class))
    (hdesc : Scheme.CechPic.map (u₁) (Scheme.CechPic.mk 𝒩 γ.class)
        = Scheme.CechPic.map (u₂) (Scheme.CechPic.mk 𝒩 γ.class)) :
    Nonempty (NormalizedCechComparison k A B C σ 𝒩 γ) := by
  classical
  -- ### the trivializing cochain `ρ` of the section pullback of `γ`, from `hrig`
  have hrig' := hrig.map_eq
  rw [Scheme.CechPic.map_mk, Scheme.Hom.pullbackUnitsH1_class,
    Scheme.CechPic.mk_eq_one_iff] at hrig'
  have hcoh : ((sB).pullbackUnitsCocycle γ).IsCohomologous
      (1 : (SB).unitsCocycle (𝒩.pullback (sB))) :=
    (OneCocycle.class_eq_iff _ _).mp hrig'
  obtain ⟨ρ, hρ₀⟩ := (OneCocycle.isCohomologous_iff_evInf _ _).mp hcoh
  have hρ : ∀ b b' : SB,
      (SB).unitsRestrict
          (inf_le_left :
            (𝒩.pullback (sB)).opens b ⊓ (𝒩.pullback (sB)).opens b'
              ≤ (𝒩.pullback (sB)).opens b) (ρ b)
        * (sB).unitsAppLE (𝒩.opens ((sB).base b) ⊓ 𝒩.opens ((sB).base b'))
            ((𝒩.pullback (sB)).opens b ⊓ (𝒩.pullback (sB)).opens b')
            ((sB).le_preimage_inf inf_le_left inf_le_right)
            (Scheme.unitsEvInf γ ((sB).base b) ((sB).base b'))
        = (SB).unitsRestrict inf_le_right (ρ b') := by
    intro b b'
    have h := hρ₀ b b'
    rw [OneCocycle.one_evInf, one_mul] at h
    exact h
  -- ### the comparison cochain `θ₀` on a common refinement `𝒲`, from `hdesc`
  rw [Scheme.CechPic.map_mk, Scheme.CechPic.map_mk, Scheme.Hom.pullbackUnitsH1_class,
    Scheme.Hom.pullbackUnitsH1_class] at hdesc
  obtain ⟨𝒲, hW₁, hW₂, eW⟩ := Scheme.CechPic.mk_eq_mk_iff.mp hdesc
  have eW' : (((u₁).pullbackUnitsCocycle γ).res fun x ↦ homOfLE (hW₁ x)).IsCohomologous
      (((u₂).pullbackUnitsCocycle γ).res fun x ↦ homOfLE (hW₂ x)) :=
    (OneCocycle.class_eq_iff _ _).mp eW
  obtain ⟨θ₀, hθ₀⟩ := (OneCocycle.isCohomologous_iff_evInf _ _).mp eW'
  -- the coboundary relation for `θ₀`, in `unitsAppLE` normal form
  have hdown : ∀ x y : Xq,
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
          * (Xq).unitsRestrict inf_le_right (θ₀ y) := by
    intro x y
    have h1 : (Xq).unitsRestrict (inf_le_left : 𝒲.opens x ⊓ 𝒲.opens y ≤ 𝒲.opens x) (θ₀ x)
          * Scheme.unitsEvInf
              (((u₁).pullbackUnitsCocycle γ).res fun z ↦ homOfLE (hW₁ z)) x y
        = Scheme.unitsEvInf
              (((u₂).pullbackUnitsCocycle γ).res fun z ↦ homOfLE (hW₂ z)) x y
          * (Xq).unitsRestrict inf_le_right (θ₀ y) := hθ₀ x y
    rw [Scheme.res_unitsEvInf, Scheme.res_unitsEvInf,
      Scheme.Hom.pullbackUnitsCocycle_unitsEvInf,
      Scheme.Hom.pullbackUnitsCocycle_unitsEvInf,
      Scheme.Hom.unitsAppLE_map, Scheme.Hom.unitsAppLE_map] at h1
    exact h1
  -- ### glue the σ-defect of `θ₀` to a global unit `δ` (the freedom, as an H⁰ class)
  obtain ⟨δ, hδ⟩ := exists_glued_sigmaDefect C σ 𝒩 γ 𝒲 hW₁ hW₂ θ₀ hdown ρ hρ
  -- ### normalize: `θ := θ₀ / p₂^♯ δ` has σ-restriction the ρ-comparison
  have hs : sq ≫ p₂ = 𝟙 (Sq) :=
    Over.sectionOfPoint_left_comp_snd C
      (Over.overSpecMap ((Algebra.ofId A (B ⊗[A] B)).restrictScalars k) ≫ σ)
  refine ⟨{
    sectionTriv := ρ
    sectionTriv_rel := hρ
    cover := 𝒲
    le_pullbackInl := hW₁
    le_pullbackInr := hW₂
    θ := correctedComparison C 𝒲 θ₀ (Units.map (p₂).appTop.hom.toMonoidHom δ)
    witness := ?_
    normalized := ?_ }⟩
  · intro x y
    simp only [correctedComparison, map_div, Scheme.unitsRestrict_unitsRestrict]
    exact witness_div_global (hdown x y)
  · intro y
    have h1 : (sq).unitsAppLE (𝒲.opens ((sq).base y))
        ((Over.normalizationCover C σ 𝒩 𝒲).opens y)
        (Over.normalizationCover_le_section C σ 𝒩 𝒲 y)
        ((Xq).unitsRestrict le_top (Units.map (p₂).appTop.hom.toMonoidHom δ))
        = (Sq).unitsRestrict le_top δ := by
      rw [Scheme.Hom.unitsAppLE_unitsRestrict_top, units_map_appTop_comp, hs,
        units_map_appTop_id]
    simp only [correctedComparison, map_div]
    rw [h1, hδ y]
    simp only [sigmaDefectCochain]
    exact div_defect_mul _ _ _

end Over

end AlgebraicGeometry
