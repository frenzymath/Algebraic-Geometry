/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.ComparisonDefect

/-!
# Coherence of the σ-normalized comparison ((C2) effectivity, brick E1: `lm:aut`)

**(N3), the brick's point**: for a proper, geometrically irreducible and geometrically
reduced curve, the three coface pullbacks of a σ-normalized comparison `θ`
(`AlgebraicGeometry.NormalizedCechComparison`) to the curve over the triple base
`Spec (B ⊗[A] (B ⊗[A] B))` satisfy the Amitsur cocycle identity **on the nose**
(`NormalizedCechComparison.coherent`):

`(w₂₃^♯ θ) ⋅ (w₁₂^♯ θ) = w₁₃^♯ θ`

— in the exact face convention of `Module.IsDescentCocycle.cocycle`
(`descentFace₂₃ u ⋅ descentFace₁₂ u = descentFace₁₃ u`; the `w`-maps are the whiskered
`Spec`s of the same `Module.descentFace` maps), so the per-piece descent brick E2 can
restrict this identity along the `cg`-saturated affine pieces at zero cost.

Kleiman's `lm:aut` argument (*The Picard Scheme*, proof of Theorem 2.5(2)), cocycle
form: coherence is a *consequence* of (N1) + (N2), not an extra datum.

* The Amitsur defect `ε = (w₂₃^♯ θ) ⋅ (w₁₂^♯ θ) / (w₁₃^♯ θ)`
  (`Over.productDefectCochain`) glues to a global unit `ε̄` of `X_{B⊗B⊗B}` by the
  `𝒪ˣ`-sheaf axiom (`Over.exists_glued_productDefect`,
  `AlgebraicJacobian.Picard.ComparisonDefect` — the H⁰ step; no hypotheses).
* The σ-restriction of `ε̄` is `1`: pulling the glued identity back along the section
  `s_cb` turns the `w`-faces into `f`-faces of the σ-restriction of `θ` (the section
  squares), and the three ρ-comparisons of (N2) telescope to `1` through the `Spec`-side
  simplicial coincidences (`sectionPullback_productDefect_eq_one`).
* G2 (`Over.unitsAppTop_sectionOfPoint_bijective`, Kleiman's `lm:aut`) at the — possibly
  disconnected, never integral — affine test `B ⊗[A] (B ⊗[A] B)` forces `ε̄ = 1`, which
  is the coherence identity on the nose.

Faithful flatness is nowhere needed; the geometric triple `[IsProper C.hom]
[GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]` enters only through G2.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace AlgebraicGeometry

/-- The abelian telescope of the σ-restriction of the Amitsur defect: three one-sided
relations against a common triple `a, b, c` cancel to the cocycle identity. -/
private lemma telescope_eq_one {G : Type u} [CommGroup G] {T₂₃ T₁₂ T₁₃ a b c : G}
    (h₂₃ : T₂₃ * c = b) (h₁₂ : T₁₂ * b = a) (h₁₃ : T₁₃ * c = a) :
    T₂₃ * T₁₂ / T₁₃ = 1 := by
  have h : T₁₃ * c = T₁₂ * (T₂₃ * c) := by rw [h₂₃, h₁₂]; exact h₁₃
  rw [← mul_assoc] at h
  rw [div_eq_one, mul_comm]
  exact mul_right_cancel h.symm

/-- **Pullback of a per-point normalization relation along a morphism of schemes**, in
composite normal form with the output composites re-expressed along given coincidences
`ht, h₁, h₂`.  If a `0`-cochain relation `(st^♯ c)(y) ⋅ (n₂^♯ a)(y) = (n₁^♯ a)(y)` holds
on a pointed cover `𝒟` of `Y` (in applications: the (N2) normalization on
`Over.normalizationCover`), its pullback along `g : X ⟶ Y` holds in the
`t = g ≫ st`-composite normal form.  Stated over abstract schemes so the (rewrite-heavy)
proof is kernel-checked once, over small types. -/
lemma unitsAppLE_normalization_pullback {X Y Yc Ya : Scheme.{u}}
    (g : X ⟶ Y) (st : Y ⟶ Yc) (n₁ n₂ : Y ⟶ Ya) (t : X ⟶ Yc) (m₁ m₂ : X ⟶ Ya)
    {𝒞 : Yc.PointedCover} {𝒜 : Ya.PointedCover} {𝒟 : Y.PointedCover}
    (c : ∀ v : Yc, Γ(Yc, 𝒞.opens v)ˣ) (a : ∀ v : Ya, Γ(Ya, 𝒜.opens v)ˣ)
    (et : ∀ y : Y, 𝒟.opens y ≤ st ⁻¹ᵁ 𝒞.opens (st.base y))
    (e₁ : ∀ y : Y, 𝒟.opens y ≤ n₁ ⁻¹ᵁ 𝒜.opens (n₁.base y))
    (e₂ : ∀ y : Y, 𝒟.opens y ≤ n₂ ⁻¹ᵁ 𝒜.opens (n₂.base y))
    (hrel : ∀ y : Y,
      st.unitsAppLE (𝒞.opens (st.base y)) (𝒟.opens y) (et y) (c (st.base y))
          * n₂.unitsAppLE (𝒜.opens (n₂.base y)) (𝒟.opens y) (e₂ y) (a (n₂.base y))
        = n₁.unitsAppLE (𝒜.opens (n₁.base y)) (𝒟.opens y) (e₁ y) (a (n₁.base y)))
    (ht : g ≫ st = t) (h₁ : g ≫ n₁ = m₁) (h₂ : g ≫ n₂ = m₂)
    (x : X) {O : X.Opens} (hO : O ≤ g ⁻¹ᵁ 𝒟.opens (g.base x))
    (etO : O ≤ t ⁻¹ᵁ 𝒞.opens (t.base x))
    (e₁O : O ≤ m₁ ⁻¹ᵁ 𝒜.opens (m₁.base x))
    (e₂O : O ≤ m₂ ⁻¹ᵁ 𝒜.opens (m₂.base x)) :
    t.unitsAppLE (𝒞.opens (t.base x)) O etO (c (t.base x))
        * m₂.unitsAppLE (𝒜.opens (m₂.base x)) O e₂O (a (m₂.base x))
      = m₁.unitsAppLE (𝒜.opens (m₁.base x)) O e₁O (a (m₁.base x)) := by
  subst ht h₁ h₂
  have H := congrArg (g.unitsAppLE (𝒟.opens (g.base x)) O hO) (hrel (g.base x))
  rw [map_mul, Scheme.unitsAppLE_unitsAppLE, Scheme.unitsAppLE_unitsAppLE,
    Scheme.unitsAppLE_unitsAppLE] at H
  exact H

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

/-! ## The σ-restriction of the glued defect -/

/-- The pointed cover of the affine triple base on which the σ-restriction of the glued
defect is computed: the defect cover pulled back along the section, intersected with the
three coface pullbacks of the normalization cover.  An opaque `def` with named
`≤`-lemmas, following the (C1) Step-G pattern. -/
private noncomputable def sectionTelescopeCover (𝒩 : (XB).PointedCover)
    (𝒲 : (Xq).PointedCover) : (Scb).PointedCover :=
  ((amitsurProductCover C 𝒲).pullback (scb))
    ⊓ (((normalizationCover C σ 𝒩 𝒲).pullback (f₂₃)
        ⊓ (normalizationCover C σ 𝒩 𝒲).pullback (f₁₂))
      ⊓ (normalizationCover C σ 𝒩 𝒲).pullback (f₁₃))

private lemma sectionTelescopeCover_le_section (𝒩 : (XB).PointedCover)
    (𝒲 : (Xq).PointedCover) (t : Scb) :
    (sectionTelescopeCover C σ 𝒩 𝒲).opens t
      ≤ (scb) ⁻¹ᵁ (amitsurProductCover C 𝒲).opens ((scb).base t) :=
  inf_le_left

private lemma sectionTelescopeCover_le_f₂₃ (𝒩 : (XB).PointedCover)
    (𝒲 : (Xq).PointedCover) (t : Scb) :
    (sectionTelescopeCover C σ 𝒩 𝒲).opens t
      ≤ (f₂₃) ⁻¹ᵁ (normalizationCover C σ 𝒩 𝒲).opens ((f₂₃).base t) :=
  inf_le_right.trans (inf_le_left.trans inf_le_left)

private lemma sectionTelescopeCover_le_f₁₂ (𝒩 : (XB).PointedCover)
    (𝒲 : (Xq).PointedCover) (t : Scb) :
    (sectionTelescopeCover C σ 𝒩 𝒲).opens t
      ≤ (f₁₂) ⁻¹ᵁ (normalizationCover C σ 𝒩 𝒲).opens ((f₁₂).base t) :=
  inf_le_right.trans (inf_le_left.trans inf_le_right)

private lemma sectionTelescopeCover_le_f₁₃ (𝒩 : (XB).PointedCover)
    (𝒲 : (Xq).PointedCover) (t : Scb) :
    (sectionTelescopeCover C σ 𝒩 𝒲).opens t
      ≤ (f₁₃) ⁻¹ᵁ (normalizationCover C σ 𝒩 𝒲).opens ((f₁₃).base t) :=
  inf_le_right.trans inf_le_right

set_option maxHeartbeats 1600000 in
-- The pulled-back normalization instances on the triple towers are large expressions.
/-- **The σ-restriction of the glued Amitsur defect is `1`.**  Pulling the glued defect
identity back along the section `s_cb` turns the three `w`-face pullbacks of `θ₀` into
`f`-face pullbacks of the σ-restriction of `θ₀` (the section squares); the (N2)
normalization replaces each by a ratio of `ρ`-terms, which telescope to `1` through the
`Spec`-level simplicial coincidences.  No geometric hypotheses. -/
private theorem sectionPullback_productDefect_eq_one (𝒩 : (XB).PointedCover)
    (𝒲 : (Xq).PointedCover) (θ₀ : ∀ x : Xq, Γ(Xq, 𝒲.opens x)ˣ)
    (ρ : ∀ b : SB, Γ(SB, (𝒩.pullback (sB)).opens b)ˣ)
    (hnorm : ∀ y : Sq,
      (sq).unitsAppLE (𝒲.opens ((sq).base y))
          ((normalizationCover C σ 𝒩 𝒲).opens y)
          (normalizationCover_le_section C σ 𝒩 𝒲 y) (θ₀ ((sq).base y))
        * (q₂).unitsAppLE ((𝒩.pullback (sB)).opens ((q₂).base y))
            ((normalizationCover C σ 𝒩 𝒲).opens y)
            (normalizationCover_le_inr C σ 𝒩 𝒲 y) (ρ ((q₂).base y))
      = (q₁).unitsAppLE ((𝒩.pullback (sB)).opens ((q₁).base y))
          ((normalizationCover C σ 𝒩 𝒲).opens y)
          (normalizationCover_le_inl C σ 𝒩 𝒲 y) (ρ ((q₁).base y)))
    (εbar : Γ(Xcb, ⊤)ˣ)
    (hεbar : ∀ z : Xcb,
      (Xcb).unitsRestrict le_top εbar = productDefectCochain C 𝒲 θ₀ z) :
    Units.map (scb).appTop.hom.toMonoidHom εbar = 1 := by
  refine Scheme.global_unit_ext (𝒰 := sectionTelescopeCover C σ 𝒩 𝒲) _ _ fun t ↦ ?_
  rw [map_one]
  -- the pullback of the glued defect identity, in `f ≫ s_q` composite normal form
  have hLHS := unitsAppLE_defect_pullback (scb) (w₂₃) (w₁₂) (w₁₃)
    (f₂₃ ≫ (sq)) (f₁₂ ≫ (sq)) (f₁₃ ≫ (sq)) θ₀ εbar
    (sectionTelescopeCover_le_section C σ 𝒩 𝒲 t) t
    (amitsurProductCover_le_w₂₃ C 𝒲 ((scb).base t))
    (amitsurProductCover_le_w₁₂ C 𝒲 ((scb).base t))
    (amitsurProductCover_le_w₁₃ C 𝒲 ((scb).base t))
    (hεbar ((scb).base t))
    (Over.sectionCb_comp_face₂₃ C σ) (Over.sectionCb_comp_face₁₂ C σ)
    (Over.sectionCb_comp_face₁₃ C σ)
    ((sectionTelescopeCover_le_f₂₃ C σ 𝒩 𝒲 t).trans
      ((f₂₃).preimage_mono (normalizationCover_le_section C σ 𝒩 𝒲 ((f₂₃).base t))))
    ((sectionTelescopeCover_le_f₁₂ C σ 𝒩 𝒲 t).trans
      ((f₁₂).preimage_mono (normalizationCover_le_section C σ 𝒩 𝒲 ((f₁₂).base t))))
    ((sectionTelescopeCover_le_f₁₃ C σ 𝒩 𝒲 t).trans
      ((f₁₃).preimage_mono (normalizationCover_le_section C σ 𝒩 𝒲 ((f₁₃).base t))))
  -- the three pulled normalization relations, rewired onto the three insertions
  have rel₂₃ := unitsAppLE_normalization_pullback (f₂₃) (sq) (q₁) (q₂)
    (f₂₃ ≫ (sq)) (f₂₃ ≫ (q₁)) (f₂₃ ≫ (q₂)) θ₀ ρ
    (normalizationCover_le_section C σ 𝒩 𝒲) (normalizationCover_le_inl C σ 𝒩 𝒲)
    (normalizationCover_le_inr C σ 𝒩 𝒲) hnorm rfl rfl rfl t
    (sectionTelescopeCover_le_f₂₃ C σ 𝒩 𝒲 t)
    ((sectionTelescopeCover_le_f₂₃ C σ 𝒩 𝒲 t).trans
      ((f₂₃).preimage_mono (normalizationCover_le_section C σ 𝒩 𝒲 ((f₂₃).base t))))
    ((sectionTelescopeCover_le_f₂₃ C σ 𝒩 𝒲 t).trans
      ((f₂₃).preimage_mono (normalizationCover_le_inl C σ 𝒩 𝒲 ((f₂₃).base t))))
    ((sectionTelescopeCover_le_f₂₃ C σ 𝒩 𝒲 t).trans
      ((f₂₃).preimage_mono (normalizationCover_le_inr C σ 𝒩 𝒲 ((f₂₃).base t))))
  have rel₁₂ := unitsAppLE_normalization_pullback (f₁₂) (sq) (q₁) (q₂)
    (f₁₂ ≫ (sq)) (f₁₂ ≫ (q₁)) (f₂₃ ≫ (q₁)) θ₀ ρ
    (normalizationCover_le_section C σ 𝒩 𝒲) (normalizationCover_le_inl C σ 𝒩 𝒲)
    (normalizationCover_le_inr C σ 𝒩 𝒲) hnorm rfl rfl
    (Over.overSpecMap_left_face₁₂_inr (k := k) (A := A) (B := B)) t
    (sectionTelescopeCover_le_f₁₂ C σ 𝒩 𝒲 t)
    ((sectionTelescopeCover_le_f₁₂ C σ 𝒩 𝒲 t).trans
      ((f₁₂).preimage_mono (normalizationCover_le_section C σ 𝒩 𝒲 ((f₁₂).base t))))
    ((sectionTelescopeCover_le_f₁₂ C σ 𝒩 𝒲 t).trans
      ((f₁₂).preimage_mono (normalizationCover_le_inl C σ 𝒩 𝒲 ((f₁₂).base t))))
    ((sectionTelescopeCover_le_f₂₃ C σ 𝒩 𝒲 t).trans
      ((f₂₃).preimage_mono (normalizationCover_le_inl C σ 𝒩 𝒲 ((f₂₃).base t))))
  have rel₁₃ := unitsAppLE_normalization_pullback (f₁₃) (sq) (q₁) (q₂)
    (f₁₃ ≫ (sq)) (f₁₂ ≫ (q₁)) (f₂₃ ≫ (q₂)) θ₀ ρ
    (normalizationCover_le_section C σ 𝒩 𝒲) (normalizationCover_le_inl C σ 𝒩 𝒲)
    (normalizationCover_le_inr C σ 𝒩 𝒲) hnorm rfl
    (Over.overSpecMap_left_face₁₂_inl (k := k) (A := A) (B := B)).symm
    (Over.overSpecMap_left_face₁₃_inr (k := k) (A := A) (B := B)) t
    (sectionTelescopeCover_le_f₁₃ C σ 𝒩 𝒲 t)
    ((sectionTelescopeCover_le_f₁₃ C σ 𝒩 𝒲 t).trans
      ((f₁₃).preimage_mono (normalizationCover_le_section C σ 𝒩 𝒲 ((f₁₃).base t))))
    ((sectionTelescopeCover_le_f₁₂ C σ 𝒩 𝒲 t).trans
      ((f₁₂).preimage_mono (normalizationCover_le_inl C σ 𝒩 𝒲 ((f₁₂).base t))))
    ((sectionTelescopeCover_le_f₂₃ C σ 𝒩 𝒲 t).trans
      ((f₂₃).preimage_mono (normalizationCover_le_inr C σ 𝒩 𝒲 ((f₂₃).base t))))
  exact hLHS.trans (telescope_eq_one rel₂₃ rel₁₂ rel₁₃)

/-! ## The coherence theorem (N3) -/

set_option maxHeartbeats 1600000 in
-- The instantiated cover expressions on the triple curve product are large.
/-- **(N3), the coherence of the σ-normalized comparison** (Kleiman's `lm:aut`, the
heart of the (C2) effectivity campaign): for a proper, geometrically irreducible and
geometrically reduced curve, the three coface pullbacks of the comparison `θ` of a
`NormalizedCechComparison` to the curve over `Spec (B ⊗[A] (B ⊗[A] B))` satisfy the
Amitsur cocycle identity `(w₂₃^♯ θ) ⋅ (w₁₂^♯ θ) = w₁₃^♯ θ` **on the nose**, in the face
convention of `Module.IsDescentCocycle.cocycle`.

The coherence is a consequence of (N1) + (N2): the defect glues to a global unit whose
σ-restriction is `1` by the normalization, and G2
(`Over.unitsAppTop_sectionOfPoint_bijective` at the affine test `B ⊗[A] (B ⊗[A] B)`)
kills it.  Faithful flatness is not needed. -/
theorem _root_.AlgebraicGeometry.NormalizedCechComparison.coherent
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ) (z : Xcb) :
    (w₂₃).unitsAppLE (W.cover.opens ((w₂₃).base z))
        ((amitsurProductCover C W.cover).opens z)
        (amitsurProductCover_le_w₂₃ C W.cover z) (W.θ ((w₂₃).base z))
      * (w₁₂).unitsAppLE (W.cover.opens ((w₁₂).base z))
          ((amitsurProductCover C W.cover).opens z)
          (amitsurProductCover_le_w₁₂ C W.cover z) (W.θ ((w₁₂).base z))
    = (w₁₃).unitsAppLE (W.cover.opens ((w₁₃).base z))
        ((amitsurProductCover C W.cover).opens z)
        (amitsurProductCover_le_w₁₃ C W.cover z) (W.θ ((w₁₃).base z)) := by
  -- glue the defect (H⁰), kill its σ-restriction (N2), conclude by G2 (`lm:aut`)
  obtain ⟨εbar, hεbar⟩ := exists_glued_productDefect C 𝒩 γ W.cover
    W.le_pullbackInl W.le_pullbackInr W.θ W.witness
  have hsec : Units.map (scb).appTop.hom.toMonoidHom εbar = 1 :=
    sectionPullback_productDefect_eq_one C σ 𝒩 W.cover W.θ W.sectionTriv
      W.normalized εbar hεbar
  have hone : εbar = 1 := by
    apply (Over.unitsAppTop_sectionOfPoint_bijective
      (Over.overSpecMap ((Algebra.ofId A (B ⊗[A] (B ⊗[A] B))).restrictScalars k)
        ≫ σ)).injective
    rw [map_one, unitsAppLE_top_global, hsec, map_one]
  have h1 : productDefectCochain C W.cover W.θ z = 1 := by
    rw [← hεbar z, hone, map_one]
  exact div_eq_one.mp h1

end Over

end AlgebraicGeometry
