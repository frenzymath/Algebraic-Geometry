/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.WitnessCorrection
import AlgebraicJacobian.Picard.PicAffineCover

/-!
# The glued witness components on the basic opens of the tensor square (ζ2·ii, G5)

Concrete instantiation, on the tensor towers `Spec B ← Spec (B ⊗[A] B) ← Spec (B ⊗[A]
(B ⊗[A] B))`, of the corrected-witness calculus of
`AlgebraicJacobian.Picard.WitnessCorrection`: given an Amitsur-coherent Čech witness
`θ' : CoherentCechWitness k A B 𝒩 γ` and a finite basic refinement `P` of `𝒩`, this file
produces the **witness components** of the ζ2·ii pi-assembly as glued unit sections on
the basic opens `D(q₁^♯(P.r i) ⋅ q₂^♯(P.r j))` of `Spec (B ⊗[A] B)`, and proves their
two identities:

* `AlgebraicGeometry.Over.pairSection` / `Over.tripleSection`: the global sections of
  `Spec (B ⊗[A] B)` resp. `Spec (B ⊗[A] (B ⊗[A] B))` cutting out the double and triple
  basic opens, spelled through the coprojections `q₁, q₂` and the canonical composites
  `f₁₂ ≫ q₁`, `f₁₂ ≫ q₂`, `f₁₃ ≫ q₂` (the three insertions).
* `AlgebraicGeometry.Over.witnessBasicSection`: the glued corrected witness unit on
  `D(q₁^♯(P.r i) ⋅ q₂^♯(P.r j))`, with defining property `witnessBasicSection_spec`.
* `AlgebraicGeometry.Over.witnessAppLE_diag_eq_one`: the diagonal triviality of the
  coherent witness — the coherence pulled back along the degeneracy `σ = Spec (μ₁₂)` and
  the diagonal `Δ = Spec (mul)`.
* `AlgebraicGeometry.Over.witnessBasicSection_amitsur`: the Amitsur cocycle identity of
  the glued components over the triple tensor — single application of
  `glued_corr_amitsur` along the landed `Spec`-level simplicial coincidences.
* `AlgebraicGeometry.Over.witnessBasicSection_collapse`: the diagonal collapse — the
  `Δ`-pullback of the glued component is the Zariski cover cocycle `P.coverCocycle γ`.

The algebra bridge (`AlgebraicJacobian.Picard.WitnessAssembly`) transports these three
statements through the localization identifications `S i ⊗[A] S j ≅ Γ(D(...))` into the
hypotheses of the pure-algebra assembly `AlgebraicJacobian.Algebra.PiAssembly`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

set_option quotPrecheck false in
local notation "XB" => (overSpec k B).left
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
set_option quotPrecheck false in
local notation "Δs" => (Over.overSpecMap (tensorMul (k := k) (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "σs" => (Over.overSpecMap (tensorMul₁₂ (k := k) (A := A) (B := B))).left

namespace Over

variable {𝒩 : ((overSpec k B).left).PointedCover}
variable {γ : ((overSpec k B).left).unitsCocycle 𝒩}

/-! ## The double and triple basic sections and their containments -/

variable (P : 𝒩.BasicRefinement)

/-- The global section of the tensor square cutting out the double basic open
`D(q₁^♯(P.r i)) ⊓ D(q₂^♯(P.r j))`. -/
noncomputable def pairSection (i j : P.ι) : Γ(Sq, ⊤) :=
  (q₁).appTop.hom (P.r i) * (q₂).appTop.hom (P.r j)

lemma pairSection_def (i j : P.ι) :
    pairSection P i j = (q₁).appTop.hom (P.r i) * (q₂).appTop.hom (P.r j) :=
  rfl

/-- The global section of the triple tensor cutting out the triple basic open, spelled
through the three canonical insertions `f₁₂ ≫ q₁`, `f₁₂ ≫ q₂`, `f₁₃ ≫ q₂`. -/
noncomputable def tripleSection (i j l : P.ι) : Γ(Scb, ⊤) :=
  (f₁₂ ≫ q₁).appTop.hom (P.r i)
    * ((f₁₂ ≫ q₂).appTop.hom (P.r j) * (f₁₃ ≫ q₂).appTop.hom (P.r l))

lemma tripleSection_def (i j l : P.ι) :
    tripleSection P i j l
      = (f₁₂ ≫ q₁).appTop.hom (P.r i)
        * ((f₁₂ ≫ q₂).appTop.hom (P.r j) * (f₁₃ ≫ q₂).appTop.hom (P.r l)) :=
  rfl

/-- The double basic open refines the `q₁`-pullback of the trivializing cover at
`P.pt i`. -/
lemma basicOpen_pairSection_le_inl (i j : P.ι) :
    (Sq).basicOpen (pairSection P i j) ≤ (q₁) ⁻¹ᵁ 𝒩.opens (P.pt i) := by
  rw [pairSection_def, Scheme.basicOpen_mul]
  refine inf_le_left.trans ?_
  rw [← Scheme.preimage_basicOpen_top]
  exact (q₁).preimage_mono (P.basicOpen_le i)

/-- The double basic open refines the `q₂`-pullback of the trivializing cover at
`P.pt j`. -/
lemma basicOpen_pairSection_le_inr (i j : P.ι) :
    (Sq).basicOpen (pairSection P i j) ≤ (q₂) ⁻¹ᵁ 𝒩.opens (P.pt j) := by
  rw [pairSection_def, Scheme.basicOpen_mul]
  refine inf_le_right.trans ?_
  rw [← Scheme.preimage_basicOpen_top]
  exact (q₂).preimage_mono (P.basicOpen_le j)

/-- Elementwise composite of `appTop`s. -/
private lemma appTop_appTop {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Γ(Z, ⊤)) : f.appTop.hom (g.appTop.hom x) = (f ≫ g).appTop.hom x := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- `appTop` along an equal morphism. -/
private lemma appTop_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (x : Γ(Y, ⊤)) : f.appTop.hom x = g.appTop.hom x := by
  subst h; rfl

/-- The `f₂₃`-pullback of the double section at `(j, l)` in insertion normal form. -/
lemma appTop_pairSection_f₂₃ (j l : P.ι) :
    (f₂₃).appTop.hom (pairSection P j l)
      = (f₁₂ ≫ q₂).appTop.hom (P.r j) * (f₁₃ ≫ q₂).appTop.hom (P.r l) := by
  rw [pairSection_def, map_mul, appTop_appTop, appTop_appTop,
    appTop_congr_hom (Over.overSpecMap_left_face₁₂_inr (k := k) (A := A) (B := B)).symm
      (P.r j),
    appTop_congr_hom (Over.overSpecMap_left_face₁₃_inr (k := k) (A := A) (B := B)).symm
      (P.r l)]

/-- The `f₁₂`-pullback of the double section at `(i, j)` in insertion normal form. -/
lemma appTop_pairSection_f₁₂ (i j : P.ι) :
    (f₁₂).appTop.hom (pairSection P i j)
      = (f₁₂ ≫ q₁).appTop.hom (P.r i) * (f₁₂ ≫ q₂).appTop.hom (P.r j) := by
  rw [pairSection_def, map_mul, appTop_appTop, appTop_appTop]

/-- The `f₁₃`-pullback of the double section at `(i, l)` in insertion normal form. -/
lemma appTop_pairSection_f₁₃ (i l : P.ι) :
    (f₁₃).appTop.hom (pairSection P i l)
      = (f₁₂ ≫ q₁).appTop.hom (P.r i) * (f₁₃ ≫ q₂).appTop.hom (P.r l) := by
  rw [pairSection_def, map_mul, appTop_appTop, appTop_appTop,
    appTop_congr_hom (Over.overSpecMap_left_face₁₂_inl (k := k) (A := A) (B := B)).symm
      (P.r i)]

/-- The triple basic open sits inside the `f₂₃`-preimage of the double basic open at
`(j, l)`. -/
lemma basicOpen_tripleSection_le_f₂₃ (i j l : P.ι) :
    (Scb).basicOpen (tripleSection P i j l) ≤ (f₂₃) ⁻¹ᵁ (Sq).basicOpen (pairSection P j l) := by
  rw [Scheme.preimage_basicOpen_top, appTop_pairSection_f₂₃]
  exact Scheme.basicOpen_le_of_dvd ⟨(f₁₂ ≫ q₁).appTop.hom (P.r i), by rw [tripleSection_def]; ring⟩

/-- The triple basic open sits inside the `f₁₂`-preimage of the double basic open at
`(i, j)`. -/
lemma basicOpen_tripleSection_le_f₁₂ (i j l : P.ι) :
    (Scb).basicOpen (tripleSection P i j l) ≤ (f₁₂) ⁻¹ᵁ (Sq).basicOpen (pairSection P i j) := by
  rw [Scheme.preimage_basicOpen_top, appTop_pairSection_f₁₂]
  exact Scheme.basicOpen_le_of_dvd ⟨(f₁₃ ≫ q₂).appTop.hom (P.r l), by rw [tripleSection_def]; ring⟩

/-- The triple basic open sits inside the `f₁₃`-preimage of the double basic open at
`(i, l)`. -/
lemma basicOpen_tripleSection_le_f₁₃ (i j l : P.ι) :
    (Scb).basicOpen (tripleSection P i j l) ≤ (f₁₃) ⁻¹ᵁ (Sq).basicOpen (pairSection P i l) := by
  rw [Scheme.preimage_basicOpen_top, appTop_pairSection_f₁₃]
  exact Scheme.basicOpen_le_of_dvd ⟨(f₁₂ ≫ q₂).appTop.hom (P.r j), by rw [tripleSection_def]; ring⟩

/-- The `Δ`-pullback of the double section is the Zariski double section. -/
lemma appTop_pairSection_diag (i j : P.ι) :
    (Δs).appTop.hom (pairSection P i j) = P.r i * P.r j := by
  rw [pairSection_def, map_mul, appTop_appTop, appTop_appTop,
    appTop_congr_hom (Over.overSpecMap_left_mul_inl (k := k) (A := A) (B := B)) (P.r i),
    appTop_congr_hom (Over.overSpecMap_left_mul_inr (k := k) (A := A) (B := B)) (P.r j),
    Scheme.Hom.id_appTop]
  rfl

/-- The Zariski double basic open sits inside the `Δ`-preimage of the double basic
open. -/
lemma basicOpen_mul_le_diag_pairSection (i j : P.ι) :
    (XB).basicOpen (P.r i * P.r j) ≤ (Δs) ⁻¹ᵁ (Sq).basicOpen (pairSection P i j) := by
  rw [Scheme.preimage_basicOpen_top, appTop_pairSection_diag]

/-! ## The glued witness components -/

variable (θ' : CoherentCechWitness k A B 𝒩 γ)

/-- **The glued witness component** (ζ2·ii, G5): the corrected witness values
`q₁^♯ γ(pt i, q₁ x) ⋅ (θ x)⁻¹ ⋅ q₂^♯ γ(q₂ x, pt j)` glued over the double basic open
`D(q₁^♯(P.r i) ⋅ q₂^♯(P.r j))` of `Spec (B ⊗[A] B)`. -/
noncomputable def witnessBasicSection (i j : P.ι) :
    Γ(Sq, (Sq).basicOpen (pairSection P i j))ˣ :=
  (exists_glued_unitsCorrCochain q₁ q₂ θ'.cover 𝒩 θ'.θ γ
    θ'.le_pullbackInl θ'.le_pullbackInr (P.pt i) (P.pt j)
    ((Sq).basicOpen (pairSection P i j))
    (basicOpen_pairSection_le_inl P i j) (basicOpen_pairSection_le_inr P i j)
    θ'.witness).choose

/-- The defining property of the glued witness component: its restriction to
`θ'.cover.opens x ⊓ D` is the corrected witness value at `x`. -/
lemma witnessBasicSection_spec (i j : P.ι) (x : Sq) :
    (Sq).unitsRestrict
        (inf_le_right : θ'.cover.opens x ⊓ (Sq).basicOpen (pairSection P i j)
          ≤ (Sq).basicOpen (pairSection P i j))
        (witnessBasicSection P θ' i j)
      = unitsCorrCochain q₁ q₂ θ'.cover 𝒩 θ'.θ γ θ'.le_pullbackInl θ'.le_pullbackInr
          (P.pt i) (P.pt j) ((Sq).basicOpen (pairSection P i j))
          (basicOpen_pairSection_le_inl P i j) (basicOpen_pairSection_le_inr P i j) x :=
  (exists_glued_unitsCorrCochain q₁ q₂ θ'.cover 𝒩 θ'.θ γ
    θ'.le_pullbackInl θ'.le_pullbackInr (P.pt i) (P.pt j)
    ((Sq).basicOpen (pairSection P i j))
    (basicOpen_pairSection_le_inl P i j) (basicOpen_pairSection_le_inr P i j)
    θ'.witness).choose_spec x

/-! ## Diagonal triviality of the coherent witness -/

/-- **The coherent witness is `1` along the diagonal `Δ = Spec (mul)`** — the coherence
pulled back along the degeneracy `σ = Spec (μ₁₂)` and then along `Δ`. -/
theorem witnessAppLE_diag_eq_one (v : XB) {O : (XB).Opens}
    (hO : O ≤ (Δs) ⁻¹ᵁ θ'.cover.opens ((Δs).base v)) :
    (Δs).unitsAppLE (θ'.cover.opens ((Δs).base v)) O hO (θ'.θ ((Δs).base v)) = 1 := by
  have hΔδr : Δs ≫ (q₁ ≫ Δs) = Δs := by
    rw [← Category.assoc, Over.overSpecMap_left_mul_inl, Category.id_comp]
  exact unitsAppLE_diag_eq_one_of_coherent Δs (q₁ ≫ Δs) hΔδr θ'.cover θ'.θ
    (fun y _ hO'₁ hO'₂ => unitsAppLE_eq_one_of_coherent f₂₃ f₁₂ f₁₃ σs (q₁ ≫ Δs)
      (Over.overSpecMap_left_mul₁₂_face₂₃ (k := k) (A := A) (B := B))
      (Over.overSpecMap_left_mul₁₂_face₁₂ (k := k) (A := A) (B := B))
      (Over.overSpecMap_left_mul₁₂_face₁₃ (k := k) (A := A) (B := B))
      θ'.cover θ'.θ θ'.coherent y hO'₁ hO'₂)
    v hO

/-! ## The two identities of the glued components -/

set_option maxHeartbeats 1000000 in
-- The instantiation on the triple tensor tower is a large term.
/-- **The Amitsur cocycle identity of the glued witness components** (ζ2·ii): over the
triple basic open of `Spec (B ⊗[A] (B ⊗[A] B))`,
`f₂₃^♯ u(j,l) ⋅ f₁₂^♯ u(i,j) = f₁₃^♯ u(i,l)`.  Single application of
`glued_corr_amitsur` along the landed simplicial coincidences; this is where the Amitsur
coherence of `θ'` becomes the cocycle identity of the pi-assembly. -/
theorem witnessBasicSection_amitsur (i j l : P.ι) :
    (f₂₃).unitsAppLE ((Sq).basicOpen (pairSection P j l))
        ((Scb).basicOpen (tripleSection P i j l))
        (basicOpen_tripleSection_le_f₂₃ P i j l) (witnessBasicSection P θ' j l)
      * (f₁₂).unitsAppLE ((Sq).basicOpen (pairSection P i j))
          ((Scb).basicOpen (tripleSection P i j l))
          (basicOpen_tripleSection_le_f₁₂ P i j l) (witnessBasicSection P θ' i j)
    = (f₁₃).unitsAppLE ((Sq).basicOpen (pairSection P i l))
        ((Scb).basicOpen (tripleSection P i j l))
        (basicOpen_tripleSection_le_f₁₃ P i j l) (witnessBasicSection P θ' i l) :=
  glued_corr_amitsur f₂₃ f₁₂ f₁₃ q₁ q₂ θ'.cover 𝒩 θ'.θ γ
    θ'.le_pullbackInl θ'.le_pullbackInr
    (Over.overSpecMap_left_face₁₂_inl (k := k) (A := A) (B := B)).symm
    (Over.overSpecMap_left_face₁₂_inr (k := k) (A := A) (B := B)).symm
    (Over.overSpecMap_left_face₁₃_inr (k := k) (A := A) (B := B)).symm
    θ'.coherent (P.pt i) (P.pt j) (P.pt l)
    ((Sq).basicOpen (pairSection P j l)) ((Sq).basicOpen (pairSection P i j))
    ((Sq).basicOpen (pairSection P i l))
    (basicOpen_pairSection_le_inl P j l) (basicOpen_pairSection_le_inr P j l)
    (basicOpen_pairSection_le_inl P i j) (basicOpen_pairSection_le_inr P i j)
    (basicOpen_pairSection_le_inl P i l) (basicOpen_pairSection_le_inr P i l)
    (witnessBasicSection_spec P θ' j l) (witnessBasicSection_spec P θ' i j)
    (witnessBasicSection_spec P θ' i l)
    (basicOpen_tripleSection_le_f₂₃ P i j l) (basicOpen_tripleSection_le_f₁₂ P i j l)
    (basicOpen_tripleSection_le_f₁₃ P i j l)

set_option maxHeartbeats 1000000 in
-- The instantiation on the tensor tower is a large term.
/-- **The diagonal collapse of the glued witness components onto the Zariski cover
cocycle** (ζ2·ii, the G6 component identity): the `Δ`-pullback of the glued component on
`D(P.r i ⋅ P.r j) ⊆ Spec B` is `P.coverCocycle γ i j`. -/
theorem witnessBasicSection_collapse (i j : P.ι) :
    (Δs).unitsAppLE ((Sq).basicOpen (pairSection P i j)) ((XB).basicOpen (P.r i * P.r j))
        (basicOpen_mul_le_diag_pairSection P i j) (witnessBasicSection P θ' i j)
      = P.coverCocycle γ i j :=
  glued_corr_collapse q₁ q₂ θ'.cover 𝒩 θ'.θ γ θ'.le_pullbackInl θ'.le_pullbackInr Δs
    (Over.overSpecMap_left_mul_inl (k := k) (A := A) (B := B))
    (Over.overSpecMap_left_mul_inr (k := k) (A := A) (B := B))
    (fun v _ hO => witnessAppLE_diag_eq_one θ' v hO)
    (P.pt i) (P.pt j) ((Sq).basicOpen (pairSection P i j))
    (basicOpen_pairSection_le_inl P i j) (basicOpen_pairSection_le_inr P i j)
    (witnessBasicSection_spec P θ' i j)
    (basicOpen_mul_le_diag_pairSection P i j)
    ((P.overlap_le i j).trans inf_le_left) ((P.overlap_le i j).trans inf_le_right)

end Over

end AlgebraicGeometry
