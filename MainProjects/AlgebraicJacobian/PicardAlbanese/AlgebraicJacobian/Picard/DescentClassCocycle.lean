/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DescentSectionEval
import AlgebraicJacobian.Picard.CechPicSurjective

/-!
# The Čech representative of a descended Picard class, with its `μ`-data (ζ3 brick M)

Let `A → B` be faithfully flat and `w` a global unit on `Spec (B ⊗[A] B)` whose
`ΓSpecIso`-avatar `W ∈ (B ⊗[A] B)ˣ` is a descent `1`-cocycle.  The descended module
`Mod := descended W ⊆ B` is an invertible `A`-module; this file represents its Picard
class as a Čech class on `Spec A` **together with the unit data that trivializes its
pullback to `Spec B`**:

* a pointed cover and unit cocycle on `Spec A` (a trivializing family for the
  `Γ(Spec A, ⊤)`-avatar of `Mod`);
* for each point `a`, a **unit** `μ a` on the `g_S`-preimage of the cover member — the
  evaluation of the generator of the trivialization at `a` — such that
  - (`ratio`) the two coprojection pullbacks of `μ a` to `Spec (B ⊗[A] B)` differ
    exactly by the restriction of `w` (from the descent equation of `Mod`, via
    `Over.evalT_ratio`), and
  - (`transition`) on overlaps, `μ a` and `μ b` differ exactly by the `g_S`-pullback of
    the cocycle value (from the transition-unit action on generators).

`μ a` is a unit because the descent equivalence `B ⊗[A] Mod ≃ₗ[B] B` makes the
generator's evaluation generate the base-changed sections
(`Module.isUnit_map_rTensor_generator`).

This file lands the **interface** of the brick — the structure `Over.DescentClassRep` —
together with the descent equation of the descended module in coprojection form
(`descended_tensorInr_eq`, the input to `Over.evalT_ratio`) and the base-change collapse
of generator tensors (`cancelN`, `cancelN_rTensor`).  The construction of a
`DescentClassRep` is `AlgebraicJacobian.Picard.DescentClassRepBuild`.
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
local notation "SA" => (overSpec k A).left
set_option quotPrecheck false in
local notation "SB" => (overSpec k B).left
set_option quotPrecheck false in
local notation "Sq" => (overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "gS" => (Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left
set_option quotPrecheck false in
local notation "q₁" => (Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "q₂" => (Over.overSpecMap (tensorInr (A := A) (B := B))).left

attribute [local instance] specSectionsAlgebra overSpecSectionsAlgebra
  overSpecSectionsAlgebraSq algebraA_sections isScalarTower_sections
  isScalarTower_sections_basicOpen Over.overSpecSectionsAlgebraA

/-- The base `Spec A` of the tower is affine, in the `overSpec`-spelling (scoped). -/
@[reducible] noncomputable def isAffineOverSpecA : IsAffine (SA) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))

attribute [local instance] isAffineOverSpecA

namespace Over

/-- The scalar tower `A → Γ(Spec A, ⊤) → Γ(Spec A, D(g))` on the base side. -/
local instance isScalarTower_sectionsA_basicOpen (g : Γ(SA, ⊤)) :
    IsScalarTower A Γ(SA, ⊤) Γ(SA, (SA).basicOpen g) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    change (SA).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
      = (SA).presheaf.map (homOfLE ((SA).basicOpen_le g)).op
          ((SA).presheaf.map (homOfLE le_top).op
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- **The Čech representative of a descended Picard class, with its `μ`-data** (ζ3
brick M).  The cover/cocycle present the descended class on `Spec A`; the units `μ a`
trivialize its `g_S`-pullback with coprojection ratio exactly `w`.  The `ratio` and
`transition` fields are quantified over an arbitrary sub-open of their natural domains,
so that consumers never transport unit sections across equalities of opens. -/
structure DescentClassRep [Module.FaithfullyFlat A B] (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w)) :
    Type u where
  /-- The pointed cover of `Spec A` carrying the representing cocycle. -/
  cover : (SA).PointedCover
  /-- The representing unit cocycle. -/
  cocycle : (SA).unitsCocycle cover
  /-- The trivializing units of the pulled-back class. -/
  μ : ∀ a : SA, Γ(SB, (gS) ⁻¹ᵁ cover.opens a)ˣ
  /-- The coprojection ratio of `μ` is the restriction of `w`. -/
  ratio : ∀ (a : SA) (O : (Sq).Opens)
    (e₁ : O ≤ (q₁) ⁻¹ᵁ ((gS) ⁻¹ᵁ cover.opens a))
    (e₂ : O ≤ (q₂) ⁻¹ᵁ ((gS) ⁻¹ᵁ cover.opens a)),
    (q₂).unitsAppLE ((gS) ⁻¹ᵁ cover.opens a) O e₂ (μ a)
      = (Sq).unitsRestrict (le_top : O ≤ ⊤) w
        * (q₁).unitsAppLE ((gS) ⁻¹ᵁ cover.opens a) O e₁ (μ a)
  /-- On overlaps, the `μ`'s differ by the `g_S`-pullback of the cocycle value. -/
  transition : ∀ (a b : SA) (T : (SB).Opens)
    (ha : T ≤ (gS) ⁻¹ᵁ cover.opens a) (hb : T ≤ (gS) ⁻¹ᵁ cover.opens b),
    (SB).unitsRestrict ha (μ a)
      = (gS).unitsAppLE (cover.opens a ⊓ cover.opens b) T
          ((gS).le_preimage_inf ha hb) (Scheme.unitsEvInf cocycle a b)
        * (SB).unitsRestrict hb (μ b)

variable [Module.FaithfullyFlat A B]

omit [Module.FaithfullyFlat A B] in
/-- The descent equation of the descended module, in the coprojection form consumed by
`Over.evalT_ratio`. -/
lemma descended_tensorInr_eq (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (m : hW.descended) :
    tensorInr (k := k) (A := A) (B := B) (m : B)
      = (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom w.val
        * tensorInl (k := k) (A := A) (B := B) (m : B) := by
  have h := hW.mem_descended.mp m.2
  -- `W ⋅ (m ⊗ₜ 1) = 1 ⊗ₜ m`, and `W = ΓSpecIso (w)`
  have h1 : tensorInl (k := k) (A := A) (B := B) (m : B) = (m : B) ⊗ₜ[A] (1 : B) := by
    simp [tensorInl]
  have h2 : tensorInr (k := k) (A := A) (B := B) (m : B) = (1 : B) ⊗ₜ[A] (m : B) := by
    simp [tensorInr]
  rw [h1, h2, ← h]
  rfl

/-- The base-change collapse of the generator tensor: `Γ(Spec A, D(g)) ⊗[Γ(Spec A, ⊤)]
(Γ(Spec A, ⊤) ⊗[A] Mod) ≃ Γ(Spec A, D(g)) ⊗[A] Mod`. -/
noncomputable def cancelN (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (g : Γ(SA, ⊤)) :
    (Γ(SA, (SA).basicOpen g) ⊗[Γ(SA, ⊤)] (Γ(SA, ⊤) ⊗[A] ↥(hW.descended)))
      ≃ₗ[Γ(SA, (SA).basicOpen g)] Γ(SA, (SA).basicOpen g) ⊗[A] ↥(hW.descended) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange A Γ(SA, ⊤) Γ(SA, (SA).basicOpen g)
    Γ(SA, (SA).basicOpen g) ↥(hW.descended)

set_option maxHeartbeats 2000000 in
-- the unification of the composite section-ring module instances is heartbeat-hungry
omit [IsScalarTower k A B] [Module.FaithfullyFlat A B] in
/-- `cancelN` intertwines `rTensor` of a restriction on the two sides. -/
lemma cancelN_rTensor (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (g g' : Γ(SA, ⊤))
    (hle : (SA).basicOpen g' ≤ (SA).basicOpen g)
    (x : Γ(SA, (SA).basicOpen g) ⊗[Γ(SA, ⊤)] (Γ(SA, ⊤) ⊗[A] ↥(hW.descended))) :
    LinearMap.rTensor (↥(hW.descended))
        (((Scheme.basicRes g g' hle).toLinearMap).restrictScalars A)
        (cancelN (k := k) w hW g x)
      = cancelN (k := k) w hW g'
          (LinearMap.rTensor (Γ(SA, ⊤) ⊗[A] ↥(hW.descended))
            (Scheme.basicRes g g' hle).toLinearMap x) := by
  induction x with
  | zero => simp only [map_zero]
  | tmul s n =>
      induction n with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | tmul r m =>
          simp only [cancelN, LinearMap.rTensor_tmul,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            LinearMap.coe_restrictScalars, map_smul]
      | add n n' hn hn' =>
          simp only [TensorProduct.tmul_add, map_add, hn, hn']
  | add x y hx hy => simp only [map_add, hx, hy]

end Over

end AlgebraicGeometry
