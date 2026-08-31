/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.SectionsDescent
import AlgebraicJacobian.Picard.UnitsGlobalPullback
import AlgebraicJacobian.Picard.AmitsurCochain

/-!
# The descent unit of a Čech class killed by the base change (ζ3 brick W)

Let `C` be proper, geometrically irreducible and geometrically reduced over a field `k`,
and `A → B` a tower of `k`-algebras.  A Čech Picard class on `X_A = (C ⊗ Spec A).left`
killed by the base-change pullback `cg^*` is trivialized by a unit `0`-cochain `β` on
the pulled-back cover.  The ratio of the two coprojection pullbacks of `β` to
`X_{B ⊗[A] B}` is compatible on overlaps, so it glues to a global unit and descends
through the projection (ε1 at `⊤`, ζ2·P) to a global unit `w` on `Spec (B ⊗[A] B)`; `w`
satisfies the Amitsur cocycle identity — checked after pullback to the triple-tensor
curve product, where the telescope of `β`-ratios cancels along the simplicial
coincidences — and restricts to `1` along the diagonal, so through `ΓSpecIso` its
avatar is a descent `1`-cocycle (`Module.IsDescentCocycle`).

Main declaration: `AlgebraicGeometry.Over.exists_kernelDescentUnit`.  The kernel-lemma
assembly (`AlgebraicJacobian.Picard.CechKernelLemma`) consumes `w` twice: its Picard
class over `A` is the descended class, and the recorded local form of `p₂^♯ w` makes
the `μ`-corrected trivialization of the ratio class descend through
`AlgebraicJacobian.Picard.SectionsDescent`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry

/-! ## Abstract pullback lemmas for ratio cochains -/

/-- Division companion of `unitsAppLE_ratio_pullback`: the `n`-pullback of a global unit
whose restriction is an `a / b` ratio of pulled-back cochain values, in composite normal
form, with the output composites re-expressed along given coincidences. -/
lemma unitsAppLE_div_pullback {X Y Za : Scheme.{u}}
    (n : X ⟶ Y) (g₂ g₁ : Y ⟶ Za) (a₂ a₁ : X ⟶ Za)
    {𝒴 : Za.PointedCover} (α : ∀ z : Za, Γ(Za, 𝒴.opens z)ˣ)
    (Ψ : Γ(Y, ⊤)ˣ) {V : Y.Opens} {O : X.Opens} (e : O ≤ n ⁻¹ᵁ V) (x : X)
    (e₂ : V ≤ g₂ ⁻¹ᵁ 𝒴.opens (g₂.base (n.base x)))
    (e₁ : V ≤ g₁ ⁻¹ᵁ 𝒴.opens (g₁.base (n.base x)))
    (hΨ : Y.unitsRestrict (le_top : V ≤ ⊤) Ψ
        = g₂.unitsAppLE (𝒴.opens (g₂.base (n.base x))) V e₂ (α (g₂.base (n.base x)))
          / g₁.unitsAppLE (𝒴.opens (g₁.base (n.base x))) V e₁ (α (g₁.base (n.base x))))
    (h₂ : n ≫ g₂ = a₂) (h₁ : n ≫ g₁ = a₁)
    (e₂O : O ≤ a₂ ⁻¹ᵁ 𝒴.opens (a₂.base x))
    (e₁O : O ≤ a₁ ⁻¹ᵁ 𝒴.opens (a₁.base x)) :
    n.unitsAppLE ⊤ O le_top Ψ
      = a₂.unitsAppLE (𝒴.opens (a₂.base x)) O e₂O (α (a₂.base x))
        / a₁.unitsAppLE (𝒴.opens (a₁.base x)) O e₁O (α (a₁.base x)) := by
  subst h₂ h₁
  refine (Scheme.Hom.map_unitsAppLE n e ((homOfLE le_top).op) Ψ).symm.trans ?_
  refine (congrArg (n.unitsAppLE V O e) hΨ).trans ?_
  simp only [map_div, Scheme.unitsAppLE_unitsAppLE]
  rfl

/-- Two elements cobounding against the same factor have equal ratios. -/
private lemma div_eq_div_of_mul_eq {G : Type u} [CommGroup G] {a b a' b' P : G}
    (ha : a * P = a') (hb : b * P = b') : a / b = a' / b' := by
  rw [← ha, ← hb, mul_div_mul_comm, div_self', mul_one]

/-- The exact cancellation of the Amitsur telescope of a ratio family. -/
private lemma ratio_mul_cancel {G : Type u} [CommGroup G] (a b c : G) :
    a / b * (c / a) = c / b := by
  rw [div_mul_div_comm, mul_comm a c, mul_div_mul_right_eq_div]

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
local notation "f₁₂" => (Over.overSpecMap (tensorFace₁₂ (k := k) (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "f₁₃" => (Over.overSpecMap (tensorFace₁₃ (k := k) (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "f₂₃" => (Over.overSpecMap (tensorFace₂₃ (k := k) (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "Δs" => (Over.overSpecMap (tensorMul (k := k) (A := A) (B := B))).left
-- product-side objects and maps
set_option quotPrecheck false in
local notation "XA" => (C ⊗ overSpec k A).left
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
local notation "cg" =>
  (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left
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
local notation "ΔX" => (C ◁ Over.overSpecMap (tensorMul (k := k) (A := A) (B := B))).left

namespace Over

/-! ## Whiskered degeneracy coincidences -/

/-- The whiskered diagonal against the first coprojection: `ΔX ≫ u₁ = 𝟙`. -/
lemma whiskerLeft_mul_inl : (ΔX) ≫ (u₁) = 𝟙 (XB) := by
  rw [← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← Over.overSpecMap_comp,
    tensorMul_comp_tensorInl, Over.overSpecMap_id, MonoidalCategory.whiskerLeft_id,
    Over.id_left]

/-- The whiskered diagonal against the second coprojection: `ΔX ≫ u₂ = 𝟙`. -/
lemma whiskerLeft_mul_inr : (ΔX) ≫ (u₂) = 𝟙 (XB) := by
  rw [← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← Over.overSpecMap_comp,
    tensorMul_comp_tensorInr, Over.overSpecMap_id, MonoidalCategory.whiskerLeft_id,
    Over.id_left]

/-! ## The kernel descent unit -/

variable {C}

/-- The pulled-back coboundary relation of `β`, on any small enough open.  Abstract
schemes keep the kernel check small; instantiated inside `exists_kernelDescentUnit`. -/
private lemma ratio_pull {Y Z Q : Scheme.{u}} (g : Y ⟶ Z)
    (ℰ : Z.PointedCover) (lam : Z.unitsCocycle ℰ) (𝒜 : Y.PointedCover)
    (h𝒜 : ∀ v : Y, 𝒜.opens v ≤ g ⁻¹ᵁ ℰ.opens (g.base v))
    (β : ∀ v : Y, Γ(Y, 𝒜.opens v)ˣ)
    (hβ : ∀ v v' : Y,
      Y.unitsRestrict (inf_le_left : 𝒜.opens v ⊓ 𝒜.opens v' ≤ 𝒜.opens v) (β v)
          * g.unitsAppLE (ℰ.opens (g.base v) ⊓ ℰ.opens (g.base v'))
              (𝒜.opens v ⊓ 𝒜.opens v')
              (g.le_preimage_inf (inf_le_left.trans (h𝒜 v))
                (inf_le_right.trans (h𝒜 v')))
              (Scheme.unitsEvInf lam (g.base v) (g.base v'))
        = Y.unitsRestrict inf_le_right (β v'))
    (z z' : Q) (φ : Q ⟶ Y) (O : Q.Opens)
    (hO : O ≤ φ ⁻¹ᵁ (𝒜.opens (φ.base z) ⊓ 𝒜.opens (φ.base z'))) :
    φ.unitsAppLE (𝒜.opens (φ.base z)) O
        (hO.trans (φ.preimage_mono inf_le_left)) (β (φ.base z))
      * (φ ≫ g).unitsAppLE
          (ℰ.opens ((φ ≫ g).base z) ⊓ ℰ.opens ((φ ≫ g).base z')) O
          (hO.trans (φ.preimage_mono
            (g.le_preimage_inf (inf_le_left.trans (h𝒜 (φ.base z)))
              (inf_le_right.trans (h𝒜 (φ.base z'))))))
          (Scheme.unitsEvInf lam ((φ ≫ g).base z) ((φ ≫ g).base z'))
    = φ.unitsAppLE (𝒜.opens (φ.base z')) O
        (hO.trans (φ.preimage_mono inf_le_right)) (β (φ.base z')) := by
  have h := congrArg (φ.unitsAppLE (𝒜.opens (φ.base z) ⊓ 𝒜.opens (φ.base z')) O hO)
    (hβ (φ.base z) (φ.base z'))
  rw [map_mul, Scheme.Hom.map_unitsAppLE, Scheme.Hom.map_unitsAppLE,
    Scheme.unitsAppLE_unitsAppLE] at h
  exact h

/-- Compatibility of the coprojection ratio family on overlaps, over abstract schemes
and `v₁ v₂ : Q ⟶ Y` with `v₁ ≫ g = v₂ ≫ g`; instantiated in `exists_kernelDescentUnit`. -/
private lemma ratio_compat {Y Z Q : Scheme.{u}} (g : Y ⟶ Z) (v₁ v₂ : Q ⟶ Y)
    (hgeq : v₁ ≫ g = v₂ ≫ g)
    (ℰ : Z.PointedCover) (lam : Z.unitsCocycle ℰ) (𝒜 : Y.PointedCover)
    (h𝒜 : ∀ v : Y, 𝒜.opens v ≤ g ⁻¹ᵁ ℰ.opens (g.base v))
    (β : ∀ v : Y, Γ(Y, 𝒜.opens v)ˣ)
    (hβ : ∀ v v' : Y,
      Y.unitsRestrict (inf_le_left : 𝒜.opens v ⊓ 𝒜.opens v' ≤ 𝒜.opens v) (β v)
          * g.unitsAppLE (ℰ.opens (g.base v) ⊓ ℰ.opens (g.base v'))
              (𝒜.opens v ⊓ 𝒜.opens v')
              (g.le_preimage_inf (inf_le_left.trans (h𝒜 v))
                (inf_le_right.trans (h𝒜 v')))
              (Scheme.unitsEvInf lam (g.base v) (g.base v'))
        = Y.unitsRestrict inf_le_right (β v'))
    (z z' : Q) :
    Q.unitsRestrict
        (inf_le_left : (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z
          ⊓ (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z'
          ≤ (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z)
        (v₁.unitsAppLE (𝒜.opens (v₁.base z))
            ((𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z) inf_le_left
            (β (v₁.base z))
          / v₂.unitsAppLE (𝒜.opens (v₂.base z))
            ((𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z) inf_le_right
            (β (v₂.base z)))
      = Q.unitsRestrict inf_le_right
          (v₁.unitsAppLE (𝒜.opens (v₁.base z'))
              ((𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z') inf_le_left
              (β (v₁.base z'))
            / v₂.unitsAppLE (𝒜.opens (v₂.base z'))
              ((𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z') inf_le_right
              (β (v₂.base z'))) := by
  have h₁ := ratio_pull g ℰ lam 𝒜 h𝒜 β hβ z z' v₁
    ((𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z
      ⊓ (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z')
    (v₁.le_preimage_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans inf_le_left))
  have h₂ := ratio_pull g ℰ lam 𝒜 h𝒜 β hβ z z' v₂
    ((𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z
      ⊓ (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z')
    (v₂.le_preimage_inf (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_right))
  have emid : (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z
        ⊓ (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z'
      ≤ (v₁ ≫ g) ⁻¹ᵁ (ℰ.opens ((v₁ ≫ g).base z)
        ⊓ ℰ.opens ((v₁ ≫ g).base z')) :=
    (v₁.le_preimage_inf (inf_le_left.trans inf_le_left)
        (inf_le_right.trans inf_le_left)).trans
      (v₁.preimage_mono (g.le_preimage_inf
        (inf_le_left.trans (h𝒜 (v₁.base z)))
        (inf_le_right.trans (h𝒜 (v₁.base z')))))
  have hmid := Scheme.Hom.unitsAppLE_pair_congr_hom hgeq
    (fun s t ↦ ℰ.opens s ⊓ ℰ.opens t) (fun s t ↦ Scheme.unitsEvInf lam s t) z z' emid
  have h₂' := (congrArg
    (fun t ↦ v₂.unitsAppLE (𝒜.opens (v₂.base z))
      ((𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z
        ⊓ (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z')
      ((v₂.le_preimage_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right)).trans (v₂.preimage_mono inf_le_left))
      (β (v₂.base z)) * t) hmid).trans h₂
  have l₁ := Scheme.Hom.unitsAppLE_map (f := v₁)
    (inf_le_left : (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z
      ≤ v₁ ⁻¹ᵁ 𝒜.opens (v₁.base z))
    ((homOfLE (inf_le_left : (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z
      ⊓ (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z'
      ≤ (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z)).op) (β (v₁.base z))
  have l₂ := Scheme.Hom.unitsAppLE_map (f := v₂)
    (inf_le_right : (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z
      ≤ v₂ ⁻¹ᵁ 𝒜.opens (v₂.base z))
    ((homOfLE (inf_le_left : (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z
      ⊓ (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z'
      ≤ (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z)).op) (β (v₂.base z))
  have l₃ := Scheme.Hom.unitsAppLE_map (f := v₁)
    (inf_le_left : (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z'
      ≤ v₁ ⁻¹ᵁ 𝒜.opens (v₁.base z'))
    ((homOfLE (inf_le_right : (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z
      ⊓ (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z'
      ≤ (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z')).op) (β (v₁.base z'))
  have l₄ := Scheme.Hom.unitsAppLE_map (f := v₂)
    (inf_le_right : (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z'
      ≤ v₂ ⁻¹ᵁ 𝒜.opens (v₂.base z'))
    ((homOfLE (inf_le_right : (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z
      ⊓ (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z'
      ≤ (𝒜.pullback v₁ ⊓ 𝒜.pullback v₂).opens z')).op) (β (v₂.base z'))
  exact (map_div _ _ _).trans ((congrArg₂ (· / ·) l₁ l₂).trans
    (((div_eq_div_of_mul_eq h₁ h₂').trans
      (congrArg₂ (· / ·) l₃.symm l₄.symm)).trans (map_div _ _ _).symm))

variable [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

set_option maxHeartbeats 1600000 in
-- instantiated at the concrete triple-tensor curve product; default budget insufficient
/-- The Amitsur cocycle identity of the descent unit, from its local ratio form. -/
private lemma amitsur_of_local (𝒜 : (XB).PointedCover)
    (β : ∀ v : XB, Γ(XB, 𝒜.opens v)ˣ) (w : Γ(Sq, ⊤)ˣ)
    (hwloc : ∀ z : Xq,
      (Xq).unitsRestrict
          (le_top : (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).opens z ≤ ⊤)
          (Units.map (p₂).appTop.hom.toMonoidHom w)
        = (u₁).unitsAppLE (𝒜.opens ((u₁).base z))
            ((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).opens z) inf_le_left (β ((u₁).base z))
          / (u₂).unitsAppLE (𝒜.opens ((u₂).base z))
            ((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).opens z) inf_le_right
            (β ((u₂).base z))) :
    Units.map (f₂₃).appTop.hom.toMonoidHom w
        * Units.map (f₁₂).appTop.hom.toMonoidHom w
      = Units.map (f₁₃).appTop.hom.toMonoidHom w := by
  have hfactor : ∀ (φS : Scb ⟶ Sq) (φX : Xcb ⟶ Xq) (_ : φX ≫ (p₂) = (p₃) ≫ φS)
      (O : (Xcb).Opens),
      (Xcb).unitsRestrict (le_top : O ≤ ⊤)
          (Units.map (p₃).appTop.hom.toMonoidHom
            (Units.map φS.appTop.hom.toMonoidHom w))
        = φX.unitsAppLE ⊤ O le_top (Units.map (p₂).appTop.hom.toMonoidHom w) := by
    intro φS φX hcomm O
    rw [units_map_appTop_comp, ← hcomm, ← units_map_appTop_comp, unitsAppLE_top_global]
  have hface : ∀ (φX : Xcb ⟶ Xq) (a₂ a₁ : Xcb ⟶ XB)
      (h₂ : φX ≫ (u₁) = a₂) (h₁ : φX ≫ (u₂) = a₁) (x : Xcb) (O : (Xcb).Opens)
      (hOx : O ≤ φX ⁻¹ᵁ ((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).opens (φX.base x)))
      (e₂O : O ≤ a₂ ⁻¹ᵁ 𝒜.opens (a₂.base x))
      (e₁O : O ≤ a₁ ⁻¹ᵁ 𝒜.opens (a₁.base x)),
      φX.unitsAppLE ⊤ O le_top (Units.map (p₂).appTop.hom.toMonoidHom w)
        = a₂.unitsAppLE (𝒜.opens (a₂.base x)) O e₂O (β (a₂.base x))
          / a₁.unitsAppLE (𝒜.opens (a₁.base x)) O e₁O (β (a₁.base x)) := by
    intro φX a₂ a₁ h₂ h₁ x O hOx e₂O e₁O
    exact unitsAppLE_div_pullback φX (u₁) (u₂) a₂ a₁ β
      (Units.map (p₂).appTop.hom.toMonoidHom w) hOx x inf_le_left inf_le_right
      (hwloc (φX.base x)) h₂ h₁ e₂O e₁O
  apply Over.appTop_units_injective C (B ⊗[A] (B ⊗[A] B))
  rw [map_mul]
  apply Scheme.global_unit_ext
    (𝒰 := ((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₂₃)
        ⊓ (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₁₂))
      ⊓ (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₁₃))
  intro x
  rw [map_mul]
  rw [hfactor (f₂₃) (w₂₃)
      (Over.snd_left_naturality C
        (Over.overSpecMap (tensorFace₂₃ (k := k) (A := A) (B := B))))
      ((((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₂₃)
          ⊓ (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₁₂))
        ⊓ (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₁₃)).opens x),
    hfactor (f₁₂) (w₁₂)
      (Over.snd_left_naturality C
        (Over.overSpecMap (tensorFace₁₂ (k := k) (A := A) (B := B))))
      ((((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₂₃)
          ⊓ (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₁₂))
        ⊓ (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₁₃)).opens x),
    hfactor (f₁₃) (w₁₃)
      (Over.snd_left_naturality C
        (Over.overSpecMap (tensorFace₁₃ (k := k) (A := A) (B := B))))
      ((((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₂₃)
          ⊓ (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₁₂))
        ⊓ (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₁₃)).opens x),
    hface (w₂₃) (w₂₃ ≫ (u₁)) (w₂₃ ≫ (u₂)) rfl rfl x
      ((((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₂₃)
          ⊓ (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₁₂))
        ⊓ (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₁₃)).opens x)
      (inf_le_left.trans inf_le_left)
      ((inf_le_left.trans inf_le_left).trans ((w₂₃).preimage_mono inf_le_left))
      ((inf_le_left.trans inf_le_left).trans ((w₂₃).preimage_mono inf_le_right)),
    hface (w₁₂) (w₁₂ ≫ (u₁)) (w₂₃ ≫ (u₁))
      rfl (Over.whiskerLeft_face₁₂_inr (k := k) (A := A) (B := B) C) x
      ((((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₂₃)
          ⊓ (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₁₂))
        ⊓ (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₁₃)).opens x)
      (inf_le_left.trans inf_le_right)
      ((inf_le_left.trans inf_le_right).trans ((w₁₂).preimage_mono inf_le_left))
      ((inf_le_left.trans inf_le_left).trans ((w₂₃).preimage_mono inf_le_left)),
    hface (w₁₃) (w₁₂ ≫ (u₁)) (w₂₃ ≫ (u₂))
      (Over.whiskerLeft_face₁₂_inl (k := k) (A := A) (B := B) C).symm
      (Over.whiskerLeft_face₁₃_inr (k := k) (A := A) (B := B) C) x
      ((((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₂₃)
          ⊓ (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₁₂))
        ⊓ (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (w₁₃)).opens x)
      inf_le_right
      ((inf_le_left.trans inf_le_right).trans ((w₁₂).preimage_mono inf_le_left))
      ((inf_le_left.trans inf_le_left).trans ((w₂₃).preimage_mono inf_le_right))]
  exact ratio_mul_cancel _ _ _

/-- The diagonal normalization of the descent unit, from its local ratio form. -/
private lemma diag_of_local (𝒜 : (XB).PointedCover)
    (β : ∀ v : XB, Γ(XB, 𝒜.opens v)ˣ) (w : Γ(Sq, ⊤)ˣ)
    (hwloc : ∀ z : Xq,
      (Xq).unitsRestrict
          (le_top : (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).opens z ≤ ⊤)
          (Units.map (p₂).appTop.hom.toMonoidHom w)
        = (u₁).unitsAppLE (𝒜.opens ((u₁).base z))
            ((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).opens z) inf_le_left (β ((u₁).base z))
          / (u₂).unitsAppLE (𝒜.opens ((u₂).base z))
            ((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).opens z) inf_le_right
            (β ((u₂).base z))) :
    Units.map (Δs).appTop.hom.toMonoidHom w = 1 := by
  apply Over.appTop_units_injective C B
  rw [map_one, units_map_appTop_comp,
    ← Over.snd_left_naturality C
      (Over.overSpecMap (tensorMul (k := k) (A := A) (B := B))),
    ← units_map_appTop_comp]
  apply Scheme.global_unit_ext
    (𝒰 := (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (ΔX))
  intro v
  rw [map_one]
  have h0 := unitsAppLE_top_global (ΔX)
    (le_top : ((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).pullback (ΔX)).opens v ≤ _)
    (Units.map (p₂).appTop.hom.toMonoidHom w)
  have hdiv := unitsAppLE_div_pullback (ΔX) (u₁) (u₂) ((ΔX) ≫ (u₁)) ((ΔX) ≫ (u₁)) β
    (Units.map (p₂).appTop.hom.toMonoidHom w) le_rfl v inf_le_left inf_le_right
    (hwloc ((ΔX).base v)) rfl
    ((whiskerLeft_mul_inr C).trans (whiskerLeft_mul_inl C).symm)
    (le_rfl.trans ((ΔX).preimage_mono inf_le_left))
    (le_rfl.trans ((ΔX).preimage_mono inf_le_left))
  exact h0.symm.trans (hdiv.trans (div_self' _))

/-- **The descent unit of a Čech class killed by the base change (ζ3 brick W).**
Given a unit `0`-cochain `β` on a cover `𝒜` of `X_B` refining the pullback of `ℰ` and
trivializing the pulled-back cocycle of `lam` (hypothesis `hβ`), there is a global unit
`w` on `Spec (B ⊗[A] B)` such that

* the pullback of `w` to the curve product restricts, on the canonical common
  refinement, to the ratio of the two coprojection pullbacks of `β`; and
* the `ΓSpecIso`-avatar of `w` in `(B ⊗[A] B)ˣ` is a descent `1`-cocycle.

The gluing is the ζ2·P toolkit; the Amitsur identity is checked upstairs along the
simplicial coincidences, where the `β`-telescope cancels exactly; the diagonal
normalization is the whiskered degeneracy. -/
theorem exists_kernelDescentUnit
    (ℰ : (XA).PointedCover) (lam : (XA).unitsCocycle ℰ) (𝒜 : (XB).PointedCover)
    (h𝒜 : ∀ v : XB, 𝒜.opens v ≤ (cg) ⁻¹ᵁ ℰ.opens ((cg).base v))
    (β : ∀ v : XB, Γ(XB, 𝒜.opens v)ˣ)
    (hβ : ∀ v v' : XB,
      (XB).unitsRestrict (inf_le_left : 𝒜.opens v ⊓ 𝒜.opens v' ≤ 𝒜.opens v) (β v)
          * (cg).unitsAppLE (ℰ.opens ((cg).base v) ⊓ ℰ.opens ((cg).base v'))
              (𝒜.opens v ⊓ 𝒜.opens v')
              ((cg).le_preimage_inf (inf_le_left.trans (h𝒜 v))
                (inf_le_right.trans (h𝒜 v')))
              (Scheme.unitsEvInf lam ((cg).base v) ((cg).base v'))
        = (XB).unitsRestrict inf_le_right (β v')) :
    ∃ w : Γ(Sq, ⊤)ˣ,
      (∀ z : Xq,
        (Xq).unitsRestrict
            (le_top : (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).opens z ≤ ⊤)
            (Units.map (p₂).appTop.hom.toMonoidHom w)
          = (u₁).unitsAppLE (𝒜.opens ((u₁).base z))
              ((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).opens z)
              inf_le_left (β ((u₁).base z))
            / (u₂).unitsAppLE (𝒜.opens ((u₂).base z))
              ((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).opens z)
              inf_le_right (β ((u₂).base z)))
      ∧ Module.IsDescentCocycle
          (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w) := by
  classical
  obtain ⟨Ψ, hΨ⟩ := Scheme.exists_global_unit_of_compatible
    (𝒰 := 𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂))
    (fun z ↦ (u₁).unitsAppLE (𝒜.opens ((u₁).base z))
        ((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).opens z) inf_le_left (β ((u₁).base z))
      / (u₂).unitsAppLE (𝒜.opens ((u₂).base z))
        ((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).opens z) inf_le_right (β ((u₂).base z)))
    (ratio_compat (cg) (u₁) (u₂)
      ((Over.whiskerLeft_inl_comp_ofId C).trans (Over.whiskerLeft_inr_comp_ofId C).symm)
      ℰ lam 𝒜 h𝒜 β hβ)
  obtain ⟨w, hw⟩ := Over.appTop_units_surjective C (B ⊗[A] B) Ψ
  have hwloc : ∀ z : Xq,
      (Xq).unitsRestrict
          (le_top : (𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).opens z ≤ ⊤)
          (Units.map (p₂).appTop.hom.toMonoidHom w)
        = (u₁).unitsAppLE (𝒜.opens ((u₁).base z))
            ((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).opens z) inf_le_left (β ((u₁).base z))
          / (u₂).unitsAppLE (𝒜.opens ((u₂).base z))
            ((𝒜.pullback (u₁) ⊓ 𝒜.pullback (u₂)).opens z) inf_le_right
            (β ((u₂).base z)) := by
    intro z
    rw [hw]
    exact hΨ z
  refine ⟨w, fun z ↦ hwloc z, ?_⟩
  have hamitsur := amitsur_of_local 𝒜 β w hwloc
  have hdiag := diag_of_local 𝒜 β w hwloc
  have hval : ∀ (σ : B ⊗[A] B →ₐ[k] B ⊗[A] (B ⊗[A] B)),
      (Scheme.ΓSpecIso (.of (B ⊗[A] (B ⊗[A] B)))).hom.hom
          (((Over.overSpecMap σ).left).appTop.hom w.val)
        = σ.toRingHom ((Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom w.val) :=
    fun σ ↦ ΓSpecIso_hom_appTop (CommRingCat.ofHom σ.toRingHom) w.val
  constructor
  · -- normalization: `lmul'` of the avatar is `1`
    have h := ΓSpecIso_hom_appTop
      (CommRingCat.ofHom (tensorMul (k := k) (A := A) (B := B)).toRingHom) w.val
    have hΔval : (Spec.map (CommRingCat.ofHom
          (tensorMul (k := k) (A := A) (B := B)).toRingHom)).appTop.hom w.val = 1 :=
      congrArg Units.val hdiag
    rw [hΔval, map_one] at h
    exact h.symm
  · -- the cocycle identity of the avatar
    have hv : (f₂₃).appTop.hom w.val * (f₁₂).appTop.hom w.val
        = (f₁₃).appTop.hom w.val := by
      have h := congrArg Units.val hamitsur
      rw [Units.val_mul] at h
      exact h
    have e₂₃ := hval (tensorFace₂₃ (k := k) (A := A) (B := B))
    have e₁₂ := hval (tensorFace₁₂ (k := k) (A := A) (B := B))
    have e₁₃ := hval (tensorFace₁₃ (k := k) (A := A) (B := B))
    calc Module.descentFace₂₃ A B
            ((Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w).val)
          * Module.descentFace₁₂ A B
            ((Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w).val)
        = (Scheme.ΓSpecIso (.of (B ⊗[A] (B ⊗[A] B)))).hom.hom ((f₂₃).appTop.hom w.val)
          * (Scheme.ΓSpecIso (.of (B ⊗[A] (B ⊗[A] B)))).hom.hom
            ((f₁₂).appTop.hom w.val) := (congrArg₂ (· * ·) e₂₃ e₁₂).symm
      _ = (Scheme.ΓSpecIso (.of (B ⊗[A] (B ⊗[A] B)))).hom.hom
            ((f₂₃).appTop.hom w.val * (f₁₂).appTop.hom w.val) :=
          (map_mul _ _ _).symm
      _ = (Scheme.ΓSpecIso (.of (B ⊗[A] (B ⊗[A] B)))).hom.hom
            ((f₁₃).appTop.hom w.val) := congrArg _ hv
      _ = Module.descentFace₁₃ A B
            ((Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w).val) :=
          e₁₃

end Over

end AlgebraicGeometry
