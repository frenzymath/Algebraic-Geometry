/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.CategoryTheory.Sites.NonabelianCohomology.H1
import AlgebraicJacobian.Picard.CechH1

/-!
# Unit-valued Čech cocycles on pointed covers and their pullback

This file sets up the cocycle-level substrate of the Čech Picard group
(`AlgebraicJacobian.Picard.Pic`):

* `AlgebraicGeometry.Scheme.PointedCover`: one open per point, containing it; a
  `SemilatticeInf` with an `OrderTop`, refinement `𝒱 ≤ 𝒰 ↔ ∀ x, 𝒱.opens x ≤ 𝒰.opens x`,
  and pullback along a morphism of schemes.
* `AlgebraicGeometry.Scheme.unitsCocycle`, `Scheme.unitsH1`: unit-valued Čech 1-cocycles
  and `H¹` on a pointed cover; `Scheme.unitsRes`: restriction along a refinement, a group
  homomorphism, strictly functorial (`unitsRes_unitsRes`).
* `AlgebraicGeometry.Scheme.unitsEvInf`, `Scheme.unitsRestrict`: the pair values of a
  unit cocycle and restriction of unit sections, retyped through `Γ(X, U)ˣ`. Statements
  phrased through these are honestly `Γ`-typed, so `rw`/`simp` work on them; goals arising
  from the `OneCochain` field types (whose carriers go through `unitsPresheaf.obj`) are
  closed against them by `exact` — the two spellings are definitionally equal.
* `AlgebraicGeometry.Scheme.Hom.pullbackUnitsCocycle`, `Hom.pullbackUnitsH1`: pullback of
  unit cocycles and their `H¹` classes along a morphism of schemes, compatible with
  restriction (`unitsRes_pullbackUnitsH1`) — the substrate for `CechPic.map`.

The file starts with generic `evInf` algebra for `CategoryTheory.PresheafOfGroups`
(values of cochains/cocycles at binary infima commute with `1`, `*`, `⁻¹`); it lives here
only because `CechH1.lean` is at the file-size cap, and should move alongside
`OneCochain.evInf` when that file is split for a mathlib PR.
-/

set_option autoImplicit false

universe w' w u

open CategoryTheory Opposite CategoryTheory.PresheafOfGroups

namespace CategoryTheory.PresheafOfGroups

-- Generic `evInf` algebra; lives here only because `CechH1.lean` is at the file-size cap.
-- Move alongside `OneCochain.evInf` when that file is split for the mathlib PR.

variable {P : Type u} [SemilatticeInf P] {I : Type w'} {G : Pᵒᵖ ⥤ GrpCat.{w}} {U : I → P}

@[simp]
lemma OneCochain.one_evInf (i j : I) : (1 : OneCochain G U).evInf i j = 1 :=
  rfl

@[simp]
lemma OneCochain.mul_evInf (γ₁ γ₂ : OneCochain G U) (i j : I) :
    (γ₁ * γ₂).evInf i j = γ₁.evInf i j * γ₂.evInf i j :=
  rfl

@[simp]
lemma OneCochain.inv_evInf (γ : OneCochain G U) (i j : I) :
    (γ⁻¹).evInf i j = (γ.evInf i j)⁻¹ :=
  rfl

@[simp]
lemma OneCocycle.one_evInf (i j : I) : (1 : OneCocycle G U).evInf i j = 1 :=
  rfl

variable {Gc : Pᵒᵖ ⥤ CommGrpCat.{w}}

@[simp]
lemma OneCocycle.mul_evInf {U : I → P}
    (γ₁ γ₂ : OneCocycle (Gc ⋙ forget₂ CommGrpCat GrpCat) U) (i j : I) :
    (γ₁ * γ₂).evInf i j = γ₁.evInf i j * γ₂.evInf i j :=
  rfl

@[simp]
lemma OneCocycle.inv_evInf {U : I → P}
    (γ : OneCocycle (Gc ⋙ forget₂ CommGrpCat GrpCat) U) (i j : I) :
    (γ⁻¹).evInf i j = (γ.evInf i j)⁻¹ :=
  rfl

end CategoryTheory.PresheafOfGroups
namespace AlgebraicGeometry

namespace Scheme

variable {X Y Z : Scheme.{u}}

/-! ## Pointed covers -/

/-- A pointed open cover of a scheme: one open per point, containing it. Pointed covers
are the index discipline of `Scheme.CechPic`: the index type is the carrier of `X` (so
everything stays in `Type u`), refinement is indexwise, and pointwise `⊓` makes the
refinement order directed. -/
structure PointedCover (X : Scheme.{u}) : Type u where
  /-- The member of the cover attached to a point. -/
  opens : X → X.Opens
  /-- Each point lies in its member. -/
  mem_opens : ∀ x, x ∈ opens x

namespace PointedCover

@[ext]
lemma ext {𝒰 𝒱 : X.PointedCover} (h : ∀ x, 𝒰.opens x = 𝒱.opens x) : 𝒰 = 𝒱 := by
  cases 𝒰; cases 𝒱
  simpa using funext h

instance : SemilatticeInf X.PointedCover where
  le 𝒱 𝒰 := ∀ x, 𝒱.opens x ≤ 𝒰.opens x
  le_refl 𝒰 x := le_rfl
  le_trans 𝒰 𝒱 𝒲 h₁ h₂ x := (h₁ x).trans (h₂ x)
  le_antisymm 𝒰 𝒱 h₁ h₂ := ext fun x ↦ le_antisymm (h₁ x) (h₂ x)
  inf 𝒰 𝒱 :=
    { opens := fun x ↦ 𝒰.opens x ⊓ 𝒱.opens x
      mem_opens := fun x ↦ ⟨𝒰.mem_opens x, 𝒱.mem_opens x⟩ }
  inf_le_left 𝒰 𝒱 x := inf_le_left
  inf_le_right 𝒰 𝒱 x := inf_le_right
  le_inf 𝒰 𝒱 𝒲 h₁ h₂ x := le_inf (h₁ x) (h₂ x)

instance : OrderTop X.PointedCover where
  top := { opens := fun _ ↦ ⊤, mem_opens := fun _ ↦ trivial }
  le_top _ _ := le_top

lemma le_def {𝒰 𝒱 : X.PointedCover} : 𝒱 ≤ 𝒰 ↔ ∀ x, 𝒱.opens x ≤ 𝒰.opens x :=
  Iff.rfl

@[simp]
lemma inf_opens (𝒰 𝒱 : X.PointedCover) (x : X) :
    (𝒰 ⊓ 𝒱).opens x = 𝒰.opens x ⊓ 𝒱.opens x :=
  rfl

@[simp]
lemma top_opens (x : X) : (⊤ : X.PointedCover).opens x = ⊤ :=
  rfl

/-- The pullback of a pointed cover along a morphism of schemes: the pointed cover by
preimages, `x ↦ f ⁻¹ᵁ 𝒰.opens (f x)`. -/
def pullback (f : X ⟶ Y) (𝒰 : Y.PointedCover) : X.PointedCover where
  opens x := f ⁻¹ᵁ 𝒰.opens (f.base x)
  mem_opens x := 𝒰.mem_opens (f.base x)

@[simp]
lemma pullback_opens (f : X ⟶ Y) (𝒰 : Y.PointedCover) (x : X) :
    (𝒰.pullback f).opens x = f ⁻¹ᵁ 𝒰.opens (f.base x) :=
  rfl

lemma pullback_mono (f : X ⟶ Y) {𝒰 𝒱 : Y.PointedCover} (h : 𝒱 ≤ 𝒰) :
    𝒱.pullback f ≤ 𝒰.pullback f :=
  fun x ↦ ((TopologicalSpace.Opens.map f.base).map (homOfLE (h (f.base x)))).le

end PointedCover

/-! ## Unit cocycles on a pointed cover and their restriction -/

/-- The unit-valued Čech 1-cocycles of `X` on a pointed cover. -/
abbrev unitsCocycle (X : Scheme.{u}) (𝒰 : X.PointedCover) : Type u :=
  PresheafOfGroups.OneCocycle (X.unitsPresheaf ⋙ forget₂ CommGrpCat GrpCat) 𝒰.opens

/-- The unit-valued Čech `H¹` of `X` on a pointed cover. -/
abbrev unitsH1 (X : Scheme.{u}) (𝒰 : X.PointedCover) : Type u :=
  PresheafOfGroups.H1 (X.unitsPresheaf ⋙ forget₂ CommGrpCat GrpCat) 𝒰.opens

/-- Restriction of unit Čech classes along a refinement of pointed covers, as a group
homomorphism. -/
def unitsRes {𝒰 𝒱 : X.PointedCover} (h : 𝒱 ≤ 𝒰) : X.unitsH1 𝒰 →* X.unitsH1 𝒱 :=
  H1.resHom fun x ↦ homOfLE (h x)

/-- Restriction along refinements of pointed covers is strictly functorial. -/
@[simp]
lemma unitsRes_unitsRes {𝒰 𝒱 𝒲 : X.PointedCover} (h₁ : 𝒱 ≤ 𝒰) (h₂ : 𝒲 ≤ 𝒱)
    (a : X.unitsH1 𝒰) : unitsRes h₂ (unitsRes h₁ a) = unitsRes (h₂.trans h₁) a :=
  H1.res_res _ _ a

@[simp]
lemma unitsRes_rfl {𝒰 : X.PointedCover} {h : 𝒰 ≤ 𝒰} (a : X.unitsH1 𝒰) :
    unitsRes h a = a :=
  H1.res_id a
/-- If `U` is contained in the preimages of two opens, it is contained in the preimage
of their intersection. -/
lemma Hom.le_preimage_inf (f : X.Hom Y) {U : X.Opens} {V₁ V₂ : Y.Opens}
    (h₁ : U ≤ f ⁻¹ᵁ V₁) (h₂ : U ≤ f ⁻¹ᵁ V₂) : U ≤ f ⁻¹ᵁ (V₁ ⊓ V₂) :=
  fun _ hx ↦ ⟨h₁ hx, h₂ hx⟩

/-- The pair value `γ.evInf i j` of a unit Čech cocycle, retyped as a unit section in
`Γ(X, 𝒰.opens i ⊓ 𝒰.opens j)ˣ` (definitionally equal). Statements phrased through
`unitsEvInf` are honestly `Γ`-typed, so `rw`/`simp` work on them; goals arising from the
`OneCochain` field types are closed against them by `exact` (definitional bridging). -/
def unitsEvInf {𝒰 : X.PointedCover} (γ : X.unitsCocycle 𝒰) (i j : X) :
    Γ(X, 𝒰.opens i ⊓ 𝒰.opens j)ˣ :=
  γ.evInf i j

/-- Restriction of a unit section along `W ≤ U`, as a group homomorphism between the
honest `Γ`-typed unit groups (definitionally the units-presheaf restriction map). -/
abbrev unitsRestrict (X : Scheme.{u}) {U W : X.Opens} (h : W ≤ U) :
    Γ(X, U)ˣ →* Γ(X, W)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom

@[simp]
lemma one_unitsEvInf {𝒰 : X.PointedCover} (i j : X) :
    unitsEvInf (1 : X.unitsCocycle 𝒰) i j = 1 :=
  rfl

@[simp]
lemma mul_unitsEvInf {𝒰 : X.PointedCover} (γ₁ γ₂ : X.unitsCocycle 𝒰) (i j : X) :
    unitsEvInf (γ₁ * γ₂) i j = unitsEvInf γ₁ i j * unitsEvInf γ₂ i j :=
  rfl

/-- The cocycle identity for the pair values, in unit-section language. -/
lemma unitsEvInf_trans {𝒰 : X.PointedCover} (γ : X.unitsCocycle 𝒰) (i j k : X) :
    X.unitsRestrict (inf_le_left :
          𝒰.opens i ⊓ 𝒰.opens j ⊓ 𝒰.opens k ≤ 𝒰.opens i ⊓ 𝒰.opens j)
        (unitsEvInf γ i j)
      * X.unitsRestrict (inf_le_inf_right _ inf_le_right :
          𝒰.opens i ⊓ 𝒰.opens j ⊓ 𝒰.opens k ≤ 𝒰.opens j ⊓ 𝒰.opens k)
          (unitsEvInf γ j k)
      = X.unitsRestrict (inf_le_inf_right _ inf_le_left :
          𝒰.opens i ⊓ 𝒰.opens j ⊓ 𝒰.opens k ≤ 𝒰.opens i ⊓ 𝒰.opens k)
          (unitsEvInf γ i k) :=
  γ.evInf_trans i j k

/-- Restriction along a refinement, at the level of pair values. -/
lemma res_unitsEvInf {𝒲 𝒰 : X.PointedCover} (hle : 𝒲 ≤ 𝒰) (γ : X.unitsCocycle 𝒰)
    (i j : X) :
    unitsEvInf (γ.res fun k ↦ homOfLE (hle k)) i j
      = X.unitsRestrict (inf_le_inf (hle i) (hle j)) (unitsEvInf γ i j) :=
  γ.res_evInf _ i j
namespace Hom

variable (f : X ⟶ Y) {𝒰 𝒲 : Y.PointedCover}

/-- Pullback of the cocycle identity: the pair values of a unit cocycle on `Y`, pulled
back through `f : X ⟶ Y` to a common open `T`, still satisfy the cocycle identity. -/
private lemma pullback_pair_trans (f : X ⟶ Y) {𝒰 : Y.PointedCover}
    (γ : Y.unitsCocycle 𝒰) (i j k : Y) {T : X.Opens}
    (e₁ : T ≤ f ⁻¹ᵁ (𝒰.opens i ⊓ 𝒰.opens j)) (e₂ : T ≤ f ⁻¹ᵁ (𝒰.opens j ⊓ 𝒰.opens k))
    (e₃ : T ≤ f ⁻¹ᵁ (𝒰.opens i ⊓ 𝒰.opens k)) :
    f.unitsAppLE (𝒰.opens i ⊓ 𝒰.opens j) T e₁ (unitsEvInf γ i j)
      * f.unitsAppLE (𝒰.opens j ⊓ 𝒰.opens k) T e₂ (unitsEvInf γ j k)
      = f.unitsAppLE (𝒰.opens i ⊓ 𝒰.opens k) T e₃ (unitsEvInf γ i k) := by
  have E : T ≤ f ⁻¹ᵁ (𝒰.opens i ⊓ 𝒰.opens j ⊓ 𝒰.opens k) :=
    fun t ht ↦ ⟨e₁ ht, (e₂ ht).2⟩
  have ht := congrArg (f.unitsAppLE (𝒰.opens i ⊓ 𝒰.opens j ⊓ 𝒰.opens k) T E)
    (unitsEvInf_trans γ i j k)
  rw [map_mul, Scheme.Hom.map_unitsAppLE, Scheme.Hom.map_unitsAppLE,
    Scheme.Hom.map_unitsAppLE] at ht
  exact ht

/-- The pullback of a unit 1-cocycle along a morphism of schemes, on the pulled-back
pointed cover. -/
def pullbackUnitsCocycle (f : X ⟶ Y) (γ : Y.unitsCocycle 𝒰) :
    X.unitsCocycle (𝒰.pullback f) where
  ev x y _ a b :=
    f.unitsAppLE (𝒰.opens (f.base x) ⊓ 𝒰.opens (f.base y)) _
      (f.le_preimage_inf a.le b.le) (unitsEvInf γ (f.base x) (f.base y))
  ev_precomp x y _ _ φ a b :=
    f.unitsAppLE_map (f.le_preimage_inf a.le b.le) φ.op
      (unitsEvInf γ (f.base x) (f.base y))
  ev_trans x y z _ a b c :=
    pullback_pair_trans f γ (f.base x) (f.base y) (f.base z)
      (f.le_preimage_inf a.le b.le) (f.le_preimage_inf b.le c.le)
      (f.le_preimage_inf a.le c.le)

@[simp]
lemma pullbackUnitsCocycle_ev (γ : Y.unitsCocycle 𝒰) (x y : X) {T : X.Opens}
    (a : T ⟶ (𝒰.pullback f).opens x) (b : T ⟶ (𝒰.pullback f).opens y) :
    (f.pullbackUnitsCocycle γ).ev x y a b
      = f.unitsAppLE (𝒰.opens (f.base x) ⊓ 𝒰.opens (f.base y)) T
          (f.le_preimage_inf a.le b.le) (unitsEvInf γ (f.base x) (f.base y)) :=
  rfl

@[simp]
lemma pullbackUnitsCocycle_unitsEvInf (γ : Y.unitsCocycle 𝒰) (x y : X) :
    unitsEvInf (f.pullbackUnitsCocycle γ) x y
      = f.unitsAppLE (𝒰.opens (f.base x) ⊓ 𝒰.opens (f.base y))
          ((𝒰.pullback f).opens x ⊓ (𝒰.pullback f).opens y)
          (f.le_preimage_inf inf_le_left inf_le_right)
          (unitsEvInf γ (f.base x) (f.base y)) :=
  rfl

@[simp]
lemma pullbackUnitsCocycle_one :
    f.pullbackUnitsCocycle (1 : Y.unitsCocycle 𝒰) = 1 := by
  ext x y T a b
  exact map_one (f.unitsAppLE (𝒰.opens (f.base x) ⊓ 𝒰.opens (f.base y)) T
    (f.le_preimage_inf a.le b.le))

@[simp]
lemma pullbackUnitsCocycle_mul (γ₁ γ₂ : Y.unitsCocycle 𝒰) :
    f.pullbackUnitsCocycle (γ₁ * γ₂)
      = f.pullbackUnitsCocycle γ₁ * f.pullbackUnitsCocycle γ₂ := by
  ext x y T a b
  exact map_mul (f.unitsAppLE (𝒰.opens (f.base x) ⊓ 𝒰.opens (f.base y)) T
      (f.le_preimage_inf a.le b.le))
    (unitsEvInf γ₁ (f.base x) (f.base y)) (unitsEvInf γ₂ (f.base x) (f.base y))

/-- Pullback of unit cocycles commutes with restriction along a refinement. -/
lemma pullbackUnitsCocycle_res (h : 𝒲 ≤ 𝒰) (γ : Y.unitsCocycle 𝒰) :
    (f.pullbackUnitsCocycle γ).res (fun x ↦ homOfLE (PointedCover.pullback_mono f h x))
      = f.pullbackUnitsCocycle (γ.res (fun y ↦ homOfLE (h y))) := by
  ext x y T a b
  have h₁ := congrArg
    (f.unitsAppLE (𝒲.opens (f.base x) ⊓ 𝒲.opens (f.base y)) T
      (f.le_preimage_inf a.le b.le))
    (res_unitsEvInf h γ (f.base x) (f.base y))
  rw [Scheme.Hom.map_unitsAppLE] at h₁
  exact h₁.symm

/-- Pullback of a single coboundary comparison along a morphism of schemes: the honest
`Γ`-typed computation behind `pullbackUnitsCocycle_isCohomologous`. -/
private lemma pullback_coboundary (f : X ⟶ Y) {𝒰 : Y.PointedCover}
    (γ₁ γ₂ : Y.unitsCocycle 𝒰) (α : ∀ i : Y, Γ(Y, 𝒰.opens i)ˣ)
    (hα : ∀ i j, Y.unitsRestrict (inf_le_left : 𝒰.opens i ⊓ 𝒰.opens j ≤ 𝒰.opens i) (α i)
          * unitsEvInf γ₁ i j
        = unitsEvInf γ₂ i j
          * Y.unitsRestrict (inf_le_right : 𝒰.opens i ⊓ 𝒰.opens j ≤ 𝒰.opens j) (α j))
    (x y : X) {T : X.Opens}
    (ha : T ≤ (𝒰.pullback f).opens x) (hb : T ≤ (𝒰.pullback f).opens y) :
    X.unitsRestrict ha
        (f.unitsAppLE (𝒰.opens (f.base x)) ((𝒰.pullback f).opens x) le_rfl
          (α (f.base x)))
      * f.unitsAppLE (𝒰.opens (f.base x) ⊓ 𝒰.opens (f.base y)) T
          (f.le_preimage_inf ha hb) (unitsEvInf γ₁ (f.base x) (f.base y))
      = f.unitsAppLE (𝒰.opens (f.base x) ⊓ 𝒰.opens (f.base y)) T
          (f.le_preimage_inf ha hb) (unitsEvInf γ₂ (f.base x) (f.base y))
        * X.unitsRestrict hb
            (f.unitsAppLE (𝒰.opens (f.base y)) ((𝒰.pullback f).opens y) le_rfl
              (α (f.base y))) := by
  have h' := congrArg
    (f.unitsAppLE (𝒰.opens (f.base x) ⊓ 𝒰.opens (f.base y)) T (f.le_preimage_inf ha hb))
    (hα (f.base x) (f.base y))
  rw [map_mul, map_mul, Scheme.Hom.map_unitsAppLE, Scheme.Hom.map_unitsAppLE] at h'
  rw [Scheme.Hom.unitsAppLE_map, Scheme.Hom.unitsAppLE_map]
  exact h'

/-- Pullback of a cohomology relation along a morphism of schemes. -/
lemma pullbackUnitsCocycle_isCohomologous {γ₁ γ₂ : Y.unitsCocycle 𝒰}
    (h : γ₁.IsCohomologous γ₂) :
    (f.pullbackUnitsCocycle γ₁).IsCohomologous (f.pullbackUnitsCocycle γ₂) := by
  obtain ⟨α, hα⟩ := h
  exact ⟨fun x ↦ f.unitsAppLE (𝒰.opens (f.base x)) ((𝒰.pullback f).opens x) le_rfl
      (α (f.base x)),
    fun x y T a b ↦ pullback_coboundary f γ₁ γ₂ α
      (fun i j ↦ hα i j (homOfLE inf_le_left) (homOfLE inf_le_right)) x y a.le b.le⟩

/-- The pullback of unit Čech `H¹` classes along a morphism of schemes. -/
def pullbackUnitsH1 (f : X ⟶ Y) (𝒰 : Y.PointedCover) :
    Y.unitsH1 𝒰 →* X.unitsH1 (𝒰.pullback f) where
  toFun := Quot.map f.pullbackUnitsCocycle
    (fun _ _ h ↦ f.pullbackUnitsCocycle_isCohomologous h)
  map_one' := congrArg OneCocycle.class f.pullbackUnitsCocycle_one
  map_mul' a b := by
    induction a using Quot.ind with | _ γ₁ =>
    induction b using Quot.ind with | _ γ₂ =>
    exact congrArg (Quot.mk _) (f.pullbackUnitsCocycle_mul γ₁ γ₂)

@[simp]
lemma pullbackUnitsH1_class (γ : Y.unitsCocycle 𝒰) :
    f.pullbackUnitsH1 𝒰 γ.class = (f.pullbackUnitsCocycle γ).class :=
  rfl

/-- Pullback of unit `H¹` classes commutes with restriction along a refinement. -/
lemma unitsRes_pullbackUnitsH1 (h : 𝒲 ≤ 𝒰) (a : Y.unitsH1 𝒰) :
    unitsRes (PointedCover.pullback_mono f h) (f.pullbackUnitsH1 𝒰 a)
      = f.pullbackUnitsH1 𝒲 (unitsRes h a) := by
  induction a using Quot.ind with
  | _ γ => exact congrArg (Quot.mk _) (f.pullbackUnitsCocycle_res h γ)

end Hom

end Scheme

end AlgebraicGeometry
