/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.WitnessComponents
import AlgebraicJacobian.Algebra.TensorAway

/-!
# Section rings on basic opens of the tensor towers as two-base localizations (ζ2·ii)

The `ΓSpecIso` crossing of the ζ2·ii pi-assembly, fixed once and for all (see the design
note below), together with the resulting identifications of the tensor products
`S i ⊗[A] S j` and `S i ⊗[A] (S j ⊗[A] S l)` of the basic-open section rings
`S i := Γ(Spec B, D(P.r i))` with the section rings on the double/triple basic opens of
`Spec (B ⊗[A] B)` / `Spec (B ⊗[A] (B ⊗[A] B))`:

* `AlgebraicGeometry.isLocalization_away_sections`: the section ring on `D(g)` is the
  `Away` localization of the ring `R` itself, at the element `ΓSpecIso.hom g : R`;
* `AlgebraicGeometry.Over.awayElt`: the element of `B` cutting out `D(P.r i)`;
* `AlgebraicGeometry.Over.ΓSpecIso_hom_pairSection` / `ΓSpecIso_hom_tripleSection`: the
  localization elements of the double/triple basic opens are the tensor elements
  `(bᵢ ⊗ 1)(1 ⊗ bⱼ)` (via `ΓSpecIso`-naturality applied to the coprojections and the
  three insertions);
* `AlgebraicGeometry.Over.pairAwayEquiv` / `Over.tripleAwayEquiv`: the two-base
  localization identifications (`IsLocalization.Away.tensorAwayEquiv` of
  `AlgebraicJacobian.Algebra.TensorAway`, at the transported `Away` instances).

## The `ΓSpecIso` crossing (design decision, fixed once here)

All section rings of `Spec R` (`R` any of `B`, `B ⊗[A] B`, `B ⊗[A] (B ⊗[A] B)`) carry
the canonical `R`-algebra structure whose structure map is **definitionally**
`ΓSpecIso.inv` followed by restriction (`specSectionsAlgebra`, keyed on the bare ring so
instance search finds it; since `(overSpec k R).left = Spec (.of R)` holds by `rfl` the
re-keyed forms apply on the nose).  The bridge between the scheme-side base rings
`Γ(Spec R, ⊤)` and the algebra-side rings `R` is crossed exactly twice, abstractly: by
`isLocalization_away_sections` (transport of the canonical localization along `ΓSpecIso`
via `IsLocalization.of_ringEquiv_left`) and by the elementwise naturality lemmas
`ΓSpecIso_hom_appTop` / `ΓSpecIso_inv_appTop`.  The `A`-algebra structures on the
section rings are the composites through the canonical `R`-structures
(`algebraA_sections`); all of these are `local instance`s — consumers reactivate them
with `attribute [local instance]`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry

/-! ## Section rings on basic opens as localizations of the ring itself -/

/-- Elementwise `ΓSpecIso`-naturality: `ΓSpecIso.hom` intertwines `(Spec.map f).appTop`
with `f`. -/
lemma ΓSpecIso_hom_appTop {R S : CommRingCat.{u}} (f : R ⟶ S) (x : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso S).hom.hom ((Spec.map f).appTop.hom x)
      = f.hom ((Scheme.ΓSpecIso R).hom.hom x) := by
  have h := congrArg (fun (g : Γ(Spec R, ⊤) ⟶ S) => g.hom x) (Scheme.ΓSpecIso_naturality f)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h

/-- Elementwise round-trip of `ΓSpecIso`. -/
lemma ΓSpecIso_inv_hom (R : CommRingCat.{u}) (x : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso R).inv.hom ((Scheme.ΓSpecIso R).hom.hom x) = x := by
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

/-- The canonical `R`-algebra structure on the section rings of `Spec R` — the structure
map is `ΓSpecIso.inv` followed by restriction, definitionally as in mathlib's
`algebraMap_Spec_obj` — keyed on the bare ring `R` rather than on `↑(CommRingCat.of R)`
so that instance search finds it (local to this file). -/
noncomputable local instance specSectionsAlgebra (R : Type u) [CommRing R]
    (U : (Spec (CommRingCat.of R)).Opens) : Algebra R Γ(Spec (CommRingCat.of R), U) :=
  (((Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top).op).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra

/-- **The section ring on a basic open of `Spec R` is an `Away` localization of `R`
itself**, at the `ΓSpecIso`-image of the cutting section: the transport of the canonical
`Γ(Spec R, ⊤)`-localization structure along `ΓSpecIso`. -/
theorem isLocalization_away_sections (R : Type u) [CommRing R]
    (g : Γ(Spec (CommRingCat.of R), ⊤)) :
    IsLocalization.Away ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom g)
      Γ(Spec (CommRingCat.of R), (Spec (CommRingCat.of R)).basicOpen g) := by
  set e : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm with he
  refine IsLocalization.of_ringEquiv_left e
    (M₁ := Submonoid.powers g)
    (M₂ := Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom g)) ?_ ?_
  · rw [Submonoid.map_powers]
    congr 1
    exact ΓSpecIso_inv_hom (CommRingCat.of R) g
  · intro x
    rfl


/-! ## The concrete ζ2·ii context -/

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

/-- `specSectionsAlgebra`, re-keyed on the `overSpec`-spelling of `Spec B` (local). -/
noncomputable local instance overSpecSectionsAlgebra (U : (XB).Opens) :
    Algebra B Γ(XB, U) :=
  specSectionsAlgebra B U

/-- `specSectionsAlgebra`, re-keyed on the `overSpec`-spelling of `Spec (B ⊗[A] B)`
(local). -/
noncomputable local instance overSpecSectionsAlgebraSq (U : (Sq).Opens) :
    Algebra (B ⊗[A] B) Γ(Sq, U) :=
  specSectionsAlgebra (B ⊗[A] B) U

/-- `specSectionsAlgebra`, re-keyed on the `overSpec`-spelling of
`Spec (B ⊗[A] (B ⊗[A] B))` (local). -/
noncomputable local instance overSpecSectionsAlgebraScb (U : (Scb).Opens) :
    Algebra (B ⊗[A] (B ⊗[A] B)) Γ(Scb, U) :=
  specSectionsAlgebra (B ⊗[A] (B ⊗[A] B)) U

/-- The `A`-algebra structure on the section rings of `Spec B`, composed through the
canonical `B`-structure (local to this file). -/
noncomputable local instance algebraA_sections (U : (XB).Opens) : Algebra A Γ(XB, U) :=
  ((algebraMap B Γ(XB, U)).comp (algebraMap A B)).toAlgebra

local instance isScalarTower_sections (U : (XB).Opens) :
    IsScalarTower A B Γ(XB, U) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The scalar tower `A → Γ(Spec B, ⊤) → Γ(Spec B, D(g))`: the two composed
`A`-structures agree because the two-step restriction `⊤ → ⊤ → D(g)` is the one-step
restriction. -/
local instance isScalarTower_sections_basicOpen (g : Γ(XB, ⊤)) :
    IsScalarTower A Γ(XB, ⊤) Γ(XB, (XB).basicOpen g) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    change (XB).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a))
      = (XB).presheaf.map (homOfLE ((XB).basicOpen_le g)).op
          ((XB).presheaf.map (homOfLE le_top).op
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a)))
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- Elementwise inverse `ΓSpecIso`-naturality: `ΓSpecIso.inv` intertwines `f` with
`appTop` of `Spec.map f`. -/
lemma ΓSpecIso_inv_appTop {R S : CommRingCat.{u}} (f : R ⟶ S) (x : R) :
    (Spec.map f).appTop.hom ((Scheme.ΓSpecIso R).inv.hom x)
      = (Scheme.ΓSpecIso S).inv.hom (f.hom x) := by
  have h := congrArg (fun (g : R ⟶ Γ(Spec S, ⊤)) => g.hom x)
    (Scheme.ΓSpecIso_inv_naturality f)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h.symm

/-- Elementwise form of `appLE` applied to a restricted global section:
`f^♯(z|_V)|_U = (f^♯z)|_U`. -/
lemma appLE_restrict_top {X Y : Scheme.{u}} (f : X ⟶ Y) {V : Y.Opens}
    {U : X.Opens} (e : U ≤ f ⁻¹ᵁ V) (z : Γ(Y, ⊤)) :
    (f.appLE V U e).hom ((Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom z)
      = (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (f.appTop.hom z) := by
  have h := congrArg (fun (φ : Γ(Y, ⊤) ⟶ Γ(X, U)) => φ.hom z)
    (Scheme.Hom.map_appLE f e (homOfLE (le_top : V ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h.trans rfl

namespace Over

variable {𝒩 : ((overSpec k B).left).PointedCover}
variable {γ : ((overSpec k B).left).unitsCocycle 𝒩}
variable (P : 𝒩.BasicRefinement)

/-! ## The localization elements and the two-base localization identifications -/

/-- The element of `B` cutting out the basic open `D(P.r i)` — the `ΓSpecIso`-image of
the cutting section. -/
noncomputable def awayElt (i : P.ι) : B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (P.r i)

/-- The section rings on the basic opens are `Away` models over `B` itself. -/
lemma isLocalization_awayElt (i : P.ι) :
    IsLocalization.Away (awayElt P i) Γ(XB, (XB).basicOpen (P.r i)) :=
  isLocalization_away_sections B (P.r i)

/-- Elementwise composite of `appTop`s. -/
private lemma appTop_appTop {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Γ(Z, ⊤)) : f.appTop.hom (g.appTop.hom x) = (f ≫ g).appTop.hom x := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

set_option linter.unusedSectionVars false in
/-- `ΓSpecIso` intertwines `q₁^♯` with `tensorInl` (defeq instance of naturality). -/
private lemma hom_q₁_appTop (x : Γ(XB, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] B))).hom.hom ((q₁).appTop.hom x)
      = ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom x) ⊗ₜ[A] (1 : B) :=
  ΓSpecIso_hom_appTop (CommRingCat.ofHom (tensorInl (A := A) (B := B)).toRingHom) x

/-- `ΓSpecIso` intertwines `q₂^♯` with `tensorInr` (defeq instance of naturality). -/
private lemma hom_q₂_appTop (x : Γ(XB, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] B))).hom.hom ((q₂).appTop.hom x)
      = (1 : B) ⊗ₜ[A] ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom x) :=
  ΓSpecIso_hom_appTop (CommRingCat.ofHom (tensorInr (A := A) (B := B)).toRingHom) x

/-- `ΓSpecIso` intertwines `f₁₂^♯` with `tensorFace₁₂` (defeq instance of naturality). -/
private lemma hom_f₁₂_appTop (y : Γ(Sq, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))).hom.hom ((f₁₂).appTop.hom y)
      = tensorFace₁₂ (k := k) (A := A) (B := B)
          ((Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] B))).hom.hom y) :=
  ΓSpecIso_hom_appTop
    (CommRingCat.ofHom (tensorFace₁₂ (k := k) (A := A) (B := B)).toRingHom) y

/-- `ΓSpecIso` intertwines `f₁₃^♯` with `tensorFace₁₃` (defeq instance of naturality). -/
private lemma hom_f₁₃_appTop (y : Γ(Sq, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))).hom.hom ((f₁₃).appTop.hom y)
      = tensorFace₁₃ (k := k) (A := A) (B := B)
          ((Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] B))).hom.hom y) :=
  ΓSpecIso_hom_appTop
    (CommRingCat.ofHom (tensorFace₁₃ (k := k) (A := A) (B := B)).toRingHom) y

/-- The composite intertwining for the insertion `f₁₂ ≫ q₁`. -/
private lemma hom_f₁₂_q₁_appTop (x : Γ(XB, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))).hom.hom
        ((f₁₂).appTop.hom ((q₁).appTop.hom x))
      = ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom x)
          ⊗ₜ[A] ((1 : B) ⊗ₜ[A] (1 : B)) := by
  refine (hom_f₁₂_appTop ((q₁).appTop.hom x)).trans ?_
  refine (congrArg (tensorFace₁₂ (k := k) (A := A) (B := B)) (hom_q₁_appTop x)).trans ?_
  rfl

/-- The composite intertwining for the insertion `f₁₂ ≫ q₂`. -/
private lemma hom_f₁₂_q₂_appTop (x : Γ(XB, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))).hom.hom
        ((f₁₂).appTop.hom ((q₂).appTop.hom x))
      = (1 : B) ⊗ₜ[A]
          (((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom x) ⊗ₜ[A] (1 : B)) := by
  refine (hom_f₁₂_appTop ((q₂).appTop.hom x)).trans ?_
  refine (congrArg (tensorFace₁₂ (k := k) (A := A) (B := B)) (hom_q₂_appTop x)).trans ?_
  rfl

/-- The composite intertwining for the insertion `f₁₃ ≫ q₂`. -/
private lemma hom_f₁₃_q₂_appTop (x : Γ(XB, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))).hom.hom
        ((f₁₃).appTop.hom ((q₂).appTop.hom x))
      = (1 : B) ⊗ₜ[A]
          ((1 : B) ⊗ₜ[A] ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom x)) := by
  refine (hom_f₁₃_appTop ((q₂).appTop.hom x)).trans ?_
  refine (congrArg (tensorFace₁₃ (k := k) (A := A) (B := B)) (hom_q₂_appTop x)).trans ?_
  rfl

/-- The `ΓSpecIso`-image of `pairSection` is the two-base localization element
`(awayElt i ⊗ 1) ⋅ (1 ⊗ awayElt j)`. -/
lemma ΓSpecIso_hom_pairSection (i j : P.ι) :
    (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] B))).hom.hom (pairSection P i j)
      = (awayElt P i ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] awayElt P j) :=
  ((congrArg _ (pairSection_def P i j)).trans (map_mul _ _ _)).trans
    (congrArg₂ (· * ·) (hom_q₁_appTop (P.r i)) (hom_q₂_appTop (P.r j)))

/-- The tensor-element identity finishing `ΓSpecIso_hom_tripleSection` (pure algebra). -/
private lemma triple_elt_eq (x y z : B) :
    (x ⊗ₜ[A] ((1 : B) ⊗ₜ[A] (1 : B)))
        * (((1 : B) ⊗ₜ[A] (y ⊗ₜ[A] (1 : B))) * ((1 : B) ⊗ₜ[A] ((1 : B) ⊗ₜ[A] z)))
      = (x ⊗ₜ[A] (1 : B ⊗[A] B))
        * ((1 : B) ⊗ₜ[A] ((y ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] z))) := by
  simp only [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def,
    one_mul, mul_one]

/-- The `ΓSpecIso`-image of `tripleSection` is the two-base localization element of the
triple tensor, in the shape consumed by `isLocalization_away_tensor`. -/
lemma ΓSpecIso_hom_tripleSection (i j l : P.ι) :
    (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))).hom.hom (tripleSection P i j l)
      = (awayElt P i ⊗ₜ[A] (1 : B ⊗[A] B))
        * ((1 : B) ⊗ₜ[A] ((awayElt P j ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] awayElt P l))) := by
  have e₁ : tripleSection P i j l
      = (f₁₂).appTop.hom ((q₁).appTop.hom (P.r i))
        * ((f₁₂).appTop.hom ((q₂).appTop.hom (P.r j))
          * (f₁₃).appTop.hom ((q₂).appTop.hom (P.r l))) := by
    rw [tripleSection_def, appTop_appTop (f₁₂) (q₁), appTop_appTop (f₁₂) (q₂),
      appTop_appTop (f₁₃) (q₂)]
  refine ((congrArg _ e₁).trans (map_mul _ _ _)).trans ?_
  refine (congrArg₂ (· * ·) (hom_f₁₂_q₁_appTop (P.r i))
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hom_f₁₂_q₂_appTop (P.r j))
      (hom_f₁₃_q₂_appTop (P.r l))))).trans ?_
  exact triple_elt_eq (awayElt P i) (awayElt P j) (awayElt P l)

open IsLocalization.Away in
/-- The two-base localization identification of `S i ⊗[A] S j` with the section ring on
the double basic open of the tensor square. -/
noncomputable def pairAwayEquiv (i j : P.ι) :
    letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r i))
      Γ(XB, (XB).basicOpen (P.r j))
    (Γ(XB, (XB).basicOpen (P.r i)) ⊗[A] Γ(XB, (XB).basicOpen (P.r j)))
      ≃ₐ[B ⊗[A] B] Γ(Sq, (Sq).basicOpen (pairSection P i j)) :=
  haveI := isLocalization_awayElt P i
  haveI := isLocalization_awayElt P j
  haveI : IsLocalization.Away
      ((awayElt P i ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] awayElt P j))
      Γ(Sq, (Sq).basicOpen (pairSection P i j)) := by
    have h := isLocalization_away_sections (B ⊗[A] B) (pairSection P i j)
    rwa [ΓSpecIso_hom_pairSection P i j] at h
  tensorAwayEquiv A B B (awayElt P i) (awayElt P j)
    Γ(XB, (XB).basicOpen (P.r i)) Γ(XB, (XB).basicOpen (P.r j))
    Γ(Sq, (Sq).basicOpen (pairSection P i j))

open IsLocalization.Away in
/-- The two-base localization identification of `S i ⊗[A] (S j ⊗[A] S l)` with the
section ring on the triple basic open of the triple tensor. -/
noncomputable def tripleAwayEquiv (i j l : P.ι) :
    letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r j))
      Γ(XB, (XB).basicOpen (P.r l))
    haveI := IsLocalization.Away.tensorAwayScalarTower A B B Γ(XB, (XB).basicOpen (P.r j))
      Γ(XB, (XB).basicOpen (P.r l))
    letI := IsLocalization.Away.tensorAwayAlgebra A B (B ⊗[A] B) Γ(XB, (XB).basicOpen (P.r i))
      (Γ(XB, (XB).basicOpen (P.r j)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l)))
    (Γ(XB, (XB).basicOpen (P.r i))
        ⊗[A] (Γ(XB, (XB).basicOpen (P.r j)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l))))
      ≃ₐ[B ⊗[A] (B ⊗[A] B)] Γ(Scb, (Scb).basicOpen (tripleSection P i j l)) :=
  letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r j))
    Γ(XB, (XB).basicOpen (P.r l))
  haveI := IsLocalization.Away.tensorAwayScalarTower A B B Γ(XB, (XB).basicOpen (P.r j))
    Γ(XB, (XB).basicOpen (P.r l))
  haveI := isLocalization_awayElt P i
  haveI := isLocalization_awayElt P j
  haveI := isLocalization_awayElt P l
  haveI := isLocalization_away_tensor A B B (awayElt P j) (awayElt P l)
    Γ(XB, (XB).basicOpen (P.r j)) Γ(XB, (XB).basicOpen (P.r l))
  haveI : IsLocalization.Away
      ((awayElt P i ⊗ₜ[A] (1 : B ⊗[A] B))
        * ((1 : B) ⊗ₜ[A] ((awayElt P j ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] awayElt P l))))
      Γ(Scb, (Scb).basicOpen (tripleSection P i j l)) := by
    have h := isLocalization_away_sections (B ⊗[A] (B ⊗[A] B)) (tripleSection P i j l)
    rwa [ΓSpecIso_hom_tripleSection P i j l] at h
  tensorAwayEquiv A B (B ⊗[A] B) (awayElt P i)
    ((awayElt P j ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] awayElt P l))
    Γ(XB, (XB).basicOpen (P.r i))
    (Γ(XB, (XB).basicOpen (P.r j)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l)))
    Γ(Scb, (Scb).basicOpen (tripleSection P i j l))

end Over

end AlgebraicGeometry
