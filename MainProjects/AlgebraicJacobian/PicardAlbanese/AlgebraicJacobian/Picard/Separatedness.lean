/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RefinementInjectivity
import AlgebraicJacobian.Picard.UniversalSections

/-!
# Separatedness brick 3: pullback along the projection is injective on Picard groups

For `C` proper, geometrically irreducible and geometrically reduced over a field `k` and
**any** test object `T` over `Spec k`, pullback of Čech Picard classes along the second
projection `pr : (C ⊗ T).left ⟶ T.left` is injective
(`AlgebraicGeometry.Over.prPullback_injective`) — brick 3 of the separatedness ledger
(design §4.4), the cocycle recast of "a line bundle pulled back from the base which
trivializes on the product was trivial", the projection step of Kleiman,
*The Picard Scheme*, Theorem 2.5(1).

## The section-level engine

Everything reduces to the section rings: for an **affine** open `V ⊆ T.left`, pullback of
sections along the projection is bijective,
`Γ(T.left, V) ≅ Γ((C ⊗ T).left, pr⁻¹ V)` (`Over.isIso_appLE_snd`). This is brick 2
(`Over.isIso_appTop_snd_overSpec`, `Picard/UniversalSections.lean`) freed from its
`T = Spec A`, `V = ⊤` special case: the qcqs pushout square of
`Mathlib.AlgebraicGeometry.Morphisms.Flat` is applied to the pullback square
`(C ⊗ T).left = C.left ×_{Spec k} T.left` with the *affine* slot at `V ⊆ T.left` and the
*qcqs* slot at `⊤ ⊆ C.left`, and the `k ≅ Γ(C.left, 𝒪)` leg (Wave 1) transfers the
isomorphism across the square. Flatness of `T.hom` is automatic over a field
(`AlgebraicGeometry.Flat.of_field`). By sheaf separation the injectivity half extends to
**arbitrary** opens `W ⊆ T.left` (`Over.appLE_snd_injective`), which is why no affineness
or quasi-separatedness hypothesis on `T` survives into the final statement.

## The cocycle assembly

A Picard class on `T` dying on `C ⊗ T` is represented, after refining to an affine
pointed cover `𝒰` (`Scheme.PointedCover.exists_isAffineOpen_le`), by a unit cocycle `γ`
whose pullback is — by refinement injectivity, `Picard/RefinementInjectivity.lean` — a
coboundary `w` **on the pulled-back cover itself**. Choosing a point `sec t` in each
fiber of the (surjective) projection, the trivializing units `w (sec t) ∈ 𝒪ˣ(pr⁻¹ 𝒰 t)`
descend through the section bijection (`Over.unitsAppLE_snd_bijective`) to units
`v t ∈ 𝒪ˣ(𝒰 t)`, and the coboundary relation for `v` follows from the one for `w` by
injectivity of pullback on `𝒰 t ⊓ 𝒰 t'`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  CategoryTheory.PresheafOfGroups TopologicalSpace

namespace AlgebraicGeometry

/-! ## Flatness over a field -/

/-- Every morphism of schemes into the spectrum of a field is flat. -/
theorem Flat.of_field {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) : Flat f := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Flat) X.affineCover]
  intro i
  have h : Flat (Spec.map (Spec.preimage (X.affineCover.f i ≫ f))) := by
    rw [Flat.SpecMap_iff]
    letI := (Spec.preimage (X.affineCover.f i ≫ f)).hom.toAlgebra
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  exact Spec.map_preimage (X.affineCover.f i ≫ f) ▸ h

variable {k : Type u} [Field k]

/-- The structure morphism of any object of `Over (Spec k)` is flat, `k` a field. -/
instance flat_hom_over_field (T : Over (Spec (.of k))) : Flat T.hom :=
  Flat.of_field T.hom

/-! ## The section bijection over an affine open of the test scheme -/

namespace Over

variable (C T : Over (Spec (.of k)))
  [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

/-- **Sections over an affine open pull back bijectively along the projection**
(brick 2 of the separatedness ledger, freed from the affine-test special case): for `C`
proper, geometrically irreducible and geometrically reduced over the field `k`, any `T`
over `Spec k`, and an affine open `V ⊆ T.left`, pullback of sections along the second
projection is an isomorphism `Γ(T.left, V) ≅ Γ((C ⊗ T).left, pr⁻¹ V)`. -/
theorem isIso_appLE_snd {V : T.left.Opens} (hV : IsAffineOpen V) :
    IsIso ((snd C T).left.appLE V ((snd C T).left ⁻¹ᵁ V) le_rfl) := by
  -- `⊤ ⊆ C.left` is quasi-compact and quasi-separated, since `C` is proper over a field.
  have hC : IsCompact ((⊤ : C.left.Opens) : Set C.left) := by
    have : CompactSpace C.left := QuasiCompact.compactSpace_of_compactSpace C.hom
    simpa using CompactSpace.isCompact_univ
  have hC' : IsQuasiSeparated ((⊤ : C.left.Opens) : Set C.left) := by
    have : QuasiSeparatedSpace C.left := quasiSeparatedSpace_of_quasiSeparated C.hom
    simpa using isQuasiSeparated_univ
  have hUST : V ≤ T.hom ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) :=
    le_top.trans (Scheme.Hom.preimage_top T.hom).ge
  have hUSX : (⊤ : C.left.Opens) ≤ C.hom ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) :=
    (Scheme.Hom.preimage_top C.hom).ge
  have hUY : (snd C T).left ⁻¹ᵁ V
      = (fst C T).left ⁻¹ᵁ (⊤ : C.left.Opens) ⊓ (snd C T).left ⁻¹ᵁ V := by
    rw [Scheme.Hom.preimage_top, top_inf_eq]
  -- the master pushout square on sections, affine slot at `V ⊆ T.left`
  have hp := (isIso_pushoutSection_iff _ _ _ _).mp
    (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
      (Over.isPullback_left C T) hUST hUSX hUY (isAffineOpen_top _) hV hC hC')
  -- Wave 1: the `C`-side leg `Γ(Spec k, ⊤) ⟶ Γ(C.left, ⊤)` is an isomorphism.
  haveI : IsIso (C.hom.appLE ⊤ (⊤ : C.left.Opens) hUSX) := by
    have h : C.hom.appLE ⊤ (⊤ : C.left.Opens) hUSX = C.hom.appTop :=
      Scheme.Hom.appLE_eq_app C.hom
    rw [h]
    infer_instance
  -- a pushout of an isomorphism is an isomorphism
  have htriv : IsPushout (C.hom.appLE ⊤ (⊤ : C.left.Opens) hUSX) (T.hom.appLE ⊤ V hUST)
      (inv (C.hom.appLE ⊤ (⊤ : C.left.Opens) hUSX) ≫ T.hom.appLE ⊤ V hUST) (𝟙 _) :=
    IsPushout.of_horiz_isIso ⟨by rw [IsIso.hom_inv_id_assoc, Category.comp_id]⟩
  have h2 := hp.inr_isoIsPushout_hom _ _ htriv
  rw [Iso.comp_hom_eq_id] at h2
  rw [h2]
  infer_instance

/-- **Sections pull back injectively along the projection over arbitrary opens**
`W ⊆ T.left`: by separation for the structure sheaf, injectivity glues from the affine
opens contained in `W`, where pullback is even bijective (`Over.isIso_appLE_snd`). -/
theorem appLE_snd_injective (W : T.left.Opens) :
    Function.Injective ((snd C T).left.appLE W ((snd C T).left ⁻¹ᵁ W) le_rfl).hom := by
  intro s t hst
  refine T.left.sheaf.eq_of_locally_eq'
    (fun V : {V : T.left.Opens // IsAffineOpen V ∧ V ≤ W} ↦ V.1) W
    (fun V ↦ homOfLE V.2.2) (fun w hw ↦ ?_) s t (fun V ↦ ?_)
  · -- the affine opens contained in `W` cover it
    obtain ⟨V, hVaff, hwV, hVW⟩ :=
      Opens.isBasis_iff_nbhd.mp T.left.isBasis_affineOpens hw
    exact Opens.mem_iSup.mpr ⟨⟨V, hVaff, hVW⟩, hwV⟩
  · -- on an affine piece, transport the hypothesis to `pr⁻¹ V` and use bijectivity
    haveI := isIso_appLE_snd C T V.2.1
    have hres := congrArg ((C ⊗ T).left.presheaf.map (homOfLE
      (show (snd C T).left ⁻¹ᵁ V.1 ≤ (snd C T).left ⁻¹ᵁ W from
        fun x hx ↦ V.2.2 hx)).op).hom hst
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_map] at hres
    have key : ((snd C T).left.appLE V.1 ((snd C T).left ⁻¹ᵁ V.1) le_rfl).hom
          ((T.left.presheaf.map (homOfLE V.2.2).op).hom s)
        = ((snd C T).left.appLE V.1 ((snd C T).left ⁻¹ᵁ V.1) le_rfl).hom
          ((T.left.presheaf.map (homOfLE V.2.2).op).hom t) := by
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
      exact hres
    exact (ConcreteCategory.bijective_of_isIso
      ((snd C T).left.appLE V.1 ((snd C T).left ⁻¹ᵁ V.1) le_rfl)).injective key

/-- **Unit sections over an affine open pull back bijectively along the projection**:
the unit-group face of `Over.isIso_appLE_snd`. -/
theorem unitsAppLE_snd_bijective {V : T.left.Opens} (hV : IsAffineOpen V) :
    Function.Bijective
      ((snd C T).left.unitsAppLE V ((snd C T).left ⁻¹ᵁ V) le_rfl) := by
  constructor
  · intro a b hab
    exact Units.ext (appLE_snd_injective C T V (congrArg Units.val hab))
  · intro y
    haveI := isIso_appLE_snd C T hV
    have hbij := ConcreteCategory.bijective_of_isIso
      ((snd C T).left.appLE V ((snd C T).left ⁻¹ᵁ V) le_rfl)
    obtain ⟨a, ha⟩ := hbij.surjective (y : Γ((C ⊗ T).left, (snd C T).left ⁻¹ᵁ V))
    obtain ⟨b, hb⟩ := hbij.surjective
      ((y⁻¹ : Γ((C ⊗ T).left, (snd C T).left ⁻¹ᵁ V)ˣ) :
        Γ((C ⊗ T).left, (snd C T).left ⁻¹ᵁ V))
    have hab : a * b = 1 := by
      apply hbij.injective
      rw [map_mul, ha, hb, map_one]
      exact y.mul_inv
    have hba : b * a = 1 := by rw [mul_comm]; exact hab
    exact ⟨⟨a, b, hab, hba⟩, Units.ext ha⟩

end Over

/-! ## Affine refinement of pointed covers -/

/-- Every pointed cover of a scheme refines to one by affine opens: affine opens form a
basis of the topology. -/
theorem Scheme.PointedCover.exists_isAffineOpen_le {X : Scheme.{u}}
    (𝒰 : X.PointedCover) :
    ∃ 𝒱 : X.PointedCover, 𝒱 ≤ 𝒰 ∧ ∀ x, IsAffineOpen (𝒱.opens x) := by
  have h : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ 𝒰.opens x := fun x ↦ by
    obtain ⟨V, hVaff, hxV, hVU⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (𝒰.mem_opens x)
    exact ⟨V, hVaff, hxV, hVU⟩
  choose V hVaff hxV hVle using h
  exact ⟨⟨V, hxV⟩, hVle, hVaff⟩

/-! ## Brick 3: `prPullback_injective` -/

namespace Over

variable (C T : Over (Spec (.of k)))
  [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

/-- The projection `(C ⊗ T).left ⟶ T.left` is surjective: `C.hom` is surjective (its
source is irreducible, hence nonempty, and its target is a point), and surjectivity is
stable under base change. -/
instance surjective_snd_left : Surjective (snd C T).left :=
  MorphismProperty.of_isPullback (P := @Surjective) (Over.isPullback_left C T)
    inferInstance

/-- The descent step for `prPullback_injective`, with the fiber points and the descended
units abstracted: if the pullback cocycle of `γ` is the coboundary of `w`, and `vt, vt'`
pull back to the trivializing units of `w` at points `z, z'` of the product lying over
`t, t'`, then `vt, vt'` satisfy the coboundary relation for `γ` at `(t, t')`. The
equations `hz, hz'` let the fiber-point choices be substituted away. -/
private lemma descend_coboundary {𝒰 : T.left.PointedCover}
    (γ : T.left.unitsCocycle 𝒰)
    (w : ∀ z : (C ⊗ T).left,
      Γ((C ⊗ T).left, (𝒰.pullback (snd C T).left).opens z)ˣ)
    (hw : ∀ z z',
      (C ⊗ T).left.unitsRestrict
          (inf_le_left : (𝒰.pullback (snd C T).left).opens z
              ⊓ (𝒰.pullback (snd C T).left).opens z'
            ≤ (𝒰.pullback (snd C T).left).opens z) (w z)
          * Scheme.unitsEvInf ((snd C T).left.pullbackUnitsCocycle γ) z z'
        = (C ⊗ T).left.unitsRestrict inf_le_right (w z'))
    (z z' : (C ⊗ T).left) (t t' : T.left)
    (hz : (snd C T).left.base z = t) (hz' : (snd C T).left.base z' = t')
    (hzle : (snd C T).left ⁻¹ᵁ 𝒰.opens t ≤ (𝒰.pullback (snd C T).left).opens z)
    (hz'le : (snd C T).left ⁻¹ᵁ 𝒰.opens t' ≤ (𝒰.pullback (snd C T).left).opens z')
    (vt : Γ(T.left, 𝒰.opens t)ˣ) (vt' : Γ(T.left, 𝒰.opens t')ˣ)
    (hvt : (snd C T).left.unitsAppLE (𝒰.opens t) ((snd C T).left ⁻¹ᵁ 𝒰.opens t)
        le_rfl vt = (C ⊗ T).left.unitsRestrict hzle (w z))
    (hvt' : (snd C T).left.unitsAppLE (𝒰.opens t') ((snd C T).left ⁻¹ᵁ 𝒰.opens t')
        le_rfl vt' = (C ⊗ T).left.unitsRestrict hz'le (w z')) :
    T.left.unitsRestrict (inf_le_left : 𝒰.opens t ⊓ 𝒰.opens t' ≤ 𝒰.opens t) vt
        * Scheme.unitsEvInf γ t t'
      = T.left.unitsRestrict inf_le_right vt' := by
  subst hz hz'
  -- apply injectivity of pullback of unit sections on `𝒰 (pr z) ⊓ 𝒰 (pr z')`
  have hinj : Function.Injective ((snd C T).left.unitsAppLE
      (𝒰.opens ((snd C T).left.base z) ⊓ 𝒰.opens ((snd C T).left.base z'))
      ((snd C T).left ⁻¹ᵁ
        (𝒰.opens ((snd C T).left.base z) ⊓ 𝒰.opens ((snd C T).left.base z')))
      le_rfl) :=
    fun a b hab ↦ Units.ext (appLE_snd_injective C T _ (congrArg Units.val hab))
  apply hinj
  rw [map_mul]
  -- the descended units, restricted to `pr⁻¹(𝒰 (pr z) ⊓ 𝒰 (pr z'))`
  have e₁ := congrArg ((C ⊗ T).left.unitsRestrict
    (fun y hy ↦ hy.1 : (snd C T).left ⁻¹ᵁ
        (𝒰.opens ((snd C T).left.base z) ⊓ 𝒰.opens ((snd C T).left.base z'))
      ≤ (snd C T).left ⁻¹ᵁ 𝒰.opens ((snd C T).left.base z))) hvt
  rw [Scheme.Hom.unitsAppLE_map, Scheme.unitsRestrict_unitsRestrict] at e₁
  have e₂ := congrArg ((C ⊗ T).left.unitsRestrict
    (fun y hy ↦ hy.2 : (snd C T).left ⁻¹ᵁ
        (𝒰.opens ((snd C T).left.base z) ⊓ 𝒰.opens ((snd C T).left.base z'))
      ≤ (snd C T).left ⁻¹ᵁ 𝒰.opens ((snd C T).left.base z'))) hvt'
  rw [Scheme.Hom.unitsAppLE_map, Scheme.unitsRestrict_unitsRestrict] at e₂
  -- the coboundary relation for `w`, restricted to `pr⁻¹(𝒰 (pr z) ⊓ 𝒰 (pr z'))`
  have e₃ := congrArg ((C ⊗ T).left.unitsRestrict
    (fun y hy ↦ ⟨hy.1, hy.2⟩ : (snd C T).left ⁻¹ᵁ
        (𝒰.opens ((snd C T).left.base z) ⊓ 𝒰.opens ((snd C T).left.base z'))
      ≤ (𝒰.pullback (snd C T).left).opens z
          ⊓ (𝒰.pullback (snd C T).left).opens z')) (hw z z')
  rw [map_mul, Scheme.unitsRestrict_unitsRestrict, Scheme.unitsRestrict_unitsRestrict,
    Scheme.Hom.pullbackUnitsCocycle_unitsEvInf, Scheme.Hom.unitsAppLE_map] at e₃
  -- assemble
  rw [Scheme.Hom.map_unitsAppLE, Scheme.Hom.map_unitsAppLE, e₁, e₂]
  exact e₃

/-- **Brick 3 of the separatedness ledger** (design §4.4; the projection step of Kleiman,
*The Picard Scheme*, Theorem 2.5(1)): for `C` proper, geometrically irreducible and
geometrically reduced over the field `k` and **any** `T` over `Spec k`, pullback of Čech
Picard classes along the second projection `(C ⊗ T).left ⟶ T.left` is injective. -/
theorem prPullback_injective :
    Function.Injective (Scheme.CechPic.map (X := (C ⊗ T).left) (snd C T).left) := by
  -- the `H¹`-level heart, on an affine pointed cover
  have H : ∀ (𝒰 : T.left.PointedCover), (∀ t, IsAffineOpen (𝒰.opens t)) →
      ∀ a : T.left.unitsH1 𝒰, (snd C T).left.pullbackUnitsH1 𝒰 a = 1 → a = 1 := by
    intro 𝒰 haff a ha
    induction a using Quot.ind with | _ γ =>
    replace ha : ((snd C T).left.pullbackUnitsCocycle γ).class = OneCocycle.class 1 := ha
    obtain ⟨w, hw⟩ :=
      (OneCocycle.isCohomologous_iff_evInf _ _).mp ((OneCocycle.class_eq_iff _ _).mp ha)
    -- the coboundary data, in `Γ`-typed form
    have hw' : ∀ z z',
        (C ⊗ T).left.unitsRestrict
            (inf_le_left : (𝒰.pullback (snd C T).left).opens z
                ⊓ (𝒰.pullback (snd C T).left).opens z'
              ≤ (𝒰.pullback (snd C T).left).opens z) (w z)
            * Scheme.unitsEvInf ((snd C T).left.pullbackUnitsCocycle γ) z z'
          = (C ⊗ T).left.unitsRestrict inf_le_right (w z') := by
      intro z z'
      have h1 := hw z z'
      rw [OneCocycle.one_evInf, one_mul] at h1
      exact h1
    -- choose a point in each fiber of the projection, descend the trivializing units
    obtain ⟨sec, hsec⟩ := (snd C T).left.surjective.hasRightInverse
    have hchoice : ∀ t, ∃ v : Γ(T.left, 𝒰.opens t)ˣ,
        (snd C T).left.unitsAppLE (𝒰.opens t) ((snd C T).left ⁻¹ᵁ 𝒰.opens t) le_rfl v
          = (C ⊗ T).left.unitsRestrict
              (le_of_eq (by rw [Scheme.PointedCover.pullback_opens, hsec t]) :
                (snd C T).left ⁻¹ᵁ 𝒰.opens t
                  ≤ (𝒰.pullback (snd C T).left).opens (sec t)) (w (sec t)) :=
      fun t ↦ (unitsAppLE_snd_bijective C T (haff t)).surjective _
    choose v hv using hchoice
    -- the descended units witness the coboundary relation for `γ`
    rw [show (1 : T.left.unitsH1 𝒰) = OneCocycle.class 1 from rfl]
    refine (OneCocycle.class_eq_iff _ _).mpr
      ((OneCocycle.isCohomologous_iff_evInf _ _).mpr ⟨v, fun t t' ↦ ?_⟩)
    rw [OneCocycle.one_evInf, one_mul]
    exact descend_coboundary C T γ w hw' (sec t) (sec t') t t' (hsec t) (hsec t')
      _ _ (v t) (v t') (hv t) (hv t')
  -- assembly: refine to an affine pointed cover and use `CechPic.mk_eq_one_iff`
  refine (injective_iff_map_eq_one _).mpr fun x hx ↦ ?_
  induction x using Scheme.CechPic.ind with | _ 𝒰₀ a₀ =>
  obtain ⟨𝒰, hle, haff⟩ := 𝒰₀.exists_isAffineOpen_le
  rw [← Scheme.CechPic.mk_unitsRes hle] at hx ⊢
  rw [Scheme.CechPic.map_mk, Scheme.CechPic.mk_eq_one_iff] at hx
  rw [Scheme.CechPic.mk_eq_one_iff]
  exact H 𝒰 haff _ hx

end Over

end AlgebraicGeometry
