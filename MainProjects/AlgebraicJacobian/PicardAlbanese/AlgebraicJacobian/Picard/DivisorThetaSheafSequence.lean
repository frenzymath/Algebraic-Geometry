/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorThetaGlue
import AlgebraicJacobian.RiemannRoch.ChiSlice

/-!
# The theta-ideal inclusion as a morphism of sheaves

The chart presentation `thetaIdealDatum` is the line bundle `O(a Theta - d)`.  Its
piecewise equations assemble on the two theta charts to a section of `O(a Theta)`.
This file packages that assembly as the canonical monomorphism of sheaves

`O(a Theta - d) -> O(a Theta)`.

The construction uses the already established `gluedToIdeal₀/₁` assemblies.  Their
restriction laws give naturality, their theta-overlap comparison gives the target
twist relation, and regularity of the local equations gives monicity.  Consequently,
vanishing of `H^1(O(a Theta - d))` makes the cokernel projection surjective on global
sections by the general six-term cohomology slice.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations}

/-! ## The sectionwise inclusion -/

variable (A : DivisorAdaptation C R π d) (a : ℕ)

/-- The chart-zero component of the theta-ideal inclusion over an arbitrary open. -/
noncomputable def thetaIdealInclFst (W : (relCurve C R).Opens)
    (s : A.ThetaIdealSections a W) :
    Γ(relCurve C R, W ⊓ (relCover C R (fiberTwoCover π)).V₀) :=
  gluedToIdeal₀ A a inf_le_right
    (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s)

/-- The chart-one component of the theta-ideal inclusion over an arbitrary open. -/
noncomputable def thetaIdealInclSnd (W : (relCurve C R).Opens)
    (s : A.ThetaIdealSections a W) :
    Γ(relCurve C R, W ⊓ (relCover C R (fiberTwoCover π)).V₁) :=
  gluedToIdeal₁ A a inf_le_right
    (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s)

variable {A a}

/-- The two assembled components satisfy the theta twist relation. -/
theorem thetaIdealIncl_mem (W : (relCurve C R).Opens)
    (s : A.ThetaIdealSections a W) :
    (A.thetaIdealInclFst a W s, A.thetaIdealInclSnd a W s) ∈
      twistSubmodule R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) W := by
  rw [mem_twistSubmodule_iff]
  let V₀ := (relCover C R (fiberTwoCover π)).V₀
  let V₁ := (relCover C R (fiberTwoCover π)).V₁
  have hOmega : W ⊓ V₀ ⊓ V₁ ≤ V₀ ⊓ V₁ :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have h0 := gluedToIdeal₀_secRes (A := A) (a := a)
    (inf_le_left : W ⊓ V₀ ⊓ V₁ ≤ W ⊓ V₀)
    (inf_le_right : W ⊓ V₀ ≤ V₀)
    (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s)
  have h1 := gluedToIdeal₁_secRes (A := A) (a := a)
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W ⊓ V₀ ⊓ V₁ ≤ W ⊓ V₁)
    (inf_le_right : W ⊓ V₁ ≤ V₁)
    (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s)
  rw [secRes_secRes] at h0 h1
  have hcmp := gluedToIdeal₀_eq_theta_mul_gluedToIdeal₁ (A := A) (a := a) hOmega
    (secRes ((A.thetaIdealDatum a).sheaf)
      (inf_le_left.trans inf_le_left : W ⊓ V₀ ⊓ V₁ ≤ W) s)
  exact h0.symm.trans (hcmp.trans (congrArg
    (fun t => (relCurve C R).resHom hOmega
      ((relThetaCocycle C R π a : Γ(relCurve C R, V₀ ⊓ V₁)ˣ) :
        Γ(relCurve C R, V₀ ⊓ V₁)) * t) h1))

private lemma thetaIdealInclFst_add (W : (relCurve C R).Opens)
    (s t : A.ThetaIdealSections a W) :
    A.thetaIdealInclFst a W (s + t) =
      A.thetaIdealInclFst a W s + A.thetaIdealInclFst a W t := by
  change gluedToIdeal₀ A a inf_le_right
      (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left (s + t)) =
    gluedToIdeal₀ A a inf_le_right
        (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s) +
      gluedToIdeal₀ A a inf_le_right
        (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left t)
  rw [map_add, gluedToIdeal₀_add]

private lemma thetaIdealInclSnd_add (W : (relCurve C R).Opens)
    (s t : A.ThetaIdealSections a W) :
    A.thetaIdealInclSnd a W (s + t) =
      A.thetaIdealInclSnd a W s + A.thetaIdealInclSnd a W t := by
  change gluedToIdeal₁ A a inf_le_right
      (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left (s + t)) =
    gluedToIdeal₁ A a inf_le_right
        (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s) +
      gluedToIdeal₁ A a inf_le_right
        (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left t)
  rw [map_add, gluedToIdeal₁_add]

private lemma thetaIdealInclFst_smul (W : (relCurve C R).Opens) (r : R)
    (s : A.ThetaIdealSections a W) :
    A.thetaIdealInclFst a W (r • s) = r • A.thetaIdealInclFst a W s := by
  change gluedToIdeal₀ A a inf_le_right
      (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left (r • s)) =
    r • gluedToIdeal₀ A a inf_le_right
      (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s)
  rw [map_smul, gluedToIdeal₀_smul]

private lemma thetaIdealInclSnd_smul (W : (relCurve C R).Opens) (r : R)
    (s : A.ThetaIdealSections a W) :
    A.thetaIdealInclSnd a W (r • s) = r • A.thetaIdealInclSnd a W s := by
  change gluedToIdeal₁ A a inf_le_right
      (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left (r • s)) =
    r • gluedToIdeal₁ A a inf_le_right
      (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s)
  rw [map_smul, gluedToIdeal₁_smul]

/-- The theta-ideal inclusion on sections over one open. -/
noncomputable def thetaIdealInclApp (W : (relCurve C R).Opens) :
    A.ThetaIdealSections a W →ₗ[R]
      (relThetaTwistSheaf C R π a).obj.obj (op W) where
  toFun s := ⟨(A.thetaIdealInclFst a W s, A.thetaIdealInclSnd a W s),
    A.thetaIdealIncl_mem (a := a) W s⟩
  map_add' s t := Subtype.ext (Prod.ext
    (thetaIdealInclFst_add W s t) (thetaIdealInclSnd_add W s t))
  map_smul' r s := Subtype.ext (Prod.ext
    (thetaIdealInclFst_smul W r s) (thetaIdealInclSnd_smul W r s))

@[simp]
theorem thetaIdealInclApp_fst (W : (relCurve C R).Opens)
    (s : A.ThetaIdealSections a W) :
    (A.thetaIdealInclApp (a := a) W s).val.1 = A.thetaIdealInclFst a W s := rfl

@[simp]
theorem thetaIdealInclApp_snd (W : (relCurve C R).Opens)
    (s : A.ThetaIdealSections a W) :
    (A.thetaIdealInclApp (a := a) W s).val.2 = A.thetaIdealInclSnd a W s := rfl

/-! ## Chartwise inverse sections

On either pinned theta chart, a section whose germs lie in the local divisor ideal
has the canonical lift supplied by `idealToGlued₀/₁`.  These identities are the
local ingredients for the arbitrary-open range characterization below; importantly,
they quantify over the actual open and do not introduce a chart-typed cover.
-/

theorem thetaIdealInclApp_idealToGlued₀
    {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀)
    (β : Γ(relCurve C R, W))
    (hβ : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom β ∈ d.stalkIdeal z) :
    A.thetaIdealInclApp (a := a) W (idealToGlued₀ A a hW β hβ) =
      (twistTriv₀ R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) hW).symm β := by
  apply (twistTriv₀ R (relCover C R (fiberTwoCover π)).V₀
    (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) hW).injective
  rw [LinearEquiv.apply_symm_apply]
  change (relCurve C R).resHom (le_inf le_rfl hW)
      (gluedToIdeal₀ A a inf_le_right
        (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left
          (idealToGlued₀ A a hW β hβ))) = β
  rw [gluedToIdeal₀_secRes (A := A) (a := a) inf_le_left hW
    (idealToGlued₀ A a hW β hβ)]
  simp only [Scheme.resHom_resHom]
  rw [Scheme.resHom_self]
  exact gluedToIdeal₀_idealToGlued₀ (A := A) (a := a) hW β hβ

theorem thetaIdealInclApp_idealToGlued₁
    {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₁)
    (β : Γ(relCurve C R, W))
    (hβ : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom β ∈ d.stalkIdeal z) :
    A.thetaIdealInclApp (a := a) W (idealToGlued₁ A a hW β hβ) =
      (twistTriv₁ R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) hW).symm β := by
  apply (twistTriv₁ R (relCover C R (fiberTwoCover π)).V₀
    (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) hW).injective
  rw [LinearEquiv.apply_symm_apply]
  change (relCurve C R).resHom (le_inf le_rfl hW)
      (gluedToIdeal₁ A a inf_le_right
        (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left
          (idealToGlued₁ A a hW β hβ))) = β
  rw [gluedToIdeal₁_secRes (A := A) (a := a) inf_le_left hW
    (idealToGlued₁ A a hW β hβ)]
  simp only [Scheme.resHom_resHom]
  rw [Scheme.resHom_self]
  exact gluedToIdeal₁_idealToGlued₁ (A := A) (a := a) hW β hβ

/-- The sectionwise theta-ideal inclusion commutes with restriction. -/
theorem thetaIdealInclApp_res {W' W : (relCurve C R).Opens} (h : W' ≤ W)
    (s : A.ThetaIdealSections a W) :
    A.thetaIdealInclApp (a := a) W'
        (secRes ((A.thetaIdealDatum a).sheaf) h s) =
      twistRes R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) h
        (A.thetaIdealInclApp (a := a) W s) := by
  apply Subtype.ext
  apply Prod.ext
  · change gluedToIdeal₀ A a inf_le_right
        (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left
          (secRes ((A.thetaIdealDatum a).sheaf) h s)) =
      (relCurve C R).resHom (inf_le_inf_right _ h)
        (gluedToIdeal₀ A a inf_le_right
          (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s))
    simpa only [secRes_secRes] using
      (gluedToIdeal₀_secRes (A := A) (a := a) (inf_le_inf_right _ h)
        inf_le_right (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s))
  · change gluedToIdeal₁ A a inf_le_right
        (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left
          (secRes ((A.thetaIdealDatum a).sheaf) h s)) =
      (relCurve C R).resHom (inf_le_inf_right _ h)
        (gluedToIdeal₁ A a inf_le_right
          (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s))
    simpa only [secRes_secRes] using
      (gluedToIdeal₁_secRes (A := A) (a := a) (inf_le_inf_right _ h)
        inf_le_right (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s))


/-! ## The sheaf morphism and monicity -/

/-- The natural transformation underlying the theta-ideal inclusion. -/
noncomputable def thetaIdealInclPresheaf :
    (A.thetaIdealDatum a).sheaf.obj ⟶ (relThetaTwistSheaf C R π a).obj where
  app W := ModuleCat.ofHom (A.thetaIdealInclApp (a := a) W.unop)
  naturality := by
    intro U V i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact A.thetaIdealInclApp_res (a := a) i.unop.le s

/-- The canonical inclusion `O(a Theta - d) -> O(a Theta)`. -/
noncomputable def thetaIdealIncl :
    (A.thetaIdealDatum a).sheaf ⟶ relThetaTwistSheaf C R π a :=
  (fullyFaithfulSheafToPresheaf _ _).preimage
    (thetaIdealInclPresheaf (A := A) (a := a))

theorem thetaIdealIncl_hom :
    (thetaIdealIncl (A := A) (a := a)).hom =
      thetaIdealInclPresheaf (A := A) (a := a) :=
  (fullyFaithfulSheafToPresheaf _ _).map_preimage
    (X := (A.thetaIdealDatum a).sheaf) (Y := relThetaTwistSheaf C R π a)
      (thetaIdealInclPresheaf (A := A) (a := a))

@[simp]
theorem thetaIdealIncl_app (W : (relCurve C R).Opens) :
    (thetaIdealIncl (A := A) (a := a)).hom.app (op W) =
      ModuleCat.ofHom (A.thetaIdealInclApp (a := a) W) := by
  rw [thetaIdealIncl_hom (A := A) (a := a)]
  rfl

/-- The theta-ideal inclusion is injective on sections over every open. -/
theorem thetaIdealInclApp_injective (W : (relCurve C R).Opens) :
    Function.Injective (A.thetaIdealInclApp (a := a) W) := by
  intro s t hst
  have h0 : A.thetaIdealInclFst a W s = A.thetaIdealInclFst a W t :=
    congrArg (fun q => q.val.1) hst
  have h1 : A.thetaIdealInclSnd a W s = A.thetaIdealInclSnd a W t :=
    congrArg (fun q => q.val.2) hst
  let V₀ := (relCover C R (fiberTwoCover π)).V₀
  let V₁ := (relCover C R (fiberTwoCover π)).V₁
  let s0 := secRes ((A.thetaIdealDatum a).sheaf) (inf_le_left : W ⊓ V₀ ≤ W) s
  let t0 := secRes ((A.thetaIdealDatum a).sheaf) (inf_le_left : W ⊓ V₀ ≤ W) t
  let s1 := secRes ((A.thetaIdealDatum a).sheaf) (inf_le_left : W ⊓ V₁ ≤ W) s
  let t1 := secRes ((A.thetaIdealDatum a).sheaf) (inf_le_left : W ⊓ V₁ ≤ W) t
  change gluedToIdeal₀ A a inf_le_right s0 = gluedToIdeal₀ A a inf_le_right t0 at h0
  change gluedToIdeal₁ A a inf_le_right s1 = gluedToIdeal₁ A a inf_le_right t1 at h1
  have hs0 : s0 = t0 := by
    apply gluedSections_ext₀ (A := A) (a := a) (inf_le_right : W ⊓ V₀ ≤ V₀)
    intro i
    apply A.eqn_res_cancel (Sum.inl i) inf_le_right
    change (relCurve C R).resHom inf_le_right (A.eqn (Sum.inl i)) *
        A.gluedComp₀ s0 i =
      (relCurve C R).resHom inf_le_right (A.eqn (Sum.inl i)) * A.gluedComp₀ t0 i
    calc
      _ = (relCurve C R).resHom inf_le_left (gluedToIdeal₀ A a inf_le_right s0) :=
        (res_gluedToIdeal₀ (inf_le_right : W ⊓ V₀ ≤ V₀) s0 i).symm
      _ = (relCurve C R).resHom inf_le_left (gluedToIdeal₀ A a inf_le_right t0) :=
        congrArg ((relCurve C R).resHom inf_le_left) h0
      _ = _ := res_gluedToIdeal₀ (inf_le_right : W ⊓ V₀ ≤ V₀) t0 i
  have hs1 : s1 = t1 := by
    apply gluedSections_ext₁ (A := A) (a := a) (inf_le_right : W ⊓ V₁ ≤ V₁)
    intro j
    apply A.eqn_res_cancel (Sum.inr j) inf_le_right
    change (relCurve C R).resHom inf_le_right (A.eqn (Sum.inr j)) *
        A.gluedComp₁ s1 j =
      (relCurve C R).resHom inf_le_right (A.eqn (Sum.inr j)) * A.gluedComp₁ t1 j
    calc
      _ = (relCurve C R).resHom inf_le_left (gluedToIdeal₁ A a inf_le_right s1) :=
        (res_gluedToIdeal₁ (inf_le_right : W ⊓ V₁ ≤ V₁) s1 j).symm
      _ = (relCurve C R).resHom inf_le_left (gluedToIdeal₁ A a inf_le_right t1) :=
        congrArg ((relCurve C R).resHom inf_le_left) h1
      _ = _ := res_gluedToIdeal₁ (inf_le_right : W ⊓ V₁ ≤ V₁) t1 j
  apply TopCat.Sheaf.eq_of_locally_eq₂ ((A.thetaIdealDatum a).sheaf)
    (homOfLE (inf_le_left : W ⊓ V₀ ≤ W))
    (homOfLE (inf_le_left : W ⊓ V₁ ≤ W))
  · rw [← inf_sup_left, relCover_sup, inf_top_eq]
  · exact hs0
  · exact hs1

/-- The theta-ideal inclusion is a monomorphism of sheaves. -/
instance thetaIdealIncl_mono : Mono (thetaIdealIncl (A := A) (a := a)) := by
  haveI happ : ∀ W, Mono ((thetaIdealInclPresheaf (A := A) (a := a)).app W) := fun W => by
    rw [ModuleCat.mono_iff_injective]
    exact thetaIdealInclApp_injective (A := A) (a := a) W.unop
  haveI hpre : Mono (thetaIdealInclPresheaf (A := A) (a := a)) :=
    NatTrans.mono_of_mono_app _
  have hmap : (sheafToPresheaf _ _).map (thetaIdealIncl (A := A) (a := a)) =
      thetaIdealInclPresheaf (A := A) (a := a) :=
    thetaIdealIncl_hom (A := A) (a := a)
  apply (sheafToPresheaf _ _).mono_of_mono_map
  rw [hmap]
  exact hpre

/-! ## Arbitrary-open range

The two chartwise lifts glue on every open.  This is the cover-independent range
statement needed by the global theta cokernel: membership is tested only by the
germs of the two components, while the open itself remains arbitrary.
-/

theorem exists_thetaIdealInclApp_of_germ_mem
    {W : (relCurve C R).Opens}
    (x : (relThetaTwistSheaf C R π a).obj.obj (op W))
    (hx0 : ∀ (z : relCurve C R) (hz : z ∈ W ⊓
      (relCover C R (fiberTwoCover π)).V₀),
      ((relCurve C R).presheaf.germ (W ⊓
        (relCover C R (fiberTwoCover π)).V₀) z hz).hom x.val.1 ∈ d.stalkIdeal z)
    (hx1 : ∀ (z : relCurve C R) (hz : z ∈ W ⊓
      (relCover C R (fiberTwoCover π)).V₁),
      ((relCurve C R).presheaf.germ (W ⊓
        (relCover C R (fiberTwoCover π)).V₁) z hz).hom x.val.2 ∈ d.stalkIdeal z) :
    ∃ s : A.ThetaIdealSections a W, A.thetaIdealInclApp (a := a) W s = x := by
  let V₀ := (relCover C R (fiberTwoCover π)).V₀
  let V₁ := (relCover C R (fiberTwoCover π)).V₁
  let U : Bool → (relCurve C R).Opens := fun b =>
    match b with
    | false => W ⊓ V₀
    | true => W ⊓ V₁
  have hUW : ∀ b : Bool, U b ≤ W := by
    intro b
    cases b <;> exact inf_le_left
  let s : ∀ b : Bool, A.ThetaIdealSections a (U b) := fun b => match b with
    | false => idealToGlued₀ A a (show U false ≤ V₀ from inf_le_right) x.val.1 hx0
    | true => idealToGlued₁ A a (show U true ≤ V₁ from inf_le_right) x.val.2 hx1
  have hlocal : ∀ b : Bool,
      A.thetaIdealInclApp (a := a) (U b) (s b) =
        twistRes R V₀ V₁ (relThetaCocycle C R π a) (hUW b) x := by
    intro b
    cases b with
    | false =>
      let hU : U false ≤ V₀ := show U false ≤ V₀ from inf_le_right
      have hchart :
          A.thetaIdealInclApp (a := a) (U false) (s false) =
            (twistTriv₀ R V₀ V₁ (relThetaCocycle C R π a) hU).symm x.val.1 := by
        simpa [s] using
          (thetaIdealInclApp_idealToGlued₀ (A := A) (a := a) hU x.val.1 hx0)
      apply (twistTriv₀ R V₀ V₁ (relThetaCocycle C R π a) hU).injective
      rw [hchart, LinearEquiv.apply_symm_apply, twistTriv₀_apply, twistRes_coe_fst]
      calc
        x.val.1 = (relCurve C R).resHom (le_refl (U false)) x.val.1 :=
          (Scheme.resHom_self (le_refl (U false)) x.val.1).symm
        _ = (relCurve C R).resHom (le_inf le_rfl hU)
            ((relCurve C R).resHom
              (inf_le_inf_right V₀ (inf_le_left : U false ≤ W)) x.val.1) := by
          rw [Scheme.resHom_resHom]
    | true =>
      let hU : U true ≤ V₁ := show U true ≤ V₁ from inf_le_right
      have hchart :
          A.thetaIdealInclApp (a := a) (U true) (s true) =
            (twistTriv₁ R V₀ V₁ (relThetaCocycle C R π a) hU).symm x.val.2 := by
        simpa [s] using
          (thetaIdealInclApp_idealToGlued₁ (A := A) (a := a) hU x.val.2 hx1)
      apply (twistTriv₁ R V₀ V₁ (relThetaCocycle C R π a) hU).injective
      rw [hchart, LinearEquiv.apply_symm_apply, twistTriv₁_apply, twistRes_coe_snd]
      calc
        x.val.2 = (relCurve C R).resHom (le_refl (U true)) x.val.2 :=
          (Scheme.resHom_self (le_refl (U true)) x.val.2).symm
        _ = (relCurve C R).resHom (le_inf le_rfl hU)
            ((relCurve C R).resHom
              (inf_le_inf_right V₁ (inf_le_left : U true ≤ W)) x.val.2) := by
          rw [Scheme.resHom_resHom]
  have hcompat : ∀ i j : Bool,
      secRes ((A.thetaIdealDatum a).sheaf)
          (inf_le_left : U i ⊓ U j ≤ U i) (s i) =
        secRes ((A.thetaIdealDatum a).sheaf)
          (inf_le_right : U i ⊓ U j ≤ U j) (s j) := by
    intro i j
    apply A.thetaIdealInclApp_injective (a := a) (U i ⊓ U j)
    rw [thetaIdealInclApp_res, thetaIdealInclApp_res, hlocal i, hlocal j]
    apply Subtype.ext
    apply Prod.ext
    · change (relCurve C R).resHom _ ((relCurve C R).resHom _ x.val.1) =
        (relCurve C R).resHom _ ((relCurve C R).resHom _ x.val.1)
      rw [Scheme.resHom_resHom, Scheme.resHom_resHom]
    · change (relCurve C R).resHom _ ((relCurve C R).resHom _ x.val.2) =
        (relCurve C R).resHom _ ((relCurve C R).resHom _ x.val.2)
      rw [Scheme.resHom_resHom, Scheme.resHom_resHom]
  have hcompat' : TopCat.Presheaf.IsCompatible ((A.thetaIdealDatum a).sheaf).obj
      U (fun b => s b) := by
    intro i j
    exact hcompat i j
  have hcover : W ≤ ⨆ b : Bool, U b := by
    intro z hz
    have hz' : z ∈ V₀ ⊔ V₁ := by
      rw [relCover_sup]
      trivial
    rcases Opens.mem_sup.mp hz' with h | h
    · exact Opens.mem_iSup.mpr ⟨false, ⟨hz, h⟩⟩
    · exact Opens.mem_iSup.mpr ⟨true, ⟨hz, h⟩⟩
  obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    ((A.thetaIdealDatum a).sheaf) (fun b : Bool => U b) W
    (fun b => homOfLE (hUW b)) hcover (fun b => s b) hcompat'
  refine ⟨σ, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq₂ (relThetaTwistSheaf C R π a)
    (homOfLE (hUW false)) (homOfLE (hUW true))
  · change W ≤ U false ⊔ U true
    change W ≤ (W ⊓ V₀) ⊔ (W ⊓ V₁)
    rw [← inf_sup_left, relCover_sup, inf_top_eq]
  · change twistRes R V₀ V₁ (relThetaCocycle C R π a) (hUW false)
      (A.thetaIdealInclApp (a := a) W σ) =
      twistRes R V₀ V₁ (relThetaCocycle C R π a) (hUW false) x
    rw [← thetaIdealInclApp_res]
    change A.thetaIdealInclApp (a := a) (U false)
        (secRes ((A.thetaIdealDatum a).sheaf) (hUW false) σ) =
      twistRes R V₀ V₁ (relThetaCocycle C R π a) (hUW false) x
    rw [show secRes ((A.thetaIdealDatum a).sheaf) (hUW false) σ = s false from hσ false]
    exact hlocal false
  · change twistRes R V₀ V₁ (relThetaCocycle C R π a) (hUW true)
      (A.thetaIdealInclApp (a := a) W σ) =
      twistRes R V₀ V₁ (relThetaCocycle C R π a) (hUW true) x
    rw [← thetaIdealInclApp_res]
    change A.thetaIdealInclApp (a := a) (U true)
        (secRes ((A.thetaIdealDatum a).sheaf) (hUW true) σ) =
      twistRes R V₀ V₁ (relThetaCocycle C R π a) (hUW true) x
    rw [show secRes ((A.thetaIdealDatum a).sheaf) (hUW true) σ = s true from hσ true]
    exact hlocal true

/-- The pointwise range of the theta-ideal inclusion on an arbitrary open is exactly
the theta sections whose two pinned components vanish along the divisor germwise. -/
theorem mem_range_thetaIdealInclApp_iff_germ_mem
    {W : (relCurve C R).Opens}
    (x : (relThetaTwistSheaf C R π a).obj.obj (op W)) :
    x ∈ LinearMap.range (A.thetaIdealInclApp (a := a) W) ↔
      (∀ (z : relCurve C R) (hz : z ∈ W ⊓
        (relCover C R (fiberTwoCover π)).V₀),
        ((relCurve C R).presheaf.germ (W ⊓
          (relCover C R (fiberTwoCover π)).V₀) z hz).hom x.val.1 ∈ d.stalkIdeal z) ∧
      (∀ (z : relCurve C R) (hz : z ∈ W ⊓
        (relCover C R (fiberTwoCover π)).V₁),
        ((relCurve C R).presheaf.germ (W ⊓
          (relCover C R (fiberTwoCover π)).V₁) z hz).hom x.val.2 ∈ d.stalkIdeal z) := by
  constructor
  · rintro ⟨s, rfl⟩
    constructor
    · intro z hz
      exact germ_gluedToIdeal₀_mem (A := A) (a := a) inf_le_right
        (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s) z hz
    · intro z hz
      exact germ_gluedToIdeal₁_mem (A := A) (a := a) inf_le_right
        (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s) z hz
  · rintro ⟨hx0, hx1⟩
    obtain ⟨s, hs⟩ := A.exists_thetaIdealInclApp_of_germ_mem (a := a) x hx0 hx1
    exact ⟨s, hs⟩
/-! ## Global right exactness -/

/-- Vanishing of `H^1(O(a Theta - d))` makes the theta quotient sheaf globally generated
by theta sections. -/
theorem thetaIdealCokernel_app_top_surjective
    [Subsingleton (Sheaf.HModule (A.thetaIdealDatum a).sheaf 1)] :
    Function.Surjective
      ((cokernel.π (thetaIdealIncl (A := A) (a := a))).hom.app
        (op (⊤ : (relCurve C R).Opens))).hom :=
  Sheaf.HModule.cokernelπ_app_surjective_of_subsingleton_h1
    (thetaIdealIncl (A := A) (a := a)) isTerminalTop

end DivisorAdaptation

end AlgebraicGeometry
