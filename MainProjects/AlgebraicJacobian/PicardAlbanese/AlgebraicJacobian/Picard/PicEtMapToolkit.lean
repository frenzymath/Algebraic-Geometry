/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEt
import AlgebraicJacobian.Picard.PicEtAffZariskiGlue

/-!
# The basic-open toolkit for the Layer-2 functoriality

The functoriality of `picEt` along an arbitrary morphism of test objects evaluates a
compatible family on finite basic-open refinements of the preimages of affine opens.
This file provides the toolkit:

* `AlgebraicGeometry.Scheme.exists_basic_subcover`: a finite family of sections of an
  affine open spanning the unit ideal whose basic opens are subordinate to any given
  pointwise-open constraint.
* `AlgebraicGeometry.Over.resAwayAlgHom`: restriction between basic opens of an affine
  open as an algebra map over its sections — hence *the* map between the corresponding
  localizations (`IsLocalization.algHom_subsingleton`).
* `AlgebraicGeometry.picEt.eq_of_basic_eq`: the Zariski separation of `PicEtAff`
  instantiated at the section rings of a basic cover of an affine open — two plus
  classes over `Γ(U)` agreeing on every member of a spanning family of basic opens
  agree.
* `AlgebraicGeometry.picEt.mapAlg_appLE_eq`: **choice independence** — the restriction
  of a compatible family through two different affine opens of the target agree; the
  well-definedness of the glued functoriality.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra

/-! ## Basic subcovers subordinate to a constraint -/

/-- Any pointwise-open constraint on an affine open is refined by a finite spanning
family of basic opens. -/
theorem Scheme.exists_basic_subcover {X : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W)
    (P : X.Opens → Prop) (hloc : ∀ w ∈ W, ∃ U₀ : X.Opens, w ∈ U₀ ∧ P U₀) :
    ∃ s : Finset Γ(X, W), Ideal.span (↑s : Set Γ(X, W)) = ⊤
      ∧ ∀ r ∈ s, ∃ U₀, P U₀ ∧ X.basicOpen r ≤ U₀ := by
  classical
  -- a pointwise basic refinement
  have hpt : ∀ w : ↥W, ∃ (r : Γ(X, W)) (U₀ : X.Opens),
      P U₀ ∧ X.basicOpen r ≤ U₀ ∧ (w : X) ∈ X.basicOpen r := by
    rintro ⟨w, hw⟩
    obtain ⟨U₀, hwU₀, hPU₀⟩ := hloc w hw
    obtain ⟨r, hrle, hwr⟩ := hW.exists_basicOpen_le (⟨w, hwU₀⟩ : U₀) hw
    exact ⟨r, U₀, hPU₀, hrle, hwr⟩
  choose rfun Ufun hP hle hmem using hpt
  -- a finite subcover by compactness
  obtain ⟨t, ht⟩ := hW.isCompact.elim_finite_subcover
    (fun w : ↥W => (X.basicOpen (rfun w) : Set X))
    (fun w => (X.basicOpen (rfun w)).2) (fun x hx => by
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩)
  refine ⟨t.image rfun, ?_, ?_⟩
  · -- the spanning condition
    rw [← hW.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun r => X.basicOpen_le _) fun x hx => ?_
    obtain ⟨w, hwt, hxw⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Opens.mem_iSup.mpr ⟨⟨rfun w, Finset.mem_image_of_mem rfun hwt⟩, hxw⟩
  · intro r hr
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨Ufun w, hP w, hle w⟩

/-! ## Restriction between basic opens over the sections of the ambient affine -/

namespace Over

variable {k : Type u} [Field k]

/-- Restriction between basic opens of an open of a test object, as an algebra map over
the sections of the ambient open (with mathlib's restriction algebras). -/
noncomputable def resAwayAlgHom (T' : Over (Spec (.of k))) {W : T'.left.Opens}
    {u v : Γ(T'.left, W)} (h : T'.left.basicOpen v ≤ T'.left.basicOpen u) :
    Γ(T'.left, T'.left.basicOpen u) →ₐ[Γ(T'.left, W)]
      Γ(T'.left, T'.left.basicOpen v) where
  toRingHom := (T'.left.presheaf.map (homOfLE h).op).hom
  commutes' r := by
    have key : T'.left.presheaf.map (homOfLE (T'.left.basicOpen_le u)).op
        ≫ T'.left.presheaf.map (homOfLE h).op
        = T'.left.presheaf.map (homOfLE (T'.left.basicOpen_le v)).op := by
      rw [← Functor.map_comp, ← op_comp, homOfLE_comp]
    exact congr($(key).hom r)

@[simp]
lemma resAwayAlgHom_apply (T' : Over (Spec (.of k))) {W : T'.left.Opens}
    {u v : Γ(T'.left, W)} (h : T'.left.basicOpen v ≤ T'.left.basicOpen u)
    (x : Γ(T'.left, T'.left.basicOpen u)) :
    resAwayAlgHom T' h x = T'.left.presheaf.map (homOfLE h).op x :=
  rfl

set_option maxSynthPendingDepth 10 in
/-- The `k`-restriction of `resAwayAlgHom` is the plain section restriction. -/
lemma resAwayAlgHom_restrictScalars (T' : Over (Spec (.of k))) {W : T'.left.Opens}
    {u v : Γ(T'.left, W)} (h : T'.left.basicOpen v ≤ T'.left.basicOpen u) :
    (resAwayAlgHom T' h).restrictScalars k = Over.resAlgHom T' h :=
  AlgHom.ext fun _ => rfl

end Over

/-! ## Zariski separation over the section rings of a basic cover -/

namespace picEt

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

/-- Two plus classes over the sections of an affine open agreeing on every member of a
finite spanning family of basic opens agree: the Zariski separation of `PicEtAff`,
instantiated at section rings. -/
theorem eq_of_basic_eq {T' : Over (Spec (.of k))} (W : T'.left.affineOpens)
    (s : Finset Γ(T'.left, W.1)) (hs : Ideal.span (↑s : Set Γ(T'.left, W.1)) = ⊤)
    {x y : PicEtAff C Γ(T'.left, W.1)}
    (h : ∀ r ∈ s, PicEtAff.mapAlg C (Over.resAlgHom T' (T'.left.basicOpen_le r)) x
      = PicEtAff.mapAlg C (Over.resAlgHom T' (T'.left.basicOpen_le r)) y) :
    x = y := by
  classical
  haveI hAway : ∀ r : ↥s, IsLocalization.Away (r : Γ(T'.left, W.1))
      Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1))) := fun r =>
    W.2.isLocalization_basicOpen (r : Γ(T'.left, W.1))
  haveI htow : ∀ r : ↥s, IsScalarTower k Γ(T'.left, W.1)
      Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1))) := fun r =>
    Over.isScalarTower_sections_basicOpen T' W.1 (r : Γ(T'.left, W.1))
  refine PicEtAff.eq_of_away_eq C (fun r : ↥s => (r : Γ(T'.left, W.1)))
    (fun r : ↥s => Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1)))) ?_ ?_
  · rw [show (Set.range fun r : ↥s => (r : Γ(T'.left, W.1))) = (↑s : Set _) from
      Subtype.range_coe]
    exact hs
  · intro r
    rw [show IsScalarTower.toAlgHom k Γ(T'.left, W.1)
        Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1)))
      = Over.resAlgHom T' (T'.left.basicOpen_le (r : Γ(T'.left, W.1))) from
      AlgHom.ext fun _ => rfl]
    exact h r r.2

/-! ## Choice independence of the glued evaluation -/

variable {T T' : Over (Spec (.of k))}

/-- **Choice independence**: restricting a compatible family through two different
affine opens of the target gives the same plus class on any affine open of the source
contained in both preimages. -/
theorem mapAlg_appLE_eq (f : T' ⟶ T) (s : picEt C T) {W₀ : T'.left.affineOpens}
    {V V' : T.left.affineOpens} (hV : W₀.1 ≤ f.left ⁻¹ᵁ V.1)
    (hV' : W₀.1 ≤ f.left ⁻¹ᵁ V'.1) :
    PicEtAff.mapAlg C (Over.appLEAlgHom f V.1 W₀.1 hV) (s.1 V)
      = PicEtAff.mapAlg C (Over.appLEAlgHom f V'.1 W₀.1 hV') (s.1 V') := by
  classical
  -- refine by basic opens whose image lies in an affine open inside `V ⊓ V'`
  obtain ⟨sub, hspan, hsub⟩ := Scheme.exists_basic_subcover W₀.2
    (fun U₀ => ∃ V'' : T.left.affineOpens,
      V''.1 ≤ V.1 ∧ V''.1 ≤ V'.1 ∧ U₀ = f.left ⁻¹ᵁ V''.1)
    (fun w hw => by
      have hfw : f.left.base w ∈ V.1 ⊓ V'.1 := ⟨hV hw, hV' hw⟩
      obtain ⟨V'', hV''aff, hwV'', hV''le⟩ := Opens.isBasis_iff_nbhd.mp
        T.left.isBasis_affineOpens hfw
      exact ⟨f.left ⁻¹ᵁ V'', hwV'', ⟨⟨V'', hV''aff⟩,
        hV''le.trans inf_le_left, hV''le.trans inf_le_right, rfl⟩⟩)
  choose V'' hV''₁ hV''₂ hU₀ using fun (r : Γ(T'.left, W₀.1)) (hr : r ∈ sub) =>
    (hsub r hr).choose_spec.1
  have hDle : ∀ (r : Γ(T'.left, W₀.1)) (hr : r ∈ sub),
      T'.left.basicOpen r ≤ f.left ⁻¹ᵁ (V'' r hr).1 := fun r hr => by
    have h1 := (hsub r hr).choose_spec.2
    rw [hU₀ r hr] at h1
    exact h1
  refine eq_of_basic_eq C W₀ sub hspan (fun r hr => ?_)
  -- both sides restrict to the value at `V'' r hr` on the basic piece
  have hcalc : ∀ (Vb : T.left.affineOpens) (hVb : W₀.1 ≤ f.left ⁻¹ᵁ Vb.1)
      (hb₁ : (V'' r hr).1 ≤ Vb.1),
      PicEtAff.mapAlg C (Over.resAlgHom T' (T'.left.basicOpen_le r))
        (PicEtAff.mapAlg C (Over.appLEAlgHom f Vb.1 W₀.1 hVb) (s.1 Vb))
      = PicEtAff.mapAlg C
          (Over.appLEAlgHom f (V'' r hr).1 (T'.left.basicOpen r) (hDle r hr))
          (s.1 (V'' r hr)) := by
    intro Vb hVb hb₁
    rw [← PicEtAff.mapAlg_comp, Over.resAlgHom_comp_appLEAlgHom,
      ← Over.appLEAlgHom_comp_resAlgHom f (T'.left.basicOpen r) hb₁
        (hDle r hr) ((T'.left.basicOpen_le r).trans hVb),
      PicEtAff.mapAlg_comp, s.compat (V'' r hr) Vb hb₁]
  rw [hcalc V hV (hV''₁ r hr), hcalc V' hV' (hV''₂ r hr)]

end picEt

end AlgebraicGeometry
