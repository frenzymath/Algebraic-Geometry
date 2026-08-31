/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.FlatteningStratification
import AlgebraicJacobian.Picard.QuotScheme
import AlgebraicJacobian.Cohomology.QcohTildeSections
import AlgebraicJacobian.Cohomology.PullbackQuasicoherent

/-!
# Generic flatness: the geometric statement (Nitsure §4)

This file proves the **geometric generic flatness theorem**
`AlgebraicGeometry.genericFlatness` (blueprint node `thm:generic_flatness`,
Nitsure §4): over an integral locally noetherian base `S`, a finitely
presented module sheaf on a finite-type (quasi-compact and locally of finite
type) `X ⟶ S` has flat sections over all affine pairs below some non-empty
open `V ⊆ S`.

It is the geometric-glue layer on top of the algebraic generic-freeness
engine of `AlgebraicJacobian.Picard.FlatteningStratification`
(`GenericFreeness.genericFlatnessAlgebraic`, Stacks 051R).  The declaration
lives in its own file — rather than in `FlatteningStratification.lean`, which
it logically belongs with — because the glue needs the qcqs
section-localization engine of `AlgebraicJacobian.Picard.QuotScheme`
(Stacks 01P0/01PC/01I8) and the base-ring descent of
`AlgebraicJacobian.Cohomology.QcohTildeSections`, and importing those files
into `FlatteningStratification.lean` perturbs the instance environment of its
dévissage proofs.

The layer structure, bottom to top:

1. `Module.Flat.of_isLocalizedModule_algebra` — mixed-base stability: flatness
   over the base survives localizing the module at a submonoid of the fibre
   algebra (Mathlib has only the same-ring version).
2. `flat_section_chartBasic` — on a basic open of a chart lying above a base
   basic open `D(g)`, sections are flat over the ambient affine `Γ(S, U₀)`,
   given freeness of the chart sections localized at `g`.
3. `flat_section_pair` — the two-layer basic-open reduction from an arbitrary
   affine pair `(U, W)` to chart-basic pieces, via
   `Module.flat_of_isLocalized_span` and two
   `Module.flat_iff_of_isLocalization` exchanges.
4. `genericFlatness` — chart supply by
   `Scheme.Modules.exists_affine_finite_sections_nhds` (Stacks 01PC), one
   generic-freeness witness per chart, product denominator, `V := D(f)`.
-/

universe u v

open CategoryTheory Limits

open scoped TensorProduct

namespace AlgebraicGeometry

/-! ## §1b. Geometric glue for generic flatness

The algebraic generic-freeness theorem (`GenericFreeness.genericFlatnessAlgebraic`)
concerns one finite module over one finite-type algebra.  The geometric statement
`genericFlatness` below quantifies over *all* affine pairs `U ≤ V`, `W ≤ p ⁻¹ᵁ U`.
This section provides the glue:

* `Module.Flat.of_isLocalizedModule_algebra` — flatness over the base survives
  localizing the module at a submonoid of the fibre algebra (mixed-base
  stability; Mathlib has only the same-ring `Module.Flat.of_isLocalizedModule`);
* `flat_sections_congr` — transport of section flatness along an equality of
  opens (the `appLE` restriction witness is proof-irrelevant);
* `flat_section_chartBasic` — the core: on a basic open of a chart lying above a
  base basic open `D(g)`, the sections of `F` are flat over the ambient affine
  `Γ(S, U₀)`, given that the chart sections localized at `g` are free.  The
  abstract localization is matched with the section module by the qcqs
  section-localization engine (`Scheme.Modules.isLocalizedModule_basicOpen_of_isCompact`,
  Stacks 01P0) via the base-ring descent
  `isLocalizedModule_powers_restrictScalars_of_algebraMap`, and the remaining
  fibre-side localization is absorbed by the mixed-base stability lemma;
* `flat_section_pair` — the two-layer basic-open reduction: an arbitrary affine
  pair `(U, W)` is covered fibre-side by opens that are simultaneously basic in
  `W` and in a chart and lie above base basic opens common to `U` and `U₀`
  (`exists_basicOpen_le_affine_inter`, twice), and
  `Module.flat_of_isLocalized_span` plus two `Module.flat_iff_of_isLocalization`
  exchanges assemble the pieces. -/

section GenericFlatnessGeometricGlue

/-- Elementwise fibre-side `appLE` coherence: restricting the image of `appLE`
equals `appLE` into the smaller open. -/
private lemma appLE_res_apply {S X : Scheme.{u}} (p : X ⟶ S) {U : S.Opens}
    {W W' : X.Opens} (e : W ≤ p ⁻¹ᵁ U) (h : W' ≤ W) (u : Γ(S, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((p.appLE U W e).hom u) =
      (p.appLE U W' (h.trans e)).hom u := by
  have h1 := congrArg (fun (φ : Γ(S, U) ⟶ Γ(X, W')) => φ.hom u)
    (Scheme.Hom.appLE_map (f := p) e (homOfLE h).op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h1

/-- Elementwise base-side `appLE` coherence: `appLE` of a restricted base section
equals `appLE` from the larger base open. -/
private lemma appLE_base_res_apply {S X : Scheme.{u}} (p : X ⟶ S) {U U' : S.Opens}
    {W : X.Opens} (h : U' ≤ U) (e' : W ≤ p ⁻¹ᵁ U') (e : W ≤ p ⁻¹ᵁ U) (u : Γ(S, U)) :
    (p.appLE U' W e').hom ((S.presheaf.map (homOfLE h).op).hom u) =
      (p.appLE U W e).hom u := by
  have h1 := congrArg (fun (φ : Γ(S, U) ⟶ Γ(X, W)) => φ.hom u)
    (Scheme.Hom.map_appLE (f := p) e' (homOfLE h).op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h1

/-- Transport of section flatness along an equality of opens: the `Module.compHom`
structures via `appLE` agree definitionally because the `≤`-witness of `appLE` is
proof-irrelevant. -/
private theorem flat_sections_congr {S X : Scheme.{u}} (p : X ⟶ S) (F : X.Modules)
    {U₀ : S.Opens} {O₁ O₂ : X.Opens} (hEq : O₁ = O₂)
    (e₁ : O₁ ≤ p ⁻¹ᵁ U₀) (e₂ : O₂ ≤ p ⁻¹ᵁ U₀)
    (h : letI : Module Γ(S, U₀) Γ(F, O₁) := Module.compHom _ (p.appLE U₀ O₁ e₁).hom
         Module.Flat Γ(S, U₀) Γ(F, O₁)) :
    letI : Module Γ(S, U₀) Γ(F, O₂) := Module.compHom _ (p.appLE U₀ O₂ e₂).hom
    Module.Flat Γ(S, U₀) Γ(F, O₂) := by
  subst hEq
  exact h

open TensorProduct in
/-- **Mixed-base stability of flatness under module localization.**  Let `B` be an
`R`-algebra, `N` a `B`-module that is flat over `R`, and `g : N →ₗ[B] N'` a
localization of `N` at a submonoid `p ⊆ B`.  Then `N'` is still flat over `R`.

Mathlib's `Module.Flat.of_isLocalizedModule` treats only submonoids of `R`
itself; here the localization happens on the fibre side.  The proof rewrites
`𝟙 N' ⊗ f` as the `IsLocalizedModule.map` of `𝟙 N ⊗ f` (Mathlib's
`IsLocalizedModule.map_lTensor`, with the `IsLocalizedModule.rTensor` instances)
and uses that localization preserves injectivity
(`IsLocalizedModule.map_injective`). -/
theorem _root_.Module.Flat.of_isLocalizedModule_algebra {R B : Type v} [CommRing R]
    [CommRing B] [Algebra R B] (p : Submonoid B) {N N' : Type v} [AddCommGroup N]
    [Module R N] [Module B N] [IsScalarTower R B N] [AddCommGroup N'] [Module R N']
    [Module B N'] [IsScalarTower R B N'] (g : N →ₗ[B] N') [IsLocalizedModule p g]
    [Module.Flat R N] : Module.Flat R N' := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ I
  rw [← TensorProduct.AlgebraTensorModule.coe_lTensor (A := B)]
  rw [← IsLocalizedModule.map_lTensor (S := p) (g := g) (f := I.subtype)]
  exact IsLocalizedModule.map_injective p
    (TensorProduct.AlgebraTensorModule.rTensor R I g)
    (TensorProduct.AlgebraTensorModule.rTensor R P g)
    (TensorProduct.AlgebraTensorModule.lTensor B N I.subtype)
    (by
      rw [TensorProduct.AlgebraTensorModule.coe_lTensor (A := B)]
      exact Module.Flat.lTensor_preserves_injective_linearMap I.subtype
        Subtype.val_injective)

set_option maxHeartbeats 1200000 in
-- Heartbeat headroom: several `IsLocalizedModule`/scalar-tower instance chains
-- at localized section modules (qcqs section-localization engine).
/-- **Chart-basic core of generic flatness.**  Let `Wj ≤ p ⁻¹ᵁ U₀` be an affine
chart whose section module localized at `g ∈ Γ(S, U₀)` is free over
`Γ(S, U₀)_g` (the output of algebraic generic freeness), and let `c ∈ Γ(X, Wj)`
cut a basic open lying above the base basic open `D(g)`.  Then the sections of
`F` over `D(c)` (presented as any open `O = D(c)`) are flat over `Γ(S, U₀)`.

Proof: `D(β) = Wj ⊓ p ⁻¹ᵁ D(g)` for `β := appLE g`; the section restriction
`Γ(F, Wj) → Γ(F, D(β))` is a localization at `powers β` over `Γ(X, Wj)`
(Stacks 01P0) hence at `powers g` over `Γ(S, U₀)` (base-ring descent), so
`Γ(F, D(β))` inherits freeness-hence-flatness over `Γ(S, U₀)` from the
hypothesis; finally `Γ(F, D(β)) → Γ(F, D(c))` is a fibre-side localization,
absorbed by mixed-base stability. -/
private theorem flat_section_chartBasic {S X : Scheme.{u}} (p : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] {U₀ : S.Opens}
    {Wj : X.Opens} (hWj : IsAffineOpen Wj) (eWj : Wj ≤ p ⁻¹ᵁ U₀) (g : Γ(S, U₀))
    (hfree :
      letI : Module Γ(S, U₀) Γ(F, Wj) := Module.compHom _ (p.appLE U₀ Wj eWj).hom
      Module.Free (Localization.Away g)
        (LocalizedModule (Submonoid.powers g) Γ(F, Wj)))
    (c : Γ(X, Wj)) (hc : X.basicOpen c ≤ p ⁻¹ᵁ (S.basicOpen g))
    {O : X.Opens} (hO : O = X.basicOpen c) (eO : O ≤ p ⁻¹ᵁ U₀) :
    letI : Module Γ(S, U₀) Γ(F, O) := Module.compHom _ (p.appLE U₀ O eO).hom
    Module.Flat Γ(S, U₀) Γ(F, O) := by
  subst hO
  letI : Module Γ(S, U₀) Γ(F, Wj) := Module.compHom _ (p.appLE U₀ Wj eWj).hom
  -- the base element pushed into the chart ring, and its basic open
  set β : Γ(X, Wj) := (p.appLE U₀ Wj eWj).hom g with hβ
  have hDβ : X.basicOpen β = Wj ⊓ p ⁻¹ᵁ (S.basicOpen g) := by
    rw [hβ, show (p.appLE U₀ Wj eWj).hom g
        = (X.presheaf.map (homOfLE eWj).op).hom ((p.app U₀).hom g) from rfl]
    rw [Scheme.basicOpen_res, Scheme.preimage_basicOpen]
  have hDcβ : X.basicOpen c ≤ X.basicOpen β := by
    rw [hDβ]
    exact le_inf (X.basicOpen_le c) hc
  have eβ : X.basicOpen β ≤ p ⁻¹ᵁ U₀ := (X.basicOpen_le β).trans eWj
  -- (1) chart-side localization of sections at β (Stacks 01P0)
  letI : Module Γ(X, Wj) Γ(F, X.basicOpen β) :=
    Module.compHom _ (algebraMap Γ(X, Wj) Γ(X, X.basicOpen β))
  haveI : IsScalarTower Γ(X, Wj) Γ(X, X.basicOpen β) Γ(F, X.basicOpen β) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI hlocB : IsLocalizedModule (Submonoid.powers β)
      (Scheme.Modules.restrictBasicOpenₗ F β) :=
    Scheme.Modules.isLocalizedModule_basicOpen_of_isCompact F hWj.isCompact
      hWj.isQuasiSeparated β
  -- (2) `Γ(S, U₀)`-module structures and scalar towers
  letI : Algebra Γ(S, U₀) Γ(X, Wj) := (p.appLE U₀ Wj eWj).hom.toAlgebra
  letI : Module Γ(S, U₀) Γ(F, X.basicOpen β) :=
    Module.compHom _ (p.appLE U₀ (X.basicOpen β) eβ).hom
  haveI : IsScalarTower Γ(S, U₀) Γ(X, Wj) Γ(F, Wj) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI : IsScalarTower Γ(S, U₀) Γ(X, Wj) Γ(F, X.basicOpen β) :=
    IsScalarTower.of_algebraMap_smul (fun a n => by
      change (X.presheaf.map (homOfLE (X.basicOpen_le β)).op).hom
          ((p.appLE U₀ Wj eWj).hom a) • n
        = (p.appLE U₀ (X.basicOpen β) eβ).hom a • n
      rw [appLE_res_apply p eWj (X.basicOpen_le β) a])
  -- (3) base-ring descent of the localization, and flatness of `Γ(F, D(β))`
  haveI hlocA : IsLocalizedModule (Submonoid.powers g)
      ((Scheme.Modules.restrictBasicOpenₗ F β).restrictScalars Γ(S, U₀)) := by
    refine isLocalizedModule_powers_restrictScalars_of_algebraMap g _ ?_
    exact hlocB
  haveI hfreeg : Module.Free (Localization.Away g)
      (LocalizedModule (Submonoid.powers g) Γ(F, Wj)) := hfree
  haveI hflatLoc : Module.Flat Γ(S, U₀)
      (LocalizedModule (Submonoid.powers g) Γ(F, Wj)) := by
    haveI : Module.Flat (Localization.Away g)
        (LocalizedModule (Submonoid.powers g) Γ(F, Wj)) := inferInstance
    exact (Module.flat_iff_of_isLocalization (Localization.Away g)
      (Submonoid.powers g) (LocalizedModule (Submonoid.powers g) Γ(F, Wj))).mp this
  haveI hflatNβ : Module.Flat Γ(S, U₀) Γ(F, X.basicOpen β) :=
    Module.Flat.of_linearEquiv
      (IsLocalizedModule.iso (Submonoid.powers g)
        ((Scheme.Modules.restrictBasicOpenₗ F β).restrictScalars Γ(S, U₀))).symm
  -- (4) restrict from `D(β)` to `D(c)` and absorb by mixed-base stability
  set c' : Γ(X, X.basicOpen β) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le β)).op).hom c with hc'
  have hDc' : X.basicOpen c' = X.basicOpen c := by
    rw [hc', Scheme.basicOpen_res]
    exact inf_eq_right.mpr hDcβ
  have ec' : X.basicOpen c' ≤ p ⁻¹ᵁ U₀ := (X.basicOpen_le c').trans eβ
  letI : Module Γ(X, X.basicOpen β) Γ(F, X.basicOpen c') :=
    Module.compHom _ (algebraMap Γ(X, X.basicOpen β) Γ(X, X.basicOpen c'))
  haveI : IsScalarTower Γ(X, X.basicOpen β) Γ(X, X.basicOpen c')
      Γ(F, X.basicOpen c') :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI hlocC : IsLocalizedModule (Submonoid.powers c')
      (Scheme.Modules.restrictBasicOpenₗ F c') :=
    Scheme.Modules.isLocalizedModule_basicOpen_of_isCompact F
      (hWj.basicOpen β).isCompact (hWj.basicOpen β).isQuasiSeparated c'
  letI : Module Γ(S, U₀) Γ(F, X.basicOpen c') :=
    Module.compHom _ (p.appLE U₀ (X.basicOpen c') ec').hom
  letI : Algebra Γ(S, U₀) Γ(X, X.basicOpen β) :=
    (p.appLE U₀ (X.basicOpen β) eβ).hom.toAlgebra
  haveI : IsScalarTower Γ(S, U₀) Γ(X, X.basicOpen β) Γ(F, X.basicOpen β) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI : IsScalarTower Γ(S, U₀) Γ(X, X.basicOpen β) Γ(F, X.basicOpen c') :=
    IsScalarTower.of_algebraMap_smul (fun a n => by
      change (X.presheaf.map (homOfLE (X.basicOpen_le c')).op).hom
          ((p.appLE U₀ (X.basicOpen β) eβ).hom a) • n
        = (p.appLE U₀ (X.basicOpen c') ec').hom a • n
      rw [appLE_res_apply p eβ (X.basicOpen_le c') a])
  haveI hflatC' : Module.Flat Γ(S, U₀) Γ(F, X.basicOpen c') :=
    Module.Flat.of_isLocalizedModule_algebra (Submonoid.powers c')
      (Scheme.Modules.restrictBasicOpenₗ F c')
  exact flat_sections_congr p F hDc' ec' eO hflatC'

set_option maxHeartbeats 1600000 in
-- Heartbeat headroom: per-piece instance provisioning under binders for the
-- `flat_of_isLocalized_span` application.
/-- **Two-layer basic-open reduction for generic flatness.**  Given affine charts
`Wc j ≤ p ⁻¹ᵁ U₀` covering `p ⁻¹ᵁ U₀`, all of whose section modules localized
at `f ∈ Γ(S, U₀)` are free (the output of algebraic generic freeness at a
common denominator `f`), every affine pair `U ≤ D(f)`, `W ≤ p ⁻¹ᵁ U` has flat
sections: cover `W` by opens simultaneously basic in `W` and in a chart, lying
above base basic opens common to `U` and `U₀`; conclude with
`Module.flat_of_isLocalized_span` over `Γ(X, W)` and the two
`Module.flat_iff_of_isLocalization` exchanges on the base. -/
private theorem flat_section_pair {S X : Scheme.{u}} (p : X ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] {U₀ : S.Opens} (hU₀ : IsAffineOpen U₀)
    {ι : Type u} (Wc : ι → X.Opens) (hWc : ∀ j, IsAffineOpen (Wc j))
    (eWc : ∀ j, Wc j ≤ p ⁻¹ᵁ U₀)
    (hcover : ∀ x ∈ p ⁻¹ᵁ U₀, ∃ j, x ∈ Wc j) (f : Γ(S, U₀))
    (hfree : ∀ j,
      letI : Module Γ(S, U₀) Γ(F, Wc j) :=
        Module.compHom _ (p.appLE U₀ (Wc j) (eWc j)).hom
      Module.Free (Localization.Away f)
        (LocalizedModule (Submonoid.powers f) Γ(F, Wc j)))
    {U : S.Opens} (hU : IsAffineOpen U) (hUf : U ≤ S.basicOpen f)
    {W : X.Opens} (hW : IsAffineOpen W) (e : W ≤ p ⁻¹ᵁ U) :
    letI : Module Γ(S, U) Γ(F, W) := Module.compHom _ (p.appLE U W e).hom
    Module.Flat Γ(S, U) Γ(F, W) := by
  letI : Module Γ(S, U) Γ(F, W) := Module.compHom _ (p.appLE U W e).hom
  have hUU₀ : U ≤ U₀ := hUf.trans (S.basicOpen_le f)
  have hWU₀ : W ≤ p ⁻¹ᵁ U₀ := e.trans (fun x hx => hUU₀ hx)
  -- per-point choice of a simultaneous basic open
  have Hx : ∀ x : ↥W, ∃ (b : Γ(X, W)) (a : Γ(S, U)) (a' : Γ(S, U₀)) (j : ι)
      (c : Γ(X, Wc j)),
      X.basicOpen b = X.basicOpen c ∧ (x : X) ∈ X.basicOpen b ∧
      S.basicOpen a = S.basicOpen a' ∧
      X.basicOpen b ≤ p ⁻¹ᵁ (S.basicOpen a) := by
    intro x
    have hxU : p.base x.1 ∈ U := e x.2
    have hxU₀ : p.base x.1 ∈ U₀ := hUU₀ hxU
    obtain ⟨a, a', haa', hpa⟩ :=
      AlgebraicGeometry.exists_basicOpen_le_affine_inter hU hU₀ (p.base x.1)
        ⟨hxU, hxU₀⟩
    obtain ⟨j, hxj⟩ := hcover x.1 (hWU₀ x.2)
    have hxT : x.1 ∈ (W ⊓ (p ⁻¹ᵁ S.basicOpen a ⊓ Wc j) : X.Opens) :=
      ⟨x.2, ⟨hpa, hxj⟩⟩
    obtain ⟨b₁, hb₁le, hxb₁⟩ := hW.exists_basicOpen_le
      (⟨x.1, hxT⟩ : ↥(W ⊓ (p ⁻¹ᵁ S.basicOpen a ⊓ Wc j) : X.Opens)) x.2
    obtain ⟨f₁, c, hfc, hxf₁⟩ := AlgebraicGeometry.exists_basicOpen_le_affine_inter
      (hW.basicOpen b₁) (hWc j) x.1 ⟨hxb₁, hxj⟩
    obtain ⟨b, hb⟩ := hW.basicOpen_basicOpen_is_basicOpen b₁ f₁
    exact ⟨b, a, a', j, c, hb.trans hfc, hb.symm ▸ hxf₁, haa',
      hb.symm ▸ ((X.basicOpen_le f₁).trans
        (hb₁le.trans (inf_le_right.trans inf_le_left)))⟩
  choose bb aa aa' jj cc hbc hxb haa' hba using Hx
  -- the covering family spans `Γ(X, W)`
  have hspan : Ideal.span (Set.range bb) = ⊤ := by
    rw [← hW.iSup_basicOpen_eq_self_iff]
    apply le_antisymm
    · exact iSup_le fun r => X.basicOpen_le _
    · intro y hy
      exact TopologicalSpace.Opens.mem_iSup.mpr
        ⟨⟨bb ⟨y, hy⟩, Set.mem_range_self _⟩, hxb ⟨y, hy⟩⟩
  -- instance packs for the span lemma
  letI : Algebra Γ(S, U) Γ(X, W) := (p.appLE U W e).hom.toAlgebra
  haveI : IsScalarTower Γ(S, U) Γ(X, W) Γ(F, W) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI instBpiece : ∀ r : Set.range bb, Module Γ(X, W) Γ(F, X.basicOpen r.1) :=
    fun r => Module.compHom _ (algebraMap Γ(X, W) Γ(X, X.basicOpen r.1))
  haveI instTowerB : ∀ r : Set.range bb,
      IsScalarTower Γ(X, W) Γ(X, X.basicOpen r.1) Γ(F, X.basicOpen r.1) :=
    fun r => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI instLoc : ∀ r : Set.range bb, IsLocalizedModule (Submonoid.powers r.1)
      (Scheme.Modules.restrictBasicOpenₗ F r.1) := fun r =>
    Scheme.Modules.isLocalizedModule_basicOpen_of_isCompact F hW.isCompact
      hW.isQuasiSeparated r.1
  letI instRpiece : ∀ r : Set.range bb, Module Γ(S, U) Γ(F, X.basicOpen r.1) :=
    fun r =>
      Module.compHom _ (p.appLE U (X.basicOpen r.1) ((X.basicOpen_le r.1).trans e)).hom
  haveI instTowerR : ∀ r : Set.range bb,
      IsScalarTower Γ(S, U) Γ(X, W) Γ(F, X.basicOpen r.1) := fun r =>
    IsScalarTower.of_algebraMap_smul fun u n => by
      change (X.presheaf.map (homOfLE (X.basicOpen_le r.1)).op).hom
          ((p.appLE U W e).hom u) • n
        = (p.appLE U (X.basicOpen r.1) ((X.basicOpen_le r.1).trans e)).hom u • n
      rw [appLE_res_apply p e (X.basicOpen_le r.1) u]
  -- assemble by the span criterion; the pieces are handled below
  refine Module.flat_of_isLocalized_span (R := Γ(S, U)) Γ(X, W) Γ(F, W)
    (Set.range bb) hspan (fun r => Γ(F, X.basicOpen r.1))
    (fun r => Scheme.Modules.restrictBasicOpenₗ F r.1) ?_
  -- per-piece flatness
  intro r
  obtain ⟨x, hx⟩ := r.2
  have hbar : X.basicOpen r.1 ≤ p ⁻¹ᵁ (S.basicOpen (aa x)) := hx ▸ hba x
  have hbcr : X.basicOpen r.1 = X.basicOpen (cc x) := hx ▸ hbc x
  have epieceU₀ : X.basicOpen r.1 ≤ p ⁻¹ᵁ U₀ := (X.basicOpen_le r.1).trans hWU₀
  have haU : S.basicOpen (aa x) ≤ U := S.basicOpen_le (aa x)
  have haU₀ : S.basicOpen (aa x) ≤ U₀ :=
    (haa' x).symm ▸ S.basicOpen_le (aa' x)
  -- module structures over the three base rings
  letI mA : Module Γ(S, S.basicOpen (aa x)) Γ(F, X.basicOpen r.1) :=
    Module.compHom _ (p.appLE (S.basicOpen (aa x)) (X.basicOpen r.1) hbar).hom
  letI mA0 : Module Γ(S, U₀) Γ(F, X.basicOpen r.1) :=
    Module.compHom _ (p.appLE U₀ (X.basicOpen r.1) epieceU₀).hom
  -- localization instances on the base
  haveI hloc1 : IsLocalization.Away (aa x) Γ(S, S.basicOpen (aa x)) :=
    hU.isLocalization_basicOpen (aa x)
  haveI tow1 : IsScalarTower Γ(S, U) Γ(S, S.basicOpen (aa x))
      Γ(F, X.basicOpen r.1) :=
    IsScalarTower.of_algebraMap_smul fun u n => by
      change (p.appLE (S.basicOpen (aa x)) (X.basicOpen r.1) hbar).hom
          ((S.presheaf.map (homOfLE haU).op).hom u) • n
        = (p.appLE U (X.basicOpen r.1) ((X.basicOpen_le r.1).trans e)).hom u • n
      rw [appLE_base_res_apply p haU hbar ((X.basicOpen_le r.1).trans e) u]
  letI algA : Algebra Γ(S, U₀) Γ(S, S.basicOpen (aa x)) :=
    ((S.presheaf.map (homOfLE haU₀).op).hom).toAlgebra
  haveI hloc2 : IsLocalization.Away (aa' x) Γ(S, S.basicOpen (aa x)) :=
    hU₀.isLocalization_of_eq_basicOpen (aa' x) (homOfLE haU₀) (haa' x)
  haveI tow2 : IsScalarTower Γ(S, U₀) Γ(S, S.basicOpen (aa x))
      Γ(F, X.basicOpen r.1) :=
    IsScalarTower.of_algebraMap_smul fun u n => by
      change (p.appLE (S.basicOpen (aa x)) (X.basicOpen r.1) hbar).hom
          ((S.presheaf.map (homOfLE haU₀).op).hom u) • n
        = (p.appLE U₀ (X.basicOpen r.1) epieceU₀).hom u • n
      rw [appLE_base_res_apply p haU₀ hbar epieceU₀ u]
  -- flatness over `Γ(S, U₀)` from the chart-basic core
  have hA : Module.Flat Γ(S, U₀) Γ(F, X.basicOpen r.1) := by
    have hDaf : S.basicOpen (aa x) ≤ S.basicOpen f := haU.trans hUf
    have hcle : X.basicOpen (cc x) ≤ p ⁻¹ᵁ (S.basicOpen (f * aa' x)) := by
      have h1 : X.basicOpen (cc x) ≤ p ⁻¹ᵁ (S.basicOpen (aa x)) := hbcr ▸ hbar
      have h2 : S.basicOpen (aa x) ≤ S.basicOpen (f * aa' x) := by
        rw [Scheme.basicOpen_mul]
        exact le_inf hDaf (haa' x).le
      exact h1.trans (fun y hy => h2 hy)
    letI mWj : Module Γ(S, U₀) Γ(F, Wc (jj x)) :=
      Module.compHom _ (p.appLE U₀ (Wc (jj x)) (eWc (jj x))).hom
    have hfree_g :
        Module.Free (Localization.Away (f * aa' x))
          (LocalizedModule (Submonoid.powers (f * aa' x)) Γ(F, Wc (jj x))) :=
      GenericFreeness.free_localizedModule_powers_mul Γ(S, U₀) Γ(F, Wc (jj x))
        f (aa' x) (hfree (jj x))
    exact flat_section_chartBasic p F (hWc (jj x)) (eWc (jj x)) (f * aa' x)
      hfree_g (cc x) hcle hbcr epieceU₀
  -- exchange the base ring twice: `U₀ → D(aa x) → U`
  have h2 : Module.Flat Γ(S, S.basicOpen (aa x)) Γ(F, X.basicOpen r.1) :=
    (Module.flat_iff_of_isLocalization (R := Γ(S, U₀))
      Γ(S, S.basicOpen (aa x)) (Submonoid.powers (aa' x))
      Γ(F, X.basicOpen r.1)).mpr hA
  exact (Module.flat_iff_of_isLocalization (R := Γ(S, U))
    Γ(S, S.basicOpen (aa x)) (Submonoid.powers (aa x))
    Γ(F, X.basicOpen r.1)).mp h2

end GenericFlatnessGeometricGlue

/-! ## §2. Generic flatness (Nitsure §4)

Over a noetherian integral base `S`, a coherent sheaf on a finite-type
`X ⟶ S` is flat above some non-empty open `V ⊆ S`. This is the inductive
engine of the flattening-stratification theorem: combined with
Noetherian induction on the closed complement `S ∖ V`, it produces the
finite stratification of `S` by flatness loci.

Algebraically (blueprint node `generic_flatness_algebraic`): for a
noetherian domain `A`, a finite-type `A`-algebra `B`, and a finite
`B`-module `M`, there exists a non-zero `f ∈ A` such that `M_f` is a
free `A_f`-module. The geometric form (this declaration) restricts to a
non-empty affine open `Spec A ⊆ S` and applies the algebraic form on
each finite-type-algebra patch of `X` above `Spec A`.

Blueprint reference: `thm:generic_flatness` (Nitsure §4). -/

/-- **Generic flatness theorem, quasi-coherent core** (Nitsure §4).

For a noetherian integral scheme `S`, a finite-type morphism `p : X ⟶ S`,
and a quasi-coherent `𝓞_X`-module `𝓕` equipped with a supply of affine
charts with finite section modules (`hfin` — for finitely presented `𝓕`
this is Stacks 01PC, see `genericFlatness` below; for pulled-back sheaves
in the flattening-stratification induction it comes from
`finite_section_pullback_piece`), there exists a non-empty open subscheme
`V ⊆ S` such that `𝓕|_{X_V} = 𝓕|_{p⁻¹V}` is flat over `𝓞_V`.

The proof follows Nitsure §4: pass to a non-empty affine
open `U₀ ⊆ S` with `A := Γ(S, U₀)` a noetherian domain, cover the compact
preimage `p ⁻¹ᵁ U₀` by finitely many affine charts with finitely generated
sections (`Scheme.Modules.exists_affine_finite_sections_nhds`, Stacks 01PC),
apply algebraic generic freeness (`GenericFreeness.genericFlatnessAlgebraic`)
on each chart, and take `f ∈ A` the product of the witnesses.  The witness
open is `V := D(f)`, non-empty since `A` is a domain and `f ≠ 0`; the
quantified flatness on affine pairs below `V` is `flat_section_pair` (§1b).

The `[QuasiCompact p]` hypothesis is essential: Nitsure requires `p` of
**finite type** in the EGA sense, i.e. quasi-compact *and* locally of finite
type.  With `LocallyOfFiniteType` alone the statement is false: for
`X = ⨿_q Spec 𝔽_q → Spec ℤ` (locally of finite type, not quasi-compact,
structure sheaf finitely presented) every non-empty open `V ⊆ Spec ℤ`
contains all but finitely many primes `q`, and `𝔽_q` is never flat over the
corresponding `ℤ[1/n]`.  Quasi-compactness is what bounds the number of
denominators to clear. -/
theorem genericFlatness_of_finite_sections {S X : Scheme.{u}} [IsIntegral S]
    [IsLocallyNoetherian S] (p : X ⟶ S) [QuasiCompact p] [LocallyOfFiniteType p]
    (F : X.Modules) [F.IsQuasicoherent]
    (hfin : ∀ (x : X) (O : X.Opens), x ∈ O → ∃ V : X.Opens, IsAffineOpen V ∧
      x ∈ V ∧ V ≤ O ∧ Module.Finite Γ(X, V) Γ(F, V)) :
    ∃ (V : S.Opens), (V : Set S).Nonempty ∧
      ∀ {U : S.Opens} (_ : IsAffineOpen U) (_ : U ≤ V) {W : X.Opens}
        (_ : IsAffineOpen W) (e : W ≤ p ⁻¹ᵁ U),
        letI : Module Γ(S, U) Γ(F, W) := Module.compHom _ (p.appLE U W e).hom
        Module.Flat Γ(S, U) Γ(F, W) := by
  classical
  -- an ambient nonempty affine chart of the integral base
  obtain ⟨x₀⟩ : Nonempty S := inferInstance
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hx₀U₀, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₀) isOpen_univ
  haveI : IsDomain Γ(S, U₀) := @IsIntegral.component_integral _ _ _ ⟨⟨x₀, hx₀U₀⟩⟩
  haveI : IsNoetherianRing Γ(S, U₀) :=
    IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  -- affine charts with finitely generated sections covering the compact preimage
  have hK : IsCompact ((p ⁻¹ᵁ U₀ : X.Opens) : Set X) :=
    p.isCompact_preimage hU₀.isCompact
  have HX : ∀ x : X, x ∈ p ⁻¹ᵁ U₀ → ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧
      V ≤ p ⁻¹ᵁ U₀ ∧ Module.Finite Γ(X, V) Γ(F, V) := fun x hx =>
    hfin x (p ⁻¹ᵁ U₀) hx
  choose! V hVaff hxV hVle hVfin using HX
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun x : ↥(p ⁻¹ᵁ U₀ : X.Opens) => ((V x.1 : X.Opens) : Set X))
    (fun x => (V x.1).2)
    (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxV y hy⟩)
  -- per-chart generic freeness over `A := Γ(S, U₀)`
  have hGF : ∀ i : ↥t, ∃ fi : Γ(S, U₀), fi ≠ 0 ∧
      (letI : Module Γ(S, U₀) Γ(F, V i.1.1) :=
        Module.compHom _ (p.appLE U₀ (V i.1.1) (hVle i.1.1 i.1.2)).hom
      Module.Free (Localization.Away fi)
        (LocalizedModule (Submonoid.powers fi) Γ(F, V i.1.1))) := by
    intro i
    letI : Module Γ(S, U₀) Γ(F, V i.1.1) :=
      Module.compHom _ (p.appLE U₀ (V i.1.1) (hVle i.1.1 i.1.2)).hom
    letI : Algebra Γ(S, U₀) Γ(X, V i.1.1) :=
      (p.appLE U₀ (V i.1.1) (hVle i.1.1 i.1.2)).hom.toAlgebra
    haveI : IsScalarTower Γ(S, U₀) Γ(X, V i.1.1) Γ(F, V i.1.1) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    haveI hft : Algebra.FiniteType Γ(S, U₀) Γ(X, V i.1.1) :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) p ‹_› ⟨U₀, hU₀⟩
        ⟨V i.1.1, hVaff i.1.1 i.1.2⟩ (hVle i.1.1 i.1.2)
    haveI := hVfin i.1.1 i.1.2
    exact GenericFreeness.genericFlatnessAlgebraic Γ(S, U₀) Γ(X, V i.1.1)
      Γ(F, V i.1.1)
  choose ff hff0 hffree using hGF
  -- the common denominator
  set f : Γ(S, U₀) := ∏ i ∈ (Finset.univ : Finset ↥t), ff i with hfdef
  have hf0 : f ≠ 0 := by
    rw [hfdef]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hff0 i
  refine ⟨S.basicOpen f, ?_, ?_⟩
  · -- non-emptiness: on a reduced scheme `D(f) = ⊥` forces `f = 0`
    rw [← TopologicalSpace.Opens.ne_bot_iff_nonempty]
    intro hbot
    exact hf0 ((basicOpen_eq_bot_iff f).mp hbot)
  · -- flatness on every affine pair below `D(f)`, via the two-layer reduction
    intro U hU hUf W hW e
    refine flat_section_pair p F hU₀ (fun i : ↥t => V i.1.1)
      (fun i => hVaff i.1.1 i.1.2) (fun i => hVle i.1.1 i.1.2) ?_ f ?_ hU hUf hW e
    · -- the charts cover `p ⁻¹ᵁ U₀`
      intro x hx
      have := ht hx
      rw [Set.mem_iUnion₂] at this
      obtain ⟨i, hi, hxi⟩ := this
      exact ⟨⟨i, hi⟩, hxi⟩
    · -- freeness at the common denominator, chart by chart
      intro i
      letI : Module Γ(S, U₀) Γ(F, V i.1.1) :=
        Module.compHom _ (p.appLE U₀ (V i.1.1) (hVle i.1.1 i.1.2)).hom
      have h1 := GenericFreeness.free_localizedModule_powers_mul Γ(S, U₀)
        Γ(F, V i.1.1) (ff i) (∏ j ∈ Finset.univ.erase i, ff j) (hffree i)
      rwa [Finset.mul_prod_erase _ _ (Finset.mem_univ i)] at h1

/-- **Generic flatness theorem**, finitely-presented form (Nitsure §4).  The
statement of `thm:generic_flatness`: the chart supply of
`genericFlatness_of_finite_sections` is discharged by Stacks 01PC
(`Scheme.Modules.exists_affine_finite_sections_nhds`). -/
theorem genericFlatness {S X : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
    (p : X ⟶ S) [QuasiCompact p] [LocallyOfFiniteType p] (F : X.Modules)
    [F.IsFinitePresentation] :
    ∃ (V : S.Opens), (V : Set S).Nonempty ∧
      ∀ {U : S.Opens} (_ : IsAffineOpen U) (_ : U ≤ V) {W : X.Opens}
        (_ : IsAffineOpen W) (e : W ≤ p ⁻¹ᵁ U),
        letI : Module Γ(S, U) Γ(F, W) := Module.compHom _ (p.appLE U W e).hom
        Module.Flat Γ(S, U) Γ(F, W) :=
  genericFlatness_of_finite_sections p F
    (fun x O hxO => Scheme.Modules.exists_affine_finite_sections_nhds F x O hxO)

/-! ## §3. Flatness under pushout base change (algebra core)

Let `R → S` and `R → A` be ring maps with pushout `B = S ⊗[R] A`
(`Algebra.IsPushout R S A B`), and let `M` be an `A`-module that is flat
over `R`.  Then `B ⊗[A] M` — and hence any base change of `M` along
`A → B` — is flat over `S`.  This is the module form of "flatness is
stable under arbitrary base change" (Stacks 00HI item (3), relative
form).  Mathlib has the special case `Module.Flat.baseChange`
(`A = R`, `B = S`) and the ring form
`RingHom.Flat.isStableUnderBaseChange`, but not this mixed module form.

The engine is `isBaseChange_pushout_tensorProduct`: `B ⊗[A] M` *is* the
base change of `M` along `R → S`, i.e. `B ⊗[A] M = S ⊗[R] M`.  The proof
is by the universal property (`IsBaseChange.of_lift_unique`): an
`R`-linear map `g : M → Q` into an `S`-module extends to `B ⊗[A] M` by
lifting the `A`-indexed family `a ↦ (m ↦ g (a • m))` through the ring
base change `B = S ⊗[R] A` (`Algebra.IsPushout.out.lift`) and applying
the balanced-product constructor `TensorProduct.liftAddHom`. -/

section FlatPushout

open TensorProduct

variable (R S A B : Type v) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
variable [IsScalarTower R A B] [IsScalarTower R S B]
variable (M : Type v) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

attribute [local instance] SMulCommClass.of_commMonoid

set_option maxSynthPendingDepth 3 in
/-- **`B ⊗[A] M` is the base change of `M` along `R → S`** for a pushout square
`B = S ⊗[R] A` [Stacks 00HI, module form].  The `S`-module structure on
`B ⊗[A] M` is through the left factor. -/
theorem isBaseChange_pushout_tensorProduct [h : Algebra.IsPushout R S A B] :
    IsBaseChange S (((TensorProduct.mk A B M) 1).restrictScalars R) := by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ g
  -- the `A`-indexed family of `R`-linear maps `m ↦ g (a • m)`
  let β : A →ₗ[R] (M →ₗ[R] Q) :=
    { toFun := fun a =>
        { toFun := fun m => g (a • m)
          map_add' := fun x y => by rw [smul_add, map_add]
          map_smul' := fun r x => by
            rw [RingHom.id_apply, smul_comm, map_smul] }
      map_add' := fun a₁ a₂ => LinearMap.ext fun m => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, add_smul, map_add,
          LinearMap.add_apply]
      map_smul' := fun r a => LinearMap.ext fun m => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
          LinearMap.smul_apply, ← map_smul, smul_assoc] }
  -- lift it through the ring base change `B = S ⊗[R] A`
  let Λ : B →ₗ[S] (M →ₗ[R] Q) := h.out.lift β
  have hΛ_alg : ∀ a : A, Λ (algebraMap A B a) = β a := fun a => by
    simpa only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom'] using
      h.out.lift_eq β a
  -- balancedness of the pairing `(b, m) ↦ Λ b m` over `A`
  have hbal : ∀ (a : A) (b : B) (m : M),
      Λ (algebraMap A B a * b) m = Λ b (a • m) := by
    intro a b m
    induction b using h.out.inductionOn with
    | zero => rw [mul_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
    | tmul a' =>
      rw [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', ← map_mul,
        hΛ_alg, hΛ_alg]
      change g ((a * a') • m) = g (a' • a • m)
      rw [← smul_smul, smul_comm]
    | smul s b e =>
      rw [mul_smul_comm, map_smul, LinearMap.smul_apply, e, map_smul Λ s b,
        LinearMap.smul_apply]
    | add b₁ b₂ e₁ e₂ =>
      rw [mul_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
        e₁, e₂]
  -- the balanced-product extension `B ⊗[A] M →+ Q`
  let h₀ : B ⊗[A] M →+ Q := TensorProduct.liftAddHom
    { toFun := fun b => (Λ b).toAddMonoidHom
      map_zero' := by ext m; simp only [map_zero, LinearMap.toAddMonoidHom_coe,
        LinearMap.zero_apply, AddMonoidHom.zero_apply]
      map_add' := fun b₁ b₂ => by
        ext m
        simp only [map_add, LinearMap.toAddMonoidHom_coe, LinearMap.add_apply,
          AddMonoidHom.add_apply] }
    (fun a b m => by
      simpa only [Algebra.smul_def, LinearMap.toAddMonoidHom_coe,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk] using hbal a b m)
  have h₀_tmul : ∀ (b : B) (m : M), h₀ (b ⊗ₜ m) = Λ b m := fun b m =>
    TensorProduct.liftAddHom_tmul _ _ b m
  -- `S`-linearity of the extension
  have hS : ∀ (s : S) (x : B ⊗[A] M), h₀ (s • x) = s • h₀ x := by
    intro s x
    induction x with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul b m =>
      rw [smul_tmul', h₀_tmul, h₀_tmul, map_smul, LinearMap.smul_apply]
    | add x y ex ey => rw [smul_add, map_add, ex, ey, map_add, smul_add]
  refine ⟨{ toFun := h₀, map_add' := map_add h₀, map_smul' := hS }, ?_, ?_⟩
  · -- the extension restricts to `g` along `m ↦ 1 ⊗ m`
    apply LinearMap.ext
    intro m
    change h₀ ((1 : B) ⊗ₜ m) = g m
    rw [h₀_tmul, show (1 : B) = algebraMap A B 1 from (map_one _).symm, hΛ_alg]
    change g ((1 : A) • m) = g m
    rw [one_smul]
  · -- uniqueness
    intro h' hh'
    apply LinearMap.ext
    intro x
    change h' x = h₀ x
    induction x with
    | zero => rw [map_zero, map_zero]
    | tmul b m =>
      rw [h₀_tmul]
      induction b using h.out.inductionOn with
      | zero => rw [zero_tmul, map_zero, map_zero, LinearMap.zero_apply]
      | tmul a =>
        rw [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', hΛ_alg]
        have : (algebraMap A B a) ⊗ₜ[A] m = (1 : B) ⊗ₜ[A] (a • m) := by
          rw [Algebra.algebraMap_eq_smul_one, smul_tmul]
        rw [this]
        have h2 := congrArg (fun (φ : M →ₗ[R] Q) => φ (a • m)) hh'
        simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars,
          Function.comp_apply, TensorProduct.mk_apply] at h2
        exact h2
      | smul s b e =>
        rw [← smul_tmul', map_smul, e, map_smul Λ s b, LinearMap.smul_apply]
      | add b₁ b₂ e₁ e₂ =>
        rw [add_tmul, map_add, map_add, LinearMap.add_apply, e₁, e₂]
    | add x y ex ey => rw [map_add, map_add, ex, ey]

set_option maxSynthPendingDepth 3 in
/-- **Flatness under pushout base change** [Stacks 00HI, module form].  Let
`B = S ⊗[R] A` be a pushout of rings (`Algebra.IsPushout R S A B`), `M` an
`A`-module flat over `R`, and `N` a `B`-module which is a base change of `M`
along `A → B` (`IsBaseChange B f`).  Then `N` is flat over `S` (acting through
`S → B`).  Mathlib covers `A = R`, `B = S` (`Module.Flat.baseChange`); this
mixed form is the per-piece engine of the flattening stratification. -/
theorem _root_.Module.Flat.of_isPushout [h : Algebra.IsPushout R S A B]
    {N : Type v} [AddCommGroup N] [Module A N] [Module B N] [Module S N]
    [IsScalarTower A B N] [IsScalarTower S B N]
    {f : M →ₗ[A] N} (hf : IsBaseChange B f) [Module.Flat R M] :
    Module.Flat S N := by
  haveI : Module.Flat S (B ⊗[A] M) :=
    Module.Flat.isBaseChange (R := R) (S := S) (M := M) (B ⊗[A] M)
      (isBaseChange_pushout_tensorProduct R S A B M)
  exact Module.Flat.of_linearEquiv (hf.equiv.restrictScalars S).symm

end FlatPushout

/-! ## §4. Affine pieces of a fibre-product square

For a cartesian square `H : IsPullback g iY iX f` (so `Y = X ×ₛ T` with
projections `g : Y ⟶ X`, `iY : Y ⟶ T` over `iX : X ⟶ S`, `f : T ⟶ S`) and
affine opens `US ⊆ S`, `UX ⊆ iX⁻¹US`, `UT ⊆ f⁻¹US`, the **piece**
`UY := g⁻¹UX ⊓ iY⁻¹UT ⊆ Y` is an affine open whose section ring is the
pushout `Γ(X,UX) ⊗_{Γ(S,US)} Γ(T,UT)` (Mathlib's
`isIso_pushoutSection_of_isAffineOpen`), and whose `F`-pullback sections are
the base change `Γ(Y,UY) ⊗_{Γ(X,UX)} Γ(F,UX)` (the section formula
`pullback_app_isoTensor_baseMap_sectionLinearEquiv`, Stacks 01HQ/01I8).
Combining the two with `Module.Flat.of_isPushout` (§3) transports flatness
of `Γ(F,UX)` over `Γ(S,US)` to flatness of the piece sections over
`Γ(T,UT)`; `Module.Finite.base_change` similarly transports finiteness over
the fibre ring.  These are the two per-piece inputs of the
flattening-stratification induction. -/

section PullbackPiece

open TensorProduct

variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
variable (H : IsPullback g iY iX f)
variable {US : S.Opens} {UT : T.Opens} {UX : X.Opens}
variable (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US)

include H hUST hUSX

/-- The piece `g⁻¹UX ⊓ iY⁻¹UT` of a fibre-product square over affine opens is
affine: it is isomorphic to the pullback of the restricted affine cospan
(`Scheme.Hom.isPullback_resLE`). -/
theorem isAffineOpen_pullback_piece (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT)
    (hUX : IsAffineOpen UX) : IsAffineOpen (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) := by
  have : IsAffine US := hUS
  have : IsAffine UT := hUT
  have : IsAffine UX := hUX
  exact IsAffine.of_isIso (Scheme.Hom.isPullback_resLE H hUST hUSX rfl).isoPullback.hom

/-- The section-ring square of a fibre-product square at an affine piece is a
pushout in `CommRingCat` (Mathlib's `isIso_pushoutSection_of_isAffineOpen`,
repackaged). -/
theorem isPushout_appLE_pullback_piece (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT)
    (hUX : IsAffineOpen UX) :
    CategoryTheory.IsPushout (iX.appLE US UX hUSX) (f.appLE US UT hUST)
      (g.appLE UX (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_left)
      (iY.appLE UT (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_right) :=
  (isIso_pushoutSection_iff H hUST hUSX rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H hUST hUSX rfl hUS hUT hUX)

set_option maxSynthPendingDepth 3 in
/-- **Per-piece flatness transfer.**  If the `F`-sections on the affine
`UX ⊆ X` are flat over the affine `US ⊆ S`, then for any affine `UT ⊆ T`
above `US`, the pulled-back sections on the piece `g⁻¹UX ⊓ iY⁻¹UT ⊆ Y` are
flat over `UT`.  This is `Module.Flat.of_isPushout` (§3) fed with the ring
pushout of `isPushout_appLE_pullback_piece` and the base-change
section formula. -/
theorem flat_section_pullback_piece (F : X.Modules) [F.IsQuasicoherent]
    (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT) (hUX : IsAffineOpen UX)
    (hflat :
      letI : Module Γ(S, US) Γ(F, UX) := Module.compHom _ (iX.appLE US UX hUSX).hom
      Module.Flat Γ(S, US) Γ(F, UX)) :
    letI : Module Γ(T, UT) Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :=
      Module.compHom _ (iY.appLE UT (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_right).hom
    Module.Flat Γ(T, UT) Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) := by
  have hUY : IsAffineOpen (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :=
    isAffineOpen_pullback_piece H hUST hUSX hUS hUT hUX
  -- ring algebra structures on the four corners
  letI : Algebra Γ(S, US) Γ(X, UX) := (iX.appLE US UX hUSX).hom.toAlgebra
  letI : Algebra Γ(S, US) Γ(T, UT) := (f.appLE US UT hUST).hom.toAlgebra
  letI : Algebra Γ(X, UX) Γ(Y, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :=
    (g.appLE UX (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_left).hom.toAlgebra
  letI : Algebra Γ(T, UT) Γ(Y, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :=
    (iY.appLE UT (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_right).hom.toAlgebra
  letI : Algebra Γ(S, US) Γ(Y, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :=
    ((g.appLE UX (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_left).hom.comp
      (iX.appLE US UX hUSX).hom).toAlgebra
  haveI : IsScalarTower Γ(S, US) Γ(X, UX) Γ(Y, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(S, US) Γ(T, UT) Γ(Y, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :=
    IsScalarTower.of_algebraMap_eq' (by
      change ((g.appLE UX _ inf_le_left).hom.comp (iX.appLE US UX hUSX).hom) =
        (iY.appLE UT _ inf_le_right).hom.comp (f.appLE US UT hUST).hom
      have key : ∀ (φ : Y ⟶ S) (_ : iY ≫ f = φ)
          (w₁ : (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) ≤ φ ⁻¹ᵁ US)
          (w₂ : (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) ≤ (iY ≫ f) ⁻¹ᵁ US),
          φ.appLE US (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) w₁ =
            (iY ≫ f).appLE US (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) w₂ := by
        rintro φ rfl w₁ w₂; rfl
      have h1 : iX.appLE US UX hUSX ≫ g.appLE UX (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_left =
          f.appLE US UT hUST ≫ iY.appLE UT (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_right := by
        rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact key (g ≫ iX) H.w.symm _ _
      exact congrArg CommRingCat.Hom.hom h1)
  -- the pushout of section rings, in `Algebra.IsPushout` form
  haveI hpo₁ : Algebra.IsPushout Γ(S, US) Γ(X, UX) Γ(T, UT)
      Γ(Y, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :=
    CommRingCat.isPushout_iff_isPushout.mp
      (isPushout_appLE_pullback_piece H hUST hUSX hUS hUT hUX)
  haveI hpo₂ : Algebra.IsPushout Γ(S, US) Γ(T, UT) Γ(X, UX)
      Γ(Y, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) := hpo₁.symm
  -- module structures on the sections
  letI : Module Γ(S, US) Γ(F, UX) := Module.compHom _ (iX.appLE US UX hUSX).hom
  haveI : IsScalarTower Γ(S, US) Γ(X, UX) Γ(F, UX) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module Γ(X, UX) Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :=
    Module.compHom _ (g.appLE UX (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_left).hom
  letI : Module Γ(T, UT) Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :=
    Module.compHom _ (iY.appLE UT (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_right).hom
  haveI : IsScalarTower Γ(X, UX) Γ(Y, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
      Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower Γ(T, UT) Γ(Y, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
      Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI hMflat : Module.Flat Γ(S, US) Γ(F, UX) := hflat
  -- the base-change section formula
  obtain ⟨⟨eqv, heqv⟩⟩ :=
    pullback_app_isoTensor_baseMap_sectionLinearEquiv g F hUY hUX inf_le_left
  have hbc : IsBaseChange Γ(Y, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
      (pullback_app_isoTensor_baseMap g F (V := UX) inf_le_left) :=
    IsBaseChange.of_equiv eqv heqv
  exact Module.Flat.of_isPushout Γ(S, US) Γ(T, UT) Γ(X, UX)
    Γ(Y, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) Γ(F, UX) hbc

set_option maxSynthPendingDepth 3 in
/-- **Per-piece finiteness transfer.**  If the `F`-sections on the affine
`UX ⊆ X` are finite over `Γ(X, UX)`, the pulled-back sections on the piece
are finite over the piece's own section ring (base change of a finite module
is finite). -/
theorem finite_section_pullback_piece (F : X.Modules) [F.IsQuasicoherent]
    (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT) (hUX : IsAffineOpen UX)
    (hfin : Module.Finite Γ(X, UX) Γ(F, UX)) :
    Module.Finite Γ(Y, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
      Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) := by
  have hUY : IsAffineOpen (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :=
    isAffineOpen_pullback_piece H hUST hUSX hUS hUT hUX
  letI : Algebra Γ(X, UX) Γ(Y, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :=
    (g.appLE UX (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_left).hom.toAlgebra
  letI : Module Γ(X, UX) Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :=
    Module.compHom _ (g.appLE UX (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_left).hom
  obtain ⟨⟨eqv, -⟩⟩ :=
    pullback_app_isoTensor_baseMap_sectionLinearEquiv g F hUY hUX inf_le_left
  haveI : Module.Finite Γ(Y, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
      (TensorProduct Γ(X, UX) Γ(Y, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) Γ(F, UX)) :=
    Module.Finite.base_change _ _ _
  exact Module.Finite.equiv eqv

end PullbackPiece

/-! ## §5. Flatness over the base is affine-local (cover ⟹ all pairs)

If a quasi-coherent module `G` on `Y ⟶ T` has flat sections on one family of
affine chart pairs `(Uc j ⊆ T, Wc j ⊆ q⁻¹Uc j)` whose fibre-side charts cover
`Y`, then *every* affine pair `(U, W)` has flat sections — Stacks 00HT-style
affine-locality, in the two-layer basic-open reduction style of
`flat_section_pair`: cover `W` by opens simultaneously basic in `W` and in a
chart, lying above base basic opens common to `U` and the chart's base
`Uc j`; per piece, restrict the chart flatness fibre-side (mixed-base
stability `Module.Flat.of_isLocalizedModule_algebra`), then exchange the base
ring twice (`Module.flat_iff_of_isLocalization`); glue with
`Module.flat_of_isLocalized_span`. -/

section FlatAffineLocal

set_option maxHeartbeats 1600000 in
-- Heartbeat headroom: per-piece instance provisioning under binders, as in
-- `flat_section_pair`.
/-- **Flatness over the base is affine-local.**  Chart flatness on an affine
cover implies flatness on every affine pair. -/
theorem flat_section_of_affine_cover {T Y : Scheme.{u}} (q : Y ⟶ T) (G : Y.Modules)
    [G.IsQuasicoherent] {ι : Type u}
    (Wc : ι → Y.Opens) (hWc : ∀ j, IsAffineOpen (Wc j))
    (Uc : ι → T.Opens) (hUc : ∀ j, IsAffineOpen (Uc j))
    (eWc : ∀ j, Wc j ≤ q ⁻¹ᵁ Uc j)
    (hcover : ∀ y : Y, ∃ j, y ∈ Wc j)
    (hflat : ∀ j,
      letI : Module Γ(T, Uc j) Γ(G, Wc j) :=
        Module.compHom _ (q.appLE (Uc j) (Wc j) (eWc j)).hom
      Module.Flat Γ(T, Uc j) Γ(G, Wc j))
    {U : T.Opens} (hU : IsAffineOpen U) {W : Y.Opens} (hW : IsAffineOpen W)
    (e : W ≤ q ⁻¹ᵁ U) :
    letI : Module Γ(T, U) Γ(G, W) := Module.compHom _ (q.appLE U W e).hom
    Module.Flat Γ(T, U) Γ(G, W) := by
  letI : Module Γ(T, U) Γ(G, W) := Module.compHom _ (q.appLE U W e).hom
  -- per-point choice of a simultaneous basic open
  have Hx : ∀ x : ↥W, ∃ (b : Γ(Y, W)) (j : ι) (a : Γ(T, U)) (a' : Γ(T, Uc j))
      (c : Γ(Y, Wc j)),
      Y.basicOpen b = Y.basicOpen c ∧ (x : Y) ∈ Y.basicOpen b ∧
      T.basicOpen a = T.basicOpen a' ∧
      Y.basicOpen b ≤ q ⁻¹ᵁ (T.basicOpen a) := by
    intro x
    obtain ⟨j, hxj⟩ := hcover x.1
    have hxU : q.base x.1 ∈ U := e x.2
    have hxUj : q.base x.1 ∈ Uc j := eWc j hxj
    obtain ⟨a, a', haa', hqa⟩ :=
      AlgebraicGeometry.exists_basicOpen_le_affine_inter hU (hUc j) (q.base x.1)
        ⟨hxU, hxUj⟩
    have hxT : x.1 ∈ (W ⊓ (q ⁻¹ᵁ T.basicOpen a ⊓ Wc j) : Y.Opens) :=
      ⟨x.2, ⟨hqa, hxj⟩⟩
    obtain ⟨b₁, hb₁le, hxb₁⟩ := hW.exists_basicOpen_le
      (⟨x.1, hxT⟩ : ↥(W ⊓ (q ⁻¹ᵁ T.basicOpen a ⊓ Wc j) : Y.Opens)) x.2
    obtain ⟨f₁, c, hfc, hxf₁⟩ := AlgebraicGeometry.exists_basicOpen_le_affine_inter
      (hW.basicOpen b₁) (hWc j) x.1 ⟨hxb₁, hxj⟩
    obtain ⟨b, hb⟩ := hW.basicOpen_basicOpen_is_basicOpen b₁ f₁
    exact ⟨b, j, a, a', c, hb.trans hfc, hb.symm ▸ hxf₁, haa',
      hb.symm ▸ ((Y.basicOpen_le f₁).trans
        (hb₁le.trans (inf_le_right.trans inf_le_left)))⟩
  choose bb jj aa aa' cc hbc hxb haa' hba using Hx
  -- the covering family spans `Γ(Y, W)`
  have hspan : Ideal.span (Set.range bb) = ⊤ := by
    rw [← hW.iSup_basicOpen_eq_self_iff]
    apply le_antisymm
    · exact iSup_le fun r => Y.basicOpen_le _
    · intro y hy
      exact TopologicalSpace.Opens.mem_iSup.mpr
        ⟨⟨bb ⟨y, hy⟩, Set.mem_range_self _⟩, hxb ⟨y, hy⟩⟩
  -- instance packs for the span lemma
  letI : Algebra Γ(T, U) Γ(Y, W) := (q.appLE U W e).hom.toAlgebra
  haveI : IsScalarTower Γ(T, U) Γ(Y, W) Γ(G, W) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI instBpiece : ∀ r : Set.range bb, Module Γ(Y, W) Γ(G, Y.basicOpen r.1) :=
    fun r => Module.compHom _ (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen r.1))
  haveI instTowerB : ∀ r : Set.range bb,
      IsScalarTower Γ(Y, W) Γ(Y, Y.basicOpen r.1) Γ(G, Y.basicOpen r.1) :=
    fun r => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI instLoc : ∀ r : Set.range bb, IsLocalizedModule (Submonoid.powers r.1)
      (Scheme.Modules.restrictBasicOpenₗ G r.1) := fun r =>
    Scheme.Modules.isLocalizedModule_basicOpen_of_isCompact G hW.isCompact
      hW.isQuasiSeparated r.1
  letI instRpiece : ∀ r : Set.range bb, Module Γ(T, U) Γ(G, Y.basicOpen r.1) :=
    fun r =>
      Module.compHom _ (q.appLE U (Y.basicOpen r.1) ((Y.basicOpen_le r.1).trans e)).hom
  haveI instTowerR : ∀ r : Set.range bb,
      IsScalarTower Γ(T, U) Γ(Y, W) Γ(G, Y.basicOpen r.1) := fun r =>
    IsScalarTower.of_algebraMap_smul fun u n => by
      change (Y.presheaf.map (homOfLE (Y.basicOpen_le r.1)).op).hom
          ((q.appLE U W e).hom u) • n
        = (q.appLE U (Y.basicOpen r.1) ((Y.basicOpen_le r.1).trans e)).hom u • n
      rw [appLE_res_apply q e (Y.basicOpen_le r.1) u]
  -- assemble by the span criterion; the pieces are handled below
  refine Module.flat_of_isLocalized_span (R := Γ(T, U)) Γ(Y, W) Γ(G, W)
    (Set.range bb) hspan (fun r => Γ(G, Y.basicOpen r.1))
    (fun r => Scheme.Modules.restrictBasicOpenₗ G r.1) ?_
  -- per-piece flatness
  intro r
  obtain ⟨x, hx⟩ := r.2
  have hbar : Y.basicOpen r.1 ≤ q ⁻¹ᵁ (T.basicOpen (aa x)) := hx ▸ hba x
  have hbcr : Y.basicOpen r.1 = Y.basicOpen (cc x) := hx ▸ hbc x
  have hcWj : Y.basicOpen (cc x) ≤ Wc (jj x) := Y.basicOpen_le (cc x)
  have hcUj : Y.basicOpen (cc x) ≤ q ⁻¹ᵁ Uc (jj x) :=
    fun y hy => eWc (jj x) (hcWj hy)
  have hrUj : Y.basicOpen r.1 ≤ q ⁻¹ᵁ Uc (jj x) := hbcr ▸ hcUj
  have haU : T.basicOpen (aa x) ≤ U := T.basicOpen_le (aa x)
  have haUj : T.basicOpen (aa x) ≤ Uc (jj x) :=
    (haa' x).trans_le (T.basicOpen_le (aa' x))
  -- (α) chart flatness restricts to the chart-basic open, mixed-base
  have hA : (letI : Module Γ(T, Uc (jj x)) Γ(G, Y.basicOpen (cc x)) :=
        Module.compHom _ (q.appLE (Uc (jj x)) (Y.basicOpen (cc x)) hcUj).hom
      Module.Flat Γ(T, Uc (jj x)) Γ(G, Y.basicOpen (cc x))) := by
    letI : Module Γ(T, Uc (jj x)) Γ(G, Wc (jj x)) :=
      Module.compHom _ (q.appLE (Uc (jj x)) (Wc (jj x)) (eWc (jj x))).hom
    letI : Algebra Γ(T, Uc (jj x)) Γ(Y, Wc (jj x)) :=
      (q.appLE (Uc (jj x)) (Wc (jj x)) (eWc (jj x))).hom.toAlgebra
    haveI : IsScalarTower Γ(T, Uc (jj x)) Γ(Y, Wc (jj x)) Γ(G, Wc (jj x)) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    letI : Module Γ(Y, Wc (jj x)) Γ(G, Y.basicOpen (cc x)) :=
      Module.compHom _ (algebraMap Γ(Y, Wc (jj x)) Γ(Y, Y.basicOpen (cc x)))
    haveI : IsScalarTower Γ(Y, Wc (jj x)) Γ(Y, Y.basicOpen (cc x))
        Γ(G, Y.basicOpen (cc x)) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    letI : Module Γ(T, Uc (jj x)) Γ(G, Y.basicOpen (cc x)) :=
      Module.compHom _ (q.appLE (Uc (jj x)) (Y.basicOpen (cc x)) hcUj).hom
    haveI : IsScalarTower Γ(T, Uc (jj x)) Γ(Y, Wc (jj x))
        Γ(G, Y.basicOpen (cc x)) :=
      IsScalarTower.of_algebraMap_smul fun u n => by
        change (Y.presheaf.map (homOfLE hcWj).op).hom
            ((q.appLE (Uc (jj x)) (Wc (jj x)) (eWc (jj x))).hom u) • n
          = (q.appLE (Uc (jj x)) (Y.basicOpen (cc x)) hcUj).hom u • n
        rw [appLE_res_apply q (eWc (jj x)) hcWj u]
    haveI hlocB : IsLocalizedModule (Submonoid.powers (cc x))
        (Scheme.Modules.restrictBasicOpenₗ G (cc x)) :=
      Scheme.Modules.isLocalizedModule_basicOpen_of_isCompact G
        (hWc (jj x)).isCompact (hWc (jj x)).isQuasiSeparated (cc x)
    haveI : Module.Flat Γ(T, Uc (jj x)) Γ(G, Wc (jj x)) := hflat (jj x)
    exact Module.Flat.of_isLocalizedModule_algebra (Submonoid.powers (cc x))
      (Scheme.Modules.restrictBasicOpenₗ G (cc x))
  -- (β) transport along `D(r) = D(c)`
  have hA' : (letI : Module Γ(T, Uc (jj x)) Γ(G, Y.basicOpen r.1) :=
        Module.compHom _ (q.appLE (Uc (jj x)) (Y.basicOpen r.1) hrUj).hom
      Module.Flat Γ(T, Uc (jj x)) Γ(G, Y.basicOpen r.1)) :=
    flat_sections_congr q G hbcr.symm hcUj hrUj hA
  -- (γ) exchange the base ring twice: `Uc (jj x) → D(aa x) → U`
  letI mA : Module Γ(T, T.basicOpen (aa x)) Γ(G, Y.basicOpen r.1) :=
    Module.compHom _ (q.appLE (T.basicOpen (aa x)) (Y.basicOpen r.1) hbar).hom
  letI mA0 : Module Γ(T, Uc (jj x)) Γ(G, Y.basicOpen r.1) :=
    Module.compHom _ (q.appLE (Uc (jj x)) (Y.basicOpen r.1) hrUj).hom
  haveI hloc1 : IsLocalization.Away (aa x) Γ(T, T.basicOpen (aa x)) :=
    hU.isLocalization_basicOpen (aa x)
  haveI tow1 : IsScalarTower Γ(T, U) Γ(T, T.basicOpen (aa x))
      Γ(G, Y.basicOpen r.1) :=
    IsScalarTower.of_algebraMap_smul fun u n => by
      change (q.appLE (T.basicOpen (aa x)) (Y.basicOpen r.1) hbar).hom
          ((T.presheaf.map (homOfLE haU).op).hom u) • n
        = (q.appLE U (Y.basicOpen r.1) ((Y.basicOpen_le r.1).trans e)).hom u • n
      rw [appLE_base_res_apply q haU hbar ((Y.basicOpen_le r.1).trans e) u]
  letI algA : Algebra Γ(T, Uc (jj x)) Γ(T, T.basicOpen (aa x)) :=
    ((T.presheaf.map (homOfLE haUj).op).hom).toAlgebra
  haveI hloc2 : IsLocalization.Away (aa' x) Γ(T, T.basicOpen (aa x)) :=
    (hUc (jj x)).isLocalization_of_eq_basicOpen (aa' x) (homOfLE haUj) (haa' x)
  haveI tow2 : IsScalarTower Γ(T, Uc (jj x)) Γ(T, T.basicOpen (aa x))
      Γ(G, Y.basicOpen r.1) :=
    IsScalarTower.of_algebraMap_smul fun u n => by
      change (q.appLE (T.basicOpen (aa x)) (Y.basicOpen r.1) hbar).hom
          ((T.presheaf.map (homOfLE haUj).op).hom u) • n
        = (q.appLE (Uc (jj x)) (Y.basicOpen r.1) hrUj).hom u • n
      rw [appLE_base_res_apply q haUj hbar hrUj u]
  have h2 : Module.Flat Γ(T, T.basicOpen (aa x)) Γ(G, Y.basicOpen r.1) :=
    (Module.flat_iff_of_isLocalization (R := Γ(T, Uc (jj x)))
      Γ(T, T.basicOpen (aa x)) (Submonoid.powers (aa' x))
      Γ(G, Y.basicOpen r.1)).mpr hA'
  exact (Module.flat_iff_of_isLocalization (R := Γ(T, U))
    Γ(T, T.basicOpen (aa x)) (Submonoid.powers (aa x))
    Γ(G, Y.basicOpen r.1)).mp h2

end FlatAffineLocal

/-! ## §6. Reduced closed subschemes and flatness transport

Support facts for the Noetherian induction: the vanishing-ideal subscheme of
a closed subset is reduced (its ideal sheaf is radical, so the affine cover
pieces `Spec (Γ(S,U)/I(U))` are reduced); if the closed subset is
irreducible, the subscheme is integral.  `coherentSheafFlat_of_iso`
transports the coherent-sheaf-flatness predicate along an isomorphism of
module sheaves. -/

section ReducedSubscheme

variable {S : Scheme.{u}}

lemma support_vanishingIdeal (Z : TopologicalSpace.Closeds S) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := by
  ext1
  exact Scheme.IdealSheafData.coe_support_vanishingIdeal (X := S) Z

lemma radical_vanishingIdeal (Z : TopologicalSpace.Closeds S) :
    (Scheme.IdealSheafData.vanishingIdeal Z).radical =
      Scheme.IdealSheafData.vanishingIdeal Z := by
  rw [← Scheme.IdealSheafData.vanishingIdeal_support, support_vanishingIdeal]

lemma isRadical_vanishingIdeal_ideal (Z : TopologicalSpace.Closeds S)
    (U : S.affineOpens) :
    ((Scheme.IdealSheafData.vanishingIdeal Z).ideal U).IsRadical := by
  have h := congrArg (fun I => Scheme.IdealSheafData.ideal I U)
    (radical_vanishingIdeal Z)
  simp only [Scheme.IdealSheafData.radical_ideal] at h
  rw [← h]
  exact Ideal.radical_isRadical _

instance isReduced_vanishingIdeal_subscheme (Z : TopologicalSpace.Closeds S) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  haveI : ∀ U, IsReduced
      ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.X U) := by
    intro U
    haveI : _root_.IsReduced
        (Γ(S, U.1) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp
        (isRadical_vanishingIdeal_ideal Z U)
    exact inferInstanceAs (IsReduced (Spec (.of
      (Γ(S, U.1) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U))))
  exact IsReduced.of_openCover
    (𝒰 := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover)

lemma isIntegral_vanishingIdeal_subscheme (Z : TopologicalSpace.Closeds S)
    (hZ : IsIrreducible (Z : Set S)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  haveI : IrreducibleSpace ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    have h : IsIrreducible
        (((Scheme.IdealSheafData.vanishingIdeal Z).support : Set S)) := by
      rw [show (((Scheme.IdealSheafData.vanishingIdeal Z).support : Set S)) = (Z : Set S) by
        rw [support_vanishingIdeal]]
      exact hZ
    exact Subtype.irreducibleSpace h
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Transport of `CoherentSheafFlat` along an isomorphism of module sheaves. -/
lemma coherentSheafFlat_of_iso {T' Y' : Scheme.{u}} (q : Y' ⟶ T') {G G' : Y'.Modules}
    (e : G ≅ G') (h : Scheme.CoherentSheafFlat q G) : Scheme.CoherentSheafFlat q G' := by
  intro U hU V hV eV
  letI : Module Γ(T', U) Γ(G', V) := Module.compHom _ (q.appLE U V eV).hom
  letI : Module Γ(T', U) Γ(G, V) := Module.compHom _ (q.appLE U V eV).hom
  haveI hG : Module.Flat Γ(T', U) Γ(G, V) := h hU hV eV
  refine Module.Flat.of_linearEquiv (M := Γ(G, V)) (e := ?_)
  exact
    { toFun := fun x => (Scheme.Modules.Hom.app e.inv V).hom x
      invFun := fun x => (Scheme.Modules.Hom.app e.hom V).hom x
      left_inv := fun x => by
        have h1 := congrArg
          (fun (φ : G' ⟶ G') => (Scheme.Modules.Hom.app φ V).hom x) e.inv_hom_id
        simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
          AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
          AddCommGrpCat.hom_id, AddMonoidHom.id_apply] at h1
        exact h1
      right_inv := fun x => by
        have h1 := congrArg
          (fun (φ : G ⟶ G) => (Scheme.Modules.Hom.app φ V).hom x) e.hom_inv_id
        simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
          AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
          AddCommGrpCat.hom_id, AddMonoidHom.id_apply] at h1
        exact h1
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => Scheme.Modules.Hom.app_smul e.inv
        ((q.appLE U V eV).hom r) x }

end ReducedSubscheme

/-! ## §7. The flat stratum over one irreducible component

For an irreducible closed subset `Zc ⊆ S` with reduced subscheme `T`, generic
flatness on the base-changed family `X ×_S T ⟶ T` produces a non-empty open
`Ω ⊆ T` such that for *every* open `St ≤ Ω` the family restricted to the
locally closed stratum `St ⟶ S` has flat pullback: chart flatness on the
piece cover of `X ×_S St` comes from the generic-flatness output through the
pasted pullback square (`IsPullback.of_bot`) and the per-piece transfer of
§4, `flat_section_of_affine_cover` (§5) globalizes, and
`coherentSheafFlat_of_iso` rewrites the pulled-back sheaf through
`pullbackComp`. -/

section FlatStratum

variable {S X : Scheme.{u}} [IsNoetherian S] (π : X ⟶ S) [IsProper π]
variable (F : X.Modules) [F.IsFinitePresentation]
variable (Zc : TopologicalSpace.Closeds S)

set_option quotPrecheck false in
local notation "Tsch" => (Scheme.IdealSheafData.vanishingIdeal Zc).subscheme

set_option quotPrecheck false in
local notation "kT" => (Scheme.IdealSheafData.vanishingIdeal Zc).subschemeι

/-- **Flat stratum over an irreducible component** [Nitsure §4, induction
step core].  For `Zc ⊆ S` irreducible closed with reduced subscheme `T`,
there is a non-empty open `Ω ⊆ T` such that every open substratum
`St ≤ Ω`, viewed as a locally closed subscheme of `S`, has flat pullback
family. -/
theorem flat_stratum_of_irreducible (hirr : IsIrreducible (Zc : Set S)) :
    ∃ Ω : (Tsch).Opens, (Ω : Set Tsch).Nonempty ∧
      ∀ St : (Tsch).Opens, St ≤ Ω →
        Scheme.CoherentSheafFlat (pullback.snd π (St.ι ≫ kT))
          ((Scheme.Modules.pullback (pullback.fst π (St.ι ≫ kT))).obj F) := by
  classical
  haveI : IsIntegral Tsch := isIntegral_vanishingIdeal_subscheme Zc hirr
  haveI : IsLocallyNoetherian Tsch := LocallyOfFiniteType.isLocallyNoetherian kT
  haveI hFqc : F.IsQuasicoherent := inferInstance
  haveI hFTqc : ((Scheme.Modules.pullback (pullback.fst π kT)).obj F).IsQuasicoherent :=
    pullback_isQuasicoherent_hom _ F hFqc
  -- chart supply for the pulled-back module on `X ×_S T`
  have hfinT : ∀ (x : ↑(pullback π kT)) (O : (pullback π kT).Opens), x ∈ O →
      ∃ V : (pullback π kT).Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ O ∧
        Module.Finite Γ(pullback π kT, V)
          Γ((Scheme.Modules.pullback (pullback.fst π kT)).obj F, V) := by
    intro x O hxO
    obtain ⟨_, ⟨US, hUS, rfl⟩, hs₀, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ ((kT) ((pullback.snd π kT) x))) isOpen_univ
    have hxt : (pullback.snd π kT) x ∈ kT ⁻¹ᵁ US := hs₀
    obtain ⟨_, ⟨UT, hUT, rfl⟩, hxUT, hUTle⟩ :=
      (Tsch).isBasis_affineOpens.exists_subset_of_mem_open hxt (kT ⁻¹ᵁ US).2
    have hxw : (pullback.fst π kT) x ∈ π ⁻¹ᵁ US := by
      have h1 : π ((pullback.fst π kT) x) = (kT) ((pullback.snd π kT) x) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      change π ((pullback.fst π kT) x) ∈ US
      rw [h1]
      exact hs₀
    obtain ⟨WX, hWX, hxWX, hWXle, hWfin⟩ :=
      Scheme.Modules.exists_affine_finite_sections_nhds F
        ((pullback.fst π kT).base x) (π ⁻¹ᵁ US) hxw
    have hP : IsAffineOpen
        ((pullback.fst π kT) ⁻¹ᵁ WX ⊓ (pullback.snd π kT) ⁻¹ᵁ UT) :=
      isAffineOpen_pullback_piece (IsPullback.of_hasPullback π kT) hUTle hWXle
        hUS hUT hWX
    have hxP : x ∈ (pullback.fst π kT) ⁻¹ᵁ WX ⊓ (pullback.snd π kT) ⁻¹ᵁ UT :=
      ⟨hxWX, hxUT⟩
    have hPfin : Module.Finite
        Γ(pullback π kT, (pullback.fst π kT) ⁻¹ᵁ WX ⊓ (pullback.snd π kT) ⁻¹ᵁ UT)
        Γ((Scheme.Modules.pullback (pullback.fst π kT)).obj F,
          (pullback.fst π kT) ⁻¹ᵁ WX ⊓ (pullback.snd π kT) ⁻¹ᵁ UT) :=
      finite_section_pullback_piece (IsPullback.of_hasPullback π kT) hUTle hWXle
        F hUS hUT hWX hWfin
    obtain ⟨β, hβle, hxβ⟩ := hP.exists_basicOpen_le
      (⟨x, ⟨hxP, hxO⟩⟩ : ↥(((pullback.fst π kT) ⁻¹ᵁ WX ⊓ (pullback.snd π kT) ⁻¹ᵁ UT) ⊓ O))
      hxP
    refine ⟨(pullback π kT).basicOpen β, hP.basicOpen β, hxβ,
      hβle.trans inf_le_right, ?_⟩
    -- localized finiteness on the basic open
    letI : Module
        Γ(pullback π kT, (pullback.fst π kT) ⁻¹ᵁ WX ⊓ (pullback.snd π kT) ⁻¹ᵁ UT)
        Γ((Scheme.Modules.pullback (pullback.fst π kT)).obj F,
          (pullback π kT).basicOpen β) :=
      Module.compHom _ (algebraMap
        Γ(pullback π kT, (pullback.fst π kT) ⁻¹ᵁ WX ⊓ (pullback.snd π kT) ⁻¹ᵁ UT)
        Γ(pullback π kT, (pullback π kT).basicOpen β))
    haveI : IsScalarTower
        Γ(pullback π kT, (pullback.fst π kT) ⁻¹ᵁ WX ⊓ (pullback.snd π kT) ⁻¹ᵁ UT)
        Γ(pullback π kT, (pullback π kT).basicOpen β)
        Γ((Scheme.Modules.pullback (pullback.fst π kT)).obj F,
          (pullback π kT).basicOpen β) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    haveI hloc : IsLocalizedModule (Submonoid.powers β)
        (Scheme.Modules.restrictBasicOpenₗ
          ((Scheme.Modules.pullback (pullback.fst π kT)).obj F) β) :=
      Scheme.Modules.isLocalizedModule_basicOpen_of_isCompact _ hP.isCompact
        hP.isQuasiSeparated β
    haveI hlocR : IsLocalization.Away β
        Γ(pullback π kT, (pullback π kT).basicOpen β) :=
      hP.isLocalization_basicOpen β
    exact Module.Finite.of_isLocalizedModule (Submonoid.powers β)
      (Rₚ := Γ(pullback π kT, (pullback π kT).basicOpen β))
      (Scheme.Modules.restrictBasicOpenₗ
        ((Scheme.Modules.pullback (pullback.fst π kT)).obj F) β)
  -- generic flatness on the reduced-component family
  obtain ⟨Ω, hΩne, hΩflat⟩ := genericFlatness_of_finite_sections
    (pullback.snd π kT) ((Scheme.Modules.pullback (pullback.fst π kT)).obj F) hfinT
  refine ⟨Ω, hΩne, ?_⟩
  intro St hStΩ
  -- the comparison morphism into the component family
  have hcondSt : pullback.fst π (St.ι ≫ kT) ≫ π =
      (pullback.snd π (St.ι ≫ kT) ≫ St.ι) ≫ kT := by
    rw [pullback.condition, Category.assoc]
  -- κ : X ×_S St ⟶ X ×_S T
  -- (over `𝟙 X` and `St.ι`)
  have hκfst : pullback.lift (pullback.fst π (St.ι ≫ kT))
      (pullback.snd π (St.ι ≫ kT) ≫ St.ι) hcondSt ≫ pullback.fst π kT =
      pullback.fst π (St.ι ≫ kT) := pullback.lift_fst _ _ _
  have hκsnd : pullback.lift (pullback.fst π (St.ι ≫ kT))
      (pullback.snd π (St.ι ≫ kT) ≫ St.ι) hcondSt ≫ pullback.snd π kT =
      pullback.snd π (St.ι ≫ kT) ≫ St.ι := pullback.lift_snd _ _ _
  -- the left square of the vertical pasting is a pullback
  have Hbig : IsPullback (pullback.snd π (St.ι ≫ kT))
      (pullback.lift (pullback.fst π (St.ι ≫ kT))
        (pullback.snd π (St.ι ≫ kT) ≫ St.ι) hcondSt ≫ pullback.fst π kT)
      (St.ι ≫ kT) π := by
    rw [hκfst]
    exact (IsPullback.of_hasPullback π (St.ι ≫ kT)).flip
  have Hleft : IsPullback
      (pullback.lift (pullback.fst π (St.ι ≫ kT))
        (pullback.snd π (St.ι ≫ kT) ≫ St.ι) hcondSt)
      (pullback.snd π (St.ι ≫ kT)) (pullback.snd π kT) St.ι :=
    (IsPullback.of_bot Hbig hκsnd.symm
      ((IsPullback.of_hasPullback π kT).flip)).flip
  -- per-point chart data on the stratum family
  have Hch : ∀ y : ↑(pullback π (St.ι ≫ kT)),
      ∃ (WX : X.Opens) (U₁ : (Tsch).Opens) (US : S.Opens),
        IsAffineOpen WX ∧ IsAffineOpen U₁ ∧ IsAffineOpen US ∧ U₁ ≤ St ∧ U₁ ≤ Ω ∧
        WX ≤ π ⁻¹ᵁ US ∧ U₁ ≤ kT ⁻¹ᵁ US ∧
        y ∈ (pullback.fst π (St.ι ≫ kT)) ⁻¹ᵁ WX ∧
        y ∈ (pullback.snd π (St.ι ≫ kT)) ⁻¹ᵁ (St.ι ⁻¹ᵁ U₁) := by
    intro y
    obtain ⟨_, ⟨US, hUS, rfl⟩, hs₀, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ ((St.ι ≫ kT) ((pullback.snd π (St.ι ≫ kT)) y)))
        isOpen_univ
    have hmemSt : St.ι ((pullback.snd π (St.ι ≫ kT)) y) ∈ St := by
      have hmr : St.ι ((pullback.snd π (St.ι ≫ kT)) y) ∈ Set.range St.ι.base :=
        ⟨(pullback.snd π (St.ι ≫ kT)) y, rfl⟩
      rwa [Scheme.Opens.range_ι] at hmr
    have hxt : (St.ι ((pullback.snd π (St.ι ≫ kT)) y)) ∈
        (St ⊓ Ω ⊓ kT ⁻¹ᵁ US : (Tsch).Opens) := by
      refine ⟨⟨hmemSt, hStΩ hmemSt⟩, ?_⟩
      change (kT) (St.ι ((pullback.snd π (St.ι ≫ kT)) y)) ∈ US
      rwa [← Scheme.Hom.comp_apply] at hs₀
    obtain ⟨_, ⟨U₁, hU₁, rfl⟩, hxU₁, hU₁le⟩ :=
      (Tsch).isBasis_affineOpens.exists_subset_of_mem_open hxt
        (St ⊓ Ω ⊓ kT ⁻¹ᵁ US).2
    have hxw : (pullback.fst π (St.ι ≫ kT)) y ∈ π ⁻¹ᵁ US := by
      have h1 : π ((pullback.fst π (St.ι ≫ kT)) y) =
          (St.ι ≫ kT) ((pullback.snd π (St.ι ≫ kT)) y) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      change π ((pullback.fst π (St.ι ≫ kT)) y) ∈ US
      rw [h1]
      exact hs₀
    obtain ⟨_, ⟨WX, hWX, rfl⟩, hxWX, hWXle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxw (π ⁻¹ᵁ US).2
    exact ⟨WX, U₁, US, hWX, hU₁, hUS, (hU₁le.trans inf_le_left).trans inf_le_left,
      (hU₁le.trans inf_le_left).trans inf_le_right, hWXle, hU₁le.trans inf_le_right,
      hxWX, hxU₁⟩
  choose WXc U₁c USc hWXc hU₁c hUSc hU₁St hU₁Ω hWXle hU₁le hyWX hyU₁ using Hch
  -- chart flatness for the `κ`-pulled-back module, fed by generic flatness
  -- through the pasted square
  have hchart : ∀ y : ↑(pullback π (St.ι ≫ kT)),
      letI : Module Γ(St, St.ι ⁻¹ᵁ U₁c y)
          Γ((Scheme.Modules.pullback (pullback.lift (pullback.fst π (St.ι ≫ kT))
              (pullback.snd π (St.ι ≫ kT) ≫ St.ι) hcondSt)).obj
            ((Scheme.Modules.pullback (pullback.fst π kT)).obj F),
            (pullback.fst π (St.ι ≫ kT)) ⁻¹ᵁ WXc y ⊓
              (pullback.snd π (St.ι ≫ kT)) ⁻¹ᵁ (St.ι ⁻¹ᵁ U₁c y)) :=
        Module.compHom _ ((pullback.snd π (St.ι ≫ kT)).appLE (St.ι ⁻¹ᵁ U₁c y)
          ((pullback.fst π (St.ι ≫ kT)) ⁻¹ᵁ WXc y ⊓
            (pullback.snd π (St.ι ≫ kT)) ⁻¹ᵁ (St.ι ⁻¹ᵁ U₁c y)) inf_le_right).hom
      Module.Flat Γ(St, St.ι ⁻¹ᵁ U₁c y)
        Γ((Scheme.Modules.pullback (pullback.lift (pullback.fst π (St.ι ≫ kT))
            (pullback.snd π (St.ι ≫ kT) ≫ St.ι) hcondSt)).obj
          ((Scheme.Modules.pullback (pullback.fst π kT)).obj F),
          (pullback.fst π (St.ι ≫ kT)) ⁻¹ᵁ WXc y ⊓
            (pullback.snd π (St.ι ≫ kT)) ⁻¹ᵁ (St.ι ⁻¹ᵁ U₁c y)) := by
    intro y
    -- the piece of the component family
    have hP₁ : IsAffineOpen
        ((pullback.fst π kT) ⁻¹ᵁ WXc y ⊓ (pullback.snd π kT) ⁻¹ᵁ U₁c y) :=
      isAffineOpen_pullback_piece (IsPullback.of_hasPullback π kT) (hU₁le y)
        (hWXle y) (hUSc y) (hU₁c y) (hWXc y)
    -- generic flatness on that piece
    have hflat₁ :
        letI : Module Γ(Tsch, U₁c y)
            Γ((Scheme.Modules.pullback (pullback.fst π kT)).obj F,
              (pullback.fst π kT) ⁻¹ᵁ WXc y ⊓ (pullback.snd π kT) ⁻¹ᵁ U₁c y) :=
          Module.compHom _ ((pullback.snd π kT).appLE (U₁c y)
            ((pullback.fst π kT) ⁻¹ᵁ WXc y ⊓ (pullback.snd π kT) ⁻¹ᵁ U₁c y)
            inf_le_right).hom
        Module.Flat Γ(Tsch, U₁c y)
          Γ((Scheme.Modules.pullback (pullback.fst π kT)).obj F,
            (pullback.fst π kT) ⁻¹ᵁ WXc y ⊓ (pullback.snd π kT) ⁻¹ᵁ U₁c y) :=
      hΩflat (hU₁c y) (hU₁Ω y) hP₁ inf_le_right
    -- affinity of the stratum chart
    have hU₁' : IsAffineOpen (St.ι ⁻¹ᵁ U₁c y) :=
      IsAffineOpen.preimage_of_isOpenImmersion (hU₁c y) St.ι
        (by rw [Scheme.Opens.opensRange_ι]; exact hU₁St y)
    -- the per-piece transfer over the left square
    have htransfer :=
      flat_section_pullback_piece (H := Hleft) (hUST := le_rfl)
        (hUSX := inf_le_right)
        ((Scheme.Modules.pullback (pullback.fst π kT)).obj F)
        (hU₁c y) hU₁' hP₁ hflat₁
    -- identify the piece with the stratum chart open
    have hopeq : (pullback.lift (pullback.fst π (St.ι ≫ kT))
        (pullback.snd π (St.ι ≫ kT) ≫ St.ι) hcondSt) ⁻¹ᵁ
          ((pullback.fst π kT) ⁻¹ᵁ WXc y ⊓ (pullback.snd π kT) ⁻¹ᵁ U₁c y) ⊓
        (pullback.snd π (St.ι ≫ kT)) ⁻¹ᵁ (St.ι ⁻¹ᵁ U₁c y) =
        (pullback.fst π (St.ι ≫ kT)) ⁻¹ᵁ WXc y ⊓
          (pullback.snd π (St.ι ≫ kT)) ⁻¹ᵁ (St.ι ⁻¹ᵁ U₁c y) := by
      rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, hκfst,
        ← Scheme.Hom.comp_preimage, hκsnd, Scheme.Hom.comp_preimage]
      rw [inf_assoc, inf_idem]
    exact flat_sections_congr (pullback.snd π (St.ι ≫ kT)) _ hopeq
      (hopeq ▸ inf_le_right) inf_le_right htransfer
  -- globalize over the stratum: all affine pairs are flat for the
  -- `κ`-pulled-back module
  have hallκ : Scheme.CoherentSheafFlat (pullback.snd π (St.ι ≫ kT))
      ((Scheme.Modules.pullback (pullback.lift (pullback.fst π (St.ι ≫ kT))
          (pullback.snd π (St.ι ≫ kT) ≫ St.ι) hcondSt)).obj
        ((Scheme.Modules.pullback (pullback.fst π kT)).obj F)) := by
    intro U hU V hV eV
    haveI hκqc : ((Scheme.Modules.pullback (pullback.lift (pullback.fst π (St.ι ≫ kT))
        (pullback.snd π (St.ι ≫ kT) ≫ St.ι) hcondSt)).obj
          ((Scheme.Modules.pullback (pullback.fst π kT)).obj F)).IsQuasicoherent :=
      pullback_isQuasicoherent_hom _ _ hFTqc
    exact flat_section_of_affine_cover (pullback.snd π (St.ι ≫ kT)) _
      (fun y => (pullback.fst π (St.ι ≫ kT)) ⁻¹ᵁ WXc y ⊓
        (pullback.snd π (St.ι ≫ kT)) ⁻¹ᵁ (St.ι ⁻¹ᵁ U₁c y))
      (fun y => by
        have hP₁ : IsAffineOpen
            ((pullback.fst π kT) ⁻¹ᵁ WXc y ⊓ (pullback.snd π kT) ⁻¹ᵁ U₁c y) :=
          isAffineOpen_pullback_piece (IsPullback.of_hasPullback π kT) (hU₁le y)
            (hWXle y) (hUSc y) (hU₁c y) (hWXc y)
        have hU₁' : IsAffineOpen (St.ι ⁻¹ᵁ U₁c y) :=
          IsAffineOpen.preimage_of_isOpenImmersion (hU₁c y) St.ι
            (by rw [Scheme.Opens.opensRange_ι]; exact hU₁St y)
        have hopeq : (pullback.lift (pullback.fst π (St.ι ≫ kT))
            (pullback.snd π (St.ι ≫ kT) ≫ St.ι) hcondSt) ⁻¹ᵁ
              ((pullback.fst π kT) ⁻¹ᵁ WXc y ⊓ (pullback.snd π kT) ⁻¹ᵁ U₁c y) ⊓
            (pullback.snd π (St.ι ≫ kT)) ⁻¹ᵁ (St.ι ⁻¹ᵁ U₁c y) =
            (pullback.fst π (St.ι ≫ kT)) ⁻¹ᵁ WXc y ⊓
              (pullback.snd π (St.ι ≫ kT)) ⁻¹ᵁ (St.ι ⁻¹ᵁ U₁c y) := by
          rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, hκfst,
            ← Scheme.Hom.comp_preimage, hκsnd, Scheme.Hom.comp_preimage]
          rw [inf_assoc, inf_idem]
        rw [← hopeq]
        exact isAffineOpen_pullback_piece (H := Hleft) (hUST := le_rfl)
          (hUSX := inf_le_right) (hU₁c y) hU₁' hP₁)
      (fun y => St.ι ⁻¹ᵁ U₁c y)
      (fun y => IsAffineOpen.preimage_of_isOpenImmersion (hU₁c y) St.ι
        (by rw [Scheme.Opens.opensRange_ι]; exact hU₁St y))
      (fun y => inf_le_right)
      (fun y => ⟨y, ⟨hyWX y, hyU₁ y⟩⟩)
      hchart hU hV eV
  -- transport along `pullbackComp` to the stratum family's sheaf
  have esheaf : (Scheme.Modules.pullback (pullback.lift (pullback.fst π (St.ι ≫ kT))
        (pullback.snd π (St.ι ≫ kT) ≫ St.ι) hcondSt)).obj
      ((Scheme.Modules.pullback (pullback.fst π kT)).obj F) ≅
      (Scheme.Modules.pullback (pullback.fst π (St.ι ≫ kT))).obj F :=
    (Scheme.Modules.pullbackComp (pullback.lift (pullback.fst π (St.ι ≫ kT))
      (pullback.snd π (St.ι ≫ kT) ≫ St.ι) hcondSt) (pullback.fst π kT)).app F ≪≫
    (Scheme.Modules.pullbackCongr hκfst).app F
  intro U hU V hV eV
  exact coherentSheafFlat_of_iso (pullback.snd π (St.ι ≫ kT)) esheaf hallκ hU hV eV

end FlatStratum

/-! ## §7b. Transport of coherent-sheaf flatness along base isomorphisms

`CoherentSheafFlat` is insensitive to an isomorphism on the base leg: if a
module sheaf is flat for `q ≫ w` with `w` an isomorphism of schemes, it is
flat for `q`.  The section-level content is that flatness of a module
transports along a factorization of the acting ring map through a bijective
ring map (`Module.compHom` structures; the section module is unchanged). -/

section IsoTransport

/-- Flatness of a module transports along a factorization of the acting ring
map through a bijective ring map: if `ψ = φ ∘ ρ` with `ρ : R →+* R'`
bijective and `M` flat for the `R'`-action through `φ`, then `M` is flat for
the `R`-action through `ψ`.  (`R'` is a free `R`-module of rank one via `ρ`,
so this is `Module.Flat.trans` along the scalar tower `R → R' → M`.) -/
private theorem flat_of_ringHom_comp_bijective {R R' O M : Type v} [CommRing R]
    [CommRing R'] [CommRing O] [AddCommGroup M] [Module O M] (ρ : R →+* R')
    (hρ : Function.Bijective ρ) (φ : R' →+* O) (ψ : R →+* O)
    (hψ : ψ = φ.comp ρ)
    (h : letI : Module R' M := Module.compHom M φ; Module.Flat R' M) :
    letI : Module R M := Module.compHom M ψ; Module.Flat R M := by
  subst hψ
  letI : Module R' M := Module.compHom M φ
  letI : Module R M := Module.compHom M (φ.comp ρ)
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Flat R' M := h
  haveI : Module.Flat R R' := by
    have hcoe : ⇑(Algebra.linearMap R R') = ⇑ρ := by
      funext x
      simp [RingHom.algebraMap_toAlgebra]
    exact Module.Flat.of_linearEquiv
      ((LinearEquiv.ofBijective (Algebra.linearMap R R')
        (by rw [hcoe]; exact hρ)).symm)
  haveI : IsScalarTower R R' M :=
    ⟨fun r r' m => by
      change φ (ρ r * r') • m = φ (ρ r) • (φ r' • m)
      rw [map_mul, mul_smul]⟩
  exact Module.Flat.trans R R' M

/-- **Coherent-sheaf flatness absorbs an isomorphism on the base**: if `𝓖` is
flat for `q ≫ w` with `w` an isomorphism of schemes, then `𝓖` is flat for
`q`.  Applied below with `q = 𝟙 P` to convert flatness over an isomorphic
copy of `P` (e.g. `pullback.snd` of a pullback along an identity) into
flatness over `P` itself. -/
theorem coherentSheafFlat_of_comp_isIso {P W W' : Scheme.{u}} (q : P ⟶ W)
    (w : W ⟶ W') [IsIso w] (G : P.Modules)
    (h : Scheme.CoherentSheafFlat (q ≫ w) G) : Scheme.CoherentSheafFlat q G := by
  intro U hU V hV eV
  have hrange : U ≤ (inv w).opensRange := by
    intro x hx
    refine ⟨w.base x, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    simp
  have hU' : IsAffineOpen ((inv w) ⁻¹ᵁ U) :=
    hU.preimage_of_isOpenImmersion (inv w) hrange
  have heq : (q ≫ w) ⁻¹ᵁ ((inv w) ⁻¹ᵁ U) = q ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have eV' : V ≤ (q ≫ w) ⁻¹ᵁ ((inv w) ⁻¹ᵁ U) := eV.trans heq.ge
  have hflat := h hU' hV eV'
  have hfact : q.appLE U V eV =
      (inv w).appLE U ((inv w) ⁻¹ᵁ U) le_rfl ≫
        (q ≫ w).appLE ((inv w) ⁻¹ᵁ U) V eV' := by
    rw [Scheme.Hom.appLE_comp_appLE]
    have hmor : (q ≫ w) ≫ inv w = q := by
      rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    simp only [hmor]
  haveI : IsIso ((inv w).appLE U ((inv w) ⁻¹ᵁ U) le_rfl) := by
    rw [← Scheme.Hom.app_eq_appLE]
    infer_instance
  exact flat_of_ringHom_comp_bijective
    ((inv w).appLE U ((inv w) ⁻¹ᵁ U) le_rfl).hom
    (ConcreteCategory.bijective_of_isIso _)
    ((q ≫ w).appLE ((inv w) ⁻¹ᵁ U) V eV').hom (q.appLE U V eV).hom
    (by rw [hfact]; rfl) hflat

end IsoTransport

/-! ## §8. The flattening stratification

The geometric part of the flattening-stratification theorem (Nitsure §4
sub-lemmas, main theorem, universal property, curve specialisation) lives
here rather than in `FlatteningStratification.lean`, because the proof of
Lemma 6 (`flatLocusReduction`) consumes `genericFlatness`, which needs the
QuotScheme engine that `FlatteningStratification.lean` does not import. -/

/-- **Lemma 6 (Noetherian-induction reduction).** [Nitsure §4 general
case opening]

For `S` noetherian, `π : X ⟶ S` proper, and `𝓕` coherent on `X`, there
exist finitely many reduced locally-closed immersions `V_i ⟶ S` with
pairwise disjoint set-theoretic images covering `|S|`, such that the
pullback `𝓕|_{X ×_S V_i}` is flat over `V_i`.

Nitsure's proof: peel off non-empty open flat patches by
`genericFlatness` applied to each irreducible component (with its
reduced subscheme structure), induct on the closed complement
`S ∖ V` (which is again noetherian, hence the induction terminates by
Noetherianity).

The substantive content over the special case (Lemma 5) is that the
strata `V_i` are *reduced* and that `𝓕` becomes flat above them (not
merely that strata exist); the polynomial-indexed refinement of the
main theorem (`flatteningStratification`) requires further assembly
(`flatLocusAssembly`).

The hypothesis is `IsNoetherian S` (Nitsure's "noetherian"), not merely
`IsLocallyNoetherian S`.  With only local noetherianity the *finite*
family is impossible: on `S = ⊔_{n≥1} 𝔸ⁿ` give component `n` the coherent
sheaf `⊕_{k≤n} (i_{V_k})_* 𝓞_{V_k}` for a strictly nested flag
`V_1 ⊃ ⋯ ⊃ V_n`; a flat locally-closed stratum through the generic point
`η_k` of `V_k` cannot contain `η_{k'}` for `k' ≠ k` (near `η_{k'}` every
neighbourhood meets the dense lower level, so `T ∩ V_{k'}` is not open in
`T`, contradicting the clopen-support criterion for local freeness), so
component `n` needs at least `n + 1` strata and no finite family covers
all components.  The same hypothesis is required by every finite-strata
statement below (`flatLocusAssembly`, `flatteningStratification`,
`flatteningStratification_universal`, `.ofCurve`); the ℕ-indexed `n = 0`
special case (Lemma 5) is correct for locally noetherian `S` because the
fibre rank provides the global countable index.

The proof is by well-founded induction on the closed target
(`WellFoundedLT (Closeds S)` from noetherianity).  For non-empty `Z`,
each irreducible component (imaged in `S`, with reduced subscheme
structure from `vanishingIdeal`) receives a flat relatively open stratum
from `flat_stratum_of_irreducible`, shrunk to avoid the other components;
the union of these strata is relatively open and dense in `Z`, so its
closed complement is strictly smaller and the induction terminates. -/
theorem flatLocusReduction {S X : Scheme.{u}} [IsNoetherian S]
    (π : X ⟶ S) [IsProper π] (F : X.Modules) [F.IsFinitePresentation] :
    ∃ (I : Type u) (_ : Finite I) (V_ : I → Scheme.{u}) (ι : ∀ i, V_ i ⟶ S),
      (∀ i, IsImmersion (ι i)) ∧
      (∀ i j, i ≠ j → Disjoint (Set.range (ι i).base) (Set.range (ι j).base)) ∧
      (∀ s : S, ∃ i, s ∈ Set.range (ι i).base) ∧
      (∀ i, Scheme.CoherentSheafFlat (pullback.snd π (ι i))
        ((Scheme.Modules.pullback (pullback.fst π (ι i))).obj F)) := by
  classical
  suffices H : ∀ Z : TopologicalSpace.Closeds S,
      ∃ (I : Type u) (_ : Finite I) (V_ : I → Scheme.{u}) (ι : ∀ i, V_ i ⟶ S),
        (∀ i, IsImmersion (ι i)) ∧
        (∀ i j, i ≠ j → Disjoint (Set.range (ι i).base) (Set.range (ι j).base)) ∧
        (⋃ i, Set.range (ι i).base) = (Z : Set S) ∧
        (∀ i, Scheme.CoherentSheafFlat (pullback.snd π (ι i))
          ((Scheme.Modules.pullback (pullback.fst π (ι i))).obj F)) by
    obtain ⟨I, hI, V_, ι, h1, h2, h3, h4⟩ := H ⊤
    refine ⟨I, hI, V_, ι, h1, h2, fun s => ?_, h4⟩
    have hs : s ∈ (⋃ i, Set.range (ι i).base) := by
      rw [h3]; trivial
    exact Set.mem_iUnion.mp hs
  intro Z₀
  haveI : TopologicalSpace.NoetherianSpace S := inferInstance
  induction Z₀ using WellFoundedLT.induction with | ind Z IH => ?_
  by_cases hZ : (Z : Set S) = ∅
  · refine ⟨PEmpty.{u+1}, inferInstance, fun i => i.elim, fun i => i.elim,
      fun i => i.elim, fun i j _ => i.elim, ?_, fun i => i.elim⟩
    rw [hZ]
    exact Set.iUnion_of_empty _
  have hZne : (Z : Set S).Nonempty := Set.nonempty_iff_ne_empty.mpr hZ
  -- the finitely many irreducible components of `Z`, imaged in `S`
  haveI hNZ : TopologicalSpace.NoetherianSpace ↥(Z : Set S) :=
    TopologicalSpace.NoetherianSpace.set _
  have hfinC : (irreducibleComponents ↥(Z : Set S)).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  haveI : Finite ↥(irreducibleComponents ↥(Z : Set S)) := hfinC.to_subtype
  have hZval : Topology.IsClosedEmbedding ((↑) : ↥(Z : Set S) → S) :=
    Z.isClosed.isClosedEmbedding_subtypeVal
  let Zc : ↥(irreducibleComponents ↥(Z : Set S)) → TopologicalSpace.Closeds S :=
    fun c => ⟨Subtype.val '' c.1,
      hZval.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ c.2)⟩
  have hirrc : ∀ c, IsIrreducible (Zc c : Set S) := fun c =>
    c.2.1.image _ continuous_subtype_val.continuousOn
  have hZcZ : ∀ c, (Zc c : Set S) ⊆ (Z : Set S) := fun c =>
    Subtype.coe_image_subset _ _
  have hcompcover : ∀ z ∈ (Z : Set S), ∃ c, z ∈ (Zc c : Set S) := by
    intro z hz
    exact ⟨⟨irreducibleComponent (⟨z, hz⟩ : ↥(Z : Set S)),
      irreducibleComponent_mem_irreducibleComponents _⟩,
      ⟨⟨z, hz⟩, mem_irreducibleComponent, rfl⟩⟩
  -- flat strata over the reduced components
  choose Ω hΩne hΩflat using fun c =>
    flat_stratum_of_irreducible π F (Zc c) (hirrc c)
  -- the open complement of the other components
  let A : ↥(irreducibleComponents ↥(Z : Set S)) → Set S := fun c =>
    ⋃ c' : {c' // c' ≠ c}, (Zc c'.1 : Set S)
  have hAclosed : ∀ c, IsClosed (A c) := fun c =>
    isClosed_iUnion_of_finite fun c' => (Zc c'.1).isClosed
  let E : ↥(irreducibleComponents ↥(Z : Set S)) → S.Opens := fun c =>
    ⟨(A c)ᶜ, (hAclosed c).isOpen_compl⟩
  -- the strata
  let St : ∀ c, ((Scheme.IdealSheafData.vanishingIdeal (Zc c)).subscheme).Opens :=
    fun c => Ω c ⊓ (Scheme.IdealSheafData.vanishingIdeal (Zc c)).subschemeι ⁻¹ᵁ E c
  let ιst : ∀ c, ((St c) : Scheme) ⟶ S := fun c =>
    (St c).ι ≫ (Scheme.IdealSheafData.vanishingIdeal (Zc c)).subschemeι
  have himm : ∀ c, IsImmersion (ιst c) := fun c =>
    MorphismProperty.comp_mem @IsImmersion _ _ inferInstance inferInstance
  have hrangek : ∀ c, Set.range
      ((Scheme.IdealSheafData.vanishingIdeal (Zc c)).subschemeι).base = (Zc c : Set S) := by
    intro c
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact congrArg SetLike.coe (support_vanishingIdeal (Zc c))
  have hrangest : ∀ c, Set.range (ιst c).base =
      ((Scheme.IdealSheafData.vanishingIdeal (Zc c)).subschemeι).base ''
        ((St c) : Set _) := by
    intro c
    change Set.range ((St c).ι ≫ _).base = _
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
  -- S-open realizations of the strata
  have hWc : ∀ c, ∃ W : Set S, IsOpen W ∧
      ((Scheme.IdealSheafData.vanishingIdeal (Zc c)).subschemeι).base ⁻¹' W =
        ((St c) : Set _) := by
    intro c
    haveI hCI : IsClosedImmersion
        (Scheme.IdealSheafData.vanishingIdeal (Zc c)).subschemeι := inferInstance
    obtain ⟨W, hW, hWeq⟩ := (hCI.isClosedEmbedding.isInducing.isOpen_iff).mp (St c).2
    exact ⟨W, hW, hWeq⟩
  choose W hWopen hWeq using hWc
  have hrange_eq : ∀ c, Set.range (ιst c).base = W c ∩ (Zc c : Set S) := by
    intro c
    rw [hrangest c, ← hWeq c, Set.image_preimage_eq_inter_range, hrangek c]
  have hstE : ∀ c, Set.range (ιst c).base ⊆ (E c : Set S) := by
    intro c
    rw [hrangest c]
    rintro _ ⟨t, ht, rfl⟩
    exact (ht.2 : _ ∈ _)
  -- the union of the strata is relatively open in `Z`
  have hVW : (⋃ c, Set.range (ιst c).base) =
      (Z : Set S) ∩ ⋃ c, (W c ∩ (E c : Set S)) := by
    apply subset_antisymm
    · refine Set.iUnion_subset fun c => ?_
      intro z hz
      have h1 : z ∈ W c ∩ (Zc c : Set S) := hrange_eq c ▸ hz
      exact ⟨hZcZ c h1.2, Set.mem_iUnion.mpr ⟨c, ⟨h1.1, hstE c hz⟩⟩⟩
    · rintro z ⟨hzZ, hzW⟩
      obtain ⟨c, hzWE⟩ := Set.mem_iUnion.mp hzW
      obtain ⟨c', hzc'⟩ := hcompcover z hzZ
      have hcc' : c' = c := by
        by_contra hne
        exact (hzWE.2 : z ∈ (E c : Set S))
          (Set.mem_iUnion.mpr ⟨⟨c', hne⟩, hzc'⟩)
      refine Set.mem_iUnion.mpr ⟨c, ?_⟩
      rw [hrange_eq c]
      exact ⟨hzWE.1, hcc' ▸ hzc'⟩
  -- the complementary closed set
  let Z' : TopologicalSpace.Closeds S :=
    ⟨(Z : Set S) ∩ (⋃ c, (W c ∩ (E c : Set S)))ᶜ,
      Z.isClosed.inter (isClosed_compl_iff.mpr (isOpen_iUnion fun c =>
        (hWopen c).inter (E c).2))⟩
  -- some component's stratum is non-empty
  obtain ⟨z₀, hz₀⟩ := hZne
  obtain ⟨c₀, hz₀c₀⟩ := hcompcover z₀ hz₀
  have hnotsub : ¬ ((Zc c₀ : Set S) ⊆ A c₀) := by
    intro hsub
    have hsub' : c₀.1 ⊆ ⋃₀ (irreducibleComponents ↥(Z : Set S) \ {c₀.1}) := by
      intro t ht
      obtain ⟨c', hc'⟩ := Set.mem_iUnion.mp (hsub ⟨t, ht, rfl⟩)
      obtain ⟨t', ht', hval⟩ := hc'
      have hteq : t' = t := Subtype.val_injective hval
      subst hteq
      refine ⟨c'.1.1, ⟨c'.1.2, ?_⟩, ht'⟩
      intro hmem
      exact c'.2 (Subtype.ext (by simpa using hmem))
    have hmem := mem_of_subset_sUnion_irreducibleComponents c₀.1 c₀.2 _
      (hfinC.sdiff) Set.sdiff_subset hsub'
    exact hmem.2 rfl
  obtain ⟨z₁, hz₁Zc, hz₁A⟩ := Set.not_subset.mp hnotsub
  have hz₁r : z₁ ∈ Set.range
      ((Scheme.IdealSheafData.vanishingIdeal (Zc c₀)).subschemeι).base := by
    rw [hrangek c₀]; exact hz₁Zc
  obtain ⟨t₁, ht₁⟩ := hz₁r
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal (Zc c₀)).subscheme :=
    isIntegral_vanishingIdeal_subscheme _ (hirrc c₀)
  have hStne : ((St c₀ :
      (Scheme.IdealSheafData.vanishingIdeal (Zc c₀)).subscheme.Opens) :
      Set ↑((Scheme.IdealSheafData.vanishingIdeal (Zc c₀)).subscheme)).Nonempty := by
    have h1 := hΩne c₀
    have h2 : ((((Scheme.IdealSheafData.vanishingIdeal (Zc c₀)).subschemeι ⁻¹ᵁ E c₀) :
        (Scheme.IdealSheafData.vanishingIdeal (Zc c₀)).subscheme.Opens) :
        Set ↑((Scheme.IdealSheafData.vanishingIdeal (Zc c₀)).subscheme)).Nonempty := by
      refine ⟨t₁, ?_⟩
      change ((Scheme.IdealSheafData.vanishingIdeal (Zc c₀)).subschemeι).base t₁ ∈
        (E c₀ : Set S)
      rw [ht₁]
      exact hz₁A
    have h3 := (IrreducibleSpace.isIrreducible_univ
      (↑((Scheme.IdealSheafData.vanishingIdeal (Zc c₀)).subscheme))).2
      _ _ (Ω c₀).2
      ((Scheme.IdealSheafData.vanishingIdeal (Zc c₀)).subschemeι ⁻¹ᵁ E c₀).2
      (by simpa using h1) (by simpa using h2)
    simpa only [St, TopologicalSpace.Opens.coe_inf, Set.univ_inter,
      TopologicalSpace.Opens.carrier_eq_coe] using h3
  -- strict decrease
  have hZ'lt : Z' < Z := by
    refine lt_of_le_of_ne (fun z hz => hz.1) ?_
    intro heq
    obtain ⟨t₀, ht₀⟩ := hStne
    have hz₂ : (ιst c₀) ⟨t₀, ht₀⟩ ∈ ⋃ c, Set.range (ιst c).base :=
      Set.mem_iUnion.mpr ⟨c₀, ⟨⟨t₀, ht₀⟩, rfl⟩⟩
    rw [hVW] at hz₂
    have hmem : (ιst c₀) ⟨t₀, ht₀⟩ ∈ (Z' : Set S) := by
      rw [heq]; exact hz₂.1
    exact hmem.2 hz₂.2
  -- recurse and combine
  obtain ⟨I', hI', V', ι', h1', h2', h3', h4'⟩ := IH Z' hZ'lt
  haveI := hI'
  refine ⟨↥(irreducibleComponents ↥(Z : Set S)) ⊕ I', inferInstance,
    Sum.elim (fun c => ((St c) : Scheme)) V',
    (fun i => match i with
      | Sum.inl c => ιst c
      | Sum.inr i' => ι' i'), ?_, ?_, ?_, ?_⟩
  · rintro (c | i')
    · exact himm c
    · exact h1' i'
  · rintro (c | i') (c' | j') hne
    · have hne' : c ≠ c' := fun h => hne (congrArg Sum.inl h)
      refine Set.disjoint_left.mpr fun {z} hz hz' => ?_
      have h1 : z ∈ W c ∩ (Zc c : Set S) := hrange_eq c ▸ hz
      have h2 := hstE c' hz'
      exact (h2 : z ∈ (E c' : Set S))
        (Set.mem_iUnion.mpr ⟨⟨c, hne'⟩, h1.2⟩)
    · refine Set.disjoint_left.mpr fun {z} hz hz' => ?_
      have hzV : z ∈ (Z : Set S) ∩ ⋃ c'', (W c'' ∩ (E c'' : Set S)) := by
        rw [← hVW]; exact Set.mem_iUnion.mpr ⟨c, hz⟩
      have hzZ' : z ∈ (Z' : Set S) := by
        rw [← h3']
        exact Set.mem_iUnion.mpr ⟨j', hz'⟩
      exact hzZ'.2 hzV.2
    · refine Set.disjoint_left.mpr fun {z} hz hz' => ?_
      have hzV : z ∈ (Z : Set S) ∩ ⋃ c'', (W c'' ∩ (E c'' : Set S)) := by
        rw [← hVW]; exact Set.mem_iUnion.mpr ⟨c', hz'⟩
      have hzZ' : z ∈ (Z' : Set S) := by
        rw [← h3']
        exact Set.mem_iUnion.mpr ⟨i', hz⟩
      exact hzZ'.2 hzV.2
    · have hne' : i' ≠ j' := fun h => hne (congrArg Sum.inr h)
      exact h2' i' j' hne'
  · -- covering
    apply subset_antisymm
    · intro z hz
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
      match i with
      | Sum.inl c =>
        have : z ∈ (Z : Set S) ∩ ⋃ c'', (W c'' ∩ (E c'' : Set S)) := by
          rw [← hVW]; exact Set.mem_iUnion.mpr ⟨c, hzi⟩
        exact this.1
      | Sum.inr i' =>
        have : z ∈ (Z' : Set S) := by
          rw [← h3']; exact Set.mem_iUnion.mpr ⟨i', hzi⟩
        exact this.1
    · intro z hzZ
      by_cases hzW : z ∈ ⋃ c, (W c ∩ (E c : Set S))
      · have hmem : z ∈ (Z : Set S) ∩ ⋃ c, (W c ∩ (E c : Set S)) := ⟨hzZ, hzW⟩
        rw [← hVW] at hmem
        obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hmem
        exact Set.mem_iUnion.mpr ⟨Sum.inl c, hc⟩
      · have hmem : z ∈ (Z' : Set S) := ⟨hzZ, hzW⟩
        rw [← h3'] at hmem
        obtain ⟨i', hi'⟩ := Set.mem_iUnion.mp hmem
        exact Set.mem_iUnion.mpr ⟨Sum.inr i', hi'⟩
  · rintro (c | i')
    · exact hΩflat c (St c) inf_le_left
    · exact h4' i'

/-- **Lemma 7 (assembly via direct images).** [Nitsure §4 assembly step]

For `S` noetherian and `𝓕` coherent on a proper `π : X ⟶ S`, there
exists an integer `N` such that iterating the `n = 0` stratification
(Lemma 5) on the direct images `E_i := π_*𝓕(N+i)` on `S`
(`i = 0, 1, …`) produces, after finitely many refinements, the
Hilbert-polynomial-indexed stratification of the main theorem.

The mathematical content of the step is the existence of the uniform
vanishing bound `N` together with the finite refinement chain producing
the locally-closed strata `S_f` from the rank strata `W_{e_0, …, e_n}`.

The statement below records the existence of a finite locally-closed
stratification refining Lemma 6, together with a label
`P : I → (ℕ → ℤ)` standing for the Hilbert polynomial of a stratum (a
numerical polynomial restricted to `ℕ`), i.e. the
"polynomial-locally-constant" content of Nitsure's statement (A).

Caveat on the strength of that label: as typed, the `P`-conjunct only
demands *some* injection `I → (ℕ → ℤ)`, which any finite index type
admits, so the statement is a formal corollary of `flatLocusReduction`
and is proved as such below.  A genuinely Hilbert-indexed version would
have to tie `P f` to the Euler characteristics of the fibres; the further
refinement of the label to a numerical polynomial of degree `≤ n` is also
not part of this statement. -/
lemma flatLocusAssembly {S X : Scheme.{u}} [IsNoetherian S]
    (π : X ⟶ S) [IsProper π] (F : X.Modules) [F.IsFinitePresentation] :
    ∃ (I : Type u) (_ : Finite I) (S_ : I → Scheme.{u}) (ι : ∀ f, S_ f ⟶ S)
      (P : I → ℕ → ℤ),
      (∀ f, IsImmersion (ι f)) ∧
      (∀ f g, f ≠ g → Disjoint (Set.range (ι f).base) (Set.range (ι g).base)) ∧
      (∀ s : S, ∃ f, s ∈ Set.range (ι f).base) ∧
      (∀ f, Scheme.CoherentSheafFlat (pullback.snd π (ι f))
        ((Scheme.Modules.pullback (pullback.fst π (ι f))).obj F)) ∧
      (∀ f g, f = g ↔ P f = P g) := by
  obtain ⟨I, hI, V_, ι, himm, hdisj, hcov, hflat⟩ := flatLocusReduction π F
  haveI := hI
  haveI := Fintype.ofFinite I
  refine ⟨I, hI, V_, ι, fun i _ => ((Fintype.equivFin I) i : ℤ), himm, hdisj, hcov, hflat,
    fun f g => ⟨fun h => h ▸ rfl, fun h => ?_⟩⟩
  have h0 : (((Fintype.equivFin I) f : ℕ) : ℤ) = (((Fintype.equivFin I) g : ℕ) : ℤ) :=
    congrFun h 0
  exact (Fintype.equivFin I).injective (Fin.val_injective (by exact_mod_cast h0))

/-- **Flattening stratification existence theorem** [Nitsure §4 main /
Stacks 052H].

For a noetherian scheme `S`, a proper morphism `π : X ⟶ S`, and a
coherent `𝓞_X`-module `𝓕`, there exists a finite locally-closed
stratification `{S_f}` of `S` indexed by a finite set `I` such that
- each `ι : S_f ⟶ S` is a (locally-closed) immersion;
- the underlying sets `|S_f|` partition `|S|` (disjoint and covering);
- the pullback `𝓕|_{X ×_S S_f}` is flat over `S_f` for each `f`.

Caveat: the theorem in its full form also asserts that the index set `I`
is in bijection with the set of Hilbert polynomials arising on the fibres,
and that each `S_f` is uniquely determined by its Hilbert polynomial.
That labelling is not part of the statement here; it appears — still in a
weak form — as the injection `P : I → ℕ → ℤ` of `flatLocusAssembly`.  The
conclusion as typed is exactly the conclusion of `flatLocusReduction`
(Lemma 6) up to the order of the conjuncts, and is proved below by that
reduction, so the mathematical content sits in `flatLocusReduction`
(Noetherian induction on `genericFlatness`) and in `genericFlatness`
itself.  A Hilbert-polynomial-indexed refinement would need relative
projective space `ℙⁿ_S`, Castelnuovo–Mumford regularity, and direct-image
base change (Stacks 02KH). -/
theorem flatteningStratification {S X : Scheme.{u}} [IsNoetherian S]
    (π : X ⟶ S) [IsProper π] (F : X.Modules) [F.IsFinitePresentation] :
    ∃ (I : Type u) (_ : Finite I) (S_ : I → Scheme.{u}) (ι : ∀ f, S_ f ⟶ S),
      (∀ f, IsImmersion (ι f)) ∧
      (∀ s : S, ∃ f, s ∈ Set.range (ι f).base) ∧
      (∀ f g, f ≠ g → Disjoint (Set.range (ι f).base) (Set.range (ι g).base)) ∧
      (∀ f, Scheme.CoherentSheafFlat (pullback.snd π (ι f))
        ((Scheme.Modules.pullback (pullback.fst π (ι f))).obj F)) := by
  obtain ⟨I, hI, V_, ι, himm, hdisj, hcov, hflat⟩ := flatLocusReduction π F
  exact ⟨I, hI, V_, ι, himm, hcov, hdisj, hflat⟩

/-- **Lemma 5 (special case `n = 0`).** [Nitsure §4 special case]

For `S` noetherian and `𝓕` a coherent `𝓞_S`-module, there exists a
countable family `S_e ⊆ S` (indexed by `e ∈ ℕ`) of locally-closed
subschemes such that
- each `S_e ⟶ S` is a (locally-closed) immersion;
- the underlying sets `|S_e|` partition `|S|`;
- the pullback `𝓕|_{S_e}` is flat over `𝓞_{S_e}` — encoded as
  `CoherentSheafFlat (𝟙 (S_ e))`, i.e. flatness of the section modules of
  the pulled-back sheaf over the section rings of the stratum *itself*.
  (The *rank*-`e` locally-free refinement is not part of this statement; it
  needs the locally-free-of-rank-`e` predicate.)

Flatness has to be asserted over the stratum, not over the *ambient* `S`
via the immersion: `CoherentSheafFlat (ι e)` is false for any non-open
stratum, as the rank stratification of the skyscraper `k(0)` on `𝔸¹`
shows.  Nitsure's content is flatness — indeed local freeness — over the
stratum, which is `CoherentSheafFlat (𝟙 (S_ e))`.

The hypothesis is `IsNoetherian S`, not `IsLocallyNoetherian S`, matching
the standing noetherian assumption of [Nitsure] §4.  Without the rank-`e`
labelling the strata are not canonical, so the gluing argument that would
extend the ℕ-indexed statement to a merely locally noetherian base
(canonical rank strata glue over any affine cover) is unavailable here.

The proof specializes the existence theorem
`flatteningStratification` to `π = 𝟙 S`.  The finitely many strata
`V_f` are re-indexed over `ℕ` via `Fintype.equivFin`, with the *pullback
scheme* `(𝟙 S) ×_S V_f` itself as stratum and `pullback.fst` as the
immersion (equal to `pullback.snd ≫ ι f` with `pullback.snd` an
isomorphism, since `𝟙 S` is), padded by the empty scheme for indices
`≥ card I`.  Flatness over the stratum transports from the conclusion of
`flatteningStratification` by `coherentSheafFlat_of_comp_isIso`, and over
the empty scheme every section module is flat (the section rings are
trivial). -/
lemma flatLocusStratification {S : Scheme.{u}} [IsNoetherian S]
    (F : S.Modules) [F.IsFinitePresentation] :
    ∃ (S_ : ℕ → Scheme.{u}) (ι : ∀ e, S_ e ⟶ S),
      (∀ e, IsImmersion (ι e)) ∧
      (∀ e e', e ≠ e' → Disjoint (Set.range (ι e).base) (Set.range (ι e').base)) ∧
      (∀ s : S, ∃ e, s ∈ Set.range (ι e).base) ∧
      (∀ e, Scheme.CoherentSheafFlat (𝟙 (S_ e))
        ((Scheme.Modules.pullback (ι e)).obj F)) := by
  classical
  haveI : IsProper (𝟙 S) := MorphismProperty.id_mem _ S
  obtain ⟨I, hI, V_, ι₀, himm, hcov, hdisj, hflat⟩ := flatteningStratification (𝟙 S) F
  haveI := hI
  haveI := Fintype.ofFinite I
  let eqv := Fintype.equivFin I
  -- the first projection is the composition of the iso `pullback.snd` with `ι₀`
  have hfst : ∀ i : I,
      pullback.fst (𝟙 S) (ι₀ i) = pullback.snd (𝟙 S) (ι₀ i) ≫ ι₀ i := fun i => by
    simpa using pullback.condition (f := 𝟙 S) (g := ι₀ i)
  have hrange : ∀ i : I,
      Set.range (pullback.fst (𝟙 S) (ι₀ i)).base = Set.range (ι₀ i).base := by
    intro i
    have hsurj : Function.Surjective (pullback.snd (𝟙 S) (ι₀ i)).base :=
      (ConcreteCategory.bijective_of_isIso (pullback.snd (𝟙 S) (ι₀ i)).base).2
    rw [hfst i]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rw [hsurj.range_eq, Set.image_univ]
  -- reindex the finite strata over `ℕ`, padding with the empty scheme
  let P : ℕ → Σ X : Scheme.{u}, X ⟶ S := fun e =>
    if h : e < Fintype.card I then
      ⟨pullback (𝟙 S) (ι₀ (eqv.symm ⟨e, h⟩)),
        pullback.fst (𝟙 S) (ι₀ (eqv.symm ⟨e, h⟩))⟩
    else ⟨∅, Scheme.emptyTo S⟩
  -- the branch values of `P`, as equalities of the full dependent pair (the
  -- `dite` cannot be reduced under the projections: the motive would not be
  -- type-correct)
  have hPpos : ∀ (e : ℕ) (h : e < Fintype.card I),
      P e = ⟨pullback (𝟙 S) (ι₀ (eqv.symm ⟨e, h⟩)),
        pullback.fst (𝟙 S) (ι₀ (eqv.symm ⟨e, h⟩))⟩ := fun e h => dif_pos h
  have hPneg : ∀ (e : ℕ), ¬ e < Fintype.card I →
      P e = ⟨∅, Scheme.emptyTo S⟩ := fun e h => dif_neg h
  refine ⟨fun e => (P e).1, fun e => (P e).2, ?_, ?_, ?_, ?_⟩
  · -- immersions
    intro e
    change IsImmersion (P e).2
    by_cases h : e < Fintype.card I
    · rw [hPpos e h]
      change IsImmersion (pullback.fst (𝟙 S) (ι₀ (eqv.symm ⟨e, h⟩)))
      haveI := himm (eqv.symm ⟨e, h⟩)
      rw [hfst (eqv.symm ⟨e, h⟩)]
      infer_instance
    · rw [hPneg e h]
      change IsImmersion (Scheme.emptyTo S)
      infer_instance
  · -- disjoint ranges
    intro e e' hne
    change Disjoint (Set.range (P e).2.base) (Set.range (P e').2.base)
    by_cases h : e < Fintype.card I
    · by_cases h' : e' < Fintype.card I
      · rw [hPpos e h, hPpos e' h']
        change Disjoint
          (Set.range (pullback.fst (𝟙 S) (ι₀ (eqv.symm ⟨e, h⟩))).base)
          (Set.range (pullback.fst (𝟙 S) (ι₀ (eqv.symm ⟨e', h'⟩))).base)
        rw [hrange _, hrange _]
        refine hdisj _ _ fun hcontra => hne ?_
        have h2 := congrArg eqv hcontra
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2
        exact congrArg Fin.val h2
      · rw [hPneg e' h']
        change Disjoint (Set.range (P e).2.base) (Set.range (Scheme.emptyTo S).base)
        rw [Set.range_eq_empty (Scheme.emptyTo S).base]
        exact Set.disjoint_empty _
    · rw [hPneg e h]
      change Disjoint (Set.range (Scheme.emptyTo S).base) (Set.range (P e').2.base)
      rw [Set.range_eq_empty (Scheme.emptyTo S).base]
      exact Set.empty_disjoint _
  · -- covering
    intro s
    obtain ⟨f, hf⟩ := hcov s
    refine ⟨(eqv f : ℕ), ?_⟩
    change s ∈ Set.range (P ((eqv f : Fin _) : ℕ)).2.base
    have hlt : ((eqv f : Fin _) : ℕ) < Fintype.card I := (eqv f).isLt
    rw [hPpos _ hlt]
    change s ∈ Set.range (pullback.fst (𝟙 S) (ι₀ (eqv.symm ⟨((eqv f : Fin _) : ℕ), hlt⟩))).base
    rw [hrange _]
    have heq : eqv.symm ⟨((eqv f : Fin _) : ℕ), hlt⟩ = f := by
      simp
    rw [heq]
    exact hf
  · -- flatness over each stratum
    intro e
    change Scheme.CoherentSheafFlat (𝟙 (P e).1)
      ((Scheme.Modules.pullback (P e).2).obj F)
    obtain h | h := Nat.lt_or_ge e (Fintype.card I)
    · rw [hPpos e h]
      change Scheme.CoherentSheafFlat
        (𝟙 (pullback (𝟙 S) (ι₀ (eqv.symm ⟨e, h⟩))))
        ((Scheme.Modules.pullback (pullback.fst (𝟙 S) (ι₀ (eqv.symm ⟨e, h⟩)))).obj F)
      refine coherentSheafFlat_of_comp_isIso
        (𝟙 (pullback (𝟙 S) (ι₀ (eqv.symm ⟨e, h⟩))))
        (pullback.snd (𝟙 S) (ι₀ (eqv.symm ⟨e, h⟩)))
        ((Scheme.Modules.pullback (pullback.fst (𝟙 S) (ι₀ (eqv.symm ⟨e, h⟩)))).obj F) ?_
      rw [Category.id_comp]
      exact hflat _
    · rw [hPneg e (not_lt.mpr h)]
      change Scheme.CoherentSheafFlat (𝟙 (∅ : Scheme.{u}))
        ((Scheme.Modules.pullback (Scheme.emptyTo S)).obj F)
      intro U hU V hV eV
      haveI : Subsingleton Γ((∅ : Scheme.{u}), U) :=
        inferInstanceAs (Subsingleton PUnit)
      letI : Module Γ((∅ : Scheme.{u}), U)
          Γ((Scheme.Modules.pullback (Scheme.emptyTo S)).obj F, V) :=
        Module.compHom _ (Scheme.Hom.appLE (𝟙 (∅ : Scheme.{u})) U V eV).hom
      haveI := Module.Free.of_subsingleton' Γ((∅ : Scheme.{u}), U)
        Γ((Scheme.Modules.pullback (Scheme.emptyTo S)).obj F, V)
      infer_instance

/-! The **universal property of the flat-locus stratification**
(`AlgebraicGeometry.flatLocusStratification_universal`, [Nitsure §4,
special case `n = 0`, parts (i) + (ii)]) is stated and proved in
`AlgebraicJacobian.Picard.FlatteningStratificationUniversal`: its proof
consumes the canonical rank strata of
`AlgebraicJacobian.Picard.EntryIdealStratum`, which this file does not
import. -/

/-- **Flattening stratification for a coherent sheaf on a relative
curve** [Nitsure §4 corollary].

Let `k` be a field, `C` a smooth proper curve over `k` (encoded as
`C : Over (Spec k)` with `[SmoothOfRelativeDimension 1 C.hom]` and
`[IsProper C.hom]`), and `T` a noetherian `k`-scheme. For any coherent
sheaf `𝓕` on the relative curve `C ×_k T`, the flattening
stratification conclusion of `flatteningStratification` applies to
`π = pr_T : C ×_k T → T` and `𝓕`: there is a finite locally-closed
stratification `{T_f ⊆ T}` set-theoretically covering `T` disjointly,
such that `𝓕|_{C ×_k T_f}` is flat over `T_f` for each `f`.

The body invokes `flatteningStratification` on the base-changed
morphism `pullback.snd C.hom T.hom : (C ×_k T) ⟶ T`, using that
`IsProper (pullback.snd C.hom T.hom)` holds by base change of
`IsProper C.hom`. -/
theorem flatteningStratification.ofCurve {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (.of k))) [IsNoetherian T.left]
    (F : (Limits.pullback C.hom T.hom).Modules) [F.IsFinitePresentation] :
    ∃ (I : Type u) (_ : Finite I) (T_ : I → Scheme.{u}) (ι : ∀ f, T_ f ⟶ T.left),
      (∀ f, IsImmersion (ι f)) ∧
      (∀ t : T.left, ∃ f, t ∈ Set.range (ι f).base) ∧
      (∀ f g, f ≠ g → Disjoint (Set.range (ι f).base) (Set.range (ι g).base)) ∧
      (∀ f, Scheme.CoherentSheafFlat
        (pullback.snd (pullback.snd C.hom T.hom) (ι f))
        ((Scheme.Modules.pullback
          (pullback.fst (pullback.snd C.hom T.hom) (ι f))).obj F)) :=
  flatteningStratification (pullback.snd C.hom T.hom) F

end AlgebraicGeometry
