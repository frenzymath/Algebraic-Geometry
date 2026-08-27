/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.QuotFunctorDef
import AlgebraicJacobian.Picard.LineBundlePullback
import AlgebraicJacobian.Picard.FlatKernelBase
import AlgebraicJacobian.Cohomology.AffineSerreVanishing

/-!
# The relative-divisor functor `Div_{X/S}` (real definition)

This file constructs the relative-effective-divisor functor
`AlgebraicGeometry.Scheme.DivFunctor π : (Sch/S)ᵒᵖ ⥤ Type (u+1)` of Kleiman,
"The Picard scheme", §3 (Def. `df:red` + Def. `df:div`; FGA Explained Ch. 9,
arXiv:math/0504020), the source of the Abel map of the A.2.c FGA assembly
(`Picard/FGAPicRepresentability.lean`, whose `divFunctor` carrier this file
makes real).

## Encoding decision (quotient encoding)

Kleiman §3 Def. `df:red`/`df:div`: a *relative effective divisor* on `X_T/T`
is a closed subscheme `D ⊆ X_T` whose ideal `I` is **invertible** and which is
**`T`-flat**; `Div_{X/S}(T)` is the set of such `D`.  We encode a divisor by
its structure-sheaf quotient — the same encoding by which `Div ⊆ Hilb =
Quot_{O}` sits inside the Quot functor (Kleiman §3 Thm. `th:repDiv`): a
`DivFamily π T` is a `Scheme.QuotFamily`-shaped structure with `E` the unit
module `O_X` (so `q : O_{X_T} ⟶ F` up to the canonical isomorphism
`(pr₁)^* O_X ≅ O_{X_T}`; we state the source of `q` verbatim as the pullback
of the unit, exactly as `QuotFamily` does for a general `E`, so that the whole
pullback/functoriality skeleton of `QuotFunctorDef.lean` is reusable), and the
**divisor condition** is: the kernel ideal `I = ker q` is invertible, encoded
by the project-side line-bundle predicate
`Scheme.LineBundle.IsLocallyTrivial (kernel q)` (locally trivial of rank one,
Stacks 01HK — the same predicate that carves the line bundles out of
`Scheme.Modules` in `Picard/LineBundlePullback.lean`).  Between the two
candidate encodings of invertibility (a bundled mono `ι : I ⟶ O` with a
cokernel identification, versus the predicate on the categorical kernel) we
choose the **kernel predicate**: `X.Modules` is abelian, so `ker q` is
available functorially with no extra data fields, the equivalence relation on
families stays literally that of the Quot functor (`ker q = ker q'` — no
well-definedness burden for extra fields), and invertibility-of-an-object is
exactly what `IsLocallyTrivial` and its proved pullback-stability
(`IsLocallyTrivial.pullback`, Stacks 01HH) speak about.

Two families are equivalent iff an isomorphism of the targets commutes with
the quotient maps — equivalently `ker q = ker q'` as subobjects of `O_{X_T}`,
i.e. the two quotients cut out the same closed subscheme `D`.  The value
`DivFunctor π |_T` is the quotient by this relation, so it is Kleiman's *set*
of relative effective divisors on `X_T/T`, not a groupoid of quotients.

Faithfulness notes (Kleiman §3):

* the fields `isFinitePresentation` and `properSupport` do not shrink the set
  of divisors in the intended regime: `F = O_D = coker(I ⟶ O)` with `I`
  invertible is automatically finitely presented, and for the FGA
  instantiation (`π` proper, e.g. the curve `C/k`) the schematic support `D`
  is a closed subscheme of the `T`-proper `X_T`, hence automatically proper
  over `T`.  They are included to keep the family shape identical to
  `QuotFamily` (Div sits inside Hilb) and to reuse its base-change lemmas
  verbatim;
* there is **no Hilbert-polynomial field**: Kleiman's `Div_{X/S}` (`df:div`)
  is not filtered by `Φ` — the degree decomposition `Div = ∐_m Div^m`
  (Kleiman §3 Ex. `ex:DivC`) is a later, separate refinement;
* no hypotheses on `π` are needed for the *functor* (Kleiman `df:div` imposes
  none; projectivity/flatness enter only in the representability theorem
  `th:repDiv`, which is not stated in this file).

## Base-change well-definedness

The pullback action reuses the `QuotFamily` base-change lemmas for the shared
fields (finite presentation: `Modules.pullback_isFinitePresentation`, proved;
flatness: `CoherentSheafFlat.of_isPullback`, proved; proper support:
`Modules.HasProperSupport.of_isPullback`, proved in
`Picard/QuotSupportBaseChange.lean`) and needs exactly one new fact for the
divisor condition, proved in this file as the theorem
`Scheme.Modules.pullback_kernel_isLocallyTrivial` (blueprint
`lem:relative_divisor_base_change`): the kernel of the pulled-back quotient
is the pullback of the kernel — because `0 → I → O → O_D → 0` stays exact
after base change, `Tor_1` against the `T`-flat `O_D` vanishing (Kleiman §3,
functoriality note after `df:div`: "Since `D` is `T`-flat, `p_{X_T}^* I`
equals the ideal of `D_{T'}`") — and pullback preserves invertibility
(`IsLocallyTrivial.pullback`, Stacks 01HH).  The theorem carries a
quasi-coherence hypothesis on the source of the quotient (removable once
extension-closure of quasi-coherence, Stacks 01LA, is available; see the
declaration docstring), discharged here by `pullback_isQuasicoherent_hom` +
`Modules.unit_isQuasicoherent` since the source is the pulled-back unit.
The supporting lemmas — the Stacks 00HL algebra heart
`Module.Flat.rTensor_injective_of_exact`, the comparison map
`Modules.pullbackKernelComparison`, and the chart-shrinking lemmas — live in
`Picard/FlatKernelBase.lean`; the derivation of the pinned statement from
the isomorphism form of the comparison is
`Modules.pullback_kernel_isLocallyTrivial_of_isIso_kernelComparison` (§0).

The functor laws are verbatim the pseudofunctor-coherence argument of
`Scheme.QuotFunctor` (`Modules.pullback_id_app_coherence`,
`Modules.pullback_comp_app_coherence_inv`), which was stated in
`QuotFunctorDef.lean` for arbitrary modules and so applies to the unit.

## References

Blueprint: `def:div_family`, `lem:relative_divisor_base_change`,
`def:div_functor` (`blueprint/src/chapters/Picard_QuotScheme.tex`);
consumed by `def:div_functor_carrier`
(`blueprint/src/chapters/Picard_FGAPicRepresentability.tex`).
Source: [Kleiman], "The Picard scheme", §3 (arXiv:math/0504020).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

open scoped TensorProduct

namespace AlgebraicGeometry

namespace Scheme

/-! ## §0. Invertibility is invariant under isomorphism -/

/-- **Local triviality of rank one is invariant under isomorphism.**  If
`M ≅ N` in `X.Modules` and `M` is locally trivial of rank one
(`Scheme.LineBundle.IsLocallyTrivial`, Stacks 01HK), then so is `N`: restrict
the isomorphism to each trivialising affine chart of `M` (restriction along
an open immersion is functorial). -/
lemma LineBundle.IsLocallyTrivial.of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (hM : LineBundle.IsLocallyTrivial M) :
    LineBundle.IsLocallyTrivial N := by
  intro x
  obtain ⟨U, hxU, hUaff, ⟨t⟩⟩ := hM x
  exact ⟨U, hxU, hUaff, ⟨(Scheme.Modules.restrictFunctor U.ι).mapIso e.symm ≪≫ t⟩⟩

/-- **Read-off along the kernel–pullback comparison**: if the comparison map
`Scheme.Modules.pullbackKernelComparison g' q : g'^*(ker q) ⟶ ker (g'^* q)`
(`Picard/FlatKernelBase.lean`) is an isomorphism, then local triviality of
`ker q` transports to `ker (g'^* q)`: pullback preserves local triviality
(`IsLocallyTrivial.pullback`, Stacks 01HH) and local triviality is invariant
under isomorphism (`IsLocallyTrivial.of_iso`).  This derives the pinned
base-change statement `Modules.pullback_kernel_isLocallyTrivial` from the
isomorphism form of the comparison (the route of blueprint
`lem:relative_divisor_base_change`). -/
lemma Modules.pullback_kernel_isLocallyTrivial_of_isIso_kernelComparison
    {X' X : Scheme.{u}} (g' : X' ⟶ X) {E F : X.Modules} (q : E ⟶ F)
    (hcomp : IsIso (Modules.pullbackKernelComparison g' q))
    (hker : LineBundle.IsLocallyTrivial (Limits.kernel q)) :
    LineBundle.IsLocallyTrivial
      (Limits.kernel ((Scheme.Modules.pullback g').map q)) :=
  haveI := hcomp
  LineBundle.IsLocallyTrivial.of_iso
    (asIso (Modules.pullbackKernelComparison g' q))
    (hker.pullback g')

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of the `fromSpec`/pullback base map.**  Derived from the public
`pullback_app_isoTensor_baseMap` together with naturality of the adjunction unit
(with `pullback_app_isoTensor_unitAtV` inlined). -/
private lemma Modules.baseMap_naturality
    {X Y : Scheme.{u}} (g : Y ⟶ X) {N N' : X.Modules}
    (h : N ⟶ N') {U : Y.Opens} {V : X.Opens} (e : U ≤ g ⁻¹ᵁ V) (x : Γ(N, V)) :
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g).map h) U).hom
        (pullback_app_isoTensor_baseMap g N e x) =
      pullback_app_isoTensor_baseMap g N' e ((Scheme.Modules.Hom.app h V).hom x) := by
  have hb := congrArg
    (fun (k : N ⟶ (Scheme.Modules.pushforward g).obj
        ((Scheme.Modules.pullback g).obj N')) =>
      (Scheme.Modules.Hom.app k V).hom x)
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality h)
  have ha := congrArg
    (fun (k : Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ V) ⟶
        Γ((Scheme.Modules.pullback g).obj N', U)) =>
      (AddCommGrpCat.Hom.hom k)
        ((((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).val.app
          (Opposite.op V)).hom x))
    ((Scheme.Modules.Hom.mapPresheaf ((Scheme.Modules.pullback g).map h)).naturality
      (homOfLE e).op)
  exact ha.trans (congrArg
    (fun w => ((((Scheme.Modules.pullback g).obj N').presheaf.map (homOfLE e).op).hom) w)
    hb.symm)

set_option backward.isDefEq.respectTransparency false in
/-- **Bijectivity of the `fromSpec` base map.**  The canonical base map along
`hV.fromSpec` is bijective for any module `N` (no quasi-coherence needed): it is the
section-level realization of "restriction to an affine open, sections over `⊤` = sections
over `V`".  Modelled on `tildeIso_of_isQuasicoherent_isAffineOpen` with `unitAtV` inlined. -/
private lemma baseMap_fromSpec_bijective {X : Scheme.{u}} (N : X.Modules)
    {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Bijective (pullback_app_isoTensor_baseMap hV.fromSpec N
      (le_of_eq hV.fromSpec_preimage_self.symm)) := by
  have him : hV.fromSpec ''ᵁ (hV.fromSpec ⁻¹ᵁ V) = V := by
    rw [hV.fromSpec_preimage_self, Scheme.Hom.image_top_eq_opensRange,
      hV.opensRange_fromSpec]
  have hrestr : Function.Bijective
      ((((Scheme.Modules.pullback hV.fromSpec).obj N).presheaf.map
        (homOfLE (le_of_eq hV.fromSpec_preimage_self.symm)).op).hom) := by
    rw [Subsingleton.elim
      (homOfLE (le_of_eq hV.fromSpec_preimage_self.symm))
      (eqToHom hV.fromSpec_preimage_self.symm),
      eqToHom_op, eqToHom_map]
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have h1 : Function.Bijective ((Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictAdjunction hV.fromSpec).unit.app N) V).hom) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    refine Function.bijective_iff_has_inverse.mpr
      ⟨(N.presheaf.map (eqToHom him.symm).op).hom, fun y => ?_, fun y => ?_⟩
    · change (AddCommGrpCat.Hom.hom (N.presheaf.map (eqToHom him.symm).op))
          ((AddCommGrpCat.Hom.hom
            (N.presheaf.map (homOfLE (hV.fromSpec.image_preimage_le V)).op)) y) = y
      have hcomp1 : N.presheaf.map (homOfLE (hV.fromSpec.image_preimage_le V)).op ≫
          N.presheaf.map (eqToHom him.symm).op = 𝟙 _ := by
        rw [← Functor.map_comp, ← op_comp,
          Subsingleton.elim
            (eqToHom him.symm ≫ homOfLE (hV.fromSpec.image_preimage_le V)) (𝟙 V),
          op_id, CategoryTheory.Functor.map_id]
      exact congrArg (fun φ => (AddCommGrpCat.Hom.hom φ) y) hcomp1
    · change (AddCommGrpCat.Hom.hom
            (N.presheaf.map (homOfLE (hV.fromSpec.image_preimage_le V)).op))
          ((AddCommGrpCat.Hom.hom (N.presheaf.map (eqToHom him.symm).op)) y) = y
      have hcomp2 : N.presheaf.map (eqToHom him.symm).op ≫
          N.presheaf.map (homOfLE (hV.fromSpec.image_preimage_le V)).op = 𝟙 _ := by
        rw [← Functor.map_comp, ← op_comp,
          Subsingleton.elim
            (homOfLE (hV.fromSpec.image_preimage_le V) ≫ eqToHom him.symm)
            (𝟙 (hV.fromSpec ''ᵁ (hV.fromSpec ⁻¹ᵁ V))),
          op_id, CategoryTheory.Functor.map_id]
      exact congrArg (fun φ => (AddCommGrpCat.Hom.hom φ) y) hcomp2
  have h2 : Function.Bijective ((Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).hom.app N)
      (hV.fromSpec ⁻¹ᵁ V)).hom) := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨((Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).inv.app N)
        (hV.fromSpec ⁻¹ᵁ V)).hom), fun y => ?_, fun y => ?_⟩
    · simp only [← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app,
        Iso.hom_inv_id_app, Scheme.Modules.Hom.id_app, AddCommGrpCat.hom_id,
        AddMonoidHom.id_apply]
    · simp only [← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app,
        Iso.inv_hom_id_app, Scheme.Modules.Hom.id_app, AddCommGrpCat.hom_id,
        AddMonoidHom.id_apply]
  have hcomp : (Scheme.Modules.restrictAdjunction hV.fromSpec).unit.app N ≫
      (Scheme.Modules.pushforward hV.fromSpec).map
        ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).hom.app N) =
      (Scheme.Modules.pullbackPushforwardAdjunction hV.fromSpec).unit.app N :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ N
  have hunit : Function.Bijective
      (fun x : Γ(N, V) =>
        (((((Scheme.Modules.pullbackPushforwardAdjunction hV.fromSpec).unit.app N).val).app
          (Opposite.op V)).hom) x) := by
    have hfun : ∀ x : Γ(N, V),
        (((((Scheme.Modules.pullbackPushforwardAdjunction hV.fromSpec).unit.app N).val).app
          (Opposite.op V)).hom) x =
        (Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).hom.app N)
          (hV.fromSpec ⁻¹ᵁ V)).hom
        ((Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictAdjunction hV.fromSpec).unit.app N) V).hom x) :=
      fun x => (congrArg (fun φ => (Scheme.Modules.Hom.app φ V).hom x) hcomp.symm)
    have hrw : (fun x : Γ(N, V) =>
          (((((Scheme.Modules.pullbackPushforwardAdjunction hV.fromSpec).unit.app N).val).app
            (Opposite.op V)).hom) x) =
        (fun y => (Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).hom.app N)
          (hV.fromSpec ⁻¹ᵁ V)).hom y) ∘
        (fun x => (Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictAdjunction hV.fromSpec).unit.app N) V).hom x) :=
      funext hfun
    rw [hrw]
    exact h2.comp h1
  have hcompose : ⇑(pullback_app_isoTensor_baseMap hV.fromSpec N
        (le_of_eq hV.fromSpec_preimage_self.symm)) =
      (fun y => (((Scheme.Modules.pullback hV.fromSpec).obj N).presheaf.map
        (homOfLE (le_of_eq hV.fromSpec_preimage_self.symm)).op).hom y) ∘
      (fun x : Γ(N, V) =>
        (((((Scheme.Modules.pullbackPushforwardAdjunction hV.fromSpec).unit.app N).val).app
          (Opposite.op V)).hom) x) := rfl
  rw [hcompose]
  exact hrestr.comp hunit

set_option maxHeartbeats 1600000 in
-- Heartbeat headroom: the Čech-vanishing transport and short-exact base change under
-- binders provision many instances, as in the affine-locality engines of `QuotScheme`.
/-- **Section surjectivity of an epimorphism of quasi-coherent sheaves over an affine
open.**  For an epimorphism `q : E ⟶ F` of quasi-coherent modules with
quasi-coherent kernel, and an affine open `V`, the section map `Γ(q, V) : Γ(E,V) → Γ(F,V)`
is surjective (the `H¹(V, ker q) = 0` content).  Transport the short exact sequence
`0 → ker q → E → F → 0` along the exact `hV.fromSpec`-pullback to `Spec Γ(X,V)`, apply
the Čech section-surjectivity `affine_surj_of_vanishing_affine`, then transport back through
the (bijective, `q`-natural) `fromSpec` base map. -/
private theorem section_surjective_of_epi_qcoh
    {X : Scheme.{u}} {E F : X.Modules} (q : E ⟶ F) [Epi q]
    [E.IsQuasicoherent] [F.IsQuasicoherent] [(Limits.kernel q).IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Surjective ((Scheme.Modules.Hom.app q V).hom) := by
  haveI hoi : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  haveI : PreservesFiniteColimits (Scheme.Modules.pullback hV.fromSpec) := by
    haveI := (Scheme.Modules.pullbackPushforwardAdjunction
      hV.fromSpec).leftAdjoint_preservesColimits
    infer_instance
  haveI : PreservesFiniteLimits (Scheme.Modules.pullback hV.fromSpec) := inferInstance
  set SC : ShortComplex X.Modules :=
    ShortComplex.mk (Limits.kernel.ι q) q (Limits.kernel.condition q) with hSC
  have hSCse : SC.ShortExact := ShortComplex.ShortExact.mk (ShortComplex.exact_kernel q)
  set S : ShortComplex (Spec Γ(X, V)).Modules :=
    SC.map (Scheme.Modules.pullback hV.fromSpec) with hSdef
  have hS : S.ShortExact := hSCse.map_of_exact (Scheme.Modules.pullback hV.fromSpec)
  haveI : (S.X₁).IsQuasicoherent :=
    pullback_isQuasicoherent_hom hV.fromSpec (Limits.kernel q) inferInstance
  have hvanish : ∀ (n : ℕ) (g : Fin n → Γ(X, V)),
      IsAffineOpen (X := Spec Γ(X, V))
          (⨆ i : ULift.{u} (Fin n), PrimeSpectrum.basicOpen (g i.down)) →
      ∀ (qq : ℕ), 0 < qq →
        IsZero (cechCohomology
          (fun i : ULift.{u} (Fin n) => PrimeSpectrum.basicOpen (g i.down))
          ((Scheme.Modules.toPresheafOfModules (Spec Γ(X, V))).obj S.X₁) qq) := by
    intro n g haff qq hqq
    refine cechCohomology_isZero_of_iso _
      ((Scheme.Modules.toPresheafOfModules (Spec Γ(X, V))).mapIso
        (qcoh_iso_tilde_sections S.X₁).symm) qq ?_
    exact sectionCech_homology_exact_of_affineOpen (moduleSpecΓFunctor.obj S.X₁)
      (fun i : ULift.{u} (Fin n) => g i.down) haff qq hqq
  have hsurj := affine_surj_of_vanishing_affine S hS hvanish ⊤ (isAffineOpen_top _)
  intro y
  have e : (⊤ : (Spec Γ(X, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V :=
    le_of_eq hV.fromSpec_preimage_self.symm
  obtain ⟨z, hz⟩ := hsurj (pullback_app_isoTensor_baseMap hV.fromSpec F e y)
  obtain ⟨x', hx'⟩ := (baseMap_fromSpec_bijective E hV).surjective z
  refine ⟨x', (baseMap_fromSpec_bijective F hV).injective ?_⟩
  rw [← Modules.baseMap_naturality hV.fromSpec q e x', hx']
  exact hz

/-- The canonical base-change addition map `B ⊗[A] M → D ⊗[C] M`,
`b ⊗ m ↦ (algebraMap B D b) ⊗ m`, for a pushout square `A → B, A → C, C → D, B → D`
and a `C`-module `M`. -/
private noncomputable def pushoutTmulAddHom
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra C D] [Algebra B D] [Algebra A D]
    [IsScalarTower A C D] [IsScalarTower A B D]
    (M : Type u) [AddCommGroup M] [Module A M] [Module C M] [IsScalarTower A C M] :
    (B ⊗[A] M) →+ (D ⊗[C] M) :=
  (TensorProduct.lift
    ({ toFun := fun b => (TensorProduct.mk C D M (algebraMap B D b)).restrictScalars A
       map_add' := fun b b' => by
         ext m
         simp only [map_add, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
           LinearMap.add_apply]
       map_smul' := fun a b => by
         ext m
         simp only [RingHom.id_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
           LinearMap.smul_apply]
         rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply A B D,
           TensorProduct.smul_tmul', Algebra.smul_def, IsScalarTower.algebraMap_apply A C D] } :
      B →ₗ[A] M →ₗ[A] (D ⊗[C] M))).toAddMonoidHom

private lemma pushoutTmulAddHom_apply
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra C D] [Algebra B D] [Algebra A D]
    [IsScalarTower A C D] [IsScalarTower A B D]
    {M : Type u} [AddCommGroup M] [Module A M] [Module C M] [IsScalarTower A C M]
    (b : B) (m : M) :
    pushoutTmulAddHom (A := A) (C := C) M (b ⊗ₜ[A] m) = algebraMap B D b ⊗ₜ[C] m := rfl

/-- **Base-change injectivity across a pushout of rings.**  For a pushout square
`A → B, A → C, C → D` (`D = B ⊗[A] C`) and a `C`-linear map `φ : MK → ME`, if the
`A`-base change `B ⊗[A] φ` is injective, then the `C`-base change `D ⊗[C] φ` is
injective.  The two are conjugate by the pushout scalar-extension iso
`bijective_addHom_of_isPushout`. -/
private lemma lTensor_injective_of_pushout
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra C D] [Algebra B D] [Algebra A D]
    [IsScalarTower A C D] [IsScalarTower A B D] [Algebra.IsPushout A C B D]
    {MK ME : Type u} [AddCommGroup MK] [Module A MK] [Module C MK] [IsScalarTower A C MK]
    [AddCommGroup ME] [Module A ME] [Module C ME] [IsScalarTower A C ME]
    (φ : MK →ₗ[C] ME)
    (hinj : Function.Injective (LinearMap.lTensor B (φ.restrictScalars A))) :
    Function.Injective (TensorProduct.AlgebraTensorModule.lTensor D D φ) := by
  have hbijK : Function.Bijective (pushoutTmulAddHom (A := A) (B := B) (C := C) (D := D) MK) :=
    SectionBaseChange.bijective_addHom_of_isPushout _ (fun b m => rfl)
  have hbijE : Function.Bijective (pushoutTmulAddHom (A := A) (B := B) (C := C) (D := D) ME) :=
    SectionBaseChange.bijective_addHom_of_isPushout _ (fun b m => rfl)
  -- the reconciliation square: `σ_E ∘ (B ⊗ φ) = (D ⊗ φ) ∘ σ_K`
  have hsq : ∀ z : B ⊗[A] MK,
      pushoutTmulAddHom (A := A) (B := B) (C := C) (D := D) ME
          (LinearMap.lTensor B (φ.restrictScalars A) z) =
        TensorProduct.AlgebraTensorModule.lTensor D D φ
          (pushoutTmulAddHom (A := A) (B := B) (C := C) (D := D) MK z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b m => rfl
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]
  -- conclude: `D ⊗ φ = σ_E ∘ (B ⊗ φ) ∘ σ_K⁻¹`, injective
  intro a₁ a₂ ha
  obtain ⟨w₁, rfl⟩ := hbijK.surjective a₁
  obtain ⟨w₂, rfl⟩ := hbijK.surjective a₂
  rw [← hsq, ← hsq] at ha
  have := hinj (hbijE.injective ha)
  rw [this]

/-- The `V`-section map of a morphism of sheaves of modules, bundled as a
`Γ(X, V)`-linear map (the underlying additive map is `(Hom.app φ V).hom`;
`Γ(X, V)`-linearity is `Hom.app_smul`). -/
private noncomputable def Modules.appₗ {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (V : X.Opens) :
    Γ(M, V) →ₗ[Γ(X, V)] Γ(N, V) where
  toFun := (Scheme.Modules.Hom.app φ V).hom
  map_add' := map_add _
  map_smul' := fun r x => Scheme.Modules.Hom.app_smul φ r x

set_option maxSynthPendingDepth 3 in
-- Instance-search depth: the per-piece instance provisioning mirrors
-- `flat_section_pullback_piece` (`GenericFlatnessGeometric`), plus the section-equiv
-- conjugation and pushout reconciliation.
/-- **Per-piece injectivity of the pulled-back kernel inclusion.**  On an affine piece
`W = g'⁻¹V ⊓ f'⁻¹Ut` of the fibre-product
square (over an affine base `U`, with `V` affine `⊆ f⁻¹U` and `Ut` affine `⊆ g⁻¹U`),
the pulled-back kernel inclusion `g'^*(ker q ↪ E)` is injective on `W`-sections.  Proof:
the section-equiv `pullback_app_isoTensor_baseMap_sectionLinearEquiv` conjugates the
`W`-section map into `Γ(X',W) ⊗_{Γ(X,V)} Γ(ker q,V) → Γ(X',W) ⊗_{Γ(X,V)} Γ(E,V)`; the
pushout `Γ(X',W) = Γ(X,V) ⊗_{Γ(S,U)} Γ(S',Ut)` rebases this to `Γ(S',Ut) ⊗_{Γ(S,U)} ·`
(`lTensor_injective_of_pushout`), where flatness of `Γ(F,V)` over `Γ(S,U)` and the section
SES (`section_surjective_of_epi_qcoh` + left-exactness of `Γ(-,V)`) give injectivity
(`Module.Flat.lTensor_injective_of_exact`). -/
private theorem app_injective_on_piece
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) {E F : X.Modules} (q : E ⟶ F) [Epi q]
    [E.IsQuasicoherent] [F.IsQuasicoherent] [(Limits.kernel q).IsQuasicoherent]
    (hflat : CoherentSheafFlat f F)
    {U : S.Opens} {V : X.Opens} {Ut : S'.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUt : IsAffineOpen Ut)
    (hUSX : V ≤ f ⁻¹ᵁ U) (hUST : Ut ≤ g ⁻¹ᵁ U) :
    Function.Injective ((Scheme.Modules.Hom.app
      ((Scheme.Modules.pullback g').map (Limits.kernel.ι q))
      (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut)).hom) := by
  have hW : IsAffineOpen (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) :=
    isAffineOpen_pullback_piece sq hUST hUSX hU hUt hV
  -- ring/algebra structures on the four corners (as in `flat_section_pullback_piece`)
  letI : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hUSX).hom.toAlgebra
  letI : Algebra Γ(S, U) Γ(S', Ut) := (g.appLE U Ut hUST).hom.toAlgebra
  letI : Algebra Γ(X, V) Γ(X', g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) :=
    (g'.appLE V (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) inf_le_left).hom.toAlgebra
  letI : Algebra Γ(S', Ut) Γ(X', g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) :=
    (f'.appLE Ut (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) inf_le_right).hom.toAlgebra
  letI : Algebra Γ(S, U) Γ(X', g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) :=
    ((g'.appLE V (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) inf_le_left).hom.comp
      (f.appLE U V hUSX).hom).toAlgebra
  haveI : IsScalarTower Γ(S, U) Γ(X, V) Γ(X', g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(S, U) Γ(S', Ut) Γ(X', g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) :=
    IsScalarTower.of_algebraMap_eq' (by
      change ((g'.appLE V _ inf_le_left).hom.comp (f.appLE U V hUSX).hom) =
        (f'.appLE Ut _ inf_le_right).hom.comp (g.appLE U Ut hUST).hom
      have h1 : f.appLE U V hUSX ≫ g'.appLE V (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) inf_le_left =
          g.appLE U Ut hUST ≫ f'.appLE Ut (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) inf_le_right := by
        rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        have key : ∀ (φ : X' ⟶ S) (_ : f' ≫ g = φ)
            (w₁ : (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) ≤ φ ⁻¹ᵁ U)
            (w₂ : (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) ≤ (f' ≫ g) ⁻¹ᵁ U),
            φ.appLE U (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) w₁ =
              (f' ≫ g).appLE U (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) w₂ := by
          rintro φ rfl w₁ w₂; rfl
        exact key (g' ≫ f) sq.w.symm _ _
      exact congrArg CommRingCat.Hom.hom h1)
  haveI hpo : Algebra.IsPushout Γ(S, U) Γ(X, V) Γ(S', Ut)
      Γ(X', g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) :=
    CommRingCat.isPushout_iff_isPushout.mp
      (isPushout_appLE_pullback_piece sq hUST hUSX hU hUt hV)
  -- module structures on `Γ(ker q, V)`, `Γ(E, V)` over `Γ(S, U)`
  letI : Module Γ(S, U) Γ(Limits.kernel q, V) := Module.compHom _ (f.appLE U V hUSX).hom
  haveI : IsScalarTower Γ(S, U) Γ(X, V) Γ(Limits.kernel q, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module Γ(S, U) Γ(E, V) := Module.compHom _ (f.appLE U V hUSX).hom
  haveI : IsScalarTower Γ(S, U) Γ(X, V) Γ(E, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module Γ(S, U) Γ(F, V) := Module.compHom _ (f.appLE U V hUSX).hom
  haveI : IsScalarTower Γ(S, U) Γ(X, V) Γ(F, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  -- the two section maps as `Γ(X, V)`-linear maps
  set φ := Modules.appₗ (Limits.kernel.ι q) V with hφ
  set ψ := Modules.appₗ q V with hψ
  -- the section-level SES data
  set SC : ShortComplex X.Modules :=
    ShortComplex.mk (Limits.kernel.ι q) q (Limits.kernel.condition q) with hSC
  have hSCse : SC.ShortExact := ShortComplex.ShortExact.mk (ShortComplex.exact_kernel q)
  haveI hpfl : PreservesFiniteLimits (sectionsFunctor V) := by
    unfold sectionsFunctor; infer_instance
  haveI hpzm : (sectionsFunctor V).PreservesZeroMorphisms := by
    unfold sectionsFunctor; infer_instance
  have hφinj : Function.Injective φ := by
    have hm : Mono ((sectionsFunctor V).map SC.f) :=
      inferInstanceAs (Mono ((sectionsFunctor V).map SC.f))
    rw [AddCommGrpCat.mono_iff_injective] at hm
    exact hm
  have hexact : Function.Exact φ ψ := by
    have hex : (SC.map (sectionsFunctor V)).Exact :=
      ShortComplex.Exact.map_of_mono_of_preservesKernel hSCse.exact
        (sectionsFunctor V) hSCse.mono_f inferInstance
    rw [ShortComplex.ab_exact_iff_function_exact] at hex
    exact hex
  have hψsurj : Function.Surjective ψ := section_surjective_of_epi_qcoh q hV
  have hFflat : Module.Flat Γ(S, U) Γ(F, V) := hflat hU hV hUSX
  -- injectivity of the rebased tensor map
  have hLinj : Function.Injective
      (TensorProduct.AlgebraTensorModule.lTensor Γ(X', g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut)
        Γ(X', g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) φ) := by
    refine lTensor_injective_of_pushout (A := Γ(S, U)) (B := Γ(S', Ut))
      (D := Γ(X', g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut)) φ ?_
    exact Module.Flat.lTensor_injective_of_exact (f := φ.restrictScalars Γ(S, U))
      (g := ψ.restrictScalars Γ(S, U)) hφinj hexact hψsurj hFflat Γ(S', Ut)
  -- section equivs for `ker q` and `E`
  obtain ⟨⟨fK, hfK⟩⟩ :=
    pullback_app_isoTensor_baseMap_sectionLinearEquiv g' (Limits.kernel q) hW hV inf_le_left
  obtain ⟨⟨fE, hfE⟩⟩ :=
    pullback_app_isoTensor_baseMap_sectionLinearEquiv g' E hW hV inf_le_left
  -- conjugation: the `W`-section map, precomposed with `fK`, is `fE ∘ (Γ(X',W) ⊗ φ)`
  set T := Modules.appₗ ((Scheme.Modules.pullback g').map (Limits.kernel.ι q))
    (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) with hT
  have hcong : T.comp fK.toLinearMap =
      fE.toLinearMap.comp (TensorProduct.AlgebraTensorModule.lTensor
        Γ(X', g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) Γ(X', g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut) φ) := by
    refine SectionBaseChange.linearMap_ext_one_tmul (fun x => ?_)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.AlgebraTensorModule.lTensor_tmul]
    rw [hfK x, hfE (φ x)]
    exact Modules.baseMap_naturality g' (Limits.kernel.ι q) inf_le_left x
  -- conclude injectivity of `T`
  have hTfK : Function.Injective (T.comp fK.toLinearMap) := by
    rw [hcong]
    exact fE.injective.comp hLinj
  intro a b hab
  obtain ⟨a', rfl⟩ := fK.surjective a
  obtain ⟨b', rfl⟩ := fK.surjective b
  refine congrArg (⇑fK) (hTfK ?_)
  change (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g').map (Limits.kernel.ι q))
      (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut)).hom (fK a')
    = (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g').map (Limits.kernel.ι q))
      (g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut)).hom (fK b')
  exact hab

set_option maxSynthPendingDepth 3 in
-- Instance-search depth: the per-basic-open localization instances
-- (`isLocalizedModule_basicOpen`) and the localized-map universal property are
-- provisioned under binders, as in the affine section engines of `QuotScheme`.
/-- **Descent of section injectivity to a basic open** (globalisation glue).  For a
morphism `φ` of quasi-coherent modules and an affine open `W`, injectivity of the
`W`-section map descends to injectivity of the section map over any basic open
`X.basicOpen f` (`f : Γ(X, W)`): both section modules are localisations of the
`W`-sections at `powers f` (`Scheme.Modules.isLocalizedModule_basicOpen`), and the
localisation of an injective linear map stays injective
(`IsLocalizedModule.map_injective`, identified with the basic-open section map by the
universal property `IsLocalizedModule.linearMap_ext` + presheaf naturality of `φ`). -/
private theorem app_injective_basicOpen {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) {W : X.Opens} (hW : IsAffineOpen W)
    (hinj : Function.Injective ((Scheme.Modules.Hom.app φ W).hom)) (f : Γ(X, W)) :
    Function.Injective ((Scheme.Modules.Hom.app φ (X.basicOpen f)).hom) := by
  letI : Module Γ(X, W) Γ(M, X.basicOpen f) :=
    Module.compHom _ (algebraMap Γ(X, W) Γ(X, X.basicOpen f))
  haveI : IsScalarTower Γ(X, W) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module Γ(X, W) Γ(N, X.basicOpen f) :=
    Module.compHom _ (algebraMap Γ(X, W) Γ(X, X.basicOpen f))
  haveI : IsScalarTower Γ(X, W) Γ(X, X.basicOpen f) Γ(N, X.basicOpen f) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI hlocM : IsLocalizedModule (Submonoid.powers f)
      (Scheme.Modules.restrictBasicOpenₗ M f) :=
    Scheme.Modules.isLocalizedModule_basicOpen M hW f
  haveI hlocN : IsLocalizedModule (Submonoid.powers f)
      (Scheme.Modules.restrictBasicOpenₗ N f) :=
    Scheme.Modules.isLocalizedModule_basicOpen N hW f
  have hmapinj : Function.Injective (IsLocalizedModule.map (Submonoid.powers f)
      (Scheme.Modules.restrictBasicOpenₗ M f) (Scheme.Modules.restrictBasicOpenₗ N f)
      (Modules.appₗ φ W)) :=
    IsLocalizedModule.map_injective (Submonoid.powers f)
      (Scheme.Modules.restrictBasicOpenₗ M f) (Scheme.Modules.restrictBasicOpenₗ N f)
      (Modules.appₗ φ W) hinj
  have hid : IsLocalizedModule.map (Submonoid.powers f)
        (Scheme.Modules.restrictBasicOpenₗ M f) (Scheme.Modules.restrictBasicOpenₗ N f)
        (Modules.appₗ φ W)
      = (Modules.appₗ φ (X.basicOpen f)).restrictScalars Γ(X, W) := by
    refine IsLocalizedModule.linearMap_ext (Submonoid.powers f)
      (Scheme.Modules.restrictBasicOpenₗ M f) (Scheme.Modules.restrictBasicOpenₗ N f) ?_
    rw [IsLocalizedModule.map_comp]
    ext x
    exact (congr($(φ.mapPresheaf.naturality (homOfLE (X.basicOpen_le f)).op) x)).symm
  intro a b hab
  apply hmapinj
  rw [hid]
  exact hab

/-! ## §1. Base change of the ideal of a relative effective divisor

The one NEW base-change fact the divisor functor needs beyond the Quot-family
lemmas of `QuotFunctorDef.lean` §2: the invertible kernel ideal of a `T`-flat
quotient of `O` pulls back to the (again invertible) kernel ideal of the
pulled-back quotient.  Blueprint node: `lem:relative_divisor_base_change`. -/

/-- **`g'^*` preserves the kernel inclusion `ker q ↪ E` as a monomorphism** — the
flat-base-change monomorphism at the heart of `lem:relative_divisor_base_change`
(Stacks 00HL).  For a cartesian square and an epimorphism `q` of quasi-coherent modules
with `F` finitely presented and flat over the base and `ker q` locally trivial, the
pullback `g'^*(ker q ↪ E)` stays monic.  Route: per-piece injectivity
`app_injective_on_piece` (the affine-local `Module.Flat.rTensor_injective_of_exact`
content) holds on every affine piece `W = g'⁻¹V ⊓ f'⁻¹Ut` of the fibre-product square;
the pieces are affine and cover `X'` but are NOT a topological basis (the scheme fibre
product carries a topology finer than `|X| ×_{|S|} |S'|`), so the injectivity is descended
to the basic opens of the pieces (`app_injective_basicOpen`, flat localisation
`isLocalizedModule_basicOpen`), which DO form a basis of `X'`, and the basis-local
monomorphism criterion `Modules.mono_of_injective_app_of_isBasis` concludes. -/
theorem Modules.mono_pullback_map_kernel_ι
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) {E F : X.Modules} (q : E ⟶ F) (hq : Epi q)
    (hE : E.IsQuasicoherent)
    (hfp : F.IsFinitePresentation) (hflat : CoherentSheafFlat f F)
    (hker : LineBundle.IsLocallyTrivial (Limits.kernel q)) :
    Mono ((Scheme.Modules.pullback g').map (Limits.kernel.ι q)) := by
  haveI := hq
  -- Provision the quasi-coherence instances the per-piece engine consumes: `E` (`hE`),
  -- `F` (finitely presented, `hfp`), `ker q` (locally trivial ⟹ finitely presented,
  -- `hker`), and their pullbacks (`pullback_isQuasicoherent_hom`).
  haveI := hE
  haveI := hfp
  haveI := hker.isFinitePresentation
  haveI hMqc : ((Scheme.Modules.pullback g').obj (Limits.kernel q)).IsQuasicoherent :=
    pullback_isQuasicoherent_hom g' (Limits.kernel q) inferInstance
  haveI hNqc : ((Scheme.Modules.pullback g').obj E).IsQuasicoherent :=
    pullback_isQuasicoherent_hom g' E inferInstance
  set φ := (Scheme.Modules.pullback g').map (Limits.kernel.ι q) with hφ
  -- per-point: an affine piece through the point, on which `φ` is section-injective
  have H : ∀ x : X', ∃ W : X'.Opens, IsAffineOpen W ∧ x ∈ W ∧
      Function.Injective ((Scheme.Modules.Hom.app φ W).hom) := by
    intro x
    have hbase : f.base (g'.base x) = g.base (f'.base x) := by
      have h := congrArg (fun ψ : X' ⟶ S => ψ.base x) sq.w
      simpa using h
    obtain ⟨U, hU, hsU, -⟩ := exists_isAffineOpen_mem_and_subset
      (TopologicalSpace.Opens.mem_top (f.base (g'.base x)))
    obtain ⟨V, hV, hxV, hVsub⟩ := exists_isAffineOpen_mem_and_subset
      (show g'.base x ∈ f ⁻¹ᵁ U from hsU)
    obtain ⟨Ut, hUt, hxUt, hUtsub⟩ := exists_isAffineOpen_mem_and_subset
      (show f'.base x ∈ g ⁻¹ᵁ U by
        change g.base (f'.base x) ∈ U
        rw [← hbase]; exact hsU)
    exact ⟨g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut,
      isAffineOpen_pullback_piece sq hUtsub hVsub hU hUt hV, ⟨hxV, hxUt⟩,
      app_injective_on_piece sq q hflat hU hV hUt hVsub hUtsub⟩
  choose W hWaff hxW hinjW using H
  -- the basic opens of the covering pieces form a basis of `X'`; `φ` is injective on each
  refine Modules.mono_of_injective_app_of_isBasis
    (B := fun p : Σ x : X', Γ(X', W x) => X'.basicOpen p.2) ?_ φ ?_
  · rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro O pt hptO
    obtain ⟨fb, hfle, hxf⟩ := (hWaff pt).exists_basicOpen_le (⟨pt, hptO⟩ : O) (hxW pt)
    exact ⟨X'.basicOpen fb, ⟨⟨pt, fb⟩, rfl⟩, hxf, hfle⟩
  · rintro ⟨x, fb⟩
    exact app_injective_basicOpen φ (hWaff x) (hinjW x) fb

/-- **The invertible kernel of a base-flat quotient stays invertible under
base change** (Kleiman §3, the functoriality of `Div_{X/S}` — the note after
Def. `df:div`: "Since `D` is `T`-flat, `p_{X_T}^* \mathcal I` equals the
ideal of `D_{T'}`.  But, since `\mathcal I` is invertible, so is
`p_{X_T}^* \mathcal I`").

For a cartesian square `sq : X' = X ×_S S'` and an epimorphism `q : E ⟶ F` of
`O_X`-modules with `E` quasi-coherent and `F` finitely presented and flat
over `S` (`Scheme.CoherentSheafFlat`), if `ker q` is locally trivial of rank
one then so is `ker (g'^* q)`.  Mathematical content: the short exact
sequence `0 → ker q → E → F → 0` stays exact after applying the right-exact
`g'^*`, because affine-locally the failure of left exactness is
`Tor_1^{Γ(S,U)}(Γ(F,V), Γ(S',U_t))`, which vanishes by base-flatness of `F`
(Stacks 00HL, `Module.Flat.rTensor_injective_of_exact`);
hence `ker (g'^* q) ≅ g'^* (ker q)`, and pullback preserves local triviality
of rank one (`Scheme.LineBundle.IsLocallyTrivial.pullback`, Stacks 01HH).
See the blueprint node `lem:relative_divisor_base_change` for the complete
proof.

The hypothesis `hE : E.IsQuasicoherent` is needed by the affine-local section
calculus (`pullback_app_isoTensor`); the statement is true without it —
`E` is an extension of the quasi-coherent `F` by the locally trivial (hence
quasi-coherent, `LineBundle.IsLocallyTrivial.isFinitePresentation`) `ker q`,
and an extension of quasi-coherents is quasi-coherent (Stacks 01LA) — but
extension-closure of `IsQuasicoherent` is not yet available, and the sole
consumer (`DivFamily.pullbackAlong`) instantiates `E` at a pullback of the
unit module, quasi-coherent by `pullback_isQuasicoherent_hom` +
`Modules.unit_isQuasicoherent`. -/
theorem Modules.pullback_kernel_isLocallyTrivial
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) {E F : X.Modules} (q : E ⟶ F) (hq : Epi q)
    (hE : E.IsQuasicoherent)
    (hfp : F.IsFinitePresentation) (hflat : CoherentSheafFlat f F)
    (hker : LineBundle.IsLocallyTrivial (Limits.kernel q)) :
    LineBundle.IsLocallyTrivial
      (Limits.kernel ((Scheme.Modules.pullback g').map q)) := by
  -- The comparison `κ = pullbackKernelComparison g' q : g'^*(ker q) ⟶ ker (g'^* q)`
  -- is always epi (`q` epi, `g'^*` right exact: `epi_pullbackKernelComparison`).  It is
  -- an isomorphism as soon as `g'^*` keeps the kernel inclusion `ker q ↪ E` monic
  -- (`isIso_pullbackKernelComparison_of_mono`, `FlatKernelBase.lean`) — the
  -- flat-base-change monomorphism `mono_pullback_map_kernel_ι` — and then the read-off
  -- lemma `pullback_kernel_isLocallyTrivial_of_isIso_kernelComparison` (§0) transports the
  -- rank-one local triviality of `ker q` across it.
  haveI := hq
  exact Modules.pullback_kernel_isLocallyTrivial_of_isIso_kernelComparison g' q
    (Modules.isIso_pullbackKernelComparison_of_mono g' q
      (Modules.mono_pullback_map_kernel_ι sq q hq hE hfp hflat hker)) hker

/-- **The kernel–pullback comparison is an isomorphism** (blueprint
`lem:relative_divisor_base_change`; the Abel-map feeder).  For a cartesian square and an
epimorphism `q` of quasi-coherent modules with `F` finitely presented and flat over the
base and `ker q` locally trivial, the comparison
`Scheme.Modules.pullbackKernelComparison g' q : g'^*(ker q) ⟶ ker (g'^* q)` is an
isomorphism: it is always an epimorphism (`epi_pullbackKernelComparison`, `q` epi and
`g'^*` right exact) and, by the flat-base-change monomorphism
`mono_pullback_map_kernel_ι`, the pullback of the kernel inclusion stays monic, so
`isIso_pullbackKernelComparison_of_mono` (`X'.Modules` is abelian, hence balanced) upgrades
it to an isomorphism.  This is the isomorphism form that `DivFamily.pullbackAlong` /
the Abel map consume via `pullback_kernel_isLocallyTrivial_of_isIso_kernelComparison`. -/
theorem Modules.isIso_pullbackKernelComparison
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) {E F : X.Modules} (q : E ⟶ F) (hq : Epi q)
    (hE : E.IsQuasicoherent)
    (hfp : F.IsFinitePresentation) (hflat : CoherentSheafFlat f F)
    (hker : LineBundle.IsLocallyTrivial (Limits.kernel q)) :
    IsIso (Modules.pullbackKernelComparison g' q) := by
  haveI := hq
  exact Modules.isIso_pullbackKernelComparison_of_mono g' q
    (Modules.mono_pullback_map_kernel_ι sq q hq hE hfp hflat hker)

/-! ## §2. Families of relative effective divisors -/

variable {S X : Scheme.{u}}

/-- A **family of relative effective divisors on `X ×_S T / T`** (Kleiman §3
Def. `df:red`/`df:div`, in the quotient encoding — see the module docstring):
a `T`-flat, finitely presented quotient `q` of the structure sheaf of the
relative product `X_T = X ×_S T` with proper support, whose kernel ideal
`I = ker q` is invertible (`Scheme.LineBundle.IsLocallyTrivial`).  The
associated divisor is the schematic support `D` of `F = O_{X_T}/I = O_D`;
conversely a relative effective divisor `D ⊆ X_T` yields the family
`q : O_{X_T} ↠ O_D`.

The source of `q` is stated as the pullback of the unit module `O_X` along
the first projection — canonically isomorphic to `O_{X_T}` — verbatim the
`E`-slot of `Scheme.QuotFamily` at `E = O_X`, so the Quot-family base-change
lemmas and pseudofunctor-coherence functor laws apply unchanged.  The fields
`isFinitePresentation` and `properSupport` are automatic for divisors on a
`T`-proper `X_T` (the FGA regime); see the module docstring.

**NOTHING IN THIS PROJECT CONSTRUCTS A `DivFamily`** (`review-ajc`, 2026-07-29).
The converse direction described above — "a relative effective divisor `D ⊆ X_T`
yields the family `q : O_{X_T} ↠ O_D`" — is mathematics, not a declaration here:
there is no producer of this structure for any curve, any base, or any test
object, including the trivial one. Measured with the elaborator rather than by
grep: `exact?` on
`Nonempty (DivFamily C.hom (Over.mk (𝟙 (Spec (.of k)))))`, with the three curve
binders in scope, fails to close the goal.

Consequences a reader should carry downstream, since this type is the input of the
whole divisor-side development. Every statement quantified over a `DivFamily` is
*true but untested* — it has no instance to be wrong about, and a green build over
it is evidence about elaboration only. `Picard/IdentityComponent.lean` says so
explicitly at the one place it matters most (`ClassDegreePinned`'s acceptance test
`classDegree_ne_zero_of_exists_pos_fiberDeg`, whose degree-`d` family is a
*hypothesis* precisely because none can be supplied); this note exists so the fact
is visible at the definition too, and not only to a reader who reaches the degree
interface. Building the first producer is campaign milestone D1′ (`Picard/DivDegree.lean`
provides the degree slices *of the functor*, not a family). -/
structure DivFamily (π : X ⟶ S) (T : Over S) : Type (u + 1) where
  /-- The structure sheaf `O_D` of the divisor, as a quotient module on the
  relative product `X ×_S T`. -/
  F : (Limits.pullback π T.hom).Modules
  /-- `F` is finitely presented (automatic for an invertible ideal's
  quotient; kept to match the Quot-family shape). -/
  isFinitePresentation : F.IsFinitePresentation
  /-- `F = O_D` is flat over `T` — the divisor is a *relative* effective
  divisor (Kleiman §3 Def. `df:red`). -/
  flat : CoherentSheafFlat (pullback.snd π T.hom) F
  /-- The schematic support (the divisor `D` itself) is proper over `T`
  (automatic when `π` is proper; kept to match the Quot-family shape). -/
  properSupport : Modules.HasProperSupport (pullback.snd π T.hom) F
  /-- The quotient map `O_{X_T} ⟶ O_D` (source stated as the pulled-back
  unit, as in `QuotFamily` with `E = O_X`). -/
  q : (Scheme.Modules.pullback (pullback.fst π T.hom)).obj
      (SheafOfModules.unit X.ringCatSheaf) ⟶ F
  /-- The quotient map is an epimorphism. -/
  epi : Epi q
  /-- **The divisor condition** (Kleiman §3 Def. `df:red`): the kernel ideal
  `I = ker q` is invertible, i.e. locally trivial of rank one. -/
  kerLocallyTrivial : LineBundle.IsLocallyTrivial (Limits.kernel q)

namespace DivFamily

variable {π : X ⟶ S}

/-- Two families of divisors are **equivalent** when an isomorphism of the
target sheaves commutes with the quotient maps — equivalently, when
`ker q = ker q'` as subobjects of `O_{X_T}`, i.e. when they cut out the same
closed subscheme (same convention as `QuotFamily.Rel`). -/
def Rel {T : Over S} (x y : DivFamily π T) : Prop :=
  ∃ f : x.F ≅ y.F, x.q ≫ f.hom = y.q

lemma rel_refl {T : Over S} (x : DivFamily π T) : x.Rel x :=
  ⟨Iso.refl _, Category.comp_id _⟩

lemma rel_symm {T : Over S} {x y : DivFamily π T} (h : x.Rel y) : y.Rel x := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f.symm, by rw [Iso.symm_hom, Iso.comp_inv_eq]; exact hf.symm⟩

lemma rel_trans {T : Over S} {x y z : DivFamily π T}
    (h1 : x.Rel y) (h2 : y.Rel z) : x.Rel z := by
  obtain ⟨f, hf⟩ := h1; obtain ⟨g, hg⟩ := h2
  exact ⟨f ≪≫ g,
    (congrArg (x.q ≫ ·) (Iso.trans_hom f g)).trans <|
      (Category.assoc x.q f.hom g.hom).symm.trans <|
        (congrArg (· ≫ g.hom) hf).trans hg⟩

/-- The equivalence-of-families setoid. -/
instance setoid (π : X ⟶ S) (T : Over S) : Setoid (DivFamily π T) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

/-- The **pullback action** on a family of divisors along `ψ : T' ⟶ T` of
`Over S`: pull the sheaf and the quotient map back along
`quotBaseMap π ψ : X_{T'} ⟶ X_T`, matching the `O`-side through
`pullbackTriangleIso (quotBaseMap_fst π ψ)` — exactly
`QuotFamily.pullbackAlong` at `E = O_X`.  The divisor condition base-changes
by `Modules.pullback_kernel_isLocallyTrivial`
(`lem:relative_divisor_base_change`). -/
noncomputable def pullbackAlong {T T' : Over S} (ψ : T' ⟶ T)
    (x : DivFamily π T) : DivFamily π T' where
  F := (Scheme.Modules.pullback (quotBaseMap π ψ)).obj x.F
  isFinitePresentation :=
    Modules.pullback_isFinitePresentation _ x.F x.isFinitePresentation
  flat := fun {_} hU {_} hV e =>
    CoherentSheafFlat.of_isPullback (quotBaseSquare π ψ) x.F
      (letI := x.isFinitePresentation; inferInstance) x.flat hU hV e
  properSupport :=
    Modules.HasProperSupport.of_isPullback (quotBaseSquare π ψ) x.F
      x.isFinitePresentation x.properSupport
  q := (pullbackTriangleIso (quotBaseMap_fst π ψ)
      (SheafOfModules.unit X.ringCatSheaf)).inv ≫
    (Scheme.Modules.pullback (quotBaseMap π ψ)).map x.q
  epi :=
    @CategoryTheory.epi_comp _ _ _ _ _
      (pullbackTriangleIso (quotBaseMap_fst π ψ)
        (SheafOfModules.unit X.ringCatSheaf)).inv inferInstance
      ((Scheme.Modules.pullback (quotBaseMap π ψ)).map x.q)
      (@CategoryTheory.Functor.map_epi _ _ _ _
        (Scheme.Modules.pullback (quotBaseMap π ψ)) inferInstance _ _ x.q x.epi)
  kerLocallyTrivial :=
    LineBundle.IsLocallyTrivial.of_iso
      (kernelIsIsoComp
        (pullbackTriangleIso (quotBaseMap_fst π ψ)
          (SheafOfModules.unit X.ringCatSheaf)).inv
        ((Scheme.Modules.pullback (quotBaseMap π ψ)).map x.q)).symm
      (Modules.pullback_kernel_isLocallyTrivial (quotBaseSquare π ψ) x.q x.epi
        (pullback_isQuasicoherent_hom (pullback.fst π T.hom)
          (SheafOfModules.unit X.ringCatSheaf) inferInstance)
        x.isFinitePresentation x.flat x.kerLocallyTrivial)

/-- The pullback action respects the equivalence relation. -/
lemma pullbackAlong_rel {T T' : Over S} (ψ : T' ⟶ T)
    {x y : DivFamily π T} (h : x.Rel y) :
    (pullbackAlong ψ x).Rel (pullbackAlong ψ y) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨(Scheme.Modules.pullback (quotBaseMap π ψ)).mapIso f, ?_⟩
  change ((pullbackTriangleIso (quotBaseMap_fst π ψ)
        (SheafOfModules.unit X.ringCatSheaf)).inv ≫
      (Scheme.Modules.pullback (quotBaseMap π ψ)).map x.q) ≫
      (Scheme.Modules.pullback (quotBaseMap π ψ)).map f.hom
    = (pullbackTriangleIso (quotBaseMap_fst π ψ)
        (SheafOfModules.unit X.ringCatSheaf)).inv ≫
      (Scheme.Modules.pullback (quotBaseMap π ψ)).map y.q
  rw [Category.assoc, ← (Scheme.Modules.pullback (quotBaseMap π ψ)).map_comp]
  exact congrArg
    (fun m => (pullbackTriangleIso (quotBaseMap_fst π ψ)
        (SheafOfModules.unit X.ringCatSheaf)).inv ≫
      (Scheme.Modules.pullback (quotBaseMap π ψ)).map m) hf

end DivFamily

/-! ## §3. The relative-divisor functor -/

set_option backward.isDefEq.respectTransparency false in
/-- The **relative-divisor functor** `Div_{X/S}` (Kleiman §3 Def. `df:div`):
the contravariant functor `(Sch/S)ᵒᵖ ⥤ Type (u+1)` sending an `S`-scheme
`T → S` to the set of relative effective divisors on `X_T/T` — encoded as
equivalence classes of families of invertible-kernel quotients of `O_{X_T}`
(`Scheme.DivFamily`; two families are identified iff `ker q = ker q'`, i.e.
iff they cut out the same divisor) — and a morphism to the pullback of
families (`DivFamily.pullbackAlong`).  The identity and composition laws are
the pseudofunctor coherence laws of the module pullback, packaged as
`Scheme.Modules.pullback_id_app_coherence` and
`Scheme.Modules.pullback_comp_app_coherence_inv` in `QuotFunctorDef.lean`. -/
noncomputable def DivFunctor (π : X ⟶ S) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Quotient (DivFamily.setoid π T.unop)
  map {T T'} g := TypeCat.ofHom (Quotient.map (DivFamily.pullbackAlong g.unop)
    (fun _ _ h => DivFamily.pullbackAlong_rel g.unop h))
  map_id T := by
    ext z
    induction z using Quotient.ind with
    | _ x =>
      change Quotient.mk _ (DivFamily.pullbackAlong (𝟙 T.unop) x) = Quotient.mk _ x
      refine Quotient.sound ⟨(Scheme.Modules.pullbackCongr (quotBaseMap_id π T.unop)).app x.F ≪≫
        (Scheme.Modules.pullbackId _).app x.F, ?_⟩
      change ((pullbackTriangleIso (quotBaseMap_fst π (𝟙 T.unop))
            (SheafOfModules.unit X.ringCatSheaf)).inv ≫
          (Scheme.Modules.pullback (quotBaseMap π (𝟙 T.unop))).map x.q) ≫
          (Scheme.Modules.pullbackCongr (quotBaseMap_id π T.unop)).hom.app x.F ≫
          (Scheme.Modules.pullbackId _).hom.app x.F
        = x.q
      rw [Category.assoc,
        (Scheme.Modules.pullbackCongr (quotBaseMap_id π T.unop)).hom.naturality_assoc x.q,
        (Scheme.Modules.pullbackId _).hom.naturality x.q]
      have key := Scheme.Modules.pullback_id_app_coherence (quotBaseMap_id π T.unop)
        (quotBaseMap_fst π (𝟙 T.unop)) (SheafOfModules.unit X.ringCatSheaf)
      simp only [pullbackTriangleIso, Iso.trans_inv, Iso.app_inv, Category.assoc]
      rw [reassoc_of% key]
      rfl
  map_comp {T T' T''} g h := by
    ext z
    induction z using Quotient.ind with
    | _ x =>
      change Quotient.mk _ (DivFamily.pullbackAlong (h.unop ≫ g.unop) x)
        = Quotient.mk _ (DivFamily.pullbackAlong h.unop (DivFamily.pullbackAlong g.unop x))
      refine Quotient.sound
        ⟨(Scheme.Modules.pullbackCongr (quotBaseMap_comp π g.unop h.unop)).app x.F ≪≫
          ((Scheme.Modules.pullbackComp (quotBaseMap π h.unop) (quotBaseMap π g.unop)).app
            x.F).symm, ?_⟩
      change ((pullbackTriangleIso (quotBaseMap_fst π (h.unop ≫ g.unop))
            (SheafOfModules.unit X.ringCatSheaf)).inv ≫
          (Scheme.Modules.pullback (quotBaseMap π (h.unop ≫ g.unop))).map x.q) ≫
          (Scheme.Modules.pullbackCongr (quotBaseMap_comp π g.unop h.unop)).hom.app x.F ≫
          (Scheme.Modules.pullbackComp (quotBaseMap π h.unop) (quotBaseMap π g.unop)).inv.app
            x.F
        = (pullbackTriangleIso (quotBaseMap_fst π h.unop)
            (SheafOfModules.unit X.ringCatSheaf)).inv ≫
          (Scheme.Modules.pullback (quotBaseMap π h.unop)).map
            ((pullbackTriangleIso (quotBaseMap_fst π g.unop)
              (SheafOfModules.unit X.ringCatSheaf)).inv ≫
              (Scheme.Modules.pullback (quotBaseMap π g.unop)).map x.q)
      rw [Category.assoc,
        (Scheme.Modules.pullbackCongr (quotBaseMap_comp π g.unop h.unop)).hom.naturality_assoc
          x.q,
        (Scheme.Modules.pullbackComp (quotBaseMap π h.unop)
          (quotBaseMap π g.unop)).inv.naturality x.q]
      have key := Scheme.Modules.pullback_comp_app_coherence_inv
        (quotBaseMap π h.unop) (quotBaseMap π g.unop)
        (quotBaseMap_comp π g.unop h.unop) (pullback.fst π T.unop.hom)
        (quotBaseMap_fst π g.unop) (quotBaseMap_fst π (h.unop ≫ g.unop))
        (quotBaseMap_fst π h.unop) (SheafOfModules.unit X.ringCatSheaf)
      simp only [pullbackTriangleIso, Iso.trans_inv, Iso.app_inv, Category.assoc,
        Functor.map_comp]
      rw [reassoc_of% key]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rfl

end Scheme

end AlgebraicGeometry
