/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Albanese.RationalMapFunctionField
import AlgebraicJacobian.Albanese.PolePurity

/-!
# Milne Lemma 3.3, Substep 3: the spreading criterion for rational-map domains

Per `informal/m33-spec.md` (D4). The heart is the **abstract spreading
criterion** `Scheme.RationalMap.mem_domain_of_fromSpecStalk`: for a rational
map `F : Y ⤏ Z` of `S`-schemes out of an integral scheme with `Z` locally of
finite type over `S`, a point `P ∈ Y` lies in the domain of `F` as soon as
the generic morphism `Spec K(Y) ⟶ Z` of `F` factors through
`Spec 𝒪_{Y,P} ⟶ Z` compatibly with the structure morphisms. This rides on
Mathlib's spreading-out engine (`Scheme.PartialMap.ofFromSpecStalk`,
`spread_out_of_isGermInjective'`) and the germ-injectivity of integral
schemes.

Supporting API:

* `Scheme.isGermInjectiveAt_of_isIntegral` — integral schemes are
  germ-injective at every point (instance; feeds the spreading engine).
* `Scheme.Opens.fromSpecStalkOfMem_specializes`,
  `Scheme.PartialMap.fromSpecStalkOfMem_specializes` — the stalk-to-scheme
  morphisms of a partial map are compatible with specialisation inside the
  domain; this is what re-anchors the spread-out morphism at the generic
  point.

§2 corestriction (`mem_domain_of_forall_germ_mem_range`): if every section of
an affine open `V ∋ γ = F(η_Y)` has generic germ pullback `Λ s ∈ K(Y)` in the
range of `𝒪_{Y,P} ⟶ K(Y)`, then `P ∈ Dom F`. §3 is the easy converse
(`germ_stalkPullback_mem_range_of_mem_domain`, via the germ pullback
`Scheme.PartialMap.germPullback` at a point of definition), and §4 the
assembly-facing pole corollary
(`exists_germ_stalkPullback_notMem_range_of_notMem_domain`): where `F` is
undefined, some `Λ s` has a pole at a coheight-one specialisation (landed 4a
pole-divisor purity).

Blueprint reference: `lem:milne_codim1_indeterminacy` (Milne, *Abelian
Varieties*, §I.3 Lemma 3.3, pp. 17–18; `abelian-varieties:page-0023/0024`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace IsLocalRing

namespace AlgebraicGeometry

/-- **Integral schemes are germ-injective at every point**: any affine open
`U ∋ x` has `Γ(Y, U)` a domain and `Γ(Y, U) ⟶ 𝒪_{Y,x}` a localization map,
hence injective (`germ_injective_of_isIntegral`). Feeds Mathlib's
spreading-out engine (`spread_out_of_isGermInjective'`). -/
instance (priority := 100) Scheme.isGermInjectiveAt_of_isIntegral
    {Y : Scheme.{u}} [IsIntegral Y] (P : ↥Y) : Y.IsGermInjectiveAt P := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hPU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ P) isOpen_univ
  exact ⟨⟨U, hPU, hU, germ_injective_of_isIntegral Y P hPU⟩⟩

/-- The stalk-to-subscheme morphisms of an open are compatible with
specialisation: `Spec 𝒪_Q ⟶ Spec 𝒪_P ⟶ U` is `Spec 𝒪_Q ⟶ U` for `Q ⤳ P`
both in `U`. -/
lemma Scheme.Opens.fromSpecStalkOfMem_specializes
    {Y : Scheme.{u}} (U : Y.Opens) {P Q : ↥Y} (hsp : Q ⤳ P)
    (hP : P ∈ U) (hQ : Q ∈ U) :
    Spec.map (Y.presheaf.stalkSpecializes hsp) ≫ U.fromSpecStalkOfMem P hP
      = U.fromSpecStalkOfMem Q hQ := by
  rw [← cancel_mono U.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

/-- The stalk-to-target morphisms of a partial map are compatible with
specialisation inside the domain. -/
lemma Scheme.PartialMap.fromSpecStalkOfMem_specializes
    {Y Z : Scheme.{u}} (g : Y.PartialMap Z) {P Q : ↥Y} (hsp : Q ⤳ P)
    (hP : P ∈ g.domain) (hQ : Q ∈ g.domain) :
    Spec.map (Y.presheaf.stalkSpecializes hsp) ≫ g.fromSpecStalkOfMem hP
      = g.fromSpecStalkOfMem hQ := by
  change Spec.map (Y.presheaf.stalkSpecializes hsp)
      ≫ g.domain.fromSpecStalkOfMem P hP ≫ g.hom
    = g.domain.fromSpecStalkOfMem Q hQ ≫ g.hom
  rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_specializes g.domain hsp hP hQ]

/-- **The abstract spreading criterion.** Let `F : Y ⤏ Z` be a rational map
of `S`-schemes with `Y` integral and `Z` locally of finite type over `S`. If
the generic morphism `Spec K(Y) ⟶ Z` of `F` factors through a morphism
`φ : Spec 𝒪_{Y,P} ⟶ Z` compatible with the structure morphisms, then
`P ∈ Dom F` — `φ` spreads out to a partial map defined at `P` representing
`F` (Milne's "`Φ` is defined at `P` as soon as `𝒪_{G,e}` pulls back into
`𝒪_{Y,P}`", substep 3 of Lemma 3.3). -/
theorem Scheme.RationalMap.mem_domain_of_fromSpecStalk
    {Y Z S : Scheme.{u}} [IsIntegral Y] (qY : Y ⟶ S) (qZ : Z ⟶ S)
    [LocallyOfFiniteType qZ] (F : Y.RationalMap Z) (P : ↥Y)
    (φ : Spec (Y.presheaf.stalk P) ⟶ Z)
    (hcomp : φ ≫ qZ = Y.fromSpecStalk P ≫ qY)
    (hgen : Spec.map (Y.presheaf.stalkSpecializes (genericPoint_specializes P)) ≫ φ
      = F.fromFunctionField) :
    P ∈ F.domain := by
  set ψP := Scheme.PartialMap.ofFromSpecStalk qY qZ φ hcomp with hψdef
  have hPψ : P ∈ ψP.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk qY qZ φ hcomp
  -- The generic point lies in both domains.
  have hηψ : genericPoint ↥Y ∈ ψP.domain :=
    (genericPoint_specializes _).mem_open ψP.domain.2
      ψP.dense_domain.nonempty.choose_spec
  obtain ⟨g, hg⟩ := F.exists_rep
  have hηg : genericPoint ↥Y ∈ g.domain :=
    (genericPoint_specializes _).mem_open g.domain.2
      g.dense_domain.nonempty.choose_spec
  -- Both restrict to the generic morphism of `F` at the generic point.
  have hψη : ψP.fromSpecStalkOfMem hηψ = F.fromFunctionField := by
    have hφ : ψP.fromSpecStalkOfMem hPψ = φ :=
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk qY qZ φ hcomp
    rw [← Scheme.PartialMap.fromSpecStalkOfMem_specializes ψP
      (genericPoint_specializes P) hPψ hηψ, hφ, hgen]
  have hgη : g.fromSpecStalkOfMem hηg = F.fromFunctionField := by
    rw [← hg, Scheme.RationalMap.fromFunctionField_toRationalMap]
  -- Hence the spread-out partial map represents `F`, and `P` is in its domain.
  have hequiv : ψP.equiv g :=
    Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq ψP g hηψ hηg
      (hψη.trans hgη.symm)
  exact Scheme.RationalMap.mem_domain.mpr
    ⟨ψP, hPψ, (Scheme.PartialMap.toRationalMap_eq_iff.mpr hequiv).trans hg⟩

/-! ## §2. The germ-range criterion

The concrete form of substep 3: the generic germ pullback
`Λ = germ_γ ≫ stalkPullback F : Γ(Z, V) ⟶ K(Y)` of an affine open `V`
containing the generic image `γ` lands in `𝒪_{Y,P} ⊆ K(Y)` for all sections
iff `F` is defined at `P` (we prove the substantive "if" direction). -/

/-- The generic morphism of a rational map factors through any affine open
containing the generic image: `Spec.map (germ_γ ≫ stalkPullback) ≫ V.fromSpec`
is `F.fromFunctionField`. -/
lemma Scheme.RationalMap.specMap_germ_stalkPullback_fromSpec
    {Y Z : Scheme.{u}} [IsIntegral Y] (F : Y.RationalMap Z)
    {V : Z.Opens} (hV : IsAffineOpen V)
    (hγV : F.fromFunctionField (closedPoint Y.functionField) ∈ V) :
    Spec.map (Z.presheaf.germ V (F.fromFunctionField (closedPoint Y.functionField)) hγV
        ≫ F.stalkPullback) ≫ hV.fromSpec
      = F.fromFunctionField := by
  have hSP : F.stalkPullback = Scheme.stalkClosedPointTo F.fromFunctionField := rfl
  rw [Spec.map_comp, Category.assoc,
    show Spec.map (Z.presheaf.germ V
        (F.fromFunctionField (closedPoint Y.functionField)) hγV) ≫ hV.fromSpec
      = hV.fromSpecStalk hγV from rfl,
    IsAffineOpen.fromSpecStalk_eq_fromSpecStalk, hSP,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

/-- Routing a `Spec`-shaped morphism through an affine base: composing
`Spec.map ρ ≫ hU.fromSpec` with a structure morphism `q : W ⟶ S` into an
affine scheme is again `Spec`-shaped, with ring map `q.appLE ⊤ U _ ≫ ρ`. -/
lemma specMap_fromSpec_comp {W S : Scheme.{u}} [IsAffine S] (q : W ⟶ S)
    {U : W.Opens} (hU : IsAffineOpen U) {R : CommRingCat.{u}} (ρ : Γ(W, U) ⟶ R) :
    (Spec.map ρ ≫ hU.fromSpec) ≫ q
      = Spec.map (q.appLE ⊤ U (by simp) ≫ ρ) ≫ (isAffineOpen_top S).fromSpec := by
  rw [Spec.map_comp, Category.assoc, Category.assoc,
    IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top S) hU]

/-- **The germ-range spreading criterion (Milne 3.3, substep 3).** Let
`F : Y ⤏ Z` be a rational map of schemes over an affine base `S`, with `Y`
integral and `Z` locally of finite type over `S`, and let `V` be an affine
open of `Z` containing the generic image `γ = F(η_Y)`. If every section
`s ∈ Γ(Z, V)` has generic germ pullback `Λ s = germ_γ(s)|_η ∈ K(Y)` lying in
the image of `𝒪_{Y,P} ⟶ K(Y)`, then `F` is defined at `P`. -/
theorem Scheme.RationalMap.mem_domain_of_forall_germ_mem_range
    {Y Z S : Scheme.{u}} [IsIntegral Y] [IsAffine S] (qY : Y ⟶ S) (qZ : Z ⟶ S)
    [LocallyOfFiniteType qZ] (F : Y.RationalMap Z)
    (hFover : F.fromFunctionField ≫ qZ
      = Y.fromSpecStalk (genericPoint ↥Y) ≫ qY)
    {V : Z.Opens} (hV : IsAffineOpen V)
    (hγV : F.fromFunctionField (closedPoint Y.functionField) ∈ V) (P : ↥Y)
    (H : ∀ s : Γ(Z, V),
      (Z.presheaf.germ V (F.fromFunctionField (closedPoint Y.functionField)) hγV
        ≫ F.stalkPullback) s
      ∈ (algebraMap (Y.presheaf.stalk P) Y.functionField).range) :
    P ∈ F.domain := by
  have hinj : Function.Injective (algebraMap (Y.presheaf.stalk P) Y.functionField) :=
    IsFractionRing.injective _ _
  -- The corestriction `α : Γ(Z, V) ⟶ 𝒪_{Y,P}` of the germ pullback through the
  -- stalk range, packaged existentially so that all later rewriting happens on
  -- an opaque variable.
  obtain ⟨α, hα⟩ : ∃ α : Γ(Z, V) ⟶ Y.presheaf.stalk P,
      α ≫ CommRingCat.ofHom (algebraMap (Y.presheaf.stalk P) Y.functionField)
        = Z.presheaf.germ V (F.fromFunctionField (closedPoint Y.functionField)) hγV
          ≫ F.stalkPullback := by
    let e : (Y.presheaf.stalk P) ≃+*
        ((algebraMap (Y.presheaf.stalk P) Y.functionField).range) :=
      RingEquiv.ofBijective
        (algebraMap (Y.presheaf.stalk P) Y.functionField).rangeRestrict
        ⟨fun a b h => hinj (by simpa using congrArg Subtype.val h),
          (algebraMap (Y.presheaf.stalk P) Y.functionField).rangeRestrict_surjective⟩
    refine ⟨CommRingCat.ofHom (e.symm.toRingHom.comp
      ((Z.presheaf.germ V (F.fromFunctionField (closedPoint Y.functionField)) hγV
        ≫ F.stalkPullback).hom.codRestrict _ H)), ?_⟩
    ext s
    exact congrArg Subtype.val (e.apply_symm_apply ⟨_, H s⟩)
  -- The canonical map `𝒪_{Y,P} ⟶ K(Y)` is the stalk-specialisation map.
  have hspec : Y.presheaf.stalkSpecializes (genericPoint_specializes P)
      = CommRingCat.ofHom (algebraMap (Y.presheaf.stalk P) Y.functionField) := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  -- Property 1: the generic factorisation.
  have hgen : Spec.map (Y.presheaf.stalkSpecializes (genericPoint_specializes P))
      ≫ Spec.map α ≫ hV.fromSpec = F.fromFunctionField := by
    have e2 : α ≫ Y.presheaf.stalkSpecializes (genericPoint_specializes P)
        = Z.presheaf.germ V (F.fromFunctionField (closedPoint Y.functionField)) hγV
          ≫ F.stalkPullback := by
      rw [hspec]; exact hα
    calc Spec.map (Y.presheaf.stalkSpecializes (genericPoint_specializes P))
        ≫ Spec.map α ≫ hV.fromSpec
        = Spec.map (α ≫ Y.presheaf.stalkSpecializes (genericPoint_specializes P))
            ≫ hV.fromSpec := by
          rw [← Category.assoc, ← Spec.map_comp]
      _ = Spec.map (Z.presheaf.germ V
              (F.fromFunctionField (closedPoint Y.functionField)) hγV
            ≫ F.stalkPullback) ≫ hV.fromSpec :=
          congrArg (Spec.map · ≫ hV.fromSpec) e2
      _ = F.fromFunctionField :=
          Scheme.RationalMap.specMap_germ_stalkPullback_fromSpec F hV hγV
  -- Property 2: compatibility over the affine base.
  have hcomp : (Spec.map α ≫ hV.fromSpec) ≫ qZ = Y.fromSpecStalk P ≫ qY := by
    obtain ⟨_, ⟨U', hU', rfl⟩, hPU', -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ P) isOpen_univ
    have hηU' : genericPoint ↥Y ∈ U' :=
      (genericPoint_specializes P).mem_open U'.2 hPU'
    -- The generic-point identity, from the over-compatibility of `F`.
    have h5 : Spec.map (qZ.appLE ⊤ V (by simp)
          ≫ (Z.presheaf.germ V (F.fromFunctionField (closedPoint Y.functionField)) hγV
            ≫ F.stalkPullback)) ≫ (isAffineOpen_top S).fromSpec
        = Spec.map (qY.appLE ⊤ U' (by simp)
            ≫ Y.presheaf.germ U' (genericPoint ↥Y) hηU')
          ≫ (isAffineOpen_top S).fromSpec := by
      rw [← specMap_fromSpec_comp qZ hV,
        ← specMap_fromSpec_comp qY hU' (Y.presheaf.germ U' (genericPoint ↥Y) hηU'),
        Scheme.RationalMap.specMap_germ_stalkPullback_fromSpec F hV hγV,
        show Spec.map (Y.presheaf.germ U' (genericPoint ↥Y) hηU') ≫ hU'.fromSpec
          = Y.fromSpecStalk (genericPoint ↥Y) from
          (show Spec.map (Y.presheaf.germ U' _ hηU') ≫ hU'.fromSpec
            = hU'.fromSpecStalk hηU' from rfl).trans
            (IsAffineOpen.fromSpecStalk_eq_fromSpecStalk hU' hηU'), hFover]
    have h6 : qZ.appLE ⊤ V (by simp)
          ≫ (Z.presheaf.germ V (F.fromFunctionField (closedPoint Y.functionField)) hγV
            ≫ F.stalkPullback)
        = qY.appLE ⊤ U' (by simp) ≫ Y.presheaf.germ U' (genericPoint ↥Y) hηU' :=
      Spec.map_injective ((cancel_mono _).mp h5)
    have hg2 : Y.presheaf.germ U' P hPU'
          ≫ Y.presheaf.stalkSpecializes (genericPoint_specializes P)
        = Y.presheaf.germ U' (genericPoint ↥Y) hηU' :=
      Y.presheaf.germ_stalkSpecializes hPU' (genericPoint_specializes P)
    -- The ring-level identity at `P`, by cancelling the injective `𝒪_P ⟶ K(Y)`.
    haveI : Mono (CommRingCat.ofHom
        (algebraMap (Y.presheaf.stalk P) Y.functionField)) :=
      ConcreteCategory.mono_of_injective _ hinj
    have hRG : qZ.appLE ⊤ V (by simp) ≫ α
        = qY.appLE ⊤ U' (by simp) ≫ Y.presheaf.germ U' P hPU' := by
      refine (cancel_mono (CommRingCat.ofHom
        (algebraMap (Y.presheaf.stalk P) Y.functionField))).mp ?_
      calc (qZ.appLE ⊤ V (by simp) ≫ α)
            ≫ CommRingCat.ofHom (algebraMap (Y.presheaf.stalk P) Y.functionField)
          = qZ.appLE ⊤ V (by simp) ≫ (α ≫ CommRingCat.ofHom
              (algebraMap (Y.presheaf.stalk P) Y.functionField)) :=
            Category.assoc _ _ _
        _ = qZ.appLE ⊤ V (by simp)
              ≫ (Z.presheaf.germ V
                  (F.fromFunctionField (closedPoint Y.functionField)) hγV
                ≫ F.stalkPullback) := whisker_eq _ hα
        _ = qY.appLE ⊤ U' (by simp)
              ≫ Y.presheaf.germ U' (genericPoint ↥Y) hηU' := h6
        _ = qY.appLE ⊤ U' (by simp)
              ≫ (Y.presheaf.germ U' P hPU'
                ≫ Y.presheaf.stalkSpecializes (genericPoint_specializes P)) :=
            whisker_eq _ hg2.symm
        _ = qY.appLE ⊤ U' (by simp)
              ≫ (Y.presheaf.germ U' P hPU'
                ≫ CommRingCat.ofHom
                  (algebraMap (Y.presheaf.stalk P) Y.functionField)) :=
            whisker_eq _ (whisker_eq _ hspec)
        _ = (qY.appLE ⊤ U' (by simp) ≫ Y.presheaf.germ U' P hPU')
              ≫ CommRingCat.ofHom
                (algebraMap (Y.presheaf.stalk P) Y.functionField) :=
            (Category.assoc _ _ _).symm
    -- Assemble.
    calc (Spec.map α ≫ hV.fromSpec) ≫ qZ
        = Spec.map (qZ.appLE ⊤ V (by simp) ≫ α)
            ≫ (isAffineOpen_top S).fromSpec := specMap_fromSpec_comp qZ hV α
      _ = Spec.map (qY.appLE ⊤ U' (by simp) ≫ Y.presheaf.germ U' P hPU')
            ≫ (isAffineOpen_top S).fromSpec :=
          congrArg (Spec.map · ≫ (isAffineOpen_top S).fromSpec) hRG
      _ = (Spec.map (Y.presheaf.germ U' P hPU') ≫ hU'.fromSpec) ≫ qY :=
          (specMap_fromSpec_comp qY hU' (Y.presheaf.germ U' P hPU')).symm
      _ = Y.fromSpecStalk P ≫ qY :=
          congrArg (· ≫ qY)
            ((show Spec.map (Y.presheaf.germ U' P hPU') ≫ hU'.fromSpec
                = hU'.fromSpecStalk hPU' from rfl).trans
              (IsAffineOpen.fromSpecStalk_eq_fromSpecStalk hU' hPU'))
  exact Scheme.RationalMap.mem_domain_of_fromSpecStalk qY qZ F P
    (Spec.map α ≫ hV.fromSpec) hcomp hgen

/-! ## §3. The converse: definedness gives germ-range membership (3-easy)

If a representative `g` of `F` is defined at `Q` with value `g(Q) ∈ V`, the
generic germ pullback of every section of `V` is regular at `Q`: it factors
through `𝒪_{Y,Q}` by the germ-at-the-value pullback of `g` at `Q`. -/

/-- The germ pullback of a partial map at a point `Q` of its domain: the germ
of a section of `V ∋ g(Q)` at the value `g(Q)`, pulled back through the stalk
map of `g` and the stalk isomorphism of the domain inclusion. This is the
`𝒪_{Y,Q}`-valued corestriction of the generic germ pullback `Λ`
(see `germ_stalkPullback_mem_range_of_mem_domain`). -/
noncomputable def Scheme.PartialMap.germPullback
    {Y Z : Scheme.{u}} (g : Y.PartialMap Z) {V : Z.Opens} {Q : ↥Y}
    (hQg : Q ∈ g.domain) (hQV : g.hom.base ⟨Q, hQg⟩ ∈ V) :
    Γ(Z, V) ⟶ Y.presheaf.stalk Q :=
  -- the inverse stalk map is bound at its natural type first: elaborating it
  -- directly inside the composite stalls the `IsIso` instance under the
  -- expected-type unification `ι(⟨Q, hQg⟩) ≡ Q`
  let ν : (g.domain.toScheme).presheaf.stalk ⟨Q, hQg⟩ ⟶
      Y.presheaf.stalk (g.domain.ι.base ⟨Q, hQg⟩) :=
    inv (g.domain.ι.stalkMap ⟨Q, hQg⟩)
  Z.presheaf.germ V (g.hom.base ⟨Q, hQg⟩) hQV ≫ g.hom.stalkMap ⟨Q, hQg⟩ ≫ ν

/-- `Spec` of the germ pullback of `g` at `Q`, composed into the target through
the affine open `V`, is the stalk-to-scheme morphism `Spec 𝒪_{Y,Q} ⟶ Z` of the
partial map `g` at `Q`. -/
lemma Scheme.PartialMap.specMap_germPullback_fromSpec
    {Y Z : Scheme.{u}} (g : Y.PartialMap Z) {V : Z.Opens} (hV : IsAffineOpen V)
    {Q : ↥Y} (hQg : Q ∈ g.domain) (hQV : g.hom.base ⟨Q, hQg⟩ ∈ V) :
    Spec.map (g.germPullback hQg hQV) ≫ hV.fromSpec = g.fromSpecStalkOfMem hQg := by
  change Spec.map (Z.presheaf.germ V (g.hom.base ⟨Q, hQg⟩) hQV ≫ g.hom.stalkMap ⟨Q, hQg⟩
      ≫ inv (g.domain.ι.stalkMap ⟨Q, hQg⟩)) ≫ hV.fromSpec
    = g.fromSpecStalkOfMem hQg
  rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    show Spec.map (Z.presheaf.germ V (g.hom.base ⟨Q, hQg⟩) hQV) ≫ hV.fromSpec
      = hV.fromSpecStalk hQV from rfl,
    IsAffineOpen.fromSpecStalk_eq_fromSpecStalk hV hQV,
    Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc]
  rfl

/-- **The corestriction identity.** The germ pullback of `g` at a domain point
`Q` with `g(Q) ∈ V`, composed with the canonical `𝒪_{Y,Q} ⟶ K(Y)`, is the
generic germ pullback `Λ` of the rational map represented by `g`. -/
lemma Scheme.PartialMap.germPullback_stalkSpecializes
    {Y Z : Scheme.{u}} [IsIntegral Y] (g : Y.PartialMap Z)
    {V : Z.Opens} (hV : IsAffineOpen V)
    {Q : ↥Y} (hQg : Q ∈ g.domain) (hQV : g.hom.base ⟨Q, hQg⟩ ∈ V)
    (hγV : g.toRationalMap.fromFunctionField (closedPoint Y.functionField) ∈ V) :
    g.germPullback hQg hQV
        ≫ Y.presheaf.stalkSpecializes (genericPoint_specializes Q)
      = Z.presheaf.germ V
          (g.toRationalMap.fromFunctionField (closedPoint Y.functionField)) hγV
        ≫ g.toRationalMap.stalkPullback := by
  have hηg : genericPoint ↥Y ∈ g.domain :=
    (genericPoint_specializes _).mem_open g.domain.2
      g.dense_domain.nonempty.choose_spec
  apply Spec.map_injective
  rw [← cancel_mono hV.fromSpec, Spec.map_comp, Category.assoc,
    Scheme.PartialMap.specMap_germPullback_fromSpec g hV hQg hQV,
    Scheme.PartialMap.fromSpecStalkOfMem_specializes g (genericPoint_specializes Q)
      hQg hηg,
    Scheme.RationalMap.specMap_germ_stalkPullback_fromSpec g.toRationalMap hV hγV,
    Scheme.RationalMap.fromFunctionField_toRationalMap]

/-- **Definedness gives germ-range membership (Milne 3.3, substep 3-easy).**
If a representative `g` of the rational map `F : Y ⤏ Z` is defined at `Q` with
value `g(Q) ∈ V`, then the generic germ pullback `Λ s ∈ K(Y)` of every section
`s ∈ Γ(Z, V)` lies in the image of `𝒪_{Y,Q} ⟶ K(Y)` — namely, `Λ s` is the
image of the germ pullback of `s` at `g(Q)`. Consumed by the 4b-transport at
`Q = δ(z)` with value `Φ₀(δ(z)) = e ∈ V` (spec D5(d)). -/
theorem Scheme.RationalMap.germ_stalkPullback_mem_range_of_mem_domain
    {Y Z : Scheme.{u}} [IsIntegral Y] (F : Y.RationalMap Z)
    {V : Z.Opens} (hV : IsAffineOpen V)
    (hγV : F.fromFunctionField (closedPoint Y.functionField) ∈ V)
    (g : Y.PartialMap Z) (hg : g.toRationalMap = F)
    {Q : ↥Y} (hQg : Q ∈ g.domain) (hQV : g.hom.base ⟨Q, hQg⟩ ∈ V)
    (s : Γ(Z, V)) :
    (Z.presheaf.germ V (F.fromFunctionField (closedPoint Y.functionField)) hγV
        ≫ F.stalkPullback) s
      ∈ (algebraMap (Y.presheaf.stalk Q) Y.functionField).range := by
  subst hg
  have hspec : Y.presheaf.stalkSpecializes (genericPoint_specializes Q)
      = CommRingCat.ofHom (algebraMap (Y.presheaf.stalk Q) Y.functionField) := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  refine RingHom.mem_range.mpr ⟨g.germPullback hQg hQV s, ?_⟩
  calc algebraMap (Y.presheaf.stalk Q) Y.functionField (g.germPullback hQg hQV s)
      = (g.germPullback hQg hQV
          ≫ Y.presheaf.stalkSpecializes (genericPoint_specializes Q)) s := by
        rw [hspec, CommRingCat.comp_apply, CommRingCat.ofHom_apply]
    _ = (Z.presheaf.germ V
            (g.toRationalMap.fromFunctionField (closedPoint Y.functionField)) hγV
          ≫ g.toRationalMap.stalkPullback) s := by
        rw [Scheme.PartialMap.germPullback_stalkSpecializes g hV hQg hQV hγV]

/-! ## §4. The pole corollary

The assembly-facing contrapositive: if `F` is undefined at `P`, some section
of `V` has generic germ pullback with a pole at a coheight-one point
specialising to `P` (landed 4a pole-divisor purity). -/

/-- **The pole-existence corollary (substep 3 + landed 4a).** Let `F : Y ⤏ Z`
be a rational map over an affine base with `Y` integral, locally Noetherian
and with regular stalks, `Z` locally of finite type over the base, and `V` an
affine open of `Z` containing the generic image. If `F` is **not** defined at
`P`, then some section `s ∈ Γ(Z, V)` has generic germ pullback `Λ s ∈ K(Y)`
that is non-regular at a coheight-one point `w ⤳ P`. -/
theorem Scheme.RationalMap.exists_germ_stalkPullback_notMem_range_of_notMem_domain
    {Y Z S : Scheme.{u}} [IsIntegral Y] [IsAffine S] [IsLocallyNoetherian Y]
    (hreg : ∀ y : ↥Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (qY : Y ⟶ S) (qZ : Z ⟶ S) [LocallyOfFiniteType qZ] (F : Y.RationalMap Z)
    (hFover : F.fromFunctionField ≫ qZ
      = Y.fromSpecStalk (genericPoint ↥Y) ≫ qY)
    {V : Z.Opens} (hV : IsAffineOpen V)
    (hγV : F.fromFunctionField (closedPoint Y.functionField) ∈ V)
    (P : ↥Y) (hP : P ∉ F.domain) :
    ∃ s : Γ(Z, V), ∃ w : ↥Y, w ⤳ P ∧ Order.coheight w = 1 ∧
      (Z.presheaf.germ V (F.fromFunctionField (closedPoint Y.functionField)) hγV
          ≫ F.stalkPullback) s
        ∉ (algebraMap (Y.presheaf.stalk w) Y.functionField).range := by
  have hne : ¬ ∀ s : Γ(Z, V),
      (Z.presheaf.germ V (F.fromFunctionField (closedPoint Y.functionField)) hγV
          ≫ F.stalkPullback) s
        ∈ (algebraMap (Y.presheaf.stalk P) Y.functionField).range := fun H =>
    hP (Scheme.RationalMap.mem_domain_of_forall_germ_mem_range qY qZ F hFover
      hV hγV P H)
  push Not at hne
  obtain ⟨s, hs⟩ := hne
  obtain ⟨w, hwP, hcw, hw⟩ :=
    Scheme.exists_specializes_coheight_eq_one_of_notMem_stalk_range Y hreg P _ hs
  exact ⟨s, w, hwP, hcw, hw⟩

end AlgebraicGeometry
