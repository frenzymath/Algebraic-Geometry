/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Std.Tactic.BVDecide.LRAT.Internal.Clause

/-!
# Relative spectrum of a quasi-coherent sheaf of algebras (A.1.a)

This file constructs the relative spectrum from Mathlib's affine-Zariski gluing data. A
`QcohAlgebra X` consists of a sheaf of commutative rings, an `O_X`-algebra unit, and the
`NatTrans.Coequifibered` localization condition consumed by
`Scheme.AffineZariskiSite.relativeGluingData`.

The construction provides:

* `Scheme.RelativeSpec` and `RelativeSpec.structureMorphism`;
* affineness of the structure morphism and of the total space over an affine base;
* an explicit algebra reconstructed from a base-changed relative spectrum;
* a canonical isomorphism between that spectrum and the scheme-theoretic pullback;
* the object assignment from quasi-coherent algebras to schemes over the base.

## References

Blueprint: `blueprint/src/chapters/Picard_RelativeSpec.tex`.
Stacks Project, tags 01LL (situation), 01LO (affine-base case), 01LQ (existence +
universal property), 01LR (definition + functoriality), 01LS (base change).
Hartshorne, *Algebraic Geometry*, II Exercise 5.17.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-! ## §1. Quasi-coherent sheaves of `O_X`-algebras

For a scheme `X`, a quasi-coherent sheaf of `O_X`-algebras is a sheaf of
`O_X`-algebras whose underlying `O_X`-module is quasi-coherent. Stacks tag
01LL packages the notion as a sheaf $\mathcal{A}$ on $X$ taking values in
commutative rings together with a unit map from the structure sheaf
$\mathcal{O}_X$, plus the quasi-coherence requirement.

We use the `Coequifibered` formulation: on every affine open `U` and section `f`,
restriction to the basic open `D(f)` is an `IsLocalization.Away f`. This is the
condition required by Mathlib's relative-gluing construction.

Blueprint reference: `def:qc_sheaf_of_algebras` (Stacks 01LL,
situation-relative-spec). -/

/-- A **quasi-coherent sheaf of `O_X`-algebras** in the form used by Mathlib's
relative-gluing construction.

A triple of
- `sheaf` : a sheaf of commutative rings on the underlying topological space
  of `X`,
- `unit` : an `O_X`-algebra unit, i.e. a morphism of sheaves of commutative
  rings `X.sheaf ⟶ sheaf` from the structure sheaf to the carrier, and
- `coequifibered` : the Stacks-01LL form of quasi-coherence — every
  restriction of `sheaf` to a basic-open `D(f) ⊆ U` is the
  `IsLocalization.Away f` of `sheaf U`. This is the exact predicate
  consumed by `Scheme.AffineZariskiSite.relativeGluingData`
  (`Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean:293`).

The shape matches the input of Mathlib's relative-gluing construction
verbatim, so `RelativeSpec` is defined directly as
`(relativeGluingData 𝒜.coequifibered).glued`. -/
structure QcohAlgebra (X : Scheme.{u}) where
  /-- The underlying sheaf of commutative rings on `X`. -/
  sheaf : TopCat.Sheaf CommRingCat.{u} X.toPresheafedSpace
  /-- The `O_X`-algebra unit `X.sheaf ⟶ sheaf` exhibiting `sheaf` as a sheaf
  of `O_X`-algebras. -/
  unit : X.sheaf ⟶ sheaf
  /-- **Stacks 01LL quasi-coherence overlay (`Coequifibered` form)**: every
  restriction of `sheaf` to a basic-open `D(f) ⊆ U` is `IsLocalization.Away f`.
  This is the exact predicate consumed by `AffineZariskiSite.relativeGluingData`. -/
  coequifibered : NatTrans.Coequifibered
    (Functor.whiskerLeft (AffineZariskiSite.toOpensFunctor X).op unit.hom)

namespace RelativeSpec

/-! ## §2. The relative-spectrum scheme

The construction proceeds affine-locally: on an affine open `U = Spec R ⊆ X` we
set `π⁻¹(U) := Spec(𝒜(U))`, where `𝒜(U)` is regarded as an `R`-algebra. The local
pieces glue compatibly because `𝒜` is quasi-coherent (the transition isomorphism
`𝒜(U) ⊗_R S ≅ 𝒜(V)` for `V = Spec S ⊆ U` gives an open immersion of the
corresponding Specs).

Blueprint reference: `thm:relative_spec_exists` (Stacks 01LQ,
`lemma-glue-relative-spec`). -/

end RelativeSpec

/-- The **relative spectrum** scheme `Spec_X(𝒜)` of a quasi-coherent sheaf of
`O_X`-algebras `𝒜`.

It is the glued scheme of `AffineZariskiSite.relativeGluingData 𝒜.coequifibered`,
whose affine pieces are `Spec(𝒜(U))`. -/
noncomputable def RelativeSpec {X : Scheme.{u}} (𝒜 : X.QcohAlgebra) : Scheme.{u} :=
  (AffineZariskiSite.relativeGluingData 𝒜.coequifibered).glued

/-- The **structure morphism** `π : Spec_X(𝒜) → X`, obtained by descending the affine-local
maps `Spec(𝒜(U)) → U`. -/
noncomputable def RelativeSpec.structureMorphism {X : Scheme.{u}}
    (𝒜 : X.QcohAlgebra) : X.RelativeSpec 𝒜 ⟶ X :=
  (AffineZariskiSite.relativeGluingData 𝒜.coequifibered).toBase

/-! ### Algebra reconstructed from a base-changed relative spectrum

Given a morphism `g : T ⟶ X` and a quasi-coherent `O_X`-algebra `𝒜`, the
pulled-back qcoh algebra `g^* 𝒜 : T.QcohAlgebra` is realised as the
pushforward of the structure sheaf of the relative-spec pullback. The
`sheaf` and `unit` fields are concrete (the topological pushforward of the
pullback's structure sheaf and the canonical natural transformation `q.c`
respectively, where `q := pullback.fst g (structureMorphism 𝒜)`). The
`coequifibered` field records that pushforward along the affine projection preserves the
Stacks-01LL localization condition: `q` is affine via
`MorphismProperty.pullback_fst` applied to `UniversalProperty 𝒜`, so on
every affine `U ⊆ T` with section `f ∈ Γ(T, U)` we have
`Γ(P, q⁻¹(D(f))) = Γ(P, q⁻¹U)[1/q.app f]`, i.e. the basic-open restriction
of the pushforward is the relevant `IsLocalization.Away`. The two facts are packaged by
`QcohAlgebra.pullback_fst_isAffineHom` and `QcohAlgebra.pullback_coequifibered`. -/

namespace RelativeSpec

/-! ## §3. Universal property — affine structure morphism

The Stacks 01LQ universal property says `Spec_X(𝒜)` represents the functor
sending an `X`-scheme `g : T → X` to the set of `O_X`-algebra maps
`𝒜 → g_* O_T`. A direct structural consequence of representability is that the
relative-spectrum structure morphism `π : Spec_X(𝒜) → X` is affine (Stacks 01LR,
`lemma-spec-properties`). The theorem below records this structural consequence.

Blueprint reference: `thm:relative_spec_univ` (Stacks 01LQ lemma-spec). -/

/-- **Universal property of the relative spectrum (affine-structure form).**

The structure morphism `π : Spec_X(𝒜) → X` of the relative spectrum is affine.
This is the substantive consequence of the Stacks 01LQ representability
statement (an `X`-scheme is the relative spectrum of some quasi-coherent
algebra iff its structure morphism is affine). -/
theorem UniversalProperty {X : Scheme.{u}} (𝒜 : X.QcohAlgebra) :
    IsAffineHom (RelativeSpec.structureMorphism 𝒜) := by
  -- For each `x : X`, choose an affine open `U` containing it
  -- pick an affine open `U ∋ x` (every `X` has such by `exists_isAffineOpen_mem_and_subset`),
  -- and identify the structure-morphism preimage of `U` with the range of the colimit
  -- inclusion of the affine fiber `Spec(𝒜(U))` (via
  -- `Cover.RelativeGluingData.toBase_preimage_eq_opensRange_ι`); affineness of the
  -- opens-range then follows from `isAffineOpen_opensRange` since the source is
  -- `Scheme.Spec` of `𝒜.sheaf.val.obj (op U)`, an affine scheme.
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro x
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (Set.mem_univ x)
  refine ⟨U, hxU, hU, ?_⟩
  set d := AffineZariskiSite.relativeGluingData 𝒜.coequifibered
  let i : X.AffineZariskiSite := ⟨U, hU⟩
  change IsAffineOpen (d.toBase ⁻¹ᵁ U)
  have key : d.toBase ⁻¹ᵁ U = (d.cover.f i).opensRange := by
    have h := d.toBase_preimage_eq_opensRange_ι i
    simp only [Scheme.Opens.opensRange_ι] at h
    exact h
  rw [key]
  have : IsAffine (d.cover.X i) := by
    change IsAffine (Scheme.Spec.obj _)
    infer_instance
  exact isAffineOpen_opensRange _

/-! ## §4. Affine base case

When the base `X = Spec R` is affine, `Spec_X(𝒜)` reduces to the absolute
spectrum of the global sections: `Spec_X(𝒜) ≅ Spec(Γ(X, 𝒜))`. The substantive
consequence formalized here is that the relative spectrum is affine. This is
Stacks 01LO, `lemma-spec-affine`.

Blueprint reference: `thm:relative_spec_affine_base`. -/

/-- **Affine-base reduction of the relative spectrum.**

For an affine scheme `X = Spec R` and a quasi-coherent `O_X`-algebra `𝒜`,
the relative spectrum `Spec_X(𝒜)` is itself an affine scheme. -/
theorem affine_base_iff {R : CommRingCat.{u}} (𝒜 : (Spec R).QcohAlgebra) :
    IsAffine ((Spec R).RelativeSpec 𝒜) := by
  -- Affineness of the relative-spec total space when the base is affine is the
  -- standard "affine over affine is affine" consequence: by
  -- `UniversalProperty` the structure morphism is `IsAffineHom`, and `Spec R`
  -- is itself `IsAffine`, so `isAffine_of_isAffineHom` closes the goal.
  have h : IsAffineHom (RelativeSpec.structureMorphism 𝒜) := UniversalProperty 𝒜
  exact isAffine_of_isAffineHom (RelativeSpec.structureMorphism 𝒜)

end RelativeSpec

/-! ## §4.5 Helpers for the reconstructed algebra

Two named helpers feeding the `coequifibered` field of the `QcohAlgebra.pullback`
constructor below. -/

/-- **Affineness of the structural pullback projection.**

Given `g : T ⟶ X` and `𝒜 : X.QcohAlgebra`, the projection
`q := pullback.fst g (structureMorphism 𝒜) : (T ×_X Spec_X(𝒜)) ⟶ T` is an affine
morphism. Combined with `RelativeSpec.UniversalProperty 𝒜` (which exhibits the
relative-spec structure morphism as affine) and the fact that affineness is
stable under base change (`MorphismProperty.pullback_fst` on `@isAffineHom`),
this is purely an instance derivation. -/
lemma QcohAlgebra.pullback_fst_isAffineHom {X T : Scheme.{u}} (g : T ⟶ X)
    (𝒜 : X.QcohAlgebra) :
    IsAffineHom (CategoryTheory.Limits.pullback.fst g
      (RelativeSpec.structureMorphism 𝒜)) := by
  haveI : IsAffineHom (RelativeSpec.structureMorphism 𝒜) :=
    RelativeSpec.UniversalProperty 𝒜
  exact MorphismProperty.pullback_fst _ _ inferInstance

/-- **Stacks 01LL Coequifibered overlay for the pushforward of `O_P` along an
affine `q : P ⟶ T`.**

Per the Mathlib characterization
`Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway`, the
claim reduces to: for every affine open `U ⊆ T` and section `r : Γ(T, U.1)`,
the basic-open restriction `q_* O_P (D(r)) = Γ(P, q⁻¹(D(r)))` is the
`IsLocalization.Away` of `q.app r` over `Γ(P, q⁻¹U)`. The named helper
`pullback_fst_isAffineHom` exhibits `q` as affine, so every preimage
`q⁻¹U` of an affine open `U` is itself affine; combined with
`Scheme.Hom.preimage_basicOpen` (which identifies `q⁻¹(T.basicOpen r)` with
`P.basicOpen (q.app U.1 r)`), `IsAffineOpen.isLocalization_of_eq_basicOpen`
supplies the localization with the desired algebra structure (restriction
along the inclusion `q⁻¹(U.basicOpen r) ⊆ q⁻¹U` induced by
`q.preimage_mono` on the AffineZariski-site inclusion). -/
lemma QcohAlgebra.pullback_coequifibered {X T : Scheme.{u}} (g : T ⟶ X)
    (𝒜 : X.QcohAlgebra) :
    NatTrans.Coequifibered ((AffineZariskiSite.toOpensFunctor T).op.whiskerLeft
      ({ hom := (CategoryTheory.Limits.pullback.fst g
            (RelativeSpec.structureMorphism 𝒜)).c } :
        T.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u}
          (CategoryTheory.Limits.pullback.fst g
            (RelativeSpec.structureMorphism 𝒜)).base).obj
          (CategoryTheory.Limits.pullback g
            (RelativeSpec.structureMorphism 𝒜)).sheaf).hom) := by
  haveI : IsAffineHom (CategoryTheory.Limits.pullback.fst g
      (RelativeSpec.structureMorphism 𝒜)) :=
    QcohAlgebra.pullback_fst_isAffineHom g 𝒜
  refine AlgebraicGeometry.Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mpr
    fun U r => ?_
  set q := CategoryTheory.Limits.pullback.fst g (RelativeSpec.structureMorphism 𝒜)
  have hqU : IsAffineOpen (q ⁻¹ᵁ U.1) := U.2.preimage q
  have hle : (U.basicOpen r).toOpens ≤ U.toOpens := T.basicOpen_le r
  exact hqU.isLocalization_of_eq_basicOpen (q.app U.1 r)
    (homOfLE (q.preimage_mono hle)) (q.preimage_basicOpen r)

/-- **Algebra reconstructed from the base-changed relative spectrum.**

Given a morphism `g : T ⟶ X` and a quasi-coherent `O_X`-algebra `𝒜`, the
reconstructed algebra is the pushforward of the structure sheaf of the
scheme-theoretic pullback. The
`sheaf` and `unit` fields are concrete (the topological pushforward of the
pullback's structure sheaf and the canonical natural transformation `q.c`
respectively, where `q := pullback.fst g (structureMorphism 𝒜)`). The
`coequifibered` field is supplied by the named helper
`QcohAlgebra.pullback_coequifibered`, which packages the Stacks-01LR
pushforward-along-affine-morphism compatibility. -/
noncomputable def QcohAlgebra.pullback {X T : Scheme.{u}} (g : T ⟶ X)
    (𝒜 : X.QcohAlgebra) : T.QcohAlgebra :=
  let q : CategoryTheory.Limits.pullback g (RelativeSpec.structureMorphism 𝒜) ⟶ T :=
    CategoryTheory.Limits.pullback.fst g (RelativeSpec.structureMorphism 𝒜)
  { sheaf := (TopCat.Sheaf.pushforward CommRingCat.{u} q.base).obj
      (CategoryTheory.Limits.pullback g (RelativeSpec.structureMorphism 𝒜)).sheaf
    unit := ⟨q.c⟩
    coequifibered := QcohAlgebra.pullback_coequifibered g 𝒜 }

namespace RelativeSpec

/-! ## §5. Base change

For a morphism `g : T → X`, let `𝒜_g` be `QcohAlgebra.pullback g 𝒜`, the algebra
reconstructed from the pullback scheme. This section constructs
`T ×_X Spec_X(𝒜) ≅ Spec_T(𝒜_g)`.

Blueprint reference: `thm:relative_spec_base_change` (Stacks 01LS,
`lemma-spec-base-change`). -/

/-! ### Helpers for `base_change`

The base-change theorem packages the canonical iso content into named helpers
(`pullback_iso_affine_piece`, `pullback_iso_construction`, and `pullback_iso`,
below) and consumes the file-level `Scheme.QcohAlgebra.pullback` constructor
declared just above the namespace. -/

/-- **Per-affine-open identification for the base-change isomorphism.**

For an affine open `U : T.AffineZariskiSite`, the preimage
`q ⁻¹ᵁ U.1` under `q := pullback.fst g (structureMorphism 𝒜)` is itself affine
(since `q` is `IsAffineHom` by `QcohAlgebra.pullback_fst_isAffineHom`). Its
canonical iso with `Spec(Γ(pullback, q ⁻¹ᵁ U.1))` (`IsAffineOpen.isoSpec`)
matches `Spec((QcohAlgebra.pullback g 𝒜).sheaf.val(.op U.1))`
**by definitional unfolding** of the pushforward sheaf
(`(QcohAlgebra.pullback g 𝒜).sheaf := (pushforward q.base).obj (pullback _).sheaf`,
so its value at `U` is `(pullback _).sheaf.val(.op (q ⁻¹ᵁ U.1))` defeq).

This is the per-affine-piece isomorphism used in the global `pullback_iso`
construction. -/
noncomputable def pullback_iso_affine_piece {X T : Scheme.{u}} (g : T ⟶ X)
    (𝒜 : X.QcohAlgebra) (U : T.AffineZariskiSite) :
    ((CategoryTheory.Limits.pullback.fst g
        (RelativeSpec.structureMorphism 𝒜)) ⁻¹ᵁ U.1).toScheme ≅
      Scheme.Spec.obj (.op ((QcohAlgebra.pullback g 𝒜).sheaf.obj.obj (.op U.1))) :=
  haveI : IsAffineHom (CategoryTheory.Limits.pullback.fst g
      (RelativeSpec.structureMorphism 𝒜)) :=
    QcohAlgebra.pullback_fst_isAffineHom g 𝒜
  (U.2.preimage _).isoSpec

/-! ### Structural decomposition of the base-change isomorphism

Five helpers feeding `pullback_iso_construction`:

* `pullback_iso_affine_piece` — the per-affine isomorphism
  `(q ⁻¹ᵁ U.1).toScheme ≅ Spec(𝒜_g(U))`.
* `pullback_cocone` — cocone on `(relativeGluingData _).functor` with point
  `pullback g (structureMorphism 𝒜)` whose components are the `fromSpec` maps
  of the pulled-back affine opens.
* `pullback_cocone_desc_comp_fst` — the cocone descent composed with the
  pullback projection equals the relative-gluing-data structure morphism;
  the load-bearing identification that makes the open-cover argument work.
* `pullback_iso_desc_isIso` — the cocone descent is an iso, via the local
  affine-open argument on `pullback g (structureMorphism 𝒜)`.
* `pullback_iso_construction` — final assembly: `asIso desc |>.symm`.
-/

set_option backward.isDefEq.respectTransparency false in
/-- **Cocone on `(relativeGluingData _).functor` with point
`pullback g (structureMorphism 𝒜)`.**

The components are the `IsAffineOpen.fromSpec` maps of the pulled-back affine
opens `q⁻¹U.1`. Naturality follows from `IsAffineOpen.map_fromSpec` once
the relative-gluing-data functor's `map` action is unfolded as
`Spec.map (P.presheaf.map ((q.preimage_mono ...).op))`. -/
noncomputable def pullback_cocone {X T : Scheme.{u}} (g : T ⟶ X)
    (𝒜 : X.QcohAlgebra) :
    haveI : IsAffineHom (CategoryTheory.Limits.pullback.fst g
        (RelativeSpec.structureMorphism 𝒜)) :=
      QcohAlgebra.pullback_fst_isAffineHom g 𝒜
    Limits.Cocone (AffineZariskiSite.relativeGluingData
      (QcohAlgebra.pullback g 𝒜).coequifibered).functor :=
  haveI : IsAffineHom (CategoryTheory.Limits.pullback.fst g
      (RelativeSpec.structureMorphism 𝒜)) :=
    QcohAlgebra.pullback_fst_isAffineHom g 𝒜
  { pt := CategoryTheory.Limits.pullback g (RelativeSpec.structureMorphism 𝒜)
    ι :=
    { app := fun U => (U.2.preimage (CategoryTheory.Limits.pullback.fst g
        (RelativeSpec.structureMorphism 𝒜))).fromSpec
      naturality := fun U V x => by
        -- After unfolding `relativeGluingData.functor.map` through its
        -- `rightOp ⋙ Spec` template and the pushforward sheaf, the goal
        -- becomes `Spec.map ((pullback _ _).presheaf.map _) ≫
        --   (V.2.preimage q).fromSpec = (U.2.preimage q).fromSpec ≫ 𝟙 _`,
        -- which is `IsAffineOpen.map_fromSpec` + `Category.comp_id`.
        set q := CategoryTheory.Limits.pullback.fst g
          (RelativeSpec.structureMorphism 𝒜)
        simp only [AffineZariskiSite.relativeGluingData, Functor.comp_map,
          Functor.rightOp_map, Functor.const_obj_map]
        exact (V.2.preimage q).map_fromSpec (U.2.preimage q) _ } }

/-- **The descent composed with `q` equals `d.toBase`.**

The pullback-cocone descent `T.RelativeSpec(g^*𝒜) ⟶ pullback g _`, composed
with the pullback projection `q := pullback.fst _ _`, equals the relative-
gluing-data's structure morphism `d.toBase`. Proof: `colimit.hom_ext`, then
the per-component identity uses `SpecMap_appLE_fromSpec`. -/
lemma pullback_cocone_desc_comp_fst {X T : Scheme.{u}} (g : T ⟶ X)
    (𝒜 : X.QcohAlgebra) :
    haveI : IsAffineHom (CategoryTheory.Limits.pullback.fst g
        (RelativeSpec.structureMorphism 𝒜)) :=
      QcohAlgebra.pullback_fst_isAffineHom g 𝒜
    haveI : ((AffineZariskiSite.relativeGluingData
        (QcohAlgebra.pullback g 𝒜).coequifibered).functor ⋙
        Scheme.forget).IsLocallyDirected :=
      Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin _
    Limits.colimit.desc _ (pullback_cocone g 𝒜) ≫
        CategoryTheory.Limits.pullback.fst g (RelativeSpec.structureMorphism 𝒜) =
      (AffineZariskiSite.relativeGluingData
        (QcohAlgebra.pullback g 𝒜).coequifibered).toBase := by
  haveI : IsAffineHom (CategoryTheory.Limits.pullback.fst g
      (RelativeSpec.structureMorphism 𝒜)) :=
    QcohAlgebra.pullback_fst_isAffineHom g 𝒜
  haveI : ((AffineZariskiSite.relativeGluingData
      (QcohAlgebra.pullback g 𝒜).coequifibered).functor ⋙
      Scheme.forget).IsLocallyDirected :=
    Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin _
  set q := CategoryTheory.Limits.pullback.fst g (RelativeSpec.structureMorphism 𝒜)
  set d := AffineZariskiSite.relativeGluingData (QcohAlgebra.pullback g 𝒜).coequifibered
  refine Limits.colimit.hom_ext fun U => ?_
  rw [← Category.assoc, Limits.colimit.ι_desc, d.ι_toBase U]
  change (U.2.preimage q).fromSpec ≫ q = _
  rw [← U.2.SpecMap_appLE_fromSpec q (U.2.preimage q) le_rfl,
    Scheme.Hom.appLE_eq_app, ← IsAffineOpen.isoSpec_inv_ι, ← Category.assoc]
  rfl

/-- **The descent map is an isomorphism.**

The canonical descent map `T.RelativeSpec(g^*𝒜) ⟶ pullback g (structureMorphism 𝒜)`
defined by the cocone `pullback_cocone g 𝒜` is an isomorphism. Proof:
`IsZariskiLocalAtTarget` for the isomorphism property applied to the
affine open cover `{q ⁻¹ᵁ U.1}` of `pullback g _`. The preimage of each
piece under `desc` matches `(colimit.ι d.functor U).opensRange` by
`pullback_cocone_desc_comp_fst` + `Cover.RelativeGluingData.toBase_preimage_eq_opensRange_ι`,
and the local restriction is then a composition of three explicit isos. -/
lemma pullback_iso_desc_isIso {X T : Scheme.{u}} (g : T ⟶ X)
    (𝒜 : X.QcohAlgebra) :
    haveI : IsAffineHom (CategoryTheory.Limits.pullback.fst g
        (RelativeSpec.structureMorphism 𝒜)) :=
      QcohAlgebra.pullback_fst_isAffineHom g 𝒜
    haveI : ((AffineZariskiSite.relativeGluingData
        (QcohAlgebra.pullback g 𝒜).coequifibered).functor ⋙
        Scheme.forget).IsLocallyDirected :=
      Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin _
    IsIso (Limits.colimit.desc _ (pullback_cocone g 𝒜)) := by
  haveI : IsAffineHom (CategoryTheory.Limits.pullback.fst g
      (RelativeSpec.structureMorphism 𝒜)) :=
    QcohAlgebra.pullback_fst_isAffineHom g 𝒜
  haveI : ((AffineZariskiSite.relativeGluingData
      (QcohAlgebra.pullback g 𝒜).coequifibered).functor ⋙
      Scheme.forget).IsLocallyDirected :=
    Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin _
  set q := CategoryTheory.Limits.pullback.fst g (RelativeSpec.structureMorphism 𝒜)
  set d := AffineZariskiSite.relativeGluingData (QcohAlgebra.pullback g 𝒜).coequifibered
  set desc := Limits.colimit.desc d.functor (pullback_cocone g 𝒜) with desc_def
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme)
    (fun U : T.AffineZariskiSite => q ⁻¹ᵁ U.1) ?_).mpr fun U ↦ ?_
  · -- iSup of preimages = preimage of iSup = preimage of ⊤ = ⊤.
    rw [← Scheme.Hom.preimage_iSup]
    convert Scheme.Hom.preimage_top q using 2
    exact iSup_affineOpens_eq_top T
  · -- Per-piece: `desc ∣_ q⁻¹U.1` is iso. Following the template at
    -- `SmallAffineZariski.isColimitCocone` (file
    -- `Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean:343`), reduce
    -- to `IsIso (pullback.snd desc (q⁻¹U.1).ι)` and build an iso
    -- `pullback desc (q⁻¹U.1).ι ≅ d.functor.obj U` via range matching using
    -- the key fact `hPre`.
    have hPre : desc ⁻¹ᵁ q ⁻¹ᵁ U.1 = (Limits.colimit.ι d.functor U).opensRange := by
      rw [← Scheme.Hom.comp_preimage, pullback_cocone_desc_comp_fst g 𝒜]
      have h := d.toBase_preimage_eq_opensRange_ι U
      simpa [AffineZariskiSite.directedCover, Scheme.Opens.opensRange_ι] using h
    -- The per-piece factorisation: `desc ∣_ q⁻¹U.1` factors as three isos:
    --   (1) `Scheme.isoOfEq _ hPre`:
    --       `(desc⁻¹q⁻¹U.1).toScheme ≅ (colim.ι U).opensRange.toScheme`
    --   (2) `colim.ι U .isoOpensRange.symm`:
    --       `(colim.ι U).opensRange.toScheme ≅ d.functor.obj U`
    --   (3) `(pullback_iso_affine_piece g 𝒜 U).symm`:
    --       `d.functor.obj U ≅ Spec(𝒜_g(U)) ≅ (q⁻¹U.1).toScheme`
    --       (the inverse via `IsAffineOpen.isoSpec.inv ≫ ι`).
    -- Commute the chain through `(q⁻¹U.1).ι` by canceling the mono ι.
    let iso_chain : (desc ⁻¹ᵁ q ⁻¹ᵁ U.1).toScheme ≅ (q ⁻¹ᵁ U.1).toScheme :=
      Scheme.isoOfEq _ hPre ≪≫
        (Limits.colimit.ι d.functor U).isoOpensRange.symm ≪≫
        (pullback_iso_affine_piece g 𝒜 U).symm
    suffices h : desc ∣_ q ⁻¹ᵁ U.1 = iso_chain.hom by
      change IsIso (desc ∣_ q ⁻¹ᵁ U.1)
      rw [h]; exact iso_chain.isIso_hom
    -- Verify equality by post-composing with `(q⁻¹ᵁ U.1).ι` (which is mono).
    have h_paff_inv : (pullback_iso_affine_piece g 𝒜 U).inv ≫ (q ⁻¹ᵁ U.1).ι =
        (U.2.preimage q).fromSpec := (U.2.preimage q).isoSpec_inv_ι
    have h_cocone : (U.2.preimage q).fromSpec =
        Limits.colimit.ι d.functor U ≫ desc := by
      change _ = Limits.colimit.ι d.functor U ≫
        Limits.colimit.desc d.functor (pullback_cocone g 𝒜)
      rw [Limits.colimit.ι_desc]
      rfl
    have h_post : (desc ∣_ (q ⁻¹ᵁ U.1)) ≫ (q ⁻¹ᵁ U.1).ι =
        iso_chain.hom ≫ (q ⁻¹ᵁ U.1).ι := by
      refine (morphismRestrict_ι desc (q ⁻¹ᵁ U.1)).trans ?_
      calc (desc ⁻¹ᵁ q ⁻¹ᵁ U.1).ι ≫ desc
          = ((Scheme.isoOfEq _ hPre).hom ≫
              (Limits.colimit.ι d.functor U).opensRange.ι) ≫ desc := by
            rw [Scheme.isoOfEq_hom_ι]
        _ = (Scheme.isoOfEq _ hPre).hom ≫
              (Limits.colimit.ι d.functor U).opensRange.ι ≫ desc := by
            rw [Category.assoc]
        _ = (Scheme.isoOfEq _ hPre).hom ≫
              ((Limits.colimit.ι d.functor U).isoOpensRange.inv ≫
              Limits.colimit.ι d.functor U) ≫ desc := by
            rw [(Limits.colimit.ι d.functor U).isoOpensRange_inv_comp]
        _ = (Scheme.isoOfEq _ hPre).hom ≫
              (Limits.colimit.ι d.functor U).isoOpensRange.inv ≫
              (Limits.colimit.ι d.functor U ≫ desc) := by
            rw [Category.assoc]
        _ = (Scheme.isoOfEq _ hPre).hom ≫
              (Limits.colimit.ι d.functor U).isoOpensRange.inv ≫
              (pullback_iso_affine_piece g 𝒜 U).inv ≫ (q ⁻¹ᵁ U.1).ι := by
            rw [← h_cocone, ← h_paff_inv]; rfl
        _ = iso_chain.hom ≫ (q ⁻¹ᵁ U.1).ι := by
            simp [iso_chain, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    exact (cancel_mono (q ⁻¹ᵁ U.1).ι).mp h_post

/-- **Canonical base-change isomorphism.**

Builds the isomorphism
`pullback g (structureMorphism 𝒜) ≅ T.RelativeSpec (QcohAlgebra.pullback g 𝒜)`.

**Construction**: the cocone `pullback_cocone g 𝒜` on the relative-gluing-data
functor of `𝒜_g` has point `pullback g (structureMorphism 𝒜)`. The colimit
descent map `T.RelativeSpec(𝒜_g) ⟶ pullback g _` from this cocone is an
isomorphism by `pullback_iso_desc_isIso`; the result is the inverse iso. -/
noncomputable def pullback_iso_construction {X T : Scheme.{u}} (g : T ⟶ X)
    (𝒜 : X.QcohAlgebra) :
    CategoryTheory.Limits.pullback g (RelativeSpec.structureMorphism 𝒜) ≅
      T.RelativeSpec (QcohAlgebra.pullback g 𝒜) := by
  haveI : IsAffineHom (CategoryTheory.Limits.pullback.fst g
      (RelativeSpec.structureMorphism 𝒜)) :=
    QcohAlgebra.pullback_fst_isAffineHom g 𝒜
  haveI : ((AffineZariskiSite.relativeGluingData
      (QcohAlgebra.pullback g 𝒜).coequifibered).functor ⋙
      Scheme.forget).IsLocallyDirected :=
    Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin _
  set d := AffineZariskiSite.relativeGluingData (QcohAlgebra.pullback g 𝒜).coequifibered
  let desc : T.RelativeSpec (QcohAlgebra.pullback g 𝒜) ⟶
      CategoryTheory.Limits.pullback g (RelativeSpec.structureMorphism 𝒜) :=
    Limits.colimit.desc d.functor (pullback_cocone g 𝒜)
  haveI : IsIso desc := pullback_iso_desc_isIso g 𝒜
  exact (asIso desc).symm

/-- **Canonical base-change isomorphism (Nonempty form).** The pullback
`pullback g (structureMorphism 𝒜)` (formed in `Scheme`) is canonically
isomorphic to the relative spectrum of the pulled-back qcoh algebra
`QcohAlgebra.pullback g 𝒜`. Witnessed by `pullback_iso_construction`. -/
theorem pullback_iso {X T : Scheme.{u}} (g : T ⟶ X)
    (𝒜 : X.QcohAlgebra) :
    Nonempty (CategoryTheory.Limits.pullback g (RelativeSpec.structureMorphism 𝒜) ≅
              T.RelativeSpec (QcohAlgebra.pullback g 𝒜)) :=
  ⟨pullback_iso_construction g 𝒜⟩

/-- **Base change of the relative spectrum.**

For a morphism `g : T → X` and a quasi-coherent `O_X`-algebra `𝒜`, there
exists a quasi-coherent `O_T`-algebra `𝒜'` and an isomorphism of `T`-schemes
`T ×_X Spec_X(𝒜) ≅ Spec_T(𝒜')`. The witness is the reconstructed algebra
`QcohAlgebra.pullback g 𝒜`. -/
theorem base_change {X T : Scheme.{u}} (g : T ⟶ X) (_𝒜 : X.QcohAlgebra) :
    ∃ (𝒜' : T.QcohAlgebra),
      Nonempty (pullback g (RelativeSpec.structureMorphism _𝒜) ≅
                  T.RelativeSpec 𝒜') :=
  ⟨QcohAlgebra.pullback g _𝒜, pullback_iso g _𝒜⟩

/-! ## §6. Functoriality

The definition below records the object assignment
`𝒜 ↦ (Spec_X(𝒜) → X)` in the over category.

Blueprint reference: `thm:relative_spec_functorial` (Stacks 01LR
definition-relative-spec + lemma-glueing-gives-functor-spec). -/

/-- **The relative-spectrum functor (object level).**

The object-level functorial action `𝒜 ↦ Over.mk (π_𝒜) : Over X`, packaging
the relative spectrum together with its structure morphism over `X`. -/
noncomputable def functor (X : Scheme.{u}) :
    X.QcohAlgebra → Over X :=
  fun 𝒜 => Over.mk (RelativeSpec.structureMorphism 𝒜)

end RelativeSpec

end Scheme

end AlgebraicGeometry
