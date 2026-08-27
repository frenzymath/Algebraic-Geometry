/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Descent
import AlgebraicJacobian.Cohomology.CechHigherDirectImage
import AlgebraicJacobian.Cohomology.FlatBaseChange
import AlgebraicJacobian.Cohomology.TildeExactness
import AlgebraicJacobian.Cohomology.QcohTildeSections
import AlgebraicJacobian.Cohomology.CechTermAcyclic
import AlgebraicJacobian.Cohomology.ModulesCoverConservativity
import AlgebraicJacobian.Cohomology.AffinePushPullEssImage
import AlgebraicJacobian.Cohomology.PullbackQuasicoherent
-- Added run 0068 r3.  Supplies the general 02KG/02KH mate `canonicalBaseChangeMap` together with
-- its `IsIso` theorem (flat `g`, qcqs `f`, quasi-coherent `F`) and the qcqs pushforward
-- quasi-coherence `Scheme.Modules.pushforward_isQuasicoherent` (Stacks 01XJ).  An earlier revision
-- of this file's docstring said this module "is deliberately not imported because it carries
-- `sorry`s": that was FALSE at HEAD and is the reason two obligations here were priced as open.
-- Its cone is `sorry`-free (five modules new here), and it does not import this file: no cycle.
import AlgebraicJacobian.Picard.QuotScheme
-- Added run 0068 r4.  Supplies the σ-COORDINATE FORMULA FOR THE ČECH NERVE COFACE, which is what
-- the twisted-nerve square needs and what this file could not previously see:
-- `backboneIncl_nerveδ` (`…LegMid1`) factors the σ'-summand inclusion followed by the geometric
-- coface as the open inclusion `U_{σ'} ⊆ U_{σ'∘δᵏ}` followed by the reindexed summand inclusion,
-- and `pushPull_sigma_iso_π_incl` / `cechNerve_drop_δ` (`…Leg`) turn that into a statement about
-- `pushPull_sigma_iso` and the nerve's own `δ`.
--
-- These lemmas had been in the project for many sessions and were NOT in this file's import cone;
-- a `#check` in this file was the one-second test, and three predecessor sessions priced the
-- twisted square without running it.  Cone: 8 modules, all already reachable except these two, and
-- neither imports this file (checked transitively) — no cycle.
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLegMid1

/-!
# Unconditional higher direct images via Čech complexes, and flat base change

For a separated quasi-compact morphism of schemes `f : X ⟶ S`, a finite affine open cover
`𝒰` of `X` and a quasi-coherent `F : X.Modules`, the higher direct image `Rⁱ f_* F` is the
`i`-th cohomology of the relative Čech complex `Č•(𝒰, F)`.  No enough-injectives hypothesis
on `O_X`-modules is needed: it is the cohomology of an explicit complex of quasi-coherent
sheaves.  The bulk of the file establishes flat base change for these Čech higher direct
images: for a cartesian square with `g : S' ⟶ S` flat, `g^*(Rⁱ f_* F) ≅ Rⁱ f'_* (g'^* F)`.

The base-change proof reduces, through the product decomposition of a fibre power of the
cover into its intersection opens, to a Beck–Chevalley comparison over a single Čech
intersection open `U_σ`.  Over an affine base and for a separated `f` that open is affine,
the restricted cartesian square becomes a pushout square of rings, and the comparison is the
affine termwise base change of `FlatBaseChange.lean`, matched to the abstract push–pull
objects through the `tilde` dictionary over `Spec`.

## Main results

* `cechHigherDirectImage`: the `i`-th higher direct image, as the `i`-th cohomology of the
  relative Čech complex.
* `openImmersion_beckChevalley`: for a cartesian square base-changing an open immersion `p`
  onto an affine open along `g'`, the isomorphism `g'^*(p_* p^* F) ≅ p'_* p'^*(g'^* F)`.
* `pushPullObj_coverInter_baseChange`: base change of the push–pull object over a single Čech
  intersection open, over affine bases.
* `cechComplex_baseChange_iso`: applying `g^*` degreewise to `Č•(𝒰, F)` gives `Č•(𝒰', g'^* F)`
  for the base-changed cover `𝒰'` and the base-changed sheaf `g'^* F`.
* `cech_flatBaseChange`: flat base change for the Čech higher direct images.
* `cech_flatBaseChange_qcoh`: the same conclusion with the flat-exactness leaf absent from the
  proof term and no extra hypotheses.
* `cech_flatBaseChange_oneLeaf`: **the form to consume** — same hypotheses and conclusion again,
  with the flat-exactness leaf *and* the S-level cosimplicial leaf both absent, so exactly one
  `sorry` (the twisted-nerve naturality square) separates it from Stacks 02KH.
* `cech_pushforward_baseChange_natIso_flat` / `isIso_cechOuterBC_nerve_obj`: the S-level
  cosimplicial comparison, `sorry`-free, via the definitional identity of `cechOuterBC` with
  `canonicalBaseChangeMap` and the landed `canonicalBaseChangeMap_isIso`.
* `isQuasicoherent_cechComplex_X`: every term of the relative Čech complex is quasi-coherent,
  which is what discharges the hypotheses of `cech_flatBaseChange_of_termsQuasicoherent`.
* `cechOuterBC` / `cech_pushforward_baseChange_natIso_of_isIso` / `isIso_app_pi_of_isIso_app`:
  the cosimplicial comparison as a *whiskered mate*, which removes the cosimplicial naturality
  obligation entirely and leaves one `IsIso` per index tuple.
* `cechNerve_backbone_δ_sigma` / `cechNerve_drop_δ_sigma` (run 0068 r4): the Čech nerve's coface
  read through the σ-product decomposition — "reindex the tuple by `δᵏ`, then restrict along
  `U_{σ'} ⊆ U_{σ'∘δᵏ}`".  Composed from lemmas that had been in the project for many sessions and
  were merely outside this file's import cone.
* `alternatingCofaceComplexIsoOfDelta` (run 0068 r4): an isomorphism of alternating coface
  complexes from **coface** compatibility alone, no general-`φ` naturality.  The differential is
  `∑ᵢ (-1)ⁱ • δᵢ`, so that is all any consumer here can see — and it is all this tree's
  σ-coordinate lemmas can supply.
* `sigmaAssembled_δ_square` / `twistedNerve_δ_square_concrete` (run 0068 r4): the twisted leaf's
  coface square, **proved** from the per-σ compatibility `TwistedPerSigmaDeltaCompat` — but in
  σ-decomposed form (target a `Pi` product).
* `twistedComponent` / `twistedComponent_δ_square` (run 0068 r5): the same square at
  `twisted_cech_nerve_iso`'s **own** spelling, target the base-changed nerve's degree object.  The
  bridge is `cechNerve_backbone_δ_sigma` applied to the *base-changed* cover.  This is the wiring
  r4's own notes named as unwritten, so the twisted leaf now has ONE open item, not two.
* `BcSquareNaturality` / `BcSquarePullbackSide` / `bcSquareNaturality_iff_pullbackSide` (run 0068
  r5): half (a) — the one remaining obligation — as a **named** `Prop` rather than an unnamed
  hypothesis binder, together with an equivalent form carrying no `pushforward`, hence attackable by
  the pullback pseudofunctor's coherence and the mate's unit law.
* `counit_comp_decomp`, `rawPushPullMap_pullback_counit`, `bcv_hom_eq`, `bcv_pullback_counit`
  (run 0068 r6): **both** Beck–Chevalley mates in half (a) are *eliminable*.  r5 removed one and
  recorded honestly that the other was blocked by `pushPullMap (wmap …)` sitting between the mate
  and the counit; the fix is that that restriction map is *itself* built from a unit, so the same
  "under `p^*`, past the counit" move kills it.  See the section "THE SECOND MATE IS ELIMINABLE
  TOO" below.  The reduction these feed —  `BcSquareCoherence` and
  `bcSquareCounitSide_of_coherence` — lives in
  `AlgebraicJacobian.Cohomology.CechTwistedCoherenceReduction`, deliberately in a **separate
  module**: its proof unfolds two `asIso`-wrapped `IsIso` instances, which is cheap against an
  olean and pathological (35 min CPU, 10 GB RSS, unfinished) when they are local to this file.
  **None of this discharges anything**: `BcSquareCoherence` is assumed, not proved.

## Obligations not yet discharged

Three statements below are still assumed rather than proved.

**And one more that a `sorry` census cannot see, because it is a hypothesis and not a `sorry`:
`BcSquareCoherence` (run 0068 r6, in `Cohomology.CechTwistedCoherenceReduction`).**  It is what the
twisted-nerve chain now rests on.  It is stated with no Beck–Chevalley mate in it, which is the
round's advance — but it is *not proved and not free*: it is a genuine identity relating the
pullback pseudofunctor's coherence isomorphisms to the cover-intersection inclusion
`U_{σ'} ⊆ U_{σ'∘δᵏ}`.  Listed here because a reader counting `sorry`s will not find it, and this
file has a history of obligations that stayed invisible for exactly that reason.

* `pullback_preservesMonomorphisms`: for `g` flat, `g^*` preserves monomorphisms — for
  *arbitrary* `𝒪_S`-modules.  **It is no longer on the critical path, and it should not be
  attempted.**  The statement is walled: mathlib gives `SheafOfModules.pullback` no pointwise
  model, and the sibling project `MR0555258-Compactifying-Picard` independently reduced `j_!` to
  the same missing brick.  What changed (run 0068 r1) is that nothing needs it:

  - flat left-exactness was being demanded at the strongest generality that makes the sentence
    true, while every consumer instantiates it at *quasi-coherent* objects;
  - on quasi-coherent objects it is now **proved**, sorry-free, by
    `pullback_preservesKernel_of_isQuasicoherent` — via cone-cancellation
    (`preservesLimit_comp_cancel`) off the tilde-image exactness already in the tree, plus the
    fullness of `tilde`;
  - and the homology comparison the Čech proof consumes needs only *one kernel per degree*
    (`mapHomologicalComplexHomologyIso_of_preservesKernel`), not global exactness — so
    `pullback_mapHC_homologyIso_of_isQuasicoherent` is an axiom-clean replacement for
    `pullback_mapHC_homologyIso`.

  Measured, not asserted: `scripts/axiom-frontier.lean`'s `leakProbe_qcohRoute_*` report clean
  axioms while `leakControl_qcohRoute_oldRoute` — the same conclusion via the old route — still
  reports `sorryAx`.  Prefer the `_of_isQuasicoherent` forms in anything new; the two `[Flat g]`
  declarations that route through mono-preservation are kept only so the reduction stays legible.
* the two `sorry`s in `cech_pushforward_baseChange_natIso` and `twisted_cech_nerve_iso`.  Both are
  `NatIso.ofComponents` naturality obligations, but **they are not the same kind of obligation**,
  and only the second is still on the critical path.

  `cech_pushforward_baseChange_natIso` IS FULLY REPLACED (run 0068 r3) by
  `cech_pushforward_baseChange_natIso_flat`, which is `sorry`-free.  Two steps got it there.  First,
  naturality was an *artefact of the construction*: both sides are `N ⋙ (a composite)` for the same
  cosimplicial `N`, so `cech_pushforward_baseChange_natIso_of_isIso` whiskers `cechOuterBC` and
  naturality is free, leaving one `IsIso` per index tuple `σ` via `isIso_app_pi_of_isIso_app`.
  Second — and this is what three sessions missed — that per-σ `IsIso` is **already a theorem
  here**: `cechOuterBC f g f' g' h` is *definitionally* `canonicalBaseChangeMap h`
  (`Picard/QuotScheme.lean`, checked by `rfl`), and `canonicalBaseChangeMap_isIso` proves that mate
  invertible at every quasi-coherent module for `[QuasiCompact f] [QuasiSeparated f] [Flat g]`.  The
  only missing input was quasi-coherence of the σ-term, now
  `isQuasicoherent_pushPullObj_coverInter`.  No `mateEquiv_vcomp` split, and no identification of
  `pushPullObj_coverInter_baseChange` with the mate, was needed.

  For `twisted_cech_nerve_iso` the whiskering argument **does not apply**: its right-hand side is
  the nerve of the *base-changed cover*, a different cosimplicial object, so there is no natural
  transformation to whisker.  Its naturality is genuine work — the compatibility of the cover
  base-change identification `coverInterOpen_baseChange_eq` with the index-omission maps.  Attempt
  the first leaf before this one, despite this one's lighter hypotheses — that advice is now
  spent: the first leaf is closed, and this square is **the single remaining obstruction** between
  this file and Stacks 02KG/02KH.  Its axiom-clean-modulo-this-one form is
  `cech_flatBaseChange_oneLeaf`.

  **RUN 0068 r4 REDUCED IT TO ONE PER-σ EQUATION, and the `sorry` stands only because that equation
  is unproved — not because anything around it is.**  The obligation as posed asked for naturality
  in *every* simplex map; the consumer chain bottoms out at `alternatingCofaceMapComplex`, whose
  differential is `∑ᵢ (-1)ⁱ • δᵢ`, so **coface** compatibility suffices
  (`alternatingCofaceComplexIsoOfDelta`).  That distinction is load-bearing rather than cosmetic:
  this tree's σ-coordinate lemmas are stated for `δ k` **only**, and no general-`φ` analogue exists
  in this workspace or in mathlib, so the obligation was out of reach *as stated* and is in reach
  once narrowed.  Given the narrowing, `cechNerve_drop_δ_sigma` +
  `sigmaAssembled_δ_square` + `twistedNerve_δ_square_concrete` **prove** the coface square from
  `TwistedPerSigmaDeltaCompat` alone, which says the per-σ Beck–Chevalley isos commute with the
  intersection-open inclusions.  Read that as: `twisted_cech_nerve_per_sigma` is built per σ and its
  **naturality in the over-object** is what is missing.  A `Y`-natural Beck–Chevalley for
  `pushPullFunctor` would supply it as a component; a workspace-wide search found none, and
  `pushPullFunctor` has no API beyond being whiskered once in `cechNerveCosimplicial`.

  **RUN 0068 r6: A `Y`-NATURAL BECK–CHEVALLEY IS NO LONGER WHAT IS NEEDED.**  The mate does not have
  to be related across squares — it can be *removed*, on both sides (`bcv_pullback_counit` and
  `rawPushPullMap_pullback_counit` below).  What is left is `BcSquareCoherence`
  (`Cohomology.CechTwistedCoherenceReduction`), an identity about the pullback pseudofunctor's
  coherence isomorphisms and the cover-intersection inclusion, with no mate in it.  The `sorry` in
  `twisted_cech_nerve_iso` still stands, because `BcSquareCoherence` is unproved; what changed is
  *which* statement must be proved, and that the tools for the new one
  (`pseudofunctor_associativity` and its unitality siblings, `pullbackCongr`, `ppTel` naturality)
  do exist here and in mathlib — which is exactly what the old frontier lacked.

Neither `pullback_preservesFiniteLimits` nor `pullback_preservesHomology` is an `instance`, and
that is deliberate: as instances they leaked `sorryAx` into every *synthesis site* while
declarations merely quantifying over them reported clean axioms.  Do not restore the attribute
before the carrier is proved.

Everything downstream of these — in particular `cechComplex_baseChange_iso` and
`cech_flatBaseChange` — is proved modulo them.

## References

* Stacks project, tags 02KG and 02KH (flat base change for cohomology), 01I8 (quasi-coherent
  sheaves on an affine scheme), 01BG (stability of quasi-coherence under pullback).
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.Modules

variable {S S' X X' : Scheme.{u}}

/-- **Unconditional higher direct image via Čech.** For a separated quasi-compact
`f : X ⟶ S`, a finite affine open cover `𝒰` of `X`, and a quasi-coherent
`F : X.Modules`, the `i`-th higher direct image is the `i`-th cohomology of the
relative Čech complex. This needs **no** enough-injectives hypothesis on
`O_X`-modules: it is the cohomology of an explicit complex of quasi-coherent
sheaves. By `cech_computes_higherDirectImage` it agrees with the derived-functor
higher direct image wherever the latter is defined, and is independent of the
chosen affine cover up to canonical isomorphism. For `i = 0` one recovers the
ordinary pushforward `R⁰ f_* F = f_* F`. -/
noncomputable def cechHigherDirectImage (f : X ⟶ S) (𝒰 : X.OpenCover)
    (F : X.Modules) (i : ℕ) : S.Modules :=
  (CechComplex f 𝒰 F).homology i

/-! ### Structure of the proof of `cech_flatBaseChange` (Stacks 02KH, separated case)

The proof decomposes into two independent halves, assembled in `cech_flatBaseChange`.

1. **Homology side.** The pullback `g^*` is exact, so it commutes with
   `HomologicalComplex.homology`:
   * `pullback_preservesFiniteColimits` — `g^*` is a left adjoint;
   * `pullback_preservesFiniteLimits` — `g` flat implies `g^*` left-exact.  Reduced to
     mono-preservation by `preservesFiniteLimits_of_preservesMonomorphisms`, whose open input
     `pullback_preservesMonomorphisms` is walled — **and is no longer needed**: for the
     quasi-coherent objects this complex actually has, use
     `pullback_preservesKernel_of_isQuasicoherent` and
     `pullback_mapHC_homologyIso_of_isQuasicoherent`, which are axiom-clean;
   * `pullback_preservesHomology` — derived from the two previous items via
     `Functor.preservesHomologyOfExact`;
   * `mapHomologicalComplexHomologyIso` and `pullback_mapHC_homologyIso` — the complex-level
     form of `ShortComplex.mapHomologyIso`.
2. **`cechComplex_baseChange_iso` (Stacks 02KG).** Applying `g^*` degreewise to `Č•(𝒰, F)`
   recovers `Č•(𝒰', g'^* F)`.  It comes from `cechComplex_baseChange_cosimplicialIso`, the
   whiskered composite of the cosimplicial Beck–Chevalley isomorphism
   `cech_pushforward_baseChange_natIso` (degreewise the per-σ
   `pushPullObj_coverInter_baseChange`, routed through the bridge
   `pushPullObj_pushforward_iso_tilde` to the affine termwise base change
   `affinePushforwardPullbackBaseChange` over the ring pushout carved out by
   `restrictedCartesianAffinePushout`) with the twisted-nerve identification
   `twisted_cech_nerve_iso` (degreewise `twisted_cech_nerve_per_sigma`, itself the X-level
   open-immersion Beck–Chevalley `openImmersion_beckChevalley` over the cover-base-change
   identity `coverInterOpen_baseChange_eq`).  Both cosimplicial isomorphisms are constructed
   degreewise; their cosimplicial naturality is not yet proved.

No spectral sequence is needed here: this is the *separated* case (`[IsSeparated f]`).
The Čech-to-cohomology spectral sequence enters only in the promotion from the separated to
the general quasi-separated case of Stacks 02KH, which is not this statement. -/

section HomologyComm

variable {C D : Type*} [Category.{u} C] [Category.{u} D] [Preadditive C] [Preadditive D]
  [CategoryWithHomology C] [CategoryWithHomology D]

/-- **Complex-level upgrade of `ShortComplex.mapHomologyIso`.** An additive functor `F`
that preserves homology commutes with `HomologicalComplex.homology`. The degree-`i`
short complex of `(F.mapHomologicalComplex c).obj K` is *definitionally* `F` applied to
the degree-`i` short complex `K.sc i` of `K` (both have `Xⱼ = F.obj (K.Xⱼ)` and
`d = F.map (K.d)`), so this is exactly `ShortComplex.mapHomologyIso (K.sc i) F`. -/
noncomputable def mapHomologicalComplexHomologyIso (F : C ⥤ D) [F.Additive]
    [F.PreservesHomology] {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c) (i : ι) :
    ((F.mapHomologicalComplex c).obj K).homology i ≅ F.obj (K.homology i) :=
  ShortComplex.mapHomologyIso (K.sc i) F

end HomologyComm

/-! ### Right exact + mono-preserving ⟹ left exact

The categorical step that converts the flat-pullback obligation from a statement about
*all* finite limits into a statement about *monomorphisms only*.  For an additive functor
between abelian categories, right exactness (which `g^*` has for free, being a left
adjoint) plus preservation of monomorphisms already forces left exactness.  Indeed
`Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono` says left exactness is
equivalent to: every short exact `0 → A → B → C → 0` maps to an exact `F A → F B → F C`
with `F A → F B` mono.  The exactness half is `ShortComplex.Exact.map_of_epi_of_preservesCokernel`
(available from right exactness alone, since `B → C` is epi), and the mono half is the
hypothesis.  Note this is *not* a "right exact ⟹ exact" fallacy: the mono hypothesis is
exactly the flatness input, and without it the statement is false (tensoring by a
non-flat module is right exact and not left exact). -/
section RightExactMono

variable {C D : Type*} [Category.{u} C] [Category.{u} D] [Abelian C] [Abelian D]

/-- **Right exact + mono-preserving ⟹ left exact**, for an additive functor between abelian
categories.  Project-local categorical supplement: mathlib has the TFAE
`Functor.preservesFiniteLimits_tfae` characterising left exactness by "short exact sequences
map to left-exact ones", and the right-exactness transport
`ShortComplex.Exact.map_of_epi_of_preservesCokernel`, but not this packaged criterion.
It is what reduces `pullback_preservesFiniteLimits` to mono-preservation. -/
theorem preservesFiniteLimits_of_preservesMonomorphisms (F : C ⥤ D) [F.Additive]
    [Limits.PreservesFiniteColimits F] [F.PreservesMonomorphisms] :
    Limits.PreservesFiniteLimits F := by
  rw [F.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro T hT
  have := hT.mono_f
  exact ⟨hT.exact.map_of_epi_of_preservesCokernel F hT.epi_g inferInstance, inferInstance⟩

end RightExactMono

/-! ### Monomorphisms of `𝒪_X`-modules are sectionwise

The mono half of flat left-exactness is checked on sections, so both directions of
"mono ⟺ injective on sections" are needed.  The `⟸` direction (over a basis) is
`Modules.mono_of_injective_app_of_isBasis` in `Picard/FlatKernelBase.lean`; the `⟹`
direction is below.  Together they make mono-preservation of a *sectionwise* functor
mechanical, which discharges the open-immersion case of `pullback_preservesMonomorphisms`
outright. -/

set_option backward.isDefEq.respectTransparency false in
/-- **A monomorphism of `𝒪_X`-modules is injective on sections over every open.**  The
forgetful functor `Scheme.Modules.toPresheaf` preserves limits, hence monomorphisms; a
monomorphism of `Ab`-valued presheaves is one sectionwise (evaluation preserves limits);
and mono in `Ab` is injectivity.  Converse of `Modules.mono_of_injective_app_of_isBasis`
(`Picard/FlatKernelBase.lean`).  Project-local: mathlib has the iso-level
`Scheme.Modules.Hom.isIso_iff_isIso_app` but not the mono-level statement. -/
theorem Modules.injective_app_of_mono {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    [Mono φ] (U : X.Opens) : Function.Injective (φ.app U) := by
  have h1 : Mono ((Scheme.Modules.toPresheaf X).map φ) := inferInstance
  haveI := h1
  have h2 : Mono (((Scheme.Modules.toPresheaf X).map φ).app (Opposite.op U)) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).mp h2

set_option backward.isDefEq.respectTransparency false in
/-- **Sectionwise criterion for a monomorphism of `𝒪_X`-modules.**  If `φ` is injective on
sections over *every* open then `φ` is a monomorphism: injectivity on all opens makes the
underlying `Ab`-presheaf morphism sectionwise mono, hence mono in the functor category, and
the faithful `Scheme.Modules.toPresheaf` reflects monomorphisms.  Converse of
`Modules.injective_app_of_mono`; sharpened to a basis just below.  Project-local. -/
theorem Modules.mono_of_injective_app {X : Scheme.{u}} {M N : X.Modules} {φ : M ⟶ N}
    (h : ∀ U : X.Opens, Function.Injective (φ.app U)) : Mono φ := by
  have hpre : Mono ((Scheme.Modules.toPresheaf X).map φ) := by
    haveI : ∀ U, Mono (((Scheme.Modules.toPresheaf X).map φ).app U) := fun U =>
      (AddCommGrpCat.mono_iff_injective _).mpr (h U.unop)
    exact NatTrans.mono_of_mono_app _
  haveI := hpre
  exact (Scheme.Modules.toPresheaf X).mono_of_mono_map hpre

set_option backward.isDefEq.respectTransparency false in
/-- **Basis-local criterion for a monomorphism of `𝒪_X`-modules.**  Only the sections over a
*basis* of opens need to be checked: basis injectivity gives stalkwise injectivity
(`TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis`), a morphism of sheaves of abelian
groups with monic stalk maps is monic (`TopCat.Presheaf.mono_of_stalk_mono`), and the faithful
`Scheme.Modules.toPresheaf` reflects it.  Sharpens `Modules.mono_of_injective_app`; the same
statement is proved in `Picard/FlatKernelBase.lean` as
`Modules.mono_of_injective_app_of_isBasis`, which this file cannot import (that file pulls in
all of `Picard/`).  Project-local. -/
theorem Modules.mono_of_injective_app_isBasis {X : Scheme.{u}} {M N : X.Modules}
    {ι : Type*} {B : ι → X.Opens} (hB : TopologicalSpace.Opens.IsBasis (Set.range B))
    {φ : M ⟶ N} (h : ∀ i, Function.Injective (φ.app (B i))) : Mono φ := by
  have happ : ∀ U ∈ Set.range B,
      Function.Injective (((Scheme.Modules.toPresheaf X).map φ).app (Opposite.op U)) := by
    rintro U ⟨i, rfl⟩; exact h i
  let MS : TopCat.Sheaf Ab.{u} X := ⟨M.presheaf, M.isSheaf⟩
  let NS : TopCat.Sheaf Ab.{u} X := ⟨N.presheaf, N.isSheaf⟩
  let fS : MS ⟶ NS := ⟨(Scheme.Modules.toPresheaf X).map φ⟩
  haveI : ∀ x, Mono ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map fS.1) := fun x =>
    (AddCommGrpCat.mono_iff_injective _).mpr
      (TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB happ x)
  haveI hmS : Mono fS := TopCat.Presheaf.mono_of_stalk_mono fS
  haveI : Mono ((Scheme.Modules.toPresheaf X).map φ) :=
    (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono _ _ fS).mp hmS
  exact (Scheme.Modules.toPresheaf X).mono_of_mono_map ‹_›

/-- **The opens lying inside a cover member form a basis.**  For an open cover `𝒰` of `X`, the
images `f_j(V)` of opens `V` of the cover members are a basis of `X`: given `x ∈ U`, the cover
provides a preimage `y` of `x` in some member, and `f_j(f_j⁻¹(U))` is a basic open containing
`x` and contained in `U`.  This is what makes mono-checking *cover-local*
(`Modules.mono_of_mono_restrict`).  Project-local. -/
theorem Scheme.OpenCover.isBasis_image_opens {X : Scheme.{u}} (𝒰 : X.OpenCover) :
    TopologicalSpace.Opens.IsBasis
      (Set.range (fun p : (j : 𝒰.I₀) × (𝒰.X j).Opens => (𝒰.f p.1) ''ᵁ p.2)) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hxU
  obtain ⟨y, hy⟩ := 𝒰.covers x
  refine ⟨(𝒰.f (𝒰.idx x)) ''ᵁ ((𝒰.f (𝒰.idx x)) ⁻¹ᵁ U), ⟨⟨𝒰.idx x, _⟩, rfl⟩, ?_, ?_⟩
  · exact ⟨y, by simpa [← hy] using hxU, hy⟩
  · rintro z ⟨w, hw, rfl⟩
    exact hw

/-- **Mono-checking is cover-local.**  If the restriction of `φ` to every member of an open
cover is a monomorphism then `φ` is one.  Combines the basis criterion
`Modules.mono_of_injective_app_isBasis` with `Scheme.OpenCover.isBasis_image_opens`, using that
restriction is sectionwise.  Companion of the iso-level
`Scheme.Modules.Hom.isIso_iff_isIso_restrict` (`Cohomology/ModulesCoverConservativity.lean`).

This is the reduction step for the general flat case of `pullback_preservesMonomorphisms`:
mono-preservation may be checked after restricting to an affine cover of the source, where the
morphism factors through an affine open of the target.  Project-local. -/
theorem Modules.mono_of_mono_restrict {X : Scheme.{u}} {M N : X.Modules} {φ : M ⟶ N}
    (𝒰 : X.OpenCover)
    (h : ∀ j, Mono ((Scheme.Modules.restrictFunctor (𝒰.f j)).map φ)) : Mono φ := by
  refine Modules.mono_of_injective_app_isBasis 𝒰.isBasis_image_opens (φ := φ) ?_
  rintro ⟨j, V⟩
  haveI := h j
  exact Modules.injective_app_of_mono ((Scheme.Modules.restrictFunctor (𝒰.f j)).map φ) V

/-- **Restriction along an open immersion preserves monomorphisms.**  Restriction is
*sectionwise* — `((restrictFunctor f).map φ).app U = φ.app (f ''ᵁ U)` holds by `rfl`
(`Scheme.Modules.restrict_obj`) — so injectivity on sections transfers verbatim, and
`Modules.mono_of_injective_app` concludes.
Combined with `Scheme.Modules.restrictFunctorIsoPullback` this gives the open-immersion
case of `pullback_preservesMonomorphisms` with no flatness input beyond the (automatic)
flatness of an open immersion.  Project-local. -/
theorem Modules.restrictFunctor_preservesMonomorphisms {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : (Scheme.Modules.restrictFunctor f).PreservesMonomorphisms where
  preserves {M N} φ hφ := by
    haveI := hφ
    refine Modules.mono_of_injective_app (fun U => ?_)
    exact Modules.injective_app_of_mono φ (f ''ᵁ U)

/-- **Flat pullback along an open immersion preserves monomorphisms** — the open-immersion
case of `pullback_preservesMonomorphisms`, transported from
`Modules.restrictFunctor_preservesMonomorphisms` along
`Scheme.Modules.restrictFunctorIsoPullback`.  Project-local. -/
theorem Modules.pullback_preservesMonomorphisms_of_isOpenImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.pullback f).PreservesMonomorphisms :=
  haveI := Modules.restrictFunctor_preservesMonomorphisms f
  Functor.preservesMonomorphisms.of_iso (Scheme.Modules.restrictFunctorIsoPullback f)

/-! ### The affine case of flat exactness, on the tilde image

For a flat ring map `φ : R ⟶ R'` the composite `(~) ⋙ g^*` (with `g = Spec.map φ`) *is* exact.
This is the affine-morphism ingredient of `pullback_preservesMonomorphisms`, and it is available
because both factors of the identification `pullback_spec_tilde_iso` are exact: extension of
scalars along a flat map (`ModuleCat.preservesFiniteLimits_extendScalars_of_flat`) and the tilde
functor itself (`tildePreservesFiniteLimits`, `Cohomology/TildeExactness.lean`).

The limitation is the domain, not the flatness: this says `g^*` is exact *on the tilde image*,
i.e. on quasi-coherent modules, whereas `PreservesMonomorphisms` quantifies over all modules.
See the docstring of `pullback_preservesMonomorphisms` for what that leaves open. -/

/-- **The tilde/pullback identification, at the level of functors.**  `pullback_spec_tilde_iso`
(`Cohomology/FlatBaseChange.lean`) is literally the `M`-component of a natural isomorphism — it
is built as `((conjugateIsoEquiv adjL adjR).symm (gammaPushforwardNatIso φ)).symm |>.app M` — so
the functor-level statement is obtained by dropping the `.app M`.  Recorded here because the
exactness argument needs naturality, and re-deriving it componentwise would be pointless.
Project-local. -/
noncomputable def tildePullbackNatIso {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars.{u, u, u} φ.hom ⋙ tilde.functor R' :=
  let adjL := (tilde.adjunction (R := R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
  let adjR := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := R'))
  ((conjugateIsoEquiv adjL adjR).symm (gammaPushforwardNatIso φ)).symm

/-- **Affine flat pullback is exact on the tilde image.**  For a flat ring map `φ : R ⟶ R'`, the
composite `M ↦ (Spec φ)^*(M^~)` preserves finite limits: by `tildePullbackNatIso` it is
isomorphic to `M ↦ (R' ⊗_R M)^~`, and both of those factors are exact — extension of scalars
because `φ` is flat (`ModuleCat.preservesFiniteLimits_extendScalars_of_flat`), and `~` by
`tildePreservesFiniteLimits`.

This is the affine-morphism ingredient of `pullback_preservesMonomorphisms`; with cover-locality
(`Modules.mono_of_mono_restrict`) and the open-immersion case it covers every *quasi-coherent*
module.  Project-local. -/
@[implicit_reducible]
noncomputable def tildePullback_preservesFiniteLimits {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (hφ : φ.hom.Flat) :
    Limits.PreservesFiniteLimits (tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ)) := by
  haveI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  haveI := tildePreservesFiniteLimits (R := R')
  haveI : Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} φ.hom ⋙ tilde.functor R') := inferInstance
  exact Limits.preservesFiniteLimits_of_natIso (tildePullbackNatIso φ).symm

/-! ### Cone-cancellation: exactness ON THE TILDE IMAGE, not merely of the composite

`tildePullback_preservesFiniteLimits` says the *composite* `(~) ⋙ g^*` is left exact.  That is
weaker than what a consumer needs, because a consumer holds a diagram of `𝒪_S`-modules that
*happen to be* tildes, not a diagram of modules over the ring.  The gap is closed by pure
category theory: if `F` preserves the limit of `K` and `F ⋙ G` preserves the limit of `K`, then
`G` preserves the limit of `K ⋙ F` — because `F` maps the limit cone of `K` to a limit cone,
which is therefore *the* limit cone of `K ⋙ F`, and `G` sends it to a limit cone by hypothesis
on the composite.

This is the step that was missing when the previous session concluded "the affine case holds
only on the tilde image".  It does hold only on the tilde image — but "on the tilde image" is
exactly the hypothesis the Čech consumer can supply, and cone-cancellation converts the
composite statement into a statement about `g^*` applied to tilde-shaped diagrams. -/

/-- **Cone-cancellation for preserved limits.**  If `F` preserves the limit of `K`, and the
composite `F ⋙ G` preserves the limit of `K`, then `G` preserves the limit of the *transported*
diagram `K ⋙ F`.  Pure category theory, no schemes: `F` carries the limit cone of `K` to a limit
cone of `K ⋙ F`, and it suffices to check `G` on that one cone
(`preservesLimit_of_preserves_limit_cone`).  Project-local; mathlib has the composition and
reflection lemmas but not this cancellation. -/
theorem preservesLimit_comp_cancel {J C D E : Type*} [Category J] [Category C]
    [Category D] [Category E] (K : J ⥤ C) (F : C ⥤ D) (G : D ⥤ E)
    [Limits.HasLimit K] [Limits.PreservesLimit K F] [Limits.PreservesLimit K (F ⋙ G)] :
    Limits.PreservesLimit (K ⋙ F) G :=
  Limits.preservesLimit_of_preserves_limit_cone
    (Limits.isLimitOfPreserves F (Limits.limit.isLimit K))
    (Limits.isLimitOfPreserves (F ⋙ G) (Limits.limit.isLimit K))

/-- **Affine flat pullback preserves finite limits of diagrams of tildes.**  For a flat ring map
`φ : R ⟶ R'` and any finite diagram `K` of `R`-modules, `(Spec φ)^*` preserves the limit of the
diagram `K ⋙ (~)` of `𝒪_{Spec R}`-modules.  Cone-cancellation
(`preservesLimit_comp_cancel`) applied to the two exactness facts already available:
`tildePreservesFiniteLimits` for `(~)` and `tildePullback_preservesFiniteLimits` for the
composite.  Project-local. -/
theorem tildePullback_preservesLimit_comp {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (hφ : φ.hom.Flat) {J : Type} [SmallCategory J] [FinCategory J] (K : J ⥤ ModuleCat.{u} R) :
    Limits.PreservesLimit (K ⋙ tilde.functor R) (Scheme.Modules.pullback (Spec.map φ)) := by
  haveI := tildePreservesFiniteLimits (R := R)
  haveI := tildePullback_preservesFiniteLimits φ hφ
  exact preservesLimit_comp_cancel K (tilde.functor R) _

/-- **Affine flat pullback preserves the kernel of a map of tildes.**  The parallel-pair
specialisation of `tildePullback_preservesLimit_comp`: for flat `φ` and `f : M ⟶ N` a map of
`R`-modules, `(Spec φ)^*` preserves `ker (f^~)`.  The diagram
`parallelPair f 0 ⋙ (~)` is isomorphic to `parallelPair (f^~) 0` (the tilde functor is additive,
so it sends the zero map to the zero map), and preservation transports along an iso of diagrams.
Project-local. -/
theorem tildePullback_preservesKernel {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (hφ : φ.hom.Flat) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    Limits.PreservesLimit (Limits.parallelPair ((tilde.functor R).map f) 0)
      (Scheme.Modules.pullback (Spec.map φ)) := by
  haveI := tildePullback_preservesLimit_comp φ hφ (Limits.parallelPair f 0)
  exact Limits.preservesLimit_of_iso_diagram (Scheme.Modules.pullback (Spec.map φ))
    (Limits.parallelPair.ext (Iso.refl _) (Iso.refl _) :
      Limits.parallelPair f 0 ⋙ tilde.functor R ≅
        Limits.parallelPair ((tilde.functor R).map f) 0)

/-- **Flat affine pullback preserves the kernel of ANY map of quasi-coherent modules.**  The
linchpin: `tildePullback_preservesKernel` only speaks about maps *of the form* `f^~`, which looks
like a severe restriction until one remembers that `tilde` is **full**
(`tilde.fullyFaithfulFunctor`, from `IsIso (tilde.adjunction).unit`).  So a map between objects of
the tilde essential image, transported along the two witnessing isomorphisms, *is* `tilde.map` of
a module map — not merely isomorphic to one — and preservation transports back along the iso of
parallel pairs.

Quasi-coherence enters only through `isIso_fromTildeΓ_iff : IsIso M.fromTildeΓ ↔ essImage M`,
which the tree already supplies for quasi-coherent modules over an affine base
(`isIso_fromTildeΓ_of_quasicoherent`, `Cohomology/QcohTildeSections.lean`).

This is the statement that makes flat base change for the Čech complex reachable without
`pullback_preservesMonomorphisms`: it is exactly the hypothesis of
`mapHomologicalComplexHomologyIso_of_preservesKernel`, at the objects the Čech complex actually
has.  Project-local. -/
theorem tildePullback_preservesKernel_of_essImage {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (hφ : φ.hom.Flat) {A B : (Spec R).Modules} (ψ : A ⟶ B)
    (hA : (tilde.functor R).essImage A) (hB : (tilde.functor R).essImage B) :
    Limits.PreservesLimit (Limits.parallelPair ψ 0) (Scheme.Modules.pullback (Spec.map φ)) := by
  obtain ⟨M, ⟨eA⟩⟩ := hA
  obtain ⟨N, ⟨eB⟩⟩ := hB
  set ψ' : (tilde.functor R).obj M ⟶ (tilde.functor R).obj N := eA.hom ≫ ψ ≫ eB.inv with hψ'
  obtain ⟨f, hf⟩ : ∃ f : M ⟶ N, (tilde.functor R).map f = ψ' :=
    ⟨(tilde.functor R).preimage ψ', (tilde.functor R).map_preimage ψ'⟩
  haveI : Limits.PreservesLimit (Limits.parallelPair ψ' 0)
      (Scheme.Modules.pullback (Spec.map φ)) := by
    rw [← hf]; exact tildePullback_preservesKernel φ hφ f
  refine Limits.preservesLimit_of_iso_diagram _
    (Limits.parallelPair.ext eA eB ?_ ?_ :
      Limits.parallelPair ψ' 0 ≅ Limits.parallelPair ψ 0)
  · simp [hψ']
  · simp

/-- **Quasi-coherent modules over an affine base lie in the tilde essential image.**  Repackaging
of `isIso_fromTildeΓ_iff` with the project's `isIso_fromTildeΓ_of_quasicoherent`, so that
`tildePullback_preservesKernel_of_essImage` can be applied from a quasi-coherence hypothesis
directly.  Project-local. -/
theorem essImage_tilde_of_isQuasicoherent {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (hM : M.IsQuasicoherent) : (tilde.functor R).essImage M := by
  haveI := hM
  exact isIso_fromTildeΓ_iff.mp inferInstance

/-! ### From `Spec.map (Γ g)` to a general flat `g` between affine schemes

`tildePullback_preservesKernel_of_essImage` is stated for a literal `Spec.map φ`.  The Čech
consumer carries `[IsAffine S] [IsAffine S']`, where `g` is `isoSpec`-conjugate to
`Spec.map (Γ g)` by `Scheme.isoSpec_inv_naturality`.  The conjugating functors are pullbacks along
*isomorphisms*, hence equivalences (`Scheme.Modules.pullbackIsoPushforwardInv` identifies them
with pushforwards along the inverse), so they neither create nor destroy preserved limits. -/

/-- **Pullback along an isomorphism is an equivalence.**  Via
`Scheme.Modules.pullbackIsoPushforwardInv`, which identifies it with the pushforward along the
inverse, itself half of `pushforwardEquivOfIso`.  Project-local; needed to move preserved limits
across the affine conjugation. -/
theorem Modules.pullback_iso_isEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) :
    (Scheme.Modules.pullback e.hom).IsEquivalence := by
  haveI : (Scheme.Modules.pushforward e.inv).IsEquivalence :=
    (Scheme.Modules.pushforwardEquivOfIso e.symm).isEquivalence_functor
  exact Functor.isEquivalence_of_iso (Scheme.Modules.pullbackIsoPushforwardInv e).symm

/-- **Quasi-coherence is closed under finite products over an affine base.**  Over `Spec R` a
finite product of quasi-coherent modules is quasi-coherent.

The proof is the tilde dictionary, and it is short *because* of
`essImage_tilde_of_isQuasicoherent`: each factor is `M_j^~` for some `R`-module `M_j`, the tilde
functor preserves finite limits (`tildePreservesFiniteLimits`, `Cohomology/TildeExactness.lean`)
so it carries `∏ M_j` to `∏ M_j^~`, and a tilde is quasi-coherent outright (mathlib's instance via
`presentationTilde`).  Quasi-coherence is closed under isomorphism, which transports the conclusion
back along that comparison.

Over a *general* base this is not available by this argument — the tilde dictionary is affine — and
the corresponding statement is a genuine gap; mathlib's `Quasicoherent.lean` offers only
`IsClosedUnderIsomorphisms` and `IsQuasicoherent.of_coversTop`.  But the affine case is the only one
the Čech consumer needs, since `cech_flatBaseChange` carries `[IsAffine S]`.  Project-local. -/
theorem isQuasicoherent_pi_of_isAffineBase {R : CommRingCat.{u}} {J : Type u} [Finite J]
    (A : J → (Spec R).Modules) (hA : ∀ j, (A j).IsQuasicoherent) :
    (∏ᶜ A).IsQuasicoherent := by
  haveI : Limits.PreservesFiniteLimits (tilde.functor R) := tildePreservesFiniteLimits
  haveI : Fintype J := Fintype.ofFinite J
  choose M e using fun j => essImage_tilde_of_isQuasicoherent (A j) (hA j)
  refine (SheafOfModules.isQuasicoherent.{u} (Spec R).ringCatSheaf).prop_of_iso
    (Limits.PreservesProduct.iso (tilde.functor R) M ≪≫
      Limits.Pi.mapIso (fun j => (e j).some)) ?_
  exact (presentationTilde.{u} (∏ᶜ M) Set.univ (by simp) _
    (Submodule.span_eq _)).isQuasicoherent

/-- **Quasi-coherence is closed under finite products over an ABSTRACT affine base.**  The
`isoSpec`-conjugated form of `isQuasicoherent_pi_of_isAffineBase`, which is stated over a literal
`Spec R` while the Čech consumer carries `[IsAffine S]` with `S` abstract.

Pushforward along the *iso* `S.isoSpec` is an equivalence, so it carries the product to the
product (`PreservesProduct.iso`) and moves quasi-coherence in both directions
(`pushforward_iso_preserves_qcoh`, `Cohomology/OpenImmersionPushforward.lean`).  Project-local. -/
theorem isQuasicoherent_pi_of_isAffine {B : Scheme.{u}} [IsAffine B] {J : Type u} [Finite J]
    (A : J → B.Modules) (hA : ∀ j, (A j).IsQuasicoherent) : (∏ᶜ A).IsQuasicoherent := by
  haveI : Fintype J := Fintype.ofFinite J
  have hA' : ∀ j, ((Scheme.Modules.pushforward B.isoSpec.hom).obj (A j)).IsQuasicoherent :=
    fun j => pushforward_iso_preserves_qcoh B.isoSpec (A j) (hA j)
  have hprod : (∏ᶜ fun j => (Scheme.Modules.pushforward B.isoSpec.hom).obj (A j)
      ).IsQuasicoherent :=
    isQuasicoherent_pi_of_isAffineBase _ hA'
  haveI : (Scheme.Modules.pushforward B.isoSpec.hom).IsEquivalence :=
    (Scheme.Modules.pushforwardEquivOfIso B.isoSpec).isEquivalence_functor
  have hback : ((Scheme.Modules.pushforward B.isoSpec.hom).obj (∏ᶜ A)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent.{u} (Spec Γ(B, ⊤)).ringCatSheaf).prop_of_iso
      (Limits.PreservesProduct.iso (Scheme.Modules.pushforward B.isoSpec.hom) A).symm hprod
  refine (SheafOfModules.isQuasicoherent.{u} B.ringCatSheaf).prop_of_iso ?_
    (pushforward_iso_preserves_qcoh B.isoSpec.symm _ hback)
  exact ((Scheme.Modules.pushforwardComp B.isoSpec.hom B.isoSpec.inv).app _) ≪≫
    (Scheme.Modules.pushforwardCongr B.isoSpec.hom_inv_id).app _ ≪≫
    (Scheme.Modules.pushforwardId B).app _

/-- **Affine pushforward preserves quasi-coherence, at a literal `Spec.map`.**  For a ring map
`φ : R ⟶ R'` and a quasi-coherent `M` on `Spec R'`, the pushforward `(Spec φ)_* M` is
quasi-coherent on `Spec R`.

This is the brick the Čech terms need and it is *entirely* mathlib: `isIso_fromTildeΓ_pushforward`
(`Mathlib/AlgebraicGeometry/Modules/Tilde.lean`) says exactly that an affine pushforward preserves
the tilde model, and `isIso_fromTildeΓ_iff` converts that to essential-image membership, whence
quasi-coherence because a tilde is quasi-coherent outright.

**Why this exists here rather than being imported — and the reason is now historical.**  The general
statement `Scheme.Modules.pushforward_isQuasicoherent` (Stacks 01XJ, qcqs morphisms) lives in
`Picard/QuotScheme.lean`, which this file used not to import on the ground that that module carries
`sorry`s.  **That ground was false at HEAD** (its whole cone is `sorry`-free), and run 0068 r3 added
the import, so the general form *is* available here now and
`isQuasicoherent_pushPullObj_coverInter` uses it.  This affine special case is retained because it
is four lines of mathlib, needs no qcqs side conditions, and several existing proofs consume it.
Project-local. -/
theorem isQuasicoherent_pushforward_specMap {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (M : (Spec R').Modules) (hM : M.IsQuasicoherent) :
    ((Scheme.Modules.pushforward (Spec.map φ)).obj M).IsQuasicoherent := by
  haveI := hM
  haveI hpf : IsIso ((Scheme.Modules.pushforward (Spec.map φ)).obj M).fromTildeΓ :=
    isIso_fromTildeΓ_pushforward φ M
  obtain ⟨N, ⟨e⟩⟩ := isIso_fromTildeΓ_iff.mp hpf
  exact (SheafOfModules.isQuasicoherent.{u} (Spec R).ringCatSheaf).prop_of_iso e
    (presentationTilde.{u} N Set.univ (by simp) _ (Submodule.span_eq _)).isQuasicoherent

/-- **Pushforward along ANY morphism of affine schemes preserves quasi-coherence.**  The
`isoSpec`-conjugated form of `isQuasicoherent_pushforward_specMap`: `q` is conjugate to
`Spec.map (Γ q)` by `Scheme.isoSpec_hom_naturality`, and the conjugating functors are pushforwards
along isomorphisms, which move quasi-coherence in both directions.

This is the shape the Čech term consumes: each intersection open `U_σ` is affine (`X` separated,
cover affine) and the base `S` is affine, so `j_σ ≫ f : U_σ ⟶ S` is a morphism of affine schemes.
Project-local. -/
theorem isQuasicoherent_pushforward_of_isAffine {A B : Scheme.{u}} (q : A ⟶ B)
    [IsAffine A] [IsAffine B] (M : A.Modules) (hM : M.IsQuasicoherent) :
    ((Scheme.Modules.pushforward q).obj M).IsQuasicoherent := by
  set φ : Γ(B, ⊤) ⟶ Γ(A, ⊤) := Scheme.Hom.appTop q with hφ
  have hM' : ((Scheme.Modules.pushforward A.isoSpec.hom).obj M).IsQuasicoherent :=
    pushforward_iso_preserves_qcoh A.isoSpec M hM
  have hstep : ((Scheme.Modules.pushforward (Spec.map φ)).obj
      ((Scheme.Modules.pushforward A.isoSpec.hom).obj M)).IsQuasicoherent :=
    isQuasicoherent_pushforward_specMap φ _ hM'
  have hnat : A.isoSpec.hom ≫ Spec.map φ = q ≫ B.isoSpec.hom :=
    Scheme.isoSpec_hom_naturality q
  have h1 : ((Scheme.Modules.pushforward (q ≫ B.isoSpec.hom)).obj M).IsQuasicoherent := by
    refine (SheafOfModules.isQuasicoherent.{u} (Spec Γ(B, ⊤)).ringCatSheaf).prop_of_iso ?_ hstep
    exact ((Scheme.Modules.pushforwardComp A.isoSpec.hom (Spec.map φ)).app M) ≪≫
      (Scheme.Modules.pushforwardCongr hnat).app M
  have h2 : ((Scheme.Modules.pushforward B.isoSpec.hom).obj
      ((Scheme.Modules.pushforward q).obj M)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent.{u} (Spec Γ(B, ⊤)).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pushforwardComp q B.isoSpec.hom).app M).symm h1
  refine (SheafOfModules.isQuasicoherent.{u} B.ringCatSheaf).prop_of_iso ?_
    (pushforward_iso_preserves_qcoh B.isoSpec.symm _ h2)
  exact ((Scheme.Modules.pushforwardComp B.isoSpec.hom B.isoSpec.inv).app _) ≪≫
    (Scheme.Modules.pushforwardCongr B.isoSpec.hom_inv_id).app _ ≪≫
    (Scheme.Modules.pushforwardId B).app _

set_option synthInstance.maxHeartbeats 800000 in
-- The σ-indexed Čech product exceeds the default instance-synthesis budget.
set_option maxHeartbeats 1000000 in
/-- **Every term of the relative Čech complex is quasi-coherent** — the discharge of the `h₂`/`h₃`
hypotheses of `cech_flatBaseChange_of_termsQuasicoherent`.

Over an affine base `S` and for a separated `f`, the degree-`p` term
`Čᵖ(𝒰, F) = f_*(∏_σ (j_σ)_*((j_σ)^* F))` is quasi-coherent.

Affineness of the intersection opens is a *hypothesis* `hσ` here rather than derived, only because
`coverInterOpen_isAffine` — which does derive it from `[IsSeparated f]` and `[IsAffine S]`, with no
separatedness assumption on `X` — is declared further down this file.  Callers pass
`fun σ => coverInterOpen_isAffine f 𝒰 σ`, so nothing extra is assumed downstream.  Three inputs,
all in this cone:

* the degree-`p` term *is* `f_*(pushPullObj F (backbone p))` — definitionally (`rfl`), the same
  identity `cechTerm_pushforward_acyclic` uses;
* the σ-product decomposition `pushPull_sigma_iso`, transported through `f_*` (which preserves
  the finite product), reduces to one factor;
* per factor, `f_*((j_σ)_* N) ≅ (j_σ ≫ f)_* N` (`pushforwardComp`) with `U_σ` affine (`hσ`) and
  `S` affine, so `isQuasicoherent_pushforward_of_isAffine` applies to a `(j_σ)^* F` that is
  quasi-coherent by `isQuasicoherent_pullback_opens`;
* reassembly over the affine base by `isQuasicoherent_pi_of_isAffine`.

Project-local. -/
theorem isQuasicoherent_cechComplex_X (f : X ⟶ S) [IsSeparated f] [IsAffine S]
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (hσ : ∀ {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀),
      IsAffineOpen (coverInterOpen 𝒰 σ))
    (F : X.Modules) (hF : F.IsQuasicoherent) (p : ℕ) :
    ((CechComplex f 𝒰 F).X p).IsQuasicoherent := by
  change ((Scheme.Modules.pushforward f).obj
    (pushPullObj F ((coverCechNerveOver 𝒰).obj (Opposite.op (SimplexCategory.mk p))))
      ).IsQuasicoherent
  refine (SheafOfModules.isQuasicoherent.{u} S.ringCatSheaf).prop_of_iso
    (((Scheme.Modules.pushforward f).mapIso (pushPull_sigma_iso 𝒰 F p)) ≪≫
      Limits.PreservesProduct.iso (Scheme.Modules.pushforward f) _).symm ?_
  refine isQuasicoherent_pi_of_isAffine (J := Fin (p + 1) → 𝒰.I₀) _ (fun σ => ?_)
  haveI : IsAffine (↑(coverInterOpen 𝒰 σ) : Scheme.{u}) := hσ σ
  refine (SheafOfModules.isQuasicoherent.{u} S.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.pushforwardComp (Scheme.Opens.ι (coverInterOpen 𝒰 σ)) f).app _).symm ?_
  exact isQuasicoherent_pushforward_of_isAffine _ _
    (isQuasicoherent_pullback_opens (coverInterOpen 𝒰 σ) F hF)

/-- **`Γ(g)` is flat for a flat `g` between affine schemes.**  Specialisation of
`Flat.flat_appLE` to `U = V = ⊤`, where `appLE` is `appTop` up to the identity restriction map.
Project-local. -/
theorem flat_appTop_of_flat (g : S' ⟶ S) [Flat g] [IsAffine S] [IsAffine S'] :
    (Scheme.Hom.appTop g).hom.Flat := by
  have h := Flat.flat_appLE g (U := ⊤) (isAffineOpen_top S) (V := ⊤) (isAffineOpen_top S')
    (by simp)
  rw [Scheme.Hom.appLE] at h
  simpa [Scheme.Hom.appTop] using h

/-- The `inv`-direction conjugation square, the one that composes correctly for pullbacks:
`g^* ⋙ (isoSpec_{S'}.inv)^* ≅ (isoSpec_S.inv)^* ⋙ (Spec Γg)^*`, from
`Scheme.isoSpec_inv_naturality`.  Project-local. -/
noncomputable def pullbackConjSpecInvIso (g : S' ⟶ S) [IsAffine S] [IsAffine S'] :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback S'.isoSpec.inv ≅
      Scheme.Modules.pullback S.isoSpec.inv ⋙
        Scheme.Modules.pullback (Spec.map (Scheme.Hom.appTop g)) :=
  Scheme.Modules.pullbackComp S'.isoSpec.inv g ≪≫
    Scheme.Modules.pullbackCongr (Scheme.isoSpec_inv_naturality g).symm ≪≫
    (Scheme.Modules.pullbackComp (Spec.map (Scheme.Hom.appTop g)) S.isoSpec.inv).symm

/-- **FLAT BASE CHANGE PRESERVES KERNELS OF QUASI-COHERENT MAPS, over an affine base.**  For a
flat `g : S' ⟶ S` between affine schemes and any `ψ : A ⟶ B` with `A`, `B` quasi-coherent,
`g^*` preserves `ker ψ`.  This is the general-`g` form of
`tildePullback_preservesKernel_of_essImage`, and — paired with
`mapHomologicalComplexHomologyIso_of_preservesKernel` — it is a complete substitute for
`pullback_preservesFiniteLimits` at every place the Čech flat-base-change proof uses it.

Route, in three moves.  (1) Transport `ψ` to the `Spec Γ(S,⊤)` side along `(isoSpec.inv)^*`;
quasi-coherence survives, by `pullback_isQuasicoherent_hom`.  (2) There the kernel is preserved by
`tildePullback_preservesKernel_of_essImage`, since `Γ(g)` is flat (`flat_appTop_of_flat`) and
quasi-coherent modules over an affine lie in the tilde essential image.  (3) Move back: the
conjugating functors are pullbacks along isomorphisms, hence equivalences
(`Modules.pullback_iso_isEquivalence`), so they both preserve the limit *and*, being fully
faithful, reflect it — which lets `preservesLimit_of_reflects_of_preserves` cancel the right-hand
factor off the composite rewritten by `pullbackConjSpecInvIso`.

No mono-preservation and no stalk model appear anywhere in this chain.  Project-local. -/
theorem pullback_preservesKernel_of_isQuasicoherent (g : S' ⟶ S) [Flat g]
    [IsAffine S] [IsAffine S'] {A B : S.Modules} (ψ : A ⟶ B)
    (hA : A.IsQuasicoherent) (hB : B.IsQuasicoherent) :
    Limits.PreservesLimit (Limits.parallelPair ψ 0) (Scheme.Modules.pullback g) := by
  set T := Scheme.Modules.pullback S.isoSpec.inv with hT
  haveI hqA : ((Scheme.Modules.pullback S.isoSpec.inv).obj A).IsQuasicoherent :=
    pullback_isQuasicoherent_hom _ _ hA
  haveI hqB : ((Scheme.Modules.pullback S.isoSpec.inv).obj B).IsQuasicoherent :=
    pullback_isQuasicoherent_hom _ _ hB
  haveI hspec : Limits.PreservesLimit (Limits.parallelPair (T.map ψ) 0)
      (Scheme.Modules.pullback (Spec.map (Scheme.Hom.appTop g))) :=
    tildePullback_preservesKernel_of_essImage _ (flat_appTop_of_flat g) _
      (essImage_tilde_of_isQuasicoherent _ hqA) (essImage_tilde_of_isQuasicoherent _ hqB)
  haveI hTeq := Modules.pullback_iso_isEquivalence S.isoSpec.symm
  haveI hT'eq := Modules.pullback_iso_isEquivalence S'.isoSpec.symm
  haveI : (Scheme.Modules.pullback S'.isoSpec.inv).Full := hT'eq.full
  haveI : (Scheme.Modules.pullback S'.isoSpec.inv).Faithful := hT'eq.faithful
  haveI : T.IsEquivalence := hTeq
  haveI : Limits.PreservesLimit (Limits.parallelPair ψ 0) T := inferInstance
  haveI : Limits.PreservesLimit (Limits.parallelPair ψ 0 ⋙ T)
      (Scheme.Modules.pullback (Spec.map (Scheme.Hom.appTop g))) :=
    Limits.preservesLimit_of_iso_diagram _
      (Limits.parallelPair.ext (Iso.refl _) (Iso.refl _) :
        Limits.parallelPair (T.map ψ) 0 ≅ Limits.parallelPair ψ 0 ⋙ T)
  haveI : Limits.PreservesLimit (Limits.parallelPair ψ 0)
      (T ⋙ Scheme.Modules.pullback (Spec.map (Scheme.Hom.appTop g))) :=
    Limits.comp_preservesLimit _ _
  haveI : Limits.PreservesLimit (Limits.parallelPair ψ 0)
      (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback S'.isoSpec.inv) :=
    Limits.preservesLimit_of_natIso _ (pullbackConjSpecInvIso g).symm
  exact Limits.preservesLimit_of_reflects_of_preserves (Scheme.Modules.pullback g)
    (Scheme.Modules.pullback S'.isoSpec.inv)

/-! ### The consumer needs ONE kernel, not global exactness

This is the second half of the reduction, and it is what makes the tilde-image restriction
usable rather than merely true.  Mathlib's homology comparison `ShortComplex.mapHomologyIso`
does **not** require `F.PreservesHomology`: it requires `F.PreservesLeftHomologyOf S` for the
one short complex `S` at hand.  And a left homology datum of `S` is preserved as soon as `F`
preserves *the kernel of `S.g`* — the cokernel half of `LeftHomologyData.IsPreservedBy` is free
for a left adjoint (`pullback_preservesFiniteColimits`).

So the chain `PreservesFiniteLimits ⟸ PreservesMonomorphisms` that the older revisions of this
file treated as the only route is a detour: the Čech consumer never needs `g^*` to be exact on
all of `S.Modules`, only to preserve the single kernel appearing in each degree, where the
objects are quasi-coherent. -/

/-- **Left-homology preservation from a single kernel.**  For an additive, right-exact `F`
between abelian categories and a *fixed* short complex `S`, preserving the kernel of `S.g`
already gives `F.PreservesLeftHomologyOf S`, hence `ShortComplex.mapHomologyIso`.  Project-local:
mathlib has `PreservesLeftHomologyOf.mk'` (from one *datum*) but not this form, which is the one
a consumer can discharge, since `parallelPair S.g 0` is a diagram it can name. -/
theorem preservesLeftHomologyOf_of_preservesKernel {C D : Type*} [Category.{u} C] [Category.{u} D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteColimits F]
    (S : ShortComplex C) [Limits.PreservesLimit (Limits.parallelPair S.g 0) F] :
    F.PreservesLeftHomologyOf S :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩⟩

/-- **Complex-level homology comparison from ONE kernel per degree.**  The weakening of
`mapHomologicalComplexHomologyIso` that this file's flat-base-change consumer can actually
discharge: instead of the global `[F.PreservesHomology]`, it asks only that `F` preserve the
kernel of the degree-`i` differential-out `(K.sc i).g`.  Everything else is
`preservesLeftHomologyOf_of_preservesKernel` plus the same
`ShortComplex.mapHomologyIso (K.sc i) F` as the strong version — the degree-`i` short complex of
`(F.mapHomologicalComplex c).obj K` is definitionally `F` applied to `K.sc i`.

This is the declaration that removes `pullback_preservesMonomorphisms` from the critical path:
`Rⁱ f_* F` is the homology of a complex whose terms are quasi-coherent, and on quasi-coherent
objects the needed kernel is preserved by `tildePullback_preservesKernel`.  Project-local. -/
noncomputable def mapHomologicalComplexHomologyIso_of_preservesKernel {C D : Type*}
    [Category.{u} C] [Category.{u} D] [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]
    [Limits.PreservesFiniteColimits F]
    {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c) (i : ι)
    [Limits.PreservesLimit (Limits.parallelPair (K.sc i).g 0) F] :
    ((F.mapHomologicalComplex c).obj K).homology i ≅ F.obj (K.homology i) :=
  haveI : F.PreservesLeftHomologyOf (K.sc i) :=
    preservesLeftHomologyOf_of_preservesKernel F (K.sc i)
  ShortComplex.mapHomologyIso (K.sc i) F

/-- **Flat base change has left-adjoint pullback**, hence `g^*` preserves finite
colimits (free: `g^* = pullback g` is a left adjoint). -/
instance pullback_preservesFiniteColimits (g : S' ⟶ S) :
    Limits.PreservesFiniteColimits (Scheme.Modules.pullback g) := inferInstance

/-- **Reduction of flat left-exactness to mono-preservation.**  For any `g`, if the module
pullback `g^*` preserves monomorphisms then it preserves finite limits: it is additive and
right exact (a left adjoint), so `preservesFiniteLimits_of_preservesMonomorphisms` applies.
This is the *whole* categorical content of `pullback_preservesFiniteLimits`; the residual
mathematics is the single statement `Mono (g^* ι)` for a mono `ι`, i.e. that flat pullback
does not destroy injections (Stacks 00HL / 01BG stalkwise).  Project-local. -/
theorem pullback_preservesFiniteLimits_of_preservesMonomorphisms (g : S' ⟶ S)
    (h : (Scheme.Modules.pullback g).PreservesMonomorphisms) :
    Limits.PreservesFiniteLimits (Scheme.Modules.pullback g) :=
  haveI := h
  preservesFiniteLimits_of_preservesMonomorphisms (Scheme.Modules.pullback g)

/-- **Flat pullback preserves monomorphisms** (OPEN — the sole residual content of flat
left-exactness, after `pullback_preservesFiniteLimits_of_preservesMonomorphisms`).

The statement is true for *arbitrary* `𝒪_S`-modules, not just quasi-coherent ones, and the
only proof is stalkwise: for `x : S'` the stalk of `g^* M` is
`M_{g(x)} ⊗_{𝒪_{S,g(x)}} 𝒪_{S',x}`, the stalk map `𝒪_{S,g(x)} ⟶ 𝒪_{S',x}` of a flat `g` is
flat (`AlgebraicGeometry.Flat.iff_flat_stalkMap`), and a flat base change preserves
injections; mono in `S'.Modules` is then detected on stalks
(`TopCat.Presheaf.mono_of_stalk_mono` through the faithful `Scheme.Modules.toPresheaf`, as in
`Modules.mono_of_injective_app_of_isBasis`).

**Why this is not discharged here, stated precisely so the next session does not re-derive
the dead ends.**  Mathlib defines `SheafOfModules.pullback` as `(pushforward φ).leftAdjoint`
and gives it *no* pointwise description; `SheafOfModules.pullbackIso` factors it as
`forget ⋙ PresheafOfModules.pullback φ.hom ⋙ PresheafOfModules.sheafification`, whose outer
two factors are left exact in mathlib already (`SheafOfModules.Finite.forgetPreservesFiniteLimits`
and the `PreservesFiniteLimits (sheafification α)` instance, both of which *do* synthesise on
the scheme site — checked), but whose middle factor `PresheafOfModules.pullback` is again
only a left adjoint with no formula.  So the missing input is the same either way: a stalk (or
affine-section) model of the module pullback.

Two routes that do **not** work, and why:
* the *affine* section formula `Scheme.Modules.pullback_app_isoTensor` (Picard/QuotScheme.lean)
  does give `Γ(g^* N, U) ≅ Γ(N, V) ⊗_{Γ(S,V)} Γ(S',U)` and would combine with
  `Modules.mono_of_injective_app_of_isBasis` — but it carries `[N.IsQuasicoherent]`, which the
  instance's statement (all modules) does not, and over an affine base `Scheme.Modules` is
  *not* `ModuleCat Γ(S,⊤)`, so quasi-coherence cannot be dropped from that route;
* there is no mathlib "right exact + preserves monos ⟹ exact" gap any more — that is closed
  above by `preservesFiniteLimits_of_preservesMonomorphisms` — so the categorical glue is
  *not* what is missing.  The whole obligation is now this one mono statement.

**WHAT IS DISCHARGED, and how little is left.**  Three of the four ingredients now exist,
sorry-free:
* the *open-immersion* case, `Modules.pullback_preservesMonomorphisms_of_isOpenImmersion` above
  (there `g^*` is the sectionwise `restrictFunctor`);
* *cover-locality*, `Modules.mono_of_mono_restrict` above: mono-preservation may be checked
  after restricting to an affine cover of the **source** `S'`, and on an affine `W ⊆ S'` with
  `g(W) ⊆ V` affine in `S` the map `W.ι ≫ g` factors through `V` with `Flat.flat_appLE` making
  that factor `Spec` of a flat ring map;
* the *affine* case **on the tilde image**, `tildePullback_preservesFiniteLimits` below — for a
  flat ring map `φ`, `g^* ∘ (~)` is exact, because `pullback_spec_tilde_iso` identifies it with
  `(~) ∘ extendScalars φ` and both factors are exact
  (`ModuleCat.preservesFiniteLimits_extendScalars_of_flat` for flat `φ`, and
  `tildePreservesFiniteLimits` — proved this session in `Cohomology/TildeExactness.lean`).

**WHAT IS STILL MISSING, AND WHY YOU SHOULD NOT PAY FOR IT** (revised run 0068 r1).  The affine
case is available only *on the tilde image*, i.e. for quasi-coherent modules, while
`PreservesMonomorphisms` quantifies over **all** `𝒪_S`-modules; over an affine base
`Scheme.Modules` is strictly larger than `ModuleCat Γ(S, ⊤)`, since `tilde` is fully faithful but
not essentially surjective.  Closing that gap needs either
(a) a mono-preservation statement for the affine pullback on arbitrary modules — the stalk model
    again, now only over an affine base, or
(b) mono-preservation for arbitrary modules from the quasi-coherent case, which would need the
    quasi-coherent objects to generate — false in general.

**Neither is worth attempting, because the obligation was mis-scoped.**  Every consumer in this
file instantiates flat exactness at quasi-coherent objects, and there it is now *proved*:
`pullback_preservesKernel_of_isQuasicoherent`.  Two observations did it, and both are downstream:
cone-cancellation (`preservesLimit_comp_cancel`) turns "the composite `(~) ⋙ g^*` is exact" into
"`g^*` is exact on tilde-shaped diagrams", the fullness of `tilde` upgrades that to *all* maps of
quasi-coherent modules, and `ShortComplex.mapHomologyIso` never wanted global exactness in the
first place — one kernel per degree suffices.

So this declaration is a **monument, not a frontier**: keep it for the reduction's legibility,
do not prove it, and route new work through the `_of_isQuasicoherent` forms.  If you believe you
need the arbitrary-module statement, check first what your consumer instantiates it at. -/
theorem pullback_preservesMonomorphisms (g : S' ⟶ S) [Flat g] :
    (Scheme.Modules.pullback g).PreservesMonomorphisms := sorry

/-- **Flat implies `g^*` is left-exact.**  Now a two-line derivation: `g^*` is additive and
right exact (a left adjoint, `pullback_preservesFiniteColimits`), so by
`pullback_preservesFiniteLimits_of_preservesMonomorphisms` left exactness follows from
mono-preservation, which for a flat `g` is `pullback_preservesMonomorphisms`.

**DELIBERATELY NOT AN `instance`.**  It was one until this revision, and that was the worse
choice: as an instance it was picked up by typeclass synthesis at arbitrary sites, so any
declaration *quantifying over* it reported clean axioms while every *synthesis site* silently
acquired `sorryAx` — the leak the AJC ledger warns about.  As a plain theorem the dependency is
visible in every proof term that uses it (`haveI := pullback_preservesFiniteLimits g` below),
and no declaration acquires `sorryAx` without naming it.  Do **not** restore the `instance`
attribute before `pullback_preservesMonomorphisms` is proved; once it is, the attribute is free
and harmless.

The leak now has a single named carrier, `pullback_preservesMonomorphisms`, whose statement is
one line of mathematics (flat base change preserves injections, stalkwise) rather than a
three-functor sheafification argument.  Measure at a synthesis site, e.g.
`scripts/axiom-frontier.lean`'s `leakProbe_pullback_finiteLimits`. -/
theorem pullback_preservesFiniteLimits (g : S' ⟶ S) [Flat g] :
    Limits.PreservesFiniteLimits (Scheme.Modules.pullback g) :=
  pullback_preservesFiniteLimits_of_preservesMonomorphisms g
    (pullback_preservesMonomorphisms g)

/-- **Flat implies `g^*` preserves homology**, derived from left-exactness together with
left-adjointness via `Functor.preservesHomologyOfExact`.  Not an `instance`, for the same
reason as `pullback_preservesFiniteLimits`: its only unproved input is
`pullback_preservesMonomorphisms`, and that dependency should be visible rather than
synthesised. -/
theorem pullback_preservesHomology (g : S' ⟶ S) [Flat g] :
    (Scheme.Modules.pullback g).PreservesHomology :=
  haveI := pullback_preservesFiniteLimits g
  Functor.preservesHomologyOfExact _

/-- **`g^*` commutes with Čech homology** (flat exactness, at the level of complexes).
A specialisation of `mapHomologicalComplexHomologyIso` to `g^* = pullback g`, which is
additive and, for `g` flat, preserves homology. -/
noncomputable def pullback_mapHC_homologyIso (g : S' ⟶ S) [Flat g]
    (K : CochainComplex S.Modules ℕ) (i : ℕ) :
    (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology i
      ≅ (Scheme.Modules.pullback g).obj (K.homology i) :=
  haveI := pullback_preservesHomology g
  mapHomologicalComplexHomologyIso (Scheme.Modules.pullback g) K i

/-- **`g^*` commutes with the homology of a QUASI-COHERENT complex — with no open input.**  The
`sorry`-free replacement for `pullback_mapHC_homologyIso`, and the reason the flat-exactness leaf
is off the critical path.  It asks for exactly the two things the Čech complex supplies:
an affine base and quasi-coherence of the two terms that meet in degree `i`
(`K.X i` and `K.X (next i)`, which are `(K.sc i).X₂` and `(K.sc i).X₃` definitionally).

Compare `pullback_mapHC_homologyIso`, whose `[Flat g]` route runs through
`pullback_preservesHomology → pullback_preservesFiniteLimits → pullback_preservesMonomorphisms`
and so inherits that leaf's `sorryAx`.  Here the same conclusion comes from
`pullback_preservesKernel_of_isQuasicoherent` (the kernel of `(K.sc i).g`) fed into
`mapHomologicalComplexHomologyIso_of_preservesKernel`.  Project-local. -/
noncomputable def pullback_mapHC_homologyIso_of_isQuasicoherent (g : S' ⟶ S) [Flat g]
    [IsAffine S] [IsAffine S'] (K : CochainComplex S.Modules ℕ) (i : ℕ)
    (h₂ : (K.sc i).X₂.IsQuasicoherent) (h₃ : (K.sc i).X₃.IsQuasicoherent) :
    (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology i
      ≅ (Scheme.Modules.pullback g).obj (K.homology i) :=
  haveI := pullback_preservesKernel_of_isQuasicoherent g (K.sc i).g h₂ h₃
  mapHomologicalComplexHomologyIso_of_preservesKernel (Scheme.Modules.pullback g) K i

/-! ## Additive functors and the alternating coface complex

The relative Čech complex `CechComplex` is, by construction
(`relativeCechComplexOfNerve`), the alternating coface-map cochain complex of a
cosimplicial object.  The base change `cechComplex_baseChange_iso` must move the
degreewise pullback `g^*` *inside* this `alternatingCofaceMapComplex` construction.  The
following two declarations package exactly that move at the cosimplicial level, with no
reference to schemes: an additive functor `F` commutes with the alternating coface map
complex, naturally in the cosimplicial variable. -/

section AlternatingCoface

open AlgebraicTopology

variable {C D : Type*} [Category.{u} C] [Category.{u} D] [Preadditive C] [Preadditive D]

/-- The degree-`n` differential of the alternating coface complex is the alternating sum
`objD`. -/
private theorem alternatingCofaceMapComplex_d
    (Y : CosimplicialObject C) (n : ℕ) :
    ((alternatingCofaceMapComplex C).obj Y).d n (n + 1)
      = AlternatingCofaceMapComplex.objD Y n := by
  simp only [alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj, CochainComplex.of_d]

/-- **An additive functor commutes with the alternating coface differential.** For an
additive functor `F : C ⥤ D` and a cosimplicial object `Y`, applying `F` to the
degree-`n` alternating coface differential `objD Y n = ∑ᵢ (-1)ⁱ • Yδᵢ` equals the
alternating coface differential of the post-composed cosimplicial object `Y ⋙ F`. This is
`F.map_sum` together with `Functor.map_zsmul` (both available since `F` is additive). -/
theorem map_alternatingCofaceMapComplex_objD (F : C ⥤ D) [F.Additive]
    (Y : CosimplicialObject C) (i : ℕ) :
    F.map (AlternatingCofaceMapComplex.objD Y i)
      = AlternatingCofaceMapComplex.objD
          (((CosimplicialObject.whiskering C D).obj F).obj Y) i := by
  rw [AlternatingCofaceMapComplex.objD, AlternatingCofaceMapComplex.objD, Functor.map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Functor.map_zsmul]
  rfl

/-- **Additive functors commute with `alternatingCofaceMapComplex`.** For an additive
functor `F : C ⥤ D` and a cosimplicial object `Y` in `C`, applying `F` degreewise to the
alternating coface map cochain complex of `Y` yields the alternating coface map cochain
complex of the post-composed cosimplicial object `F ∘ Y`:
`F.mapHomologicalComplex (alternatingCofaceMapComplex Y) ≅ alternatingCofaceMapComplex (F ∘ Y)`.
The degreewise components are identities (the degree-`n` terms are `F.obj (Y.obj [n])` on
both sides) and the differential compatibility is `map_alternatingCofaceMapComplex_objD`.
This is what pushes `g^*` into the relative Čech complex `relativeCechComplexOfNerve`. -/
private noncomputable def mapAlternatingCofaceMapComplexIso (F : C ⥤ D) [F.Additive]
    (Y : CosimplicialObject C) :
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((alternatingCofaceMapComplex C).obj Y)
      ≅ (alternatingCofaceMapComplex D).obj
          (((CosimplicialObject.whiskering C D).obj F).obj Y) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro i j (rfl : i + 1 = j)
    have h : F.map (((alternatingCofaceMapComplex C).obj Y).d i (i + 1))
        = ((alternatingCofaceMapComplex D).obj
            (((CosimplicialObject.whiskering C D).obj F).obj Y)).d i (i + 1) := by
      rw [alternatingCofaceMapComplex_d, alternatingCofaceMapComplex_d]
      exact map_alternatingCofaceMapComplex_objD F Y i
    rw [Functor.mapHomologicalComplex_obj_d, h]
    erw [Category.id_comp, Category.comp_id])

/-- **An isomorphism of alternating coface complexes from COFACE compatibility alone.**

`(alternatingCofaceMapComplex C).mapIso` needs a *cosimplicial* isomorphism: a degreewise family
plus naturality in **every** simplex morphism `φ : ⦋n⦌ ⟶ ⦋m⦌`, codegeneracies included.  But the
cochain complex it produces never mentions anything except the cofaces — its differential is
`objD Y n = ∑ᵢ (-1)ⁱ • Y.δ i` — so that much data already determines the same isomorphism of
complexes.  This lemma asks for exactly that much.

**Why this is a reduction and not a convenience.**  The obligation it replaces is what has kept
`twisted_cech_nerve_iso` open.  In *this tree* the Čech nerve's coface has a σ-coordinate formula
— `backboneIncl_nerveδ` (`CechSectionIdentificationLegMid1`) composed with
`pushPull_sigma_iso_π_incl` (`CechSectionIdentificationLeg`) — and both are stated for `δ k`
only; no general-`φ` analogue exists anywhere in the workspace or in mathlib (mathlib's
`Arrow.cechNerve` has `mapCechNerve` and the Čech adjunction, and no lemma computing a general
structure map in coordinates).  So a naturality obligation phrased for all `φ` is out of reach of
the tree's own lemmas, while the same obligation phrased for `δ` is one rewrite away from them.
Weakening the *interface* is therefore what makes the residue reachable — the same move as
`cechComplex_baseChange_iso_of_cosimplicialIso`, one level finer.

Pure category theory: no additivity of any functor, no abelian structure, and no relation between
`Y` and `Z` beyond the supplied data.  Project-local. -/
private theorem objD_comm_of_delta {Y Z : CosimplicialObject C}
    (e : ∀ n : ℕ, Y.obj (SimplexCategory.mk n) ≅ Z.obj (SimplexCategory.mk n))
    (hδ : ∀ (n : ℕ) (k : Fin (n + 2)), (e n).hom ≫ Z.δ k = Y.δ k ≫ (e (n + 1)).hom) (n : ℕ) :
    (e n).hom ≫ AlternatingCofaceMapComplex.objD Z n
      = AlternatingCofaceMapComplex.objD Y n ≫ (e (n + 1)).hom := by
  rw [AlternatingCofaceMapComplex.objD, AlternatingCofaceMapComplex.objD,
    Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  exact congrArg _ (hδ n k)

noncomputable def alternatingCofaceComplexIsoOfDelta (Y Z : CosimplicialObject C)
    (e : ∀ n : ℕ, Y.obj (SimplexCategory.mk n) ≅ Z.obj (SimplexCategory.mk n))
    (hδ : ∀ (n : ℕ) (k : Fin (n + 2)), (e n).hom ≫ Z.δ k = Y.δ k ≫ (e (n + 1)).hom) :
    (alternatingCofaceMapComplex C).obj Y ≅ (alternatingCofaceMapComplex C).obj Z :=
  HomologicalComplex.Hom.isoOfComponents (fun n => e n) (by
    rintro i j (rfl : i + 1 = j)
    rw [alternatingCofaceMapComplex_d, alternatingCofaceMapComplex_d]
    exact objD_comm_of_delta e hδ i)

end AlternatingCoface

/-- **The degreewise pullback of the relative Čech complex, in alternating-coface form.**
Specialising `mapAlternatingCofaceMapComplexIso` to `F = g^* = Scheme.Modules.pullback g`
and the push-forward cosimplicial object underlying `CechComplex f 𝒰 F`, this identifies
`g^*` applied degreewise to `Č•(𝒰, F)` with the alternating coface complex of the
cosimplicial object obtained by post-composing the dropped Čech nerve with `f_*` then `g^*`.
This is the first step towards `cechComplex_baseChange_iso`: it moves the degreewise pullback
inside the `alternatingCofaceMapComplex` construction, reducing the remaining content to a
Beck–Chevalley natural isomorphism of the underlying cosimplicial objects
`(g^* ∘ f_* ∘ nerve) ≅ (f'_* ∘ g'^* ∘ nerve')`. -/
noncomputable def pullback_cechComplex_alternatingIso (f : X ⟶ S) (g : S' ⟶ S)
    (𝒰 : X.OpenCover) (F : X.Modules) :
    ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (CechComplex f 𝒰 F)
      ≅ (AlgebraicTopology.alternatingCofaceMapComplex S'.Modules).obj
          (((CosimplicialObject.whiskering S.Modules S'.Modules).obj
              (Scheme.Modules.pullback g)).obj
            (((CosimplicialObject.whiskering X.Modules S.Modules).obj
                (Scheme.Modules.pushforward f)).obj
              (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)))) :=
  mapAlternatingCofaceMapComplexIso (Scheme.Modules.pullback g) _

/-- **Reduction of the Čech base change to a cosimplicial Beck–Chevalley isomorphism.** The
full Čech base-change isomorphism `cechComplex_baseChange_iso` follows formally from a single
natural isomorphism of the underlying cosimplicial objects: the cosimplicial object
`g^* ∘ f_* ∘ (Čech nerve of 𝒰, F)` is isomorphic to `f'_* ∘ g'^* ∘ (Čech nerve of 𝒰', g'^*F)`.
Given such an `e`, `Functor.mapIso (alternatingCofaceMapComplex …)` transports it to a chain
isomorphism whose differential compatibility is automatic, and pre-composing with
`pullback_cechComplex_alternatingIso` (which moves `g^*` inside the alternating-coface
construction) yields the claim. This isolates the substantive content of Stacks 02KG/02KH
— the Beck–Chevalley natural isomorphism `g^* ∘ f_* ≅ f'_* ∘ g'^*` whiskered through the
nerve, together with the affine reduction on `S` — into the single hypothesis `e`. -/
noncomputable def cechComplex_baseChange_iso_of_cosimplicialIso
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) (F : X.Modules)
    (e : ((CosimplicialObject.whiskering S.Modules S'.Modules).obj
            (Scheme.Modules.pullback g)).obj
          (((CosimplicialObject.whiskering X.Modules S.Modules).obj
              (Scheme.Modules.pushforward f)).obj
            (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)))
        ≅ ((CosimplicialObject.whiskering X'.Modules S'.Modules).obj
            (Scheme.Modules.pushforward f')).obj
          (CosimplicialObject.Augmented.drop.obj
            (CechNerve ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
              h.isoPullback.symm.hom) ((Scheme.Modules.pullback g').obj F)))) :
    ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (CechComplex f 𝒰 F)
      ≅ CechComplex f'
          ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
          ((Scheme.Modules.pullback g').obj F) :=
  pullback_cechComplex_alternatingIso f g 𝒰 F ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex S'.Modules).mapIso e

/-- **Degreewise affine reduction of the Čech base change** (Stacks 02KG).
Fix a cosimplicial degree `p`. On the standard affine model of the cover the `(p+1)`-fold
fibre power `U_{i₀…iₚ} = U_{i₀} ×_X ⋯ ×_X U_{iₚ}` is `Spec` of the finite affine intersection
`A := A_{i₀} ⊗_R ⋯ ⊗_R A_{iₚ}` of the coordinate rings of the cover members, and the X-level
cartesian square defining the base change along `g'` restricts, over `U_{i₀…iₚ}`, to the affine
pushout (tensor) square of rings `(φ : R ⟶ A, ψ : R ⟶ R', ρ : A ⟶ B, σ : R' ⟶ B)`. On that
affine model the degreewise Beck–Chevalley comparison
```
  g'^*(p_* p^* F)  ≅  p'_* p'^*(g'^* F)        over U_{i₀…iₚ}
```
IS the affine termwise base change `affinePushforwardPullbackBaseChange`
(`FlatBaseChange.lean`), assembled from the concrete tilde dictionaries
`pushforward_spec_tilde_iso` / `pullback_spec_tilde_iso` and the commutative-algebra
cancellation `cancelBaseChange` — *not* the canonical adjoint mate `pushforwardBaseChangeMap`.
These affine identifications are natural with respect to the index-omission maps that generate
the cosimplicial structure of the nerve (each coface is the ring inclusion that inserts the
omitted tensor factor), since `affinePushforwardPullbackBaseChange` is natural in the ring.

The same per-degree statement underlies both `cech_pushforward_baseChange_natIso` and
`twisted_cech_nerve_iso`: at each degree, after the affine identification of the fibre power,
the components of either natural isomorphism are this one.  It is a repackaging of the affine
termwise base change at the intersection ring `A`. -/
noncomputable def cech_degree_affine_baseChange {R A R' B : CommRingCat.{u}}
    (φ : R ⟶ A) (ψ : R ⟶ R') (ρ : A ⟶ B) (σ : R' ⟶ B)
    (h : CategoryTheory.IsPushout φ ψ ρ σ) (M : ModuleCat.{u} A) :
    (Scheme.Modules.pullback (Spec.map ψ)).obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)) ≅
      (Scheme.Modules.pushforward (Spec.map σ)).obj
        ((Scheme.Modules.pullback (Spec.map ρ)).obj (tilde M)) :=
  affinePushforwardPullbackBaseChange φ ψ ρ σ h M

/-! ## The abstract-to-affine `pushPullObj ≅ tilde` bridge

The two degreewise Beck–Chevalley isomorphisms (`cech_pushforward_baseChange_natIso`,
`twisted_cech_nerve_iso`) reduce, on the affine model of the cover, to
`cech_degree_affine_baseChange`.  The step still needed (Stacks 01I8 and 01BG) identifies the
abstract push–pull data of a fibre power with the `tilde`-model over `Spec`.  It is built in
two stages:

* **stage 1** (`pullbackRestrict_iso_tilde`): the restriction `p^* F = (V.ι)^* F` of a
  quasi-coherent `F` to an affine open `V` of `X`, *pushed forward along the whole-scheme iso*
  `V ≅ Spec Γ(X, V)` (`IsAffineOpen.isoSpec`), is `tilde` of its global sections over
  `Spec Γ(X, V)`. Quasi-coherence is preserved by pullback along the open immersion `V.ι`
  (`pullback_isQuasicoherent`/`isQuasicoherent_pullback_opens`) and by pushforward along the
  iso `isoSpec` (`pushforward_iso_preserves_qcoh`), so the affine structure theorem 01I8
  (`qcoh_iso_tilde_sections`, unconditional via the live instance
  `isIso_fromTildeΓ_of_quasicoherent`) applies.
* **stage 2** (`pushPullObj_pushforward_iso_tilde`): over the affine base `S = Spec R`,
  the pushed-forward push–pull object `f_*(p_* p^* F) = f_*((V.ι)_* (V.ι)^* F)` is
  `(Spec φ)_* (tilde N)`
  — collapse `f_* ∘ (V.ι)_*` to `(V.ι ≫ f)_*` by `pushforwardComp`, factor
  `V.ι ≫ f = isoSpec.hom ≫ Spec.map φ` (with `φ := Spec.preimage (fromSpec ≫ f)`,
  `Spec.map_preimage`), split off `(Spec.map φ)_*` by `pushforwardComp` again, and feed stage 1
  through `(Spec.map φ)_*`. This is exactly the form `cech_degree_affine_baseChange` consumes.

The ingredients are `isQuasicoherent_pullback_opens` (`CechTermAcyclic`),
`pushforward_iso_preserves_qcoh` (`OpenImmersionPushforward`), and the unconditional affine
structure theorem 01I8 `qcoh_iso_tilde_sections` (`QcohTildeSections`).
-/

/-- **Pullback preserves quasi-coherence** (Stacks 01BG, open case).  For an open `V` of `X` and a
quasi-coherent `F : X.Modules`, the restriction `(V.ι)^* F` is quasi-coherent on `V`.  This is the
open-immersion case the fibre-power projections of the {\v C}ech nerve require (each
`Y_n = U_{i₀} ∩ ⋯ ∩ U_{iₙ} ↪ X` is an open immersion); the general-morphism case is
`pullback_isQuasicoherent_hom` (`Cohomology/PullbackQuasicoherent.lean`), which localizes the
pullback along the preimage cover before transporting the presentation.  Restates
`isQuasicoherent_pullback_opens` (proved via `IsQuasicoherent.of_coversTop` on the preimage
cover). -/
theorem pullback_isQuasicoherent (V : X.Opens) (F : X.Modules) (hF : F.IsQuasicoherent) :
    ((Scheme.Modules.pullback V.ι).obj F).IsQuasicoherent :=
  isQuasicoherent_pullback_opens V F hF

/-- **Stage 1 of the bridge: `(V.ι)^* F` pushed to `Spec Γ(X,V)` is `tilde N`** (Stacks 01I8).
For a quasi-coherent `F : X.Modules` and an affine open `V` of `X`, the restriction `(V.ι)^* F`,
pushed forward along the whole-scheme iso `isoSpec : V ≅ Spec Γ(X, V)`, is canonically
isomorphic to the `tilde` of its module of global sections `N = Γ(Spec Γ(X,V), -)`.
The pullback is quasi-coherent
(`pullback_isQuasicoherent`) and quasi-coherence is preserved by the iso-pushforward
(`pushforward_iso_preserves_qcoh`), so the unconditional affine structure theorem 01I8
(`qcoh_iso_tilde_sections`, via the live instance `isIso_fromTildeΓ_of_quasicoherent`)
applies. -/
noncomputable def pullbackRestrict_iso_tilde (F : X.Modules) (hF : F.IsQuasicoherent)
    {V : X.Opens} (hV : IsAffineOpen V) :
    (Scheme.Modules.pushforward hV.isoSpec.hom).obj ((Scheme.Modules.pullback V.ι).obj F) ≅
      tilde (moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward hV.isoSpec.hom).obj ((Scheme.Modules.pullback V.ι).obj F))) :=
  haveI : ((Scheme.Modules.pushforward hV.isoSpec.hom).obj
      ((Scheme.Modules.pullback V.ι).obj F)).IsQuasicoherent :=
    pushforward_iso_preserves_qcoh hV.isoSpec ((Scheme.Modules.pullback V.ι).obj F)
      (pullback_isQuasicoherent V F hF)
  qcoh_iso_tilde_sections _

/-- **Stage 2 of the bridge: `f_*(p_* p^* F) ≅ (Spec φ)_* (tilde N)`** (Stacks 01I8, at the
pushed-forward level).  Over the affine base `S = Spec R`, with `V` an affine open of `X` and
`φ := Spec.preimage (fromSpec ≫ f) : R ⟶ Γ(X, V)` the ring map presenting the composite
`isoSpec.inv ≫ V.ι ≫ f = fromSpec ≫ f` as `Spec.map φ`, the pushed-forward push–pull object
`(pushforward f).obj (pushPullObj F (Over.mk V.ι))` is canonically isomorphic to
`(pushforward (Spec.map φ)).obj (tilde N)`.

The construction: collapse `f_* ∘ (V.ι)_*` to `(V.ι ≫ f)_*` by `pushforwardComp`; rewrite
`V.ι ≫ f = isoSpec.hom ≫ Spec.map φ` (from `Spec.map_preimage` and `isoSpec_inv_ι`) by
`pushforwardCongr`; split off `(Spec.map φ)_*` by `pushforwardComp` again (leaving the stage-1
domain `(isoSpec.hom)_* ((V.ι)^* F)`); then push stage 1 (`pullbackRestrict_iso_tilde`) through
`(Spec.map φ)_*`.  The right-hand side is exactly the form consumed by
`cech_degree_affine_baseChange`. -/
noncomputable def pushPullObj_pushforward_iso_tilde {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) (F : X.Modules) (hF : F.IsQuasicoherent)
    {V : X.Opens} (hV : IsAffineOpen V) :
    (Scheme.Modules.pushforward f).obj (pushPullObj F (Over.mk V.ι)) ≅
      (Scheme.Modules.pushforward (Spec.map (Spec.preimage (hV.fromSpec ≫ f)))).obj
        (tilde (moduleSpecΓFunctor.obj
          ((Scheme.Modules.pushforward hV.isoSpec.hom).obj
            ((Scheme.Modules.pullback V.ι).obj F)))) :=
  have heq : V.ι ≫ f = hV.isoSpec.hom ≫ Spec.map (Spec.preimage (hV.fromSpec ≫ f)) := by
    rw [Spec.map_preimage, ← IsAffineOpen.isoSpec_inv_ι hV, Category.assoc, Iso.hom_inv_id_assoc]
  (pushforwardComp V.ι f).app ((Scheme.Modules.pullback V.ι).obj F) ≪≫
    (pushforwardCongr heq).app ((Scheme.Modules.pullback V.ι).obj F) ≪≫
    (pushforwardComp hV.isoSpec.hom (Spec.map (Spec.preimage (hV.fromSpec ≫ f)))).symm.app
      ((Scheme.Modules.pullback V.ι).obj F) ≪≫
    (Scheme.Modules.pushforward (Spec.map (Spec.preimage (hV.fromSpec ≫ f)))).mapIso
      (pullbackRestrict_iso_tilde F hF hV)

/-- **Stage 2 over an abstract affine base** (Stacks 01I8, the generalization of
`pushPullObj_pushforward_iso_tilde` to an abstract `S`). For a *separated* `f : X ⟶ S` with `S`
an **abstract** affine scheme (`[IsAffine S]`, so `S` need not be a literal `Spec`), write
`e_S := S.isoSpec : S ≅ Spec Γ(S)`
for the canonical affine identification.  The pushed-forward push–pull object
`(pushforward f).obj (pushPullObj F (Over.mk V.ι))` is canonically isomorphic to the stage-2
`(Spec φ)_*(tilde N)` form, **transported back along `e_S⁻¹`** so it lands in `O_S`-modules rather
than `O_{Spec Γ(S)}`-modules, where `φ := Spec.preimage (hV.fromSpec ≫ (f ≫ e_S.hom))` presents
`(e_S ∘ f) ∘ (isoSpec ∘ j_V)` as `Spec φ`.

The composite `f ≫ e_S.hom : X ⟶ Spec Γ(S)` has a *literal* affine base, so
`pushPullObj_pushforward_iso_tilde` applies to it; then conjugate by `(pushforward e_S.inv)`
and collapse `pushforward e_S.hom ⋙ pushforward e_S.inv ≅ id` via
`pushforwardComp`/`pushforwardCongr`/`pushforwardId`.  This is the form
`pushPullObj_coverInter_baseChange` consumes, applied once for `f` and once for `f'`. -/
noncomputable def pushPullObj_pushforward_iso_tilde_affine [IsAffine S]
    (f : X ⟶ S) (F : X.Modules) (hF : F.IsQuasicoherent)
    {V : X.Opens} (hV : IsAffineOpen V) :
    (Scheme.Modules.pushforward f).obj (pushPullObj F (Over.mk V.ι)) ≅
      (Scheme.Modules.pushforward S.isoSpec.inv).obj
        ((Scheme.Modules.pushforward (Spec.map (Spec.preimage
            (hV.fromSpec ≫ (f ≫ S.isoSpec.hom))))).obj
          (tilde (moduleSpecΓFunctor.obj
            ((Scheme.Modules.pushforward hV.isoSpec.hom).obj
              ((Scheme.Modules.pullback V.ι).obj F))))) :=
  -- `collapse : (e_S⁻¹)_* ((f ≫ e_S)_* P) ≅ f_* P`, the `e_S` cancellation; take `.symm` to start
  -- from `f_* P`, then push the literal bridge through `(e_S⁻¹)_*`.
  ((Scheme.Modules.pushforward S.isoSpec.inv).mapIso
        ((Scheme.Modules.pushforwardComp f S.isoSpec.hom).symm.app
          (pushPullObj F (Over.mk V.ι))) ≪≫
      (Scheme.Modules.pushforwardComp S.isoSpec.hom S.isoSpec.inv).app
        ((Scheme.Modules.pushforward f).obj (pushPullObj F (Over.mk V.ι))) ≪≫
      (Scheme.Modules.pushforwardCongr S.isoSpec.hom_inv_id).app
        ((Scheme.Modules.pushforward f).obj (pushPullObj F (Over.mk V.ι))) ≪≫
      (Scheme.Modules.pushforwardId S).app
        ((Scheme.Modules.pushforward f).obj (pushPullObj F (Over.mk V.ι)))).symm ≪≫
    (Scheme.Modules.pushforward S.isoSpec.inv).mapIso
      (pushPullObj_pushforward_iso_tilde (f ≫ S.isoSpec.hom) F hF hV)

/-- **Čech intersection opens are affine** (separated case).  For a separated `f : X ⟶ S`
with `S` affine and an affine open cover `𝒰` of `X`, every finite nonempty fibre-power
intersection open `coverInterOpen 𝒰 σ = ⨅ k, (𝒰.f (σ k)).opensRange` is affine.  `X` is
separated over the terminal scheme (`f` separated and `S` affine — hence separated — so the
composite `terminal.from X = f ≫ terminal.from S` is separated), so the absolute diagonal of
`X` is a closed immersion, hence affine; finite intersections of affine opens of a scheme with
affine diagonal are affine (`IsAffineOpen.iInf`), and each member open is affine as the range of
an open immersion out of the affine `𝒰.X (σ k)` (`isAffineOpen_opensRange`).  This is the
affineness hypothesis needed by `pushPullObj_coverInter_baseChange`. -/
theorem coverInterOpen_isAffine (f : X ⟶ S) [IsSeparated f] [IsAffine S]
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)] {κ : Type} [Finite κ] [Nonempty κ]
    (σ : κ → 𝒰.I₀) : IsAffineOpen (coverInterOpen 𝒰 σ) := by
  -- `X` is separated over the terminal scheme: `terminal.from X = f ≫ terminal.from S`, with
  -- `f` separated and `terminal.from S` separated (`S` affine ⟹ `S.IsSeparated`).
  haveI hsep : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    exact IsSeparated.comp_iff.mpr ‹IsSeparated f›
  -- hence the absolute diagonal is a closed immersion (⟹ affine), unlocking `IsAffineOpen.iInf`.
  haveI : IsClosedImmersion (pullback.diagonal (terminal.from X)) :=
    IsSeparated.isClosedImmersion_diagonal
  exact IsAffineOpen.iInf (fun k => isAffineOpen_opensRange (𝒰.f (σ k)))

/-- **Restriction of the cartesian square over an affine intersection open is a (ring) pushout**
(Stacks 02KG).  Restricting the global
cartesian square `X' = X ×_S S' → X` over the Čech fibre-power intersection open
`V = coverInterOpen 𝒰 σ ↪ X` (open immersion `j_σ`) replaces `X` by `V` and `X'` by the fibre
product `X' ×_X V`, and the restricted square
```
  X' ×_X V --pullback.fst--> V
   |pullback.snd             |j_σ
   v                         v
  X'  --------g'------------> X
```
is cartesian.  This is the geometric half of the reduction: under `[IsSeparated f]`,
`[IsAffine S]`, `[IsAffine S']` and an affine cover, `V` is affine (`coverInterOpen_isAffine`)
and `X' ×_X V` is affine, so applying global sections turns this cartesian square of affines into
the cocartesian (pushout) square of rings `R → A_σ`, `R → R'`, `A_σ → A_σ ⊗_R R'` via the
affine-pullback ↔ ring-pushout equivalence `CommRingCat.isPushout_iff_isPushout` — exactly the
affine pushout square consumed by `cech_degree_affine_baseChange`.  The restricted square is a
pullback by construction (`IsPullback.of_hasPullback`). -/
theorem restrictedCartesianAffinePushout (g' : X' ⟶ X)
    (𝒰 : X.OpenCover) {κ : Type} (σ : κ → 𝒰.I₀) :
    IsPullback (pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (Scheme.Opens.ι (coverInterOpen 𝒰 σ)) g' :=
  (IsPullback.of_hasPullback g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).flip

/-- **LHS abstract → tilde for a single intersection open** (carved block
`lem:coverinter_lhs_iso_tilde`). Over the affine base `S = Spec R`, for a separated
`f : X ⟶ Spec R`, an affine open-immersion cover `𝒰` and a finite nonempty multi-index
`σ`, the intersection open `V = coverInterOpen 𝒰 σ` is affine
(`coverInterOpen_isAffine`) and the pushed-forward push–pull object
`f_*(pushPullObj F (Over.mk j_σ)) = f_*((j_σ)_* (j_σ)^* F)` is the affine pushforward
`(Spec φ)_*(tilde N)` of the tilde of its global sections, where `φ = Spec.preimage (fromSpec ≫ f)`
presents `f ∘ j_σ` as `Spec φ`.  This is the LHS comparison side of the per-intersection-open base
change; it is the altitude-2 bridge `pushPullObj_pushforward_iso_tilde` applied at the affine open
`V = coverInterOpen 𝒰 σ`.  Project-local; blueprint `lem:coverinter_lhs_iso_tilde`. -/
noncomputable def pushPullObj_coverInter_pushforward_iso_tilde {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) [IsSeparated f]
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent)
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    (Scheme.Modules.pushforward f).obj
        (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) ≅
      (Scheme.Modules.pushforward (Spec.map (Spec.preimage
          ((coverInterOpen_isAffine f 𝒰 σ).fromSpec ≫ f)))).obj
        (tilde (moduleSpecΓFunctor.obj
          ((Scheme.Modules.pushforward (coverInterOpen_isAffine f 𝒰 σ).isoSpec.hom).obj
            ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj F)))) :=
  pushPullObj_pushforward_iso_tilde f F hF (coverInterOpen_isAffine f 𝒰 σ)

/-- **The base-changed sections are the tensor base change of `N`** (carved block
`lem:coverinter_baseChanged_module_iso_tensor`).  For the affine pushout square of rings cut out by
restricting the cartesian base-change square over the affine intersection open `V = Spec A_σ`
(`φ : R ⟶ A_σ`, `ψ : R ⟶ R'`, `ρ : A_σ ⟶ B`, `σ' : R' ⟶ B` with corner `B ≅ A_σ ⊗_R R'`), the
base-changed module of sections `N' = (j'_σ)^*((g')^* F)` over the affine `V' = Spec B` is, as a
`B`-module restricted to `R'` (resp. read as the corner `B`-module `B ⊗_{A_σ} N`), the tensor base
change `N ⊗_R R' = R' ⊗_R N`.  This is precisely the module-level corner identification realised by
the inverse of `baseChangeCancelModuleIso`: `restrict_σ'(B ⊗_{A_σ} N) ≅ R' ⊗_R N`.  The geometric
wrapping (relating the geometric `Γ(V', (j'_σ)^*((g')^*F))` to `B ⊗_{A_σ} N` via the cartesian
pullback comparison and the affine tilde dictionary) is carried by the RHS leaf
`pushPullObj_coverInter_baseChanged_pushforward_iso_tilde`.  Project-local; blueprint
`lem:coverinter_baseChanged_module_iso_tensor` (module core). -/
noncomputable def coverInter_baseChanged_sections_iso_tensor {R A R' B : CommRingCat.{u}}
    (φ : R ⟶ A) (ψ : R ⟶ R') (ρ : A ⟶ B) (σ' : R' ⟶ B)
    (h : CategoryTheory.IsPushout φ ψ ρ σ') (N : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars σ'.hom).obj ((ModuleCat.extendScalars ρ.hom).obj N) ≅
      (ModuleCat.extendScalars ψ.hom).obj ((ModuleCat.restrictScalars φ.hom).obj N) :=
  (baseChangeCancelModuleIso φ ψ ρ σ' h N).symm

/-- For a finite family of opens, the lattice infimum has carrier the set intersection
(`⨅` over a `Finite` index is the finite intersection, which is again open).  Project-local
topology helper used by `coverInterOpen_baseChange_eq`. -/
private theorem coe_iInf_of_finite {Y : Scheme.{u}} {κ : Type} [Finite κ]
    (U : κ → Y.Opens) :
    (↑(⨅ k, U k) : Set Y) = ⋂ k, (↑(U k) : Set Y) := by
  apply subset_antisymm
  · exact Set.subset_iInter fun k => SetLike.coe_subset_coe.mpr (iInf_le U k)
  · have hopen : IsOpen (⋂ k, (↑(U k) : Set Y)) := isOpen_iInter_of_finite fun k => (U k).2
    have hO : (⟨⋂ k, (↑(U k) : Set Y), hopen⟩ : Y.Opens) ≤ ⨅ k, U k :=
      le_iInf fun k => Set.iInter_subset _ k
    exact SetLike.coe_subset_coe.mpr hO

/-- **The range of a base-changed cover member is the preimage of the original member's range.**
For the base-changed cover `𝒰' = (openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom`
of `X' = X ×_S S'`, the open `(𝒰'.f i).opensRange = (g')⁻¹((𝒰.f i).opensRange)`.  The member map
`𝒰'.f i` is the base change of the open immersion `𝒰.f i` along `g'` (the `openCoverOfLeft`
square, transported along the iso `X' ≅ pullback f g` to land on `g'`), so this is the
open-immersion base-change range identity
`IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback`.  Project-local; the per-member
content of `lem:coverinteropen_basechange_eq`. -/
private theorem coverOpen_baseChange_eq (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) (i : 𝒰.I₀) :
    (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom).f i).opensRange
      = g' ⁻¹ᵁ (𝒰.f i).opensRange := by
  -- expose the member of the base-changed cover as `oclf.f i ≫ (the iso)`
  have e1 : ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom).f i
      = (Scheme.Pullback.openCoverOfLeft 𝒰 f g).f i ≫ h.isoPullback.symm.hom := rfl
  -- mathlib's base-change square for `openCoverOfLeft` (cf. `Scheme.isPullback_of_openCover`)
  have hbase : IsPullback (pullback.fst (𝒰.f i ≫ f) g)
      ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).f i) (𝒰.f i) (pullback.fst f g) := by
    rw [Scheme.Pullback.openCoverOfLeft_f]
    refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback f g)
    · have hs : pullback.map (𝒰.f i ≫ f) g f g (𝒰.f i) (𝟙 S') (𝟙 S) (by simp) (by simp) ≫
          pullback.snd f g = pullback.snd (𝒰.f i ≫ f) g := by rw [pullback.lift_snd]; simp
      rw [hs]; exact IsPullback.of_hasPullback (𝒰.f i ≫ f) g
    · rw [pullback.lift_fst]
  -- transport along the iso `pullback f g ≅ X'` so the bottom edge becomes `g'`
  have hsq : IsPullback (pullback.fst (𝒰.f i ≫ f) g)
      (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom).f i)
      (𝒰.f i) g' := by
    refine hbase.of_iso (Iso.refl _) (Iso.refl _) h.isoPullback.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · rw [Iso.refl_hom, Category.id_comp]; exact e1.symm
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom]; exact h.isoPullback_inv_fst.symm
  haveI hoi : IsOpenImmersion
      (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom).f i) :=
    Scheme.Cover.map_prop
      ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom) i
  haveI hoiV : IsOpenImmersion (𝒰.f i) := Scheme.Cover.map_prop 𝒰 i
  -- the open-immersion base-change range identity for the cartesian square `hsq`
  have key := @AlgebraicGeometry.IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    X' X _ _ g' (pullback.fst (𝒰.f i ≫ f) g)
    (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom).f i)
    (𝒰.f i) hoiV hoi hsq ⊤
  rw [Scheme.Hom.preimage_top] at key
  rw [(@Scheme.Hom.image_top_eq_opensRange _ _ _ hoi).symm,
    (@Scheme.Hom.image_top_eq_opensRange _ _ (𝒰.f i) hoiV).symm]
  exact key

/-- **The base-changed cover intersection is the preimage of the intersection** (Stacks 02KG;
carved block `lem:coverinteropen_basechange_eq`).  For the base-changed cover
`𝒰' = (openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom` of `X' = X ×_S S'` and a
*finite* index family `σ : κ → 𝒰.I₀`, the Čech intersection open of `𝒰'` is the `g'`-preimage of
the intersection open of `𝒰`:
```
  coverInterOpen 𝒰' σ = (g')⁻¹(coverInterOpen 𝒰 σ).
```
Per member `coverOpen_baseChange_eq` gives the preimage identity, and preimage commutes with the
finite intersection (`coe_iInf_of_finite` + `Set.preimage_iInter`).  Finiteness of `κ` is genuinely
needed (the `Opens.map` frame hom preserves only *finite* meets); the Čech use is over
`Fin (n+1)`.  Project-local; blueprint `lem:coverinteropen_basechange_eq`. -/
theorem coverInterOpen_baseChange_eq (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) {κ : Type} [Finite κ] (σ : κ → 𝒰.I₀) :
    coverInterOpen ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom) σ
      = g' ⁻¹ᵁ coverInterOpen 𝒰 σ := by
  apply TopologicalSpace.Opens.ext
  rw [coverInterOpen, coverInterOpen, coe_iInf_of_finite, TopologicalSpace.Opens.map_coe,
    coe_iInf_of_finite, Set.preimage_iInter]
  refine Set.iInter_congr fun k => ?_
  have hk := coverOpen_baseChange_eq f g f' g' h 𝒰 (σ k)
  simp only [coverOpen]
  rw [hk, TopologicalSpace.Opens.map_coe]

/-- **Bare Beck–Chevalley mate** for the restricted cartesian square `IsPullback gV p' p g'`
(`gV ≫ p = p' ≫ g'`).  This is the canonical base-change natural transformation
`g'^* ∘ p_* ⟶ p'_* ∘ gV^*` obtained as the *mate* (Beck–Chevalley transform) — under the
`pullback ⊣ pushforward` adjunctions for `p` and `p'` — of the canonical pullback 2-isomorphism
`pullback g' ⋙ pullback p' ≅ pullback p ⋙ pullback gV` coming from `p' ≫ g' = gV ≫ p`.

This natural transformation always exists (no flatness, no open-immersion hypothesis): it is the
*comparison map* whose being an iso is the genuine Beck–Chevalley content.  It is a 6-line local
restatement of `canonicalBaseChangeMap`, originally written that way to avoid importing
`QuotScheme` — a precaution based on the false claim that that module carries `sorry`s.  Since run
0068 r3 this file *does* import it, and the two are definitionally equal (`cechOuterBC` below is
literally `canonicalBaseChangeMap`, by `rfl`), which is what closed the S-level cosimplicial leaf.
The local copy is kept because the open-immersion Stage-2 factorization lemmas below are stated
against it.  Project-local; blueprint `lem:openimm_beckchevalley` (mate). -/
noncomputable def openImmersion_bareBC {V V' : Scheme.{u}}
    (g' : X' ⟶ X) (p : V ⟶ X) (p' : V' ⟶ X') (gV : V' ⟶ V)
    (hsq : IsPullback gV p' p g') :
    pushforward p ⋙ Scheme.Modules.pullback g' ⟶
      Scheme.Modules.pullback gV ⋙ pushforward p' :=
  CategoryTheory.mateEquiv
    (pullbackPushforwardAdjunction p)
    (pullbackPushforwardAdjunction p')
    (((pullbackComp p' g') ≪≫
      pullbackCongr hsq.w.symm ≪≫
      (pullbackComp gV p).symm).hom)

/-- **Pullback telescope across the restricted cartesian square** (the pseudofunctor leg of the
open-immersion Beck–Chevalley).  Using only the pseudofunctor structure of `pullback`
(`pullbackComp`, `pullbackCongr`) and the square equation `p' ≫ g' = gV ≫ p`, the iterated
pullback `p'^*(g'^* F)` is canonically isomorphic to `gV^*(p^* F)`:
```
  p'^*(g'^* F) ≅ (p' ≫ g')^* F = (gV ≫ p)^* F ≅ gV^*(p^* F).
```
Sorry-free, build-cheap (no flatness, no affineness).  Together with `openImmersion_bareBC` this
collapses `openImmersion_beckChevalley` to the single obligation `IsIso (openImmersion_bareBC …)`.
Project-local; blueprint `lem:openimm_beckchevalley` (telescope). -/
noncomputable def openImmersion_bc_telescope {V V' : Scheme.{u}}
    (g' : X' ⟶ X) (p : V ⟶ X) (p' : V' ⟶ X') (gV : V' ⟶ V)
    (hsq : IsPullback gV p' p g') (F : X.Modules) :
    (Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback g').obj F) ≅
      (Scheme.Modules.pullback gV).obj ((Scheme.Modules.pullback p).obj F) :=
  ((pullbackComp p' g') ≪≫
      pullbackCongr hsq.w.symm ≪≫
      (pullbackComp gV p).symm).app F

/-- **The base-changed edge `p'` of the restricted cartesian square is an open immersion.**
For the cartesian square `hsq : IsPullback gV p' p g'` (so `p' : V' ⟶ X'` is the base change of
`p` along `g'`), if `p` is an open immersion then so is `p'` — open immersions are stable under
base change (`MorphismProperty.IsStableUnderBaseChange @IsOpenImmersion`).  This is the
open-immersion-ness of the *left* edge of the square that the sectionwise cover-refinement
route of `openImmersion_beckChevalley` (Stage 2) consumes: it is what lets
`pushforward p'` / `pullback p'`
be identified with restriction along `p'` (`restrictFunctorIsoPullback p'`) on the target side of
the bare Beck–Chevalley mate.  Project-local; blueprint `lem:openimm_beckchevalley` (left-edge
open-immersion side-condition). -/
theorem isOpenImmersion_of_isPullback_left {V V' : Scheme.{u}}
    (g' : X' ⟶ X) (p : V ⟶ X) (p' : V' ⟶ X') (gV : V' ⟶ V)
    (hsq : IsPullback gV p' p g') [IsOpenImmersion p] : IsOpenImmersion p' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq ‹IsOpenImmersion p›

/-! ## Stage-2 reduction: the bare mate factors as `unit ≫ iso`

The mate formula (`mateEquiv_apply`) exhibits `openImmersion_bareBC` at each object `c` as
```
  unit_{p'} (g'^*(p_* c)) ≫ p'_*(telescope-iso) ≫ p'_*(gV^*(counit_p c)).
```
For an *open immersion* `p`, the counit of the geometric adjunction
`pullback p ⊣ pushforward p` is an isomorphism — it is conjugate, under the
`leftAdjointUniq` comparison `restrictFunctorIsoPullback p`, to the counit of the
site-level `restrictAdjunction p`, invertible in Mathlib.  Hence the *only* non-iso
factor is the leading `p'`-unit, and `IsIso (bareBC.app c)` collapses to the single
node `IsIso (unit_{p'}.app (g'^*(p_* c)))` — "`g'^*(p_* c)` is in the essential image
of `p'_*`".  This is a strict sharpening of the blueprint Stage-2 chain
(`lem:openimm_bareBC_isIso`): the legs-are-restrictions reduction
(`lem:openimm_bareBC_legs_restriction`) is here replaced by the exact mate
factorization, so the member/assembly work only ever has to handle the unit. -/

set_option backward.isDefEq.respectTransparency false in
/-- **The geometric counit at an open immersion is an isomorphism.**  For an open
immersion `q`, the counit `q^*(q_* c) ⟶ c` of the geometric adjunction
`pullback q ⊣ pushforward q` is invertible: by
`Adjunction.leftAdjointUniq_hom_app_counit` it factors the counit of the site-level
`restrictAdjunction q` — an isomorphism in Mathlib (`restrictFunctorAdjCounitIso`) —
through the `leftAdjointUniq` comparison (`restrictFunctorIsoPullback q`, an iso).
Project-local; blueprint `lem:openimm_pullback_counit_isIso`. -/
theorem openImmersion_pullback_counit_isIso {V : Scheme.{u}} (q : V ⟶ X)
    [IsOpenImmersion q] (c : V.Modules) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction q).counit.app c) := by
  haveI hnat : IsIso ((Scheme.Modules.restrictAdjunction q).counit) :=
    inferInstanceAs (IsIso (Scheme.Modules.restrictFunctorAdjCounitIso q).hom)
  haveI happ : IsIso ((Scheme.Modules.restrictAdjunction q).counit.app c) :=
    NatIso.isIso_app_of_isIso _ c
  exact IsIso.of_isIso_fac_left (Adjunction.leftAdjointUniq_hom_app_counit
    (Scheme.Modules.restrictAdjunction q) (Scheme.Modules.pullbackPushforwardAdjunction q) c)

set_option backward.isDefEq.respectTransparency false in
/-- **Mate factorization of the bare Beck–Chevalley comparison.**  At each `c : V.Modules`
the mate `openImmersion_bareBC` is, per the `mateEquiv` formula, the `p'`-unit at
`g'^*(p_* c)` followed by `p'_*` of the three pullback-telescope iso components and
`p'_*(gV^*(-))` of the `p`-counit.  Every factor after the unit is an isomorphism.
Project-local; blueprint `lem:openimm_bareBC_isIso` (factorization). -/
theorem openImmersion_bareBC_app_eq {V V' : Scheme.{u}}
    (g' : X' ⟶ X) (p : V ⟶ X) (p' : V' ⟶ X') (gV : V' ⟶ V)
    (hsq : IsPullback gV p' p g') (c : V.Modules) :
    (openImmersion_bareBC g' p p' gV hsq).app c =
      (Scheme.Modules.pullbackPushforwardAdjunction p').unit.app
          ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pushforward p).obj c)) ≫
        (Scheme.Modules.pushforward p').map
          ((pullbackComp p' g').hom.app ((Scheme.Modules.pushforward p).obj c)) ≫
        (Scheme.Modules.pushforward p').map
          ((pullbackCongr hsq.w.symm).hom.app ((Scheme.Modules.pushforward p).obj c)) ≫
        (Scheme.Modules.pushforward p').map
          ((pullbackComp gV p).inv.app ((Scheme.Modules.pushforward p).obj c)) ≫
        (Scheme.Modules.pushforward p').map ((Scheme.Modules.pullback gV).map
          ((Scheme.Modules.pullbackPushforwardAdjunction p).counit.app c)) := by
  simp only [openImmersion_bareBC, mateEquiv_apply, Functor.id_obj]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **`IsIso bareBC` collapses to the unit node.**  Since the telescope components and the
`p`-counit factor (`openImmersion_pullback_counit_isIso`) are isomorphisms, the mate
`openImmersion_bareBC` is an isomorphism at `c` as soon as the `p'`-unit is one at
`g'^*(p_* c)` — i.e. as soon as `g'^*(p_* c)` lies in the essential image of `p'_*`.
Project-local; blueprint `lem:openimm_bareBC_isIso` (reduction). -/
theorem openImmersion_bareBC_app_isIso_of_unit {V V' : Scheme.{u}}
    (g' : X' ⟶ X) (p : V ⟶ X) (p' : V' ⟶ X') (gV : V' ⟶ V)
    (hsq : IsPullback gV p' p g') [IsOpenImmersion p] (c : V.Modules)
    (hu : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction p').unit.app
      ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pushforward p).obj c)))) :
    IsIso ((openImmersion_bareBC g' p p' gV hsq).app c) := by
  rw [openImmersion_bareBC_app_eq]
  haveI := hu
  haveI := openImmersion_pullback_counit_isIso p c
  infer_instance

/-- **Unit-iso from essential-image membership** (open-immersion case).  For an open
immersion `p'`, the pushforward `p'_*` is fully faithful (Mathlib instances on
`restrictAdjunction`), so by `Adjunction.isIso_unit_app_of_iso` the unit of
`pullback p' ⊣ pushforward p'` is an isomorphism at every module in the essential image
of `p'_*`.  Project-local; blueprint `lem:openimm_bareBC_isIso` (essential-image form). -/
theorem openImmersion_unit_isIso_of_essImage {V' : Scheme.{u}} (p' : V' ⟶ X')
    [IsOpenImmersion p'] (M : X'.Modules)
    (h : (Scheme.Modules.pushforward p').essImage M) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction p').unit.app M) := by
  obtain ⟨K, ⟨e⟩⟩ := h
  exact (Scheme.Modules.pullbackPushforwardAdjunction p').isIso_unit_app_of_iso e.symm

/-! ## Stage-2 assembly: essential-image membership is cover-local

The essential-image node is verified member-by-member on an open cover of `X'`.  The
engine is elementary: membership `M ∈ essImage p'_*` is equivalent (fully-faithful
`p'_*`) to invertibility of the `p'`-unit at `M`; transported to the site-level
`restrictAdjunction p'`, the unit's components are the plain presheaf restrictions
`M(U) → M(U ∩ ran p')`, so cover-conservativity (`isIso_iff_isIso_restrict`) applies
with NO pushforward/restriction commutation coherence: the restricted morphism again
has plain `M.presheaf.map` components, compared against the member datum through a
lattice identity of opens. -/

/-- Component of a restricted morphism of modules is the component at the image open.
Definitional. Project-local; blueprint `lem:essimage_pushforward_cover_local` (component). -/
theorem restrictFunctor_map_app {W : Scheme.{u}} (w : W ⟶ X') [IsOpenImmersion w]
    {M N : X'.Modules} (ψ : M ⟶ N) (O : W.Opens) :
    ((Scheme.Modules.restrictFunctor w).map ψ).app O = ψ.app (w ''ᵁ O) := rfl

/-- **Restriction maps of a pushforward-presented module are isomorphisms.**  If
`N : W.Modules` is isomorphic to a pushforward `(O₀.ι)_* K` from the open `O₀ ⊆ W`, then
for every open `O ⊆ W` the presheaf restriction `N(O) → N(O ⊓ O₀)` is an isomorphism: on
the pushforward side it is `K.presheaf.map` of the identity inclusion
`O₀.ι⁻¹(O ⊓ O₀) = O₀.ι⁻¹(O)` (an `eqToHom`), and the comparison iso conjugates.
Project-local; blueprint `lem:restrictionMap_isIso_of_essImage`. -/
theorem restrictionMap_isIso_of_essImage {W : Scheme.{u}} (O₀ : W.Opens)
    (N : W.Modules) (h : (Scheme.Modules.pushforward O₀.ι).essImage N) (O : W.Opens) :
    IsIso (N.presheaf.map (homOfLE (inf_le_left : O ⊓ O₀ ≤ O)).op) := by
  obtain ⟨K, ⟨e⟩⟩ := h
  have eP : ((Scheme.Modules.pushforward O₀.ι).obj K).presheaf ≅ N.presheaf :=
    (Scheme.Modules.toPresheaf W).mapIso e
  have hpre : Opposite.op (O₀.ι ⁻¹ᵁ O) = Opposite.op (O₀.ι ⁻¹ᵁ (O ⊓ O₀)) := by
    rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, inf_top_eq]
  haveI hK : IsIso
      ((((Scheme.Modules.pushforward O₀.ι).obj K).presheaf.map
        (homOfLE (inf_le_left : O ⊓ O₀ ≤ O)).op)) := by
    rw [Scheme.Modules.pushforward_obj_presheaf_map]
    have hcast : ((TopologicalSpace.Opens.map O₀.ι.base).map
        (homOfLE (inf_le_left : O ⊓ O₀ ≤ O))).op = eqToHom hpre := by
      apply Quiver.Hom.unop_inj
      apply Subsingleton.elim
    rw [hcast]
    exact Functor.map_isIso _ _
  have nat := eP.hom.naturality (homOfLE (inf_le_left : O ⊓ O₀ ≤ O)).op
  exact IsIso.of_isIso_fac_left nat.symm

set_option backward.isDefEq.respectTransparency false in
/-- **Membership in the essential image of `p'_*` is cover-local** (Stage-2 assembly).
If the restriction of `M` to every member `W_j` of an open cover of `X'` is a pushforward
from the open `W_j ∩ (ran p')` — i.e. lies in the essential image of the pushforward
along `(𝒞.f j) ⁻¹ᵁ p'.opensRange ↪ W_j` — then `M` itself lies in the essential image
of `p'_*`.  Route: the site-level `restrictAdjunction p'` unit at `M` has components
the plain presheaf restrictions `M(U) → M(U ∩ ran p')`; its invertibility is checked
cover-locally (`isIso_iff_isIso_restrict`), where each component over `O ⊆ W_j` is,
through the lattice identity `w''(O ⊓ w⁻¹(ran p')) = p'''(p'⁻¹(w''O))` and an `eqToHom`
cast, the member restriction map handled by `restrictionMap_isIso_of_essImage`; the
`leftAdjointUniq` comparison transports invertibility to the geometric unit, whence
membership (`mem_essImage_of_unit_isIso`).  Sorry-free.  Project-local; blueprint
`lem:essimage_pushforward_cover_local`. -/
theorem essImage_pushforward_of_openCover {V' : Scheme.{u}} (p' : V' ⟶ X')
    [IsOpenImmersion p'] (M : X'.Modules) (𝒞 : X'.OpenCover)
    (hloc : ∀ j, (Scheme.Modules.pushforward ((𝒞.f j) ⁻¹ᵁ p'.opensRange).ι).essImage
      ((Scheme.Modules.restrictFunctor (𝒞.f j)).obj M)) :
    (Scheme.Modules.pushforward p').essImage M := by
  -- the site-level unit is an isomorphism, checked cover-locally with plain components
  have hsite : IsIso ((Scheme.Modules.restrictAdjunction p').unit.app M) := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_restrict _ 𝒞]
    intro j
    haveI : IsOpenImmersion (𝒞.f j) := Scheme.Cover.map_prop 𝒞 j
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro O
    rw [restrictFunctor_map_app, Scheme.Modules.restrictAdjunction_unit_app_app]
    -- identify the target open: w''(O ⊓ w⁻¹(ran p')) = p'''(p'⁻¹(w''O))
    have hOO : (𝒞.f j) ''ᵁ (O ⊓ (𝒞.f j) ⁻¹ᵁ p'.opensRange)
        = p' ''ᵁ (p' ⁻¹ᵁ ((𝒞.f j) ''ᵁ O)) := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      apply TopologicalSpace.Opens.ext
      change ((𝒞.f j) '' (O ∩ (𝒞.f j) ⁻¹' p'.opensRange) : Set X') = _
      rw [Set.image_inter_preimage, TopologicalSpace.Opens.coe_inf, Set.inter_comm]
      rfl
    -- factor the unit component through the member restriction map + a cast
    have hfac : M.presheaf.map (homOfLE (p'.image_preimage_le ((𝒞.f j) ''ᵁ O))).op
        = M.presheaf.map
            ((𝒞.f j).opensFunctor.map
              (homOfLE (inf_le_left : O ⊓ (𝒞.f j) ⁻¹ᵁ p'.opensRange ≤ O))).op ≫
          M.presheaf.map (eqToHom (congrArg Opposite.op hOO)) := by
      rw [← Functor.map_comp]
      congr 1
    rw [hfac]
    haveI hkey : IsIso (M.presheaf.map
        ((𝒞.f j).opensFunctor.map
          (homOfLE (inf_le_left : O ⊓ (𝒞.f j) ⁻¹ᵁ p'.opensRange ≤ O))).op) :=
      restrictionMap_isIso_of_essImage _ _ (hloc j) O
    haveI hcast : IsIso (M.presheaf.map (eqToHom (congrArg Opposite.op hOO))) :=
      Functor.map_isIso _ _
    exact IsIso.comp_isIso
  -- transport to the geometric unit and conclude essential-image membership
  haveI hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction p').unit.app M) := by
    rw [← Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction p')
      (Scheme.Modules.pullbackPushforwardAdjunction p') M]
    haveI h1 : IsIso ((Adjunction.leftAdjointUniq (Scheme.Modules.restrictAdjunction p')
        (Scheme.Modules.pullbackPushforwardAdjunction p')).hom) := Iso.isIso_hom _
    haveI h2 : IsIso ((Adjunction.leftAdjointUniq (Scheme.Modules.restrictAdjunction p')
        (Scheme.Modules.pullbackPushforwardAdjunction p')).hom.app M) :=
      NatIso.isIso_app_of_isIso _ M
    haveI h3 : IsIso ((Scheme.Modules.pushforward p').map
        ((Adjunction.leftAdjointUniq (Scheme.Modules.restrictAdjunction p')
          (Scheme.Modules.pullbackPushforwardAdjunction p')).hom.app M)) :=
      Functor.map_isIso _ _
    exact IsIso.comp_isIso' hsite h3
  exact (Scheme.Modules.pullbackPushforwardAdjunction p').mem_essImage_of_unit_isIso M

/-! ## Project-local Mathlib supplement — refining affine cover for the open-immersion
Beck–Chevalley assembly (Stage-2 reduction of `openImmersion_beckChevalley`)

The `IsIso bareBC` residual of `openImmersion_beckChevalley` is checked *cover-locally* on `X'`
(keystone `Scheme.Modules.Hom.isIso_iff_isIso_restrict`).  This section supplies the geometric
input for that assembly: an affine open cover `{Wⱼ}` of `X'` such that each `g'|_{Wⱼ}` lands in an
affine open `Uⱼ ⊆ X` (so `g'|_{Wⱼ}` is a map of affine schemes, a `Spec`-map).  It is pure geometry
(no flatness, no quasi-coherence), obtained by pulling the standard affine cover of `X` back along
`g'` and refining each preimage to affine members. -/

/-- **Packaged output of `openImmersion_refiningAffineCover`.**  An affine open cover of `X'`
together with, for each member `Wⱼ`, an affine open `Uⱼ ⊆ X` containing the image `g'(Wⱼ)` (recorded
as the range containment `Set.range (Wⱼ.f ≫ g').base ⊆ Uⱼ`).  Project-local packaging of the
Stage-2 geometric datum of `openImmersion_beckChevalley`; blueprint
`lem:openimm_refining_affine_cover`. -/
structure OpenImmersionRefiningAffineCover (g' : X' ⟶ X) where
  /-- the affine open cover of `X'`. -/
  cover : X'.OpenCover
  /-- every member of `cover` is affine. -/
  isAffine_cover : ∀ j, IsAffine (cover.X j)
  /-- the containing affine open of `X` for each member. -/
  U : cover.I₀ → X.Opens
  /-- each `U j` is an affine open. -/
  isAffineOpen_U : ∀ j, IsAffineOpen (U j)
  /-- the image `g'(Wⱼ)` is contained in `U j`. -/
  le_U : ∀ j, Set.range (cover.f j ≫ g').base ⊆ (U j : Set X)

/-- The pullback of the standard affine cover of `X` along `g'`, refined to affine members. -/
private noncomputable abbrev pullbackAffineRefinementCover (g' : X' ⟶ X) : X'.OpenCover :=
  (Scheme.OpenCover.affineRefinement (X.affineOpenCover.openCover.pullback₁ g')).openCover

set_option backward.isDefEq.respectTransparency false in
/-- **Affine cover of `X'` refining preimages of affine opens of `X`** (blueprint
`lem:openimm_refining_affine_cover`).  For any `g' : X' ⟶ X` there is an affine open cover `{Wⱼ}` of
`X'` together with, for each `j`, an affine open `Uⱼ ⊆ X` with `g'(Wⱼ) ⊆ Uⱼ`; hence `g'|_{Wⱼ}` is a
map of affine schemes.  Constructed by pulling `X.affineOpenCover` back along `g'`
(`OpenCover.pullback₁`) — whose member over index `i` maps, via `Cover.pullbackHom`, into the affine
`X.affineOpenCover.X i` — and refining each (possibly non-affine) preimage member to affine pieces
(`OpenCover.affineRefinement`).  The containment is the range monotonicity
`Set.range (φ ≫ g'(=…≫ Uᵢ.ι)).base ⊆ Set.range Uᵢ.ι.base = Uᵢ`.  Pure geometry — no flatness or
quasi-coherence.  Project-local: the Stage-2 geometric input of `openImmersion_beckChevalley`. -/
noncomputable def openImmersion_refiningAffineCover (g' : X' ⟶ X) :
    OpenImmersionRefiningAffineCover g' where
  cover := pullbackAffineRefinementCover g'
  isAffine_cover j := by infer_instance
  U j := (X.affineOpenCover.openCover.f j.1).opensRange
  isAffineOpen_U j := isAffineOpen_opensRange _
  le_U j := by
    have hcomp : (pullbackAffineRefinementCover g').f j ≫ g'
        = (((X.affineOpenCover.openCover.pullback₁ g').X j.1).affineCover.f j.2
            ≫ X.affineOpenCover.openCover.pullbackHom g' j.1)
          ≫ X.affineOpenCover.openCover.f j.1 := by
      have hf : (pullbackAffineRefinementCover g').f j
          = ((X.affineOpenCover.openCover.pullback₁ g').X j.1).affineCover.f j.2
          ≫ (X.affineOpenCover.openCover.pullback₁ g').f j.1 := rfl
      rw [hf, Category.assoc, ← Scheme.Cover.pullbackHom_map, ← Category.assoc]
    rintro x ⟨y, rfl⟩
    rw [SetLike.mem_coe, Scheme.Hom.mem_opensRange]
    exact ⟨(((X.affineOpenCover.openCover.pullback₁ g').X j.1).affineCover.f j.2
            ≫ X.affineOpenCover.openCover.pullbackHom g' j.1).base y,
      by rw [hcomp, Scheme.Hom.comp_base]; rfl⟩

/-! **Open-immersion Beck–Chevalley over a restricted cartesian square** (Stacks 02KG; carved
block `lem:openimm_beckchevalley`).  Let `p : V ⟶ X` be an *open immersion* and let the square
```
  V' --gV--> V
  |p'        |p
  v          v
  X' --g'--> X
```
be cartesian (`hsq`), so `p'` is the open immersion onto the preimage `(g')⁻¹(V)`.  Then there is
a Beck–Chevalley isomorphism of `O_{X'}`-modules
```
  (g')^*(p_* p^* F) ≅ p'_* p'^*((g')^* F),
```
i.e. `(pullback g').obj (pushPullObj F (Over.mk p)) ≅ pushPullObj ((pullback g').obj F)
(Over.mk p')`.

**STAGE 1 (landed, sorry-free): structural reduction.**  The body is built as
`asIso (openImmersion_bareBC … |>.app (p^* F)) ≪≫ (pushforward p').mapIso (telescope).symm`,
where `telescope = openImmersion_bc_telescope …` rewrites the RHS pullback `p'^*(g'^* F)` into
`gV^*(p^* F)` purely by the pseudofunctor structure of `pullback`.  This collapses the leaf to the
**single residual obligation** `IsIso ((openImmersion_bareBC g' p p' gV hsq).app (p^* F))` — the
bare Beck–Chevalley comparison being an iso.

**STAGE 2 (mate factorization LANDED; essential-image node CLOSED).**  The mate formula
(`openImmersion_bareBC_app_eq`) factors `bareBC.app (p^* F)` as the `p'`-unit at
`g'^*(p_*(p^* F))` followed by isomorphisms (the pullback-telescope components and the `p`-counit,
invertible for open immersions by `openImmersion_pullback_counit_isIso`).  Since `p'_*` is fully
faithful for the open immersion `p'`, the unit is an isomorphism at every module in the essential
image of `p'_*` (`openImmersion_unit_isIso_of_essImage`), so the last obligation was the
essential-image node `openImmersion_pushPull_essImage`:
`g'^*(p_*(p^* F)) ∈ essImage p'_*` — now proved cover-locally over the refining affine cover,
with the member node discharged by `restrict_pullback_pushforward_essImage`
(`Cohomology/AffinePushPullEssImage.lean`); for the affine tilde dictionary the square is
specialized to `p = V₀.ι` of an affine open `V₀ : X.Opens`.  (The earlier docstring sketch
"`p_*` is extension-by-zero off `V`" was mathematically WRONG — `p_*` is the *right adjoint*
direct image; the off-`V'` data is real and is exactly what the essential-image node encodes.)
Project-local; blueprint `lem:openimm_beckchevalley`. -/
/-- **The member node** (the Stage-2 frontier, post mate-factorization and cover-local
assembly — now CLOSED).  For the restricted cartesian square `hsq : IsPullback gV p' V₀.ι g'`
over an affine open `V₀ ⊆ X`, with `X` separated, `F` quasi-coherent, and a member
`W_j` of the refining affine cover `𝒜` of `X'` (so `W_j` is affine and
`g'(W_j) ⊆ U_j := 𝒜.U j` is an affine open of `X`), the restriction
`M|_{W_j} = (restrictFunctor w_j).obj (g'^*((V₀.ι)_*(V₀.ι^* F)))` is a pushforward from the
open `w_j⁻¹(ran p') = W_j ∩ (g')⁻¹(V₀)` — i.e. lies in the essential image of the
pushforward along `(𝒜.cover.f j) ⁻¹ᵁ p'.opensRange ↪ W_j`.

The hypotheses are exactly those under which the statement is true (the arbitrary-`F` form
is FALSE, see the blueprint remark at `lem:openimm_beckchevalley`).  Route (landed in
`Cohomology/AffinePushPullEssImage.lean`): identify `ran p' = g'⁻¹(V₀)` (range of the base
change of an open immersion, `IsOpenImmersion.range_pullbackSnd`), then apply the member
assembly `restrict_pullback_pushforward_essImage` — the pullback pseudofunctor rewrites
`M|_{W_j} ≅ gU^*(((V₀.ι)_* V₀.ι^* F)|_{U_j})`, the open-open pushforward–restriction
commutation `pushforwardRestrictOpensIso` (the `glueOverlapBaseChangeIso` pattern) rewrites
the restricted pushforward as `((U_j.ι⁻¹V₀).ι)_*` of a quasi-coherent restriction, `U_j ∩ V₀`
is affine (`IsAffineOpen.inf`, `X` separated), and the affine heart
`pullback_pushforward_affineOpen_essImage` (the sorry-free
`affinePushforwardPullbackBaseChange` over the abstract ring pushout, transported along
`isoSpec` and the `isoOfRangeEq` range identification) concludes.
Project-local; blueprint `lem:openimm_bareBC_app_isIso_affine` (essential-image member). -/
theorem openImmersion_pushPull_essImage_member {V' : Scheme.{u}}
    (g' : X' ⟶ X) {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) (p' : V' ⟶ X') (gV : V' ⟶ ↑V₀)
    (hsq : IsPullback gV p' V₀.ι g') [IsOpenImmersion p']
    [IsSeparated (terminal.from X)] (F : X.Modules) (hF : F.IsQuasicoherent)
    (𝒜 : OpenImmersionRefiningAffineCover g') (j : 𝒜.cover.I₀) :
    (Scheme.Modules.pushforward ((𝒜.cover.f j) ⁻¹ᵁ p'.opensRange).ι).essImage
      ((Scheme.Modules.restrictFunctor (𝒜.cover.f j)).obj
        ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pushforward V₀.ι).obj
          ((Scheme.Modules.pullback V₀.ι).obj F)))) := by
  -- the range of `p'` is the preimage of `V₀` (range of the base-changed open immersion)
  have hRange : p'.opensRange = g' ⁻¹ᵁ V₀ := by
    have h1 : Set.range p' = Set.range (pullback.snd V₀.ι g') := by
      rw [← hsq.isoPullback_hom_snd]
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr hsq.isoPullback.hom.surjective, Set.image_univ]
    apply TopologicalSpace.Opens.ext
    rw [show (p'.opensRange : Set X') = Set.range p' from rfl, h1,
      IsOpenImmersion.range_pullbackSnd]
    simp [Scheme.Opens.opensRange_ι]
  rw [hRange]
  -- separatedness gives the affine absolute diagonal consumed by `IsAffineOpen.inf`
  haveI : IsClosedImmersion (pullback.diagonal (terminal.from X)) :=
    IsSeparated.isClosedImmersion_diagonal
  haveI : IsOpenImmersion (𝒜.cover.f j) := Scheme.Cover.map_prop 𝒜.cover j
  haveI : IsAffine (𝒜.cover.X j) := 𝒜.isAffine_cover j
  exact restrict_pullback_pushforward_essImage g' hV₀ (𝒜.cover.f j)
    (𝒜.isAffineOpen_U j) (𝒜.le_U j) F hF

/-- **The essential-image node**, reduced to the member node by the cover-local assembly
`essImage_pushforward_of_openCover` over the refining affine cover
`openImmersion_refiningAffineCover g'`.  For the restricted cartesian square with `p` an
open immersion, `V` affine, `X` separated and `F` quasi-coherent, the pulled-back
push–pull module `g'^*(p_*(p^* F))` lies in the essential image of `p'_*`.  No `sorry`
of its own.  Project-local; blueprint `lem:openimm_bareBC_isIso` (essential-image node). -/
theorem openImmersion_pushPull_essImage {V' : Scheme.{u}}
    (g' : X' ⟶ X) {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) (p' : V' ⟶ X') (gV : V' ⟶ ↑V₀)
    (hsq : IsPullback gV p' V₀.ι g')
    [IsSeparated (terminal.from X)] (F : X.Modules) (hF : F.IsQuasicoherent) :
    (Scheme.Modules.pushforward p').essImage
      ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pushforward V₀.ι).obj
        ((Scheme.Modules.pullback V₀.ι).obj F))) := by
  haveI : IsOpenImmersion p' := isOpenImmersion_of_isPullback_left g' V₀.ι p' gV hsq
  exact essImage_pushforward_of_openCover p' _ (openImmersion_refiningAffineCover g').cover
    (fun j => openImmersion_pushPull_essImage_member g' hV₀ p' gV hsq F hF
      (openImmersion_refiningAffineCover g') j)

/-- **The unit node**, derived from the essential-image node
(`openImmersion_pushPull_essImage` + `openImmersion_unit_isIso_of_essImage`): for the
restricted cartesian square with `p` an open immersion, `V` affine, `X` separated and `F`
quasi-coherent, the `p'`-unit is an isomorphism at `g'^*(p_*(p^* F))`.  No `sorry` of its
own.  Project-local; blueprint `lem:openimm_bareBC_isIso` (unit node). -/
theorem openImmersion_pushPull_unit_isIso {V' : Scheme.{u}}
    (g' : X' ⟶ X) {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) (p' : V' ⟶ X') (gV : V' ⟶ ↑V₀)
    (hsq : IsPullback gV p' V₀.ι g')
    [IsSeparated (terminal.from X)] (F : X.Modules) (hF : F.IsQuasicoherent) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction p').unit.app
      ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pushforward V₀.ι).obj
        ((Scheme.Modules.pullback V₀.ι).obj F)))) := by
  haveI : IsOpenImmersion p' := isOpenImmersion_of_isPullback_left g' V₀.ι p' gV hsq
  exact openImmersion_unit_isIso_of_essImage p' _
    (openImmersion_pushPull_essImage g' hV₀ p' gV hsq F hF)

noncomputable def openImmersion_beckChevalley {V' : Scheme.{u}}
    (g' : X' ⟶ X) {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) (p' : V' ⟶ X') (gV : V' ⟶ ↑V₀)
    (hsq : IsPullback gV p' V₀.ι g')
    [IsSeparated (terminal.from X)] (F : X.Modules) (hF : F.IsQuasicoherent) :
    (Scheme.Modules.pullback g').obj (pushPullObj F (Over.mk V₀.ι)) ≅
      pushPullObj ((Scheme.Modules.pullback g').obj F) (Over.mk p') := by
  -- STAGE 1 (sorry-free): the pseudofunctor telescope reduces the leaf to one `IsIso` on the
  -- bare mate `openImmersion_bareBC … |>.app (V₀.ι^* F)`.
  haveI hiso : IsIso ((openImmersion_bareBC g' V₀.ι p' gV hsq).app
      ((Scheme.Modules.pullback V₀.ι).obj F)) :=
    -- STAGE 2 (mate factorization landed): the telescope component and the `p`-counit factor
    -- are isos (`openImmersion_bareBC_app_isIso_of_unit`), so the comparison is an iso as soon
    -- as the `p'`-unit is one at `g'^*((V₀.ι)_*(V₀.ι^* F))` — the unit node
    -- `openImmersion_pushPull_unit_isIso`, now CLOSED via the essential-image member node.
    openImmersion_bareBC_app_isIso_of_unit g' V₀.ι p' gV hsq _
      (openImmersion_pushPull_unit_isIso g' hV₀ p' gV hsq F hF)
  exact (@asIso _ _ _ _ ((openImmersion_bareBC g' V₀.ι p' gV hsq).app
      ((Scheme.Modules.pullback V₀.ι).obj F)) hiso) ≪≫
    ((pushforward p').mapIso (openImmersion_bc_telescope g' V₀.ι p' gV hsq F)).symm

/-! ### The cosimplicial comparison is a WHISKERED MATE — so naturality is not an obligation

This is the structural correction that removes the *first* of the two cosimplicial naturality
`sorry`s — an earlier revision of this heading claimed both, and two `rfl` probes refuted that (the
twisted leaf's right-hand side is a different cosimplicial object; see its docstring).  It is worth
stating why they existed.  Both `cech_pushforward_baseChange_natIso` and
`twisted_cech_nerve_iso` were built with `NatIso.ofComponents`: a degree-`n` isomorphism plus a
*proof obligation* that those isomorphisms commute with the index-omission maps.  That obligation
is genuinely hard as posed — an earlier revision established that `Pi.hom_ext`, the tool that
closed this project's other naturality squares, cannot fire, because the σ-decomposition sits
mid-chain behind pushforward/pullback applications.

But the obligation is an artefact of the *construction*, not of the mathematics.  Two facts:

* `openImmersion_bareBC` is **misnamed**.  Read its docstring: it needs no open immersion and no
  flatness.  It is the Beck–Chevalley mate of the `pullback` pseudofunctor 2-isomorphism attached
  to *any* commuting square.  Instantiated at the **outer** square `h : IsPullback g' f' f g` it
  is a natural transformation `f_* ⋙ g^* ⟶ g'^* ⋙ f'_*` of functors `X.Modules ⥤ S'.Modules`.
* The nested `CosimplicialObject.whiskering` in both statements **is** functor composition: each
  side is definitionally `N ⋙ (…)` for `N` the dropped Čech nerve (checked both ways by `rfl`).

So `Functor.whiskerLeft N (cechOuterBC …)` is already a morphism between exactly the two
cosimplicial objects in question, and its naturality in the simplex index *is* the naturality of
the transformation being whiskered — free, by construction.  `NatIso.isIso_of_isIso_app` then
promotes it to an isomorphism from one `IsIso` per degree, and no cosimplicial statement is left.

The moral, recorded because this run found three variants of it: a walled obligation can be an
artefact of how the object was *built*, not only of how its statement was *phrased*.
`NatIso.ofComponents` asks for naturality; whiskering a natural transformation never does.

**AND THE SECOND HALF, run 0068 r3.**  The `IsIso` residue this reduction leaves was *also* not new
work.  `cechOuterBC` is definitionally `canonicalBaseChangeMap` and its invertibility at
quasi-coherent modules is `canonicalBaseChangeMap_isIso`, already proved in this project; see
`isIso_cechOuterBC_coverInter` / `isIso_cechOuterBC_nerve_obj` below and the note there.  So the
S-level leaf is closed, and the whole chain here — reduce by whiskering, then apply an existing
theorem — is `sorry`-free.  Only the twisted-nerve square remains. -/

/-- **The S-level base-change mate at the outer cartesian square.**  `openImmersion_bareBC`
instantiated at `h : IsPullback g' f' f g` itself — no open immersion, no flatness, no affineness
(see the section note above on why that lemma's name is misleading).  This is the canonical
comparison `f_*(−)` pulled back along `g` ⟶ pushed forward along `f'` of the `g'`-pullback:
```
  f_* ⋙ g^*  ⟶  g'^* ⋙ f'_*.
```
Being a natural transformation is the whole point: whiskering a *cosimplicial* object with it
produces a map of cosimplicial objects whose compatibility with the coface maps is automatic.
Project-local. -/
noncomputable def cechOuterBC (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback g ⟶
      Scheme.Modules.pullback g' ⋙ Scheme.Modules.pushforward f' :=
  openImmersion_bareBC g f f' g' h

/-- **The whiskered cosimplicial base-change comparison, from a degreewise `IsIso` alone.**
Given that the outer mate `cechOuterBC` is invertible at every object of the dropped Čech nerve,
this assembles the natural isomorphism of cosimplicial objects that
`cechComplex_baseChange_cosimplicialIso` consumes.

**There is no naturality hypothesis, and that is the content.**  The two sides are
definitionally `N ⋙ (f_* ⋙ g^*)` and `N ⋙ (g'^* ⋙ f'_*)`, so `Functor.whiskerLeft N` of the
mate is a morphism between them, and its coface compatibility is the mate's own naturality.
Compare `cech_pushforward_baseChange_natIso`, which builds the same isomorphism degreewise via
`NatIso.ofComponents` and therefore *does* carry a naturality obligation — the one that has been
open in this file.  Project-local. -/
noncomputable def cech_pushforward_baseChange_natIso_of_isIso
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) (F : X.Modules)
    (hiso : ∀ n : SimplexCategory, IsIso ((cechOuterBC f g f' g' h).app
      ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).obj n))) :
    ((CosimplicialObject.whiskering S.Modules S'.Modules).obj
        (Scheme.Modules.pullback g)).obj
      (((CosimplicialObject.whiskering X.Modules S.Modules).obj
          (Scheme.Modules.pushforward f)).obj
        (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)))
      ≅ ((CosimplicialObject.whiskering X'.Modules S'.Modules).obj
          (Scheme.Modules.pushforward f')).obj
        (((CosimplicialObject.whiskering X.Modules X'.Modules).obj
            (Scheme.Modules.pullback g')).obj
          (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F))) :=
  letI happ : ∀ n, IsIso ((Functor.whiskerLeft
      (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)) (cechOuterBC f g f' g' h)).app n) :=
    fun n => hiso n
  @asIso _ _ _ _ (Functor.whiskerLeft
      (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)) (cechOuterBC f g f' g' h))
    (@NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ happ)

/-- **A natural transformation is invertible at a finite product as soon as it is invertible at
each factor** — provided both functors preserve that product.

Pure category theory, and the second half of the naturality removal: it takes the degreewise
obligation of `cech_pushforward_baseChange_natIso_of_isIso` down to one `IsIso` **per index tuple
`σ`**, which is where this file's per-σ machinery lives.  The proof is the naturality square of
`α` against the projections `Pi.π A j`, which identifies `α.app (∏ A)` with
`Pi.map (fun j => α.app (A j))` after the two `piComparison` isomorphisms — so it is an iso
because each component is.

Note what this does *not* need: no additivity, no abelian structure, and no compatibility between
`α` and any independently-constructed product decomposition.  Project-local; mathlib has
`Pi.map_isIso` and `piComparison` but not this combination. -/
theorem isIso_app_pi_of_isIso_app {C D : Type*} [Category C] [Category D]
    {P Q : C ⥤ D} (α : P ⟶ Q) {J : Type*} [Finite J] (A : J → C)
    [Limits.HasProduct A] [Limits.HasProduct (fun j => P.obj (A j))]
    [Limits.HasProduct (fun j => Q.obj (A j))]
    [Limits.PreservesLimit (Discrete.functor A) P]
    [Limits.PreservesLimit (Discrete.functor A) Q]
    (h : ∀ j, IsIso (α.app (A j))) : IsIso (α.app (∏ᶜ A)) := by
  have hsq : (Limits.PreservesProduct.iso P A).hom ≫ Limits.Pi.map (fun j => α.app (A j)) =
      α.app (∏ᶜ A) ≫ (Limits.PreservesProduct.iso Q A).hom := by
    refine Limits.Pi.hom_ext _ _ (fun j => ?_)
    simp only [Category.assoc, Limits.Pi.map_π, Limits.PreservesProduct.iso_hom]
    rw [← Category.assoc, Limits.piComparison_comp_π, Limits.piComparison_comp_π]
    exact α.naturality (Limits.Pi.π A j)
  haveI hj : ∀ j, IsIso (α.app (A j)) := h
  haveI : IsIso (Limits.Pi.map (fun j => α.app (A j))) := by
    refine ⟨Limits.Pi.map (fun j => inv (α.app (A j))), ?_, ?_⟩ <;>
      refine Limits.Pi.hom_ext _ _ (fun j => ?_) <;> simp
  exact IsIso.of_isIso_fac_right hsq.symm

/-! ### The per-σ mate obligation is `canonicalBaseChangeMap_isIso`, and it is already proved

The `IsIso` residue left by `cech_pushforward_baseChange_natIso_of_isIso` was priced, across three
sessions, as genuinely open Beck–Chevalley content needing `mateEquiv_vcomp` and a `TwoSquare`
`hComp`/`vComp` calculation.  It is neither.  `cechOuterBC f g f' g' h` is *definitionally* (checked
by `rfl`) the mate `canonicalBaseChangeMap h` of `Picard/QuotScheme.lean` — the same `mateEquiv` of
the same `pullbackComp`/`pullbackCongr` 2-isomorphism — and `canonicalBaseChangeMap_isIso` proves
that mate invertible at every quasi-coherent module for `[QuasiCompact f] [QuasiSeparated f]
[Flat g]`, `sorry`-free.  So the only thing that had to be supplied here is *quasi-coherence of the
single-intersection-open push–pull object*, which is `isQuasicoherent_pushPullObj_coverInter` below;
the degree-`n` object needs no separate quasi-coherence lemma, because
`isIso_cechOuterBC_nerve_obj` splits the degree into its σ-factors *first*, via
`isIso_app_of_iso_obj` and `isIso_app_pi_of_isIso_app`, and only then applies the mate theorem
factorwise.

(An earlier revision of this paragraph advertised a second lemma `isQuasicoherent_cechNerve_obj`
"below".  **No such declaration exists, here or anywhere in the project** — I named a lemma the
route does not need, inside the very note whose subject is an unchecked absence claim.  Found by a
fresh-context reviewer, not by me.  The recorded failure mode is "docstring declaration lists are
unchecked"; the cheap guard is to grep each advertised name and see it resolve to a `def`/`theorem`
line rather than only to the docstring that promises it.)

Why it was missed: this file's own docstring asserted that `Picard/QuotScheme` "is deliberately not
imported because it carries `sorry`s".  That was false at HEAD — its whole five-module cone is
`sorry`-free — and the false claim was load-bearing, since it also ruled out the qcqs pushforward
quasi-coherence (Stacks 01XJ) that the nerve-term argument needs.  An absence claim about a
*module* silently became an absence claim about two *theorems*. -/

/-- **The single-intersection-open push–pull object is quasi-coherent.**  For `U_σ = coverInterOpen
𝒰 σ` with `f` separated and `S` affine, the open `U_σ` is affine (`coverInterOpen_isAffine`), hence
its inclusion `j_σ` is an affine morphism into the separated `X` — so
`pushPullObj F (Over.mk j_σ) = (j_σ)_*((j_σ)^* F)` is quasi-coherent by Stacks 01BG for the
restriction and Stacks 01XJ for the pushforward.

This is the input that turns the per-σ mate obligation of
`cech_pushforward_baseChange_natIso_of_isIso` into an application of `canonicalBaseChangeMap_isIso`.
Project-local. -/
theorem isQuasicoherent_pushPullObj_coverInter (f : X ⟶ S) [IsSeparated f] [IsAffine S]
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀)
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))).IsQuasicoherent := by
  haveI hsepX : X.IsSeparated := by
    constructor
    rw [← terminal.comp_from f]
    exact IsSeparated.comp_iff.mpr ‹IsSeparated f›
  haveI : IsAffine (↑(coverInterOpen 𝒰 σ) : Scheme.{u}) := coverInterOpen_isAffine f 𝒰 σ
  haveI haff : IsAffineHom (Scheme.Opens.ι (coverInterOpen 𝒰 σ)) :=
    isAffineHom_of_isAffine_of_isSeparated _
  haveI haff' : IsAffineHom (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).hom := haff
  haveI : QuasiCompact (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).hom := inferInstance
  haveI : QuasiSeparated (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).hom := inferInstance
  haveI : ((Scheme.Modules.pullback (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).hom).obj
      F).IsQuasicoherent :=
    isQuasicoherent_pullback_opens (coverInterOpen 𝒰 σ) F hF
  exact Scheme.Modules.pushforward_isQuasicoherent
    (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).hom _

/-- **`IsIso` of a natural transformation transports along an isomorphism of the object.**
If `α.app Z'` is invertible and `Z ≅ Z'`, then `α.app Z` is invertible.

**This is mathlib's `CategoryTheory.NatTrans.isIso_app_iff_of_iso`, in its `.mpr` direction**, and
it is kept only as a named one-directional abbreviation because it reads better at the single use
site below.  An earlier revision of this docstring called it "the bridge that lets…" and gave it a
four-line proof of its own; a fresh-context reviewer found the mathlib lemma, so the proof is now
that lemma rather than a duplicate of it.  Do not treat this as project infrastructure.

What it is *for*: the per-σ decomposition `pushPull_sigma_iso` is an isomorphism of *objects*, and
the obligation is `IsIso` of a *map*, so the decomposition cannot be substituted directly — that
gap is the "groups agree ≠ maps agree" error, and this lemma is what bridges it. -/
theorem isIso_app_of_iso_obj {C D : Type*} [Category C] [Category D] {P Q : C ⥤ D} (α : P ⟶ Q)
    {Z Z' : C} (e : Z ≅ Z') (h : IsIso (α.app Z')) : IsIso (α.app Z) :=
  (CategoryTheory.NatTrans.isIso_app_iff_of_iso α e).mpr h

/-- **The outer mate is invertible at a single-intersection-open push–pull object.**  This is the
per-σ obligation that `isIso_app_pi_of_isIso_app` reduces the degreewise one to, and it is a *direct
application* of the 02KG/02KH mate theorem: `cechOuterBC` is `canonicalBaseChangeMap` (by `rfl`, see
the section note), and the argument is quasi-coherent by
`isQuasicoherent_pushPullObj_coverInter`.

Recorded because this leaf was priced as open Beck–Chevalley content for three sessions: the
`mateEquiv_vcomp` split proposed in earlier revisions is not needed, and neither is any
identification of `pushPullObj_coverInter_baseChange` with the mate's component.  Project-local. -/
theorem isIso_cechOuterBC_coverInter (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [QuasiSeparated f]
    [IsSeparated f] [IsAffine S]
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀)
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    IsIso ((cechOuterBC f g f' g' h).app
      (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))))) := by
  haveI := isQuasicoherent_pushPullObj_coverInter f 𝒰 σ F hF
  exact canonicalBaseChangeMap_isIso h _

set_option maxHeartbeats 1600000 in
-- The σ-indexed product decomposition of the nerve degree forces the same finite-product
-- and quasi-coherence instance searches as `isQuasicoherent_cechComplex_X`.
set_option synthInstance.maxHeartbeats 800000 in
/-- **The outer mate is invertible at every degree of the dropped Čech nerve.**  The degree-`n`
object is the push–pull object over the degree-`n` fibre power, which decomposes as the finite
product over index tuples `σ` (`pushPull_sigma_iso`); `isIso_app_of_iso_obj` moves the obligation
across that decomposition, `isIso_app_pi_of_isIso_app` splits the product, and each factor is
`isIso_cechOuterBC_coverInter`.

This is the *whole* degreewise hypothesis of `cech_pushforward_baseChange_natIso_of_isIso`, so
together they replace `cech_pushforward_baseChange_natIso` with a `sorry`-free construction.
Project-local. -/
theorem isIso_cechOuterBC_nerve_obj (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [QuasiSeparated f]
    [IsSeparated f] [IsAffine S]
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] [∀ i, IsAffine (𝒰.X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent) (n : SimplexCategory) :
    IsIso ((cechOuterBC f g f' g' h).app
      ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).obj n)) := by
  -- the degree-`n` object IS `pushPullObj F (backbone n)` (`rfl`), and that is the σ-product
  refine isIso_app_of_iso_obj (cechOuterBC f g f' g' h)
    (pushPull_sigma_iso 𝒰 F n.len) ?_
  refine isIso_app_pi_of_isIso_app (cechOuterBC f g f' g' h) _ (fun σ => ?_)
  exact isIso_cechOuterBC_coverInter f g f' g' h 𝒰 σ F hF

set_option maxHeartbeats 1600000 in
-- Elaborating the two nested `CosimplicialObject.whiskering` applications in the statement is
-- what costs here, as in the declaration this replaces; the proof itself is one application.
set_option synthInstance.maxHeartbeats 800000 in
/-- **The cosimplicial base-change comparison, `sorry`-free** (Stacks 02KG, the cosimplicial half).
`cech_pushforward_baseChange_natIso_of_isIso` fed by `isIso_cechOuterBC_nerve_obj`: same statement
as `cech_pushforward_baseChange_natIso`, no naturality obligation and no open leaf.  Its extra
hypotheses over that declaration are `[QuasiCompact f]`, `[QuasiSeparated f]` and `[Flat g]` — all
three already carried by `cech_flatBaseChange`, whose route this serves, and `[IsAffine S']` is
*not* needed.  Project-local. -/
noncomputable def cech_pushforward_baseChange_natIso_flat
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [QuasiSeparated f]
    [IsSeparated f] [IsAffine S]
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] [∀ i, IsAffine (𝒰.X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    ((CosimplicialObject.whiskering S.Modules S'.Modules).obj
        (Scheme.Modules.pullback g)).obj
      (((CosimplicialObject.whiskering X.Modules S.Modules).obj
          (Scheme.Modules.pushforward f)).obj
        (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)))
      ≅ ((CosimplicialObject.whiskering X'.Modules S'.Modules).obj
          (Scheme.Modules.pushforward f')).obj
        (((CosimplicialObject.whiskering X.Modules X'.Modules).obj
            (Scheme.Modules.pullback g')).obj
          (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F))) :=
  cech_pushforward_baseChange_natIso_of_isIso f g f' g' h 𝒰 F
    (fun n => isIso_cechOuterBC_nerve_obj f g f' g' h 𝒰 F hF n)

/-- **Per-intersection-open X-level Beck–Chevalley** (the per-σ residual of the X-level leaf
`twisted_cech_nerve_iso`, after the product decomposition `pushPull_sigma_iso`).  For a Čech
fibre-power intersection open `U_σ = coverInterOpen 𝒰 σ ↪ X` (open immersion `j_σ`), pulling the
single-open push–pull object `pushPullObj F (Over.mk j_σ) = (j_σ)_* (j_σ)^* F` back along `g'`
is the push–pull object of the base-changed data `(g'^* F)` over the corresponding intersection
`U'_σ = coverInterOpen 𝒰' σ ↪ X'` of the base-changed cover
`𝒰' = (openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom`:
```
  g'^*((j_σ)_* (j_σ)^* F)  ≅  (j'_σ)_* (j'_σ)^* (g'^* F)        over U'_σ.
```
This is the open-immersion Beck–Chevalley identification for the cartesian square cut out over
`U_σ` (`X`-level square, no base affineness): geometrically `U'_σ = (g')⁻¹(U_σ)` (pullback
preserves the fibre powers `U_{i₀} ×_X ⋯ ×_X U_{iₚ}`), so the restricted square is cartesian and
the push–pull of the restriction commutes with `g'^*`.  **CLOSED**: the cover-base-change
identification `coverInterOpen 𝒰' σ = (g')⁻¹(coverInterOpen 𝒰 σ)` (`coverInterOpen_baseChange_eq`)
plus the now sorry-free open-immersion Beck–Chevalley `openImmersion_beckChevalley` for the
restricted square (`restrictedCartesianAffinePushout`), transported along the `isoOfRangeEq`
slice iso by `pushPullObjCongr` — blueprinted `lem:twisted_cech_nerve_iso` (per-open instance).
Project-local. -/
noncomputable def twisted_cech_nerve_per_sigma
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [IsSeparated f] [IsAffine S]
    [∀ i, IsAffine (𝒰.X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent) {κ : Type} [Finite κ] [Nonempty κ]
    (σ : κ → 𝒰.I₀) :
    (Scheme.Modules.pullback g').obj
        (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) ≅
      pushPullObj ((Scheme.Modules.pullback g').obj F)
        (Over.mk (Scheme.Opens.ι (coverInterOpen
          ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom) σ))) := by
  -- CLOSED — three CLOSED carved blocks + the slice transport:
  --   (1) the restricted cartesian square over `U_σ = coverInterOpen 𝒰 σ` is supplied by the
  --       sorry-free `restrictedCartesianAffinePushout g' 𝒰 σ`;
  --   (2) `openImmersion_beckChevalley` (now sorry-free via the essential-image member node)
  --       gives `g'^*(pushPullObj F (Over.mk (ι U_σ))) ≅ pushPullObj (g'^*F)
  --       (Over.mk (pullback.fst g' (ι U_σ)))`;
  --   (3) `pullback.fst g' (ι U_σ)` and `ι (coverInterOpen 𝒰' σ)` are open immersions with the
  --       SAME range `(g')⁻¹(U_σ)` — `IsOpenImmersion.range_pullbackFst` and the CLOSED
  --       `coverInterOpen_baseChange_eq` (needs `[Finite κ]`) — so the `isoOfRangeEq` slice iso
  --       transports the `pushPullObj` along `pushPullObjCongr`.
  haveI hsepX : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    exact IsSeparated.comp_iff.mpr ‹IsSeparated f›
  haveI hfst : IsOpenImmersion (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))) :=
    isOpenImmersion_of_isPullback_left g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))
      (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (restrictedCartesianAffinePushout g' 𝒰 σ)
  haveI hι' : IsOpenImmersion (Scheme.Opens.ι (coverInterOpen
      ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom) σ)) :=
    inferInstance
  have hre : Set.range (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      = Set.range (Scheme.Opens.ι (coverInterOpen
          ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom) σ)) := by
    rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι,
      coverInterOpen_baseChange_eq f g f' g' h 𝒰 σ, Scheme.Opens.opensRange_ι]
  exact (openImmersion_beckChevalley g' (coverInterOpen_isAffine f 𝒰 σ)
      (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (restrictedCartesianAffinePushout g' 𝒰 σ) F hF) ≪≫
    pushPullObjCongr _ (Over.isoMk
      (@IsOpenImmersion.isoOfRangeEq _ _ _
        (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
        (Scheme.Opens.ι (coverInterOpen
          ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom) σ))
        hfst hι' hre)
      (@IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
        (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
        (Scheme.Opens.ι (coverInterOpen
          ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom) σ))
        hfst hι' hre))

/-- **RHS abstract → tilde for a single intersection open (base-changed side)** (carved block
`lem:coverinter_rhs_iso_tilde`).  Over the affine bases `S = Spec R`, `S' = Spec R'`, for the
cartesian base-change square `h : IsPullback g' f' f g` with `f : X ⟶ Spec R` separated, the
base-changed RHS push–pull object `f'_*((g')^*(pushPullObj F (Over.mk j_σ)))` is the affine
pushforward of the tilde of the base-changed module of sections.

**CLOSED** — the two-step composite of the intended route: push `g'` through the per-σ
X-level Beck–Chevalley `twisted_cech_nerve_per_sigma` (now sorry-free) to turn
`(g')^*((j_σ)_*(j_σ)^* F)` into `pushPullObj ((g')^*F) (Over.mk j'_σ)` over the base-changed
intersection open `V' = coverInterOpen 𝒰' σ`, then apply the altitude-2 bridge
`pushPullObj_coverInter_pushforward_iso_tilde` for `f'` at the base-changed data
`(𝒰', (g')^* F)`.  Quasi-coherence of the base-changed module `(g')^* F` is the
general-morphism pullback stability `pullback_isQuasicoherent_hom`
(`PullbackQuasicoherent.lean`, Stacks 01BG).  The further identification of the
base-changed section module with the tensor `N ⊗_R R'`
(`coverInter_baseChanged_sections_iso_tensor`) is consumed downstream by the affine gap of
`pushPullObj_coverInter_baseChange`, not here.  Project-local; blueprint
`lem:coverinter_rhs_iso_tilde`. -/
noncomputable def pushPullObj_coverInter_baseChanged_pushforward_iso_tilde
    {R R' : CommRingCat.{u}}
    (f : X ⟶ Spec R) (g : Spec R' ⟶ Spec R) (f' : X' ⟶ Spec R') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) [IsSeparated f] [IsSeparated f']
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent)
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    (Scheme.Modules.pushforward f').obj
        ((Scheme.Modules.pullback g').obj
          (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))))) ≅
      (Scheme.Modules.pushforward (Spec.map (Spec.preimage
          ((coverInterOpen_isAffine f'
            ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
            σ).fromSpec ≫ f')))).obj
        (tilde (moduleSpecΓFunctor.obj
          ((Scheme.Modules.pushforward (coverInterOpen_isAffine f'
              ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
              σ).isoSpec.hom).obj
            ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen
                ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
                σ))).obj
              ((Scheme.Modules.pullback g').obj F))))) :=
  (Scheme.Modules.pushforward f').mapIso
      (twisted_cech_nerve_per_sigma f g f' g' h 𝒰 F hF σ) ≪≫
    pushPullObj_coverInter_pushforward_iso_tilde f'
      ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
      ((Scheme.Modules.pullback g').obj F)
      (pullback_isQuasicoherent_hom g' F hF) σ

/-! ### The per-σ affine-reduction heart: carving the ring pushout

The restricted cartesian square over the affine intersection open `V_σ` is carved into an
affine pushout square of rings, the base-changed section module is rewritten as the tensor
base change `N ⊗_R R'`, and the comparison becomes the sorry-free affine brick
`affinePushforwardPullbackBaseChange`. -/

/-- **Spec-cartesian ⟹ ring pushout** (converse of `isPullback_SpecMap_of_isPushout`).
A commutative square of rings whose `Spec`-square is cartesian in `Scheme` is a pushout of
rings: `Scheme.Spec` is fully faithful, so the cartesian square reflects to a pullback in
`CommRingCatᵒᵖ`, i.e. a pushout in `CommRingCat`.  Project-local; ingredient of the
ring-pushout carve in the proof of blueprint `lem:pushpullobj_coverinter_basechange`. -/
theorem isPushout_of_isPullback_SpecMap {A B C P : CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ C)
    (ρ : B ⟶ P) (σ : C ⟶ P)
    (H : IsPullback (Spec.map ρ) (Spec.map σ) (Spec.map φ) (Spec.map ψ)) :
    IsPushout φ ψ ρ σ := by
  have H' : IsPullback (Scheme.Spec.map ρ.op) (Scheme.Spec.map σ.op)
      (Scheme.Spec.map φ.op) (Scheme.Spec.map ψ.op) := H
  have H'' := IsPullback.of_map_of_faithful (F := Scheme.Spec) H'
  simpa using H''.unop.flip

/-- **The slice iso `pullback g' j_σ ≅ V'_σ`.**  The categorical pullback of the base change
`g'` along the intersection-open immersion `j_σ : V_σ ↪ X` is the base-changed intersection
open `V'_σ = coverInterOpen 𝒰' σ` of the base-changed cover: `pullback.fst` is an open
immersion with range `(g')⁻¹(V_σ)`, which is `V'_σ` by the cover-base-change identity
`coverInterOpen_baseChange_eq`.  Project-local. -/
noncomputable def coverInterOpen_baseChange_sliceIso
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover)
    {κ : Type} [Finite κ] (σ : κ → 𝒰.I₀) :
    (pullback g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)) : Scheme.{u}) ≅
      ↑(coverInterOpen ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
        h.isoPullback.symm.hom) σ) :=
  haveI hfst : IsOpenImmersion (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))) :=
    isOpenImmersion_of_isPullback_left g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))
      (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (restrictedCartesianAffinePushout g' 𝒰 σ)
  @IsOpenImmersion.isoOfRangeEq _ _ _
    (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
    (Scheme.Opens.ι (coverInterOpen ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom) σ))
    hfst inferInstance
    (by
      rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι,
        coverInterOpen_baseChange_eq f g f' g' h 𝒰 σ, Scheme.Opens.opensRange_ι])

/-- The slice iso composed with the base-changed open immersion is `pullback.fst`. -/
lemma coverInterOpen_baseChange_sliceIso_hom_ι
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover)
    {κ : Type} [Finite κ] (σ : κ → 𝒰.I₀) :
    (coverInterOpen_baseChange_sliceIso f g f' g' h 𝒰 σ).hom ≫
        Scheme.Opens.ι (coverInterOpen ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
          h.isoPullback.symm.hom) σ) =
      pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)) := by
  unfold coverInterOpen_baseChange_sliceIso
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Inverse form of `coverInterOpen_baseChange_sliceIso_hom_ι`. -/
lemma coverInterOpen_baseChange_sliceIso_inv_fst
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover)
    {κ : Type} [Finite κ] (σ : κ → 𝒰.I₀) :
    (coverInterOpen_baseChange_sliceIso f g f' g' h 𝒰 σ).inv ≫
        pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)) =
      Scheme.Opens.ι (coverInterOpen ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
        h.isoPullback.symm.hom) σ) := by
  rw [Iso.inv_comp_eq, ← coverInterOpen_baseChange_sliceIso_hom_ι f g f' g' h 𝒰 σ]

/-- The restriction of `g'` over the intersection open: `V'_σ ⟶ V_σ`. -/
noncomputable def coverInterOpen_baseChange_restrictedMap
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover)
    {κ : Type} [Finite κ] (σ : κ → 𝒰.I₀) :
    (↑(coverInterOpen ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
        h.isoPullback.symm.hom) σ) : Scheme.{u}) ⟶
      ↑(coverInterOpen 𝒰 σ) :=
  (coverInterOpen_baseChange_sliceIso f g f' g' h 𝒰 σ).inv ≫
    pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))

/-- The restricted square commutes: `ι_{V'_σ} ≫ g' = (g'|_σ) ≫ ι_{V_σ}`. -/
lemma coverInterOpen_baseChange_restrictedMap_comm
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover)
    {κ : Type} [Finite κ] (σ : κ → 𝒰.I₀) :
    Scheme.Opens.ι (coverInterOpen ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
        h.isoPullback.symm.hom) σ) ≫ g' =
      coverInterOpen_baseChange_restrictedMap f g f' g' h 𝒰 σ ≫
        Scheme.Opens.ι (coverInterOpen 𝒰 σ) := by
  unfold coverInterOpen_baseChange_restrictedMap
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    coverInterOpen_baseChange_sliceIso_inv_fst f g f' g' h 𝒰 σ]

section LiteralSpec

variable {R R' : CommRingCat.{u}}
variable (f : X ⟶ Spec R) (g : Spec R' ⟶ Spec R) (f' : X' ⟶ Spec R') (g' : X' ⟶ X)

/-- The corner ring map `ρ : Γ(X, V_σ) ⟶ Γ(X', V'_σ)` presenting the restricted top map
of the base-change square, conjugated by the two `isoSpec`s. -/
noncomputable def coverInterCornerRingMap
    (h : IsPullback g' f' f g) [IsSeparated f] [IsSeparated f']
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    Γ(X, coverInterOpen 𝒰 σ) ⟶
      Γ(X', coverInterOpen ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
        h.isoPullback.symm.hom) σ) :=
  Spec.preimage
    ((coverInterOpen_isAffine f'
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
        σ).isoSpec.inv ≫
      coverInterOpen_baseChange_restrictedMap f g f' g' h 𝒰 σ ≫
      (coverInterOpen_isAffine f 𝒰 σ).isoSpec.hom)

/-- `Spec` of the corner ring map recovers the `isoSpec`-conjugated restricted map. -/
lemma coverInterCornerRingMap_SpecMap
    (h : IsPullback g' f' f g) [IsSeparated f] [IsSeparated f']
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    Spec.map (coverInterCornerRingMap f g f' g' h 𝒰 σ) =
      (coverInterOpen_isAffine f'
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
        σ).isoSpec.inv ≫
      coverInterOpen_baseChange_restrictedMap f g f' g' h 𝒰 σ ≫
      (coverInterOpen_isAffine f 𝒰 σ).isoSpec.hom := by
  unfold coverInterCornerRingMap
  rw [Spec.map_preimage]

set_option backward.isDefEq.respectTransparency false in
/-- The restricted base-change square over the affine intersection open, as a
pushout of rings `(φ, ψ, ρ, ψ')` with corner `Γ(X', V'_σ)`. -/
theorem coverInter_ring_isPushout
    (h : IsPullback g' f' f g) [IsSeparated f] [IsSeparated f']
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    IsPushout (Spec.preimage ((coverInterOpen_isAffine f 𝒰 σ).fromSpec ≫ f))
      (Spec.preimage g)
      (coverInterCornerRingMap f g f' g' h 𝒰 σ)
      (Spec.preimage ((coverInterOpen_isAffine f'
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
        σ).fromSpec ≫ f')) := by
  apply isPushout_of_isPullback_SpecMap
  rw [Spec.map_preimage, Spec.map_preimage, Spec.map_preimage,
    coverInterCornerRingMap_SpecMap f g f' g' h 𝒰 σ]
  -- paste the restricted square onto the global cartesian square
  have H₁ : IsPullback (pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)) ≫ f')
      (Scheme.Opens.ι (coverInterOpen 𝒰 σ) ≫ f) g :=
    (restrictedCartesianAffinePushout g' 𝒰 σ).paste_vert h
  refine H₁.of_iso'
    ((coverInterOpen_isAffine f'
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
        σ).isoSpec.symm ≪≫ (coverInterOpen_baseChange_sliceIso f g f' g' h 𝒰 σ).symm)
    (coverInterOpen_isAffine f 𝒰 σ).isoSpec.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · -- e₁.hom ≫ pullback.snd = (ĩ.inv ≫ restrictedMap ≫ e.hom) ≫ e.inv
    simp [coverInterOpen_baseChange_restrictedMap]
  · -- e₁.hom ≫ (pullback.fst ≫ f') = (fromSpec ≫ f') ≫ 𝟙
    have hfac := reassoc_of% (coverInterOpen_baseChange_sliceIso_inv_fst f g f' g' h 𝒰 σ)
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Category.comp_id, Category.assoc]
    rw [hfac, ← IsAffineOpen.isoSpec_inv_ι, Category.assoc]
    simp only [Iso.symm_hom]
  · -- e₂.hom ≫ (V.ι ≫ f) = (fromSpec ≫ f) ≫ 𝟙
    simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    rw [← IsAffineOpen.isoSpec_inv_ι, Category.assoc]
  · simp

end LiteralSpec

section LiteralSpec2

variable {R R' : CommRingCat.{u}}
variable (f : X ⟶ Spec R) (g : Spec R' ⟶ Spec R) (f' : X' ⟶ Spec R') (g' : X' ⟶ X)

set_option maxHeartbeats 800000 in
-- Normalizing the affine-tilde/pullback isomorphism chain exceeds the default budget.
/-- **The base-changed section module is the corner extension of scalars**
(blueprint `lem:coverinter_rhs_tensor_rewrite`).  The module of sections of the base-changed
restriction `(j'_σ)^*((g')^* F)` over the affine `V'_σ = Spec B` is the extension of scalars
`B ⊗_{A_σ} N` of the module of sections `N = Γ(V_σ, F|_{V_σ})` along the corner ring map
`ρ : A_σ ⟶ B`: pull the restriction chain through the restricted square
(`coverInterOpen_baseChange_restrictedMap_comm`), rewrite `F|_{V_σ}` as a tilde
(`pullbackRestrict_iso_tilde`), and apply the affine tilde dictionary
`pullback_spec_tilde_iso` for `Spec ρ`.  Project-local; blueprint
`lem:coverinter_rhs_tensor_rewrite`. -/
noncomputable def coverInter_baseChanged_sections_tensor_rewrite
    (h : IsPullback g' f' f g) [IsSeparated f] [IsSeparated f']
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent)
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward (coverInterOpen_isAffine f'
            ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
            σ).isoSpec.hom).obj
          ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen
              ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
              σ))).obj
            ((Scheme.Modules.pullback g').obj F))) ≅
      (ModuleCat.extendScalars (coverInterCornerRingMap f g f' g' h 𝒰 σ).hom).obj
        (moduleSpecΓFunctor.obj
          ((Scheme.Modules.pushforward (coverInterOpen_isAffine f 𝒰 σ).isoSpec.hom).obj
            ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj F))) :=
  -- notation
  letI hV := coverInterOpen_isAffine f 𝒰 σ
  letI hV' := coverInterOpen_isAffine f'
    ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom) σ
  -- the V-side restriction is `tilde N` after pushing along `isoSpec`
  letI isoA : (Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj F ≅
      (Scheme.Modules.pullback hV.isoSpec.hom).obj
        (tilde (moduleSpecΓFunctor.obj
          ((Scheme.Modules.pushforward hV.isoSpec.hom).obj
            ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj F)))) :=
    (pushforwardEquivOfIso hV.isoSpec).unitIso.app
        ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj F) ≪≫
      (Scheme.Modules.pushforward hV.isoSpec.inv).mapIso
        (pullbackRestrict_iso_tilde F hF hV) ≪≫
      ((pullbackIsoPushforwardInv hV.isoSpec).app _).symm
  moduleSpecΓFunctor.mapIso
    ((Scheme.Modules.pushforward hV'.isoSpec.hom).mapIso
        ((Scheme.Modules.pullbackComp (Scheme.Opens.ι (coverInterOpen
              ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
              σ)) g').app F ≪≫
          (Scheme.Modules.pullbackCongr
            (coverInterOpen_baseChange_restrictedMap_comm f g f' g' h 𝒰 σ)).app F ≪≫
          ((Scheme.Modules.pullbackComp
              (coverInterOpen_baseChange_restrictedMap f g f' g' h 𝒰 σ)
              (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).symm).app F ≪≫
          (Scheme.Modules.pullback
              (coverInterOpen_baseChange_restrictedMap f g f' g' h 𝒰 σ)).mapIso isoA ≪≫
          (Scheme.Modules.pullbackComp
            (coverInterOpen_baseChange_restrictedMap f g f' g' h 𝒰 σ)
            hV.isoSpec.hom).app _ ≪≫
          (Scheme.Modules.pullbackCongr (by
            rw [coverInterCornerRingMap_SpecMap f g f' g' h 𝒰 σ, Iso.hom_inv_id_assoc])).app _ ≪≫
          ((Scheme.Modules.pullbackComp hV'.isoSpec.hom
            (Spec.map (coverInterCornerRingMap f g f' g' h 𝒰 σ))).symm).app _) ≪≫
      (Scheme.Modules.pushforward hV'.isoSpec.hom).mapIso
        ((pullbackIsoPushforwardInv hV'.isoSpec).app _) ≪≫
      (Scheme.Modules.pushforwardComp hV'.isoSpec.inv hV'.isoSpec.hom).app _ ≪≫
      (Scheme.Modules.pushforwardCongr hV'.isoSpec.inv_hom_id).app _ ≪≫
      (Scheme.Modules.pushforwardId _).app _ ≪≫
      pullback_spec_tilde_iso (coverInterCornerRingMap f g f' g' h 𝒰 σ) _) ≪≫
  (tilde.toTildeΓNatIso.app
    ((ModuleCat.extendScalars (coverInterCornerRingMap f g f' g' h 𝒰 σ).hom).obj
      (moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward hV.isoSpec.hom).obj
          ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj F))))).symm

/-- **Per-intersection-open base change over literal `Spec` bases.**  The assembly of the
four sorry-free bricks over `S = Spec R`, `S' = Spec R'`: LHS → tilde
(`pushPullObj_coverInter_pushforward_iso_tilde`), the affine base change
`affinePushforwardPullbackBaseChange` for the carved ring pushout
(`coverInter_ring_isPushout`), the tensor rewrite of the base-changed sections
(`coverInter_baseChanged_sections_tensor_rewrite`), and RHS → tilde
(`pushPullObj_coverInter_baseChanged_pushforward_iso_tilde`).  Project-local. -/
noncomputable def pushPullObj_coverInter_baseChange_spec
    (h : IsPullback g' f' f g) [IsSeparated f] [IsSeparated f']
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent)
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    (Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pushforward f).obj
          (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))))) ≅
      (Scheme.Modules.pushforward f').obj
        ((Scheme.Modules.pullback g').obj
          (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))))) :=
  (Scheme.Modules.pullback g).mapIso
      (pushPullObj_coverInter_pushforward_iso_tilde f 𝒰 F hF σ) ≪≫
    (Scheme.Modules.pullbackCongr (Spec.map_preimage g).symm).app _ ≪≫
    affinePushforwardPullbackBaseChange
      (Spec.preimage ((coverInterOpen_isAffine f 𝒰 σ).fromSpec ≫ f))
      (Spec.preimage g)
      (coverInterCornerRingMap f g f' g' h 𝒰 σ)
      (Spec.preimage ((coverInterOpen_isAffine f'
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
        σ).fromSpec ≫ f'))
      (coverInter_ring_isPushout f g f' g' h 𝒰 σ)
      (moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward (coverInterOpen_isAffine f 𝒰 σ).isoSpec.hom).obj
          ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj F))) ≪≫
    (Scheme.Modules.pushforward (Spec.map (Spec.preimage ((coverInterOpen_isAffine f'
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
        σ).fromSpec ≫ f')))).mapIso
      (pullback_spec_tilde_iso (coverInterCornerRingMap f g f' g' h 𝒰 σ) _ ≪≫
        (tilde.functor _).mapIso
          (coverInter_baseChanged_sections_tensor_rewrite f g f' g' h 𝒰 F hF σ).symm) ≪≫
    (pushPullObj_coverInter_baseChanged_pushforward_iso_tilde f g f' g' h 𝒰 F hF σ).symm

end LiteralSpec2

/-- **Per-intersection-open S-level base change** (the per-σ heart of the degreewise
Beck–Chevalley leaf, after the product decomposition `pushPull_sigma_iso`).  For a Čech
fibre-power intersection open `V = coverInterOpen 𝒰 σ` of `X` (affine under `[IsSeparated f]`
+ affine cover), the abstract base-change iso
```
  g^*(f_*(p_* p^* F))  ≅  f'_*(g'^*(p_* p^* F))   over the single open `V`
```
at the single-open push–pull object `pushPullObj F (Over.mk V.ι)`, for the cartesian square `h`
with affine base `S` and `S'`.

**CLOSED** — the abstract bases are transported to the literal `Spec Γ(S)`, `Spec Γ(S')` along
the `isoSpec` conjugation (both the cartesian square `h` and the push–pull data), where the
comparison is `pushPullObj_coverInter_baseChange_spec`: the restricted cartesian square over
the affine `V_σ` is carved into a ring pushout (`coverInter_ring_isPushout`, via the
Spec-cartesian ⟹ ring-pushout converse `isPushout_of_isPullback_SpecMap`), the genuinely
geometric content is the sorry-free affine brick `affinePushforwardPullbackBaseChange`, and
the two sides are matched by the tilde bridges (`pushPullObj_coverInter_pushforward_iso_tilde`
and `pushPullObj_coverInter_baseChanged_pushforward_iso_tilde`) together with the tensor
rewrite `coverInter_baseChanged_sections_tensor_rewrite`.  Project-local; blueprint
`lem:pushpullobj_coverinter_basechange`. -/
noncomputable def pushPullObj_coverInter_baseChange
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) [IsSeparated f] [IsAffine S] [IsAffine S']
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)] (F : X.Modules) (hF : F.IsQuasicoherent)
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    (Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pushforward f).obj
          (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))))) ≅
      (Scheme.Modules.pushforward f').obj
        ((Scheme.Modules.pullback g').obj
          (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))))) := by
  -- transport the cartesian square to the literal-`Spec` bases along the `isoSpec`s
  have h' : IsPullback g' (f' ≫ S'.isoSpec.hom) (f ≫ S.isoSpec.hom)
      (S'.isoSpec.inv ≫ (g ≫ S.isoSpec.hom)) :=
    h.of_iso (Iso.refl _) (Iso.refl _) S'.isoSpec S.isoSpec (by simp) (by simp) (by simp)
      (by simp)
  haveI : IsSeparated f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsSeparated) h ‹_›
  haveI : IsSeparated (f ≫ S.isoSpec.hom) := inferInstance
  haveI : IsSeparated (f' ≫ S'.isoSpec.hom) := inferInstance
  haveI : ∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 (f ≫ S.isoSpec.hom)
      (S'.isoSpec.inv ≫ (g ≫ S.isoSpec.hom))).pushforwardIso h'.isoPullback.symm.hom).X i) :=
    fun i => inferInstanceAs (IsAffine (pullback (𝒰.f i ≫ (f ≫ S.isoSpec.hom))
      (S'.isoSpec.inv ≫ (g ≫ S.isoSpec.hom))))
  exact
    (pushforwardEquivOfIso S'.isoSpec).unitIso.app _ ≪≫
      (Scheme.Modules.pushforward S'.isoSpec.inv).mapIso
        (((pullbackIsoPushforwardInv S'.isoSpec.symm).app _).symm ≪≫
          (Scheme.Modules.pullback S'.isoSpec.inv).mapIso
            ((Scheme.Modules.pullback g).mapIso
              ((pushforwardEquivOfIso S.isoSpec).unitIso.app _ ≪≫
                ((pullbackIsoPushforwardInv S.isoSpec).app _).symm) ≪≫
              (Scheme.Modules.pullbackComp g S.isoSpec.hom).app _) ≪≫
          (Scheme.Modules.pullbackComp S'.isoSpec.inv (g ≫ S.isoSpec.hom)).app _ ≪≫
          (Scheme.Modules.pullback (S'.isoSpec.inv ≫ (g ≫ S.isoSpec.hom))).mapIso
            ((Scheme.Modules.pushforwardComp f S.isoSpec.hom).app _) ≪≫
          pushPullObj_coverInter_baseChange_spec (f ≫ S.isoSpec.hom)
            (S'.isoSpec.inv ≫ (g ≫ S.isoSpec.hom)) (f' ≫ S'.isoSpec.hom) g' h' 𝒰 F hF σ ≪≫
          (Scheme.Modules.pushforwardComp f' S'.isoSpec.hom).symm.app _) ≪≫
      ((pushforwardEquivOfIso S'.isoSpec).unitIso.app _).symm

/-- **Beck–Chevalley natural iso through the Čech nerve** (Stacks 02KG, genuine content).
Whiskered through the Čech nerve, the cosimplicial `O_{S'}`-module obtained by pushing the
nerve forward along `f` and then pulling back along `g` is naturally isomorphic to the one
obtained by first pulling back along `g'` (at the `X`-level) and then pushing forward along
`f'`:
```
  g^* ∘ (pushforward f) ∘ drop(nerve 𝒰 F)  ≅  (pushforward f') ∘ g'^* ∘ drop(nerve 𝒰 F).
```
This is the Beck–Chevalley comparison for the cartesian square `h`, valid at every
cosimplicial degree. Each cosimplicial degree of the Čech nerve is a finite affine
intersection `U_{i₀…iₚ}` over which the cartesian square restricts to the affine pushout
square, so degreewise the asserted isomorphism is the sorry-free affine termwise base change
`affinePushforwardPullbackBaseChange` (FlatBaseChange.lean), assembled from the concrete tilde
dictionaries `pushforward_spec_tilde_iso`/`pullback_spec_tilde_iso` and the commutative-algebra
cancellation `cancelBaseChange` — *not* the canonical adjoint mate `pushforwardBaseChangeMap`.
Cosimplicial naturality is restriction along inclusions of finite affine intersections.

**DO NOT DISCHARGE THE `sorry` BELOW — REPLACE THIS DECLARATION** (run 0068 r2).  The residual
`sorry` is the `NatIso.ofComponents` naturality obligation, and it is an artefact of building the
isomorphism degreewise.  An earlier session established that it is unreachable as posed:
`Pi.hom_ext`, the tool that closed this project's other naturality squares, cannot fire because
the σ-decomposition sits mid-chain behind pushforward/pullback applications.  That diagnosis is
correct, and the conclusion to draw from it is that the construction is wrong, not that the
mathematics is hard.

Use `cech_pushforward_baseChange_natIso_of_isIso` instead: it builds the *same* isomorphism by
whiskering the natural transformation `cechOuterBC` (see the section note above), so naturality
holds by construction and the entire residue is one `IsIso` per degree — reduced further to one
per index tuple `σ` by `isIso_app_pi_of_isIso_app`.  Both are sorry-free.

**What is genuinely open, stated so it is not over-read.**  The per-σ obligation is
```
  IsIso ((cechOuterBC f g f' g' h).app (pushPullObj F (Over.mk j_σ))).
```
This file *already* has an isomorphism with exactly those endpoints,
`pushPullObj_coverInter_baseChange` — but an isomorphism between the same two objects is **not**
`IsIso` of a specific map, and treating it as one is the "groups agree ≠ maps agree" error this
workspace has recorded.  Two ways to close it, and the second looks right:

* identify `pushPullObj_coverInter_baseChange` *with* the mate's component (a compatibility
  square — the same shape of work that the tilde-bridge assembly already does, but on the mate);
* or split the mate.  `CategoryTheory.mateEquiv_vcomp` (mathlib) says the mate of a vertically
  composed square is the vertical composite of the mates.  Stack the *inner* square over `U_σ`
  (base change of the open immersion `j_σ` along `g'`) on top of the outer square `h`: the
  composite is the square for `j_σ ≫ f : U_σ ⟶ S`, a morphism **between affine schemes**, where
  flat base change is the affine brick `affinePushforwardPullbackBaseChange`; and the inner factor
  is `openImmersion_beckChevalley`, already sorry-free here.  So the per-σ mate would factor as
  (affine mate, `g` flat) ∘ᵥ (open-immersion mate, landed), with `mateEquiv_vcomp` as the glue.

Project-local; the residual is the genuine open content of Stacks 02KG/02KH. -/
noncomputable def cech_pushforward_baseChange_natIso
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    [IsSeparated f] [IsAffine S] [IsAffine S'] [∀ i, IsAffine (𝒰.X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    ((CosimplicialObject.whiskering S.Modules S'.Modules).obj
        (Scheme.Modules.pullback g)).obj
      (((CosimplicialObject.whiskering X.Modules S.Modules).obj
          (Scheme.Modules.pushforward f)).obj
        (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)))
      ≅ ((CosimplicialObject.whiskering X'.Modules S'.Modules).obj
          (Scheme.Modules.pushforward f')).obj
        (((CosimplicialObject.whiskering X.Modules X'.Modules).obj
            (Scheme.Modules.pullback g')).obj
          (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F))) :=
  -- The natural iso is constructed degreewise via `NatIso.ofComponents`.
  --
  -- COPRODUCT/PRODUCT LAYER — NOW CLOSED (compiling).  The degree-`n` fibre power
  -- `Yₙ = (coverCechNerveOver 𝒰).obj (op n)` is the coproduct `∐_σ U_σ` over index tuples
  -- `σ : Fin (n.len + 1) → 𝒰.I₀` of the intersection opens `U_σ = coverInterOpen 𝒰 σ`, so the
  -- push–pull object decomposes as a product `pushPullObj F Yₙ ≅ ∏_σ pushPullObj F (Over.mk j_σ)`
  -- by the sorry-free `pushPull_sigma_iso` (needs `[Finite 𝒰.I₀]`).  Both `pushforward` and
  -- `pullback` preserve this finite product (`PreservesProduct.iso`), so the degree-`n` `app`
  -- reduces *mechanically* (no remaining cosimplicial/sheaf plumbing) to the per-σ single-open
  -- base-change iso `pushPullObj_coverInter_baseChange`.
  --
  -- RESIDUAL (per-σ, the genuine open content): `pushPullObj_coverInter_baseChange` — the
  -- single-intersection-open S-level base change, dischargeable via the bridge
  -- `pushPullObj_pushforward_iso_tilde` (altitude 2) + the affine brick
  -- `cech_degree_affine_baseChange`; its body carries the affine-pushout-square-extraction sorry.
  -- `naturality` is the index-omission restriction compatibility of those degreewise isos.
  NatIso.ofComponents
    (fun n =>
      (Scheme.Modules.pullback g).mapIso
          ((Scheme.Modules.pushforward f).mapIso (pushPull_sigma_iso 𝒰 F n.len)) ≪≫
        (Scheme.Modules.pullback g).mapIso
          (Limits.PreservesProduct.iso (Scheme.Modules.pushforward f) _) ≪≫
        Limits.PreservesProduct.iso (Scheme.Modules.pullback g) _ ≪≫
        Limits.Pi.mapIso (fun σ => pushPullObj_coverInter_baseChange f g f' g' h 𝒰 F hF σ) ≪≫
        (Limits.PreservesProduct.iso (Scheme.Modules.pushforward f') _).symm ≪≫
        (Scheme.Modules.pushforward f').mapIso
          (Limits.PreservesProduct.iso (Scheme.Modules.pullback g') _).symm ≪≫
        (Scheme.Modules.pushforward f').mapIso
          ((Scheme.Modules.pullback g').mapIso (pushPull_sigma_iso 𝒰 F n.len).symm))
    (fun {n m} φ => sorry)

/-! ### The Čech nerve coface IN σ-COORDINATES — the statement the tree had but never wrote down

The twisted-nerve square is a compatibility between the per-σ identifications and the *coface*
maps.  To state it one needs to know what the coface **does** in σ-coordinates, and that fact was
already available in this project — one import away, in `CechSectionIdentification{Leg,LegMid1}`:

* `backboneIncl_nerveδ` — the σ'-summand inclusion of the degree-`(p+1)` backbone followed by the
  geometric coface equals the open inclusion `U_{σ'} ⊆ U_{σ'∘δᵏ}` followed by the summand inclusion
  at the **reindexed** tuple `σ' ∘ δᵏ`;
* `pushPull_sigma_iso_π_incl` — the σ-projection of `pushPull_sigma_iso` is `pushPullMap F` of that
  summand inclusion;
* `cechNerve_drop_δ` — the nerve's own coface **is** `pushPullMap F` of the geometric coface.

Three predecessor sessions priced the twisted square without these, because a `#check` in *this*
file failed and the absence was read as mathematical rather than cone-relative.  The lemma below
is what those three compose to, and it is the only genuinely new content on the σ-coordinate side.
-/

/-- **The coface of the dropped Čech nerve, read through the σ-product decomposition.**

Projecting `(drop.obj (CechNerve 𝒰 F)).δ k` onto the `σ'`-component of the degree-`(p+1)`
decomposition is the `σ' ∘ δᵏ`-component of the degree-`p` decomposition followed by the push–pull
restriction along the intersection-open inclusion `U_{σ'} ⊆ U_{σ' ∘ δᵏ}`:
```
  sigma_iso(p) ≫ π_{σ'∘δᵏ} ≫ pushPullMap F (interLegHom 𝒰 σ' k)
    = nerve.δ k ≫ sigma_iso(p+1) ≫ π_{σ'}.
```
So the coface is "reindex the tuple by `δᵏ`, then restrict" — index-omission on the nose.

Every input is a one-line composition of existing lemmas; what was missing was that they were not
in this file's import cone.  Project-local. -/
theorem cechNerve_backbone_δ_sigma (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules) (p : ℕ)
    (k : Fin (p + 2)) (σ' : Fin (p + 2) → 𝒰.I₀) :
    (pushPull_sigma_iso 𝒰 F p).hom ≫
        Pi.π (fun τ : Fin (p + 1) → 𝒰.I₀ =>
          pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 τ))))
          (σ' ∘ (SimplexCategory.δ k).toOrderHom) ≫
        pushPullMap F (interLegHom 𝒰 σ' k)
      = pushPullMap F ((coverCechNerveOver 𝒰).map ((SimplexCategory.δ k).op)) ≫
          (pushPull_sigma_iso 𝒰 F (p + 1)).hom ≫
          Pi.π (fun τ : Fin (p + 2) → 𝒰.I₀ =>
            pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 τ)))) σ' := by
  -- Turn every σ-projection into `pushPullMap` of a summand inclusion, then use that `pushPullMap`
  -- is contravariantly functorial: both sides become `pushPullMap F` of a composite in `Over X`,
  -- and `backboneIncl_nerveδ` is exactly the equality of those two composites.
  rw [← Category.assoc, pushPull_sigma_iso_π_incl, pushPull_sigma_iso_π_incl,
    ← pushPullMap_comp, ← pushPullMap_comp, backboneIncl_nerveδ]

/-- `cechNerve_backbone_δ_sigma`, with the geometric coface replaced by the nerve's own `δ`.

Split from it because `CosimplicialObject C` and `SimplexCategory ⥤ C` are `rfl`-equal spellings
that make `rw` report a motive failure ("not type-correct under `instances` transparency") when the
coface is rewritten inside the σ-projection composite — the geometric statement carries no
cosimplicial vocabulary, so it has no such boundary. -/
theorem cechNerve_drop_δ_sigma (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules) (p : ℕ)
    (k : Fin (p + 2)) (σ' : Fin (p + 2) → 𝒰.I₀) :
    (pushPull_sigma_iso 𝒰 F p).hom ≫
        Pi.π (fun τ : Fin (p + 1) → 𝒰.I₀ =>
          pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 τ))))
          (σ' ∘ (SimplexCategory.δ k).toOrderHom) ≫
        pushPullMap F (interLegHom 𝒰 σ' k)
      = (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ k ≫
          (pushPull_sigma_iso 𝒰 F (p + 1)).hom ≫
          Pi.π (fun τ : Fin (p + 2) → 𝒰.I₀ =>
            pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 τ)))) σ' :=
  (cechNerve_backbone_δ_sigma 𝒰 F p k σ').trans
    (congrArg (fun m => m ≫ (pushPull_sigma_iso 𝒰 F (p + 1)).hom ≫
      Pi.π (fun τ : Fin (p + 2) → 𝒰.I₀ =>
        pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 τ)))) σ')
      (cechNerve_drop_δ 𝒰 F k).symm)

/-- **The base-changed nerve is the nerve of the base-changed data** (Stacks 02KG, the
mechanical half). Applying `(g')^*` (at the `X`-level) to the dropped Čech nerve of
`(𝒰, F)` yields the dropped Čech nerve of the base-changed data `(𝒰', (g')^* F)`, where
`𝒰' = (openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom` is the base change of
`𝒰` along `g'`:
```
  g'^* ∘ drop(nerve 𝒰 F)  ≅  drop(nerve 𝒰' (g'^* F)).
```
The geometric backbone `coverCechNerve` of `𝒰` base-changes to that of `𝒰'`: the fibre
powers `U_{i₀} ×_X ⋯ ×_X U_{iₚ}` commute with the base change `g'` (pullback preserves fibre
products), so the preimages `(g')⁻¹(U_{i₀…iₚ})` are exactly the corresponding intersections
of `𝒰'`. The pullback then commutes with the push–pull functor `pushPullFunctor` termwise —
itself a Beck–Chevalley identification `g'^* (p_* p^* F) ≅ p'_* p'^* (g'^* F)` for the
restricted cartesian square — and the identifications are compatible with the cosimplicial
structure maps because both are induced by the same inclusions of intersections.

**THE WHISKERING CORRECTION DOES *NOT* TRANSFER TO THIS LEAF — the two leaves are asymmetric**
(run 0068 r2; recorded because the obvious guess is wrong).

For `cech_pushforward_baseChange_natIso` the naturality obligation evaporates because *both* sides
are `N ⋙ (a composite of functors)` for one and the same cosimplicial object
`N = drop.obj (CechNerve 𝒰 F)`, so a whiskered natural transformation maps between them and
naturality is inherited.  Here that fails: the left side is indeed `N ⋙ g'^*`, but the right side
is `drop.obj (CechNerve 𝒰' (g'^* F))` — **a different cosimplicial object**, the nerve of the
base-changed cover, not a whiskering of `N`.  There is no natural transformation to whisker,
because the source and target cosimplicial objects are not built from a common one.

So this leaf's naturality is genuine work, and it is a *comparison of two nerves*: the content is
that the geometric backbone base-changes, `coverInterOpen 𝒰' σ = (g')⁻¹(coverInterOpen 𝒰 σ)`
(`coverInterOpen_baseChange_eq`, landed), **compatibly with the index-omission maps** — i.e. that
the `isoOfRangeEq` slice identifications used per σ in `twisted_cech_nerve_per_sigma` commute with
the inclusions `U_τ ⊆ U_σ` for `σ` a subtuple of `τ`.  That is a statement about the cover
base-change identification, not about modules, and it is the honest residue here.

**THAT RESIDUE IS NOW ISOLATED AND THE REST IS PROVED (run 0068 r4) — DO NOT DISCHARGE THIS `sorry`,
AND DO NOT READ THE PARAGRAPH ABOVE AS A PRICE.**  Two things changed.

*The general-`φ` obligation was over-strong.*  This declaration's only consumer is
`cechComplex_baseChange_cosimplicialIso`, and *its* only consumer takes
`alternatingCofaceMapComplex`, whose differential is `∑ᵢ (-1)ⁱ • δᵢ` — no codegeneracy appears
anywhere downstream.  `alternatingCofaceComplexIsoOfDelta` therefore builds the same complex
isomorphism from **coface** compatibility alone.  That is what brings the obligation into range:
this tree's σ-coordinate lemmas are stated for `δ k` only, and no general-`φ` analogue exists in
this workspace or in mathlib, so the wide obligation was unprovable from the lemmas we have while
the narrow one is not.

*And the coface square is proved from a per-σ hypothesis.*  See `cechNerve_drop_δ_sigma` (the
coface in σ-coordinates is "reindex by `δᵏ`, then restrict"), `sigmaAssembled_δ_square` and
`twistedNerve_δ_square_concrete`.  What is left is `TwistedPerSigmaDeltaCompat`: that the per-σ
Beck–Chevalley isos commute with the intersection-open inclusions — exactly the residue named in
prose above, now a Lean equation between composites of landed `sorry`-free declarations, with no
nerve, product or cosimplicial vocabulary in it.

Equivalently, and this is the useful way to see what is missing: `twisted_cech_nerve_per_sigma` is
built *per σ*, and the residue is its **naturality in the over-object**.  A `Y`-natural
Beck–Chevalley for `pushPullFunctor` would give it as a component, and a workspace-wide search found
none — `pushPullFunctor` has no API at all beyond being whiskered once in `cechNerveCosimplicial`.

Project-local. -/
noncomputable def twisted_cech_nerve_iso
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    [IsSeparated f] [IsAffine S] [∀ i, IsAffine (𝒰.X i)]
    [Finite ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).I₀]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    ((CosimplicialObject.whiskering X.Modules X'.Modules).obj
        (Scheme.Modules.pullback g')).obj
      (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F))
      ≅ CosimplicialObject.Augmented.drop.obj
          (CechNerve ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
            h.isoPullback.symm.hom) ((Scheme.Modules.pullback g').obj F)) :=
  -- LHS COPRODUCT/PRODUCT LAYER — NOW CLOSED (compiling).  The degree-`n` `app` obligation is the
  -- X-level Beck–Chevalley iso
  --     `(pullback g').obj (pushPullObj F Yₙ) ≅ pushPullObj (g'^* F) Y'ₙ`
  -- (`g'^*(p_* p^* F) ≅ p'_* p'^*(g'^* F)`), where `Yₙ = (coverCechNerveOver 𝒰).obj (op n)` and
  -- `Y'ₙ = (coverCechNerveOver 𝒰').obj (op n)` for the base-changed cover `𝒰'`.  The LHS
  -- decomposes as a product over the index tuples `σ` via the sorry-free `pushPull_sigma_iso` and
  -- preservation of finite products by `pullback g'` (`PreservesProduct.iso`):
  --     LHS ≅ ∏_σ (pullback g').obj (pushPullObj F (Over.mk j_σ)).
  --
  -- RESIDUAL (the genuine open content + the RHS-matching obstruction): the remaining goal is
  --     `∏_σ (pullback g').obj (pushPullObj F (Over.mk j_σ)) ≅ pushPullObj (g'^* F) Y'ₙ`.
  -- The per-σ X-level Beck–Chevalley iso `(pullback g').obj (pushPullObj F (Over.mk j_σ)) ≅
  -- pushPullObj (g'^* F) (Over.mk j'_σ)` (base change of push–pull along the open immersion j_σ,
  -- for the restricted cartesian square over `U_σ`) is the per-σ content; reassembling
  -- the σ-product on the RHS would use `(pushPull_sigma_iso 𝒰' (g'^* F) n.len).symm`, but
  -- that needs
  -- `[Finite 𝒰'.I₀]` and `[∀ i, IsAffine (𝒰'.X i)]` for the base-changed cover `𝒰'`, which are NOT
  -- available in this signature (the X-level leaf carries no `[IsAffine S']`; the
  -- base-changed cover members' affineness is the geometric cover-base-change route
  -- `coverInterOpen 𝒰' σ = g'⁻¹(U_σ)`).
  -- That cover-base-change identification is the residual Beck–Chevalley heart of this leaf.
  -- STEP-1 sig extension landed `[Finite 𝒰'.I₀]`/`[∀ i, IsAffine (𝒰'.X i)]` for the base-changed
  -- cover `𝒰'`, so the σ-product on the RHS *can now* be reassembled by
  -- `(pushPull_sigma_iso 𝒰' (g'^* F) n.len).symm`.  The residual per-σ content is isolated into the
  -- named leaf `twisted_cech_nerve_per_sigma` (the open-immersion Beck–Chevalley and
  -- cover-base-change identification). Only the cosimplicial `naturality` remains beyond
  -- that leaf.
  NatIso.ofComponents
    (fun n =>
      (Scheme.Modules.pullback g').mapIso (pushPull_sigma_iso 𝒰 F n.len) ≪≫
        Limits.PreservesProduct.iso (Scheme.Modules.pullback g') _ ≪≫
        Limits.Pi.mapIso (fun σ => twisted_cech_nerve_per_sigma f g f' g' h 𝒰 F hF σ) ≪≫
        (pushPull_sigma_iso ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
          h.isoPullback.symm.hom) ((Scheme.Modules.pullback g').obj F) n.len).symm)
    (fun {n m} φ => sorry)

/-! ### The twisted leaf, restated as a δ-square — and what remains is stated in σ-coordinates

`twisted_cech_nerve_iso` is consumed only through `alternatingCofaceMapComplex`, whose differential
is `∑ᵢ (-1)ⁱ • δᵢ`.  So the full cosimplicial isomorphism is more than any consumer needs:
`alternatingCofaceComplexIsoOfDelta` (above) builds the same complex isomorphism from the
degreewise family plus **coface** compatibility.  The declarations below carry out that
replacement, and the point of doing so is that the coface obligation is stateable in the
σ-coordinates that `cechNerve_drop_δ_sigma` provides, whereas the general-`φ` one is not.

The residue is named `twistedPerSigmaDeltaCompat` and is one equation between two composites of
*existing* maps, with no cosimplicial vocabulary left in it: that the per-σ Beck–Chevalley
identifications `twisted_cech_nerve_per_sigma` commute with the reindex-and-restrict description of
the coface.  That is the honest content — the same statement the previous docstring named
informally ("the `isoOfRangeEq` slice identifications commute with the inclusions `U_τ ⊆ U_σ`"),
now written as a Lean equation a session can attack directly. -/

/-- **The per-σ compatibility that the twisted leaf's coface square reduces to.**

Read it as: base-change-then-restrict = restrict-then-base-change, for the intersection-open
inclusion `U_{σ'} ⊆ U_{σ' ∘ δᵏ}` and its base change `U'_{σ'} ⊆ U'_{σ' ∘ δᵏ}`.  The left vertical
maps are the per-σ Beck–Chevalley isos `twisted_cech_nerve_per_sigma`; the horizontals are the
push–pull restrictions along `interLegHom`, pulled back along `g'` on the source side.

This is stated as a hypothesis rather than proved: it is the residue of `twisted_cech_nerve_iso`,
carved so that everything *around* it is discharged.  Both sides are composites of declarations
that already exist and are `sorry`-free.  Project-local. -/
def TwistedPerSigmaDeltaCompat (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [IsSeparated f] [IsAffine S]
    [∀ i, IsAffine (𝒰.X i)] (F : X.Modules) (hF : F.IsQuasicoherent) : Prop :=
  ∀ (p : ℕ) (k : Fin (p + 2)) (σ' : Fin (p + 2) → 𝒰.I₀),
    (twisted_cech_nerve_per_sigma f g f' g' h 𝒰 F hF
        (σ' ∘ (SimplexCategory.δ k).toOrderHom)).hom ≫
      pushPullMap ((Scheme.Modules.pullback g').obj F)
        (interLegHom ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
          h.isoPullback.symm.hom) σ' k)
      = (Scheme.Modules.pullback g').map (pushPullMap F (interLegHom 𝒰 σ' k)) ≫
          (twisted_cech_nerve_per_sigma f g f' g' h 𝒰 F hF σ').hom

/-! #### The σ-product calculus, over an ABSTRACT target cover

Everything below about assembling the degreewise component out of the per-σ isomorphisms is
independent of *which* cover of `X'` is on the right.  It is stated that way deliberately, and the
reason is mechanical rather than aesthetic: the actual target cover is
`(openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom`, whose `IsIso` instance is keyed on
the spelling `h.isoPullback.symm.hom`.  Any `rw`/`simp` that normalises that to `h.isoPullback.inv`
— `Iso.symm_hom` does, and it is hard to avoid once the composite is being reassociated — makes the
goal fail to typecheck, reported as "motive is not type correct" naming the `IsIso` argument.
Abstracting the cover as a variable removes the term from the proof entirely, so the trap cannot
fire; the real cover is supplied only at the application site, where nothing is rewritten. -/

section SigmaCalculus

variable {Y : Scheme.{u}} (q : Y ⟶ X)

/-- The degreewise component of a twisted-nerve-style identification, assembled from a family of
per-σ isomorphisms and the source σ-product decomposition.

The target is an **arbitrary** family `T` of `𝒪_Y`-modules indexed by tuples, not the base-changed
cover's push–pull objects.  Two reasons, both mechanical.  First, the real target cover is
`(openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom`, whose `IsIso` instance is keyed on
the spelling `h.isoPullback.symm.hom`; any `rw`/`simp` normalising that to `h.isoPullback.inv`
(`Iso.symm_hom` does) makes the goal fail to typecheck, reported as "motive is not type correct".
Second — **and this half is retracted, see `baseChangedCover_I₀`** — an earlier revision of this
section believed that cover's index type agreed with `𝒰.I₀` only *propositionally* and threaded a
transport `hI ▸ σ l` through every statement.  It is `rfl`, and the transport was the thing making
the reindexed tuple and the tuple-then-reindexed disagree as terms.  The first reason stands on its
own and is why the abstraction is kept: the real data is supplied at the application site, where
nothing is rewritten. -/
noncomputable def sigmaAssembledComponent (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (F : X.Modules) (n : ℕ) (T : (Fin (n + 1) → 𝒰.I₀) → Y.Modules)
    (e : ∀ σ, (Scheme.Modules.pullback q).obj
        (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) ≅ T σ) :
    (Scheme.Modules.pullback q).obj
        (pushPullObj F ((coverCechNerveOver 𝒰).obj (Opposite.op (SimplexCategory.mk n))))
      ≅ ∏ᶜ T :=
  (Scheme.Modules.pullback q).mapIso (pushPull_sigma_iso 𝒰 F n) ≪≫
    Limits.PreservesProduct.iso (Scheme.Modules.pullback q) _ ≪≫
    Limits.Pi.mapIso e

/-- **The σ-projection of the assembled component**: decompose the source, project, apply the
per-σ iso.  Pure `piComparison`/`Pi.map` calculus. -/
theorem sigmaAssembledComponent_π (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (F : X.Modules) (n : ℕ) (T : (Fin (n + 1) → 𝒰.I₀) → Y.Modules)
    (e : ∀ σ, (Scheme.Modules.pullback q).obj
        (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) ≅ T σ)
    (σ : Fin (n + 1) → 𝒰.I₀) :
    (sigmaAssembledComponent q 𝒰 F n T e).hom ≫ Limits.Pi.π T σ
      = (Scheme.Modules.pullback q).map ((pushPull_sigma_iso 𝒰 F n).hom ≫
          Limits.Pi.π (fun τ : Fin (n + 1) → 𝒰.I₀ =>
            pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 τ)))) σ) ≫ (e σ).hom := by
  rw [sigmaAssembledComponent, Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, Category.assoc, Limits.Pi.mapIso_hom_π,
    Limits.PreservesProduct.iso_hom, Limits.piComparison_comp_π_assoc, ← Functor.map_comp_assoc]

/-- **The coface square for the assembled components, from the per-σ compatibility alone.**

This is the reduction, stated over an abstract target cover.  The hypothesis `hcompat` is
"base-change-then-restrict = restrict-then-base-change" for the intersection-open inclusions; the
conclusion is that the assembled degreewise components commute with the two Čech cofaces, after the
target-side σ-decomposition.

Why `Pi.hom_ext` fires here and did not for the original `NatIso.ofComponents` obligation: the
earlier diagnosis was that the σ-decomposition sits mid-chain behind pushforward/pullback
applications, so the projections cannot be pushed through.  With `cechNerve_drop_δ_sigma` the coface
*is* reindex-then-restrict in σ-coordinates, so both sides reduce to per-σ' statements and `hcompat`
closes each. -/
theorem sigmaAssembled_δ_square (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (F : X.Modules) (n : ℕ)
    (T : (Fin (n + 1) → 𝒰.I₀) → Y.Modules) (T' : (Fin (n + 2) → 𝒰.I₀) → Y.Modules)
    (e : ∀ σ, (Scheme.Modules.pullback q).obj
        (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) ≅ T σ)
    (e' : ∀ σ, (Scheme.Modules.pullback q).obj
        (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) ≅ T' σ)
    (k : Fin (n + 2))
    -- the target-side restriction maps, indexed by the top tuple
    (r : ∀ σ' : Fin (n + 2) → 𝒰.I₀, T (σ' ∘ (SimplexCategory.δ k).toOrderHom) ⟶ T' σ')
    (hcompat : ∀ σ' : Fin (n + 2) → 𝒰.I₀,
      (e (σ' ∘ (SimplexCategory.δ k).toOrderHom)).hom ≫ r σ'
        = (Scheme.Modules.pullback q).map (pushPullMap F (interLegHom 𝒰 σ' k)) ≫ (e' σ').hom) :
    (sigmaAssembledComponent q 𝒰 F n T e).hom ≫
        Limits.Pi.lift (fun σ' : Fin (n + 2) → 𝒰.I₀ =>
          Limits.Pi.π T (σ' ∘ (SimplexCategory.δ k).toOrderHom) ≫ r σ')
      = (Scheme.Modules.pullback q).map
            (pushPullMap F ((coverCechNerveOver 𝒰).map ((SimplexCategory.δ k).op))) ≫
          (sigmaAssembledComponent q 𝒰 F (n + 1) T' e').hom := by
  -- Compare σ'-projections of the target product.
  refine Limits.Pi.hom_ext _ _ (fun σ' => ?_)
  rw [Category.assoc, Limits.Pi.lift_π]
  -- LHS: the σ'-leg is "project at the OMITTED tuple, then restrict"; feed it to `hcompat`.
  rw [← Category.assoc, sigmaAssembledComponent_π, Category.assoc, hcompat σ']
  -- RHS: project the assembled component at σ', then the σ-coordinate coface formula closes it.
  rw [Category.assoc, sigmaAssembledComponent_π, ← Category.assoc, ← Functor.map_comp,
    ← Category.assoc, ← Functor.map_comp, ← cechNerve_backbone_δ_sigma 𝒰 F n k σ',
    Category.assoc]

end SigmaCalculus

/-- **The twisted leaf's coface square, at the real base-change data.**  `sigmaAssembled_δ_square`
instantiated with the per-σ Beck–Chevalley isomorphisms `twisted_cech_nerve_per_sigma` — so the
hypothesis is exactly `TwistedPerSigmaDeltaCompat`, and everything else is discharged.

`r` is the target-side restriction, supplied as an argument rather than computed: the base-changed
cover's index type is only propositionally `𝒰.I₀`, so `interLegHom 𝒰' (transport σ') k` does not
have the type `T (σ' ∘ δᵏ) ⟶ T' σ'` on the nose.  Naming it as data is what keeps the transport out
of the proof; the caller supplies it with the compatibility it must satisfy.  Project-local. -/
theorem twistedNerve_δ_square
    (g' : X' ⟶ X) (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (F : X.Modules) (n : ℕ) (k : Fin (n + 2))
    (T : (Fin (n + 1) → 𝒰.I₀) → X'.Modules) (T' : (Fin (n + 2) → 𝒰.I₀) → X'.Modules)
    (e : ∀ σ, (Scheme.Modules.pullback g').obj
        (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) ≅ T σ)
    (e' : ∀ σ, (Scheme.Modules.pullback g').obj
        (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) ≅ T' σ)
    (r : ∀ σ' : Fin (n + 2) → 𝒰.I₀, T (σ' ∘ (SimplexCategory.δ k).toOrderHom) ⟶ T' σ')
    (hcompat : ∀ σ' : Fin (n + 2) → 𝒰.I₀,
      (e (σ' ∘ (SimplexCategory.δ k).toOrderHom)).hom ≫ r σ'
        = (Scheme.Modules.pullback g').map (pushPullMap F (interLegHom 𝒰 σ' k)) ≫ (e' σ').hom) :
    (sigmaAssembledComponent g' 𝒰 F n T e).hom ≫
        Limits.Pi.lift (fun σ' : Fin (n + 2) → 𝒰.I₀ =>
          Limits.Pi.π T (σ' ∘ (SimplexCategory.δ k).toOrderHom) ≫ r σ')
      = (Scheme.Modules.pullback g').map
            (pushPullMap F ((coverCechNerveOver 𝒰).map ((SimplexCategory.δ k).op))) ≫
          (sigmaAssembledComponent g' 𝒰 F (n + 1) T' e').hom :=
  sigmaAssembled_δ_square g' 𝒰 F n T T' e e' k r hcompat

/-- **The base-changed cover has the SAME index type, definitionally.**  `pushforwardIso` is built
from `Cover.copy` with `I₀ := 𝒰.I₀`, and `openCoverOfLeft` keeps the index type of `𝒰`, so this is
`rfl`.

Worth a named lemma because an earlier revision of the σ-calculus above carried a transport
`hI ▸ σ l` through every statement on the assumption that the agreement was only propositional.
It is not, and the transport was pure cost: it does not commute syntactically with `σ ∘ δᵏ`, which
is what made the reindexed tuple and the tuple-then-reindexed disagree as terms.  Project-local. -/
theorem baseChangedCover_I₀ (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) :
    ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom).I₀ = 𝒰.I₀ :=
  rfl

/-- The per-σ isomorphisms of the twisted leaf, as a target family for
`sigmaAssembledComponent` — `twisted_cech_nerve_per_sigma` read as data.  Witnesses that the
abstract σ-calculus above applies to the real base-change situation and is not vacuous.

Note the target: `coverInterOpen 𝒰' σ` for a tuple `σ` into `𝒰.I₀`, with **no transport**, which
typechecks by `baseChangedCover_I₀`. -/
noncomputable def twistedPerSigmaTarget
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [IsSeparated f] [IsAffine S]
    [∀ i, IsAffine (𝒰.X i)] (F : X.Modules) (hF : F.IsQuasicoherent) (n : ℕ) :
    ∀ σ : Fin (n + 1) → 𝒰.I₀, (Scheme.Modules.pullback g').obj
        (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))))
      ≅ pushPullObj ((Scheme.Modules.pullback g').obj F)
          (Over.mk (Scheme.Opens.ι (coverInterOpen
            ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
              h.isoPullback.symm.hom) σ))) :=
  fun σ => twisted_cech_nerve_per_sigma f g f' g' h 𝒰 F hF σ

/-- **The twisted leaf's coface square at the ACTUAL base-change data**, with the target family and
the target-side restriction both the real ones — not abstract placeholders.

The restriction is `pushPullMap (g'^*F) (interLegHom 𝒰' σ' k)`, i.e. exactly the base-changed
intersection-open inclusion, and the target is `twistedPerSigmaTarget`.  The remaining hypothesis is
`TwistedPerSigmaDeltaCompat` in a per-degree form.  So the twisted leaf's coface obligation is fully
reduced: no product, no nerve, no cosimplicial vocabulary and no abstraction left in it — only the
commutation of the per-σ Beck–Chevalley isomorphisms with the intersection-open inclusions.
Project-local. -/
theorem twistedNerve_δ_square_concrete
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    [IsSeparated f] [IsAffine S] [∀ i, IsAffine (𝒰.X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent) (n : ℕ) (k : Fin (n + 2))
    (hcompat : ∀ σ' : Fin (n + 2) → 𝒰.I₀,
      (twistedPerSigmaTarget f g f' g' h 𝒰 F hF n
            (σ' ∘ (SimplexCategory.δ k).toOrderHom)).hom ≫
          pushPullMap ((Scheme.Modules.pullback g').obj F)
            (interLegHom ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
              h.isoPullback.symm.hom) σ' k)
        = (Scheme.Modules.pullback g').map (pushPullMap F (interLegHom 𝒰 σ' k)) ≫
            (twistedPerSigmaTarget f g f' g' h 𝒰 F hF (n + 1) σ').hom) :
    (sigmaAssembledComponent g' 𝒰 F n _ (twistedPerSigmaTarget f g f' g' h 𝒰 F hF n)).hom ≫
        Limits.Pi.lift (fun σ' : Fin (n + 2) → 𝒰.I₀ =>
          Limits.Pi.π _ (σ' ∘ (SimplexCategory.δ k).toOrderHom) ≫
            pushPullMap ((Scheme.Modules.pullback g').obj F)
              (interLegHom ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
                h.isoPullback.symm.hom) σ' k))
      = (Scheme.Modules.pullback g').map
            (pushPullMap F ((coverCechNerveOver 𝒰).map ((SimplexCategory.δ k).op))) ≫
          (sigmaAssembledComponent g' 𝒰 F (n + 1) _
            (twistedPerSigmaTarget f g f' g' h 𝒰 F hF (n + 1))).hom :=
  sigmaAssembled_δ_square g' 𝒰 F n _ _
    (twistedPerSigmaTarget f g f' g' h 𝒰 F hF n)
    (twistedPerSigmaTarget f g f' g' h 𝒰 F hF (n + 1)) k _ hcompat

/-- **The cosimplicial Beck–Chevalley iso `e`** consumed by
`cechComplex_baseChange_iso_of_cosimplicialIso`. It is the whiskered composite of the
Beck–Chevalley natural iso `cech_pushforward_baseChange_natIso` with the twisted-nerve
identification `twisted_cech_nerve_iso` pushed forward along `f'`:
```
  e = cech_pushforward_baseChange_natIso ≪≫ (pushforward f')_* .mapIso twisted_cech_nerve_iso.
```
Project-local; isolates the open content into the two lemmas above. -/
noncomputable def cechComplex_baseChange_cosimplicialIso
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    [IsSeparated f] [IsAffine S] [IsAffine S'] [∀ i, IsAffine (𝒰.X i)]
    [Finite ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).I₀]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    ((CosimplicialObject.whiskering S.Modules S'.Modules).obj
        (Scheme.Modules.pullback g)).obj
      (((CosimplicialObject.whiskering X.Modules S.Modules).obj
          (Scheme.Modules.pushforward f)).obj
        (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)))
      ≅ ((CosimplicialObject.whiskering X'.Modules S'.Modules).obj
          (Scheme.Modules.pushforward f')).obj
        (CosimplicialObject.Augmented.drop.obj
          (CechNerve ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
            h.isoPullback.symm.hom) ((Scheme.Modules.pullback g').obj F))) :=
  cech_pushforward_baseChange_natIso f g f' g' h 𝒰 F hF ≪≫
    ((CosimplicialObject.whiskering X'.Modules S'.Modules).obj
        (Scheme.Modules.pushforward f')).mapIso (twisted_cech_nerve_iso f g f' g' h 𝒰 F hF)

/-- **The cosimplicial Beck–Chevalley iso with the S-level leaf REMOVED** (run 0068 r3).  Same
statement as `cechComplex_baseChange_cosimplicialIso`, but its first factor is the `sorry`-free
`cech_pushforward_baseChange_natIso_flat` rather than `cech_pushforward_baseChange_natIso`.  So its
proof term contains **exactly one** open leaf — the twisted-nerve naturality square — not two, and
that square is the only obstruction left between this file and Stacks 02KG/02KH.

The price is the three instance binders `[Flat g]`, `[QuasiCompact f]`, `[QuasiSeparated f]`; all
three are carried by `cech_flatBaseChange` already (`[QuasiSeparated f]` follows from
`[IsSeparated f]` by a mathlib instance), so this is a strict drop-in for that route.
Project-local. -/
noncomputable def cechComplex_baseChange_cosimplicialIso_flat
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    [Flat g] [QuasiCompact f] [IsSeparated f] [IsAffine S] [IsAffine S']
    [∀ i, IsAffine (𝒰.X i)]
    [Finite ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).I₀]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    ((CosimplicialObject.whiskering S.Modules S'.Modules).obj
        (Scheme.Modules.pullback g)).obj
      (((CosimplicialObject.whiskering X.Modules S.Modules).obj
          (Scheme.Modules.pushforward f)).obj
        (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)))
      ≅ ((CosimplicialObject.whiskering X'.Modules S'.Modules).obj
          (Scheme.Modules.pushforward f')).obj
        (CosimplicialObject.Augmented.drop.obj
          (CechNerve ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
            h.isoPullback.symm.hom) ((Scheme.Modules.pullback g').obj F))) :=
  cech_pushforward_baseChange_natIso_flat f g f' g' h 𝒰 F hF ≪≫
    ((CosimplicialObject.whiskering X'.Modules S'.Modules).obj
        (Scheme.Modules.pushforward f')).mapIso (twisted_cech_nerve_iso f g f' g' h 𝒰 F hF)

/-- **Tensorial base change of the Čech complex** (Stacks 02KG; *load-bearing*, OPEN).
Applying `g^*` degreewise to the relative Čech complex `Č•(𝒰, F)` yields the relative
Čech complex `Č•(𝒰', g'^* F)` of the base-changed data. Sorry-free *modulo* the cosimplicial
Beck–Chevalley iso `cechComplex_baseChange_cosimplicialIso`: the live route is the whiskered
composite of `cech_pushforward_baseChange_natIso` (degreewise → the per-σ affine-reduction heart
`pushPullObj_coverInter_baseChange`, which routes through the altitude-2 bridge
`pushPullObj_pushforward_iso_tilde` to the **sorry-free** affine termwise base change
`affinePushforwardPullbackBaseChange` via the carved ring-pushout
`restrictedCartesianAffinePushout`)
with the twisted-nerve identification `twisted_cech_nerve_iso` (per-σ
`twisted_cech_nerve_per_sigma`, the X-level open-immersion Beck–Chevalley
`openImmersion_beckChevalley` over the cover-base-change identity `coverInterOpen_baseChange_eq`).
The route uses the concrete-tilde non-mate brick, NOT the walled adjoint-mate machinery. *(STUB —
the residual content is the named per-σ leaves above; the genuine open content of 02KH/02KG.)* -/
noncomputable def cechComplex_baseChange_iso
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) [QuasiCompact f] [IsSeparated f]
    [IsAffine S] [IsAffine S']
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] [∀ i, IsAffine (𝒰.X i)]
    [Finite ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).I₀]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (CechComplex f 𝒰 F)
      ≅ CechComplex f'
          ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
          ((Scheme.Modules.pullback g').obj F) :=
  -- Reduced (iter-304) to the factoring lemma: the homology/differential plumbing is
  -- discharged, so the SOLE residual obligation is the cosimplicial Beck–Chevalley iso `e`
  -- (`g^* ∘ f_* ∘ nerve ≅ f'_* ∘ g'^* ∘ nerve'`). Decomposed (iter-315): `e` is supplied by
  -- `cechComplex_baseChange_cosimplicialIso`, the whiskered composite of the Beck–Chevalley
  -- natural iso `cech_pushforward_baseChange_natIso` with the twisted-nerve identification
  -- `twisted_cech_nerve_iso`. The monolithic sorry is thereby replaced by those two named,
  -- blueprinted residuals — the genuine open content of Stacks 02KG/02KH.
  cechComplex_baseChange_iso_of_cosimplicialIso f g f' g' h 𝒰 F
    (cechComplex_baseChange_cosimplicialIso f g f' g' h 𝒰 F hF)

/-- **The tensorial base change of the Čech complex, with the S-level leaf REMOVED** (run 0068 r3).
Same conclusion as `cechComplex_baseChange_iso`, built from
`cechComplex_baseChange_cosimplicialIso_flat`, so `cech_pushforward_baseChange_natIso` — one of the
two open leaves of that declaration — is **absent from this proof term**.  The single remaining
leaf is `twisted_cech_nerve_iso`'s naturality square.

Extra binder over `cechComplex_baseChange_iso`: `[Flat g]`, which every consumer of that
declaration in this file already has.  Project-local. -/
noncomputable def cechComplex_baseChange_iso_flat
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [IsSeparated f]
    [IsAffine S] [IsAffine S']
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] [∀ i, IsAffine (𝒰.X i)]
    [Finite ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).I₀]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (CechComplex f 𝒰 F)
      ≅ CechComplex f'
          ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
          ((Scheme.Modules.pullback g').obj F) :=
  cechComplex_baseChange_iso_of_cosimplicialIso f g f' g' h 𝒰 F
    (cechComplex_baseChange_cosimplicialIso_flat f g f' g' h 𝒰 F hF)

/-- **Flat base change for the Čech higher direct images** (Stacks 02KH,
`lemma-flat-base-change-cohomology`).

Given the cartesian square
```
  X' --g'--> X
  |f'        |f
  v          v
  S' --g---> S
```
with `f` separated and quasi-compact, `F` quasi-coherent, `F' = (g')^* F`, and
`g` flat, for every `i ≥ 0` the canonical base-change map between the
unconditional Čech higher direct images is an isomorphism
```
  g^*(Rⁱ f_* F) ≅ Rⁱ f'_* ((g')^* F).
```
Equivalently, for `S = Spec A`, `S' = Spec B` with `A → B` flat, the comparison
`Hⁱ(X, F) ⊗_A B → Hⁱ(X', F')` of `B`-modules is an isomorphism.

We state the isomorphism as `Nonempty (… ≅ …)`; `𝒰` is a finite affine open cover of `X`,
and the cover of `X' = X ×_S S'` used on the right is its canonical base change along `g'`
(`Scheme.Pullback.openCoverOfLeft 𝒰 f g` transported to `X'` via `IsPullback.isoPullback`). -/
theorem cech_flatBaseChange
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [IsSeparated f]
    [IsAffine S] [IsAffine S']
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] [∀ i, IsAffine (𝒰.X i)]
    [Finite ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).I₀]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent) (i : ℕ) :
    Nonempty ((Scheme.Modules.pullback g).obj (cechHigherDirectImage f 𝒰 F i) ≅
      cechHigherDirectImage f'
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
        ((Scheme.Modules.pullback g').obj F) i) := by
  -- Re-wired (iter-304): the assembly is now sorry-free *modulo* the single load-bearing
  -- leaf-2 iso `cechComplex_baseChange_iso`. The two-step composite is:
  --   (1) `pullback_mapHC_homologyIso` (flat exactness, complex level) commuting `g^*` with
  --       Čech homology, and (2) `homologyMapIso` of the tensorial base-change iso
  --       `cechComplex_baseChange_iso`. `cechHigherDirectImage = (CechComplex …).homology i`
  --       definitionally, so the two endpoints match up to `rfl`.
  exact ⟨(pullback_mapHC_homologyIso g (CechComplex f 𝒰 F) i).symm ≪≫
    HomologicalComplex.homologyMapIso (cechComplex_baseChange_iso f g f' g' h 𝒰 F hF) i⟩

/-- **Flat base change for the Čech higher direct images, with the flat-exactness leaf REMOVED
from the proof term** (Stacks 02KH).

Identical conclusion to `cech_flatBaseChange`, and identical hypotheses except that the two
quasi-coherence facts the *homology half* needs are taken as named hypotheses `h₂`, `h₃` on the
degree-`i` short complex of `Č•(𝒰, F)`.  In exchange, the homology half is routed through
`pullback_mapHC_homologyIso_of_isQuasicoherent` rather than `pullback_mapHC_homologyIso`, so
`pullback_preservesMonomorphisms` does not appear in the proof term at all.

**What this does and does not buy.**  It does *not* make flat base change axiom-clean.  Its second
half is `cechComplex_baseChange_iso`, and that declaration still reaches **both** cosimplicial
naturality `sorry`s — it is the `_flat` variant `cechComplex_baseChange_iso_flat` that reaches only
`twisted_cech_nerve_iso`'s.  So for the one-leaf route use `cech_flatBaseChange_oneLeaf`, whose
hypotheses and conclusion are identical to this theorem's.  (An earlier revision of this sentence
said *this* declaration carried "exactly one" as of run 0068 r3: false of the declaration it named,
true only of what the reader should use instead.  Caught by a fresh-context reviewer.)

What this theorem does buy is that the *flat-exactness* leaf is no longer one of the reasons it is
unproved — that source of the leak is gone, and what remains is the Beck–Chevalley heart rather than
a statement about arbitrary modules that nobody needs.

**`h₂`/`h₃` ARE NOW DISCHARGEABLE, and `cech_flatBaseChange_qcoh` below does it** — see
`isQuasicoherent_cechComplex_X`.  Prefer that form; this one is kept because taking the two
quasi-coherence facts as hypotheses is what makes the *reduction* legible, and because a caller
with a different complex can still use it.

(Two earlier revisions of this paragraph were wrong, both in the direction of over-stating an
absence.  The first asserted that closure of quasi-coherence under finite products is missing from
mathlib and this workspace: false over an affine base, which is the only case this theorem is
stated in — `isQuasicoherent_pi_of_isAffineBase`.  The second then advertised the remaining route
as "`isQuasicoherent_pullback_opens` plus `pushforward_isQuasicoherent`, so what remains is
bookkeeping": at the time, `Scheme.Modules.pushforward_isQuasicoherent` was indeed not in this
file's import cone.  **THE THIRD REVISION — the fix to the second — WAS ALSO WRONG, in the opposite
direction.**  It said `Picard/QuotScheme.lean` "is deliberately not imported because it carries
`sorry`s".  That was false at HEAD: QuotScheme's import cone is `sorry`-free — six modules, five
of them new to this file; its seven `sorry` *mentions* are docstrings asserting a chain is
sorry-free — and it does not import this file.  Run 0068 r3 imports it, which is how Stacks 01XJ
and — far more importantly — `canonicalBaseChangeMap_isIso` became available here.  So an
over-stated absence about a *module* had silently priced two *theorems* as unavailable, one of them
this file's priority obligation.
The affine special case built instead is still used and still correct:
`isQuasicoherent_pushforward_specMap` and `isQuasicoherent_pushforward_of_isAffine`.)
Project-local. -/
theorem cech_flatBaseChange_of_termsQuasicoherent
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [IsSeparated f]
    [IsAffine S] [IsAffine S']
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] [∀ i, IsAffine (𝒰.X i)]
    [Finite ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).I₀]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent) (i : ℕ)
    (h₂ : ((CechComplex f 𝒰 F).sc i).X₂.IsQuasicoherent)
    (h₃ : ((CechComplex f 𝒰 F).sc i).X₃.IsQuasicoherent) :
    Nonempty ((Scheme.Modules.pullback g).obj (cechHigherDirectImage f 𝒰 F i) ≅
      cechHigherDirectImage f'
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
        ((Scheme.Modules.pullback g').obj F) i) :=
  ⟨(pullback_mapHC_homologyIso_of_isQuasicoherent g (CechComplex f 𝒰 F) i h₂ h₃).symm ≪≫
    HomologicalComplex.homologyMapIso (cechComplex_baseChange_iso f g f' g' h 𝒰 F hF) i⟩

/-- **Flat base change for the Čech higher direct images, with the flat-exactness leaf REMOVED and
NO extra hypotheses** (Stacks 02KH).

The form to use.  Hypotheses and conclusion are **exactly** those of `cech_flatBaseChange` — no
extra binder of any kind (an earlier revision carried `[X.IsSeparated]`; that was unnecessary,
since `coverInterOpen_isAffine` *derives* separatedness of `X` from `[IsSeparated f]` and
`[IsAffine S]`).  The two quasi-coherence facts that
`cech_flatBaseChange_of_termsQuasicoherent` takes as `h₂`/`h₃` are *discharged* here by
`isQuasicoherent_cechComplex_X`, so the homology half runs through
`pullback_mapHC_homologyIso_of_isQuasicoherent` and `pullback_preservesMonomorphisms` does not
appear in the proof term.

**What is left, stated exactly.**  This is still not axiom-clean, because
`cechComplex_baseChange_iso` carries the two cosimplicial naturality `sorry`s of
`cech_pushforward_baseChange_natIso` and `twisted_cech_nerve_iso` (Stacks 02KG).  Those are the
*only* obstruction between this tree and flat base change — the flat-exactness leaf is gone from
this route, and so are the two quasi-coherence hypotheses.

**PREFER `cech_flatBaseChange_oneLeaf` (run 0068 r3), whose hypotheses and conclusion are
identical.**  It routes the tensorial half through `cechComplex_baseChange_iso_flat`, so the
S-level cosimplicial leaf is gone too and exactly ONE `sorry` — the twisted-nerve square — stands
between it and Stacks 02KH.  This declaration is retained because its proof term is the legible
two-step reduction.  Measure both at `scripts/axiom-frontier.lean` §6d/§6g. -/
theorem cech_flatBaseChange_qcoh
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [IsSeparated f]
    [IsAffine S] [IsAffine S']
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] [h𝒰 : ∀ i, IsAffine (𝒰.X i)]
    [Finite ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).I₀]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent) (i : ℕ) :
    Nonempty ((Scheme.Modules.pullback g).obj (cechHigherDirectImage f 𝒰 F i) ≅
      cechHigherDirectImage f'
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
        ((Scheme.Modules.pullback g').obj F) i) :=
  -- Affineness of the Čech intersection opens is DERIVED, not assumed:
  -- `coverInterOpen_isAffine` gets it from `[IsSeparated f]` + `[IsAffine S]` (the composite
  -- `terminal.from X = f ≫ terminal.from S` is separated).  That is why this theorem needs no
  -- `[X.IsSeparated]` binder and its hypotheses are *exactly* `cech_flatBaseChange`'s.
  --
  -- `h₂` is at degree `i` and `h₃` at `(ComplexShape.up ℕ).next i`, written explicitly rather than
  -- as `_`: `isQuasicoherent_cechComplex_X` proves *every* degree, so an underscore would elaborate
  -- to whatever unification produced and a reader could not check which.
  cech_flatBaseChange_of_termsQuasicoherent f g f' g' h 𝒰 F hF i
    (isQuasicoherent_cechComplex_X f 𝒰 (fun σ => coverInterOpen_isAffine f 𝒰 σ) F hF i)
    (isQuasicoherent_cechComplex_X f 𝒰 (fun σ => coverInterOpen_isAffine f 𝒰 σ) F hF
      ((ComplexShape.up ℕ).next i))

/-- **Flat base change for the Čech higher direct images — ONE OPEN LEAF LEFT** (Stacks 02KH; run
0068 r3, the form to consume).

Hypotheses and conclusion are **exactly** those of `cech_flatBaseChange` and
`cech_flatBaseChange_qcoh`: no extra binder of any kind.  What changed is the proof term, and it
changed twice over:

* the *flat-exactness* leaf `pullback_preservesMonomorphisms` is absent (inherited from
  `cech_flatBaseChange_qcoh`'s route through `pullback_mapHC_homologyIso_of_isQuasicoherent`);
* the *S-level cosimplicial* leaf `cech_pushforward_baseChange_natIso` is absent too, because the
  tensorial half now runs through `cechComplex_baseChange_iso_flat`.

So the **only** remaining reason this theorem is not axiom-clean is the naturality square of
`twisted_cech_nerve_iso` — the compatibility of the cover base-change identification
`coverInterOpen_baseChange_eq` with the index-omission maps.  Everything else in Stacks 02KG/02KH is
proved here: the per-σ mate is `canonicalBaseChangeMap_isIso` (see `isIso_cechOuterBC_coverInter`),
the per-σ X-level Beck–Chevalley is `twisted_cech_nerve_per_sigma`, and the homology half is the
quasi-coherent kernel route.

Measure at `scripts/axiom-frontier.lean` §6e. -/
theorem cech_flatBaseChange_oneLeaf
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [IsSeparated f]
    [IsAffine S] [IsAffine S']
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] [h𝒰 : ∀ i, IsAffine (𝒰.X i)]
    [Finite ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).I₀]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent) (i : ℕ) :
    Nonempty ((Scheme.Modules.pullback g).obj (cechHigherDirectImage f 𝒰 F i) ≅
      cechHigherDirectImage f'
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
        ((Scheme.Modules.pullback g').obj F) i) :=
  ⟨(pullback_mapHC_homologyIso_of_isQuasicoherent g (CechComplex f 𝒰 F) i
      (isQuasicoherent_cechComplex_X f 𝒰 (fun σ => coverInterOpen_isAffine f 𝒰 σ) F hF i)
      (isQuasicoherent_cechComplex_X f 𝒰 (fun σ => coverInterOpen_isAffine f 𝒰 σ) F hF
        ((ComplexShape.up ℕ).next i))).symm ≪≫
    HomologicalComplex.homologyMapIso
      (cechComplex_baseChange_iso_flat f g f' g' h 𝒰 F hF) i⟩

/-! ## `TwistedPerSigmaDeltaCompat` SPLIT IN TWO — one half free, the other named (run 0068 r4)

`twisted_cech_nerve_per_sigma` is, **by `rfl`** (`tcnps_eq`), a two-layer composite:

* the Beck–Chevalley iso `bcv` for the square restricted over `U_σ`, and
* a slice transport `pushPullObjCongr _ eIso` along the `isoOfRangeEq` identification of
  `pullback.fst g' (ι U_σ)` with `ι (coverInterOpen 𝒰' σ)`.

So the per-σ compatibility splits along that seam, and the two halves are not comparable in cost.

**HALF (b) IS FREE, AND THIS RETRACTS THIS FILE'S OWN PRICING OF THE RESIDUE.**  The
`twisted_cech_nerve_iso` docstring names the residue in prose as "the `isoOfRangeEq` slice
identifications commute with the inclusions `U_τ ⊆ U_σ`".  That sentence describes half (b), and
half (b) costs nothing: both composites are morphisms of `Over X'` into an object whose
structure map is an open immersion, hence a **mono**, so they agree by `ext` + `cancel_mono`
with no geometry, no cover base change and no transport (`slice_compat`).  Anything priced
against that sentence is mispriced; the real content is half (a).

**HALF (a) IS THE CRUX, and it is naturality in the SQUARE, not in the module.**
`bc_square_naturality` states it: for affine opens `V₀ ≤ W₀` and their base changes along `g'`, the
two restricted-square Beck–Chevalley isos commute with restriction along the inclusion.  It is *not*
`openImmersion_bareBC_app_eq` (that is naturality in the module) nor `pushPullMap_comp`/`_id` (those
are functor laws in the slice variable) — nothing in the tree relates the mate across a *change of
square*.

Two facts make it actionable, both machine-checked here and neither previously recorded:

* `openImmersion_bareBC` **never uses cartesianness** — `bareBC_eq_of_w` says it is `bareBC_of_w` at
  `hsq.w`, by `rfl`.  So the mate exists for *any* commuting square, including the degenerate one
  with right edge `𝟙 X`, which is the shape `pushPullMap` has.  The `IsPullback` binder is
  decoration on this leaf; only the invertibility node consumes it.
* the two restricted squares **paste vertically**: `inclusion_square_comm` gives
  `gV ≫ homOfLE hle = w.left ≫ gW` by cancelling the mono `W₀.ι`.  So `mateEquiv_vcomp` is the
  applicable glue.

MEASURED NEGATIVE, recorded so it is not re-attempted as a triviality: "`pushPullMap F u` is the
degenerate-square mate" — the composite of `(pullbackId X).inv`, `bareBC_of_w (𝟙 X) …` and the two
telescope corrections — **typechecks but is not `rfl`**, and `simp` with `bareBC_of_w`,
`pushPullMap`, `rawPushPullMap`, `mateEquiv_apply` does not close it (`aesop_cat` times out in
`whnf`).  It is a genuine lemma, and it is the brick half (a) needs.

`TwistedPerSigmaDeltaCompat` follows from half (a) alone: `twistedPerSigmaCompat_of_bcNaturality`.
Everything else in this section is `sorry`-free.

**ITEM (i), THE WIRING, IS NOW WRITTEN (run 0068 r5) — ONE ITEM REMAINS, NOT TWO.**
`sigmaAssembled_δ_square` and `twistedNerve_δ_square_concrete` prove the coface square in the
**σ-decomposed** form: their target is a `Pi` product, and the target-side coface appears as a
`Pi.lift`.  Feeding that to `alternatingCofaceComplexIsoOfDelta` at `twisted_cech_nerve_iso`'s *own*
spelling — where the target is the base-changed nerve's degree object — was named here as unwritten
bookkeeping.  It is `twistedComponent_δ_square` below, and the bridge is that the **same**
σ-coordinate coface formula applies to the base-changed cover: `cechNerve_backbone_δ_sigma` at `𝒰'`
says its nerve's coface, read through `pushPull_sigma_iso 𝒰'`, is reindex-then-restrict — exactly
the `Pi.lift` shape.  No transport: the index types agree on the nose (`baseChangedCover_I₀`).

So the honest state is one item:

  (ii) half (a) — mate-naturality in the SQUARE, now named `BcSquareNaturality` and shown
       equivalent to a pushforward-free form `BcSquarePullbackSide`.

Neither is a `sorry` in this file; `twisted_cech_nerve_iso`'s own square is still the only one. -/

/-! ### (i) THE WIRING — the σ-decomposed square, at `twisted_cech_nerve_iso`'s own spelling

`sigmaAssembled_δ_square` proves the coface square with the *target* a `Pi` product and the
target-side coface a `Pi.lift`.  `alternatingCofaceComplexIsoOfDelta` wants it at the spelling
`twisted_cech_nerve_iso` uses: source `(g'^* ∘ drop(nerve 𝒰 F))`, target `drop(nerve 𝒰' (g'^*F))`,
whose degree object is `pushPullObj (g'^*F) ((coverCechNerveOver 𝒰').obj (op ⦋n⦌))`.

The bridge is `cechNerve_drop_δ_sigma` **for the base-changed cover** — the same lemma, instantiated
at `𝒰'` instead of `𝒰`.  It says the target nerve's coface, read through `pushPull_sigma_iso 𝒰'`,
is reindex-then-restrict, which is exactly the `Pi.lift` shape.  Nothing new is needed: the index
type of `𝒰'` is `𝒰.I₀` on the nose (`baseChangedCover_I₀`), so the two σ-families are the same
family and no transport appears.  This is what r4 left unwritten. -/

/-- The base-changed cover, abbreviated.  Named so the wiring lemmas below can mention it without
repeating the `pushforwardIso`/`isoPullback.symm.hom` spelling whose `IsIso` instance is
spelling-keyed (see the `SigmaCalculus` section note). -/
noncomputable abbrev bcCover (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) : X'.OpenCover :=
  (Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom

/-- **The target-side σ-decomposition of the base-changed nerve's coface.**
`cechNerve_drop_δ_sigma` at the base-changed cover `𝒰'` and the base-changed module `g'^*F`,
with the index type silently `𝒰.I₀` (`baseChangedCover_I₀`, `rfl`).

Read it as: `sigma_iso(𝒰',n) ≫ π_{σ'∘δᵏ} ≫ restrict = nerve'.δ k ≫ sigma_iso(𝒰',n+1) ≫ π_{σ'}` —
so post-composing with `(pushPull_sigma_iso 𝒰' _ n).symm` turns the `Pi.lift` produced by
`sigmaAssembled_δ_square` into the nerve's own coface.  Project-local. -/
theorem bcNerve_drop_δ_sigma (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover)
    [Finite (bcCover f g f' g' h 𝒰).I₀] (F : X.Modules) (n : ℕ) (k : Fin (n + 2))
    (σ' : Fin (n + 2) → 𝒰.I₀) :
    (pushPull_sigma_iso (bcCover f g f' g' h 𝒰) ((Scheme.Modules.pullback g').obj F) n).hom ≫
        Pi.π (fun τ : Fin (n + 1) → 𝒰.I₀ =>
          pushPullObj ((Scheme.Modules.pullback g').obj F)
            (Over.mk (Scheme.Opens.ι (coverInterOpen (bcCover f g f' g' h 𝒰) τ))))
          (σ' ∘ (SimplexCategory.δ k).toOrderHom) ≫
        pushPullMap ((Scheme.Modules.pullback g').obj F)
          (interLegHom (bcCover f g f' g' h 𝒰) σ' k)
      = (CosimplicialObject.Augmented.drop.obj
            (CechNerve (bcCover f g f' g' h 𝒰) ((Scheme.Modules.pullback g').obj F))).δ k ≫
          (pushPull_sigma_iso (bcCover f g f' g' h 𝒰)
            ((Scheme.Modules.pullback g').obj F) (n + 1)).hom ≫
          Pi.π (fun τ : Fin (n + 2) → 𝒰.I₀ =>
            pushPullObj ((Scheme.Modules.pullback g').obj F)
              (Over.mk (Scheme.Opens.ι (coverInterOpen (bcCover f g f' g' h 𝒰) τ)))) σ' :=
  cechNerve_drop_δ_sigma (bcCover f g f' g' h 𝒰)
    ((Scheme.Modules.pullback g').obj F) n k σ'

/-- **The degreewise component of `twisted_cech_nerve_iso`, factored through the σ-product.**
`sigmaAssembledComponent` for the real per-σ family, followed by the base-changed cover's own
σ-decomposition read backwards.  This is *definitionally* the component
`twisted_cech_nerve_iso` uses — same four factors, same order — so it is a renaming that makes
the `Pi` product an explicit intermediate object the coface square can be stated against.
Project-local. -/
noncomputable def twistedComponent (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    [IsSeparated f] [IsAffine S] [∀ i, IsAffine (𝒰.X i)]
    [Finite (bcCover f g f' g' h 𝒰).I₀]
    (F : X.Modules) (hF : F.IsQuasicoherent) (n : ℕ) :
    (Scheme.Modules.pullback g').obj
        (pushPullObj F ((coverCechNerveOver 𝒰).obj (Opposite.op (SimplexCategory.mk n))))
      ≅ pushPullObj ((Scheme.Modules.pullback g').obj F)
          ((coverCechNerveOver (bcCover f g f' g' h 𝒰)).obj
            (Opposite.op (SimplexCategory.mk n))) :=
  sigmaAssembledComponent g' 𝒰 F n _ (twistedPerSigmaTarget f g f' g' h 𝒰 F hF n) ≪≫
    (pushPull_sigma_iso (bcCover f g f' g' h 𝒰)
      ((Scheme.Modules.pullback g').obj F) n).symm

/-- `twistedComponent` IS the degreewise component of `twisted_cech_nerve_iso`.

Both are `(pullback g').mapIso (sigma_iso 𝒰) ≪≫ PreservesProduct.iso ≪≫ Pi.mapIso (per-σ) ≪≫
(sigma_iso 𝒰').symm`: `sigmaAssembledComponent` is literally the first three factors and
`twistedPerSigmaTarget` is literally the per-σ family.  This is what licenses reading the coface
square below as a statement about `twisted_cech_nerve_iso`.

**NOT `rfl`, and the reason is worth recording** (a first attempt asserted it and the kernel timed
out rather than refusing).  `≪≫` is right-associated, so `twisted_cech_nerve_iso` spells its
component `A ≪≫ (B ≪≫ (C ≪≫ D))` while factoring the first three into
`sigmaAssembledComponent` forces `(A ≪≫ (B ≪≫ C)) ≪≫ D`.  Those differ by two applications of
`Category.assoc` — an associativity of composition that no category has by definition.  The
content is nil; the `rfl` claim was not. -/
theorem twistedComponent_eq (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    [IsSeparated f] [IsAffine S] [∀ i, IsAffine (𝒰.X i)]
    [Finite (bcCover f g f' g' h 𝒰).I₀]
    (F : X.Modules) (hF : F.IsQuasicoherent) (n : ℕ) :
    twistedComponent f g f' g' h 𝒰 F hF n
      = (Scheme.Modules.pullback g').mapIso (pushPull_sigma_iso 𝒰 F n) ≪≫
          Limits.PreservesProduct.iso (Scheme.Modules.pullback g') _ ≪≫
          Limits.Pi.mapIso (fun σ => twisted_cech_nerve_per_sigma f g f' g' h 𝒰 F hF σ) ≪≫
          (pushPull_sigma_iso (bcCover f g f' g' h 𝒰)
            ((Scheme.Modules.pullback g').obj F) n).symm := by
  apply Iso.ext
  simp only [twistedComponent, sigmaAssembledComponent, Iso.trans_hom, Category.assoc]
  rfl

/-- **`sigmaAssembled_δ_square` with the target's σ-decomposition CANCELLED**, over abstract target
data.  Given the target degree objects `Tobj`, `Tobj'`, their σ-decompositions `A`, `B` and a target
coface `dT` whose σ-coordinate description is the hypothesis `hlift`, the assembled components
composed with `A.symm` / `B.symm` commute with `dT`.

Stated over variables for the same reason as the `SigmaCalculus` section above: the real `A`, `B`
are `pushPull_sigma_iso` at the base-changed cover, whose `IsIso` instance is keyed on the spelling
`h.isoPullback.symm.hom`.  Any `Iso.symm_hom` rewrite normalises that to `.inv` and the goal stops
typechecking ("motive is not type correct"); and the real `Pi` families then print with the cover
unfolded, so the `Pi.lift` in `hlift` and the one in `sigmaAssembled_δ_square` fail to match
syntactically even though they are the same term.  With everything a variable neither can fire.
Project-local. -/
theorem sigmaAssembled_δ_square_cancel {Y : Scheme.{u}} (q : Y ⟶ X)
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules) (n : ℕ) (k : Fin (n + 2))
    {Tobj Tobj' : Y.Modules}
    (T : (Fin (n + 1) → 𝒰.I₀) → Y.Modules) (T' : (Fin (n + 2) → 𝒰.I₀) → Y.Modules)
    (e : ∀ σ, (Scheme.Modules.pullback q).obj
        (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) ≅ T σ)
    (e' : ∀ σ, (Scheme.Modules.pullback q).obj
        (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) ≅ T' σ)
    (A : Tobj ≅ ∏ᶜ T) (B : Tobj' ≅ ∏ᶜ T') (dT : Tobj ⟶ Tobj')
    (r : ∀ σ' : Fin (n + 2) → 𝒰.I₀, T (σ' ∘ (SimplexCategory.δ k).toOrderHom) ⟶ T' σ')
    (hcompat : ∀ σ' : Fin (n + 2) → 𝒰.I₀,
      (e (σ' ∘ (SimplexCategory.δ k).toOrderHom)).hom ≫ r σ'
        = (Scheme.Modules.pullback q).map (pushPullMap F (interLegHom 𝒰 σ' k)) ≫ (e' σ').hom)
    (hlift : dT ≫ B.hom
      = A.hom ≫ Limits.Pi.lift (fun σ' : Fin (n + 2) → 𝒰.I₀ =>
          Limits.Pi.π T (σ' ∘ (SimplexCategory.δ k).toOrderHom) ≫ r σ')) :
    (sigmaAssembledComponent q 𝒰 F n T e ≪≫ A.symm).hom ≫ dT
      = (Scheme.Modules.pullback q).map
            (pushPullMap F ((coverCechNerveOver 𝒰).map ((SimplexCategory.δ k).op))) ≫
          (sigmaAssembledComponent q 𝒰 F (n + 1) T' e' ≪≫ B.symm).hom := by
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, Category.assoc]
  -- Cancel `A` and `B` against `hlift`: the target coface, conjugated, IS the `Pi.lift`.
  have h1 : A.inv ≫ dT
      = Limits.Pi.lift (fun σ' : Fin (n + 2) → 𝒰.I₀ =>
          Limits.Pi.π T (σ' ∘ (SimplexCategory.δ k).toOrderHom) ≫ r σ') ≫ B.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hlift, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [h1, ← Category.assoc, sigmaAssembled_δ_square q 𝒰 F n T T' e e' k r hcompat,
    Category.assoc]

/-- **THE WIRING, COMPLETE: the coface square at the nerve's own spelling.**

`sigmaAssembled_δ_square` gives the square with the target a `Pi` product and the target coface a
`Pi.lift`.  This turns both into the base-changed nerve's own vocabulary:

* the source coface `(drop.obj (CechNerve 𝒰 F)).δ k` replaces `pushPullMap F (backbone.map δᵏ)`
  by `cechNerve_drop_δ`;
* the target `Pi` product is replaced by `pushPullObj (g'^*F) (backbone' (op ⦋n⦌))` through
  `pushPull_sigma_iso 𝒰'`, and the `Pi.lift` becomes `(drop.obj (CechNerve 𝒰' (g'^*F))).δ k`
  by `bcNerve_drop_δ_sigma` — the *same* σ-coordinate lemma at the base-changed cover.

That last step is the one r4 named as unwritten.  It is `Pi.hom_ext` again: two maps into
`∏ᶜ (per-σ targets)` agree because their σ'-legs do, and each leg is `bcNerve_drop_δ_sigma`.

With this, `alternatingCofaceComplexIsoOfDelta` applies to `twistedComponent` directly, so the
`twisted_cech_nerve_iso` obligation is `TwistedPerSigmaDeltaCompat` and nothing else.
Project-local. -/
theorem twistedComponent_δ_square (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    [IsSeparated f] [IsAffine S] [∀ i, IsAffine (𝒰.X i)]
    [Finite (bcCover f g f' g' h 𝒰).I₀]
    (F : X.Modules) (hF : F.IsQuasicoherent)
    (hcompat : TwistedPerSigmaDeltaCompat f g f' g' h 𝒰 F hF)
    (n : ℕ) (k : Fin (n + 2)) :
    (twistedComponent f g f' g' h 𝒰 F hF n).hom ≫
        (CosimplicialObject.Augmented.drop.obj
          (CechNerve (bcCover f g f' g' h 𝒰) ((Scheme.Modules.pullback g').obj F))).δ k
      = (Scheme.Modules.pullback g').map
            ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ k) ≫
          (twistedComponent f g f' g' h 𝒰 F hF (n + 1)).hom := by
  -- STEP 0.  Replace BOTH nerve cofaces by their geometric backbone form.  Everything below then
  -- lives in the geometric spelling: inside a σ-projection composite the
  -- `CosimplicialObject C` / `SimplexCategory ⥤ C` boundary makes `rw` report a motive failure
  -- (the trap `cechNerve_drop_δ_sigma`'s docstring records).
  rw [cechNerve_drop_δ 𝒰 F k, cechNerve_drop_δ (bcCover f g f' g' h 𝒰)
    ((Scheme.Modules.pullback g').obj F) k]
  -- Everything else is `sigmaAssembled_δ_square_cancel`, whose target data is abstract.  The only
  -- input is `hlift`: the target coface, read through the base-changed cover's own
  -- σ-decomposition, is reindex-then-restrict — the σ-coordinate coface formula AT THE
  -- BASE-CHANGED COVER, the same lemma at the other cover.  This is the step r4 left unwritten,
  -- and it needs no transport: `𝒰'.I₀` is `𝒰.I₀` on the nose (`baseChangedCover_I₀`).
  refine sigmaAssembled_δ_square_cancel g' 𝒰 F n k _ _
    (twistedPerSigmaTarget f g f' g' h 𝒰 F hF n)
    (twistedPerSigmaTarget f g f' g' h 𝒰 F hF (n + 1))
    (pushPull_sigma_iso (bcCover f g f' g' h 𝒰) ((Scheme.Modules.pullback g').obj F) n)
    (pushPull_sigma_iso (bcCover f g f' g' h 𝒰) ((Scheme.Modules.pullback g').obj F) (n + 1))
    _ _ (hcompat n k) ?_
  refine (Limits.Pi.hom_ext _ _ (fun σ' => ?_)).symm
  rw [Category.assoc, Limits.Pi.lift_π, Category.assoc]
  exact cechNerve_backbone_δ_sigma (bcCover f g f' g' h 𝒰)
    ((Scheme.Modules.pullback g').obj F) n k σ'

set_option maxHeartbeats 1600000 in
-- Elaborating this application unfolds `twistedComponent` at two adjacent degrees, so both
-- four-factor Beck-Chevalley composites over an intersection open are forced in one goal, and the
-- σ-product instances (finite products over `Fin (n+1) → 𝒰.I₀`) are re-synthesised per degree.
set_option synthInstance.maxHeartbeats 800000 in
/-- **THE WIRING, CONSUMED — the twisted leaf as an actual isomorphism of complexes, modulo one
hypothesis.**  `alternatingCofaceComplexIsoOfDelta` fed the degreewise family `twistedComponent`
together with the coface square `twistedComponent_δ_square`.

**This declaration is why "item (i) is closed" is a claim about Lean and not about prose.**  A
degreewise family plus a proved square is not yet progress: what matters is whether the *consumer*
accepts them, and this workspace has repeatedly shipped interfaces nothing could consume.  Here the
consumer is applied, so the composition typechecks and the wiring is exercised rather than asserted.

Note what the hypothesis is: `TwistedPerSigmaDeltaCompat`, i.e. half (a) and nothing else.  So the
distance from here to Stacks 02KG/02KH's twisted half is exactly one named `Prop` — see
`BcSquareNaturality` and its two equivalent restatements below.

This does *not* by itself discharge `twisted_cech_nerve_iso`: that declaration is built with
`NatIso.ofComponents` and produces a full *cosimplicial* isomorphism, whereas this produces the
isomorphism of alternating-coface complexes that every consumer downstream actually reads
(`cechComplex_baseChange_iso_of_cosimplicialIso` bottoms out at `alternatingCofaceMapComplex`).
Rewiring the endpoint chain onto this is the next mechanical step and is not done here.
Project-local. -/
noncomputable def twistedCechComplexIsoOfCompat
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    [IsSeparated f] [IsAffine S] [∀ i, IsAffine (𝒰.X i)]
    [Finite (bcCover f g f' g' h 𝒰).I₀]
    (F : X.Modules) (hF : F.IsQuasicoherent)
    (hcompat : TwistedPerSigmaDeltaCompat f g f' g' h 𝒰 F hF) :
    (AlgebraicTopology.alternatingCofaceMapComplex X'.Modules).obj
        (((CosimplicialObject.whiskering X.Modules X'.Modules).obj
          (Scheme.Modules.pullback g')).obj
          (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)))
      ≅ (AlgebraicTopology.alternatingCofaceMapComplex X'.Modules).obj
          (CosimplicialObject.Augmented.drop.obj
            (CechNerve (bcCover f g f' g' h 𝒰) ((Scheme.Modules.pullback g').obj F))) :=
  alternatingCofaceComplexIsoOfDelta _ _
    (fun n => twistedComponent f g f' g' h 𝒰 F hF n)
    (fun n k => twistedComponent_δ_square f g f' g' h 𝒰 F hF hcompat n k)

/-- In a slice category over `T`, if the target's structure map is a mono then any two slice
morphisms with the same source and target are equal. -/
theorem over_hom_ext_of_mono {C : Type*} [Category C] {T : C} {A B : Over T}
    [Mono B.hom] (a b : A ⟶ B) : a = b := by
  ext
  exact (cancel_mono B.hom).mp (by rw [Over.w, Over.w])

/-- The base change along `g'` of the inclusion of intersection opens `U_σ ⊆ U_{σ∘α}`,
as a morphism of the slice `Over X'` between the two `pullback.fst` legs. -/
noncomputable def wmap (g' : X' ⟶ X) (𝒰 : X.OpenCover) {κ κ' : Type} (α : κ' → κ)
    (σ : κ → 𝒰.I₀) :
    Over.mk (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))) ⟶
      Over.mk (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 (σ ∘ α)))) :=
  Over.homMk
    (pullback.lift (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)) ≫
        X.homOfLE (coverInterOpen_comp_le 𝒰 α σ))
      (by rw [Category.assoc, Scheme.homOfLE_ι]; exact pullback.condition))
    (pullback.lift_fst _ _ _)

/-- `X` is separated over the terminal scheme, from `[IsSeparated f]` and `[IsAffine S]`. -/
theorem hsepX_of (f : X ⟶ S) [IsSeparated f] [IsAffine S] : IsSeparated (terminal.from X) := by
  rw [← terminal.comp_from f]
  exact IsSeparated.comp_iff.mpr ‹IsSeparated f›

/-- The `pullback.fst` leg of the restricted square is an open immersion. -/
theorem instFstOI (g' : X' ⟶ X) (𝒰 : X.OpenCover) {κ : Type} (σ : κ → 𝒰.I₀) :
    IsOpenImmersion (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))) :=
  isOpenImmersion_of_isPullback_left g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))
    (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
    (pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
    (restrictedCartesianAffinePushout g' 𝒰 σ)

/-- The range equality feeding `isoOfRangeEq` in `twisted_cech_nerve_per_sigma`. -/
theorem hre_of (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) {κ : Type} [Finite κ] (σ : κ → 𝒰.I₀) :
    Set.range (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      = Set.range (Scheme.Opens.ι (coverInterOpen
          ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom) σ)) := by
  rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι,
    coverInterOpen_baseChange_eq f g f' g' h 𝒰 σ, Scheme.Opens.opensRange_ι]

/-- The `isoOfRangeEq` slice transport used inside `twisted_cech_nerve_per_sigma`. -/
noncomputable def eIso (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) {κ : Type} [Finite κ] (σ : κ → 𝒰.I₀) :
    Over.mk (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))) ≅
      Over.mk (Scheme.Opens.ι (coverInterOpen
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom) σ)) :=
  Over.isoMk
    (@IsOpenImmersion.isoOfRangeEq _ _ _
      (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (Scheme.Opens.ι (coverInterOpen
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom) σ))
      (instFstOI g' 𝒰 σ) (Scheme.Opens.instIsOpenImmersionι _) (hre_of f g f' g' h 𝒰 σ))
    (@IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
      (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (Scheme.Opens.ι (coverInterOpen
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom) σ))
      (instFstOI g' 𝒰 σ) (Scheme.Opens.instIsOpenImmersionι _) (hre_of f g f' g' h 𝒰 σ))

/-- The Beck-Chevalley iso for the square restricted over `U_σ`, before the slice transport. -/
noncomputable def bcv (f : X ⟶ S) (g' : X' ⟶ X) (𝒰 : X.OpenCover) [IsSeparated f] [IsAffine S]
    [∀ i, IsAffine (𝒰.X i)] (F : X.Modules) (hF : F.IsQuasicoherent)
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    (Scheme.Modules.pullback g').obj
        (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) ≅
      pushPullObj ((Scheme.Modules.pullback g').obj F)
        (Over.mk (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) :=
  haveI := hsepX_of f
  openImmersion_beckChevalley g' (coverInterOpen_isAffine f 𝒰 σ)
    (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
    (pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
    (restrictedCartesianAffinePushout g' 𝒰 σ) F hF

set_option maxHeartbeats 1600000 in
-- The `rfl` compares two four-factor Beck-Chevalley composites over an intersection open, so
-- whnf must unfold `openImmersion_beckChevalley` and both `isoOfRangeEq` transports.
set_option synthInstance.maxHeartbeats 800000 in
/-- `twisted_cech_nerve_per_sigma` is `bcv` followed by the `eIso` slice transport -- by `rfl`. -/
theorem tcnps_eq (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [IsSeparated f] [IsAffine S]
    [∀ i, IsAffine (𝒰.X i)] (F : X.Modules) (hF : F.IsQuasicoherent)
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    twisted_cech_nerve_per_sigma f g f' g' h 𝒰 F hF σ
      = bcv f g' 𝒰 F hF σ ≪≫
          pushPullObjCongr ((Scheme.Modules.pullback g').obj F) (eIso f g f' g' h 𝒰 σ) :=
  rfl

/-! ### (b) The `isoOfRangeEq` slice transports commute with the inclusions -- FREE by mono-ext -/

set_option maxHeartbeats 1600000 in
-- Mono-cancellation in `Over X'` at the base-changed intersection open re-runs the same
-- open-immersion and finite-intersection instance searches as `coverInterOpen_isAffine`.
set_option synthInstance.maxHeartbeats 800000 in
/-- **Half (b).** The two ways of going from the base-changed intersection open `U'_{σ'}` to the
pullback leg over `U_{σ'∘δᵏ}` agree: transport by `isoOfRangeEq` after including, or include after
transporting.  Both are slice maps into an object whose structure map is an open immersion, hence a
mono, so they are equal with no computation. -/
theorem slice_compat (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) {p : ℕ} (k : Fin (p + 2))
    (σ' : Fin (p + 2) → 𝒰.I₀) :
    interLegHom ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
          σ' k ≫
        (eIso f g f' g' h 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom)).inv
      = (eIso f g f' g' h 𝒰 σ').inv ≫ wmap g' 𝒰 (SimplexCategory.δ k).toOrderHom σ' := by
  haveI : Mono (Over.mk (pullback.fst g' (Scheme.Opens.ι
      (coverInterOpen 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom))))).hom :=
    @IsOpenImmersion.mono _ _ _ (instFstOI g' 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom))
  exact over_hom_ext_of_mono _ _

/-! ### The reduction: the whole obligation follows from half (a) -/

set_option maxHeartbeats 1600000 in
-- Chains the two `tcnps_eq` unfoldings against the slice-compatibility rewrite, so both
-- four-factor composites are elaborated in one goal.
set_option synthInstance.maxHeartbeats 800000 in
/-- **THE REDUCTION.**  `TwistedPerSigmaDeltaCompat` follows from `hBC`: the naturality of the
restricted-square Beck-Chevalley iso `bcv` with respect to the morphism of cartesian squares
induced by the intersection-open inclusion `U_{σ'} ⊆ U_{σ'∘δᵏ}`.  Everything else -- the two
`isoOfRangeEq` slice transports and the index bookkeeping -- is discharged here. -/
theorem twistedPerSigmaCompat_of_bcNaturality
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [IsSeparated f] [IsAffine S]
    [∀ i, IsAffine (𝒰.X i)] (F : X.Modules) (hF : F.IsQuasicoherent)
    (hBC : ∀ (p : ℕ) (k : Fin (p + 2)) (σ' : Fin (p + 2) → 𝒰.I₀),
      (bcv f g' 𝒰 F hF (σ' ∘ (SimplexCategory.δ k).toOrderHom)).hom ≫
          pushPullMap ((Scheme.Modules.pullback g').obj F)
            (wmap g' 𝒰 (SimplexCategory.δ k).toOrderHom σ')
        = (Scheme.Modules.pullback g').map (pushPullMap F (interLegHom 𝒰 σ' k)) ≫
            (bcv f g' 𝒰 F hF σ').hom) :
    TwistedPerSigmaDeltaCompat f g f' g' h 𝒰 F hF := by
  intro p k σ'
  rw [tcnps_eq f g f' g' h 𝒰 F hF, tcnps_eq f g f' g' h 𝒰 F hF, Iso.trans_hom, Iso.trans_hom,
    Category.assoc]
  change _ ≫ pushPullMap _ (eIso f g f' g' h 𝒰 _).inv ≫ _
      = _ ≫ _ ≫ pushPullMap _ (eIso f g f' g' h 𝒰 σ').inv
  have e1 := congrArg (pushPullMap ((Scheme.Modules.pullback g').obj F))
    (slice_compat f g f' g' h 𝒰 k σ')
  rw [← pushPullMap_comp]
  refine Eq.trans (congrArg (fun m =>
    (bcv f g' 𝒰 F hF (σ' ∘ (SimplexCategory.δ k).toOrderHom)).hom ≫ m) e1) ?_
  rw [pushPullMap_comp, ← Category.assoc, hBC p k σ', Category.assoc]

/-- The `w`-only variant of `openImmersion_bareBC`: cartesianness is never used in its body. -/
noncomputable def bareBC_of_w {V V' : Scheme.{u}} (g' : X' ⟶ X) (p : V ⟶ X) (p' : V' ⟶ X')
    (gV : V' ⟶ V) (hw : gV ≫ p = p' ≫ g') :
    Scheme.Modules.pushforward p ⋙ Scheme.Modules.pullback g' ⟶
      Scheme.Modules.pullback gV ⋙ Scheme.Modules.pushforward p' :=
  CategoryTheory.mateEquiv
    (Scheme.Modules.pullbackPushforwardAdjunction p)
    (Scheme.Modules.pullbackPushforwardAdjunction p')
    (((Scheme.Modules.pullbackComp p' g') ≪≫
      Scheme.Modules.pullbackCongr hw.symm ≪≫
      (Scheme.Modules.pullbackComp gV p).symm).hom)

/-- `openImmersion_bareBC` IS `bareBC_of_w` at `hsq.w` -- by `rfl`. -/
theorem bareBC_eq_of_w {V V' : Scheme.{u}} (g' : X' ⟶ X) (p : V ⟶ X) (p' : V' ⟶ X')
    (gV : V' ⟶ V) (hsq : IsPullback gV p' p g') :
    openImmersion_bareBC g' p p' gV hsq = bareBC_of_w g' p p' gV hsq.w :=
  rfl

/-- **A right adjoint reflects equality of maps into its image.**  For `adj : L ⊣ R`, two morphisms
`a b : M ⟶ R.obj Z` are equal as soon as `L.map a = L.map b`.

This is the cancellation half (a) needs, and it is why half (a) needs no "generator" on the source:
**both** sides of the compatibility land in `pV_* (…)` — a pushforward — so comparing their
`pV^*`-images suffices.  Pure adjunction theory: `L.map a` determines
`(homEquiv).symm a = L.map a ≫ counit`, and `homEquiv` is a bijection.  Project-local. -/
theorem eq_of_map_eq_of_adjunction {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {M : C} {Z : D} (a b : M ⟶ R.obj Z) (hab : L.map a = L.map b) : a = b :=
  (adj.homEquiv M Z).symm.injective (by
    simp only [Adjunction.homEquiv_counit, hab])

/-- **The counit form of the same cancellation, and the one that is actually usable.**
`a = b` as soon as `L.map a ≫ counit = L.map b ≫ counit`.

Weaker hypothesis than `eq_of_map_eq_of_adjunction` (it is that lemma's hypothesis post-composed
with the counit), and strictly more useful here: mathlib's mate API computes **exactly** this
composite.  `CategoryTheory.mateEquiv_counit` reads

    L₂.map ((mateEquiv adj₁ adj₂ α).app d) ≫ adj₂.counit.app _
      = α.app _ ≫ H.map (adj₁.counit.app d)

i.e. it evaluates `L.map (mate) ≫ counit` and *removes the mate*, replacing it by the 2-cell `α` it
came from.  So this is the cancellation that turns a statement about mates into one about the
pullback pseudofunctor's own coherence — see `BcSquareCounitSide`.  Project-local. -/
theorem eq_of_map_comp_counit_eq {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {M : C} {Z : D} (a b : M ⟶ R.obj Z)
    (hab : L.map a ≫ adj.counit.app Z = L.map b ≫ adj.counit.app Z) : a = b :=
  (adj.homEquiv M Z).symm.injective (by
    simp only [Adjunction.homEquiv_counit]; exact hab)

/-! ### HALF (a), NAMED — and reduced to a statement with no pushforward on the target

Half (a) has been described in prose in this file since r4 and passed around as an unnamed
hypothesis `hBC` of `twistedPerSigmaCompat_of_bcNaturality`.  Naming it is not cosmetic: an
obligation that exists only as a binder cannot be cited, measured by a probe, or reduced.
`BcSquareNaturality` below is that binder, verbatim, as a `Prop`.

Two restatements follow, each cancelling more.  Both sides of the equation land in
`pushPullObj (g'^*F) (Over.mk pV) = pV_* pV^*(g'^*F)`, the image of a right adjoint, so the
`pushforward pV` can be dropped:

* `BcSquarePullbackSide` compares the two composites after applying `pV^*`
  (`eq_of_map_eq_of_adjunction`).  No `pushforward` occurs in it.
* `BcSquareCounitSide` compares them after `pV^*` **and** post-composition with the `pV`-counit
  (`eq_of_map_comp_counit_eq`).  This is the weakest as a hypothesis and **the one to prove**, for a
  specific reason: `CategoryTheory.mateEquiv_counit` evaluates exactly that composite and
  *eliminates the mate*, replacing it by the 2-cell it was built from.  Since
  `openImmersion_bareBC` is by definition `mateEquiv` of the pullback-pseudofunctor telescope, that
  law converts half (a) from a statement about mates across a change of square — for which the tree
  has nothing — into one about `pullbackComp`/`pullbackCongr`, which it has.

**These are EQUIVALENT restatements, not weakenings, and that is stated up front rather than
discovered later.**  `bcSquareNaturality_iff_pullbackSide` proves both directions (the converse is
`congrArg`), and `bcSquareCounitSide_of_pullbackSide` / `bcSquareNaturality_of_counitSide` close the
triangle.  So nothing here reduces the mathematical content of half (a); what changes is the
*vocabulary*, from one with no handle to one the mate API can speak about.

What the tree still lacks, measured at r5 by unfolding `bcv`: both sides of half (a) are
`asIso (openImmersion_bareBC … .app (ι U_σ ^* F))` followed by
`(pushforward (pullback.fst g' (ι U_σ))).mapIso (openImmersion_bc_telescope …).symm`, compared
across the change of σ.  So it is a statement about `openImmersion_bareBC` **and**
`openImmersion_bc_telescope` across a change of square.

The `mateEquiv_vcomp` route recorded below remains the other candidate, and it is genuinely blocked
on the brick "`pushPullMap` is the degenerate-square mate" — measured here as typechecking but not
`rfl` and not closable by `simp`. -/

/-- **HALF (a), the crux of the twisted leaf, as a named `Prop`.**  Naturality of the
restricted-square Beck–Chevalley iso `bcv` in the SQUARE: for the intersection-open inclusion
`U_{σ'} ⊆ U_{σ'∘δᵏ}` and its base change `wmap`, base-change-then-restrict equals
restrict-then-base-change.

This is exactly the hypothesis `hBC` of `twistedPerSigmaCompat_of_bcNaturality`, and by that theorem
plus `twistedComponent_δ_square` it is the ONLY thing between this file and Stacks 02KG/02KH.  It is
*not* `openImmersion_bareBC_app_eq` (naturality in the module) nor `pushPullMap_comp`/`_id` (functor
laws in the slice variable): nothing in the tree relates the mate across a change of square.
Project-local. -/
def BcSquareNaturality (f : X ⟶ S) (g' : X' ⟶ X) (𝒰 : X.OpenCover) [IsSeparated f] [IsAffine S]
    [∀ i, IsAffine (𝒰.X i)] (F : X.Modules) (hF : F.IsQuasicoherent) : Prop :=
  ∀ (p : ℕ) (k : Fin (p + 2)) (σ' : Fin (p + 2) → 𝒰.I₀),
    (bcv f g' 𝒰 F hF (σ' ∘ (SimplexCategory.δ k).toOrderHom)).hom ≫
        pushPullMap ((Scheme.Modules.pullback g').obj F)
          (wmap g' 𝒰 (SimplexCategory.δ k).toOrderHom σ')
      = (Scheme.Modules.pullback g').map (pushPullMap F (interLegHom 𝒰 σ' k)) ≫
          (bcv f g' 𝒰 F hF σ').hom

/-- **Half (a) with the target pushforward cancelled.**  The same two composites, compared after
applying `pV^*` where `pV = pullback.fst g' (ι U_{σ'})` is the target's structure map.  No
`pushforward pV` occurs, so this is an equation between maps of *pullbacks* — pseudofunctor
bookkeeping plus the mate's unit law, not a mate-across-squares statement.  Project-local. -/
def BcSquarePullbackSide (f : X ⟶ S) (g' : X' ⟶ X) (𝒰 : X.OpenCover) [IsSeparated f] [IsAffine S]
    [∀ i, IsAffine (𝒰.X i)] (F : X.Modules) (hF : F.IsQuasicoherent) : Prop :=
  ∀ (p : ℕ) (k : Fin (p + 2)) (σ' : Fin (p + 2) → 𝒰.I₀),
    (Scheme.Modules.pullback
        (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ')))).map
      ((bcv f g' 𝒰 F hF (σ' ∘ (SimplexCategory.δ k).toOrderHom)).hom ≫
        pushPullMap ((Scheme.Modules.pullback g').obj F)
          (wmap g' 𝒰 (SimplexCategory.δ k).toOrderHom σ'))
      = (Scheme.Modules.pullback
          (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ')))).map
        ((Scheme.Modules.pullback g').map (pushPullMap F (interLegHom 𝒰 σ' k)) ≫
          (bcv f g' 𝒰 F hF σ').hom)

/-- **THE CANCELLATION: half (a) follows from its pullback-side form.**  `pushPullObj` is by
definition `p_* p^* (−)`, so the common target of the two composites is in the image of the right
adjoint `pushforward pV`; `eq_of_map_eq_of_adjunction` then reflects the equality down from
`pV^*`.  Nothing about the mate, the square, or open immersions is used.  Project-local. -/
theorem bcSquareNaturality_of_pullbackSide (f : X ⟶ S) (g' : X' ⟶ X) (𝒰 : X.OpenCover)
    [IsSeparated f] [IsAffine S] [∀ i, IsAffine (𝒰.X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent)
    (hpb : BcSquarePullbackSide f g' 𝒰 F hF) : BcSquareNaturality f g' 𝒰 F hF :=
  fun p k σ' => eq_of_map_eq_of_adjunction
    (Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ')))) _ _ (hpb p k σ')

/-- **Half (a), COUNIT-SIDE — the form mathlib's mate API can actually consume.**  The two
composites' `pV^*`-images, post-composed with the `pV`-counit.

Strictly weaker as a hypothesis than `BcSquarePullbackSide` (it is that, post-composed), and it is
the form to attack, because `CategoryTheory.mateEquiv_counit` **evaluates exactly this composite**:
`L.map (mate.app d) ≫ counit = α.app _ ≫ H.map (counit)`, with the mate *eliminated* in favour of
the 2-cell `α` it was built from.  Since `openImmersion_bareBC` is by definition
`mateEquiv … (pullbackComp ≪≫ pullbackCongr ≪≫ (pullbackComp).symm).hom`, applying that law to both
occurrences turns half (a) from a statement about mates across a change of square into one about the
pullback pseudofunctor's coherence isomorphisms — which the tree does have.  Project-local. -/
def BcSquareCounitSide (f : X ⟶ S) (g' : X' ⟶ X) (𝒰 : X.OpenCover) [IsSeparated f] [IsAffine S]
    [∀ i, IsAffine (𝒰.X i)] (F : X.Modules) (hF : F.IsQuasicoherent) : Prop :=
  ∀ (p : ℕ) (k : Fin (p + 2)) (σ' : Fin (p + 2) → 𝒰.I₀),
    (Scheme.Modules.pullback
          (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ')))).map
        ((bcv f g' 𝒰 F hF (σ' ∘ (SimplexCategory.δ k).toOrderHom)).hom ≫
          pushPullMap ((Scheme.Modules.pullback g').obj F)
            (wmap g' 𝒰 (SimplexCategory.δ k).toOrderHom σ')) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction
        (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ')))).counit.app _
      = (Scheme.Modules.pullback
            (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ')))).map
          ((Scheme.Modules.pullback g').map (pushPullMap F (interLegHom 𝒰 σ' k)) ≫
            (bcv f g' 𝒰 F hF σ').hom) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction
          (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ')))).counit.app _

/-- **Half (a) from its counit-side form** — via `eq_of_map_comp_counit_eq`.  This is the weakest of
the three equivalent forms as a hypothesis, hence the best one to prove.  Project-local. -/
theorem bcSquareNaturality_of_counitSide (f : X ⟶ S) (g' : X' ⟶ X) (𝒰 : X.OpenCover)
    [IsSeparated f] [IsAffine S] [∀ i, IsAffine (𝒰.X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent)
    (hct : BcSquareCounitSide f g' 𝒰 F hF) : BcSquareNaturality f g' 𝒰 F hF :=
  fun p k σ' => eq_of_map_comp_counit_eq
    (Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ')))) _ _ (hct p k σ')

/-- **The full chain from half (a)'s pullback-side form to `TwistedPerSigmaDeltaCompat`.**
`bcSquareNaturality_of_pullbackSide` then `twistedPerSigmaCompat_of_bcNaturality`.  Stated so the
single remaining obligation of flat base change is citable in one name.  Project-local. -/
theorem twistedPerSigmaCompat_of_pullbackSide (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [IsSeparated f] [IsAffine S]
    [∀ i, IsAffine (𝒰.X i)] (F : X.Modules) (hF : F.IsQuasicoherent)
    (hpb : BcSquarePullbackSide f g' 𝒰 F hF) :
    TwistedPerSigmaDeltaCompat f g f' g' h 𝒰 F hF :=
  twistedPerSigmaCompat_of_bcNaturality f g f' g' h 𝒰 F hF
    (bcSquareNaturality_of_pullbackSide f g' 𝒰 F hF hpb)

/-- **The whole residue from the WEAKEST of the three forms.**  `BcSquareCounitSide` is what a
future session should aim at: it is implied by each of the other two, and it is the one
`mateEquiv_counit` speaks about.  Project-local. -/
theorem twistedPerSigmaCompat_of_counitSide (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [IsSeparated f] [IsAffine S]
    [∀ i, IsAffine (𝒰.X i)] (F : X.Modules) (hF : F.IsQuasicoherent)
    (hct : BcSquareCounitSide f g' 𝒰 F hF) :
    TwistedPerSigmaDeltaCompat f g f' g' h 𝒰 F hF :=
  twistedPerSigmaCompat_of_bcNaturality f g f' g' h 𝒰 F hF
    (bcSquareNaturality_of_counitSide f g' 𝒰 F hF hct)

/-- The counit-side form follows from the pullback-side one by post-composing with the counit.  With
`bcSquareNaturality_of_counitSide` and the equivalence below, all three forms of half (a) are
interderivable — so `BcSquareCounitSide`, the weakest as a hypothesis, is the one to prove. -/
theorem bcSquareCounitSide_of_pullbackSide (f : X ⟶ S) (g' : X' ⟶ X) (𝒰 : X.OpenCover)
    [IsSeparated f] [IsAffine S] [∀ i, IsAffine (𝒰.X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent)
    (hpb : BcSquarePullbackSide f g' 𝒰 F hF) : BcSquareCounitSide f g' 𝒰 F hF :=
  fun p k σ' => congrArg (fun m => m ≫ (Scheme.Modules.pullbackPushforwardAdjunction
    (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ')))).counit.app _) (hpb p k σ')

/-- **THE CONVERSE — so the two forms are EQUIVALENT, and this is a restatement, not a weakening.**
Trivially `congrArg`, and stated for a reason this workspace has been bitten by: a "reduction" whose
converse fails may have thrown away what made the statement true, and one whose converse holds is
honestly a *change of vocabulary*.  This one is the latter.

What the change buys is nonetheless real: `BcSquarePullbackSide` mentions no `pushforward`, so it is
attackable by the pullback pseudofunctor's own coherence (`pullbackComp`, `pullbackCongr`) plus the
mate's unit law `unit_mateEquiv`, whereas `BcSquareNaturality` had a `p_*` around everything and no
handle at all.  Project-local. -/
theorem bcSquarePullbackSide_of_naturality (f : X ⟶ S) (g' : X' ⟶ X) (𝒰 : X.OpenCover)
    [IsSeparated f] [IsAffine S] [∀ i, IsAffine (𝒰.X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent)
    (hbc : BcSquareNaturality f g' 𝒰 F hF) : BcSquarePullbackSide f g' 𝒰 F hF :=
  fun p k σ' => congrArg (Scheme.Modules.pullback
    (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ')))).map (hbc p k σ')

/-- The two forms of half (a) are equivalent (`bcSquareNaturality_of_pullbackSide` and its
converse).  Recorded as one statement so a reader cannot take the reduction for a weakening. -/
theorem bcSquareNaturality_iff_pullbackSide (f : X ⟶ S) (g' : X' ⟶ X) (𝒰 : X.OpenCover)
    [IsSeparated f] [IsAffine S] [∀ i, IsAffine (𝒰.X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    BcSquareNaturality f g' 𝒰 F hF ↔ BcSquarePullbackSide f g' 𝒰 F hF :=
  ⟨bcSquarePullbackSide_of_naturality f g' 𝒰 F hF,
   bcSquareNaturality_of_pullbackSide f g' 𝒰 F hF⟩

/-- **THE MATE IS ELIMINABLE: `openImmersion_bareBC` under `p'^*` and past the counit IS the
pullback telescope.**  For any cartesian square,
```
  p'^*(bareBC.app c) ≫ counit_{p'} = telescope.app (p_* c) ≫ gV^*(counit_p.app c),
```
where `telescope = (pullbackComp p' g') ≪≫ pullbackCongr ≪≫ (pullbackComp gV p).symm` is the
pseudofunctor 2-cell `openImmersion_bareBC` was defined as the mate of.

**This is the brick half (a) was missing, and it costs one `rw` plus mathlib's
`CategoryTheory.mateEquiv_counit`** — measured, not conjectured.  Its significance: the right-hand
side contains **no mate at all**.  Everything in it is either a pullback-pseudofunctor coherence
isomorphism (`pullbackComp`, `pullbackCongr`) or a counit of a *single* adjunction, and this tree
has lemmas about both.  So in `BcSquareCounitSide` — half (a) read under `pV^*` and past the
counit — both occurrences of the Beck–Chevalley mate can be replaced by telescopes, turning
"naturality of the mate across a change of square", for which nothing exists here or in mathlib,
into a pseudofunctor coherence statement.

Note what this does *not* use: no open immersion, no flatness, no quasi-coherence, and (per
`bareBC_eq_of_w`) not even cartesianness — `mateEquiv_counit` is a general fact about mates.  The
`IsPullback` binder is carried only to match `openImmersion_bareBC`'s signature.

The previously recorded route needed the brick "`pushPullMap` is the degenerate-square mate", which
was measured to typecheck but not be `rfl`.  That brick is still unproved and is still the blocker
for the `mateEquiv_vcomp` route; this one sidesteps it.

**HOW FAR IT GETS, MEASURED — and it is not all the way, said here rather than left to be
discovered.**  Applied to `BcSquareCounitSide` after unfolding `bcv`, this lemma fires on the
**right-hand side only**.  There the mate and the counit are at the *same* σ', so the pattern
matches.  On the left-hand side the mate is at `σ' ∘ δᵏ` while the counit is at `σ'`, with a
telescope inverse and `pushPullMap (wmap …)` sitting between them — so `rw` does not fire (measured:
"did not find an occurrence", with the counit's argument visibly at the other index).

So half (a) is **not** a one-rewrite consequence of the mate law, and the residue is now sharply
located: getting the LHS counit adjacent to its mate, i.e. commuting `pushPullMap (wmap …)` and the
telescope past the counit.

**And that step is NOT plain counit naturality — checked, so the next session does not start by
trying it.**  `Adjunction.counit_naturality` for `pV^* ⊣ pV_*` reads
`pV^*(pV_*(ψ)) ≫ counit = counit ≫ ψ` for `ψ` between objects of `V'.Modules`, i.e. it moves past
the counit only maps that are already `pV_*` of something.  Here the map to be moved is
`pushPullMap (g'^*F) (wmap …) : pushPullObj (g'^*F) (Over.mk pV_{σ'∘δᵏ}) ⟶ pushPullObj (g'^*F)
(Over.mk pV_{σ'})`, whose **source is a pushforward along a different morphism** — so it is not of
that form and the lemma does not apply.

That is the honest frontier: a comparison of the counits of two *different* adjunctions along the
slice map `wmap`.  Still a smaller and better-located obligation than "the mate across a change of
square" — the mate is gone from it — but it is not free, and this note is here so it is not
mispriced in either direction.  Project-local. -/
theorem bareBC_pullback_counit {V V' : Scheme.{u}}
    (g' : X' ⟶ X) (p : V ⟶ X) (p' : V' ⟶ X') (gV : V' ⟶ V)
    (hsq : IsPullback gV p' p g') (c : V.Modules) :
    (Scheme.Modules.pullback p').map ((openImmersion_bareBC g' p p' gV hsq).app c) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction p').counit.app _
      = (((pullbackComp p' g') ≪≫ pullbackCongr hsq.w.symm ≪≫
            (pullbackComp gV p).symm).hom).app ((pushforward p).obj c) ≫
          (Scheme.Modules.pullback gV).map
            ((Scheme.Modules.pullbackPushforwardAdjunction p).counit.app c) := by
  rw [openImmersion_bareBC]
  exact CategoryTheory.mateEquiv_counit _ _ _ c

/-! (2) THE PASTE STRUCTURE -- an alternative route to half (a), NOT the one taken.

MEASURED NEGATIVE: the statement

  (pullbackId X).inv.app (pushPullObj F Y₁)
    ≫ (bareBC_of_w (𝟙 X) Y₁.hom Y₂.hom u.left _).app ((pullback Y₁.hom).obj F)
    ≫ (pushforward Y₂.hom).map ((pullbackComp u.left Y₁.hom).hom.app F
        ≫ (pullbackCongr (Over.w u)).hom.app F)
      = pushPullMap F u

typechecks but is NOT `rfl`, and `simp [bareBC_of_w, pushPullMap, rawPushPullMap, mateEquiv_apply]`
does not close it (`aesop_cat` times out at whnf).  So "`pushPullMap` is a degenerate-square mate"
is a real lemma, not a definitional unfolding. -/

/-- **The inclusion square commutes.**  `V' ⟶ W'` over `V₀ ⟶ W₀`: this is the square that pastes
onto the `W₀`-square to give the `V₀`-square, so `mateEquiv_vcomp` is the applicable glue.
Proved by cancelling the mono `W₀.ι`. -/
theorem inclusion_square_comm {V' W' : Scheme.{u}} (g' : X' ⟶ X)
    {V₀ W₀ : X.Opens} (hle : V₀ ≤ W₀)
    (pV : V' ⟶ X') (gV : V' ⟶ ↑V₀) (hsqV : IsPullback gV pV V₀.ι g')
    (pW : W' ⟶ X') (gW : W' ⟶ ↑W₀) (hsqW : IsPullback gW pW W₀.ι g')
    (w : Over.mk pV ⟶ Over.mk pW) :
    gV ≫ X.homOfLE hle = w.left ≫ gW := by
  have hmono : Mono W₀.ι := inferInstance
  have hwl : (w.left : V' ⟶ W') ≫ pW = pV := Over.w w
  refine (cancel_mono W₀.ι).mp ?_
  calc (gV ≫ X.homOfLE hle) ≫ W₀.ι
      = gV ≫ (X.homOfLE hle ≫ W₀.ι) := Category.assoc _ _ _
    _ = gV ≫ V₀.ι := by rw [Scheme.homOfLE_ι]
    _ = pV ≫ g' := hsqV.w
    _ = ((w.left : V' ⟶ W') ≫ pW) ≫ g' := congrArg (fun m => m ≫ g') hwl.symm
    _ = (w.left : V' ⟶ W') ≫ (pW ≫ g') := Category.assoc _ _ _
    _ = (w.left : V' ⟶ W') ≫ (gW ≫ W₀.ι) :=
        congrArg (fun m => (w.left : V' ⟶ W') ≫ m) hsqW.w.symm
    _ = ((w.left : V' ⟶ W') ≫ gW) ≫ W₀.ι := (Category.assoc _ _ _).symm

/-! ### THE SECOND MATE IS ELIMINABLE TOO: the adjunct of `pushPullMap` (run 0068 r6)

`bareBC_pullback_counit` above removed the Beck–Chevalley mate from half (a) by putting it under
the left adjoint and past the counit.  It fired on **one side only**, and the recorded reason was
precise: on the other side the mate sits at `σ' ∘ δᵏ` while the counit sits at `σ'`, separated by
`pushPullMap (wmap …)`.  So what was missing was not a fact about the mate at all, but the
**adjunct of `pushPullMap` itself** — the same "put it under `p^*` and past the counit" move
applied to the restriction map instead of to the mate.

`rawPushPullMap_pullback_counit_self` below is that lemma, and it has the same character as
`bareBC_pullback_counit`: the *unit* that `rawPushPullMap` is built from **disappears**, leaving
pullback-pseudofunctor coherence (`pullbackComp`) plus a single ordinary counit.  So both
occurrences in `BcSquareCounitSide` can now be evaluated, not merely rewritten past each other.

Two notes recorded because they cost this round's time, and neither is mathematics:

* `pushforward (a ≫ p₁)` and `pushforward a ⋙ pushforward p₁` are `rfl`-equal but differently
  *spelled*, and after `counit_comp_decomp` fires the goal is not type-correct at `instances`
  transparency.  Plain `rw` then reports "did not find an occurrence" **and** an application type
  mismatch naming exactly those two spellings — a spelling failure wearing a broken-goal costume.
  `set_option backward.isDefEq.respectTransparency false` (as `pushPullMap_id` already does in
  `CechHigherDirectImage.lean`) plus stating each naturality square as a `have` in the goal's own
  spelling is what makes it go through; `erw`, `simp only [Functor.comp_obj]` and `set` do not.
* Generalising the head to an arbitrary `v` is load-bearing, not cosmetic: with `v` a variable
  every square can be supplied in term mode (`.inv.naturality _`, `.counit_naturality v`,
  `.left_triangle_components _`), so no rewrite has to unify across the two spellings.

Project-local.  Both declarations are axiom-clean. -/

/-- **The composite counit factors through the pullback telescope.**  For `a ≫ p₁`, the counit of
`pullback (a ≫ p₁) ⊣ pushforward (a ≫ p₁)` equals `pullbackComp`-inverse followed by the two
single-morphism counits.  This is mathlib's `conjugateEquiv_counit` at the composed adjunction,
transported along `conjugateEquiv_pullbackComp_inv` (and using that `pushforwardComp` is the
identity on the nose, `pushforwardComp_hom_app_id`).  Project-local. -/
theorem counit_comp_decomp {Z₁ Z₂ : Scheme.{u}} (a : Z₂ ⟶ Z₁) (p₁ : Z₁ ⟶ X)
    (d : Z₂.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ p₁)).counit.app d
      = (Scheme.Modules.pullbackComp a p₁).inv.app
            ((Scheme.Modules.pushforward a ⋙ Scheme.Modules.pushforward p₁).obj d) ≫
          (Scheme.Modules.pullback a).map
            ((Scheme.Modules.pullbackPushforwardAdjunction p₁).counit.app
              ((Scheme.Modules.pushforward a).obj d)) ≫
          (Scheme.Modules.pullbackPushforwardAdjunction a).counit.app d := by
  have h := CategoryTheory.conjugateEquiv_counit
    ((Scheme.Modules.pullbackPushforwardAdjunction p₁).comp
      (Scheme.Modules.pullbackPushforwardAdjunction a))
    (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ p₁))
    (Scheme.Modules.pullbackComp a p₁).inv d
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, pushforwardComp_hom_app_id,
    Adjunction.comp_counit_app] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- **THE ADJUNCT OF `pushPullMap`: under `p^*` and past the counit, its unit disappears.**
The exact analogue for the restriction map `rawPushPullMap` of what `bareBC_pullback_counit` is for
the Beck–Chevalley mate, and the brick half (a) was actually missing.

`rawPushPullMap` is built from the `a`-unit (see `rawPushPullMap_self`).  Read under
`(a ≫ p₁)^*` and post-composed with the `(a ≫ p₁)`-counit, that unit is cancelled by the left
triangle identity, and what remains mentions **no unit and no mate**: only the pullback
pseudofunctor's coherence iso `pullbackComp` and a single `p₁`-counit.

Why this is the missing piece rather than one more restatement: `BcSquareCounitSide`'s left-hand
side has the mate at `σ' ∘ δᵏ` and the counit at `σ'`, with `pushPullMap (wmap …)` in between, which
is exactly why `bareBC_pullback_counit` fired on the right-hand side only.  Evaluating the
restriction map's own adjunct is what lets the two be brought together, and it is not
`Adjunction.counit_naturality` (that moves only maps already of the form `p_*ψ` past the counit; a
`pushPullMap` has a pushforward along a *different* morphism as its source).

No flatness, no quasi-coherence, no open immersion, no cartesian square: this is adjunction and
pseudofunctor bookkeeping.  Project-local. -/
theorem rawPushPullMap_pullback_counit_self {Z₁ Z₂ : Scheme.{u}} (a : Z₂ ⟶ Z₁) (p₁ : Z₁ ⟶ X)
    (F : X.Modules) :
    (Scheme.Modules.pullback (a ≫ p₁)).map (rawPushPullMap a p₁ (a ≫ p₁) rfl F) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ p₁)).counit.app
          ((Scheme.Modules.pullback (a ≫ p₁)).obj F)
      = (Scheme.Modules.pullbackComp a p₁).inv.app
            ((Scheme.Modules.pushforward p₁).obj ((Scheme.Modules.pullback p₁).obj F)) ≫
          (Scheme.Modules.pullback a).map
            ((Scheme.Modules.pullbackPushforwardAdjunction p₁).counit.app
              ((Scheme.Modules.pullback p₁).obj F)) ≫
          (Scheme.Modules.pullbackComp a p₁).hom.app F := by
  -- Generic head `v`: stating the step for an arbitrary `v` keeps every type in the
  -- `pushforward p₁ ∘ pushforward a` spelling, so the naturality squares can be supplied
  -- in term mode and no rewrite has to unify across the two spellings of `pushforward (a ≫ p₁)`.
  have key : ∀ v : (Scheme.Modules.pullback p₁).obj F ⟶
        (Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback (a ≫ p₁)).obj F),
      (Scheme.Modules.pullback (a ≫ p₁)).map ((Scheme.Modules.pushforward p₁).map v) ≫
          (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ p₁)).counit.app
            ((Scheme.Modules.pullback (a ≫ p₁)).obj F)
        = (Scheme.Modules.pullbackComp a p₁).inv.app
              ((Scheme.Modules.pushforward p₁).obj ((Scheme.Modules.pullback p₁).obj F)) ≫
            (Scheme.Modules.pullback a).map
              ((Scheme.Modules.pullbackPushforwardAdjunction p₁).counit.app
                ((Scheme.Modules.pullback p₁).obj F)) ≫
            (Scheme.Modules.pullback a).map v ≫
              (Scheme.Modules.pullbackPushforwardAdjunction a).counit.app
                ((Scheme.Modules.pullback (a ≫ p₁)).obj F) := by
    intro v
    rw [counit_comp_decomp]
    -- naturality of the telescope inverse, written in the spelling the goal uses
    have hnat : (Scheme.Modules.pullback (a ≫ p₁)).map
            ((Scheme.Modules.pushforward p₁).map v) ≫
          (Scheme.Modules.pullbackComp a p₁).inv.app
            ((Scheme.Modules.pushforward a ⋙ Scheme.Modules.pushforward p₁).obj
              ((Scheme.Modules.pullback (a ≫ p₁)).obj F))
        = (Scheme.Modules.pullbackComp a p₁).inv.app
              ((Scheme.Modules.pushforward p₁).obj ((Scheme.Modules.pullback p₁).obj F)) ≫
            (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback p₁).map
              ((Scheme.Modules.pushforward p₁).map v)) :=
      (Scheme.Modules.pullbackComp a p₁).inv.naturality _
    -- counit naturality for `p₁`, again in the goal's spelling
    have hc1 : (Scheme.Modules.pullback p₁).map ((Scheme.Modules.pushforward p₁).map v) ≫
          (Scheme.Modules.pullbackPushforwardAdjunction p₁).counit.app
            ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback (a ≫ p₁)).obj F))
        = (Scheme.Modules.pullbackPushforwardAdjunction p₁).counit.app
            ((Scheme.Modules.pullback p₁).obj F) ≫ v :=
      (Scheme.Modules.pullbackPushforwardAdjunction p₁).counit_naturality v
    rw [← Category.assoc, hnat, Category.assoc]
    slice_lhs 2 3 => rw [← Functor.map_comp]
    rw [hc1, Functor.map_comp, Category.assoc]
  -- instantiate `key` at the actual head of `rawPushPullMap`
  rw [rawPushPullMap_self, key, Functor.map_comp, Category.assoc]
  -- counit naturality for `a`, then the left triangle kills the `a`-unit.
  have hc2 : (Scheme.Modules.pullback a).map ((Scheme.Modules.pushforward a).map
            ((Scheme.Modules.pullbackComp a p₁).hom.app F)) ≫
          (Scheme.Modules.pullbackPushforwardAdjunction a).counit.app
            ((Scheme.Modules.pullback (a ≫ p₁)).obj F)
      = (Scheme.Modules.pullbackPushforwardAdjunction a).counit.app
            ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback p₁).obj F)) ≫
          (Scheme.Modules.pullbackComp a p₁).hom.app F :=
    (Scheme.Modules.pullbackPushforwardAdjunction a).counit_naturality _
  have htri : (Scheme.Modules.pullback a).map
          ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
            ((Scheme.Modules.pullback p₁).obj F)) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction a).counit.app
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback p₁).obj F))
      = 𝟙 ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback p₁).obj F)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction a).left_triangle_components _
  rw [hc2, reassoc_of% htri]

/-- The pullback telescope for a **general** over-triangle `w : a ≫ p₁ = p₂`:
`p₂^* ≅ p₁^* ⋙ a^*`, as `pullbackComp` followed by the `pullbackCongr` transport along `w`.
Project-local. -/
noncomputable def ppTel {Z₁ Z₂ : Scheme.{u}} (a : Z₂ ⟶ Z₁) (p₁ : Z₁ ⟶ X) (p₂ : Z₂ ⟶ X)
    (w : a ≫ p₁ = p₂) :
    Scheme.Modules.pullback p₁ ⋙ Scheme.Modules.pullback a ≅ Scheme.Modules.pullback p₂ :=
  Scheme.Modules.pullbackComp a p₁ ≪≫ Scheme.Modules.pullbackCongr w

/-- **The adjunct of `pushPullMap`, general over-triangle** — and this is the form the twisted
square needs, not the `rfl` one.

Measured, and worth stating because it is the kind of thing that silently blocks a route: the
over-triangle of `wmap` is a **genuine equation, not `rfl`** (probed: `rfl` fails, `Over.w` is
needed).  So `rawPushPullMap_pullback_counit_self` alone does not apply to `BcSquareCounitSide`;
this version, with the triangle as a free hypothesis, does.  The proof is `subst w` onto the
`rfl` case — cheap, because substituting removes the transport before anything is normalised
(the same trick `pushPull_transport_cancel` uses in `CechHigherDirectImage.lean`).

Project-local; axiom-clean. -/
theorem rawPushPullMap_pullback_counit {Z₁ Z₂ : Scheme.{u}} (a : Z₂ ⟶ Z₁) (p₁ : Z₁ ⟶ X)
    (p₂ : Z₂ ⟶ X) (w : a ≫ p₁ = p₂) (F : X.Modules) :
    (Scheme.Modules.pullback p₂).map (rawPushPullMap a p₁ p₂ w F) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction p₂).counit.app
          ((Scheme.Modules.pullback p₂).obj F)
      = (ppTel a p₁ p₂ w).inv.app
            ((Scheme.Modules.pushforward p₁).obj ((Scheme.Modules.pullback p₁).obj F)) ≫
          (Scheme.Modules.pullback a).map
            ((Scheme.Modules.pullbackPushforwardAdjunction p₁).counit.app
              ((Scheme.Modules.pullback p₁).obj F)) ≫
          (ppTel a p₁ p₂ w).hom.app F := by
  subst w
  simpa [ppTel, Scheme.Modules.pullbackCongr] using
    rawPushPullMap_pullback_counit_self a p₁ F

/-- **`bcv` IS the bare mate followed by the telescope — by `rfl`.**  Probed, not assumed:
`bcv` is `openImmersion_beckChevalley`, which is `asIso (openImmersion_bareBC … .app _)`
composed with `(pushforward pV).mapIso telescope.symm`, so its `hom` is definitionally that
composite.  Isolated as a named lemma because the `IsIso` instance inside `asIso` makes the
unfolding invisible to `simp` and expensive to rediscover.  Project-local. -/
theorem bcv_hom_eq (f : X ⟶ S) (g' : X' ⟶ X) (𝒰 : X.OpenCover) [IsSeparated f]
    [IsAffine S] [∀ i, IsAffine (𝒰.X i)] (F : X.Modules) (hF : F.IsQuasicoherent)
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    (bcv f g' 𝒰 F hF σ).hom
      = (openImmersion_bareBC g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))
              (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
              (pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
              (restrictedCartesianAffinePushout g' 𝒰 σ)).app
            ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj F) ≫
          (Scheme.Modules.pushforward
              (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))).map
            (openImmersion_bc_telescope g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))
              (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
              (pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
              (restrictedCartesianAffinePushout g' 𝒰 σ) F).inv :=
  rfl

set_option maxHeartbeats 1600000 in
-- The `bcv_hom_eq` unfolding forces whnf of `openImmersion_beckChevalley` through the `asIso`
-- of its `IsIso` instance, and the `erw` then re-runs the open-immersion and finite-intersection
-- instance searches over the intersection open, as `coverInterOpen_isAffine` does above.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **THE ADJUNCT OF `bcv`, IN CLOSED MATE-FREE FORM — the reusable brick half (a) is built from.**

Read under `pV^*` and past the `pV`-counit, the restricted-square Beck–Chevalley iso `bcv` is
*entirely* pullback-pseudofunctor coherence plus **one** counit of the *open inclusion*
`U_σ ↪ X`.  No mate, no `bcv`, no `openImmersion_bareBC` survives on the right-hand side.

This is `bcv_hom_eq` followed by `bareBC_pullback_counit` (with one `counit_naturality` to move
the telescope factor past the counit), and it is the statement that makes both sides of
`BcSquareCounitSide` speak the same language: each becomes a `ppTel`/telescope conjugate of the
*same* shape, one at `σ'` and one at `σ' ∘ δᵏ`.

What remains of half (a) after applying this on both sides is therefore a comparison of two
pseudofunctor-coherence conjugations across the change of `σ` — no Beck–Chevalley mate, no
flatness, no quasi-coherence, and no open-immersion property is left in it.  That is a
strictly better-located obligation than "the mate across a change of square", which is what
this file recorded as the frontier for four rounds.

Project-local; axiom-clean. -/
theorem bcv_pullback_counit (f : X ⟶ S) (g' : X' ⟶ X) (𝒰 : X.OpenCover) [IsSeparated f]
    [IsAffine S] [∀ i, IsAffine (𝒰.X i)] (F : X.Modules) (hF : F.IsQuasicoherent)
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    (Scheme.Modules.pullback
          (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))).map (bcv f g' 𝒰 F hF σ).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction
          (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))).counit.app _
      = (((pullbackComp (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))) g') ≪≫
              pullbackCongr (restrictedCartesianAffinePushout g' 𝒰 σ).w.symm ≪≫
              (pullbackComp (pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
                (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).symm).hom).app
            ((Scheme.Modules.pushforward (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj
              ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj F)) ≫
          (Scheme.Modules.pullback
              (pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))).map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).counit.app
                ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj F)) ≫
            (openImmersion_bc_telescope g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))
              (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
              (pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
              (restrictedCartesianAffinePushout g' 𝒰 σ) F).inv := by
  rw [bcv_hom_eq, Functor.map_comp, Category.assoc]
  erw [Adjunction.counit_naturality]
  rw [← Category.assoc, bareBC_pullback_counit, Category.assoc]

end AlgebraicGeometry
