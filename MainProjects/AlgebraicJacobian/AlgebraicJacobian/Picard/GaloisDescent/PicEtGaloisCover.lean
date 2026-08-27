/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GaloisDescent.PicEtGaloisBridge

/-!
# `hcov` is a purely set-theoretic condition: joint surjectivity

`Picard/GaloisDescent/PicEtGaloisBridge.lean` §4 leaves one antecedent,
`hcov`, undischarged, and four landed `sorry`-free theorems carry it:
`projections_agree_of_invariant`, `exists_unique_descend_picEt_of_invariant`,
and the two assembly theorems of `Picard/PicEtDescentRepresentability.lean`.
`hcov` says the `Gal(k'/k)`-indexed family of sections
`coverSelfSection T γ = ⟨𝟙, twist γ⟩ : T_{k'} ⟶ T_{k'} ×_T T_{k'}`
generates a covering sieve of the étale topology on the slice over `Spec k`.

**This file reduces `hcov` to joint surjectivity of that family on points, with
nothing else owed** (`hcov_of_jointlySurjective`). The morphism-property half —
which the board and `PicEtGaloisBridge.lean`'s own `hcov_iff_scheme_level`
docstring both priced as *genuinely owed* — is **free**, and the reason is not
the one those sites were looking for.

## The repricing, and it is the finding

`I-1458` (and the corrected `hcov_iff_scheme_level` docstring after it) split
`hcov` into a *topology* half, declared free, and an *open-immersion* half,
declared owed: "the open-immersion half is genuinely owed — but a failed
`infer_instance` is not absence: `IsOpenImmersion (Sigma.ι …)` is a *theorem*
… where that theorem applies". The prescription was therefore to base-change
`selfTensorSpecCoproduct` along `T_{k'} ⟶ Spec k'` and match the coproduct's
`γ`-component to `coverSelfSection T γ`.

**None of that is needed.** The étale topology's covering criterion
(`Scheme.ofArrows_mem_precoverage_iff`) asks for `Etale` of each member, *not*
`IsOpenImmersion`; and `Etale` of a section is free by post-composition
cancellation, because `Etale` carries
`MorphismProperty.HasOfPostcompProperty @Etale`:

* `coverSelfSection T γ ≫ pullback.fst = 𝟙` (`coverSelfSection_fst`), so on
  underlying schemes the composite is `𝟙`, which is `Etale`;
* `(pullback.fst _ _).left` is `Etale`, being a base change of
  `(coverMap T).left = pullback.fst T.hom (specMapAlgebra k k')`
  (`etale_pullback_fst_specMap`) — and `Over.forget` sends the slice pullback
  to a scheme pullback, since pullback is a connected shape;
* cancelling the second factor gives `Etale (coverSelfSection T γ).left`.

So the coproduct splitting, `selfTensorSpecCoproduct`, `IsGalois` and
`sigmaSpec` are **all** absent from this file: nothing here needs the Galois
level, and `etale_coverSelfSection_left` holds for an arbitrary finite
separable `k'/k` and an arbitrary test `T`. Do not budget a coproduct
base-change argument for `hcov`.

**Why `IsOpenImmersion` was the wrong target — and the first version of this
paragraph got the reason wrong, which matters more than the conclusion**
(`I-1510`, `I-1513`; refuted by a fresh-context audit and reproduced here as
`isOpenImmersion_coverSelfSection_left`). That version said `IsOpenImmersion` is
"*strictly* stronger than the site asks for … and it is the one that fails
`infer_instance` while the cheap one does not". **Both halves are false.**

* `IsOpenImmersion` is **not** strictly stronger here: it is *equivalent*, and
  provable in three lines **from `etale_coverSelfSection_left` itself**. `Etale`
  gives `Flat` and `LocallyOfFinitePresentation` by synthesis, the section
  identity gives `Mono` by `mono_of_mono_fac`, and
  `IsOpenImmersion.of_flat_of_mono` closes it. So the withdrawn prescription was
  not *more expensive* — it was **less direct**, and it is a corollary of the
  cheap route rather than an alternative to it.
* `infer_instance` fails on the **`Etale`** goal too. There is no synthesis
  asymmetry, so the sentence that made the withdrawal read as *measured* was
  measuring nothing.

What survives, and it is the whole content: the étale site's criterion asks for
`Etale`, and `Etale` of a section is one cancellation, so **no coproduct
base-change is needed for the morphism-property half**. That is a
cheapest-route finding, not a strictness ordering. The general-`γ` route to
`IsOpenImmersion` is `of_flat_of_mono`; "the diagonal of an unramified morphism
is one" — the justification the first version offered — only applies at
`γ = 1`, where `coverSelfSection_one` puts the section at the diagonal.

## What remains, stated exactly

`hcov_of_jointlySurjective`'s hypothesis: every point of
`(T_{k'} ×_T T_{k'}).left` is in the image of some `(coverSelfSection T γ).left`.
That is one statement about points, with no morphism property, no sieve, no
`picEt` and no slice in it. At a nontrivial Galois level it is the honest
content of `hcov` and it is **not** discharged here.

`I-1454` remains in force about the degenerate witness: at
`Mono (specMapAlgebra k k')` joint surjectivity holds for the trivial reason
that `coverSelfSection T 1` is an isomorphism, and there the *consequent* of §4
is free too. So this file does not exhibit a non-degenerate model; it removes
one of the two things a lane building one would have had to pay for.

## The route to joint surjectivity, measured link by link

Not built here, but every link probed to exist (`lake env lean` `EXIT=0`), so a
lane closing this owes no search:

1. `AlgebraicGeometry.pullbackSpecIso k k' k'` — Mathlib, and in *exactly* the
   shape needed: `Spec k' ×_{Spec k} Spec k' ≅ Spec (k' ⊗_k k')`.
2. Composed with `selfTensorSpecCoproduct` (already in
   `PicEtGaloisBridge.lean` §6, needs `[IsGalois k k']`), the `Spec`-level
   self-pullback **is** the `Gal`-indexed coproduct of copies of `Spec k'`, and
   the comparison is `IsIso` by synthesis.
3. `Scheme` is `FinitaryPreExtensive` **by synthesis**, and
   `CategoryTheory.FinitaryPreExtensive.isIso_sigmaDesc_fst` is the lemma that
   distributes a pullback over that coproduct. No new extensivity lemma is
   needed — and note this project already wraps it, at
   `AlgebraicGeometry.prod_coproduct_distrib` /`coprodFirst_distrib`
   (`Cohomology/CechSectionIdentificationBase.lean`), so check those before
   re-deriving.
4. A universe step: `isIso_sigmaDesc_fst` binds its index at `Type` (i.e.
   `Type 0`) while `k' ≃ₐ[k] k'` lives in `Type u`. `Gal(k'/k)` is finite, hence
   `Small.{0}` by `inferInstance`, and `Limits.Sigma.reindex (equivShrink _).symm`
   crosses it (the project wrappers in link 3 bind `ι : Type` as well, so they
   inherit this step rather than removing it).

**And the two steps where the work actually is are NOT in that list — corrected
here** (`I-1511`, fresh-context audit; the first version of this note said
"every link has been probed to exist", which invited reading it as *no unknown
link remains*). Links 1–4 deliver a *decomposition* of the self-pullback and
stop short of the goal. Still owed, and they are exactly the two steps the
withdrawn prescription named — they are the only ones that touch the
`γ`-indexing:

* base change of the `Spec`-level coproduct along `T_{k'} ⟶ Spec k'`;
* identification of the coproduct's `γ`-component with `coverSelfSection T γ`.

Joint surjectivity of *coproduct inclusions* is free once those are in hand
(`(sigmaOpenCover g).exists_eq`), so the residue is entirely the `γ`-matching.
What links 1–4 buy is that no *library* gap sits under it.

One further fact measured on the way and recorded because `inferInstance` does
**not** give it: `coverMap T` is `IsFinite` on underlying schemes, via
`IsFinite.SpecMap_iff` + `RingHom.finite_algebraMap` and then base change along
`T.hom`. (`[Algebra.IsSeparable]` is not consumed by that one.)

## Main declarations

* `etale_coverSelfSection_left` — each `γ`-section is `Etale` on underlying
  schemes, unconditionally in `γ`; the étale half of `hcov`, free.
* `mono_coverSelfSection_left`, `isOpenImmersion_coverSelfSection_left` — the
  withdrawn prescription's property, *derived from* the étale one, which is why
  "strictly stronger" was wrong.
* `hcov_of_jointlySurjective` — `hcov` from joint surjectivity alone.
* `jointlySurjective_of_mono` — the satisfiability witness **for the
  point-level hypothesis**, as a declaration rather than a docstring sentence.
* `projections_agree_of_jointlySurjective`,
  `exists_unique_descend_picEt_of_jointlySurjective` — the two
  `PicEtGaloisBridge.lean` consumers restated on the set-theoretic hypothesis.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace PicScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  [Algebra.IsSeparable k k'] [Module.Finite k k']

/-! ## §1. The étale half of `hcov`, free -/

/-- **The `γ`-section is `Etale`, and it needs no open-immersion input.**

`coverSelfSection T γ` is a *section* of `pullback.fst (coverMap T) (coverMap T)`
by `coverSelfSection_fst`, and that projection is `Etale` on underlying schemes
as a base change of `(coverMap T).left`. `Etale` has
`MorphismProperty.HasOfPostcompProperty @Etale`, so cancelling the projection
off the identity gives the section's own étaleness.

Arbitrary `γ`, arbitrary test `T`, no `[IsGalois k k']`: this is where the
previously-quoted "genuinely owed" half of `hcov` goes. -/
theorem etale_coverSelfSection_left (T : Over (Spec (CommRingCat.of k)))
    (γ : k' ≃ₐ[k] k') :
    Etale (coverSelfSection (k := k) (k' := k') T γ).left := by
  have hcm : Etale (coverMap (k := k) (k' := k') T).left := by
    rw [coverMap_left]; exact etale_pullback_fst_specMap k k' T.left T.hom
  have hpb := (IsPullback.of_hasPullback (coverMap (k := k) (k' := k') T)
    (coverMap (k := k) (k' := k') T)).map (Over.forget (Spec (CommRingCat.of k)))
  have hfst : Etale (Limits.pullback.fst (coverMap (k := k) (k' := k') T)
      (coverMap (k := k) (k' := k') T)).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) hpb.flip hcm
  have hcomp : (coverSelfSection (k := k) (k' := k') T γ).left ≫
      (Limits.pullback.fst (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).left = 𝟙 _ := by
    rw [← Over.comp_left, coverSelfSection_fst]; rfl
  refine MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _ _ hfst ?_
  rw [hcomp]; infer_instance

omit [Algebra.IsSeparable k k'] [Module.Finite k k'] in
/-- The `γ`-section is a monomorphism: it is split by `pullback.fst`.

Neither separability nor finiteness is consumed — being split is formal — so both
are `omit`ted; they are the étale half's price, not this one's. -/
theorem mono_coverSelfSection_left (T : Over (Spec (CommRingCat.of k)))
    (γ : k' ≃ₐ[k] k') :
    Mono (coverSelfSection (k := k) (k' := k') T γ).left := by
  have hfac : (coverSelfSection (k := k) (k' := k') T γ).left ≫
      (Limits.pullback.fst (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).left = 𝟙 _ := by
    rw [← Over.comp_left, coverSelfSection_fst]; rfl
  exact mono_of_mono_fac hfac

/-- **The withdrawn prescription's property, DERIVED from the étale one.**

`IsOpenImmersion (coverSelfSection T γ).left` — the thing `I-1458` and two
docstrings called the "genuinely owed" half of `hcov` — follows in three lines
from `etale_coverSelfSection_left`: `Etale` gives `Flat` and
`LocallyOfFinitePresentation` by synthesis, `mono_coverSelfSection_left` gives
`Mono`, and `IsOpenImmersion.of_flat_of_mono` finishes.

**This declaration exists to make the correction compiler-checked rather than
asserted.** It is *why* calling `IsOpenImmersion` "strictly stronger" was wrong
(`I-1510`): at this site the two are equivalent, and the expensive one is a
corollary of the cheap one. Note that `hcov_of_jointlySurjective` does not use
it — the site never needed it — which is the separate point. -/
theorem isOpenImmersion_coverSelfSection_left (T : Over (Spec (CommRingCat.of k)))
    (γ : k' ≃ₐ[k] k') :
    IsOpenImmersion (coverSelfSection (k := k) (k' := k') T γ).left :=
  haveI := etale_coverSelfSection_left (k := k) (k' := k') T γ
  haveI := mono_coverSelfSection_left (k := k) (k' := k') T γ
  IsOpenImmersion.of_flat_of_mono _

/-! ## §2. `hcov` from joint surjectivity -/

/-- **`hcov` reduces to joint surjectivity on points, with nothing else owed.**

Given only that every point of the self-pullback is hit by some
`(coverSelfSection T γ).left`, the `Gal`-indexed family generates a covering
sieve of `etaleTopologyOver k`.

The route: `Scheme.Cover.mkOfCovers` assembles the family into an étale
`Cover` of the underlying scheme — joint surjectivity is its first field and
`etale_coverSelfSection_left` its second — and then
`hcov_iff_scheme_level` (already in `PicEtGaloisBridge.lean`) transports
membership from the slice to the underlying scheme, where
`Cover.mem_grothendieckTopology` finishes. The final step checks the
transported sieve contains the cover's, which is `Sieve.overEquiv_iff` applied
to `coverSelfSection T γ` itself.

**Non-vacuity, and the caveat it does not remove.** The hypothesis is
satisfiable, by `jointlySurjective_of_mono` below — but by `I-1454` that site
*also* makes §4's consequent free, so this is satisfiability and not a
non-degenerate model. What this theorem changes is the price of building one:
only the point-level statement is left.

**The citation here was wrong in the first version and is corrected**
(`I-1512`): it named `etaleTopology_generate_coverSelfSection_of_mono`, which
concludes **sieve membership** — i.e. `hcov` itself — not joint surjectivity on
points. Those are different propositions and `hcov` does not imply the point
statement, so that name could not have backed this sentence. The witness is now
`jointlySurjective_of_mono`, a declaration in this file at the right
proposition, per the `I-1413`/`I-1454` rule the paragraph above invokes: an
antecedent audit has to be a theorem, not a probe. -/
theorem hcov_of_jointlySurjective (T : Over (Spec (CommRingCat.of k)))
    (hsurj : ∀ x : (Limits.pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).left,
      ∃ (γ : k' ≃ₐ[k] k') (y : ((restrictTest k k').obj (baseTest (k' := k') T)).left),
        (coverSelfSection (k := k) (k' := k') T γ).left y = x) :
    Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      etaleTopologyOver k (Limits.pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)) := by
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale)
      (Limits.pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).left :=
    Scheme.Cover.mkOfCovers (P := @Etale) (k' ≃ₐ[k] k')
      (fun _ => ((restrictTest k k').obj (baseTest (k' := k') T)).left)
      (fun γ => (coverSelfSection (k := k) (k' := k') T γ).left)
      hsurj
      (fun γ => etale_coverSelfSection_left T γ)
  rw [hcov_iff_scheme_level]
  refine GrothendieckTopology.superset_covering _ ?_ 𝒰.mem_grothendieckTopology
  rintro W f ⟨Z, a, b, hb, rfl⟩
  cases hb with | mk γ =>
  refine Sieve.downward_closed _ ?_ a
  rw [Sieve.overEquiv_iff]
  refine ⟨(restrictTest k k').obj (baseTest (k' := k') T),
    Over.homMk (𝟙 _) ?_, coverSelfSection (k := k) (k' := k') T γ,
    Presieve.ofArrows.mk γ, ?_⟩
  case refine_1 =>
    exact (Category.id_comp _).trans ((coverSelfSection (k := k) (k' := k') T γ).w).symm
  case refine_2 =>
    apply Over.OverMorphism.ext
    exact Category.id_comp _

omit [Algebra.IsSeparable k k'] [Module.Finite k k'] in
/-- **The joint-surjectivity hypothesis IS SATISFIABLE**, at any extension whose
`Spec` map is a monomorphism (`k' = k` in particular, by `specMapAlgebra_self`):
there `coverSelfSection T 1` is an isomorphism, so every point is in the image of
the `γ = 1` section.

**This is satisfiability and NOT non-vacuity**, and the reason is `I-1454`, in
force unchanged: at this very site `specGal_eq_id_of_mono` collapses every `γ` to
the identity, so `twistTest T γ = 𝟙` and §4's *consequent* holds with neither
hypothesis. So this theorem shows `hcov_of_jointlySurjective` is not conditioned
on a false statement, and shows nothing more. A model with a nontrivial
automorphism is what remains open.

It is stated as a declaration rather than left in a scratch probe because that is
the rule the file's own docstring invokes (`I-1413`, `I-1512`): the antecedent
audit must be in the tree at the proposition being audited.

**Binder note**: neither `[Algebra.IsSeparable k k']` nor `[Module.Finite k k']`
is consumed here — the witness is pure category theory about an isomorphism — so
both are `omit`ted. They are input 1's price, needed by `hcov_of_jointlySurjective`
via the étale half, not by this satisfiability statement. -/
theorem jointlySurjective_of_mono [Mono (specMapAlgebra k k')]
    (T : Over (Spec (CommRingCat.of k))) :
    ∀ x : (Limits.pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).left,
      ∃ (γ : k' ≃ₐ[k] k') (y : ((restrictTest k k').obj (baseTest (k' := k') T)).left),
        (coverSelfSection (k := k) (k' := k') T γ).left y = x := by
  intro x
  have hiso : IsIso (coverSelfSection (k := k) (k' := k') T 1) := by
    rw [coverSelfSection_one]; infer_instance
  refine ⟨1, (inv (coverSelfSection (k := k) (k' := k') T 1)).left x, ?_⟩
  have h2 : (inv (coverSelfSection (k := k) (k' := k') T 1)).left ≫
      (coverSelfSection (k := k) (k' := k') T 1).left = 𝟙 _ := by
    rw [← Over.comp_left, IsIso.inv_hom_id]; rfl
  rw [← Scheme.Hom.comp_apply, h2]; simp

/-! ## §3. The two `PicEtGaloisBridge` consumers, on the new hypothesis -/

/-- **`projections_agree_of_invariant` with `hcov` replaced by joint
surjectivity.** This is the form a `G1` consumer can actually aim at: the
hypothesis is a statement about points of one scheme. -/
theorem projections_agree_of_jointlySurjective (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k)))
    (hsurj : ∀ x : (Limits.pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).left,
      ∃ (γ : k' ≃ₐ[k] k') (y : ((restrictTest k k').obj (baseTest (k' := k') T)).left),
        (coverSelfSection (k := k) (k' := k') T γ).left y = x)
    (x : (picEt C).obj (Opposite.op ((restrictTest k k').obj (baseTest (k' := k') T))))
    (hinv : ∀ γ : k' ≃ₐ[k] k', (picEt C).map (twistTest T γ).op x = x) :
    (picEt C).map (Limits.pullback.fst (coverMap (k := k) (k' := k') T)
          (coverMap (k := k) (k' := k') T)).op x
      = (picEt C).map (Limits.pullback.snd (coverMap (k := k) (k' := k') T)
          (coverMap (k := k) (k' := k') T)).op x :=
  projections_agree_of_invariant C T (hcov_of_jointlySurjective T hsurj) x hinv

/-- **The descent step with a point-level hypothesis.**

`exists_unique_descend_picEt_of_invariant` composed with §2: a `γ`-invariant
class on `T_{k'}` descends to a unique class on `T`, given only that the
`γ`-sections are jointly surjective on points. -/
theorem exists_unique_descend_picEt_of_jointlySurjective
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k)))
    (hsurj : ∀ x : (Limits.pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).left,
      ∃ (γ : k' ≃ₐ[k] k') (y : ((restrictTest k k').obj (baseTest (k' := k') T)).left),
        (coverSelfSection (k := k) (k' := k') T γ).left y = x)
    (x : (picEt C).obj (Opposite.op ((restrictTest k k').obj (baseTest (k' := k') T))))
    (hinv : ∀ γ : k' ≃ₐ[k] k', (picEt C).map (twistTest T γ).op x = x) :
    ∃! y : (picEt C).obj (Opposite.op T),
      (picEt C).map (coverMap (k' := k') T).op y = x :=
  exists_unique_descend_picEt_of_invariant C T (hcov_of_jointlySurjective T hsurj) x hinv

end PicScheme
end Scheme
end AlgebraicGeometry
