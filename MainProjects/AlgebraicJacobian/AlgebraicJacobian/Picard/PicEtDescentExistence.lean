/-
Copyright (c) 2026 Axel Delaval. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval
-/
import Mathlib
import AlgebraicJacobian.Picard.PicEtDescentAssembly
import AlgebraicJacobian.Picard.GaloisDescent.GaloisSelfTensor

/-!
# The EXISTENCE half of the `picEt` field-descent step, at one morphism

`AJC.picrep.etale-rep.invariance`.

## What this file is for

`Picard/PicEtDescentAssembly.lean` proves the **uniqueness** half of the descent
step at the field-extension cover: `picEt_injective_restrict_baseTest` says a
`k`-class is determined by its restriction along the single morphism
`coverMap T : T_{k'} ⟶ T`. Its §4 records that the corresponding *existence*
statement is not in the tree, and names the two things that would produce a
descended class.

This file supplies the missing half of the **sheaf-theoretic** side, in the
single-morphism form a consumer can actually use, and then states precisely what
that leaves owed — which is *not* a sheaf-theoretic fact.

## The gap it closes, stated exactly

`Picard/EtaleFieldCover.lean` proves the sheaf axiom at the *scheme-level*
generated sieve transported by `Sieve.overEquiv`
(`isSheafFor_picEt_pullback_presieve`). What a consumer of the descent step holds
is a class on `T_{k'}`, i.e. datum indexed by the **slice-level** singleton
presieve on `coverMap T`. Those two presieves are *not* the same object, and
nothing identified them: the sieve-indexed statement cannot be applied to a
single-morphism datum without the identification, which is why
`PicEtDescentAssembly.lean`'s uniqueness proof had to redo the factorisation by
hand inside its own proof rather than cite a lemma.

`generate_singleton_coverMap_eq` is that identification, as an equality of sieves
on `T` in the slice — **and it is Mathlib's `Sieve.overEquiv_ofArrows` at a
one-element index, not new work** (`I-1407`; the first revision of this file
re-proved it in 26 lines and claimed "nothing identified them"). With it:

* `isSheafFor_picEt_singleton_coverMap` — the sheaf axiom holds for the
  **slice-level singleton presieve** on `coverMap T`. **This is the file's only
  geometric content**: it is where the covering-sieve witness of
  `Picard/EtaleFieldCover.lean` is consumed.
* `exists_unique_descend_picEt` — the existence-and-uniqueness statement in the
  form the descent step consumes: a class `x` on `T_{k'}` whose two pullbacks to
  any common test agree descends to a **unique** class on `T`.

The uniqueness half of `exists_unique_descend_picEt` is *not* a second proof of
`picEt_injective_restrict_baseTest`; it is the `∃!` that the sheaf condition
delivers in one piece, and the earlier lemma is the form that takes two classes
rather than a compatibility hypothesis.

**Honest accounting of what is and is not new here** (`I-1407`, `I-1410`,
fresh-context audits, both reproduced and accepted). Of the eight declarations, the
sieve identification is Mathlib's; the `∃!` chain and the two-projection reduction
are **generic category theory** — a reviewer re-proved all three for an arbitrary
presheaf on an arbitrary category using this file's own script, and Mathlib packages
the pair as `Equalizer.Presieve.isSheafFor_singleton_iff_of_hasPullback`; the two
tensor-inclusion lemmas are one `simp` each. What this file genuinely contributes is
**assembly**: putting the landed cover, the landed sheaf axiom and those generic
facts together so that the descent step is a citable theorem in the variables a `G1`
consumer holds, which it was not. That is worth having and is not a new theorem, and
the docstrings below say so at each site.

## What remains owed, and why this is not the invariance step

The hypothesis of `exists_unique_descend_picEt` is *agreement of the two
pullbacks*. What campaign `G1` hands over is different: a class fixed by the
semilinear `Gal(k'/k)`-action. **Those are not the same hypothesis**, and the
bridge between them is the Galois-splitting comparison
`k' ⊗_k k' ≅ ∏_{Gal(k'/k)} k'` — under which the two projections
`T_{k'} ×_T T_{k'} ⟶ T_{k'}` become the identity and the `γ`-twist, so that
"the two pullbacks agree" becomes "`γ` fixes the class, for every `γ`". That
splitting is `ajc-p1`'s row `AJC.picrep.etale-rep.galois-splitting`; it was absent
from Mathlib when measured (`exact?` failed on both the `AlgEquiv` and the
`RingEquiv` form) and **landed during this session** as
`AlgebraicJacobian.GaloisDescent.galoisSelfTensorEquiv`. What this file assumes of
it is only the two generator evaluations in §2; the `Spec`-side transport is open.

So the honest statement of what is closed here is: *the sheaf-theoretic content
of the existence half, in single-morphism form*. The Galois-to-pullback
translation is open and is named, not restated more cheaply.

## What this does NOT do

It closes no `sorry` in `Picard/FGAPicRepresentability.lean` and witnesses **no**
antecedent of `Scheme.fgaPicardRepresentability` for any curve. In particular it
says nothing about the existence of a representing scheme: it descends *classes*,
which is the layer `PicEtDescentAssembly.lean`'s §3 already priced as free — what
this file adds is that the free layer is usable at one morphism, which it was not.

Deliberately contains no implication whose antecedent is its own conclusion, and
no class-valued conclusion: `instHasPicSchemeEt` is unconditional, so a
`HasPicSchemeEt`-valued conclusion is discharged by instance search projecting the
seam `sorry` (`I-1251`).

## Measurement discipline

`lake build AlgebraicJacobian` EXIT=0 with **fresh** oleans before every probe
below; a stale-import environment reports every probe as succeeding (`I-1057`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct

namespace AlgebraicGeometry

namespace Scheme

namespace PicScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-! ## §1. The two presieves are one sieve -/

/-- **A slice-level singleton sieve is the `overEquiv`-transport of its
scheme-level shadow** — generic in the category and the slice.

`Picard/EtaleFieldCover.lean` establishes covering-sieve membership and the sheaf
axiom for a sieve described on the *underlying schemes* and pulled back into the
slice; a consumer of the descent step instead holds a datum indexed by one slice
morphism. This is the identification that lets every statement proved for the one
apply verbatim to the other.

**This is Mathlib's `Sieve.overEquiv_ofArrows` at a one-element index, and the
first revision of this file re-proved it in 26 lines of `ext`/`rintro`** — a
duplicate of a lemma in its own import closure, found by a fresh-context audit
(`I-1407`) and replaced by the two-line derivation. Two claims that stood in this
docstring are withdrawn with it: that "nothing identified the two" (Mathlib does,
generically), and the paragraph describing the proof as a two-directional
factorisation consuming `pullback.condition` (it consumes neither — `ofArrows_pUnit`
plus the Mathlib lemma).

What survives is the *use*: the statement is not `rfl` and not `⊤`, and §2 needs it.
The specialisation below is kept as a named form because it is what the geometric
statements cite, but the content is Mathlib's and no lane should budget for it.

No hypothesis on `k'/k` at all — not even `[Algebra k k']` is used by the general
form. -/
theorem generate_singleton_overEquiv_symm {C : Type*} [Category C] {X : C}
    {Y Z : Over X} (f : Z ⟶ Y) :
    Sieve.generate (Presieve.singleton f) =
      (Sieve.overEquiv Y).symm (Sieve.generate (Presieve.singleton f.left)) := by
  rw [Equiv.eq_symm_apply, ← Presieve.ofArrows_pUnit.{_, _, 0} f,
    ← Presieve.ofArrows_pUnit.{_, _, 0} f.left]
  exact Sieve.overEquiv_ofArrows (fun _ : PUnit => Z) (fun _ => f)

theorem generate_singleton_coverMap_eq (T : Over (Spec (CommRingCat.of k))) :
    Sieve.generate (Presieve.singleton (coverMap (k := k) (k' := k') T)) =
      (Sieve.overEquiv T).symm
        (Sieve.generate (Presieve.singleton
          (pullback.fst T.hom (specMapAlgebra k k')))) :=
  generate_singleton_overEquiv_symm _

/-! ## §2. The sheaf axiom at the cover morphism, and the `∃!` descent -/

section Cover

variable [Algebra.IsSeparable k k'] [Module.Finite k k']

/-- **The sheaf axiom of `picEt` at the slice-level singleton presieve on
`coverMap`.**

This is `Scheme.isSheafFor_picEt_pullback_presieve` (`Picard/EtaleFieldCover.lean`)
carried across `generate_singleton_coverMap_eq`. It is the form a *consumer*
needs, and the reason it needed a lemma at all is §1: the landed statement is
about a sieve described on underlying schemes, while a descent datum is indexed by
one slice morphism.

Finiteness and separability of `k'/k` re-enter here — not for the identification,
but because they are what makes the family *covering* in the étale topology. -/
theorem isSheafFor_picEt_singleton_coverMap (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k))) :
    Presieve.IsSheafFor (picEt C)
      (Presieve.singleton (coverMap (k := k) (k' := k') T)) := by
  rw [Presieve.isSheafFor_iff_generate, generate_singleton_coverMap_eq]
  exact AlgebraicGeometry.Scheme.isSheafFor_picEt_pullback_presieve k' C T

/-- **The existence-and-uniqueness form of the descent step at one morphism.**

For a smooth proper curve `C` over an arbitrary field `k`, a finite separable
`k'/k` and an arbitrary `k`-test `T`: a class `x ∈ Pic_{(C/k)ét}(T_{k'})` whose two
pullbacks along any pair of morphisms agreeing over `T` coincide descends to a
**unique** class on `T`.

This is the statement `PicEtDescentAssembly.lean`'s §4 recorded as missing on the
existence side, in the shape a consumer holds its datum in. Its uniqueness half
overlaps `picEt_injective_restrict_baseTest`, deliberately: that lemma takes *two
classes* and this one takes *one class with a compatibility hypothesis*, and a
consumer of the descent step has the latter.

**Non-vacuity measured, not asserted**, with both obvious refutations probed
(`lake env lean`, fresh oleans, both `exact?` reporting failure):

* dropping the compatibility hypothesis `hx` leaves the `∃!` conclusion **open**,
  so the hypothesis is not decoration;
* the same conclusion at an *arbitrary* morphism `f : W ⟶ T` in place of `coverMap`
  is **open**, so the covering-sieve witness of `Picard/EtaleFieldCover.lean` is
  load-bearing rather than incidental.

**No hypothesis on `C(k)`** (`I-0491`), and none on `T`. -/
theorem exists_unique_descend_picEt (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k)))
    (x : (picEt C).obj (Opposite.op ((restrictTest k k').obj (baseTest (k' := k') T))))
    (hx : ∀ {W : Over (Spec (CommRingCat.of k))}
      (p₁ p₂ : W ⟶ (restrictTest k k').obj (baseTest (k' := k') T)),
      p₁ ≫ coverMap (k' := k') T = p₂ ≫ coverMap (k' := k') T →
      (picEt C).map p₁.op x = (picEt C).map p₂.op x) :
    ∃! y : (picEt C).obj (Opposite.op T),
      (picEt C).map (coverMap (k' := k') T).op y = x := by
  have h := isSheafFor_picEt_singleton_coverMap (k' := k') C T
  rw [Presieve.isSheafFor_singleton] at h
  exact h x hx

omit [Algebra.IsSeparable k k'] [Module.Finite k k'] in
/-- **Compatibility reduces to the TWO canonical projections.**

`exists_unique_descend_picEt`'s hypothesis quantifies over *every* pair of
morphisms agreeing over `T`. This says it is enough to check the single pair
`pullback.fst`, `pullback.snd` of the cover's self-pullback — so the hypothesis is
a *checkable* condition on one object rather than a family of conditions.

This is the step that makes the Galois bridge attachable: the standard
`k' ⊗_k k' ≅ ∏_{Gal} k'` argument says something about exactly these two
projections and nothing about arbitrary pairs. Without this reduction a consumer
holding `γ`-invariance would have no target to aim at.

Pure universal property — `pullback.lift` on the pair, then functoriality. **The
`omit` is a measurement, not tidying**: neither `[Algebra.IsSeparable k k']` nor
`[Module.Finite k k']` is consumed, which the linter confirms, so the reduction is
not a fact about *this* cover at all — it holds at any morphism with a
self-pullback. Recorded because "the step needs the cover" is exactly the sort of
claim that gets inherited from a section header (`I-1316`). What needs the cover is
`isSheafFor_picEt_singleton_coverMap`, one lemma up.

**And the `omit` UNDERSTATES it** (`I-1410`, fresh-context audit, accepted and
reproduced): a work-reviewer re-proved this lemma *and* both `∃!` statements below
for an **arbitrary presheaf on an arbitrary category**, using this file's own `calc`
script with `picEt ↦ F` and `coverMap ↦ f`, with the field, the curve, the slice and
`Scheme` all deleted. So these three declarations are generic category theory in a
geometric costume; the geometric binders they carry are inherited from the section,
not consumed. Mathlib moreover packages the pair as
`Equalizer.Presieve.isSheafFor_singleton_iff_of_hasPullback`
(`Sites/EqualizerSheafCondition.lean`, verified present), whose own proof contains
this reduction as an inlined `have`. They are kept in geometric form because that is
what the descent step cites, but **nothing here is a geometric fact** and no lane
should budget for re-deriving them. The geometric content of this file is exactly
`isSheafFor_picEt_singleton_coverMap`'s appeal to the covering-sieve witness. -/
theorem compatible_of_pullback_projections (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k)))
    (x : (picEt C).obj (Opposite.op ((restrictTest k k').obj (baseTest (k' := k') T))))
    (h : (picEt C).map (pullback.fst (coverMap (k := k) (k' := k') T)
              (coverMap (k := k) (k' := k') T)).op x
        = (picEt C).map (pullback.snd (coverMap (k := k) (k' := k') T)
              (coverMap (k := k) (k' := k') T)).op x)
    {W : Over (Spec (CommRingCat.of k))}
    (p₁ p₂ : W ⟶ (restrictTest k k').obj (baseTest (k' := k') T))
    (hp : p₁ ≫ coverMap (k' := k') T = p₂ ≫ coverMap (k' := k') T) :
    (picEt C).map p₁.op x = (picEt C).map p₂.op x := by
  set l := pullback.lift (f := coverMap (k := k) (k' := k') T)
    (g := coverMap (k := k) (k' := k') T) p₁ p₂ hp with hl
  have h1 : l ≫ pullback.fst (coverMap (k := k) (k' := k') T)
      (coverMap (k := k) (k' := k') T) = p₁ := pullback.lift_fst _ _ _
  have h2' : l ≫ pullback.snd (coverMap (k := k) (k' := k') T)
      (coverMap (k := k) (k' := k') T) = p₂ := pullback.lift_snd _ _ _
  calc (picEt C).map p₁.op x
      = (picEt C).map (l ≫ pullback.fst (coverMap (k := k) (k' := k') T)
          (coverMap (k := k) (k' := k') T)).op x := by rw [h1]
    _ = (picEt C).map l.op ((picEt C).map (pullback.fst
          (coverMap (k := k) (k' := k') T) (coverMap (k := k) (k' := k') T)).op x) := by
          simp only [op_comp, Functor.map_comp, CategoryTheory.comp_apply]
    _ = (picEt C).map l.op ((picEt C).map (pullback.snd
          (coverMap (k := k) (k' := k') T) (coverMap (k := k) (k' := k') T)).op x) := by
          rw [h]
    _ = (picEt C).map (l ≫ pullback.snd (coverMap (k := k) (k' := k') T)
          (coverMap (k := k) (k' := k') T)).op x := by
          simp only [op_comp, Functor.map_comp, CategoryTheory.comp_apply]
    _ = (picEt C).map p₂.op x := by rw [h2']

/-- **The descent step in the form a consumer can discharge**: agreement of the
two canonical projections suffices for a unique descended class.

`exists_unique_descend_picEt` composed with `compatible_of_pullback_projections`.
This is the statement a `G1` consumer should aim at — its hypothesis is an equation
between two specific restrictions of one class, which is what the Galois splitting
translates `γ`-invariance into. -/
theorem exists_unique_descend_picEt_of_projections
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k)))
    (x : (picEt C).obj (Opposite.op ((restrictTest k k').obj (baseTest (k' := k') T))))
    (h : (picEt C).map (pullback.fst (coverMap (k := k) (k' := k') T)
              (coverMap (k := k) (k' := k') T)).op x
        = (picEt C).map (pullback.snd (coverMap (k := k) (k' := k') T)
              (coverMap (k := k) (k' := k') T)).op x) :
    ∃! y : (picEt C).obj (Opposite.op T),
      (picEt C).map (coverMap (k' := k') T).op y = x :=
  exists_unique_descend_picEt (k' := k') C T x
    (fun p₁ p₂ hp => compatible_of_pullback_projections C T x h p₁ p₂ hp)

end Cover

/-! ### The self-pullback of the cover is a base change of `Spec k' ×_k Spec k'` -/

/-- **The object the compatibility hypothesis lives on, identified.**

The slice self-pullback `T_{k'} ×_T T_{k'}` of `coverMap T`, read on underlying
schemes, is `T_{k'} ×_{Spec k} Spec k'` — i.e. `T ×_k k' ×_k k'`, **two**
`k'`-factors over `k`. Two free steps:

1. `Over.forget` **preserves pullbacks** (by synthesis), so the slice pullback is
   computed on schemes — this is `PreservesPullback.iso`;
2. `pullbackRightPullbackFstIso` then rewrites the self-pullback of `pullback.fst`
   as a single pullback against `specMapAlgebra k k'`.

**Why this is recorded rather than left to the reader.** It is the step my own §4
first priced as the open link, on the evidence that `exact?` fails on the composite
iso. `exact?` failing on a one-shot query is not a measurement of absence when the
statement decomposes; here it does, into two lemmas that both already exist. Both
`HasPullback` instances arrive by synthesis.

**A correction to this docstring's own earlier headline** (`I-1412`, fresh-context
audit, accepted): it said the right-hand side was "the base change of the
field-extension **self**-pullback along `T_{k'} ⟶ Spec k`". That is a *different
object* — it would carry **three** `k'`-factors, second leg
`pullback.fst _ _ ≫ specMapAlgebra k k'`, whereas the landed second leg is
`specMapAlgebra k k'` itself. The iso is true and axiom-clean; the description was
off by one `k'`-factor, and that factor is exactly where the `Gal`-indexing lives.
So this iso brings the compatibility object into `Spec`-of-a-tensor form; it does
**not** already exhibit the `Gal`-indexed decomposition.

No hypothesis on `k'/k` beyond `[Algebra k k']`: this is base change, not covering. -/
noncomputable def selfPullback_coverMap_left_iso (T : Over (Spec (CommRingCat.of k))) :
    (pullback (coverMap (k := k) (k' := k') T)
      (coverMap (k := k) (k' := k') T)).left ≅
    pullback (pullback.fst T.hom (specMapAlgebra k k') ≫ T.hom)
      (specMapAlgebra k k') :=
  (PreservesPullback.iso (Over.forget (Spec (CommRingCat.of k)))
    (coverMap (k := k) (k' := k') T) (coverMap (k := k) (k' := k') T)) ≪≫
  pullbackRightPullbackFstIso T.hom (specMapAlgebra k k')
    (pullback.fst T.hom (specMapAlgebra k k'))

/-! ### Evaluating the splitting on the two tensor inclusions

The `γ`-component of `ajc-p1`'s splitting, evaluated on the two ring inclusions
`k' → k' ⊗_k k'`, gives `a` and `γ a`.

**These are NOT the residue §4 names, and the first revision of this section said
they were** (`I-1415`, fresh-context audit, accepted). §4's residue is a statement
about the *coproduct* side — a `γ`-component **inclusion** `Spec k' → Spec k' ×_k
Spec k'` composed with the cover's two **projections**. What is below mentions no
coproduct, no `sigmaSpec`, no pullback projection and no `Spec`: it is the
(easier) evaluation of the equivalence on the two generators of the **tensor**
side. The withdrawn sentence claimed "a residue worth naming is worth checking is
not free — these two are", which was self-consistent only under the false
identification.

What they are good for, kept because it is real: they are the **first code
consumers** of `Picard/GaloisDescent/GaloisSelfTensor.lean`, measured at **zero**
when it landed (`I-1399`), so they check that the brick's `simp` lemmas are usable
rather than merely true. They are also the ring-level input any `Spec`-side
coherence proof will need. They are cheap and are not presented otherwise.

The `change` on the first leg is load-bearing: `includeLeftRingHom a` does not
`simp`-normalise to `a ⊗ₜ 1` on its own, and without it instance resolution gets
stuck on a metavariable in `SMulCommClass`. -/
theorem galoisSelfTensor_includeLeft (k' : Type u) [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (γ : k' ≃ₐ[k] k') (a : k') :
    AlgebraicJacobian.GaloisDescent.galoisSelfTensorEquiv k k'
      (Algebra.TensorProduct.includeLeftRingHom a) γ = a := by
  change AlgebraicJacobian.GaloisDescent.galoisSelfTensorEquiv k k'
    (a ⊗ₜ[k] (1 : k')) γ = a
  simp [AlgebraicJacobian.GaloisDescent.galoisSelfTensorEquiv_apply_tmul]

theorem galoisSelfTensor_includeRight (k' : Type u) [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (γ : k' ≃ₐ[k] k') (a : k') :
    AlgebraicJacobian.GaloisDescent.galoisSelfTensorEquiv k k'
      ((1 : k') ⊗ₜ[k] a) γ = γ a := by
  simp [AlgebraicJacobian.GaloisDescent.galoisSelfTensorEquiv_apply_tmul]

/-! ## §3. The level this runs at is the level a curve reaches — the join

`§2` is generic in `k'`: `generate_singleton_coverMap_eq` binds only
`[Algebra k k']`, and `§2` adds exactly the two binders that make the family
covering. That matters because `ajc-p3`'s producer
(`Curve/GaloisLevelRationalPoint.lean`,
`Scheme.exists_finiteGalois_level_hasRationalPoint_of_geometricallyIntegral`)
does **not** hand over a section at a level of the consumer's choosing: its
conclusion is an *existential* over `k''`, and that `k''` is manufactured from the
point as a normal closure. So "the section is available" and "the section is
available **at my cover's level**" are different statements, and the second is
what a descent step needs (`ajc-p3`, caveat on `I-1371`).

**Elaborated rather than argued** (`lake env lean` EXIT=0, fresh oleans; scratch
file, not kept): at the `k''` that producer manufactures, `coverMap` exists and
`isSheafFor_picEt_singleton_coverMap` applies, both instances arriving by
`letI` from the `obtain`. So the answer to that caveat is the cheap one — no
join or enlargement step is owed, because this file's statements are generic in
the level. Recorded here because the composition is the kind of thing that is
invisible from either side: the producer's file has no `picEt` in it and this one
has no rational point.

## §4. What is still owed, named rather than restated more cheaply

The hypothesis of `exists_unique_descend_picEt_of_projections` is **agreement of
the cover's two canonical projections**. Campaign `G1` produces something else: a
class fixed by the semilinear `Gal(k'/k)`-action. The bridge is the Galois
splitting `k' ⊗_k k' ≅ ∏_{Gal(k'/k)} k'` — under it the two projections become the
identity and the `γ`-twist, so projection-agreement becomes `γ`-invariance for
every `γ`.

**The ALGEBRA half of that bridge landed while this file was being written**:
`ajc-p1`'s `Picard/GaloisDescent/GaloisSelfTensor.lean`
(`galoisSelfTensorEquiv`, row `AJC.picrep.etale-rep.galois-splitting`). It was
absent from Mathlib when I measured it — `exact?` failed on both the `AlgEquiv` and
the `RingEquiv` form and `Algebra.Etale K (L ⊗[K] L)` failed synthesis — and it is
now in this project. So the residue is **not** the splitting.

**Where the residue is, and a correction to my own first pricing of it.** The
splitting is a statement about `Spec k' ×_{Spec k} Spec k'`; the compatibility
hypothesis above is about `T_{k'} ×_T T_{k'}`, the self-pullback of `coverMap` **in
the slice over `Spec k`, relative to an arbitrary test `T`**. My first revision of
this paragraph called that `T`-relative comparison the open link, on the evidence
that `exact?` fails on the iso. **That was a one-shot query mistaken for a
measurement**: the comparison *decomposes*, and both steps are free —
`selfPullback_coverMap_left_iso` below is the two-line composite. So the
`T`-relative base change is **not** the residue either.

**What is genuinely left — CORRECTED 2026-07-30 (`ajc-p1`, `I-1438`), because the
version of this paragraph that stood here was wrong in both directions.** That
version said the residue was "transporting the `Gal`-**indexing** across
`pullbackSpecIso` and the `sigmaSpec` iso so that the two projections become the
identity and the `γ`-twist *as morphisms*", listed those two plus
`galoisSelfTensorEquiv` as the ingredients, and called the missing piece "the
*coherence* — that the coproduct's `γ`-component inclusion composed with the two
projections gives `id` and `γ` … a computation about specific morphisms".

**The coherence is free and needs NONE of those three.**
`Picard/GaloisDescent/PicEtGaloisBridge.lean` builds the `γ`-component as
`coverSelfSection T γ := pullback.lift (𝟙 _) (twistTest T γ)` — from the universal
property of the pullback and `twistTest_comp_coverMap` alone — and the two
identities this paragraph asked for *are* `pullback.lift_fst` and
`pullback.lift_snd`. No `pullbackSpecIso`, no `sigmaSpec`, no
`galoisSelfTensorEquiv` occurs in any proof term there. What a consumer needs is a
*section of the self-pullback*, not a transport of the `Gal`-indexing.

**And the two directions are not symmetric, which this paragraph did not
separate.** `invariant_of_projections_agree` derives `γ`-invariance from the
agreement hypothesis above **unconditionally** — arbitrary field, only
`[Algebra k k']`, no finiteness, separability or `IsGalois` — by one restriction
along that section. The *converse*, which is the direction `G1` needs, cannot be
functoriality at all: the two projections lie in the image of no single section, so
the `γ`-sections must **jointly cover** the self-pullback.
`projections_agree_of_invariant` carries exactly that as an explicit, undischarged
antecedent, and `exists_unique_descend_picEt_of_invariant` is this file's `∃!` with
`γ`-invariance in place of projection-agreement.

So what a lane closing this owes is a **covering** statement about the `Gal`-indexed
section family — a different kind of fact from a coherence identity — and that is
where `[IsGalois]` enters the route: by `galoisSelfTensorHom_bijective_iff_isGalois`
the splitting is *false* below the Galois level, so there the antecedent fails
rather than merely being unproved. `galoisSelfTensorEquiv` is the algebra input to
*that*, not to the coherence. §2's two tensor-inclusion lemmas are the **ring-level** input
to that computation and are explicitly *not* the computation itself (`I-1415`).

This file does not assume the bridge and does not weaken the invariance step to
something the splitting alone would make free.

**Where the `IsGalois` binder does and does not belong, since this was contested.**
`ajc-p1` established that `galoisSelfTensorHom` is bijective **iff**
`IsGalois k k'` — so at a merely finite separable level the splitting is not
unavailable, it is *false* — and inferred from this that a Galois binder is forced
on the invariance step. **That inference does not hold for the statements in this
file**, and the binder lists are the measurement: `isSheafFor_picEt_singleton_coverMap`
and `exists_unique_descend_picEt_of_projections` carry
`[Algebra.IsSeparable k k']` and `[Module.Finite k k']` and **no** `IsGalois`, and
`selfPullback_coverMap_left_iso` carries only `[Algebra k k']`. Nothing here is
normality-dependent, because étaleness of the cover — which is all the sheaf side
consumes — does not need normality.

So the two halves separate cleanly, and a lane pricing the step should not inherit
the stronger binder: **descent of `picEt`-classes along the cover works at any
finite separable level**; only the *translation* of `γ`-invariance into
projection-agreement needs `IsGalois`, and it needs it because the splitting is
false without it. The consequence for planning is that the Galois hypothesis enters
the route exactly once, at the bridge, and not at the descent.

Beyond that bridge, the scheme-level `G2` quotient is unchanged and untouched: it
is what turns descended *classes* into a representing *scheme*, and it is gated on
`AlgebraicJacobian.GaloisDescent.HasGaloisQuotient`, which has an instance only on
the affine locus while the object this route descends is glued.

**The summary that stood here contradicted the paragraph above it** and both
sentences were mine, in one docstring, about one object (`I-1412`): the body said
the `T`-relative base change "is **not** the residue either", and the summary
called it "**open**, and now the single link". The base change is landed
(`selfPullback_coverMap_left_iso`); it is the `Gal`-**indexing** that is open. A
reader planning from the summary would have re-derived a landed lemma.

So, corrected and stated once:

* the sheaf-theoretic side of the existence half — **closed** at one morphism and
  reduced to a two-projection check;
* the Galois splitting — **landed** (`ajc-p1`), with its two generator evaluations
  consumed here;
* the `T`-relative base change of the compatibility object — **landed** here;
* the `Gal`-**indexed** identification of that object — **the entry that this list
  got wrong, corrected 2026-07-30 (`ajc-p1`, `I-1438`)**. It read: "transporting the
  two ring identities through `Spec` and `sigmaSpec` so they become the cover's two
  *projections* — OPEN. Attempted this session and not landed: the composite sticks
  on `Scheme.Spec.map` versus `Spec.map` … Ring content done, categorical plumbing
  owed." That transport is **not needed**: `Picard/GaloisDescent/PicEtGaloisBridge.lean`
  gets the `γ`-component from `pullback.lift` and the two projection identities from
  `pullback.lift_fst`/`lift_snd`, with `sigmaSpec` and `pullbackSpecIso` absent from
  every proof term. So the plumbing this entry called owed was never on the route.
  What *is* open is one level up and is a different kind of statement: that the
  `Gal`-indexed **section family covers** the self-pullback (`hcov` there). The free
  half — projection-agreement ⟹ `γ`-invariance — is **landed** and unconditional.
* `k'`-side representability and the `G2` quotient — **open**, and not made cheaper
  by anything here.

**A pattern this file's history is evidence for, and the reason to distrust the
line above.** Every residue named on this step during one session turned out cheaper
than named — the splitting (closed within the hour), the `T`-relative base change
(two Mathlib lemmas), the morphism coherence as I first stated it (one `simp` each,
and on the wrong side of the equivalence). Three retractions in three commits. A
lane inheriting the item above should probe it before budgeting for it, and should
read `I-1402`: a failing `exact?` measures absence only when the goal is atomic.
-/

end PicScheme

end Scheme

end AlgebraicGeometry
