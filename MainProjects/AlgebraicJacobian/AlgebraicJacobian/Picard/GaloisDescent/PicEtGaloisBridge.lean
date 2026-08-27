/-
Copyright (c) 2026 Axel Delaval. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval
-/
import Mathlib
import AlgebraicJacobian.Picard.PicEtDescentExistence

/-!
# The Galois bridge: `γ`-invariance versus agreement of the cover's two projections

`AJC.picrep.etale-rep.invariance`.

## The gap this closes

`Picard/PicEtDescentExistence.lean` (`ajc-p2`) ends the sheaf-theoretic side of the
`picEt` field-descent step at `exists_unique_descend_picEt_of_projections`, whose
hypothesis is **agreement of the cover's two canonical projections**
`T_{k'} ×_T T_{k'} ⟶ T_{k'}`. Campaign `G1` produces something else: a class fixed
by the `Gal(k'/k)`-action. Its §4 names the remaining link as the *morphism-level
coherence* — that the `Gal`-indexed splitting's `γ`-component, composed with the two
projections, gives the identity and the `γ`-twist — and calls it "a computation about
specific morphisms, not a missing lemma".

This file is that computation, and it comes out asymmetric. **The direction the
route needs and the direction that is free are different directions**, so the two
are stated separately rather than as an `iff` with one hypothesis carried through
both halves.

## What is proved

* `twistTest` — the `γ`-twist of the base-changed test `T_{k'}`, as an endomorphism
  **in the slice over `Spec k`** (§1). **Its scheme-level ingredients are NOT new,
  and the first version of this line said they were** (`I-1455`, fresh-context
  audit, reproduced here): `twistLeft` and `specGal` are `rfl`-equal to
  `AlgebraicJacobian.GaloisDescent.pullbackGalMap … γ⁻¹` and `toSpecAut … γ⁻¹`
  (`Picard/FiniteGaloisQuotient.lean`), which also ships `pullbackGalMap_fst`/`_snd`
  — the content of `twistTest_comp_coverMap` — and the full
  `pullbackSemilinearGalAction`. That version's census was scoped to the directory
  `Picard/GaloisDescent/` and published as a claim about the project; the sought
  declaration was one directory up. What is genuinely this file's is the *slice*
  packaging and everything from §2 on.
* `coverSelfSection` — the `γ`-component section
  `T_{k'} ⟶ T_{k'} ×_T T_{k'}`, `⟨id, twist γ⟩` (§2). This is the coherence, and
  §2's two `simp` lemmas are its content: the section's composites with the two
  projections *are* `𝟙` and the `γ`-twist, by `pullback.lift_fst`/`lift_snd`.
* `invariant_of_projections_agree` (§3) — **projection agreement ⟹ `γ`-invariance,
  for every `γ`, unconditionally**. Arbitrary field `k`, arbitrary extension `k'/k`,
  arbitrary test `T`: no finiteness, no separability, no normality, no `IsGalois`.
* `projections_agree_of_invariant` (§4) — the converse, **as an implication with one
  explicitly named antecedent**: the `γ`-family must generate a *covering* sieve on
  the self-pullback. That antecedent is `hcov`, it is not discharged here, and §4
  says exactly what discharging it needs.
* `exists_unique_descend_picEt_of_invariant` (§5) — the composite a `G1` consumer
  calls: `γ`-invariance for every `γ`, plus `hcov`, gives the **unique** descended
  class. This is `ajc-p2`'s `∃!` with its hypothesis replaced by the one `G1`
  actually holds.

## Why the two directions are not symmetric, since this reprices the residue

The coherence identities are *equations between morphisms* and hold for any field
extension. What they buy in each direction is different:

* **Agreement ⟹ invariance** is pure functoriality: restrict the agreement along the
  section `⟨id, twist γ⟩`. One class, one section, no covering property. **Free.**
* **Invariance ⟹ agreement** cannot be functoriality, because the two projections are
  not in the image of any single section. It needs the `γ`-sections to *jointly* see
  all of `T_{k'} ×_T T_{k'}`, i.e. to generate a covering sieve — and *that* is where
  `IsGalois` enters, via `galoisSelfTensorEquiv` (`Picard/GaloisDescent/GaloisSelfTensor.lean`).

So the residue named in `PicEtDescentExistence.lean` §4 was **half free and half
mispriced**: the coherence itself is `pullback.lift_fst`, three lines, and it was
never the obstruction. The obstruction is a *covering* statement about the
`Gal`-indexed family, which is a different kind of fact — and `IsGalois` is needed
for it exactly as `ajc-p1`'s `galoisSelfTensorHom_bijective_iff_isGalois` predicts:
below the Galois level the family does not cover, because the splitting is false.

**Two of §4's three ingredients ARE needed — one level up.** The first version of
this paragraph, and `I-1438`, said the ingredient list (`pullbackSpecIso`,
`IsIso (sigmaSpec …)`, `galoisSelfTensorEquiv`) is needed for *none* of it. That is
true of the coherence and **false as a statement about the route**: §6's
`selfTensorSpecCoproduct` consumes `IsIso (sigmaSpec …)` and
`galoisSelfTensorEquiv`, and only `pullbackSpecIso` has no use here. A lane reading
the stronger form would delete `sigmaSpec` from its budget for the whole route and
then need it, so the overclaim ran in the expensive direction.

This does **not** rehabilitate §4's prescription, and its author declined that
reading when it was offered: those ingredients were prescribed *for the coherence*,
which is the obligation `pullback.lift` closes, and a prescription aimed at the
wrong obligation is wrong even when its ingredient list later matches a different
one. What is corrected here is only my own absolute, not their error.

## What this does NOT do

It closes no `sorry` in `Picard/FGAPicRepresentability.lean` and witnesses **no**
antecedent of `Scheme.fgaPicardRepresentability` for any curve: `k'`-side
representability is untouched, and `G2`'s scheme-level quotient is untouched. What it
changes is which hypothesis a `G1` consumer must supply — `γ`-invariance, which the
Galois action gives, rather than projection agreement, which it does not.

No hypothesis on `C(k)` anywhere (`I-0491`).

## Measurement discipline

`lake env lean` with **fresh** oleans for every probe; a stale-import environment
reports every probe as succeeding (`I-1057`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct

namespace AlgebraicGeometry

namespace Scheme

namespace PicScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-! ## §1. The `γ`-twist of a base-changed test -/

/-- `Spec γ : Spec k' ⟶ Spec k'`, the scheme map of a `k`-automorphism of `k'`. -/
noncomputable abbrev specGal (γ : k' ≃ₐ[k] k') :
    Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k') :=
  Spec.map (CommRingCat.ofHom (γ : k' →+* k'))

/-- **`Spec γ` is a morphism over `Spec k`.**

This is `γ.commutes` — that `γ` fixes `k` — transported through `Spec`. It is the
only place the `k`-algebra structure of `γ` (as opposed to its being a ring
automorphism) is consumed, and everything else in this file is formal. -/
theorem specGal_comp (γ : k' ≃ₐ[k] k') :
    specGal γ ≫ specMapAlgebra k k' = specMapAlgebra k k' := by
  rw [specMapAlgebra, ← Spec.map_comp]
  congr 1
  ext x
  exact γ.commutes x

/-- The `γ`-twist of `T ×_k Spec k'` on underlying schemes: the identity on the `T`
factor and `Spec γ` on the `Spec k'` factor.

Well defined because `Spec γ` is a morphism over `Spec k` (`specGal_comp`), so the
twisted pair still satisfies the pullback condition. -/
noncomputable def twistLeft (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    pullback T.hom (specMapAlgebra k k') ⟶ pullback T.hom (specMapAlgebra k k') :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ specGal γ) (by
    rw [Category.assoc, specGal_comp]
    exact pullback.condition)

/-- **The `γ`-twist as an endomorphism of the base-changed test, in the slice over
`Spec k`.**

This is the morphism a `γ`-invariance hypothesis is a statement about. **The
scheme-level twist already existed and an earlier revision of this docstring denied
it** (`I-1455`): `twistLeft` is `rfl`-equal to
`AlgebraicJacobian.GaloisDescent.pullbackGalMap k k' T.hom γ⁻¹`
(`Picard/FiniteGaloisQuotient.lean`, which also has the two projection identities
and the whole semilinear action). The denial was a census scoped to
`Picard/GaloisDescent/` reported as a fact about the project — literally true of the
directory, false of the tree, and exactly the trap that makes a lane rebuild a
landed construction. What this file adds is the **slice-over-`Spec k`** packaging,
which is what `picEt` consumes.

It is a slice morphism over `Spec k`, not over `Spec k'`: the twist moves the
`k'`-structure and is *not* `k'`-linear, which is exactly the semilinearity of the
Galois action, and is why the descent runs in the `k`-slice. -/
noncomputable def twistTest (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    (restrictTest k k').obj (baseTest (k' := k') T) ⟶
      (restrictTest k k').obj (baseTest (k' := k') T) :=
  Over.homMk (twistLeft T γ) (by
    change twistLeft T γ ≫ pullback.snd _ _ ≫ specMapAlgebra k k' = _
    rw [twistLeft, pullback.lift_snd_assoc, Category.assoc, specGal_comp]
    rfl)

/-- **The twist lives over `T`**: it commutes with the covering morphism.

This is what makes the twist a morphism of *descent data* rather than merely of
schemes, and it is `pullback.lift_fst` — the twist is the identity on the `T`
factor. -/
theorem twistTest_comp_coverMap (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    twistTest T γ ≫ coverMap (k' := k') T = coverMap (k' := k') T := by
  apply Over.OverMorphism.ext
  change twistLeft T γ ≫ pullback.fst _ _ = pullback.fst _ _
  exact pullback.lift_fst _ _ _

/-! ## §2. The `γ`-component section of the cover's self-pullback -/

/-- **THE COHERENCE, as a morphism**: the `γ`-component
`T_{k'} ⟶ T_{k'} ×_T T_{k'}`, namely `⟨𝟙, twist γ⟩`.

`PicEtDescentExistence.lean` §4 named the open link as "the `Gal`-coproduct's
`γ`-component inclusion composed with the two projections gives `id` and `γ`", with
the ingredients listed as `pullbackSpecIso`, `IsIso (sigmaSpec …)` and
`galoisSelfTensorEquiv`. **None of those three is needed for the coherence itself.**
The section exists by the universal property of the pullback, from
`twistTest_comp_coverMap` alone, and the two identities below are
`pullback.lift_fst` and `pullback.lift_snd`. The splitting is needed for something
else — see §4.

No hypothesis on `k'/k` beyond `[Algebra k k']`. -/
noncomputable def coverSelfSection (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    (restrictTest k k').obj (baseTest (k' := k') T) ⟶
      pullback (coverMap (k := k) (k' := k') T) (coverMap (k := k) (k' := k') T) :=
  pullback.lift (𝟙 _) (twistTest T γ) (by
    rw [Category.id_comp, twistTest_comp_coverMap])

/-- The `γ`-component composed with the **first** projection is the identity. -/
@[simp] theorem coverSelfSection_fst (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    coverSelfSection T γ ≫ pullback.fst (coverMap (k := k) (k' := k') T)
      (coverMap (k := k) (k' := k') T) = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The `γ`-component composed with the **second** projection is the `γ`-twist. -/
@[simp] theorem coverSelfSection_snd (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    coverSelfSection T γ ≫ pullback.snd (coverMap (k := k) (k' := k') T)
      (coverMap (k := k) (k' := k') T) = twistTest T γ :=
  pullback.lift_snd _ _ _

/-! ## §3. Agreement ⟹ invariance — free, and at full generality -/

/-- **The direction that is free: projection agreement gives `γ`-invariance, for
every `γ`.**

If a class `x` on `T_{k'}` has equal pullbacks along the two projections of
`T_{k'} ×_T T_{k'}`, then `x` is fixed by the `γ`-twist for every
`γ ∈ Gal(k'/k)` — hence `ajc-p2`'s hypothesis is *at least as strong as*
`γ`-invariance.

**Binder list is the measurement.** Arbitrary field `k`, arbitrary extension `k'/k`
with only `[Algebra k k']`, arbitrary test `T`, arbitrary smooth proper curve `C`:
**no** `[Module.Finite]`, **no** `[Algebra.IsSeparable]`, **no** `[IsGalois]`. So
this half of the bridge is not a Galois fact at all — which is why §4's converse,
which *does* need `IsGalois`, cannot be obtained by symmetry.

The proof is one restriction: apply `(picEt C).map (coverSelfSection T γ).op` to the
agreement and rewrite the two composites with §2. -/
theorem invariant_of_projections_agree (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k)))
    (x : (picEt C).obj (Opposite.op ((restrictTest k k').obj (baseTest (k' := k') T))))
    (h : (picEt C).map (pullback.fst (coverMap (k := k) (k' := k') T)
              (coverMap (k := k) (k' := k') T)).op x
        = (picEt C).map (pullback.snd (coverMap (k := k) (k' := k') T)
              (coverMap (k := k) (k' := k') T)).op x)
    (γ : k' ≃ₐ[k] k') :
    (picEt C).map (twistTest T γ).op x = x := by
  have := congrArg ((picEt C).map (coverSelfSection T γ).op) h
  simp only [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp,
    coverSelfSection_fst, coverSelfSection_snd] at this
  simpa using this.symm

/-! ## §4. Invariance ⟹ agreement — an implication, with its antecedent named -/

/-- **The direction the route needs, stated with its one antecedent explicit and
undischarged.**

If the `γ`-sections `⟨𝟙, twist γ⟩` generate a **covering** sieve on the
self-pullback `T_{k'} ×_T T_{k'}` (hypothesis `hcov`), then `γ`-invariance for every
`γ` implies agreement of the two projections — which is exactly what
`Picard/PicEtDescentExistence.lean`'s `∃!` consumes.

**`hcov` IS NOT DISCHARGED HERE and this theorem does not claim it is.** Naming it
as a hypothesis rather than proving it is the honest state: what it says is that the
`Gal`-indexed family of sections is jointly surjective and étale, i.e. that
`T_{k'} ×_T T_{k'}` is the `Gal`-indexed disjoint union of copies of `T_{k'}` with
the `γ`-component being `coverSelfSection T γ`. That is a *covering* statement, not
a coherence identity, and it is where `[IsGalois k k']` enters the route —
`ajc-p1`'s `galoisSelfTensorHom_bijective_iff_isGalois` shows the splitting
`k' ⊗_k k' ≅ ∏_{Gal} k'` is **false** at a merely finite separable level, so at such
a level `hcov` fails rather than being merely unproved.

**Why this is not a weaker restatement of the obligation.** The content is that
`hcov` is the *only* thing owed: `γ`-invariance plus a covering property gives
agreement, with no further input about `picEt`, the curve, or the classes. The
`picEt` side of the argument is one line — separatedness of the sheaf at `hcov`'s
sieve, from `isSheafFor_picEt_of_mem`, which holds at *every* covering sieve — and
the rest is §2's two identities.

**`hcov` is SATISFIABLE, but no exhibited model separates the two projections —
and the first version of this paragraph drew the wrong conclusion from the first
half.** `etaleTopology_generate_coverSelfSection_of_mono` (§6) exhibits `hcov` at
every extension whose `Spec` map is a monomorphism. That version then said "so this
implication is not conditioned on a false statement", implying content. **It does
not follow, and a fresh-context audit (`I-1454`) refuted the inference, reproduced
here as `specGal_eq_id_of_mono` and `twistTest_eq_id_of_mono`**: at `Mono` every
`γ` is forced to be the identity, so the `γ`-twist is the identity, `hinv` is
*also* free, and the two projections coincide — the conclusion holds there with
neither hypothesis. So the witness establishes satisfiability and **not**
non-vacuity in the sense that matters.

The honest statement is therefore: `hcov` is satisfiable; **no model in this file
has a nontrivial automorphism**, hence none separates the two projections; and
exhibiting `hcov` — or merely projection *in*equality — at one extension with a
nontrivial automorphism is open, alongside `hcov` at a genuine Galois level. -/
theorem projections_agree_of_invariant (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k)))
    (hcov : Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      etaleTopologyOver k (pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)))
    (x : (picEt C).obj (Opposite.op ((restrictTest k k').obj (baseTest (k' := k') T))))
    (hinv : ∀ γ : k' ≃ₐ[k] k', (picEt C).map (twistTest T γ).op x = x) :
    (picEt C).map (pullback.fst (coverMap (k := k) (k' := k') T)
          (coverMap (k := k) (k' := k') T)).op x
      = (picEt C).map (pullback.snd (coverMap (k := k) (k' := k') T)
          (coverMap (k := k) (k' := k') T)).op x := by
  refine (isSheafFor_picEt_of_mem C _ hcov).isSeparatedFor.ext ?_
  rintro W f ⟨Z, a, b, hb, rfl⟩
  cases hb with | mk γ =>
  simp only [op_comp, Functor.map_comp, CategoryTheory.comp_apply]
  congr 1
  simp only [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp,
    coverSelfSection_fst, coverSelfSection_snd]
  simp [hinv γ]

/-! ## §5. The form a `G1` consumer calls -/

section Cover

variable [Algebra.IsSeparable k k'] [Module.Finite k k']

/-- **The descent step with `γ`-invariance as its hypothesis.**

`ajc-p2`'s `exists_unique_descend_picEt_of_projections` composed with §4: a
`γ`-invariant class on `T_{k'}` descends to a **unique** class on `T`, given `hcov`.

This is the statement campaign `G1` should aim at, and the reason it could not be
stated before is that nothing turned invariance into projection agreement. What
remains owed is `hcov` and **only** `hcov` — named in §4, not restated more cheaply
here.

`[Algebra.IsSeparable]` and `[Module.Finite]` re-enter only because
`exists_unique_descend_picEt_of_projections` needs them: they are what makes
`Spec k' ⟶ Spec k` a *covering* in the étale topology. Neither §3 nor §4 uses
them. -/
theorem exists_unique_descend_picEt_of_invariant (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k)))
    (hcov : Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      etaleTopologyOver k (pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)))
    (x : (picEt C).obj (Opposite.op ((restrictTest k k').obj (baseTest (k' := k') T))))
    (hinv : ∀ γ : k' ≃ₐ[k] k', (picEt C).map (twistTest T γ).op x = x) :
    ∃! y : (picEt C).obj (Opposite.op T),
      (picEt C).map (coverMap (k' := k') T).op y = x :=
  exists_unique_descend_picEt_of_projections (k' := k') C T x
    (projections_agree_of_invariant C T hcov x hinv)

end Cover

/-! ## §6. `hcov` is satisfiable — and the witness site is degenerate

§4's antecedent `hcov` is a hypothesis on the `Gal`-indexed section family. A file
that leaves an antecedent open owes a demonstration that the antecedent is not
*false*. That demonstration is below, as declarations rather than as a docstring
sentence, and what makes the family cover is not "`k' = k`" but **`Spec (k'/k)`
being a monomorphism** — at such an extension the `γ = 1` section is literally the
diagonal, an isomorphism because `coverMap` is then mono.

**And the demonstration is weaker than what §4's implication needs, which the first
version of this section claimed it established.** A fresh-context audit
(`I-1454`, `I-1456`) showed the witness site *also* makes the hypothesis `hinv` and
the consequent free — `specGal_eq_id_of_mono` and `twistTest_eq_id_of_mono`, both
landed above — so it proves satisfiability and not content. The transferable rule,
one turn of the screw past `I-1413`: landing the non-vacuity witness as a
declaration audits the *antecedent*; whether the implication has content is a
question about the **consequent at the witness site**, and nothing in a sorry sweep,
axiom check, or satisfiability witness asks it.

What remains genuinely open on this row is therefore two things, not one: `hcov` at
a nontrivial Galois level, and — strictly weaker, and the right first target —
`hcov` or mere projection *inequality* at any extension with a nontrivial
automorphism. -/

/-- `Spec` of the identity extension is the identity morphism. -/
theorem specMapAlgebra_self : specMapAlgebra k k = 𝟙 _ := by
  rw [specMapAlgebra]
  have h : (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (CommRingCat.of k) := by
    ext x; rfl
  rw [h, Spec.map_id]

/-- `Spec 1 = 𝟙`: the trivial automorphism twists nothing. -/
theorem specGal_one : specGal (1 : k' ≃ₐ[k] k') = 𝟙 _ := by
  rw [specGal]
  have h : (CommRingCat.ofHom ((1 : k' ≃ₐ[k] k') : k' →+* k')) = 𝟙 (CommRingCat.of k') := by
    ext x; rfl
  rw [h, Spec.map_id]

/-- The `γ = 1` twist is the identity endomorphism of `T_{k'}`. -/
theorem twistTest_one (T : Over (Spec (CommRingCat.of k))) :
    twistTest (k' := k') T 1 = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change twistLeft T (1 : k' ≃ₐ[k] k') = _
  rw [twistLeft]
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst]
    change _ = 𝟙 _ ≫ _
    rw [Category.id_comp]
  · rw [pullback.lift_snd, specGal_one, Category.comp_id]
    change _ = 𝟙 _ ≫ _
    rw [Category.id_comp]

/-- **The `γ = 1` component of the section family IS the diagonal of the cover.**

Immediate from `twistTest_one` and the two projection identities, and it is what
makes the non-vacuity witness below a two-line argument instead of a computation:
`pullback.diagonal` of a *mono* is an isomorphism by a Mathlib instance. -/
theorem coverSelfSection_one (T : Over (Spec (CommRingCat.of k))) :
    coverSelfSection (k' := k') T 1 = pullback.diagonal (coverMap (k' := k') T) := by
  rw [coverSelfSection]
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst, pullback.diagonal_fst]
  · rw [pullback.lift_snd, pullback.diagonal_snd, twistTest_one]

/-- The cover morphism is a monomorphism whenever `Spec (k'/k)` is — base change of
a mono, reflected into the slice by `Over.forget`. -/
instance mono_coverMap_of_mono [Mono (specMapAlgebra k k')]
    (T : Over (Spec (CommRingCat.of k))) : Mono (coverMap (k := k) (k' := k') T) := by
  have h : Mono ((Over.forget (Spec (CommRingCat.of k))).map
      (coverMap (k := k) (k' := k') T)) := by
    change Mono (coverMap (k := k) (k' := k') T).left
    rw [coverMap_left]
    exact pullback.fst_of_mono
  exact Functor.mono_of_mono_map _ h

/-- **`Spec (k' ⊗_k k')` IS the `Gal`-indexed coproduct of copies of `Spec k'`** —
the scheme-level form of `ajc-p1`'s splitting, and the first thing `hcov` needs.

`galoisSelfTensorEquiv` is an algebra statement; this is it read through `Spec`,
composed with `sigmaSpec` being an isomorphism at a *finite* index set. Both halves
are library: `RingEquiv.toCommRingCatIso` turns the splitting into a `CommRingCat`
iso (an earlier revision here hand-built that iso with four field proofs — it is one
mathlib call, and `PicEtDescentExistence.lean` §4's own ingredient list named
`IsIso (sigmaSpec …)`, which *is* needed for this, unlike for §2's coherence).

**`[IsGalois k k']` is load-bearing here and only here in this file.** By
`galoisSelfTensorHom_bijective_iff_isGalois` the splitting is *false* at a merely
finite separable level, so this iso does not exist there — which is the precise
sense in which `hcov` fails rather than being unproved below the Galois level.

**What this does NOT yet give**, stated so the gap is not read as closed: `hcov` is
about the self-pullback of `coverMap` over an arbitrary test `T`, i.e. this object
*base-changed along* `T_{k'} ⟶ Spec k'`, and it needs the coproduct's `γ`-component
to be identified with `coverSelfSection T γ`. This iso is the input to that
identification, not the identification. -/
noncomputable def selfTensorSpecCoproduct (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [FiniteDimensional k k'] [IsGalois k k'] :
    (∐ fun _ : (k' ≃ₐ[k] k') => Spec (CommRingCat.of k')) ≅
      Spec (CommRingCat.of (k' ⊗[k] k')) :=
  (asIso (AlgebraicGeometry.sigmaSpec (fun _ : (k' ≃ₐ[k] k') => CommRingCat.of k'))) ≪≫
    Scheme.Spec.mapIso
      ((RingEquiv.toCommRingCatIso
        (AlgebraicJacobian.GaloisDescent.galoisSelfTensorEquiv k k').toRingEquiv).op)

/-- **`hcov` is a SCHEME-level covering statement — the reduction, free.**

The slice topology `etaleTopologyOver k` is `Scheme.etaleTopology.over (Spec k)`, so
membership is by definition membership of the transported sieve on the underlying
scheme (`GrothendieckTopology.mem_over_iff`). Recorded because it says where the
remaining obligation lives: `hcov` is not a statement about the slice, the test `T`,
or `picEt` at all — it is that the `Gal`-indexed family of *scheme* morphisms
`(coverSelfSection T γ).left` is an étale covering of `(T_{k'} ×_T T_{k'}).left`.

**What is measured about that obligation**: `infer_instance` for
`IsOpenImmersion (coverSelfSection T γ).left` **fails** at a finite Galois `k'/k`
(control in the same probe: `#print axioms fgaPicardRepresentability` reports
`sorryAx`, so the environment is live and the failure is not a stale-import
artefact, `I-1057`).

**But the conclusion the first version of this docstring drew from that — "the
covering property is not available from the étale-precoverage machinery for free,
and closing this row means building it" — OVER-PRICES the residue, and is corrected
here** (`I-1458`, `ajc-p2`, measured). The obligation splits in two and only one
half is owed:

* the **topology** half is free: for any `OpenCover`, the generated sieve is an
  étale covering sieve in one line
  (`zariskiTopology_le_etaleTopology` ∘ `Cover.mem_grothendieckTopology`), so no
  étale-site work sits between "the `γ`-sections are an open cover" and `hcov`;
* the **open-immersion** half is genuinely owed — but a failed `infer_instance` is
  not absence: `IsOpenImmersion (Sigma.ι …)` is a *theorem*
  (`(sigmaOpenCover _).map_prop`) on which `inferInstance` also fails, and by §6's
  `selfTensorSpecCoproduct` the object here *is* a `Gal`-indexed coproduct, where
  that theorem applies.

**THE SECOND BULLET AND THE PARAGRAPH BELOW IT ARE WITHDRAWN — the
morphism-property half is FREE, and `IsOpenImmersion` is not what the site
asks for** (`pic-a`, 2026-07-30, landed as
`Picard/GaloisDescent/PicEtGaloisCover.lean`'s `etale_coverSelfSection_left`,
`sorry`-free and axiom-clean). The étale precoverage criterion
(`Scheme.ofArrows_mem_precoverage_iff`) asks for `Etale` of each member, **not**
`IsOpenImmersion`. And the
cheap route is post-composition cancellation: `coverSelfSection T γ` is a
*section* of `pullback.fst` (`coverSelfSection_fst`), `Etale` carries
`MorphismProperty.HasOfPostcompProperty @Etale`, and `Over.forget` sends this
slice pullback to a *scheme* pullback (pullback is a connected shape, so
`PreservesLimitsOfShape` is an instance) — which is the step no site here had
used, and it is what makes `(pullback.fst _ _).left` a base change of
`(coverMap T).left`. So `selfTensorSpecCoproduct`, `sigmaSpec` and `[IsGalois]`
are **all absent** from that file, and nothing about the coproduct is needed for
this half.

**The bullet above is withdrawn for its CONCLUSION, not for its content, and an
earlier revision of this correction got that backwards** (`I-1510`, `I-1513`,
fresh-context audit). It said `IsOpenImmersion` is "strictly stronger than the
site needs, which is exactly why `inferInstance` fails on it and succeeds on the
cheap route". **Both clauses were false**: `inferInstance` fails on the `Etale`
goal too, and `IsOpenImmersion` is *equivalent* here — it is now landed as
`isOpenImmersion_coverSelfSection_left`, proved **from**
`etale_coverSelfSection_left` via `mono_of_mono_fac` and
`IsOpenImmersion.of_flat_of_mono`. So the prescription this bullet gave was
**less direct, not more expensive**, and its target is a corollary of the cheap
route.

**What is actually owed, all of it**: joint surjectivity of the `γ`-sections on
points of `(T_{k'} ×_T T_{k'}).left`. `hcov_of_jointlySurjective` derives `hcov`
from that alone — one statement about points, with no sieve, no morphism
property, no `picEt` and no slice in it. Aim there, and read that file's route
note before budgeting it — but read it for what it says: the *library* links
(`pullbackSpecIso`, `FinitaryPreExtensive` by synthesis, a `Sigma.reindex` for
the `Type 0` vs `Type u` index) are probed to exist, while the two
content-bearing steps — base change along `T_{k'} ⟶ Spec k'`, and matching the
coproduct's `γ`-component to `coverSelfSection T γ` — are **still owed**, and
they are the two this bullet named. -/
theorem hcov_iff_scheme_level (T : Over (Spec (CommRingCat.of k))) :
    Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      etaleTopologyOver k (pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T))
    ↔ Sieve.overEquiv _ (Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)))
      ∈ Scheme.etaleTopology (pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).left :=
  GrothendieckTopology.mem_over_iff _ _

/-- **The `Mono` witness site is DEGENERATE: it forces every `γ` to be the
identity.** Reproduced from a fresh-context audit of this file (`I-1454`).

If `Spec (k'/k)` is a monomorphism then `specGal_comp` plus `cancel_mono` collapse
every `γ ∈ Gal(k'/k)` to `𝟙`. So the "`Gal`-indexed family" at the only site where
this file exhibits `hcov` is a single constant arrow. -/
theorem specGal_eq_id_of_mono [Mono (specMapAlgebra k k')] (γ : k' ≃ₐ[k] k') :
    specGal γ = 𝟙 _ := by
  have h : specGal γ ≫ specMapAlgebra k k' = 𝟙 _ ≫ specMapAlgebra k k' := by
    rw [Category.id_comp, specGal_comp]
  exact (cancel_mono (specMapAlgebra k k')).mp h

/-- **Hence `hinv` is ALSO free at the witness site** — which is why exhibiting
`hcov` there does not show §4's implication has content.

The `γ`-twist is the identity, so `(picEt C).map (twistTest T γ).op x = x` holds for
every class `x` with no hypothesis at all. Landed as a theorem rather than left as
the prose remark the audit refuted (`I-1454`, `I-1456`): a satisfiable antecedent is
not a non-vacuous implication, and the check that separates them is whether the
witness site also makes the *consequent* free. Here it does. -/
theorem twistTest_eq_id_of_mono [Mono (specMapAlgebra k k')]
    (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    twistTest (k' := k') T γ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change twistLeft T γ = _
  rw [twistLeft]
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst]
    change _ = 𝟙 _ ≫ _
    rw [Category.id_comp]
  · rw [pullback.lift_snd, specGal_eq_id_of_mono, Category.comp_id]
    change _ = 𝟙 _ ≫ _
    rw [Category.id_comp]

/-- **`hcov` IS SATISFIABLE**: at any extension whose `Spec` map is a
monomorphism — `k' = k` in particular, by `specMapAlgebra_self` — the
`Gal`-indexed section family generates `⊤`, hence a covering sieve.

**This is satisfiability and NOT non-vacuity**, and the two declarations above are
why: at this very site every `γ` is the identity, so `hinv` is free too and the two
projections coincide. `hcov` — or merely projection *in*equality — at an extension
with a nontrivial automorphism is open.

So `projections_agree_of_invariant` and
`exists_unique_descend_picEt_of_invariant` are implications with a *satisfiable*
antecedent, and neither is vacuously true. The proof: `coverSelfSection T 1` is the
diagonal (`coverSelfSection_one`), the diagonal of a mono is an isomorphism, and a
sieve containing an isomorphism is `⊤`.

**What this does NOT witness, stated because it is the whole open obligation**: at a
nontrivial Galois extension `Spec (k'/k)` is *not* mono, so this witness says
nothing there, and `hcov` at such a level is exactly what remains owed. The point of
proving it here is that the §4 implication has content, not that the route is
finished. -/
theorem etaleTopology_generate_coverSelfSection_of_mono [Mono (specMapAlgebra k k')]
    (T : Over (Spec (CommRingCat.of k))) :
    Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      etaleTopologyOver k (pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)) := by
  have hiso : IsIso (coverSelfSection (k' := k') T 1) := by
    rw [coverSelfSection_one]; infer_instance
  have htop : Sieve.generate (Presieve.ofArrows
      (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
      (fun γ => coverSelfSection T γ)) = ⊤ :=
    Sieve.id_mem_iff_eq_top.mp ⟨_, inv (coverSelfSection (k' := k') T 1),
      coverSelfSection T 1, Presieve.ofArrows.mk 1, by simp⟩
  rw [htop]
  exact GrothendieckTopology.top_mem _ _

end PicScheme

end Scheme

end AlgebraicGeometry
