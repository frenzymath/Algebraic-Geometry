/-
Copyright (c) 2026 Axel Delaval. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval
-/
import Mathlib
import AlgebraicJacobian.Picard.PicEtDescentExistence
import AlgebraicJacobian.Picard.PicEtQuotientHom
import AlgebraicJacobian.Picard.GaloisDescent.PicEtGaloisBridge

/-!
# The descent ASSEMBLY: a `k`-representation of `picEt C` from cover-compatible classes

`AJC.picrep.etale-rep.descent-assembly`.

## What this file is, and what it is not

Four lanes have been filling **antecedents** of the `picEt` field-descent step, and
for four rounds nothing stated the theorem they are antecedents *of*. Three sites
measured that absence independently: `Picard/FGAPicRepresentability.lean`'s
four-input paragraph ("There is **still** no declaration anywhere in this project
stating the theorem they are antecedents *of*"), `I-1312`, and
`Picard/PicEtDescentAssembly.lean`'s own §4. That is the recorded
*scoreboard-of-antecedents-has-no-goal* shape, at the exact seam that named it.

This file writes the consumer. `representableBy_of_coverCompatibleEquiv` takes data
**over the cover** and concludes a `RepresentableBy` **over `k`** — so it crosses
the descent step rather than restating one side of it, which is what
`representableByRestrict_of_baseChange` was refuted for doing (`I-1312`).

**It closes no `sorry` and witnesses no antecedent of
`Scheme.fgaPicardRepresentability` for any curve.** `Y` and the `Equiv` family are
hypotheses; `hcov` is undischarged above the monomorphism level. What changes is
that `ajc-p1`'s invariance bridge and `ajc-p4`'s Hom side now have a stated
consumer, so their outputs are *checkably composable* instead of believed to be.

## The three things measured here rather than asserted

**1. The cover is Mathlib's, and `coverMap` is an adjunction counit.** `T ↦ T_{k'}`
is `Over.pullback (specMapAlgebra k k') ⋙ Over.map (specMapAlgebra k k')`, and
`coverMap_eq_counit` proves (by `simp`) that `PicEtDescentAssembly.lean`'s hand-built
`coverMap` **is** the counit of `Over.map ⊣ Over.pullback`. Consequences: the cover
is functorial for free, the cover square is counit naturality
(`coverFunctor_map_comp_coverMap`), and `coverRestrictNat` is
`whiskerRight (NatTrans.op counit) (picEt C)` rather than a hand-built
`NatTrans`. A lane extending the cover should take its functoriality from there.

**2. The invariance bridge needs no finiteness or separability — on EITHER side.**
`isGalInvariant_of_isCoverCompatible` and `isCoverCompatible_of_isGalInvariant`
both carry `omit [Algebra.IsSeparable k k'] [Module.Finite k k']`, linter-confirmed,
and a fresh-context audit strengthened this: both, *and*
`coverCompatibleEquivGalInvariant`, re-elaborate in a section with neither binder in
scope at all.

**The global census that stood here is FALSE and is withdrawn** (`I-1470`). It said
those binders are consumed in this cluster at exactly *one* place, covering-sieve
membership. `selfTensorSpecCoproduct` (`GaloisDescent/PicEtGaloisBridge.lean`) is a
second, load-bearing site: `FiniteDimensional k k'` **is** `Module.Finite k k'` by
`rfl`, dropping it gives two synthesis failures, and `[IsGalois k k']` does not
supply it. A name-level grep misses this because the alias is spelled differently —
which is exactly why an "exactly one place" claim needs a census and this one did not
have one. It is a second site *on the route this file's own §`hcov` paragraph
prices*. What survives is the local fact, which is all the bridge needs: **the
invariance correspondence itself is free of both binders**.

**3. The assembly is a CHANGE OF COORDINATES, not a strengthening**, and that is
recorded as a theorem (`coverCompatibleEquiv_of_representableBy`) rather than as a
hedge. A representation of `picEt C` yields back exactly the data the assembly
consumes, naturality included, so the two are inter-derivable. The honest reading:
*to represent `picEt C` it is equivalent to represent the cover-compatible-classes
functor.* That is a real repricing — the right-hand side is what a Galois quotient
of a `k'`-side representation produces — but it is **not** a discount on the seam.

**And the coordinates are GENERIC, which is the sentence a lane deciding whether to
build on this file needs** (`I-1471`, fresh-context audit; the paragraph above was
true and left this implicit). Both `representableBy_of_coverCompatibleEquiv` and its
converse were re-derived with `Scheme`, `Field`, `Algebra`, `picEt`, the cover and
the descent **all deleted** — an arbitrary category, an arbitrary presheaf, an
arbitrary per-object `Equiv` family — closing on `[propext, Quot.sound]`. The bodies
are `Equiv.trans`, `Equiv.apply_symm_apply` and `rep.homEquiv_comp`. So **no
geometry lives in the two assembly theorems**: substitute any per-test equiv family
and the same statement holds. All the geometry is in the *input*
`restrictCompatEquiv`, which is genuine descent (`PicEtDescentExistence.lean`'s `∃!`
at the covering sieve). Budget accordingly: the assembly is plumbing that was
missing, not a theorem about curves.

## What is still owed, named at the declaration and not restated more cheaply

* the `Equiv` family itself, from a `k'`-side representation and its Galois
  quotient — `ajc-p4`'s `homClassMap_of_galoisQuotient` is its injective half, and
  the scheme-level quotient (`G2(c)`, non-affine) is `ajc-p3`'s row;
* `hcov`, `ajc-p1`'s covering antecedent, carried per-test by
  `representableBy_of_galInvariantEquiv`. It is **satisfiable** — at every extension
  with `Mono (specMapAlgebra k k')`, by
  `etaleTopology_generate_coverSelfSection_of_mono` — and the sentence that stood
  here, *"hence not vacuous"*, is **WITHDRAWN as a non-sequitur** (`I-1454`,
  fresh-context audit of `PicEtGaloisBridge.lean`; the inference was inherited from
  that file and repeated here). `Mono (specMapAlgebra k k')` forces every
  `γ : k' ≃ₐ[k] k'` to be the identity — reproduced in a scratch probe (since
  deleted) from `GaloisDescent/PicEtGaloisBridge.lean`'s `specGal_comp` and
  `cancel_mono`, before this paragraph was changed. The first revision of this
  sentence said "reproduced **here**", which reads as *in this file* and is false:
  neither name occurs below, and both live two files away (`I-1471`) — so at the
  only exhibited model
  the group is trivial, `twistTest T γ` is the identity, the two projections of the
  cover coincide, and the *consequent* holds with neither `hcov` nor invariance. A
  satisfiable antecedent whose only witness also trivialises the conclusion
  establishes satisfiability and **not** content. The honest wording, which is what
  a lane should budget against: *satisfiable, but no exhibited model separates the
  two projections*, and exhibiting one at an extension with a nontrivial
  automorphism (`ℂ/ℝ`, `𝔽_{p²}/𝔽_p`) is open;
* `k'`-side representability itself — the campaign's undischarged output.

**No hypothesis on `C(k)`** (`I-0491`).
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

namespace PicScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-- The cover as an ENDOFUNCTOR of `k`-tests: `T ↦ T_{k'}`, read back as a `k`-test.
Mathlib's `Over.pullback` followed by `restrictTest = Over.map`. -/
noncomputable abbrev coverFunctor :
    Over (Spec (CommRingCat.of k)) ⥤ Over (Spec (CommRingCat.of k)) :=
  Over.pullback (specMapAlgebra k k') ⋙ restrictTest k k'

theorem coverFunctor_obj (T : Over (Spec (CommRingCat.of k))) :
    (coverFunctor (k := k) (k' := k')).obj T
      = (restrictTest k k').obj (baseTest (k' := k') T) := rfl

/-- `coverMap` is the COUNIT of `Over.map ⊣ Over.pullback`. -/
theorem coverMap_eq_counit (T : Over (Spec (CommRingCat.of k))) :
    coverMap (k' := k') T
      = (Over.mapPullbackAdj (specMapAlgebra k k')).counit.app T := by
  apply Over.OverMorphism.ext
  change pullback.fst T.hom (specMapAlgebra k k') = _
  simp

theorem coverFunctor_map_comp_coverMap {T T' : Over (Spec (CommRingCat.of k))}
    (f : T ⟶ T') :
    (coverFunctor (k := k) (k' := k')).map f ≫ coverMap (k' := k') T'
      = coverMap (k' := k') T ≫ f := by
  rw [coverMap_eq_counit, coverMap_eq_counit]
  exact (Over.mapPullbackAdj (specMapAlgebra k k')).counit.naturality f

/-- A class on `T_{k'}` whose two pullbacks to the self-intersection of the cover agree. -/
def IsCoverCompatible (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k)))
    (x : (picEt C).obj (op ((coverFunctor (k := k) (k' := k')).obj T))) : Prop :=
  (picEt C).map (pullback.fst (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).op x
    = (picEt C).map (pullback.snd (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).op x

/-- The cover-compatible classes on `T_{k'}`. -/
def CoverCompatible (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k))) : Type (u + 1) :=
  {x : (picEt C).obj (op ((coverFunctor (k := k) (k' := k')).obj T)) //
    IsCoverCompatible (k' := k') C T x}

section Descend

variable [Algebra.IsSeparable k k'] [Module.Finite k k']

omit [Algebra.IsSeparable k k'] [Module.Finite k k'] in
theorem isCoverCompatible_restrict (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k))) (y : (picEt C).obj (op T)) :
    IsCoverCompatible (k' := k') C T ((picEt C).map (coverMap (k' := k') T).op y) := by
  change (picEt C).map _ ((picEt C).map _ y) = (picEt C).map _ ((picEt C).map _ y)
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp, ← op_comp, ← op_comp, pullback.condition]

/-- Restriction along the cover, as a map into the cover-compatible classes. -/
noncomputable def restrictCompat (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k))) (y : (picEt C).obj (op T)) :
    CoverCompatible (k' := k') C T :=
  ⟨(picEt C).map (coverMap (k' := k') T).op y, isCoverCompatible_restrict C T y⟩

theorem restrictCompat_bijective (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k))) :
    Function.Bijective (restrictCompat (k' := k') C T) := by
  constructor
  · intro a b hab
    exact picEt_injective_restrict_baseTest (k' := k') C T (congrArg Subtype.val hab)
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, -⟩ := exists_unique_descend_picEt_of_projections (k' := k') C T x hx
    exact ⟨y, Subtype.ext hy⟩

/-- **The descent equivalence**: classes on `T` are exactly the cover-compatible
classes on `T_{k'}`. -/
noncomputable def restrictCompatEquiv (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k))) :
    (picEt C).obj (op T) ≃ CoverCompatible (k' := k') C T :=
  Equiv.ofBijective _ (restrictCompat_bijective (k' := k') C T)

@[simp]
theorem restrictCompatEquiv_apply (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k))) (y : (picEt C).obj (op T)) :
    ((restrictCompatEquiv (k' := k') C T) y).1
      = (picEt C).map (coverMap (k' := k') T).op y := rfl

/-- **Restriction along the cover as a NATURAL TRANSFORMATION** `picEt C ⟶ coverᵒᵖ ⋙ picEt C`.

Naturality is the counit square of `Over.map ⊣ Over.pullback`, opposed. -/
noncomputable def coverRestrictNat (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    picEt C ⟶ (coverFunctor (k := k) (k' := k')).op ⋙ picEt C :=
  Functor.whiskerRight
    (NatTrans.op (Over.mapPullbackAdj (specMapAlgebra k k')).counit) (picEt C)

omit [Algebra.IsSeparable k k'] [Module.Finite k k'] in
@[simp]
theorem coverRestrictNat_app (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k))) (y : (picEt C).obj (op T)) :
    (coverRestrictNat (k' := k') C).app (op T) y
      = (picEt C).map (coverMap (k' := k') T).op y := by
  change (picEt C).map ((Over.mapPullbackAdj (specMapAlgebra k k')).counit.app T).op y = _
  rw [coverMap_eq_counit]
  rfl

/-- The descent equivalence is NATURAL in the test: its underlying map is the
component of `coverRestrictNat`. -/
theorem restrictCompatEquiv_naturality (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {T T' : Over (Spec (CommRingCat.of k))} (f : T ⟶ T')
    (y : (picEt C).obj (op T')) :
    ((restrictCompatEquiv (k' := k') C T) ((picEt C).map f.op y)).1
      = ((coverFunctor (k := k) (k' := k')).op ⋙ picEt C).map f.op
          ((restrictCompatEquiv (k' := k') C T') y).1 := by
  rw [restrictCompatEquiv_apply, restrictCompatEquiv_apply,
    ← coverRestrictNat_app (k' := k') C T, ← coverRestrictNat_app (k' := k') C T']
  exact NatTrans.naturality_apply (coverRestrictNat (k' := k') C) f.op y

/-! ## What `hcov` costs — the topology half is one line -/

omit [Algebra.IsSeparable k k'] [Module.Finite k k'] in
/-- **An open cover's sieve is an ÉTALE covering sieve** — one line, and it reprices
`ajc-p1`'s `hcov`.

`PicEtGaloisBridge.lean`'s `hcov_iff_scheme_level` reduces `hcov` to a covering
statement about the scheme morphisms `(coverSelfSection T γ).left`, and its docstring
records — correctly, with a live `sorryAx` control — that
`IsOpenImmersion (coverSelfSection T γ).left` does **not** synthesise, concluding
"the covering property is not available from the étale-precoverage machinery for
free, and closing this row means building it".

**The second clause needs splitting, and this lemma is the reason.** What IS free,
once one has an `OpenCover`, is everything topological:
`Cover.mem_grothendieckTopology` plus `zariskiTopology_le_etaleTopology`. So `hcov`
is **not** a topology obligation at all; it is exactly the geometric statement *the
`Gal`-indexed sections are an open cover of the self-pullback*, and no étale-site
work sits between that and `hcov`.

**How many geometric facts that is: TWO, not one** (`I-1473`, fresh-context audit
correcting the first revision of this paragraph, which said "what is not free is
*that the sections are open immersions*" — one of the two). `Scheme.OpenCover` is
`Cover (precoverage @IsOpenImmersion)` and `Scheme.precoverage P` is
`jointlySurjectivePrecoverage ⊓ P.precoverage`, so an `OpenCover` bundles **joint
surjectivity** as well as the property. The second fact is that the `γ`-sections are
*jointly surjective* onto the self-pullback — which is the "self-pullback IS the
`Gal`-indexed disjoint union" content, i.e. the substance of the covering claim
rather than a side condition. Intended-failure control fired: with only the
open-immersion half in hand, `exact?` cannot close the `etaleTopology` goal.

**And the same audit sharpened the win in the other direction**: given *both* halves
at the level of underlying schemes, all of `hcov` closes axiom-clean via one further
`rw [Sieve.overEquiv_ofArrows]`.

**The sentence that stood here — "so the residue is exactly two named facts about
the morphisms `(coverSelfSection T γ).left`" — is FALSE and is replaced rather
than appended to** (`pic-a`, 2026-07-30; the append form was itself an audit
finding, since it left the false count three lines above its own correction).
Both of those facts are now **theorems**, in
`Picard/GaloisDescent/PicEtGaloisCover.lean`, `sorry`-free and axiom-clean with
no `[IsGalois]` and no coproduct input:

* `etale_coverSelfSection_left` — the étale one, which is what the site's
  criterion (`Scheme.ofArrows_mem_precoverage_iff`) actually asks for; `Etale` of
  a section is one post-composition cancellation
  (`MorphismProperty.HasOfPostcompProperty @Etale`);
* `isOpenImmersion_coverSelfSection_left` — the open-immersion one, **derived
  from** the étale one via `mono_of_mono_fac` and
  `IsOpenImmersion.of_flat_of_mono`. So the two are *equivalent* here, not
  ordered by strength; an earlier revision of this correction wrote "strictly
  stronger" and that is withdrawn (`I-1510`).

So `hcov_of_jointlySurjective` reduces `hcov` to **joint surjectivity on points
alone**, and that single point-level statement is the whole residue.

Two further measurements, both with `fgaPicardRepresentability` firing `sorryAx` in
the same probe file (`I-1057`):

* `IsOpenImmersion (Sigma.ι g i)` fails by `inferInstance` **but is a theorem**:
  `(sigmaOpenCover g).map_prop i` closes it. So a failed synthesis on a coproduct
  inclusion is not evidence of absence (`I-1402`, at an instance goal rather than a
  tactic).
* consequently, on `ajc-p1`'s route through `selfTensorSpecCoproduct`, the step from
  "the self-pullback IS the `Gal`-indexed coproduct" to `hcov` is library work:
  a coproduct in `Scheme` carries `sigmaOpenCover`, and this lemma converts it.

**What this does NOT do**: it does not prove `hcov`. The base change of
`selfTensorSpecCoproduct` along `T_{k'} ⟶ Spec k'` and the identification of its
`γ`-component with `coverSelfSection T γ` are still owed, and they are where the
work is. This lemma removes the *last* step from that list, not the first. -/
theorem etaleTopology_generate_of_openCover {X : Scheme.{u}} (U : X.OpenCover) :
    Sieve.generate (Presieve.ofArrows U.X U.f) ∈ Scheme.etaleTopology X :=
  Scheme.zariskiTopology_le_etaleTopology _ U.mem_grothendieckTopology

omit [Algebra.IsSeparable k k'] [Module.Finite k k'] in
/-- **A coproduct inclusion in `Scheme` IS an open immersion** — recorded because
`inferInstance` fails on it, which is how it gets read as absent. -/
theorem isOpenImmersion_sigmaι {σ : Type u} [Small.{u} σ] (g : σ → Scheme.{u}) (i : σ) :
    IsOpenImmersion (Sigma.ι g i) :=
  (sigmaOpenCover g).map_prop i

/-! ## The assembly: from cover-compatible classes to a `k`-representation -/

/-- **THE ASSEMBLY.** A `k`-scheme `Y` whose points are naturally the
cover-compatible `picEt C`-classes on `T_{k'}` REPRESENTS `picEt C`.

This is the theorem the descent step's four inputs are antecedents *of*, on the
class side: it takes data over the cover and concludes over `k`. -/
noncomputable def representableBy_of_coverCompatibleEquiv
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {Y : Over (Spec (CommRingCat.of k))}
    (e : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ Y) ≃ CoverCompatible (k' := k') C T)
    (he : ∀ {T T' : Over (Spec (CommRingCat.of k))} (f : T ⟶ T') (g : T' ⟶ Y),
      (e T (f ≫ g)).1 = ((coverFunctor (k := k) (k' := k')).op ⋙ picEt C).map f.op (e T' g).1) :
    (picEt C).RepresentableBy Y where
  homEquiv {T} := (e T).trans (restrictCompatEquiv (k' := k') C T).symm
  homEquiv_comp {T T'} f g := by
    apply (restrictCompatEquiv (k' := k') C T).injective
    change (restrictCompatEquiv (k' := k') C T)
        ((restrictCompatEquiv (k' := k') C T).symm (e T (f ≫ g))) = _
    rw [Equiv.apply_symm_apply]
    refine Subtype.ext ?_
    rw [restrictCompatEquiv_naturality (k' := k') C f]
    change (e T (f ≫ g)).1 = ((coverFunctor (k := k) (k' := k')).op ⋙ picEt C).map f.op
      ((restrictCompatEquiv (k' := k') C T')
        ((restrictCompatEquiv (k' := k') C T').symm (e T' g))).1
    rw [Equiv.apply_symm_apply]
    exact he f g

/-- **THE CONVERSE — so the assembly is a CHANGE OF COORDINATES, not a
strengthening, and this file says so as a theorem rather than as a caveat.**

A representation of `picEt C` by `Y` yields exactly the data
`representableBy_of_coverCompatibleEquiv` consumes: the per-test `Equiv` *and* its
naturality. Composed with that theorem, the two are **inter-derivable**.

This is the check a "reduction" claim owes before publication. Both directions are
proved, so the honest description of the assembly is: *to represent `picEt C` it is
equivalent to represent the cover-compatible-classes functor*. That is a genuine
repricing — the right-hand side is what a Galois quotient of a `k'`-side
representation produces, and the left-hand side is clause (1) field 1 — but it is
**not** a discount on the seam and must not be reported as one. -/
noncomputable def coverCompatibleEquiv_of_representableBy
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {Y : Over (Spec (CommRingCat.of k))}
    (rep : (picEt C).RepresentableBy Y) :
    Σ' e : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ Y) ≃ CoverCompatible (k' := k') C T,
      ∀ {T T' : Over (Spec (CommRingCat.of k))} (f : T ⟶ T') (g : T' ⟶ Y),
        (e T (f ≫ g)).1
          = ((coverFunctor (k := k) (k' := k')).op ⋙ picEt C).map f.op (e T' g).1 :=
  ⟨fun T => rep.homEquiv.trans (restrictCompatEquiv (k' := k') C T), by
    intro T T' f g
    change (picEt C).map (coverMap (k' := k') T).op (rep.homEquiv (f ≫ g)) = _
    rw [rep.homEquiv_comp]
    exact restrictCompatEquiv_naturality (k' := k') C f (rep.homEquiv g)⟩

/-! ### The Γ-INVARIANT form, which is what a `G1` consumer holds -/

/-- A class on `T_{k'}` fixed by every `γ ∈ Gal(k'/k)`, in `ajc-p1`'s `twistTest`
spelling. -/
def IsGalInvariant (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k)))
    (x : (picEt C).obj (op ((coverFunctor (k := k) (k' := k')).obj T))) : Prop :=
  ∀ γ : k' ≃ₐ[k] k',
    (picEt C).map (twistTest (k' := k') T γ).op x = x

omit [Algebra.IsSeparable k k'] [Module.Finite k k'] in
/-- **`IsCoverCompatible` implies `IsGalInvariant`, unconditionally** — `ajc-p1`'s
`invariant_of_projections_agree`, in this file's predicate spelling. -/
theorem isGalInvariant_of_isCoverCompatible (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k)))
    {x : (picEt C).obj (op ((coverFunctor (k := k) (k' := k')).obj T))}
    (hx : IsCoverCompatible (k' := k') C T x) :
    IsGalInvariant (k' := k') C T x :=
  fun γ => invariant_of_projections_agree C T x hx γ

omit [Algebra.IsSeparable k k'] [Module.Finite k k'] in
/-- **The converse, with `ajc-p1`'s covering antecedent `hcov` carried explicitly
and NOT discharged.** -/
theorem isCoverCompatible_of_isGalInvariant (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k)))
    (hcov : Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      etaleTopologyOver k (pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)))
    {x : (picEt C).obj (op ((coverFunctor (k := k) (k' := k')).obj T))}
    (hx : IsGalInvariant (k' := k') C T x) :
    IsCoverCompatible (k' := k') C T x :=
  projections_agree_of_invariant C T hcov x hx

/-- **The Γ-invariant classes on `T_{k'}`.** -/
def GalInvariant (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k))) : Type (u + 1) :=
  {x : (picEt C).obj (op ((coverFunctor (k := k) (k' := k')).obj T)) //
    IsGalInvariant (k' := k') C T x}

/-- The two subtypes AGREE, given `hcov` at every test — one inclusion is free,
the other is `hcov`. -/
noncomputable def coverCompatibleEquivGalInvariant (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k)))
    (hcov : Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      etaleTopologyOver k (pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T))) :
    CoverCompatible (k' := k') C T ≃ GalInvariant (k' := k') C T where
  toFun x := ⟨x.1, isGalInvariant_of_isCoverCompatible C T x.2⟩
  invFun x := ⟨x.1, isCoverCompatible_of_isGalInvariant C T hcov x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **THE ASSEMBLY, in the Γ-invariant form a `G1`/quotient consumer produces.**

A `k`-scheme `Y` whose points are naturally the `Γ`-INVARIANT `picEt C`-classes on
`T_{k'}` represents `picEt C` — given `hcov` at every test. -/
noncomputable def representableBy_of_galInvariantEquiv
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {Y : Over (Spec (CommRingCat.of k))}
    (hcov : ∀ T : Over (Spec (CommRingCat.of k)), Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      etaleTopologyOver k (pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)))
    (e : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ Y) ≃ GalInvariant (k' := k') C T)
    (he : ∀ {T T' : Over (Spec (CommRingCat.of k))} (f : T ⟶ T') (g : T' ⟶ Y),
      (e T (f ≫ g)).1 = ((coverFunctor (k := k) (k' := k')).op ⋙ picEt C).map f.op (e T' g).1) :
    (picEt C).RepresentableBy Y :=
  representableBy_of_coverCompatibleEquiv (k' := k') C
    (fun T => (e T).trans (coverCompatibleEquivGalInvariant C T (hcov T)).symm)
    (fun f g => he f g)

end Descend

end PicScheme

end Scheme

end AlgebraicGeometry
