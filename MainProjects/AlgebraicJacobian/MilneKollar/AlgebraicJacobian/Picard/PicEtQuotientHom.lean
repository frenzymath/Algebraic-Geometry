/-
Copyright (c) 2026 Axel Delaval. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval
-/
import AlgebraicJacobian.Picard.FiniteGaloisQuotient
import AlgebraicJacobian.Picard.PicEtDescentAssembly

/-!
# The Hom-side of the étale descent goal

`Picard/FGAPicRepresentability.lean` records, at `:475`, that the seam's
four-input paragraph lists *antecedents* and that **no declaration in this
project states the theorem they are antecedents of**; `I-1312` refuted the one
claim that `Picard/PicEtDescentAssembly.lean` supplied such a statement, and that
file's own §4 says the same. This file states and proves the part of that missing
goal which is **not** `P → P`.

## What is here, and why it is not a restatement of a hypothesis

The obstruction §4 of `PicEtDescentAssembly.lean` correctly identifies is that an
implication whose antecedent reads "the `k`-scheme exists with its properties" has
its own conclusion as a hypothesis. That is a fact about the *object* side of the
descent. The **Hom** side is different: clause 3 of
`AlgebraicJacobian.GaloisDescent.IsGaloisQuotient` already *asserts* a unique
descent of equivariant morphisms, and no declaration in the project extracts it
as the bijection

```
Hom_K(T, Y)  ≃  { equivariant  T_L ⟶ X  over  Spec L }
```

that the phrase "`Hom_K(T, Y) ≅ Hom_L(T_L, X)^Γ`" in that clause's own docstring
names. `quotientHomEquiv` below is that extraction, and
`picEtQuotientHomEquiv` composes it with a `k'`-side representation of
`picEt (C_{k'})` to land on **classes of the curve**: for every `k`-test `T`,

```
Hom_k(T, Y)  ≃  { equivariant  T_{k'} ⟶ X' }  →  picEt(C_{k'})(T_{k'})
```

with the first map a bijection and the second the representation's `homEquiv`.

## Three things this does NOT claim

* **It does not close the seam.** `Scheme.fgaPicardRepresentability` is untouched
  and is used here only as a `sorryAx` control. Clause (1)'s field 1 is witnessed
  for no curve, and the `k'`-side representation is a **hypothesis** of every
  statement below, not a produced object — it is the Milne–Kollár campaign's
  undischarged output.
* **It is not the invariance step.** The right-hand side above is
  *`Γ`-equivariant morphisms*, not *`Γ`-invariant `picEt`-classes*. Matching those
  two predicates is `G1`, roadmap `AJC.picrep.etale-rep.invariance` (held by
  `ajc-p1` as of `I-1417`; `ajc-p2` released it), and is deliberately left as the
  named residue rather than assumed. That match is *all* `G1` is owed here — see
  `range_equivariantToClass` and the withdrawal below.

## Two claims this file published and then withdrew

Both were refuted by a fresh-context audit (`I-1405`, `I-1406`, `I-1409`,
`I-1411`), reproduced by the author, and are corrected here at the sentence that
made them rather than annotated beneath it.

**WITHDRAWN 1 — "the data-valued `Equiv` is unprovable, so a lane wanting it must
strengthen `IsGaloisQuotient` to a structure".** FALSE, and it was a false price on
the project's own gate. `Classical.choice` eliminates a `Prop`-valued `Exists` into
`Type`, and this file already depends on it: `(quotientHomEquiv ρ hq T t).some` *is*
the `Equiv`, as a `noncomputable def`. What is true is only that the `Nonempty`
form is what a `Prop`-valued hypothesis gives *without* choice. The gate needs no
strengthening for this step. The same audit made a second, correct point: the
per-`T` `Nonempty` cannot carry a naturality square, so it cannot feed a
`RepresentableBy`. That is now **fixed rather than noted** —
`quotientHomEquiv_uniform` is the uniform form, and it follows from the same proof
script with no extra hypothesis.

**WITHDRAWN 2 — "no `omit` is needed because the linter flags both instances as
unused".** There is no `omit` in this file and there never was: the section binds
only `[Field K] [Field L] [Algebra K L]`, so `[FiniteDimensional K L]` and
`[IsGalois K L]` were never in scope and no linter could have flagged them. The
*mathematical* claim survives and is stronger for being read off the signature:
`quotientHomEquiv` needs no field theory at all, because clause 3's content is a
bijection between a `∃!` and its own witness set. Finiteness and Galois-ness enter
`IsGaloisQuotient`'s *inhabitation* (`HasGaloisQuotient`), never this extraction.
The description of how that was measured was fabricated; the fact is checkable from
the binders.

## The Hom side of Galois descent carries no geometry — measured

Every declaration of §2 below compiles **verbatim** with
`picEt (baseChangeField C k')` replaced by an arbitrary
`{F : (Over (Spec (CommRingCat.of k')))ᵒᵖ ⥤ Type (u+1)}` and with `C` and its two
curve instances **deleted** — `lake env lean` EXIT=0, axiom-clean, with
`fgaPicardRepresentability` firing `sorryAx` in the same file. So the curve is
*carried* here, not used.

The declarations below nonetheless keep `C`, because that is the shape the seam's
clause (1) consumes and a generic-`F` restatement would be a second name for one
theorem. What matters is the planning consequence: **a lane budgeting curve or
Picard infrastructure for the Hom side of Galois descent is over-budgeting.** The
geometry enters at the `k'`-side representation `rep` (the campaign's undischarged
output) and at `IsGaloisQuotient`'s *inhabitation*, never at this bookkeeping.

Note also which test this passes and which it fails: every declaration mentions its
object in the conclusion, so the `I-0838` reading of the vacuity test is satisfied —
and the geometry is still idle. "Delete the geometry and retypecheck" is the sharper
probe (`I-1411`).

## And the correction that matters for planning

The image of the Hom-map **is** characterised outright, with no invariance input:
see `range_equivariantToClass`. So the earlier sentence "what is missing is the
characterisation of the image, which is campaign `G1`" over-priced `G1`. What `G1`
actually owes is narrower — matching the predicate "the representing morphism is
`Γ`-equivariant" against "the class is `Γ`-invariant", two predicates on one
object. And the "not surjective" claim was refuted by this file's own boasted
generality: with no hypothesis on `k'/k`, `k' = k` is in the domain, `Γ` is trivial,
equivariance is vacuous, and the leg is surjective
(`surjective_equivariantToClass_of_subsingleton`). Both are now theorems here
rather than assertions.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace AlgebraicGeometry

namespace Scheme

namespace PicScheme

open AlgebraicJacobian.GaloisDescent

section QuotientHom

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- **Clause 3 of `IsGaloisQuotient`, extracted as the bijection its own docstring
names**: for every `K`-test `T`, morphisms `T ⟶ Y` over `Spec K` correspond to
`Γ`-equivariant morphisms `T_L ⟶ X` over `Spec L`.

The forward map is `u ↦ (u ×_K L) ≫ e.hom`, i.e. base-change the descended
morphism and compare along the quotient's structural isomorphism. Injectivity and
surjectivity are the uniqueness and existence halves of clause 3's `∃!`.

`Nonempty` is what a `Prop`-valued hypothesis gives directly. It is **not** a
limitation: `(quotientHomEquiv ρ hq T t).some` is the `Equiv` itself as a
`noncomputable def`, since `Classical.choice` eliminates `Exists` into `Type`. An
earlier revision of this docstring claimed the data-valued form was *unprovable* and
that the gate needed strengthening; that is withdrawn (`I-1405`, module docstring).

**No field-theoretic hypothesis is used**, and this is read off the binders rather
than from a linter: the section binds only `[Field K] [Field L] [Algebra K L]`, so
`[FiniteDimensional K L]` and `[IsGalois K L]` never enter. -/
theorem quotientHomEquiv {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (ρ : SemilinearGalAction K L X f) {Y : Scheme.{u}}
    {g : Y ⟶ Spec (CommRingCat.of K)} (hq : IsGaloisQuotient ρ g)
    (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of K)) :
    Nonempty ({u : T ⟶ Y // u ≫ g = t} ≃
      {h : pullback t (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ X //
        h ≫ f = pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧
          (pullbackSemilinearGalAction K L t).IsEquivariant ρ h}) := by
  obtain ⟨e, he, heq, huniv⟩ := hq
  refine ⟨Equiv.ofBijective
    (fun u => ⟨pullbackBaseChange K L g t u.1 u.2 ≫ e.hom, ?_, ?_⟩) ⟨?_, ?_⟩⟩
  · rw [Category.assoc, he, pullbackBaseChange_snd]
  · exact SemilinearGalAction.isEquivariant_pullbackBaseChange_comp (g := g) (t := t) ρ
      (he := heq) u.1 u.2
  · intro a b hab
    obtain ⟨w, hw, hwu⟩ := huniv T t (pullbackBaseChange K L g t b.1 b.2 ≫ e.hom)
      (by rw [Category.assoc, he, pullbackBaseChange_snd])
      (SemilinearGalAction.isEquivariant_pullbackBaseChange_comp (g := g) (t := t) ρ
        (he := heq) b.1 b.2)
    exact (hwu _ (congrArg Subtype.val hab)).trans (hwu _ rfl).symm
  · rintro ⟨h, hhf, hheq⟩
    obtain ⟨w, hw, -⟩ := huniv T t h hhf hheq
    exact ⟨w, Subtype.ext hw⟩

/-- **`Over`-homs are the subtype of scheme morphisms commuting with the structure
maps.** Pure bookkeeping (`Over.w` one way, `Over.homMk` the other), recorded
because it is the bridge between `quotientHomEquiv`, which is stated on bare
schemes because `IsGaloisQuotient` is, and the `Over (Spec k)`-tests that `picEt`
is a functor on. -/
noncomputable def overHomEquivSubtype {k : Type u} [Field k]
    (T Y : Over (Spec (CommRingCat.of k))) :
    (T ⟶ Y) ≃ {u : T.left ⟶ Y.left // u ≫ Y.hom = T.hom} where
  toFun φ := ⟨φ.left, Over.w φ⟩
  invFun u := Over.homMk u.1 u.2
  left_inv φ := by ext; rfl
  right_inv u := by ext; rfl

/-- **The uniform form — one `Nonempty` covering every test at once.**

This is the version a consumer building a `RepresentableBy` needs, and
`quotientHomEquiv` is *not* it: `Nonempty (E T)` separately for each `T` yields no
function `T ↦ E T`, so the per-test form cannot carry a naturality square. The
uniform form does.

It follows from the **same proof script** with no extra hypothesis — the
quantifier simply moves inside the `Nonempty`. Recorded because the per-test form
was landed first and a lane could reasonably have assumed the uniform one cost
more (`I-1405`). Still no field theory: the section binds only
`[Field K] [Field L] [Algebra K L]`. -/
theorem quotientHomEquiv_uniform {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (ρ : SemilinearGalAction K L X f) {Y : Scheme.{u}}
    {g : Y ⟶ Spec (CommRingCat.of K)} (hq : IsGaloisQuotient ρ g) :
    Nonempty (∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of K)),
      {u : T ⟶ Y // u ≫ g = t} ≃
      {h : pullback t (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ X //
        h ≫ f = pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧
          (pullbackSemilinearGalAction K L t).IsEquivariant ρ h}) := by
  obtain ⟨e, he, heq, huniv⟩ := hq
  refine ⟨fun T t => Equiv.ofBijective
    (fun u => ⟨pullbackBaseChange K L g t u.1 u.2 ≫ e.hom, ?_, ?_⟩) ⟨?_, ?_⟩⟩
  · rw [Category.assoc, he, pullbackBaseChange_snd]
  · exact SemilinearGalAction.isEquivariant_pullbackBaseChange_comp (g := g) (t := t) ρ
      (he := heq) u.1 u.2
  · intro a b hab
    obtain ⟨w, hw, hwu⟩ := huniv T t (pullbackBaseChange K L g t b.1 b.2 ≫ e.hom)
      (by rw [Category.assoc, he, pullbackBaseChange_snd])
      (SemilinearGalAction.isEquivariant_pullbackBaseChange_comp (g := g) (t := t) ρ
        (he := heq) b.1 b.2)
    exact (hwu _ (congrArg Subtype.val hab)).trans (hwu _ rfl).symm
  · rintro ⟨h, hhf, hheq⟩
    obtain ⟨w, hw, -⟩ := huniv T t h hhf hheq
    exact ⟨w, Subtype.ext hw⟩

end QuotientHom

/-! ## §2. Composing with the `k'`-side representation: down to classes of the curve -/

section CurveClasses

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-- **`quotientHomEquiv` in the slice**: for a semilinear action on `X'.left` with
Galois quotient `Y`, morphisms `T ⟶ Y` *in `Over (Spec k)`* correspond to
`Γ`-equivariant `T_{k'} ⟶ X'.left` over `Spec k'`.

`quotientHomEquiv` composed with `overHomEquivSubtype`. This is the form the
descent goal needs, because `picEt` is a functor on `Over (Spec k)` while
`IsGaloisQuotient` is stated on bare schemes.

**No curve occurs here, and that is deliberate.** An earlier draft of this
declaration bound `C` with its two curve instances; `C` did not appear in the
conclusion, which is exactly the `HasDivFunctor` failure mode protection `I-0838`
names. The binder is removed rather than justified: this statement is about the
action and the quotient, nothing else. The curve enters at
`equivariantToClass` and at `homClassMap_of_galoisQuotient` below, where it
occurs in the conclusion. -/
theorem homEquiv_equivariant_of_galoisQuotient
    {X' : Over (Spec (CommRingCat.of k'))}
    (ρ : AlgebraicJacobian.GaloisDescent.SemilinearGalAction k k' X'.left X'.hom)
    {Y : Over (Spec (CommRingCat.of k))}
    (hq : AlgebraicJacobian.GaloisDescent.IsGaloisQuotient ρ Y.hom)
    (T : Over (Spec (CommRingCat.of k))) :
    Nonempty ((T ⟶ Y) ≃
      {h : pullback T.hom (specMapAlgebra k k') ⟶ X'.left //
        h ≫ X'.hom = pullback.snd T.hom (specMapAlgebra k k') ∧
          (AlgebraicJacobian.GaloisDescent.pullbackSemilinearGalAction k k'
            T.hom).IsEquivariant ρ h}) := by
  obtain ⟨φ⟩ := quotientHomEquiv ρ hq T.left T.hom
  exact ⟨(overHomEquivSubtype T Y).trans φ⟩

/-- **The second leg**: an equivariant `T_{k'} ⟶ X'.left` over `Spec k'` gives a
`picEt (C_{k'})`-class on the base-changed test, by the representation's own
`homEquiv`.

The equivariance is *discarded* here on purpose — that is precisely the
information `G1` must recover, and stating the leg without it is what makes the
residue visible instead of hidden inside a bundled claim.

It is nonetheless **injective** (`equivariantToClass_injective`): forgetting
equivariance loses no morphisms, only cuts down the target. -/
noncomputable def equivariantToClass
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (PicScheme.picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    (ρ : AlgebraicJacobian.GaloisDescent.SemilinearGalAction k k' X'.left X'.hom)
    (T : Over (Spec (CommRingCat.of k)))
    (h : {h : pullback T.hom (specMapAlgebra k k') ⟶ X'.left //
        h ≫ X'.hom = pullback.snd T.hom (specMapAlgebra k k') ∧
          (AlgebraicJacobian.GaloisDescent.pullbackSemilinearGalAction k k'
            T.hom).IsEquivariant ρ h}) :
    (PicScheme.picEt (Scheme.baseChangeField C k')).obj
      (Opposite.op (PicScheme.baseTest (k' := k') T)) :=
  rep.homEquiv (Over.homMk h.1 h.2.1)

/-- **The second leg is injective.** `rep.homEquiv` is an equivalence and
`Over.homMk` is injective in its underlying map, so forgetting equivariance
does not merge two morphisms — it only fails to be *surjective*.

An earlier draft of this file's docstrings said only "the second leg is a map, not
a bijection", which leaves the reader to guess which half fails, and then said the
missing half was "the characterisation of the image, which is campaign `G1`". The
second sentence is **withdrawn**: the image is characterised outright by
`range_equivariantToClass`, and surjectivity can even *hold*
(`surjective_equivariantToClass_of_subsingleton`). Injectivity is what this lemma
adds; see the module docstring for what `G1` is actually owed. -/
theorem equivariantToClass_injective
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (PicScheme.picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    (ρ : AlgebraicJacobian.GaloisDescent.SemilinearGalAction k k' X'.left X'.hom)
    (T : Over (Spec (CommRingCat.of k))) :
    Function.Injective (equivariantToClass C rep ρ T) := by
  intro a b hab
  have h1 : (Over.homMk a.1 a.2.1 : PicScheme.baseTest (k' := k') T ⟶ X')
      = Over.homMk b.1 b.2.1 := rep.homEquiv.injective hab
  exact Subtype.ext (congrArg CategoryTheory.Over.Hom.left h1)

/-- **The image of the second leg, characterised outright** — with no invariance
input, no hypothesis on `k'/k`, and no appeal to campaign `G1`.

A class `c` on `T_{k'}` comes from an equivariant morphism exactly when the
morphism `rep` already assigns to it is equivariant. That is a tautology once
stated, and stating it is the point: an earlier revision of this file priced "the
characterisation of the image" as `G1`'s work. It is not. What `G1` owes is
narrower — matching *this* predicate, "`rep.homEquiv.symm c` is `Γ`-equivariant",
against "`c` is a `Γ`-invariant `picEt`-class". Those are two predicates on one
object, and the reduction between them is what an invariance lemma must supply.

Recorded as a theorem rather than a remark because the assertion it replaces was
believed for the length of three commits (`I-1406`). -/
theorem range_equivariantToClass
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (PicScheme.picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    (ρ : AlgebraicJacobian.GaloisDescent.SemilinearGalAction k k' X'.left X'.hom)
    (T : Over (Spec (CommRingCat.of k))) :
    Set.range (equivariantToClass C rep ρ T)
      = {c | (AlgebraicJacobian.GaloisDescent.pullbackSemilinearGalAction k k'
                T.hom).IsEquivariant ρ (rep.homEquiv.symm c).left} := by
  ext c
  constructor
  · rintro ⟨h, rfl⟩
    simp only [equivariantToClass, Set.mem_setOf_eq, Equiv.symm_apply_apply]
    exact h.2.2
  · intro hc
    refine ⟨⟨(rep.homEquiv.symm c).left, Over.w (rep.homEquiv.symm c), hc⟩, ?_⟩
    simp only [equivariantToClass]
    rw [show (Over.homMk (rep.homEquiv.symm c).left (Over.w (rep.homEquiv.symm c))
      : PicScheme.baseTest (k' := k') T ⟶ X') = rep.homEquiv.symm c from
        CategoryTheory.Over.homMk_eta _ _]
    exact rep.homEquiv.apply_symm_apply c

/-- **The second leg can be surjective**, so "it is injective but not surjective"
was false as stated.

The refutation uses nothing but the generality this file advertises: no
separability or finiteness on `k'/k` is assumed anywhere, so `k' = k` is in the
domain; there `Gal(k'/k)` is a subsingleton, the equivariance condition holds for
the only group element, and every class is hit.

This is the degenerate substitution that a "strictly weaker than" or "not
surjective" claim needs before publication — the parameter the boast leaves
unconstrained is the one to try first (`I-1413`). -/
theorem surjective_equivariantToClass_of_subsingleton
    [Subsingleton (k' ≃ₐ[k] k')]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (PicScheme.picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    (ρ : AlgebraicJacobian.GaloisDescent.SemilinearGalAction k k' X'.left X'.hom)
    (T : Over (Spec (CommRingCat.of k))) :
    Function.Surjective (equivariantToClass C rep ρ T) := by
  intro c
  refine ⟨⟨(rep.homEquiv.symm c).left, Over.w (rep.homEquiv.symm c), ?_⟩, ?_⟩
  · intro γ
    have h1 : γ = 1 := Subsingleton.elim _ _
    subst h1
    change ((AlgebraicJacobian.GaloisDescent.pullbackSemilinearGalAction k k'
      T.hom).act 1).hom ≫ _ = _ ≫ (ρ.act 1).hom
    rw [map_one, map_one]
    change (Iso.refl _).hom ≫ _ = _ ≫ (Iso.refl _).hom
    rw [Iso.refl_hom, Category.id_comp]
    rw [Iso.refl_hom, Category.comp_id]
  · simp only [equivariantToClass]
    rw [show (Over.homMk (rep.homEquiv.symm c).left (Over.w (rep.homEquiv.symm c))
      : PicScheme.baseTest (k' := k') T ⟶ X') = rep.homEquiv.symm c from
        CategoryTheory.Over.homMk_eta _ _]
    exact rep.homEquiv.apply_symm_apply c

/-- **The Hom-side of the descent goal, with the curve in the conclusion.**

For a smooth proper curve `C` over an **arbitrary** field `k`, a field extension
`k'/k`, a `k'`-scheme `X'` **representing** `picEt (C_{k'})`, a semilinear
`Gal`-action on `X'.left`, and a `k`-scheme `Y` that is its Galois quotient: there
is a map

```
Hom_{Over (Spec k)}(T, Y)  ⟶  picEt (C_{k'}) (T_{k'})
```

for every `k`-test `T`, factoring as a **bijection** onto `Γ`-equivariant
morphisms followed by the representation's `homEquiv`. This is the statement the
seam's four-input paragraph (`Picard/FGAPicRepresentability.lean:475`) lists
antecedents *of*, on its Hom side, and it is the shape the descent step must
upgrade.

**Exactly which half is owed.** The first leg is a bijection
(`homEquiv_equivariant_of_galoisQuotient`, from `IsGaloisQuotient` clause 3) and the
second leg is **injective** (`equivariantToClass_injective`), so the whole composite
is injective (`homClassMap_of_galoisQuotient_injective`).

What is owed is **not** "the characterisation of the image". That sentence stood here
and is **withdrawn** (`I-1418`, `I-1421`): `range_equivariantToClass` characterises
the image outright, with no invariance input, and
`surjective_equivariantToClass_of_subsingleton` shows the leg can even *be*
surjective. What is owed is the narrower **predicate match** — that
"`rep.homEquiv.symm c` is `Γ`-equivariant as a morphism" agrees with "`c` is a
`Γ`-invariant `picEt`-class" — which is `G1`, roadmap
`AJC.picrep.etale-rep.invariance` (held by `ajc-p1` as of `I-1417`; `ajc-p2`
released it).

Do **not** read this as a representation of `picEt C`: it is an injection into the
classes of the base-**changed** curve, and even a bijection onto the invariants would
still need the amalgamation of `Picard/EtaleFieldCover.lean` to descend to
`picEt C (T)`.

**Three things this does not do.**
* It does not close or weaken `Scheme.fgaPicardRepresentability`, which is used in
  this file's verification only as a `sorryAx` control.
* `rep` is a **hypothesis**, the campaign's undischarged output; field 1 of clause
  (1) is witnessed for no curve, so nothing here is instantiable at a curve today.
* It carries no `HasRationalPoint` binder (`I-0491`), and no separability or
  finiteness hypothesis on `k'/k` — none is used. -/
noncomputable def homClassMap_of_galoisQuotient
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (PicScheme.picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    (ρ : AlgebraicJacobian.GaloisDescent.SemilinearGalAction k k' X'.left X'.hom)
    {Y : Over (Spec (CommRingCat.of k))}
    (hq : AlgebraicJacobian.GaloisDescent.IsGaloisQuotient ρ Y.hom)
    (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ Y) → (PicScheme.picEt (Scheme.baseChangeField C k')).obj
      (Opposite.op (PicScheme.baseTest (k' := k') T)) :=
  fun φ => equivariantToClass C rep ρ T
    ((homEquiv_equivariant_of_galoisQuotient ρ hq T).some φ)

/-- **The composite is injective**: distinct `k`-morphisms `T ⟶ Y` give distinct
`picEt (C_{k'})`-classes on `T_{k'}`.

Both legs are injective, so this is their composition: a Galois quotient of a
`k'`-representation **embeds** its `k`-points into the classes of the base-changed
curve, for every test, over an arbitrary field.

**Two claims that stood here are withdrawn** (`I-1418`, `I-1421`), and this file now
contradicts both itself. "It is the strongest statement available without `G1`" is
false — `surjective_equivariantToClass_of_subsingleton` gives *bijectivity* with no
`G1` input. "What remains is the image characterisation, not the injection" is false —
`range_equivariantToClass` is that characterisation, and it is free. What remains is
the predicate match described at `homClassMap_of_galoisQuotient`. -/
theorem homClassMap_of_galoisQuotient_injective
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (PicScheme.picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    (ρ : AlgebraicJacobian.GaloisDescent.SemilinearGalAction k k' X'.left X'.hom)
    {Y : Over (Spec (CommRingCat.of k))}
    (hq : AlgebraicJacobian.GaloisDescent.IsGaloisQuotient ρ Y.hom)
    (T : Over (Spec (CommRingCat.of k))) :
    Function.Injective (homClassMap_of_galoisQuotient C rep ρ hq T) :=
  (equivariantToClass_injective C rep ρ T).comp
    (homEquiv_equivariant_of_galoisQuotient ρ hq T).some.injective

end CurveClasses

end PicScheme

end Scheme

end AlgebraicGeometry
