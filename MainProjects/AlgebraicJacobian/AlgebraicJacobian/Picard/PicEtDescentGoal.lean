/-
Copyright (c) 2026 Axel Delaval. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval
-/
import AlgebraicJacobian.Picard.GaloisDescent.PicEtGaloisAction
import AlgebraicJacobian.Picard.PicEtDescentRepresentability
import AlgebraicJacobian.Picard.PicEtSeparated

/-!
# THE DESCENT GOAL: `k'`-side representability + a Galois quotient ⟹ clause (1) over `k`

`AJC.picrep.etale-rep.descent-assembly`.

## The defect this file addresses

`Picard/FGAPicRepresentability.lean` said, of the four inputs of the étale-descent
repair, that every entry is an *antecedent* and that there was **no declaration
anywhere in this project stating the theorem they are antecedents of**.

**That sentence is no longer in the source, because this file made it false and the
paragraph is now past-tense there.** An earlier revision of this docstring
block-quoted its present-tense form and said "quoted rather than paraphrased" —
which stopped being accurate the moment the seam file was corrected, i.e. within an
hour (fresh-context audit, finding 4). Paraphrased on purpose now: a verbatim quote
of a file this one is actively changing rots faster than a paraphrase.

`I-1312` refuted the one file that had claimed to supply such a statement
(`Picard/PicEtDescentAssembly.lean`'s `representableByRestrict_of_baseChange`
concludes a `RepresentableBy` for a `k'`-**object**, i.e. restates the `k'`-side
input in the right variables rather than crossing the descent step). This file
states and proves that theorem.

Its shape, and the reason it is not `P → P`: the hypothesis is a representation of
`picEt (C_{k'})` — the Picard functor of the **base-changed** curve, over `k'` —
plus a Galois quotient of the resulting action. The conclusion is a representation
of `picEt C`, the functor over `k` whose representability is field 1 of the seam's
clause (1). Neither the conclusion nor `HasPicSchemeEt C` occurs in any hypothesis.

## What composes, and where each piece comes from

**Read the dependency list below as a list of PRECEDENTS, not of dependencies.** An
earlier revision of this section said "four files hold the pieces; nothing joined
them", which reads as a claim about this file's proof terms and is false of two of
the four (fresh-context audit, finding 4). Measured: only item 4 occurs in any proof
term here. Items 2 and 3 occur **only in docstrings** — this file re-derives item 2
(as `quotientHomEquivOfIso`, for the reason in §2b) and inlines item 3 (as
`Equiv.subtypeEquiv rep.homEquiv`). A reader budgeting against "four files hold the
pieces" would be reading the wrong graph.

1. `GaloisDescent/PicEtGaloisAction.lean` — `semilinearGalActionOfRepresentableBy`
   makes the semilinear Galois action **free from `rep`**. *Used*, in §6's
   `_canonical` form.
2. `PicEtQuotientHom.lean` — `quotientHomEquiv_uniform` turns clause 3 of
   `IsGaloisQuotient` into `Hom_k(T, Y) ≃ {equivariant T_{k'} ⟶ X'}`. **Not used**:
   its `Nonempty` cannot carry a naturality square, so §2b re-derives the same
   bijection with its forward map pinned. Precedent for the script, not a dependency.
3. `rep` itself — the second leg `{equivariant T_{k'} ⟶ X'} → picEt(C_{k'})(T_{k'})`.
   `range_equivariantToClass` characterises its image; **not used** here, the leg is
   inlined as a subtype equivalence.
4. `PicEtDescentRepresentability.lean` — `representableBy_of_galInvariantEquiv`
   takes a natural family of `Equiv`s onto the `Γ`-**invariant** classes on `T_{k'}`
   and concludes `(picEt C).RepresentableBy Y`. **The one genuine dependency**, and
   the only place `[Algebra.IsSeparable k k']` and `[Module.Finite k k']` are spent.

So the composite needs the two ends to meet, and what stands between them is
exactly the predicate match `G1` owes: leg 3's image is
`{c | rep.homEquiv.symm c is Γ-equivariant}` while leg 4 consumes
`{c | c is a Γ-invariant picEt-class}`. That match is **carried here as one named
explicit hypothesis** (`IsInvariantMatch`), not absorbed and not proved: it is
`AJC.picrep.etale-rep.invariance`, and `hcov` is `AJC.picrep.etale-rep.hcov`
(`pic-a`'s row this round).

## What this does NOT do

* It does **not** close `Scheme.fgaPicardRepresentability`. `rep` is a hypothesis —
  the Milne–Kollár campaign's undischarged output — and clause (1) field 1 is
  witnessed for **no** curve. This file is used in its own verification with that
  theorem as a `sorryAx` control.
* It witnesses **no** antecedent of the seam. It converts four antecedents plus one
  named predicate match into the seam's conclusion; the antecedents stay open.
* Per `I-0491` there is no `HasRationalPoint` binder anywhere in this file.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicJacobian.GaloisDescent

namespace AlgebraicGeometry

namespace Scheme

namespace PicScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-! ## §1. The predicate match `G1` owes, as a named hypothesis -/

/-- **The `G1` predicate match, named.**

Leg 3 of the descent composite lands on the classes whose representing morphism is
`Γ`-equivariant (`range_equivariantToClass`); leg 4 consumes the classes that are
`Γ`-**invariant** in the sense of `IsGalInvariant`. This is the statement that the
two predicates agree — two predicates on one object, which is all that campaign
`G1` is owed on this route (`Picard/PicEtQuotientHom.lean`, module docstring).

It is carried as an explicit hypothesis of everything below. Stated as a definition so
that a lane closing `G1` has a name to discharge and so that the composite's
obligations are countable rather than inlined.

**AND IT IS NOW DISCHARGED AT THE CANONICAL ACTION, so `G1` IS NO LONGER AN INPUT OF
THIS ROUTE.** `PicScheme.isInvariantMatch_canonical`
(`Picard/PicEtInvariantMatch.lean`) proves
`IsInvariantMatch C rep (semilinearGalActionOfRepresentableBy C rep) T` for every `T`,
with no hypothesis beyond `rep` and the curve's own binders — arbitrary `k`, arbitrary
`k'/k`, no finiteness, no separability, no `IsGalois`, no condition on `Gal(k'/k)`. The
reason it is free is that the canonical action's `γ`-component **is** `twistMor γ`,
which is defined by transporting `galoisActionPicEt` along `rep`, so equivariance and
invariance are two readings of one functor-level equation and naturality converts
between them. Use `seamClauseOne_of_isGaloisQuotient_noMatch` there rather than
supplying `hmatch`; the paragraphs below are kept because the *definition* is still
what a non-canonical action would have to satisfy.

**THE PARAGRAPH THAT USED TO STAND HERE said this predicate was "satisfiable but not
measured non-vacuous, and the only exhibited witness site trivialises the theorem it
feeds", with `isInvariantMatch_of_subsingleton` and `representableBy_picEt_of_degenerate`
below as that measurement.** Both theorems stand and are still true; the *reading* is
withdrawn — "exhibiting a model at an extension with a nontrivial automorphism is open"
is no longer the question for *this* hypothesis at the canonical action, since it is free
at every extension there.

**But `isInvariantMatch_of_subsingleton` is NOT subsumed, and a revision of this very
paragraph claimed it was** (fresh-context audit, refuting the correction rather than the
original). That lemma quantifies over an **arbitrary** `ρ`; `isInvariantMatch_canonical`
pins `ρ` to the canonical action, so the two are **incomparable** — one is more general
in the extension, the other in the action. The lemma remains **load-bearing** at
`representableBy_picEt_of_degenerate` below, which takes an external `ρ`: do not delete it
and do not reroute that call.

**What the withdrawal does NOT extend to, and this is the half that survives:** `hcov`.
Its only exhibited witness site still trivialises the conclusion
(`etaleTopology_generate_coverSelfSection_of_mono` at `k' = k`), so the trap
`Picard/PicEtDescentRepresentability.lean` records for `hcov` is untouched, and
`representableBy_picEt_of_degenerate` below still shows that at `k' = k` the remaining
inputs collapse. Do not read the theorems of §5–§6 as instantiable at a nondegenerate
site: the reason is now `hcov` and the `k'`-side representation alone. -/
def IsInvariantMatch (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    (ρ : SemilinearGalAction k k' X'.left X'.hom)
    (T : Over (Spec (CommRingCat.of k))) : Prop :=
  ∀ c : (picEt (Scheme.baseChangeField C k')).obj (op (baseTest (k' := k') T)),
    (pullbackSemilinearGalAction k k' T.hom).IsEquivariant ρ (rep.homEquiv.symm c).left
      ↔ IsGalInvariant (k' := k') C T
          ((picEt_crossBaseIso C k').hom.app (op (baseTest (k' := k') T)) c)

/-- **`IsInvariantMatch` is FREE at a trivial Galois group** — the satisfiability
half, and half of why satisfiability is not content here.

Both sides of the iff quantify over `γ`; with only `γ = 1` present, the left side is
the action's unit law and the right is `twistTest_one` plus `Functor.map_id`. No
input about `rep`, the curve, or the classes is used. -/
theorem isInvariantMatch_of_subsingleton [Subsingleton (k' ≃ₐ[k] k')]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    (ρ : SemilinearGalAction k k' X'.left X'.hom)
    (T : Over (Spec (CommRingCat.of k))) :
    IsInvariantMatch C rep ρ T := by
  intro c
  constructor
  · intro _ γ
    obtain rfl : γ = 1 := Subsingleton.elim _ _
    rw [twistTest_one, op_id]
    simp
  · intro _ γ
    obtain rfl : γ = 1 := Subsingleton.elim _ _
    change ((pullbackSemilinearGalAction k k' T.hom).act 1).hom ≫ _
      = _ ≫ (ρ.act 1).hom
    rw [map_one, map_one]
    change (Iso.refl _).hom ≫ _ = _ ≫ (Iso.refl _).hom
    rw [Iso.refl_hom, Category.id_comp, Iso.refl_hom, Category.comp_id]

/-! ## §2. The descent class of a `k`-morphism, and its naturality

The composite must be built from the **explicit** forward map of `IsGaloisQuotient`
clause 3, not from `(quotientHomEquiv …).some`: a `Nonempty` of a per-test `Equiv`
gives no function `T ↦ e T`, hence no naturality square, hence no
`RepresentableBy` (`Picard/PicEtQuotientHom.lean`, `I-1405`). So this section works
with the structural iso `e` of the quotient directly. -/

section DescentClass

variable {C : Over (Spec (CommRingCat.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  {X' : Over (Spec (CommRingCat.of k'))}
  (rep : (picEt (Scheme.baseChangeField C k')).RepresentableBy X')
  {Y : Over (Spec (CommRingCat.of k))}
  (e : Limits.pullback Y.hom (specMapAlgebra k k') ≅ X'.left)
  (he : e.hom ≫ X'.hom = pullback.snd Y.hom (specMapAlgebra k k'))

/-- **The `k'`-side test morphism of a `k`-morphism `u : T ⟶ Y`**: base-change `u`
along `k ⊆ k'` and compare along the quotient's structural iso. This is the forward
map of `IsGaloisQuotient` clause 3, written explicitly. -/
noncomputable def quotientIsoOver : (Over.pullback (specMapAlgebra k k')).obj Y ⟶ X' :=
  Over.homMk e.hom he

noncomputable def descentMor (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ Y) :
    baseTest (k' := k') T ⟶ X' :=
  (Over.pullback (specMapAlgebra k k')).map u ≫ quotientIsoOver e he

/-- **The underlying map of `descentMor` is the one `IsGaloisQuotient` clause 3
speaks about**: `pullbackBaseChange` of `u` followed by the structural iso. The two
spellings of "base change of a slice morphism" — mathlib's `Over.pullback` functor
and the project's `pullbackBaseChange` — agree, and this is the bridge. -/
theorem descentMor_left (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ Y) :
    (descentMor e he T u).left
      = pullbackBaseChange k k' Y.hom T.hom u.left (Over.w u) ≫ e.hom := by
  refine congrArg (· ≫ e.hom) ?_
  have hL : ((Over.pullback (specMapAlgebra k k')).map u).left
      = Limits.pullback.lift
          (Limits.pullback.fst T.hom (specMapAlgebra k k') ≫ u.left)
          (Limits.pullback.snd T.hom (specMapAlgebra k k'))
          (by simp [Limits.pullback.condition, Over.w u]) := rfl
  refine hL.trans (Limits.pullback.hom_ext ?_ ?_)
  · rw [Limits.pullback.lift_fst, pullbackBaseChange_fst]
  · rw [Limits.pullback.lift_snd, pullbackBaseChange_snd]

/-- **The descent class**: the `picEt C`-class on `T_{k'}` that `u : T ⟶ Y`
determines, via `rep` and the cross-base identification. -/
noncomputable def descentClass (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ Y) :
    (picEt C).obj (op ((coverFunctor (k := k) (k' := k')).obj T)) :=
  (picEt_crossBaseIso C k').hom.app (op (baseTest (k' := k') T))
    (rep.homEquiv (descentMor e he T u))

/-- **`descentMor` is functorial in the test** — and it is *two lines*, which is the
whole reason `descentMor` is defined through the `Over.pullback` **functor**:
`Functor.map_comp` and `Category.assoc`, no pullback computation at all.

**An earlier revision of this docstring cited `pullbackBaseChange_comp` here.** That
was a description of a route this proof does not take, and the name is not even in
this file's import closure (it lives in `Picard/FiniteGaloisQuotientAffine.lean`,
which nothing here imports) — so it would have failed a `#check`, not just a
reading. Recorded rather than silently deleted: a docstring naming the *first*
attempt's ingredients is the failure mode that survives a green build. -/
theorem descentMor_comp {T T' : Over (Spec (CommRingCat.of k))}
    (f : T ⟶ T') (g : T' ⟶ Y) :
    descentMor e he T (f ≫ g)
      = ((Over.pullback (specMapAlgebra k k')).map f) ≫ descentMor e he T' g := by
  change (Over.pullback (specMapAlgebra k k')).map (f ≫ g) ≫ quotientIsoOver e he
      = _ ≫ (Over.pullback (specMapAlgebra k k')).map g ≫ quotientIsoOver e he
  rw [Functor.map_comp]
  exact Category.assoc _ _ _

end DescentClass

/-! ## §2b. Clause 3 of `IsGaloisQuotient` with its forward map PINNED to `descentMor`

`quotientHomEquiv` and `quotientHomEquiv_uniform` (`Picard/PicEtQuotientHom.lean`)
give the bijection only inside a `Nonempty`, so `.some` is an anonymous `Equiv`
about which nothing further can be proved. The version below is the same bijection
with its `toFun` **fixed** to be `descentMor`, which is what makes the naturality of
§4 provable at all. -/

section QuotientHomPinned

variable {C : Over (Spec (CommRingCat.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  {X' : Over (Spec (CommRingCat.of k'))}
  {Y : Over (Spec (CommRingCat.of k))}

set_option maxHeartbeats 1000000 in
-- Heartbeat headroom: the `Over`/`pullback` coercion chain of `descentMor` is
-- unfolded repeatedly against `IsGaloisQuotient`'s bare-scheme spelling.
/-- **Clause 3, as an `Equiv` in the slice with a named forward map.**

Extracted from a quotient's structural iso `e` rather than from
`IsGaloisQuotient` as a whole, so that the forward map is `descentMor e he` on the
nose. Injectivity and surjectivity are the uniqueness and existence halves of
clause 3's `∃!`, exactly as in `quotientHomEquiv`. -/
noncomputable def quotientHomEquivOfIso
    (ρ : SemilinearGalAction k k' X'.left X'.hom)
    (e : Limits.pullback Y.hom (specMapAlgebra k k') ≅ X'.left)
    (he : e.hom ≫ X'.hom = pullback.snd Y.hom (specMapAlgebra k k'))
    (heq : (pullbackSemilinearGalAction k k' Y.hom).IsEquivariant ρ e.hom)
    (huniv : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k))
      (h : Limits.pullback t (specMapAlgebra k k') ⟶ X'.left),
      h ≫ X'.hom = pullback.snd t (specMapAlgebra k k') →
      (pullbackSemilinearGalAction k k' t).IsEquivariant ρ h →
      ∃! u : {u : T ⟶ Y.left // u ≫ Y.hom = t},
        pullbackBaseChange k k' Y.hom t u.1 u.2 ≫ e.hom = h)
    (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ Y) ≃ {h : Limits.pullback T.hom (specMapAlgebra k k') ⟶ X'.left //
      h ≫ X'.hom = pullback.snd T.hom (specMapAlgebra k k') ∧
        (pullbackSemilinearGalAction k k' T.hom).IsEquivariant ρ h} := by
  have hsnd : ∀ u : T ⟶ Y,
      (pullbackBaseChange k k' Y.hom T.hom u.left (Over.w u) ≫ e.hom) ≫ X'.hom
        = pullback.snd T.hom (specMapAlgebra k k') := fun u => by
    rw [Category.assoc, he, pullbackBaseChange_snd]
  have hfwd : ∀ u : T ⟶ Y,
      (pullbackSemilinearGalAction k k' T.hom).IsEquivariant ρ
        (pullbackBaseChange k k' Y.hom T.hom u.left (Over.w u) ≫ e.hom) := fun u =>
    SemilinearGalAction.isEquivariant_pullbackBaseChange_comp
      (g := Y.hom) (t := T.hom) ρ (he := heq) u.left (Over.w u)
  refine Equiv.ofBijective
    (fun u => ⟨pullbackBaseChange k k' Y.hom T.hom u.left (Over.w u) ≫ e.hom,
      hsnd u, hfwd u⟩) ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨w, -, hwu⟩ := huniv T.left T.hom
      (pullbackBaseChange k k' Y.hom T.hom b.left (Over.w b) ≫ e.hom)
      (hsnd b) (hfwd b)
    refine CategoryTheory.Over.OverMorphism.ext ?_
    exact congrArg Subtype.val
      ((hwu ⟨a.left, Over.w a⟩ (congrArg Subtype.val hab)).trans
        (hwu ⟨b.left, Over.w b⟩ rfl).symm)
  · rintro ⟨h, hh1, hh2⟩
    obtain ⟨w, hw, -⟩ := huniv T.left T.hom h hh1 hh2
    exact ⟨Over.homMk w.1 w.2, Subtype.ext hw⟩

end QuotientHomPinned

/-! ## §3. The composite Equiv at one test -/

/-- **Leg 1 ∘ leg 3, as an `Equiv` onto the `Γ`-invariant classes on `T_{k'}`,
given the `G1` match.**

`Hom_k(T, Y) ≃ {equivariant T_{k'} ⟶ X'} ≃ {equivariant-image classes}
             = {Γ-invariant classes}`,

where the first step is clause 3 of `IsGaloisQuotient` (`quotientHomEquivOfIso`)
, the second is `rep` restricted to its
image (`range_equivariantToClass`), and the third is the hypothesis
`IsInvariantMatch` transported along `picEt_crossBaseIso`.

Its forward map is `descentClass` (`galInvariantEquivOfQuotient_val`), which is
what makes the naturality of §4 provable — see `§2b`. -/
noncomputable def galInvariantEquivOfQuotient
    {C : Over (Spec (CommRingCat.of k))}
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    (ρ : SemilinearGalAction k k' X'.left X'.hom)
    {Y : Over (Spec (CommRingCat.of k))}
    (e : Limits.pullback Y.hom (specMapAlgebra k k') ≅ X'.left)
    (he : e.hom ≫ X'.hom = pullback.snd Y.hom (specMapAlgebra k k'))
    (heq : (pullbackSemilinearGalAction k k' Y.hom).IsEquivariant ρ e.hom)
    (huniv : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k))
      (h : Limits.pullback t (specMapAlgebra k k') ⟶ X'.left),
      h ≫ X'.hom = pullback.snd t (specMapAlgebra k k') →
      (pullbackSemilinearGalAction k k' t).IsEquivariant ρ h →
      ∃! u : {u : T ⟶ Y.left // u ≫ Y.hom = t},
        pullbackBaseChange k k' Y.hom t u.1 u.2 ≫ e.hom = h)
    (hmatch : ∀ T, IsInvariantMatch C rep ρ T)
    (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ Y) ≃ GalInvariant (k' := k') C T := by
  refine (quotientHomEquivOfIso ρ e he heq huniv T).trans ?_
  -- the subtype of bare equivariant morphisms is the subtype of slice morphisms
  have eA : {h : pullback T.hom (specMapAlgebra k k') ⟶ X'.left //
        h ≫ X'.hom = pullback.snd T.hom (specMapAlgebra k k') ∧
          (pullbackSemilinearGalAction k k' T.hom).IsEquivariant ρ h} ≃
      {φ : baseTest (k' := k') T ⟶ X' //
        (pullbackSemilinearGalAction k k' T.hom).IsEquivariant ρ φ.left} := by
    have hw : ∀ φ : baseTest (k' := k') T ⟶ X',
        φ.left ≫ X'.hom = pullback.snd T.hom (specMapAlgebra k k') := fun φ => Over.w φ
    let inv : {φ : baseTest (k' := k') T ⟶ X' //
          (pullbackSemilinearGalAction k k' T.hom).IsEquivariant ρ φ.left} →
        {h : pullback T.hom (specMapAlgebra k k') ⟶ X'.left //
          h ≫ X'.hom = pullback.snd T.hom (specMapAlgebra k k') ∧
            (pullbackSemilinearGalAction k k' T.hom).IsEquivariant ρ h} :=
      fun φ => ⟨φ.1.left, hw φ.1, φ.2⟩
    exact
      { toFun := fun h => ⟨Over.homMk h.1 h.2.1, h.2.2⟩
        invFun := inv
        left_inv := fun _ => rfl
        right_inv := fun φ =>
          Subtype.ext (CategoryTheory.Over.homMk_eta φ.1 (hw φ.1)) }
  refine eA.trans (Equiv.trans ?_
    (Equiv.subtypeEquiv
      ((picEt_crossBaseIso C k').app (op (baseTest (k' := k') T))).toEquiv
      (fun c => hmatch T c)))
  exact Equiv.subtypeEquiv rep.homEquiv (fun _ => by rw [Equiv.symm_apply_apply])

set_option maxHeartbeats 1000000 in
-- Heartbeat headroom: same `Over`/`pullback` coercion chain as
-- `quotientHomEquivOfIso`, unfolded once more through the composite's three legs.
/-- **The value of the composite Equiv IS the descent class.**

This is the identity that makes naturality provable: the composite's underlying
class is `descentClass`, which §2 proved functorial. With
`quotientHomEquiv_uniform`'s `.some` in the forward slot there would be no such
formula. -/
theorem galInvariantEquivOfQuotient_val
    {C : Over (Spec (CommRingCat.of k))}
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    (ρ : SemilinearGalAction k k' X'.left X'.hom)
    {Y : Over (Spec (CommRingCat.of k))}
    (e : Limits.pullback Y.hom (specMapAlgebra k k') ≅ X'.left)
    (he : e.hom ≫ X'.hom = pullback.snd Y.hom (specMapAlgebra k k'))
    (heq : (pullbackSemilinearGalAction k k' Y.hom).IsEquivariant ρ e.hom)
    (huniv : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k))
      (h : Limits.pullback t (specMapAlgebra k k') ⟶ X'.left),
      h ≫ X'.hom = pullback.snd t (specMapAlgebra k k') →
      (pullbackSemilinearGalAction k k' t).IsEquivariant ρ h →
      ∃! u : {u : T ⟶ Y.left // u ≫ Y.hom = t},
        pullbackBaseChange k k' Y.hom t u.1 u.2 ≫ e.hom = h)
    (hmatch : ∀ T, IsInvariantMatch C rep ρ T)
    (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ Y) :
    (galInvariantEquivOfQuotient rep ρ e he heq huniv hmatch T u).1
      = descentClass rep e he T u := by
  exact congrArg (fun m => (picEt_crossBaseIso C k').hom.app _ (rep.homEquiv m))
    (CategoryTheory.Over.OverMorphism.ext (descentMor_left e he T u)).symm

/-! ## §4. Naturality of the descent class -/

set_option maxHeartbeats 1000000 in
-- Heartbeat headroom: as above; the cross-base naturality square is checked
-- against the `Over.pullback`/`coverFunctor` spellings of the same functor.
/-- **The descent class is natural in the test.**

Two steps, both already available: `descentMor` is functorial (§2) so
`rep.homEquiv_comp` moves the class along `picEt (C_{k'})`, and
`picEt_crossBaseIso` is a natural isomorphism, so transporting commutes with that
map. This is the clause `representableBy_of_galInvariantEquiv` needs and the one
a `.some`-based `Equiv` cannot supply. -/
theorem descentClass_natural
    {C : Over (Spec (CommRingCat.of k))}
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    {Y : Over (Spec (CommRingCat.of k))}
    (e : Limits.pullback Y.hom (specMapAlgebra k k') ≅ X'.left)
    (he : e.hom ≫ X'.hom = pullback.snd Y.hom (specMapAlgebra k k'))
    {T T' : Over (Spec (CommRingCat.of k))} (f : T ⟶ T') (g : T' ⟶ Y) :
    descentClass rep e he T (f ≫ g)
      = ((coverFunctor (k := k) (k' := k')).op ⋙ picEt C).map f.op
          (descentClass rep e he T' g) := by
  have hstep : rep.homEquiv (descentMor e he T (f ≫ g))
      = (picEt (Scheme.baseChangeField C k')).map
          ((Over.pullback (specMapAlgebra k k')).map f).op
          (rep.homEquiv (descentMor e he T' g)) :=
    (congrArg rep.homEquiv (descentMor_comp e he f g)).trans
      (rep.homEquiv_comp _ _)
  change (picEt_crossBaseIso C k').hom.app (op (baseTest (k' := k') T))
      (rep.homEquiv (descentMor e he T (f ≫ g))) = _
  rw [hstep]
  have hnat := NatTrans.naturality_apply (picEt_crossBaseIso C k').hom
    (X := op (baseTest (k' := k') T')) (Y := op (baseTest (k' := k') T))
    ((Over.pullback (specMapAlgebra k k')).map f).op
    (rep.homEquiv (descentMor e he T' g))
  exact hnat

/-! ## §5. THE DESCENT GOAL -/

set_option maxHeartbeats 1000000 in
-- Heartbeat headroom: as above.
/-- **THE THEOREM THE SEAM'S FOUR ANTECEDENTS ARE ANTECEDENTS OF.**

For a smooth proper curve `C` over an **arbitrary** field `k` and an extension
`k'/k` (finite separable, which is input 1's price — see below):

> a `k'`-scheme `X'` **representing** `picEt (C_{k'})`, whose canonical semilinear
> Galois action has a **Galois quotient** `Y` over `k`, and for which the `G1`
> predicate match holds at every test — yields
> **`(picEt C).RepresentableBy Y`**, i.e. field 1 of clause (1) of
> `Scheme.fgaPicardRepresentability`, over `k`.

**Why this is not `P → P`.** The hypothesis is a representation of the Picard
functor of the **base-changed** curve over `k'`. The conclusion is a representation
of `picEt C` over `k`. Neither `HasPicSchemeEt C` nor the conclusion's own shape
occurs in any hypothesis, and the theorem genuinely crosses the descent step —
which is precisely what `I-1312` found `Picard/PicEtDescentAssembly.lean`'s
`representableByRestrict_of_baseChange` does *not* do.

**What it does not do, stated because it is the natural over-reading.**

* It closes **no** `sorry`. `rep` is the Milne–Kollár campaign's undischarged
  output; `IsGaloisQuotient` at a *glued* (non-affine) `X'` is the open `G2(c)`
  gate; `hcov` is `AJC.picrep.etale-rep.hcov`; and `IsInvariantMatch` is `G1`. All
  four are **explicit hypotheses here**, none is discharged, and clause (1) field 1
  is therefore still witnessed for no curve.
* The `hcov` and `IsInvariantMatch` hypotheses are quantified over **every** test,
  which is what `representableBy_of_galInvariantEquiv` consumes; a lane closing
  either must close it at that generality.
* Per `I-0491` there is no `HasRationalPoint` binder. -/
noncomputable def representableBy_picEt_of_galoisQuotient
    [Algebra.IsSeparable k k'] [Module.Finite k k']
    {C : Over (Spec (CommRingCat.of k))}
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    (ρ : SemilinearGalAction k k' X'.left X'.hom)
    {Y : Over (Spec (CommRingCat.of k))}
    (e : Limits.pullback Y.hom (specMapAlgebra k k') ≅ X'.left)
    (he : e.hom ≫ X'.hom = pullback.snd Y.hom (specMapAlgebra k k'))
    (heq : (pullbackSemilinearGalAction k k' Y.hom).IsEquivariant ρ e.hom)
    (huniv : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k))
      (h : Limits.pullback t (specMapAlgebra k k') ⟶ X'.left),
      h ≫ X'.hom = pullback.snd t (specMapAlgebra k k') →
      (pullbackSemilinearGalAction k k' t).IsEquivariant ρ h →
      ∃! u : {u : T ⟶ Y.left // u ≫ Y.hom = t},
        pullbackBaseChange k k' Y.hom t u.1 u.2 ≫ e.hom = h)
    (hcov : ∀ T : Over (Spec (CommRingCat.of k)), Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      etaleTopologyOver k (Limits.pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)))
    (hmatch : ∀ T, IsInvariantMatch C rep ρ T) :
    (picEt C).RepresentableBy Y :=
  representableBy_of_galInvariantEquiv (k' := k') C hcov
    (galInvariantEquivOfQuotient rep ρ e he heq huniv hmatch)
    (fun {T T'} f g => by
      rw [galInvariantEquivOfQuotient_val, galInvariantEquivOfQuotient_val]
      exact descentClass_natural rep e he f g)

/-- **The same conclusion in the seam's own shape**: clause (1) of
`Scheme.fgaPicardRepresentability`, in full, from the same hypotheses.

The two side conjuncts are free — `LocallyOfFiniteType` needs the descent of
`Picard/PicEtSeparated.lean`'s `locallyOfFiniteType_of_baseChange` and
`IsSeparated` is `isSeparated_of_representableBy_picEt`, both from the bare
representation. So this restates the theorem above at the shape the `sorry`
consumes, and the local-finiteness hypothesis is the *only* thing it adds. -/
theorem seamClauseOne_of_galoisQuotient
    [Algebra.IsSeparable k k'] [Module.Finite k k']
    {C : Over (Spec (CommRingCat.of k))}
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    (ρ : SemilinearGalAction k k' X'.left X'.hom)
    {Y : Over (Spec (CommRingCat.of k))}
    (e : Limits.pullback Y.hom (specMapAlgebra k k') ≅ X'.left)
    (he : e.hom ≫ X'.hom = pullback.snd Y.hom (specMapAlgebra k k'))
    (heq : (pullbackSemilinearGalAction k k' Y.hom).IsEquivariant ρ e.hom)
    (huniv : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k))
      (h : Limits.pullback t (specMapAlgebra k k') ⟶ X'.left),
      h ≫ X'.hom = pullback.snd t (specMapAlgebra k k') →
      (pullbackSemilinearGalAction k k' t).IsEquivariant ρ h →
      ∃! u : {u : T ⟶ Y.left // u ≫ Y.hom = t},
        pullbackBaseChange k k' Y.hom t u.1 u.2 ≫ e.hom = h)
    (hcov : ∀ T : Over (Spec (CommRingCat.of k)), Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      etaleTopologyOver k (Limits.pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)))
    (hmatch : ∀ T, IsInvariantMatch C rep ρ T)
    (hlft : LocallyOfFiniteType Y.hom) :
    ∃ Z : Over (Spec (CommRingCat.of k)),
      Nonempty ((picEt C).RepresentableBy Z) ∧
        LocallyOfFiniteType Z.hom ∧ IsSeparated Z.hom :=
  seamClauseOne_of_representableBy_locallyOfFiniteType C
    ⟨Y, ⟨representableBy_picEt_of_galoisQuotient rep ρ e he heq huniv hcov hmatch⟩,
      hlft⟩

/-! ## §6. The form a consumer actually holds: `IsGaloisQuotient` as a class

The two theorems of §5 take the quotient's four *components*. A consumer holds the
bundled `Prop`-valued `IsGaloisQuotient` instead, so the convenience forms below
exist to spare every consumer the unpacking.

**THE STRONGER CLAIM THIS SECTION MADE IS WITHDRAWN, and it is the same overclaim
`Picard/PicEtQuotientHom.lean` already withdrew one file over** (`I-1405`: "the
data-valued `Equiv` is unprovable, so the gate needs strengthening"). This docstring
said destructuring `IsGaloisQuotient` into the `Type`-valued conclusion **fails**,
that "the component form is not usable as it stands", and that the `RepresentableBy`
version **must** go through `Nonempty`. Refuted by a fresh-context audit, which
elaborated

  `representableBy_picEt_of_galoisQuotient rep ρ hq.choose hq.choose_spec.1`
  `  hq.choose_spec.2.1 hq.choose_spec.2.2 hcov hmatch`

with **no error and no `Nonempty` wrapper**. What is true is narrower: the *tactic*
`obtain`/`Exists.casesOn` cannot eliminate an `∃` into `Type` — but `Exists.choose`,
which *is* `Classical.choice`, can, and the same paragraph was already invoking that
axiom. So the component form was usable all along by a caller willing to write
`.choose`; these forms are a convenience, not a repair.

What survives, and is the genuinely useful half: the **asymmetry in what choice is
spent on**. The `RepresentableBy` form needs `Classical.choice` (however spelled);
the `∃`-shaped clause (1) needs none, because eliminating an `∃` into a `Prop` is
free. That is why `seamClauseOne_of_isGaloisQuotient` is a `theorem` and not a
`noncomputable def`. -/

section Bundled

variable [Algebra.IsSeparable k k'] [Module.Finite k k']
  {C : Over (Spec (CommRingCat.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  {X' : Over (Spec (CommRingCat.of k'))}
  (rep : (picEt (Scheme.baseChangeField C k')).RepresentableBy X')
  (ρ : SemilinearGalAction k k' X'.left X'.hom)
  {Y : Over (Spec (CommRingCat.of k))}

/-- **THE DESCENT GOAL, from the bundled `IsGaloisQuotient`** — the form every
consumer of the `G2` cluster holds.

`Nonempty` because `IsGaloisQuotient` is `Prop`-valued: see the section docstring.
This is the statement a lane closing `G2(c)`, `hcov` or `G1` should aim at. -/
theorem nonempty_representableBy_picEt_of_isGaloisQuotient
    (hq : IsGaloisQuotient ρ Y.hom)
    (hcov : ∀ T : Over (Spec (CommRingCat.of k)), Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      Scheme.etaleTopologyOver k (Limits.pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)))
    (hmatch : ∀ T, IsInvariantMatch C rep ρ T) :
    Nonempty ((picEt C).RepresentableBy Y) := by
  obtain ⟨e, he, heq, huniv⟩ := hq
  exact ⟨representableBy_picEt_of_galoisQuotient rep ρ e he heq huniv hcov hmatch⟩

/-- **Clause (1) of the seam, in full, from the bundled quotient.**

No `Nonempty` wrapper is needed here and none is used: clause (1) is itself an
existential, so this eliminates the quotient's `∃` into a `Prop` and stays
choice-free in that step. **This is the statement the `sorry` of
`Scheme.fgaPicardRepresentability` consumes**, reduced to: a `k'`-side
representation, a Galois quotient of its canonical action, `hcov`, the `G1` match,
and local finiteness of the quotient. -/
theorem seamClauseOne_of_isGaloisQuotient
    (hq : IsGaloisQuotient ρ Y.hom)
    (hcov : ∀ T : Over (Spec (CommRingCat.of k)), Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      Scheme.etaleTopologyOver k (Limits.pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)))
    (hmatch : ∀ T, IsInvariantMatch C rep ρ T)
    (hlft : LocallyOfFiniteType Y.hom) :
    ∃ Z : Over (Spec (CommRingCat.of k)),
      Nonempty ((picEt C).RepresentableBy Z) ∧
        LocallyOfFiniteType Z.hom ∧ IsSeparated Z.hom :=
  seamClauseOne_of_representableBy_locallyOfFiniteType C
    ⟨Y, nonempty_representableBy_picEt_of_isGaloisQuotient rep ρ hq hcov hmatch, hlft⟩

/-- **The action need not be supplied either.**

`semilinearGalActionOfRepresentableBy` (`GaloisDescent/PicEtGaloisAction.lean`)
makes the semilinear action free from `rep`, so the quotient hypothesis can be
stated at *that* action and the `ρ` binder disappears. This is the minimal-input
form: a `k'`-representation, a Galois quotient of the action it determines, `hcov`,
the `G1` match, local finiteness. -/
theorem seamClauseOne_of_isGaloisQuotient_canonical
    (hq : IsGaloisQuotient (semilinearGalActionOfRepresentableBy C rep) Y.hom)
    (hcov : ∀ T : Over (Spec (CommRingCat.of k)), Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      Scheme.etaleTopologyOver k (Limits.pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)))
    (hmatch : ∀ T, IsInvariantMatch C rep (semilinearGalActionOfRepresentableBy C rep) T)
    (hlft : LocallyOfFiniteType Y.hom) :
    ∃ Z : Over (Spec (CommRingCat.of k)),
      Nonempty ((picEt C).RepresentableBy Z) ∧
        LocallyOfFiniteType Z.hom ∧ IsSeparated Z.hom :=
  seamClauseOne_of_isGaloisQuotient rep _ hq hcov hmatch hlft

/-- **THE DEGENERATE SITE, as a theorem: at a trivial Galois group TWO of the four
inputs evaporate.**

This is the non-vacuity measurement of §1 carried through to the headline, and it is
stated in Lean rather than hedged in prose because that is the only form a later
reader cannot skip. Under `[Mono (specMapAlgebra k k')]` and
`[Subsingleton (k' ≃ₐ[k] k')]` — and `k' = k` is such a site, by
`specMapAlgebra_self` and `inferInstance` — the conclusion of
`representableBy_picEt_of_galoisQuotient` follows from `rep` and the quotient
**alone**: `hcov` comes from `etaleTopology_generate_coverSelfSection_of_mono` and
`hmatch` from `isInvariantMatch_of_subsingleton`, neither supplied from outside.

**So satisfiability of the two named antecedents is established and their CONTENT is
not.** Anyone pricing `G1` or `hcov` against this file's theorems must exhibit a
model at an extension with a *nontrivial* automorphism; at every model exhibited
here, the "four inputs" are two. Same trap
`Picard/PicEtDescentRepresentability.lean` records for `hcov` on its own, now
measured for the pair. -/
noncomputable def representableBy_picEt_of_degenerate
    [Mono (specMapAlgebra k k')] [Subsingleton (k' ≃ₐ[k] k')]
    (e : Limits.pullback Y.hom (specMapAlgebra k k') ≅ X'.left)
    (he : e.hom ≫ X'.hom = pullback.snd Y.hom (specMapAlgebra k k'))
    (heq : (pullbackSemilinearGalAction k k' Y.hom).IsEquivariant ρ e.hom)
    (huniv : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k))
      (h : Limits.pullback t (specMapAlgebra k k') ⟶ X'.left),
      h ≫ X'.hom = pullback.snd t (specMapAlgebra k k') →
      (pullbackSemilinearGalAction k k' t).IsEquivariant ρ h →
      ∃! u : {u : T ⟶ Y.left // u ≫ Y.hom = t},
        pullbackBaseChange k k' Y.hom t u.1 u.2 ≫ e.hom = h) :
    (picEt C).RepresentableBy Y :=
  representableBy_picEt_of_galoisQuotient rep ρ e he heq huniv
    (fun T => etaleTopology_generate_coverSelfSection_of_mono T)
    (fun T => isInvariantMatch_of_subsingleton C rep ρ T)

end Bundled

end PicScheme

end Scheme

end AlgebraicGeometry
