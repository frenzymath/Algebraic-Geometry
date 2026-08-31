/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianDataAbelSurj
import AlgebraicJacobian.Picard.Pic0ChartTestPoint
import AlgebraicJacobian.Picard.Pic0AtlasFromDivRep
-- The four modules below are imported so that every declaration this file's docstrings CITE is
-- in its own import closure.  A cited name that resolves only by `grep` is a name this file
-- cannot see, and that failure mode has recurred four times in this project (I-1073, I-0994).
import AlgebraicJacobian.Picard.JacobianDataAbelSquareVacuity
import AlgebraicJacobian.Picard.JacobianDataAbelEffectivePoint
import AlgebraicJacobian.Picard.DivisorFamilyFieldSurj
import AlgebraicJacobian.Picard.JacobianDataAbelDegreeWindow

/-!
# DAT-J's `quasiCompact` field: the Abel map is not an input, it is `rep.homEquiv.symm`

`JacobianData` (`Picard/JacobianData.lean:87`) has four fields.  `rep` is the representability
antecedent; `locallyOfFiniteType` has a producer (`Picard/Pic0AtlasFiniteType.lean`).  The
remaining field, `quasiCompact`, had **no producer of any shape**: every route in the tree ends
in a hypothesis nothing supplies.

* `quasiCompact_gluedHom` (`Picard/JacobianDataCharts.lean:164`) wants `[Finite ι]`, and the
  atlas is class-indexed.
* `JacobianData.ofChartsOfAbelImage` / `ofChartsOfAbelLifts`
  (`Picard/JacobianDataAbelImage.lean:159`, `Picard/JacobianDataAbelSurj.lean:193`) want a
  morphism `abel : DivScheme g ⟶ J.left`.
* `exists_residueField_lift_of_abelCompatible` (`Picard/JacobianDataAbelSquare.lean:172`) wants
  an `IsAbelClassifyCompatible` square *and* a `pt` function, neither with a producer.

This file removes the middle two.  The observation is that **the Abel morphism is not a
construction the tree owes**: `divSchemeOver` is a test object of `Over (Spec k)`, so a
degree-zero class `lam : pic⁰(divSchemeOver …)` names a morphism `divSchemeOver … ⟶ J`
outright, as `rep.homEquiv.symm lam`, for *any* representing object `J`.  Its `.left` is the
`abel` every `JacobianData` producer above asks for.

**WHAT THIS IS AND IS NOT — corrected in place after a fresh-context audit (`I-1071`–`I-1074`),
because the first draft of this header priced it wrongly and the wrong price is the dangerous
part.**

It is a **change of coordinates**, not a reduction in the number of obligations.  The first
draft said "three inputs with no producer (`abel`, the square, the lifts) become two"; that is
**false**, and the refutation is the same `Equiv` the file runs on.  `homEquiv` is a
*bijection*, so the passage runs both ways: `abelOfPic0Class rep (rep.homEquiv abel) = abel`,
and per-point lifts of an arbitrary `abel` give `hcl` at `lam := rep.homEquiv abel`.  So the
morphism-coordinates obligation and the class-coordinates obligation are **the same
obligation**, and no input was removed.

Two further corrections of record:

* **The square was already known free, for an *arbitrary* `abel`.**
  `Picard/JacobianDataAbelSquareVacuity.lean` (landed before this file) proves
  `exists_isAbelClassifyCompatible`: because the interface takes the point map `pt` as an
  *argument*, a consumer may choose it, and the square becomes a case split with no geometry.
  So "the square is free at *this* `abel`" is a weaker statement than what the tree already
  had, and citing `I-0525` as though the gap were live here was wrong.
* **What survives is one statement in either coordinate system.**  That is worth stating
  because `dat-j`'s row once counted the square as a separate obligation, and it is not one.

What this file therefore contributes is the **Pic-side spelling** of that single obligation,
`JacobianData.ofPic0ClassSurjective` (the assembly in one signature), and the two measurements
below — the extension-tolerance characterisation and the falsifiability of `hcl`.

**The single surviving statement, spelled here as a class condition.**
`quasiCompact_of_pic0_class_surjective` below takes exactly:

> for every point `y` of `J.left`, some `q : overSpec k κ(y) ⟶ divSchemeOver …` with
> `pic0Map C q lam = rep.homEquiv (Over.testPoint y)`

— *the class of `y` is pulled back from `lam` along some field point of the divisor scheme*.
That is a statement about classes only.  It is what the effectivity chain
(`exists_effective_deg_eq_of_pic0_at_point`, `Picard/JacobianDataAbelEffectivePoint.lean`) and
the fibrewise classifier (`effectiveDivisorClassifyZar`,
`Picard/DivisorFamilyFieldSurj.lean:217`) between them are shaped to produce.

## Scope, stated because this file closes no gate

`rep`, `lam` and `hcl` are all **hypotheses**, and nothing here produces any of them.  No
antecedent of the north star is discharged.

`hcl` is *not* a weakening of `Function.Surjective abel.base`: it is that statement in class
coordinates, and the audit closed the round trip in both directions.  A reader pricing this
route should count **one** open statement, in whichever spelling, and should not add the
morphism or the square as separate items — the square is free for an arbitrary `abel` already
(`Picard/JacobianDataAbelSquareVacuity.lean`).

The honest residue, recorded elsewhere and unchanged: `effectiveDivisorClassifyZar` pins
`deg D = g` **on the nose**, which the window form of the effectivity leg does not deliver
(`Picard/JacobianDataAbelDegreeWindow.lean`).  And that `g` is not a free parameter a producer
may choose: the classifier's own `hχ : χ(𝒪) = 1 − g` is an equation about the *curve*, so it
determines `g` uniquely — two parameters cannot both satisfy it.  Measured, not argued.

## Main declarations

* `AlgebraicGeometry.abelOfPic0Class` — the Abel morphism of a degree-zero class on the divisor
  scheme, `rep.homEquiv.symm lam`.  No construction; the universal property names it.
* `AlgebraicGeometry.abelOfPic0Class_comp_class` — its defining property: the class of a
  composite `q ≫ abel` is `pic0Map C q lam`.  This is the compatibility square, proved.
* `AlgebraicGeometry.residueField_lift_of_pic0_class` — the per-point lift obligation of
  `JacobianData.ofAbelLifts`, from the class statement.
* `AlgebraicGeometry.quasiCompact_of_pic0_class_surjective` — **the qc field**, from `rep`, a
  class `lam` on the divisor scheme, and `hcl`.
* `AlgebraicGeometry.JacobianData.ofPic0ClassSurjective` — the three-input `JacobianData`
  producer: `rep`, the lft certificate, and `hcl`.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

section Abel

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
variable {A B : X.CurveDivisor} {g r₁ r₂ : ℕ}
variable {b₁ : Module.Basis (Fin r₁) k ↥(Scheme.divisorSections k B ⊤)}
variable {b₂ : Module.Basis (Fin r₂) k ↥(Scheme.divisorSections k (A + B) ⊤)}

/-- **The Abel morphism of a degree-zero class on the divisor scheme.**

`divSchemeOver … : Over (Spec k)` is a test object of the degree-zero Picard functor, so a class
`lam : pic⁰(divSchemeOver …)` *is* a morphism to any representing object, by the universal
property.  No geometry is used: this is `rep.homEquiv.symm`.

Every `JacobianData` producer of `Picard/JacobianDataAbelImage.lean` and
`Picard/JacobianDataAbelSurj.lean` takes such a morphism as an unproduced hypothesis `abel`.
Its `.left` (`abelOfPic0Class_left` below is `rfl`) is that hypothesis, so those producers are
reachable from a class. -/
def abelOfPic0Class {J : Over (Spec (.of k))}
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (lam : pic0Subgroup C (divSchemeOver k A B g r₁ r₂ b₁ b₂)) :
    divSchemeOver k A B g r₁ r₂ b₁ b₂ ⟶ J :=
  rep.homEquiv.symm lam

/-- The underlying morphism of schemes out of `DivScheme g` — the `abel` of
`JacobianData.ofAbelImage`. -/
@[simp]
lemma abelOfPic0Class_left {J : Over (Spec (.of k))}
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (lam : pic0Subgroup C (divSchemeOver k A B g r₁ r₂ b₁ b₂)) :
    (abelOfPic0Class rep lam).left
      = ((rep.homEquiv.symm lam : divSchemeOver k A B g r₁ r₂ b₁ b₂ ⟶ J)).left :=
  rfl

/-- **The compatibility square, proved rather than assumed.**

The class of a composite `q ≫ abel` is the restriction `pic0Map C q lam` of `lam` along `q`.
This is `RepresentableBy.homEquiv_comp` after `Equiv.apply_symm_apply`, and it is what
`IsAbelClassifyCompatible` (`Picard/JacobianDataAbelSquare.lean:147`) posits for an abstractly
given `abel`.

Recorded as the reason the "groups agree ≠ maps agree" gap (`I-0525`) does not arise here: the
gap is about relating two *independently named* morphisms, and this `abel` is named by the same
equivalence that names the classes. -/
lemma abelOfPic0Class_comp_class {J : Over (Spec (.of k))}
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (lam : pic0Subgroup C (divSchemeOver k A B g r₁ r₂ b₁ b₂))
    {T : Over (Spec (.of k))} (q : T ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂) :
    rep.homEquiv (q ≫ abelOfPic0Class rep lam) = pic0Map C q lam := by
  rw [abelOfPic0Class, rep.homEquiv_comp (f := q), Equiv.apply_symm_apply]
  rfl

/-- **A field point whose class is pulled back from `lam` lifts through the Abel morphism.**

If `q : overSpec k κ(y) ⟶ divSchemeOver …` carries `lam` to the class of the field point of `y`,
then `q ≫ abelOfPic0Class rep lam` **is** that field point — not merely a morphism with the same
class.  The upgrade is `Equiv.injective`: `homEquiv` is an equivalence, so two morphisms into `J`
with equal classes are equal.

This is the step that would otherwise be the compatibility square. -/
lemma comp_abelOfPic0Class_eq_testPoint {J : Over (Spec (.of k))}
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (lam : pic0Subgroup C (divSchemeOver k A B g r₁ r₂ b₁ b₂)) (y : J.left)
    (q : overSpec k (Over.testPointField y) ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂)
    (hq : pic0Map C q lam = rep.homEquiv (Over.testPoint y)) :
    q ≫ abelOfPic0Class rep lam = Over.testPoint y := by
  apply rep.homEquiv.injective
  rw [abelOfPic0Class_comp_class]
  exact hq

/-- **The per-point residue-field lift, from the class statement.**

`Over.testPoint y` has carrier `fromSpecResidueField y` by definition
(`Over.testPoint_left`), so the previous lemma delivers exactly the hypothesis
`surjective_of_forall_exists_residueField_lift` (`Picard/JacobianDataAbelSurj.lean:82`) and
hence `JacobianData.ofAbelLifts` consume — with the morphism and the square supplied here
instead of assumed. -/
lemma residueField_lift_of_pic0_class {J : Over (Spec (.of k))}
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (lam : pic0Subgroup C (divSchemeOver k A B g r₁ r₂ b₁ b₂))
    (hcl : ∀ y : J.left,
      ∃ q : overSpec k (Over.testPointField y) ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂,
        pic0Map C q lam = rep.homEquiv (Over.testPoint y))
    (y : J.left) :
    ∃ q : Spec (J.left.residueField y) ⟶ DivScheme k A B g r₁ r₂ b₁ b₂,
      q ≫ (abelOfPic0Class rep lam).left = J.left.fromSpecResidueField y := by
  obtain ⟨q, hq⟩ := hcl y
  exact ⟨q.left, congrArg Over.Hom.left
    (comp_abelOfPic0Class_eq_testPoint rep lam y q hq)⟩

/-- **DAT-J's `quasiCompact` field, from a class on the divisor scheme.**

Given a representation `rep` of the degree-zero Picard functor by `J`, a degree-zero class `lam`
on `divSchemeOver …`, and the statement that *every* point of `J.left` has its class pulled back
from `lam` along some field point of the divisor scheme, the structure morphism `J.hom` is
quasi-compact.

The chain: `hcl` gives per-point lifts through `abelOfPic0Class rep lam`
(`residueField_lift_of_pic0_class`), those give point surjectivity
(`surjective_of_forall_exists_residueField_lift`), `DivScheme g` is a compact space
(`compactSpace_divScheme`, DD-Q) and `Spec k` is affine, so DJ-0's
`quasiCompact_of_surjective` applies.

**What is and is not discharged.**  `lam` and `hcl` are hypotheses; this proves the implication.
What it removes from the previous obligation list is the Abel *morphism* and the compatibility
*square* — neither is an input any more. -/
theorem quasiCompact_of_pic0_class_surjective {J : Over (Spec (.of k))}
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (lam : pic0Subgroup C (divSchemeOver k A B g r₁ r₂ b₁ b₂))
    (hcl : ∀ y : J.left,
      ∃ q : overSpec k (Over.testPointField y) ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂,
        pic0Map C q lam = rep.homEquiv (Over.testPoint y)) :
    QuasiCompact J.hom :=
  quasiCompact_of_forall_residueField_lift_from_divScheme A B g r₁ r₂ b₁ b₂ J
    (abelOfPic0Class rep lam).left (residueField_lift_of_pic0_class rep lam hcl)

/-! ### The `κ(y)` pin was never what `QuasiCompact` needed

`hcl` above pins the lift's source to `overSpec k κ(y)`.  That pin is **not needed**: point
surjectivity only asks for *some* point of the divisor scheme lying over `y`, and the residue
field of the test that produces it is irrelevant.  So a divisor produced over a finite separable
*splitting field* `L` of `κ(y)` — which is what the effectivity chain
(`Picard/JacobianDataAbelEffectivePoint.lean`) actually delivers — is accepted as produced, with
no descent step.

**SCOPED after a fresh-context audit (`I-1072`), because the first draft of this heading claimed
more than the theorem.**  It said the widening "deletes an obligation two files record as the
honest remaining cost".  It does not delete anything: the extension-tolerant hypothesis is
**equivalent** to bare `Function.Surjective (abelOfPic0Class rep lam).left.base`, not weaker
than it (converse: pick `x` in the fibre over `y`, take `T := overSpec k κ(x)` with `q :=
Over.testPoint x`).  Since `quasiCompact_of_surjective_from_divScheme` already consumed bare
surjectivity, DJ-0 was never asking for the pin in the first place.

What survives, and it is a characterisation rather than a discount: the `Spec κ(y)` pin in
`JacobianData.ofAbelLifts`'s `hlift` (`Picard/JacobianDataAbelSurj.lean:153`) is an artefact of
that signature, not a requirement of quasi-compactness.  A lane reading those two files' "what
remains is DESCENT" should check whether its consumer is the qc field — for that consumer there
is nothing to descend — and any *other* consumer of the `hlift` signature still owes it. -/

/-- **The extension-tolerant lift hypothesis gives point surjectivity.**

For each `y`, a `k`-test `T` with a point, a morphism `e : T ⟶ overSpec k κ(y)`, and a
divisor-scheme morphism `q` whose class matches that of `e ≫ Over.testPoint y`.  For a field
extension `L ⊇ κ(y)` this is `T := overSpec k L`, so the splitting field the effectivity chain
lands over is accepted directly.

Strictly weaker than `hcl`: `extensionTolerant_of_kappaPinned` below is the `T := overSpec k κ(y)`,
`e := 𝟙` face. -/
theorem surjective_of_extensionTolerant_lift {J : Over (Spec (.of k))}
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (lam : pic0Subgroup C (divSchemeOver k A B g r₁ r₂ b₁ b₂))
    (h : ∀ y : J.left, ∃ (T : Over (Spec (.of k))) (_ : Nonempty T.left)
      (e : T ⟶ overSpec k (Over.testPointField y))
      (q : T ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂),
      pic0Map C q lam = rep.homEquiv (e ≫ Over.testPoint y)) :
    Function.Surjective (abelOfPic0Class rep lam).left.base := by
  intro y
  obtain ⟨T, ⟨p⟩, e, q, hq⟩ := h y
  have hqt : q ≫ abelOfPic0Class rep lam = e ≫ Over.testPoint y := by
    apply rep.homEquiv.injective
    rw [abelOfPic0Class_comp_class]
    exact hq
  refine ⟨q.left.base p, ?_⟩
  have h2 := congrArg (fun (m : T ⟶ J) => m.left.base p) hqt
  refine h2.trans ?_
  exact Over.testPoint_base y (e.left.base p)

/-- **The qc field from the extension-tolerant hypothesis** — the form to hand a producer,
since it accepts a divisor produced over any extension of the residue field. -/
theorem quasiCompact_of_extensionTolerant_lift {J : Over (Spec (.of k))}
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (lam : pic0Subgroup C (divSchemeOver k A B g r₁ r₂ b₁ b₂))
    (h : ∀ y : J.left, ∃ (T : Over (Spec (.of k))) (_ : Nonempty T.left)
      (e : T ⟶ overSpec k (Over.testPointField y))
      (q : T ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂),
      pic0Map C q lam = rep.homEquiv (e ≫ Over.testPoint y)) :
    QuasiCompact J.hom :=
  quasiCompact_of_surjective_from_divScheme A B g r₁ r₂ b₁ b₂ J
    (abelOfPic0Class rep lam).left (surjective_of_extensionTolerant_lift rep lam h)

/-- The `κ(y)`-pinned hypothesis is the `T := overSpec k κ(y)`, `e := 𝟙` face of the
extension-tolerant one — recorded so the generalisation is visibly not a weakening of the
*conclusion*, only of the hypothesis. -/
theorem extensionTolerant_of_kappaPinned {J : Over (Spec (.of k))}
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (lam : pic0Subgroup C (divSchemeOver k A B g r₁ r₂ b₁ b₂))
    (hcl : ∀ y : J.left,
      ∃ q : overSpec k (Over.testPointField y) ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂,
        pic0Map C q lam = rep.homEquiv (Over.testPoint y)) (y : J.left) :
    ∃ (T : Over (Spec (.of k))) (_ : Nonempty T.left)
      (e : T ⟶ overSpec k (Over.testPointField y))
      (q : T ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂),
      pic0Map C q lam = rep.homEquiv (e ≫ Over.testPoint y) := by
  obtain ⟨q, hq⟩ := hcl y
  refine ⟨overSpec k (Over.testPointField y), ⟨Nonempty.some inferInstance⟩, 𝟙 _, q, ?_⟩
  rw [Category.id_comp]
  exact hq

/-! ### Falsifiability: the hypothesis has content

`hcl` implies `CompactSpace J.left`, so it is **refuted** at any representing object whose space
is not compact.  Recorded because a hypothesis nobody can refute is the shape the 2026-07-29
audit found 17 times: `HasDivFunctor`'s field asserted only that a category is nonempty. -/

/-- `hcl` implies compactness of the representing object's space — hence it is false whenever
that space is non-compact, so the hypothesis is falsifiable rather than vacuous. -/
theorem compactSpace_of_pic0_class_surjective {J : Over (Spec (.of k))}
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (lam : pic0Subgroup C (divSchemeOver k A B g r₁ r₂ b₁ b₂))
    (hcl : ∀ y : J.left,
      ∃ q : overSpec k (Over.testPointField y) ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂,
        pic0Map C q lam = rep.homEquiv (Over.testPoint y)) :
    CompactSpace J.left :=
  compactSpace_of_surjective (abelOfPic0Class rep lam).left
    (surjective_of_forall_exists_residueField_lift _
      (residueField_lift_of_pic0_class rep lam hcl))

/-! ### `lam` is PRODUCED, not assumed — the chart layer's own `divRep` supplies it

The class `lam` above is not a second open input.  `chartValueTrans`
(`Picard/Pic0AtlasFromDivRep.lean:176`) is a natural transformation
`divFunctor C π n ⟶ pic0TypeFunctor C`, built from `chartValue_mem_pic0Subgroup`; applied at
the representing object to the universal element of a divisor-functor representation it yields
a degree-zero class on that object outright.

So a lane holding the `divRep` the chart layer *already assumes* (`abelSigmaChart` takes it,
`mixedParamChart` takes one per index) holds `lam` at no cost, and the qc field's hypothesis
list is **one** statement, not two.  Recorded here because the same `divRep` appears on both
sides and it is easy to double-count it. -/

/-- **The degree-zero class on the divisor scheme, from a divisor-functor representation.**

The universal element of `divRep` pushed through `chartValueTrans` — the same construction the
Abel chart map uses, evaluated at the representing object itself.  Takes exactly the data
`abelSigmaChart` does (`rep`, the twist exponent `m`, the chart index `Z`, and its legality
`hdeg`), and no more. -/
def lamOfDivRep {π : C.left ⟶ P1 k} [IsAffineHom π] (n : ℕ) {D : Over (Spec (.of k))}
    (divRep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ)) :
    pic0Subgroup C D :=
  (chartValueTrans C π n m Z hdeg).app (op D) (divRep.homEquiv (𝟙 D))

/-- **The qc field with `lam` supplied by the chart layer's own representation** — the form in
which the field costs exactly ONE open statement.

Everything except `hcl` is data the chart layer already carries: `rep` is antecedent 3, `hlft`
is discharged at the divisor-representability carrier (`Picard/Pic0AtlasFiniteType.lean`), and
`divRep`/`m`/`Z`/`hdeg` are precisely `abelSigmaChart`'s arguments. -/
theorem quasiCompact_of_divRep_of_lift {π : C.left ⟶ P1 k} [IsAffineHom π] (n : ℕ)
    (divRep : (divFunctor C π n).RepresentableBy (divSchemeOver k A B g r₁ r₂ b₁ b₂))
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    {J : Over (Spec (.of k))} (rep : (pic0TypeFunctor C).RepresentableBy J)
    (hcl : ∀ y : J.left,
      ∃ q : overSpec k (Over.testPointField y) ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂,
        pic0Map C q (lamOfDivRep n divRep m Z hdeg)
          = rep.homEquiv (Over.testPoint y)) :
    QuasiCompact J.hom :=
  quasiCompact_of_pic0_class_surjective rep (lamOfDivRep n divRep m Z hdeg) hcl

/-- **The `JacobianData` producer with the qc field discharged from a class.**

Three inputs: the representation, the locally-of-finite-type certificate (which
`Picard/Pic0AtlasFiniteType.lean` supplies — free at the divisor-representability lane's own
carrier), and `hcl`.  Compare `JacobianData.ofAbelLifts`
(`Picard/JacobianDataAbelSurj.lean:149`), which needs the same `rep` and `hlft` plus an
unproduced `abel` and per-point lifts *of that morphism*. -/
def JacobianData.ofPic0ClassSurjective (C) [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] (J : Over (Spec (.of k)))
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (hlft : LocallyOfFiniteType J.hom)
    (lam : pic0Subgroup C (divSchemeOver k A B g r₁ r₂ b₁ b₂))
    (hcl : ∀ y : J.left,
      ∃ q : overSpec k (Over.testPointField y) ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂,
        pic0Map C q lam = rep.homEquiv (Over.testPoint y)) :
    JacobianData C :=
  JacobianData.ofRepresentableBy C J rep hlft
    (quasiCompact_of_pic0_class_surjective rep lam hcl)

@[simp]
lemma JacobianData.ofPic0ClassSurjective_J (C) [SmoothOfRelativeDimension 1 C.hom]
    [IsProper C.hom] [GeometricallyIrreducible C.hom] (J : Over (Spec (.of k)))
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (hlft : LocallyOfFiniteType J.hom)
    (lam : pic0Subgroup C (divSchemeOver k A B g r₁ r₂ b₁ b₂))
    (hcl : ∀ y : J.left,
      ∃ q : overSpec k (Over.testPointField y) ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂,
        pic0Map C q lam = rep.homEquiv (Over.testPoint y)) :
    (JacobianData.ofPic0ClassSurjective C J rep hlft lam hcl).J = J :=
  rfl

end Abel

end

end AlgebraicGeometry
