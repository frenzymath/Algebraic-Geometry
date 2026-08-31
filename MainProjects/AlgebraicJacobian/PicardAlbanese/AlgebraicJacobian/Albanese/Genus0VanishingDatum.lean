/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Albanese.Genus0Terminal
import AlgebraicJacobian.Picard.Pic0VanishingRoute

/-!
# S11 with the datum SUPPLIED from the vanishing, not assumed alongside it

`Albanese/Genus0Terminal.lean` closes the uniqueness half of the frozen
`exists_unique_ofCurve_comp` in the degenerate case, and every one of its statements takes a
`(d : JacobianData C)` as its first argument.  That binder is not free: `JacobianData` is the
Wave-4 north star.

`Picard/Pic0VanishingRoute.lean` produces a `JacobianData` from the *same* vanishing hypothesis
that `Genus0Terminal`'s theorems already assume.  Feeding it to those theorems supplies the
binder from the hypothesis already in hand, so the chain below needs no datum from elsewhere.

## Two things a draft of this header claimed and I have deleted (`I-1575`)

Both were wrong in the direction that flatters this file, which is the direction nobody checks.

* It said the `AJCR.w6-albanese.genus0` row **prices the leaf as gated behind `divRep`**, and
  that this file refutes that.  The row does not.  It opens with `GATE WAS INHERITED FOLKLORE`,
  carries `depends_on: []`, and states that D6 gates the `Sym^g` fork and not this leaf; its only
  "far gate" text is a *quotation* of the worksheet, presented as the thing being refuted — in
  run 0078, by a different argument.  **The row already agrees**, and arguing with it was the
  overclaim.
* It said **"the datum binder and the vanishing hypothesis were never independent"**, and that a
  file assuming both assumes the second twice.  False.  `Genus0Terminal`'s theorems hold at an
  *arbitrary* `d`.  The statements below instantiate at one carrier, and their conclusions' types
  mention `(jacobianData_of_vanishing C h).J`, so a consumer holding a *different* datum cannot
  use them.  The binder is **instantiated, not removed** — this is the
  `d := Over.mk (𝟙 (Spec k))` face of a strictly more general theorem, not a strengthening of it.

So read the declarations below as: *at this carrier*, the S11 chain runs from the vanishing
alone.  That is smaller than "the leaf is ungated" and it is what is proved.

## What is unconditional here, and what is not

Unconditional given the vanishing: existence of the datum, terminality of its representing
object, and the uniqueness clause of the Albanese property.

**Still open, and it is the same debt `Genus0Terminal` names:** the vanishing itself.
`genus C = 0 → pic0Subgroup C T = ⊥` is real curve theory and no declaration in this tree
proves it.  Nothing below weakens that; what changes is that the vanishing is now the *only*
input, where before it was the vanishing *plus* a datum.

Note what has changed *around* it, though, because it decides where to attack the implication:
its antecedent is no longer out of reach.  `Curve/P1Curve.lean` supplies the three curve binders
at `P1.asOver k` and `Curve/P1H1Vanishing.lean` proves `genus (P1.asOver k) = 0` there, for an
arbitrary field — so the implication now has a concrete instance to be proved *at*, rather than
only a variable `C`.  What it needs at that instance is the relative statement
`Pic(ℙ¹_T) ≅ Pic(T) × ℤ`; a base-field-only computation would not discharge the `∀ T` binder.

Also still open, and equally unchanged: the *existence* half of the Albanese `∃!`, which is
Milne I 3.9.  It appears as the explicit `hex` hypothesis, exactly as upstream.

## Main declarations

* `AlgebraicGeometry.jacobianData_of_vanishing` — the datum from `pic0Subgroup C T = ⊥`, i.e.
  in the spelling `Genus0Terminal` uses.
* `AlgebraicGeometry.isTerminal_jacobianData_of_vanishing` — that datum's representing object is
  terminal.
* `AlgebraicGeometry.existsUnique_ofCurve_comp_of_vanishing` — **S11's uniqueness clause running
  from the vanishing alone**, at this carrier.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

variable (C) in
/-- **The datum, from the `= ⊥` spelling of the vanishing.**

`Genus0Terminal` states its hypothesis as `pic0Subgroup C T = ⊥`; the producer in
`Pic0VanishingRoute` takes the `Subsingleton` form.  They are interderivable
(`subsingleton_of_pic0Subgroup_eq_bot`), so this is the producer in the spelling the
consumers below want. -/
def jacobianData_of_vanishing
    (h : ∀ T : Over (Spec (.of k)), pic0Subgroup C T = ⊥) :
    JacobianData C :=
  jacobianData_of_subsingleton C fun T => subsingleton_of_pic0Subgroup_eq_bot (h T)

variable (C) in
/-- **Terminality of the datum built from the vanishing.**

`JacobianData.isTerminal_of_pic0Subgroup_eq_bot` concludes `IsTerminal d.J` from a datum `d`
plus the vanishing.  Here the datum comes from the vanishing, so no `d` is assumed.

Cheap, and honestly so: the representing object is `Over.mk (𝟙 (Spec k))` by construction, so
`Over.mkIdTerminal` proves the same goal directly.  The composite is kept because it is the
upstream theorem *applied*, which is the check that the producer's output is admissible input
there — a statement can be sorry-free and have no site (`I-1463`). -/
def isTerminal_jacobianData_of_vanishing
    (h : ∀ T : Over (Spec (.of k)), pic0Subgroup C T = ⊥) :
    IsTerminal (jacobianData_of_vanishing C h).J :=
  JacobianData.isTerminal_of_pic0Subgroup_eq_bot _ h

end

variable (C) in
/-- **S11's uniqueness clause with the datum supplied rather than assumed.**

`JacobianData.existsUnique_ofCurve_comp_of_pic0Subgroup_eq_bot` is the upstream assembly; it
takes a datum, the vanishing, surjectivity of the curve's structure morphism, a rational
point, and the existence half `hex`.  This is the same theorem with the datum *built from the
vanishing*, so the hypotheses are: the vanishing, a nonempty curve, a rational point, and `hex`.

**Not a generalisation of the upstream theorem** (`I-1575`): that one holds at an arbitrary `d`,
and this is its `d := jacobianData_of_vanishing C h` face.  The conclusion's type names that
carrier, so a consumer holding a different datum must use the upstream form.  What is bought is
that the chain runs from the vanishing alone, with no datum from elsewhere.

`hex` is Milne I 3.9 and is still open, exactly as upstream. -/
theorem existsUnique_ofCurve_comp_of_vanishing
    (h : ∀ T : Over (Spec (.of k)), pic0Subgroup C T = ⊥) (hs : Surjective C.hom)
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) {A : Over (Spec (.of k))} (f : C ⟶ A)
    (hex : ∃ g : (jacobianData_of_vanishing C h).J ⟶ A,
      f = (jacobianData_of_vanishing C h).ofCurve P ≫ g) :
    ∃! g : (jacobianData_of_vanishing C h).J ⟶ A,
      f = (jacobianData_of_vanishing C h).ofCurve P ≫ g :=
  JacobianData.existsUnique_ofCurve_comp_of_pic0Subgroup_eq_bot _ h hs P f hex

end AlgebraicGeometry
