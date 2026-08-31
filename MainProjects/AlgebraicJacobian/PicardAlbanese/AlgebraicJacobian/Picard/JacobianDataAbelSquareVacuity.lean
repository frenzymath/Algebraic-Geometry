/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianDataAbelSquare

/-!
# The Abel-compatibility square demands nothing, and its consumer is circular

Roadmap `AJCR.w4-rep.datum.dat-j` records DAT-J as owing **three** things, the first being

> 1. `IsAbelClassifyCompatible` for the campaign's Abel morphism — bookkeeping-shaped, but a
>    real statement, and nobody has written it;

with the fibrewise Riemann–Roch effectivity input `heff` as a *separate* item 2.  **That
partition does not survive contact with the interface**, and this file measures why in Lean
rather than in prose.

## The measurement

`IsAbelClassifyCompatible … abel pt` takes the point map `pt` as an **argument**, not as
fixed data.  So a consumer entitled to choose `pt` can choose it to be the classifier
composite itself, and the square becomes `dif_pos` — for an **arbitrary** `abel`, over an
arbitrary curve, with no geometry whatsoever:

* `AlgebraicGeometry.exists_isAbelClassifyCompatible` below. Its only hypothesis beyond
  `abel` is that the `pt` *type* is inhabited at all (`pt0`), which supplies the junk branch
  of the case split.

So obligation 1 is not "bookkeeping-shaped but real".  It is **free**, in the precise sense
that `∃ pt, IsAbelClassifyCompatible … abel pt` is a theorem.  This is the recorded
"isolating a residue as a class" failure mode (inbox `I-0605`): a residue whose witness is
existentially quantified over the very datum that would make it non-trivial demands nothing,
and the cheap test is to try to inhabit it with junk **before** treating it as a reduction.

## The consequence for the consumer, which is the part that matters

`exists_residueField_lift_of_abelCompatible` (`Picard/JacobianDataAbelSquare.lean`) consumes
`pt`, `hsq` and `heff` and concludes

> `∀ y, ∃ q : Spec κ(y) ⟶ DivScheme g, q ≫ abel = J.fromSpecResidueField y`.

Instantiate it at the `pt` produced above and read `heff`: it asks for a `D` with
`pt κ(y) D = J.fromSpecResidueField y`, which at that `pt` unfolds to
`(classify D).left ≫ abel = J.fromSpecResidueField y` — **verbatim the conclusion**.  So at
the `pt` that makes `hsq` free, the theorem is a tautology: `heff` has silently absorbed all
of the content that item 1 appeared to carry.  `exists_residueField_lift_of_abelCompatible`
is therefore a *reduction only relative to a `pt` pinned independently* — pinned to the
campaign Abel map's own point map — and the interface never pins it.

`heff_iff_conclusion_of_pt_eq` records that circularity as a lemma, so the claim is
machine-checked and not an argument in a docstring.

## What DAT-J actually owes, restated

**One** statement, not two, and it is strictly stronger than the "Riemann–Roch over a field"
that item 2 describes: for every point `y` of `J`, an effective degree-`g` divisor on the
curve over `κ(y)` **whose classifying morphism composes with `abel` to `fromSpecResidueField
y`**.  The Riemann–Roch half produces the divisor; the compatibility half is the honest
residue, and it cannot be split off into a separate row because any `pt` making the split
statable is either the pinned campaign one (in which case there is no separate row to prove)
or a chosen one (in which case the split is vacuous).

Spelling of the Riemann–Roch half stays binding per `informal/w4-datj-worksheet.md` §0.5:
`exists_effective_of_picClass` / `riemann_inequality`, **never** `riemann_inequality_curve`
(it imports `Challenge.lean` and would create an import cycle).

## What this does NOT do

It produces no lift, no `JacobianData`, and no effectivity witness — it **removes a row**
from DAT-J's ledger by showing that row was free, and relocates its content onto the row
that was already there.  Critical-path §7.6 (L8) is untouched.

## Main declarations

* `AlgebraicGeometry.exists_isAbelClassifyCompatible` — the square is satisfiable for an
  arbitrary `abel`: obligation 1 of the `dat-j` row is vacuous.
* `AlgebraicGeometry.heff_iff_conclusion_of_pt_eq` — at such a `pt`, the remaining
  hypothesis `heff` is equivalent to the conclusion it was supposed to imply.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

section AbelSquareVacuity

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftAbelSquareVac :
    C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
  [IsDominant pi]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g : ℕ)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
variable (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
variable (r1 r2 : ℕ)
variable (b1 : Module.Basis (Fin r1) k
  ↥(divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(divisorSections k
    ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤))

local notation "DivSch" =>
  DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm)

/-- **The point map that makes the square free**: the classifier composite where the divisor
is effective of degree `g`, and an arbitrary supplied fallback elsewhere.

The case split is on exactly the two hypotheses `IsAbelClassifyCompatible` quantifies over,
so on its branch the square holds by `dif_pos`.  `pt0` exists only to inhabit the other
branch — nothing about it is used. -/
noncomputable def abelClassifyPt {J : Scheme.{u}} (abel : DivSch ⟶ J)
    (pt0 : ∀ (K : Type u) [Field K] [Algebra k K] [IsIntegral (relCurve C K)]
      [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
      [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))],
      (relCurve C K).CurveDivisor → (Spec (CommRingCat.of K) ⟶ J)) :
    ∀ (K : Type u) [Field K] [Algebra k K] [IsIntegral (relCurve C K)]
      [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
      [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))],
      (relCurve C K).CurveDivisor → (Spec (CommRingCat.of K) ⟶ J) :=
  fun K _ _ _ _ _ D =>
    open Classical in
    if h : 0 ≤ D ∧ Scheme.CurveDivisor.deg K D = (g : ℤ) then
      (effectiveDivisorClassifyZar hpi g hO hchi r1 r2 b1 b2 D h.1 h.2).left ≫ abel
    else pt0 K D

/-- **DAT-J's obligation 1 is VACUOUS.**  For an **arbitrary** `abel : DivScheme g ⟶ J`,
some point map satisfies the Abel-compatibility square.  No geometry, no surjectivity, no
property of `abel` at all — only that the point-map type is inhabited.

Read against the `dat-j` roadmap row, which lists `IsAbelClassifyCompatible` as a real
statement nobody had written: it is not a statement about `abel`, because `pt` is one of its
arguments.  See the module docstring for what this does to its consumer. -/
theorem exists_isAbelClassifyCompatible {J : Scheme.{u}} (abel : DivSch ⟶ J)
    (pt0 : ∀ (K : Type u) [Field K] [Algebra k K] [IsIntegral (relCurve C K)]
      [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
      [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))],
      (relCurve C K).CurveDivisor → (Spec (CommRingCat.of K) ⟶ J)) :
    ∃ pt, IsAbelClassifyCompatible hpi g hO hchi r1 r2 b1 b2 abel pt := by
  classical
  refine ⟨abelClassifyPt hpi g hO hchi r1 r2 b1 b2 abel pt0, ?_⟩
  intro K _ _ _ _ _ D hD hdeg
  -- beta-reduce the chosen `pt` before rewriting: the `dite` is under a lambda applied to
  -- six instance arguments, and `rw` cannot see through that
  change _ = (if h : 0 ≤ D ∧ Scheme.CurveDivisor.deg K D = (g : ℤ) then
      (effectiveDivisorClassifyZar hpi g hO hchi r1 r2 b1 b2 D h.1 h.2).left ≫ abel
    else pt0 K D)
  rw [dif_pos ⟨hD, hdeg⟩]

/-- **The consumer is circular at that `pt`.**  `exists_residueField_lift_of_abelCompatible`
concludes `∃ q, q ≫ abel = J.fromSpecResidueField y`; at the `pt` above, its remaining
hypothesis `heff` asks for an effective degree-`g` `D` with
`pt κ(y) D = J.fromSpecResidueField y`, which is that same equation for `q = (classify D).left`.

Stated as the one implication that carries the point — the hypothesis gives the conclusion
directly, with the theorem it was meant to feed contributing nothing.  So `heff` is not a
"separate Riemann–Roch input" beside the square: at a chosen `pt` it **is** the whole
obligation. -/
theorem heff_iff_conclusion_of_pt_eq {J : Scheme.{u}} (abel : DivSch ⟶ J)
    (pt0 : ∀ (K : Type u) [Field K] [Algebra k K] [IsIntegral (relCurve C K)]
      [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
      [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))],
      (relCurve C K).CurveDivisor → (Spec (CommRingCat.of K) ⟶ J))
    (y : J)
    (h : ∃ (_ : Algebra k (J.residueField y))
      (_ : IsIntegral (relCurve C (J.residueField y)))
      (_ : SmoothOfRelativeDimension 1
        (relCurve C (J.residueField y) ↘ Spec (CommRingCat.of (J.residueField y))))
      (_ : QuasiCompact
        (relCurve C (J.residueField y) ↘ Spec (CommRingCat.of (J.residueField y))))
      (D : (relCurve C (J.residueField y)).CurveDivisor) (_ : 0 ≤ D)
      (_ : Scheme.CurveDivisor.deg (J.residueField y) D = (g : ℤ)),
      abelClassifyPt hpi g hO hchi r1 r2 b1 b2 abel pt0 (J.residueField y) D
        = J.fromSpecResidueField y) :
    ∃ q : Spec (J.residueField y) ⟶ DivSch, q ≫ abel = J.fromSpecResidueField y := by
  classical
  obtain ⟨_, _, _, _, D, hD, hdeg, hpt⟩ := h
  refine ⟨(effectiveDivisorClassifyZar hpi g hO hchi r1 r2 b1 b2 D hD hdeg).left, ?_⟩
  -- unfold the chosen `pt` on its `dif_pos` branch: `hpt` IS the goal
  rwa [abelClassifyPt, dif_pos ⟨hD, hdeg⟩] at hpt

end AbelSquareVacuity

end AlgebraicGeometry
