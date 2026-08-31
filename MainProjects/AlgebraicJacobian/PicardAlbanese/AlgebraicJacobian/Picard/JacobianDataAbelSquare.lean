/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyFieldSurj
import AlgebraicJacobian.Picard.JacobianDataFromPicRepDatum

/-!
# DAT-J step 3 is one compatibility square, not a construction

`Picard/JacobianDataFromPicRepDatum.lean` reduced DAT-J to two inputs: a
`PicRepDatum k k C` and, for every point `y` of the representing object, a lift

> `∃ q : Spec κ(y) ⟶ DivScheme g, q ≫ abel = fromSpecResidueField y`.

The lift has been read as "the Abel map is surjective on points", i.e. as geometry still
to be done. **The morphism half is already built**, in a rooted file, and what is missing
is only that it sits over the right point.

## What is landed, and had no consumer

`Picard/DivisorFamilyFieldSurj.lean` (rooted, sorry-free) carries the whole *fibrewise*
chain, and the reason it is short is that **over a field the certificate is free**:

* `DivisorAdaptation.isCertified_of_deg` (`:104`) — over a field `K`, an adaptation whose
  presentation divisor has degree `n` is `IsCertified n`.  All seven clauses: projectivity
  and both flat-cokernel clauses are `Module.Free.of_divisionRing` instances, `(c1)`
  finiteness is `moduleFinite_colength`, and the `(c2)` rank clause is the *unconditional*
  CRT identity `deg_presentationDivisor` read against the degree hypothesis.  No support
  separation is needed — which the file records as a deviation of record, since full
  support separation is unachievable when a support point lies in both charts' overlap.
* `exists_divFam_divFamDivisor_eq` (`:147`) — hence every effective degree-`g` divisor over
  `K` *is* the divisor of a `DivFam`.
* `effectiveDivisorClassifyZar` (`:217`) — and it classifies, giving
  `overSpec k K ⟶ divSchemeOver …`, characterized by `effectiveDivisorClassifyZar_spec`
  (`:231`).

This is the sharp form of critical-path §7.6's own observation that the `DivFamZar` no-go
is a purely *relative* phenomenon, **vacuous over a field**: the difficulty that makes U2
hard does not exist fibrewise.

## What is therefore actually missing

`effectiveDivisorClassifyZar_spec` says the morphism is `divRepClassifyZar` of a family
presenting `D`.  It says **nothing about `abel`**.  So joining it to `hlift` needs exactly
one statement — that classifying an effective divisor and then applying the Abel map
returns the class of that divisor's point:

> `AbelCompatible abel` : for every field point and every effective degree-`g` divisor `D`
> over it, `(effectiveDivisorClassifyZar … D …).left ≫ abel` is the morphism `Spec K ⟶ J`
> named by the class of `D`.

That is a *compatibility square*, not a surjectivity theorem, and it is the recorded
"groups agree ≠ maps agree" gap (inbox `I-0525`): a bijection between divisor classes and
`DivScheme`-points is unusable until the square relating the two named morphisms lands.

## Main declarations

* `AlgebraicGeometry.IsAbelClassifyCompatible` — the square, as a named interface.
* `AlgebraicGeometry.exists_residueField_lift_of_abelCompatible` — the square plus
  fibrewise effectivity gives the `hlift` obligation **verbatim** as
  `JacobianData.ofAbelLifts` / `PicRepDatum.toJacobianDataOfAbelLifts` consume it.

## What this does NOT do

It produces no `AbelClassifyCompatible` and no effectivity witness, so it builds no
`JacobianData`.  It removes the *construction* from DAT-J step 3 and leaves a square and
an effectivity input, both stated here rather than assumed anywhere.

## AMENDMENT 2026-07-29: `heff` is NOT the divRep-gated half

The text above calls `heff` "the honest geometric input", which is right, and the `dat-j`
roadmap row read that as work still gated behind divisor representability.  It is not:
`Picard/JacobianDataAbelEffective.lean` and `Picard/JacobianDataAbelEffectivePoint.lean`
discharge the effectivity content, at every point of *any* `Pic⁰`-representing object, with
no `divFunctor`, no `DivFamZar`, no certificate and no chart
(`exists_effective_deg_eq_of_pic0_at_point`).

So of the two halves this file separates, only the **square** is divRep-gated — naming
`abel` requires the representation.  They were never gated alike.  What the effectivity side
still owes is *descent*: its divisor lives over a finite separable splitting field of `κ(y)`,
and `hlift` wants `Spec κ(y)` itself.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

section AbelSquare

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftAbelSquare :
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

/-! ## The square -/

/-- **The Abel-compatibility square** — the one statement standing between the landed
fibrewise classification and DAT-J's `hlift` obligation.

At a scheme `J` and a morphism `abel : DivScheme g ⟶ J`, this says: whenever a point `y`
of `J` is presented by an effective degree-`g` divisor `D` on the curve over its own
residue field — presented in the sense that the classifying morphism composed with `abel`
is required to be `fromSpecResidueField y` — the composite is that structural morphism.

Stated as a hypothesis over `y` and `D` rather than as a surjectivity claim, because that
is the shape `hlift` consumes: `hlift` needs, *for each* `y`, *some* divisor; the geometric
content is producing `D`, and the bookkeeping content is this square.  Separating them is
the point of this file (compare inbox `I-0525`: an isomorphism of class groups is unusable
without the square relating the named morphisms). -/
def IsAbelClassifyCompatible {J : Scheme.{u}} (abel : DivSch ⟶ J)
    (pt : ∀ (K : Type u) [Field K] [Algebra k K] [IsIntegral (relCurve C K)]
      [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
      [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))],
      (relCurve C K).CurveDivisor → (Spec (CommRingCat.of K) ⟶ J)) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K]
    [IsIntegral (relCurve C K)]
    [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
    (D : (relCurve C K).CurveDivisor) (hD : 0 ≤ D)
    (hdeg : Scheme.CurveDivisor.deg K D = (g : ℤ)),
    (effectiveDivisorClassifyZar hpi g hO hchi r1 r2 b1 b2 D hD hdeg).left ≫ abel
      = pt K D

/-- **The `hlift` obligation from the square plus fibrewise effectivity** — `DAT-J` step 3
in the exact shape `JacobianData.ofAbelLifts` and
`PicRepDatum.toJacobianDataOfAbelLifts` consume (`Picard/JacobianDataAbelSurj.lean`,
`Picard/JacobianDataFromPicRepDatum.lean`).

The lift is `effectiveDivisorClassifyZar` of the supplied divisor, and the triangle is the
square.  Note what is *not* here: no surjectivity of the Abel map on points is proved, and
no divisor is produced — `heff` is the honest geometric input (Riemann–Roch: a degree-`g`
class on a curve of genus `g` over a field has an effective representative, to be spelled
with `exists_effective_of_picClass` / `riemann_inequality` and **never** with
`riemann_inequality_curve`, which imports `Challenge.lean`). -/
theorem exists_residueField_lift_of_abelCompatible {J : Scheme.{u}} (abel : DivSch ⟶ J)
    (pt : ∀ (K : Type u) [Field K] [Algebra k K] [IsIntegral (relCurve C K)]
      [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
      [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))],
      (relCurve C K).CurveDivisor → (Spec (CommRingCat.of K) ⟶ J))
    (hsq : IsAbelClassifyCompatible hpi g hO hchi r1 r2 b1 b2 abel pt)
    (heff : ∀ y : J, ∃ (_ : Algebra k (J.residueField y))
      (_ : IsIntegral (relCurve C (J.residueField y)))
      (_ : SmoothOfRelativeDimension 1
        (relCurve C (J.residueField y) ↘ Spec (CommRingCat.of (J.residueField y))))
      (_ : QuasiCompact
        (relCurve C (J.residueField y) ↘ Spec (CommRingCat.of (J.residueField y))))
      (D : (relCurve C (J.residueField y)).CurveDivisor) (_ : 0 ≤ D)
      (_ : Scheme.CurveDivisor.deg (J.residueField y) D = (g : ℤ)),
      pt (J.residueField y) D = J.fromSpecResidueField y) :
    ∀ y : J, ∃ q : Spec (J.residueField y) ⟶ DivSch,
      q ≫ abel = J.fromSpecResidueField y := by
  intro y
  obtain ⟨_, _, _, _, D, hD, hdeg, hpt⟩ := heff y
  exact ⟨(effectiveDivisorClassifyZar hpi g hO hchi r1 r2 b1 b2 D hD hdeg).left,
    (hsq (J.residueField y) D hD hdeg).trans hpt⟩

end AbelSquare

end AlgebraicGeometry
