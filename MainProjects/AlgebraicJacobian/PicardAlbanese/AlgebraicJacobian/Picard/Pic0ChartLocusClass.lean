/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartLocusOpen
import AlgebraicJacobian.Picard.Pic0ChartLocusFibreField

/-!
# The class-indexed witness locus and its openness (the untwisted predecessor of `chartLocus`)

`Picard/Pic0ChartLocusOpen.lean` proves openness of the witness locus of a *chosen*
basic-open cocycle datum `D`; `Picard/Pic0ChartLocusFibreField.lean` proves that the witness
predicate is intrinsic to the *fibre class* of the datum.  Both are stated per datum.  This
file makes the step neither takes: it indexes the locus by a **class**.

* `AlgebraicGeometry.cechWitnessLocus π c` — `{q : Spec B | every basic-open cocycle datum
  with fibre class `c` has an effective witness divisor with vanishing `H¹` at `κ(q)`}`.
* `AlgebraicGeometry.mem_cechWitnessLocus_iff_of_datum` — any ONE presenting datum is a
  sound and complete test (class-intrinsicity).
* `AlgebraicGeometry.mem_cechWitnessLocus_iff_exists` — the ∀-form and the ∃-form agree
  (every class is presented, `BasicOpenCocycleDatum.exists_cechPicClass_eq`).
* `AlgebraicGeometry.isOpen_cechWitnessLocus` — the openness.

## THIS IS NOT `chartLocus`, AND NOT `isOpen_chartLocus`

Those two names are RESERVED, and co-signed between two lanes: `informal/w4-datc-worksheet.md`
§3.3 (CHART-U(a)) freezes `chartLocus c λ` for a locus over a general test `T`, indexed by a
**plus class** `λ ∈ pic0Subgroup C (Over.mk a)`, at the **twisted** fibre class
`λ_t · θ^m · (−Σ)`; `informal/w4-datb-worksheet.md` §1.6 co-signs it with two binding
amendments — the predicate for arbitrary plus classes is the SPLIT form over a finite
separable `L/κ(t)`, and the openness route of record is a three-transport chain — and row B-4
owns `isOpen_chartLocus` as the *assembly* of DAT-B's transports (i)/(ii) against DAT-C's
shifted-datum half.  None of that is here.

What IS here is the step those amendments presuppose and nobody had written: over an affine
base, for an UNTWISTED `CechPic` class, the engine's per-datum output is a locus of the class.
Call it transport (0).  Still missing for `chartLocus` proper: the shifted-datum constructor
(DAT-C GAP-1 — no `BasicOpenCocycleDatum.mul`/tensor exists), the split predicate
(a-amendment), and transports (i) descent and (ii) étale image (DAT-B).

Free of the DD-R certificate lane and of `divRep`: no `DivFamZar`, no `IsCertified`, no
`RepresentableBy` datum appears in the cone.
-/
set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

variable (π) in
/-- **The witness locus of an untwisted class over an affine base**: the set of points of
`Spec B` at which the fibre of the Čech class `c` admits an effective witness divisor with
vanishing `H¹`.

Stated over *classes*, not over data: a basic-open cocycle datum is a presentation, and the
campaign's consumers index charts by a Picard class.  The ∀-quantifier is harmless because
the predicate is class-intrinsic
(`BasicOpenCocycleDatum.hasWitnessH1Vanishing_congr_of_cechPicClass_eq`) and every class is
presented (`BasicOpenCocycleDatum.exists_cechPicClass_eq`) — see
`mem_cechWitnessLocus_iff_exists`.

NOT the co-signed `chartLocus c λ` of `w4-datc` §3.3 / `w4-datb` §1.6: that one lives over a
general test, is indexed by a plus class, and reads the TWISTED fibre class.  See the module
header. -/
def cechWitnessLocus (c : (relCurve C B).CechPic) : Set (PrimeSpectrum B) :=
  {q : PrimeSpectrum B | ∀ D : BasicOpenCocycleDatum C B π,
    D.cechPicClass = c → D.HasWitnessH1Vanishing q.asIdeal.ResidueField}

theorem mem_cechWitnessLocus_iff (c : (relCurve C B).CechPic) (q : PrimeSpectrum B) :
    q ∈ cechWitnessLocus π c ↔ ∀ D : BasicOpenCocycleDatum C B π,
      D.cechPicClass = c → D.HasWitnessH1Vanishing q.asIdeal.ResidueField :=
  Iff.rfl

/-- **Membership is testable at any one presentation**: a datum `D` presenting `c` is a
sound and complete test for membership of the witness locus.  This is the class-intrinsicity
of the witness predicate, `hasWitnessH1Vanishing_congr_of_cechPicClass_eq`, in the form
the consumers use. -/
theorem mem_cechWitnessLocus_iff_of_datum {c : (relCurve C B).CechPic}
    (D : BasicOpenCocycleDatum C B π) (hD : D.cechPicClass = c) (q : PrimeSpectrum B) :
    q ∈ cechWitnessLocus π c ↔ D.HasWitnessH1Vanishing q.asIdeal.ResidueField := by
  refine ⟨fun h => h D hD, fun h D' hD' => ?_⟩
  refine (D'.hasWitnessH1Vanishing_congr_of_cechPicClass_eq D
    q.asIdeal.ResidueField ?_).mpr h
  exact congrArg (Scheme.CechPic.map (relCurveMap C B q.asIdeal.ResidueField))
    (hD'.trans hD.symm)

/-- **The ∀-form and the ∃-form of the witness locus agree**: every class is presented by
some datum, and the witness predicate does not depend on which. -/
theorem mem_cechWitnessLocus_iff_exists (c : (relCurve C B).CechPic) (q : PrimeSpectrum B) :
    q ∈ cechWitnessLocus π c ↔ ∃ D : BasicOpenCocycleDatum C B π,
      D.cechPicClass = c ∧ D.HasWitnessH1Vanishing q.asIdeal.ResidueField := by
  obtain ⟨D₀, hD₀⟩ := BasicOpenCocycleDatum.exists_cechPicClass_eq (C := C) (π := π) c
  refine ⟨fun h => ⟨D₀, hD₀, h D₀ hD₀⟩, fun ⟨D, hD, h⟩ => ?_⟩
  exact (mem_cechWitnessLocus_iff_of_datum D hD q).mpr h

/-- **The class-indexed witness locus is open**: it is the witness locus of any one
presenting datum, and that is open by
`BasicOpenCocycleDatum.isOpen_setOf_exists_witness_h1_vanishing` (the audited,
Noetherian-free openness engine).

This is the first *datum-choice-free* openness statement in the campaign — the engine output
is stated for a chosen `D`, which is not something a locus indexed by a Picard class may
depend on.  It is strictly weaker than the reserved `isOpen_chartLocus` (dat-b row B-4),
which assembles this with the shifted-datum constructor and the descent/étale-image
transports; do not cite it as that. -/
theorem isOpen_cechWitnessLocus (hπ : π ≫ P1.structureMap k = C.hom)
    (c : (relCurve C B).CechPic) : IsOpen (cechWitnessLocus π c) := by
  obtain ⟨D₀, hD₀⟩ := BasicOpenCocycleDatum.exists_cechPicClass_eq (C := C) (π := π) c
  have hset : cechWitnessLocus π c
      = {q : PrimeSpectrum B |
          ∃ W : ((C ⊗ overSpec k q.asIdeal.ResidueField).left).CurveDivisor,
            Scheme.CurveDivisor.picClass q.asIdeal.ResidueField W
                = Scheme.CechPic.map (relCurveMap C B q.asIdeal.ResidueField)
                    D₀.cechPicClass
              ∧ Subsingleton (Sheaf.HModule
                  ((C ⊗ overSpec k q.asIdeal.ResidueField).left.divisorSheaf
                    q.asIdeal.ResidueField W) 1)} :=
    Set.ext fun q => mem_cechWitnessLocus_iff_of_datum D₀ hD₀ q
  rw [hset]
  exact D₀.isOpen_setOf_exists_witness_h1_vanishing hπ

end AlgebraicGeometry
