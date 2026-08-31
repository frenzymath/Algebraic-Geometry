/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorThetaSurjectivity
import AlgebraicJacobian.Cohomology.GluedSheafDatumFibre

/-!
# DD-4 (Task 4) — the fibrewise `H¹` hypothesis of the theta-ideal datum

The W6-full fibre-restriction seam, instantiated on the twisted ideal datum
`DivisorAdaptation.thetaIdealDatum` presenting `𝒪(Θᵃ − d)`
(`informal/dat-d-worksheet.md` §2.3 step 2, `informal/spec-dat-1.md` 1d-ii):

* `DivisorAdaptation.thetaIdealDatum_hfib_of_witness` — **the engine's fibrewise
  hypothesis discharged from fibre witnesses**: if at every prime `p` of the test ring
  the fibre datum's Čech Picard class on the fibre curve `C_{κ(p)}` is presented by a
  Weil divisor with vanishing `H¹`, then the complex-form fibrewise hypothesis
  `hfib : ∀ p, Subsingleton (H¹(pair) ⊗[R] κ(p))` of `thetaGluedEval_surjective`
  holds — in that exact spelling.
* `DivisorAdaptation.thetaGluedEval_surjective_of_fibre_witness` — **right exactness
  of the section sequence from fibre witnesses**: the Θ-twisted colength evaluation
  `thetaGluedEval : H⁰(𝒪(Θᵃ)) → W(d)^{Θᵃ}` is surjective under the same per-fibre
  witness hypothesis, feeding `windowQuotEquiv`/`divisorWindowGr`
  (`Picard/DivisorFamilyWindow.lean`).

The remaining numeric input is the witness production: the fibre class is
`CechPic.map (relCurveMap C R κ(p)) (thetaIdealDatum a).cechPicClass`
(`cechPicClass_baseChange`), any Weil divisor of that class serves
(`CurveDivisor.exists_picClass_eq`), and its `H¹` vanishes once its degree
`a·δ − deg d` clears the DAT-0a uniform bound on the fibre curve
(`exists_bound_subsingleton_hModule_one_of_isFinite_toP1`) — the class-degree law of
the theta-ideal datum and the fibre-uniform bound are the residual bricks.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} {R : Type u} [CommRing R]
  [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations}

/-- **The engine's fibrewise `H¹` hypothesis for the theta-ideal datum, discharged
from fibre witnesses** (the W6-full fibre-restriction seam on `𝒪(Θᵃ − d)`): if at
every prime `p` of the test ring the Čech Picard class of the fibre datum
`(thetaIdealDatum a).baseChange κ(p)` is presented by a Weil divisor on the fibre
curve `C_{κ(p)}` with vanishing `H¹`, then the complex-form fibrewise hypothesis of
`thetaGluedEval_surjective` holds, in that exact spelling. -/
theorem thetaIdealDatum_hfib_of_witness (A : DivisorAdaptation C R π d) (a : ℕ)
    (hwit : ∀ p : PrimeSpectrum R,
      ∃ W : ((C ⊗ overSpec k p.asIdeal.ResidueField).left).CurveDivisor,
        Scheme.CurveDivisor.picClass p.asIdeal.ResidueField W
            = ((A.thetaIdealDatum a).baseChange p.asIdeal.ResidueField).cechPicClass
          ∧ Subsingleton (Sheaf.HModule
              ((C ⊗ overSpec k p.asIdeal.ResidueField).left.divisorSheaf
                p.asIdeal.ResidueField W) 1)) :
    ∀ p : PrimeSpectrum R,
      Subsingleton ((datumPair (A.thetaIdealDatum a)).H1 ⊗[R]
        p.asIdeal.ResidueField) :=
  fun p =>
    (A.thetaIdealDatum a).subsingleton_h1_residueField_tensor_of_witness p (hwit p)

/-- **Right exactness of the section sequence from fibre witnesses** (worksheet §2.3
step 2, unconditional modulo the numeric witness input): the Θ-twisted colength
evaluation `thetaGluedEval : H⁰(𝒪(Θᵃ)) → W(d)^{Θᵃ}` is surjective whenever every
fibre of the twisted ideal datum's class is presented by a Weil divisor with vanishing
`H¹` — e.g. any divisor of the fibre class once its degree `a·δ − deg d` clears the
DAT-0a bound. Plugs into `windowQuotEquiv`/`divisorWindowGr`. -/
theorem thetaGluedEval_surjective_of_fibre_witness {A : DivisorAdaptation C R π d}
    {a : ℕ} (hπ : π ≫ P1.structureMap k = C.hom)
    (hwit : ∀ p : PrimeSpectrum R,
      ∃ W : ((C ⊗ overSpec k p.asIdeal.ResidueField).left).CurveDivisor,
        Scheme.CurveDivisor.picClass p.asIdeal.ResidueField W
            = ((A.thetaIdealDatum a).baseChange p.asIdeal.ResidueField).cechPicClass
          ∧ Subsingleton (Sheaf.HModule
              ((C ⊗ overSpec k p.asIdeal.ResidueField).left.divisorSheaf
                p.asIdeal.ResidueField W) 1)) :
    Function.Surjective (A.thetaGluedEval a) :=
  thetaGluedEval_surjective hπ (thetaIdealDatum_hfib_of_witness A a hwit)

end DivisorAdaptation

end AlgebraicGeometry
