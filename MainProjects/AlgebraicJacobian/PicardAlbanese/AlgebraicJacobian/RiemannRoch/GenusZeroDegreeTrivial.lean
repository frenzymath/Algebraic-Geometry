/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.SectionBound
import AlgebraicJacobian.RiemannRoch.ChiLedger
import AlgebraicJacobian.RiemannRoch.SectionSpaces
import AlgebraicJacobian.Picard.DivisorClassMeromorphic
import AlgebraicJacobian.Picard.JacobianDataAbelDegreeWindow

/-!
# AT GENUS `0`, A DEGREE-ZERO PICARD CLASS IS TRIVIAL

The degree homomorphism `classDeg` (`RiemannRoch/Degree.lean`) has a large landed API in one
direction — `classDeg_one`, `classDeg_mul`, `classDeg_inv`, `classDeg_picClass`,
`classDeg_eq_zero_of_mem_picFromBase` — every one of which computes a degree *from* a class.
This file supplies the other direction at `χ(𝒪) = 1`, i.e. at genus `0`, in the **equality of
classes** spelling that `relPicDeg` consumers need.

**CORRECTED, and the correction matters more than the file.**  An earlier version of this
header said "the converse is absent: nothing in the tree concludes that a class is trivial
from its degree, at any genus", and cited a consumer/producer count as the evidence.  **Both
halves were wrong**, found by a fresh-context review:

* the conclusion follows in four lines from the landed
  `exists_effective_deg_eq_of_le_classDeg` (`Picard/JacobianDataAbelDegreeWindow.lean:132`,
  landed two days earlier) at `g := 0, d := 0` — verified to elaborate.  What is genuinely new
  here is only the *spelling*: that lemma concludes an existential (an effective divisor of the
  right class and degree), and every consumer downstream of this file wants `L = 1`.  A name
  census could not see the overlap precisely because the two conclusions have different shapes,
  and the two files are in disjoint import closures;
* the count was a figure from the task brief, restated as a per-file measurement of a
  different carrier.  Measured at HEAD: `hvan`-shaped binders occur in 3 files, not 93 —
  the "93 consumers" figure is about `JacobianData.rep`, a different object.  Do not quote a
  consumer count from this header; run the grep.

The proof below is therefore written through the landed lemma rather than re-deriving its
three steps.

## The argument

`exists_effective_deg_eq_of_le_classDeg` at target degree `0` (entry condition `1 ≤ deg + χ`,
which at `χ = 1` and `deg = 0` is `1 ≤ 1`) produces an **effective** divisor of the class with
degree `0`; and an effective divisor of degree `≤ 0` is `0`
(`Scheme.CurveDivisor.eq_zero_of_deg_le_zero`, coefficients nonnegative weighted by positive
residue degrees).  So the class is the class of `0`, which is `1`.

**No `H¹`-vanishing hypothesis is needed** — χ alone forces the section, `h⁰ = χ + h¹ ≥ χ`.
That is inherited from the landed lemma, not a property of this file.

## What this is for

It is the field-level layer of the degree-zero Picard vanishing that
`Picard/Pic0VanishingAffineReduction.lean` reduces to test rings, and the debt
`Albanese/Genus0Terminal.lean` isolates.  It does **not** discharge that debt: the vanishing
quantifies over test *rings*, and this statement is over a *field*.  The remaining step is the
ring-level one, and it is not supplied here.

## Main declarations

* `AlgebraicGeometry.eq_one_of_classDeg_eq_zero_of_chi_one` — at `χ(𝒪) = 1`, a Čech Picard
  class of degree `0` is trivial.  The equality-of-classes face of
  `exists_effective_deg_eq_of_le_classDeg`.
* `AlgebraicGeometry.classDeg_eq_zero_iff_eq_one_of_chi_one` — bundled as an iff with the
  landed `classDeg_one`, so both directions sit under one name.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

/-- **At `χ(𝒪) = 1`, a degree-zero Picard class is trivial** — the equality-of-classes face of
the landed `exists_effective_deg_eq_of_le_classDeg`.

That lemma at `g := 0, d := 0` already produces an effective divisor of `L`'s class of degree
`0`; all that is added here is `eq_zero_of_deg_le_zero` to collapse it to the zero divisor and
`picClass_zero` to read off `L = 1`.  The earlier version of this proof re-derived the landed
lemma's three internal steps; it is written through the lemma instead. -/
theorem eq_one_of_classDeg_eq_zero_of_chi_one
    (hchi : Sheaf.chi (X.moduleKSheaf K) = 1)
    (L : X.CechPic) (hL : classDeg K L = 0) : L = 1 := by
  obtain ⟨E, hEeff, hEcl, hEdeg⟩ :=
    exists_effective_deg_eq_of_le_classDeg K 0 0 (by simpa using hchi) le_rfl L hL
  rw [← hEcl, Scheme.CurveDivisor.eq_zero_of_deg_le_zero K hEeff (le_of_eq hEdeg)]
  exact Scheme.CurveDivisor.picClass_zero K

/-- The two directions under one name: at `χ(𝒪) = 1` the degree of a Čech Picard class
vanishes exactly when the class is trivial.  The forward direction is the landed
`classDeg_one`. -/
theorem classDeg_eq_zero_iff_eq_one_of_chi_one
    (hchi : Sheaf.chi (X.moduleKSheaf K) = 1) (L : X.CechPic) :
    classDeg K L = 0 ↔ L = 1 :=
  ⟨eq_one_of_classDeg_eq_zero_of_chi_one K hchi L, fun h => by rw [h]; exact classDeg_one K⟩

end AlgebraicGeometry
