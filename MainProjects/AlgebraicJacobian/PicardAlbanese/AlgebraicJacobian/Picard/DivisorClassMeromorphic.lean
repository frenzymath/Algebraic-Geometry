/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PresentationExtraction
import AlgebraicJacobian.Picard.PointPresentation

/-!
# The Čech Picard class of a Weil divisor: surjectivity and extraction

For the curve bundle `X` (integral, smooth of relative dimension one and quasi-compact
over a field `K`), this file assembles the meromorphic bridge (deg-D2 W3+W4 endpoints):
the total, fully anchored class map

`CurveDivisor.picClass K : X.CurveDivisor → X.CechPic`,

defined by realizing every Weil divisor as the divisor of a meromorphic presentation
(`Scheme.exists_presentationDivisor_eq` — products of the anchored point presentations)
and taking the class of any realization (well-defined by the class law of
`AlgebraicJacobian.Picard.PresentationClassLaw`). Its interface is the degree lane's
gate:

* **(S) surjectivity** — `CurveDivisor.exists_picClass_eq`: every Čech Picard class of
  the curve is the class of a Weil divisor (via `exists_meromorphicPresentation` and the
  class law `CurveDivisor.picClass_presentationDivisor`);
* **(X) extraction** — `CurveDivisor.exists_divOf_of_picClass_eq`: divisors of equal
  class differ by a principal divisor; with the converse
  (`CurveDivisor.picClass_divOf`: principal divisors have trivial class) this is the
  full characterization `CurveDivisor.picClass_eq_iff`;
* the group law `CurveDivisor.picClass_add` / `picClass_zero` and the normalization
  anchor `CurveDivisor.picClass_single`.

This map plays the role that deg-D1's `Scheme.divisorClass` was intended to play; that
constructor's public interface does not determine the divisor its point equations cut
out (see `AlgebraicJacobian.Picard.PointPresentation`), so the bridge is anchored on the
tracked point presentations instead. See the deviation note in the campaign report.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace Scheme

open MeromorphicPresentation

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-! ## Realization: every Weil divisor is the divisor of a presentation -/

/-- **Realization of Weil divisors** (totality of the meromorphic bridge): every Weil
divisor on the curve is the divisor of a meromorphic presentation — a product of
(inverses of) the anchored point presentations, one per point of the support. -/
theorem exists_presentationDivisor_eq (D : X.CurveDivisor) :
    ∃ P : X.MeromorphicPresentation, presentationDivisor K P = D := by
  -- one-point divisors, by induction on the multiplicity
  have hsingle : ∀ (x : X) (hx : x ≠ genericPoint X) (n : ℤ),
      ∃ P : X.MeromorphicPresentation,
        presentationDivisor K P = CurveDivisor.single hx n := by
    intro x hx n
    induction n using Int.induction_on with
    | zero => exact ⟨1, by rw [presentationDivisor_one, CurveDivisor.single_zero]⟩
    | succ n ih =>
      obtain ⟨P, hP⟩ := ih
      refine ⟨P * (pointEquations K hx (pointUniformizerData K hx)).presentation, ?_⟩
      rw [presentationDivisor_mul, hP, presentationDivisor_pointEquations,
        CurveDivisor.single_add]
    | pred n ih =>
      obtain ⟨P, hP⟩ := ih
      refine ⟨P * ((pointEquations K hx (pointUniformizerData K hx)).presentation)⁻¹, ?_⟩
      rw [presentationDivisor_mul, hP, presentationDivisor_inv,
        presentationDivisor_pointEquations, ← CurveDivisor.single_neg,
        CurveDivisor.single_add, sub_eq_add_neg]
  -- the general case, by induction on the finitely supported function
  have hmain : ∀ f : {p : X // p ≠ genericPoint X} →₀ ℤ,
      ∃ P : X.MeromorphicPresentation, presentationDivisor K P = f := by
    intro f
    induction f using Finsupp.induction with
    | zero => exact ⟨1, presentationDivisor_one K⟩
    | single_add p b f _ _ ih =>
      obtain ⟨P, hP⟩ := ih
      obtain ⟨Q, hQ⟩ := hsingle p.1 p.2 b
      refine ⟨Q * P, ?_⟩
      rw [presentationDivisor_mul, hP, hQ]
      rfl
  exact hmain D

/-! ## The class of a Weil divisor -/

/-- **The Čech Picard class `𝒪(D)` of a Weil divisor**: the class of any meromorphic
presentation whose divisor is `D`. Well-defined on divisors by the class law
(`CurveDivisor.picClass_presentationDivisor`); surjective onto `X.CechPic`
(`CurveDivisor.exists_picClass_eq`), with fibers the principal divisors
(`CurveDivisor.picClass_eq_iff`). -/
noncomputable def CurveDivisor.picClass (D : X.CurveDivisor) : X.CechPic :=
  (exists_presentationDivisor_eq K D).choose.picClass

private lemma CurveDivisor.picClass_spec (D : X.CurveDivisor) :
    presentationDivisor K (exists_presentationDivisor_eq K D).choose = D :=
  (exists_presentationDivisor_eq K D).choose_spec

/-- **The class law** (deg-D2 W3, endpoint form): the class of the divisor of a
meromorphic presentation is the presented class. -/
theorem CurveDivisor.picClass_presentationDivisor (P : X.MeromorphicPresentation) :
    CurveDivisor.picClass K (presentationDivisor K P) = P.picClass :=
  MeromorphicPresentation.picClass_eq_of_presentationDivisor_eq K
    (CurveDivisor.picClass_spec K (presentationDivisor K P))

/-- **(S) Surjectivity, existential form**: every Čech Picard class of the curve is the
class of a Weil divisor. -/
theorem CurveDivisor.exists_picClass_eq (L : X.CechPic) :
    ∃ D : X.CurveDivisor, CurveDivisor.picClass K D = L := by
  obtain ⟨P, hP⟩ := exists_meromorphicPresentation L
  exact ⟨presentationDivisor K P,
    (CurveDivisor.picClass_presentationDivisor K P).trans hP⟩

/-- **(S) Surjectivity**: the class map `CurveDivisor.picClass` is onto `X.CechPic`. -/
theorem CurveDivisor.picClass_surjective :
    Function.Surjective fun D : X.CurveDivisor => CurveDivisor.picClass K D :=
  CurveDivisor.exists_picClass_eq K

/-- **(X) Extraction** (deg-D2 W4, endpoint form): Weil divisors of equal Čech Picard
class differ by the principal divisor of a rational function. -/
theorem CurveDivisor.exists_divOf_of_picClass_eq {D D' : X.CurveDivisor}
    (h : CurveDivisor.picClass K D = CurveDivisor.picClass K D') :
    ∃ g : X.functionFieldˣ, D - D' = Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g := by
  obtain ⟨g, hg⟩ := MeromorphicPresentation.exists_divOf_of_picClass_eq K h
  rw [CurveDivisor.picClass_spec, CurveDivisor.picClass_spec] at hg
  exact ⟨g, hg⟩

/-! ## The group law and normalizations -/

@[simp]
theorem CurveDivisor.picClass_zero :
    CurveDivisor.picClass K (0 : X.CurveDivisor) = 1 := by
  have h := CurveDivisor.picClass_presentationDivisor K (1 : X.MeromorphicPresentation)
  rw [presentationDivisor_one, picClass_one] at h
  exact h

/-- The class map is additive: `𝒪(D + D') = 𝒪(D) · 𝒪(D')`. -/
theorem CurveDivisor.picClass_add (D D' : X.CurveDivisor) :
    CurveDivisor.picClass K (D + D')
      = CurveDivisor.picClass K D * CurveDivisor.picClass K D' := by
  have h := CurveDivisor.picClass_presentationDivisor K
    ((exists_presentationDivisor_eq K D).choose
      * (exists_presentationDivisor_eq K D').choose)
  rw [presentationDivisor_mul, CurveDivisor.picClass_spec, CurveDivisor.picClass_spec,
    MeromorphicPresentation.picClass_mul] at h
  exact h

/-- **Principal divisors have trivial class**: `𝒪(div g) = 1`. -/
@[simp]
theorem CurveDivisor.picClass_divOf (g : X.functionFieldˣ) :
    CurveDivisor.picClass K (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) = 1 := by
  have h := CurveDivisor.picClass_presentationDivisor K
    (MeromorphicPresentation.principal g)
  rw [presentationDivisor_principal, picClass_principal] at h
  exact h

/-- **The kernel of the class map is the principal divisors**: two Weil divisors have
the same Čech Picard class iff they differ by a principal divisor. -/
theorem CurveDivisor.picClass_eq_iff {D D' : X.CurveDivisor} :
    CurveDivisor.picClass K D = CurveDivisor.picClass K D'
      ↔ ∃ g : X.functionFieldˣ,
          D - D' = Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g := by
  refine ⟨CurveDivisor.exists_divOf_of_picClass_eq K, ?_⟩
  rintro ⟨g, hg⟩
  have hD : D = D' + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g := by
    rw [← hg]; abel
  rw [hD, CurveDivisor.picClass_add, CurveDivisor.picClass_divOf, mul_one]

/-- **Normalization anchor**: the class of the one-point divisor `1 · x` is the class of
the anchored point local equations at `x`. -/
theorem CurveDivisor.picClass_single {x : X} (hx : x ≠ genericPoint X) :
    CurveDivisor.picClass K (CurveDivisor.single hx 1)
      = (pointEquations K hx (pointUniformizerData K hx)).picClass := by
  have h := CurveDivisor.picClass_presentationDivisor K
    (pointEquations K hx (pointUniformizerData K hx)).presentation
  rw [presentationDivisor_pointEquations, LocalEquations.presentation_picClass] at h
  exact h

end Scheme

end AlgebraicGeometry
