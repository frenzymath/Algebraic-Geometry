/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafSubord
import AlgebraicJacobian.Cohomology.GluedSheafH0BaseChange
import AlgebraicJacobian.Cohomology.GluedSheafFibre
import AlgebraicJacobian.RiemannRoch.W6Full
import AlgebraicJacobian.Curve.BaseChangeInstances

/-!
# The fibre-restriction seam of the datum engine, closed (DAT-1 (1d-ii) × DAT-3)

The full `hfib` discharge chain for a pinned basic-open cocycle datum
`D : BasicOpenCocycleDatum C B π` (`informal/spec-dat-1.md` 1d-ii second half — the
"one open seam" of the W6-full chain, `informal/w4-datum-worksheet.md` §3.1(a)):

* `BasicOpenCocycleDatum.subsingleton_h1_tensor_of_baseChange` — **the complex-form
  fibre hypothesis from the fibre datum**: for any `k`-algebra map `B → B'`, vanishing
  of `H¹` of the two-lattice pair of the base-changed datum forces
  `Subsingleton (H¹(pair D) ⊗[B] B')` — the base-changed Čech differential is
  surjective through the landed δ-naturality square (`datumDiffBaseChange`), and the
  cokernel identification is right-exactness (`subsingleton_h1_rTensor_iff`).
* `BasicOpenCocycleDatum.presentationSheafIso` — **the presentation bridge** (over a
  field): the datum's glued sheaf is isomorphic to the glued sheaf of the meromorphic
  presentation `MeromorphicPresentation.ofCocycle` of its canonical subordinated
  cocycle — the subordination isomorphism (`gluedSheafSubord`) at the pointed cover by
  pieces; the presented class is `D.cechPicClass` on the nose.
* `BasicOpenCocycleDatum.subsingleton_sheaf_h1_of_picClass_eq` — **`hfib` in datum
  sheaf form over a field**: vanishing of `H¹(𝒪(W))` for any witness divisor `W` of
  the datum's Čech Picard class discharges `H¹` of the datum's glued sheaf (through
  the presentation bridge and the W6-full export
  `subsingleton_hModule_gluedSheaf_one_of_picClass_eq`).
* `BasicOpenCocycleDatum.subsingleton_h1_residueField_tensor_of_witness` — **the seam,
  closed**: at a prime `p` of the test ring, a witness divisor of the fibre datum's
  class on the fibre curve `C_{κ(p)}` with vanishing `H¹(𝒪(W))` discharges the
  engine's complex-form fibre hypothesis
  `Subsingleton (H¹(pair D) ⊗[B] κ(p))` (`datumRigidEngine`'s `hfib p`).  The fibre
  curve's instance package fires from `Curve.BaseChangeInstances` (G-D5(a)).

Everything upstream of the witness hypothesis is unconditional; producing the witness
at a prescribed degree — `cechPicClass_baseChange` plus the degree seam and DAT-0a's
uniform bound — is the consumer's numeric input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule
attribute [local instance 10000] relCurve.instOver

open AlgebraicJacobian

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {π : C.left ⟶ P1 k} [IsFinite π]

namespace BasicOpenCocycleDatum

/-! ## The complex-form fibre hypothesis from the fibre datum -/

/-- **The complex-form fibre hypothesis from the fibre datum** (the (1d-ii) second
half): for a `k`-algebra `B'` over the test ring, the vanishing of `H¹` of the
two-lattice pair of the base-changed datum forces the vanishing of the base change of
`H¹` of the pair of the datum: the fibre pair's Čech differential is surjective, the
δ-naturality square (`datumDiffBaseChange`) carries surjectivity to the base-changed
differential, and `H¹(pair) ⊗ B'` is its cokernel by right-exactness. -/
theorem subsingleton_h1_tensor_of_baseChange (D : BasicOpenCocycleDatum C B π)
    (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B'] [IsScalarTower k B B']
    (h : Subsingleton (datumPair (D.baseChange B')).H1) :
    Subsingleton ((datumPair D).H1 ⊗[B] B') := by
  -- the fibre pair's differential is surjective
  have himg : (datumPair (D.baseChange B')).imageLattice = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp h
  have hsurj' : Function.Surjective (datumPair (D.baseChange B')).diff := by
    rw [← LinearMap.range_eq_top, (datumPair (D.baseChange B')).range_diff_eq]
    exact himg
  -- surjectivity transports backward across the δ-naturality square
  have hsq : ∀ a, (D.termBaseChangeInf B').symm ((datumPair (D.baseChange B')).diff a)
      = ((datumPair D).diff.baseChange B') ((D.datumDomBaseChange B').symm a) := by
    intro a
    have hkey := D.datumDiffBaseChange B' ((D.datumDomBaseChange B').symm a)
    rw [LinearEquiv.apply_symm_apply] at hkey
    rw [← hkey, LinearEquiv.symm_apply_apply]
  have hbc : Function.Surjective ((datumPair D).diff.baseChange B') :=
    RigidEngine.surjective_congr _ _ (D.datumDomBaseChange B').symm
      (D.termBaseChangeInf B').symm hsq hsurj'
  -- the base change of `H¹` is the cokernel of the base-changed differential
  rw [(datumPair D).subsingleton_h1_rTensor_iff B']
  exact Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr hbc)

/-- The sheaf-level form: `H¹` of the base-changed datum's glued sheaf vanishing
forces the complex-form fibre hypothesis (through `datumH1Equiv` at the fibre
datum). -/
theorem subsingleton_h1_tensor_of_baseChange_sheaf (D : BasicOpenCocycleDatum C B π)
    (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B'] [IsScalarTower k B B']
    (h : Subsingleton (Sheaf.HModule (D.baseChange B').sheaf 1)) :
    Subsingleton ((datumPair D).H1 ⊗[B] B') :=
  D.subsingleton_h1_tensor_of_baseChange B'
    ((subsingleton_datumPair_h1_iff (D.baseChange B')).mpr h)

/-! ## The presentation bridge over a field -/

section Field

variable {K : Type u} [Field K] [Algebra k K]
variable [IsIntegral (relCurve C K)]
variable [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
variable [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- **The presentation bridge**: over a field, the datum's glued sheaf is isomorphic
to the glued sheaf of the meromorphic presentation of its canonical subordinated
cocycle (`MeromorphicPresentation.ofCocycle` on the pointed cover by pieces) — the
subordination isomorphism `gluedSheafSubord`.  The presented class is
`E.cechPicClass` by definition. -/
noncomputable def presentationSheafIso (E : BasicOpenCocycleDatum C K π) :
    E.sheaf ≅ (Scheme.MeromorphicPresentation.ofCocycle E.pointedCover
      (gluedSubordCocycle E.isGluingCocycle E.pointedCover E.pieceIndex
        fun _ => le_rfl)).gluedSheaf K :=
  gluedSheafSubord K (σ := E.pieceIndex) (fun _ => le_rfl)
    (fun x y =>
      congrArg Units.val
        (gluedSubordCocycle_evInf E.isGluingCocycle E.pointedCover E.pieceIndex
          (fun _ => le_rfl) x y))
    E.isGluingCocycle
    (fun z => ⟨z, E.pointedCover.mem_opens z⟩)

/-- **`hfib` in datum sheaf form over a field** (the datum-level face of the W6-full
step (c)+(d) exports): the vanishing of `H¹(𝒪(W))` for any witness divisor `W` of the
datum's Čech Picard class discharges the vanishing of `H¹` of the datum's glued
sheaf. -/
theorem subsingleton_sheaf_h1_of_picClass_eq (E : BasicOpenCocycleDatum C K π)
    {W : (relCurve C K).CurveDivisor}
    (hW : Scheme.CurveDivisor.picClass K W = E.cechPicClass)
    (hvan : Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K W) 1)) :
    Subsingleton (Sheaf.HModule E.sheaf 1) := by
  have hpres : Subsingleton (Sheaf.HModule
      ((Scheme.MeromorphicPresentation.ofCocycle E.pointedCover
        (gluedSubordCocycle E.isGluingCocycle E.pointedCover E.pieceIndex
          fun _ => le_rfl)).gluedSheaf K) 1) :=
    subsingleton_hModule_gluedSheaf_one_of_picClass_eq K _ hW hvan
  exact (Sheaf.HModule.mapEquiv (presentationSheafIso E) 1).toEquiv.subsingleton_congr.mpr
    hpres

end Field

/-! ## The seam, closed: the engine's fibre hypothesis from a fibre witness -/

/-- **The W6-full fibre-restriction seam, closed** (spec-dat-1 (1d-ii) second half):
at a prime `p` of the test ring `B`, a witness divisor `W` of the fibre datum's Čech
Picard class on the fibre curve `C_{κ(p)}` with `H¹(𝒪(W)) = 0` discharges the rigid
engine's complex-form fibre hypothesis `Subsingleton (H¹(pair D) ⊗[B] κ(p))` — the
`hfib p` clause of `datumRigidEngine` and `datum_subsingleton_pairH1`.

The fibre curve carries its geometric package by base change
(`Curve.BaseChangeInstances`); the witness is spelled on the product spelling
`(C ⊗ overSpec k κ(p)).left` those instances are keyed on (definitionally
`relCurve C κ(p)`). -/
theorem subsingleton_h1_residueField_tensor_of_witness
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
    (D : BasicOpenCocycleDatum C B π) (p : PrimeSpectrum B)
    (hwit : ∃ W : ((C ⊗ overSpec k p.asIdeal.ResidueField).left).CurveDivisor,
      Scheme.CurveDivisor.picClass p.asIdeal.ResidueField W
          = (D.baseChange p.asIdeal.ResidueField).cechPicClass
        ∧ Subsingleton (Sheaf.HModule
            ((C ⊗ overSpec k p.asIdeal.ResidueField).left.divisorSheaf
              p.asIdeal.ResidueField W) 1)) :
    Subsingleton ((datumPair D).H1 ⊗[B] p.asIdeal.ResidueField) := by
  obtain ⟨W, hW, hvan⟩ := hwit
  haveI : IsIntegral (relCurve C p.asIdeal.ResidueField) :=
    instIsIntegralBaseChange C p.asIdeal.ResidueField
  haveI : SmoothOfRelativeDimension 1
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
    instSmoothOfRelativeDimensionBaseChange C p.asIdeal.ResidueField
  haveI : QuasiCompact
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
    instQuasiCompactBaseChange C p.asIdeal.ResidueField
  refine D.subsingleton_h1_tensor_of_baseChange_sheaf p.asIdeal.ResidueField ?_
  exact subsingleton_sheaf_h1_of_picClass_eq (D.baseChange p.asIdeal.ResidueField)
    hW hvan

end BasicOpenCocycleDatum

end AlgebraicGeometry
