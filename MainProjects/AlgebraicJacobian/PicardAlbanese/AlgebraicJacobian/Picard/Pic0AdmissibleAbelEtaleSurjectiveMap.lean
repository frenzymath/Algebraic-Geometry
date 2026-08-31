/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AtlasFromDivRepAffChallenge

/-!
# Application formulas for the admissible widened Abel map

This file isolates the map-level equalities needed after a widened divisor family has been
constructed on an affine test. It exposes the chart datum chosen inside the admissible map,
computes a represented point under the Sigma-extended Abel transformation, identifies the
affine Abel value after the vehicle collapse, and packages the final cancellation of the
fixed chart twists.

No quotient, atlas, or representability conclusion is asserted here.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

variable (C) in
/-- The chart index and divisor chosen inside the admissible Abel map can be exposed without
choosing new data. The equality is definitional after unfolding the admissible map. -/
theorem exists_abelSigmaChartAffAdmissible_eq :
    ∃ (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
      (hdeg : Scheme.CurveDivisor.deg k Z
        = (m : ℤ) * classDeg k (thetaCechClass C)
          - (divRepAffAdmissibleParameter C : ℤ)),
      abelSigmaChartAffAdmissible C =
        abelSigmaChartAff C (divRepAffAdmissibleParameter C)
          (divFunctorAff_admissible_representableBy C) m Z hdeg := by
  dsimp only [abelSigmaChartAffAdmissible]
  exact ⟨_, _, _, rfl⟩

variable {n : ℕ}

/-- Classifying a section with a representer and then evaluating the Sigma-extended Abel map
at the underlying scheme morphism returns the original section's chart value. The equality of
the two structure morphisms is handled by sigma-extension extensionality. -/
theorem abelSigmaChartAff_app_homEquiv_symm
    {D : Over (Spec (.of k))}
    (rep : (divFunctorAff C n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    {Y : Scheme.{u}} (a : Y ⟶ Spec (.of k))
    (s : divFamZarAff C n (Over.mk a)) :
    let q := rep.homEquiv.symm s
    (abelSigmaChartAff C n rep m Z hdeg).app (op Y) q.left =
      (⟨a, (chartValueAffTrans C n m Z hdeg).app (op (Over.mk a)) s⟩ :
        (pic0SigmaSheaf C).1.obj (op Y)) := by
  let q := rep.homEquiv.symm s
  change (abelSigmaChartAff C n rep m Z hdeg).app (op Y) q.left =
    (⟨a, (chartValueAffTrans C n m Z hdeg).app (op (Over.mk a)) s⟩ :
      (pic0SigmaSheaf C).1.obj (op Y))
  change (⟨q.left ≫ D.hom, _⟩ :
      (pic0SigmaSheaf C).1.obj (op Y)) =
    ⟨a, (chartValueAffTrans C n m Z hdeg).app (op (Over.mk a)) s⟩
  refine Over.sigmaExtension_ext (pic0TypeFunctor C) q.w ?_
  let e := Over.mkCongr q.w
  let q' : Over.mk (q.left ≫ D.hom) ⟶ D :=
    Over.homMk (U := Over.mk (q.left ≫ D.hom)) q.left
  change (pic0TypeFunctor C).map e.op
      ((chartValueAffTrans C n m Z hdeg).app (op (Over.mk a)) s) =
    (chartValueAffTrans C n m Z hdeg).app
      (op (Over.mk (q.left ≫ D.hom))) (rep.homEquiv q')
  have hhom : e ≫ q = q' := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  have hq : rep.homEquiv q = s := by
    dsimp only [q]
    exact Equiv.apply_symm_apply rep.homEquiv s
  have hfamily : rep.homEquiv q' =
      (divFunctorAff C n).map e.op s := by
    calc
      rep.homEquiv q' = rep.homEquiv (e ≫ q) := congrArg rep.homEquiv hhom.symm
      _ = (divFunctorAff C n).map e.op (rep.homEquiv q) := rep.homEquiv_comp e q
      _ = (divFunctorAff C n).map e.op s := congrArg _ hq
  have hnat := ConcreteCategory.congr_hom
    ((chartValueAffTrans C n m Z hdeg).naturality e.op) s
  calc
    _ = (chartValueAffTrans C n m Z hdeg).app
        (op (Over.mk (q.left ≫ D.hom))) ((divFunctorAff C n).map e.op s) := by
      simpa only [ConcreteCategory.comp_apply] using hnat.symm
    _ = _ := congrArg _ hfamily.symm

omit [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] in
/-- On an affine test, passing a widened affine family through the inverse vehicle comparison
and then taking its Abel value recovers the direct affine Abel value. -/
theorem picEtAffineEquiv_abelDivAff'_affineEquiv_symm
    {A : Type u} [CommRing A] [Algebra k A] (F : DivFamZarAff C A n) :
    picEtAffineEquiv C A
        (abelDivAff' C n (overSpec k A) ((divFamZarAffAffineEquiv C n A).symm F))
      = abelDivAffPlus C A F := by
  rw [picEtAffineEquiv_abelDivAff', Equiv.apply_symm_apply]

/-- If the Abel value of a widened family is the inverse chart twist of a target degree-zero
class, then the chart transformation sends that family to the target itself. -/
theorem chartValueAffTrans_app_eq_of_abelDivAff'_eq_chartTwist
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    {T : Over (Spec (.of k))} (s : divFamZarAff C n T)
    (lam : pic0Subgroup C T)
    (habel : abelDivAff' C n T s = chartTwist C m Z T lam.1) :
    (chartValueAffTrans C n m Z hdeg).app (op T) s = lam := by
  apply Subtype.ext
  rw [chartValueAffTrans_app_coe]
  change chartValueAff C n m Z T s = lam.1
  rw [chartValueAff, habel, chartTwist]
  group

end

end AlgebraicGeometry
