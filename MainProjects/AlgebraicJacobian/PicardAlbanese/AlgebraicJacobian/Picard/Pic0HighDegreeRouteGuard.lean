/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartAbelNonInjective
import AlgebraicJacobian.Picard.Pic0ChartForkNegativeBranch
import AlgebraicJacobian.Picard.Pic0ChartOpenImmersionCriterion
import AlgebraicJacobian.Picard.Pic0AtlasFromDivRepAff
import AlgebraicJacobian.RiemannRoch.ChiCurve

/-!
# The high-degree Abel route guard

The unrestricted Abel map at degree `n > genus C` cannot be the open chart used by the
rank-one strategy. A degree-`n` point over any field extension has at least two sections by
Riemann's inequality. After replacing it by an effective divisor of the same class, the
existing field dictionary gives two distinct divisor families with the same chart value.

The field-extension divisor in the final theorem is the precise nonemptiness input. It cannot
be omitted: an empty source can map by an open immersion. Coverage arguments provide exactly
this input, so the guard applies to the old high-degree direct-Abel route without assuming a
rational point on the curve.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} {n : ℕ}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

section Abel

variable [IsAffineHom π]
variable {D : Over (Spec (.of k))} (rep : (divFunctor C π n).RepresentableBy D)
variable (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
variable (hdeg : Scheme.CurveDivisor.deg k Z
  = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))

/-- Noninjectivity of `chartValue` at one test refutes open immersion of the actual Abel
natural transformation. The proof keeps the structure-morphism component of `abelSigmaChart`;
it is not merely a statement about the Picard-class projection. -/
theorem not_isOpenImmersion_abelSigmaChart_of_not_injective_chartValue
    {T : Over (Spec (.of k))}
    (hnot : ¬ Function.Injective (chartValue C π n m Z T)) :
    ¬ IsOpenImmersion.presheaf (abelSigmaChart C π n rep m Z hdeg) := by
  intro hopen
  apply hnot
  intro s₁ s₂ hval
  by_contra hne
  exact (not_injective_abelSigmaChart_of_divFamZar rep m Z hdeg s₁ s₂ hne hval)
    (injective_of_isOpenImmersion_presheaf hopen (op T.left))

end Abel

section AbelAff

variable {D : Over (Spec (.of k))} (rep : (divFunctorAff C n).RepresentableBy D)
variable (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
variable (hdeg : Scheme.CurveDivisor.deg k Z
  = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))

/-- Two points of a widened divisor-space representation with equal structure morphism and equal
affine chart value refute injectivity of its Abel chart. -/
theorem not_injective_abelSigmaChartAff_of_points {Y : Scheme.{u}} (x₁ x₂ : Y ⟶ D.left)
    (hne : x₁ ≠ x₂) (hstruct : x₁ ≫ D.hom = x₂ ≫ D.hom)
    (hval : chartValueAff C n m Z (Over.mk (x₁ ≫ D.hom))
        (rep.homEquiv (Over.homMk x₁ rfl))
      = chartValueAff C n m Z (Over.mk (x₁ ≫ D.hom))
          (rep.homEquiv (Over.homMk x₂ hstruct.symm))) :
    ¬ Function.Injective ((abelSigmaChartAff C n rep m Z hdeg).app (op Y)) := by
  intro hinj
  refine hne (hinj ?_)
  refine Over.sigmaExtension_ext (pic0TypeFunctor C) hstruct ?_
  have hmap : (divFunctorAff C n).map (Over.mkCongr hstruct).op
        (rep.homEquiv (Over.homMk x₂ rfl))
      = rep.homEquiv (Over.homMk x₂ hstruct.symm) := by
    rw [← rep.homEquiv_comp]
    exact congrArg rep.homEquiv (Over.OverMorphism.ext (Category.id_comp x₂))
  have hnat := ConcreteCategory.congr_hom
    ((chartValueAffTrans C n m Z hdeg).naturality (Over.mkCongr hstruct).op)
    (rep.homEquiv (Over.homMk x₂ rfl))
  refine hnat.symm.trans ?_
  rw [ConcreteCategory.comp_apply, hmap]
  exact Subtype.ext hval.symm

/-- Two distinct widened divisor families with the same affine chart value refute injectivity of
the represented widened Abel chart. -/
theorem not_injective_abelSigmaChartAff_of_divFamZarAff {T : Over (Spec (.of k))}
    (s₁ s₂ : divFamZarAff C n T) (hne : s₁ ≠ s₂)
    (hval : chartValueAff C n m Z T s₁ = chartValueAff C n m Z T s₂) :
    ¬ Function.Injective ((abelSigmaChartAff C n rep m Z hdeg).app (op T.left)) := by
  set x₁ : T.left ⟶ D.left := (rep.homEquiv.symm s₁).left with hx₁
  set x₂ : T.left ⟶ D.left := (rep.homEquiv.symm s₂).left with hx₂
  have hs₁ : x₁ ≫ D.hom = T.hom := Over.w _
  have hs₂ : x₂ ≫ D.hom = T.hom := Over.w _
  have hstruct : x₁ ≫ D.hom = x₂ ≫ D.hom := hs₁.trans hs₂.symm
  have hrec₁ : rep.homEquiv (Over.homMk x₁ hs₁) = s₁ := by
    refine (congrArg rep.homEquiv (Over.OverMorphism.ext ?_)).trans
      (rep.homEquiv.apply_symm_apply s₁)
    rfl
  have hrec₂ : rep.homEquiv (Over.homMk x₂ (hstruct.symm.trans hs₁)) = s₂ := by
    refine (congrArg rep.homEquiv (Over.OverMorphism.ext ?_)).trans
      (rep.homEquiv.apply_symm_apply s₂)
    rfl
  refine not_injective_abelSigmaChartAff_of_points rep m Z hdeg x₁ x₂ ?_ hstruct ?_
  · intro h
    exact hne (hrec₁.symm.trans ((congrArg rep.homEquiv
      (Over.OverMorphism.ext h)).trans hrec₂))
  · set e : Over.mk (x₁ ≫ D.hom) ⟶ T :=
      Over.homMk (𝟙 T.left) ((Category.id_comp T.hom).trans hs₁.symm) with he
    have hfac₁ : (Over.homMk x₁ rfl : Over.mk (x₁ ≫ D.hom) ⟶ D)
        = e ≫ rep.homEquiv.symm s₁ :=
      Over.OverMorphism.ext (Category.id_comp x₁).symm
    have hfac₂ : (Over.homMk x₂ hstruct.symm : Over.mk (x₁ ≫ D.hom) ⟶ D)
        = e ≫ rep.homEquiv.symm s₂ :=
      Over.OverMorphism.ext (Category.id_comp x₂).symm
    have hpull : ∀ s : divFamZarAff C n T,
        rep.homEquiv (e ≫ rep.homEquiv.symm s) = divFamZarAff.map C n e s := by
      intro s
      rw [rep.homEquiv_comp, rep.homEquiv.apply_symm_apply]
      rfl
    have hstep : ∀ (s : divFamZarAff C n T) (y : Over.mk (x₁ ≫ D.hom) ⟶ D),
        y = e ≫ rep.homEquiv.symm s →
        chartValueAff C n m Z (Over.mk (x₁ ≫ D.hom)) (rep.homEquiv y)
          = picEtMap C e (chartValueAff C n m Z T s) := by
      intro s y hy
      subst hy
      exact (congrArg (chartValueAff C n m Z (Over.mk (x₁ ≫ D.hom))) (hpull s)).trans
        (picEtMap_chartValueAff C n m Z e s).symm
    exact (hstep s₁ _ hfac₁).trans
      ((congrArg (picEtMap C e) hval).trans (hstep s₂ _ hfac₂).symm)

/-- Noninjectivity of the widened chart value at one test refutes open immersion of the actual
widened Abel natural transformation. -/
theorem not_isOpenImmersion_abelSigmaChartAff_of_not_injective_chartValueAff
    {T : Over (Spec (.of k))}
    (hnot : ¬ Function.Injective (chartValueAff C n m Z T)) :
    ¬ IsOpenImmersion.presheaf (abelSigmaChartAff C n rep m Z hdeg) := by
  intro hopen
  apply hnot
  intro s₁ s₂ hval
  by_contra hne
  exact (not_injective_abelSigmaChartAff_of_divFamZarAff rep m Z hdeg s₁ s₂ hne hval)
    (injective_of_isOpenImmersion_presheaf hopen (op T.left))

end AbelAff

section Compare

variable [IsAffineHom π]
variable (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)

/-- Noninjectivity on the chart-typed subfunctor transports to the widened affine functor because
the vehicle comparison is injective and preserves chart values. -/
theorem not_injective_chartValueAff_of_not_injective_chartValue
    {T : Over (Spec (.of k))}
    (hnot : ¬ Function.Injective (chartValue C π n m Z T)) :
    ¬ Function.Injective (chartValueAff C n m Z T) := by
  intro hinj
  apply hnot
  intro s₁ s₂ hval
  apply divFamZarToAffVehicle_injective
  apply hinj
  rw [chartValueAff_toAff, chartValueAff_toAff]
  exact hval

end Compare

section HighDegree

variable [IsFinite π]
variable {D : Over (Spec (.of k))} (rep : (divFunctor C π n).RepresentableBy D)
variable (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
variable (hdeg : Scheme.CurveDivisor.deg k Z
  = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))

/- The base-change instances are keyed on the product spelling. Keep these bridges local so the
public guard uses the canonical `relCurve` spelling without exporting overlapping instances. -/
local instance routeGuardIntegral {K : Type u} [Field K] [Algebra k K] :
    IsIntegral (relCurve C K) :=
  instIsIntegralBaseChange C K

local instance routeGuardSmooth {K : Type u} [Field K] [Algebra k K] :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

local instance routeGuardQuasiCompact {K : Type u} [Field K] [Algebra k K] :
    QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

local instance routeGuardH0Finite {K : Type u} [Field K] [Algebra k K] :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

local instance routeGuardH1Finite {K : Type u} [Field K] [Algebra k K] :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

/-- **Root route guard.** If the degree-`n` divisor space has a point after a field extension
and `genus C < n`, the unrestricted degree-`n` Abel map is not an open immersion.

The proof uses `riemann_inequality` to obtain `h⁰ ≥ 2`, replaces the divisor by an
effective representative, and consumes `not_injective_chartValue_of_two_le_h0`. It is stronger
than the positive-genus form required by the review: no positivity hypothesis is needed. -/
theorem not_isOpenImmersion_abelSigmaChart_of_genus_lt_degree
    {K : Type u} [Field K] [Algebra k K]
    (W : (relCurve C K).CurveDivisor)
    (hdegW : Scheme.CurveDivisor.deg K W = (n : ℤ))
    (hng : genus C < n) :
    ¬ IsOpenImmersion.presheaf (abelSigmaChart C π n rep m Z hdeg) := by
  haveI : IsProper (baseChangeBundle C K).hom := instIsProperSndLeft C K
  haveI : SmoothOfRelativeDimension 1 (baseChangeBundle C K).hom :=
    instSmoothOfRelativeDimensionSndLeft C K
  haveI : GeometricallyIrreducible (baseChangeBundle C K).hom :=
    instGeometricallyIrreducibleSndLeft C K
  have hO : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1 :=
    h0_moduleKSheaf (baseChangeBundle C K)
  have hchi : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (genus C : ℤ) := by
    have h := chi_moduleKSheaf (baseChangeBundle C K)
    rw [genus_baseField C K] at h
    exact h
  have hh0z := riemann_inequality K W
  rw [hdegW, hchi] at hh0z
  have hh0W : 2 ≤ Sheaf.h0 ((relCurve C K).divisorSheaf K W) := by
    omega
  obtain ⟨A, hA, hdegA, hh0A, -⟩ :=
    exists_effective_deg_two_le_h0_of_two_le_h0 (C := C) (π := π) (n := n)
      W hdegW hh0W
  exact not_isOpenImmersion_abelSigmaChart_of_not_injective_chartValue rep m Z hdeg
    (not_injective_chartValue_of_two_le_h0 (C := C) (π := π) (n := n)
      hO A hA hdegA hh0A m Z)

include π

/-- **Widened root route guard.** Under the same nonemptiness and degree hypotheses, the live
arbitrary-affine-open Abel map is not an open immersion when `genus C < n`.

* Provenance: ADAPTED.
* TO CHECK: Milne's cited page assumes positive genus, while this statement is
  packaged for all genera; verify the genus-zero scope. -/
theorem not_isOpenImmersion_abelSigmaChartAff_of_genus_lt_degree
    {Daff : Over (Spec (.of k))} (repAff : (divFunctorAff C n).RepresentableBy Daff)
    {K : Type u} [Field K] [Algebra k K]
    (W : (relCurve C K).CurveDivisor)
    (hdegW : Scheme.CurveDivisor.deg K W = (n : ℤ))
    (hng : genus C < n) :
    ¬ IsOpenImmersion.presheaf (abelSigmaChartAff C n repAff m Z hdeg) := by
  haveI : IsProper (baseChangeBundle C K).hom := instIsProperSndLeft C K
  haveI : SmoothOfRelativeDimension 1 (baseChangeBundle C K).hom :=
    instSmoothOfRelativeDimensionSndLeft C K
  haveI : GeometricallyIrreducible (baseChangeBundle C K).hom :=
    instGeometricallyIrreducibleSndLeft C K
  have hO : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1 :=
    h0_moduleKSheaf (baseChangeBundle C K)
  have hchi : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (genus C : ℤ) := by
    have h := chi_moduleKSheaf (baseChangeBundle C K)
    rw [genus_baseField C K] at h
    exact h
  have hh0z := riemann_inequality K W
  rw [hdegW, hchi] at hh0z
  have hh0W : 2 ≤ Sheaf.h0 ((relCurve C K).divisorSheaf K W) := by
    omega
  obtain ⟨A, hA, hdegA, hh0A, -⟩ :=
    exists_effective_deg_two_le_h0_of_two_le_h0 (C := C) (π := π) (n := n)
      W hdegW hh0W
  exact not_isOpenImmersion_abelSigmaChartAff_of_not_injective_chartValueAff
    repAff m Z hdeg
    (not_injective_chartValueAff_of_not_injective_chartValue m Z
      (not_injective_chartValue_of_two_le_h0 (C := C) (π := π) (n := n)
        hO A hA hdegA hh0A m Z))

end HighDegree

end

end AlgebraicGeometry
