/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.DegreeIsoTransport
import AlgebraicJacobian.RiemannRoch.DegreePullbackFiber

/-!
# EV-4: degree multiplicativity under pullback — the E-v headline (Lane B)

For a finite surjective morphism `h : D ⟶ E` of curve bundles over a field `K`, this
file assembles **EV-main** (`informal/w7-ev-worksheet.md` §1.1, the probe-EV-A pin):

`classDeg K (CechPic.map h.left Λ) = [K(D) : K(E)] · classDeg K Λ`,

the function-field degree taken along the landed `functionFieldMap` (the named
`functionFieldAlgebra` tower of `RiemannRoch/DegreePullbackDictionary.lean`).  Its only
consumer join is F-6.  The ladder mirrors `RiemannRoch/DegreeBaseFieldInvariance.lean`
line by line, with the base-field transition `π` replaced by an arbitrary finite
dominant `f` and the fiber-degree identity (†) replaced by the EV-3 keystone
(`sum_ordZ_residueDeg_of_isFinite`, `RiemannRoch/DegreePullbackFiber.lean`): reduce
along `CurveDivisor.picClass` generators by `Finsupp.induction` + `classDeg_zpow`,
present the point class by the tracked point equations, pull the presentation back
along `f` (`pointPullbackEquations`; regularity by
`pullbackEqn_germ_mem_nonZeroDivisors` at `genericPoint_eq_of_surjective`), read off
the fiber-supported divisor (`pointPullbackEquations_presentation_elem_of_eq`/`_of_ne`)
and close with EV-3.  Main declarations: `pointPullbackEquations`, `pointPullbackUnit`,
`classDeg_cechPicMap_eq_finrank_mul`, `classDeg_cechPicMap_of_isFinite` (**EV-main**).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section SchemeLevel

variable (K : Type u) [Field K] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))] [IsIntegral Y]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]

/-! ## The pulled tracked point system

The pulled tracked point equations along a generic-to-generic morphism, their
trivializing unit `f^♯(uniformizer)` and the on/off-fiber presentation elements are
the landed W7-B3 plumbing (`RiemannRoch/DegreeIsoTransport.lean`): `pointPullbackEquations`,
`pointPullbackUnit`, `pointPullbackEquations_presentation_elem_of_eq`/`_of_ne` — stated
there for arbitrary `f` precisely so this campaign can consume them. -/

/-! ## Order at a non-unit point (file-local copy of the deg-D1 lemma) -/

omit [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- A section that is a non-unit at a closed point `z` has germ at `η` of nontrivial
order at `z` (file-local copy of the private deg-D1 lemma). -/
private lemma ord_ne_one_of_not_isUnit_germ {z : X}
    (hz : z ≠ genericPoint X) {U : X.Opens} (s : Γ(X, U)) (hη : genericPoint X ∈ U)
    (hzU : z ∈ U) (hnu : ¬ IsUnit ((X.presheaf.germ U z hzU).hom s)) :
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
      ((X.presheaf.germ U (genericPoint X) hη).hom s) ≠ 1 := by
  letI := isDiscreteValuationRing_stalk (X ↘ Spec (CommRingCat.of K)) hz
  letI := isDedekindDomain_stalk (X ↘ Spec (CommRingCat.of K)) hz
  have hgs : (X.presheaf.germ U (genericPoint X) hη).hom s
      = algebraMap (X.presheaf.stalk z) X.functionField
        ((X.presheaf.germ U z hzU).hom s) :=
    Scheme.germ_generic_eq_algebraMap_germ hη hzU s
  have hord : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
      = (stalkHeightOne X z).valuation X.functionField := rfl
  rw [hgs, ne_eq, hord, IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  intro h
  exact hnu (IsLocalRing.notMem_maximalIdeal.mp h)

/-! ## The degree of the pulled point divisor -/

/-- **The pulled point divisor has degree `n` times the degree of the point**
(EV-4 steps 4–5): the divisor of the presentation of the pulled tracked point system is
supported in the fiber `f⁻¹(x')` with coefficients `ord(f^♯ t)`, and EV-3 sums it to
`[K(X) : K(Y)] · [κ(x') : K]`. -/
private theorem deg_presentationDivisor_pointPullback (f : X ⟶ Y) [IsFinite f]
    (hcomp : f ≫ (Y ↘ Spec (CommRingCat.of K)) = X ↘ Spec (CommRingCat.of K))
    (hf : f.base (genericPoint X) = genericPoint Y)
    {x' : Y} (hx' : x' ≠ genericPoint Y) :
    letI := f.functionFieldAlgebra hf
    Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K
        (pointPullbackEquations K f hf hx').presentation)
      = (Module.finrank Y.functionField X.functionField : ℤ)
        * (Y.residueDeg K x' : ℤ) := by
  classical
  letI := f.functionFieldAlgebra hf
  set d := Scheme.pointUniformizerData K hx' with hd
  -- the affine sub-chart of the tracked neighbourhood
  obtain ⟨V, hVaff, hx'V, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    Y.isBasis_affineOpens d.mem
  have hηV : genericPoint Y ∈ V := Scheme.genericPoint_mem_of_nonempty ⟨x', hx'V⟩
  -- the restricted tracked section and its unit
  set t := (Y.presheaf.map (homOfLE hVle).op).hom d.sec with ht
  set g₁ : Y.functionFieldˣ :=
    Units.mk0 (uniformizer K hx') (uniformizer_ne_zero K hx') with hg₁def
  have hgu : (Y.presheaf.germ V (genericPoint Y) hηV).hom t = uniformizer K hx' := by
    rw [ht, Y.presheaf.germ_res_apply (homOfLE hVle) _ hηV d.sec]
    exact d.germ_generic
  have hgt : (g₁ : Y.functionField)
      = (Y.presheaf.germ V (genericPoint Y) hηV).hom t := hgu.symm
  have hordx' : Scheme.ordZ (Y ↘ Spec (CommRingCat.of K)) hx' g₁
      = Multiplicative.ofAdd (1 : ℤ) :=
    Scheme.ordZ_eq_ofAdd_one_of_val_eq_uniformizer K hx' rfl
  have hunit : ∀ (z : Y) (hz : z ∈ V), z ≠ x' →
      IsUnit ((Y.presheaf.germ V z hz).hom t) := by
    intro z hz hzx
    rw [ht, Y.presheaf.germ_res_apply (homOfLE hVle) z hz d.sec]
    exact d.isUnit_germ z (hVle hz) hzx
  -- the coefficient description of the pulled divisor
  have hcoeff : ∀ (z : X) (hz : z ≠ genericPoint X),
      coeffAt hz (Scheme.presentationDivisor K
          (pointPullbackEquations K f hf hx').presentation)
        = Multiplicative.toAdd
          (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz
            ((pointPullbackEquations K f hf hx').presentation.elem z)) :=
    fun z hz => Scheme.coeffAt_presentationDivisor K _ hz
  have hzero : ∀ (z : X) (hz : z ≠ genericPoint X), f.base z ≠ x' →
      coeffAt hz (Scheme.presentationDivisor K
        (pointPullbackEquations K f hf hx').presentation) = 0 := by
    intro z hz hne
    rw [hcoeff z hz, pointPullbackEquations_presentation_elem_of_ne K f hf hx' hne,
      map_one, toAdd_one]
  -- the support is contained in the fiber over `x'`
  have hSfiber : ∀ p ∈ (toFinsupp (Scheme.presentationDivisor K
      (pointPullbackEquations K f hf hx').presentation)).support,
      f.base p.1 = x' := by
    intro p hp
    by_contra hne
    rw [Finsupp.mem_support_iff] at hp
    exact hp (hzero p.1 p.2 hne)
  have hSV : ∀ p ∈ (toFinsupp (Scheme.presentationDivisor K
      (pointPullbackEquations K f hf hx').presentation)).support,
      p.1 ∈ f ⁻¹ᵁ V := by
    intro p hp
    change f.base p.1 ∈ V
    rw [hSfiber p hp]
    exact hx'V
  have hη₂ : genericPoint X ∈ f ⁻¹ᵁ V := by
    change f.base (genericPoint X) ∈ V
    rw [hf]
    exact hηV
  -- the value of the pulled section at `η_X` is the pulled uniformizer
  have hg₂v : ((X.presheaf.germ (f ⁻¹ᵁ V) (genericPoint X) hη₂).hom
        ((f.appLE V (f ⁻¹ᵁ V) le_rfl).hom t))
      = (pointPullbackUnit K f hf hx' : X.functionField) := by
    have happ : ((f.appLE V (f ⁻¹ᵁ V) le_rfl).hom t) = ((f.app V).hom t) :=
      congr($(Scheme.Hom.appLE_eq_app f).hom t)
    rw [coe_pointPullbackUnit, happ, ← f.functionFieldMap_germ hf V hηV hη₂ t]
    exact congrArg _ hgu
  -- the unit-outside hypothesis at the support
  have hout : ∀ (z : X) (hz : z ∈ f ⁻¹ᵁ V) (hzg : z ≠ genericPoint X),
      (⟨z, hzg⟩ : {y : X // y ≠ genericPoint X})
        ∉ (toFinsupp (Scheme.presentationDivisor K
          (pointPullbackEquations K f hf hx').presentation)).support →
      IsUnit ((X.presheaf.germ (f ⁻¹ᵁ V) z hz).hom
        ((f.appLE V (f ⁻¹ᵁ V) le_rfl).hom t)) := by
    intro z hz hzg hzS
    have hzV : f.base z ∈ V := hz
    have happ : ((f.appLE V (f ⁻¹ᵁ V) le_rfl).hom t) = ((f.app V).hom t) :=
      congr($(Scheme.Hom.appLE_eq_app f).hom t)
    by_cases hfib : f.base z = x'
    · -- fiber case: outside the support the order is trivial, hence the germ is a unit
      by_contra hnu
      have hord := ord_ne_one_of_not_isUnit_germ K hzg
        ((f.appLE V (f ⁻¹ᵁ V) le_rfl).hom t) hη₂ hz hnu
      have hordZ : Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hzg
          (pointPullbackUnit K f hf hx') ≠ 1 := by
        rw [ne_eq, Scheme.ordZ_eq_one_iff, ← hg₂v]
        exact hord
      apply hzS
      rw [Finsupp.mem_support_iff]
      change coeffAt hzg (Scheme.presentationDivisor K
        (pointPullbackEquations K f hf hx').presentation) ≠ 0
      rw [hcoeff z hzg, pointPullbackEquations_presentation_elem_of_eq K f hf hx' hfib]
      exact fun h0 => hordZ (toAdd_eq_zero.mp h0)
    · -- off the fiber: the tracked section is a unit there, and unit germs pull back
      rw [happ, ← f.germ_stalkMap_apply V z hzV t]
      exact ((hunit _ hzV hfib).map (f.stalkMap z).hom)
  -- the degree as the fiber sum
  have hdeg : Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K
      (pointPullbackEquations K f hf hx').presentation)
      = ∑ p ∈ (toFinsupp (Scheme.presentationDivisor K
          (pointPullbackEquations K f hf hx').presentation)).support,
        Multiplicative.toAdd
          (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) p.2
            (pointPullbackUnit K f hf hx'))
          * (X.residueDeg K p.1 : ℤ) := by
    change ∑ p ∈ (toFinsupp (Scheme.presentationDivisor K
        (pointPullbackEquations K f hf hx').presentation)).support,
      (toFinsupp (Scheme.presentationDivisor K
        (pointPullbackEquations K f hf hx').presentation)) p
        * (X.residueDeg K p.1 : ℤ) = _
    refine Finset.sum_congr rfl fun p hp => ?_
    have hcp : (toFinsupp (Scheme.presentationDivisor K
        (pointPullbackEquations K f hf hx').presentation)) p
        = coeffAt p.2 (Scheme.presentationDivisor K
          (pointPullbackEquations K f hf hx').presentation) := rfl
    rw [hcp, hcoeff p.1 p.2,
      pointPullbackEquations_presentation_elem_of_eq K f hf hx' (hSfiber p hp)]
  rw [hdeg]
  -- close by EV-3 (the fiber sum equals `n · [κ(x') : K]`)
  have hev3 : ∑ p ∈ (toFinsupp (Scheme.presentationDivisor K
        (pointPullbackEquations K f hf hx').presentation)).support,
      Multiplicative.toAdd
        (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) p.2 (f.functionFieldMapUnits hf g₁))
        * (X.residueDeg K p.1 : ℤ)
      = (Module.finrank Y.functionField X.functionField : ℤ)
        * (Y.residueDeg K x' : ℤ) :=
    sum_ordZ_residueDeg_of_isFinite K f hcomp hf hVaff hηV g₁ hgt hx' hx'V hordx' hunit
      ((toFinsupp (Scheme.presentationDivisor K
        (pointPullbackEquations K f hf hx').presentation)).support) hSV hout
  exact hev3

/-! ## EV-main, scheme form -/

variable [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]

/-- The single-point case of EV-main: pulling back the class of a one-point divisor
multiplies its degree by `n = [K(X) : K(Y)]`. -/
private theorem classDeg_cechPicMap_picClass_single (f : X ⟶ Y) [IsFinite f]
    (hcomp : f ≫ (Y ↘ Spec (CommRingCat.of K)) = X ↘ Spec (CommRingCat.of K))
    (hf : f.base (genericPoint X) = genericPoint Y)
    {x' : Y} (hx' : x' ≠ genericPoint Y) :
    letI := f.functionFieldAlgebra hf
    classDeg K (Scheme.CechPic.map f
        (Scheme.CurveDivisor.picClass K (Scheme.CurveDivisor.single hx' 1)))
      = (Module.finrank Y.functionField X.functionField : ℤ)
        * classDeg K (Scheme.CurveDivisor.picClass K
            (Scheme.CurveDivisor.single hx' 1)) := by
  letI := f.functionFieldAlgebra hf
  have h1 : Scheme.CechPic.map f
      (Scheme.CurveDivisor.picClass K (Scheme.CurveDivisor.single hx' 1))
      = (pointPullbackEquations K f hf hx').picClass := by
    rw [Scheme.CurveDivisor.picClass_single K hx']
    exact (Scheme.LocalEquations.picClass_pullback _ _ _).symm
  have h2 : (pointPullbackEquations K f hf hx').picClass
      = Scheme.CurveDivisor.picClass K (Scheme.presentationDivisor K
          (pointPullbackEquations K f hf hx').presentation) := by
    rw [Scheme.CurveDivisor.picClass_presentationDivisor,
      Scheme.LocalEquations.presentation_picClass]
  rw [h1, h2, classDeg_picClass, classDeg_picClass,
    deg_presentationDivisor_pointPullback K f hcomp hf hx',
    Scheme.CurveDivisor.deg_single' K hx' 1]
  ring

/-- **EV-main, scheme form**: for a finite morphism `f : X ⟶ Y` of curve bundles over
`K` (compatible with the structure morphisms, generic point to generic point) and every
Čech Picard class `Λ` of `Y`,

`classDeg K (CechPic.map f Λ) = [K(X) : K(Y)] · classDeg K Λ`.

Proved by the E-iv-alg ladder: reduce along the surjective additive class map
`CurveDivisor.picClass` to one-point divisors, present the point class by the tracked
point equations, pull the presentation back along `f`, and close with EV-3. -/
theorem classDeg_cechPicMap_eq_finrank_mul (f : X ⟶ Y) [IsFinite f]
    (hcomp : f ≫ (Y ↘ Spec (CommRingCat.of K)) = X ↘ Spec (CommRingCat.of K))
    (hf : f.base (genericPoint X) = genericPoint Y) (Λ : Y.CechPic) :
    letI := f.functionFieldAlgebra hf
    classDeg K (Scheme.CechPic.map f Λ)
      = (Module.finrank Y.functionField X.functionField : ℤ) * classDeg K Λ := by
  letI := f.functionFieldAlgebra hf
  obtain ⟨DD, rfl⟩ := Scheme.CurveDivisor.exists_picClass_eq K Λ
  suffices h : ∀ φ : {p : Y // p ≠ genericPoint Y} →₀ ℤ,
      classDeg K (Scheme.CechPic.map f (Scheme.CurveDivisor.picClass K φ))
        = (Module.finrank Y.functionField X.functionField : ℤ)
          * classDeg K (Scheme.CurveDivisor.picClass K φ) from h DD
  intro φ
  induction φ using Finsupp.induction with
  | zero =>
    change classDeg K (Scheme.CechPic.map f
      (Scheme.CurveDivisor.picClass K (0 : Y.CurveDivisor)))
      = (Module.finrank Y.functionField X.functionField : ℤ)
        * classDeg K (Scheme.CurveDivisor.picClass K (0 : Y.CurveDivisor))
    rw [Scheme.CurveDivisor.picClass_zero, map_one, classDeg_one, classDeg_one,
      mul_zero]
  | single_add p b φ hpφ hb ih =>
    have key : ∀ DD : Y.CurveDivisor,
        classDeg K (Scheme.CechPic.map f (Scheme.CurveDivisor.picClass K DD))
          = (Module.finrank Y.functionField X.functionField : ℤ)
            * classDeg K (Scheme.CurveDivisor.picClass K DD) →
        classDeg K (Scheme.CechPic.map f (Scheme.CurveDivisor.picClass K
          (Scheme.CurveDivisor.single p.2 b + DD)))
          = (Module.finrank Y.functionField X.functionField : ℤ)
            * classDeg K (Scheme.CurveDivisor.picClass K
              (Scheme.CurveDivisor.single p.2 b + DD)) := by
      intro DD hDD
      rw [Scheme.CurveDivisor.picClass_add, ← Scheme.picClass_single_zpow K p.2 b,
        map_mul, map_zpow, classDeg_mul, classDeg_mul, classDeg_zpow, classDeg_zpow,
        hDD, classDeg_cechPicMap_picClass_single K f hcomp hf p.2]
      ring
    exact key φ ih

end SchemeLevel

/-! ## EV-main, the pinned `Over`-form (`w7-ev-worksheet.md` §1.1) -/

/-- **EV-main (EV-4, the E-v headline)**: for a finite surjective morphism `h : D ⟶ E`
of curve bundles over a field `K` and every Čech Picard class `Λ` of `E.left`,

`classDeg K (CechPic.map h.left Λ) = [K(D) : K(E)] · classDeg K Λ`,

the function-field degree taken along `functionFieldMap` at
`genericPoint_eq_of_surjective` (the probe-EV-A statement pin; the algebra is the named
`functionFieldAlgebra` tower, definitionally `functionFieldMap.hom.toAlgebra`).
Multiplicativity is decoupled from the dichotomy: the finite/dominant case is stated
with `[Surjective h.left] [IsFinite h.left]` as hypotheses, and F-6 supplies the case
split. -/
theorem classDeg_cechPicMap_of_isFinite {K : Type u} [Field K]
    (D E : Over (Spec (CommRingCat.of K)))
    [IsProper D.hom] [SmoothOfRelativeDimension 1 D.hom] [GeometricallyIrreducible D.hom]
    [IsProper E.hom] [SmoothOfRelativeDimension 1 E.hom] [GeometricallyIrreducible E.hom]
    (h : D ⟶ E) [Surjective h.left] [IsFinite h.left] (Λ : E.left.CechPic) :
    letI : D.left.Over (Spec (CommRingCat.of K)) := .ofHom D.hom
    letI : E.left.Over (Spec (CommRingCat.of K)) := .ofHom E.hom
    haveI : SmoothOfRelativeDimension 1 (D.left ↘ Spec (CommRingCat.of K)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 D.hom)
    haveI : QuasiCompact (D.left ↘ Spec (CommRingCat.of K)) :=
      inferInstanceAs (QuasiCompact D.hom)
    haveI : SmoothOfRelativeDimension 1 (E.left ↘ Spec (CommRingCat.of K)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 E.hom)
    haveI : QuasiCompact (E.left ↘ Spec (CommRingCat.of K)) :=
      inferInstanceAs (QuasiCompact E.hom)
    haveI : Module.Finite K (Sheaf.HModule (D.left.moduleKSheaf K) 0) :=
      moduleFinite_hModule_zero D
    haveI : Module.Finite K (Sheaf.HModule (D.left.moduleKSheaf K) 1) :=
      moduleFinite_hModule_one D
    haveI : Module.Finite K (Sheaf.HModule (E.left.moduleKSheaf K) 0) :=
      moduleFinite_hModule_zero E
    haveI : Module.Finite K (Sheaf.HModule (E.left.moduleKSheaf K) 1) :=
      moduleFinite_hModule_one E
    letI := h.left.functionFieldAlgebra (genericPoint_eq_of_surjective h.left)
    classDeg K (Scheme.CechPic.map h.left Λ)
      = (Module.finrank E.left.functionField D.left.functionField : ℤ)
        * classDeg K Λ := by
  letI : D.left.Over (Spec (CommRingCat.of K)) := .ofHom D.hom
  letI : E.left.Over (Spec (CommRingCat.of K)) := .ofHom E.hom
  haveI : SmoothOfRelativeDimension 1 (D.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 D.hom)
  haveI : QuasiCompact (D.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (QuasiCompact D.hom)
  haveI : SmoothOfRelativeDimension 1 (E.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 E.hom)
  haveI : QuasiCompact (E.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (QuasiCompact E.hom)
  haveI : Module.Finite K (Sheaf.HModule (D.left.moduleKSheaf K) 0) :=
    moduleFinite_hModule_zero D
  haveI : Module.Finite K (Sheaf.HModule (D.left.moduleKSheaf K) 1) :=
    moduleFinite_hModule_one D
  haveI : Module.Finite K (Sheaf.HModule (E.left.moduleKSheaf K) 0) :=
    moduleFinite_hModule_zero E
  haveI : Module.Finite K (Sheaf.HModule (E.left.moduleKSheaf K) 1) :=
    moduleFinite_hModule_one E
  exact classDeg_cechPicMap_eq_finrank_mul K h.left (Over.w h)
    (genericPoint_eq_of_surjective h.left) Λ

end AlgebraicGeometry
