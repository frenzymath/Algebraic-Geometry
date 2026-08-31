/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowFibreModel

/-!
# Seed cases for the recursive high-window fibre model

The first two recursive relations are the transported universal Grassmannian
windows.  Their cancelled fibre-reading equivalences therefore identify their
closed-normalized images with the canonical divisor windows at stages zero and
one.  This supplies the two base cases for the later projectivity-and-image
induction.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section HighWindowFibreModelBase

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowFibreModelBase :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k
    (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k
    ((windowS_choice pi hpi g • fiberWeilDivisor pi) +
      (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)

local notation "RP" => PairChartRing k g r1 g r2 i j
local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
local notation "N1" =>
  (divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule
local notation "N2" =>
  (divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule
local notation "Kr[" n "]" => divUniversalHighWindowRelation
  (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n

variable (K : Type u) [Field K] [Algebra k K]
  [Algebra (PairChartRing k g r1 g r2 i j) K]
  [IsScalarTower k (PairChartRing k g r1 g r2 i j) K]
  [Algebra (DivCarveChartRing k
    (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi)
    g r1 r2 b1 b2 i j) K]
  [IsScalarTower (PairChartRing k g r1 g r2 i j)
    (DivCarveChartRing k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j) K]
  [IsScalarTower k (DivCarveChartRing k
    (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi)
    g r1 r2 b1 b2 i j) K]

noncomputable local instance instIsIntegralRelCurveHighWindowFibreModelBase :
    IsIntegral (relCurve C K) := instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveHighWindowFibreModelBase :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveHighWindowFibreModelBase :
    QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTRelCurveHighWindowFibreModelBase :
    LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveHighWindowFibreModelBase :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

noncomputable local instance instFinH1RelCurveHighWindowFibreModelBase :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

local notation "A[" n "]" => Scheme.divisorSections K
  (windowN C K hpi g + n • windowS C K hpi g) ⊤
local notation "KM" => divUniversalFibreKM C hpi g r1 r2 b1 i j K
local notation "KMS" => divUniversalFibreK' C hpi g r1 r2 b2 i j K

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
  (hker : divCarveIdeal k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j ≤ RingHom.ker
        (algebraMap (PairChartRing k g r1 g r2 i j) K))

/-! ## A range/comap bridge -/

/-- If a map into one ambient submodule has the same underlying values as an
equivalence onto another submodule, its range is the corresponding comap. -/
private theorem range_eq_comap_of_equiv_coe
    {F X : Type u} [AddCommGroup F] [Module K F]
    [AddCommGroup X] [Module K X]
    (B A : Submodule K F) (f : X →ₗ[K] ↥B) (e : X ≃ₗ[K] ↥A)
    (h : B.subtype.comp f = A.subtype.comp e.toLinearMap) :
    LinearMap.range f = A.comap B.subtype := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    have hx := LinearMap.congr_fun h x
    simp only [LinearMap.comp_apply] at hx
    change B.subtype (f x) ∈ A
    rw [hx]
    exact (e x).property
  · intro hy
    let a : A := ⟨y.1, hy⟩
    obtain ⟨x, hx⟩ := e.surjective a
    refine ⟨x, Subtype.ext ?_⟩
    have hfx := LinearMap.congr_fun h x
    simp only [LinearMap.comp_apply] at hfx
    change (f x : F) = (y : B)
    calc
      (f x : F) = (e x : A) := hfx
      _ = (a : A) := congrArg Subtype.val hx
      _ = (y : B) := rfl

/-! ## The two seed reading squares -/

set_option maxHeartbeats 2400000 in
-- The nested closed normalization and two scalar extensions are expensive to elaborate.
/-- Read the scalar extension of the first seed relation through the closed
stage-zero normalization. -/
private noncomputable def divUniversalHighWindowClosedFstRead :
    K ⊗[RZ] ↥N1 →ₗ[K] (relCurve C K).functionField :=
  A[0].subtype.comp
    ((divUniversalHighWindowClosedAmbientFibreEquiv
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 0).toLinearMap.comp
        ((LinearMap.baseChange K
          (LinearMap.baseChange RZ
            (divUniversalHighWindowZeroEquiv
              (C := C) (pi := pi) hpi g).toLinearMap)).comp
          (LinearMap.baseChange K
            ((divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule).subtype)))

set_option maxHeartbeats 2400000 in
-- The nested closed normalization and two scalar extensions are expensive to elaborate.
/-- Read the scalar extension of the second seed relation through the closed
stage-one normalization. -/
private noncomputable def divUniversalHighWindowClosedSndRead :
    K ⊗[RZ] ↥N2 →ₗ[K] (relCurve C K).functionField :=
  A[1].subtype.comp
    ((divUniversalHighWindowClosedAmbientFibreEquiv
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 1).toLinearMap.comp
        ((LinearMap.baseChange K
          (LinearMap.baseChange RZ
            (divUniversalHighWindowOneEquiv
              (C := C) (pi := pi) hpi g).toLinearMap)).comp
          (LinearMap.baseChange K
            ((divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule).subtype)))

set_option maxHeartbeats 4000000 in
-- Tensor induction repeatedly expands the closed stage-zero normalization and seed read.
set_option synthInstance.maxHeartbeats 1000000 in
/-- Closed stage-zero normalization agrees with the original first-window
fibre-reading equivalence. -/
private theorem divUniversalHighWindowClosedFstRead_eq :
    divUniversalHighWindowClosedFstRead
        C hpi g r1 r2 b1 b2 i j K =
      (divUniversalFibreKM C hpi g r1 r2 b1 i j K).subtype.comp
        (divUniversalFstFibreReadEquiv
          (π := pi) C hpi g r1 r2 b1 b2 i j K).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x =>
      have hzero : windowM_choice pi hpi g =
          divUniversalHighWindowExponent (C := C) (pi := pi) hpi g 0 := by
        simp [divUniversalHighWindowExponent]
      have hmap :
          (divUniversalHighWindowZeroEquiv
              (C := C) (pi := pi) hpi g).toLinearMap =
            (divisorWindowExponentEquiv
              (C := C) (pi := pi) hzero).toLinearMap := by
        apply LinearMap.ext
        intro y
        rfl
      have hunit :
          divUniversalHighWindowClosedCoherenceUnit
              (C := C) (pi := pi) hpi g K 0 = 1 := by
        rw [divUniversalHighWindowClosedCoherenceUnit]
        simp only [pow_zero, mul_one]
        rw [← hzero, mul_inv_cancel]
      have hcancel :
          divUniversalHighWindowAmbientCancelEquiv
              (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 0
              (1 ⊗ₜ[RZ]
                (LinearMap.baseChange RZ
                  (divUniversalHighWindowZeroEquiv
                    (C := C) (pi := pi) hpi g).toLinearMap x.1)) =
            LinearMap.baseChange K
              (divUniversalHighWindowZeroEquiv
                (C := C) (pi := pi) hpi g).toLinearMap
              (windowCompare RZ K x.1) := by
        calc
          _ = divUniversalHighWindowAmbientCancelEquiv
                (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 0
                (LinearMap.baseChange K
                  (LinearMap.baseChange RZ
                    (divUniversalHighWindowZeroEquiv
                      (C := C) (pi := pi) hpi g).toLinearMap)
                  (1 ⊗ₜ[RZ] x.1)) := by
              rw [LinearMap.baseChange_tmul]
          _ = LinearMap.baseChange K
                (divUniversalHighWindowZeroEquiv
                  (C := C) (pi := pi) hpi g).toLinearMap
                (TensorProduct.AlgebraTensorModule.cancelBaseChange k RZ K K
                  ↥(Scheme.divisorSections k
                    (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤)
                  (1 ⊗ₜ[RZ] x.1)) := by
              simpa only [divUniversalHighWindowAmbientCancelEquiv] using
                divUniversalHighWindowAmbientCancelEquiv_baseChange
                  (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K
                  (divUniversalHighWindowZeroEquiv
                    (C := C) (pi := pi) hpi g).toLinearMap
                  (1 ⊗ₜ[RZ] x.1)
          _ = _ := by
              rw [← windowCompare_eq_cancelBaseChange
                (k := k)
                (H := ↥(Scheme.divisorSections k
                  (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
                RZ K x.1]
      have hcore :
          divUniversalHighWindowClosedFstRead
              C hpi g r1 r2 b1 b2 i j K (1 ⊗ₜ[RZ] x) =
            ((divUniversalFibreKM C hpi g r1 r2 b1 i j K).subtype.comp
              (divUniversalFstFibreReadEquiv
                (π := pi) C hpi g r1 r2 b1 b2 i j K).toLinearMap)
              (1 ⊗ₜ[RZ] x) := by
        rw [divUniversalHighWindowClosedFstRead, LinearMap.comp_apply,
          LinearMap.comp_apply, LinearMap.comp_apply,
          LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
        change
          ((divUniversalHighWindowClosedAmbientFibreEquiv
              (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 0
              (1 ⊗ₜ[RZ]
                (LinearMap.baseChange RZ
                  (divUniversalHighWindowZeroEquiv
                    (C := C) (pi := pi) hpi g).toLinearMap x.1)) : A[0]) :
            (relCurve C K).functionField) =
            ((divUniversalFstFibreReadEquiv
              (π := pi) C hpi g r1 r2 b1 b2 i j K
              (1 ⊗ₜ[RZ] x) :
              divUniversalFibreKM C hpi g r1 r2 b1 i j K) :
              (relCurve C K).functionField)
        rw [divUniversalHighWindowClosedAmbientFibreEquiv_apply
              (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 0
              (1 ⊗ₜ[RZ]
                (LinearMap.baseChange RZ
                  (divUniversalHighWindowZeroEquiv
                    (C := C) (pi := pi) hpi g).toLinearMap x.1)),
          hcancel,
          divUniversalFstFibreReadEquiv_one_tmul
            (π := pi) C hpi g r1 r2 b1 b2 i j K x,
          hmap]
        rw [hunit]
        simp only [Units.val_one, one_mul]
        exact divFamPhi_baseChange_divisorWindowExponentEquiv
          (C := C) (pi := pi) K hzero
          (relThetaPairH1_windowM C pi hpi g)
          (relThetaPairH1_windowM_add_mulS C pi hpi g 0)
          (windowCompare RZ K x.1)
      rw [TensorProduct.tmul_eq_smul_one_tmul]
      simpa only [map_smul] using congrArg (fun y => c • y) hcore

set_option maxHeartbeats 4000000 in
-- Tensor induction repeatedly expands the closed stage-one normalization and seed read.
set_option synthInstance.maxHeartbeats 1000000 in
/-- Closed stage-one normalization agrees with the coherence-adjusted
second-window fibre-reading equivalence. -/
private theorem divUniversalHighWindowClosedSndRead_eq :
    divUniversalHighWindowClosedSndRead
        C hpi g r1 r2 b1 b2 i j K =
      (divUniversalFibreK' C hpi g r1 r2 b2 i j K).subtype.comp
        (divUniversalSndFibreReadEquiv
          (π := pi) C hpi g r1 r2 b1 b2 i j K).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x =>
      have hone : windowM_choice pi hpi g + windowS_choice pi hpi g =
          divUniversalHighWindowExponent (C := C) (pi := pi) hpi g 1 := by
        simp [divUniversalHighWindowExponent]
      have hmap :
          (divUniversalHighWindowOneEquiv
              (C := C) (pi := pi) hpi g).toLinearMap =
            (divisorWindowExponentEquiv
              (C := C) (pi := pi) hone).toLinearMap := by
        apply LinearMap.ext
        intro y
        rfl
      have hcancel :
          divUniversalHighWindowAmbientCancelEquiv
              (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 1
              (1 ⊗ₜ[RZ]
                (LinearMap.baseChange RZ
                  (divUniversalHighWindowOneEquiv
                    (C := C) (pi := pi) hpi g).toLinearMap x.1)) =
            LinearMap.baseChange K
              (divUniversalHighWindowOneEquiv
                (C := C) (pi := pi) hpi g).toLinearMap
              (windowCompare RZ K x.1) := by
        calc
          _ = divUniversalHighWindowAmbientCancelEquiv
                (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 1
                (LinearMap.baseChange K
                  (LinearMap.baseChange RZ
                    (divUniversalHighWindowOneEquiv
                      (C := C) (pi := pi) hpi g).toLinearMap)
                  (1 ⊗ₜ[RZ] x.1)) := by
              rw [LinearMap.baseChange_tmul]
          _ = LinearMap.baseChange K
                (divUniversalHighWindowOneEquiv
                  (C := C) (pi := pi) hpi g).toLinearMap
                (TensorProduct.AlgebraTensorModule.cancelBaseChange k RZ K K
                  ↥(Scheme.divisorSections k
                    ((windowM_choice pi hpi g + windowS_choice pi hpi g) •
                      fiberWeilDivisor pi) ⊤)
                  (1 ⊗ₜ[RZ] x.1)) := by
              simpa only [divUniversalHighWindowAmbientCancelEquiv] using
                divUniversalHighWindowAmbientCancelEquiv_baseChange
                  (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K
                  (divUniversalHighWindowOneEquiv
                    (C := C) (pi := pi) hpi g).toLinearMap
                  (1 ⊗ₜ[RZ] x.1)
          _ = _ := by
              rw [← windowCompare_eq_cancelBaseChange
                (k := k)
                (H := ↥(Scheme.divisorSections k
                  ((windowM_choice pi hpi g + windowS_choice pi hpi g) •
                    fiberWeilDivisor pi) ⊤)) RZ K x.1]
      have hcore :
          divUniversalHighWindowClosedSndRead
              C hpi g r1 r2 b1 b2 i j K (1 ⊗ₜ[RZ] x) =
            ((divUniversalFibreK' C hpi g r1 r2 b2 i j K).subtype.comp
              (divUniversalSndFibreReadEquiv
                (π := pi) C hpi g r1 r2 b1 b2 i j K).toLinearMap)
              (1 ⊗ₜ[RZ] x) := by
        rw [divUniversalHighWindowClosedSndRead, LinearMap.comp_apply,
          LinearMap.comp_apply, LinearMap.comp_apply,
          LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
        change
          ((divUniversalHighWindowClosedAmbientFibreEquiv
              (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 1
              (1 ⊗ₜ[RZ]
                (LinearMap.baseChange RZ
                  (divUniversalHighWindowOneEquiv
                    (C := C) (pi := pi) hpi g).toLinearMap x.1)) : A[1]) :
            (relCurve C K).functionField) =
            ((divUniversalSndFibreReadEquiv
              (π := pi) C hpi g r1 r2 b1 b2 i j K
              (1 ⊗ₜ[RZ] x) :
              divUniversalFibreK' C hpi g r1 r2 b2 i j K) :
              (relCurve C K).functionField)
        rw [divUniversalHighWindowClosedAmbientFibreEquiv_apply
              (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 1
              (1 ⊗ₜ[RZ]
                (LinearMap.baseChange RZ
                  (divUniversalHighWindowOneEquiv
                    (C := C) (pi := pi) hpi g).toLinearMap x.1)),
          hcancel,
          divUniversalSndFibreReadEquiv_one_tmul
            (π := pi) C hpi g r1 r2 b1 b2 i j K x,
          divUniversalHighWindowClosedCoherenceUnit_one,
          hmap]
        exact congrArg
          (fun y : (relCurve C K).functionField =>
            ((msCoherenceUnit C K hpi g :
              (relCurve C K).functionFieldˣ) :
              (relCurve C K).functionField) * y)
          (divFamPhi_baseChange_divisorWindowExponentEquiv
            (C := C) (pi := pi) K hone
            (relThetaPairH1_windowMS C pi hpi g)
            (relThetaPairH1_windowM_add_mulS C pi hpi g 1)
            (windowCompare RZ K x.1))
      rw [TensorProduct.tmul_eq_smul_one_tmul]
      simpa only [map_smul] using congrArg (fun y => c • y) hcore

/-! ## Field-valued image base cases -/

set_option maxHeartbeats 4000000 in
-- The stage-zero range comparison unfolds two nested base changes and ambient transports.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The recursively defined relation has the canonical divisor-window image at
stage zero. -/
theorem divUniversalHighWindowFibreImage_zero :
    DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker 0 := by
  rw [DivUniversalHighWindowFibreImage,
    divUniversalHighWindowRelation_zero_eq_firstWindow,
    Grassmannian.baseChange_map_submodule]
  change Submodule.map
      (divUniversalHighWindowClosedAmbientFibreEquiv
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 0).toLinearMap
      (Submodule.map
        (LinearMap.baseChange K
          (LinearMap.baseChange RZ
            (divUniversalHighWindowZeroEquiv
              (C := C) (pi := pi) hpi g).toLinearMap))
        (LinearMap.range (LinearMap.baseChange K
          ((divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule).subtype))) = _
  rw [← LinearMap.range_comp, ← LinearMap.range_comp]
  rw [divUniversalFibreHighWindowInAmbient,
    divUniversalFibreHighWindow_zero
      C hpi g r1 r2 b1 b2 i j K hO hchi hker]
  exact range_eq_comap_of_equiv_coe K A[0] KM
    ((divUniversalHighWindowClosedAmbientFibreEquiv
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 0).toLinearMap.comp
        ((LinearMap.baseChange K
          (LinearMap.baseChange RZ
            (divUniversalHighWindowZeroEquiv
              (C := C) (pi := pi) hpi g).toLinearMap)).comp
          (LinearMap.baseChange K
            ((divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule).subtype)))
    (divUniversalFstFibreReadEquiv
      (π := pi) C hpi g r1 r2 b1 b2 i j K)
    (divUniversalHighWindowClosedFstRead_eq
      C hpi g r1 r2 b1 b2 i j K)

set_option maxHeartbeats 4000000 in
-- The stage-one range comparison unfolds two nested base changes and ambient transports.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The recursively defined relation has the canonical divisor-window image at
stage one. -/
theorem divUniversalHighWindowFibreImage_one
    (hb : 0 < windowBound pi hpi) :
    DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker 1 := by
  rw [DivUniversalHighWindowFibreImage,
    divUniversalHighWindowRelation_one_eq_secondWindow
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb,
    divUniversalHighWindowStageOne_toSubmodule,
    Grassmannian.baseChange_map_submodule]
  change Submodule.map
      (divUniversalHighWindowClosedAmbientFibreEquiv
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 1).toLinearMap
      (Submodule.map
        (LinearMap.baseChange K
          (LinearMap.baseChange RZ
            (divUniversalHighWindowOneEquiv
              (C := C) (pi := pi) hpi g).toLinearMap))
        (LinearMap.range (LinearMap.baseChange K
          ((divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule).subtype))) = _
  rw [← LinearMap.range_comp, ← LinearMap.range_comp]
  rw [divUniversalFibreHighWindowInAmbient,
    divUniversalFibreHighWindow_one
      C hpi g r1 r2 b1 b2 i j K hO hchi hker]
  exact range_eq_comap_of_equiv_coe K A[1] KMS
    ((divUniversalHighWindowClosedAmbientFibreEquiv
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 1).toLinearMap.comp
        ((LinearMap.baseChange K
          (LinearMap.baseChange RZ
            (divUniversalHighWindowOneEquiv
              (C := C) (pi := pi) hpi g).toLinearMap)).comp
          (LinearMap.baseChange K
            ((divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule).subtype)))
    (divUniversalSndFibreReadEquiv
      (π := pi) C hpi g r1 r2 b1 b2 i j K)
    (divUniversalHighWindowClosedSndRead_eq
      C hpi g r1 r2 b1 b2 i j K)

/-! ## Residue-prime model base cases -/

set_option maxHeartbeats 4000000 in
-- Residue-field specialization expands the complete carve-chart scalar tower.
set_option synthInstance.maxHeartbeats 1000000 in
/-- Every residue field sees the canonical stage-zero fibre image. -/
theorem divUniversalHighWindowFibreModel_zero :
    DivUniversalHighWindowFibreModel
      C hpi g r1 r2 b1 b2 i j hO hchi 0 := by
  intro p
  exact divUniversalHighWindowFibreImage_zero
    C hpi g r1 r2 b1 b2 i j p.asIdeal.ResidueField hO hchi
      (divCarveIdeal_le_ker_of_tower k
        (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi)
        g r1 r2 b1 b2 i j p.asIdeal.ResidueField)

set_option maxHeartbeats 4000000 in
-- Residue-field specialization expands the complete carve-chart scalar tower.
set_option synthInstance.maxHeartbeats 1000000 in
/-- Every residue field sees the canonical stage-one fibre image. -/
theorem divUniversalHighWindowFibreModel_one
    (hb : 0 < windowBound pi hpi) :
    DivUniversalHighWindowFibreModel
      C hpi g r1 r2 b1 b2 i j hO hchi 1 := by
  intro p
  exact divUniversalHighWindowFibreImage_one
    C hpi g r1 r2 b1 b2 i j p.asIdeal.ResidueField hO hchi
      (divCarveIdeal_le_ker_of_tower k
        (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi)
        g r1 r2 b1 b2 i j p.asIdeal.ResidueField) hb

/-! ## Decoupled curve parameter -/

set_option maxHeartbeats 4000000 in
-- Mapping the doubly base-changed first seed through closed normalization is reduction-heavy.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The degree-`g` relation has the canonical stage-zero fibre image for an
independent curve parameter `gamma ≤ g`. -/
theorem divUniversalHighWindowFibreImage_zero_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker 0 := by
  rw [DivUniversalHighWindowFibreImage_at,
    divUniversalHighWindowRelation_zero_eq_firstWindow,
    Grassmannian.baseChange_map_submodule]
  change Submodule.map
      (divUniversalHighWindowClosedAmbientFibreEquiv
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 0).toLinearMap
      (Submodule.map
        (LinearMap.baseChange K
          (LinearMap.baseChange RZ
            (divUniversalHighWindowZeroEquiv
              (C := C) (pi := pi) hpi g).toLinearMap))
        (LinearMap.range (LinearMap.baseChange K
          ((divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule).subtype))) = _
  rw [← LinearMap.range_comp, ← LinearMap.range_comp]
  rw [divUniversalFibreHighWindowInAmbient_at,
    divUniversalFibreHighWindow_zero_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker]
  exact range_eq_comap_of_equiv_coe K A[0] KM
    ((divUniversalHighWindowClosedAmbientFibreEquiv
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 0).toLinearMap.comp
        ((LinearMap.baseChange K
          (LinearMap.baseChange RZ
            (divUniversalHighWindowZeroEquiv
              (C := C) (pi := pi) hpi g).toLinearMap)).comp
          (LinearMap.baseChange K
            ((divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule).subtype)))
    (divUniversalFstFibreReadEquiv
      (π := pi) C hpi g r1 r2 b1 b2 i j K)
    (divUniversalHighWindowClosedFstRead_eq
      C hpi g r1 r2 b1 b2 i j K)

set_option maxHeartbeats 4000000 in
-- Mapping the doubly base-changed second seed through closed normalization is reduction-heavy.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The degree-`g` relation has the canonical stage-one fibre image for an
independent curve parameter `gamma ≤ g`. -/
theorem divUniversalHighWindowFibreImage_one_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker 1 := by
  rw [DivUniversalHighWindowFibreImage_at,
    divUniversalHighWindowRelation_one_eq_secondWindow_at
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchiGamma,
    divUniversalHighWindowStageOne_toSubmodule,
    Grassmannian.baseChange_map_submodule]
  change Submodule.map
      (divUniversalHighWindowClosedAmbientFibreEquiv
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 1).toLinearMap
      (Submodule.map
        (LinearMap.baseChange K
          (LinearMap.baseChange RZ
            (divUniversalHighWindowOneEquiv
              (C := C) (pi := pi) hpi g).toLinearMap))
        (LinearMap.range (LinearMap.baseChange K
          ((divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule).subtype))) = _
  rw [← LinearMap.range_comp, ← LinearMap.range_comp]
  rw [divUniversalFibreHighWindowInAmbient_at,
    divUniversalFibreHighWindow_one_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker]
  exact range_eq_comap_of_equiv_coe K A[1] KMS
    ((divUniversalHighWindowClosedAmbientFibreEquiv
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K 1).toLinearMap.comp
        ((LinearMap.baseChange K
          (LinearMap.baseChange RZ
            (divUniversalHighWindowOneEquiv
              (C := C) (pi := pi) hpi g).toLinearMap)).comp
          (LinearMap.baseChange K
            ((divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule).subtype)))
    (divUniversalSndFibreReadEquiv
      (π := pi) C hpi g r1 r2 b1 b2 i j K)
    (divUniversalHighWindowClosedSndRead_eq
      C hpi g r1 r2 b1 b2 i j K)

set_option maxHeartbeats 4000000 in
-- Residue-field specialization reconstructs the complete carve-chart scalar tower.
set_option synthInstance.maxHeartbeats 1000000 in
/-- Every residue field sees the off-diagonal canonical stage-zero image. -/
theorem divUniversalHighWindowFibreModel_zero_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    DivUniversalHighWindowFibreModel_at
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma 0 := by
  intro p
  exact divUniversalHighWindowFibreImage_zero_at
    C hpi g r1 r2 b1 b2 i j p.asIdeal.ResidueField
      (divCarveIdeal_le_ker_of_tower k
        (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi)
        g r1 r2 b1 b2 i j p.asIdeal.ResidueField)
      hgamma hchiGamma

set_option maxHeartbeats 4000000 in
-- Residue-field specialization reconstructs the complete carve-chart scalar tower.
set_option synthInstance.maxHeartbeats 1000000 in
/-- Every residue field sees the off-diagonal canonical stage-one image. -/
theorem divUniversalHighWindowFibreModel_one_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    DivUniversalHighWindowFibreModel_at
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma 1 := by
  intro p
  exact divUniversalHighWindowFibreImage_one_at
    C hpi g r1 r2 b1 b2 i j p.asIdeal.ResidueField
      (divCarveIdeal_le_ker_of_tower k
        (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi)
        g r1 r2 b1 b2 i j p.asIdeal.ResidueField)
      hgamma hchiGamma

end HighWindowFibreModelBase

end AlgebraicGeometry
