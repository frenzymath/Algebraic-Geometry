/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowRelationFibreEquiv
import AlgebraicJacobian.Picard.DivSchemeHighWindowRelativeKoszul

/-!
# Fibre conjugacy for high-window multiplication

At a field-valued carve-chart point, a projective high-window quotient identifies
the scalar extension of its relation with the canonical divisor fibre window.
Distributing scalar extension over the finite product source gives the corresponding
product equivalence.  Under that equivalence and the closed-ambient normalization,
the relative high-window multiplication map is the concrete finite multiplication
map indexed by the scalar extension of the fixed multiplier basis.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section HighWindowMulConjugacy

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowMulConjugacy :
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

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
local notation "HS0" => ↥( Scheme.divisorSections k
  (windowS_choice pi hpi g • fiberWeilDivisor pi) ⊤)
local notation "HI" => Fin (Module.finrank k HS0)
local notation "Amb[" n "]" => divUniversalHighWindowAmbient
  (C := C) (pi := pi) (hpi := hpi) (g := g)
    (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n
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

noncomputable local instance instIsIntegralRelCurveHighWindowMulConjugacy :
    IsIntegral (relCurve C K) := instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveHighWindowMulConjugacy :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveHighWindowMulConjugacy :
    QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTRelCurveHighWindowMulConjugacy :
    LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveHighWindowMulConjugacy :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

noncomputable local instance instFinH1RelCurveHighWindowMulConjugacy :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
  (hker : divCarveIdeal k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j ≤
        RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))

local notation "HF[" n "]" => divUniversalFibreHighWindow
  C hpi g r1 r2 b1 b2 i j K hO hchi hker n

set_option maxHeartbeats 2400000 in
-- The dependent finite product and relation quotient need a larger reduction budget.
set_option synthInstance.maxHeartbeats 800000 in
-- Projectivity transport traverses the full carve-ring scalar tower.
/-- Scalar extension distributes over the finite multiplication source, and
each relation component is then read in the canonical divisor fibre window. -/
noncomputable def divUniversalHighWindowMulSourceFibreEquiv (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n) :
    K ⊗[RZ] DivUniversalHighWindowMulSource (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n Kr[n] ≃ₗ[K]
      (HI → ↥HF[n]) :=
  (TensorProduct.piRight RZ K K (fun _ : HI => ↥Kr[n])).trans
    (LinearEquiv.piCongrRight fun _ : HI =>
      divUniversalHighWindowRelationFibreEquiv
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n himage)

set_option maxHeartbeats 2400000 in
-- Reducing the composite finite-product equivalence exceeds the default budget.
set_option synthInstance.maxHeartbeats 800000 in
-- The pointwise relation-fibre equivalence has a deep instance chain.
@[simp]
theorem divUniversalHighWindowMulSourceFibreEquiv_apply (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n)
    (x : K ⊗[RZ] DivUniversalHighWindowMulSource (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n Kr[n]) (t : HI) :
    divUniversalHighWindowMulSourceFibreEquiv
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n himage x t =
      divUniversalHighWindowRelationFibreEquiv
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n himage
        (TensorProduct.piRightHom RZ K K (fun _ : HI => ↥Kr[n]) x t) := by
  rw [divUniversalHighWindowMulSourceFibreEquiv, LinearEquiv.trans_apply,
    TensorProduct.piRight_apply]
  rfl

set_option maxHeartbeats 2400000 in
-- The normalized ambient contains the full dependent high-window expression.
set_option synthInstance.maxHeartbeats 800000 in
-- Scalar extension through the carve ring needs additional instance search.
/-- Read a scalar-extended high-window ambient as an element of the function
field of the fibre curve. -/
noncomputable def divUniversalHighWindowClosedAmbientFibreRead (n : Nat) :
    (K ⊗[RZ] Amb[n]) →ₗ[K] (relCurve C K).functionField :=
  (Scheme.divisorSections K
      (windowN C K hpi g + n • windowS C K hpi g) ⊤).subtype.comp
    (divUniversalHighWindowClosedAmbientFibreEquiv
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K n).toLinearMap

@[simp]
theorem divUniversalHighWindowClosedAmbientFibreRead_apply (n : Nat)
    (x : K ⊗[RZ] Amb[n]) :
    divUniversalHighWindowClosedAmbientFibreRead
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K n x =
      (divUniversalHighWindowClosedAmbientFibreEquiv
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K n x :
          (relCurve C K).functionField) :=
  rfl

set_option maxHeartbeats 4000000 in
-- Comparing the relative row with fibre multiplication is reduction-heavy.
set_option synthInstance.maxHeartbeats 1000000 in
-- Both relation and closed-ambient scalar towers must be synthesized.
set_option maxRecDepth 20000 in
/-- One relative multiplication row becomes multiplication by the corresponding
member of the scalar-extended fixed multiplier basis. -/
theorem divUniversalHighWindowMulRow_fibre_conjugacy (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n)
    (t : HI) (x : K ⊗[RZ] ↥Kr[n]) :
    divUniversalHighWindowClosedAmbientFibreRead
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K (n + 1)
        (LinearMap.baseChange K
          (divUniversalHighWindowMulRow (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j n Kr[n] t) x) =
      (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K t :
          (relCurve C K).functionField) *
        (divUniversalHighWindowRelationFibreEquiv
          C hpi g r1 r2 b1 b2 i j K hO hchi hker n himage x :
            (relCurve C K).functionField) := by
  rw [divUniversalHighWindowClosedAmbientFibreRead_apply,
    divUniversalHighWindowMulRow, LinearMap.baseChange_comp,
    LinearMap.comp_apply,
    divUniversalHighWindowClosedAmbientFibreEquiv_shiftMul,
    divUniversalHighWindowRelationFibreEquiv_coe]
  simp only [divUniversalMultiplierFibreBasis, Module.Basis.map_apply,
    Module.Basis.baseChange_apply]

set_option maxHeartbeats 4000000 in
-- Expanding the finite component sum and its fibre reads exceeds the default budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- Each summand carries the dependent relation-fibre equivalence.
set_option maxRecDepth 20000 in
/-- The base change of the whole relative high-window multiplication map is
conjugate to the fixed-field finite multiplication map. -/
theorem divUniversalHighWindowMulMap_fibre_conjugacy (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n)
    (x : K ⊗[RZ] DivUniversalHighWindowMulSource (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n Kr[n]) :
    divUniversalHighWindowClosedAmbientFibreRead
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K (n + 1)
        (LinearMap.baseChange K
          (divUniversalHighWindowMulMap (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j n Kr[n]) x) =
      Scheme.finiteMulMap
        (Scheme.divisorSections K (windowS C K hpi g) ⊤) HF[n]
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)
        (divUniversalHighWindowMulSourceFibreEquiv
          C hpi g r1 r2 b1 b2 i j K hO hchi hker n himage x) := by
  rw [divUniversalHighWindowMulMap_eq_finiteComponentSum,
    baseChange_finiteComponentSum, LinearMap.comp_apply,
    LinearMap.sum_apply, map_sum, Scheme.finiteMulMap_apply]
  apply Finset.sum_congr rfl
  intro t _
  simp only [LinearMap.comp_apply, LinearMap.proj_apply,
    divUniversalHighWindowMulSourceFibreEquiv_apply]
  exact divUniversalHighWindowMulRow_fibre_conjugacy
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K hO hchi hker n himage t
      (TensorProduct.piRightHom RZ K K (fun _ : HI => ↥Kr[n]) x t)

set_option maxHeartbeats 4000000 in
-- Equality of the two large dependent linear maps needs a larger reduction budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- The map-level statement retains the projective relation quotient instance.
set_option maxRecDepth 20000 in
/-- Linear-map form of `divUniversalHighWindowMulMap_fibre_conjugacy`. -/
theorem divUniversalHighWindowMulMap_fibre_conjugacy_map (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n) :
    (divUniversalHighWindowClosedAmbientFibreRead
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K (n + 1)).comp
      (LinearMap.baseChange K
        (divUniversalHighWindowMulMap (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n Kr[n])) =
    (Scheme.finiteMulMap
        (Scheme.divisorSections K (windowS C K hpi g) ⊤) HF[n]
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)).comp
      (divUniversalHighWindowMulSourceFibreEquiv
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n himage).toLinearMap := by
  ext x
  exact divUniversalHighWindowMulMap_fibre_conjugacy
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K hO hchi hker n himage x

/-! ## Decoupled fibre conjugacy -/

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- Scalar extension of the multiplication source, read in the off-diagonal canonical
divisor fibre window. -/
noncomputable def divUniversalHighWindowMulSourceFibreEquiv_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j ≤
        RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (n : Nat) [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n) :
    K ⊗[RZ] DivUniversalHighWindowMulSource (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n Kr[n] ≃ₗ[K]
      (HI → ↥(divUniversalFibreHighWindow_at
        C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n)) :=
  (TensorProduct.piRight RZ K K (fun _ : HI => ↥Kr[n])).trans
    (LinearEquiv.piCongrRight fun _ : HI =>
      divUniversalHighWindowRelationFibreEquiv_at
        C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n himage)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
@[simp]
theorem divUniversalHighWindowMulSourceFibreEquiv_apply_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j ≤
        RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (n : Nat) [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n)
    (x : K ⊗[RZ] DivUniversalHighWindowMulSource (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n Kr[n]) (t : HI) :
    divUniversalHighWindowMulSourceFibreEquiv_at
        C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n himage x t =
      divUniversalHighWindowRelationFibreEquiv_at
        C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n himage
        (TensorProduct.piRightHom RZ K K (fun _ : HI => ↥Kr[n]) x t) := by
  rw [divUniversalHighWindowMulSourceFibreEquiv_at, LinearEquiv.trans_apply,
    TensorProduct.piRight_apply]
  rfl

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- One relative multiplication row becomes fibre multiplication in the off-diagonal
canonical divisor window. -/
theorem divUniversalHighWindowMulRow_fibre_conjugacy_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j ≤
        RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (n : Nat) [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n)
    (t : HI) (x : K ⊗[RZ] ↥Kr[n]) :
    divUniversalHighWindowClosedAmbientFibreRead
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K (n + 1)
        (LinearMap.baseChange K
          (divUniversalHighWindowMulRow (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j n Kr[n] t) x) =
      (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K t :
          (relCurve C K).functionField) *
        (divUniversalHighWindowRelationFibreEquiv_at
          C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n himage x :
            (relCurve C K).functionField) := by
  rw [divUniversalHighWindowClosedAmbientFibreRead_apply,
    divUniversalHighWindowMulRow, LinearMap.baseChange_comp,
    LinearMap.comp_apply,
    divUniversalHighWindowClosedAmbientFibreEquiv_shiftMul,
    divUniversalHighWindowRelationFibreEquiv_coe_at]
  simp only [divUniversalMultiplierFibreBasis, Module.Basis.map_apply,
    Module.Basis.baseChange_apply]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- The whole relative high-window multiplication map is conjugate to finite
multiplication in the off-diagonal canonical fibre. -/
theorem divUniversalHighWindowMulMap_fibre_conjugacy_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j ≤
        RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (n : Nat) [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n)
    (x : K ⊗[RZ] DivUniversalHighWindowMulSource (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n Kr[n]) :
    divUniversalHighWindowClosedAmbientFibreRead
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K (n + 1)
        (LinearMap.baseChange K
          (divUniversalHighWindowMulMap (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j n Kr[n]) x) =
      Scheme.finiteMulMap
        (Scheme.divisorSections K (windowS C K hpi g) ⊤)
        (divUniversalFibreHighWindow_at
          C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n)
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)
        (divUniversalHighWindowMulSourceFibreEquiv_at
          C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n himage x) := by
  rw [divUniversalHighWindowMulMap_eq_finiteComponentSum,
    baseChange_finiteComponentSum, LinearMap.comp_apply,
    LinearMap.sum_apply, map_sum, Scheme.finiteMulMap_apply]
  apply Finset.sum_congr rfl
  intro t _
  simp only [LinearMap.comp_apply, LinearMap.proj_apply,
    divUniversalHighWindowMulSourceFibreEquiv_apply_at]
  exact divUniversalHighWindowMulRow_fibre_conjugacy_at
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K
      hgamma hχgamma hkerGamma n himage t
      (TensorProduct.piRightHom RZ K K (fun _ : HI => ↥Kr[n]) x t)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- Linear-map form of the decoupled multiplication conjugacy. -/
theorem divUniversalHighWindowMulMap_fibre_conjugacy_map_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j ≤
        RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (n : Nat) [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n) :
    (divUniversalHighWindowClosedAmbientFibreRead
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K (n + 1)).comp
      (LinearMap.baseChange K
        (divUniversalHighWindowMulMap (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n Kr[n])) =
    (Scheme.finiteMulMap
        (Scheme.divisorSections K (windowS C K hpi g) ⊤)
        (divUniversalFibreHighWindow_at
          C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n)
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)).comp
      (divUniversalHighWindowMulSourceFibreEquiv_at
        C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n himage).toLinearMap := by
  ext x
  exact divUniversalHighWindowMulMap_fibre_conjugacy_at
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K
      hgamma hχgamma hkerGamma n himage x

end HighWindowMulConjugacy

end AlgebraicGeometry
