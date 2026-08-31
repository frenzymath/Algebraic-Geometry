/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowFibreModelBase
import AlgebraicJacobian.Picard.DivSchemeHighWindowRelationKoszulConjugacy

/-!
# Induction for the relative high-window fibre model

The relative successor multiplication map is transported to multiplication
of canonical divisor windows on every residue field.  Its image is therefore
the next canonical window.  Coupled with the relative Koszul criterion, this
gives a simultaneous induction proving the fibre model and projectivity of
every finite-stage relation quotient over the nonreduced carve ring.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 16000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section HighWindowFibreModelInduction

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowFibreModelInduction :
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
local notation "HS0" => ↥(Scheme.divisorSections k
  (windowS_choice pi hpi g • fiberWeilDivisor pi) ⊤)
local notation "HI" => Fin (Module.finrank k HS0)
local notation "Amb[" n "]" => divUniversalHighWindowAmbient
  (C := C) (pi := pi) (hpi := hpi) (g := g)
    (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n
local notation "Kr[" n "]" => divUniversalHighWindowRelation
  (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n
local notation "Q[" n "]" => divUniversalHighWindowRelationQuotient
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

noncomputable local instance instIsIntegralRelCurveHighWindowFibreModelInduction :
    IsIntegral (relCurve C K) := instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveHighWindowFibreModelInduction :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveHighWindowFibreModelInduction :
    QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTRelCurveHighWindowFibreModelInduction :
    LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveHighWindowFibreModelInduction :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

noncomputable local instance instFinH1RelCurveHighWindowFibreModelInduction :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
  (hker : divCarveIdeal k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j ≤ RingHom.ker
        (algebraMap (PairChartRing k g r1 g r2 i j) K))

local notation "HF[" n "]" => divUniversalFibreHighWindow
  C hpi g r1 r2 b1 b2 i j K hO hchi hker n
local notation "FA[" n "]" => divUniversalFibreHighWindowInAmbient
  C hpi g r1 r2 b1 b2 i j K hO hchi hker n
local notation "CA[" n "]" => Scheme.divisorSections K
  (windowN C K hpi g + n • windowS C K hpi g) ⊤

/-! ## The fibre successor map -/

set_option maxHeartbeats 2400000 in
-- The two nested section submodules and the dependent finite source are expensive to elaborate.
set_option synthInstance.maxHeartbeats 800000 in
/-- The finite fibre multiplication map, corestricted to the next canonical
window and then viewed inside the closed ambient divisor window. -/
noncomputable def divUniversalFibreHighWindowMulMapToInAmbient
    (hb : 0 < windowBound pi hpi) (n : Nat) :
    (HI → ↥HF[n]) →ₗ[K] ↥FA[n + 1] :=
  (divUniversalFibreHighWindowInAmbientEquiv
      C hpi g r1 r2 b1 b2 i j K hO hchi hker (n + 1)).symm.toLinearMap.comp
    (Scheme.finiteMulMapTo
      (Scheme.divisorSections K (windowS C K hpi g) ⊤) HF[n] HF[n + 1]
      (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)
      (divUniversalFibreHighWindow_mulSpan_eq_of_windowBound_pos
        C hpi g r1 r2 b1 b2 i j K hO hchi hker hb n))

set_option maxHeartbeats 2400000 in
-- The codomain retains both the closed-ambient and canonical-window subtype layers.
set_option synthInstance.maxHeartbeats 800000 in
/-- The same finite fibre multiplication map with codomain the closed ambient
divisor window. -/
noncomputable def divUniversalFibreHighWindowMulMapToClosedAmbient
    (hb : 0 < windowBound pi hpi) (n : Nat) :
    (HI → ↥HF[n]) →ₗ[K] ↥CA[n + 1] :=
  FA[n + 1].subtype.comp
    (divUniversalFibreHighWindowMulMapToInAmbient
      C hpi g r1 r2 b1 b2 i j K hO hchi hker hb n)

set_option maxHeartbeats 2400000 in
-- Normalizing the inverse nested-submodule equivalence exceeds the default budget.
set_option synthInstance.maxHeartbeats 800000 in
/-- The inverse in-ambient equivalence also preserves the underlying
function-field element. -/
@[simp]
theorem divUniversalFibreHighWindowInAmbientEquiv_symm_coe (n : Nat)
    (x : ↥HF[n]) :
    (((((divUniversalFibreHighWindowInAmbientEquiv
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n).symm x : ↥FA[n]) :
      ↥CA[n]) : (relCurve C K).functionField)) =
      (x : (relCurve C K).functionField) := by
  simpa only [LinearEquiv.apply_symm_apply] using
    (divUniversalFibreHighWindowInAmbientEquiv_coe
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n
        ((divUniversalFibreHighWindowInAmbientEquiv
          C hpi g r1 r2 b1 b2 i j K hO hchi hker n).symm x)).symm

set_option maxHeartbeats 2400000 in
-- Reducing the two nested corestrictions retains the full canonical-window expression.
set_option synthInstance.maxHeartbeats 800000 in
/-- The closed-ambient fibre successor map reads as the ordinary finite
multiplication map in the function field. -/
@[simp]
theorem divUniversalFibreHighWindowMulMapToClosedAmbient_coe
    (hb : 0 < windowBound pi hpi) (n : Nat) (x : HI → ↥HF[n]) :
    ((divUniversalFibreHighWindowMulMapToClosedAmbient
        C hpi g r1 r2 b1 b2 i j K hO hchi hker hb n x : ↥CA[n + 1]) :
      (relCurve C K).functionField) =
      Scheme.finiteMulMap
        (Scheme.divisorSections K (windowS C K hpi g) ⊤) HF[n]
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K) x := by
  rw [divUniversalFibreHighWindowMulMapToClosedAmbient,
    divUniversalFibreHighWindowMulMapToInAmbient, LinearMap.comp_apply,
    Submodule.subtype_apply]
  calc
    _ = ((Scheme.finiteMulMapTo
        (Scheme.divisorSections K (windowS C K hpi g) ⊤) HF[n] HF[n + 1]
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)
        (divUniversalFibreHighWindow_mulSpan_eq_of_windowBound_pos
          C hpi g r1 r2 b1 b2 i j K hO hchi hker hb n) x : ↥HF[n + 1]) :
          (relCurve C K).functionField) :=
      divUniversalFibreHighWindowInAmbientEquiv_symm_coe
        C hpi g r1 r2 b1 b2 i j K hO hchi hker (n + 1) _
    _ = _ := by
      exact LinearMap.codRestrict_apply _ _ _

set_option maxHeartbeats 3200000 in
-- Surjectivity is transported through the dependent canonical-window equivalence.
set_option synthInstance.maxHeartbeats 800000 in
/-- The closed-ambient fibre successor map has exactly the next canonical
window as its range. -/
theorem range_divUniversalFibreHighWindowMulMapToClosedAmbient
    (hb : 0 < windowBound pi hpi) (n : Nat) :
    LinearMap.range
      (divUniversalFibreHighWindowMulMapToClosedAmbient
        C hpi g r1 r2 b1 b2 i j K hO hchi hker hb n) = FA[n + 1] := by
  have hsurj : Function.Surjective
      (divUniversalFibreHighWindowMulMapToInAmbient
        C hpi g r1 r2 b1 b2 i j K hO hchi hker hb n) :=
    (divUniversalFibreHighWindowInAmbientEquiv
      C hpi g r1 r2 b1 b2 i j K hO hchi hker (n + 1)).symm.surjective.comp
      (Scheme.finiteMulMapTo_surjective
        (Scheme.divisorSections K (windowS C K hpi g) ⊤) HF[n] HF[n + 1]
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)
        (divUniversalFibreHighWindow_mulSpan_eq_of_windowBound_pos
          C hpi g r1 r2 b1 b2 i j K hO hchi hker hb n))
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (divUniversalFibreHighWindowMulMapToInAmbient
      C hpi g r1 r2 b1 b2 i j K hO hchi hker hb n x).property
  · intro hy
    obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
    refine ⟨x, ?_⟩
    simpa only [divUniversalFibreHighWindowMulMapToClosedAmbient,
      LinearMap.comp_apply, Submodule.subtype_apply] using congrArg Subtype.val hx

set_option maxHeartbeats 4000000 in
-- Comparing the relative multiplication map with the doubly corestricted fibre map is costly.
set_option synthInstance.maxHeartbeats 1000000 in
-- The source equivalence retains the projective relation quotient and the full scalar tower.
set_option maxRecDepth 20000 in
/-- The relative successor multiplication map becomes the closed-ambient
canonical fibre multiplication map after scalar extension. -/
theorem divUniversalHighWindowMulMap_fibre_conjugacy_closedAmbient
    (hb : 0 < windowBound pi hpi) (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n)
    (x : K ⊗[RZ] DivUniversalHighWindowMulSource (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n Kr[n]) :
    divUniversalHighWindowClosedAmbientFibreEquiv
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K (n + 1)
        (LinearMap.baseChange K
          (divUniversalHighWindowMulMap (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j n Kr[n]) x) =
      divUniversalFibreHighWindowMulMapToClosedAmbient
        C hpi g r1 r2 b1 b2 i j K hO hchi hker hb n
        (divUniversalHighWindowMulSourceFibreEquiv
          C hpi g r1 r2 b1 b2 i j K hO hchi hker n himage x) := by
  apply Subtype.ext
  simpa only [divUniversalHighWindowClosedAmbientFibreRead_apply,
    divUniversalFibreHighWindowMulMapToClosedAmbient_coe] using
    (divUniversalHighWindowMulMap_fibre_conjugacy
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K hO hchi hker n himage x)

set_option maxHeartbeats 4000000 in
-- Rewriting the recursive range and transporting its scalar extension is reduction-heavy.
set_option synthInstance.maxHeartbeats 1000000 in
-- The source and target fibre equivalences both carry the carve-ring scalar tower.
set_option maxRecDepth 20000 in
/-- If stage `n` has the canonical fibre image and its quotient is projective,
then the successor relation has the next canonical fibre image. -/
theorem divUniversalHighWindowFibreImage_succ_of_projective
    (hb : 0 < windowBound pi hpi) (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n) :
    DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker (n + 1) := by
  unfold DivUniversalHighWindowFibreImage
  cases n with
  | zero =>
      -- The recursive relation has a separate seed at stage one.
      exact divUniversalHighWindowFibreImage_one
        C hpi g r1 r2 b1 b2 i j K hO hchi hker hb
  | succ n =>
      rw [divUniversalHighWindowRelation_succ_succ]
      change
        Submodule.map
            (divUniversalHighWindowClosedAmbientFibreEquiv
              (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K (n + 2)).toLinearMap
            (Submodule.baseChange K
              (LinearMap.range
                (divUniversalHighWindowMulMap (C := C) (pi := pi)
                  hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1]))) =
          FA[n + 2]
      calc
        _ = LinearMap.range
            (divUniversalFibreHighWindowMulMapToClosedAmbient
              C hpi g r1 r2 b1 b2 i j K hO hchi hker hb (n + 1)) :=
          map_baseChange_range_eq_range_of_conjugate
            (divUniversalHighWindowMulMap (C := C) (pi := pi)
              hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1])
            (divUniversalFibreHighWindowMulMapToClosedAmbient
              C hpi g r1 r2 b1 b2 i j K hO hchi hker hb (n + 1))
            (divUniversalHighWindowMulSourceFibreEquiv
              C hpi g r1 r2 b1 b2 i j K hO hchi hker (n + 1) himage)
            (divUniversalHighWindowClosedAmbientFibreEquiv
              (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K (n + 2))
            (fun x => divUniversalHighWindowMulMap_fibre_conjugacy_closedAmbient
              (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K hO hchi hker
                hb (n + 1) himage x)
        _ = FA[n + 2] :=
          range_divUniversalFibreHighWindowMulMapToClosedAmbient
            C hpi g r1 r2 b1 b2 i j K hO hchi hker hb (n + 1)

/-! ## Decoupled fibre successor map -/

variable {gamma : Nat} (hgamma : gamma ≤ g)
  (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))

local notation "HFγ[" n "]" => divUniversalFibreHighWindow_at
  C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n
local notation "FAγ[" n "]" => divUniversalFibreHighWindowInAmbient_at
  C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n

set_option maxHeartbeats 2400000 in
-- The source and target retain nested off-diagonal canonical-window subtypes.
set_option synthInstance.maxHeartbeats 800000 in
/-- The finite fibre multiplication map corestricted to the next canonical
off-diagonal window. -/
noncomputable def divUniversalFibreHighWindowMulMapToInAmbient_at (n : Nat) :
    (HI → ↥HFγ[n]) →ₗ[K] ↥FAγ[n + 1] :=
  (divUniversalFibreHighWindowInAmbientEquiv_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker (n + 1)).symm.toLinearMap.comp
    (Scheme.finiteMulMapTo
      (Scheme.divisorSections K (windowS C K hpi g) ⊤) HFγ[n] HFγ[n + 1]
      (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)
      (divUniversalFibreHighWindow_mulSpan_eq_at
        C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n))

set_option maxHeartbeats 2400000 in
-- Corestricting the successor map into the closed ambient subtype is expensive.
set_option synthInstance.maxHeartbeats 800000 in
/-- The off-diagonal finite fibre multiplication map with codomain the closed
ambient divisor window. -/
noncomputable def divUniversalFibreHighWindowMulMapToClosedAmbient_at (n : Nat) :
    (HI → ↥HFγ[n]) →ₗ[K] ↥CA[n + 1] :=
  FAγ[n + 1].subtype.comp
    (divUniversalFibreHighWindowMulMapToInAmbient_at
      C hpi g r1 r2 b1 b2 i j K hker hgamma hchiGamma n)

set_option maxHeartbeats 2400000 in
-- Normalizing the inverse nested-submodule equivalence exceeds the default budget.
set_option synthInstance.maxHeartbeats 800000 in
@[simp]
theorem divUniversalFibreHighWindowInAmbientEquiv_symm_coe_at (n : Nat)
    (x : ↥HFγ[n]) :
    (((((divUniversalFibreHighWindowInAmbientEquiv_at
        C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n).symm x : ↥FAγ[n]) :
      ↥CA[n]) : (relCurve C K).functionField)) =
      (x : (relCurve C K).functionField) := by
  simpa only [LinearEquiv.apply_symm_apply] using
    (divUniversalFibreHighWindowInAmbientEquiv_coe_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n
        ((divUniversalFibreHighWindowInAmbientEquiv_at
          C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n).symm x)).symm

set_option maxHeartbeats 2400000 in
-- Reducing the two nested corestrictions retains the full canonical-window expression.
set_option synthInstance.maxHeartbeats 800000 in
@[simp]
theorem divUniversalFibreHighWindowMulMapToClosedAmbient_coe_at
    (n : Nat) (x : HI → ↥HFγ[n]) :
    ((divUniversalFibreHighWindowMulMapToClosedAmbient_at
        C hpi g r1 r2 b1 b2 i j K hker hgamma hchiGamma n x : ↥CA[n + 1]) :
      (relCurve C K).functionField) =
      Scheme.finiteMulMap
        (Scheme.divisorSections K (windowS C K hpi g) ⊤) HFγ[n]
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K) x := by
  rw [divUniversalFibreHighWindowMulMapToClosedAmbient_at,
    divUniversalFibreHighWindowMulMapToInAmbient_at, LinearMap.comp_apply,
    Submodule.subtype_apply]
  calc
    _ = ((Scheme.finiteMulMapTo
        (Scheme.divisorSections K (windowS C K hpi g) ⊤) HFγ[n] HFγ[n + 1]
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)
        (divUniversalFibreHighWindow_mulSpan_eq_at
          C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n) x : ↥HFγ[n + 1]) :
          (relCurve C K).functionField) :=
      divUniversalFibreHighWindowInAmbientEquiv_symm_coe_at
        C hpi g r1 r2 b1 b2 i j K hker hgamma hchiGamma (n + 1) _
    _ = _ := LinearMap.codRestrict_apply _ _ _

set_option maxHeartbeats 3200000 in
-- Surjectivity is transported through the dependent canonical-window equivalence.
set_option synthInstance.maxHeartbeats 800000 in
/-- The off-diagonal closed-ambient successor map has exactly the next
canonical window as its range. -/
theorem range_divUniversalFibreHighWindowMulMapToClosedAmbient_at (n : Nat) :
    LinearMap.range
      (divUniversalFibreHighWindowMulMapToClosedAmbient_at
        C hpi g r1 r2 b1 b2 i j K hker hgamma hchiGamma n) = FAγ[n + 1] := by
  have hsurj : Function.Surjective
      (divUniversalFibreHighWindowMulMapToInAmbient_at
        C hpi g r1 r2 b1 b2 i j K hker hgamma hchiGamma n) :=
    (divUniversalFibreHighWindowInAmbientEquiv_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker (n + 1)).symm.surjective.comp
      (Scheme.finiteMulMapTo_surjective
        (Scheme.divisorSections K (windowS C K hpi g) ⊤) HFγ[n] HFγ[n + 1]
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)
        (divUniversalFibreHighWindow_mulSpan_eq_at
          C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n))
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (divUniversalFibreHighWindowMulMapToInAmbient_at
      C hpi g r1 r2 b1 b2 i j K hker hgamma hchiGamma n x).property
  · intro hy
    obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
    refine ⟨x, ?_⟩
    simpa only [divUniversalFibreHighWindowMulMapToClosedAmbient_at,
      LinearMap.comp_apply, Submodule.subtype_apply] using congrArg Subtype.val hx

set_option maxHeartbeats 4000000 in
-- Comparing the relative multiplication map with the closed-ambient map is costly.
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- The relative successor map becomes the off-diagonal closed-ambient
canonical multiplication map after scalar extension. -/
theorem divUniversalHighWindowMulMap_fibre_conjugacy_closedAmbient_at
    (n : Nat) [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n)
    (x : K ⊗[RZ] DivUniversalHighWindowMulSource (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n Kr[n]) :
    divUniversalHighWindowClosedAmbientFibreEquiv
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K (n + 1)
        (LinearMap.baseChange K
          (divUniversalHighWindowMulMap (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j n Kr[n]) x) =
      divUniversalFibreHighWindowMulMapToClosedAmbient_at
        C hpi g r1 r2 b1 b2 i j K hker hgamma hchiGamma n
        (divUniversalHighWindowMulSourceFibreEquiv_at
          C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n himage x) := by
  apply Subtype.ext
  simpa only [divUniversalHighWindowClosedAmbientFibreRead_apply,
    divUniversalFibreHighWindowMulMapToClosedAmbient_coe_at] using
    (divUniversalHighWindowMulMap_fibre_conjugacy_at
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker
        n himage x)

set_option maxHeartbeats 4000000 in
-- Rewriting the recursive range and transporting its scalar extension is reduction-heavy.
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- A projective off-diagonal stage with canonical fibre image passes that
image to its successor. -/
theorem divUniversalHighWindowFibreImage_succ_of_projective_at
    (n : Nat) [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n) :
    DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker (n + 1) := by
  unfold DivUniversalHighWindowFibreImage_at
  cases n with
  | zero =>
      exact divUniversalHighWindowFibreImage_one_at
        C hpi g r1 r2 b1 b2 i j K hker hgamma hchiGamma
  | succ n =>
      rw [divUniversalHighWindowRelation_succ_succ]
      change
        Submodule.map
            (divUniversalHighWindowClosedAmbientFibreEquiv
              (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K (n + 2)).toLinearMap
            (Submodule.baseChange K
              (LinearMap.range
                (divUniversalHighWindowMulMap (C := C) (pi := pi)
                  hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1]))) =
          FAγ[n + 2]
      calc
        _ = LinearMap.range
            (divUniversalFibreHighWindowMulMapToClosedAmbient_at
              C hpi g r1 r2 b1 b2 i j K hker hgamma hchiGamma (n + 1)) :=
          map_baseChange_range_eq_range_of_conjugate
            (divUniversalHighWindowMulMap (C := C) (pi := pi)
              hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1])
            (divUniversalFibreHighWindowMulMapToClosedAmbient_at
              C hpi g r1 r2 b1 b2 i j K hker hgamma hchiGamma (n + 1))
            (divUniversalHighWindowMulSourceFibreEquiv_at
              C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker (n + 1) himage)
            (divUniversalHighWindowClosedAmbientFibreEquiv
              (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K (n + 2))
            (fun x => divUniversalHighWindowMulMap_fibre_conjugacy_closedAmbient_at
              (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K hker
                hgamma hchiGamma (n + 1) himage x)
        _ = FAγ[n + 2] :=
          range_divUniversalFibreHighWindowMulMapToClosedAmbient_at
            C hpi g r1 r2 b1 b2 i j K hker hgamma hchiGamma (n + 1)

end HighWindowFibreModelInduction

section HighWindowFibreModelGlobalInduction

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowFibreModelGlobalInduction :
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
local notation "Amb[" n "]" => divUniversalHighWindowAmbient
  (C := C) (pi := pi) (hpi := hpi) (g := g)
    (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n
local notation "Kr[" n "]" => divUniversalHighWindowRelation
  (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n
local notation "Q[" n "]" => divUniversalHighWindowRelationQuotient
  (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

set_option maxHeartbeats 4800000 in
-- Every residue field reconstructs the full carve-chart scalar tower and successor square.
set_option synthInstance.maxHeartbeats 1200000 in
-- The projective relation quotient is used to construct the source fibre equivalence.
set_option maxRecDepth 24000 in
/-- A projective stage carrying the canonical residue-prime model passes that
model to its successor. -/
theorem divUniversalHighWindowFibreModel_succ_of_projective
    (hb : 0 < windowBound pi hpi) (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (hmodel : DivUniversalHighWindowFibreModel
      C hpi g r1 r2 b1 b2 i j hO hchi n) :
    DivUniversalHighWindowFibreModel
      C hpi g r1 r2 b1 b2 i j hO hchi (n + 1) := by
  intro p
  exact divUniversalHighWindowFibreImage_succ_of_projective
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j p.asIdeal.ResidueField hO hchi
      (divCarveIdeal_le_ker_of_tower k
        (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi)
        g r1 r2 b1 b2 i j p.asIdeal.ResidueField)
      hb n (hmodel p)

set_option maxHeartbeats 6400000 in
-- Strong induction repeatedly elaborates the projectivity and fibre-model towers together.
set_option synthInstance.maxHeartbeats 1600000 in
-- The two-step case contains both adjacent quotient instances and every residue-field tower.
set_option maxRecDepth 32000 in
/-- Every finite relation stage is projective over the nonreduced carve ring
and has the canonical divisor-window image over every residue field. -/
theorem projective_and_divUniversalHighWindowFibreModel_all
    (hb : 0 < windowBound pi hpi) (n : Nat) :
    Module.Projective RZ Q[n] ∧
      DivUniversalHighWindowFibreModel
        C hpi g r1 r2 b1 b2 i j hO hchi n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          exact ⟨projective_divUniversalHighWindowRelationQuotient_zero
              (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j,
            divUniversalHighWindowFibreModel_zero
              C hpi g r1 r2 b1 b2 i j hO hchi⟩
      | succ n =>
          cases n with
          | zero =>
              exact ⟨projective_divUniversalHighWindowRelationQuotient_one
                  (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb,
                divUniversalHighWindowFibreModel_one
                  C hpi g r1 r2 b1 b2 i j hO hchi hb⟩
          | succ n =>
              have hn := ih n (by omega)
              have hnNext := ih (n + 1) (by omega)
              letI : Module.Projective RZ Q[n] := hn.1
              letI : Module.Projective RZ Q[n + 1] := hnNext.1
              exact
                ⟨projective_divUniversalHighWindowRelationQuotient_succ_succ_of_fibreModels
                    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi
                      hb n hn.2 hnNext.2,
                  divUniversalHighWindowFibreModel_succ_of_projective
                    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi
                      hb (n + 1) hnNext.2⟩

include hO hchi in
/-- Every finite relation quotient is projective over the carve ring. -/
theorem projective_divUniversalHighWindowRelationQuotient_all
    (hb : 0 < windowBound pi hpi) (n : Nat) :
    Module.Projective RZ Q[n] :=
  (projective_and_divUniversalHighWindowFibreModel_all
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb n).1

/-- Every finite relation stage has the canonical divisor-window model on all
residue fields. -/
theorem divUniversalHighWindowFibreModel_all
    (hb : 0 < windowBound pi hpi) (n : Nat) :
    DivUniversalHighWindowFibreModel
      C hpi g r1 r2 b1 b2 i j hO hchi n :=
  (projective_and_divUniversalHighWindowFibreModel_all
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb n).2

set_option maxHeartbeats 1600000 in
-- Synthesizing flatness unfolds the complete dependent relation quotient.
set_option synthInstance.maxHeartbeats 400000 in
-- Projectivity is supplied by the simultaneous all-stage induction above.
include hO hchi in
/-- Every finite relation quotient is flat over the possibly nonreduced carve
ring. -/
theorem flat_divUniversalHighWindowRelationQuotient_all
    (hb : 0 < windowBound pi hpi) (n : Nat) :
    Module.Flat RZ Q[n] := by
  letI := projective_divUniversalHighWindowRelationQuotient_all
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb n
  exact Module.Flat.of_projective

/-! ## Decoupled global induction -/

variable {gamma : Nat} (hgamma : gamma ≤ g)
  (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))

set_option maxHeartbeats 4800000 in
-- Every residue field reconstructs the carve-chart tower and successor square.
set_option synthInstance.maxHeartbeats 1200000 in
set_option maxRecDepth 24000 in
/-- A projective stage carrying the off-diagonal residue-prime model passes
that model to its successor. -/
theorem divUniversalHighWindowFibreModel_succ_of_projective_at
    (n : Nat) [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (hmodel : DivUniversalHighWindowFibreModel_at
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma n) :
    DivUniversalHighWindowFibreModel_at
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma (n + 1) := by
  intro p
  exact divUniversalHighWindowFibreImage_succ_of_projective_at
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j p.asIdeal.ResidueField
      (divCarveIdeal_le_ker_of_tower k
        (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi)
        g r1 r2 b1 b2 i j p.asIdeal.ResidueField)
      hgamma hchiGamma n (hmodel p)

set_option maxHeartbeats 6400000 in
-- Strong induction elaborates the projectivity and fibre-model towers together.
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxRecDepth 32000 in
/-- Every finite relation stage is projective and has the canonical
off-diagonal divisor-window image over every residue field. -/
theorem projective_and_divUniversalHighWindowFibreModel_all_at (n : Nat) :
    Module.Projective RZ Q[n] ∧
      DivUniversalHighWindowFibreModel_at
        C hpi g r1 r2 b1 b2 i j hgamma hchiGamma n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          exact ⟨projective_divUniversalHighWindowRelationQuotient_zero
              (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j,
            divUniversalHighWindowFibreModel_zero_at
              C hpi g r1 r2 b1 b2 i j hgamma hchiGamma⟩
      | succ n =>
          cases n with
          | zero =>
              exact ⟨projective_divUniversalHighWindowRelationQuotient_one_at
                  (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchiGamma,
                divUniversalHighWindowFibreModel_one_at
                  C hpi g r1 r2 b1 b2 i j hgamma hchiGamma⟩
          | succ n =>
              have hn := ih n (by omega)
              have hnNext := ih (n + 1) (by omega)
              letI : Module.Projective RZ Q[n] := hn.1
              letI : Module.Projective RZ Q[n + 1] := hnNext.1
              exact
                ⟨projective_divUniversalHighWindowRelationQuotient_succ_succ_of_fibreModels_at
                    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j
                      hgamma hchiGamma n hn.2 hnNext.2,
                  divUniversalHighWindowFibreModel_succ_of_projective_at
                    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j
                      hgamma hchiGamma (n + 1) hnNext.2⟩

include hgamma hchiGamma in
/-- Every finite relation quotient is projective at independent curve
parameter `gamma ≤ g`. -/
theorem projective_divUniversalHighWindowRelationQuotient_all_at (n : Nat) :
    Module.Projective RZ Q[n] :=
  (projective_and_divUniversalHighWindowFibreModel_all_at
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchiGamma n).1

/-- Every finite relation stage has the canonical off-diagonal divisor-window
model on all residue fields. -/
theorem divUniversalHighWindowFibreModel_all_at (n : Nat) :
    DivUniversalHighWindowFibreModel_at
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma n :=
  (projective_and_divUniversalHighWindowFibreModel_all_at
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchiGamma n).2

set_option maxHeartbeats 1600000 in
-- Synthesizing flatness unfolds the complete dependent relation quotient.
set_option synthInstance.maxHeartbeats 400000 in
include hgamma hchiGamma in
/-- Every finite relation quotient is flat at independent curve parameter
`gamma ≤ g`. -/
theorem flat_divUniversalHighWindowRelationQuotient_all_at (n : Nat) :
    Module.Flat RZ Q[n] := by
  letI := projective_divUniversalHighWindowRelationQuotient_all_at
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchiGamma n
  exact Module.Flat.of_projective

end HighWindowFibreModelGlobalInduction

end AlgebraicGeometry
