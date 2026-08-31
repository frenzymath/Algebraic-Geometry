/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartClassUnivAffWindows
import AlgebraicJacobian.Picard.DivRepClassifyZarAffSurj

/-! # The second universal widened window at an arbitrary classifier test -/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 16000

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

open Grassmannian Scheme ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

namespace PointwiseAchiever

section UniversalAffSnd

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftDivRepChartClassUnivAffSnd :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(divisorSections k
    ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤))
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))

local notation "b2c" => b2.map (windowShiftEquiv hpi g).symm
local notation "ChartRing" => fun i j =>
  DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2c i j

set_option maxHeartbeats 4000000 in
-- The quotient equality is extracted before the second compiled window comparison is applied.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
/-- The classifier hypothesis identifies the second intrinsic epsilon window with the mapped
second universal window. -/
theorem universalSndEps_eq_map
    (i0 : (glueData k g r1).J) (j0 : (glueData k g r2).J)
    (hb : 0 < windowBound pi hpi)
    {T : Type u} [CommRing T] [Algebra k T]
    [Algebra (ChartRing i0 j0) T] [IsScalarTower k (ChartRing i0 j0) T]
    (G : CertifiedDivisorFamilyAff C T g)
    (hG : G.toZarAff = DivFamZarAff.mapAlg T g
      (divFamZarAffUniv C hpi g r1 r2 b1 b2c i0 j0 hO hchi hb)) :
    (G.eps hpi g).2 =
      (Module.Grassmannian.map (IsScalarTower.toAlgHom k (ChartRing i0 j0) T)
        (divUniversalSndWindow C pi hpi g r1 r2 b1 b2c i0 j0)).toSubmodule := by
  let alpha : ChartRing i0 j0 →ₐ[k] T :=
    IsScalarTower.toAlgHom k (ChartRing i0 j0) T
  have hGhom : G.toZarAff = DivFamZarAff.mapAlgHom alpha
      (divFamZarAffUniv C hpi g r1 r2 b1 b2c i0 j0 hO hchi hb) :=
    hG.trans (DivFamZarAff.mapAlgHom_eq_mapAlg alpha (fun _ => rfl) _).symm
  letI : Algebra (ChartRing i0 j0) T := alpha.toAlgebra
  haveI : IsScalarTower k (ChartRing i0 j0) T :=
    .of_algebraMap_eq fun a => (alpha.commutes a).symm
  let d := univSystemAff C hpi g r1 r2 b1 b2c i0 j0 hO hchi hb
  let hloc := isLocallyCertifiedAff_univSeed
    C hpi g r1 r2 b1 b2 hO hchi i0 j0 hb
  let hreg := hloc.germ_pullbackEqn_mem_nonZeroDivisors T g
  have hmk : DivFamZarAff.mk G.eqns G.isLocallyCertifiedAff =
      DivFamZarAff.mk (d.pullback (relCurveMap C (ChartRing i0 j0) T) hreg)
        (hloc.pullback T g hreg) := by
    simpa only [CertifiedDivisorFamilyAff.toZarAff, DivFamZarAff.mapAlgHom,
      divFamZarAffUniv_eq_mk, DivFamZarAff.mapAlg_mk] using hGhom
  have hdiv : G.eqns.DivEq
      (d.pullback (relCurveMap C (ChartRing i0 j0) T) hreg) :=
    DivFamZarAff.mk_eq_mk_iff.mp hmk
  have hsnd :
      (divUniversalSndWindow C pi hpi g r1 r2 b1 b2c i0 j0).toSubmodule ≤
        divisorWindow d (relThetaPairH1_windowMS C pi hpi g) := by
    exact divUniversalSndWindow_le_highWindow_divisorWindow
      C hpi g r1 r2 b1 b2c i0 j0 hO hchi hb
  exact universalSndWindow_eq_map
    (C := C) (pi := pi) (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
    (b1 := b1) (b2 := b2) (hO := hO) (hchi := hchi)
    i0 j0 T alpha G d hsnd hreg hdiv

set_option maxHeartbeats 4000000 in
-- The off-diagonal quotient equality is extracted before the second window comparison.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
/-- At independent curve parameter `gamma ≤ g`, the classifier hypothesis identifies the
second intrinsic epsilon window with the mapped second universal window. -/
theorem universalSndEps_eq_map_at
    (i0 : (glueData k g r1).J) (j0 : (glueData k g r2).J)
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int))
    {T : Type u} [CommRing T] [Algebra k T]
    [Algebra (ChartRing i0 j0) T] [IsScalarTower k (ChartRing i0 j0) T]
    (G : CertifiedDivisorFamilyAff C T g)
    (hG : G.toZarAff = DivFamZarAff.mapAlg T g
      (divFamZarAffUniv_at C hpi g r1 r2 b1 b2c i0 j0 hgamma hchiGamma)) :
    (G.eps hpi g).2 =
      (Module.Grassmannian.map (IsScalarTower.toAlgHom k (ChartRing i0 j0) T)
        (divUniversalSndWindow C pi hpi g r1 r2 b1 b2c i0 j0)).toSubmodule := by
  let alpha : ChartRing i0 j0 →ₐ[k] T :=
    IsScalarTower.toAlgHom k (ChartRing i0 j0) T
  have hGhom : G.toZarAff = DivFamZarAff.mapAlgHom alpha
      (divFamZarAffUniv_at
        C hpi g r1 r2 b1 b2c i0 j0 hgamma hchiGamma) :=
    hG.trans (DivFamZarAff.mapAlgHom_eq_mapAlg alpha (fun _ => rfl) _).symm
  letI : Algebra (ChartRing i0 j0) T := alpha.toAlgebra
  haveI : IsScalarTower k (ChartRing i0 j0) T :=
    .of_algebraMap_eq fun a => (alpha.commutes a).symm
  let d := univSystemAff_at C hpi g r1 r2 b1 b2c i0 j0 hgamma hchiGamma
  let hloc := isLocallyCertifiedAff_univSeed_at
    C hpi g r1 r2 b1 b2 i0 j0 hgamma hchiGamma
  let hreg := hloc.germ_pullbackEqn_mem_nonZeroDivisors T g
  have hmk : DivFamZarAff.mk G.eqns G.isLocallyCertifiedAff =
      DivFamZarAff.mk (d.pullback (relCurveMap C (ChartRing i0 j0) T) hreg)
        (hloc.pullback T g hreg) := by
    simpa only [CertifiedDivisorFamilyAff.toZarAff, DivFamZarAff.mapAlgHom,
      divFamZarAffUniv_at_eq_mk, DivFamZarAff.mapAlg_mk] using hGhom
  have hdiv : G.eqns.DivEq
      (d.pullback (relCurveMap C (ChartRing i0 j0) T) hreg) :=
    DivFamZarAff.mk_eq_mk_iff.mp hmk
  have hsnd :
      (divUniversalSndWindow C pi hpi g r1 r2 b1 b2c i0 j0).toSubmodule ≤
        divisorWindow d (relThetaPairH1_windowMS C pi hpi g) := by
    exact divUniversalSndWindow_le_highWindow_divisorWindow_at
      C hpi g r1 r2 b1 b2c i0 j0 hgamma hchiGamma
  exact universalSndWindow_eq_map_at
    (C := C) (pi := pi) (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
    (b1 := b1) (b2 := b2) i0 j0 hgamma hchiGamma T alpha G d hsnd hreg hdiv

end UniversalAffSnd

end PointwiseAchiever

end AlgebraicGeometry
