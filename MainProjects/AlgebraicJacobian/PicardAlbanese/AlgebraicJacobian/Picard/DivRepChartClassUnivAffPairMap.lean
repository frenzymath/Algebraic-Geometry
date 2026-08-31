/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartClassUnivAffFstCoord
import AlgebraicJacobian.Picard.DivRepChartClassUnivAffSndCoord
import AlgebraicJacobian.Picard.DivRepClassifyZarAffSurj

/-! # Recovering the universal divisor chart map from its two windows -/

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

section UniversalAffPairMap

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftDivRepChartClassUnivAffPairMap :
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

local notation "b2c" => b2.map (windowShiftEquiv hpi g).symm
local notation "ChartRing" => fun i j =>
  DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2c i j
local notation "ChartMap" => fun i j =>
  divCarveChartToDivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2c i j

set_option maxHeartbeats 1200000 in
-- The framed submodule equalities cross both compiled Grassmannian coordinates.
set_option synthInstance.maxHeartbeats 800000 in
/-- Equality of the two intrinsic epsilon windows with the mapped universal windows identifies
the induced pair-chart morphism with any framed pair-chart morphism. -/
theorem pairChartMap_eq_of_eps_eq_universal
    (i0 : (glueData k g r1).J) (j0 : (glueData k g r2).J)
    {T : Type u} [CommRing T] [Algebra k T]
    (alpha : ChartRing i0 j0 →ₐ[k] T)
    (G : CertifiedDivisorFamilyAff C T g)
    (i : (glueData k g r1).J) (j : (glueData k g r2).J)
    (w : PairChartRing k g r1 g r2 i j →ₐ[k] T)
    (hw : G.IsPairChartFramed hpi g b1 b2 i j w)
    (heps1 : (G.eps hpi g).1 =
      (Module.Grassmannian.map alpha
        (divUniversalFstWindow C pi hpi g r1 r2 b1 b2c i0 j0)).toSubmodule)
    (heps2 : (G.eps hpi g).2 =
      (Module.Grassmannian.map alpha
        (divUniversalSndWindow C pi hpi g r1 r2 b1 b2c i0 j0)).toSubmodule) :
    Spec.map (CommRingCat.ofHom
        ((alpha.comp (divCarveChartMk k
          (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi)
          g r1 r2 b1 b2c i0 j0)).toRingHom)) ≫
        pairChartMap k g r1 g r2 i0 j0 =
      Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r1 g r2 i j := by
  have hcoord1 :
      congrAmbient b1.equivFun
          (Module.Grassmannian.map alpha
            (divUniversalFstWindow C pi hpi g r1 r2 b1 b2c i0 j0)) =
        Module.Grassmannian.map
          (alpha.comp (divCarveChartMk k
            (windowS_choice pi hpi g • fiberWeilDivisor pi)
            (windowM_choice pi hpi g • fiberWeilDivisor pi)
            g r1 r2 b1 b2c i0 j0))
          (pairTautFst k g r1 r2 i0 j0) :=
    map_divUniversalFstWindow_eq_map_pairTautFst
      (C := C) (pi := pi) (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
      (b1 := b1) (b2 := b2) i0 j0 alpha
  have hcoord2 :
      congrAmbient b2.equivFun
          (Module.Grassmannian.map alpha
            (divUniversalSndWindow C pi hpi g r1 r2 b1 b2c i0 j0)) =
        Module.Grassmannian.map
          (alpha.comp (divCarveChartMk k
            (windowS_choice pi hpi g • fiberWeilDivisor pi)
            (windowM_choice pi hpi g • fiberWeilDivisor pi)
            g r1 r2 b1 b2c i0 j0))
          (pairTautSnd k g r1 r2 i0 j0) :=
    map_divUniversalSndWindow_eq_map_pairTautSnd
      (C := C) (pi := pi) (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
      (b1 := b1) (b2 := b2) i0 j0 alpha
  have hmap1 :
      Module.Grassmannian.map
          (alpha.comp (divCarveChartMk k
            (windowS_choice pi hpi g • fiberWeilDivisor pi)
            (windowM_choice pi hpi g • fiberWeilDivisor pi)
            g r1 r2 b1 b2c i0 j0))
          (pairTautFst k g r1 r2 i0 j0) =
        Module.Grassmannian.map w (pairTautFst k g r1 r2 i j) := by
    apply Module.Grassmannian.ext
    rw [hw.1, heps1, ← congrAmbient_toSubmodule]
    exact congrArg Module.Grassmannian.toSubmodule hcoord1.symm
  have hmap2 :
      Module.Grassmannian.map
          (alpha.comp (divCarveChartMk k
            (windowS_choice pi hpi g • fiberWeilDivisor pi)
            (windowM_choice pi hpi g • fiberWeilDivisor pi)
            g r1 r2 b1 b2c i0 j0))
          (pairTautSnd k g r1 r2 i0 j0) =
        Module.Grassmannian.map w (pairTautSnd k g r1 r2 i j) := by
    apply Module.Grassmannian.ext
    rw [hw.2, heps2, ← congrAmbient_toSubmodule]
    exact congrArg Module.Grassmannian.toSubmodule hcoord2.symm
  have hpair := specMap_pairChartMap_eq_of_map_pairTaut_eq
    k g r1 r2 i0 i j0 j
      (alpha.comp (divCarveChartMk k
        (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi)
        g r1 r2 b1 b2c i0 j0)) w hmap1 hmap2
  exact hpair

set_option maxHeartbeats 400000 in
-- The canonical chart triangle elaborates through the affine-scheme comparison.
set_option synthInstance.maxHeartbeats 800000 in
/-- The explicit-algebra-map comparison specializes to the canonical divisor-chart triangle. -/
theorem divCarveChart_classifies_of_eps_eq_universal
    (i0 : (glueData k g r1).J) (j0 : (glueData k g r2).J)
    {T : Type u} [CommRing T] [Algebra k T]
    [Algebra (ChartRing i0 j0) T] [IsScalarTower k (ChartRing i0 j0) T]
    (G : CertifiedDivisorFamilyAff C T g)
    (i : (glueData k g r1).J) (j : (glueData k g r2).J)
    (w : PairChartRing k g r1 g r2 i j →ₐ[k] T)
    (hw : G.IsPairChartFramed hpi g b1 b2 i j w)
    (heps1 : (G.eps hpi g).1 =
      (Module.Grassmannian.map
        (IsScalarTower.toAlgHom k (ChartRing i0 j0) T)
        (divUniversalFstWindow C pi hpi g r1 r2 b1 b2c i0 j0)).toSubmodule)
    (heps2 : (G.eps hpi g).2 =
      (Module.Grassmannian.map
        (IsScalarTower.toAlgHom k (ChartRing i0 j0) T)
        (divUniversalSndWindow C pi hpi g r1 r2 b1 b2c i0 j0)).toSubmodule) :
    Spec.map (CommRingCat.ofHom (algebraMap (ChartRing i0 j0) T)) ≫
        ChartMap i0 j0 ≫
          divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
            (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2c =
      Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r1 g r2 i j := by
  have hpair := pairChartMap_eq_of_eps_eq_universal
    (C := C) (pi := pi) (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
    (b1 := b1) (b2 := b2) i0 j0
    (IsScalarTower.toAlgHom k (ChartRing i0 j0) T) G i j w hw heps1 heps2
  rw [divCarveChartToDivScheme_divSchemeι
      (k := k)
      (A := windowS_choice pi hpi g • fiberWeilDivisor pi)
      (B := windowM_choice pi hpi g • fiberWeilDivisor pi)
      (g := g) (r₁ := r1) (r₂ := r2) (b₁ := b1) (b₂ := b2c) i0 j0,
    ← Category.assoc, ← Spec.map_comp]
  exact hpair

end UniversalAffPairMap

end PointwiseAchiever

end AlgebraicGeometry
