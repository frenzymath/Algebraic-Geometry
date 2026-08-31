/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowRelations
import AlgebraicJacobian.Picard.SlicingFlatKernel

/-!
# The relative flatness gate for high-window relations

The recursively generated high-window relation modules are finite, but finiteness and
fieldwise persistence do not by themselves make their quotients flat over the possibly
nonreduced carve-chart ring.  This file isolates the exact extra input needed by the
landed flattening criterion: a finite syzygy submodule whose image generates the full
kernel of the multiplication presentation after tensoring with every residue field.

With that input, the successor quotient is flat; over the Noetherian carve-chart ring it
is therefore finite projective.  The first two recursive quotients are already projective
and flat, because the carve equations identify them with the two Grassmannian windows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section HighWindowRelationFlat

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowRelationFlat :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k ((windowS_choice pi hpi g • fiberWeilDivisor pi)
    + (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j

/-- The quotient by the recursively generated relation module at a high window. -/
abbrev divUniversalHighWindowRelationQuotient (n : Nat) : Type u :=
  divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
      (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n ⧸
    divUniversalHighWindowRelation (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n

set_option maxHeartbeats 1600000 in
-- The fully expanded high-window source and fibre kernel exceed the default elaboration budget.
/-- The precise relative persistence condition on a proposed syzygy module for one
successor multiplication presentation. -/
def DivUniversalHighWindowSyzygySpans (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n))
    (L : Submodule RZ
      (DivUniversalHighWindowMulSource (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K)) : Prop :=
  L ≤ LinearMap.ker
      (divUniversalHighWindowMulMap (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K) ∧
    ∀ p : PrimeSpectrum RZ,
      LinearMap.ker
          ((divUniversalHighWindowMulMap (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j n K).rTensor p.asIdeal.ResidueField) ≤
        LinearMap.range (L.subtype.rTensor p.asIdeal.ResidueField)

set_option maxHeartbeats 1600000 in
-- The dependent high-window multiplication presentation exceeds the default elaboration budget.
set_option synthInstance.maxHeartbeats 400000 in
-- Synthesizing finiteness and flatness through the dependent source needs additional search time.
/-- A successor high-window quotient is flat once a finite relative syzygy module
generates the complete kernel on every residue-field fibre. -/
theorem flat_divUniversalHighWindowMulSpanQuotient_of_syzygies (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n))
    [Module.Finite RZ ↥K]
    (L : Submodule RZ
      (DivUniversalHighWindowMulSource (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K))
    (hL : DivUniversalHighWindowSyzygySpans (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K L) :
    Module.Flat RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
          (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) (n + 1) ⧸
        divUniversalHighWindowMulSpan (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n K) := by
  letI := finite_divUniversalHighWindowMulSource
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n K
  letI := finite_divUniversalHighWindowAmbient
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j (n + 1)
  letI := flat_divUniversalHighWindowAmbient
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j (n + 1)
  exact Module.Flat.quotient_range_of_forall_ker_rTensor_residueField_le
    (divUniversalHighWindowMulMap (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K) L hL.1 hL.2

set_option maxHeartbeats 1600000 in
-- The dependent high-window quotient type exceeds the default elaboration budget.
set_option synthInstance.maxHeartbeats 400000 in
-- Projectivity synthesis unfolds the finite-presentation instances for this quotient.
/-- Over the Noetherian carve-chart ring, the flat successor quotient supplied by the
syzygy criterion is finite projective. -/
theorem projective_divUniversalHighWindowMulSpanQuotient_of_syzygies (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n))
    [Module.Finite RZ ↥K]
    (L : Submodule RZ
      (DivUniversalHighWindowMulSource (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K))
    (hL : DivUniversalHighWindowSyzygySpans (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K L) :
    Module.Projective RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
          (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) (n + 1) ⧸
        divUniversalHighWindowMulSpan (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n K) := by
  letI := flat_divUniversalHighWindowMulSpanQuotient_of_syzygies
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n K L hL
  letI : Module.Finite RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
          (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) (n + 1) ⧸
        divUniversalHighWindowMulSpan (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n K) := by
    infer_instance
  letI := Module.finitePresentation_of_finite RZ
    (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) (n + 1) ⧸
      divUniversalHighWindowMulSpan (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K)
  exact Module.Flat.projective_of_finitePresentation

set_option maxHeartbeats 1600000 in
-- Rewriting the recursive high-window stage to its multiplication span is elaboration-heavy.
set_option synthInstance.maxHeartbeats 400000 in
-- The recursive finite-submodule instance requires additional synthesis time.
/-- Recursive form of the syzygy criterion: it proves flatness at stage `n + 2`. -/
theorem flat_divUniversalHighWindowRelationQuotient_succ_succ_of_syzygies (n : Nat)
    (L : Submodule RZ
      (DivUniversalHighWindowMulSource (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1)
          (divUniversalHighWindowRelation (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j (n + 1))))
    (hL : DivUniversalHighWindowSyzygySpans (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (n + 1)
        (divUniversalHighWindowRelation (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j (n + 1)) L) :
    Module.Flat RZ
      (divUniversalHighWindowRelationQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 2)) := by
  change Module.Flat RZ
    ((divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) (n + 2)) ⧸
      divUniversalHighWindowMulSpan (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1)
        (divUniversalHighWindowRelation (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j (n + 1)))
  letI := finite_divUniversalHighWindowRelation
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j (n + 1)
  exact flat_divUniversalHighWindowMulSpanQuotient_of_syzygies
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j (n + 1)
      (divUniversalHighWindowRelation (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1)) L hL

set_option maxHeartbeats 1600000 in
-- Comparing the two expanded stage-zero quotient types exceeds the default budget.
/-- Quotient transport from relation stage zero to the first Grassmannian point. -/
noncomputable def divUniversalHighWindowRelationZeroQuotientEquiv :
    divUniversalHighWindowRelationQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 0 ≃ₗ[RZ]
      divUniversalHighWindowQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 0
        (divUniversalHighWindowStageZero (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j) :=
  Submodule.Quotient.equiv
    (divUniversalHighWindowRelation (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j 0)
    (divUniversalHighWindowStageZero (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j).toSubmodule
    (LinearEquiv.refl RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi)
        (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
        (b1 := b1) (b2 := b2) (i := i) (j := j) 0)) (by
      rw [LinearEquiv.refl_toLinearMap, Submodule.map_id]
      exact divUniversalHighWindowRelation_zero (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j)

set_option maxHeartbeats 1600000 in
-- Comparing the two expanded stage-one quotient types exceeds the default budget.
/-- Quotient transport from relation stage one to the second Grassmannian point. -/
noncomputable def divUniversalHighWindowRelationOneQuotientEquiv
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))
    (hb : 0 < windowBound pi hpi) :
    divUniversalHighWindowRelationQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 1 ≃ₗ[RZ]
      divUniversalHighWindowQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 1
        (divUniversalHighWindowStageOne (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j) :=
  Submodule.Quotient.equiv
    (divUniversalHighWindowRelation (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j 1)
    (divUniversalHighWindowStageOne (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j).toSubmodule
    (LinearEquiv.refl RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi)
        (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
        (b1 := b1) (b2 := b2) (i := i) (j := j) 1)) (by
      rw [LinearEquiv.refl_toLinearMap, Submodule.map_id]
      exact divUniversalHighWindowRelation_one_eq_secondWindow
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb)

set_option maxHeartbeats 1600000 in
-- Comparing the two expanded stage-one quotient types exceeds the default budget.
/-- Quotient transport from relation stage one to the degree-`g` second Grassmannian
point at independent Euler parameter `gamma ≤ g`. -/
noncomputable def divUniversalHighWindowRelationOneQuotientEquiv_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    divUniversalHighWindowRelationQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 1 ≃ₗ[RZ]
      divUniversalHighWindowQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 1
        (divUniversalHighWindowStageOne (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j) :=
  Submodule.Quotient.equiv
    (divUniversalHighWindowRelation (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j 1)
    (divUniversalHighWindowStageOne (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j).toSubmodule
    (LinearEquiv.refl RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi)
        (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
        (b1 := b1) (b2 := b2) (i := i) (j := j) 1)) (by
      rw [LinearEquiv.refl_toLinearMap, Submodule.map_id]
      exact divUniversalHighWindowRelation_one_eq_secondWindow_at
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchi)

set_option maxHeartbeats 1600000 in
-- Elaborating the expanded quotient equivalence exceeds the default budget.
/-- The relation quotient at stage zero is the first Grassmannian quotient. -/
theorem projective_divUniversalHighWindowRelationQuotient_zero :
    Module.Projective RZ
      (divUniversalHighWindowRelationQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 0) := by
  exact Module.Projective.of_equiv
    (divUniversalHighWindowRelationZeroQuotientEquiv
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j).symm

set_option maxHeartbeats 1600000 in
-- Synthesizing flatness through the expanded stage-zero quotient exceeds the default budget.
/-- The relation quotient at stage zero is flat. -/
theorem flat_divUniversalHighWindowRelationQuotient_zero :
    Module.Flat RZ
      (divUniversalHighWindowRelationQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 0) := by
  letI := projective_divUniversalHighWindowRelationQuotient_zero
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j
  exact Module.Flat.of_projective

set_option maxHeartbeats 1600000 in
-- Elaborating the expanded stage-one quotient equivalence exceeds the default budget.
/-- The relation quotient at stage one is the second Grassmannian quotient. -/
theorem projective_divUniversalHighWindowRelationQuotient_one
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))
    (hb : 0 < windowBound pi hpi) :
    Module.Projective RZ
      (divUniversalHighWindowRelationQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 1) := by
  exact Module.Projective.of_equiv
    (divUniversalHighWindowRelationOneQuotientEquiv
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb).symm

set_option maxHeartbeats 1600000 in
-- Elaborating the expanded stage-one quotient equivalence exceeds the default budget.
/-- At independent Euler parameter `gamma ≤ g`, the relation quotient at stage one
is the degree-`g` second Grassmannian quotient. -/
theorem projective_divUniversalHighWindowRelationQuotient_one_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    Module.Projective RZ
      (divUniversalHighWindowRelationQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 1) := by
  exact Module.Projective.of_equiv
    (divUniversalHighWindowRelationOneQuotientEquiv_at
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchi).symm

set_option maxHeartbeats 1600000 in
-- Synthesizing flatness through the expanded stage-one quotient exceeds the default budget.
/-- The relation quotient at stage one is flat. -/
theorem flat_divUniversalHighWindowRelationQuotient_one
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))
    (hb : 0 < windowBound pi hpi) :
    Module.Flat RZ
      (divUniversalHighWindowRelationQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 1) := by
  letI := projective_divUniversalHighWindowRelationQuotient_one
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb
  exact Module.Flat.of_projective

set_option maxHeartbeats 1600000 in
-- Synthesizing flatness through the expanded stage-one quotient exceeds the default budget.
/-- At independent Euler parameter `gamma ≤ g`, the relation quotient at stage one
is flat. -/
theorem flat_divUniversalHighWindowRelationQuotient_one_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    Module.Flat RZ
      (divUniversalHighWindowRelationQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 1) := by
  letI := projective_divUniversalHighWindowRelationQuotient_one_at
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchi
  exact Module.Flat.of_projective

end HighWindowRelationFlat

end AlgebraicGeometry
