/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartClassUnivAffWindows

/-! # Basis transport for the second universal divisor window -/

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

section BasisTransport

variable {k V V' : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']

/-- Transporting a basis backwards and then returning along the same equivalence cancels. -/
theorem basisMap_symm_equivFun_symm_trans (n : Nat)
    (b : Module.Basis (Fin n) k V') (e : V ≃ₗ[k] V') :
    (b.map e.symm).equivFun.symm.trans e = b.equivFun.symm := by
  rw [Module.Basis.map_equivFun]
  ext x
  simp

end BasisTransport

section UniversalAffSndBasis

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftDivRepChartClassUnivAffSndBasis :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (.of k))
variable (g r2 : Nat)
variable (b2 : Module.Basis (Fin r2) k
  ↥(divisorSections k
    ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤))

/-- The seed and classifier use the same reindexing of the shifted divisor window. -/
theorem seedWindowShiftEquiv_eq_windowShiftEquiv :
    seedWindowShiftEquiv C pi hpi g = windowShiftEquiv hpi g := by
  apply LinearEquiv.ext
  intro x
  rfl

set_option maxHeartbeats 1200000 in
-- The large window types make rewriting the named equivalence equality expensive.
/-- The shifted basis used by the carve chart cancels the seed's window-shift equivalence. -/
theorem mappedWindowShiftBasis_symm_trans_seedWindowShiftEquiv :
    (b2.map (windowShiftEquiv hpi g).symm).equivFun.symm.trans
        (seedWindowShiftEquiv C pi hpi g) =
      b2.equivFun.symm := by
  rw [seedWindowShiftEquiv_eq_windowShiftEquiv C hpi g]
  exact basisMap_symm_equivFun_symm_trans r2 b2 (windowShiftEquiv hpi g)

end UniversalAffSndBasis

end PointwiseAchiever

end AlgebraicGeometry
