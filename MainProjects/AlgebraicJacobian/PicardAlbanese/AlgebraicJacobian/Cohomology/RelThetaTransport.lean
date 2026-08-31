/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RelThetaTwist
import AlgebraicJacobian.Picard.UniversalSections

/-!
# DD-4 base-field-transport sub-brick — the relative theta twist collapses to the field level

The M–L infrastructure gap of `informal` inbox item I-0175: the relative theta twist sheaf
`relThetaTwistSheaf C k π n` lives on the **relative curve** `relCurve C k = (C ⊗ overSpec k
k).left`, while the Task-1 field package (`thetaTwistH0Equiv`,
`subsingleton_hModule_thetaTwistSheaf_one_iff`) lives on `C.left`.  These are different
schemes, isomorphic via the terminal-like `overSpec k k` (the first projection is an iso,
`isIso_fst_left_overSpec_self`).  This file transports the whole theta package across that
iso.

Everything runs through the two-lattice pairs of both sheaves (`RigidEngine4Assembly`): the
relative pair `relTwistPair C k π (relThetaCocycle C k π n)` and the field pair
`thetaFieldPairData π n` of `thetaTwistSheaf π n`.  Their carriers are the twisted section
modules on the pinned charts, which are identified across the collapse iso by the section
pullback `relPullbackSection C k` (an isomorphism at test ring `k`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule

section SchemeIso

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

/-- **(a) The base-field collapse isomorphism** `relCurve C k ≅ C.left`: the first
projection of `C ⊗ overSpec k k`, an isomorphism because `overSpec k k` is terminal-like
(`isIso_fst_left_overSpec_self`, the pullback of the iso `Spec k ⟶ Spec k`).  Under it the
pinned relative cover of `relCurve C k` is the pinned field-level cover of `C.left`, and the
relative theta cocycle corresponds to `thetaUnit π ^ n`. -/
noncomputable def relCurveSelfIso : relCurve C k ≅ C.left :=
  asIso (fst C (overSpec k k)).left

@[simp]
lemma relCurveSelfIso_hom : (relCurveSelfIso C).hom = (fst C (overSpec k k)).left := rfl

end SchemeIso

/-! ## The field-level two-lattice pair of `thetaTwistSheaf π n` -/

section FieldPair

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (π : C.left ⟶ P1 k) [IsFinite π] (n : ℕ)

attribute [local instance] Over.sectionsAlgebra

/-- The canonical `k`-scheme structure on `C.left` through the bundle morphism `C.hom`,
matching the one used by the section base change `relSectionsBaseChange`. -/
noncomputable local instance instOverCleft : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

/-- The twist sheaf `𝒪(Θⁿ)` is quasi-coherently packaged on the first pinned chart. -/
noncomputable local instance instQcohThetaField₀ :
    Scheme.QcohOn (thetaTwistSheaf π n) (fiberChart₀ π) :=
  twistSheaf.instQcohOn₀ k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)

/-- The twist sheaf `𝒪(Θⁿ)` is quasi-coherently packaged on the second pinned chart. -/
noncomputable local instance instQcohThetaField₁ :
    Scheme.QcohOn (thetaTwistSheaf π n) (fiberChart₁ π) :=
  twistSheaf.instQcohOn₁ k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)

/-- **The field-level two-cover pair data of `𝒪(Θⁿ) = thetaTwistSheaf π n`**: the
two-lattice pair on the pinned field-level cover `fiberChart₀/₁ π`, with chart coordinates
`t₀ = fiberCoord π`, `t₁ = fiberCoord₁ π` and cocycle `thetaUnit π ^ n` — the field-level
mirror of `relTwistPairData C R π`. -/
noncomputable def thetaFieldPairData :
    Scheme.TwoCoverPairData (thetaTwistSheaf π n) (fiberChart₀ π) (fiberChart₁ π) :=
  twistPairData k (thetaUnit π ^ n)
    (fiberCoord π) (fiberCoord₁ π)
    (preimage_inf_eq_basicOpen_fiberCoord π)
    (preimage_inf_eq_basicOpen_fiberCoord₁ π)
    (fiberCoord_mul_fiberCoord₁_res π)

/-- The field-level two-lattice pair of `thetaTwistSheaf π n`. -/
noncomputable abbrev thetaFieldPair :=
  (thetaFieldPairData C π n).pair
    (isAffineOpen_preimage_chartOpen π 0) (isAffineOpen_preimage_chartOpen π 1)

/-- **`H⁰(𝒪(Θⁿ)) ≃ₗ[k] H⁰` of the field pair.** -/
noncomputable def thetaFieldH0PairEquiv :
    Sheaf.HModule (thetaTwistSheaf π n) 0 ≃ₗ[k] ↥(thetaFieldPair C π n).H0 :=
  (thetaFieldPairData C π n).h0Equiv
    (isAffineOpen_preimage_chartOpen π 0) (isAffineOpen_preimage_chartOpen π 1)
    (preimage_chartOpen_sup π)

/-- **`H¹(𝒪(Θⁿ)) ≃ₗ[k] H¹` of the field pair.** -/
noncomputable def thetaFieldH1PairEquiv :
    Sheaf.HModule (thetaTwistSheaf π n) 1 ≃ₗ[k] (thetaFieldPair C π n).H1 :=
  (thetaFieldPairData C π n).h1Equiv
    (isAffineOpen_preimage_chartOpen π 0) (isAffineOpen_preimage_chartOpen π 1)
    (preimage_chartOpen_sup π)

end FieldPair

/-! ## The relative two-lattice pair at test ring `k` -/

section RelPair

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (π : C.left ⟶ P1 k) [IsFinite π] (n : ℕ)

/-- **`H⁰(relThetaTwistSheaf C k π n) ≃ₗ[k] H⁰` of the relative pair.** -/
noncomputable def relThetaH0PairEquiv :
    Sheaf.HModule (relThetaTwistSheaf C k π n) 0 ≃ₗ[k]
      ↥(relTwistPair C k π (relThetaCocycle C k π n)).H0 :=
  (relTwistPairData C k π (relThetaCocycle C k π n)).h0Equiv
    (relCover_isAffineOpen₀ C k (fiberTwoCover π))
    (relCover_isAffineOpen₁ C k (fiberTwoCover π))
    (relCover_sup C k (fiberTwoCover π))

/-- **`H¹(relThetaTwistSheaf C k π n) ≃ₗ[k] H¹` of the relative pair.** -/
noncomputable def relThetaH1PairEquiv :
    Sheaf.HModule (relThetaTwistSheaf C k π n) 1 ≃ₗ[k]
      (relTwistPair C k π (relThetaCocycle C k π n)).H1 :=
  (relTwistPairData C k π (relThetaCocycle C k π n)).h1Equiv
    (relCover_isAffineOpen₀ C k (fiberTwoCover π))
    (relCover_isAffineOpen₁ C k (fiberTwoCover π))
    (relCover_sup C k (fiberTwoCover π))

end RelPair

end AlgebraicGeometry
