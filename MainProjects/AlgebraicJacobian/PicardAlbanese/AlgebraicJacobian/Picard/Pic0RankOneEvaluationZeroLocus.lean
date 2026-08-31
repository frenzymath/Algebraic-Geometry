/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneNativePresentation

/-!
# The rank-one evaluation zero-locus comparison

The canonical inverse is cut out by the evaluation counit, while the existing divisor engine
consumes the tied cocycle datum's local equations.  This file proves the section-level comparison
between those two descriptions before any Noetherian or regularity hypothesis is introduced.

For a tied local presentation, transporting a datum section through `module_iso.inv` commutes
with restriction to every open.  Since every component of the sheaf isomorphism is injective,
restriction vanishes on the module side exactly when it vanishes on the datum side.  Applying
this to the canonical unit-lift through the evaluation counit identifies its restriction-
vanishing predicate with that of `datumSection`.  The final theorem specializes the comparison
to `PicRankOneNativePresentation`, whose converted module is definitionally the native module.

The second half passes to the canonical `O_X`-linear piece trivializations of the native module.
It proves that the evaluated section has coordinate `datum.component` on every cocycle piece, and
hence that the two principal local ideals agree.  This closes the local equation comparison, but
does not yet glue those ideals into a base-change-compatible family-level evaluation divisor.  The
file also does not assert regularity or manufacture the still-missing arbitrary-affine presentation
producer.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite MonoidalCategory
  CartesianMonoidalCategory

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {A : Type u} [CommRing A] [Algebra k A]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}

namespace BasicOpenCocycleDatum

variable {B : Type u} [CommRing B] [Algebra k B]

/-- The coordinate of a native global section on one cocycle piece.

This is obtained by restricting the section to `D.pieces j` and applying the canonical
`O_X`-linear trivialization of the native module there. -/
noncomputable def nativePieceCoordinate
    (D : BasicOpenCocycleDatum C B pi)
    (s : Γ(D.nativeModule, (⊤ : (relCurve C B).Opens)))
    (j : D.index) : Γ(relCurve C B, D.pieces j) :=
  gluedTriv B D.isGluingCocycle j le_rfl
    (gluedRes B D.pieces D.unit
      (le_top : D.pieces j ≤ (⊤ : (relCurve C B).Opens)) s)

/-- The native coordinate is the datum component of the same global section. -/
theorem nativePieceCoordinate_eq_component
    (D : BasicOpenCocycleDatum C B pi)
    (s : Γ(D.nativeModule, (⊤ : (relCurve C B).Opens)))
    (j : D.index) :
    D.nativePieceCoordinate s j = D.component s j := by
  rw [nativePieceCoordinate, gluedTriv_apply, gluedRes_coe]
  simp only [Scheme.resHom_resHom, component]

/-- Native piece coordinates commute with arbitrary affine coefficient extension. -/
theorem nativePieceCoordinate_sectionsMapTop
    (D : BasicOpenCocycleDatum C B pi)
    (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B']
    [IsScalarTower k B B']
    (s : Γ(D.nativeModule, (⊤ : (relCurve C B).Opens)))
    (j : D.index) :
    (D.baseChange B').nativePieceCoordinate (D.sectionsMapTop B' s) j =
      D.toBasicOpenCoverData.piecesMap B' j (D.nativePieceCoordinate s j) := by
  rw [(D.baseChange B').nativePieceCoordinate_eq_component,
    D.component_sectionsMapTop B' s, D.nativePieceCoordinate_eq_component]

/-- The principal native-coordinate ideal is preserved by arbitrary affine coefficient
extension. This is the ideal-level consumer of `nativePieceCoordinate_sectionsMapTop`. -/
theorem nativePieceIdeal_sectionsMapTop
    (D : BasicOpenCocycleDatum C B pi)
    (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B']
    [IsScalarTower k B B']
    (s : Γ(D.nativeModule, (⊤ : (relCurve C B).Opens)))
    (j : D.index) :
    Ideal.map (D.toBasicOpenCoverData.piecesMap B' j)
        (Ideal.span {D.nativePieceCoordinate s j}) =
      Ideal.span {
        (D.baseChange B').nativePieceCoordinate (D.sectionsMapTop B' s) j} := by
  rw [Ideal.map_span, Set.image_singleton, D.nativePieceCoordinate_sectionsMapTop]
  rfl

/-- The inverse of the native base-ring section equivalence is the identity on underlying
sections. -/
@[simp]
theorem nativeModuleKSectionsEquiv_symm_apply
    (D : BasicOpenCocycleDatum C B pi)
    (U : (relCurve C B).Opens) (s : D.sheaf.obj.obj (op U)) :
    (D.nativeModuleKSectionsEquiv U).symm s = s := by
  apply (D.nativeModuleKSectionsEquiv U).injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The inverse component of the native base-ring sheaf isomorphism is the identity on
underlying sections. -/
@[simp]
theorem nativeModuleKSheafIso_inv_app
    (D : BasicOpenCocycleDatum C B pi)
    (U : (relCurve C B).Opens) (s : D.sheaf.obj.obj (op U)) :
    (D.nativeModuleKSheafIso.inv.hom.app (op U)).hom s = s := by
  change (D.nativeModuleKSectionsEquiv U).symm s = s
  exact D.nativeModuleKSectionsEquiv_symm_apply U s

end BasicOpenCocycleDatum

namespace PicRankOneLocalPresentation

/-- Transport through the tied sheaf isomorphism commutes with restriction on sections. -/
theorem module_iso_inv_restrict
    (P : PicRankOneLocalPresentation pi lam)
    {U V : (relCurve C P.cover.Carrier).Opens} (h : V ≤ U)
    (s : P.datum.sheaf.obj.obj (op U)) :
    (((Scheme.toModuleKSheafOfModules
      (Over.mk (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)))
        P.module).obj.map (homOfLE h).op).hom
      ((P.module_iso.inv.hom.app (op U)).hom s)) =
      (P.module_iso.inv.hom.app (op V)).hom
        ((P.datum.sheaf.obj.map (homOfLE h).op).hom s) := by
  exact congrArg (fun z => z.hom s)
    (P.module_iso.inv.hom.naturality (homOfLE h).op).symm

/-- Restriction vanishes after transport to the base-ring module exactly when the datum restriction
vanishes.  This is a pointwise section comparison supplied by `module_iso`; it is not a statement
about the native `O_X`-module ideal and needs no Noetherian hypothesis. -/
theorem module_iso_inv_restrict_eq_zero_iff
    (P : PicRankOneLocalPresentation pi lam)
    {U V : (relCurve C P.cover.Carrier).Opens} (h : V ≤ U)
    (s : P.datum.sheaf.obj.obj (op U)) :
    (((Scheme.toModuleKSheafOfModules
      (Over.mk (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)))
        P.module).obj.map (homOfLE h).op).hom
      ((P.module_iso.inv.hom.app (op U)).hom s) = 0) ↔
      ((P.datum.sheaf.obj.map (homOfLE h).op).hom s = 0) := by
  rw [P.module_iso_inv_restrict h s]
  exact map_eq_zero_iff _
    (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (P.module_iso.inv.hom.app (op V))).1

/-- The evaluation counit sends the canonical H⁰ unit-lift to the module section obtained
from the tied datum class. -/
theorem evaluation_evaluationLiftOfH0_eq_moduleSectionsEquiv
    (P : PicRankOneLocalPresentation pi lam)
    (y : Sheaf.HModule P.datum.sheaf 0) :
    (Scheme.Modules.Hom.app P.evaluation
      ((relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) ⁻¹ᵁ
        (⊤ : (Spec (.of P.cover.Carrier)).Opens))).hom
      (P.evaluationLiftOfH0 y) = P.moduleSectionsEquiv y := by
  calc
    _ = P.pushforwardSectionOfH0 y := P.evaluation_evaluationLiftOfH0 y
    _ = P.moduleSectionsEquiv y := rfl

/-- The canonical evaluation section and the tied datum section have the same restriction-
vanishing predicate on every open of the relative curve.

This is the immediate consumer of `module_iso_inv_restrict_eq_zero_iff`: the evaluated section
is first identified with `moduleSectionsEquiv y`, then with the inverse image of
`datumSection y` under the presentation's sheaf isomorphism. -/
theorem evaluationLift_restrict_eq_zero_iff
    (P : PicRankOneLocalPresentation pi lam)
    {V : (relCurve C P.cover.Carrier).Opens} (h : V ≤ ⊤)
    (y : Sheaf.HModule P.datum.sheaf 0) :
    (((Scheme.toModuleKSheafOfModules
      (Over.mk (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)))
        P.module).obj.map (homOfLE h).op).hom
      ((Scheme.Modules.Hom.app P.evaluation
        ((relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) ⁻¹ᵁ
          (⊤ : (Spec (.of P.cover.Carrier)).Opens))).hom
        (P.evaluationLiftOfH0 y)) = 0) ↔
      ((P.datum.sheaf.obj.map (homOfLE h).op).hom
        (P.datumSection y) = 0) := by
  rw [P.evaluation_evaluationLiftOfH0_eq_moduleSectionsEquiv y]
  rw [← P.module_iso_inv_datumSection y]
  exact P.module_iso_inv_restrict_eq_zero_iff h (P.datumSection y)

end PicRankOneLocalPresentation

namespace PicRankOneNativePresentation

/-- Native specialization of the evaluation/datum zero-locus comparison.

`toLocalPresentation.module` is definitionally `P.datum.nativeModule`, so this theorem is the
consumer-facing native base-ring section comparison rather than a second choice of line bundle.
The native `O_X`-linear ideal comparison remains a separate producer obligation. -/
theorem evaluationLift_restrict_eq_zero_iff
    (P : PicRankOneNativePresentation pi lam)
    {V : (relCurve C P.toLocalPresentation.cover.Carrier).Opens} (h : V ≤ ⊤)
    (y : Sheaf.HModule P.toLocalPresentation.datum.sheaf 0) :
    (((Scheme.toModuleKSheafOfModules
      (Over.mk (relCurve C P.toLocalPresentation.cover.Carrier ↘
        Spec (.of P.toLocalPresentation.cover.Carrier)))
        P.toLocalPresentation.module).obj.map (homOfLE h).op).hom
      ((Scheme.Modules.Hom.app P.toLocalPresentation.evaluation
        ((relCurve C P.toLocalPresentation.cover.Carrier ↘
          Spec (.of P.toLocalPresentation.cover.Carrier)) ⁻¹ᵁ
          (⊤ : (Spec (.of P.toLocalPresentation.cover.Carrier)).Opens))).hom
        (P.toLocalPresentation.evaluationLiftOfH0 y)) = 0) ↔
      ((P.toLocalPresentation.datum.sheaf.obj.map (homOfLE h).op).hom
        (P.toLocalPresentation.datumSection y) = 0) := by
  exact P.toLocalPresentation.evaluationLift_restrict_eq_zero_iff h y

/-- Under the native trivialization, the section attached to a datum `H⁰` class has the datum's
component as its coordinate on every cocycle piece. -/
theorem moduleSectionsEquiv_nativePieceCoordinate_eq_component
    (P : PicRankOneNativePresentation pi lam)
    (y : Sheaf.HModule P.toLocalPresentation.datum.sheaf 0)
    (j : P.datum.index) :
    P.datum.nativePieceCoordinate (P.toLocalPresentation.moduleSectionsEquiv y) j =
      P.datum.component (P.toLocalPresentation.datumSection y) j := by
  rw [← P.toLocalPresentation.module_iso_inv_datumSection y]
  change P.datum.nativePieceCoordinate
      ((P.datum.nativeModuleKSheafIso.inv.hom.app
        (op (⊤ : (relCurve C P.cover.Carrier).Opens))).hom
          (P.toLocalPresentation.datumSection y)) j = _
  rw [P.datum.nativeModuleKSheafIso_inv_app]
  exact P.datum.nativePieceCoordinate_eq_component _ j

/-- The canonical evaluation counit section has `datum.component` as its coordinate under the
native `O_X`-linear trivialization on every cocycle piece. -/
theorem evaluationLift_nativePieceCoordinate_eq_component
    (P : PicRankOneNativePresentation pi lam)
    (y : Sheaf.HModule P.toLocalPresentation.datum.sheaf 0)
    (j : P.datum.index) :
    P.datum.nativePieceCoordinate
        ((Scheme.Modules.Hom.app P.toLocalPresentation.evaluation
          ((relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) ⁻¹ᵁ
            (⊤ : (Spec (.of P.cover.Carrier)).Opens))).hom
          (P.toLocalPresentation.evaluationLiftOfH0 y)) j =
      P.datum.component (P.toLocalPresentation.datumSection y) j := by
  -- `erw` bridges the defeq `P.cover` vs `P.toLocalPresentation.cover` projection gap
  erw [P.toLocalPresentation.evaluation_evaluationLiftOfH0_eq_moduleSectionsEquiv y]
  exact P.moduleSectionsEquiv_nativePieceCoordinate_eq_component y j

/-- The principal ideal cut out by the native evaluation section on a cocycle piece is exactly
the principal ideal generated by the datum component consumed by the divisor engine. -/
theorem evaluationLift_nativePieceIdeal_eq_componentIdeal
    (P : PicRankOneNativePresentation pi lam)
    (y : Sheaf.HModule P.toLocalPresentation.datum.sheaf 0)
    (j : P.datum.index) :
    Ideal.span {P.datum.nativePieceCoordinate
        ((Scheme.Modules.Hom.app P.toLocalPresentation.evaluation
          ((relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) ⁻¹ᵁ
            (⊤ : (Spec (.of P.cover.Carrier)).Opens))).hom
          (P.toLocalPresentation.evaluationLiftOfH0 y)) j} =
      Ideal.span {P.datum.component (P.toLocalPresentation.datumSection y) j} := by
  rw [P.evaluationLift_nativePieceCoordinate_eq_component y j]

end PicRankOneNativePresentation

end AlgebraicGeometry
