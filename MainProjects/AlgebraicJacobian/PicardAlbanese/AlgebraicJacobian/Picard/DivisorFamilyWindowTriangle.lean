/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyWindowBaseChange

/-!
# G-2 (DD-4 Task 7), crux half — THE TRIANGLE of the window identification

Continuation of `AlgebraicJacobian.Picard.DivisorFamilyWindowBaseChange` (the 500-line
cap forced the split): the val-computation of the rigid engine's on-the-nose `H⁰` base
change on pure tensors, and **the G-2 crux triangle** — the window identification
`relThetaWindowEquiv` over `R'` of the `cancelBaseChange`-compared ambient vector is
the `relSectionsMap`-compared window identification over `R`, chart-componentwise
(`resHom_relThetaWindowEquiv_cancelBaseChange_fst/snd`).  Consumed by the two halves of
`divFamEps_mapAlg` (`AlgebraicJacobian.Picard.DivisorFamilyEpsNaturality`).
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## The val-computation of the rigid engine's `H⁰` base change, consumer half -/

section H0BaseChangeVal

open AlgebraicJacobian

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (S : Type u) [CommRing S] [Algebra k S]
variable (π : C.left ⟶ P1 k) [IsFinite π]
variable (g : Γ(relCurve C k, (relCover C k (fiberTwoCover π)).V₀ ⊓
  (relCover C k (fiberTwoCover π)).V₁)ˣ)
variable (hH1 : Subsingleton (relTwistPair C k π g).H1)

set_option maxHeartbeats 2000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
/-- (Implementation) The `H⁰`-carrier value of the base-changed class on `1 ⊗ y`: the
pair of the two term base changes of the chart restrictions of `y`. -/
private lemma h0Equiv_val_relTwistH0BaseChange_one_tmul
    (y : Sheaf.HModule (relTwistSheaf C k (fiberTwoCover π) g) 0) :
    ((relTwistPairData C S π
        (relCocycleBaseChange C k S (fiberTwoCover π) g)).h0Equiv
        (relCover_isAffineOpen₀ C S (fiberTwoCover π))
        (relCover_isAffineOpen₁ C S (fiberTwoCover π))
        (relCover_sup C S (fiberTwoCover π))
        (relTwistH0BaseChange C k S π g hH1 (1 ⊗ₜ y))).val =
      (relTwistTermBaseChange₀ C k S (fiberTwoCover π) g
          (1 ⊗ₜ (((relTwistPairData C k π g).h0Equiv
            (relCover_isAffineOpen₀ C k (fiberTwoCover π))
            (relCover_isAffineOpen₁ C k (fiberTwoCover π))
            (relCover_sup C k (fiberTwoCover π)) y).val.1)),
        relTwistTermBaseChange₁ C k S (fiberTwoCover π) g
          (1 ⊗ₜ (((relTwistPairData C k π g).h0Equiv
            (relCover_isAffineOpen₀ C k (fiberTwoCover π))
            (relCover_isAffineOpen₁ C k (fiberTwoCover π))
            (relCover_sup C k (fiberTwoCover π)) y).val.2))) := by
  -- the abstract clause on the pure tensor: `1 ⊗ (H⁰-carrier of y)`
  have hinner : ((relTwistH0BaseChangeEquiv C k π g hH1 S (1 ⊗ₜ y) :
      LinearMap.ker ((relTwistPair C k π g).diff.baseChange S)) : S ⊗[k] _)
      = 1 ⊗ₜ (((relTwistPairData C k π g).h0Equiv
          (relCover_isAffineOpen₀ C k (fiberTwoCover π))
          (relCover_isAffineOpen₁ C k (fiberTwoCover π))
          (relCover_sup C k (fiberTwoCover π)) y).val) := by
    have h1 : relTwistH0BaseChangeEquiv C k π g hH1 S (1 ⊗ₜ y)
        = RigidEngine.kerBaseChangeEquiv (relTwistPair C k π g).diff S
            ((relTwistPairData C k π g).surjective_diff
              (relCover_isAffineOpen₀ C k (fiberTwoCover π))
              (relCover_isAffineOpen₁ C k (fiberTwoCover π)) hH1)
            (1 ⊗ₜ ((relTwistPairData C k π g).h0Equiv
              (relCover_isAffineOpen₀ C k (fiberTwoCover π))
              (relCover_isAffineOpen₁ C k (fiberTwoCover π))
              (relCover_sup C k (fiberTwoCover π)) y)) := by
      change (relTwistPairData C k π g).h0BaseChangeEquiv
          (relCover_isAffineOpen₀ C k (fiberTwoCover π))
          (relCover_isAffineOpen₁ C k (fiberTwoCover π))
          (relCover_sup C k (fiberTwoCover π)) hH1 S (1 ⊗ₜ y) = _
      rw [Scheme.TwoCoverPairData.h0BaseChangeEquiv, LinearEquiv.trans_apply,
        LinearEquiv.baseChange_tmul]
      rfl
    rw [h1]
    exact kerBaseChangeEquiv_tmul_coe S _ _ 1 _
  refine (congrArg Subtype.val
    (h0Equiv_relTwistH0BaseChange C S π g hH1 (1 ⊗ₜ y))).trans ?_
  refine (RigidEngine.kerCongr_apply_coe _ _ _ _ _ _).trans ?_
  refine (congrArg (relTwistDomBaseChange C k S (fiberTwoCover π) g) hinner).trans ?_
  rw [relTwistDomBaseChange, LinearEquiv.trans_apply, TensorProduct.prodRight_tmul]
  rfl

set_option maxHeartbeats 2000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 800000 in
/-- **The val-computation of the `H⁰` base change, chart 0**: on `1 ⊗ y` the rigid
engine's on-the-nose `H⁰` base change reads, on the first chart, as the sections
comparison `relSectionsMap C k S` of the chart-0 component of `y`. -/
theorem resHom_relTwistH0BaseChange_one_tmul_fst
    (y : Sheaf.HModule (relTwistSheaf C k (fiberTwoCover π) g) 0) :
    (relCurve C S).resHom (le_inf le_top le_rfl)
        ((relTwistSectionsEquiv₀ C S (fiberTwoCover π)
          (relCocycleBaseChange C k S (fiberTwoCover π) g)
          (relTwistH0BaseChange C k S π g hH1 (1 ⊗ₜ y))).val.1)
      = relSectionsMap C k S (fiberTwoCover π).V₀
          ((relCurve C k).resHom (le_inf le_top le_rfl)
            ((relTwistSectionsEquiv₀ C k (fiberTwoCover π) g y).val.1)) := by
  -- the `H⁰`-carrier value, in chart components
  have hval := congrArg Prod.fst (h0Equiv_val_relTwistH0BaseChange_one_tmul C S π g hH1 y)
  rw [Scheme.TwoCoverPairData.h0Equiv_val] at hval
  -- read both sides through the chart-0 trivialization
  have hread := congrArg (twistTriv₀ S (relCover C S (fiberTwoCover π)).V₀
    (relCover C S (fiberTwoCover π)).V₁
    (relCocycleBaseChange C k S (fiberTwoCover π) g)
    (le_refl (relCover C S (fiberTwoCover π)).V₀)) hval
  rw [twistTriv₀_relTwistTermBaseChange₀, one_smul] at hread
  -- the `1 ⊗`-side chart component through the `k`-level carrier value
  have hk := congrArg Prod.fst (Scheme.TwoCoverPairData.h0Equiv_val
    (relTwistPairData C k π g) (relCover_isAffineOpen₀ C k (fiberTwoCover π))
    (relCover_isAffineOpen₁ C k (fiberTwoCover π))
    (relCover_sup C k (fiberTwoCover π)) y)
  rw [hk] at hread
  -- read the chart-0 trivialization of a restricted global section as a restriction
  have hgenS : ∀ x : Sheaf.HModule (relTwistSheaf C S (fiberTwoCover π)
      (relCocycleBaseChange C k S (fiberTwoCover π) g)) 0,
      twistTriv₀ S (relCover C S (fiberTwoCover π)).V₀
        (relCover C S (fiberTwoCover π)).V₁
        (relCocycleBaseChange C k S (fiberTwoCover π) g)
        (le_refl (relCover C S (fiberTwoCover π)).V₀)
        (secRes (relTwistSheaf C S (fiberTwoCover π)
            (relCocycleBaseChange C k S (fiberTwoCover π) g)) le_top
          (Sheaf.HModule.linearEquiv₀
            (Opens.grothendieckTopology ((relCurve C S : Scheme.{u}) : TopCat))
            isTerminalTop _ x))
        = (relCurve C S).resHom (le_inf le_top le_rfl)
            ((relTwistSectionsEquiv₀ C S (fiberTwoCover π)
              (relCocycleBaseChange C k S (fiberTwoCover π) g) x).val.1) := fun x => by
    rw [show secRes (relTwistSheaf C S (fiberTwoCover π)
          (relCocycleBaseChange C k S (fiberTwoCover π) g)) le_top
          (Sheaf.HModule.linearEquiv₀
            (Opens.grothendieckTopology ((relCurve C S : Scheme.{u}) : TopCat))
            isTerminalTop _ x)
        = twistRes S (relCover C S (fiberTwoCover π)).V₀
            (relCover C S (fiberTwoCover π)).V₁
            (relCocycleBaseChange C k S (fiberTwoCover π) g) le_top
            (relTwistSectionsEquiv₀ C S (fiberTwoCover π)
              (relCocycleBaseChange C k S (fiberTwoCover π) g) x) from rfl,
      twistTriv₀_apply, twistRes_coe_fst, Scheme.resHom_resHom]
  have hgenk : ∀ x : Sheaf.HModule (relTwistSheaf C k (fiberTwoCover π) g) 0,
      twistTriv₀ k (relCover C k (fiberTwoCover π)).V₀
        (relCover C k (fiberTwoCover π)).V₁ g
        (le_refl (relCover C k (fiberTwoCover π)).V₀)
        (secRes (relTwistSheaf C k (fiberTwoCover π) g) le_top
          (Sheaf.HModule.linearEquiv₀
            (Opens.grothendieckTopology ((relCurve C k : Scheme.{u}) : TopCat))
            isTerminalTop _ x))
        = (relCurve C k).resHom (le_inf le_top le_rfl)
            ((relTwistSectionsEquiv₀ C k (fiberTwoCover π) g x).val.1) := fun x => by
    rw [show secRes (relTwistSheaf C k (fiberTwoCover π) g) le_top
          (Sheaf.HModule.linearEquiv₀
            (Opens.grothendieckTopology ((relCurve C k : Scheme.{u}) : TopCat))
            isTerminalTop _ x)
        = twistRes k (relCover C k (fiberTwoCover π)).V₀
            (relCover C k (fiberTwoCover π)).V₁ g le_top
            (relTwistSectionsEquiv₀ C k (fiberTwoCover π) g x) from rfl,
      twistTriv₀_apply, twistRes_coe_fst, Scheme.resHom_resHom]
  rw [hgenS, hgenk] at hread
  exact hread

set_option maxHeartbeats 2000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 800000 in
/-- **The val-computation of the `H⁰` base change, chart 1** (mirror of
`resHom_relTwistH0BaseChange_one_tmul_fst`). -/
theorem resHom_relTwistH0BaseChange_one_tmul_snd
    (y : Sheaf.HModule (relTwistSheaf C k (fiberTwoCover π) g) 0) :
    (relCurve C S).resHom (le_inf le_top le_rfl)
        ((relTwistSectionsEquiv₀ C S (fiberTwoCover π)
          (relCocycleBaseChange C k S (fiberTwoCover π) g)
          (relTwistH0BaseChange C k S π g hH1 (1 ⊗ₜ y))).val.2)
      = relSectionsMap C k S (fiberTwoCover π).V₁
          ((relCurve C k).resHom (le_inf le_top le_rfl)
            ((relTwistSectionsEquiv₀ C k (fiberTwoCover π) g y).val.2)) := by
  have hval := congrArg Prod.snd (h0Equiv_val_relTwistH0BaseChange_one_tmul C S π g hH1 y)
  rw [Scheme.TwoCoverPairData.h0Equiv_val] at hval
  have hread := congrArg (twistTriv₁ S (relCover C S (fiberTwoCover π)).V₀
    (relCover C S (fiberTwoCover π)).V₁
    (relCocycleBaseChange C k S (fiberTwoCover π) g)
    (le_refl (relCover C S (fiberTwoCover π)).V₁)) hval
  rw [twistTriv₁_relTwistTermBaseChange₁, one_smul] at hread
  have hk := congrArg Prod.snd (Scheme.TwoCoverPairData.h0Equiv_val
    (relTwistPairData C k π g) (relCover_isAffineOpen₀ C k (fiberTwoCover π))
    (relCover_isAffineOpen₁ C k (fiberTwoCover π))
    (relCover_sup C k (fiberTwoCover π)) y)
  rw [hk] at hread
  have hgenS : ∀ x : Sheaf.HModule (relTwistSheaf C S (fiberTwoCover π)
      (relCocycleBaseChange C k S (fiberTwoCover π) g)) 0,
      twistTriv₁ S (relCover C S (fiberTwoCover π)).V₀
        (relCover C S (fiberTwoCover π)).V₁
        (relCocycleBaseChange C k S (fiberTwoCover π) g)
        (le_refl (relCover C S (fiberTwoCover π)).V₁)
        (secRes (relTwistSheaf C S (fiberTwoCover π)
            (relCocycleBaseChange C k S (fiberTwoCover π) g)) le_top
          (Sheaf.HModule.linearEquiv₀
            (Opens.grothendieckTopology ((relCurve C S : Scheme.{u}) : TopCat))
            isTerminalTop _ x))
        = (relCurve C S).resHom (le_inf le_top le_rfl)
            ((relTwistSectionsEquiv₀ C S (fiberTwoCover π)
              (relCocycleBaseChange C k S (fiberTwoCover π) g) x).val.2) := fun x => by
    rw [show secRes (relTwistSheaf C S (fiberTwoCover π)
          (relCocycleBaseChange C k S (fiberTwoCover π) g)) le_top
          (Sheaf.HModule.linearEquiv₀
            (Opens.grothendieckTopology ((relCurve C S : Scheme.{u}) : TopCat))
            isTerminalTop _ x)
        = twistRes S (relCover C S (fiberTwoCover π)).V₀
            (relCover C S (fiberTwoCover π)).V₁
            (relCocycleBaseChange C k S (fiberTwoCover π) g) le_top
            (relTwistSectionsEquiv₀ C S (fiberTwoCover π)
              (relCocycleBaseChange C k S (fiberTwoCover π) g) x) from rfl,
      twistTriv₁_apply, twistRes_coe_snd, Scheme.resHom_resHom]
  have hgenk : ∀ x : Sheaf.HModule (relTwistSheaf C k (fiberTwoCover π) g) 0,
      twistTriv₁ k (relCover C k (fiberTwoCover π)).V₀
        (relCover C k (fiberTwoCover π)).V₁ g
        (le_refl (relCover C k (fiberTwoCover π)).V₁)
        (secRes (relTwistSheaf C k (fiberTwoCover π) g) le_top
          (Sheaf.HModule.linearEquiv₀
            (Opens.grothendieckTopology ((relCurve C k : Scheme.{u}) : TopCat))
            isTerminalTop _ x))
        = (relCurve C k).resHom (le_inf le_top le_rfl)
            ((relTwistSectionsEquiv₀ C k (fiberTwoCover π) g x).val.2) := fun x => by
    rw [show secRes (relTwistSheaf C k (fiberTwoCover π) g) le_top
          (Sheaf.HModule.linearEquiv₀
            (Opens.grothendieckTopology ((relCurve C k : Scheme.{u}) : TopCat))
            isTerminalTop _ x)
        = twistRes k (relCover C k (fiberTwoCover π)).V₀
            (relCover C k (fiberTwoCover π)).V₁ g le_top
            (relTwistSectionsEquiv₀ C k (fiberTwoCover π) g x) from rfl,
      twistTriv₁_apply, twistRes_coe_snd, Scheme.resHom_resHom]
  rw [hgenS, hgenk] at hread
  exact hread

end H0BaseChangeVal

/-! ## THE TRIANGLE: the window identification commutes with base change -/

section Triangle

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable (π : C.left ⟶ P1 k) [IsFinite π]

noncomputable local instance instOverCleftWBC : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]

variable (a : ℕ)
variable (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 4000 in
/-- (Implementation) The window identification at `1 ⊗ h`, unfolded to the generic
global-sections reading of the base-changed twisted sheaf. -/
private lemma relThetaWindowEquiv_one_tmul (S : Type u) [CommRing S] [Algebra k S]
    (hH1' : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (h : ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) :
    (relThetaWindowEquiv C S π a hH1' (1 ⊗ₜ h)).val
      = (relTwistSectionsEquiv₀ C S (fiberTwoCover π) (relThetaCocycle C S π a)
          (Sheaf.HModule.mapEquiv
            (eqToIso (congrArg (relTwistSheaf C S (fiberTwoCover π))
              (relThetaCocycle_baseChange C S π a))) 0
            (relTwistH0BaseChange C k S π (relThetaCocycle C k π a) hH1'
              (1 ⊗ₜ (((relThetaH0FieldEquiv C π a).trans
                (thetaTwistH0Equiv k π a)).symm h))))).val := by
  congr 1

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 4000 in
/-- (Implementation) The window identification at `1 ⊗ h`, chart 0: the `k → S`
sections comparison of a fixed field-level section, independent of the test ring. -/
private lemma resHom_relThetaWindowEquiv_one_tmul_fst (S : Type u) [CommRing S]
    [Algebra k S] (h : ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) :
    (relCurve C S).resHom (le_inf le_top le_rfl)
        ((relThetaWindowEquiv C S π a hH1 (1 ⊗ₜ h)).val.1)
      = relSectionsMap C k S (fiberTwoCover π).V₀
          ((relCurve C k).resHom (le_inf le_top le_rfl)
            ((relTwistSectionsEquiv₀ C k (fiberTwoCover π) (relThetaCocycle C k π a)
              (((relThetaH0FieldEquiv C π a).trans
                (thetaTwistH0Equiv k π a)).symm h)).val.1)) := by
  rw [congrArg ((relCurve C S).resHom (le_inf le_top le_rfl))
      (congrArg Prod.fst (relThetaWindowEquiv_one_tmul C π a S hH1 h)),
    congrArg ((relCurve C S).resHom (le_inf le_top le_rfl))
      (congrArg Prod.fst (val_relTwistSectionsEquiv₀_mapEquiv C S (fiberTwoCover π)
        (relThetaCocycle_baseChange C S π a) _))]
  exact resHom_relTwistH0BaseChange_one_tmul_fst C S π (relThetaCocycle C k π a) hH1 _

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 4000 in
/-- (Implementation) Chart-1 mirror of `resHom_relThetaWindowEquiv_one_tmul_fst`. -/
private lemma resHom_relThetaWindowEquiv_one_tmul_snd (S : Type u) [CommRing S]
    [Algebra k S] (h : ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) :
    (relCurve C S).resHom (le_inf le_top le_rfl)
        ((relThetaWindowEquiv C S π a hH1 (1 ⊗ₜ h)).val.2)
      = relSectionsMap C k S (fiberTwoCover π).V₁
          ((relCurve C k).resHom (le_inf le_top le_rfl)
            ((relTwistSectionsEquiv₀ C k (fiberTwoCover π) (relThetaCocycle C k π a)
              (((relThetaH0FieldEquiv C π a).trans
                (thetaTwistH0Equiv k π a)).symm h)).val.2)) := by
  rw [congrArg ((relCurve C S).resHom (le_inf le_top le_rfl))
      (congrArg Prod.snd (relThetaWindowEquiv_one_tmul C π a S hH1 h)),
    congrArg ((relCurve C S).resHom (le_inf le_top le_rfl))
      (congrArg Prod.snd (val_relTwistSectionsEquiv₀_mapEquiv C S (fiberTwoCover π)
        (relThetaCocycle_baseChange C S π a) _))]
  exact resHom_relTwistH0BaseChange_one_tmul_snd C S π (relThetaCocycle C k π a) hH1 _

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
/-- **THE TRIANGLE, chart 0** (the G-2 crux, `informal/spec-w4-gates.md` §G-2): the
window identification over `R'` of the `cancelBaseChange`-compared ambient vector is
the `relSectionsMap`-compared window identification over `R`, on the first chart
component.  The recorded orientation seam: the ambient comparison is
`cancelBaseChange k R R' R'` applied to `1 ⊗ₜ x` — the `ker_baseChangeMkQ` normal form
of `Picard/DivCarveKit.lean`. -/
theorem resHom_relThetaWindowEquiv_cancelBaseChange_fst
    (x : R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) :
    (relCurve C R').resHom (le_inf le_top le_rfl)
        ((relThetaWindowEquiv C R' π a hH1
          (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _
            (1 ⊗ₜ x))).val.1)
      = relSectionsMap C R R' (fiberTwoCover π).V₀
          ((relCurve C R).resHom (le_inf le_top le_rfl)
            ((relThetaWindowEquiv C R π a hH1 x).val.1)) := by
  induction x with
  | zero => simp only [TensorProduct.tmul_zero, map_zero, Submodule.coe_zero,
      Prod.fst_zero, map_zero]
  | add x y hx hy =>
    have hL : TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R'
        (↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) (1 ⊗ₜ (x + y))
        = TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _ (1 ⊗ₜ x)
          + TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _ (1 ⊗ₜ y) := by
      rw [TensorProduct.tmul_add, map_add]
    have h2 : (relThetaWindowEquiv C R' π a hH1
          (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _ (1 ⊗ₜ x)
            + TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _
              (1 ⊗ₜ y))).val.1
        = (relThetaWindowEquiv C R' π a hH1
            (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R'
              _ (1 ⊗ₜ x))).val.1
          + (relThetaWindowEquiv C R' π a hH1
              (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R'
                _ (1 ⊗ₜ y))).val.1 := by
      rw [map_add]
      rfl
    have h3 : (relThetaWindowEquiv C R π a hH1 (x + y)).val.1
        = (relThetaWindowEquiv C R π a hH1 x).val.1
          + (relThetaWindowEquiv C R π a hH1 y).val.1 := by
      rw [map_add]
      rfl
    rw [hL, h2, map_add, hx, hy, h3, map_add, map_add]
  | tmul r h =>
    -- the compared pure tensor: `1 ⊗ (r ⊗ h) ↦ algebraMap r • (1 ⊗ h)`
    have hcmp : TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R'
        (↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) (1 ⊗ₜ (r ⊗ₜ h))
        = algebraMap R R' r • ((1 : R') ⊗ₜ h) := by
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
    have hsm : (r ⊗ₜ h : R ⊗[k] ↥(Scheme.divisorSections k
        (a • fiberWeilDivisor π) ⊤)) = r • ((1 : R) ⊗ₜ h) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have e1 : (relThetaWindowEquiv C R' π a hH1
          (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _
            (1 ⊗ₜ (r ⊗ₜ h)))).val.1
        = algebraMap R R' r • (relThetaWindowEquiv C R' π a hH1 (1 ⊗ₜ h)).val.1 := by
      rw [hcmp, map_smul]
      rfl
    have e2 : (relThetaWindowEquiv C R π a hH1 (r ⊗ₜ h)).val.1
        = r • (relThetaWindowEquiv C R π a hH1 (1 ⊗ₜ h)).val.1 := by
      rw [hsm, map_smul]
      rfl
    refine ((congrArg ((relCurve C R').resHom (le_inf le_top le_rfl)) e1).trans
      (resHom_smul_rel' C R' _ _ _)).trans ?_
    refine (congrArg (algebraMap R R' r • ·)
      (resHom_relThetaWindowEquiv_one_tmul_fst C π a hH1 R' h)).trans ?_
    refine ((congrArg (algebraMap R R' r • ·)
      (relSectionsMap_relSectionsMap C R R' (fiberTwoCover π).V₀ _)).symm).trans ?_
    refine ((relSectionsMap_smul C R R' (fiberTwoCover π).V₀ r _).symm).trans ?_
    refine congrArg (relSectionsMap C R R' (fiberTwoCover π).V₀) ?_
    exact (((congrArg ((relCurve C R).resHom (le_inf le_top le_rfl)) e2).trans
      (resHom_smul_rel' C R _ _ _)).trans
      (congrArg (r • ·)
        (resHom_relThetaWindowEquiv_one_tmul_fst C π a hH1 R h))).symm
set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
/-- **THE TRIANGLE, chart 1** (mirror of
`resHom_relThetaWindowEquiv_cancelBaseChange_fst`). -/
theorem resHom_relThetaWindowEquiv_cancelBaseChange_snd
    (x : R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) :
    (relCurve C R').resHom (le_inf le_top le_rfl)
        ((relThetaWindowEquiv C R' π a hH1
          (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _
            (1 ⊗ₜ x))).val.2)
      = relSectionsMap C R R' (fiberTwoCover π).V₁
          ((relCurve C R).resHom (le_inf le_top le_rfl)
            ((relThetaWindowEquiv C R π a hH1 x).val.2)) := by
  induction x with
  | zero => simp only [TensorProduct.tmul_zero, map_zero, Submodule.coe_zero,
      Prod.snd_zero, map_zero]
  | add x y hx hy =>
    have hL : TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R'
        (↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) (1 ⊗ₜ (x + y))
        = TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _ (1 ⊗ₜ x)
          + TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _ (1 ⊗ₜ y) := by
      rw [TensorProduct.tmul_add, map_add]
    have h2 : (relThetaWindowEquiv C R' π a hH1
          (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _ (1 ⊗ₜ x)
            + TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _
              (1 ⊗ₜ y))).val.2
        = (relThetaWindowEquiv C R' π a hH1
            (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R'
              _ (1 ⊗ₜ x))).val.2
          + (relThetaWindowEquiv C R' π a hH1
              (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R'
                _ (1 ⊗ₜ y))).val.2 := by
      rw [map_add]
      rfl
    have h3 : (relThetaWindowEquiv C R π a hH1 (x + y)).val.2
        = (relThetaWindowEquiv C R π a hH1 x).val.2
          + (relThetaWindowEquiv C R π a hH1 y).val.2 := by
      rw [map_add]
      rfl
    rw [hL, h2, map_add, hx, hy, h3, map_add, map_add]
  | tmul r h =>
    -- the compared pure tensor: `1 ⊗ (r ⊗ h) ↦ algebraMap r • (1 ⊗ h)`
    have hcmp : TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R'
        (↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) (1 ⊗ₜ (r ⊗ₜ h))
        = algebraMap R R' r • ((1 : R') ⊗ₜ h) := by
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
    have hsm : (r ⊗ₜ h : R ⊗[k] ↥(Scheme.divisorSections k
        (a • fiberWeilDivisor π) ⊤)) = r • ((1 : R) ⊗ₜ h) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have e1 : (relThetaWindowEquiv C R' π a hH1
          (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _
            (1 ⊗ₜ (r ⊗ₜ h)))).val.2
        = algebraMap R R' r • (relThetaWindowEquiv C R' π a hH1 (1 ⊗ₜ h)).val.2 := by
      rw [hcmp, map_smul]
      rfl
    have e2 : (relThetaWindowEquiv C R π a hH1 (r ⊗ₜ h)).val.2
        = r • (relThetaWindowEquiv C R π a hH1 (1 ⊗ₜ h)).val.2 := by
      rw [hsm, map_smul]
      rfl
    refine ((congrArg ((relCurve C R').resHom (le_inf le_top le_rfl)) e1).trans
      (resHom_smul_rel' C R' _ _ _)).trans ?_
    refine (congrArg (algebraMap R R' r • ·)
      (resHom_relThetaWindowEquiv_one_tmul_snd C π a hH1 R' h)).trans ?_
    refine ((congrArg (algebraMap R R' r • ·)
      (relSectionsMap_relSectionsMap C R R' (fiberTwoCover π).V₁ _)).symm).trans ?_
    refine ((relSectionsMap_smul C R R' (fiberTwoCover π).V₁ r _).symm).trans ?_
    refine congrArg (relSectionsMap C R R' (fiberTwoCover π).V₁) ?_
    exact (((congrArg ((relCurve C R).resHom (le_inf le_top le_rfl)) e2).trans
      (resHom_smul_rel' C R _ _ _)).trans
      (congrArg (r • ·)
        (resHom_relThetaWindowEquiv_one_tmul_snd C π a hH1 R h))).symm

end Triangle

end AlgebraicGeometry
