/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafTermBaseChange
import AlgebraicJacobian.Cohomology.RelativeH1BaseChange

/-!
# Chart-term base change of the glued sheaf, on the nose (DAT-1, stage 1d-ii, terms —
part 2)

The assembly of the stage-(1d-ii) term identification: on a pinned chart open `V`
carrying a finite subordinate trivializing basic-open family, the glued sections of the
base-changed datum are **on the nose** the base change of the glued sections,

* `termBaseChange_bijective` — the comparison
  `Ψ : A' ⊗[A] F_D(V_B) →ₗ[A'] F_{D'}(V_{B'})` is bijective: by
  `bijective_of_isLocalized_span` over the B-side family, the localized comparisons are
  bijective since both sides are localizations of `A' ⊗[A] F(V_B)` at the powers of
  `h i` (`termPieceLocalized` for the target, the tensor-of-localizations instance for
  the source) — `IsLocalizedModule.bijective_of_comp_eq`.
* `termBaseChange` — **the on-the-nose chart-term base change**
  `B' ⊗[B] F_D(V_B) ≃ₗ[B'] F_{D'}(V_{B'})`, assembled from
  `IsBaseChange.tensorProduct_mk_one` (base change in stages, along the landed
  `relTermBaseChange`) and the bijective comparison.
* `termBaseChange_tmul` — the computation rule
  `b' ⊗ s ↦ b' • sectionsMap s` (the m-chart mirror of the 2-chart
  `relTwistTermBaseChange₀/₁` tmul rules; the DAT-3 (a)-step and RE-5 transport
  interface).
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C B, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k B).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite

open scoped TensorProduct

namespace AlgebraicGeometry

namespace BasicOpenCocycleDatum

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B'] [IsScalarTower k B B']
variable {π : C.left ⟶ P1 k} [IsAffineHom π]
variable (D : BasicOpenCocycleDatum C B π)

attribute [local instance] Scheme.overModule

section Assembly

variable (V : C.left.Opens)
variable [Scheme.QcohOn D.sheaf ((fst C (overSpec k B)).left ⁻¹ᵁ V)]
variable [Scheme.QcohOn (D.baseChange B').sheaf ((fst C (overSpec k B')).left ⁻¹ᵁ V)]
variable {ι : Type u} (σ : ι → D.index)
variable (h : ι → Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))

set_option maxHeartbeats 1000000 in
-- The mixed-spelling defeq checks and the instance searches on the tensor types are
-- heavy, as in the 2-chart template (`RigidEngine4BaseChange`).
set_option synthInstance.maxHeartbeats 400000 in
/-- **Bijectivity of the chart-term comparison** (stage 1d-ii): the `liftBaseChange` of
the componentwise `sectionsMap` is bijective — locally on the trivializing family both
sides are localizations of the source at the powers of `h i`. -/
theorem termBaseChange_bijective
    (hVaff : IsAffineOpen ((fst C (overSpec k B)).left ⁻¹ᵁ V))
    (hVaff' : IsAffineOpen ((fst C (overSpec k B')).left ⁻¹ᵁ V))
    (hq : ∀ {W : (relCurve C B).Opens} (hW : W ≤ (fst C (overSpec k B)).left ⁻¹ᵁ V)
      (r : Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))
      (s : ↥(gluedSubmodule B D.pieces D.unit W)),
      Scheme.QcohOn.qsmul (F := D.sheaf) hW r s = gluedQsmul B D.pieces D.unit hW r s)
    (hq' : ∀ {W : (relCurve C B').Opens}
      (hW : W ≤ (fst C (overSpec k B')).left ⁻¹ᵁ V)
      (r : Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V))
      (s : ↥(gluedSubmodule B' (D.baseChange B').pieces (D.baseChange B').unit W)),
      Scheme.QcohOn.qsmul (F := (D.baseChange B').sheaf) hW r s =
        gluedQsmul B' (D.baseChange B').pieces (D.baseChange B').unit hW r s)
    (hP : ∀ i : ι, (relCurve C B).basicOpen (h i) ≤ D.pieces (σ i))
    (hspan : Ideal.span (Set.range h) = ⊤) :
    letI := Scheme.QcohOn.moduleOfLE (F := D.sheaf)
      (le_refl ((fst C (overSpec k B)).left ⁻¹ᵁ V))
    letI := Scheme.QcohOn.moduleOfLE (F := (D.baseChange B').sheaf)
      (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))
    letI : Algebra Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
        Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) :=
      (relSectionsMap C B B' V).toAlgebra
    letI : Module Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
        ((D.baseChange B').sheaf.obj.obj (op ((fst C (overSpec k B')).left ⁻¹ᵁ V))) :=
      Module.compHom _ (relSectionsMap C B B' V)
    letI : IsScalarTower Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
        Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
        ((D.baseChange B').sheaf.obj.obj (op ((fst C (overSpec k B')).left ⁻¹ᵁ V))) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    Function.Bijective
      (LinearMap.liftBaseChange Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
        (sectionsMapₗ B' D V hq hq')) := by
  letI := Scheme.QcohOn.moduleOfLE (F := D.sheaf)
    (le_refl ((fst C (overSpec k B)).left ⁻¹ᵁ V))
  letI := Scheme.QcohOn.moduleOfLE (F := (D.baseChange B').sheaf)
    (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))
  letI : Algebra Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) :=
    (relSectionsMap C B B' V).toAlgebra
  letI : Module Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      ((D.baseChange B').sheaf.obj.obj (op ((fst C (overSpec k B')).left ⁻¹ᵁ V))) :=
    Module.compHom _ (relSectionsMap C B B' V)
  letI : IsScalarTower Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
      ((D.baseChange B').sheaf.obj.obj (op ((fst C (overSpec k B')).left ⁻¹ᵁ V))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  classical
  have hmem : ∀ gg : Set.range h, ∃ i : ι, h i = gg.1 := fun gg => gg.2
  -- the per-generator module skeleton
  letI iA'F' : ∀ gg : Set.range h,
      Module Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
        ((D.baseChange B').sheaf.obj.obj
          (op ((relCurve C B').basicOpen (termFamily B' V h (hmem gg).choose)))) :=
    fun gg => Scheme.QcohOn.moduleOfLE (F := (D.baseChange B').sheaf)
      ((relCurve C B').basicOpen_le (termFamily B' V h (hmem gg).choose))
  letI iAF : ∀ gg : Set.range h,
      Module Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
        (D.sheaf.obj.obj (op ((relCurve C B).basicOpen (h (hmem gg).choose)))) :=
    fun gg => Scheme.QcohOn.moduleOfLE (F := D.sheaf)
      ((relCurve C B).basicOpen_le (h (hmem gg).choose))
  letI iAΓ' : ∀ gg : Set.range h,
      Algebra Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
        Γ(relCurve C B', (relCurve C B').basicOpen
          (termFamily B' V h (hmem gg).choose)) :=
    fun gg => ((algebraMap Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
      Γ(relCurve C B', (relCurve C B').basicOpen
        (termFamily B' V h (hmem gg).choose))).comp (relSectionsMap C B B' V)).toAlgebra
  haveI iTAA'Γ' : ∀ gg : Set.range h,
      IsScalarTower Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
        Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
        Γ(relCurve C B', (relCurve C B').basicOpen
          (termFamily B' V h (hmem gg).choose)) :=
    fun gg => IsScalarTower.of_algebraMap_eq' rfl
  letI iAF' : ∀ gg : Set.range h,
      Module Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
        ((D.baseChange B').sheaf.obj.obj
          (op ((relCurve C B').basicOpen (termFamily B' V h (hmem gg).choose)))) :=
    fun gg => Module.compHom _ (relSectionsMap C B B' V)
  haveI iTAA'F' : ∀ gg : Set.range h,
      IsScalarTower Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
        Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
        ((D.baseChange B').sheaf.obj.obj
          (op ((relCurve C B').basicOpen (termFamily B' V h (hmem gg).choose)))) :=
    fun gg => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  -- the source-side localizations: tensors of localizations, per generator
  haveI hfinst : ∀ gg : Set.range h, IsLocalizedModule.Away
      (gg.1 : Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))
      (TensorProduct.map
        ((Algebra.linearMap Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
          Γ(relCurve C B', (relCurve C B').basicOpen
            (termFamily B' V h (hmem gg).choose))).restrictScalars
              Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))
        (Scheme.QcohOn.secResₗ (F := D.sheaf)
          ((relCurve C B).basicOpen_le (h (hmem gg).choose))
          (le_refl ((fst C (overSpec k B)).left ⁻¹ᵁ V)))) := by
    intro gg
    letI := Scheme.QcohOn.moduleOfLE (F := D.sheaf)
      ((relCurve C B).basicOpen_le (h (hmem gg).choose))
    letI aΓΓ' : Algebra Γ(relCurve C B, (relCurve C B).basicOpen (h (hmem gg).choose))
        Γ(relCurve C B', (relCurve C B').basicOpen
          (termFamily B' V h (hmem gg).choose)) :=
      (((relCurveMap C B B').appLE
        ((relCurve C B).basicOpen (h (hmem gg).choose))
        ((relCurve C B').basicOpen (termFamily B' V h (hmem gg).choose))
        (termFamily_basicOpen B' V h (hmem gg).choose).le).hom).toAlgebra
    haveI tAΓΓ' : IsScalarTower Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
        Γ(relCurve C B, (relCurve C B).basicOpen (h (hmem gg).choose))
        Γ(relCurve C B', (relCurve C B').basicOpen
          (termFamily B' V h (hmem gg).choose)) := by
      refine IsScalarTower.of_algebraMap_eq fun a => ?_
      exact (relCurveMap C B B').appLE_resHom
        ((relCurve C B).basicOpen_le (h (hmem gg).choose)) (le_preimage_chart B' V)
        (termFamily_basicOpen B' V h (hmem gg).choose).le
        ((relCurve C B').basicOpen_le (termFamily B' V h (hmem gg).choose)) a
    haveI hLocB : IsLocalization.Away (h (hmem gg).choose)
        Γ(relCurve C B, (relCurve C B).basicOpen (h (hmem gg).choose)) :=
      hVaff.isLocalization_basicOpen (h (hmem gg).choose)
    haveI hLocB' : IsLocalization.Away (termFamily B' V h (hmem gg).choose)
        Γ(relCurve C B', (relCurve C B').basicOpen
          (termFamily B' V h (hmem gg).choose)) :=
      hVaff'.isLocalization_basicOpen (termFamily B' V h (hmem gg).choose)
    haveI hρ' : IsLocalizedModule
        (Submonoid.powers (termFamily B' V h (hmem gg).choose))
        (Algebra.linearMap Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
          Γ(relCurve C B', (relCurve C B').basicOpen
            (termFamily B' V h (hmem gg).choose))) :=
      (isLocalizedModule_iff_isLocalization' _ _).mpr hLocB'
    haveI hρ'' : IsLocalizedModule (Submonoid.powers
        (algebraMap Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
          Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) (h (hmem gg).choose)))
        (Algebra.linearMap Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
          Γ(relCurve C B', (relCurve C B').basicOpen
            (termFamily B' V h (hmem gg).choose))) := hρ'
    haveI hρ : IsLocalizedModule (Submonoid.powers (h (hmem gg).choose))
        ((Algebra.linearMap Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
          Γ(relCurve C B', (relCurve C B').basicOpen
            (termFamily B' V h (hmem gg).choose))).restrictScalars
              Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)) :=
      isLocalizedModule_restrictScalars_powers (h (hmem gg).choose) _
    haveI hsec : IsLocalizedModule (Submonoid.powers (h (hmem gg).choose))
        (Scheme.QcohOn.secResₗ (F := D.sheaf)
          ((relCurve C B).basicOpen_le (h (hmem gg).choose))
          (le_refl ((fst C (overSpec k B)).left ⁻¹ᵁ V))) :=
      isLocalizedModule_secResₗ_glued B D.pieces D.unit hVaff D.isGluingCocycle hq hP
        (hmem gg).choose
    have hpow : Submonoid.powers (gg.1 :
        Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)) =
        Submonoid.powers (h (hmem gg).choose) :=
      congrArg Submonoid.powers (hmem gg).choose_spec.symm
    change IsLocalizedModule (Submonoid.powers (gg.1 :
      Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))) _
    rw [hpow]
    infer_instance
  -- the target-side localizations: restricted piece restrictions, per generator
  haveI hginst : ∀ gg : Set.range h, IsLocalizedModule.Away
      (gg.1 : Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))
      ((Scheme.QcohOn.secResₗ (F := (D.baseChange B').sheaf)
        ((relCurve C B').basicOpen_le (termFamily B' V h (hmem gg).choose))
        (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))).restrictScalars
          Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)) := by
    intro gg
    haveI hsec' : IsLocalizedModule
        (Submonoid.powers (termFamily B' V h (hmem gg).choose))
        (Scheme.QcohOn.secResₗ (F := (D.baseChange B').sheaf)
          ((relCurve C B').basicOpen_le (termFamily B' V h (hmem gg).choose))
          (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))) :=
      isLocalizedModule_secResₗ_glued B' (D.baseChange B').pieces
        (D.baseChange B').unit hVaff' (D.baseChange B').isGluingCocycle hq'
        (termFamily_le B' D V σ h hP) (hmem gg).choose
    haveI hsec'' : IsLocalizedModule (Submonoid.powers
        (algebraMap Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
          Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) (h (hmem gg).choose)))
        (Scheme.QcohOn.secResₗ (F := (D.baseChange B').sheaf)
          ((relCurve C B').basicOpen_le (termFamily B' V h (hmem gg).choose))
          (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))) := hsec'
    have hpow : Submonoid.powers (gg.1 :
        Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)) =
        Submonoid.powers (h (hmem gg).choose) :=
      congrArg Submonoid.powers (hmem gg).choose_spec.symm
    change IsLocalizedModule (Submonoid.powers (gg.1 :
      Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))) _
    rw [hpow]
    exact isLocalizedModule_restrictScalars_powers (h (hmem gg).choose) _
  -- the localized comparisons are bijective
  refine bijective_of_isLocalized_span (Set.range h) hspan
    (Mₚ := fun gg =>
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h (hmem gg).choose))
        ⊗[Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)]
        (D.sheaf.obj.obj (op ((relCurve C B).basicOpen (h (hmem gg).choose)))))
    (f := fun gg => TensorProduct.map
      ((Algebra.linearMap Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
        Γ(relCurve C B', (relCurve C B').basicOpen
          (termFamily B' V h (hmem gg).choose))).restrictScalars
            Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))
      (Scheme.QcohOn.secResₗ (F := D.sheaf)
        ((relCurve C B).basicOpen_le (h (hmem gg).choose))
        (le_refl ((fst C (overSpec k B)).left ⁻¹ᵁ V))))
    (Nₚ := fun gg =>
      ((D.baseChange B').sheaf.obj.obj
        (op ((relCurve C B').basicOpen (termFamily B' V h (hmem gg).choose)))))
    (g := fun gg =>
      (Scheme.QcohOn.secResₗ (F := (D.baseChange B').sheaf)
        ((relCurve C B').basicOpen_le (termFamily B' V h (hmem gg).choose))
        (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))).restrictScalars
          Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))
    (F := (LinearMap.liftBaseChange
      Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
      (sectionsMapₗ B' D V hq hq')).restrictScalars
        Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))
    ?_
  intro gg
  -- bijectivity of the localized comparison, from the two localization structures
  have hpow : Submonoid.powers (gg.1 :
      Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)) =
      Submonoid.powers (h (hmem gg).choose) :=
    congrArg Submonoid.powers (hmem gg).choose_spec.symm
  haveI hcomp : IsLocalizedModule (Submonoid.powers (gg.1 :
      Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)))
      (((Scheme.QcohOn.secResₗ (F := (D.baseChange B').sheaf)
        ((relCurve C B').basicOpen_le (termFamily B' V h (hmem gg).choose))
        (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))).restrictScalars
          Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)) ∘ₗ
        ((LinearMap.liftBaseChange
          Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
          (sectionsMapₗ B' D V hq hq')).restrictScalars
            Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))) := by
    rw [hpow]
    exact termPieceLocalized B' D V σ h hVaff hVaff' hq hq' hP (hmem gg).choose
  refine IsLocalizedModule.bijective_of_comp_eq
    (Submonoid.powers (gg.1 :
      Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)))
    (TensorProduct.map
      ((Algebra.linearMap Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
        Γ(relCurve C B', (relCurve C B').basicOpen
          (termFamily B' V h (hmem gg).choose))).restrictScalars
            Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))
      (Scheme.QcohOn.secResₗ (F := D.sheaf)
        ((relCurve C B).basicOpen_le (h (hmem gg).choose))
        (le_refl ((fst C (overSpec k B)).left ⁻¹ᵁ V))))
    (((Scheme.QcohOn.secResₗ (F := (D.baseChange B').sheaf)
        ((relCurve C B').basicOpen_le (termFamily B' V h (hmem gg).choose))
        (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))).restrictScalars
          Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)) ∘ₗ
      ((LinearMap.liftBaseChange Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
        (sectionsMapₗ B' D V hq hq')).restrictScalars
          Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)))
    _ ?_
  exact LinearMap.ext fun x => IsLocalizedModule.map_apply _ _ _ _ x

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The on-the-nose chart-term base change** (stage 1d-ii): on a pinned chart `V`
carrying a finite subordinate trivializing basic-open family, the glued sections of the
base-changed datum are, `B'`-linearly, the base change of the glued sections,

`B' ⊗[B] F_D(V_B) ≃ₗ[B'] F_{D'}(V_{B'})`.

Assembled from `IsBaseChange.tensorProduct_mk_one` (base change in stages, along the
landed chart-ring comparison `relTermBaseChange`) and the bijective comparison
`termBaseChange_bijective`: the chart-ring `A' = Γ(V_{B'})` is the base change of
`A = Γ(V_B)` along `B → B'`, so `B' ⊗[B] F(V_B) ≃ A' ⊗[A] F(V_B)`, and the latter is
`F'(V_{B'})` by `termBaseChange_bijective`. -/
noncomputable def termBaseChange
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
    (hVaff : IsAffineOpen ((fst C (overSpec k B)).left ⁻¹ᵁ V))
    (hVaff' : IsAffineOpen ((fst C (overSpec k B')).left ⁻¹ᵁ V))
    (hq : ∀ {W : (relCurve C B).Opens} (hW : W ≤ (fst C (overSpec k B)).left ⁻¹ᵁ V)
      (r : Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))
      (s : ↥(gluedSubmodule B D.pieces D.unit W)),
      Scheme.QcohOn.qsmul (F := D.sheaf) hW r s = gluedQsmul B D.pieces D.unit hW r s)
    (hq' : ∀ {W : (relCurve C B').Opens}
      (hW : W ≤ (fst C (overSpec k B')).left ⁻¹ᵁ V)
      (r : Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V))
      (s : ↥(gluedSubmodule B' (D.baseChange B').pieces (D.baseChange B').unit W)),
      Scheme.QcohOn.qsmul (F := (D.baseChange B').sheaf) hW r s =
        gluedQsmul B' (D.baseChange B').pieces (D.baseChange B').unit hW r s)
    (hP : ∀ i : ι, (relCurve C B).basicOpen (h i) ≤ D.pieces (σ i))
    (hspan : Ideal.span (Set.range h) = ⊤) :
    B' ⊗[B] (D.sheaf.obj.obj (op ((fst C (overSpec k B)).left ⁻¹ᵁ V))) ≃ₗ[B']
      ((D.baseChange B').sheaf.obj.obj
        (op ((fst C (overSpec k B')).left ⁻¹ᵁ V))) :=
  letI := Scheme.QcohOn.moduleOfLE (F := D.sheaf)
    (le_refl ((fst C (overSpec k B)).left ⁻¹ᵁ V))
  letI := Scheme.QcohOn.moduleOfLE (F := (D.baseChange B').sheaf)
    (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))
  letI algBA : Algebra B Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V) :=
    ((relCurve C B).overAlgebraMap B ((fst C (overSpec k B)).left ⁻¹ᵁ V)).toAlgebra
  letI algB'A' : Algebra B' Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) :=
    ((relCurve C B').overAlgebraMap B' ((fst C (overSpec k B')).left ⁻¹ᵁ V)).toAlgebra
  letI algAA' : Algebra Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) :=
    (relSectionsMap C B B' V).toAlgebra
  letI algBA' : Algebra B Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) :=
    ((algebraMap B' Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)).comp
      (algebraMap B B')).toAlgebra
  letI : Module Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      ((D.baseChange B').sheaf.obj.obj (op ((fst C (overSpec k B')).left ⁻¹ᵁ V))) :=
    Module.compHom _ (relSectionsMap C B B' V)
  haveI : IsScalarTower Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
      ((D.baseChange B').sheaf.obj.obj (op ((fst C (overSpec k B')).left ⁻¹ᵁ V))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower B B'
      Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower B Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun b =>
      (relSectionsMap_overAlgebraMap C B B' V b).symm
  haveI : IsScalarTower B Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      (D.sheaf.obj.obj (op ((fst C (overSpec k B)).left ⁻¹ᵁ V))) :=
    isScalarTower_coeff B D.pieces D.unit hq (le_refl _)
  haveI : IsScalarTower B'
      Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
      ((D.baseChange B').sheaf.obj.obj
        (op ((fst C (overSpec k B')).left ⁻¹ᵁ V))) :=
    isScalarTower_coeff B' (D.baseChange B').pieces (D.baseChange B').unit hq'
      (le_refl _)
  letI hA : IsBaseChange B' ((IsScalarTower.toAlgHom B
      Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)).toLinearMap) :=
    IsBaseChange.of_equiv (relTermBaseChange C B B' V hV hV') fun x => by
      rw [relTermBaseChange_tmul, one_smul]; rfl
  (IsBaseChange.tensorProduct_mk_one hA).equiv.trans
    ((LinearEquiv.ofBijective
      (LinearMap.liftBaseChange Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
        (sectionsMapₗ B' D V hq hq'))
      (termBaseChange_bijective B' D V σ h hVaff hVaff' hq hq' hP hspan)).restrictScalars
        B')

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The chart-term base change on a pure tensor**: `b' ⊗ s` goes to the `B'`-action of
`b'` on the compared section `sectionsMap s` — the m-chart mirror of the 2-chart
`relTwistTermBaseChange₀/₁` tmul rules (the DAT-3 (a)-step and RE-5 transport interface). -/
theorem termBaseChange_tmul
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
    (hVaff : IsAffineOpen ((fst C (overSpec k B)).left ⁻¹ᵁ V))
    (hVaff' : IsAffineOpen ((fst C (overSpec k B')).left ⁻¹ᵁ V))
    (hq : ∀ {W : (relCurve C B).Opens} (hW : W ≤ (fst C (overSpec k B)).left ⁻¹ᵁ V)
      (r : Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))
      (s : ↥(gluedSubmodule B D.pieces D.unit W)),
      Scheme.QcohOn.qsmul (F := D.sheaf) hW r s = gluedQsmul B D.pieces D.unit hW r s)
    (hq' : ∀ {W : (relCurve C B').Opens}
      (hW : W ≤ (fst C (overSpec k B')).left ⁻¹ᵁ V)
      (r : Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V))
      (s : ↥(gluedSubmodule B' (D.baseChange B').pieces (D.baseChange B').unit W)),
      Scheme.QcohOn.qsmul (F := (D.baseChange B').sheaf) hW r s =
        gluedQsmul B' (D.baseChange B').pieces (D.baseChange B').unit hW r s)
    (hP : ∀ i : ι, (relCurve C B).basicOpen (h i) ≤ D.pieces (σ i))
    (hspan : Ideal.span (Set.range h) = ⊤)
    (b' : B') (s : D.sheaf.obj.obj (op ((fst C (overSpec k B)).left ⁻¹ᵁ V))) :
    termBaseChange B' D V σ h hV hV' hVaff hVaff' hq hq' hP hspan (b' ⊗ₜ[B] s) =
      b' • D.sectionsMap B' (le_preimage_chart B' V) s := by
  letI := Scheme.QcohOn.moduleOfLE (F := D.sheaf)
    (le_refl ((fst C (overSpec k B)).left ⁻¹ᵁ V))
  letI := Scheme.QcohOn.moduleOfLE (F := (D.baseChange B').sheaf)
    (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))
  letI algBA : Algebra B Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V) :=
    ((relCurve C B).overAlgebraMap B ((fst C (overSpec k B)).left ⁻¹ᵁ V)).toAlgebra
  letI algB'A' : Algebra B' Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) :=
    ((relCurve C B').overAlgebraMap B' ((fst C (overSpec k B')).left ⁻¹ᵁ V)).toAlgebra
  letI algAA' : Algebra Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) :=
    (relSectionsMap C B B' V).toAlgebra
  letI algBA' : Algebra B Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) :=
    ((algebraMap B' Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)).comp
      (algebraMap B B')).toAlgebra
  letI : Module Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      ((D.baseChange B').sheaf.obj.obj (op ((fst C (overSpec k B')).left ⁻¹ᵁ V))) :=
    Module.compHom _ (relSectionsMap C B B' V)
  haveI : IsScalarTower Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
      ((D.baseChange B').sheaf.obj.obj (op ((fst C (overSpec k B')).left ⁻¹ᵁ V))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower B B'
      Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower B Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun b =>
      (relSectionsMap_overAlgebraMap C B B' V b).symm
  haveI : IsScalarTower B Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      (D.sheaf.obj.obj (op ((fst C (overSpec k B)).left ⁻¹ᵁ V))) :=
    isScalarTower_coeff B D.pieces D.unit hq (le_refl _)
  haveI : IsScalarTower B'
      Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
      ((D.baseChange B').sheaf.obj.obj
        (op ((fst C (overSpec k B')).left ⁻¹ᵁ V))) :=
    isScalarTower_coeff B' (D.baseChange B').pieces (D.baseChange B').unit hq'
      (le_refl _)
  simp only [termBaseChange, LinearEquiv.trans_apply, IsBaseChange.equiv_tmul,
    LinearMap.restrictScalars_apply, TensorProduct.mk_apply, map_smul,
    LinearEquiv.restrictScalars_apply, LinearEquiv.ofBijective_apply,
    LinearMap.liftBaseChange_tmul, one_smul]
  rfl

end Assembly

end BasicOpenCocycleDatum

end AlgebraicGeometry
