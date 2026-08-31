/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafTermBaseChangeEquiv
import AlgebraicJacobian.Cohomology.GluedSheafAffineProjective
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaDescent

/-!
# Restriction of affine theta-section models

This file proves the module base-change bridge needed to compare the theta modules on
two members of an affine divisor cover. Its construction is intrinsic to the glued
sheaf: there is no extra hypothesis on the divisor family or on the affine opens.

The key geometric input is a finite basic-open cover of an affine subopen `W ≤ V`
which is simultaneously subordinate to the original gluing pieces. This lets later
localization arguments use the established piece-localization theorem for the glued
sheaf. We package the canonical section restriction and prove that its base-change map
is bijective for every inclusion of affine opens.

## Main declarations

* `BasicOpenCocycleDatum.exists_finite_basicOpen_cover_le` produces the finite
  subordinate localization family;
* `BasicOpenCocycleDatum.affineSectionsBaseChange` is the canonical comparison;
* `BasicOpenCocycleDatum.affineSectionsBaseChange_bijective` proves that comparison is
  an equivalence, without an additional hypothesis.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

section Algebra

variable {R A S M N : Type u}
variable [CommRing R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S] [Algebra A S]
variable [IsScalarTower R A S]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N] [Module A N] [Module S N]
variable [IsScalarTower R A N] [IsScalarTower R S N] [IsScalarTower A S N]

/-- Base change in stages preserves the base-change property: if `S ⊗[R] M → N` is
an equivalence, then so is `S ⊗[A] (A ⊗[R] M) → N`. -/
theorem isBaseChange_liftBaseChange_of_isBaseChange
    (f : M →ₗ[R] N) (hf : IsBaseChange S f) :
    IsBaseChange S (LinearMap.liftBaseChange A f) := by
  let e : S ⊗[A] (A ⊗[R] M) ≃ₗ[S] N :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A S S M).trans hf.equiv
  apply IsBaseChange.of_equiv e
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
  | tmul a m =>
      change hf.equiv
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange R A S S M)
            (1 ⊗ₜ[A] (a ⊗ₜ[R] m))) = _
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        IsBaseChange.equiv_tmul, LinearMap.liftBaseChange_tmul]
      simp

end Algebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {pi : C.left ⟶ P1 k} [IsAffineHom pi]

namespace BasicOpenCocycleDatum

/-- If `W ≤ V` are affine opens, there is a finite family of basic opens of `V`
covering `W`, each subordinate to a gluing piece. After restriction to `W`, their
defining sections span the unit ideal of `Γ(W)`. -/
theorem exists_finite_basicOpen_cover_le
    (D : BasicOpenCocycleDatum C B pi)
    {V W : (relCurve C B).Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hWV : W ≤ V) :
    ∃ (ι : Type u) (_ : Fintype ι) (f : ι → Γ(relCurve C B, V))
      (anchor : ι → relCurve C B),
      (∀ i, (relCurve C B).basicOpen (f i) ≤ W) ∧
      (∀ i, (relCurve C B).basicOpen (f i) ≤ D.pieces (D.pieceIndex (anchor i))) ∧
      Ideal.span (Set.range (fun i ↦ (relCurve C B).resHom hWV (f i))) = ⊤ := by
  classical
  let X := relCurve C B
  have hpt : ∀ p : ↥W, ∃ f : Γ(X, V),
      X.basicOpen f ≤ W ⊓ D.pieces (D.pieceIndex (p : X)) ∧
        (p : X) ∈ X.basicOpen f := fun p =>
    hV.exists_basicOpen_le
      (⟨(p : X), p.2, D.mem_pieces_pieceIndex (p : X)⟩ :
        ↥(W ⊓ D.pieces (D.pieceIndex (p : X))))
      (hWV p.2)
  choose f hfle hfmem using hpt
  have hcov : (W : Set X) ⊆ ⋃ p : ↥W, (X.basicOpen (f p) : Set X) := fun q hq =>
    Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hfmem ⟨q, hq⟩⟩
  obtain ⟨t, ht⟩ := hW.isCompact.elim_finite_subcover
    (fun p : ↥W => (X.basicOpen (f p) : Set X))
    (fun p => (X.basicOpen (f p)).isOpen) hcov
  let ι := {p : ↥W // p ∈ t}
  let f' : ι → Γ(X, V) := fun i => f (i : ↥W)
  let anchor : ι → X := fun i => ((i : ↥W) : X)
  have hfW (i : ι) : X.basicOpen (f' i) ≤ W :=
    (hfle (i : ↥W)).trans inf_le_left
  have hfP (i : ι) : X.basicOpen (f' i) ≤ D.pieces (D.pieceIndex (anchor i)) :=
    (hfle (i : ↥W)).trans inf_le_right
  refine ⟨ι, inferInstance, f', anchor, hfW, hfP, ?_⟩
  apply hW.self_le_iSup_basicOpen_iff.mp
  intro q hq
  obtain ⟨p, hpt, hpq⟩ := Set.mem_iUnion₂.mp (ht hq)
  let i : ι := ⟨p, hpt⟩
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨⟨X.resHom hWV (f' i), Set.mem_range_self i⟩, ?_⟩
  rw [Scheme.basicOpen_resHom hWV]
  exact ⟨hq, hpq⟩

/-- Restriction of glued-sheaf sections between two selected affine section models,
viewed as a semilinear map along the restriction homomorphism on functions. -/
noncomputable def affineSectionsRestriction
    (D : BasicOpenCocycleDatum C B pi)
    {V W : (relCurve C B).Opens} (hWV : W ≤ V)
    (MV : D.AffineSectionsModel V) (MW : D.AffineSectionsModel W) :
    letI := MV.qcoh
    letI : Module Γ(relCurve C B, V) (D.sheaf.obj.obj (op V)) :=
      Scheme.QcohOn.moduleOfLE (F := D.sheaf) (le_refl V)
    letI := MW.qcoh
    letI : Module Γ(relCurve C B, W) (D.sheaf.obj.obj (op W)) :=
      Scheme.QcohOn.moduleOfLE (F := D.sheaf) (le_refl W)
    D.sheaf.obj.obj (op V) →ₛₗ[(relCurve C B).resHom hWV]
      D.sheaf.obj.obj (op W) := by
  letI := MV.qcoh
  letI : Module Γ(relCurve C B, V) (D.sheaf.obj.obj (op V)) :=
    Scheme.QcohOn.moduleOfLE (F := D.sheaf) (le_refl V)
  letI := MW.qcoh
  letI : Module Γ(relCurve C B, W) (D.sheaf.obj.obj (op W)) :=
    Scheme.QcohOn.moduleOfLE (F := D.sheaf) (le_refl W)
  refine
    { toFun := secRes D.sheaf hWV
      map_add' := (secRes D.sheaf hWV).map_add
      map_smul' := fun r s => ?_ }
  change secRes D.sheaf hWV
      (Scheme.QcohOn.qsmul (F := D.sheaf) (le_refl V) r s) =
    Scheme.QcohOn.qsmul (F := D.sheaf) (le_refl W)
      ((relCurve C B).resHom hWV r) (secRes D.sheaf hWV s)
  rw [MV.qsmul_eq, MW.qsmul_eq]
  exact (gluedRes_gluedQsmul B D.pieces D.unit hWV (le_refl V) r s).trans
    (gluedQsmul_res B D.pieces D.unit (le_refl W) hWV r
      (gluedRes B D.pieces D.unit hWV s)).symm

/-- The canonical base-change comparison from sections on `V` to sections on the
affine subopen `W`. Its source and target actions are exactly those carried by the
chosen `AffineSectionsModel`s. -/
noncomputable def affineSectionsBaseChange
    (D : BasicOpenCocycleDatum C B pi)
    {V W : (relCurve C B).Opens} (hWV : W ≤ V)
    (MV : D.AffineSectionsModel V) (MW : D.AffineSectionsModel W) :
    letI := MV.qcoh
    letI : Module Γ(relCurve C B, V) (D.sheaf.obj.obj (op V)) :=
      Scheme.QcohOn.moduleOfLE (F := D.sheaf) (le_refl V)
    letI := MW.qcoh
    letI : Module Γ(relCurve C B, W) (D.sheaf.obj.obj (op W)) :=
      Scheme.QcohOn.moduleOfLE (F := D.sheaf) (le_refl W)
    letI : Algebra Γ(relCurve C B, V) Γ(relCurve C B, W) :=
      ((relCurve C B).resHom hWV).toAlgebra
    Γ(relCurve C B, W) ⊗[Γ(relCurve C B, V)] D.sheaf.obj.obj (op V) →ₗ[
      Γ(relCurve C B, W)] D.sheaf.obj.obj (op W) := by
  letI := MV.qcoh
  letI : Module Γ(relCurve C B, V) (D.sheaf.obj.obj (op V)) :=
    Scheme.QcohOn.moduleOfLE (F := D.sheaf) (le_refl V)
  letI : Module Γ(relCurve C B, V) (D.sheaf.obj.obj (op W)) :=
    Scheme.QcohOn.moduleOfLE (F := D.sheaf) hWV
  letI := MW.qcoh
  letI : Module Γ(relCurve C B, W) (D.sheaf.obj.obj (op W)) :=
    Scheme.QcohOn.moduleOfLE (F := D.sheaf) (le_refl W)
  letI : Algebra Γ(relCurve C B, V) Γ(relCurve C B, W) :=
    ((relCurve C B).resHom hWV).toAlgebra
  haveI : IsScalarTower Γ(relCurve C B, V) Γ(relCurve C B, W)
      (D.sheaf.obj.obj (op W)) := by
    apply IsScalarTower.of_algebraMap_smul
    intro r s
    change Scheme.QcohOn.qsmul (F := D.sheaf) (le_refl W)
        ((relCurve C B).resHom hWV r) s =
      Scheme.QcohOn.qsmul (F := D.sheaf) hWV r s
    rw [MW.qsmul_eq, MV.qsmul_eq]
    exact gluedQsmul_res B D.pieces D.unit (le_refl W) hWV r s
  exact LinearMap.liftBaseChange Γ(relCurve C B, W)
    (Scheme.QcohOn.secResₗ (F := D.sheaf) hWV (le_refl V))

@[simp]
theorem affineSectionsBaseChange_tmul
    (D : BasicOpenCocycleDatum C B pi)
    {V W : (relCurve C B).Opens} (hWV : W ≤ V)
    (MV : D.AffineSectionsModel V) (MW : D.AffineSectionsModel W)
    (r : Γ(relCurve C B, W)) (s : D.sheaf.obj.obj (op V)) :
    letI := MV.qcoh
    letI : Module Γ(relCurve C B, V) (D.sheaf.obj.obj (op V)) :=
      Scheme.QcohOn.moduleOfLE (F := D.sheaf) (le_refl V)
    letI := MW.qcoh
    letI : Module Γ(relCurve C B, W) (D.sheaf.obj.obj (op W)) :=
      Scheme.QcohOn.moduleOfLE (F := D.sheaf) (le_refl W)
    letI : Algebra Γ(relCurve C B, V) Γ(relCurve C B, W) :=
      ((relCurve C B).resHom hWV).toAlgebra
    D.affineSectionsBaseChange hWV MV MW (r ⊗ₜ s) =
      r • secRes D.sheaf hWV s := by
  rfl

set_option maxHeartbeats 1600000 in
-- Instance synthesis traverses the dependent family of localized comparison modules.
set_option synthInstance.maxHeartbeats 800000 in
/-- Given a finite subordinate family whose restrictions span `Γ(W)`, the canonical
base-change comparison from `V` to `W` is bijective. The heartbeat allowance is for the
dependent localization-span instance graph over the chosen family. -/
theorem affineSectionsBaseChange_bijective_of_cover
    (D : BasicOpenCocycleDatum C B pi)
    {V W : (relCurve C B).Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hWV : W ≤ V)
    (MV : D.AffineSectionsModel V) (MW : D.AffineSectionsModel W)
    {iota : Type u}
    (f : iota → Γ(relCurve C B, V)) (anchor : iota → relCurve C B)
    (hfW : ∀ i, (relCurve C B).basicOpen (f i) ≤ W)
    (hfP : ∀ i, (relCurve C B).basicOpen (f i) ≤
      D.pieces (D.pieceIndex (anchor i)))
    (hspan : Ideal.span (Set.range (fun i ↦
      (relCurve C B).resHom hWV (f i))) = ⊤) :
    Function.Bijective (D.affineSectionsBaseChange hWV MV MW) := by
  let X := relCurve C B
  letI := MV.qcoh
  letI : Module Γ(X, V) (D.sheaf.obj.obj (op V)) :=
    Scheme.QcohOn.moduleOfLE (F := D.sheaf) (le_refl V)
  letI : Module Γ(X, V) (D.sheaf.obj.obj (op W)) :=
    Scheme.QcohOn.moduleOfLE (F := D.sheaf) hWV
  letI := MW.qcoh
  letI : Module Γ(X, W) (D.sheaf.obj.obj (op W)) :=
    Scheme.QcohOn.moduleOfLE (F := D.sheaf) (le_refl W)
  letI : Algebra Γ(X, V) Γ(X, W) := (X.resHom hWV).toAlgebra
  haveI : IsScalarTower Γ(X, V) Γ(X, W) (D.sheaf.obj.obj (op W)) := by
    apply IsScalarTower.of_algebraMap_smul
    intro r s
    change Scheme.QcohOn.qsmul (F := D.sheaf) (le_refl W)
        (X.resHom hWV r) s = Scheme.QcohOn.qsmul (F := D.sheaf) hWV r s
    rw [MW.qsmul_eq, MV.qsmul_eq]
    exact gluedQsmul_res B D.pieces D.unit (le_refl W) hWV r s
  classical
  let g : iota → Γ(X, W) := fun i ↦ X.resHom hWV (f i)
  have hbasic (i : iota) : X.basicOpen (g i) = X.basicOpen (f i) := by
    rw [Scheme.basicOpen_resHom hWV]
    exact inf_eq_right.mpr (hfW i)
  have hPg (i : iota) : X.basicOpen (g i) ≤
      D.pieces (D.pieceIndex (anchor i)) := by
    rw [hbasic i]
    exact hfP i
  have hmem : ∀ gg : Set.range g, ∃ i : iota, g i = gg.1 := fun gg ↦ gg.2
  letI iWF : ∀ gg : Set.range g,
      Module Γ(X, W) (D.sheaf.obj.obj
        (op (X.basicOpen (g (hmem gg).choose)))) :=
    fun gg ↦ Scheme.QcohOn.moduleOfLE (F := D.sheaf)
      (X.basicOpen_le (g (hmem gg).choose))
  letI iWGamma : ∀ gg : Set.range g,
      Algebra Γ(X, W) Γ(X, X.basicOpen (g (hmem gg).choose)) :=
    fun gg ↦ (X.resHom (X.basicOpen_le (g (hmem gg).choose))).toAlgebra
  haveI hfinst : ∀ gg : Set.range g, IsLocalizedModule.Away
      (gg.1 : Γ(X, W))
      ((TensorProduct.mk Γ(X, W)
        Γ(X, X.basicOpen (g (hmem gg).choose))
        (Γ(X, W) ⊗[Γ(X, V)] D.sheaf.obj.obj (op V))) 1) := by
    intro gg
    haveI hLoc : IsLocalization.Away (g (hmem gg).choose)
        Γ(X, X.basicOpen (g (hmem gg).choose)) :=
      hW.isLocalization_basicOpen (g (hmem gg).choose)
    have hpow : Submonoid.powers (gg.1 : Γ(X, W)) =
        Submonoid.powers (g (hmem gg).choose) :=
      congrArg Submonoid.powers (hmem gg).choose_spec.symm
    change IsLocalizedModule (Submonoid.powers (gg.1 : Γ(X, W))) _
    rw [hpow]
    exact (isLocalizedModule_iff_isBaseChange
      (Submonoid.powers (g (hmem gg).choose))
      Γ(X, X.basicOpen (g (hmem gg).choose)) _).mpr
        (TensorProduct.isBaseChange Γ(X, W)
          (Γ(X, W) ⊗[Γ(X, V)] D.sheaf.obj.obj (op V))
          Γ(X, X.basicOpen (g (hmem gg).choose)))
  haveI hginst : ∀ gg : Set.range g, IsLocalizedModule.Away
      (gg.1 : Γ(X, W))
      (Scheme.QcohOn.secResₗ (F := D.sheaf)
        (X.basicOpen_le (g (hmem gg).choose)) (le_refl W)) := by
    intro gg
    haveI hsec : IsLocalizedModule
        (Submonoid.powers (g (hmem gg).choose))
        (Scheme.QcohOn.secResₗ (F := D.sheaf)
          (X.basicOpen_le (g (hmem gg).choose)) (le_refl W)) :=
      isLocalizedModule_secResₗ_glued B D.pieces D.unit hW D.isGluingCocycle
        (fun hU r s ↦ MW.qsmul_eq hU r s) hPg (hmem gg).choose
    have hpow : Submonoid.powers (gg.1 : Γ(X, W)) =
        Submonoid.powers (g (hmem gg).choose) :=
      congrArg Submonoid.powers (hmem gg).choose_spec.symm
    change IsLocalizedModule (Submonoid.powers (gg.1 : Γ(X, W))) _
    rw [hpow]
    exact hsec
  refine bijective_of_isLocalized_span (Set.range g) hspan
    (Mₚ := fun gg ↦
      Γ(X, X.basicOpen (g (hmem gg).choose)) ⊗[Γ(X, W)]
        (Γ(X, W) ⊗[Γ(X, V)] D.sheaf.obj.obj (op V)))
    (f := fun gg ↦ (TensorProduct.mk Γ(X, W)
      Γ(X, X.basicOpen (g (hmem gg).choose))
      (Γ(X, W) ⊗[Γ(X, V)] D.sheaf.obj.obj (op V))) 1)
    (Nₚ := fun gg ↦ D.sheaf.obj.obj
      (op (X.basicOpen (g (hmem gg).choose))))
    (g := fun gg ↦ Scheme.QcohOn.secResₗ (F := D.sheaf)
      (X.basicOpen_le (g (hmem gg).choose)) (le_refl W))
    (F := D.affineSectionsBaseChange hWV MV MW) ?_
  intro gg
  let idx : iota := (hmem gg).choose
  let O : X.Opens := X.basicOpen (g idx)
  letI : Module Γ(X, V) (D.sheaf.obj.obj (op O)) :=
    Scheme.QcohOn.moduleOfLE (F := D.sheaf)
      ((X.basicOpen_le (g idx)).trans hWV)
  letI : Algebra Γ(X, V) Γ(X, O) :=
    (X.resHom ((X.basicOpen_le (g idx)).trans hWV)).toAlgebra
  letI : Module Γ(X, O) (D.sheaf.obj.obj (op O)) :=
    gluedPieceModule B D.pieces D.unit D.isGluingCocycle hPg idx
  haveI iWON : IsScalarTower Γ(X, W) Γ(X, O)
      (D.sheaf.obj.obj (op O)) :=
    isScalarTower_chart_piece B D.pieces D.unit D.isGluingCocycle
      (fun hU r s ↦ MW.qsmul_eq hU r s) hPg idx
  haveI iVWO : IsScalarTower Γ(X, V) Γ(X, W) Γ(X, O) := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    exact (X.resHom_resHom hWV (X.basicOpen_le (g idx)) r).symm
  haveI iVWN : IsScalarTower Γ(X, V) Γ(X, W)
      (D.sheaf.obj.obj (op O)) := by
    apply IsScalarTower.of_algebraMap_smul
    intro r s
    change Scheme.QcohOn.qsmul (F := D.sheaf)
        (X.basicOpen_le (g idx)) (X.resHom hWV r) s =
      Scheme.QcohOn.qsmul (F := D.sheaf)
        ((X.basicOpen_le (g idx)).trans hWV) r s
    rw [MW.qsmul_eq, MV.qsmul_eq]
    exact gluedQsmul_res B D.pieces D.unit
      (X.basicOpen_le (g idx)) hWV r s
  haveI iVON : IsScalarTower Γ(X, V) Γ(X, O)
      (D.sheaf.obj.obj (op O)) := by
    apply IsScalarTower.of_algebraMap_smul
    intro r s
    rw [IsScalarTower.algebraMap_apply Γ(X, V) Γ(X, W) Γ(X, O),
      IsScalarTower.algebraMap_smul Γ(X, O),
      IsScalarTower.algebraMap_smul Γ(X, W)]
  haveI hLocV : IsLocalization.Away (f idx) Γ(X, O) := by
    letI : Algebra Γ(X, V) Γ(X, X.basicOpen (f idx)) :=
      (X.resHom (X.basicOpen_le (f idx))).toAlgebra
    haveI : IsLocalization.Away (f idx) Γ(X, X.basicOpen (f idx)) :=
      hV.isLocalization_basicOpen (f idx)
    let e : Γ(X, X.basicOpen (f idx)) ≃ₐ[Γ(X, V)] Γ(X, O) :=
      AlgEquiv.ofRingEquiv
        (f := (relResCongrAlg C B (hbasic idx).symm).toRingEquiv) (fun r ↦ by
          change X.resHom (hbasic idx).symm.ge
              (X.resHom (X.basicOpen_le (f idx)) r) =
            X.resHom ((X.basicOpen_le (g idx)).trans hWV) r
          rw [Scheme.resHom_resHom])
    exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (f idx)) e
  haveI hsecV : IsLocalizedModule (Submonoid.powers (f idx))
      (Scheme.QcohOn.secResₗ (F := D.sheaf)
        ((X.basicOpen_le (g idx)).trans hWV) (le_refl V)) := by
    letI : Module Γ(X, V)
        (D.sheaf.obj.obj (op (X.basicOpen (f idx)))) :=
      Scheme.QcohOn.moduleOfLE (F := D.sheaf) (X.basicOpen_le (f idx))
    haveI hsecV0 : IsLocalizedModule (Submonoid.powers (f idx))
        (Scheme.QcohOn.secResₗ (F := D.sheaf)
          (X.basicOpen_le (f idx)) (le_refl V)) :=
      isLocalizedModule_secResₗ_glued B D.pieces D.unit hV D.isGluingCocycle
        (fun hU r s ↦ MV.qsmul_eq hU r s) hfP idx
    let e : D.sheaf.obj.obj (op (X.basicOpen (f idx))) ≃ₗ[Γ(X, V)]
        D.sheaf.obj.obj (op O) :=
      LinearEquiv.ofLinear
        (Scheme.QcohOn.secResₗ (F := D.sheaf)
          (hbasic idx).le (X.basicOpen_le (f idx)))
        (Scheme.QcohOn.secResₗ (F := D.sheaf)
          (hbasic idx).ge ((X.basicOpen_le (g idx)).trans hWV))
        (LinearMap.ext fun s ↦ by
          change gluedRes B D.pieces D.unit (hbasic idx).le
              (gluedRes B D.pieces D.unit (hbasic idx).ge s) = s
          rw [gluedRes_gluedRes]
          exact gluedRes_self B D.pieces D.unit _ s)
        (LinearMap.ext fun s ↦ by
          change gluedRes B D.pieces D.unit (hbasic idx).ge
              (gluedRes B D.pieces D.unit (hbasic idx).le s) = s
          rw [gluedRes_gluedRes]
          exact gluedRes_self B D.pieces D.unit _ s)
    have heq : (e : D.sheaf.obj.obj (op (X.basicOpen (f idx))) →ₗ[Γ(X, V)]
          D.sheaf.obj.obj (op O)) ∘ₗ
        Scheme.QcohOn.secResₗ (F := D.sheaf)
          (X.basicOpen_le (f idx)) (le_refl V) =
        Scheme.QcohOn.secResₗ (F := D.sheaf)
          ((X.basicOpen_le (g idx)).trans hWV) (le_refl V) := by
      refine LinearMap.ext fun s ↦ ?_
      change gluedRes B D.pieces D.unit (hbasic idx).le
          (gluedRes B D.pieces D.unit (X.basicOpen_le (f idx)) s) =
        gluedRes B D.pieces D.unit
          ((X.basicOpen_le (g idx)).trans hWV) s
      rw [gluedRes_gluedRes]
    rw [← heq]
    exact IsLocalizedModule.of_linearEquiv _ _ _
  let secVO : D.sheaf.obj.obj (op V) →ₗ[Γ(X, V)]
      D.sheaf.obj.obj (op O) :=
    Scheme.QcohOn.secResₗ (F := D.sheaf)
      ((X.basicOpen_le (g idx)).trans hWV) (le_refl V)
  have hbcVO : IsBaseChange Γ(X, O) secVO :=
    IsLocalizedModule.isBaseChange (Submonoid.powers (f idx)) Γ(X, O) secVO
  have hbcLift : IsBaseChange Γ(X, O)
      (LinearMap.liftBaseChange Γ(X, W) secVO) :=
    isBaseChange_liftBaseChange_of_isBaseChange secVO hbcVO
  haveI hLocW : IsLocalization.Away (g idx) Γ(X, O) :=
    hW.isLocalization_basicOpen (g idx)
  haveI hLift : IsLocalizedModule (Submonoid.powers (g idx))
      (LinearMap.liftBaseChange Γ(X, W) secVO) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers (g idx)) Γ(X, O)
      (LinearMap.liftBaseChange Γ(X, W) secVO)).mpr hbcLift
  let q : D.sheaf.obj.obj (op W) →ₗ[Γ(X, W)]
      D.sheaf.obj.obj (op O) :=
    Scheme.QcohOn.secResₗ (F := D.sheaf)
      (X.basicOpen_le (g idx)) (le_refl W)
  have hcompEq : q ∘ₗ D.affineSectionsBaseChange hWV MV MW =
      LinearMap.liftBaseChange Γ(X, W) secVO := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r s =>
        change q (r • secRes D.sheaf hWV s) = r • secRes D.sheaf
          ((X.basicOpen_le (g idx)).trans hWV) s
        rw [map_smul]
        congr 1
        change gluedRes B D.pieces D.unit (X.basicOpen_le (g idx))
            (gluedRes B D.pieces D.unit hWV s) =
          gluedRes B D.pieces D.unit ((X.basicOpen_le (g idx)).trans hWV) s
        rw [gluedRes_gluedRes]
  have hpow : Submonoid.powers (gg.1 : Γ(X, W)) =
      Submonoid.powers (g idx) :=
    congrArg Submonoid.powers (hmem gg).choose_spec.symm
  haveI hcomp : IsLocalizedModule (Submonoid.powers (gg.1 : Γ(X, W)))
      (q ∘ₗ D.affineSectionsBaseChange hWV MV MW) := by
    rw [hpow, hcompEq]
    exact hLift
  refine IsLocalizedModule.bijective_of_comp_eq
    (Submonoid.powers (gg.1 : Γ(X, W)))
    ((TensorProduct.mk Γ(X, W) Γ(X, O)
      (Γ(X, W) ⊗[Γ(X, V)] D.sheaf.obj.obj (op V))) 1)
    (q ∘ₗ D.affineSectionsBaseChange hWV MV MW)
    _ ?_
  exact LinearMap.ext fun x ↦ IsLocalizedModule.map_apply _ _ _ _ x

set_option maxHeartbeats 1600000 in
-- The wrapper elaborates the finite affine refinement and the dependent theorem above.
set_option synthInstance.maxHeartbeats 800000 in
/-- On any inclusion `W ≤ V` of affine opens, sections of the cocycle-glued line bundle
on `W` are the base change of sections on `V`. The heartbeat allowance covers synthesis
of the finite subordinate localization family used by the preceding theorem. -/
theorem affineSectionsBaseChange_bijective
    (D : BasicOpenCocycleDatum C B pi)
    {V W : (relCurve C B).Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hWV : W ≤ V)
    (MV : D.AffineSectionsModel V) (MW : D.AffineSectionsModel W) :
    Function.Bijective (D.affineSectionsBaseChange hWV MV MW) := by
  obtain ⟨iota, _, f, anchor, hfW, hfP, hspan⟩ :=
    D.exists_finite_basicOpen_cover_le hV hW hWV
  exact D.affineSectionsBaseChange_bijective_of_cover hV hW hWV MV MW
    f anchor hfW hfP hspan

end BasicOpenCocycleDatum

end AlgebraicGeometry
