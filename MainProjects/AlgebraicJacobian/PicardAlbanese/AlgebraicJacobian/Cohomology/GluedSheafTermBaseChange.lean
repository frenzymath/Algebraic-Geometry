/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafDatumBaseChange
import AlgebraicJacobian.Cohomology.GluedSheafModule
import AlgebraicJacobian.Cohomology.GluedBaseChangeAlgebra

/-!
# Chart-term base change of the glued sheaf: the comparison and its localizations
(DAT-1, stage 1d-ii, terms — part 1)

On a pinned chart open `V` carrying a finite subordinate trivializing basic-open family,
this file builds the comparison `Ψ : A' ⊗[A] F_D(V_B) →ₗ[A'] F_{D'}(V_{B'})`
(`A := Γ(V_B)`, `A' := Γ(V_{B'})`, the `liftBaseChange` of the componentwise
`sectionsMap`) and proves the piece-level localization identification that stage
(1d-ii)'s bijectivity argument consumes:

* `termFamily`/`termFamily_le`/`termFamily_span`/`termFamily_cover` — the base-changed
  trivializing family (images under `relSectionsMap`), subordinate to the base-changed
  pieces, spanning the unit ideal.
* `sectionsMapₗ` — the comparison as an `A`-linear map (`A` acting on the target
  through the chart-ring comparison).
* `termPieceLocalized` — **the piece-level identification**: composing the comparison
  `Ψ` with the piece restriction `F'(V_{B'}) → F'(D(h'ᵢ))` is a localization of
  `A' ⊗[A] F(V_B)` at the powers of `h i` — through the piece trivializations, the
  target is `Γ'(D(h'ᵢ))`, free of rank one, and the composite matches the
  tensor-of-localizations of the source.

Part 2 (`GluedSheafTermBaseChangeEquiv`) assembles these into the on-the-nose
equivalence `B' ⊗[B] F(V_B) ≃ₗ[B'] F'(V_{B'})` by span-locality.
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

section Terms

variable (V : C.left.Opens)

/-- (Implementation) The chart inclusion of the base-changed open into the
comparison-preimage. -/
lemma le_preimage_chart :
    (fst C (overSpec k B')).left ⁻¹ᵁ V ≤
      relCurveMap C B B' ⁻¹ᵁ ((fst C (overSpec k B)).left ⁻¹ᵁ V) :=
  (relCurveMap_preimage C B B' V).ge

variable {ι : Type u} (σ : ι → D.index)
variable (h : ι → Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))

/-- The base-changed trivializing family: the images of the generators under the
sections comparison. -/
noncomputable def termFamily (i : ι) :
    Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) :=
  relSectionsMap C B B' V (h i)

/-- The base-changed pieces of the family are the comparison-preimages of the
pieces. -/
lemma termFamily_basicOpen (i : ι) :
    (relCurve C B').basicOpen (termFamily B' V h i) =
      relCurveMap C B B' ⁻¹ᵁ ((relCurve C B).basicOpen (h i)) :=
  relSectionsMap_basicOpen C B B' V (h i)

/-- The base-changed family is subordinate to the base-changed pieces. -/
lemma termFamily_le (hP : ∀ i : ι, (relCurve C B).basicOpen (h i) ≤ D.pieces (σ i))
    (i : ι) :
    (relCurve C B').basicOpen (termFamily B' V h i) ≤
      (D.baseChange B').pieces (σ i) := by
  rw [termFamily_basicOpen]
  exact le_of_le_of_eq (Scheme.Hom.preimage_mono _ (hP i))
    (D.toBasicOpenCoverData.pieces_baseChange B' (σ i)).symm

/-- The base-changed family spans the unit ideal. -/
lemma termFamily_span (hspan : Ideal.span (Set.range h) = ⊤) :
    Ideal.span (Set.range (termFamily B' V h)) = ⊤ := by
  have himg : Set.range (termFamily B' V h) =
      (relSectionsMap C B B' V) '' Set.range h := by
    rw [← Set.range_comp]
    rfl
  rw [himg, ← Ideal.map_span, hspan]
  exact Ideal.map_top _

/-- The base-changed family covers the base-changed chart. -/
lemma termFamily_cover (hspan : Ideal.span (Set.range h) = ⊤) :
    ((fst C (overSpec k B')).left ⁻¹ᵁ V : (relCurve C B').Opens) ≤
      ⨆ i : ι, (relCurve C B').basicOpen (termFamily B' V h i) := by
  have hsup := iSup_basicOpen_of_span_eq_top
    ((fst C (overSpec k B')).left ⁻¹ᵁ V : (relCurve C B').Opens)
    (Set.range (termFamily B' V h)) (termFamily_span B' V h hspan)
  conv_lhs => rw [← hsup]
  refine iSup₂_le_iff.mpr fun g hg => ?_
  obtain ⟨i, rfl⟩ := hg
  exact le_iSup (fun i => (relCurve C B').basicOpen (termFamily B' V h i)) i

end Terms

section Comparison

variable (V : C.left.Opens)
variable [Scheme.QcohOn D.sheaf ((fst C (overSpec k B)).left ⁻¹ᵁ V)]
variable [Scheme.QcohOn (D.baseChange B').sheaf ((fst C (overSpec k B')).left ⁻¹ᵁ V)]

/-- **The comparison of glued chart sections, `Γ(V_B)`-linearly**: the componentwise
`sectionsMap`, linear over the chart ring acting on the target through the chart-ring
comparison `relSectionsMap` (the two packaged actions intertwine by
`sectionsMap_gluedQsmul`). -/
noncomputable def sectionsMapₗ
    (hq : ∀ {W : (relCurve C B).Opens} (hW : W ≤ (fst C (overSpec k B)).left ⁻¹ᵁ V)
      (r : Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))
      (s : ↥(gluedSubmodule B D.pieces D.unit W)),
      Scheme.QcohOn.qsmul (F := D.sheaf) hW r s = gluedQsmul B D.pieces D.unit hW r s)
    (hq' : ∀ {W : (relCurve C B').Opens}
      (hW : W ≤ (fst C (overSpec k B')).left ⁻¹ᵁ V)
      (r : Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V))
      (s : ↥(gluedSubmodule B' (D.baseChange B').pieces (D.baseChange B').unit W)),
      Scheme.QcohOn.qsmul (F := (D.baseChange B').sheaf) hW r s =
        gluedQsmul B' (D.baseChange B').pieces (D.baseChange B').unit hW r s) :
    letI := Scheme.QcohOn.moduleOfLE (F := D.sheaf)
      (le_refl ((fst C (overSpec k B)).left ⁻¹ᵁ V))
    letI := Scheme.QcohOn.moduleOfLE (F := (D.baseChange B').sheaf)
      (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))
    letI : Module Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
        ((D.baseChange B').sheaf.obj.obj (op ((fst C (overSpec k B')).left ⁻¹ᵁ V))) :=
      Module.compHom _ (relSectionsMap C B B' V)
    (D.sheaf.obj.obj (op ((fst C (overSpec k B)).left ⁻¹ᵁ V)))
      →ₗ[Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)]
      ((D.baseChange B').sheaf.obj.obj (op ((fst C (overSpec k B')).left ⁻¹ᵁ V))) :=
  letI := Scheme.QcohOn.moduleOfLE (F := D.sheaf)
    (le_refl ((fst C (overSpec k B)).left ⁻¹ᵁ V))
  letI := Scheme.QcohOn.moduleOfLE (F := (D.baseChange B').sheaf)
    (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))
  letI : Module Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      ((D.baseChange B').sheaf.obj.obj (op ((fst C (overSpec k B')).left ⁻¹ᵁ V))) :=
    Module.compHom _ (relSectionsMap C B B' V)
  { toFun := D.sectionsMap B' (le_preimage_chart B' V)
    map_add' := fun s t => D.sectionsMap_add B' (le_preimage_chart B' V) s t
    map_smul' := fun a s => by
      rw [RingHom.id_apply]
      change D.sectionsMap B' (le_preimage_chart B' V)
        (Scheme.QcohOn.qsmul (F := D.sheaf)
          (le_refl ((fst C (overSpec k B)).left ⁻¹ᵁ V)) a s) = _
      rw [hq (le_refl _) a s,
        D.sectionsMap_gluedQsmul B' (le_refl _) (le_preimage_chart B' V)
          (le_preimage_chart B' V) (le_refl _) a s,
        ← hq' (le_refl _) (((relCurveMap C B B').appLE
          ((fst C (overSpec k B)).left ⁻¹ᵁ V) ((fst C (overSpec k B')).left ⁻¹ᵁ V)
          (le_preimage_chart B' V)).hom a) (D.sectionsMap B' (le_preimage_chart B' V) s)]
      rfl }

end Comparison

section Piece

variable (V : C.left.Opens)
variable [Scheme.QcohOn D.sheaf ((fst C (overSpec k B)).left ⁻¹ᵁ V)]
variable [Scheme.QcohOn (D.baseChange B').sheaf ((fst C (overSpec k B')).left ⁻¹ᵁ V)]
variable {ι : Type u} (σ : ι → D.index)
variable (h : ι → Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))

set_option maxHeartbeats 1000000 in
-- The mixed-spelling defeq checks and the instance searches on the tensor types are
-- heavy, as in the 2-chart template (`RigidEngine4BaseChange`).
set_option synthInstance.maxHeartbeats 400000 in
/-- **The piece-level identification** (stage 1d-ii, the localization step): composing
the chart comparison `Ψ = liftBaseChange (sectionsMapₗ)` with the piece restriction
`F'(V_{B'}) → F'(D(h'ᵢ))` exhibits the base-changed piece sections as the localization
of `A' ⊗[A] F(V_B)` at the powers of `h i`. Through the piece trivializations both
sides are free of rank one over the localized rings, and the comparison matches the
canonical one. -/
theorem termPieceLocalized
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
    (hP : ∀ i : ι, (relCurve C B).basicOpen (h i) ≤ D.pieces (σ i)) (i : ι) :
    letI := Scheme.QcohOn.moduleOfLE (F := D.sheaf)
      (le_refl ((fst C (overSpec k B)).left ⁻¹ᵁ V))
    letI := Scheme.QcohOn.moduleOfLE (F := (D.baseChange B').sheaf)
      (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))
    letI := Scheme.QcohOn.moduleOfLE (F := (D.baseChange B').sheaf)
      ((relCurve C B').basicOpen_le (termFamily B' V h i))
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
    letI : Module Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
        ((D.baseChange B').sheaf.obj.obj
          (op ((relCurve C B').basicOpen (termFamily B' V h i)))) :=
      Module.compHom _ (relSectionsMap C B B' V)
    letI : IsScalarTower Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
        Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
        ((D.baseChange B').sheaf.obj.obj
          (op ((relCurve C B').basicOpen (termFamily B' V h i)))) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    IsLocalizedModule (Submonoid.powers (h i))
      (((Scheme.QcohOn.secResₗ (F := (D.baseChange B').sheaf)
          ((relCurve C B').basicOpen_le (termFamily B' V h i))
          (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))).restrictScalars
            Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)) ∘ₗ
        ((LinearMap.liftBaseChange Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
          (sectionsMapₗ B' D V hq hq')).restrictScalars
            Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))) := by
  letI := Scheme.QcohOn.moduleOfLE (F := D.sheaf)
    (le_refl ((fst C (overSpec k B)).left ⁻¹ᵁ V))
  letI := Scheme.QcohOn.moduleOfLE (F := (D.baseChange B').sheaf)
    (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))
  letI := Scheme.QcohOn.moduleOfLE (F := (D.baseChange B').sheaf)
    ((relCurve C B').basicOpen_le (termFamily B' V h i))
  letI := Scheme.QcohOn.moduleOfLE (F := D.sheaf)
    ((relCurve C B).basicOpen_le (h i))
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
  letI : Module Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      ((D.baseChange B').sheaf.obj.obj
        (op ((relCurve C B').basicOpen (termFamily B' V h i)))) :=
    Module.compHom _ (relSectionsMap C B B' V)
  letI : IsScalarTower Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
      ((D.baseChange B').sheaf.obj.obj
        (op ((relCurve C B').basicOpen (termFamily B' V h i)))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  -- the piece rings are the away-localizations of the chart rings
  haveI hLocB : IsLocalization.Away (h i)
      Γ(relCurve C B, (relCurve C B).basicOpen (h i)) :=
    hVaff.isLocalization_basicOpen (h i)
  haveI hLocB' : IsLocalization.Away (termFamily B' V h i)
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i)) :=
    hVaff'.isLocalization_basicOpen (termFamily B' V h i)
  -- the piece ring comparison, and the `A`-algebra structure it induces
  letI aΓΓ' : Algebra Γ(relCurve C B, (relCurve C B).basicOpen (h i))
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i)) :=
    (((relCurveMap C B B').appLE ((relCurve C B).basicOpen (h i))
      ((relCurve C B').basicOpen (termFamily B' V h i))
      (termFamily_basicOpen B' V h i).le).hom).toAlgebra
  letI aAΓ' : Algebra Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i)) :=
    ((algebraMap Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))).comp
        (relSectionsMap C B B' V)).toAlgebra
  haveI tAA'Γ' : IsScalarTower Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI tAΓΓ' : IsScalarTower Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B, (relCurve C B).basicOpen (h i))
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i)) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    exact (relCurveMap C B B').appLE_resHom
      ((relCurve C B).basicOpen_le (h i)) (le_preimage_chart B' V)
      (termFamily_basicOpen B' V h i).le
      ((relCurve C B').basicOpen_le (termFamily B' V h i)) a
  -- the two chart-ring localizations, `A`-linearly
  haveI hρ' : IsLocalizedModule (Submonoid.powers (termFamily B' V h i))
      (Algebra.linearMap Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
        Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))) :=
    (isLocalizedModule_iff_isLocalization' _ _).mpr hLocB'
  haveI hρ'' : IsLocalizedModule (Submonoid.powers
      (algebraMap Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
        Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) (h i)))
      (Algebra.linearMap Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
        Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))) := hρ'
  haveI hρ : IsLocalizedModule (Submonoid.powers (h i))
      ((Algebra.linearMap Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
        Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))).restrictScalars
          Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)) :=
    isLocalizedModule_restrictScalars_powers (h i) _
  -- the two glued-piece localizations
  haveI hsec : IsLocalizedModule (Submonoid.powers (h i))
      (Scheme.QcohOn.secResₗ (F := D.sheaf) ((relCurve C B).basicOpen_le (h i))
        (le_refl ((fst C (overSpec k B)).left ⁻¹ᵁ V))) :=
    isLocalizedModule_secResₗ_glued B D.pieces D.unit hVaff D.isGluingCocycle hq hP i
  haveI hsec' : IsLocalizedModule (Submonoid.powers (termFamily B' V h i))
      (Scheme.QcohOn.secResₗ (F := (D.baseChange B').sheaf)
        ((relCurve C B').basicOpen_le (termFamily B' V h i))
        (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))) :=
    isLocalizedModule_secResₗ_glued B' (D.baseChange B').pieces (D.baseChange B').unit
      hVaff' (D.baseChange B').isGluingCocycle hq' (termFamily_le B' D V σ h hP) i
  haveI hsec'' : IsLocalizedModule (Submonoid.powers
      (algebraMap Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
        Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V) (h i)))
      (Scheme.QcohOn.secResₗ (F := (D.baseChange B').sheaf)
        ((relCurve C B').basicOpen_le (termFamily B' V h i))
        (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))) := hsec'
  haveI hsecA' : IsLocalizedModule (Submonoid.powers (h i))
      ((Scheme.QcohOn.secResₗ (F := (D.baseChange B').sheaf)
        ((relCurve C B').basicOpen_le (termFamily B' V h i))
        (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))).restrictScalars
          Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)) :=
    isLocalizedModule_restrictScalars_powers (h i) _
  -- the piece module structures and the piece trivializations, `A`-linearly
  letI : Module Γ(relCurve C B, (relCurve C B).basicOpen (h i))
      (D.sheaf.obj.obj (op ((relCurve C B).basicOpen (h i)))) :=
    gluedPieceModule B D.pieces D.unit D.isGluingCocycle hP i
  haveI : IsScalarTower Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B, (relCurve C B).basicOpen (h i))
      (D.sheaf.obj.obj (op ((relCurve C B).basicOpen (h i)))) :=
    isScalarTower_chart_piece B D.pieces D.unit D.isGluingCocycle hq hP i
  letI : Module Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))
      ((D.baseChange B').sheaf.obj.obj
        (op ((relCurve C B').basicOpen (termFamily B' V h i)))) :=
    gluedPieceModule B' (D.baseChange B').pieces (D.baseChange B').unit
      (D.baseChange B').isGluingCocycle (termFamily_le B' D V σ h hP) i
  haveI : IsScalarTower Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))
      ((D.baseChange B').sheaf.obj.obj
        (op ((relCurve C B').basicOpen (termFamily B' V h i)))) :=
    isScalarTower_chart_piece B' (D.baseChange B').pieces (D.baseChange B').unit
      (D.baseChange B').isGluingCocycle hq' (termFamily_le B' D V σ h hP) i
  haveI tAΓ'F' : IsScalarTower Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))
      ((D.baseChange B').sheaf.obj.obj
        (op ((relCurve C B').basicOpen (termFamily B' V h i)))) := by
    refine IsScalarTower.of_algebraMap_smul fun a x => ?_
    exact algebraMap_smul
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))
      (relSectionsMap C B B' V a) x
  letI : Module Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      ↥(gluedSubmodule B D.pieces D.unit ((relCurve C B).basicOpen (h i))) :=
    Scheme.QcohOn.moduleOfLE (F := D.sheaf) ((relCurve C B).basicOpen_le (h i))
  letI : Module Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
      ↥(gluedSubmodule B' (D.baseChange B').pieces (D.baseChange B').unit
        ((relCurve C B').basicOpen (termFamily B' V h i))) :=
    Scheme.QcohOn.moduleOfLE (F := (D.baseChange B').sheaf)
      ((relCurve C B').basicOpen_le (termFamily B' V h i))
  letI : Module Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      ↥(gluedSubmodule B' (D.baseChange B').pieces (D.baseChange B').unit
        ((relCurve C B').basicOpen (termFamily B' V h i))) :=
    Module.compHom _ (relSectionsMap C B B' V)
  letI : Module Γ(relCurve C B, (relCurve C B).basicOpen (h i))
      ↥(gluedSubmodule B D.pieces D.unit ((relCurve C B).basicOpen (h i))) :=
    gluedPieceModule B D.pieces D.unit D.isGluingCocycle hP i
  letI : Module Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))
      ↥(gluedSubmodule B' (D.baseChange B').pieces (D.baseChange B').unit
        ((relCurve C B').basicOpen (termFamily B' V h i))) :=
    gluedPieceModule B' (D.baseChange B').pieces (D.baseChange B').unit
      (D.baseChange B').isGluingCocycle (termFamily_le B' D V σ h hP) i
  haveI : IsScalarTower Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B, (relCurve C B).basicOpen (h i))
      ↥(gluedSubmodule B D.pieces D.unit ((relCurve C B).basicOpen (h i))) :=
    isScalarTower_chart_piece B D.pieces D.unit D.isGluingCocycle hq hP i
  haveI : IsScalarTower Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))
      ↥(gluedSubmodule B' (D.baseChange B').pieces (D.baseChange B').unit
        ((relCurve C B').basicOpen (termFamily B' V h i))) :=
    isScalarTower_chart_piece B' (D.baseChange B').pieces (D.baseChange B').unit
      (D.baseChange B').isGluingCocycle hq' (termFamily_le B' D V σ h hP) i
  haveI : IsScalarTower Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))
      ↥(gluedSubmodule B' (D.baseChange B').pieces (D.baseChange B').unit
        ((relCurve C B').basicOpen (termFamily B' V h i))) := by
    refine IsScalarTower.of_algebraMap_smul fun a x => ?_
    exact algebraMap_smul
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))
      (relSectionsMap C B B' V a) x
  let eB : (D.sheaf.obj.obj (op ((relCurve C B).basicOpen (h i))))
      ≃ₗ[Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)]
      Γ(relCurve C B, (relCurve C B).basicOpen (h i)) :=
    (gluedPieceEquiv B D.pieces D.unit D.isGluingCocycle hP
      i).restrictScalars Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
  let eB' : ((D.baseChange B').sheaf.obj.obj
      (op ((relCurve C B').basicOpen (termFamily B' V h i))))
      ≃ₗ[Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)]
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i)) :=
    (gluedPieceEquiv B' (D.baseChange B').pieces (D.baseChange B').unit
      (D.baseChange B').isGluingCocycle (termFamily_le B' D V σ h hP)
      i).restrictScalars Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
  -- the multiplication equivalence on the piece rings
  set ν : Γ(relCurve C B, (relCurve C B).basicOpen (h i)) ⊗[Γ(relCurve C B,
      (fst C (overSpec k B)).left ⁻¹ᵁ V)]
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i)) →ₗ[Γ(relCurve C B,
        (fst C (overSpec k B)).left ⁻¹ᵁ V)]
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i)) :=
    TensorProduct.lift ((LinearMap.mul Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))).comp
        ((IsScalarTower.toAlgHom Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
          Γ(relCurve C B, (relCurve C B).basicOpen (h i))
          Γ(relCurve C B', (relCurve C B').basicOpen
            (termFamily B' V h i))).toLinearMap)) with hνdef
  have hν : Function.Bijective ν := by
    haveI hid : IsLocalizedModule (Submonoid.powers (h i))
        (LinearMap.id (R := Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))
          (M := Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i)))) :=
      isLocalizedModule_id (Submonoid.powers (h i))
        Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))
        Γ(relCurve C B, (relCurve C B).basicOpen (h i))
    refine IsLocalizedModule.bijective_of_comp_eq (Submonoid.powers (h i))
      ((TensorProduct.mk Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
        Γ(relCurve C B, (relCurve C B).basicOpen (h i))
        Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))) 1)
      LinearMap.id ν ?_
    ext x'
    change ν ((1 : Γ(relCurve C B, (relCurve C B).basicOpen (h i))) ⊗ₜ x') = x'
    rw [hνdef]
    simp only [TensorProduct.lift.tmul, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, map_one, LinearMap.mul_apply', one_mul]
  -- the piece equivalence and the composite identification
  set eᵣ := (TensorProduct.congr (LinearEquiv.refl Γ(relCurve C B,
      (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))) eB).trans
    ((TensorProduct.comm Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)
      Γ(relCurve C B', (relCurve C B').basicOpen (termFamily B' V h i))
      Γ(relCurve C B, (relCurve C B).basicOpen (h i))).trans
        ((LinearEquiv.ofBijective ν hν).trans eB'.symm)) with heᵣdef
  have hσeq : ((Scheme.QcohOn.secResₗ (F := (D.baseChange B').sheaf)
        ((relCurve C B').basicOpen_le (termFamily B' V h i))
        (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V))).restrictScalars
          Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)) ∘ₗ
      ((LinearMap.liftBaseChange Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
        (sectionsMapₗ B' D V hq hq')).restrictScalars
          Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)) =
      eᵣ.toLinearMap ∘ₗ (TensorProduct.map
        ((Algebra.linearMap Γ(relCurve C B', (fst C (overSpec k B')).left ⁻¹ᵁ V)
          Γ(relCurve C B', (relCurve C B').basicOpen
            (termFamily B' V h i))).restrictScalars
              Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V))
        (Scheme.QcohOn.secResₗ (F := D.sheaf) ((relCurve C B).basicOpen_le (h i))
          (le_refl ((fst C (overSpec k B)).left ⁻¹ᵁ V)))) := by
    refine TensorProduct.ext' fun a' s => ?_
    -- left side: restrict the scaled comparison to the piece
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.restrictScalars_apply, LinearMap.liftBaseChange_tmul, map_smul,
      TensorProduct.map_tmul]
    -- right side: unfold the equivalence chain on the pure tensor
    rw [heᵣdef]
    rw [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
      TensorProduct.comm_tmul, LinearEquiv.ofBijective_apply, hνdef]
    rw [TensorProduct.lift.tmul, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      LinearMap.mul_apply']
    rw [LinearEquiv.eq_symm_apply]
    -- both sides, trivialized on the piece
    have hres : (Scheme.QcohOn.secResₗ (F := (D.baseChange B').sheaf)
        ((relCurve C B').basicOpen_le (termFamily B' V h i))
        (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V)))
        ((sectionsMapₗ B' D V hq hq') s) =
        D.sectionsMap B' (termFamily_basicOpen B' V h i).le
          (gluedRes B D.pieces D.unit ((relCurve C B).basicOpen_le (h i)) s) := by
      change gluedRes B' (D.baseChange B').pieces (D.baseChange B').unit
        ((relCurve C B').basicOpen_le (termFamily B' V h i))
        (D.sectionsMap B' (le_preimage_chart B' V) s) = _
      exact D.gluedRes_sectionsMap B' ((relCurve C B).basicOpen_le (h i))
        (le_preimage_chart B' V) (termFamily_basicOpen B' V h i).le
        ((relCurve C B').basicOpen_le (termFamily B' V h i)) s
    -- the `A'`-action of `a'` on the restricted section, trivialized
    have hsmul : (gluedPieceEquiv B' (D.baseChange B').pieces (D.baseChange B').unit
        (D.baseChange B').isGluingCocycle (termFamily_le B' D V σ h hP) i)
        (a' • (Scheme.QcohOn.secResₗ (F := (D.baseChange B').sheaf)
          ((relCurve C B').basicOpen_le (termFamily B' V h i))
          (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V)))
          ((sectionsMapₗ B' D V hq hq') s)) =
        (relCurve C B').resHom ((relCurve C B').basicOpen_le (termFamily B' V h i)) a' *
          gluedTriv B' (D.baseChange B').isGluingCocycle (σ i)
            (termFamily_le B' D V σ h hP i)
            ((Scheme.QcohOn.secResₗ (F := (D.baseChange B').sheaf)
              ((relCurve C B').basicOpen_le (termFamily B' V h i))
              (le_refl ((fst C (overSpec k B')).left ⁻¹ᵁ V)))
              ((sectionsMapₗ B' D V hq hq') s)) := by
      change gluedTriv B' (D.baseChange B').isGluingCocycle (σ i)
          (termFamily_le B' D V σ h hP i)
          (Scheme.QcohOn.qsmul (F := (D.baseChange B').sheaf)
            ((relCurve C B').basicOpen_le (termFamily B' V h i)) a' _) = _
      rw [hq' ((relCurve C B').basicOpen_le (termFamily B' V h i)) a' _]
      exact gluedTriv_gluedQsmul B' (D.baseChange B').pieces (D.baseChange B').unit
        (D.baseChange B').isGluingCocycle
        ((relCurve C B').basicOpen_le (termFamily B' V h i))
        (termFamily_le B' D V σ h hP i) a' _
    have heB' : ∀ z, eB' z = (gluedPieceEquiv B' (D.baseChange B').pieces
        (D.baseChange B').unit (D.baseChange B').isGluingCocycle
        (termFamily_le B' D V σ h hP) i) z := fun z => rfl
    rw [heB', hsmul, hres]
    -- trivialize the compared restricted section
    have htriv := D.gluedTriv_sectionsMap B' (termFamily_basicOpen B' V h i).le
      (hP i) (termFamily_le B' D V σ h hP i)
      (gluedRes B D.pieces D.unit ((relCurve C B).basicOpen_le (h i)) s)
    rw [htriv]
    rw [mul_comm]
    rfl
  rw [hσeq]
  exact IsLocalizedModule.of_linearEquiv _ _ _

end Piece

end BasicOpenCocycleDatum

end AlgebraicGeometry
