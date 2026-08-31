/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafExtraction
import AlgebraicJacobian.Cohomology.GluedSheafModule
import AlgebraicJacobian.Cohomology.GluedSheafClass
import AlgebraicJacobian.Algebra.LocalizationTrivialization
import AlgebraicJacobian.Descent.InvertibleModule

/-!
# Invertible sections of a cocycle-glued line bundle on an affine open

The cocycle pieces used to construct `gluedSheaf` need not contain an arbitrary affine
open.  Nevertheless, every affine open admits a finite basic-open refinement subordinate
to the canonical pointed cover by those pieces.  On each refined basic open the glued
sheaf is free of rank one.  The existing localization-span engine then proves that its
sections on the original affine open are finite projective.

`BasicOpenCocycleDatum.AffineSectionsModel` packages the quasi-coherent action chosen by
that internal refinement together with the finite, projective, and invertible instances.
Returning a `Nonempty` model keeps the refinement choice noncomputable while giving
downstream code a single datum from which it can install all four compatible instances.

This is the chart-free line-bundle substrate needed to restrict a positive theta twist to
the arbitrary affine pieces of `AffAdaptation`: the divisor cover is not required to lie in
either pinned theta chart.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {pi : C.left ⟶ P1 k} [IsAffineHom pi]

namespace BasicOpenCocycleDatum

/-- A compatible quasi-coherent module structure on the sections of a cocycle-glued
line bundle over an affine open, together with its finite projective rank-one properties.

The module instance is written explicitly in the fields so that it is definitionally the
one induced by `qcoh`; a consumer may install `M.qcoh` and recover `M.finite` and
`M.projective` without any proof-irrelevance transport. -/
structure AffineSectionsModel (D : BasicOpenCocycleDatum C B pi)
    (V : (relCurve C B).Opens) where
  qcoh : Scheme.QcohOn D.sheaf V
  qsmul_eq : ∀ {W : (relCurve C B).Opens} (hWV : W ≤ V) (r : Γ(relCurve C B, V))
      (s : D.sheaf.obj.obj (op W)),
      letI := qcoh
      Scheme.QcohOn.qsmul (F := D.sheaf) hWV r s =
        gluedQsmul B D.pieces D.unit hWV r s
  finite : @Module.Finite Γ(relCurve C B, V) (D.sheaf.obj.obj (op V))
    _ _ (@Scheme.QcohOn.moduleOfLE B _ (relCurve C B) V D.sheaf qcoh V (le_refl V))
  projective : @Module.Projective Γ(relCurve C B, V) _
    (D.sheaf.obj.obj (op V)) _
    (@Scheme.QcohOn.moduleOfLE B _ (relCurve C B) V D.sheaf qcoh V (le_refl V))
  invertible : @Module.Invertible Γ(relCurve C B, V) (D.sheaf.obj.obj (op V))
    _ _ (@Scheme.QcohOn.moduleOfLE B _ (relCurve C B) V D.sheaf qcoh V (le_refl V))

/-- Sections of a cocycle-glued line bundle on every affine open admit a compatible
invertible module model.  The proof chooses a finite basic-open refinement of the canonical
pointed cover, trivializes after the resulting faithfully flat product localization, and
descends invertibility; finiteness and projectivity are recorded on the same action. -/
theorem nonempty_affineSectionsModel (D : BasicOpenCocycleDatum C B pi)
    (V : (relCurve C B).Opens) (hV : IsAffineOpen V) :
    Nonempty (D.AffineSectionsModel V) := by
  classical
  obtain ⟨ι, fint, f, anchor, coeff, hP, hpart⟩ :=
    hV.exists_finite_basicOpen_refinement D.pointedCover
  letI : Fintype ι := fint
  let sigma : ι → D.index := fun i => D.pieceIndex (anchor i)
  have hP' : ∀ i : ι, (relCurve C B).basicOpen (f i) ≤ D.pieces (sigma i) := hP
  have hcov : V ≤ ⨆ i : ι, (relCurve C B).basicOpen (f i) :=
    le_iSup_basicOpen_of_sum_eq_one coeff f hpart
  let q : Scheme.QcohOn D.sheaf V :=
    gluedQcohOn B D.pieces D.unit D.isGluingCocycle hP' hcov
  letI : Scheme.QcohOn D.sheaf V := q
  let m : Module Γ(relCurve C B, V) (D.sheaf.obj.obj (op V)) :=
    Scheme.QcohOn.moduleOfLE (F := D.sheaf) (le_refl V)
  have hspan : Ideal.span (Set.range f) = ⊤ :=
    Ideal.span_range_eq_top_of_sum_eq_one coeff f hpart
  have hfin : @Module.Finite Γ(relCurve C B, V) (D.sheaf.obj.obj (op V)) _ _ m :=
    moduleFinite_glued B D.pieces D.unit hV D.isGluingCocycle
      (fun _ _ _ => rfl) hP' hspan
  have hproj : @Module.Projective Γ(relCurve C B, V) _
      (D.sheaf.obj.obj (op V)) _ m :=
    projective_glued B D.pieces D.unit hV D.isGluingCocycle
      (fun _ _ _ => rfl) hP' hspan
  letI pieceBaseModule : ∀ i : ι, Module Γ(relCurve C B, V)
      (D.sheaf.obj.obj (op ((relCurve C B).basicOpen (f i)))) := fun i =>
    Scheme.QcohOn.moduleOfLE (F := D.sheaf) ((relCurve C B).basicOpen_le (f i))
  letI pieceModule : ∀ i : ι,
      Module Γ(relCurve C B, (relCurve C B).basicOpen (f i))
        (D.sheaf.obj.obj (op ((relCurve C B).basicOpen (f i)))) := fun i =>
    gluedPieceModule B D.pieces D.unit D.isGluingCocycle hP' i
  letI pieceTower : ∀ i : ι, IsScalarTower Γ(relCurve C B, V)
      Γ(relCurve C B, (relCurve C B).basicOpen (f i))
      (D.sheaf.obj.obj (op ((relCurve C B).basicOpen (f i)))) := fun i =>
    isScalarTower_chart_piece B D.pieces D.unit D.isGluingCocycle
      (fun _ _ _ => rfl) hP' i
  letI pieceLocalization : ∀ i : ι, IsLocalization.Away (f i)
      Γ(relCurve C B, (relCurve C B).basicOpen (f i)) := fun i =>
    hV.isLocalization_basicOpen (f i)
  haveI pieceLocalized : ∀ i : ι, IsLocalizedModule (Submonoid.powers (f i))
      (Scheme.QcohOn.secResₗ (F := D.sheaf)
        ((relCurve C B).basicOpen_le (f i)) (le_refl V)) := fun i =>
    isLocalizedModule_secResₗ_glued B D.pieces D.unit hV D.isGluingCocycle
      (fun _ _ _ => rfl) hP' i
  let e (i : ι) :
      Γ(relCurve C B, (relCurve C B).basicOpen (f i)) ⊗[Γ(relCurve C B, V)]
          (D.sheaf.obj.obj (op V))
        ≃ₗ[Γ(relCurve C B, (relCurve C B).basicOpen (f i))]
          Γ(relCurve C B, (relCurve C B).basicOpen (f i)) :=
    (IsLocalizedModule.isBaseChange (Submonoid.powers (f i))
      Γ(relCurve C B, (relCurve C B).basicOpen (f i))
      (Scheme.QcohOn.secResₗ (F := D.sheaf)
        ((relCurve C B).basicOpen_le (f i)) (le_refl V))).equiv.trans
      (gluedPieceEquiv B D.pieces D.unit D.isGluingCocycle hP' i)
  letI : Module.FaithfullyFlat Γ(relCurve C B, V)
      (∀ i : ι, Γ(relCurve C B, (relCurve C B).basicOpen (f i))) :=
    Module.FaithfullyFlat.pi_of_span_eq_top f hspan
  let E := Module.piTrivialization e
  letI : Module.Invertible
      (∀ i : ι, Γ(relCurve C B, (relCurve C B).basicOpen (f i)))
      ((∀ i : ι, Γ(relCurve C B, (relCurve C B).basicOpen (f i))) ⊗[Γ(relCurve C B, V)]
        (D.sheaf.obj.obj (op V))) :=
    Module.Invertible.congr E.symm
  have hinv : @Module.Invertible Γ(relCurve C B, V) (D.sheaf.obj.obj (op V)) _ _ m :=
    Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat
      Γ(relCurve C B, V)
      (∀ i : ι, Γ(relCurve C B, (relCurve C B).basicOpen (f i)))
      (D.sheaf.obj.obj (op V))
  exact ⟨{
    qcoh := q
    qsmul_eq := fun _ _ _ => rfl
    finite := hfin
    projective := hproj
    invertible := hinv
  }⟩

end BasicOpenCocycleDatum

end AlgebraicGeometry
