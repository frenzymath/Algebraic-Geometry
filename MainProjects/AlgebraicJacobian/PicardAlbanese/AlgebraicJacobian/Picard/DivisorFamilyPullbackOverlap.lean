/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyPullback

/-!
# Base change of pieces and overlaps of the finite chart adaptation (DD-1 stage (c))

The index-level instantiations of the piece-level term identification
(`AlgebraicJacobian.Picard.DivisorFamilyPullback`) on the `Fin`-indexed cover data: the
pieces `D(h_j)` of the two pinned charts, and their pairwise overlaps
`D(h_i) ⊓ D(h_j)` — which are themselves basic opens of the (affine) chart overlaps,
via the **overlap generator** `ovlGen i j = res h_i · res h_j` (`basicOpen_ovlGen`).

* `AlgebraicGeometry.relResCongrAlg` — transport of relative-curve sections along an
  equality of opens, as an `R`-algebra equivalence.
* `FinCoverData.piecesMap`/`FinCoverData.ovlMap` — the scheme-level comparison maps on
  pieces and overlaps (`appLE` of `relCurveMap`), with the restriction compatibilities
  `ovlMap_resHom_left`/`ovlMap_resHom_right` (the inputs to the `δ`-naturality square).
* `FinCoverData.pieceQuotBaseChange` — base change of a piece quotient
  `R' ⊗ (Γ(D(h_j)) ⧸ (E)) ≃ₐ[R'] Γ(D(h'_j)) ⧸ (E')`, the index-level colength
  transport (casewise from `pieceQuotBaseChangeAlg`).
* `FinCoverData.ovlQuotBaseChange` — the **overlap linchpin**: the same transport on
  the piece overlaps, obtained by conjugating the generic transport at the overlap
  generator by the opens identifications `basicOpen_ovlGen`.

Both transports carry `1 ⊗ [s] ↦ [compared s]` (`…_one_tmul_mk`), which is all the
certificate transport consumes.
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
open Opposite TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## Transport of sections along equalities of opens -/

/-- `appLE` between pairwise equal opens, conjugated by the restrictions along the
equalities (the proof-irrelevant `subst` collapse). -/
lemma Scheme.Hom.appLE_resHom_of_eq {X Y : Scheme.{u}} (f : X.Hom Y) {U U' : Y.Opens}
    {W W' : X.Opens} (hU : U = U') (hW : W = W') (e : W ≤ f ⁻¹ᵁ U) (e' : W' ≤ f ⁻¹ᵁ U')
    (s : Γ(Y, U)) :
    (f.appLE U' W' e').hom (Y.resHom hU.ge s) = X.resHom hW.ge ((f.appLE U W e).hom s) := by
  subst hU hW
  simp only [Scheme.resHom_refl]

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable {π : C.left ⟶ P1 k} [IsAffineHom π]

/-- Transport of relative-curve sections along an equality of opens, as an `R`-algebra
equivalence (mutually inverse restrictions along the equality). -/
noncomputable def relResCongrAlg (C : Over (Spec (.of k))) (R : Type u) [CommRing R]
    [Algebra k R] {U V : (relCurve C R).Opens} (h : U = V) :
    Γ(relCurve C R, U) ≃ₐ[R] Γ(relCurve C R, V) :=
  AlgEquiv.ofAlgHom (relResAlgHom C R h.ge) (relResAlgHom C R h.le)
    (AlgHom.ext fun s => by
      have hres : (relCurve C R).resHom h.ge ((relCurve C R).resHom h.le s) = s := by
        rw [Scheme.resHom_resHom, Scheme.resHom_refl]
      exact hres)
    (AlgHom.ext fun s => by
      have hres : (relCurve C R).resHom h.le ((relCurve C R).resHom h.ge s) = s := by
        rw [Scheme.resHom_resHom, Scheme.resHom_refl]
      exact hres)

@[simp]
lemma relResCongrAlg_apply {U V : (relCurve C R).Opens} (h : U = V)
    (s : Γ(relCurve C R, U)) :
    relResCongrAlg C R h s = (relCurve C R).resHom h.ge s :=
  rfl

@[simp]
lemma relResCongrAlg_symm_apply {U V : (relCurve C R).Opens} (h : U = V)
    (s : Γ(relCurve C R, V)) :
    (relResCongrAlg C R h).symm s = (relCurve C R).resHom h.le s :=
  rfl

namespace FinCoverData

variable (D : FinCoverData C R π)

/-! ## Charts and generators, indexed -/

/-- The pinned chart of a piece index: chart 0 for `inl`, chart 1 for `inr` (an open of
the base curve `C.left`; the piece lives in its `fst`-preimage). -/
noncomputable def chart : D.index → C.left.Opens :=
  Sum.elim (fun _ => fiberChart₀ π) (fun _ => fiberChart₁ π)

/-- The generator of a piece, as a section of the base change of its pinned chart. -/
noncomputable def gen :
    ∀ j : D.index, Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ D.chart j)
  | .inl j => D.h₀ j
  | .inr j => D.h₁ j

lemma pieces_eq_basicOpen_gen (j : D.index) :
    D.pieces j = (relCurve C R).basicOpen (D.gen j) := by
  cases j <;> rfl

lemma pieces_le_preimage_chart (j : D.index) :
    D.pieces j ≤ (fst C (overSpec k R)).left ⁻¹ᵁ D.chart j := by
  rw [D.pieces_eq_basicOpen_gen j]
  exact (relCurve C R).basicOpen_le (D.gen j)

/-- The chart of the base-changed cover data is the chart (the index shapes agree). -/
lemma chart_baseChange (j : D.index) : (D.baseChange R').chart j = D.chart j := by
  cases j <;> rfl

/-- The generator of the base-changed cover data is the compared generator. -/
lemma gen_baseChange (j : D.index) :
    (D.baseChange R').gen j = relSectionsMap C R R' (D.chart j) (D.gen j) := by
  cases j <;> rfl

/-! ## The chart packet: affineness of charts and chart overlaps -/

lemma isAffineOpen_chart (j : D.index) : IsAffineOpen (D.chart j) := by
  cases j
  · exact (fiberTwoCover π).isAffineOpen₀
  · exact (fiberTwoCover π).isAffineOpen₁

lemma isAffineOpen_chart_inf (i j : D.index) : IsAffineOpen (D.chart i ⊓ D.chart j) := by
  cases i <;> cases j
  · change IsAffineOpen (fiberChart₀ π ⊓ fiberChart₀ π)
    rw [inf_idem]
    exact (fiberTwoCover π).isAffineOpen₀
  · exact (fiberTwoCover π).isAffineOpen_inf
  · change IsAffineOpen (fiberChart₁ π ⊓ fiberChart₀ π)
    rw [inf_comm]
    exact (fiberTwoCover π).isAffineOpen_inf
  · change IsAffineOpen (fiberChart₁ π ⊓ fiberChart₁ π)
    rw [inf_idem]
    exact (fiberTwoCover π).isAffineOpen₁

/-- The chart overlaps have affine base change over every test ring (preimage of an
affine open along the affine first projection). -/
lemma isAffineOpen_preimage_chart_inf (S : Type u) [CommRing S] [Algebra k S]
    (i j : D.index) :
    IsAffineOpen ((fst C (overSpec k S)).left ⁻¹ᵁ (D.chart i ⊓ D.chart j)) :=
  (D.isAffineOpen_chart_inf i j).preimage (fst C (overSpec k S)).left

/-! ## The indexed piece comparison and the piece-quotient transport -/

/-- The scheme-level piece comparison at an index: `appLE` of `relCurveMap` from the
piece to the base-changed piece. -/
noncomputable def piecesMap (j : D.index) :
    Γ(relCurve C R, D.pieces j) →+* Γ(relCurve C R', (D.baseChange R').pieces j) :=
  ((relCurveMap C R R').appLE (D.pieces j) ((D.baseChange R').pieces j)
    (D.baseChange_pieces_le_preimage R' j)).hom

lemma piecesMap_inl (j : Fin D.m₀) :
    D.piecesMap R' (Sum.inl j) = pieceSectionsMap R' (fiberChart₀ π) (D.h₀ j) := rfl

lemma piecesMap_inr (j : Fin D.m₁) :
    D.piecesMap R' (Sum.inr j) = pieceSectionsMap R' (fiberChart₁ π) (D.h₁ j) := rfl

/-- **Base change of a piece quotient** (the index-level colength transport): for a set
`E` of equations on the piece `D(h_j)`,
`R' ⊗[R] (Γ(D(h_j)) ⧸ (E)) ≃ₐ[R'] Γ(D(h'_j)) ⧸ (piecesMap '' E)` — casewise the generic
`pieceQuotBaseChangeAlg` at the pinned charts. -/
noncomputable def pieceQuotBaseChange :
    ∀ (j : D.index) (E : Set Γ(relCurve C R, D.pieces j)),
      R' ⊗[R] (Γ(relCurve C R, D.pieces j) ⧸ Ideal.span E) ≃ₐ[R']
        Γ(relCurve C R', (D.baseChange R').pieces j) ⧸
          Ideal.span (D.piecesMap R' j '' E)
  | .inl j, E =>
      pieceQuotBaseChangeAlg R' (fiberChart₀ π)
        (fiberTwoCover π).isAffineOpen₀.isCompact
        (fiberTwoCover π).isAffineOpen₀.isQuasiSeparated
        (relCover_isAffineOpen₀ C R (fiberTwoCover π))
        (relCover_isAffineOpen₀ C R' (fiberTwoCover π)) (D.h₀ j) E
  | .inr j, E =>
      pieceQuotBaseChangeAlg R' (fiberChart₁ π)
        (fiberTwoCover π).isAffineOpen₁.isCompact
        (fiberTwoCover π).isAffineOpen₁.isQuasiSeparated
        (relCover_isAffineOpen₁ C R (fiberTwoCover π))
        (relCover_isAffineOpen₁ C R' (fiberTwoCover π)) (D.h₁ j) E

/-- The piece-quotient transport on a pure tensor of a residue class:
`1 ⊗ [s] ↦ [piecesMap s]`. -/
lemma pieceQuotBaseChange_one_tmul_mk (j : D.index)
    (E : Set Γ(relCurve C R, D.pieces j)) (s : Γ(relCurve C R, D.pieces j)) :
    D.pieceQuotBaseChange R' j E ((1 : R') ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span E) s) =
      Ideal.Quotient.mk (Ideal.span (D.piecesMap R' j '' E)) (D.piecesMap R' j s) := by
  cases j with
  | inl j =>
      exact pieceQuotBaseChangeAlg_one_tmul_mk R' (fiberChart₀ π)
        (fiberTwoCover π).isAffineOpen₀.isCompact
        (fiberTwoCover π).isAffineOpen₀.isQuasiSeparated
        (relCover_isAffineOpen₀ C R (fiberTwoCover π))
        (relCover_isAffineOpen₀ C R' (fiberTwoCover π)) (D.h₀ j) E s
  | inr j =>
      exact pieceQuotBaseChangeAlg_one_tmul_mk R' (fiberChart₁ π)
        (fiberTwoCover π).isAffineOpen₁.isCompact
        (fiberTwoCover π).isAffineOpen₁.isQuasiSeparated
        (relCover_isAffineOpen₁ C R (fiberTwoCover π))
        (relCover_isAffineOpen₁ C R' (fiberTwoCover π)) (D.h₁ j) E s

/-! ## The overlap generator: piece overlaps are basic opens of the chart overlaps -/

/-- **The overlap generator**: the product of the two generators restricted to the
(affine) chart overlap. Its basic open is the piece overlap (`basicOpen_ovlGen`). -/
noncomputable def ovlGen (i j : D.index) :
    Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ (D.chart i ⊓ D.chart j)) :=
  (relCurve C R).resHom
      (Scheme.Hom.preimage_mono (fst C (overSpec k R)).left inf_le_left) (D.gen i) *
    (relCurve C R).resHom
      (Scheme.Hom.preimage_mono (fst C (overSpec k R)).left inf_le_right) (D.gen j)

/-- The basic open of the overlap generator is the piece overlap. -/
lemma basicOpen_ovlGen (i j : D.index) :
    (relCurve C R).basicOpen (D.ovlGen i j) = D.pieces i ⊓ D.pieces j := by
  have hij : D.pieces i ⊓ D.pieces j ≤
      (fst C (overSpec k R)).left ⁻¹ᵁ (D.chart i ⊓ D.chart j) := by
    rw [Scheme.Hom.preimage_inf]
    exact inf_le_inf (D.pieces_le_preimage_chart i) (D.pieces_le_preimage_chart j)
  rw [ovlGen, Scheme.basicOpen_mul, Scheme.basicOpen_resHom, Scheme.basicOpen_resHom,
    ← D.pieces_eq_basicOpen_gen i, ← D.pieces_eq_basicOpen_gen j]
  refine le_antisymm (inf_le_inf inf_le_right inf_le_right)
    (le_inf (le_inf hij inf_le_left) (le_inf hij inf_le_right))

/-- The overlap generator of the base-changed cover data is the compared overlap
generator. -/
lemma ovlGen_baseChange (i j : D.index) :
    relSectionsMap C R R' (D.chart i ⊓ D.chart j) (D.ovlGen i j) =
      (D.baseChange R').ovlGen i j := by
  rw [ovlGen, map_mul, ovlGen, gen_baseChange, gen_baseChange]
  congr 1
  · exact relSectionsMap_resHom C R R'
      (inf_le_left : D.chart i ⊓ D.chart j ≤ D.chart i) (D.gen i)
  · exact relSectionsMap_resHom C R R'
      (inf_le_right : D.chart i ⊓ D.chart j ≤ D.chart j) (D.gen j)

/-- The basic open of the compared overlap generator is the overlap of the base-changed
pieces. -/
lemma basicOpen_relSectionsMap_ovlGen (i j : D.index) :
    (relCurve C R').basicOpen
        (relSectionsMap C R R' (D.chart i ⊓ D.chart j) (D.ovlGen i j)) =
      (D.baseChange R').pieces i ⊓ (D.baseChange R').pieces j := by
  rw [D.ovlGen_baseChange R' i j]
  exact (D.baseChange R').basicOpen_ovlGen i j

/-! ## The indexed overlap comparison -/

/-- The scheme-level overlap comparison at a pair of indices: `appLE` of `relCurveMap`
from the piece overlap to the base-changed piece overlap. -/
noncomputable def ovlMap (i j : D.index) :
    Γ(relCurve C R, D.pieces i ⊓ D.pieces j) →+*
      Γ(relCurve C R', (D.baseChange R').pieces i ⊓ (D.baseChange R').pieces j) :=
  ((relCurveMap C R R').appLE (D.pieces i ⊓ D.pieces j)
    ((D.baseChange R').pieces i ⊓ (D.baseChange R').pieces j)
    (D.baseChange_inf_le_preimage R' i j)).hom

/-- The overlap comparison restricted from the left piece: comparing then restricting
equals restricting then comparing (`Scheme.Hom.appLE_resHom`). -/
lemma ovlMap_resHom_left (i j : D.index) (s : Γ(relCurve C R, D.pieces i)) :
    D.ovlMap R' i j ((relCurve C R).resHom inf_le_left s) =
      (relCurve C R').resHom inf_le_left (D.piecesMap R' i s) :=
  ((relCurveMap C R R').appLE_resHom inf_le_left
    (D.baseChange_pieces_le_preimage R' i) (D.baseChange_inf_le_preimage R' i j)
    inf_le_left s).symm

/-- The overlap comparison restricted from the right piece. -/
lemma ovlMap_resHom_right (i j : D.index) (s : Γ(relCurve C R, D.pieces j)) :
    D.ovlMap R' i j ((relCurve C R).resHom inf_le_right s) =
      (relCurve C R').resHom inf_le_right (D.piecesMap R' j s) :=
  ((relCurveMap C R R').appLE_resHom inf_le_right
    (D.baseChange_pieces_le_preimage R' j) (D.baseChange_inf_le_preimage R' i j)
    inf_le_right s).symm

/-- The overlap comparison is the generic piece-sections comparison at the overlap
generator, conjugated by the opens identifications `basicOpen_ovlGen` (the
proof-irrelevant `appLE` collapse `Scheme.Hom.appLE_resHom_of_eq`). -/
lemma ovlMap_eq_conj (i j : D.index) (s : Γ(relCurve C R, D.pieces i ⊓ D.pieces j)) :
    D.ovlMap R' i j s =
      relResCongrAlg C R' (D.basicOpen_relSectionsMap_ovlGen R' i j)
        (pieceSectionsMap R' (D.chart i ⊓ D.chart j) (D.ovlGen i j)
          ((relResCongrAlg C R (D.basicOpen_ovlGen i j)).symm s)) := by
  have key := (relCurveMap C R R').appLE_resHom_of_eq
    (D.basicOpen_ovlGen i j).symm (D.basicOpen_relSectionsMap_ovlGen R' i j).symm
    (D.baseChange_inf_le_preimage R' i j)
    (relSectionsMap_basicOpen C R R' (D.chart i ⊓ D.chart j) (D.ovlGen i j)).le s
  -- `key : pieceSectionsMap (res s) = res (ovlMap s)`; apply the forward restriction
  have happ := congrArg
    ((relCurve C R').resHom (D.basicOpen_relSectionsMap_ovlGen R' i j).ge) key
  rw [Scheme.resHom_resHom, Scheme.resHom_refl] at happ
  rw [relResCongrAlg_apply, relResCongrAlg_symm_apply]
  exact happ.symm

/-! ## The overlap-section transport -/

/-- Base change of an overlap section ring, obtained by conjugating the generic
basic-open transport with the identifications of the overlap as `D(ovlGen)`. -/
noncomputable def ovlTermBaseChange (i j : D.index) :
    R' ⊗[R] Γ(relCurve C R, D.pieces i ⊓ D.pieces j) ≃ₐ[R']
      Γ(relCurve C R', (D.baseChange R').pieces i ⊓ (D.baseChange R').pieces j) :=
  (Algebra.TensorProduct.congr AlgEquiv.refl
    (relResCongrAlg C R (D.basicOpen_ovlGen i j)).symm).trans
  ((pieceTermBaseChangeAlg R' (D.chart i ⊓ D.chart j)
      (D.isAffineOpen_chart_inf i j).isCompact
      (D.isAffineOpen_chart_inf i j).isQuasiSeparated
      (D.isAffineOpen_preimage_chart_inf R i j)
      (D.isAffineOpen_preimage_chart_inf R' i j)
      (D.ovlGen i j)).trans
    (relResCongrAlg C R' (D.basicOpen_relSectionsMap_ovlGen R' i j)))

/-- The overlap-section transport sends `1 ⊗ s` to the indexed overlap comparison of
`s`. -/
lemma ovlTermBaseChange_one_tmul (i j : D.index)
    (s : Γ(relCurve C R, D.pieces i ⊓ D.pieces j)) :
    D.ovlTermBaseChange R' i j ((1 : R') ⊗ₜ[R] s) = D.ovlMap R' i j s := by
  change relResCongrAlg C R' (D.basicOpen_relSectionsMap_ovlGen R' i j)
      (pieceTermBaseChangeAlg R' (D.chart i ⊓ D.chart j)
        (D.isAffineOpen_chart_inf i j).isCompact
        (D.isAffineOpen_chart_inf i j).isQuasiSeparated
        (D.isAffineOpen_preimage_chart_inf R i j)
        (D.isAffineOpen_preimage_chart_inf R' i j)
        (D.ovlGen i j)
        ((1 : R') ⊗ₜ[R]
          (relResCongrAlg C R (D.basicOpen_ovlGen i j)).symm s)) = _
  rw [pieceTermBaseChangeAlg_one_tmul]
  exact (D.ovlMap_eq_conj R' i j s).symm

/-! ## The overlap-quotient transport (the overlap linchpin) -/

/-- **The overlap linchpin** (`informal/spec-dd-1.md` §3 stage (c), overlap row): base
change of an overlap quotient,
`R' ⊗[R] (Γ(D(h_i) ⊓ D(h_j)) ⧸ (E)) ≃ₐ[R'] Γ(D(h'_i) ⊓ D(h'_j)) ⧸ (ovlMap '' E)` —
the generic transport at the overlap generator of the affine chart overlap, conjugated
by the opens identifications `basicOpen_ovlGen`. -/
noncomputable def ovlQuotBaseChange (i j : D.index)
    (E : Set Γ(relCurve C R, D.pieces i ⊓ D.pieces j)) :
    R' ⊗[R] (Γ(relCurve C R, D.pieces i ⊓ D.pieces j) ⧸ Ideal.span E) ≃ₐ[R']
      Γ(relCurve C R', (D.baseChange R').pieces i ⊓ (D.baseChange R').pieces j) ⧸
        Ideal.span (D.ovlMap R' i j '' E) :=
  (Algebra.TensorProduct.congr AlgEquiv.refl
    (Ideal.quotientEquivAlg (Ideal.span E)
      (Ideal.span ((relResCongrAlg C R (D.basicOpen_ovlGen i j)).symm '' E))
      (relResCongrAlg C R (D.basicOpen_ovlGen i j)).symm
      (Ideal.map_span _ E).symm)).trans
  ((pieceQuotBaseChangeAlg R' (D.chart i ⊓ D.chart j)
      (D.isAffineOpen_chart_inf i j).isCompact
      (D.isAffineOpen_chart_inf i j).isQuasiSeparated
      (D.isAffineOpen_preimage_chart_inf R i j)
      (D.isAffineOpen_preimage_chart_inf R' i j)
      (D.ovlGen i j)
      ((relResCongrAlg C R (D.basicOpen_ovlGen i j)).symm '' E)).trans
    (Ideal.quotientEquivAlg _ (Ideal.span (D.ovlMap R' i j '' E))
      (relResCongrAlg C R' (D.basicOpen_relSectionsMap_ovlGen R' i j))
      (by
        rw [Ideal.map_span, ← Set.image_comp, ← Set.image_comp]
        exact congrArg Ideal.span
          (Set.image_congr fun s _ => D.ovlMap_eq_conj R' i j s))))

/-- The overlap-quotient transport on a pure tensor of a residue class:
`1 ⊗ [s] ↦ [ovlMap s]`. -/
lemma ovlQuotBaseChange_one_tmul_mk (i j : D.index)
    (E : Set Γ(relCurve C R, D.pieces i ⊓ D.pieces j))
    (s : Γ(relCurve C R, D.pieces i ⊓ D.pieces j)) :
    D.ovlQuotBaseChange R' i j E ((1 : R') ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span E) s) =
      Ideal.Quotient.mk (Ideal.span (D.ovlMap R' i j '' E)) (D.ovlMap R' i j s) := by
  have h1 : D.ovlQuotBaseChange R' i j E
      ((1 : R') ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span E) s) =
      Ideal.Quotient.mk (Ideal.span (D.ovlMap R' i j '' E))
        (relResCongrAlg C R' (D.basicOpen_relSectionsMap_ovlGen R' i j)
          (pieceTermBaseChangeAlg R' (D.chart i ⊓ D.chart j)
            (D.isAffineOpen_chart_inf i j).isCompact
            (D.isAffineOpen_chart_inf i j).isQuasiSeparated
            (D.isAffineOpen_preimage_chart_inf R i j)
            (D.isAffineOpen_preimage_chart_inf R' i j)
            (D.ovlGen i j)
            ((1 : R') ⊗ₜ[R]
              (relResCongrAlg C R (D.basicOpen_ovlGen i j)).symm s))) := rfl
  rw [h1, pieceTermBaseChangeAlg_one_tmul]
  exact congrArg (Ideal.Quotient.mk _) (D.ovlMap_eq_conj R' i j s).symm

end FinCoverData

end AlgebraicGeometry
