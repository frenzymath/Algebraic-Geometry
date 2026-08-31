/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamily
import AlgebraicJacobian.Picard.FlatCokernel
import AlgebraicJacobian.Cohomology.GluedSheafDatumBaseChange
import AlgebraicJacobian.Cohomology.RelativeH1BaseChange

/-!
# Base change of certified divisor families (the DD-1 stage (c) pullback,
`informal/spec-dd-1.md` §3 stage (c))

Along a test-ring change `R → R'` (a `k`-algebra map, packaged as `[Algebra R R']`
`[IsScalarTower k R R']`), a certified divisor family over `R` pulls back to one over
`R'` through the relative-curve comparison morphism `relCurveMap C R R'`. This file builds
the geometric half of that pullback — the cover data and adaptation push forward through
the sections comparison `relSectionsMap` (`Scheme.Hom.appLE`), pieces to pieces
(`relSectionsMap_basicOpen`), partitions by `map_sum`/`map_mul`/`map_one` — and prepares
the certificate transport that turns it into `DivFam.mapAlg` — which is LANDED in
`AlgebraicJacobian.Picard.DivisorFamilyMapAlg` (this file remains its geometric feeder).

* `AlgebraicGeometry.FinCoverData.baseChange` — the `Fin`-indexed cover data pushes
  forward: generators/partition coefficients go through `relSectionsMap`, the partition
  witnesses by ring-hom functoriality (the `Fin`-indexed mirror of
  `BasicOpenCoverData.baseChange`).
* `AlgebraicGeometry.FinCoverData.pieces_baseChange` — pieces base-change to pieces
  (`relSectionsMap_basicOpen`): `(D.baseChange R').pieces j = relCurveMap ⁻¹ᵁ D.pieces j`.

The module structures are the local instances of the DD-1 carrier (`Scheme.overModule`,
`Scheme.overSectionsAlgebra`, house rule); the mixed `relCurve`/product spellings force
`backward.isDefEq.respectTransparency false`, as in `RelativeSectionsLinear`.
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

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable {π : C.left ⟶ P1 k} [IsAffineHom π]

/-! ## The cover data base change -/

namespace FinCoverData

variable (D : FinCoverData C R π)

/-- **Base change of the `Fin`-indexed cover data** along `R → R'`: the generators and
partition coefficients push forward through the sections comparison `relSectionsMap`; the
partition witnesses are carried by `map_sum`/`map_mul`/`map_one` (the `Fin`-indexed mirror
of `BasicOpenCoverData.baseChange`). -/
noncomputable def baseChange : FinCoverData C R' π where
  m₀ := D.m₀
  m₁ := D.m₁
  h₀ j := relSectionsMap C R R' (fiberChart₀ π) (D.h₀ j)
  h₁ j := relSectionsMap C R R' (fiberChart₁ π) (D.h₁ j)
  a₀ j := relSectionsMap C R R' (fiberChart₀ π) (D.a₀ j)
  a₁ j := relSectionsMap C R R' (fiberChart₁ π) (D.a₁ j)
  partition₀ := by
    have h := congrArg (relSectionsMap C R R' (fiberChart₀ π)) D.partition₀
    rw [map_sum, map_one] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => (map_mul _ _ _).symm
  partition₁ := by
    have h := congrArg (relSectionsMap C R R' (fiberChart₁ π)) D.partition₁
    rw [map_sum, map_one] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => (map_mul _ _ _).symm

@[simp]
lemma baseChange_h₀ (j : Fin D.m₀) :
    (D.baseChange R').h₀ j = relSectionsMap C R R' (fiberChart₀ π) (D.h₀ j) := rfl

@[simp]
lemma baseChange_h₁ (j : Fin D.m₁) :
    (D.baseChange R').h₁ j = relSectionsMap C R R' (fiberChart₁ π) (D.h₁ j) := rfl

/-- **Pieces base-change to pieces**: the pieces of the base-changed cover data are the
`relCurveMap`-preimages of the pieces (`relSectionsMap_basicOpen`). -/
theorem pieces_baseChange (j : D.index) :
    (D.baseChange R').pieces j = relCurveMap C R R' ⁻¹ᵁ D.pieces j := by
  cases j with
  | inl j => exact relSectionsMap_basicOpen C R R' (fiberChart₀ π) (D.h₀ j)
  | inr j => exact relSectionsMap_basicOpen C R R' (fiberChart₁ π) (D.h₁ j)

/-- The base-changed pieces are below the preimages of the pieces (the `≤`-form of
`pieces_baseChange` consumed by `appLE`). -/
lemma baseChange_pieces_le_preimage (j : D.index) :
    (D.baseChange R').pieces j ≤ relCurveMap C R R' ⁻¹ᵁ D.pieces j :=
  (D.pieces_baseChange R' j).le

/-- Double overlaps of base-changed pieces are below the preimages of the double
overlaps. -/
lemma baseChange_inf_le_preimage (i j : D.index) :
    (D.baseChange R').pieces i ⊓ (D.baseChange R').pieces j ≤
      relCurveMap C R R' ⁻¹ᵁ (D.pieces i ⊓ D.pieces j) := by
  rw [Scheme.Hom.preimage_inf]
  exact inf_le_inf (D.baseChange_pieces_le_preimage R' i)
    (D.baseChange_pieces_le_preimage R' j)

end FinCoverData

/-! ## The chart-ring base change, as an algebra equivalence

`relTermBaseChange` is the `R'`-linear base change of chart sections; on the chart charts
it is in fact multiplicative (the underlying map `r' ⊗ y ↦ r' • relSectionsMap y` is a
ring homomorphism because `relSectionsMap` is), so it promotes to an `R'`-algebra
equivalence. This is the ring-level input to the piece-level term identification (the
away-localization base change of `IsLocalization.Away.tensorProductEquivTMulRight`). -/

/-- **The chart-ring base change**, as an `R'`-algebra equivalence
`R' ⊗[R] Γ(C_R, V_R) ≃ₐ[R'] Γ(C_{R'}, V_{R'})`: the promotion of the `R'`-linear
`relTermBaseChange` (multiplicative because `relSectionsMap` is a ring homomorphism). -/
noncomputable def relTermBaseChangeAlg (V : C.left.Opens)
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left)) :
    R' ⊗[R] Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V) ≃ₐ[R']
      Γ(relCurve C R', (fst C (overSpec k R')).left ⁻¹ᵁ V) :=
  AlgEquiv.ofLinearEquiv (relTermBaseChange C R R' V hV hV')
    (by
      rw [Algebra.TensorProduct.one_def, relTermBaseChange_tmul, one_smul, map_one])
    (by
      intro x y
      induction x with
      | zero => rw [zero_mul, map_zero, zero_mul]
      | add x₁ x₂ hx₁ hx₂ => rw [add_mul, map_add, hx₁, hx₂, map_add, add_mul]
      | tmul a s =>
        induction y with
        | zero => rw [mul_zero, map_zero, mul_zero]
        | add y₁ y₂ hy₁ hy₂ => rw [mul_add, map_add, hy₁, hy₂, map_add, mul_add]
        | tmul b t =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, relTermBaseChange_tmul,
            relTermBaseChange_tmul, relTermBaseChange_tmul, map_mul, smul_mul_smul_comm])

@[simp]
lemma relTermBaseChangeAlg_tmul (V : C.left.Opens)
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
    (r' : R') (y : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)) :
    relTermBaseChangeAlg (R := R) R' V hV hV' (r' ⊗ₜ y) = r' • relSectionsMap C R R' V y :=
  relTermBaseChange_tmul C R R' hV hV' r' y

/-! ## The piece-level term identification (the certificate linchpin)

For a section `h` of an affine chart `V_R`, the piece `D(h)` sections are the away
localization of `Γ(V_R)` at `h`; base change commutes with this localization, so
`R' ⊗[R] Γ(D(h)) ≃ₐ[R'] Γ(D(h'))` where `h' = relSectionsMap h`. This is the
`IsLocalization.Away.tensorProductEquivTMulRight` base change transported along the
chart-ring iso `relTermBaseChangeAlg`. -/

section Piece

variable (V : C.left.Opens)
variable (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
variable (hVaff : IsAffineOpen ((fst C (overSpec k R)).left ⁻¹ᵁ V))
variable (hVaff' : IsAffineOpen ((fst C (overSpec k R')).left ⁻¹ᵁ V))
variable (h : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V))

/-- The `R`-to-piece scalar tower: the structure map `R → Γ(D(h))` factors through the
chart ring `Γ(V_R)`. -/
lemma isScalarTower_R_chart_piece :
    IsScalarTower R Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)
      Γ(relCurve C R, (relCurve C R).basicOpen h) := by
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  rw [Scheme.algebraMap_overSectionsAlgebra, Scheme.algebraMap_overSectionsAlgebra]
  exact ((relCurve C R).overAlgebraMap_apply_res R
    (homOfLE ((relCurve C R).basicOpen_le h)).op r).symm

/-- (Implementation) The `R' ⊗[R] Γ(V_R)`-algebra structure on the base-changed piece
sections `Γ(D(h'))`, `h' = relSectionsMap h`: scalars act through the chart-ring iso
`relTermBaseChangeAlg` followed by restriction to the piece. Named (rather than a `letI`
inside `pieceTermBaseChangeAlg`) so that the computation rule
`pieceTermBaseChangeAlg_one_tmul` can re-enter the same instance context. -/
@[reducible]
noncomputable def pieceTensorChartAlgebra :
    Algebra (R' ⊗[R] Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V))
      Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h)) :=
  ((algebraMap Γ(relCurve C R', (fst C (overSpec k R')).left ⁻¹ᵁ V)
    Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h))).comp
      (relTermBaseChangeAlg (C := C) (R := R) R' V hV hV').toAlgHom.toRingHom).toAlgebra

/-- **The piece-level term identification** (the certificate linchpin,
`informal/spec-dd-1.md` §3 stage (c), "localization commutes with base change at the
pieces"): base change of the piece sections `Γ(D(h))` is the piece sections of the
base-changed generator, `R' ⊗[R] Γ(D(h)) ≃ₐ[R'] Γ(D(h'))` with `h' = relSectionsMap h`.
Assembled from the away-localization base change
`IsLocalization.Away.tensorProductEquivTMulRight` (source is `Away (1 ⊗ h)` over
`R' ⊗[R] Γ(V_R)`) transported along the chart-ring iso `relTermBaseChangeAlg`
(sending `1 ⊗ h ↦ h'`), which exhibits `Γ(D(h'))` as the same away localization. -/
noncomputable def pieceTermBaseChangeAlg :
    R' ⊗[R] Γ(relCurve C R, (relCurve C R).basicOpen h) ≃ₐ[R']
      Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h)) := by
  haveI := isScalarTower_R_chart_piece (R := R) V h
  haveI hLoc : IsLocalization.Away h Γ(relCurve C R, (relCurve C R).basicOpen h) :=
    hVaff.isLocalization_basicOpen h
  haveI hLoc' : IsLocalization.Away (relSectionsMap C R R' V h)
      Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h)) :=
    hVaff'.isLocalization_basicOpen (relSectionsMap C R R' V h)
  -- the base-ring iso, and the fact that it carries `1 ⊗ h` to `h'`
  set e := relTermBaseChangeAlg (C := C) (R := R) R' V hV hV' with he
  have heh : e ((1 : R') ⊗ₜ[R] h) = relSectionsMap C R R' V h := by
    rw [he, relTermBaseChangeAlg_tmul, one_smul]
  -- exhibit `Γ(D(h'))` as the away localization of `R' ⊗[R] Γ(V_R)` at `1 ⊗ h`
  letI algPK : Algebra (R' ⊗[R] Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V))
      Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h)) :=
    pieceTensorChartAlgebra R' V hV hV' h
  haveI hLocPK : IsLocalization.Away ((1 : R') ⊗ₜ[R] h)
      Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h)) := by
    refine IsLocalization.of_ringEquiv_left e.toRingEquiv
      (M₂ := Submonoid.powers ((1 : R') ⊗ₜ[R] h))
      ?_ (fun x => rfl) (M₁ := Submonoid.powers (relSectionsMap C R R' V h))
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers heh
  -- the `R'`-scalar towers for `restrictScalars`
  haveI tR' : IsScalarTower R' Γ(relCurve C R', (fst C (overSpec k R')).left ⁻¹ᵁ V)
      Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h)) :=
    isScalarTower_R_chart_piece (R := R') V (relSectionsMap C R R' V h)
  haveI : IsScalarTower R' (R' ⊗[R] Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V))
      Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h)) := by
    refine IsScalarTower.of_algebraMap_eq fun r' => ?_
    change _ = algebraMap Γ(relCurve C R', (fst C (overSpec k R')).left ⁻¹ᵁ V) _
      (e (algebraMap R' _ r'))
    rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  -- the two localizations of `R' ⊗[R] Γ(V_R)` at `1 ⊗ h` are algebra-equivalent
  exact (IsLocalization.Away.tensorProductEquivTMulRight R R' h
    Γ(relCurve C R, (relCurve C R).basicOpen h)).trans
    ((IsLocalization.algEquiv (Submonoid.powers ((1 : R') ⊗ₜ[R] h))
      (Localization.Away ((1 : R') ⊗ₜ[R] h))
      Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h))).restrictScalars R')

/-! ## Naturality of the piece-level term identification -/

/-- The scheme-level piece-sections comparison along `R → R'`: `appLE` of the
relative-curve comparison from the piece `D(h)` to the base-changed piece `D(h')`,
`h' = relSectionsMap h` (the inclusion is `relSectionsMap_basicOpen`). This is the map
the piece-level term identification computes on `1 ⊗ s`
(`pieceTermBaseChangeAlg_one_tmul`). -/
noncomputable def pieceSectionsMap :
    Γ(relCurve C R, (relCurve C R).basicOpen h) →+*
      Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h)) :=
  ((relCurveMap C R R').appLE ((relCurve C R).basicOpen h)
    ((relCurve C R').basicOpen (relSectionsMap C R R' V h))
    (relSectionsMap_basicOpen C R R' V h).le).hom

/-- The piece-sections comparison restricted along the chart algebra maps is the chart
comparison: `pieceSectionsMap (algebraMap a) = algebraMap (relSectionsMap a)` (both
algebra maps are the chart-to-piece restrictions; `Scheme.Hom.appLE_resHom`). -/
lemma pieceSectionsMap_algebraMap (a : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)) :
    pieceSectionsMap R' V h
        (algebraMap Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)
          Γ(relCurve C R, (relCurve C R).basicOpen h) a) =
      algebraMap Γ(relCurve C R', (fst C (overSpec k R')).left ⁻¹ᵁ V)
        Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h))
        (relSectionsMap C R R' V a) :=
  ((relCurveMap C R R').appLE_resHom
    ((relCurve C R).basicOpen_le h)
    (le_of_eq (relCurveMap_preimage C R R' V).symm)
    (relSectionsMap_basicOpen C R R' V h).le
    ((relCurve C R').basicOpen_le (relSectionsMap C R R' V h)) a).symm

set_option maxHeartbeats 800000 in
-- The mixed-spelling defeq checks through `relCurve`/product spellings are heavy, as in
-- `relTermBaseChange_tmul`.
/-- **Naturality of the piece-level term identification**: on `1 ⊗ s` the linchpin
`pieceTermBaseChangeAlg` is the scheme-level piece-sections comparison
`pieceSectionsMap` (`appLE` of `relCurveMap` between the pieces). Both sides are ring
homomorphisms out of the away localization `Γ(D(h))`, so it suffices to compare them on
the chart ring (`IsLocalization.ringHom_ext`), where both are
`algebraMap ∘ relSectionsMap` (`tensorProductEquivTMulRight_tmul` + `AlgEquiv.commutes`
on the left, `Scheme.Hom.appLE_resHom` on the right). -/
theorem pieceTermBaseChangeAlg_one_tmul
    (s : Γ(relCurve C R, (relCurve C R).basicOpen h)) :
    pieceTermBaseChangeAlg R' V hV hV' hVaff hVaff' h ((1 : R') ⊗ₜ[R] s) =
      pieceSectionsMap R' V h s := by
  haveI := isScalarTower_R_chart_piece (R := R) V h
  haveI hLoc : IsLocalization.Away h Γ(relCurve C R, (relCurve C R).basicOpen h) :=
    hVaff.isLocalization_basicOpen h
  haveI hLoc' : IsLocalization.Away (relSectionsMap C R R' V h)
      Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h)) :=
    hVaff'.isLocalization_basicOpen (relSectionsMap C R R' V h)
  -- re-enter the instance context of the linchpin definition
  have heh : relTermBaseChangeAlg (C := C) (R := R) R' V hV hV' ((1 : R') ⊗ₜ[R] h)
      = relSectionsMap C R R' V h := by
    rw [relTermBaseChangeAlg_tmul, one_smul]
  letI algPK : Algebra (R' ⊗[R] Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V))
      Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h)) :=
    pieceTensorChartAlgebra R' V hV hV' h
  haveI hLocPK : IsLocalization.Away ((1 : R') ⊗ₜ[R] h)
      Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h)) := by
    refine IsLocalization.of_ringEquiv_left
      (relTermBaseChangeAlg (C := C) (R := R) R' V hV hV').toRingEquiv
      (M₂ := Submonoid.powers ((1 : R') ⊗ₜ[R] h))
      ?_ (fun x => rfl) (M₁ := Submonoid.powers (relSectionsMap C R R' V h))
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers heh
  have key : ((pieceTermBaseChangeAlg R' V hV hV' hVaff hVaff' h).toAlgHom.toRingHom).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := R')
        (B := Γ(relCurve C R, (relCurve C R).basicOpen h))).toRingHom
      = pieceSectionsMap R' V h := by
    refine IsLocalization.ringHom_ext (Submonoid.powers h) (RingHom.ext fun a => ?_)
    -- unfold the linchpin on the pure tensor `1 ⊗ (algebraMap a)`
    have h1 : pieceTermBaseChangeAlg R' V hV hV' hVaff hVaff' h
        ((1 : R') ⊗ₜ[R] (algebraMap Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)
          Γ(relCurve C R, (relCurve C R).basicOpen h) a)) =
        (IsLocalization.algEquiv (Submonoid.powers ((1 : R') ⊗ₜ[R] h))
          (Localization.Away ((1 : R') ⊗ₜ[R] h))
          Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h)))
        (IsLocalization.Away.tensorProductEquivTMulRight R R' h
          Γ(relCurve C R, (relCurve C R).basicOpen h)
          ((1 : R') ⊗ₜ[R] (algebraMap Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)
            Γ(relCurve C R, (relCurve C R).basicOpen h) a))) := rfl
    have h2 : (IsLocalization.Away.tensorProductEquivTMulRight R R' h
        Γ(relCurve C R, (relCurve C R).basicOpen h))
        ((1 : R') ⊗ₜ[R] (algebraMap Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)
          Γ(relCurve C R, (relCurve C R).basicOpen h) a)) =
        algebraMap (R' ⊗[R] Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V))
          (Localization.Away ((1 : R') ⊗ₜ[R] h)) ((1 : R') ⊗ₜ[R] a) :=
      IsLocalization.Away.tensorProductEquivTMulRight_tmul (R := R) (S := R')
        Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V) h
        Γ(relCurve C R, (relCurve C R).basicOpen h) 1 a
    have h3 : (IsLocalization.algEquiv (Submonoid.powers ((1 : R') ⊗ₜ[R] h))
        (Localization.Away ((1 : R') ⊗ₜ[R] h))
        Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h)))
        (algebraMap (R' ⊗[R] Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V))
          (Localization.Away ((1 : R') ⊗ₜ[R] h)) ((1 : R') ⊗ₜ[R] a)) =
        algebraMap (R' ⊗[R] Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V))
          Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h))
          ((1 : R') ⊗ₜ[R] a) :=
      AlgEquiv.commutes _ _
    have h4 : algebraMap (R' ⊗[R] Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V))
        Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h))
        ((1 : R') ⊗ₜ[R] a) =
        algebraMap Γ(relCurve C R', (fst C (overSpec k R')).left ⁻¹ᵁ V)
          Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h))
          (relTermBaseChangeAlg (C := C) (R := R) R' V hV hV' ((1 : R') ⊗ₜ[R] a)) := rfl
    have h5 : relTermBaseChangeAlg (C := C) (R := R) R' V hV hV' ((1 : R') ⊗ₜ[R] a)
        = relSectionsMap C R R' V a := by
      rw [relTermBaseChangeAlg_tmul, one_smul]
    change pieceTermBaseChangeAlg R' V hV hV' hVaff hVaff' h
        ((1 : R') ⊗ₜ[R] (algebraMap Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)
          Γ(relCurve C R, (relCurve C R).basicOpen h) a)) =
      pieceSectionsMap R' V h
        (algebraMap Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)
          Γ(relCurve C R, (relCurve C R).basicOpen h) a)
    rw [h1, h2, h3, h4, h5, pieceSectionsMap_algebraMap]
  exact RingHom.congr_fun key s

/-! ## Base change of piece quotients (the colength transport) -/

/-- The piece-level term identification carries the extended span of a set of
equations to the span of the compared equations (`Ideal.map_span` +
`pieceTermBaseChangeAlg_one_tmul`); the `hIJ` input of the colength transport. -/
lemma pieceSpan_map_eq (E : Set Γ(relCurve C R, (relCurve C R).basicOpen h)) :
    Ideal.span (pieceSectionsMap R' V h '' E) =
      ((Ideal.span E).map (Algebra.TensorProduct.includeRight (R := R) (A := R')
        (B := Γ(relCurve C R, (relCurve C R).basicOpen h)))).map
        (pieceTermBaseChangeAlg R' V hV hV' hVaff hVaff' h : _ →+* _) := by
  rw [Ideal.map_span, Ideal.map_span, ← Set.image_comp]
  exact congrArg Ideal.span (Set.image_congr fun s _ =>
    (pieceTermBaseChangeAlg_one_tmul R' V hV hV' hVaff hVaff' h s).symm)

/-- **Base change of a quotient of piece sections** (the colength transport,
`informal/spec-dd-1.md` §3 stage (c)): for a set `E` of equations on the piece `D(h)`,
`R' ⊗[R] (Γ(D(h)) ⧸ (E)) ≃ₐ[R'] Γ(D(h')) ⧸ (E')` where `h' = relSectionsMap h` and `E'`
is the image of `E` under the piece-sections comparison. Quotient right-exactness
(`Algebra.TensorProduct.tensorQuotientEquiv`) followed by transport along the
piece-level term identification (`Ideal.quotientEquivAlg`; the span is carried by the
naturality rule `pieceTermBaseChangeAlg_one_tmul`). At `E = {f}` this is the chart-local
colength transport; at the two-element `E` it is the overlap-colength transport. -/
noncomputable def pieceQuotBaseChangeAlg
    (E : Set Γ(relCurve C R, (relCurve C R).basicOpen h)) :
    R' ⊗[R] (Γ(relCurve C R, (relCurve C R).basicOpen h) ⧸ Ideal.span E) ≃ₐ[R']
      Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V h)) ⧸
        Ideal.span (pieceSectionsMap R' V h '' E) :=
  (Algebra.TensorProduct.tensorQuotientEquiv R' Γ(relCurve C R, (relCurve C R).basicOpen h)
    R' (Ideal.span E)).trans
    (Ideal.quotientEquivAlg _ _ (pieceTermBaseChangeAlg R' V hV hV' hVaff hVaff' h)
      (pieceSpan_map_eq R' V hV hV' hVaff hVaff' h E))

/-- The quotient transport on a pure tensor of a residue class: `1 ⊗ [s] ↦ [s']` with
`s'` the compared section `pieceSectionsMap s`. -/
lemma pieceQuotBaseChangeAlg_one_tmul_mk
    (E : Set Γ(relCurve C R, (relCurve C R).basicOpen h))
    (s : Γ(relCurve C R, (relCurve C R).basicOpen h)) :
    pieceQuotBaseChangeAlg R' V hV hV' hVaff hVaff' h E
        ((1 : R') ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span E) s) =
      Ideal.Quotient.mk (Ideal.span (pieceSectionsMap R' V h '' E))
        (pieceSectionsMap R' V h s) := by
  have h1 : pieceQuotBaseChangeAlg R' V hV hV' hVaff hVaff' h E
      ((1 : R') ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span E) s) =
      Ideal.Quotient.mk (Ideal.span (pieceSectionsMap R' V h '' E))
        (pieceTermBaseChangeAlg R' V hV hV' hVaff hVaff' h ((1 : R') ⊗ₜ[R] s)) := rfl
  rw [h1, pieceTermBaseChangeAlg_one_tmul]

end Piece

end AlgebraicGeometry
