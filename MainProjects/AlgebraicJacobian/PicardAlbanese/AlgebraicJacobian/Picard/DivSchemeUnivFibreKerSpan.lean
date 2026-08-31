/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeSeedDvd
import AlgebraicJacobian.Picard.DivisorFamilyPullbackOverlap

/-!
# G-4 — the shared piece-colength base-change setup for `hspan` and `hfield`

The two fibre-comparison inputs of the sound seed-close capstone
`ThetaGeneratorSeed.isGenerator_of_fibrewise_ker_span_of_field_vanishing`
(`Picard/DivSchemeSeedUnivClose.lean`) — `hspan` (the carve fibre-kernel-spanning law) and
`hfield` (the fibre-vanishing of the `K`-side components) — are both stated in the residue
fibre of the per-piece **colength** `Γ(D(h z)) ⧸ (eqn z)`.  Both need the *same* algebraic
transport: the base change of the colength to a residue field `κ(p)` is the fibre colength
`Γ(D(h z')) ⧸ (eqn z')` of the base-changed piece.  This file factors that transport once,
side-uniformly over the pinned-chart side `D.side z`, from the generic piece-colength base
change `pieceQuotBaseChangeAlg` (`Picard/DivisorFamilyPullback.lean`).

* `ThetaGeneratorSeed.pinnedPieceSectionsMap` — the side-uniform piece-sections comparison
  `Γ(D(h)) → Γ(D(h'))`, `h' = relPinnedSectionsMap b h`;
* `ThetaGeneratorSeed.pinnedPieceQuotBaseChangeAlg` — the colength transport
  `R' ⊗[R] (Γ(D(h)) ⧸ (E)) ≃ₐ[R'] Γ(D(h')) ⧸ (pinnedPieceSectionsMap '' E)`;
* `ThetaGeneratorSeed.pinnedPieceQuotBaseChangeAlg_one_tmul_mk` — its value on `1 ⊗ [s]`;
* `ThetaGeneratorSeed.mk_tmul_one_eq_zero_iff_pinnedPieceSectionsMap_mem` — the transport
  of the fibre-vanishing clause `[s] ⊗ₜ 1 = 0` to fibre divisibility (the shape both
  `hfield` and the `hspan` kernel comparison consume).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}
variable {K : Submodule R (relThetaSections C R π a)}

namespace ThetaGeneratorSeed

/-! ## The side-uniform piece comparison and colength transport -/

/-- **The side-uniform piece-sections comparison**: the base-change section map on the
basic open `D(h)` of a pinned chart, cased over the side `b`
(`pieceSectionsMap` at `fiberChart₀`/`fiberChart₁`).  Its target is the piece of the
base-changed generator `relPinnedSectionsMap b h`. -/
noncomputable def pinnedPieceSectionsMap (b : Bool)
    (h : Γ(relCurve C R, relPinnedChart C R π b)) :
    Γ(relCurve C R, (relCurve C R).basicOpen h) →+*
      Γ(relCurve C R', (relCurve C R').basicOpen (relPinnedSectionsMap C R R' π b h)) :=
  match b, h with
  | false, h => pieceSectionsMap R' (fiberChart₀ π) h
  | true, h => pieceSectionsMap R' (fiberChart₁ π) h

/-- **The side-uniform piece-colength transport**: for a set `E` of equations on `D(h)`,
`R' ⊗[R] (Γ(D(h)) ⧸ (E)) ≃ₐ[R'] Γ(D(h')) ⧸ (pinnedPieceSectionsMap '' E)`, `h' =
relPinnedSectionsMap b h` — the generic `pieceQuotBaseChangeAlg`, cased over the side. -/
noncomputable def pinnedPieceQuotBaseChangeAlg (b : Bool)
    (h : Γ(relCurve C R, relPinnedChart C R π b))
    (E : Set Γ(relCurve C R, (relCurve C R).basicOpen h)) :
    R' ⊗[R] (Γ(relCurve C R, (relCurve C R).basicOpen h) ⧸ Ideal.span E) ≃ₐ[R']
      Γ(relCurve C R', (relCurve C R').basicOpen (relPinnedSectionsMap C R R' π b h)) ⧸
        Ideal.span (pinnedPieceSectionsMap R' b h '' E) :=
  match b, h with
  | false, h =>
      pieceQuotBaseChangeAlg R' (fiberChart₀ π)
        (fiberTwoCover π).isAffineOpen₀.isCompact
        (fiberTwoCover π).isAffineOpen₀.isQuasiSeparated
        (relCover_isAffineOpen₀ C R (fiberTwoCover π))
        (relCover_isAffineOpen₀ C R' (fiberTwoCover π)) h E
  | true, h =>
      pieceQuotBaseChangeAlg R' (fiberChart₁ π)
        (fiberTwoCover π).isAffineOpen₁.isCompact
        (fiberTwoCover π).isAffineOpen₁.isQuasiSeparated
        (relCover_isAffineOpen₁ C R (fiberTwoCover π))
        (relCover_isAffineOpen₁ C R' (fiberTwoCover π)) h E

/-- The colength transport on a pure tensor of a residue class:
`1 ⊗ [s] ↦ [pinnedPieceSectionsMap s]`. -/
lemma pinnedPieceQuotBaseChangeAlg_one_tmul_mk (b : Bool)
    (h : Γ(relCurve C R, relPinnedChart C R π b))
    (E : Set Γ(relCurve C R, (relCurve C R).basicOpen h))
    (s : Γ(relCurve C R, (relCurve C R).basicOpen h)) :
    pinnedPieceQuotBaseChangeAlg R' b h E
        ((1 : R') ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span E) s) =
      Ideal.Quotient.mk (Ideal.span (pinnedPieceSectionsMap R' b h '' E))
        (pinnedPieceSectionsMap R' b h s) := by
  cases b with
  | false =>
      exact pieceQuotBaseChangeAlg_one_tmul_mk R' (fiberChart₀ π)
        (fiberTwoCover π).isAffineOpen₀.isCompact
        (fiberTwoCover π).isAffineOpen₀.isQuasiSeparated
        (relCover_isAffineOpen₀ C R (fiberTwoCover π))
        (relCover_isAffineOpen₀ C R' (fiberTwoCover π)) h E s
  | true =>
      exact pieceQuotBaseChangeAlg_one_tmul_mk R' (fiberChart₁ π)
        (fiberTwoCover π).isAffineOpen₁.isCompact
        (fiberTwoCover π).isAffineOpen₁.isQuasiSeparated
        (relCover_isAffineOpen₁ C R (fiberTwoCover π))
        (relCover_isAffineOpen₁ C R' (fiberTwoCover π)) h E s

/-- **The transported fibre-vanishing clause**: the residue class `[s]` of a piece section
dies in the fibre `κ(p)` (`[s] ⊗ₜ 1 = 0`) iff its image `pinnedPieceSectionsMap s` in the
base-changed piece lies in the ideal generated by the transported equations
`pinnedPieceSectionsMap '' E` — the exact reduction of `hfield` (and of the `hspan` fibre
kernel comparison) to fibre divisibility on the base-changed curve. -/
lemma mk_tmul_one_eq_zero_iff_pinnedPieceSectionsMap_mem (b : Bool)
    (h : Γ(relCurve C R, relPinnedChart C R π b))
    (E : Set Γ(relCurve C R, (relCurve C R).basicOpen h))
    (s : Γ(relCurve C R, (relCurve C R).basicOpen h)) :
    (Ideal.Quotient.mk (Ideal.span E) s ⊗ₜ[R] (1 : R')
        : (Γ(relCurve C R, (relCurve C R).basicOpen h) ⧸ Ideal.span E) ⊗[R] R') = 0
      ↔ pinnedPieceSectionsMap R' b h s
          ∈ Ideal.span (pinnedPieceSectionsMap R' b h '' E) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem,
    ← pinnedPieceQuotBaseChangeAlg_one_tmul_mk R' b h E s,
    map_eq_zero_iff _ (pinnedPieceQuotBaseChangeAlg R' b h E).injective,
    ← LinearEquiv.map_eq_zero_iff (TensorProduct.comm R _ R'), TensorProduct.comm_tmul]

/-! ## The `hfield` reduction: to per-generator fibre divisibility -/

variable (D : ThetaGeneratorSeed C R π a K)

set_option maxHeartbeats 1600000 in
-- the `D.piece z` ↔ `(relCurve C R).basicOpen (D.h z)` defeq over the heavy relCurve
-- section-ring colength drives the transport application past the default budget
set_option synthInstance.maxHeartbeats 400000 in
/-- **`hfield` reduced to fibre divisibility**: if every `K`-side component of the seed
`D`, restricted to the base-changed piece `D(h z')` at each base prime `p`, is divisible by
the base-changed equation `eqn z'`, then the `hfield` clause of
`isGenerator_of_fibrewise_ker_span_of_field_vanishing` holds — every element of the
`K`-side-component submodule `N z` dies in the residue-field fibre.  The transport is
`mk_tmul_one_eq_zero_iff_pinnedPieceSectionsMap_mem`; the residual honest content is the
`hdiv` fibre-divisibility (the `d_p` achiever, for the universal seed). -/
theorem hfield_of_forall_pinnedPieceSectionsMap_mem
    (hdiv : ∀ (z : relCurve C R) (p : PrimeSpectrum R) ⦃ψ : relThetaSections C R π a⦄,
      ψ ∈ K →
      pinnedPieceSectionsMap p.asIdeal.ResidueField (D.side z) (D.h z)
          (relThetaResSide a (D.side z) (D.piece_le z) ψ)
        ∈ Ideal.span {pinnedPieceSectionsMap p.asIdeal.ResidueField (D.side z) (D.h z)
          (D.eqn z)}) :
    ∀ (z : relCurve C R) (y : relCurve C R) (hy : y ∈ D.piece z)
        (x : ↥(D.sideColengthSubmodule z)),
        ((x : Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}) ⊗ₜ[R]
            (1 : (basePrime (R := R)
              ((relCurve C R).presheaf.germ (D.piece z) y hy).hom).asIdeal.ResidueField))
          = 0 := by
  intro z y hy x
  obtain ⟨ψ, hψK, hψx⟩ := x.2
  have hmk : (x : Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z})
      = Ideal.Quotient.mk (Ideal.span {D.eqn z})
          (relThetaResSide a (D.side z) (D.piece_le z) ψ) := hψx.symm
  rw [hmk]
  refine (mk_tmul_one_eq_zero_iff_pinnedPieceSectionsMap_mem _ (D.side z) (D.h z)
    {D.eqn z} (relThetaResSide a (D.side z) (D.piece_le z) ψ)).mpr ?_
  rw [Set.image_singleton]
  exact hdiv z _ hψK

/-! ## The `hspan` reduction: to fibre injectivity of the induced map -/

set_option maxHeartbeats 1600000 in
-- the heavy relCurve section-ring colength drives the `rTensor` factorisation defeq past
-- the default budget
set_option synthInstance.maxHeartbeats 400000 in
/-- **`hspan` reduced to induced-map fibre injectivity**: the fibrewise-kernel-spanning law
`hspan` of `isGenerator_of_fibrewise_ker_span_of_field_vanishing` follows from injectivity,
at every base prime, of the residue-fibre of the map `K ⧸ ker f_z → colength z` **induced**
by the `K`-side-component map `f_z = kColengthMap z ∘ K.subtype` (`f_z` with its kernel
divided out).  The `≥` inclusion of the fibre kernel is automatic (right-exactness of
`− ⊗ κ(p)` on the sequence `ker f_z ↪ K ↠ K ⧸ ker f_z`, `rTensor_exact`); the `≤`
inclusion `hspan` is exactly this induced-map fibre injectivity `hinj`.

This is the *sound* replacement of the false `FibreInjective` route: `FibreInjective`
asked `f_z ⊗ κ(p)` itself to be injective (false — `f_z` always kills the seed section),
whereas the induced map `K ⧸ ker f_z → colength z` divides that kernel out first, so its
fibre injectivity is the genuine carve rank-`g` content (`divUniversal_carve_residueField`),
never contradicted by the seed section. -/
theorem hspan_of_forall_liftQ_rTensor_injective
    (hinj : ∀ (z : relCurve C R) (p : PrimeSpectrum R),
      Function.Injective
        (((LinearMap.ker ((D.kColengthMap z).comp K.subtype)).liftQ
            ((D.kColengthMap z).comp K.subtype) le_rfl).rTensor p.asIdeal.ResidueField)) :
    ∀ (z : relCurve C R) (p : PrimeSpectrum R),
      LinearMap.ker (((D.kColengthMap z).comp K.subtype).rTensor p.asIdeal.ResidueField)
        ≤ LinearMap.range
          ((LinearMap.ker ((D.kColengthMap z).comp K.subtype)).subtype.rTensor
            p.asIdeal.ResidueField) := by
  intro z p u hu
  set f := (D.kColengthMap z).comp K.subtype with hf
  set L := LinearMap.ker f with hL
  have hcomp : f.rTensor p.asIdeal.ResidueField
      = (L.liftQ f le_rfl).rTensor p.asIdeal.ResidueField ∘ₗ
          L.mkQ.rTensor p.asIdeal.ResidueField := by
    rw [← LinearMap.rTensor_comp, Submodule.liftQ_mkQ]
  have h0 : L.mkQ.rTensor p.asIdeal.ResidueField u = 0 := by
    apply hinj z p
    rw [map_zero]
    have hu0 := LinearMap.mem_ker.mp hu
    rw [hcomp, LinearMap.comp_apply] at hu0
    exact hu0
  have hex := rTensor_exact (R := R) p.asIdeal.ResidueField
    (LinearMap.exact_subtype_mkQ L) (Submodule.mkQ_surjective L)
  rw [← LinearMap.exact_iff.mp hex, LinearMap.mem_ker]
  exact h0

end ThetaGeneratorSeed

end AlgebraicGeometry
