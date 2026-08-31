/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeFamily
import AlgebraicJacobian.Picard.DivSchemeSeedFibre

/-!
# DDR-3 seed provider — `IsGenerator` from chart data (the fibre-regularity discharge)

The assembly step of the DDR-3 seed provider (I-0198 OPEN item): a
`ThetaGeneratorSeed` whose divisibility clause holds and whose chart-level equation
component is **fibrewise nonzero wherever its piece meets the fibre** satisfies
`IsGenerator` — the `fibre_regular` clause is discharged through the
`DivSchemeSeedFibre` keystones:

* `AlgebraicGeometry.relPinnedSectionsMap` — the side-uniform fibre comparison on the
  pinned charts (`relSectionsMap` at `fiberChart₀/₁`);
* `AlgebraicGeometry.relPinned_tmul_one_mem_nonZeroDivisors` — the side-uniform
  fibre-regularity keystone on basic opens of a pinned chart;
* `AlgebraicGeometry.ThetaGeneratorSeed.basicOpen_eq_basicOpen_mul` — every basic
  sub-open of a piece is the basic open of a chart-level section (`D(f) = D(h·u)`,
  denominator clearing);
* `AlgebraicGeometry.ThetaGeneratorSeed.isGenerator_of_fibre_ne_zero` — **the
  keystone**: `dvd` + fibrewise nonvanishing of the chart component of the chosen
  generator (at every prime whose fibre meets the piece) imply `IsGenerator`.

What remains for the unconditional seed over the `Z(♦)`-chart rings is the *choice*
side (P-fib at `κ(p)` + `exists_achiever_of_span` + the window dictionary at the fibre
— the DD-4 base-field-transport seam); this file makes the geometric packaging of that
choice a single named boundary.
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

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable {π : C.left ⟶ P1 k} [IsFinite π]

/-! ## The side-uniform fibre comparison on the pinned charts -/

variable (C R π) in
/-- **The side-uniform fibre comparison on the pinned charts**: `relSectionsMap` at the
chart of the side (`fiberChart₀` for `false`, `fiberChart₁` for `true`), typed on
`relPinnedChart`. -/
noncomputable def relPinnedSectionsMap :
    ∀ b : Bool, Γ(relCurve C R, relPinnedChart C R π b) →+*
      Γ(relCurve C R', relPinnedChart C R' π b)
  | false => relSectionsMap C R R' (fiberChart₀ π)
  | true => relSectionsMap C R R' (fiberChart₁ π)

/-! ## The side-uniform fibre-regularity keystone -/

variable [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]

section Field

variable (L : Type u) [Field L] [Algebra k L] [Algebra R L] [IsScalarTower k R L]

set_option maxHeartbeats 1600000 in
-- the side-uniform statement forces the `relPinnedChart` ↔ chart-preimage defeq checks
-- through the product spelling in each branch
set_option synthInstance.maxHeartbeats 800000 in
-- the pinned-chart section rings and their tensor algebras drive long instance chains
variable (C R π) in
/-- **The side-uniform fibre-regularity keystone**: for `g, E` sections of a pinned
chart with the compared section `E` nonzero on the fibre whenever the fibre basic open
`D(g')` is nonempty, the restricted pure tensor `E|_{D(g)} ⊗ 1` is a nonzerodivisor in
`Γ(C_R, D(g)) ⊗[R] L` — the `DivSchemeSeedFibre` keystones, cased over the side. -/
theorem relPinned_tmul_one_mem_nonZeroDivisors (b : Bool)
    (g E : Γ(relCurve C R, relPinnedChart C R π b))
    (hE : ((relCurve C L).basicOpen (relPinnedSectionsMap C R L π b g) :
        (relCurve C L).Opens) ≠ ⊥ → relPinnedSectionsMap C R L π b E ≠ 0) :
    ((relCurve C R).resHom ((relCurve C R).basicOpen_le g) E) ⊗ₜ[R] (1 : L)
      ∈ nonZeroDivisors (Γ(relCurve C R, (relCurve C R).basicOpen g) ⊗[R] L) := by
  cases b with
  | false =>
    exact tmul_one_mem_nonZeroDivisors_of_relBasicPull C R (fiberChart₀ π) L
      (isAffineOpen_preimage_chartOpen π 0).isCompact
      (isAffineOpen_preimage_chartOpen π 0).isQuasiSeparated
      (isAffineOpen_relPinnedChart C R π false)
      (isAffineOpen_relPinnedChart C L π false) g
      ((relCurve C R).resHom ((relCurve C R).basicOpen_le g) E)
      (fun hne => relBasicPull_resHom_ne_zero_of_relSectionsMap_ne_zero C R
        (fiberChart₀ π) L g E (hE hne) hne)
  | true =>
    exact tmul_one_mem_nonZeroDivisors_of_relBasicPull C R (fiberChart₁ π) L
      (isAffineOpen_preimage_chartOpen π 1).isCompact
      (isAffineOpen_preimage_chartOpen π 1).isQuasiSeparated
      (isAffineOpen_relPinnedChart C R π true)
      (isAffineOpen_relPinnedChart C L π true) g
      ((relCurve C R).resHom ((relCurve C R).basicOpen_le g) E)
      (fun hne => relBasicPull_resHom_ne_zero_of_relSectionsMap_ne_zero C R
        (fiberChart₁ π) L g E (hE hne) hne)

/-- Transport of the pure-tensor nonzerodivisor property across an equality of opens:
if the restriction along the equality is a nonzerodivisor after tensoring, so is the
original section. -/
lemma tmul_one_mem_nonZeroDivisors_of_eq {X : Scheme.{u}} [X.Over (Spec (.of R))]
    {O₁ O₂ : X.Opens} (hEq : O₁ = O₂) (x : Γ(X, O₁))
    (hx : (X.resHom hEq.ge x) ⊗ₜ[R] (1 : L) ∈ nonZeroDivisors (Γ(X, O₂) ⊗[R] L)) :
    x ⊗ₜ[R] (1 : L) ∈ nonZeroDivisors (Γ(X, O₁) ⊗[R] L) := by
  subst hEq
  rwa [Scheme.resHom_refl] at hx

end Field

/-! ## Basic sub-opens of a piece are chart basic opens -/

namespace ThetaGeneratorSeed

variable {a : ℕ} {K : Submodule R (relThetaSections C R π a)}
variable (D : ThetaGeneratorSeed C R π a K)

omit [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] in
/-- **Denominator clearing on a piece**: every basic sub-open `D(f)` of the piece at `z`
is the basic open of a chart-level section `h z · u`. -/
lemma basicOpen_eq_basicOpen_mul (z : relCurve C R)
    (f : Γ(relCurve C R, D.piece z)) :
    ∃ u : Γ(relCurve C R, relPinnedChart C R π (D.side z)),
      (relCurve C R).basicOpen f = (relCurve C R).basicOpen (D.h z * u) := by
  obtain ⟨u, n, hun⟩ := IsAffineOpen.exists_pow_mul_eq_resHom
    (isAffineOpen_relPinnedChart C R π (D.side z)) (D.h z) rfl (D.piece_le z) f
  refine ⟨u, ?_⟩
  have hunit : IsUnit ((relCurve C R).resHom (D.piece_le z) (D.h z)) :=
    (relCurve C R).isUnit_resHom_of_eq_basicOpen (D.h z) rfl (D.piece_le z)
  have hON : (relCurve C R).basicOpen
      ((relCurve C R).resHom (D.piece_le z) (D.h z) ^ n) = D.piece z :=
    (relCurve C R).toLocallyRingedSpace.toRingedSpace.basicOpen_of_isUnit (hunit.pow n)
  have h1 : (relCurve C R).basicOpen f = D.piece z ⊓ (relCurve C R).basicOpen f :=
    (inf_eq_right.mpr ((relCurve C R).basicOpen_le f)).symm
  have h2 : D.piece z ⊓ (relCurve C R).basicOpen f
      = (relCurve C R).basicOpen ((relCurve C R).resHom (D.piece_le z) (D.h z) ^ n)
        ⊓ (relCurve C R).basicOpen f :=
    congrArg (fun O => O ⊓ (relCurve C R).basicOpen f) hON.symm
  have h3 : (relCurve C R).basicOpen ((relCurve C R).resHom (D.piece_le z) (D.h z) ^ n)
        ⊓ (relCurve C R).basicOpen f
      = (relCurve C R).basicOpen
          ((relCurve C R).resHom (D.piece_le z) (D.h z) ^ n * f) :=
    ((relCurve C R).basicOpen_mul _ _).symm
  have h4 : (relCurve C R).basicOpen
        ((relCurve C R).resHom (D.piece_le z) (D.h z) ^ n * f)
      = (relCurve C R).basicOpen ((relCurve C R).resHom (D.piece_le z) u) :=
    congrArg (fun s => (relCurve C R).basicOpen s) hun
  have h5 : (relCurve C R).basicOpen ((relCurve C R).resHom (D.piece_le z) u)
      = D.piece z ⊓ (relCurve C R).basicOpen u :=
    Scheme.basicOpen_resHom (D.piece_le z) u
  have h7 : (relCurve C R).basicOpen (D.h z) ⊓ (relCurve C R).basicOpen u
      = (relCurve C R).basicOpen (D.h z * u) :=
    ((relCurve C R).basicOpen_mul _ _).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h7))))

/-! ## The keystone: `IsGenerator` from `dvd` + fibrewise nonvanishing -/

set_option maxHeartbeats 800000 in
-- the mixed relCurve/product defeq checks at the residue fields are heavy
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
-- the `κ(p)` residue-field towers over an abstract test ring exceed the lakefile
-- pending-depth default, and the pinned-chart tensor algebras drive long searches
-- (recorded escape hatch, I-0198 hazard 3)
/-- **`IsGenerator` from chart data** (the DDR-3 fibre-regularity discharge): a theta
generator seed satisfies `IsGenerator` as soon as

* `hdvd` — its divisibility clause holds (the Nakayama-neighbourhood output), and
* `hfib` — at every prime `p` whose fibre meets the piece at `z`, the compared
  chart-level component of the chosen generator is nonzero on the fibre curve.

The `fibre_regular` clause follows: every basic sub-open of the piece is a chart basic
open (`basicOpen_eq_basicOpen_mul`), and on those the `DivSchemeSeedFibre` keystones
turn fibrewise nonvanishing into pure-tensor regularity through the injective fibre
comparison and integrality of the fibre curve. -/
theorem isGenerator_of_fibre_ne_zero
    (hdvd : ∀ (z : relCurve C R) ⦃ψ : relThetaSections C R π a⦄, ψ ∈ K →
      relThetaResSide a (D.side z) (D.piece_le z) ψ ∈ Ideal.span {D.eqn z})
    (hfib : ∀ (z : relCurve C R) (p : PrimeSpectrum R),
      ((relCurve C p.asIdeal.ResidueField).basicOpen
          (relPinnedSectionsMap C R p.asIdeal.ResidueField π (D.side z) (D.h z)) :
        (relCurve C p.asIdeal.ResidueField).Opens) ≠ ⊥ →
      relPinnedSectionsMap C R p.asIdeal.ResidueField π (D.side z)
        (relThetaResSide a (D.side z) le_rfl (D.sec z)) ≠ 0) :
    D.IsGenerator where
  dvd := hdvd
  fibre_regular := by
    intro z p f
    -- the basic sub-open is a chart basic open
    obtain ⟨u, hBO⟩ := D.basicOpen_eq_basicOpen_mul z f
    -- transport the goal across the opens equality
    refine tmul_one_mem_nonZeroDivisors_of_eq p.asIdeal.ResidueField hBO _ ?_
    -- collapse the two restrictions onto the chart-level component
    have hcollapse : (relCurve C R).resHom hBO.ge
          ((relCurve C R).resHom ((relCurve C R).basicOpen_le f) (D.eqn z))
        = (relCurve C R).resHom
            ((relCurve C R).basicOpen_le (D.h z * u))
            (relThetaResSide a (D.side z) le_rfl (D.sec z)) := by
      rw [Scheme.resHom_resHom,
        show D.eqn z = relThetaResSide a (D.side z) (D.piece_le z) (D.sec z) from rfl,
        resHom_relThetaResSide, resHom_relThetaResSide]
    rw [hcollapse]
    -- fibrewise nonvanishing survives shrinking the chart basic open
    refine relPinned_tmul_one_mem_nonZeroDivisors C R π p.asIdeal.ResidueField
      (D.side z) (D.h z * u) (relThetaResSide a (D.side z) le_rfl (D.sec z))
      (fun hne => hfib z p ?_)
    -- `D(map (h·u)) ≤ D(map h)`: a nonempty product basic open forces the piece's
    intro hbot
    exact hne (by
      rw [map_mul, (relCurve C p.asIdeal.ResidueField).basicOpen_mul, hbot, bot_inf_eq])

end ThetaGeneratorSeed

end AlgebraicGeometry

/-! ## The free-module fibre-nonvanishing neighbourhood

The element-keeping strengthening of `exists_fibrewise_tmul_ne_zero_of_projective` on a
free ambient (the DDR-3 choice step feeds the *chosen* achiever through the free window
`R ⊗[k] H_a`, so its fibrewise nonvanishing locus is the union of the coordinate basic
opens). -/

namespace Module

open scoped TensorProduct

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- Coordinates detect ideal multiples in a free module: `x ∈ I·M` iff every coordinate
of `x` lies in `I`. -/
lemma mem_ideal_smul_top_iff_repr {ι : Type u} (b : Module.Basis ι R M) (I : Ideal R)
    (x : M) : x ∈ I • (⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun u v hu hv => ?_)
    · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hr
    · rw [map_add, Finsupp.add_apply]
      exact I.add_mem hu hv
  · intro hall
    have hx : (b.repr x).sum (fun i c => c • b i) = x := by
      rw [← Finsupp.linearCombination_apply, b.linearCombination_repr]
    rw [← hx]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    exact Submodule.smul_mem_smul (hall i) Submodule.mem_top

/-- **The fibre-nonvanishing neighbourhood of a fixed element of a free module**: if
`x ⊗ 1` is nonzero in the residue-field fibre at `p`, some coordinate `f` of `x`
survives at `p`, and `x ⊗ 1` stays nonzero at every prime of `D(f)` — the
element-keeping form of the Nakayama-neighbourhood step (the generators corollary keeps
only *some* section; on a free module the chosen one survives). -/
theorem exists_forall_tmul_residueField_ne_zero {ι : Type u} (b : Module.Basis ι R M)
    (x : M) (p : PrimeSpectrum R)
    (hx : (x ⊗ₜ[R] (1 : p.asIdeal.ResidueField) : M ⊗[R] p.asIdeal.ResidueField) ≠ 0) :
    ∃ f, f ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum R, f ∉ q.asIdeal →
      (x ⊗ₜ[R] (1 : q.asIdeal.ResidueField) : M ⊗[R] q.asIdeal.ResidueField) ≠ 0 := by
  haveI : Module.Free R M := Module.Free.of_basis b
  haveI : Module.Flat R M := Module.Flat.of_free
  have hxp : ¬ ∀ i, b.repr x i ∈ p.asIdeal := by
    intro hall
    exact hx (tmul_residueField_one_eq_zero_of_mem_smul_top p.asIdeal
      ((mem_ideal_smul_top_iff_repr b _ x).mpr hall))
  obtain ⟨i, hi⟩ := not_forall.mp hxp
  refine ⟨b.repr x i, hi, fun q hq h0 => ?_⟩
  exact hq ((mem_ideal_smul_top_iff_repr b _ x).mp
    (Module.Flat.mem_smul_top_of_tmul_residueField_one_eq_zero q.asIdeal h0) i)

end Module
