/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeSeed
import AlgebraicJacobian.Picard.DivSchemeRedesignFibreCut

/-!
# DD-4 redesign — the redesigned seed's generator clause (`isGenerator` from the ann-cutter)

The seed-revision payoff (`informal/spec-dd4-redesign.md` §1.5, landing note I-0289): the
revised universal seed `seedUniv'` — whose `sec z` is the **relative achiever** (brick 2,
`DivSchemeRedesignAchiever.lean`) and whose `h z` is the **ann-based fibre-cutter** (brick 3,
`DivSchemeRedesignFibreCut.lean`) — is a `ThetaGeneratorSeed.IsGenerator` via the *simpler*
finale `isGenerator_of_fibre_ne_zero` (`DivSchemeSeed.lean:188`), **not** the fibrewise-ker
-span capstone.  The `hdvd` clause is DIRECT: it comes from the ann containment
`h z · (read ψ) ∈ ⟨read sec z⟩` (the fibre-cutter's defining property), threaded through
`hdvd_of_forall_smul_relThetaResSide_mem_span`.  The `hfib` clause is the fibrewise
nonvanishing of the achiever section (the landed span bridge, I-0258 keystones).

* `ThetaGeneratorSeed.isGenerator_of_ann_cutter` — **the redesigned `isGenerator_seedUniv`**:
  for any seed whose cutter `h z` annihilates the base-ideal colength (`hann`, the ann
  containment) and whose section is fibrewise nonvanishing (`hfib`), `IsGenerator` holds.
  This is exactly `isGenerator_of_fibre_ne_zero (hdvd) (hfib)` with the DIRECT `hdvd` — the
  entry point the seedUniv' assembly and the (non-circular) certificate consume.

The concrete `seedUniv'` value (choosing `sec = ` the brick-2 achiever, `h = ` the brick-3
ann-cutter at the `DivCarveChartRing` seed base) is the follow-up: its `hann` premise is the
fibre-cutter's `z ∉ supp(N z)` = the relative-local-BPF Nakayama `RD-N`, gated on the carve
`J`-flatness (brick 1's `hsub_seedUniv` residual, I-0290).  This file lands the generator
clause reduced to `hann`/`hfib` so it is non-circular and forward-compatible.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace ThetaGeneratorSeed

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}
variable {K : Submodule R (relThetaSections C R π a)}
variable (D : ThetaGeneratorSeed C R π a K)

/-- **The redesigned seed is a generator** (the seed-revision `isGenerator_seedUniv`,
`informal/spec-dd4-redesign.md` §1.5): a `ThetaGeneratorSeed` whose cutter `h z` annihilates
the base-ideal colength — the ann containment `h z · (read ψ) ∈ ⟨read (sec z)⟩` per point
(`hann`, the defining property of the brick-3 ann-based fibre-cutter) — and whose section is
fibrewise nonvanishing (`hfib`, the achiever span bridge) satisfies `IsGenerator`.

This is the redesign's `isGenerator_of_fibre_ne_zero (hdvd) (hfib)` with a **DIRECT** `hdvd`
supplied by `hdvd_of_forall_smul_relThetaResSide_mem_span` — no per-fibre `hfield`, no
`isGenerator_of_fibrewise_ker_span_of_field_vanishing` capstone.  It dissolves I-0288's razor:
`D(h z)` is a genuine fibre-neighbourhood (the ann-cutter shrinks it), on which the base
ideal collapses to `⟨eqn z⟩`. -/
theorem isGenerator_of_ann_cutter
    (hann : ∀ (z : relCurve C R) ⦃ψ : relThetaSections C R π a⦄, ψ ∈ K →
      D.h z * relThetaResSide a (D.side z) le_rfl ψ
        ∈ Ideal.span {relThetaResSide a (D.side z) le_rfl (D.sec z)})
    (hfib : ∀ (z : relCurve C R) (p : PrimeSpectrum R),
      ((relCurve C p.asIdeal.ResidueField).basicOpen
          (relPinnedSectionsMap C R p.asIdeal.ResidueField π (D.side z) (D.h z)) :
        (relCurve C p.asIdeal.ResidueField).Opens) ≠ ⊥ →
      relPinnedSectionsMap C R p.asIdeal.ResidueField π (D.side z)
        (relThetaResSide a (D.side z) le_rfl (D.sec z)) ≠ 0) :
    D.IsGenerator :=
  D.isGenerator_of_fibre_ne_zero (D.hdvd_of_forall_smul_relThetaResSide_mem_span hann) hfib

end ThetaGeneratorSeed

end AlgebraicGeometry
