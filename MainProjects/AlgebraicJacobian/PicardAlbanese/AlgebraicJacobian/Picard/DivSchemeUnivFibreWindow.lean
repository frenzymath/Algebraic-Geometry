/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeUnivFibreKerSpan
import AlgebraicJacobian.Picard.DivSchemeSeedUnivRead

/-!
# G-4 — the shared fibre-window ↔ colength side-component brick

Both cores of the sound seed close (`hdiv`/`hfield` and `hinj`/`hspan`) read a `K`-side
component of a window section on the *base-changed piece* `D(h')` at a residue field `κ(p)`,
through `ThetaGeneratorSeed.pinnedPieceSectionsMap`.  This file identifies that reading with
the **fibre window section** of the compared window vector: the piece-level lift of the G-2
crux triangle `relPinnedSectionsMap_relThetaResSide_windowEquiv`
(`Picard/DivSchemeSeedUnivRead.lean`), which lives on the whole pinned chart, to the basic
sub-open `D(h)` of the piece.

* `ThetaGeneratorSeed.pinnedPieceSectionsMap_resHom` — **the piece-vs-chart naturality**:
  the compared piece section of a chart section restricted to `D(h)` is the restriction to
  `D(h')` of the compared chart section (`pieceSectionsMap_algebraMap`, cased over the side);
* `ThetaGeneratorSeed.pinnedPieceSectionsMap_relThetaResSide_windowEquiv` — **the shared
  brick**: the fibre reading `pinnedPieceSectionsMap κ(p) b h (relThetaResSide a b … (Θ x))`
  of the side component of a window section `Θ x = relThetaWindowEquiv x` is the side
  component, restricted to `D(h')`, of the **fibre window section**
  `relThetaWindowEquiv (windowCompare x)` of the compared vector — the identification both
  cores consume to move to the fibre curve over `κ(p)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace ThetaGeneratorSeed

/-! ## The piece-vs-chart naturality of the side-uniform piece comparison -/

section Naturality

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable {π : C.left ⟶ P1 k} [IsFinite π]

/-- **The piece-vs-chart naturality of `pinnedPieceSectionsMap`**: for chart sections `h`
(the piece generator) and `s` on a pinned chart, the compared piece section of `s|_{D(h)}`
is the restriction to `D(h')` (`h' = relPinnedSectionsMap b h`) of the compared chart
section `relPinnedSectionsMap b s`.  Both `pinnedPieceSectionsMap` and `relPinnedSectionsMap`
are `appLE` of `relCurveMap`, so this is `pieceSectionsMap_algebraMap` (the chart-to-piece
`algebraMap` is `resHom`), cased over the side. -/
lemma pinnedPieceSectionsMap_resHom (b : Bool)
    (h s : Γ(relCurve C R, relPinnedChart C R π b)) :
    pinnedPieceSectionsMap R' b h
        ((relCurve C R).resHom ((relCurve C R).basicOpen_le h) s)
      = (relCurve C R').resHom
          ((relCurve C R').basicOpen_le (relPinnedSectionsMap C R R' π b h))
          (relPinnedSectionsMap C R R' π b s) := by
  cases b with
  | false => exact pieceSectionsMap_algebraMap R' (fiberChart₀ π) h s
  | true => exact pieceSectionsMap_algebraMap R' (fiberChart₁ π) h s

end Naturality

/-! ## The shared brick: piece reading = fibre window side component -/

section Brick

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (K : Type u) [Field K] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
variable (π : C.left ⟶ P1 k) [IsFinite π]

noncomputable local instance instOverCleftFibreWindow : C.left.Over (Spec (.of k)) :=
  ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable (a : ℕ)
variable (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)

set_option maxHeartbeats 800000 in
-- the piece-level lift of the G-2 triangle crosses the mixed `relCurve`/product spellings
set_option synthInstance.maxHeartbeats 400000 in
/-- **The shared fibre-window ↔ colength brick**: the fibre reading, on the base-changed
piece `D(h')`, of the side component of a relative window section `Θ x = relThetaWindowEquiv x`
is the side component (restricted to `D(h')`) of the **fibre window section**
`relThetaWindowEquiv (windowCompare x)` of the compared vector.

This lifts the chart-level crux triangle `relPinnedSectionsMap_relThetaResSide_windowEquiv`
to the piece `D(h)` via the piece-vs-chart naturality `pinnedPieceSectionsMap_resHom` and the
restriction law `resHom_relThetaResSide` on both ends.  It is the common step of both seed-close
cores: the `hfield` divisibility and the `hspan` fibre injectivity both read `K`-side
components as fibre window sections through this identity. -/
theorem pinnedPieceSectionsMap_relThetaResSide_windowEquiv (b : Bool)
    (h : Γ(relCurve C R, relPinnedChart C R π b))
    (x : R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) :
    pinnedPieceSectionsMap K b h
        (relThetaResSide a b ((relCurve C R).basicOpen_le h)
          (relThetaWindowEquiv C R π a hH1 x))
      = relThetaResSide a b
          ((relCurve C K).basicOpen_le (relPinnedSectionsMap C R K π b h))
          (relThetaWindowEquiv C K π a hH1 (windowCompare R K x)) := by
  have e1 : relThetaResSide a b ((relCurve C R).basicOpen_le h)
        (relThetaWindowEquiv C R π a hH1 x)
      = (relCurve C R).resHom ((relCurve C R).basicOpen_le h)
          (relThetaResSide a b le_rfl (relThetaWindowEquiv C R π a hH1 x)) :=
    (resHom_relThetaResSide a b le_rfl ((relCurve C R).basicOpen_le h) _).symm
  rw [e1, pinnedPieceSectionsMap_resHom K b h _,
    relPinnedSectionsMap_relThetaResSide_windowEquiv C R K π a hH1 b x,
    resHom_relThetaResSide a b le_rfl
      ((relCurve C K).basicOpen_le (relPinnedSectionsMap C R K π b h)) _]

end Brick

end ThetaGeneratorSeed

end AlgebraicGeometry
