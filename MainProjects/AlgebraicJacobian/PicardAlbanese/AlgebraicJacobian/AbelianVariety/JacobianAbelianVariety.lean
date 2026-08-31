/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.AbelianVariety.JacobianSmooth
import AlgebraicJacobian.AbelianVariety.AbelSource
import AlgebraicJacobian.Tangent.Pic0TangentSpace

/-!
# The Jacobian is an abelian variety: the Wave-5 assembly (S3 shape, conditional)

The top-level Wave-5 statement, assembled from the legs proved across `Tangent/`
and `AbelianVariety/`, and **conditional on exactly the inputs that are still
open**. Following `informal/w5-s-worksheet.md` §2.1 recommendation (a): assemble
the package now with the open inputs as explicit arguments, rather than wait —
that unblocks everything downstream of the assembly and keeps the residual
obligations visible in the signatures instead of buried in `sorry`s.

## What is closed and what is open

Closed, unconditionally, at the datum:

* `IsSeparated d.J.hom` — X1, group-theoretic (`AbelianVariety/GroupSeparated.lean`).
* `LocallyOfFiniteType` / `QuasiCompact` — the datum's construction certificates.
* the tangent identifications `T₀(d.J) ≃ Dual κ(e) (m_e/m_e²) ≃ ker(Pic⁰(k[ε]) → Pic⁰(k))`
  — T1/T5 (`Tangent/Pic0TangentSpace.lean`).

Open, and therefore *arguments* here rather than hypotheses discharged elsewhere:

1. `AbelSourceData d` — the proper `Div^d`-source with its Abel morphism (**P1**,
   a cross-wave gate on the divisor-representability shapes). Supplies properness
   (P3) and geometric irreducibility (G1).
2. `GeometricallyReduced d.J.hom` — **S1**. See `informal/w5-s-worksheet.md` §2:
   its remaining content is the reduced-stalk-at-the-identity statement, gated on
   the T3/T4 `ε`-kernel computation, plus a transcendental-extension step that the
   pinned mathlib does not have.
3. `hdim` — the T3/T4 numeral `dim_κ(e) m_e/m_e² = genus C`.

## Why `SmoothOfRelativeDimension (genus C)` is *not* claimed here

S3's route is frozen in `informal/w5-s-worksheet.md` §3 and is genuinely
available — mathlib's `SmoothOfRelativeDimension` is pointwise and
local-at-source, so translation homogeneity (X2) transporting the identity count
(T5) is the whole uniformity argument, with no locally-constant-dimension theorem
needed. But it consumes `hdim` *chartwise*, through
`IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth`, and that chart
bookkeeping is real work that the numeral does not yet support. Claiming it now
would mean either a `sorry` or a hypothesis so strong it assumes the conclusion;
neither is honest. `isAbelianVariety_of_abelSource` below therefore delivers the
*proper + smooth + geometrically irreducible group scheme* package — everything
except the frozen numeral — and `smoothOfRelativeDimension_statement` records
what remains, as a `Prop`-valued abbreviation so that the residual obligation has
a name and a home.

## Main declarations

* `AlgebraicGeometry.JacobianData.isProper_and_smooth_of_abelSource` — proper and
  smooth over `k`, given (1) and (2).
* `AlgebraicGeometry.JacobianData.isAbelianVariety_of_abelSource` — the full
  package: separated, proper, smooth, geometrically irreducible.

Reference: Kleiman, "The Picard scheme", §5 `cor:sm` (arXiv:math/0504020);
Milne, "Abelian varieties", Thm. 1.6 and Prop. 2.1.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace JacobianData

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
  {d : JacobianData C}

/-- **Proper and smooth over `k`**, given an Abel source (P1) and geometric
reducedness (S1). Properness is P3 (`isProper_of_abelSource`: X1 + P2 + the
local-finite-type certificate) and smoothness is S2 (`JacobianData.smooth`, i.e.
mathlib's group-scheme criterion). -/
theorem isProper_and_smooth_of_abelSource (a : AbelSourceData d)
    [GeometricallyReduced d.J.hom] :
    IsProper d.J.hom ∧ Smooth d.J.hom :=
  ⟨isProper_of_abelSource a, d.smooth⟩

/-- **The Wave-5 abelian-variety package for the Jacobian**, given an Abel source
(P1) and geometric reducedness (S1): the representing object of the datum is a
separated, proper, smooth, geometrically irreducible group scheme over `k`.

The group structure itself is `d.grpObj` and is not restated in the conjunction;
what the four conjuncts add is exactly the "abelian variety" content beyond being
a group object. The remaining Wave-5 item after this is the *frozen numeral*
(relative dimension `genus C`), recorded in `smoothOfRelativeDimension_statement`
below. -/
theorem isAbelianVariety_of_abelSource (a : AbelSourceData d)
    [GeometricallyReduced d.J.hom] :
    IsSeparated d.J.hom ∧ IsProper d.J.hom ∧ Smooth d.J.hom
      ∧ GeometricallyIrreducible d.J.hom :=
  ⟨d.isSeparated, isProper_of_abelSource a, d.smooth,
    geometricallyIrreducible_of_abelSource a⟩

/-- **The residual Wave-5 obligation, named** (S3, roadmap `AJCR.w5-av.s3`): that
`d.J` is smooth of relative dimension `genus C` over `k`. Its route is frozen in
`informal/w5-s-worksheet.md` §3 (pointwise charts + X2 translation transport of
the T5 identity count; **no** rel-dim descent and **no**
locally-constant-dimension theorem needed), and it consumes the T3/T4 numeral
chartwise.

Kept as a named `Prop` rather than a `sorry`ed theorem so that the obligation is
citable, greppable, and machine-checkable when discharged, without registering a
staged fact (w5-worksheet §0(4)). -/
abbrev smoothOfRelativeDimension_statement (d : JacobianData C) : Prop :=
  SmoothOfRelativeDimension (genus C) d.J.hom

/-- Given the frozen numeral (S3), the full package upgrades: relative dimension
`genus C` implies smoothness, so the Abel source is the only remaining input for
properness and geometric irreducibility, and `GeometricallyReduced` is no longer
needed as a separate hypothesis — it follows from smoothness
(`Curve/GeometricallyReduced.lean`, `SmoothOfRelativeDimension.geometricallyReduced`).

This is the shape the frozen gate will instantiate; recording it now makes the
dependency direction explicit and prevents the circularity S1 invites (S2 derives
`Smooth` *from* `GeometricallyReduced`, so the converse must only ever be used
on the S3 side). -/
theorem isAbelianVariety_of_abelSource_of_relativeDimension (a : AbelSourceData d)
    (hs : smoothOfRelativeDimension_statement d) :
    IsSeparated d.J.hom ∧ IsProper d.J.hom ∧ Smooth d.J.hom
      ∧ GeometricallyIrreducible d.J.hom :=
  haveI := hs
  haveI : GeometricallyReduced d.J.hom :=
    SmoothOfRelativeDimension.geometricallyReduced (genus C) d.J.hom
  isAbelianVariety_of_abelSource a

end JacobianData

end AlgebraicGeometry
