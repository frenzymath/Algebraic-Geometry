/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.ProjectiveMorphism
import AlgebraicJacobian.Picard.QuotFunctorDef

/-!
# Representability of the Quot scheme (honest statement)

The endgame statement of the A.2.b Quot-scheme chapter
(`thm:quot_representable`, [Nitsure] §5 "Main Existence Theorems"): for a
projective morphism `π : X ⟶ S` over a locally noetherian base, carrying a
relatively very ample line bundle `L`, and a coherent sheaf `E`, the Quot
functor `Quot^{Φ,L}_{E/X/S}` (`AlgebraicGeometry.Scheme.QuotFunctor`,
`Picard/QuotFunctorDef.lean`) is representable by an `S`-scheme.

This file carries the **faithful restatement** settled in inbox `I-0118`:
projectivity of `π` with very ample `L` is encoded by
`Scheme.Hom.IsProjectiveWith` (`Picard/ProjectiveMorphism.lean` — a closed
immersion into `ℙ(Fin (d+1); S)` over `S` with `L ≅ i^* O(1)`).  The
statement lives here rather than in `QuotFunctorDef.lean` because the
projectivity vocabulary imports that file; this split mirrors
`Grassmannian.representable` (`GrassmannianRepresentability.lean`).
Everything is at `Scheme.{0}`: `IsProjectiveWith` rests on the Serre twist,
hence on the universe-monomorphic descent engine `Scheme.Modules.glue`
(`GlueDescent.lean`).

The proof is open — the Quot endgame of [Nitsure] §5 (boundedness by
Castelnuovo–Mumford regularity, embedding into a relative Grassmannian,
flattening stratification, valuative criterion); the theorem below is its
single tracked `sorry`.

Blueprint: `thm:quot_representable`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
Source: [Nitsure] §5 (FGA Explained Ch. 5, arXiv:math/0504020).
-/

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-- **Representability of the Quot scheme** (Grothendieck, Altman–Kleiman;
`thm:quot_representable`, [Nitsure] §5 "Main Existence Theorems"): let `S`
be locally noetherian, `π : X ⟶ S` projective carrying the relatively very
ample line bundle `L` (`Scheme.Hom.IsProjectiveWith` — the faithful encoding
settled in inbox `I-0118`), `E` a coherent (finitely presented) sheaf on `X`
and `Φ ∈ ℚ[λ]`.  Then the Quot functor `Quot^{Φ,L}_{E/X/S}` is representable
by an `S`-scheme.  Projectivity supplies finite type
(`IsProjectiveWith.locallyOfFiniteType`), so the statement carries no
separate `[LocallyOfFiniteType π]` binder.

History (inbox `I-0118`): an earlier pin of this theorem hypothesized only
`[IsProper π] [LocallyOfFiniteType π]` over arbitrary quasi-coherent `L` and
arbitrary `E`.  That signature is *not* the cited theorem and is
false-or-open: for merely proper `π` the Quot functor is in general only an
algebraic space (Hironaka's smooth proper non-projective 3-fold gives the
standard counterexample family).

NAMED LEAF (`sorry`): the proof is the [Nitsure] §5 route — boundedness by
Castelnuovo–Mumford `m`-regularity, embedding into a relative Grassmannian
by pushing forward twists (`Grassmannian.representable`,
`GrassmannianRepresentability.lean`), flattening stratification
(`AlgebraicGeometry.flatteningStratification`), and the valuative criterion
for closedness of the locus — and awaits the Serre-finiteness lane
(`sectionGradedModule_fg`, `Picard/SerreFiniteness.lean`, inbox `I-0109`)
plus the Castelnuovo–Mumford boundedness input, which stays a
blueprint-side target for now. -/
theorem QuotScheme {S X : Scheme.{0}} [IsLocallyNoetherian S]
    (π : X ⟶ S) (L E : X.Modules) [L.IsQuasicoherent]
    (hproj : π.IsProjectiveWith L) (hE : E.IsFinitePresentation)
    (Φ : Polynomial ℚ) :
    haveI := hproj.locallyOfFiniteType
    ∃ (Q : Over S), Nonempty ((QuotFunctor π L E Φ).RepresentableBy Q) := by
  sorry

end Scheme

end AlgebraicGeometry
