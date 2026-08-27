/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.QuasiProjectiveFiniteInAffine
import AlgebraicJacobian.Projective.EffectiveCartierSupport
import AlgebraicJacobian.Projective.Grassmannian

/-!
# Demand ledger for projective-morphism infrastructure

This file records the projective infrastructure demanded by the Picard
representability seam.  It is a ledger, not a second projectivity API.

## A seam-facing sufficient producer

`Scheme.PointedPicSharpRep` asks for a representing scheme that is locally of
finite type and satisfies `Scheme.FiniteInAffine`.  It does not ask for a line
bundle.  The existing project-local route supplies those two side conditions
from a coproduct of H-quasi-projective pieces:

* `Scheme.Hom.IsHQuasiProjective` is the universe-polymorphic embedding
  predicate from `Picard/ProjectiveMorphismBasic.lean`;
* `Scheme.locallyOfFiniteType_sigma` and
  `Scheme.finiteInAffine_over_sigma_of_isHQuasiProjective` aggregate the two
  side conditions in `Picard/QuasiProjectiveFiniteInAffine.lean`;
* at `Scheme.{0}`, `Scheme.Hom.IsHQuasiProjective.exists_isHQuasiProjectiveWith`
  adds a carried pullback of `O(1)`.  Thus the existing
  `IsHQuasiProjectiveWith` is already the required very-ample output; defining
  an alias named `IsVeryAmple` would only re-spell it.

A strong sufficient producer is recorded as
`pointedPicSharpQuasiProjectivePieces_demand`: if proved, it would construct the
representing coproduct and prove H-quasi-projectivity piecewise.  It is not the
minimal seam price: `HasGoodGaloisLevel` and `seamClauseOne` expose a weaker
single-finite-Galois-level route.  The two proved adapters below are only typing
and consumption checks.  They both assume `H`, whose closed proposition
packages the representation witness; they produce no representation and do not
reduce the current seam debt.  Their signatures add no explicit
`RepresentableBy` argument.

## The D4' Grassmannian demand

The committed divisor route has one narrower projective consumer before the
Picard-piece producer exists.  D3' must carve a scheme `Z` with a quasi-compact
immersion into the chosen scheme representing a Grassmannian over a field.  D4'
then needs `Z` to be H-quasi-projective so that its finite point sets lie in
affine opens.  The existing `IsHQuasiProjective.comp_isImmersion` performs the
last step. The field representer is now supplied directly by
`Scheme.Grassmannian.representingScheme_isHQuasiProjective_of_field`.

`Projective/Grassmannian.lean` proves the field-specialised transport: it derives
global freeness on `Spec K`, base-changes the absolute Grassmannian, and uses
uniqueness of representing objects. `Projective/GrassmannianProjective.lean`
now supplies the absolute certificate by the Plucker embedding. Properness of
the absolute Grassmannian is combined there with the proved immersion into
relative projective space; properness alone would not imply the project-local
definition of H-quasi-projectivity.

## The finite-fibre part of D3'

`Projective/EffectiveCartierSupport.lean` now proves that the schematic support
of every `DivFamily` on a proper smooth geometrically integral relative curve
has finite set-theoretic fibres.  It immediately consumes that theorem through
the existing `DivFamily.locallyQuasiFinite_of_finite_fibers` reduction and
registers the resulting instance.  The synthesis theorem below checks the exact
binder used by `DivPushforwardFlat`; it is not a second quasi-finiteness API.

This closes only the finite-fibre geometric input of D3'.  Constructing the
whole-fibre `ExistsUnique` Grassmannian locus remains open.

## No current section-Proj demand

Mathlib's `AlgebraicGeometry.Proj` is the Proj of an `N`-graded commutative
ring, not a relative Proj of a sheaf of graded algebras.  The project has enough
section-ring data to make that absolute Proj elaborate after two elementary
structure assemblies, but no Picard declaration consumes it: there is no
intrinsic `picSharpDeg` carrier, representing scheme for such a component, or
Picard-piece line bundle from which to form the section ring.  Consequently
those assemblies are not demands of the seam and are deliberately absent from
this ledger.

The live predecessor is the intrinsic degree and representation construction;
only that construction can expose a narrower Proj or ampleness signature.  A
general relative-Proj gluing theory or a general ample predicate must not be
built before then.  The whole Picard scheme must also not be strengthened to
`IsProjective`: its degree-graded coproduct is not quasi-compact, as recorded by
`Picard/AmbientPicNotProper.lean` and `Scheme.PointedPicSharpRepProjective`.

## Existing inputs

Curve projectivity is already produced by
`Adelic.isProjective_of_smoothProperGeometricallyIntegral`.  The carried
`O(1)`, base-change and open-image transport, `FiniteInAffine` transport, and
Over-coproduct assembly remain owned by the established Picard modules and are
imported here read-only.
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme

/-- A sufficient projective presentation that the pointed Picard reduction can
consume at every universe: `picSharp` is represented by a coproduct of
H-quasi-projective schemes over the ground field.

The integer index records the intended degree pieces without introducing a
second, currently nonexistent `picSharpDeg` functor.  This closed proposition
contains the representation witness in its conclusion; no downstream theorem
takes an explicit representation-witness argument.  This keeps the strict
binder count unchanged, but it remains logically a representation assumption. -/
def PointedPicSharpQuasiProjectivePieces : Prop :=
  ∀ {K : Type u} [Field K] (E : Over (Spec (CommRingCat.of K))),
    ∀ [SmoothOfRelativeDimension 1 E.hom] [IsProper E.hom]
      [GeometricallyIntegral E.hom],
      HasRationalPoint E →
        ∃ X : ℤ → Over (Spec (CommRingCat.of K)),
          Nonempty ((PicScheme.picSharp E).RepresentableBy (∐ X)) ∧
            ∀ d, (X d).hom.IsHQuasiProjective

/-- A piecewise H-quasi-projective representation supplies exactly the local
finite type and `FiniteInAffine` conjuncts of `PointedPicSharpRep`.

This is the seam-side typecheck for the ledger, not producer movement. -/
theorem pointedPicSharpRep_of_quasiProjectivePieces
    (H : PointedPicSharpQuasiProjectivePieces.{u}) :
    PointedPicSharpRep.{u} := by
  intro K _ E _ _ _ hpt
  obtain ⟨X, hrep, hX⟩ := H E hpt
  refine ⟨∐ X, hrep, ?_, ?_⟩
  · exact locallyOfFiniteType_sigma X fun d => (hX d).locallyOfFiniteType
  · exact finiteInAffine_over_sigma_of_isHQuasiProjective X hX

/-- Conditional on the open ledger demand, the central seam follows verbatim,
with no rational point binder on the target theorem.  This adapter is not a
sorry-free producer or a discharge of the seam. -/
theorem fgaPicardRepresentability_of_quasiProjectivePieces
    {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom]
    (H : PointedPicSharpQuasiProjectivePieces.{u}) :
    (∃ X : Over (Spec (CommRingCat.of k)),
        Nonempty ((PicScheme.picEt C).RepresentableBy X) ∧
          LocallyOfFiniteType X.hom ∧ IsSeparated X.hom) ∧
      (HasRationalPoint C → IsIso (PicScheme.picEtComparison C)) :=
  fgaPicardRepresentability_of_pointedPicSharpRep C
    (pointedPicSharpRep_of_quasiProjectivePieces H)

/-- **Open sufficient producer.** Construct the pointed Picard representer as a
coproduct of H-quasi-projective pieces.  This is deliberately stronger than the
single-finite-Galois-level price of seam clause one. -/
theorem pointedPicSharpQuasiProjectivePieces_demand :
    PointedPicSharpQuasiProjectivePieces.{u} := by
  sorry

end Scheme

namespace Scheme
namespace DivFamily

/-- The finite-fibre producer is visible at the demand ledger and discharges
the exact locally-quasi-finite binder carried by the divisor pushforward
theorems.  The remaining D3' demand is the whole-fibre `ExistsUnique` locus. -/
theorem d3Support_locallyQuasiFinite_of_curve
    {S X : Scheme.{u}} {π : X ⟶ S} {T : Over S}
    [SmoothOfRelativeDimension 1 π] [GeometricallyIntegral π] [IsProper π]
    (x : DivFamily π T) :
    LocallyQuasiFinite
      (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) := by
  infer_instance

end DivFamily
end Scheme

namespace Scheme
namespace Grassmannian

/-- A quasi-compact D3' immersion into an H-quasi-projective Grassmannian gives
the exact H-quasi-projectivity certificate carried by D4'.

This is a typing check for the demand above, not a construction of the missing
D3' locus or of the ambient Grassmannian certificate. -/
theorem d4Locus_isHQuasiProjective_over
    {S : Scheme.{0}} [IsLocallyNoetherian S]
    {V : S.Modules} {r d : ℕ}
    (hV : SheafOfModules.IsLocallyFreeOfRank V r)
    (hd : 1 ≤ d) (hdr : d ≤ r)
    (Z : Over S)
    (j : Z ⟶ representingScheme hV hd hdr)
    [IsImmersion j.left] [QuasiCompact j.left]
    (hGr : (representingScheme hV hd hdr).hom.IsHQuasiProjective) :
    Z.hom.IsHQuasiProjective := by
  rw [← j.w]
  exact hGr.comp_isImmersion j.left

end Grassmannian
end Scheme
end AlgebraicGeometry
