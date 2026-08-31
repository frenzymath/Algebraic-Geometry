/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffZar
import AlgebraicJacobian.Picard.DivRepClassifyZarKit
import AlgebraicJacobian.Picard.DivCarvePairChart
import AlgebraicJacobian.Picard.GrassmannianGlue

/-!
# The ε-pair and its pair-chart framing are CARRIER-INDIFFERENT

The DD-R representability consumer asks for the chart-typed value: `divRepClassifyZar`
(`Picard/DivRepClassifyZar.lean`) and `divFunctor_representableBy_of_chartRange`
(`Picard/DivRepChartRange.lean`) both quantify over `DivFamZar`, and the chart data they need
comes from `DivFamZar.exists_certChartCover` (`Picard/DivRepClassifyZarKit.lean`).  Since the
widened comparison `DivFamZar.toAff` runs chart-typed → widened and has no reverse (a widened
cover has no chart typing to recover, and manufacturing one is the fixed-pair confinement that
protection I-0492 clause 3 forbids), it is natural to read this as "R2 has not reached the
consumer".

**That reading is wrong, and this file measures why.**  The chart dependency of
`exists_certChartCover` does not run through the divisor's *cover* at all.  It runs through the
**window**:

* `divFamEps` (`Picard/DivisorFamilyWindow.lean`) is `divisorWindow G.eqns` at two windows, and
  `eqns : (relCurve C R).LocalEquations` is a field of `CertifiedDivisorFamilyAff` exactly as it
  is of `CertifiedDivisorFamily`.  The cover never enters.
* the framing clause is two equations between submodules of `R ⊗[k] H`, comparing
  `Module.Grassmannian.map w` of a tautological subbundle against the base change of the window.
  Neither side mentions a cover, a piece, or a chart typing of the divisor.

So "which carrier the certificate lives on" and "where the ε-pair sits in the Grassmannian" are
independent questions, and the widening is invisible to the second.  The declarations below say
that in Lean rather than in prose: both are *statements* about a widened family, and their
elaboration is the content.

## What this does NOT claim

It does not prove `exists_certChartCover` over the widened carrier.  What is established here is
that no *type* obstruction stands in the way: the clause is expressible, so the remaining
question is a proof, not a redesign.

**A previous version of this paragraph priced that remaining proof as "runs the certificate
cover and the per-piece frame covers, which is real work".  That over-priced it, and the reason
generalises** (measured 2026-07-30, `Picard/DivisorFamilyAffFrameCover.lean`, inbox `I-1327`):
`divFamEps_exists_frameCover` reads its *carrier* at exactly three points, all inside
`exists_frame_chart_at_prime` — `Module.Finite`, `Module.Projective` and `rankAtStalk = g` of the
window quotient `(R ⊗[k] H_a) ⧸ F.window`.  Everything below them takes a Grassmannian *point*
and a base ring and cannot see what produced the submodule, and `divisorWindow` names no
adaptation, cover or chart typing.  So the cover that proof runs belongs to `d`, which **both**
carriers share.  A proof that "runs a cover" is chart-dependent only if the cover is indexed by
the chart typing.

The step that *was* real, and which the old pricing did not name, is the tower transport:
`map_divFamWindowGr` obtains its composite from `DivFam.mapAlg_comp`, i.e. from the carrier's own
functoriality, so carrier-free it has to be proved on the submodule
(`windowBaseChange_windowBaseChange`, new).  None of this discharges an antecedent — see that
file's `Reachability` section for the no-go that still blocks the widened side.

## Main declarations

* `AlgebraicGeometry.CertifiedDivisorFamilyAff.eps` — the ε-pair of a **widened** certified
  family, computed from its `eqns` alone.
* `AlgebraicGeometry.CertifiedDivisorFamilyAff.IsPairChartFramed` — the framing clause of
  `exists_certChartCover`, stated over the widened carrier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry

open Grassmannian Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]
variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
variable [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k ((Scheme.moduleKSheaf k C.left).HModule 0)]
variable [Module.Finite k ((Scheme.moduleKSheaf k C.left).HModule 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (.of k)) (g : ℕ)

namespace CertifiedDivisorFamilyAff

-- the window's `H`-finiteness instances are found through the moduleKSheaf tower, which
-- exceeds the default instance budget
set_option synthInstance.maxHeartbeats 800000 in
/-- **The ε-pair of a WIDENED certified family.**  Verbatim `divFamEps`, with the widened
carrier in place of the chart-typed one — which type-checks because both carriers have the same
`eqns : LocalEquations` field and `divisorWindow` reads nothing else.

This is the declaration that refutes "the ε-pair needs the chart-typed value". -/
noncomputable def eps (F : CertifiedDivisorFamilyAff C R g) :
    Submodule R (R ⊗[k]
        ↥(Scheme.divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
      × Submodule R (R ⊗[k] ↥(Scheme.divisorSections k
          ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤)) :=
  (divisorWindow F.eqns (relThetaPairH1_windowM C pi hpi g),
   divisorWindow F.eqns (relThetaPairH1_windowMS C pi hpi g))

variable {r₁ r₂ : ℕ}
variable (b₁ : Module.Basis (Fin r₁) k ↥(Scheme.divisorSections k
  (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k ↥(Scheme.divisorSections k
  ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤))

-- same instance tower as `eps`, plus the Grassmannian side
set_option synthInstance.maxHeartbeats 800000 in
/-- **The pair-chart framing clause, over the WIDENED carrier.**  Exactly the two Grassmannian
equations of `DivFamZar.exists_certChartCover`, with `divFamEps (DivFam.mk G)` replaced by
`F.eps`.

That this elaborates is the point: the framing is a condition on where the ε-pair sits in the
Grassmannian, and the ε-pair does not know which cover certified the family.  So no *type*
obstruction separates the widened carrier from the chart-cover extraction the representability
consumer runs — see the module docstring for what is still owed. -/
def IsPairChartFramed (F : CertifiedDivisorFamilyAff C R g)
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] R) : Prop :=
  (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange R b₁.equivFun.toLinearMap)
        (F.eps hpi g).1
    ∧ (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange R b₂.equivFun.toLinearMap)
        (F.eps hpi g).2

-- `rfl`, but the window unfolds through the section-ring algebra instances and exceeds the
-- default recursion depth on the way
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
/-- The ε-pair of a widened family is its two windows, by definition.  Recorded because it is
the seam a restatement of `exists_certChartCover` would rewrite along. -/
@[simp]
lemma eps_fst (F : CertifiedDivisorFamilyAff C R g) :
    (F.eps hpi g).1 = divisorWindow F.eqns (relThetaPairH1_windowM C pi hpi g) := rfl

-- as `eps_fst`
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
@[simp]
lemma eps_snd (F : CertifiedDivisorFamilyAff C R g) :
    (F.eps hpi g).2 = divisorWindow F.eqns (relThetaPairH1_windowMS C pi hpi g) := rfl

end CertifiedDivisorFamilyAff

end AlgebraicGeometry
