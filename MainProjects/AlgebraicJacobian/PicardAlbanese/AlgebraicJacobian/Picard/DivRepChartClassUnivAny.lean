/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartClassUnivFree

/-!
# U2 does not ask about the CHOSEN adaptation: any certified one will do

Every statement of U2's residue so far has been phrased at
`ThetaGeneratorSeed.divisorAdaptation` (`Picard/DivSchemeFamily.lean`), which is a
`Classical.choose` — `(exists_divisorAdaptation …).some`.  So the recorded obligation reads

> `IsCertified g` **for the adaptation the extraction happened to pick**

and a producer that builds its own adaptation cannot discharge it, however good that
adaptation is.  **That is an artefact of the spelling, not of the mathematics**, and the
two landed facts that say so are one line each:

* `divisorWindow` "depends only on `d`, not on any chart adaptation" — its own docstring
  (`Picard/DivisorFamilyWindow.lean`), and `divFamEps` is two `divisorWindow`s;
* `divisorWindow_eq_of_le_of_isCertified` (`Picard/DivSchemeEps.lean`) takes an
  **arbitrary** `A : DivisorAdaptation C R π d` and concludes about `d` alone;
* `CertifiedDivisorFamily` (`Picard/DivisorFamily.lean`) is a *triple* `(eqns, adaptation,
  certified)` whose `adaptation` field is any adaptation of `eqns` — it never mentions the
  extraction.

So the honest residue is the existential below, and this file states it and re-derives the
whole U2 package from it.  The gain is not a shorter proof; it is that a producer may now
**supply its own adaptation**, which is what any certificate-assembly route does (it builds
a cover, adapts to it, and certifies *that*).

## Main declarations

* `AlgebraicGeometry.ThetaGeneratorSeed.HasCertifiedAdaptation` — the residue: *some*
  adaptation of the seed's local-equation system carries a degree-`n` certificate.
* `AlgebraicGeometry.ThetaGeneratorSeed.certifiedFamilyOfAdaptation` and
  `divFamEps_certifiedFamilyOfAdaptation` — the ε-projection identity from a certificate at
  an arbitrary adaptation, the general (seed-level, no chart) form.
* `AlgebraicGeometry.PointwiseAchiever` ·
  `exists_divFamZar_divFamEps_eq_universal_pair_of_hasCertifiedAdaptation`
  — U2's ε-identity **and** the `DivFamZar` class over the chart ring, from
  `HasCertifiedAdaptation` plus `g ≠ 0`, i.e. from the weakest form of the certificate
  obligation with no scalar side condition.

## What this does NOT do

It produces no certificate and no adaptation, so no gate clears.  What changes is the shape
of the debt: an existential over adaptations rather than a property of a `Classical.choose`.
Critical-path §7.6 (L8) is untouched.

**One thing it deliberately does not claim.**  It does not bridge
`AffAdaptation.IsCertified` (the widened R2 carrier, `Picard/DivisorFamilyAffAdaptation.lean`)
to `DivisorAdaptation.IsCertified`.  `DivisorAdaptation` extends `FinCoverData`, so a
widened cover has no chart typing to recover and manufacturing one is what protection
`I-0492` clause 3 forbids.  This file makes the *chart-typed* obligation as weak as it can
be; re-typing the ε layer onto the widened adaptation remains the open seam.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 16000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

/-! ## The residue, at the seed level -/

namespace ThetaGeneratorSeed

section AnyAdaptation

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftUnivAny :
    C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
  [IsDominant π]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable {a : ℕ} {K : Submodule R (relThetaSections C R π a)}

/-- **The certified family of an ARBITRARY adaptation** — `CertifiedDivisorFamily` is the
triple `(eqns, adaptation, certified)`, so nothing forces `adaptation` to be the extraction
`ThetaGeneratorSeed.divisorAdaptation`.  This is `certifiedFamily` with the
`Classical.choose` removed. -/
noncomputable def certifiedFamilyOfAdaptation [IsNoetherianRing R] {n : ℕ}
    (D : ThetaGeneratorSeed C R π a K) (hD : D.IsGenerator)
    (A : DivisorAdaptation C R π (D.localEquations hD)) (hc : A.IsCertified n) :
    CertifiedDivisorFamily C R π n where
  eqns := D.localEquations hD
  adaptation := A
  certified := hc

/-- **The ε-projection identity from a certificate at an arbitrary adaptation.**

Verbatim `ThetaGeneratorSeed.divFamEps_certifiedFamily` with `D.divisorAdaptation hD`
replaced by a variable `A`.  The proof is the same composition, and it goes through for a
structural reason worth naming: `divFamEps` is two `divisorWindow`s, `divisorWindow` reads
only the local-equation system, and `divisorWindow_eq_of_le_of_isCertified` quantifies over
the adaptation.  The first-window containment is DDR-3's `le_vanishingSubmodule` (about the
seed, not the adaptation); the surjectivities come from `A`'s own certificate. -/
theorem divFamEps_certifiedFamilyOfAdaptation [IsNoetherianRing R] {g : ℕ}
    (x₁ : Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) g R)
    (x₂ : Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) g R)
    (D : ThetaGeneratorSeed C R π (windowM_choice π hπ g)
      (Submodule.map
        (relThetaWindowEquiv C R π (windowM_choice π hπ g)
          (relThetaPairH1_windowM C π hπ g)).toLinearMap x₁.toSubmodule))
    (hD : D.IsGenerator)
    (A : DivisorAdaptation C R π (D.localEquations hD)) (hc : A.IsCertified g)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hle₂ : x₂.toSubmodule ≤
      divisorWindow (D.localEquations hD) (relThetaPairH1_windowMS C π hπ g)) :
    divFamEps hπ g (DivFam.mk (D.certifiedFamilyOfAdaptation hD A hc))
      = (x₁.toSubmodule, x₂.toSubmodule) :=
  divFamEps_mk_eq_of_le hπ (D.certifiedFamilyOfAdaptation hD A hc) x₁ x₂
    (DivisorAdaptation.IsCertified.thetaGluedEval_surjective C π hπ hc hO hχ
      (relThetaPairH1_windowM C π hπ g) le_rfl)
    (DivisorAdaptation.IsCertified.thetaGluedEval_surjective C π hπ hc hO hχ
      (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _))
    (Submodule.map_le_iff_le_comap.mp (D.le_vanishingSubmodule hD)) hle₂

/-- **The residue, named**: *some* adaptation of the seed's local-equation system carries a
degree-`n` certificate.  This is the weakest form of the G-4 obligation a producer can be
asked for — it lets the producer choose the cover and the adaptation, which every
certificate-assembly route does. -/
def HasCertifiedAdaptation [IsNoetherianRing R] (n : ℕ)
    (D : ThetaGeneratorSeed C R π a K) (hD : D.IsGenerator) : Prop :=
  ∃ A : DivisorAdaptation C R π (D.localEquations hD), A.IsCertified n

/-- The `Classical.choose`n adaptation being certified is a *special case* of the residue —
recorded so the relation between the old spelling and the new one is a lemma, not prose. -/
theorem hasCertifiedAdaptation_of_divisorAdaptation [IsNoetherianRing R] {n : ℕ}
    (D : ThetaGeneratorSeed C R π a K) (hD : D.IsGenerator)
    (hc : (D.divisorAdaptation hD).IsCertified n) :
    D.HasCertifiedAdaptation n hD :=
  ⟨D.divisorAdaptation hD, hc⟩

end AnyAdaptation

end ThetaGeneratorSeed

/-! ## U2 from the weakened residue -/

namespace PointwiseAchiever

section UniversalAnyAdaptation

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftUnivAnyChart :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k
    (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k
    ((windowS_choice pi hpi g • fiberWeilDivisor pi) +
      (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j

set_option maxHeartbeats 2400000 in
-- The universal instantiation unfolds `DivCarveChartRing` (an `Ideal.Quotient`) while
-- unifying `glueData`'s `ULift` index, over the `relThetaSections` tower: the same defeq
-- profile as `divFamEps_highWindow_eq_universal_pair`, which is budgeted identically.
set_option synthInstance.maxHeartbeats 800000 in
/-- **U2's ε-identity and its `DivFamZar` class from the WEAKEST certificate obligation.**

Inputs: `g ≠ 0` (which discharges the scalar, `Picard/DivRepChartClassUnivFree.lean`) and
`HasCertifiedAdaptation` at the high-window universal seed — *some* adaptation certified,
not the extraction's.  Output: a locally certified class over the chart ring whose `ε` is
the universal tautological pair, i.e. exactly what U2 asks a producer to exhibit.

The two are packaged together on purpose: a class without its ε-value does not serve
`isChartClause_iff_forall_classify_eq` (`Picard/DivRepChartRange.lean`), and an ε-value
without the class cannot be fed to it.

**WARNING, and read it before planning off this theorem** (inbox `I-0705`, confirmed by the
no-go's owner): the hypothesis `HasCertifiedAdaptation` is **refuted** by
`forall_not_isCertified_of_straddling` (`Picard/DivisorFamilyAffStrict.lean:127`) whenever the
seed's local equations are connected and meet both pinned fibres — that theorem concludes
`∀ A n, ¬ A.IsCertified n`, which is this existential's negation at the same binder.  Whether
the high-window universal seed straddles in that sense is **unmeasured**, and the same no-go
refutes the older `(D.divisorAdaptation hD).IsCertified g` spelling too, since that is one
instance of its `∀`.  So this theorem is a sound *reduction* whose hypothesis may be false;
do not read it as "U2 is one certificate away". -/
theorem exists_divFamZar_divFamEps_eq_universal_pair_of_hasCertifiedAdaptation
    (hg : g ≠ 0)
    (hca : (univSeed C hpi g r1 r2 b1 b2 i j hO hchi
        (windowBound_pos_of_ne_zero C hpi g hO hchi hg)).HasCertifiedAdaptation
      g (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi
        (windowBound_pos_of_ne_zero C hpi g hO hchi hg))) :
    ∃ G : CertifiedDivisorFamily C RZ pi g,
      divFamEps hpi g (DivFam.mk G)
        = ((divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule,
           (divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule) := by
  obtain ⟨A, hc⟩ := hca
  -- The witness is named explicitly rather than left to `refine ⟨_, ?_⟩`: with the
  -- adaptation coming from the existential, the placeholder is not determined by the
  -- goal and the elaborator leaves it open (measured -- the kernel reported an unsolved
  -- goal at exactly this shape).
  exact ⟨_, ThetaGeneratorSeed.divFamEps_certifiedFamilyOfAdaptation hpi
    (divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j)
    (divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j)
    (univSeed C hpi g r1 r2 b1 b2 i j hO hchi
      (windowBound_pos_of_ne_zero C hpi g hO hchi hg))
    (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi
      (windowBound_pos_of_ne_zero C hpi g hO hchi hg))
    A hc hO hchi
    (divUniversalSndWindow_le_highWindow_divisorWindow C hpi g r1 r2 b1 b2 i j hO hchi
      (windowBound_pos_of_ne_zero C hpi g hO hchi hg))⟩

/-- **The `DivFamZar` class over the chart ring from the weakened residue** — a global
certificate is a local one through the trivial one-member cover, so no Zariski shrinking is
involved. -/
noncomputable def divFamZarUnivOfHasCertifiedAdaptation (hg : g ≠ 0)
    (hca : (univSeed C hpi g r1 r2 b1 b2 i j hO hchi
        (windowBound_pos_of_ne_zero C hpi g hO hchi hg)).HasCertifiedAdaptation
      g (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi
        (windowBound_pos_of_ne_zero C hpi g hO hchi hg))) :
    DivFamZar C RZ pi g :=
  DivFamZar.mk
    (exists_divFamZar_divFamEps_eq_universal_pair_of_hasCertifiedAdaptation
      C hpi g r1 r2 b1 b2 i j hO hchi hg hca).choose.eqns
    (exists_divFamZar_divFamEps_eq_universal_pair_of_hasCertifiedAdaptation
      C hpi g r1 r2 b1 b2 i j hO hchi hg hca).choose.isLocallyCertified

end UniversalAnyAdaptation

end PointwiseAchiever

end AlgebraicGeometry
