/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartClassUniv

/-!
# U2's scalar side condition is a genus disjunction, not an obligation

`Picard/DivRepChartClassUniv.lean` reduced the DDR9-U ε-identity at the universal point
to two inputs: a certificate `IsCertified g` at the high-window universal seed, and the
scalar `hb : 0 < windowBound π hπ`.  The roadmap leaf `…divrep.u2` then recorded `hb` as
a *side condition to be discharged*, with the warning that `windowBound` is a
`Classical.choose` from a predicate upward-closed in `b`, so "some valid bound is
positive" is trivial while "the chosen one is" is not.

**The warning was right about the shape and wrong about the state.**  The tree already
carries the discharge, and has since the F3 ledger extension:

> `genus_eq_zero_of_windowBound_nonpos` (`RiemannRoch/WindowLedgerF3.lean`) —
> `windowBound ≤ 0` makes `windowBound_spec` fire at the **zero** divisor, so
> `h¹(𝒪) = 0`, and with the normalizations `h⁰(𝒪) = 1`, `χ(𝒪) = 1 − g` that forces
> `g = 0`.

So `hb` is not an obligation: it is a genus disjunction whose degenerate branch is
already proved.  `WindowLedgerF3` itself uses exactly this pattern twice
(`two_mul_genus_le_S_mul_windowδ`, `two_mul_genus_le_M_mul_windowδ`) — every consumer
`by_cases`es on `windowBound ≤ 0` and lands in `g = 0`.

This file draws that consequence for U2's own inputs, at the ledger data U2 uses:
`hO`, `hχ` over `C.left` are exactly `genus_eq_zero_of_windowBound_nonpos`'s
normalizations at `Y = C.left`, `K = k`.  So **`hb` follows from `g ≠ 0`**, and the
ε-identity at the universal point needs no scalar hypothesis once `g ≠ 0` — which every
consumer of a genus-`g` Jacobian has, `g = 0` being the case where `Pic⁰` is trivial.

## Main declarations

* `AlgebraicGeometry.windowBound_pos_of_genus_ne_zero` — `g ≠ 0 → 0 < windowBound π hπ`,
  from the ledger normalizations alone.  General: no seed, no chart, no universal point.
* `AlgebraicGeometry.PointwiseAchiever.divFamEps_highWindow_eq_universal_pair_of_ne_zero`
  — the U2 ε-identity with `hb` replaced by `g ≠ 0`.
* `AlgebraicGeometry.PointwiseAchiever` ·
  `exists_certifiedFamily_divFamEps_eq_universal_pair_of_ne_zero` and `divFamZarUnivOfNeZero`
  — the existential and the `DivFamZar` class, same swap.

## What this does NOT do

It produces no certificate.  U2's residue after this file is **exactly one statement**,
`IsCertified g` at the high-window universal seed's adaptation over the chart ring — no
scalar beside it.  L8 (critical-path §7.6) is untouched and remains the campaign's real
gate.
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

/-! ## The scalar, from the genus -/

section WindowBoundPos

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]
  (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
  (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K))

/-- **The uniform vanishing bound is positive as soon as the genus is** — the
contrapositive of `genus_eq_zero_of_windowBound_nonpos`.

This is the whole discharge of the scalar side condition every high-window declaration
carries as `hb : 0 < windowBound π hπ`.  Nothing about the `Classical.choose` is
inspected: if the chosen bound were `≤ 0` the vanishing it certifies would fire at the
zero divisor, kill `h¹(𝒪_Y)` and force `g = 0` against the hypothesis. -/
theorem windowBound_pos_of_genus_ne_zero (g : ℕ) (hg : g ≠ 0)
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ)) :
    0 < windowBound π hπ := by
  by_contra hb
  exact hg (genus_eq_zero_of_windowBound_nonpos π hπ g (not_lt.mp hb) hO hχ)

end WindowBoundPos

namespace PointwiseAchiever

section UniversalEpsIdentityFree

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftDivRepChartClassUnivFree :
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

include hO hchi in
/-- **The scalar side condition at U2's own ledger data.**  `hO`/`hchi` are stated over
`C.left` with base field `k`, which is exactly the instantiation
`windowBound_pos_of_genus_ne_zero` asks for.

The `include` is load-bearing and was found by the kernel: `hO`/`hchi` appear only in the
PROOF, so without it they are not section variables of this theorem, and the four call sites
below then pass arguments the signature does not have. -/
theorem windowBound_pos_of_ne_zero (hg : g ≠ 0) : 0 < windowBound pi hpi :=
  windowBound_pos_of_genus_ne_zero pi hpi g hg hO hchi

/-- **The DDR9-U ε-identity at the universal point, with no scalar hypothesis.**
Identical to `divFamEps_highWindow_eq_universal_pair` with `hb` replaced by `g ≠ 0`,
which is what a genus-`g` consumer holds. -/
theorem divFamEps_highWindow_eq_universal_pair_of_ne_zero (hg : g ≠ 0)
    (hc : ((univSeed C hpi g r1 r2 b1 b2 i j hO hchi
      (windowBound_pos_of_ne_zero C hpi g hO hchi hg)).divisorAdaptation
      (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi
        (windowBound_pos_of_ne_zero C hpi g hO hchi hg))).IsCertified g) :
    divFamEps hpi g (DivFam.mk
        ((univSeed C hpi g r1 r2 b1 b2 i j hO hchi
            (windowBound_pos_of_ne_zero C hpi g hO hchi hg)).certifiedFamily g
          (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi
            (windowBound_pos_of_ne_zero C hpi g hO hchi hg)) hc))
      = ((divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule,
         (divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule) :=
  divFamEps_highWindow_eq_universal_pair C hpi g r1 r2 b1 b2 i j hO hchi
    (windowBound_pos_of_ne_zero C hpi g hO hchi hg) hc

/-- **The existential form with no scalar hypothesis** — what a chart-class producer
consumes once it knows the genus is nonzero. -/
theorem exists_certifiedFamily_divFamEps_eq_universal_pair_of_ne_zero (hg : g ≠ 0)
    (hc : ((univSeed C hpi g r1 r2 b1 b2 i j hO hchi
      (windowBound_pos_of_ne_zero C hpi g hO hchi hg)).divisorAdaptation
      (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi
        (windowBound_pos_of_ne_zero C hpi g hO hchi hg))).IsCertified g) :
    ∃ G : CertifiedDivisorFamily C RZ pi g,
      divFamEps hpi g (DivFam.mk G)
        = ((divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule,
           (divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule) :=
  ⟨_, divFamEps_highWindow_eq_universal_pair_of_ne_zero
    C hpi g r1 r2 b1 b2 i j hO hchi hg hc⟩

/-- **The `DivFamZar` class of the universal point with no scalar hypothesis.** -/
noncomputable def divFamZarUnivOfNeZero (hg : g ≠ 0)
    (hc : ((univSeed C hpi g r1 r2 b1 b2 i j hO hchi
      (windowBound_pos_of_ne_zero C hpi g hO hchi hg)).divisorAdaptation
      (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi
        (windowBound_pos_of_ne_zero C hpi g hO hchi hg))).IsCertified g) :
    DivFamZar C RZ pi g :=
  divFamZarUniv C hpi g r1 r2 b1 b2 i j hO hchi
    (windowBound_pos_of_ne_zero C hpi g hO hchi hg) hc

end UniversalEpsIdentityFree

end PointwiseAchiever

end AlgebraicGeometry
