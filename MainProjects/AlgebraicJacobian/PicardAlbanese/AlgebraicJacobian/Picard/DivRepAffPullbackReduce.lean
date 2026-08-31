/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAffKit
import AlgebraicJacobian.Picard.DivRepClassifyZarSep

/-!
# One fewer obligation on the affine pullback package (F6)

`DivRepAffinePullback` (`Picard/DivRepAffKit.lean`) is the exact output F5 owes before the
affine representability equivalence is packaged.  As landed it demands FOUR fields:
`pull`, `pull_classify`, `isDivRepClassify_pull` and `pull_naturality`.

The separation theorem (`Picard/DivRepClassifyZarSep.lean`) makes `pull_classify`
**redundant**: if the pulled class of every morphism satisfies the characterizing clause
for that morphism, then in particular `pull (classify F)` and `F` are both classified by
`classify F`, so they are equal.  This file records that.

* `AlgebraicGeometry.pull_classify_of_isDivRepClassify_pull` — the reduction, stated for a
  bare `pull` function so it can be used before any package exists.
* `AlgebraicGeometry.DivRepAffinePullback.ofPull` — **the three-field constructor**.  A
  producer now owes `pull`, the clause law, and naturality; the round-trip law is derived.

This does not produce a `DivRepAffinePullback` — there is still no producer of one — but
it removes one of the four obligations from whoever writes it, and it is the obligation
that would otherwise have to be re-proved by a second cover chase.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Grassmannian Scheme

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftDivRepAffReduce :
    C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
  [IsDominant pi]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g : ℕ)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
variable (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
variable (r1 r2 : ℕ)
variable (b1 : Module.Basis (Fin r1) k
  ↥(divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(divisorSections k
    ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤))

local notation "DivOver" =>
  divSchemeOver k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm)

local notation "ChartRing" => fun i j =>
  DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm) i j

local notation "ChartMap" => fun i j =>
  divCarveChartToDivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm) i j

include hO hchi in
/-- **The F5 overlap obligation collapses to a per-chart clause** (the corollary the
separation theorem was for): if each chart pullback of `U` satisfies the characterizing
clause for its own chart morphism, then `U` is compatible.

`DivRepChartFamily.IsCompatible`'s docstring says the universal family will prove it "from
its ε identity AND the total mono theorem".  The mono leg is now unnecessary: two chart
points presenting the SAME morphism `q` give two classes both classified by `q`, and
`eq_of_isDivRepClassify` identifies them.  What is left is exactly the per-chart clause —
i.e. exactly the DDR9-U ε-identity U2 — so the F5 overlap obligation is no longer a second,
separate thing to prove. -/
theorem isCompatible_of_isDivRepClassify_divRepPullAt
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hcl : ∀ {S : Type u} [CommRing S] [Algebra k S]
      (i : (glueData k g r1).J) (j : (glueData k g r2).J)
      (omega : ChartRing i j →ₐ[k] S),
      IsDivRepClassify hpi g r1 r2 b1 b2
        (divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U i j omega)
        (Spec.map (CommRingCat.ofHom omega.toRingHom) ≫ ChartMap i j)) :
    DivRepChartFamily.IsCompatible (hpi := hpi) g r1 r2 b1 b2 U := by
  intro S _ _ i j i' j' omega omega' hq
  refine eq_of_isDivRepClassify hpi g hO hchi r1 r2 b1 b2 _ _ (v := ?_) ?_ ?_
  · exact Spec.map (CommRingCat.ofHom omega.toRingHom) ≫ ChartMap i j
  · exact hcl i j omega
  · exact hq ▸ hcl i' j' omega'

include hO hchi in
/-- **The round-trip law is free once the clause law holds** (F6, via the separation
theorem): if `pull` produces, for every morphism `v`, a class classified by `v`, then it
inverts the backward classifier.

Both `pull S (divRepClassifyZar F)` and `F` satisfy the characterizing clause for the
single morphism `divRepClassifyZar F` — the first by hypothesis, the second by
`divRepClassifyZar_isDivRepClassify` — so `eq_of_isDivRepClassify` identifies them. -/
theorem pull_classify_of_isDivRepClassify_pull
    (pull : ∀ (S : Type u) [CommRing S] [Algebra k S],
      (overSpec k S ⟶ DivOver) → DivFamZar C S pi g)
    (hpull : ∀ (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver),
      IsDivRepClassify hpi g r1 r2 b1 b2 (pull S v) v.left)
    (S : Type u) [CommRing S] [Algebra k S] (F : DivFamZar C S pi g) :
    pull S (divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 S F) = F :=
  eq_of_isDivRepClassify hpi g hO hchi r1 r2 b1 b2 _ F
    (hpull S (divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 S F))
    (divRepClassifyZar_isDivRepClassify hpi g hO hchi r1 r2 b1 b2 F)

namespace DivRepAffinePullback

include hO hchi in
/-- **The three-field constructor of `DivRepAffinePullback`**: the `pull_classify` field is
derived from `isDivRepClassify_pull` by `pull_classify_of_isDivRepClassify_pull`, so a
producer owes only the pullback map, the characterizing clause it satisfies, and
naturality. -/
noncomputable def ofPull
    (pull : ∀ (S : Type u) [CommRing S] [Algebra k S],
      (overSpec k S ⟶ DivOver) → DivFamZar C S pi g)
    (hpull : ∀ (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver),
      IsDivRepClassify hpi g r1 r2 b1 b2 (pull S v) v.left)
    (hnat : ∀ {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
      (phi : A →ₐ[k] B) (v : overSpec k A ⟶ DivOver),
      pull B (Over.overSpecMap phi ≫ v) = DivFamZar.mapAlgHom phi (pull A v)) :
    DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2 where
  pull := pull
  pull_classify := pull_classify_of_isDivRepClassify_pull hpi g hO hchi r1 r2 b1 b2
    pull hpull
  isDivRepClassify_pull := hpull
  pull_naturality := hnat

set_option linter.unusedSectionVars false in
@[simp]
theorem ofPull_pull
    (pull : ∀ (S : Type u) [CommRing S] [Algebra k S],
      (overSpec k S ⟶ DivOver) → DivFamZar C S pi g)
    (hpull : ∀ (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver),
      IsDivRepClassify hpi g r1 r2 b1 b2 (pull S v) v.left)
    (hnat : ∀ {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
      (phi : A →ₐ[k] B) (v : overSpec k A ⟶ DivOver),
      pull B (Over.overSpecMap phi ≫ v) = DivFamZar.mapAlgHom phi (pull A v))
    (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver) :
    (ofPull hpi g hO hchi r1 r2 b1 b2 pull hpull hnat).pull S v = pull S v :=
  rfl

end DivRepAffinePullback

end Curve

end AlgebraicGeometry
