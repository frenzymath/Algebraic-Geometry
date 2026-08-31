/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAffKit

/-!
# F5, the overlap agreement of the forward map (`informal/w4-ddr9-worksheet.md` §3.4)

The affine forward map of DDR-9 is built by factorizing a morphism `v : overSpec k S ⟶ DivOver`
through the carve-chart atlas (`divScheme_exists_chartFactor`,
`Picard/DivSchemeAtlasFactor.lean:382` — landed), pulling the supplied universal chart family
back along each factorizing chart map (`divRepPullAt`), and gluing the resulting locally
certified classes (`DivFamZar.exists_glue_of_away_compat`).

Gluing needs the pieces to agree on overlaps.  This file proves that they do, from the chart
family's own compatibility hypothesis and nothing else:

* `AlgebraicGeometry.divRepPullAt_mapAlgHom_eq_of_chartFactor` — **the overlap agreement**.
  Two chart presentations of the SAME `v`, over two carriers `A`, `A'`, restrict to the same
  locally certified class over any common `k`/`S`-tower ring `B`.

This is the whole of §3.4's family-side W3, and it is free of the DDR9-U ε-identity U2: the
overlap of two presentations of one morphism is exactly the input `DivRepChartFamily.IsCompatible`
is stated to supply.  U2 is what will *prove* `IsCompatible` for the universal family; it is not
needed to *use* it.

What remains for the forward map after this file is the choice bookkeeping (glue, then show the
glued class is independent of the factorization) and the two U2-gated laws; see the roadmap row
`AJCR.w4-rep.datum.dat-d.ddr.divrep`.
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

noncomputable local instance instOverCleftDivRepAffOverlap :
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

set_option linter.unusedSectionVars false in
/-- (Implementation) A chart presentation of `v` over a carrier `A` pushes to any common
`k`/`S`-tower ring `B`: the presenting chart map composes with the structure map. -/
private theorem specMap_chartMap_pushforward
    {S : Type u} [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver)
    {A B : Type u} [CommRing A] [Algebra k A] [Algebra S A] [IsScalarTower k S A]
    [CommRing B] [Algebra k B] [Algebra S B] [IsScalarTower k S B]
    [Algebra A B] [IsScalarTower k A B] [IsScalarTower S A B]
    {i : (glueData k g r1).J} {j : (glueData k g r2).J}
    (omega : ChartRing i j →ₐ[k] A)
    (homega : Spec.map (CommRingCat.ofHom omega.toRingHom) ≫ ChartMap i j
      = Spec.map (CommRingCat.ofHom (algebraMap S A)) ≫ v.left) :
    Spec.map (CommRingCat.ofHom ((IsScalarTower.toAlgHom k A B).comp omega).toRingHom)
        ≫ ChartMap i j
      = Spec.map (CommRingCat.ofHom (algebraMap S B)) ≫ v.left := by
  have hAB : CommRingCat.ofHom omega.toRingHom ≫ CommRingCat.ofHom (algebraMap A B)
      = CommRingCat.ofHom ((IsScalarTower.toAlgHom k A B).comp omega).toRingHom := by
    rw [← CommRingCat.ofHom_comp]
    rfl
  have hSB : CommRingCat.ofHom (algebraMap S A) ≫ CommRingCat.ofHom (algebraMap A B)
      = CommRingCat.ofHom (algebraMap S B) := by
    rw [← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  rw [← hAB, Spec.map_comp, Category.assoc, homega, ← Category.assoc, ← Spec.map_comp, hSB]

set_option maxHeartbeats 800000 in
-- The two `divRepPullAt` composites unfold `DivFamZar.mapAlgHom` through the chart-ring
-- notation; the defeq check is what costs (I-0227 budget).
set_option linter.unusedSectionVars false in
/-- **The F5 overlap agreement** (w4-ddr9 §3.4, family-side W3): if two carve-chart
presentations `(i, j, ω)` over `A` and `(i', j', ω')` over `A'` present the SAME morphism
`v : overSpec k S ⟶ DivOver`, then the classes they pull back from a compatible universal
chart family agree after restriction to any common `k`/`S`-tower ring `B`.

This is the hypothesis `DivFamZar.exists_glue_of_away_compat` consumes, and it is free of
the DDR9-U ε-identity: `DivRepChartFamily.IsCompatible` is precisely the statement that two
chart points inducing the same morphism to `DivScheme` have equal pulled classes, and both
presentations induce `Spec.map (algebraMap S B) ≫ v.left` after pushforward.  U2 is what
will prove `IsCompatible` for the universal family, not what is needed to use it. -/
theorem divRepPullAt_mapAlgHom_eq_of_chartFactor
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hU : DivRepChartFamily.IsCompatible (hpi := hpi) g r1 r2 b1 b2 U)
    {S : Type u} [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver)
    {A A' B : Type u}
    [CommRing A] [Algebra k A] [Algebra S A] [IsScalarTower k S A]
    [CommRing A'] [Algebra k A'] [Algebra S A'] [IsScalarTower k S A']
    [CommRing B] [Algebra k B] [Algebra S B] [IsScalarTower k S B]
    [Algebra A B] [IsScalarTower k A B] [IsScalarTower S A B]
    [Algebra A' B] [IsScalarTower k A' B] [IsScalarTower S A' B]
    {i : (glueData k g r1).J} {j : (glueData k g r2).J}
    {i' : (glueData k g r1).J} {j' : (glueData k g r2).J}
    (omega : ChartRing i j →ₐ[k] A) (omega' : ChartRing i' j' →ₐ[k] A')
    (homega : Spec.map (CommRingCat.ofHom omega.toRingHom) ≫ ChartMap i j
      = Spec.map (CommRingCat.ofHom (algebraMap S A)) ≫ v.left)
    (homega' : Spec.map (CommRingCat.ofHom omega'.toRingHom) ≫ ChartMap i' j'
      = Spec.map (CommRingCat.ofHom (algebraMap S A')) ≫ v.left) :
    DivFamZar.mapAlgHom (IsScalarTower.toAlgHom k A B)
        (divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U i j omega)
      = DivFamZar.mapAlgHom (IsScalarTower.toAlgHom k A' B)
        (divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U i' j' omega') := by
  have h1 := divRepPullAt_comp (hpi := hpi) g r1 r2 b1 b2 U i j omega
    (IsScalarTower.toAlgHom k A B)
  have h2 := divRepPullAt_comp (hpi := hpi) g r1 r2 b1 b2 U i' j' omega'
    (IsScalarTower.toAlgHom k A' B)
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact hU i j i' j' _ _
    ((specMap_chartMap_pushforward hpi g r1 r2 b1 b2 v omega homega).trans
      (specMap_chartMap_pushforward hpi g r1 r2 b1 b2 v omega' homega').symm)

end Curve

end AlgebraicGeometry
