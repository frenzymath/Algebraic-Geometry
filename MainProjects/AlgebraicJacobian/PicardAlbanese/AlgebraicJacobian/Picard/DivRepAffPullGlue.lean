/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAffChartOverlap
import AlgebraicJacobian.Picard.DivRepAwaySpanGlue

/-!
# F5 — gluing the chart pulls of one morphism (`informal/w4-ddr9-worksheet.md` §3.4)

The affine forward map of DDR-9 is built from three landed pieces:

1. the atlas factorization `divScheme_exists_chartFactor`
   (`Picard/DivSchemeAtlasFactor.lean`) — a morphism `v : overSpec k S ⟶ DivOver`
   factors, over a finite spanning family `f : Fin m → S`, through carve charts along
   `k`-algebra maps `ω t : R_Z →ₐ[k] Localization.Away (f t)`;
2. the per-chart pull `divRepPullAt` (`Picard/DivRepAffKit.lean`) of a supplied
   universal chart family of `DivFamZar` classes;
3. the overlap agreement `divRepPullAt_mapAlgHom_eq_of_chartFactor`
   (`Picard/DivRepAffChartOverlap.lean`) — two chart presentations of the *same* `v`
   pull to the same class over any common tower ring.

What was missing between them is the glue itself, and the reason is mechanical rather
than mathematical: (3) is stated over an abstract common ring `B` with an instance pack
in scope, while the gluing keystone needs the *canonical* overlap carrier
`Localization.Away (f p * f q)` together with its eight-field pack.
`Picard/DivRepAwaySpanGlue.lean` supplies that pack; this file uses it.

* `AlgebraicGeometry.divRepPullAt_awayMul_compat` — **the overlap hypothesis in the
  canonical spelling**: the chart pulls of the pieces of one factorization agree along
  the two comparison maps into `Localization.Away (f p * f q)`.  This is (3) at the
  canonical carrier, with the comparison maps identified with the structure maps of the
  instance pack.
* `AlgebraicGeometry.exists_divRepPullGlue` — **the glued pull**: the chart pulls glue
  to a class over `S` restricting to each piece.
* `AlgebraicGeometry.existsUnique_divRepPullGlue` — the glued class is the *unique* one
  restricting to the pieces, so it is determined by the factorization data.

Together these are the whole of the `pull` field's construction over a *given*
factorization.  Independence of the choice of factorization is a separate statement, proved
in `Picard/DivRepAffPullIndep.lean` — and it turned out **not** to need the DDR9-U ε-identity
U2 either, for the reason given in that file's header (the overlap lemma quantifies over two
*independent* presentations of one morphism).  An earlier version of this paragraph asserted
the opposite; it was written before that was checked.  Everything in this file is U2-free: it
consumes `DivRepChartFamily.IsCompatible` as a hypothesis, exactly as
`Picard/DivRepAffChartOverlap.lean` does, and U2 is what will *prove* that hypothesis
for the universal family rather than what is needed to *use* it.
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

noncomputable local instance instOverCleftDivRepAffPullGlue :
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

/-! ## The overlap hypothesis at the canonical carrier -/

set_option maxHeartbeats 1600000 in
-- The two `divRepPullAt` composites unfold `DivFamZar.mapAlgHom` through the chart-ring
-- notation while the instance pack of the canonical overlap carrier is being unified;
-- the defeq check is what costs (the I-0227 budget, as in the overlap lemma itself).
/-- **The overlap hypothesis of the chart pulls, in the canonical-carrier spelling.**
Two pieces `p`, `q` of one atlas factorization of `v` present the same morphism, so
their chart pulls agree after base change along the two comparison maps
`awayMulLeft`/`awayMulRight` into `Localization.Away (f p * f q)`.

This is `divRepPullAt_mapAlgHom_eq_of_chartFactor` at the canonical overlap carrier: the
instance pack is built from the comparison maps themselves, so the abstract
`IsScalarTower.toAlgHom k A B` of that lemma's conclusion *is* the comparison map, and
the two statements agree on the nose. -/
theorem divRepPullAt_awayMul_compat
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hU : DivRepChartFamily.IsCompatible (hpi := hpi) g r1 r2 b1 b2 U)
    {S : Type u} [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver)
    {m : ℕ} (f : Fin m → S)
    (ci : Fin m → (glueData k g r1).J) (cj : Fin m → (glueData k g r2).J)
    (cw : ∀ t : Fin m, ChartRing (ci t) (cj t) →ₐ[k] Localization.Away (f t))
    (hcw : ∀ t : Fin m,
      Spec.map (CommRingCat.ofHom (cw t).toRingHom) ≫ ChartMap (ci t) (cj t)
        = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f t)))) ≫ v.left)
    (p q : Fin m) :
    DivFamZar.mapAlgHom (DivFamZar.awayMulLeft (k := k) f p q)
        (divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U (ci p) (cj p) (cw p))
      = DivFamZar.mapAlgHom (DivFamZar.awayMulRight (k := k) f p q)
        (divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U (ci q) (cj q) (cw q)) := by
  classical
  -- the canonical overlap carrier receives both away carriers, by the comparison maps
  letI algL : Algebra (Localization.Away (f p)) (Localization.Away (f p * f q)) :=
    (DivFamZar.awayMulLeft (k := k) f p q).toRingHom.toAlgebra
  letI algR : Algebra (Localization.Away (f q)) (Localization.Away (f p * f q)) :=
    (DivFamZar.awayMulRight (k := k) f p q).toRingHom.toAlgebra
  haveI towSL : IsScalarTower S (Localization.Away (f p))
      (Localization.Away (f p * f q)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact (DivFamZar.awayMulOfDvd_algebraMap (k := k) (f p * f q) (f p) (f q)
        rfl x).symm)
  haveI towSR : IsScalarTower S (Localization.Away (f q))
      (Localization.Away (f p * f q)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact (DivFamZar.awayMulOfDvd_algebraMap (k := k) (f p * f q) (f q) (f p)
        (mul_comm _ _) x).symm)
  haveI towkL : IsScalarTower k (Localization.Away (f p))
      (Localization.Away (f p * f q)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact ((DivFamZar.awayMulLeft (k := k) f p q).commutes x).symm)
  haveI towkR : IsScalarTower k (Localization.Away (f q))
      (Localization.Away (f p * f q)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact ((DivFamZar.awayMulRight (k := k) f p q).commutes x).symm)
  -- the abstract tower maps of the overlap lemma ARE the two comparison maps
  have hL : IsScalarTower.toAlgHom k (Localization.Away (f p))
      (Localization.Away (f p * f q)) = DivFamZar.awayMulLeft (k := k) f p q :=
    AlgHom.ext fun x => by
      change algebraMap (Localization.Away (f p)) (Localization.Away (f p * f q)) x = _
      rw [RingHom.algebraMap_toAlgebra]
      rfl
  have hR : IsScalarTower.toAlgHom k (Localization.Away (f q))
      (Localization.Away (f p * f q)) = DivFamZar.awayMulRight (k := k) f p q :=
    AlgHom.ext fun x => by
      change algebraMap (Localization.Away (f q)) (Localization.Away (f p * f q)) x = _
      rw [RingHom.algebraMap_toAlgebra]
      rfl
  rw [← hL, ← hR]
  exact divRepPullAt_mapAlgHom_eq_of_chartFactor hpi g r1 r2 b1 b2 U hU v
    (cw p) (cw q) (hcw p) (hcw q)

/-! ## The glued pull over a given factorization -/

/-- **The glued pull of a factorization**: the chart pulls of the pieces of an atlas
factorization of `v` glue to a locally certified class over `S` restricting to each
piece.  Existence is `DivFamZar.exists_glue_of_awaySpan` fed by
`divRepPullAt_awayMul_compat`. -/
theorem exists_divRepPullGlue
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hU : DivRepChartFamily.IsCompatible (hpi := hpi) g r1 r2 b1 b2 U)
    {S : Type u} [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver)
    {m : ℕ} (f : Fin m → S) (hspan : Ideal.span (Set.range f) = ⊤)
    (ci : Fin m → (glueData k g r1).J) (cj : Fin m → (glueData k g r2).J)
    (cw : ∀ t : Fin m, ChartRing (ci t) (cj t) →ₐ[k] Localization.Away (f t))
    (hcw : ∀ t : Fin m,
      Spec.map (CommRingCat.ofHom (cw t).toRingHom) ≫ ChartMap (ci t) (cj t)
        = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f t)))) ≫ v.left) :
    ∃ F₀ : DivFamZar C S pi g, ∀ t : Fin m,
      DivFamZar.mapAlgHom (IsScalarTower.toAlgHom k S (Localization.Away (f t))) F₀
        = divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U (ci t) (cj t) (cw t) :=
  DivFamZar.exists_glue_of_awaySpan f hspan
    (fun t => divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U (ci t) (cj t) (cw t))
    (divRepPullAt_awayMul_compat hpi g r1 r2 b1 b2 U hU v f ci cj cw hcw)

/-- **The glued pull is unique**: no two classes over `S` restrict to the same family of
chart pulls, by Zariski separation over the factorization's spanning family.  So the
`pull` field's value is determined by the factorization data, with no further choice —
what remains for full choice-independence is comparing two *different* factorizations,
which is the U2-gated statement. -/
theorem existsUnique_divRepPullGlue
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hU : DivRepChartFamily.IsCompatible (hpi := hpi) g r1 r2 b1 b2 U)
    {S : Type u} [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver)
    {m : ℕ} (f : Fin m → S) (hspan : Ideal.span (Set.range f) = ⊤)
    (ci : Fin m → (glueData k g r1).J) (cj : Fin m → (glueData k g r2).J)
    (cw : ∀ t : Fin m, ChartRing (ci t) (cj t) →ₐ[k] Localization.Away (f t))
    (hcw : ∀ t : Fin m,
      Spec.map (CommRingCat.ofHom (cw t).toRingHom) ≫ ChartMap (ci t) (cj t)
        = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f t)))) ≫ v.left) :
    ∃! F₀ : DivFamZar C S pi g, ∀ t : Fin m,
      DivFamZar.mapAlgHom (IsScalarTower.toAlgHom k S (Localization.Away (f t))) F₀
        = divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U (ci t) (cj t) (cw t) :=
  DivFamZar.existsUnique_glue_of_awaySpan f hspan
    (fun t => divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U (ci t) (cj t) (cw t))
    (divRepPullAt_awayMul_compat hpi g r1 r2 b1 b2 U hU v f ci cj cw hcw)

end Curve

end AlgebraicGeometry
