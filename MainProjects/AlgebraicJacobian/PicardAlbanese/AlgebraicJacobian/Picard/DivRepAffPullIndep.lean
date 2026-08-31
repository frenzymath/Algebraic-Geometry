/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAffPullGlue
import AlgebraicJacobian.Picard.DivRepAffPullbackReduce

/-!
# F5 — the glued pull does not depend on the factorization, and it is U2-free

`Picard/DivRepAffPullGlue.lean` glues the chart pulls of ONE atlas factorization of a
morphism `v : overSpec k S ⟶ DivOver` into a class over `S`, uniquely determined by that
factorization's data.  What was still owed for the `pull` field of
`DivRepAffinePullback` is that two *different* factorizations of the same `v` give the
same class.

`informal/w4-ddr9-worksheet.md` §3.4 lists this as "choice-independence of the
factorization", and the roadmap leaf `AJCR.w4-rep.datum.dat-d.ddr.divrep.u2` describes
the affine package as "U2 + choice bookkeeping", which reads as though this bookkeeping
were downstream of the DDR9-U ε-identity.  **It is not.**  The reason is a property of
the landed overlap lemma that nobody had used:

> `divRepPullAt_mapAlgHom_eq_of_chartFactor` (`Picard/DivRepAffChartOverlap.lean`)
> compares **any two chart presentations of the same morphism `v`**, over any two
> carriers `A`, `A'`, restricted to any common tower ring `B`.  It never asks that the
> two presentations come from the same factorization.

So the cross-refinement of two factorizations is handled by exactly the lemma that
handles one factorization's own overlaps.  Concretely: the products `f p * f' q` of two
spanning families span the unit ideal, the canonical carrier `Localization.Away (f p * f' q)`
receives both `Localization.Away (f p)` and `Localization.Away (f' q)` by the comparison maps
of `Picard/DivRepAwaySpanGlue.lean`, and the two glued classes agree there.

The spanning statement is the already-landed `span_range_mul_eq_top`
(`Picard/DivRepClassifyZarSep.lean:157`), reached here by importing
`Picard/DivRepAffPullbackReduce.lean`.  An earlier draft re-proved it as
`span_mul_span_of_span_eq_top`; a fresh-context review caught the duplication, which had
survived only because `DivRepClassifyZarSep` was not in this file's original import closure —
the standing lesson being that `horizon search` returns both side by side.

* `AlgebraicGeometry.divRepPullGlue_eq_of_chartFactors` — **factorization-independence**:
  two classes over `S`, each restricting to the chart pulls of its own factorization of
  the same `v`, are equal.

With this, the `pull` field of `DivRepAffinePullback` is a well-defined function of `v`
alone, over a supplied compatible chart family, with no residual choice and no ε-identity
consumed in the *proof*.

**What "U2-free" does and does not mean here, because the distinction is easy to overstate
and a fresh-context review had to correct it once.**  What is true: this proof consumes no
ε-identity, so factorization-independence is no longer a *second* obligation standing beside
U2.  What is **not** true is that any gate has been cleared.  `DivRepChartFamily.IsCompatible`
has no producer, and its only intended producer is U2 —
`isCompatible_of_isDivRepClassify_divRepPullAt` (`Picard/DivRepAffPullbackReduce.lean:98`)
derives it from exactly the per-chart ε clause, and no converse or alternative route is known.
So a consumer still cannot instantiate this theorem without proving U2 or finding another way
to `IsCompatible`.  The set of unproved statements is unchanged; what changed is its
partition, and hence the size of the remaining target: `isDivRepClassify_pull` and
`IsCompatible`, rather than those plus an open-ended pile of "choice bookkeeping".
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

noncomputable local instance instOverCleftDivRepAffPullIndep :
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

/-! ## Factorization-independence -/

set_option maxHeartbeats 1600000 in
-- The cross-refinement carrier `Localization.Away (f p * f' q)` receives both
-- factorizations' away carriers, so the instance pack of two towers is unified at once;
-- the defeq cost is the same as in `divRepPullAt_awayMul_compat`.
/-- **The glued pull is independent of the factorization** (`w4-ddr9` §3.4's
"choice-independence", and it is U2-FREE).  If `F₀` restricts to the chart pulls of one
atlas factorization `(f, ci, cj, cw)` of `v`, and `F₁` to those of another
`(f', ci', cj', cw')`, then `F₀ = F₁`.

Route, and the point is that it is the *same* lemma as the single-factorization overlap:
the cross products `f p * f' q` span (`span_range_mul_eq_top`), so it suffices to
compare over each `Localization.Away (f p * f' q)`; that canonical carrier receives both
`Localization.Away (f p)` and `Localization.Away (f' q)` by the comparison maps
`DivFamZar.awayMulOfDvd`; and the two restricted values are chart pulls of two
presentations of the *same* `v`, which `divRepPullAt_mapAlgHom_eq_of_chartFactor` equates
— that lemma never required the two presentations to share a factorization, which is
exactly why no ε-identity is consumed here. -/
theorem divRepPullGlue_eq_of_chartFactors
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hU : DivRepChartFamily.IsCompatible (hpi := hpi) g r1 r2 b1 b2 U)
    {S : Type u} [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver)
    {m m' : ℕ} (f : Fin m → S) (f' : Fin m' → S)
    (hspan : Ideal.span (Set.range f) = ⊤)
    (hspan' : Ideal.span (Set.range f') = ⊤)
    (ci : Fin m → (glueData k g r1).J) (cj : Fin m → (glueData k g r2).J)
    (cw : ∀ t : Fin m, ChartRing (ci t) (cj t) →ₐ[k] Localization.Away (f t))
    (hcw : ∀ t : Fin m,
      Spec.map (CommRingCat.ofHom (cw t).toRingHom) ≫ ChartMap (ci t) (cj t)
        = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f t)))) ≫ v.left)
    (ci' : Fin m' → (glueData k g r1).J) (cj' : Fin m' → (glueData k g r2).J)
    (cw' : ∀ t : Fin m', ChartRing (ci' t) (cj' t) →ₐ[k] Localization.Away (f' t))
    (hcw' : ∀ t : Fin m',
      Spec.map (CommRingCat.ofHom (cw' t).toRingHom) ≫ ChartMap (ci' t) (cj' t)
        = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f' t))))
          ≫ v.left)
    {F₀ F₁ : DivFamZar C S pi g}
    (hF₀ : ∀ t : Fin m,
      DivFamZar.mapAlgHom (IsScalarTower.toAlgHom k S (Localization.Away (f t))) F₀
        = divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U (ci t) (cj t) (cw t))
    (hF₁ : ∀ t : Fin m',
      DivFamZar.mapAlgHom (IsScalarTower.toAlgHom k S (Localization.Away (f' t))) F₁
        = divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U (ci' t) (cj' t) (cw' t)) :
    F₀ = F₁ := by
  classical
  -- compare over the cross-refinement, which spans
  refine DivFamZar.eq_of_awaySpan_eq (fun pq : Fin m × Fin m' => f pq.1 * f' pq.2)
    (span_range_mul_eq_top f f' hspan hspan') (fun pq => ?_)
  obtain ⟨p, q⟩ := pq
  -- the cross-refinement carrier receives both away carriers
  letI algL : Algebra (Localization.Away (f p)) (Localization.Away (f p * f' q)) :=
    (DivFamZar.awayMulOfDvd (k := k) (f p * f' q) (f p) (f' q)
      rfl).toRingHom.toAlgebra
  letI algR : Algebra (Localization.Away (f' q)) (Localization.Away (f p * f' q)) :=
    (DivFamZar.awayMulOfDvd (k := k) (f p * f' q) (f' q) (f p)
      (mul_comm _ _)).toRingHom.toAlgebra
  haveI towSL : IsScalarTower S (Localization.Away (f p))
      (Localization.Away (f p * f' q)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact (DivFamZar.awayMulOfDvd_algebraMap (k := k) (f p * f' q) (f p) (f' q)
        rfl x).symm)
  haveI towSR : IsScalarTower S (Localization.Away (f' q))
      (Localization.Away (f p * f' q)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact (DivFamZar.awayMulOfDvd_algebraMap (k := k) (f p * f' q) (f' q) (f p)
        (mul_comm _ _) x).symm)
  haveI towkL : IsScalarTower k (Localization.Away (f p))
      (Localization.Away (f p * f' q)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact ((DivFamZar.awayMulOfDvd (k := k) (f p * f' q) (f p) (f' q)
        rfl).commutes x).symm)
  haveI towkR : IsScalarTower k (Localization.Away (f' q))
      (Localization.Away (f p * f' q)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact ((DivFamZar.awayMulOfDvd (k := k) (f p * f' q) (f' q) (f p)
        (mul_comm _ _)).commutes x).symm)
  -- the abstract tower maps of the overlap lemma ARE the two comparison maps
  have hL : IsScalarTower.toAlgHom k (Localization.Away (f p))
        (Localization.Away (f p * f' q))
      = DivFamZar.awayMulOfDvd (k := k) (f p * f' q) (f p) (f' q) rfl :=
    AlgHom.ext fun x => by
      change algebraMap (Localization.Away (f p)) (Localization.Away (f p * f' q)) x = _
      rw [RingHom.algebraMap_toAlgebra]
      rfl
  have hR : IsScalarTower.toAlgHom k (Localization.Away (f' q))
        (Localization.Away (f p * f' q))
      = DivFamZar.awayMulOfDvd (k := k) (f p * f' q) (f' q) (f p) (mul_comm _ _) :=
    AlgHom.ext fun x => by
      change algebraMap (Localization.Away (f' q)) (Localization.Away (f p * f' q)) x = _
      rw [RingHom.algebraMap_toAlgebra]
      rfl
  -- each side factors through its own away carrier, then to the cross-refinement
  have hsplitL : (DivFamZar.awayMulOfDvd (k := k) (f p * f' q) (f p) (f' q) rfl).comp
      (IsScalarTower.toAlgHom k S (Localization.Away (f p)))
        = IsScalarTower.toAlgHom k S (Localization.Away (f p * f' q)) :=
    AlgHom.ext fun x =>
      DivFamZar.awayMulOfDvd_toAlgHom (k := k) (f p * f' q) (f p) (f' q) rfl x
  have hsplitR : (DivFamZar.awayMulOfDvd (k := k) (f p * f' q) (f' q) (f p)
        (mul_comm _ _)).comp (IsScalarTower.toAlgHom k S (Localization.Away (f' q)))
        = IsScalarTower.toAlgHom k S (Localization.Away (f p * f' q)) :=
    AlgHom.ext fun x =>
      DivFamZar.awayMulOfDvd_toAlgHom (k := k) (f p * f' q) (f' q) (f p)
        (mul_comm _ _) x
  -- rewrite each side through ITS OWN away carrier; the two sides are syntactically
  -- identical before this, so a bare `rw` would rewrite both with the left factorization
  conv_lhs => rw [← hsplitL]
  conv_rhs => rw [← hsplitR]
  rw [DivFamZar.mapAlgHom_comp, DivFamZar.mapAlgHom_comp, hF₀ p, hF₁ q, ← hL, ← hR]
  -- both are chart pulls of presentations of the SAME `v`
  exact divRepPullAt_mapAlgHom_eq_of_chartFactor hpi g r1 r2 b1 b2 U hU v
    (cw p) (cw' q) (hcw p) (hcw' q)

end Curve

end AlgebraicGeometry
