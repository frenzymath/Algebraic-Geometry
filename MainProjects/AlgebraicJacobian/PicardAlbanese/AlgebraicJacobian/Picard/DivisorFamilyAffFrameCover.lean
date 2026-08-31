/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffFraming
import AlgebraicJacobian.Picard.DivSchemeFrameCover
-- For `forall_not_isCertified_of_straddling`, the no-go `not_reachable_of_straddling` states.
-- Imported rather than merely cited: a name that exists in source but not in this file's
-- import closure is a nonexistent citation, and grep cannot tell the difference.
import AlgebraicJacobian.Picard.DivisorFamilyAffStrict

/-!
# The ε frame cover, keyed on the WINDOW QUOTIENT rather than on a carrier

Roadmap leaf `AJCR.w4-rep.datum.dat-d.ddr.divrep.framecover-aff`.

`Picard/DivisorFamilyAffFraming.lean` established that the ε-pair and its pair-chart framing
clause are expressible over the widened carrier, and recorded what it did not do:

> It does not prove `exists_certChartCover` over the widened carrier — that theorem's proof
> runs the certificate cover and the per-piece frame covers, which is real work and belongs to
> whoever restates it.

**This file measures that work, and the measurement is the content.**  Inside
`exists_frame_chart_at_prime` the frame-cover keystone `divFamEps_exists_frameCover`
(`Picard/DivSchemeFrameCover.lean:456`) reads its carrier `DivFam C S π g` at **eight** sites, of
**two** kinds:

* **six** are facts about the window *quotient* — `DivFam.finite_/projective_window_quotient`
  at each of the two ledger windows (:347–357), and `F.window` in the `exists_away_free_pair`
  call (:361, :365).  Constant fibre rank enters separately, through `divFamWindowGr`'s own
  definition.  These are what the layer below restates as hypotheses.
* **two** are *functoriality* of the carrier: `DivFam.window_mapAlg` in the closing `rfl` blocks
  (:426, :443), i.e. "window of `mapAlg` = `windowBaseChange`".  These are **not** window-quotient
  facts, and they are exactly what `windowBaseChange_windowBaseChange` below had to replace.

Everything downstream of the helper — `exists_component_matrix`,
`exists_det_submatrix_notMem_of_mul_eq_one`, `exists_away_isUnit_of_notMem`,
`map_component_chart` — consumes a Grassmannian *point* and a base ring, and never asks what
produced the submodule.

*A predecessor version of this paragraph said "exactly three points" and listed
finite/projective/rankAtStalk.  That both under-counted the reads and mis-classified the two
that motivated this file's one new theorem; corrected here (audit `I-1336`).*

`divisorWindow d hH1` (`Picard/DivisorFamilyWindow.lean:103`) is independent of the
**adaptation** — of which cover refines `d` — which is what lets the declarations below typecheck
carrier-free.  It is **not** independent of the pinned charts: it is a `Submodule.comap` of
`d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀ … .V₁ …`, so the fixed two-chart pair
occurs in its definition.  *A predecessor version said "no adaptation, no cover and no chart
typing"; only the first clause is true (`I-1336`).*

## The one step that is genuinely new

Restating the layer with the three facts as hypotheses is free, but the tower transport is
not.  The chart-typed `map_divFamWindowGr` (`Picard/DivSchemeFrameCover.lean:188`) proves
`Grassmannian.map β (point over R_h) = point over R_u` by routing through the divisor
*object* — `DivFam.window_mapAlg` on both legs plus `DivFam.mapAlg_comp` — which needs a
carrier with a functorial `mapAlg`.  Carrier-free there is no object to route through, so the
composite must be proved where it actually lives, on the submodule:

* `windowBaseChange_windowBaseChange` — transitivity of the window pushforward over a tower
  `R → R' → R''`, for an arbitrary `k`-module ambient `H`.  Not in the tree before; both
  inclusions are `windowBaseChange_le_iff` against the compared generators, and the content
  is one `cancelBaseChange` compatibility (`rfl` fails on it, checked).

## What this does and does NOT establish

It does **not** produce a widened divisor-representability, and no antecedent of
`pic0RepresentableByOfCharts` moves.  The window-quotient facts are **hypotheses** in the window
layer.  The `Reachability` section below gives the chart-typed route to them; the correct ledger
for the *widened* route is:

  the frame cover's chart dependence   REMOVED (this file, sorry-free)
  its window-quotient inputs           reachable chart-typed (below), and reachable WIDENED by
                                       the same three-line proofs through
                                       `AffAdaptation.windowQuotEquiv`
                                       (`Picard/DivisorFamilyAffTheta.lean:914`) — whose source
                                       is the SAME quotient — gated on surjectivity of the
                                       widened `thetaGluedEval`, which that file leaves OPEN.

**Two corrections to predecessor versions of this docstring, both from an audit
(`I-1335`/`I-1337`) that I reproduced before accepting.**  I first wrote that the inputs "reduce
to widened evaluation surjectivity"; I then over-corrected to "the ONE route that exists" plus
"REFUTED on the straddling divisors".  The second is worse than the first and is the one to
retract loudly:

* the widened route **exists** and is gated on a *missing proof*, not on a refutation;
* and the straddling no-go **cannot** bear on it, because
  `forall_not_isCertified_of_straddling` quantifies over `DivisorAdaptation` while the widened
  route consumes `AffAdaptation`.  On exactly those divisors,
  `isCertified_affine_and_not_isCertified_chart` (`Picard/DivisorFamilyAffStrict.lean`) proves
  the *opposite* conjunction: some widened adaptation IS certified while no chart-typed one is.
  So there the widened side is the one that works, and the no-go is evidence *for* it.

One nuance neither the audit nor I had stated, added here because it is the actual widened
residue: `AffAdaptation.windowQuotEquiv` also takes a `ChartTyping C R π D`, and
`AffAdaptation.isEmpty_chartTyping_of_straddling` (same file) *empties* that index on a piece
holding a point outside `V₀` and one outside `V₁`.  So the widened route owes **both** the
evaluation surjectivity and a chart typing (or a `ThetaTrivData`-style replacement index — see
`Picard/DivisorFamilyAffThetaTyping.lean`, inhabited at exponent `0`).  That is a second missing
input, still not a refutation.

## Main declarations

* `AlgebraicGeometry.divisorWindowGrOfQuot` — the window as a Grassmannian point from the
  quotient certificate alone; `divFamWindowGr` with its vehicle removed.
* `AlgebraicGeometry.windowBaseChange_windowBaseChange` — transitivity of the window
  pushforward.
* `AlgebraicGeometry.map_divisorWindowGrOfQuot` — the tower transport, carrier-free.
* `AlgebraicGeometry.exists_component_matrix_of_windowQuot` — the per-prime matrix
  presentation, carrier-free.
* `AlgebraicGeometry.finite_divisorWindow_quot_of_isCertified` and its two siblings — the
  chart-typed supply of the hypotheses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

open Grassmannian Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftAffFrameCover :
    C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
  [IsDominant π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g : ℕ)

/-! ## The window layer, keyed on the window submodule rather than on a carrier -/

section WindowLayer

-- The curve instances of the ambient section are genuinely unused in this layer: the window
-- Grassmannian point is built from `divisorWindow d` and three facts about its quotient, and
-- `divisorWindow` names no adaptation, cover or chart typing.  That is the measurement this
-- section exists to record, so the linter is silenced rather than the variables omitted (the
-- ambient instances are mutually referenced and cannot be dropped individually).
set_option linter.unusedSectionVars false

variable (a : ℕ) (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
variable {R : Type u} [CommRing R] [Algebra k R]

/-- **The window as a Grassmannian point, from the quotient certificate alone**: the
`windowBaseChangeGr` package of `divisorWindow d`, taking the three quotient facts as
hypotheses rather than extracting them from an adaptation.

This is `divFamWindowGr` (`Picard/DivSchemeFrameCover.lean:143`) with its vehicle removed.
`divisorWindow` (`Picard/DivisorFamilyWindow.lean:103`) is a `Submodule.comap` of
`d.vanishingSubmodule` and mentions no adaptation, no cover and no chart typing, so
nothing here knows which carrier certified `d`. -/
noncomputable def divisorWindowGrOfQuot (d : (relCurve C R).LocalEquations)
    (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
    [Module.Finite R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1)]
    [Module.Projective R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1)]
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1) p = g) :
    Grassmannian.grFunctorAff k
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤) g R' :=
  windowBaseChangeGr R' (divisorWindow d ha1) g hrank

@[simp]
lemma divisorWindowGrOfQuot_toSubmodule (d : (relCurve C R).LocalEquations)
    (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
    [Module.Finite R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1)]
    [Module.Projective R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1)]
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1) p = g) :
    (divisorWindowGrOfQuot g a ha1 d R' hrank).toSubmodule
      = windowBaseChange R' (divisorWindow d ha1) :=
  rfl

/-- **Transitivity of the window pushforward** over a tower `R → R' → R''`.

This is the step the chart-typed transport did NOT have to prove: `map_divFamWindowGr`
(`Picard/DivSchemeFrameCover.lean:188`) reaches the same conclusion by going *through the
divisor object* — `DivFam.window_mapAlg` on both legs plus `DivFam.mapAlg_comp` — which needs
a carrier with a functorial `mapAlg`.  Carrier-free there is no object to route through, so
the composite has to be proved where it lives, on the submodule.

Both inclusions are `windowBaseChange_le_iff` against the compared generators; the tower
hypothesis enters only as `IsScalarTower`, and `H` is an arbitrary `k`-module. -/
theorem windowBaseChange_windowBaseChange {H : Type u} [AddCommGroup H] [Module k H]
    {R : Type u} [CommRing R] [Algebra k R]
    (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
    (R'' : Type u) [CommRing R''] [Algebra k R''] [Algebra R R''] [Algebra R' R'']
    [IsScalarTower k R R''] [IsScalarTower k R' R''] [IsScalarTower R R' R'']
    (N : Submodule R (R ⊗[k] H)) :
    windowBaseChange R'' (windowBaseChange R' N) = windowBaseChange R'' N := by
  -- the `R'`-linear comparison arrow `R' ⊗[k] H → R'' ⊗[k] H` of the upper leg
  set ψ : (R' ⊗[k] H) →ₗ[R'] (R'' ⊗[k] H) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k R' R'' R'' H).toLinearMap ∘ₗ
      (TensorProduct.mk R' R'' (R' ⊗[k] H) 1) with hψdef
  have hψ : ∀ y : R' ⊗[k] H, ψ y
      = TensorProduct.AlgebraTensorModule.cancelBaseChange k R' R'' R'' H (1 ⊗ₜ y) :=
    fun _ => rfl
  -- the tower compatibility of the comparison: the two legs agree on the lower generators
  have key : ∀ x : R ⊗[k] H,
      ψ (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' H (1 ⊗ₜ x))
        = TensorProduct.AlgebraTensorModule.cancelBaseChange k R R'' R'' H (1 ⊗ₜ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul r h => simp [hψ]
  refine le_antisymm ?_ ?_
  · -- `⊆`: test the upper generators, then the lower ones through `ψ`
    rw [windowBaseChange_le_iff]
    have hstep : windowBaseChange R' N
        ≤ Submodule.comap ψ ((windowBaseChange R'' N).restrictScalars R') := by
      rw [windowBaseChange_le_iff]
      intro x hx
      refine Submodule.mem_comap.mpr ?_
      rw [key x]
      exact cancelBaseChange_one_tmul_mem_windowBaseChange hx
    intro y hy
    rw [← hψ y]
    exact hstep hy
  · -- `⊇`: a lower generator is `ψ` of an upper generator
    rw [windowBaseChange_le_iff]
    intro x hx
    rw [← key x, hψ]
    exact cancelBaseChange_one_tmul_mem_windowBaseChange
      (cancelBaseChange_one_tmul_mem_windowBaseChange hx)

set_option maxHeartbeats 800000 in
-- Instantiates the window pushforward at two localizations inside a `toAlgebra` tower; the
-- same elaboration profile as the chart-typed `map_divFamWindowGr`, which is budgeted
-- identically.
/-- **The tower transport of the window point, carrier-free** — the analogue of
`map_divFamWindowGr` (`Picard/DivSchemeFrameCover.lean:188`) with no `DivFam` in it. -/
theorem map_divisorWindowGrOfQuot (d : (relCurve C R).LocalEquations)
    [Module.Finite R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1)]
    [Module.Projective R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1)]
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1) p = g)
    (h u : R) (β : Localization.Away h →ₐ[k] Localization.Away u)
    (hβ : β.toRingHom.comp (algebraMap R (Localization.Away h))
      = algebraMap R (Localization.Away u)) :
    Module.Grassmannian.map β
        (divisorWindowGrOfQuot g a ha1 d (Localization.Away h) hrank)
      = divisorWindowGrOfQuot g a ha1 d (Localization.Away u) hrank := by
  letI : Algebra (Localization.Away h) (Localization.Away u) := β.toAlgebra
  letI : IsScalarTower k (Localization.Away h) (Localization.Away u) :=
    IsScalarTower.of_algebraMap_eq' (IsScalarTower.algebraMap_eq k _ _)
  haveI htowerR : IsScalarTower R (Localization.Away h) (Localization.Away u) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [RingHom.algebraMap_toAlgebra]
    exact hβ.symm
  refine Module.Grassmannian.ext ?_
  rw [Module.Grassmannian.map_toSubmodule β
      (divisorWindowGrOfQuot g a ha1 d (Localization.Away h) hrank),
    divisorWindowGrOfQuot_toSubmodule]
  -- the projective-quotient instance the `ker_baseChangeMkQ` description consumes is the
  -- Grassmannian point's own field, at the intermediate ring
  haveI : Module.Projective (Localization.Away h)
      ((Localization.Away h ⊗[k]
        ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        windowBaseChange (Localization.Away h) (divisorWindow d ha1)) :=
    (divisorWindowGrOfQuot g a ha1 d (Localization.Away h) hrank).projective_quotient
  rw [Grassmannian.ker_baseChangeMkQ_eq_map_baseChange (Localization.Away u)
      (windowBaseChange (Localization.Away h) (divisorWindow d ha1)),
    divisorWindowGrOfQuot_toSubmodule]
  exact windowBaseChange_windowBaseChange (Localization.Away h) (Localization.Away u)
    (divisorWindow d ha1)

set_option maxHeartbeats 800000 in
-- The quotient equivalence unfolds the window through the section-ring algebra tower; same
-- elaboration profile as the chart-typed `divFamWindowGrQuotEquiv`.
/-- The quotient of the packaged window point is the base change of the `R`-level quotient —
`divFamWindowGrQuotEquiv` (`Picard/DivSchemeFrameCover.lean:161`) with no carrier: it was
already a statement about the submodule alone. -/
noncomputable def divisorWindowGrOfQuotEquiv (d : (relCurve C R).LocalEquations)
    (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
    [Module.Finite R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1)]
    [Module.Projective R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1)]
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1) p = g) :
    ((R' ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        (divisorWindowGrOfQuot g a ha1 d R' hrank).toSubmodule) ≃ₗ[R']
      R' ⊗[R] ((R ⊗[k]
        ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1) :=
  (Submodule.quotEquivOfEq _ _
      (windowBaseChange_eq_ker_baseChangeMkQ R' (divisorWindow d ha1))).trans
    (Module.Grassmannian.baseChangeMkQEquiv (divisorWindow d ha1))

set_option maxHeartbeats 800000 in
-- Instantiates the free-quotient/matrix kit at the window types; elaboration cost, as for the
-- chart-typed `exists_component_matrix` this replaces.
/-- **One window component, presented over the free locus — carrier-free.**  The analogue of
the private `exists_component_matrix` (`Picard/DivSchemeFrameCover.lean:238`) with the `DivFam`
hypothesis replaced by the three window-quotient facts.

This is the atom the frame cover is built from, and its proof is the chart-typed one verbatim:
freeness transports to the coordinate point, `exists_matrixPoint_eq_of_free` presents it, and
`exists_det_submatrix_notMem_of_mul_eq_one` selects a frame minor off the prime.  Nothing in it
mentions a cover or a chart typing, which is the point. -/
theorem exists_component_matrix_of_windowQuot {r : ℕ}
    (b : Module.Basis (Fin r) k
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤))
    (d : (relCurve C R).LocalEquations)
    [Module.Finite R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1)]
    [Module.Projective R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1)]
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1) p = g)
    (h : R) (pl : PrimeSpectrum (Localization.Away h))
    (hfree : Module.Free (Localization.Away h) (Localization.Away h ⊗[R] ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1))) :
    ∃ (X : Matrix (Fin g) (Fin r) (Localization.Away h))
      (hX : Function.Surjective (matrixProj k g r (Localization.Away h) X))
      (I : Finset (Fin r)) (hI : I.card = g),
      (frameMinor k g r (Localization.Away h) X I hI).det ∉ pl.asIdeal ∧
      matrixPoint k g r (Localization.Away h) X hX
        = congrAmbient b.equivFun
            (divisorWindowGrOfQuot g a ha1 d (Localization.Away h) hrank) := by
  haveI : Nontrivial (Localization.Away h) := by
    rcases subsingleton_or_nontrivial (Localization.Away h) with hs | hn
    · exact absurd (pl.asIdeal.eq_top_iff_one.mpr
        (by rw [Subsingleton.elim (1 : Localization.Away h) 0]; exact zero_mem _))
        pl.isPrime.ne_top
    · exact hn
  have hfreeP : Module.Free (Localization.Away h)
      ((Localization.Away h ⊗[k]
        ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        (divisorWindowGrOfQuot g a ha1 d (Localization.Away h) hrank).toSubmodule) :=
    haveI := hfree
    Module.Free.of_equiv
      (divisorWindowGrOfQuotEquiv g a ha1 d (Localization.Away h) hrank).symm
  obtain ⟨X, hX, hXeq⟩ := exists_matrixPoint_eq_of_free
    (congrAmbient b.equivFun (divisorWindowGrOfQuot g a ha1 d (Localization.Away h) hrank))
    (free_quotient_congrAmbient b.equivFun _ hfreeP)
  obtain ⟨Y, hY⟩ := exists_mul_eq_one_of_matrixProj_surjective k g r _ X hX
  obtain ⟨I, hI, hdet⟩ := exists_det_submatrix_notMem_of_mul_eq_one pl.asIdeal X Y hY
  exact ⟨X, hX, I, hI, hdet, hXeq⟩

end WindowLayer

/-! ## Who can supply the three hypotheses — and the sharp limit on it

The window layer above is carrier-free, so its three hypotheses may be discharged by *any*
route to the window quotient.  The section records the one route that exists, and then the
reason it does not rescue the widened carrier.  Both halves matter; publishing only the first
would overstate the file. -/

section Reachability

-- `not_reachable_of_straddling` uses none of the ambient curve instances: the no-go is about
-- the two pinned fibres and the support, not about smoothness or properness of `C`.  Measured,
-- not assumed — the linter reported exactly this list.  Silenced rather than `omit`-ed because
-- the ambient instances are mutually referenced and cannot be dropped individually.
set_option linter.unusedSectionVars false

variable (a : ℕ) (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
variable (hMa : windowM_choice π hπ g ≤ a)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
variable {R : Type u} [CommRing R] [Algebra k R]

include hπ hO hχ hMa in
/-- **The three window-quotient hypotheses from a chart-typed certificate on the SAME `d`** —
finiteness. -/
theorem finite_divisorWindow_quot_of_isCertified {d : (relCurve C R).LocalEquations}
    (A : DivisorAdaptation C R π d) (hc : A.IsCertified g) :
    Module.Finite R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1) :=
  haveI := hc.finite_thetaGlued a
  Module.Finite.equiv (windowQuotEquiv A ha1
    (hc.thetaGluedEval_surjective (C := C) (π := π) hπ hO hχ ha1 hMa)).symm

include hπ hO hχ hMa in
/-- Projectivity, same route. -/
theorem projective_divisorWindow_quot_of_isCertified {d : (relCurve C R).LocalEquations}
    (A : DivisorAdaptation C R π d) (hc : A.IsCertified g) :
    Module.Projective R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1) :=
  haveI := hc.projective_thetaGlued a
  Module.Projective.of_equiv (windowQuotEquiv A ha1
    (hc.thetaGluedEval_surjective (C := C) (π := π) hπ hO hχ ha1 hMa)).symm

include hπ hO hχ hMa in
/-- Constant fibre rank, same route. -/
theorem rankAtStalk_divisorWindow_quot_of_isCertified {d : (relCurve C R).LocalEquations}
    (A : DivisorAdaptation C R π d) (hc : A.IsCertified g) (p : PrimeSpectrum R) :
    Module.rankAtStalk ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1) p = g := by
  rw [congrFun (Module.rankAtStalk_eq_of_equiv (windowQuotEquiv A ha1
    (hc.thetaGluedEval_surjective (C := C) (π := π) hπ hO hχ ha1 hMa))) p]
  exact hc.rankAtStalk_thetaGlued a p

/-! ### The scope of the chart-typed route, and why it is NOT a limit on the widened one

A predecessor of this file carried a theorem `not_reachable_of_straddling` here, asserting "the
route above is unavailable exactly on the divisors R2 exists for".  **It is withdrawn**, and the
reasoning is kept in its place because that is the reusable part (audit `I-1334`/`I-1335`/
`I-1337`, reproduced before accepting).

Three things were wrong with it:

1. it was a **verbatim restatement** of `forall_not_isCertified_of_straddling`
   (`Picard/DivisorFamilyAffStrict.lean:127`) — same binders, same conclusion, body a direct
   delegation — and that lemma is in this file's own import closure, so the restatement served
   nobody;
2. it carried `[IsNoetherianRing R]`, which its proof does not use;
3. and the claim it was there to support is **false**.  The reachability theorems above are
   about `DivisorAdaptation`, and so is the no-go.  The *widened* route to the same three
   hypotheses runs through `AffAdaptation.windowQuotEquiv`, over `AffAdaptation`, which the
   no-go's `∀` does not reach.  Worse for the old framing:
   `isCertified_affine_and_not_isCertified_chart` proves that on exactly those straddling
   divisors *some widened adaptation is certified* while no chart-typed one is — so there the
   widened carrier is the one that works.

What is true, and all that is true: the three theorems above are the **chart-typed** supply of
the window-quotient hypotheses, and it is unavailable on straddling divisors.  Cite
`forall_not_isCertified_of_straddling` directly for that; it needs no wrapper here. -/

end Reachability

end Curve

end AlgebraicGeometry
