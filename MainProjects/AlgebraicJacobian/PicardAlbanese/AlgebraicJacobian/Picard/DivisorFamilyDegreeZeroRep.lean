/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyDegreeZeroGeneral
import AlgebraicJacobian.Picard.DivisorFamilyZarSheaf

/-!
# A PRODUCER OF `rep` AT PARAMETER `0`

`rep : (divFunctor C π n).RepresentableBy D` is the hypothesis the whole Pic⁰ seam is
quantified over — `mixedParamChart` takes one per index — and it has had **no producer at any
parameter**.  This file supplies one at `n = 0`.

## The two halves, and where each comes from

* **Inhabited.**  `DivFamZar.trivZar` and `DivFamZar.trivSection`
  (`Picard/DivisorFamilyDegreeZero.lean`) give a point of `divFamZar C π 0 T` at every test,
  unconditionally.  Not this file's work.
* **Unique.**  `DivisorAdaptation.divEq_trivEqns_of_isCertified_zero`
  (`Picard/DivisorFamilyDegreeZeroGeneral.lean`) says a degree-`0` certified system is
  divisor-equal to the trivial one, over an **arbitrary** test ring — the unit argument, no
  field.  Descending it through `IsLocallyCertified` is the work below.

Together the value is a singleton at every test object, so `divFunctor C π 0` is the terminal
presheaf on the slice, and the terminal object `Over.mk (𝟙 (Spec k))` represents it.

## Why the descent is not free, and what pays for it

`DivFamZar` is defined by `IsLocallyCertified`: a span-`⊤` family `g : Fin m → R` with
certified families over the localizations `Localization.Away (g i)`, each divisor-equal to the
*pulled-back* system.  So the unit argument applies over each `Localization.Away (g i)`, not
over `R`, and the conclusion has to come back down.  It does, through two landed facts:

* `Scheme.LocalEquations.divEq_of_divEq_pullback` — divisor equality is local for a cover by
  open immersions (`Picard/DivisorFamilyZariskiSep.lean`);
* `exists_relCurveMap_base_eq` — the localization comparisons of a span-`⊤` family jointly
  cover the relative curve.

Both were built for `DivFam.eq_of_away_eq` and are reused verbatim.  The one bookkeeping step
is the index universe: `IsLocallyCertified` uses `Fin m : Type 0` while the descent lemma wants
`ι : Type u`, so the family is transported along `ULift`.

## What this does and does not give the seam

**Does**: a genuine `(divFunctor C π 0).RepresentableBy`, and hence — per pic-c's
`abel-noninj` work, which takes `Subsingleton ((divFunctor C π n).obj (op T))` as its
antecedent — an inhabitant of the antecedent that makes the Abel chart a monomorphism at this
parameter.  The `rep` slot is no longer producerless.

**Does not**: give `mixedParamChart` an atlas at a useful parameter.  A chart at `nn i = 0`
still needs a legal index `Z i` of degree `m·d₁ − 0`, and the seam's coverage antecedent is
untouched.  This is one antecedent discharged, not the seam closed.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161); pin in-file. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsAffineHom pi]

noncomputable section

/-! ## The pullback of the trivial system is trivial -/

/-- **The trivial system pulls back to the trivial system**, up to divisor equality, along an
arbitrary comparison of relative curves.  Both have cover `⊤` and the pulled equation is a
restriction of `1`, so the comparison unit is `1`.

This is the mirror of `DivFamZar.mapAlg_trivZar` at the level of *systems* rather than classes,
and it is what lets the descent below compare like with like on each localization. -/
theorem divEq_pullback_trivEqns {S : Type u} [CommRing S] [Algebra k S]
    (w : relCurve C S ⟶ relCurve C R) (hreg) :
    Scheme.LocalEquations.DivEq
      ((DivFamZar.trivEqns C R).pullback w hreg) (DivFamZar.trivEqns C S) := by
  refine ⟨⊤, fun _ => le_top, fun _ => le_top, fun y => ⟨1, ?_⟩⟩
  rw [Units.val_one, one_mul, Scheme.LocalEquations.pullback_eqn, DivFamZar.trivEqns_eqn]
  change (CommRingCat.Hom.hom _) ((CommRingCat.Hom.hom _) (1 : _))
      = (CommRingCat.Hom.hom _) (1 : _)
  rw [map_one, map_one, map_one]

/-! ## The descent to the locally certified carrier -/

set_option maxHeartbeats 1600000 in
-- The `IsLocallyCertified` destructuring plus the four descent arguments elaborate past the
-- default heartbeat budget; scoped to this one declaration rather than to the whole file.
/-- **A locally certified degree-`0` system is divisor-equal to the trivial one**, over an
arbitrary test ring.

The unit argument (`divEq_trivEqns_of_isCertified_zero`) applies over each
`Localization.Away (g i)`, where `IsLocallyCertified` supplies a genuine certified family; the
conclusion descends because divisor equality is local for the cover by the localization
comparisons, which are open immersions jointly covering the relative curve.

Field-free: the corresponding field statement `divEq_of_isCertified_zero`
(`Picard/DivisorFamilyDegreeZeroUnique.lean`) needs `Field K` for
`divEq_of_presentationDivisor_eq`, and this route needs no such input. -/
theorem divEq_trivEqns_of_isLocallyCertified_zero
    {d : (relCurve C R).LocalEquations} (hd : IsLocallyCertified C R pi 0 d) :
    Scheme.LocalEquations.DivEq d (DivFamZar.trivEqns C R) := by
  classical
  obtain ⟨m, g, hspan, hG⟩ := hd
  -- `IsLocallyCertified` indexes by `Fin m : Type 0`; the descent lemma wants `Type u`
  set g' : ULift.{u} (Fin m) → R := fun i => g i.down with hg'
  have hspan' : Ideal.span (Set.range g') = ⊤ := by
    rw [← hspan]
    congr 1
    exact Set.ext fun x =>
      ⟨fun ⟨i, hi⟩ => ⟨i.down, hi⟩, fun ⟨i, hi⟩ => ⟨ULift.up i, hi⟩⟩
  haveI : ∀ i : ULift.{u} (Fin m),
      IsOpenImmersion (relCurveMap C R (Localization.Away (g' i))) :=
    fun i => isOpenImmersion_relCurveMap_away C R (Localization.Away (g' i)) (g' i)
  refine Scheme.LocalEquations.divEq_of_divEq_pullback
    (fun i : ULift.{u} (Fin m) => relCurveMap C R (Localization.Away (g' i)))
    (fun y => exists_relCurveMap_base_eq C R g'
      (fun i => Localization.Away (g' i)) hspan' y)
    (fun i => Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
      (relCurveMap C R (Localization.Away (g' i))) d)
    (fun i => Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
      (relCurveMap C R (Localization.Away (g' i))) (DivFamZar.trivEqns C R))
    (fun i => ?_)
  obtain ⟨G, hGdiv⟩ := hG i.down
  exact (hGdiv.symm.trans
      (G.adaptation.divEq_trivEqns_of_isCertified_zero G.certified)).trans
    (divEq_pullback_trivEqns _ _).symm

/-- **THE FUNCTOR CARRIER IS A SUBSINGLETON AT EVERY TEST RING** — the statement
`Picard/DivisorFamilyDegreeZeroUnique.lean` records as open.

`instSubsingletonDivFamZarZero` there needs `Field K` twice; this needs no field at all. -/
instance instSubsingletonDivFamZarZeroGeneral :
    Subsingleton (DivFamZar C R pi 0) := by
  refine ⟨fun x y => ?_⟩
  induction x using Quotient.ind with | _ d₁ =>
  induction y using Quotient.ind with | _ d₂ =>
  exact Quotient.sound
    ((divEq_trivEqns_of_isLocallyCertified_zero d₁.2).trans
      (divEq_trivEqns_of_isLocallyCertified_zero d₂.2).symm)

/-- **Exactly one degree-zero divisor class over every test ring**: `Nonempty` from
`DivFamZar.trivZar`, `Subsingleton` from the pin above. -/
@[reducible] def DivFamZar.uniqueZero : Unique (DivFamZar C R pi 0) :=
  uniqueOfSubsingleton (DivFamZar.trivZar C R pi)

/-! ## The functor value at an arbitrary test, and the representation -/

/-- **The degree-zero vehicle value is a subsingleton at EVERY test object**, not only at
affine ones.  `divFamZar C π 0 T` is a *subtype* of `Π U : T.left.affineOpens, DivFamZar …`,
so the componentwise subsingleton above transports through `Subtype.ext` and `funext` with no
sheaf argument. -/
instance instSubsingletonDivFamZarSectionZero (T : Over (Spec (.of k))) :
    Subsingleton (divFamZar C pi 0 T) :=
  ⟨fun _ _ => Subtype.ext (funext fun _ => Subsingleton.elim _ _)⟩

/-- **THE DEGREE-ZERO DIVISOR FUNCTOR IS A SINGLETON-VALUED PRESHEAF**: its value at every
test object has exactly one element.

`Nonempty` is `DivFamZar.trivSection` (`Picard/DivisorFamilyDegreeZero.lean`, unconditional);
`Subsingleton` is the general-`R` pin of this file. -/
@[reducible] def divFamZar.uniqueZero (T : Over (Spec (.of k))) :
    Unique (divFamZar C pi 0 T) :=
  uniqueOfSubsingleton (DivFamZar.trivSection C pi T)

/-- **A PRODUCER OF `rep` AT PARAMETER `0`** — the point of this file.

`divFunctor C π 0` is singleton-valued, and the slice's terminal object `Over.mk (𝟙 …)` has a
singleton hom-set into it, so the two are in natural bijection: `homEquiv` is
`Equiv.equivOfSubsingletonOfSubsingleton` and `homEquiv_comp` holds because the target is a
subsingleton.

**This is the first inhabitant of the `rep` slot at any parameter.**  `mixedParamChart`,
`abelSigmaChart`, `IsChartUniv` and the rest of the `Pic0Chart*` cluster all take
`rep : (divFunctor C π n).RepresentableBy D` as a hypothesis, and until now nothing produced
one, so every statement quantified over it was true but untested.

*No count is given here on purpose.*  Two reasonable methods disagree — `grep -c "rep :
(divFunctor"` over `AlgebraicJacobian/` and a per-declaration census of header binders differ by
about a third, and the task brief that prompted this work quoted a third figure again.  The
claim that matters is a zero, not a large number: **the producer side was empty**, verified by
reading the three existing `…representableBy` declarations
(`DivRepGlobalData.representableBy`, `divFunctor_representableBy_of_chartClause`,
`DivRepAffinePullback.representableBy`), each of which takes an unwitnessed structure whose only
producer is itself gated on U2.

**What it does not do.**  It does not give the seam an atlas at this parameter: a chart at
`nn i = 0` still needs a legal index `Z i` of degree `m·d₁ − 0`, and the coverage antecedent is
untouched.

What *is* known against this parameter, at the strength it actually has:
`not_mem_chartLocus_of_two_le_genus_zero_param`
(`Picard/Pic0ChartSubsingletonCollapse.lean`) proves the **chart locus** at `n = 0` is empty
once `g ≥ 2`, from the rank formula `h⁰ = n + 1 − g` of `Picard/Pic0ChartLocusH0Rank.lean`
(at `0` it reads `1 − g ≤ −1` with `h⁰` a cast natural), under that theorem's own `hlam` and
`hχ` hypotheses.  So the **`chartLocus`-mediated** route to coverage is dead here.

**An earlier draft of this paragraph — and both of my commit messages — instead said "coverage
is provably impossible at `n = 0`", and that is not a theorem.**  `PointwiseCoverage`
(`Pic0ChartAtlasCoupling.lean:99`) quantifies over an *arbitrary* open `W ∋ t` and never
mentions `chartLocus`; `chartsCoverLocally_of_pointwise` calls `chartLocusOpens` only the
*intended* instantiation; and `Pic0ChartAtlasCoupling.lean:52-55` states outright that the two
carriers do not meet and that **no declaration in the tree relates them**.  So "coverage needs
the locus inhabited" is a missing implication, not a step.  The overclaim ran against my own
result, which is exactly why it read as audited — and it would have told a later lane not to
try an `n = 0` coverage route that is not in fact refuted.

The honest joint statement: an inhabited `rep` at `n = 0`, where the known coverage route is
dead for `g ≥ 2`, and unconditional coverage at `n = M·δ + g`, where `rep` has no producer —
opposite sides of one rank inequality, with nothing connecting them.  A reader taking this
definition as a step toward representability of `Pic⁰` would be wrong.

What it *is* usable for immediately is pic-c's `abel-noninj` fork, whose antecedent is exactly
`Subsingleton ((divFunctor C π n).obj (op T))`: at this parameter the Abel chart is a
monomorphism, `D` is terminal, and the whole `V`-interval collapses to `{⊥, ⊤}`. -/
def divFunctorZeroRepresentableBy :
    (divFunctor C pi 0).RepresentableBy (Over.mk (𝟙 (Spec (CommRingCat.of k)))) where
  homEquiv {T} :=
    { toFun := fun _ => DivFamZar.trivSection C pi T
      invFun := fun _ => Over.mkIdTerminal.from T
      left_inv := fun f => Over.mkIdTerminal.hom_ext _ f
      right_inv := fun _ =>
        (instSubsingletonDivFamZarSectionZero T).allEq _ _ }
  homEquiv_comp {T _} _ _ :=
    (instSubsingletonDivFamZarSectionZero T).allEq _ _

end

end AlgebraicGeometry
