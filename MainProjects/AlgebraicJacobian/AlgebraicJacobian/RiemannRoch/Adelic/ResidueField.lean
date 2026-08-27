/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Adelic.LedgerClosure
import AlgebraicJacobian.RiemannRoch.Adelic.GateInstances
import AlgebraicJacobian.RiemannRoch.Adelic.FiniteMapToP1
import AlgebraicJacobian.RiemannRoch.CurveBaseChange
import AlgebraicJacobian.Picard.TangentSpaceStalkAlgebra

/-!
# Adelic Riemann–Roch — the residue field of a closed point is the base field

This file **discharges** the residue-degree fact `[κ(P) : k̄] = 1` for a prime divisor of
an AJC curve over an algebraically closed base field.  It is the input that
`Adelic/GlobalGeneration.lean` §5–§7 and `Adelic/SectionBounds.lean` §4 both reduce to,
and which those files leave open.

## What changes relative to `GlobalGeneration.lean` §7

`hasRationalResidues_of_isAlgClosed` (there) derives the approximation statement from
**three stalk-level instance binders**, and its own docstring records — correctly — that
none of them is constructed anywhere in AJC, so that it "trades one unproved fact for
three unbuilt instances" and is a *reformulation, not a discharge*.

This file builds all three, for a curve `C : Over (Spec k)`, and so closes the gap:

1. `Algebra k 𝒪_P` — `stalkStructureHom` (`Picard/TangentSpaceStalkAlgebra.lean`) already
   supplies the ring map; what was missing is that it is **compatible with the
   `Algebra k K(C)` of `Adelic/GateInstances.lean`**.  That is
   `algebraMap_stalk_functionField`, proved by factoring both through `Γ(C,⊤)`:
   `stalkStructureHom = constMap ≫ germ_⊤` (`stalkStructureHom_eq_constMap_germ`, from
   mathlib's `Hom.germ_stalkMap`), after which mathlib's
   `functionField_isScalarTower` matches the two composites.
2. `IsScalarTower k 𝒪_P K(C)` — a corollary of (1) (`isScalarTower_stalk_functionField`).
3. `Module.Finite k κ_P` — **not needed at all** on this route, which is the substantive
   simplification.  §7's argument goes through `IsAlgClosed.algebraMap_bijective_of_isIntegral`,
   which needs the residue field to be *integral* over `k` and hence a finiteness input that
   AJC does not have.  Mathlib's `AlgebraicGeometry.residueFieldIsoBase` proves
   `κ(x) ≅ k` for a closed point of a scheme **locally of finite type** over an
   algebraically closed field, obtaining integrality from
   `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace` instead.  `LocallyOfFiniteType C.hom`
   is a hypothesis the project's curves genuinely have, unlike a bare residue-finiteness gate.

So the exchange is: one open fact **out**, and in its place a `LocallyOfFiniteType`
hypothesis plus the closedness of the point — both genuinely available.

**Where `LocallyOfFiniteType` comes from, precisely.**  From `[IsProper C.hom]`, which mathlib
declares as `class IsProper extends IsSeparated f, UniversallyClosed f, LocallyOfFiniteType f` —
so a proper curve has it structurally, and every real consumer of this file (notably
`Scheme.WeilDivisor.principal_degree_zero`) carries `[IsProper]`.

It does **not** come from smoothness in this file's import closure, and an earlier version of
this docstring implied otherwise.  The `SmoothOfRelativeDimension 1 → Smooth` bridge lives in
`AlgebraicJacobian/Curve/GeometricallyReduced.lean`, which this module does not import;
`infer_instance` for `LocallyOfFiniteType` from `[SmoothOfRelativeDimension 1]` alone **fails**
here (machine-checked), while from `[IsProper]` it succeeds.  A caller who has smoothness but
not properness must supply `LocallyOfFiniteType` by hand — `Adelic/FiniteMapToP1.lean` does
exactly that at its own use site, via `SmoothOfRelativeDimension.smooth`.

## The N14 finiteness gate falls out too

Because the route above needs no finiteness, it *yields* some.  `ChiLedger.lean` §N14 carries
`Module.Finite k (localStepTgt k P 1)` — "`[κ(P):k] < ∞`" — as an explicit binder on roughly
twenty statements across the lane, describing it as "the gated keystone input, not re-proved
here".  Approximation by constants makes `κ(P)` spanned by the single class of `1`, hence
finitely generated: `finite_localStepTgt_one_of_hasRationalResidues`, and on curve hypotheses
`finite_localStepTgt_one_of_isAlgClosed_curve`.

That is why nothing in §3–§4 below carries a finiteness binder, including
`residueDeg_eq_one_of_isAlgClosed_curve`: the binder is discharged internally rather than
passed to the caller.  It is deliberately **not** registered as a global instance — see the
diamond note below, and note that a global instance would fire during synthesis inside every
lane statement and pin the `k`-action there.

## The closedness input

`residueFieldIsoBase` needs `IsClosed {P.point}`.  For a prime divisor this is *not* an
extra assumption: `Adelic/FiniteMapToP1.lean` proves
`isClosed_singleton_of_coheight_le_one`, and a prime divisor has `coheight = 1` by
definition while the generic point has coheight `0` on a curve.  `isClosed_primeDivisor`
below packages this, taking the one-dimensionality of the curve as the hypothesis
`hdim` that the sibling file also uses.

## Main declarations

* `stalkStructureHom_eq_constMap_germ`, `algebraMap_stalk_functionField`,
  `isScalarTower_stalk_functionField` — the compatibility layer (item 1–2 above).
* `bijective_residue_comp_stalkStructureHom` — `k → 𝒪_P → κ(P)` is **bijective** at a
  closed point, from mathlib's `residueFieldIsoBase`.
* `hasRationalResidues_of_isAlgClosed_curve` — `HasRationalResidues k P`, **discharged**:
  every function regular at `P` agrees with a constant to first order.
* `finite_localStepTgt_one_of_hasRationalResidues`,
  `finite_localStepTgt_one_of_isAlgClosed_curve` — the **N14 finiteness gate**, discharged.
* `residueDeg_eq_one_of_isAlgClosed_curve` — `[κ(P):k] = 1`, the campaign's residue fact,
  with no finiteness binder.
* `degree_principal_eq_zero_of_isAlgClosed_curve` — the **unweighted** principal-degree-zero
  statement, from the ledger, with the residue input now discharged rather than assumed.

## A note on an instance diamond (read before adding imports here)

With `Picard/TangentSpaceStalkAlgebra.lean` imported, `open scoped AlgebraicGeometry`
brings in `overStalkAlgebra C x : Algebra k 𝒪_{C,x}`.  At `x = genericPoint C.left` its
target `𝒪_{C,generic}` *is* `K(C)` by definition, so it competes with
`Scheme.functionFieldAlgebra` for `Algebra k K(C)` — and the two are **not**
definitionally equal.  Activating it would silently re-pin
`sectionSub`/`orderGeSub`/`residueDeg` to a different `k`-action than the rest of the
lane uses — with no error, no `sorry`, and clean `#print axioms`.

**What actually protects this file, stated precisely** (a reviewer rightly doubted an earlier
version of this paragraph, which asserted the protection without saying why it works).  The two
instances sit in *different namespaces*:

* `AlgebraicGeometry.overStalkAlgebra` — namespace `AlgebraicGeometry`;
* `AlgebraicGeometry.Scheme.functionFieldAlgebra` — namespace `AlgebraicGeometry.Scheme`.

So `open scoped AlgebraicGeometry.Scheme`, which is what this file uses, activates the second
and **not** the first, while `open scoped AlgebraicGeometry` activates both.  Machine-checked
both ways: with the narrow open,
`algebraMap k K(C) c = (Scheme.functionFieldAlgebra C).algebraMap c` closes by `rfl`; with the
wide open, the *same* `rfl` fails to elaborate.  That pair of results is the evidence, not the
reasoning.

Consequence for a future edit: adding `open scoped AlgebraicGeometry` to this file, or importing it
into a file that has one, is not a style question — it changes which theorem the declarations below
state.  Constructing the stalk algebra as an explicit `letI` inside each proof (as §1 does) is what
keeps that choice local.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits IsDedekindDomain
open scoped WithZero AlgebraicGeometry.Scheme

namespace AlgebraicGeometry
namespace Adelic

/-! ## §1. The stalk `k`-algebra and its compatibility with `K(C)` -/

section StalkAlgebra

variable {k : Type u} [Field k]

/-- **The structure homomorphism into a stalk factors through the global sections.**
`k → 𝒪_{C,x}` is `constMap C : k → Γ(C,⊤)` followed by the germ at `x`.

Both sides are the stalk map of `C.hom` precomposed with `ΓSpecIso.inv`; mathlib's
`Hom.germ_stalkMap` is exactly the statement that the germ commutes past a stalk map.
This is the lemma that ties `Picard/TangentSpaceStalkAlgebra.lean`'s stalk algebra to
`Adelic/GateInstances.lean`'s function-field algebra, which is built from `constMap`. -/
theorem stalkStructureHom_eq_constMap_germ (C : Over (Spec (CommRingCat.of k)))
    (x : C.left) :
    stalkStructureHom C.hom x
      = Scheme.constMap C ≫ C.left.presheaf.germ ⊤ x trivial := by
  rw [stalkStructureHom, Scheme.constMap, Category.assoc]
  congr 1
  exact C.hom.germ_stalkMap ⊤ x trivial

/-- **The two `k`-algebra structures agree.**  The image of a constant `c : k` in `K(C)`
is the same whether one goes `k → 𝒪_P → K(C)` (through `stalkStructureHom`) or directly
`k → K(C)` (through `Scheme.functionFieldAlgebra`).

This is what makes the stalk-level argument of §2 usable in the order language of the
adelic lane, whose `algebraMap k K(X)` is the latter.  Proof: rewrite the stalk map as
`constMap ≫ germ` (`stalkStructureHom_eq_constMap_germ`), then both sides are
`algebraMap Γ(C,⊤) K(C) ∘ constMap` — the first by mathlib's
`functionField_isScalarTower`, the second by `Scheme.algebraMap_functionField_eq`. -/
theorem algebraMap_stalk_functionField (C : Over (Spec (CommRingCat.of k)))
    [IsIntegral C.left] (x : C.left) (c : k) :
    algebraMap (C.left.presheaf.stalk x) C.left.functionField
        ((stalkStructureHom C.hom x).hom c)
      = algebraMap k C.left.functionField c := by
  haveI : Nonempty (⊤ : C.left.Opens) := Scheme.nonempty_top_opens C.left
  letI : Algebra ↥Γ(C.left, ⊤) (C.left.presheaf.stalk x) :=
    C.left.presheaf.algebra_section_stalk (⟨x, trivial⟩ : (⊤ : C.left.Opens))
  haveI : IsScalarTower ↥Γ(C.left, ⊤) (C.left.presheaf.stalk x)
      C.left.functionField :=
    functionField_isScalarTower C.left ⊤ ⟨x, trivial⟩
  have h1 : (stalkStructureHom C.hom x).hom c
      = algebraMap ↥Γ(C.left, ⊤) (C.left.presheaf.stalk x)
        ((Scheme.constMap C).hom c) := by
    rw [stalkStructureHom_eq_constMap_germ C x]; rfl
  rw [h1, ← IsScalarTower.algebraMap_apply]
  rfl

/-- **The tower `k → 𝒪_P → K(C)`** — binder (2) of `GlobalGeneration.lean` §7, now built.
Immediate from `algebraMap_stalk_functionField`. -/
theorem isScalarTower_stalk_functionField (C : Over (Spec (CommRingCat.of k)))
    [IsIntegral C.left] (x : C.left) :
    letI : Algebra k (C.left.presheaf.stalk x) := stalkAlgebra C.hom x
    IsScalarTower k (C.left.presheaf.stalk x) C.left.functionField := by
  letI : Algebra k (C.left.presheaf.stalk x) := stalkAlgebra C.hom x
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  exact (algebraMap_stalk_functionField C x c).symm

end StalkAlgebra

/-! ## §2. `κ(P) = k` at a closed point, over an algebraically closed base

Mathlib's `AlgebraicGeometry.residueFieldIsoBase` gives `κ(x) ≅ k` as a `CommRingCat`
iso for a closed point of a scheme locally of finite type over an algebraically closed
`k`.  What is needed here is the *ring-map* form: that the composite
`k → 𝒪_x → κ(x)` — the map the order language sees — is bijective.  That follows once
the composite is identified with the iso's inverse, which is `residue_stalkStructureHom_eq`
below: an identity of `Spec`-morphisms, checked through `Spec.map_injective`. -/

section ResidueBijective

variable {k : Type u} [Field k]

/-- **A prime divisor of a curve is a closed point.**  On an irreducible scheme all of
whose points have coheight `≤ 1` (the curve condition, supplied by
`coheight_le_one_of_curve`), a point of coheight `1` is not the generic point — the
generic point has coheight `0` — hence is closed by
`isClosed_singleton_of_coheight_le_one` (`Adelic/FiniteMapToP1.lean`).

This is why the closedness input of `residueFieldIsoBase` costs nothing here: it is part
of what `X.PrimeDivisor` already asserts. -/
theorem isClosed_primeDivisor {X : Scheme.{u}} [IrreducibleSpace X]
    (hdim : ∀ w : X, Order.coheight w ≤ 1) (P : X.PrimeDivisor) :
    IsClosed ({P.point} : Set X) := by
  refine isClosed_singleton_of_coheight_le_one hdim ?_
  intro hgen
  -- the generic point is maximal in the specialisation order, so has coheight `0`
  have hmax : IsMax (genericPoint X) := fun y hy => genericPoint_specializes y
  have h0 : Order.coheight P.point = 0 := by
    rw [hgen]; exact Order.IsMax.coheight_eq_zero hmax
  rw [P.coheight] at h0
  exact absurd h0 (by simp)

/-- **Every non-generic point of a curve has coheight exactly one** — hence *is* a prime divisor.

`coheight_le_one_of_curve` (`Adelic/FiniteMapToP1.lean`) gives `≤ 1` from smoothness.  The
reverse needs only that a non-generic point is not maximal in the specialisation order: the
generic point satisfies `P ≤ genericPoint` always (mathlib's convention is
`x ≤ y ↔ y ⤳ x`, and the generic point specialises to everything), so if `P` were maximal it
would satisfy `genericPoint ≤ P` too and antisymmetry would force `P = genericPoint`.

**Why this is worth having as a theorem.** `X.PrimeDivisor` bundles a point with a proof that
its coheight is `1`, and until now AJC had no way to *produce* one on a curve:
`Scheme.WeilDivisor.ofClosedPoint` case-splits on `Order.coheight P = 1` and falls back to the
zero divisor when it cannot be shown, so every statement quantified over `X.PrimeDivisor` was
formally at risk of being vacuous.  `primeDivisorOfNotGeneric` below removes that risk. -/
theorem coheight_eq_one_of_ne_genericPoint (C : Over (Spec (CommRingCat.of k)))
    [IrreducibleSpace C.left] [SmoothOfRelativeDimension 1 C.hom]
    {x : C.left} (hx : x ≠ genericPoint C.left) :
    Order.coheight x = 1 := by
  refine le_antisymm (coheight_le_one_of_curve C x) ?_
  -- `x` is not maximal (the generic point strictly dominates it), so its coheight is not `0`
  have hnotmax : ¬ IsMax x := by
    intro hmax
    exact hx ((genericPoint_specializes x).antisymm
      (hmax (genericPoint_specializes x))).symm.eq
  have hne : Order.coheight x ≠ 0 := fun h => hnotmax (Order.coheight_eq_zero.mp h)
  exact Order.one_le_iff_ne_zero.mpr hne

/-- **A non-generic point of a curve, packaged as a prime divisor.**  The producer that makes
every `∀ P : C.left.PrimeDivisor` statement in this lane non-vacuous. -/
def primeDivisorOfNotGeneric (C : Over (Spec (CommRingCat.of k)))
    [IrreducibleSpace C.left] [SmoothOfRelativeDimension 1 C.hom]
    {x : C.left} (hx : x ≠ genericPoint C.left) :
    C.left.PrimeDivisor :=
  ⟨x, coheight_eq_one_of_ne_genericPoint C hx⟩

/-- **The composite `k → 𝒪_x → κ(x)` is the inverse of mathlib's `residueFieldIsoBase`.**

Both are morphisms `k ⟶ κ(x)` in `CommRingCat`; `Spec` is faithful, so it suffices to
check the induced `Spec` morphisms agree, and there both sides unfold to
`X.fromSpecResidueField x ≫ C.hom` — the left by `Scheme.fromSpecResidueField` plus
`fromSpecStalk_comp_eq` (`Picard/TangentSpaceStalkAlgebra.lean`), the right by mathlib's
`SpecMap_residueFieldIsoBase_inv`. -/
theorem residue_stalkStructureHom_eq [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType C.hom]
    (x : C.left) (hx : IsClosed ({x} : Set C.left)) :
    stalkStructureHom C.hom x ≫ C.left.residue x
      = (residueFieldIsoBase C.hom x hx).inv := by
  apply Spec.map_injective
  rw [SpecMap_residueFieldIsoBase_inv, Spec.map_comp, Scheme.fromSpecResidueField,
    ← fromSpecStalk_comp_eq, Category.assoc]

/-- **`k → κ(x)` is bijective at a closed point of a curve over an algebraically closed
base.**  Immediate from `residue_stalkStructureHom_eq`: an iso of `CommRingCat` has
bijective underlying ring map.

This is the statement that replaces `GlobalGeneration.lean` §7's three-binder route: no
`Module.Finite k κ_P` gate is consumed, because mathlib obtains integrality of `κ(x)` over
`k` from `LocallyOfFiniteType` through the Jacobson-space finiteness criterion. -/
theorem bijective_residue_comp_stalkStructureHom [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType C.hom]
    (x : C.left) (hx : IsClosed ({x} : Set C.left)) :
    Function.Bijective
      ((C.left.residue x).hom.comp (stalkStructureHom C.hom x).hom) := by
  have h : (C.left.residue x).hom.comp (stalkStructureHom C.hom x).hom
      = (residueFieldIsoBase C.hom x hx).inv.hom := by
    rw [← residue_stalkStructureHom_eq C x hx]; rfl
  rw [h]
  exact (ConcreteCategory.isIso_iff_bijective
    (residueFieldIsoBase C.hom x hx).inv).mp inferInstance

/-- **Every stalk element is a constant modulo the maximal ideal.**  The surjectivity half
of `bijective_residue_comp_stalkStructureHom`, restated as the approximation statement on
the stalk: for `a ∈ 𝒪_x` there is `c : k` with `a − c ∈ 𝔪_x`. -/
theorem exists_const_sub_mem_maximalIdeal [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType C.hom]
    (x : C.left) (hx : IsClosed ({x} : Set C.left))
    (a : C.left.presheaf.stalk x) :
    ∃ c : k, a - (stalkStructureHom C.hom x).hom c ∈
      IsLocalRing.maximalIdeal (C.left.presheaf.stalk x) := by
  obtain ⟨c, hc⟩ := (bijective_residue_comp_stalkStructureHom C x hx).surjective
    ((C.left.residue x).hom a)
  rw [RingHom.comp_apply] at hc
  refine ⟨c, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff]
  change (C.left.residue x).hom _ = 0
  rw [map_sub, hc, sub_self]

end ResidueBijective

/-! ## §3. `HasRationalResidues`, discharged

The stalk statement of §2 is now translated into the order language of the adelic lane.
The translation has two steps and both are already available:

* `f` with `ord_P f ≥ 0` lifts to `a ∈ 𝒪_P` — `exists_stalk_lift_of_order_nonneg`
  (`ChiLedger.lean` §N14b);
* `a − c ∈ 𝔪_P` becomes `ord_P (f − c) ≥ 1` — `mem_orderGe_one_iff_mem_maximalIdeal`
  (`GlobalGeneration.lean` §7), whose statement is phrased on `orderGe P 1` rather than on
  the raw inequality precisely so that `f = c` is admitted (the project's `ord_P 0 = 0`
  convention would make the inequality form false there).

The `k`-action bookkeeping is `algebraMap_stalk_functionField` (§1): the constant produced
on the stalk and the constant the order language expects are the same element of `K(C)`. -/

section Discharge

variable {k : Type u} [Field k]

/-- **`HasRationalResidues` holds at every prime divisor of a curve over an algebraically
closed field** — the residue fact of the campaign, now a theorem on AJC's own curve
hypotheses rather than on unbuilt stalk binders.

Compare `hasRationalResidues_of_isAlgClosed` (`GlobalGeneration.lean` §7), which proves the
same conclusion but from `[Algebra k 𝒪_P]`, `[IsScalarTower k 𝒪_P K(X)]` and
`[Module.Finite k κ_P]`, none of which AJC constructs.  Here the first two are built (§1)
and the third is not needed (§2). -/
theorem hasRationalResidues_of_isAlgClosed_curve [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    [LocallyOfFiniteType C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (P : C.left.PrimeDivisor) :
    HasRationalResidues k P := by
  intro f hf
  rcases eq_or_ne f 0 with rfl | hf0
  · refine ⟨0, ?_⟩
    rw [map_zero, sub_zero]
    exact (orderGe P 1).zero_mem
  -- lift `f` to the stalk
  obtain ⟨a, ha⟩ := exists_stalk_lift_of_order_nonneg hf0
    ((mem_orderGe_of_ne_zero hf0).mp hf)
  -- `P.point` is a closed point of the curve, so `κ(P) = k`
  have hclosed : IsClosed ({P.point} : Set C.left) :=
    isClosed_primeDivisor (coheight_le_one_of_curve C) P
  obtain ⟨c, hc⟩ := exists_const_sub_mem_maximalIdeal C P.point hclosed a
  refine ⟨c, ?_⟩
  have himg := (mem_orderGe_one_iff_mem_maximalIdeal P
    (a - (stalkStructureHom C.hom P.point).hom c)).mpr hc
  rw [map_sub, ha, algebraMap_stalk_functionField C P.point c] at himg
  exact himg

/-! ### The N14 residue-finiteness gate is discharged too

`Module.Finite k (localStepTgt k P 1)` — "`[κ(P):k] < ∞`" — is carried as an instance binder
by roughly twenty statements across the adelic lane, and `ChiLedger.lean` §N14 describes it
as "the gated keystone input, not re-proved here".  It is now **provable** on curve
hypotheses, and cheaply, because `hasRationalResidues_of_isAlgClosed_curve` above needs no
finiteness at all: approximation by constants says every class in the quotient is a
`k`-multiple of the class of `1`, so the quotient is spanned by a *single* vector.

This is why §3 is ordered the way it is.  Proving `residueDeg k P = 1` through
`residueDeg_eq_one_iff_hasRationalResidues` would require the finiteness binder, since that
equivalence carries it; deriving finiteness from the approximation statement *first* removes
the binder from everything downstream, including `residueDeg_eq_one_of_isAlgClosed_curve`
itself. -/

/-- **The residue field is finite-dimensional, from approximation by constants alone.**
If every function regular at `P` agrees with a constant to first order, then
`κ(P) = orderGe P 0 ⧸ orderGe P 1` is spanned by the class of `1`, hence finitely generated.

Stated on `HasRationalResidues` rather than on curve hypotheses so that it is reusable: this
is the general fact that the approximation statement is *strictly stronger* than the
finiteness gate N14 assumes.  The spanning computation is the one in the `←` branch of
`residueDeg_eq_one_iff_hasRationalResidues`; here it is used for finiteness rather than for
the rank bound. -/
theorem finite_localStepTgt_one_of_hasRationalResidues
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Scheme.IsRegularInCodimensionOne X] [Algebra k X.functionField]
    [IsConstantField k X] (P : X.PrimeDivisor)
    (happrox : HasRationalResidues k P) :
    Module.Finite k (localStepTgt k P 1) := by
  have hone : (1 : X.functionField) ∈ orderGeSub k P (1 - 1) := by
    rw [mem_orderGeSub]
    exact Or.inr (by rw [Scheme.RationalMap.order_one]; norm_num)
  -- every class is a `k`-multiple of the class of `1`
  have hspan : (⊤ : Submodule k (localStepTgt k P 1)) ≤
      Submodule.span k {Submodule.Quotient.mk (p := Submodule.comap
        (orderGeSub k P (1 - 1)).subtype (orderGeSub k P 1)) ⟨1, hone⟩} := by
    intro z _
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨c, hc⟩ := happrox (g : X.functionField)
      (by
        have hg2 := g.2
        rw [mem_orderGeSub] at hg2
        exact orderGe_antitone (by norm_num) hg2)
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap,
      Submodule.subtype_apply]
    have hval : ((c • ⟨1, hone⟩ - g : orderGeSub k P (1 - 1)) :
        X.functionField) = -(g - algebraMap k X.functionField c) := by
      change c • (1 : X.functionField) - (g : X.functionField) = _
      rw [Algebra.smul_def, mul_one]
      ring
    rw [mem_orderGeSub, hval]
    exact (orderGe P 1).neg_mem hc
  -- a module whose `⊤` sits inside a one-vector span is finitely generated
  have htop : (⊤ : Submodule k (localStepTgt k P 1))
      = Submodule.span k {Submodule.Quotient.mk (p := Submodule.comap
        (orderGeSub k P (1 - 1)).subtype (orderGeSub k P 1)) ⟨1, hone⟩} :=
    le_antisymm hspan le_top
  exact Module.Finite.of_fg_top (htop ▸ Submodule.fg_span_singleton _)

/-- **The N14 residue-finiteness gate, discharged on curve hypotheses.**
`[κ(P):k] < ∞` at every prime divisor of a curve over an algebraically closed base.

Not registered as a global instance: the lane's statements take it as an explicit binder and
a global instance here would change which `k`-action they synthesize against (see the diamond
note in the module docstring).  Consumers should apply it explicitly, or `haveI` it. -/
theorem finite_localStepTgt_one_of_isAlgClosed_curve [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    [LocallyOfFiniteType C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (P : C.left.PrimeDivisor) :
    Module.Finite k (localStepTgt k P 1) :=
  finite_localStepTgt_one_of_hasRationalResidues P
    (hasRationalResidues_of_isAlgClosed_curve C P)

/-- **The residue degree is one** at every prime divisor of a curve over an algebraically
closed base: `[κ(P) : k] = 1`.

This is the fact that `SectionBounds.lean` §4 and `GlobalGeneration.lean` §5–§7 both reduce
to and both leave open.  It closes item 1 of the two-item residue list in
`SectionBounds.lean` §4.

Note there is **no finiteness binder**: it is supplied internally by
`finite_localStepTgt_one_of_isAlgClosed_curve`, so this statement's hypotheses are the curve
hypotheses and nothing else. -/
theorem residueDeg_eq_one_of_isAlgClosed_curve [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    [LocallyOfFiniteType C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (P : C.left.PrimeDivisor) :
    residueDeg k P = 1 :=
  haveI := finite_localStepTgt_one_of_isAlgClosed_curve C P
  (residueDeg_eq_one_iff_hasRationalResidues k P).mpr
    (hasRationalResidues_of_isAlgClosed_curve C P)

/-! ## §4. The consequences, with the residue input no longer a hypothesis

`GlobalGeneration.lean` §6 draws two conclusions from `HasRationalResidues` — uniform global
generation with threshold `b + 1`, and the unweighted principal-degree-zero statement — but
carries it as a hypothesis `hres`.  §3 above discharges `hres` on curve hypotheses, so both
conclusions can be restated with **one** open input instead of two.

Read the remaining hypothesis carefully: `hledger` is the closed χ-ledger.  An earlier
version of this paragraph said it was "*still* not a theorem in this project", proved only on
the effective cone, with the negative part needing an input the lane does not have.  **That
is out of date**: `Adelic/LedgerClosure.chi_eq_of_bump` proves the closed ledger at every Weil
divisor from the one-point bump alone, because `hbump` admits an arbitrary base divisor and so
the telescope is not confined to the effective cone.

The `hledger` hypothesis below is therefore discharged wherever the bump is available, and the
lane's residual input is the **bump**.  At overlap primes that is one application of
`chi_add_eq_residueDeg`, consuming the ledger exact sequence's connecting/surjectivity data plus
strong approximation; off the overlap that producer is unavailable (it requires
`P.point ∈ U₀ ⊓ U₁`).  **And on a genuine cover (`U₀ ⊔ U₁ = ⊤`) with finite-dimensional chart
sections and a prime divisor off a chart, both the bump and `hledger` are outright FALSE**
(`ChiUnconditional.not_bump_of_notMem_left`, `ChiUnconditional.ledger_refuted_of_notMem_left`):
χ is bounded along the tower `n·P` while both demand linear growth.  So the reduction below is a
reduction from two open inputs to one *only on a cover where those hypotheses can hold* —
otherwise it is a valid implication with an unsatisfiable hypothesis.  Subject to that, the
remaining one is a local statement at a single prime divisor rather than a global identity. -/

/-- **The weighted degree is the geometric degree on a curve over an algebraically closed
base.**  `deg_k = deg`, with the residue-degree-one input discharged rather than assumed.

This is what makes the adelic lane's weighted statements into statements about the geometric
`Scheme.WeilDivisor.degree` that the rest of the project uses. -/
theorem degK_eq_degree_of_isAlgClosed_curve [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
    [IsNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    [LocallyOfFiniteType C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (D : C.left.WeilDivisor) :
    degK k D = Scheme.WeilDivisor.degree D :=
  degK_eq_degree_of_residueDeg_eq_one k
    (fun P _ => residueDeg_eq_one_of_isAlgClosed_curve C P)

/-- **Principal divisors have geometric degree zero on a curve over an algebraically closed
base, given the closed ledger** — the adelic route to the open leaf
`Scheme.WeilDivisor.principal_degree_zero`, now resting on the **ledger alone**.

Compare `degree_principal_eq_zero_of_hasRationalResidues` (`GlobalGeneration.lean` §6),
which takes both the ledger *and* the approximation statement.  The second hypothesis is
gone here.

This is the sharpest honest form of the leaf reachable today.  It is deliberately **not**
substituted into `Scheme.WeilDivisor.principal_degree_zero`, whose statement mentions no
hypotheses: doing so would make a hypothesis-free theorem depend silently on the ledger. -/
theorem degree_principal_eq_zero_of_isAlgClosed_curve [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
    [IsNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    [LocallyOfFiniteType C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (U₀ U₁ : C.left.Opens)
    (hledger : ∀ D : C.left.WeilDivisor,
      chi k U₀ U₁ D = chi k U₀ U₁ 0 + degK k D)
    {g : C.left.functionField} (hg : g ≠ 0) :
    Scheme.WeilDivisor.degree (Scheme.WeilDivisor.principal g hg) = 0 :=
  degree_principal_eq_zero_of_residueDeg_eq_one k U₀ U₁ hledger hg
    (fun P _ => residueDeg_eq_one_of_isAlgClosed_curve C P)

/-- **Uniform global generation with threshold `b + 1`**, with the residue input discharged.
Above weighted degree `b`, `𝒪(D)` is generated by global sections at *every* prime divisor,
the residue-degree bound being `r = 1` on a curve over an algebraically closed base.

Still single-field, and still conditional on the ledger, the base vanishing and the peel —
see the three-gap discussion in `BoundedVanishing.lean`. -/
theorem exists_bound_forall_generatedAt_of_isAlgClosed_curve [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
    [IsNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    [LocallyOfFiniteType C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [∀ D : C.left.WeilDivisor, Module.Finite k (sectionSub k ⊤ D)]
    (U₀ U₁ : C.left.Opens)
    (hledger : ∀ D : C.left.WeilDivisor,
      chi k U₀ U₁ D = chi k U₀ U₁ 0 + degK k D)
    (D₀ : C.left.WeilDivisor) (hbase : Subsingleton (H1Mod k U₀ U₁ D₀))
    (hpeel : ∀ D' : C.left.WeilDivisor,
      (∀ P : C.left.PrimeDivisor, (show C.left.PrimeDivisor →₀ ℤ from D₀) P ≤
        (show C.left.PrimeDivisor →₀ ℤ from D') P) →
      Peel k U₀ U₁ D₀ D') :
    ∃ b : ℤ, ∀ D : C.left.WeilDivisor, b ≤ degK k D →
      ∀ P : C.left.PrimeDivisor, GeneratedAt k D P :=
  haveI : ∀ P : C.left.PrimeDivisor, Module.Finite k (localStepTgt k P 1) :=
    fun P => finite_localStepTgt_one_of_isAlgClosed_curve C P
  exists_bound_forall_generatedAt k U₀ U₁ hledger D₀ hbase hpeel 1
    (fun P => le_of_eq (residueDeg_eq_one_of_isAlgClosed_curve C P))

/-- **The threshold conclusions are not vacuous, unconditionally on a curve.**  For every bound
`b` and every prime divisor `P`, some multiple `n·P` has weighted degree `≥ b`.

`exists_degK_ge` (`BoundedVanishing.lean`) proves this but carries the residue-finiteness
binder; here it is discharged, so the non-vacuity of every `∃ b, ∀ D, b ≤ deg_k D → …`
conclusion in the lane is unconditional on curve hypotheses.  Worth having as a statement
rather than a remark: that quantifier shape is exactly the one that *can* be satisfied
trivially, and a reader is entitled to see it ruled out. -/
theorem exists_degK_ge_of_isAlgClosed_curve [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
    [IsNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    [LocallyOfFiniteType C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (b : ℤ) (P : C.left.PrimeDivisor) :
    ∃ n : ℕ, b ≤ degK k ((n : ℤ) • pointDivisor P : C.left.WeilDivisor) :=
  haveI := finite_localStepTgt_one_of_isAlgClosed_curve C P
  exists_degK_ge k b P

/-! ### Riemann–Roch in the vanishing range, on the geometric degree

The lane's numerical conclusions are all stated on the residue-weighted `deg_k`, because that
is what the χ-ledger telescopes to.  On a curve over an algebraically closed base the two
degrees agree (`degK_eq_degree_of_isAlgClosed_curve`), so those conclusions can be restated on
`Scheme.WeilDivisor.degree` — the invariant the rest of the project, and the classical
statement, use.

`exists_bound_ell_eq_degree_of_isAlgClosed_curve` below is the `ℓ(D) = χ(0) + deg D` form (the
weighted original is `BoundedVanishing.exists_bound_ell_eq`); with `χ(0) = 1 − g` it is the
classical `ℓ(D) = deg D + 1 − g` for `deg D` large.  Note it is *not* free of the lane's open
inputs: it is `exists_bound_ell_eq` with the degree translated, so the ledger, the base
vanishing and the peel are all still there.  What the translation removes is only the
residue-weighting, which was never an open input but was an obstacle to *quoting* the result. -/

/-- **The Riemann inequality on the geometric degree.**  `deg D + χ(0) ≤ ℓ(D)` for every
divisor on a curve over an algebraically closed base, given the closed ledger.  The weighted
form is `degK_add_chi_zero_le_ell`; here the weighting is discharged. -/
theorem degree_add_chi_zero_le_ell_of_isAlgClosed_curve [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
    [IsNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    [LocallyOfFiniteType C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (U₀ U₁ : C.left.Opens)
    (hledger : ∀ D : C.left.WeilDivisor,
      chi k U₀ U₁ D = chi k U₀ U₁ 0 + degK k D)
    (D : C.left.WeilDivisor) :
    Scheme.WeilDivisor.degree D + chi k U₀ U₁ 0 ≤ (ell k D : ℤ) := by
  rw [← degK_eq_degree_of_isAlgClosed_curve C D]
  exact degK_add_chi_zero_le_ell k U₀ U₁ hledger D

/-- **Riemann–Roch in the vanishing range, on the geometric degree.**  There is a threshold
past which `ℓ(D) = χ(0) + deg D` — an equality, not merely the Riemann inequality — for every
divisor of large geometric degree on a curve over an algebraically closed base.

With `χ(0) = 1 − g` this is the classical `ℓ(D) = deg D + 1 − g`.  The threshold is stated on
`deg` rather than `deg_k` because the two coincide here.

Conditional on the lane's three inputs (closed ledger, base vanishing, peel) exactly as
`exists_bound_ell_eq` is; the residue-weighting is what has been discharged, not those. -/
theorem exists_bound_ell_eq_degree_of_isAlgClosed_curve [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
    [IsNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    [LocallyOfFiniteType C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (U₀ U₁ : C.left.Opens)
    (hledger : ∀ D : C.left.WeilDivisor,
      chi k U₀ U₁ D = chi k U₀ U₁ 0 + degK k D)
    (D₀ : C.left.WeilDivisor) (hbase : Subsingleton (H1Mod k U₀ U₁ D₀))
    (hpeel : ∀ D' : C.left.WeilDivisor,
      (∀ P : C.left.PrimeDivisor, (show C.left.PrimeDivisor →₀ ℤ from D₀) P ≤
        (show C.left.PrimeDivisor →₀ ℤ from D') P) →
      Peel k U₀ U₁ D₀ D') :
    ∃ b : ℤ, ∀ D : C.left.WeilDivisor, b ≤ Scheme.WeilDivisor.degree D →
      (ell k D : ℤ) = chi k U₀ U₁ 0 + Scheme.WeilDivisor.degree D := by
  obtain ⟨b, hb⟩ := exists_bound_ell_eq k U₀ U₁ hledger D₀ hbase hpeel
  refine ⟨b, fun D hD => ?_⟩
  rw [← degK_eq_degree_of_isAlgClosed_curve C D] at hD ⊢
  exact hb D hD

end Discharge

/-! ## §5. Extension uniformity: the statement, at last written down

The lane's docstrings (`BoundedVanishing.lean`, `GlobalGeneration.lean` §"three gaps",
`SectionBounds.lean` §"What is NOT proved here") record gap (2), **extension uniformity**, as
not merely unproved but *not statable*: "the invariants here are pinned on a chosen 2-affine
cover, and `RiemannRoch/CurveBaseChange.lean` does not transport that cover to `C_κ`".  A
memory note to the same effect warned against re-planning it wrongly.

**That is too strong, and this section corrects it.**  `CurveBaseChange.lean` §3 *does*
transport a cover: `AffineCoverMVSquare.baseChangeField` produces a bundled 2-affine cover of
`C_κ` from one of `C`, and its `U₁`/`U₂` are ordinary `Opens`, which is what `chi`, `ell`,
`h1dim` and `H1Mod` consume.  Together with the `κ`-algebra on `K(C_κ)` and the
`IsConstantField` gate — both available from `GateInstances.lean` applied to
`Scheme.baseChangeField C κ`, whose curve instances `CurveBaseChange.lean` §2 supplies — the
uniformity predicate can be written down.  `UniformlyBoundedVanishing` below does that.

So the honest status of gap (2) is: **statable, and open**.  That is a weaker claim than
"proved" and a stronger one than "not statable", and the distinction matters because the two
call for different next steps — the second says build cover transport first, the first says the
transport exists and what is missing is the mathematics of flat base change for the invariants.

What is genuinely missing, stated as precisely as I can:

* `ℓ`, `h¹` and `χ` are `κ`-dimensions on `C_κ` and `k`-dimensions on `C`.  Uniformity needs
  them *compared*, which is flat base change for the section spaces —
  `Γ(C_κ, 𝒪(D_κ)) ≃ Γ(C, 𝒪(D)) ⊗_k κ` — and no such comparison exists in this project.
* Even the divisor correspondence is missing: `D ↦ D_κ` requires pulling a Weil divisor back
  along `C_κ ⟶ C`, and prime divisors need not stay prime (a closed point can split).  There is
  no `WeilDivisor` pullback in AJC.

Neither is a cover-transport problem.  Recording the predicate without either of them is
deliberate: it makes the gap a statement someone can attack, rather than a paragraph asserting
it cannot be written.
-/

section Uniformity

variable {k : Type u} [Field k]

/-- **The extension-uniform bounded-vanishing predicate** — cluster P's gap (2), written down.

`UniformlyBoundedVanishing C S` says: there is a **single** threshold `b`, independent of the
extension, such that for every field extension `κ/k` and every Weil divisor `D` of the
base-changed curve `C_κ` with `deg_κ D ≥ b`, the cover cohomology `Ȟ¹(D)` computed on the
base-changed cover `S_κ` vanishes.

Contrast `exists_bound_subsingleton_h1Mod`, which fixes `k`, the cover and the base divisor:
there the bound may depend on all three.  Here `b` is chosen before `κ` is.

This is a **definition, not a theorem** — nothing below proves it, and §5's docstring lists the
two genuinely missing inputs (flat base change for the section spaces, and a `WeilDivisor`
pullback along `C_κ ⟶ C`).  Its value is that the predicate typechecks, which the lane's
docstrings claimed it could not. -/
def UniformlyBoundedVanishing (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (S : C.left.AffineCoverMVSquare) : Prop :=
  ∃ b : ℤ, ∀ (κ : Type u) (_ : Field κ) (_ : Algebra k κ),
    ∀ D : (Scheme.baseChangeField C κ).left.WeilDivisor,
      b ≤ degK κ D → Subsingleton
        (H1Mod κ (S.baseChangeField κ).U₁ (S.baseChangeField κ).U₂ D)

/-- **The instance-binder form of the same predicate.**  `UniformlyBoundedVanishing` above
quantifies over the `Field κ` and `Algebra k κ` structures *positionally*, which is the
faithful reading of "for every field extension" but makes the predicate awkward to use: a
consumer must supply those structures as explicit arguments, and doing so forces Lean to
unfold the base-change pullback and re-synthesise the curve-instance tower inside `H1Mod`.

This version takes them as instance binders instead.  The two are equivalent
(`uniformlyBoundedVanishing_iff_instBinders`), so nothing about the mathematical content
changes; what changes is that instance resolution does the work at the use site. -/
def UniformlyBoundedVanishing' (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (S : C.left.AffineCoverMVSquare) : Prop :=
  ∃ b : ℤ, ∀ (κ : Type u) [Field κ] [Algebra k κ],
    ∀ D : (Scheme.baseChangeField C κ).left.WeilDivisor,
      b ≤ degK κ D → Subsingleton
        (H1Mod κ (S.baseChangeField κ).U₁ (S.baseChangeField κ).U₂ D)

/-- **The two spellings of extension uniformity are the same predicate, definitionally.**
Positional and instance-binder quantification over the extension structures differ only in
binder annotation, so `Iff.rfl` closes it: instance-implicit and explicit binders erase to the
same `∀`.

The proof is worth a note, because the obvious tactic route **fails**.  Writing
`constructor` and then `exact ⟨b, fun κ _ _ => hb κ ‹Field κ› ‹Algebra k κ›⟩` blows the
`whnf` heartbeat limit (200000, machine-checked): unifying the two `Subsingleton (H1Mod …)`
bodies makes Lean unfold the base-change pullback and re-synthesise the curve-instance tower.
`Iff.rfl` never compares the bodies, so it costs nothing — and it proves something stronger
than the `Iff` asked for, namely that the two definitions are *defeq* rather than merely
interderivable.

This is the same heartbeat wall that this section's closing note records for instantiating the
predicate at `κ = k`, met from a different direction — evidence that the cost is intrinsic to
unfolding the base change, not an artefact of one proof attempt. -/
theorem uniformlyBoundedVanishing_iff_instBinders
    (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (S : C.left.AffineCoverMVSquare) :
    UniformlyBoundedVanishing C S ↔ UniformlyBoundedVanishing' C S :=
  Iff.rfl

/-! **What is now instantiable, and what still is not.**  An earlier version of this note
recorded that the obvious sanity check on the predicate — instantiate at `κ = k` and read off
a single-field bound on `C_k` — does not elaborate, exceeding the `whnf` heartbeat limit
because supplying `Field k` and `Algebra.id k` positionally forces Lean to unfold the
base-change pullback and re-synthesise the whole curve-instance tower inside `H1Mod`.  It
also said that the natural fix, instance binders, "changes the predicate's shape".

That last clause was wrong on the *shape* question and right on the cost.
`uniformlyBoundedVanishing_iff_instBinders` above settles the shape: the instance-binder form
`UniformlyBoundedVanishing'` is the same predicate **definitionally** (`Iff.rfl`), so using it
weakens nothing.  What the predecessor got right is the price: my first attempt at that very
equivalence, via `constructor` and `exact`, hit the identical 200000-heartbeat `whnf` wall,
because it made Lean unify the two `Subsingleton (H1Mod …)` bodies and so unfold the
base-change tower.  Two independent proof attempts hitting the same wall from different
directions is good evidence the cost is intrinsic to unfolding the base change rather than an
artefact — which is what the predecessor claimed and what raising `maxHeartbeats` would have
hidden.

So: the quantifier spelling is free to change, and the base-change unfolding is not.  A
consumer should use the primed form and still expect to pay at the point where a specific `κ`
is supplied.

Still genuinely missing, and unaffected by any of this: flat base change for the section
spaces (`Γ(C_κ, 𝒪(D_κ)) ≃ Γ(C,𝒪(D)) ⊗_k κ`) and a `WeilDivisor` pullback along `C_κ ⟶ C`.
Neither predicate is proved at any curve. -/

end Uniformity

/-! ## §6. Cluster P on a curve, assembled: every discharge applied at once

The lane's results are spread over six modules and each carries the hypotheses it needs.  A
consumer asking "what does AJC actually give me on a curve, and what must I still supply?"
should not have to reassemble that.  This section answers it in single statements.

**What is supplied here and no longer asked of the caller:** the residue-degree-one fact and
the N14 residue-finiteness gate (§3), the translation from the weighted `deg_k` to the
geometric `degree` (§4), and — the change that makes this section worth writing — the closed
χ-ledger, which `Adelic/LedgerClosure.chi_eq_of_bump` derives from the one-point bump.

**What the caller must still supply, and it is exactly two things:**

1. `hbump` — the one-point χ-equality `χ(1·P + E) = χ(E) + [κ(P):k]`, uniformly in `P` and
   `E`.  One application of `ChiLedger.chi_add_eq_residueDeg` per instance, which consumes the
   ledger exact sequence's connecting/surjectivity data and the strong-approximation input.
2. `hbase` + the peel — one base vanishing, and the one-point peel.  By
   `LedgerClosure.pointPeel_of_pointPeel_on_overlap` the peel is only needed at primes meeting
   the overlap.

Both are one-point local statements.  Neither is a gate class, and nothing below is a `sorry`.
Read the count honestly: two open inputs is not zero, and this section does not make the lane
unconditional.

**A note on the instance binders, because getting them wrong cost a build cycle here.**  The
theorems below take **no** `[Algebra k K(C)]` or `[IsConstantField k C.left]` binder, matching
their §4 counterparts.  Those instances come from the *scoped* `Scheme.functionFieldAlgebra` and
`Scheme.instIsConstantField` (`GateInstances.lean`), activated by this file's
`open scoped AlgebraicGeometry.Scheme`.

Writing them as explicit binders instead — the natural thing to do — **fails**, with an
application type mismatch showing `@chi k … inst✝¹ …` against
`@chi k … (Scheme.functionFieldAlgebra C) …`: the binder shadows the scoped instance and the two
`Algebra k K(C)` structures are not syntactically identical, so `chi` and `degK` get re-pinned
and no conclusion matches its consumer.  That is precisely the instance-**diamond** hazard filed
as project memory by an earlier session on this task, met in the wild; the fix is to drop the
binders and let the scoped instances be found.  Recorded because the error message names `chi`,
not the instance, and reads like a defect in the mathematics. -/

section ClusterP

variable {k : Type u} [Field k]

/-- **Riemann–Roch in the vanishing range on a curve, with every available discharge applied.**

For a curve over an algebraically closed base there is a threshold `b` past which

`ℓ(D) = χ(0) + deg D`

on the **geometric** degree — the classical `ℓ(D) = deg D + 1 − g` once `χ(0) = 1 − g`.

Compare the inputs with `exists_bound_ell_eq_degree_of_isAlgClosed_curve` above, which is the
same conclusion: there the closed ledger is a hypothesis, here it is discharged from `hbump`.
That is the whole difference, and it is the reason this statement is the one to quote. -/
theorem exists_bound_ell_eq_degree_of_bump [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
    [IsNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    [LocallyOfFiniteType C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (U₀ U₁ : C.left.Opens)
    (hbump : ∀ (P : C.left.PrimeDivisor) (E : C.left.WeilDivisor),
      chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E + residueDeg k P)
    (D₀ : C.left.WeilDivisor) (hbase : Subsingleton (H1Mod k U₀ U₁ D₀))
    (hpeel : ∀ D' : C.left.WeilDivisor,
      (∀ P : C.left.PrimeDivisor, (show C.left.PrimeDivisor →₀ ℤ from D₀) P ≤
        (show C.left.PrimeDivisor →₀ ℤ from D') P) →
      Peel k U₀ U₁ D₀ D') :
    ∃ b : ℤ, ∀ D : C.left.WeilDivisor, b ≤ Scheme.WeilDivisor.degree D →
      (ell k D : ℤ) = chi k U₀ U₁ 0 + Scheme.WeilDivisor.degree D :=
  exists_bound_ell_eq_degree_of_isAlgClosed_curve C U₀ U₁
    (chi_eq_of_bump k U₀ U₁ hbump) D₀ hbase hpeel

/-- **Uniform global generation on a curve, with every available discharge applied.**

Above a threshold on the geometric degree, `𝒪(D)` is generated by global sections at *every*
prime divisor.  The residue-degree bound `r = 1` is discharged (§3), as is the ledger; what
remains is `hbump`, the base vanishing and the peel.

Note the threshold is stated on `degK`, matching `exists_bound_forall_generatedAt`; on this
curve `degK = degree` (`degK_eq_degree_of_isAlgClosed_curve`), so a caller may translate. -/
theorem exists_bound_forall_generatedAt_of_bump_curve [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
    [IsNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    [LocallyOfFiniteType C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [∀ D : C.left.WeilDivisor, Module.Finite k (sectionSub k ⊤ D)]
    (U₀ U₁ : C.left.Opens)
    (hbump : ∀ (P : C.left.PrimeDivisor) (E : C.left.WeilDivisor),
      chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E + residueDeg k P)
    (D₀ : C.left.WeilDivisor) (hbase : Subsingleton (H1Mod k U₀ U₁ D₀))
    (hpeel : ∀ D' : C.left.WeilDivisor,
      (∀ P : C.left.PrimeDivisor, (show C.left.PrimeDivisor →₀ ℤ from D₀) P ≤
        (show C.left.PrimeDivisor →₀ ℤ from D') P) →
      Peel k U₀ U₁ D₀ D') :
    ∃ b : ℤ, ∀ D : C.left.WeilDivisor, b ≤ degK k D →
      ∀ P : C.left.PrimeDivisor, GeneratedAt k D P :=
  exists_bound_forall_generatedAt_of_isAlgClosed_curve C U₀ U₁
    (chi_eq_of_bump k U₀ U₁ hbump) D₀ hbase hpeel

/-- **Principal divisors have geometric degree zero on a curve, from the bump.**

The sharpest honest form of the open leaf `Scheme.WeilDivisor.principal_degree_zero` reachable
today: `deg (div g) = 0`, unweighted, on curve hypotheses, from `hbump` and nothing else — no
residue input, no ledger hypothesis, no base vanishing, no peel.

It is deliberately **not** substituted into `principal_degree_zero`, whose statement mentions
no hypotheses; doing so would make a hypothesis-free theorem depend silently on `hbump`. -/
theorem degree_principal_eq_zero_of_bump [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
    [IsNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    [LocallyOfFiniteType C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (U₀ U₁ : C.left.Opens)
    (hbump : ∀ (P : C.left.PrimeDivisor) (E : C.left.WeilDivisor),
      chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E + residueDeg k P)
    {g : C.left.functionField} (hg : g ≠ 0) :
    Scheme.WeilDivisor.degree (Scheme.WeilDivisor.principal g hg) = 0 :=
  degree_principal_eq_zero_of_isAlgClosed_curve C U₀ U₁
    (chi_eq_of_bump k U₀ U₁ hbump) hg

end ClusterP

end Adelic
end AlgebraicGeometry
