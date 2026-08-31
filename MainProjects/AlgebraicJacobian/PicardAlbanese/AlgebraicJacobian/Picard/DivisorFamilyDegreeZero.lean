/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyZarFunctor
import AlgebraicJacobian.Picard.DivisorFamilyBackward

/-!
# THE DEGREE-ZERO DIVISOR FUNCTOR IS INHABITED, UNCONDITIONALLY

`DivFamZar C R π n` (`Picard/DivisorFamilyZar.lean:235`) is the value of the divisor functor
that the whole Pic⁰ representability seam consumes, through
`rep : (divFunctor C π n).RepresentableBy D` in `mixedParamChart`
(`Picard/Pic0ChartAtlasParamFree.lean:64`).  Its own header names the open question:

> it does not produce the representations. `mixedParamChart` takes `rep i` as a hypothesis, one
> per parameter, and the divisor-representability lane supplies `divFunctor C π g` — a single
> parameter.

Every landed route to `rep` targets `n = g` through the chart-typed classifier and is gated on
U2 / the G-4 certificate (`AJCR.w4-rep.datum.dat-d.ddr.divrep.u2`).  **Nobody had asked what
happens at `n = 0`**, and this file answers it: at parameter `0` the entire certificate
apparatus is free.

## What is proved here, and why the certificate collapses

The colength certificate `DivisorAdaptation.IsCertified n` (`Picard/DivisorFamily.lean:426`)
asks for finite projective chart-local colengths, a finite projective glued colength module of
constant fibre rank `n` at every prime, and two flat-cokernel clauses.  On the **trivial**
local-equation system — cover `⊤`, equation `1` everywhere, which is
`Scheme.LocalEquations.unitEquations` up to the `IsIntegral` binder that is not needed here —
every colength module is `Γ(…) ⧸ (1) = 0`.  A zero module is free, hence finite, projective and
flat; and `Module.rankAtStalk` of a subsingleton is `0`, which **is** the `n = 0` clause.  So
all seven fields close with no hypothesis on the curve beyond what `relCurve` needs to exist.

The whole content is that `n = 0` is the degree at which the rank clause asks for *nothing*.
Over a **nontrivial** test ring the same construction fails at `n > 0` on exactly one field,
`rankAtStalk_glued`, and that is the honest boundary.  The nontriviality qualifier is not
decoration: over the zero ring `PrimeSpectrum R` is empty, so the rank clause is vacuous at
*every* `n` and `trivAdapt` is certified in every degree.  An earlier draft stated the boundary
without it and was refuted by that case in a fresh-context audit.

## Main declarations

* `AlgebraicGeometry.DivFamZar.trivEqns` — the trivial system, with no `IsIntegral` binder.
* `AlgebraicGeometry.DivFamZar.trivAdapt` — its one-piece-per-chart adaptation.
* `AlgebraicGeometry.DivFamZar.isCertified_trivAdapt` — **the degree-zero certificate, free**.
* `AlgebraicGeometry.DivFamZar.trivFam` — an unconditional `CertifiedDivisorFamily C R π 0`.
* `AlgebraicGeometry.DivFamZar.trivZar` — hence `DivFamZar C R π 0` is inhabited, and
  `instInhabitedDivFamZarZero` registers it.
* `AlgebraicGeometry.DivFamZar.mapAlgHom_trivZar` — **the trivial class is base-change invariant
  along an arbitrary `k`-algebra map**, with no tower hypotheses at all.
* `AlgebraicGeometry.DivFamZar.trivSection` / `divFunctor_obj_nonempty_zero` — hence the
  degree-zero divisor functor has a point over **every** test object of the slice, not only
  affine ones.

TWO CORRECTIONS TO EARLIER DRAFTS OF THIS LIST, both found by a fresh-context audit of my own
work and both recorded rather than quietly fixed.

*First*, an earlier draft named `divFunctor_obj_nonempty_zero` while no such declaration
existed — the `cited-names-need-check-not-grep` failure, in the summary a reader hits first.
*Second*, and this is the more interesting one: the commit that retracted it replaced the
citation with a **hedge that was itself false**.  It said the general-test section was blocked
because `Over.resAlgHom T h` must agree with `algebraMap` and that is not `rfl`.  That reads the
dependency backwards.  `DivFamZar.mapAlgHom` *defines* the algebra structure it uses as
`φ.toRingHom.toAlgebra` (`Picard/DivisorFamilyZarVehicle.lean`), so the agreement holds **by
construction at every `φ`** — the tower hypotheses I thought I needed can be manufactured
locally with `letI`/`haveI`, and `mapAlgHom_trivZar` below carries none of them.  The section is
landed above.  A hedge standing in for an unattempted check is worse than no note; a hedge that
misreads the consumer's own definition schedules work that is minutes away.

## What this does NOT do

It does not represent `divFunctor C π 0`: a point of every value is not a natural bijection
with a scheme's points.  Representability at `0` additionally needs *uniqueness* — that the
degree-zero value is a subsingleton — which is a separate statement and is not proved here.
`Picard/DivisorFamilyDegreeZeroUnique.lean` takes that up.

Nor does it give the seam an atlas: `mixedParamChart` at `nn i = 0` also needs a chart index
`Z i` of degree `m·d₁ − 0` and the two seam antecedents, none of which this file touches.
What it removes is the standing sentence that `rep` has **no** producer at **any** parameter —
the object side at parameter `0` is now built and axiom-clean.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling; see
`AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace DivFamZar

/-! ## Zero modules are finite, projective and flat

Three one-line consequences of `Module.Free.of_subsingleton`, stated because the certificate
needs them at four different module expressions and `infer_instance` cannot see
`Subsingleton` through the quotient spellings. -/

section ZeroModule

variable (R : Type u) [CommRing R]

theorem finite_of_subsingleton (M : Type u) [AddCommGroup M] [Module R M] [Subsingleton M] :
    Module.Finite R M :=
  haveI := Module.Free.of_subsingleton R M
  Module.Finite.of_finite

theorem projective_of_subsingleton (M : Type u) [AddCommGroup M] [Module R M]
    [Subsingleton M] : Module.Projective R M :=
  haveI := Module.Free.of_subsingleton R M
  Module.Projective.of_free

theorem flat_of_subsingleton (M : Type u) [AddCommGroup M] [Module R M] [Subsingleton M] :
    Module.Flat R M :=
  haveI := Module.Free.of_subsingleton R M
  inferInstance

end ZeroModule

/-! ## The trivial local-equation system and its adaptation -/

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (pi : C.left ⟶ P1 k) [IsAffineHom pi]

/-- **The trivial local-equation system on the relative curve**: the constant equation `1` on
the top cover.

This is `Scheme.LocalEquations.unitEquations` (`Picard/DivisorFamilyBackward.lean:51`)
transcribed *without* its `[IsIntegral X]` binder — that lemma's section carries the binder for
its `presentationDivisor` statements, and `relCurve C R` over a general test ring `R` is not
integral, so the landed name is not applicable at the site this file needs.  The two `Prop`
fields need only that `1` is a unit: `regular` is `map_one` plus `one_mem`, and the overlap
ratio is `1`. -/
noncomputable def trivEqns : (relCurve C R).LocalEquations where
  cover := ⊤
  eqn := fun _ => 1
  regular := fun _ y _ => by rw [map_one]; exact one_mem _
  ratio_isUnit := fun _ _ => ⟨1, by simp⟩

@[simp]
lemma trivEqns_eqn (y : relCurve C R) : (trivEqns C R).eqn y = 1 := rfl

@[simp]
lemma trivEqns_cover : (trivEqns C R).cover = ⊤ := rfl

/-- **The one-piece-per-chart cover datum**: one basic open per pinned chart, cut out by the
unit `1`, with partition coefficient `1`.  The basic open of `1` is the whole chart, so this is
the coarsest legal `FinCoverData` and the partition witnesses are `mul_one`. -/
noncomputable def trivCover : FinCoverData C R pi where
  m₀ := 1
  m₁ := 1
  h₀ := fun _ => 1
  h₁ := fun _ => 1
  a₀ := fun _ => 1
  a₁ := fun _ => 1
  partition₀ := by simp
  partition₁ := by simp

/-- **The trivial adaptation**: equation `1` on each of the two pieces.  The refinement clause
`eqn_rel` holds with unit `1`, because both sides restrict `1` to the same overlap. -/
noncomputable def trivAdapt : DivisorAdaptation C R pi (trivEqns C R) where
  toFinCoverData := trivCover C R pi
  eqn := fun _ => 1
  eqn_rel := fun _ _ => ⟨1, by rw [Units.val_one, one_mul, trivEqns_eqn, map_one, map_one]⟩

@[simp]
lemma trivAdapt_eqn (j : (trivAdapt C R pi).index) : (trivAdapt C R pi).eqn j = 1 := rfl

/-! ## Every colength module of the trivial adaptation vanishes

This is the whole reason the degree-zero certificate is free: the colength modules are
quotients by the ideal generated by the *equation*, and the equation is a unit. -/

instance subsingleton_trivAdapt_colength (j : (trivAdapt C R pi).index) :
    Subsingleton ((trivAdapt C R pi).colength j) := by
  change Subsingleton (_ ⧸ Ideal.span {(trivAdapt C R pi).eqn j})
  rw [trivAdapt_eqn, Ideal.span_singleton_one]
  exact Submodule.Quotient.subsingleton_iff.mpr rfl

/-- The overlap colength modules vanish too.  Here the ideal is the *symmetric* span of the two
restricted equations, so the `span_singleton_one` shortcut does not apply directly: instead the
first generator restricts to `1`, and an ideal containing `1` is `⊤`. -/
instance subsingleton_trivAdapt_ovlColength (i j : (trivAdapt C R pi).index) :
    Subsingleton ((trivAdapt C R pi).ovlColength i j) := by
  change Subsingleton (_ ⧸ (trivAdapt C R pi).ovlIdeal i j)
  refine Submodule.Quotient.subsingleton_iff.mpr (le_antisymm le_top fun x _ => ?_)
  have h : (1 : Γ(relCurve C R, (trivAdapt C R pi).pieces i ⊓ (trivAdapt C R pi).pieces j))
      ∈ (trivAdapt C R pi).ovlIdeal i j := by
    have hm : relResAlgHom C R
        (inf_le_left : (trivAdapt C R pi).pieces i ⊓ (trivAdapt C R pi).pieces j
          ≤ (trivAdapt C R pi).pieces i) ((trivAdapt C R pi).eqn i)
        ∈ (trivAdapt C R pi).ovlIdeal i j :=
      Ideal.subset_span (Set.mem_insert _ _)
    rwa [trivAdapt_eqn, relResAlgHom_apply, map_one] at hm
  simpa using Ideal.mul_mem_left _ x h

instance subsingleton_trivAdapt_chartProd : Subsingleton ((trivAdapt C R pi).chartProd) :=
  ⟨fun _ _ => funext fun _ => Subsingleton.elim _ _⟩

instance subsingleton_trivAdapt_ovlProd : Subsingleton ((trivAdapt C R pi).ovlProd) :=
  ⟨fun _ _ => funext fun _ => Subsingleton.elim _ _⟩

instance subsingleton_trivAdapt_glued : Subsingleton ((trivAdapt C R pi).Glued) :=
  ⟨fun _ _ => Subtype.ext (Subsingleton.elim _ _)⟩

/-! ## The degree-zero certificate -/

/-- **THE DEGREE-ZERO COLENGTH CERTIFICATE IS FREE.**

All seven fields of `DivisorAdaptation.IsCertified 0` hold for the trivial adaptation with **no
hypothesis** beyond those needed for `relCurve C R` to exist: the four finiteness/projectivity
clauses and the two flat-cokernel clauses are the zero module being free, and the rank clause
`rankAtStalk_glued` asks for rank `0`, which `Module.rankAtStalk_eq_zero_of_subsingleton`
supplies.

**The boundary is that last field and nothing else.**  Over a nontrivial test ring `trivAdapt`
still satisfies the other six clauses at `n > 0` and fails this one, so `0` is not an arbitrary
choice of small parameter — it is the unique degree at which the rank clause is satisfiable
here.  Over the zero ring there are no primes and every degree is certified, which is why the
nontriviality qualifier belongs in the statement of the boundary rather than in a footnote. -/
theorem isCertified_trivAdapt : (trivAdapt C R pi).IsCertified 0 where
  finite_colength := fun _ => finite_of_subsingleton R _
  projective_colength := fun _ => projective_of_subsingleton R _
  finite_glued := finite_of_subsingleton R _
  projective_glued := projective_of_subsingleton R _
  rankAtStalk_glued := fun p => by
    have h : Module.rankAtStalk (R := R) (trivAdapt C R pi).Glued = 0 :=
      Module.rankAtStalk_eq_zero_of_subsingleton
    rw [h]
    rfl
  flat_coker_incl := flat_of_subsingleton R _
  flat_coker_diff := flat_of_subsingleton R _

/-- **An unconditional degree-zero certified divisor family.**  The first inhabitant of
`CertifiedDivisorFamily C R π n` at any parameter that is not gated on the DD-R certificate
tower. -/
noncomputable def trivFam : CertifiedDivisorFamily C R pi 0 where
  eqns := trivEqns C R
  adaptation := trivAdapt C R pi
  certified := isCertified_trivAdapt C R pi

/-- **`DivFamZar C R π 0` is inhabited**, via `CertifiedDivisorFamily.isLocallyCertified`
(a global certificate is a local one, at the trivial cover `g = ![1]`). -/
noncomputable def trivZar : DivFamZar C R pi 0 :=
  DivFamZar.mk (trivFam C R pi).eqns (trivFam C R pi).isLocallyCertified

instance instNonemptyDivFamZarZero : Nonempty (DivFamZar C R pi 0) :=
  ⟨trivZar C R pi⟩

/-! ## The trivial class is base-change invariant, hence a GENERAL-TEST section

`divFamZar C π n T` (`Picard/DivisorFamilyZarVehicle.lean:187`) is a compatible family of
`DivFamZar` classes over the affine opens of `T.left`.  Taking the trivial class at every
affine open gives such a family precisely because base change sends the trivial class to the
trivial class — and it does, for the cheapest possible reason: the pulled system's equation is
the *restriction of* `1`, and restriction is a ring hom. -/

section BaseChange

variable {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A']

/-- **Base change preserves the trivial class**, in the `mapAlg` spelling.  Both systems have
cover `⊤`, and the pulled equation is a restriction of `1`, so `DivEq` holds with unit `1`. -/
theorem mapAlg_trivZar [Algebra A A'] [IsScalarTower k A A'] :
    DivFamZar.mapAlg (C := C) (π := pi) (R := A) A' 0 (trivZar C A pi) = trivZar C A' pi := by
  refine DivFamZar.mk_eq_mk_iff.mpr ?_
  refine ⟨(trivEqns C A').cover, fun _ => le_top, le_rfl, fun _ => ⟨1, ?_⟩⟩
  rw [Units.val_one, one_mul, Scheme.LocalEquations.pullback_eqn]
  change (CommRingCat.Hom.hom _) ((CommRingCat.Hom.hom _) (1 : _))
      = (CommRingCat.Hom.hom _) (1 : _)
  rw [map_one, map_one, map_one]

/-- **Base change preserves the trivial class along an ARBITRARY `k`-algebra map** — no
`[Algebra A A']`, no `[IsScalarTower]`, no agreement hypothesis.

This is the form the vehicle's compatibility clause consumes, and the reason it needs nothing:
`DivFamZar.mapAlgHom` *defines* the algebra structure it uses as `phi.toRingHom.toAlgebra`, so
the tower data can be manufactured locally from `phi` itself and the agreement with
`algebraMap` is `rfl` by construction.  An earlier version of this file carried all three
hypotheses and hedged that the general-test section was blocked on the agreement; see the
corrections in the module docstring. -/
theorem mapAlgHom_trivZar (phi : A →ₐ[k] A') :
    DivFamZar.mapAlgHom (C := C) (π := pi) (n := 0) phi (trivZar C A pi) = trivZar C A' pi := by
  letI : Algebra A A' := phi.toRingHom.toAlgebra
  haveI : IsScalarTower k A A' := .of_algebraMap_eq fun a => (phi.commutes a).symm
  exact mapAlg_trivZar C pi

end BaseChange

/-! ## The general-test section

`divFamZar C π n T` (`Picard/DivisorFamilyZarVehicle.lean`) is a compatible family of `DivFamZar`
classes over the affine opens of `T.left`.  Base-change invariance in the hypothesis-free form
above makes the constant-trivial family compatible in one line, so the degree-zero divisor
functor has a point over **every** test object of the slice. -/

/-- **The trivial section of the degree-zero divisor functor at an arbitrary test.** -/
noncomputable def trivSection (T : Over (Spec (.of k))) : divFamZar C pi 0 T :=
  ⟨fun _ => trivZar C _ pi, fun _ _ h => mapAlgHom_trivZar C pi (Over.resAlgHom T h)⟩

/-- **The degree-zero divisor functor has a point over every test object.**  Worth stating
separately from `instNonemptyDivFamZarZero`: that one is affine-local, this is the functor value
on the whole slice. -/
theorem divFunctor_obj_nonempty_zero (T : (Over (Spec (.of k)))ᵒᵖ) :
    Nonempty ((divFunctor C pi 0).obj T) :=
  ⟨trivSection C pi T.unop⟩

end DivFamZar

end AlgebraicGeometry

