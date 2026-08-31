/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyH1Locus

/-!
# CHART-U(b) — datum-level openness of the chart-membership (witness) locus
(`informal/w4-datb-worksheet.md` §1.6, `informal/w4-datc-worksheet.md` §3.3)

The affine-level heart of the shared CHART-U(b) brick, stated directly on a pinned
basic-open cocycle datum in the **witness form** the `chartLocus` predicate uses.

For a datum `D` over an affine base `B`, the locus of primes `q` of `B` at which the
fibre class of `D` at `κ(q)` admits an effective witness divisor with vanishing `H¹`
is Zariski-open in `Spec B`.  This is the single sanctioned openness mechanism of the
campaign (`datumRigidEngine_isOpen_vanishing`, Noetherian-free — dat-d §3.5) read
through the two-way datum dictionary of C1
(`BasicOpenCocycleDatum.subsingleton_h1_tensor_iff_exists_witness`,
`informal/w4-datc-worksheet.md` GAP-6): the engine open is the complex-form fibre
condition `Subsingleton (H¹(pair D) ⊗[B] κ(q))`, and the dictionary rewrites it,
pointwise and class-intrinsically, as the effective-witness/h¹-vanishing condition.

Role in the CHART-U(b) chain (the two unlanded links of §5 risk 1):

* **the shifted-datum constructor (link 1):** over the étale carrier `B` the plus
  class collapses to an honest Čech class; twisted by the theta layer and DAT-C's
  GAP-1 inverse datum into the `λθᵐ(Σ-shift)⁻¹` class, then extracted
  (`BasicOpenCocycleDatum.exists_cechPicClass_eq`) to a datum `D`.  The output of
  that link is exactly a `BasicOpenCocycleDatum C B π` — the input of the theorem
  below, whose witness set is then the `chartLocus`-over-`B`.
* **the étale-image openness transport (link 2):** the locus over the test base `A`
  is the image, under the (open, surjective) étale carrier map `Spec B → Spec A`, of
  the open locus this theorem produces — carried to `A` by mathlib's
  `IsOpenMap.isQuotientMap`/`IsQuotientMap.isOpen_preimage` once the fibre-field
  invariance identifies the preimage.

The theorem is class-intrinsic (any datum in the class has the same witness set, by
(V1a)), so a change of extracted representative is free.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-- **CHART-U(b), the datum-level witness-locus openness** (`w4-datc` §3.3 step (3)):
for a pinned basic-open cocycle datum `D` over the affine base `B`, the locus of primes
`q` at which the fibre class of `D` at `κ(q)` has an effective witness divisor with
vanishing `H¹` is open in `Spec B`.

This is `datumRigidEngine_isOpen_vanishing` (the single audited openness engine,
Noetherian-free) read in the class/witness form of the `chartLocus` predicate through
the two-way datum dictionary
`BasicOpenCocycleDatum.subsingleton_h1_tensor_iff_exists_witness` (C1, GAP-6):
pointwise the engine's complex-form condition `Subsingleton (H¹(pair D) ⊗[B] κ(q))`
is exactly the existence of such a witness. -/
theorem BasicOpenCocycleDatum.isOpen_setOf_exists_witness_h1_vanishing
    (D : BasicOpenCocycleDatum C B π) (hπ : π ≫ P1.structureMap k = C.hom) :
    IsOpen {q : PrimeSpectrum B |
      ∃ W : ((C ⊗ overSpec k q.asIdeal.ResidueField).left).CurveDivisor,
        Scheme.CurveDivisor.picClass q.asIdeal.ResidueField W
            = Scheme.CechPic.map (relCurveMap C B q.asIdeal.ResidueField) D.cechPicClass
          ∧ Subsingleton (Sheaf.HModule
              ((C ⊗ overSpec k q.asIdeal.ResidueField).left.divisorSheaf
                q.asIdeal.ResidueField W) 1)} := by
  have hset : {q : PrimeSpectrum B |
      ∃ W : ((C ⊗ overSpec k q.asIdeal.ResidueField).left).CurveDivisor,
        Scheme.CurveDivisor.picClass q.asIdeal.ResidueField W
            = Scheme.CechPic.map (relCurveMap C B q.asIdeal.ResidueField) D.cechPicClass
          ∧ Subsingleton (Sheaf.HModule
              ((C ⊗ overSpec k q.asIdeal.ResidueField).left.divisorSheaf
                q.asIdeal.ResidueField W) 1)}
      = {p : PrimeSpectrum B |
          Subsingleton ((datumPair D).H1 ⊗[B] p.asIdeal.ResidueField)} := by
    refine Set.ext fun q => ?_
    exact (D.subsingleton_h1_tensor_iff_exists_witness q.asIdeal.ResidueField).symm
  rw [hset]
  exact datumRigidEngine_isOpen_vanishing D hπ

/-! ## The openness transport (CHART-U(b) link 2, topological half)

The engine produces the open witness locus over the étale carrier `Spec B` (or, on the
away pieces, over `Spec (Localization.Away f)`).  CHART-U(b)'s transport (ii)
(`w4-datb` §1.6, "the Kleiman tex 2204-2244 step, now one `IsOpenMap` application")
carries it down to the test base `Spec A` along the étale carrier map, which is open
and surjective.  The pure-topology core of that step is below; the remaining
mathematical content of link 2 is the *fibre-field invariance* that identifies the
preimage of the base locus with the carrier locus (`κ(q)/κ(p)` a separable extension;
`isH1VanishingAt_comap_away_iff` is the landed avatar for the away case). -/

/-- **Openness descends along an open continuous surjection**: if `f` is continuous,
open, and surjective and `f ⁻¹' V` is open, then `V` is open — because
`V = f '' (f ⁻¹' V)` (surjectivity) and `f` carries opens to opens.  This is the
topological core of CHART-U(b)'s transport (ii). -/
theorem isOpen_of_isOpen_preimage_of_isOpenMap_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hcont : Continuous f) (hopen : IsOpenMap f) (hsurj : Function.Surjective f)
    {V : Set Y} (hV : IsOpen (f ⁻¹' V)) : IsOpen V :=
  ((hopen.isQuotientMap hcont hsurj).isOpen_preimage).mp hV

/-- **The `Spec`-level openness transport of CHART-U(b)** (transport (ii), topological
half): for a ring map `f : R →+* S` whose induced `Spec S → Spec R` is open and
surjective (e.g. an étale carrier map), a locus of `Spec R` whose preimage in `Spec S`
is open is itself open.  The engine's open witness locus lives on the carrier `Spec S`;
this pushes it to the test base `Spec R`. -/
theorem isOpen_of_isOpen_comap_preimage {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hopen : IsOpenMap (PrimeSpectrum.comap f))
    (hsurj : Function.Surjective (PrimeSpectrum.comap f))
    {V : Set (PrimeSpectrum R)} (hV : IsOpen (PrimeSpectrum.comap f ⁻¹' V)) :
    IsOpen V :=
  isOpen_of_isOpen_preimage_of_isOpenMap_surjective
    (PrimeSpectrum.continuous_comap f) hopen hsurj hV

end AlgebraicGeometry
