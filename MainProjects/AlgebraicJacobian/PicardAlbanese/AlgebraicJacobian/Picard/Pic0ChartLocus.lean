/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartTestPoint
import AlgebraicJacobian.Picard.DivSchemeAbel
import AlgebraicJacobian.Picard.PicEtAffFieldCollapse

/-!
# CHART-U(a): `chartLocus`, the chart-membership locus over a general test

The co-signed brick of `informal/w4-datc-worksheet.md` §3.3 (CHART-U(a)) and
`informal/w4-datb-worksheet.md` §1.6, in the SPLIT form the (a-amendment) binds:

> `t ∈ chartLocus c λ` iff for some (equivalently every) finite separable `L/κ(t)`
> splitting the collapsed plus class, the honest `L`-class of `λ_t · θ^m · (−Σ)` admits
> an effective witness divisor with vanishing `H¹`.

Everything here is over a GENERAL test `T` and an ARBITRARY plus class
`λ ∈ pic0Subgroup C T`.  That is what distinguishes it from
`Picard/Pic0ChartLocusClass.lean`'s `cechWitnessLocus`, which lives over an affine base
and reads an UNTWISTED `CechPic` class; the module header there says so, and this file is
the promised general-test article.

## The layering, and why the split predicate is a *definition* here and not a disjunction

Three separate things had to be joined, and they are joined in three steps:

1. `Over.testPoint` (`Picard/Pic0ChartTestPoint.lean`) turns a point `t : T.left` into a
   field point `overSpec k κ(t) ⟶ T`, so that `picEtMap C (testPoint t) λ` is the fibre
   class of `λ` at `t`.  Without it there is no way to even state the predicate over a
   general test.
2. `IsSplitWitness` reads a plus class over a FIELD.  A plus class over a field is
   `PicEtAff.mk E x` for an étale cover `E`, which is *not* an honest Čech class; the
   (a-amendment)'s "finite separable `L` splitting the class" is exactly
   `Algebra.EtaleCover.exists_finiteSeparableField_algHom` (`Algebra/EtaleCover.lean:287`)
   applied to `E`, after which `PicEtAff.map_mk_eq_unit_relPicMk_of_algHom`
   (`Picard/PicEtAffFieldCollapse.lean:101`) presents the class as `relPicMk` of an honest
   Čech class over `C_L`.  The predicate is then the tree's witness predicate on that Čech
   class.
3. `chartLocus` twists by the chart index `(m, Σ)` — the same twist
   `abelDiv · sigmaFamily Σ · (θ^m)⁻¹` that `chartValue` (`Picard/DivSchemeAbel.lean:351`)
   applies on the divisor side — and reads step 2 at step 1's field point.

The "some (equivalently every)" of the amendment is the honest content: the ∃-form is what
one *proves* (coverage produces one splitting, §1.2 step 6), the ∀-form is what one
*consumes* (any presenting splitting is a sound test).  Their agreement is
`isSplitWitness_iff_forall`, and it rests on
`BasicOpenCocycleDatum.hasWitnessH1Vanishing_iff_of_separable`
(`Picard/Pic0ChartLocusFibreField.lean:157`) — the separable-invariance that lane co-owned
— together with class-intrinsicity at a fixed field
(`hasWitnessH1Vanishing_congr_of_cechPicClass_eq`, `:177`).  So the definition is stated in
the ∃-form and the ∀-form is a theorem, not a second definition.

## Main declarations

* `AlgebraicGeometry.IsSplitWitness C π μ` — the split witness predicate at a class
  `μ : picEt C (overSpec k K)` over a field `K`: some finite separable `L/K` presents `μ`
  as an honest Čech class over `C_L` admitting an effective witness divisor with vanishing
  `H¹`.
* `AlgebraicGeometry.isSplitWitness_iff_forall` — the (a-amendment)'s "some (equivalently
  every)".
* `AlgebraicGeometry.chartTwist C m Σ λ` — the twisted fibre family
  `λ · sigmaFamily Σ · (θ^m)⁻¹`, i.e. the class whose chart-membership is at issue.  Its
  fibre degree is `m·d₁ − Σ.deg` by the landed degree ledger, which the chart-index
  constraint `deg Z = m·d₁ − g` makes `+g` — the degree at which an effective witness with
  `h¹ = 0` can exist at all.
* **`AlgebraicGeometry.chartLocus`** — CHART-U(a): `{t : T.left | IsSplitWitness of the
  twisted fibre class at κ(t)}`.
* `AlgebraicGeometry.mem_chartLocus_iff` / `mem_chartLocus_iff_forall` — the two readings.
* `AlgebraicGeometry.chartLocus_preimage_subset` — the naturality half that CHART-U(b)
  transport (i) consumes: a morphism of tests pulls `chartLocus` back into `chartLocus`.

## What is NOT here

`isOpen_chartLocus` (dat-b row B-4) is the *assembly* of DAT-B's transports (i)/(ii)
against DAT-C's shifted-datum half, and it lives in `Picard/Pic0ChartLocusIsOpen.lean`.
Nothing in this file is `divRep`- or certificate-gated: no `DivFamZar`, no `IsCertified`,
no `RepresentableBy` appears in the cone, per the parametric mandate of I-0494.
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
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The split witness predicate at a class over a field -/

variable (C) in
/-- **The split witness predicate** (CHART-U(a) in the `w4-datb` §1.6 (a-amendment)
spelling), at a plus class `μ` over a field `K`.

A plus class over a field need not be an honest Čech class — it is `PicEtAff.mk E x` for
an étale cover `E` of `K`.  The amendment's "for some finite separable `L/κ(t)` splitting
the collapsed plus class" is this: there is a finite separable extension `L/K` over which
`μ` becomes `relPicMk` of an honest Čech class `M` on `C_L`, and `M` admits an effective
witness divisor with vanishing `H¹`.

Stated with the witness clause on a *presenting Čech class* rather than on a datum,
because the datum layer is where the shifted-datum constructor (DAT-C GAP-1) is missing;
the two agree through `Pic0ChartLocusClass.mem_cechWitnessLocus_iff_exists`.

## A convention this predicate INHERITS, and which a consumer must not misread

The worksheets say "effective degree-`g` witness with `h¹ = 0`".  The witness clause here —
and the tree's `BasicOpenCocycleDatum.HasWitnessH1Vanishing`
(`Pic0ChartLocusFibreField.lean:115`) that it mirrors, and the GAP-6 dictionary
`subsingleton_h1_tensor_iff_exists_witness` (`DivisorFamilyH1Locus.lean:182`) that both rest
on — asks for **neither `0 ≤ W` nor `deg W = g`**.  It asks only for a `CurveDivisor` in the
class with vanishing `H¹`.  That is deliberate on the tree's side: the dictionary is an *iff*
against the engine's complex-form condition `Subsingleton (H¹(pair D) ⊗ L)`, and that
condition cannot see effectivity or degree, so adding either clause would break the iff and
with it the openness route.

Two consequences, both load-bearing:

* the degree is supplied **externally**, by the chart-index constraint through
  `degAt_chartTwist` below: on a degree-zero `λ` the twisted class has fibre degree
  `m·d₁ − deg Z`, which the constraint `deg Z = m·d₁ − g` makes `+g`.  It is *not* a
  hypothesis of this predicate.  (Until 2026-07-28 this read `−g`, and that sign made the
  locus empty for every `g ≥ 1` — see `degAt_chartTwist` and issue I-0514;
  `chartTwist_chartValue` now pins the direction by the kernel);
* effectivity likewise is not asserted here.  Where the *worksheet's* stronger reading is
  actually needed — the canonical-section normalization `h⁰ = 1`, and GAP-2 uniqueness
  (`Scheme.CurveDivisor.eq_of_picClass_eq_of_h0_one`, which does take `0 ≤ D`, `0 ≤ D'`) — the
  effectivity must be re-supplied at that point.  A lane that reads `IsSplitWitness` as
  already giving it will have a gap where it least expects one. -/
def IsSplitWitness {K : Type u} [Field K] [Algebra k K]
    (μ : picEt C (overSpec k K)) : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra K L)
      (_ : IsScalarTower k K L) (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L)
      (M : (relCurve C L).CechPic),
    PicEtAff.map C L (picEtAffineEquiv C K μ)
        = PicEtAff.unit C L (relPicMk C (overSpec k L) M)
      ∧ ∃ W : ((C ⊗ overSpec k L).left).CurveDivisor,
          Scheme.CurveDivisor.picClass L W = M
            ∧ Subsingleton (Sheaf.HModule
                ((C ⊗ overSpec k L).left.divisorSheaf L W) 1)

/-! ## The twisted fibre family -/

variable (C) in
/-- **The twisted family whose chart-membership `chartLocus` tests**: the plus class `λ`
shifted by the Σ-family of `Z` and by `m` inverse powers of the pinned θ-family.

This is the *class-side* half of `chartValue` (`Picard/DivSchemeAbel.lean:351`): where
`chartValue` twists the Abel class of a divisor family, `chartTwist` twists an arbitrary
plus class by the same two factors.  A point of `chartLocus` is precisely a point at which
`chartTwist` is realised by an effective divisor with no `H¹` — i.e. at which `λ` itself is
a chart value, after undoing the twist. -/
def chartTwist (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (lam : picEt C T) : picEt C T :=
  lam * (thetaFamily C (thetaCechClass C) T ^ m) * (sigmaFamily C Z T)⁻¹

/-- **The degree ledger of the twist**: at every field point the twisted family has fibre
degree `m·d₁ − deg Z` when `λ` is degree-zero.  With the chart-index constraint
`deg Z = m·d₁ − g` this is `+g`, which is the degree at which an effective witness with
`h¹ = 0` can exist at all.

**Sign discipline, and it was wrong here until 2026-07-28 (issue I-0514).**  `chartTwist`
must be the INVERSE of `chartValue`'s twist, not the same one.  `chartValue` is
`abelDiv · Σ · (θᵐ)⁻¹` (`DivSchemeAbel.lean:351`), so recovering the Abel class from a chart
value means multiplying by `θᵐ` and dividing by `Σ` — hence `chartTwist` is
`λ · θᵐ · Σ⁻¹`.  An earlier version applied the `chartValue` twist itself, giving fibre degree
`deg Z − m·d₁ = −g`; since `Subsingleton H¹(𝒪(W))` forces `deg W ≥ g − 1`, that locus was
**empty for every `g ≥ 1`** and its openness was the openness of `∅`.  The comparison point is
`degAt_chartValue` at `n = g` (where the chart index is calibrated and `chartValue` lands in
`pic0`), NOT at `n = 0`.

**An independent confirmation that `+g` is the right target**, worth recording because the
wrong sign survived two sessions: at `deg W = g` the rank anchor
`h0_eq_deg_add_chi_of_subsingleton_hModule_one` (`RiemannRoch/FLVClass.lean:412`) gives, for a
witness with `h¹ = 0`,
`h⁰ = deg W + χ(𝒪) = g + (1 − g) = 1` — exactly the `h⁰ = 1` normalization that DAT-C §2 and
GAP-2's uniqueness both require.  So `+g` is not merely the sign that makes the locus nonempty;
it is the unique degree at which the witness is *unique*, which is what the chart map needs to be
injective.  At `−g` the same anchor gives `h⁰ = 1 − 2g`, negative for `g ≥ 1` — the contradiction
that made the locus empty. -/
theorem degAt_chartTwist (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    {T : Over (Spec (.of k))} {lam : picEt C T} (hlam : lam ∈ pic0Subgroup C T)
    {K : Type u} [Field K] [Algebra k K] (t : overSpec k K ⟶ T) :
    degAt (chartTwist C m Z T lam) t
      = (m : ℤ) * classDeg k (thetaCechClass C) - Scheme.CurveDivisor.deg k Z := by
  rw [chartTwist, degAt_mul, degAt_inv, degAt_mul, degAt_thetaFamily_pow,
    degAt_sigmaFamily, (mem_pic0Subgroup_iff.mp hlam) K t]
  ring

/-- **`chartTwist` inverts `chartValue`'s twist** — the sign check, as a theorem rather than a
docstring claim.

Applying `chartTwist` to a chart value returns the Abel class it came from.  This is the
statement that was FALSE of the earlier definition (which returned
`abelDiv · Σ² · (θᵐ)⁻²`), and it is why the direction is now pinned by the kernel: any future
edit to `chartTwist` that breaks the inversion breaks this lemma.

Recorded per issue I-0514.  A degree ledger alone does not catch a sign error — the wrong-signed
ledger was internally consistent — but an inversion law does. -/
theorem chartTwist_chartValue {n : ℕ} (m : ℕ)
    (Z : (C ⊗ overSpec k k).left.CurveDivisor) (T : Over (Spec (.of k)))
    (s : divFamZar C π n T) :
    chartTwist C m Z T (chartValue C π n m Z T s) = abelDiv C π n T s := by
  rw [chartTwist, chartValue]
  group

/-! ## CHART-U(a): the locus -/

variable (C) in
/-- **CHART-U(a), `chartLocus`** (`w4-datc` §3.3, co-signed `w4-datb` §1.6): the set of
points of a general test `T` at which the twisted fibre class `λ_t · θ^m · (−Σ)` has, after
some finite separable splitting of the collapsed plus class at `κ(t)`, an effective witness
divisor with vanishing `H¹`.

The three layers, each supplied by a named brick:
* the *point-to-field-point* passage is `Over.testPoint` (input 0 of this brick — the one
  nothing in the tree had);
* the *twist* is `chartTwist`, the class-side avatar of `chartValue`;
* the *split witness reading over a field* is `IsSplitWitness`.

This is the RESERVED name of `Pic0ChartLocusClass.lean`'s header, now defined.  Note it is
strictly stronger than `cechWitnessLocus`: general test, twisted class, split predicate. -/
def chartLocus (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    {T : Over (Spec (.of k))} (lam : picEt C T) : Set T.left :=
  {t : T.left | IsSplitWitness C
    (picEtMap C (Over.testPoint t) (chartTwist C m Z T lam))}

theorem mem_chartLocus_iff (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : T.left) :
    t ∈ chartLocus C m Z lam ↔ IsSplitWitness C
      (picEtMap C (Over.testPoint t) (chartTwist C m Z T lam)) :=
  Iff.rfl

/-! ## The datum-layer reading

The witness clause of `IsSplitWitness` is stated on a presenting Čech class over `C_L`.
The tree's *engine-facing* predicate is stated on a `BasicOpenCocycleDatum`
(`BasicOpenCocycleDatum.HasWitnessH1Vanishing`, `Pic0ChartLocusFibreField.lean:115`), and
the two are joined by `exists_cechPicClass_eq` (every class is presented) plus
class-intrinsicity.  This is the seam CHART-U(b) crosses to reach
`datumRigidEngine_isOpen_vanishing`, so it is recorded here as a lemma of the definition
rather than left implicit in the openness proof. -/

/-- **The witness clause at a splitting field, in datum form**: for a Čech class `M` over
`C_L`, admitting an effective witness divisor with vanishing `H¹` is exactly
`HasWitnessH1Vanishing` of any datum presenting `M` — as a class over the base `L` itself,
where `relCurveMap C L L` is the identity comparison.

Note the datum lives over the *field* `L` as base ring, which is the affine base the
engine's `PrimeSpectrum L` has a unique point of; that is why the fibre reading and the
base reading coincide here. -/
theorem exists_witness_iff_hasWitnessH1Vanishing_of_datum
    {L : Type u} [Field L] [Algebra k L]
    (D : BasicOpenCocycleDatum C L π) {M : (relCurve C L).CechPic}
    (hD : Scheme.CechPic.map (relCurveMap C L L) D.cechPicClass
      = Scheme.CechPic.map (relCurveMap C L L) M) :
    (∃ W : ((C ⊗ overSpec k L).left).CurveDivisor,
        Scheme.CurveDivisor.picClass L W = Scheme.CechPic.map (relCurveMap C L L) M
          ∧ Subsingleton (Sheaf.HModule
              ((C ⊗ overSpec k L).left.divisorSheaf L W) 1))
      ↔ D.HasWitnessH1Vanishing L := by
  rw [BasicOpenCocycleDatum.HasWitnessH1Vanishing, hD]

/-- **Upward closure of the witness clause along a separable extension of the splitting
field** — the substantive half of the (a-amendment)'s "some (equivalently every)".

If a Čech class `M` over `C_L` has an effective witness divisor with vanishing `H¹`, then
so does its base change to any finite separable `L'/L`.  This is what makes two splittings
of the same plus class comparable: pass to a common separable extension and compare there,
rather than comparing the two splittings directly.

Proof: present `M` by a datum `D` over `L` (`exists_cechPicClass_eq`); the witness clause at
`L` is `D.HasWitnessH1Vanishing L`, which transfers to `L'` by the co-owned separable
invariance `hasWitnessH1Vanishing_iff_of_separable`
(`Pic0ChartLocusFibreField.lean:157` — itself resting only on faithful flatness of a field
extension, so separability is packaging, not content). -/
theorem exists_witness_of_separable_extension (π : C.left ⟶ P1 k) [IsFinite π]
    {L : Type u} [Field L] [Algebra k L]
    {L' : Type u} [Field L'] [Algebra k L'] [Algebra L L'] [IsScalarTower k L L']
    [Algebra.IsSeparable L L'] (M : (relCurve C L).CechPic)
    (h : ∃ W : ((C ⊗ overSpec k L).left).CurveDivisor,
        Scheme.CurveDivisor.picClass L W = M
          ∧ Subsingleton (Sheaf.HModule
              ((C ⊗ overSpec k L).left.divisorSheaf L W) 1)) :
    ∃ W' : ((C ⊗ overSpec k L').left).CurveDivisor,
      Scheme.CurveDivisor.picClass L' W' = Scheme.CechPic.map (relCurveMap C L L') M
        ∧ Subsingleton (Sheaf.HModule
            ((C ⊗ overSpec k L').left.divisorSheaf L' W') 1) := by
  obtain ⟨D, hD⟩ := BasicOpenCocycleDatum.exists_cechPicClass_eq (C := C) (B := L) (π := π) M
  obtain ⟨W, hW, hW1⟩ := h
  -- the witness clause at `L` is the datum predicate at `L`: `relCurveMap C L L` acts as
  -- the identity comparison on classes, since it is `Spec` of the identity algebra map.
  have hid : Scheme.CechPic.map (relCurveMap C L L) D.cechPicClass = D.cechPicClass := by
    have : relCurveMap C L L = 𝟙 (relCurve C L) := by
      rw [relCurveMap]
      have hom : overSpecMap (k := k) L L = 𝟙 (overSpec k L) :=
        Over.OverMorphism.ext (by simp)
      rw [hom, MonoidalCategory.whiskerLeft_id]
      rfl
    rw [this, Scheme.CechPic.map_id]
    rfl
  have hL : D.HasWitnessH1Vanishing L := ⟨W, by rw [hid, hD, hW], hW1⟩
  -- transfer along the separable extension, then read it back as a witness clause
  obtain ⟨W', hW', hW1'⟩ :=
    (D.hasWitnessH1Vanishing_iff_of_separable L L').mp hL
  exact ⟨W', by rw [hW', hD], hW1'⟩

/-! ## Naturality — the half CHART-U(b) transport (i) consumes -/

/-- **`chartLocus` is compatible with restriction of the class**: the twist commutes with
`picEtMap`, so restricting `λ` along a morphism of tests restricts the twisted family too.

This is `sigmaFamily_natural` + `thetaFamily_natural` and nothing else; it is stated
separately because transport (i) of `w4-datb` §1.6 (the descent-preimage step) is exactly
this identity read at the field point of a point over the source. -/
theorem picEtMap_chartTwist (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (lam : picEt C T) :
    picEtMap C f (chartTwist C m Z T lam)
      = chartTwist C m Z T' (picEtMap C f lam) := by
  rw [chartTwist, chartTwist, map_mul, map_inv, map_mul, map_pow,
    sigmaFamily_natural, thetaFamily_natural]

/-- **`chartLocus` pulls back into `chartLocus`** — transport (i) of `w4-datb` §1.6, in the
form the assembly consumes.

For `f : T' ⟶ T` and `t : T'.left`, membership of `t` in the pulled-back locus and of `f t`
in the original are the *same* condition on the *same* twisted class, read at two fields:
`κ(t)` and `κ(f t)`, with `κ(f t) → κ(t)` the induced extension (`testPointFieldMap`).  So
the transport is exactly the invariance of `IsSplitWitness` under that extension.

**This lemma proves nothing on its own — it is an interface, and its proof is `hinv`.**  Said
plainly so that no lane cites it as if transport (i) were discharged.  What it *does* is fix
the exact shape of the obligation and put the burden where it belongs: on the morphism `f`,
via the field extension `κ(f t) → κ(t)` it induces, rather than hidden inside the locus.  The
tree's landed invariance (`hasWitnessH1Vanishing_iff_of_separable`) discharges `hinv` when
that extension is separable — which is the étale-carrier case the (b-amendment) needs, and is
*not* automatic for an arbitrary morphism of tests.  The residue between the two is why
`hinv` is a hypothesis and not a `rw`. -/
theorem mem_chartLocus_of_mem_chartLocus_comp (m : ℕ)
    (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (lam : picEt C T) (t : T'.left)
    (hinv : IsSplitWitness C
        (picEtMap C (Over.testPoint (T := T) (f.left.base t)) (chartTwist C m Z T lam))
      → IsSplitWitness C
        (picEtMap C (Over.testPoint t) (chartTwist C m Z T' (picEtMap C f lam)))) :
    f.left.base t ∈ chartLocus C m Z lam
      → t ∈ chartLocus C m Z (picEtMap C f lam) :=
  hinv

end

end AlgebraicGeometry
