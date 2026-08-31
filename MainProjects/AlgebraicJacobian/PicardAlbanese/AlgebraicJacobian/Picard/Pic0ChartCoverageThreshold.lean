/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartCoverageIndexSlack
import AlgebraicJacobian.Picard.Pic0ChartIndexAdmissible
import AlgebraicJacobian.Picard.DivisorDatumRankOne
import AlgebraicJacobian.RiemannRoch.WindowFieldTransport

/-!
# B-5 step 3: the vanishing threshold at the splitting field is UNIFORM, and it is π-free

## Current endpoint (2026-07-30)

The earlier analysis below correctly proves that a legal index calibrated at a threshold `b`
has chart parameter `n = b`, but it silently specialised `b` to the *smallest named bound*
`B = M·δ + g`.  Vanishing is monotone: any `n ≥ B` is equally valid.  The declarations
`admissibleCoverageParameter` through `exists_uniform_admissibleCoverageChart_eq_univ` choose
`n = B·d₁`, prove it is both above `B` and a divisor degree, produce one legal chart index, and
show that its chart locus is `Set.univ` for every `pic⁰` class.  Thus the former residue
`IsDivisorDegree C g` is not an obligation of coverage; it belongs only to the fixed-`B` branch
retained later in this file and in `Pic0ChartIndexLedgerFeed`.

`Picard/Pic0ChartCoverageIndexSlack.lean` settles that at a chart index legal at parameter
`n` the coverage hypothesis `hb` of `mem_chartLocus_of_vanishing_bound` forces `b = n`, and
that `b = g` is false in general (`hb_forces_h0_eq_one`).  Its item 3 then names the residue:
*reconcile the chart parameter with the threshold*.  Both that file and
`Picard/Pic0ChartCoverageNoDrop.lean`'s retraction treat the threshold `b` — DAT-0a's bound
**at the splitting field `L`** — as a per-`L` quantity that has to be obtained before the
reconciliation can even be stated.

**That is where the pricing is wrong, and this file measures why.**  Two separate points:

* **RETRACTED, 2026-07-30, by a fresh-context audit and reproduced by the author (inbox
  `I-1349`/`I-1350`).**  This bullet read: *"DAT-0a itself is not instantiable at `L` ... there
  is no `relCurve C L ⟶ P1 L` anywhere in this tree, so a lane trying to instantiate DAT-0a at
  a splitting field is trying to build a morphism the project does not have."*  **That is
  false.**  `exists_isFinite_isDominant_toP1` (`Curve/MapToP1.lean:126`) *produces* such a
  morphism for any bundle satisfying the curve hypotheses, and
  `Curve/BaseChangeInstances.lean` supplies those for `baseChangeBundle C L`
  (`instSmoothOfRelativeDimensionSndLeft`, `instIsProperSndLeft`,
  `instGeometricallyIrreducibleSndLeft`).  So DAT-0a *is* instantiable at a splitting field,
  in three `haveI`s.  The error was grepping for the arrow as a *term* when the answer was an
  `exists_`-producer quantified over curves — a producer census, not a term census, is what
  settles "no such morphism exists".
* **The threshold does not need DAT-0a.**  `subsingleton_hModule_one_of_witness`
  (`RiemannRoch/WindowFieldTransport.lean:87`) is the **π-free peeling**: a *single* witness
  divisor with vanishing `H¹` gives vanishing for every divisor of degree
  `≥ deg W₀ + 1 − χ`.  And `windowN C L hπ g` (`:307`) is such a witness on `relCurve C L`
  for every field extension `L/k`, with `subsingleton_h1_windowN` and
  `deg_windowN = M·δ`.

## THE HEADLINE IS A RE-DERIVATION — read this before citing `subsingleton_h1_of_ledger_bound`

**Also from the 2026-07-30 audit (`I-1349`), and it is the more important correction.**
`subsingleton_h1_of_windowA_le_deg` (`Picard/DivSchemeSeedUnivFibre.lean:259`, landed
2026-07-19) is *already* the uniform π-free per-field-extension threshold: same
`subsingleton_hModule_one_of_witness` peel, same transported-window witness, bound
`windowA_choice π hπ · δ + g`.  And that bound is **smaller** than this file's — via
`Nat.find_le (windowBound_le_M_mul π hπ g)` one gets `windowA_choice ≤ windowM_choice`, hence
`a·δ ≤ M·δ`.  So `subsingleton_h1_of_ledger_bound` is a strictly **weaker** corollary of a
landed lemma, not a new fact, and a lane wanting the threshold should cite the `windowA` form.

What survives as genuinely new is the *coverage-side composition* — `mem_chartLocus_of_ledger_bound`
onwards, which nothing previously connected to the chart layer — and even that goes through at
the smaller landed parameter with the same script modulo the constant.  The repricing of the
two coverage sites also survives, since neither of them cited *any* threshold at `L`.

**Why the duplicate escaped me**, recorded because it is the workspace's most expensive
recurring failure: I searched for occurrences of `windowN` and of
`subsingleton_hModule_one_of_witness` in the chart layer, found zero, and read that as
novelty.  But `windowA` also has zero occurrences there — and `windowA` is the name carrying
the equivalent fact.  A name-scoped novelty check cannot see a same-content lemma under a
different name; the check that would have caught it is a search on the *statement*
(`leansearch`/`loogle` on "uniform H¹ vanishing threshold over a field extension"), which I
did not run against this shape.

## The consequence, and it is the point of the file

The bound that comes out is `windowM_choice π hπ g * windowδ π + g`, in which **`L` does not
occur**: `windowM_choice` and `windowδ` are ledger constants of the *base* field `k` (see
I-0204 — the per-field ledger constants do not transport, which is exactly why the window
lane transports window *facts* instead, and why the transported witness carries a `k`-level
degree).  So the threshold is **uniform across all splitting fields**, and the "which
threshold at which fibre" half of the reconciliation is not a residue at all.

What that buys, precisely: `index_of_threshold`
(`Picard/Pic0ChartCoverageIndexSlack.lean:147`) already realises *any* `b ≥ 0` as the ledger
value of a legal chart index at parameter `b.toNat`.  What it could not be composed with was a
`b` known to exist at the splitting field.  Now it can, at one `b` for all fibres.

## What this does NOT do, stated plainly

* **It closes no antecedent of `pic0RepresentableByOfCharts`.**  Coverage still owes the
  *existence of the chart point*, i.e. the pointwise datum of
  `chartsCoverLocally_of_pointwise`; this file supplies one hypothesis of one theorem on the
  route to the locus-membership half.
* **`hb_forces_h0_eq_one` stands.**  Taking the threshold to be `g` is false in general.  The
  earlier conclusion that the chart parameter therefore has to be the minimal bound `M·δ + g`
  is superseded: it may be any larger admissible parameter.  `admissibleCoverageParameter`
  supplies one unconditionally; representability at that larger parameter remains the join with
  the divRep lane.
* **It is not new geometry, and the threshold is not even new Lean** — see the
  re-derivation section above.  `windowN` and `subsingleton_hModule_one_of_witness` did have
  zero occurrences in any `Pic0Chart*` file before this one, but that measured the wrong thing:
  `windowA` also has zero occurrences there, and `windowA` is the name under which the
  equivalent threshold was already landed.

  If you re-check the zero-occurrence claim, note it is about the state *before* this file:
  the corrections it prompted at `Pic0ChartCoverageIndexSlack.lean` and
  `Pic0ChartCoverageNoDrop.lean` now name both declarations, so `grep windowN Pic0Chart*`
  returns hits today.  Verify at `042e9e1154`, where both files were still unedited.  (This is
  the I-0717 shape — an absence claim breaking the grep that would check it — here caused by
  the fix rather than by the claim.)

## Main declarations

* `AlgebraicGeometry.subsingleton_h1_of_ledger_bound` — **the uniform threshold at an
  arbitrary field extension**: every divisor on `relCurve C L` of degree `≥ M·δ + g` has
  vanishing `H¹`, with `L` occurring in neither the bound nor any hypothesis but the tower.
* `AlgebraicGeometry.exists_uniform_bound_forall_baseChange` — the same read as DAT-0a's own
  `∃ b`-shape, with the `∃` **outside** the quantifier over `L`.  This is the statement the
  coverage layer's "per-fibre threshold" pricing assumed to be unavailable.
* `AlgebraicGeometry.mem_chartLocus_of_ledger_bound` — coverage's locus membership with the
  threshold hypothesis **discharged**, leaving `hdeg` (the calibration) as the only numeric
  input.
* `AlgebraicGeometry.exists_chartIndex_mem_chartLocus_of_ledger_bound` — the composite with
  `index_of_threshold`'s direction: at the ledger parameter there is a legal chart index whose
  locus contains the point.
* `AlgebraicGeometry.admissibleCoverageParameter` — a multiple of the positive theta degree
  above the uniform bound, hence unconditionally a divisor degree.
* `AlgebraicGeometry.exists_uniform_admissibleCoverageChart_eq_univ` — one legal chart locus is
  `Set.univ` for every `pic⁰` class, uniformly in the test; no splitting or arithmetic input
  remains.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-- The standing `C.left`-over-`k` structure keyed on `C.hom`, the one the ledger's `hπ` and
the χ-normalization are phrased against. -/
noncomputable local instance instOverCleftCoverageThreshold :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]

noncomputable section

/-! ## The uniform threshold -/

/-- **THE THRESHOLD AT AN ARBITRARY SPLITTING FIELD, PI-FREE AND UNIFORM.**

Every divisor on `relCurve C L` whose degree is at least
`windowM_choice π hπ g * windowδ π + g` has vanishing `H¹` — for **every** field extension
`L/k`, with the same bound.

Read the bound: `windowM_choice π hπ g` and `windowδ π` are ledger constants of the *base*
field, so `L` occurs nowhere in it.  That is what makes this uniform, and it is the fact the
coverage layer's pricing of its own residue assumed to be unavailable
(`Pic0ChartCoverageIndexSlack.lean` item 3, `Pic0ChartCoverageNoDrop.lean`'s retraction: both
treat DAT-0a's threshold at `L` as a per-`L` quantity still to be obtained).

The route uses **no** `π` at the extension.  **The clause that used to follow here — "which is
why it exists at all: DAT-0a needs a finite dominant `relCurve C L ⟶ P1 L` and this tree has
none" — is RETRACTED** (see the module docstring): the tree does produce one, via
`exists_isFinite_isDominant_toP1` plus the `baseChangeBundle` instances, so DAT-0a *is*
instantiable at `L` and being π-free is a convenience here rather than a necessity.  See also
the re-derivation notice: this statement is a weaker corollary of the landed
`subsingleton_h1_of_windowA_le_deg`.  Concretely,
`subsingleton_hModule_one_of_witness` peels from a single witness, and the witness is the
transported window divisor `windowN C L hπ g` whose vanishing is `subsingleton_h1_windowN`
and whose degree is `M·δ` (`deg_windowN`).  The χ at `L` is the base normalization
transported by `chi_relCurve`. -/
theorem subsingleton_h1_of_ledger_bound {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (L : Type u) [Field L] [Algebra k L]
    [IsIntegral (relCurve C L)]
    [SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L))]
    [QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L))]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0)]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1)]
    (D : (relCurve C L).CurveDivisor)
    (hD : (windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ)
      ≤ Scheme.CurveDivisor.deg L D) :
    Subsingleton (Sheaf.HModule ((relCurve C L).divisorSheaf L D) 1) := by
  refine subsingleton_hModule_one_of_witness L (windowN C L hπ g) D
    (subsingleton_h1_windowN C L hπ g) ?_
  rw [deg_windowN, chi_relCurve (n := g) hχ L]
  linarith

/-- **The threshold in DAT-0a's own `∃ b` shape, with the `∃` OUTSIDE the quantifier over
the field.**

`exists_bound_subsingleton_hModule_one_of_isFinite_toP1` reads
`∃ b, ∀ D, b ≤ deg D → H¹ = 0` at *one* curve over *one* field.  The coverage layer needs it
at the splitting field of each test point, and the pricing in
`Picard/Pic0ChartCoverageIndexSlack.lean` reasons about "the threshold `b_L`" as though the
`∃` had to sit inside the choice of `L`.  It does not: this is the same shape with the
quantifiers in the order that makes the calibration a single equation rather than a family of
them.

Stated separately from `subsingleton_h1_of_ledger_bound` because *this* is the statement the
residue was priced against, and having it as an `∃` makes the comparison mechanical rather
than a reading of two docstrings.  The witness is the ledger value, which is why it does not
depend on `L`. -/
theorem exists_uniform_bound_forall_baseChange {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ)) :
    ∃ b : ℤ, ∀ (L : Type u) (_ : Field L) (_ : Algebra k L),
      ∀ (_ : IsIntegral (relCurve C L))
        (_ : SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)))
        (_ : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)))
        (_ : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0))
        (_ : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1)),
      ∀ D : (relCurve C L).CurveDivisor, b ≤ Scheme.CurveDivisor.deg L D →
        Subsingleton (Sheaf.HModule ((relCurve C L).divisorSheaf L D) 1) :=
  ⟨(windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ),
    fun L _ _ _ _ _ _ _ D hD => subsingleton_h1_of_ledger_bound hπ g hχ L D hD⟩

/-! ## An unconditional admissible parameter above the bound

The ledger value `B = M·δ + g` is a sufficient vanishing bound, not a parameter to which the
chart degree must be equal.  Requiring equality created the false residue
`IsDivisorDegree C g`: over an arbitrary field the genus need not be a divisor degree.

The repair is to choose a larger parameter which is visibly a divisor degree.  The pinned
theta degree `d₁` is positive, so `B·d₁ ≥ B`; it is also a divisor degree by construction.
This section packages that choice and composes it with the existing finite-separable splitting
producer.  No field, divisor, splitting, or arithmetic hypothesis is added.
-/

/-- A chart parameter which is both above the uniform vanishing bound and visibly admissible.

It is the nonnegative ledger bound multiplied by the positive degree of the pinned theta class.
The `toNat`s only turn those already nonnegative integers into a chart parameter. -/
def admissibleCoverageParameter {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ) : ℕ :=
  (((windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ)).toNat) *
    (classDeg k (thetaCechClass C)).toNat

/-- The integer value of `admissibleCoverageParameter` is `B·d₁`. -/
theorem admissibleCoverageParameter_cast
    {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ) :
    (admissibleCoverageParameter (C := C) hπ g : ℤ)
      = ((windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ)) *
          classDeg k (thetaCechClass C) := by
  have hB : 0 ≤ (windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ) :=
    add_nonneg (mul_nonneg (Int.natCast_nonneg _) (windowδ_nonneg π))
      (Int.natCast_nonneg _)
  rw [admissibleCoverageParameter, Nat.cast_mul, Int.toNat_of_nonneg hB,
    Int.toNat_of_nonneg (le_trans (by omega) (one_le_classDeg_thetaCechClass (C := C)))]

/-- The admissible parameter is at least the uniform ledger bound. -/
theorem ledgerBound_le_admissibleCoverageParameter
    {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ) :
    (windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ)
      ≤ (admissibleCoverageParameter (C := C) hπ g : ℤ) := by
  have hB : 0 ≤ (windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ) :=
    add_nonneg (mul_nonneg (Int.natCast_nonneg _) (windowδ_nonneg π))
      (Int.natCast_nonneg _)
  rw [admissibleCoverageParameter_cast hπ g]
  exact le_mul_of_one_le_right hB (one_le_classDeg_thetaCechClass (C := C))

/-- The admissible parameter is the degree of a divisor on the base-changed curve. -/
theorem isDegree_admissibleCoverageParameter
    {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ) :
    IsDivisorDegree C (admissibleCoverageParameter (C := C) hπ g : ℤ) := by
  have hB : 0 ≤ (windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ) :=
    add_nonneg (mul_nonneg (Int.natCast_nonneg _) (windowδ_nonneg π))
      (Int.natCast_nonneg _)
  rw [admissibleCoverageParameter_cast hπ g]
  simpa [Int.toNat_of_nonneg hB] using
    isDegree_mul_thetaDeg C
      (((windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ)).toNat)

/-- A legal chart index at the unconditional admissible coverage parameter. -/
theorem exists_admissibleCoverageChartIndex
    {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ) :
    ∃ (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor),
      Scheme.CurveDivisor.deg k Z
        = (m : ℤ) * classDeg k (thetaCechClass C)
          - (admissibleCoverageParameter (C := C) hπ g : ℤ) :=
  chartIndex_of_isDegree C (isDegree_admissibleCoverageParameter hπ g)

/-- A legal index at the admissible parameter contains every degree-zero fibre point in its
chart locus.

The finite separable splitting and presenting class are produced internally by
`exists_splitting_of_picEt`.  The only caller input about the class is the degree-zero equation
already carried by `pic0Subgroup`. -/
theorem mem_chartLocus_of_admissibleCoverageIndex
    {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hZ : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C)
        - (admissibleCoverageParameter (C := C) hπ g : ℤ))
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : T.left)
    (hlam : degAt lam (Over.testPoint t) = 0) :
    t ∈ chartLocus C m Z lam := by
  obtain ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, M₀, hM₀⟩ :=
    exists_splitting_of_picEt C (picEtMap C (Over.testPoint t) lam)
  letI := hLfield
  letI := hkL
  letI := hKL
  letI := htow
  letI := hfin
  letI := hsep
  haveI : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L
  haveI : SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instSmoothOfRelativeDimensionBaseChange C L
  haveI : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instQuasiCompactBaseChange C L
  haveI : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
    instModuleFiniteHModuleZeroBaseChange C L
  haveI : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
    instModuleFiniteHModuleOneBaseChange C L
  refine mem_chartLocus_of_vanishing_bound C lam t m Z M₀ hM₀
    (admissibleCoverageParameter (C := C) hπ g : ℤ) ?_ ?_
  · intro D hD
    exact subsingleton_h1_of_ledger_bound hπ g hχ L D
      ((ledgerBound_le_admissibleCoverageParameter hπ g).trans hD)
  · rw [relCurveMap_eq_overSpecMap_ofId]
    refine (classDeg_presenting_twist C lam (Over.testPoint t) hlam L M₀ hM₀ m Z).trans ?_
    rw [hZ]
    ring

/-- One chart index, chosen independently of the test and class, contains every degree-zero
fibre point in its chart locus. -/
theorem exists_uniform_admissibleCoverageChart
    {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ)) :
    ∃ (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor),
      Scheme.CurveDivisor.deg k Z
          = (m : ℤ) * classDeg k (thetaCechClass C)
            - (admissibleCoverageParameter (C := C) hπ g : ℤ) ∧
        ∀ {T : Over (Spec (.of k))} (lam : picEt C T) (t : T.left),
          degAt lam (Over.testPoint t) = 0 → t ∈ chartLocus C m Z lam := by
  obtain ⟨m, Z, hZ⟩ := exists_admissibleCoverageChartIndex hπ g
  exact ⟨m, Z, hZ, fun lam t hlam =>
    mem_chartLocus_of_admissibleCoverageIndex hπ g hχ m Z hZ lam t hlam⟩

/-- **The producer-facing endpoint:** one legal chart locus is all of the test space for every
`pic⁰` class, uniformly in the test.

This closes the numeric and splitting part of pointwise coverage.  It does not produce the
neighbourhood morphism into the chart; that separate spreading-out obligation remains in
`Pic0ChartCoverageSlice`. -/
theorem exists_uniform_admissibleCoverageChart_eq_univ
    {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ)) :
    ∃ (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor),
      Scheme.CurveDivisor.deg k Z
          = (m : ℤ) * classDeg k (thetaCechClass C)
            - (admissibleCoverageParameter (C := C) hπ g : ℤ) ∧
        ∀ {T : Over (Spec (.of k))} (lam : pic0Subgroup C T),
          chartLocus C m Z lam.1 = Set.univ := by
  obtain ⟨m, Z, hZ, hmem⟩ := exists_uniform_admissibleCoverageChart hπ g hχ
  refine ⟨m, Z, hZ, ?_⟩
  intro T lam
  apply Set.eq_univ_of_forall
  intro t
  exact hmem lam.1 t
    (mem_pic0Subgroup_iff.mp lam.2 (Over.testPointField t) (Over.testPoint t))

/-! ## Coverage with the threshold discharged

`mem_chartLocus_of_vanishing_bound` (`Picard/Pic0ChartCoverageNoDrop.lean:154`) takes `hb`
(the threshold) and `hdeg` (the calibration).  The threshold is now available at the
splitting field, so the composite below carries only the calibration — which is what
`Pic0ChartCoverageIndexSlack`'s `index_of_threshold` is about. -/

/-- **Coverage's locus membership with the threshold hypothesis DISCHARGED.**

Verbatim `mem_chartLocus_of_vanishing_bound` with `hb` supplied by
`subsingleton_h1_of_ledger_bound` at the ledger bound, so the only numeric input left is
`hdeg` — the calibration equating the twisted presenting class's degree with the bound.

Note what remains and what does not.  Gone: the per-fibre existence of a threshold, which the
coverage prose treated as the blocker.  Still here: `hdeg`, and by `ledger_forces_b_eq_n` that
pins the chart parameter to `windowM_choice π hπ g * windowδ π + g`.  Since `n` is free
throughout the chart layer, that is admissible — but it is *not* `n = g`, and
`hb_forces_h0_eq_one` continues to show why it cannot be. -/
theorem mem_chartLocus_of_ledger_bound {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : T.left)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    {L : Type u} [Field L] [Algebra k L] [Algebra (Over.testPointField t) L]
    [IsScalarTower k (Over.testPointField t) L]
    [Module.Finite (Over.testPointField t) L]
    [Algebra.IsSeparable (Over.testPointField t) L]
    (M₀ : (relCurve C L).CechPic)
    (hM₀ : PicEtAff.map C L
        (picEtAffineEquiv C (Over.testPointField t) (picEtMap C (Over.testPoint t) lam))
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    [IsIntegral (relCurve C L)]
    [SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L))]
    [QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L))]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0)]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1)]
    (hdeg : classDeg L (M₀ * Scheme.CechPic.map (relCurveMap C k L)
      (chartTwistClass C m Z))
      = (windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ)) :
    t ∈ chartLocus C m Z lam :=
  mem_chartLocus_of_vanishing_bound C lam t m Z M₀ hM₀
    ((windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ))
    (fun D hD => subsingleton_h1_of_ledger_bound hπ g hχ L D hD) hdeg

/-! ## The calibration is discharged by the chart-index constraint alone

`mem_chartLocus_of_ledger_bound` still carries `hdeg`.  But `hdeg` is not an independent
obligation: `classDeg_presenting_twist` (`Picard/Pic0ChartCoverageDegreeStep2.lean:124`)
computes the presenting class's degree as `m·d₁ − deg_k Z` from the degree-zero-ness of `λ` at
the point, so the constraint `deg_k Z = m·d₁ − (M·δ + g)` — a chart index legal at the ledger
parameter, in the sense of `index_of_threshold` — supplies it outright. -/

/-- **COVERAGE AT THE LEDGER PARAMETER, WITH BOTH NUMERIC INPUTS DISCHARGED.**

Given only: `λ` of fibre degree zero at the point, a splitting `M₀` of its fibre class, and a
chart index legal at the **ledger parameter** `M·δ + g` (i.e. `deg_k Z = m·d₁ − (M·δ + g)`),
the point lies in the chart locus.

Compare `mem_chartLocus_of_vanishing_bound`, whose two numeric hypotheses were `hb` (the
threshold) and `hdeg` (the calibration).  Both are gone: `hb` by
`subsingleton_h1_of_ledger_bound` — the uniform π-free threshold — and `hdeg` by
`classDeg_presenting_twist` from the index constraint.  What remains is *only* the splitting
and the degree-zero-ness, which coverage has (`exists_splitting_of_picEt`,
`Pic0ChartSplit.lean:143`, and the `pic0Subgroup` membership of the class).

**This is the reduction, and it is worth being exact about its scope.**  It is
locus-membership at a point of a test, at ONE chart parameter, and it says nothing about the
pointwise datum `chartsCoverLocally_of_pointwise` needs — that also wants a chart POINT over a
neighbourhood, i.e. the divisor family whose class is `λ`, which is the spreading-out
`Pic0ChartCoverageSlice.lean` records as absent for this carrier.  So antecedent 2 is not
closed and I claim nothing on it.  What is closed is that the *numeric* half of B-5 step 3 —
which two files and the `dat-b` row present as the open question — has no content left.

The parameter is `M·δ + g`, not `g`: `hb_forces_h0_eq_one` is untouched, and this route
deliberately does not go near `b = g`. -/
theorem mem_chartLocus_of_ledgerIndex {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : T.left)
    (hlam : degAt lam (Over.testPoint t) = 0)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hZ : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C)
        - ((windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ)))
    {L : Type u} [Field L] [Algebra k L] [Algebra (Over.testPointField t) L]
    [IsScalarTower k (Over.testPointField t) L]
    [Module.Finite (Over.testPointField t) L]
    [Algebra.IsSeparable (Over.testPointField t) L]
    (M₀ : (C ⊗ overSpec k L).left.CechPic)
    (hM₀ : PicEtAff.map C L
        (picEtAffineEquiv C (Over.testPointField t) (picEtMap C (Over.testPoint t) lam))
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    [IsIntegral (relCurve C L)]
    [SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L))]
    [QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L))]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0)]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1)] :
    t ∈ chartLocus C m Z lam := by
  refine mem_chartLocus_of_ledger_bound hπ g hχ lam t m Z M₀ hM₀ ?_
  -- `mem_chartLocus_of_vanishing_bound` states `hdeg` in the `relCurveMap` spelling while
  -- `classDeg_presenting_twist` delivers the E-iv-alg transition one; they are the same
  -- morphism (`relCurveMap_eq_overSpecMap_ofId`), but not syntactically.
  rw [relCurveMap_eq_overSpecMap_ofId]
  -- `.trans` rather than a second `rw`: the two spellings of the fibre curve
  -- (`relCurve C L` and the product `(C ⊗ overSpec k L).left`) are defeq but not at
  -- `instances` transparency, so `rw` reports no occurrence on a goal that displays the
  -- pattern.  Application-position unification uses default transparency and goes through.
  refine (classDeg_presenting_twist C lam (Over.testPoint t) hlam L M₀ hM₀ m Z).trans ?_
  rw [hZ]
  ring

/-- **The `∃`-form the DAT-B B-6 packaging consumes**, at the ledger parameter: the chart index
is exhibited rather than assumed.

`index_of_threshold` says the ledger parameter is realisable; this says the realisation feeds
coverage.  The witness is `⟨m, Z⟩` for any `(m, Z)` satisfying the ledger constraint, so the
statement is only as strong as the existence of such a pair — which is why the constraint stays
a hypothesis: `Z` of prescribed degree is a divisor-side existence statement this file does not
prove and does not claim. -/
theorem exists_chartIndex_mem_chartLocus_of_ledgerIndex
    {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : T.left)
    (hlam : degAt lam (Over.testPoint t) = 0)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hZ : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C)
        - ((windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ)))
    {L : Type u} [Field L] [Algebra k L] [Algebra (Over.testPointField t) L]
    [IsScalarTower k (Over.testPointField t) L]
    [Module.Finite (Over.testPointField t) L]
    [Algebra.IsSeparable (Over.testPointField t) L]
    (M₀ : (C ⊗ overSpec k L).left.CechPic)
    (hM₀ : PicEtAff.map C L
        (picEtAffineEquiv C (Over.testPointField t) (picEtMap C (Over.testPoint t) lam))
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    [IsIntegral (relCurve C L)]
    [SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L))]
    [QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L))]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0)]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1)] :
    ∃ (m' : ℕ) (Z' : (C ⊗ overSpec k k).left.CurveDivisor),
      t ∈ chartLocus C m' Z' lam :=
  ⟨m, Z, mem_chartLocus_of_ledgerIndex hπ g hχ lam t hlam m Z hZ M₀ hM₀⟩

/-! ## The coupling limit, as a theorem rather than a caveat

The parameter this route delivers is `M·δ + g`, and the divisor-representability endpoint
`divFunctor_representableBy_of_chartClause` (`Picard/DivRepAffPullClause.lean:490`) supplies
`rep` at the parameter its own `hchi` pins, i.e. at the genus.  Those two are the same number
only in the degenerate case, and the statement below is the proof — recorded so the limit
cannot be mistaken for a hedge, and so that nobody reads the reduction above as delivering a
chart parameter the divRep lane can currently feed.

This is the sharp form of the question `Pic0ChartAtlasParamFree.lean`'s header hands to the
divRep lane: *at which parameters is `divFunctor C π n` representable?*  Heterogeneity
(`mixedParamChart`) means the atlas needs no uniform answer, but it does need **some**
parameter at which both coverage and `rep` are available, and `M·δ + g = g` is not it. -/

-- The `C.hom` instances are idle here: the statement is ledger arithmetic plus
-- `genus_eq_zero_of_windowBound_nonpos`, which reads only the `C.left`-over-`k` side.
end

/-! ### The coupling limit lives on an abstract curve, not on `C`

Rather than `omit` the idle `C.hom` instances one at a time — the linter cannot be satisfied
piecewise here, because dropping any proper subset leaves a referenced section variable — the
statement is given at the generality its proof actually inhabits.  It is ledger arithmetic plus
`genus_eq_zero_of_windowBound_nonpos`, both of which are stated for an abstract curve `Y` over
`K` with a finite dominant `π`; the challenge curve `C` never enters.  So the honest home is
this section, and `C` does not occur in the statement at all.

That is also the `delete-the-geometry-and-retypecheck` test applied to my own theorem: what
survived the deletion is where the theorem lives. -/

section LedgerParam

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]

/-- **THE LEDGER PARAMETER EQUALS THE GENUS ONLY WHEN THE GENUS IS ZERO.**

If `M·δ + g = g` then `g = 0`.  Since `δ ≥ 1` (`one_le_windowδ`), the equation forces
`M = 0`; `windowM_spec` then makes `windowBound ≤ 0` — because its right-hand side is `M·δ = 0`
while the left-hand side dominates `windowBound` — and `genus_eq_zero_of_windowBound_nonpos`
concludes.

**Current reading.**  This theorem still rules out identifying the *minimal named bound*
`M·δ + g` with the genus on a positive-genus curve.  It is no longer a coupling limit for the
coverage route: `admissibleCoverageParameter` chooses a larger parameter, and
`exists_uniform_admissibleCoverageChart_eq_univ` proves the corresponding chart-locus endpoint
without a genus-degree hypothesis.  The remaining join is representability at that larger
parameter, not equality of the minimal bound with `g`. -/
theorem genus_eq_zero_of_ledgerParam_eq_genus {π : Y ⟶ P1 K} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K)) (g : ℕ)
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ))
    (heq : (windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ) = (g : ℤ)) :
    g = 0 := by
  have hδ : 1 ≤ windowδ π := one_le_windowδ π
  have hM : (windowM_choice π hπ g : ℤ) * windowδ π = 0 := by linarith
  have hspec := windowM_spec π hπ g
  have hgnn : (0 : ℤ) ≤ (g : ℤ) := Int.natCast_nonneg _
  have hsnn : (0 : ℤ) ≤ (windowS_choice π hπ g : ℤ) := Int.natCast_nonneg _
  have hprod : (0 : ℤ) ≤ ((g : ℤ) + 2) * ((windowS_choice π hπ g : ℤ) + 1) * windowδ π := by
    have h1 : (0 : ℤ) ≤ (g : ℤ) + 2 := by linarith
    have h2 : (0 : ℤ) ≤ (windowS_choice π hπ g : ℤ) + 1 := by linarith
    exact mul_nonneg (mul_nonneg h1 h2) (by linarith)
  refine genus_eq_zero_of_windowBound_nonpos π hπ g ?_ hO hχ
  rw [hM] at hspec
  linarith

end LedgerParam

end AlgebraicGeometry
