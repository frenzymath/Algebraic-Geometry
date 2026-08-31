/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartCoveragePointwise
import AlgebraicJacobian.Picard.Pic0ChartIndexAdmissible
import AlgebraicJacobian.Picard.Pic0ChartUnivReduce

/-!
# The coupling of the atlas open to the coverage witness

`pic0RepresentableByOfCharts` (`Picard/Pic0SigmaSheaf.lean:161`) has three antecedents, and
the board tracks them on three separate rows: `IsChartUniv` (c9b), Zariski-local surjectivity
of `Sigma.desc f` (dat-b B-6), and `rep i` (divrep).  Reading those rows one concludes the
three compose — discharge each and the seam fires.

**They do not compose as stated.**  The atlas the seam consumes is a family of *restricted*
charts `restrictChart (abelSigmaChart …) (V i)` (`Picard/Pic0ChartAtlasParamFree.lean:86`),
whose source is `(V i : Scheme)` — an open of the *chart source*, i.e. of the divisor scheme.
So the coverage antecedent, unfolded through `chartsCoverLocally_of_pointwise`
(`Pic0ChartCoveragePointwise.lean:128`), must produce a chart point
`x : (W : Scheme) ⟶ (V i : Scheme)` landing **in that same `V i`**, while coverage geometry
produces a point of the divisor scheme `D.left` with no such constraint.  The two opens the
route wants to identify live on different objects — `V i` on the divisor scheme, `chartLocus`
on the test — and no declaration in the tree relates them.

That is an obligation *between* two antecedents, owned by no row, and it is why "close c9b,
then close B-6" would not have composed even with both closed.

## What this file does about it

It names the coupling and derives restricted coverage from unrestricted coverage together
with a range containment: the coverage witness, viewed in the chart source, factors
set-theoretically through `V i`.  Given that, the witness lifts to `V i` along the open
immersion `(V i).ι` by `IsOpenImmersion.lift`, and the class it names is unchanged because
`restrictChart` is *by definition* precomposition with `yoneda.map (V i).ι` — so the lift's
chart value is the unlifted one, with no transport.

**THREE CORRECTIONS TO AN EARLIER DRAFT OF THIS HEADER**, all from a fresh-context audit
(2026-07-29, inbox `I-0894`), because each would have mispriced the row:

1. the hypothesis is **NOT "weaker than either antecedent"**, as the draft claimed.  It is the
   unrestricted coverage datum **conjoined** with the containment, so it *implies* the
   coverage antecedent and is strictly STRONGER than it.  What is true is the much smaller
   claim that the containment is all that separates unrestricted from restricted coverage;
2. `liftPointwiseToOpens` and `pointwise_of_pointwise_restrictChart` together are one
   **biconditional**, and its transport step (`restrictChart_app_apply`) is `rfl`.  So this
   file is a *repackaging with its difference named*, and **it closes no gate**.  It is
   reported as routing information, not as progress on any antecedent;
3. the draft argued about "`V i = chartLocus`" in two places.  **Those carriers do not meet**:
   `V i : (X i).Opens` is an open of the chart source (the divisor scheme), while
   `chartLocus C m Z lam : Set ↥T.left` is a set on a *test*.  The only bridge is
   `chartLocusOpens`, which lands in `T.left.Opens` and costs `haff` (= dat-b's B-4).  The
   mismatch is precisely what this file was written to expose, so reasoning as though the two
   were interchangeable — as the draft did below — defeated the purpose.

What survives all three: the containment is genuine content (probes below), it is exactly the
difference between the two coverage statements (the converse), and no declaration in the tree
relates the two carriers.

## Main declarations

* `AlgebraicGeometry.PointwiseCoverage` — the pointwise coverage datum of B-5, named for an
  arbitrary chart family so the two atlases (unrestricted, restricted) can be compared.
* `AlgebraicGeometry.liftPointwiseToOpens` — **the coupling**: pointwise coverage for a family
  `f` plus the range containment gives pointwise coverage for the *restricted* family
  `fun i => restrictChart (f i) (V i)`.
* `AlgebraicGeometry.isLocallySurjective_restrictChart_of_pointwise` — the composite into the
  instance the seam consumes, for the restricted atlas.
* `AlgebraicGeometry.pointwise_of_pointwise_restrictChart` — the **converse**: restricted
  coverage gives unrestricted coverage *and* the containment.  So `hV` is not a hypothesis
  chosen for provability — it is exactly the difference between the two, and a lane cannot
  reach the restricted atlas while avoiding it.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

variable (C) in
/-- **The pointwise coverage datum of B-5**, named.

This is verbatim the hypothesis of `chartsCoverLocally_of_pointwise`
(`Pic0ChartCoveragePointwise.lean:128`), given a name so that the same statement can be
compared at two different chart families — which is the whole point of this file: B-6 is
consumed at the *restricted* atlas, while coverage geometry produces the datum at the
*unrestricted* one. -/
def PointwiseCoverage {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) : Prop :=
  ∀ (T : Scheme.{u}) (s : (pic0SigmaSheaf C).1.obj (op T)) (t : ↥T),
    ∃ (W : T.Opens) (_ : t ∈ W) (i : ι) (x : (W : Scheme.{u}) ⟶ X i),
      (f i).app (op (W : Scheme.{u})) x = (pic0SigmaSheaf C).1.map (W.ι).op s

/-! ## The chart value of a restricted chart at a lifted point -/

/-- **A restricted chart reads a lifted point exactly as the unrestricted chart reads the
point itself.**

`restrictChart f V` is `yoneda.map V.ι ≫ f` by definition, so its value at `u` is the value
of `f` at `u ≫ V.ι`.  No transport, no naturality of `f` — the composition is on the source
side, where `yoneda.map` is precomposition.

This is the entire reason the coupling below is cheap, and it is worth isolating: a lane that
expected the two chart values to differ by a restriction map would look for a compatibility
that is not needed. -/
lemma restrictChart_app_apply {X : Scheme.{u}} (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1)
    (V : X.Opens) {S : Scheme.{u}} (u : S ⟶ (V : Scheme.{u})) :
    (restrictChart f V).app (op S) u = f.app (op S) (u ≫ V.ι) :=
  rfl

/-! ## The coupling -/

variable (C) in
/-- **THE COUPLING**: pointwise coverage for `f` plus a range containment gives pointwise
coverage for the restricted family.

The containment is the honest content: at the point, index and witness coverage produces, the
witness's image in the chart source lies inside `V i`.  Everything else is the lift along the
open immersion `(V i).ι` and `restrictChart_app_apply`, which is `rfl` — so this direction
carries no mathematics beyond the lift, and together with its converse below it is a
biconditional rather than a reduction.  **It closes no gate.**

Note the shape of the hypothesis: it quantifies over the data coverage *returns*, not over all
opens or all witnesses.  So a producer discharges it exactly where it produces the witness,
which is the only place the information is available; a formulation asking for the containment
uniformly over all witnesses would be strictly stronger.

What the containment *means* geometrically depends on which open `V i` is, and this file
deliberately does not assume an answer — in particular `V i` is an open of the chart source
while `chartLocus` is a set on a test, so the two are not interchangeable and the intended
instantiation still owes the `chartLocusOpens` bridge (cost: `haff`, i.e. dat-b's B-4). -/
theorem liftPointwiseToOpens {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) (V : ∀ i, (X i).Opens)
    (h : ∀ (T : Scheme.{u}) (s : (pic0SigmaSheaf C).1.obj (op T)) (t : ↥T),
      ∃ (W : T.Opens) (_ : t ∈ W) (i : ι) (x : (W : Scheme.{u}) ⟶ X i),
        (f i).app (op (W : Scheme.{u})) x = (pic0SigmaSheaf C).1.map (W.ι).op s ∧
          Set.range (x.base) ⊆ Set.range ((V i).ι.base)) :
    PointwiseCoverage C (fun i => restrictChart (f i) (V i)) := by
  intro T s t
  obtain ⟨W, htW, i, x, hx, hrange⟩ := h T s t
  refine ⟨W, htW, i, IsOpenImmersion.lift ((V i).ι) x hrange, ?_⟩
  rw [restrictChart_app_apply, IsOpenImmersion.lift_fac]
  exact hx

variable (C) in
/-- **The composite**: coverage plus the containment gives the local-surjectivity instance
`pic0RepresentableByOfCharts` consumes *at the restricted atlas* — which is the atlas
`mixedParamRepresentableBy` (`Pic0ChartAtlasParamFree.lean:125`) and every real chart family
is built from.

Stated because this, not `isLocallySurjective_sigmaDesc_of_pointwise`, is what a coverage lane
owes when the atlas is restricted: the two differ by exactly `hV`. -/
theorem isLocallySurjective_restrictChart_of_pointwise {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) (V : ∀ i, (X i).Opens)
    (h : ∀ (T : Scheme.{u}) (s : (pic0SigmaSheaf C).1.obj (op T)) (t : ↥T),
      ∃ (W : T.Opens) (_ : t ∈ W) (i : ι) (x : (W : Scheme.{u}) ⟶ X i),
        (f i).app (op (W : Scheme.{u})) x = (pic0SigmaSheaf C).1.map (W.ι).op s ∧
          Set.range (x.base) ⊆ Set.range ((V i).ι.base)) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (fun i => restrictChart (f i) (V i))) :=
  isLocallySurjective_sigmaDesc_of_pointwise C _ (liftPointwiseToOpens C f V h)

/-! ## The converse: `hV` is the exact difference, not a convenient extra

A coupling lemma whose hypothesis is stronger than the gap it bridges hides the gap instead of
naming it.  This section rules that out: restricted coverage gives back unrestricted coverage
together with the containment, so `hV` is precisely what separates the two. -/

variable (C) in
/-- **The converse of the coupling.**  Pointwise coverage for the restricted family gives
pointwise coverage for `f` *and* the range containment at the produced witness.

So `liftPointwiseToOpens`' hypothesis is not a strengthening chosen to make the proof go: it
is logically equivalent to the conclusion.  In particular a lane cannot obtain B-6 for the
restricted atlas — the one the seam consumes — while avoiding the statement that coverage hits
its classes inside `V i`.

The witness is `x ≫ (V i).ι`, whose range is contained in that of `(V i).ι` by construction,
and whose chart value under `f i` is the restricted chart's value at `x` by
`restrictChart_app_apply`. -/
theorem pointwise_of_pointwise_restrictChart {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) (V : ∀ i, (X i).Opens)
    (h : PointwiseCoverage C (fun i => restrictChart (f i) (V i))) :
    ∀ (T : Scheme.{u}) (s : (pic0SigmaSheaf C).1.obj (op T)) (t : ↥T),
      ∃ (W : T.Opens) (_ : t ∈ W) (i : ι) (x : (W : Scheme.{u}) ⟶ X i),
        (f i).app (op (W : Scheme.{u})) x = (pic0SigmaSheaf C).1.map (W.ι).op s ∧
          Set.range (x.base) ⊆ Set.range ((V i).ι.base) := by
  intro T s t
  obtain ⟨W, htW, i, u, hu⟩ := h T s t
  refine ⟨W, htW, i, u ≫ (V i).ι, hu, ?_⟩
  intro z hz
  obtain ⟨w, rfl⟩ := hz
  exact ⟨u.base w, rfl⟩

/-! ## A multi-index atlas does not remove chart-index arithmetic -/

variable (C) in
/-- Pointwise coverage has a genuinely inhabited chart index.  The witness is read at
`Spec k`, not at the empty test, where every index-valued condition collapses. -/
theorem nonempty_index_of_pointwiseCoverage {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (hcov : PointwiseCoverage C f) : Nonempty ι := by
  classical
  let s : (pic0SigmaSheaf C).1.obj (op (Spec (.of k))) := ⟨𝟙 _, 1⟩
  let t : Spec (.of k) := Classical.choice inferInstance
  obtain ⟨_, _, i, _, _⟩ := hcov (Spec (.of k)) s t
  exact ⟨i⟩

variable (C) in
/-- A nonempty family of legal chart indices at one parameter exists exactly when that
parameter is a divisor degree.  Allowing arbitrarily many indices does not weaken the
arithmetic condition carried by one legal index. -/
theorem exists_nonempty_legal_chart_index_family_iff_isDivisorDegree (n : ℕ) :
    (∃ (ι : Type u) (_ : Nonempty ι) (m : ι → ℕ)
        (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor),
      ∀ i, Scheme.CurveDivisor.deg k (Z i)
        = (m i : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
      ↔ IsDivisorDegree C (n : ℤ) := by
  constructor
  · rintro ⟨ι, hι, m, Z, hdeg⟩
    let i : ι := Classical.choice hι
    exact isDegree_of_chartIndex C (m i) (Z i) (hdeg i)
  · intro hn
    obtain ⟨m, Z, hdeg⟩ := chartIndex_of_isDegree C hn
    exact ⟨PUnit, inferInstance, fun _ => m, fun _ => Z, fun _ => hdeg⟩

variable (C) in
/-- Any pointwise-covering family indexed by legal charts at parameter `n` forces `n` to be
a divisor degree.  In particular, a genus-parameter multi-index atlas cannot be produced
unconditionally by replacing one base-field chart with many base-field charts. -/
theorem isDivisorDegree_of_pointwiseCoverage_legal_chart_index_family
    {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (hcov : PointwiseCoverage C f) (n : ℕ) (m : ι → ℕ)
    (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ)) :
    IsDivisorDegree C (n : ℤ) := by
  let i : ι := Classical.choice (nonempty_index_of_pointwiseCoverage C f hcov)
  exact isDegree_of_chartIndex C (m i) (Z i) (hdeg i)

end

end AlgebraicGeometry
