/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartCoverageAffineTest
import AlgebraicJacobian.Picard.Pic0ChartCoverageAbel

/-!
# DAT-B B-5: the coverage datum RE-SPELLED in the slice — and why that discharges nothing

`Picard/Pic0ChartCoverageAbel.lean:105` (`abelChartApp_eq`) records that the chart
application is a **pair**, and its header warns that a coverage producer must match *two*
equations rather than one — the Σ-components before the classes are even in the same type.
Two roadmap rows and the c9b thread price the coverage datum accordingly.

**This file first claimed that price was avoidable.  It is not, and the retraction is the
content.**  The claim was: a producer working in the slice over `Over.mk (W.ι ≫ s.1)`, rather
than handing over a bare `x : (W : Scheme) ⟶ D.left`, gets the Σ-equation as `Over.w` "for
free".  What is true is that `Over.mk (W.ι ≫ s.1) ⟶ D` **is by definition** the pair of an
`x` and a proof that `x ≫ D.hom = W.ι ≫ s.1`: `(Over.homMk x hx).left = x` and
`Over.w (Over.homMk x hx) = hx` both hold by `rfl`, so the two hypotheses are interderivable
and a producer can do nothing here it could not do before.  Refuted by a fresh-context audit
(inbox `I-1021`); the durable lesson is `I-1024`.

**The reusable error, since it is subtle.**  The non-vacuity check this file ran — `rfl` on
`x ≫ D.hom = W.ι ≫ s.1` at unconstrained `x` **fails** — was read as licensing the discount.
It forbids it.  An equation that is not definitionally free does not become free by moving
into a binder's type; it merely stops appearing as a goal, which is what made the report
convincing.  `slice_iff_bare` below is the one-line probe that settles such a question, and it
is landed so the claim cannot be re-made here.

## What this file is, honestly

A **re-spelling** of the coverage datum, with the pair equation traded for one class equation
plus a richer input type carrying the other.  `datum_of_slice` is one half of an equivalence
(`bare_of_slice` is the other), so by the `I-0896` criterion no obligation was reduced.  It is
worth keeping only because the slice spelling is the shape a divisor-side producer would want
— every such producer here is stated over `overSpec k S`, so a route through them needs the
identification of `Over.mk (W.ι ≫ s.1)` with `overSpec k Γ(Y, W)` at an affine `W`, and that
identification is against the slice form, not the bare one.  That seam is not written here.

The class equation is untouched and is the whole of what remains: it asks that the chart value
of the divisor family named by `g` **is** the given class restricted.  Its cost is a divisor
family over a *neighbourhood* produced from data at a *point* — a spreading-out, measured
absent from the tree for this carrier by two independent censuses (every `DivFamZar` producer
takes its base ring or the affine-opens limit first; the only spreading lemmas,
`exists_supportTube` and its `Confine` instance, act on the support locus of an already-given
local-equation system, not on a class; mathlib's `spread_out_of_isGermInjective'` is about
morphism germs).

**A second limit, and it is the sharper one.**  The two composites below are stated at the
**unrestricted** chart `abelSigmaChart`, whose source is all of `D.left`.
`Pic0AtlasFromDivRep.lean:54` and `Pic0ChartPair.lean:14` both hold that antecedent 1 is
*false* there (the fibres are linear systems `|D|`, so it is not a monomorphism), while the
atlas the tree intends, `mixedParamChart`, has source `(V i : Scheme)`.  So these endpoints
supply antecedent 2 at a family where antecedent 1 fails, and the two do not co-instantiate —
`I-0861`'s V-coupling defect, filed here as `I-1022`.  The site content of
`Pic0ChartCoverageAffineTest.lean` is family-generic and does apply to `mixedParamChart`; only
these instantiated composites are stranded.

## Main declarations

* `AlgebraicGeometry.sigmaComponent_of_slice` — the Σ-component of a slice morphism, which is
  `Over.w`.  **Not a discharge**: see `slice_iff_bare`.
* `AlgebraicGeometry.slice_iff_bare` — **the refutation of this file's original claim**, in the
  kernel rather than in prose: a slice morphism over `Over.mk (W.ι ≫ s.1)` is exactly a bare
  morphism together with the Σ-equation, both directions by `rfl`.
* `AlgebraicGeometry.datum_of_slice` — the datum equation of `chartsCoverLocally_of_affineLocal`
  from the class equation in the slice, and `bare_of_slice` its converse, so the pair is an
  equivalence and reduces nothing.
* `AlgebraicGeometry.chartsCoverLocally_of_slice` — `ChartsCoverLocally` from per-point slice
  data over affine tests.
* `AlgebraicGeometry.isLocallySurjective_of_slice` — antecedent 2, from the same.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

noncomputable section

/-! ## The Σ-component, discharged -/

/-- **The Σ-component of a slice morphism is `Over.w`** — true, and *not* a discharge of the
coverage datum's Σ-equation.  Read it with `slice_iff_bare` immediately below, which is why. -/
theorem sigmaComponent_of_slice {D : Over (Spec (.of k))}
    (Y : Scheme.{u}) (s : (pic0SigmaSheaf C).1.obj (op Y)) (W : Y.Opens)
    (g : Over.mk (W.ι ≫ s.1) ⟶ D) :
    g.left ≫ D.hom = W.ι ≫ s.1 :=
  Over.w g

/-- **A slice morphism IS a bare morphism plus the Σ-equation** — the refutation of this
file's original "the Σ-component is absorbed for free" claim, stated so it cannot be re-made.

Both directions are `rfl`: `Over.homMk` bundles `(x, hx)` into `g` with `g.left = x`, and
`Over.w` projects it back out.  So working in the slice **moves** the Σ-equation into the input
type; it does not discharge it, and a producer owes exactly what it owed before.  What changes
is only that the equation stops appearing as a goal — which is why the original claim looked
measured.

The general form of this check (inbox `I-1024`): when a file reports an obligation absorbed by
a richer input type, derive the new hypothesis from the old one.  One probe settles it. -/
theorem slice_iff_bare {D : Over (Spec (.of k))}
    (Y : Scheme.{u}) (s : (pic0SigmaSheaf C).1.obj (op Y)) (W : Y.Opens) :
    Nonempty (Over.mk (W.ι ≫ s.1) ⟶ D) ↔
      ∃ x : (W : Scheme.{u}) ⟶ D.left, x ≫ D.hom = W.ι ≫ s.1 :=
  ⟨fun ⟨g⟩ => ⟨g.left, Over.w g⟩, fun ⟨x, hx⟩ => ⟨Over.homMk x hx⟩⟩

/-! ## The reduction: one class equation is the whole datum -/

/-- **THE DATUM FROM A SLICE MORPHISM PLUS ONE CLASS EQUATION.**

The hypothesis `hcl` is the class equation in the slice over `Over.mk (W.ι ≫ s.1)`: the chart
value of the divisor family that `g` names is the given class, restricted.  Given it, the full
pair equation that `chartsCoverLocally_of_affineLocal` consumes holds — the Σ-component is
`Over.w g` and the `Over.mkCongr` transport is handled by `Over.sigmaExtension_ext`.

This is the discount `abelChartApp_eq`'s header asks a producer to pay and a producer of this
shape does not owe. -/
theorem datum_of_slice {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (Y : Scheme.{u}) (s : (pic0SigmaSheaf C).1.obj (op Y)) (W : Y.Opens)
    (g : Over.mk (W.ι ≫ s.1) ⟶ D)
    (hcl : (pic0TypeFunctor C).map (Over.mkCongr (Over.w g)).op
        ((pic0TypeFunctor C).map
          (Over.homMk W.ι rfl : Over.mk (W.ι ≫ s.1) ⟶ Over.mk s.1).op s.2)
      = ⟨chartValue C π n m Z (Over.mk (g.left ≫ D.hom))
          (rep.homEquiv (Over.homMk g.left rfl)),
        chartValue_mem_pic0Subgroup C π n m Z hdeg _ _⟩) :
    (abelSigmaChart C π n rep m Z hdeg).app (op (W : Scheme.{u})) g.left
      = (pic0SigmaSheaf C).1.map (W.ι).op s := by
  rw [abelChartApp_eq]
  rw [show ((pic0SigmaSheaf C).1.map (W.ι).op s)
      = ⟨W.ι ≫ s.1, (pic0TypeFunctor C).map
          (Over.homMk W.ι rfl : Over.mk (W.ι ≫ s.1) ⟶ Over.mk s.1).op s.2⟩ from rfl]
  exact Over.sigmaExtension_ext (pic0TypeFunctor C) (Over.w g) hcl

/-- **The converse of `datum_of_slice`**, so the pair is visibly an equivalence and this file
claims no reduction (the `I-0896` criterion).  From the datum equation the class equation is
read off by `Over.sigmaExtension_snd_eq`, the same one-liner with the projection replacing the
constructor. -/
theorem bare_of_slice {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (Y : Scheme.{u}) (s : (pic0SigmaSheaf C).1.obj (op Y)) (W : Y.Opens)
    (g : Over.mk (W.ι ≫ s.1) ⟶ D)
    (hdatum : (abelSigmaChart C π n rep m Z hdeg).app (op (W : Scheme.{u})) g.left
      = (pic0SigmaSheaf C).1.map (W.ι).op s) :
    (pic0TypeFunctor C).map (Over.mkCongr (Over.w g)).op
        ((pic0TypeFunctor C).map
          (Over.homMk W.ι rfl : Over.mk (W.ι ≫ s.1) ⟶ Over.mk s.1).op s.2)
      = ⟨chartValue C π n m Z (Over.mk (g.left ≫ D.hom))
          (rep.homEquiv (Over.homMk g.left rfl)),
        chartValue_mem_pic0Subgroup C π n m Z hdeg _ _⟩ :=
  Over.sigmaExtension_snd_eq (pic0TypeFunctor C) (Over.w g) hdatum

/-! ## Through to antecedent 2

The two composites, so the discount lands at the seam rather than in mid-air.  Both are
stated for the ONE-CHART family `fun _ : ι => abelSigmaChart …`: the slice reduction is about
the chart application, which does not see the index, and heterogeneity is orthogonal
(`Pic0ChartAtlasParamFree.lean`). -/

variable (C π n) in
/-- **`ChartsCoverLocally` from per-point slice data over affine tests.**

The hypothesis is the coverage obligation in its cheapest measured form: over an affine test
only (`Pic0ChartCoverageAffineTest.lean`), a slice morphism rather than a bare morphism (so
the Σ-component is `Over.w`), and one class equation.  Nothing else stands between it and the
sieve condition. -/
theorem chartsCoverLocally_of_slice {ι : Type u} [Nonempty ι] {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (h : ∀ (Y : Scheme.{u}) [IsAffine Y] (s : (pic0SigmaSheaf C).1.obj (op Y)) (y : ↥Y),
      ∃ (W : Y.Opens) (_ : y ∈ W) (g : Over.mk (W.ι ≫ s.1) ⟶ D),
        (pic0TypeFunctor C).map (Over.mkCongr (Over.w g)).op
            ((pic0TypeFunctor C).map
              (Over.homMk W.ι rfl : Over.mk (W.ι ≫ s.1) ⟶ Over.mk s.1).op s.2)
          = ⟨chartValue C π n m Z (Over.mk (g.left ≫ D.hom))
              (rep.homEquiv (Over.homMk g.left rfl)),
            chartValue_mem_pic0Subgroup C π n m Z hdeg _ _⟩) :
    ChartsCoverLocally C (fun _ : ι => abelSigmaChart C π n rep m Z hdeg) := by
  refine chartsCoverLocally_of_affineLocal C _ fun Y _ s y => ?_
  obtain ⟨W, hyW, g, hcl⟩ := h Y s y
  exact ⟨W, hyW, Classical.arbitrary ι, g.left,
    datum_of_slice rep m Z hdeg Y s W g hcl⟩

variable (C π n) in
/-- **Antecedent 2 of `pic0RepresentableByOfCharts`, from slice data over affine tests.**

The composite with B-6 (`isLocallySurjective_sigmaDesc`).  This is the honest endpoint of the
reduction: the instance the DAT-glue seam consumes, from the cheapest form of the coverage
datum the tree can currently state.

**The class equation is still open**, and it is the whole of what is left here.  Its cost is a
divisor family over a *neighbourhood* produced from data at a *point* — a spreading-out, absent
from the tree for this carrier. -/
theorem isLocallySurjective_of_slice {ι : Type u} [Nonempty ι] {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (h : ∀ (Y : Scheme.{u}) [IsAffine Y] (s : (pic0SigmaSheaf C).1.obj (op Y)) (y : ↥Y),
      ∃ (W : Y.Opens) (_ : y ∈ W) (g : Over.mk (W.ι ≫ s.1) ⟶ D),
        (pic0TypeFunctor C).map (Over.mkCongr (Over.w g)).op
            ((pic0TypeFunctor C).map
              (Over.homMk W.ι rfl : Over.mk (W.ι ≫ s.1) ⟶ Over.mk s.1).op s.2)
          = ⟨chartValue C π n m Z (Over.mk (g.left ≫ D.hom))
              (rep.homEquiv (Over.homMk g.left rfl)),
            chartValue_mem_pic0Subgroup C π n m Z hdeg _ _⟩) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (fun _ : ι => abelSigmaChart C π n rep m Z hdeg)) :=
  isLocallySurjective_sigmaDesc _ (chartsCoverLocally_of_slice C π n rep m Z hdeg h)

end

end AlgebraicGeometry
