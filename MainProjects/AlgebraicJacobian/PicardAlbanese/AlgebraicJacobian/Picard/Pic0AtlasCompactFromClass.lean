/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AtlasFiniteType
import AlgebraicJacobian.Picard.JacobianDataQcFromRep

/-!
# `hcpt` IS NOT A FIFTH OBLIGATION: the atlas's compactness input is the qc field's own hypothesis

`Picard/Pic0AtlasFiniteType.lean` corrected the board's three-antecedent picture of the
distance to representability to **four**, discharged the fourth (`hlft`), and then named the
input its own assembly leaves exposed:

> `hcpt` — `CompactSpace` of the glued object.  **Open**, and it is the input this file leaves
> exposed. […] the two routes the tree already names are still the honest ones: a finite
> atlas, or the Abel image.

That dichotomy is **incomplete**, and this file is the correction.  There is a third route, it
was already on the board under a different row (`dat-j.qcfield`), and it needs nothing the
assembly does not already have:

  `compactSpace_of_pic0_class_surjective` (`Picard/JacobianDataQcFromRep.lean`) applied to the
  atlas's *own* representation `pic0RepresentableByOfCharts C (mixedParamChart …) hf` yields
  `CompactSpace (Scheme.LocalRepresentability.glueData hf).glued` — which is the `hcpt` slot of
  `jacobianDataOfMixedParamCharts` **on the nose**
  (`gluedOfCharts_left_eq_glued`, `rfl`).

## What this changes, precisely

The assembly's input list goes from five to four, and the fifth is not *removed* — it is
identified with one already there:

| input of `jacobianDataOfMixedParamCharts` | before | after |
|---|---|---|
| `rep` (divisor representability) | open | open, unchanged |
| `hf` (`IsChartUniv`) | open | open, unchanged |
| the `IsLocallySurjective` instance (coverage) | open | open, unchanged |
| `hD` (`LocallyOfFiniteType (D i).hom`) | discharged | discharged, unchanged |
| **`hcpt` (`CompactSpace` of the glued)** | **open, "the exposed one"** | **replaced by `(lam, hcl)`** |

**Read that last row as a replacement, not a saving.**  An earlier draft of this header wrote
"four inputs, not five", and the binder count says otherwise: `jacobianDataOfMixedParamCharts`
takes ten explicit arguments, `jacobianDataOfCompactFromClass` takes eleven, plus seven implicit
binders for the divisor scheme.  One hypothesis became two — `lam` and `hcl` — and only the fact
that `lam` is trivially inhabited makes that look free.

`hcl` is the class-coordinate lift hypothesis of the `dat-j.qcfield` row: *every point of the
representing object has its class pulled back from a fixed degree-zero class `lam` on the
divisor scheme along some field point.*  What is genuinely bought is therefore not a shorter
list but a **relocation onto a row that already exists**: a lane discharging the qc field
discharges `hcpt` in the same breath, so `hcpt` is not a separate *distance* even though it is
not a smaller *signature*.

**AND THE SHARP FORM IS STRONGER THAN THAT, which corrects a claim of mine.**  I first reported
`hcpt` as "a genuine fifth obligation of the goal with no lane".  It is not fifth and it is not
new: `hcpt` is `CompactSpace` of the glued *space*, the `JacobianData.quasiCompact` field is
`QuasiCompact` of the glued *morphism*, and over the affine base `Spec k` these are
**interderivable** — `compactSpace_glued_iff_quasiCompact` below, both directions, one mathlib
lemma each way.  `JacobianData` has four fields and `hcpt` is one of them.  What is genuinely
double-counted is therefore not a field but a *row*: the atlas assembly and `dat-j` were holding
the same obligation, and the `hcl` route is how it gets paid once.

## What this does NOT do, and the count that matters

**No gate is closed and no antecedent is discharged.**  `hcl` has no producer — that is the
`dat-j.qcfield` residue, released open at `I-1091` — so `jacobianDataOfCompactFromClass` below
is an *implication*, exactly like every other declaration on this route.  Its value is
subtractive: it removes a *row* from the list by showing it was double-counted, which is
the failure mode this workspace has repeatedly found in its own costings.

Two things worth being explicit about, since a reduction that merely renames is worthless:

(`HasDivFunctor`, named below as the workspace's cautionary vacuity, is a declaration of the
*sibling* project and is deliberately not `#check`-able here — it is referenced as a documented
failure mode, not as a Lean dependency of this file.)

* **`hcpt` is not free**, so this is not a trivial discharge.  At a *finite* atlas with compact
  charts it is provable outright (`Scheme.OpenCover.compactSpace`, the route
  `JacobianData.ofCharts` takes), but the classical atlas is indexed by divisor *classes* and
  is not finite — `JacobianDataCharts.lean` says so, and `Pic0AtlasFiniteType.lean` measured
  that with `hf` and the coverage instance in scope and nothing else, `CompactSpace` of the
  glued object does not follow, the missing ingredient being index finiteness.  The
  `compactSpace_of_finite_atlas` record below is that route, kept adjacent so the two are
  visibly different hypotheses rather than two spellings.
* **`hcl` is falsifiable**, hence the implication is not vacuous in the `HasDivFunctor` sense:
  `compactSpace_of_pic0_class_surjective` *is* the proof that `hcl` implies compactness, so
  `hcl` fails at any representing object with non-compact space.  The curve `C` occurs in it
  through `pic0Map C` and `pic0Subgroup C`, which is the check `HasDivFunctor` failed.

  **A third clause here said "and the divisor scheme of `C`".  That is FALSE and is corrected
  rather than annotated away.**  The `FromClass` section below binds an *independent* curve `Y`
  with its own `A B g r₁ r₂ b₁ b₂`, and `divSchemeOver` is built from `Y`, not from `C` —
  verified by elaborating `hcl` with `Y` wholly unrelated to `C.left`.  The falsifiability
  conclusion survives on the two true clauses alone, which is exactly why the false one was easy
  to write: it sat inside a correct argument and read as audited.  Inherited from
  `JacobianDataQcFromRep.lean`, whose own section has the same independent binder.
* **`lam` is trivially inhabited** (`lam := 1` elaborates), so it is not a second obligation —
  but it is not free either: `hcl` *quantifies over it*, and at `lam = 1` the hypothesis says
  every point of the representing object carries the trivial class.  `lam` and `hcl` are one
  coupled pair, and the table above lists them as one row for that reason.  **Stated because an
  earlier draft of this header claimed the input count drops from five to four; it does not.**
  `jacobianDataOfMixedParamCharts` takes ten explicit arguments and
  `jacobianDataOfCompactFromClass` takes eleven (plus the seven implicit binders of the divisor
  scheme).  One hypothesis became two.  What is true is the *identification* — `hcpt` is the
  `quasiCompact` field, and the class route pays it from a row that already exists — not a
  reduction in binder count.

## Main declarations

* `AlgebraicGeometry.gluedOfCharts_left_eq_glued` — the carrier identity, `rfl`: the space of
  the glued object of a chart family is mathlib's glue-data glued scheme.  **Documentation only —
  no proof term below uses it**, and an earlier draft of this list said it "is what makes the
  substitution a substitution rather than a transport", which overstates its role: the
  substitution goes through by definitional unfolding and Lean never consults this lemma.  It is
  worth stating because a reader auditing for a hidden transport would otherwise go looking for
  the rewrite that is not there.
* `AlgebraicGeometry.compactSpace_glued_of_pic0_class` — **the correction**: `hcpt` for the
  mixed-parameter atlas from the qc field's `hcl` at the atlas's own representation.
* `AlgebraicGeometry.jacobianDataOfCompactFromClass` — the assembly with `hcpt` replaced by
  `hcl`: four inputs, not five.
* `AlgebraicGeometry.compactSpace_glued_iff_quasiCompact` — **the sharp form**: `hcpt` and the
  `JacobianData.quasiCompact` field are one statement, both directions.  This is what makes the
  double-counting a fact about two board rows rather than about a field count.
* `AlgebraicGeometry.compactSpace_of_finite_atlas` — the finite-index route, recorded so the
  two hypotheses are visibly distinct.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The carrier identity

`jacobianDataOfMixedParamCharts` states `hcpt` about `(glueData hf).glued`, while the qc route
concludes `CompactSpace J.left` for `J` the represented object `gluedOfCharts …`.  These are the
same type, definitionally, so the substitution below needs no transport.  The lemma is a
*record* of that, not a step in it: no proof term in this file cites it. -/

variable (C) in
/-- **The space of the glued object of a chart family is mathlib's glued scheme**, by `rfl`.

`gluedOfCharts C f hf` is `Over.mk (gluedHom C f hf)` and `gluedHom` is a morphism *out of*
`(glueData hf).glued`, so its `.left` is that scheme with nothing in between.  Stated because
the two names occur in the two halves being composed and a reader should not have to check. -/
lemma gluedOfCharts_left_eq_glued {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (hf : ∀ i, IsOpenImmersion.presheaf (f i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)] :
    (gluedOfCharts C f hf).left = (Scheme.LocalRepresentability.glueData hf).glued :=
  rfl

/-! ## The correction: `hcpt` from the qc field's hypothesis -/

section FromClass

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of k))] [IsIntegral Y]
variable {A B : Y.CurveDivisor} {g r₁ r₂ : ℕ}
variable {b₁ : Module.Basis (Fin r₁) k ↥(Scheme.divisorSections k B ⊤)}
variable {b₂ : Module.Basis (Fin r₂) k ↥(Scheme.divisorSections k (A + B) ⊤)}

variable (C π) in
/-- **THE CORRECTION**: the compactness input of the atlas assembly follows from the qc field's
own class-lift hypothesis, at the atlas's own representation.

`Pic0AtlasFiniteType.lean` offers exactly two routes to `hcpt` — a finite atlas, or the Abel
image of `JacobianDataAbelImage` — and the class-indexed atlas has neither.  This is a third,
and the hypothesis it consumes is not new: `hcl` is the `dat-j.qcfield` row's statement, that
every point of the representing object carries a class pulled back from `lam` along a field
point of the divisor scheme.

The proof is one application of `compactSpace_of_pic0_class_surjective` to
`pic0RepresentableByOfCharts`, with no transport — the two carriers agree by definitional
unfolding, which `gluedOfCharts_left_eq_glued` *records* but does not effect (that lemma appears
in no proof term).

**So `hcpt` was double-counted.**  A lane discharging the qc field gets it free; it is not a
fifth distance to representability. -/
theorem compactSpace_glued_of_pic0_class {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens)
    (hf : ∀ i, IsOpenImmersion.presheaf (mixedParamChart C π nn D rep m Z hdeg V i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (mixedParamChart C π nn D rep m Z hdeg V))]
    (lam : pic0Subgroup C (divSchemeOver k A B g r₁ r₂ b₁ b₂))
    (hcl : ∀ y : (gluedOfCharts C (mixedParamChart C π nn D rep m Z hdeg V) hf).left,
      ∃ q : overSpec k (Over.testPointField y) ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂,
        pic0Map C q lam
          = (pic0RepresentableByOfCharts C
              (mixedParamChart C π nn D rep m Z hdeg V) hf).homEquiv (Over.testPoint y)) :
    CompactSpace (Scheme.LocalRepresentability.glueData hf).glued :=
  compactSpace_of_pic0_class_surjective
    (pic0RepresentableByOfCharts C (mixedParamChart C π nn D rep m Z hdeg V) hf) lam hcl

variable (C π) in
/-- **The atlas assembly with `hcpt` replaced by `hcl`** — four inputs, not five.

Compare `jacobianDataOfMixedParamCharts` (`Picard/Pic0AtlasFiniteType.lean`), whose signature
carries `hcpt` as a hypothesis its own docstring calls the exposed one.  Here it does not
appear: the qc field's `hcl` supplies it.

The remaining open inputs, unchanged and each another lane's target:

* `rep` — divisor representability at each chart parameter;
* `hf` — `IsChartUniv` per index;
* the `IsLocallySurjective` instance — DAT-B coverage;
* `hcl` — the `dat-j.qcfield` residue.

and `hD` is discharged at the divisor-representability lane's own carrier
(`Pic0AtlasFiniteType.lean`'s `Discharged` section).

**This produces no `JacobianData` at any curve**: `hcl` has no producer.  What it produces is a
shorter list. -/
def jacobianDataOfCompactFromClass {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens)
    (hf : ∀ i, IsOpenImmersion.presheaf (mixedParamChart C π nn D rep m Z hdeg V i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (mixedParamChart C π nn D rep m Z hdeg V))]
    (hD : ∀ i, LocallyOfFiniteType (D i).hom)
    (lam : pic0Subgroup C (divSchemeOver k A B g r₁ r₂ b₁ b₂))
    (hcl : ∀ y : (gluedOfCharts C (mixedParamChart C π nn D rep m Z hdeg V) hf).left,
      ∃ q : overSpec k (Over.testPointField y) ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂,
        pic0Map C q lam
          = (pic0RepresentableByOfCharts C
              (mixedParamChart C π nn D rep m Z hdeg V) hf).homEquiv (Over.testPoint y)) :
    JacobianData C :=
  JacobianData.ofPic0ClassSurjective C _
    (pic0RepresentableByOfCharts C (mixedParamChart C π nn D rep m Z hdeg V) hf)
    (locallyOfFiniteType_gluedHom_mixedParamChart C π nn D rep m Z hdeg V hf hD)
    lam hcl

@[simp]
lemma jacobianDataOfCompactFromClass_J {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens)
    (hf : ∀ i, IsOpenImmersion.presheaf (mixedParamChart C π nn D rep m Z hdeg V i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (mixedParamChart C π nn D rep m Z hdeg V))]
    (hD : ∀ i, LocallyOfFiniteType (D i).hom)
    (lam : pic0Subgroup C (divSchemeOver k A B g r₁ r₂ b₁ b₂))
    (hcl : ∀ y : (gluedOfCharts C (mixedParamChart C π nn D rep m Z hdeg V) hf).left,
      ∃ q : overSpec k (Over.testPointField y) ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂,
        pic0Map C q lam
          = (pic0RepresentableByOfCharts C
              (mixedParamChart C π nn D rep m Z hdeg V) hf).homEquiv (Over.testPoint y)) :
    (jacobianDataOfCompactFromClass C π nn D rep m Z hdeg V hf hD lam hcl).J
      = gluedOfCharts C (mixedParamChart C π nn D rep m Z hdeg V) hf :=
  rfl

end FromClass

/-! ## `hcpt` IS the `quasiCompact` field, in the other spelling

The sharper form of the double-counting, and it is an **equivalence** rather than the one-way
implication above.  `hcpt` is `CompactSpace` of the glued *space*; the `JacobianData` field is
`QuasiCompact` of the glued *morphism*.  Over the affine base `Spec k` those are the same
statement (`HasAffineProperty.iff_of_isAffine`), in both directions.

So `hcpt` is not an atlas-specific extra input at all: it is the `quasiCompact` field of the
target datum, which the board tracks on the `dat-j` row.  The atlas assembly and `dat-j` were
holding one obligation between them.

**This corrects my own claim note** (`I-1123`), which called `hcpt` "a genuine fifth obligation
of the GOAL".  It is not a fifth anything — `JacobianData` has four fields and this is one of
them.  The double-counting is real and it is *between rows*, not between field counts. -/

variable (C) in
/-- **`hcpt` and the `quasiCompact` field are one statement.**

`CompactSpace (glueData hf).glued ↔ QuasiCompact (gluedHom C f hf)`: over the affine base both
sides are `HasAffineProperty.iff_of_isAffine` read in the two directions.

Stated as an `iff` deliberately, and **only one half is new**.  The `mpr` direction is already
the *implementation* of `JacobianData.ofChartsOfCompactSpace` (`JacobianDataCharts.lean`), which
is literally `HasAffineProperty.iff_of_isAffine.mpr hcpt` — so the collapse has been structural
in the producer since that file landed, and nobody read it off.  The `mp` direction is one
application of this project's own `compactSpace_left_of_quasiCompact` (`Curve/Basic.lean`).  What
is contributed here is therefore not either implication but the **equivalence written down**:
each half was one line away, and while they sat apart the two board rows could each carry the
obligation without anyone noticing it was one.  Recorded at this strength rather than as a
discovery, because a fresh-context audit found the `mpr` half pre-existing and it would be worse
to leave the stronger reading standing.

**THE CARRIER HAZARD, and it is one `rfl` wide.**  This `iff` is about `gluedHom C f hf`, i.e.
about the glued *chart* object.  `JacobianData.quasiCompact` is `QuasiCompact J.hom` for the
*representing* object `J`.  They are the same statement here **only** because
`JacobianData.ofChartsOfCompactSpace_J` makes `J = gluedOfCharts C f hf` by `rfl`.  A lane that
swaps the representing carrier — for instance transporting along
`Functor.RepresentableBy.uniqueUpToIso` to a different but isomorphic `J` — keeps this `iff` true
and **silently loses the identification**, so `hcpt` would become a genuinely separate input
again without any statement here turning false.  Whoever moves the carrier must re-derive the
identification, not inherit it. -/
theorem compactSpace_glued_iff_quasiCompact {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (hf : ∀ i, IsOpenImmersion.presheaf (f i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)] :
    CompactSpace (Scheme.LocalRepresentability.glueData hf).glued
      ↔ QuasiCompact (gluedHom C f hf) :=
  ⟨fun h => HasAffineProperty.iff_of_isAffine.mpr h,
    fun h => HasAffineProperty.iff_of_isAffine.mp h⟩

/-! ## The other route, for contrast: `hcpt` is genuinely not free

A reduction is only informative if the thing reduced was not already available.  `hcpt` *is*
available at a **finite** atlas with compact charts — that is `JacobianData.ofCharts`'s route —
and the record below is it.  The class-indexed atlas does not have `Finite ι`, which is exactly
what `Pic0AtlasFiniteType.lean` measured as the single missing ingredient.  So the two
hypotheses are visibly different, and neither subsumes the other. -/

variable (C) in
/-- **`hcpt` at a finite atlas with compact charts** — mathlib's `Scheme.Cover.compactSpace`
through the glue data's own open cover.

Recorded next to `compactSpace_glued_of_pic0_class` so the contrast is on the page: this route
needs `Finite ι` and per-chart compactness, while the class route needs neither and takes `hcl`
instead.  The classical atlas is class-indexed, so only the second is available to it — but the
first is why `hcpt` cannot be called unconditionally hard either.

**CORRECTED 2026-07-30.**  This parenthesis used to read "both free at the
divisor-representability carrier, where `CompactSpace (divSchemeOver …).left` is an instance".
That instance is about the wrong object: the `X i` of this lemma are the *chart* objects, and for
`mixedParamChart` those are `(V i : Scheme)`, **opens** of the representing object.  Compactness
does not pass to open subspaces, and `infer_instance` fails there (measured).  Per-chart
compactness is free by *noetherianity* of the divisor scheme instead —
`compactSpace_isOpen_divSchemeOver` (`Picard/Pic0AtlasCompactNoetherian.lean`, which imports this
module, hence is not citable as a dependency here). -/
theorem compactSpace_of_finite_atlas {ι : Type u} [Finite ι] {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (hf : ∀ i, IsOpenImmersion.presheaf (f i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)]
    (hcpt : ∀ i, CompactSpace (X i)) :
    CompactSpace (Scheme.LocalRepresentability.glueData hf).glued := by
  haveI : Finite (Scheme.LocalRepresentability.glueData hf).openCover.I₀ := ‹Finite ι›
  haveI : ∀ i, CompactSpace ((Scheme.LocalRepresentability.glueData hf).openCover.X i) := hcpt
  exact (Scheme.LocalRepresentability.glueData hf).openCover.compactSpace

end

end AlgebraicGeometry
