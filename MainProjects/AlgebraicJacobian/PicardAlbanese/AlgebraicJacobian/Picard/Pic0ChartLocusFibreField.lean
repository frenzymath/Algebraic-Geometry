/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyH1Locus

/-!
# CHART-U(b) gap-2, the chartLocus-free core — fibre-field invariance of witness
h¹-vanishing (`informal/w4-datb-worksheet.md` §1.6 transport (ii), I-0252 gap 2)

CHART-U(b)'s transport (ii) (the "one `IsOpenMap` application", `Pic0ChartLocusOpen`
keystones 2/3) pushes the engine's open witness locus from the étale carrier `Spec B`
down to the test base `Spec A`.  Its remaining mathematical content (I-0252 gap 2) is
the *fibre-field invariance* that identifies the preimage of the base locus with the
carrier locus: for a prime `q` of the carrier over `p`, the residue-field extension
`κ(q)/κ(p)` is separable (étale/étale-plus carrier) and must **preserve** the witness
h¹-vanishing of the fibre class.

That content is `chartLocus`-free (I-0252's phrasing through the still-undefined
`chartLocus`, DAT-C C9, is pure plumbing on top) and is landed here in the **witness
form** `BasicOpenCocycleDatum.isOpen_setOf_exists_witness_h1_vanishing`
(`Pic0ChartLocusOpen`) uses.  The heart is a single module fact:

* `AlgebraicGeometry.subsingleton_tensorProduct_field_ext_iff` — for an `S`-module `H`
  and a field extension `L → L'` in the `S`-tower, `H ⊗[S] L` is subsingleton iff
  `H ⊗[S] L'` is.  Going up is `0 ⊗ = 0`; coming down is the faithful flatness of the
  (nonzero) field extension.  **Separability is not needed** — every field extension is
  faithfully flat; it is the geometric packaging (étale carrier) that makes the residue
  extensions separable, not the transfer.

Read through the two-way datum dictionary
`BasicOpenCocycleDatum.subsingleton_h1_tensor_iff_exists_witness` (C1, GAP-6) — under
which the witness predicate at a field `L` is exactly the engine's complex-form fibre
condition `Subsingleton ((datumPair D).H1 ⊗[B] L)` — this gives:

* `BasicOpenCocycleDatum.HasWitnessH1Vanishing` — the field-parametrised witness
  predicate; for `L = κ(q)` it is membership of `q` in the keystone-1 locus.
* `BasicOpenCocycleDatum.hasWitnessH1Vanishing_iff_of_fieldExtension` — **the gap-2
  core**: witness h¹-vanishing of `D` at `L` transfers to and from `L'` for any field
  extension `L → L'` in the `k`/`B` tower.
* `BasicOpenCocycleDatum.hasWitnessH1Vanishing_iff_of_separable` — the separable
  specialisation the CHART-U(b) consumer names (`Algebra.IsSeparable`).
* `BasicOpenCocycleDatum.hasWitnessH1Vanishing_congr_of_cechPicClass_eq` — the fixed-
  field class-intrinsicity (V1a): the witness predicate depends only on the mapped fibre
  class, so two data with equal fibre class at `L` have the same predicate.

## What the CHART-U(b) / C9 assembly consumes and the residual (I-0252 gap 2)

The `comap`-preimage identity keystone 3 needs, `comap f ⁻¹'(chartLocus_A) = locus_B`,
reduces pointwise (for `q` over `p`, `κ(q)/κ(p)` separable) to two links:
`hasWitnessH1Vanishing_iff_of_fieldExtension` (the `κ(p) → κ(q)` field transfer, landed
here) composed with `hasWitnessH1Vanishing_congr_of_cechPicClass_eq` at the fixed field
`κ(q)` (landed here).  The **residual** is the input to the latter — the shifted-datum
class identity `map (relCurveMap … κ(q)) D_A.cechPicClass = map (relCurveMap … κ(q))
D_B.cechPicClass` (I-0252 gap 1, the Σ/θ naturality) — and the `chartLocus` definition
itself (DAT-C C9).  Both are divRep/C9-gated; neither is a mathematical wall on the
invariance itself, which is complete.
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

/-! ## The module-theoretic core -/

/-- **Base change of a module along a field extension preserves triviality**: for an
`S`-module `H` and a field extension `L → L'` inside the `S`-tower, `H ⊗[S] L` is
subsingleton iff `H ⊗[S] L'` is.

Going up is `0 ⊗ = 0`; coming down is the faithful flatness of the (nonzero) field
extension `L → L'` (`Module.FaithfullyFlat.lTensor_reflects_triviality`), read across the
base-change-in-stages equivalence `(TensorProduct.AlgebraTensorModule.cancelBaseChange)`.
**Separability is not used** — every field extension is faithfully flat. -/
theorem subsingleton_tensorProduct_field_ext_iff
    {S L L' H : Type u} [CommRing S] [Field L] [Field L'] [Algebra S L] [Algebra S L']
    [Algebra L L'] [IsScalarTower S L L'] [AddCommGroup H] [Module S H] :
    Subsingleton (H ⊗[S] L) ↔ Subsingleton (H ⊗[S] L') := by
  have e := TensorProduct.AlgebraTensorModule.cancelBaseChange S L L' L' H
  rw [(TensorProduct.comm S H L).toEquiv.subsingleton_congr,
      (TensorProduct.comm S H L').toEquiv.subsingleton_congr,
      ← e.toEquiv.subsingleton_congr]
  exact ⟨fun _ => inferInstance,
    fun _ => Module.FaithfullyFlat.lTensor_reflects_triviality L L' (L ⊗[S] H)⟩

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-! ## The witness predicate as a function of the fibre field -/

/-- **The chart-membership witness predicate at a field `L`** — the field-parametrised
form of the set of `BasicOpenCocycleDatum.isOpen_setOf_exists_witness_h1_vanishing`
(`Pic0ChartLocusOpen`): the fibre class of `D` at `L` admits an effective witness divisor
with vanishing `H¹`.  For `L = q.asIdeal.ResidueField` this is definitionally membership
of `q` in the keystone-1 witness locus. -/
def BasicOpenCocycleDatum.HasWitnessH1Vanishing (D : BasicOpenCocycleDatum C B π)
    (L : Type u) [Field L] [Algebra k L] [Algebra B L] [IsScalarTower k B L] : Prop :=
  ∃ W : ((C ⊗ overSpec k L).left).CurveDivisor,
    Scheme.CurveDivisor.picClass L W
        = Scheme.CechPic.map (relCurveMap C B L) D.cechPicClass
      ∧ Subsingleton (Sheaf.HModule ((C ⊗ overSpec k L).left.divisorSheaf L W) 1)

/-- The witness predicate is the engine's complex-form fibre condition
`Subsingleton ((datumPair D).H1 ⊗[B] L)`, via the two-way datum dictionary
`subsingleton_h1_tensor_iff_exists_witness` (C1, GAP-6). -/
theorem BasicOpenCocycleDatum.hasWitnessH1Vanishing_iff_subsingleton
    (D : BasicOpenCocycleDatum C B π) (L : Type u) [Field L] [Algebra k L] [Algebra B L]
    [IsScalarTower k B L] :
    D.HasWitnessH1Vanishing L ↔ Subsingleton ((datumPair D).H1 ⊗[B] L) :=
  (D.subsingleton_h1_tensor_iff_exists_witness L).symm

/-! ## The fibre-field invariance (the gap-2 core) -/

/-- **CHART-U(b) gap-2 core — fibre-field invariance of witness h¹-vanishing**: for a
pinned datum `D` over the affine base `B` and a field extension `L → L'` inside the
`k`/`B` tower (the residue-field seam `κ(p) → κ(q)` of a carrier map `comap f`), the
witness h¹-vanishing of `D` at `L` transfers to and from `L'`.

Both sides are, via the datum dictionary, `Subsingleton ((datumPair D).H1 ⊗[B] ·)`, and
that transfers along the (faithfully flat) field extension `L → L'`
(`subsingleton_tensorProduct_field_ext_iff`).  In particular this covers the separable
residue-field extensions of an étale/étale-plus carrier map. -/
theorem BasicOpenCocycleDatum.hasWitnessH1Vanishing_iff_of_fieldExtension
    (D : BasicOpenCocycleDatum C B π)
    (L L' : Type u) [Field L] [Field L'] [Algebra k L] [Algebra k L']
    [Algebra B L] [Algebra B L'] [IsScalarTower k B L] [IsScalarTower k B L']
    [Algebra L L'] [IsScalarTower B L L'] :
    D.HasWitnessH1Vanishing L ↔ D.HasWitnessH1Vanishing L' := by
  rw [D.hasWitnessH1Vanishing_iff_subsingleton L,
      D.hasWitnessH1Vanishing_iff_subsingleton L']
  exact subsingleton_tensorProduct_field_ext_iff

/-- **The separable specialisation the CHART-U(b) transport (ii) names** (I-0252 gap 2):
for a **separable** residue-field extension `L → L'` (`Algebra.IsSeparable`, the case of
an étale/étale-plus carrier map), witness h¹-vanishing of `D` transfers between `L` and
`L'`.  Separability is recorded to name the intended consumer; the transfer holds for any
field extension (`hasWitnessH1Vanishing_iff_of_fieldExtension`). -/
theorem BasicOpenCocycleDatum.hasWitnessH1Vanishing_iff_of_separable
    (D : BasicOpenCocycleDatum C B π)
    (L L' : Type u) [Field L] [Field L'] [Algebra k L] [Algebra k L']
    [Algebra B L] [Algebra B L'] [IsScalarTower k B L] [IsScalarTower k B L']
    [Algebra L L'] [IsScalarTower B L L'] [Algebra.IsSeparable L L'] :
    D.HasWitnessH1Vanishing L ↔ D.HasWitnessH1Vanishing L' :=
  D.hasWitnessH1Vanishing_iff_of_fieldExtension L L'

/-! ## Fixed-field class-intrinsicity (the other half the `comap` identity needs) -/

/-- **Class-intrinsicity of the witness predicate at a fixed field** (V1a): the witness
h¹-vanishing predicate depends only on the mapped fibre class
`Scheme.CechPic.map (relCurveMap C B L) D.cechPicClass`, so two data — over possibly
different bases `B`, `B'` — whose fibre classes at `L` agree have the same witness
predicate at `L`.

Together with `hasWitnessH1Vanishing_iff_of_fieldExtension` (the `κ(p) → κ(q)` transfer)
this is exactly what the CHART-U(b) `comap`-preimage identity reduces to at C9-time; the
one residual input is the shifted-datum class identity of I-0252 gap 1 (the Σ/θ
naturality), which is divRep-gated. -/
theorem BasicOpenCocycleDatum.hasWitnessH1Vanishing_congr_of_cechPicClass_eq
    {B' : Type u} [CommRing B'] [Algebra k B']
    (D : BasicOpenCocycleDatum C B π) (D' : BasicOpenCocycleDatum C B' π)
    (L : Type u) [Field L] [Algebra k L] [Algebra B L] [Algebra B' L]
    [IsScalarTower k B L] [IsScalarTower k B' L]
    (hcl : Scheme.CechPic.map (relCurveMap C B L) D.cechPicClass
        = Scheme.CechPic.map (relCurveMap C B' L) D'.cechPicClass) :
    D.HasWitnessH1Vanishing L ↔ D'.HasWitnessH1Vanishing L := by
  simp only [BasicOpenCocycleDatum.HasWitnessH1Vanishing, hcl]

end AlgebraicGeometry
