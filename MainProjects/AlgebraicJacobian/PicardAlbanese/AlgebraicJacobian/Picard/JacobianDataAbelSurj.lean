/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianDataAbelImage

/-!
# DJ-1, the topological half: point surjectivity from residue-field lifts

`Picard/JacobianDataAbelImage.lean` reduced DAT-J's quasi-compactness field to a single
statement, `Function.Surjective abel.base` — *step 3* of `informal/w4-datj-worksheet.md`
§2.2, the node's one honest brick.  §2.3 describes the argument for it in the language the
Picard theory supplies: *every field point of `J.left` is a degree-zero class over its
residue field, shift it by `fiberTwist`, take an effective representative, and that
representative is a `DivScheme`-point hitting the original point.*

That argument produces, for a point `y`, a **morphism** `Spec κ(y) ⟶ DivScheme g` — not an
element of the fibre of `abel.base` over `y`.  Nothing in the tree converted the first into
the second, and it is not bookkeeping that can be skipped: the target of DJ-1 is a statement
about the underlying *topological* map, while everything the Picard side produces is a
morphism of schemes.

This file supplies exactly that conversion, and nothing else:

> `surjective_of_forall_exists_residueField_lift` — if for every `y : Y` some
> `q : Spec (Y.residueField y) ⟶ X` satisfies `q ≫ f = Y.fromSpecResidueField y`, then
> `f.base` is surjective.

The proof is `Scheme.range_fromSpecResidueField` (mathlib): the range of
`Y.fromSpecResidueField y` is `{y}`, and `Spec κ(y)` is nonempty because `κ(y)` is a field,
so any point of `Spec κ(y)` maps into the fibre.  Composed with the DJ-0 lemmas this gives
the Jacobian datum producers in the shape the classical argument actually delivers: a
*per-point lift*, which is what `exists_effective_of_picClass` hands back.

## Main declarations

* `AlgebraicGeometry.surjective_of_forall_exists_residueField_lift` — the conversion.
  Pure scheme topology; no curve, no Picard functor, no divisor scheme.
* `AlgebraicGeometry.quasiCompact_of_forall_residueField_lift_from_divScheme` — DJ-1's qc
  step from per-point lifts.
* `AlgebraicGeometry.JacobianData.ofAbelLifts` and
  `AlgebraicGeometry.JacobianData.ofChartsOfAbelLifts` — the two `JacobianData` producers
  with the surjectivity hypothesis replaced by per-point lifts.

## What this does NOT do

It produces no lift.  Producing one is the divRep-gated mathematics of §2.3 (the
`fiberTwist` shift plus `exists_effective_of_picClass`, which must stay Challenge-free per
§0.5 — `riemann_inequality`, never `riemann_inequality_curve`).  What changes is the shape
of that obligation: a lift *per point*, stated with no reference to `Function.Surjective`,
instead of a global surjectivity claim about a topological map.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ## The conversion: per-point lifts give surjectivity -/

section Topology

variable {X Y : Scheme.{u}}

/-- **Per-point residue-field lifts give point surjectivity.**  If every point `y` of `Y`
admits a morphism `q : Spec κ(y) ⟶ X` with `q ≫ f = Y.fromSpecResidueField y`, then the
underlying map of `f` is surjective.

`Spec κ(y)` is nonempty (a field is nontrivial), and the range of `Y.fromSpecResidueField y`
is `{y}` (mathlib `Scheme.range_fromSpecResidueField`), so the image under `q` of any point
of `Spec κ(y)` lies in the fibre of `f` over `y`.

This is the missing link between what the Picard side produces and what DAT-J's
quasi-compactness field consumes: `exists_effective_of_picClass` yields a *morphism* out of
a residue field, while `quasiCompact_of_surjective` wants a surjection of topological
spaces. -/
theorem surjective_of_forall_exists_residueField_lift (f : X ⟶ Y)
    (h : ∀ y : Y, ∃ q : Spec (Y.residueField y) ⟶ X,
      q ≫ f = Y.fromSpecResidueField y) :
    Function.Surjective f.base := by
  intro y
  obtain ⟨q, hq⟩ := h y
  -- a field is nontrivial, so `Spec κ(y)` has a point
  obtain ⟨s⟩ := (inferInstance : Nonempty (PrimeSpectrum (Y.residueField y)))
  refine ⟨q.base s, ?_⟩
  have hs : (q ≫ f).base s = (Y.fromSpecResidueField y).base s := by rw [hq]
  rw [Scheme.fromSpecResidueField_apply] at hs
  exact hs

end Topology

/-! ## DJ-1's quasi-compactness step from per-point lifts -/

section Qc

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
variable (A B : X.CurveDivisor) (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k ↥(Scheme.divisorSections k B ⊤))
variable (b₂ : Module.Basis (Fin r₂) k ↥(Scheme.divisorSections k (A + B) ⊤))

/-- **DJ-1's quasi-compactness step, from per-point lifts** (w4-datj §2.2 with step 3 in
the shape §2.3 delivers it): if every point of the Jacobian-to-be receives a
`DivScheme g`-valued lift of its residue-field point, the structure morphism is
quasi-compact.

This composes `surjective_of_forall_exists_residueField_lift` with DJ-0's
`quasiCompact_of_surjective_from_divScheme`; the compact source is DD-Q's
`compactSpace_divScheme` instance, and the base is affine. -/
theorem quasiCompact_of_forall_residueField_lift_from_divScheme
    (J : Over (Spec (CommRingCat.of k)))
    (abel : DivScheme k A B g r₁ r₂ b₁ b₂ ⟶ J.left)
    (hlift : ∀ y : J.left, ∃ q : Spec (J.left.residueField y) ⟶
      DivScheme k A B g r₁ r₂ b₁ b₂,
      q ≫ abel = J.left.fromSpecResidueField y) :
    QuasiCompact J.hom :=
  quasiCompact_of_surjective_from_divScheme A B g r₁ r₂ b₁ b₂ J abel
    (surjective_of_forall_exists_residueField_lift abel hlift)

end Qc

/-! ## The `JacobianData` producers -/

section Package

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
variable {A B : X.CurveDivisor} {g r₁ r₂ : ℕ}
variable {b₁ : Module.Basis (Fin r₁) k ↥(Scheme.divisorSections k B ⊤)}
variable {b₂ : Module.Basis (Fin r₂) k ↥(Scheme.divisorSections k (A + B) ⊤)}

/-- **DJ-2 against per-point lifts**: the pinned Jacobian datum from a representation of
the degree-zero Picard functor, its locally-of-finite-type certificate, and a
`DivScheme g`-valued lift of every residue-field point of `J.left`.

`JacobianData.ofAbelImage` asks for `Function.Surjective abel.base`; this asks for the
per-point lifts the classical argument produces, which is the same input one step earlier. -/
noncomputable def JacobianData.ofAbelLifts (J : Over (Spec (.of k)))
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (hlft : LocallyOfFiniteType J.hom)
    (abel : DivScheme k A B g r₁ r₂ b₁ b₂ ⟶ J.left)
    (hlift : ∀ y : J.left, ∃ q : Spec (J.left.residueField y) ⟶
      DivScheme k A B g r₁ r₂ b₁ b₂,
      q ≫ abel = J.left.fromSpecResidueField y) :
    JacobianData C :=
  JacobianData.ofAbelImage C J rep hlft abel
    (surjective_of_forall_exists_residueField_lift abel hlift)

@[simp]
lemma JacobianData.ofAbelLifts_J (J : Over (Spec (.of k)))
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (hlft : LocallyOfFiniteType J.hom)
    (abel : DivScheme k A B g r₁ r₂ b₁ b₂ ⟶ J.left)
    (hlift : ∀ y : J.left, ∃ q : Spec (J.left.residueField y) ⟶
      DivScheme k A B g r₁ r₂ b₁ b₂,
      q ≫ abel = J.left.fromSpecResidueField y) :
    (JacobianData.ofAbelLifts C J rep hlft abel hlift).J = J :=
  rfl

end Package

/-! ## The chart-atlas form -/

section Charts

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {ι : Type u} {Xc : ι → Scheme.{u}}
variable (f : ∀ i, yoneda.obj (Xc i) ⟶ (pic0SigmaSheaf C).1)
variable (hf : ∀ i, IsOpenImmersion.presheaf (f i))
variable [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
variable {A B : X.CurveDivisor} {g r₁ r₂ : ℕ}
variable {b₁ : Module.Basis (Fin r₁) k ↥(Scheme.divisorSections k B ⊤)}
variable {b₂ : Module.Basis (Fin r₂) k ↥(Scheme.divisorSections k (A + B) ⊤)}

/-- **The atlas producer against per-point lifts** — the one critical-path §7.5 needs, since
the chart index is infinite and `CompactSpace` of the glued object is genuinely
a-posteriori.  Per-point residue-field lifts of the Abel morphism supply it. -/
noncomputable def JacobianData.ofChartsOfAbelLifts
    (hlft : ∀ i, LocallyOfFiniteType (chartHom C f i))
    (abel : DivScheme k A B g r₁ r₂ b₁ b₂ ⟶ (gluedOfCharts C f hf).left)
    (hlift : ∀ y : (gluedOfCharts C f hf).left,
      ∃ q : Spec ((gluedOfCharts C f hf).left.residueField y) ⟶
        DivScheme k A B g r₁ r₂ b₁ b₂,
        q ≫ abel = (gluedOfCharts C f hf).left.fromSpecResidueField y) :
    JacobianData C :=
  JacobianData.ofChartsOfAbelImage C f hf hlft abel
    (surjective_of_forall_exists_residueField_lift abel hlift)

end Charts

end AlgebraicGeometry
