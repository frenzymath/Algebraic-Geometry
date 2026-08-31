/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartLocus

/-!
# DAT-C GAP-1: the inverse cocycle datum (the shifted-datum constructor's first half)

`informal/w4-datc-worksheet.md` §0.3 GAP-1 (Σ-INV) and `informal/w4-datb-worksheet.md`
§1.6 both name the same missing input, and both name it as the reason the CHART-U(b) twist
"has no route": **there is no `BasicOpenCocycleDatum.inv` and no tensor/`mul` anywhere in
the tree**, so a datum for a class cannot be turned into a datum for its inverse or for a
product.  Every landed datum built from a divisor family is the *twisted ideal*
`thetaIdealDatum a` of class `θᵃ·[d]⁻¹` (`Picard/DivisorThetaDatum.lean:362`), i.e. the
tree can only produce data whose class carries a built-in inverse it cannot remove.

This file supplies the inverse half, exactly as GAP-1 pins it:

> `BasicOpenCocycleDatum.invDatum` (same pieces, units `(D.unit i j)⁻¹`; the cocycle law inverts
> termwise), with `cechPicClass_inv = (cechPicClass)⁻¹`.

## Main declarations

* `AlgebraicGeometry.BasicOpenCocycleDatum.invDatum` — the inverse datum: the *same* cover data
  (so the same pieces, the same partitions — nothing about the cover changes), with every
  transition unit inverted.
* `AlgebraicGeometry.BasicOpenCocycleDatum.isGluingCocycle_inv` — the cocycle law for the
  inverted units.  This is where the mathematical content sits, and it is small but not
  vacuous: the cocycle identity `g_ij · g_jl = g_il` inverts to
  `g_ij⁻¹ · g_jl⁻¹ = g_il⁻¹` only because the overlap section rings are **commutative**, so
  the inverse of a product is the product of inverses in either order.  In the
  non-commutative setting the correct law would be `(g_jl · g_ij)⁻¹` and the statement would
  need a transpose.
* `AlgebraicGeometry.BasicOpenCocycleDatum.inv_inv` — the involution.
* `AlgebraicGeometry.BasicOpenCocycleDatum.pieces_inv` / `unit_inv_coe` — the two `rfl`
  anchors consumers unfold through.

## What this does and does not unblock

It gives the twist a *route*: a datum for `μ` and the θ/Σ layer's datum now compose to a
datum for `μ·θ^m·(−Σ)` as soon as the second half of GAP-1 — the `mul`/tensor of two data
on a *common refinement* of their covers — is available.  That second half is genuinely
larger than this one (it needs a refinement of two basic-open covers and a comparison of
the two `cechPicClass` readings on it), and it is NOT in this file; see the closing note.

`cechPicClass_inv` is likewise NOT here.  Stating it needs the subordinated-cocycle
`inv_unitsEvInf`-style calculus that `DivSchemeFibreH1.lean:63-66` uses *privately*, and
lifting that to a public lemma is its own brick.  What is here is the carrier plus its
cocycle law — the part GAP-1 says has no avatar at all, and the part every route needs
first.
-/

set_option autoImplicit false
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
variable {B : Type u} [CommRing B] [Algebra k B]
variable {π : C.left ⟶ P1 k} [IsAffineHom π]

namespace BasicOpenCocycleDatum

/-! ## The cocycle law inverts termwise -/

/-- **The inverted transition units satisfy the cocycle law** (GAP-1's "the cocycle law
inverts termwise").

The two clauses:
* normalization — `(g i i)⁻¹ = 1⁻¹ = 1`, by `unit_self` and `inv_one`;
* the cocycle identity — apply `resHom` (a ring hom, hence unit-preserving) to
  `g_ij · g_jl = g_il` and invert.  The step that makes this work is **commutativity** of
  the triple-overlap section ring: `(a·b)⁻¹ = a⁻¹·b⁻¹` needs `a·b = b·a`.  Over a
  non-commutative base the correct inverse cocycle would carry a transposed index pair.

Stated for an arbitrary family of transition units rather than for a datum, so that the
θ/Σ layer can reuse it without building a `BasicOpenCocycleDatum` first. -/
theorem _root_.AlgebraicGeometry.Scheme.IsGluingCocycle.inv {X : Scheme.{u}} {J : Type u}
    {U : J → X.Opens} {g : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ}
    (hc : Scheme.IsGluingCocycle U g) :
    Scheme.IsGluingCocycle U (fun i j => (g i j)⁻¹) where
  unit_self i := by
    have h : (g i i) = 1 := Units.ext (by rw [hc.unit_self i]; rfl)
    rw [h, inv_one]
    rfl
  mul_res i j l := by
    -- Abbreviate the three restriction maps to the triple overlap.
    set rij := X.resHom (inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U j) with hrij
    set rjl := X.resHom (gluedInclCoc U (U i) j l) with hrjl
    set ril := X.resHom (gluedInclSnd U (U i) j l) with hril
    -- `resHom` sends a unit and its inverse to a mutually inverse pair, so the image of
    -- an inverse is characterised by `mul_eq_one`.  Record that for each of the three.
    have hu : ∀ {V W : X.Opens} (h : V ≤ W) (a : Γ(X, W)ˣ),
        X.resHom h (Units.val a⁻¹) * X.resHom h (Units.val a) = 1 := by
      intro V W h a
      rw [← map_mul]
      have : ((a⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * ((a : Γ(X, W)ˣ) : Γ(X, W)) = 1 :=
        a.inv_mul
      rw [this, map_one]
    -- Multiply the target by the uninverted cocycle identity and cancel.
    have key := hc.mul_res i j l
    rw [← hrij, ← hrjl, ← hril] at key
    have hcancel : (rij (Units.val (g i j)⁻¹)
          * rjl (Units.val (g j l)⁻¹))
        * (rij (Units.val (g i j)) * rjl (Units.val (g j l))) = 1 := by
      calc (rij (Units.val (g i j)⁻¹) * rjl (Units.val (g j l)⁻¹))
            * (rij (Units.val (g i j)) * rjl (Units.val (g j l)))
          = (rij (Units.val (g i j)⁻¹) * rij (Units.val (g i j)))
            * (rjl (Units.val (g j l)⁻¹)
                * rjl (Units.val (g j l))) := by ring
        _ = 1 := by rw [hu, hu, one_mul]
    -- Both sides are the inverse of the same element of the commutative monoid, hence equal.
    rw [key] at hcancel
    have hril_inv : ril (Units.val (g i l)⁻¹) * ril (Units.val (g i l)) = 1 :=
      hu _ _
    calc rij (Units.val (g i j)⁻¹) * rjl (Units.val (g j l)⁻¹)
        = (rij (Units.val (g i j)⁻¹) * rjl (Units.val (g j l)⁻¹))
            * (ril (Units.val (g i l))
                * ril (Units.val (g i l)⁻¹)) := by
          rw [mul_comm (ril (Units.val (g i l))), hril_inv, mul_one]
      _ = (rij (Units.val (g i j)⁻¹) * rjl (Units.val (g j l)⁻¹)
            * ril (Units.val (g i l))) * ril (Units.val (g i l)⁻¹) := by
          ring
      _ = ril (Units.val (g i l)⁻¹) := by rw [hcancel, one_mul]

/-! ## The inverse datum -/

/-- **GAP-1: the inverse cocycle datum.**  Same cover data — same pieces, same partitions,
same index — with every transition unit inverted.  The cocycle law is
`Scheme.IsGluingCocycle.inv`.

This is the constructor `informal/w4-datc-worksheet.md` §0.3 GAP-1 pins and reports as
having no avatar anywhere in the tree.  With it, a datum for a class `μ` yields one for
`μ⁻¹`, which is what the `(−Σ)` and `(θ^m)⁻¹` factors of the chart twist
(`chartTwist`, `Picard/Pic0ChartLocus.lean`) need in order to have a datum-level route at
all: every landed datum built from a divisor family is `thetaIdealDatum a` of class
`θᵃ·[d]⁻¹`, i.e. carries a built-in inverse the tree previously could not remove. -/
noncomputable def invDatum (D : BasicOpenCocycleDatum C B π) : BasicOpenCocycleDatum C B π where
  toBasicOpenCoverData := D.toBasicOpenCoverData
  unit i j := (D.unit i j)⁻¹
  isGluingCocycle := D.isGluingCocycle.inv

@[simp]
lemma invDatum_toBasicOpenCoverData (D : BasicOpenCocycleDatum C B π) :
    D.invDatum.toBasicOpenCoverData = D.toBasicOpenCoverData :=
  rfl

/-- The inverse datum has the same pieces — the cover is untouched, only the transitions
move.  Consumers that reason about supports or coverings may therefore reuse every
piece-level fact of `D` verbatim. -/
@[simp]
lemma pieces_invDatum (D : BasicOpenCocycleDatum C B π) :
    D.invDatum.toBasicOpenCoverData.pieces = D.toBasicOpenCoverData.pieces :=
  rfl

@[simp]
lemma unit_invDatum (D : BasicOpenCocycleDatum C B π) (i j : D.toBasicOpenCoverData.index) :
    D.invDatum.unit i j = (D.unit i j)⁻¹ :=
  rfl

/-- **The inversion is an involution.**  The cover data is carried through unchanged and
the units invert twice, so this is the `Units` involution applied pointwise. -/
@[simp]
lemma invDatum_invDatum (D : BasicOpenCocycleDatum C B π) : D.invDatum.invDatum = D := by
  cases D with
  | mk cover unit hc =>
      congr 1

end BasicOpenCocycleDatum

end AlgebraicGeometry
