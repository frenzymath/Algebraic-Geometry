/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffCover
import AlgebraicJacobian.Picard.EffectivityPieces

/-!
# Base change of sections on an ARBITRARY affine open (R2, human decision I-0492)

The section-level input the widened base-change layer needs, in the `relCurve`/`relCurveMap`
spelling the divisor layer uses.

## Why this file exists rather than reusing the chart-typed route

`DivisorFamilyPullback.lean` reaches an affine piece **through its pinned chart**:
`relTermBaseChangeAlg` identifies `R' ⊗[R] Γ(C_R, V_R)` with `Γ(C_{R'}, V_{R'})` for `V` an
open of the BASE curve, and its proof is freeness-based (`relSectionsBaseChange`,
`R ⊗[k] Γ(C.left, V) ≃ Γ(relCurve C R, V_R)`); `pieceTermBaseChangeAlg` then localizes at a
generator.  Neither step is available for an arbitrary affine open of `relCurve C R`: there
is no generator, and no presentation as a base-changed open of `C.left`.

What replaces both is already in the tree, at exactly the right generality:
`Over.pieceRingEquiv` (`Picard/EffectivityPieces.lean`) gives
`Γ(U) ⊗[A] B ≃+* Γ(cg⁻¹ U)` for `U` an **arbitrary affine open**, from mathlib's affine
`pushoutSection` — no flatness, no freeness, `IsAffineOpen U` as the only hypothesis.  Its
`cg` is `relCurveMap` on the nose (`relCurveMap_eq_cg`).

## Main declarations

* `AlgebraicGeometry.relCurveMap_eq_cg` — the two spellings of the curve comparison agree
  (`rfl`), which is what makes the effectivity keystone reusable here.
* `AlgebraicGeometry.isAffineOpen_relCurveMap_preimage` — the preimage of an affine open is
  affine.  The chart layer had to re-derive this as "a basic open of an affine chart".
* `AlgebraicGeometry.relAffSectionsMap` — the section comparison at an arbitrary open.
* `AlgebraicGeometry.relSectionsBaseChangeAff` — `R' ⊗[R] Γ(relCurve C R, V) ≃ₐ[R']
  Γ(relCurve C R', relCurveMap ⁻¹ᵁ V)` for an arbitrary affine open `V`, with
  `relSectionsBaseChangeAff_one_tmul` (`1 ⊗ s ↦ relAffSectionsMap s`) as the one computation
  rule everything downstream runs on.
* `AlgebraicGeometry.relQuotBaseChangeAff` — the quotient transport
  `R' ⊗[R] (Γ(V) ⧸ (E)) ≃ₐ[R'] Γ(V') ⧸ (E')`, the widened colength transport, with
  `relQuotBaseChangeAff_one_tmul_mk`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable {R : Type u} [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']

/-- **The curve comparison of the divisor layer is the cover inclusion of the effectivity
layer.**  `relCurveMap` whiskers `overSpecMap R R'`, whose underlying morphism is
`Spec.map (algebraMap R R')`; `Over.overSpecMap ((Algebra.ofId R R').restrictScalars k)` is
the same `Over.homMk` of the same morphism. -/
lemma relCurveMap_eq_cg :
    relCurveMap C R R'
      = (C ◁ Over.overSpecMap ((Algebra.ofId R R').restrictScalars k)).left :=
  rfl

/-- **The preimage of an affine open under the curve comparison is affine.**  `relCurveMap` is
the base change of the affine `Spec (algebraMap R R')` along the second projection, hence
affine (`Over.isAffineHom_cg`), and preimages of affine opens along an affine morphism are
affine. -/
theorem isAffineOpen_relCurveMap_preimage {V : (relCurve C R).Opens} (hV : IsAffineOpen V) :
    IsAffineOpen (relCurveMap C R R' ⁻¹ᵁ V) :=
  Over.isAffineOpen_cgPreimage (A := R) (B := R') C hV

/-! ## The section comparison at an arbitrary affine open -/

/-- **The section comparison** at an arbitrary open `V` of the relative curve: `appLE` of the
curve comparison from `V` to its preimage.  For `V` a base-changed chart this agrees with
`relSectionsMap`; unlike that map it needs no presentation of `V`. -/
noncomputable def relAffSectionsMap (V : (relCurve C R).Opens) :
    Γ(relCurve C R, V) →+* Γ(relCurve C R', relCurveMap C R R' ⁻¹ᵁ V) :=
  ((relCurveMap C R R').appLE V (relCurveMap C R R' ⁻¹ᵁ V) le_rfl).hom

@[simp]
lemma relAffSectionsMap_apply (V : (relCurve C R).Opens) (s : Γ(relCurve C R, V)) :
    relAffSectionsMap C R' V s
      = (relCurveMap C R R').appLE V (relCurveMap C R R' ⁻¹ᵁ V) le_rfl s :=
  rfl

/-! ## The section base change at an arbitrary affine open

`Over.pieceRingEquiv` is stated on the `(C ⊗ overSpec k A).left` product spelling, with the
`Over.sectionsAlgebraA` algebra structure and the tensor factor on the RIGHT.  All three
differences from the divisor layer's conventions are `rfl`: the product spelling IS
`relCurve` (`relCurve` is a `def` for it), `Over.sectionsAlgebraA` IS
`Scheme.overSectionsAlgebra` at the relative curve, and `cg` IS `relCurveMap`
(`relCurveMap_eq_cg`).  Only the tensor side needs an actual move, and that is
`Algebra.TensorProduct.comm`. -/

/-- **Restriction naturality of the section comparison**: comparing then restricting is
restricting then comparing.  Holds for ARBITRARY opens `W ≤ V` — no affineness, because it is
only the two `appLE` collapse rules.  This is what identifies the base-changed overlap ideal
with the ideal of the base-changed equations. -/
lemma relAffSectionsMap_res {V W : (relCurve C R).Opens} (h : W ≤ V)
    (s : Γ(relCurve C R, V)) :
    ((relCurve C R').presheaf.map (homOfLE ((relCurveMap C R R').preimage_mono h)).op).hom
        (relAffSectionsMap C R' V s)
      = relAffSectionsMap C R' W (((relCurve C R).presheaf.map (homOfLE h).op).hom s) := by
  have hle : relCurveMap C R R' ⁻¹ᵁ W ≤ relCurveMap C R R' ⁻¹ᵁ V :=
    (relCurveMap C R R').preimage_mono h
  calc ((relCurve C R').presheaf.map (homOfLE hle).op).hom (relAffSectionsMap C R' V s)
      = ((relCurveMap C R R').appLE V (relCurveMap C R R' ⁻¹ᵁ W)
          (hle.trans le_rfl)).hom s := by
        rw [relAffSectionsMap_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    _ = relAffSectionsMap C R' W (((relCurve C R).presheaf.map (homOfLE h).op).hom s) := by
        rw [relAffSectionsMap_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

section BaseChange

attribute [local instance] Over.sectionsAlgebraA

/-- **The raw section base change** at an arbitrary affine open, tensor factor on the right:
`Γ(V) ⊗[R] R' ≃+* Γ(relCurveMap ⁻¹ᵁ V)`.  This is `Over.pieceRingEquiv` read in the
`relCurve`/`relCurveMap` spelling — the identification is `rfl`, so this is a rename and not a
construction. -/
noncomputable def relSectionsBaseChangeAffRingEquiv {V : (relCurve C R).Opens}
    (hV : IsAffineOpen V) :
    Γ(relCurve C R, V) ⊗[R] R' ≃+* Γ(relCurve C R', relCurveMap C R R' ⁻¹ᵁ V) :=
  Over.pieceRingEquiv (A := R) (B := R') C hV

/-- On `s ⊗ 1` the raw base change is the section comparison `relAffSectionsMap`. -/
lemma relSectionsBaseChangeAffRingEquiv_tmul_one {V : (relCurve C R).Opens}
    (hV : IsAffineOpen V) (s : Γ(relCurve C R, V)) :
    relSectionsBaseChangeAffRingEquiv C R' hV (s ⊗ₜ 1) = relAffSectionsMap C R' V s :=
  Over.pieceRingEquiv_tmul_one (A := R) (B := R') C hV s

/-- On `1 ⊗ r'` the raw base change is the structure map of `Γ(V')` over `R'`. -/
lemma relSectionsBaseChangeAffRingEquiv_one_tmul {V : (relCurve C R).Opens}
    (hV : IsAffineOpen V) (r' : R') :
    relSectionsBaseChangeAffRingEquiv C R' hV (1 ⊗ₜ r')
      = algebraMap R' Γ(relCurve C R', relCurveMap C R R' ⁻¹ᵁ V) r' :=
  Over.pieceRingEquiv_one_tmul (A := R) (B := R') C hV r'

/-- **The section base change at an arbitrary affine open, as an `R'`-algebra equivalence**
`R' ⊗[R] Γ(relCurve C R, V) ≃ₐ[R'] Γ(relCurve C R', relCurveMap ⁻¹ᵁ V)` — the widened
replacement for `relTermBaseChangeAlg ∘ pieceTermBaseChangeAlg`.  Assembled from
`Algebra.TensorProduct.comm` (to put the base-change factor on the left, the divisor layer's
convention) followed by the raw ring equivalence; `R'`-linearity is
`relSectionsBaseChangeAffRingEquiv_one_tmul`.

No freeness, no localization, no generator: the only hypothesis is that `V` is affine. -/
noncomputable def relSectionsBaseChangeAff {V : (relCurve C R).Opens} (hV : IsAffineOpen V) :
    R' ⊗[R] Γ(relCurve C R, V) ≃ₐ[R'] Γ(relCurve C R', relCurveMap C R R' ⁻¹ᵁ V) :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.comm R R' Γ(relCurve C R, V)).toRingEquiv.trans
      (relSectionsBaseChangeAffRingEquiv C R' hV))
    (fun r' => by
      change relSectionsBaseChangeAffRingEquiv C R' hV
          (Algebra.TensorProduct.comm R R' Γ(relCurve C R, V) (r' ⊗ₜ 1)) = _
      rw [Algebra.TensorProduct.comm_tmul, relSectionsBaseChangeAffRingEquiv_one_tmul])

/-- **The computation rule** the whole widened layer runs on: `1 ⊗ s ↦ relAffSectionsMap s`. -/
@[simp]
lemma relSectionsBaseChangeAff_one_tmul {V : (relCurve C R).Opens} (hV : IsAffineOpen V)
    (s : Γ(relCurve C R, V)) :
    relSectionsBaseChangeAff C R' hV ((1 : R') ⊗ₜ[R] s) = relAffSectionsMap C R' V s := by
  change relSectionsBaseChangeAffRingEquiv C R' hV
      (Algebra.TensorProduct.comm R R' Γ(relCurve C R, V) ((1 : R') ⊗ₜ[R] s)) = _
  rw [Algebra.TensorProduct.comm_tmul, relSectionsBaseChangeAffRingEquiv_tmul_one]

/-! ## The quotient transport (the widened colength transport) -/

/-- The section base change carries the extended span of a set of equations to the span of
the compared equations — the `hIJ` input of the quotient transport. -/
lemma relSpanAff_map_eq {V : (relCurve C R).Opens} (hV : IsAffineOpen V)
    (E : Set Γ(relCurve C R, V)) :
    Ideal.span (relAffSectionsMap C R' V '' E) =
      ((Ideal.span E).map (Algebra.TensorProduct.includeRight (R := R) (A := R')
        (B := Γ(relCurve C R, V)))).map
        (relSectionsBaseChangeAff C R' hV : _ →+* _) := by
  rw [Ideal.map_span, Ideal.map_span, ← Set.image_comp]
  exact congrArg Ideal.span (Set.image_congr fun s _ =>
    (relSectionsBaseChangeAff_one_tmul C R' hV s).symm)

/-- **Base change of a quotient of section rings at an arbitrary affine open** (the widened
colength transport): for a set `E` of equations on `V`,
`R' ⊗[R] (Γ(V) ⧸ (E)) ≃ₐ[R'] Γ(V') ⧸ (E')` with `V' = relCurveMap ⁻¹ᵁ V` and `E'` the image
of `E` under the section comparison.  Quotient right-exactness
(`Algebra.TensorProduct.tensorQuotientEquiv`) followed by transport along
`relSectionsBaseChangeAff`.

At `E = {f}` this is the widened (c1) colength transport; at a two-element `E` it is the
overlap-colength transport — and, unlike the chart-typed layer, the two are the SAME
declaration at two opens, because an overlap of affine opens is again an affine open and needs
no re-presentation as a basic open of anything. -/
noncomputable def relQuotBaseChangeAff {V : (relCurve C R).Opens} (hV : IsAffineOpen V)
    (E : Set Γ(relCurve C R, V)) :
    R' ⊗[R] (Γ(relCurve C R, V) ⧸ Ideal.span E) ≃ₐ[R']
      Γ(relCurve C R', relCurveMap C R R' ⁻¹ᵁ V) ⧸
        Ideal.span (relAffSectionsMap C R' V '' E) :=
  (Algebra.TensorProduct.tensorQuotientEquiv R' Γ(relCurve C R, V) R' (Ideal.span E)).trans
    (Ideal.quotientEquivAlg _ _ (relSectionsBaseChangeAff C R' hV)
      (relSpanAff_map_eq C R' hV E))

/-- The quotient transport on a pure tensor of a residue class: `1 ⊗ [s] ↦ [s']`. -/
lemma relQuotBaseChangeAff_one_tmul_mk {V : (relCurve C R).Opens} (hV : IsAffineOpen V)
    (E : Set Γ(relCurve C R, V)) (s : Γ(relCurve C R, V)) :
    relQuotBaseChangeAff C R' hV E ((1 : R') ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span E) s) =
      Ideal.Quotient.mk (Ideal.span (relAffSectionsMap C R' V '' E))
        (relAffSectionsMap C R' V s) := by
  have h1 : relQuotBaseChangeAff C R' hV E
      ((1 : R') ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span E) s) =
      Ideal.Quotient.mk (Ideal.span (relAffSectionsMap C R' V '' E))
        (relSectionsBaseChangeAff C R' hV ((1 : R') ⊗ₜ[R] s)) := rfl
  rw [h1, relSectionsBaseChangeAff_one_tmul]

end BaseChange

end AlgebraicGeometry
