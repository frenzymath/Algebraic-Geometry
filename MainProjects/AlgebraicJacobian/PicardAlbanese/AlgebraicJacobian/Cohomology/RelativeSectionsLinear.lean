/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RelativeTwoCover

/-!
# `R`-linear base change of sections on the relative curve

For the curve bundle `C` over a field `k` and a commutative `k`-algebra `R` (the affine
test ring), the landed `Over.sectionsBaseChange` identifies `Γ(C.left, V) ⊗[k] R` with
the sections of the relative curve `C_R := relCurve C R` over the preimage `V_R` — but
only as a *ring* equivalence. This file threads the `R`-module structures through it,
once, and builds the comparison morphism between relative curves over a change of test
ring `R → R'`:

* `AlgebraicGeometry.Over.sectionsBaseChange_one_tmul_overAlgebraMap` — **the
  `R`-linear threading lemma**: the base-change equivalence carries `1 ⊗ r` to the
  structure pullback `overAlgebraMap R _ r` of `r` along `C_R ⟶ Spec R`. Definitional
  once both sides are put in `appLE` normal form.
* `AlgebraicGeometry.relSectionsBaseChange` — **sections of the relative curve are the
  free base change**: `R ⊗[k] Γ(C.left, V) ≃ₗ[R] Γ(C_R, V_R)` as an `R`-linear
  equivalence (`R` acting on the left tensor factor and through `Scheme.overModule` on
  the right), with the computation rule `relSectionsBaseChange_tmul`.
* `AlgebraicGeometry.relCurveMap` — the comparison morphism `C_{R'} ⟶ C_R` over a
  `k`-algebra map `R → R'` (the whiskering of `Spec` of the algebra map), with its
  projection identities `relCurveMap_fst`, `relCurveMap_snd` and the preimage identity
  `relCurveMap_preimage`.
* `AlgebraicGeometry.relSectionsMap` — the induced ring homomorphism
  `Γ(C_R, V_R) →+* Γ(C_{R'}, V_{R'})`, with its three governing identities: it commutes
  with the curve pullbacks (`relSectionsMap_pullback`), it intertwines the structure
  actions along `algebraMap R R'` (`relSectionsMap_overAlgebraMap`, whence the
  semilinearity `relSectionsMap_smul`), and it commutes with restriction
  (`relSectionsMap_resHom`).

These are the CBC-1 ingredients; the two-term complex and `H¹` are base-changed in
`AlgebraicJacobian.Cohomology.RelativeH1BaseChange`.

## Implementation notes

The module structures are the canonical ones of the landed convention (`Scheme.overModule`
and `Over.sectionsAlgebra` as local instances); the threading lemma is what makes the
`R`-action on `Γ(C_R, V_R)` (restriction along the *second* projection) match the
`R`-action on the tensor factor. The proof of `map_smul'` for `relSectionsBaseChange`
deliberately avoids the ring structure on `R ⊗[k] Γ(C.left, V)` (which is not available
with the `overModule` instances): it computes on pure tensors through
`Over.sectionsBaseChange_tmul`.
-/

set_option autoImplicit false
/- The statements of this file mix `Γ(relCurve C R, ·)` with opens produced on the
product spelling `(C ⊗ overSpec k R).left` (the two are definitionally equal through the
semireducible `relCurve`); tactic-level congruence closure needs defeq checks through
these semireducible definitions, as in `AlgebraicJacobian.RiemannRoch.FiberTwist` and
mathlib's own algebraic-geometry files. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TensorProduct
open Opposite TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Over.sectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]

/-! ## The `R`-linear threading of the sections base change -/

/-- **Pullback of a curve section to the relative curve** along the first projection,
as a section over the base-changed open (typed at `relCurve C R`). -/
noncomputable def relPullbackSection (V : C.left.Opens) (s : Γ(C.left, V)) :
    Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V) :=
  (fst C (overSpec k R)).left.appLE V ((fst C (overSpec k R)).left ⁻¹ᵁ V) le_rfl s

section Threading

variable {V : C.left.Opens}

/-- **The `R`-linear threading lemma**: the sections base-change equivalence carries
`1 ⊗ r` to the pullback of `r` along the structure morphism `relCurve C R ⟶ Spec R`
(the `Scheme.overAlgebraMap` of the relative curve). This is the one point where the
`R`-action on the tensor factor is matched with the `R`-action on relative sections. -/
theorem Over.sectionsBaseChange_one_tmul_overAlgebraMap
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left)) (r : R) :
    Over.sectionsBaseChange C R hV hV' (1 ⊗ₜ r) =
      (relCurve C R).overAlgebraMap R ((fst C (overSpec k R)).left ⁻¹ᵁ V) r := by
  rw [Over.sectionsBaseChange_one_tmul]
  rfl

/-- **Sections of the relative curve are the free base change of the curve's sections**:
the `R`-linear equivalence `R ⊗[k] Γ(C.left, V) ≃ₗ[R] Γ(relCurve C R, V_R)`, for a qcqs
open `V ⊆ C.left`. The underlying map is the landed ring equivalence
`Over.sectionsBaseChange` (composed with the flip of the tensor factors); the `R`-module
structure on the right is `Scheme.overModule` for the structure morphism to `Spec R`. -/
noncomputable def relSectionsBaseChange
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left)) :
    R ⊗[k] Γ(C.left, V) ≃ₗ[R]
      Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V) where
  toFun x := Over.sectionsBaseChange C R hV hV' (TensorProduct.comm k R Γ(C.left, V) x)
  invFun y := (TensorProduct.comm k R Γ(C.left, V)).symm
    ((Over.sectionsBaseChange C R hV hV').symm y)
  left_inv x := by
    simp only [RingEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  right_inv y := by
    simp only [LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  map_add' x y := by rw [map_add, map_add]
  map_smul' r x := by
    rw [RingHom.id_apply]
    induction x with
    | zero => simp only [smul_zero, map_zero]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, map_add, map_add, smul_add]
    | tmul a s =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.comm_tmul,
        TensorProduct.comm_tmul, Over.sectionsBaseChange_tmul,
        Over.sectionsBaseChange_tmul, map_mul, Scheme.overModule_smul_def]
      exact mul_left_comm _ _ _

/-- The base-change equivalence on a pure tensor: `a ⊗ s` goes to the structure
pullback of `a` times the pullback of `s` along the first projection (equivalently,
by `Scheme.overModule_smul_def`, to the `Scheme.overModule` action of `a` on the
pullback of `s`). -/
lemma relSectionsBaseChange_tmul
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
    (a : R) (s : Γ(C.left, V)) :
    relSectionsBaseChange C R hV hV' (a ⊗ₜ s) =
      (relCurve C R).overAlgebraMap R ((fst C (overSpec k R)).left ⁻¹ᵁ V) a *
        relPullbackSection C R V s := by
  change Over.sectionsBaseChange C R hV hV'
    (TensorProduct.comm k R Γ(C.left, V) (a ⊗ₜ s)) = _
  rw [TensorProduct.comm_tmul, Over.sectionsBaseChange_tmul]
  exact mul_comm _ _

end Threading

/-! ## The comparison morphism between relative curves over `R → R'` -/

section CurveMap

variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']

/-- `Spec` of the algebra map `R → R'`, as a morphism `overSpec k R' ⟶ overSpec k R`
in `Over (Spec k)`. -/
noncomputable def overSpecMap : overSpec k R' ⟶ overSpec k R :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (by
    simp only [overSpec_left, Over.mk_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])

@[simp]
lemma overSpecMap_left :
    (overSpecMap (k := k) R R').left = Spec.map (CommRingCat.ofHom (algebraMap R R')) :=
  rfl

/-- **The comparison morphism between relative curves** over the test-ring change
`R → R'`: the underlying scheme morphism of the whiskering `C ◁ overSpecMap R R'`,
`relCurve C R' ⟶ relCurve C R`. -/
noncomputable def relCurveMap : relCurve C R' ⟶ relCurve C R :=
  (C ◁ overSpecMap (k := k) R R').left

/-- The comparison morphism commutes with the first projections. -/
lemma relCurveMap_fst :
    relCurveMap C R R' ≫ (fst C (overSpec k R)).left = (fst C (overSpec k R')).left :=
  congrArg (fun φ : C ⊗ overSpec k R' ⟶ C ↦ φ.left)
    (whiskerLeft_fst C (overSpecMap (k := k) R R'))

/-- The comparison morphism intertwines the second projections through `Spec` of the
algebra map. -/
lemma relCurveMap_snd :
    relCurveMap C R R' ≫ (snd C (overSpec k R)).left =
      (snd C (overSpec k R')).left ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) :=
  congrArg (fun φ : C ⊗ overSpec k R' ⟶ overSpec k R ↦ φ.left)
    (whiskerLeft_snd C (overSpecMap (k := k) R R'))

/-- The comparison morphism pulls the base-changed opens of `C_R` back to the
base-changed opens of `C_{R'}`. -/
lemma relCurveMap_preimage (V : C.left.Opens) :
    relCurveMap C R R' ⁻¹ᵁ ((fst C (overSpec k R)).left ⁻¹ᵁ V) =
      (fst C (overSpec k R')).left ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, relCurveMap_fst]

/-- `appLE` is invariant under an equality of morphisms (the inclusion witness is
proof-irrelevant). -/
private lemma appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) {U : Y.Opens}
    {W : X.Opens} (e : W ≤ f ⁻¹ᵁ U) :
    f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h; rfl

/-- **The relative sections comparison map** over the test-ring change `R → R'`: the
ring homomorphism `Γ(C_R, V_R) →+* Γ(C_{R'}, V_{R'})` induced by `relCurveMap`. -/
noncomputable def relSectionsMap (V : C.left.Opens) :
    Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V) →+*
      Γ(relCurve C R', (fst C (overSpec k R')).left ⁻¹ᵁ V) :=
  ((relCurveMap C R R').appLE ((fst C (overSpec k R)).left ⁻¹ᵁ V)
    ((fst C (overSpec k R')).left ⁻¹ᵁ V)
    (le_of_eq (relCurveMap_preimage C R R' V).symm)).hom

/-- The sections comparison map commutes with the curve pullbacks: pulled-back sections
of the curve compare to pulled-back sections. -/
lemma relSectionsMap_pullback (V : C.left.Opens) (s : Γ(C.left, V)) :
    relSectionsMap C R R' V (relPullbackSection C R V s) =
      relPullbackSection C R' V s := by
  have h : (fst C (overSpec k R)).left.appLE V ((fst C (overSpec k R)).left ⁻¹ᵁ V)
        le_rfl ≫
      (relCurveMap C R R').appLE ((fst C (overSpec k R)).left ⁻¹ᵁ V)
        ((fst C (overSpec k R')).left ⁻¹ᵁ V)
        (le_of_eq (relCurveMap_preimage C R R' V).symm) =
      (fst C (overSpec k R')).left.appLE V ((fst C (overSpec k R')).left ⁻¹ᵁ V)
        le_rfl := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_hom (relCurveMap_fst C R R') _
  exact congr($(h).hom s)

/-- The sections comparison map intertwines the structure actions: the pullback of
`r : R` compares to the pullback of `algebraMap R R' r`. -/
lemma relSectionsMap_overAlgebraMap (V : C.left.Opens) (r : R) :
    relSectionsMap C R R' V
      ((relCurve C R).overAlgebraMap R ((fst C (overSpec k R)).left ⁻¹ᵁ V) r) =
      (relCurve C R').overAlgebraMap R' ((fst C (overSpec k R')).left ⁻¹ᵁ V)
        (algebraMap R R' r) := by
  have hmor : ((Scheme.ΓSpecIso (.of R)).inv ≫
        (snd C (overSpec k R)).left.appLE ⊤ ((fst C (overSpec k R)).left ⁻¹ᵁ V)
          (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k R)).left).ge)) ≫
      (relCurveMap C R R').appLE ((fst C (overSpec k R)).left ⁻¹ᵁ V)
        ((fst C (overSpec k R')).left ⁻¹ᵁ V)
        (le_of_eq (relCurveMap_preimage C R R' V).symm) =
      CommRingCat.ofHom (algebraMap R R') ≫ (Scheme.ΓSpecIso (.of R')).inv ≫
        (snd C (overSpec k R')).left.appLE ⊤ ((fst C (overSpec k R')).left ⁻¹ᵁ V)
          (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k R')).left).ge) := by
    have hnat : (Scheme.ΓSpecIso (.of R)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R R'))).appTop =
        CommRingCat.ofHom (algebraMap R R') ≫ (Scheme.ΓSpecIso (.of R')).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc,
        ← Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R R')),
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hsplit : ((snd C (overSpec k R')).left ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R'))).appLE ⊤
          ((fst C (overSpec k R')).left ⁻¹ᵁ V)
          ((relCurveMap_snd C R R') ▸
            (le_of_eq (relCurveMap_preimage C R R' V).symm).trans
              (Scheme.Hom.preimage_mono _ (le_top.trans
                (Scheme.Hom.preimage_top (snd C (overSpec k R)).left).ge))) =
        (Spec.map (CommRingCat.ofHom (algebraMap R R'))).appLE ⊤ ⊤
            (Scheme.Hom.preimage_top _).ge ≫
          (snd C (overSpec k R')).left.appLE ⊤ ((fst C (overSpec k R')).left ⁻¹ᵁ V)
            (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k R')).left).ge) :=
      (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    have happ : (Spec.map (CommRingCat.ofHom (algebraMap R R'))).appLE ⊤ ⊤
        (Scheme.Hom.preimage_top _).ge =
        (Spec.map (CommRingCat.ofHom (algebraMap R R'))).appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [Category.assoc, Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom (relCurveMap_snd C R R'), hsplit, happ, ← Category.assoc,
      hnat, Category.assoc]
  exact congr($(hmor).hom r)

/-- **Semilinearity of the sections comparison map**: it intertwines the
`Scheme.overModule` actions along `algebraMap R R'`. -/
lemma relSectionsMap_smul (V : C.left.Opens) (r : R)
    (y : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)) :
    relSectionsMap C R R' V (r • y) =
      algebraMap R R' r • relSectionsMap C R R' V y := by
  rw [Scheme.overModule_smul_def, map_mul, relSectionsMap_overAlgebraMap,
    Scheme.overModule_smul_def]

/-- The sections comparison map commutes with restriction along `W ≤ V`. -/
lemma relSectionsMap_resHom {W V : C.left.Opens} (hWV : W ≤ V)
    (y : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)) :
    relSectionsMap C R R' W
      ((relCurve C R).resHom
        (Scheme.Hom.preimage_mono (fst C (overSpec k R)).left hWV) y) =
      (relCurve C R').resHom
        (Scheme.Hom.preimage_mono (fst C (overSpec k R')).left hWV)
        (relSectionsMap C R R' V y) := by
  have h1 := Scheme.Hom.map_appLE (relCurveMap C R R')
    (le_of_eq (relCurveMap_preimage C R R' W).symm)
    (homOfLE (Scheme.Hom.preimage_mono (fst C (overSpec k R)).left hWV)).op
  have h2 := Scheme.Hom.appLE_map (relCurveMap C R R')
    (le_of_eq (relCurveMap_preimage C R R' V).symm)
    (homOfLE (Scheme.Hom.preimage_mono (fst C (overSpec k R')).left hWV)).op
  exact (congr($(h1).hom y)).trans (congr($(h2).hom y)).symm

end CurveMap

end AlgebraicGeometry
