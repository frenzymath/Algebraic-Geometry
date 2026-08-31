/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RelativeSectionsLinear
import AlgebraicJacobian.Cohomology.TwistedSheaf

/-!
# Base change of the two-term complex and of `H¹` on the relative curve

CBC-1/2 for the structure sheaf, bundled: for the curve bundle `C` over a field `k`, a
tower of test rings `R → R'` (commutative `k`-algebras) and the base-changed affine
two-cover `relCover C R D` of the relative curve `C_R`, this file base-changes the
two-term Čech complex `Γ(V₀ᴿ) × Γ(V₁ᴿ) → Γ(V₀ᴿ ⊓ V₁ᴿ)` along `R → R'` and deduces the
degree-one comparison isomorphism — Kleiman's "cohomology commutes with base change" in
the curve-lite two-cover form.

* `LinearMap.quotRangeBaseChangeEquiv` — the general right-exactness input: base change
  commutes with cokernels, `A ⊗[R] (N ⧸ range f) ≃ₗ[A] (A ⊗[R] N) ⧸ range (f.baseChange A)`.
* `AlgebraicGeometry.relTermBaseChange` — **CBC-1, termwise**: for a qcqs open
  `V ⊆ C.left`, the `R'`-linear equivalence
  `R' ⊗[R] Γ(C_R, V_R) ≃ₗ[R'] Γ(C_{R'}, V_{R'})`, with the computation rule
  `relTermBaseChange_tmul` (`r' ⊗ y ↦ r' • relSectionsMap y`).
* `AlgebraicGeometry.relDiffBaseChange` — **CBC-1, the complex**: the base change of the
  two-cover restriction-difference map `TwoCover.diff` over `R` is carried to the
  difference map over `R'` under the term equivalences (the commuting square).
* `AlgebraicGeometry.relH1CokBaseChange` — **CBC-2 (`i = 1`), cokernel form**:
  `R' ⊗[R] H1Cok R (C_R) ≃ₗ[R'] H1Cok R' (C_{R'})`, unconditionally in `R → R'` (the
  cokernel of a base-changed complex is the base change of the cokernel; no flatness).
* `AlgebraicGeometry.relH1BaseChange` — **CBC-2 (`i = 1`)**: the same statement on the
  cohomology carriers, `R' ⊗[R] H¹(C_R, 𝒪) ≃ₗ[R'] H¹(C_{R'}, 𝒪)`, through the landed
  relative two-cover identification `relTwoCoverH1`.

Degree zero for the structure sheaf needs no separate statement: `H⁰(C_R, 𝒪) ≃+* R`
on the nose (`AlgebraicGeometry.relStructureSectionsTop`), so its base change is
`R ⊗_R R' ≃ R'`.

## Implementation notes

The overlap opens `V₀ᴿ ⊓ V₁ᴿ` (the `TwoCover.H1Cok` spelling) and
`fst ⁻¹ᵁ (D.V₀ ⊓ D.V₁)` (the base-change spelling) are definitionally equal; statements
are given in the `H1Cok` spelling, and spelling adapters are introduced as local `have`s
justified by `exact` where the two must meet. See
`AlgebraicJacobian.Cohomology.RelativeSectionsLinear` for the transparency option.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TensorProduct
open Opposite TopologicalSpace

/-! ## Base change commutes with cokernels -/

namespace LinearMap

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (f : M →ₗ[R] N)

private lemma ker_mkQ_baseChange :
    LinearMap.ker ((LinearMap.range f).mkQ.baseChange A) =
      LinearMap.range (f.baseChange A) := by
  apply LinearMap.exact_iff.mp
  rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
  exact lTensor_exact A (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _)

private lemma surjective_mkQ_baseChange :
    Function.Surjective ((LinearMap.range f).mkQ.baseChange A) := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective A (Submodule.mkQ_surjective _)

/-- **Base change commutes with cokernels**: for a linear map `f : M →ₗ[R] N` and an
`R`-algebra `A`, the base change of the cokernel of `f` is the cokernel of the base
change of `f`, `A`-linearly. Right-exactness of `A ⊗[R] -` in the two-term form consumed
by the Čech-complex base change. 


 * Provenance: CUSTOM.
-/
noncomputable def quotRangeBaseChangeEquiv :
    A ⊗[R] (N ⧸ LinearMap.range f) ≃ₗ[A]
      (A ⊗[R] N) ⧸ LinearMap.range (f.baseChange A) :=
  ((Submodule.quotEquivOfEq _ _ (ker_mkQ_baseChange A f).symm).trans
    (((LinearMap.range f).mkQ.baseChange A).quotKerEquivOfSurjective
      (surjective_mkQ_baseChange A f))).symm

/-- Provenance: CUSTOM. -/
@[simp]
lemma quotRangeBaseChangeEquiv_tmul_mk (a : A) (n : N) :
    quotRangeBaseChangeEquiv A f (a ⊗ₜ Submodule.Quotient.mk n) =
      Submodule.Quotient.mk (a ⊗ₜ n) := by
  rw [quotRangeBaseChangeEquiv, ← LinearEquiv.eq_symm_apply, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  calc ((LinearMap.range f).mkQ.baseChange A).quotKerEquivOfSurjective
        (surjective_mkQ_baseChange A f) (Submodule.Quotient.mk (a ⊗ₜ n))
      = ((LinearMap.range f).mkQ.baseChange A) (a ⊗ₜ n) := rfl
    _ = a ⊗ₜ Submodule.Quotient.mk n := by
        rw [LinearMap.baseChange_tmul, Submodule.mkQ_apply]

end LinearMap

/-! ## CBC-1: termwise base change of the two-term complex -/

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Over.sectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']

/-- **CBC-1, termwise**: base change of relative sections along the test-ring change
`R → R'`, as an `R'`-linear equivalence
`R' ⊗[R] Γ(C_R, V_R) ≃ₗ[R'] Γ(C_{R'}, V_{R'})` for a qcqs open `V ⊆ C.left`. Composite
of the two free base-change identifications `relSectionsBaseChange` with the tensor
cancellation `(R' ⊗[R] (R ⊗[k] -)) ≃ (R' ⊗[k] -)`. -/
noncomputable def relTermBaseChange (V : C.left.Opens)
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left)) :
    R' ⊗[R] Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V) ≃ₗ[R']
      Γ(relCurve C R', (fst C (overSpec k R')).left ⁻¹ᵁ V) :=
  (LinearEquiv.baseChange R R' _ _ (relSectionsBaseChange C R hV hV').symm).trans
    ((AlgebraTensorModule.cancelBaseChange k R R' R' Γ(C.left, V)).trans
      (relSectionsBaseChange C R' hV hV'))

set_option maxHeartbeats 1000000 in
-- The `respectTransparency false` defeq checks through the `relCurve`/product spellings
-- make elaboration exceed the default limit ...
set_option synthInstance.maxHeartbeats 400000 in
-- ... and the instance searches on the large tensor types exceed the default limit.
/-- The termwise base change on a pure tensor: `r' ⊗ y` goes to the `R'`-action of `r'`
on the compared section `relSectionsMap y`. -/
lemma relTermBaseChange_tmul {V : C.left.Opens}
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
    (r' : R') (y : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)) :
    relTermBaseChange C R R' V hV hV' (r' ⊗ₜ y) =
      r' • relSectionsMap C R R' V y := by
  obtain ⟨x, rfl⟩ := (relSectionsBaseChange C R hV hV').surjective y
  rw [relTermBaseChange, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply]
  induction x with
  | zero =>
    simp only [map_zero, TensorProduct.tmul_zero, smul_zero]
  | add x y hx hy =>
    rw [TensorProduct.tmul_add, map_add, map_add, map_add, map_add, hx, hy, smul_add]
  | tmul a s =>
    rw [AlgebraTensorModule.cancelBaseChange_tmul, relSectionsBaseChange_tmul,
      relSectionsBaseChange_tmul, map_mul, relSectionsMap_overAlgebraMap,
      relSectionsMap_pullback, Scheme.overModule_smul_def, Algebra.smul_def, map_mul,
      mul_assoc]
    exact mul_left_comm _ _ _

variable (D : C.left.AffineTwoCover)

/-! ## CBC-1: the complex base-changes -/

/-- The base change of the two-cover complex's degree-zero term: the product of the two
chart-term equivalences, `R' ⊗[R] (Γ(V₀ᴿ) × Γ(V₁ᴿ)) ≃ₗ[R'] Γ(V₀ᴿ') × Γ(V₁ᴿ')`. -/
noncomputable def relDiffDomBaseChange :
    R' ⊗[R] (Γ(relCurve C R, (relCover C R D).V₀) ×
        Γ(relCurve C R, (relCover C R D).V₁)) ≃ₗ[R']
      Γ(relCurve C R', (relCover C R' D).V₀) × Γ(relCurve C R', (relCover C R' D).V₁) :=
  (TensorProduct.prodRight R R' R' _ _).trans
    ((relTermBaseChange C R R' D.V₀ D.isAffineOpen₀.isCompact
        D.isAffineOpen₀.isQuasiSeparated).prodCongr
      (relTermBaseChange C R R' D.V₁ D.isAffineOpen₁.isCompact
        D.isAffineOpen₁.isQuasiSeparated))

/-- The overlap-term base change, in the `V₀ᴿ ⊓ V₁ᴿ` spelling of the two-cover
carrier. -/
noncomputable def relDiffCodBaseChange :
    R' ⊗[R] Γ(relCurve C R, (relCover C R D).V₀ ⊓ (relCover C R D).V₁) ≃ₗ[R']
      Γ(relCurve C R', (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁) :=
  relTermBaseChange C R R' (D.V₀ ⊓ D.V₁) D.isAffineOpen_inf.isCompact
    D.isAffineOpen_inf.isQuasiSeparated

/-- The overlap-term base change on a pure tensor. -/
lemma relDiffCodBaseChange_tmul (r' : R')
    (y : Γ(relCurve C R, (relCover C R D).V₀ ⊓ (relCover C R D).V₁)) :
    relDiffCodBaseChange C R R' D (r' ⊗ₜ y) =
      r' • relSectionsMap C R R' (D.V₀ ⊓ D.V₁) y :=
  relTermBaseChange_tmul C R R' D.isAffineOpen_inf.isCompact
    D.isAffineOpen_inf.isQuasiSeparated r' y

set_option maxHeartbeats 1000000 in
-- Same limits as `relTermBaseChange_tmul`: the mixed-spelling defeq checks are heavy.
set_option synthInstance.maxHeartbeats 400000 in
-- (Instance-search limit, same reason.)
/-- **CBC-1 (the commuting square, pointwise)**: the base change of the two-cover
restriction-difference map over `R` is carried to the restriction-difference map over
`R'` under the term equivalences. -/
lemma relDiffBaseChange
    (x : R' ⊗[R] (Γ(relCurve C R, (relCover C R D).V₀) ×
      Γ(relCurve C R, (relCover C R D).V₁))) :
    relDiffCodBaseChange C R R' D
      ((TwoCover.diff R (relCurve C R) (relCover C R D).V₀
          (relCover C R D).V₁).baseChange R' x) =
      TwoCover.diff R' (relCurve C R') (relCover C R' D).V₀ (relCover C R' D).V₁
        (relDiffDomBaseChange C R R' D x) := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r' p =>
    -- spelling adapters: the comparison map commutes with the two chart restrictions
    have e₀ : relSectionsMap C R R' (D.V₀ ⊓ D.V₁)
        ((relCurve C R).resHom
          (inf_le_left : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
            (relCover C R D).V₀) p.1) =
        (relCurve C R').resHom
          (inf_le_left : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
            (relCover C R' D).V₀)
          (relSectionsMap C R R' D.V₀ p.1) :=
      relSectionsMap_resHom C R R' inf_le_left p.1
    have e₁ : relSectionsMap C R R' (D.V₀ ⊓ D.V₁)
        ((relCurve C R).resHom
          (inf_le_right : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
            (relCover C R D).V₁) p.2) =
        (relCurve C R').resHom
          (inf_le_right : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
            (relCover C R' D).V₁)
          (relSectionsMap C R R' D.V₁ p.2) :=
      relSectionsMap_resHom C R R' inf_le_right p.2
    have hres₀ : (relCurve C R').resHom
        (inf_le_left : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
          (relCover C R' D).V₀)
        (r' • relSectionsMap C R R' D.V₀ p.1) =
        r' • (relCurve C R').resHom inf_le_left (relSectionsMap C R R' D.V₀ p.1) := by
      rw [Scheme.overModule_smul_def, map_mul, Scheme.overModule_smul_def]
      congr 1
      exact (relCurve C R').overAlgebraMap_apply_res R' (homOfLE _).op r'
    have hres₁ : (relCurve C R').resHom
        (inf_le_right : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
          (relCover C R' D).V₁)
        (r' • relSectionsMap C R R' D.V₁ p.2) =
        r' • (relCurve C R').resHom inf_le_right (relSectionsMap C R R' D.V₁ p.2) := by
      rw [Scheme.overModule_smul_def, map_mul, Scheme.overModule_smul_def]
      congr 1
      exact (relCurve C R').overAlgebraMap_apply_res R' (homOfLE _).op r'
    have hdom : relDiffDomBaseChange C R R' D (r' ⊗ₜ p) =
        (r' • relSectionsMap C R R' D.V₀ p.1, r' • relSectionsMap C R R' D.V₁ p.2) := by
      rw [relDiffDomBaseChange, LinearEquiv.trans_apply, TensorProduct.prodRight_tmul]
      exact Prod.ext
        (relTermBaseChange_tmul C R R' D.isAffineOpen₀.isCompact
          D.isAffineOpen₀.isQuasiSeparated r' p.1)
        (relTermBaseChange_tmul C R R' D.isAffineOpen₁.isCompact
          D.isAffineOpen₁.isQuasiSeparated r' p.2)
    rw [LinearMap.baseChange_tmul, relDiffCodBaseChange_tmul, hdom]
    simp only [TwoCover.diff_apply]
    rw [map_sub, e₀, e₁, smul_sub]
    exact congrArg₂ (· - ·) hres₀.symm hres₁.symm

/-! ## CBC-2 (`i = 1`): base change of the two-cover `H¹` -/

/-- The commuting square of CBC-1, in range form: the term equivalence over the overlap
carries the range of the base-changed difference map onto the range of the difference
map over `R'`. -/
lemma relDiffBaseChange_range :
    Submodule.map (relDiffCodBaseChange C R R' D : _ →ₗ[R'] _)
      (LinearMap.range ((TwoCover.diff R (relCurve C R) (relCover C R D).V₀
        (relCover C R D).V₁).baseChange R')) =
      LinearMap.range (TwoCover.diff R' (relCurve C R') (relCover C R' D).V₀
        (relCover C R' D).V₁) := by
  have hcomp : (relDiffCodBaseChange C R R' D).toLinearMap.comp
      ((TwoCover.diff R (relCurve C R) (relCover C R D).V₀
        (relCover C R D).V₁).baseChange R') =
      (TwoCover.diff R' (relCurve C R') (relCover C R' D).V₀
        (relCover C R' D).V₁).comp (relDiffDomBaseChange C R R' D).toLinearMap :=
    LinearMap.ext fun x ↦ relDiffBaseChange C R R' D x
  rw [← LinearMap.range_comp, hcomp,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- **CBC-2 (`i = 1`), cokernel form**: the two-cover `H¹` cokernel carrier of the
structure sheaf base-changes along `R → R'`, unconditionally —
`R' ⊗[R] H1Cok R (C_R) ≃ₗ[R'] H1Cok R' (C_{R'})` (the cokernel of the base-changed
complex is the base change of the cokernel; right-exactness needs no flatness). -/
noncomputable def relH1CokBaseChange :
    R' ⊗[R] TwoCover.H1Cok R (relCurve C R) (relCover C R D).V₀ (relCover C R D).V₁
      ≃ₗ[R']
      TwoCover.H1Cok R' (relCurve C R') (relCover C R' D).V₀ (relCover C R' D).V₁ :=
  (LinearMap.quotRangeBaseChangeEquiv R'
    (TwoCover.diff R (relCurve C R) (relCover C R D).V₀ (relCover C R D).V₁)).trans
    (Submodule.Quotient.equiv _ _ (relDiffCodBaseChange C R R' D)
      (relDiffBaseChange_range C R R' D))

/-- The `H¹` cokernel base change on the class of a pure tensor: `r' ⊗ [s]` goes to the
class of `r' • relSectionsMap s`. -/
lemma relH1CokBaseChange_tmul_mk (r' : R')
    (s : Γ(relCurve C R, (relCover C R D).V₀ ⊓ (relCover C R D).V₁)) :
    relH1CokBaseChange C R R' D (r' ⊗ₜ Submodule.Quotient.mk s) =
      Submodule.Quotient.mk (r' • relSectionsMap C R R' (D.V₀ ⊓ D.V₁) s) := by
  rw [relH1CokBaseChange, LinearEquiv.trans_apply,
    LinearMap.quotRangeBaseChangeEquiv_tmul_mk, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply]
  exact congrArg Submodule.Quotient.mk (relDiffCodBaseChange_tmul C R R' D r' s)

/-- **CBC-2 (`i = 1`)**: degree-one cohomology of the structure sheaf on the relative
curve commutes with base change of the test ring, unconditionally —
`R' ⊗[R] H¹(C_R, 𝒪) ≃ₗ[R'] H¹(C_{R'}, 𝒪)`, through the landed relative two-cover
carrier `relTwoCoverH1`. The curve-lite form of Kleiman's *"cohomology commutes with
flat base change"* for the structure sheaf in degree one (here without flatness, by
right-exactness of the two-term complex's cokernel). -/
noncomputable def relH1BaseChange :
    R' ⊗[R] Sheaf.HModule ((relCurve C R).moduleKSheaf R) 1 ≃ₗ[R']
      Sheaf.HModule ((relCurve C R').moduleKSheaf R') 1 :=
  (LinearEquiv.baseChange R R' _ _ (relTwoCoverH1 C R D)).trans
    ((relH1CokBaseChange C R R' D).trans (relTwoCoverH1 C R' D).symm)

/-! ## Toward CBC-1/2 for the twisted sheaf

The unit cocycle base-changes to a unit cocycle (`g ↦ g ⊗ 1`, units map to units), and
the terms of the twisted two-cover complex base-change through the chart
trivializations. **Frontier** (deliberately not built here): the compatibility of these
term equivalences with the *twisted* restriction-difference map (the cocycle-conjugated
analogue of `relDiffBaseChange`), hence `H¹` base change for `F_g`; it is the same
`relSectionsMap` bookkeeping with one extra `g`-factor carried through
`relSectionsMap.map_mul`. -/

section Twisted

variable (g : Γ(relCurve C R, (relCover C R D).V₀ ⊓ (relCover C R D).V₁)ˣ)

/-- **The unit cocycle base-changes**: the image of a two-cover unit cocycle on `C_R`
under the sections comparison map is a unit cocycle on the base-changed two-cover of
`C_{R'}` (`g ↦ g ⊗ 1`; units map to units). -/
noncomputable def relCocycleBaseChange :
    Γ(relCurve C R', (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁)ˣ :=
  Units.map (relSectionsMap C R R' (D.V₀ ⊓ D.V₁)).toMonoidHom g

/-- CBC-1 for the twisted sheaf, first chart term: sections of `F_g` over the first
chart base-change onto sections of `F_{g ⊗ 1}`, through the chart trivializations and
the structure-sheaf term base change. -/
noncomputable def relTwistTermBaseChange₀ :
    R' ⊗[R] ↥(twistSubmodule R (relCover C R D).V₀ (relCover C R D).V₁ g
        (relCover C R D).V₀) ≃ₗ[R']
      ↥(twistSubmodule R' (relCover C R' D).V₀ (relCover C R' D).V₁
        (relCocycleBaseChange C R R' D g) (relCover C R' D).V₀) :=
  (LinearEquiv.baseChange R R' _ _
    (twistTriv₀ R (relCover C R D).V₀ (relCover C R D).V₁ g le_rfl)).trans
    ((relTermBaseChange C R R' D.V₀ D.isAffineOpen₀.isCompact
        D.isAffineOpen₀.isQuasiSeparated).trans
      (twistTriv₀ R' (relCover C R' D).V₀ (relCover C R' D).V₁
        (relCocycleBaseChange C R R' D g) le_rfl).symm)

/-- CBC-1 for the twisted sheaf, second chart term. -/
noncomputable def relTwistTermBaseChange₁ :
    R' ⊗[R] ↥(twistSubmodule R (relCover C R D).V₀ (relCover C R D).V₁ g
        (relCover C R D).V₁) ≃ₗ[R']
      ↥(twistSubmodule R' (relCover C R' D).V₀ (relCover C R' D).V₁
        (relCocycleBaseChange C R R' D g) (relCover C R' D).V₁) :=
  (LinearEquiv.baseChange R R' _ _
    (twistTriv₁ R (relCover C R D).V₀ (relCover C R D).V₁ g le_rfl)).trans
    ((relTermBaseChange C R R' D.V₁ D.isAffineOpen₁.isCompact
        D.isAffineOpen₁.isQuasiSeparated).trans
      (twistTriv₁ R' (relCover C R' D).V₀ (relCover C R' D).V₁
        (relCocycleBaseChange C R R' D g) le_rfl).symm)

/-- CBC-1 for the twisted sheaf, overlap term (the term whose cokernel is the twisted
`H¹` of `AlgebraicGeometry.relTwistTwoCoverH1`). -/
noncomputable def relTwistOverlapBaseChange :
    R' ⊗[R] ↥(twistSubmodule R (relCover C R D).V₀ (relCover C R D).V₁ g
        ((relCover C R D).V₀ ⊓ (relCover C R D).V₁)) ≃ₗ[R']
      ↥(twistSubmodule R' (relCover C R' D).V₀ (relCover C R' D).V₁
        (relCocycleBaseChange C R R' D g)
        ((relCover C R' D).V₀ ⊓ (relCover C R' D).V₁)) :=
  (LinearEquiv.baseChange R R' _ _
    (twistTriv₀ R (relCover C R D).V₀ (relCover C R D).V₁ g inf_le_left)).trans
    ((relDiffCodBaseChange C R R' D).trans
      (twistTriv₀ R' (relCover C R' D).V₀ (relCover C R' D).V₁
        (relCocycleBaseChange C R R' D g) inf_le_left).symm)

end Twisted

end AlgebraicGeometry
