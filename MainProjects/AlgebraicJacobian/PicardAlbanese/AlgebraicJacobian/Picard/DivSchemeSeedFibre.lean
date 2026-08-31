/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeFamilySide
import AlgebraicJacobian.Curve.BaseChangeInstances
import AlgebraicJacobian.Cohomology.GluedSheafDatumBaseChange
import AlgebraicJacobian.Cohomology.RelativeH1BaseChange
import AlgebraicJacobian.Cohomology.RigidEngine5Toolkit
import AlgebraicJacobian.Picard.OpenImmersionUnits

/-!
# DDR-3 seed provider — the fibre comparison on basic opens and fibre regularity

The fibre-sections identification of the DDR-3 route (I-0198 item (iv)), in the
injectivity form the seed's `fibre_regular` clause consumes: on a basic open `D(g)` of a
base-changed chart `V_R` of the relative curve, the multiplication comparison

  `Γ(C_R, D(g)) ⊗[R] R' ⟶ Γ(C_{R'}, D(g'))`,  `g' := relSectionsMap g`,

is **injective** — at chart level it agrees with the landed termwise base change
`relTermBaseChange` (hence is bijective), and on the basic open both sides are
away-localizations of the chart rings, so injectivity descends by denominator clearing.

* `AlgebraicGeometry.relBasicPull` — the fibre pullback `Γ(C_R, D(g)) →+* Γ(C_{R'}, D(g'))`
  (`relCurveMap.appLE` through `relSectionsMap_basicOpen`), with restriction naturality
  (`relBasicPull_resHom`) and structure-map compatibility (`relBasicPull_overAlgebraMap`);
* `AlgebraicGeometry.relChartFibreMul` / `relBasicFibreMul` — the multiplication
  comparisons `Γ ⊗[R] R' →+* Γ'` at chart and basic-open level;
* `AlgebraicGeometry.relChartFibreMul_bijective` — chart-level bijectivity, transported
  from `relTermBaseChange` by pure-tensor agreement;
* `AlgebraicGeometry.relBasicFibreMul_injective` — **the injectivity keystone**;
* `AlgebraicGeometry.sections_mem_nonZeroDivisors_of_ne_zero_of_isIntegral` — on an
  integral scheme, a section that is nonzero (whenever its open is nonempty) is a
  nonzerodivisor;
* `AlgebraicGeometry.tmul_one_mem_nonZeroDivisors_of_relBasicPull` /
  `relBasicPull_resHom_ne_zero_of_relSectionsMap_ne_zero` — **the fibre-regularity
  keystones** at a field fibre `L`: exactly the shape of
  `ThetaGeneratorSeed.IsGenerator.fibre_regular`, fed by nonvanishing of the chart-level
  compared section (fibre-curve integrality comes from `Curve/BaseChangeInstances`).
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C B, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k B).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable (V : C.left.Opens)

/-! ## The fibre pullback on a basic open of a chart -/

/-- **The fibre pullback on a basic open**: the ring homomorphism
`Γ(C_R, D(g)) →+* Γ(C_{R'}, D(g'))`, `g' := relSectionsMap g`, induced by the curve
comparison `relCurveMap` (whose preimage of `D(g)` is `D(g')`,
`relSectionsMap_basicOpen`). -/
noncomputable def relBasicPull (g : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)) :
    Γ(relCurve C R, (relCurve C R).basicOpen g) →+*
      Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V g)) :=
  ((relCurveMap C R R').appLE ((relCurve C R).basicOpen g)
    ((relCurve C R').basicOpen (relSectionsMap C R R' V g))
    (le_of_eq (relSectionsMap_basicOpen C R R' V g))).hom

/-- The fibre pullback commutes with restriction from the chart: pulling back a
restricted chart section is restricting the compared section. -/
lemma relBasicPull_resHom (g : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V))
    (y : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)) :
    relBasicPull C R R' V g ((relCurve C R).resHom ((relCurve C R).basicOpen_le g) y)
      = (relCurve C R').resHom
          ((relCurve C R').basicOpen_le (relSectionsMap C R R' V g))
          (relSectionsMap C R R' V y) := by
  exact (Scheme.Hom.appLE_resHom (relCurveMap C R R')
    ((relCurve C R).basicOpen_le g)
    (le_of_eq (relCurveMap_preimage C R R' V).symm)
    (le_of_eq (relSectionsMap_basicOpen C R R' V g))
    ((relCurve C R').basicOpen_le (relSectionsMap C R R' V g)) y).symm

/-- The fibre pullback intertwines the structure actions on the basic open. -/
lemma relBasicPull_overAlgebraMap
    (g : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)) (r : R) :
    relBasicPull C R R' V g
        ((relCurve C R).overAlgebraMap R ((relCurve C R).basicOpen g) r)
      = (relCurve C R').overAlgebraMap R'
          ((relCurve C R').basicOpen (relSectionsMap C R R' V g))
          (algebraMap R R' r) := by
  have h1 : (relCurve C R).overAlgebraMap R ((relCurve C R).basicOpen g) r
      = (relCurve C R).resHom ((relCurve C R).basicOpen_le g)
          ((relCurve C R).overAlgebraMap R ((fst C (overSpec k R)).left ⁻¹ᵁ V) r) :=
    ((relCurve C R).overAlgebraMap_apply_res R
      (homOfLE ((relCurve C R).basicOpen_le g)).op r).symm
  rw [h1, relBasicPull_resHom, relSectionsMap_overAlgebraMap]
  exact (relCurve C R').overAlgebraMap_apply_res R'
    (homOfLE ((relCurve C R').basicOpen_le (relSectionsMap C R R' V g))).op
    (algebraMap R R' r)

/-! ## The multiplication comparisons -/

section MulAux

variable {R R'}

set_option synthInstance.maxHeartbeats 200000 in
-- tensor-algebra instance assembly exceeds the lakefile default
/-- (Implementation) The multiplication comparison induced by a pullback homomorphism
`ψ` compatible with the structure actions: `a ⊗ c ↦ ψ a · ρ c`. -/
private noncomputable def fibreMulAux {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] (ψ : A →+* B) (ρ : R' →+* B)
    (hψρ : ∀ r : R, ψ (algebraMap R A r) = ρ (algebraMap R R' r)) :
    A ⊗[R] R' →+* B :=
  letI : Algebra R' B := ρ.toAlgebra
  letI : Algebra R B := (ρ.comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' B := IsScalarTower.of_algebraMap_eq' rfl
  (Algebra.TensorProduct.productMap
    { toRingHom := ψ, commutes' := hψρ } (IsScalarTower.toAlgHom R R' B)).toRingHom

set_option synthInstance.maxHeartbeats 200000 in
-- tensor-algebra instance assembly exceeds the lakefile default
private lemma fibreMulAux_tmul {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] (ψ : A →+* B) (ρ : R' →+* B)
    (hψρ : ∀ r : R, ψ (algebraMap R A r) = ρ (algebraMap R R' r))
    (a : A) (c : R') :
    fibreMulAux ψ ρ hψρ (a ⊗ₜ c) = ψ a * ρ c := by
  letI : Algebra R' B := ρ.toAlgebra
  letI : Algebra R B := (ρ.comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' B := IsScalarTower.of_algebraMap_eq' rfl
  exact Algebra.TensorProduct.productMap_apply_tmul
    { toRingHom := ψ, commutes' := hψρ } (IsScalarTower.toAlgHom R R' B) a c

end MulAux

set_option synthInstance.maxHeartbeats 400000 in
-- tensor-algebra instance searches on the large section rings exceed the lakefile default
/-- **The chart-level multiplication comparison**
`Γ(C_R, V_R) ⊗[R] R' →+* Γ(C_{R'}, V_{R'})`: `y ⊗ c ↦ relSectionsMap y · c`. -/
noncomputable def relChartFibreMul :
    Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V) ⊗[R] R' →+*
      Γ(relCurve C R', (fst C (overSpec k R')).left ⁻¹ᵁ V) :=
  fibreMulAux (relSectionsMap C R R' V)
    ((relCurve C R').overAlgebraMap R' ((fst C (overSpec k R')).left ⁻¹ᵁ V))
    (fun r => relSectionsMap_overAlgebraMap C R R' V r)

set_option synthInstance.maxHeartbeats 400000 in
-- tensor-algebra instance searches on the large section rings exceed the lakefile default
lemma relChartFibreMul_tmul (y : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V))
    (c : R') :
    relChartFibreMul C R R' V (y ⊗ₜ c)
      = relSectionsMap C R R' V y
        * (relCurve C R').overAlgebraMap R' ((fst C (overSpec k R')).left ⁻¹ᵁ V) c :=
  fibreMulAux_tmul _ _ _ y c

set_option synthInstance.maxHeartbeats 400000 in
-- tensor-algebra instance searches on the large section rings exceed the lakefile default
/-- **The basic-open multiplication comparison**
`Γ(C_R, D(g)) ⊗[R] R' →+* Γ(C_{R'}, D(g'))`. -/
noncomputable def relBasicFibreMul
    (g : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)) :
    Γ(relCurve C R, (relCurve C R).basicOpen g) ⊗[R] R' →+*
      Γ(relCurve C R', (relCurve C R').basicOpen (relSectionsMap C R R' V g)) :=
  fibreMulAux (relBasicPull C R R' V g)
    ((relCurve C R').overAlgebraMap R'
      ((relCurve C R').basicOpen (relSectionsMap C R R' V g)))
    (fun r => relBasicPull_overAlgebraMap C R R' V g r)

set_option synthInstance.maxHeartbeats 400000 in
-- tensor-algebra instance searches on the large section rings exceed the lakefile default
lemma relBasicFibreMul_tmul (g : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V))
    (e : Γ(relCurve C R, (relCurve C R).basicOpen g)) (c : R') :
    relBasicFibreMul C R R' V g (e ⊗ₜ c)
      = relBasicPull C R R' V g e
        * (relCurve C R').overAlgebraMap R'
            ((relCurve C R').basicOpen (relSectionsMap C R R' V g)) c :=
  fibreMulAux_tmul _ _ _ e c

/-! ## Chart-level bijectivity -/

set_option maxHeartbeats 800000 in
-- `relTermBaseChange_tmul`'s statement elaborates through the mixed relCurve/product
-- spellings (heavy defeq checks with `respectTransparency false`), as in its home file
set_option synthInstance.maxHeartbeats 400000 in
/-- **Chart-level bijectivity**: the multiplication comparison agrees with the landed
termwise base change `relTermBaseChange` (composed with the tensor flip) on pure tensors,
hence everywhere, hence is bijective. -/
theorem relChartFibreMul_bijective
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left)) :
    Function.Bijective (relChartFibreMul C R R' V) := by
  have hagree : ⇑(relChartFibreMul C R R' V)
      = fun x => relTermBaseChange C R R' V hV hV'
          (TensorProduct.comm R Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V) R' x) := by
    funext x
    induction x with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul y c =>
      rw [relChartFibreMul_tmul, TensorProduct.comm_tmul, relTermBaseChange_tmul,
        Scheme.overModule_smul_def]
      exact (mul_comm _ _)
  rw [hagree]
  exact (relTermBaseChange C R R' V hV hV').bijective.comp
    (TensorProduct.comm R Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V) R').bijective

/-! ## The restriction tensor and its naturality -/

/-- (Implementation) Restriction of sections as an algebra homomorphism over the base of
an over-scheme (the `Scheme.overSectionsAlgebra` structures). -/
private noncomputable def resOverAlgHom (K : Type u) [CommRing K] (X : Scheme.{u})
    [X.Over (Spec (.of K))] {W U : X.Opens} (h : W ≤ U) :
    Γ(X, U) →ₐ[K] Γ(X, W) :=
  { X.resHom h with
    commutes' := fun r => X.overAlgebraMap_apply_res K (homOfLE h).op r }

private lemma resOverAlgHom_apply (K : Type u) [CommRing K] (X : Scheme.{u})
    [X.Over (Spec (.of K))] {W U : X.Opens} (h : W ≤ U) (s : Γ(X, U)) :
    resOverAlgHom K X h s = X.resHom h s :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- tensor-algebra instance searches on the large section rings exceed the lakefile default
/-- The basic-open comparison intertwines the restriction tensor with the chart-level
comparison followed by restriction. -/
lemma relBasicFibreMul_resTensor
    (g : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V))
    (η : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V) ⊗[R] R') :
    relBasicFibreMul C R R' V g
        (Algebra.TensorProduct.map
          (resOverAlgHom R (relCurve C R) ((relCurve C R).basicOpen_le g))
          (AlgHom.id R R') η)
      = (relCurve C R').resHom
          ((relCurve C R').basicOpen_le (relSectionsMap C R R' V g))
          (relChartFibreMul C R R' V η) := by
  induction η with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul y c =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, resOverAlgHom_apply,
      relBasicFibreMul_tmul, relBasicPull_resHom, relChartFibreMul_tmul, map_mul]
    congr 1
    exact ((relCurve C R').overAlgebraMap_apply_res R'
      (homOfLE ((relCurve C R').basicOpen_le (relSectionsMap C R R' V g))).op c).symm

/-! ## The injectivity keystone -/

set_option maxHeartbeats 1200000 in
-- tensor-algebra instance searches on the large section rings plus the mixed
-- relCurve/product defeq checks exceed the default budget (template: 1d-ii terms)
set_option synthInstance.maxHeartbeats 400000 in
/-- **Injectivity of the basic-open multiplication comparison** (the DDR-3 fibre-sections
identification, injectivity half): both `Γ(C_R, D(g)) ⊗[R] R'` and `Γ(C_{R'}, D(g'))` are
away-localizations of the chart pictures, the chart comparison is bijective, and the
localized element `g|_{D(g)} ⊗ 1` is a unit — so a kernel element is killed by a unit
power after denominator clearing. -/
theorem relBasicFibreMul_injective
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
    (hVaff : IsAffineOpen ((fst C (overSpec k R)).left ⁻¹ᵁ V : (relCurve C R).Opens))
    (hVaff' : IsAffineOpen ((fst C (overSpec k R')).left ⁻¹ᵁ V : (relCurve C R').Opens))
    (g : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)) :
    Function.Injective (relBasicFibreMul C R R' V g) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro ξ hξ
  -- denominator clearing on the `R`-side
  choose u n hu using fun x : Γ(relCurve C R, (relCurve C R).basicOpen g) =>
    hVaff.exists_pow_mul_eq_resHom g rfl ((relCurve C R).basicOpen_le g) x
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset ξ
  set N : ℕ := S.sup fun p => n p.1 with hN
  set gW : Γ(relCurve C R, (relCurve C R).basicOpen g) :=
    (relCurve C R).resHom ((relCurve C R).basicOpen_le g) g with hgW
  -- the cleared numerator on the chart
  set η : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V) ⊗[R] R' :=
    ∑ p ∈ S, (g ^ (N - n p.1) * u p.1) ⊗ₜ p.2 with hη
  -- `(g|_W ⊗ 1)^N · ξ` is the restriction tensor of `η`
  have hclear : (gW ⊗ₜ (1 : R')) ^ N * ξ
      = Algebra.TensorProduct.map
          (resOverAlgHom R (relCurve C R) ((relCurve C R).basicOpen_le g))
          (AlgHom.id R R') η := by
    rw [hS, hη, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, resOverAlgHom_apply,
      Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul]
    congr 1
    have hres : (relCurve C R).resHom ((relCurve C R).basicOpen_le g)
        (g ^ (N - n p.1) * u p.1)
        = gW ^ (N - n p.1) * (relCurve C R).resHom ((relCurve C R).basicOpen_le g)
            (u p.1) := by
      rw [map_mul, map_pow, hgW]
    rw [hres, ← hu p.1, hgW]
    have hle : n p.1 ≤ N := Finset.le_sup (f := fun p => n p.1) hp
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  -- the compared numerator vanishes after restriction to `D(g')`
  have hres0 : (relCurve C R').resHom
      ((relCurve C R').basicOpen_le (relSectionsMap C R R' V g))
      (relChartFibreMul C R R' V η) = 0 := by
    rw [← relBasicFibreMul_resTensor, ← hclear, map_mul, hξ, mul_zero]
  -- kill it by a power of `g'` on the chart
  obtain ⟨m, hm⟩ := hVaff'.exists_pow_mul_eq_zero_of_resHom_eq_zero
    (relSectionsMap C R R' V g) rfl
    ((relCurve C R').basicOpen_le (relSectionsMap C R R' V g))
    (relChartFibreMul C R R' V η) hres0
  -- pull the annihilation back through the bijective chart comparison
  have hη0 : ((g ^ m) ⊗ₜ (1 : R')) * η = 0 := by
    refine (relChartFibreMul_bijective C R R' V hV hV').injective ?_
    rw [map_mul, map_zero, relChartFibreMul_tmul, map_pow, map_one, mul_one]
    exact hm
  -- restrict back to the basic open and cancel the unit
  have hfinal : (gW ⊗ₜ (1 : R')) ^ (m + N) * ξ = 0 := by
    have happly := congrArg (Algebra.TensorProduct.map
      (resOverAlgHom R (relCurve C R) ((relCurve C R).basicOpen_le g))
      (AlgHom.id R R')) hη0
    rw [map_zero, map_mul, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
      resOverAlgHom_apply, map_pow] at happly
    rw [pow_add, mul_assoc, hclear]
    calc (gW ⊗ₜ (1 : R')) ^ m * Algebra.TensorProduct.map
          (resOverAlgHom R (relCurve C R) ((relCurve C R).basicOpen_le g))
          (AlgHom.id R R') η
        = (((relCurve C R).resHom ((relCurve C R).basicOpen_le g) g ^ m) ⊗ₜ (1 : R'))
          * Algebra.TensorProduct.map
            (resOverAlgHom R (relCurve C R) ((relCurve C R).basicOpen_le g))
            (AlgHom.id R R') η := by
          rw [hgW, Algebra.TensorProduct.tmul_pow, one_pow]
      _ = 0 := happly
  -- `g|_{D(g)} ⊗ 1` is a unit
  have hunit : IsUnit (gW ⊗ₜ (1 : R') :
      Γ(relCurve C R, (relCurve C R).basicOpen g) ⊗[R] R') := by
    have hg : IsUnit gW := (relCurve C R).isUnit_resHom_of_eq_basicOpen g rfl
      ((relCurve C R).basicOpen_le g)
    exact hg.map (Algebra.TensorProduct.includeLeft (S := R)).toRingHom
  exact ((hunit.pow (m + N)).mul_right_eq_zero).mp hfinal

/-! ## Fibre regularity at a field fibre -/

section Regularity

/-- On an integral scheme, a section that is nonzero whenever its open is nonempty is a
nonzerodivisor (a domain when the open is nonempty, a subsingleton when it is empty). -/
lemma sections_mem_nonZeroDivisors_of_ne_zero_of_isIntegral {Y : Scheme.{u}}
    [IsIntegral Y] {U : Y.Opens} {t : Γ(Y, U)} (ht : U ≠ ⊥ → t ≠ 0) :
    t ∈ nonZeroDivisors Γ(Y, U) := by
  by_cases hU : U = ⊥
  · haveI := Y.subsingleton_sections_of_le_bot hU.le
    rw [mem_nonZeroDivisors_iff_right]
    intro z _
    exact Subsingleton.elim z 0
  · have hne : ((U : Set Y)).Nonempty := by
      rcases Set.eq_empty_or_nonempty ((U : Set Y)) with h | h
      · exact absurd (by ext y; rw [h]; simp : U = ⊥) hU
      · exact h
    obtain ⟨y, hy⟩ := hne
    haveI : Nonempty U := ⟨⟨y, hy⟩⟩
    haveI : IsDomain Γ(Y, U) := IsIntegral.component_integral U
    exact mem_nonZeroDivisors_of_ne_zero (ht hU)

variable (L : Type u) [Field L] [Algebra k L] [Algebra R L] [IsScalarTower k R L]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

omit [IsProper C.hom] in
/-- The field fibre of the relative curve is integral (`Curve/BaseChangeInstances`,
keyed on the product spelling; `relCurve` is definitionally that product). -/
lemma isIntegral_relCurve_of_field : IsIntegral (relCurve C L) :=
  inferInstanceAs (IsIntegral ((C ⊗ overSpec k L).left))

omit [IsProper C.hom] in
/-- **Nonvanishing descends from the chart to nonempty basic opens of the fibre curve**:
if the compared chart section `relSectionsMap y` is nonzero and the fibre basic open
`D(g')` is nonempty, the pulled-back restriction `relBasicPull (y|_{D(g)})` is nonzero —
restriction between nonempty opens of the integral fibre curve is injective. -/
theorem relBasicPull_resHom_ne_zero_of_relSectionsMap_ne_zero
    (g y : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V))
    (hy : relSectionsMap C R L V y ≠ 0)
    (hne : ((relCurve C L).basicOpen (relSectionsMap C R L V g) : (relCurve C L).Opens)
      ≠ ⊥) :
    relBasicPull C R L V g ((relCurve C R).resHom ((relCurve C R).basicOpen_le g) y)
      ≠ 0 := by
  haveI : IsIntegral (relCurve C L) := isIntegral_relCurve_of_field C L
  rw [relBasicPull_resHom]
  intro h0
  have hne' : ((((relCurve C L).basicOpen (relSectionsMap C R L V g) :
      (relCurve C L).Opens)) : Set (relCurve C L)).Nonempty := by
    rcases Set.eq_empty_or_nonempty
        ((((relCurve C L).basicOpen (relSectionsMap C R L V g) :
          (relCurve C L).Opens)) : Set (relCurve C L)) with h | h
    · exact absurd (by ext z; rw [h]; simp :
        ((relCurve C L).basicOpen (relSectionsMap C R L V g) : (relCurve C L).Opens)
          = ⊥) hne
    · exact h
  obtain ⟨z, hz⟩ := hne'
  haveI : Nonempty ((relCurve C L).basicOpen (relSectionsMap C R L V g)) := ⟨⟨z, hz⟩⟩
  have hinj := AlgebraicGeometry.map_injective_of_isIntegral (relCurve C L)
    (homOfLE ((relCurve C L).basicOpen_le (relSectionsMap C R L V g)))
  apply hy
  refine hinj ?_
  rw [map_zero]
  exact h0

set_option maxHeartbeats 800000 in
-- the nonzerodivisor transport multiplies in the large tensor ring; instance searches
-- and mixed-spelling defeq checks exceed the default budget
set_option synthInstance.maxHeartbeats 400000 in
omit [IsProper C.hom] in
/-- **The fibre-regularity keystone** (the `IsGenerator.fibre_regular` discharge shape):
for `e` a section on the basic open `D(g)` whose fibre pullback is nonzero whenever the
fibre basic open is nonempty, the pure tensor `e ⊗ 1` is a nonzerodivisor in
`Γ(C_R, D(g)) ⊗[R] L` — transported along the injective multiplication comparison into
the sections of the integral fibre curve. -/
theorem tmul_one_mem_nonZeroDivisors_of_relBasicPull
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
    (hVaff : IsAffineOpen ((fst C (overSpec k R)).left ⁻¹ᵁ V : (relCurve C R).Opens))
    (hVaff' : IsAffineOpen ((fst C (overSpec k L)).left ⁻¹ᵁ V : (relCurve C L).Opens))
    (g : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V))
    (e : Γ(relCurve C R, (relCurve C R).basicOpen g))
    (he : ((relCurve C L).basicOpen (relSectionsMap C R L V g) : (relCurve C L).Opens)
        ≠ ⊥ → relBasicPull C R L V g e ≠ 0) :
    e ⊗ₜ[R] (1 : L)
      ∈ nonZeroDivisors (Γ(relCurve C R, (relCurve C R).basicOpen g) ⊗[R] L) := by
  haveI : IsIntegral (relCurve C L) := isIntegral_relCurve_of_field C L
  have hreg : relBasicFibreMul C R L V g (e ⊗ₜ (1 : L))
      ∈ nonZeroDivisors
          Γ(relCurve C L, (relCurve C L).basicOpen (relSectionsMap C R L V g)) := by
    rw [relBasicFibreMul_tmul, map_one, mul_one]
    exact sections_mem_nonZeroDivisors_of_ne_zero_of_isIntegral he
  rw [mem_nonZeroDivisors_iff_right]
  intro z hz
  have h0 : relBasicFibreMul C R L V g z
      * relBasicFibreMul C R L V g (e ⊗ₜ (1 : L)) = 0 := by
    rw [← map_mul, hz, map_zero]
  have hz0 : relBasicFibreMul C R L V g z = 0 :=
    (mul_right_mem_nonZeroDivisors_eq_zero_iff hreg).mp h0
  refine relBasicFibreMul_injective C R L V hV hV' hVaff hVaff' g ?_
  rw [hz0, map_zero]

end Regularity

end AlgebraicGeometry
