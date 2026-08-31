/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.TensorFiniteSubextension
import AlgebraicJacobian.Picard.FiniteStageData
import AlgebraicJacobian.Cohomology.DatumDescent
import AlgebraicJacobian.Picard.DivisorFamilyWindowBaseChange

/-!
# Finite tensor-stage descent of a pinned cocycle datum

A `BasicOpenCocycleDatum` over `K ⊗[F] B` descends to a datum over
`M ⊗[F] B` for a finite intermediate field `M/F`.  The datum is first descended to a
finitely generated coefficient subalgebra, then that subalgebra is factored through one
finite tensor stage.  The tower law for datum base change transports the certificate strictly.

The noncomputable `FiniteStageCocycleDatum.choose` operation fixes this witness once at the
producer boundary, so consumers can use the packaged datum and its pinned base-change proof.
-/

set_option autoImplicit false

universe u

open CategoryTheory

open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

/-- Spread a pinned cocycle datum over `K ⊗[F] B` to one finite tensor stage over `F`. -/
theorem BasicOpenCocycleDatum.exists_finSubext_tensorStage
    {F K B : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [CommRing B] [Algebra F B]
    {C : Over (Spec (.of F))} {pi : C.left ⟶ P1 F} [IsAffineHom pi]
    (D : BasicOpenCocycleDatum C (K ⊗[F] B) pi) :
    ∃ M : DatG0.FinSubext F K,
      letI : Algebra F (M.1 ⊗[F] B) := Algebra.TensorProduct.instAlgebra
      let ι : M.1 ⊗[F] B →ₐ[F] K ⊗[F] B :=
        Algebra.TensorProduct.map M.1.val (AlgHom.id F B)
      letI : Algebra (M.1 ⊗[F] B) (K ⊗[F] B) := ι.toAlgebra
      letI : IsScalarTower F (M.1 ⊗[F] B) (K ⊗[F] B) :=
        @IsScalarTower.of_algebraMap_eq F (M.1 ⊗[F] B) (K ⊗[F] B)
          inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
          (fun x => (ι.commutes x).symm)
      ∃ D_M : BasicOpenCocycleDatum C (M.1 ⊗[F] B) pi,
        D_M.baseChange (K ⊗[F] B) = D := by
  obtain ⟨A₀, hA₀, D₀, hD₀⟩ := D.exists_fg_subalgebra_baseChange_eq
  obtain ⟨M, f, hfactor⟩ :=
    DatG0.exists_finSubext_fg_subalgebra_tensorProduct_factor A₀ hA₀
  letI : Algebra F (M.1 ⊗[F] B) := Algebra.TensorProduct.instAlgebra
  let ι : M.1 ⊗[F] B →ₐ[F] K ⊗[F] B :=
    Algebra.TensorProduct.map M.1.val (AlgHom.id F B)
  letI : Algebra A₀ (M.1 ⊗[F] B) :=
    f.toRingHom.toAlgebra' (by
      intro c x
      exact mul_comm (f.toRingHom c) x)
  letI : IsScalarTower F A₀ (M.1 ⊗[F] B) :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  letI : Algebra (M.1 ⊗[F] B) (K ⊗[F] B) :=
    ι.toRingHom.toAlgebra' (by
      intro c x
      exact mul_comm (ι.toRingHom c) x)
  letI : IsScalarTower F (M.1 ⊗[F] B) (K ⊗[F] B) :=
    @IsScalarTower.of_algebraMap_eq F (M.1 ⊗[F] B) (K ⊗[F] B)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (fun x => (ι.commutes x).symm)
  letI : IsScalarTower A₀ (M.1 ⊗[F] B) (K ⊗[F] B) :=
    @IsScalarTower.of_algebraMap_eq A₀ (M.1 ⊗[F] B) (K ⊗[F] B)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (fun a => by
        change a.1 = ι (f a)
        exact congrArg (fun g : A₀ →ₐ[F] K ⊗[F] B => g a) hfactor.symm)
  refine ⟨M, ?_⟩
  dsimp only
  exact ⟨D₀.baseChange (M.1 ⊗[F] B),
    (D₀.baseChange_baseChange C (A₀ : Type u) (M.1 ⊗[F] B) (K ⊗[F] B)).trans hD₀⟩

/-- Package the finite tensor-stage descent witness as `FiniteStageData`.

This is an additive adapter for consumers that need to retain the stage and
its finite-dimensionality witness as a single object.  The explicit local
instances mirror `exists_finSubext_tensorStage`, so the resulting datum has
the same canonical tensor-stage map.
-/
theorem BasicOpenCocycleDatum.exists_finiteStageData_tensorStage
    {F K B : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [CommRing B] [Algebra F B]
    {C : Over (Spec (.of F))} {pi : C.left ⟶ P1 F} [IsAffineHom pi]
    (D : BasicOpenCocycleDatum C (K ⊗[F] B) pi) :
    ∃ S : DatG0.FiniteStageData F K,
      letI : Algebra F (S.stage ⊗[F] B) := Algebra.TensorProduct.instAlgebra
      let ι : S.stage ⊗[F] B →ₐ[F] K ⊗[F] B :=
        Algebra.TensorProduct.map S.inclusion (AlgHom.id F B)
      letI : Algebra (S.stage ⊗[F] B) (K ⊗[F] B) := ι.toAlgebra
      letI : IsScalarTower F (S.stage ⊗[F] B) (K ⊗[F] B) :=
        @IsScalarTower.of_algebraMap_eq F (S.stage ⊗[F] B) (K ⊗[F] B)
          inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
          (fun x => (ι.commutes x).symm)
      ∃ D_M : BasicOpenCocycleDatum C (S.stage ⊗[F] B) pi,
        D_M.baseChange (K ⊗[F] B) = D := by
  obtain ⟨M, hM⟩ := D.exists_finSubext_tensorStage
  refine ⟨DatG0.FiniteStageData.ofFinSubext M, ?_⟩
  dsimp [DatG0.FiniteStageData.ofFinSubext]
  exact hM

/-! ## Stable finite-stage cocycle data

`exists_finiteStageData_tensorStage` is retained for compatibility, but its result still
contains a chain of local instances.  The record below names the stage, the descended datum,
and the exact tensor algebra/tower used for the comparison.  Consumers can therefore carry one
value across later base-change lemmas without reopening the existential or asking typeclass
search to choose a different action.
-/

/-- A cocycle datum together with one pinned finite tensor stage over which it descends. -/
structure FiniteStageCocycleDatum
    {F K B : Type u} [Field F] [Field K] [Algebra F K]
    [CommRing B] [Algebra F B]
    {C : Over (Spec (.of F))} {pi : C.left ⟶ P1 F} [IsAffineHom pi]
    (D : BasicOpenCocycleDatum C (K ⊗[F] B) pi) where
  stage : DatG0.FiniteStageData F K
  datum : BasicOpenCocycleDatum C (stage.stage ⊗[F] B) pi
  baseChange_eq :
    letI : Algebra (stage.stage ⊗[F] B) (K ⊗[F] B) :=
      stage.tensorAlgebra (A := B)
    letI : IsScalarTower F (stage.stage ⊗[F] B) (K ⊗[F] B) :=
      stage.tensorTower (A := B)
    datum.baseChange (B' := K ⊗[F] B) = D

namespace FiniteStageCocycleDatum

/-- The canonical map from the selected finite tensor stage to the ambient tensor product. -/
abbrev map
    {F K B : Type u} [Field F] [Field K] [Algebra F K]
    [CommRing B] [Algebra F B]
    {C : Over (Spec (.of F))} {pi : C.left ⟶ P1 F} [IsAffineHom pi]
    {D : BasicOpenCocycleDatum C (K ⊗[F] B) pi}
    (P : FiniteStageCocycleDatum D) :
    P.stage.stage ⊗[F] B →ₐ[F] K ⊗[F] B :=
  P.stage.tensorMap (A := B)

/-! The record field above preserves the historical existential shape.  This theorem is the
    migration boundary for consumers: every algebra and tower witness is an explicit argument
    of `baseChange`, so the equality no longer depends on whichever instances happen to be in
    scope at the call site. -/

theorem baseChange_eq_pinned
    {F K B : Type u} [Field F] [Field K] [Algebra F K]
    [CommRing B] [Algebra F B]
    {C : Over (Spec (.of F))} {pi : C.left ⟶ P1 F} [IsAffineHom pi]
    {D : BasicOpenCocycleDatum C (K ⊗[F] B) pi}
    (P : FiniteStageCocycleDatum D) :
    @BasicOpenCocycleDatum.baseChange F (inferInstance : Field F) C
      (P.stage.stage ⊗[F] B)
      (inferInstance : CommRing (P.stage.stage ⊗[F] B))
      (inferInstance : Algebra F (P.stage.stage ⊗[F] B))
      (K ⊗[F] B)
      (inferInstance : CommRing (K ⊗[F] B))
      (inferInstance : Algebra F (K ⊗[F] B))
      (P.stage.tensorAlgebra (A := B))
      (P.stage.tensorTower (A := B))
      pi
      (inferInstance : IsAffineHom pi)
      P.datum = D := by
  letI : Algebra (P.stage.stage ⊗[F] B) (K ⊗[F] B) :=
    P.stage.tensorAlgebra (A := B)
  letI : IsScalarTower F (P.stage.stage ⊗[F] B) (K ⊗[F] B) :=
    P.stage.tensorTower (A := B)
  simpa only using P.baseChange_eq

/-- Package the legacy nested existential without changing its selected witnesses. -/
theorem of_raw
    {F K B : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [CommRing B] [Algebra F B]
    {C : Over (Spec (.of F))} {pi : C.left ⟶ P1 F} [IsAffineHom pi]
    (D : BasicOpenCocycleDatum C (K ⊗[F] B) pi) :
    Nonempty (FiniteStageCocycleDatum D) := by
  obtain ⟨S, hS⟩ := D.exists_finiteStageData_tensorStage
  dsimp only at hS
  obtain ⟨D_M, hD⟩ := hS
  exact ⟨{ stage := S, datum := D_M, baseChange_eq := hD }⟩

/-- Select one finite-stage cocycle datum from the legacy existential producer.

The choice is made once at the producer boundary, so consumers can retain the
stage, descended datum, and pinned comparison certificate as one value. -/
noncomputable def choose
    {F K B : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [CommRing B] [Algebra F B]
    {C : Over (Spec (.of F))} {pi : C.left ⟶ P1 F} [IsAffineHom pi]
    (D : BasicOpenCocycleDatum C (K ⊗[F] B) pi) :
    FiniteStageCocycleDatum D :=
  Classical.choice (of_raw D)

theorem choose_baseChange_eq_pinned
    {F K B : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [CommRing B] [Algebra F B]
    {C : Over (Spec (.of F))} {pi : C.left ⟶ P1 F} [IsAffineHom pi]
    (D : BasicOpenCocycleDatum C (K ⊗[F] B) pi) :
    @BasicOpenCocycleDatum.baseChange F (inferInstance : Field F) C
      ((choose D).stage.stage ⊗[F] B)
      (inferInstance : CommRing ((choose D).stage.stage ⊗[F] B))
      (inferInstance : Algebra F ((choose D).stage.stage ⊗[F] B))
      (K ⊗[F] B)
      (inferInstance : CommRing (K ⊗[F] B))
      (inferInstance : Algebra F (K ⊗[F] B))
      ((choose D).stage.tensorAlgebra (A := B))
      ((choose D).stage.tensorTower (A := B))
      pi
      (inferInstance : IsAffineHom pi)
      (choose D).datum = D := by
  exact (choose D).baseChange_eq_pinned

@[simp]
theorem map_apply_tmul
    {F K B : Type u} [Field F] [Field K] [Algebra F K]
    [CommRing B] [Algebra F B]
    {C : Over (Spec (.of F))} {pi : C.left ⟶ P1 F} [IsAffineHom pi]
    {D : BasicOpenCocycleDatum C (K ⊗[F] B) pi}
    (P : FiniteStageCocycleDatum D) (x : P.stage.stage) (b : B) :
    P.map (x ⊗ₜ[F] b) = (x : K) ⊗ₜ[F] b := by
  exact P.stage.tensorMap_apply_tmul x b

end FiniteStageCocycleDatum

end

end AlgebraicGeometry
