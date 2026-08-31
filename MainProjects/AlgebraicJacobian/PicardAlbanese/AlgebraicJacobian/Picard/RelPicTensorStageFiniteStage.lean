/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageDatum
import AlgebraicJacobian.Picard.RelPicPi
import AlgebraicJacobian.Cohomology.GluedSheafExtraction

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

/-! ## Stable finite tensor-stage outputs

The original producers below are retained as compatibility adapters.  Their result types
put algebra and scalar-tower witnesses inside nested `letI` binders, so a propositionally
equal tensor map can acquire a different dependent type at each call site.  The records in
this section expose the stage, its canonical tensor map, and the descended relative Picard
class as one reusable value.  In particular, consumers no longer eliminate a nested
existential before every base-change calculation.
-/

/-- A relative Picard class descended to one named finite tensor stage. -/
structure RelPicTensorStageData
    {F K B : Type u} [Field F] [Field K] [Algebra F K]
    [CommRing B] [Algebra F B]
    {C : Over (Spec (.of F))} (pi : C.left ⟶ P1 F) [IsAffineHom pi]
    (q : relPic C (overSpec F (K ⊗[F] B))) where
  /-- The finite intermediate field used for the descent. -/
  stage : DatG0.FiniteStageData F K
  /-- The relative Picard class over the finite tensor stage. -/
  qStage : relPic C (overSpec F (stage.stage ⊗[F] B))
  /-- Compatibility with the canonical tensor map into the ambient stage. -/
  map_eq : relPicAlgMap C (stage.tensorMap (A := B)) qStage = q

namespace RelPicTensorStageData

/-- The canonical tensor map carried by a stage datum. -/
noncomputable abbrev map
    {F K B : Type u} [Field F] [Field K] [Algebra F K]
    [CommRing B] [Algebra F B]
    {C : Over (Spec (.of F))} (pi : C.left ⟶ P1 F) [IsAffineHom pi]
    {q : relPic C (overSpec F (K ⊗[F] B))}
    (D : RelPicTensorStageData pi q) :
    D.stage.stage ⊗[F] B →ₐ[F] K ⊗[F] B :=
  D.stage.tensorMap (A := B)

@[simp]
theorem compatibility
    {F K B : Type u} [Field F] [Field K] [Algebra F K]
    [CommRing B] [Algebra F B]
    {C : Over (Spec (.of F))} (pi : C.left ⟶ P1 F) [IsAffineHom pi]
    {q : relPic C (overSpec F (K ⊗[F] B))}
    (D : RelPicTensorStageData pi q) :
    relPicAlgMap C (D.map pi) D.qStage = q :=
  D.map_eq

end RelPicTensorStageData

/-- A finite family of relative Picard classes sharing one tensor stage. -/
structure RelPicTensorStageFamilyData
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    {ι : Type*} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)]
    {C : Over (Spec (.of F))} (pi : C.left ⟶ P1 F) [IsAffineHom pi]
    (q : ∀ i, relPic C (overSpec F (K ⊗[F] B i))) where
  /-- The common finite intermediate field. -/
  stage : DatG0.FiniteStageData F K
  /-- The descended relative Picard classes at the common stage. -/
  qStage : ∀ i, relPic C (overSpec F (stage.stage ⊗[F] B i))
  /-- The family of canonical tensor-stage compatibility equations. -/
  map_eq : ∀ i,
    relPicAlgMap C (stage.tensorMap (A := B i)) (qStage i) = q i

namespace RelPicTensorStageFamilyData

/-- The canonical tensor map for one member of a family datum. -/
noncomputable abbrev map
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    {ι : Type*} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)]
    {C : Over (Spec (.of F))} (pi : C.left ⟶ P1 F) [IsAffineHom pi]
    {q : ∀ i, relPic C (overSpec F (K ⊗[F] B i))}
    (D : RelPicTensorStageFamilyData B pi q) (i : ι) :
    D.stage.stage ⊗[F] B i →ₐ[F] K ⊗[F] B i :=
  D.stage.tensorMap (A := B i)

@[simp]
theorem compatibility
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    {ι : Type*} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)]
    {C : Over (Spec (.of F))} (pi : C.left ⟶ P1 F) [IsAffineHom pi]
    {q : ∀ i, relPic C (overSpec F (K ⊗[F] B i))}
    (D : RelPicTensorStageFamilyData B pi q) (i : ι) :
    relPicAlgMap C (D.map B pi i) (D.qStage i) = q i :=
  D.map_eq i

end RelPicTensorStageFamilyData

/-! ## Legacy existential adapters -/

set_option backward.isDefEq.respectTransparency false in
theorem exists_finSubext_relPic_tensorStage
    {F K B : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [CommRing B] [Algebra F B]
    {C : Over (Spec (.of F))} {pi : C.left ⟶ P1 F} [IsAffineHom pi]
    (q : relPic C (overSpec F (K ⊗[F] B))) :
    ∃ M : DatG0.FinSubext F K,
      letI : Algebra F (M.1 ⊗[F] B) := Algebra.TensorProduct.instAlgebra
      let iota : M.1 ⊗[F] B →ₐ[F] K ⊗[F] B :=
        Algebra.TensorProduct.map M.1.val (AlgHom.id F B)
      letI : Algebra (M.1 ⊗[F] B) (K ⊗[F] B) := iota.toAlgebra
      letI : IsScalarTower F (M.1 ⊗[F] B) (K ⊗[F] B) :=
        @IsScalarTower.of_algebraMap_eq F (M.1 ⊗[F] B) (K ⊗[F] B)
          (inferInstance : CommSemiring F)
          (inferInstance : CommSemiring (M.1 ⊗[F] B))
          (inferInstance : Semiring (K ⊗[F] B))
          (Algebra.TensorProduct.instAlgebra (R := F) (A := M.1) (B := B))
          iota.toAlgebra
          (Algebra.TensorProduct.instAlgebra (R := F) (A := K) (B := B))
          (fun x => (iota.commutes x).symm)
      ∃ qM : relPic C (overSpec F (M.1 ⊗[F] B)),
        relPicAlgMap C iota qM = q := by
  obtain ⟨c, hc⟩ := relPicMk_surjective C (overSpec F (K ⊗[F] B)) q
  obtain ⟨D, hD⟩ := BasicOpenCocycleDatum.exists_cechPicClass_eq (π := pi) c
  obtain ⟨M, DM, hDM⟩ := D.exists_finSubext_tensorStage
  refine ⟨M, ?_⟩
  dsimp only
  let iota : M.1 ⊗[F] B →ₐ[F] K ⊗[F] B :=
    Algebra.TensorProduct.map M.1.val (AlgHom.id F B)
  letI : Algebra (M.1 ⊗[F] B) (K ⊗[F] B) := iota.toAlgebra
  letI : IsScalarTower F (M.1 ⊗[F] B) (K ⊗[F] B) :=
    @IsScalarTower.of_algebraMap_eq F (M.1 ⊗[F] B) (K ⊗[F] B)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (fun x => (iota.commutes x).symm)
  refine ⟨relPicMk C (overSpec F (M.1 ⊗[F] B)) DM.cechPicClass, ?_⟩
  rw [relPicAlgMap_mk]
  have hcurve : (C ◁ Over.overSpecMap iota).left =
      relCurveMap C (M.1 ⊗[F] B) (K ⊗[F] B) := by
    refine congrArg (fun g : overSpec F (K ⊗[F] B) ⟶
      overSpec F (M.1 ⊗[F] B) => (C ◁ g).left) ?_
    exact Over.OverMorphism.ext rfl
  rw [hcurve]
  have hclass := (DM.cechPicClass_baseChange (B' := K ⊗[F] B)).symm
  rw [hDM, hD] at hclass
  exact (congrArg (relPicMk C (overSpec F (K ⊗[F] B))) hclass).trans hc

set_option backward.isDefEq.respectTransparency false in
theorem exists_finSubext_relPic_tensorStage_finite
    {F K : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    {ι : Type*} [Finite ι]
    {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)]
    {C : Over (Spec (.of F))} {pi : C.left ⟶ P1 F} [IsAffineHom pi]
    (q : ∀ i, relPic C (overSpec F (K ⊗[F] B i))) :
    ∃ M : DatG0.FinSubext F K,
      ∀ i,
        letI : Algebra F (M.1 ⊗[F] B i) := Algebra.TensorProduct.instAlgebra
        let iota : M.1 ⊗[F] B i →ₐ[F] K ⊗[F] B i :=
          Algebra.TensorProduct.map M.1.val (AlgHom.id F (B i))
        letI : Algebra (M.1 ⊗[F] B i) (K ⊗[F] B i) := iota.toAlgebra
        letI : IsScalarTower F (M.1 ⊗[F] B i) (K ⊗[F] B i) :=
          @IsScalarTower.of_algebraMap_eq F (M.1 ⊗[F] B i) (K ⊗[F] B i)
            (inferInstance : CommSemiring F)
            (inferInstance : CommSemiring (M.1 ⊗[F] B i))
            (inferInstance : Semiring (K ⊗[F] B i))
            (Algebra.TensorProduct.instAlgebra (R := F) (A := M.1) (B := B i))
            iota.toAlgebra
            (Algebra.TensorProduct.instAlgebra (R := F) (A := K) (B := B i))
            (fun x => (iota.commutes x).symm)
        ∃ qM : relPic C (overSpec F (M.1 ⊗[F] B i)),
          relPicAlgMap C iota qM = q i := by
  classical
  letI := Fintype.ofFinite ι
  choose M hM using fun i =>
    exists_finSubext_relPic_tensorStage
      (F := F) (K := K) (B := B i) (C := C) (pi := pi) (q i)
  have hupper_aux : ∀ s : Finset ι,
      ∃ N : DatG0.FinSubext F K, ∀ i ∈ s, M i ≤ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨Classical.choice (inferInstance : Nonempty (DatG0.FinSubext F K)), by
          simp⟩
    | @insert i s hi ih =>
        obtain ⟨N, hN⟩ := ih
        obtain ⟨N', hNN', hiN'⟩ := DatG0.directed_finSubext N (M i)
        refine ⟨N', ?_⟩
        intro j hj
        by_cases hj' : j = i
        · simpa [hj'] using hiN'
        · exact (hN j (Finset.mem_of_mem_insert_of_ne hj hj')).trans hNN'
  obtain ⟨N, hMN⟩ := hupper_aux Finset.univ
  refine ⟨N, ?_⟩
  intro i
  dsimp only at hM
  obtain ⟨qMi, hqi⟩ := hM i
  letI : Algebra F (M i).1 := IntermediateField.algebra' (M i).1
  letI : Algebra F N.1 := IntermediateField.algebra' N.1
  letI : Algebra F ((M i).1 ⊗[F] B i) := Algebra.TensorProduct.instAlgebra
  letI : Algebra F (N.1 ⊗[F] B i) := Algebra.TensorProduct.instAlgebra
  have hMiN : (M i).1 ≤ N.1 := hMN i (Finset.mem_univ i)
  let j : (M i).1 ⊗[F] B i →ₐ[F] N.1 ⊗[F] B i :=
    Algebra.TensorProduct.map (IntermediateField.inclusion hMiN) (AlgHom.id F (B i))
  let iotaN : N.1 ⊗[F] B i →ₐ[F] K ⊗[F] B i :=
    Algebra.TensorProduct.map N.1.val (AlgHom.id F (B i))
  let iotaM : (M i).1 ⊗[F] B i →ₐ[F] K ⊗[F] B i :=
    Algebra.TensorProduct.map (M i).1.val (AlgHom.id F (B i))
  letI : Algebra ((M i).1 ⊗[F] B i) (N.1 ⊗[F] B i) := j.toAlgebra
  letI : Algebra (N.1 ⊗[F] B i) (K ⊗[F] B i) := iotaN.toAlgebra
  letI : IsScalarTower F ((M i).1 ⊗[F] B i) (N.1 ⊗[F] B i) :=
    @IsScalarTower.of_algebraMap_eq F _ _ inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance (fun x => (j.commutes x).symm)
  letI : IsScalarTower F (N.1 ⊗[F] B i) (K ⊗[F] B i) :=
    @IsScalarTower.of_algebraMap_eq F _ _ inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance (fun x => (iotaN.commutes x).symm)
  have hcomp : iotaN.comp j = iotaM := by
    ext x <;> rfl
  refine ⟨relPicAlgMap C j qMi, ?_⟩
  change relPicAlgMap C iotaN (relPicAlgMap C j qMi) = q i
  rw [← relPicAlgMap_comp, hcomp, hqi]

/-! ## Producers for the stable records -/

/-- Produce the stable single-stage record from the legacy finite-stage theorem.

The only use of the legacy nested `letI` result is contained in this adapter; the returned
record has a plain type and can be passed through later constructions unchanged. -/
theorem exists_relPic_tensorStage_data
    {F K B : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [CommRing B] [Algebra F B]
    {C : Over (Spec (.of F))} {pi : C.left ⟶ P1 F} [IsAffineHom pi]
    (q : relPic C (overSpec F (K ⊗[F] B))) :
    Nonempty (RelPicTensorStageData pi q) := by
  obtain ⟨M, hM⟩ := exists_finSubext_relPic_tensorStage
    (F := F) (K := K) (B := B) (C := C) (pi := pi) q
  dsimp only at hM
  obtain ⟨qM, hq⟩ := hM
  let S : DatG0.FiniteStageData F K := DatG0.FiniteStageData.ofFinSubext M
  refine ⟨{ stage := S, qStage := qM, map_eq := ?_ }⟩
  change relPicAlgMap C
      (Algebra.TensorProduct.map M.1.val (AlgHom.id F B)) qM = q
  exact hq

/-- Produce one stable common-stage record for a finite family of relative Picard classes. -/
theorem exists_relPic_tensorStage_family_data
    {F K : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    {ι : Type*} [Finite ι]
    {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)]
    {C : Over (Spec (.of F))} {pi : C.left ⟶ P1 F} [IsAffineHom pi]
    (q : ∀ i, relPic C (overSpec F (K ⊗[F] B i))) :
    Nonempty (RelPicTensorStageFamilyData B pi q) := by
  classical
  obtain ⟨M, hM⟩ := exists_finSubext_relPic_tensorStage_finite
    (F := F) (K := K) (B := B) (C := C) (pi := pi) q
  let S : DatG0.FiniteStageData F K := DatG0.FiniteStageData.ofFinSubext M
  let qStage : ∀ i, relPic C (overSpec F (S.stage ⊗[F] B i)) :=
    fun i => Classical.choose (hM i)
  refine ⟨{ stage := S, qStage := qStage, map_eq := ?_ }⟩
  intro i
  dsimp [qStage, S]
  exact Classical.choose_spec (hM i)

end AlgebraicGeometry
