/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.TensorFiniteSubextension

/-!
# Algebra maps at finite subextensions

An algebra map between scalar extensions from `F` to an algebraic field extension `K`
is already defined over a finite subextension when its source algebra is of finite type.
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgebraicGeometry.DatG0

/-- A `K`-algebra map between base changes of `F`-algebras descends to a finite
subextension of `K/F` when the source algebra is of finite type. The descended map
commutes with the canonical maps to the original `K`-algebras. -/
theorem exists_finSubext_tensorProduct_algHom
    {F K A B : Type u} [Field F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] [CommRing A] [Algebra F A]
    [Algebra.FiniteType F A] [CommRing B] [Algebra F B]
    (phi : K ⊗[F] A →ₐ[K] K ⊗[F] B) :
    ∃ L : FinSubext F K, ∃ phiL : L.1 ⊗[F] A →ₐ[L.1] L.1 ⊗[F] B,
      (Algebra.TensorProduct.map L.1.val (AlgHom.id F B)).comp
          (phiL.restrictScalars F) =
        (phi.restrictScalars F).comp
          (Algebra.TensorProduct.map L.1.val (AlgHom.id F A)) := by
  let fA : A →ₐ[F] K ⊗[F] B :=
    (phi.restrictScalars F).comp Algebra.TensorProduct.includeRight
  have hfA : fA.range.FG := by
    simpa only [Algebra.map_top] using
      (Subalgebra.FG.map fA Algebra.FiniteType.out)
  obtain ⟨L, g, hg⟩ :=
    exists_finSubext_fg_subalgebra_tensorProduct_factor fA.range hfA
  let fL : A →ₐ[F] L.1 ⊗[F] B := g.comp fA.rangeRestrict
  let phiL : L.1 ⊗[F] A →ₐ[L.1] L.1 ⊗[F] B :=
    AlgHom.liftEquiv F L.1 A (L.1 ⊗[F] B) fL
  have hbase (a : A) :
      (Algebra.TensorProduct.map L.1.val (AlgHom.id F B)) (fL a) = fA a := by
    change ((Algebra.TensorProduct.map L.1.val (AlgHom.id F B)).comp g)
      (fA.rangeRestrict a) = fA a
    rw [hg]
    rfl
  refine ⟨L, phiL, ?_⟩
  ext x
  · change (Algebra.TensorProduct.map L.1.val (AlgHom.id F B))
        (phiL (Algebra.TensorProduct.includeLeft (R := F) (S := L.1)
          (A := L.1) (B := A) x)) =
      phi ((Algebra.TensorProduct.map L.1.val (AlgHom.id F A))
        (Algebra.TensorProduct.includeLeft (R := F) (S := L.1)
          (A := L.1) (B := A) x))
    simp only [Algebra.TensorProduct.includeLeft_apply, phiL, AlgHom.liftEquiv_tmul,
      Algebra.TensorProduct.map_tmul, map_one]
    have hunit :
        (Algebra.TensorProduct.map L.1.val (AlgHom.id F B)) (fL 1) = 1 := by
      calc
        (Algebra.TensorProduct.map L.1.val (AlgHom.id F B)) (fL 1) =
            (Algebra.TensorProduct.map L.1.val (AlgHom.id F B)) 1 :=
          congrArg (Algebra.TensorProduct.map L.1.val (AlgHom.id F B)) fL.map_one'
        _ = 1 := map_one _
    simpa [Algebra.smul_def, hunit] using (phi.commutes (x : K)).symm
  · change (Algebra.TensorProduct.map L.1.val (AlgHom.id F B))
        (phiL (Algebra.TensorProduct.includeRight (R := F) (A := L.1) (B := A) x)) =
      phi ((Algebra.TensorProduct.map L.1.val (AlgHom.id F A))
        (Algebra.TensorProduct.includeRight (R := F) (A := L.1) (B := A) x))
    simp only [Algebra.TensorProduct.includeRight_apply, phiL, AlgHom.liftEquiv_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, one_smul]
    exact hbase x

/-! ## Bundled finite families of descended algebra maps -/

/-- A finite-stage family of algebra maps together with one pinned common stage.

The raw finite-family theorem below exposes the stage and every descended map through
nested existential witnesses.  This record keeps those dependent choices together and
stores the base-change equations at the same stage, so consumers do not have to reopen
the existential or reconstruct the family of maps.
-/
structure FinSubextTensorAlgHomFamilyData
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] {ι : Type*}
    (A B : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)]
    [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)]
    (phi : ∀ i, K ⊗[F] A i →ₐ[K] K ⊗[F] B i) where
  stage : FinSubext F K
  map : ∀ i, stage.1 ⊗[F] A i →ₐ[stage.1] stage.1 ⊗[F] B i
  commutes : ∀ i,
    (Algebra.TensorProduct.map stage.1.val (AlgHom.id F (B i))).comp
        ((map i).restrictScalars F) =
      ((phi i).restrictScalars F).comp
        (Algebra.TensorProduct.map stage.1.val (AlgHom.id F (A i)))

namespace FinSubextTensorAlgHomFamilyData

/-- Package a raw common-stage finite-family witness. -/
theorem of_raw
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] {ι : Type*}
    (A B : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)]
    [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)]
    (phi : ∀ i, K ⊗[F] A i →ₐ[K] K ⊗[F] B i)
    (h : ∃ L : FinSubext F K, ∀ i,
      ∃ phiL : L.1 ⊗[F] A i →ₐ[L.1] L.1 ⊗[F] B i,
        (Algebra.TensorProduct.map L.1.val (AlgHom.id F (B i))).comp
            (phiL.restrictScalars F) =
          ((phi i).restrictScalars F).comp
            (Algebra.TensorProduct.map L.1.val (AlgHom.id F (A i)))) :
    Nonempty (FinSubextTensorAlgHomFamilyData A B phi) := by
  obtain ⟨L, hL⟩ := h
  choose phiL hphiL using hL
  exact ⟨{
    stage := L
    map := phiL
    commutes := hphiL }⟩

/-- Recover the legacy nested-existential shape from a packaged family. -/
theorem exists_raw
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] {ι : Type*}
    (A B : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)]
    [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)]
    (phi : ∀ i, K ⊗[F] A i →ₐ[K] K ⊗[F] B i)
    (D : FinSubextTensorAlgHomFamilyData A B phi) :
    ∃ L : FinSubext F K, ∀ i,
      ∃ phiL : L.1 ⊗[F] A i →ₐ[L.1] L.1 ⊗[F] B i,
        (Algebra.TensorProduct.map L.1.val (AlgHom.id F (B i))).comp
            (phiL.restrictScalars F) =
          ((phi i).restrictScalars F).comp
            (Algebra.TensorProduct.map L.1.val (AlgHom.id F (A i))) := by
  exact ⟨D.stage, fun i => ⟨D.map i, D.commutes i⟩⟩

end FinSubextTensorAlgHomFamilyData

/-- Two algebra maps at a finite tensor stage are equal if their composites with the
canonical map to the ambient algebraic extension are equal.  This is the equation-reflection
step used after spreading inverse and cocycle identities. -/
theorem tensorProduct_algHom_eq_of_map_comp_eq
    {F K A B : Type u} [Field F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] [CommRing A] [Algebra F A]
    [CommRing B] [Algebra F B] (L : FinSubext F K)
    (phi psi : L.1 ⊗[F] A →ₐ[L.1] L.1 ⊗[F] B)
    (h :
      (Algebra.TensorProduct.map L.1.val (AlgHom.id F B)).comp
          (phi.restrictScalars F) =
        (Algebra.TensorProduct.map L.1.val (AlgHom.id F B)).comp
          (psi.restrictScalars F)) :
    phi = psi := by
  apply DFunLike.ext _ _
  intro x
  apply tensorProduct_map_finSubext_injective L
  exact congrArg (fun f => f x) h

/-- A composition identity descends once all three maps commute with base change.  This is
the equation step needed after spreading transition maps: inverse and cocycle identities can
be checked over the ambient algebraic extension and then reflected to the finite stage. -/
theorem tensorProduct_algHom_comp_eq_of_baseChange
    {F K A B D : Type u} [Field F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K]
    [CommRing A] [Algebra F A] [CommRing B] [Algebra F B]
    [CommRing D] [Algebra F D] (L : FinSubext F K)
    (phiL : L.1 ⊗[F] A →ₐ[L.1] L.1 ⊗[F] B)
    (psiL : L.1 ⊗[F] B →ₐ[L.1] L.1 ⊗[F] D)
    (chiL : L.1 ⊗[F] A →ₐ[L.1] L.1 ⊗[F] D)
    (phiK : K ⊗[F] A →ₐ[K] K ⊗[F] B)
    (psiK : K ⊗[F] B →ₐ[K] K ⊗[F] D)
    (chiK : K ⊗[F] A →ₐ[K] K ⊗[F] D)
    (hphi :
      (Algebra.TensorProduct.map L.1.val (AlgHom.id F B)).comp
          (phiL.restrictScalars F) =
        (phiK.restrictScalars F).comp
          (Algebra.TensorProduct.map L.1.val (AlgHom.id F A)))
    (hpsi :
      (Algebra.TensorProduct.map L.1.val (AlgHom.id F D)).comp
          (psiL.restrictScalars F) =
        (psiK.restrictScalars F).comp
          (Algebra.TensorProduct.map L.1.val (AlgHom.id F B)))
    (hchi :
      (Algebra.TensorProduct.map L.1.val (AlgHom.id F D)).comp
          (chiL.restrictScalars F) =
        (chiK.restrictScalars F).comp
          (Algebra.TensorProduct.map L.1.val (AlgHom.id F A)))
    (hK : psiK.comp phiK = chiK) :
    psiL.comp phiL = chiL := by
  apply DFunLike.ext _ _
  intro x
  apply tensorProduct_map_finSubext_injective L
  calc
    (Algebra.TensorProduct.map L.1.val (AlgHom.id F D))
        ((psiL.comp phiL) x) =
      psiK ((Algebra.TensorProduct.map L.1.val (AlgHom.id F B)) (phiL x)) := by
        exact DFunLike.congr_fun hpsi (phiL x)
    _ = psiK (phiK
        ((Algebra.TensorProduct.map L.1.val (AlgHom.id F A)) x)) := by
      exact congrArg psiK (DFunLike.congr_fun hphi x)
    _ = chiK ((Algebra.TensorProduct.map L.1.val (AlgHom.id F A)) x) := by
      exact DFunLike.congr_fun hK
        ((Algebra.TensorProduct.map L.1.val (AlgHom.id F A)) x)
    _ = (Algebra.TensorProduct.map L.1.val (AlgHom.id F D)) (chiL x) := by
      exact (DFunLike.congr_fun hchi x).symm

set_option synthInstance.maxHeartbeats 200000 in
-- The dependent finite family creates one tensor-product algebra instance per member.
/-- A finite family of algebra maps between base changes of `F`-algebras descends to one
common finite subextension of `K/F` when every source algebra is of finite type. -/
theorem exists_finSubext_tensorProduct_algHom_finite
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] {ι : Type*} [Finite ι]
    (A B : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)]
    [∀ i, Algebra.FiniteType F (A i)]
    [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)]
    (phi : ∀ i, K ⊗[F] A i →ₐ[K] K ⊗[F] B i) :
    ∃ L : FinSubext F K, ∀ i,
      ∃ phiL : L.1 ⊗[F] A i →ₐ[L.1] L.1 ⊗[F] B i,
        (Algebra.TensorProduct.map L.1.val (AlgHom.id F (B i))).comp
            (phiL.restrictScalars F) =
          ((phi i).restrictScalars F).comp
            (Algebra.TensorProduct.map L.1.val (AlgHom.id F (A i))) := by
  classical
  letI := Fintype.ofFinite ι
  choose Li phiLi hphiLi using fun i =>
    exists_finSubext_tensorProduct_algHom (phi i)
  let A0i (i : ι) : Subalgebra F K := (Li i).1.toSubalgebra
  have hA0i (i : ι) : (A0i i).FG := by
    rw [Subalgebra.fg_iff_finiteType]
    change Algebra.FiniteType F (Li i).1
    infer_instance
  let A0 : Subalgebra F K := Finset.univ.sup A0i
  have hA0 : A0.FG := by
    dsimp only [A0]
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simpa using (Subalgebra.fg_bot : (⊥ : Subalgebra F K).FG)
    | @insert i s hi hs =>
        simpa [Finset.sup_insert] using (hA0i i).sup hs
  have hA0iA0 : ∀ i, A0i i ≤ A0 := fun i =>
    Finset.le_sup (s := Finset.univ) (f := A0i) (Finset.mem_univ i)
  letI : Algebra.IsAlgebraic F A0 :=
    Algebra.IsAlgebraic.of_injective A0.val Subtype.val_injective
  let L0 : IntermediateField F K := Algebra.IsAlgebraic.toIntermediateField A0
  letI : Algebra.FiniteType F L0 := by
    change Algebra.FiniteType F A0
    exact (Subalgebra.fg_iff_finiteType A0).mp hA0
  letI : Module.Finite F L0 := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let L : FinSubext F K := ⟨L0, inferInstance⟩
  refine ⟨L, ?_⟩
  intro i
  have hLiL : (Li i).1 ≤ L.1 := hA0iA0 i
  let inc : (Li i).1 →ₐ[F] L.1 := IntermediateField.inclusion hLiL
  let fL : A i →ₐ[F] L.1 ⊗[F] B i :=
    (Algebra.TensorProduct.map inc (AlgHom.id F (B i))).comp
      ((phiLi i).restrictScalars F |>.comp
        (Algebra.TensorProduct.includeRight (R := F) (A := (Li i).1) (B := A i)))
  let phiL : L.1 ⊗[F] A i →ₐ[L.1] L.1 ⊗[F] B i :=
    AlgHom.liftEquiv F L.1 (A i) (L.1 ⊗[F] B i) fL
  have hmap :
      (Algebra.TensorProduct.map L.1.val (AlgHom.id F (B i))).comp
          (Algebra.TensorProduct.map inc (AlgHom.id F (B i))) =
        Algebra.TensorProduct.map (Li i).1.val (AlgHom.id F (B i)) := by
    ext x <;> rfl
  refine ⟨phiL, ?_⟩
  ext x
  · change (Algebra.TensorProduct.map L.1.val (AlgHom.id F (B i)))
        (phiL (Algebra.TensorProduct.includeLeft (R := F) (S := L.1)
          (A := L.1) (B := A i) x)) =
      phi i ((Algebra.TensorProduct.map L.1.val (AlgHom.id F (A i)))
        (Algebra.TensorProduct.includeLeft (R := F) (S := L.1)
          (A := L.1) (B := A i) x))
    simp only [Algebra.TensorProduct.includeLeft_apply, phiL, AlgHom.liftEquiv_tmul,
      Algebra.TensorProduct.map_tmul, map_one]
    have hunit :
        (Algebra.TensorProduct.map L.1.val (AlgHom.id F (B i)))
            (fL 1) = 1 := by
      calc
        (Algebra.TensorProduct.map L.1.val (AlgHom.id F (B i))) (fL 1) =
            (Algebra.TensorProduct.map L.1.val (AlgHom.id F (B i))) 1 :=
          congrArg (Algebra.TensorProduct.map L.1.val (AlgHom.id F (B i))) fL.map_one'
        _ = 1 := map_one _
    simpa [Algebra.smul_def, hunit] using ((phi i).commutes (x : K)).symm
  · change (Algebra.TensorProduct.map L.1.val (AlgHom.id F (B i)))
        (phiL (Algebra.TensorProduct.includeRight (R := F) (A := L.1) (B := A i) x)) =
      phi i ((Algebra.TensorProduct.map L.1.val (AlgHom.id F (A i)))
        (Algebra.TensorProduct.includeRight (R := F) (A := L.1) (B := A i) x))
    simp only [Algebra.TensorProduct.includeRight_apply, phiL, AlgHom.liftEquiv_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, one_smul, fL,
      AlgHom.comp_apply]
    rw [← AlgHom.comp_apply, hmap]
    exact DFunLike.congr_fun (hphiLi i)
      (Algebra.TensorProduct.includeRight (R := F) (A := (Li i).1) (B := A i) x)

namespace FinSubextTensorAlgHomFamilyData

/-- Package the finite-family descent theorem. -/
theorem of_exists
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] {ι : Type*} [Finite ι]
    (A B : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)]
    [∀ i, Algebra.FiniteType F (A i)]
    [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)]
    (phi : ∀ i, K ⊗[F] A i →ₐ[K] K ⊗[F] B i) :
    Nonempty (FinSubextTensorAlgHomFamilyData A B phi) :=
  of_raw A B phi (exists_finSubext_tensorProduct_algHom_finite A B phi)

end FinSubextTensorAlgHomFamilyData

end AlgebraicGeometry.DatG0
