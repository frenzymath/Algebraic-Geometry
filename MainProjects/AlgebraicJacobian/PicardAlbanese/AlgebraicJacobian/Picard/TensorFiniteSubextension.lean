/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicRepColimitResidual
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.TensorProduct.DirectLimitFG

/-!
# Tensor products over algebraic extensions at finite subextensions

Elements and equalities in a tensor product with an algebraic field extension are already
defined at finite intermediate extensions.  These are finite-field wrappers around the
finitely generated subalgebra results in `Mathlib.RingTheory.TensorProduct.DirectLimitFG`.
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgebraicGeometry.DatG0

/-- Every element of `K ⊗[F] B` comes from `L ⊗[F] B` for some finite subextension
`L/F` of an algebraic extension `K/F`. -/
theorem exists_finSubext_tensorProduct_preimage
    {F K B : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [CommRing B] [Algebra F B] (x : K ⊗[F] B) :
    ∃ L : FinSubext F K, ∃ xL : L.1 ⊗[F] B,
      LinearMap.rTensor B L.1.val.toLinearMap xL = x := by
  obtain ⟨A, hA, xA, hxA⟩ := TensorProduct.Algebra.exists_of_fg x
  letI : Algebra.IsAlgebraic F A :=
    Algebra.IsAlgebraic.of_injective A.val Subtype.val_injective
  let L0 : IntermediateField F K := Algebra.IsAlgebraic.toIntermediateField A
  letI : Algebra.FiniteType F L0 := by
    change Algebra.FiniteType F A
    exact (Subalgebra.fg_iff_finiteType A).mp hA
  letI : Module.Finite F L0 := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let L : FinSubext F K := ⟨L0, inferInstance⟩
  exact ⟨L, xA, hxA⟩

/-- If two tensors over a finite subextension become equal over `K`, they are already equal
after passage to some larger finite subextension. -/
theorem exists_finSubext_tensorProduct_eq
    {F K B : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [CommRing B] [Algebra F B] (L : FinSubext F K) (x y : L.1 ⊗[F] B)
    (hxy : LinearMap.rTensor B L.1.val.toLinearMap x =
      LinearMap.rTensor B L.1.val.toLinearMap y) :
    ∃ M : FinSubext F K, ∃ hLM : L.1 ≤ M.1,
      LinearMap.rTensor B (IntermediateField.inclusion hLM).toLinearMap x =
        LinearMap.rTensor B (IntermediateField.inclusion hLM).toLinearMap y := by
  have hLfg : L.1.toSubalgebra.FG := by
    rw [Subalgebra.fg_iff_finiteType]
    change Algebra.FiniteType F L.1
    infer_instance
  obtain ⟨A, hLA, hA, hxyA⟩ :=
    TensorProduct.Algebra.eq_of_fg_of_subtype_eq hLfg hxy
  letI : Algebra.IsAlgebraic F A :=
    Algebra.IsAlgebraic.of_injective A.val Subtype.val_injective
  let M0 : IntermediateField F K := Algebra.IsAlgebraic.toIntermediateField A
  letI : Algebra.FiniteType F M0 := by
    change Algebra.FiniteType F A
    exact (Subalgebra.fg_iff_finiteType A).mp hA
  letI : Module.Finite F M0 := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let M : FinSubext F K := ⟨M0, inferInstance⟩
  have hLM : L.1 ≤ M.1 := hLA
  exact ⟨M, hLM, hxyA⟩

/-- A finite family of elements of `K ⊗[F] B` comes from one common finite
subextension of `K/F`. -/
theorem exists_finSubext_tensorProduct_preimage_finite
    {F K B : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [CommRing B] [Algebra F B] {iota : Type*} [Finite iota]
    (x : iota → K ⊗[F] B) :
    ∃ L : FinSubext F K, ∃ xL : iota → L.1 ⊗[F] B,
      ∀ i, LinearMap.rTensor B L.1.val.toLinearMap (xL i) = x i := by
  classical
  letI := Fintype.ofFinite iota
  choose A hA xA hxA using fun i => TensorProduct.Algebra.exists_of_fg (x i)
  let A0 : Subalgebra F K := Finset.univ.sup A
  have hA0 : A0.FG := by
    dsimp only [A0]
    induction (Finset.univ : Finset iota) using Finset.induction_on with
    | empty => simpa using (Subalgebra.fg_bot : (⊥ : Subalgebra F K).FG)
    | @insert i s hi hs =>
        simpa [Finset.sup_insert] using (hA i).sup hs
  have hAA0 : ∀ i, A i ≤ A0 := fun i =>
    Finset.le_sup (s := Finset.univ) (f := A) (Finset.mem_univ i)
  let xA0 : iota → A0 ⊗[F] B := fun i =>
    LinearMap.rTensor B (Subalgebra.inclusion (hAA0 i)).toLinearMap (xA i)
  have hxA0 : ∀ i, LinearMap.rTensor B A0.val.toLinearMap (xA0 i) = x i := by
    intro i
    have hcomp :
        A0.val.toLinearMap.comp (Subalgebra.inclusion (hAA0 i)).toLinearMap =
          (A i).val.toLinearMap := by
      ext
      rfl
    dsimp only [xA0]
    rw [← LinearMap.rTensor_comp_apply, hcomp]
    exact hxA i
  letI : Algebra.IsAlgebraic F A0 :=
    Algebra.IsAlgebraic.of_injective A0.val Subtype.val_injective
  let L0 : IntermediateField F K := Algebra.IsAlgebraic.toIntermediateField A0
  letI : Algebra.FiniteType F L0 := by
    change Algebra.FiniteType F A0
    exact (Subalgebra.fg_iff_finiteType A0).mp hA0
  letI : Module.Finite F L0 := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let L : FinSubext F K := ⟨L0, inferInstance⟩
  exact ⟨L, xA0, hxA0⟩

/-! ## Bundled finite-stage presentations -/

/-- A finite family of tensors presented at one pinned finite subextension.

The older existential theorem returns the stage, the family of preimages, and the
compatibility equations as three nested witnesses.  This record keeps the stage and
the map that transports it to `K` together, so consumers do not have to reconstruct
the map (or unfold a `LinearMap.rTensor`) at every use site.
-/
structure FinSubextTensorPreimageFamilyData
    (F K B : Type u) [Field F] [Field K] [Algebra F K]
    [CommRing B] [Algebra F B] {ι : Type*}
    (x : ι → K ⊗[F] B) where
  stage : FinSubext F K
  map : stage.1 ⊗[F] B →ₐ[F] K ⊗[F] B
  map_spec : map = Algebra.TensorProduct.map stage.1.val (AlgHom.id F B)
  preimage : ι → stage.1 ⊗[F] B
  map_eq : ∀ i, map (preimage i) = x i

namespace FinSubextTensorPreimageFamilyData

/-- Package the raw common-stage finite-family theorem. -/
theorem of_raw
    {F K B : Type u} [Field F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] [CommRing B] [Algebra F B]
    {ι : Type*} [Finite ι] (x : ι → K ⊗[F] B) :
    Nonempty (FinSubextTensorPreimageFamilyData F K B x) := by
  obtain ⟨L, xL, hxL⟩ :=
    exists_finSubext_tensorProduct_preimage_finite (x := x)
  let ιL : L.1 ⊗[F] B →ₐ[F] K ⊗[F] B :=
    Algebra.TensorProduct.map L.1.val (AlgHom.id F B)
  refine ⟨{
    stage := L
    map := ιL
    map_spec := by rfl
    preimage := xL
    map_eq := ?_ }⟩
  intro i
  change LinearMap.rTensor B L.1.val.toLinearMap (xL i) = x i
  exact hxL i

@[simp]
theorem map_apply_tmul
    {F K B : Type u} [Field F] [Field K] [Algebra F K]
    [CommRing B] [Algebra F B]
    {ι : Type*} {x : ι → K ⊗[F] B}
    (D : FinSubextTensorPreimageFamilyData F K B x)
    (a : D.stage.1) (b : B) :
    D.map (a ⊗ₜ[F] b) = (a : K) ⊗ₜ[F] b := by
  rw [D.map_spec]
  rfl

end FinSubextTensorPreimageFamilyData

/-- The canonical map from a finite tensor stage into the tensor product over `K` is injective.
This is flatness of `B` over the field `F`, expressed through the tensor-product algebra map. -/
theorem tensorProduct_map_finSubext_injective
    {F K B : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [CommRing B] [Algebra F B] (L : FinSubext F K) :
    Function.Injective
      (Algebra.TensorProduct.map L.1.val (AlgHom.id F B) :
        L.1 ⊗[F] B →ₐ[F] K ⊗[F] B) := by
  have hmap :
      (Algebra.TensorProduct.map L.1.val (AlgHom.id F B) :
        L.1 ⊗[F] B →ₐ[F] K ⊗[F] B).toLinearMap =
        LinearMap.rTensor B L.1.val.toLinearMap := by
    ext x b
    rfl
  have hinj : Function.Injective (LinearMap.rTensor B L.1.val.toLinearMap) :=
    Module.Flat.rTensor_preserves_injective_linearMap
      L.1.val.toLinearMap Subtype.val_injective
  rw [← hmap] at hinj
  exact hinj

/-- A finitely generated subalgebra of `K ⊗[F] B` factors through one finite tensor stage.
The factorization is an algebra map, so it can be used directly to base-change a cocycle datum. -/
theorem exists_finSubext_fg_subalgebra_tensorProduct_factor
    {F K B : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [CommRing B] [Algebra F B]
    (A₀ : Subalgebra F (K ⊗[F] B)) (hA₀ : A₀.FG) :
    ∃ (M : FinSubext F K) (f : A₀ →ₐ[F] M.1 ⊗[F] B),
      (Algebra.TensorProduct.map M.1.val (AlgHom.id F B)).comp f = A₀.val := by
  classical
  obtain ⟨s, hsfinite, hs⟩ := Subalgebra.fg_def.mp hA₀
  letI : Finite s := hsfinite.to_subtype
  obtain ⟨M, xM, hxM⟩ :=
    exists_finSubext_tensorProduct_preimage_finite
      (x := fun a : s => (a.1 : K ⊗[F] B))
  let ι : M.1 ⊗[F] B →ₐ[F] K ⊗[F] B :=
    Algebra.TensorProduct.map M.1.val (AlgHom.id F B)
  have hmap : ι.toLinearMap = LinearMap.rTensor B M.1.val.toLinearMap := by
    ext x b
    rfl
  have hsrange : s ⊆ (ι.range : Set (K ⊗[F] B)) := by
    intro x hx
    refine ⟨xM ⟨x, hx⟩, ?_⟩
    change ι.toLinearMap (xM ⟨x, hx⟩) = x
    rw [hmap]
    exact hxM ⟨x, hx⟩
  have hArange : A₀ ≤ ι.range := by
    rw [← hs]
    exact Algebra.adjoin_le hsrange
  have hι : Function.Injective ι := tensorProduct_map_finSubext_injective M
  let e : M.1 ⊗[F] B ≃ₐ[F] ι.range := AlgEquiv.ofInjective ι hι
  let f : A₀ →ₐ[F] M.1 ⊗[F] B :=
    e.symm.toAlgHom.comp (Subalgebra.inclusion hArange)
  refine ⟨M, f, ?_⟩
  ext a
  change ι (e.symm ⟨a.1, hArange a.2⟩) = a.1
  exact congrArg Subtype.val (e.apply_symm_apply ⟨a.1, hArange a.2⟩)

/-! ## Bundled finite tensor factors -/

/-- A finitely generated tensor subalgebra together with its pinned finite factor.

The legacy factorization theorem returns the finite stage, factor map, and compatibility
equation as nested witnesses.  This record retains the canonical tensor map alongside those
witnesses, so downstream consumers can use one stable carrier without re-synthesizing its
`AlgHom` structure.
-/
structure FinSubextTensorFactorData
    (F K B : Type u) [Field F] [Field K] [Algebra F K]
    [CommRing B] [Algebra F B]
    (A₀ : Subalgebra F (K ⊗[F] B)) where
  stage : FinSubext F K
  map : stage.1 ⊗[F] B →ₐ[F] K ⊗[F] B
  map_spec : map = Algebra.TensorProduct.map stage.1.val (AlgHom.id F B)
  factor : A₀ →ₐ[F] stage.1 ⊗[F] B
  factor_spec : map.comp factor = A₀.val

namespace FinSubextTensorFactorData

/-- Package the raw finitely generated tensor-factor theorem. -/
theorem of_raw
    {F K B : Type u} [Field F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] [CommRing B] [Algebra F B]
    (A₀ : Subalgebra F (K ⊗[F] B)) (hA₀ : A₀.FG) :
    Nonempty (FinSubextTensorFactorData F K B A₀) := by
  obtain ⟨M, f, hf⟩ :=
    exists_finSubext_fg_subalgebra_tensorProduct_factor A₀ hA₀
  let map : M.1 ⊗[F] B →ₐ[F] K ⊗[F] B :=
    Algebra.TensorProduct.map M.1.val (AlgHom.id F B)
  refine ⟨{
    stage := M
    map := map
    map_spec := by rfl
    factor := f
    factor_spec := ?_ }⟩
  simpa only [map] using hf

end FinSubextTensorFactorData

/-- A finite family of tensor equalities that holds over `K` already holds over one common
finite subextension containing the original stage. -/
theorem exists_finSubext_tensorProduct_eq_finite
    {F K B : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [CommRing B] [Algebra F B] {iota : Type*} [Finite iota]
    (L : FinSubext F K) (x y : iota → L.1 ⊗[F] B)
    (hxy : ∀ i, LinearMap.rTensor B L.1.val.toLinearMap (x i) =
      LinearMap.rTensor B L.1.val.toLinearMap (y i)) :
    ∃ M : FinSubext F K, ∃ hLM : L.1 ≤ M.1, ∀ i,
      LinearMap.rTensor B (IntermediateField.inclusion hLM).toLinearMap (x i) =
        LinearMap.rTensor B (IntermediateField.inclusion hLM).toLinearMap (y i) := by
  classical
  letI := Fintype.ofFinite iota
  have hLfg : L.1.toSubalgebra.FG := by
    rw [Subalgebra.fg_iff_finiteType]
    change Algebra.FiniteType F L.1
    infer_instance
  choose A hLA hA hxyA using fun i =>
    TensorProduct.Algebra.eq_of_fg_of_subtype_eq hLfg (hxy i)
  let A0 : Subalgebra F K := L.1.toSubalgebra ⊔ Finset.univ.sup A
  have hA0 : A0.FG := by
    apply hLfg.sup
    induction (Finset.univ : Finset iota) using Finset.induction_on with
    | empty => simpa using (Subalgebra.fg_bot : (⊥ : Subalgebra F K).FG)
    | @insert i s hi hs =>
        simpa [Finset.sup_insert] using (hA i).sup hs
  have hLA0 : L.1.toSubalgebra ≤ A0 := le_sup_left
  have hAA0 : ∀ i, A i ≤ A0 := fun i =>
    (Finset.le_sup (s := Finset.univ) (f := A) (Finset.mem_univ i)).trans le_sup_right
  have hxyA0 : ∀ i,
      LinearMap.rTensor B (Subalgebra.inclusion hLA0).toLinearMap (x i) =
        LinearMap.rTensor B (Subalgebra.inclusion hLA0).toLinearMap (y i) := by
    intro i
    have hi := congrArg
      (LinearMap.rTensor B (Subalgebra.inclusion (hAA0 i)).toLinearMap) (hxyA i)
    have hcomp :
        (Subalgebra.inclusion (hAA0 i)).toLinearMap.comp
            (Subalgebra.inclusion (hLA i)).toLinearMap =
          (Subalgebra.inclusion hLA0).toLinearMap := by
      ext
      rfl
    simpa only [← LinearMap.rTensor_comp_apply, hcomp] using hi
  letI : Algebra.IsAlgebraic F A0 :=
    Algebra.IsAlgebraic.of_injective A0.val Subtype.val_injective
  let M0 : IntermediateField F K := Algebra.IsAlgebraic.toIntermediateField A0
  letI : Algebra.FiniteType F M0 := by
    change Algebra.FiniteType F A0
    exact (Subalgebra.fg_iff_finiteType A0).mp hA0
  letI : Module.Finite F M0 := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let M : FinSubext F K := ⟨M0, inferInstance⟩
  have hLM : L.1 ≤ M.1 := hLA0
  exact ⟨M, hLM, hxyA0⟩

/-! ## Bundled finite-stage equality families -/

/-- A family of tensor equalities together with one finite stage containing the original
stage.  The transported equality is stored as a field, so consumers can keep the chosen
stage and inclusion without reopening the nested existential returned by
`exists_finSubext_tensorProduct_eq_finite`. -/
structure FiniteStageTensorEqualityFamilyData
    (F K B : Type u) [Field F] [Field K] [Algebra F K]
    [CommRing B] [Algebra F B] {ι : Type*}
    (L : FinSubext F K) (x y : ι → L.1 ⊗[F] B) where
  stage : FinSubext F K
  inclusion : L.1 ≤ stage.1
  map : L.1 →ₐ[F] stage.1
  map_spec : map = IntermediateField.inclusion inclusion
  equality : ∀ i,
    LinearMap.rTensor B map.toLinearMap (x i) =
      LinearMap.rTensor B map.toLinearMap (y i)

namespace FiniteStageTensorEqualityFamilyData

/-- Package the raw common-stage finite-family equality theorem. -/
theorem of_raw
    {F K B : Type u} [Field F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] [CommRing B] [Algebra F B]
    {ι : Type*} [Finite ι]
    (L : FinSubext F K) (x y : ι → L.1 ⊗[F] B)
    (hxy : ∀ i, LinearMap.rTensor B L.1.val.toLinearMap (x i) =
      LinearMap.rTensor B L.1.val.toLinearMap (y i)) :
    Nonempty (FiniteStageTensorEqualityFamilyData F K B L x y) := by
  obtain ⟨M, hLM, hM⟩ :=
    exists_finSubext_tensorProduct_eq_finite (L := L) (x := x) (y := y) hxy
  exact ⟨{
    stage := M
    inclusion := hLM
    map := IntermediateField.inclusion hLM
    map_spec := rfl
    equality := hM }⟩

theorem equality_apply
    {F K B : Type u} [Field F] [Field K] [Algebra F K]
    [CommRing B] [Algebra F B] {ι : Type*}
    {L : FinSubext F K} {x y : ι → L.1 ⊗[F] B}
    (D : FiniteStageTensorEqualityFamilyData F K B L x y) (i : ι) :
    LinearMap.rTensor B D.map.toLinearMap (x i) =
      LinearMap.rTensor B D.map.toLinearMap (y i) :=
  D.equality i

/-- Recover the legacy nested-existential shape from a packaged equality family. -/
theorem exists_raw
    {F K B : Type u} [Field F] [Field K] [Algebra F K]
    [CommRing B] [Algebra F B] {ι : Type*}
    {L : FinSubext F K} {x y : ι → L.1 ⊗[F] B}
    (D : FiniteStageTensorEqualityFamilyData F K B L x y) :
    ∃ M : FinSubext F K, ∃ hLM : L.1 ≤ M.1, ∀ i,
      LinearMap.rTensor B (IntermediateField.inclusion hLM).toLinearMap (x i) =
        LinearMap.rTensor B (IntermediateField.inclusion hLM).toLinearMap (y i) :=
  ⟨D.stage, D.inclusion, fun i => by
    simpa only [D.map_spec] using D.equality i⟩

end FiniteStageTensorEqualityFamilyData

end AlgebraicGeometry.DatG0
