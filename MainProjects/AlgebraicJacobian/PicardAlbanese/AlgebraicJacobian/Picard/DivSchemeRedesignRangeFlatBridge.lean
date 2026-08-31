/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRelDivisor
import AlgebraicJacobian.Picard.DivSchemeRedesignSeedFinish

/-!
# DD-4 redesign: the valid flat-range fibre bridge

Let `P ≤ M` be an `R`-linear range and let `L ≤ P`.  There is a canonical exact
sequence `0 → map (L.mkQ) P → M/L → M/P → 0`.

If `M/P` is `R`-flat, the first map stays injective after tensoring with every
`R`-module.  Consequently, if the image `map (L.mkQ) P` dies in a residue-field
fibre of `M/L`, its own tensor fibre is zero.  The containment `L ≤ P` is essential:
`e ∈ P` alone does not imply `(e) ⊆ P` for an `R`-linear submodule.  For example,
with `R = k`, `M = k[t]`, `P = k · t`, and `e = t`, one has `e ∈ P` but `t² ∉ P`.
No ideal-flatness claim is made here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uR uM u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

namespace FlatRangeBridge

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- The image of `P` in the quotient by `L`. -/
noncomputable def imageInQuotient (L P : Submodule R M) : Submodule R (M ⧸ L) :=
  Submodule.map L.mkQ P

/-- Image of a range in a quotient, written as the range of the composite quotient map. -/
lemma imageInQuotient_range (L : Submodule R M) {U : Type*}
    [AddCommGroup U] [Module R U] (f : U →ₗ[R] M) :
    imageInQuotient L (LinearMap.range f) = LinearMap.range (L.mkQ.comp f) := by
  rw [imageInQuotient, ← LinearMap.range_comp]

/-- The quotient map induced by `L ≤ P`. -/
noncomputable def quotientMapOfLE {L P : Submodule R M} (hLP : L ≤ P) :
    (M ⧸ L) →ₗ[R] (M ⧸ P) :=
  L.liftQ P.mkQ fun x hx => by
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hLP hx

@[simp]
lemma quotientMapOfLE_mk {L P : Submodule R M} (hLP : L ≤ P) (x : M) :
    quotientMapOfLE hLP (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  rw [quotientMapOfLE, Submodule.liftQ_apply, Submodule.mkQ_apply]

lemma quotientMapOfLE_surjective {L P : Submodule R M} (hLP : L ≤ P) :
    Function.Surjective (quotientMapOfLE hLP) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective P y
  exact ⟨Submodule.Quotient.mk x, quotientMapOfLE_mk hLP x⟩

lemma ker_quotientMapOfLE {L P : Submodule R M} (hLP : L ≤ P) :
    LinearMap.ker (quotientMapOfLE hLP) = imageInQuotient L P := by
  ext y
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    rw [LinearMap.mem_ker, quotientMapOfLE_mk, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨z, hz, hzx⟩
      have hzx' : x - z ∈ L := by
        exact (Submodule.Quotient.eq _).mp hzx.symm
      simpa only [sub_add_cancel] using P.add_mem (hLP hzx') hz

lemma exact_imageInQuotient_subtype_quotientMapOfLE {L P : Submodule R M}
    (hLP : L ≤ P) :
    Function.Exact (imageInQuotient L P).subtype (quotientMapOfLE hLP) := by
  rw [LinearMap.exact_iff, Submodule.range_subtype, ker_quotientMapOfLE hLP]

/-- Flatness of `M/P` makes the inclusion of the image in `M/L` universally injective. -/
lemma imageInQuotient_lTensor_injective_of_flat_quotient
    {L P : Submodule R M} (hLP : L ≤ P) [Module.Flat R (M ⧸ P)]
    (A : Type*) [AddCommGroup A] [Module R A] :
    Function.Injective ((imageInQuotient L P).subtype.lTensor A) := by
  exact LinearMap.lTensor_injective_of_exact_of_flat
    (quotientMapOfLE hLP) (quotientMapOfLE_surjective hLP)
    (imageInQuotient L P).subtype (Submodule.injective_subtype _)
    (exact_imageInQuotient_subtype_quotientMapOfLE hLP) A

/-- If the image dies in an arbitrary fibre, its tensor fibre is subsingleton. -/
lemma subsingleton_imageInQuotient_tensor_of_flat_quotient
    {L P : Submodule R M} (hLP : L ≤ P) [Module.Flat R (M ⧸ P)]
    (A : Type*) [AddCommGroup A] [Module R A]
    (hzero : ∀ n : imageInQuotient L P, ∀ a : A,
      ((n : M ⧸ L) ⊗ₜ[R] a) = 0) :
    Subsingleton (imageInQuotient L P ⊗[R] A) := by
  have hinj := imageInQuotient_lTensor_injective_of_flat_quotient hLP A
  have hz : ∀ u : A ⊗[R] ↥(imageInQuotient L P),
      (LinearMap.lTensor A (imageInQuotient L P).subtype) u = 0 := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a n =>
        rw [LinearMap.lTensor_tmul, Submodule.subtype_apply,
          show a ⊗ₜ[R] (n : M ⧸ L) =
            TensorProduct.comm R (M ⧸ L) A ((n : M ⧸ L) ⊗ₜ[R] a) from
            (TensorProduct.comm_tmul R (M ⧸ L) A (n : M ⧸ L) a).symm,
          hzero n a, map_zero]
    | add u v hu hv => rw [map_add, hu, hv, add_zero]
  haveI : Subsingleton (A ⊗[R] ↥(imageInQuotient L P)) :=
    ⟨fun s t => hinj (by rw [hz s, hz t])⟩
  exact (TensorProduct.comm R (imageInQuotient L P) A).toEquiv.subsingleton

/-- Residue-field form of the preceding bridge; only the pure tensor with `1` is needed. -/
lemma subsingleton_imageInQuotient_tmul_residueField_of_flat_quotient
    {L P : Submodule R M} (hLP : L ≤ P) [Module.Flat R (M ⧸ P)]
    (p : PrimeSpectrum R)
    (hzero : ∀ n : imageInQuotient L P,
      ((n : M ⧸ L) ⊗ₜ[R] (1 : p.asIdeal.ResidueField)) = 0) :
    Subsingleton (imageInQuotient L P ⊗[R] p.asIdeal.ResidueField) := by
  apply subsingleton_imageInQuotient_tensor_of_flat_quotient hLP
  intro n a
  rw [show ((n : M ⧸ L) ⊗ₜ[R] a)
      = TensorProduct.comm R p.asIdeal.ResidueField (M ⧸ L)
        (a ⊗ₜ[R] (n : M ⧸ L)) from
        (TensorProduct.comm_tmul R p.asIdeal.ResidueField (M ⧸ L) a (n : M ⧸ L)).symm]
  have haz : (a ⊗ₜ[R] (n : M ⧸ L) :
      p.asIdeal.ResidueField ⊗[R] (M ⧸ L)) = 0 := by
    rw [show (a ⊗ₜ[R] (n : M ⧸ L))
        = a • ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] (n : M ⧸ L)) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    have h1' : (1 : p.asIdeal.ResidueField) ⊗ₜ[R] (n : M ⧸ L) = 0 := by
      have hc := congrArg (TensorProduct.comm R (M ⧸ L) p.asIdeal.ResidueField) (hzero n)
      rwa [TensorProduct.comm_tmul, map_zero] at hc
    rw [h1', smul_zero]
  rw [haz, map_zero]

/-- The principal ideal containment needed above, in an elementwise form. -/
lemma span_singleton_restrictScalars_le_of_mul_mem
    {B : Type*} [CommRing B] [Algebra R B] (e : B) (P : Submodule R B)
    (h : ∀ c : B, c * e ∈ P) :
    (Ideal.span ({e} : Set B)).restrictScalars R ≤ P := by
  intro x hx
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
  rw [← hc]
  exact h c

end FlatRangeBridge

namespace ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}

/-- The principal section submodule, viewed over the base ring `R`. -/
noncomputable def chartReadPrincipalSubmodule
    (_K : Submodule R (relThetaSections C R π a)) (b : Bool)
    (s : relThetaSections C R π a) :
    Submodule R Γ(relCurve C R, relPinnedChart C R π b) :=
  (Ideal.span {relThetaResSide a b (le_rfl) s}).restrictScalars R

/-- The existing base colength is the image of the `R`-range in the principal quotient. -/
theorem chartColengthModuleBase_eq_imageInQuotient
    (K : Submodule R (relThetaSections C R π a)) (b : Bool)
    (s : relThetaSections C R π a) :
    chartColengthModuleBase K b s =
      FlatRangeBridge.imageInQuotient (chartReadPrincipalSubmodule K b s)
        (LinearMap.range (chartReadMap K b)) := by
  unfold chartColengthModuleBase chartReadPrincipalSubmodule
    FlatRangeBridge.imageInQuotient
  rw [← LinearMap.range_comp]
  rfl

/-- A section belonging to `K` gives the weak fact `e ∈ range(chartReadMap)`.  The
stronger principal-ideal containment is a separate hypothesis. -/
theorem chartRead_mem_range
    (K : Submodule R (relThetaSections C R π a)) (b : Bool)
    (s : relThetaSections C R π a) (hs : s ∈ K) :
    relThetaResSide a b (le_rfl) s ∈ LinearMap.range (chartReadMap K b) :=
  ⟨⟨s, hs⟩, rfl⟩

set_option maxHeartbeats 800000 in
/-- The valid RD-N fibre bridge for the chart range.  The required containment is
`(read s) ⊆ range(chartReadMap)`, not merely `read s ∈ range(chartReadMap)`. -/
theorem subsingleton_chartColengthModuleBase_tmul_residueField_of_flat_range_quotient
    (K : Submodule R (relThetaSections C R π a)) (b : Bool)
    (s : relThetaSections C R π a)
    [Module.Flat R (Γ(relCurve C R, relPinnedChart C R π b) ⧸
      LinearMap.range (chartReadMap K b))]
    (hle : chartReadPrincipalSubmodule K b s ≤ LinearMap.range (chartReadMap K b))
    (p : PrimeSpectrum R)
    (hzero : ∀ n : chartColengthModuleBase K b s,
      ((n : Γ(relCurve C R, relPinnedChart C R π b) ⧸
          Ideal.span {relThetaResSide a b (le_rfl) s}) ⊗ₜ[R]
        (1 : p.asIdeal.ResidueField)) = 0) :
    Subsingleton (chartColengthModuleBase K b s ⊗[R] p.asIdeal.ResidueField) := by
  rw [chartColengthModuleBase_eq_imageInQuotient] at hzero ⊢
  apply FlatRangeBridge.subsingleton_imageInQuotient_tmul_residueField_of_flat_quotient hle p
  intro n
  exact hzero n

/-- Elementwise spelling of the containment premise for callers with a multiplication law. -/
theorem chartReadPrincipalSubmodule_le_range_of_forall_mul_mem
    (K : Submodule R (relThetaSections C R π a)) (b : Bool)
    (s : relThetaSections C R π a)
    (hmul : ∀ c : Γ(relCurve C R, relPinnedChart C R π b),
      c * relThetaResSide a b (le_rfl) s ∈ LinearMap.range (chartReadMap K b)) :
    chartReadPrincipalSubmodule K b s ≤ LinearMap.range (chartReadMap K b) :=
  FlatRangeBridge.span_singleton_restrictScalars_le_of_mul_mem _ _ hmul

end ThetaGeneratorSeed

end AlgebraicGeometry
