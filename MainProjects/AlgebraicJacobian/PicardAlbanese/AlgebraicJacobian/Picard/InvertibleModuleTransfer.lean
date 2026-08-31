/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Invertible modules over a finite algebra: transfer to the base ring (DD-4 (c2)-transport)

Pure commutative algebra, no schemes (the D1 module-algebra discipline): let `A` be an
`R`-algebra that is finite projective as an `R`-module, and let `M` be an **invertible**
`A`-module (`Module.Invertible`, mathlib's Picard-group vocabulary).  Then `M` is finite
projective over `R` **of the same rank as `A` at every prime**:

* `Module.Projective.trans` — projectivity descends along a projective algebra: if `A`
  is projective over `R` and `P` projective over `A`, then `P` is projective over `R`
  (the projective mirror of `Module.Projective.of_free_algebra` in
  `AlgebraicJacobian.Picard.FlatCokernel`).
* `TensorProduct.baseChangeAlgebraModule` — the base-change collapse
  `(S ⊗[R] A) ⊗[A] M ≃ₗ[S] S ⊗[R] M` for an `A`-module `M` (the `A`-algebra structure
  on `S ⊗[R] A` through `Algebra.TensorProduct.rightAlgebra`).
* `Module.Invertible.finite_trans` / `Module.Invertible.projective_trans` — the
  finiteness/projectivity transfers.
* `Module.Invertible.rankAtStalk_eq_of_module_finite` — **the rank transfer**: at every
  prime `p` of `R`, `rankAtStalk M p = rankAtStalk A p`.  Route (the semilocal
  Pic-vanishing): the fibre algebra `κ(p) ⊗[R] A` is a finite algebra over the residue
  field, hence artinian, hence semilocal, so its Picard group is trivial (mathlib) and
  the fibre of `M` — an invertible module over the fibre algebra — is **free of rank
  one**; taking `κ(p)`-dimensions gives the claim through `Module.rankAtStalk_eq`.

The DD-4 consumer instantiates this at `A := ` the glued equalizer algebra of a certified
divisor family (with `Module.Finite`/`Projective`/`rankAtStalk = g` from the certificate
clause (c2)) and `M := ` the Θ-twisted glued module `W(d)^{Θᵃ}`
(`AlgebraicJacobian.Picard.DivisorFamilyThetaRank`).
-/

set_option autoImplicit false

universe u v

open TensorProduct

/-! ## Projectivity descends along a projective algebra -/

/-- **Projectivity is transitive**: if `A` is a projective `R`-module and `P` is a
projective `A`-module, then `P` is projective as an `R`-module.  The `A`-splitting
`P →ₗ[A] (P →₀ A)` provided by `Module.projective_def'` restricts to an `R`-splitting,
and `P →₀ A` is a projective `R`-module (a direct sum of copies of `A`, through
`finsuppLequivDFinsupp`). -/
theorem Module.Projective.trans {R : Type u} [CommRing R] (A : Type v) [CommRing A]
    [Algebra R A] {P : Type*} [AddCommMonoid P] [Module A P] [Module R P]
    [IsScalarTower R A P] [Module.Projective R A] [Module.Projective A P] :
    Module.Projective R P := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective A P›
  haveI : Module.Projective R (P →₀ A) :=
    Module.Projective.of_equiv (finsuppLequivDFinsupp (R := R) (M := A) (ι := P)).symm
  exact Module.Projective.of_split
    (LinearMap.restrictScalars R s)
    (LinearMap.restrictScalars R (Finsupp.linearCombination A _root_.id))
    (LinearMap.ext fun p => DFunLike.congr_fun hs p)

/-! ## The base-change collapse `(S ⊗[R] A) ⊗[A] M ≃ₗ[S] S ⊗[R] M` -/

namespace TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section BaseChangeAlgebraModule

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
variable (A : Type u) [CommRing A] [Algebra R A]
variable (M : Type u) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- The `S`-linear structure map `M →ₗ[R] (S ⊗[R] A) ⊗[A] M`, `m ↦ 1 ⊗ₜ m`. -/
noncomputable def baseChangeAlgebraModuleUnit : M →ₗ[R] (S ⊗[R] A) ⊗[A] M :=
  LinearMap.restrictScalars R (TensorProduct.mk A (S ⊗[R] A) M 1)

@[simp]
lemma baseChangeAlgebraModuleUnit_apply (m : M) :
    baseChangeAlgebraModuleUnit S A M m = (1 : S ⊗[R] A) ⊗ₜ[A] m := rfl

/-- (Implementation) The collapse pairing `(S ⊗[R] A) →ₗ[R] M →ₗ[R] S ⊗[R] M`,
`(s ⊗ a, m) ↦ s ⊗ (a • m)`, obtained by currying the composite of the associator with
the `A`-action collapse on the right factor. -/
noncomputable def baseChangeAlgebraModulePairing :
    (S ⊗[R] A) →ₗ[R] M →ₗ[R] S ⊗[R] M :=
  TensorProduct.curry
    ((LinearMap.lTensor S
        ((LinearMap.liftBaseChange A (LinearMap.id : M →ₗ[R] M)).restrictScalars R)) ∘ₗ
      (TensorProduct.assoc R S A M).toLinearMap)

@[simp]
lemma baseChangeAlgebraModulePairing_tmul (s : S) (a : A) (m : M) :
    baseChangeAlgebraModulePairing S A M (s ⊗ₜ[R] a) m = s ⊗ₜ[R] (a • m) := by
  simp [baseChangeAlgebraModulePairing]

/-- The `A`-action on `S ⊗[R] A` through `Algebra.TensorProduct.rightAlgebra`, on pure
tensors. -/
lemma rightAlgebra_smul_tmul (a : A) (s : S) (b : A) :
    a • (s ⊗ₜ[R] b) = s ⊗ₜ[R] (a * b) := by
  change ((1 : S) ⊗ₜ[R] a) * (s ⊗ₜ[R] b) = s ⊗ₜ[R] (a * b)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- (Implementation) The pairing is `A`-balanced. -/
lemma baseChangeAlgebraModulePairing_smul (a : A) (x : S ⊗[R] A) (m : M) :
    baseChangeAlgebraModulePairing S A M (a • x) m
      = baseChangeAlgebraModulePairing S A M x (a • m) := by
  induction x with
  | zero => simp
  | tmul s b =>
      rw [rightAlgebra_smul_tmul, baseChangeAlgebraModulePairing_tmul,
        baseChangeAlgebraModulePairing_tmul, mul_smul, smul_comm]
  | add x y hx hy => rw [smul_add, map_add, LinearMap.add_apply, hx, hy, map_add,
      LinearMap.add_apply]

/-- (Implementation) The pairing is `S`-semilinear in the first slot. -/
lemma baseChangeAlgebraModulePairing_smul_left (c : S) (x : S ⊗[R] A) (m : M) :
    baseChangeAlgebraModulePairing S A M (c • x) m
      = c • baseChangeAlgebraModulePairing S A M x m := by
  induction x with
  | zero => simp
  | tmul s b =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, baseChangeAlgebraModulePairing_tmul,
        baseChangeAlgebraModulePairing_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [smul_add, map_add, LinearMap.add_apply, hx, hy, map_add,
      LinearMap.add_apply, smul_add]

/-- (Implementation) The additive collapse `(S ⊗[R] A) ⊗[A] M →+ S ⊗[R] M`. -/
noncomputable def baseChangeAlgebraModuleCollapse :
    (S ⊗[R] A) ⊗[A] M →+ S ⊗[R] M :=
  TensorProduct.liftAddHom
    { toFun := fun x =>
        { toFun := fun m => baseChangeAlgebraModulePairing S A M x m
          map_zero' := by simp
          map_add' := fun m n => by simp }
      map_zero' := by ext m; simp
      map_add' := fun x y => by ext m; simp }
    (fun a x m => baseChangeAlgebraModulePairing_smul S A M a x m)

@[simp]
lemma baseChangeAlgebraModuleCollapse_tmul (x : S ⊗[R] A) (m : M) :
    baseChangeAlgebraModuleCollapse S A M (x ⊗ₜ[A] m)
      = baseChangeAlgebraModulePairing S A M x m := rfl

/-- **The base-change collapse**: for an `A`-module `M` and an `R`-algebra `S`, the
base change of `M` along `A → S ⊗[R] A` is the base change along `R → S`,
`S`-linearly: `(S ⊗[R] A) ⊗[A] M ≃ₗ[S] S ⊗[R] M` on generators
`(s ⊗ a) ⊗ m ↦ s ⊗ (a • m)`. -/
noncomputable def baseChangeAlgebraModule : (S ⊗[R] A) ⊗[A] M ≃ₗ[S] S ⊗[R] M where
  toFun := baseChangeAlgebraModuleCollapse S A M
  map_add' := map_add _
  map_smul' := by
    intro c z
    rw [RingHom.id_apply]
    induction z with
    | zero => simp
    | tmul x m =>
        rw [show c • (x ⊗ₜ[A] m) = (c • x) ⊗ₜ[A] m from TensorProduct.smul_tmul' c x m,
          baseChangeAlgebraModuleCollapse_tmul, baseChangeAlgebraModuleCollapse_tmul,
          baseChangeAlgebraModulePairing_smul_left]
    | add z w hz hw =>
        rw [smul_add, map_add, map_add, hz, hw, smul_add]
  invFun := LinearMap.liftBaseChange S (baseChangeAlgebraModuleUnit S A M)
  left_inv := by
    intro z
    induction z with
    | zero => simp
    | tmul x m =>
        rw [baseChangeAlgebraModuleCollapse_tmul]
        induction x with
        | zero => simp [TensorProduct.zero_tmul]
        | tmul s b =>
            rw [baseChangeAlgebraModulePairing_tmul, LinearMap.liftBaseChange_tmul,
              baseChangeAlgebraModuleUnit_apply]
            calc s • ((1 : S ⊗[R] A) ⊗ₜ[A] (b • m))
                = s • (b • ((1 : S ⊗[R] A) ⊗ₜ[A] m)) := by
                  rw [TensorProduct.tmul_smul]
              _ = s • ((b • (1 : S ⊗[R] A)) ⊗ₜ[A] m) := by
                  rw [TensorProduct.smul_tmul' b _ m]
              _ = (s • b • (1 : S ⊗[R] A)) ⊗ₜ[A] m := TensorProduct.smul_tmul' s _ m
              _ = (s ⊗ₜ[R] b) ⊗ₜ[A] m := by
                  congr 1
                  rw [show b • (1 : S ⊗[R] A) = (1 : S) ⊗ₜ[R] (b * 1) from
                    rightAlgebra_smul_tmul S A b 1 1, mul_one, TensorProduct.smul_tmul',
                    smul_eq_mul, mul_one]
        | add x y hx hy =>
            rw [map_add, LinearMap.add_apply, map_add, hx, hy, TensorProduct.add_tmul]
    | add z w hz hw =>
        rw [map_add, map_add, hz, hw]
  right_inv := by
    intro z
    induction z with
    | zero => simp
    | tmul s m =>
        rw [LinearMap.liftBaseChange_tmul, baseChangeAlgebraModuleUnit_apply,
          TensorProduct.smul_tmul' s _ m, baseChangeAlgebraModuleCollapse_tmul,
          show s • (1 : S ⊗[R] A) = s ⊗ₜ[R] (1 : A) by
            rw [show (1 : S ⊗[R] A) = (1 : S) ⊗ₜ[R] (1 : A) from rfl,
              TensorProduct.smul_tmul', smul_eq_mul, mul_one],
          baseChangeAlgebraModulePairing_tmul, one_smul]
    | add z w hz hw => rw [map_add, map_add, hz, hw]

@[simp]
lemma baseChangeAlgebraModule_tmul_tmul (s : S) (a : A) (m : M) :
    baseChangeAlgebraModule S A M ((s ⊗ₜ[R] a) ⊗ₜ[A] m) = s ⊗ₜ[R] (a • m) := by
  change baseChangeAlgebraModuleCollapse S A M ((s ⊗ₜ[R] a) ⊗ₜ[A] m) = s ⊗ₜ[R] (a • m)
  rw [baseChangeAlgebraModuleCollapse_tmul, baseChangeAlgebraModulePairing_tmul]

end BaseChangeAlgebraModule

end TensorProduct

/-! ## The invertible-module transfer -/

namespace Module.Invertible

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]

section Transfer

variable {M : Type u} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- **Finiteness transfer**: an invertible module over a module-finite `R`-algebra is a
finite `R`-module. -/
theorem finite_trans [Module.Finite R A] [Module.Invertible A M] :
    Module.Finite R M :=
  Module.Finite.trans A M

/-- **Projectivity transfer**: an invertible module over an `R`-algebra that is
projective as an `R`-module is projective over `R`. -/
theorem projective_trans [Module.Projective R A] [Module.Invertible A M] :
    Module.Projective R M :=
  Module.Projective.trans A

end Transfer

section Rank

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {M : Type u} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable [Module.Finite R A] [Module.Projective R A] [Module.Invertible A M]

omit [Module.Projective R A] [Module.Invertible A M] in
/-- (Implementation) The fibre algebra `κ(p) ⊗[R] A` of a finite `R`-algebra is
semilocal: it is a finite algebra over the residue field, hence artinian. -/
theorem finite_maximalSpectrum_fiber (p : PrimeSpectrum R) :
    Finite (MaximalSpectrum (p.asIdeal.ResidueField ⊗[R] A)) := by
  haveI : IsArtinianRing (p.asIdeal.ResidueField ⊗[R] A) := by
    haveI : IsArtinian p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] A) :=
      isArtinian_of_fg_of_artinian'
    exact isArtinian_of_tower p.asIdeal.ResidueField inferInstance
  infer_instance

/-- **The rank transfer** (the semilocal Pic-vanishing): an invertible module over a
finite projective `R`-algebra `A` has the same rank as `A` at every prime of `R`.
Route: `rankAtStalk` is the fibre dimension (`Module.rankAtStalk_eq`); the fibre
`κ(p) ⊗[R] M ≃ (κ(p) ⊗[R] A) ⊗[A] M` is an invertible module over the fibre algebra,
which is artinian (hence semilocal), so its Picard group is trivial and the fibre is
free of rank one over the fibre algebra. -/
theorem rankAtStalk_eq_of_module_finite (p : PrimeSpectrum R) :
    Module.rankAtStalk M p = Module.rankAtStalk A p := by
  haveI : Module.Finite R M := finite_trans (A := A)
  haveI : Module.Projective R M := projective_trans (A := A)
  haveI : Module.Flat R M := Module.Flat.of_projective
  haveI : Module.Flat R A := Module.Flat.of_projective
  rw [Module.rankAtStalk_eq, Module.rankAtStalk_eq]
  set κ := p.asIdeal.ResidueField
  -- the fibre algebra and the fibre of `M` over it
  set Aκ := κ ⊗[R] A with hAκ
  haveI : Finite (MaximalSpectrum Aκ) := finite_maximalSpectrum_fiber (A := A) p
  -- the fibre of `M` as a base change over `A`, an invertible `Aκ`-module
  haveI hinv : Module.Invertible Aκ (Aκ ⊗[A] M) := inferInstance
  haveI : Module.Free Aκ (Aκ ⊗[A] M) := inferInstance
  obtain ⟨e⟩ : Nonempty ((Aκ ⊗[A] M) ≃ₗ[Aκ] Aκ) :=
    Module.Invertible.free_iff_linearEquiv.mp ‹_›
  -- transport dimensions along the collapse and the rank-one equivalence
  have h1 : Module.finrank κ (κ ⊗[R] M) = Module.finrank κ (Aκ ⊗[A] M) :=
    (TensorProduct.baseChangeAlgebraModule κ A M).symm.finrank_eq
  have h2 : Module.finrank κ (Aκ ⊗[A] M) = Module.finrank κ Aκ :=
    (e.restrictScalars κ).finrank_eq
  change Module.finrank κ (κ ⊗[R] M) = Module.finrank κ (κ ⊗[R] A)
  rw [h1, h2]

end Rank

end Module.Invertible
