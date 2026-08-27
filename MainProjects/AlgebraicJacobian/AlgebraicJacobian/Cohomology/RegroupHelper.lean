/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Regrouping isomorphism — pure-tensor-algebra core

This file contains `AlgebraicGeometry.base_change_regroup_linearEquiv`, the
axiom-clean `R'`-linear equivalence `(A ⊗[R] R') ⊗[A] M ≃ₗ[R'] R' ⊗[R] M`
that is the mathematical heart of the section-level flat-base-change mate.

It lives in a separate compilation unit so that the `Module A (A ⊗[R] R')`
instance diamond (between `Algebra.TensorProduct.rightAlgebra` and the
`extendScalars`/`restrictScalars` canonical structure) normalises at the
import boundary, enabling `FlatBaseChange.lean` to close its
`base_change_mate_regroupEquiv` `map_smul'` with the one-liner
`exact LinearEquiv.toModuleIso (base_change_regroup_linearEquiv ↑M)`.

See `blueprint/src/chapters/Cohomology_RegroupHelper.tex`.
-/

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace AlgebraicGeometry

/-! ## Regrouping isomorphism for the section-level mate (L4-a) -/

/-- **Regrouping isomorphism, pure-tensor-algebra core.** For ring homomorphisms `ψ : R → R'`,
`φ : R → A` (giving `A` the `R`-algebra structure) and an `A`-module `M` (with `M` an `R`-module
via `φ` and `IsScalarTower R A M`), there is a bundled `R'`-linear isomorphism
\[ (A \otimes_R R') \otimes_A M \;\xrightarrow{\ \sim\ }\; R' \otimes_R M, \]
where `R'` acts on the source through the `right`-algebra structure on `A ⊗[R] R'`
(`Algebra.TensorProduct.rightAlgebra`, i.e. the `includeRight` factor). On the generator it sends
`(1 ⊗ r') ⊗ m ↦ r' ⊗ m`; its inverse sends `r' ⊗ m ↦ (1 ⊗ r') ⊗ m`. It carries **no** flatness
hypothesis.

The construction is exactly the blueprint composite
`comm ≪≫ cancelBaseChange ≪≫ comm` (in the `A ⊗_R R'` orientation):
\[ (A \otimes_R R') \otimes_A M \xrightarrow{\texttt{comm}} M \otimes_A (A \otimes_R R')
   \xrightarrow{\operatorname{cancelBaseChange}} M \otimes_R R'
   \xrightarrow{\texttt{comm}} R' \otimes_R M, \]
assembled at the additive level from Mathlib's `TensorProduct.comm` (×2) and
`TensorProduct.AlgebraTensorModule.cancelBaseChange` (instantiated at the tower `R → A → A` with
module `M` and base-change object `R'`), then re-bundled as an `R'`-linear equivalence by verifying
`R'`-`map_smul` on generators (`cancelBaseChange_tmul` plus the `rightAlgebra` action
`r' • (a ⊗ s) = a ⊗ (r' * s)`). This is the **mathematical heart** of the section-level mate
identification (`lem:base_change_mate_regroupEquiv`); the object-level packaging needed by the
chain is `base_change_mate_regroupEquiv` below. Axiom-clean (`propext`, `Quot.sound`).

Source: Stacks Project, Cohomology of Schemes, Lemma "Affine base change", proof, the
"boils down to the equality `(R' ⊗_R A) ⊗_A M = R' ⊗_R M`" step. -/
noncomputable def base_change_regroup_linearEquiv
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] (M : Type u) [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] :
    letI : Algebra R' (A ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
    ((A ⊗[R] R') ⊗[A] M) ≃ₗ[R'] (R' ⊗[R] M) := by
  letI : Algebra R' (A ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  -- The underlying additive composite `comm ≫ cancelBaseChange ≫ comm`.
  let g : ((A ⊗[R] R') ⊗[A] M) ≃+ (R' ⊗[R] M) :=
    (TensorProduct.comm A (A ⊗[R] R') M).toAddEquiv.trans
      (((TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M R').toAddEquiv).trans
        (TensorProduct.comm R M R').toAddEquiv)
  refine { g with map_smul' := ?_ }
  intro r' x
  simp only [AddEquiv.toFun_eq_coe, RingHom.id_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [smul_add, map_add, map_add, smul_add, ha, hb]
  | tmul t m =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [TensorProduct.add_tmul, smul_add, map_add, map_add, smul_add, ha, hb]
    | tmul a s =>
      -- `r' • ((a ⊗ s) ⊗ m) = (a ⊗ (r' * s)) ⊗ m` via the `rightAlgebra` action on `A ⊗[R] R'`.
      have hsmul : r' • ((a ⊗ₜ[R] s) ⊗ₜ[A] m) = (a ⊗ₜ[R] (r' * s)) ⊗ₜ[A] m := by
        rw [TensorProduct.smul_tmul']
        congr 1
        rw [Algebra.smul_def, show (algebraMap R' (A ⊗[R] R')) r' = (1 : A) ⊗ₜ[R] r' from rfl,
          Algebra.TensorProduct.tmul_mul_tmul]
        simp
      rw [hsmul]
      change (TensorProduct.comm R M R') (TensorProduct.AlgebraTensorModule.cancelBaseChange
          R A A M R' ((TensorProduct.comm A (A ⊗[R] R') M) ((a ⊗ₜ[R] (r' * s)) ⊗ₜ[A] m)))
        = r' • g ((a ⊗ₜ[R] s) ⊗ₜ[A] m)
      change _ = r' • (TensorProduct.comm R M R')
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M R'
          ((TensorProduct.comm A (A ⊗[R] R') M) ((a ⊗ₜ[R] s) ⊗ₜ[A] m)))
      simp only [TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.smul_tmul']
      rw [smul_eq_mul]

end AlgebraicGeometry
