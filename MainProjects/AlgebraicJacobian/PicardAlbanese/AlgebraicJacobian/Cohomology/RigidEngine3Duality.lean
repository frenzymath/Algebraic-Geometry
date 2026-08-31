/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Finiteness.Projective

/-!
# RE-3 — finite-projective duality bookkeeping (Kleiman `eq:Q`)

This is the duality corollary of the wave-4 rigid engine's `RE-3` sub-brick
(worksheet `informal/w4-rigid-engine-worksheet.md`, §1.2, §4). Once the split/flat
rigidity of `RigidEngine3Rigidity` exhibits `H⁰` as a **finite projective** `R`-module, the
representing-functor bookkeeping of Kleiman `eq:Q` (tex 1902–1904) is the natural
identification
`H⁰ ⊗ P ≅ Hom(H⁰^∨, P)`
for every `R`-module `P`, where `H⁰^∨ = Module.Dual R H⁰`. No `f_*`-functor is formed: the
datum's `ℙ(Q)` chart takes `Q := H⁰` directly, and this file supplies the reusable
finite-projective duality that RE-4/w4-6 applies to `Q = H⁰`.

The load-bearing fact — absent from Mathlib, which has the natural map `dualTensorHom` as an
equivalence only for finite **free** modules (`dualTensorHomEquiv`) — is that the natural
map `M^∨ ⊗ N → Hom(M, N)` is an isomorphism already for finite **projective** `M`. We prove
it by the standard retract argument: a finite projective `M` is a retract of a finite free
`F` (`Module.Finite.exists_comp_eq_id_of_projective`), and `dualTensorHom` is natural, so
the finite-free equivalence transports along the retract.

## Main results

* `RigidEngine.dualTensorHomEquivProjective`: for `M` finite projective,
  `Module.Dual R M ⊗[R] N ≃ₗ[R] (M →ₗ[R] N)`, the finite-projective upgrade of
  `dualTensorHomEquiv`.
* `RigidEngine.tensorDualHomEquiv`: for `M` finite projective,
  `M ⊗[R] P ≃ₗ[R] (Module.Dual R M →ₗ[R] P)` — the Kleiman `eq:Q` duality
  `H⁰ ⊗ P ≅ Hom(H⁰^∨, P)`, obtained from the previous result at `Module.Dual R M` composed
  with reflexivity (`Module.evalEquiv`).
-/

universe u v w

open scoped TensorProduct
open Module (Dual)

namespace AlgebraicJacobian.RigidEngine

variable {R : Type u} [CommRing R]

/-- **Finite-projective duality (bijectivity of the contraction map).** For a finite
projective `R`-module `M`, the natural contraction map `dualTensorHom : M^∨ ⊗ N → Hom(M, N)`
is bijective. Proved by transporting the finite-free equivalence `dualTensorHomEquiv` along a
retract `M → Fⁿ → M` (`Module.Finite.exists_comp_eq_id_of_projective`). 


 * Provenance: CUSTOM.
-/
theorem bijective_dualTensorHom_of_projective
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (N : Type w) [AddCommGroup N] [Module R N] :
    Function.Bijective (dualTensorHom R M N) := by
  classical
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  -- `F := Fin n → R` is finite free; `f : F → M`, `g : M → F`, `f ∘ₗ g = id`.
  set dTHF : Dual R (Fin n → R) ⊗[R] N ≃ₗ[R] ((Fin n → R) →ₗ[R] N) :=
    dualTensorHomEquiv R (Fin n → R) N with hdTHF
  have hcoe_apply : ∀ z, dTHF z = dualTensorHom R (Fin n → R) N z := fun z =>
    LinearMap.congr_fun (dualTensorHomEquivOfBasis_toLinearMap _) z
  -- Naturality of `dualTensorHom` along `g : M → F` and `f : F → M`.
  have hI : dualTensorHom R M N ∘ₗ (g.dualMap.rTensor N)
      = (LinearMap.lcomp R N g) ∘ₗ dualTensorHom R (Fin n → R) N := by
    refine TensorProduct.ext' fun ψ y => LinearMap.ext fun x => ?_
    simp [dualTensorHom_apply]
  have hIa : ∀ w, dualTensorHom R M N ((g.dualMap.rTensor N) w)
      = (LinearMap.lcomp R N g) (dualTensorHom R (Fin n → R) N w) := fun w => by
    have := LinearMap.congr_fun hI w; simpa using this
  have hII : (LinearMap.lcomp R N f) ∘ₗ dualTensorHom R M N
      = dualTensorHom R (Fin n → R) N ∘ₗ (f.dualMap.rTensor N) := by
    refine TensorProduct.ext' fun ψ y => LinearMap.ext fun x => ?_
    simp [dualTensorHom_apply]
  have hIIa : ∀ y, (LinearMap.lcomp R N f) (dualTensorHom R M N y)
      = dualTensorHom R (Fin n → R) N ((f.dualMap.rTensor N) y) := fun y => by
    have := LinearMap.congr_fun hII y; simpa using this
  -- The retract identity on duals: `g^∨ ∘ f^∨ = id`.
  have hdual : g.dualMap ∘ₗ f.dualMap = LinearMap.id := by
    rw [LinearMap.dualMap_comp_dualMap, hfg, LinearMap.dualMap_id]
  refine Function.bijective_iff_has_inverse.2
    ⟨(g.dualMap.rTensor N) ∘ₗ dTHF.symm.toLinearMap ∘ₗ (LinearMap.lcomp R N f),
      fun y => ?_, fun h => ?_⟩
  · -- left inverse: `inv (dualTensorHom y) = y` on `M^∨ ⊗ N`
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hIIa y, ← hcoe_apply, dTHF.symm_apply_apply, ← LinearMap.comp_apply,
      ← LinearMap.rTensor_comp, hdual, LinearMap.rTensor_id, LinearMap.id_apply]
  · -- right inverse: `dualTensorHom (inv h) = h` on `M →ₗ N`
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hIa, ← hcoe_apply, dTHF.apply_symm_apply]
    simp only [LinearMap.lcomp_apply']
    rw [LinearMap.comp_assoc, hfg, LinearMap.comp_id]

/-- **Finite-projective duality (`dualTensorHom` form).** For a finite projective
`R`-module `M`, the natural contraction map `M^∨ ⊗ N → Hom(M, N)` is an equivalence — the
finite-projective upgrade of the finite-free `dualTensorHomEquiv`. 


 * Provenance: CUSTOM.
-/
noncomputable def dualTensorHomEquivProjective
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (N : Type w) [AddCommGroup N] [Module R N] :
    Dual R M ⊗[R] N ≃ₗ[R] (M →ₗ[R] N) :=
  LinearEquiv.ofBijective (dualTensorHom R M N)
    (bijective_dualTensorHom_of_projective M N)

/-- **Kleiman `eq:Q` duality.** For a finite projective `R`-module `M` (in the application
`M = H⁰ = Q`) and any `R`-module `P`, there is a natural equivalence
`M ⊗[R] P ≃ₗ[R] Hom(M^∨, P)`; i.e. `H⁰ ⊗ P ≅ Hom(H⁰^∨, P)`. This is the representing-functor
bookkeeping consumed by the `th:LinSys` step of the datum (worksheet §1.2, §4.5). It is
obtained from `dualTensorHomEquivProjective` at `Module.Dual R M` together with the
reflexivity `M ≅ M^∨∨`. 


 * Provenance: ADAPTED.
-/
noncomputable def tensorDualHomEquiv
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (P : Type w) [AddCommGroup P] [Module R P] :
    M ⊗[R] P ≃ₗ[R] (Dual R M →ₗ[R] P) :=
  TensorProduct.congr (Module.evalEquiv R M) (LinearEquiv.refl R P) ≪≫ₗ
    dualTensorHomEquivProjective (Dual R M) P

end AlgebraicJacobian.RigidEngine
