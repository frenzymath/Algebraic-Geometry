/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Kernels in pushout squares of commutative rings

This file computes the kernel of a coprojection in a pushout square when the opposite map is
surjective.  It is the extension of the original kernel along the other leg of the span.
-/

open CategoryTheory Limits
open scoped TensorProduct

namespace CommRingCat

/-- In a pushout of commutative rings, base-changing a surjection maps its kernel to the
kernel of the other coprojection. -/
lemma ker_inr_eq_map_ker_of_isPushout
    {R S T P : CommRingCat} (f : R ⟶ S) (g : R ⟶ T)
    (inl : S ⟶ P) (inr : T ⟶ P)
    (H : IsPushout f g inl inr) (hf : Function.Surjective f) :
    RingHom.ker inr.hom = (RingHom.ker f.hom).map g.hom := by
  algebraize [f.hom, g.hom]
  let q : T ⊗[R] R →ₐ[R] T ⊗[R] S :=
    Algebra.TensorProduct.map (AlgHom.id R T) (Algebra.ofId R S)
  let u : T ⊗[R] R ≃+* T :=
    (Algebra.TensorProduct.rid R R T).toRingEquiv
  let c : T ⊗[R] S ≃+* S ⊗[R] T :=
    (Algebra.TensorProduct.comm R T S).toRingEquiv
  have hq : RingHom.ker q =
      (RingHom.ker f.hom).map
        (Algebra.TensorProduct.includeRight : R →ₐ[R] T ⊗[R] R).toRingHom := by
    change RingHom.ker q =
      (RingHom.ker (Algebra.ofId R S)).map
        (Algebra.TensorProduct.includeRight : R →ₐ[R] T ⊗[R] R).toRingHom
    exact Algebra.TensorProduct.lTensor_ker (A := T) (Algebra.ofId R S) hf
  have hinclude :
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom =
        c.toRingHom.comp (q.toRingHom.comp u.symm.toRingHom) := by
    ext t
    simp [q, u, c]
  have hcanonical :
      RingHom.ker
          (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom =
        (RingHom.ker f.hom).map g.hom := by
    rw [hinclude]
    calc
      RingHom.ker (c.toRingHom.comp (q.toRingHom.comp u.symm.toRingHom)) =
          RingHom.ker (q.toRingHom.comp u.symm.toRingHom) :=
        RingHom.ker_comp_of_injective _ c.injective
      _ = (RingHom.ker q).comap u.symm.toRingHom :=
        (RingHom.comap_ker q.toRingHom u.symm.toRingHom).symm
      _ = ((RingHom.ker f.hom).map
          (Algebra.TensorProduct.includeRight : R →ₐ[R] T ⊗[R] R).toRingHom).comap
            u.symm.toRingHom := congrArg (Ideal.comap u.symm.toRingHom) hq
      _ = ((RingHom.ker f.hom).map
          (Algebra.TensorProduct.includeRight : R →ₐ[R] T ⊗[R] R).toRingHom).map
            u.toRingHom := Ideal.comap_symm u
      _ = (RingHom.ker f.hom).map (u.toRingHom.comp
          (Algebra.TensorProduct.includeRight : R →ₐ[R] T ⊗[R] R).toRingHom) :=
        Ideal.map_map _ _
      _ = (RingHom.ker f.hom).map g.hom := by
        congr 1
        ext r
        simp [u, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  let e := ((isPushout_tensorProduct R S T).isoIsPushout S T H).commRingCatIsoToRingEquiv
  have hinr :
      e.toRingHom.comp
          (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom = inr.hom :=
    congrArg Hom.hom
      ((isPushout_tensorProduct R S T).inr_isoIsPushout_hom S T H)
  calc
    RingHom.ker inr.hom = RingHom.ker (e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom) :=
      congrArg RingHom.ker hinr.symm
    _ = RingHom.ker
        (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom :=
      RingHom.ker_comp_of_injective _ e.injective
    _ = (RingHom.ker f.hom).map g.hom := hcanonical

end CommRingCat
