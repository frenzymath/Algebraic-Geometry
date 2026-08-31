/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtAff
import AlgebraicJacobian.Picard.PicEtFiniteStageCover

/-!
# Finite-stage covers for etale Picard representatives

Every element of `PicEtAff C K` has a representative whose etale cover is the base change of
a cover over a finite subextension of an algebraic extension `K/k`.

This result descends only the **cover carrying the representative**.  Its descent class remains
a class over `K`; no finite-stage descent of that class is asserted here.
-/

set_option autoImplicit false

universe u

open CategoryTheory

open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

/-- A class in the etale plus construction over an algebraic field extension can be represented
on the base change of an etale cover from a finite subextension.  The representative's descent
class is still defined over the full field `K`. -/
theorem exists_finSubext_baseChanged_cover_representation
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (C : Over (Spec (.of k))) (x : PicEtAff C K) :
    ∃ (L : DatG0.FinSubext k K) (E₀ : Algebra.EtaleCover L.1)
      (ξK : descentClasses C (E₀.baseChange K)),
      PicEtAff.mk C (E₀.baseChange K) ξK = x := by
  induction x using PicEtAff.ind with
  | _ E ξ =>
      obtain ⟨L, B₀, hRing, hAlg, hEtale, hsurj, ⟨e⟩⟩ :=
        DatG0.exists_finSubext_etaleCover_model (k := k) (K := K) E
      letI : CommRing B₀ := hRing
      letI : Algebra L.1 B₀ := hAlg
      letI : Algebra.Etale L.1 B₀ := hEtale
      let E₀ : Algebra.EtaleCover L.1 := Algebra.EtaleCover.of B₀ hsurj
      let e₀ : E₀.Carrier ≃ₐ[L.1] B₀ := Algebra.EtaleCover.ofEquiv B₀ hsurj
      let bcEquiv : (E₀.baseChange K).Carrier ≃ₐ[K] K ⊗[L.1] B₀ :=
        (E₀.baseChangeEquiv K).trans
          (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e₀)
      let ψ : E.Carrier ≃ₐ[K] (E₀.baseChange K).Carrier := e.trans bcEquiv.symm
      exact ⟨L, E₀, descentMap C ψ.toAlgHom ξ, PicEtAff.mk_descentMap C ψ.toAlgHom ξ⟩

end

end AlgebraicGeometry
