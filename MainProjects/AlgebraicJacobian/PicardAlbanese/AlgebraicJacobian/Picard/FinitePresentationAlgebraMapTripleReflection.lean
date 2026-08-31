/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.FinitePresentationAlgebraMapFiniteStage

/-!
# Reflection of triple algebra-map compositions

A composition of three algebra maps at a finite tensor stage is determined by its
scalar extension to the ambient algebraic field extension.
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgebraicGeometry.DatG0

/-- A triple composition identity descends once all four maps commute with base change. -/
theorem tensorProduct_algHom_triple_comp_eq_of_baseChange
    {F K A B D E : Type u} [Field F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K]
    [CommRing A] [Algebra F A] [CommRing B] [Algebra F B]
    [CommRing D] [Algebra F D] [CommRing E] [Algebra F E]
    (L : FinSubext F K)
    (phiL : L.1 ⊗[F] A →ₐ[L.1] L.1 ⊗[F] B)
    (psiL : L.1 ⊗[F] B →ₐ[L.1] L.1 ⊗[F] D)
    (rhoL : L.1 ⊗[F] D →ₐ[L.1] L.1 ⊗[F] E)
    (chiL : L.1 ⊗[F] A →ₐ[L.1] L.1 ⊗[F] E)
    (phiK : K ⊗[F] A →ₐ[K] K ⊗[F] B)
    (psiK : K ⊗[F] B →ₐ[K] K ⊗[F] D)
    (rhoK : K ⊗[F] D →ₐ[K] K ⊗[F] E)
    (chiK : K ⊗[F] A →ₐ[K] K ⊗[F] E)
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
    (hrho :
      (Algebra.TensorProduct.map L.1.val (AlgHom.id F E)).comp
          (rhoL.restrictScalars F) =
        (rhoK.restrictScalars F).comp
          (Algebra.TensorProduct.map L.1.val (AlgHom.id F D)))
    (hchi :
      (Algebra.TensorProduct.map L.1.val (AlgHom.id F E)).comp
          (chiL.restrictScalars F) =
        (chiK.restrictScalars F).comp
          (Algebra.TensorProduct.map L.1.val (AlgHom.id F A)))
    (hK : rhoK.comp (psiK.comp phiK) = chiK) :
    rhoL.comp (psiL.comp phiL) = chiL := by
  apply DFunLike.ext _ _
  intro x
  apply tensorProduct_map_finSubext_injective L
  calc
    (Algebra.TensorProduct.map L.1.val (AlgHom.id F E))
        ((rhoL.comp (psiL.comp phiL)) x) =
      rhoK ((Algebra.TensorProduct.map L.1.val (AlgHom.id F D))
        ((psiL.comp phiL) x)) := by
          exact DFunLike.congr_fun hrho ((psiL.comp phiL) x)
    _ = rhoK (psiK
        ((Algebra.TensorProduct.map L.1.val (AlgHom.id F B)) (phiL x))) := by
      exact congrArg rhoK (DFunLike.congr_fun hpsi (phiL x))
    _ = rhoK (psiK (phiK
        ((Algebra.TensorProduct.map L.1.val (AlgHom.id F A)) x))) := by
      exact congrArg (fun y => rhoK (psiK y)) (DFunLike.congr_fun hphi x)
    _ = chiK ((Algebra.TensorProduct.map L.1.val (AlgHom.id F A)) x) := by
      exact DFunLike.congr_fun hK
        ((Algebra.TensorProduct.map L.1.val (AlgHom.id F A)) x)
    _ = (Algebra.TensorProduct.map L.1.val (AlgHom.id F E)) (chiL x) := by
      exact (DFunLike.congr_fun hchi x).symm

end AlgebraicGeometry.DatG0
