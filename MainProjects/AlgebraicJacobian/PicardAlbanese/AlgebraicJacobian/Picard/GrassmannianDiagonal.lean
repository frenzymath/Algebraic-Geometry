/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GrassmannianScheme

/-!
# The restricted-diagonal ring map of the Grassmannian (DD-3, stage 3d)

Following the route map's separatedness argument (Nitsure §1): the Grassmannian is
separated over `k` because on each affine patch `U^I ×_k U^J` of `Gr ×_k Gr` the
restricted diagonal is a closed immersion, equivalently the comorphism
`δ_{I,J} : R^I ⊗[k] R^J → R^I_J`, `X^I ⊗ 1 ↦ X^I`, `1 ⊗ X^J ↦ (X^I_J)⁻¹ X^I`,
is surjective (`informal/spec-dd-3.md` §2/§3).

* `AlgebraicGeometry.Grassmannian.diagonalRingMap`: `δ_{I,J}`, the tensor-product lift
  over `k` of the structure map and the pre-localisation transition hom.
* `AlgebraicGeometry.Grassmannian.diagonalRingMap_surjective`: **surjectivity** — the
  image contains `R^I` (left factor) and `1/P^I_J = δ_{I,J}(1 ⊗ P^J_I)` (right
  factor), which generate `R^I[1/P^I_J]`.
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory TensorProduct

namespace AlgebraicGeometry.Grassmannian

/-- The **restricted-diagonal ring map** `δ_{I,J} : R^I ⊗[k] R^J →ₐ[k] R^I_J`: the
tensor-product lift of the structure map `R^I → R^I_J` (first factor) and the
pre-localisation transition hom `θ̃_{I,J} : R^J → R^I_J` (second factor), so
`X^I ⊗ 1 ↦ X^I` and `1 ⊗ X^J ↦ (X^I_J)⁻¹ X^I`. -/
noncomputable def diagonalRingMap (k : Type u) [Field k] (d r : ℕ) (I J : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) :
    TensorProduct k (ChartRing k d r I) (ChartRing k d r J) →ₐ[k]
      Localization.Away (minorDet k d r I J hI hJ) :=
  Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom k (ChartRing k d r I)
      (Localization.Away (minorDet k d r I J hI hJ)))
    (transitionPreMap k d r I J hI hJ)
    (fun _ _ => Commute.all _ _)

/-- `δ_{I,J}` on the left factor is the structure map: `δ_{I,J}(a ⊗ 1) = a` in
`R^I_J`. -/
theorem diagonalRingMap_left (k : Type u) [Field k] (d r : ℕ) (I J : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) (a : ChartRing k d r I) :
    diagonalRingMap k d r I J hI hJ (a ⊗ₜ[k] 1)
      = algebraMap _ (Localization.Away (minorDet k d r I J hI hJ)) a := by
  rw [diagonalRingMap, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rfl

/-- `δ_{I,J}` on the right factor is the pre-localisation transition hom:
`δ_{I,J}(1 ⊗ b) = θ̃_{I,J}(b)`. -/
theorem diagonalRingMap_right (k : Type u) [Field k] (d r : ℕ) (I J : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) (b : ChartRing k d r J) :
    diagonalRingMap k d r I J hI hJ (1 ⊗ₜ[k] b) = transitionPreMap k d r I J hI hJ b := by
  rw [diagonalRingMap, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

/-- The **restricted-diagonal ring map is surjective**: the comorphism
`δ_{I,J} : R^I ⊗[k] R^J → R^I_J` of the restricted diagonal is surjective, so the
restricted diagonal `U^I_J → U^I ×_k U^J` is a closed immersion.  The image contains
the structure-map image of `R^I` (left factor) and `1/P^I_J = δ_{I,J}(1 ⊗ P^J_I)`
(right factor), which together generate `R^I_J = R^I[1/P^I_J]`. -/
theorem diagonalRingMap_surjective (k : Type u) [Field k] (d r : ℕ)
    (I J : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) :
    Function.Surjective (diagonalRingMap k d r I J hI hJ) := by
  intro z
  -- `z · uⁿ = algebraMap a` for some `a` and a power `n` of `u := P^I_J`, by the
  -- localisation property.
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (minorDet k d r I J hI hJ)) z
  obtain ⟨n, hn⟩ := s.2
  -- The witness pushes the power into the second tensor factor: `a ⊗ (P^J_I)ⁿ`.
  refine ⟨a ⊗ₜ[k] (minorDet k d r J I hJ hI ^ n), ?_⟩
  -- `v := θ̃_{I,J}(P^J_I)` is the inverse of `u := P^I_J` in `R^I_J`.
  have hvu : transitionPreMap k d r I J hI hJ (minorDet k d r J I hJ hI) *
      algebraMap (ChartRing k d r I)
        (Localization.Away (minorDet k d r I J hI hJ)) (minorDet k d r I J hI hJ) = 1 :=
    transitionPreMap_minorDet_swap_mul k d r I J hI hJ
  -- `algebraMap ↑s = uⁿ`.
  have hsu : algebraMap (ChartRing k d r I)
      (Localization.Away (minorDet k d r I J hI hJ)) (s : ChartRing k d r I)
      = (algebraMap (ChartRing k d r I)
          (Localization.Away (minorDet k d r I J hI hJ)) (minorDet k d r I J hI hJ)) ^ n := by
    rw [← hn, map_pow]
  -- `algebraMap a = z · uⁿ`.
  have key : algebraMap (ChartRing k d r I)
      (Localization.Away (minorDet k d r I J hI hJ)) a
      = z * (algebraMap (ChartRing k d r I)
          (Localization.Away (minorDet k d r I J hI hJ)) (minorDet k d r I J hI hJ)) ^ n := by
    rw [← hs, hsu]
  -- `δ(a ⊗ (P^J_I)ⁿ) = algebraMap a · vⁿ = z · uⁿ · vⁿ = z · (u·v)ⁿ = z`.
  rw [diagonalRingMap, Algebra.TensorProduct.lift_tmul, map_pow,
    IsScalarTower.coe_toAlgHom', key, mul_assoc, ← mul_pow, mul_comm _
      (transitionPreMap k d r I J hI hJ (minorDet k d r J I hJ hI)), hvu, one_pow, mul_one]

end AlgebraicGeometry.Grassmannian
