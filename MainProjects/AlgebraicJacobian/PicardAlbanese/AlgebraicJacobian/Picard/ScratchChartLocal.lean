import AlgebraicJacobian.Picard.DivSchemeRedesignLocalIdealFibre
import AlgebraicJacobian.Picard.DivSchemeRedesignChartReadIdeal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}

namespace ThetaGeneratorSeed

theorem test_chart_local
    (K : Submodule R (relThetaSections C R π a)) (b : Bool)
    (s : relThetaSections C R π a) (hsK : s ∈ K)
    (p : PrimeSpectrum Γ(relCurve C R, relPinnedChart C R π b))
    (hgen : ∀ x : chartReadIdeal K b, ∃ r,
      r ∉ p.asIdeal ∧ ∃ c,
        r * (x : Γ(relCurve C R, relPinnedChart C R π b)) =
          c * relThetaResSide a b le_rfl s) :
    Subsingleton ((chartIdealColengthModule K b s) ⊗[
      Γ(relCurve C R, relPinnedChart C R π b)] p.asIdeal.ResidueField) := by
  let B : Type u := Γ(relCurve C R, relPinnedChart C R π b)
  let e : B := relThetaResSide a b le_rfl s
  let J : Ideal B := chartReadIdeal K b
  let f : B →ₗ[B] (B ⧸ Ideal.span ({e} : Set B)) :=
    (Ideal.Quotient.mkₐ B (Ideal.span ({e} : Set B))).toLinearMap
  have heJ : e ∈ J := by
    exact Ideal.subset_span ⟨⟨s, hsK⟩, rfl⟩
  have hfe : f e = 0 := by
    change Ideal.Quotient.mk (Ideal.span ({e} : Set B)) e = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have h := LocalIdealFibre.subsingleton_ideal_map_tensor_residueField_of_local_generation
    J f p e heJ (fun x => by
      obtain ⟨r, hr, c, hrc⟩ := hgen x
      refine ⟨r, hr, ?_⟩
      exact Ideal.mem_span_singleton'.mpr ⟨c, by simpa [mul_comm] using hrc⟩) hfe
  change Subsingleton ((Submodule.map f (J : Submodule B B)) ⊗[B] p.asIdeal.ResidueField) at h
  simpa [B, e, J, f, chartIdealColengthModule] using h

end ThetaGeneratorSeed

end AlgebraicGeometry
