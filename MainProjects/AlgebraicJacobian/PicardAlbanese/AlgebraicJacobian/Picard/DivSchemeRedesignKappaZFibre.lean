/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeFibrePointRead
import AlgebraicJacobian.Picard.DivSchemeRedesignKappaZ

/-!
# The sharp `κ(z)` fibre bridge

The fibre-order argument naturally lives after base change to the residue field of the
base point.  This file records exactly what it can imply at the *total chart point*.
There are two separate ingredients:

* a local-ring lemma turns a fibre germ divisibility statement into membership of the
  total chart readings in the point prime, using the stalk-map comparison; and
* a pointwise residue-fibre injectivity hypothesis for the chart-colength inclusion then
  turns those prime memberships into `Subsingleton (N ⊗ κ(z))`.

The injectivity hypothesis is intentionally explicit.  Ambient quotient vanishing alone
does not imply vanishing of the tensor of the image module (the `k[ε]` example is the
standard obstruction), so this theorem does not assume or infer flatness of `B / J`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace MonoidalCategory CartesianMonoidalCategory
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## Local-ring reflection along a stalk map -/

/-- If two sections are compared with their fibre-side sections by a stalk map, then
fibre germ divisibility carries membership in the affine chart prime from the first
section to the second, provided the first section already lies in that prime. -/
theorem mem_prime_of_stalkMap_germ_mem_span
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {W : X.Opens}
    (hU : IsAffineOpen U) {z : X} (hz : z ∈ W)
    (hzbase : f.base z ∈ U)
    {s t : Γ(Y, U)} {s' t' : Γ(X, W)}
    (hscomp : (f.stalkMap z).hom
        ((Y.presheaf.germ U (f.base z) hzbase).hom s) =
      (X.presheaf.germ W z hz).hom s')
    (htcomp : (f.stalkMap z).hom
        ((Y.presheaf.germ U (f.base z) hzbase).hom t) =
      (X.presheaf.germ W z hz).hom t')
    (hdiv : (X.presheaf.germ W z hz).hom t' ∈
      Ideal.span {(X.presheaf.germ W z hz).hom s'})
    (hs : s ∈ (hU.primeIdealOf ⟨f.base z, hzbase⟩).asIdeal) :
    t ∈ (hU.primeIdealOf ⟨f.base z, hzbase⟩).asIdeal := by
  have hsmax : (Y.presheaf.germ U (f.base z) hzbase).hom s ∈
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base z)) := by
    rw [hU.primeIdealOf_eq_map_closedPoint] at hs
    exact hs
  have hsfmax : (X.presheaf.germ W z hz).hom s' ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    rw [← hscomp]
    exact map_nonunit (f.stalkMap z).hom _ hsmax
  have htfmax : (X.presheaf.germ W z hz).hom t' ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hdiv
    rw [hc]
    exact Ideal.mul_mem_right _ _ hsfmax
  have htmax : (Y.presheaf.germ U (f.base z) hzbase).hom t ∈
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base z)) := by
    have htfmax' : (f.stalkMap z).hom
        ((Y.presheaf.germ U (f.base z) hzbase).hom t) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
      rw [htcomp]
      exact htfmax
    rw [← Ideal.mem_comap, IsLocalRing.maximalIdeal_comap] at htfmax'
    exact htfmax'
  rw [hU.primeIdealOf_eq_map_closedPoint]
  exact htmax

/-! ## Pure point-fibre algebra -/

private theorem qmk_tmul_residueField_eq_zero_of_mem
    {B : Type u} [CommRing B]
    (I : Ideal B) (p : Ideal B) [p.IsPrime]
    {e : B} (he : e ∈ p) (x : p.ResidueField) :
    Ideal.Quotient.mk I e ⊗ₜ[B] x = 0 := by
  rw [show Ideal.Quotient.mk I e = e • (Ideal.Quotient.mk I (1 : B)) by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one]]
  rw [TensorProduct.smul_tmul, show e • x = 0 by
    rw [Algebra.smul_def, Ideal.algebraMap_residueField_eq_zero.mpr he, zero_mul],
    TensorProduct.tmul_zero]

private theorem qmk_tmul_residueField_eq_zero_of_notMem
    {B : Type u} [CommRing B]
    (p : Ideal B) [p.IsPrime] {s e : B} (hs : s ∉ p)
    (x : p.ResidueField) :
    Ideal.Quotient.mk (Ideal.span {s}) e ⊗ₜ[B] x = 0 := by
  have hs0 : algebraMap B p.ResidueField s ≠ 0 := by
    intro h
    exact hs (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hx : x = s • ((algebraMap B p.ResidueField s)⁻¹ * x) := by
    rw [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
  have hsq : Ideal.Quotient.mk (Ideal.span {s}) s = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  calc
    Ideal.Quotient.mk (Ideal.span {s}) e ⊗ₜ[B] x =
        Ideal.Quotient.mk (Ideal.span {s}) e ⊗ₜ[B]
          (s • ((algebraMap B p.ResidueField s)⁻¹ * x)) :=
      congrArg (fun y => Ideal.Quotient.mk (Ideal.span {s}) e ⊗ₜ[B] y) hx
    _ = (s • Ideal.Quotient.mk (Ideal.span {s}) e) ⊗ₜ[B]
          ((algebraMap B p.ResidueField s)⁻¹ * x) :=
      (TensorProduct.smul_tmul s _ _).symm
    _ = 0 := by
      rw [show s • Ideal.Quotient.mk (Ideal.span {s}) e = 0 by
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
        have hmul : Ideal.Quotient.mk (Ideal.span {s}) (s * e) =
            Ideal.Quotient.mk (Ideal.span {s}) s *
              Ideal.Quotient.mk (Ideal.span {s}) e := by simp
        rw [hmul, hsq, zero_mul], TensorProduct.zero_tmul]

private theorem subsingleton_of_rTensor_subtype_injective_of_tmul_eq_zero
    {B F Q : Type u} [CommRing B] [Field F] [Algebra B F]
    [AddCommGroup Q] [Module B Q]
    {P : Submodule B Q}
    (hinj : Function.Injective (P.subtype.rTensor F))
    (hzero : ∀ x : P, ∀ a : F, (x : Q) ⊗ₜ[B] a = 0) :
    Subsingleton (P ⊗[B] F) := by
  have hz : ∀ u : P ⊗[B] F, (P.subtype.rTensor F) u = 0 := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => rw [map_add, hu, hv, add_zero]
    | tmul x a =>
        rw [LinearMap.rTensor_tmul]
        exact hzero x a
  exact ⟨fun s t => hinj (by rw [hz s, hz t])⟩

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}

namespace ThetaGeneratorSeed

/-- **Sharp `κ(z)` tensor reduction.**  Let `p` be the affine-chart prime of `z` and
`N = chartColengthModule K b s`.  If the residue-fibre of the inclusion
`N ↪ Γ(V)/(read s)` is injective, then the pointwise prime-membership condition
`read s ∈ p → (∀ ψ ∈ K, read ψ ∈ p)` implies
`Subsingleton (N ⊗_{Γ(V)} κ(p))`.

The premise is the exact purity/injectivity datum needed at the point.  No flatness of
the ambient quotient or of the chart ideal is inferred here. -/
theorem subsingleton_chartColengthModule_tmul_residueField_of_rTensor_subtype_injective
    (K : Submodule R (relThetaSections C R π a)) (b : Bool)
    (s : relThetaSections C R π a)
    (p : PrimeSpectrum Γ(relCurve C R, relPinnedChart C R π b))
    (hinj : Function.Injective
      ((chartColengthModule K b s).subtype.rTensor p.asIdeal.ResidueField))
    (hread : relThetaResSide a b le_rfl s ∈ p.asIdeal →
      ∀ ⦃ψ : relThetaSections C R π a⦄, ψ ∈ K →
        relThetaResSide a b le_rfl ψ ∈ p.asIdeal) :
    Subsingleton (↥(chartColengthModule K b s) ⊗[
      Γ(relCurve C R, relPinnedChart C R π b)] p.asIdeal.ResidueField) := by
  apply subsingleton_of_rTensor_subtype_injective_of_tmul_eq_zero hinj
  intro n x
  refine Submodule.span_induction
    (p := fun y _ => ∀ x : p.asIdeal.ResidueField,
      y ⊗ₜ[Γ(relCurve C R, relPinnedChart C R π b)] x = 0) ?_ ?_ ?_ ?_
      n.property x
  · rintro _ ⟨ψ, rfl⟩ x
    rcases ψ with ⟨ψ, hψ⟩
    change Ideal.Quotient.mk (Ideal.span {relThetaResSide a b le_rfl s})
      (relThetaResSide a b le_rfl ψ) ⊗ₜ[
        Γ(relCurve C R, relPinnedChart C R π b)] x = 0
    by_cases hs : relThetaResSide a b le_rfl s ∈ p.asIdeal
    · exact qmk_tmul_residueField_eq_zero_of_mem _ p.asIdeal (hread hs hψ) x
    · exact qmk_tmul_residueField_eq_zero_of_notMem p.asIdeal hs x
  · intro x
    simp
  · rintro y₁ y₂ _ _ h₁ h₂ x
    rw [TensorProduct.add_tmul, h₁ x, h₂ x, add_zero]
  · rintro c y _ hy x
    rw [TensorProduct.smul_tmul, hy]

end ThetaGeneratorSeed

end AlgebraicGeometry
