/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyPullbackCert

/-!
# Base change of the glued colength module (DD-1 stage (c), clauses (c2)–(c4))

The endgame of the certificate transport: under the flat-cokernel clauses (c3)/(c4),
the glued equalizer module `W(d)` commutes with arbitrary test-ring change, and the
remaining certificate clauses transport.

* `DivisorAdaptation.gluedBaseChange` — **the (c2) keystone**:
  `R' ⊗[R] W(d) ≃ₗ[R'] W'` — `FlatCokernel`'s `tensorKerEquivOfFlatCoker` followed by
  kernel transport along the `δ`-naturality square `delta_baseChange_comm`.
* `finite_pulledGlued`/`projective_pulledGlued`/`rankAtStalk_pulledGlued` — the (c2)
  clause transports (`Module.rankAtStalk_baseChange` through the glued transport).
* `flat_pulledCokerIncl` (c3) / `flat_pulledCokerDiff` (c4) — the flat-cokernel clause
  transports: right-exactness (`quotRangeBaseChangeEquiv`) + the purity keystone
  (`ker_lTensor_eq_of_flat_coker`) identify the pulled cokernels with base changes of
  the cokernels, which are flat by `Module.Flat.baseChange`.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## Kernel and range transport along commuting squares of equivalences -/

section SquareTransport

variable {S : Type u} [CommRing S] {M M₂ N N₂ : Type u}
variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup N] [AddCommGroup N₂]
variable [Module S M] [Module S M₂] [Module S N] [Module S N₂]

/-- Kernels transport along a commuting square whose verticals are equivalences. -/
lemma LinearEquiv.map_ker_of_comp_eq (e : M ≃ₗ[S] M₂) (g : N ≃ₗ[S] N₂)
    (f : M →ₗ[S] N) (f₂ : M₂ →ₗ[S] N₂)
    (h : f₂ ∘ₗ (e : M →ₗ[S] M₂) = (g : N →ₗ[S] N₂) ∘ₗ f) :
    (LinearMap.ker f).map (e : M →ₗ[S] M₂) = LinearMap.ker f₂ := by
  ext x
  rw [Submodule.mem_map, LinearMap.mem_ker]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [LinearMap.mem_ker] at hy
    have hsq := congr($(h) y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hsq
    simp only [LinearEquiv.coe_coe]
    rw [hsq, hy, map_zero]
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [LinearMap.mem_ker]
    have hsq := congr($(h) (e.symm x))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e.apply_symm_apply] at hsq
    have hg : g (f (e.symm x)) = 0 := by rw [← hsq, hx]
    have hzero := congrArg g.symm hg
    rwa [g.symm_apply_apply, map_zero] at hzero

/-- Ranges transport along a commuting square whose verticals are equivalences. -/
lemma LinearEquiv.range_eq_map_range_of_comp_eq (e : M ≃ₗ[S] M₂) (g : N ≃ₗ[S] N₂)
    (f : M →ₗ[S] N) (f₂ : M₂ →ₗ[S] N₂)
    (h : f₂ ∘ₗ (e : M →ₗ[S] M₂) = (g : N →ₗ[S] N₂) ∘ₗ f) :
    LinearMap.range f₂ = (LinearMap.range f).map (g : N →ₗ[S] N₂) := by
  ext x
  rw [LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    have hsq := congr($(h) (e.symm y))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e.apply_symm_apply] at hsq
    exact ⟨f (e.symm y), LinearMap.mem_range_self _ _, hsq.symm⟩
  · rintro ⟨z, hz, rfl⟩
    rw [LinearMap.mem_range] at hz
    obtain ⟨y, rfl⟩ := hz
    have hsq := congr($(h) y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hsq
    exact ⟨e y, hsq⟩

end SquareTransport


variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable {π : C.left ⟶ P1 k} [IsAffineHom π]

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R π d)

/-! ## The glued-module transport (certificate clause (c2)) -/

/-- The kernel of `id ⊗ δ` is carried onto the pulled glued module by the chart-product
transport. -/
lemma map_ker_lTensor_delta :
    (LinearMap.ker (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight))).map
        (A.chartProdBaseChange R' : R' ⊗[R] A.chartProd →ₗ[R'] A.pulledChartProd R') =
      A.pulledGluedSubmodule R' :=
  LinearEquiv.map_ker_of_comp_eq (A.chartProdBaseChange R') (A.ovlProdBaseChange R')
    (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight))
    (A.pulledDeltaLeft R' - A.pulledDeltaRight R') (A.delta_baseChange_comm R')

/-- The pulled glued module is carried onto the kernel of `id ⊗ δ` by the inverse
transport. -/
lemma map_pulledGluedSubmodule_symm :
    (A.pulledGluedSubmodule R').map
        ((A.chartProdBaseChange R').symm :
          A.pulledChartProd R' →ₗ[R'] R' ⊗[R] A.chartProd) =
      LinearMap.ker (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight)) :=
  LinearEquiv.map_ker_of_comp_eq (A.chartProdBaseChange R').symm
    (A.ovlProdBaseChange R').symm
    (A.pulledDeltaLeft R' - A.pulledDeltaRight R')
    (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight))
    (A.delta_baseChange_comm' R')

/-- The range of `id ⊗ δ` is the pulled range, transported back. -/
lemma range_lTensor_delta :
    LinearMap.range (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight)) =
      (LinearMap.range (A.pulledDeltaLeft R' - A.pulledDeltaRight R')).map
        ((A.ovlProdBaseChange R').symm :
          A.pulledOvlProd R' →ₗ[R'] R' ⊗[R] A.ovlProd) :=
  LinearEquiv.range_eq_map_range_of_comp_eq (A.chartProdBaseChange R').symm
    (A.ovlProdBaseChange R').symm
    (A.pulledDeltaLeft R' - A.pulledDeltaRight R')
    (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight))
    (A.delta_baseChange_comm' R')

/-- **Base change of the glued colength module** (the (c2) keystone): under the
flat-cokernel clauses (c3)/(c4), `R' ⊗[R] W(d) ≃ₗ[R'] W'` — the `FlatCokernel`
comparison followed by kernel transport along the `δ`-naturality square. -/
noncomputable def gluedBaseChange
    [Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)]
    [Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))] :
    R' ⊗[R] A.Glued ≃ₗ[R'] ↥(A.pulledGluedSubmodule R') :=
  haveI : Module.Flat R
      (A.chartProd ⧸ LinearMap.ker (A.deltaLeft - A.deltaRight)) :=
    ‹Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)›
  (LinearMap.tensorKerEquivOfFlatCoker (A.deltaLeft - A.deltaRight) R').trans
    (((A.chartProdBaseChange R').submoduleMap
        (LinearMap.ker (AlgebraTensorModule.lTensor R' R'
          (A.deltaLeft - A.deltaRight)))).trans
      (LinearEquiv.ofEq _ _ (A.map_ker_lTensor_delta R')))

/-- (c2) transport, finiteness. -/
theorem finite_pulledGlued
    [Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)]
    [Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))]
    (hfin : Module.Finite R A.Glued) :
    Module.Finite R' ↥(A.pulledGluedSubmodule R') := by
  haveI := hfin
  exact Module.Finite.equiv (A.gluedBaseChange R')

/-- (c2) transport, projectivity. -/
theorem projective_pulledGlued
    [Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)]
    [Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))]
    (hproj : Module.Projective R A.Glued) :
    Module.Projective R' ↥(A.pulledGluedSubmodule R') := by
  haveI := hproj
  exact Module.Projective.of_equiv (A.gluedBaseChange R')

/-- (c2) transport, constant fibre rank: `Module.rankAtStalk_baseChange` through the
glued transport. -/
theorem rankAtStalk_pulledGlued {n : ℕ}
    [Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)]
    [Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))]
    (hfin : Module.Finite R A.Glued) (hproj : Module.Projective R A.Glued)
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk A.Glued p = n)
    (p : PrimeSpectrum R') :
    Module.rankAtStalk (↥(A.pulledGluedSubmodule R')) p = n := by
  haveI := hfin
  haveI := hproj
  rw [← Module.rankAtStalk_eq_of_equiv (A.gluedBaseChange R'),
    Module.rankAtStalk_baseChange]
  exact hrank _

/-! ## The flat-cokernel transports (certificate clauses (c3)/(c4)) -/

omit [Algebra k R'] [IsScalarTower k R R'] in
/-- The base change of the glued inclusion has the kernel of `id ⊗ δ` as range (the
`FlatCokernel` purity keystone, `R'`-linear form). -/
lemma range_baseChange_gluedSubtype
    [Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)]
    [Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))] :
    LinearMap.range ((A.gluedSubmodule).subtype.baseChange R') =
      LinearMap.ker (AlgebraTensorModule.lTensor R' R'
        (A.deltaLeft - A.deltaRight)) := by
  haveI : Module.Flat R
      (A.chartProd ⧸ LinearMap.ker (A.deltaLeft - A.deltaRight)) :=
    ‹Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)›
  have h := LinearMap.ker_lTensor_eq_of_flat_coker (A.deltaLeft - A.deltaRight) R'
  ext x
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  have hx := SetLike.ext_iff.mp h x
  rw [LinearMap.mem_ker, LinearMap.mem_range] at hx
  constructor
  · rintro ⟨y, rfl⟩
    exact hx.mpr ⟨y, rfl⟩
  · intro hker
    obtain ⟨y, hy⟩ := hx.mp hker
    exact ⟨y, hy⟩

/-- (c3) transport: the cokernel of the pulled glued inclusion is flat over `R'`
(right-exactness identifies it with the base change of the cokernel, which is flat by
`Module.Flat.baseChange`). -/
theorem flat_pulledCokerIncl
    [Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)]
    [Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))] :
    Module.Flat R' (A.pulledChartProd R' ⧸ A.pulledGluedSubmodule R') := by
  refine Module.Flat.of_linearEquiv (N := A.pulledChartProd R' ⧸ A.pulledGluedSubmodule R')
    (M := R' ⊗[R] (A.chartProd ⧸ A.gluedSubmodule)) ?_
  refine (Submodule.Quotient.equiv (A.pulledGluedSubmodule R')
      (LinearMap.ker (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight)))
      (A.chartProdBaseChange R').symm (A.map_pulledGluedSubmodule_symm R')).trans
    ((Submodule.quotEquivOfEq _ _ (A.range_baseChange_gluedSubtype R').symm).trans
      (((LinearMap.quotRangeBaseChangeEquiv R' (A.gluedSubmodule).subtype).symm).trans
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R')
          (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype A.gluedSubmodule)))))

omit [Algebra k R'] [IsScalarTower k R R'] in
/-- The range of `id ⊗ δ` in the base-change spelling. -/
lemma range_lTensor_eq_range_baseChange :
    LinearMap.range (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight)) =
      LinearMap.range ((A.deltaLeft - A.deltaRight).baseChange R') := by
  ext x
  rw [LinearMap.mem_range, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩

/-- (c4) transport: the cokernel of the pulled difference arrow is flat over `R'`. -/
theorem flat_pulledCokerDiff
    [Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))] :
    Module.Flat R' (A.pulledOvlProd R' ⧸
      LinearMap.range (A.pulledDeltaLeft R' - A.pulledDeltaRight R')) := by
  refine Module.Flat.of_linearEquiv
    (N := A.pulledOvlProd R' ⧸
      LinearMap.range (A.pulledDeltaLeft R' - A.pulledDeltaRight R'))
    (M := R' ⊗[R] (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))) ?_
  refine (Submodule.Quotient.equiv
      (LinearMap.range (A.pulledDeltaLeft R' - A.pulledDeltaRight R'))
      (LinearMap.range (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight)))
      (A.ovlProdBaseChange R').symm (A.range_lTensor_delta R').symm).trans
    ((Submodule.quotEquivOfEq _ _ (A.range_lTensor_eq_range_baseChange R')).trans
      (LinearMap.quotRangeBaseChangeEquiv R' (A.deltaLeft - A.deltaRight)).symm)

end DivisorAdaptation

end AlgebraicGeometry
