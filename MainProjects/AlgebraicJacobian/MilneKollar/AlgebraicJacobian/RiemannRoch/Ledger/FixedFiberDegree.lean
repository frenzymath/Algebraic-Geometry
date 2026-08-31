/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.FiberCoordinateComplex
import AlgebraicJacobian.RiemannRoch.Ledger.GenusFieldInvariance
import AlgebraicJacobian.RiemannRoch.Ledger.MapToP1FieldBaseChange
import AlgebraicJacobian.RiemannRoch.Ledger.ExtensionUniformity

/-!
# A fixed fiber divisor has extension-independent degree

This file closes the degree clause of `UniformBaseDivisor`.  Choose the project's fixed finite
dominant map `C -> P1` once over the ground field and pull its source-side two-chart coordinate
data through every field extension.  For the divisor

`genus(C) * coordinateWeilDivisor`

the normalized Mayer--Vietoris differential commutes with scalar extension.  Its surjectivity
is equivalent to vanishing of `H^1`, while its kernel computes `H^0`.  Kernel base change then
keeps `h^0` fixed.  Riemann--Roch and invariance of the genus force the divisor degree to stay
fixed as well.

The construction works for arbitrary field extensions and adds no hypothesis to the curve.
Its main outputs are:

* `FiberCoordinateData.subsingleton_coordinate_baseChange_of_base`: transport of the fixed
  divisor's `H^1` vanishing;
* `FiberCoordinateData.h0_coordinate_baseChange_eq`: invariance of its `h^0`;
* `FiberCoordinateData.degree_coordinate_baseChange_eq`: invariance of its degree;
* `FiberCoordinateData.uniformBaseDivisor_fixedCoordinate`: the previously missing producer of
  `UniformBaseDivisor` at every genus;
* `FiberCoordinateData.uniformVanishing_fixedCoordinate`: extension-uniform large-degree
  vanishing with no additional antecedent.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace TensorProduct

namespace CategoryTheory
namespace GrothendieckTopology
namespace MayerVietorisSquare

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable {R : Type u} [CommRing R] [HasSheafify J (ModuleCat.{u} R)]
variable (S : J.MayerVietorisSquare)
variable (F : Sheaf J (ModuleCat.{u} R))

noncomputable def h0KernelLinearEquiv :
    F.obj.obj (op S.X₄) ≃ₗ[R] LinearMap.ker (S.moduleDiff F) :=
  LinearEquiv.ofBijective
    ((F.obj.map S.f₂₄.op).hom.prod (F.obj.map S.f₃₄.op).hom |>.codRestrict
      (LinearMap.ker (S.moduleDiff F)) (fun x => by
        rw [LinearMap.mem_ker]
        exact S.moduleDiff_restriction F x))
    (by
      constructor
      · intro x y hxy
        exact S.sections_ext F x y
          (congrArg (fun z : LinearMap.ker (S.moduleDiff F) => z.1.1) hxy)
          (congrArg (fun z : LinearMap.ker (S.moduleDiff F) => z.1.2) hxy)
      · rintro ⟨t, ht⟩
        rw [LinearMap.mem_ker] at ht
        obtain ⟨x, hx₂, hx₃⟩ := S.exists_glue_of_moduleDiff_eq_zero F t ht
        refine ⟨x, Subtype.ext ?_⟩
        exact Prod.ext hx₂ hx₃)

theorem moduleDiff_surjective_of_subsingleton_hModule'
    (h : Subsingleton (Sheaf.HModule' F S.X₄ 1)) :
    Function.Surjective (S.moduleDiff F) := by
  letI := h
  intro s
  exact S.exists_of_moduleDelta_eq_zero F s (Subsingleton.elim _ _)

theorem subsingleton_hModule'_of_moduleDiff_surjective
    [Subsingleton (Sheaf.HModule' F S.X₂ 1)]
    [Subsingleton (Sheaf.HModule' F S.X₃ 1)]
    (hd : Function.Surjective (S.moduleDiff F)) :
    Subsingleton (Sheaf.HModule' F S.X₄ 1) := by
  refine subsingleton_of_forall_eq 0 ?_
  intro y
  obtain ⟨s, rfl⟩ := S.moduleDelta_surjective F y
  obtain ⟨t, rfl⟩ := hd s
  exact S.moduleDelta_moduleDiff F t

end MayerVietorisSquare
end GrothendieckTopology
end CategoryTheory

namespace AlgebraicGeometry

namespace FiberCoordinateData

theorem surjective_left_of_comm
    {K M N M' N' : Type u} [CommRing K]
    [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N]
    [AddCommGroup M'] [Module K M']
    [AddCommGroup N'] [Module K N']
    {f : M →ₗ[K] N} {g : M' →ₗ[K] N'}
    (e₀ : M ≃ₗ[K] M') (e₁ : N ≃ₗ[K] N')
    (h : g.comp e₀.toLinearMap = e₁.toLinearMap.comp f)
    (hg : Function.Surjective g) : Function.Surjective f := by
  intro y
  obtain ⟨x', hx'⟩ := hg (e₁ y)
  refine ⟨e₀.symm x', ?_⟩
  apply e₁.injective
  have hc := LinearMap.congr_fun h (e₀.symm x')
  calc
    e₁ (f (e₀.symm x')) = g (e₀ (e₀.symm x')) := by
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using hc.symm
    _ = g x' := by rw [e₀.apply_symm_apply]
    _ = e₁ y := hx'

theorem surjective_right_of_comm
    {K M N M' N' : Type u} [CommRing K]
    [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N]
    [AddCommGroup M'] [Module K M']
    [AddCommGroup N'] [Module K N']
    {f : M →ₗ[K] N} {g : M' →ₗ[K] N'}
    (e₀ : M ≃ₗ[K] M') (e₁ : N ≃ₗ[K] N')
    (h : g.comp e₀.toLinearMap = e₁.toLinearMap.comp f)
    (hf : Function.Surjective f) : Function.Surjective g := by
  intro y'
  obtain ⟨x, hx⟩ := hf (e₁.symm y')
  refine ⟨e₀ x, ?_⟩
  have hc := LinearMap.congr_fun h x
  calc
    g (e₀ x) = e₁ (f x) := by
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using hc
    _ = e₁ (e₁.symm y') := by rw [hx]
    _ = y' := e₁.apply_symm_apply y'

end FiberCoordinateData
end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

namespace FiberCoordinateData

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  (Q : FiberCoordinateData Y)

noncomputable def coordinateH0KerEquiv (n : ℕ) :
    Sheaf.HModule (Y.divisorSheaf K (n • Q.coordinateWeilDivisor (K := K))) 0 ≃ₗ[K]
      LinearMap.ker (Q.coordinateDiff (K := K) n) :=
  (Sheaf.HModule.linearEquiv₀ (Opens.grothendieckTopology (Y : TopCat))
      (isTerminalTop : IsTerminal (⊤ : Y.Opens))
      (Y.divisorSheaf K (n • Q.coordinateWeilDivisor (K := K)))).trans
    (((Y.twoCoverSquare Q.V₀ Q.V₁ Q.cover).h0KernelLinearEquiv
      (Y.divisorSheaf K (n • Q.coordinateWeilDivisor (K := K)))).trans
        (kerEquivOfComm K
          (Q.coordinateSectionsEquivDom (K := K) n)
          (Q.coordinateSectionsEquivOverlap (K := K) n)
          (Q.coordinateDiff_intertwine (K := K) n)).symm)

section H0Transport

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIntegral C.hom]
variable (κ : Type u) [Field κ] [Algebra k κ]
variable (D : FiberCoordinateData C.left)

theorem h0_coordinate_baseChange_eq
    (n : ℕ)
    (hbase :
      letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
      haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
        inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
      Subsingleton (Sheaf.HModule (C.left.divisorSheaf k
        (n • D.coordinateWeilDivisor (K := k))) 1)) :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    haveI : SmoothOfRelativeDimension 1
        ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
    Sheaf.h0 ((Scheme.baseChangeField C κ).left.divisorSheaf κ
        (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ))) =
      Sheaf.h0 (C.left.divisorSheaf k
        (n • D.coordinateWeilDivisor (K := k))) := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  letI hbase' : Subsingleton (Sheaf.HModule (C.left.divisorSheaf k
      (n • D.coordinateWeilDivisor (K := k))) 1) := hbase
  have htop : Subsingleton (Sheaf.HModule'
      (C.left.divisorSheaf k (n • D.coordinateWeilDivisor (K := k)))
      (C.left.twoCoverSquare D.V₀ D.V₁ D.cover).X₄ 1) := by
    change Subsingleton (Sheaf.HModule'
      (C.left.divisorSheaf k (n • D.coordinateWeilDivisor (K := k)))
      (⊤ : C.left.Opens) 1)
    exact (Sheaf.HModule.linearEquivHModule'
      (isTerminalTop : IsTerminal (⊤ : C.left.Opens))
      (C.left.divisorSheaf k (n • D.coordinateWeilDivisor (K := k))) 1).symm.toEquiv.subsingleton
  have hmd : Function.Surjective
      ((C.left.twoCoverSquare D.V₀ D.V₁ D.cover).moduleDiff
        (C.left.divisorSheaf k (n • D.coordinateWeilDivisor (K := k)))) :=
    (C.left.twoCoverSquare D.V₀ D.V₁ D.cover).moduleDiff_surjective_of_subsingleton_hModule'
      (C.left.divisorSheaf k (n • D.coordinateWeilDivisor (K := k))) htop
  have hd : Function.Surjective (D.coordinateDiff (K := k) n) :=
    surjective_left_of_comm (K := k)
      (D.coordinateSectionsEquivDom (K := k) n)
      (D.coordinateSectionsEquivOverlap (K := k) n)
      (D.coordinateDiff_intertwine (K := k) n) hmd
  letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
    .ofHom (Scheme.baseChangeField C κ).hom
  haveI : SmoothOfRelativeDimension 1
      ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
  change Module.finrank κ (Sheaf.HModule
      ((Scheme.baseChangeField C κ).left.divisorSheaf κ
        (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ))) 0) =
    Module.finrank k (Sheaf.HModule (C.left.divisorSheaf k
      (n • D.coordinateWeilDivisor (K := k))) 0)
  calc
    _ = Module.finrank κ
        (LinearMap.ker ((D.baseChangeField κ).coordinateDiff (K := κ) n)) :=
      ((D.baseChangeField κ).coordinateH0KerEquiv (K := κ) n).finrank_eq
    _ = Module.finrank κ
        (κ ⊗[k] LinearMap.ker (D.coordinateDiff (K := k) n)) :=
      (coordinateDiffKerBaseChangeEquiv (κ := κ) (D := D) n hd).finrank_eq.symm
    _ = Module.finrank k (LinearMap.ker (D.coordinateDiff (K := k) n)) :=
      Module.finrank_baseChange
    _ = _ := (D.coordinateH0KerEquiv (K := k) n).finrank_eq.symm

end H0Transport
end FiberCoordinateData
end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

namespace FiberCoordinateData

section Transport

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom]
variable (κ : Type u) [Field κ] [Algebra k κ]
variable (D : FiberCoordinateData C.left)

theorem subsingleton_coordinate_baseChange_of_base
    (n : ℕ)
    (hbase :
      letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
      haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
        inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
      Subsingleton (Sheaf.HModule (C.left.divisorSheaf k
        (n • D.coordinateWeilDivisor (K := k))) 1)) :
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    haveI : SmoothOfRelativeDimension 1
        ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
    Subsingleton (Sheaf.HModule ((Scheme.baseChangeField C κ).left.divisorSheaf κ
      (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ))) 1) := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  letI hbase' : Subsingleton (Sheaf.HModule (C.left.divisorSheaf k
      (n • D.coordinateWeilDivisor (K := k))) 1) := hbase
  have htop : Subsingleton (Sheaf.HModule'
      (C.left.divisorSheaf k (n • D.coordinateWeilDivisor (K := k)))
      (C.left.twoCoverSquare D.V₀ D.V₁ D.cover).X₄ 1) := by
    change Subsingleton (Sheaf.HModule'
      (C.left.divisorSheaf k (n • D.coordinateWeilDivisor (K := k)))
      (⊤ : C.left.Opens) 1)
    exact (Sheaf.HModule.linearEquivHModule'
      (isTerminalTop : IsTerminal (⊤ : C.left.Opens))
      (C.left.divisorSheaf k (n • D.coordinateWeilDivisor (K := k))) 1).symm.toEquiv.subsingleton
  have hmd : Function.Surjective
      ((C.left.twoCoverSquare D.V₀ D.V₁ D.cover).moduleDiff
        (C.left.divisorSheaf k (n • D.coordinateWeilDivisor (K := k)))) :=
    (C.left.twoCoverSquare D.V₀ D.V₁ D.cover).moduleDiff_surjective_of_subsingleton_hModule'
      (C.left.divisorSheaf k (n • D.coordinateWeilDivisor (K := k))) htop
  have hd : Function.Surjective (D.coordinateDiff (K := k) n) :=
    surjective_left_of_comm (K := k)
      (D.coordinateSectionsEquivDom (K := k) n)
      (D.coordinateSectionsEquivOverlap (K := k) n)
      (D.coordinateDiff_intertwine (K := k) n) hmd
  letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
    .ofHom (Scheme.baseChangeField C κ).hom
  haveI : SmoothOfRelativeDimension 1
      ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
  have hdκ : Function.Surjective
      ((D.baseChangeField κ).coordinateDiff (K := κ) n) :=
    coordinateDiff_baseChangeField_surjective (κ := κ) (D := D) n hd
  have hmdκ : Function.Surjective
      (((Scheme.baseChangeField C κ).left.twoCoverSquare
        (D.baseChangeField κ).V₀ (D.baseChangeField κ).V₁
        (D.baseChangeField κ).cover).moduleDiff
        ((Scheme.baseChangeField C κ).left.divisorSheaf κ
          (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ)))) :=
    surjective_right_of_comm (K := κ)
      ((D.baseChangeField κ).coordinateSectionsEquivDom (K := κ) n)
      ((D.baseChangeField κ).coordinateSectionsEquivOverlap (K := κ) n)
      ((D.baseChangeField κ).coordinateDiff_intertwine (K := κ) n) hdκ
  letI : Subsingleton (Sheaf.HModule'
      ((Scheme.baseChangeField C κ).left.divisorSheaf κ
        (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ)))
      ((D.baseChangeField κ).V₀) 1) :=
    (D.baseChangeField κ).isAffineOpen_V₀.subsingleton_hModule'_divisorSheaf_one κ _
  letI : Subsingleton (Sheaf.HModule'
      ((Scheme.baseChangeField C κ).left.divisorSheaf κ
        (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ)))
      ((D.baseChangeField κ).V₁) 1) :=
    (D.baseChangeField κ).isAffineOpen_V₁.subsingleton_hModule'_divisorSheaf_one κ _
  letI : Subsingleton (Sheaf.HModule'
      ((Scheme.baseChangeField C κ).left.divisorSheaf κ
        (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ)))
      ((Scheme.baseChangeField C κ).left.twoCoverSquare
        (D.baseChangeField κ).V₀ (D.baseChangeField κ).V₁
        (D.baseChangeField κ).cover).X₂ 1) := by
    change Subsingleton (Sheaf.HModule'
      ((Scheme.baseChangeField C κ).left.divisorSheaf κ
        (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ)))
      ((D.baseChangeField κ).V₀) 1)
    infer_instance
  letI : Subsingleton (Sheaf.HModule'
      ((Scheme.baseChangeField C κ).left.divisorSheaf κ
        (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ)))
      ((Scheme.baseChangeField C κ).left.twoCoverSquare
        (D.baseChangeField κ).V₀ (D.baseChangeField κ).V₁
        (D.baseChangeField κ).cover).X₃ 1) := by
    change Subsingleton (Sheaf.HModule'
      ((Scheme.baseChangeField C κ).left.divisorSheaf κ
        (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ)))
      ((D.baseChangeField κ).V₁) 1)
    infer_instance
  have htopκ : Subsingleton (Sheaf.HModule'
      ((Scheme.baseChangeField C κ).left.divisorSheaf κ
        (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ)))
      ((Scheme.baseChangeField C κ).left.twoCoverSquare
        (D.baseChangeField κ).V₀ (D.baseChangeField κ).V₁
        (D.baseChangeField κ).cover).X₄ 1) :=
    ((Scheme.baseChangeField C κ).left.twoCoverSquare
      (D.baseChangeField κ).V₀ (D.baseChangeField κ).V₁
      (D.baseChangeField κ).cover).subsingleton_hModule'_of_moduleDiff_surjective
      ((Scheme.baseChangeField C κ).left.divisorSheaf κ
        (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ))) hmdκ
  have htopκ' : Subsingleton (Sheaf.HModule'
      ((Scheme.baseChangeField C κ).left.divisorSheaf κ
        (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ)))
      (⊤ : (Scheme.baseChangeField C κ).left.Opens) 1) := by
    change Subsingleton (Sheaf.HModule'
      ((Scheme.baseChangeField C κ).left.divisorSheaf κ
        (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ)))
      ((Scheme.baseChangeField C κ).left.twoCoverSquare
        (D.baseChangeField κ).V₀ (D.baseChangeField κ).V₁
        (D.baseChangeField κ).cover).X₄ 1)
    exact htopκ
  letI := htopκ'
  exact (Sheaf.HModule.linearEquivHModule'
    (isTerminalTop : IsTerminal (⊤ : (Scheme.baseChangeField C κ).left.Opens))
    ((Scheme.baseChangeField C κ).left.divisorSheaf κ
      (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ))) 1).toEquiv.subsingleton

end Transport
end FiberCoordinateData
end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

namespace FiberCoordinateData

section DegreeTransport

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom]
variable (κ : Type u) [Field κ] [Algebra k κ]
variable (D : FiberCoordinateData C.left)

theorem degree_coordinate_baseChange_eq
    (n : ℕ)
    (hbase :
      letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
      haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
        inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
      Subsingleton (Sheaf.HModule (C.left.divisorSheaf k
        (n • D.coordinateWeilDivisor (K := k))) 1)) :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    haveI : SmoothOfRelativeDimension 1
        ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
    CurveDivisor.deg κ (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ)) =
      CurveDivisor.deg k (n • D.coordinateWeilDivisor (K := k)) := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  letI hbase' : Subsingleton (Sheaf.HModule (C.left.divisorSheaf k
      (n • D.coordinateWeilDivisor (K := k))) 1) := hbase
  letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
    .ofHom (Scheme.baseChangeField C κ).hom
  haveI : SmoothOfRelativeDimension 1
      ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
  have h1ext : Subsingleton (Sheaf.HModule
      ((Scheme.baseChangeField C κ).left.divisorSheaf κ
        (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ))) 1) :=
    subsingleton_coordinate_baseChange_of_base κ D n hbase
  letI := h1ext
  have h0eq : Sheaf.h0 ((Scheme.baseChangeField C κ).left.divisorSheaf κ
      (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ))) =
      Sheaf.h0 (C.left.divisorSheaf k (n • D.coordinateWeilDivisor (K := k))) :=
    h0_coordinate_baseChange_eq κ D n hbase
  have hchiBase := chi_divisorSheaf_genus C
    (n • D.coordinateWeilDivisor (K := k))
  have hchiExt := chi_divisorSheaf_genus (Scheme.baseChangeField C κ)
    (n • (D.baseChangeField κ).coordinateWeilDivisor (K := κ))
  rw [Sheaf.chi_eq_h0 hbase'] at hchiBase
  rw [Sheaf.chi_eq_h0 h1ext] at hchiExt
  rw [genus_baseChangeField_curve C κ] at hchiExt
  rw [h0eq] at hchiExt
  omega

end DegreeTransport
end FiberCoordinateData
end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

namespace FiberCoordinateData

section FixedProducer

variable {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable def fixedCoordinateData : FiberCoordinateData C.left :=
  FiberCoordinateData.ofMap (fixedFiniteMapToP1 C)

noncomputable def fixedCoordinateDegree : ℤ := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  exact CurveDivisor.deg k (genus C •
    (fixedCoordinateData C).coordinateWeilDivisor (K := k))

theorem uniformBaseDivisor_fixedCoordinate :
    UniformBaseDivisor C (fixedCoordinateDegree C) := by
  apply uniformBaseDivisor_of_exists_deg_le C
  intro κ _ _
  letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
    .ofHom (Scheme.baseChangeField C κ).hom
  haveI : SmoothOfRelativeDimension 1
      ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
  have hbase :
      letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
      haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
        inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
      Subsingleton (Sheaf.HModule (C.left.divisorSheaf k
        (genus C • (fixedCoordinateData C).coordinateWeilDivisor (K := k))) 1) := by
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
    simpa only [fixedCoordinateData,
      FiberCoordinateData.coordinateWeilDivisor_ofMap] using
      subsingleton_hModule_divisorSheaf_one_genus_smul_fiber_curve C
        (fixedFiniteMapToP1 C) (fixedFiniteMapToP1_comp_structureMap C)
  have hvan := subsingleton_coordinate_baseChange_of_base κ
    (fixedCoordinateData C) (genus C) hbase
  have hdeg := degree_coordinate_baseChange_eq κ
    (fixedCoordinateData C) (genus C) hbase
  refine ⟨genus C • ((fixedCoordinateData C).baseChangeField κ).coordinateWeilDivisor,
    hvan, ?_⟩
  simpa only [fixedCoordinateDegree] using hdeg.le

/-- Large-degree `H^1` vanishing is uniform over every field extension of the ground field.
This is the unconditional endpoint of the fixed-coordinate degree construction. -/
theorem uniformVanishing_fixedCoordinate : UniformVanishing C :=
  uniformVanishing_of_uniformBaseDivisor_curve C (uniformBaseDivisor_fixedCoordinate C)

end FixedProducer
end FiberCoordinateData
end AlgebraicGeometry
