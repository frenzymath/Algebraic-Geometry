/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter1CurveStalks
import HartshorneLib.Chapter2ModuleKSheaf

/-!
# Residue degrees of closed points

For a scheme over `Spec K`, the residue field at a point is a `K`-algebra via the
structure morphism.  On a smooth integral curve, non-generic residue fields are
finite extensions of `K`; over an algebraically closed base their degree is one.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

section ResidueDegree

variable (K : Type u) [CommRing K] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of K))]

/-- The `K`-algebra structure map on the residue field `κ(x)`, through the stalk and residue
maps of the structure sheaf. -/
noncomputable def Scheme.residueOverAlgebraMap (x : X) : K →+* X.residueField x :=
  (X.residue x).hom.comp
    (((X.presheaf.germ ⊤ x trivial).hom).comp (X.overAlgebraMap K ⊤))

/-- Restriction of scalars along `residueOverAlgebraMap`; kept local where finrank is used. -/
@[reducible] noncomputable def Scheme.residueFieldOverModule (x : X) :
    Module K (X.residueField x) :=
  (X.residueOverAlgebraMap K x).toModule

attribute [local instance] Scheme.residueFieldOverModule

/-- The residue degree `[κ(x) : K]`. -/
noncomputable def Scheme.residueDeg (x : X) : ℕ :=
  Module.finrank K (X.residueField x)

end ResidueDegree

attribute [local instance] Scheme.residueFieldOverModule

variable {K : Type u} [Field K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))]

/-- A non-generic residue field on an integral smooth curve is finite over the base field. -/
theorem Scheme.residueDeg_finite
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {x : X} (hx : x ≠ genericPoint X) :
    Module.Finite K (X.residueField x) := by
  obtain ⟨V, hV, hxV, hD⟩ :=
    Hartshorne.smoothCurve_exists_dedekind_affineOpen
      (X ↘ Spec (CommRingCat.of K)) x
  haveI := hD
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  set q := hV.primeIdealOf ⟨x, hxV⟩ with hq
  haveI : q.asIdeal.IsPrime := q.isPrime
  have hbot : q.asIdeal ≠ ⊥ := by
    intro h
    apply hx
    have h1 : hV.fromSpec.base q = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
    have hgen : (genericPoint (Spec Γ(X, V)) : Spec Γ(X, V)) = q := by
      rw [genericPoint_eq_bot_of_affine]
      exact (PrimeSpectrum.ext h).symm
    rw [← h1, ← hgen, genericPoint_eq_of_isOpenImmersion hV.fromSpec]
  haveI hmax : q.asIdeal.IsMaximal := q.isPrime.isMaximal hbot
  letI : Field (Γ(X, V) ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal
  set φ' := IsLocalization.algEquiv q.asIdeal.primeCompl
    (Localization.AtPrime q.asIdeal) (X.presheaf.stalk x) with hφ'
  set m := IsLocalRing.ResidueField.mapEquiv φ'.toRingEquiv with hm
  set b := RingEquiv.ofBijective (algebraMap (Γ(X, V) ⧸ q.asIdeal) q.asIdeal.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal) with hb
  set e' := b.trans m with he'
  set ψ := (Ideal.Quotient.mk q.asIdeal).comp (X.overAlgebraMap K V) with hψ
  have hmid : (X.presheaf.germ ⊤ x trivial).hom.comp (X.overAlgebraMap K ⊤)
      = (X.presheaf.germ V x hxV).hom.comp (X.overAlgebraMap K V) := by
    have hgr : X.presheaf.germ ⊤ x trivial =
        X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫
          X.presheaf.germ V x hxV :=
      (X.presheaf.germ_res (homOfLE (le_top : V ≤ ⊤)) x hxV).symm
    rw [hgr, CommRingCat.hom_comp, RingHom.comp_assoc,
      X.overAlgebraMap_naturality K (homOfLE (le_top : V ≤ ⊤)).op]
  have hchart : X.residueOverAlgebraMap K x =
      ((X.residue x).hom.comp (X.presheaf.germ V x hxV).hom).comp
        (X.overAlgebraMap K V) := by
    rw [Scheme.residueOverAlgebraMap, hmid, ← RingHom.comp_assoc]
  have hcore : e'.toRingHom.comp (Ideal.Quotient.mk q.asIdeal) =
      (X.residue x).hom.comp (X.presheaf.germ V x hxV).hom := by
    ext y
    simp only [he', hb, hm, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.trans_apply, RingEquiv.coe_ofBijective,
      IsLocalRing.ResidueField.mapEquiv_apply,
      Ideal.algebraMap_quotient_residueField_mk]
    rw [IsScalarTower.algebraMap_apply Γ(X, V) (Localization.AtPrime q.asIdeal)
        q.asIdeal.ResidueField, IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.ResidueField.map_residue]
    simp only [RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    rfl
  have hcompat : ∀ c : K, e' (ψ c) = X.residueOverAlgebraMap K x c := fun c => by
    have h := DFunLike.congr_fun hcore (X.overAlgebraMap K V c)
    rw [hchart]
    exact h
  letI : Algebra K (Γ(X, V) ⧸ q.asIdeal) := ψ.toAlgebra
  have hoa : (X.overAlgebraMap K V).FiniteType := by
    have happ : X.overAlgebraMap K V =
        ((X ↘ Spec (CommRingCat.of K)).appLE ⊤ V le_top).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := by
      rw [Scheme.overAlgebraMap, CommRingCat.hom_comp]
      rfl
    rw [happ]
    exact RingHom.FiniteType.comp
      ((X ↘ Spec (CommRingCat.of K)).finiteType_appLE (isAffineOpen_top _) hV le_top)
      (RingHom.FiniteType.of_surjective _
        (((ConcreteCategory.isIso_iff_bijective
          (Scheme.ΓSpecIso (CommRingCat.of K)).inv).mp inferInstance).surjective))
  have hψft : ψ.FiniteType := by
    rw [hψ]
    exact RingHom.FiniteType.comp_surjective hoa Ideal.Quotient.mk_surjective
  letI : Algebra.FiniteType K (Γ(X, V) ⧸ q.asIdeal) := hψft
  have hfin : Module.Finite K (Γ(X, V) ⧸ q.asIdeal) :=
    finite_of_finite_type_of_isJacobsonRing K (Γ(X, V) ⧸ q.asIdeal)
  letI := hfin
  refine Module.Finite.of_surjective
    ({ toFun := e'
       map_add' := map_add e'
       map_smul' := fun c z => by
         simp only [RingHom.id_apply]
         rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, hcompat c]
         rfl } :
      (Γ(X, V) ⧸ q.asIdeal) →ₗ[K] X.residueField x) e'.surjective

/-- A non-generic residue degree on an integral smooth curve is positive. -/
theorem Scheme.residueDeg_pos
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {x : X} (hx : x ≠ genericPoint X) :
    0 < X.residueDeg K x := by
  letI := Scheme.residueDeg_finite (K := K) hx
  change 0 < Module.finrank K (X.residueField x)
  exact (Module.finrank_pos_iff_of_free K (X.residueField x)).mpr inferInstance

/-- Over an algebraically closed field, every non-generic residue field has degree one. -/
theorem Scheme.residueDeg_eq_one_of_isAlgClosed
    [IsAlgClosed K]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {x : X} (hx : x ≠ genericPoint X) :
    X.residueDeg K x = 1 := by
  letI := Scheme.residueDeg_finite (K := K) hx
  letI : Algebra K (X.residueField x) :=
    (X.residueOverAlgebraMap K x).toAlgebra
  letI : Algebra.IsIntegral K (X.residueField x) :=
    Algebra.IsIntegral.of_finite K _
  have hbij : Function.Bijective (algebraMap K (X.residueField x)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  change Module.finrank K (X.residueField x) = 1
  have e : K ≃ₗ[K] X.residueField x :=
    LinearEquiv.ofBijective (Algebra.linearMap K (X.residueField x)) hbij
  rw [← e.finrank_eq, Module.finrank_self]

end AlgebraicGeometry
