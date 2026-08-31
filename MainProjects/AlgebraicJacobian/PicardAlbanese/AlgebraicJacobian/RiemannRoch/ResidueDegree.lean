/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.ClosedPoint

/-!
# Finiteness and positivity of the residue degree at a closed point

For a scheme `X` smooth of relative dimension one over a field `K`, integral, and locally of
finite type (the curve bundle of the Jacobian challenge), the residue field `κ(x)` at a
non-generic (hence closed) point `x` is a *finite* extension of `K`, and its degree is
positive:

* `AlgebraicGeometry.Scheme.residueDeg_finite`: `κ(x)` is a finite `K`-module;
* `AlgebraicGeometry.Scheme.residueDeg_pos`: `0 < [κ(x) : K]`.

The `K`-module structure on `κ(x)` is the landed `Scheme.residueFieldOverModule K X x` (restriction
of scalars along the explicit ring hom `Scheme.residueOverAlgebraMap`), activated as a local
instance below.

## Mathematical route (Zariski's lemma through a chart)

A closed point `x` lies in a Dedekind affine chart `V ∋ x` with section ring `B := Γ(X, V)`; the
prime `q := hV.primeIdealOf ⟨x, _⟩` is nonzero, hence maximal, so `B ⧸ q` is a field. Two facts
combine:

1. **Finite type ⇒ finite (Zariski/Jacobson).** `K → B` is of finite type (locally of finite type
   applied to the chart), so `K → B → B ⧸ q` is a finite-type map into a *field*; over the
   Jacobson ring `K`, `finite_of_finite_type_of_isJacobsonRing` upgrades finite type to finite.
2. **`κ(x) ≅ B ⧸ q` `K`-linearly.** The stalk `𝒪_{X,x}` is the localization of `B` at `q`, so its
   residue field is `q.ResidueField`; for maximal `q` this is `B ⧸ q`. Transporting the module
   finiteness along this ring iso — shown `K`-linear by a compatibility of structure maps through
   the chart — gives finiteness of `κ(x)`.

Positivity is then `Module.finrank_pos_iff_of_free` for the nontrivial free finite module `κ(x)`
over the field `K`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

attribute [local instance] Scheme.residueFieldOverModule

/-- A nonzero-prime witness at a closed point of an affine Dedekind chart: on an integral scheme
with a domain section ring, the prime of `Γ(X, V)` cut out by a non-generic point of an affine open
is not `⊥`. (Re-derivation of the ne-bot fact used in `IsAffineOpen.isDiscreteValuationRing_stalk`.)
-/
private theorem primeIdealOf_ne_bot {X : Scheme.{u}} [IsIntegral X] {V : X.Opens}
    (hV : IsAffineOpen V) [IsDomain Γ(X, V)] {x : X} (hx : x ∈ V) (hxg : x ≠ genericPoint X) :
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal ≠ ⊥ := by
  intro h
  apply hxg
  have h1 : hV.fromSpec.base (hV.primeIdealOf ⟨x, hx⟩) = x := hV.fromSpec_primeIdealOf ⟨x, hx⟩
  have hgen : (genericPoint (Spec Γ(X, V)) : Spec Γ(X, V)) = hV.primeIdealOf ⟨x, hx⟩ := by
    rw [genericPoint_eq_bot_of_affine]
    exact (PrimeSpectrum.ext h).symm
  rw [← h1, ← hgen, genericPoint_eq_of_isOpenImmersion hV.fromSpec]

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

/-- **Finiteness of the residue degree at a closed point.** On an integral scheme smooth of
relative dimension one and locally of finite type over a field `K`, the residue field at a
non-generic point is a finite `K`-module. -/
theorem Scheme.residueDeg_finite
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {x : X} (hx : x ≠ genericPoint X) :
    Module.Finite K (X.residueField x) := by
  -- A Dedekind affine chart `V ∋ x`, its section ring `Γ(X, V)`, and the nonzero maximal prime `q`.
  obtain ⟨V, hV, hxV, hD⟩ :=
    SmoothOfRelativeDimension.exists_isDedekindDomain_section (X ↘ Spec (CommRingCat.of K)) x
  haveI := hD
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  set q := hV.primeIdealOf ⟨x, hxV⟩ with hq
  haveI : q.asIdeal.IsPrime := q.isPrime
  haveI hmax : q.asIdeal.IsMaximal := q.isPrime.isMaximal (primeIdealOf_ne_bot hV hxV hx)
  letI : Field (Γ(X, V) ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal
  -- The residue-field ring iso `B ⧸ q ≃+* κ(x)`, from the localization and the maximal quotient.
  set φ' := IsLocalization.algEquiv q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal)
    (X.presheaf.stalk x) with hφ'
  set m := IsLocalRing.ResidueField.mapEquiv φ'.toRingEquiv with hm
  set b := RingEquiv.ofBijective (algebraMap (Γ(X, V) ⧸ q.asIdeal) q.asIdeal.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal) with hb
  set e' := b.trans m with he'
  -- The finite-type structure map `ψ : K → B ⧸ q`.
  set ψ := (Ideal.Quotient.mk q.asIdeal).comp (X.overAlgebraMap K V) with hψ
  -- `κ(x)` seen through the chart: `residue ∘ germ_V ∘ overAlgebraMap_V`.
  have hmid : (X.presheaf.germ ⊤ x trivial).hom.comp (X.overAlgebraMap K ⊤)
      = (X.presheaf.germ V x hxV).hom.comp (X.overAlgebraMap K V) := by
    have hgr : X.presheaf.germ ⊤ x trivial
        = X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ X.presheaf.germ V x hxV :=
      (X.presheaf.germ_res (homOfLE (le_top : V ≤ ⊤)) x hxV).symm
    rw [hgr, CommRingCat.hom_comp, RingHom.comp_assoc,
      X.overAlgebraMap_naturality K (homOfLE (le_top : V ≤ ⊤)).op]
  have hchart : X.residueOverAlgebraMap K x
      = ((X.residue x).hom.comp (X.presheaf.germ V x hxV).hom).comp (X.overAlgebraMap K V) := by
    rw [Scheme.residueOverAlgebraMap, hmid, ← RingHom.comp_assoc]
  -- Core compatibility of the ring iso with the chart's residue map (no `K` involved).
  have hcore : e'.toRingHom.comp (Ideal.Quotient.mk q.asIdeal)
      = (X.residue x).hom.comp (X.presheaf.germ V x hxV).hom := by
    ext y
    simp only [he', hb, hm, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.trans_apply, RingEquiv.coe_ofBijective,
      IsLocalRing.ResidueField.mapEquiv_apply, Ideal.algebraMap_quotient_residueField_mk]
    rw [IsScalarTower.algebraMap_apply Γ(X, V) (Localization.AtPrime q.asIdeal)
        q.asIdeal.ResidueField, IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.ResidueField.map_residue]
    simp only [RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    rfl
  -- `K`-linear compatibility `e' (ψ c) = residueOverAlgebraMap c`.
  have hcompat : ∀ c : K, e' (ψ c) = X.residueOverAlgebraMap K x c := fun c => by
    have h := DFunLike.congr_fun hcore (X.overAlgebraMap K V c)
    rw [hchart]
    exact h
  -- Finiteness of `B ⧸ q` over `K` by Zariski's lemma (finite type into a field, Jacobson base).
  letI : Algebra K (Γ(X, V) ⧸ q.asIdeal) := ψ.toAlgebra
  have hoa : (X.overAlgebraMap K V).FiniteType := by
    have happ : X.overAlgebraMap K V = ((X ↘ Spec (CommRingCat.of K)).appLE ⊤ V le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := by
      rw [Scheme.overAlgebraMap, CommRingCat.hom_comp]; rfl
    rw [happ]
    exact RingHom.FiniteType.comp
      ((X ↘ Spec (CommRingCat.of K)).finiteType_appLE (isAffineOpen_top _) hV le_top)
      (RingHom.FiniteType.of_surjective _
        (((ConcreteCategory.isIso_iff_bijective
          (Scheme.ΓSpecIso (CommRingCat.of K)).inv).mp inferInstance).surjective))
  have hψft : ψ.FiniteType := by
    rw [hψ]; exact RingHom.FiniteType.comp_surjective hoa Ideal.Quotient.mk_surjective
  haveI : Algebra.FiniteType K (Γ(X, V) ⧸ q.asIdeal) := hψft
  have hfin : Module.Finite K (Γ(X, V) ⧸ q.asIdeal) :=
    finite_of_finite_type_of_isJacobsonRing K (Γ(X, V) ⧸ q.asIdeal)
  -- Transport finiteness `K`-linearly along `e'`.
  haveI := hfin
  refine Module.Finite.of_surjective
    ({ toFun := e'
       map_add' := map_add e'
       map_smul' := fun c z => by
         simp only [RingHom.id_apply]
         rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, hcompat c]
         rfl } :
      (Γ(X, V) ⧸ q.asIdeal) →ₗ[K] X.residueField x) e'.surjective

/-- **Positivity of the residue degree at a closed point.** On an integral scheme smooth of
relative dimension one and locally of finite type over a field `K`, the residue degree at a
non-generic point is positive. -/
theorem Scheme.residueDeg_pos
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {x : X} (hx : x ≠ genericPoint X) :
    0 < X.residueDeg K x := by
  haveI := Scheme.residueDeg_finite (K := K) hx
  change 0 < Module.finrank K (X.residueField x)
  exact (Module.finrank_pos_iff_of_free K (X.residueField x)).mpr inferInstance

end AlgebraicGeometry
