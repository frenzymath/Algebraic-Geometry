/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.FiniteGaloisQuotient

/-!
# The affine finite Galois quotient theorem (campaign `G2`, affine model)

Let `L/K` be a finite Galois extension with group `Γ = Gal(L/K)` and let `A` be an
`L`-algebra with a semilinear `Γ`-action (`specSemilinearGalAction`, the affine model
of `AlgebraicJacobian.Picard.FiniteGaloisQuotient`).  This file proves the wave-2
milestone of campaign `G2`: `Spec (A^Γ) ⟶ Spec K` **is a finite Galois quotient** of
`Spec A` — the full `IsGaloisQuotient` predicate (`isGaloisQuotient_spec`) — by
Speiser descent only, never Noether invariant finiteness.

## Structure of the proof

1. **The base-change isomorphism** `Spec A^Γ ×_{Spec K} Spec L ≅ Spec A`
   (`affineQuotientPullbackIso`): mathlib's `pullbackSpecIso K (A^Γ) L` composed with
   the tensor-factor swap `Spec (A^Γ ⊗[K] L) ≅ Spec (L ⊗[K] A^Γ)` (the engine
   convention keeps the Galois-acted factor `L` on the **left**; the swap is where
   the two conventions are bridged) and with `Spec` of the Speiser descent
   isomorphism `descentAlgEquiv : L ⊗[K] A^Γ ≃ₐ[L] A`.  It is over `Spec L`
   (`affineQuotientPullbackIso_hom_specMap`) and `Γ`-equivariant
   (`isEquivariant_affineQuotientPullbackIso_hom`); equivariance through the swap is
   checked on the two pullback projections (`toSpecAut_hom_pullbackSpecLIso_inv`).

2. **The `T`-points property for affine `T`**
   (`existsUnique_pullbackBaseChange_of_affine`): the scheme-level transport of the
   proved algebraic Hom property `affineGaloisQuotientHomEquiv`, along the
   identification `T ×_{Spec K} Spec L ≅ Spec (L ⊗[K] B)` (`pullbackSpecLIso`) for
   `T = Spec B`.  The workhorse `pullbackBaseChange_comp_affineQuotientPullbackIso_hom`
   computes the base change of any `u : Spec B ⟶ Spec A^Γ` over `Spec K` through the
   descent isomorphism as `Spec` of `extendScalarsAlgHom` of its algebra map.

3. **The `T`-points property for all schemes `T`**: uniqueness globalizes first from
   an affine open cover (`affineQuotient_hom_unique` — morphisms of schemes are
   determined on an open cover, and on each affine piece the affine `∃!` applies);
   existence then glues the local affine solutions via `Scheme.Cover.glueMorphisms`,
   with agreement on the (possibly non-affine) overlaps supplied by the globalized
   uniqueness.  This order breaks the apparent circularity: overlap pieces of an
   affine cover of a non-separated `T` need not be affine.

The gate `HasGaloisQuotient` is instance-free **only off the affine locus** now: this
file's theorem was generalised from the affine *model* to every affine total space in
`Picard/GaloisQuotientAffineGeneral.lean`, whose `hasGaloisQuotient_of_isAffine` is a
global instance. The residue is the non-affine case, where the Hironaka trap bites (see
the module docstring of `FiniteGaloisQuotient`). The affine-model theorem proved here is
legitimately unconditional because `Spec A` *is* a single `Γ`-stable affine chart.
**`HasStableAffineCover` is no longer instance-free** — `G2(a)` was discharged
after this sentence was written, and `StableAffineCover.lean:279` derives it as a
global instance from `[ρ.OrbitsInAffineOpen]` (measured `review-ajc`, 2026-07-29:
`infer_instance` succeeds for an abstract `ρ` with the orbit hypothesis, fails
without it).

Campaign reference: `G2` of `informal/pic-representability-campaign.md` (Kleiman,
*The Picard scheme* §4; Milne, *Jacobian Varieties* §4; the affine heart is Speiser's
theorem, `SemilinearAlgebras.descentAlgEquiv`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicJacobian.GaloisDescent

open SemilinearAction

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-! ## `Spec` of a ring equivalence -/

section SpecRingEquivIso

/-- The isomorphism of spectra induced by a ring equivalence `ψ : S ≃+* T`.  By the
contravariance of `Spec`, the *hom* `Spec S ⟶ Spec T` is `Spec.map` of `ψ.symm`. -/
noncomputable def specRingEquivIso {S T : Type u} [CommRing S] [CommRing T]
    (ψ : S ≃+* T) : Spec (CommRingCat.of S) ≅ Spec (CommRingCat.of T) where
  hom := Spec.map (CommRingCat.ofHom (ψ.symm : T →+* S))
  inv := Spec.map (CommRingCat.ofHom (ψ : S →+* T))
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show ((ψ.symm : T →+* S).comp (ψ : S →+* T)) = RingHom.id S from
        RingHom.ext fun s => ψ.symm_apply_apply s,
      CommRingCat.ofHom_id, Spec.map_id]
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show ((ψ : S →+* T).comp (ψ.symm : T →+* S)) = RingHom.id T from
        RingHom.ext fun t => ψ.apply_symm_apply t,
      CommRingCat.ofHom_id, Spec.map_id]

@[simp] lemma specRingEquivIso_hom {S T : Type u} [CommRing S] [CommRing T]
    (ψ : S ≃+* T) :
    (specRingEquivIso ψ).hom = Spec.map (CommRingCat.ofHom (ψ.symm : T →+* S)) := rfl

@[simp] lemma specRingEquivIso_inv {S T : Type u} [CommRing S] [CommRing T]
    (ψ : S ≃+* T) :
    (specRingEquivIso ψ).inv = Spec.map (CommRingCat.ofHom (ψ : S →+* T)) := rfl

end SpecRingEquivIso

/-! ## Composition calculus for `pullbackBaseChange` -/

section BaseChangeCalculus

/-- Base change is functorial: the base change of a composite of morphisms over
`Spec K` is the composite of the base changes. -/
@[reassoc]
lemma pullbackBaseChange_comp {T' T Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of K)) (t : T ⟶ Spec (CommRingCat.of K))
    (t' : T' ⟶ Spec (CommRingCat.of K)) (u : T ⟶ Y) (hu : u ≫ g = t)
    (v : T' ⟶ T) (hv : v ≫ t = t') :
    pullbackBaseChange K L g t' (v ≫ u) (by rw [Category.assoc, hu, hv])
      = pullbackBaseChange K L t t' v hv ≫ pullbackBaseChange K L g t u hu := by
  apply pullback.hom_ext <;> simp

/-- `pullbackBaseChange` only depends on the underlying morphism. -/
lemma pullbackBaseChange_congr {T Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of K)) (t : T ⟶ Spec (CommRingCat.of K))
    {u u' : T ⟶ Y} (huu' : u = u') (hu : u ≫ g = t) :
    pullbackBaseChange K L g t u hu = pullbackBaseChange K L g t u' (huu' ▸ hu) := by
  subst huu'; rfl

end BaseChangeCalculus

/-- `Spec` of a `K`-algebra map is a morphism over `Spec K`. -/
lemma specMap_algHom_comp {C D : Type u} [CommRing C] [CommRing D] [Algebra K C]
    [Algebra K D] (φ : C →ₐ[K] D) :
    Spec.map (CommRingCat.ofHom φ.toRingHom)
        ≫ Spec.map (CommRingCat.ofHom (algebraMap K C))
      = Spec.map (CommRingCat.ofHom (algebraMap K D)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact φ.comp_algebraMap

/-! ## The base change of an affine scheme, in engine order `L ⊗[K] ·` -/

section PullbackSpecLIso

variable (C : Type u) [CommRing C] [Algebra K C]

/-- For affine `T = Spec C` over `Spec K`, the base change `T ×_{Spec K} Spec L` is
`Spec (L ⊗[K] C)`, with the tensor factors in the engine order (the Galois-acted
factor `L` on the **left**): mathlib's `pullbackSpecIso` composed with the factor
swap `Algebra.TensorProduct.comm`. -/
noncomputable def pullbackSpecLIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap K C)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      ≅ Spec (CommRingCat.of (L ⊗[K] C)) :=
  pullbackSpecIso K C L ≪≫
    specRingEquivIso (Algebra.TensorProduct.comm K C L).toRingEquiv

@[reassoc (attr := simp)]
lemma pullbackSpecLIso_inv_fst :
    (pullbackSpecLIso K L C).inv ≫ pullback.fst _ _
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : C →ₐ[K] L ⊗[K] C).toRingHom) := by
  simp only [pullbackSpecLIso, Iso.trans_inv, specRingEquivIso_inv]
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

@[reassoc (attr := simp)]
lemma pullbackSpecLIso_inv_snd :
    (pullbackSpecLIso K L C).inv ≫ pullback.snd _ _
      = Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] C))) := by
  simp only [pullbackSpecLIso, Iso.trans_inv, specRingEquivIso_inv]
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- Equivariance of `pullbackSpecLIso`, inverse form: the `toSpecAut` action of `γ`
on `Spec (L ⊗[K] C)` (left-factor Galois action) corresponds to the canonical
base-change action `pullbackGalMap` on `Spec C ×_{Spec K} Spec L`. -/
lemma toSpecAut_hom_pullbackSpecLIso_inv (γ : L ≃ₐ[K] L) :
    (toSpecAut (L ≃ₐ[K] L) (L ⊗[K] C) γ).hom ≫ (pullbackSpecLIso K L C).inv
      = (pullbackSpecLIso K L C).inv
          ≫ pullbackGalMap K L (Spec.map (CommRingCat.ofHom (algebraMap K C))) γ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullbackGalMap_fst, pullbackSpecLIso_inv_fst,
      toSpecAut_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext c
    change γ⁻¹ • ((1 : L) ⊗ₜ[K] c) = (1 : L) ⊗ₜ[K] c
    rw [galTensor_smul_def]
    simp
  · rw [Category.assoc, Category.assoc, pullbackGalMap_snd,
      pullbackSpecLIso_inv_snd_assoc, pullbackSpecLIso_inv_snd, toSpecAut_hom,
      toSpecAut_hom, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2

/-- Equivariance of `pullbackSpecLIso`, hom form. -/
lemma pullbackGalMap_pullbackSpecLIso_hom (γ : L ≃ₐ[K] L) :
    pullbackGalMap K L (Spec.map (CommRingCat.ofHom (algebraMap K C))) γ
        ≫ (pullbackSpecLIso K L C).hom
      = (pullbackSpecLIso K L C).hom ≫ (toSpecAut (L ≃ₐ[K] L) (L ⊗[K] C) γ).hom := by
  rw [← cancel_epi (pullbackSpecLIso K L C).inv, ← Category.assoc,
    ← toSpecAut_hom_pullbackSpecLIso_inv, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Iso.inv_hom_id_assoc]

/-- Naturality of `pullbackSpecLIso` in the affine base: the base change of `Spec`
of a `K`-algebra map `φ : C →ₐ[K] D` corresponds to `Spec (id_L ⊗ φ)`. -/
lemma pullbackSpecLIso_inv_pullbackBaseChange {D : Type u} [CommRing D] [Algebra K D]
    (φ : C →ₐ[K] D) :
    (pullbackSpecLIso K L D).inv
        ≫ pullbackBaseChange K L (Spec.map (CommRingCat.ofHom (algebraMap K C)))
            (Spec.map (CommRingCat.ofHom (algebraMap K D)))
            (Spec.map (CommRingCat.ofHom φ.toRingHom)) (specMap_algHom_comp K φ)
      = Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.map (AlgHom.id L L) φ).toRingHom)
        ≫ (pullbackSpecLIso K L C).inv := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullbackBaseChange_fst,
      pullbackSpecLIso_inv_fst_assoc, pullbackSpecLIso_inv_fst, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
  · rw [Category.assoc, Category.assoc, pullbackBaseChange_snd,
      pullbackSpecLIso_inv_snd, pullbackSpecLIso_inv_snd, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    change algebraMap L (L ⊗[K] D) a
      = Algebra.TensorProduct.map (AlgHom.id L L) φ (algebraMap L (L ⊗[K] C) a)
    change a ⊗ₜ[K] (1 : D) = Algebra.TensorProduct.map (AlgHom.id L L) φ (a ⊗ₜ[K] (1 : C))
    simp

end PullbackSpecLIso

/-! ## The equivariant base-change isomorphism `Spec A^Γ ×_{Spec K} Spec L ≅ Spec A` -/

section AffineGaloisQuotient

variable (A : Type u) [CommRing A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]
variable [MulSemiringAction (L ≃ₐ[K] L) A] [IsSemilinear K L A]
variable [FiniteDimensional K L] [IsGalois K L]

omit [Algebra K A] [IsScalarTower K L A] [FiniteDimensional K L] [IsGalois K L] in
@[simp] lemma specSemilinearGalAction_act (γ : L ≃ₐ[K] L) :
    (specSemilinearGalAction K L A).act γ = toSpecAut (L ≃ₐ[K] L) A γ := rfl

/-- **The `Γ`-equivariant base-change isomorphism** (Speiser descent, `Spec` form):
`Spec (A^Γ) ×_{Spec K} Spec L ≅ Spec A`, the composite of `pullbackSpecLIso` with
`Spec` of the descent isomorphism `L ⊗[K] A^Γ ≃ₐ[L] A`. -/
noncomputable def affineQuotientPullbackIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A))))
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      ≅ Spec (CommRingCat.of A) :=
  pullbackSpecLIso K L (invariantsSubalgebra K L A) ≪≫
    specRingEquivIso (descentAlgEquiv K L A).toRingEquiv

/-- The descent isomorphism is a morphism over `Spec L` (inverse form). -/
@[reassoc (attr := simp)]
theorem affineQuotientPullbackIso_inv_snd :
    (affineQuotientPullbackIso K L A).inv ≫ pullback.snd _ _
      = Spec.map (CommRingCat.ofHom (algebraMap L A)) := by
  simp only [affineQuotientPullbackIso, Iso.trans_inv, specRingEquivIso_inv]
  rw [Category.assoc, pullbackSpecLIso_inv_snd, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  exact (descentAlgEquiv K L A).commutes a

/-- The quotient projection underlying the named base-change isomorphism is the
canonical map induced by the inclusion of the invariant subalgebra.  This is the
projection identity used to restrict the quotient to stable open subsets. -/
@[reassoc]
theorem affineQuotientPullbackIso_inv_fst :
    (affineQuotientPullbackIso K L A).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (SemilinearAction.invariantsSubalgebra K L A).val) := by
  simp only [affineQuotientPullbackIso, Iso.trans_inv, specRingEquivIso_inv]
  rw [Category.assoc, pullbackSpecLIso_inv_fst, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext w
  change SemilinearAction.descentAlgEquiv K L A (1 ⊗ₜ[K] w) = (w : A)
  rw [SemilinearAction.descentAlgEquiv_tmul, one_smul]

/-- The descent isomorphism is a morphism over `Spec L` (clause 1 of
`IsGaloisQuotient`). -/
@[reassoc (attr := simp)]
theorem affineQuotientPullbackIso_hom_specMap :
    (affineQuotientPullbackIso K L A).hom
        ≫ Spec.map (CommRingCat.ofHom (algebraMap L A))
      = pullback.snd _ _ := by
  rw [← affineQuotientPullbackIso_inv_snd K L A, Iso.hom_inv_id_assoc]

/-- The descent isomorphism is `Γ`-equivariant (clause 2 of `IsGaloisQuotient`). -/
theorem isEquivariant_affineQuotientPullbackIso_hom :
    (pullbackSemilinearGalAction K L
        (Spec.map (CommRingCat.ofHom
          (algebraMap K (invariantsSubalgebra K L A))))).IsEquivariant
      (specSemilinearGalAction K L A) (affineQuotientPullbackIso K L A).hom := by
  intro γ
  rw [pullbackSemilinearGalAction_act_hom, specSemilinearGalAction_act]
  simp only [affineQuotientPullbackIso, Iso.trans_hom]
  rw [← Category.assoc, pullbackGalMap_pullbackSpecLIso_hom, Category.assoc,
    Category.assoc]
  congr 1
  rw [toSpecAut_hom, toSpecAut_hom, specRingEquivIso_hom, ← Spec.map_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  change γ⁻¹ • ((descentAlgEquiv K L A).symm x) = (descentAlgEquiv K L A).symm (γ⁻¹ • x)
  apply (descentAlgEquiv K L A).injective
  rw [galTensor_smul_def, descentAlgEquiv_map_left, AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]

/-! ## The `T`-points property, affine case -/

variable (B : Type u) [CommRing B] [Algebra K B]

/-- The base change of `Spec` of a `K`-algebra map `φ : A^Γ →ₐ[K] B`, composed with
the descent isomorphism, is `Spec` of `extendScalarsAlgHom φ : A →ₐ[L] L ⊗[K] B`
read through `pullbackSpecLIso`.  Scheme-level form of the forward direction of
`invariantAlgHomEquiv`. -/
theorem pullbackBaseChange_specMap_algHom_comp_hom
    (φ : invariantsSubalgebra K L A →ₐ[K] B) :
    pullbackBaseChange K L
        (Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A))))
        (Spec.map (CommRingCat.ofHom (algebraMap K B)))
        (Spec.map (CommRingCat.ofHom φ.toRingHom)) (specMap_algHom_comp K φ)
      ≫ (affineQuotientPullbackIso K L A).hom
      = (pullbackSpecLIso K L B).hom
          ≫ Spec.map (CommRingCat.ofHom (extendScalarsAlgHom K L A B φ).toRingHom) := by
  rw [← Iso.inv_comp_eq]
  simp only [affineQuotientPullbackIso, Iso.trans_hom]
  rw [← Category.assoc, pullbackSpecLIso_inv_pullbackBaseChange K L _ φ,
    Category.assoc, Iso.inv_hom_id_assoc, specRingEquivIso_hom, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2

/-- The value of `affineGaloisQuotientHomEquiv` is `Spec` of `extendScalarsAlgHom` of
the corresponding algebra map (definitional unfolding). -/
lemma affineGaloisQuotientHomEquiv_apply_coe
    (u : {u : Spec (CommRingCat.of B) ⟶
        Spec (CommRingCat.of (invariantsSubalgebra K L A)) //
      u ≫ Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A)))
        = Spec.map (CommRingCat.ofHom (algebraMap K B))}) :
    (affineGaloisQuotientHomEquiv K L A B u).1
      = Spec.map (CommRingCat.ofHom (extendScalarsAlgHom K L A B
          (specOverEquivAlgHom K (invariantsSubalgebra K L A) B u)).toRingHom) := rfl

/-- The base change of any morphism `Spec B ⟶ Spec A^Γ` over `Spec K`, composed with
the descent isomorphism, computes as the corresponding equivariant morphism
`Spec (L ⊗[K] B) ⟶ Spec A` of `affineGaloisQuotientHomEquiv`, read through
`pullbackSpecLIso`. -/
theorem pullbackBaseChange_comp_affineQuotientPullbackIso_hom
    (u : {u : Spec (CommRingCat.of B) ⟶
        Spec (CommRingCat.of (invariantsSubalgebra K L A)) //
      u ≫ Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A)))
        = Spec.map (CommRingCat.ofHom (algebraMap K B))}) :
    pullbackBaseChange K L
        (Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A))))
        (Spec.map (CommRingCat.ofHom (algebraMap K B))) u.1 u.2
      ≫ (affineQuotientPullbackIso K L A).hom
      = (pullbackSpecLIso K L B).hom ≫ (affineGaloisQuotientHomEquiv K L A B u).1 := by
  have hu1 : u.1 = Spec.map (CommRingCat.ofHom
      (specOverEquivAlgHom K (invariantsSubalgebra K L A) B u).toRingHom) :=
    congrArg Subtype.val
      ((specOverEquivAlgHom K (invariantsSubalgebra K L A) B).symm_apply_apply u).symm
  rw [pullbackBaseChange_congr K L _ _ hu1,
    pullbackBaseChange_specMap_algHom_comp_hom, affineGaloisQuotientHomEquiv_apply_coe]

/-- **The `T`-points property of the affine Galois quotient, affine `T`** (campaign
`G2(b)`, `∃!` form): for affine `T = Spec B` over `Spec K`, every `Γ`-equivariant
morphism `T ×_{Spec K} Spec L ⟶ Spec A` over `Spec L` descends uniquely through the
descent isomorphism to `T ⟶ Spec (A^Γ)` over `Spec K`.  Speiser descent
(`affineGaloisQuotientHomEquiv`), never Noether invariant finiteness. -/
theorem existsUnique_pullbackBaseChange_of_affine
    (t : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of K))
    (ht : t = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    (h : pullback t (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      ⟶ Spec (CommRingCat.of A))
    (hover : h ≫ Spec.map (CommRingCat.ofHom (algebraMap L A)) = pullback.snd _ _)
    (hequiv : (pullbackSemilinearGalAction K L t).IsEquivariant
      (specSemilinearGalAction K L A) h) :
    ∃! u : {u : Spec (CommRingCat.of B) ⟶
        Spec (CommRingCat.of (invariantsSubalgebra K L A)) //
      u ≫ Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A))) = t},
      pullbackBaseChange K L
          (Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A))))
          t u.1 u.2
        ≫ (affineQuotientPullbackIso K L A).hom = h := by
  subst ht
  have hover' : ((pullbackSpecLIso K L B).inv ≫ h)
      ≫ Spec.map (CommRingCat.ofHom (algebraMap L A))
      = Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] B))) := by
    rw [Category.assoc, hover, pullbackSpecLIso_inv_snd]
  have hequiv' : ∀ γ : L ≃ₐ[K] L,
      (toSpecAut (L ≃ₐ[K] L) (L ⊗[K] B) γ).hom ≫ ((pullbackSpecLIso K L B).inv ≫ h)
        = ((pullbackSpecLIso K L B).inv ≫ h) ≫ (toSpecAut (L ≃ₐ[K] L) A γ).hom := by
    intro γ
    have h1 := hequiv γ
    rw [pullbackSemilinearGalAction_act_hom, specSemilinearGalAction_act] at h1
    rw [← Category.assoc, toSpecAut_hom_pullbackSpecLIso_inv, Category.assoc,
      Category.assoc, h1]
  set w := (affineGaloisQuotientHomEquiv K L A B).symm
      ⟨(pullbackSpecLIso K L B).inv ≫ h, hover', hequiv'⟩ with hwdef
  have hclause : pullbackBaseChange K L
      (Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A))))
      (Spec.map (CommRingCat.ofHom (algebraMap K B))) w.1 w.2
      ≫ (affineQuotientPullbackIso K L A).hom = h := by
    rw [pullbackBaseChange_comp_affineQuotientPullbackIso_hom, hwdef,
      Equiv.apply_symm_apply]
    exact Iso.hom_inv_id_assoc _ _
  refine ⟨w, hclause, fun y hy => ?_⟩
  replace hy : pullbackBaseChange K L
      (Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A))))
      (Spec.map (CommRingCat.ofHom (algebraMap K B))) y.1 y.2
      ≫ (affineQuotientPullbackIso K L A).hom = h := hy
  apply (affineGaloisQuotientHomEquiv K L A B).injective
  apply Subtype.ext
  rw [hwdef, Equiv.apply_symm_apply]
  change (affineGaloisQuotientHomEquiv K L A B y).1 = (pullbackSpecLIso K L B).inv ≫ h
  rw [pullbackBaseChange_comp_affineQuotientPullbackIso_hom] at hy
  rw [← hy, Iso.inv_hom_id_assoc]

/-! ## Globalized uniqueness -/

/-- **Globalized uniqueness of the descended morphism**: for *any* scheme `T` over
`Spec K`, two morphisms `T ⟶ Spec (A^Γ)` over `Spec K` with the same base change
through the descent isomorphism are equal.  Restrict to an affine open cover and
apply the uniqueness clause of the affine `∃!`; morphisms of schemes are determined
by their restrictions to an open cover. -/
theorem affineQuotient_hom_unique {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)}
    {u₁ u₂ : T ⟶ Spec (CommRingCat.of (invariantsSubalgebra K L A))}
    (hu₁ : u₁ ≫ Spec.map (CommRingCat.ofHom
      (algebraMap K (invariantsSubalgebra K L A))) = t)
    (hu₂ : u₂ ≫ Spec.map (CommRingCat.ofHom
      (algebraMap K (invariantsSubalgebra K L A))) = t)
    (heq : pullbackBaseChange K L _ t u₁ hu₁ ≫ (affineQuotientPullbackIso K L A).hom
      = pullbackBaseChange K L _ t u₂ hu₂ ≫ (affineQuotientPullbackIso K L A).hom) :
    u₁ = u₂ := by
  apply T.affineOpenCover.openCover.hom_ext
  change ∀ i : T.affineOpenCover.I₀,
    T.affineOpenCover.f i ≫ u₁ = T.affineOpenCover.f i ≫ u₂
  intro i
  letI : Algebra K ↥(T.affineOpenCover.X i) :=
    ((Spec.preimage (T.affineOpenCover.f i ≫ t)).hom).toAlgebra
  have ht : T.affineOpenCover.f i ≫ t
      = Spec.map (CommRingCat.ofHom (algebraMap K ↥(T.affineOpenCover.X i))) := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  -- `@`-application: re-synthesis of `Algebra K ↥(𝒜.X i)` diverges (the instance
  -- search unfolds the affine-cover choice term), so pass the `letI` explicitly.
  have hEU := @existsUnique_pullbackBaseChange_of_affine K L _ _ _ A _ _ _ _ _ _ _ _
    ↥(T.affineOpenCover.X i) _ this
    (T.affineOpenCover.f i ≫ t) ht
    (pullbackBaseChange K L t (T.affineOpenCover.f i ≫ t) (T.affineOpenCover.f i) rfl
      ≫ pullbackBaseChange K L _ t u₁ hu₁ ≫ (affineQuotientPullbackIso K L A).hom)
    (by
      rw [Category.assoc, Category.assoc, affineQuotientPullbackIso_hom_specMap,
        pullbackBaseChange_snd]
      exact pullbackBaseChange_snd K L t _ (T.affineOpenCover.f i) rfl)
    (SemilinearGalAction.isEquivariant_pullbackBaseChange_comp t _
      (specSemilinearGalAction K L A)
      (SemilinearGalAction.isEquivariant_pullbackBaseChange_comp _ t
        (specSemilinearGalAction K L A)
        (isEquivariant_affineQuotientPullbackIso_hom K L A) u₁ hu₁)
      (T.affineOpenCover.f i) rfl)
  have h₁ : pullbackBaseChange K L
        (Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A))))
        (T.affineOpenCover.f i ≫ t) (T.affineOpenCover.f i ≫ u₁)
        (by rw [Category.assoc, hu₁])
      ≫ (affineQuotientPullbackIso K L A).hom
      = pullbackBaseChange K L t (T.affineOpenCover.f i ≫ t) (T.affineOpenCover.f i) rfl
        ≫ pullbackBaseChange K L _ t u₁ hu₁ ≫ (affineQuotientPullbackIso K L A).hom := by
    rw [pullbackBaseChange_comp K L _ t _ u₁ hu₁ (T.affineOpenCover.f i) rfl,
      Category.assoc]
  have h₂ : pullbackBaseChange K L
        (Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A))))
        (T.affineOpenCover.f i ≫ t) (T.affineOpenCover.f i ≫ u₂)
        (by rw [Category.assoc, hu₂])
      ≫ (affineQuotientPullbackIso K L A).hom
      = pullbackBaseChange K L t (T.affineOpenCover.f i ≫ t) (T.affineOpenCover.f i) rfl
        ≫ pullbackBaseChange K L _ t u₁ hu₁ ≫ (affineQuotientPullbackIso K L A).hom := by
    rw [pullbackBaseChange_comp K L _ t _ u₂ hu₂ (T.affineOpenCover.f i) rfl,
      Category.assoc, heq]
  exact congrArg Subtype.val
    (hEU.unique (y₁ := ⟨T.affineOpenCover.f i ≫ u₁, by rw [Category.assoc, hu₁]⟩)
      (y₂ := ⟨T.affineOpenCover.f i ≫ u₂, by rw [Category.assoc, hu₂]⟩) h₁ h₂)

/-! ## The fixed-isomorphism universal property and the main theorem -/

/-- **The universal `T`-points property for the named affine quotient
isomorphism** `affineQuotientPullbackIso`.

This is clause 3 of `isGaloisQuotient_spec`, exposed before it is packaged into
the proposition-valued `IsGaloisQuotient`.  Open restriction needs the equation
against this particular isomorphism: choosing an arbitrary existential witness
from the packaged predicate could twist the resulting quotient projection by an
automorphism. -/
theorem affineQuotient_existsUnique (T : Scheme.{u})
    (t : T ⟶ Spec (CommRingCat.of K))
    (h : pullback t (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶
      Spec (CommRingCat.of A))
    (hover : h ≫ Spec.map (CommRingCat.ofHom (algebraMap L A)) =
      pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (hequiv : (pullbackSemilinearGalAction K L t).IsEquivariant
      (specSemilinearGalAction K L A) h) :
    ∃! u : {u : T ⟶ Spec (CommRingCat.of (invariantsSubalgebra K L A)) //
        u ≫ Spec.map (CommRingCat.ofHom
          (algebraMap K (invariantsSubalgebra K L A))) = t},
      pullbackBaseChange K L
          (Spec.map (CommRingCat.ofHom
            (algebraMap K (invariantsSubalgebra K L A)))) t u.1 u.2 ≫
        (affineQuotientPullbackIso K L A).hom = h := by
  -- local affine solutions on the pieces of an affine open cover
  have hloc : ∀ i : T.affineOpenCover.I₀,
      ∃ u : {u : Spec (T.affineOpenCover.X i) ⟶
          Spec (CommRingCat.of (invariantsSubalgebra K L A)) //
        u ≫ Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A)))
          = T.affineOpenCover.f i ≫ t},
        pullbackBaseChange K L
            (Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A))))
            (T.affineOpenCover.f i ≫ t) u.1 u.2
          ≫ (affineQuotientPullbackIso K L A).hom
        = pullbackBaseChange K L t (T.affineOpenCover.f i ≫ t)
            (T.affineOpenCover.f i) rfl ≫ h := by
    intro i
    letI : Algebra K ↥(T.affineOpenCover.X i) :=
      ((Spec.preimage (T.affineOpenCover.f i ≫ t)).hom).toAlgebra
    have ht : T.affineOpenCover.f i ≫ t
        = Spec.map (CommRingCat.ofHom (algebraMap K ↥(T.affineOpenCover.X i))) := by
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
    -- `@`-application: see `affineQuotient_hom_unique` (instance-diamond dodge)
    exact (@existsUnique_pullbackBaseChange_of_affine K L _ _ _ A _ _ _ _ _ _ _ _
      ↥(T.affineOpenCover.X i) _ this
      (T.affineOpenCover.f i ≫ t) ht
      (pullbackBaseChange K L t (T.affineOpenCover.f i ≫ t) (T.affineOpenCover.f i) rfl
        ≫ h)
      (by
        rw [Category.assoc, hover]
        exact pullbackBaseChange_snd K L t _ (T.affineOpenCover.f i) rfl)
      (SemilinearGalAction.isEquivariant_pullbackBaseChange_comp t _
        (specSemilinearGalAction K L A) hequiv (T.affineOpenCover.f i) rfl)).exists
  choose v hv using hloc
  -- the local solutions agree on overlaps, by the globalized uniqueness
  have hglue : ∀ i j : T.affineOpenCover.I₀,
      pullback.fst (T.affineOpenCover.f i) (T.affineOpenCover.f j) ≫ (v i).1
        = pullback.snd _ _ ≫ (v j).1 := by
    intro i j
    have hsnd : pullback.snd (T.affineOpenCover.f i) (T.affineOpenCover.f j)
          ≫ (T.affineOpenCover.f j ≫ t)
        = pullback.fst (T.affineOpenCover.f i) (T.affineOpenCover.f j)
            ≫ (T.affineOpenCover.f i ≫ t) := by
      rw [← Category.assoc, ← pullback.condition, Category.assoc]
    have hi : pullbackBaseChange K L
          (Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A))))
          (pullback.fst (T.affineOpenCover.f i) (T.affineOpenCover.f j)
            ≫ (T.affineOpenCover.f i ≫ t))
          (pullback.fst _ _ ≫ (v i).1) (by rw [Category.assoc, (v i).2])
        ≫ (affineQuotientPullbackIso K L A).hom
        = pullbackBaseChange K L t _
            (pullback.fst _ _ ≫ T.affineOpenCover.f i) (Category.assoc _ _ _) ≫ h := by
      rw [pullbackBaseChange_comp_assoc K L _ (T.affineOpenCover.f i ≫ t) _ (v i).1
          (v i).2 (pullback.fst _ _) rfl,
        pullbackBaseChange_comp_assoc K L t (T.affineOpenCover.f i ≫ t) _
          (T.affineOpenCover.f i) rfl (pullback.fst _ _) rfl, hv i]
    have hj : pullbackBaseChange K L
          (Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A))))
          (pullback.fst (T.affineOpenCover.f i) (T.affineOpenCover.f j)
            ≫ (T.affineOpenCover.f i ≫ t))
          (pullback.snd _ _ ≫ (v j).1) (by rw [Category.assoc, (v j).2]; exact hsnd)
        ≫ (affineQuotientPullbackIso K L A).hom
        = pullbackBaseChange K L t _
            (pullback.snd _ _ ≫ T.affineOpenCover.f j)
            (by rw [Category.assoc]; exact hsnd) ≫ h := by
      rw [pullbackBaseChange_comp_assoc K L _ (T.affineOpenCover.f j ≫ t) _ (v j).1
          (v j).2 (pullback.snd _ _) hsnd,
        pullbackBaseChange_comp_assoc K L t (T.affineOpenCover.f j ≫ t) _
          (T.affineOpenCover.f j) rfl (pullback.snd _ _) hsnd, hv j]
    have hcongr : pullbackBaseChange K L t
          (pullback.fst (T.affineOpenCover.f i) (T.affineOpenCover.f j)
            ≫ (T.affineOpenCover.f i ≫ t))
          (pullback.fst _ _ ≫ T.affineOpenCover.f i) (Category.assoc _ _ _)
        = pullbackBaseChange K L t _
            (pullback.snd _ _ ≫ T.affineOpenCover.f j)
            (by rw [Category.assoc]; exact hsnd) :=
      pullbackBaseChange_congr K L t _ pullback.condition _
    exact affineQuotient_hom_unique K L A (by rw [Category.assoc, (v i).2])
      (by rw [Category.assoc, (v j).2]; exact hsnd)
      (hi.trans (by rw [hcongr]; exact hj.symm))
  -- glue the local solutions
  set w : T ⟶ Spec (CommRingCat.of (invariantsSubalgebra K L A)) :=
    T.affineOpenCover.openCover.glueMorphisms (fun i => (v i).1) hglue with hw
  have hι : ∀ i, T.affineOpenCover.f i ≫ w = (v i).1 := fun i =>
    T.affineOpenCover.openCover.ι_glueMorphisms (fun i => (v i).1) hglue i
  have hwt : w ≫ Spec.map (CommRingCat.ofHom
      (algebraMap K (invariantsSubalgebra K L A))) = t := by
    apply T.affineOpenCover.openCover.hom_ext
    change ∀ i : T.affineOpenCover.I₀,
      T.affineOpenCover.f i ≫ w ≫ Spec.map (CommRingCat.ofHom
        (algebraMap K (invariantsSubalgebra K L A))) = T.affineOpenCover.f i ≫ t
    intro i
    rw [← Category.assoc, hι i, (v i).2]
  have hmain : pullbackBaseChange K L
      (Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A))))
      t w hwt ≫ (affineQuotientPullbackIso K L A).hom = h := by
    apply (Scheme.Pullback.openCoverOfLeft T.affineOpenCover.openCover t
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).hom_ext
    change ∀ i : T.affineOpenCover.I₀,
      pullbackBaseChange K L t (T.affineOpenCover.f i ≫ t) (T.affineOpenCover.f i) rfl
        ≫ (pullbackBaseChange K L
            (Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A))))
            t w hwt ≫ (affineQuotientPullbackIso K L A).hom)
      = pullbackBaseChange K L t (T.affineOpenCover.f i ≫ t)
          (T.affineOpenCover.f i) rfl ≫ h
    intro i
    rw [← Category.assoc,
      ← pullbackBaseChange_comp K L _ t (T.affineOpenCover.f i ≫ t) w hwt
        (T.affineOpenCover.f i) rfl,
      pullbackBaseChange_congr K L _ (T.affineOpenCover.f i ≫ t) (hι i) _, hv i]
  exact ⟨⟨w, hwt⟩, hmain, fun y hy => Subtype.ext
    (affineQuotient_hom_unique K L A y.2 hwt (hy.trans hmain.symm))⟩

/-- **The affine finite Galois quotient theorem** (campaign `G2`, wave-2 milestone):
for the affine model `specSemilinearGalAction` of a semilinear `Gal(L/K)`-action on
`Spec A`, the canonical morphism `Spec (A^Γ) ⟶ Spec K` is a finite Galois quotient —
the full `IsGaloisQuotient` predicate: the `Γ`-equivariant base-change isomorphism
over `Spec L` (`affineQuotientPullbackIso`, Speiser descent) together with the
universal `T`-points property `Hom_K(T, Spec A^Γ) ≅ Hom_L(T_L, Spec A)^Γ` for
**all** schemes `T` (affine case via `affineGaloisQuotientHomEquiv`, globalized by
gluing along an affine open cover of `T`). -/
theorem isGaloisQuotient_spec :
    IsGaloisQuotient (specSemilinearGalAction K L A)
      (Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A)))) :=
  ⟨affineQuotientPullbackIso K L A, affineQuotientPullbackIso_hom_specMap K L A,
    isEquivariant_affineQuotientPullbackIso_hom K L A,
    affineQuotient_existsUnique K L A⟩

end AffineGaloisQuotient

end AlgebraicJacobian.GaloisDescent
