/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.Basic

/-!
# Global sections of a proper geometrically integral scheme over a field

The keystone of the curve substrate: for a scheme `X` proper and geometrically integral over a
field `K`, the structure map induces an isomorphism `K ≅ Γ(X, 𝒪_X)`.

* `AlgebraicGeometry.bijective_appTop_of_isProper_of_geometricallyIntegral`:
  the honest general form — `f.appTop : Γ(Spec K, ⊤) ⟶ Γ(X, ⊤)` is bijective.
* `AlgebraicGeometry.isIso_appTop_of_isProper_of_geometricallyIntegral` and the bundle instance
  `AlgebraicGeometry.isIso_hom_appTop_of_geometricallyReduced`: the instance-friendly forms.

## Proof sketch

Write `A := Γ(X, ⊤)`. By Mathlib's properness facts (`isField_of_universallyClosed`,
`finite_appTop_of_universallyClosed`), `A` is a field, finite over `K`. Base change `f` along
`Spec A ⟶ Spec K`: the total space `X_A` is again proper and geometrically integral over the
field `A`, so `Γ(X_A, ⊤)` is a field as well. Flat base change of sections
(`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`) exhibits `Γ(X_A, ⊤)` as the pushout
`A ⊗[K] A`. A pushout of a field extension along itself being a field forces `K ⟶ A` to be an
*epimorphism* of rings (`CommRingCat.epi_of_isPushout_of_isField`: the codiagonal
`A ⊗[K] A ⟶ A` is injective, being a ring map out of a field, and surjective, being split by
`inl`; hence `inl` is an isomorphism and the two coprojections agree). A finite ring
epimorphism is surjective (`RingHom.surjective_of_epi_of_finite`), and any ring map out of a
field is injective.

Geometric reducedness enters only through `GeometricallyIntegral`; for the curve bundle of the
challenge it is supplied by "smooth ⟹ geometrically reduced", proved elsewhere in this project.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace CommRingCat

/-- If a pushout square of commutative rings has isomorphic legs (`e : C ≅ B` intertwining
`ψ` and `φ`) and its pushout `D` is a field, then `φ` is an epimorphism.

This is the classical "diagonal" criterion: the codiagonal `μ : D ⟶ B` determined by
`𝟙 B` and `e.hom` is injective (a ring map out of a field into a nontrivial ring) and split
surjective, hence an isomorphism; so `inl = e.inv ≫ inr`, which makes `φ` epi. -/
lemma epi_of_isPushout_of_isField {A B C D : CommRingCat.{u}}
    {φ : A ⟶ B} {ψ : A ⟶ C} {inl : B ⟶ D} {inr : C ⟶ D}
    (H : IsPushout φ ψ inl inr) (hD : IsField D) [Nontrivial B]
    (e : C ≅ B) (he : ψ ≫ e.hom = φ) : Epi φ := by
  letI : Field D := hD.toField
  -- the codiagonal
  let μ : D ⟶ B := H.desc (𝟙 B) e.hom (by rw [Category.comp_id, he])
  have hμinl : inl ≫ μ = 𝟙 B := H.inl_desc _ _ _
  have hμinr : inr ≫ μ = e.hom := H.inr_desc _ _ _
  have : IsIso μ := by
    refine (ConcreteCategory.isIso_iff_bijective μ).mpr ⟨μ.hom.injective, fun b ↦ ⟨inl b, ?_⟩⟩
    simpa using congr($(hμinl) b)
  -- the two coprojections agree up to `e`
  have key : e.inv ≫ inr = inl := by
    rw [← cancel_mono μ, Category.assoc, hμinr, hμinl, Iso.inv_hom_id]
  refine ⟨fun {W} u v huv ↦ ?_⟩
  have w : φ ≫ u = ψ ≫ (e.hom ≫ v) := by
    rw [← Category.assoc, he]; exact huv
  calc u = inl ≫ H.desc u (e.hom ≫ v) w := (H.inl_desc _ _ _).symm
    _ = e.inv ≫ inr ≫ H.desc u (e.hom ≫ v) w := by rw [← Category.assoc, key]
    _ = e.inv ≫ e.hom ≫ v := by rw [H.inr_desc]
    _ = v := by rw [Iso.inv_hom_id_assoc]

end CommRingCat

namespace AlgebraicGeometry

/-- Bundled variant of `AlgebraicGeometry.isField_of_universallyClosed`: if `X` is an integral
scheme, universally closed over the spectrum of a (bundled) commutative ring `R` that is a
field, then `Γ(X, ⊤)` is a field. -/
theorem isField_of_universallyClosed_of_isField {R : CommRingCat.{u}} (hR : IsField R)
    {X : Scheme.{u}} (f : X ⟶ Spec R) [IsIntegral X] [UniversallyClosed f] :
    IsField Γ(X, ⊤) := by
  let F := (Scheme.ΓSpecIso R).inv ≫ f.appTop
  have : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  algebraize [F.hom]
  exact isField_of_isIntegral_of_isField' hR

/-- **Global sections of a proper geometrically integral scheme over a field.**
If `X` is proper and geometrically integral over a field `K`, then the map on global sections
`Γ(Spec K, ⊤) ⟶ Γ(X, ⊤)` induced by the structure morphism is bijective; informally,
`Γ(X, 𝒪_X) = K`. -/
theorem bijective_appTop_of_isProper_of_geometricallyIntegral
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [GeometricallyIntegral f] :
    Function.Bijective f.appTop := by
  have hX : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  -- `A := Γ(X, ⊤)` is a field, finite over `K`.
  have hA : IsField Γ(X, ⊤) := isField_of_universallyClosed K f
  letI : Field Γ(X, ⊤) := hA.toField
  letI : Field Γ(Spec (CommRingCat.of K), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  refine ⟨f.appTop.hom.injective, ?_⟩
  -- Surjectivity: `f.appTop` is a finite epimorphism.
  suffices h : Epi f.appTop from
    RingHom.surjective_of_epi_of_finite f.appTop (finite_appTop_of_universallyClosed K f)
  -- Base change to `Spec Γ(X, ⊤)`.
  set q : Spec Γ(X, ⊤) ⟶ Spec (CommRingCat.of K) :=
    Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop) with hq
  -- The total space of the base change is integral, so its global sections form a field.
  have hsub : Subsingleton ↥(Spec Γ(X, ⊤)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Γ(X, ⊤)))
  have hYint : IsIntegral (pullback f q) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.snd f q)
  have hUC : UniversallyClosed (pullback.snd f q) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have hD : IsField Γ(pullback f q, ⊤) :=
    isField_of_universallyClosed_of_isField hA (pullback.snd f q)
  -- Flat base change of global sections: the pushout square.
  have hUST : (⊤ : (Spec Γ(X, ⊤)).Opens) ≤ q ⁻¹ᵁ ⊤ := (Scheme.Hom.preimage_top q).ge
  have hUSX : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ := (Scheme.Hom.preimage_top f).ge
  have hUY : (⊤ : (pullback f q).Opens) =
      pullback.fst f q ⁻¹ᵁ ⊤ ⊓ pullback.snd f q ⁻¹ᵁ ⊤ := by simp
  have hCS : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hQS : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback f q) hUST hUSX hUY
    (isAffineOpen_top _) (isAffineOpen_top _)
    (by simpa using CompactSpace.isCompact_univ)
    (by simpa using isQuasiSeparated_univ)
  have hpo := (isIso_pushoutSection_iff
    (IsPullback.of_hasPullback f q) hUST hUSX hUY).mp hiso
  -- The two legs of the pushout square agree up to `ΓSpecIso`.
  have hcompat : q.appLE ⊤ ⊤ hUST ≫ (Scheme.ΓSpecIso Γ(X, ⊤)).hom = f.appLE ⊤ ⊤ hUSX := by
    have h₁ : q.appLE ⊤ ⊤ hUST = q.appTop := Scheme.Hom.appLE_eq_app q
    have h₂ : f.appLE ⊤ ⊤ hUSX = f.appTop := Scheme.Hom.appLE_eq_app f
    rw [h₁, h₂, hq, Scheme.ΓSpecIso_naturality, Iso.hom_inv_id_assoc]
  have hepi : Epi (f.appLE ⊤ ⊤ hUSX) :=
    CommRingCat.epi_of_isPushout_of_isField hpo hD (Scheme.ΓSpecIso Γ(X, ⊤)) hcompat
  rwa [show f.appLE ⊤ ⊤ hUSX = f.appTop from Scheme.Hom.appLE_eq_app f] at hepi

/-- Instance-friendly form of
`AlgebraicGeometry.bijective_appTop_of_isProper_of_geometricallyIntegral`. -/
theorem isIso_appTop_of_isProper_of_geometricallyIntegral
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [GeometricallyIntegral f] :
    IsIso f.appTop :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (bijective_appTop_of_isProper_of_geometricallyIntegral f)

variable {k : Type u} [Field k]

/-- `Γ(C, 𝒪_C) ≅ k` for the curve bundle: the structure morphism of a proper, geometrically
irreducible, geometrically reduced scheme over `k` induces an isomorphism on global sections.

Geometric reducedness is a hypothesis here; for the curve bundle of the challenge it is
supplied by "smooth ⟹ geometrically reduced", proved elsewhere in this project. -/
instance isIso_hom_appTop_of_geometricallyReduced (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom] :
    IsIso C.hom.appTop :=
  have : GeometricallyIntegral C.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible C.hom
  isIso_appTop_of_isProper_of_geometricallyIntegral (K := k) C.hom

section RegressionChecks

variable {C : Over (Spec (CommRingCat.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
  [GeometricallyReduced C.hom]

-- The composite `k ≅ Γ(Spec k, ⊤) ≅ Γ(C, 𝒪_C)` is available to downstream waves.
noncomputable example : CommRingCat.of k ≅ Γ(C.left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).symm ≪≫ asIso C.hom.appTop

end RegressionChecks

end AlgebraicGeometry
