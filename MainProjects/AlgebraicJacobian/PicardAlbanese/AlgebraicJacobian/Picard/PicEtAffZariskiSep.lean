/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RelPicPi
import AlgebraicJacobian.Picard.PicEtAffMap

/-!
# Zariski separation of the étale plus construction

The affine étale Picard functor `PicEtAff C ·` is a separated presheaf for the Zariski
topology of affine tests: two plus classes over `A` agreeing on every member of a finite
basic-open cover of `Spec A` agree (`AlgebraicGeometry.PicEtAff.eq_of_away_eq`).

Route: the plus construction of *any* presheaf is separated — representatives agreeing
on each localization agree on an étale cover assembled from the local witnessing covers,
and the finite product of the witnessing carriers is again an étale cover of the base.
The gluing across the factors of the product is the relative Picard decomposition of a
finite product of test algebras (`AlgebraicGeometry.relPic.eq_of_pi_proj_eq`,
`AlgebraicJacobian.Picard.RelPicPi`).

The file also provides `AlgebraicGeometry.PicEtAff.exists_relPicAlgMap_eq_of_mapAlg_eq`,
the representative-level unfolding of an equality of restricted plus classes, consumed
by the gluing half (`AlgebraicJacobian.Picard.PicEtAffZariskiGlue`).
-/

set_option autoImplicit false

universe u

open CategoryTheory

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

namespace PicEtAff

/-! ## Unfolding an equality of restricted plus classes -/

/-- Unfolding an equality of restrictions of two plus classes along two algebra maps
into a common test algebra `R`: the descent-class representatives admit refinement maps
into a common étale cover of `R`, semilinear over the restriction maps, with equal
transports of the underlying relative Picard classes. -/
theorem exists_relPicAlgMap_eq_of_mapAlg_eq {A₁ A₂ R : Type u}
    [CommRing A₁] [Algebra k A₁] [CommRing A₂] [Algebra k A₂] [CommRing R] [Algebra k R]
    (φ₁ : A₁ →ₐ[k] R) (φ₂ : A₂ →ₐ[k] R)
    (E₁ : Algebra.EtaleCover A₁) (E₂ : Algebra.EtaleCover A₂)
    (ξ₁ : descentClasses C E₁) (ξ₂ : descentClasses C E₂)
    (h : mapAlg C φ₁ (mk C E₁ ξ₁) = mapAlg C φ₂ (mk C E₂ ξ₂)) :
    ∃ (H : Algebra.EtaleCover R) (m₁ : E₁.Carrier →ₐ[k] H.Carrier)
      (m₂ : E₂.Carrier →ₐ[k] H.Carrier),
      (∀ a : A₁, m₁ (algebraMap A₁ E₁.Carrier a) = algebraMap R H.Carrier (φ₁ a))
        ∧ (∀ a : A₂, m₂ (algebraMap A₂ E₂.Carrier a) = algebraMap R H.Carrier (φ₂ a))
        ∧ relPicAlgMap C m₁ (ξ₁ : relPic C (overSpec k E₁.Carrier))
            = relPicAlgMap C m₂ (ξ₂ : relPic C (overSpec k E₂.Carrier)) := by
  letI : Algebra A₁ R := φ₁.toRingHom.toAlgebra
  haveI : IsScalarTower k A₁ R := .of_algebraMap_eq fun a => (φ₁.commutes a).symm
  letI : Algebra A₂ R := φ₂.toRingHom.toAlgebra
  haveI : IsScalarTower k A₂ R := .of_algebraMap_eq fun a => (φ₂.commutes a).symm
  have h' : PicEtAff.map C R (mk C E₁ ξ₁) = PicEtAff.map C R (mk C E₂ ξ₂) := h
  rw [map_mk, map_mk] at h'
  obtain ⟨H, r₁, r₂, hr⟩ := (mk_eq_mk_iff C).mp h'
  refine ⟨H,
    (r₁.restrictScalars k).comp ((E₁.baseChangeInclude R).restrictScalars k),
    (r₂.restrictScalars k).comp ((E₂.baseChangeInclude R).restrictScalars k),
    ?_, ?_, ?_⟩
  · intro a
    change r₁ (E₁.baseChangeInclude R (algebraMap A₁ E₁.Carrier a)) = _
    rw [AlgHom.commutes (E₁.baseChangeInclude R) a,
      IsScalarTower.algebraMap_apply A₁ R ((E₁.baseChange R).Carrier) a,
      AlgHom.commutes r₁ (algebraMap A₁ R a)]
    rfl
  · intro a
    change r₂ (E₂.baseChangeInclude R (algebraMap A₂ E₂.Carrier a)) = _
    rw [AlgHom.commutes (E₂.baseChangeInclude R) a,
      IsScalarTower.algebraMap_apply A₂ R ((E₂.baseChange R).Carrier) a,
      AlgHom.commutes r₂ (algebraMap A₂ R a)]
    rfl
  · have hval := congrArg Subtype.val hr
    rw [descentMap_coe, descentMap_coe, descentBaseChange_coe, descentBaseChange_coe,
      ← relPicAlgMap_comp, ← relPicAlgMap_comp] at hval
    exact hval

/-! ## Zariski separation -/

variable {A : Type u} [CommRing A] [Algebra k A]
variable {ι : Type u} [Finite ι] (g : ι → A)
variable (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra k (S i)]
  [∀ i, Algebra A (S i)] [∀ i, IsScalarTower k A (S i)]
  [∀ i, IsLocalization.Away (g i) (S i)]

/-- A finite covering family of localizations assembles the local étale covers into an
étale cover of the base: the product of the carriers. -/
theorem exists_etaleCover_pi (hg : Ideal.span (Set.range g) = ⊤)
    (K : ∀ i, Algebra.EtaleCover (S i)) :
    ∃ W : Algebra.EtaleCover A, Nonempty (W.Carrier ≃ₐ[A] Π i, (K i).Carrier) := by
  classical
  haveI : ∀ i, Algebra.Etale A (S i) := fun i =>
    Algebra.Etale.of_isLocalizationAway (g i)
  haveI : ∀ i, Algebra.Etale A (K i).Carrier := fun i =>
    Algebra.Etale.comp A (S i) (K i).Carrier
  haveI : Algebra.Etale A (Π i, (K i).Carrier) := inferInstance
  have hsurj : Function.Surjective
      (PrimeSpectrum.comap (algebraMap A (Π i, (K i).Carrier))) := by
    intro p
    -- some `g i` lies outside `p`
    have hexists : ∃ i, g i ∉ p.asIdeal := by
      by_contra hall
      have hle : Ideal.span (Set.range g) ≤ p.asIdeal := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact of_not_not fun hc => hall ⟨i, hc⟩
      rw [hg] at hle
      exact p.isPrime.ne_top (top_le_iff.mp hle)
    obtain ⟨i, hi⟩ := hexists
    -- lift through the localization and the local cover
    have hploc : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (S i))) := by
      rw [PrimeSpectrum.localization_away_comap_range (S := S i) (g i)]
      exact hi
    obtain ⟨q, hq⟩ := hploc
    obtain ⟨r, hr⟩ := (K i).comap_surjective q
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun j => (K j).Carrier) i) r, ?_⟩
    have hcomp : (Pi.evalRingHom (fun j => (K j).Carrier) i).comp
        (algebraMap A (Π j, (K j).Carrier)) = algebraMap A ((K i).Carrier) := rfl
    rw [← PrimeSpectrum.comap_comp_apply, hcomp,
      IsScalarTower.algebraMap_eq A (S i) ((K i).Carrier),
      PrimeSpectrum.comap_comp_apply, hr, hq]
  exact ⟨Algebra.EtaleCover.of (Π i, (K i).Carrier) hsurj,
    ⟨Algebra.EtaleCover.ofEquiv (Π i, (K i).Carrier) hsurj⟩⟩

/-- **Zariski separation of the étale plus construction**: two plus classes over `A`
agreeing on every member of a finite covering family of localizations agree. -/
theorem eq_of_away_eq (hg : Ideal.span (Set.range g) = ⊤) {x y : PicEtAff C A}
    (h : ∀ i, PicEtAff.mapAlg C (IsScalarTower.toAlgHom k A (S i)) x
      = PicEtAff.mapAlg C (IsScalarTower.toAlgHom k A (S i)) y) :
    x = y := by
  classical
  -- reduce to triviality of the ratio
  suffices hone : ∀ z : PicEtAff C A,
      (∀ i, PicEtAff.mapAlg C (IsScalarTower.toAlgHom k A (S i)) z = 1) → z = 1 by
    have hxy := hone (x * y⁻¹) fun i => by
      rw [map_mul, map_inv, h i, mul_inv_cancel]
    exact mul_inv_eq_one.mp hxy
  intro z hz
  induction z using PicEtAff.ind with | _ G ζ =>
  -- unfold each local triviality to a refinement witness
  have hloc : ∀ i, ∃ (K : Algebra.EtaleCover (S i)) (m : G.Carrier →ₐ[k] K.Carrier),
      (∀ a : A, m (algebraMap A G.Carrier a)
        = algebraMap (S i) K.Carrier (algebraMap A (S i) a))
      ∧ relPicAlgMap C m (ζ : relPic C (overSpec k G.Carrier)) = 1 := by
    intro i
    have hi : mapAlg C (IsScalarTower.toAlgHom k A (S i)) (mk C G ζ)
        = mapAlg C (IsScalarTower.toAlgHom k A (S i))
            (mk C (.self A) (1 : descentClasses C (.self A))) := by
      rw [hz i, PicEtAff.mk_one C (.self A), map_one]
    obtain ⟨K, m₁, m₂, hm₁, hm₂, hval⟩ := exists_relPicAlgMap_eq_of_mapAlg_eq C
      (IsScalarTower.toAlgHom k A (S i)) (IsScalarTower.toAlgHom k A (S i))
      G (.self A) ζ 1 hi
    refine ⟨K, m₁, fun a => ?_, ?_⟩
    · exact hm₁ a
    · rw [hval, show ((1 : descentClasses C (.self A)) :
        relPic C (overSpec k (Algebra.EtaleCover.self A).Carrier)) = 1 from rfl,
        map_one]
  choose K m hmcomm hmone using hloc
  -- assemble the product cover
  obtain ⟨W, ⟨e⟩⟩ := exists_etaleCover_pi g S hg K
  -- the joint refinement map
  have hmA : ∀ i, ∀ a : A, m i (algebraMap A G.Carrier a)
      = algebraMap A ((K i).Carrier) a := by
    intro i a
    rw [hmcomm i a, ← IsScalarTower.algebraMap_apply A (S i) ((K i).Carrier) a]
  -- the underlying relative Picard class dies on the product
  have hpi : relPicAlgMap C
      (Pi.algHom k (fun j => (K j).Carrier) (fun j => m j))
      (ζ : relPic C (overSpec k G.Carrier)) = 1 := by
    refine relPic.eq_of_pi_proj_eq C (fun j => (K j).Carrier) (fun i => ?_)
    rw [← relPicAlgMap_comp, map_one,
      show (Pi.evalAlgHom k (fun j => (K j).Carrier) i).comp
          (Pi.algHom k (fun j => (K j).Carrier) (fun j => m j))
        = m i from AlgHom.ext fun _ => rfl]
    exact hmone i
  -- transport through the carrier identification
  have hW : relPicAlgMap C
      ((e.symm.toAlgHom.restrictScalars k).comp
        (Pi.algHom k (fun j => (K j).Carrier) (fun j => m j)))
      (ζ : relPic C (overSpec k G.Carrier)) = 1 := by
    rw [relPicAlgMap_comp, hpi, map_one]
  -- the joint refinement map is an `A`-algebra map
  have hcommA : ∀ a : A,
      ((e.symm.toAlgHom.restrictScalars k).comp
        (Pi.algHom k (fun j => (K j).Carrier) (fun j => m j)))
        (algebraMap A G.Carrier a) = algebraMap A W.Carrier a := by
    intro a
    have h1 : (Pi.algHom k (fun j => (K j).Carrier) (fun j => m j))
        (algebraMap A G.Carrier a) = algebraMap A (Π j, (K j).Carrier) a := by
      ext j
      exact hmA j a
    change e.symm ((Pi.algHom k (fun j => (K j).Carrier) (fun j => m j))
      (algebraMap A G.Carrier a)) = _
    rw [h1]
    exact e.symm.commutes a
  set nA : G.Carrier →ₐ[A] W.Carrier :=
    { toRingHom := ((e.symm.toAlgHom.restrictScalars k).comp
        (Pi.algHom k (fun j => (K j).Carrier) (fun j => m j))).toRingHom
      commutes' := hcommA } with hnA
  have hval : descentMap C nA ζ = 1 := by
    refine Subtype.ext ?_
    rw [descentMap_coe,
      show nA.restrictScalars k
        = (e.symm.toAlgHom.restrictScalars k).comp
            (Pi.algHom k (fun j => (K j).Carrier) (fun j => m j)) from
        AlgHom.ext fun _ => rfl]
    exact hW
  calc mk C G ζ = mk C W (descentMap C nA ζ) := (mk_descentMap C nA ζ).symm
    _ = mk C W 1 := by rw [hval]
    _ = 1 := mk_one C W

end PicEtAff

end AlgebraicGeometry
