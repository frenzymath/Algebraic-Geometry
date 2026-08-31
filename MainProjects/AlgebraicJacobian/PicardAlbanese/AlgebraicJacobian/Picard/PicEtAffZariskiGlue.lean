/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtAffZariskiSep
import AlgebraicJacobian.Picard.RelPicCoverInjective
import AlgebraicJacobian.Algebra.TensorAwayPi

/-!
# Zariski gluing of the étale plus construction

The gluing half of the Zariski sheaf property of the affine étale Picard functor: a
family of plus classes on a finite basic-open cover of `Spec A`, compatible on the
pairwise overlaps, glues to a plus class on `A`
(`AlgebraicGeometry.PicEtAff.exists_mapAlg_eq_of_compat`).

The engine is the **pair condition** (`PicEtAff.relPicAlgMap_tensor_eq_of_compat`): for
descent-class representatives `ξ₁, ξ₂` of two compatible classes over localizations
`S₁, S₂` of `A`, the two pullbacks to the `A`-tensor product of the covering carriers
agree.  The overlap compatibility supplies a common refinement over the overlap
localization; base-changing it to the tensor product and transporting through
`AlgebraicGeometry.relPicAlgMap_congr` (the two routes into the base change are
semilinear over the *same* localization, and `A`-algebra maps out of a localization are
unique) reduces the claim to injectivity of relative Picard restriction along an étale
cover — the (C1) corollary
(`AlgebraicGeometry.relPicAlgMap_injective_of_etaleCover`).  This is the single point
where the Layer-2 functoriality consumes étale separatedness.

The glued class is then assembled through the relative Picard decomposition of finite
products (`AlgebraicGeometry.relPic.exists_pi_lift`, `relPic.eq_of_pi_proj_eq`) and the
pi-decomposition of the tensor square (`Algebra.TensorProduct.piDoubleEquivA`).
-/

set_option autoImplicit false

universe u

open CategoryTheory

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

namespace PicEtAff

section PairCondition

variable {A : Type u} [CommRing A] [Algebra k A]
variable {S₁ S₂ Tv : Type u} [CommRing S₁] [CommRing S₂] [CommRing Tv]
  [Algebra k S₁] [Algebra k S₂] [Algebra k Tv]
  [Algebra A S₁] [Algebra A S₂] [Algebra A Tv]
  [IsScalarTower k A S₁] [IsScalarTower k A S₂] [IsScalarTower k A Tv]
variable (φ₁ : S₁ →ₐ[A] Tv) (φ₂ : S₂ →ₐ[A] Tv)
variable (E₁ : Algebra.EtaleCover S₁) (E₂ : Algebra.EtaleCover S₂)

set_option maxHeartbeats 3200000 in
-- The instance towers over the tensor product of the covering carriers exceed the
-- default unification budget.
/-- **The pair condition**: descent-class representatives of two plus classes over the
localizations `S₁, S₂` of `A` that agree over an overlap localization `Tv` have equal
pullbacks to the `A`-tensor product of the covering carriers.  This is the step of the
Layer-2 gluing licensed by the (C1) étale separatedness. -/
theorem relPicAlgMap_tensor_eq_of_compat (g₁ g₂ : A)
    [IsLocalization.Away g₁ S₁] [IsLocalization.Away g₂ S₂]
    [IsLocalization.Away (g₁ * g₂) Tv]
    (ξ₁ : descentClasses C E₁) (ξ₂ : descentClasses C E₂)
    (h : PicEtAff.mapAlg C (φ₁.restrictScalars k) (PicEtAff.mk C E₁ ξ₁)
      = PicEtAff.mapAlg C (φ₂.restrictScalars k) (PicEtAff.mk C E₂ ξ₂)) :
    relPicAlgMap C ((Algebra.TensorProduct.includeLeft :
        E₁.Carrier →ₐ[k] E₁.Carrier ⊗[A] E₂.Carrier))
      (ξ₁ : relPic C (overSpec k E₁.Carrier))
      = relPicAlgMap C ((Algebra.TensorProduct.includeRight :
          E₂.Carrier →ₐ[A] E₁.Carrier ⊗[A] E₂.Carrier).restrictScalars k)
        (ξ₂ : relPic C (overSpec k E₂.Carrier)) := by
  classical
  -- unfold the overlap compatibility to a common refinement over `Tv`
  obtain ⟨H, m₁, m₂, hm₁, hm₂, hval⟩ := exists_relPicAlgMap_eq_of_mapAlg_eq C
    (φ₁.restrictScalars k) (φ₂.restrictScalars k) E₁ E₂ ξ₁ ξ₂ h
  -- `a ⊗ 1 = 1 ⊗ a` for scalars from the base
  have htensor : ∀ a : A,
      (algebraMap A E₁.Carrier a) ⊗ₜ[A] (1 : E₂.Carrier)
        = (1 : E₁.Carrier) ⊗ₜ[A] (algebraMap A E₂.Carrier a) := fun a => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  -- `g₁ * g₂` becomes a unit in `(E₁.Carrier ⊗[A] E₂.Carrier)`
  have hu : IsUnit (algebraMap A (E₁.Carrier ⊗[A] E₂.Carrier) (g₁ * g₂)) := by
    rw [map_mul]
    refine IsUnit.mul ?_ ?_
    · have h₁ : IsUnit (algebraMap A E₁.Carrier g₁) := by
        rw [IsScalarTower.algebraMap_apply A S₁ E₁.Carrier g₁]
        exact (IsLocalization.Away.algebraMap_isUnit (S := S₁) g₁).map
          (algebraMap S₁ E₁.Carrier)
      have h₂ := h₁.map (Algebra.TensorProduct.includeLeft
        (R := A) (S := A) (B := E₂.Carrier))
      rwa [show (Algebra.TensorProduct.includeLeft (R := A) (S := A)
          (B := E₂.Carrier)) (algebraMap A E₁.Carrier g₁)
          = algebraMap A (E₁.Carrier ⊗[A] E₂.Carrier) g₁ from
        ((Algebra.TensorProduct.includeLeft (R := A) (S := A)
          (B := E₂.Carrier)).commutes g₁)] at h₂
    · have h₁ : IsUnit (algebraMap A E₂.Carrier g₂) := by
        rw [IsScalarTower.algebraMap_apply A S₂ E₂.Carrier g₂]
        exact (IsLocalization.Away.algebraMap_isUnit (S := S₂) g₂).map
          (algebraMap S₂ E₂.Carrier)
      have h₂ := h₁.map (Algebra.TensorProduct.includeRight
        (R := A) (A := E₁.Carrier))
      rwa [show (Algebra.TensorProduct.includeRight (R := A) (A := E₁.Carrier))
          (algebraMap A E₂.Carrier g₂)
          = algebraMap A (E₁.Carrier ⊗[A] E₂.Carrier) g₂ from
        ((Algebra.TensorProduct.includeRight (R := A)
          (A := E₁.Carrier)).commutes g₂)] at h₂
  -- the induced `A`-algebra map from the overlap localization into `(E₁.Carrier ⊗[A] E₂.Carrier)`
  set ρ : Tv →ₐ[A] (E₁.Carrier ⊗[A] E₂.Carrier) :=
    IsLocalization.liftAlgHom (M := Submonoid.powers (g₁ * g₂))
    (f := Algebra.ofId A (E₁.Carrier ⊗[A] E₂.Carrier)) (fun y => by
      obtain ⟨n, hn⟩ := y.2
      simpa [Algebra.ofId_apply, ← hn, map_pow] using hu.pow n) with hρdef
  letI : Algebra Tv (E₁.Carrier ⊗[A] E₂.Carrier) := ρ.toRingHom.toAlgebra
  haveI : IsScalarTower A Tv (E₁.Carrier ⊗[A] E₂.Carrier) :=
    .of_algebraMap_eq fun a => (ρ.commutes a).symm
  haveI : IsScalarTower k Tv (E₁.Carrier ⊗[A] E₂.Carrier) := .of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k A (E₁.Carrier ⊗[A] E₂.Carrier) c,
      IsScalarTower.algebraMap_apply k A Tv c]
    exact (ρ.commutes (algebraMap k A c)).symm
  -- the base change of the common refinement to `(E₁.Carrier ⊗[A] E₂.Carrier)`
  set W := H.baseChange (E₁.Carrier ⊗[A] E₂.Carrier) with hWdef
  set θ : H.Carrier →ₐ[Tv] W.Carrier :=
    H.baseChangeInclude (E₁.Carrier ⊗[A] E₂.Carrier) with hθdef
  -- the (C1) corollary: restriction along `(E₁.Carrier ⊗[A] E₂.Carrier) → W.Carrier` is injective
  apply relPicAlgMap_injective_of_etaleCover C W
  rw [← relPicAlgMap_comp, ← relPicAlgMap_comp]
  -- the two `S`-semilinear routes into `W.Carrier`
  -- left: through the tensor product
  haveI hsub₁ : Subsingleton (S₁ →ₐ[A] (E₁.Carrier ⊗[A] E₂.Carrier)) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers g₁)
  haveI hsub₂ : Subsingleton (S₂ →ₐ[A] (E₁.Carrier ⊗[A] E₂.Carrier)) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers g₂)
  haveI : SMulCommClass A S₁ E₁.Carrier :=
    ⟨fun a s b => by simp only [Algebra.smul_def]; ring⟩
  haveI : IsScalarTower A S₁ (E₁.Carrier ⊗[A] E₂.Carrier) :=
    .of_algebraMap_eq fun a => by
      simp only [Algebra.TensorProduct.algebraMap_apply]
      rw [← IsScalarTower.algebraMap_apply A S₁ E₁.Carrier a]
  letI : Algebra S₂ (E₁.Carrier ⊗[A] E₂.Carrier) :=
    ((Algebra.TensorProduct.includeRight :
      E₂.Carrier →ₐ[A] (E₁.Carrier ⊗[A] E₂.Carrier)).toRingHom.comp
        (algebraMap S₂ E₂.Carrier)).toAlgebra
  haveI : IsScalarTower k S₂ (E₁.Carrier ⊗[A] E₂.Carrier) := .of_algebraMap_eq fun c => by
    change algebraMap k (E₁.Carrier ⊗[A] E₂.Carrier) c = Algebra.TensorProduct.includeRight
      (algebraMap S₂ E₂.Carrier (algebraMap k S₂ c))
    rw [← IsScalarTower.algebraMap_apply k S₂ E₂.Carrier c,
      IsScalarTower.algebraMap_apply k A E₂.Carrier c,
      show (Algebra.TensorProduct.includeRight :
          E₂.Carrier →ₐ[A] (E₁.Carrier ⊗[A] E₂.Carrier))
          (algebraMap A E₂.Carrier (algebraMap k A c))
        = algebraMap A (E₁.Carrier ⊗[A] E₂.Carrier) (algebraMap k A c) from
        Algebra.TensorProduct.includeRight.commutes (algebraMap k A c),
      ← IsScalarTower.algebraMap_apply k A (E₁.Carrier ⊗[A] E₂.Carrier) c]
  haveI : IsScalarTower A S₂ (E₁.Carrier ⊗[A] E₂.Carrier) := .of_algebraMap_eq fun a => by
    change algebraMap A (E₁.Carrier ⊗[A] E₂.Carrier) a = Algebra.TensorProduct.includeRight
      (algebraMap S₂ E₂.Carrier (algebraMap A S₂ a))
    rw [← IsScalarTower.algebraMap_apply A S₂ E₂.Carrier a,
      show (Algebra.TensorProduct.includeRight :
          E₂.Carrier →ₐ[A] (E₁.Carrier ⊗[A] E₂.Carrier)) (algebraMap A E₂.Carrier a)
        = algebraMap A (E₁.Carrier ⊗[A] E₂.Carrier) a from
        Algebra.TensorProduct.includeRight.commutes a]
  -- towers into `W.Carrier` (the canonical instance chains through `(E₁.Carrier ⊗[A] E₂.Carrier)`)
  haveI : IsScalarTower k S₁ (E₁.Carrier ⊗[A] E₂.Carrier) := .of_algebraMap_eq fun c => by
    simp only [Algebra.TensorProduct.algebraMap_apply]
    rw [← IsScalarTower.algebraMap_apply k S₁ E₁.Carrier c]
  haveI : IsScalarTower k S₁ W.Carrier := .of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k (E₁.Carrier ⊗[A] E₂.Carrier) W.Carrier c,
      IsScalarTower.algebraMap_apply k S₁ (E₁.Carrier ⊗[A] E₂.Carrier) c,
      ← IsScalarTower.algebraMap_apply S₁ (E₁.Carrier ⊗[A] E₂.Carrier) W.Carrier
        (algebraMap k S₁ c)]
  haveI : IsScalarTower k S₂ W.Carrier := .of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k (E₁.Carrier ⊗[A] E₂.Carrier) W.Carrier c,
      IsScalarTower.algebraMap_apply k S₂ (E₁.Carrier ⊗[A] E₂.Carrier) c,
      ← IsScalarTower.algebraMap_apply S₂ (E₁.Carrier ⊗[A] E₂.Carrier) W.Carrier
        (algebraMap k S₂ c)]
  -- the two `S₁`-algebra maps out of `E₁.Carrier`
  have hkey₁ : ρ.comp φ₁ = IsScalarTower.toAlgHom A S₁ (E₁.Carrier ⊗[A] E₂.Carrier) :=
    Subsingleton.elim _ _
  have hkey₂ : ρ.comp φ₂ = IsScalarTower.toAlgHom A S₂ (E₁.Carrier ⊗[A] E₂.Carrier) :=
    Subsingleton.elim _ _
  set j₁L : E₁.Carrier →ₐ[S₁] W.Carrier :=
    ((Algebra.ofId (E₁.Carrier ⊗[A] E₂.Carrier) W.Carrier).restrictScalars S₁).comp
      (Algebra.TensorProduct.includeLeft (S := S₁)) with hj₁L
  set j₂L : E₁.Carrier →ₐ[S₁] W.Carrier :=
    { toRingHom := ((θ.restrictScalars k).comp m₁).toRingHom
      commutes' := fun s => by
        change θ (m₁ (algebraMap S₁ E₁.Carrier s)) = _
        rw [hm₁ s]
        change θ (algebraMap Tv H.Carrier (φ₁ s)) = _
        rw [θ.commutes (φ₁ s),
          IsScalarTower.algebraMap_apply Tv (E₁.Carrier ⊗[A] E₂.Carrier) W.Carrier (φ₁ s),
          show algebraMap Tv (E₁.Carrier ⊗[A] E₂.Carrier) (φ₁ s) = (ρ.comp φ₁) s from rfl, hkey₁,
          show (IsScalarTower.toAlgHom A S₁ (E₁.Carrier ⊗[A] E₂.Carrier)) s
            = algebraMap S₁ (E₁.Carrier ⊗[A] E₂.Carrier) s from rfl,
          ← IsScalarTower.algebraMap_apply S₁ (E₁.Carrier ⊗[A] E₂.Carrier) W.Carrier s] } with hj₂L
  have hcongr₁ := relPicAlgMap_congr C j₁L j₂L ξ₁.2
  -- the two `S₂`-algebra maps out of `E₂.Carrier`
  set inclR : E₂.Carrier →ₐ[S₂] (E₁.Carrier ⊗[A] E₂.Carrier) :=
    { toRingHom := (Algebra.TensorProduct.includeRight :
        E₂.Carrier →ₐ[A] (E₁.Carrier ⊗[A] E₂.Carrier)).toRingHom
      commutes' := fun s => rfl } with hinclR
  set j₁R : E₂.Carrier →ₐ[S₂] W.Carrier :=
    ((Algebra.ofId (E₁.Carrier ⊗[A] E₂.Carrier) W.Carrier).restrictScalars S₂).comp inclR with hj₁R
  set j₂R : E₂.Carrier →ₐ[S₂] W.Carrier :=
    { toRingHom := ((θ.restrictScalars k).comp m₂).toRingHom
      commutes' := fun s => by
        change θ (m₂ (algebraMap S₂ E₂.Carrier s)) = _
        rw [hm₂ s]
        change θ (algebraMap Tv H.Carrier (φ₂ s)) = _
        rw [θ.commutes (φ₂ s),
          IsScalarTower.algebraMap_apply Tv (E₁.Carrier ⊗[A] E₂.Carrier) W.Carrier (φ₂ s),
          show algebraMap Tv (E₁.Carrier ⊗[A] E₂.Carrier) (φ₂ s) = (ρ.comp φ₂) s from rfl, hkey₂,
          show (IsScalarTower.toAlgHom A S₂ (E₁.Carrier ⊗[A] E₂.Carrier)) s
            = algebraMap S₂ (E₁.Carrier ⊗[A] E₂.Carrier) s from rfl,
          ← IsScalarTower.algebraMap_apply S₂ (E₁.Carrier ⊗[A] E₂.Carrier) W.Carrier s] } with hj₂R
  have hcongr₂ := relPicAlgMap_congr C j₁R j₂R ξ₂.2
  -- assemble the chain
  have hL : (j₁L.restrictScalars k : E₁.Carrier →ₐ[k] W.Carrier)
      = ((Algebra.ofId (E₁.Carrier ⊗[A] E₂.Carrier) W.Carrier).restrictScalars k).comp
          (Algebra.TensorProduct.includeLeft :
            E₁.Carrier →ₐ[k] E₁.Carrier ⊗[A] E₂.Carrier) :=
    AlgHom.ext fun _ => rfl
  have hR : (j₁R.restrictScalars k : E₂.Carrier →ₐ[k] W.Carrier)
      = ((Algebra.ofId (E₁.Carrier ⊗[A] E₂.Carrier) W.Carrier).restrictScalars k).comp
          ((Algebra.TensorProduct.includeRight :
            E₂.Carrier →ₐ[A] (E₁.Carrier ⊗[A] E₂.Carrier)).restrictScalars k) :=
    AlgHom.ext fun _ => rfl
  have hML : (j₂L.restrictScalars k : E₁.Carrier →ₐ[k] W.Carrier)
      = (θ.restrictScalars k).comp m₁ := AlgHom.ext fun _ => rfl
  have hMR : (j₂R.restrictScalars k : E₂.Carrier →ₐ[k] W.Carrier)
      = (θ.restrictScalars k).comp m₂ := AlgHom.ext fun _ => rfl
  rw [hL] at hcongr₁
  rw [hR] at hcongr₂
  rw [hML] at hcongr₁
  rw [hMR] at hcongr₂
  calc relPicAlgMap C
        (((Algebra.ofId (E₁.Carrier ⊗[A] E₂.Carrier) W.Carrier).restrictScalars k).comp
        (Algebra.TensorProduct.includeLeft :
          E₁.Carrier →ₐ[k] E₁.Carrier ⊗[A] E₂.Carrier))
        (ξ₁ : relPic C (overSpec k E₁.Carrier))
      = relPicAlgMap C ((θ.restrictScalars k).comp m₁)
          (ξ₁ : relPic C (overSpec k E₁.Carrier)) := hcongr₁
    _ = relPicAlgMap C (θ.restrictScalars k)
          (relPicAlgMap C m₁ (ξ₁ : relPic C (overSpec k E₁.Carrier))) :=
        relPicAlgMap_comp C _ _ _
    _ = relPicAlgMap C (θ.restrictScalars k)
          (relPicAlgMap C m₂ (ξ₂ : relPic C (overSpec k E₂.Carrier))) := by rw [hval]
    _ = relPicAlgMap C ((θ.restrictScalars k).comp m₂)
          (ξ₂ : relPic C (overSpec k E₂.Carrier)) := (relPicAlgMap_comp C _ _ _).symm
    _ = relPicAlgMap C
          (((Algebra.ofId (E₁.Carrier ⊗[A] E₂.Carrier) W.Carrier).restrictScalars k).comp
          ((Algebra.TensorProduct.includeRight :
            E₂.Carrier →ₐ[A] (E₁.Carrier ⊗[A] E₂.Carrier)).restrictScalars k))
          (ξ₂ : relPic C (overSpec k E₂.Carrier)) := hcongr₂.symm

end PairCondition

/-! ## Assembly of the glued class -/

section GlueHelpers

omit [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

/-- Restriction of relative Picard classes along a `k`-algebra isomorphism is
injective. -/
theorem relPicAlgMap_algEquiv_injective {A B : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (e : A ≃ₐ[k] B) :
    Function.Injective (relPicAlgMap C e.toAlgHom) := by
  intro u v huv
  have h2 := congrArg (relPicAlgMap C e.symm.toAlgHom) huv
  rw [← relPicAlgMap_comp, ← relPicAlgMap_comp,
    show e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id k A from
      AlgHom.ext fun a => e.symm_apply_apply a] at h2
  rwa [relPicAlgMap_id, relPicAlgMap_id] at h2

/-- Sufficient criterion for computing a restricted plus class on a given cover: a
refinement map semilinear over the restriction carrying the representative onto the
target representative. -/
theorem mapAlg_mk_eq_mk {A₁ R : Type u} [CommRing A₁] [Algebra k A₁] [CommRing R]
    [Algebra k R] (φ : A₁ →ₐ[k] R) (E₁ : Algebra.EtaleCover A₁)
    (F : Algebra.EtaleCover R) (ξ : descentClasses C E₁) (η : descentClasses C F)
    (n : E₁.Carrier →ₐ[k] F.Carrier)
    (hsemi : ∀ a : A₁, n (algebraMap A₁ E₁.Carrier a) = algebraMap R F.Carrier (φ a))
    (hcls : relPicAlgMap C n (ξ : relPic C (overSpec k E₁.Carrier))
      = (η : relPic C (overSpec k F.Carrier))) :
    mapAlg C φ (mk C E₁ ξ) = mk C F η := by
  letI : Algebra A₁ R := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A₁ R := .of_algebraMap_eq fun a => (φ.commutes a).symm
  have hstep : PicEtAff.map C R (mk C E₁ ξ) = mk C F η := by
    rw [map_mk]
    -- the `R`-algebra extension of `n` to the base change
    set nA : E₁.Carrier →ₐ[A₁] F.Carrier :=
      { toRingHom := n.toRingHom
        commutes' := hsemi } with hnA
    set nR : (E₁.baseChange R).Carrier →ₐ[R] F.Carrier :=
      (Algebra.TensorProduct.lift (Algebra.ofId R F.Carrier) nA
        (fun r x => Commute.all _ _)).comp (E₁.baseChangeEquiv R).toAlgHom with hnR
    refine (mk_eq_mk_iff C).mpr ⟨F, nR, AlgHom.id R F.Carrier, ?_⟩
    refine Subtype.ext ?_
    rw [descentMap_coe, descentMap_coe, descentBaseChange_coe, ← relPicAlgMap_comp,
      show (AlgHom.id R F.Carrier).restrictScalars k = AlgHom.id k F.Carrier from rfl,
      relPicAlgMap_id,
      show (nR.restrictScalars k).comp
          ((E₁.baseChangeInclude R).restrictScalars k) = n from AlgHom.ext fun z => by
        simp [hnR, hnA, Algebra.EtaleCover.baseChangeInclude, Algebra.ofId_apply]]
    exact hcls
  exact hstep

end GlueHelpers

section Glue

variable {A : Type u} [CommRing A] [Algebra k A]
variable {ι : Type u} [Finite ι] (g : ι → A)
variable (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra k (S i)]
  [∀ i, Algebra A (S i)] [∀ i, IsScalarTower k A (S i)]
  [∀ i, IsLocalization.Away (g i) (S i)]
variable (T : ι → ι → Type u) [∀ i j, CommRing (T i j)] [∀ i j, Algebra k (T i j)]
  [∀ i j, Algebra A (T i j)] [∀ i j, IsScalarTower k A (T i j)]
  [∀ i j, IsLocalization.Away (g i * g j) (T i j)]

set_option maxHeartbeats 3200000 in
-- The pi- and tensor-instance towers exceed the default unification budget.
/-- **Zariski gluing of the étale plus construction**: a family of plus classes on a
finite covering family of localizations of `A`, compatible on the pairwise overlap
localizations, is the family of restrictions of a plus class on `A`.  Together with
`PicEtAff.eq_of_away_eq` this is the Zariski sheaf property of `PicEtAff C ·` on affine
tests, the gluing engine of the Layer-2 functor. -/
theorem exists_mapAlg_eq_of_compat (hg : Ideal.span (Set.range g) = ⊤)
    (x : ∀ i, PicEtAff C (S i))
    (hcompat : ∀ i j, PicEtAff.mapAlg C
        ((IsLocalization.Away.algHomOfDvd (g i) (g i * g j) (S i) (T i j)
          (dvd_mul_right (g i) (g j))).restrictScalars k) (x i)
      = PicEtAff.mapAlg C
        ((IsLocalization.Away.algHomOfDvd (g j) (g i * g j) (S j) (T i j)
          (dvd_mul_left (g j) (g i))).restrictScalars k) (x j)) :
    ∃ z : PicEtAff C A,
      ∀ i, PicEtAff.mapAlg C (IsScalarTower.toAlgHom k A (S i)) z = x i := by
  classical
  haveI := Fintype.ofFinite ι
  -- representatives
  have hrep : ∀ i, ∃ (E : Algebra.EtaleCover (S i)) (ξ : descentClasses C E),
      x i = PicEtAff.mk C E ξ := by
    intro i
    induction x i using PicEtAff.ind with | _ E ξ => exact ⟨E, ξ, rfl⟩
  choose E ξ hx using hrep
  -- scalar towers for the covering carriers
  haveI htower : ∀ i, IsScalarTower k A (E i).Carrier := fun i =>
    .of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k (S i) (E i).Carrier c,
        IsScalarTower.algebraMap_apply k A (S i) c,
        ← IsScalarTower.algebraMap_apply A (S i) (E i).Carrier (algebraMap k A c)]
  -- the pair conditions
  have hpair : ∀ i j,
      relPicAlgMap C (Algebra.TensorProduct.includeLeft :
        (E i).Carrier →ₐ[k] (E i).Carrier ⊗[A] (E j).Carrier)
        ((ξ i : relPic C (overSpec k (E i).Carrier)))
      = relPicAlgMap C ((Algebra.TensorProduct.includeRight :
          (E j).Carrier →ₐ[A] (E i).Carrier ⊗[A] (E j).Carrier).restrictScalars k)
        ((ξ j : relPic C (overSpec k (E j).Carrier))) := by
    intro i j
    refine relPicAlgMap_tensor_eq_of_compat C
      (IsLocalization.Away.algHomOfDvd (g i) (g i * g j) (S i) (T i j)
        (dvd_mul_right (g i) (g j)))
      (IsLocalization.Away.algHomOfDvd (g j) (g i * g j) (S j) (T i j)
        (dvd_mul_left (g j) (g i)))
      (E i) (E j) (g i) (g j) (ξ i) (ξ j) ?_
    rw [← hx i, ← hx j]
    exact hcompat i j
  -- lift the underlying classes to the product
  obtain ⟨ζ, hζ⟩ := relPic.exists_pi_lift C (fun i => (E i).Carrier)
    (fun i => (ξ i : relPic C (overSpec k (E i).Carrier)))
  -- the product cover of the base
  obtain ⟨W, ⟨e⟩⟩ := exists_etaleCover_pi g S hg E
  set ζW : relPic C (overSpec k W.Carrier) :=
    relPicAlgMap C (e.symm.toAlgHom.restrictScalars k) ζ with hζW
  -- the descent condition of the lifted class over `A`
  have hmem : ζW ∈ descentClasses C W := by
    rw [mem_descentClasses_iff]
    -- transport to the pi-decomposition of the tensor square
    set Ψ : (W.Carrier ⊗[A] W.Carrier)
        ≃ₐ[A] Π p : ι × ι, (E p.1).Carrier ⊗[A] (E p.2).Carrier :=
      (Algebra.TensorProduct.congr e e).trans
        (Algebra.TensorProduct.piDoubleEquivA A (fun i => (E i).Carrier)) with hΨ
    apply relPicAlgMap_algEquiv_injective C (Ψ.restrictScalars k)
    rw [show (Ψ.restrictScalars k).toAlgHom = Ψ.toAlgHom.restrictScalars k from rfl,
      ← relPicAlgMap_comp, ← relPicAlgMap_comp, hζW, ← relPicAlgMap_comp,
      ← relPicAlgMap_comp]
    -- componentwise over the finite product
    refine relPic.eq_of_pi_proj_eq C
      (fun p : ι × ι => (E p.1).Carrier ⊗[A] (E p.2).Carrier) (fun p => ?_)
    rw [← relPicAlgMap_comp, ← relPicAlgMap_comp]
    -- identify the two composites
    have hcompL : (Pi.evalAlgHom k
          (fun p : ι × ι => (E p.1).Carrier ⊗[A] (E p.2).Carrier) p).comp
          (((Ψ.toAlgHom.restrictScalars k).comp
            ((doubleInl W : W.Carrier →ₐ[k] W.Carrier ⊗[A] W.Carrier))).comp
            (e.symm.toAlgHom.restrictScalars k))
        = (Algebra.TensorProduct.includeLeft :
            (E p.1).Carrier →ₐ[k] (E p.1).Carrier ⊗[A] (E p.2).Carrier).comp
          (Pi.evalAlgHom k (fun i => (E i).Carrier) p.1) := by
      ext z
      simp [hΨ, doubleInl, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.piDoubleEquivA, Algebra.TensorProduct.piPiAlgEquiv_tmul]
    have hcompR : (Pi.evalAlgHom k
          (fun p : ι × ι => (E p.1).Carrier ⊗[A] (E p.2).Carrier) p).comp
          (((Ψ.toAlgHom.restrictScalars k).comp
            ((doubleInr W : W.Carrier →ₐ[k] W.Carrier ⊗[A] W.Carrier))).comp
            (e.symm.toAlgHom.restrictScalars k))
        = (AlgHom.restrictScalars k (Algebra.TensorProduct.includeRight :
            (E p.2).Carrier →ₐ[A] (E p.1).Carrier ⊗[A] (E p.2).Carrier)).comp
          (Pi.evalAlgHom k (fun i => (E i).Carrier) p.2) := by
      ext z
      simp [hΨ, doubleInr, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.piDoubleEquivA, Algebra.TensorProduct.piPiAlgEquiv_tmul]
    rw [hcompL, hcompR, relPicAlgMap_comp, relPicAlgMap_comp, hζ p.1, hζ p.2]
    exact hpair p.1 p.2
  -- the glued class and its restrictions
  refine ⟨PicEtAff.mk C W ⟨ζW, hmem⟩, fun i => ?_⟩
  rw [hx i]
  refine mapAlg_mk_eq_mk C (IsScalarTower.toAlgHom k A (S i)) W (E i) ⟨ζW, hmem⟩ (ξ i)
    ((Pi.evalAlgHom k (fun j => (E j).Carrier) i).comp
      (e.toAlgHom.restrictScalars k)) (fun a => ?_) ?_
  · change (Pi.evalAlgHom k (fun j => (E j).Carrier) i) (e (algebraMap A W.Carrier a))
      = _
    rw [e.commutes a]
    change algebraMap A ((E i).Carrier) a = _
    rw [IsScalarTower.algebraMap_apply A (S i) ((E i).Carrier) a]
    rfl
  · change relPicAlgMap C ((Pi.evalAlgHom k (fun j => (E j).Carrier) i).comp
        (e.toAlgHom.restrictScalars k)) ζW
      = (ξ i : relPic C (overSpec k (E i).Carrier))
    rw [hζW, ← relPicAlgMap_comp,
      show ((Pi.evalAlgHom k (fun j => (E j).Carrier) i).comp
          (e.toAlgHom.restrictScalars k)).comp (e.symm.toAlgHom.restrictScalars k)
        = Pi.evalAlgHom k (fun j => (E j).Carrier) i from AlgHom.ext fun z => by
          simp]
    exact hζ i

end Glue

end PicEtAff

end AlgebraicGeometry
