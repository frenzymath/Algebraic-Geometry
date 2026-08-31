/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.QuasiAffine
import AlgebraicJacobian.Picard.SectionRingUniversal

/-!
# Sheaf-level H⁰ base change for a proper geometrically integral curve (campaign `B1`)

For a proper geometrically integral curve `C` over a field `k` and an arbitrary `k`-scheme `T`
(`πT : T ⟶ Spec k`), let `π := pullback.snd C.hom πT : (C ×_k T) ⟶ T` be the second projection of
the relative product.  The structure-sheaf pushforward comparison `𝒪_T ⟶ π_* 𝒪_{C ×_k T}` is an
**isomorphism**: a global function on `C ×_k T` is pulled back from `T`.  Geometrically this is the
degree-`0` cohomology-and-base-change statement `Γ(C_κ, 𝒪) = κ` on every fibre (the field of
constants, campaign `B0`), and its commutation with base change.

This file supplies the `B1` brick and its automorphism-freeness consumer (Kleiman §2,
rigidification of `Pic^♯`).  Contents:

* **P1 — affine base** (unconditional): `bijective_snd_appTop_baseChange` /
  `isIso_snd_appTop_baseChange`: for `A` a `k`-algebra, `Γ(Spec A, 𝒪) → Γ(C ×_k Spec A, 𝒪)` is
  bijective.  Proof: the `B0` base-change isomorphism
  `Γ(Spec A) ⊗_{Γ(Spec k)} Γ(C) ≅ Γ(C ×_k Spec A)` (`globalSectionsBaseChangeAlgEquiv`) composed
  with `includeLeft`, which is bijective because the right tensor factor `Γ(C, 𝒪) = k` collapses
  (`Γ(C, 𝒪) ≃ₐ[k] k`, `globalSectionsAlgEquivBase`).  Generalised to **any affine base scheme**
  `W` with any `πT : W ⟶ Spec k` in `bijective_snd_appTop_of_isAffine` (transport across
  `W ≅ Spec Γ(W, 𝒪)`).

* **P2 — arbitrary base** (`isIso_snd_appTop`): the sheaf-level iso `IsIso π.appTop` for a general
  `T`, proved **unconditionally**.  Step A (`isIso_snd_app_of_isAffineOpen`) identifies `π ⁻¹ᵁ V`
  with the base change `C ×_k V` on each affine open `V` (pullback pasting + restriction-pullback)
  so the comparison is the P1 iso there; Step B assembles the per-affine-open isos over the
  affine-opens basis `T.isBasis_affineOpens` via stalks (mirroring
  `QuotScheme.isIso_sheaf_of_isIso_app_basicOpen`).  The `Prop`-class
  `HasStructureSheafPushforwardIso` is retained as a lightweight interface and discharged
  unconditionally by `instHasStructureSheafPushforwardIso`, so all P3 consumers fire for every `T`.

* **P3 — `lm:aut`** (unconditional at the ring level): `eq_apply_of_isRetraction` /
  `eq_one_of_isRetraction_of_restrict_eq_one` (ring form) and their scheme wrappers
  `appTop_restrict_eq_of_section`, `eq_one_of_section_of_restrict_eq_one`(`_of_gate`): a section
  `σ` of `π` retracts the (bijective) comparison map, so a global function on `C ×_k T` rigidified
  to `1` along `σ` equals `1`.

Campaign reference: milestone `B1` of `informal/pic-representability-campaign.md`; Kleiman §2.
Substrate: `AlgebraicJacobian/Picard/SectionRingUniversal.lean` (campaign `B0`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- The structure map `Γ(Spec k, 𝒪) → Γ(C, 𝒪_C)` of a proper geometrically integral
curve `C/k` is bijective (field of constants: `Γ(C, 𝒪_C) = k`). -/
theorem bijective_hom_appTop (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom] :
    Function.Bijective (C.hom.appTop).hom := by
  have hconst : Function.Bijective (constMap C).hom := by
    have := globalSectionsAlgEquivBase C
    constructor
    · exact (algebraMap k Γ(C.left, ⊤)).injective
    · exact HasTrivialConstants.surjective_constMap
  have hiso : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    ConcreteCategory.bijective_of_isIso _
  have hcomp : (constMap C).hom
      = (C.hom.appTop.hom).comp ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) := by
    simp [constMap]
  rw [hcomp] at hconst
  exact (Function.Bijective.of_comp_iff _ hiso).mp hconst

open TensorProduct in
set_option backward.isDefEq.respectTransparency false in
theorem bijective_snd_appTop_baseChange (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom]
    (A : Type u) [CommRing A] [Algebra k A] :
    Function.Bijective
      ((pullback.snd C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop).hom := by
  set g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k A)) with hg
  letI instSA : Algebra ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(Spec (CommRingCat.of A), ⊤) :=
    ((Spec.map (CommRingCat.ofHom (algebraMap k A))).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI instMA : Algebra ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(C.left, ⊤) :=
    (C.hom.appTop).hom.toAlgebra
  letI instPull : Algebra ↥Γ(Spec (CommRingCat.of A), ⊤)
      ↥Γ(pullback C.hom g, ⊤) :=
    ((pullback.snd C.hom g).appTop).hom.toAlgebra
  haveI : CompactSpace C.left := QuasiCompact.compactSpace_of_compactSpace C.hom
  haveI : QuasiSeparatedSpace C.left := quasiSeparatedSpace_of_quasiSeparated C.hom
  have e := globalSectionsBaseChangeAlgEquiv C.hom A
  -- The structure map `R = Γ(Spec k) → M = Γ(C)` is bijective (field of constants),
  -- so `M ≃ₐ[R] R`, hence `S ⊗[R] M ≃ₐ[S] S`, hence `includeLeft = algebraMap S (S⊗M)`
  -- is bijective; composing with the base-change iso `e` gives the claim.
  set R := ↥Γ(Spec (CommRingCat.of k), ⊤)
  set S := ↥Γ(Spec (CommRingCat.of A), ⊤)
  set M := ↥Γ(C.left, ⊤)
  have hRM : Function.Bijective (algebraMap R M) := bijective_hom_appTop C
  let φ : M ≃ₐ[R] R := (AlgEquiv.ofBijective (Algebra.ofId R M) hRM).symm
  let ε : (S ⊗[R] M) ≃ₐ[S] S :=
    (Algebra.TensorProduct.congr AlgEquiv.refl φ).trans (Algebra.TensorProduct.rid R S S)
  have hb2 : ∀ s : S, algebraMap S (S ⊗[R] M) s = ε.symm s := by
    intro s
    have h := ε.commutes s
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at h
    exact ε.eq_symm_apply.mpr h
  have hleft : Function.Bijective ⇑(algebraMap S (S ⊗[R] M)) := by
    have : ⇑(algebraMap S (S ⊗[R] M)) = ⇑ε.symm := funext hb2
    rw [this]; exact ε.symm.bijective
  change Function.Bijective ⇑(algebraMap S ↥Γ(pullback C.hom g, ⊤))
  have hcomp : ⇑(algebraMap S ↥Γ(pullback C.hom g, ⊤))
      = ⇑e ∘ ⇑(algebraMap S (S ⊗[R] M)) := by
    funext s; exact (e.commutes s).symm
  rw [hcomp]
  exact e.bijective.comp hleft

/-- **P1 as an isomorphism of `CommRingCat` objects.**  The comparison ring map
`Γ(Spec A, 𝒪) → Γ(C ×_k Spec A, 𝒪)` is an isomorphism. -/
theorem isIso_snd_appTop_baseChange (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom]
    (A : Type u) [CommRing A] [Algebra k A] :
    IsIso ((pullback.snd C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_snd_appTop_baseChange C A)

/-- `appTop` of an isomorphism is an isomorphism (`appTop` is contravariantly functorial). -/
private lemma isIso_appTop_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    IsIso (f.appTop) := by
  refine ⟨(inv f).appTop, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_appTop, IsIso.inv_hom_id]; simp
  · rw [← Scheme.Hom.comp_appTop, IsIso.hom_inv_id]; simp

/-- **P1 for an arbitrary affine base scheme.**  For any affine scheme `W` and any structure
morphism `h : W ⟶ Spec k`, the comparison `Γ(W, 𝒪) → Γ(C ×_k W, 𝒪)` is bijective.  This is P1
transported across `W ≅ Spec Γ(W, 𝒪)` (every affine `W` is `Spec` of its global sections, and every
`Spec Γ(W) ⟶ Spec k` is `Spec.map` of a ring map, i.e. gives `Γ(W)` a `k`-algebra structure). -/
theorem bijective_snd_appTop_of_isAffine (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom]
    {W : Scheme.{u}} [IsAffine W] (h : W ⟶ Spec (CommRingCat.of k)) :
    Function.Bijective ((pullback.snd C.hom h).appTop).hom := by
  set e : W ≅ Spec Γ(W, ⊤) := W.isoSpec with he
  set h₀ : Spec Γ(W, ⊤) ⟶ Spec (CommRingCat.of k) := e.inv ≫ h with hh0
  have hh : h = e.hom ≫ h₀ := by rw [hh0, Iso.hom_inv_id_assoc]
  set φ : CommRingCat.of k ⟶ Γ(W, ⊤) := Spec.preimage h₀ with hφ
  have hspec : Spec.map φ = h₀ := Spec.map_preimage h₀
  letI : Algebra k Γ(W, ⊤) := φ.hom.toAlgebra
  have hP1 := bijective_snd_appTop_baseChange C Γ(W, ⊤)
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap k Γ(W, ⊤))) = h₀ := by
    rw [show (algebraMap k Γ(W, ⊤)) = CommRingCat.Hom.hom φ from rfl,
      CommRingCat.ofHom_hom, hspec]
  rw [hbase] at hP1
  -- Transport across the arrow isomorphism `m` (base change along `e.hom : W ≅ Spec Γ(W)`).
  let m : pullback C.hom h ⟶ pullback C.hom h₀ :=
    pullback.map C.hom h C.hom h₀ (𝟙 _) e.hom (𝟙 _) (by simp) (by simp [hh])
  haveI hmiso : IsIso m := by apply pullback.map_isIso
  have hcompat : m ≫ pullback.snd C.hom h₀ = pullback.snd C.hom h ≫ e.hom := by
    simp only [m, pullback.map, Limits.pullback.lift_snd]
  have key := congrArg Scheme.Hom.appTop hcompat
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at key
  haveI hIsoP1 : IsIso ((pullback.snd C.hom h₀).appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hP1
  haveI : IsIso (m.appTop) := isIso_appTop_of_isIso m
  haveI : IsIso (e.hom.appTop) := isIso_appTop_of_isIso e.hom
  haveI : IsIso ((pullback.snd C.hom h).appTop) := by
    have hh2 : (pullback.snd C.hom h).appTop
        = inv (e.hom.appTop) ≫ (pullback.snd C.hom h₀).appTop ≫ m.appTop := by
      rw [key, IsIso.inv_hom_id_assoc]
    rw [hh2]; infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mp this

/-- Transport `IsIso (·.appTop)` across an isomorphism of arrows: given scheme morphisms
`a : W ⟶ X`, `b : Y ⟶ Z` and isomorphisms `l : W ≅ Y`, `r : X ≅ Z` forming a commuting square
`a ≫ r.hom = l.hom ≫ b`, if `b.appTop` is an isomorphism then so is `a.appTop`.  (The two ends of
the square being isomorphisms makes the induced global-section maps differ by isomorphisms.) -/
private lemma isIso_appTop_of_isoSq {W X Y Z : Scheme.{u}} {a : W ⟶ X} {b : Y ⟶ Z}
    (l : W ≅ Y) (r : X ≅ Z) (comm : a ≫ r.hom = l.hom ≫ b) [IsIso (b.appTop)] :
    IsIso (a.appTop) := by
  have key := congrArg Scheme.Hom.appTop comm
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at key
  haveI : IsIso (r.hom.appTop) := isIso_appTop_of_isIso r.hom
  haveI : IsIso (l.hom.appTop) := isIso_appTop_of_isIso l.hom
  have ha : a.appTop = inv (r.hom.appTop) ≫ b.appTop ≫ l.hom.appTop := by
    rw [← key, IsIso.inv_hom_id_assoc]
  rw [ha]; infer_instance

/-- **Step A: the per-affine-open comparison is an isomorphism.**  For a proper geometrically
integral curve `C/k`, an arbitrary base `T` with structure map `πT : T ⟶ Spec k`, and any affine
open `V ⊆ T`, the structure-sheaf comparison `Γ(T, V) → Γ(C ×_k T, π⁻¹ V)`
(`π = pullback.snd C.hom πT`) is an isomorphism.  This is P1 at the affine base `V.toScheme`
(`bijective_snd_appTop_of_isAffine` with structure map `V.ι ≫ πT`) transported across the
identification `π ⁻¹ᵁ V ≅ C ×_k V` supplied by pullback pasting (`pullbackLeftPullbackSndIso`) and
the restriction-pullback isomorphism (`pullbackRestrictIsoRestrict`). -/
theorem isIso_snd_app_of_isAffineOpen (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom]
    {T : Scheme.{u}} (πT : T ⟶ Spec (CommRingCat.of k))
    {V : T.Opens} (hV : IsAffineOpen V) :
    IsIso ((pullback.snd C.hom πT).app V) := by
  haveI : IsAffine V.toScheme := hV
  set π := pullback.snd C.hom πT with hπ
  -- P1 at the affine base `V.toScheme`, structure map `V.ι ≫ πT`.
  haveI hbase : IsIso ((pullback.snd C.hom (V.ι ≫ πT)).appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_snd_appTop_of_isAffine C (V.ι ≫ πT))
  -- Transport 1: the pasting iso `pullback π V.ι ≅ pullback C.hom (V.ι ≫ πT)`.
  haveI h1 : IsIso ((pullback.snd π V.ι).appTop) :=
    isIso_appTop_of_isoSq (b := pullback.snd C.hom (V.ι ≫ πT))
      (pullbackLeftPullbackSndIso C.hom πT V.ι) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id]
          exact (pullbackLeftPullbackSndIso_hom_snd C.hom πT V.ι).symm)
  -- Transport 2: the restriction-pullback iso `(π ⁻¹ᵁ V).toScheme ≅ pullback π V.ι`.
  haveI h2 : IsIso ((π ∣_ V).appTop) :=
    isIso_appTop_of_isoSq (b := pullback.snd π V.ι)
      (pullbackRestrictIsoRestrict π V).symm (Iso.refl _) (by simp [morphismRestrict])
  -- Convert `(π ∣_ V).appTop` to `π.app V` via `morphismRestrict_appTop`.  The trailing factor is
  -- `presheaf.map` of an `eqToHom`, hence an isomorphism.
  have happ := morphismRestrict_appTop π V
  haveI hg_iso : IsIso ((pullback C.hom πT).presheaf.map
      (eqToHom (image_morphismRestrict_preimage π V ⊤)).op) := by
    rw [eqToHom_op, eqToHom_map]; infer_instance
  -- `happ : (π ∣_ V).appTop = π.app (V.ι ''ᵁ ⊤) ≫ g` with `g` the iso above; peel off `g`.
  have h2' : IsIso (π.app (V.ι ''ᵁ ⊤) ≫ (pullback C.hom πT).presheaf.map
      (eqToHom (image_morphismRestrict_preimage π V ⊤)).op) := by rw [← happ]; exact h2
  haveI happV : IsIso (π.app (V.ι ''ᵁ ⊤)) := (isIso_comp_right_iff _ _).mp h2'
  have hVeq : V.ι ''ᵁ ⊤ = V := V.ι_image_top
  exact hVeq ▸ happV

/-! ## P2: the sheaf-level H⁰ base-change brick over an arbitrary base `T`

For an arbitrary `k`-scheme `T` with structure morphism `πT : T ⟶ Spec k`, the structure-sheaf
comparison `𝒪_T ⟶ π_* 𝒪_{C×T}` (`π = pullback.snd C.hom πT`) is an isomorphism.  The proof route
(Kleiman §2; cohomology-and-base-change in degree `0`) is: for every affine open `V ⊆ T` the
restricted comparison `Γ(T, V) → Γ(C × T, π⁻¹V)` is the P1 base-change iso at `A = Γ(V, 𝒪)`
(because `π⁻¹V ≅ C ×_k V`), and these per-affine-open isos assemble to a sheaf isomorphism on the
affine-opens basis `T.isBasis_affineOpens` via stalks (mirroring
`QuotScheme.isIso_sheaf_of_isIso_app_basicOpen`).

This is now proved **unconditionally for every base** in `isIso_snd_appTop` below (Step A per
affine open + Step B stalk assembly).  The `Prop`-class `HasStructureSheafPushforwardIso` is
retained as a lightweight interface and discharged unconditionally by
`instHasStructureSheafPushforwardIso`, so every downstream consumer (`lm:aut`) fires for arbitrary
`T`. -/

/-- **Step B (`B1`, P2): the structure-sheaf pushforward comparison is an isomorphism over an
arbitrary base.**  For a proper geometrically integral curve `C/k` and an arbitrary `k`-scheme `T`
with structure map `πT : T ⟶ Spec k`, the comparison `Γ(T, 𝒪) → Γ(C ×_k T, 𝒪)` on global sections
is an isomorphism (`π = pullback.snd C.hom πT`).

Proof: the presheaf-level comparison `π.c`, packaged as a morphism of the sheaves of commutative
rings `𝒪_T ⟶ π_* 𝒪_{C ×_k T}` on `T`, is an isomorphism on every affine open by Step A
(`isIso_snd_app_of_isAffineOpen`).  Since the affine opens form a basis
(`Scheme.isBasis_affineOpens`), the induced stalk maps are all bijective (injectivity via
`stalkFunctor_map_injective_of_isBasis`, surjectivity via the per-affine-open germ lift), so the
`⊤`-component `π.appTop` is an isomorphism (`app_isIso_of_stalkFunctor_map_iso`).  This mirrors
`QuotScheme.isIso_sheaf_of_isIso_app_basicOpen` but on the affine-opens basis. -/
theorem isIso_snd_appTop (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom]
    {T : Scheme.{u}} (πT : T ⟶ Spec (CommRingCat.of k)) :
    IsIso ((pullback.snd C.hom πT).appTop) := by
  set π := pullback.snd C.hom πT with hπ
  -- Package the presheaf-level comparison `π.c` as a morphism of sheaves of rings on `T`.
  let G := (TopCat.Sheaf.pushforward CommRingCat π.base).obj (pullback C.hom πT).sheaf
  let α : T.sheaf ⟶ G := ⟨π.c⟩
  -- On every affine open the component is `π.app U`, an isomorphism by Step A.
  have hbasis : ∀ U ∈ T.affineOpens, IsIso (α.1.app (Opposite.op U)) := fun U hU =>
    isIso_snd_app_of_isAffineOpen C πT hU
  have hinj : ∀ U ∈ T.affineOpens, Function.Injective (α.1.app (Opposite.op U)) := fun U hU =>
    ((ConcreteCategory.isIso_iff_bijective _).mp (hbasis U hU)).1
  -- Every stalk map of `α` is bijective, hence an isomorphism.
  haveI hstalk : ∀ x : ↑T,
      IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map α.1) := by
    intro x
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis
      T.isBasis_affineOpens hinj x, ?_⟩
    intro t
    obtain ⟨U, hxU, hUB, s, rfl⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis T.isBasis_affineOpens G.presheaf x t
    obtain ⟨s', rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).mp (hbasis U hUB)).2 s
    exact ⟨T.sheaf.presheaf.germ U x hxU s',
      by rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]⟩
  -- The `⊤`-component of `α` is therefore an isomorphism, and equals `π.appTop`.
  haveI : ∀ x : (⊤ : TopologicalSpace.Opens ↑T),
      IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x.val).map α.1) := fun x => hstalk x.val
  exact TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso α (⊤ : TopologicalSpace.Opens ↑T)

/-- **Gate (`B1`, P2): the structure-sheaf pushforward comparison is an isomorphism.**  Carries the
conclusion `IsIso (π.appTop)` — equivalently `Γ(T, 𝒪) → Γ(C × T, 𝒪)` bijective — for the second
projection `π = pullback.snd C.hom πT` of the relative product.

Discharged **unconditionally for every base** by `instHasStructureSheafPushforwardIso` (Step B,
`isIso_snd_appTop`).  It is retained as a lightweight interface for the automorphism-rigidity
(`lm:aut`) consumers of campaign `B1`; every such consumer is now available for arbitrary `T`. -/
class HasStructureSheafPushforwardIso (C : Over (Spec (CommRingCat.of k)))
    {T : Scheme.{u}} (πT : T ⟶ Spec (CommRingCat.of k)) : Prop where
  isIso_appTop : IsIso ((pullback.snd C.hom πT).appTop)

/-- **The gate is unconditional for every base** (Step B).  For a proper geometrically integral
curve `C/k`, an arbitrary `k`-scheme `T`, and any structure map `πT : T ⟶ Spec k`, the
structure-sheaf pushforward comparison `Γ(T, 𝒪) → Γ(C ×_k T, 𝒪)` is an isomorphism
(`isIso_snd_appTop`: the per-affine-open P1 base-change isos assembled over the affine-opens basis).
This subsumes the earlier affine-only instance and discharges the gate for all downstream
`lm:aut` consumers of campaign `B1`. -/
instance instHasStructureSheafPushforwardIso (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom]
    {T : Scheme.{u}} (πT : T ⟶ Spec (CommRingCat.of k)) :
    HasStructureSheafPushforwardIso C πT :=
  ⟨isIso_snd_appTop C πT⟩

/-- Extract the global-sections bijectivity from the gate. -/
theorem bijective_appTop_of_hasStructureSheafPushforwardIso
    (C : Over (Spec (CommRingCat.of k))) {T : Scheme.{u}} (πT : T ⟶ Spec (CommRingCat.of k))
    [HasStructureSheafPushforwardIso C πT] :
    Function.Bijective ((pullback.snd C.hom πT).appTop).hom :=
  (ConcreteCategory.isIso_iff_bijective _).mp HasStructureSheafPushforwardIso.isIso_appTop

/-! ## `lm:aut`: global functions on `C × T` are pulled back from `T`, uniquely

The ring-theoretic heart of the automorphism-rigidity lemma (Kleiman §2, rigidification of
`Pic^♯`): if the structure map `f : Γ(T, 𝒪) → Γ(C × T, 𝒪)` is bijective (P1/P2) and admits a
retraction `s` coming from a section `σ : T ⟶ C × T` of `π`, then every global function on
`C × T` is `f` of its restriction along `σ`.  Stated abstractly on rings so it is reusable for
both the affine base (P1) and the general base (P2). -/

/-- **Pulled-back-from-`T` (ring form).**  If `f : R →+* S` is bijective with retraction
`s : S →+* R` (`s ∘ f = id`), then every `u : S` satisfies `f (s u) = u`: `u` is determined by
its restriction `s u`.  Here `f = π.appTop` (the structure-sheaf comparison map) and `s = σ.appTop`
for a section `σ` of `π`. -/
theorem eq_apply_of_isRetraction {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : S →+* R) (hf : Function.Bijective f)
    (hsf : s.comp f = RingHom.id R) (u : S) : f (s u) = u := by
  obtain ⟨r, rfl⟩ := hf.surjective u
  have hsr : s (f r) = r := by rw [← RingHom.comp_apply, hsf, RingHom.id_apply]
  exact congrArg f hsr

/-- **Automorphism rigidity (ring form, `lm:aut`).**  A global function `u` on `C × T` whose
restriction along the section `σ` is `1` (`s u = 1`) is itself `1`, provided the comparison map
`f = π.appTop` is bijective and `s = σ.appTop` retracts it.  Downstream: a unit on `C × T`
rigidified to `1` along `σ` equals `1`. -/
theorem eq_one_of_isRetraction_of_restrict_eq_one {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : S →+* R) (hf : Function.Bijective f)
    (hsf : s.comp f = RingHom.id R) (u : S) (hu : s u = 1) : u = 1 := by
  have h := eq_apply_of_isRetraction f s hf hsf u
  rw [hu, map_one] at h
  exact h.symm

/-- A section `σ` of `π = pullback.snd C.hom πT` induces a retraction of the structure-sheaf
comparison map on global sections: `σ.appTop ∘ π.appTop = id`. -/
theorem retraction_appTop_of_section (C : Over (Spec (CommRingCat.of k)))
    {T : Scheme.{u}} (πT : T ⟶ Spec (CommRingCat.of k))
    (σ : T ⟶ pullback C.hom πT) (hσ : σ ≫ pullback.snd C.hom πT = 𝟙 T) :
    (σ.appTop).hom.comp ((pullback.snd C.hom πT).appTop).hom = RingHom.id _ := by
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, hσ]; simp

/-- **Global functions on `C × T` are pulled back from `T`, uniquely (scheme form).**  Given the
field-of-constants comparison bijectivity `hbij` (P1 for `T = Spec A`, P2 for general `T`) and a
section `σ` of `π = pullback.snd C.hom πT`, every global function `u` on `C × T` equals the
pullback along `π` of its restriction `σ.appTop u` along the section. -/
theorem appTop_restrict_eq_of_section (C : Over (Spec (CommRingCat.of k)))
    {T : Scheme.{u}} (πT : T ⟶ Spec (CommRingCat.of k))
    (hbij : Function.Bijective ((pullback.snd C.hom πT).appTop).hom)
    (σ : T ⟶ pullback C.hom πT) (hσ : σ ≫ pullback.snd C.hom πT = 𝟙 T)
    (u : ↥Γ(pullback C.hom πT, ⊤)) :
    ((pullback.snd C.hom πT).appTop).hom ((σ.appTop).hom u) = u :=
  eq_apply_of_isRetraction _ _ hbij (retraction_appTop_of_section C πT σ hσ) u

/-- **Automorphism rigidity for `C × T` (`lm:aut`, scheme form).**  Given the field-of-constants
comparison bijectivity `hbij` and a section `σ` of `π`, any global function `u` on `C × T` whose
restriction along `σ` is `1` equals `1` (Kleiman §2 rigidification of `Pic^♯`: a unit rigidified
to `1` along the identity section is trivial). -/
theorem eq_one_of_section_of_restrict_eq_one (C : Over (Spec (CommRingCat.of k)))
    {T : Scheme.{u}} (πT : T ⟶ Spec (CommRingCat.of k))
    (hbij : Function.Bijective ((pullback.snd C.hom πT).appTop).hom)
    (σ : T ⟶ pullback C.hom πT) (hσ : σ ≫ pullback.snd C.hom πT = 𝟙 T)
    (u : ↥Γ(pullback C.hom πT, ⊤)) (hu : (σ.appTop).hom u = 1) : u = 1 :=
  eq_one_of_isRetraction_of_restrict_eq_one _ _ hbij
    (retraction_appTop_of_section C πT σ hσ) u hu

/-- **Automorphism rigidity, gated form (`lm:aut`).**  For any base `T` supplying the P2 gate
`HasStructureSheafPushforwardIso`, a global function on `C × T` rigidified to `1` along a section
`σ` is `1`.  Unconditional for affine `T` (the gate instance is P1).  This is the reusable shape
Kleiman §2 uses to rigidify `Pic^♯`: a line-bundle automorphism restricting to the identity along
the identity section is the identity. -/
theorem eq_one_of_section_of_restrict_eq_one_of_gate (C : Over (Spec (CommRingCat.of k)))
    {T : Scheme.{u}} (πT : T ⟶ Spec (CommRingCat.of k))
    [HasStructureSheafPushforwardIso C πT]
    (σ : T ⟶ pullback C.hom πT) (hσ : σ ≫ pullback.snd C.hom πT = 𝟙 T)
    (u : ↥Γ(pullback C.hom πT, ⊤)) (hu : (σ.appTop).hom u = 1) : u = 1 :=
  eq_one_of_section_of_restrict_eq_one C πT
    (bijective_appTop_of_hasStructureSheafPushforwardIso C πT) σ hσ u hu

end AlgebraicGeometry.Scheme
