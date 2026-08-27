/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.RelPicFunctor
import AlgebraicJacobian.Picard.StructureSheafPushforward

/-!
# Rigidified relative Picard bundles (B1: the `RigidifiedPic` API)

For a relative curve `πC : C ⟶ S` with a **section of the projection**
`σ : T ⟶ C ×_S T` (i.e. `σ ≫ π_T = 𝟙_T`, where `π_T = pullback.snd πC πT`), Kleiman's
rigidification of the relative Picard functor replaces a bare line bundle `L` on
`C ×_S T` by a *rigidified* one — a bundle equipped with a trivialisation of its
restriction `σ^* L ≅ 𝒪_T` along the section. Rigidified bundles have no non-trivial
automorphisms (`lm:aut`, the ring-level heart of which is
`StructureSheafPushforward.eq_one_of_section_of_restrict_eq_one_of_gate`), so the
rigidified functor is a Zariski sheaf and represents the relative Picard functor.

This file supplies the substrate of that programme:

* `sectionPullbackProjIso` — the section base-change iso `σ^*(π_T^* N) ≅ N` (from
  `σ ≫ π_T = 𝟙_T` via the pullback pseudofunctor);
* `Rigidification σ L` — a trivialisation `σ^* L ≅ 𝒪_T`;
* `exists_rigidification_relPicRel` — **Kleiman `lm:fff`**: every `L` is
  `H_T`-equivalent to a rigidified bundle `L' = L ⊗ π_T^*((σ^* L)⁻¹)`;
* `rationalPointSection` — the section `σ_T` of the projection produced by a
  `k`-rational point `x₀` of `C`, matching the hypothesis shape consumed by the
  `StructureSheafPushforward` `lm:aut` lemmas.

Blueprint references: Kleiman §2 Def. `df:Pfs`, Lemmas `lm:fff` (existence of the
rigidified representative), `lm:aut` (automorphism-freeness). The `H_T`-relation
`PicSharp.relPicRel` is the one of `Picard/RelPicFunctor.lean`.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

namespace PicSharp

/-! ## §1. The section base-change isomorphism -/

/-- **Section base-change iso** `σ^*(π_T^* N) ≅ N`.

For a section `σ : T ⟶ C ×_S T` of the projection `π_T = pullback.snd πC πT`
(so `σ ≫ π_T = 𝟙_T`) and a sheaf of modules `N` on `T`, the pullback pseudofunctor
identity `(σ ≫ π_T)^* ≅ σ^* ∘ π_T^*` together with `𝟙_T^* ≅ id` identifies the
double pullback `σ^*(π_T^* N)` with `N`. This is the same three-step
`pullbackComp`/`pullbackCongr`/`pullbackId` chain as `LineBundle.pullback_pullback_eq`,
specialised to a section. -/
noncomputable def sectionPullbackProjIso {S C T : Scheme.{u}} {πC : C ⟶ S} {πT : T ⟶ S}
    (σ : T ⟶ Limits.pullback πC πT)
    (hσ : σ ≫ Limits.pullback.snd πC πT = 𝟙 T) (N : T.Modules) :
    (Scheme.Modules.pullback σ).obj
        ((Scheme.Modules.pullback (Limits.pullback.snd πC πT)).obj N) ≅ N :=
  (Scheme.Modules.pullbackComp σ (Limits.pullback.snd πC πT)).app N ≪≫
    (Scheme.Modules.pullbackCongr hσ).app N ≪≫ (Scheme.Modules.pullbackId T).app N

/-! ## §2. Rigidifications -/

/-- A **rigidification** of a line bundle `L` on `C ×_S T` along a section `σ` of the
projection is a trivialisation of the restriction `σ^* L ≅ 𝒪_T`. -/
structure Rigidification {S C T : Scheme.{u}} {πC : C ⟶ S} {πT : T ⟶ S}
    (σ : T ⟶ Limits.pullback πC πT) (L : LineBundle.OnProduct πC πT) where
  /-- The trivialising isomorphism `σ^* L ≅ 𝒪_T`. -/
  triv : (Scheme.Modules.pullback σ).obj L.carrier ≅ SheafOfModules.unit T.ringCatSheaf

/-! ## §3. Existence of a rigidified representative (`lm:fff`) -/

/-- **Existence of a rigidified representative** (Kleiman §2, `lm:fff`).

Every line bundle `L` on `C ×_S T` is `H_T`-equivalent (`PicSharp.relPicRel`) to a
line bundle `L'` carrying a rigidification along the section `σ`. Explicitly
`L' = L ⊗ π_T^*((σ^* L)⁻¹)`: its restriction along `σ` is
`σ^*L ⊗ σ^*(π_T^*(σ^*L)⁻¹) ≅ σ^*L ⊗ (σ^*L)⁻¹ ≅ 𝒪_T`
(using the section base-change iso `sectionPullbackProjIso`), and `L' ≅ π_T^*((σ^*L)⁻¹) ⊗ L`
differs from `L` by a pullback from the base, hence `[L'] = [L]` in
`Pic(C ×_S T) / π_T^* Pic(T)`. -/
theorem exists_rigidification_relPicRel {S C T : Scheme.{u}} {πC : C ⟶ S} {πT : T ⟶ S}
    (σ : T ⟶ Limits.pullback πC πT)
    (hσ : σ ≫ Limits.pullback.snd πC πT = 𝟙 T) (L : LineBundle.OnProduct πC πT) :
    ∃ L' : LineBundle.OnProduct πC πT,
      Nonempty (Rigidification σ L') ∧ PicSharp.relPicRel πC πT L' L := by
  classical
  -- `σ^* L` is locally trivial (pullback of a line bundle is a line bundle, 01HH).
  have hσL : LineBundle.IsLocallyTrivial ((Scheme.Modules.pullback σ).obj L.carrier) :=
    L.isLocallyTrivial.pullback σ
  -- Its tensor inverse `Ninv` on `T`, with `eN : σ^* L ⊗ Ninv ≅ 𝒪_T`.
  obtain ⟨Ninv, hNinv, ⟨eN⟩⟩ := Modules.exists_tensorObj_inverse hσL
  -- The twist `L' := L ⊗ π_T^* Ninv`.
  refine ⟨⟨Modules.tensorObj L.carrier
      (LineBundle.pullbackAlongProjection πC πT Ninv hNinv).carrier,
      Modules.tensorObj_isLocallyTrivial L.isLocallyTrivial
        (LineBundle.pullbackAlongProjection πC πT Ninv hNinv).isLocallyTrivial⟩, ?_, ?_⟩
  · -- Rigidification of `L'`:
    -- `σ^*(L ⊗ π_T^*Ninv) ≅ σ^*L ⊗ σ^*(π_T^*Ninv) ≅ σ^*L ⊗ Ninv ≅ 𝒪_T`.
    exact ⟨⟨Modules.pullbackTensorIsoOfLocallyTrivial σ L.carrier
          (LineBundle.pullbackAlongProjection πC πT Ninv hNinv).carrier
          L.isLocallyTrivial
          (LineBundle.pullbackAlongProjection πC πT Ninv hNinv).isLocallyTrivial ≪≫
        Modules.tensorObjIsoOfIso (Iso.refl _) (sectionPullbackProjIso σ hσ Ninv) ≪≫ eN⟩⟩
  · -- `H_T`-equivalence `L' ~ L`: `L' = L ⊗ π_T^*Ninv ≅ π_T^*Ninv ⊗ L` (braiding), take `N = Ninv`.
    exact ⟨Ninv, hNinv, ⟨Modules.tensorObj_braiding L.carrier
      (LineBundle.pullbackAlongProjection πC πT Ninv hNinv).carrier⟩⟩

/-! ## §4. The section attached to a rational point -/

/-- **The section of the projection produced by a rational point.** A `k`-rational
point `x₀ : Spec k ⟶ C` (a section of the structure map `πC`) determines, for every
test object `T` with structure map `πT : T ⟶ S`, a section
`σ_T := ⟨π_T ≫ x₀, 𝟙_T⟩ : T ⟶ C ×_S T` of the projection `π_T = pullback.snd πC πT`.
This is the section along which the relative Picard functor is rigidified. -/
noncomputable def rationalPointSection {S C T : Scheme.{u}} {πC : C ⟶ S} (πT : T ⟶ S)
    (x₀ : S ⟶ C) (hx₀ : x₀ ≫ πC = 𝟙 S) :
    T ⟶ Limits.pullback πC πT :=
  Limits.pullback.lift (πT ≫ x₀) (𝟙 T)
    (by rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp])

@[simp]
theorem rationalPointSection_comp_snd {S C T : Scheme.{u}} {πC : C ⟶ S} (πT : T ⟶ S)
    (x₀ : S ⟶ C) (hx₀ : x₀ ≫ πC = 𝟙 S) :
    rationalPointSection πT x₀ hx₀ ≫ Limits.pullback.snd πC πT = 𝟙 T :=
  Limits.pullback.lift_snd _ _ _

end PicSharp

end Scheme

end AlgebraicGeometry
