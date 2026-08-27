/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
## Project-local Mathlib supplement — cover-localization iso criterion for `Scheme.Modules`

A morphism `φ : M ⟶ N` of sheaves of modules on a scheme `X` is an isomorphism iff its
restriction to each member of an open cover `𝒰` is an isomorphism.  Mathlib has the
"iso ⟺ iso on every open" criterion (`Scheme.Modules.Hom.isIso_iff_isIso_app`) and the
"restrict-to-open-immersion vs. stalk" comparison (`Scheme.Modules.restrictStalkNatIso`), but not
this *joint* cover-conservativity statement.  It is the keystone of the open-immersion
Beck–Chevalley leaf of the flat-base-change development (Stacks 02KH): it lets one verify that the
base-change comparison morphism is an isomorphism by checking it on the members of an affine cover.

The reverse (content) direction goes through the underlying presheaves of abelian groups: the
forgetful functor `Scheme.Modules.toPresheaf X` reflects isomorphisms, presheaves of modules are
sheaves of abelian groups (`Scheme.Modules.isSheaf`), and isomorphy of a sheaf-of-`Ab` morphism is
detected on stalks (`TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`); the per-point reduction to a
cover member is exactly `Scheme.Modules.restrictStalkNatIso`.
-/

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Hom

/-- A morphism of sheaves of modules on a scheme is an isomorphism iff its restriction to every
member of an open cover is an isomorphism.  This is the joint cover-conservativity of the family of
restriction functors `{restrictFunctor (𝒰.f j)}`; project-local because Mathlib only packages the
single-open criterion `isIso_iff_isIso_app` and the per-leg stalk comparison `restrictStalkNatIso`,
not this assembled cover statement. -/
theorem isIso_iff_isIso_restrict
    {X : Scheme} {M N : X.Modules} (φ : M ⟶ N) (𝒰 : X.OpenCover) :
    IsIso φ ↔ ∀ j, IsIso ((Scheme.Modules.restrictFunctor (𝒰.f j)).map φ) := by
  constructor
  · -- (⟹) restriction functors preserve isomorphisms.
    intro h j
    haveI := h
    infer_instance
  · -- (⟸) the content direction.
    intro hj
    -- It suffices that the underlying presheaf morphism is an iso: `toPresheaf X` reflects isos.
    haveI key : IsIso ((Scheme.Modules.toPresheaf X).map φ) := by
      -- Present `M`, `N` as sheaves of abelian groups and `φ` as a morphism of `TopCat.Sheaf Ab`.
      set F : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩ with hF
      set G : TopCat.Sheaf Ab X.carrier := ⟨N.presheaf, N.isSheaf⟩ with hG
      set fS : F ⟶ G := ⟨(Scheme.Modules.toPresheaf X).map φ⟩ with hfS_def
      -- It suffices that `fS` be an iso: `Sheaf.forget` sends it to `(toPresheaf X).map φ`.
      suffices hfS : IsIso fS by
        haveI : IsIso fS := hfS
        exact Functor.map_isIso (TopCat.Sheaf.forget Ab X.carrier) fS
      -- Detect isomorphy of the sheaf-of-`Ab` morphism on stalks.
      rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
      intro x
      change IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map ((Scheme.Modules.toPresheaf X).map φ))
      -- Choose a cover member through `x` and a preimage point `y`.
      set j := 𝒰.idx x with hj_def
      obtain ⟨y, hy⟩ := 𝒰.covers x
      rw [← hy]
      -- The restricted morphism is an iso (hyp); push it through the functors to its `y`-stalk.
      haveI hrestr := hj j
      have hstalk : IsIso ((TopCat.Presheaf.stalkFunctor Ab y).map
          ((Scheme.Modules.toPresheaf (𝒰.X j)).map
            ((Scheme.Modules.restrictFunctor (𝒰.f j)).map φ))) :=
        Functor.map_isIso _ _
      -- `restrictStalkNatIso` conjugates the `y`-stalk of the restriction with `φ`'s `x`-stalk.
      exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso (𝒰.f j) y) φ).mp hstalk
    exact isIso_of_reflects_iso φ (Scheme.Modules.toPresheaf X)

end AlgebraicGeometry.Scheme.Modules.Hom
