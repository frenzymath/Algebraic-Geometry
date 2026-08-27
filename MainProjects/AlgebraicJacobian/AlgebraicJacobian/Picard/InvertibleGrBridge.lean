/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.SectionGradedRing
import AlgebraicJacobian.Picard.FlatKernelBase

/-!
# The bridge `IsLocallyTrivial → IsInvertibleGr` (P0.5)

`Picard/SectionGradedRing.lean` defines the section graded ring `Γ_*(X, L)` and,
for the commutativity of the multiplication, the trivialising-basis predicate
`IsInvertibleGr L` (`SectionGradedRing.lean:146`): there is an indexed *basis*
`{Uᵢ}` of opens of `X` on each of which the section module `Γ(L, Uᵢ)` is an
**invertible** `Γ(X, Uᵢ)`-module.

`Picard/LineBundlePullback.lean` defines the geometric notion `IsLocallyTrivial M`
(`LineBundlePullback.lean:115`): every point has an affine open neighbourhood on
which `M` restricts to the structure sheaf `𝒪`.

This file supplies the missing bridge between the two: **a locally trivial sheaf
of modules is invertible-graded**, `IsLocallyTrivial.isInvertibleGr`.  The three
ingredients (wave-5 scoping) are:

* `Module.Invertible` from a section-level trivialisation
  (`Scheme.LineBundle.isInvertible_of_restrict_iso`): applying `Γ(-, ⊤)` to a
  chart trivialisation `M|_V ≅ 𝒪_V` presents the section module `Γ(M, V)` as a
  rank-one free `Γ(X, V)`-module, hence invertible
  (`Module.Invertible R R` + `Module.Invertible.congr`);
* the trivialising opens form a **basis**
  (`TopologicalSpace.Opens.isBasis_iff_nbhd`): every neighbourhood of every point
  contains an affine trivialising chart by
  `IsLocallyTrivial.exists_affine_trivializing_le` (which is the chart-shrink
  `IsLocallyTrivial.trivialization_of_le` of `Picard/FlatKernelBase.lean`);
* assembling these into the `IsInvertibleGr` witness against its basis-form
  definition.

Blueprint: `def:isInvertible`, `lem:sectionGradedRing_gcommSemiring`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).  Source: Stacks tag 01CR / 01HK.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.LineBundle

variable {X : Scheme.{u}}

/-- **Section-level invertibility from a chart trivialisation.** If `M` restricts
to the structure sheaf on an open `V` (`M|_V ≅ 𝒪_V`), then the section module
`Γ(M, V)` is an invertible `Γ(X, V)`-module: the top-open component of the
trivialisation is a `Γ(X, V)`-linear isomorphism `Γ(M, V) ≃ₗ Γ(𝒪_V, ⊤)` onto the
rank-one free module `Γ(X, V)`, so `Module.Invertible.congr` transports the
tautological invertibility `Module.Invertible Γ(X, V) Γ(X, V)`. -/
lemma isInvertible_of_restrict_iso {M : X.Modules} (V : X.Opens)
    (e : M.restrict V.ι ≅ SheafOfModules.unit (V : Scheme).ringCatSheaf) :
    Module.Invertible ↥(X.presheaf.obj (op V)) ↥(M.val.obj (op V)) := by
  -- Work at the top open of `(V : Scheme)`, where `Γ(M, V.ι ''ᵁ ⊤) = Γ(M.restrict V.ι, ⊤)`
  -- and `Γ(X, V.ι ''ᵁ ⊤) = Γ((V : Scheme), ⊤) = Γ(𝒪_V, ⊤)` definitionally (`restrict_obj`,
  -- `Scheme.Opens.toScheme_presheaf_obj`, and the unit-section identity, all `rfl`).  Taking the
  -- codomain to be the *ring* `Γ(X, V.ι ''ᵁ ⊤)` itself (its self-module) keeps every instance on
  -- the `X`-side, so `.congr` lands the goal's module instance and no scheme-instance gap remains.
  -- `restrictAppIso` is the mathlib `Ab`-iso `Γ(M.restrict V.ι, ⊤) ≅ Γ(M, V.ι ''ᵁ ⊤)`
  -- bridging the two (non-defeq) section-module structures, with the scalar-compatibility
  -- lemmas `smul_restrictAppIso_*` and `ι_appIso : V.ι.appIso ⊤ = Iso.refl`.
  set α : Γ(M.restrict V.ι, ⊤) ≅ Γ(M, V.ι ''ᵁ ⊤) := M.restrictAppIso V.ι ⊤ with hα
  let f : Γ(M, V.ι ''ᵁ ⊤) ≃ₗ[Γ(X, V.ι ''ᵁ ⊤)] Γ(X, V.ι ''ᵁ ⊤) :=
    { toFun := fun x => e.hom.app ⊤ (α.inv x)
      map_add' := fun x y => by rw [map_add, map_add]; rfl
      map_smul' := fun r x => by
        simp only [hα, Scheme.Modules.smul_restrictAppIso_inv_apply,
          Scheme.Opens.ι_appIso, Iso.refl_hom, Scheme.Modules.Hom.app_smul, RingHom.id_apply]
        rfl
      invFun := fun y => α.hom (e.inv.app ⊤ y)
      left_inv := fun x => by
        have h1 : e.inv.app ⊤ (e.hom.app ⊤ (α.inv x)) = α.inv x := by
          change (e.hom ≫ e.inv).app ⊤ (α.inv x) = α.inv x
          rw [e.hom_inv_id]; rfl
        change α.hom (e.inv.app ⊤ (e.hom.app ⊤ (α.inv x))) = x
        rw [h1]; exact α.inv_hom_id_apply x
      right_inv := fun y => by
        have h1 : α.inv (α.hom (e.inv.app ⊤ y)) = e.inv.app ⊤ y := α.hom_inv_id_apply _
        change e.hom.app ⊤ (α.inv (α.hom (e.inv.app ⊤ y))) = y
        rw [h1]
        change (e.inv ≫ e.hom).app ⊤ y = y
        rw [e.inv_hom_id]; rfl }
  have key : Module.Invertible Γ(X, V.ι ''ᵁ ⊤) Γ(M, V.ι ''ᵁ ⊤) :=
    Module.Invertible.congr f.symm
  exact V.ι_image_top ▸ key

/-- **The bridge `IsLocallyTrivial → IsInvertibleGr`** (P0.5).  A locally trivial
sheaf of modules `M` is invertible-graded: the trivialising opens
`{V : M|_V ≅ 𝒪_V}` form the required basis (every neighbourhood of every point
contains an affine trivialising chart, by `exists_affine_trivializing_le`), and
on each such open the section module `Γ(M, V)` is an invertible `Γ(X, V)`-module
(`isInvertible_of_restrict_iso`).  This unlocks the graded-commutative section
ring `sectionGradedRing_gcommSemiring` for every line bundle. -/
theorem IsLocallyTrivial.isInvertibleGr {M : X.Modules} (hM : IsLocallyTrivial M) :
    Scheme.Modules.IsInvertibleGr M := by
  refine ⟨{ V : X.Opens //
      Nonempty (M.restrict V.ι ≅ SheafOfModules.unit (V : Scheme).ringCatSheaf) },
    Subtype.val, ?_, ?_⟩
  · -- the trivialising opens form a basis
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro W x hxW
    obtain ⟨V, hxV, _hVaff, hVW, hV⟩ := hM.exists_affine_trivializing_le hxW
    exact ⟨V, ⟨⟨V, hV⟩, rfl⟩, hxV, hVW⟩
  · -- each trivialising open carries an invertible section module
    rintro ⟨V, ⟨e⟩⟩
    exact isInvertible_of_restrict_iso V e

end AlgebraicGeometry.Scheme.LineBundle
