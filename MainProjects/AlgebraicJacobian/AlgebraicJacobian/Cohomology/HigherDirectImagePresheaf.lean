/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.HigherDirectImage
import AlgebraicJacobian.Cohomology.CechHigherDirectImage

/-!
# Presheaf description of the higher direct images `Rⁱ f_*` (Stacks 01XJ)

This file builds project-local infrastructure towards
`lem:higher_direct_image_presheaf`: the higher direct image `Rⁱ f_* F` is the
sheafification of the presheaf `V ↦ Hⁱ(f⁻¹(V), F)`.

The categorical heart of Stacks 01XJ is that **cohomology of a complex of sheaves
of modules is the sheafification of the objectwise (presheaf-level) homology**:
this holds because the sheafification functor of presheaves of modules is exact
(it preserves finite limits — `Mathlib`'s
`PresheafOfModules.instPreservesFiniteLimitsSheafification` — and, being a left
adjoint, finite colimits), hence preserves homology, and the counit of the
sheafification adjunction is an isomorphism on sheaves.

This file isolates that engine (`PresheafOfModules.homologyIsoSheafify`) and feeds
it through the right-derived-functor computation
(`InjectiveResolution.isoRightDerivedObj`) to express `Rⁿ f_* G`, for a chosen
injective resolution of `G`, as the sheafification of the presheaf-level homology
of the pushed-forward resolution
(`AlgebraicGeometry.higherDirectImage_iso_sheafify_presheafHomology`). The
remaining step to the blueprint statement — identifying that presheaf-level
homology with the cohomology presheaf `V ↦ Hⁿ(f⁻¹(V), G)` — is handed off (see
the `## Why I stopped` note in the task result).

See `blueprint/src/chapters/Cohomology_CechHigherDirectImage.tex`
(`lem:higher_direct_image_presheaf`, `def:higher_direct_image`).
-/

universe v u

open CategoryTheory Limits

/-! ## Project-local Mathlib supplement — homology of a complex under a functor -/

namespace CategoryTheory.Functor

/-- The homological-complex level of `ShortComplex.mapHomologyIso`: an additive,
homology-preserving functor `F` commutes with taking homology of a complex,
`((F.mapHomologicalComplex c).obj K).homology i ≅ F.obj (K.homology i)`.

Project-local: `Mathlib` provides this isomorphism only at the `ShortComplex`
level (`ShortComplex.mapHomologyIso`); we lift it degreewise to
`HomologicalComplex` (the two `homology` objects are definitionally the homology
of the relevant short complexes, so the lift is the `ShortComplex` isomorphism
applied to `K.sc i`). -/
noncomputable def mapHomologyIso'
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex A c) (i : ι) :
    ((F.mapHomologicalComplex c).obj K).homology i ≅ F.obj (K.homology i) :=
  (K.sc i).mapHomologyIso F

end CategoryTheory.Functor

/-! ## Project-local Mathlib supplement — sheaf homology is sheafified presheaf homology -/

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{v}} {R : Sheaf J RingCat.{v}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasSheafify J AddCommGrpCat.{v}]
  {ιc : Type} (cc : ComplexShape ιc)

/-- The sheafification functor of presheaves of modules is additive (it preserves
binary products, being a left adjoint that preserves finite limits).

Project-local: needed so that `sheafification α` can be applied to homological
complexes via `mapHomologicalComplex`. -/
noncomputable instance sheafificationAdditive :
    (PresheafOfModules.sheafification α).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The counit of the sheafification adjunction, applied levelwise to a complex of
sheaves of modules, is an isomorphism of complexes
`sheafify (forget K) ≅ K`. This is the sheaf-side input to
`homologyIsoSheafify`: a sheaf complex is recovered (up to canonical iso) by
sheafifying its underlying presheaf complex.

Project-local: assembled from `Mathlib`'s `IsIso (sheafificationAdjunction α).counit`
via `isoOfComponents`. -/
noncomputable def counitComplexIso (K : HomologicalComplex (SheafOfModules.{v} R) cc) :
    ((PresheafOfModules.sheafification α).mapHomologicalComplex cc).obj
        (((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α).mapHomologicalComplex
          cc).obj K) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (asIso (sheafificationAdjunction α).counit).app (K.X n))
    (fun n m _ => ((sheafificationAdjunction α).counit.naturality (K.d n m)).symm)

/-- **Engine for Stacks 01XJ.** Homology of a complex of sheaves of modules is the
sheafification of the objectwise (presheaf-level) homology of its underlying
presheaf complex:
`K.homology i ≅ (sheafification α).obj ((forget K).homology i)`.

The proof transports homology across the counit isomorphism `sheafify (forget K) ≅ K`
of `counitComplexIso` and then uses that `sheafification α` preserves homology
(it is exact: preserves finite limits and, as a left adjoint, finite colimits),
via `Functor.mapHomologyIso'`.

Project-local: `Mathlib` has the exactness ingredients but not this packaged
"cohomology sheaf = sheafify of objectwise cohomology" comparison. -/
noncomputable def homologyIsoSheafify (K : HomologicalComplex (SheafOfModules.{v} R) cc)
    (i : ιc) :
    K.homology i ≅ (PresheafOfModules.sheafification α).obj
      ((((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α).mapHomologicalComplex
        cc).obj K).homology i) :=
  (HomologicalComplex.homologyFunctor _ cc i).mapIso (counitComplexIso α cc K).symm ≪≫
    (PresheafOfModules.sheafification α).mapHomologyIso' cc
      (((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α).mapHomologicalComplex
        cc).obj K) i

end PresheafOfModules

/-! ## Project-local Mathlib supplement — `Rⁿ f_*` as a sheafified presheaf homology -/

namespace AlgebraicGeometry

variable {S X : Scheme.{u}}

/-- The underlying presheaf-of-modules complex of the pushed-forward injective
resolution `f_* I^•`, whose `n`-th objectwise homology is the cohomology presheaf
`V ↦ Hⁿ(f⁻¹(V), G)` (with the implicit choice of injective resolution `I`).

Project-local: the presheaf whose sheafification is `Rⁿ f_* G`. -/
noncomputable def pushforwardResolutionPresheafComplex
    [HasInjectiveResolutions X.Modules] (f : X ⟶ S) {G : X.Modules}
    (I : InjectiveResolution G) :
    HomologicalComplex (PresheafOfModules S.ringCatSheaf.obj) (ComplexShape.up ℕ) :=
  ((SheafOfModules.forget S.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 S.ringCatSheaf.obj)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
    (((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)

/-- **Stacks 01XJ, resolution form.** For any chosen injective resolution
`I : InjectiveResolution G`, the `n`-th higher direct image `Rⁿ f_* G` is the
sheafification of the presheaf-level homology of the pushed-forward resolution
`f_* I^•`. Concretely, `Rⁿ f_* G ≅ sheafify(V ↦ Hⁿ((f_* I^•)(V)))`, and the
presheaf `V ↦ Hⁿ((f_* I^•)(V)) = Hⁿ(I^•(f⁻¹ V))` is the cohomology presheaf
`V ↦ Hⁿ(f⁻¹(V), G)` of the blueprint statement.

The proof composes `InjectiveResolution.isoRightDerivedObj` (computing the right
derived functor `Rⁿ f_* = (f_*).rightDerived n` via the resolution) with the
sheafification engine `PresheafOfModules.homologyIsoSheafify`.

Project-local: the resolution-dependent form of `lem:higher_direct_image_presheaf`;
the identification of the displayed presheaf with the absolute cohomology presheaf
`V ↦ Hⁿ(f⁻¹(V), G)` is the remaining hand-off step. -/
noncomputable def higherDirectImage_iso_sheafify_presheafHomology
    [HasInjectiveResolutions X.Modules] (f : X ⟶ S) (n : ℕ) {G : X.Modules}
    (I : InjectiveResolution G) :
    higherDirectImage f n G ≅
      (PresheafOfModules.sheafification (𝟙 S.ringCatSheaf.obj)).obj
        ((pushforwardResolutionPresheafComplex f I).homology n) :=
  I.isoRightDerivedObj (Scheme.Modules.pushforward f) n ≪≫
    PresheafOfModules.homologyIsoSheafify (𝟙 S.ringCatSheaf.obj) (ComplexShape.up ℕ)
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex) n

end AlgebraicGeometry
