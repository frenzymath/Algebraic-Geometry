/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.CechAugmentedResolution
import AlgebraicJacobian.Cohomology.CechTermAcyclic

/-!
# Čech computation of higher direct images — capstone leaf

This file is the downstream leaf hosting the Route-A capstone: the canonical theorem
`cech_computes_higherDirectImage` under the **correct** hypotheses
`[X.IsSeparated]` and `h𝒰 : ∀ i, IsAffine (𝒰.X i)`.

The companion `CechHigherDirectImage.lean` provides the surrounding infrastructure
(`CechNerve`, `CechComplex`, `cechAugmentedComplex`, etc.).  The theorem proved here
is the definitively-stated capstone with the correct separatedness hypotheses.

Blueprint chapter: `blueprint/src/chapters/Cohomology_CechHigherDirectImage.tex`, including
`lem:rightAcyclic_finite_prod`, `lem:cech_term_pushforward_acyclic`,
`lem:pushforward_mapHC_cechComplexOnX`, `lem:cechAugmented_to_acyclicResolutionInput`, and
`lem:cech_computes_cohomology_affineCover`.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.Modules

variable {X S : Scheme.{u}}

/-! ## Pushforward commutes with the Čech complex functor -/

/-- **An additive functor commutes with the alternating coface map complex** (object-level
cosimplicial analogue of `AlgebraicTopology.map_alternatingFaceMapComplex`). The components are
identities: in each degree both complexes have the object `G.obj (Y.obj ⦋p⦌)`, and the
differential of the whiskered complex is `G` applied to the alternating coface differential,
by additivity (`Functor.map_sum`, `Functor.map_zsmul`). Project-local helper. -/
noncomputable def mapAlternatingCofaceMapComplexIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (G : C ⥤ D) [G.Additive] (Y : CosimplicialObject C) :
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((AlgebraicTopology.alternatingCofaceMapComplex C).obj Y) ≅
      (AlgebraicTopology.alternatingCofaceMapComplex D).obj
        (((CosimplicialObject.whiskering C D).obj G).obj Y) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro i j (rfl : i + 1 = j)
    -- (v4.31.0: `dsimp only [AlternatingCofaceMapComplex.obj]` no longer reduces the functor-
    -- wrapped `.obj`, so the old `dsimp; rw [of_d]` broke. Unfold the functor + def + `of_d`
    -- via `simp only`, clear the (defeq-wrapped) identity components with `erw`, then both sides
    -- are the alternating sum `∑ (-1)^k • G.map (Y.δ k)` definitionally — `(whisker G Y).δ` is
    -- `rfl`-equal to `G.map (Y.δ)` — so `rfl` closes it.)
    simp only [Iso.refl_hom, Functor.mapHomologicalComplex_obj_d,
      AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
      AlgebraicTopology.AlternatingCofaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul]
    erw [Category.id_comp, Category.comp_id]
    rfl)

/-- **The `f_*`-image of the un-augmented Čech complex on `X` is isomorphic to the relative Čech
complex** (blueprint `lem:pushforward_mapHC_cechComplexOnX`). -/
noncomputable def pushforward_mapHomologicalComplex_cechComplexOnX
    (f : X ⟶ S) (𝒰 : X.OpenCover) (F : X.Modules) :
    ((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cechComplexOnX 𝒰 F) ≅ CechComplex f 𝒰 F :=
  -- `cechComplexOnX` and `CechComplex` are *definitionally* the alternating coface complexes of
  -- the (un-whiskered, resp. `f_*`-whiskered) underlying cosimplicial object of the Čech nerve,
  -- so the general helper applies on the nose.
  mapAlternatingCofaceMapComplexIso (Scheme.Modules.pushforward f)
    (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F))

/-! ## From augmented exactness to the acyclic-resolution input data -/

/-- **From augmented exactness to the P4 input data**
(blueprint `lem:cechAugmented_to_acyclicResolutionInput`).

Given the hypotheses of `cechAugmented_exact`, this compatibility declaration packages the two
pieces of data that `rightDerivedIsoOfAcyclicResolution` requires:
an isomorphism `e : F ≅ (cechComplexOnX 𝒰 F).cycles 0` identifying `F` with the 0-cocycles,
and exactness `(cechComplexOnX 𝒰 F).ExactAt (n+1)` in every positive degree. -/
noncomputable def cechAugmented_to_acyclicResolutionInput
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (h𝒰 : ∀ i, IsAffine (𝒰.X i)) [X.IsSeparated]
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    (F ≅ (cechComplexOnX 𝒰 F).cycles 0) ×' (∀ n, (cechComplexOnX 𝒰 F).ExactAt (n + 1)) := by
  have hexact : ∀ n, (cechAugmentedComplex 𝒰 F).ExactAt n := fun n =>
    (HomologicalComplex.exactAt_iff_isZero_homology _ n).2
      (cechAugmented_exact 𝒰 h𝒰 F hF n)
  exact ⟨CochainComplex.cyclesZeroIsoOfAugmentExact (cechComplexOnX 𝒰 F)
      (cechAugmentation 𝒰 F) (cechAugmentation_comp_d 𝒰 F) hexact,
    CochainComplex.exactAt_succ_of_augment_exact (cechComplexOnX 𝒰 F)
      (cechAugmentation 𝒰 F) (cechAugmentation_comp_d 𝒰 F) hexact⟩
/-! ## Capstone: Čech computes higher direct images (affine-cover form) -/
/-- **The Čech complex computes the higher direct images** (Stacks Tag 02KE;
blueprint `lem:cech_computes_cohomology`).

Let `f : X ⟶ S` be a separated quasi-compact morphism with `X` and `S` both separated, `F` a
quasi-coherent `O_X`-module, `𝒰` a finite affine open cover of `X` (with all cover opens affine,
`h𝒰 : ∀ i, IsAffine (𝒰.X i)`, so all intersections are affine by `X.IsSeparated`), and `hres`
threading `HasInjectiveResolutions` on each intersection subscheme.  Then for every `i ≥ 0`
there is an isomorphism between the `i`-th cohomology of the relative Čech complex and the `i`-th
higher direct image:
```
  (CechComplex f 𝒰 F).homology i ≅ R^i f_* F  =  higherDirectImage f i F.
```
This is the canonical statement of the Čech-to-derived-pushforward comparison, proved under the
correct hypotheses `[X.IsSeparated] [S.IsSeparated]` and `h𝒰`. -/
theorem cech_computes_higherDirectImage [HasInjectiveResolutions X.Modules]
    (f : X ⟶ S) [QuasiCompact f] [IsSeparated f] [X.IsSeparated] [S.IsSeparated]
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (h𝒰 : ∀ i, IsAffine (𝒰.X i))
    (F : X.Modules) (hF : F.IsQuasicoherent) (i : ℕ)
    (hres : ∀ (n : ℕ) (σ : Fin (n + 1) → 𝒰.I₀),
      HasInjectiveResolutions (Scheme.Opens.toScheme (coverInterOpen 𝒰 σ)).Modules) :
    Nonempty ((CechComplex f 𝒰 F).homology i ≅ higherDirectImage f i F) := by
  have hexact : ∀ n, (cechAugmentedComplex 𝒰 F).ExactAt n := fun n =>
    (HomologicalComplex.exactAt_iff_isZero_homology _ n).2
      (cechAugmented_exact 𝒰 h𝒰 F hF n)
  haveI : ∀ n, (Scheme.Modules.pushforward f).IsRightAcyclic ((cechComplexOnX 𝒰 F).X n) :=
    fun n => cechTerm_pushforward_acyclic f 𝒰 h𝒰 F hF n (hres n)
  haveI : PreservesLimits (Scheme.Modules.pushforward f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits
  exact ⟨(HomologicalComplex.homologyFunctor S.Modules (ComplexShape.up ℕ) i).mapIso
      (pushforward_mapHomologicalComplex_cechComplexOnX f 𝒰 F).symm ≪≫
    ((Scheme.Modules.pushforward f).rightDerivedIsoOfAcyclicAugmentation
      (cechComplexOnX 𝒰 F) F (cechAugmentation 𝒰 F) (cechAugmentation_comp_d 𝒰 F)
      hexact i).symm⟩

end AlgebraicGeometry
