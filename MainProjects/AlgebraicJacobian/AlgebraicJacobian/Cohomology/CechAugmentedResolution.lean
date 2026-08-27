/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import AlgebraicJacobian.Cohomology.CechHigherDirectImage
import AlgebraicJacobian.Cohomology.CechAcyclic
import AlgebraicJacobian.Cohomology.HigherDirectImagePresheaf
import AlgebraicJacobian.Cohomology.AffineSerreVanishing
import AlgebraicJacobian.Cohomology.QcohTildeSections
import AlgebraicJacobian.Cohomology.CechSectionContractibility
import AlgebraicJacobian.Cohomology.CechSectionIdentification

/-!
# The augmented Čech complex is exact (blueprint `lem:cech_augmented_resolution`)

This file proves that the augmented Čech complex `cechAugmentedComplex 𝒰 F` is exact
(every homology object is the zero object in `X.Modules`) whenever `𝒰` is a finite
affine open cover of `X` with all pairwise intersections affine (ensured by separatedness
of `X`) and `F` is a quasi-coherent `O_X`-module.

The theorem is placed here rather than in `CechHigherDirectImage.lean` to avoid an import
cycle: every ingredient of the sections/sheafification proof route
(`PresheafOfModules.homologyIsoSheafify`, `sectionCech_homology_exact_of_localizationAway`,
`affineCoverSystem`, `qcoh_iso_tilde_sections`) lives in a file that transitively imports
`CechHigherDirectImage.lean`.  Placing `cechAugmented_exact` in this downstream file
(`CechAugmentedResolution.lean`) makes all those ingredients available without a cycle.
The pure-Mathlib site lemmas (`isZero_presheafToSheaf_obj_of_W`,
`isZero_presheafToSheaf_obj_of_W_isZero`, `isZero_presheafToSheaf_obj_of_isLocallyBijective`)
live in `CechHigherDirectImage.lean` and are importable here.

Blueprint: `lem:cech_augmented_resolution`.
Source: Stacks Project, Cohomology of Schemes,
  `lemma-cech-cohomology-quasi-coherent-trivial`.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}}

/-! ## Project-local Mathlib supplement — reflecting `IsZero` through a faithful functor -/

/-- **A faithful functor that preserves zero morphisms reflects the zero object.**
If `F` is faithful and preserves zero morphisms and `F.obj X` is a zero object, then
`X` is a zero object. (Three-line proof off `IsZero.iff_id_eq_zero` +
`Functor.map_injective`; lighter than `reflects_exact_of_faithful`, which needs
`[Abelian]`.) Project-local Mathlib supplement (category theory). -/
lemma isZero_of_faithful_preservesZeroMorphisms
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.Faithful] {Y : C}
    (h : IsZero (F.obj Y)) : IsZero Y := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  apply F.map_injective
  rw [F.map_id, F.map_zero]
  exact h

/-! ## Project-local Mathlib supplement — a null-homotopic identity kills homology -/

/-- **A complex homotopy-equivalent to zero has vanishing homology.**
If the identity of a homological complex `D` is homotopic to the zero map
(`Homotopy (𝟙 D) 0`), then every homology object `D.homology p` is a zero object.
This is the categorical packaging of the contracting-homotopy criterion: the
prepend-`i_fix` homotopy on the section {\v C}ech complex produces exactly such a
`Homotopy (𝟙 D) 0`, and this lemma converts it into the required
`IsZero (D.homology p)`.

The proof is the standard three-lemma combo: homotopy-invariance of the induced
homology map (`Homotopy.homologyMap_eq`), the identity/zero computations
(`homologyMap_id`, `homologyMap_zero`), and the "identity equals zero" criterion for a
zero object (`IsZero.iff_id_eq_zero`).  Project-local Mathlib supplement (homological
algebra); blueprint `lem:cech_augmented_resolution`, formalization mechanism Step 3(d). -/
lemma isZero_homology_of_homotopy_id_zero {C : Type*} [Category C] [Preadditive C]
    {ι : Type*} {c : ComplexShape ι} (D : HomologicalComplex C c) (p : ι)
    [D.HasHomology p] (ho : Homotopy (𝟙 D) 0) : IsZero (D.homology p) := by
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  rw [← HomologicalComplex.homologyMap_id, ho.homologyMap_eq p, HomologicalComplex.homologyMap_zero]

/-- **Transport `IsZero` of homology across a complex iso plus a null-homotopic identity.**
If `D ≅ D'` as homological complexes and the identity of `D'` is homotopic to `0`, then
`D.homology p` is a zero object.  This is the consumer-side glue for the section-{\v C}ech
route: the evaluated augmented {\v C}ech complex `D` is identified with a concrete section
complex `D'` (`cechSection_complex_iso`) which carries a contracting homotopy
(`cechSection_contractible`); this lemma turns that pair into `IsZero (D.homology p)`.
Project-local Mathlib supplement (homological algebra). -/
lemma isZero_homology_of_iso_homotopy_id_zero {C : Type*} [Category C] [Preadditive C]
    [CategoryWithHomology C] {ι : Type*} {c : ComplexShape ι}
    {D D' : HomologicalComplex C c} (e : D ≅ D') (p : ι)
    (ho : Homotopy (𝟙 D') 0) : IsZero (D.homology p) :=
  IsZero.of_iso (isZero_homology_of_homotopy_id_zero D' p ho)
    ((HomologicalComplex.homologyFunctor C c p).mapIso e)

/-! ## Project-local Mathlib supplement — sheafification of a locally-zero presheaf -/

open Opposite in
/-- **The sheafification of a presheaf that is locally a zero object vanishes.**
If for every object `U` of the site there is a covering sieve `S ∈ J U` all of whose
members `g : V ⟶ U` land on an object `V` where `Q.obj (op V)` is a zero object, then
the sheafification of `Q` is the zero object.

This packages the three imported site lemmas
(`isZero_presheafToSheaf_obj_of_isLocallyBijective`) into the "locally zero" form the
{\v C}ech-resolution argument consumes: the presheaf homology `V ↦ Ȟᵖ(V, F)` is a zero
object over every `V` contained in a cover member, and those `V` are a covering basis.
The local injectivity of `0 : Q ⟶ Z` (`Z` the constant zero presheaf) comes from the
hypothesis (each member's section group is a subsingleton); the local surjectivity is
free (the target is a zero object). Project-local Mathlib supplement (site theory). -/
lemma isZero_presheafToSheaf_of_locally_isZero {C : Type u} [Category C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
    (h : ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧
      ∀ ⦃V : C⦄ ⦃g : V ⟶ U⦄, S.arrows g → IsZero (Q.obj (op V))) :
    IsZero ((presheafToSheaf J AddCommGrpCat.{u}).obj Q) := by
  let Z : Cᵒᵖ ⥤ AddCommGrpCat.{u} := (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of PUnit)
  have hZobj : ∀ x : Cᵒᵖ, IsZero (Z.obj x) := by
    intro x
    change IsZero (AddCommGrpCat.of PUnit)
    exact AddCommGrpCat.isZero_of_subsingleton _
  have hZ : IsZero Z := (Functor.isZero_iff Z).mpr hZobj
  haveI hli : Presheaf.IsLocallyInjective J (0 : Q ⟶ Z) := by
    refine ⟨?_⟩
    intro X x y _
    obtain ⟨S, hS, hSzero⟩ := h X.unop
    apply J.superset_covering _ hS
    intro V g hg
    change (ConcreteCategory.hom (Q.map g.op)) x = (ConcreteCategory.hom (Q.map g.op)) y
    haveI := AddCommGrpCat.subsingleton_of_isZero (hSzero hg)
    exact Subsingleton.elim _ _
  haveI hls : Presheaf.IsLocallySurjective J (0 : Q ⟶ Z) := by
    refine ⟨?_⟩
    intro U s
    refine J.superset_covering (fun V g _ => ?_) (J.top_mem U)
    refine ⟨0, ?_⟩
    haveI : Subsingleton (Z.obj (op V)) := AddCommGrpCat.subsingleton_of_isZero (hZobj (op V))
    exact Subsingleton.elim _ _
  exact CategoryTheory.GrothendieckTopology.isZero_presheafToSheaf_obj_of_isLocallyBijective
    J (0 : Q ⟶ Z) hZ

/-- **The evaluated augmented Čech section complex has vanishing homology over any open
contained in a cover member** (blueprint `lem:cechSection_isZero_homology`).

For `V ≤ coverOpen 𝒰 i`, the augmented Čech complex `cechAugmentedComplex 𝒰 F`, pushed
through the forgetful/restrict-scalars adapter and evaluated at `V`, has zero homology in
every degree.  This is the consumer-facing packaging of the Sub-brick A chain: the
evaluated complex is identified with the concrete augmented section Čech complex by
`cechSection_complex_iso` from `CechSectionIdentification.lean`, and
`cechSection_contractible` from `CechSectionContractibility.lean` supplies the prepend-`i`
contracting homotopy when `V ≤ coverOpen 𝒰 i`.  The in-file glue
`isZero_homology_of_iso_homotopy_id_zero` combines the pair. -/
lemma cechSection_isZero_homology (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules)
    (V : TopologicalSpace.Opens X) (i : 𝒰.I₀) (hiV : V ≤ coverOpen 𝒰 i) (p : ℕ) :
    let α : X.ringCatSheaf.obj ⟶ X.ringCatSheaf.obj := 𝟙 X.ringCatSheaf.obj
    let cc := ComplexShape.up ℕ
    let K := cechAugmentedComplex 𝒰 F
    let Kp := ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars α).mapHomologicalComplex cc).obj K
    let GV :=
      PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
      (evaluation (TopologicalSpace.Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)
    IsZero (((GV.mapHomologicalComplex cc).obj Kp).homology p) :=
  isZero_homology_of_iso_homotopy_id_zero (cechSection_complex_iso 𝒰 F V) p
    (cechSection_contractible 𝒰 F V i hiV)

/- Planner strategy:
Route: sections + sheafification (NOT stalks — `SheafOfModules.stalk` is absent from Mathlib).
Step 1: reflect `IsZero (homology p)` through the faithful additive forgetful functor
`SheafOfModules.toSheaf` (it preserves zero morphisms, so it reflects the zero object). Step 2:
the homology SHEAF = sheafification of the PRESHEAF homology, via the project engine
`PresheafOfModules.homologyIsoSheafify` (HigherDirectImagePresheaf.lean). Step 3: the presheaf
homology is `V ↦ Ȟᵖ(V,F)`, locally zero on the affine basis — over each basic affine `D(g) ⊆ Uᵢ`,
`qcoh_iso_tilde_sections` gives `F|_{D(g)} ≅ ~M` and
`sectionCech_homology_exact_of_localizationAway` (CechAcyclic.lean) kills positive-degree homology;
the basic affines are cofinal (`standard_cover_cofinal` / `affineCoverSystem`), so the map
`0 → presheaf-homology` is locally bijective, hence its sheafification (= the homology sheaf) is
zero. The reusable abelian-sheaf site lemmas `isZero_presheafToSheaf_obj_of_W` /`_of_W_isZero`/
`_of_isLocallyBijective` (in CechHigherDirectImage.lean, importable) discharge the site-theory half.
The ONE bridge to build here: connect the module-level `homologyIsoSheafify` to those abelian-sheaf
site lemmas via the sheafification square `toSheaf ∘ sheafification ≅ presheafToSheaf ∘ forget`
(cf. `PresheafOfModules.sheafificationCompToSheaf`, used in AffineSerreVanishing.lean; see
`analogies/tosheaf-epi.md` and the iter-053 mathlib-analogist report on the toSheaf-reflection
bridge). Diamond-prone — work with `.hom` not `.val`, defeq/`change` not `rw`. Step 4: the
degree-0 augmentation node uses the same spanning-family exactness (`exact_of_isLocalized_span` /
`combDifferential_exact`). Blueprint: `lem:cech_augmented_resolution`.
-/

/-- **The augmented Čech complex is a resolution** (Stacks
`lemma-cech-cohomology-quasi-coherent-trivial`; blueprint `lem:cech_augmented_resolution`).

Let `X` be a separated scheme, `𝒰` a finite open cover of `X` all of whose members are
affine (so every finite intersection `U_{i₀} ∩ ⋯ ∩ U_{iₚ}` is affine by separatedness),
and `F` a quasi-coherent `O_X`-module. Then every homology object of the augmented Čech
complex `cechAugmentedComplex 𝒰 F` is zero:
```
  ∀ p, IsZero ((cechAugmentedComplex 𝒰 F).homology p).
```
Equivalently, the {\v C}ech nerve of `𝒰` is a resolution of `F` in `X.Modules`. -/
theorem cechAugmented_exact (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (_h𝒰 : ∀ i, IsAffine (𝒰.X i)) [X.IsSeparated]
    (F : X.Modules) (_hF : F.IsQuasicoherent) :
    ∀ p, IsZero ((cechAugmentedComplex 𝒰 F).homology p) := by
  intro p
  -- Step 1: reflect through the faithful, zero-preserving `toSheaf`.
  apply isZero_of_faithful_preservesZeroMorphisms (SheafOfModules.toSheaf X.ringCatSheaf)
  -- Step 2: transport `IsZero` across `homologyIsoSheafify` and the sheafification square.
  set α : X.ringCatSheaf.obj ⟶ X.ringCatSheaf.obj := 𝟙 X.ringCatSheaf.obj with hα
  set cc := ComplexShape.up ℕ with hcc
  set K := cechAugmentedComplex 𝒰 F with hK
  set P := ((((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars α).mapHomologicalComplex cc).obj K).homology p) with hP
  refine IsZero.of_iso ?_
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso
        (PresheafOfModules.homologyIsoSheafify α cc K p) ≪≫
      (PresheafOfModules.sheafificationCompToSheaf α).app P)
  -- Step 3: the presheaf homology is locally a zero object on the cover-member basis.
  set Q := (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj P with hQ
  apply isZero_presheafToSheaf_of_locally_isZero (Opens.grothendieckTopology X) (Q := Q)
  -- Section-level vanishing on every open `V` contained in a cover member `Uᵢ`:
  -- the restricted cover `{Uₛ ∩ V}` has the member `Uᵢ ∩ V = V`, giving a contracting
  -- (prepend-`i_fix`) homotopy on the augmented section complex over `V`. (F-agnostic.)
  have hSec : ∀ (V : TopologicalSpace.Opens X) (i : 𝒰.I₀),
      V ≤ coverOpen 𝒰 i → IsZero (Q.obj (Opposite.op V)) := by
    intro V i hiV
    -- Evaluate-at-`V` the underlying presheaf complex: this functor is additive and
    -- preserves homology, so `Q.obj (op V) ≅ Hᵖ(Γ(V, K•))` (the section complex homology).
    set GV := PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
      (evaluation (TopologicalSpace.Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V) with hGV
    set Kp := (((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars α).mapHomologicalComplex cc).obj K) with hKp
    refine IsZero.of_iso ?_ (GV.mapHomologyIso' cc Kp p).symm
    -- Remaining: the augmented section complex `Γ(V, cechAugmentedComplex 𝒰 F)` is exact
    -- in degree `p`.  Since `V ≤ coverOpen 𝒰 i`, the restricted cover `{Uₛ ∩ V}` has the
    -- member `coverOpen 𝒰 i ∩ V = V`; prepending that fixed index `i` is a contracting
    -- homotopy `d∘h + h∘d = id` on the section complex (template
    -- `CombinatorialCech.combHomotopy` / the objectwise homotopy of FreePresheafComplex),
    -- so every homology object vanishes.  F-agnostic, cover-agnostic.
    -- Step 3(d): discharged by `cechSection_isZero_homology` above, combining the
    -- identification and contractibility modules via `isZero_homology_of_iso_homotopy_id_zero`.
    exact cechSection_isZero_homology 𝒰 F V i hiV p
  -- Assemble the covering sieve `{g : V ⟶ U | V ≤ some Uᵢ}` of every open `U`.
  intro U
  refine ⟨{ arrows := fun {V} _ => ∃ i, V ≤ coverOpen 𝒰 i,
            downward_closed := fun {V W} g hg h => ?_ }, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hg
    exact ⟨i, le_trans (leOfHom h) hi⟩
  · -- membership in the opens topology: cover `U` pointwise via `⨆ᵢ Uᵢ = ⊤`.
    intro x hx
    have hx' : x ∈ (⨆ i, coverOpen 𝒰 i) := by
      have htop : (⨆ i, coverOpen 𝒰 i) = ⊤ := Scheme.OpenCover.iSup_opensRange 𝒰
      rw [htop]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    exact ⟨U ⊓ coverOpen 𝒰 i, homOfLE inf_le_left, ⟨i, inf_le_right⟩, hx, hi⟩
  · rintro V g ⟨i, hi⟩
    exact hSec V i hi

end AlgebraicGeometry
