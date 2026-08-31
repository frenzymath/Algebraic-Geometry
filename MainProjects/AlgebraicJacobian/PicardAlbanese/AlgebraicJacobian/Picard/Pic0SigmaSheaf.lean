/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtCoverBridge
import AlgebraicJacobian.Picard.OverSigmaExtension
import Mathlib.AlgebraicGeometry.Sites.Representability

/-!
# The big-site Zariski sheaf `pic⁰` and the 01JJ seam (DAT-6, stage 3)

The slice trick assembled: the Σ-extension of the degree-zero Picard functor is an
honest sheaf for the big Zariski topology on `Scheme`, and mathlib's 01JJ
local-representability engine applied to it descends to a representation of the
degree-zero Picard functor itself on the slice.

* `AlgebraicGeometry.pic0TypeFunctor C`: the degree-zero Picard functor with values in
  types — the `forget₂ ⋙ forget` massage of `pic0Functor`, owned here once
  (`pic0TypeFunctor_obj`/`pic0TypeFunctor_map_apply` are `rfl`).
* `AlgebraicGeometry.pic0SigmaFunctor C : Scheme.{u}ᵒᵖ ⥤ Type u`: the Σ-extension
  `T ↦ Σ (a : T ⟶ Spec k), pic⁰(Over.mk a)` — the big-site carrier.
* `AlgebraicGeometry.pic0SigmaFunctor_isSheaf` / **`pic0SigmaSheaf C`**: the sheaf
  certificate.  By mathlib's own reduction the big-site sheaf condition collapses to
  elementwise ∃!-amalgamation on honest open covers
  (`Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange`,
  `exists_cover_of_mem_pretopology`, `Presieve.isSheafFor_arrows_iff` — the
  `BigZariski` TODO is never touched): the Σ-components glue by
  `Scheme.Cover.glueMorphisms`, the fibre components glue by the DAT-6 stage-1
  evaluation bridge (`pic0Subgroup_existsUnique_of_cover`), and the two layers are
  stitched by the stage-2 amalgamation seam (`sigmaExtension_map_mk_eq_iff`) and
  compatibility descent (`map_eq_of_sigmaExtension_map_eq`).
* `AlgebraicGeometry.pic0RepresentableByOfCharts`: **the DAT-glue seam** — given a
  chart family of relatively representable open immersions into `pic0SigmaSheaf`
  (DAT-C) that is jointly locally surjective (DAT-B), mathlib's
  `Scheme.LocalRepresentability.representableBy` produces a representation of the
  Σ-extension by the glued scheme, and the stage-2 Σ-descent `overSlice` turns it
  into a representation of `pic0TypeFunctor C` by the glued scheme over the
  Σ-component of the universal element.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

/-! ## The type-valued degree-zero Picard functor -/

/-- The degree-zero Picard functor with values in types: the `forget₂ ⋙ forget`
massage of `pic0Functor`, owned here once for the Σ-extension statements. -/
noncomputable abbrev pic0TypeFunctor : (Over (Spec (.of k)))ᵒᵖ ⥤ Type u :=
  (pic0Functor C ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat

@[simp]
lemma pic0TypeFunctor_obj (T : (Over (Spec (.of k)))ᵒᵖ) :
    (pic0TypeFunctor C).obj T = pic0Subgroup C T.unop :=
  rfl

lemma pic0TypeFunctor_map_apply {T T' : (Over (Spec (.of k)))ᵒᵖ} (g : T ⟶ T')
    (lam : pic0Subgroup C T.unop) :
    (pic0TypeFunctor C).map g lam = pic0Map C g.unop lam :=
  rfl

/-! ## The Σ-extension as a presheaf on the big site -/

/-- **The big-site carrier of the slice trick**: the Σ-extension of the type-valued
degree-zero Picard functor, `T ↦ Σ (a : T ⟶ Spec k), pic⁰(Over.mk a)`.  Reducible so
that the stage-2 `sigmaExtension` calculus applies syntactically. -/
noncomputable abbrev pic0SigmaFunctor : Scheme.{u}ᵒᵖ ⥤ Type u :=
  Over.sigmaExtension (Spec (.of k)) (pic0TypeFunctor C)

variable [GeometricallyReduced C.hom]

set_option maxHeartbeats 800000 in
-- The amalgamation seams unify the `forget₂ ⋙ forget` massage of `pic0Functor`
-- against the Σ-extension calculus by unfolding; within the DAT-2/PicEtMap 1600000
-- precedent.
/-- **The big-site Zariski sheaf certificate of the Σ-extension** (DAT-6 keystone,
worksheet §1.2 site gap 1): mathlib's reduction collapses the sheaf condition to
elementwise ∃!-amalgamation on honest open covers, where the Σ-components glue by
`Scheme.Cover.glueMorphisms` and the fibre components by the stage-1 evaluation
bridge. -/
theorem pic0SigmaFunctor_isSheaf :
    Presieve.IsSheaf Scheme.zariskiTopology (pic0SigmaFunctor C) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro Y S hS
  obtain ⟨𝓤, rfl⟩ := Scheme.exists_cover_of_mem_pretopology hS
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  -- glue the Σ-components along the scheme-level cover
  have hpair : ∀ i j, pullback.fst (𝓤.f i) (𝓤.f j) ≫ (x i).1
      = pullback.snd (𝓤.f i) (𝓤.f j) ≫ (x j).1 := fun i j =>
    congrArg Sigma.fst
      (hx i j (pullback (𝓤.f i) (𝓤.f j)) (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition)
  obtain ⟨aY, ha⟩ : ∃ aY : Y ⟶ Spec (.of k), ∀ i, 𝓤.f i ≫ aY = (x i).1 :=
    ⟨𝓤.glueMorphisms (fun i => (x i).1) hpair,
      fun i => 𝓤.ι_glueMorphisms (fun i => (x i).1) hpair i⟩
  -- the induced slice cover of `Over.mk aY` and its member sections
  haveI hop : ∀ i, IsOpenImmersion
      ((Over.homMk (𝓤.f i) (ha i) : Over.mk ((x i).1) ⟶ Over.mk aY)).left :=
    fun i => 𝓤.map_prop i
  have hcov : ∀ p : (Over.mk aY).left, ∃ i, p ∈ Scheme.Hom.opensRange
      ((Over.homMk (𝓤.f i) (ha i) : Over.mk ((x i).1) ⟶ Over.mk aY)).left := by
    intro p
    obtain ⟨i, y, hy⟩ := 𝓤.exists_eq p
    exact ⟨i, y, hy⟩
  -- the fibre components are a compatible family on the slice cover
  have hcompat : ∀ (i j : 𝓤.I₀) (Z : Over (Spec (.of k)))
      (gi : Z ⟶ Over.mk ((x i).1)) (gj : Z ⟶ Over.mk ((x j).1)),
      gi ≫ (Over.homMk (𝓤.f i) (ha i) : Over.mk ((x i).1) ⟶ Over.mk aY)
          = gj ≫ (Over.homMk (𝓤.f j) (ha j) : Over.mk ((x j).1) ⟶ Over.mk aY) →
      pic0Map C gi ((x i).2) = pic0Map C gj ((x j).2) := by
    intro i j Z gi gj hg
    have hleft : gi.left ≫ 𝓤.f i = gj.left ≫ 𝓤.f j := congrArg Over.Hom.left hg
    have hdesc := Over.map_eq_of_sigmaExtension_map_eq gi gj
      (hx i j Z.left gi.left gj.left hleft)
    rwa [pic0TypeFunctor_map_apply, pic0TypeFunctor_map_apply] at hdesc
  -- glue the fibre components by the stage-1 evaluation bridge
  obtain ⟨s, hs, hsu⟩ := pic0Subgroup_existsUnique_of_cover
    (fun i => (Over.homMk (𝓤.f i) (ha i) : Over.mk ((x i).1) ⟶ Over.mk aY))
    hcov (fun i => (x i).2) hcompat
  refine ⟨⟨aY, s⟩, fun i => ?_, ?_⟩
  · -- the glued Σ-element restricts to the members
    refine (Over.sigmaExtension_map_mk_eq_iff (𝓤.f i) (ha i) s ((x i).2)).mpr ?_
    rw [pic0TypeFunctor_map_apply]
    exact hs i
  · -- uniqueness: Σ-components by `hom_ext`, fibres by bridge separation
    rintro ⟨a', s'⟩ ht'
    obtain rfl : aY = a' := 𝓤.hom_ext aY a' fun i =>
      (ha i).trans (congrArg Sigma.fst (ht' i) : 𝓤.f i ≫ a' = (x i).1).symm
    refine congrArg (Sigma.mk aY) (hsu s' fun i => ?_)
    have hmem := (Over.sigmaExtension_map_mk_eq_iff (𝓤.f i) (ha i) s' ((x i).2)).mp
      (ht' i)
    rwa [pic0TypeFunctor_map_apply] at hmem

/-- **The Σ-extension of the degree-zero Picard functor, bundled as a sheaf on the
big Zariski site** — the object mathlib's 01JJ local-representability engine
consumes. -/
noncomputable def pic0SigmaSheaf : Sheaf Scheme.zariskiTopology.{u} (Type u) :=
  ⟨pic0SigmaFunctor C,
    (isSheaf_iff_isSheaf_of_type _ _).mpr (pic0SigmaFunctor_isSheaf C)⟩

/-! ## The DAT-glue seam -/

/-- **The DAT-glue statement (worksheet §4, DAT-glue row)**: a chart family of
relatively representable open immersions into the Σ-extension sheaf (DAT-C's
certificates) that is jointly Zariski-locally surjective (DAT-B's coverage) induces —
through mathlib's 01JJ engine and the stage-2 Σ-descent — a representation of the
type-valued degree-zero Picard functor by the glued scheme placed over the
Σ-component of the universal element.  The represented object's `.left` is
`(Scheme.LocalRepresentability.glueData hf).glued` and its `.hom` is the universal
element's Σ-component, both definitionally. -/
noncomputable def pic0RepresentableByOfCharts
    {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (hf : ∀ i, IsOpenImmersion.presheaf (f i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)] :
    (pic0TypeFunctor C).RepresentableBy
      (Over.mk ((Scheme.LocalRepresentability.representableBy hf).homEquiv
        (𝟙 (Scheme.LocalRepresentability.glueData hf).glued)).1) :=
  (Scheme.LocalRepresentability.representableBy hf).overSlice

end AlgebraicGeometry
