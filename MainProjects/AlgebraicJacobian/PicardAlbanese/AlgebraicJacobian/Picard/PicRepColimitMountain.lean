/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicRepColimitResidual
import AlgebraicJacobian.Cohomology.SectionsBaseChange

/-!
# DAT-G0 β1 — the δ-scheme colimit `Spec K_s = lim S` and the mountain

This file lands the two DAT-G0 β1 bricks that sit between the δ *field* directed system
(`Picard/PicRepColimitResidual.lean`, commit `ad6cd964f`) and β1-at-`K_s`:

1. **The δ-scheme colimit (S–M, `divRep`-free).**  The concrete cofiltered system
   `S : (FinSubext k K)ᵒᵖ ⥤ Over (Spec k)`, `S.obj (op k'') = overSpec k k''`, whose
   limit is `Spec K = overSpec k K` and whose transition maps are `Spec` of the field
   inclusions.  The honest colimit content is the **ring-level** colimit
   `K = colim k''` (`deltaIsColimit`), built from the landed joint-surjectivity
   `coe_iSup_finSubext`/`iSup_finSubext_eq_top` via `Types.FilteredColimit.isColimitOf'`
   and `forget CommRingCat` reflecting the filtered colimit; `Spec` (a right adjoint)
   turns it into the scheme limit.  The residual's three hypotheses — affine transition
   maps, compact and quasi-separated stages — hold because every stage is `Spec` of a
   field (`instAffineTransition_delta`, `CompactSpace`/`QuasiSeparatedSpace` of `Spec`).

## References

Route pinned in landing notes I-0263 / I-0266 and the `PicRepColimitCompat` module
docstring.  Mathlib avatars (`v4.31.0`): `CommRingCat.forget_preservesFilteredColimits`
(`Algebra/Category/Ring/FilteredColimits.lean:363`),
`CategoryTheory.Limits.Types.FilteredColimit.isColimitOf'`
(`Limits/Types/Filtered.lean:90`), `CommRingCat.preservesColimit_coyoneda_of_finitePresentation`
(`Algebra/Category/Ring/FinitePresentation.lean:144`),
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
(`AlgebraicGeometry/AffineTransitionLimit.lean:1177`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite IntermediateField

namespace AlgebraicGeometry.DatG0

/-! ## The δ ring diagram and its colimit `K = colim k''` -/

section FieldColimit

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- **The δ `CommRingCat` diagram.**  The finite subextensions `k''` of `K`, as commutative
rings, with the field inclusions `k'' ↪ k'''` as transition maps.  Its filtered colimit is
`K` (`deltaIsColimit`): the honest ring-level "`K = colim k''`". -/
noncomputable def deltaRingDiagram : FinSubext k K ⥤ CommRingCat.{u} where
  obj L := CommRingCat.of L.1
  map {L₁ L₂} h := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom h)).toRingHom
  map_id L := by
    apply CommRingCat.hom_ext
    ext x
    simp [IntermediateField.inclusion_self]
  map_comp {L₁ L₂ L₃} f g := by
    apply CommRingCat.hom_ext
    ext x
    simp [IntermediateField.inclusion_inclusion]

/-- **The δ colimit cocone.**  The inclusion cocone from the finite subextensions to the
whole field `K`, with `app k'' = k'' ↪ K`. -/
noncomputable def deltaCocone : Cocone (deltaRingDiagram (k := k) (K := K)) where
  pt := CommRingCat.of K
  ι :=
    { app := fun L => CommRingCat.ofHom (IntermediateField.val L.1).toRingHom
      naturality := fun {L₁ L₂} h => by
        apply CommRingCat.hom_ext
        ext x
        rfl }

/-- **The δ colimit `K = colim k''` (ring level).**  The inclusion cocone `deltaCocone` is a
colimit: `forget CommRingCat` reflects filtered colimits, and on underlying types the cocone
is a filtered colimit by `Types.FilteredColimit.isColimitOf'` — joint surjectivity is the
landed `coe_iSup_finSubext`/`iSup_finSubext_eq_top` (every `x : K` lives at a finite stage),
and the injections are the field inclusions. -/
noncomputable def deltaIsColimit [Algebra.IsAlgebraic k K] :
    IsColimit (deltaCocone (k := k) (K := K)) := by
  haveI : ReflectsColimit (deltaRingDiagram (k := k) (K := K)) (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget CommRingCat.{u})
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    have hx : x ∈ ⋃ L : FinSubext k K, (L.1 : Set K) := by
      rw [← coe_iSup_finSubext, iSup_finSubext_eq_top]; trivial
    obtain ⟨L, hxL⟩ := Set.mem_iUnion.mp hx
    exact ⟨L, ⟨x, hxL⟩, rfl⟩
  · intro L x y hxy
    exact ⟨L, 𝟙 L, by rw [show x = y from Subtype.ext hxy]⟩

end FieldColimit

/-! ## The δ scheme system `S : (FinSubext k K)ᵒᵖ ⥤ Over (Spec k)` -/

section SchemeSystem

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The underlying scheme of `overSpec k A` is affine (it is `Spec A`). -/
instance isAffine_overSpec_left (A : Type u) [CommRing A] [Algebra k A] :
    IsAffine (overSpec k A).left :=
  inferInstanceAs (IsAffine (Spec _))

/-- The δ scheme transition morphism `Spec k''' ⟶ Spec k''` in `Over (Spec k)`, for
`k'' ≤ k'''`: `Spec` of the field inclusion `k'' ↪ k'''`.  Well-defined over `Spec k`
because the inclusion is a `k`-algebra map. -/
noncomputable def deltaSchemeMap {L₁ L₂ : FinSubext k K} (h : L₁.1 ≤ L₂.1) :
    overSpec k L₂.1 ⟶ overSpec k L₁.1 :=
  Over.homMk (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)) (by
    simp only [overSpec_left, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2)

@[simp]
lemma deltaSchemeMap_left {L₁ L₂ : FinSubext k K} (h : L₁.1 ≤ L₂.1) :
    (deltaSchemeMap h).left
      = Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) :=
  rfl

/-- **The δ scheme diagram.**  `S.obj (op k'') = overSpec k k'' = Spec k''` over `Spec k`,
with the transition maps `Spec` of the field inclusions.  Its limit is `Spec K = overSpec k K`
(`deltaSchemeIsLimit`). -/
noncomputable def deltaSchemeDiagram : (FinSubext k K)ᵒᵖ ⥤ Over (Spec (.of k)) where
  obj L := overSpec k (unop L).1
  map {L₁ L₂} h := deltaSchemeMap (leOfHom h.unop)
  map_id L := by
    apply Over.OverMorphism.ext
    simp only [deltaSchemeMap_left, Over.id_left, overSpec_left]
    rw [← Spec.map_id]
    congr 1
  map_comp {L₁ L₂ L₃} f g := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, deltaSchemeMap_left, overSpec_left, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2

@[simp]
lemma deltaSchemeDiagram_map {L₁ L₂ : (FinSubext k K)ᵒᵖ} (h : L₁ ⟶ L₂) :
    deltaSchemeDiagram.map h = deltaSchemeMap (leOfHom h.unop) :=
  rfl

/-- Every δ transition map is affine (`Spec` of a field hom; both source and target are
affine). -/
instance deltaSchemeMap_isAffineHom {L₁ L₂ : FinSubext k K} (h : L₁.1 ≤ L₂.1) :
    IsAffineHom (deltaSchemeMap h).left :=
  isAffineHom_of_isAffine _

/-- Every δ stage is a one-point (hence compact) space: `Spec` of a field. -/
instance deltaSchemeDiagram_compactSpace (L : (FinSubext k K)ᵒᵖ) :
    CompactSpace ((deltaSchemeDiagram.obj L).left) :=
  inferInstanceAs (CompactSpace (Spec _))

/-- Every δ stage is quasi-separated: `Spec` of a field is affine. -/
instance deltaSchemeDiagram_quasiSeparatedSpace (L : (FinSubext k K)ᵒᵖ) :
    QuasiSeparatedSpace ((deltaSchemeDiagram.obj L).left) :=
  inferInstanceAs (QuasiSeparatedSpace (Spec _))

end SchemeSystem

/-! ## The δ scheme limit `Spec K = lim S` -/

section SchemeLimit

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]

/-- `Scheme.Spec` is a right adjoint (`Γ ⊣ Spec`), so it preserves the δ cofiltered limit. -/
noncomputable instance : PreservesLimitsOfShape (FinSubext k K)ᵒᵖ Scheme.Spec.{u} :=
  inferInstance

omit [Algebra.IsAlgebraic k K] in
/-- **The δ bridge (definitional).**  Forgetting the base of the δ *scheme* diagram gives the
δ *ring* diagram, opposite, under `Scheme.Spec`: both send `k'' ↦ Spec k''`. -/
lemma deltaScheme_forget_eq :
    deltaSchemeDiagram (k := k) (K := K) ⋙ Over.forget (Spec (.of k))
      = deltaRingDiagram.op ⋙ Scheme.Spec := rfl

/-- The forgotten δ scheme diagram (`k'' ↦ Spec k''` in `Scheme`) has a limit `Spec K`: it is
`Scheme.Spec` of the δ ring colimit `deltaIsColimit` (opposite), and `Scheme.Spec` (right adjoint
`Γ ⊣ Spec`) preserves limits.  This is the honest `Spec K_s = lim_{k''} Spec k''`. -/
noncomputable instance hasLimit_deltaScheme_forget :
    HasLimit (deltaSchemeDiagram (k := k) (K := K) ⋙ Over.forget (Spec (.of k))) := by
  rw [deltaScheme_forget_eq]
  exact ⟨_, isLimitOfPreserves Scheme.Spec deltaIsColimit.op⟩

/-- **The δ scheme colimit `Spec K = lim S`.**  The δ scheme diagram `S` has a limit — `Spec K`:
`Over.forget (Spec k)` *creates* limits of this (cofiltered ⟹ connected) shape, lifting the
forgotten limit `Spec K = Scheme.Spec (colim_{k''} k'')` (`hasLimit_deltaScheme_forget`) uniquely
to `Over (Spec k)`.  So the δ scheme system `S` is a legal input to the β1 residual
`Pic0PreservesFilteredBaseColimit`, and its limit is `Spec K_s`. -/
noncomputable instance : HasLimit (deltaSchemeDiagram (k := k) (K := K)) := by
  haveI : IsConnected (FinSubext k K)ᵒᵖ := IsCofiltered.isConnected _
  exact hasLimit_of_created (deltaSchemeDiagram (k := k) (K := K)) (Over.forget (Spec (.of k)))

end SchemeLimit

/-! ## The δ system plugs into the β1 residual, and the mountain

`preservesColimit_deltaScheme_of_residual` closes the loop of deliverable 1: the concrete δ
scheme system `deltaSchemeDiagram` (all its residual hypotheses — affine transition maps,
compact and quasi-separated stages, `HasLimit`/`Spec K = lim S` — discharged above) **is a legal
input** to the β1 residual `Pic0PreservesFilteredBaseColimit C`, and feeding it in yields the
concrete β1-at-`K_s` statement:

> `pic0TypeFunctor C` sends `Spec K_s = lim_{k''} Spec k''` to the filtered colimit of its values,
> i.e. `colim_{k''} pic0Subgroup C (Spec k'') → pic0Subgroup C (Spec K_s)` is a bijection.

**The mountain (`Pic0PreservesFilteredBaseColimit C`) is NOT discharged here** — it is the
genuine M–L residual (landing notes I-0263/I-0266), stating that `pic0TypeFunctor C` is *locally
of finite presentation as a functor*.  On affine tests `overSpec k A` it is exactly that
`PicEtAff C A` (hence `pic0Subgroup C (overSpec k A)`) commutes with filtered colimits of the test
algebra `A`, riding **finite presentation of the proper smooth curve `C/k`**: `C.hom` is
`SmoothOfRelativeDimension 1` (hence `LocallyOfFiniteType`/`LocallyOfFinitePresentation`) and
`IsProper` (hence quasi-compact and quasi-separated), so `C.hom` is finitely presented.  The
general (qcqs) case reduces to the affine one by spreading the affine opens and sections of
`S_{K_s} = lim S_{k''}` back to a finite stage.  Named mathlib avatars (`v4.31.0`):
`CommRingCat.preservesColimit_coyoneda_of_finitePresentation`
(`Algebra/Category/Ring/FinitePresentation.lean:144`),
`RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit` (`:81`) /
`exists_comp_map_eq_of_isColimit` (`:45`),
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
(`AlgebraicGeometry/AffineTransitionLimit.lean:1177`),
`Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType` (`:686`),
`Scheme.exists_isAffineOpen_preimage_eq` (`:1058`) / `exists_isOpenCover_and_isAffine` (`:1078`).
-/

section Residual

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable (K : Type u) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]

/-- **The δ system plugs into the β1 residual.**  Given the β1 residual
`Pic0PreservesFilteredBaseColimit C` (the pinned M–L mountain), the concrete δ scheme system
`deltaSchemeDiagram`, with all its residual hypotheses discharged (affine transition maps,
compact and quasi-separated `Spec`-of-field stages, and `HasLimit`/`Spec K = lim S`), yields
β1-at-`K_s`: `pic0TypeFunctor C` preserves the δ colimit
`colim_{k''} pic0(Spec k'') → pic0(Spec K)`.  This is the honest consumption of the δ substrate
by the residual, `divRep`-free. -/
theorem preservesColimit_deltaScheme_of_residual
    (h : Pic0PreservesFilteredBaseColimit C) :
    PreservesColimit (deltaSchemeDiagram (k := k) (K := K)).op (pic0TypeFunctor C) := by
  apply h (deltaSchemeDiagram (k := k) (K := K))
  · intro i j f
    exact deltaSchemeMap_isAffineHom (leOfHom f.unop)
  · intro i
    exact deltaSchemeDiagram_compactSpace i
  · intro i
    exact deltaSchemeDiagram_quasiSeparatedSpace i

end Residual

end AlgebraicGeometry.DatG0
