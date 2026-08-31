/-
Copyright (c) 2026 The StacksPart08Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart08Lib Contributors
-/

import StacksPart08Lib.MorphismProperties
import StacksPart08Lib.Representability

namespace StacksPart08

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open AlgebraicGeometry

universe u

/-- The presheaves on schemes used as moduli functors. -/
abbrev ModuliPresheaf := Presheaf Scheme

/-- A pairwise, represented-pullback formulation of a diagonal property. -/
def PairwiseDiagonalProperty (P : MorphismProperty Scheme) (F : ModuliPresheaf) : Prop :=
  ∀ ⦃T : Scheme⦄ (g : yoneda.obj T ⟶ F ⨯ F),
    ∃ (U : Scheme) (fst : yoneda.obj U ⟶ F) (snd : U ⟶ T),
      IsPullback fst (yoneda.map snd) (Limits.diag F) g ∧ P snd

/-- The relative morphism property of the diagonal of a moduli presheaf. -/
abbrev RelativeDiagonalProperty (P : MorphismProperty Scheme) (F : ModuliPresheaf) : Prop :=
  RelativeMorphismProperty (C := Scheme) (D := ModuliPresheaf) yoneda P (Limits.diag F)

/-- The pairwise criterion directly supplies the witnesses required by the
relative morphism-property constructor. -/
theorem relativeDiagonalProperty_of_pairwise (P : MorphismProperty Scheme)
    [P.RespectsIso] {F : ModuliPresheaf} (h : PairwiseDiagonalProperty P F) :
    RelativeDiagonalProperty P F := by
  apply MorphismProperty.relative.of_exists
  intro T g
  obtain ⟨U, fst, snd, hsquare, hprop⟩ := h g
  exact ⟨U, fst, snd, hsquare, hprop⟩

/-- A map-pair formulation of the represented diagonal criterion. -/
def PairwiseMapDiagonalProperty (P : MorphismProperty Scheme) (F : ModuliPresheaf) : Prop :=
  ∀ ⦃T : Scheme⦄ (x y : yoneda.obj T ⟶ F),
    ∃ (U : Scheme) (fst : yoneda.obj U ⟶ F) (snd : U ⟶ T),
      IsPullback fst (yoneda.map snd) (Limits.diag F) (Limits.prod.lift x y) ∧ P snd

/-- A map-pair criterion implies the pairwise criterion by expressing a map
to a product as the product lift of its two projections. -/
theorem pairwiseDiagonalProperty_of_pairwiseMap (P : MorphismProperty Scheme)
    {F : ModuliPresheaf} (h : PairwiseMapDiagonalProperty P F) :
    PairwiseDiagonalProperty P F := by
  intro T g
  let x : yoneda.obj T ⟶ F := g ≫ Limits.prod.fst
  let y : yoneda.obj T ⟶ F := g ≫ Limits.prod.snd
  have hg : Limits.prod.lift x y = g := by
    apply Limits.prod.hom_ext
    · dsimp [x]
      rw [Limits.prod.lift_fst]
    · dsimp [y]
      rw [Limits.prod.lift_snd]
  obtain ⟨U, fst, snd, hsquare, hprop⟩ := h x y
  refine ⟨U, fst, snd, ?_, hprop⟩
  rw [← hg]
  exact hsquare

/-- The affine finite-presentation diagonal interface for coherent moduli. -/
abbrev CoherentDiagonalAffineFinitePresentation (Coh : ModuliPresheaf) : Prop :=
  RelativeDiagonalProperty schemeAffineFinitePresentation Coh

theorem coherentDiagonal_affineFinitePresentation_of_pairwise
    {Coh : ModuliPresheaf}
    (h : PairwiseMapDiagonalProperty schemeAffineFinitePresentation Coh) :
    CoherentDiagonalAffineFinitePresentation Coh :=
  relativeDiagonalProperty_of_pairwise _ (pairwiseDiagonalProperty_of_pairwiseMap _ h)

/-- The closed diagonal interface for a Quot-type moduli presheaf. -/
abbrev QuotDiagonalClosed (Q : ModuliPresheaf) : Prop :=
  RelativeDiagonalProperty (@IsClosedImmersion) Q

theorem quotDiagonal_closed_of_pairwise {Q : ModuliPresheaf}
    (h : PairwiseMapDiagonalProperty (@IsClosedImmersion) Q) :
    QuotDiagonalClosed Q :=
  relativeDiagonalProperty_of_pairwise _ (pairwiseDiagonalProperty_of_pairwiseMap _ h)

/-- The closed finite-presentation diagonal interface for a Quot-type moduli
presheaf. -/
abbrev QuotDiagonalClosedFinitePresentation (Q : ModuliPresheaf) : Prop :=
  RelativeDiagonalProperty schemeClosedFinitePresentation Q

theorem quotDiagonal_closedFinitePresentation_of_pairwise {Q : ModuliPresheaf}
    (h : PairwiseMapDiagonalProperty schemeClosedFinitePresentation Q) :
    QuotDiagonalClosedFinitePresentation Q :=
  relativeDiagonalProperty_of_pairwise _ (pairwiseDiagonalProperty_of_pairwiseMap _ h)

end StacksPart08
