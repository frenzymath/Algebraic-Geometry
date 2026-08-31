/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RepresentabilityOverlap
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Chosen tensor pullbacks for Picard representability descent

This module realizes the double and triple Amitsur overlaps of a field extension
as the chosen pullbacks used by `Pseudofunctor.DescentData'`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- The tensor-product overlap is the fiber product of `Spec L` with itself over
`Spec k`. -/
lemma tensorOverlap_isPullback : IsPullback
    (tensorOverlapInl (k := k) (L := L))
    (tensorOverlapInr (k := k) (L := L))
    (tensorOverlapBase (k := k) (L := L))
    (tensorOverlapBase (k := k) (L := L)) := by
  unfold tensorOverlapInl tensorOverlapInr tensorOverlapBase
  rw [show (tensorInl (k := k) (A := k) (B := L)).toRingHom =
        Algebra.TensorProduct.includeLeftRingHom by rfl]
  rw [show (tensorInr (k := k) (A := k) (B := L)).toRingHom =
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := L)).toRingHom by rfl]
  exact isPullback_SpecMap_of_isPushout
    (CommRingCat.ofHom (algebraMap k L))
    (CommRingCat.ofHom (algebraMap k L))
    (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := L) (B := L)))
    (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := L)).toRingHom)
    (CommRingCat.isPushout_tensorProduct k L L)

/-- The concrete tensor-product overlap, chosen as the pullback used by descent data. -/
noncomputable def tensorOverlapChosenPullback :
    ChosenPullback
      (tensorOverlapBase (k := k) (L := L))
      (tensorOverlapBase (k := k) (L := L)) where
  pullback := Spec (.of (L ⊗[k] L))
  p₁ := tensorOverlapInl (k := k) (L := L)
  p₂ := tensorOverlapInr (k := k) (L := L)
  condition := tensorOverlapInl_comp_base (k := k) (L := L)
  isLimit := (tensorOverlap_isPullback (k := k) (L := L)).isLimit

/-- The ring square whose dual is the pullback defining the triple overlap. -/
noncomputable def tensorTriple_isPushout :
    IsPushout
      (CommRingCat.ofHom
        (tensorInr (k := k) (A := k) (B := L)).toRingHom)
      (CommRingCat.ofHom
        (tensorInl (k := k) (A := k) (B := L)).toRingHom)
      (CommRingCat.ofHom (Module.descentFace₁₂ k L).toRingHom)
      (CommRingCat.ofHom (Module.descentFace₂₃ k L).toRingHom) := by
  let b : CommRingCat.of k ⟶ CommRingCat.of L :=
    CommRingCat.ofHom (algebraMap k L)
  let i₁ : CommRingCat.of L ⟶ CommRingCat.of (L ⊗[k] L) :=
    CommRingCat.ofHom (tensorInl (k := k) (A := k) (B := L)).toRingHom
  let i₂ : CommRingCat.of L ⟶ CommRingCat.of (L ⊗[k] L) :=
    CommRingCat.ofHom (tensorInr (k := k) (A := k) (B := L)).toRingHom
  let f₁₂ : CommRingCat.of (L ⊗[k] L) ⟶
      CommRingCat.of (L ⊗[k] (L ⊗[k] L)) :=
    CommRingCat.ofHom (Module.descentFace₁₂ k L).toRingHom
  let f₂₃ : CommRingCat.of (L ⊗[k] L) ⟶
      CommRingCat.of (L ⊗[k] (L ⊗[k] L)) :=
    CommRingCat.ofHom (Module.descentFace₂₃ k L).toRingHom
  change IsPushout i₂ i₁ f₁₂ f₂₃
  have htop : IsPushout b b i₁ i₂ := by
    dsimp only [b, i₁, i₂]
    rw [show (tensorInl (k := k) (A := k) (B := L)).toRingHom =
          Algebra.TensorProduct.includeLeftRingHom by rfl]
    rw [show (tensorInr (k := k) (A := k) (B := L)).toRingHom =
          (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := L)).toRingHom by rfl]
    exact CommRingCat.isPushout_tensorProduct k L L
  have hBase : b ≫ i₁ =
      CommRingCat.ofHom (algebraMap k (L ⊗[k] L)) := by
    ext x
    simp [b, i₁, tensorInl]
  have hCoord1 : i₁ ≫ f₁₂ =
      CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom
          (R := k) (A := L) (B := L ⊗[k] L)) := by
    ext x
    simp [i₁, f₁₂, tensorInl, Algebra.TensorProduct.one_def]
  have hFace23 : f₂₃ =
      CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight
          (R := k) (A := L) (B := L ⊗[k] L)).toRingHom := by
    rfl
  have houter : IsPushout b (b ≫ i₁) (i₁ ≫ f₁₂) f₂₃ := by
    rw [hBase, hCoord1, hFace23]
    dsimp only [b]
    exact CommRingCat.isPushout_tensorProduct k L (L ⊗[k] L)
  exact houter.of_top (by
    dsimp only [i₁, i₂, f₁₂, f₂₃]
    ext x
    simp [tensorInl, tensorInr]) htop

/-- The two adjacent faces exhibit the triple tensor product as the pullback of
the right and left overlap projections. -/
lemma tensorTriple_isPullback : IsPullback
    (tensorTripleFace12 (k := k) (L := L))
    (tensorTripleFace23 (k := k) (L := L))
    (tensorOverlapInr (k := k) (L := L))
    (tensorOverlapInl (k := k) (L := L)) := by
  unfold tensorTripleFace12 tensorTripleFace23 tensorOverlapInr tensorOverlapInl
  exact isPullback_SpecMap_of_isPushout
    (CommRingCat.ofHom
      (tensorInr (k := k) (A := k) (B := L)).toRingHom)
    (CommRingCat.ofHom
      (tensorInl (k := k) (A := k) (B := L)).toRingHom)
    (CommRingCat.ofHom (Module.descentFace₁₂ k L).toRingHom)
    (CommRingCat.ofHom (Module.descentFace₂₃ k L).toRingHom)
    (tensorTriple_isPushout (k := k) (L := L))

/-- The concrete triple tensor product as the pullback of two adjacent double
overlaps. -/
noncomputable def tensorTripleChosenPullback :
    ChosenPullback
      (tensorOverlapChosenPullback (k := k) (L := L)).p₂
      (tensorOverlapChosenPullback (k := k) (L := L)).p₁ where
  pullback := Spec (.of (L ⊗[k] (L ⊗[k] L)))
  p₁ := tensorTripleFace12 (k := k) (L := L)
  p₂ := tensorTripleFace23 (k := k) (L := L)
  condition := by
    simpa only [tensorOverlapChosenPullback, tensorTripleCoord2] using
      tensorTripleCoord2_eq_face23_inl (k := k) (L := L)
  isLimit := (tensorTriple_isPullback (k := k) (L := L)).isLimit
  p := tensorTripleCoord2 (k := k) (L := L)
  hp₁ := rfl

/-- The chosen threefold pullback whose three pairwise projections are the
`12`, `23`, and `13` Amitsur faces. -/
noncomputable def tensorOverlapChosenPullback₃ :
    ChosenPullback₃
      (tensorOverlapChosenPullback (k := k) (L := L))
      (tensorOverlapChosenPullback (k := k) (L := L))
      (tensorOverlapChosenPullback (k := k) (L := L)) where
  chosenPullback := tensorTripleChosenPullback (k := k) (L := L)
  p := tensorTripleBase (k := k) (L := L)
  p₁ := tensorTripleCoord1 (k := k) (L := L)
  p₃ := tensorTripleCoord3 (k := k) (L := L)
  l :=
    { f := tensorTripleFace13 (k := k) (L := L)
      f_p₁ := tensorTripleFace13_inl (k := k) (L := L)
      f_p₂ := tensorTripleFace13_inr (k := k) (L := L)
      f_p := by
        dsimp only [tensorOverlapChosenPullback, ChosenPullback.p]
        exact (congrArg
          (fun q => q ≫ tensorOverlapBase (k := k) (L := L))
          (tensorTripleFace13_inl (k := k) (L := L))).trans
            (tensorTripleCoord1_comp_base (k := k) (L := L)) }
  hp₁ := rfl
  hp₃ := (tensorTripleCoord3_eq_face23_inr (k := k) (L := L)).symm

end AlgebraicGeometry
