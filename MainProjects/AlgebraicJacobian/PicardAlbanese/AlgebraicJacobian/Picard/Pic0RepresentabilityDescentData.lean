/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.DescentDataNormalization
import AlgebraicJacobian.Descent.OverPullbackPseudofunctor
import AlgebraicJacobian.Picard.Pic0RepresentabilityPullbacks

/-!
# Picard representability as scheme descent data

This module packages the canonical tensor-overlap isomorphism of a local Picard
representative as honest descent data for the pullback pseudofunctor of schemes.
-/

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Pseudofunctor

open LocallyDiscreteOpToCat

/-- For the pullback pseudofunctor of over categories, `pullHom` is the literal
three-factor pullback comparison. -/
lemma pullHom_eq_pullbackFaceIsoOfEq_hom
    {D : Type u} [Category.{v, u} D] [HasPullbacks D]
    {V W X : D} (r₀ r₁ : V ⟶ X) (q : V ⟶ W) (p₀ p₁ : W ⟶ X)
    (J : Over X) (h₀ : r₀ = q ≫ p₀) (h₁ : r₁ = q ≫ p₁)
    (i : (Over.pullback p₀).obj J ≅ (Over.pullback p₁).obj J) :
    pullHom (F := Over.pullbackPseudofunctor (C := D)) i.hom q r₀ r₁ h₀.symm h₁.symm =
      (Functor.RepresentableBy.Over.pullbackFaceIsoOfEq
        r₀ r₁ q p₀ p₁ h₀ h₁ i).hom := by
  subst r₀
  subst r₁
  rfl

end CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {J : Over (Spec (.of L))}

/-- The singleton family consisting of the finite field-extension cover. -/
noncomputable abbrev pic0DescentCoverObj (_ : Unit) : Scheme.{u} := Spec (.of L)

/-- The structure map of the singleton field-extension cover. -/
noncomputable abbrev pic0DescentCoverMap (i : Unit) :
    pic0DescentCoverObj (L := L) i ⟶ Spec (.of k) :=
  tensorOverlapBase (k := k) (L := L)

/-- The chosen double overlap for the singleton field-extension cover. -/
noncomputable def pic0DescentPullback :
    (i j : Unit) → ChosenPullback
      (pic0DescentCoverMap (k := k) (L := L) i)
      (pic0DescentCoverMap (k := k) (L := L) j)
  | (), () => tensorOverlapChosenPullback (k := k) (L := L)

/-- The chosen triple overlap for the singleton field-extension cover. -/
noncomputable def pic0DescentPullback₃ :
    (i₁ i₂ i₃ : Unit) → ChosenPullback₃
      (pic0DescentPullback (k := k) (L := L) i₁ i₂)
      (pic0DescentPullback (k := k) (L := L) i₂ i₃)
      (pic0DescentPullback (k := k) (L := L) i₁ i₃)
  | (), (), () => tensorOverlapChosenPullback₃ (k := k) (L := L)

@[simp]
lemma pic0DescentPullback_p₁ (i j : Unit) :
    (pic0DescentPullback (k := k) (L := L) i j).p₁ =
      tensorOverlapInl (k := k) (L := L) := rfl

@[simp]
lemma pic0DescentPullback_p₂ (i j : Unit) :
    (pic0DescentPullback (k := k) (L := L) i j).p₂ =
      tensorOverlapInr (k := k) (L := L) := rfl

@[simp]
lemma pic0DescentPullback₃_p₁₂ (i₁ i₂ i₃ : Unit) :
    (pic0DescentPullback₃ (k := k) (L := L) i₁ i₂ i₃).p₁₂ =
      tensorTripleFace12 (k := k) (L := L) := rfl

@[simp]
lemma pic0DescentPullback₃_p₂₃ (i₁ i₂ i₃ : Unit) :
    (pic0DescentPullback₃ (k := k) (L := L) i₁ i₂ i₃).p₂₃ =
      tensorTripleFace23 (k := k) (L := L) := rfl

@[simp]
lemma pic0DescentPullback₃_p₁₃ (i₁ i₂ i₃ : Unit) :
    (pic0DescentPullback₃ (k := k) (L := L) i₁ i₂ i₃).p₁₃ =
      tensorTripleFace13 (k := k) (L := L) := rfl

@[simp]
lemma pic0DescentPullback₃_p₁ (i₁ i₂ i₃ : Unit) :
    (pic0DescentPullback₃ (k := k) (L := L) i₁ i₂ i₃).p₁ =
      tensorTripleCoord1 (k := k) (L := L) := rfl

@[simp]
lemma pic0DescentPullback₃_p₂ (i₁ i₂ i₃ : Unit) :
    (pic0DescentPullback₃ (k := k) (L := L) i₁ i₂ i₃).p₂ =
      tensorTripleCoord2 (k := k) (L := L) := rfl

@[simp]
lemma pic0DescentPullback₃_p₃ (i₁ i₂ i₃ : Unit) :
    (pic0DescentPullback₃ (k := k) (L := L) i₁ i₂ i₃).p₃ =
      tensorTripleCoord3 (k := k) (L := L) := by
  rcases i₁ with ⟨⟩
  rcases i₂ with ⟨⟩
  rcases i₃ with ⟨⟩
  rfl

@[simp]
lemma pic0DescentPullback₃_p (i₁ i₂ i₃ : Unit) :
    (pic0DescentPullback₃ (k := k) (L := L) i₁ i₂ i₃).p =
      tensorTripleBase (k := k) (L := L) := by
  rcases i₁ with ⟨⟩
  rcases i₂ with ⟨⟩
  rcases i₃ with ⟨⟩
  rfl

/-- The local representative as an object of the pullback pseudofunctor over
the singleton cover. -/
noncomputable def pic0DescentObj (J : Over (Spec (.of L))) (i : Unit) :
    (Over.pullbackPseudofunctor (C := Scheme.{u})).obj
      (.mk (.op (pic0DescentCoverObj (L := L) i))) :=
  Over.pullbackPseudofunctorObj J

/-- The overlap morphism supplied by uniqueness of the two local Picard
representatives. -/
noncomputable def pic0DescentHom
    (rep : (pic0TypeFunctor ((baseChange k L).obj C)).RepresentableBy J) :
    ∀ i j : Unit,
    ((Over.pullbackPseudofunctor (C := Scheme.{u})).map
      (pic0DescentPullback (k := k) (L := L) i j).p₁.op.toLoc).toFunctor.obj
        (pic0DescentObj J i) ⟶
      ((Over.pullbackPseudofunctor (C := Scheme.{u})).map
      (pic0DescentPullback (k := k) (L := L) i j).p₂.op.toLoc).toFunctor.obj
        (pic0DescentObj J j)
  | (), () => (tensorOverlapIso (C := C) rep).hom

/-- The first concrete triple face is the pullback of the double-overlap map. -/
lemma pic0Face12_pullHom
    (rep : (pic0TypeFunctor ((baseChange k L).obj C)).RepresentableBy J) :
    CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := Over.pullbackPseudofunctor (C := Scheme.{u}))
        (tensorOverlapIso (C := C) rep).hom
        (tensorTripleFace12 (k := k) (L := L))
        (tensorTripleCoord1 (k := k) (L := L))
        (tensorTripleCoord2 (k := k) (L := L)) rfl rfl =
      (tensorTripleIso12_face (C := C) rep).hom := by
  have h := Pseudofunctor.pullHom_eq_pullbackFaceIsoOfEq_hom
    (D := Scheme.{u})
    (tensorTripleCoord1 (k := k) (L := L))
    (tensorTripleCoord2 (k := k) (L := L))
    (tensorTripleFace12 (k := k) (L := L))
    (tensorOverlapInl (k := k) (L := L))
    (tensorOverlapInr (k := k) (L := L)) J rfl rfl
    (tensorOverlapIso (C := C) rep)
  exact h

/-- The second concrete triple face is the pullback of the double-overlap map. -/
lemma pic0Face23_pullHom
    (rep : (pic0TypeFunctor ((baseChange k L).obj C)).RepresentableBy J) :
    CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := Over.pullbackPseudofunctor (C := Scheme.{u}))
        (tensorOverlapIso (C := C) rep).hom
        (tensorTripleFace23 (k := k) (L := L))
        (tensorTripleCoord2 (k := k) (L := L))
        (tensorTripleCoord3 (k := k) (L := L))
        (tensorTripleCoord2_eq_face23_inl (k := k) (L := L)).symm
        (tensorTripleCoord3_eq_face23_inr (k := k) (L := L)).symm =
      (tensorTripleIso23_face (C := C) rep).hom := by
  have h := Pseudofunctor.pullHom_eq_pullbackFaceIsoOfEq_hom
    (D := Scheme.{u})
    (tensorTripleCoord2 (k := k) (L := L))
    (tensorTripleCoord3 (k := k) (L := L))
    (tensorTripleFace23 (k := k) (L := L))
    (tensorOverlapInl (k := k) (L := L))
    (tensorOverlapInr (k := k) (L := L)) J
    (tensorTripleCoord2_eq_face23_inl (k := k) (L := L))
    (tensorTripleCoord3_eq_face23_inr (k := k) (L := L))
    (tensorOverlapIso (C := C) rep)
  exact h

/-- The direct concrete triple face is the independently defined `1,3` map. -/
lemma pic0Face13_pullHom
    (rep : (pic0TypeFunctor ((baseChange k L).obj C)).RepresentableBy J) :
    CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := Over.pullbackPseudofunctor (C := Scheme.{u}))
        (tensorOverlapIso (C := C) rep).hom
        (tensorTripleFace13 (k := k) (L := L))
        (tensorTripleCoord1 (k := k) (L := L))
        (tensorTripleCoord3 (k := k) (L := L))
        (tensorTripleFace13_inl (k := k) (L := L))
        (tensorTripleFace13_inr (k := k) (L := L)) =
      (tensorTripleIso13_face (C := C) rep).hom := by
  have h := Pseudofunctor.pullHom_eq_pullbackFaceIsoOfEq_hom
    (D := Scheme.{u})
    (tensorTripleCoord1 (k := k) (L := L))
    (tensorTripleCoord3 (k := k) (L := L))
    (tensorTripleFace13 (k := k) (L := L))
    (tensorOverlapInl (k := k) (L := L))
    (tensorOverlapInr (k := k) (L := L)) J
    (tensorTripleFace13_inl (k := k) (L := L)).symm
    (tensorTripleFace13_inr (k := k) (L := L)).symm
    (tensorOverlapIso (C := C) rep)
  exact h

/-- The `12` pullback appearing in the chosen descent datum is the concrete
tensor-triple face isomorphism. -/
lemma pic0DescentPullHom12
    (rep : (pic0TypeFunctor ((baseChange k L).obj C)).RepresentableBy J) :
    Pseudofunctor.DescentData'.pullHom'
        (F := Over.pullbackPseudofunctor (C := Scheme.{u}))
        (f := pic0DescentCoverMap (k := k) (L := L))
        (sq := pic0DescentPullback (k := k) (L := L))
        (pic0DescentHom (C := C) rep)
        (pic0DescentPullback₃ (k := k) (L := L) () () ()).p
        (pic0DescentPullback₃ (k := k) (L := L) () () ()).p₁
        (pic0DescentPullback₃ (k := k) (L := L) () () ()).p₂
        (by
          rw [pic0DescentPullback₃_p]
          exact tensorTripleCoord1_comp_base) (by
          rw [pic0DescentPullback₃_p]
          exact tensorTripleCoord2_comp_base) =
      (tensorTripleIso12_face (C := C) rep).hom := by
  rw [Pseudofunctor.DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃
    (F := Over.pullbackPseudofunctor (C := Scheme.{u}))
    (sq := pic0DescentPullback (k := k) (L := L))
    (sq₃ := pic0DescentPullback₃ (k := k) (L := L))
    (hom := pic0DescentHom (C := C) rep) () () ()]
  exact pic0Face12_pullHom (C := C) rep

/-- The `23` pullback appearing in the chosen descent datum is the concrete
tensor-triple face isomorphism. -/
lemma pic0DescentPullHom23
    (rep : (pic0TypeFunctor ((baseChange k L).obj C)).RepresentableBy J) :
    Pseudofunctor.DescentData'.pullHom'
        (F := Over.pullbackPseudofunctor (C := Scheme.{u}))
        (f := pic0DescentCoverMap (k := k) (L := L))
        (sq := pic0DescentPullback (k := k) (L := L))
        (pic0DescentHom (C := C) rep)
        (pic0DescentPullback₃ (k := k) (L := L) () () ()).p
        (pic0DescentPullback₃ (k := k) (L := L) () () ()).p₂
        (pic0DescentPullback₃ (k := k) (L := L) () () ()).p₃
        (by
          rw [pic0DescentPullback₃_p]
          exact tensorTripleCoord2_comp_base) (by
          rw [pic0DescentPullback₃_p]
          exact tensorTripleCoord3_comp_base) =
      (tensorTripleIso23_face (C := C) rep).hom := by
  rw [Pseudofunctor.DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃
    (F := Over.pullbackPseudofunctor (C := Scheme.{u}))
    (sq := pic0DescentPullback (k := k) (L := L))
    (sq₃ := pic0DescentPullback₃ (k := k) (L := L))
    (hom := pic0DescentHom (C := C) rep) () () ()]
  exact pic0Face23_pullHom (C := C) rep

/-- The `13` pullback appearing in the chosen descent datum is the concrete
tensor-triple face isomorphism. -/
lemma pic0DescentPullHom13
    (rep : (pic0TypeFunctor ((baseChange k L).obj C)).RepresentableBy J) :
    Pseudofunctor.DescentData'.pullHom'
        (F := Over.pullbackPseudofunctor (C := Scheme.{u}))
        (f := pic0DescentCoverMap (k := k) (L := L))
        (sq := pic0DescentPullback (k := k) (L := L))
        (pic0DescentHom (C := C) rep)
        (pic0DescentPullback₃ (k := k) (L := L) () () ()).p
        (pic0DescentPullback₃ (k := k) (L := L) () () ()).p₁
        (pic0DescentPullback₃ (k := k) (L := L) () () ()).p₃
        (by
          rw [pic0DescentPullback₃_p]
          exact tensorTripleCoord1_comp_base) (by
          rw [pic0DescentPullback₃_p]
          exact tensorTripleCoord3_comp_base) =
      (tensorTripleIso13_face (C := C) rep).hom := by
  rw [Pseudofunctor.DescentData'.pullHom'₁₃_eq_pullHom_of_chosenPullback₃
    (F := Over.pullbackPseudofunctor (C := Scheme.{u}))
    (sq := pic0DescentPullback (k := k) (L := L))
    (sq₃ := pic0DescentPullback₃ (k := k) (L := L))
    (hom := pic0DescentHom (C := C) rep) () () ()]
  exact pic0Face13_pullHom (C := C) rep

/- The singleton index leaves one concrete cocycle equation. Keeping this
equation specialized avoids repeated dependent reduction over `Unit`. -/
lemma pic0DescentHom_comp
    (rep : (pic0TypeFunctor ((baseChange k L).obj C)).RepresentableBy J) :
      Pseudofunctor.DescentData'.pullHom'
          (F := Over.pullbackPseudofunctor (C := Scheme.{u}))
          (f := pic0DescentCoverMap (k := k) (L := L))
          (sq := pic0DescentPullback (k := k) (L := L))
          (pic0DescentHom (C := C) rep)
          (pic0DescentPullback₃ (k := k) (L := L) () () ()).p
          (pic0DescentPullback₃ (k := k) (L := L) () () ()).p₁
          (pic0DescentPullback₃ (k := k) (L := L) () () ()).p₂
          (by
            rw [pic0DescentPullback₃_p]
            exact tensorTripleCoord1_comp_base) (by
            rw [pic0DescentPullback₃_p]
            exact tensorTripleCoord2_comp_base) ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := Over.pullbackPseudofunctor (C := Scheme.{u}))
          (f := pic0DescentCoverMap (k := k) (L := L))
          (sq := pic0DescentPullback (k := k) (L := L))
          (pic0DescentHom (C := C) rep)
          (pic0DescentPullback₃ (k := k) (L := L) () () ()).p
          (pic0DescentPullback₃ (k := k) (L := L) () () ()).p₂
          (pic0DescentPullback₃ (k := k) (L := L) () () ()).p₃
          (by
            rw [pic0DescentPullback₃_p]
            exact tensorTripleCoord2_comp_base) (by
            rw [pic0DescentPullback₃_p]
            exact tensorTripleCoord3_comp_base) =
        Pseudofunctor.DescentData'.pullHom'
          (F := Over.pullbackPseudofunctor (C := Scheme.{u}))
          (f := pic0DescentCoverMap (k := k) (L := L))
          (sq := pic0DescentPullback (k := k) (L := L))
          (pic0DescentHom (C := C) rep)
          (pic0DescentPullback₃ (k := k) (L := L) () () ()).p
          (pic0DescentPullback₃ (k := k) (L := L) () () ()).p₁
          (pic0DescentPullback₃ (k := k) (L := L) () () ()).p₃
          (by
            rw [pic0DescentPullback₃_p]
            exact tensorTripleCoord1_comp_base) (by
            rw [pic0DescentPullback₃_p]
            exact tensorTripleCoord3_comp_base) := by
  rw [pic0DescentPullHom12 (C := C) rep,
    pic0DescentPullHom23 (C := C) rep,
    pic0DescentPullHom13 (C := C) rep]
  change (tensorTripleIso12_face (C := C) rep).hom ≫
      (tensorTripleIso23_face (C := C) rep).hom =
    (tensorTripleIso13_face (C := C) rep).hom
  exact congrArg Iso.hom (tensorTripleIso_face_cocycle (C := C) rep).symm

/-- The tensor-overlap comparison satisfies the chosen-pullback cocycle for
the whole singleton cover family. -/
lemma pic0DescentHom_comp_all
    (rep : (pic0TypeFunctor ((baseChange k L).obj C)).RepresentableBy J) :
    ∀ i₁ i₂ i₃,
      Pseudofunctor.DescentData'.pullHom'
          (F := Over.pullbackPseudofunctor (C := Scheme.{u}))
          (f := pic0DescentCoverMap (k := k) (L := L))
          (sq := pic0DescentPullback (k := k) (L := L))
          (pic0DescentHom (C := C) rep)
          (pic0DescentPullback₃ (k := k) (L := L) i₁ i₂ i₃).p
          (pic0DescentPullback₃ (k := k) (L := L) i₁ i₂ i₃).p₁
          (pic0DescentPullback₃ (k := k) (L := L) i₁ i₂ i₃).p₂
          (by
            rw [pic0DescentPullback₃_p]
            exact tensorTripleCoord1_comp_base) (by
            rw [pic0DescentPullback₃_p]
            exact tensorTripleCoord2_comp_base) ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := Over.pullbackPseudofunctor (C := Scheme.{u}))
          (f := pic0DescentCoverMap (k := k) (L := L))
          (sq := pic0DescentPullback (k := k) (L := L))
          (pic0DescentHom (C := C) rep)
          (pic0DescentPullback₃ (k := k) (L := L) i₁ i₂ i₃).p
          (pic0DescentPullback₃ (k := k) (L := L) i₁ i₂ i₃).p₂
          (pic0DescentPullback₃ (k := k) (L := L) i₁ i₂ i₃).p₃
          (by
            rw [pic0DescentPullback₃_p]
            exact tensorTripleCoord2_comp_base) (by
            rw [pic0DescentPullback₃_p]
            exact tensorTripleCoord3_comp_base) =
        Pseudofunctor.DescentData'.pullHom'
          (F := Over.pullbackPseudofunctor (C := Scheme.{u}))
          (f := pic0DescentCoverMap (k := k) (L := L))
          (sq := pic0DescentPullback (k := k) (L := L))
          (pic0DescentHom (C := C) rep)
          (pic0DescentPullback₃ (k := k) (L := L) i₁ i₂ i₃).p
          (pic0DescentPullback₃ (k := k) (L := L) i₁ i₂ i₃).p₁
          (pic0DescentPullback₃ (k := k) (L := L) i₁ i₂ i₃).p₃
          (by
            rw [pic0DescentPullback₃_p]
            exact tensorTripleCoord1_comp_base) (by
            rw [pic0DescentPullback₃_p]
            exact tensorTripleCoord3_comp_base) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩
  apply eq_of_heq
  exact heq_of_eq (pic0DescentHom_comp (C := C) rep)

/-- Every tensor-overlap comparison morphism is invertible. -/
lemma pic0DescentHom_isIso
    (rep : (pic0TypeFunctor ((baseChange k L).obj C)).RepresentableBy J) :
    ∀ i j, IsIso (pic0DescentHom (C := C) rep i j) := by
  rintro ⟨⟩ ⟨⟩
  change IsIso ((tensorOverlapIso (C := C) rep).hom)
  infer_instance

/-- The canonical Picard representative with its invertible tensor-overlap cocycle. -/
noncomputable def pic0RepresentabilityDescentCocycle
    (rep : (pic0TypeFunctor ((baseChange k L).obj C)).RepresentableBy J) :
    (Over.pullbackPseudofunctor (C := Scheme.{u})).DescentCocycle'
      (pic0DescentPullback (k := k) (L := L))
      (pic0DescentPullback₃ (k := k) (L := L)) where
  obj := pic0DescentObj J
  hom := pic0DescentHom (C := C) rep
  homIso := pic0DescentHom_isIso (C := C) rep
  pullHom'_hom_comp := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    apply eq_of_heq
    exact heq_of_eq (pic0DescentHom_comp (C := C) rep)

/-- The canonical Picard representative with its tensor-overlap descent data. -/
noncomputable def pic0RepresentabilityDescentData
    (rep : (pic0TypeFunctor ((baseChange k L).obj C)).RepresentableBy J) :=
  Pseudofunctor.DescentCocycle'.toDescentData
    (C := Scheme.{u})
    (F := Over.pullbackPseudofunctor (C := Scheme.{u}))
    (ι := Unit)
    (S := Spec (.of k))
    (X := pic0DescentCoverObj (L := L))
    (f := pic0DescentCoverMap (k := k) (L := L))
    (sq := pic0DescentPullback (k := k) (L := L))
    (sq₃ := pic0DescentPullback₃ (k := k) (L := L))
    (pic0RepresentabilityDescentCocycle (C := C) rep)

end AlgebraicGeometry
