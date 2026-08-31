/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicRepColimitCompat
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# A finitely presented Picard representative preserves filtered base colimits

Representability turns the fixed-base Picard-zero functor into the functor of morphisms to its
representing scheme.  If that scheme is locally of finite presentation, the scheme-theoretic
finite-stage factorization and equality theorems show that this functor preserves the filtered
colimits occurring in `Pic0PreservesFilteredBaseColimit`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- A locally finitely presented scheme representing `pic0TypeFunctor C` discharges the
fixed-base filtered-colimit residual `Pic0PreservesFilteredBaseColimit C`. -/
theorem pic0PreservesFilteredBaseColimit_of_representableBy
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom]
    (J : Over (Spec (.of k))) (rep : (pic0TypeFunctor C).RepresentableBy J)
    [LocallyOfFinitePresentation J.hom] :
    Pic0PreservesFilteredBaseColimit C := by
  intro I _ _ S h_aff hcompact hqs _
  letI : IsConnected I := IsCofiltered.isConnected I
  let D := S ⋙ Over.forget (Spec (.of k))
  let t : D ⟶ (Functor.const I).obj (Spec (.of k)) :=
    { app := fun i => (S.obj i).hom
      naturality := fun {i j} f => by
        change (S.map f).left ≫ (S.obj j).hom = (S.obj i).hom ≫ 𝟙 _
        rw [Category.comp_id]
        exact Over.w (S.map f) }
  let c : Cone D := (Over.forget (Spec (.of k))).mapCone (limit.cone S)
  have hc : IsLimit c :=
    isLimitOfPreserves (Over.forget (Spec (.of k))) (limit.isLimit S)
  letI {i j : I} (f : i ⟶ j) : IsAffineHom (D.map f) := h_aff f
  letI (i : I) : CompactSpace (D.obj i) := hcompact i
  letI (i : I) : QuasiSeparatedSpace (D.obj i) := hqs i
  refine preservesColimit_of_preserves_colimit_cocone
    (K := S.op) (F := pic0TypeFunctor C) (limit.isLimit S).op ?_
  refine Types.FilteredColimit.isColimitOf' (S.op ⋙ pic0TypeFunctor C)
    ((pic0TypeFunctor C).mapCocone (limit.cone S).op) ?_ ?_
  · intro x
    let a : limit S ⟶ J := rep.homEquiv.symm x
    have ha : c.π ≫ t = (Functor.const I).map (a.left ≫ J.hom) := by
      ext i
      change (limit.π S i).left ≫ (S.obj i).hom = a.left ≫ J.hom
      rw [Over.w (limit.π S i), Over.w a]
    obtain ⟨i, g, hg, hgbase⟩ :=
      Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
        D t J.hom c hc a.left ha
    let g' : S.obj i ⟶ J := Over.homMk g hgbase
    refine ⟨op i, rep.homEquiv g', ?_⟩
    change x = (pic0TypeFunctor C).map (limit.π S i).op (rep.homEquiv g')
    rw [← rep.homEquiv_comp]
    rw [show x = rep.homEquiv a from (rep.homEquiv.apply_symm_apply x).symm]
    apply congrArg rep.homEquiv
    apply Over.OverMorphism.ext
    exact hg.symm
  · intro ii x y hxy
    let i := unop ii
    let a : S.obj i ⟶ J := rep.homEquiv.symm x
    let b : S.obj i ⟶ J := rep.homEquiv.symm y
    have ha : t.app i = a.left ≫ J.hom := (Over.w a).symm
    have hb : t.app i = b.left ≫ J.hom := (Over.w b).symm
    have habOver : limit.π S i ≫ a = limit.π S i ≫ b := by
      apply rep.homEquiv.injective
      rw [rep.homEquiv_comp, rep.homEquiv_comp,
        rep.homEquiv.apply_symm_apply, rep.homEquiv.apply_symm_apply]
      exact hxy
    have hab : c.π.app i ≫ a.left = c.π.app i ≫ b.left :=
      congrArg Over.Hom.left habOver
    obtain ⟨j, hji, heq⟩ :=
      Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
        D t J.hom c hc a.left b.left ha hb hab
    refine ⟨op j, hji.op, ?_⟩
    change (pic0TypeFunctor C).map (S.map hji).op x =
      (pic0TypeFunctor C).map (S.map hji).op y
    rw [show x = rep.homEquiv a from (rep.homEquiv.apply_symm_apply x).symm,
      show y = rep.homEquiv b from (rep.homEquiv.apply_symm_apply y).symm,
      ← rep.homEquiv_comp, ← rep.homEquiv_comp]
    apply congrArg rep.homEquiv
    apply Over.OverMorphism.ext
    exact heq

end AlgebraicGeometry
