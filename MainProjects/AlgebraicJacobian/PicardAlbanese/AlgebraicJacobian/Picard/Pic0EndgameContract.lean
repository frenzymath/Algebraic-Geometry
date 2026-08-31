/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAffChallenge
import AlgebraicJacobian.Picard.Pic0AtlasFromDivRep

/-!
# Category-correct ambient contract for the rank-one Picard route

The rank-one locus lives in degree `genus C`, not in `pic0`. This module installs the concrete
ambient maps that the later open-locus restriction must consume:

* `abelDivAffTrans` maps the widened degree-`n` divisor functor to `picDegLayerFunctor C n`;
* `abelDivAffSigma` extends a represented slice map to the ambient big-site presheaf;
* `abelDivAffGenusSigma` specializes the map using the canonical genus representation.

The future public `PicRankOneOpen` must therefore be a subfunctor of
`picDegLayerFunctor C (genus C)`, and `DivRankOneOpen` must be an open of
`divRepAffGenusScheme C`. Its `rankOneAbel` is the restriction of
`abelDivAffGenusSigma`, after applying the corresponding Sigma extension. No placeholder locus,
inverse, representability witness, or endgame theorem is postulated here.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} {n : ℕ}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

variable (C n) in
/-- The widened Abel transformation into the intrinsic degree-`n` Picard layer. -/
def abelDivAffTrans : divFunctorAff C n ⟶ picDegLayerFunctor C (n : ℤ) where
  app T := ↾fun s => ⟨abelDivAff' C n T.unop s, fun K _ _ t => degAt_abelDivAff' s t⟩
  naturality T T' g := by
    ext s
    refine Subtype.ext ?_
    exact (picEtMap_abelDivAff' g.unop s).symm

@[simp]
lemma abelDivAffTrans_app_coe
    (T : (Over (Spec (.of k)))ᵒᵖ) (s : divFamZarAff C n T.unop) :
    ((abelDivAffTrans C n).app T s).1 = abelDivAff' C n T.unop s :=
  rfl

variable (C n) in
/-- Extend a represented widened Abel map from the slice over `Spec k` to the big site. -/
def abelDivAffSigma {D : Over (Spec (.of k))}
    (rep : (divFunctorAff C n).RepresentableBy D) :
    yoneda.obj D.left ⟶
      Over.sigmaExtension (Spec (.of k)) (picDegLayerFunctor C (n : ℤ)) :=
  rep.toSigmaExtension ≫ Over.sigmaExtensionNat (abelDivAffTrans C n)

@[simp]
lemma abelDivAffSigma_app_fst {D : Over (Spec (.of k))}
    (rep : (divFunctorAff C n).RepresentableBy D) (T : Schemeᵒᵖ)
    (x : T.unop ⟶ D.left) :
    ((abelDivAffSigma C n rep).app T x).1 = x ≫ D.hom :=
  rfl

@[simp]
lemma abelDivAffSigma_app_coe {D : Over (Spec (.of k))}
    (rep : (divFunctorAff C n).RepresentableBy D) (T : Schemeᵒᵖ)
    (x : T.unop ⟶ D.left) :
    ((abelDivAffSigma C n rep).app T x).2.1 =
      abelDivAff' C n (Over.mk (x ≫ D.hom)) (rep.homEquiv (Over.homMk x rfl)) :=
  rfl

variable (C) in
/-- The ambient genus-degree Abel map on the canonical represented widened divisor scheme.

This is the map that the future rank-one divisor open must restrict. It is not itself claimed to
be an open immersion. -/
def abelDivAffGenusSigma :
    yoneda.obj (divRepAffGenusScheme C).left ⟶
      Over.sigmaExtension (Spec (.of k)) (picDegLayerFunctor C (genus C : ℤ)) :=
  abelDivAffSigma C (genus C) (divFunctorAff_genus_representableBy C)

end

end AlgebraicGeometry
