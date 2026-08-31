/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.Pic0RankOneTranslatedCover
import AlgebraicJacobian.Curve.SepPointsDense
import AlgebraicJacobian.Tangent.TangentIdentitySection
import AlgebraicJacobian.RiemannRoch.ClosedPoint

/-!
# Rational-point residue bridge for the translated cover

The density oracle used by the translated-cover drop has to record residue degree one at the
chosen points.  This file supplies that arithmetic bridge from the actual section certificate,
rather than adding `residueDeg = 1` as an unrelated existential field.  The relative specialization
is the exact point produced by `Over.rationalPointBaseChange`.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance 10000] relCurve.instOver

/-! ## Sections have residue degree one -/

theorem residueDeg_one_of_section
    {K : Type u} [Field K]
    {X : Over (Spec (CommRingCat.of K))}
    {e : Spec (CommRingCat.of K) ⟶ X.left}
    (he : e ≫ X.hom = 𝟙 (Spec (CommRingCat.of K)))
    {x : X.left}
    (hx : e.base (IsLocalRing.closedPoint K) = x) :
    X.left.residueDeg K x = 1 := by
  letI : Algebra K (X.left.presheaf.stalk x) := stalkAlgebra X.hom x
  have h := bijective_algebraMap_residueField_of_section X he hx
  have hmap :
      algebraMap K (IsLocalRing.ResidueField (X.left.presheaf.stalk x)) =
        X.left.residueOverAlgebraMap K x := by
    ext c
    rw [IsScalarTower.algebraMap_apply K (X.left.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.left.presheaf.stalk x)),
      IsLocalRing.ResidueField.algebraMap_eq, Scheme.residueOverAlgebraMap,
      algebraMap_overStalkAlgebra]
    simp [stalkStructureHom, Scheme.overAlgebraMap]
    rfl
  letI : Algebra K (X.left.residueField x) :=
    (X.left.residueOverAlgebraMap K x).toAlgebra
  unfold Scheme.residueDeg
  change Module.finrank K (X.left.residueField x) = 1
  apply Module.finrank_of_bijective_algebraMap
  change Function.Bijective (X.left.residueOverAlgebraMap K x)
  rw [← hmap]
  exact h

/-! ## The base-changed rational point is such a section -/

theorem residueDeg_one_of_rationalPointBaseChange
    {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    (L : Type u) [Field L] [Algebra k L]
    (p : Spec (.of k) ⟶ C.left)
    (hp : p ≫ C.hom = 𝟙 (Spec (.of k))) :
    ((C ⊗ overSpec k L).left).residueDeg L
      ((Over.rationalPointBaseChange C L p hp).base (IsLocalRing.closedPoint L)) = 1 := by
  apply residueDeg_one_of_section
    (X := Over.mk (snd C (overSpec k L)).left)
    (e := Over.rationalPointBaseChange C L p hp)
  · exact Over.rationalPointBaseChange_snd C L p hp
  · rfl

/-- The graph point of a field-valued point has residue degree one. -/
theorem residueDeg_one_of_graphPoint
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom]
    (t : overSpec k K ⟶ C) :
    (C ⊗ overSpec k K).left.residueDeg K (Over.graphPoint C t) = 1 := by
  exact residueDeg_one_of_section
    (X := Over.mk (snd C (overSpec k K)).left)
    (e := (Over.sectionOfPoint t).left)
    (by
      exact congrArg (fun q : overSpec k K ⟶ overSpec k K => q.left)
        (Over.sectionOfPoint_snd t))
    (by
      change (Over.sectionOfPoint t).left.base (IsLocalRing.closedPoint K) =
        (Over.sectionOfPoint t).left.base default
      exact congrArg (Over.sectionOfPoint t).left.base
        (Subsingleton.elim _ _))

/-- The graph presentation has multiplicity one at its graph point.

`presentationDivisor_graphLocalEquations` initially records the multiplicity as an order.
The graph class and its residue field both have degree one, so the degree formula forces that
order to be one.  This is the pointwise input for finite-support class descent below. -/
theorem graphPicClass_eq_picClass_single
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom]
    (t : overSpec k K ⟶ C) :
    Over.graphPicClass C t =
      Scheme.CurveDivisor.picClass K
        (Scheme.CurveDivisor.single (graphPoint_ne_genericPoint C t) 1) := by
  let hx := graphPoint_ne_genericPoint C t
  let a : ℤ :=
    Multiplicative.toAdd
      (Scheme.ordZ ((C ⊗ overSpec k K).left ↘ Spec (CommRingCat.of K))
        hx ((Over.graphLocalEquations C t).presentation.elem (Over.graphPoint C t)))
  have hsingle :
      Scheme.presentationDivisor K (Over.graphLocalEquations C t).presentation =
        Scheme.CurveDivisor.single hx a := by
    exact presentationDivisor_graphLocalEquations C t
  have hclass :
      Scheme.CurveDivisor.picClass K (Scheme.CurveDivisor.single hx a) =
        Over.graphPicClass C t := by
    rw [← hsingle, Scheme.CurveDivisor.picClass_presentationDivisor K,
      Scheme.LocalEquations.presentation_picClass]
    rfl
  have hdeg := classDeg_graphPicClass C t
  rw [← hclass, classDeg_picClass, Scheme.CurveDivisor.deg_single'] at hdeg
  rw [residueDeg_one_of_graphPoint C t, Nat.cast_one, mul_one] at hdeg
  rw [hdeg] at hclass
  exact hclass.symm

/-! ## Image-set packaging -/

theorem residueDeg_one_of_mem_rationalPointBaseChange_image
    {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    (L : Type u) [Field L] [Algebra k L]
    (P : Set (relCurve C L))
    (hP : ∀ x ∈ P, ∃ (p : Spec (.of k) ⟶ C.left)
      (hp : p ≫ C.hom = 𝟙 (Spec (.of k))),
      (Over.rationalPointBaseChange C L p hp).base (IsLocalRing.closedPoint L) = x) :
    ∀ x ∈ P, (relCurve C L).residueDeg L x = 1 := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hP x hx
  rw [← hpx]
  exact residueDeg_one_of_rationalPointBaseChange C L p hp

/-! ## The dense point image used by the drop oracle -/

/-- The points obtained by base-changing actual `k`-rational sections of `C` to `L`.

The section certificate is retained in the membership predicate, so later consumers can recover
the base point and its exact residue-degree proof.  This is deliberately an image set, rather
than an existential carrier unrelated to the chosen curve and extension. -/
def rationalPointBaseChangeImage
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    (L : Type u) [Field L] [Algebra k L] : Set (relCurve C L) :=
  {x | ∃ (p : Spec (.of k) ⟶ C.left)
      (hp : p ≫ C.hom = 𝟙 (Spec (.of k))),
      (Over.rationalPointBaseChange C L p hp).base
        (IsLocalRing.closedPoint L) = x}

/-- Base-changed `k`-rational points are dense over a separably closed base. -/
theorem dense_rationalPointBaseChangeImage
    {k : Type u} [Field k] [IsSepClosed k]
    (C : Over (Spec (.of k)))
    (L : Type u) [Field L] [Algebra k L]
    [SmoothOfRelativeDimension 1 C.hom] [IsIntegral C.left]
    (U : (relCurve C L).Opens)
    (hU : (U : Set (relCurve C L)).Nonempty) :
    (rationalPointBaseChangeImage C L ∩ U).Nonempty := by
  obtain ⟨p, hp, hmem⟩ := Over.dense_baseChange_rationalPoints C L U hU
  exact ⟨_, ⟨⟨p, hp, rfl⟩, hmem⟩⟩

/-- Every point in the dense image has residue degree one, by its retained section certificate. -/
theorem residueDeg_one_of_mem_rationalPointBaseChangeImage'
    {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    (L : Type u) [Field L] [Algebra k L] :
    ∀ x ∈ rationalPointBaseChangeImage C L,
      (relCurve C L).residueDeg L x = 1 := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hx
  rw [← hpx]
  exact residueDeg_one_of_rationalPointBaseChange C L p hp

/-! ## Class descent for divisors supported on the rational-point image -/

/-- Every point in the rational-point image is non-generic.  The retained section certificate
identifies it with an actual graph point, where `graphPoint_ne_genericPoint` applies. -/
theorem ne_genericPoint_of_mem_rationalPointBaseChangeImage
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] :
    ∀ x ∈ rationalPointBaseChangeImage C L,
      x ≠ genericPoint (C ⊗ overSpec k L).left := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hx
  rw [← hpx]
  let q : overSpec k k ⟶ C := Over.homMk p (by
    rw [overSpec_self_hom]
    exact hp)
  change Over.graphPoint C
      (Over.overSpecMap (Algebra.ofId k L) ≫ q) ≠
        genericPoint (C ⊗ overSpec k L).left
  exact graphPoint_ne_genericPoint C _

/-- The one-point divisor at a base-changed rational point is the base change of a class on the
base curve.  This is deliberately a class statement: no pullback operation on Weil divisors is
needed. -/
theorem exists_baseClass_picClass_single_of_mem_rationalPointBaseChangeImage
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom]
    (x : (C ⊗ overSpec k L).left)
    (hx : x ≠ genericPoint (C ⊗ overSpec k L).left)
    (hmem : x ∈ rationalPointBaseChangeImage C L) :
    ∃ c : (C ⊗ overSpec k k).left.CechPic,
      Scheme.CurveDivisor.picClass L (Scheme.CurveDivisor.single hx 1) =
        Scheme.CechPic.map (relCurveMap C k L) c := by
  obtain ⟨p, hp, hpx⟩ := hmem
  let q : overSpec k k ⟶ C := Over.homMk p (by
    rw [overSpec_self_hom]
    exact hp)
  change Over.graphPoint C
      (Over.overSpecMap (Algebra.ofId k L) ≫ q) = x at hpx
  subst x
  refine ⟨Over.graphPicClass C q, ?_⟩
  rw [← graphPicClass_eq_picClass_single C]
  exact graphPicClass_base_of_field C L q

/-- A divisor whose finite support consists of base-changed rational points has a Picard class
defined over the base field.

The proof folds the pointwise graph-class identity over the divisor's `Finsupp` support.  It
works for arbitrary integer multiplicities; effectivity and the prescribed drop degree are
orthogonal hypotheses used by the greedy reduction, not by class descent. -/
theorem exists_baseClass_of_supported_on_rationalPointBaseChangeImage
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom]
    (S : (C ⊗ overSpec k L).left.CurveDivisor)
    (hsupp : ∀ (x : (C ⊗ overSpec k L).left)
      (hx : x ≠ genericPoint (C ⊗ overSpec k L).left),
      coeffAt hx S ≠ 0 → x ∈ rationalPointBaseChangeImage C L) :
    ∃ c : (C ⊗ overSpec k k).left.CechPic,
      Scheme.CurveDivisor.picClass L S =
        Scheme.CechPic.map (relCurveMap C k L) c := by
  suffices hmain : ∀ f : {x : (C ⊗ overSpec k L).left //
      x ≠ genericPoint (C ⊗ overSpec k L).left} →₀ ℤ,
      (∀ (x : (C ⊗ overSpec k L).left)
        (hx : x ≠ genericPoint (C ⊗ overSpec k L).left),
        coeffAt hx f ≠ 0 → x ∈ rationalPointBaseChangeImage C L) →
      ∃ c : (C ⊗ overSpec k k).left.CechPic,
        Scheme.CurveDivisor.picClass L f =
          Scheme.CechPic.map (relCurveMap C k L) c from hmain S hsupp
  intro f
  induction f using Finsupp.induction with
  | zero =>
      intro _
      refine ⟨1, ?_⟩
      change Scheme.CurveDivisor.picClass L
        (0 : (C ⊗ overSpec k L).left.CurveDivisor) =
          Scheme.CechPic.map (relCurveMap C k L) 1
      rw [Scheme.CurveDivisor.picClass_zero, map_one]
      rfl
  | single_add p b f hpf hb ih =>
      intro hsupport
      have hfp : f p = 0 := Finsupp.notMem_support_iff.mp hpf
      have hpMem : p.1 ∈ rationalPointBaseChangeImage C L := by
        apply hsupport p.1 p.2
        change (Finsupp.single p b + f) p ≠ 0
        rw [Finsupp.add_apply, Finsupp.single_eq_same, hfp, add_zero]
        exact hb
      have hfSupport : ∀ (x : (C ⊗ overSpec k L).left)
          (hx : x ≠ genericPoint (C ⊗ overSpec k L).left),
          coeffAt hx f ≠ 0 → x ∈ rationalPointBaseChangeImage C L := by
        intro x hx hfx
        apply hsupport x hx
        change (Finsupp.single p b + f) ⟨x, hx⟩ ≠ 0
        have hxp : (⟨x, hx⟩ : {z : (C ⊗ overSpec k L).left //
            z ≠ genericPoint (C ⊗ overSpec k L).left}) ≠ p := by
          intro heq
          subst p
          exact hfx hfp
        rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hxp, zero_add]
        exact hfx
      obtain ⟨cp, hcp⟩ :=
        exists_baseClass_picClass_single_of_mem_rationalPointBaseChangeImage
          C p.1 p.2 hpMem
      have key : ∀ D : (C ⊗ overSpec k L).left.CurveDivisor,
          (∃ cf : (C ⊗ overSpec k k).left.CechPic,
            Scheme.CurveDivisor.picClass L D =
              Scheme.CechPic.map (relCurveMap C k L) cf) →
          ∃ c : (C ⊗ overSpec k k).left.CechPic,
            Scheme.CurveDivisor.picClass L
              (Scheme.CurveDivisor.single p.2 b + D) =
              Scheme.CechPic.map (relCurveMap C k L) c := by
        intro D hD
        obtain ⟨cf, hcf⟩ := hD
        refine ⟨cp ^ b * cf, ?_⟩
        unfold relCurveMap relCurve at hcp hcf ⊢
        rw [Scheme.CurveDivisor.picClass_add,
          ← Scheme.picClass_single_zpow L p.2 b, hcp, hcf, map_mul, map_zpow]
      exact key f (ih hfSupport)

/-- Exact discharge of `SepClosedTranslatedDropData.baseSubtraction` for the rational-point
image.  The descended class is re-presented by an actual base-field divisor `Z`; at exponent
zero, the inverse of `chartTwistClass C 0 Z` is precisely `picClass k Z`. -/
theorem exists_baseSubtraction_of_supported_on_rationalPointBaseChangeImage
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom]
    (S : (C ⊗ overSpec k L).left.CurveDivisor)
    (hsupp : ∀ (x : (C ⊗ overSpec k L).left)
      (hx : x ≠ genericPoint (C ⊗ overSpec k L).left),
      coeffAt hx S ≠ 0 → x ∈ rationalPointBaseChangeImage C L) :
    ∃ Z : (C ⊗ overSpec k k).left.CurveDivisor,
      Scheme.CurveDivisor.picClass L S =
        Scheme.CechPic.map (relCurveMap C k L)
          ((chartTwistClass C 0 Z)⁻¹) := by
  obtain ⟨c, hc⟩ :=
    exists_baseClass_of_supported_on_rationalPointBaseChangeImage C S hsupp
  obtain ⟨Z, hZ⟩ := Scheme.CurveDivisor.exists_picClass_eq k c
  refine ⟨Z, ?_⟩
  rw [hc]
  apply congrArg
  simp only [chartTwistClass, pow_zero, one_mul]
  rw [hZ]
  exact (inv_inv c).symm

/-! ## The separably-closed drop package -/

section DropPackage

variable {k : Type u} [Field k] [IsSepClosed k]
variable {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {K L : Type u} [Field K] [Algebra k K]
  [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Module.Finite K L] [Algebra.IsSeparable K L]

/-- Build the translated-drop package using the actual dense image of base-field rational
points.  Density, non-genericity, residue degree one, and the base-subtraction class identity
are derived here; only the lambda-tied positive-twist divisor and its degree/vanishing data
remain inputs. -/
noncomputable def sepClosedTranslatedDropDataOfRationalPointImage
    (μ : picEt C (overSpec k K))
    (m : ℕ)
    (M₀ : (relCurve C L).CechPic)
    (hM₀ : PicEtAff.map C L (picEtAffineEquiv C K μ) =
      PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    (W₀ : (C ⊗ overSpec k L).left.CurveDivisor)
    (hW₀ : Scheme.CurveDivisor.picClass L W₀ =
      M₀ * Scheme.CechPic.map (relCurveMap C k L)
        (chartTwistClass C m (0 : (C ⊗ overSpec k k).left.CurveDivisor)))
    (excess : ℕ)
    (hdeg : Scheme.CurveDivisor.deg L W₀ = (genus C : ℤ) + excess)
    (h1 : Subsingleton (Sheaf.HModule
      ((C ⊗ overSpec k L).left.divisorSheaf L W₀) 1)) :
    SepClosedTranslatedDropData (C := C) (L := L) μ where
  m := m
  M₀ := M₀
  hM₀ := hM₀
  W₀ := W₀
  hW₀ := hW₀
  genusValue := genus C
  excess := excess
  hχ := chi_moduleKSheaf C
  hdeg := hdeg
  h1 := h1
  P := rationalPointBaseChangeImage C L
  hdense := dense_rationalPointBaseChangeImage C L
  hPcl := ne_genericPoint_of_mem_rationalPointBaseChangeImage C
  hPdeg := residueDeg_one_of_mem_rationalPointBaseChangeImage' C L
  baseSubtraction := by
    intro S _ _ hsupp
    exact exists_baseSubtraction_of_supported_on_rationalPointBaseChangeImage C S hsupp

/-- Immediate lambda-tied consumer of the rational-point-image package.

The result contains the effective subtraction divisor, a base-field translating divisor,
`h⁰ = 1`, preservation of `H¹ = 0`, the class-level base-change identity, and the existing
`IsSplitWitness` for `μ` translated by that specific base-field class. -/
theorem exists_sepClosedTranslatedDropResult_of_rationalPointImage
    (μ : picEt C (overSpec k K))
    (m : ℕ)
    (M₀ : (relCurve C L).CechPic)
    (hM₀ : PicEtAff.map C L (picEtAffineEquiv C K μ) =
      PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    (W₀ : (C ⊗ overSpec k L).left.CurveDivisor)
    (hW₀ : Scheme.CurveDivisor.picClass L W₀ =
      M₀ * Scheme.CechPic.map (relCurveMap C k L)
        (chartTwistClass C m (0 : (C ⊗ overSpec k k).left.CurveDivisor)))
    (excess : ℕ)
    (hdeg : Scheme.CurveDivisor.deg L W₀ = (genus C : ℤ) + excess)
    (h1 : Subsingleton (Sheaf.HModule
      ((C ⊗ overSpec k L).left.divisorSheaf L W₀) 1)) :
    Nonempty (SepClosedTranslatedDropResult (C := C) (L := L) μ
      (sepClosedTranslatedDropDataOfRationalPointImage
        μ m M₀ hM₀ W₀ hW₀ excess hdeg h1)) := by
  exact exists_sepClosedTranslatedDropResult μ
    (sepClosedTranslatedDropDataOfRationalPointImage
      μ m M₀ hM₀ W₀ hW₀ excess hdeg h1)

end DropPackage

end AlgebraicGeometry
