/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneCanonicalEvaluation
import AlgebraicJacobian.Picard.Pic0RankOneOpenProducer
import AlgebraicJacobian.Picard.Pic0RankOneTranslatedCoverMembership
import AlgebraicJacobian.Picard.Pic0ChartAtlasCoupling
import AlgebraicJacobian.Picard.JacobianDataCharts
import AlgebraicJacobian.Picard.DivSchemeQProj

/-!
# Representability of `Pic^0` over a separably closed field

This module turns the public rank-one open and the translated field-point theorem into the
Zariski atlas required by `pic0RepresentableByOfCharts`.  The chart source is the actual open of
the genus divisor representer supplied by `DivRankOneOpenData`; its map to the rank-one locus is
the canonical Abel isomorphism, and each chart is translated by the same base class that indexes
it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## Sigma-extension isomorphisms -/

/-- Sigma extension preserves natural isomorphisms of slice presheaves. -/
noncomputable def sigmaExtensionIso {F G : (Over (Spec (.of k)))ᵒᵖ ⥤ Type u}
    (e : F ≅ G) :
    Over.sigmaExtension (Spec (.of k)) F ≅
      Over.sigmaExtension (Spec (.of k)) G where
  hom := Over.sigmaExtensionNat e.hom
  inv := Over.sigmaExtensionNat e.inv
  hom_inv_id := by
    ext T x
    rcases x with ⟨a, x⟩
    exact congrArg (Sigma.mk a) (e.hom_inv_id_app_apply _ x)
  inv_hom_id := by
    ext T x
    rcases x with ⟨a, x⟩
    exact congrArg (Sigma.mk a) (e.inv_hom_id_app_apply _ x)

/-- A representation on the slice extends to an isomorphism between the ambient Yoneda
presheaf of its representing object and the sigma extension. -/
noncomputable def representableBySigmaIso
    {F : (Over (Spec (.of k)))ᵒᵖ ⥤ Type u} {J : Over (Spec (.of k))}
    (rep : F.RepresentableBy J) :
    yoneda.obj J.left ≅ Over.sigmaExtension (Spec (.of k)) F where
  hom := rep.toSigmaExtension
  inv :=
    { app := fun T => TypeCat.ofHom fun x => (rep.homEquiv.symm x.2).left
      naturality := by
        intro T T' f
        ext x
        rcases x with ⟨a, x⟩
        let q : Over.mk (f.unop ≫ a) ⟶ Over.mk a := Over.homMk f.unop rfl
        exact (congrArg Over.Hom.left
          (rep.comp_homEquiv_symm x q)).symm }
  hom_inv_id := by
    ext T v
    exact congrArg Over.Hom.left (rep.homEquiv.symm_apply_apply
      (Over.homMk v rfl : Over.mk (v ≫ J.hom) ⟶ J))
  inv_hom_id := by
    ext T x
    rcases x with ⟨a, x⟩
    let g := rep.homEquiv.symm x
    have hga : g.left ≫ J.hom = a := g.w
    refine Over.sigmaExtension_ext F hga ?_
    change F.map (Over.mkCongr hga).op x =
      rep.homEquiv (Over.homMk g.left rfl : Over.mk (g.left ≫ J.hom) ⟶ J)
    rw [← rep.homEquiv.apply_symm_apply x]
    rw [← rep.homEquiv_comp]
    exact congrArg rep.homEquiv (Over.OverMorphism.ext rfl)

/-! ## The represented rank-one open -/

/-- The Yoneda range of an open immersion is represented by its source.  Here the range is
identified with the exact divisor predicate whose Abel class lies in `PicRankOneOpen`. -/
noncomputable def rankOneDivisorOpenRepresentableBy
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (h : DivRankOneOpenData (C := C) pi) :
    (divRankOnePresentationPreimageRepresenter pi).toFunctor.RepresentableBy
      (divRankOneOpenOver pi h) where
  homEquiv {T} :=
    { toFun := fun y => ⟨y ≫ divRankOneOpenOverMap pi h, by
        have hy : y ≫ divRankOneOpenOverMap pi h ∈
            (openSubfunctor (divRepAffGenusScheme C) h.carrier).obj (op T) :=
          ⟨y, rfl⟩
        rw [h.carrier_eq] at hy
        exact hy⟩
      invFun := fun x => Classical.choose
        (rankOneRepresenterRestriction_factorization pi h x)
      left_inv := fun y => by
        apply Over.OverMorphism.ext
        letI : IsOpenImmersion (divRankOneOpenMap pi h) :=
          divRankOneOpen_isOpenImmersion pi h
        apply (cancel_mono (divRankOneOpenMap pi h)).mp
        exact congrArg Over.Hom.left (Classical.choose_spec
          (rankOneRepresenterRestriction_factorization pi h
            ⟨y ≫ divRankOneOpenOverMap pi h, by
              have hy : y ≫ divRankOneOpenOverMap pi h ∈
                  (openSubfunctor (divRepAffGenusScheme C) h.carrier).obj (op T) :=
                ⟨y, rfl⟩
              rw [h.carrier_eq] at hy
              exact hy⟩))
      right_inv := fun x => by
        apply Subtype.ext
        exact Classical.choose_spec
          (rankOneRepresenterRestriction_factorization pi h x) }
  homEquiv_comp {T T'} f y := by
    apply Subtype.ext
    exact Category.assoc f y (divRankOneOpenOverMap pi h)

/-- The canonical Abel map and canonical evaluation divisor form an isomorphism already on the
slice.  Its sigma extension is `canonicalRankOneAbelIso`. -/
noncomputable def canonicalRankOneAbelSliceIso :
    (divRankOnePresentationPreimageRepresenter (divRepAffP1Map C)).toFunctor ≅
      (PicRankOneOpen (divRepAffP1Map C)).toFunctor where
  hom := rankOneAbelRepresented (divRepAffP1Map C)
  inv := canonicalRankOneRepresenterTrans (C := C)
  hom_inv_id := by
    ext T x
    apply rankOneAbelRepresented_app_injective (divRepAffP1Map C) T.unop
    exact canonicalRankOneRepresenterTrans_abel
      ((rankOneAbelRepresented (divRepAffP1Map C)).app T x)
  inv_hom_id := by
    ext T x
    exact canonicalRankOneRepresenterTrans_abel x

/-- The certified divisor open represents the public rank-one Picard locus. -/
noncomputable def picRankOneOpenRepresentableBy
    (h : DivRankOneOpenData (C := C) (divRepAffP1Map C)) :
    (PicRankOneOpen (divRepAffP1Map C)).toFunctor.RepresentableBy
      (divRankOneOpenOver (divRepAffP1Map C) h) :=
  (rankOneDivisorOpenRepresentableBy (C := C) (divRepAffP1Map C) h).ofIso
    (canonicalRankOneAbelSliceIso (C := C))

/-! ## Translation by a base class of degree `genus C` -/

/-- Base classes which translate degree zero into the genus-degree layer. -/
abbrev PicRankOneTranslatorIndex :=
  {L : (C ⊗ overSpec k k).left.CechPic // classDeg k L = (genus C : ℤ)}

/-- Multiplication by a translator, at one test object. -/
noncomputable def pic0GenusTranslationEquiv
    (a : PicRankOneTranslatorIndex (C := C)) (T : Over (Spec (.of k))) :
    pic0Subgroup C T ≃ picDegLayer C (genus C : ℤ) T where
  toFun lam := ⟨lam.1 * thetaFamily C a.1 T, fun K _ _ t => by
    rw [degAt_mul, lam.2 K t, degAt_thetaFamily, zero_add, a.2]⟩
  invFun lam := ⟨lam.1 * (thetaFamily C a.1 T)⁻¹,
    mem_pic0Subgroup_iff.mpr fun K _ _ t => by
      rw [degAt_mul, degAt_inv, degAt_thetaFamily, lam.2 K t, a.2]
      ring⟩
  left_inv lam := Subtype.ext (mul_inv_cancel_right _ _)
  right_inv lam := Subtype.ext (inv_mul_cancel_right _ _)

/-- Multiplication by a translator is the natural isomorphism from `Pic^0` to the genus-degree
Picard layer.  It is the degree-specialized, one-fold form of `mulThetaPowNatIso`. -/
noncomputable def pic0GenusTranslationIso (a : PicRankOneTranslatorIndex (C := C)) :
    pic0TypeFunctor C ≅ picDegLayerFunctor C (genus C : ℤ) :=
  NatIso.ofComponents (fun T => (pic0GenusTranslationEquiv (C := C) a T.unop).toIso) (by
    intro T T' f
    ext lam
    refine Subtype.ext ?_
    have key :
        picEtMap C f.unop ((pic0Subgroup C T.unop).subtype lam) *
            thetaFamily C a.1 T'.unop =
          picEtMap C f.unop
            ((pic0Subgroup C T.unop).subtype lam * thetaFamily C a.1 T.unop) := by
      rw [map_mul, thetaFamily_natural]
    exact key)

/-! ## The translated rank-one charts -/

/-- The certified divisor open, transported by the canonical Abel isomorphism, represents the
rank-one Picard locus on the big site. -/
noncomputable def picRankOneOpenSigmaIso
    (h : DivRankOneOpenData (C := C) (divRepAffP1Map C)) :
    yoneda.obj (divRankOneOpenOver (divRepAffP1Map C) h).left ≅
      rankOneLocus (C := C) (pi := divRepAffP1Map C) :=
  representableBySigmaIso
      (rankOneDivisorOpenRepresentableBy (C := C) (divRepAffP1Map C) h) ≪≫
    canonicalRankOneAbelIso (C := C)

/-- The canonical rank-one Abel isomorphism followed by the public rank-one-locus
inclusion is an open immersion. -/
theorem rankOneAbel_isOpenImmersion
    (hopen : PicRankOneOpen.IsOpen (divRepAffP1Map C)) :
    IsOpenImmersion.presheaf
      ((canonicalRankOneAbelIso (C := C)).hom ≫
        picRankOneOpenSigmaIncl (divRepAffP1Map C)) := by
  apply MorphismProperty.IsStableUnderComposition.comp_mem
  · exact MorphismProperty.of_isIso (P := IsOpenImmersion.presheaf) _
  · exact hopen

/-- The chart indexed by a base class `a` of degree `genus C`: first use canonical Abel on the
rank-one divisor open, then multiply by `a⁻¹` to return to degree zero. -/
noncomputable def picRankOneTranslatedChart
    (h : DivRankOneOpenData (C := C) (divRepAffP1Map C))
    (a : PicRankOneTranslatorIndex (C := C)) :
    yoneda.obj (divRankOneOpenOver (divRepAffP1Map C) h).left ⟶
      (pic0SigmaSheaf C).1 :=
  (picRankOneOpenSigmaIso (C := C) h).hom ≫
    picRankOneOpenSigmaIncl (divRepAffP1Map C) ≫
      (sigmaExtensionIso (pic0GenusTranslationIso (C := C) a)).inv

/-- Every translated rank-one chart is a representable open immersion. -/
theorem picRankOneTranslatedChart_isOpenImmersion
    (hopen : PicRankOneOpen.IsOpen (divRepAffP1Map C))
    (a : PicRankOneTranslatorIndex (C := C)) :
    IsOpenImmersion.presheaf
      (picRankOneTranslatedChart (C := C)
        (divRankOneOpenDataOfPicRankOneOpen (divRepAffP1Map C) hopen) a) := by
  have hrepresenter : IsOpenImmersion.presheaf
      (representableBySigmaIso
        (rankOneDivisorOpenRepresentableBy (C := C) (divRepAffP1Map C)
          (divRankOneOpenDataOfPicRankOneOpen (divRepAffP1Map C) hopen))).hom :=
    MorphismProperty.of_isIso (P := IsOpenImmersion.presheaf) _
  have htranslation : IsOpenImmersion.presheaf
      (sigmaExtensionIso (pic0GenusTranslationIso (C := C) a)).inv :=
    MorphismProperty.of_isIso (P := IsOpenImmersion.presheaf) _
  simpa only [picRankOneTranslatedChart, picRankOneOpenSigmaIso, Iso.trans_hom,
    Category.assoc] using
      MorphismProperty.IsStableUnderComposition.comp_mem _ _
        (MorphismProperty.IsStableUnderComposition.comp_mem _ _ hrepresenter
          (rankOneAbel_isOpenImmersion (C := C) hopen)) htranslation

/-! ## Finiteness of the translated charts -/

/-- The chosen genus divisor representer is locally of finite type over the base.  In positive
genus it is definitionally a divisor scheme.  In genus zero, representer uniqueness transports
the certificate from the terminal representer. -/
theorem locallyOfFiniteType_divRepAffGenusScheme :
    LocallyOfFiniteType (divRepAffGenusScheme C).hom := by
  by_cases hg : genus C = 0
  · let D0 : Over (Spec (.of k)) := Over.mk (𝟙 (Spec (.of k)))
    have rep0 : (divFunctorAff C (genus C)).RepresentableBy D0 := by
      rw [hg]
      exact divFunctorAffZeroRepresentableBy (C := C) (pi := divRepAffP1Map C)
    let e := (divFunctorAff_genus_representableBy C).uniqueUpToIso rep0
    haveI : LocallyOfFiniteType D0.hom := by
      change LocallyOfFiniteType (𝟙 (Spec (.of k)))
      infer_instance
    rw [← Over.w e.hom]
    infer_instance
  · unfold divRepAffGenusScheme divFunctorAffGenusRepresenter divRepAffScheme_at
      divFunctorAffRepresenter_at
    dsimp only
    rw [dif_neg hg]
    infer_instance

/-- The certified rank-one divisor open is locally of finite type over the base field. -/
theorem locallyOfFiniteType_divRankOneOpenOver
    (h : DivRankOneOpenData (C := C) (divRepAffP1Map C)) :
    LocallyOfFiniteType (divRankOneOpenOver (divRepAffP1Map C) h).hom := by
  change LocallyOfFiniteType
    (divRankOneOpenMap (divRepAffP1Map C) h ≫ (divRepAffGenusScheme C).hom)
  letI : IsOpenImmersion (divRankOneOpenMap (divRepAffP1Map C) h) :=
    divRankOneOpen_isOpenImmersion (divRepAffP1Map C) h
  haveI : LocallyOfFiniteType (divRepAffGenusScheme C).hom :=
    locallyOfFiniteType_divRepAffGenusScheme (C := C)
  infer_instance

/-- The structure map read from a translated rank-one chart is the structure map of its
rank-one divisor-open source. -/
lemma chartHom_picRankOneTranslatedChart
    (h : DivRankOneOpenData (C := C) (divRepAffP1Map C))
    (a : PicRankOneTranslatorIndex (C := C)) :
    chartHom C (fun a : PicRankOneTranslatorIndex (C := C) =>
      picRankOneTranslatedChart (C := C) h a) a =
      (divRankOneOpenOver (divRepAffP1Map C) h).hom :=
  rfl

/-! ## From residue-field coverage to pointwise coverage -/

/-- A family of representable open immersions covers pointwise as soon as it covers the class at
every residue-field point.  Relative representability pulls a chosen field factorization back to
an open immersion over the test; its open range is the required neighborhood. -/
theorem pointwiseCoverage_of_residueField
    {I : Type u} {X : I → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (hf : ∀ i, IsOpenImmersion.presheaf (f i))
    (hfield : ∀ (T : Scheme.{u}) (s : (pic0SigmaSheaf C).1.obj (op T)) (t : T),
      ∃ (Y : Scheme.{u}) (q : Y) (y : Y ⟶ T) (i : I) (x : Y ⟶ X i),
        y.base q = t ∧
          (f i).app (op Y) x = (pic0SigmaSheaf C).1.map y.op s) :
    PointwiseCoverage C f := by
  intro T s t
  obtain ⟨Y, q, y, i, x, hyt, hx⟩ := hfield T s t
  let g : yoneda.obj T ⟶ (pic0SigmaSheaf C).1 := yonedaEquiv.symm s
  obtain ⟨Z, snd, fst, hpb⟩ := (hf i).rep g
  letI : IsOpenImmersion snd := (hf i).property g fst snd hpb
  have hpbY := (IsPullback.iff_app.mp hpb) (op Y)
  rw [Types.isPullback_iff] at hpbY
  have hg : g.app (op Y) y = (pic0SigmaSheaf C).1.map y.op s := by
    exact yonedaEquiv_symm_app_apply s _ y
  obtain ⟨z, hz₁, hz₂⟩ := hpbY.2.2 x y (hx.trans hg.symm)
  let W : T.Opens := snd.opensRange
  have htW : t ∈ W := by
    change t ∈ snd.opensRange
    apply Scheme.Hom.mem_opensRange.mpr
    refine ⟨z.base q, ?_⟩
    have hz := congrArg (fun m : Y ⟶ T => m.base q) hz₂
    exact hz.trans hyt
  refine ⟨W, htW, i, fst.app (op (W : Scheme.{u})) snd.isoOpensRange.inv, ?_⟩
  have hpbW := (IsPullback.iff_app.mp hpb) (op (W : Scheme.{u}))
  rw [Types.isPullback_iff] at hpbW
  have hcomm := congrArg
    (fun q => (ConcreteCategory.hom q) snd.isoOpensRange.inv) hpbW.1
  change (f i).app (op (W : Scheme.{u}))
      (fst.app (op (W : Scheme.{u})) snd.isoOpensRange.inv) = _
  change (f i).app (op (W : Scheme.{u}))
      (fst.app (op (W : Scheme.{u})) snd.isoOpensRange.inv) =
    g.app (op (W : Scheme.{u})) (snd.isoOpensRange.inv ≫ snd) at hcomm
  rw [Scheme.Hom.isoOpensRange_inv_comp] at hcomm
  change (f i).app (op (W : Scheme.{u}))
      (fst.app (op (W : Scheme.{u})) snd.isoOpensRange.inv) =
    (yonedaEquiv.symm s).app (op (W : Scheme.{u})) W.ι at hcomm
  rwa [yonedaEquiv_symm_app_apply] at hcomm

/-! ## The separably closed field-point producer -/

variable [IsSepClosed k]

/-- Every degree-zero field class is hit by the translated chart indexed by the exact base class
returned by `exists_sepClosedTranslated_mem_picRankOneOpen`. -/
theorem exists_picRankOneTranslatedChart_fieldFactorization
    (hopen : PicRankOneOpen.IsOpen (divRepAffP1Map C))
    {K : Type u} [Field K] [Algebra k K]
    (mu : pic0Subgroup C (overSpec k K)) :
    ∃ (a : PicRankOneTranslatorIndex (C := C))
      (x : (overSpec k K).left ⟶
        (divRankOneOpenOver (divRepAffP1Map C)
          (divRankOneOpenDataOfPicRankOneOpen (divRepAffP1Map C) hopen)).left),
      (picRankOneTranslatedChart (C := C)
          (divRankOneOpenDataOfPicRankOneOpen (divRepAffP1Map C) hopen) a).app
        (op (overSpec k K).left) x =
          (⟨(overSpec k K).hom, mu⟩ :
            (pic0SigmaSheaf C).1.obj (op (overSpec k K).left)) := by
  obtain ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, d, r, hdeg, hsupp, hmem⟩ :=
    exists_sepClosedTranslated_mem_picRankOneOpen
      (C := C) (divRepAffP1Map C) (divRepAffP1Map_comp C) mu
  letI := hLfield
  letI := hkL
  letI := hKL
  letI := htow
  letI := hfin
  letI := hsep
  let a : PicRankOneTranslatorIndex (C := C) :=
    ⟨chartTwistClass C d.m r.Z, hdeg⟩
  let baseValue : (pic0SigmaSheaf C).1.obj (op (overSpec k K).left) :=
    ⟨(overSpec k K).hom, mu⟩
  let translatedValue :=
    (sigmaExtensionIso (pic0GenusTranslationIso (C := C) a)).hom.app
      (op (overSpec k K).left) baseValue
  have htranslated : translatedValue.2 = r.rankOneLayer mu.1 d := by
    apply Subtype.ext
    change mu.1 * thetaFamily C (chartTwistClass C d.m r.Z) (overSpec k K) = _
    rw [SepClosedTranslatedDropResult.rankOneLayer_coe]
  have htranslatedMem : translatedValue.2 ∈
      (PicRankOneOpen (divRepAffP1Map C)).obj (op (overSpec k K)) := by
    rw [htranslated]
    exact hmem
  let v : (rankOneLocus (C := C) (pi := divRepAffP1Map C)).obj
      (op (overSpec k K).left) :=
    ⟨translatedValue.1, ⟨translatedValue.2, htranslatedMem⟩⟩
  let e := picRankOneOpenSigmaIso (C := C)
    (divRankOneOpenDataOfPicRankOneOpen (divRepAffP1Map C) hopen)
  refine ⟨a, e.inv.app (op (overSpec k K).left) v, ?_⟩
  change (sigmaExtensionIso (pic0GenusTranslationIso (C := C) a)).inv.app _
      ((picRankOneOpenSigmaIncl (divRepAffP1Map C)).app _
        (e.hom.app _ (e.inv.app _ v))) = baseValue
  rw [e.inv_hom_id_app_apply]
  change (sigmaExtensionIso (pic0GenusTranslationIso (C := C) a)).inv.app _
      translatedValue = baseValue
  exact (sigmaExtensionIso (pic0GenusTranslationIso (C := C) a)).hom_inv_id_app_apply
    _ baseValue

/-! ## Pointwise coverage and representability -/

set_option maxHeartbeats 800000 in
-- Elaborating the residue-field specialization crosses both sigma-extension dependent fibres.
/-- The translated rank-one charts cover the sigma extension pointwise.  At a point `t`,
restrict the degree-zero class to `Spec κ(t)`, use the exact separably-closed translated
rank-one factorization there, and take the whole residue-field point as the covering source. -/
theorem picRankOneTranslatedChart_pointwiseCoverage
    (hopen : PicRankOneOpen.IsOpen (divRepAffP1Map C)) :
    PointwiseCoverage C (fun a : PicRankOneTranslatorIndex (C := C) =>
      picRankOneTranslatedChart (C := C)
        (divRankOneOpenDataOfPicRankOneOpen (divRepAffP1Map C) hopen) a) := by
  apply pointwiseCoverage_of_residueField (C := C)
  · exact fun a => picRankOneTranslatedChart_isOpenImmersion (C := C) hopen a
  · intro T s t
    rcases s with ⟨b, mu⟩
    let Tbar : Over (Spec (.of k)) := Over.mk b
    let K := Over.testPointField (T := Tbar) t
    let p : overSpec k K ⟶ Tbar := Over.testPoint (T := Tbar) t
    let muK : pic0Subgroup C (overSpec k K) := (pic0TypeFunctor C).map p.op mu
    obtain ⟨a, x, hx⟩ :=
      exists_picRankOneTranslatedChart_fieldFactorization (C := C) hopen muK
    let q : (overSpec k K).left := Classical.choice inferInstance
    have hq : p.left.base q = t := by
      dsimp only [p]
      exact Over.testPoint_base (T := Tbar) t q
    refine ⟨(overSpec k K).left, q, p.left, a, x, ?_, ?_⟩
    · exact hq
    · exact hx.trans (Over.sigmaExtension_map_left_mk p mu).symm

/-- Over a separably closed field, openness of the rank-one Picard locus gives a scheme
representing `Pic^0`.  This conditional form keeps the geometric gluing argument reusable. -/
noncomputable def pic0_sepClosed_representableBy_of_isOpen
    (hopen : PicRankOneOpen.IsOpen (divRepAffP1Map C)) :
    Σ J : Over (Spec (.of k)), (pic0TypeFunctor C).RepresentableBy J := by
  let h := divRankOneOpenDataOfPicRankOneOpen (divRepAffP1Map C) hopen
  let f := fun a : PicRankOneTranslatorIndex (C := C) =>
    picRankOneTranslatedChart (C := C) h a
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) :=
    isLocallySurjective_sigmaDesc_of_pointwise C f
      (picRankOneTranslatedChart_pointwiseCoverage (C := C) hopen)
  exact ⟨_, pic0RepresentableByOfCharts C f
    (fun a => picRankOneTranslatedChart_isOpenImmersion (C := C) hopen a)⟩

/-- Over a separably closed field, `Pic^0` is represented by the scheme obtained by gluing the
translated canonical rank-one Abel charts. -/
noncomputable def pic0_sepClosed_representableBy :
    Σ J : Over (Spec (.of k)), (pic0TypeFunctor C).RepresentableBy J :=
  pic0_sepClosed_representableBy_of_isOpen
    (C := C) (picRankOneOpen_isOpen (divRepAffP1Map C) (divRepAffP1Map_comp C))

/-- The exact separably closed representing scheme constructed above is locally of finite type
over the base field. -/
theorem locallyOfFiniteType_pic0_sepClosed_representableBy :
    LocallyOfFiniteType (pic0_sepClosed_representableBy (C := C)).1.hom := by
  let hopen := picRankOneOpen_isOpen (C := C)
    (divRepAffP1Map C) (divRepAffP1Map_comp C)
  let h := divRankOneOpenDataOfPicRankOneOpen (divRepAffP1Map C) hopen
  let f := fun a : PicRankOneTranslatorIndex (C := C) =>
    picRankOneTranslatedChart (C := C) h a
  let hf := fun a : PicRankOneTranslatorIndex (C := C) =>
    picRankOneTranslatedChart_isOpenImmersion (C := C) hopen a
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) :=
    isLocallySurjective_sigmaDesc_of_pointwise C f
      (picRankOneTranslatedChart_pointwiseCoverage (C := C) hopen)
  change LocallyOfFiniteType (gluedHom C f hf)
  apply locallyOfFiniteType_gluedHom C f hf
  intro a
  rw [chartHom_picRankOneTranslatedChart]
  exact locallyOfFiniteType_divRankOneOpenOver h

end

end AlgebraicGeometry
