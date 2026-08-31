/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveSite
import AlgebraicJacobian.Picard.Pic0ChartLocusIsoInvariance
import AlgebraicJacobian.Picard.Pic0RankOneNativePresentationSplit
import AlgebraicJacobian.Picard.Pic0RankOneSplitDescent
import AlgebraicJacobian.Picard.Pic0RankOneSplitMembership
import Mathlib.RingTheory.RingHom.Flat

/-!
# The unconditional open producer for the rank-one Picard locus

The public rank-one locus is detected at field-valued points by `IsSplitWitness`.  This file
turns that pointwise characterization into the represented open fibres required by
`PicRankOneOpen.FibrePresented`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite MonoidalCategory
  CartesianMonoidalCategory

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-- The pointwise split locus of a Picard class on an arbitrary test scheme. -/
def picRankOneSplitLocus (T : Over (Spec (.of k))) (lam : picEt C T) : Set T.left :=
  {t | IsSplitWitness C (picEtMap C (Over.testPoint t) lam)}

/-- Pointwise split loci pull back exactly along a morphism of tests. -/
theorem picRankOneSplitLocus_map_eq_preimage
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (lam : picEt C T) :
    picRankOneSplitLocus (C := C) T' (picEtMap C f lam) =
      f.left.base ⁻¹' picRankOneSplitLocus (C := C) T lam := by
  refine Set.ext fun t => ?_
  change IsSplitWitness C (picEtMap C (Over.testPoint t) (picEtMap C f lam)) ↔
    IsSplitWitness C
      (picEtMap C (Over.testPoint (T := T) (f.left.base t)) lam)
  let e := Over.testPointFieldAlgHom f t
  have hfac : picEtMap C (Over.testPoint t) (picEtMap C f lam) =
      picEtMap C (Over.overSpecMap e)
        (picEtMap C (Over.testPoint (T := T) (f.left.base t)) lam) := by
    rw [← picEtMap_comp, ← picEtMap_comp, Over.testPoint_comp f t]
  rw [hfac]
  exact ⟨isSplitWitness_of_overSpecMap pi e _,
    isSplitWitness_map_overSpecMap_of_algHom pi e _⟩

/-- The pointwise split locus of an affine genus-degree class is open.

The class is made honest on the carrier of a native étale datum.  There the datum-level
`H¹` engine proves openness.  The carrier locus is the pullback of the original locus by
split-witness ascent and descent along residue-field extensions, and faithful flatness makes
the spectrum map a quotient map. -/
theorem isOpen_picRankOneSplitLocus_overSpec
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (hpi : pi ≫ P1.structureMap k = C.hom)
    {A : Type u} [CommRing A] [Algebra k A]
    (lam : picDegLayer C (genus C : ℤ) (overSpec k A)) :
    IsOpen (picRankOneSplitLocus (C := C) (overSpec k A) lam.1) := by
  obtain ⟨P⟩ := PicRankOneNativeDatum.nonempty (C := C) pi lam
  let iota : A →ₐ[k] P.cover.Carrier :=
    (Algebra.ofId A P.cover.Carrier).restrictScalars k
  let f : overSpec k P.cover.Carrier ⟶ overSpec k A := Over.overSpecMap iota
  let mu : picEt C (overSpec k P.cover.Carrier) :=
    relPicToPicEt C (overSpec k P.cover.Carrier)
      (P.representative : relPic C (overSpec k P.cover.Carrier))
  have hmu : picEtMap C f lam.1 = mu := by
    exact picEtMap_eq_relPicToPicEt_of_affineRepresentative C lam.1 P.cover
      P.representative P.represents.symm
  have hfib : IsChartDatumPlusFibre C pi mu P.datum := by
    dsimp only [mu]
    rw [P.datum_class]
    exact isChartDatumPlusFibre_of_relPicToPicEt C pi
      P.datum.cechPicClass P.datum rfl
  have hopenCarrier : IsOpen (picRankOneSplitLocus (C := C)
      (overSpec k P.cover.Carrier) mu) := by
    exact isOpen_setOf_isSplitWitness_of_presentation C pi hpi
      (isChartDatumPresentation_of_plusFibre_tower C pi hfib)
  have hpre : picRankOneSplitLocus (C := C) (overSpec k P.cover.Carrier) mu =
      PrimeSpectrum.comap (algebraMap A P.cover.Carrier) ⁻¹'
        picRankOneSplitLocus (C := C) (overSpec k A) lam.1 := by
    rw [← hmu]
    exact picRankOneSplitLocus_map_eq_preimage pi f lam.1
  refine ((PrimeSpectrum.isQuotientMap_of_generalizingMap
    P.cover.comap_surjective ?_).isOpen_preimage).mp ?_
  · exact RingHom.Flat.generalizingMap_comap
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  · rwa [← hpre]

/-- The pointwise split locus of a genus-degree class on an arbitrary test scheme is open. -/
theorem isOpen_picRankOneSplitLocus
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (hpi : pi ≫ P1.structureMap k = C.hom)
    {T : Over (Spec (.of k))}
    (lam : picDegLayer C (genus C : ℤ) T) :
    IsOpen (picRankOneSplitLocus (C := C) T lam.1) := by
  rw [isOpen_iff_forall_mem_open]
  intro t ht
  obtain ⟨U, hUmem⟩ : ∃ U : T.left.affineOpens, t ∈ U.1 := by
    obtain ⟨U, hU, hmem, -⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.left.isBasis_affineOpens)
        (show t ∈ (⊤ : T.left.Opens) from trivial)
    exact ⟨⟨U, hU⟩, hmem⟩
  let lamU : picDegLayer C (genus C : ℤ)
      (overSpec k Γ(T.left, U.1)) :=
    (picDegLayerFunctor C (genus C : ℤ)).map
      (Over.fromSpecAffine T U).op lam
  have hopenU : IsOpen (picRankOneSplitLocus (C := C)
      (overSpec k Γ(T.left, U.1)) lamU.1) :=
    isOpen_picRankOneSplitLocus_overSpec pi hpi lamU
  have hpre : picRankOneSplitLocus (C := C)
        (overSpec k Γ(T.left, U.1)) lamU.1 =
      (Over.fromSpecAffine T U).left.base ⁻¹'
        picRankOneSplitLocus (C := C) T lam.1 := by
    change picRankOneSplitLocus (C := C)
        (overSpec k Γ(T.left, U.1))
          (picEtMap C (Over.fromSpecAffine T U) lam.1) = _
    exact picRankOneSplitLocus_map_eq_preimage pi
      (Over.fromSpecAffine T U) lam.1
  refine ⟨picRankOneSplitLocus (C := C) T lam.1 ∩ U.1,
    Set.inter_subset_left, ?_, ht, hUmem⟩
  have hoi : IsOpenImmersion (Over.fromSpecAffine T U).left :=
    U.2.isOpenImmersion_fromSpec
  have hrange : Set.range (Over.fromSpecAffine T U).left.base =
      (U.1 : Set T.left) := by
    change Set.range (U.2.fromSpec).base = _
    exact U.2.range_fromSpec
  have himg : (Over.fromSpecAffine T U).left.base ''
        picRankOneSplitLocus (C := C)
          (overSpec k Γ(T.left, U.1)) lamU.1 =
      picRankOneSplitLocus (C := C) T lam.1 ∩ U.1 := by
    rw [hpre, Set.image_preimage_eq_inter_range, hrange]
  rw [← himg]
  haveI := hoi
  exact (Over.fromSpecAffine T U).left.isOpenEmbedding.isOpenMap _ hopenU

/-- The pointwise split locus as an actual open subscheme of the test. -/
noncomputable def picRankOneSplitOpen
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (hpi : pi ≫ P1.structureMap k = C.hom)
    {T : Over (Spec (.of k))}
    (lam : picDegLayer C (genus C : ℤ) T) : T.left.Opens :=
  ⟨picRankOneSplitLocus (C := C) T lam.1,
    isOpen_picRankOneSplitLocus pi hpi lam⟩

/-- Pointwise splitting on an affine test supplies the complete native presentation of the
same displayed genus-degree class. -/
noncomputable def PicRankOneNativePresentation.of_pointwiseSplit
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (hpi : pi ≫ P1.structureMap k = C.hom)
    {A : Type u} [CommRing A] [Algebra k A]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (hsplit : ∀ t : (overSpec k A).left,
      IsSplitWitness C (picEtMap C (Over.testPoint t) lam.1)) :
    PicRankOneNativePresentation pi lam := by
  let P := (PicRankOneNativeDatum.nonempty (C := C) pi lam).some
  apply P.toNativePresentation_of_residueH1Witness hpi
  apply P.residueH1Witness_of_isSplitWitness
  intro t
  let iota : A →ₐ[k] P.cover.Carrier :=
    (Algebra.ofId A P.cover.Carrier).restrictScalars k
  let f : overSpec k P.cover.Carrier ⟶ overSpec k A := Over.overSpecMap iota
  let mu : picEt C (overSpec k P.cover.Carrier) :=
    relPicToPicEt C (overSpec k P.cover.Carrier)
      (P.representative : relPic C (overSpec k P.cover.Carrier))
  have hmu : picEtMap C f lam.1 = mu := by
    exact picEtMap_eq_relPicToPicEt_of_affineRepresentative C lam.1 P.cover
      P.representative P.represents.symm
  rw [show relPicToPicEt C (overSpec k P.cover.Carrier)
      (P.representative : relPic C (overSpec k P.cover.Carrier)) =
        picEtMap C f lam.1 from hmu.symm]
  have h := hsplit (f.left.base t)
  have hup := isSplitWitness_map_overSpecMap_of_algHom pi
    (Over.testPointFieldAlgHom f t)
    (picEtMap C (Over.testPoint (T := overSpec k A) (f.left.base t)) lam.1) h
  have hfac : picEtMap C (Over.testPoint t) (picEtMap C f lam.1) =
      picEtMap C (Over.overSpecMap (Over.testPointFieldAlgHom f t))
        (picEtMap C (Over.testPoint (T := overSpec k A) (f.left.base t)) lam.1) := by
    rw [← picEtMap_comp, ← picEtMap_comp, Over.testPoint_comp f t]
  rwa [hfac]

/-- Pointwise splitting on an affine test supplies a native presentation nonemptiness
certificate in the precise form consumed by the public rank-one locus. -/
theorem PicRankOneNativePresentation.nonempty_of_pointwiseSplit
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (hpi : pi ≫ P1.structureMap k = C.hom)
    {A : Type u} [CommRing A] [Algebra k A]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (hsplit : ∀ t : (overSpec k A).left,
      IsSplitWitness C (picEtMap C (Over.testPoint t) lam.1)) :
    Nonempty (PicRankOneNativePresentation pi lam) :=
  ⟨PicRankOneNativePresentation.of_pointwiseSplit pi hpi hsplit⟩

/-- A genus-degree class which is split at every point belongs to the public rank-one locus. -/
theorem mem_picRankOneOpen_of_pointwiseSplit
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (hpi : pi ≫ P1.structureMap k = C.hom)
    {T : Over (Spec (.of k))}
    (lam : picDegLayer C (genus C : ℤ) T)
    (hsplit : ∀ t : T.left,
      IsSplitWitness C (picEtMap C (Over.testPoint t) lam.1)) :
    lam ∈ (PicRankOneOpen pi).obj (op T) := by
  apply mem_picRankOneOpen_of_nativePresentations pi
  intro A _ _ t
  apply PicRankOneNativePresentation.nonempty_of_pointwiseSplit pi hpi
  intro q
  have hpre := picRankOneSplitLocus_map_eq_preimage pi t lam.1
  change q ∈ picRankOneSplitLocus (C := C) (overSpec k A)
    ((picDegLayerFunctor C (genus C : ℤ)).map t.op lam).1
  change q ∈ picRankOneSplitLocus (C := C) (overSpec k A)
    (picEtMap C t lam.1)
  rw [hpre]
  exact hsplit (t.left.base q)

/-- Restricting the universal element of a Yoneda family agrees with evaluating the family on
the restricting morphism. -/
private theorem sigmaExtension_universal_restrict
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (g : yoneda.obj X ⟶
      Over.sigmaExtension (Spec (.of k))
        (picDegLayerFunctor C (genus C : ℤ))) :
    (Over.sigmaExtension (Spec (.of k))
        (picDegLayerFunctor C (genus C : ℤ))).map f.op
          (g.app (op X) (𝟙 X)) =
      (yoneda.map f ≫ g).app (op Y) (𝟙 Y) := by
  change _ = g.app (op Y) f
  have hnat := ConcreteCategory.congr_hom (g.naturality f.op) (𝟙 X)
  change g.app (op Y) f = _ at hnat
  exact hnat.symm

/-- The inclusion of the rank-one subfunctor remains injective after `Σ`-extension. -/
private theorem picRankOneOpenSigmaIncl_app_injective
    (pi : C.left ⟶ P1 k) [IsFinite pi] (S : Scheme.{u}) :
    Function.Injective ((picRankOneOpenSigmaIncl pi).app (op S)) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  have hab : a = b := congrArg Sigma.fst h
  apply Over.sigmaExtension_ext (PicRankOneOpen pi).toFunctor hab
  apply Subtype.ext
  exact Over.sigmaExtension_snd_eq
    (picDegLayerFunctor C (genus C : ℤ)) hab h

set_option maxHeartbeats 800000 in
-- Dependent `Σ`-fibre equalities require extra elaboration budget.
/-- The pointwise split open represents the pullback of the public rank-one locus along an
arbitrary displayed family. -/
noncomputable def picRankOneOpen_fibrePresented
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (hpi : pi ≫ P1.structureMap k = C.hom)
    {X : Scheme.{u}}
    (g : yoneda.obj X ⟶
      Over.sigmaExtension (Spec (.of k))
        (picDegLayerFunctor C (genus C : ℤ))) :
    PicRankOneOpen.FibrePresented pi g := by
  rcases hgamma : g.app (op X) (𝟙 X) with ⟨a, lam⟩
  let T : Over (Spec (.of k)) := Over.mk a
  let W : X.Opens := picRankOneSplitOpen pi hpi lam
  let j : Over.mk (W.ι ≫ a) ⟶ T := Over.homMk W.ι rfl
  let lamW : picDegLayer C (genus C : ℤ) (Over.mk (W.ι ≫ a)) :=
    (picDegLayerFunctor C (genus C : ℤ)).map j.op lam
  have hsplitW : ∀ z : (W : Scheme.{u}),
      IsSplitWitness C (picEtMap C (Over.testPoint z) lamW.1) := by
    intro z
    change z ∈ picRankOneSplitLocus (C := C) (Over.mk (W.ι ≫ a)) lamW.1
    change z ∈ picRankOneSplitLocus (C := C) (Over.mk (W.ι ≫ a))
      (picEtMap C j lam.1)
    rw [picRankOneSplitLocus_map_eq_preimage pi j lam.1]
    change W.ι.base z ∈ (W : Set X)
    rw [← W.range_ι]
    exact Set.mem_range_self z
  have hmemW : lamW ∈ (PicRankOneOpen pi).obj (op (Over.mk (W.ι ≫ a))) :=
    mem_picRankOneOpen_of_pointwiseSplit pi hpi lamW hsplitW
  let valueW : (Over.sigmaExtension (Spec (.of k))
      (PicRankOneOpen pi).toFunctor).obj (op (W : Scheme.{u})) :=
    ⟨W.ι ≫ a, ⟨lamW, hmemW⟩⟩
  let fst : yoneda.obj (W : Scheme.{u}) ⟶
      Over.sigmaExtension (Spec (.of k)) (PicRankOneOpen pi).toFunctor :=
    yonedaEquiv.symm valueW
  have hsq : fst ≫ picRankOneOpenSigmaIncl pi = yoneda.map W.ι ≫ g := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, show fst = yonedaEquiv.symm valueW from rfl,
      Equiv.apply_symm_apply, yonedaEquiv_apply]
    change (⟨W.ι ≫ a, lamW⟩ :
        (Over.sigmaExtension (Spec (.of k))
          (picDegLayerFunctor C (genus C : ℤ))).obj (op (W : Scheme.{u}))) = _
    rw [← sigmaExtension_universal_restrict W.ι g, hgamma]
    exact (Over.sigmaExtension_map_left_mk j lam).symm
  refine
    { W := W
      fst := fst
      sq := hsq
      exists_factor := ?_ }
  intro S v w hvw
  rcases v with ⟨b, vlam⟩
  let jw : Over.mk (w ≫ a) ⟶ T := Over.homMk w rfl
  have hwval :
      (⟨b, (vlam.1 : picDegLayer C (genus C : ℤ) (Over.mk b))⟩ :
        (Over.sigmaExtension (Spec (.of k))
          (picDegLayerFunctor C (genus C : ℤ))).obj (op S)) =
      ⟨w ≫ a, (picDegLayerFunctor C (genus C : ℤ)).map jw.op lam⟩ := by
    change (⟨b, vlam.1⟩ : (Over.sigmaExtension (Spec (.of k))
      (picDegLayerFunctor C (genus C : ℤ))).obj (op S)) = g.app (op S) w at hvw
    have hrest := sigmaExtension_universal_restrict w g
    rw [hgamma] at hrest
    exact hvw.trans (hrest.symm.trans (Over.sigmaExtension_map_left_mk jw lam))
  have hb : b = w ≫ a := congrArg Sigma.fst hwval
  subst b
  have hlam : (picDegLayerFunctor C (genus C : ℤ)).map jw.op lam = vlam.1 := by
    exact (eq_of_heq (Sigma.mk.inj hwval).2).symm
  have hrange : Set.range w.base ⊆ (W : Set X) := by
    rintro _ ⟨s, rfl⟩
    change w.base s ∈ picRankOneSplitLocus (C := C) T lam.1
    have hs : s ∈ picRankOneSplitLocus (C := C) (Over.mk (w ≫ a))
        ((picDegLayerFunctor C (genus C : ℤ)).map jw.op lam).1 := by
      change IsSplitWitness C (picEtMap C (Over.testPoint s)
        ((picDegLayerFunctor C (genus C : ℤ)).map jw.op lam).1)
      rw [hlam]
      exact isSplitWitness_testPoint_of_mem pi vlam.2 s
    have hpre := picRankOneSplitLocus_map_eq_preimage pi jw lam.1
    change s ∈ picRankOneSplitLocus (C := C) (Over.mk (w ≫ a))
      (picEtMap C jw lam.1) at hs
    rw [hpre] at hs
    exact hs
  have hrange' : Set.range w.base ⊆ Set.range W.ι.base := by
    rwa [W.range_ι]
  let u : S ⟶ (W : Scheme.{u}) := IsOpenImmersion.lift W.ι w hrange'
  have hu : u ≫ W.ι = w := IsOpenImmersion.lift_fac W.ι w hrange'
  refine ⟨u, ?_, hu⟩
  apply picRankOneOpenSigmaIncl_app_injective pi S
  have happ := congrArg (fun q => q.app (op S) u) hsq
  change (picRankOneOpenSigmaIncl pi).app (op S) (fst.app (op S) u) =
      g.app (op S) (u ≫ W.ι) at happ
  rw [hu] at happ
  exact happ.trans hvw.symm

/-- The public rank-one Picard locus is relatively open. -/
theorem picRankOneOpen_isOpen
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (hpi : pi ≫ P1.structureMap k = C.hom) :
    PicRankOneOpen.IsOpen pi := by
  apply picRankOneOpen_isOpen_of_fibrePresented pi
  intro X g
  exact picRankOneOpen_fibrePresented pi hpi g

end

end AlgebraicGeometry
