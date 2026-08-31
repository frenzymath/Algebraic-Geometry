/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorSubschemeGlobal
import AlgebraicJacobian.Picard.DivisorSubschemeFinite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Faithful flatness of the intrinsic divisor's affine-piece cover

For an affine scheme, restriction to an affine open is flat.  A finite affine open cover
therefore gives a faithfully flat map from global functions to the product of the rings
of functions on the cover members.  Applying this to the intrinsic divisor of a certified
widened adaptation identifies that map with the existing inclusion
`gluedSubalgebra A → A.chartProd`.

The only certificate input is the existing finiteness clause used to make the intrinsic
divisor affine.  No containment, fixed-chart, or `SwallowedBy` hypothesis occurs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-- Restriction from an affine scheme to an affine open is a flat ring map. -/
theorem flat_globalRestriction_of_isAffineOpen
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsAffineOpen U) :
    (X.presheaf.map
      (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op).hom.Flat := by
  letI : IsAffine U := hU
  have hflat : U.ι.appTop.hom.Flat := U.ι.flat_appTop
  have hiso : U.topIso.hom.hom.Flat :=
    RingHom.Flat.of_bijective U.topIso.commRingCatIsoToRingEquiv.bijective
  rw [← show U.ι.appTop ≫ U.topIso.hom =
      X.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op by
    simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom,
      ← Functor.map_comp]
    congr 1]
  exact hflat.comp hiso

/-- The maps on prime spectra induced by the members of an affine open cover jointly
cover the spectrum of global functions. -/
theorem iUnion_range_comap_globalRestriction_eq_univ
    {X : Scheme.{u}} [IsAffine X] {ι : Type v}
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    ⋃ i, Set.range (PrimeSpectrum.comap
      (X.presheaf.map
        (homOfLE (le_top : U i ≤ (⊤ : X.Opens))).op).hom) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  let x : X := X.isoSpec.inv p
  obtain ⟨i, hxi⟩ := hcover x
  letI : IsAffine (U i) := hU i
  let y : (U i : Scheme) := ⟨x, hxi⟩
  let q0 : PrimeSpectrum Γ((U i : Scheme), ⊤) :=
    (U i : Scheme).isoSpec.hom y
  let q : PrimeSpectrum Γ(X, U i) :=
    PrimeSpectrum.comap (U i).topIso.inv.hom q0
  apply Set.mem_iUnion.mpr
  refine ⟨i, ⟨q, ?_⟩⟩
  rw [show q = PrimeSpectrum.comap (U i).topIso.inv.hom q0 from rfl]
  change (PrimeSpectrum.comap
      (X.presheaf.map
        (homOfLE (le_top : U i ≤ (⊤ : X.Opens))).op).hom ∘
    PrimeSpectrum.comap (U i).topIso.inv.hom) q0 = p
  rw [← PrimeSpectrum.comap_comp]
  have hres :
      (U i).ι.appTop ≫ (U i).topIso.hom =
        X.presheaf.map (homOfLE (le_top : U i ≤ (⊤ : X.Opens))).op := by
    simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom,
      ← Functor.map_comp]
    congr 1
  have hcompCat :
      X.presheaf.map (homOfLE (le_top : U i ≤ (⊤ : X.Opens))).op ≫
        (U i).topIso.inv = (U i).ι.appTop := by
    rw [← hres, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hcomp :
      (U i).topIso.inv.hom.comp
        (X.presheaf.map
          (homOfLE (le_top : U i ≤ (⊤ : X.Opens))).op).hom =
        (U i).ι.appTop.hom :=
    congrArg CommRingCat.Hom.hom hcompCat
  rw [hcomp]
  have hn := congrArg
    (fun f : (U i : Scheme) ⟶ Spec Γ(X, ⊤) => f y)
    (Scheme.isoSpec_hom_naturality (U i).ι)
  change PrimeSpectrum.comap (U i).ι.appTop.hom q0 = X.isoSpec.hom x at hn
  rw [hn]
  exact congrArg
    (fun f : Spec Γ(X, ⊤) ⟶ Spec Γ(X, ⊤) => f p)
    X.isoSpec.inv_hom_id

/-- A finite product of flat ring maps is faithfully flat when their maps on spectra
jointly cover the source spectrum. -/
theorem faithfullyFlat_pi_of_flat_of_iUnion_range_eq_univ
    {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
    {S : ι → Type u} [∀ i, CommRing (S i)]
    (f : ∀ i, R →+* S i) (hflat : ∀ i, (f i).Flat)
    (hcover : ⋃ i, Set.range (PrimeSpectrum.comap (f i)) = Set.univ) :
    (RingHom.pi f).FaithfullyFlat := by
  classical
  letI := Fintype.ofFinite ι
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  constructor
  · rw [RingHom.Flat]
    letI (i : ι) : Algebra R (S i) := (f i).toAlgebra
    letI (i : ι) : Module.Flat R (S i) := hflat i
    exact Module.Flat.of_linearEquiv
      (DFinsupp.linearEquivFunOnFintype (R := R) (M := S)).symm
  · rw [← Set.range_eq_univ,
      ← PrimeSpectrum.iUnion_range_comap_comp_evalRingHom (RingHom.pi f)]
    have hcomp : ∀ i,
        (Pi.evalRingHom S i).comp (RingHom.pi f) = f i := by
      intro i
      ext r
      rfl
    simp_rw [hcomp]
    exact hcover

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

/-- Global functions on a certified intrinsic divisor map faithfully flatly to the
product of its widened affine-piece colength rings. -/
theorem faithfullyFlat_divisorGlobalToPiecesRingHom [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n) :
    A.divisorGlobalToPiecesRingHom.FaithfullyFlat := by
  letI : IsAffine A.divisorSubscheme :=
    A.isAffine_divisorSubscheme hc
  let f : ∀ i : D.index,
      Γ(A.divisorSubscheme, ⊤) →+*
        Γ(A.divisorSubscheme, A.divisorSubschemeι ⁻¹ᵁ D.pieces i) :=
    fun i => (A.divisorSubscheme.presheaf.map
      (homOfLE (le_top :
        A.divisorSubschemeι ⁻¹ᵁ D.pieces i ≤
          (⊤ : A.divisorSubscheme.Opens))).op).hom
  have hflat : ∀ i, (f i).Flat :=
    fun i => flat_globalRestriction_of_isAffineOpen
      A.divisorSubscheme
      (A.divisorSubschemeι ⁻¹ᵁ D.pieces i)
      (A.isAffineOpen_divisorPiece i)
  have hcover :
      ⋃ i, Set.range (PrimeSpectrum.comap (f i)) = Set.univ :=
    iUnion_range_comap_globalRestriction_eq_univ
      (fun i => A.divisorSubschemeι ⁻¹ᵁ D.pieces i)
      (fun i => A.isAffineOpen_divisorPiece i)
      (fun x => by
        obtain ⟨i, hi⟩ := D.exists_mem_pieces (A.divisorSubschemeι x)
        exact ⟨i, hi⟩)
  have hff : (RingHom.pi f).FaithfullyFlat :=
    faithfullyFlat_pi_of_flat_of_iUnion_range_eq_univ f hflat hcover
  let e :
      (∀ i : D.index,
        Γ(A.divisorSubscheme, A.divisorSubschemeι ⁻¹ᵁ D.pieces i)) ≃+*
        A.chartProd :=
    RingEquiv.piCongrRight fun i => A.divisorSubschemePieceRingEquiv i
  have he : e.toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective e.bijective
  have hcomp :=
    RingHom.FaithfullyFlat.stableUnderComposition
      (RingHom.pi f) e.toRingHom hff he
  rw [show e.toRingHom.comp (RingHom.pi f) =
      A.divisorGlobalToPiecesRingHom by
    ext s i
    rfl] at hcomp
  exact hcomp

/-- The intrinsic widened equalizer algebra includes faithfully flatly into the product
of its affine-piece colength rings. -/
theorem faithfullyFlat_gluedSubalgebra_val [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n) :
    (gluedSubalgebra A).val.toRingHom.FaithfullyFlat := by
  have hglobal := A.faithfullyFlat_divisorGlobalToPiecesRingHom hc
  have he :
      A.divisorGlobalSectionsEquivGlued.symm.toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective
      A.divisorGlobalSectionsEquivGlued.symm.bijective
  have hcomp :=
    RingHom.FaithfullyFlat.stableUnderComposition
      A.divisorGlobalSectionsEquivGlued.symm.toRingHom
      A.divisorGlobalToPiecesRingHom he hglobal
  rw [show A.divisorGlobalToPiecesRingHom.comp
      A.divisorGlobalSectionsEquivGlued.symm.toRingHom =
      (gluedSubalgebra A).val.toRingHom by
    ext x i
    change
      (A.divisorGlobalSectionsEquivGlued
        (A.divisorGlobalSectionsEquivGlued.symm x)).1 i = x.1 i
    rw [RingEquiv.apply_symm_apply]] at hcomp
  exact hcomp

/-- The certified affine-piece product is finite over the widened equalizer algebra. -/
theorem IsCertified.finite_gluedSubalgebra_val
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n) :
    (gluedSubalgebra A).val.toRingHom.Finite := by
  letI : ∀ i : D.index, Module.Finite R (A.colength i) :=
    fun i => hc.finite_colength i
  letI : Module.Finite R A.chartProd := Module.Finite.pi
  apply RingHom.Finite.of_comp_finite
    (f := algebraMap R ↥(gluedSubalgebra A))
  rw [show (gluedSubalgebra A).val.toRingHom.comp
      (algebraMap R ↥(gluedSubalgebra A)) =
      algebraMap R A.chartProd by
    ext r i
    rfl]
  exact RingHom.finite_algebraMap.mpr inferInstance

/-! ## Certified pieces are clopen -/

/-- A certified divisor piece is finite over the whole intrinsic divisor.  Indeed, both
the piece and the divisor are finite over the test base, and the latter structure morphism
is separated. -/
theorem IsCertified.isFinite_divisorPieceMap [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n)
    (i : D.index) : IsFinite (A.divisorPieceMap i) := by
  haveI : IsFinite A.divisorSubschemeOver.hom :=
    A.isFinite_divisorSubschemeOver hc
  haveI : IsFinite
      (A.divisorPieceMap i ≫ A.divisorSubschemeOver.hom) := by
    rw [A.divisorPieceMap_over i]
    apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr (hc.finite_colength i)
  exact IsFinite.of_comp (A.divisorPieceMap i)
    A.divisorSubschemeOver.hom

/-- Each certified divisor piece is also a closed subscheme of the intrinsic divisor:
its map is finite and, as an open immersion, a monomorphism. -/
theorem IsCertified.isClosedImmersion_divisorPieceMap [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n)
    (i : D.index) : IsClosedImmersion (A.divisorPieceMap i) := by
  apply (IsClosedImmersion.iff_isFinite_and_mono _).mpr
  exact ⟨hc.isFinite_divisorPieceMap A i, inferInstance⟩

/-- The inverse image of a certified adapted piece is clopen in the intrinsic divisor. -/
theorem IsCertified.isClopen_divisorPiece [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n)
    (i : D.index) :
    IsClopen (A.divisorSubschemeι ⁻¹ᵁ D.pieces i :
      Set A.divisorSubscheme) := by
  rw [← A.opensRange_divisorPieceMap i]
  haveI : IsClosedImmersion (A.divisorPieceMap i) :=
    hc.isClosedImmersion_divisorPieceMap A i
  exact ⟨(A.divisorPieceMap i).isClosedEmbedding.isClosed_range,
    (A.divisorPieceMap i).isOpenEmbedding.isOpen_range⟩

/-- The open immersion of a certified divisor piece is itself a closed immersion. -/
theorem IsCertified.isClosedImmersion_divisorPieceOpen [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n)
    (i : D.index) :
    IsClosedImmersion
      (A.divisorSubschemeι ⁻¹ᵁ D.pieces i).ι := by
  let U : A.divisorSubscheme.Opens :=
    A.divisorSubschemeι ⁻¹ᵁ D.pieces i
  have hrange : Set.range (A.divisorPieceMap i) = Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact congrArg Opens.carrier (A.opensRange_divisorPieceMap i)
  let e := IsOpenImmersion.isoOfRangeEq (A.divisorPieceMap i) U.ι hrange
  rw [← MorphismProperty.cancel_left_of_respectsIso
    (P := @IsClosedImmersion) e.hom]
  rw [IsOpenImmersion.isoOfRangeEq_hom_fac]
  exact hc.isClosedImmersion_divisorPieceMap A i

/-- Restriction of global functions to a certified divisor piece is surjective. -/
theorem IsCertified.surjective_divisorGlobalRestriction [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n)
    (i : D.index) :
    Function.Surjective
      (A.divisorSubscheme.presheaf.map
        (homOfLE (le_top :
          A.divisorSubschemeι ⁻¹ᵁ D.pieces i ≤
            (⊤ : A.divisorSubscheme.Opens))).op).hom := by
  letI : IsAffine A.divisorSubscheme :=
    A.isAffine_divisorSubscheme hc
  let U : A.divisorSubscheme.Opens :=
    A.divisorSubschemeι ⁻¹ᵁ D.pieces i
  haveI : IsClosedImmersion U.ι :=
    hc.isClosedImmersion_divisorPieceOpen A i
  have happ : Function.Surjective U.ι.appTop.hom :=
    U.ι.app_surjective ⊤ (isAffineOpen_top A.divisorSubscheme)
  have hiso : Function.Surjective U.topIso.hom.hom :=
    (ConcreteCategory.bijective_of_isIso U.topIso.hom).surjective
  rw [← show U.ι.appTop ≫ U.topIso.hom =
      A.divisorSubscheme.presheaf.map
        (homOfLE (le_top :
          A.divisorSubschemeι ⁻¹ᵁ D.pieces i ≤
            (⊤ : A.divisorSubscheme.Opens))).op by
    simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom,
      ← Functor.map_comp]
    congr 1]
  exact hiso.comp happ

/-- Every certified divisor-piece component of the global restriction map is
surjective. -/
theorem IsCertified.surjective_divisorGlobalToPiece [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n)
    (i : D.index) :
    Function.Surjective (fun s : Γ(A.divisorSubscheme, ⊤) =>
      A.divisorGlobalToPiecesRingHom s i) := by
  intro x
  obtain ⟨t, rfl⟩ :=
    (A.divisorSubschemePieceRingEquiv i).surjective x
  obtain ⟨s, hs⟩ := hc.surjective_divisorGlobalRestriction A i t
  exact ⟨s, congrArg (A.divisorSubschemePieceRingEquiv i) hs⟩

/-- Evaluation from the widened equalizer algebra onto every certified colength piece
is surjective. -/
theorem IsCertified.surjective_gluedSubalgebraPieceMap [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n)
    (i : D.index) :
    Function.Surjective (A.gluedSubalgebraPieceMap i) := by
  intro x
  obtain ⟨s, hs⟩ := hc.surjective_divisorGlobalToPiece A i x
  exact ⟨A.divisorGlobalSectionsEquivGlued s, hs⟩

end AffAdaptation

end AlgebraicGeometry
