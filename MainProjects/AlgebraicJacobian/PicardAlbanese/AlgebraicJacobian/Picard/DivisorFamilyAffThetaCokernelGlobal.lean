/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffFibreData
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaKernelGlobal
import AlgebraicJacobian.Picard.DivisorThetaSheafSequence
import AlgebraicJacobian.Picard.DivSchemeCertificateEngine

/-!
# The global theta cokernel and the widened intrinsic range

A widened certificate supplies fibrewise vanishing for `O(a Theta - d)`.  After choosing
an auxiliary chart presentation of the same local equations, the existing rigid engine
turns those witnesses into vanishing of the first cohomology of its theta-ideal sheaf.
The canonical sheaf inclusion from `DivisorThetaSheafSequence` therefore has a surjective
cokernel projection on global sections.

The range of that inclusion on global sections is exactly the cover-independent vanishing
submodule.  Hence the cokernel is canonically the same quotient already identified with
the range of intrinsic widened theta evaluation.  No chart typing of the widened cover and
no additional hypothesis occur.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (π : C.left ⟶ P1 k) [IsFinite π]

attribute [local instance] instOverCleftWFT

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations}

/-- On global sections, the sheaf inclusion is the established junction from the
theta-ideal datum to the cover-independent vanishing submodule. -/
theorem thetaIdealInclApp_top_eq_gluedToVanishing (B : DivisorAdaptation C R π d)
    (a : ℕ) (s : B.ThetaIdealSections a ⊤) :
    B.thetaIdealInclApp (a := a) ⊤ s =
      ((B.gluedToVanishingₗ a s :
        d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
          (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a)) :
        relThetaSections C R π a) := by
  rfl

/-- The pointwise range of the theta-ideal sheaf inclusion on global sections is exactly
the intrinsic, cover-independent divisor-family vanishing submodule. -/
theorem range_thetaIdealInclApp_top (B : DivisorAdaptation C R π d) (a : ℕ) :
    LinearMap.range (B.thetaIdealInclApp (a := a) ⊤) =
      d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    rw [thetaIdealInclApp_top_eq_gluedToVanishing C R π B a s]
    exact (B.gluedToVanishingₗ a s).property
  · intro hx
    let y : ↥(d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a)) := ⟨x, hx⟩
    refine ⟨(B.gluedEquivVanishing a).symm y, ?_⟩
    rw [thetaIdealInclApp_top_eq_gluedToVanishing C R π B]
    exact congrArg Subtype.val ((B.gluedEquivVanishing a).apply_symm_apply y)

/-! ## The local cokernel kernel

The arbitrary-open range producer immediately gives the corresponding kernel fact for
the sheaf cokernel.  Keeping this at an arbitrary open is useful when the intrinsic
descent proof compares restrictions before specializing to `⊤`.
-/

theorem cokernelπ_app_eq_zero_of_germ_mem (B : DivisorAdaptation C R π d)
    {a : ℕ} {W : (relCurve C R).Opens}
    (x : (relThetaTwistSheaf C R π a).obj.obj (op W))
    (hx0 : ∀ (z : relCurve C R) (hz : z ∈ W ⊓
      (relCover C R (fiberTwoCover π)).V₀),
      ((relCurve C R).presheaf.germ (W ⊓
        (relCover C R (fiberTwoCover π)).V₀) z hz).hom x.val.1 ∈ d.stalkIdeal z)
    (hx1 : ∀ (z : relCurve C R) (hz : z ∈ W ⊓
      (relCover C R (fiberTwoCover π)).V₁),
      ((relCurve C R).presheaf.germ (W ⊓
        (relCover C R (fiberTwoCover π)).V₁) z hz).hom x.val.2 ∈ d.stalkIdeal z) :
    ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app (op W)).hom x = 0 := by
  obtain ⟨s, hs⟩ := B.exists_thetaIdealInclApp_of_germ_mem (a := a) x hx0 hx1
  rw [← hs]
  have hnat := congrArg
    (fun f : (B.thetaIdealDatum a).sheaf ⟶ cokernel (B.thetaIdealIncl (a := a)) =>
      f.hom.app (op W)) (cokernel.condition (B.thetaIdealIncl (a := a)))
  have hlin := congrArg ModuleCat.Hom.hom hnat
  exact LinearMap.congr_fun hlin s

end DivisorAdaptation

/-! ## Restriction through the glued--twist equivalence -/

/-- Restricting a global twisted theta section after converting it to the glued
presentation is the same as restricting it directly in the twisted sheaf. -/
theorem gluedTwistEquiv_res_top_symm (a : ℕ)
    (W : (relCurve C R).Opens) (x : relThetaSections C R π a) :
    gluedTwistEquiv C R π a W
        (secRes (thetaChartDatum C R π a).sheaf
          (le_top : W ≤ (⊤ : (relCurve C R).Opens))
          ((gluedTwistEquiv C R π a (⊤ : (relCurve C R).Opens)).symm x)) =
      secRes (relThetaTwistSheaf C R π a)
        (le_top : W ≤ (⊤ : (relCurve C R).Opens)) x := by
  change gluedToTwistApp C R π a W
      (gluedRes R (thetaChartDatum C R π a).pieces
        (thetaChartDatum C R π a).unit le_top
        ((gluedTwistEquiv C R π a (⊤ : (relCurve C R).Opens)).symm x)) =
    twistRes R (relCover C R (fiberTwoCover π)).V₀
      (relCover C R (fiberTwoCover π)).V₁
      (relThetaCocycle C R π a) le_top x
  rw [gluedToTwistApp_res]
  change twistRes R (relCover C R (fiberTwoCover π)).V₀
      (relCover C R (fiberTwoCover π)).V₁
      (relThetaCocycle C R π a) le_top
      ((gluedTwistEquiv C R π a (⊤ : (relCurve C R).Opens))
        ((gluedTwistEquiv C R π a (⊤ : (relCurve C R).Opens)).symm x)) =
    twistRes R (relCover C R (fiberTwoCover π)).V₀
      (relCover C R (fiberTwoCover π)).V₁
      (relThetaCocycle C R π a) le_top x
  rw [LinearEquiv.apply_symm_apply]

section CokernelGlobal

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [IsDominant π] [IsIntegral C.left]

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]

namespace AffAdaptation

/-- A widened high-window certificate produces an auxiliary chart presentation of the
same equations whose theta-ideal sheaf has vanishing first cohomology. -/
theorem IsCertified.exists_chartAdaptation_subsingleton_thetaIdealH1
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {a : ℕ} (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    ∃ B : DivisorAdaptation C R π d,
      Subsingleton (Sheaf.HModule (B.thetaIdealDatum a).sheaf 1) := by
  obtain ⟨B⟩ := exists_divisorAdaptation C R π d
  refine ⟨B, (subsingleton_datumPair_h1_iff (B.thetaIdealDatum a)).mp
    (datum_subsingleton_pairH1 (B.thetaIdealDatum a) hπ ?_)⟩
  apply B.thetaIdealDatum_hfib_of_witness a
  intro p
  obtain ⟨W, hWclass, hWH1⟩ :=
    hc.fibrewise_thetaSub_h1_witness C R π hπ hO hχ ha1 hMa p
  refine ⟨W, ?_, hWH1⟩
  rw [BasicOpenCocycleDatum.cechPicClass_baseChange,
    B.cechPicClass_thetaIdealDatum]
  exact hWclass

/-- The auxiliary theta-ideal `H¹` vanishing producer with the curve parameter
`gamma` independent of the certified divisor degree `g`. -/
theorem IsCertified.exists_chartAdaptation_subsingleton_thetaIdealH1_at
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g gamma : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {a : ℕ} (hMa : windowM_choice π hπ g ≤ a) :
    ∃ B : DivisorAdaptation C R π d,
      Subsingleton (Sheaf.HModule (B.thetaIdealDatum a).sheaf 1) := by
  obtain ⟨B⟩ := exists_divisorAdaptation C R π d
  refine ⟨B, (subsingleton_datumPair_h1_iff (B.thetaIdealDatum a)).mp
    (datum_subsingleton_pairH1 (B.thetaIdealDatum a) hπ ?_)⟩
  apply B.thetaIdealDatum_hfib_of_witness a
  intro p
  obtain ⟨W, hWclass, hWH1⟩ :=
    hc.fibrewise_thetaSub_h1_witness_at C R π hπ hgamma hχ hMa p
  refine ⟨W, ?_, hWH1⟩
  rw [BasicOpenCocycleDatum.cechPicClass_baseChange,
    B.cechPicClass_thetaIdealDatum]
  exact hWclass

/-- The same producer in the form consumed by the global cokernel projection. -/
theorem IsCertified.exists_chartAdaptation_thetaIdealCokernel_app_top_surjective
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {a : ℕ} (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    ∃ B : DivisorAdaptation C R π d,
      Function.Surjective
        ((cokernel.π (DivisorAdaptation.thetaIdealIncl (A := B) (a := a))).hom.app
          (op (⊤ : (relCurve C R).Opens))).hom := by
  obtain ⟨B, hB⟩ := hc.exists_chartAdaptation_subsingleton_thetaIdealH1
    C R π hπ hO hχ ha1 hMa
  letI : Subsingleton (Sheaf.HModule (B.thetaIdealDatum a).sheaf 1) := hB
  exact ⟨B, B.thetaIdealCokernel_app_top_surjective⟩

/-- The global theta-cokernel surjectivity producer with independent curve and divisor
parameters. -/
theorem IsCertified.exists_chartAdaptation_thetaIdealCokernel_app_top_surjective_at
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g gamma : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {a : ℕ} (hMa : windowM_choice π hπ g ≤ a) :
    ∃ B : DivisorAdaptation C R π d,
      Function.Surjective
        ((cokernel.π (DivisorAdaptation.thetaIdealIncl (A := B) (a := a))).hom.app
          (op (⊤ : (relCurve C R).Opens))).hom := by
  obtain ⟨B, hB⟩ := hc.exists_chartAdaptation_subsingleton_thetaIdealH1_at
    C R π hπ hgamma hχ hMa
  letI : Subsingleton (Sheaf.HModule (B.thetaIdealDatum a).sheaf 1) := hB
  exact ⟨B, B.thetaIdealCokernel_app_top_surjective⟩

end AffAdaptation

end CokernelGlobal

section CokernelDescent

variable [IsProper C.hom]

namespace AffAdaptation

attribute [local instance] thetaPieceSectionsModule thetaOverlapSectionsModule
  thetaPieceQuotientModule thetaOverlapQuotientModule

/-! ## Overlap vanishing in the theta cokernel

The intrinsic overlap ideal is detected germwise by the widened kernel theorem.  After
the glued--twist conversion, its two pinned components therefore lie in the kernel of
the auxiliary theta-ideal cokernel on the overlap.
-/

theorem thetaOverlapVanishing_gluedTwist_cokernel_eq_zero
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} (B : DivisorAdaptation C R π d) (a : ℕ)
    (i j : D.index)
    (v : A.ThetaOverlapSections (π := π) a i j)
    (hv : v ∈ A.thetaOverlapVanishing (π := π) a i j) :
    ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
      (op (D.pieces i ⊓ D.pieces j))).hom
      (gluedTwistEquiv C R π a (D.pieces i ⊓ D.pieces j) v) = 0 := by
  let W := D.pieces i ⊓ D.pieces j
  have h := (A.mem_thetaOverlapVanishing_iff_forall_germ (π := π) a i j v).mp hv
  have hx :
      (∀ (z : relCurve C R) (hz : z ∈ W ⊓
        (relCover C R (fiberTwoCover π)).V₀),
        ((relCurve C R).presheaf.germ (W ⊓
          (relCover C R (fiberTwoCover π)).V₀) z hz).hom
            (gluedTwistEquiv C R π a W v).val.1 ∈ d.stalkIdeal z) ∧
      (∀ (z : relCurve C R) (hz : z ∈ W ⊓
        (relCover C R (fiberTwoCover π)).V₁),
        ((relCurve C R).presheaf.germ (W ⊓
          (relCover C R (fiberTwoCover π)).V₁) z hz).hom
            (gluedTwistEquiv C R π a W v).val.2 ∈ d.stalkIdeal z) := by
    constructor
    · intro z hz
      have hswap :
          ((relCurve C R).presheaf.germ
            (W ⊓ (relCover C R (fiberTwoCover π)).V₀) z hz).hom
              ((relCurve C R).resHom
                (inf_le_inf_left W
                  (thetaChartCover_pieces_inl C R π PUnit.unit).ge)
                (v.val (Sum.inl PUnit.unit))) =
            ((relCurve C R).presheaf.germ
              (W ⊓ (thetaChartDatum C R π a).pieces (Sum.inl PUnit.unit)) z
              ⟨hz.1, (thetaChartCover_pieces_inl C R π PUnit.unit).ge hz.2⟩).hom
                (v.val (Sum.inl PUnit.unit)) :=
        TopCat.Presheaf.germ_res_apply _ _ _ _ _
      change ((relCurve C R).presheaf.germ
        (W ⊓ (relCover C R (fiberTwoCover π)).V₀) z hz).hom
          ((relCurve C R).resHom
            (inf_le_inf_left W (thetaChartCover_pieces_inl C R π PUnit.unit).ge)
            (v.val (Sum.inl PUnit.unit))) ∈ d.stalkIdeal z
      rw [hswap]
      exact h (Sum.inl PUnit.unit) z
        ⟨hz.1, (thetaChartCover_pieces_inl C R π PUnit.unit).ge hz.2⟩
    · intro z hz
      have hswap :
          ((relCurve C R).presheaf.germ
            (W ⊓ (relCover C R (fiberTwoCover π)).V₁) z hz).hom
              ((relCurve C R).resHom
                (inf_le_inf_left W
                  (thetaChartCover_pieces_inr C R π PUnit.unit).ge)
                (v.val (Sum.inr PUnit.unit))) =
            ((relCurve C R).presheaf.germ
              (W ⊓ (thetaChartDatum C R π a).pieces (Sum.inr PUnit.unit)) z
              ⟨hz.1, (thetaChartCover_pieces_inr C R π PUnit.unit).ge hz.2⟩).hom
                (v.val (Sum.inr PUnit.unit)) :=
        TopCat.Presheaf.germ_res_apply _ _ _ _ _
      change ((relCurve C R).presheaf.germ
        (W ⊓ (relCover C R (fiberTwoCover π)).V₁) z hz).hom
          ((relCurve C R).resHom
            (inf_le_inf_left W (thetaChartCover_pieces_inr C R π PUnit.unit).ge)
            (v.val (Sum.inr PUnit.unit))) ∈ d.stalkIdeal z
      rw [hswap]
      exact h (Sum.inr PUnit.unit) z
        ⟨hz.1, (thetaChartCover_pieces_inr C R π PUnit.unit).ge hz.2⟩
  exact DivisorAdaptation.cokernelπ_app_eq_zero_of_germ_mem C R π B
    (gluedTwistEquiv C R π a W v) hx.1 hx.2

/-! ## Cokernel compatibility of intrinsic representatives

The equalizer relation on two piece representatives is a quotient equality on the
overlap.  The preceding overlap-kernel producer turns that quotient equality into
equality after passage to the auxiliary theta cokernel.
-/

theorem thetaPieceCokernel_eq_of_overlap_eq
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} (B : DivisorAdaptation C R π d) (a : ℕ)
    (i j : D.index)
    (si : A.ThetaPieceSections (π := π) a i)
    (sj : A.ThetaPieceSections (π := π) a j)
    (hij : A.thetaToOverlapLeft (π := π) a i j
        (Submodule.Quotient.mk si : A.ThetaPieceQuotient (π := π) a i) =
      A.thetaToOverlapRight (π := π) a i j
        (Submodule.Quotient.mk sj : A.ThetaPieceQuotient (π := π) a j)) :
    ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
      (op (D.pieces i ⊓ D.pieces j))).hom
      (gluedTwistEquiv C R π a (D.pieces i ⊓ D.pieces j)
        (secRes (thetaChartDatum C R π a).sheaf inf_le_left si)) =
    ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
      (op (D.pieces i ⊓ D.pieces j))).hom
      (gluedTwistEquiv C R π a (D.pieces i ⊓ D.pieces j)
        (secRes (thetaChartDatum C R π a).sheaf inf_le_right sj)) := by
  let sleft := secRes (thetaChartDatum C R π a).sheaf
    (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) si
  let sright := secRes (thetaChartDatum C R π a).sheaf
    (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j) sj
  have hq :
      (Submodule.Quotient.mk sleft : A.ThetaOverlapQuotient (π := π) a i j) =
        (Submodule.Quotient.mk sright : A.ThetaOverlapQuotient (π := π) a i j) := by
    simpa only [sleft, sright, A.thetaToOverlapLeft_mk, A.thetaToOverlapRight_mk] using hij
  have hv : sleft - sright ∈ A.thetaOverlapVanishing (π := π) a i j :=
    (Submodule.Quotient.eq (A.thetaOverlapVanishing (π := π) a i j)).mp hq
  have hz := A.thetaOverlapVanishing_gluedTwist_cokernel_eq_zero C R π B a i j
    (sleft - sright) hv
  have htw :
      gluedTwistEquiv C R π a (D.pieces i ⊓ D.pieces j) (sleft - sright) =
        gluedTwistEquiv C R π a (D.pieces i ⊓ D.pieces j) sleft -
          gluedTwistEquiv C R π a (D.pieces i ⊓ D.pieces j) sright :=
    (gluedTwistEquiv C R π a (D.pieces i ⊓ D.pieces j)).map_sub sleft sright
  rw [htw] at hz
  have hmap :
      ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
          (op (D.pieces i ⊓ D.pieces j))).hom
          (gluedTwistEquiv C R π a (D.pieces i ⊓ D.pieces j) sleft -
            gluedTwistEquiv C R π a (D.pieces i ⊓ D.pieces j) sright) =
        ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
          (op (D.pieces i ⊓ D.pieces j))).hom
          (gluedTwistEquiv C R π a (D.pieces i ⊓ D.pieces j) sleft) -
          ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
            (op (D.pieces i ⊓ D.pieces j))).hom
            (gluedTwistEquiv C R π a (D.pieces i ⊓ D.pieces j) sright) := by
    exact map_sub _ _ _
  have hzero :
      ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
          (op (D.pieces i ⊓ D.pieces j))).hom
          (gluedTwistEquiv C R π a (D.pieces i ⊓ D.pieces j) sleft) -
          ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
            (op (D.pieces i ⊓ D.pieces j))).hom
            (gluedTwistEquiv C R π a (D.pieces i ⊓ D.pieces j) sright) = 0 := by
    rw [← hmap]
    exact hz
  exact sub_eq_zero.mp hzero

/-! ## Piecewise exactness of the auxiliary cokernel

The pointwise cokernel kernel is exactly the equation-generated theta submodule on each
widened piece.  This is the local converse needed when a glued cokernel lift is compared
back with chosen intrinsic representatives.
-/

omit [IsProper C.hom] in
theorem thetaPieceVanishing_iff_gluedTwist_cokernel_eq_zero
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} (B : DivisorAdaptation C R π d) (a : ℕ)
    (j : D.index) (v : A.ThetaPieceSections (π := π) a j) :
    v ∈ A.thetaPieceVanishing (π := π) a j ↔
      ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
        (op (D.pieces j))).hom
        (gluedTwistEquiv C R π a (D.pieces j) v) = 0 := by
  let W := D.pieces j
  constructor
  · intro hv
    have h := (A.mem_thetaPieceVanishing_iff_forall_germ (π := π) a j v).mp hv
    have hx :
        (∀ (z : relCurve C R) (hz : z ∈ W ⊓
          (relCover C R (fiberTwoCover π)).V₀),
          ((relCurve C R).presheaf.germ (W ⊓
            (relCover C R (fiberTwoCover π)).V₀) z hz).hom
              (gluedTwistEquiv C R π a W v).val.1 ∈ d.stalkIdeal z) ∧
        (∀ (z : relCurve C R) (hz : z ∈ W ⊓
          (relCover C R (fiberTwoCover π)).V₁),
          ((relCurve C R).presheaf.germ (W ⊓
            (relCover C R (fiberTwoCover π)).V₁) z hz).hom
              (gluedTwistEquiv C R π a W v).val.2 ∈ d.stalkIdeal z) := by
      constructor
      · intro z hz
        have hswap :
            ((relCurve C R).presheaf.germ
              (W ⊓ (relCover C R (fiberTwoCover π)).V₀) z hz).hom
                ((relCurve C R).resHom
                  (inf_le_inf_left W
                    (thetaChartCover_pieces_inl C R π PUnit.unit).ge)
                  (v.val (Sum.inl PUnit.unit))) =
              ((relCurve C R).presheaf.germ
                (W ⊓ (thetaChartDatum C R π a).pieces (Sum.inl PUnit.unit)) z
                ⟨hz.1, (thetaChartCover_pieces_inl C R π PUnit.unit).ge hz.2⟩).hom
                  (v.val (Sum.inl PUnit.unit)) :=
          TopCat.Presheaf.germ_res_apply _ _ _ _ _
        change ((relCurve C R).presheaf.germ
          (W ⊓ (relCover C R (fiberTwoCover π)).V₀) z hz).hom
            ((relCurve C R).resHom
              (inf_le_inf_left W (thetaChartCover_pieces_inl C R π PUnit.unit).ge)
              (v.val (Sum.inl PUnit.unit))) ∈ d.stalkIdeal z
        rw [hswap]
        exact h (Sum.inl PUnit.unit) z
          ⟨hz.1, (thetaChartCover_pieces_inl C R π PUnit.unit).ge hz.2⟩
      · intro z hz
        have hswap :
            ((relCurve C R).presheaf.germ
              (W ⊓ (relCover C R (fiberTwoCover π)).V₁) z hz).hom
                ((relCurve C R).resHom
                  (inf_le_inf_left W
                    (thetaChartCover_pieces_inr C R π PUnit.unit).ge)
                  (v.val (Sum.inr PUnit.unit))) =
              ((relCurve C R).presheaf.germ
                (W ⊓ (thetaChartDatum C R π a).pieces (Sum.inr PUnit.unit)) z
                ⟨hz.1, (thetaChartCover_pieces_inr C R π PUnit.unit).ge hz.2⟩).hom
                  (v.val (Sum.inr PUnit.unit)) :=
          TopCat.Presheaf.germ_res_apply _ _ _ _ _
        change ((relCurve C R).presheaf.germ
          (W ⊓ (relCover C R (fiberTwoCover π)).V₁) z hz).hom
            ((relCurve C R).resHom
              (inf_le_inf_left W (thetaChartCover_pieces_inr C R π PUnit.unit).ge)
              (v.val (Sum.inr PUnit.unit))) ∈ d.stalkIdeal z
        rw [hswap]
        exact h (Sum.inr PUnit.unit) z
          ⟨hz.1, (thetaChartCover_pieces_inr C R π PUnit.unit).ge hz.2⟩
    exact DivisorAdaptation.cokernelπ_app_eq_zero_of_germ_mem C R π B
      (gluedTwistEquiv C R π a W v) hx.1 hx.2
  · intro hv
    have hker :
        gluedTwistEquiv C R π a W v ∈
          LinearMap.ker (((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
            (op W)).hom) := (LinearMap.mem_ker).mpr hv
    rw [CategoryTheory.Sheaf.ker_cokernelπ_app_eq_range
      (B.thetaIdealIncl (a := a)) (op W)] at hker
    rw [DivisorAdaptation.thetaIdealIncl_app] at hker
    have hgerm :=
      (B.mem_range_thetaIdealInclApp_iff_germ_mem
        (a := a) (gluedTwistEquiv C R π a W v)).mp hker
    apply (A.mem_thetaPieceVanishing_iff_forall_germ (π := π) a j v).mpr
    rintro (q | q) z hz
    · cases q
      have hswap :
          ((relCurve C R).presheaf.germ
            (W ⊓ (relCover C R (fiberTwoCover π)).V₀) z
              ⟨hz.1, thetaChartCover_pieces_le_inl C R π PUnit.unit hz.2⟩).hom
              ((relCurve C R).resHom
                (inf_le_inf_left W
                  (thetaChartCover_pieces_inl C R π PUnit.unit).ge)
                (v.val (Sum.inl PUnit.unit))) =
            ((relCurve C R).presheaf.germ
              (W ⊓ (thetaChartDatum C R π a).pieces (Sum.inl PUnit.unit))
              z hz).hom (v.val (Sum.inl PUnit.unit)) :=
        TopCat.Presheaf.germ_res_apply _ _ _ _ _
      rw [← hswap]
      exact hgerm.1 z
        ⟨hz.1, thetaChartCover_pieces_le_inl C R π PUnit.unit hz.2⟩
    · cases q
      have hswap :
          ((relCurve C R).presheaf.germ
            (W ⊓ (relCover C R (fiberTwoCover π)).V₁) z
              ⟨hz.1, thetaChartCover_pieces_le_inr C R π PUnit.unit hz.2⟩).hom
              ((relCurve C R).resHom
                (inf_le_inf_left W
                  (thetaChartCover_pieces_inr C R π PUnit.unit).ge)
                (v.val (Sum.inr PUnit.unit))) =
            ((relCurve C R).presheaf.germ
              (W ⊓ (thetaChartDatum C R π a).pieces (Sum.inr PUnit.unit))
              z hz).hom (v.val (Sum.inr PUnit.unit)) :=
        TopCat.Presheaf.germ_res_apply _ _ _ _ _
      rw [← hswap]
      exact hgerm.2 z
        ⟨hz.1, thetaChartCover_pieces_le_inr C R π PUnit.unit hz.2⟩

omit [IsProper C.hom] in
/-- If the restriction of a global auxiliary cokernel class agrees with the class of a
chosen theta representative on one widened piece, then the restricted global theta
section and that representative define the same intrinsic piece quotient class. -/
theorem thetaPieceQuotient_eq_of_global_cokernel_restriction
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} (B : DivisorAdaptation C R π d) (a : ℕ)
    (j : D.index) (x : relThetaSections C R π a)
    (rj : A.ThetaPieceSections (π := π) a j)
    (hlocal :
      secRes (cokernel (B.thetaIdealIncl (a := a)))
        (le_top : D.pieces j ≤ (⊤ : (relCurve C R).Opens))
        (((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
          (op (⊤ : (relCurve C R).Opens))).hom x) =
        ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
          (op (D.pieces j))).hom
          (gluedTwistEquiv C R π a (D.pieces j) rj)) :
    (Submodule.Quotient.mk
      (secRes (thetaChartDatum C R π a).sheaf
        (le_top : D.pieces j ≤ (⊤ : (relCurve C R).Opens))
        ((gluedTwistEquiv C R π a (⊤ : (relCurve C R).Opens)).symm x)) :
      A.ThetaPieceQuotient (π := π) a j) =
      Submodule.Quotient.mk rj := by
  let sx := secRes (thetaChartDatum C R π a).sheaf
    (le_top : D.pieces j ≤ (⊤ : (relCurve C R).Opens))
    ((gluedTwistEquiv C R π a (⊤ : (relCurve C R).Opens)).symm x)
  apply (Submodule.Quotient.eq (A.thetaPieceVanishing (π := π) a j)).mpr
  apply (A.thetaPieceVanishing_iff_gluedTwist_cokernel_eq_zero
    C R π B a j (sx - rj)).mpr
  have htw :
      gluedTwistEquiv C R π a (D.pieces j) (sx - rj) =
        gluedTwistEquiv C R π a (D.pieces j) sx -
          gluedTwistEquiv C R π a (D.pieces j) rj :=
    (gluedTwistEquiv C R π a (D.pieces j)).map_sub sx rj
  rw [htw, map_sub]
  apply sub_eq_zero.mpr
  rw [gluedTwistEquiv_res_top_symm C R π]
  exact (secRes_naturality (cokernel.π (B.thetaIdealIncl (a := a)))
    (le_top : D.pieces j ≤ (⊤ : (relCurve C R).Opens)) x).trans hlocal

/-! ## Compatibility of local cokernel representatives

The quotient equalizer relation on two widened pieces is exactly the compatibility
condition for their images in the auxiliary theta cokernel sheaf.  This is the
local datum consumed by the sheaf gluing theorem below.
-/

theorem thetaPieceCokernel_family_isCompatible
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} (B : DivisorAdaptation C R π d) (a : ℕ)
    (r : ∀ j : D.index, A.ThetaPieceSections (π := π) a j)
    (hr : ∀ i j : D.index,
      A.thetaToOverlapLeft (π := π) a i j (Submodule.Quotient.mk (r i)) =
        A.thetaToOverlapRight (π := π) a i j (Submodule.Quotient.mk (r j))) :
    TopCat.Presheaf.IsCompatible
      (cokernel (B.thetaIdealIncl (a := a))).obj D.pieces
      (fun j => ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
        (op (D.pieces j))).hom
        (gluedTwistEquiv C R π a (D.pieces j) (r j))) := by
  intro i j
  let W := D.pieces i ⊓ D.pieces j
  change secRes (cokernel (B.thetaIdealIncl (a := a)))
      (inf_le_left : W ≤ D.pieces i)
      (((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
        (op (D.pieces i))).hom
        (gluedTwistEquiv C R π a (D.pieces i) (r i))) =
    secRes (cokernel (B.thetaIdealIncl (a := a)))
      (inf_le_right : W ≤ D.pieces j)
      (((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
        (op (D.pieces j))).hom
        (gluedTwistEquiv C R π a (D.pieces j) (r j)))
  have hL := secRes_naturality (cokernel.π (B.thetaIdealIncl (a := a)))
    (inf_le_left : W ≤ D.pieces i)
    (gluedTwistEquiv C R π a (D.pieces i) (r i))
  have hR := secRes_naturality (cokernel.π (B.thetaIdealIncl (a := a)))
    (inf_le_right : W ≤ D.pieces j)
    (gluedTwistEquiv C R π a (D.pieces j) (r j))
  rw [← hL, ← hR]
  have hresL :
      secRes (relThetaTwistSheaf C R π a)
          (inf_le_left : W ≤ D.pieces i)
          (gluedTwistEquiv C R π a (D.pieces i) (r i)) =
        gluedTwistEquiv C R π a W
          (A.thetaSectionsToOverlapLeft (π := π) a i j (r i)) := by
    change twistRes R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a)
          inf_le_left (gluedToTwistApp C R π a (D.pieces i) (r i)) =
      gluedToTwistApp C R π a W
        (gluedRes R (thetaChartDatum C R π a).pieces
          (thetaChartDatum C R π a).unit inf_le_left (r i))
    exact (gluedToTwistApp_res C R π a inf_le_left (r i)).symm
  have hresR :
      secRes (relThetaTwistSheaf C R π a)
          (inf_le_right : W ≤ D.pieces j)
          (gluedTwistEquiv C R π a (D.pieces j) (r j)) =
        gluedTwistEquiv C R π a W
          (A.thetaSectionsToOverlapRight (π := π) a i j (r j)) := by
    change twistRes R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a)
          inf_le_right (gluedToTwistApp C R π a (D.pieces j) (r j)) =
      gluedToTwistApp C R π a W
        (gluedRes R (thetaChartDatum C R π a).pieces
          (thetaChartDatum C R π a).unit inf_le_right (r j))
    exact (gluedToTwistApp_res C R π a inf_le_right (r j)).symm
  rw [hresL, hresR]
  have hv :
      A.thetaSectionsToOverlapLeft (π := π) a i j (r i) -
        A.thetaSectionsToOverlapRight (π := π) a i j (r j) ∈
          A.thetaOverlapVanishing (π := π) a i j := by
    change secRes (thetaChartDatum C R π a).sheaf inf_le_left (r i) -
        secRes (thetaChartDatum C R π a).sheaf inf_le_right (r j) ∈
      A.thetaOverlapVanishing (π := π) a i j
    apply (Submodule.Quotient.eq
      (A.thetaOverlapVanishing (π := π) a i j)).mp
    simpa only [A.thetaToOverlapLeft_mk, A.thetaToOverlapRight_mk] using hr i j
  have hzero := thetaOverlapVanishing_gluedTwist_cokernel_eq_zero
    C R π B a i j
    (A.thetaSectionsToOverlapLeft (π := π) a i j (r i) -
      A.thetaSectionsToOverlapRight (π := π) a i j (r j)) hv
  have hmap :
      gluedTwistEquiv C R π a W
          (A.thetaSectionsToOverlapLeft (π := π) a i j (r i) -
            A.thetaSectionsToOverlapRight (π := π) a i j (r j)) =
        gluedTwistEquiv C R π a W
          (A.thetaSectionsToOverlapLeft (π := π) a i j (r i)) -
          gluedTwistEquiv C R π a W
            (A.thetaSectionsToOverlapRight (π := π) a i j (r j)) := by
    exact (gluedTwistEquiv C R π a W).map_sub _ _
  rw [hmap, map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- Compatible representatives of an intrinsic theta class determine a global section of
the auxiliary theta cokernel whose restriction to every widened piece is their local
cokernel class. -/
theorem exists_thetaCokernel_global_of_compatible_representatives
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} (B : DivisorAdaptation C R π d) (a : ℕ)
    (r : ∀ j : D.index, A.ThetaPieceSections (π := π) a j)
    (hr : ∀ i j : D.index,
      A.thetaToOverlapLeft (π := π) a i j (Submodule.Quotient.mk (r i)) =
        A.thetaToOverlapRight (π := π) a i j (Submodule.Quotient.mk (r j))) :
    ∃ q : (cokernel (B.thetaIdealIncl (a := a))).obj.obj
        (op (⊤ : (relCurve C R).Opens)),
      ∀ j : D.index,
        secRes (cokernel (B.thetaIdealIncl (a := a)))
          (le_top : D.pieces j ≤ (⊤ : (relCurve C R).Opens)) q =
          ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
            (op (D.pieces j))).hom
            (gluedTwistEquiv C R π a (D.pieces j) (r j)) := by
  let Q := cokernel (B.thetaIdealIncl (a := a))
  have hcompat := thetaPieceCokernel_family_isCompatible C R π B a r hr
  have hcover : (⊤ : (relCurve C R).Opens) ≤ ⨆ j : D.index, D.pieces j := by
    rw [D.cover]
  obtain ⟨q, hq, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    Q D.pieces (⊤ : (relCurve C R).Opens)
    (fun j => homOfLE (le_top : D.pieces j ≤ (⊤ : (relCurve C R).Opens)))
    hcover
    (fun j => ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
      (op (D.pieces j))).hom
      (gluedTwistEquiv C R π a (D.pieces j) (r j)))
    hcompat
  exact ⟨q, hq⟩

/-- Surjectivity of the auxiliary theta-cokernel projection on global sections forces
surjectivity of intrinsic theta evaluation on the arbitrary widened affine cover.  The
proof chooses local quotient representatives, glues their cokernel classes, and uses
piecewise exactness to compare the resulting global lift back to those representatives. -/
theorem intrinsicThetaEvalRel_surjective_of_thetaIdealCokernel_app_top_surjective
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} (B : DivisorAdaptation C R π d) (a : ℕ)
    (hsurj : Function.Surjective
      ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
        (op (⊤ : (relCurve C R).Opens))).hom) :
    Function.Surjective (A.intrinsicThetaEvalRel (π := π) a) := by
  intro y
  choose r hr using fun j : D.index =>
    Submodule.Quotient.mk_surjective (A.thetaPieceVanishing (π := π) a j) (y.val j)
  have hcompat : ∀ i j : D.index,
      A.thetaToOverlapLeft (π := π) a i j (Submodule.Quotient.mk (r i)) =
        A.thetaToOverlapRight (π := π) a i j (Submodule.Quotient.mk (r j)) := by
    intro i j
    have hy := (A.mem_intrinsicThetaGluedSubmodule_iff (π := π) a y.val).mp
      y.property ⟨i, j⟩
    rw [hr i, hr j]
    exact hy
  obtain ⟨q, hq⟩ := exists_thetaCokernel_global_of_compatible_representatives
    C R π B a r hcompat
  obtain ⟨x, hx⟩ := hsurj q
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext j
  letI : Module Γ(relCurve C R, D.pieces j)
      (A.ThetaPieceSections (π := π) a j) :=
    A.thetaPieceSectionsModule (π := π) a j
  change Submodule.Quotient.mk
      (secRes (thetaChartDatum C R π a).sheaf
        (le_top : D.pieces j ≤ (⊤ : (relCurve C R).Opens))
        ((gluedTwistEquiv C R π a (⊤ : (relCurve C R).Opens)).symm x)) =
      y.val j
  rw [← hr j]
  apply thetaPieceQuotient_eq_of_global_cokernel_restriction C R π B a j x (r j)
  calc
    secRes (cokernel (B.thetaIdealIncl (a := a)))
        (le_top : D.pieces j ≤ (⊤ : (relCurve C R).Opens))
        (((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
          (op (⊤ : (relCurve C R).Opens))).hom x) =
      secRes (cokernel (B.thetaIdealIncl (a := a)))
        (le_top : D.pieces j ≤ (⊤ : (relCurve C R).Opens)) q := by
          rw [hx]
    _ = ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
        (op (D.pieces j))).hom
        (gluedTwistEquiv C R π a (D.pieces j) (r j)) := hq j

end AffAdaptation

end CokernelDescent

section CokernelGlobal

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [IsDominant π] [IsIntegral C.left]

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]

namespace AffAdaptation

/-- The widened certificate's global theta-cokernel surjectivity is enough to make the
intrinsic, chart-free theta evaluation surjective. -/
theorem IsCertified.intrinsicThetaEvalRel_surjective
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {a : ℕ} (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    Function.Surjective (A.intrinsicThetaEvalRel (π := π) a) := by
  obtain ⟨B, hB⟩ := hc.exists_chartAdaptation_thetaIdealCokernel_app_top_surjective
    C R π hπ hO hχ ha1 hMa
  exact intrinsicThetaEvalRel_surjective_of_thetaIdealCokernel_app_top_surjective
    C R π B a hB

/-- Intrinsic theta evaluation remains surjective when the Euler-characteristic
normalization uses `gamma ≤ g` independently of the certified divisor degree. -/
theorem IsCertified.intrinsicThetaEvalRel_surjective_at
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g gamma : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {a : ℕ} (hMa : windowM_choice π hπ g ≤ a) :
    Function.Surjective (A.intrinsicThetaEvalRel (π := π) a) := by
  obtain ⟨B, hB⟩ := hc.exists_chartAdaptation_thetaIdealCokernel_app_top_surjective_at
    C R π hπ hgamma hχ hMa
  exact intrinsicThetaEvalRel_surjective_of_thetaIdealCokernel_app_top_surjective
    C R π B a hB

/-- The certified intrinsic high-window carve is surjective. -/
theorem IsCertified.intrinsicWindowCarve_surjective
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {a : ℕ} (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    Function.Surjective (A.intrinsicWindowCarve (π := π) a ha1) := by
  rw [intrinsicWindowCarve, LinearMap.coe_comp]
  exact (hc.intrinsicThetaEvalRel_surjective C R π hπ hO hχ ha1 hMa).comp
    (relThetaWindowEquiv C R π a ha1).surjective

/-- The intrinsic window carve is surjective with independent curve and divisor
parameters. -/
theorem IsCertified.intrinsicWindowCarve_surjective_at
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g gamma : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {a : ℕ} (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    Function.Surjective (A.intrinsicWindowCarve (π := π) a ha1) := by
  rw [intrinsicWindowCarve, LinearMap.coe_comp]
  exact (hc.intrinsicThetaEvalRel_surjective_at C R π hπ hgamma hχ hMa).comp
    (relThetaWindowEquiv C R π a ha1).surjective

/-- The certified intrinsic window quotient is linearly equivalent to the descended
theta restriction, with the established divisor-window kernel and no extra hypothesis. -/
noncomputable def IsCertified.intrinsicWindowQuotEquiv
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {a : ℕ} (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    ((R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d ha1) ≃ₗ[R]
      A.IntrinsicThetaGlued (π := π) a :=
  (Submodule.quotEquivOfEq _ _
      (A.ker_intrinsicWindowCarve (π := π) a ha1).symm).trans
    ((A.intrinsicWindowCarve (π := π) a ha1).quotKerEquivOfSurjective
      (hc.intrinsicWindowCarve_surjective C R π hπ hO hχ ha1 hMa))

/-- The intrinsic window quotient equivalence with independent curve and divisor
parameters. -/
noncomputable def IsCertified.intrinsicWindowQuotEquiv_at
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g gamma : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {a : ℕ} (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    ((R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d ha1) ≃ₗ[R]
      A.IntrinsicThetaGlued (π := π) a :=
  (Submodule.quotEquivOfEq _ _
      (A.ker_intrinsicWindowCarve (π := π) a ha1).symm).trans
    ((A.intrinsicWindowCarve (π := π) a ha1).quotKerEquivOfSurjective
      (hc.intrinsicWindowCarve_surjective_at C R π hπ hgamma hχ ha1 hMa))

/-- Once the widened certificate supplies the auxiliary theta-ideal `H¹` vanishing,
global sections of the quotient sheaf for the chosen auxiliary chart are linearly equivalent
to the actual range of the intrinsic widened theta evaluation. -/
noncomputable def IsCertified.thetaIdealCokernelEquivIntrinsicRange
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {a : ℕ} (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    let B := Classical.choose
      (hc.exists_chartAdaptation_subsingleton_thetaIdealH1 C R π hπ hO hχ ha1 hMa)
    (cokernel (DivisorAdaptation.thetaIdealIncl (A := B) (a := a))).obj.obj
        (op (⊤ : (relCurve C R).Opens)) ≃ₗ[R]
      ↥(LinearMap.range (A.intrinsicThetaEvalRel (π := π) a)) := by
  let hB := Classical.choose_spec
    (hc.exists_chartAdaptation_subsingleton_thetaIdealH1 C R π hπ hO hχ ha1 hMa)
  let B := Classical.choose
    (hc.exists_chartAdaptation_subsingleton_thetaIdealH1 C R π hπ hO hχ ha1 hMa)
  letI : Subsingleton (Sheaf.HModule (B.thetaIdealDatum a).sheaf 1) := hB
  have hrange :
      LinearMap.range
          ((DivisorAdaptation.thetaIdealIncl (A := B) (a := a)).hom.app
            (op (⊤ : (relCurve C R).Opens))).hom =
        d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
          (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) := by
    rw [DivisorAdaptation.thetaIdealIncl_app]
    change LinearMap.range (B.thetaIdealInclApp (a := a) ⊤) = _
    exact DivisorAdaptation.range_thetaIdealInclApp_top C R π B a
  exact (Sheaf.cokernelAppEquivQuotientRange
      (DivisorAdaptation.thetaIdealIncl (A := B) (a := a))
      (op (⊤ : (relCurve C R).Opens)) B.thetaIdealCokernel_app_top_surjective).trans
    ((Submodule.quotEquivOfEq _ _ hrange).trans
      (A.intrinsicThetaQuotEquivRange (π := π) a))

/-- The global theta quotient maps into the widened intrinsic descent module.
The certified surjectivity theorem below upgrades this embedding to the intrinsic quotient
equivalence; the remaining representability seam is projectivity and the classifier endpoint. -/
noncomputable def IsCertified.thetaIdealCokernelToIntrinsic
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {a : ℕ} (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    let B := Classical.choose
      (hc.exists_chartAdaptation_subsingleton_thetaIdealH1 C R π hπ hO hχ ha1 hMa)
    (cokernel (DivisorAdaptation.thetaIdealIncl (A := B) (a := a))).obj.obj
        (op (⊤ : (relCurve C R).Opens)) →ₗ[R]
      A.IntrinsicThetaGlued (π := π) a :=
  (Submodule.subtype (LinearMap.range (A.intrinsicThetaEvalRel (π := π) a))).comp
    (hc.thetaIdealCokernelEquivIntrinsicRange C R π hπ hO hχ ha1 hMa).toLinearMap

/-- The cokernel embedding carries the quotient projection of a theta section to its
intrinsic evaluation. -/
theorem IsCertified.thetaIdealCokernelToIntrinsic_apply_cokernelπ
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {a : ℕ} (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) (x : relThetaSections C R π a) :
    let B := Classical.choose
      (hc.exists_chartAdaptation_subsingleton_thetaIdealH1 C R π hπ hO hχ ha1 hMa)
    hc.thetaIdealCokernelToIntrinsic C R π hπ hO hχ ha1 hMa
        (((cokernel.π (DivisorAdaptation.thetaIdealIncl (A := B) (a := a))).hom.app
          (op (⊤ : (relCurve C R).Opens))).hom x) =
      A.intrinsicThetaEvalRel (π := π) a x := by
  let B := Classical.choose
    (hc.exists_chartAdaptation_subsingleton_thetaIdealH1 C R π hπ hO hχ ha1 hMa)
  change ((hc.thetaIdealCokernelEquivIntrinsicRange C R π hπ hO hχ ha1 hMa)
    (((cokernel.π (DivisorAdaptation.thetaIdealIncl (A := B) (a := a))).hom.app
      (op (⊤ : (relCurve C R).Opens))).hom x) :
        A.IntrinsicThetaGlued (π := π) a) = _
  apply Subtype.ext
  simp only [IsCertified.thetaIdealCokernelEquivIntrinsicRange,
    Sheaf.cokernelAppEquivQuotientRange,
    LinearEquiv.trans_apply, LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.quotEquivOfEq_mk]
  -- One coercion layer more than the source lemma states: the goal sits under the
  -- `IntrinsicThetaGlued` subtype as well as the range subtype, so `congrArg` supplies the
  -- outer `↑`.  (Repaired by pic-g to unbreak the root build; `exact` alone was left by an
  -- edit whose targeted module check could not see this file — the mismatch only appears
  -- when the root imports it.  Author: see `Archon-Task: pic-d` on the introducing commit.)
  exact congrArg _ (A.intrinsicThetaQuotEquivRange_mk (π := π) a x)

/-- The global theta-cokernel embedding is surjective once the intrinsic evaluation has
been descended through the same certified auxiliary chart. -/
theorem IsCertified.thetaIdealCokernelToIntrinsic_surjective
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {a : ℕ} (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    Function.Surjective
      (hc.thetaIdealCokernelToIntrinsic C R π hπ hO hχ ha1 hMa) := by
  let hB := Classical.choose_spec
    (hc.exists_chartAdaptation_subsingleton_thetaIdealH1 C R π hπ hO hχ ha1 hMa)
  let B := Classical.choose
    (hc.exists_chartAdaptation_subsingleton_thetaIdealH1 C R π hπ hO hχ ha1 hMa)
  letI : Subsingleton (Sheaf.HModule (B.thetaIdealDatum a).sheaf 1) := hB
  have hev := hc.intrinsicThetaEvalRel_surjective C R π hπ hO hχ ha1 hMa
  intro y
  obtain ⟨x, hx⟩ := hev y
  let q := ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
    (op (⊤ : (relCurve C R).Opens))).hom x
  refine ⟨q, ?_⟩
  rw [show q = ((cokernel.π (B.thetaIdealIncl (a := a))).hom.app
    (op (⊤ : (relCurve C R).Opens))).hom x from rfl]
  rw [hc.thetaIdealCokernelToIntrinsic_apply_cokernelπ C R π hπ hO hχ ha1 hMa x, hx]

/-- The global theta-quotient embedding has precisely the image of intrinsic theta
evaluation as its range. -/
theorem IsCertified.range_thetaIdealCokernelToIntrinsic
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {a : ℕ} (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    LinearMap.range
        (hc.thetaIdealCokernelToIntrinsic C R π hπ hO hχ ha1 hMa) =
      LinearMap.range (A.intrinsicThetaEvalRel (π := π) a) := by
  let e := hc.thetaIdealCokernelEquivIntrinsicRange C R π hπ hO hχ ha1 hMa
  change LinearMap.range ((Submodule.subtype _).comp e.toLinearMap) = _
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact (e q).property
  · intro hy
    refine ⟨e.symm ⟨y, hy⟩, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)

/-- The global theta-quotient map is an embedding. -/
theorem IsCertified.thetaIdealCokernelToIntrinsic_injective
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {a : ℕ} (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    Function.Injective
      (hc.thetaIdealCokernelToIntrinsic C R π hπ hO hχ ha1 hMa) := by
  let e := hc.thetaIdealCokernelEquivIntrinsicRange C R π hπ hO hχ ha1 hMa
  change Function.Injective ((Submodule.subtype _).comp e.toLinearMap)
  exact (LinearMap.range (A.intrinsicThetaEvalRel (π := π) a)).injective_subtype.comp
    e.injective

end AffAdaptation

end CokernelGlobal

end AlgebraicGeometry
