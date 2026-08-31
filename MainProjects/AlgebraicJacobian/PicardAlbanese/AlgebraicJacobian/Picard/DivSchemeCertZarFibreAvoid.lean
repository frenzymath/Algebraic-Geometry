/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.TwistedFiberTwoCover
import AlgebraicJacobian.Picard.DivSchemeAdaptationFibreRegular
import AlgebraicJacobian.Picard.DivSchemeCertZarConfine
import AlgebraicJacobian.Picard.DivSchemeFibrePoint
import AlgebraicJacobian.Picard.DivSchemeSeedUnivPulledDegree
import AlgebraicJacobian.Picard.DivisorFamilyFieldDegree

/-!
# Fibrewise avoidance by a coordinate twist

Over an infinite ground field, the image in `P¹` of a finite divisor fibre misses two members of
the pencil `X₁ - aX₀`. The associated `GL₂` coordinate change puts the fibre inside the overlap of
the two twisted affine charts. Properness then spreads this confinement to a Zariski neighbourhood
of the base point.

The finiteness hypothesis is explicit: `LocalEquations` does not itself package the support as a
finite morphism. Callers must obtain fibre finiteness from their geometric divisor data, not from a
certificate.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme Grassmannian ThetaGeneratorSeed

namespace Scheme.LocalEquations

/-! ## Finite support on a curve -/

/-- A regular local-equation system on a smooth integral quasi-compact curve over a field has
finite support. Its support is contained in the finite order support of its meromorphic
presentation; regularity excludes the generic point. -/
theorem supportLocus_finite_on_curve (K : Type u) [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral X] [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    (d : X.LocalEquations) : d.supportLocus.Finite := by
  let T : Set {x : X // x ≠ genericPoint X} :=
    {p | Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) p.2
      (d.presentation.elem p.1) ≠ 1}
  have hT : T.Finite := d.presentation.ordZ_elem_support_finite K
  refine (hT.image Subtype.val).subset ?_
  intro x hx
  have hxg : x ≠ genericPoint X := by
    intro h
    subst x
    have hnot := (d.mem_supportLocus_iff_not_isUnit_germ
      (d.cover.mem_opens (genericPoint X))).mp hx
    apply hnot
    exact isUnit_iff_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp
      (d.regular (genericPoint X) (genericPoint X)
        (d.cover.mem_opens (genericPoint X))))
  refine ⟨⟨x, hxg⟩, ?_, rfl⟩
  change Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hxg
    (d.presentation.elem x) ≠ 1
  intro hord
  have hnot := (d.mem_supportLocus_iff_not_isUnit_germ
    (d.cover.mem_opens x)).mp hx
  apply hnot
  exact (Scheme.isUnit_germ_iff_ordZ_eq_one K
    (d.cover.genericPoint_mem_opens x) (d.eqn x)
    (d.presentation.elem x) (d.presentation_elem_val x)
    (d.cover.mem_opens x) hxg).mpr hord

/-- Away from the generic point, the support locus of regular local equations is exactly the
support of the associated presentation divisor. -/
theorem mem_supportLocus_iff_mem_presentationDivisor_support
    (K : Type u) [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral X] [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    (d : X.LocalEquations) {x : X} (hxg : x ≠ genericPoint X) :
    x ∈ d.supportLocus ↔
      (⟨x, hxg⟩ : {y : X // y ≠ genericPoint X}) ∈
        (toFinsupp (Scheme.presentationDivisor K d.presentation)).support := by
  rw [Finsupp.mem_support_iff]
  change x ∈ d.supportLocus ↔
    coeffAt hxg (Scheme.presentationDivisor K d.presentation) ≠ 0
  rw [Scheme.coeffAt_presentationDivisor,
    d.mem_supportLocus_iff_not_isUnit_germ (d.cover.mem_opens x),
    Scheme.isUnit_germ_iff_ordZ_eq_one K
      (d.cover.genericPoint_mem_opens x) (d.eqn x)
      (d.presentation.elem x) (d.presentation_elem_val x)
      (d.cover.mem_opens x) hxg]
  simp

/-- Regular local equations do not vanish at the generic point. -/
theorem genericPoint_not_mem_supportLocus
    (K : Type u) [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral X] [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    (d : X.LocalEquations) : genericPoint X ∉ d.supportLocus := by
  intro h
  have hnot := (d.mem_supportLocus_iff_not_isUnit_germ
    (d.cover.mem_opens (genericPoint X))).mp h
  apply hnot
  exact isUnit_iff_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp
    (d.regular (genericPoint X) (genericPoint X)
      (d.cover.mem_opens (genericPoint X))))

/-- The support locus is the image of the finite support of its presentation divisor. -/
theorem supportLocus_eq_image_presentationDivisor_support
    (K : Type u) [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral X] [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    (d : X.LocalEquations) :
    d.supportLocus =
      Subtype.val ''
        (↑(toFinsupp (Scheme.presentationDivisor K d.presentation)).support :
          Set {x : X // x ≠ genericPoint X}) := by
  ext x
  constructor
  · intro hx
    have hxg : x ≠ genericPoint X := by
      intro h
      subst x
      exact genericPoint_not_mem_supportLocus K d hx
    exact ⟨⟨x, hxg⟩,
      (mem_supportLocus_iff_mem_presentationDivisor_support K d hxg).mp hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_supportLocus_iff_mem_presentationDivisor_support K d x.2).mpr hx

/-- Counting the support locus agrees with counting the support of its presentation divisor. -/
theorem supportLocus_ncard_eq_presentationDivisor_support_card
    (K : Type u) [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral X] [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    (d : X.LocalEquations) :
    d.supportLocus.ncard =
      (toFinsupp (Scheme.presentationDivisor K d.presentation)).support.card := by
  rw [supportLocus_eq_image_presentationDivisor_support K d,
    Set.ncard_image_of_injective _ Subtype.val_injective]
  simp

/-- The number of support points of regular local equations is at most the degree of their
presentation divisor. -/
theorem supportLocus_ncard_le_deg
    (K : Type u) [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral X] [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (d : X.LocalEquations) :
    (d.supportLocus.ncard : ℤ) ≤
      CurveDivisor.deg K (Scheme.presentationDivisor K d.presentation) := by
  rw [supportLocus_ncard_eq_presentationDivisor_support_card K d]
  apply Scheme.CurveDivisor.support_card_le_deg K
  rw [Finsupp.le_def]
  intro p
  change 0 ≤ coeffAt p.2 (Scheme.presentationDivisor K d.presentation)
  exact Scheme.zero_le_coeffAt_presentationDivisor K d p.2

/-! ## Finite residue fibres -/

section ResidueFibre

variable {k : Type u} [Field k]
variable (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]

/-- The residue-field base change maps bijectively onto the corresponding topological fibre of
the relative curve. The inverse on points is the canonical residue lift. -/
theorem range_relCurveMap_residueField (p : PrimeSpectrum R) :
    Set.range (relCurveMap C R p.asIdeal.ResidueField).base =
      {z : relCurve C R | relCurveBasePoint C R z = p} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact relCurveBasePoint_relCurveMap_residueField C R p x
  · intro hz
    let z' : relCurve C p.asIdeal.ResidueField :=
      Eq.ndrec
        (motive := fun q : PrimeSpectrum R => relCurve C q.asIdeal.ResidueField)
        (relCurveResiduePoint C R z) hz
    refine ⟨z', ?_⟩
    exact (relCurveMap_residueField_cast C R hz
      (relCurveResiduePoint C R z)).trans
      (relCurveMap_relCurveResiduePoint C R z)

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-- If a local-equation system pulls back to a regular system on the residue curve, then its
support fibre is finite. This isolates the exact noncircular input needed by fibre avoidance:
regularity after residue-field pullback. -/
theorem fibre_supportLocus_finite_of_pullback_support_eq
    (d : (relCurve C R).LocalEquations) (p : PrimeSpectrum R)
    (dK : (relCurve C p.asIdeal.ResidueField).LocalEquations)
    (hsupport : dK.supportLocus =
      (relCurveMap C R p.asIdeal.ResidueField).base ⁻¹' d.supportLocus) :
    (((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {p} ∩
      d.supportLocus).Finite := by
  letI : SmoothOfRelativeDimension 1
      (relCurve C p.asIdeal.ResidueField ↘
        Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
    instSmoothOfRelativeDimensionBaseChange C p.asIdeal.ResidueField
  letI : IsIntegral (relCurve C p.asIdeal.ResidueField) :=
    instIsIntegralBaseChange C p.asIdeal.ResidueField
  letI : QuasiCompact
      (relCurve C p.asIdeal.ResidueField ↘
        Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
    instQuasiCompactBaseChange C p.asIdeal.ResidueField
  have hfinite := supportLocus_finite_on_curve p.asIdeal.ResidueField dK
  have heq :
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {p} ∩ d.supportLocus =
        (relCurveMap C R p.asIdeal.ResidueField).base '' dK.supportLocus := by
    ext x
    constructor
    · rintro ⟨hxp, hxd⟩
      change relCurveBasePoint C R x = p at hxp
      have hxrange :
          x ∈ Set.range (relCurveMap C R p.asIdeal.ResidueField).base := by
        rw [range_relCurveMap_residueField C R p]
        exact hxp
      obtain ⟨z, rfl⟩ := hxrange
      refine ⟨z, ?_, rfl⟩
      rw [hsupport]
      exact hxd
    · rintro ⟨z, hz, rfl⟩
      constructor
      · change relCurveBasePoint C R
          ((relCurveMap C R p.asIdeal.ResidueField).base z) = p
        exact relCurveBasePoint_relCurveMap_residueField C R p z
      · rw [hsupport] at hz
        exact hz
  rw [heq]
  exact hfinite.image (relCurveMap C R p.asIdeal.ResidueField).base

/-- Own-member regularity of the residue-field pullback is enough to make the support fibre
finite. Transition units first propagate regularity across every member of the pulled cover. -/
theorem fibre_supportLocus_finite_of_forall_self
    (d : (relCurve C R).LocalEquations) (p : PrimeSpectrum R)
    (hself : ∀ z : relCurve C p.asIdeal.ResidueField,
      ((relCurve C p.asIdeal.ResidueField).presheaf.germ
        ((d.cover.pullback
          (relCurveMap C R p.asIdeal.ResidueField)).opens z) z
        ((d.cover.pullback
          (relCurveMap C R p.asIdeal.ResidueField)).mem_opens z)).hom
        (pullbackEqn (relCurveMap C R p.asIdeal.ResidueField) d z) ∈
          nonZeroDivisors
            ((relCurve C p.asIdeal.ResidueField).presheaf.stalk z)) :
    (((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {p} ∩
      d.supportLocus).Finite := by
  let hreg := germ_pullbackEqn_mem_nonZeroDivisors_of_forall_self
    (relCurveMap C R p.asIdeal.ResidueField) d hself
  exact fibre_supportLocus_finite_of_pullback_support_eq C R d p
    (d.pullback (relCurveMap C R p.asIdeal.ResidueField) hreg)
    (supportLocus_pullback (relCurveMap C R p.asIdeal.ResidueField) d hreg)

end ResidueFibre

/-! ## Avoidance on a relative curve -/

variable {k : Type u} [Field k] [Infinite k]
variable {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

/-- A finite support fibre can be confined to the overlap of two charts after one coordinate
twist. The finite set fed to `P1.exists_matrix_finite_subset_chartInter` is its image under the
relative map `C_R ⟶ C ⟶ P¹`. -/
theorem exists_matrix_fibre_subset_twisted_chartInter
    (d : (relCurve C R).LocalEquations) (s : Spec (.of R))
    (hfinite : (((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s} ∩
      d.supportLocus).Finite) :
    ∃ M : Matrix.GeneralLinearGroup (Fin 2) k,
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s} ∩ d.supportLocus ⊆
        ((((twistedRelCover C R π M).V₀ ⊓ (twistedRelCover C R π M).V₁ :
          (relCurve C R).Opens) : Set (relCurve C R))) := by
  let q : relCurve C R ⟶ P1 k := (fst C (overSpec k R)).left ≫ π
  let F : Set (relCurve C R) :=
    ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s} ∩ d.supportLocus
  have hqF : (q.base '' F).Finite := hfinite.image q.base
  obtain ⟨M, hM⟩ := P1.exists_matrix_finite_subset_chartInter k (q.base '' F) hqF
  refine ⟨M, fun x hx => ?_⟩
  exact hM ⟨x, hx, rfl⟩

variable [IsProper C.hom]

/-- Fibrewise avoidance is Zariski-open on the base: after choosing the coordinate twist at one
finite fibre, the proper-support tube spreads confinement to a neighbourhood of that fibre. -/
theorem exists_matrix_opens_supportLocus_subset_twisted_chartInter
    (d : (relCurve C R).LocalEquations) (s : Spec (.of R))
    (hfinite : (((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s} ∩
      d.supportLocus).Finite) :
    ∃ (M : Matrix.GeneralLinearGroup (Fin 2) k) (V : (Spec (.of R)).Opens),
      s ∈ V ∧
        ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' (V : Set (Spec (.of R))) ∩
          d.supportLocus ⊆
            ((((twistedRelCover C R π M).V₀ ⊓ (twistedRelCover C R π M).V₁ :
              (relCurve C R).Opens) : Set (relCurve C R))) := by
  obtain ⟨M, hM⟩ :=
    exists_matrix_fibre_subset_twisted_chartInter (π := π) d s hfinite
  obtain ⟨V, hsV, hV⟩ := d.exists_supportTube
    ((relCurve C R) ↘ Spec (.of R)) (Opens.isOpen _) hM
  exact ⟨M, V, hsV, hV⟩

variable [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]

/-- The complete fibre-avoidance package from the noncircular input used by the universal seed:
residue-pullback regularity gives a finite fibre, a `GL₂` twist avoids its image in `P¹`, and
properness spreads the resulting chart confinement over a Zariski neighbourhood. -/
theorem exists_matrix_opens_supportLocus_subset_twisted_chartInter_of_forall_self
    (d : (relCurve C R).LocalEquations) (p : Spec (.of R))
    (hself : ∀ z : relCurve C p.asIdeal.ResidueField,
      ((relCurve C p.asIdeal.ResidueField).presheaf.germ
        ((d.cover.pullback
          (relCurveMap C R p.asIdeal.ResidueField)).opens z) z
        ((d.cover.pullback
          (relCurveMap C R p.asIdeal.ResidueField)).mem_opens z)).hom
        (pullbackEqn (relCurveMap C R p.asIdeal.ResidueField) d z) ∈
          nonZeroDivisors
            ((relCurve C p.asIdeal.ResidueField).presheaf.stalk z)) :
    ∃ (M : Matrix.GeneralLinearGroup (Fin 2) k) (V : (Spec (.of R)).Opens),
      p ∈ V ∧
        ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' (V : Set (Spec (.of R))) ∩
          d.supportLocus ⊆
            ((((twistedRelCover C R π M).V₀ ⊓ (twistedRelCover C R π M).V₁ :
              (relCurve C R).Opens) : Set (relCurve C R))) :=
  exists_matrix_opens_supportLocus_subset_twisted_chartInter d p
    (fibre_supportLocus_finite_of_forall_self C R d p hself)

end Scheme.LocalEquations

namespace ThetaGeneratorSeed

variable {k : Type u} [Field k] [Infinite k]
variable {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : Nat}
variable {K : Submodule R (relThetaSections C R π a)}
variable (D : ThetaGeneratorSeed C R π a K)

/-- A generator seed satisfies the fibre-avoidance input without using colength finiteness,
flatness, projectivity, or a certificate: its own `fibre_regular` clause supplies residue-pullback
regularity. -/
theorem exists_matrix_opens_supportLocus_subset_twisted_chartInter
    (hD : D.IsGenerator) (p : Spec (.of R)) :
    ∃ (M : Matrix.GeneralLinearGroup (Fin 2) k) (V : (Spec (.of R)).Opens),
      p ∈ V ∧
        ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' (V : Set (Spec (.of R))) ∩
          (D.localEquations hD).supportLocus ⊆
            ((((twistedRelCover C R π M).V₀ ⊓ (twistedRelCover C R π M).V₁ :
              (relCurve C R).Opens) : Set (relCurve C R))) :=
  Scheme.LocalEquations.exists_matrix_opens_supportLocus_subset_twisted_chartInter_of_forall_self
    (π := π) (D.localEquations hD) p
    (fun z => D.germ_self_pullbackEqn_mem_nonZeroDivisors hD p z)

end ThetaGeneratorSeed

namespace PointwiseAchiever

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section SeedSupportBound

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftSeedSupportBound :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↑(Scheme.divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↑(Scheme.divisorSections k ((windowS_choice pi hpi g • fiberWeilDivisor pi)
    + (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

local notation "RZ" => seedChartRing C hpi g r1 r2 b1 b2 i j

set_option maxHeartbeats 8000000 in
-- The residue-field base-change instances and full pointwise seed data elaborate together.
set_option synthInstance.maxHeartbeats 800000 in
/-- The certificate-free residue-fibre support of the concrete pointwise universal seed has at
most `g` points. -/
theorem supportLocus_ncard_residueFibreLocalEquations_pointwiseGeneratorSeed_le
    (hrdn : PointwiseSeedRDN C hpi g r1 r2 b1 b2 i j hO hchi)
    (p : PrimeSpectrum RZ) :
    (ThetaGeneratorSeed.residueFibreLocalEquations
      (pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn)
      (isGenerator_pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn)
      p).supportLocus.ncard ≤ g := by
  letI : SmoothOfRelativeDimension 1
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
    instSmoothOfRelativeDimensionBaseChange C p.asIdeal.ResidueField
  letI : IsIntegral (relCurve C p.asIdeal.ResidueField) :=
    instIsIntegralBaseChange C p.asIdeal.ResidueField
  letI : QuasiCompact
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
    instQuasiCompactBaseChange C p.asIdeal.ResidueField
  letI : LocallyOfFiniteType
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField)) := by
    haveI : Smooth
        (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
      SmoothOfRelativeDimension.smooth 1 _
    infer_instance
  have hbound := Scheme.LocalEquations.supportLocus_ncard_le_deg
    p.asIdeal.ResidueField
    (ThetaGeneratorSeed.residueFibreLocalEquations
      (pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn)
      (isGenerator_pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn) p)
  rw [deg_presentationDivisor_residueFibreLocalEquations_pointwiseGeneratorSeed
    C hpi g r1 r2 b1 b2 i j hO hchi hrdn p] at hbound
  exact_mod_cast hbound

end SeedSupportBound

end PointwiseAchiever

end AlgebraicGeometry
