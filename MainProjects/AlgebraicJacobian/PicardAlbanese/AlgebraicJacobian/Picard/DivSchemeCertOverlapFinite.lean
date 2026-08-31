/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.SupportTubeFinite
import AlgebraicJacobian.Picard.DivisorThetaDatum
import AlgebraicJacobian.Picard.DivisorFamilyPullbackOverlap
import AlgebraicJacobian.Picard.DivSchemeAdaptationFibreRegular
import AlgebraicJacobian.Algebra.PiLocalization

/-!
# Finiteness of adaptation overlap colengths

If the support traces on adaptation pieces do not leak, then the trace on a pairwise
overlap is the intersection of two closed traces.  The overlap ideal is principal by
`DivisorAdaptation.ovlIdeal_eq_span_left`, so the proper affine finiteness engine applies
to every overlap colength and hence to their finite product.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

/-- A ring equivalence carries nonzerodivisors to nonzerodivisors. -/
private lemma ringEquiv_mem_nonZeroDivisors {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) {x : A} (hx : x ∈ nonZeroDivisors A) :
    e x ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff] at hx ⊢
  obtain ⟨hl, hr⟩ := hx
  constructor
  · intro y hy
    have h := congrArg e.symm hy
    rw [map_mul, map_zero, e.symm_apply_apply] at h
    have hy0 : e.symm y = 0 := hl _ h
    calc y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = 0 := by rw [hy0, map_zero]
  · intro y hy
    have h := congrArg e.symm hy
    rw [map_mul, map_zero, e.symm_apply_apply] at h
    have hy0 : e.symm y = 0 := hr _ h
    calc y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = 0 := by rw [hy0, map_zero]

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

namespace FinCoverData

variable (D : FinCoverData C R pi)

omit [IsProper C.hom] in
/-- The section ring of a pairwise piece overlap is flat over the base. -/
theorem flat_sections_pieces_inf (i j : D.index) :
    Module.Flat R Γ(relCurve C R, D.pieces i ⊓ D.pieces j) := by
  haveI : Module.Free R Γ(relCurve C R,
      (fst C (overSpec k R)).left ⁻¹ᵁ (D.chart i ⊓ D.chart j)) :=
    free_relSections C R (D.chart i ⊓ D.chart j)
      (D.isAffineOpen_chart_inf i j).isCompact
      (D.isAffineOpen_chart_inf i j).isQuasiSeparated
  have hVaff := D.isAffineOpen_preimage_chart_inf R i j
  change IsAffineOpen
    ((fst C (overSpec k R)).left ⁻¹ᵁ (D.chart i ⊓ D.chart j) :
      (relCurve C R).Opens) at hVaff
  have hflat := flat_sections_basicOpen R (X := relCurve C R)
    hVaff Module.Flat.of_free (D.ovlGen i j)
  rw [D.basicOpen_ovlGen i j] at hflat
  exact hflat

end FinCoverData

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations}
variable (A : DivisorAdaptation C R pi d)

set_option maxHeartbeats 800000 in
-- Normalizing the dependent overlap section ring requires the larger elaboration budget.
/-- Closed support traces on two pieces make their overlap colength finite over the
base. -/
theorem finite_ovlColength_of_isClosed_supportLocus_inter (i j : A.index)
    (hi : IsClosed (d.supportLocus ∩ (A.pieces i : Set (relCurve C R))))
    (hj : IsClosed (d.supportLocus ∩ (A.pieces j : Set (relCurve C R)))) :
    Module.Finite R (A.ovlColength i j) := by
  let V : (relCurve C R).Opens := A.pieces i ⊓ A.pieces j
  let f : Γ(relCurve C R, V) :=
    (relCurve C R).resHom
      (inf_le_left : A.pieces i ⊓ A.pieces j ≤ A.pieces i) (A.eqn i)
  have hclosed : IsClosed ((V : Set (relCurve C R)) \
      ((relCurve C R).basicOpen f : Set (relCurve C R))) := by
    have heq : ((V : Set (relCurve C R)) \
          ((relCurve C R).basicOpen f : Set (relCurve C R))) =
        (d.supportLocus ∩ (A.pieces i : Set (relCurve C R))) ∩
          (d.supportLocus ∩ (A.pieces j : Set (relCurve C R))) := by
      rw [show (relCurve C R).basicOpen f =
        V ⊓ (relCurve C R).basicOpen (A.eqn i) from
          Scheme.basicOpen_resHom inf_le_left (A.eqn i)]
      ext x
      have htrace := Set.ext_iff.mp (A.supportLocus_inter_pieces i) x
      simp only [Set.mem_sdiff, SetLike.mem_coe, Opens.mem_inf, Set.mem_inter_iff] at htrace ⊢
      constructor
      · rintro ⟨hxV, hxnot⟩
        have hsi : x ∈ d.supportLocus ∩ (A.pieces i : Set (relCurve C R)) :=
          htrace.mpr ⟨hxV.1, fun hxi => hxnot ⟨hxV, hxi⟩⟩
        exact ⟨hsi, hsi.1, hxV.2⟩
      · rintro ⟨hsi, _, hxj⟩
        have hdiff := htrace.mp hsi
        exact ⟨⟨hsi.2, hxj⟩, fun hx => hdiff.2 hx.2⟩
    rw [heq]
    exact hi.inter hj
  have hVaff : IsAffineOpen V := by
    rw [show V = (relCurve C R).basicOpen (A.toFinCoverData.ovlGen i j) from
      (A.toFinCoverData.basicOpen_ovlGen i j).symm]
    exact (A.toFinCoverData.isAffineOpen_preimage_chart_inf R i j).basicOpen _
  have hfin := hVaff.finite_quotient_span_singleton_of_isClosed (R := R) f hclosed
  have hideal := A.ovlIdeal_eq_span_left i j
  change A.ovlIdeal i j = Ideal.span {f} at hideal
  letI : Module.Finite R (Γ(relCurve C R, V) ⧸ Ideal.span {f}) := hfin
  exact Module.Finite.equiv
    ((Submodule.quotEquivOfEq _ _ hideal).symm.restrictScalars R)

/-- Fibrewise no-leak on the two pieces makes their overlap colength finite. -/
theorem finite_ovlColength_of_forall_fibre_closure_subset (i j : A.index)
    (hnoLeak : forall (l : A.index) (s : Spec (CommRingCat.of R)),
      ((relCurve C R) ↘ Spec (CommRingCat.of R)).base ⁻¹' {s}
          ∩ closure (d.supportLocus ∩ (A.pieces l : Set (relCurve C R)))
        ⊆ (A.pieces l : Set (relCurve C R))) :
    Module.Finite R (A.ovlColength i j) := by
  apply A.finite_ovlColength_of_isClosed_supportLocus_inter i j
  · exact (d.isClosed_supportLocus_inter_iff_supportLeak_eq_empty (A.pieces i)).mpr
      (d.supportLeak_eq_empty_of_forall_fibre
        ((relCurve C R) ↘ Spec (CommRingCat.of R)) (hnoLeak i))
  · exact (d.isClosed_supportLocus_inter_iff_supportLeak_eq_empty (A.pieces j)).mpr
      (d.supportLeak_eq_empty_of_forall_fibre
        ((relCurve C R) ↘ Spec (CommRingCat.of R)) (hnoLeak j))

/-- Fibrewise no-leak on every adaptation piece makes the finite product of all overlap
colengths finite over the base. -/
theorem finite_ovlProd_of_noLeak
    (hnoLeak : forall (j : A.index) (s : Spec (CommRingCat.of R)),
      ((relCurve C R) ↘ Spec (CommRingCat.of R)).base ⁻¹' {s}
          ∩ closure (d.supportLocus ∩ (A.pieces j : Set (relCurve C R)))
        ⊆ (A.pieces j : Set (relCurve C R))) :
    Module.Finite R A.ovlProd := by
  letI : forall p : A.index × A.index, Module.Finite R (A.ovlColength p.1 p.2) :=
    fun p => A.finite_ovlColength_of_forall_fibre_closure_subset p.1 p.2 hnoLeak
  exact Module.Finite.pi

section Seed

variable [IsNoetherianRing R]
variable {a : Nat} {K : Submodule R (relThetaSections C R pi a)}
variable {D : ThetaGeneratorSeed C R pi a K} (hD : D.IsGenerator)
variable (B : DivisorAdaptation C R pi (D.localEquations hD))

set_option maxHeartbeats 1200000 in
-- The proof transports regularity through the dependent overlap base-change equivalence.
set_option synthInstance.maxHeartbeats 400000 in
omit [IsProper C.hom] in
/-- The left equation restricted to an overlap remains a nonzerodivisor after tensoring
with every residue field. -/
theorem ovlEqn_tmul_one_mem_nonZeroDivisors_of_seed (i j : B.index)
    (p : PrimeSpectrum R) :
    ((relCurve C R).resHom
        (inf_le_left : B.pieces i ⊓ B.pieces j ≤ B.pieces i) (B.eqn i) ⊗ₜ[R]
      (1 : p.asIdeal.ResidueField) :
        Γ(relCurve C R, B.pieces i ⊓ B.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
      nonZeroDivisors
        (Γ(relCurve C R, B.pieces i ⊓ B.pieces j) ⊗[R]
          p.asIdeal.ResidueField) := by
  have hpulled := B.pulledEqn_mem_nonZeroDivisors_of_seed hD p i
  have hpulledOvl := Scheme.restriction_mem_nonZeroDivisors
    (fun z hz =>
      ((B.toFinCoverData.baseChange p.asIdeal.ResidueField).isAffineOpen_pieces i)
        |>.germ_mem_nonZeroDivisors hpulled z hz)
    (inf_le_left :
      (B.toFinCoverData.baseChange p.asIdeal.ResidueField).pieces i ⊓
          (B.toFinCoverData.baseChange p.asIdeal.ResidueField).pieces j ≤
        (B.toFinCoverData.baseChange p.asIdeal.ResidueField).pieces i)
  let e := B.toFinCoverData.ovlTermBaseChange p.asIdeal.ResidueField i j
  have hback := ringEquiv_mem_nonZeroDivisors e.symm.toRingEquiv hpulledOvl
  have hinv : e.symm
      ((relCurve C p.asIdeal.ResidueField).resHom inf_le_left
        (B.pulledEqn p.asIdeal.ResidueField i)) =
      ((1 : p.asIdeal.ResidueField) ⊗ₜ[R]
        (relCurve C R).resHom inf_le_left (B.eqn i)) := by
    apply e.injective
    rw [e.apply_symm_apply,
      B.toFinCoverData.ovlTermBaseChange_one_tmul p.asIdeal.ResidueField,
      B.toFinCoverData.ovlMap_resHom_left p.asIdeal.ResidueField]
    rfl
  change e.symm
      ((relCurve C p.asIdeal.ResidueField).resHom inf_le_left
        (B.pulledEqn p.asIdeal.ResidueField i)) ∈
    nonZeroDivisors
      (p.asIdeal.ResidueField ⊗[R]
        Γ(relCurve C R, B.pieces i ⊓ B.pieces j)) at hback
  rw [hinv] at hback
  have hflip := ringEquiv_mem_nonZeroDivisors
    (Algebra.TensorProduct.comm R p.asIdeal.ResidueField
      Γ(relCurve C R, B.pieces i ⊓ B.pieces j)).toRingEquiv hback
  change (Algebra.TensorProduct.comm R p.asIdeal.ResidueField
      Γ(relCurve C R, B.pieces i ⊓ B.pieces j))
      ((1 : p.asIdeal.ResidueField) ⊗ₜ[R]
        (relCurve C R).resHom inf_le_left (B.eqn i)) ∈
    nonZeroDivisors
      (Γ(relCurve C R, B.pieces i ⊓ B.pieces j) ⊗[R]
        p.asIdeal.ResidueField) at hflip
  rwa [Algebra.TensorProduct.comm_tmul] at hflip

omit [IsProper C.hom] in
/-- Every pairwise overlap colength of a generator adaptation is flat over the base. -/
theorem flat_ovlColength_of_seed (i j : B.index) :
    Module.Flat R (B.ovlColength i j) := by
  let f : Γ(relCurve C R, B.pieces i ⊓ B.pieces j) :=
    (relCurve C R).resHom inf_le_left (B.eqn i)
  letI : Module.Flat R Γ(relCurve C R, B.pieces i ⊓ B.pieces j) :=
    B.toFinCoverData.flat_sections_pieces_inf i j
  have hflat : Module.Flat R
      (Γ(relCurve C R, B.pieces i ⊓ B.pieces j) ⧸ Ideal.span {f}) :=
    Module.Flat.quotient_span_singleton_of_forall_tmul_residueField
      (fun p => B.ovlEqn_tmul_one_mem_nonZeroDivisors_of_seed hD i j p)
  have hideal := B.ovlIdeal_eq_span_left i j
  change B.ovlIdeal i j = Ideal.span {f} at hideal
  letI : Module.Flat R
      (Γ(relCurve C R, B.pieces i ⊓ B.pieces j) ⧸ Ideal.span {f}) := hflat
  exact Module.Flat.of_linearEquiv
    ((Submodule.quotEquivOfEq _ _ hideal).restrictScalars R)

omit [IsProper C.hom] in
/-- The product of all overlap colengths of a generator adaptation is flat over the
base. -/
theorem flat_ovlProd_of_seed : Module.Flat R B.ovlProd := by
  letI : forall p : B.index × B.index, Module.Flat R (B.ovlColength p.1 p.2) :=
    fun p => B.flat_ovlColength_of_seed hD p.1 p.2
  exact Module.Flat.pi_of_finite

end Seed

end DivisorAdaptation

end AlgebraicGeometry
