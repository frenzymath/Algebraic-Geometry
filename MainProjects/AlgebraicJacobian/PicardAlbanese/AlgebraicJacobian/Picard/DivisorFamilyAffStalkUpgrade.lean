/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffFieldMono

/-!
# Stalk generation from a widened certified adaptation

The flat-colength Nakayama step used by divisor-window separation depends only on an affine
piece carrying a regular local equation.  This file states that step for an arbitrary
`AffAdaptation`; no piece is assigned to either fixed projective-line chart.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.stalkOverAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

variable (A : AffAdaptation D d)

/-- Two sections differing by a unit factor generate the same principal ideal. -/
private lemma span_eq_of_unit_mul {S : Type u} [CommRing S] {a b c : S} (hc : IsUnit c)
    (h : a = c * b) : Ideal.span {a} = Ideal.span {b} := by
  obtain ⟨v, rfl⟩ := hc
  refine le_antisymm
    (Ideal.span_singleton_le_span_singleton.mpr ⟨v, by rw [h, mul_comm]⟩)
    (Ideal.span_singleton_le_span_singleton.mpr ⟨(↑v⁻¹ : S), ?_⟩)
  rw [h, mul_comm (v : S) b, mul_assoc, Units.mul_inv, mul_one]

/-- A widened piece equation generates the family stalk ideal at each point of that piece. -/
private lemma stalkIdeal_eq_span_germ_eqn (j : D.index) {z : relCurve C R}
    (hz : z ∈ D.pieces j) :
    d.stalkIdeal z =
      Ideal.span {((relCurve C R).presheaf.germ (D.pieces j) z hz).hom (A.eqn j)} := by
  obtain ⟨v, hv⟩ := A.eqn_rel j z
  have hzW : z ∈ D.pieces j ⊓ d.cover.opens z := ⟨hz, d.cover.mem_opens z⟩
  have hgerm := congrArg ((relCurve C R).presheaf.germ
    (D.pieces j ⊓ d.cover.opens z) z hzW).hom hv
  rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hgerm
  exact (span_eq_of_unit_mul (v.isUnit.map ((relCurve C R).presheaf.germ
    (D.pieces j ⊓ d.cover.opens z) z hzW).hom) hgerm).symm

/-- If a stalk ideal is covered by a smaller ideal modulo base directions contained in the
stalk maximal ideal, projectivity of the widened piece colength removes those directions.
This is the cover-generic flat-quotient/Nakayama upgrade used by window recovery. -/
theorem stalkIdeal_eq_of_le_sup_map
    (hproj : ∀ j, Module.Projective R (A.colength j)) {z : relCurve C R}
    {s : Ideal R}
    (hs : ∀ r ∈ s, algebraMap R ((relCurve C R).presheaf.stalk z) r ∈
      IsLocalRing.maximalIdeal ((relCurve C R).presheaf.stalk z))
    {E : Ideal ((relCurve C R).presheaf.stalk z)} (hE : E ≤ d.stalkIdeal z)
    (hcov : d.stalkIdeal z ≤
      E ⊔ Ideal.map (algebraMap R ((relCurve C R).presheaf.stalk z)) s) :
    d.stalkIdeal z = E := by
  obtain ⟨j, hz⟩ := D.exists_mem_pieces z
  letI : Algebra Γ(relCurve C R, D.pieces j) ((relCurve C R).presheaf.stalk z) :=
    (relCurve C R).presheaf.algebra_section_stalk ⟨z, hz⟩
  haveI hloc := (D.isAffineOpen_pieces j).isLocalization_stalk ⟨z, hz⟩
  haveI htower : IsScalarTower R Γ(relCurve C R, D.pieces j)
      ((relCurve C R).presheaf.stalk z) :=
    Scheme.stalkOverAlgebra_isScalarTower R hz
  haveI : Module.Projective R (A.colength j) := hproj j
  haveI hflat : Module.Flat R
      (Γ(relCurve C R, D.pieces j) ⧸ Ideal.span {A.eqn j}) :=
    Module.Flat.of_projective
  have hspan := A.stalkIdeal_eq_span_germ_eqn j hz
  have halg : ((relCurve C R).presheaf.germ (D.pieces j) z hz).hom (A.eqn j) =
      algebraMap Γ(relCurve C R, D.pieces j) ((relCurve C R).presheaf.stalk z)
        (A.eqn j) := rfl
  rw [hspan, halg] at hE hcov ⊢
  exact span_singleton_algebraMap_eq_of_le_sup_map
    ((D.isAffineOpen_pieces j).primeIdealOf ⟨z, hz⟩).asIdeal
    (A.eqn_mem_nonZeroDivisors j) hs hE hcov

end AffAdaptation

end AlgebraicGeometry
