/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffMap
import AlgebraicJacobian.Picard.DivisorFamilyAffCompare
import AlgebraicJacobian.Picard.DivisorFamilyDegreeZeroRep

/-!
# The widened degree-zero divisor functor is terminal

The unit-equation proof for degree-zero certified divisors uses only the finite cover, its joint
coverage, and the equalizer certificate.  It therefore applies verbatim to arbitrary affine-open
covers.  Descending the result through the widened local-certification predicate makes every
degree-zero widened divisor value a singleton and represents the functor by the terminal object.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsAffineHom pi]

noncomputable section

namespace AffAdaptation

variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
  (A : AffAdaptation D d)

set_option linter.unusedSectionVars false in
/-- The constant section belongs to the widened glued equalizer. -/
theorem one_mem_gluedSubmodule : (1 : A.chartProd) ∈ A.gluedSubmodule := by
  rw [A.mem_gluedSubmodule_iff]
  intro p
  change A.toOvlLeft p.1 p.2 1 = A.toOvlRight p.1 p.2 1
  rw [map_one, map_one]

/-- A widened degree-zero certificate forces every adapted equation to be a unit. -/
theorem isUnit_eqn_of_isCertified_zero (hc : A.IsCertified 0) (j : D.index) :
    IsUnit (A.eqn j) := by
  haveI := hc.finite_glued
  haveI := hc.projective_glued
  haveI : Module.Flat R A.Glued := Module.Flat.of_projective
  haveI : Subsingleton A.Glued :=
    Module.rankAtStalk_eq_zero_iff_subsingleton.mp (funext fun p => hc.rankAtStalk_glued p)
  have h0 : (⟨(1 : A.chartProd), A.one_mem_gluedSubmodule⟩ : A.Glued) = 0 :=
    Subsingleton.elim _ _
  have hj : (1 : A.colength j) = 0 := congrFun (congrArg Subtype.val h0) j
  rw [← Ideal.span_singleton_eq_top (x := A.eqn j), Ideal.eq_top_iff_one]
  have hmk : Ideal.Quotient.mk (Ideal.span {A.eqn j}) 1 = 0 := hj
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmk

/-- A widened degree-zero certified system is divisor-equal to the trivial system. -/
theorem divEq_trivEqns_of_isCertified_zero (hc : A.IsCertified 0) :
    Scheme.LocalEquations.DivEq d (DivFamZar.trivEqns C R) := by
  classical
  choose piece hpiece using D.exists_mem_pieces
  refine ⟨⟨fun y => D.pieces (piece y) ⊓ d.cover.opens y,
      fun y => ⟨hpiece y, d.cover.mem_opens y⟩⟩,
    fun y => inf_le_right, fun _ => le_top, fun y => ?_⟩
  obtain ⟨u, hu⟩ := A.eqn_rel (piece y) y
  have hL : IsUnit (((relCurve C R).presheaf.map (homOfLE
      (inf_le_left : D.pieces (piece y) ⊓ d.cover.opens y
        ≤ D.pieces (piece y))).op).hom (A.eqn (piece y))) :=
    (A.isUnit_eqn_of_isCertified_zero hc (piece y)).map _
  rw [hu] at hL
  have hunit : IsUnit (((relCurve C R).presheaf.map (homOfLE
      (inf_le_right : D.pieces (piece y) ⊓ d.cover.opens y
        ≤ d.cover.opens y)).op).hom (d.eqn y)) :=
    isUnit_of_mul_isUnit_right hL
  refine ⟨hunit.unit, ?_⟩
  rw [DivFamZar.trivEqns_eqn, map_one, mul_one]
  exact hunit.unit_spec.symm

end AffAdaptation

set_option maxHeartbeats 1600000 in
-- The finite localization cover and relative-curve cover are transported through `ULift`.
/-- A widened locally certified degree-zero system is divisor-equal to the trivial system. -/
theorem divEq_trivEqns_of_isLocallyCertifiedAff_zero
    {d : (relCurve C R).LocalEquations} (hd : IsLocallyCertifiedAff 0 d) :
    Scheme.LocalEquations.DivEq d (DivFamZar.trivEqns C R) := by
  classical
  obtain ⟨m, f, hspan, hG⟩ := hd
  set f' : ULift.{u} (Fin m) → R := fun i => f i.down with hf'
  have hspan' : Ideal.span (Set.range f') = ⊤ := by
    rw [← hspan]
    congr 1
    exact Set.ext fun x =>
      ⟨fun ⟨i, hi⟩ => ⟨i.down, hi⟩, fun ⟨i, hi⟩ => ⟨ULift.up i, hi⟩⟩
  haveI : ∀ i : ULift.{u} (Fin m),
      IsOpenImmersion (relCurveMap C R (Localization.Away (f' i))) :=
    fun i => isOpenImmersion_relCurveMap_away C R (Localization.Away (f' i)) (f' i)
  refine Scheme.LocalEquations.divEq_of_divEq_pullback
    (fun i : ULift.{u} (Fin m) => relCurveMap C R (Localization.Away (f' i)))
    (fun y => exists_relCurveMap_base_eq C R f'
      (fun i => Localization.Away (f' i)) hspan' y)
    (fun i => Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
      (relCurveMap C R (Localization.Away (f' i))) d)
    (fun i => Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
      (relCurveMap C R (Localization.Away (f' i))) (DivFamZar.trivEqns C R))
    (fun i => ?_)
  obtain ⟨G, hGdiv⟩ := hG i.down
  exact (hGdiv.symm.trans
      (G.adaptation.divEq_trivEqns_of_isCertified_zero G.certified)).trans
    (divEq_pullback_trivEqns _ _).symm

instance instSubsingletonDivFamZarAffZero : Subsingleton (DivFamZarAff C R 0) := by
  refine ⟨fun x y => ?_⟩
  induction x using Quotient.ind with | _ d1 =>
  induction y using Quotient.ind with | _ d2 =>
  exact Quotient.sound
    ((divEq_trivEqns_of_isLocallyCertifiedAff_zero d1.2).trans
      (divEq_trivEqns_of_isLocallyCertifiedAff_zero d2.2).symm)

namespace DivFamZarAff

/-- The trivial widened degree-zero class. -/
noncomputable def trivZarAff : DivFamZarAff C R 0 :=
  (DivFamZar.trivFam C R pi).toAff.toZarAff

theorem mapAlgHom_trivZarAff {A A' : Type u} [CommRing A] [Algebra k A]
    [CommRing A'] [Algebra k A'] (phi : A →ₐ[k] A') :
    DivFamZarAff.mapAlgHom phi (trivZarAff (C := C) (pi := pi) (R := A)) =
      trivZarAff (C := C) (pi := pi) (R := A') :=
  Subsingleton.elim _ _

/-- The constant trivial class is a widened degree-zero section on every test. -/
noncomputable def trivSectionAff (T : Over (Spec (.of k))) : divFamZarAff C 0 T :=
  ⟨fun _ => trivZarAff (C := C) (pi := pi),
    fun _ _ h => mapAlgHom_trivZarAff (C := C) (pi := pi) (Over.resAlgHom T h)⟩

end DivFamZarAff

instance instSubsingletonDivFamZarAffSectionZero (T : Over (Spec (.of k))) :
    Subsingleton (divFamZarAff C 0 T) :=
  ⟨fun _ _ => Subtype.ext (funext fun _ => Subsingleton.elim _ _)⟩

/-- The widened degree-zero divisor functor is represented by the terminal object. -/
noncomputable def divFunctorAffZeroRepresentableBy :
    (divFunctorAff C 0).RepresentableBy (Over.mk (𝟙 (Spec (.of k)))) where
  homEquiv {T} :=
    { toFun := fun _ => DivFamZarAff.trivSectionAff (C := C) (pi := pi) T
      invFun := fun _ => Over.mkIdTerminal.from T
      left_inv := fun f => Over.mkIdTerminal.hom_ext _ f
      right_inv := fun _ =>
        (instSubsingletonDivFamZarAffSectionZero T).allEq _ _ }
  homEquiv_comp {T _} _ _ :=
    (instSubsingletonDivFamZarAffSectionZero T).allEq _ _

end

end AlgebraicGeometry
