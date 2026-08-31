/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaFinite
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaCech
import AlgebraicJacobian.Picard.DivisorFamilyAffGlue

/-!
# Intrinsic theta descent on a swallowed widened cover

On a cover `SwallowedBy d`, one affine piece contains the whole divisor support and every
other piece misses it.  The ordinary colength Cech differential is therefore zero.  The same
collapse holds for the intrinsic theta quotients: off the swallowing diagonal the overlap
colength, hence its invertible theta quotient, is trivial; on the diagonal the two restriction
maps agree.

This file records that collapse in the intrinsic, chart-free theta model.  It is the reduction
needed to transport the invertible module on the swallowing piece to the global equalizer,
without a `ChartTyping` or an additional certificate clause.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsProper C.hom]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
variable {A : AffAdaptation D d}
variable {g : Nat}

namespace AffAdaptation

attribute [local instance] thetaPieceQuotientModule thetaOverlapQuotientModule
  thetaPieceQuotientBaseModule thetaOverlapQuotientBaseModule
  thetaPieceQuotientGluedModule thetaOverlapQuotientGluedModule

/-- On a diagonal overlap, the two intrinsic theta restriction maps agree. -/
theorem thetaToOverlap_diag_eq (A : AffAdaptation D d) (a : Nat) (i : D.index) :
    A.thetaToOverlapLeft (π := pi) a i i =
      A.thetaToOverlapRight (π := pi) a i i := by
  apply DFunLike.ext _ _
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ s =>
      rw [A.thetaToOverlapLeft_mk, A.thetaToOverlapRight_mk]

/-- On a swallowed cover the intrinsic theta Cech differential is zero. -/
theorem thetaIntrinsicDeltaSub_eq_zero_of_swallowedBy (A : AffAdaptation D d)
    (a : Nat) (h : D.SwallowedBy d) :
    A.thetaIntrinsicDeltaLeftGlued (π := pi) a -
        A.thetaIntrinsicDeltaRightGlued (π := pi) a = 0 := by
  obtain ⟨j0, _, hmiss⟩ := h
  apply LinearMap.ext
  intro s
  funext p
  by_cases hp : p.1 = p.2
  · obtain ⟨i, j⟩ := p
    cases hp
    simp only [LinearMap.sub_apply, thetaIntrinsicDeltaLeftGlued,
      thetaIntrinsicDeltaRightGlued, LinearMap.pi_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.proj_apply, Pi.sub_apply,
      thetaToOverlapLeftGlued, thetaToOverlapRightGlued]
    have hdiag := DFunLike.congr_fun (A.thetaToOverlap_diag_eq a i) (s i)
    exact sub_eq_zero.mpr hdiag
  · haveI : Subsingleton (A.ovlColength p.1 p.2) := by
      by_cases h1 : p.1 = j0
      · exact A.subsingleton_ovlColength_of_swallowedBy hmiss p.1 p.2
          (Or.inr fun h2 => hp (h1.trans h2.symm))
      · exact A.subsingleton_ovlColength_of_swallowedBy hmiss p.1 p.2 (Or.inl h1)
    haveI : Subsingleton (A.ThetaOverlapQuotient (π := pi) a p.1 p.2) :=
      Module.subsingleton (A.ovlColength p.1 p.2)
        (A.ThetaOverlapQuotient (π := pi) a p.1 p.2)
    exact Subsingleton.elim _ _

/-- The underlying `R`-linear intrinsic Cech differential also vanishes on a swallowed cover. -/
theorem thetaIntrinsicDelta_eq_zero_of_swallowedBy (A : AffAdaptation D d)
    (a : Nat) (h : D.SwallowedBy d) :
    A.thetaIntrinsicDeltaLeft (π := pi) a -
        A.thetaIntrinsicDeltaRight (π := pi) a = 0 := by
  obtain ⟨j0, _, hmiss⟩ := h
  apply LinearMap.ext
  intro s
  funext p
  by_cases hp : p.1 = p.2
  · obtain ⟨i, j⟩ := p
    cases hp
    simp only [LinearMap.sub_apply, thetaIntrinsicDeltaLeft,
      thetaIntrinsicDeltaRight, LinearMap.pi_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.proj_apply, Pi.sub_apply,
      thetaToOverlapLeftLinear, thetaToOverlapRightLinear]
    have hdiag := DFunLike.congr_fun (A.thetaToOverlap_diag_eq a i) (s i)
    exact sub_eq_zero.mpr hdiag
  · haveI : Subsingleton (A.ovlColength p.1 p.2) := by
      by_cases h1 : p.1 = j0
      · exact A.subsingleton_ovlColength_of_swallowedBy hmiss p.1 p.2
          (Or.inr fun h2 => hp (h1.trans h2.symm))
      · exact A.subsingleton_ovlColength_of_swallowedBy hmiss p.1 p.2 (Or.inl h1)
    haveI : Subsingleton (A.ThetaOverlapQuotient (π := pi) a p.1 p.2) :=
      Module.subsingleton (A.ovlColength p.1 p.2)
        (A.ThetaOverlapQuotient (π := pi) a p.1 p.2)
    exact Subsingleton.elim _ _

/-- Hence every family of piece theta quotients satisfies the intrinsic Cech condition. -/
theorem intrinsicThetaGluedKernelOver_eq_top_of_swallowedBy
    (A : AffAdaptation D d) (a : Nat) (h : D.SwallowedBy d) :
    A.intrinsicThetaGluedKernelOver (π := pi) a = ⊤ := by
  rw [intrinsicThetaGluedKernelOver,
    A.thetaIntrinsicDeltaSub_eq_zero_of_swallowedBy a h]
  exact LinearMap.ker_zero

/-- The intrinsic equalizer carrier over the test ring is all of the piece product. -/
theorem intrinsicThetaGluedSubmodule_eq_top_of_swallowedBy
    (A : AffAdaptation D d) (a : Nat) (h : D.SwallowedBy d) :
    A.intrinsicThetaGluedSubmodule (π := pi) a = ⊤ := by
  rw [intrinsicThetaGluedSubmodule,
    A.thetaIntrinsicDelta_eq_zero_of_swallowedBy a h]
  exact LinearMap.ker_zero

/-- On a swallowed cover, intrinsic theta descent is the whole product of piece quotients. -/
noncomputable def intrinsicThetaGluedOverEquivPieceProdOfSwallowedBy
    (A : AffAdaptation D d) (a : Nat) (h : D.SwallowedBy d) :
    A.IntrinsicThetaGluedOver (π := pi) a ≃ₗ[↥(gluedSubalgebra A)]
      A.ThetaPieceProd (π := pi) a :=
  (LinearEquiv.ofEq _ _ (A.intrinsicThetaGluedOver_eq_ker (π := pi) a)).trans
    ((LinearEquiv.ofEq _ _
      (A.intrinsicThetaGluedKernelOver_eq_top_of_swallowedBy (pi := pi) a h)).trans
      Submodule.topEquiv)

/-- The `A_D`-linear collapse, restricted along `R → A_D`. -/
noncomputable def intrinsicThetaGluedOverEquivPieceProdBaseOfSwallowedBy
    (A : AffAdaptation D d) (a : Nat) (h : D.SwallowedBy d) :
    letI : Module R (A.IntrinsicThetaGluedOver (π := pi) a) :=
      Module.compHom _ (algebraMap R ↥(gluedSubalgebra A))
    A.IntrinsicThetaGluedOver (π := pi) a ≃ₗ[R]
      A.ThetaPieceProd (π := pi) a := by
  let AD := ↥(gluedSubalgebra A)
  let M := A.IntrinsicThetaGluedOver (π := pi) a
  letI : Module R M := Module.compHom M (algebraMap R AD)
  let eAD := A.intrinsicThetaGluedOverEquivPieceProdOfSwallowedBy
    (pi := pi) a h
  refine { __ := eAD.toEquiv
           map_add' := eAD.map_add
           map_smul' := fun r x => ?_ }
  exact eAD.map_smul (algebraMap R AD r) x

/-- Evaluation at the swallowing piece identifies the theta product with that piece. -/
noncomputable def thetaPieceProdEquivSwallowingPiece
    (A : AffAdaptation D d) (a : Nat) {j0 : D.index}
    (hmiss : ∀ j : D.index, j ≠ j0 →
      Disjoint d.supportLocus (D.pieces j : Set (relCurve C R))) :
    A.ThetaPieceProd (π := pi) a ≃ₗ[R]
      A.ThetaPieceQuotient (π := pi) a j0 := by
  let ev : A.ThetaPieceProd (π := pi) a →ₗ[R]
      A.ThetaPieceQuotient (π := pi) a j0 := LinearMap.proj j0
  apply LinearEquiv.ofBijective ev
  constructor
  · intro x y hxy
    funext j
    by_cases hj : j = j0
    · subst j
      exact hxy
    · haveI : Subsingleton (A.colength j) :=
        A.subsingleton_colength_of_ne_swallowing hmiss j hj
      haveI : Subsingleton (A.ThetaPieceQuotient (π := pi) a j) :=
        Module.subsingleton (A.colength j)
          (A.ThetaPieceQuotient (π := pi) a j)
      exact Subsingleton.elim _ _
  · intro x
    refine ⟨Pi.single j0 x, ?_⟩
    simp [ev]

/-- Evaluation identifies the ordinary colength product with the swallowing colength. -/
noncomputable def chartProdEquivSwallowingPiece
    (A : AffAdaptation D d) {j0 : D.index}
    (hmiss : ∀ j : D.index, j ≠ j0 →
      Disjoint d.supportLocus (D.pieces j : Set (relCurve C R))) :
    A.chartProd ≃ₗ[R] A.colength j0 := by
  let ev : A.chartProd →ₗ[R] A.colength j0 := LinearMap.proj j0
  apply LinearEquiv.ofBijective ev
  constructor
  · intro x y hxy
    funext j
    by_cases hj : j = j0
    · subst j
      exact hxy
    · haveI : Subsingleton (A.colength j) :=
        A.subsingleton_colength_of_ne_swallowing hmiss j hj
      exact Subsingleton.elim _ _
  · intro x
    refine ⟨Pi.single j0 x, ?_⟩
    simp [ev]

/-- On a swallowed cover, evaluation identifies the equalizer algebra with the swallowing
piece colength algebra. -/
noncomputable def gluedSubalgebraEquivSwallowingPiece
    (A : AffAdaptation D d) {j0 : D.index}
    (hsub : d.supportLocus ⊆ (D.pieces j0 : Set (relCurve C R)))
    (hmiss : ∀ j : D.index, j ≠ j0 →
      Disjoint d.supportLocus (D.pieces j : Set (relCurve C R))) :
    ↥(gluedSubalgebra A) ≃ₐ[R] A.colength j0 := by
  apply AlgEquiv.ofBijective (A.gluedSubalgebraPieceMap j0)
  constructor
  · intro x y hxy
    apply Subtype.ext
    funext j
    by_cases hj : j = j0
    · subst j
      exact hxy
    · haveI : Subsingleton (A.colength j) :=
        A.subsingleton_colength_of_ne_swallowing hmiss j hj
      exact Subsingleton.elim _ _
  · intro x
    refine ⟨⟨Pi.single j0 x, ?_⟩, ?_⟩
    · change Pi.single j0 x ∈ A.gluedSubmodule
      rw [A.gluedSubmodule_eq_top_of_swallowedBy ⟨j0, hsub, hmiss⟩]
      trivial
    · simp [gluedSubalgebraPieceMap]

/-- Finite `R`-module transport for the `A_D`-linear intrinsic carrier on a swallowed cover. -/
theorem IsCertified.finite_intrinsicThetaGluedOver_of_swallowedBy
    (A : AffAdaptation D d) (hc : A.IsCertified g) (a : Nat) (h : D.SwallowedBy d) :
    letI : Module R (A.IntrinsicThetaGluedOver (π := pi) a) :=
      Module.compHom _ (algebraMap R ↥(gluedSubalgebra A))
    Module.Finite R (A.IntrinsicThetaGluedOver (π := pi) a) := by
  obtain ⟨j0, hsub, hmiss⟩ := h
  let AD := ↥(gluedSubalgebra A)
  let M := A.IntrinsicThetaGluedOver (π := pi) a
  letI : Module R M := Module.compHom M (algebraMap R AD)
  let e : M ≃ₗ[R] A.ThetaPieceQuotient (π := pi) a j0 :=
    (A.intrinsicThetaGluedOverEquivPieceProdBaseOfSwallowedBy
      (pi := pi) a ⟨j0, hsub, hmiss⟩).trans
        (A.thetaPieceProdEquivSwallowingPiece (pi := pi) a hmiss)
  haveI : Module.Finite R (A.colength j0) := hc.finite_colength j0
  haveI : IsScalarTower R (A.colength j0)
      (A.ThetaPieceQuotient (π := pi) a j0) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Invertible (A.colength j0)
      (A.ThetaPieceQuotient (π := pi) a j0) :=
    A.invertible_thetaPieceQuotient (π := pi) a j0
  haveI : Module.Finite R
      (A.ThetaPieceQuotient (π := pi) a j0) :=
    Module.Invertible.finite_trans (A := A.colength j0)
  exact Module.Finite.equiv e.symm

/-- Projective `R`-module transport for the `A_D`-linear intrinsic carrier on a swallowed cover. -/
theorem IsCertified.projective_intrinsicThetaGluedOver_of_swallowedBy
    (A : AffAdaptation D d) (hc : A.IsCertified g) (a : Nat) (h : D.SwallowedBy d) :
    letI : Module R (A.IntrinsicThetaGluedOver (π := pi) a) :=
      Module.compHom _ (algebraMap R ↥(gluedSubalgebra A))
    Module.Projective R (A.IntrinsicThetaGluedOver (π := pi) a) := by
  obtain ⟨j0, hsub, hmiss⟩ := h
  let AD := ↥(gluedSubalgebra A)
  let M := A.IntrinsicThetaGluedOver (π := pi) a
  letI : Module R M := Module.compHom M (algebraMap R AD)
  let e : M ≃ₗ[R] A.ThetaPieceQuotient (π := pi) a j0 :=
    (A.intrinsicThetaGluedOverEquivPieceProdBaseOfSwallowedBy
      (pi := pi) a ⟨j0, hsub, hmiss⟩).trans
        (A.thetaPieceProdEquivSwallowingPiece (pi := pi) a hmiss)
  haveI : Module.Projective R (A.colength j0) := hc.projective_colength j0
  haveI : IsScalarTower R (A.colength j0)
      (A.ThetaPieceQuotient (π := pi) a j0) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Invertible (A.colength j0)
      (A.ThetaPieceQuotient (π := pi) a j0) :=
    A.invertible_thetaPieceQuotient (π := pi) a j0
  haveI : Module.Projective R
      (A.ThetaPieceQuotient (π := pi) a j0) :=
    Module.Invertible.projective_trans (A := A.colength j0)
  exact Module.Projective.of_equiv e.symm

set_option synthInstance.maxHeartbeats 300000 in
-- The dependent `A_D`/piece module instances need a larger search budget here.
/-- Rank transport from the intrinsic `A_D`-carrier to the swallowing theta piece. -/
theorem rankAtStalk_intrinsicThetaGluedOver_eq_swallowingPiece
    (A : AffAdaptation D d) (a : Nat) {j0 : D.index}
    (hsub : d.supportLocus ⊆ (D.pieces j0 : Set (relCurve C R)))
    (hmiss : ∀ j : D.index, j ≠ j0 →
      Disjoint d.supportLocus (D.pieces j : Set (relCurve C R)))
    (p : PrimeSpectrum R) :
    letI : Module R (A.IntrinsicThetaGluedOver (π := pi) a) :=
      Module.compHom _ (algebraMap R ↥(gluedSubalgebra A))
    Module.rankAtStalk (R := R) (A.IntrinsicThetaGluedOver (π := pi) a) p =
      Module.rankAtStalk (R := R)
        (A.ThetaPieceQuotient (π := pi) a j0) p := by
  let AD := ↥(gluedSubalgebra A)
  let M := A.IntrinsicThetaGluedOver (π := pi) a
  letI : Module R M := Module.compHom M (algebraMap R AD)
  let e :=
    (A.intrinsicThetaGluedOverEquivPieceProdBaseOfSwallowedBy
      (pi := pi) a ⟨j0, hsub, hmiss⟩).trans
      (A.thetaPieceProdEquivSwallowingPiece (pi := pi) a hmiss)
  exact congrFun (Module.rankAtStalk_eq_of_equiv e) p

set_option synthInstance.maxHeartbeats 300000 in
-- The rank calculation transports through two dependent module equivalences.
/-- The certified rank survives the swallowed theta descent, with no added certificate clause. -/
theorem IsCertified.rankAtStalk_intrinsicThetaGluedOver_of_swallowedBy
    (A : AffAdaptation D d) (hc : A.IsCertified g) (a : Nat)
    (h : D.SwallowedBy d) (p : PrimeSpectrum R) :
    letI : Module R (A.IntrinsicThetaGluedOver (π := pi) a) :=
      Module.compHom _ (algebraMap R ↥(gluedSubalgebra A))
    Module.rankAtStalk (R := R) (A.IntrinsicThetaGluedOver (π := pi) a) p = g := by
  obtain ⟨j0, hsub, hmiss⟩ := h
  let AD := ↥(gluedSubalgebra A)
  let M := A.IntrinsicThetaGluedOver (π := pi) a
  letI : Module R M := Module.compHom M (algebraMap R AD)
  let e : M ≃ₗ[R] A.ThetaPieceQuotient (π := pi) a j0 :=
    (A.intrinsicThetaGluedOverEquivPieceProdBaseOfSwallowedBy
      (pi := pi) a ⟨j0, hsub, hmiss⟩).trans
        (A.thetaPieceProdEquivSwallowingPiece (pi := pi) a hmiss)
  have hpiece : Module.rankAtStalk
      (A.ThetaPieceQuotient (π := pi) a j0) p =
      Module.rankAtStalk (A.colength j0) p := by
    letI : Module.Finite R (A.colength j0) := hc.finite_colength j0
    letI : Module.Projective R (A.colength j0) := hc.projective_colength j0
    letI : IsScalarTower R (A.colength j0)
        (A.ThetaPieceQuotient (π := pi) a j0) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    letI : Module.Invertible (A.colength j0)
        (A.ThetaPieceQuotient (π := pi) a j0) :=
      A.invertible_thetaPieceQuotient (π := pi) a j0
    exact Module.Invertible.rankAtStalk_eq_of_module_finite p
  have hcolength : Module.rankAtStalk (A.colength j0) p = g := by
    let ecol : A.Glued ≃ₗ[R] A.colength j0 :=
      (A.gluedEquivChartProd_of_swallowedBy ⟨j0, hsub, hmiss⟩).trans
        (A.chartProdEquivSwallowingPiece hmiss)
    calc
      Module.rankAtStalk (A.colength j0) p = Module.rankAtStalk A.Glued p :=
        (congrFun (Module.rankAtStalk_eq_of_equiv ecol) p).symm
      _ = g := hc.rankAtStalk_glued p
  calc
    Module.rankAtStalk M p =
        Module.rankAtStalk (A.ThetaPieceQuotient (π := pi) a j0) p :=
      congrFun (Module.rankAtStalk_eq_of_equiv e) p
    _ = Module.rankAtStalk (A.colength j0) p := hpiece
    _ = g := hcolength

/-- The same swallowed descent equivalence, viewed in `R`-modules. -/
noncomputable def intrinsicThetaGluedEquivPieceProdOfSwallowedBy
    (A : AffAdaptation D d) (a : Nat) (h : D.SwallowedBy d) :
    A.IntrinsicThetaGlued (π := pi) a ≃ₗ[R] A.ThetaPieceProd (π := pi) a :=
  (LinearEquiv.ofEq _ _ (A.intrinsicThetaGluedSubmodule_eq_top_of_swallowedBy (pi := pi) a h)).trans
    Submodule.topEquiv

/-- Finite intrinsic theta descent on a swallowed cover. -/
theorem IsCertified.finite_intrinsicThetaGlued_of_swallowedBy
    (hc : A.IsCertified g) (a : Nat) (h : D.SwallowedBy d) :
    Module.Finite R (A.IntrinsicThetaGlued (π := pi) a) := by
  letI : ∀ j : D.index, Module R (A.ThetaPieceQuotient (π := pi) a j) :=
    fun j => A.thetaPieceQuotientBaseModule (π := pi) a j
  letI : Module.Finite R (A.ThetaPieceProd (π := pi) a) := by
    letI : ∀ j : D.index, Module.Finite R
        (A.ThetaPieceQuotient (π := pi) a j) :=
      fun j => by
        letI : Module.Finite R (A.colength j) := hc.finite_colength j
        letI : IsScalarTower R (A.colength j)
            (A.ThetaPieceQuotient (π := pi) a j) :=
          IsScalarTower.of_algebraMap_smul fun _ _ => rfl
        letI : Module.Invertible (A.colength j)
            (A.ThetaPieceQuotient (π := pi) a j) :=
          A.invertible_thetaPieceQuotient (π := pi) a j
        exact Module.Invertible.finite_trans (A := A.colength j)
    exact Module.Finite.pi
  exact Module.Finite.equiv
    (A.intrinsicThetaGluedEquivPieceProdOfSwallowedBy (pi := pi) a h).symm

/-- Projective intrinsic theta descent on a swallowed cover. -/
theorem IsCertified.projective_intrinsicThetaGlued_of_swallowedBy
    (hc : A.IsCertified g) (a : Nat) (h : D.SwallowedBy d) :
    Module.Projective R (A.IntrinsicThetaGlued (π := pi) a) := by
  letI : ∀ j : D.index, Module R (A.ThetaPieceQuotient (π := pi) a j) :=
    fun j => A.thetaPieceQuotientBaseModule (π := pi) a j
  letI : ∀ j : D.index, Module.Projective R
      (A.ThetaPieceQuotient (π := pi) a j) :=
    fun j => by
      letI : Module.Projective R (A.colength j) := hc.projective_colength j
      letI : IsScalarTower R (A.colength j)
          (A.ThetaPieceQuotient (π := pi) a j) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      letI : Module.Invertible (A.colength j)
          (A.ThetaPieceQuotient (π := pi) a j) :=
        A.invertible_thetaPieceQuotient (π := pi) a j
      exact Module.Invertible.projective_trans (A := A.colength j)
  letI : Module.Projective R (A.ThetaPieceProd (π := pi) a) := by
    exact Module.Projective.of_equiv
      (DirectSum.linearEquivFunOnFintype R D.index
        (fun j => A.ThetaPieceQuotient (π := pi) a j))
  exact Module.Projective.of_equiv
    (A.intrinsicThetaGluedEquivPieceProdOfSwallowedBy (pi := pi) a h).symm

/-- Invertibility is stable under transport along a ring equivalence.  The target module
action is the pulled-back action, so this is a direct base-change fact rather than a new
geometric hypothesis. -/
theorem _root_.Module.Invertible.of_ringEquiv
    {S T M : Type u} [CommRing S] [CommRing T] [AddCommGroup M]
    [Module S M] (e : S ≃+* T) [Module.Invertible S M] :
    letI : Algebra S T := e.toRingHom.toAlgebra
    letI : Module T M := Module.compHom M e.symm.toRingHom
    Module.Invertible T M := by
  letI : Algebra S T := e.toRingHom.toAlgebra
  letI : Module T M := Module.compHom M e.symm.toRingHom
  letI : IsScalarTower S T M :=
    ⟨fun s t m => by
      change e.symm (e s * t) • m = s • (e.symm t • m)
      rw [map_mul, e.symm_apply_apply, mul_smul]⟩
  letI : Algebra.IsEpi S T :=
    Algebra.isEpi_of_surjective_algebraMap S T (by
      intro t
      refine ⟨e.symm t, ?_⟩
      change e (e.symm t) = t
      exact e.apply_symm_apply t)
  haveI : Module.Invertible T (TensorProduct S T M) := inferInstance
  exact Module.Invertible.congr (TensorProduct.lid' S T M)

/-- Evaluation at the swallowing piece, with the canonical `A_D`-module action. -/
noncomputable def thetaPieceProdEquivSwallowingPieceOver
    (A : AffAdaptation D d) (a : Nat) {j0 : D.index}
    (hmiss : ∀ j : D.index, j ≠ j0 →
      Disjoint d.supportLocus (D.pieces j : Set (relCurve C R))) :
    A.ThetaPieceProd (π := pi) a ≃ₗ[↥(gluedSubalgebra A)]
      A.ThetaPieceQuotient (π := pi) a j0 := by
  letI : Module ↥(gluedSubalgebra A)
      (A.ThetaPieceQuotient (π := pi) a j0) :=
    A.thetaPieceQuotientGluedModule (π := pi) a j0
  let ev : A.ThetaPieceProd (π := pi) a →ₗ[↥(gluedSubalgebra A)]
      A.ThetaPieceQuotient (π := pi) a j0 := LinearMap.proj j0
  apply LinearEquiv.ofBijective ev
  constructor
  · intro x y hxy
    funext j
    by_cases hj : j = j0
    · subst j
      exact hxy
    · haveI : Subsingleton (A.colength j) :=
        A.subsingleton_colength_of_ne_swallowing hmiss j hj
      haveI : Subsingleton (A.ThetaPieceQuotient (π := pi) a j) :=
        Module.subsingleton (A.colength j)
          (A.ThetaPieceQuotient (π := pi) a j)
      exact Subsingleton.elim _ _
  · intro x
    refine ⟨Pi.single j0 x, ?_⟩
    simp [ev]

set_option synthInstance.maxHeartbeats 300000 in
-- The final transport crosses the equalizer algebra and its distinguished piece algebra.
/-- The intrinsic theta carrier is invertible over the swallowed equalizer algebra. -/
theorem Module.Invertible.intrinsicThetaGluedOver_of_swallowedBy
    (A : AffAdaptation D d) (a : Nat) (h : D.SwallowedBy d) :
    Module.Invertible (↥(gluedSubalgebra A))
      (A.IntrinsicThetaGluedOver (π := pi) a) := by
  obtain ⟨j0, hsub, hmiss⟩ := h
  let AD := ↥(gluedSubalgebra A)
  let N := A.ThetaPieceQuotient (π := pi) a j0
  let φ := A.gluedSubalgebraEquivSwallowingPiece hsub hmiss
  letI : Module (A.colength j0) N :=
    A.thetaPieceQuotientModule (π := pi) a j0
  letI : Module AD N := Module.compHom N φ.toRingHom
  haveI : Module.Invertible (A.colength j0) N :=
    A.invertible_thetaPieceQuotient (π := pi) a j0
  haveI : Module.Invertible AD N :=
    Module.Invertible.of_ringEquiv φ.symm.toRingEquiv
  let e : A.IntrinsicThetaGluedOver (π := pi) a ≃ₗ[AD] N :=
    (A.intrinsicThetaGluedOverEquivPieceProdOfSwallowedBy
      (pi := pi) a ⟨j0, hsub, hmiss⟩).trans
        (A.thetaPieceProdEquivSwallowingPieceOver (pi := pi) a hmiss)
  exact Module.Invertible.congr e.symm

/-- Field-style entry point for the swallowed intrinsic invertibility producer. -/
theorem invertible_intrinsicThetaGluedOver_of_swallowedBy
    (A : AffAdaptation D d) (a : Nat) (h : D.SwallowedBy d) :
    Module.Invertible (↥(gluedSubalgebra A))
      (A.IntrinsicThetaGluedOver (π := pi) a) :=
  Module.Invertible.intrinsicThetaGluedOver_of_swallowedBy A a h

end AffAdaptation

end AlgebraicGeometry
