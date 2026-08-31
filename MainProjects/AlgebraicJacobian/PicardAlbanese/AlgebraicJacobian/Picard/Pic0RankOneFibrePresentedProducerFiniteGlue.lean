/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneFibrePresentedProducerAwayNaturality
import AlgebraicJacobian.Picard.PicEtAffZariskiSep
import AlgebraicJacobian.Picard.CechKernelLemma

/-!
# Finite gluing of the rank-one evaluation divisor on a presentation carrier

Over the Noetherian affine carrier of a tied rank-one presentation, the local evaluation
divisors produced on a finite spanning family of principal opens are compatible on pairwise
overlaps.  They therefore glue to an actual `DivFamZarAff` on the carrier.  Zariski separation
of `PicEtAff` identifies the Abel value of the glue with the represented input class, and
injectivity of the etale-plus unit identifies its relative Picard class with the presentation
representative.  The chosen local sections retain their exact Cech-class and native evaluation
identities.

This is deliberately only a Noetherian, presentation-carrier result.  It does **not** descend
the glued divisor through the etale cover to the original algebra `A`, does not prove
independence of the chosen presentation, does not construct an arbitrary-scheme pullback
square, and does not produce `PicRankOneOpen.FibrePresented`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {A : Type u} [CommRing A] [Algebra k A]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}

namespace PicRankOneLocalPresentation

set_option maxHeartbeats 3200000 in
/-- The finite principal-open evaluation divisors of a tied rank-one presentation glue on its
Noetherian etale carrier.  The result records the global Abel and relative-Picard identities,
while retaining the exact local Cech-class and evaluation identities of the chosen sections.

The divisor `F0` lives over `P.cover.Carrier`; this theorem neither descends it to `A` nor
constructs `PicRankOneOpen.FibrePresented`. -/
theorem exists_glued_rankOne_away_divisor_with_abel_evaluation
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier] :
    ∃ (m : ℕ) (f : Fin m → P.cover.Carrier)
      (y : Fin m → Sheaf.HModule P.datum.sheaf 0)
      (hy : ∀ (i : Fin m) (q : PrimeSpectrum P.cover.Carrier),
        f i ∉ q.asIdeal →
          (y i ⊗ₜ (1 : q.asIdeal.ResidueField) :
            Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
              q.asIdeal.ResidueField) ≠ 0)
      (F0 : DivFamZarAff C P.cover.Carrier (genus C)),
      Ideal.span (Set.range f) = ⊤ ∧
        (∀ i : Fin m,
          DivFamZarAff.mapAlgHom
              (IsScalarTower.toAlgHom k P.cover.Carrier
                (Localization.Away (f i))) F0 =
            P.baseOpenRankOneDivisor (f i) (y i) (hy i)) ∧
        abelDivAffPlus C P.cover.Carrier F0 =
          PicEtAff.mapAlg C
            ((Algebra.ofId A P.cover.Carrier).restrictScalars k)
            (picEtAffineEquiv C A lam.1) ∧
        relPicMk C (overSpec k P.cover.Carrier) F0.picClass =
          (P.representative : relPic C (overSpec k P.cover.Carrier)) ∧
        (∀ i : Fin m,
          (DivFamZarAff.mapAlgHom
              (IsScalarTower.toAlgHom k P.cover.Carrier
                (Localization.Away (f i))) F0).picClass =
            (P.datum.baseChange (Localization.Away (f i))).cechPicClass) ∧
        ∀ i : Fin m,
          (Scheme.Modules.Hom.app P.evaluation
            ((relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) ⁻¹ᵁ
              (⊤ : (Spec (.of P.cover.Carrier)).Opens))).hom
            (P.evaluationLiftOfH0 (y i)) = P.pushforwardSectionOfH0 (y i) := by
  classical
  obtain ⟨m, f, hspan, hgood⟩ :=
    P.exists_fin_rankOne_away_divisor_with_abel_evaluation
  choose y hy habel hclass heval using hgood
  let F : ∀ i : Fin m, DivFamZarAff C (Localization.Away (f i)) (genus C) :=
    fun i => P.baseOpenRankOneDivisor (f i) (y i) (hy i)
  have hcompat : ∀ i j : Fin m,
      DivFamZarAff.mapAlgHom (DivFamZar.awayMulLeft (k := k) f i j) (F i) =
        DivFamZarAff.mapAlgHom (DivFamZar.awayMulRight (k := k) f i j) (F j) := by
    intro i j
    exact P.baseOpenRankOneDivisor_awayMul_compat
      (f i) (f j) (y i) (y j) (hy i) (hy j)
  obtain ⟨F0, hF0⟩ :=
    DivFamZarAff.exists_glue_of_awaySpan f hspan F hcompat
  have habel0 : abelDivAffPlus C P.cover.Carrier F0 =
      PicEtAff.mapAlg C
        ((Algebra.ofId A P.cover.Carrier).restrictScalars k)
        (picEtAffineEquiv C A lam.1) := by
    refine PicEtAff.eq_of_away_eq C
      (fun l : ULift.{u} (Fin m) => f l.down)
      (fun l : ULift.{u} (Fin m) => Localization.Away (f l.down)) ?_ (fun l => ?_)
    · rw [show (Set.range fun l : ULift.{u} (Fin m) => f l.down) = Set.range f from
        ULift.down_surjective.range_comp f]
      exact hspan
    · let i := l.down
      change PicEtAff.mapAlg C
          (IsScalarTower.toAlgHom k P.cover.Carrier
            (Localization.Away (f i)))
          (abelDivAffPlus C P.cover.Carrier F0) = _
      calc
        PicEtAff.mapAlg C
            (IsScalarTower.toAlgHom k P.cover.Carrier
              (Localization.Away (f i)))
            (abelDivAffPlus C P.cover.Carrier F0) =
            abelDivAffPlus C (Localization.Away (f i))
              (DivFamZarAff.mapAlgHom
                (IsScalarTower.toAlgHom k P.cover.Carrier
                  (Localization.Away (f i))) F0) :=
          abelDivAffPlus_mapAlgHom
            (IsScalarTower.toAlgHom k P.cover.Carrier
              (Localization.Away (f i))) F0
        _ = abelDivAffPlus C (Localization.Away (f i)) (F i) :=
          congrArg (abelDivAffPlus C (Localization.Away (f i))) (hF0 i)
        _ = PicEtAff.mapAlg C
            (IsScalarTower.toAlgHom k P.cover.Carrier
              (Localization.Away (f i)))
            (PicEtAff.mapAlg C
              ((Algebra.ofId A P.cover.Carrier).restrictScalars k)
              (picEtAffineEquiv C A lam.1)) := by
          have hphi :
              (Algebra.ofId P.cover.Carrier (Localization.Away (f i))).restrictScalars k =
                IsScalarTower.toAlgHom k P.cover.Carrier (Localization.Away (f i)) :=
            AlgHom.ext (fun _ => rfl)
          rw [← hphi]
          simpa only [F] using habel i
  have htarget :
      PicEtAff.mapAlg C
          ((Algebra.ofId A P.cover.Carrier).restrictScalars k)
          (picEtAffineEquiv C A lam.1) =
        PicEtAff.unit C P.cover.Carrier
          (P.representative : relPic C (overSpec k P.cover.Carrier)) := by
    rw [← P.represents, PicEtAff.mapAlg_mk_eq_unit_self]
  have hrel : relPicMk C (overSpec k P.cover.Carrier) F0.picClass =
      (P.representative : relPic C (overSpec k P.cover.Carrier)) := by
    apply PicEtAff.unit_injective C P.cover.Carrier
    rw [← htarget]
    exact habel0
  refine ⟨m, f, y, hy, F0, hspan, ?_, habel0, hrel, ?_, heval⟩
  · intro i
    simpa only [F] using hF0 i
  · intro i
    rw [hF0 i]
    exact hclass i

end PicRankOneLocalPresentation

end AlgebraicGeometry
