/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAwaySpanGlue
import AlgebraicJacobian.Picard.DivisorFamilyAffGlueZar
import AlgebraicJacobian.Picard.DivisorFamilyAffFace

/-!
# Canonical away-span gluing for widened divisor classes

The canonical comparison maps of `DivRepAwaySpanGlue` live entirely on the base, so they
apply unchanged to `DivFamZarAff`.  This file exposes the widened existence, separation,
and unique-gluing statements at the canonical away localizations used by the divisor atlas.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {S : Type u} [CommRing S] [Algebra k S] {n : Nat}

namespace DivFamZarAff

set_option maxHeartbeats 1600000 in
-- The canonical overlap carrier elaborates both localization towers simultaneously.
/-- Widened locally certified classes on a canonical finite away cover glue. -/
theorem exists_glue_of_awaySpan {m : Nat} (f : Fin m -> S)
    (hspan : Ideal.span (Set.range f) = ⊤)
    (F : forall p : Fin m, DivFamZarAff C (Localization.Away (f p)) n)
    (hcompat : forall p q : Fin m,
      mapAlgHom (DivFamZar.awayMulLeft (k := k) f p q) (F p) =
        mapAlgHom (DivFamZar.awayMulRight (k := k) f p q) (F q)) :
    ∃ F0 : DivFamZarAff C S n, forall p : Fin m,
      mapAlgHom (IsScalarTower.toAlgHom k S (Localization.Away (f p))) F0 = F p := by
  classical
  letI algL : forall p q : Fin m, Algebra (Localization.Away (f p))
      (Localization.Away (f p * f q)) := fun p q =>
    (DivFamZar.awayMulLeft (k := k) f p q).toRingHom.toAlgebra
  letI algR : forall p q : Fin m, Algebra (Localization.Away (f q))
      (Localization.Away (f p * f q)) := fun p q =>
    (DivFamZar.awayMulRight (k := k) f p q).toRingHom.toAlgebra
  haveI towSL : forall p q : Fin m, IsScalarTower S (Localization.Away (f p))
      (Localization.Away (f p * f q)) := fun p q =>
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact (DivFamZar.awayMulOfDvd_algebraMap
        (k := k) (f p * f q) (f p) (f q) rfl x).symm)
  haveI towSR : forall p q : Fin m, IsScalarTower S (Localization.Away (f q))
      (Localization.Away (f p * f q)) := fun p q =>
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact (DivFamZar.awayMulOfDvd_algebraMap
        (k := k) (f p * f q) (f q) (f p) (mul_comm _ _) x).symm)
  haveI towkL : forall p q : Fin m, IsScalarTower k (Localization.Away (f p))
      (Localization.Away (f p * f q)) := fun p q =>
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact ((DivFamZar.awayMulLeft (k := k) f p q).commutes x).symm)
  haveI towkR : forall p q : Fin m, IsScalarTower k (Localization.Away (f q))
      (Localization.Away (f p * f q)) := fun p q =>
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact ((DivFamZar.awayMulRight (k := k) f p q).commutes x).symm)
  have hkey : forall l l' : ULift.{u} (Fin m),
      mapAlg (Localization.Away (f l.down * f l'.down)) n (F l.down) =
        mapAlg (Localization.Away (f l.down * f l'.down)) n (F l'.down) := by
    intro l l'
    rw [← mapAlgHom_eq_mapAlg (DivFamZar.awayMulLeft (k := k) f l.down l'.down)
        (fun _ => rfl),
      ← mapAlgHom_eq_mapAlg (DivFamZar.awayMulRight (k := k) f l.down l'.down)
        (fun _ => rfl)]
    exact hcompat l.down l'.down
  obtain ⟨F0, hF0⟩ := DivFamZarAff.exists_glue_of_away_compat
    (fun l : ULift.{u} (Fin m) => f l.down)
    (fun l : ULift.{u} (Fin m) => Localization.Away (f l.down))
    (fun l l' : ULift.{u} (Fin m) => Localization.Away (f l.down * f l'.down))
    (by
      rw [show (Set.range fun l : ULift.{u} (Fin m) => f l.down) = Set.range f from
        ULift.down_surjective.range_comp f]
      exact hspan)
    (fun l => F l.down) hkey
  refine ⟨F0, fun p => ?_⟩
  rw [mapAlgHom_eq_mapAlg
    (IsScalarTower.toAlgHom k S (Localization.Away (f p))) (fun _ => rfl)]
  exact hF0 (ULift.up p)

/-- Widened classes are separated by a finite spanning family of away localizations. -/
theorem eq_of_awaySpan_eq {iota : Type} [Finite iota] (f : iota -> S)
    (hspan : Ideal.span (Set.range f) = ⊤) {F G : DivFamZarAff C S n}
    (h : forall p : iota,
      mapAlgHom (IsScalarTower.toAlgHom k S (Localization.Away (f p))) F =
        mapAlgHom (IsScalarTower.toAlgHom k S (Localization.Away (f p))) G) :
    F = G := by
  refine DivFamZarAff.eq_of_away_eq n (fun l : ULift.{u} iota => f l.down)
    (fun l : ULift.{u} iota => Localization.Away (f l.down))
    (by
      rw [show (Set.range fun l : ULift.{u} iota => f l.down) = Set.range f from
        ULift.down_surjective.range_comp f]
      exact hspan)
    (fun l => ?_)
  rw [← mapAlgHom_eq_mapAlg
      (IsScalarTower.toAlgHom k S (Localization.Away (f l.down))) (fun _ => rfl) F,
    ← mapAlgHom_eq_mapAlg
      (IsScalarTower.toAlgHom k S (Localization.Away (f l.down))) (fun _ => rfl) G]
  exact h l.down

/-- The widened canonical away-span glue is unique. -/
theorem existsUnique_glue_of_awaySpan {m : Nat} (f : Fin m -> S)
    (hspan : Ideal.span (Set.range f) = ⊤)
    (F : forall p : Fin m, DivFamZarAff C (Localization.Away (f p)) n)
    (hcompat : forall p q : Fin m,
      mapAlgHom (DivFamZar.awayMulLeft (k := k) f p q) (F p) =
        mapAlgHom (DivFamZar.awayMulRight (k := k) f p q) (F q)) :
    ∃! F0 : DivFamZarAff C S n, forall p : Fin m,
      mapAlgHom (IsScalarTower.toAlgHom k S (Localization.Away (f p))) F0 = F p := by
  obtain ⟨F0, hF0⟩ := exists_glue_of_awaySpan f hspan F hcompat
  exact ⟨F0, hF0, fun F1 hF1 =>
    eq_of_awaySpan_eq f hspan (fun p => (hF1 p).trans (hF0 p).symm)⟩

end DivFamZarAff

end AlgebraicGeometry
