/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.AffineCech
import AlgebraicJacobian.Picard.DivisorClass
import AlgebraicJacobian.Picard.EffectivityTrivialization

/-!
# Principalizing local equations on a Picard-trivial open

If the Picard class of a Cartier local-equation system is trivial on an open `V`,
its transition cocycle has a trivializing unit cochain on the cover trimmed by `V`.
Multiplying each local equation by that cochain gives compatible ordinary sections,
which glue to one equation on `V`.

This removes the need for an affine support neighbourhood to lie in one member of
the original local-equation cover.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry
namespace Scheme.LocalEquations

variable {X : Scheme.{u}} (d : X.LocalEquations)

/-- On an open where `d.picClass` is trivial, the equations of `d` rescale and glue
to one section.  The comparison units are stated on the original cover members
trimmed by the open. -/
theorem exists_eqn_of_cechPicMap_ι_eq_one {V : X.Opens}
    (hV : Scheme.CechPic.map V.ι d.picClass = 1) :
    ∃ f : Γ(X, V), ∀ y : X,
      X.resHom (inf_le_right : d.cover.opens y ⊓ V ≤ V) f =
        ((Scheme.exists_trimmed_trivializing_of_cechPicMap_ι_eq_one
          d.cover d.unitsCocycle V hV).choose y : Γ(X, d.cover.opens y ⊓ V))
          * X.resHom inf_le_left (d.eqn y) := by
  classical
  let t : ∀ y : X, Γ(X, d.cover.opens y ⊓ V)ˣ :=
    (Scheme.exists_trimmed_trivializing_of_cechPicMap_ι_eq_one
      d.cover d.unitsCocycle V hV).choose
  have ht : ∀ y y' : X,
      X.unitsRestrict (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          (d.cover.opens y ⊓ d.cover.opens y') ⊓ V ≤ d.cover.opens y ⊓ V) (t y)
        * X.unitsRestrict (inf_le_left :
            (d.cover.opens y ⊓ d.cover.opens y') ⊓ V ≤
              d.cover.opens y ⊓ d.cover.opens y')
            (Scheme.unitsEvInf d.unitsCocycle y y')
      = X.unitsRestrict (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
          (t y') :=
    (Scheme.exists_trimmed_trivializing_of_cechPicMap_ι_eq_one
      d.cover d.unitsCocycle V hV).choose_spec
  let W : X → X.Opens := fun y => d.cover.opens y ⊓ V
  let s : ∀ y : X, Γ(X, W y) := fun y =>
    (t y : Γ(X, d.cover.opens y ⊓ V)) * X.resHom inf_le_left (d.eqn y)
  have hle : ∀ y, W y ≤ V := fun _ => inf_le_right
  have hcover : V ≤ ⨆ y, W y := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, ⟨d.cover.mem_opens x, hx⟩⟩
  have hs : TopCat.Presheaf.IsCompatible X.sheaf.1 W s := by
    intro y y'
    have hOQ : W y ⊓ W y' ≤
        (d.cover.opens y ⊓ d.cover.opens y') ⊓ V :=
      le_inf
        (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
        (inf_le_left.trans inf_le_right)
    have htr0 := congrArg Units.val (ht y y')
    rw [Units.val_mul] at htr0
    simp only [Scheme.coe_unitsRestrict,
      Scheme.LocalEquations.unitsCocycle_evInf] at htr0
    change X.resHom
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
          (t y : Γ(X, d.cover.opens y ⊓ V))
        * X.resHom inf_le_left
          (d.ratioUnit y y' : Γ(X, d.cover.opens y ⊓ d.cover.opens y')) =
      X.resHom (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (t y' : Γ(X, d.cover.opens y' ⊓ V)) at htr0
    have htr := congrArg (X.resHom hOQ) htr0
    rw [map_mul] at htr
    simp only [Scheme.resHom_resHom] at htr
    have hOU : W y ⊓ W y' ≤ d.cover.opens y ⊓ d.cover.opens y' :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    have heq0 := d.eqn_restrict_eq y y'
    change X.resHom inf_le_left (d.eqn y) =
      (d.ratioUnit y y' : Γ(X, d.cover.opens y ⊓ d.cover.opens y'))
        * X.resHom inf_le_right (d.eqn y') at heq0
    have heq := congrArg (X.resHom hOU) heq0
    rw [map_mul] at heq
    simp only [Scheme.resHom_resHom] at heq
    change X.resHom inf_le_left (s y) = X.resHom inf_le_right (s y')
    simp only [s, map_mul, Scheme.resHom_resHom]
    rw [heq]
    rw [← mul_assoc, htr]
  obtain ⟨f, hf, -⟩ :=
    X.sheaf.existsUnique_gluing' W V (fun y => homOfLE (hle y)) hcover s hs
  refine ⟨f, fun y => ?_⟩
  change (X.presheaf.map (homOfLE (inf_le_right : d.cover.opens y ⊓ V ≤ V)).op).hom f =
    (t y : Γ(X, d.cover.opens y ⊓ V)) * X.resHom inf_le_left (d.eqn y)
  exact hf y

/-- Consumer-facing principalization: the global equation on `V` agrees with every
original equation up to a unit on `V ⊓ d.cover.opens y`.  This is precisely the
point-free comparison field required by a widened `AffAdaptation`. -/
theorem exists_eqn_unit_mul_of_cechPicMap_ι_eq_one {V : X.Opens}
    (hV : Scheme.CechPic.map V.ι d.picClass = 1) :
    ∃ f : Γ(X, V), ∀ y : X,
      ∃ u : Γ(X, V ⊓ d.cover.opens y)ˣ,
        X.resHom inf_le_left f =
          (u : Γ(X, V ⊓ d.cover.opens y)) * X.resHom inf_le_right (d.eqn y) := by
  classical
  obtain ⟨f, hf⟩ := d.exists_eqn_of_cechPicMap_ι_eq_one hV
  let t : ∀ y : X, Γ(X, d.cover.opens y ⊓ V)ˣ :=
    (Scheme.exists_trimmed_trivializing_of_cechPicMap_ι_eq_one
      d.cover d.unitsCocycle V hV).choose
  refine ⟨f, fun y => ?_⟩
  have hswap : V ⊓ d.cover.opens y ≤ d.cover.opens y ⊓ V :=
    le_of_eq (inf_comm V (d.cover.opens y))
  refine ⟨X.unitsRestrict hswap (t y), ?_⟩
  have h := congrArg (X.resHom hswap) (hf y)
  rw [map_mul] at h
  change X.resHom inf_le_left f =
    X.resHom hswap (t y : Γ(X, d.cover.opens y ⊓ V))
      * X.resHom inf_le_right (d.eqn y)
  simpa only [t, Scheme.resHom_resHom] using h

end Scheme.LocalEquations
end AlgebraicGeometry
