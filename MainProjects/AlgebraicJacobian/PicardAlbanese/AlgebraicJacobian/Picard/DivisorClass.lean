/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic

/-!
# Local equations for effective Cartier divisors and their Čech Picard class

For a scheme `X`, an *effective Cartier divisor* is cut out, locally, by a single
regular equation. This file packages this data adapted to the pointed covers of the
Čech Picard group (`AlgebraicJacobian.Picard.Pic`) and turns it into a Picard class.

## Sign / normalization convention

A local-equation system `(fᵢ)` for an effective divisor `D` — one regular section `fᵢ`
on each member `𝒰 i` of a pointed cover, agreeing up to a unit on overlaps — is the
data of a trivialization of the invertible sheaf `𝒪(D)`: on `𝒰 i` the sheaf `𝒪(D)` is
trivialized by multiplication by `fᵢ`. The resulting transition units are

`g i j = fᵢ / fⱼ ∈ Γ(X, 𝒰 i ⊓ 𝒰 j)ˣ`,

i.e. the unique unit with `fᵢ|∩ = g i j · fⱼ|∩`. The class of the corresponding Čech
1-cocycle is `𝒪(D)`; this is `Scheme.LocalEquations.picClass`.

## Main declarations

* `AlgebraicGeometry.Scheme.LocalEquations`: local-equation data for an effective
  Cartier divisor adapted to a pointed cover — a regular section on each member, with
  the overlap ratios being units.
* `AlgebraicGeometry.Scheme.LocalEquations.eqn_restrict_mem_nonZeroDivisors`: the
  section-level regularity consequence — every restriction of an equation to a sub-open
  is a nonzerodivisor.
* `AlgebraicGeometry.Scheme.LocalEquations.ratioUnit`, `ratioUnit_unique`,
  `ratioUnit_trans`: the transition units `g i j = fᵢ / fⱼ`, their uniqueness (from
  regularity), and the cocycle identity on triple overlaps.
* `AlgebraicGeometry.Scheme.LocalEquations.unitsCocycle`,
  `AlgebraicGeometry.Scheme.LocalEquations.picClass`: the Čech 1-cocycle `g i j` and its
  Picard class `𝒪(D)`.
* `AlgebraicGeometry.Scheme.LocalEquations.restrict` with `picClass_restrict`: refining
  the cover does not change the class.
* `AlgebraicGeometry.Scheme.LocalEquations.mul` with `picClass_mul`: the pointwise product
  of local equations realizes the product of Picard classes `𝒪(D) · 𝒪(D')`.
* `AlgebraicGeometry.Scheme.LocalEquations.rescale` with `picClass_rescale`: multiplying
  the equations by units does not change the class — `𝒪(D)` depends only on the divisor.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite CategoryTheory.PresheafOfGroups

namespace CategoryTheory.PresheafOfGroups

/-- Over a poset with binary infima, two 1-cocycles are equal as soon as their values on
the binary infima agree. -/
private lemma OneCocycle.ext_evInf {P : Type u} [SemilatticeInf P] {I : Type u}
    {G : Pᵒᵖ ⥤ GrpCat.{u}} {U : I → P} {γ δ : OneCocycle G U}
    (h : ∀ i j, γ.evInf i j = δ.evInf i j) : γ = δ := by
  apply OneCocycle.ext
  ext i j T a b
  rw [OneCochain.ev_eq_evInf, OneCochain.ev_eq_evInf]
  exact congrArg _ (h i j)

end CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

namespace Scheme

variable {X Y : Scheme.{u}}

/-! ## Ring-level restriction helpers -/

/-- Restriction of a section along `W ≤ V ≤ U` composes to restriction along `W ≤ U`. -/
private lemma sectionRestrict_comp {W V U : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom s)
      = (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- The underlying section of a restricted unit is the ring-level restriction of its
underlying section. -/
private lemma coe_unitsRestrict {W U : X.Opens} (h : W ≤ U) (u : Γ(X, U)ˣ) :
    (X.unitsRestrict h u : Γ(X, W)) = (X.presheaf.map (homOfLE h).op).hom (u : Γ(X, U)) := by
  simp only [Scheme.unitsRestrict, Units.coe_map, MonoidHom.coe_coe]

/-- A unit Čech cocycle on a pointed cover is determined by its pair values
`Scheme.unitsEvInf`. -/
lemma unitsCocycle_ext {𝒰 : X.PointedCover} {γ δ : X.unitsCocycle 𝒰}
    (h : ∀ i j, unitsEvInf γ i j = unitsEvInf δ i j) : γ = δ :=
  OneCocycle.ext_evInf h

/-- Two unit Čech cocycles on a pointed cover are cohomologous if a `0`-cochain of unit
sections conjugates their pair values into each other. -/
lemma unitsCocycle_isCohomologous {𝒰 : X.PointedCover} {γ δ : X.unitsCocycle 𝒰}
    (α : ∀ i, Γ(X, 𝒰.opens i)ˣ)
    (h : ∀ i j, X.unitsRestrict inf_le_left (α i) * unitsEvInf γ i j
      = unitsEvInf δ i j * X.unitsRestrict inf_le_right (α j)) :
    γ.IsCohomologous δ :=
  (OneCocycle.isCohomologous_iff_evInf γ δ).mpr ⟨α, h⟩

/-! ## Local equations -/

/-- Local equations for an effective Cartier divisor on `X`, adapted to a pointed cover:
a section `eqn x` on each member `cover.opens x`, whose germ at every point of that member
is a nonzerodivisor (`regular`) and whose overlap ratios `eqn x / eqn y` are units
(`ratio_isUnit`). The class of the associated Čech cocycle of transition units is the
divisor class `𝒪(D)`, see `LocalEquations.picClass`. -/
structure LocalEquations (X : Scheme.{u}) : Type u where
  /-- The pointed cover on whose members the local equations live. -/
  cover : X.PointedCover
  /-- The local equation on the member `cover.opens x`. -/
  eqn : ∀ x, Γ(X, cover.opens x)
  /-- Each local equation is regular: its germ at every point of its member is a
  nonzerodivisor in the stalk. This is the primitive form of regularity; it implies the
  regularity of every restriction (`eqn_restrict_mem_nonZeroDivisors`). -/
  regular : ∀ (x y : X) (hy : y ∈ cover.opens x),
    (X.presheaf.germ (cover.opens x) y hy).hom (eqn x) ∈ nonZeroDivisors (X.presheaf.stalk y)
  /-- On the overlap `cover.opens x ⊓ cover.opens y` the two equations differ by a unit
  factor `eqn x = u · eqn y`, so that `𝒪(D)` is invertible. -/
  ratio_isUnit : ∀ x y, ∃ u : Γ(X, cover.opens x ⊓ cover.opens y)ˣ,
    (X.presheaf.map (homOfLE inf_le_left).op).hom (eqn x)
      = (u : Γ(X, cover.opens x ⊓ cover.opens y))
        * (X.presheaf.map (homOfLE inf_le_right).op).hom (eqn y)

namespace LocalEquations

variable (d : X.LocalEquations)

/-- Section-level regularity: the restriction of `eqn x` to any sub-open `W ≤ cover.opens x`
is a nonzerodivisor in `Γ(X, W)`. Sections of a sheaf inject into the product of their
germs, so nonzerodivisibility of the germs (the field `regular`) propagates to every
restriction. -/
lemma eqn_restrict_mem_nonZeroDivisors (x : X) {W : X.Opens} (hW : W ≤ d.cover.opens x) :
    (X.presheaf.map (homOfLE hW).op).hom (d.eqn x) ∈ nonZeroDivisors Γ(X, W) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro t ht
  apply TopCat.Presheaf.section_ext X.sheaf W t 0
  intro y hy
  rw [map_zero]
  have key : (X.presheaf.germ W y hy).hom t
      * (X.presheaf.germ W y hy).hom ((X.presheaf.map (homOfLE hW).op).hom (d.eqn x)) = 0 := by
    rw [← map_mul, ht, map_zero]
  rw [TopCat.Presheaf.germ_res_apply] at key
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff (d.regular x y (hW hy))).mp
    (by rw [mul_comm] at key; exact key)

/-! ## The transition units -/

/-- The transition unit `g x y = eqn x / eqn y ∈ Γ(X, 𝒰x ⊓ 𝒰y)ˣ`: the unique unit with
`eqn x|∩ = g x y · eqn y|∩`. -/
noncomputable def ratioUnit (x y : X) : Γ(X, d.cover.opens x ⊓ d.cover.opens y)ˣ :=
  (d.ratio_isUnit x y).choose

/-- The defining property of the transition unit `g x y`: on the overlap,
`eqn x = g x y · eqn y`. -/
lemma eqn_restrict_eq (x y : X) :
    (X.presheaf.map (homOfLE inf_le_left).op).hom (d.eqn x)
      = (d.ratioUnit x y : Γ(X, d.cover.opens x ⊓ d.cover.opens y))
        * (X.presheaf.map (homOfLE inf_le_right).op).hom (d.eqn y) :=
  (d.ratio_isUnit x y).choose_spec

/-- Uniqueness of the transition unit: any unit `u` with `eqn x = u · eqn y` on the
overlap equals `g x y`. Regularity of `eqn y` (its restriction is a nonzerodivisor) makes
the ratio unique. -/
lemma ratioUnit_unique (x y : X) (u : Γ(X, d.cover.opens x ⊓ d.cover.opens y)ˣ)
    (hu : (X.presheaf.map (homOfLE inf_le_left).op).hom (d.eqn x)
      = (u : Γ(X, d.cover.opens x ⊓ d.cover.opens y))
        * (X.presheaf.map (homOfLE inf_le_right).op).hom (d.eqn y)) :
    u = d.ratioUnit x y := by
  refine Units.ext ?_
  refine (mul_cancel_right_mem_nonZeroDivisors
    (d.eqn_restrict_mem_nonZeroDivisors y (inf_le_right : d.cover.opens x ⊓ d.cover.opens y
      ≤ d.cover.opens y))).mp ?_
  rw [← hu, d.eqn_restrict_eq x y]

/-- The cocycle identity for the transition units, on the triple overlap
`𝒰x ⊓ 𝒰y ⊓ 𝒰z`: `g x y · g y z = g x z`. Proved by multiplying through by the regular
`eqn z` and cancelling. Mirrors `Scheme.unitsEvInf_trans`. -/
lemma ratioUnit_trans (x y z : X) :
    X.unitsRestrict (inf_le_left :
          d.cover.opens x ⊓ d.cover.opens y ⊓ d.cover.opens z
            ≤ d.cover.opens x ⊓ d.cover.opens y)
        (d.ratioUnit x y)
      * X.unitsRestrict (inf_le_inf_right _ inf_le_right :
          d.cover.opens x ⊓ d.cover.opens y ⊓ d.cover.opens z
            ≤ d.cover.opens y ⊓ d.cover.opens z)
          (d.ratioUnit y z)
      = X.unitsRestrict (inf_le_inf_right _ inf_le_left :
          d.cover.opens x ⊓ d.cover.opens y ⊓ d.cover.opens z
            ≤ d.cover.opens x ⊓ d.cover.opens z)
          (d.ratioUnit x z) := by
  refine Units.ext ?_
  -- work at the level of underlying sections on the triple overlap
  rw [Units.val_mul, coe_unitsRestrict, coe_unitsRestrict, coe_unitsRestrict]
  -- cancel the regular restriction of `eqn z`
  refine (mul_cancel_right_mem_nonZeroDivisors
    (d.eqn_restrict_mem_nonZeroDivisors z (inf_le_right :
      d.cover.opens x ⊓ d.cover.opens y ⊓ d.cover.opens z ≤ d.cover.opens z))).mp ?_
  -- `g x z · eqn z = eqn x` on the triple overlap
  have hA := congrArg (X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left :
      d.cover.opens x ⊓ d.cover.opens y ⊓ d.cover.opens z
        ≤ d.cover.opens x ⊓ d.cover.opens z)).op).hom (d.eqn_restrict_eq x z)
  rw [map_mul, sectionRestrict_comp, sectionRestrict_comp] at hA
  -- `g y z · eqn z = eqn y` on the triple overlap
  have hB := congrArg (X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right :
      d.cover.opens x ⊓ d.cover.opens y ⊓ d.cover.opens z
        ≤ d.cover.opens y ⊓ d.cover.opens z)).op).hom (d.eqn_restrict_eq y z)
  rw [map_mul, sectionRestrict_comp, sectionRestrict_comp] at hB
  -- `g x y · eqn y = eqn x` on the triple overlap
  have hC := congrArg (X.presheaf.map (homOfLE (inf_le_left :
      d.cover.opens x ⊓ d.cover.opens y ⊓ d.cover.opens z
        ≤ d.cover.opens x ⊓ d.cover.opens y)).op).hom (d.eqn_restrict_eq x y)
  rw [map_mul, sectionRestrict_comp, sectionRestrict_comp] at hC
  rw [mul_assoc, ← hB, ← hC]
  exact hA

/-! ## The cocycle and its Picard class -/

/-- The Čech 1-cocycle of transition units `g x y = eqn x / eqn y` of a local-equation
system. -/
noncomputable def unitsCocycle : X.unitsCocycle d.cover :=
  OneCocycle.ofPairs (G := X.unitsPresheaf ⋙ forget₂ CommGrpCat GrpCat) (U := d.cover.opens)
    (fun x y ↦ d.ratioUnit x y) (fun x y z ↦ d.ratioUnit_trans x y z)

@[simp]
lemma unitsCocycle_evInf (x y : X) :
    unitsEvInf d.unitsCocycle x y = d.ratioUnit x y :=
  OneCocycle.ofPairs_evInf (G := X.unitsPresheaf ⋙ forget₂ CommGrpCat GrpCat)
    (U := d.cover.opens) (fun x y ↦ d.ratioUnit x y)
    (fun x y z ↦ d.ratioUnit_trans x y z) x y

/-- The Picard class `𝒪(D)` of a local-equation system for the effective divisor `D`:
the Čech class of the cocycle of transition units. -/
noncomputable def picClass : X.CechPic :=
  CechPic.mk d.cover d.unitsCocycle.class

/-! ## Refinement of the cover -/

/-- The defining ratio equation of the restricted system, phrased on the underlying
restricted sections. -/
private lemma restrict_ratio_eq (𝒱 : X.PointedCover) (h : 𝒱 ≤ d.cover) (x y : X) :
    (X.presheaf.map (homOfLE (inf_le_left : 𝒱.opens x ⊓ 𝒱.opens y ≤ 𝒱.opens x)).op).hom
        ((X.presheaf.map (homOfLE (h x)).op).hom (d.eqn x))
      = (X.unitsRestrict (inf_le_inf (h x) (h y)) (d.ratioUnit x y) : Γ(X, 𝒱.opens x ⊓ 𝒱.opens y))
        * (X.presheaf.map (homOfLE (inf_le_right : 𝒱.opens x ⊓ 𝒱.opens y ≤ 𝒱.opens y)).op).hom
            ((X.presheaf.map (homOfLE (h y)).op).hom (d.eqn y)) := by
  have E := congrArg (X.presheaf.map (homOfLE (inf_le_inf (h x) (h y))).op).hom
    (d.eqn_restrict_eq x y)
  rw [map_mul, sectionRestrict_comp, sectionRestrict_comp] at E
  rw [coe_unitsRestrict, sectionRestrict_comp, sectionRestrict_comp]
  exact E

/-- Restriction of a local-equation system along a refinement `𝒱 ≤ d.cover`: restrict each
equation to the smaller member. Regularity restricts because germs factor through
restriction; the transition units restrict likewise. -/
def restrict (𝒱 : X.PointedCover) (h : 𝒱 ≤ d.cover) : X.LocalEquations where
  cover := 𝒱
  eqn x := (X.presheaf.map (homOfLE (h x)).op).hom (d.eqn x)
  regular x y hy := by
    rw [TopCat.Presheaf.germ_res_apply]
    exact d.regular x y (h x hy)
  ratio_isUnit x y :=
    ⟨X.unitsRestrict (inf_le_inf (h x) (h y)) (d.ratioUnit x y), d.restrict_ratio_eq 𝒱 h x y⟩

/-- The transition units of the restricted system are the restrictions of the original
transition units. -/
lemma restrict_ratioUnit (𝒱 : X.PointedCover) (h : 𝒱 ≤ d.cover) (x y : X) :
    (d.restrict 𝒱 h).ratioUnit x y = X.unitsRestrict (inf_le_inf (h x) (h y)) (d.ratioUnit x y) :=
  ((d.restrict 𝒱 h).ratioUnit_unique x y _ (d.restrict_ratio_eq 𝒱 h x y)).symm

/-- The refined local-equation system has the same Picard class: its cocycle is the
restriction of the original cocycle, and restriction stabilizes the Čech class. -/
@[simp]
lemma picClass_restrict (𝒱 : X.PointedCover) (h : 𝒱 ≤ d.cover) :
    (d.restrict 𝒱 h).picClass = d.picClass := by
  have hco : (d.restrict 𝒱 h).unitsCocycle
      = d.unitsCocycle.res (fun x ↦ homOfLE (h x)) := by
    refine unitsCocycle_ext fun x y ↦ ?_
    calc unitsEvInf (d.restrict 𝒱 h).unitsCocycle x y
        = X.unitsRestrict (inf_le_inf (h x) (h y)) (d.ratioUnit x y) :=
          ((d.restrict 𝒱 h).unitsCocycle_evInf x y).trans (d.restrict_ratioUnit 𝒱 h x y)
      _ = unitsEvInf (d.unitsCocycle.res (fun x ↦ homOfLE (h x))) x y :=
          ((res_unitsEvInf h d.unitsCocycle x y).trans
            (congrArg (X.unitsRestrict (inf_le_inf (h x) (h y))) (d.unitsCocycle_evInf x y))).symm
  change CechPic.mk 𝒱 (d.restrict 𝒱 h).unitsCocycle.class = d.picClass
  rw [hco]
  exact CechPic.mk_unitsRes h d.unitsCocycle.class

/-! ## Product of local-equation systems (tensor product of divisor classes) -/

/-- The defining ratio equation for the pointwise product of two local-equation systems,
on the common refinement `d.cover ⊓ d'.cover`. -/
private lemma mul_ratio_eq (d d' : X.LocalEquations) (x y : X) :
    (X.presheaf.map (homOfLE (inf_le_left :
        (d.cover.opens x ⊓ d'.cover.opens x) ⊓ (d.cover.opens y ⊓ d'.cover.opens y)
          ≤ d.cover.opens x ⊓ d'.cover.opens x)).op).hom
        ((X.presheaf.map (homOfLE (inf_le_left :
              d.cover.opens x ⊓ d'.cover.opens x ≤ d.cover.opens x)).op).hom (d.eqn x)
          * (X.presheaf.map (homOfLE (inf_le_right :
              d.cover.opens x ⊓ d'.cover.opens x ≤ d'.cover.opens x)).op).hom (d'.eqn x))
      = ((X.unitsRestrict (inf_le_inf inf_le_left inf_le_left) (d.ratioUnit x y)
            * X.unitsRestrict (inf_le_inf inf_le_right inf_le_right) (d'.ratioUnit x y)
          : Γ(X, (d.cover.opens x ⊓ d'.cover.opens x) ⊓ (d.cover.opens y ⊓ d'.cover.opens y))ˣ)
          : Γ(X, (d.cover.opens x ⊓ d'.cover.opens x) ⊓ (d.cover.opens y ⊓ d'.cover.opens y)))
        * (X.presheaf.map (homOfLE (inf_le_right :
            (d.cover.opens x ⊓ d'.cover.opens x) ⊓ (d.cover.opens y ⊓ d'.cover.opens y)
              ≤ d.cover.opens y ⊓ d'.cover.opens y)).op).hom
            ((X.presheaf.map (homOfLE (inf_le_left :
                  d.cover.opens y ⊓ d'.cover.opens y ≤ d.cover.opens y)).op).hom (d.eqn y)
              * (X.presheaf.map (homOfLE (inf_le_right :
                  d.cover.opens y ⊓ d'.cover.opens y ≤ d'.cover.opens y)).op).hom
                  (d'.eqn y)) := by
  have Ed := congrArg (X.presheaf.map (homOfLE (inf_le_inf inf_le_left inf_le_left :
      (d.cover.opens x ⊓ d'.cover.opens x) ⊓ (d.cover.opens y ⊓ d'.cover.opens y)
        ≤ d.cover.opens x ⊓ d.cover.opens y)).op).hom (d.eqn_restrict_eq x y)
  rw [map_mul, sectionRestrict_comp, sectionRestrict_comp] at Ed
  have Ed' := congrArg (X.presheaf.map (homOfLE (inf_le_inf inf_le_right inf_le_right :
      (d.cover.opens x ⊓ d'.cover.opens x) ⊓ (d.cover.opens y ⊓ d'.cover.opens y)
        ≤ d'.cover.opens x ⊓ d'.cover.opens y)).op).hom (d'.eqn_restrict_eq x y)
  rw [map_mul, sectionRestrict_comp, sectionRestrict_comp] at Ed'
  rw [Units.val_mul, coe_unitsRestrict, coe_unitsRestrict, map_mul, map_mul,
    sectionRestrict_comp, sectionRestrict_comp, sectionRestrict_comp, sectionRestrict_comp,
    Ed, Ed']
  exact mul_mul_mul_comm _ _ _ _

/-- The pointwise product of two local-equation systems, on the common refinement
`d.cover ⊓ d'.cover`: multiply the equations. It cuts out the sum of the two divisors, and
its Picard class is the product `𝒪(D) · 𝒪(D')`. -/
def mul (d d' : X.LocalEquations) : X.LocalEquations where
  cover := d.cover ⊓ d'.cover
  eqn x := (X.presheaf.map (homOfLE (inf_le_left :
        d.cover.opens x ⊓ d'.cover.opens x ≤ d.cover.opens x)).op).hom (d.eqn x)
      * (X.presheaf.map (homOfLE (inf_le_right :
          d.cover.opens x ⊓ d'.cover.opens x ≤ d'.cover.opens x)).op).hom (d'.eqn x)
  regular x y hy := by
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact mul_mem (d.regular x y hy.1) (d'.regular x y hy.2)
  ratio_isUnit x y :=
    ⟨X.unitsRestrict (inf_le_inf inf_le_left inf_le_left) (d.ratioUnit x y)
        * X.unitsRestrict (inf_le_inf inf_le_right inf_le_right) (d'.ratioUnit x y),
      mul_ratio_eq d d' x y⟩

/-- The transition units of a product system are the products of the (restricted)
transition units. -/
lemma mul_ratioUnit (d d' : X.LocalEquations) (x y : X) :
    (d.mul d').ratioUnit x y
      = X.unitsRestrict (inf_le_inf inf_le_left inf_le_left) (d.ratioUnit x y)
        * X.unitsRestrict (inf_le_inf inf_le_right inf_le_right) (d'.ratioUnit x y) :=
  ((d.mul d').ratioUnit_unique x y _ (mul_ratio_eq d d' x y)).symm

/-- The Picard class of a product of local-equation systems is the product of the Picard
classes: `𝒪(D + D') = 𝒪(D) · 𝒪(D')`. -/
@[simp]
lemma picClass_mul (d d' : X.LocalEquations) :
    (d.mul d').picClass = d.picClass * d'.picClass := by
  have hco : (d.mul d').unitsCocycle
      = d.unitsCocycle.res (fun x ↦ homOfLE inf_le_left)
        * d'.unitsCocycle.res (fun x ↦ homOfLE inf_le_right) := by
    refine unitsCocycle_ext fun x y ↦ ?_
    calc unitsEvInf (d.mul d').unitsCocycle x y
        = X.unitsRestrict (inf_le_inf inf_le_left inf_le_left) (d.ratioUnit x y)
            * X.unitsRestrict (inf_le_inf inf_le_right inf_le_right) (d'.ratioUnit x y) :=
          ((d.mul d').unitsCocycle_evInf x y).trans (mul_ratioUnit d d' x y)
      _ = unitsEvInf (d.unitsCocycle.res (fun x ↦ homOfLE inf_le_left)
            * d'.unitsCocycle.res (fun x ↦ homOfLE inf_le_right)) x y :=
          (congr_arg₂ (· * ·)
            ((res_unitsEvInf inf_le_left d.unitsCocycle x y).trans
              (congrArg (X.unitsRestrict (inf_le_inf inf_le_left inf_le_left))
                (d.unitsCocycle_evInf x y))).symm
            ((res_unitsEvInf inf_le_right d'.unitsCocycle x y).trans
              (congrArg (X.unitsRestrict (inf_le_inf inf_le_right inf_le_right))
                (d'.unitsCocycle_evInf x y))).symm).trans
            (mul_unitsEvInf (d.unitsCocycle.res (fun x ↦ homOfLE inf_le_left))
              (d'.unitsCocycle.res (fun x ↦ homOfLE inf_le_right)) x y).symm
  have hclass : (d.mul d').unitsCocycle.class
      = unitsRes (inf_le_left : d.cover ⊓ d'.cover ≤ d.cover) d.unitsCocycle.class
        * unitsRes (inf_le_right : d.cover ⊓ d'.cover ≤ d'.cover) d'.unitsCocycle.class :=
    (congrArg OneCocycle.class hco).trans rfl
  change CechPic.mk (d.cover ⊓ d'.cover) (d.mul d').unitsCocycle.class
    = d.picClass * d'.picClass
  rw [hclass]
  change _ = CechPic.mk d.cover d.unitsCocycle.class * CechPic.mk d'.cover d'.unitsCocycle.class
  rw [CechPic.mk_mul_mk_inf]

/-! ## Independence under unit rescaling -/

/-- The defining ratio equation for a unitwise rescaling of a local-equation system. -/
private lemma rescale_ratio_eq (d : X.LocalEquations) (v : ∀ x, Γ(X, d.cover.opens x)ˣ)
    (x y : X) :
    (X.presheaf.map (homOfLE (inf_le_left :
        d.cover.opens x ⊓ d.cover.opens y ≤ d.cover.opens x)).op).hom
        ((v x : Γ(X, d.cover.opens x)) * d.eqn x)
      = ((X.unitsRestrict inf_le_left (v x) * d.ratioUnit x y
            * (X.unitsRestrict inf_le_right (v y))⁻¹
          : Γ(X, d.cover.opens x ⊓ d.cover.opens y)ˣ)
          : Γ(X, d.cover.opens x ⊓ d.cover.opens y))
        * (X.presheaf.map (homOfLE (inf_le_right :
            d.cover.opens x ⊓ d.cover.opens y ≤ d.cover.opens y)).op).hom
            ((v y : Γ(X, d.cover.opens y)) * d.eqn y) := by
  have key : (X.unitsRestrict inf_le_left (v x) * d.ratioUnit x y
        * (X.unitsRestrict inf_le_right (v y))⁻¹) * X.unitsRestrict inf_le_right (v y)
      = X.unitsRestrict inf_le_left (v x) * d.ratioUnit x y := inv_mul_cancel_right _ _
  rw [map_mul, map_mul,
    ← coe_unitsRestrict inf_le_left (v x), ← coe_unitsRestrict inf_le_right (v y),
    d.eqn_restrict_eq x y, ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul, key]

/-- A unitwise rescaling of a local-equation system: multiply each equation by a unit on
its member. It cuts out the same divisor. -/
def rescale (d : X.LocalEquations) (v : ∀ x, Γ(X, d.cover.opens x)ˣ) : X.LocalEquations where
  cover := d.cover
  eqn x := (v x : Γ(X, d.cover.opens x)) * d.eqn x
  regular x y hy := by
    rw [map_mul]
    exact mul_mem
      (((v x).isUnit.map (X.presheaf.germ (d.cover.opens x) y hy).hom).mem_nonZeroDivisors)
      (d.regular x y hy)
  ratio_isUnit x y :=
    ⟨X.unitsRestrict inf_le_left (v x) * d.ratioUnit x y * (X.unitsRestrict inf_le_right (v y))⁻¹,
      rescale_ratio_eq d v x y⟩

/-- The transition units of a rescaled system, conjugated by the rescaling units. -/
lemma rescale_ratioUnit (d : X.LocalEquations) (v : ∀ x, Γ(X, d.cover.opens x)ˣ) (x y : X) :
    (d.rescale v).ratioUnit x y
      = X.unitsRestrict inf_le_left (v x) * d.ratioUnit x y
        * (X.unitsRestrict inf_le_right (v y))⁻¹ :=
  ((d.rescale v).ratioUnit_unique x y _ (rescale_ratio_eq d v x y)).symm

/-- A commutative-group cancellation used for the rescaling coboundary. -/
private lemma inv_mul_mul_inv_cancel {G : Type u} [CommGroup G] (a r b : G) :
    a⁻¹ * (a * r * b⁻¹) = r * b⁻¹ := by
  rw [mul_assoc, inv_mul_cancel_left]

/-- The coboundary identity witnessing that rescaling does not change the Picard class:
the `0`-cochain `v⁻¹` conjugates the rescaled cocycle into the original. -/
private lemma rescale_coboundary (d : X.LocalEquations) (v : ∀ x, Γ(X, d.cover.opens x)ˣ)
    (x y : X) :
    X.unitsRestrict inf_le_left (v x)⁻¹ * (d.rescale v).ratioUnit x y
      = d.ratioUnit x y * X.unitsRestrict inf_le_right (v y)⁻¹ :=
  (congrArg (X.unitsRestrict inf_le_left (v x)⁻¹ * ·) (rescale_ratioUnit d v x y)).trans
    (inv_mul_mul_inv_cancel (X.unitsRestrict inf_le_left (v x)) (d.ratioUnit x y)
      (X.unitsRestrict inf_le_right (v y)))

/-- Unitwise rescaling does not change the Picard class: `𝒪(D)` depends only on the
divisor, not on the chosen local equations. -/
@[simp]
lemma picClass_rescale (d : X.LocalEquations) (v : ∀ x, Γ(X, d.cover.opens x)ˣ) :
    (d.rescale v).picClass = d.picClass := by
  have hcoh : (d.rescale v).unitsCocycle.IsCohomologous d.unitsCocycle :=
    unitsCocycle_isCohomologous (fun x ↦ (v x)⁻¹) fun x y ↦
      ((congrArg (X.unitsRestrict inf_le_left (v x)⁻¹ * ·)
          ((d.rescale v).unitsCocycle_evInf x y)).trans
        (rescale_coboundary d v x y)).trans
          (congrArg (· * X.unitsRestrict inf_le_right (v y)⁻¹) (d.unitsCocycle_evInf x y).symm)
  change CechPic.mk d.cover (d.rescale v).unitsCocycle.class
    = CechPic.mk d.cover d.unitsCocycle.class
  exact congrArg (CechPic.mk d.cover) hcoh.class_eq

end LocalEquations

end Scheme

end AlgebraicGeometry
