/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PresentationDivisor

/-!
# The class law: presentations with equal divisors present equal classes

For the curve bundle `X` (integral, smooth of relative dimension one and quasi-compact
over a field `K`), this file proves the heart of the meromorphic bridge (deg-D2 W3): the
Čech Picard class of a meromorphic presentation depends only on its Weil divisor.

## The ord-matching lemma

The local input is **ord-matching ⇒ unit section**: a rational function `q ∈ K(X)ˣ` with
trivial order at every closed point of an open `V` is the germ at `η` of a *unit section*
over `V` (`exists_germGenericUnits_eq_of_forall_ordZ_eq_one`). Both `q` and `q⁻¹` have
poles bounded by the zero divisor, so both are germs of sections of `𝒪_X` over `V` (the
landed `Scheme.exists_section_germ_eq` from the `𝒪(0) ≅ 𝒪_X` identification); the two
sections multiply to `1` because their germs at `η` do and `X` is integral. The
two-element form (`exists_germGenericUnits_eq_mul_inv_of_forall_ordZ_eq`) applies this to
a ratio `g / h` with matching orders.

## The class law

Two presentations `P`, `Q` with equal divisors have, on each piece of the common
refinement `P.cover ⊓ Q.cover`, elements with matching orders (piece-independence pushes
both to the piece indexed by each closed point, where the divisors agree). Ord-matching
produces unit sections `u x` with `germ_η (u x) = P.elem x / Q.elem x`; the `0`-cochain
`(u x)⁻¹` witnesses that the two restricted cocycles are cohomologous — the coboundary
identity is checked inside `K(X)ˣ` through the injective embedding
`Scheme.germGenericUnits` — and restriction does not move the Čech class
(`MeromorphicPresentation.picClass_eq_of_presentationDivisor_eq`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

namespace Scheme

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]

/-! ## Ord-matching: rational functions of trivial order are unit sections -/

/-- **Ord-matching, primitive form.** A rational function `q ∈ K(X)ˣ` whose order is
trivial at every closed point of a nonempty open `V` is the germ at `η` of a unit
section over `V`: both `q` and `q⁻¹` lie in `𝒪(0)(V)`, hence are germs of sections, and
the two sections are mutually inverse because their germs at `η` are. -/
theorem exists_germGenericUnits_eq_of_forall_ordZ_eq_one {V : X.Opens}
    (hηV : genericPoint X ∈ V) {q : X.functionFieldˣ}
    (hq : ∀ (x : X) (hx : x ≠ genericPoint X), x ∈ V →
      Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hx q = 1) :
    ∃ u : Γ(X, V)ˣ, germGenericUnits hηV u = q := by
  have hVne : (V : Set X).Nonempty := ⟨genericPoint X, hηV⟩
  have hmem : (q : X.functionField) ∈ divisorSections K 0 V := by
    rw [mem_divisorSections_of_nonempty K hVne]
    intro x hx hxV
    rw [divisorBound_zero]
    exact le_of_eq ((Scheme.ordZ_eq_one_iff _ hx q).mp (hq x hx hxV))
  have hmem' : ((q⁻¹ : X.functionFieldˣ) : X.functionField) ∈ divisorSections K 0 V := by
    rw [mem_divisorSections_of_nonempty K hVne]
    intro x hx hxV
    rw [divisorBound_zero]
    refine le_of_eq ((Scheme.ordZ_eq_one_iff _ hx q⁻¹).mp ?_)
    rw [map_inv, hq x hx hxV, inv_one]
  obtain ⟨s, hs⟩ := exists_section_germ_eq K hηV hmem
  obtain ⟨s', hs'⟩ := exists_section_germ_eq K hηV hmem'
  have hmul : s * s' = 1 := by
    apply germ_injective_of_isIntegral X (genericPoint X) hηV
    rw [map_mul, map_one, hs, hs']
    exact q.mul_inv
  refine ⟨Units.mkOfMulEqOne s s' hmul, Units.ext ?_⟩
  rw [germGenericUnits_val, Units.val_mkOfMulEqOne]
  exact hs

/-- **Ord-matching, two-element form** (the W3 local heart): two rational functions
`g, h ∈ K(X)ˣ` with equal orders at every closed point of a nonempty open `V` differ by
(the germ at `η` of) a unit section over `V`. -/
theorem exists_germGenericUnits_eq_mul_inv_of_forall_ordZ_eq {V : X.Opens}
    (hηV : genericPoint X ∈ V) {g h : X.functionFieldˣ}
    (hgh : ∀ (x : X) (hx : x ≠ genericPoint X), x ∈ V →
      Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hx g
        = Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hx h) :
    ∃ u : Γ(X, V)ˣ, germGenericUnits hηV u = g * h⁻¹ := by
  refine exists_germGenericUnits_eq_of_forall_ordZ_eq_one K hηV fun x hx hxV => ?_
  rw [map_mul, map_inv, hgh x hx hxV, mul_inv_cancel]

namespace MeromorphicPresentation

/-- The germ at `η` of a pair value of a restricted presentation cocycle is the ratio of
the trivializing elements: restriction does not move germs at `η`. -/
lemma germGenericUnits_unitsEvInf_res (P : X.MeromorphicPresentation)
    {𝒲 : X.PointedCover} (h : 𝒲 ≤ P.cover) (x y : X)
    (hη : genericPoint X ∈ 𝒲.opens x ⊓ 𝒲.opens y) :
    germGenericUnits hη
        (unitsEvInf (P.cocycle.res fun k => homOfLE (h k)) x y)
      = P.elem x * (P.elem y)⁻¹ := by
  rw [res_unitsEvInf, germGenericUnits_unitsRestrict]
  exact (P.ratio x y).symm

variable [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-- **The class law** (the W3 keystone): meromorphic presentations with equal divisors
present equal Čech Picard classes. On the common refinement, ord-matching produces unit
sections `u x` with `germ_η (u x) = P.elem x / Q.elem x`; the `0`-cochain `(u x)⁻¹`
exhibits the two restricted cocycles as cohomologous, the coboundary identity being
verified inside `K(X)ˣ`. -/
theorem picClass_eq_of_presentationDivisor_eq {P Q : X.MeromorphicPresentation}
    (h : presentationDivisor K P = presentationDivisor K Q) :
    P.picClass = Q.picClass := by
  -- the divisor equality, read as order matching at every closed point
  have hordAll : ∀ (z : X) (hz : z ≠ genericPoint X),
      Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz (P.elem z)
        = Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz (Q.elem z) := by
    intro z hz
    have hv := congrArg (coeffAt hz) h
    rw [coeffAt_presentationDivisor, coeffAt_presentationDivisor] at hv
    exact Multiplicative.toAdd.injective hv
  -- order matching on each piece of the common refinement, via piece-independence
  have hmatch : ∀ (x z : X) (hz : z ≠ genericPoint X),
      z ∈ (P.cover ⊓ Q.cover).opens x →
      Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz (P.elem x)
        = Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz (Q.elem x) := by
    intro x z hz hzx
    rw [P.ordZ_elem_eq K hz hzx.1, Q.ordZ_elem_eq K hz hzx.2]
    exact hordAll z hz
  -- ord-matching: the trivializing ratios are unit sections on the refined pieces
  choose u hu using fun x : X =>
    exists_germGenericUnits_eq_mul_inv_of_forall_ordZ_eq K
      ((P.cover ⊓ Q.cover).genericPoint_mem_opens x)
      (g := P.elem x) (h := Q.elem x) (fun z hz hzx => hmatch x z hz hzx)
  -- the coboundary identity, checked inside `K(X)ˣ`
  have hcoh : (P.cocycle.res fun k =>
        homOfLE ((inf_le_left : P.cover ⊓ Q.cover ≤ P.cover) k)).IsCohomologous
      (Q.cocycle.res fun k =>
        homOfLE ((inf_le_right : P.cover ⊓ Q.cover ≤ Q.cover) k)) := by
    refine unitsCocycle_isCohomologous (fun x => (u x)⁻¹) fun x y => ?_
    apply germGenericUnits_injective ((P.cover ⊓ Q.cover).genericPoint_mem_inf x y)
    simp only [map_mul, map_inv]
    rw [germGenericUnits_unitsRestrict, germGenericUnits_unitsRestrict, hu x, hu y,
      P.germGenericUnits_unitsEvInf_res inf_le_left x y,
      Q.germGenericUnits_unitsEvInf_res inf_le_right x y]
    group
  -- restriction does not move the Čech class
  calc P.picClass
      = CechPic.mk (P.cover ⊓ Q.cover)
          (unitsRes (inf_le_left : P.cover ⊓ Q.cover ≤ P.cover) P.cocycle.class) :=
        (CechPic.mk_unitsRes inf_le_left P.cocycle.class).symm
    _ = CechPic.mk (P.cover ⊓ Q.cover)
          (Q.cocycle.res fun k =>
            homOfLE ((inf_le_right : P.cover ⊓ Q.cover ≤ Q.cover) k)).class := by
        rw [unitsRes_class]
        exact congrArg _ hcoh.class_eq
    _ = CechPic.mk (P.cover ⊓ Q.cover)
          (unitsRes (inf_le_right : P.cover ⊓ Q.cover ≤ Q.cover) Q.cocycle.class) := by
        rw [unitsRes_class]
    _ = Q.picClass := CechPic.mk_unitsRes inf_le_right Q.cocycle.class

end MeromorphicPresentation

end Scheme

end AlgebraicGeometry
