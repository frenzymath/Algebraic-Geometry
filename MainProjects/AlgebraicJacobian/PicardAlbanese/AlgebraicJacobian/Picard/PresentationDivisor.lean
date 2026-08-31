/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.MeromorphicPresentation
import AlgebraicJacobian.RiemannRoch.ChiFiniteness

/-!
# The divisor of a meromorphic presentation

For the curve bundle `X` (integral, smooth of relative dimension one and quasi-compact
over a field `K`) and a meromorphic presentation `P`
(`AlgebraicJacobian.Picard.MeromorphicPresentation`), this file constructs the Weil
divisor cut out by the presentation: at a closed point `x`, the multiplicity is the
order of vanishing of the trivializing element of the piece indexed by `x` itself,

`presentationDivisor K P = ∑ₓ ord_x (P.elem x) · x`.

## Well-definedness and finiteness

* piece-independence (`MeromorphicPresentation.ordZ_elem_eq`): on any piece containing a
  closed point `x`, the trivializing elements have the same order at `x` — their ratio is
  the germ at `η` of a *unit section* on the overlap, and germs of unit sections have
  trivial order at every point of their open (`Scheme.ordZ_germGenericUnits`);
* finite support (`MeromorphicPresentation.ordZ_elem_support_finite`): the curve is
  quasi-compact, so finitely many pieces cover it; on each piece the multiplicities are
  read off one rational function, whose order support is finite
  (`Scheme.ordZ_support_finite`).

## `coeffAt` calculus

The file also provides the small transport calculus for the landed coefficient function
`AlgebraicGeometry.coeffAt` (`RiemannRoch/Devissage.lean`) — extensionality and values on
`0`, `+`, `-`, negation and one-point divisors — used by every divisor comparison in the
meromorphic-bridge campaign (`CurveDivisor` is a sealed `Finsupp`; these lemmas keep raw
`Finsupp` projections out of downstream proofs).
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace Scheme

/-! ## The `coeffAt` calculus for Weil divisors -/

namespace CurveDivisor

variable {X : Scheme.{u}} [IsIntegral X]

/-- Two Weil divisors with the same coefficient at every closed point are equal. -/
lemma ext_coeffAt {D D' : X.CurveDivisor}
    (h : ∀ (x : X) (hx : x ≠ genericPoint X), coeffAt hx D = coeffAt hx D') : D = D' :=
  Finsupp.ext fun p => h p.1 p.2

variable {x : X} (hx : x ≠ genericPoint X)

@[simp]
lemma coeffAt_zero : coeffAt hx (0 : X.CurveDivisor) = 0 :=
  rfl

@[simp]
lemma coeffAt_add (D D' : X.CurveDivisor) :
    coeffAt hx (D + D') = coeffAt hx D + coeffAt hx D' :=
  Finsupp.add_apply _ _ _

@[simp]
lemma coeffAt_neg (D : X.CurveDivisor) : coeffAt hx (-D) = -coeffAt hx D :=
  Finsupp.neg_apply _ _

@[simp]
lemma coeffAt_sub (D D' : X.CurveDivisor) :
    coeffAt hx (D - D') = coeffAt hx D - coeffAt hx D' :=
  Finsupp.sub_apply _ _ _

/-- The coefficient of the one-point divisor `n · x` at `x` is `n`. -/
@[simp]
lemma coeffAt_single_self (n : ℤ) : coeffAt hx (CurveDivisor.single hx n) = n :=
  Finsupp.single_eq_same

/-- The coefficient of the one-point divisor `n · x` at a closed point `z ≠ x` is `0`. -/
lemma coeffAt_single_of_ne {z : X} (hz : z ≠ genericPoint X) (hzx : z ≠ x) (n : ℤ) :
    coeffAt hz (CurveDivisor.single hx n) = 0 :=
  Finsupp.single_eq_of_ne fun h => hzx (Subtype.mk_eq_mk.mp h)

/-- One-point divisors negate their multiplicities. -/
lemma single_neg (n : ℤ) :
    CurveDivisor.single hx (-n) = -CurveDivisor.single hx n :=
  Finsupp.single_neg _ _

/-- The coefficient of a principal divisor at a closed point is the order of vanishing
there. -/
lemma coeffAt_divOf {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 f] [IsIntegral X]
    [LocallyOfFiniteType f] [QuasiCompact f] (g : X.functionFieldˣ) {x : X}
    (hx : x ≠ genericPoint X) :
    coeffAt hx (Scheme.divOf f g) = Multiplicative.toAdd (Scheme.ordZ f hx g) :=
  rfl

end CurveDivisor

/-! ## Orders of the trivializing elements -/

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]

/-- **Unit sections have trivial order.** The germ at `η` of a unit section over an open
`U` has order zero at every closed point of `U`: locally the rational function is a unit
of the structure sheaf. This is the local vanishing statement behind the
piece-independence of `presentationDivisor`. -/
theorem ordZ_germGenericUnits {U : X.Opens} (hηU : genericPoint X ∈ U) (u : Γ(X, U)ˣ)
    {x : X} (hx : x ≠ genericPoint X) (hxU : x ∈ U) :
    Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hx (germGenericUnits hηU u) = 1 := by
  rw [Scheme.ordZ_eq_one_iff]
  have hmem : x ∈ X.basicOpen (u : Γ(X, U)) :=
    (X.mem_basicOpen (u : Γ(X, U)) x hxU).mpr
      (u.isUnit.map (X.presheaf.germ U x hxU).hom)
  exact Scheme.ord_eq_one_of_mem_basicOpen (X ↘ Spec (CommRingCat.of K)) hx
    (u : Γ(X, U)) hηU hmem

/-- The bridge between the classical order `ordZ` and the mathlib valuation `ord`: the
inverse of `ordZ` (recall the sign inversion in its definition), coerced into `ℤᵐ⁰`, is
the valuation of the underlying rational function. -/
theorem coe_inv_ordZ (g : X.functionFieldˣ) {x : X} (hx : x ≠ genericPoint X) :
    (((Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hx g)⁻¹ : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ))
      = Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (g : X.functionField) := by
  rw [Scheme.ordZ]
  simp only [MonoidHom.comp_apply, invMonoidHom_apply, inv_inv, MulEquiv.coe_toMonoidHom,
    WithZero.coe_unitsWithZeroEquiv_eq_units_val]
  rfl

namespace MeromorphicPresentation

/-- **Piece-independence of the order.** At a closed point `x` of a piece
`P.cover.opens y`, the trivializing element of that piece has the same order as the
trivializing element of the piece indexed by `x` itself: their ratio is the germ of a
unit section on the overlap. -/
theorem ordZ_elem_eq (P : X.MeromorphicPresentation) {x : X} (hx : x ≠ genericPoint X)
    {y : X} (hxy : x ∈ P.cover.opens y) :
    Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hx (P.elem y)
      = Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hx (P.elem x) := by
  have key := congrArg (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hx) (P.ratio x y)
  rw [map_mul, map_inv,
    ordZ_germGenericUnits K (P.cover.genericPoint_mem_inf x y) _ hx
      ⟨P.cover.mem_opens x, hxy⟩] at key
  exact (mul_inv_eq_one.mp key).symm

variable [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-- **Finite support.** The closed points at which the (piece-indexed) trivializing
element has nontrivial order form a finite set: finitely many pieces cover the
quasi-compact curve, and on each piece the orders are those of a single rational
function. -/
theorem ordZ_elem_support_finite (P : X.MeromorphicPresentation) :
    {p : {x : X // x ≠ genericPoint X} |
      Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) p.2 (P.elem p.1) ≠ 1}.Finite := by
  haveI : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i : X => (P.cover.opens i : Set X)) (fun i => (P.cover.opens i).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, P.cover.mem_opens x⟩)
  refine Set.Finite.subset (Set.Finite.biUnion t.finite_toSet
    (fun i _ => Scheme.ordZ_support_finite (X ↘ Spec (CommRingCat.of K)) (P.elem i))) ?_
  intro p hp
  obtain ⟨i, hit, hpi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p.1))
  refine Set.mem_biUnion hit ?_
  change Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) p.2 (P.elem i) ≠ 1
  rw [P.ordZ_elem_eq K p.2 hpi]
  exact hp

end MeromorphicPresentation

/-! ## The divisor of a presentation -/

/-- **The divisor of a meromorphic presentation** (the W2 deliverable): the Weil divisor
whose multiplicity at a closed point `x` is the order of vanishing at `x` of the
trivializing element `P.elem x` of the piece indexed by `x`. By piece-independence
(`MeromorphicPresentation.ordZ_elem_eq`) this is the order of the local trivialization
of the presented class near `x`, whichever piece is used to read it off. -/
noncomputable def presentationDivisor [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    (P : X.MeromorphicPresentation) : X.CurveDivisor :=
  Finsupp.onFinset (P.ordZ_elem_support_finite K).toFinset
    (fun p => Multiplicative.toAdd
      (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) p.2 (P.elem p.1)))
    (fun p hp => by
      rw [Set.Finite.mem_toFinset]
      exact fun he => hp (by rw [he, toAdd_one]))

/-- The multiplicity of the divisor of a presentation at a closed point `x` is the order
of vanishing of the trivializing element `P.elem x`. -/
@[simp]
theorem coeffAt_presentationDivisor [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    (P : X.MeromorphicPresentation) {x : X} (hx : x ≠ genericPoint X) :
    coeffAt hx (presentationDivisor K P)
      = Multiplicative.toAdd (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hx (P.elem x)) :=
  rfl

end Scheme

end AlgebraicGeometry
