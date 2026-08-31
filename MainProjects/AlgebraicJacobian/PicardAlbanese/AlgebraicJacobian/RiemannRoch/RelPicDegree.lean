/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.DegreeBaseFieldInvariance

/-!
# The degree on the relative Picard group over a field (gap G-D5(b), SB-5 descent gadgets)

For the challenge curve `C : Over (Spec k)` and a field extension `K` of `k`, the relative
Picard group `relPic C (overSpec k K) = CechPic(C_K) ⧸ picFromBase` quotients out the classes
pulled back from `Spec K` — but `Spec K` is a one-point space, so its Čech Picard group is
trivial (`Scheme.CechPic.subsingleton_of_subsingleton`) and `classDeg K` kills `picFromBase`
(`classDeg_eq_zero_of_mem_picFromBase`).  The degree therefore descends to the relative
Picard group:

* `AlgebraicGeometry.relPicDeg K : Additive (relPic C (overSpec k K)) →+ ℤ`, with the anchor
  `relPicDeg_relPicMk : relPicDeg K (relPicMk C (overSpec k K) L) = classDeg K L`;
* `AlgebraicGeometry.relPicDeg_relPicAlgMap` — **E-iv-alg descended to `relPic`**: the
  relative degree is invariant under restriction along `Spec` of any `k`-algebra map of
  field extensions, `relPicDeg K₂ (relPicAlgMap C φ x) = relPicDeg K₁ x`.

These are the two descent gadgets of `informal/deg-d5b-worksheet.md` §4 SB-5; the `degAt`
brick (SB-6) consumes `relPicDeg` and `relPicDeg_relPicAlgMap` verbatim — on a field
representative `(K', y)` of an étale-locally-trivial class, the honest degree is
`relPicDeg K' y`, well-defined across representatives by `relPicDeg_relPicAlgMap`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-! ## `classDeg` kills the classes from the base -/

/-- **The degree vanishes on classes pulled back from the base field**: `Spec K` is a
one-point space, so its Čech Picard group is trivial and every class of `picFromBase` is
trivial. -/
theorem classDeg_eq_zero_of_mem_picFromBase {K : Type u} [Field K] [Algebra k K]
    {L : (C ⊗ overSpec k K).left.CechPic} (hL : L ∈ picFromBase C (overSpec k K)) :
    classDeg K L = 0 := by
  obtain ⟨N, rfl⟩ := (mem_picFromBase_iff C).mp hL
  haveI : Subsingleton (overSpec k K).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  rw [Scheme.CechPic.eq_one_of_subsingleton (overSpec k K).left N, map_one, classDeg_one]

/-! ## The relative degree -/

/-- **The degree on the relative Picard group over a field** (worksheet SB-5, first descent
gadget): `classDeg K` descends along `relPicMk` to the quotient
`relPic C (overSpec k K) = CechPic(C_K) ⧸ picFromBase`, because the Čech Picard group of the
one-point scheme `Spec K` is trivial.  The `degAt` brick (SB-6) reads the degree of a
field-representative of an étale-locally-trivial class through this homomorphism. -/
noncomputable def relPicDeg (K : Type u) [Field K] [Algebra k K] :
    Additive (relPic C (overSpec k K)) →+ ℤ :=
  MonoidHom.toAdditiveLeft
    (QuotientGroup.lift (picFromBase C (overSpec k K))
      (AddMonoidHom.toMultiplicativeRight (classDeg K))
      (fun L hL => by
        have h0 : classDeg K L = 0 := classDeg_eq_zero_of_mem_picFromBase hL
        rw [MonoidHom.mem_ker]
        change Multiplicative.ofAdd (classDeg K L) = 1
        rw [h0, ofAdd_zero]))

/-- **The anchor of the relative degree**: on the class of `L`, the relative degree is
`classDeg K L`. -/
@[simp]
theorem relPicDeg_relPicMk (K : Type u) [Field K] [Algebra k K]
    (L : (C ⊗ overSpec k K).left.CechPic) :
    relPicDeg K (relPicMk C (overSpec k K) L) = classDeg K L :=
  rfl

/-- **E-iv-alg descended to the relative Picard group** (worksheet SB-5, second descent
gadget): the relative degree is invariant under restriction along `Spec` of a `k`-algebra
map `φ : K₁ →ₐ[k] K₂` of field extensions — the degree of a relative Picard class does not
depend on the field over which it is presented. -/
theorem relPicDeg_relPicAlgMap {K₁ K₂ : Type u} [Field K₁] [Algebra k K₁] [Field K₂]
    [Algebra k K₂] (φ : K₁ →ₐ[k] K₂) (x : relPic C (overSpec k K₁)) :
    relPicDeg K₂ (relPicAlgMap C φ x) = relPicDeg K₁ x := by
  induction x using relPic.ind with
  | mk L =>
    have h1 : relPicAlgMap C φ (relPicMk C (overSpec k K₁) L)
        = relPicMk C (overSpec k K₂)
          (Scheme.CechPic.map ((C ◁ Over.overSpecMap φ).left) L) :=
      relPicMap_mk C (Over.overSpecMap φ) L
    rw [h1, relPicDeg_relPicMk, relPicDeg_relPicMk,
      classDeg_cechPicMap_baseFieldTransition C φ L]

end AlgebraicGeometry
