/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.TwoTermFiniteFree
import AlgebraicJacobian.Picard.TwoTermKernelSemicontinuity

/-!
# Local constancy of two-term fibre Euler indices

This file records the pure commutative-algebra index carried by a
`TwoTermFiniteReplacement`.  At a prime `t` of `A`, the signed dimension

`dim ker(d_t) - dim coker(d_t)`

of the original base-changed map equals the virtual fibre rank

`rank_t(R.K0) - R.n`

of any finite replacement `R`.  The right-hand side is independent of the
choice of replacement and is locally constant on `PrimeSpectrum A`.

The first ingredient is only a carrier bridge:
`Ideal.isLocallyConstant_fiberRank` rewrites the project's residue-field
`Ideal.fiberRank` as Mathlib's `Module.rankAtStalk`, whose local constancy for
finitely presented flat modules is already available.  The substantive
two-term step uses both universal cohomology comparisons stored in `R`:
`R.h0_bijective` transports kernels and `R.h1_bijective` transports
cokernels from the finite replacement to the original complex.

Everything here is affine two-term algebra.  No declaration identifies this
index with `Scheme.Hom.fiberEulerIndex`, sheaf or curve cohomology, a
line-bundle degree, or a function on arbitrary test schemes.  In particular,
this file proves neither relative-Picard or etale descent nor a PicEt degree
producer.

## Main declarations

* `Ideal.isLocallyConstant_fiberRank`: the residue-field/stalk-rank bridge.
* `TwoTermFiniteReplacement.fiberEulerIndex_eq_virtualRank`: the original
  complex's signed fibre index equals the replacement's virtual rank.
* `TwoTermFiniteReplacement.fiberVirtualRank_independent`: independence from
  the chosen finite replacement.
* `TwoTermFiniteReplacement.isLocallyConstant_fiberEulerIndex`: local
  constancy of the original complex's signed fibre index on `Spec A`.
-/

set_option autoImplicit false

universe u

open Module TensorProduct

namespace Ideal

variable {A K : Type u} [CommRing A] [AddCommGroup K] [Module A K]

/-- The residue-field fibre rank of a finitely presented flat module is
locally constant on `PrimeSpectrum A`.

This is a direct transport of Mathlib's
`Module.isLocallyConstant_rankAtStalk` through
`Ideal.finrank_fiber_eq_rankAtStalk`; it is a notation/carrier bridge rather
than a new semicontinuity theorem. -/
theorem isLocallyConstant_fiberRank
    [Module.FinitePresentation A K] [Module.Flat A K] :
    IsLocallyConstant (fun t : PrimeSpectrum A => t.asIdeal.fiberRank K) := by
  convert Module.isLocallyConstant_rankAtStalk (R := A) (M := K) using 1
  funext t
  exact Ideal.finrank_fiber_eq_rankAtStalk t.asIdeal

end Ideal

namespace AlgebraicJacobian
namespace TwoTermFiniteReplacement

/-- The signed kernel/cokernel index of the original two-term complex after
base change to `kappa(t)` equals the virtual fibre rank of any finite
replacement.

All subtraction is in `Int`.  This result is stronger than rearranging
`TwoTerm.finrank_ker_baseChange_add_eq`: `R.h0_bijective` and
`R.h1_bijective` first identify the replacement kernel and cokernel with
those of the original map `d.baseChange kappa(t)`, and
`TwoTerm.fiberRank_quotRange_eq_finrank_quot_baseChange` identifies the
replacement cokernel rank. -/
theorem fiberEulerIndex_eq_virtualRank
    {A : Type u} [CommRing A]
    {M0 M1 : Type u} [AddCommGroup M0] [Module A M0]
    [AddCommGroup M1] [Module A M1] {d : M0 →ₗ[A] M1}
    (R : TwoTermFiniteReplacement d) (t : PrimeSpectrum A) :
    (Module.finrank t.asIdeal.ResidueField
        (LinearMap.ker (d.baseChange t.asIdeal.ResidueField)) : ℤ) -
      (Module.finrank t.asIdeal.ResidueField
        ((t.asIdeal.ResidueField ⊗[A] M1) ⧸
          LinearMap.range (d.baseChange t.asIdeal.ResidueField)) : ℤ) =
      (t.asIdeal.fiberRank R.K0 : ℤ) - (R.n : ℤ) := by
  have h0 :
      Module.finrank t.asIdeal.ResidueField
          (LinearMap.ker (R.k.baseChange t.asIdeal.ResidueField)) =
        Module.finrank t.asIdeal.ResidueField
          (LinearMap.ker (d.baseChange t.asIdeal.ResidueField)) :=
    LinearEquiv.finrank_eq
      (LinearEquiv.ofBijective
        (TwoTerm.h0Map (R.k.baseChange t.asIdeal.ResidueField)
          (d.baseChange t.asIdeal.ResidueField)
          (R.a0.baseChange t.asIdeal.ResidueField)
          (R.a1.baseChange t.asIdeal.ResidueField)
          (TwoTerm.baseChange_square R.k d R.a0 R.a1 t.asIdeal.ResidueField R.comm))
        (R.h0_bijective t.asIdeal.ResidueField))
  have h1 :
      Module.finrank t.asIdeal.ResidueField
          ((t.asIdeal.ResidueField ⊗[A] (Fin R.n → A)) ⧸
            LinearMap.range (R.k.baseChange t.asIdeal.ResidueField)) =
        Module.finrank t.asIdeal.ResidueField
          ((t.asIdeal.ResidueField ⊗[A] M1) ⧸
            LinearMap.range (d.baseChange t.asIdeal.ResidueField)) :=
    LinearEquiv.finrank_eq
      (LinearEquiv.ofBijective
        (TwoTerm.h1Map (R.k.baseChange t.asIdeal.ResidueField)
          (d.baseChange t.asIdeal.ResidueField)
          (R.a0.baseChange t.asIdeal.ResidueField)
          (R.a1.baseChange t.asIdeal.ResidueField)
          (TwoTerm.baseChange_square R.k d R.a0 R.a1 t.asIdeal.ResidueField R.comm))
        (R.h1_bijective t.asIdeal.ResidueField))
  have hcoker :=
    TwoTerm.fiberRank_quotRange_eq_finrank_quot_baseChange R.k t
  have hrank := TwoTerm.finrank_ker_baseChange_add_eq R.n R.k t
  omega

/-- The virtual fibre rank `(rank_t R.K0 : Int) - R.n` is independent of the
chosen finite replacement of the same original map.  Both sides equal the
signed kernel/cokernel index of that original map. -/
theorem fiberVirtualRank_independent
    {A : Type u} [CommRing A]
    {M0 M1 : Type u} [AddCommGroup M0] [Module A M0]
    [AddCommGroup M1] [Module A M1] {d : M0 →ₗ[A] M1}
    (R R' : TwoTermFiniteReplacement d) (t : PrimeSpectrum A) :
    (t.asIdeal.fiberRank R.K0 : ℤ) - (R.n : ℤ) =
      (t.asIdeal.fiberRank R'.K0 : ℤ) - (R'.n : ℤ) := by
  rw [← R.fiberEulerIndex_eq_virtualRank t,
    ← R'.fiberEulerIndex_eq_virtualRank t]

/-- The signed kernel/cokernel index of the original base-changed two-term
complex is locally constant on `PrimeSpectrum A`.

The finite-projective module `R.K0` is finitely presented and flat, so its
fibre rank is locally constant.  Postcomposing by `r |-> (r : Int) - R.n`
and using `fiberEulerIndex_eq_virtualRank` gives the stated function.  This is
only an affine module-theoretic result, with no sheaf-cohomology comparison. -/
theorem isLocallyConstant_fiberEulerIndex
    {A : Type u} [CommRing A]
    {M0 M1 : Type u} [AddCommGroup M0] [Module A M0]
    [AddCommGroup M1] [Module A M1] {d : M0 →ₗ[A] M1}
    (R : TwoTermFiniteReplacement d) :
    IsLocallyConstant (fun t : PrimeSpectrum A =>
      (Module.finrank t.asIdeal.ResidueField
          (LinearMap.ker (d.baseChange t.asIdeal.ResidueField)) : ℤ) -
        (Module.finrank t.asIdeal.ResidueField
          ((t.asIdeal.ResidueField ⊗[A] M1) ⧸
            LinearMap.range (d.baseChange t.asIdeal.ResidueField)) : ℤ)) := by
  letI : Module.Flat A R.K0 := Module.Flat.of_projective
  letI : Module.FinitePresentation A R.K0 :=
    Module.finitePresentation_of_projective A R.K0
  have h : IsLocallyConstant (fun t : PrimeSpectrum A =>
      (t.asIdeal.fiberRank R.K0 : ℤ) - (R.n : ℤ)) := by
    change IsLocallyConstant
      ((fun r : ℕ => (r : ℤ) - (R.n : ℤ)) ∘
        (fun t : PrimeSpectrum A => t.asIdeal.fiberRank R.K0))
    exact (Ideal.isLocallyConstant_fiberRank (A := A) (K := R.K0)).comp
      fun r => (r : ℤ) - (R.n : ℤ)
  convert h using 1
  funext t
  exact R.fiberEulerIndex_eq_virtualRank t

end TwoTermFiniteReplacement
end AlgebraicJacobian
