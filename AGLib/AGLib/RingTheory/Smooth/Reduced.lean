/-
Copyright (c) 2026 Frenzymath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frenzymath
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Unramified.Field

/-!
# Reducedness of standard smooth algebras

This file proves that flat, essentially finite type, formally unramified algebras over domains
are reduced. It then applies this result to etale and standard smooth algebras.

For the standard smooth case, Mathlib's
`RingHom.IsStandardSmooth.exists_etale_mvPolynomial` presents the target as etale over a
polynomial ring. This is the etale-coordinate description appearing in
[The Stacks Project, Tag 054L][stacks-project]; see also
[The Stacks Project, Tag 00T7][stacks-project] for the basic properties of standard smooth
algebras.

## Main results

* `Algebra.FormallyUnramified.isReduced_of_isDomain`
* `Algebra.Etale.isReduced_of_isDomain`
* `RingHom.IsStandardSmooth.isReduced_of_isDomain`
* `Algebra.IsStandardSmooth.isReduced_of_isDomain`

## Provenance

The proofs were audited from the Mathlib-only modules
`MainProjects/AlgebraicJacobian/MilneKollar/AlgebraicJacobian/Curve/GeometricallyReduced.lean`
and
`MainProjects/AlgebraicJacobian/PicardAlbanese/AlgebraicJacobian/Curve/GeometricallyReduced.lean`
at repository commit `9223d85c786394721963a9d642b08d066b72a594`.
-/

public section

open TensorProduct

section RingTheory

/-- A flat, essentially finite type, formally unramified algebra over a domain is reduced.

This extends `Algebra.FormallyUnramified.isReduced_of_field` from a field to a domain; flatness
is used to embed the algebra into its base change to the fraction field. -/
theorem Algebra.FormallyUnramified.isReduced_of_isDomain (R A : Type*) [CommRing R] [CommRing A]
    [IsDomain R] [Algebra R A] [Algebra.FormallyUnramified R A]
    [Algebra.EssFiniteType R A] [Module.Flat R A] : IsReduced A := by
  have : IsReduced (FractionRing R ⊗[R] A) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing R) (FractionRing R ⊗[R] A)
  refine isReduced_of_injective
    (Algebra.TensorProduct.includeRight (R := R) (A := FractionRing R) (B := A)) ?_
  have h : ⇑(Algebra.TensorProduct.includeRight (R := R) (A := FractionRing R) (B := A)) =
      ⇑(LinearMap.rTensor A (Algebra.ofId R (FractionRing R)).toLinearMap) ∘
        ⇑(TensorProduct.lid R A).symm := by
    ext a
    simp
  rw [h]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _
    (IsFractionRing.injective R (FractionRing R))).comp (TensorProduct.lid R A).symm.injective

/-- An etale algebra over a domain is reduced. -/
theorem Algebra.Etale.isReduced_of_isDomain (R A : Type*) [CommRing R] [CommRing A] [IsDomain R]
    [Algebra R A] [Algebra.Etale R A] : IsReduced A :=
  Algebra.FormallyUnramified.isReduced_of_isDomain R A

/-- The target of a standard smooth ring homomorphism from a domain is reduced.

The proof uses the etale coordinates for a standard smooth algebra described in
[The Stacks Project, Tag 054L][stacks-project]. -/
theorem RingHom.IsStandardSmooth.isReduced_of_isDomain {R A : Type*} [CommRing R] [CommRing A]
    [IsDomain R] {f : R →+* A} (hf : f.IsStandardSmooth) : IsReduced A := by
  obtain ⟨n, g, -, hg⟩ := hf.exists_etale_mvPolynomial
  algebraize [g]
  exact Algebra.Etale.isReduced_of_isDomain (MvPolynomial (Fin n) R) A

/-- A standard smooth algebra over a domain is reduced. -/
theorem Algebra.IsStandardSmooth.isReduced_of_isDomain (R A : Type*) [CommRing R] [CommRing A]
    [IsDomain R] [Algebra R A] [Algebra.IsStandardSmooth R A] : IsReduced A :=
  (RingHom.isStandardSmooth_algebraMap.mpr ‹_›).isReduced_of_isDomain

end RingTheory
