/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.StalksDVR
import AlgebraicJacobian.Cohomology.ModuleKSheaf

/-!
# Closed points of a curve: valuation order and residue degree

For a scheme `X` smooth of relative dimension one over a field `K` and integral (the curve
bundle of the Jacobian challenge), every non-generic point `x` is closed, its local ring
`𝒪_{X,x}` is a discrete valuation ring, and it carries:

* `AlgebraicGeometry.isDiscreteValuationRing_stalk` / `isDedekindDomain_stalk`: the DVR /
  Dedekind structure on the stalk at a closed point;
* `AlgebraicGeometry.Scheme.ord`: the `ℤᵐ⁰`-valued valuation of the function field determined
  by the closed point (the order of vanishing of a rational function at `x`);
* `AlgebraicGeometry.Scheme.residueDeg`: the residue degree `[κ(x) : K]`, the `K`-dimension of
  the residue field, together with (in a later section) its finiteness and positivity.

The `K`-module structure on the residue field is carried by the explicit ring homomorphism
`Scheme.residueOverAlgebraMap` (through the structure morphism), never a global `Algebra`
instance, mirroring the `Scheme.overModule` discipline of `Cohomology.ModuleKSheaf`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section DVR

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- **DVR at a closed point of an affine Dedekind chart.** If `x` lies in an affine open with
Dedekind section ring and is not the generic point of the (irreducible) scheme, its stalk is a
discrete valuation ring: the localization of a Dedekind domain at a nonzero prime. -/
theorem IsAffineOpen.isDiscreteValuationRing_stalk [IsIntegral X] {V : X.Opens}
    (hV : IsAffineOpen V) (hD : IsDedekindDomain Γ(X, V)) {x : X} (hx : x ∈ V)
    (hxg : x ≠ genericPoint X) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  set q := hV.primeIdealOf ⟨x, hx⟩ with hq
  have hbot : q.asIdeal ≠ ⊥ := by
    intro h
    apply hxg
    have h1 : hV.fromSpec.base q = x := hV.fromSpec_primeIdealOf ⟨x, hx⟩
    have hgen : (genericPoint (Spec Γ(X, V)) : Spec Γ(X, V)) = q := by
      rw [genericPoint_eq_bot_of_affine]
      exact (PrimeSpectrum.ext h).symm
    rw [← h1, ← hgen, genericPoint_eq_of_isOpenImmersion hV.fromSpec]
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain Γ(X, V) hbot _

/-- **DVR at a closed point of a smooth curve.** On an integral scheme smooth of relative
dimension one over a field, the stalk at a non-generic point is a discrete valuation ring. -/
theorem isDiscreteValuationRing_stalk (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X} (hx : x ≠ genericPoint X) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  obtain ⟨V, hV, hxV, hD⟩ :=
    SmoothOfRelativeDimension.exists_isDedekindDomain_section f x
  exact hV.isDiscreteValuationRing_stalk hD hxV hx

/-- The stalk at a closed point of a smooth curve is a Dedekind domain (a DVR is a PID). -/
theorem isDedekindDomain_stalk (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X} (hx : x ≠ genericPoint X) :
    IsDedekindDomain (X.presheaf.stalk x) := by
  haveI := isDiscreteValuationRing_stalk f hx
  infer_instance

/-- **Closed points are the non-generic points.** On an integral smooth curve, every point
other than the generic point is closed: its only generalization is itself or the generic
point (height-one specialization order). -/
theorem isClosed_singleton_of_ne_genericPoint (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X} (hx : x ≠ genericPoint X) :
    IsClosed ({x} : Set X) :=
  Scheme.isClosed_singleton_of_forall_specializes
    (fun _ _ h => SmoothOfRelativeDimension.specializes_eq_genericPoint_or_eq f h) hx

end DVR

section Order

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- **The order valuation at a closed point.** The `ℤᵐ⁰`-valued valuation of the function
field `K(X)` determined by the discrete valuation ring `𝒪_{X,x}` at a closed point `x`: the
order of vanishing of a rational function at `x`. -/
noncomputable def Scheme.ord (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X} (hx : x ≠ genericPoint X) :
    Valuation X.functionField (WithZero (Multiplicative ℤ)) := by
  letI := isDiscreteValuationRing_stalk f hx
  letI := isDedekindDomain_stalk f hx
  exact
    ({ asIdeal := IsLocalRing.maximalIdeal (X.presheaf.stalk x)
       isPrime := (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).isPrime
       ne_bot := IsDiscreteValuationRing.not_a_field (X.presheaf.stalk x) } :
      IsDedekindDomain.HeightOneSpectrum (X.presheaf.stalk x)).valuation X.functionField

end Order

section ResidueDegree

variable (K : Type u) [CommRing K] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))]

/-- The `K`-algebra structure map on the residue field `κ(x)` of a scheme over `Spec K`,
through the structure morphism: `K →+* Γ(X, ⊤) →+* 𝒪_{X,x} →+* κ(x)`. Deliberately not a
global `Algebra` instance (same overlap hazard as `Scheme.overModule`). -/
noncomputable def Scheme.residueOverAlgebraMap (x : X) : K →+* X.residueField x :=
  (X.residue x).hom.comp
    (((X.presheaf.germ ⊤ x trivial).hom).comp (X.overAlgebraMap K ⊤))

/-- The `K`-module structure on the residue field `κ(x)`, by restriction of scalars along
`Scheme.residueOverAlgebraMap`. Activate with `attribute [local instance]` where needed. -/
@[reducible] noncomputable def Scheme.residueFieldOverModule (x : X) :
    Module K (X.residueField x) :=
  (X.residueOverAlgebraMap K x).toModule

attribute [local instance] Scheme.residueFieldOverModule

/-- **The residue degree** `[κ(x) : K]`: the `K`-dimension of the residue field at `x`. -/
noncomputable def Scheme.residueDeg (x : X) : ℕ :=
  Module.finrank K (X.residueField x)

end ResidueDegree

end AlgebraicGeometry
