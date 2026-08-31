/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.TruncExpCechTransport
import AlgebraicJacobian.Picard.LaurentTwoChartCoboundary
import AlgebraicJacobian.Picard.TwoChartCechPicTrivial

/-!
# The algebra→scheme seam for two-chart ℙ¹ coboundaries

The pure-algebra layer (`Picard/LaurentTwoChartCoboundary.lean` and the `Algebra/Laurent*`
files) characterises `laurentCoboundaryUnits A`, the coboundary subgroup of the abstract
two-chart datum `Polynomial.toLaurent`, `rightChart A` on the Laurent overlap ring
`LaurentPolynomial A`.  A scheme consumer of `Scheme.cechPic_eq_one_of_forall_presenting_coboundary`
instead holds `Scheme.twoChartCoboundaryUnits V`, the coboundary subgroup of the scheme
restriction maps `X.resHom` on `Γ(X, V₀ ⊓ V₁)ˣ`.

Both are literally `TruncExpCech.cechCoboundaryUnits` of the respective restriction ring homs
(`Scheme.twoChartCoboundaryUnits` unfolds to it by definition, `LaurentTwoChartCoboundary.lean`
and `TwoChartCechPicTrivial.lean:71`).  So an **identification of the two data** — ring
isomorphisms of the two chart section rings with `A[t]` and of the overlap section ring with
`A[T;T⁻¹]`, intertwining the scheme restrictions with `toLaurent`/`rightChart` — transports
coboundary membership between them.  This file is that seam: it consumes the identification as
hypotheses (the base-changed `ℙ¹_A` two-chart cover that realises them is the remaining scheme
build) and hands back the scheme-side `twoChartCoboundaryUnits` membership the criterion wants.

Nothing here assumes the identifying isomorphisms are anything in particular, and nothing here
uses a new hypothesis on the ring `A`: it is the naturality of `cechCoboundaryUnits`
(`TruncExpCech.mem_cechCoboundaryUnits_map_iff`) instantiated at the two Laurent chart maps.

## Main declarations

* `AlgebraicGeometry.mem_twoChartCoboundaryUnits_iff_laurent` — given the chart identification
  data, a scheme overlap unit is in `twoChartCoboundaryUnits V` iff its `A[T;T⁻¹]ˣ` image is in
  `laurentCoboundaryUnits A`.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {V : Bool → X.Opens}

/-- **The algebra→scheme coboundary seam.**

Suppose the two-chart cover `V` of `X` is Laurent-identified over `A`: ring isomorphisms
`γ₀ : Γ(X, V false) ≃+* A[t]`, `γ₁ : Γ(X, V true) ≃+* A[t]` of the two chart section rings and
`γ₀₁ : Γ(X, V false ⊓ V true) ≃+* A[T;T⁻¹]` of the overlap section ring, intertwining the
scheme restrictions `X.resHom` with the two Laurent chart maps
(`Polynomial.toLaurent`, `rightChart A`):

* `hres₀ : γ₀₁ ∘ resHom(inf_le_left) = toLaurent ∘ γ₀`;
* `hres₁ : γ₀₁ ∘ resHom(inf_le_right) = rightChart A ∘ γ₁`.

Then a scheme overlap unit `u : Γ(X, V false ⊓ V true)ˣ` is a two-chart coboundary iff its
image `Units.map γ₀₁ u : (A[T;T⁻¹])ˣ` is a Laurent coboundary.  Composed with the landed
`mem_laurentCoboundaryUnits_iff_general`, this reads the scheme-side coboundary condition off
the exponent-zero normal form of the transported Laurent unit — with no new hypothesis. -/
theorem mem_twoChartCoboundaryUnits_iff_laurent
    (γ₀ : Γ(X, V false) ≃+* Polynomial A) (γ₁ : Γ(X, V true) ≃+* Polynomial A)
    (γ₀₁ : Γ(X, V false ⊓ V true) ≃+* LaurentPolynomial A)
    (hres₀ : (γ₀₁ : Γ(X, V false ⊓ V true) →+* LaurentPolynomial A).comp
        (X.resHom (inf_le_left : V false ⊓ V true ≤ V false))
      = (Polynomial.toLaurent : Polynomial A →+* LaurentPolynomial A).comp
        (γ₀ : Γ(X, V false) →+* Polynomial A))
    (hres₁ : (γ₀₁ : Γ(X, V false ⊓ V true) →+* LaurentPolynomial A).comp
        (X.resHom (inf_le_right : V false ⊓ V true ≤ V true))
      = (rightChart A).comp (γ₁ : Γ(X, V true) →+* Polynomial A))
    (u : Γ(X, V false ⊓ V true)ˣ) :
    u ∈ Scheme.twoChartCoboundaryUnits V
      ↔ Units.map (γ₀₁ : Γ(X, V false ⊓ V true) →+* LaurentPolynomial A).toMonoidHom u
          ∈ laurentCoboundaryUnits A := by
  have h :=
    TruncExpCech.mem_cechCoboundaryUnits_map_iff
      (X.resHom (inf_le_left : V false ⊓ V true ≤ V false))
      (X.resHom (inf_le_right : V false ⊓ V true ≤ V true))
      (Polynomial.toLaurent : Polynomial A →+* LaurentPolynomial A) (rightChart A)
      γ₀ γ₁ γ₀₁ hres₀ hres₁ u
  exact h.symm

end AlgebraicGeometry
