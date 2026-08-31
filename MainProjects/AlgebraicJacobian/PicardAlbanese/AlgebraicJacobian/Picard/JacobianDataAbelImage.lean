/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.CompactImageQc
import AlgebraicJacobian.Picard.JacobianDataCharts
import AlgebraicJacobian.Picard.DivSchemeQProj

/-!
# DAT-J: the datum from a Pic⁰ representation and a surjective Abel map (DJ-1/DJ-2)

`informal/w4-datj-worksheet.md` §2.2 freezes the mechanism of `JacobianData.quasiCompact`:
*"a posteriori, `|J|` is the image of a quasi-compact divisor scheme under the Abel map."*
DJ-0 (`Picard/CompactImageQc.lean`) is the abstract engine and DD-Q's
`compactSpace_divScheme` is the compact source.  This file removes the remaining
bookkeeping between them, so the qc field costs exactly one surjectivity statement:

* `AlgebraicGeometry.quasiCompact_of_surjective_from_divScheme` — **DJ-1's qc step**: a
  surjection from `DivScheme g` onto `J.left` gives `QuasiCompact J.hom`.  The compact
  source is the DD-Q instance, the base is affine, and DJ-0 does the rest; nothing about
  divisors or the Abel map enters, only that the source is *that* scheme.
* `AlgebraicGeometry.JacobianData.ofAbelImage` — **DJ-2**: the four-field packaging with the
  qc field replaced by the Abel-image hypothesis.  A producer owes a Pic⁰ representation, an
  lft certificate, and a point-surjective morphism out of `DivScheme g`.
* `AlgebraicGeometry.JacobianData.ofChartsOfAbelImage` — the same against a chart atlas, so
  the infinite-atlas producer `ofChartsOfCompactSpace` (whose `CompactSpace` hypothesis is
  §2.1's genuinely a-posteriori one) becomes usable from a surjection.

**What this is and is not.**  It is the plumbing of §2.2 steps 1, 2 and 4, discharged once.
Step 3 — surjectivity of the Abel map on points — is DJ-1's honest brick and is *not* proved
here.  Per §0.5 that brick must stay Challenge-free: use `exists_effective_of_picClass` /
`riemann_inequality`, never `riemann_inequality_curve`, which imports `Challenge.lean`.

**AMENDMENT 2026-07-29, two corrections to the sentence this replaces.**  It used to say the
brick "needs the universal degree-`g` class, hence `divRep`, plus `exists_effective_of_picClass`
and the `fiberTwist` shift".  Both cost claims were wrong:

* **Not `divRep`-gated.**  The effectivity content is landed and divRep-free at every point of
  any `Pic⁰`-representing object (`exists_effective_deg_eq_of_pic0_at_point`,
  `Picard/JacobianDataAbelEffectivePoint.lean`).  Only the Abel *square* needs the
  representation.
* **No `fiberTwist` shift.**  At degree exactly `g` the entry condition `1 ≤ deg W + χ(𝒪)`
  reads `g ≤ deg W`, so the class sits on the boundary and `exists_effective_of_picClass` fires
  with no slack.  A shift is what one needs to lift a degree-*zero* class into the effective
  range, and that is one multiplication by a fixed degree-`g` class
  (`exists_effective_deg_eq_of_classDeg_eq_zero`), not a `fiberTwist` construction.

What genuinely remains on this side is **descent**: the divisor is produced over a finite
separable splitting field of `κ(y)`, and `hlift` wants `Spec κ(y)`.

Note that the statements below take the surjection as a *bare morphism* out of `DivScheme g`
rather than as an Abel map built from a representation.  That is deliberate: it keeps the
file independent of the divisor-representability chain, so the qc mechanism is available to
any producer of a surjection — including the chart-atlas route, which does not name an Abel
map at all.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

/-! ## The qc step at the campaign's compact source -/

section Qc

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
variable (A B : X.CurveDivisor) (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k ↥(Scheme.divisorSections k B ⊤))
variable (b₂ : Module.Basis (Fin r₂) k ↥(Scheme.divisorSections k (A + B) ⊤))

/-- **DJ-1's quasi-compactness step** (w4-datj §2.2 steps 1, 2, 4): if the Jacobian-to-be
receives a point-surjective morphism from the divisor scheme `DivScheme g`, its structure
morphism is quasi-compact.

`DivScheme g` is a compact space (`compactSpace_divScheme`, DD-Q: it is a closed subscheme of
a Grassmannian pair with a finite affine atlas), the base `Spec k` is affine, and DJ-0's
`quasiCompact_of_surjective` converts a surjection out of a compact space into
quasi-compactness of the structure morphism.

So the whole a-posteriori qc argument is reduced to surjectivity — which is DJ-1's honest
brick and is not supplied here. -/
theorem quasiCompact_of_surjective_from_divScheme (J : Over (Spec (CommRingCat.of k)))
    (abel : DivScheme k A B g r₁ r₂ b₁ b₂ ⟶ J.left)
    (hsurj : Function.Surjective abel.base) :
    QuasiCompact J.hom :=
  quasiCompact_of_surjective abel J.hom hsurj

end Qc

/-! ## DJ-2: the packaging -/

section Package

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
variable {A B : X.CurveDivisor} {g r₁ r₂ : ℕ}
variable {b₁ : Module.Basis (Fin r₁) k ↥(Scheme.divisorSections k B ⊤)}
variable {b₂ : Module.Basis (Fin r₂) k ↥(Scheme.divisorSections k (A + B) ⊤)}

/-- **DJ-2, the packaging** (w4-datj §1.1): the pinned Jacobian datum from a representation
of the degree-zero Picard functor, its locally-of-finite-type certificate, and a
point-surjective morphism from `DivScheme g`.

This is `JacobianData.ofRepresentableBy` with the fourth field replaced by the Abel-image
hypothesis, which is the form the classical construction produces: quasi-compactness of the
Jacobian is *not* structural (its atlas is infinite, §2.1) and has to come from the image
argument. -/
noncomputable def JacobianData.ofAbelImage (J : Over (Spec (.of k)))
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (hlft : LocallyOfFiniteType J.hom)
    (abel : DivScheme k A B g r₁ r₂ b₁ b₂ ⟶ J.left)
    (hsurj : Function.Surjective abel.base) :
    JacobianData C :=
  JacobianData.ofRepresentableBy C J rep hlft
    (quasiCompact_of_surjective_from_divScheme A B g r₁ r₂ b₁ b₂ J abel hsurj)

@[simp]
lemma JacobianData.ofAbelImage_J (J : Over (Spec (.of k)))
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (hlft : LocallyOfFiniteType J.hom)
    (abel : DivScheme k A B g r₁ r₂ b₁ b₂ ⟶ J.left)
    (hsurj : Function.Surjective abel.base) :
    (JacobianData.ofAbelImage C J rep hlft abel hsurj).J = J :=
  rfl

end Package

/-! ## The chart-atlas form -/

section Charts

variable {ι : Type u} {Xc : ι → Scheme.{u}}
variable (f : ∀ i, yoneda.obj (Xc i) ⟶ (pic0SigmaSheaf C).1)
variable (hf : ∀ i, IsOpenImmersion.presheaf (f i))
variable [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
variable {A B : X.CurveDivisor} {g r₁ r₂ : ℕ}
variable {b₁ : Module.Basis (Fin r₁) k ↥(Scheme.divisorSections k B ⊤)}
variable {b₂ : Module.Basis (Fin r₂) k ↥(Scheme.divisorSections k (A + B) ⊤)}

/-- **The atlas producer with the qc field discharged by the Abel image**: the infinite-atlas
producer `JacobianData.ofChartsOfCompactSpace` asks for `CompactSpace` of the glued object,
which §2.1 records as the genuinely a-posteriori input.  This supplies it from a surjection
out of `DivScheme g`, so an atlas plus a surjective Abel map is enough — no finiteness of the
chart index, which the chart index (one chart per divisor class with an effective witness)
does not have. -/
noncomputable def JacobianData.ofChartsOfAbelImage
    (hlft : ∀ i, LocallyOfFiniteType (chartHom C f i))
    (abel : DivScheme k A B g r₁ r₂ b₁ b₂ ⟶ (gluedOfCharts C f hf).left)
    (hsurj : Function.Surjective abel.base) :
    JacobianData C :=
  JacobianData.ofChartsOfCompactSpace C f hf hlft
    (compactSpace_of_surjective abel hsurj)

end Charts

end AlgebraicGeometry
