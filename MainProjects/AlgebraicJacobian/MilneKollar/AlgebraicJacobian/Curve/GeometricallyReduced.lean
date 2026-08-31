/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Unramified.Field

/-!
# Smooth morphisms are geometrically reduced

A smooth morphism of schemes is geometrically reduced: every base change to the spectrum of a
field is reduced. Combined with geometric irreducibility, this upgrades the standing hypotheses
of the Jacobian challenge (`SmoothOfRelativeDimension 1 C.hom` and
`GeometricallyIrreducible C.hom`) to `GeometricallyIntegral C.hom`, which is what all the
actual geometry of the project consumes.

The commutative-algebra core is that a standard smooth algebra over a domain is reduced. By the
structure theorem for standard smooth algebras (Stacks 00T7,
`RingHom.IsStandardSmooth.exists_etale_mvPolynomial`), such an algebra `S` is étale over a
polynomial ring `P` over the base. Since `S` is flat over the domain `P`, it embeds into
`Frac(P) ⊗[P] S`, which is formally unramified and essentially of finite type over the field
`Frac(P)`, hence reduced by `Algebra.FormallyUnramified.isReduced_of_field`.

## Main results

* `Algebra.FormallyUnramified.isReduced_of_isDomain`: a flat, formally unramified algebra,
  essentially of finite type over a domain, is reduced.
* `Algebra.Etale.isReduced_of_isDomain`, `RingHom.IsStandardSmooth.isReduced_of_isDomain`,
  `Algebra.IsStandardSmooth.isReduced_of_isDomain`: étale/standard smooth algebras over
  domains are reduced.
* `AlgebraicGeometry.Smooth.isReduced_of_field`: a scheme smooth over `Spec` of a field is
  reduced.
* `AlgebraicGeometry.Smooth.geometricallyReduced`: a smooth morphism is geometrically reduced
  (instance), together with the `SmoothOfRelativeDimension` variant.
* `AlgebraicGeometry.Smooth.geometricallyIntegral`: a smooth, geometrically irreducible
  morphism is geometrically integral (instance), together with the
  `SmoothOfRelativeDimension` variant.

This file is written in mathlib generality and is a candidate for upstreaming. It was
developed in the sibling project `Algebraic-Jacobian-Challenge-Rebuild`
(`AlgebraicJacobian/Curve/GeometricallyReduced.lean`) and imported here unchanged; it
depends on Mathlib only, so the two copies can be kept in step by file copy until one
of them is upstreamed.

In this project it closes the geometric-integrality half of the headline's hypothesis
gap: `AlgebraicGeometry.genus` and `AlgebraicGeometry.Jacobian` are stated for a
smooth proper **geometrically irreducible** curve, while the Picard/FGA development
runs under `GeometricallyIntegral`. `Smooth.geometricallyIntegral` bridges the two, so
the only remaining hypothesis gap at the headline is the `k`-rational point, which is a
genuine mathematical gap rather than missing infrastructure (see
`AlgebraicJacobian/Jacobian.lean`, leaf `hasRationalPoint_of_curve`).
-/

set_option autoImplicit false

universe u

open TensorProduct

section RingTheory

/-- A flat, formally unramified algebra, essentially of finite type over a domain, is reduced.
This generalizes `Algebra.FormallyUnramified.isReduced_of_field` from fields to domains, at the
price of the flatness assumption (which is automatic over a field). -/
theorem Algebra.FormallyUnramified.isReduced_of_isDomain (B S : Type*) [CommRing B] [CommRing S]
    [IsDomain B] [Algebra B S] [Algebra.FormallyUnramified B S] [Algebra.EssFiniteType B S]
    [Module.Flat B S] : IsReduced S := by
  have : IsReduced (FractionRing B ⊗[B] S) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing B) (FractionRing B ⊗[B] S)
  refine isReduced_of_injective
    (Algebra.TensorProduct.includeRight (R := B) (A := FractionRing B) (B := S)) ?_
  have h : ⇑(Algebra.TensorProduct.includeRight (R := B) (A := FractionRing B) (B := S)) =
      ⇑(LinearMap.rTensor S (Algebra.ofId B (FractionRing B)).toLinearMap) ∘
        ⇑(TensorProduct.lid B S).symm := by
    ext s
    simp
  rw [h]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _
    (IsFractionRing.injective B (FractionRing B))).comp (TensorProduct.lid B S).symm.injective

/-- An étale algebra over a domain is reduced. -/
theorem Algebra.Etale.isReduced_of_isDomain (B S : Type*) [CommRing B] [CommRing S] [IsDomain B]
    [Algebra B S] [Algebra.Etale B S] : IsReduced S :=
  Algebra.FormallyUnramified.isReduced_of_isDomain B S

/-- The target of a standard smooth ring homomorphism out of a domain is reduced: by
Stacks 00T7 it is étale over a polynomial ring over the base, and étale algebras over
domains are reduced. -/
theorem RingHom.IsStandardSmooth.isReduced_of_isDomain {B S : Type*} [CommRing B] [CommRing S]
    [IsDomain B] {g : B →+* S} (hg : g.IsStandardSmooth) : IsReduced S := by
  obtain ⟨n, φ, -, hφ⟩ := hg.exists_etale_mvPolynomial
  algebraize [φ]
  exact Algebra.Etale.isReduced_of_isDomain (MvPolynomial (Fin n) B) S

/-- A standard smooth algebra over a domain is reduced. -/
theorem Algebra.IsStandardSmooth.isReduced_of_isDomain (B S : Type*) [CommRing B] [CommRing S]
    [IsDomain B] [Algebra B S] [Algebra.IsStandardSmooth B S] : IsReduced S :=
  (RingHom.isStandardSmooth_algebraMap.mpr ‹_›).isReduced_of_isDomain

end RingTheory

namespace AlgebraicGeometry

open CategoryTheory Limits

variable {X Y : Scheme.{u}}

/-- A scheme smooth over the spectrum of a field is reduced. -/
theorem Smooth.isReduced_of_field {K : Type u} [Field K] (f : X ⟶ Spec (.of K)) [Smooth f] :
    IsReduced X := by
  have hsub : Subsingleton (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  choose U hU V hV hxV e hsm using Smooth.exists_isStandardSmooth f
  -- Each chart is the spectrum of a standard smooth algebra over (a ring isomorphic to) `K`,
  -- hence reduced.
  have hred (x : X) : IsReduced (V x).toScheme := by
    have : IsAffine (V x).toScheme := hV x
    have hfx : f x ∈ U x := e x (hxV x)
    have hUx : U x = ⊤ := by
      refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y ↦ ?_)
      exact Subsingleton.elim (f x) y ▸ hfx
    have hdom : IsDomain Γ(Spec (CommRingCat.of K), U x) := by
      rw [hUx]
      exact Function.Injective.isDomain
        (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv (RingEquiv.injective _)
    have hΓ : _root_.IsReduced Γ(X, V x) := (hsm x).isReduced_of_isDomain
    have : _root_.IsReduced Γ((V x).toScheme, ⊤) :=
      isReduced_of_injective (V x).topIso.commRingCatIsoToRingEquiv (RingEquiv.injective _)
    exact isReduced_of_isAffine_isReduced _
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers X (fun x ↦ (V x).toScheme) (fun x ↦ (V x).ι)
    (fun x ↦ ⟨x, ⟨x, hxV x⟩, rfl⟩) (fun x ↦ inferInstance)
  have : ∀ i, IsReduced (𝒰.X i) := hred
  exact IsReduced.of_openCover _ 𝒰

/-- A smooth morphism of schemes is geometrically reduced: every base change to the spectrum
of a field is smooth over that field, hence reduced. -/
instance (priority := 100) Smooth.geometricallyReduced (f : X ⟶ Y) [Smooth f] :
    GeometricallyReduced f where
  geometrically_isReduced := fun K _ y Z fst snd h ↦
    have : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h ‹Smooth f›
    Smooth.isReduced_of_field snd

/-- A morphism smooth of relative dimension `1` is smooth. This is the relative dimension of
the curve bundle of the Jacobian challenge; the general statement is
`SmoothOfRelativeDimension.smooth`, which cannot be an instance since `n` does not occur in
the conclusion. -/
instance (priority := 100) Smooth.of_smoothOfRelativeDimension_one (f : X ⟶ Y)
    [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f

/-- A morphism smooth of some relative dimension is geometrically reduced. Not an instance
since `n` cannot be inferred from the conclusion; for relative dimension `1`, instance
resolution goes through `Smooth.of_smoothOfRelativeDimension_one`. -/
theorem SmoothOfRelativeDimension.geometricallyReduced (n : ℕ) (f : X ⟶ Y)
    [SmoothOfRelativeDimension n f] : GeometricallyReduced f :=
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  inferInstance

/-- A smooth, geometrically irreducible morphism is geometrically integral. -/
instance (priority := 100) Smooth.geometricallyIntegral (f : X ⟶ Y) [Smooth f]
    [GeometricallyIrreducible f] : GeometricallyIntegral f :=
  .of_geometricallyReduced_of_geometricallyIrreducible f

/-- A geometrically irreducible morphism, smooth of some relative dimension, is geometrically
integral. Not an instance since `n` cannot be inferred from the conclusion. -/
theorem SmoothOfRelativeDimension.geometricallyIntegral (n : ℕ) (f : X ⟶ Y)
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f] : GeometricallyIntegral f :=
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  .of_geometricallyReduced_of_geometricallyIrreducible f

section CurveBundle

/-! Instance-resolution smoke tests for the hypothesis bundle of the Jacobian challenge
(the `IsProper` hypothesis is omitted as it plays no role here): the curve `C` is
geometrically reduced and geometrically integral, by `inferInstance`. -/

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]

example : GeometricallyReduced C.hom := inferInstance
example : GeometricallyIntegral C.hom := inferInstance

end CurveBundle

end AlgebraicGeometry
