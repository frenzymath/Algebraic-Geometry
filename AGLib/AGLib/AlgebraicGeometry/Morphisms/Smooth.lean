/-
Copyright (c) 2026 Frenzymath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frenzymath
-/
module

public import AGLib.RingTheory.Smooth.Reduced
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth morphisms are geometrically reduced

A scheme smooth over the spectrum of a field is reduced. Consequently, smooth morphisms of
schemes are geometrically reduced and, when geometrically irreducible, geometrically integral.
The reducedness theorem is the scheme-level form of
[The Stacks Project, Tag 033B][stacks-project], which states that a smooth algebra over a reduced
ring is reduced.

## Main results

* `AlgebraicGeometry.Smooth.isReduced_of_field`
* `AlgebraicGeometry.Smooth.geometricallyReduced`
* `AlgebraicGeometry.SmoothOfRelativeDimension.geometricallyReduced`
* `AlgebraicGeometry.Smooth.geometricallyIntegral`
* `AlgebraicGeometry.SmoothOfRelativeDimension.geometricallyIntegral`

## Provenance

The proofs were audited from the Mathlib-only modules
`MainProjects/AlgebraicJacobian/MilneKollar/AlgebraicJacobian/Curve/GeometricallyReduced.lean`
and
`MainProjects/AlgebraicJacobian/PicardAlbanese/AlgebraicJacobian/Curve/GeometricallyReduced.lean`
at repository commit `9223d85c786394721963a9d642b08d066b72a594`. The source's relative-dimension-one
smoothness instance is intentionally omitted: Mathlib provides the general theorem
`SmoothOfRelativeDimension.smooth`, while choosing one dimension for instance synthesis is not
canonical.
-/

public section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

variable {X Y : Scheme.{u}}

/-- A scheme smooth over the spectrum of a field is reduced.

This is the scheme-level field case of
[The Stacks Project, Tag 033B][stacks-project]. -/
theorem Smooth.isReduced_of_field {K : Type u} [Field K] (f : X ⟶ Spec (.of K)) [Smooth f] :
    IsReduced X := by
  letI : Subsingleton (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  choose U hU V hV hxV e hsm using Smooth.exists_isStandardSmooth f
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

/-- A smooth morphism is geometrically reduced. -/
instance (priority := 100) Smooth.geometricallyReduced (f : X ⟶ Y) [Smooth f] :
    GeometricallyReduced f where
  geometrically_isReduced := fun K _ y Z fst snd h ↦
    have : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h ‹Smooth f›
    Smooth.isReduced_of_field snd

/-- A morphism smooth of relative dimension `n` is geometrically reduced. -/
theorem SmoothOfRelativeDimension.geometricallyReduced (n : ℕ) (f : X ⟶ Y)
    [SmoothOfRelativeDimension n f] : GeometricallyReduced f :=
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  inferInstance

/-- A smooth, geometrically irreducible morphism is geometrically integral. -/
instance (priority := 100) Smooth.geometricallyIntegral (f : X ⟶ Y) [Smooth f]
    [GeometricallyIrreducible f] : GeometricallyIntegral f :=
  .of_geometricallyReduced_of_geometricallyIrreducible f

/-- A geometrically irreducible morphism smooth of relative dimension `n` is geometrically
integral. -/
theorem SmoothOfRelativeDimension.geometricallyIntegral (n : ℕ) (f : X ⟶ Y)
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f] : GeometricallyIntegral f :=
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  .of_geometricallyReduced_of_geometricallyIrreducible f

end AlgebraicGeometry
