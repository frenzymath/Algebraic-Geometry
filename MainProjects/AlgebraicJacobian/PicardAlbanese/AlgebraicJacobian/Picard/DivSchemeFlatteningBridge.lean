/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.SupportTubeFinite

/-!
# Finite-presentation bridge for flattening the chart-reading quotient

The universal flattening-stratification theorem works with a finitely presented module
sheaf on a Noetherian base.  The genuine chart-reading quotient is initially presented as
an affine chart-ring quotient.  This file records the two formal conversions needed to
connect those descriptions:

* a quotient which is finite over a Noetherian base is finitely presented over that base;
* the `tilde` sheaf of a finitely presented module is a finitely presented module sheaf.

Together with `IsAffineOpen.finite_quotient_of_isClosed`, this packages a chart quotient
as an admissible input to the old flattening-stratification route.  The geometric
closed-support/no-leak hypothesis remains explicit: this bridge does not assert it for the
universal chart-reading ideal.
-/

set_option autoImplicit false

universe u u₁ u₂ v₁ v₂

open CategoryTheory Limits Opposite

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{u}}
variable [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
variable {S : Sheaf J' RingCat.{u}}
variable [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
variable [J'.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/-- Mapping a finite presentation along a colimit-preserving functor preserves the
finite generator and relation index types. -/
instance Presentation.map_isFinite {M : SheafOfModules.{u} R} (P : Presentation M)
    (F : CategoryTheory.Functor (SheafOfModules.{u} R) (SheafOfModules.{u} S))
    [PreservesColimitsOfSize.{u, u} F] (η : unit S ≅ F.obj (unit R))
    [P.IsFinite] : (P.map F η).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite P.generators.I)⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite P.relations.I)⟩

end SheafOfModules

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace FlatteningBridge

set_option backward.isDefEq.respectTransparency false in
/-- The sheaf associated to a finitely presented module is finitely presented. -/
theorem tilde_isFinitePresentation_of_module
    {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.FinitePresentation (R : Type u) M] :
    (tilde M).IsFinitePresentation := by
  classical
  obtain ⟨s, hs, hker⟩ :=
    (inferInstance : Module.FinitePresentation (R : Type u) M)
  obtain ⟨t, ht⟩ := hker
  let P : (tilde M).Presentation :=
    presentationTilde M (s : Set M) hs (t : Set (s →₀ (R : Type u))) ht
  haveI hPgen : P.generators.IsFiniteType :=
    { finite := Set.Finite.to_subtype s.finite_toSet }
  haveI hPrel : P.relations.IsFiniteType :=
    { finite := Set.Finite.to_subtype t.finite_toSet }
  haveI hP : P.IsFinite :=
    SheafOfModules.Presentation.IsFinite.mk.{u, u, u} hPgen hPrel
  let q := P.quasicoherentData
  have hq : q.IsFinitePresentation := by
    apply SheafOfModules.QuasicoherentData.IsFinitePresentation.mk
    intro i
    dsimp [q, SheafOfModules.Presentation.quasicoherentData]
    infer_instance
  exact SheafOfModules.IsFinitePresentation.mk.{u, u, u}
    (M := tilde M) ⟨q, hq⟩

end FlatteningBridge

namespace IsAffineOpen

variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable [X.Over (Spec (CommRingCat.of R))]

include hV in
/-- A chart quotient with closed support in a proper finite-type ambient scheme is
finitely presented over a Noetherian base. -/
theorem finitePresentation_quotient_of_isClosed
    [UniversallyClosed (X ↘ Spec (CommRingCat.of R))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of R))]
    (I : Ideal Γ(X, V))
    (hclosed : IsClosed (X.zeroLocus (I : Set Γ(X, V)) ∩ (V : Set X))) :
    Module.FinitePresentation R (Γ(X, V) ⧸ I) := by
  haveI : Module.Finite R (Γ(X, V) ⧸ I) :=
    hV.finite_quotient_of_isClosed I hclosed
  exact Module.finitePresentation_of_finite R _

/-- The `Spec R` module sheaf attached to an affine chart quotient. -/
noncomputable def quotientTilde (_hV : IsAffineOpen V) (I : Ideal Γ(X, V)) :
    (Spec (CommRingCat.of R)).Modules :=
  tilde (ModuleCat.of R (Γ(X, V) ⧸ I))

/-- The chart quotient packaged as a finitely presented module sheaf, the exact input
shape required by a flattening stratification on `Spec R`. -/
theorem quotientTilde_isFinitePresentation_of_isClosed
    [UniversallyClosed (X ↘ Spec (CommRingCat.of R))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of R))]
    (I : Ideal Γ(X, V))
    (hclosed : IsClosed (X.zeroLocus (I : Set Γ(X, V)) ∩ (V : Set X))) :
    (quotientTilde (R := R) hV I).IsFinitePresentation := by
  letI : Module.FinitePresentation R (Γ(X, V) ⧸ I) :=
    hV.finitePresentation_quotient_of_isClosed I hclosed
  exact FlatteningBridge.tilde_isFinitePresentation_of_module
    (R := CommRingCat.of R)
    (ModuleCat.of R (Γ(X, V) ⧸ I))

end IsAffineOpen

end AlgebraicGeometry
