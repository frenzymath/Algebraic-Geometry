/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneLocalDivisor

/-!
# Affine evaluation-divisor coherence for the FibrePresented producer

The arbitrary-scheme `PicRankOneOpen.FibrePresented` producer needs a divisor cut by the
canonical evaluation section which is stable under restriction of affine test schemes.  This
file records two construction-level inputs for that gluing step:

* `datumSectionBaseChange_tower` proves that the tied datum section itself is coherent along
  every affine coefficient tower;
* `baseOpenRankOneDivisor_mul_eq` proves independence of the chosen rank-one generator after
  passing to a pairwise product open.

The remaining gluing edge is deliberately explicit: one must identify `DivFamZarAff.mapAlg` of
the local divisor with the divisor cut by the tower-transported section.  No
`PicRankOneOpen.FibrePresented` or pullback-square hypothesis is introduced here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {A : Type u} [CommRing A] [Algebra k A]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}

namespace PicRankOneLocalPresentation

/-- The actual section attached to a tied presentation is transitive under arbitrary affine
coefficient extension.  The cast is along the canonical equality between iterated and direct
base change of the same cocycle datum. -/
theorem datumSectionBaseChange_tower
    (P : PicRankOneLocalPresentation pi lam)
    (B : Type u) [CommRing B] [Algebra k B] [Algebra P.cover.Carrier B]
    [IsScalarTower k P.cover.Carrier B]
    (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra P.cover.Carrier B']
    [Algebra B B'] [IsScalarTower k P.cover.Carrier B'] [IsScalarTower k B B']
    [IsScalarTower P.cover.Carrier B B']
    (y : Sheaf.HModule P.datum.sheaf 0) :
    let hD : (P.datum.baseChange B).baseChange B' = P.datum.baseChange B' :=
      P.datum.baseChange_baseChange C P.cover.Carrier B B'
    cast (congrArg (fun E : BasicOpenCocycleDatum C B' pi =>
      ↑(gluedSubmodule B' E.pieces E.unit ⊤)) hD)
        ((P.datum.baseChange B).sectionsMapTop B'
          (P.datumSectionBaseChange B y)) =
      P.datumSectionBaseChange B' y := by
  rw [P.datumSectionBaseChange_one_tmul B y,
    P.datumSectionBaseChange_one_tmul B' y]
  exact P.datum.sectionsMapTop_tower
    C P.cover.Carrier B B' (P.datumSection y)

/-- A generator which is fibrewise nonzero on `D(f)` remains so on `D(f * g)`. -/
theorem generator_nonzero_on_mul_left
    (P : PicRankOneLocalPresentation pi lam)
    (f g : P.cover.Carrier)
    (y : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0) :
    ∀ p : PrimeSpectrum P.cover.Carrier, f * g ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0 := by
  intro p hfg
  exact hy p fun hf => hfg (p.asIdeal.mul_mem_right g hf)

/-- A generator which is fibrewise nonzero on `D(g)` remains so on `D(f * g)`. -/
theorem generator_nonzero_on_mul_right
    (P : PicRankOneLocalPresentation pi lam)
    (f g : P.cover.Carrier)
    (y : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, g ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0) :
    ∀ p : PrimeSpectrum P.cover.Carrier, f * g ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0 := by
  intro p hfg
  exact hy p fun hg => hfg (p.asIdeal.mul_mem_left f hg)

/-- Local evaluation divisors cut by two rank-one generators agree on the direct pairwise
product open.  This is the generator-independence half of the compatibility premise required
by `divFamZarAff.exists_glue_of_basic_compat`. -/
theorem baseOpenRankOneDivisor_mul_eq
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier]
    (f g : P.cover.Carrier)
    (y y' : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0)
    (hy' : ∀ p : PrimeSpectrum P.cover.Carrier, g ∉ p.asIdeal →
      (y' ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0) :
    P.baseOpenRankOneDivisor (f * g) y
        (P.generator_nonzero_on_mul_left f g y hy) =
      P.baseOpenRankOneDivisor (f * g) y'
        (P.generator_nonzero_on_mul_right f g y' hy') :=
  P.baseOpenRankOneDivisor_eq (f * g) y y'
    (P.generator_nonzero_on_mul_left f g y hy)
    (P.generator_nonzero_on_mul_right f g y' hy')

end PicRankOneLocalPresentation

end AlgebraicGeometry
