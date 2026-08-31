/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneFibrePresentedProducerSectionDivEq
import AlgebraicJacobian.Picard.DivisorFamilyAffMapAlg
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveH0BaseChange
import AlgebraicJacobian.Curve.BaseChangeInstances

/-!
# Fibre nonvanishing of a datum section cutting a certified divisor

A glued section of a `BasicOpenCocycleDatum` whose cut local equations are `DivEq` to an
honest widened certified divisor (`IsLocallyCertifiedAff (genus C)`) cannot vanish on any
residue-field fibre of the base.

The route is by contradiction.  If the compared section `D.sectionsMapTop κ(q) s` were
zero, every base-changed component would vanish, so the `relCurveMap`-pullback of every cut
equation to the fibre curve over `κ(q)` would be the zero section.  But the certificate's
regularity engine (`IsLocallyCertifiedAff.germ_pullbackEqn_mem_nonZeroDivisors`, an
arbitrary-test-tower statement with no Noetherian hypothesis) makes the pulled equations of
the certified representative regular, and regularity transports across the `DivEq` to the
section-cut equations (`germ_pullbackEqn_mem_nonZeroDivisors_of_divEq`).  The fibre curve
is integral, hence nonempty with nontrivial (local) stalks, and `0` is never a
nonzerodivisor in a nontrivial ring — contradiction.

The immediate consumer (`tmul_residueField_ne_zero_of_divEq_certified`) restates the
conclusion in the tensor form `y ⊗ₜ 1 ≠ 0` in `H⁰ ⊗ κ(q)` consumed by the rank-one
unit-extraction engine (`Module.exists_notMem_bijective_toSpanSingleton`,
`Module.exists_notMem_smul_eq_of_tmul_ne_zero` in `DivisorFamilyMonoH1.lean`), through the
datum `H⁰` base-change bridge `linearEquiv₀_datumH0BaseChange_one_tmul`.
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
variable {B : Type u} [CommRing B] [Algebra k B]
variable {pi : C.left ⟶ P1 k}

namespace BasicOpenCocycleDatum

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] in
/-- The components of the zero glued section are zero. -/
private lemma component_zero [IsAffineHom pi] {B' : Type u} [CommRing B'] [Algebra k B']
    (E : BasicOpenCocycleDatum C B' pi) (j : E.index) :
    E.component (0 : ↥(gluedSubmodule B' E.pieces E.unit ⊤)) j = 0 := by
  unfold BasicOpenCocycleDatum.component
  rw [ZeroMemClass.coe_zero, Pi.zero_apply, map_zero]

/-- **Fibre nonvanishing of a datum section cutting a certified divisor**: if the local
equations cut by a germ-regular glued section of the datum are divisor-equal to a widened
locally certified system of degree `genus C`, then the compared section is nonzero on every
residue-field fibre of the base.

By contradiction: vanishing at `q` makes every pulled cut equation the zero section of the
fibre curve, while the certificate makes the pulled equations regular — and `0` is never a
nonzerodivisor in the nontrivial stalks of the integral fibre curve. -/
theorem sectionsMapTop_ne_zero_of_divEq_certified [IsAffineHom pi]
    (D : BasicOpenCocycleDatum C B pi)
    (s : ↥(gluedSubmodule B D.pieces D.unit ⊤))
    (𝒲 : (relCurve C B).PointedCover) (σ : relCurve C B → D.index)
    (hσ : ∀ x : relCurve C B, 𝒲.opens x ≤ D.pieces (σ x))
    (hreg : ∀ (j : D.index) (x : relCurve C B) (hx : x ∈ D.pieces j),
      ((relCurve C B).presheaf.germ (D.pieces j) x hx).hom (D.component s j)
        ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk x))
    {d : (relCurve C B).LocalEquations}
    (hd : IsLocallyCertifiedAff (genus C) d)
    (hdiv : Scheme.LocalEquations.DivEq (D.sectionLocalEquations s 𝒲 σ hσ hreg) d)
    (q : PrimeSpectrum B) :
    D.sectionsMapTop q.asIdeal.ResidueField s ≠ 0 := by
  intro hzero
  haveI : IsIntegral (relCurve C q.asIdeal.ResidueField) :=
    instIsIntegralBaseChange C q.asIdeal.ResidueField
  set e := D.sectionLocalEquations s 𝒲 σ hσ hreg with he
  set f := relCurveMap C B q.asIdeal.ResidueField with hf
  -- regularity of the pulled certified equations, transported across the `DivEq`
  have hereg := Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_divEq
    f hdiv.symm (hd.germ_pullbackEqn_mem_nonZeroDivisors q.asIdeal.ResidueField (genus C))
  -- a point of the nonempty integral fibre curve
  obtain ⟨z⟩ := IsIntegral.nonempty (X := relCurve C q.asIdeal.ResidueField)
  have hz := hereg z z ((e.cover.pullback f).mem_opens z)
  -- the pulled cut equation at `z` is the zero section
  have hcomp0 : D.toBasicOpenCoverData.piecesMap q.asIdeal.ResidueField (σ (f.base z))
      (D.component s (σ (f.base z))) = 0 := by
    rw [← D.component_sectionsMapTop q.asIdeal.ResidueField s (σ (f.base z)), hzero,
      component_zero]
  have hval : relAffSectionsMap C q.asIdeal.ResidueField (D.pieces (σ (f.base z)))
      (D.component s (σ (f.base z))) = 0 := by
    rw [← D.resHom_piecesMap_eq_relAffSectionsMap q.asIdeal.ResidueField (σ (f.base z))
      (D.component s (σ (f.base z))), hcomp0, map_zero]
  have happ := Scheme.Hom.appLE_resHom f (hσ (f.base z))
    (le_rfl : f ⁻¹ᵁ D.pieces (σ (f.base z)) ≤ f ⁻¹ᵁ D.pieces (σ (f.base z)))
    (le_rfl : f ⁻¹ᵁ 𝒲.opens (f.base z) ≤ f ⁻¹ᵁ 𝒲.opens (f.base z))
    (Scheme.Hom.preimage_mono f (hσ (f.base z)))
    (D.component s (σ (f.base z)))
  have heqn0 : Scheme.LocalEquations.pullbackEqn f e z = 0 := by
    calc Scheme.LocalEquations.pullbackEqn f e z
        = (relCurve C q.asIdeal.ResidueField).resHom
            (Scheme.Hom.preimage_mono f (hσ (f.base z)))
            (relAffSectionsMap C q.asIdeal.ResidueField (D.pieces (σ (f.base z)))
              (D.component s (σ (f.base z)))) := happ.symm
      _ = 0 := by rw [hval, map_zero]
  rw [heqn0, map_zero] at hz
  exact zero_notMem_nonZeroDivisors hz

set_option maxHeartbeats 1600000 in
-- Matching the compared section against the datum `H⁰` base-change bridge unfolds the
-- dependent glued-sheaf carriers; the sibling H0 base-change files need the same budget.
/-- **The tensor-form consumer corollary** (the unit-extraction enabler): a datum `H⁰`
class whose glued section cuts equations divisor-equal to a certified divisor of degree
`genus C` has nonzero image in every residue-field fibre `H⁰ ⊗ κ(q)` — exactly the
hypothesis shape of `Module.exists_notMem_bijective_toSpanSingleton` and
`Module.exists_notMem_smul_eq_of_tmul_ne_zero` (`DivisorFamilyMonoH1.lean`). -/
theorem tmul_residueField_ne_zero_of_divEq_certified [IsFinite pi]
    (D : BasicOpenCocycleDatum C B pi)
    (hH1 : Subsingleton (datumPair D).H1)
    (y : Sheaf.HModule D.sheaf 0)
    (𝒲 : (relCurve C B).PointedCover) (σ : relCurve C B → D.index)
    (hσ : ∀ x : relCurve C B, 𝒲.opens x ≤ D.pieces (σ x))
    (hreg : ∀ (j : D.index) (x : relCurve C B) (hx : x ∈ D.pieces j),
      ((relCurve C B).presheaf.germ (D.pieces j) x hx).hom
        (D.component (Sheaf.HModule.linearEquiv₀
          (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
          isTerminalTop D.sheaf y) j)
        ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk x))
    {d : (relCurve C B).LocalEquations}
    (hd : IsLocallyCertifiedAff (genus C) d)
    (hdiv : Scheme.LocalEquations.DivEq
      (D.sectionLocalEquations
        (Sheaf.HModule.linearEquiv₀
          (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
          isTerminalTop D.sheaf y) 𝒲 σ hσ hreg) d)
    (q : PrimeSpectrum B) :
    (y ⊗ₜ[B] (1 : q.asIdeal.ResidueField) :
      Sheaf.HModule D.sheaf 0 ⊗[B] q.asIdeal.ResidueField) ≠ 0 := by
  intro hy
  have h1 : ((1 : q.asIdeal.ResidueField) ⊗ₜ[B] y :
      q.asIdeal.ResidueField ⊗[B] Sheaf.HModule D.sheaf 0) = 0 := by
    have h := congrArg
      (TensorProduct.comm B (Sheaf.HModule D.sheaf 0) q.asIdeal.ResidueField) hy
    simpa using h
  refine D.sectionsMapTop_ne_zero_of_divEq_certified _ 𝒲 σ hσ hreg hd hdiv q ?_
  rw [← D.linearEquiv₀_datumH0BaseChange_one_tmul q.asIdeal.ResidueField hH1 y, h1,
    map_zero, map_zero]

end BasicOpenCocycleDatum

end AlgebraicGeometry
