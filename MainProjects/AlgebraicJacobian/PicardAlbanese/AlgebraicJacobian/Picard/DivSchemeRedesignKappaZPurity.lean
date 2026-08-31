/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignKappaZFibre
import AlgebraicJacobian.Picard.DivSchemeRedesignRangeFlatBridge
import AlgebraicJacobian.Picard.DivSchemeRedesignChartReadIdeal

/-!
# Conditional purity for the sharp `κ(z)` inclusion

The chart-colength module is the image of the genuine chart-reading ideal `J` in
`B/(read s)`.  This file records the exact quotient sequence used to obtain its
residue-fibre injectivity.  The only flatness premise is the explicitly stronger
`B`-module statement `Flat B (B/J)`; no inference from multiplication persistence
or from base-flatness is made.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}

namespace ThetaGeneratorSeed

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 600000 in
/-- **Conditional sharp-fibre injectivity.**  Put `B = Γ(V)`,
`J = chartReadIdeal K b`, and `I = (read s)`.  If `s ∈ K` (so `I ≤ J`) and
`B/J` is flat as a `B`-module, then the residue-fibre inclusion
`chartColengthModule K b s ↪ B/I` is injective at every chart prime.

This is the exact short-exact-sequence consequence
`0 → (J + I)/I → B/I → B/J → 0`; it is a conditional theorem and does not assert
that the universal seed satisfies the `B`-flat premise. -/
theorem chartColengthModule_subtype_rTensor_injective_of_flat_chartIdeal_quotient
    (K : Submodule R (relThetaSections C R π a)) (b : Bool)
    (s : relThetaSections C R π a) (hs : s ∈ K)
    [Module.Flat
      Γ(relCurve C R, relPinnedChart C R π b)
      (Γ(relCurve C R, relPinnedChart C R π b) ⧸ chartReadIdeal K b)]
    (p : PrimeSpectrum Γ(relCurve C R, relPinnedChart C R π b)) :
    Function.Injective
      ((chartColengthModule K b s).subtype.rTensor p.asIdeal.ResidueField) := by
  let B : Type u := Γ(relCurve C R, relPinnedChart C R π b)
  let I : Ideal B := Ideal.span {relThetaResSide a b le_rfl s}
  let J : Ideal B := chartReadIdeal K b
  have hIJ : I ≤ J := by
    change Ideal.span {relThetaResSide a b le_rfl s} ≤
      Ideal.span (Set.range (chartReadMap K b))
    refine Ideal.span_le.2 ?_
    intro x hx
    rcases hx with rfl
    exact Ideal.subset_span ⟨⟨s, hs⟩, rfl⟩
  have hflat : Module.Flat B (B ⧸ J) := by
    simpa only [B, J] using (inferInstance :
      Module.Flat
        Γ(relCurve C R, relPinnedChart C R π b)
        (Γ(relCurve C R, relPinnedChart C R π b) ⧸ chartReadIdeal K b))
  have hinjImage : Function.Injective
      ((FlatRangeBridge.imageInQuotient (R := B) (M := B)
        I J).subtype.rTensor
          p.asIdeal.ResidueField) := by
    letI : Module.Flat B (B ⧸ J) := hflat
    have hL : (I : Submodule B B) ≤ J := hIJ
    have hL' := FlatRangeBridge.imageInQuotient_lTensor_injective_of_flat_quotient
      (R := B) (M := B) hL p.asIdeal.ResidueField
    exact ((FlatRangeBridge.imageInQuotient I J).subtype.lTensor_inj_iff_rTensor_inj
        p.asIdeal.ResidueField).mp hL'
  have hEq : FlatRangeBridge.imageInQuotient (R := B) (M := B)
      I J =
      chartColengthModule K b s := by
    change chartIdealColengthModule K b s = chartColengthModule K b s
    exact chartIdealColengthModule_eq_chartColengthModule K b s
  rw [← hEq]
  exact hinjImage

/-- The same sharp-fibre injectivity with the standard semantic name for the premise:
`Ideal.Pure J` means precisely that `B ⧸ J` is flat as a `B`-module. -/
theorem chartColengthModule_subtype_rTensor_injective_of_pure_chartIdeal
    (K : Submodule R (relThetaSections C R π a)) (b : Bool)
    (s : relThetaSections C R π a) (hs : s ∈ K)
    [Ideal.Pure (chartReadIdeal K b)]
    (p : PrimeSpectrum Γ(relCurve C R, relPinnedChart C R π b)) :
    Function.Injective
      ((chartColengthModule K b s).subtype.rTensor p.asIdeal.ResidueField) :=
  chartColengthModule_subtype_rTensor_injective_of_flat_chartIdeal_quotient K b s hs p

end ThetaGeneratorSeed

end AlgebraicGeometry
