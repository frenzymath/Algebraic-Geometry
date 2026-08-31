/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafEngine
import AlgebraicJacobian.Cohomology.RelativeH1BaseChange

/-!
# The fibre steps of the W6-full discharge chain (DAT-3, steps (a) and (b))

The first two links of the §3.1 discharge chain of `informal/w4-datum-worksheet.md`, at
a fibre `p` of the test ring `B`, for the pinned cocycle datum
`D : BasicOpenCocycleDatum C B π`:

* **(a), the right-exactness half** — `TwoLatticePair.h1BaseChangeEquiv`: for any
  two-lattice pair `P` over `R` and any `R`-algebra `A`, base change of `H¹` is the
  cokernel of the base-changed Čech differential,
  `A ⊗[R] H¹(P) ≃ₗ[A] (A ⊗[R] N) ⧸ range (P.diff.baseChange A)` (right-exactness of
  `A ⊗[R] -` through the landed `LinearMap.quotRangeBaseChangeEquiv`); on the datum at
  `A := κ(p)` this is `datum_subsingleton_h1_residueField_tensor_iff`, the engine's
  complex-form fibre hypothesis `hfib` as a vanishing condition on the base-changed
  complex.

  **Seam (recorded, BINDING note)**: the second half of step (a) — identifying
  `range (diff.baseChange κ(p))` inside the fibre datum's own overlap module through
  the m-chart term identifications (the mirrors of `relTwistTermBaseChange₀/₁`,
  `relTwistOverlapBaseChange`) — is DAT-1 stage (1d-ii). The residue-field
  comparison this file used to await is LANDED:
  `BasicOpenCocycleDatum.subsingleton_h1_residueField_tensor_of_witness`
  (`AlgebraicJacobian.Cohomology.GluedSheafDatumFibre`) with its theta-ideal
  instantiation `thetaIdealDatum_hfib_of_witness`
  (`AlgebraicJacobian.Picard.DivisorThetaFibre`). The statements here are deliberately
  phrased against the abstract base-changed complex so those clauses plug in without
  restating anything.

* **(b)** — `datumH1Equiv`: the degree-one cohomology of the datum's glued sheaf is
  `H¹` of the datum pair, `Sheaf.HModule D.sheaf 1 ≃ₗ[B] (datumPair D).H1` — the landed
  `TwoCoverPairData.h1Equiv` instantiated on the datum's pair data. At a field
  `B := κ(p)` (the fibre datum, once stage (1d-ii) provides it) this is exactly the
  step (b) identification `H¹(pair over κ(p)) ≃ H¹(fibre glued sheaf)`; combined with
  the DAT-3 core (`RiemannRoch/GluedDivisorSheaf.lean`) and FLV it discharges `hfib`
  in the sheaf form.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite

open scoped TensorProduct

/-! ## (a), abstract half: `H¹` of a two-lattice pair after base change -/

namespace TwoLatticePair

variable {R : Type u} [CommRing R]
variable {M₀ M₁ N : Type u}
variable [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup N]
variable [Module R M₀] [Module R M₁] [Module R N]
variable (P : TwoLatticePair R M₀ M₁ N)
variable (A : Type u) [CommRing A] [Algebra R A]

/-- **`H¹` base change, right-exactness half** (step (a) of the W6-full chain,
worksheet §3.1): for a two-lattice pair `P` over `R` and an `R`-algebra `A`, the base
change of `H¹(P) = N ⧸ range δ` is the cokernel of the base-changed Čech differential,
`A`-linearly. Pure right-exactness of `A ⊗[R] -`
(`LinearMap.quotRangeBaseChangeEquiv`); the identification of the base-changed complex
with the complex of the base-changed datum is the DAT-1 stage (1d-ii) seam. -/
noncomputable def h1BaseChangeEquiv :
    A ⊗[R] P.H1 ≃ₗ[A] (A ⊗[R] N) ⧸ LinearMap.range (P.diff.baseChange A) :=
  (LinearEquiv.baseChange R A P.H1 (N ⧸ LinearMap.range P.diff)
    (Submodule.quotEquivOfEq P.imageLattice (LinearMap.range P.diff)
      P.range_diff_eq.symm)).trans
    (LinearMap.quotRangeBaseChangeEquiv A P.diff)

/-- **The complex-form fibre criterion** (step (a), `Subsingleton` form, in the
`H¹ ⊗[R] A` spelling the engine's `hfib` consumes): the fibre of `H¹` at `A` vanishes
iff the cokernel of the base-changed Čech differential does. -/
theorem subsingleton_h1_rTensor_iff :
    Subsingleton (P.H1 ⊗[R] A) ↔
      Subsingleton ((A ⊗[R] N) ⧸ LinearMap.range (P.diff.baseChange A)) := by
  rw [(TensorProduct.comm R P.H1 A).toEquiv.subsingleton_congr,
    (P.h1BaseChangeEquiv A).toEquiv.subsingleton_congr]

end TwoLatticePair

/-! ## The datum instantiations -/

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable (D : BasicOpenCocycleDatum C B π)

/-- **(b) The `H¹` carrier of the datum's glued sheaf**: degree-one cohomology of the
glued sheaf of the pinned cocycle datum is `H¹` of the datum pair — the landed
`Scheme.TwoCoverPairData.h1Equiv` fired on `D.pairData`. Instantiated at a field
`B := κ(p)` (the fibre datum of DAT-1 stage (1d-ii)), this is step (b) of the W6-full
discharge chain: `H¹(pair over κ(p)) ≃ Sheaf.HModule (fibre glued sheaf) 1`. -/
noncomputable def datumH1Equiv :
    Sheaf.HModule D.sheaf 1 ≃ₗ[B] (datumPair D).H1 :=
  D.pairData.h1Equiv (relCover_isAffineOpen₀ C B (fiberTwoCover π))
    (relCover_isAffineOpen₁ C B (fiberTwoCover π)) (relCover_sup C B (fiberTwoCover π))

/-- Step (b), vanishing form: `H¹` of the datum pair vanishes iff the degree-one
cohomology of the datum's glued sheaf does. -/
theorem subsingleton_datumPair_h1_iff :
    Subsingleton (datumPair D).H1 ↔ Subsingleton (Sheaf.HModule D.sheaf 1) :=
  (datumH1Equiv D).symm.toEquiv.subsingleton_congr

/-- **(a) at a fibre `p` of the test ring, on the datum**: the engine's complex-form
fibre hypothesis `Subsingleton (H¹(pair) ⊗ κ(p))` (the `hfib p` clause of
`datumRigidEngine`) holds iff the cokernel of the `κ(p)`-base-changed Čech differential
of the datum pair vanishes. Right-exactness only; the identification of the
base-changed complex with the complex of the fibre datum is the recorded DAT-1 stage
(1d-ii) seam (see the module docstring). -/
theorem datum_subsingleton_h1_residueField_tensor_iff (p : PrimeSpectrum B) :
    Subsingleton ((datumPair D).H1 ⊗[B] p.asIdeal.ResidueField) ↔
      Subsingleton ((p.asIdeal.ResidueField ⊗[B]
          (D.sheaf.obj.obj (op ((relCover C B (fiberTwoCover π)).V₀ ⊓
            (relCover C B (fiberTwoCover π)).V₁)))) ⧸
        LinearMap.range ((datumPair D).diff.baseChange p.asIdeal.ResidueField)) :=
  (datumPair D).subsingleton_h1_rTensor_iff p.asIdeal.ResidueField

end AlgebraicGeometry
