/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.DualNumberCarrierReduction
import AlgebraicJacobian.Tangent.ChartTrivialityGeo

/-!
# The two chart presentations at `ε ↦ 0` and the square between them (W5-T4, instantiation)

`Tangent/ChartTrivialityGeo.lean` proves **(iii-c2-aff-geo)** over three hypotheses that it names
rather than builds: a presentation `e : Γ(Z, O) ≃+* A[ε]` upstairs, a presentation
`e' : Γ(X, g⁻¹O) ≃+* A` downstairs, and the square `hsq` intertwining `g.appLE` with `ε ↦ 0`. This
file supplies all three at the Wave-5 charts, with `Z = C_ε`, `X = C_k`, `A = Γ(C.left, W)` and
`g = relCurveMap C k[ε] k`:

* `epsChartDown` — the downstairs presentation `Γ(C_k, fst⁻¹W) ≃+* Γ(C.left, W)`;
* `Over.dualNumberSectionsOfIsAffineOpen` (already landed) — the upstairs one, used through its
  `symm`;
* `relSectionsMap_eq_fstRingHom_comp` — **the square**.

## Why the square was already three quarters written

`Over.relSectionsMap_dualNumberSections` (`Tangent/DualNumberCarrierReduction.lean`) says
`relSectionsMap C k[ε] k W (dualNumberSections x) = sectionsBaseChange (fst x ⊗ₜ 1)`. That *is*
the square's content — the docstring there calls it "the statement the `ε`-kernel computation
spends". What was missing is only that its right-hand side is stated as a base-changed pure tensor
rather than as an element of `Γ(C.left, W)`; `Algebra.TensorProduct.rid` closes that gap, and
`epsChartDown` is precisely `sectionsBaseChange.symm` followed by `rid`.

So the instantiation item that T4's residue had been reduced to is a *composition of landed
pieces*, and the honest reading is that (iii-c2-aff-geo) came with its own instantiation nearly
free. Recorded because the alternative reading — "the square is a new obligation" — is what the
roadmap said an hour before this file was written.

## Two spelling notes, both of which cost a cycle

**Both scoped instances must be opened.** `Over.sectionsAlgebra` is
`attribute [local instance]` (as in `DualNumberCarrier.lean`, `RelativeH1BaseChange.lean` and five
other files), and `TruncExpCech.EpsilonReduction`'s `epsAlgebra` is `scoped`. Without the first,
`Algebra k Γ(C.left, W)` fails to synthesize; without the second, `Algebra k[ε] k` does. Neither
absence means infrastructure is missing — the standing lesson of inbox `I-0567`/`I-0634`.

**`sectionsBaseChangeOfIsAffineOpen` is `sectionsBaseChange` at the affine witness by `rfl`, but
`rw` will not see through it.** The proof therefore states that step as an explicit
`rw [show … from rfl]` before applying `RingEquiv.symm_apply_apply`. This is `I-0685`'s trap again:
the goal is type-correct and the message is about a spelling.

## Scope

`A` is instantiated at the *section ring of a chart*, not at `k` — which is why
`Tangent/EpsZeroSurjective.lean` was worth proving over an arbitrary commutative ring rather than
for `Spec k → Spec k[ε]`. The two files meet here.

This file does **not** discharge `¬ IsAffine C.left` (the remaining input of
`Tangent/TwoChartHonest.lean`), and does not itself assemble the tangent-space conclusion: it
supplies the three chart-level hypotheses, at one affine open `W` at a time.

## Main declarations

* `AlgebraicGeometry.epsChartDown` — the downstairs chart presentation.
* `AlgebraicGeometry.relSectionsMap_eq_fstRingHom_comp` — the square `hsq` of
  `Opens.cechPicMap_ι_eq_one_of_map_eq_one`.

Reference: `informal/w5-t4-worksheet.md` §§6.17, 6.27.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open TensorProduct TruncExpCech DualNumber TrivSqZeroExt

namespace AlgebraicGeometry

open scoped TruncExpCech.EpsilonReduction

attribute [local instance] Over.sectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

/-- **The downstairs chart presentation.** Base-changing the curve along `k → k` does not change
its sections: `Γ(C_k, fst⁻¹W) ≃+* Γ(C.left, W)`, as `Over.sectionsBaseChange` (which presents the
left side as `Γ(C.left, W) ⊗[k] k`) followed by `Algebra.TensorProduct.rid`.

This is the `e'` that `Opens.cechPicMap_ι_eq_one_of_map_eq_one` takes, at `A = Γ(C.left, W)`. -/
noncomputable def epsChartDown {W : C.left.Opens} (hW : IsAffineOpen W) :
    Γ(relCurve C k, (fst C (overSpec k k)).left ⁻¹ᵁ W) ≃+* Γ(C.left, W) :=
  (Over.sectionsBaseChangeOfIsAffineOpen C k hW).symm.trans
    (Algebra.TensorProduct.rid k k _).toRingEquiv

/-- **The square `hsq`**: the relative-sections comparison along `ε ↦ 0`, read through the two
chart presentations, IS `ε ↦ 0` on dual numbers.

`relSectionsMap C k[ε] k W` is by definition `(relCurveMap C k[ε] k).appLE` at the two chart
preimages (`Cohomology/RelativeSectionsLinear.lean`), so this is exactly the hypothesis
`Opens.cechPicMap_ι_eq_one_of_map_eq_one` calls `hsq`, at
`g = relCurveMap C k[ε] k`, `A = Γ(C.left, W)`, `e = (dualNumberSectionsOfIsAffineOpen C hW).symm`
and `e' = epsChartDown C hW`.

The content is `Over.relSectionsMap_dualNumberSections`; everything else is transporting its
right-hand side from a pure tensor to a section via `rid`. -/
theorem relSectionsMap_eq_fstRingHom_comp {W : C.left.Opens} (hW : IsAffineOpen W) :
    (epsChartDown C hW : Γ(relCurve C k, (fst C (overSpec k k)).left ⁻¹ᵁ W) →+* Γ(C.left, W)).comp
        (relSectionsMap C (DualNumber k) k W)
      = (TruncExpCech.fstRingHom (R := Γ(C.left, W))).comp
          ((Over.dualNumberSectionsOfIsAffineOpen C hW).symm :
            Γ((C ⊗ overSpec k (DualNumber k)).left,
              (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W) →+* DualNumber Γ(C.left, W)) := by
  ext y
  simp only [RingHom.coe_comp, Function.comp_apply]
  set x := (Over.dualNumberSectionsOfIsAffineOpen C hW).symm y with hx
  have hy : y = Over.dualNumberSectionsOfIsAffineOpen C hW x := by
    rw [hx, RingEquiv.apply_symm_apply]
  rw [hy]
  simp only [RingEquiv.coe_toRingHom]
  rw [Over.dualNumberSectionsOfIsAffineOpen, Over.relSectionsMap_dualNumberSections]
  change (Algebra.TensorProduct.rid k k _)
      ((Over.sectionsBaseChangeOfIsAffineOpen C k hW).symm
        ((Over.sectionsBaseChange C k hW.isCompact hW.isQuasiSeparated)
          (TrivSqZeroExt.fst x ⊗ₜ[k] (1 : k)))) = _
  rw [show (Over.sectionsBaseChange C k hW.isCompact hW.isQuasiSeparated)
        (TrivSqZeroExt.fst x ⊗ₜ[k] (1 : k))
      = (Over.sectionsBaseChangeOfIsAffineOpen C k hW)
          (TrivSqZeroExt.fst x ⊗ₜ[k] (1 : k)) from rfl,
    RingEquiv.symm_apply_apply]
  rw [Algebra.TensorProduct.rid_tmul, one_smul]
  change TrivSqZeroExt.fst x
      = fstRingHom ((Over.dualNumberSections C hW.isCompact hW.isQuasiSeparated).symm
          ((Over.dualNumberSections C hW.isCompact hW.isQuasiSeparated) x))
  rw [RingEquiv.symm_apply_apply, fstRingHom_apply]

end AlgebraicGeometry
