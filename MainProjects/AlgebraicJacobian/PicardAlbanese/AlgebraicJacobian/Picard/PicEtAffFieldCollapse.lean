/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtAffMap
import AlgebraicJacobian.Picard.RelPicCoverInjective

/-!
# The shared plus-class field collapse (DAT-B B-5 fibre collapse / B-4 gap-1 collapse)

This is the **shared plus-class collapse lemma** flagged by `w4-datb-worksheet.md` §5
risk 6 and by the B-4 landing note I-0252 ("state it once as a named lemma with a
characterizing property … both consume it"): a plus class of the one-step étale-plus
Picard group over a *field* becomes an honest relative-Picard class after base change to a
suitable finite separable field extension.

Over a field `K`, a plus class `p : PicEtAff C K` is `PicEtAff.mk E x` for a presented
étale cover `E` of `Spec K` and a descent class `x` (`Picard/PicEtAff.lean`).  Field
cofinality (`Algebra.EtaleCover.exists_finiteSeparableField_algHom`,
`Algebra/EtaleCover.lean` — étale covers of a field are refined by finite separable field
extensions) supplies a finite separable `L/K` together with a `K`-algebra map
`ℓ : E.Carrier →ₐ[K] L`.  Base-changing `E` to `L` yields a cover with an `L`-point, so the
base-changed descent class is, by the descent/cocycle condition (`relPicAlgMap_congr`), the
tautological datum of an honest class: `PicEtAff.map C L p` is the plus-unit of the
relative-Picard class `relPicAlgMap ℓ x` on `C_L` (`PicEtAff.unit C L …`).

## Main results

* `AlgebraicGeometry.PicEtAff.map_mk_eq_unit_of_algHom` — the collapse: `mk C E x`
  restricted over a finite separable `L/K` (via a `K`-algebra map `ℓ` of the cover
  carrier) is `PicEtAff.unit C L (relPicAlgMap ℓ x)`.
* `AlgebraicGeometry.PicEtAff.map_mk_eq_unit_relPicMk_of_algHom` — the same with the honest
  class presented as `relPicMk` of a Čech Picard class `M` on `C_L`, the form the degree
  seam (`degAt_of_affineEquiv_eq_unit_relPicMk`) and the shifted-datum extraction
  (`exists_cechPicClass_eq`) consume.

The finite separable `L` with `ℓ : E.Carrier →ₐ[K] L` is supplied by field cofinality
(`Algebra.EtaleCover.exists_finiteSeparableField_algHom`).  Both statements take the tower
`k → K → L` as clean instance hypotheses — the campaign-idiomatic fibre-extension form
(cf. `Picard/DivSchemeSeed.lean`).  A consumer must instantiate `L` with a well-behaved
`Algebra k L` (a native tower); a `RingHom.toAlgebra`-composite `letI` triggers the
two-level-tower diamond of I-0236 when `PicEtAff.map C L` unfolds the base-changed carrier
(a genuine `whnf` non-termination, verified this pass — see the landing note).

The statements carry **no** hypotheses on the curve `C.hom` (they are purely about the
plus construction), so they are available to every consumer of the plus group.
-/

set_option autoImplicit false
-- Base-changed étale carriers are quotients of polynomial rings; keep unification from
-- whnf-blowing up on them.
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

set_option maxHeartbeats 800000 in
-- The base-changed étale carrier is a quotient of a polynomial ring; the descent
-- naturality defeq through it is heavy, so bump the budget for this declaration.
/-- **The plus-class collapse at an explicit refinement `ℓ` into a finite separable
extension** — the honest math heart of the collapse, with the extension `L` and its
tower a hypothesis (so no composite-algebra `letI` is forced through the base-changed
carrier).  For a descent class `x` on a cover `E` of `K` and a `K`-algebra map
`ℓ : E.Carrier →ₐ[K] L`, the plus class `mk C E x` restricts over `L` to the plus-unit of
the honest relative-Picard class `relPicAlgMap ℓ x` on `C_L`.

Route: `map_mk` reads the restriction as `mk (E.baseChange L) (descentBaseChange x)`;
`unit_eq_mk` reads the target unit on the same cover; the descent condition
(`relPicAlgMap_congr`, applied to `baseChangeInclude` and `ofId ∘ ℓ`) identifies the two
descent classes through `descentBaseChange_coe`. -/
theorem PicEtAff.map_mk_eq_unit_of_algHom {K L : Type u} [Field K] [Algebra k K]
    [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    {E : Algebra.EtaleCover K} (x : descentClasses C E) (ℓ : E.Carrier →ₐ[K] L) :
    PicEtAff.map C L (PicEtAff.mk C E x)
      = PicEtAff.unit C L
          (relPicAlgMap C (ℓ.restrictScalars k) (x : relPic C (overSpec k E.Carrier))) := by
  have hval : (descentBaseChange C L E x : relPic C (overSpec k (E.baseChange L).Carrier))
      = relPicAlgMap C ((Algebra.ofId L (E.baseChange L).Carrier).restrictScalars k)
          (relPicAlgMap C (ℓ.restrictScalars k) (x : relPic C (overSpec k E.Carrier))) := by
    rw [descentBaseChange_coe, ← relPicAlgMap_comp]
    exact relPicAlgMap_congr C (E.baseChangeInclude L)
      (((Algebra.ofId L (E.baseChange L).Carrier).restrictScalars K).comp ℓ) x.2
  rw [PicEtAff.map_mk,
    PicEtAff.unit_eq_mk C (E.baseChange L)
      (relPicAlgMap C (ℓ.restrictScalars k) (x : relPic C (overSpec k E.Carrier)))]
  exact congrArg (PicEtAff.mk C (E.baseChange L)) (Subtype.ext hval)

/-- **The shared plus-class field collapse, Čech form** (`w4-datb` §1.2 step 1; B-4 gap-1).
The honest class `relPicAlgMap ℓ x` of `PicEtAff.map_mk_eq_unit_of_algHom` is presented as
`relPicMk` of a Čech Picard class `M` on `C_L` — the form the degree seam
(`degAt_of_affineEquiv_eq_unit_relPicMk`) and the shifted-datum extraction
(`exists_cechPicClass_eq`) consume. -/
theorem PicEtAff.map_mk_eq_unit_relPicMk_of_algHom {K L : Type u} [Field K] [Algebra k K]
    [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    {E : Algebra.EtaleCover K} (x : descentClasses C E) (ℓ : E.Carrier →ₐ[K] L) :
    ∃ M : (C ⊗ overSpec k L).left.CechPic,
      PicEtAff.map C L (PicEtAff.mk C E x)
        = PicEtAff.unit C L (relPicMk C (overSpec k L) M) := by
  obtain ⟨M, hM⟩ := relPicMk_surjective C (overSpec k L)
    (relPicAlgMap C (ℓ.restrictScalars k) (x : relPic C (overSpec k E.Carrier)))
  exact ⟨M, by rw [PicEtAff.map_mk_eq_unit_of_algHom C x ℓ, hM]⟩

end AlgebraicGeometry
