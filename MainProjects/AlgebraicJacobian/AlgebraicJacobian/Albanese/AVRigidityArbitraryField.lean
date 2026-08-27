/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.AVSelfProduct

/-!
# The two rigidity corollaries over an arbitrary base field

`Albanese/AVSelfProduct.lean` proves Milne §I.1 Corollaries 1.4 (an abelian variety is
commutative) and 1.2 (a pointed morphism of abelian varieties is a homomorphism) on the
project's four-instance abelian-variety package, but over an **algebraically closed**
field: both rest on `RigidityLemma.lean`, whose engine binds `[IsAlgClosed kbar]`.

This file removes that binder. Both corollaries hold over an arbitrary field `K`.

## Why this matters, and what it does not buy

The headline `picardJacobianWitness` (`Jacobian.lean`) is stated over an arbitrary field
with no rational-point hypothesis (owner decision, protection `I-0491`). Its fifth
obligation `isAlbanese_pic0Et` is the Albanese universal property there, and its docstring
prices the passage from `k̄` to `k` as "the Galois-descent step of cluster `G`".

That price is too high for *this* part of the passage. The Albanese engine
(`Albanese/AlbaneseFromData.lean`) is already field-agnostic — it lives in an arbitrary
`CartesianMonoidalCategory` — and consumes exactly two geometric inputs, the two rigidity
corollaries. Both are available over `K`:

* commutativity is *already* in mathlib over an arbitrary field
  (`isCommMonObj_of_isProper_of_geometricallyIntegral`, Stacks 0BFD), which descends it
  from `K̄` internally; the project's own `IsAlgClosed` version is not needed at that
  strength, because `GeometricallyIntegral` synthesises from the four-instance package;
* pointed rigidity descends by the *same* argument, which is what this file supplies
  (`isMonHom_of_pointed_arbitraryField`). `IsMonHom` is a pair of equations, `Over.pullback`
  along `K → K̄` is faithful and monoidal, and the abelian-variety package is stable under
  that base change — so the `k̄` corollary applies upstairs and reflects back down.

**What is still owed for `isAlbanese_pic0Et`, and this file does not touch any of it:**
the symmetric power `Sym^g C` (equivalently `HasColimit (permDiagram C g)`), Milne III.5.1(a)
birationality as a section over a dense open, the genus-`0` case, the basepoint condition,
and the transport of the Abel–Jacobi morphism to `Pic0SchemeEt`. Nothing here is a discharge
of the headline sorry; what it does is establish that the *field* is not among the reasons
that sorry is open.

## Main results

* `isMonHom_of_pointed_arbitraryField` — Milne I.1.2 over an arbitrary field.
* `isCommMonObj_of_package_arbitraryField` — Milne I.1.4 over an arbitrary field, recorded
  here so the pair is available together (the proof is mathlib's 0BFD plus one instance).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- **Milne §I.1 Corollary 1.4 over an arbitrary field: an abelian variety is
commutative.**

Same conclusion as `isCommMonObj_of_isProper_smooth_of_package` with the `[IsAlgClosed]`
binder deleted. The proof is mathlib's Stacks 0BFD
(`isCommMonObj_of_isProper_of_geometricallyIntegral`) after observing that
`GeometricallyIntegral` is synthesised from the project's four-instance package — a smooth
geometrically irreducible scheme over a field is geometrically integral. -/
theorem isCommMonObj_of_package_arbitraryField (A : Over (Spec (.of K)))
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom] :
    IsCommMonObj A :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A

/-- **Milne §I.1 Corollary 1.2 over an arbitrary field: a pointed morphism of abelian
varieties is a homomorphism.**

Same statement as `isMonHom_of_pointed` (`Albanese/AVSelfProduct.lean`) with the
`[IsAlgClosed kbar]` binder deleted.

The descent is the one mathlib's 0BFD uses for commutativity, and it works here for the
same reason: `IsMonHom` is a *pair of equations*, so a faithful monoidal functor reflects
it. Concretely, with `F = Over.pullback (Spec.map (algebraMap K K̄))`:

* the abelian-variety package is stable under this base change, so the `k̄` corollary
  `isMonHom_of_pointed` applies to `F.map α`;
* pointedness transports along `F` (`F.map` of the pointing equation, plus `ε`);
* `Over.pullback` is faithful, and `μ`-naturality turns the upstairs `mul_hom` into the
  downstairs one after cancelling the (iso) monoidal comparison.

No smoothness or properness of `B` beyond what the `k̄` statement asks, and no
quasi-projectivity: nothing in the argument is field-specific once the engine is applied
upstairs. -/
theorem isMonHom_of_pointed_arbitraryField {A B : Over (Spec (.of K))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    [GrpObj B] [IsProper B.hom]
    (α : A ⟶ B) (hα : η[A] ≫ α = η[B]) : IsMonHom α := by
  let f := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let F := Over.pullback f
  let A' := F.obj A
  let B' := F.obj B
  -- the abelian-variety package is stable under this base change
  have : IsProper A'.hom := by change IsProper (Limits.pullback.snd A.hom f); infer_instance
  have : Smooth A'.hom := by change Smooth (Limits.pullback.snd A.hom f); infer_instance
  have : GeometricallyIrreducible A'.hom := by
    change GeometricallyIrreducible (Limits.pullback.snd A.hom f); infer_instance
  have : IsProper B'.hom := by change IsProper (Limits.pullback.snd B.hom f); infer_instance
  -- the `k̄` corollary applies upstairs
  have hup : IsMonHom (F.map α) := by
    have hpt : η[A'] ≫ F.map α = η[B'] := by simp [← Functor.map_comp, hα]
    exact isMonHom_of_pointed (A := A') (B := B') (F.map α) hpt
  -- and reflects back down, by faithfulness plus `μ`-naturality
  refine { one_hom := hα, mul_hom := ?_ }
  exact F.map_injective <| by
    simpa [← Functor.LaxMonoidal.μ_natural_assoc,
      ← cancel_epi (Functor.LaxMonoidal.μ F A A)] using IsMonHom.mul_hom (F.map α)

end AlgebraicGeometry
