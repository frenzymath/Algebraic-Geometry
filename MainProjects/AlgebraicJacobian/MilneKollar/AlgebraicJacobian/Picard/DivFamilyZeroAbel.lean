/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivFamilyZero
import AlgebraicJacobian.Picard.FGAPicRepresentability

/-!
# The Abel map at the empty divisor

`Picard/DivFamilyZero.lean` supplies the first inhabitant of `Scheme.DivFamily`. This
file spends it on the one place where having an inhabitant changes what can be
*checked* rather than merely stated: the **Abel map**

  `A_{C/k} : Div_{C/k} ⟶ Pic^♯_{C/k}`,  `[D] ↦ [O(D)] = -[I_D]`.

`Scheme.PicScheme.abelMap_app_mk` (`Picard/FGAPicRepresentability.lean`) states the
defining property `A([D]) = -[ker q]` for an arbitrary family. Before this file that
equation had **no instantiation**: `DivFamily` had no producer, so no value of the Abel
map was ever computed, and "the Abel map sends divisors to their line bundles" was a
statement about an empty domain.

## What is proved

`abelMap_zero`: `A([∅]) = 0`, i.e. the empty divisor goes to the **identity** of the
relative Picard group. Kleiman §3: `O(∅) = O`, so this is the normalisation an Abel map
must satisfy, and it is the first computed value of `abelMap` in the project.

The proof is where the empty divisor's arithmetic shows up. `ker (0 : O_{X_T} ⟶ 0)` is
`O_{X_T}` (`Limits.kernelZeroIsoSource`, composed with
`Scheme.Modules.pullbackUnitIso` because `DivFamily.q`'s source is stated as the
*pulled-back* unit). The zero of `PicSharp.relPresheaf` is *by definition* the class of
the unit line bundle (`Scheme.PicSharp.addCommGroup_via_tensorObj`), so the ideal class
is the group identity, and `neg_zero` finishes.

## What this is not

It is not a step of the seam: `Scheme.fgaPicardRepresentability` is untouched, and no
antecedent of it is witnessed. It also does **not** discharge
`IdentityComponent.ClassDegreePinned`'s acceptance test
(`classDegree_ne_zero_of_exists_pos_fiberDeg`), which needs a divisor family of
degree `d ≠ 0` — the empty divisor has degree `0`, so it is exactly the family that
test cannot use. That producer is still owed, and it needs a rational point.

What it does buy: the Abel map's defining equation, and the degree ledger of
`Picard/DivDegree.lean`, now have a worked instance to be wrong about. `abelDeg_zero`
below records the same value through the degree-refined Abel map, which is the form the
campaign's D-cluster consumes.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

variable {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]

/-- **The ideal sheaf of the empty divisor is the structure sheaf**, as a class in the
relative Picard group: `[I_∅] = [O] = 0`.

`ker (0 : O_{X_T} ⟶ 0) ≅ O_{X_T}` by `kernelZeroIsoSource`, then
`Modules.pullbackUnitIso` identifies `DivFamily.q`'s pulled-back-unit source with the
structure sheaf, and the zero of `relPresheaf` *is* the unit class. -/
theorem PicSharp.kernelClass_divFamilyZero (T : (Over (Spec (CommRingCat.of k)))ᵒᵖ) :
    (Quotient.mk (PicSharp.relPicSetoid C.hom T.unop.hom)
      (⟨kernel (DivFamily.zero C.hom T.unop).q,
        (DivFamily.zero C.hom T.unop).kerLocallyTrivial⟩ :
        LineBundle.OnProduct C.hom T.unop.hom))
      = (0 : (PicSharp.relPresheaf C).obj T) :=
  Quotient.sound (PicSharp.relPicRel_of_iso
    ⟨Limits.kernelZeroIsoSource ≪≫ Scheme.Modules.pullbackUnitIso _⟩)

variable [GeometricallyIntegral C.hom]

/-- **THE ABEL MAP SENDS THE EMPTY DIVISOR TO THE IDENTITY**: `A([∅]) = 0`.

`O(∅) = O` (Kleiman §3), the normalisation any Abel map must satisfy — and the **first
computed value of `abelMap` in this project**, since `DivFamily` had no inhabitant to
evaluate it at before `Picard/DivFamilyZero.lean`.

Stated against `abelMapWitness`'s instance, i.e. via `abelMap_app_mk`, not under an
arbitrary `[HasAbelMap C]` binder — that class is a data slot inhabited by the constant
zero map, for which `abelMap_app_mk` provably fails (see its docstring, `I-0953`). Under
*that* inhabitant this equation would hold trivially and say nothing, which is exactly
why the instance matters here. -/
theorem PicScheme.abelMap_zero (T : (Over (Spec (CommRingCat.of k)))ᵒᵖ) :
    (PicScheme.abelMap C).app T
        (Quotient.mk (DivFamily.setoid C.hom T.unop) (DivFamily.zero C.hom T.unop))
      = (0 : (PicSharp.relPresheaf C).obj T) := by
  rw [PicScheme.abelMap_app_mk, PicSharp.kernelClass_divFamilyZero]
  exact neg_zero (G := ((PicSharp.relPresheaf C).obj T : Type _))

/-- **The degree-refined Abel map at the empty divisor**, in the form the campaign's
D-cluster consumes: `A⁰([∅]) = 0`.

`abelDeg C 0` is `divFunctorDegι ≫ abelMapWitness`, so this is `abelMap_zero` transported
along the degree-`0` inclusion; `abelDeg_app_mk` supplies the transport. -/
theorem PicScheme.abelDeg_zero (T : (Over (Spec (CommRingCat.of k)))ᵒᵖ) :
    (PicScheme.abelDeg C 0).app T (DivFunctorDeg.zeroClass C.hom T.unop)
      = (0 : (PicSharp.relPresheaf C).obj T) := by
  rw [show (DivFunctorDeg.zeroClass C.hom T.unop) =
      ⟨Quotient.mk (DivFamily.setoid C.hom T.unop) (DivFamily.zero C.hom T.unop),
        DivFunctor.classHasFiberDeg_zeroClass C.hom T.unop⟩ from rfl,
    PicScheme.abelDeg_app_mk]
  exact PicScheme.abelMap_zero C T

end Scheme

end AlgebraicGeometry
