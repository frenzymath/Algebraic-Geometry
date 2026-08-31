/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.CechKernelLemma

/-!
# Restriction of relative Picard classes to an étale cover is injective

The usable form of the (C1) étale-separatedness theorem
(`AlgebraicGeometry.PicEtAff.unit_injective`, `AlgebraicJacobian.Picard.CechKernelLemma`)
for the Layer-2 gluing arguments: for a curve `C` (proper, geometrically irreducible and
geometrically reduced over `k`), a `k`-algebra `R` and a presented étale cover `E` of
`Spec R`, two relative Picard classes over `R` with equal restrictions to the cover
carrier are equal (`AlgebraicGeometry.relPicAlgMap_injective_of_etaleCover`).

Indeed, the unit of the plus construction sends a class `z` to its tautological descent
class represented on *any* cover (`PicEtAff.unit_eq_mk`), so equal restrictions give
equal units, and the unit is injective by (C1).
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable {R : Type u} [CommRing R] [Algebra k R]

/-- The composite `R → Γ(self cover) → Γ(E)` of the tautological identifications is the
structure map of the carrier of `E`. -/
private lemma fromSelf_comp_ofId (E : Algebra.EtaleCover R) :
    (E.fromSelf.restrictScalars k).comp
        ((Algebra.ofId R (Algebra.EtaleCover.self R).Carrier).restrictScalars k)
      = (Algebra.ofId R E.Carrier).restrictScalars k := by
  ext r
  simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
    Algebra.ofId_apply, Algebra.EtaleCover.fromSelf, AlgHom.coe_comp]
  exact congrArg (algebraMap R E.Carrier)
    (((Algebra.EtaleCover.selfEquiv R).commutes r).trans rfl)

/-- The unit of the plus construction, represented on an arbitrary cover: `unit z` is the
class of the tautological descent datum of `z` on any presented étale cover `E`. -/
theorem PicEtAff.unit_eq_mk (E : Algebra.EtaleCover R) (z : relPic C (overSpec k R)) :
    PicEtAff.unit C R z
      = PicEtAff.mk C E
          ⟨relPicAlgMap C ((Algebra.ofId R E.Carrier).restrictScalars k) z,
            tautological_mem_descentClasses C E z⟩ := by
  have hval : descentMap C E.fromSelf
        ⟨relPicAlgMap C
            ((Algebra.ofId R (Algebra.EtaleCover.self R).Carrier).restrictScalars k) z,
          tautological_mem_descentClasses C (.self R) z⟩
      = ⟨relPicAlgMap C ((Algebra.ofId R E.Carrier).restrictScalars k) z,
          tautological_mem_descentClasses C E z⟩ := by
    refine Subtype.ext ?_
    rw [descentMap_coe, ← relPicAlgMap_comp, fromSelf_comp_ofId]
  calc PicEtAff.unit C R z
      = PicEtAff.mk C (.self R)
          ⟨relPicAlgMap C
              ((Algebra.ofId R (Algebra.EtaleCover.self R).Carrier).restrictScalars k) z,
            tautological_mem_descentClasses C (.self R) z⟩ := rfl
    _ = PicEtAff.mk C E (descentMap C E.fromSelf
          ⟨relPicAlgMap C
              ((Algebra.ofId R (Algebra.EtaleCover.self R).Carrier).restrictScalars k) z,
            tautological_mem_descentClasses C (.self R) z⟩) :=
        (PicEtAff.mk_descentMap C E.fromSelf _).symm
    _ = PicEtAff.mk C E
          ⟨relPicAlgMap C ((Algebra.ofId R E.Carrier).restrictScalars k) z,
            tautological_mem_descentClasses C E z⟩ := by rw [hval]

variable [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

/-- **Restriction of relative Picard classes to an étale cover is injective** — the
consumable corollary of the (C1) étale-separatedness theorem: two relative Picard
classes over `R` agreeing on a presented étale cover of `Spec R` agree.  This is what
licenses every gluing step of the Layer-2 functor. -/
theorem relPicAlgMap_injective_of_etaleCover (E : Algebra.EtaleCover R) :
    Function.Injective
      (relPicAlgMap C ((Algebra.ofId R E.Carrier).restrictScalars k)) := by
  intro x y h
  apply PicEtAff.unit_injective C R
  rw [PicEtAff.unit_eq_mk C E x, PicEtAff.unit_eq_mk C E y]
  exact congrArg (PicEtAff.mk C E) (Subtype.ext h)

end AlgebraicGeometry
