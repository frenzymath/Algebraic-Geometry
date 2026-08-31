/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.Basic
import AlgebraicJacobian.Curve.GeometricallyReduced
import AlgebraicJacobian.RiemannRoch.Ledger.P1Charts
import AlgebraicJacobian.RiemannRoch.Ledger.RationalToP1

/-!
# A finite morphism from the curve to the projective line

For the smooth, proper, geometrically irreducible curve `C` over `k`, this file is about the
existence and the basic consequences of a **finite** `k`-morphism `π : C ⟶ ℙ¹`.

## Contents

* `AlgebraicGeometry.IsFinite.of_locallyQuasiFinite_of_comp` — the general Zariski-main-theorem
  reduction: a locally quasi-finite morphism which is proper over a separated base is finite.
* `AlgebraicGeometry.isFinite_toP1_of_locallyQuasiFinite` — the specialization: a locally
  quasi-finite `k`-morphism from the proper curve `C` to `ℙ¹` is finite.
* `AlgebraicGeometry.exists_isFinite_toP1_of_locallyQuasiFinite` — the same, in existential
  form: to produce a finite `π : C ⟶ ℙ¹` over `k` it suffices to produce a locally
  quasi-finite one.
* Preimage bookkeeping for a finite `π`, consumed by the two-lattice finiteness argument for
  `H¹(C, 𝒪_C)`: the preimages of the two standard charts are affine opens covering `C`
  (`isAffineOpen_preimage_chartOpen`, `preimage_chartOpen_sup`), and the section ring of each
  preimage is module-finite over the section ring of the chart (`finite_app_chartOpen`).
* `AlgebraicGeometry.exists_isFinite_toP1` — the **existence** of a finite `π : C ⟶ ℙ¹` over
  `k`, by spreading out a transcendental rational function
  (`AlgebraicJacobian.Curve.RationalToP1`) and applying the reduction above; see its
  docstring for the proof route.
* `AlgebraicGeometry.exists_isFinite_isDominant_toP1` — the same finite `π`, now also carrying
  **dominance**, exported from the transcendence step of the construction
  (`AlgebraicJacobian.Curve.RationalToP1.exists_locallyQuasiFinite_isDominant_toP1`). This is
  the map the fibrewise-large-twist-vanishing class form consumes with no external dominance
  hypothesis.
-/

set_option autoImplicit false

universe u

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry

/-- **Zariski's main theorem, cancellation form**: a locally quasi-finite morphism `π` such
that `π ≫ g` is proper and `g` is separated is finite. (Properness of `π` follows by
cancellation, and a proper locally quasi-finite morphism is finite.) -/
theorem IsFinite.of_locallyQuasiFinite_of_comp {X Y S : Scheme.{u}}
    (π : X ⟶ Y) (g : Y ⟶ S) [LocallyQuasiFinite π] [IsSeparated g] [IsProper (π ≫ g)] :
    IsFinite π :=
  have : IsProper π := IsProper.of_comp π g
  IsFinite.of_isProper_of_locallyQuasiFinite π

variable {k : Type u} [Field k]

section ZMT

variable {X : Scheme.{u}}

/-- A locally quasi-finite `k`-morphism from a scheme which is proper over `k` to the
projective line is finite. This is the Zariski-main-theorem half of the construction of the
finite map `C ⟶ ℙ¹`: it reduces finiteness to local quasi-finiteness. -/
theorem isFinite_toP1_of_locallyQuasiFinite (f : X ⟶ Spec (.of k)) [IsProper f]
    (π : X ⟶ P1 k) [LocallyQuasiFinite π] (hπ : π ≫ P1.structureMap k = f) :
    IsFinite π :=
  have : IsProper (π ≫ P1.structureMap k) := hπ ▸ inferInstance
  IsFinite.of_locallyQuasiFinite_of_comp π (P1.structureMap k)

end ZMT

/-- To produce a finite `k`-morphism `C ⟶ ℙ¹` it suffices to produce a locally quasi-finite
one; Zariski's main theorem upgrades it. -/
theorem exists_isFinite_toP1_of_locallyQuasiFinite {C : Over (Spec (.of k))} [IsProper C.hom]
    (h : ∃ π : C.left ⟶ P1 k, LocallyQuasiFinite π ∧ π ≫ P1.structureMap k = C.hom) :
    ∃ π : C.left ⟶ P1 k, IsFinite π ∧ π ≫ P1.structureMap k = C.hom := by
  obtain ⟨π, hqf, hcomp⟩ := h
  exact ⟨π, isFinite_toP1_of_locallyQuasiFinite C.hom π hcomp, hcomp⟩

variable {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- **Existence of a finite map to the projective line**: on the smooth, proper,
geometrically irreducible curve `C/k` there is a finite `k`-morphism `π : C ⟶ ℙ¹`.

This is the keystone the two-lattice finiteness argument for `H¹(C, 𝒪_C)` consumes.

Proof route (see `informal/route-decision.md`, Wave 1 item 4):
1. `C` is integral (smooth ⟹ geometrically reduced, `AlgebraicJacobian.Curve.
   GeometricallyReduced`, plus geometric irreducibility, `AlgebraicJacobian.Curve.Basic`),
   and the function field of `C` contains an element transcendental over `k`: the étale
   coordinate of a standard smooth chart of relative dimension `1`
   (`SmoothOfRelativeDimension.exists_transcendental_functionField`, via the structure
   theorem for standard smooth algebras of Stacks 00T7);
2. the transcendental function spreads out to a morphism `π : C ⟶ ℙ¹` over `k`: the stalks
   of `C` are valuation rings (localizations of the Dedekind chart rings,
   `AlgebraicJacobian.Curve.DedekindSections` and `Curve.StalksDVR`), so at each point
   either `f` or `1/f` is a regular germ; the two chart morphisms agree generically by the
   gluing identity `P1.fromSpecChart_units`, so the associated rational map `C ⤏ ℙ¹` is
   defined everywhere (`AlgebraicJacobian.Curve.RationalToP1`);
3. `π` maps the generic point to the generic point (transcendence again), hence has finite
   fibers on the height-one Noetherian space `C`, hence is locally quasi-finite;
4. conclude with `exists_isFinite_toP1_of_locallyQuasiFinite` (Zariski's main theorem). -/
theorem exists_isFinite_toP1 :
    ∃ π : C.left ⟶ P1 k, IsFinite π ∧ π ≫ P1.structureMap k = C.hom :=
  exists_isFinite_toP1_of_locallyQuasiFinite (exists_locallyQuasiFinite_toP1 C.hom)

/-- **Existence of a finite dominant map to the projective line.** On the smooth, proper,
geometrically irreducible curve `C/k` there is a finite `k`-morphism `π : C ⟶ ℙ¹` which is
moreover **dominant**.

The dominance is exported from the construction itself: the transcendental spreading-out
`AlgebraicJacobian.Curve.RationalToP1.exists_locallyQuasiFinite_isDominant_toP1` sends the
generic point of `C` to the generic point of `ℙ¹`, whose closure is all of `ℙ¹`. Zariski's
main theorem (`isFinite_toP1_of_locallyQuasiFinite`) upgrades the locally-quasi-finite map to
a finite one, preserving dominance and the compatibility with the structure morphisms.

This is the FLV-4 frontier witness: it lets the fibrewise-large-twist-vanishing headline and
class form (`AlgebraicGeometry.subsingleton_hModule_divisorSheaf_one_of_isFinite_toP1`,
`AlgebraicGeometry.exists_subsingleton_hModule_one_of_one_le_classDeg_of_isFinite_toP1`) be
consumed with the *constructed* `π`, with no manually supplied `IsDominant` hypothesis. -/
theorem exists_isFinite_isDominant_toP1 :
    ∃ π : C.left ⟶ P1 k, IsFinite π ∧ IsDominant π ∧ π ≫ P1.structureMap k = C.hom := by
  obtain ⟨π, hqf, hdom, hcomp⟩ := exists_locallyQuasiFinite_isDominant_toP1 C.hom
  haveI := hqf
  exact ⟨π, isFinite_toP1_of_locallyQuasiFinite C.hom π hcomp, hdom, hcomp⟩

/-! ### Preimage bookkeeping for a finite morphism to the projective line

The next wave feeds these to the two-lattice/Mayer–Vietoris finiteness argument: the
preimages of the two standard charts form an affine cover of `C`, with section rings
module-finite over `k[t]`. Everything here only needs `π` finite (indeed mostly just
affine), not how it was constructed. -/

section Preimages

variable {Y : Scheme.{u}} (π : Y ⟶ P1 k)

/-- The preimage of each standard chart of `ℙ¹` under an affine (e.g. finite) morphism is an
affine open. -/
theorem isAffineOpen_preimage_chartOpen [IsAffineHom π] (i : Fin 2) :
    IsAffineOpen (π ⁻¹ᵁ P1.chartOpen k i) :=
  (P1.isAffineOpen_chartOpen k i).preimage π

/-- The preimages of the two standard charts of `ℙ¹` cover the source. -/
theorem preimage_chartOpen_sup :
    π ⁻¹ᵁ P1.chartOpen k 0 ⊔ π ⁻¹ᵁ P1.chartOpen k 1 = ⊤ := by
  refine le_antisymm le_top fun x _ => ?_
  have h : π.base x ∈ P1.chartOpen k 0 ⊔ P1.chartOpen k 1 := by
    rw [P1.chartOpen_sup]
    trivial
  rw [TopologicalSpace.Opens.mem_sup] at h ⊢
  exact h

/-- For a finite morphism `π : X ⟶ ℙ¹`, the section ring of the preimage of a standard chart
is module-finite over the section ring of the chart (that is, over `k[t]`, via
`P1.chartSectionsEquiv₀`/`₁`). -/
theorem finite_app_chartOpen [IsFinite π] (i : Fin 2) :
    RingHom.Finite (π.app (P1.chartOpen k i)).hom :=
  π.finite_app _ (P1.isAffineOpen_chartOpen k i)

/-- For a finite morphism `π : X ⟶ ℙ¹`, the section ring of the preimage of the chart
overlap is module-finite over the section ring of the overlap (that is, over the Laurent
polynomial ring, via `P1.overlapSectionsEquiv`). -/
theorem finite_app_overlap [IsFinite π] :
    RingHom.Finite (π.app (Proj.basicOpen (homogeneousSubmodule (Fin 2) k)
      (X 0 * X 1))).hom :=
  π.finite_app _ (P1.isAffineOpen_overlap k)

end Preimages

end AlgebraicGeometry
