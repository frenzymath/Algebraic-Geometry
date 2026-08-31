/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.EntriesIdeal
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The universal vanishing locus as a closed subscheme (DD-3, stage 3e)

The thin scheme-level wrapper of the entries-ideal gift
(`Picard/EntriesIdeal.lean`; `informal/spec-dd-3.md` §2): for `φ : M →ₗ[R] N` with
`M` finite and `N` finite projective, the closed subscheme
`vanishingLocus φ = Spec (R ⧸ entriesIdeal φ)` of `Spec R` represents the vanishing of
`φ` under base change — a ring map `R → S` kills the entries ideal iff it factors
(uniquely) through the quotient, iff `φ ⊗ S = 0`.

DD-R's `(♦)` carve consumes this chart-by-chart on the Grassmannian pair, glued on the
frame atlas by uniqueness of the universal property.

* `AlgebraicGeometry.Grassmannian.vanishingLocus`, `vanishingLocusι`: the closed
  subscheme and its immersion, with `isClosedImmersion_vanishingLocusι`.
* `AlgebraicGeometry.Grassmannian.entriesIdeal_le_ker_iff_factors`: the representing
  property at the level of ring maps (existence and uniqueness of the factorisation).
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Grassmannian

variable {R : Type u} [CommRing R] {M N : Type u}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [Module.Finite R M] [Module.Finite R N] [Module.Projective R N]

/-- **The universal vanishing locus** of `φ : M →ₗ[R] N` (`M` finite, `N` finite
projective): the closed subscheme `Spec (R ⧸ entriesIdeal φ)` of `Spec R` on which `φ`
universally vanishes. -/
noncomputable def vanishingLocus (φ : M →ₗ[R] N) : Scheme :=
  Spec (CommRingCat.of (R ⧸ entriesIdeal φ))

/-- The closed immersion `vanishingLocus φ ⟶ Spec R`. -/
noncomputable def vanishingLocusι (φ : M →ₗ[R] N) :
    vanishingLocus φ ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (entriesIdeal φ)))

/-- The vanishing locus is a **closed subscheme** of `Spec R`:
`IsClosedImmersion.spec_of_surjective` applied to the quotient map. -/
instance isClosedImmersion_vanishingLocusι (φ : M →ₗ[R] N) :
    IsClosedImmersion (vanishingLocusι φ) :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (entriesIdeal φ))) Ideal.Quotient.mk_surjective

/-- **The representing property** at the level of ring maps: a ring map `R → S` kills
the entries ideal iff it factors through the quotient `R ⧸ entriesIdeal φ`; the
factorisation is unique because the quotient map is surjective.  Combined with
`baseChange_eq_zero_iff`, a map kills the entries ideal iff it universally kills `φ`. -/
theorem entriesIdeal_le_ker_iff_factors (φ : M →ₗ[R] N) {S : Type u} [CommRing S]
    (f : R →+* S) :
    entriesIdeal φ ≤ RingHom.ker f ↔
      ∃! g : R ⧸ entriesIdeal φ →+* S,
        g.comp (Ideal.Quotient.mk (entriesIdeal φ)) = f := by
  constructor
  · intro h
    have hker : ∀ a ∈ entriesIdeal φ, f a = 0 := fun x hx => RingHom.mem_ker.mp (h hx)
    refine ⟨Ideal.Quotient.lift (entriesIdeal φ) f hker,
      RingHom.ext fun x => Ideal.Quotient.lift_mk (entriesIdeal φ) f hker, ?_⟩
    intro g hg
    refine RingHom.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [show g (Ideal.Quotient.mk (entriesIdeal φ) x)
        = (g.comp (Ideal.Quotient.mk (entriesIdeal φ))) x from rfl, hg]
    exact (Ideal.Quotient.lift_mk (entriesIdeal φ) f hker).symm
  · rintro ⟨g, hg, -⟩ x hx
    rw [RingHom.mem_ker, ← hg, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

end AlgebraicGeometry.Grassmannian
