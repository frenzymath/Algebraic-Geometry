/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.StableAffineCover
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The Galois-descent engine is not inert: producers for `OrbitsInAffineOpen`

An adversarial audit (2026-07-29) recorded that the two engines of the Milne–Kollár Picard
route gate on classes with **zero producers anywhere in the tree**, so that neither engine
could fire at any object.  For the Galois half that class is
`SemilinearGalAction.OrbitsInAffineOpen` (`Picard/FiniteGaloisQuotient.lean`), the EGA II
4.5.4 hypothesis feeding `hasStableAffineCover_of_orbitsInAffineOpen`
(`Picard/StableAffineCover.lean`) and the deep gate `HasGaloisQuotient`.

This file supplies the producers, and then fires the whole chain at a concrete object.

## What the audit priced wrong

The orbit hypothesis was documented as needing quasi-projectivity ("it holds e.g. for
quasi-projective `X`", `FiniteGaloisQuotient.lean`), and Mathlib `v4.31` has no
quasi-projectivity vocabulary — which is how the class came to have no producer.  But the
hypothesis is *implied* in two cheaper situations that the project already owns:

* **§1, affine total space** (`instOrbitsInAffineOpen_of_isAffine`).  If `X` is affine the
  whole of `X` is an affine open, so `⊤` contains every orbit.  One line, no geometry.  In
  particular it fires at the *affine model* `specSemilinearGalAction` — the conventions
  validator of `FiniteGaloisQuotient.lean` — which is exactly the object
  `isGaloisQuotient_spec` proves the quotient theorem about.
* **§2, the reference base-change action** (`instOrbitsInAffineOpen_pullback`).  For
  `ρ = pullbackSemilinearGalAction K L g` on `Y ×_{Spec K} Spec L`, the action is through
  the *second* factor only, so `pullback.fst` is `Γ`-invariant (`pullbackGalMap_fst`) and
  every orbit sits inside the preimage of one affine open of `Y`.  Affine opens of `Y`
  cover `Y` (`Scheme.iSup_affineOpens_eq_top`), and `pullback.fst` is an affine morphism
  (base change of the affine `Spec L ⟶ Spec K`), so that preimage is affine
  (`IsAffineOpen.preimage`).  **No quasi-projectivity, no separatedness, no finiteness of
  `L/K`** — this producer holds for an arbitrary `Y`, and the base-change action is the one
  every `IsGaloisQuotient` statement is stated against.

So the Hironaka trap recorded in `FiniteGaloisQuotient.lean` is not weakened by anything
here: it bites for a *general* semilinear action, and both producers below are about
actions where the trap provably does not apply (the affine case has no room for it, the
base-change case is `Γ`-equivariantly fibred over a scheme where the action is trivial).

## §3, the concrete witness, and what it does and does not settle

`𝔽₄/𝔽₂` (`GaloisField 2 2` over `ZMod 2`) is a finite Galois extension with a *nontrivial*
group (`nontrivial_aut_galoisField_two_two` — the whole point of naming a concrete pair is
that a trivial group would make every clause vacuous), and `L` acted on by itself
(`SemilinearModules.lean`'s regular representation) is a semilinear affine model.  At that
object:

* `orbitsInAffineOpen_specGaloisField` — the audit's empty class, inhabited at a named object;
* `hasStableAffineCover_specGaloisField` — the §G2(a) gate, *fired by synthesis* through
  `hasStableAffineCover_of_orbitsInAffineOpen`, which is the downstream consumer the audit
  asked for;
* `hasGaloisQuotient_specGaloisField` — the **deep** gate `HasGaloisQuotient`, whose
  binder `[ρ.OrbitsInAffineOpen]` was previously unsatisfiable, discharged from
  `isGaloisQuotient_spec`;
* `isGaloisQuotient_spec_galoisField` — the quotient theorem itself at that object, with
  `Spec (𝔽₄^Γ) = Spec 𝔽₂` (up to the invariants spelling) as the quotient.

What this does **not** settle is the Picard-side application: the engine now fires, but the
object it fires at here is a point, not a curve's Picard scheme.  The remaining work is to
exhibit a semilinear action on the relevant `Pic`-side scheme, and for that §2's producer is
the load-bearing one — it needs no hypothesis on `Y` at all.

Sources: EGA II 4.5.4 (the refinement pattern), SGA I V.1, Mumford *Abelian Varieties* §7.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicJacobian.GaloisDescent

/-! ## §1. Affine total space -/

/-- **Every orbit of a semilinear action on an affine scheme lies in an affine open** — `⊤`
does, and it is affine (`isAffineOpen_top`).

This is the cheapest producer of `OrbitsInAffineOpen` and it is not a degenerate one: the
*affine model* `specSemilinearGalAction`, the object `isGaloisQuotient_spec` proves the
Galois quotient theorem about, is of this shape. -/
instance instOrbitsInAffineOpen_of_isAffine {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [IsAffine X] {f : X ⟶ Spec (CommRingCat.of L)}
    (ρ : SemilinearGalAction K L X f) : ρ.OrbitsInAffineOpen :=
  ⟨fun _ => ⟨⟨⊤, isAffineOpen_top X⟩, fun _ => trivial⟩⟩

/-! ## §2. The reference base-change action, over an arbitrary scheme -/

section Pullback

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of K))

/-- `pullback.fst` of the base change to `Spec L` is an affine morphism: it is the base
change of the affine `Spec L ⟶ Spec K`. -/
instance isAffineHom_pullback_fst_baseChange :
    IsAffineHom (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :=
  MorphismProperty.pullback_fst _ _ inferInstance

/-- **`pullback.fst` is `Γ`-invariant on points**: the base-change action moves only the
`Spec L` factor, so it does not move the image in `Y`.  Point-level form of
`pullbackGalMap_fst`. -/
lemma base_pullback_fst_act (γ : L ≃ₐ[K] L)
    (x : (Limits.pullback g (Spec.map (CommRingCat.ofHom (algebraMap K L)))).carrier) :
    (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K L)))).base
        (((pullbackSemilinearGalAction K L g).act γ).hom.base x)
      = (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K L)))).base x := by
  rw [pullbackSemilinearGalAction_act_hom]
  exact congrArg (fun (m : _ ⟶ Y) => m.base x) (pullbackGalMap_fst K L g γ)

/-- **The reference base-change action always satisfies the orbit-in-affine hypothesis**,
for an *arbitrary* `Spec K`-scheme `Y` — no quasi-projectivity, no separatedness, no
finiteness of `L/K`.

The orbit of `x` lies in `pullback.fst ⁻¹ᵁ U` for any affine open `U ⊆ Y` containing the
image of `x`: the action does not move that image (§`base_pullback_fst_act`), affine opens
cover `Y` (`Scheme.iSup_affineOpens_eq_top`), and the preimage of an affine open under the
affine `pullback.fst` is affine (`IsAffineOpen.preimage`).

This is the producer the Picard route needs: `IsGaloisQuotient` states its equivariance and
`T`-points clauses against exactly this action. -/
instance instOrbitsInAffineOpen_pullback :
    (pullbackSemilinearGalAction K L g).OrbitsInAffineOpen := by
  constructor
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (x := (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K L)))).base x)
    (U := ⊤) trivial
  refine ⟨⟨pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⁻¹ᵁ U,
    hU.preimage _⟩, fun γ => ?_⟩
  change (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K L)))).base
      (((pullbackSemilinearGalAction K L g).act γ).hom.base x) ∈ U
  rw [base_pullback_fst_act]
  exact hxU

/-- The `G2(a)` gate fires at the reference base-change action, by synthesis through
`hasStableAffineCover_of_orbitsInAffineOpen` — the downstream consumer of §2. -/
theorem hasStableAffineCover_pullback [FiniteDimensional K L] [IsGalois K L] :
    HasStableAffineCover K L (pullbackSemilinearGalAction K L g) := inferInstance

end Pullback

/-! ## §3. A concrete witness: `𝔽₄/𝔽₂` acting on itself -/

section Concrete

/-- The base field of the concrete witness. -/
abbrev F2 : Type := ZMod 2

/-- The concrete quadratic Galois extension `𝔽₄/𝔽₂`. -/
abbrev F4 : Type := GaloisField 2 2

/-- **The Galois group of the witness is nontrivial** — `Gal(𝔽₄/𝔽₂) ≅ ℤ/2`, of order
`finrank 𝔽₂ 𝔽₄ = 2`.

Named and proved because a *trivial* group would make every clause of `IsGaloisQuotient`
vacuous: the equivariance and `T`-points conditions quantify over `γ`, so a one-element
group turns them into statements about the identity.  Nontriviality is what makes the
witness below a witness. -/
theorem nontrivial_aut_F4 : Nontrivial (F4 ≃ₐ[F2] F4) := by
  have h := IsGalois.card_aut_eq_finrank F2 F4
  rw [GaloisField.finrank _ two_ne_zero] at h
  exact Finite.one_lt_card_iff_nontrivial.mp (by rw [h]; omega)

/-- The regular semilinear action of `Gal(𝔽₄/𝔽₂)` on `Spec 𝔽₄` over `Spec 𝔽₄`: the affine
model at `A = L`, using the regular representation `IsSemilinear K L L`
(`GaloisDescent/SemilinearModules.lean`). -/
noncomputable abbrev specActionF4 :
    SemilinearGalAction F2 F4 (Spec (CommRingCat.of F4))
      (Spec.map (CommRingCat.ofHom (algebraMap F4 F4))) :=
  specSemilinearGalAction F2 F4 F4

/-- **The audit's empty class, inhabited at a named object.**  `OrbitsInAffineOpen` for the
regular action on `Spec 𝔽₄`, by §1. -/
theorem orbitsInAffineOpen_specF4 : specActionF4.OrbitsInAffineOpen := inferInstance

/-- **The `G2(a)` gate fires at a named object**, by synthesis: `orbitsInAffineOpen_specF4`
feeds `hasStableAffineCover_of_orbitsInAffineOpen`.  This is the downstream consumer the
audit asked to be exhibited. -/
theorem hasStableAffineCover_specF4 :
    HasStableAffineCover F2 F4 specActionF4 := inferInstance

/-- **The deep gate `HasGaloisQuotient` at a named object.**  Its binder
`[ρ.OrbitsInAffineOpen]` was previously unsatisfiable — no producer existed anywhere — so no
instance of this class could be stated, let alone proved.  With §1 it is discharged from
`isGaloisQuotient_spec` (Speiser descent plus the globalized `T`-points property).

**Generalised downstream, and this proof is NOT redundant here (2026-07-30).**
`hasGaloisQuotient_of_isAffine` (`Picard/GaloisQuotientAffineGeneral.lean`) discharges the gate
for *every* semilinear action on an affine scheme, so from a file importing that module this
goal closes by `inferInstance`. **It does not close that way here, and cannot**: that module
imports *this* one (for §1's `instOrbitsInAffineOpen_of_isAffine`), so the reverse import would
be a cycle. Measured at exactly this file's imports, `inferInstance` fails — on
`OrbitsInAffineOpen`, since §1's instance is declared below this point. An earlier revision of
this paragraph said the goal "is now closed by `inferInstance`" full stop; that was false as
placed, and it is the import-closure trap (`I-1226`) reproduced one file away from a commit
correcting another instance of it.

The explicit proof therefore stays as the producer at this site, and independently as the
non-vacuity witness: a named *nontrivial*-group object (`nontrivial_aut_F4`) is what keeps the
`∀ γ` clauses of `IsGaloisQuotient` from degenerating.

`Spec (𝔽₄^Γ) ⟶ Spec 𝔽₂` is the quotient; `𝔽₄^Γ` is `𝔽₂` by Artin, though the statement does
not need that identification. -/
theorem hasGaloisQuotient_specF4 : HasGaloisQuotient specActionF4 :=
  ⟨_, _, isGaloisQuotient_spec F2 F4 F4⟩

/-- **The quotient theorem itself, at the concrete pair** — the `IsGaloisQuotient` predicate
in full (equivariant base-change isomorphism over `Spec 𝔽₄`, plus the universal `T`-points
property for **all** schemes `T`) for the regular action of `Gal(𝔽₄/𝔽₂)`.

This is the engine of `Picard/FiniteGaloisQuotientAffine.lean:473` running at an object,
which is what "the engine can fire" means. -/
theorem isGaloisQuotient_specF4 :
    IsGaloisQuotient specActionF4
      (Spec.map (CommRingCat.ofHom
        (algebraMap F2 (SemilinearAction.invariantsSubalgebra F2 F4 F4)))) :=
  isGaloisQuotient_spec F2 F4 F4

end Concrete

end AlgebraicJacobian.GaloisDescent
