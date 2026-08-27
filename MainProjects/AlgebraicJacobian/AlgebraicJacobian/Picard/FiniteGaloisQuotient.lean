/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Combinatorics.Quiver.ReflQuiver
import AlgebraicJacobian.Picard.GaloisDescent.SemilinearAlgebras

/-!
# The finite Galois quotient engine (campaign milestone `G2`, scheme layer)

Let `k'/k` be a finite Galois extension with group `Γ = Gal(k'/k)` and let `X'` be a
`k'`-scheme with a **semilinear** `Γ`-action.  This file supplies the scheme-level
vocabulary and statements for the quotient engine `G2` of the Picard representability
campaign (`informal/pic-representability-campaign.md`, cluster `G`): the `k`-scheme
`X = X'/Γ` with `Γ`-equivariant `X ×_k k' ≅ X'` and
`Hom_k(T, X) ≅ Hom_{k'}(T_{k'}, X')^Γ`.

## Semilinearity at scheme level (audit, campaign checklist item — conventions)

A semilinear action is a group homomorphism `act : Γ →* Aut X'` together with
commuting squares over the Galois action on the base: `(act γ).hom ≫ f = f ≫ Spec γ`
(`SemilinearGalAction`).  Conventions are **validated constructively** by the affine
model `specSemilinearGalAction`: for `X' = Spec A` with a `MulSemiringAction Γ A`
that is `IsSemilinear K L A`, the assignment `γ ↦ Spec (γ⁻¹ • ·)` (`toSpecAut`) is a
group homomorphism into `Aut (Spec A)` — the inversion is forced jointly by the
contravariance of `Spec` and mathlib's `Aut` group law (`(x*y).hom = y.hom ≫ x.hom`)
— and satisfies the commuting squares.

## Hironaka trap (campaign audit item 8, BLOCKING — verdict recorded here)

The **orbit-in-affine hypothesis** (`SemilinearGalAction.OrbitsInAffineOpen`: every
`Γ`-orbit lies in an affine open) is **essential and non-technical**.  For a free
action of `ℤ/2` on Hironaka's smooth proper non-projective threefold swapping two
rational curves that meet no common affine open, the quotient does **not** exist as
a scheme (only as an algebraic space); this is the same counterexample genus as the
permanently-instance-free `HasSmoothProperQuotient` (`FGAPicRepresentability.lean`).
Consequently the quotient existence is **never** stated for a bare `X'`: every
statement below carries the orbit hypothesis (or is a `Prop`-gate with **no
instances**).  For the campaign consumer `J'_r` the hypothesis is supplied by the
Γ-stable covering `V_Σ` with Grassmannian-immersion certificates (plan `J5`/`R6`).

## Main definitions and results

* `toSpecAut G A : G →* Aut (Spec A)` — a group acting on a ring by ring
  automorphisms acts on `Spec A` by scheme automorphisms.
* `SemilinearGalAction K L X f` — semilinear `Gal(L/K)`-action on a scheme over
  `Spec L`.
* `specSemilinearGalAction` — the affine model (conventions validator).
* `pullbackSemilinearGalAction` — the canonical action on a base change
  `T ×_{Spec K} Spec L` through the second factor (used to *state* equivariance of
  the descent isomorphism and the `T`-points property).
* `SemilinearGalAction.OrbitsInAffineOpen` — the orbit-in-affine hypothesis class.
* `IsGaloisQuotient ρ g` — the full quotient predicate: `Γ`-equivariant base-change
  isomorphism **and** the universal `T`-points property
  `Hom_k(T, X) ≅ Hom_{k'}(T_{k'}, X')^Γ` (unique descent of equivariant morphisms).
* `HasStableAffineCover` — Γ-stable affine refinement, the EGA II 4.5.4 pattern
  (`finite point set in an affine open of a separated/quasi-projective scheme
  refines to a Γ-stable affine open`). **This is no longer a gate: `G2(a)` was
  discharged** and `StableAffineCover.lean:279`
  (`hasStableAffineCover_of_orbitsInAffineOpen`) is a global `instance` deriving
  it from `[ρ.OrbitsInAffineOpen]` alone. Measured (`review-ajc`, 2026-07-29):
  `infer_instance` succeeds for an *abstract* `ρ` carrying only the orbit
  hypothesis, and fails without it — so the orbit hypothesis is exactly what it
  costs. The three sentences in this file and in `FiniteGaloisQuotientAffine.lean`
  that called it instance-free predate that discharge.
* `HasGaloisQuotient` — `Prop`-gate. It **was** genuinely instance-free; it is not
  any more, and the residue is now precisely the **non-affine** case.
  `hasGaloisQuotient_of_isAffine` (`Picard/GaloisQuotientAffineGeneral.lean`) is a
  global `instance` discharging it for `[IsAffine X]`, via transport of
  `isGaloisQuotient_spec` along the equivariant `X.isoSpec`. Measured both ways
  **from a file that imports that module** — the qualification is load-bearing and
  this file is two import hops *below* it, so neither claim can be reproduced here:
  `inferInstance` closes the goal at the formerly hand-built witness
  `hasGaloisQuotient_specF4`, and **fails** for an abstract `ρ` carrying the orbit
  hypothesis without affineness. So the remaining `G2(c)` work is the gluing of
  `Spec (A_U^Γ)` along a stable affine cover — the step the repaired
  representability route actually runs on, since its consumer `J'_r` is glued.
* `affineGaloisQuotientHomEquiv` — **the affine case of the Hom property, proved**:
  for `X' = Spec A` and affine `T = Spec B`,
  `Hom_{Spec K}(T, Spec A^Γ) ≃ Γ-invariant Hom_{Spec L}(T ×_K Spec L, Spec A)`,
  by Speiser descent (`SemilinearAlgebras.invariantAlgHomEquiv`) — never via
  Noether invariant finiteness.

Campaign reference: `G2` of `informal/pic-representability-campaign.md` (consumed by
`G3`/`G4`; curve-agnostic, reusable for `Sym^d`/Albanese).  Sources: Milne, *Jacobian
Varieties* §4 and Kleiman, *The Picard scheme* (FGA explained) §4 use exactly this
finite Galois quotient to descend `Pic_{C_{k'}/k'}` to `k`; the affine heart is
Speiser's theorem.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicJacobian.GaloisDescent

/-! ## Spec of a ring action -/

section SpecAut

variable (G : Type*) [Group G] (A : Type u) [CommRing A] [MulSemiringAction G A]

lemma toRingHom_comp (γ τ : G) :
    (MulSemiringAction.toRingHom G A γ).comp (MulSemiringAction.toRingHom G A τ)
      = MulSemiringAction.toRingHom G A (γ * τ) :=
  RingHom.ext fun x => (mul_smul γ τ x).symm

lemma toRingHom_one : MulSemiringAction.toRingHom G A (1 : G) = RingHom.id A :=
  RingHom.ext fun x => one_smul G x

/-- A group acting on a commutative ring by ring automorphisms acts on `Spec A` by
scheme automorphisms: `γ` acts by `Spec (γ⁻¹ • ·)`.  The inversion is forced jointly
by the contravariance of `Spec` and the `Aut` group law, so that `toSpecAut` is a
group **homomorphism** (not an anti-homomorphism). -/
noncomputable def toSpecAut : G →* Aut (Spec (CommRingCat.of A)) :=
  MonoidHom.mk'
    (fun γ =>
      { hom := Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A γ⁻¹))
        inv := Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A γ))
        hom_inv_id := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, toRingHom_comp,
            inv_mul_cancel, toRingHom_one, CommRingCat.ofHom_id, Spec.map_id]
        inv_hom_id := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, toRingHom_comp,
            mul_inv_cancel, toRingHom_one, CommRingCat.ofHom_id, Spec.map_id] })
    (fun γ τ => by
      refine Iso.ext ?_
      change Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A (γ * τ)⁻¹))
        = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A τ⁻¹)) ≫
          Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A γ⁻¹))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, toRingHom_comp, ← mul_inv_rev])

lemma toSpecAut_hom (γ : G) :
    (toSpecAut G A γ).hom
      = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A γ⁻¹)) := rfl

lemma toSpecAut_mul_hom (γ τ : G) :
    (toSpecAut G A (γ * τ)).hom = (toSpecAut G A τ).hom ≫ (toSpecAut G A γ).hom := by
  rw [map_mul]; rfl

lemma toSpecAut_inv_hom (γ : G) :
    (toSpecAut G A γ⁻¹).hom = (toSpecAut G A γ).inv := by
  rw [map_inv]; rfl

@[reassoc (attr := simp)]
lemma toSpecAut_hom_inv_hom (γ : G) :
    (toSpecAut G A γ).hom ≫ (toSpecAut G A γ⁻¹).hom = 𝟙 _ := by
  rw [toSpecAut_inv_hom, Iso.hom_inv_id]

@[reassoc (attr := simp)]
lemma toSpecAut_inv_hom_hom (γ : G) :
    (toSpecAut G A γ⁻¹).hom ≫ (toSpecAut G A γ).hom = 𝟙 _ := by
  rw [toSpecAut_inv_hom, Iso.inv_hom_id]

end SpecAut

/-! ## Semilinear Galois actions on schemes over `Spec L` -/

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- A **semilinear `Gal(L/K)`-action** on a scheme `X` over `Spec L` (campaign
`G2(a)`): a group homomorphism into scheme automorphisms of the total space, each
automorphism lying in a commuting square over the corresponding Galois automorphism
`Spec γ` of the base.  (`X` is *not* acted on over `Spec L` — only the composite
descends to `Spec K`; this is exactly Kleiman/Milne's "descent datum" for the finite
Galois cover `Spec L → Spec K`.) -/
structure SemilinearGalAction (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of L)) where
  /-- The action by scheme automorphisms. -/
  act : (L ≃ₐ[K] L) →* Aut X
  /-- Each automorphism covers the Galois action `Spec γ` on the base. -/
  compat (γ : L ≃ₐ[K] L) :
    (act γ).hom ≫ f = f ≫ (toSpecAut (L ≃ₐ[K] L) L γ).hom

namespace SemilinearGalAction

variable {K L}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}

/-- Equivariance of a morphism between two semilinearly-acted schemes over `Spec L`. -/
def IsEquivariant {X' : Scheme.{u}} {f' : X' ⟶ Spec (CommRingCat.of L)}
    (ρ : SemilinearGalAction K L X f) (ρ' : SemilinearGalAction K L X' f')
    (h : X ⟶ X') : Prop :=
  ∀ γ : L ≃ₐ[K] L, (ρ.act γ).hom ≫ h = h ≫ (ρ'.act γ).hom

/-- The `Γ`-orbit of a point of `X` under a semilinear action. -/
def orbit (ρ : SemilinearGalAction K L X f) (x : X) : Set X :=
  Set.range fun γ : L ≃ₐ[K] L => (ρ.act γ).hom.base x

/-- **Orbit-in-affine hypothesis** (campaign `G2`, audit item 8): every `Γ`-orbit is
contained in an affine open.  This hypothesis is **essential** (Hironaka trap — see
the module docstring): without it the quotient exists only as an algebraic space.
For finite Galois `L/K` every orbit is finite, so this is the standard EGA II 4.5.4
hypothesis; it holds e.g. for quasi-projective `X` (finite point sets of
quasi-projective schemes lie in affine opens) and is supplied to the campaign
consumer by the Γ-stable `V_Σ` covers of `J5`. -/
class OrbitsInAffineOpen (ρ : SemilinearGalAction K L X f) : Prop where
  exists_affineOpen (x : X) :
    ∃ U : X.affineOpens, ∀ γ : L ≃ₐ[K] L, (ρ.act γ).hom.base x ∈ U.1

/-- A `Γ`-stable open of `X`. -/
def IsStableOpen (ρ : SemilinearGalAction K L X f) (U : X.Opens) : Prop :=
  ∀ γ : L ≃ₐ[K] L, (ρ.act γ).hom ⁻¹ᵁ U = U

end SemilinearGalAction

/-- Campaign `G2(a)`, EGA II 4.5.4 pattern: a `Γ`-stable affine refinement — every
point admits a `Γ`-stable affine open neighbourhood.

**This was a gate and is not one any more; the words "no instances" stood here after
its own discharge landed** (`review-ajc`, 2026-07-29 — and they survived one file away
from the module-header correction of the same error, which is why they are struck in
the class docstring too). `hasStableAffineCover_of_orbitsInAffineOpen`
(`Picard/StableAffineCover.lean:279`) is a global `instance` deriving this class from
`[FiniteDimensional K L] [IsGalois K L] [ρ.OrbitsInAffineOpen]` — the sanctioned
discharge, and the only one. Measured: `infer_instance` succeeds for an *abstract* `ρ`
carrying the orbit hypothesis and fails without it, so the orbit hypothesis is exactly
its price. `HasGaloisQuotient` below is the gate that remains (it fails to synthesize
even with the orbit hypothesis *and* this class in scope).

The historical discharge recipe, kept because it records what the proof cost:
from `OrbitsInAffineOpen`, given an orbit inside affine `U`, prime avoidance produces
`s ∈ Γ(U, 𝒪)` with the orbit inside `D(s) ⊆ ⋂_γ γU`, and the product `∏_γ γ(s)` cuts
out a `Γ`-stable affine basic open — a genuine multi-session lemma (walls: transport
of sections along the action isomorphisms, and basic-open-affineness bookkeeping),
pinned here per the campaign plan ("may be pinned as a separate gated statement if it
walls"). -/
class HasStableAffineCover {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (ρ : SemilinearGalAction K L X f) : Prop where
  exists_stable_affineOpen (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ρ.IsStableOpen U

/-! ## The affine model (conventions validator) -/

section AffineModel

variable (A : Type u) [CommRing A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]
variable [MulSemiringAction (L ≃ₐ[K] L) A]

/-- The affine model of a semilinear Galois action: a `MulSemiringAction Γ A` that is
`IsSemilinear K L A` induces a semilinear action on `Spec A` over `Spec L`.  This
validates the sign/direction conventions of `SemilinearGalAction` constructively. -/
noncomputable def specSemilinearGalAction [IsSemilinear K L A] :
    SemilinearGalAction K L (Spec (CommRingCat.of A))
      (Spec.map (CommRingCat.ofHom (algebraMap L A))) where
  act := toSpecAut (L ≃ₐ[K] L) A
  compat γ := by
    rw [toSpecAut_hom, toSpecAut_hom, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact SemilinearAction.smul_algebraMap K L A γ⁻¹ x

end AffineModel

/-! ## The canonical action on a base change `T ×_{Spec K} Spec L` -/

section PullbackAction

/-- Each Galois automorphism of `Spec L` is a morphism over `Spec K`. -/
lemma toSpecAut_hom_comp_baseMap (γ : L ≃ₐ[K] L) :
    (toSpecAut (L ≃ₐ[K] L) L γ).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K L))
      = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  rw [toSpecAut_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact AlgEquiv.commutes γ⁻¹ x

variable {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of K))

/-- The single automorphism of the base change `Y ×_{Spec K} Spec L` induced by
`γ` through the second factor. -/
noncomputable abbrev pullbackGalMap (γ : L ≃ₐ[K] L) :
    pullback g (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  pullback.map g _ g _ (𝟙 Y) (toSpecAut (L ≃ₐ[K] L) L γ).hom (𝟙 _)
    (by simp) (by rw [Category.comp_id, toSpecAut_hom_comp_baseMap])

@[reassoc (attr := simp)]
lemma pullbackGalMap_fst (γ : L ≃ₐ[K] L) :
    pullbackGalMap K L g γ ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      = pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have h : pullbackGalMap K L g γ ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      = pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫ 𝟙 Y :=
    pullback.lift_fst _ _ _
  rw [h, Category.comp_id]

@[reassoc (attr := simp)]
lemma pullbackGalMap_snd (γ : L ≃ₐ[K] L) :
    pullbackGalMap K L g γ ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      = pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫
          (toSpecAut (L ≃ₐ[K] L) L γ).hom :=
  pullback.lift_snd _ _ _

/-- The canonical semilinear Galois action on a base change
`Y ×_{Spec K} Spec L → Spec L` through the second factor.  This is the reference
action used to *state* equivariance of descent isomorphisms and the `T`-points
property. -/
noncomputable def pullbackSemilinearGalAction :
    SemilinearGalAction K L
      (pullback g (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap K L)))) where
  act := MonoidHom.mk'
    (fun γ =>
      { hom := pullbackGalMap K L g γ
        inv := pullbackGalMap K L g γ⁻¹
        hom_inv_id := by
          apply pullback.hom_ext
          · rw [Category.assoc, pullbackGalMap_fst, pullbackGalMap_fst, Category.id_comp]
          · rw [Category.assoc, pullbackGalMap_snd, pullbackGalMap_snd_assoc,
              toSpecAut_hom_inv_hom, Category.comp_id, Category.id_comp]
        inv_hom_id := by
          apply pullback.hom_ext
          · rw [Category.assoc, pullbackGalMap_fst, pullbackGalMap_fst, Category.id_comp]
          · rw [Category.assoc, pullbackGalMap_snd, pullbackGalMap_snd_assoc,
              toSpecAut_inv_hom_hom, Category.comp_id, Category.id_comp] })
    (fun γ τ => by
      refine Iso.ext ?_
      change pullbackGalMap K L g (γ * τ)
        = pullbackGalMap K L g τ ≫ pullbackGalMap K L g γ
      apply pullback.hom_ext
      · rw [Category.assoc, pullbackGalMap_fst, pullbackGalMap_fst, pullbackGalMap_fst]
      · rw [Category.assoc, pullbackGalMap_snd, pullbackGalMap_snd,
          pullbackGalMap_snd_assoc, toSpecAut_mul_hom])
  compat γ := pullback.lift_snd _ _ _

@[simp] lemma pullbackSemilinearGalAction_act_hom (γ : L ≃ₐ[K] L) :
    ((pullbackSemilinearGalAction K L g).act γ).hom = pullbackGalMap K L g γ := rfl

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))

/-- The base change to `Spec L` of a morphism over `Spec K`. -/
noncomputable abbrev pullbackBaseChange (u : T ⟶ Y) (hu : u ≫ g = t) :
    pullback t (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  pullback.map t _ g _ u (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hu]) (by simp)

@[reassoc (attr := simp)]
lemma pullbackBaseChange_fst (u : T ⟶ Y) (hu : u ≫ g = t) :
    pullbackBaseChange K L g t u hu ≫
        pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      = pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫ u :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullbackBaseChange_snd (u : T ⟶ Y) (hu : u ≫ g = t) :
    pullbackBaseChange K L g t u hu ≫
        pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      = pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have h : pullbackBaseChange K L g t u hu ≫
        pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      = pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫ 𝟙 _ :=
    pullback.lift_snd _ _ _
  rw [h, Category.comp_id]

variable {K L}

/-- Naturality of the base-change action: base changes of morphisms over `Spec K`
are equivariant for the canonical actions. -/
lemma pullbackGalMap_naturality (u : T ⟶ Y) (hu : u ≫ g = t) (γ : L ≃ₐ[K] L) :
    pullbackGalMap K L t γ ≫ pullbackBaseChange K L g t u hu
      = pullbackBaseChange K L g t u hu ≫ pullbackGalMap K L g γ := by
  apply pullback.hom_ext <;> simp

/-- The base change of a morphism over `Spec K`, composed with an equivariant
morphism, is equivariant.  (The "easy direction" of the `T`-points property of a
Galois quotient: descended morphisms induce equivariant ones.) -/
theorem SemilinearGalAction.isEquivariant_pullbackBaseChange_comp
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (ρ : SemilinearGalAction K L X f)
    {e : pullback g (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ X}
    (he : (pullbackSemilinearGalAction K L g).IsEquivariant ρ e)
    (u : T ⟶ Y) (hu : u ≫ g = t) :
    (pullbackSemilinearGalAction K L t).IsEquivariant ρ
      (pullbackBaseChange K L g t u hu ≫ e) := by
  intro γ
  rw [pullbackSemilinearGalAction_act_hom, ← Category.assoc,
    pullbackGalMap_naturality g t u hu γ, Category.assoc, Category.assoc]
  exact congrArg _ (he γ)

end PullbackAction

/-! ## The quotient predicate and the existence gate -/

section Quotient

variable {K L}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}

/-- `(Y, g)` is a **finite Galois quotient** of the semilinearly-acted `(X, f, ρ)`
(campaign `G2`): there is an isomorphism `e : Y ×_{Spec K} Spec L ≅ X` which is

1. over `Spec L`,
2. `Γ`-equivariant for the canonical base-change action, and
3. universal: every equivariant morphism `T ×_{Spec K} Spec L ⟶ X` over `Spec L`
   descends **uniquely** to `T ⟶ Y` over `Spec K` — this clause is exactly
   `Hom_K(T, Y) ≅ Hom_L(T_L, X)^Γ` (the inverse bijection direction is
   `SemilinearGalAction.isEquivariant_pullbackMap_comp`). -/
def IsGaloisQuotient (ρ : SemilinearGalAction K L X f) {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of K)) : Prop :=
  ∃ e : pullback g (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≅ X,
    e.hom ≫ f = pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧
    (pullbackSemilinearGalAction K L g).IsEquivariant ρ e.hom ∧
    ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of K))
      (h : pullback t (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ X),
      h ≫ f = pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap K L))) →
      (pullbackSemilinearGalAction K L t).IsEquivariant ρ h →
      ∃! u : {u : T ⟶ Y // u ≫ g = t},
        pullbackBaseChange K L g t u.1 u.2 ≫ e.hom = h

/-- GATE (campaign `G2`) — existence of the finite Galois quotient under the
orbit-in-affine hypothesis.

**No longer instance-free, and the qualification matters: it is discharged on the
AFFINE locus** (`hasGaloisQuotient_of_isAffine`,
`Picard/GaloisQuotientAffineGeneral.lean`, a global `instance`), so for `[IsAffine X]`
this class synthesizes outright and subsumes the former single-object witness
`hasGaloisQuotient_specF4`. Both measurements below are **from a file importing that
module**, which this one is two hops below, so do not expect to reproduce either
here: `inferInstance` closes the `𝔽₄` goal, and — the other direction — **fails** for
an abstract `ρ` carrying the orbit hypothesis but not affineness, so the remaining
content is exactly the non-affine case.

Intended discharge of what is left (`G2(c)`): a `Γ`-stable affine cover
(`HasStableAffineCover`, from `OrbitsInAffineOpen` via the EGA II 4.5.4 pattern),
`Spec (A_U^Γ)` on each stable affine piece by Speiser descent
(`SemilinearAlgebras.descentAlgEquiv` — the affine Hom property is
`affineGaloisQuotientHomEquiv` below; the per-chart *quotient* is now the affine
instance above rather than something to re-derive), glued via `Scheme.GlueData`.
The orbit hypothesis is **essential** for that step (Hironaka trap — module
docstring), and the affine discharge does not weaken it: an affine `X` has no room
for the trap. -/
class HasGaloisQuotient [FiniteDimensional K L] [IsGalois K L]
    (ρ : SemilinearGalAction K L X f) [ρ.OrbitsInAffineOpen] : Prop where
  exists_quotient :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of K)), IsGaloisQuotient ρ g

end Quotient

/-! ## The left-factor Galois action on `L ⊗[K] B` -/

section TensorAction

variable (B : Type u) [CommRing B] [Algebra K B]

/-- The left-factor Galois action `γ ↦ γ ⊗ id` on a base change `L ⊗[K] B`.
Scoped instance: mathlib carries no action of `L ≃ₐ[K] L` on tensor products, so no
diamond can arise; still scoped for hygiene since for `B = L` the *right*-factor
action is equally natural. -/
noncomputable scoped instance instMulSemiringActionTensor :
    MulSemiringAction (L ≃ₐ[K] L) (L ⊗[K] B) where
  smul γ x := Algebra.TensorProduct.map (γ : L →ₐ[K] L) (AlgHom.id K B) x
  one_smul x := by
    change Algebra.TensorProduct.map _ _ x = x
    rw [show ((1 : L ≃ₐ[K] L) : L →ₐ[K] L) = AlgHom.id K L from rfl,
      Algebra.TensorProduct.map_id, AlgHom.coe_id, id_eq]
  mul_smul γ τ x := by
    change Algebra.TensorProduct.map _ _ x
      = Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ x)
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
    rfl
  smul_zero γ := map_zero _
  smul_add γ := map_add _
  smul_one γ := map_one _
  smul_mul γ := map_mul _

@[simp] lemma galTensor_smul_def (γ : L ≃ₐ[K] L) (x : L ⊗[K] B) :
    γ • x = Algebra.TensorProduct.map (γ : L →ₐ[K] L) (AlgHom.id K B) x := rfl

/-- The left-factor Galois action on `L ⊗[K] B` is semilinear. -/
instance : IsSemilinear K L (L ⊗[K] B) := by
  refine SemilinearAction.isSemilinear_of_smul_algebraMap K L _ fun γ a => ?_
  change Algebra.TensorProduct.map (γ : L →ₐ[K] L) (AlgHom.id K B)
      (algebraMap L (L ⊗[K] B) a) = algebraMap L (L ⊗[K] B) (γ a)
  have h : ∀ c : L, algebraMap L (L ⊗[K] B) c = c ⊗ₜ[K] (1 : B) := fun c => rfl
  rw [h, h, Algebra.TensorProduct.map_tmul, map_one]
  rfl

end TensorAction

/-! ## Spec-side Hom bookkeeping -/

section SpecHoms

variable (R S₁ S₂ : Type u) [CommRing R] [CommRing S₁] [CommRing S₂]
variable [Algebra R S₁] [Algebra R S₂]

/-- Morphisms `Spec S₂ ⟶ Spec S₁` over `Spec R` are `R`-algebra maps `S₁ → S₂`
(affine relative Spec adjunction, triangle form). -/
noncomputable def specOverEquivAlgHom :
    {t : Spec (CommRingCat.of S₂) ⟶ Spec (CommRingCat.of S₁) //
      t ≫ Spec.map (CommRingCat.ofHom (algebraMap R S₁))
        = Spec.map (CommRingCat.ofHom (algebraMap R S₂))} ≃ (S₁ →ₐ[R] S₂) where
  toFun t :=
    { toRingHom := (Spec.preimage t.1).hom
      commutes' := fun r => by
        have h := t.2
        rw [← Spec.map_preimage t.1, ← Spec.map_comp] at h
        have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
        rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at h2
        exact DFunLike.congr_fun h2 r }
  invFun φ :=
    ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun r => φ.commutes r)⟩
  left_inv t := by
    apply Subtype.ext
    change Spec.map (CommRingCat.ofHom (Spec.preimage t.1).hom) = t.1
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  right_inv φ := by
    apply AlgHom.ext
    intro x
    change (Spec.preimage (Spec.map (CommRingCat.ofHom φ.toRingHom))).hom x = φ x
    rw [Spec.preimage_map]
    rfl

end SpecHoms

/-! ## The affine case of the Hom property -/

section AffineHomProperty

variable (A : Type u) [CommRing A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]
variable [MulSemiringAction (L ≃ₐ[K] L) A] [IsSemilinear K L A]
variable [FiniteDimensional K L] [IsGalois K L]
variable (B : Type u) [CommRing B] [Algebra K B]

open SemilinearAction

omit [Algebra K A] [IsScalarTower K L A] [IsSemilinear K L A]
  [FiniteDimensional K L] [IsGalois K L] in
/-- Equivariance of an `L`-algebra map matches equivariance of the corresponding
morphism of affine schemes (with the `toSpecAut` actions on both sides). -/
lemma isEquivariantAlgHom_iff_specMap (φ : A →ₐ[L] L ⊗[K] B) :
    IsEquivariantAlgHom K L A B φ ↔
      ∀ γ : L ≃ₐ[K] L,
        (toSpecAut (L ≃ₐ[K] L) (L ⊗[K] B) γ).hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)
          = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (toSpecAut (L ≃ₐ[K] L) A γ).hom := by
  have key : ∀ γ : L ≃ₐ[K] L,
      ((toSpecAut (L ≃ₐ[K] L) (L ⊗[K] B) γ).hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)
          = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (toSpecAut (L ≃ₐ[K] L) A γ).hom)
        ↔ ∀ x : A, γ⁻¹ • φ x = φ (γ⁻¹ • x) := by
    intro γ
    rw [toSpecAut_hom, toSpecAut_hom, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    constructor
    · intro h
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
      rw [CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at h2
      exact fun x => DFunLike.congr_fun h2 x
    · intro h
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext h)
  constructor
  · intro hφ γ
    rw [key γ]
    intro x
    rw [galTensor_smul_def, ← hφ γ⁻¹ x]
  · intro hs γ x
    have h3 := (key γ⁻¹).mp (hs γ⁻¹) x
    rw [inv_inv, galTensor_smul_def] at h3
    exact h3.symm

open Algebra in
/-- **The affine case of the Galois quotient Hom property** (campaign `G2(b)`,
scheme form, affine `T`).  For `X' = Spec A` with a semilinear `Γ`-action and any
affine `T = Spec B` over `Spec K` (with `T ×_{Spec K} Spec L = Spec (L ⊗[K] B)`):
morphisms `T ⟶ Spec (A^Γ)` over `Spec K` correspond to `Γ`-equivariant morphisms
`Spec (L ⊗[K] B) ⟶ Spec A` over `Spec L`.  Proved by Speiser descent
(`invariantAlgHomEquiv`), never via invariant finiteness. -/
noncomputable def affineGaloisQuotientHomEquiv :
    {t : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (invariantsSubalgebra K L A)) //
      t ≫ Spec.map (CommRingCat.ofHom (algebraMap K (invariantsSubalgebra K L A)))
        = Spec.map (CommRingCat.ofHom (algebraMap K B))} ≃
    {h : Spec (CommRingCat.of (L ⊗[K] B)) ⟶ Spec (CommRingCat.of A) //
      (h ≫ Spec.map (CommRingCat.ofHom (algebraMap L A))
          = Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] B)))) ∧
      ∀ γ : L ≃ₐ[K] L,
        (toSpecAut (L ≃ₐ[K] L) (L ⊗[K] B) γ).hom ≫ h
          = h ≫ (toSpecAut (L ≃ₐ[K] L) A γ).hom} :=
  ((specOverEquivAlgHom K (invariantsSubalgebra K L A) B).trans
    ((invariantAlgHomEquiv K L A B).trans
      ((Equiv.subtypeEquiv (specOverEquivAlgHom L A (L ⊗[K] B)).symm
        (fun φ => isEquivariantAlgHom_iff_specMap K L A B φ)).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter _ _))))

end AffineHomProperty

end AlgebraicJacobian.GaloisDescent
