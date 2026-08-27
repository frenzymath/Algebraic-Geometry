/-
Copyright (c) 2026 Axel Delaval. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval
-/
import AlgebraicJacobian.Picard.PicEtDescentGoal

/-!
# `G1` IS FREE AT THE CANONICAL ACTION: the invariance match, discharged

`AJC.picrep.etale-rep.invariance`.

## What this file removes

`Picard/PicEtDescentGoal.lean` states the descent goal — a `k'`-side representation
of `picEt (C_{k'})` plus a Galois quotient plus `hcov` plus a predicate match
`IsInvariantMatch` yields `(picEt C).RepresentableBy Y` over `k` — and carries that
match as an **explicit undischarged hypothesis**, identified there as what campaign
`G1` owes.

**At the canonical action it is not a hypothesis at all.** `isInvariantMatch_canonical`
proves `IsInvariantMatch C rep (semilinearGalActionOfRepresentableBy C rep) T` for
every test `T`, with **no hypothesis beyond `rep` and the curve's own binders**: no
finiteness, no separability, no `IsGalois`, no rational point, no condition on the
Galois group. So `G1` leaves this route, and the descent goal's inputs drop from four
to three: `rep`, the Galois quotient, and `hcov`.

## Why it is free — the reason, not just the fact

The two predicates being matched are *not independent conditions on one object*.
`IsInvariantMatch` asks that

* `(rep.homEquiv.symm c).left` is **equivariant** for the action `ρ`, and
* the transported class is **`Γ`-invariant** for the twist action on `picEt C`

agree. At the canonical `ρ = semilinearGalActionOfRepresentableBy C rep`, the
`γ`-component of the action *is* `twistMor C rep γ`, which is **defined** by
transporting the functor action `galoisActionPicEt` along `rep`. So both sides are
images of one and the same functor-level statement, and the match is an identity
rather than a coincidence. Three steps, each free:

1. `isEquivariant_iff_galTwistMor` — equivariance of the underlying scheme map is the
   same equation read in the slice over `Spec k'` (`Over.OverMorphism.ext` both ways).
   `galTwistMor` is that slice packaging of `pullbackGalMap`, and it is the `k'`-side
   partner of `PicEtGaloisBridge`'s `k`-slice `twistTest` — `twistTest T γ⁻¹` is
   `pullbackGalMap … γ` on underlying schemes, which is *already* recorded as `rfl` at
   `I-1455`, and `twistTest_eq_restrictTest_galTwistMor` is the slice-level form.
2. `homEquiv_twist_comp` — applying `rep.homEquiv` to the square's right-hand side
   gives `(galoisActionPicEt C γ).inv` applied to `rep.homEquiv φ`. This is
   `homEquiv_twistMor` plus **naturality of the action at `φ.op`**, and it is the step
   that makes the whole thing free: `twistMor` was built from that natural
   transformation, so naturality is exactly what un-builds it.
3. `crossBaseIso_galoisActionPicEt_inv` — transporting along `picEt_crossBaseIso`
   turns the inverse action into `picEt C` applied to
   `restrictTest_twistTestFunctor_iso`, whose components are the **identity** on
   underlying schemes. Iso cancellation; the cross-base identification's own
   `inv_hom_id_app`.

Composing, equivariance at `γ` is invariance at `γ⁻¹`; quantifying over the group,
which both predicates do, makes them equal. `Gal(k'/k)` is a group, so the
reindexing `γ ↦ γ⁻¹` is a bijection and no hypothesis on it is needed.

## What this does NOT do

* It closes **no** `sorry`. `rep` is still the campaign's undischarged output, and
  clause (1) field 1 of `Scheme.fgaPicardRepresentability` is witnessed for **no**
  curve. This file is verified with that theorem as a `sorryAx` control.
* The remaining two inputs of the descent goal are untouched: `IsGaloisQuotient` at a
  glued non-affine `X'` (`pic-f`'s row) and `hcov` at a nontrivial Galois level
  (`pic-a`'s row). Nothing here makes either cheaper.
* It does **not** rescue the non-vacuity problem `PicEtDescentGoal.lean` records for
  the *pair* `(hcov, IsInvariantMatch)`. It resolves that problem for the match by
  removing it — a hypothesis that is never assumed cannot be vacuously satisfied —
  but `hcov`'s only exhibited witness site still trivialises the conclusion, and that
  half is unchanged.
* It does **not** subsume `isInvariantMatch_of_subsingleton`. **An earlier revision of
  this docstring said it did — "the degenerate case of a fact that holds at every
  extension" — and that is false** (fresh-context audit). That lemma quantifies over an
  **arbitrary** action `ρ`; `isInvariantMatch_canonical` **pins** `ρ` to the canonical
  one. Refuted in one line: `isInvariantMatch_canonical rep T` offered against
  `IsInvariantMatch C rep ρ T` for a bound `ρ` is a type mismatch. The two are
  **incomparable** — this one is more general in the extension, strictly *less* general
  in the action — and that incomparability is intrinsic to discharging a hypothesis by
  *choosing* the object it quantified over. The older lemma is still **load-bearing** at
  its only consumer: `representableBy_picEt_of_degenerate` takes an external `ρ` and
  cannot route through this file without also pinning it.

## "Free" does not mean "empty" — and that is measured, not assumed

The natural misreading of this file is that `IsInvariantMatch` was never a real
condition. **Measured, and it was.** Asserting that the two sides of `IsInvariantMatch`
are *equal as propositions* at the canonical action — `IsEquivariant` of
`(rep.homEquiv.symm c).left` against `IsGalInvariant` of the cross-base-transported
class — and closing it by `rfl` **fails**: "not definitionally equal" (`lake env lean`,
oleans rebuilt first per `I-1057`). Equivariance of a scheme map for a semilinear action
and `Γ`-invariance of a `picEt`-class are distinct propositions about distinct objects.

So `isInvariantMatch_canonical` is a theorem and not `P ↔ P` in a costume; what §2's
three steps do is *identify* two genuinely different statements. "Free" here means **no
hypothesis is needed**, because the identification follows from the *definition* of
`twistMor` — not that there was nothing to prove. Had that `rfl` succeeded, the honest
headline would have been "the `G1` match was never an obligation", and this file would be
bookkeeping; it is recorded because the polarity of that probe is the whole difference.

**And the removal is not a relocation either** — the other half of what a "four inputs
became three" claim owes, since the natural failure is that the deleted hypothesis
reappears inside a surviving one. Probed: state §4's *predecessor*'s full hypothesis list
(`rep`, `hq`, `hcov`, `hmatch`, `hlft`) and close its conclusion by calling
`seamClauseOne_of_isGaloisQuotient_noMatch rep hq hcov hlft`, discarding `hmatch`. It
elaborates, and the `unusedVariables` linter confirms `hmatch` is never referenced. So the
new hypothesis set is *strictly* smaller — same `hq` at the same pinned action, nothing
migrated into it, nothing hidden in an instance binder. Neither probe was implied by the
green build; both were cheap.
* Per `I-0491` there is no `HasRationalPoint` binder anywhere in this file.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicJacobian.GaloisDescent

namespace AlgebraicGeometry

namespace Scheme

namespace PicScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-! ## §1. The `k'`-slice packaging of the base-change twist

`FiniteGaloisQuotient.lean`'s `pullbackGalMap` is a bare scheme map and
`SemilinearGalAction.IsEquivariant` is stated about bare scheme maps, while `picEt`
consumes slice morphisms. This section supplies the two bridges, both formal. -/

/-- **The `γ`-twist of a base-changed test, in the slice over `Spec k'`.**

Underlying map `pullbackGalMap k k' T.hom γ`; the slice condition is that map's own
`pullbackGalMap_snd`, so it is a morphism *into* `baseTest T` **from its `γ`-twist* —
which is the semilinearity, in the shape `twistMor` also has. -/
noncomputable def galTwistMor (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    (twistTestFunctor (k := k) γ).obj (baseTest (k' := k') T) ⟶ baseTest (k' := k') T :=
  Over.homMk (pullbackGalMap k k' T.hom γ) (pullbackGalMap_snd k k' T.hom γ)

@[simp] theorem galTwistMor_left (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    (galTwistMor T γ).left = pullbackGalMap k k' T.hom γ := rfl

/-- Every component of `restrictTest_twistTestFunctor_iso`'s **inverse** is the
identity on underlying schemes, like its `hom` (`..._hom_app_left`). -/
theorem restrictTest_twistTestFunctor_iso_inv_app_left (γ : k' ≃ₐ[k] k')
    (D : Over (Spec (CommRingCat.of k'))) :
    ((restrictTest_twistTestFunctor_iso (k := k) γ).inv.app D).left = 𝟙 D.left := by
  have h := congrArg Over.Hom.left
    ((restrictTest_twistTestFunctor_iso (k := k) γ).hom_inv_id_app D)
  rw [Over.comp_left, restrictTest_twistTestFunctor_iso_hom_app_left] at h
  have hfixed : @Eq (D.left ⟶ D.left)
      (𝟙 D.left ≫ ((restrictTest_twistTestFunctor_iso (k := k) γ).inv.app D).left)
      (𝟙 D.left) := h
  rw [Category.id_comp] at hfixed
  exact hfixed

/-- **The two spellings of the twist meet**: `PicEtGaloisBridge`'s `k`-slice
`twistTest T γ⁻¹` is the identity-underlying comparison followed by the restriction
of this file's `k'`-slice `galTwistMor T γ`.

The inverse on one side is not a choice: `toSpecAut` acts by `Spec (γ⁻¹ • ·)`, so the
`γ`-component of `pullbackGalMap` twists the base by `γ⁻¹`, and `I-1455` already
records the underlying-scheme identity as `rfl`. This lemma is the slice form, which
is what `picEt` can be applied to. -/
theorem twistTest_eq_restrictTest_galTwistMor
    (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    twistTest (k' := k') T γ⁻¹
      = (restrictTest_twistTestFunctor_iso (k := k) γ).inv.app (baseTest (k' := k') T)
          ≫ (restrictTest k k').map (galTwistMor T γ) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, restrictTest_twistTestFunctor_iso_inv_app_left,
    Over.map_map_left, galTwistMor_left]
  have hfixed : @Eq (Limits.pullback T.hom (specMapAlgebra k k')
      ⟶ Limits.pullback T.hom (specMapAlgebra k k'))
      (𝟙 _ ≫ pullbackGalMap k k' T.hom γ) (pullbackGalMap k k' T.hom γ) :=
    Category.id_comp _
  exact hfixed.symm

/-! ## §2. The three steps, each free -/

section Steps

variable {C : Over (Spec (CommRingCat.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  {X' : Over (Spec (CommRingCat.of k'))}
  (rep : (picEt (Scheme.baseChangeField C k')).RepresentableBy X')

set_option maxHeartbeats 1000000 in
-- Heartbeat headroom: the `Over`/`pullback` coercion chain of `baseTest` unfolded
-- against `IsEquivariant`'s bare-scheme spelling, as in `PicEtDescentGoal`'s §2b.
/-- **Step 1: equivariance is a slice equation.**

`SemilinearGalAction.IsEquivariant` at the canonical action unfolds to
`pullbackGalMap … γ ≫ φ.left = φ.left ≫ (twistMor C rep γ).left` for each `γ`, and
that is the underlying map of a square in the slice over `Spec k'`. Both directions
are `Over` extensionality — the slice condition carries no further content because
both sides already lie over `Spec k'`. -/
theorem isEquivariant_iff_galTwistMor (T : Over (Spec (CommRingCat.of k)))
    (φ : baseTest (k' := k') T ⟶ X') :
    (pullbackSemilinearGalAction k k' T.hom).IsEquivariant
        (semilinearGalActionOfRepresentableBy C rep) φ.left
      ↔ ∀ γ : k' ≃ₐ[k] k',
          galTwistMor T γ ≫ φ
            = (twistTestFunctor (k := k) γ).map φ ≫ twistMor C rep γ := by
  constructor
  · intro h γ; exact Over.OverMorphism.ext (h γ)
  · intro h γ; exact congrArg Over.Hom.left (h γ)

set_option maxHeartbeats 1000000 in
-- Heartbeat headroom: the `Over`/`pullback`/`baseTest` coercion chain is unfolded
-- repeatedly against `IsEquivariant`'s and `picEt`'s differing spellings of one
-- object, as in `PicEtDescentGoal.lean`'s §2b. Not a slow proof: each is a rewrite
-- chain, but elaborating the statement costs the default budget on its own.
/-- **Step 2, the step that makes `G1` free: the square's right-hand side is the
functor action.**

`rep.homEquiv` of `(twistTestFunctor γ).map φ ≫ twistMor C rep γ` is
`(galoisActionPicEt C γ).inv` applied to `rep.homEquiv φ`.

`twistMor` is *defined* as `rep.homEquiv.symm` of the action at the universal class,
so `homEquiv_twistMor` returns that class, `rep.homEquiv_comp` moves the
precomposition to `picEt`, and **naturality of `(galoisActionPicEt C γ).inv` at
`φ.op`** slides the action past it. No geometry, and nothing about `C` beyond its
binders: the content is that the twist at the representing object was built from a
natural transformation. -/
theorem homEquiv_twist_comp (T : Over (Spec (CommRingCat.of k)))
    (φ : baseTest (k' := k') T ⟶ X') (γ : k' ≃ₐ[k] k') :
    rep.homEquiv ((twistTestFunctor (k := k) γ).map φ ≫ twistMor C rep γ)
      = (galoisActionPicEt C γ).inv.app (op (baseTest (k' := k') T))
          (rep.homEquiv φ) := by
  have hnat := NatTrans.naturality_apply (galoisActionPicEt C γ).inv φ.op
    (rep.homEquiv (𝟙 X'))
  rw [rep.homEquiv_comp, homEquiv_twistMor, rep.homEquiv_eq φ]
  exact hnat.symm

set_option maxHeartbeats 1000000 in
-- Heartbeat headroom: the `Over`/`pullback`/`baseTest` coercion chain is unfolded
-- repeatedly against `IsEquivariant`'s and `picEt`'s differing spellings of one
-- object, as in `PicEtDescentGoal.lean`'s §2b. Not a slow proof: each is a rewrite
-- chain, but elaborating the statement costs the default budget on its own.
/-- **Step 3: the inverse action, transported across the cross-base identification,
is `picEt C` applied to an identity-underlying comparison.**

`galoisActionPicEt` is `galoisActionRestricted` conjugated by `picEt_crossBaseIso`, so
transporting back cancels one conjugation (`Iso.inv_hom_id_app`) and leaves the
restricted action, which `galoisActionRestricted_inv_app` computes as `picEt C` applied
to `restrictTest_twistTestFunctor_iso`. -/
theorem crossBaseIso_galoisActionPicEt_inv (D : Over (Spec (CommRingCat.of k')))
    (γ : k' ≃ₐ[k] k')
    (c : (picEt (Scheme.baseChangeField C k')).obj (op D)) :
    (picEt_crossBaseIso C k').hom.app (op ((twistTestFunctor (k := k) γ).obj D))
        ((galoisActionPicEt C γ).inv.app (op D) c)
      = (picEt C).map ((restrictTest_twistTestFunctor_iso (k := k) γ).hom.app D).op
          ((picEt_crossBaseIso C k').hom.app (op D) c) := by
  rw [galoisActionPicEt_inv_app_apply, galoisActionRestricted_inv_app,
    ← CategoryTheory.comp_apply, Iso.inv_hom_id_app]
  rfl

set_option maxHeartbeats 1000000 in
-- Heartbeat headroom: the `Over`/`pullback`/`baseTest` coercion chain is unfolded
-- repeatedly against `IsEquivariant`'s and `picEt`'s differing spellings of one
-- object, as in `PicEtDescentGoal.lean`'s §2b. Not a slow proof: each is a rewrite
-- chain, but elaborating the statement costs the default budget on its own.
/-- **Precomposing with the identity-underlying comparison is injective on classes,
and cancels.** Both directions of the final iff are this lemma; it is stated once
rather than inlined twice because the two orientations of `Iso.hom_inv_id_app` are
easy to get backwards. -/
theorem picEt_map_comparison_eq_iff (D : Over (Spec (CommRingCat.of k')))
    (γ : k' ≃ₐ[k] k')
    (x y : (picEt C).obj (op ((restrictTest k k').obj D))) :
    (picEt C).map ((restrictTest_twistTestFunctor_iso (k := k) γ).hom.app D).op x
        = (picEt C).map
            ((restrictTest_twistTestFunctor_iso (k := k) γ).hom.app D).op y
      ↔ x = y := by
  have hcancel : ∀ z : (picEt C).obj (op ((restrictTest k k').obj D)),
      (picEt C).map ((restrictTest_twistTestFunctor_iso (k := k) γ).inv.app D).op
          ((picEt C).map
            ((restrictTest_twistTestFunctor_iso (k := k) γ).hom.app D).op z) = z := by
    intro z
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp,
      (restrictTest_twistTestFunctor_iso (k := k) γ).inv_hom_id_app]
    simp
  constructor
  · intro h
    exact (hcancel x).symm.trans ((congrArg ((picEt C).map
      ((restrictTest_twistTestFunctor_iso (k := k) γ).inv.app D).op) h).trans
        (hcancel y))
  · intro h; rw [h]

set_option maxHeartbeats 1000000 in
-- Heartbeat headroom: the `Over`/`pullback`/`baseTest` coercion chain is unfolded
-- repeatedly against `IsEquivariant`'s and `picEt`'s differing spellings of one
-- object, as in `PicEtDescentGoal.lean`'s §2b. Not a slow proof: each is a rewrite
-- chain, but elaborating the statement costs the default budget on its own.
/-- The same cancellation in the orientation the composite's endgame presents: an
equation against `map (hom) c` is the same as `map (inv)` of the left side being `c`.
`w` is a class on the **twisted** restricted test, which is why this is not a
restatement of `picEt_map_comparison_eq_iff` with substituted variables. -/
theorem picEt_comparison_eq_iff_map_inv (D : Over (Spec (CommRingCat.of k')))
    (γ : k' ≃ₐ[k] k')
    (w : (picEt C).obj (op ((twistTestFunctor (k := k) γ ⋙ restrictTest k k').obj D)))
    (c : (picEt C).obj (op ((restrictTest k k').obj D))) :
    (w = (picEt C).map
          ((restrictTest_twistTestFunctor_iso (k := k) γ).hom.app D).op c)
      ↔ (picEt C).map
            ((restrictTest_twistTestFunctor_iso (k := k) γ).inv.app D).op w = c := by
  have hIH : ∀ z : (picEt C).obj (op ((restrictTest k k').obj D)),
      (picEt C).map ((restrictTest_twistTestFunctor_iso (k := k) γ).inv.app D).op
          ((picEt C).map
            ((restrictTest_twistTestFunctor_iso (k := k) γ).hom.app D).op z) = z := by
    intro z
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp,
      (restrictTest_twistTestFunctor_iso (k := k) γ).inv_hom_id_app]
    simp
  have hHI : ∀ v : (picEt C).obj
        (op ((twistTestFunctor (k := k) γ ⋙ restrictTest k k').obj D)),
      (picEt C).map ((restrictTest_twistTestFunctor_iso (k := k) γ).hom.app D).op
          ((picEt C).map
            ((restrictTest_twistTestFunctor_iso (k := k) γ).inv.app D).op v) = v := by
    intro v
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp,
      (restrictTest_twistTestFunctor_iso (k := k) γ).hom_inv_id_app]
    simp
  constructor
  · intro h; rw [h]; exact hIH c
  · intro h; rw [← h]; exact (hHI w).symm

/-! ## §3. THE MATCH, DISCHARGED -/

set_option maxHeartbeats 1000000 in
-- Heartbeat headroom: the `Over`/`pullback`/`baseTest` coercion chain is unfolded
-- repeatedly against `IsEquivariant`'s and `picEt`'s differing spellings of one
-- object, as in `PicEtDescentGoal.lean`'s §2b. Not a slow proof: each is a rewrite
-- chain, but elaborating the statement costs the default budget on its own.
/-- **Equivariance at `γ` IS invariance at `γ⁻¹`**, per automorphism, with no
hypothesis. This is §1–§3 composed at a single `γ`; the headline below only has to
reindex. -/
theorem galTwistMor_eq_iff_map_twistTest (T : Over (Spec (CommRingCat.of k)))
    (c : (picEt (Scheme.baseChangeField C k')).obj (op (baseTest (k' := k') T)))
    (γ : k' ≃ₐ[k] k') :
    (galTwistMor T γ ≫ rep.homEquiv.symm c
        = (twistTestFunctor (k := k) γ).map (rep.homEquiv.symm c) ≫ twistMor C rep γ)
      ↔ (picEt C).map (twistTest (k' := k') T γ⁻¹).op
            ((picEt_crossBaseIso C k').hom.app (op (baseTest (k' := k') T)) c)
          = (picEt_crossBaseIso C k').hom.app (op (baseTest (k' := k') T)) c := by
  -- Both sides of the slice square become classes under `rep.homEquiv`, injectively.
  rw [← rep.homEquiv.apply_eq_iff_eq (x := galTwistMor T γ ≫ rep.homEquiv.symm c),
    homEquiv_twist_comp, rep.homEquiv_comp, Equiv.apply_symm_apply]
  -- Transport the resulting equation of `picEt (C_{k'})`-classes along the
  -- cross-base iso; it is injective, being an iso's component. `hL` rewrites the
  -- transported left side by naturality at `galTwistMor T γ` and `hR` is step 3.
  have hL := NatTrans.naturality_apply (picEt_crossBaseIso C k').hom
    (galTwistMor T γ).op c
  have hR := crossBaseIso_galoisActionPicEt_inv (C := C)
    (baseTest (k' := k') T) γ c
  have hkey : ((picEt (Scheme.baseChangeField C k')).map (galTwistMor T γ).op c
        = (galoisActionPicEt C γ).inv.app (op (baseTest (k' := k') T)) c)
      ↔ ((picEt C).map ((restrictTest k k').map (galTwistMor T γ)).op
            ((picEt_crossBaseIso C k').hom.app (op (baseTest (k' := k') T)) c)
          = (picEt C).map ((restrictTest_twistTestFunctor_iso (k := k) γ).hom.app
                (baseTest (k' := k') T)).op
              ((picEt_crossBaseIso C k').hom.app (op (baseTest (k' := k') T)) c)) := by
    rw [← Equiv.apply_eq_iff_eq
      ((picEt_crossBaseIso C k').app (op ((twistTestFunctor (k := k) γ).obj
        (baseTest (k' := k') T)))).toEquiv]
    rw [show ((picEt_crossBaseIso C k').app (op ((twistTestFunctor (k := k) γ).obj
        (baseTest (k' := k') T)))).toEquiv
          ((picEt (Scheme.baseChangeField C k')).map (galTwistMor T γ).op c)
        = _ from hL, show ((picEt_crossBaseIso C k').app
          (op ((twistTestFunctor (k := k) γ).obj (baseTest (k' := k') T)))).toEquiv
          ((galoisActionPicEt C γ).inv.app (op (baseTest (k' := k') T)) c)
        = _ from hR]
    exact Iff.rfl
  rw [hkey]
  -- Both sides now carry the comparison, whose components are the identity on
  -- underlying schemes; `picEt_map_comparison_eq_iff` cancels it, and the
  -- left-hand side is `twistTest T γ⁻¹` by §1's bridge.
  rw [twistTest_eq_restrictTest_galTwistMor, op_comp, Functor.map_comp,
    CategoryTheory.comp_apply]
  exact picEt_comparison_eq_iff_map_inv (C := C) (baseTest (k' := k') T) γ _ _

set_option maxHeartbeats 1000000 in
-- Heartbeat headroom: the `Over`/`pullback`/`baseTest` coercion chain is unfolded
-- repeatedly against `IsEquivariant`'s and `picEt`'s differing spellings of one
-- object, as in `PicEtDescentGoal.lean`'s §2b. Not a slow proof: each is a rewrite
-- chain, but elaborating the statement costs the default budget on its own.
/-- **`G1`'S PREDICATE MATCH IS FREE AT THE CANONICAL ACTION.**

For a smooth proper curve `C` over an **arbitrary** field `k`, an **arbitrary**
extension `k'/k`, and **any** representation `rep` of `picEt (C_{k'})`, the
`IsInvariantMatch` hypothesis of `Picard/PicEtDescentGoal.lean` holds at the canonical
semilinear action `semilinearGalActionOfRepresentableBy C rep`, at **every** test.

No finiteness, no separability, no `IsGalois`, no condition on `Gal(k'/k)`, no
rational point. So campaign `G1` is **not** an input of the descent route: the
descent goal's four inputs are three (`rep`, the Galois quotient, `hcov`).

**Why it is free rather than fortunate.** The canonical action's `γ`-component is
`twistMor C rep γ`, which is *defined* by transporting the functor action
`galoisActionPicEt` along `rep`. Equivariance of `(rep.homEquiv.symm c).left` is
therefore not a condition on `c` at all — it is the image under `rep.homEquiv` of the
functor-level equation that invariance also is. `homEquiv_twist_comp` is the step
where that happens, and its content is naturality.

**The reindexing is the only bookkeeping.** Equivariance at `γ` is invariance at
`γ⁻¹` (`galTwistMor_eq_iff_map_twistTest`), because `toSpecAut` acts by
`Spec (γ⁻¹ • ·)`. Both predicates quantify over the whole group and `γ ↦ γ⁻¹` is a
bijection of it, so the two universally-quantified statements coincide — this is where
`Gal(k'/k)` being a *group* is used, and it is all that is used about it.

**This closes no `sorry`.** `rep` remains the campaign's undischarged output and
clause (1) field 1 is witnessed for no curve; see the module docstring for what stays
open, in particular that `hcov`'s non-vacuity is untouched. -/
theorem isInvariantMatch_canonical (T : Over (Spec (CommRingCat.of k))) :
    IsInvariantMatch C rep (semilinearGalActionOfRepresentableBy C rep) T := by
  intro c
  rw [isEquivariant_iff_galTwistMor rep T (rep.homEquiv.symm c)]
  constructor
  · -- equivariance at every `γ` ⟹ invariance at every `γ`: apply the per-`γ`
    -- equivalence at `γ⁻¹` and use `inv_inv`.
    intro h γ
    have := (galTwistMor_eq_iff_map_twistTest rep T c γ⁻¹).mp (h γ⁻¹)
    rwa [inv_inv] at this
  · -- and back, the same reindexing in the other direction.
    intro h γ
    refine (galTwistMor_eq_iff_map_twistTest rep T c γ).mpr ?_
    exact h γ⁻¹

/-! ## §4. THE PAYOFF: the descent goal with `G1` deleted

The theorems of `Picard/PicEtDescentGoal.lean` §5–§6 take `hmatch` as an argument.
Restated here at the canonical action with `hmatch` supplied by §3, so a consumer
never mentions it. These are the forms a lane closing `G2(c)` or `hcov` should aim
at. -/

section Payoff

variable [Algebra.IsSeparable k k'] [Module.Finite k k']

set_option maxHeartbeats 1000000 in
-- Heartbeat headroom: the `Over`/`pullback`/`baseTest` coercion chain is unfolded
-- repeatedly against `IsEquivariant`'s and `picEt`'s differing spellings of one
-- object, as in `PicEtDescentGoal.lean`'s §2b. Not a slow proof: each is a rewrite
-- chain, but elaborating the statement costs the default budget on its own.
/-- **THE DESCENT GOAL, THREE INPUTS.**

A `k'`-scheme `X'` representing `picEt (C_{k'})`, a Galois quotient `Y` over `k` of
the action that representation itself determines, and `hcov` — yield
`(picEt C).RepresentableBy Y`, i.e. field 1 of clause (1) of
`Scheme.fgaPicardRepresentability`, over `k`.

Compare `representableBy_picEt_of_galoisQuotient`, which additionally takes the `G1`
predicate match and an externally-supplied action. Both are gone: the action is free
by `semilinearGalActionOfRepresentableBy` and the match is free by §3. -/
noncomputable def representableBy_picEt_of_galoisQuotient_canonical
    {C : Over (Spec (CommRingCat.of k))}
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    {Y : Over (Spec (CommRingCat.of k))}
    (e : Limits.pullback Y.hom (specMapAlgebra k k') ≅ X'.left)
    (he : e.hom ≫ X'.hom = Limits.pullback.snd Y.hom (specMapAlgebra k k'))
    (heq : (pullbackSemilinearGalAction k k' Y.hom).IsEquivariant
      (semilinearGalActionOfRepresentableBy C rep) e.hom)
    (huniv : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k))
      (h : Limits.pullback t (specMapAlgebra k k') ⟶ X'.left),
      h ≫ X'.hom = Limits.pullback.snd t (specMapAlgebra k k') →
      (pullbackSemilinearGalAction k k' t).IsEquivariant
        (semilinearGalActionOfRepresentableBy C rep) h →
      ∃! u : {u : T ⟶ Y.left // u ≫ Y.hom = t},
        pullbackBaseChange k k' Y.hom t u.1 u.2 ≫ e.hom = h)
    (hcov : ∀ T : Over (Spec (CommRingCat.of k)), Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      Scheme.etaleTopologyOver k (Limits.pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T))) :
    (picEt C).RepresentableBy Y :=
  representableBy_picEt_of_galoisQuotient rep
    (semilinearGalActionOfRepresentableBy C rep) e he heq huniv hcov
    (fun T => isInvariantMatch_canonical rep T)

set_option maxHeartbeats 1000000 in
-- Heartbeat headroom: the `Over`/`pullback`/`baseTest` coercion chain is unfolded
-- repeatedly against `IsEquivariant`'s and `picEt`'s differing spellings of one
-- object, as in `PicEtDescentGoal.lean`'s §2b. Not a slow proof: each is a rewrite
-- chain, but elaborating the statement costs the default budget on its own.
/-- **CLAUSE (1) OF THE SEAM, FROM THREE INPUTS**, in the bundled form a `G2`
consumer holds: a `k'`-representation, a Galois quotient of the action it determines,
`hcov`, and local finiteness of the quotient.

This is the sharpest statement of what the seam's clause (1) now costs on this route.
`seamClauseOne_of_isGaloisQuotient_canonical` is this theorem with a fourth argument
`hmatch`, which §3 discharges. -/
theorem seamClauseOne_of_isGaloisQuotient_noMatch
    {C : Over (Spec (CommRingCat.of k))}
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    {Y : Over (Spec (CommRingCat.of k))}
    (hq : IsGaloisQuotient (semilinearGalActionOfRepresentableBy C rep) Y.hom)
    (hcov : ∀ T : Over (Spec (CommRingCat.of k)), Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      Scheme.etaleTopologyOver k (Limits.pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)))
    (hlft : LocallyOfFiniteType Y.hom) :
    ∃ Z : Over (Spec (CommRingCat.of k)),
      Nonempty ((picEt C).RepresentableBy Z) ∧
        LocallyOfFiniteType Z.hom ∧ IsSeparated Z.hom :=
  seamClauseOne_of_isGaloisQuotient_canonical rep hq hcov
    (fun T => isInvariantMatch_canonical rep T) hlft

end Payoff

end Steps

end PicScheme

end Scheme

end AlgebraicGeometry
