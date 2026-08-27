/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.CechTwistedCoherenceReduction

/-!
# The reduction of half (a) to `BcSquareCoherence`, as an actual theorem

`CechTwistedCoherenceReduction` states `bcAdjFree` and `BcSquareCoherence` — half (a) of the
twisted Čech square with no Beck–Chevalley mate in it — and carried the *reduction* only as a
commented-out proof, on a cost measurement (run 0068 r6): the script had been verified step by
step, but no session had seen the kernel accept it as one declaration.

This module is the structural fix that measurement prescribed, and it is one line of Lean
infrastructure rather than any new mathematics: **everything the script rewrites with arrives here
as an elaborated olean constant.**  In the previous location `bcAdjFree` and `BcSquareCoherence`
were *local* declarations, so `whnf` inside `erw` — running under
`backward.isDefEq.respectTransparency false` — could and did unfold them, together with the
`asIso`-wrapped `IsIso` instances inside `bcv`.  From here it cannot: an imported constant is
sealed.

The claim this module makes, and the one the previous round could not make: the reduction is a
theorem in this project, kernel-checked.

## Main declarations

* `bcSquareCounitSide_of_coherence` — half (a) (in its counit-side form) from `BcSquareCoherence`.
* `twistedPerSigmaCompat_of_coherence` — the whole twisted-nerve residue in one citable name.

## What is still open

`BcSquareCoherence` itself.  It is a genuine identity relating the pullback pseudofunctor's
coherence isomorphisms to the cover-intersection inclusion `U_{σ'} ⊆ U_{σ'∘δᵏ}`, and it is what
flat base change now rests on.  Being a *hypothesis* it is invisible to a `sorry` census, which is
why it is named in both modules' scope sections.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.Modules

variable {S S' X X' : Scheme.{u}}

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
/-- **THE REDUCTION: half (a) follows from a statement with no mate in it.**

Chain, each step machine-checked: expand both sides' functor images; rewrite the restriction map
to `rawPushPullMap` and kill its unit with `rawPushPullMap_pullback_counit` (the general
over-triangle version — `wmap`'s triangle is *not* `rfl`); eliminate the `σ'` mate with
`bcv_pullback_counit`; move the `σ' ∘ δᵏ` mate under `wleft^*` by naturality of `ppTel.inv`,
which is exactly the shape that puts it adjacent to its own counit; eliminate it too.

So the twisted Čech nerve square — via `bcSquareNaturality_of_counitSide` and
`twistedPerSigmaCompat_of_counitSide` — now rests on `BcSquareCoherence`, a
pullback-pseudofunctor coherence identity.  **The frontier `CechHigherDirectImageUnconditional`
recorded for four rounds ("nothing in the tree relates the Beck–Chevalley mate across a change of
square, here or in mathlib") is therefore no longer the obligation** — not because something was
found that relates mates across squares, but because both mates were *removed*.

What this does NOT claim: `BcSquareCoherence` is not proved, and it is not free.  Closing it is
the remaining work on flat base change.

Project-local. -/
theorem bcSquareCounitSide_of_coherence (f : X ⟶ S) (g' : X' ⟶ X) (𝒰 : X.OpenCover)
    [IsSeparated f] [IsAffine S] [∀ i, IsAffine (𝒰.X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent)
    (hcoh : BcSquareCoherence f g' 𝒰 F hF) : BcSquareCounitSide f g' 𝒰 F hF := by
  intro p k σ'
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  rw [pushPullMap_eq_raw]
  have hadj := rawPushPullMap_pullback_counit
    (Over.Hom.left (wmap g' 𝒰 (SimplexCategory.δ k).toOrderHom σ'))
    (Over.mk (pullback.fst g' (Scheme.Opens.ι
      (coverInterOpen 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom))))).hom
    (Over.mk (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ')))).hom
    (Over.w (wmap g' 𝒰 (SimplexCategory.δ k).toOrderHom σ'))
    ((Scheme.Modules.pullback g').obj F)
  erw [hadj]
  erw [bcv_pullback_counit f g' 𝒰 F hF σ']
  -- `ppTel.inv` naturality moves the `σ' ∘ δᵏ` mate under `wleft^*` of `pV_τ^*`, i.e. next
  -- to its own counit, which is the shape `bcv_pullback_counit` consumes.
  rw [← Category.assoc]
  erw [(ppTel (Over.Hom.left (wmap g' 𝒰 (SimplexCategory.δ k).toOrderHom σ'))
      (Over.mk (pullback.fst g' (Scheme.Opens.ι
        (coverInterOpen 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom))))).hom
      (Over.mk (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ')))).hom
      (Over.w (wmap g' 𝒰 (SimplexCategory.δ k).toOrderHom σ'))).inv.naturality
      (bcv f g' 𝒰 F hF (σ' ∘ (SimplexCategory.δ k).toOrderHom)).hom]
  rw [Category.assoc]
  -- `(pV_τ^* ⋙ wleft^*).map` vs `wleft^*.map (pV_τ^*.map _)`: rfl-equal, differently spelled.
  rw [Functor.comp_map]
  slice_lhs 2 3 => rw [← Functor.map_comp]
  erw [bcv_pullback_counit f g' 𝒰 F hF (σ' ∘ (SimplexCategory.δ k).toOrderHom)]
  exact hcoh p k σ'

/-- The whole twisted-nerve residue from the mate-free coherence identity, in one name:
`bcSquareCounitSide_of_coherence` then `twistedPerSigmaCompat_of_counitSide`.  Stated so that what
flat base change now rests on is citable as a single hypothesis.  Project-local. -/
theorem twistedPerSigmaCompat_of_coherence (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover) [IsSeparated f] [IsAffine S]
    [∀ i, IsAffine (𝒰.X i)] (F : X.Modules) (hF : F.IsQuasicoherent)
    (hcoh : BcSquareCoherence f g' 𝒰 F hF) :
    TwistedPerSigmaDeltaCompat f g f' g' h 𝒰 F hF :=
  twistedPerSigmaCompat_of_counitSide f g f' g' h 𝒰 F hF
    (bcSquareCounitSide_of_coherence f g' 𝒰 F hF hcoh)

end AlgebraicGeometry
