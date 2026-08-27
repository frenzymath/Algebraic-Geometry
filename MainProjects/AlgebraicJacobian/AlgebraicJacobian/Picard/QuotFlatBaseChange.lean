/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.GenericFlatnessGeometric

/-!
# Flatness over the base is stable under base change

This file proves the base-change stability of the coherent-sheaf flatness
predicate `AlgebraicGeometry.Scheme.CoherentSheafFlat` (blueprint node
`lem:coherent_flat_base_change`; Stacks 01U9, Nitsure §1): for a cartesian
square of schemes

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  S' --g---> S
```

and a quasi-coherent sheaf of modules `F` on `X` that is flat over `S`, the
pullback `g'^* F` is flat over `S'`.

## Proof route (affine-local, Stacks 00HB/01U9)

The proof is pure assembly of the per-piece engines of
`AlgebraicJacobian.Picard.GenericFlatnessGeometric`:

* For every point `x ∈ X'` choose an affine `U ⊆ S` around the common image
  `f(g'(x)) = g(f'(x))`, an affine `V ⊆ f⁻¹U` around `g'(x)`, and an affine
  `Ut ⊆ g⁻¹U` around `f'(x)` (`exists_isAffineOpen_mem_and_subset`).  The
  **piece** `W := g'⁻¹V ⊓ f'⁻¹Ut` is an affine open of `X'` containing `x`
  (`isAffineOpen_pullback_piece`: it is the fibre product `V ×_U Ut`).
* On the piece, the pulled-back sections `Γ(g'^*F, W)` are the base change
  `Γ(X',W) ⊗_{Γ(X,V)} Γ(F,V)` with `Γ(X',W) = Γ(X,V) ⊗_{Γ(S,U)} Γ(S',Ut)`,
  so flatness of `Γ(F,V)` over `Γ(S,U)` — the hypothesis at the affine pair
  `(U, V)` — transports to flatness of `Γ(g'^*F, W)` over `Γ(S',Ut)`
  (`flat_section_pullback_piece` = `Module.Flat.of_isPushout` fed with
  `isPushout_appLE_pullback_piece` and the base-change section formula
  `pullback_app_isoTensor_baseMap_sectionLinearEquiv`).
* The pieces cover `X'`, so the affine-locality engine
  `flat_section_of_affine_cover` (Stacks 00HT-style: simultaneous-basic-open
  refinement, mixed-base localization stability, and the
  `Module.flat_of_isLocalized_span` glue) upgrades the chart family to
  flatness at *every* affine pair `(U' ⊆ S', V' ⊆ f'⁻¹U')` — which is the
  definition of `CoherentSheafFlat f' (g'^* F)`.

Quasi-coherence of the pullback is `pullback_isQuasicoherent_hom`
(Stacks 01BG, arbitrary morphisms).

## References

Blueprint: `lem:coherent_flat_base_change`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
Source: [Nitsure], §1 (FGA Explained Ch. 5, arXiv:math/0504020); Stacks 01U9.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

/-- **Flatness over the base is stable under base change** (Stacks 01U9,
lifted to the coherent-sheaf flatness predicate `Scheme.CoherentSheafFlat`
along a cartesian square).  Affine-locally this is `Module.Flat.of_isPushout`
threaded through the quasi-coherent section calculus: on an affine piece
`g'⁻¹V ⊓ f'⁻¹Ut` of the fibre-product square the pulled-back sections are the
base change of the sections of `F`, and the affine-pair predicate is
affine-local for quasi-coherent modules (Stacks 00HT,
`flat_section_of_affine_cover`). -/
theorem CoherentSheafFlat.of_isPullback
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) (F : X.Modules) (hqc : F.IsQuasicoherent)
    (hF : CoherentSheafFlat f F) :
    CoherentSheafFlat f' ((Scheme.Modules.pullback g').obj F) := by
  haveI := hqc
  haveI : ((Scheme.Modules.pullback g').obj F).IsQuasicoherent :=
    pullback_isQuasicoherent_hom g' F hqc
  -- Per-point charts: an affine piece of the fibre-product square through the
  -- point, over an affine base chart, with flat pulled-back sections.
  have H : ∀ x : X', ∃ (W : X'.Opens) (Ut : S'.Opens),
      IsAffineOpen W ∧ IsAffineOpen Ut ∧ x ∈ W ∧ ∃ (eW : W ≤ f' ⁻¹ᵁ Ut),
        (letI : Module Γ(S', Ut) Γ((Scheme.Modules.pullback g').obj F, W) :=
          Module.compHom _ (f'.appLE Ut W eW).hom
        Module.Flat Γ(S', Ut) Γ((Scheme.Modules.pullback g').obj F, W)) := by
    intro x
    -- the two composites to `S` agree on `x`
    have hbase : f.base (g'.base x) = g.base (f'.base x) := by
      have h := congrArg (fun φ : X' ⟶ S => φ.base x) sq.w
      simpa using h
    -- affine `U ⊆ S` around the common image point
    obtain ⟨U, hU, hsU, -⟩ := exists_isAffineOpen_mem_and_subset
      (TopologicalSpace.Opens.mem_top (f.base (g'.base x)))
    -- affine `V ⊆ f⁻¹U` around `g'(x)`
    obtain ⟨V, hV, hxV, hVsub⟩ := exists_isAffineOpen_mem_and_subset
      (show g'.base x ∈ f ⁻¹ᵁ U from hsU)
    -- affine `Ut ⊆ g⁻¹U` around `f'(x)`
    obtain ⟨Ut, hUt, hxUt, hUtsub⟩ := exists_isAffineOpen_mem_and_subset
      (show f'.base x ∈ g ⁻¹ᵁ U by
        change g.base (f'.base x) ∈ U
        rw [← hbase]; exact hsU)
    have hUSX : V ≤ f ⁻¹ᵁ U := hVsub
    have hUST : Ut ≤ g ⁻¹ᵁ U := hUtsub
    exact ⟨g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ Ut, Ut,
      isAffineOpen_pullback_piece sq hUST hUSX hU hUt hV, hUt, ⟨hxV, hxUt⟩,
      inf_le_right,
      flat_section_pullback_piece sq hUST hUSX F hU hUt hV (hF hU hV hUSX)⟩
  choose Wc Uc hWc hUc hmem eWc hflat using H
  -- assemble: chart flatness on an affine cover gives every affine pair
  intro U' hU' V' hV' e
  exact flat_section_of_affine_cover f' ((Scheme.Modules.pullback g').obj F)
    Wc hWc Uc hUc eWc (fun y => ⟨y, hmem y⟩) hflat hU' hV' e

end Scheme

end AlgebraicGeometry
