/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Cohomology.MayerVietorisCore

/-!
# Mayer-Vietoris on a 2-affine cover and Čech-acyclic cover infrastructure

This file (iter-063 split, cohort 2) contains the 2-affine cover
Mayer-Vietoris theorems, the cover-totality bridges (universe-shift
`LinearEquiv`s, `finrank` / `Module.Finite` transports), the
`IsCechAcyclicCover` consumers, the comparison-iso typeclass
`HasCechToHModuleIso`, and the existence-bundled
`HasAffineCechAcyclicCover` predicate together with the producer that
fires `IsAffineHModuleVanishing` from a `HasAffineCechAcyclicCover`
hypothesis.

This is cohort 2 of the original `MayerVietoris.lean` split:
* `MayerVietorisCore.lean`: MV LES core + Mathlib gap-fill.
* `MayerVietorisCover.lean` (this file): 2-affine cover MV +
  cover-totality bridges + `IsCechAcyclicCover` consumers +
  `HasAffineCechAcyclicCover` carrier.

See `blueprint/src/chapters/Cohomology_MayerVietoris.tex`.
-/

set_option autoImplicit false

universe u v w w'

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

section AffineCoverMVSquare

/-- Phase A step 6 *Path 2* (iter-028): a bundled 2-affine cover of a scheme
together with the affineness of the pairwise intersection. The geometric input
to the abstract Mayer-Vietoris LES `HModule'_sequence_exact` consumes — packaged
to record the affineness conditions and the cover-totality hypothesis that the
abstract MV-square does not capture. The accessor `toMayerVietorisSquare`
produces the underlying Mathlib `MayerVietorisSquare`.

Mathematically: a 2-affine open cover of `X` whose pairwise intersection is also
affine. The cover hypothesis `cover : U₁ ⊔ U₂ = ⊤` is load-bearing for downstream
Serre-finiteness use (it identifies the `MayerVietorisSquare` corner `X₄` with
the whole scheme `X`). -/
structure AffineCoverMVSquare (X : Scheme.{u}) where
  /-- First affine open of the cover. -/
  U₁ : X.Opens
  /-- Second affine open of the cover. -/
  U₂ : X.Opens
  /-- `U₁` is affine. -/
  isAffineOpen_U₁ : IsAffineOpen U₁
  /-- `U₂` is affine. -/
  isAffineOpen_U₂ : IsAffineOpen U₂
  /-- The intersection `U₁ ⊓ U₂` is affine. -/
  isAffineOpen_inf : IsAffineOpen (U₁ ⊓ U₂)
  /-- Total cover: `U₁ ⊔ U₂ = ⊤`. -/
  cover : U₁ ⊔ U₂ = ⊤

/-- Phase A step 6 *Path 2* (iter-028): the underlying abstract Mayer-Vietoris
square produced by a 2-affine cover. Bridge from the geometric input (an
`AffineCoverMVSquare`) to the categorical input (a `MayerVietorisSquare` for
the Grothendieck topology on `Opens X.toTopCat`) the abstract MV-LES theorem
`HModule'_sequence_exact` consumes. The four corners collapse definitionally:
`X₁ = U₁ ⊓ U₂`, `X₂ = U₁`, `X₃ = U₂`, `X₄ = U₁ ⊔ U₂` (each by `rfl`,
plan-agent probe-verified). -/
noncomputable def AffineCoverMVSquare.toMayerVietorisSquare {X : Scheme.{u}}
    (S : X.AffineCoverMVSquare) :
    (Opens.grothendieckTopology X.toTopCat).MayerVietorisSquare :=
  Opens.mayerVietorisSquare S.U₁ S.U₂

/-- Iter-029 corner identification: `X₁ = U₁ ⊓ U₂`. The first three corners are
`rfl`-equal because `Opens.mayerVietorisSquare` defines them definitionally. -/
@[simp]
lemma AffineCoverMVSquare.toMayerVietorisSquare_toSquare_X₁
    {X : Scheme.{u}} (S : X.AffineCoverMVSquare) :
    S.toMayerVietorisSquare.toSquare.X₁ = S.U₁ ⊓ S.U₂ := rfl

/-- Iter-029 corner identification: `X₂ = U₁`. -/
@[simp]
lemma AffineCoverMVSquare.toMayerVietorisSquare_toSquare_X₂
    {X : Scheme.{u}} (S : X.AffineCoverMVSquare) :
    S.toMayerVietorisSquare.toSquare.X₂ = S.U₁ := rfl

/-- Iter-029 corner identification: `X₃ = U₂`. -/
@[simp]
lemma AffineCoverMVSquare.toMayerVietorisSquare_toSquare_X₃
    {X : Scheme.{u}} (S : X.AffineCoverMVSquare) :
    S.toMayerVietorisSquare.toSquare.X₃ = S.U₂ := rfl

/-- Iter-029 cover-totality identification: `X₄ = ⊤`. The substantive corner
identification — uses the `cover` field, which is the totality hypothesis
`U₁ ⊔ U₂ = ⊤` recorded in `AffineCoverMVSquare`. -/
@[simp]
lemma AffineCoverMVSquare.toMayerVietorisSquare_toSquare_X₄
    {X : Scheme.{u}} (S : X.AffineCoverMVSquare) :
    S.toMayerVietorisSquare.toSquare.X₄ = ⊤ := S.cover

/-- Iter-029 Mayer-Vietoris LES sequence on a 2-affine cover: a routine
specialisation of the iter-022 abstract sequence `HModule'_sequence` to the
bundled `AffineCoverMVSquare` data. Parameterised over a generic sheaf `F`
for reusability; the `toModuleKSheaf C` application is iter-030+ work. The
fully-qualified `_root_.AlgebraicGeometry.Scheme.HModule'_sequence` reference
is required because `def AffineCoverMVSquare.HModule'_sequence` auto-opens the
`AffineCoverMVSquare` namespace inside the body, causing bare
`HModule'_sequence` to recursively resolve to itself. -/
noncomputable def AffineCoverMVSquare.HModule'_sequence
    (k : Type u) [Field k] {X : Scheme.{u}} (S : X.AffineCoverMVSquare)
    (F : Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k))
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat 5 :=
  _root_.AlgebraicGeometry.Scheme.HModule'_sequence k S.toMayerVietorisSquare F n₀ n₁ h

/-- Iter-029 Mayer-Vietoris LES exactness on a 2-affine cover: a routine
specialisation of the iter-026 abstract exactness theorem
`HModule'_sequence_exact` to the bundled `AffineCoverMVSquare` data. -/
lemma AffineCoverMVSquare.HModule'_sequence_exact
    (k : Type u) [Field k] {X : Scheme.{u}} (S : X.AffineCoverMVSquare)
    (F : Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k))
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (S.HModule'_sequence k F n₀ n₁ h).Exact :=
  _root_.AlgebraicGeometry.Scheme.HModule'_sequence_exact k S.toMayerVietorisSquare F n₀ n₁ h

/-- Iter-030 Mayer-Vietoris LES on a 2-affine cover of a curve: a routine
binding of the iter-029 sheaf-parameterised `HModule'_sequence` to the
structure sheaf `toModuleKSheaf C` for `C : Over (Spec (CommRingCat.of k))`.
The dot-notation `S.HModule'_sequence` resolves cleanly via method-call
against `S : AffineCoverMVSquare`, sidestepping the iter-029 sub-namespace
shadowing trap that required `_root_` disambiguation in the abstract
specialisation's body. -/
noncomputable def AffineCoverMVSquare.HModule'_sequence_curve
    (k : Type u) [Field k] {C : Over (Spec (CommRingCat.of k))}
    (S : C.left.AffineCoverMVSquare)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat 5 :=
  S.HModule'_sequence k (Scheme.toModuleKSheaf C) n₀ n₁ h

/-- Iter-030 Mayer-Vietoris LES exactness on a 2-affine cover of a curve:
the exactness companion of `HModule'_sequence_curve`, by direct application
of the iter-029 abstract `HModule'_sequence_exact` to the structure sheaf
`toModuleKSheaf C`. -/
lemma AffineCoverMVSquare.HModule'_sequence_curve_exact
    (k : Type u) [Field k] {C : Over (Spec (CommRingCat.of k))}
    (S : C.left.AffineCoverMVSquare)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (S.HModule'_sequence_curve k n₀ n₁ h).Exact :=
  S.HModule'_sequence_exact k (Scheme.toModuleKSheaf C) n₀ n₁ h

end AffineCoverMVSquare

/-- Iter-031 cover-totality source-object identification. For a category `C`
with terminal object `T`, the sheafification of the free `k`-module on the
representable presheaf at `T` is canonically isomorphic to the constant sheaf
at `ModuleCat.of k k`. This is the natural-iso prerequisite for identifying
`HModule' k F n T` (open-evaluation cohomology at the terminal `T`, iter-014)
with `HModule k F n` (global cohomology, iter-009): both are `Ext` groups
whose source objects are made canonically isomorphic by this iso.

Assembled from three Mathlib pieces, mirroring the structure
`constantSheaf J D = Functor.const Cᵒᵖ ⋙ presheafToSheaf J D`:
1. `yoneda.obj T ≅ (Functor.const Cᵒᵖ).obj PUnit` — the terminal-collapse
   of the representable, by `IsTerminal.from`/`IsTerminal.hom_ext`.
2. `Functor.constComp _ PUnit (ModuleCat.free k)` — the identity
   `(Functor.const Cᵒᵖ).obj PUnit ⋙ ModuleCat.free k =
    (Functor.const Cᵒᵖ).obj ((ModuleCat.free k).obj PUnit)`
   packaged as an iso.
3. `(Finsupp.uniqueLinearEquiv k k PUnit.unit).toModuleIso` —
   `(ModuleCat.free k).obj PUnit ≅ ModuleCat.of k k`. -/
noncomputable def HModule'_top_sourceIso
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    {T : C} (hT : IsTerminal T) :
    (presheafToSheaf J _).obj
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj T)
      ≅ (constantSheaf J (ModuleCat.{u} k)).obj (ModuleCat.of k k) :=
  (presheafToSheaf J _).mapIso
    (Functor.isoWhiskerRight
        (NatIso.ofComponents
          (fun _ => Equiv.toIso { toFun := fun _ => PUnit.unit
                                  invFun := fun _ => hT.from _
                                  left_inv := fun _ => hT.hom_ext _ _
                                  right_inv := fun _ => rfl })
          (fun _ => by ext; rfl))
        (ModuleCat.free k) ≪≫
      Functor.constComp _ PUnit.{u+1} (ModuleCat.free k) ≪≫
      (Functor.const Cᵒᵖ).mapIso
        (Finsupp.uniqueLinearEquiv k k PUnit.unit).toModuleIso)

/-- Iter-032 cover-totality Ext-transport at universe `u+1`. Combining the
iter-031 `HModule'_top_sourceIso` (a sheaf-level natural iso between source
objects of two `Ext` computations) with the Mathlib Ext-API operation
`precompOfLinear` (pre-composition of `Ext` along an `Ext 0`-element) yields
a `k`-linear equivalence between the universe-`u+1` Ext at the sheafified
representable on `T` and `HModule k F n`.

The universe annotation `Abelian.Ext.{u+1}` on the LHS is load-bearing —
without it Lean would pick `Ext.{u}` (matching iter-014's `HModule'` choice),
and the equivalence would not typecheck against `HModule k F n : Type (u+1)`
(iter-009). By pinning the LHS to `Ext.{u+1}` we sidestep the iter-031
universe mismatch (`HModule' : Type u` vs `HModule : Type (u+1)`); both
sides of this equivalence live at `Type (u+1)`. The bridge from
`HModule' k F n T : Type u` to the LHS here is iter-033+ work — most
plausibly via a small refactor on iter-014 to align `HModule'`'s universe,
or via a `ULift.{u+1}` wrapper.

Body uses `LinearEquiv.ofLinear` with two pre-composition maps via the
iter-031 iso's hom/inv. The round-trip equations close by a four-step
rewrite: associativity (with the middle factor degree 0), composition
collapse via `mk₀_comp_mk₀`, the iso identity, and `mk₀_id_comp`. -/
noncomputable def HModule_top_linearEquiv
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (F : Sheaf J (ModuleCat.{u} k)) (n : ℕ) {T : C} (hT : IsTerminal T) :
    Abelian.Ext.{u+1}
        ((presheafToSheaf J (ModuleCat.{u} k)).obj
          ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj T)) F n
      ≃ₗ[k] HModule k F n :=
  let α := HModule'_top_sourceIso k hT
  LinearEquiv.ofLinear
    ((Abelian.Ext.mk₀ α.inv).precompOfLinear k F (zero_add n))
    ((Abelian.Ext.mk₀ α.hom).precompOfLinear k F (zero_add n))
    (by
      ext x
      change (Abelian.Ext.mk₀ α.inv).comp
        ((Abelian.Ext.mk₀ α.hom).comp x (zero_add n)) (zero_add n) = x
      rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
          α.inv_hom_id, Abelian.Ext.mk₀_id_comp])
    (by
      ext y
      change (Abelian.Ext.mk₀ α.hom).comp
        ((Abelian.Ext.mk₀ α.inv).comp y (zero_add n)) (zero_add n) = y
      rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
          α.hom_inv_id, Abelian.Ext.mk₀_id_comp])

/-- Iter-033 cover-totality Ext-transport at universe `u`. The universe-`u`
parallel of iter-032's `HModule_top_linearEquiv`. Combining the iter-031
`HModule'_top_sourceIso` (a sheaf-level natural iso between source objects
of two `Ext` computations) with the Mathlib Ext-API operation
`precompOfLinear` (pre-composition of `Ext` along an `Ext 0`-element)
yields a `k`-linear equivalence between `HModule' k F n T` (the iter-014
universe-`u` cohomology of an open at the terminal) and the universe-`u`
`Ext` at the constant sheaf on `ModuleCat.of k k`.

Both sides live at `Type u` (matching iter-014's `HModule'` ascription).
This is the universe-`u` parallel of iter-032's universe-`u+1` form; the
final bridge between the two (`Ext.{u}((constantSheaf J _).obj
(ModuleCat.of k k)) F n ≃ₗ[k] HModule k F n = Ext.{u+1}(...)`) is
iter-034+ work, requiring Mathlib's `Abelian.Ext.chgUniv` (a bare
`Equiv`, file `Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean`
L540) to be upgraded to a `LinearEquiv`.

The body is shape-identical to iter-032: `LinearEquiv.ofLinear` with two
pre-composition maps via the iter-031 iso's hom/inv. The round-trip
equations close by the same four-step rewrite chain. Lean's universe
inference adapts automatically because the LHS `HModule' k F n T`
forces `Ext.{u}` everywhere. -/
noncomputable def HModule'_top_linearEquiv
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (F : Sheaf J (ModuleCat.{u} k)) (n : ℕ) {T : C} (hT : IsTerminal T) :
    HModule' k F n T
      ≃ₗ[k] Abelian.Ext ((constantSheaf J (ModuleCat.{u} k)).obj
              (ModuleCat.of k k)) F n :=
  let α := HModule'_top_sourceIso k hT
  LinearEquiv.ofLinear
    ((Abelian.Ext.mk₀ α.inv).precompOfLinear k F (zero_add n))
    ((Abelian.Ext.mk₀ α.hom).precompOfLinear k F (zero_add n))
    (by
      ext x
      change (Abelian.Ext.mk₀ α.inv).comp
        ((Abelian.Ext.mk₀ α.hom).comp x (zero_add n)) (zero_add n) = x
      rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
          α.inv_hom_id, Abelian.Ext.mk₀_id_comp])
    (by
      ext y
      change (Abelian.Ext.mk₀ α.hom).comp
        ((Abelian.Ext.mk₀ α.inv).comp y (zero_add n)) (zero_add n) = y
      rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
          α.hom_inv_id, Abelian.Ext.mk₀_id_comp])

/-- Iter-034 universe-bump bridge. Composes iter-033's
`HModule'_top_linearEquiv` (universe-`u` cover-totality between `HModule' k F n T`
and `Ext.{u} ((constantSheaf J _).obj (ModuleCat.of k k)) F n`) with the
universe shift `Abelian.Ext.chgUnivLinearEquiv` (Mathlib gap-fill at the top
of this file) lifting the result to `Ext.{u+1} ((constantSheaf J _).obj
(ModuleCat.of k k)) F n = HModule k F n` (definitional unfold of the iter-009
abbrev). The composition gives the full bridge `HModule' k F n T ≃ₗ[k]
HModule k F n` for terminal `T`, closing Step 3 of the Serre-finiteness
scaffold. Iter-035+ specialises this to `AffineCoverMVSquare` using
iter-029's `toMayerVietorisSquare_toSquare_X₄ : ... = ⊤` simp lemma. -/
noncomputable def HModule'_eq_HModule_linearEquiv
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt.{u} (Sheaf J (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf J (ModuleCat.{u} k))]
    (F : Sheaf J (ModuleCat.{u} k)) (n : ℕ) {T : C} (hT : IsTerminal T) :
    HModule' k F n T ≃ₗ[k] HModule k F n :=
  (HModule'_top_linearEquiv k F n hT).trans Abelian.Ext.chgUnivLinearEquiv

/-- Iter-035 corner-bridge specialisation, abstract sheaf form. With iter-034's
universal bridge `HModule'_eq_HModule_linearEquiv` in scope, the natural
specialisation lands the bridge on the `X₄` corner of an `AffineCoverMVSquare`,
where iter-029's simp lemma `toMayerVietorisSquare_toSquare_X₄` identifies the
corner with `⊤ : Opens X.toTopCat`. Mathlib's `Preorder.isTerminalTop`
(`Mathlib/CategoryTheory/Limits/Preorder.lean`) supplies the
`IsTerminal ⊤` witness; transporting this back via the simp lemma's `.symm`
gives the required `IsTerminal X₄` to feed into the universal bridge. The
qualified `TopologicalSpace.Opens X.toTopCat` form is required to sidestep the
iter-029 sub-namespace shadowing trap (bare `Opens X.toTopCat` inside `def
AffineCoverMVSquare.foo` shadows to `Scheme.Opens` which expects a `Scheme`). -/
noncomputable def AffineCoverMVSquare.HModule'_X₄_linearEquiv
    (k : Type u) [Field k] {X : Scheme.{u}} (S : X.AffineCoverMVSquare)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k))]
    (F : Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)) (n : ℕ) :
    HModule' k F n S.toMayerVietorisSquare.toSquare.X₄ ≃ₗ[k] HModule k F n :=
  HModule'_eq_HModule_linearEquiv k F n
    (S.toMayerVietorisSquare_toSquare_X₄.symm ▸
      (Preorder.isTerminalTop (TopologicalSpace.Opens X.toTopCat)))

/-- Iter-035 corner-bridge curve specialisation. Direct application of
`AffineCoverMVSquare.HModule'_X₄_linearEquiv` to `F := Scheme.toModuleKSheaf C`
for `C : Over (Spec (CommRingCat.of k))`, via the dot-notation method-call form
`S.HModule'_X₄_linearEquiv` (mirrors the iter-030 `HModule'_sequence_curve`
pattern: dot-notation method-call resolves cleanly via lookup against
`S : C.left.AffineCoverMVSquare`, sidestepping the iter-029 sub-namespace
shadowing trap that required `_root_.` disambiguation in the abstract
`_sequence` body). -/
noncomputable def AffineCoverMVSquare.HModule'_X₄_linearEquiv_curve
    (k : Type u) [Field k] {C : Over (Spec (CommRingCat.of k))}
    (S : C.left.AffineCoverMVSquare)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    (n : ℕ) :
    HModule' k (Scheme.toModuleKSheaf C) n S.toMayerVietorisSquare.toSquare.X₄
      ≃ₗ[k] HModule k (Scheme.toModuleKSheaf C) n :=
  S.HModule'_X₄_linearEquiv k _ n

/-- Iter-036 finrank corollary, abstract sheaf form. With iter-035's corner-bridge
`HModule'_X₄_linearEquiv` in scope, the immediate algebraic consequence is that the
genus carrier `Module.finrank k (HModule k F n)` equals the open-evaluated form
`Module.finrank k (HModule' k F n X₄)`, by Mathlib's `LinearEquiv.finrank_eq`
applied to the bridge. The `.symm` is required: the bridge is
`HModule' k F n X₄ ≃ₗ[k] HModule k F n` (LHS-to-RHS), so the symmetric form
gives the orientation wanted by `genus C := Module.finrank k (HModule k _ 1)`. -/
theorem AffineCoverMVSquare.finrank_HModule_eq_HModule'_X₄
    (k : Type u) [Field k] {X : Scheme.{u}} (S : X.AffineCoverMVSquare)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k))]
    (F : Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)) (n : ℕ) :
    Module.finrank k (HModule k F n) =
      Module.finrank k (HModule' k F n S.toMayerVietorisSquare.toSquare.X₄) :=
  (S.HModule'_X₄_linearEquiv k F n).symm.finrank_eq

/-- Iter-036 finrank corollary, curve specialisation. Direct application of (a) to
`F := Scheme.toModuleKSheaf C` for `C : Over (Spec (CommRingCat.of k))`, via the
dot-notation method-call form `S.finrank_HModule_eq_HModule'_X₄` (mirrors the
iter-030 `_sequence_curve` and iter-035 `_X₄_linearEquiv_curve` patterns: dot-notation
method-call resolves cleanly via lookup against `S : C.left.AffineCoverMVSquare`,
sidestepping the iter-029 sub-namespace shadowing trap). -/
theorem AffineCoverMVSquare.finrank_HModule_eq_HModule'_X₄_curve
    (k : Type u) [Field k] {C : Over (Spec (CommRingCat.of k))}
    (S : C.left.AffineCoverMVSquare)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    (n : ℕ) :
    Module.finrank k (HModule k (Scheme.toModuleKSheaf C) n) =
      Module.finrank k (HModule' k (Scheme.toModuleKSheaf C) n
        S.toMayerVietorisSquare.toSquare.X₄) :=
  S.finrank_HModule_eq_HModule'_X₄ k _ n

/-- Iter-037 `Module.Finite` transport companion, abstract sheaf form. With iter-035's
corner-bridge `HModule'_X₄_linearEquiv : HModule' k F n X₄ ≃ₗ[k] HModule k F n`
in scope (LHS = X₄ form, RHS = global form), Mathlib's `Module.Finite.equiv`
transports finiteness from LHS to RHS: given `Module.Finite k (HModule' k F n X₄)`
as a hypothesis, we get `Module.Finite k (HModule k F n)` as a conclusion.
**No `.symm` is needed** — `Module.Finite.equiv` consumes the hypothesis on the
LHS of the equiv (`[Module.Finite R M]`) and produces the conclusion on the RHS
(`Module.Finite R N`), which is exactly the orientation `smoothOfRelativeDimension_genus`
(Jacobian.lean) eventually consumes. -/
theorem AffineCoverMVSquare.module_finite_HModule_of_HModule'_X₄
    (k : Type u) [Field k] {X : Scheme.{u}} (S : X.AffineCoverMVSquare)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k))]
    (F : Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)) (n : ℕ)
    [Module.Finite k (HModule' k F n S.toMayerVietorisSquare.toSquare.X₄)] :
    Module.Finite k (HModule k F n) :=
  Module.Finite.equiv (S.HModule'_X₄_linearEquiv k F n)

/-- Iter-037 `Module.Finite` transport companion, curve specialisation. Direct
application of (a) to `F := Scheme.toModuleKSheaf C` for `C : Over (Spec (CommRingCat.of k))`,
via the dot-notation method-call form `S.module_finite_HModule_of_HModule'_X₄`
(mirrors the iter-030 `_sequence_curve`, iter-035 `_X₄_linearEquiv_curve`, and
iter-036 `_finrank_HModule_eq_HModule'_X₄_curve` patterns: dot-notation method-call
resolves cleanly via lookup against `S : C.left.AffineCoverMVSquare`, sidestepping
the iter-029 sub-namespace shadowing trap). -/
theorem AffineCoverMVSquare.module_finite_HModule_of_HModule'_X₄_curve
    (k : Type u) [Field k] {C : Over (Spec (CommRingCat.of k))}
    (S : C.left.AffineCoverMVSquare)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    (n : ℕ)
    [Module.Finite k (HModule' k (Scheme.toModuleKSheaf C) n
        S.toMayerVietorisSquare.toSquare.X₄)] :
    Module.Finite k (HModule k (Scheme.toModuleKSheaf C) n) :=
  S.module_finite_HModule_of_HModule'_X₄ k _ n

/-- Iter-049: top-supremum HModule transport. With iter-048's
`subsingleton_HModule'_supr_of_isCechAcyclicCover` consumer in scope (lifting
`IsCechAcyclicCover F 𝒰 + compIso` to `Subsingleton (HModule' k F n (⨆ 𝒰))`)
and iter-034's `HModule'_eq_HModule_linearEquiv` universe bridge in scope
(identifying `HModule' k F n ⊤ ≃ₗ[k] HModule k F n`), this thin transport
chains them: under the cover-totality hypothesis `⨆ i, 𝒰 i = ⊤`, the iter-048
`HModule'`-on-supremum subsingleton lifts (via `h ▸ this`) to `HModule' k F n ⊤`,
which iter-034's bridge `.symm.toEquiv.subsingleton` transports to `HModule k F n`.

This is the universe-`u+1` form of the iter-048 vanishing, which is what
downstream consumers (notably the iter-052+ genus carrier `Module.Finite k
(HModule k (toModuleKSheaf C) 1)`) ultimately need: `genus C =
Module.finrank k (HModule k (toModuleKSheaf C) 1)` (iter-011) lives at
universe `u+1`, but the iter-048 acyclicity carrier and consumer live at
universe `u`. Iter-049 bridges. -/
theorem subsingleton_HModule_of_isCechAcyclicCover_top
    {k : Type u} [Field k] {C : Over (Spec (.of k))}
    {F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)}
    {ι : Type u} {𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat}
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [IsCechAcyclicCover F 𝒰] (h : ⨆ i, 𝒰 i = ⊤)
    (compIso : ∀ (n : ℕ),
      cechCohomology C F 𝒰 n ≃ₗ[k]
        HModule' k F n (⨆ i, 𝒰 i))
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (HModule k F n) := by
  haveI : Subsingleton (HModule' k F n (⨆ i, 𝒰 i)) :=
    subsingleton_HModule'_supr_of_isCechAcyclicCover compIso n hn
  haveI : Subsingleton (HModule' k F n ⊤) := h ▸ this
  exact (HModule'_eq_HModule_linearEquiv k F n
    (Preorder.isTerminalTop _)).symm.toEquiv.subsingleton

/-- Iter-049: curve specialisation at `F := Scheme.toModuleKSheaf C`.

Mirrors the iter-039 / iter-042 / iter-043 / iter-048 `_curve` pattern: a thin
dot-notation wrapper that saves call sites in the curve setting (where `F` is
the structure sheaf) from re-typing `toModuleKSheaf C` whenever the iter-049
consumer is chained through. Used by the iter-053 genus carrier producer
`Module.Finite k (HModule k (toModuleKSheaf C) 1)`. -/
theorem subsingleton_HModule_of_isCechAcyclicCover_top_curve
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    {ι : Type u} {𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat}
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [IsCechAcyclicCover (toModuleKSheaf C) 𝒰] (h : ⨆ i, 𝒰 i = ⊤)
    (compIso : ∀ (n : ℕ),
      cechCohomology C (toModuleKSheaf C) 𝒰 n ≃ₗ[k]
        HModule' k (toModuleKSheaf C) n (⨆ i, 𝒰 i))
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (HModule k (toModuleKSheaf C) n) :=
  subsingleton_HModule_of_isCechAcyclicCover_top (𝒰 := 𝒰) h compIso n hn

/-- Iter-050: Čech-vs-derived comparison-iso typeclass carrier. Packages the
existence of a `LinearEquiv`-valued comparison `∀ n, cechCohomology n ≃ₗ[k]
HModule' n (⨆ 𝒰)` as a `Prop`-valued class via `Nonempty`-wrapping. The
`Nonempty` wrapper is required because the `∀ n, ...` is data (a
`LinearEquiv`-valued function), and `Prop`-valued classes can only have `Prop`
fields.

Once iter-051+ proves the substantive comparison theorem
`∀ n, cechCohomology n ≃ₗ[k] HModule' n (⨆ 𝒰)` under acyclicity hypotheses,
an `instance` for `HasCechToHModuleIso F 𝒰` wraps it via `⟨⟨the_iso⟩⟩`.
Downstream producers (iter-052+ basic-open cover acyclicity + iter-053+
`IsAffineHModuleVanishing`) then chain through both `IsCechAcyclicCover` and
`HasCechToHModuleIso` via instance synthesis without re-passing the iso
explicitly at every call site. Mirrors the iter-046 instance-driven
`IsHModuleHomFinite` design.

Mirrors the iter-040 / iter-043 / iter-048 carrier-class pattern: a
`Prop`-valued class with a single field. The class is parameterised over the
sheaf `F` and cover `𝒰` (matches the iter-048 `IsCechAcyclicCover` signature). -/
class HasCechToHModuleIso
    {k : Type u} [Field k] {C : Over (Spec (.of k))}
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))] :
    Prop where
  nonempty_compIso : Nonempty
    (∀ (n : ℕ), cechCohomology C F 𝒰 n ≃ₗ[k]
        HModule' k F n (⨆ i, 𝒰 i))

/-- Iter-050: comparison-iso extractor. Given the iter-050 typeclass instance
`[HasCechToHModuleIso F 𝒰]`, recover the comparison iso as a function via
`Classical.choice` on the class field. The `noncomputable` modifier is required
because `Classical.choice` is non-constructive (already in the kernel-only
axiom set `[propext, Classical.choice, Quot.sound]` since iter-048; no new
axiom introduced). -/
noncomputable def cechToHModuleIso
    {k : Type u} [Field k] {C : Over (Spec (.of k))}
    {F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)}
    {ι : Type u} {𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat}
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasCechToHModuleIso F 𝒰] :
    ∀ (n : ℕ), cechCohomology C F 𝒰 n ≃ₗ[k]
      HModule' k F n (⨆ i, 𝒰 i) :=
  Classical.choice HasCechToHModuleIso.nonempty_compIso

/-- Iter-050: instance-driven top-supremum HModule transport. Combines iter-048's
`IsCechAcyclicCover` carrier with iter-050's `HasCechToHModuleIso` carrier:
under both class hypotheses (and the cover-totality hypothesis `⨆ i, 𝒰 i = ⊤`),
conclude `Subsingleton (HModule k F n)` for `n > 0`.

Body: applies iter-049's `subsingleton_HModule_of_isCechAcyclicCover_top`
directly, with the comparison iso supplied via the iter-050 extractor
`cechToHModuleIso`. The extractor fires automatically on the
`[HasCechToHModuleIso F 𝒰]` instance argument; no explicit `compIso` needs to
be passed at the call site.

This is the iter-050 instance-driven counterpart to iter-049's explicit-argument
form. Iter-053+ producers chain through this consumer via typeclass synthesis on
both `[IsCechAcyclicCover]` and `[HasCechToHModuleIso]` instances. -/
theorem subsingleton_HModule_of_hasCechToHModuleIso_top
    {k : Type u} [Field k] {C : Over (Spec (.of k))}
    {F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)}
    {ι : Type u} {𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat}
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [IsCechAcyclicCover F 𝒰] [HasCechToHModuleIso F 𝒰]
    (h : ⨆ i, 𝒰 i = ⊤) (n : ℕ) (hn : 0 < n) :
    Subsingleton (HModule k F n) :=
  subsingleton_HModule_of_isCechAcyclicCover_top h cechToHModuleIso n hn

/-- Iter-050: curve specialisation at `F := Scheme.toModuleKSheaf C`.

Mirrors the iter-039 / iter-042 / iter-043 / iter-048 / iter-049 `_curve`
pattern: a thin dot-notation wrapper that saves call sites in the curve setting
(where `F` is the structure sheaf) from re-typing `toModuleKSheaf C` whenever
the iter-050 instance-driven consumer is chained through. Used by the iter-053+
genus carrier producer `Module.Finite k (HModule k (toModuleKSheaf C) 1)`. -/
theorem subsingleton_HModule_of_hasCechToHModuleIso_top_curve
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    {ι : Type u} {𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat}
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [IsCechAcyclicCover (toModuleKSheaf C) 𝒰]
    [HasCechToHModuleIso (toModuleKSheaf C) 𝒰]
    (h : ⨆ i, 𝒰 i = ⊤) (n : ℕ) (hn : 0 < n) :
    Subsingleton (HModule k (toModuleKSheaf C) n) :=
  subsingleton_HModule_of_hasCechToHModuleIso_top (𝒰 := 𝒰) h n hn

/-- Iter-051: instance-driven supremum HModule' consumer (abstract sheaf form).
Combines iter-048's `IsCechAcyclicCover` carrier with iter-050's `HasCechToHModuleIso`
carrier: under both class hypotheses, conclude `Subsingleton (HModule' k F n (⨆ i, 𝒰 i))`
for `n > 0`.

Body: applies iter-048's `subsingleton_HModule'_supr_of_isCechAcyclicCover` directly,
with the comparison iso supplied via the iter-050 extractor `cechToHModuleIso`. The
extractor fires automatically on the `[HasCechToHModuleIso F 𝒰]` instance argument;
no explicit `compIso` needs to be passed at the call site.

This is the iter-051 instance-driven counterpart to iter-048's explicit-argument
supr form, completing the typeclass-driven design symmetry: iter-049 / iter-050
covers the top-supremum case at universe `u+1` (genus carrier path); iter-051
covers the intermediate-supremum case at universe `u` (used by iter-053+ to
instantiate `IsAffineHModuleVanishing` for an affine open via a basic-open cover
where `⨆𝒰 = U ≠ ⊤`).

In contrast to iter-049 / iter-050's `_top` form, this consumer requires only
single-universe `[HasExt.{u}]` (no `[HasExt.{u+1}]`), since it does not pass through
iter-034's universe bridge. The conclusion stays at universe `u`, on `HModule'` (not
`HModule`). -/
theorem subsingleton_HModule'_supr_of_hasCechToHModuleIso
    {k : Type u} [Field k] {C : Over (Spec (.of k))}
    {F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)}
    {ι : Type u} {𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat}
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [IsCechAcyclicCover F 𝒰] [HasCechToHModuleIso F 𝒰]
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (HModule' k F n (⨆ i, 𝒰 i)) :=
  subsingleton_HModule'_supr_of_isCechAcyclicCover cechToHModuleIso n hn

/-- Iter-051: curve specialisation at `F := Scheme.toModuleKSheaf C`.

Mirrors the iter-039 / iter-042 / iter-043 / iter-048 / iter-049 / iter-050
`_curve` pattern: a thin dot-notation wrapper that saves call sites in the curve
setting (where `F` is the structure sheaf) from re-typing `toModuleKSheaf C`
whenever the iter-051 instance-driven consumer is chained through. Used by the
iter-053+ producer instance for `IsAffineHModuleVanishing k C (toModuleKSheaf C)`. -/
theorem subsingleton_HModule'_supr_of_hasCechToHModuleIso_curve
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    {ι : Type u} {𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat}
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [IsCechAcyclicCover (toModuleKSheaf C) 𝒰]
    [HasCechToHModuleIso (toModuleKSheaf C) 𝒰]
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (HModule' k (toModuleKSheaf C) n (⨆ i, 𝒰 i)) :=
  subsingleton_HModule'_supr_of_hasCechToHModuleIso (𝒰 := 𝒰) n hn

/-- Iter-052: generalised rewrite-bridge HModule' consumer (abstract sheaf form).
Combines iter-051's `subsingleton_HModule'_supr_of_hasCechToHModuleIso` with a
`▸`-style rewrite via the equality hypothesis `h : ⨆ i, 𝒰 i = U`: under both
class hypotheses (and the equality), conclude `Subsingleton (HModule' k F n U)`
on an arbitrary open `U`.

Body: applies iter-051's `(⨆𝒰)`-form consumer to obtain `Subsingleton
(HModule' k F n (⨆ i, 𝒰 i))`, then rewrites `⨆ i, 𝒰 i = U` via `h ▸ this` to
land on `U`.

This is the iter-052 generalisation of iter-051: iter-051 covers the
`(⨆𝒰)`-form directly; iter-052 covers an arbitrary `U` under the equality
hypothesis. The iter-054+ producer for `IsAffineHModuleVanishing` chains: pick
a basic-open cover `𝒰` of an affine open `U` with `⨆𝒰 = U`, instantiate
`[IsCechAcyclicCover]` + `[HasCechToHModuleIso]`, apply iter-052 (this iteration)
with `h := the_cover_eq_U` to land `Subsingleton (HModule' k F i U)` directly.

Mirrors iter-049's `(h : ⨆𝒰 = ⊤)`-style rewrite at universe `u+1` for
`HModule`; iter-052 is the parallel form at universe `u` for `HModule'`. Stays
single-universe `[HasExt.{u}]` (no iter-034 universe bridge needed). -/
theorem subsingleton_HModule'_of_hasCechToHModuleIso
    {k : Type u} [Field k] {C : Over (Spec (.of k))}
    {F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)}
    {ι : Type u} {𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat}
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [IsCechAcyclicCover F 𝒰] [HasCechToHModuleIso F 𝒰]
    {U : TopologicalSpace.Opens C.left.toTopCat}
    (h : ⨆ i, 𝒰 i = U) (n : ℕ) (hn : 0 < n) :
    Subsingleton (HModule' k F n U) := by
  haveI := subsingleton_HModule'_supr_of_hasCechToHModuleIso (F := F) (𝒰 := 𝒰) n hn
  exact h ▸ this

/-- Iter-052: curve specialisation at `F := Scheme.toModuleKSheaf C`.

Mirrors the iter-039 / iter-042 / iter-043 / iter-048 / iter-049 / iter-050 /
iter-051 `_curve` pattern: a thin dot-notation wrapper that saves call sites in
the curve setting (where `F` is the structure sheaf) from re-typing
`toModuleKSheaf C` whenever the iter-052 generalised rewrite-bridge consumer is
chained through. Used by the iter-054+ producer instance for
`IsAffineHModuleVanishing k C (toModuleKSheaf C)`. -/
theorem subsingleton_HModule'_of_hasCechToHModuleIso_curve
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    {ι : Type u} {𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat}
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [IsCechAcyclicCover (toModuleKSheaf C) 𝒰]
    [HasCechToHModuleIso (toModuleKSheaf C) 𝒰]
    {U : TopologicalSpace.Opens C.left.toTopCat}
    (h : ⨆ i, 𝒰 i = U) (n : ℕ) (hn : 0 < n) :
    Subsingleton (HModule' k (toModuleKSheaf C) n U) :=
  subsingleton_HModule'_of_hasCechToHModuleIso (𝒰 := 𝒰) h n hn

/-- Iter-053: existence-bundled affine Čech-acyclic + comparison-iso cover predicate.

For each affine open `U` of `C.left.toTopCat`, asserts the existence of a
(data-bundled) basic-open cover `𝒰 : ι → Opens` with `⨆𝒰 = U` together with
both `IsCechAcyclicCover F 𝒰` (iter-048) and `HasCechToHModuleIso F 𝒰` (iter-050)
class hypotheses.

Iter-053 is a thin scaffolding step — the existence is asserted, not constructed.
The substantive iter-054+ work will instantiate `HasAffineCechAcyclicCover` for
the structure sheaf `Scheme.toModuleKSheaf C` via the standard Koszul + Čech-derived
comparison route (Hartshorne III.4 / Stacks 03F7 / Eisenbud Commutative Algebra
§17 Koszul resolution).

Mirrors the iter-040 / iter-043 / iter-048 / iter-050 carrier-predicate pattern:
package the substantive multi-iteration work behind a `Prop`-class so that
downstream consumers (iter-053 producer + iter-055+ Module.Finite ladder) can
fire via instance synthesis. -/
class HasAffineCechAcyclicCover
    {k : Type u} [Field k] {C : Over (Spec (.of k))}
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)) :
    Prop where
  exists_cover : ∀ {U : TopologicalSpace.Opens C.left.toTopCat},
    IsAffineOpen U →
      ∃ (ι : Type u) (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat),
        (⨆ i, 𝒰 i = U) ∧ IsCechAcyclicCover F 𝒰 ∧ HasCechToHModuleIso F 𝒰

/-- Iter-053: producer `IsAffineHModuleVanishing` from `HasAffineCechAcyclicCover`.

Under the iter-053 carrier hypothesis, conclude `IsAffineHModuleVanishing k C F`
on every affine open `U` and every degree `i > 0`. The proof unbundles the
existential to obtain `ι, 𝒰, h, [IsCechAcyclicCover], [HasCechToHModuleIso]`,
registers the two instances locally with `haveI`, then chains iter-052's
generalised rewrite-bridge consumer `subsingleton_HModule'_of_hasCechToHModuleIso`
to land `Subsingleton (HModule' k F i U)`.

Closes the bridge from existence-of-acyclic-cover (iter-053 carrier; substantive
iter-054+ work fills it for the structure sheaf) to per-affine-open vanishing
(iter-040 `IsAffineHModuleVanishing`). Once the iter-054+ producer instance for
`HasAffineCechAcyclicCover (Scheme.toModuleKSheaf C)` is supplied, this producer
fires automatically, supplying `[IsAffineHModuleVanishing k C (toModuleKSheaf C)]`
to iter-040's consumer chain and unblocking Phase A step 6. -/
instance instIsAffineHModuleVanishing_of_hasAffineCechAcyclicCover
    {k : Type u} [Field k] {C : Over (Spec (.of k))}
    {F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)}
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasAffineCechAcyclicCover F] : IsAffineHModuleVanishing k C F where
  subsingleton_HModule' {U} hU i hi := by
    obtain ⟨ι, 𝒰, hcov, hacyc, hcomp⟩ :=
      HasAffineCechAcyclicCover.exists_cover (F := F) hU
    haveI : IsCechAcyclicCover F 𝒰 := hacyc
    haveI : HasCechToHModuleIso F 𝒰 := hcomp
    exact subsingleton_HModule'_of_hasCechToHModuleIso hcov i hi

end AlgebraicGeometry.Scheme
