/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.StructureSheafModuleK
import Mathlib.CategoryTheory.Limits.Preorder

/-!
# The Mayer-Vietoris long exact sequence for `ModuleCat k`-valued sheaf cohomology

Let `J` be a Grothendieck topology on a category `C` and let `F` be a sheaf of
`k`-modules on `(C, J)`. The cohomology `HModule' k F n X` of an object `X` is an
`Ext`-group out of the sheafification of the free `ModuleCat k`-valued presheaf on the
presheaf represented by `X`. This file constructs, for a Mayer-Vietoris square `S` in
`(C, J)`, the associated long exact sequence

`⋯ → Hⁿ(X₄) → Hⁿ(X₂) ⊞ Hⁿ(X₃) → Hⁿ(X₁) → Hⁿ⁺¹(X₄) → ⋯`

by mirroring, for `ModuleCat k`-valued sheaves, the construction Mathlib performs for
`AddCommGrpCat`-valued ones. The mechanism is the short exact sequence of sheafified
free sheaves attached to the square, whose extension class provides the connecting
homomorphism and whose contravariant `Ext`-sequence is exact.

## Main results

* `Abelian.Ext.chgUnivLinearEquiv`: the universe change on `Ext` is a linear
  equivalence over a `Linear R`-enriched abelian category.
* `HModule'_cohomologyPresheafFunctor`, `HModule'_cohomologyPresheaf`: degree-`n`
  cohomology as a presheaf `Cᵒᵖ ⥤ AddCommGrpCat`, with value `HModule' k F n X` at
  `op X`.
* `HModule'_toBiprod`, `HModule'_fromBiprod`: the sum and the difference of the
  restriction maps of a Mayer-Vietoris square.
* `HModule'_shortComplex_shortExact`: the short complex of sheafified free sheaves
  attached to a Mayer-Vietoris square is short exact.
* `HModule'_δ`: the connecting homomorphism `Hⁿ⁰(X₁) ⟶ Hⁿ¹(X₄)`.
* `HModule'_sequence`, `HModule'_sequence_exact`: the Mayer-Vietoris sequence and its
  exactness.

## References

* `blueprint/src/chapters/Cohomology_MayerVietoris.tex`
-/

set_option autoImplicit false

universe u v w w'

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

/-! ## The universe change on `Ext` as a linear equivalence

Mathlib's `Abelian.Ext.chgUniv : Ext.{w} X Y n ≃ Ext.{w'} X Y n` is a bare `Equiv`.
Over a `Linear R`-enriched abelian category it is in fact `R`-linear: the additive and
`R`-module structures on `Ext X Y n` are transferred from the standard derived category
through `homEquiv`, and `Ext.homEquiv_chgUniv` says that `chgUniv` preserves the
underlying derived-category morphism, so it automatically commutes with `+` and `•`.

These declarations belong to the `CategoryTheory.Abelian.Ext` namespace and hence sit
outside the `AlgebraicGeometry.Scheme` namespace opened below. -/

/-- `Abelian.Ext.chgUniv` is additive. The underlying morphism `homEquiv` is preserved
by `chgUniv`, and the `AddCommGroup (Ext X Y n)` instance is defined by transferring the
group structure of the standard derived category along `homEquiv`; combining the two
through the extensionality lemma for `Ext` gives additivity. -/
private lemma Abelian.Ext.chgUniv_add
    {C : Type*} [Category C] [Abelian C]
    [HasExt.{w} C] [HasExt.{w'} C] {X Y : C} {n : ℕ} (a b : Abelian.Ext.{w} X Y n) :
    Abelian.Ext.chgUniv.{w'} (a + b) =
      Abelian.Ext.chgUniv.{w'} a + Abelian.Ext.chgUniv.{w'} b := by
  letI := HasDerivedCategory.standard C
  ext
  rw [Abelian.Ext.add_hom, ← Abelian.Ext.homAddEquiv_apply,
      ← Abelian.Ext.homAddEquiv_apply, ← Abelian.Ext.homAddEquiv_apply]
  change Abelian.Ext.homEquiv (Abelian.Ext.chgUniv.{w'} (a + b)) =
    Abelian.Ext.homEquiv (Abelian.Ext.chgUniv.{w'} a) +
      Abelian.Ext.homEquiv (Abelian.Ext.chgUniv.{w'} b)
  rw [Abelian.Ext.homEquiv_chgUniv, Abelian.Ext.homEquiv_chgUniv,
      Abelian.Ext.homEquiv_chgUniv, ← Abelian.Ext.add_hom]

/-- `Abelian.Ext.chgUniv` commutes with the `R`-action when `C` is `Linear R`-enriched.
Same argument as `chgUniv_add`, with `smul_hom` in place of `add_hom`. -/
private lemma Abelian.Ext.chgUniv_smul
    {R : Type*} [Ring R] {C : Type*} [Category C] [Abelian C] [Linear R C]
    [HasExt.{w} C] [HasExt.{w'} C] {X Y : C} {n : ℕ}
    (r : R) (a : Abelian.Ext.{w} X Y n) :
    Abelian.Ext.chgUniv.{w'} (r • a) = r • Abelian.Ext.chgUniv.{w'} a := by
  letI := HasDerivedCategory.standard C
  ext
  rw [Abelian.Ext.smul_hom, ← Abelian.Ext.homAddEquiv_apply,
      ← Abelian.Ext.homAddEquiv_apply]
  change Abelian.Ext.homEquiv (Abelian.Ext.chgUniv.{w'} (r • a)) =
    r • Abelian.Ext.homEquiv (Abelian.Ext.chgUniv.{w'} a)
  rw [Abelian.Ext.homEquiv_chgUniv, Abelian.Ext.homEquiv_chgUniv,
      ← Abelian.Ext.smul_hom]

/-- The universe change `Abelian.Ext.chgUniv : Ext.{w} X Y n ≃ Ext.{w'} X Y n` as an
`R`-linear equivalence, when `C` is `Linear R`-enriched abelian; it combines
`chgUniv_add` and `chgUniv_smul`. Mathlib's version records only the underlying
bijection, whereas chaining the universe change with other linear equivalences (as in
`HModule'_eq_HModule_linearEquiv`) needs the algebraic structure to be preserved. -/
noncomputable def Abelian.Ext.chgUnivLinearEquiv
    {R : Type*} [Ring R] {C : Type*} [Category C] [Abelian C] [Linear R C]
    [HasExt.{w} C] [HasExt.{w'} C] {X Y : C} {n : ℕ} :
    Abelian.Ext.{w} X Y n ≃ₗ[R] Abelian.Ext.{w'} X Y n where
  toFun a := Abelian.Ext.chgUniv.{w'} a
  invFun a := Abelian.Ext.chgUniv.{w} a
  left_inv a := Abelian.Ext.chgUniv.{w'}.left_inv a
  right_inv a := Abelian.Ext.chgUniv.{w'}.right_inv a
  map_add' a b := Abelian.Ext.chgUniv_add a b
  map_smul' r a := Abelian.Ext.chgUniv_smul r a

namespace AlgebraicGeometry.Scheme

/-- Degree-`n` cohomology of `ModuleCat k`-valued sheaves as a functor, the analogue of
`Sheaf.cohomologyPresheafFunctor`. It sends a sheaf `F : Sheaf J (ModuleCat k)` to the
presheaf
`X ↦ Ext^n((presheafToSheaf J _).obj ((yoneda ⋙ ModuleCat.free k).obj X), F)`,
i.e.\ to a presheaf `Cᵒᵖ ⥤ AddCommGrpCat` whose value at `op X` is `HModule' k F n X`
definitionally (see `HModule'_cohomologyPresheaf` below).

The codomain is `Cᵒᵖ ⥤ AddCommGrpCat` rather than `Cᵒᵖ ⥤ ModuleCat k` because
`Abelian.extFunctor n : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat` lands in `AddCommGrpCat` whatever the
`Linear`-enrichment of the source category; the `Module k` structure on each value
`(HModule'_cohomologyPresheaf k F n).obj (op X)` remains available through the
definitional unfolding to `HModule'`. -/
noncomputable def HModule'_cohomologyPresheafFunctor
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (n : ℕ) :
    Sheaf J (ModuleCat.{u} k) ⥤ Cᵒᵖ ⥤ AddCommGrpCat :=
  Functor.flip
    ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k) ⋙
      presheafToSheaf _ _).op ⋙ Abelian.extFunctor n)

/-- Degree-`n` cohomology of a fixed sheaf `F` as a presheaf `Cᵒᵖ ⥤ AddCommGrpCat`, the
analogue of `Sheaf.cohomologyPresheaf`: the value of
`HModule'_cohomologyPresheafFunctor` at `F`. Its value at `op X` is `HModule' k F n X`
definitionally.

The `abbrev` form is load-bearing for that definitional identification: under `def` the
wrapper would block the `rfl`-level reduction to `HModule'` that the Mayer-Vietoris and
Stein-factorization arguments rely on. -/
noncomputable abbrev HModule'_cohomologyPresheaf
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (F : Sheaf J (ModuleCat.{u} k)) (n : ℕ) :
    Cᵒᵖ ⥤ AddCommGrpCat :=
  (HModule'_cohomologyPresheafFunctor k J n).obj F

/-- The pair of restriction maps `Hⁿ(X₄) ⟶ Hⁿ(X₂)` and `Hⁿ(X₄) ⟶ Hⁿ(X₃)` of a
Mayer-Vietoris square `S`, assembled into a single map into the biproduct
`Hⁿ(X₂) ⊞ Hⁿ(X₃)`. This is the first map of the Mayer-Vietoris sequence, the analogue
of `GrothendieckTopology.MayerVietorisSquare.toBiprod`.

The codomain is the biproduct in `AddCommGrpCat`, which is available because
`HModule'_cohomologyPresheaf k F n` takes values there. -/
noncomputable def HModule'_toBiprod
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (S : J.MayerVietorisSquare) (F : Sheaf J (ModuleCat.{u} k)) (n : ℕ) :
    (HModule'_cohomologyPresheaf k F n).obj (Opposite.op S.X₄) ⟶
      (HModule'_cohomologyPresheaf k F n).obj (Opposite.op S.X₂) ⊞
        (HModule'_cohomologyPresheaf k F n).obj (Opposite.op S.X₃) :=
  biprod.lift ((HModule'_cohomologyPresheaf k F n).map S.f₂₄.op)
              ((HModule'_cohomologyPresheaf k F n).map S.f₃₄.op)

/-- The difference of the two restriction maps `Hⁿ(X₂) ⟶ Hⁿ(X₁)` and `Hⁿ(X₃) ⟶ Hⁿ(X₁)`
of a Mayer-Vietoris square `S`, as a single map out of the biproduct
`Hⁿ(X₂) ⊞ Hⁿ(X₃)`. This is the second map of the Mayer-Vietoris sequence, the analogue
of `GrothendieckTopology.MayerVietorisSquare.fromBiprod`.

The negation uses the preadditive structure on `AddCommGrpCat`-morphisms; the sign is
the standard Mayer-Vietoris convention, encoding the alternating-sum differential of the
Čech complex. -/
noncomputable def HModule'_fromBiprod
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (S : J.MayerVietorisSquare) (F : Sheaf J (ModuleCat.{u} k)) (n : ℕ) :
    (HModule'_cohomologyPresheaf k F n).obj (Opposite.op S.X₂) ⊞
        (HModule'_cohomologyPresheaf k F n).obj (Opposite.op S.X₃) ⟶
      (HModule'_cohomologyPresheaf k F n).obj (Opposite.op S.X₁) :=
  biprod.desc ((HModule'_cohomologyPresheaf k F n).map S.f₁₂.op)
              (-(HModule'_cohomologyPresheaf k F n).map S.f₁₃.op)

/-- The first two maps of the Mayer-Vietoris sequence compose to zero:
`HModule'_toBiprod k S F n ≫ HModule'_fromBiprod k S F n = 0`. The analogue of
`GrothendieckTopology.MayerVietorisSquare.toBiprod_fromBiprod`.

Unwinding the biproduct universal property
(`biprod.lift_desc : biprod.lift a b ≫ biprod.desc c d = a ≫ c + b ≫ d`) turns the
statement into the equality of the two composite restrictions `Hⁿ(X₄) ⟶ Hⁿ(X₁)`, which
is the contravariant image of the commutativity `S.f₁₂ ≫ S.f₂₄ = S.f₁₃ ≫ S.f₃₄` of the
Mayer-Vietoris square. -/
@[reassoc (attr := simp)]
lemma HModule'_toBiprod_fromBiprod
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (S : J.MayerVietorisSquare) (F : Sheaf J (ModuleCat.{u} k)) (n : ℕ) :
    HModule'_toBiprod k S F n ≫ HModule'_fromBiprod k S F n = 0 := by
  simp only [HModule'_toBiprod, HModule'_fromBiprod, biprod.lift_desc,
    Preadditive.comp_neg, ← sub_eq_add_neg, sub_eq_zero,
    ← Functor.map_comp, ← op_comp, S.toSquare.fac]

/-- `ModuleCat.free k` is a left adjoint, being left adjoint to `forget (ModuleCat k)`
via `ModuleCat.adj k`. Mathlib provides the adjunction but registers no `IsLeftAdjoint`
instance for it (unlike `AddCommGrpCat.free`); the instance is what makes
`Sheaf.composeAndSheafify J (ModuleCat.free k)` preserve colimits, as used in
`HModule'_isPushoutModuleCatFreeSheaf` below. -/
instance ModuleCat_free_isLeftAdjoint
    (k : Type u) [Field k] : (ModuleCat.free k).IsLeftAdjoint :=
  ⟨_, ⟨ModuleCat.adj k⟩⟩

/-- The image of a Mayer-Vietoris square `S` under
`yoneda ⋙ Functor.whiskeringRight ⋅ (ModuleCat.free k) ⋙ presheafToSheaf J _` is a
pushout square in `Sheaf J (ModuleCat k)`; the analogue of
`GrothendieckTopology.MayerVietorisSquare.isPushoutAddCommGrpFreeSheaf`.

The type-level pushout `S.isPushout` is transported through
`Sheaf.composeAndSheafify J (ModuleCat.free k)`, which preserves pushouts because
`ModuleCat.free k` is a left adjoint, and then corrected along the canonical
isomorphism `presheafToSheafCompComposeAndSheafifyIso`. This pushout is what makes the
short complex `HModule'_shortComplex` short exact, and hence what produces the
connecting homomorphism of the Mayer-Vietoris sequence. -/
lemma HModule'_isPushoutModuleCatFreeSheaf
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    (S : J.MayerVietorisSquare) :
    (S.map (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k) ⋙
      presheafToSheaf J _)).IsPushout :=
  (S.isPushout.map (Sheaf.composeAndSheafify J (ModuleCat.free k))).of_iso
    ((Square.mapFunctor.mapIso
      (presheafToSheafCompComposeAndSheafifyIso J (ModuleCat.free k))).app
        (S.map yoneda))

/-- The short complex of sheafified free `ModuleCat k`-valued presheaves underlying the
Mayer-Vietoris long exact sequence, the analogue of
`GrothendieckTopology.MayerVietorisSquare.shortComplex`.

Its objects are the sheafified free presheaves on the four vertices of the
Mayer-Vietoris square, the middle two `S.X₂` and `S.X₃` combined into a biproduct. The
map `f` is the difference of `yoneda.map S.f₁₂` and `yoneda.map S.f₁₃` lifted through
the biproduct, and `g` is the sum of `yoneda.map S.f₂₄` and `yoneda.map S.f₃₄` desced
through it. That `f ≫ g = 0` is the cokernel-cofork condition of the pushout square
`HModule'_isPushoutModuleCatFreeSheaf` above. -/
@[simps]
noncomputable def HModule'_shortComplex
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    (S : J.MayerVietorisSquare) :
    ShortComplex (Sheaf J (ModuleCat.{u} k)) where
  X₁ := (presheafToSheaf J _).obj (yoneda.obj S.X₁ ⋙ ModuleCat.free k)
  X₂ := (presheafToSheaf J _).obj (yoneda.obj S.X₂ ⋙ ModuleCat.free k) ⊞
    (presheafToSheaf J _).obj (yoneda.obj S.X₃ ⋙ ModuleCat.free k)
  X₃ := (presheafToSheaf J _).obj (yoneda.obj S.X₄ ⋙ ModuleCat.free k)
  f :=
    biprod.lift
      ((presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map S.f₁₂) _))
      (-(presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map S.f₁₃) _))
  g :=
    biprod.desc
      ((presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map S.f₂₄) _))
      ((presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map S.f₃₄) _))
  zero :=
    (S.map (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k) ⋙
        presheafToSheaf J _)).cokernelCofork.condition

/-- Phase A step 6 *Path 2* (iter-020 helper, Mathlib gap-fill): the free-module
functor `ModuleCat.free k : Type u ⥤ ModuleCat.{u} k` preserves monomorphisms.
Mathlib registers `AddCommGrpCat.instPreservesMonomorphismsFree :
AddCommGrpCat.free.PreservesMonomorphisms` in
`Mathlib/Algebra/Category/Grp/Adjunctions.lean` but does not register the
corresponding instance for `ModuleCat.free k` in
`Mathlib/Algebra/Category/ModuleCat/Adjunctions.lean`. This project-local
instance fills the gap so that, after `simp only [biprod.lift_snd]`, the
typeclass-search engine can discharge the residual `Mono` goal in the proof
of `HModule'_shortComplex_f_mono` below.

The proof: for an injective function `f : X → Y` between types,
`(ModuleCat.free k).map f = ModuleCat.ofHom (Finsupp.lmapDomain k k f)` (defeq),
and `Finsupp.mapDomain f` is injective on `Finsupp X k → Finsupp Y k` by
Mathlib's `Finsupp.mapDomain_injective`. Bridging via `ModuleCat.mono_iff_injective`
recovers `Mono` in `ModuleCat k`. -/
instance ModuleCat_free_preservesMonomorphisms
    (k : Type u) [Field k] : (ModuleCat.free k).PreservesMonomorphisms := by
  refine ⟨fun {X Y} f hf ↦ ?_⟩
  have hf' : Function.Injective f := (CategoryTheory.mono_iff_injective f).mp hf
  rw [ModuleCat.mono_iff_injective]
  exact Finsupp.mapDomain_injective hf'

-- Phase A step 6 *Path 2* (iter-020): `(HModule'_shortComplex k S).f` is a
-- monomorphism in `Sheaf J (ModuleCat k)`. Direct mirror of Mathlib's
-- `MayerVietorisSquare.lean` L251–257 with `AddCommGrpCat.free → ModuleCat.free k`.
-- The `set_option backward.isDefEq.respectTransparency false in` attribute is
-- required because the typeclass-search engine needs to unfold the `dsimp`-normal
-- form of `(HModule'_shortComplex k S).f` past structure-literal projection.
set_option backward.isDefEq.respectTransparency false in
instance HModule'_shortComplex_f_mono
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    (S : J.MayerVietorisSquare) :
    Mono (HModule'_shortComplex k S).f := by
  have : Mono ((HModule'_shortComplex k S).f ≫ biprod.snd) := by
    simp only [HModule'_shortComplex_f, biprod.lift_snd]
    infer_instance
  exact mono_of_mono _ biprod.snd

/-- Phase A step 6 *Path 2* (iter-020): `(HModule'_shortComplex k S).g` is an
epimorphism in `Sheaf J (ModuleCat k)`. Direct mirror of Mathlib's
`MayerVietorisSquare.lean` L259–261 with `AddCommGrpCat.free → ModuleCat.free k`.
The proof is a one-line term-mode body using
`ShortComplex.exact_and_epi_g_iff_g_is_cokernel` and the iter-019 lemma
`HModule'_isPushoutModuleCatFreeSheaf`'s `isColimitCokernelCofork` accessor. -/
instance HModule'_shortComplex_g_epi
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    (S : J.MayerVietorisSquare) :
    Epi (HModule'_shortComplex k S).g :=
  ((HModule'_shortComplex k S).exact_and_epi_g_iff_g_is_cokernel.2
    ⟨(HModule'_isPushoutModuleCatFreeSheaf k S).isColimitCokernelCofork⟩).2

/-- Phase A step 6 *Path 2* (iter-020): `(HModule'_shortComplex k S).Exact`,
i.e. the kernel of `g` equals the image of `f` in `Sheaf J (ModuleCat k)`.
Direct mirror of Mathlib's `MayerVietorisSquare.lean` L263–265 with
`AddCommGrpCat.free → ModuleCat.free k`. The proof is a one-line term-mode
body using `ShortComplex.exact_of_g_is_cokernel` and the iter-019 lemma
`HModule'_isPushoutModuleCatFreeSheaf`'s `isColimitCokernelCofork` accessor. -/
lemma HModule'_shortComplex_exact
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    (S : J.MayerVietorisSquare) :
    (HModule'_shortComplex k S).Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    (HModule'_isPushoutModuleCatFreeSheaf k S).isColimitCokernelCofork

/-- Phase A step 6 *Path 2* (iter-020): `(HModule'_shortComplex k S).ShortExact`,
the short-exact predicate (combining `Mono f`, `Epi g`, and `Exact`) in
`Sheaf J (ModuleCat k)`. Direct mirror of Mathlib's `MayerVietorisSquare.lean`
L267–268 with `AddCommGrpCat.free → ModuleCat.free k`. The proof is a one-line
anonymous-constructor: the `Mono f` and `Epi g` predicates are typeclass-resolved
from `HModule'_shortComplex_f_mono` and `HModule'_shortComplex_g_epi`, leaving
only the `exact` field which is filled with `HModule'_shortComplex_exact`. The
named lemma is consumed in iter-021+ as `S.HModule'_shortComplex_shortExact.extClass`
to define the connecting hom `HModule'_δ` of the Mayer-Vietoris LES. -/
lemma HModule'_shortComplex_shortExact
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    (S : J.MayerVietorisSquare) :
    (HModule'_shortComplex k S).ShortExact where
  exact := HModule'_shortComplex_exact k S

/-- Phase A step 6 *Path 2* (iter-021): the connecting homomorphism `δ` of the
Mayer-Vietoris long exact sequence in `ModuleCat k`-valued sheaf cohomology.
For a Mayer-Vietoris square `S` and adjacent cohomological degrees `n₀ + 1 = n₁`,
the morphism
  δ : (HModule'_cohomologyPresheaf k F n₀).obj (op S.X₁) ⟶
        (HModule'_cohomologyPresheaf k F n₁).obj (op S.X₄)
in `AddCommGrpCat` is the precomposition with the extension class
`(HModule'_shortComplex_shortExact k S).extClass : Ext (...X₁...) (...X₃...) 1`
followed by `AddCommGrpCat.ofHom` to wrap the resulting `AddMonoidHom` as a
categorical morphism. Direct mirror of Mathlib's `MayerVietorisSquare.δ`
(`Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean` L112–114)
for the `ModuleCat k` flavor with `AddCommGrpCat.free → ModuleCat.free k`.

The `[HasExt (Sheaf J (ModuleCat.{u} k))]` typeclass is required (the
`Ext.precomp` operation depends on it) and matches the corresponding
requirement on iter-016 `HModule'_cohomologyPresheafFunctor` / `..._cohomologyPresheaf`,
iter-017 `HModule'_toBiprod` / `..._fromBiprod`, and iter-018
`HModule'_toBiprod_fromBiprod`.

This connecting hom is the missing third link of the Mayer-Vietoris exact
sequence: combined with iter-017's `toBiprod` (sum of restriction) and
`fromBiprod` (difference of restriction), iter-018's `toBiprod ≫ fromBiprod = 0`,
and the iter-022+ packaging into a `ComposableArrows`-form sequence + iter-023+
sequence-iso to `Ext.contravariantSequence` + iter-024+ exactness theorem, it
will yield the full LES `... → Hⁿ(X₄) → Hⁿ(X₂) ⊞ Hⁿ(X₃) → Hⁿ(X₁) → Hⁿ⁺¹(X₄) → ...`
in `ModuleCat k`-valued sheaf cohomology. -/
noncomputable def HModule'_δ
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (S : J.MayerVietorisSquare) (F : Sheaf J (ModuleCat.{u} k))
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (HModule'_cohomologyPresheaf k F n₀).obj (Opposite.op S.X₁) ⟶
      (HModule'_cohomologyPresheaf k F n₁).obj (Opposite.op S.X₄) :=
  AddCommGrpCat.ofHom ((HModule'_shortComplex_shortExact k S).extClass.precomp _ (by omega))

/-- Phase A step 6 *Path 2* (iter-022): the Mayer-Vietoris long exact sequence
in `ModuleCat k`-valued sheaf cohomology, packaged as a `ComposableArrows` of
length 5 in `AddCommGrpCat`. The five composable morphisms are, in order,
`HModule'_toBiprod` at degree `n₀`, `HModule'_fromBiprod` at degree `n₀`, the
connecting hom `HModule'_δ` from degree `n₀` to degree `n₁`, `HModule'_toBiprod`
at degree `n₁`, and `HModule'_fromBiprod` at degree `n₁`. Direct mirror of
Mathlib's `MayerVietorisSquare.sequence`
(`Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean` L120–122)
for the `ModuleCat k` flavor.

The `noncomputable abbrev` form is load-bearing: downstream `dsimp`-based
unfolding (in iter-023+ `HModule'_sequenceIso` and iter-024+
`HModule'_sequence_exact`) needs to access `mk₅`'s field-projection simp
lemmas through the abbrev. -/
noncomputable abbrev HModule'_sequence
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (S : J.MayerVietorisSquare) (F : Sheaf J (ModuleCat.{u} k))
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat 5 :=
  ComposableArrows.mk₅ (HModule'_toBiprod k S F n₀) (HModule'_fromBiprod k S F n₀)
    (HModule'_δ k S F n₀ n₁ h)
    (HModule'_toBiprod k S F n₁) (HModule'_fromBiprod k S F n₁)

/-- Iter-023 aux lemma 1: explicit elementwise formula for `HModule'_toBiprod`
(mirror Mathlib `MayerVietoris.lean` L48–64). -/
lemma HModule'_toBiprod_apply
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (S : J.MayerVietorisSquare) (F : Sheaf J (ModuleCat.{u} k))
    {n : ℕ} (y : (HModule'_cohomologyPresheaf k F n).obj (Opposite.op S.X₄)) :
    HModule'_toBiprod k S F n y =
      (AddCommGrpCat.biprodIsoProd _ _).inv
        ⟨(HModule'_cohomologyPresheaf k F n).map S.f₂₄.op y,
          (HModule'_cohomologyPresheaf k F n).map S.f₃₄.op y⟩ := by
  apply (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective
  dsimp [HModule'_toBiprod]
  ext
  · rw [Iso.addCommGroupIsoToAddEquiv_apply, Iso.addCommGroupIsoToAddEquiv_apply,
      ← AddCommGrpCat.biprodIsoProd_inv_comp_fst_apply, Iso.hom_inv_id_apply,
      ← ConcreteCategory.comp_apply, biprod.lift_fst, Iso.inv_hom_id_apply]
  · rw [Iso.addCommGroupIsoToAddEquiv_apply, Iso.addCommGroupIsoToAddEquiv_apply,
      ← AddCommGrpCat.biprodIsoProd_inv_comp_snd_apply, Iso.hom_inv_id_apply,
      ← ConcreteCategory.comp_apply, biprod.lift_snd, Iso.inv_hom_id_apply]

/-- Iter-023 aux lemma 2: explicit elementwise formula for `HModule'_fromBiprod`
on the inverse of `biprodIsoProd` (mirror Mathlib L77–83). -/
lemma HModule'_fromBiprod_biprodIsoProd_inv_apply
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (S : J.MayerVietorisSquare) (F : Sheaf J (ModuleCat.{u} k))
    {n : ℕ}
    (y₁ : (HModule'_cohomologyPresheaf k F n).obj (Opposite.op S.X₂))
    (y₂ : (HModule'_cohomologyPresheaf k F n).obj (Opposite.op S.X₃)) :
    HModule'_fromBiprod k S F n
        ((AddCommGrpCat.biprodIsoProd _ _).inv ⟨y₁, y₂⟩) =
      (HModule'_cohomologyPresheaf k F n).map S.f₁₂.op y₁ -
        (HModule'_cohomologyPresheaf k F n).map S.f₁₃.op y₂ := by
  dsimp [HModule'_fromBiprod]
  rw [← ConcreteCategory.comp_apply]
  simp [AddCommGrpCat.biprodIsoProd_inv_comp_desc, sub_eq_add_neg]

-- Iter-023 aux lemma 3: bridges `AddCommGrpCat`-side `biprodIsoProd` and
-- `Ext`-side `Ext.biprodAddEquiv` for the `toBiprod` morphism
-- (mirror Mathlib L85–91). The `set_option ... in` and `attribute ... in`
-- wrappers match Mathlib L85, L86 verbatim.
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] HModule'_toBiprod_apply in
lemma HModule'_biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (S : J.MayerVietorisSquare) (F : Sheaf J (ModuleCat.{u} k))
    {n : ℕ} (x : (HModule'_cohomologyPresheaf k F n).obj (Opposite.op S.X₄)) :
    Abelian.Ext.biprodAddEquiv.symm
        ((AddCommGrpCat.biprodIsoProd _ _).hom (HModule'_toBiprod k S F n x)) =
      (Abelian.Ext.mk₀ (HModule'_shortComplex k S).g).comp x (zero_add n) :=
  Abelian.Ext.biprodAddEquiv.injective (by cat_disch)

-- Iter-023 aux lemma 4: bridges the same machinery for the `fromBiprod`
-- morphism (mirror Mathlib L93–106).
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] sub_eq_add_neg in
lemma HModule'_mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (S : J.MayerVietorisSquare) (F : Sheaf J (ModuleCat.{u} k))
    {n : ℕ}
    (x : ↑((HModule'_cohomologyPresheaf k F n).obj (Opposite.op S.X₂) ⊞
           (HModule'_cohomologyPresheaf k F n).obj (Opposite.op S.X₃))) :
    (Abelian.Ext.mk₀ (HModule'_shortComplex k S).f).comp
        (Abelian.Ext.biprodAddEquiv.symm
          ((AddCommGrpCat.biprodIsoProd _ _).hom x)) (zero_add n) =
      (HModule'_fromBiprod k S F n x) := by
  obtain ⟨⟨x₂, x₃⟩, rfl⟩ :=
    (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.surjective x
  dsimp
  rw [Abelian.Ext.biprodAddEquiv_symm_apply,
    Iso.addCommGroupIsoToAddEquiv_symm_apply,
    HModule'_fromBiprod_biprodIsoProd_inv_apply]
  cat_disch

-- Iter-023 main: comparison iso from the iter-022 LES sequence to
-- `Ext.contravariantSequence` (mirror Mathlib L124–138). The technical heart
-- of the Mayer-Vietoris LES.
set_option backward.isDefEq.respectTransparency false in
noncomputable def HModule'_sequenceIso
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (S : J.MayerVietorisSquare) (F : Sheaf J (ModuleCat.{u} k))
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    HModule'_sequence k S F n₀ n₁ h ≅
      Abelian.Ext.contravariantSequence (HModule'_shortComplex_shortExact k S)
        F n₀ n₁ (by omega) :=
  ComposableArrows.isoMk₅ (Iso.refl _)
    ((AddCommGrpCat.biprodIsoProd _ _).trans
      (Abelian.Ext.biprodAddEquiv.symm).toAddCommGrpIso)
    (Iso.refl _) (Iso.refl _)
    ((AddCommGrpCat.biprodIsoProd _ _).trans
      (Abelian.Ext.biprodAddEquiv.symm).toAddCommGrpIso)
    (Iso.refl _)
    (by ext; apply HModule'_biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply)
    (by ext; symm; apply HModule'_mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom)
    (by simp [ComposableArrows.Precomp.map]; rfl)
    (by ext; apply HModule'_biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply)
    (by ext; symm; apply HModule'_mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom)

/-- Iter-026: Mayer-Vietoris LES exactness theorem (mirror Mathlib
`MayerVietoris.lean` L140–141). The iter-022 sequence is exact via the iter-023
comparison iso to `Ext.contravariantSequence`. -/
lemma HModule'_sequence_exact
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (S : J.MayerVietorisSquare) (F : Sheaf J (ModuleCat.{u} k))
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (HModule'_sequence k S F n₀ n₁ h).Exact :=
  ComposableArrows.exact_of_iso (HModule'_sequenceIso k S F n₀ n₁ h).symm
    (Abelian.Ext.contravariantSequence_exact _ _ _ _ _)

/-- Iter-026: `δ ≫ toBiprod = 0` simp companion (mirror Mathlib L143–145). -/
@[reassoc (attr := simp)]
lemma HModule'_δ_toBiprod
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (S : J.MayerVietorisSquare) (F : Sheaf J (ModuleCat.{u} k))
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    HModule'_δ k S F n₀ n₁ h ≫ HModule'_toBiprod k S F n₁ = 0 :=
  (HModule'_sequence_exact k S F n₀ n₁ h).zero 2

/-- Iter-026: `fromBiprod ≫ δ = 0` simp companion (mirror Mathlib L147–149). -/
@[reassoc (attr := simp)]
lemma HModule'_fromBiprod_δ
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (S : J.MayerVietorisSquare) (F : Sheaf J (ModuleCat.{u} k))
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    HModule'_fromBiprod k S F n₀ ≫ HModule'_δ k S F n₀ n₁ h = 0 :=
  (HModule'_sequence_exact k S F n₀ n₁ h).zero 1

end AlgebraicGeometry.Scheme
