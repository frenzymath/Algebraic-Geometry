/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.SheafProperty

/-!
# Sheaves of `k`-modules: finite-length carriers

For a scheme `C` over `Spec k` this file develops the finite-length side of `ModuleCat k`-valued
sheaf cohomology: the cohomology carriers `HModule` (global) and `HModule'` (evaluated at an open),
their degree-zero `k`-linear identifications with Hom groups, the two finiteness hypotheses
`IsAffineHModuleVanishing` (vanishing of `Hⁱ` on affine opens for `i > 0`) and `IsHModuleHomFinite`
(finiteness over `k` of the global sections), and the Čech-side carriers. The structure sheaf these
act on is constructed in `Presheaf.lean` and `SheafProperty.lean`.

On a proper integral `Spec k`-scheme `IsHModuleHomFinite` holds for the structure sheaf, the
geometric input being finiteness of `Γ(C, O_C)` over `k`. No such instance is available for
`IsAffineHModuleVanishing`: producing one requires the comparison between Čech and derived-functor
cohomology on an acyclic cover, which is not proved here.

## Main results

* `HModule`, `HModule'`: `ModuleCat k`-valued sheaf cohomology, globally and at an open.
* `HModule_zero_linearEquiv`, `HModule'_zero_linearEquiv`: the degree-zero identification with a
  `k`-linear Hom group.
* `IsAffineHModuleVanishing`, `IsHModuleHomFinite`: the two finiteness hypotheses.
* `module_finite_globalSections_of_isProper`: `Γ(C, O_C)` is finite over `k` when `C` is integral
  and proper over `Spec k`.
* `instIsHModuleHomFinite_toModuleKSheaf`: the resulting instance for the structure sheaf.
* `Scheme.cechCochain`, `Scheme.cechCohomology`: Čech cochains and cohomology of a sheaf of
  `k`-modules with respect to an indexed family of opens.
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Sheaf cohomology for `ModuleCat k`-valued sheaves, the analogue of `CategoryTheory.Sheaf.H`.
Mathlib's `CategoryTheory.Sheaf.H` is parameterised over `Sheaf J AddCommGrpCat` only, which loses
the `k`-linear structure needed to define a genus. The result here carries `Module k` automatically
via `CategoryTheory.Abelian.Ext.instModule`, so `Module.finrank k` is well-defined on it. It is an
`abbrev` rather than a `def` so that instance synthesis sees through the wrapper to find the
`Module k` and `AddCommGroup` instances. -/
noncomputable abbrev HModule
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasSheafify J (ModuleCat.{u} k)] [HasExt (Sheaf J (ModuleCat.{u} k))]
    (F : Sheaf J (ModuleCat.{u} k)) (n : ℕ) : Type (u+1) :=
  Abelian.Ext ((constantSheaf J (ModuleCat.{u} k)).obj (ModuleCat.of k k)) F n

/-- The `k`-linear identification of `HModule k F 0` with the group of morphisms from the constant
sheaf at `ModuleCat.of k k` to `F`. It is `CategoryTheory.Abelian.Ext.linearEquiv₀`
(`Ext X Y 0 ≃ₗ[R] (X ⟶ Y)` in any `Linear R`-enriched abelian category) specialised to the
`Linear k` enrichment of `Sheaf J (ModuleCat.{u} k)`, which is inferred from
`HasSheafify J (ModuleCat.{u} k)`. On a connected proper `k`-curve this identifies
`H⁰(C, toModuleKSheaf C)` with `Γ(C, O_C)` viewed as a `k`-module. -/
noncomputable def HModule_zero_linearEquiv
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasSheafify J (ModuleCat.{u} k)] [HasExt (Sheaf J (ModuleCat.{u} k))]
    (F : Sheaf J (ModuleCat.{u} k)) :
    HModule k F 0 ≃ₗ[k]
      ((constantSheaf J (ModuleCat.{u} k)).obj (ModuleCat.of k k) ⟶ F) :=
  Abelian.Ext.linearEquiv₀

/-- The `ModuleCat k`-valued cohomology of an object `X : C` with values in a sheaf
`F : Sheaf J (ModuleCat.{u} k)`, mirroring Mathlib's
`Sheaf.H' F n X = (F.cohomologyPresheaf n).obj (op X)` for `AddCommGrpCat`-valued sheaves with
`AddCommGrpCat.free` replaced by `ModuleCat.free k`.

The codomain is `Type u` rather than `ModuleCat.{u} k`: `Abelian.Ext` returns a bare type, which
carries `Module k` through the `Linear k` enrichment via `Abelian.Ext.instModule`. As for
`HModule`, the `abbrev` form is needed so that instance synthesis finds
`Module k (HModule' k F n X)` and `AddCommGroup (HModule' k F n X)`; under `def`,
`Module.finrank` would fail to typecheck.

This is the coefficient carrier for a `ModuleCat k`-valued Mayer-Vietoris long exact sequence on a
`MayerVietorisSquare`, and for the comparison
`cechCohomology_OC C 𝒰 n ≅ HModule k (toModuleKSheaf C) n` on an acyclic cover; neither is proved
here. -/
noncomputable abbrev HModule' (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (F : Sheaf J (ModuleCat.{u} k)) (n : ℕ) (X : C) : Type u :=
  Abelian.Ext ((presheafToSheaf _ _).obj
    ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj X)) F n

/-- The degree-zero identification for `HModule'`, the analogue of `HModule_zero_linearEquiv`: the
`k`-linear identification of `HModule' k F 0 X` with the group of morphisms from the sheafified
representable `(presheafToSheaf _ _).obj ((yoneda ⋙ ModuleCat.free k).obj X)` to `F`. It is
`CategoryTheory.Abelian.Ext.linearEquiv₀` (`Ext X Y 0 ≃ₗ[R] (X ⟶ Y)` in any `Linear R`-enriched
abelian category) at `R = k`, using the `Linear k` enrichment of `Sheaf J (ModuleCat.{u} k)`
obtained from `HasSheafify J (ModuleCat.{u} k)` via `Sheaf.linear`. It is the algebraic input for
`H⁰(C, O_C) ≃ k` on a connected proper `k`-curve. -/
noncomputable def HModule'_zero_linearEquiv
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (F : Sheaf J (ModuleCat.{u} k)) (X : C) :
    HModule' k F 0 X ≃ₗ[k]
      ((presheafToSheaf _ _).obj
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj X) ⟶ F) :=
  Abelian.Ext.linearEquiv₀

/-- If the Hom group `((constantSheaf J _).obj (ModuleCat.of k k) ⟶ F)` is finite over `k`, then so
is `HModule k F 0`. The equivalence `HModule_zero_linearEquiv` identifies the two `k`-modules, and
`Module.Finite.equiv` transports finiteness along it; the `.symm` puts the hypothesis on the Hom
group and the conclusion on the cohomology. For proper geometrically integral `k`-curves the
hypothesis is supplied by finiteness of the global sections. -/
theorem module_finite_HModule_zero
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasSheafify J (ModuleCat.{u} k)] [HasExt (Sheaf J (ModuleCat.{u} k))]
    (F : Sheaf J (ModuleCat.{u} k))
    [Module.Finite k ((constantSheaf J (ModuleCat.{u} k)).obj (ModuleCat.of k k) ⟶ F)] :
    Module.Finite k (HModule k F 0) :=
  Module.Finite.equiv (HModule_zero_linearEquiv k F).symm

/-- The analogue of `Scheme.module_finite_HModule_zero` for `HModule'`: if the Hom group from the
sheafified representable at `X` to `F` is finite over `k`, then so is `HModule' k F 0 X`. The
equivalence `HModule'_zero_linearEquiv` identifies the two `k`-modules and `Module.Finite.equiv`
transports finiteness along its inverse. -/
theorem module_finite_HModule'_zero
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (F : Sheaf J (ModuleCat.{u} k)) (X : C)
    [Module.Finite k ((presheafToSheaf _ _).obj
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj X) ⟶ F)] :
    Module.Finite k (HModule' k F 0 X) :=
  Module.Finite.equiv (HModule'_zero_linearEquiv k F X).symm

/-- `module_finite_HModule_zero` for the structure sheaf `Scheme.toModuleKSheaf C` of a
`Spec k`-scheme `C`. The Grothendieck topology `Opens.grothendieckTopology C.left.toTopCat` is
inferred from the instances `instHasSheafify_Opens_ModuleCatK` and
`instHasExt_Sheaf_Opens_ModuleCatK`, and the sheaf argument from the result type. On a proper
geometrically integral `k`-curve the remaining hypothesis holds because `H⁰(C, O_C) ≃ k` by Stein
factorization on a connected proper curve. -/
theorem module_finite_HModule_zero_curve
    (k : Type u) [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [Module.Finite k
      ((constantSheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)).obj
        (ModuleCat.of k k) ⟶ Scheme.toModuleKSheaf C)] :
    Module.Finite k (Scheme.HModule k (Scheme.toModuleKSheaf C) 0) :=
  Scheme.module_finite_HModule_zero k _

/-- `module_finite_HModule'_zero` for the structure sheaf `Scheme.toModuleKSheaf C` of a
`Spec k`-scheme `C`, evaluated at an open `U` of the underlying topological space. The topology and
the sheaf argument are inferred; the open `U` is explicit. For an affine corner `Xᵢ` of a
Mayer-Vietoris square the Hom group
`((presheafToSheaf _ _).obj ((yoneda ⋙ ModuleCat.free k).obj Xᵢ) ⟶ toModuleKSheaf C)` is
`Γ(Xᵢ, O_C)`, so finiteness of the sections over `k` propagates to
`HModule' k (toModuleKSheaf C) 0 Xᵢ`. -/
theorem module_finite_HModule'_zero_curve
    (k : Type u) [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    (U : TopologicalSpace.Opens C.left.toTopCat)
    [Module.Finite k
      ((presheafToSheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)).obj
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj U) ⟶
          Scheme.toModuleKSheaf C)] :
    Module.Finite k (Scheme.HModule' k (Scheme.toModuleKSheaf C) 0 U) :=
  Scheme.module_finite_HModule'_zero k _ U

/-- Vanishing of higher cohomology on affine opens: for every affine open `U` of `C.left.toTopCat`
and every degree `i > 0`, the cohomology `Scheme.HModule' k F i U` is the zero `k`-module. Since
`HModule'` returns a `Type u` rather than a `ModuleCat` object, the vanishing is phrased as
`Subsingleton`. This is carried as a hypothesis: Serre vanishing on affines is not available for
`ModuleCat k`-valued sheaf cohomology. -/
class IsAffineHModuleVanishing
    (k : Type u) [Field k] (C : Over (Spec (CommRingCat.of k)))
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)) :
    Prop where
  subsingleton_HModule' : ∀ {U : TopologicalSpace.Opens C.left.toTopCat},
    AlgebraicGeometry.IsAffineOpen U → ∀ i, 0 < i →
      Subsingleton (Scheme.HModule' k F i U)

/-- Under affine vanishing, `HModule' k F i U` is finite over `k` for every affine open `U` and
every `i > 0`: the class field gives `Subsingleton (HModule' k F i U)`, and a subsingleton module
is generated by the empty set, hence finite. Together with the degree-zero statements this is the
algebraic half of finiteness of `HModule k (toModuleKSheaf C) 1`. -/
theorem module_finite_HModule'_of_isAffineHModuleVanishing
    (k : Type u) [Field k] (C : Over (Spec (CommRingCat.of k)))
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
    [IsAffineHModuleVanishing k C F]
    {U : TopologicalSpace.Opens C.left.toTopCat}
    (hU : AlgebraicGeometry.IsAffineOpen U) (i : ℕ) (hi : 0 < i) :
    Module.Finite k (Scheme.HModule' k F i U) :=
  have : Subsingleton (Scheme.HModule' k F i U) :=
    IsAffineHModuleVanishing.subsingleton_HModule' (F := F) hU i hi
  inferInstance

/-- Finiteness over `k` of the global Hom group `((constantSheaf _).obj (ModuleCat.of k k) ⟶ F)`,
that is, of the global sections `Γ(C.left, F)`. For `F = O_C` on a proper geometrically integral
`k`-curve this holds because `Γ(C, O_C) ≃ k` by Stein factorization on a proper geometrically
connected curve; see `instIsHModuleHomFinite_toModuleKSheaf`.

The condition is imposed on global sections only, and deliberately not open by open. By the Yoneda,
free-module and sheafification adjunctions, the per-open Hom group
`((presheafToSheaf _ _).obj ((yoneda ⋙ ModuleCat.free k).obj U) ⟶ F)` is `≃ₗ[k] Γ(U, F)`, and on a
proper smooth `k`-curve `Γ(U, O_C)` is *not* finite over `k` for a proper affine open `U`: for the
standard cover of `P¹_k` by two copies of `A¹_k` one has `Γ(Uᵢ, O_{P¹}) = k[t]`, which is infinite
dimensional over `k`. -/
class IsHModuleHomFinite
    (k : Type u) [Field k] (C : Over (Spec (CommRingCat.of k)))
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)) : Prop where
  module_finite_hom : Module.Finite k
    ((constantSheaf (Opens.grothendieckTopology C.left.toTopCat)
        (ModuleCat.{u} k)).obj (ModuleCat.of k k) ⟶ F)

/-- If the global sections of `F` are finite over `k`, so is `HModule k F 0`. Immediate from
`module_finite_HModule_zero`, which transports finiteness along
`HModule_zero_linearEquiv : HModule k F 0 ≃ₗ[k] ((constantSheaf _).obj _ ⟶ F)`. Only one
finiteness hypothesis is needed, on the whole space rather than one per affine open. -/
theorem module_finite_HModule_zero_of_isHModuleHomFinite
    (k : Type u) [Field k] (C : Over (Spec (CommRingCat.of k)))
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
    [IsHModuleHomFinite k C F] :
    Module.Finite k (Scheme.HModule k F 0) :=
  have := IsHModuleHomFinite.module_finite_hom (k := k) (C := C) (F := F)
  module_finite_HModule_zero k F

/-- `module_finite_HModule_zero_of_isHModuleHomFinite` at `F := Scheme.toModuleKSheaf C`, so that
the sheaf argument need not be spelled out at call sites in the curve setting. -/
theorem module_finite_HModule_zero_of_isHModuleHomFinite_curve
    (k : Type u) [Field k] (C : Over (Spec (CommRingCat.of k)))
    [IsHModuleHomFinite k C (Scheme.toModuleKSheaf C)] :
    Module.Finite k (Scheme.HModule k (Scheme.toModuleKSheaf C) 0) :=
  module_finite_HModule_zero_of_isHModuleHomFinite k C _

/-- For `C : Over (Spec (CommRingCat.of k))` an integral `k`-scheme with proper structure morphism,
the global sections `Γ(C, O_C)` form a finite-dimensional `k`-vector space.

This is the classical finiteness statement behind Stein factorization. It is deduced from
`AlgebraicGeometry.finite_appTop_of_universallyClosed`: for `X` integral and `f : X ⟶ Spec K`
universally closed and locally of finite type, the ring map `f.appTop` on global sections is
module-finite. `IsProper f` supplies both `UniversallyClosed f` and `LocallyOfFiniteType f`.

Passing from `RingHom.Finite (C.hom.appTop.hom)` to `Module.Finite k (C.left.presheaf.obj (op ⊤))`,
where the algebra structure on `Γ(C, ⊤)` comes from `kToSection`, uses `RingHom.finite_algebraMap`
together with `Module.Finite.of_equiv_equiv`, transporting the base ring from `Γ(Spec k, ⊤)` to `k`
along the ring isomorphism `Scheme.ΓSpecIso (CommRingCat.of k)`. Compatibility of the two algebra
maps amounts to
`kToSection C (op ⊤).hom = (C.hom.appTop.hom).comp (Scheme.ΓSpecIso _).inv.hom`, which follows
because the hom-set `⊤ ⟶ ⊤` is a subsingleton and the presheaf preserves identities. -/
theorem module_finite_globalSections_of_isProper
    (k : Type u) [Field k] (C : Over (Spec (CommRingCat.of k)))
    [IsIntegral C.left] [IsProper C.hom] :
    Module.Finite k (C.left.presheaf.obj (Opposite.op ⊤)) := by
  have hf : (C.hom.appTop.hom).Finite :=
    AlgebraicGeometry.finite_appTop_of_universallyClosed k C.hom
  letI alg2 : Algebra ((Spec (CommRingCat.of k)).presheaf.obj (Opposite.op ⊤))
               (C.left.presheaf.obj (Opposite.op ⊤))
    := RingHom.toAlgebra C.hom.appTop.hom
  have hM_inter :
      Module.Finite ((Spec (CommRingCat.of k)).presheaf.obj (Opposite.op ⊤))
        (C.left.presheaf.obj (Opposite.op ⊤)) := by
    rw [← RingHom.finite_algebraMap]; exact hf
  refine Module.Finite.of_equiv_equiv
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
    (RingEquiv.refl _) ?_
  ext x
  simp only [RingHom.coe_comp, RingEquiv.coe_toRingHom, RingEquiv.refl_apply,
    Function.comp_apply, RingHom.algebraMap_toAlgebra]
  have h_kts : (Scheme.toModuleKSheaf.kToSection C (Opposite.op ⊤)).hom =
                (C.hom.appTop.hom).comp ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) := by
    ext y
    simp only [Scheme.toModuleKSheaf.kToSection, CommRingCat.hom_comp,
      RingHom.coe_comp, Function.comp_apply]
    exact congrFun (congrArg (·.hom) (C.left.presheaf.map_id (Opposite.op (⊤ :
                TopologicalSpace.Opens C.left.toTopCat)))) _
  calc (CommRingCat.Hom.hom (Scheme.toModuleKSheaf.kToSection C (Opposite.op ⊤)))
        ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv x)
       = (C.hom.appTop.hom).comp ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
          ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv x) :=
              congrFun (congrArg DFunLike.coe h_kts) _
    _  = C.hom.appTop.hom x := by
        simp only [RingHom.coe_comp, Function.comp_apply]
        congr 1
        change ((Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
              (Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom x = x
        rw [Iso.hom_inv_id]; rfl

/-- The `k`-linear equivalence between the global-sections module `(Sheaf.Γ J _).obj F` and the
sections `F.obj.obj (op ⊤)` over the top open, for a sheaf `F` on a topological space `X`.

The underlying isomorphism is `Sheaf.ΓNatIsoSheafSections`: on a site with a terminal object `T`,
the global-sections functor is naturally isomorphic to evaluation at `T`. For the topology of opens
`Opens.grothendieckTopology X` the terminal object of `TopologicalSpace.Opens X` is the top open
`⊤`, by `Preorder.isTerminalTop`. The resulting isomorphism in `ModuleCat k` is upgraded to a
`LinearEquiv` by `Iso.toLinearEquiv`. -/
noncomputable def SheafGammaObj_linearEquiv_top
    (k : Type u) [Field k] {X : TopCat.{u}}
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)) :
    (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} k)).obj F
      ≃ₗ[k] F.obj.obj (Opposite.op (⊤ : TopologicalSpace.Opens X)) :=
  ((Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X)
      (ModuleCat.{u} k) (T := ⊤) (Preorder.isTerminalTop _)).app F).toLinearEquiv

/-- For a proper integral `Spec k`-scheme `C`, the global-sections module
`(Sheaf.Γ).obj (toModuleKSheaf C)` is finite over `k`. Combine
`module_finite_globalSections_of_isProper` with `SheafGammaObj_linearEquiv_top`.

The `haveI` is needed because `Module.Finite.equiv` does not synthesise the finiteness hypothesis
on its source: `module_finite_globalSections_of_isProper` concludes
`Module.Finite k (C.left.presheaf.obj (op ⊤))`, whereas the source of
`(SheafGammaObj_linearEquiv_top _ _).symm` is `(toModuleKSheaf C).obj.obj (op ⊤)`. These are the
same module, by `toModuleKPresheaf_obj`, but the instance has to be registered under the second
spelling. -/
theorem module_finite_gammaObj_of_isProper
    (k : Type u) [Field k] (C : Over (Spec (CommRingCat.of k)))
    [IsIntegral C.left] [IsProper C.hom] :
    Module.Finite k
      ((Sheaf.Γ (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)).obj
        (Scheme.toModuleKSheaf C)) := by
  haveI : Module.Finite k
      ((Scheme.toModuleKSheaf C).obj.obj
        (Opposite.op (⊤ : TopologicalSpace.Opens C.left.toTopCat)) : ModuleCat k) :=
    module_finite_globalSections_of_isProper k C
  exact Module.Finite.equiv
    (SheafGammaObj_linearEquiv_top k (Scheme.toModuleKSheaf C)).symm

/-- Iter-046: applied LinearEquiv from the constant-sheaf-Γ adjunction. For any
sheaf `F : Sheaf J (ModuleCat k)` and `X : ModuleCat k`, gives a `k`-LinearEquiv
between the Hom group `((constantSheaf).obj X ⟶ F)` (sheaf morphisms from the
constant sheaf at `X`) and `(X ⟶ (Sheaf.Γ).obj F)` (module morphisms into the
global sections of `F`).

Built from `(constantSheafΓAdj).homLinearEquiv` (iter-046 Mathlib gap-fill).
The five `haveI` lines establish the typeclass scaffolding required to invoke
the gap-fill: `presheafToSheaf` Linear (via `sheafificationAdjunction`),
`constantSheaf` Additive + Linear (via composition), and `Sheaf.Γ` Additive +
Linear (via the `right_adjoint_*` propagators along `constantSheafΓAdj`).

Used in iter-046's producer instance `instIsHModuleHomFinite_toModuleKSheaf`
to bridge from `Sheaf.Γ.obj`-finiteness (iter-045) to Hom-from-constantSheaf-
finiteness (the `IsHModuleHomFinite` carrier). -/
noncomputable def constantSheafGammaHom_linearEquiv
    (k : Type u) [Field k] {C : Type v} [Category.{u, v} C]
    (J : GrothendieckTopology C)
    [HasSheafify J (ModuleCat.{u} k)] [HasGlobalSectionsFunctor J (ModuleCat.{u} k)]
    (X : ModuleCat.{u} k) (F : Sheaf J (ModuleCat.{u} k)) :
    ((constantSheaf J _).obj X ⟶ F) ≃ₗ[k] (X ⟶ (Sheaf.Γ J _).obj F) :=
  haveI : (presheafToSheaf J (ModuleCat.{u} k)).Linear k :=
    (sheafificationAdjunction J _).left_adjoint_linear k
  haveI : (constantSheaf J (ModuleCat.{u} k)).Additive := by
    unfold constantSheaf; infer_instance
  haveI : (Sheaf.Γ J (ModuleCat.{u} k)).Additive :=
    (constantSheafΓAdj J _).right_adjoint_additive
  haveI : (constantSheaf J (ModuleCat.{u} k)).Linear k := by
    unfold constantSheaf; infer_instance
  haveI : (Sheaf.Γ J (ModuleCat.{u} k)).Linear k :=
    (constantSheafΓAdj J _).right_adjoint_linear k
  (constantSheafΓAdj J _).homLinearEquiv k X F

/-- Iter-046: Hom-from-`k` upgrade. The Hom group `(ModuleCat.of k k ⟶ M)` for
`M : ModuleCat k` is canonically `k`-LinearEquivalent to `M` via `f ↦ f 1`.
Direct one-liner combining `ModuleCat.homLinearEquiv` (Mathlib's
LinearEquiv-version of the underlying-LinearMap correspondence) with
`LinearMap.ringLmapEquivSelf` (the standard `(R →ₗ[R] M) ≃ₗ[S] M` evaluation). -/
noncomputable def homFromOne_linearEquiv (k : Type u) [Field k] (M : ModuleCat.{u} k) :
    (ModuleCat.of k k ⟶ M) ≃ₗ[k] M :=
  (ModuleCat.homLinearEquiv (M := ModuleCat.of k k) (N := M) (S := k)).trans
    (LinearMap.ringLmapEquivSelf k k M)

/-- Iter-046: **the producer instance** for `IsHModuleHomFinite k C (toModuleKSheaf C)`
on a proper integral `Spec k`-scheme `C`. Closes the four-step chain:

  (1) `constantSheafGammaHom_linearEquiv` (iter-046 step 1) bridges the Hom group
      `((constantSheaf).obj k ⟶ toModuleKSheaf C)` to `(k ⟶ Sheaf.Γ.obj (toModuleKSheaf C))`.
  (2) `homFromOne_linearEquiv` (iter-046 step 3) identifies `(k ⟶ M)` with `M`
      as `k`-modules.
  (3) Combined LinearEquiv from (1)+(2): `((constantSheaf).obj k ⟶ toModuleKSheaf C)
      ≃ₗ[k] Sheaf.Γ.obj (toModuleKSheaf C)`.
  (4) `module_finite_gammaObj_of_isProper` (iter-045 step 2) provides
      `Module.Finite k (Sheaf.Γ.obj (toModuleKSheaf C))` from `[IsIntegral C.left]
      [IsProper C.hom]` (iter-044 geometric Stein input).
  (5) Transport via `Module.Finite.equiv (.symm)` of the combined LinearEquiv.

Once landed, iter-043's curve consumer `module_finite_HModule_zero_of_isHModuleHomFinite_curve`
fires automatically on `Module.Finite k (HModule k (toModuleKSheaf C) 0)` queries,
closing the H⁰ side of the genus-finrank Module.Finite ladder.

Marked `instance` (not `theorem`) — this is a *producer* of a typeclass instance,
to be picked up by typeclass synthesis when the consumer asks for
`IsHModuleHomFinite k C (toModuleKSheaf C)`. Hypotheses `[IsIntegral C.left]`,
`[IsProper C.hom]` are class arguments propagated via instance synthesis from
the use site (where `C` is concretely a proper integral `Spec k`-scheme, e.g.\ a
smooth proper geometrically irreducible curve). -/
noncomputable instance instIsHModuleHomFinite_toModuleKSheaf
    (k : Type u) [Field k] (C : Over (Spec (CommRingCat.of k)))
    [IsIntegral C.left] [IsProper C.hom] :
    IsHModuleHomFinite k C (Scheme.toModuleKSheaf C) where
  module_finite_hom := by
    haveI := Scheme.module_finite_gammaObj_of_isProper k C
    let LE1 := constantSheafGammaHom_linearEquiv k
      (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.of k k)
      (Scheme.toModuleKSheaf C)
    let LE2 := homFromOne_linearEquiv k
      ((Sheaf.Γ (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)).obj
        (Scheme.toModuleKSheaf C))
    exact Module.Finite.equiv (LE1.trans LE2).symm

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Phase A step 6 *Path 2* (iter-012 scaffold): the Čech cochain complex of
the structure sheaf of a `Spec k`-scheme `C : Over (Spec (CommRingCat.of k))`,
with respect to an arbitrary indexed family of opens `𝒰 : ι → Opens C.left.toTopCat`.
Built from Mathlib's `CategoryTheory.cechComplexFunctor` (file
`Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean`) applied to the
underlying presheaf of `Scheme.toModuleKSheaf C` (iter-006). The result is a
cochain complex valued in `ModuleCat.{u} k`, indexed by `ℕ`.

The cohomology of this complex is `Scheme.cechCohomology_OC` below. The
downstream comparison theorem (Čech cohomology = derived-functor cohomology
= `Scheme.HModule k (Scheme.toModuleKSheaf C)` for an acyclic cover) is
queued for iter-013+; iter-012 only establishes the Čech-side carrier. -/
noncomputable def Scheme.cechCochain_OC
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat) :
    CochainComplex (ModuleCat.{u} k) ℕ :=
  (cechComplexFunctor 𝒰).obj ((sheafToPresheaf _ _).obj (Scheme.toModuleKSheaf C))

/-- Phase A step 6 *Path 2* (iter-012 scaffold): the `n`-th Čech cohomology
of the structure sheaf for an arbitrary indexed open cover. Defined as the
`n`-th homology of the Čech cochain complex `Scheme.cechCochain_OC`. The
result lives in `ModuleCat.{u} k` and therefore carries a `Module k`
structure for free; the iter-013+ comparison theorem will identify it
with `Scheme.HModule k (Scheme.toModuleKSheaf C) n` when the cover is
acyclic. -/
noncomputable def Scheme.cechCohomology_OC
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat) (n : ℕ) :
    ModuleCat.{u} k :=
  (Scheme.cechCochain_OC C 𝒰).homology n

/-- Iter-047: parameterised Čech cochain complex generalising iter-012's
`Scheme.cechCochain_OC` to any sheaf of `k`-modules `F`, not just the structure
sheaf. Built from the same Mathlib `CategoryTheory.cechComplexFunctor`
(`Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean`) applied to the
underlying presheaf of `F`. The result is a cochain complex valued in
`ModuleCat.{u} k`, indexed by `ℕ`. Iter-012's specialisation
`Scheme.cechCochain_OC C 𝒰` is recovered by setting `F := Scheme.toModuleKSheaf C`
(see `Scheme.cechCochain_OC_eq` below).

This generalisation is the foundational scaffolding the iter-048+ Čech-vs-derived
comparison theorem will build on: the comparison map
`Scheme.cechCohomology k C F 𝒰 n →ₗ[k] Scheme.HModule' k F n (⨆ᵢ 𝒰 i)`
(queued for iter-048) is naturally parameterised over the sheaf `F`, not just
the structure sheaf, so the parameterised carrier is the right level of
generality. -/
noncomputable def Scheme.cechCochain
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat) :
    CochainComplex (ModuleCat.{u} k) ℕ :=
  (cechComplexFunctor 𝒰).obj ((sheafToPresheaf _ _).obj F)

/-- Iter-047: parameterised Čech cohomology generalising iter-012's
`Scheme.cechCohomology_OC`. The `n`-th cohomology of the parameterised Čech
cochain complex. The result lives in `ModuleCat.{u} k`. Iter-012's
specialisation is recovered by `Scheme.cechCohomology_OC_eq` below. -/
noncomputable def Scheme.cechCohomology
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat) (n : ℕ) :
    ModuleCat.{u} k :=
  (Scheme.cechCochain C F 𝒰).homology n

/-- Iter-047 bridge: iter-012's `Scheme.cechCochain_OC` is definitionally the
`F := Scheme.toModuleKSheaf C` specialisation of `Scheme.cechCochain`. The
proof is `rfl` since iter-012's body is the same `(cechComplexFunctor 𝒰).obj
((sheafToPresheaf _ _).obj (Scheme.toModuleKSheaf C))` term. Used by downstream
consumers (iter-048+) to switch between the iter-012 structure-sheaf-specific
form and the iter-047 parameterised form without semantic loss. -/
theorem Scheme.cechCochain_OC_eq
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat) :
    Scheme.cechCochain_OC C 𝒰 = Scheme.cechCochain C (Scheme.toModuleKSheaf C) 𝒰 :=
  rfl

/-- Iter-047 bridge: iter-012's `Scheme.cechCohomology_OC` is definitionally the
`F := Scheme.toModuleKSheaf C` specialisation of `Scheme.cechCohomology`. -/
theorem Scheme.cechCohomology_OC_eq
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat) (n : ℕ) :
    Scheme.cechCohomology_OC C 𝒰 n =
      Scheme.cechCohomology C (Scheme.toModuleKSheaf C) 𝒰 n :=
  rfl

/-- Iter-048: Čech-side acyclicity carrier predicate. The cover `𝒰` is
*Čech-acyclic for the sheaf `F` of `k`-modules* on `C` if positive-degree Čech
cohomology vanishes (in the `Subsingleton` sense — `Scheme.cechCohomology C F 𝒰 n`
has type `ModuleCat.{u} k`, but `Subsingleton` on the underlying type is the
natural and more chainable form). Mirrors the iter-040 / iter-043 carrier-
predicate pattern: a single-field `Prop` class capturing a combinatorial
vanishing condition that downstream consumers receive as an instance argument.

This is the foundational Čech-side input that the iter-051 producer instance for
`IsAffineHModuleVanishing k C (toModuleKSheaf C)` will consume, in conjunction
with the iter-049+ Čech-vs-derived comparison theorem and iter-048's consumer. -/
class Scheme.IsCechAcyclicCover
    {k : Type u} [Field k] {C : Over (Spec (.of k))}
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat) : Prop where
  subsingleton_cechCohomology :
    ∀ (n : ℕ), 0 < n → Subsingleton (Scheme.cechCohomology C F 𝒰 n)

/-- Iter-048: subsingleton transport via Čech acyclicity + comparison.

Given the iter-048 carrier hypothesis `[IsCechAcyclicCover F 𝒰]` AND an explicit
comparison iso `compIso n : cechCohomology C F 𝒰 n ≃ₗ[k] HModule' k F n (⨆ 𝒰 i)`
(the Čech-vs-derived comparison, queued for iter-049+ to construct as a
theorem), conclude that `Subsingleton (HModule' k F n (⨆ 𝒰 i))` for `n ≥ 1`.

The `compIso` is taken as an *explicit argument*, not a class field. The
comparison itself is a `LinearEquiv` (data), so it cannot be a field of a
`Prop`-valued class; more importantly, decoupling the Čech-side combinatorial
vanishing (iter-048) from the substantive comparison theorem (iter-049+) lets
each step land as a single iteration. Iter-049+ will provide the comparison as
a theorem, which iter-048's consumer accepts directly via this argument.

The consumer body extracts the class field (the `Subsingleton` on
`cechCohomology n`) and transports along `(compIso n).symm.toEquiv.subsingleton`. -/
theorem Scheme.subsingleton_HModule'_supr_of_isCechAcyclicCover
    {k : Type u} [Field k] {C : Over (Spec (.of k))}
    {F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)}
    {ι : Type u} {𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat}
    [Scheme.IsCechAcyclicCover F 𝒰]
    (compIso : ∀ (n : ℕ),
      Scheme.cechCohomology C F 𝒰 n ≃ₗ[k]
        Scheme.HModule' k F n (⨆ i, 𝒰 i))
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (Scheme.HModule' k F n (⨆ i, 𝒰 i)) := by
  haveI := Scheme.IsCechAcyclicCover.subsingleton_cechCohomology
    (F := F) (𝒰 := 𝒰) n hn
  exact (compIso n).symm.toEquiv.subsingleton

/-- Iter-048: curve specialisation at `F := Scheme.toModuleKSheaf C`.

Mirrors the iter-039 / iter-042 / iter-043 `_curve` pattern: a thin dot-notation
wrapper that saves call sites in the curve setting (where `F` is the structure
sheaf) from re-typing `Scheme.toModuleKSheaf C` whenever the iter-048 consumer
is chained through. Used by the iter-051 `IsAffineHModuleVanishing k C (toModuleKSheaf C)`
producer instance. -/
theorem Scheme.subsingleton_HModule'_supr_of_isCechAcyclicCover_curve
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    {ι : Type u} {𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat}
    [Scheme.IsCechAcyclicCover (Scheme.toModuleKSheaf C) 𝒰]
    (compIso : ∀ (n : ℕ),
      Scheme.cechCohomology C (Scheme.toModuleKSheaf C) 𝒰 n ≃ₗ[k]
        Scheme.HModule' k (Scheme.toModuleKSheaf C) n (⨆ i, 𝒰 i))
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (Scheme.HModule' k (Scheme.toModuleKSheaf C) n (⨆ i, 𝒰 i)) :=
  Scheme.subsingleton_HModule'_supr_of_isCechAcyclicCover (𝒰 := 𝒰) compIso n hn

end AlgebraicGeometry
