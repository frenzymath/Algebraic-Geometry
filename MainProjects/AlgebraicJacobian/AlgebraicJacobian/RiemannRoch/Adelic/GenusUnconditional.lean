/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Adelic.NonconstantToP1
import AlgebraicJacobian.RiemannRoch.Adelic.P1ChartData
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.AffineDegreeOneVanishing

/-!
# Unconditional genus finiteness: the Mayer–Vietoris `(0, 1)`-slice assembly

This file closes the genus lane: it proves, **without any comparison gate**, that
the genus carrier `H¹(C, 𝒪_C) = HModule k (toModuleKSheaf C) 1` of an AJC curve is
a finite-dimensional `k`-vector space, so `AlgebraicGeometry.genus C` is an honest
natural number.

## The assembly

For a 2-affine cover `S : X.AffineCoverMVSquare` and a sheaf `F` of `k`-modules,
the `(n₀, n₁) = (0, 1)` slice of the Mayer–Vietoris long exact sequence (the
contravariant `Ext`-sequence of the short exact sheaf complex
`0 ⟶ P(U₁ ⊓ U₂) ⟶ P(U₁) ⊞ P(U₂) ⟶ P(U₁ ⊔ U₂) ⟶ 0` of sheafified free modules,
`HModule'_shortComplex_shortExact`) reads

`H⁰(U₁) ⊞ H⁰(U₂) ⟶ H⁰(U₁ ⊓ U₂) ⟶ᵟ H¹(U₁ ⊔ U₂) ⟶ H¹(U₁) ⊞ H¹(U₂)`.

* The H⁰-sections bridge `HModule'_zero_sectionsLinearEquiv` (`SectionsBridge.lean`)
  identifies the degree-0 corners with honest section modules, and its naturality
  companions identify the first map with `AffineCoverMVSquare.sectionDiff`
  (`Cokernel.lean`).  Exactness at `H⁰(U₁ ⊓ U₂)` then computes the kernel of the
  connecting map as `range (sectionDiff)` — with **no** vanishing hypothesis
  (`ker_hModule'DeltaSection`).
* Degree-1 vanishing on the two **pieces** `U₁`, `U₂` (for the structure sheaf this
  is `subsingleton_hModule'_one_toModuleKSheaf_of_isAffineOpen`,
  `AffineDegreeOneVanishing.lean`) kills the right-hand corner, so exactness at
  `H¹(U₁ ⊔ U₂)` makes the connecting map surjective
  (`surjective_hModule'DeltaSection`).
* The first isomorphism theorem then delivers
  `S.H1Cok F = Γ(U₁ ⊓ U₂, F) ⧸ range (sectionDiff) ≃ₗ[k] HModule' k F 1 (U₁ ⊔ U₂)`
  (`h1CokEquivHModule'One`), and the in-tree cover-totality/universe bridge
  `AffineCoverMVSquare.HModule'_X₄_linearEquiv` lands it on the genus carrier
  `HModule k F 1` (`hModuleOneEquivH1CokOfSubsingleton`).

## Universe discipline

Everything here is assembled at `Abelian.Ext.{u}` — the universe of `HModule'`, of
the H⁰-sections bridge and of the degree-1 affine vanishing.  We do **not** use the
curve-specialised LES wrappers (whose `HasExt` instance is baked at `Ext.{u+1}`,
cf. the universe note of `CechAcyclicInstance.lean`); instead we consume Mathlib's
universe-polymorphic element-level exactness lemmas
`Abelian.Ext.contravariant_sequence_exact₁'/₃` directly on the in-tree short exact
complex, instantiated at `Ext.{u}`.  The single `Ext.{u} → Ext.{u+1}` hop is then
the one already packaged in `AffineCoverMVSquare.HModule'_X₄_linearEquiv`
(via `Abelian.Ext.chgUnivLinearEquiv`), so no vanishing statement ever needs to be
transported across universes.

## Consumables

* `AffineCoverMVSquare.hModuleOneEquivH1Cok_curve` — **gate-free N5+N6**: for the
  structure sheaf `toModuleKSheaf C` of *any* `Spec k`-scheme `C` and *every*
  2-affine cover `S`, `HModule k (toModuleKSheaf C) 1 ≃ₗ[k] S.H1Cok (toModuleKSheaf C)`.
  This discharges, for the structure sheaf, exactly the equivalence the gated
  `AffineCoverMVSquare.hModuleOneEquivH1Cok` (`Cokernel.lean`) promised under
  `HasCechToHModuleIso` — no gate.
* `Adelic.module_finite_hModule_one` — genus finiteness under the geometric gates
  `HasFiniteMapToP1 C` + `P1HasLaurentChartData k` (the latter already an
  unconditional instance).
* `Adelic.instModuleFiniteHModuleOne` — the **unconditional instance** for AJC
  curves: under `[SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIntegral C.hom]` alone, `Module.Finite k (HModule k (toModuleKSheaf C) 1)`.

See `blueprint/src/chapters/RiemannRoch_Adelic.tex`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

section MVSlice

variable {k : Type u} [Field k] {X : Scheme.{u}} (S : X.AffineCoverMVSquare)
  (F : Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k))
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k))]

/-! ## The connecting map of the `(0, 1)`-slice, in `k`-linear form

The Mayer–Vietoris connecting homomorphism `HModule'_δ` (`MayerVietorisCore.lean`)
is packaged as an `AddCommGrpCat`-morphism; here we need its `k`-linear
incarnation (precomposition with the extension class is `k`-bilinear,
`Abelian.Ext.precompOfLinear`), with the same underlying function. -/

set_option backward.isDefEq.respectTransparency false in
/-- The Mayer–Vietoris connecting map `δ : H⁰(U₁ ⊓ U₂, F) →ₗ[k] H¹(U₁ ⊔ U₂, F)` of a
2-affine cover, as a `k`-linear map on the `HModule'` carriers: precomposition with
the extension class of the short exact Mayer–Vietoris complex of sheafified free
modules (`HModule'_shortComplex_shortExact`).  Its underlying function agrees
definitionally with that of the `AddCommGrpCat`-morphism `HModule'_δ`.

**Statement audit (genus-lane wave 2, 2026-07-09): definition** — no truth content;
the honest content is `ker_hModule'DeltaSection` and
`surjective_hModule'DeltaSection` below. -/
noncomputable def AffineCoverMVSquare.hModule'Delta :
    HModule' k F 0 (S.U₁ ⊓ S.U₂) →ₗ[k] HModule' k F 1 (S.U₁ ⊔ S.U₂) :=
  (HModule'_shortComplex_shortExact k S.toMayerVietorisSquare).extClass.precompOfLinear
    k F rfl

set_option backward.isDefEq.respectTransparency false in
/-- Elementwise formula for `hModule'Delta`: it is `Ext`-precomposition with the
extension class.  Definitional (`Abelian.Ext.bilinearCompOfLinear` applies as the
literal composition). -/
lemma AffineCoverMVSquare.hModule'Delta_apply (x : HModule' k F 0 (S.U₁ ⊓ S.U₂)) :
    S.hModule'Delta F x =
      (HModule'_shortComplex_shortExact k S.toMayerVietorisSquare).extClass.comp x rfl :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The section-level connecting map** `Γ(U₁ ⊓ U₂, F) →ₗ[k] H¹(U₁ ⊔ U₂, F)` of a
2-affine cover: the composite of the inverse H⁰-sections bridge
(`HModule'_zero_sectionsLinearEquiv`, `SectionsBridge.lean`) with the Mayer–Vietoris
connecting map `hModule'Delta`.  This is the map whose kernel is the coboundary
space `range (sectionDiff)` and whose surjectivity (under degree-1 vanishing on the
pieces) exhibits `H¹(U₁ ⊔ U₂, F)` as the concrete 2-cover Čech cokernel `H1Cok`. -/
noncomputable def AffineCoverMVSquare.hModule'DeltaSection :
    F.obj.obj (Opposite.op (S.U₁ ⊓ S.U₂)) →ₗ[k] HModule' k F 1 (S.U₁ ⊔ S.U₂) :=
  (S.hModule'Delta F).comp
    (HModule'_zero_sectionsLinearEquiv k F (S.U₁ ⊓ S.U₂)).symm.toLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- Elementwise formula for `hModule'DeltaSection`.  Definitional. -/
lemma AffineCoverMVSquare.hModule'DeltaSection_apply
    (s : F.obj.obj (Opposite.op (S.U₁ ⊓ S.U₂))) :
    S.hModule'DeltaSection F s =
      S.hModule'Delta F ((HModule'_zero_sectionsLinearEquiv k F (S.U₁ ⊓ S.U₂)).symm s) :=
  rfl

/-! ## The degree-0 corner: `mk₀ f`-precomposition is the section difference

The first map of the `(0, 1)`-slice is `Ext`-precomposition with the map
`f : P(U₁ ⊓ U₂) ⟶ P(U₁) ⊞ P(U₂)` of the Mayer–Vietoris short complex.  Through the
`Ext`-biproduct decomposition and the H⁰-sections bridge this is exactly the
difference-of-restrictions map `sectionDiff` of `Cokernel.lean`. -/

set_option backward.isDefEq.respectTransparency false in
/-- **The degree-0 corner identification.**  For sections `a ∈ Γ(U₁, F)`,
`b ∈ Γ(U₂, F)`, precomposing the biproduct-packaged pair of their H⁰ classes with
the Mayer–Vietoris map `f` yields the H⁰ class of the section difference
`a|_{U₁ ⊓ U₂} − b|_{U₁ ⊓ U₂} = sectionDiff (a, b)`.

Blueprint: the square "`H⁰(U₁) ⊕ H⁰(U₂) → H⁰(U₁ ⊓ U₂)` versus
`Γ(U₁) ⊕ Γ(U₂) → Γ(U₁ ⊓ U₂)`" commutes.  Proof: the in-tree bridge lemmas
`HModule'_mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom` and
`HModule'_fromBiprod_biprodIsoProd_inv_apply` (`MayerVietorisCore.lean`) convert
the `Ext`-precomposition into the difference of cohomology-presheaf restrictions,
and the inverse naturality of the H⁰-sections bridge
(`HModule'_zero_sectionsLinearEquiv_symm_naturality_map`) converts those into
presheaf restrictions; the square's legs `f₁₂`/`f₁₃` are literally
`homOfLE inf_le_left`/`homOfLE inf_le_right`, i.e. the constituents of
`sectionDiff`.

**Statement audit (genus-lane wave 2, 2026-07-09): TRUE at stated generality.**
Any scheme `X`, any sheaf `F` of `k`-modules, any 2-affine cover bundle `S` (the
affineness and cover fields are not used); no vanishing hypotheses. -/
lemma AffineCoverMVSquare.mk₀_f_comp_sectionPair
    (a : F.obj.obj (Opposite.op S.U₁)) (b : F.obj.obj (Opposite.op S.U₂)) :
    (Abelian.Ext.mk₀ (HModule'_shortComplex k S.toMayerVietorisSquare).f).comp
        (Abelian.Ext.biprodAddEquiv.symm
          ((HModule'_zero_sectionsLinearEquiv k F S.U₁).symm a,
           (HModule'_zero_sectionsLinearEquiv k F S.U₂).symm b)) (zero_add 0) =
      (HModule'_zero_sectionsLinearEquiv k F (S.U₁ ⊓ S.U₂)).symm
        (S.sectionDiff F (a, b)) := by
  have h4 := HModule'_mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom k
    S.toMayerVietorisSquare F
    ((AddCommGrpCat.biprodIsoProd _ _).inv
      ((HModule'_zero_sectionsLinearEquiv k F S.U₁).symm a,
       (HModule'_zero_sectionsLinearEquiv k F S.U₂).symm b))
  rw [Iso.inv_hom_id_apply] at h4
  have h5 := HModule'_zero_sectionsLinearEquiv_symm_naturality_map k F
    (U := S.U₁) (V := S.U₁ ⊓ S.U₂) S.toMayerVietorisSquare.f₁₂ a
  have h6 := HModule'_zero_sectionsLinearEquiv_symm_naturality_map k F
    (U := S.U₂) (V := S.U₁ ⊓ S.U₂) S.toMayerVietorisSquare.f₁₃ b
  rw [h4, HModule'_fromBiprod_biprodIsoProd_inv_apply]
  refine (congrArg₂ (· - ·) h5 h6).trans ?_
  exact (map_sub ((HModule'_zero_sectionsLinearEquiv k F (S.U₁ ⊓ S.U₂)).symm)
    ((F.obj.map S.toMayerVietorisSquare.f₁₂.op).hom a)
    ((F.obj.map S.toMayerVietorisSquare.f₁₃.op).hom b)).symm

/-! ## Exactness at `H⁰(U₁ ⊓ U₂)`: the kernel of the connecting map -/

set_option backward.isDefEq.respectTransparency false in
/-- **The kernel of the section-level connecting map is the coboundary space**:
`ker (hModule'DeltaSection) = range (sectionDiff)`.

Blueprint: exactness of the Mayer–Vietoris sequence at `H⁰(U₁ ⊓ U₂)` (Mathlib's
`Abelian.Ext.contravariant_sequence_exact₁'` on the short exact complex of
sheafified free modules, instantiated at `Ext.{u}`), with the degree-0 corners
identified with section modules through the H⁰-sections bridge
(`mk₀_f_comp_sectionPair`).

**Statement audit (genus-lane wave 2, 2026-07-09): TRUE at stated generality.**
Any scheme `X`, any sheaf `F` of `k`-modules, any `S` — this half of the slice
needs **no** vanishing hypothesis (only the sequence's exactness at the degree-0
corner).  Both inclusions come from the same `Function.Exact` fact. -/
lemma AffineCoverMVSquare.ker_hModule'DeltaSection :
    LinearMap.ker (S.hModule'DeltaSection F) = LinearMap.range (S.sectionDiff F) := by
  have hfe := Abelian.Ext.contravariant_sequence_exact₁'
    (HModule'_shortComplex_shortExact k S.toMayerVietorisSquare) F 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at hfe
  ext s
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hs
    obtain ⟨y, hy⟩ := (hfe ((HModule'_zero_sectionsLinearEquiv k F (S.U₁ ⊓ S.U₂)).symm s)).mp hs
    refine ⟨(HModule'_zero_sectionsLinearEquiv k F S.U₁ (Abelian.Ext.biprodAddEquiv y).1,
      HModule'_zero_sectionsLinearEquiv k F S.U₂ (Abelian.Ext.biprodAddEquiv y).2), ?_⟩
    apply (HModule'_zero_sectionsLinearEquiv k F (S.U₁ ⊓ S.U₂)).symm.injective
    rw [← S.mk₀_f_comp_sectionPair F]
    simp only [LinearEquiv.symm_apply_apply]
    rw [Prod.mk.eta, AddEquiv.symm_apply_apply]
    exact hy
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact (hfe ((HModule'_zero_sectionsLinearEquiv k F (S.U₁ ⊓ S.U₂)).symm
        (S.sectionDiff F (a, b)))).mpr
      ⟨Abelian.Ext.biprodAddEquiv.symm
          ((HModule'_zero_sectionsLinearEquiv k F S.U₁).symm a,
           (HModule'_zero_sectionsLinearEquiv k F S.U₂).symm b),
        S.mk₀_f_comp_sectionPair F a b⟩

/-! ## Exactness at `H¹(U₁ ⊔ U₂)`: surjectivity under degree-1 vanishing -/

set_option backward.isDefEq.respectTransparency false in
/-- **Surjectivity of the connecting map under degree-1 vanishing on the pieces.**
If `H¹(U₁, F)` and `H¹(U₂, F)` vanish, the section-level connecting map
`Γ(U₁ ⊓ U₂, F) → H¹(U₁ ⊔ U₂, F)` is surjective.

Blueprint: exactness of the Mayer–Vietoris sequence at `H¹(U₁ ⊔ U₂)` (Mathlib's
element-level `Abelian.Ext.contravariant_sequence_exact₃` at `Ext.{u}`): the next
term `H¹(U₁) ⊞ H¹(U₂)` is a subsingleton (via the `Ext`-biproduct decomposition
`Abelian.Ext.biprodAddEquiv`), so every degree-1 class on `U₁ ⊔ U₂` maps to `0`
there and hence lifts through the connecting map; the H⁰-sections bridge is
surjective onto the degree-0 corner.

**Statement audit (genus-lane wave 2, 2026-07-09): TRUE at stated generality.**
Any scheme `X`, any sheaf `F` of `k`-modules; the vanishing enters only through
the two `Subsingleton` hypotheses (the overlap `U₁ ⊓ U₂` needs **no** vanishing at
this degree — correct: Leray for the `(0,1)`-slice of a 2-cover only consumes
`H¹` of the pieces). -/
lemma AffineCoverMVSquare.surjective_hModule'DeltaSection
    (h₁ : Subsingleton (HModule' k F 1 S.U₁))
    (h₂ : Subsingleton (HModule' k F 1 S.U₂)) :
    Function.Surjective (S.hModule'DeltaSection F) := by
  intro y
  haveI hb : Subsingleton
      (Abelian.Ext (HModule'_shortComplex k S.toMayerVietorisSquare).X₂ F 1) := by
    haveI : Subsingleton (Abelian.Ext
        ((presheafToSheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)).obj
          (yoneda.obj (S.toMayerVietorisSquare.toSquare.X₂) ⋙ ModuleCat.free k)) F 1) := h₁
    haveI : Subsingleton (Abelian.Ext
        ((presheafToSheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)).obj
          (yoneda.obj (S.toMayerVietorisSquare.toSquare.X₃) ⋙ ModuleCat.free k)) F 1) := h₂
    exact (Abelian.Ext.biprodAddEquiv
      (X₁ := (presheafToSheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)).obj
        (yoneda.obj (S.toMayerVietorisSquare.toSquare.X₂) ⋙ ModuleCat.free k))
      (X₂ := (presheafToSheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)).obj
        (yoneda.obj (S.toMayerVietorisSquare.toSquare.X₃) ⋙ ModuleCat.free k))
      (Y := F) (n := 1)).toEquiv.subsingleton
  obtain ⟨x, hx⟩ := Abelian.Ext.contravariant_sequence_exact₃
    (HModule'_shortComplex_shortExact k S.toMayerVietorisSquare) F
    (n₁ := 1) y (Subsingleton.elim _ _) (n₀ := 0) rfl
  refine ⟨HModule'_zero_sectionsLinearEquiv k F (S.U₁ ⊓ S.U₂) x, ?_⟩
  rw [S.hModule'DeltaSection_apply F, LinearEquiv.symm_apply_apply]
  exact hx

/-! ## The `(0, 1)`-slice assembled: `H1Cok ≃ H¹` -/

set_option backward.isDefEq.respectTransparency false in
/-- **The Mayer–Vietoris `(0, 1)`-slice**: under degree-1 vanishing on the two
pieces, the concrete 2-cover Čech cokernel is the derived `H¹` of the union:
`S.H1Cok F = Γ(U₁ ⊓ U₂, F) ⧸ range (sectionDiff) ≃ₗ[k] HModule' k F 1 (U₁ ⊔ U₂)`.

Blueprint: Leray's theorem for the degree-1 cohomology of a 2-cover with
`H¹`-acyclic pieces, here as the first isomorphism theorem for the section-level
connecting map (`ker_hModule'DeltaSection` + `surjective_hModule'DeltaSection`).

**Statement audit (genus-lane wave 2, 2026-07-09): TRUE at stated generality.**
Any scheme `X`, any sheaf `F` of `k`-modules, vanishing only on the two pieces;
this is the honest generality of the classical statement (the overlap plays no
acyclicity role in degree 1). -/
noncomputable def AffineCoverMVSquare.h1CokEquivHModule'One
    (h₁ : Subsingleton (HModule' k F 1 S.U₁))
    (h₂ : Subsingleton (HModule' k F 1 S.U₂)) :
    S.H1Cok F ≃ₗ[k] HModule' k F 1 (S.U₁ ⊔ S.U₂) :=
  (Submodule.quotEquivOfEq _ _ (S.ker_hModule'DeltaSection F).symm).trans
    ((S.hModule'DeltaSection F).quotKerEquivOfSurjective
      (S.surjective_hModule'DeltaSection F h₁ h₂))

set_option backward.isDefEq.respectTransparency false in
/-- **The gate-free N6 comparison, abstract form**: under degree-1 vanishing on the
two pieces of a 2-affine cover, the genus-degree cohomology `HModule k F 1` is the
concrete two-chart cokernel `Ȟ¹ = Γ(U₁ ⊓ U₂, F) ⧸ (Γ(U₁, F) + Γ(U₂, F))`.

This is the equivalence the gated `AffineCoverMVSquare.hModuleOneEquivH1Cok`
(`Cokernel.lean`) promised under the `HasCechToHModuleIso` comparison gate, with the
gate replaced by its honest mathematical content at degree 1: the `(0, 1)` MV slice
(`h1CokEquivHModule'One`) chained with the in-tree cover-totality/universe bridge
`AffineCoverMVSquare.HModule'_X₄_linearEquiv` (the only `Ext.{u} → Ext.{u+1}` hop,
`Abelian.Ext.chgUnivLinearEquiv` inside).

**Statement audit (genus-lane wave 2, 2026-07-09): TRUE at stated generality.**
The `cover` field `U₁ ⊔ U₂ = ⊤` of `S` enters exactly here (through
`HModule'_X₄_linearEquiv`), identifying `H¹(U₁ ⊔ U₂)` with the global `H¹`. -/
noncomputable def AffineCoverMVSquare.hModuleOneEquivH1CokOfSubsingleton
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k))]
    (h₁ : Subsingleton (HModule' k F 1 S.U₁))
    (h₂ : Subsingleton (HModule' k F 1 S.U₂)) :
    HModule k F 1 ≃ₗ[k] S.H1Cok F :=
  ((S.h1CokEquivHModule'One F h₁ h₂).trans (S.HModule'_X₄_linearEquiv k F 1)).symm

end MVSlice

/-! ## The curve consumable: gate-free `H¹ ≃ H1Cok` for the structure sheaf -/

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}

/-- **Gate-free N5+N6 for the structure sheaf (the genus-lane consumable).**  For
*any* `Spec k`-scheme `C` and *every* 2-affine cover `S` of `C.left`, the
genus-degree cohomology of the structure sheaf of `k`-modules is the concrete
two-chart Čech cokernel:
`HModule k (toModuleKSheaf C) 1 ≃ₗ[k] S.H1Cok (toModuleKSheaf C)`.

The degree-1 vanishing inputs are supplied **unconditionally** by the wave-1'
degree-1 affine vanishing `subsingleton_hModule'_one_toModuleKSheaf_of_isAffineOpen`
(`AffineDegreeOneVanishing.lean`) on the affine pieces `U₁`, `U₂`; the `HasExt`
instances synthesise from Grothendieck-abelianness (`CechComparisonGate.lean`).
This discharges, for `F := toModuleKSheaf C`, exactly the equivalence that the
`HasCechToHModuleIso`-gated `AffineCoverMVSquare.hModuleOneEquivH1Cok`
(`Cokernel.lean`) promised — with no gate.

**Statement audit (genus-lane wave 2, 2026-07-09): TRUE at stated generality.**
No properness/noetherian/curve hypotheses: the vanishing input holds for every
affine open of every `Spec k`-scheme, and the MV slice is unconditional. -/
noncomputable def AffineCoverMVSquare.hModuleOneEquivH1Cok_curve
    (S : C.left.AffineCoverMVSquare) :
    HModule k (Scheme.toModuleKSheaf C) 1 ≃ₗ[k] S.H1Cok (Scheme.toModuleKSheaf C) :=
  S.hModuleOneEquivH1CokOfSubsingleton (Scheme.toModuleKSheaf C)
    (subsingleton_hModule'_one_toModuleKSheaf_of_isAffineOpen k C S.isAffineOpen_U₁)
    (subsingleton_hModule'_one_toModuleKSheaf_of_isAffineOpen k C S.isAffineOpen_U₂)

end Curve

end AlgebraicGeometry.Scheme

/-! ## Genus finiteness, unconditional for AJC curves -/

namespace AlgebraicGeometry.Adelic

open AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- **Genus finiteness of the curve (node `N12`), geometric-gate form.**  For a
curve `C` over `k` with a finite morphism to ℙ¹ (`HasFiniteMapToP1`) and the ℙ¹
chart data (`P1HasLaurentChartData`, an unconditional instance), the genus carrier
`H¹(C, 𝒪_C) = HModule k (toModuleKSheaf C) 1` is a finite `k`-module.

This feeds the gate-free comparison `hModuleOneEquivH1Cok_curve` into the `N11`
keystone `module_finite_hModule_one_of_finite_map` (`FinitenessP1.lean`): the
pullback of the standard ℙ¹ charts is a 2-affine cover with finite-dimensional
Čech cokernel, and the comparison transports the finiteness to `H¹`.

**Statement audit (genus-lane wave 2, 2026-07-09): TRUE at stated generality** —
the honest hypotheses are exactly the keystone's geometric gates; both are derived
(`HasFiniteMapToP1` from the AJC ambient instances, `P1HasLaurentChartData`
unconditionally), so see `instModuleFiniteHModuleOne` below for the instance form. -/
theorem module_finite_hModule_one (C : Over (Spec (CommRingCat.of k)))
    [HasFiniteMapToP1 C] [P1HasLaurentChartData k] :
    Module.Finite k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) :=
  module_finite_hModule_one_of_finite_map C
    (fun S => ⟨S.hModuleOneEquivH1Cok_curve⟩)

/-- **Genus finiteness of the curve — UNCONDITIONAL for AJC curves.**  Under the
ambient AJC hypotheses alone (smooth of relative dimension 1, proper,
geometrically integral over a field `k`), the genus carrier
`H¹(C, 𝒪_C) = HModule k (toModuleKSheaf C) 1` is a finite-dimensional `k`-vector
space.  Hence `AlgebraicGeometry.genus C = finrank k H¹(C, 𝒪_C)` is an honest
natural number on every AJC curve.

The gates of `module_finite_hModule_one` synthesise: `HasFiniteMapToP1 C` through
`existsNonconstantMapToProjInt_of_ajc` → `existsNonconstantMapToP1_of_…` →
`hasFiniteMapToP1_of_existsNonconstantMapToP1` (`NonconstantToP1.lean`,
`FiniteMapToP1.lean`; `GeometricallyIrreducible` from `GeometricallyIntegral`),
and `P1HasLaurentChartData k` by `instP1HasLaurentChartData` (`P1ChartData.lean`).

**Statement audit (genus-lane wave 2, 2026-07-09): TRUE at stated generality.**
Registered as an instance: the head `Module.Finite k (Abelian.Ext … 1)` is
discrimination-tree-keyed on the `Ext` of the constant sheaf against
`toModuleKSheaf C`, so it fires only on genus-carrier goals.  `GeometricallyIntegral`
is the FGA-campaign ambient form (`instHasPicScheme`).

**Update (2026-07-27).** An earlier version of this note said Mathlib v4.31 has no
`SmoothOfRelativeDimension → GeometricallyReduced` instance, so that the
`GeometricallyIrreducible`-only variant — the hypothesis set of
`AlgebraicGeometry.genus` — was "not yet derivable".  That is no longer true:
`AlgebraicJacobian/Curve/GeometricallyReduced.lean` proves
`Smooth.geometricallyReduced` in mathlib generality, so
`[SmoothOfRelativeDimension 1] [IsProper] [GeometricallyIrreducible]` synthesises
`GeometricallyIntegral` and this instance applies **at the challenge's own
hypotheses**, with nothing extra. -/
instance instModuleFiniteHModuleOne (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom] :
    Module.Finite k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) :=
  module_finite_hModule_one C

/-- Genus finiteness in the hypothesis shape of `AlgebraicGeometry.genus`
(challenge.lean: smooth + proper + geometrically **irreducible**), with the geometric
reducedness supplied as an extra hypothesis: the genus carrier is finite.

**This declaration is now redundant** (2026-07-27).  It existed only because Mathlib
v4.31 lacked the `smooth ⟹ geometrically reduced` instance, and its docstring used to
cite that gap.  The gap is closed in-tree by
`AlgebraicJacobian/Curve/GeometricallyReduced.lean` (`Smooth.geometricallyReduced`), so
`instModuleFiniteHModuleOne` already applies without the `GeometricallyReduced`
hypothesis.  Kept as a harmless convenience wrapper for callers that happen to have the
reducedness instance in hand; new code should prefer `instModuleFiniteHModuleOne`. -/
theorem module_finite_hModule_one_of_geometricallyReduced
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyReduced C.hom] [GeometricallyIrreducible C.hom] :
    Module.Finite k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) :=
  haveI : GeometricallyIntegral C.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible C.hom
  module_finite_hModule_one C

end AlgebraicGeometry.Adelic
