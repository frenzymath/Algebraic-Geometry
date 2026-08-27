/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Cohomology.MayerVietorisCover

/-!
# The 2-cover Čech cokernel `Ȟ¹(D)` for adelic Riemann–Roch (nodes N5–N7)

This file is part of the **adelic Riemann–Roch lane** (see the lane design document).
It realises the degree-`1` cohomology of a curve as the concrete cokernel of a
two-chart cover — the algebraic incarnation of Weil's repartition quotient
`A_K / (A_K(D) + K)`.

## The bridge from genus `H¹` to the Čech `H¹` (node N6)

The project's genus carrier is `H¹(C, 𝒪_C) = HModule k (toModuleKSheaf C) 1`.
For a cover `𝒰` of `C` with `⨆ 𝒰 = ⊤` that is a **good** (Leray) cover — i.e. one
for which the Čech-to-derived comparison `HasCechToHModuleIso F 𝒰` holds — there is a
`k`-linear identification
```
HModule k F 1  ≃ₗ[k]  cechCohomology C F 𝒰 1,
```
obtained by chaining the comparison iso `cechToHModuleIso` (iter-050) with the
universe bridge `HModule'_eq_HModule_linearEquiv` (iter-034) at the terminal open
`⊤ = ⨆ 𝒰`.  This is `hModuleOne_linearEquiv_cechCohomology`.

The hypothesis `HasCechToHModuleIso F 𝒰` is the existing project **gate** (a
single-field `Prop` class with no unconditional instance for a 2-affine cover of a
positive-genus curve): the equivalence is delivered *conditional* on that class,
exactly as the design intends.  Note that `IsCechAcyclicCover F 𝒰` for the whole
curve is **not** available (nor true) here: for a genus-`g` curve the degree-`1`
Čech cohomology of a 2-affine cover is `k^g ≠ 0`, so it is deliberately *not*
assumed — the comparison `HasCechToHModuleIso` (which does *not* force the
cohomology to vanish) is the correct and honest hypothesis.

## The concrete section-level cokernel (node N5 target, definition)

For a bundled 2-affine cover `S : X.AffineCoverMVSquare` and a sheaf `F` of
`k`-modules, the **difference-of-restrictions** map
```
δ : Γ(U₁, F) × Γ(U₂, F) →ₗ[k] Γ(U₁ ⊓ U₂, F),   (a, b) ↦ a|_{U₁∩U₂} − b|_{U₁∩U₂}
```
is `AffineCoverMVSquare.sectionDiff`.  Its cokernel `AffineCoverMVSquare.H1Cok`
is the concrete `Ȟ¹`, and its kernel `AffineCoverMVSquare.sectionGlue` is the
`H⁰ = L(D)` sheaf-gluing space (global sections `= { f : agree on the overlap }`).

Because `F` is an arbitrary sheaf of `k`-modules, `H1Cok S F` is *already* the
divisor-twisted `Ȟ¹(D)`: specialising `F := 𝒪_C(D)` once N3's `sectionOfDivisor`
lands recovers the `H¹(D)` of the χ-ledger.

## The concrete 2-cover family and the N6 bridge on it (this wave)

`AffineCoverMVSquare.coverFamily : ULift (Fin 2) → Opens X` packages `U₁, U₂` as the
`Type u`-indexed family that `Scheme.cechCohomology` / the N6 bridge consume, with
`iSup_coverFamily : ⨆ i, S.coverFamily i = ⊤` the family-form of the cover totality.
`hModuleOne_linearEquiv_cechCohomology_coverFamily` then lands the N6 bridge on this
concrete family: `HModule k F n ≃ₗ[k] cechCohomology C F S.coverFamily n` (gated on
`HasCechToHModuleIso F S.coverFamily`).  Chaining node N5 (below) into this at `n = 1`
gives the lane's consumable corollary `HModule k F 1 ≃ₗ[k] H1Cok S F`.

## The N5 identification `cechCohomology C F S.coverFamily 1 ≃ₗ[k] H1Cok S F` (PROVED)

The in-tree `cechCohomology` is the homology of Mathlib's **unnormalized**
`cechComplexFunctor` (`FormalCoproduct.cochainComplexFunctor` of the Čech nerve): in
degree `n` the product runs over **all** `Fin (n+1) → ι` (not just increasing
multi-indices), and the differential `dⁿ = ∑_{i} (-1)^i δⁱ` is the alternating sum of
the cosimplicial cofaces `δⁱ = evalOp(P)(mapPower δ_i)` (a `Pi.lift` of projections to
`x ∘ δ_i` followed by the restriction `P(⨅ U∘(x∘δ_i)) → P(⨅ U∘x)`).  For the 2-element
cover (`ι = ULift (Fin 2)`) this is
```
  M⁰ = Γ(U₀) × Γ(U₁)                         (indices Fin 1 → ι)
  M¹ = Γ(U₀) × Γ(U₀₁) × Γ(U₀₁) × Γ(U₁)       (indices (0,0),(0,1),(1,0),(1,1))
  M² = ∏ over the 8 indices Fin 3 → ι         (incl. the degenerate diagonals)
```
where `Γ(U₀₁) = Γ(U₀ ⊓ U₁)`, and the two diagonal factors of `M¹` are the degenerate
cofaces `U_i ⊓ U_i = U_i`.  Writing a degree-1 cochain as `(p, q, r, s)`:

* `d⁰(a, b) = (0, b|₀₁ − a|₀₁, a|₀₁ − b|₀₁, 0)`, so
  `im d⁰ = { (0, w, −w, 0) : w ∈ range (S.sectionDiff F) }` (note `w = b|₀₁ − a|₀₁` and
  `sectionDiff (a,b) = a|₀₁ − b|₀₁ = −w`, whence the images coincide as subgroups);
* `(d¹ n)_{(x₀,x₁,x₂)} = n_{(x₁,x₂)}| − n_{(x₀,x₂)}| + n_{(x₀,x₁)}|`.  The eight
  components force, after restriction (each triple intersection collapses to `U₀`, `U₁`
  or `U₀ ⊓ U₁`): the diagonals `p = s = 0` (from `x = (0,0,0)` and `(1,1,1)`) and
  `r = −q` (from `x = (0,1,0)` / `(1,0,1)`), the remaining four being automatic.  Hence
  `ker d¹ = { (0, q, −q, 0) : q ∈ Γ(U₀₁) } ≅ Γ(U₀₁)` via `q`.

Therefore `H¹ = ker d¹ / im d⁰ ≅ Γ(U₀ ⊓ U₁) / range (S.sectionDiff F) = H1Cok S F`, the
iso being `[(0, q, −q, 0)] ↦ [q]`.  The identification is **unconditional** (no
acyclicity hypothesis — it is a pure homological-algebra fact about this specific
2-cover complex), and it is carried out in full in this file:

* `sectionRestrict_trans`/`sectionRestrict_self`/`restrict_map_comp`/
  `restrict_map_self`/`isIso_restrict_map` — the poset restriction calculus every
  cancellation step reduces to;
* `cechD01`/`cechD12` with `cechD01_π`/`cechD12_π` — the low-degree differentials in
  product-typed, componentwise form;
* `overlapCocycle` with `overlapCocycle_comp_d` — the cocycle `q ↦ (0, q, −q, 0)`
  and the 8-index cancellation;
* `ker_cechD12_π_diag_zero₀`/`₁`, `ker_cechD12_π_off_diag`, `overlapKerEquiv` — the
  kernel description `ker d¹ = {(0, q, −q, 0)} ≃ₗ Γ(U₀ ⊓ U₁)`;
* `pairLift`/`pairProj`/`pairLift_comp_cechD01`/`map_range_pairDiff` — the image
  identification `im d⁰ = κ(im sectionDiff)`;
* `cechCohomologyOneEquivH1Cok` — node N5 proper, assembled through
  `isoSc' 0 1 2` and `ShortComplex.moduleCatHomologyIso`;
* `hModuleOneEquivH1Cok` — the N5+N6 consumable
  `HModule k F 1 ≃ₗ[k] H1Cok S F` under the `HasCechToHModuleIso` gate.
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-! ## Node N6 — the `k`-linear bridge `HModule k F 1 ≃ₗ[k] cechCohomology C F 𝒰 1` -/

/-- **Node N6 (bridge), abstract sheaf form.** For a sheaf `F` of `k`-modules on a
`Spec k`-scheme `C` and a cover `𝒰` with `⨆ 𝒰 = ⊤` satisfying the Čech-to-derived
comparison gate `HasCechToHModuleIso F 𝒰`, the genus-degree cohomology
`HModule k F n` is `k`-linearly identified with the Čech cohomology
`cechCohomology C F 𝒰 n` of the cover.

The equivalence chains the iter-050 comparison
`cechToHModuleIso n : cechCohomology C F 𝒰 n ≃ₗ[k] HModule' k F n (⨆ 𝒰)` with the
iter-034 universe bridge `HModule'_eq_HModule_linearEquiv` at the terminal open
`⊤ = ⨆ 𝒰` (using `Preorder.isTerminalTop` transported along `h`, exactly the
iter-035 `HModule'_X₄_linearEquiv` pattern), then symmetrises.

This is stated *conditional* on the `HasCechToHModuleIso` gate — no new `sorry` or
gate is introduced.  Downstream (`N5`, the finiteness keystone `N11`/`N12`) the
useful degree is `n = 1`: it reduces `H¹(C, 𝒪_C)` to the concrete Čech `H¹`. -/
noncomputable def hModuleOne_linearEquiv_cechCohomology
    {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasCechToHModuleIso F 𝒰]
    (h : ⨆ i, 𝒰 i = ⊤) (n : ℕ) :
    HModule k F n ≃ₗ[k] cechCohomology C F 𝒰 n :=
  ((cechToHModuleIso n).trans
    (HModule'_eq_HModule_linearEquiv k F n
      (h.symm ▸ Preorder.isTerminalTop (TopologicalSpace.Opens C.left.toTopCat)))).symm

/-- **Node N6 (bridge), curve specialisation.** Direct application of
`hModuleOne_linearEquiv_cechCohomology` to the structure sheaf
`F := Scheme.toModuleKSheaf C`.  Mirrors the iter-039/…/iter-050 `_curve` pattern
(dot-notation resolution against the structure sheaf), giving
`HModule k (toModuleKSheaf C) n ≃ₗ[k] cechCohomology C (toModuleKSheaf C) 𝒰 n`. -/
noncomputable def hModuleOne_linearEquiv_cechCohomology_curve
    {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasCechToHModuleIso (Scheme.toModuleKSheaf C) 𝒰]
    (h : ⨆ i, 𝒰 i = ⊤) (n : ℕ) :
    HModule k (Scheme.toModuleKSheaf C) n
      ≃ₗ[k] cechCohomology C (Scheme.toModuleKSheaf C) 𝒰 n :=
  hModuleOne_linearEquiv_cechCohomology (Scheme.toModuleKSheaf C) 𝒰 h n

/-! ## Node N5 — the concrete 2-element cover family of an `AffineCoverMVSquare` -/

/-- **The 2-element open cover family `𝒰 : ULift (Fin 2) → Opens X` of an
`AffineCoverMVSquare`.** Indexed by `ULift.{u} (Fin 2)` (the `Type u` two-element
index that `Scheme.cechCohomology`/`hModuleOne_linearEquiv_cechCohomology` consume),
it sends the first index to `U₁` and the second to `U₂`.  This is the family whose
Čech cohomology `cechCohomology C F S.coverFamily 1` is identified with the concrete
cokernel `H1Cok S F` (node N5 proper) and fed into the N6 bridge. -/
noncomputable def AffineCoverMVSquare.coverFamily {X : Scheme.{u}} (S : X.AffineCoverMVSquare) :
    ULift.{u} (Fin 2) → TopologicalSpace.Opens X.toTopCat :=
  fun i => if i.down = 0 then S.U₁ else S.U₂

@[simp] lemma AffineCoverMVSquare.coverFamily_zero {X : Scheme.{u}} (S : X.AffineCoverMVSquare) :
    S.coverFamily ⟨0⟩ = S.U₁ := rfl

@[simp] lemma AffineCoverMVSquare.coverFamily_one {X : Scheme.{u}} (S : X.AffineCoverMVSquare) :
    S.coverFamily ⟨1⟩ = S.U₂ := rfl

/-- **Cover totality of `coverFamily`.** The 2-element family covers `X`:
`⨆ i, S.coverFamily i = ⊤`.  This is the `ι → Opens`-family incarnation of the
`AffineCoverMVSquare.cover` field `U₁ ⊔ U₂ = ⊤`, and is the hypothesis
`hModuleOne_linearEquiv_cechCohomology` requires to land the N6 bridge on the whole
curve. -/
lemma AffineCoverMVSquare.iSup_coverFamily {X : Scheme.{u}} (S : X.AffineCoverMVSquare) :
    ⨆ i, S.coverFamily i = ⊤ := by
  refine le_antisymm le_top ?_
  have h : S.U₁ ⊔ S.U₂ ≤ ⨆ i, S.coverFamily i :=
    sup_le (le_iSup_of_le ⟨0⟩ (le_of_eq S.coverFamily_zero.symm))
      (le_iSup_of_le ⟨1⟩ (le_of_eq S.coverFamily_one.symm))
  exact S.cover ▸ h

/-- **Node N6 bridge on the concrete 2-cover family.** The specialisation of
`hModuleOne_linearEquiv_cechCohomology` to `S.coverFamily`, discharging the totality
hypothesis with `iSup_coverFamily`: for a sheaf `F` of `k`-modules on the curve `C`
satisfying the Čech-to-derived comparison gate on the 2-affine cover, the
genus-degree cohomology `HModule k F n` is `k`-linearly identified with the Čech
cohomology `cechCohomology C F S.coverFamily n` of the concrete 2-element cover.
Chaining node N5's `cechCohomology C F S.coverFamily 1 ≃ₗ[k] H1Cok S F` into this (at
`n = 1`) delivers the lane's consumable `HModule k F 1 ≃ₗ[k] H1Cok S F`. -/
noncomputable def AffineCoverMVSquare.hModuleOne_linearEquiv_cechCohomology_coverFamily
    {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
    (S : C.left.AffineCoverMVSquare)
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasCechToHModuleIso F S.coverFamily]
    (n : ℕ) :
    HModule k F n ≃ₗ[k] cechCohomology C F S.coverFamily n :=
  hModuleOne_linearEquiv_cechCohomology F S.coverFamily S.iSup_coverFamily n

/-! ## Node N5 target — the concrete section-level difference map and cokernel -/

section ConcreteCokernel

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (F : Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k))

/-- The restriction `k`-linear map `Γ(V, F) →ₗ[k] Γ(U, F)` for an inclusion of opens
`U ≤ V`, extracted from the underlying presheaf of the sheaf of `k`-modules `F`. -/
noncomputable def sectionRestrict {U V : TopologicalSpace.Opens X.toTopCat} (h : U ≤ V) :
    F.obj.obj (Opposite.op V) →ₗ[k] F.obj.obj (Opposite.op U) :=
  (F.obj.map (homOfLE h).op).hom

/-- **Node N5 target — the difference-of-restrictions map** of a 2-affine cover.
For `S : X.AffineCoverMVSquare`, this is the `k`-linear map
`Γ(U₁, F) × Γ(U₂, F) →ₗ[k] Γ(U₁ ⊓ U₂, F)` sending `(a, b)` to `a|_{U₁∩U₂} − b|_{U₁∩U₂}`.
Its image is the "coboundary" subspace `Γ(U₁) + Γ(U₂)` inside `Γ(U₁ ⊓ U₂)`. -/
noncomputable def AffineCoverMVSquare.sectionDiff (S : X.AffineCoverMVSquare) :
    (F.obj.obj (Opposite.op S.U₁) × F.obj.obj (Opposite.op S.U₂)) →ₗ[k]
      F.obj.obj (Opposite.op (S.U₁ ⊓ S.U₂)) :=
  (sectionRestrict F (inf_le_left)).comp (LinearMap.fst k _ _)
    - (sectionRestrict F (inf_le_right)).comp (LinearMap.snd k _ _)

/-- **The concrete Čech `Ȟ¹` of a 2-affine cover** as the cokernel of the
difference-of-restrictions map:
`Ȟ¹ = Γ(U₁ ⊓ U₂, F) ⧸ (Γ(U₁, F) + Γ(U₂, F))`.
For `F` an arbitrary sheaf of `k`-modules this is the divisor-twisted `Ȟ¹(D)`;
specialising `F := 𝒪_C(D)` recovers Weil's `A_K/(A_K(D)+K)`. -/
noncomputable def AffineCoverMVSquare.H1Cok (S : X.AffineCoverMVSquare) : Type u :=
  F.obj.obj (Opposite.op (S.U₁ ⊓ S.U₂)) ⧸ LinearMap.range (S.sectionDiff F)

noncomputable instance AffineCoverMVSquare.instAddCommGroupH1Cok
    (S : X.AffineCoverMVSquare) : AddCommGroup (S.H1Cok F) :=
  inferInstanceAs (AddCommGroup (_ ⧸ LinearMap.range (S.sectionDiff F)))

noncomputable instance AffineCoverMVSquare.instModuleH1Cok
    (S : X.AffineCoverMVSquare) : Module k (S.H1Cok F) :=
  inferInstanceAs (Module k (_ ⧸ LinearMap.range (S.sectionDiff F)))

/-- **The `H⁰ = L(D)` gluing space** as the kernel of the difference-of-restrictions
map: a pair `(a, b)` lies in the kernel iff `a` and `b` agree on the overlap
`U₁ ⊓ U₂`, i.e. glue to a single global section (`= { f ∈ K : div f + D ≥ 0 }` in the
twisted case).  This is the `Submodule` incarnation of `L(D)`. -/
noncomputable def AffineCoverMVSquare.sectionGlue (S : X.AffineCoverMVSquare) :
    Submodule k (F.obj.obj (Opposite.op S.U₁) × F.obj.obj (Opposite.op S.U₂)) :=
  LinearMap.ker (S.sectionDiff F)

/-- **The gluing/`L(D)` condition is agreement on the overlap.** A pair of sections
`(a, b) ∈ Γ(U₁, F) × Γ(U₂, F)` lies in the `H⁰`-gluing space `sectionGlue` exactly
when the two restrictions to `U₁ ⊓ U₂` coincide.  In the twisted case `F = 𝒪_C(D)`
this is `L(D) = { f ∈ K : div f + D ≥ 0 }`. -/
lemma AffineCoverMVSquare.mem_sectionGlue (S : X.AffineCoverMVSquare)
    (p : F.obj.obj (Opposite.op S.U₁) × F.obj.obj (Opposite.op S.U₂)) :
    p ∈ S.sectionGlue F ↔
      sectionRestrict F (inf_le_left) p.1 = sectionRestrict F (inf_le_right) p.2 := by
  rw [sectionGlue, LinearMap.mem_ker, AffineCoverMVSquare.sectionDiff,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, sub_eq_zero]

end ConcreteCokernel

/-! ## Node N5 — concrete component formulas for the unnormalized Čech differential

The in-tree `cechCohomology C F 𝒰 n = (cechCochain C F 𝒰).homology n` is the homology of
Mathlib's unnormalized `cechComplexFunctor`, routed through
`FormalCoproduct.cochainComplexFunctor = cosimplicialObjectFunctor ⋙ alternatingCofaceMapComplex`.
There is no cosimplicial dual of `alternatingFaceMapComplex_obj_d` in Mathlib, so the concrete
`Pi.π`-component formulas for the differential are derived here directly by unfolding the
alternating coface sum.  These are the reusable foundation the degree-`1` identification
(`cechCohomology C F S.coverFamily 1 ≃ₗ[k] H1Cok S F`) is built on:

* `cechCosimplicial_δ_π` — the single-coface component
  `Yδᵢ ≫ πⱼ = π_{j∘δᵢ} ≫ (reindex restriction)`;
* `prodOpens_eq_iInf` — the abstract Čech product object `∏ᶜ (𝒰∘j)` is the concrete infimum
  `⨅ₐ 𝒰(j a)` of opens (equality in the poset `Opens X`), the bridge to `Γ(⨅ₐ Uₐ)`;
* `alternatingCofaceMapComplex_objD` — the differential is the alternating coface sum (the
  missing Mathlib dual);
* `cechCochain_d01_π` / `cechCochain_d12_π` — the degree-`0`/degree-`1` differentials,
  componentwise.
-/

section CechDifferential

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
  {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat)
  (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))

/-- **The alternating coface differential (Mathlib dual, project-local).** The degree-`n`
differential of `alternatingCofaceMapComplex` is the alternating sum of coface maps
`objD Y n = ∑ᵢ (-1)ⁱ • Yδᵢ`.  Mathlib has `alternatingFaceMapComplex_obj_d` but no cosimplicial
dual; this recreates it (the same one-line `CochainComplex.of` unfolding). -/
theorem alternatingCofaceMapComplex_objD {D : Type*} [Category D] [Preadditive D]
    (Y : CosimplicialObject D) (n : ℕ) :
    ((alternatingCofaceMapComplex D).obj Y).d n (n + 1)
      = AlternatingCofaceMapComplex.objD Y n := by
  simp only [alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj, CochainComplex.of_d]

/-- The cosimplicial object underlying the Čech complex `cechCochain C F 𝒰`: it sends `⦋n⦌` to
`∏_{i : Fin (n+1) → ι} Γ(⨅ₐ 𝒰(i a), F)`.  `cechCochain C F 𝒰` is by definition
`alternatingCofaceMapComplex.obj (cechCosimplicial 𝒰 F)`. -/
noncomputable def cechCosimplicial : CosimplicialObject (ModuleCat.{u} k) :=
  (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ 𝒰).cech).obj
    ((sheafToPresheaf _ _).obj F)

lemma cechCochain_eq :
    AlgebraicGeometry.Scheme.cechCochain C F 𝒰
      = (alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (cechCosimplicial 𝒰 F) :=
  rfl

/-- **Single-coface component of the Čech cosimplicial object.** The `i₀`-th coface map
`Yδ_{i₀} : Č^n ⟶ Č^{n+1}`, projected to the factor indexed by `j : Fin (n+2) → ι`, is the factor
`j ∘ δ_{i₀}` of the source followed by the reindexing restriction
`Γ(⨅ₐ 𝒰(j(δ_{i₀} a))) ⟶ Γ(⨅ₐ 𝒰(j a))`.  Derived by unfolding
`cosimplicialObjectFunctor` (`evalOp` of the Čech nerve) and `Pi.lift ≫ Pi.π`. -/
theorem cechCosimplicial_δ_π (n : ℕ) (i₀ : Fin (n + 2)) (j : Fin (n + 2) → ι) :
    (cechCosimplicial 𝒰 F).δ i₀ ≫ Pi.π _ j
      = Pi.π _ (j ∘ (Fin.succAboveOrderEmb i₀)) ≫
          ((sheafToPresheaf _ _).obj F).map
            (Pi.lift (fun a => Pi.π ((FormalCoproduct.mk _ 𝒰).obj ∘ j)
              ((Fin.succAboveOrderEmb i₀) a))).op := by
  simp only [cechCosimplicial, CosimplicialObject.δ,
    FormalCoproduct.cosimplicialObjectFunctor_obj_map]
  erw [Limits.Pi.lift_π]
  rfl

/-- **The abstract Čech product is the concrete infimum of opens.** In the poset `Opens X` the
categorical product `∏ᶜ (𝒰∘j)` of the family `a ↦ 𝒰 (j a)` equals its infimum `⨅ₐ 𝒰 (j a)`.
This is the bridge identifying the Čech section groups `Γ(∏ᶜ 𝒰∘j, F)` with the concrete
`Γ(⨅ₐ 𝒰(j a), F)` (and, for the 2-cover, with `Γ(U₁ ⊓ U₂)`). -/
theorem prodOpens_eq_iInf {m : ℕ} (j : Fin m → ι) :
    (∏ᶜ ((FormalCoproduct.mk _ 𝒰).obj ∘ j) : TopologicalSpace.Opens C.left.toTopCat)
      = ⨅ a, 𝒰 (j a) :=
  le_antisymm (le_iInf fun a => (Limits.Pi.π ((FormalCoproduct.mk _ 𝒰).obj ∘ j) a).le)
    (Limits.Pi.lift (fun a => homOfLE (iInf_le (fun a => 𝒰 (j a)) a))).le

/-- The Čech face inclusion: the full intersection `∏ᶜ (𝒰∘j) = ⨅_{Fin (n+2)} 𝒰(j b)` is contained
in the face intersection `∏ᶜ (𝒰∘(j∘δ_{i₀})) = ⨅_{Fin (n+1)} 𝒰(j(δ_{i₀} a))` (dropping one index),
the `≤` of opens underlying the restriction that the coface map applies. -/
theorem prodOpens_δ_le {n : ℕ} (i₀ : Fin (n + 2)) (j : Fin (n + 2) → ι) :
    (∏ᶜ ((FormalCoproduct.mk _ 𝒰).obj ∘ j) : TopologicalSpace.Opens C.left.toTopCat)
      ≤ ∏ᶜ ((FormalCoproduct.mk _ 𝒰).obj ∘ (j ∘ Fin.succAboveOrderEmb i₀)) := by
  rw [prodOpens_eq_iInf, prodOpens_eq_iInf]
  exact le_iInf fun a => iInf_le (fun b => 𝒰 (j b)) (Fin.succAboveOrderEmb i₀ a)

/-- **Single-coface component of the Čech differential, as a genuine restriction map.** Because
`Opens X` is a poset (all parallel maps are equal), the abstract reindexing morphism of
`cechCosimplicial_δ_π` is *the* restriction `F.obj.map (homOfLE …)ᵒᵖ` of the face inclusion
`prodOpens_δ_le`.  This is the differential `Yδ_{i₀}`, projected to `j`, in the honest
"restrict the `(j∘δ_{i₀})`-factor along `∏ᶜ 𝒰∘j ≤ ∏ᶜ 𝒰∘(j∘δ_{i₀})`" form used by the
degree-`1` kernel/cokernel analysis. -/
theorem cechCosimplicial_δ_π_restrict (n : ℕ) (i₀ : Fin (n + 2)) (j : Fin (n + 2) → ι) :
    (cechCosimplicial 𝒰 F).δ i₀ ≫ Pi.π _ j
      = Pi.π _ (j ∘ Fin.succAboveOrderEmb i₀) ≫
          F.obj.map (homOfLE (prodOpens_δ_le 𝒰 i₀ j)).op := by
  rw [cechCosimplicial_δ_π]
  refine congrArg _ (congrArg _ ?_)
  exact congrArg Opposite.op (Subsingleton.elim _ _)

/-- **Degree-`0` differential `d⁰` of the Čech complex as an alternating coface difference.**
`d⁰ = Yδ₀ − Yδ₁` (the two cofaces `Fin 1 → Fin 2` of the alternating sum). -/
theorem cechCochain_d01_eq :
    (AlgebraicGeometry.Scheme.cechCochain C F 𝒰).d 0 1
      = (cechCosimplicial 𝒰 F).δ 0 - (cechCosimplicial 𝒰 F).δ 1 := by
  have h : (AlgebraicGeometry.Scheme.cechCochain C F 𝒰).d 0 1
      = AlternatingCofaceMapComplex.objD (cechCosimplicial 𝒰 F) 0 :=
    alternatingCofaceMapComplex_objD (cechCosimplicial 𝒰 F) 0
  rw [h, AlternatingCofaceMapComplex.objD, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul]
  abel

/-- **Degree-`1` differential `d¹` of the Čech complex as an alternating coface sum.**
`d¹ = Yδ₀ − Yδ₁ + Yδ₂` (the three cofaces `Fin 2 → Fin 3` of the alternating sum). -/
theorem cechCochain_d12_eq :
    (AlgebraicGeometry.Scheme.cechCochain C F 𝒰).d 1 2
      = (cechCosimplicial 𝒰 F).δ 0 - (cechCosimplicial 𝒰 F).δ 1 + (cechCosimplicial 𝒰 F).δ 2 := by
  have h : (AlgebraicGeometry.Scheme.cechCochain C F 𝒰).d 1 2
      = AlternatingCofaceMapComplex.objD (cechCosimplicial 𝒰 F) 1 :=
    alternatingCofaceMapComplex_objD (cechCosimplicial 𝒰 F) 1
  rw [h, AlternatingCofaceMapComplex.objD, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
    Even.neg_pow, even_two]
  abel

end CechDifferential

/-! ## Node N5 — restriction-map calculus

Every map in the degree-`1` identification is a section restriction
`sectionRestrict F h = (F.obj.map (homOfLE h).op).hom` along an inequality of opens.
Because `Opens X` is a poset, parallel restrictions agree, restrictions compose to
restrictions, and a restriction between mutually included (i.e. equal) opens is an
isomorphism.  These four lemmas are the entire calculus the kernel/cokernel analysis
needs: all "cancellation", "round-trip" and "bridge-consistency" steps below reduce
to them plus proof irrelevance of the `≤`-witnesses. -/

section SectionRestrictCalculus

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (F : Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k))

/-- Composition of section restrictions along `U ≤ V ≤ W` is the restriction along
the composite inequality. -/
lemma sectionRestrict_trans {U V W : TopologicalSpace.Opens X.toTopCat}
    (h₁ : U ≤ V) (h₂ : V ≤ W) (x : F.obj.obj (Opposite.op W)) :
    sectionRestrict F h₁ (sectionRestrict F h₂ x) = sectionRestrict F (h₁.trans h₂) x := by
  have h : F.obj.map (homOfLE (h₁.trans h₂)).op
      = F.obj.map (homOfLE h₂).op ≫ F.obj.map (homOfLE h₁).op := by
    rw [← F.obj.map_comp]
    exact congrArg F.obj.map (Subsingleton.elim _ _)
  simp only [sectionRestrict, h, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- Restriction along `U ≤ U` is the identity. -/
lemma sectionRestrict_self {U : TopologicalSpace.Opens X.toTopCat} (h : U ≤ U)
    (x : F.obj.obj (Opposite.op U)) :
    sectionRestrict F h x = x := by
  have h' : (homOfLE h).op = 𝟙 (Opposite.op U) := Subsingleton.elim _ _
  rw [sectionRestrict, h', F.obj.map_id]
  rfl

/-- A restriction map between mutually included (hence equal) opens is injective. -/
lemma sectionRestrict_injective {U V : TopologicalSpace.Opens X.toTopCat}
    (h : U ≤ V) (h' : V ≤ U) :
    Function.Injective (sectionRestrict F h) := fun a b hab => by
  have h2 := congrArg (sectionRestrict F h') hab
  rwa [sectionRestrict_trans, sectionRestrict_trans, sectionRestrict_self, sectionRestrict_self]
    at h2

/-- Morphism-level composition of the restriction maps of `F` along `U ≤ V ≤ W`. -/
lemma restrict_map_comp {U V W : TopologicalSpace.Opens X.toTopCat} (h₁ : U ≤ V) (h₂ : V ≤ W) :
    F.obj.map (homOfLE h₂).op ≫ F.obj.map (homOfLE h₁).op
      = F.obj.map (homOfLE (h₁.trans h₂)).op := by
  rw [← F.obj.map_comp]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

/-- The restriction map of `F` along mutually included (hence equal) opens is an
isomorphism (it is `F.obj.map` of an identity up to `Subsingleton.elim`). -/
lemma isIso_restrict_map {U V : TopologicalSpace.Opens X.toTopCat} (h : U ≤ V) (h' : V ≤ U) :
    IsIso (F.obj.map (homOfLE h).op) := by
  have heq : U = V := le_antisymm h h'
  subst heq
  have h0 : (homOfLE h).op = 𝟙 (Opposite.op U) := Subsingleton.elim _ _
  rw [h0, F.obj.map_id]
  infer_instance

/-- The restriction map of `F` along `U ≤ U` is the identity. -/
lemma restrict_map_self {U : TopologicalSpace.Opens X.toTopCat} (h : U ≤ U) :
    F.obj.map (homOfLE h).op = 𝟙 _ := by
  have h0 : (homOfLE h).op = 𝟙 (Opposite.op U) := Subsingleton.elim _ _
  rw [h0, F.obj.map_id]

/-- Repackaging the linear section restriction as the `ModuleCat` morphism it came
from. -/
lemma ofHom_sectionRestrict {U V : TopologicalSpace.Opens X.toTopCat} (h : U ≤ V) :
    ModuleCat.ofHom (sectionRestrict F h) = F.obj.map (homOfLE h).op :=
  rfl

end SectionRestrictCalculus

/-! ## Node N5 — the small-index Čech products as concrete infima -/

section SmallProdOpens

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
  {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat)

/-- The Čech product over a 1-element multi-index is the single open. -/
theorem prodOpens_fin_one (j : Fin 1 → ι) :
    (∏ᶜ ((FormalCoproduct.mk _ 𝒰).obj ∘ j) : TopologicalSpace.Opens C.left.toTopCat)
      = 𝒰 (j 0) := by
  rw [prodOpens_eq_iInf]
  refine le_antisymm (iInf_le _ 0) (le_iInf fun a => ?_)
  fin_cases a
  exact le_rfl

/-- The Čech product over a 2-element multi-index is the binary intersection. -/
theorem prodOpens_fin_two (j : Fin 2 → ι) :
    (∏ᶜ ((FormalCoproduct.mk _ 𝒰).obj ∘ j) : TopologicalSpace.Opens C.left.toTopCat)
      = 𝒰 (j 0) ⊓ 𝒰 (j 1) := by
  rw [prodOpens_eq_iInf]
  refine le_antisymm (le_inf (iInf_le _ 0) (iInf_le _ 1)) (le_iInf fun a => ?_)
  fin_cases a
  · exact inf_le_left
  · exact inf_le_right

/-- If every open of the multi-index `j` occurs among the opens of the multi-index `x`,
the Čech product of `x` is contained in the Čech product of `j`.  For concrete
multi-indices the hypothesis is decidable, so this yields all the inclusion witnesses
of the 8-index kernel analysis by `decide`. -/
theorem prodOpens_le_of_forall_exists {m m' : ℕ} {j : Fin m → ι} {x : Fin m' → ι}
    (h : ∀ a, ∃ b, x b = j a) :
    (∏ᶜ ((FormalCoproduct.mk _ 𝒰).obj ∘ x) : TopologicalSpace.Opens C.left.toTopCat)
      ≤ ∏ᶜ ((FormalCoproduct.mk _ 𝒰).obj ∘ j) := by
  rw [prodOpens_eq_iInf, prodOpens_eq_iInf]
  refine le_iInf fun a => ?_
  obtain ⟨b, hb⟩ := h a
  exact (iInf_le _ b).trans (le_of_eq (congrArg 𝒰 hb))

end SmallProdOpens

/-! ## Node N5 — componentwise form of the low-degree Čech differentials -/

section CechComponentFormulas

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
  {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat)
  (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))

/-- The factor of the degree-`(m-1)` Čech term indexed by the multi-index `j : Fin m → ι`:
the sections of `F` on the `m`-fold intersection `∏ᶜ (𝒰 ∘ j) = ⨅ₐ 𝒰 (j a)`.  The degree-`n`
Čech term `(cechCochain C F 𝒰).X n` is definitionally `∏ᶜ (cechTerm 𝒰 F (n + 1))`. -/
noncomputable abbrev cechTerm (m : ℕ) (j : Fin m → ι) : ModuleCat.{u} k :=
  F.obj.obj (Opposite.op (∏ᶜ ((FormalCoproduct.mk _ 𝒰).obj ∘ j)))

/-- Projections composed with restrictions only depend on the multi-index up to
propositional equality: the `sectionRestrict`-style wrapper reconciles the dependent
types on both sides, and the `≤`-witnesses are proof-irrelevant.  This is the transport
lemma that replaces the coface indices `x ∘ δᵢ` by their concrete `![…]` values in the
8-index kernel analysis. -/
lemma pi_π_restrict_congr {m m' : ℕ} {j j' : Fin m → ι} (h : j = j') {x : Fin m' → ι}
    (hW : (∏ᶜ ((FormalCoproduct.mk _ 𝒰).obj ∘ x) : TopologicalSpace.Opens C.left.toTopCat)
      ≤ ∏ᶜ ((FormalCoproduct.mk _ 𝒰).obj ∘ j))
    (hW' : (∏ᶜ ((FormalCoproduct.mk _ 𝒰).obj ∘ x) : TopologicalSpace.Opens C.left.toTopCat)
      ≤ ∏ᶜ ((FormalCoproduct.mk _ 𝒰).obj ∘ j')) :
    Pi.π (cechTerm 𝒰 F m) j ≫ F.obj.map (homOfLE hW).op
      = Pi.π (cechTerm 𝒰 F m) j' ≫ F.obj.map (homOfLE hW').op := by
  subst h
  rfl

/-- The degree-`0` Čech differential of the cover, typed against the concrete products
`∏ᶜ cechTerm` (definitionally `(cechCochain C F 𝒰).d 0 1`; the retyping keeps every
term of the kernel/cokernel analysis type-correct at `instances` transparency). -/
noncomputable def cechD01 : (∏ᶜ (cechTerm 𝒰 F 1) : ModuleCat.{u} k) ⟶ ∏ᶜ (cechTerm 𝒰 F 2) :=
  (Scheme.cechCochain C F 𝒰).d 0 1

/-- The degree-`1` Čech differential of the cover, typed against the concrete products
`∏ᶜ cechTerm` (definitionally `(cechCochain C F 𝒰).d 1 2`). -/
noncomputable def cechD12 : (∏ᶜ (cechTerm 𝒰 F 2) : ModuleCat.{u} k) ⟶ ∏ᶜ (cechTerm 𝒰 F 3) :=
  (Scheme.cechCochain C F 𝒰).d 1 2

/-- **Componentwise degree-`0` Čech differential.**  The `j`-component of `d⁰` is the
difference of the two coface restrictions. -/
lemma cechCochain_d01_π (j : Fin 2 → ι) :
    (Scheme.cechCochain C F 𝒰).d 0 1 ≫ Pi.π (cechTerm 𝒰 F 2) j
      = Pi.π (cechTerm 𝒰 F 1) (j ∘ Fin.succAboveOrderEmb 0)
          ≫ F.obj.map (homOfLE (prodOpens_δ_le 𝒰 0 j)).op
        - Pi.π (cechTerm 𝒰 F 1) (j ∘ Fin.succAboveOrderEmb 1)
          ≫ F.obj.map (homOfLE (prodOpens_δ_le 𝒰 1 j)).op := by
  have h0 := cechCosimplicial_δ_π_restrict 𝒰 F 0 0 j
  have h1 := cechCosimplicial_δ_π_restrict 𝒰 F 0 1 j
  have hd : (Scheme.cechCochain C F 𝒰).d 0 1 ≫ Pi.π (cechTerm 𝒰 F 2) j
      = ((cechCosimplicial 𝒰 F).δ 0 - (cechCosimplicial 𝒰 F).δ 1)
          ≫ Pi.π (cechTerm 𝒰 F 2) j :=
    congrArg (· ≫ Pi.π (cechTerm 𝒰 F 2) j) (cechCochain_d01_eq 𝒰 F)
  exact hd.trans ((Preadditive.sub_comp _ _ _).trans (congrArg₂ (· - ·) h0 h1))

/-- **Componentwise degree-`1` Čech differential.**  The `x`-component of `d¹` is the
alternating sum of the three coface restrictions. -/
lemma cechCochain_d12_π (x : Fin 3 → ι) :
    (Scheme.cechCochain C F 𝒰).d 1 2 ≫ Pi.π (cechTerm 𝒰 F 3) x
      = Pi.π (cechTerm 𝒰 F 2) (x ∘ Fin.succAboveOrderEmb 0)
          ≫ F.obj.map (homOfLE (prodOpens_δ_le 𝒰 0 x)).op
        - Pi.π (cechTerm 𝒰 F 2) (x ∘ Fin.succAboveOrderEmb 1)
          ≫ F.obj.map (homOfLE (prodOpens_δ_le 𝒰 1 x)).op
        + Pi.π (cechTerm 𝒰 F 2) (x ∘ Fin.succAboveOrderEmb 2)
          ≫ F.obj.map (homOfLE (prodOpens_δ_le 𝒰 2 x)).op := by
  have h0 := cechCosimplicial_δ_π_restrict 𝒰 F 1 0 x
  have h1 := cechCosimplicial_δ_π_restrict 𝒰 F 1 1 x
  have h2 := cechCosimplicial_δ_π_restrict 𝒰 F 1 2 x
  have hd : (Scheme.cechCochain C F 𝒰).d 1 2 ≫ Pi.π (cechTerm 𝒰 F 3) x
      = ((cechCosimplicial 𝒰 F).δ 0 - (cechCosimplicial 𝒰 F).δ 1 + (cechCosimplicial 𝒰 F).δ 2)
          ≫ Pi.π (cechTerm 𝒰 F 3) x :=
    congrArg (· ≫ Pi.π (cechTerm 𝒰 F 3) x) (cechCochain_d12_eq 𝒰 F)
  exact hd.trans ((Preadditive.add_comp _ _ _ _ _ _).trans
    (congrArg₂ (· + ·) ((Preadditive.sub_comp _ _ _).trans (congrArg₂ (· - ·) h0 h1)) h2))

/-- `cechCochain_d01_π`, restated for the product-typed differential `cechD01`. -/
lemma cechD01_π (j : Fin 2 → ι) :
    cechD01 𝒰 F ≫ Pi.π (cechTerm 𝒰 F 2) j
      = Pi.π (cechTerm 𝒰 F 1) (j ∘ Fin.succAboveOrderEmb 0)
          ≫ F.obj.map (homOfLE (prodOpens_δ_le 𝒰 0 j)).op
        - Pi.π (cechTerm 𝒰 F 1) (j ∘ Fin.succAboveOrderEmb 1)
          ≫ F.obj.map (homOfLE (prodOpens_δ_le 𝒰 1 j)).op :=
  cechCochain_d01_π 𝒰 F j

/-- `cechCochain_d12_π`, restated for the product-typed differential `cechD12`. -/
lemma cechD12_π (x : Fin 3 → ι) :
    cechD12 𝒰 F ≫ Pi.π (cechTerm 𝒰 F 3) x
      = Pi.π (cechTerm 𝒰 F 2) (x ∘ Fin.succAboveOrderEmb 0)
          ≫ F.obj.map (homOfLE (prodOpens_δ_le 𝒰 0 x)).op
        - Pi.π (cechTerm 𝒰 F 2) (x ∘ Fin.succAboveOrderEmb 1)
          ≫ F.obj.map (homOfLE (prodOpens_δ_le 𝒰 1 x)).op
        + Pi.π (cechTerm 𝒰 F 2) (x ∘ Fin.succAboveOrderEmb 2)
          ≫ F.obj.map (homOfLE (prodOpens_δ_le 𝒰 2 x)).op :=
  cechCochain_d12_π 𝒰 F x

/-- `d⁰ ≫ d¹ = 0`, in the product-typed form. -/
lemma cechD01_comp_cechD12 : cechD01 𝒰 F ≫ cechD12 𝒰 F = 0 :=
  (Scheme.cechCochain C F 𝒰).d_comp_d 0 1 2

/-- `d⁰`, corestricted to the degree-`1` cocycles: the concrete `toCycles` map of the
short complex `(d⁰, d¹)` whose homology is the degree-`1` Čech cohomology. -/
noncomputable def cechToCyclesD01 :
    (∏ᶜ (cechTerm 𝒰 F 1) : ModuleCat.{u} k) →ₗ[k] LinearMap.ker (cechD12 𝒰 F).hom :=
  (cechD01 𝒰 F).hom.codRestrict (LinearMap.ker (cechD12 𝒰 F).hom) fun m =>
    LinearMap.mem_ker.mpr (by
      have h := congrArg (fun t => t.hom m) (cechD01_comp_cechD12 𝒰 F)
      simpa using h)

end CechComponentFormulas

/-! ## Node N5 — the overlap 1-cocycle `q ↦ (0, q, −q, 0)` of the 2-cover -/

section OverlapCocycle

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
  (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
  (S : C.left.AffineCoverMVSquare)

/-- The overlap `U₁ ⊓ U₂` of the 2-cover, expressed through `coverFamily` — the
`TopologicalSpace.Opens X.toTopCat`-typed form (definitionally `S.U₁ ⊓ S.U₂`, but
uniformly typed so that all categorical rewriting below stays type-correct at
`instances` transparency; the `S.U₁ ⊓ S.U₂` form mixes in the `Scheme.Opens`
carrier of the `AffineCoverMVSquare` fields). -/
noncomputable abbrev AffineCoverMVSquare.overlapOpen {X : Scheme.{u}}
    (S : X.AffineCoverMVSquare) : TopologicalSpace.Opens X.toTopCat :=
  S.coverFamily ⟨0⟩ ⊓ S.coverFamily ⟨1⟩

/-- The Čech double intersection at the multi-index `(0,1)` is the overlap `U₁ ⊓ U₂`. -/
lemma AffineCoverMVSquare.prodOpens_zero_one :
    (∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨0⟩, ⟨1⟩])
        : TopologicalSpace.Opens C.left.toTopCat)
      = S.overlapOpen := by
  rw [prodOpens_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The Čech double intersection at the multi-index `(1,0)` is the overlap `U₁ ⊓ U₂`. -/
lemma AffineCoverMVSquare.prodOpens_one_zero :
    (∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨1⟩, ⟨0⟩])
        : TopologicalSpace.Opens C.left.toTopCat)
      = S.overlapOpen := by
  rw [prodOpens_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [inf_comm]

/-- **Components of the overlap 1-cocycle.**  For a section on the overlap, the
degree-`1` Čech cochain `(0, q, −q, 0)`: at the multi-index `(0,1)` the section
itself (transported by restriction along the equality `prodOpens_zero_one` of opens),
at `(1,0)` its negative, and `0` at the two diagonal indices. -/
noncomputable def AffineCoverMVSquare.overlapCocycleComponent
    (j : Fin 2 → ULift.{u} (Fin 2)) :
    F.obj.obj (op S.overlapOpen) ⟶ cechTerm S.coverFamily F 2 j :=
  if h : j = ![⟨0⟩, ⟨1⟩] then
    F.obj.map (homOfLE (le_of_eq (by rw [h]; exact S.prodOpens_zero_one))).op
  else if h' : j = ![⟨1⟩, ⟨0⟩] then
    -F.obj.map (homOfLE (le_of_eq (by rw [h']; exact S.prodOpens_one_zero))).op
  else 0

/-- **The overlap 1-cocycle** `q ↦ (0, q, −q, 0)`, as a morphism from the overlap
sections into the degree-`1` Čech term (in its concrete-product form) of the 2-cover. -/
noncomputable def AffineCoverMVSquare.overlapCocycle :
    F.obj.obj (op S.overlapOpen) ⟶ ∏ᶜ (cechTerm S.coverFamily F 2) :=
  Pi.lift (S.overlapCocycleComponent F)

@[reassoc]
lemma AffineCoverMVSquare.overlapCocycle_π (j : Fin 2 → ULift.{u} (Fin 2)) :
    S.overlapCocycle F ≫ Pi.π (cechTerm S.coverFamily F 2) j
      = S.overlapCocycleComponent F j :=
  Pi.lift_π _ _

/-- Composition of the `(0,1)`-branch of the overlap cocycle with a further
restriction: for `j = (0,1)` the component is the restriction along the composite
inequality.  Stated with the index `j` as a variable so that the coface indices
`x ∘ δᵢ` (which are only propositionally equal to `![⟨0⟩, ⟨1⟩]`) can be substituted. -/
lemma AffineCoverMVSquare.overlapCocycleComponent_comp_eq₀₁
    {j : Fin 2 → ULift.{u} (Fin 2)} (h : j = ![⟨0⟩, ⟨1⟩])
    {W : TopologicalSpace.Opens C.left.toTopCat}
    (hW : W ≤ ∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ j)) :
    S.overlapCocycleComponent F j ≫ F.obj.map (homOfLE hW).op
      = F.obj.map (homOfLE (hW.trans
          (le_of_eq (by rw [h]; exact S.prodOpens_zero_one)))).op := by
  subst h
  simp +decide only [overlapCocycleComponent, dite_true, dite_false, restrict_map_comp]

/-- Composition of the `(1,0)`-branch of the overlap cocycle with a further
restriction: for `j = (1,0)` the component is the negated restriction along the
composite inequality. -/
lemma AffineCoverMVSquare.overlapCocycleComponent_comp_eq₁₀
    {j : Fin 2 → ULift.{u} (Fin 2)} (h : j = ![⟨1⟩, ⟨0⟩])
    {W : TopologicalSpace.Opens C.left.toTopCat}
    (hW : W ≤ ∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ j)) :
    S.overlapCocycleComponent F j ≫ F.obj.map (homOfLE hW).op
      = -F.obj.map (homOfLE (hW.trans
          (le_of_eq (by rw [h]; exact S.prodOpens_one_zero)))).op := by
  subst h
  simp +decide only [overlapCocycleComponent, dite_true, dite_false, restrict_map_comp,
    Preadditive.neg_comp]

/-- The diagonal components of the overlap cocycle vanish, also after composing with
a further restriction. -/
lemma AffineCoverMVSquare.overlapCocycleComponent_comp_ne
    {j : Fin 2 → ULift.{u} (Fin 2)} (h1 : j ≠ ![⟨0⟩, ⟨1⟩]) (h2 : j ≠ ![⟨1⟩, ⟨0⟩])
    {W : TopologicalSpace.Opens C.left.toTopCat}
    (hW : W ≤ ∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ j)) :
    S.overlapCocycleComponent F j ≫ F.obj.map (homOfLE hW).op = 0 := by
  simp only [overlapCocycleComponent, dif_neg h1, dif_neg h2, zero_comp]

/-- **The overlap cochain is a 1-cocycle**: composing with the degree-`1` Čech
differential gives zero.  Componentwise this is the 8-index cancellation: on the six
"mixed" triple indices the two nonvanishing coface restrictions merge (parallel
restrictions on the opens poset agree) and cancel, and on the diagonal indices all
contributions vanish. -/
lemma AffineCoverMVSquare.overlapCocycle_comp_d :
    S.overlapCocycle F ≫ cechD12 S.coverFamily F = 0 := by
  refine Pi.hom_ext _ _ fun x => ?_
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c : Fin 2, x = ![⟨a⟩, ⟨b⟩, ⟨c⟩] :=
    ⟨(x 0).down, (x 1).down, (x 2).down, by funext i; fin_cases i <;> rfl⟩
  simp only [Category.assoc, cechD12_π, zero_comp, Preadditive.comp_add,
    Preadditive.comp_sub, overlapCocycle_π_assoc]
  fin_cases a <;> fin_cases b <;> fin_cases c
  · rw [S.overlapCocycleComponent_comp_ne F (by decide) (by decide),
      S.overlapCocycleComponent_comp_ne F (by decide) (by decide),
      S.overlapCocycleComponent_comp_ne F (by decide) (by decide)]
    abel
  · rw [S.overlapCocycleComponent_comp_eq₀₁ F (by funext i; fin_cases i <;> rfl),
      S.overlapCocycleComponent_comp_eq₀₁ F (by funext i; fin_cases i <;> rfl),
      S.overlapCocycleComponent_comp_ne F (by decide) (by decide)]
    abel
  · rw [S.overlapCocycleComponent_comp_eq₁₀ F (by funext i; fin_cases i <;> rfl),
      S.overlapCocycleComponent_comp_ne F (by decide) (by decide),
      S.overlapCocycleComponent_comp_eq₀₁ F (by funext i; fin_cases i <;> rfl)]
    abel
  · rw [S.overlapCocycleComponent_comp_ne F (by decide) (by decide),
      S.overlapCocycleComponent_comp_eq₀₁ F (by funext i; fin_cases i <;> rfl),
      S.overlapCocycleComponent_comp_eq₀₁ F (by funext i; fin_cases i <;> rfl)]
    abel
  · rw [S.overlapCocycleComponent_comp_ne F (by decide) (by decide),
      S.overlapCocycleComponent_comp_eq₁₀ F (by funext i; fin_cases i <;> rfl),
      S.overlapCocycleComponent_comp_eq₁₀ F (by funext i; fin_cases i <;> rfl)]
    abel
  · rw [S.overlapCocycleComponent_comp_eq₀₁ F (by funext i; fin_cases i <;> rfl),
      S.overlapCocycleComponent_comp_ne F (by decide) (by decide),
      S.overlapCocycleComponent_comp_eq₁₀ F (by funext i; fin_cases i <;> rfl)]
    abel
  · rw [S.overlapCocycleComponent_comp_eq₁₀ F (by funext i; fin_cases i <;> rfl),
      S.overlapCocycleComponent_comp_eq₁₀ F (by funext i; fin_cases i <;> rfl),
      S.overlapCocycleComponent_comp_ne F (by decide) (by decide)]
    abel
  · rw [S.overlapCocycleComponent_comp_ne F (by decide) (by decide),
      S.overlapCocycleComponent_comp_ne F (by decide) (by decide),
      S.overlapCocycleComponent_comp_ne F (by decide) (by decide)]
    abel

/-! ### The kernel identification `Γ(U₁ ⊓ U₂, F) ≃ₗ[k] ker d¹` (node N5, kernel half) -/

/-- The `(0,1)`-component of the overlap cocycle, uncomposed form. -/
lemma AffineCoverMVSquare.overlapCocycleComponent_zero_one :
    S.overlapCocycleComponent F ![⟨0⟩, ⟨1⟩]
      = F.obj.map (homOfLE (le_of_eq S.prodOpens_zero_one)).op := by
  unfold overlapCocycleComponent
  rw [dif_pos rfl]

/-- The `(1,0)`-component of the overlap cocycle, uncomposed form. -/
lemma AffineCoverMVSquare.overlapCocycleComponent_one_zero :
    S.overlapCocycleComponent F ![⟨1⟩, ⟨0⟩]
      = -F.obj.map (homOfLE (le_of_eq S.prodOpens_one_zero)).op := by
  unfold overlapCocycleComponent
  rw [dif_neg (by decide), dif_pos rfl]

/-- The diagonal components of the overlap cocycle vanish (uncomposed form). -/
lemma AffineCoverMVSquare.overlapCocycleComponent_eq_zero
    {j : Fin 2 → ULift.{u} (Fin 2)} (h1 : j ≠ ![⟨0⟩, ⟨1⟩]) (h2 : j ≠ ![⟨1⟩, ⟨0⟩]) :
    S.overlapCocycleComponent F j = 0 := by
  unfold overlapCocycleComponent
  rw [dif_neg h1, dif_neg h2]

/-- The kernel inclusion of `d¹` composes to zero with `d¹` (morphism form of the
cocycle condition for an arbitrary kernel element). -/
lemma AffineCoverMVSquare.kerSubtype_comp_cechD12 :
    ModuleCat.ofHom (LinearMap.ker (cechD12 S.coverFamily F).hom).subtype
      ≫ cechD12 S.coverFamily F = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun n => LinearMap.mem_ker.mp n.2)

/-- **Cocycles have vanishing `(0,0)`-component.**  The `x = (0,0,0)` component of the
cocycle condition reads `p| − p| + p| = p| = 0` on `U₁`, and the restriction
`Γ(𝒰₀ ⊓ 𝒰₀) → Γ(𝒰₀ ⊓ 𝒰₀ ⊓ 𝒰₀)` is an isomorphism. -/
lemma AffineCoverMVSquare.ker_cechD12_π_diag_zero₀ :
    ModuleCat.ofHom (LinearMap.ker (cechD12 S.coverFamily F).hom).subtype
      ≫ Pi.π (cechTerm S.coverFamily F 2) ![⟨0⟩, ⟨0⟩] = 0 := by
  have hcan : (∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨0⟩, ⟨0⟩, ⟨0⟩])
        : TopologicalSpace.Opens C.left.toTopCat)
      ≤ ∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨0⟩, ⟨0⟩]) :=
    prodOpens_le_of_forall_exists (j := ![⟨0⟩, ⟨0⟩]) (x := ![⟨0⟩, ⟨0⟩, ⟨0⟩])
      S.coverFamily (by decide)
  have hrev : (∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨0⟩, ⟨0⟩])
        : TopologicalSpace.Opens C.left.toTopCat)
      ≤ ∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨0⟩, ⟨0⟩, ⟨0⟩]) :=
    prodOpens_le_of_forall_exists (j := ![⟨0⟩, ⟨0⟩, ⟨0⟩]) (x := ![⟨0⟩, ⟨0⟩])
      S.coverFamily (by decide)
  have h := congrArg (· ≫ Pi.π (cechTerm S.coverFamily F 3) ![⟨0⟩, ⟨0⟩, ⟨0⟩])
    (S.kerSubtype_comp_cechD12 F)
  simp only [Category.assoc, cechD12_π, zero_comp, Preadditive.comp_add,
    Preadditive.comp_sub] at h
  rw [pi_π_restrict_congr S.coverFamily F
      (show (![⟨0⟩, ⟨0⟩, ⟨0⟩] ∘ ⇑(Fin.succAboveOrderEmb 0) : Fin 2 → ULift.{u} (Fin 2))
          = ![⟨0⟩, ⟨0⟩] from by funext i; fin_cases i <;> rfl) _ hcan,
    pi_π_restrict_congr S.coverFamily F
      (show (![⟨0⟩, ⟨0⟩, ⟨0⟩] ∘ ⇑(Fin.succAboveOrderEmb 1) : Fin 2 → ULift.{u} (Fin 2))
          = ![⟨0⟩, ⟨0⟩] from by funext i; fin_cases i <;> rfl) _ hcan,
    pi_π_restrict_congr S.coverFamily F
      (show (![⟨0⟩, ⟨0⟩, ⟨0⟩] ∘ ⇑(Fin.succAboveOrderEmb 2) : Fin 2 → ULift.{u} (Fin 2))
          = ![⟨0⟩, ⟨0⟩] from by funext i; fin_cases i <;> rfl) _ hcan,
    sub_self, zero_add, ← Category.assoc] at h
  haveI := isIso_restrict_map F hcan hrev
  rwa [← cancel_mono (F.obj.map (homOfLE hcan).op), zero_comp]

/-- **Cocycles have vanishing `(1,1)`-component** (the `x = (1,1,1)` component of the
cocycle condition). -/
lemma AffineCoverMVSquare.ker_cechD12_π_diag_zero₁ :
    ModuleCat.ofHom (LinearMap.ker (cechD12 S.coverFamily F).hom).subtype
      ≫ Pi.π (cechTerm S.coverFamily F 2) ![⟨1⟩, ⟨1⟩] = 0 := by
  have hcan : (∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨1⟩, ⟨1⟩, ⟨1⟩])
        : TopologicalSpace.Opens C.left.toTopCat)
      ≤ ∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨1⟩, ⟨1⟩]) :=
    prodOpens_le_of_forall_exists (j := ![⟨1⟩, ⟨1⟩]) (x := ![⟨1⟩, ⟨1⟩, ⟨1⟩])
      S.coverFamily (by decide)
  have hrev : (∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨1⟩, ⟨1⟩])
        : TopologicalSpace.Opens C.left.toTopCat)
      ≤ ∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨1⟩, ⟨1⟩, ⟨1⟩]) :=
    prodOpens_le_of_forall_exists (j := ![⟨1⟩, ⟨1⟩, ⟨1⟩]) (x := ![⟨1⟩, ⟨1⟩])
      S.coverFamily (by decide)
  have h := congrArg (· ≫ Pi.π (cechTerm S.coverFamily F 3) ![⟨1⟩, ⟨1⟩, ⟨1⟩])
    (S.kerSubtype_comp_cechD12 F)
  simp only [Category.assoc, cechD12_π, zero_comp, Preadditive.comp_add,
    Preadditive.comp_sub] at h
  rw [pi_π_restrict_congr S.coverFamily F
      (show (![⟨1⟩, ⟨1⟩, ⟨1⟩] ∘ ⇑(Fin.succAboveOrderEmb 0) : Fin 2 → ULift.{u} (Fin 2))
          = ![⟨1⟩, ⟨1⟩] from by funext i; fin_cases i <;> rfl) _ hcan,
    pi_π_restrict_congr S.coverFamily F
      (show (![⟨1⟩, ⟨1⟩, ⟨1⟩] ∘ ⇑(Fin.succAboveOrderEmb 1) : Fin 2 → ULift.{u} (Fin 2))
          = ![⟨1⟩, ⟨1⟩] from by funext i; fin_cases i <;> rfl) _ hcan,
    pi_π_restrict_congr S.coverFamily F
      (show (![⟨1⟩, ⟨1⟩, ⟨1⟩] ∘ ⇑(Fin.succAboveOrderEmb 2) : Fin 2 → ULift.{u} (Fin 2))
          = ![⟨1⟩, ⟨1⟩] from by funext i; fin_cases i <;> rfl) _ hcan,
    sub_self, zero_add, ← Category.assoc] at h
  haveI := isIso_restrict_map F hcan hrev
  rwa [← cancel_mono (F.obj.map (homOfLE hcan).op), zero_comp]

/-- **Cocycles satisfy `r = −q`** (the `x = (0,1,0)` component of the cocycle
condition, after canonicalising the three coface restrictions and using the vanishing
of the `(0,0)`-component). -/
lemma AffineCoverMVSquare.ker_cechD12_π_off_diag
    (h10 : (∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨0⟩, ⟨1⟩, ⟨0⟩])
        : TopologicalSpace.Opens C.left.toTopCat)
      ≤ ∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨1⟩, ⟨0⟩]))
    (h01 : (∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨0⟩, ⟨1⟩, ⟨0⟩])
        : TopologicalSpace.Opens C.left.toTopCat)
      ≤ ∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨0⟩, ⟨1⟩])) :
    ModuleCat.ofHom (LinearMap.ker (cechD12 S.coverFamily F).hom).subtype
        ≫ Pi.π (cechTerm S.coverFamily F 2) ![⟨1⟩, ⟨0⟩] ≫ F.obj.map (homOfLE h10).op
      = -(ModuleCat.ofHom (LinearMap.ker (cechD12 S.coverFamily F).hom).subtype
        ≫ Pi.π (cechTerm S.coverFamily F 2) ![⟨0⟩, ⟨1⟩] ≫ F.obj.map (homOfLE h01).op) := by
  have hcan00 : (∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨0⟩, ⟨1⟩, ⟨0⟩])
        : TopologicalSpace.Opens C.left.toTopCat)
      ≤ ∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨0⟩, ⟨0⟩]) :=
    prodOpens_le_of_forall_exists (j := ![⟨0⟩, ⟨0⟩]) (x := ![⟨0⟩, ⟨1⟩, ⟨0⟩])
      S.coverFamily (by decide)
  have h := congrArg (· ≫ Pi.π (cechTerm S.coverFamily F 3) ![⟨0⟩, ⟨1⟩, ⟨0⟩])
    (S.kerSubtype_comp_cechD12 F)
  simp only [Category.assoc, cechD12_π, zero_comp, Preadditive.comp_add,
    Preadditive.comp_sub] at h
  rw [pi_π_restrict_congr S.coverFamily F
      (show (![⟨0⟩, ⟨1⟩, ⟨0⟩] ∘ ⇑(Fin.succAboveOrderEmb 0) : Fin 2 → ULift.{u} (Fin 2))
          = ![⟨1⟩, ⟨0⟩] from by funext i; fin_cases i <;> rfl) _ h10,
    pi_π_restrict_congr S.coverFamily F
      (show (![⟨0⟩, ⟨1⟩, ⟨0⟩] ∘ ⇑(Fin.succAboveOrderEmb 1) : Fin 2 → ULift.{u} (Fin 2))
          = ![⟨0⟩, ⟨0⟩] from by funext i; fin_cases i <;> rfl) _ hcan00,
    pi_π_restrict_congr S.coverFamily F
      (show (![⟨0⟩, ⟨1⟩, ⟨0⟩] ∘ ⇑(Fin.succAboveOrderEmb 2) : Fin 2 → ULift.{u} (Fin 2))
          = ![⟨0⟩, ⟨1⟩] from by funext i; fin_cases i <;> rfl) _ h01] at h
  have hz : ModuleCat.ofHom (LinearMap.ker (cechD12 S.coverFamily F).hom).subtype
      ≫ Pi.π (cechTerm S.coverFamily F 2) ![⟨0⟩, ⟨0⟩] ≫ F.obj.map (homOfLE hcan00).op
      = 0 := by
    rw [← Category.assoc, S.ker_cechD12_π_diag_zero₀ F, zero_comp]
  rw [hz, sub_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The projection of a 1-cocycle to its `(0,1)`-component, transported to the
overlap sections.  This is the inverse direction of the kernel identification. -/
noncomputable def AffineCoverMVSquare.cechKerProj :
    LinearMap.ker (cechD12 S.coverFamily F).hom →ₗ[k] F.obj.obj (op S.overlapOpen) :=
  (sectionRestrict F S.prodOpens_zero_one.ge) ∘ₗ
    (Pi.π (cechTerm S.coverFamily F 2) ![⟨0⟩, ⟨1⟩]).hom ∘ₗ
      (LinearMap.ker (cechD12 S.coverFamily F).hom).subtype

/-- `cechKerProj`, as a composite of `ModuleCat` morphisms. -/
lemma AffineCoverMVSquare.ofHom_cechKerProj :
    ModuleCat.ofHom (S.cechKerProj F)
      = ModuleCat.ofHom (LinearMap.ker (cechD12 S.coverFamily F).hom).subtype
          ≫ Pi.π (cechTerm S.coverFamily F 2) ![⟨0⟩, ⟨1⟩]
          ≫ F.obj.map (homOfLE S.prodOpens_zero_one.ge).op :=
  rfl

/-- **The overlap cocycle inverts the `(0,1)`-projection on the kernel**: composing
the projection with the overlap cocycle recovers an arbitrary 1-cocycle.  The four
components are exactly the concrete kernel description `ker d¹ = {(0, q, −q, 0)}`:
the diagonal components vanish (`ker_cechD12_π_diag_zero₀`/`₁`), the `(0,1)`-component
round-trips, and the `(1,0)`-component is the negative of the `(0,1)`-component
(`ker_cechD12_π_off_diag`). -/
lemma AffineCoverMVSquare.cechKerProj_comp_overlapCocycle :
    ModuleCat.ofHom (S.cechKerProj F) ≫ S.overlapCocycle F
      = ModuleCat.ofHom (LinearMap.ker (cechD12 S.coverFamily F).hom).subtype := by
  refine Pi.hom_ext _ _ fun j => ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b : Fin 2, j = ![⟨a⟩, ⟨b⟩] :=
    ⟨(j 0).down, (j 1).down, by funext i; fin_cases i <;> rfl⟩
  rw [Category.assoc, overlapCocycle_π, S.ofHom_cechKerProj F]
  have htwo : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  rcases htwo a with rfl | rfl <;> rcases htwo b with rfl | rfl
  · -- component (0,0): both sides vanish
    rw [S.overlapCocycleComponent_eq_zero F (by decide) (by decide), comp_zero,
      S.ker_cechD12_π_diag_zero₀ F]
  · -- component (0,1): the round-trip restriction is the identity
    rw [S.overlapCocycleComponent_zero_one F]
    simp only [Category.assoc, restrict_map_comp, restrict_map_self, Category.comp_id]
  · -- component (1,0): the off-diagonal kernel relation
    have h10 : (∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨0⟩, ⟨1⟩, ⟨0⟩])
          : TopologicalSpace.Opens C.left.toTopCat)
        ≤ ∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨1⟩, ⟨0⟩]) :=
      prodOpens_le_of_forall_exists (j := ![⟨1⟩, ⟨0⟩]) (x := ![⟨0⟩, ⟨1⟩, ⟨0⟩])
        S.coverFamily (by decide)
    have hrev : (∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨1⟩, ⟨0⟩])
          : TopologicalSpace.Opens C.left.toTopCat)
        ≤ ∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨0⟩, ⟨1⟩, ⟨0⟩]) :=
      prodOpens_le_of_forall_exists (j := ![⟨0⟩, ⟨1⟩, ⟨0⟩]) (x := ![⟨1⟩, ⟨0⟩])
        S.coverFamily (by decide)
    have h01 : (∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨0⟩, ⟨1⟩, ⟨0⟩])
          : TopologicalSpace.Opens C.left.toTopCat)
        ≤ ∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨0⟩, ⟨1⟩]) :=
      prodOpens_le_of_forall_exists (j := ![⟨0⟩, ⟨1⟩]) (x := ![⟨0⟩, ⟨1⟩, ⟨0⟩])
        S.coverFamily (by decide)
    rw [S.overlapCocycleComponent_one_zero F]
    haveI := isIso_restrict_map F h10 hrev
    rw [← cancel_mono (F.obj.map (homOfLE h10).op)]
    simp only [Category.assoc]
    rw [S.ker_cechD12_π_off_diag F h10 h01]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp, restrict_map_comp]
  · -- component (1,1): both sides vanish
    rw [S.overlapCocycleComponent_eq_zero F (by decide) (by decide), comp_zero,
      S.ker_cechD12_π_diag_zero₁ F]

/-- **Node N5, kernel half: the overlap sections are the degree-`1` Čech cocycles.**
The `k`-linear equivalence `Γ(U₁ ⊓ U₂, F) ≃ₗ[k] ker d¹`, sending `q` to the cocycle
`(0, q, −q, 0)`, with inverse the `(0,1)`-component projection. -/
noncomputable def AffineCoverMVSquare.overlapKerEquiv :
    F.obj.obj (op S.overlapOpen) ≃ₗ[k] LinearMap.ker (cechD12 S.coverFamily F).hom :=
  LinearEquiv.ofLinear
    ((S.overlapCocycle F).hom.codRestrict (LinearMap.ker (cechD12 S.coverFamily F).hom)
      fun q => LinearMap.mem_ker.mpr (by
        have h := congrArg (fun t => t.hom q) (S.overlapCocycle_comp_d F)
        simpa using h))
    (S.cechKerProj F)
    (by
      refine LinearMap.ext fun n => Subtype.ext ?_
      have h := congrArg (fun t => t.hom n) (S.cechKerProj_comp_overlapCocycle F)
      simpa using h)
    (by
      refine LinearMap.ext fun q => ?_
      have h := congrArg (fun t => t.hom q) (S.overlapCocycle_π F ![⟨0⟩, ⟨1⟩])
      rw [S.overlapCocycleComponent_zero_one F] at h
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      change sectionRestrict F S.prodOpens_zero_one.ge
        ((Pi.π (cechTerm S.coverFamily F 2) ![⟨0⟩, ⟨1⟩]).hom
          ((S.overlapCocycle F).hom q)) = q
      rw [h]
      change sectionRestrict F _ (sectionRestrict F _ q) = q
      rw [sectionRestrict_trans, sectionRestrict_self])

/-! ### The range identification `κ (im sectionDiff) = im (toCycles)` (node N5) -/

/-- The Čech single intersection at the multi-index `(0)` is the first cover member. -/
lemma AffineCoverMVSquare.prodOpens_single₀ :
    (∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨0⟩])
        : TopologicalSpace.Opens C.left.toTopCat)
      = S.coverFamily ⟨0⟩ := by
  rw [prodOpens_fin_one, Matrix.cons_val_zero]

/-- The Čech single intersection at the multi-index `(1)` is the second cover member. -/
lemma AffineCoverMVSquare.prodOpens_single₁ :
    (∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ ![⟨1⟩])
        : TopologicalSpace.Opens C.left.toTopCat)
      = S.coverFamily ⟨1⟩ := by
  rw [prodOpens_fin_one, Matrix.cons_val_zero]

/-- Components of the pair lift: a pair of sections on the two cover members defines
a degree-`0` Čech cochain. -/
noncomputable def AffineCoverMVSquare.pairComponent (j : Fin 1 → ULift.{u} (Fin 2)) :
    ModuleCat.of k
        (F.obj.obj (op (S.coverFamily ⟨0⟩)) × F.obj.obj (op (S.coverFamily ⟨1⟩)))
      ⟶ cechTerm S.coverFamily F 1 j :=
  if h : j = ![⟨0⟩] then
    ModuleCat.ofHom (LinearMap.fst k _ _)
      ≫ F.obj.map (homOfLE (le_of_eq (by rw [h]; exact S.prodOpens_single₀))).op
  else if h' : j = ![⟨1⟩] then
    ModuleCat.ofHom (LinearMap.snd k _ _)
      ≫ F.obj.map (homOfLE (le_of_eq (by rw [h']; exact S.prodOpens_single₁))).op
  else 0

/-- The pair lift `Γ(𝒰₀) × Γ(𝒰₁) ⟶ Č⁰`. -/
noncomputable def AffineCoverMVSquare.pairLift :
    ModuleCat.of k
        (F.obj.obj (op (S.coverFamily ⟨0⟩)) × F.obj.obj (op (S.coverFamily ⟨1⟩)))
      ⟶ ∏ᶜ (cechTerm S.coverFamily F 1) :=
  Pi.lift (S.pairComponent F)

@[reassoc]
lemma AffineCoverMVSquare.pairLift_π (j : Fin 1 → ULift.{u} (Fin 2)) :
    S.pairLift F ≫ Pi.π (cechTerm S.coverFamily F 1) j = S.pairComponent F j :=
  Pi.lift_π _ _

/-- The pair projection `Č⁰ ⟶ Γ(𝒰₀) × Γ(𝒰₁)` (the inverse of `pairLift`). -/
noncomputable def AffineCoverMVSquare.pairProj :
    (∏ᶜ (cechTerm S.coverFamily F 1) : ModuleCat.{u} k)
      ⟶ ModuleCat.of k
        (F.obj.obj (op (S.coverFamily ⟨0⟩)) × F.obj.obj (op (S.coverFamily ⟨1⟩))) :=
  ModuleCat.ofHom (LinearMap.prod
    ((sectionRestrict F S.prodOpens_single₀.ge) ∘ₗ
      (Pi.π (cechTerm S.coverFamily F 1) ![⟨0⟩]).hom)
    ((sectionRestrict F S.prodOpens_single₁.ge) ∘ₗ
      (Pi.π (cechTerm S.coverFamily F 1) ![⟨1⟩]).hom))

/-- The `(0)`-branch of the pair component, after a further restriction (stated with
the index as a variable so the coface indices can be substituted). -/
lemma AffineCoverMVSquare.pairComponent_comp_eq₀
    {j : Fin 1 → ULift.{u} (Fin 2)} (h : j = ![⟨0⟩])
    {W : TopologicalSpace.Opens C.left.toTopCat}
    (hW : W ≤ ∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ j)) :
    S.pairComponent F j ≫ F.obj.map (homOfLE hW).op
      = ModuleCat.ofHom (LinearMap.fst k _ _)
          ≫ F.obj.map (homOfLE (hW.trans
              (le_of_eq (by rw [h]; exact S.prodOpens_single₀)))).op := by
  subst h
  simp +decide only [pairComponent, dite_true, dite_false, Category.assoc,
    restrict_map_comp]

/-- The `(1)`-branch of the pair component, after a further restriction. -/
lemma AffineCoverMVSquare.pairComponent_comp_eq₁
    {j : Fin 1 → ULift.{u} (Fin 2)} (h : j = ![⟨1⟩])
    {W : TopologicalSpace.Opens C.left.toTopCat}
    (hW : W ≤ ∏ᶜ ((FormalCoproduct.mk _ S.coverFamily).obj ∘ j)) :
    S.pairComponent F j ≫ F.obj.map (homOfLE hW).op
      = ModuleCat.ofHom (LinearMap.snd k _ _)
          ≫ F.obj.map (homOfLE (hW.trans
              (le_of_eq (by rw [h]; exact S.prodOpens_single₁)))).op := by
  subst h
  simp +decide only [pairComponent, dite_true, dite_false, Category.assoc,
    restrict_map_comp]

/-- The `(0)`-component of the pair lift, uncomposed form. -/
lemma AffineCoverMVSquare.pairComponent_eq₀' :
    S.pairComponent F ![⟨0⟩]
      = ModuleCat.ofHom (LinearMap.fst k _ _)
          ≫ F.obj.map (homOfLE (le_of_eq S.prodOpens_single₀)).op := by
  unfold pairComponent
  rw [dif_pos rfl]

/-- The `(1)`-component of the pair lift, uncomposed form. -/
lemma AffineCoverMVSquare.pairComponent_eq₁' :
    S.pairComponent F ![⟨1⟩]
      = ModuleCat.ofHom (LinearMap.snd k _ _)
          ≫ F.obj.map (homOfLE (le_of_eq S.prodOpens_single₁)).op := by
  unfold pairComponent
  rw [dif_neg (by decide), dif_pos rfl]

/-- The first component of the pair projection is the restricted `(0)`-projection. -/
lemma AffineCoverMVSquare.pairProj_fst :
    S.pairProj F ≫ ModuleCat.ofHom (LinearMap.fst k _ _)
      = Pi.π (cechTerm S.coverFamily F 1) ![⟨0⟩]
          ≫ F.obj.map (homOfLE S.prodOpens_single₀.ge).op :=
  ModuleCat.hom_ext (LinearMap.fst_prod _ _)

/-- The second component of the pair projection is the restricted `(1)`-projection. -/
lemma AffineCoverMVSquare.pairProj_snd :
    S.pairProj F ≫ ModuleCat.ofHom (LinearMap.snd k _ _)
      = Pi.π (cechTerm S.coverFamily F 1) ![⟨1⟩]
          ≫ F.obj.map (homOfLE S.prodOpens_single₁.ge).op :=
  ModuleCat.hom_ext (LinearMap.snd_prod _ _)

/-- **The pair lift is a section of the pair projection**: rebuilding a degree-`0`
cochain from its two components is the identity. -/
lemma AffineCoverMVSquare.pairProj_comp_pairLift :
    S.pairProj F ≫ S.pairLift F = 𝟙 _ := by
  refine Pi.hom_ext _ _ fun j => ?_
  obtain ⟨a, rfl⟩ : ∃ a : Fin 2, j = ![⟨a⟩] :=
    ⟨(j 0).down, by funext i; fin_cases i; rfl⟩
  have htwo : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  rw [Category.assoc, pairLift_π, Category.id_comp]
  rcases htwo a with rfl | rfl
  · rw [S.pairComponent_eq₀' F, ← Category.assoc, S.pairProj_fst F, Category.assoc,
      restrict_map_comp, restrict_map_self, Category.comp_id]
  · rw [S.pairComponent_eq₁' F, ← Category.assoc, S.pairProj_snd F, Category.assoc,
      restrict_map_comp, restrict_map_self, Category.comp_id]

/-- The difference-of-restrictions map on the pair carrier, in its uniformly-typed
`ModuleCat`-morphism form (definitionally `S.sectionDiff F`). -/
noncomputable def AffineCoverMVSquare.pairDiff :
    ModuleCat.of k
        (F.obj.obj (op (S.coverFamily ⟨0⟩)) × F.obj.obj (op (S.coverFamily ⟨1⟩)))
      ⟶ F.obj.obj (op S.overlapOpen) :=
  ModuleCat.ofHom (LinearMap.fst k _ _)
      ≫ F.obj.map (homOfLE (inf_le_left : S.overlapOpen ≤ S.coverFamily ⟨0⟩)).op
    - ModuleCat.ofHom (LinearMap.snd k _ _)
      ≫ F.obj.map (homOfLE (inf_le_right : S.overlapOpen ≤ S.coverFamily ⟨1⟩)).op

/-- `pairDiff` is definitionally the difference-of-restrictions map `sectionDiff`. -/
lemma AffineCoverMVSquare.pairDiff_hom :
    (S.pairDiff F).hom = S.sectionDiff F :=
  rfl

/-- **`d⁰` on a lifted pair is the negated overlap cocycle of the section
difference**: `d⁰ (a, b) = (0, b−a, a−b, 0) = −(0, (a−b), −(a−b), 0)`. -/
lemma AffineCoverMVSquare.pairLift_comp_cechD01 :
    S.pairLift F ≫ cechD01 S.coverFamily F
      = -(S.pairDiff F ≫ S.overlapCocycle F) := by
  refine Pi.hom_ext _ _ fun j => ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b : Fin 2, j = ![⟨a⟩, ⟨b⟩] :=
    ⟨(j 0).down, (j 1).down, by funext i; fin_cases i <;> rfl⟩
  have htwo : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  rw [Category.assoc, cechD01_π, Preadditive.comp_sub, Preadditive.neg_comp,
    Category.assoc, overlapCocycle_π, ← Category.assoc, ← Category.assoc,
    pairLift_π, pairLift_π]
  rcases htwo a with rfl | rfl <;> rcases htwo b with rfl | rfl
  · -- (0,0): both cofaces hit the first member; the diagonal cocycle component is 0
    rw [S.pairComponent_comp_eq₀ F (by funext i; fin_cases i; rfl),
      S.pairComponent_comp_eq₀ F (by funext i; fin_cases i; rfl),
      S.overlapCocycleComponent_eq_zero F (by decide) (by decide), comp_zero, neg_zero]
    abel
  · -- (0,1): `b|₀₁ − a|₀₁ = −(a−b)|₀₁`
    rw [S.pairComponent_comp_eq₁ F (by funext i; fin_cases i; rfl),
      S.pairComponent_comp_eq₀ F (by funext i; fin_cases i; rfl),
      S.overlapCocycleComponent_zero_one F]
    simp only [pairDiff, Preadditive.sub_comp, Category.assoc, restrict_map_comp]
    abel
  · -- (1,0): `a|₀₁ − b|₀₁ = −(−(a−b))|₀₁`
    rw [S.pairComponent_comp_eq₀ F (by funext i; fin_cases i; rfl),
      S.pairComponent_comp_eq₁ F (by funext i; fin_cases i; rfl),
      S.overlapCocycleComponent_one_zero F]
    simp only [pairDiff, Preadditive.sub_comp, Preadditive.comp_neg, Category.assoc,
      restrict_map_comp, neg_neg]
  · -- (1,1): both cofaces hit the second member
    rw [S.pairComponent_comp_eq₁ F (by funext i; fin_cases i; rfl),
      S.pairComponent_comp_eq₁ F (by funext i; fin_cases i; rfl),
      S.overlapCocycleComponent_eq_zero F (by decide) (by decide), comp_zero, neg_zero]
    abel

/-- The value of the concrete `toCycles` is the value of `d⁰`. -/
lemma AffineCoverMVSquare.cechToCyclesD01_coe
    (m : (∏ᶜ (cechTerm S.coverFamily F 1) : ModuleCat.{u} k)) :
    (cechToCyclesD01 S.coverFamily F m
        : (∏ᶜ (cechTerm S.coverFamily F 2) : ModuleCat.{u} k))
      = (cechD01 S.coverFamily F).hom m :=
  rfl

/-- The value of the kernel equivalence is the value of the overlap cocycle. -/
lemma AffineCoverMVSquare.overlapKerEquiv_coe (q : F.obj.obj (op S.overlapOpen)) :
    (S.overlapKerEquiv F q : (∏ᶜ (cechTerm S.coverFamily F 2) : ModuleCat.{u} k))
      = (S.overlapCocycle F).hom q :=
  rfl

/-- **The range identification (node N5)**: under the kernel equivalence
`overlapKerEquiv`, the coboundary subspace `im (sectionDiff)` of the overlap sections
corresponds exactly to the image of `d⁰` inside the cocycles. -/
lemma AffineCoverMVSquare.map_range_pairDiff :
    (LinearMap.range (S.pairDiff F).hom).map (S.overlapKerEquiv F).toLinearMap
      = LinearMap.range (cechToCyclesD01 S.coverFamily F) := by
  apply le_antisymm
  · rintro n hn
    obtain ⟨q, ⟨p, rfl⟩, rfl⟩ := Submodule.mem_map.mp hn
    refine ⟨(S.pairLift F).hom (-p), Subtype.ext ?_⟩
    have h := congrArg (fun t => t.hom p) (S.pairLift_comp_cechD01 F)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_neg,
      LinearMap.neg_apply] at h
    rw [S.cechToCyclesD01_coe F, LinearEquiv.coe_coe, S.overlapKerEquiv_coe F,
      map_neg, map_neg, h, neg_neg]
  · rintro n ⟨m, rfl⟩
    refine Submodule.mem_map.mpr
      ⟨(S.pairDiff F).hom (-((S.pairProj F).hom m)), ⟨-((S.pairProj F).hom m), rfl⟩,
        Subtype.ext ?_⟩
    have hfact := congrArg (fun t => t.hom m) (S.pairProj_comp_pairLift F)
    have h := congrArg (fun t => t.hom ((S.pairProj F).hom m)) (S.pairLift_comp_cechD01 F)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_neg,
      LinearMap.neg_apply, ModuleCat.hom_id, LinearMap.id_coe, id_eq] at hfact h
    rw [hfact] at h
    rw [LinearEquiv.coe_coe, S.overlapKerEquiv_coe F, S.cechToCyclesD01_coe F,
      map_neg, map_neg]
    exact h.symm

/-- The concrete `toCycles` is definitionally the `moduleCatToCycles` of the short
complex `sc' 0 1 2` of the Čech cochain complex. -/
lemma AffineCoverMVSquare.cechToCyclesD01_eq :
    cechToCyclesD01 S.coverFamily F
      = ((Scheme.cechCochain C F S.coverFamily).sc' 0 1 2).moduleCatToCycles :=
  rfl

/-- **Node N5 — the degree-`1` Čech cohomology of the 2-affine cover is the concrete
cokernel `Ȟ¹ = Γ(U₁ ⊓ U₂, F) ⧸ im (sectionDiff)`.**  Unconditional: this is a pure
homological-algebra fact about the 2-cover complex — no acyclicity or comparison
hypothesis.  The chain is: homology of the complex at `1` ≅ homology of the short
complex `(d⁰, d¹)` ≅ `ker d¹ ⧸ im (toCycles)` (the concrete `ModuleCat` homology),
and the kernel equivalence `overlapKerEquiv` matches `im (sectionDiff)` with
`im (toCycles)` (`map_range_sectionDiff`), so the quotients agree. -/
noncomputable def AffineCoverMVSquare.cechCohomologyOneEquivH1Cok :
    cechCohomology C F S.coverFamily 1 ≃ₗ[k] S.H1Cok F :=
  ((ShortComplex.homologyMapIso
      ((Scheme.cechCochain C F S.coverFamily).isoSc' 0 1 2
        ((ComplexShape.up ℕ).prev_eq' rfl) ((ComplexShape.up ℕ).next_eq' rfl))).trans
    ((Scheme.cechCochain C F S.coverFamily).sc' 0 1 2).moduleCatHomologyIso).toLinearEquiv.trans
  ((Submodule.Quotient.equiv (LinearMap.range (S.sectionDiff F))
      (LinearMap.range
        ((Scheme.cechCochain C F S.coverFamily).sc' 0 1 2).moduleCatToCycles)
      (S.overlapKerEquiv F)
      ((S.map_range_pairDiff F).trans
        (congrArg LinearMap.range (S.cechToCyclesD01_eq F)))).symm)

/-- **The lane's consumable corollary (nodes N5 + N6)**: under the Čech-to-derived
comparison gate on the 2-affine cover, the genus-degree cohomology `H¹(C, F)` is the
concrete two-chart cokernel `Ȟ¹ = Γ(U₁ ⊓ U₂, F) ⧸ (Γ(U₁, F) + Γ(U₂, F))`. -/
noncomputable def AffineCoverMVSquare.hModuleOneEquivH1Cok
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasCechToHModuleIso F S.coverFamily] :
    HModule k F 1 ≃ₗ[k] S.H1Cok F :=
  (S.hModuleOne_linearEquiv_cechCohomology_coverFamily F 1).trans
    (S.cechCohomologyOneEquivH1Cok F)

end OverlapCocycle

end AlgebraicGeometry.Scheme
