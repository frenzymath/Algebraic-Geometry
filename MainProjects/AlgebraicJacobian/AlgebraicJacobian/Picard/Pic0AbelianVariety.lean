/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.IdentityComponent
import AlgebraicJacobian.Picard.TangentSpaceDualNumbers
import AlgebraicJacobian.Picard.TangentSpaceIdentitySection
import AlgebraicJacobian.Picard.Pic0TangentSpace
import AlgebraicJacobian.Picard.Pic0DualNumberCocycle
import AlgebraicJacobian.Picard.OnePointRelPicCollapse
import AlgebraicJacobian.Picard.GroupSchemeSmoothAlgClosed
import AlgebraicJacobian.Picard.CurveProjectivity
import AlgebraicJacobian.Curve.GeometricallyReduced
import AlgebraicJacobian.RiemannRoch.Adelic.GenusUnconditional
import AlgebraicJacobian.Genus

/-!
# `Pic⁰_{C/k}` as an abelian variety (A.3.iii–vii)

This file is the **iter-193 Pic0AbelianVariety** file-skeleton (NEW lane,
blueprint-doctor flagged orphan resolution for the iter-192 plan-phase chapter
`Picard_Pic0AbelianVariety.tex`). It packages the strategy phase A.3.iii–vi
substrate and the A.3.vii assembly into the load-bearing Route~A statement
`Pic⁰_{C/k}` is an abelian variety, the gate of `thm:nonempty_jacobianWitness`
for `g(C) ≥ 1` curves.

The chapter consumes the abstract identity-component substrate set up in
`Picard/IdentityComponent.lean` (`Pic⁰_{C/k}` as a clopen subgroup scheme of
finite type, geometrically irreducible, formation commuting with base change)
and adds the curve-specific input: the tangent-space isomorphism
`T₀ Pic⁰_{C/k} ≅ H¹(C, 𝒪_C)`, the resulting smoothness of dimension `g` at
the origin (hence everywhere by translation), properness inherited from the
projectivity of `Pic⁰_{C/k}` for `C/k` geometrically normal, and the assembly
into an abelian variety in the sense of Milne §I.1.

## Status (run 0015, T16 W12-tangent session; previously run 0008 T5)

Proved sorry-free in this file: `grpObj` (the `GrpObj (Pic0Scheme C)`
structure, via `IdentityComponent.isSubgroupHomomorphism` +
`PicScheme.groupSchemeStructure`), `tangentSpaceCotangentDual`,
`geometricallyIrreducible` (specialisation of the sibling's
`isFiniteTypeGeometricallyIrreducible`, whose QC∧GeomIrred conjuncts were
closed in run 0009 — `IdentityComponent.lean`, Kleiman §5 Lem.~`lem:agps`(3)),
the `isAbelianVariety` assembly, and the moved
`Pic0Scheme.isAbelianVariety` (blueprint pin `thm:pic_zero_is_abelian_variety`).

## Update (run 0067): `smooth` and `proper` are now assemblies

Both former structural `sorry`s were replaced by reductions, so the file still
carries three `sorry` bodies but each is a smaller named statement:

* `smooth` = `smooth_of_geometricallyReduced` + `geometricallyReduced`. The
  first is PROVED from mathlib's `smooth_of_grpObj`, which already contains the
  translation argument and the descent along `Spec k̄ → Spec k`; its two
  structural inputs (`locallyOfFiniteType`, `grpObj`) are landed here. The only
  open input is `GeometricallyReduced (Pic0Scheme C).hom` — Cartier in
  characteristic zero, `H²(C, 𝒪_C) = 0` in characteristic `p`. Note that
  `Smooth.geometricallyReduced` is the *converse* and using it would be
  circular.
* `proper` = `proper_of_universallyClosed` + `universallyClosed`. The first is
  PROVED: mathlib's `IsProper` is `IsSeparated` + `UniversallyClosed` +
  `LocallyOfFiniteType`, and the separatedness and finite-type conjuncts are
  the already-proved `isSeparated` / `locallyOfFiniteType` of this file. The
  only open input is `UniversallyClosed`, attackable through the proved
  `universallyClosed_of_baseChange` (Stacks 02KS fpqc descent) to the
  algebraically closed case.

Neither reduction weakens a pinned statement: `smooth`, `proper` and the
`isAbelianVariety` assembly keep their types verbatim.

Remaining `sorry` bodies: `finrank_cotangentSpaceDual_eq_finrank_h1Cok` —
the wave-5 W12-cocycle reduced core of the Kleiman §5 Thm 5.11 dimension
identity: `dim_{κ(e)} Dual(m_e/m_e²) = dim_k Ȟ¹(S, 𝒪_C)` against the concrete
two-chart Čech cokernel of any 2-affine cover `S`. The formerly-sorried
dimension identity `finrank_cotangentSpace_eq_finrank_hModuleOne` (which
`tangentSpaceIso` consumes, via the run-0015
`nonempty_cotangentSpaceAddEquiv_of_finrank_eq` reduction of
`Picard/Pic0TangentSpace.lean`) is now PROVED from the reduced core by
`Subspace.dual_finrank_eq` + the genus lane's cover
(`Adelic.exists_affineCoverMVSquare_module_finite_H1Cok`) + the gate-free
comparison `AffineCoverMVSquare.hModuleOneEquivH1Cok_curve`. Wave-4
W12-finrank closed the **representability leg**
(`pointedDualNumberPoints_equiv_relPicKernel`,
`cotangentSpaceDual_equiv_relPicKernel` below, set-level both directions) and
landed the Mumford `ε ↦ aε` scaling substrate; wave-5 landed the **two-chart
Čech unit-cocycle engine** (`DualNumber.truncExpCechKernelAddEquiv`,
`Picard/Pic0DualNumberCocycle.lean` §6 — the algebra layer of the cocycle
leg, with Mumford-scaling equivariance). The remaining content of the core is
the geometric chart-triviality/section-identification substrate plus the
`k`-(semi)linearity bookkeeping — and `smooth`, `proper`.

The 5 blueprint-pinned declarations are:

1. `AlgebraicGeometry.Scheme.Pic0.tangentSpaceIso` (theorem, A.3.iii) — the
   canonical isomorphism `T₀ Pic⁰_{C/k} ≅ H¹(C, 𝒪_C)` (Kleiman §5
   Thm.~`thm:tgtsp`). Packaged as an `AddEquiv` between the cotangent space
   `m_e/m_e²` at a `k`-rational identity-section point `e` and the project's
   first-cohomology `k`-module `Scheme.HModule k (Scheme.toModuleKSheaf C) 1`
   (from `Genus.lean`). The `k`-module structure on the cotangent space at a
   `k`-rational point is supplied as part of the existential bundle.
2. `AlgebraicGeometry.Scheme.Pic0.smooth` (theorem, A.3.iv) — `Pic⁰_{C/k}` is
   `Smooth` over `k`. Kleiman §5 Cor.~`cor:sm` + Cor.~`cor:ch0`
   (characteristic-zero) + Ex.~`ex:jac` (curve case).
3. `AlgebraicGeometry.Scheme.Pic0.proper` (theorem, A.3.v) — `Pic⁰_{C/k}` is
   `IsProper` over `k`. Kleiman §5 Thm.~`th:qpp&p` (projectivity upgrade for
   geometrically normal `C/k`).
4. `AlgebraicGeometry.Scheme.Pic0.geometricallyIrreducible` (theorem, A.3.vi)
   — `Pic⁰_{C/k}` is `GeometricallyIrreducible` over `k`. Specialisation of
   `IdentityComponent.isFiniteTypeGeometricallyIrreducible` (sibling) to
   `G = PicScheme C`. Kleiman §5 Prp.~`prp:pic0`.
5. `AlgebraicGeometry.Scheme.Pic0.isAbelianVariety` (theorem, A.3.vii) —
   `Pic⁰_{C/k}` is an abelian variety: `IsProper ∧ Smooth ∧
   GeometricallyIrreducible ∧ Nonempty (GrpObj _)`. Milne §I.1, p.~8
   (defining axioms) + Kleiman §5 Rmk.~`rmk:Jac`. Load-bearing A.3.vii gate
   of Route~A.

## Note on type expressivity

Following the project rule "Never weaken the type to dodge the proof", each
pinned declaration carries a substantive, non-tautological type:

- `tangentSpaceIso C` — existentially quantifies over a `k`-rational
  identity-section point `e : Spec k ⟶ (Pic0Scheme C).left` and a `k`-module
  structure on the cotangent space `m_e/m_e²` (the `k`-module structure
  arising via the `k`-algebra structure on the stalk at a `k`-rational point;
  for the file-skeleton this Module instance is bundled as part of the Σ').
  Bundles an `AddEquiv` between the cotangent space and the
  `H¹(C, 𝒪_C)`-as-`k`-module. The body is iter-194+ work.
- `smooth C`, `proper C`, `geometricallyIrreducible C` — genuine `Prop`-valued
  statements on the structural morphism `(Pic0Scheme C).hom : Pic⁰_{C/k} ⟶
  Spec k`, not tautological.
- `isAbelianVariety C` — assembles the conjunction of the four
  abelian-variety properties (proper, smooth, geometrically irreducible,
  group-object structure); not vacuous because each conjunct is a genuine
  property/structure on the (typed-sorry) `Pic0Scheme C`.

## Coordination with `Pic0Scheme`

The underlying `k`-scheme `Pic⁰_{C/k}` is supplied by
`AlgebraicGeometry.Scheme.Pic0Scheme C` from sibling
`Picard/IdentityComponent.lean` (`def:pic_zero_subscheme` in the blueprint).
We do not redefine the underlying scheme here; the `Pic0` namespace below
collects the curve-specific abelian-variety facts about `Pic0Scheme C`.

## References

Blueprint: `blueprint/src/chapters/Picard_Pic0AbelianVariety.tex`
(735 LOC, 5 pins). Sources:
- Kleiman, "The Picard scheme", §5, Thm.~`thm:tgtsp` (tangent space),
  Cor.~`cor:sm` + Cor.~`cor:ch0` (smoothness), Thm.~`th:qpp&p`
  (quasi-projectivity/projectivity), Prp.~`prp:pic0` (irreducibility),
  Rmk.~`rmk:Jac` (assembly to abelian scheme); arXiv:math/0504020.
- Milne, "Abelian Varieties" (course notes, 2008), §I.1, p.~8
  (definition of abelian variety) + Rmk. III.1.4(e) (dimension equals genus).
-/

set_option autoImplicit false

universe u

-- `v` is used only by the scalar-transport dimension lemma
-- `Pic0.finrank_eq_of_addEquiv_of_bijective_smul`, whose two modules must share
-- a universe because mathlib's `rank_eq_of_equiv_equiv` states them at one.
universe v

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-! ## §0b. The Čech side of the cocycle leg: `Ȟ¹` as the unit-cocycle kernel

Wave-5 W12-cocycle connector: for a 2-affine cover `S` of the curve, the
concrete Čech cokernel `S.H1Cok (toModuleKSheaf C) = Γ(U₁ ⊓ U₂) ⧸ range
(sectionDiff)` — which is `H¹(C, 𝒪_C)` by the gate-free comparison
`hModuleOneEquivH1Cok_curve` — is identified additively with the kernel of
the two-chart dual-number Čech-units reduction of
`Picard/Pic0DualNumberCocycle.lean` §6, via the truncated exponential. This
is the ENTIRE Čech side of the Kleiman §5 Thm 5.11 cocycle leg; the open
geometric distance to `finrank_cotangentSpaceDual_eq_finrank_h1Cok` below is
the identification of the units-cocycle Picard kernel with the honest
relative-Pic kernel (chart triviality on the nilpotent thickening) plus the
`κ(e) ≃+* k` linearity bookkeeping. -/

/-- The restriction homomorphism `Γ(U₁, 𝒪_C) →+* Γ(U₁ ⊓ U₂, 𝒪_C)` of a
2-affine cover — the first chart map of the two-chart Čech datum. -/
noncomputable abbrev AffineCoverMVSquare.resLeft {k : Type u} [Field k]
    {C : Over (Spec (CommRingCat.of k))} (S : C.left.AffineCoverMVSquare) :
    ↥(C.left.presheaf.obj (Opposite.op S.U₁)) →+*
      ↥(C.left.presheaf.obj (Opposite.op (S.U₁ ⊓ S.U₂))) :=
  (C.left.presheaf.map (homOfLE (inf_le_left : S.U₁ ⊓ S.U₂ ≤ S.U₁)).op).hom

/-- The restriction homomorphism `Γ(U₂, 𝒪_C) →+* Γ(U₁ ⊓ U₂, 𝒪_C)` of a
2-affine cover — the second chart map of the two-chart Čech datum. -/
noncomputable abbrev AffineCoverMVSquare.resRight {k : Type u} [Field k]
    {C : Over (Spec (CommRingCat.of k))} (S : C.left.AffineCoverMVSquare) :
    ↥(C.left.presheaf.obj (Opposite.op S.U₂)) →+*
      ↥(C.left.presheaf.obj (Opposite.op (S.U₁ ⊓ S.U₂))) :=
  (C.left.presheaf.map (homOfLE (inf_le_right : S.U₁ ⊓ S.U₂ ≤ S.U₂)).op).hom

/-- **The coboundary submodule of a 2-affine cover is the additive Čech
coboundary subgroup**: the range of the difference-of-restrictions map
`sectionDiff` (whose quotient is `H1Cok`) coincides, as an additive
subgroup of the overlap ring, with `ρ₁(Γ(U₁)) + ρ₂(Γ(U₂))` — the
`DualNumber.cechCoboundaryAdd` of the restriction datum. A difference
`ρ₁ a - ρ₂ b` and a sum `ρ₁ a + ρ₂ b` span the same subgroup (the clean-binder
helpers `sub_mem_cechCoboundaryAdd` / `exists_sub_of_mem_cechCoboundaryAdd`
of `Picard/Pic0DualNumberCocycle.lean` cross the `Scheme.Opens` presentation
diamond by pure defeq `exact`s). -/
theorem AffineCoverMVSquare.range_sectionDiff_toAddSubgroup {k : Type u} [Field k]
    {C : Over (Spec (CommRingCat.of k))} (S : C.left.AffineCoverMVSquare) :
    (LinearMap.range (S.sectionDiff (Scheme.toModuleKSheaf C))).toAddSubgroup
      = DualNumber.cechCoboundaryAdd S.resLeft S.resRight := by
  refine AddSubgroup.ext fun s => Iff.intro (fun hs => ?_) (fun hs => ?_)
  · obtain ⟨⟨a, b⟩, hp⟩ :=
      LinearMap.mem_range.mp ((Submodule.mem_toAddSubgroup _).mp hs)
    have hp' : S.resLeft a - S.resRight b = s := hp
    exact hp' ▸ DualNumber.sub_mem_cechCoboundaryAdd S.resLeft S.resRight a b
  · have hs' : (s : ↥(C.left.presheaf.obj (Opposite.op (S.U₁ ⊓ S.U₂)))) ∈
        DualNumber.cechCoboundaryAdd S.resLeft S.resRight := hs
    obtain ⟨a₁, a₂, ha⟩ := DualNumber.exists_sub_of_mem_cechCoboundaryAdd
      (B := ↥(C.left.presheaf.obj (Opposite.op (S.U₁ ⊓ S.U₂)))) hs'
    exact (Submodule.mem_toAddSubgroup _).mpr
      (LinearMap.mem_range.mpr ⟨(a₁, a₂), ha⟩)

/-- The concrete Čech cokernel of a 2-affine cover, as the additive
coboundary quotient of the overlap ring: `S.H1Cok (toModuleKSheaf C) ≃+
Γ(U₁ ⊓ U₂) ⧸ (ρ₁(Γ(U₁)) + ρ₂(Γ(U₂)))`. The underlying quotients are the
same (`range_sectionDiff_toAddSubgroup`; a `Submodule` quotient is
definitionally the quotient by its `toAddSubgroup`). -/
noncomputable def AffineCoverMVSquare.h1CokAddEquivCechQuotient {k : Type u} [Field k]
    {C : Over (Spec (CommRingCat.of k))} (S : C.left.AffineCoverMVSquare) :
    S.H1Cok (Scheme.toModuleKSheaf C) ≃+
      (↥(C.left.presheaf.obj (Opposite.op (S.U₁ ⊓ S.U₂))) ⧸
        DualNumber.cechCoboundaryAdd S.resLeft S.resRight) :=
  (AddEquiv.refl _ :
      S.H1Cok (Scheme.toModuleKSheaf C) ≃+
        (↥(C.left.presheaf.obj (Opposite.op (S.U₁ ⊓ S.U₂))) ⧸
          (LinearMap.range (S.sectionDiff (Scheme.toModuleKSheaf C))).toAddSubgroup)).trans
    (QuotientAddGroup.quotientAddEquivOfEq S.range_sectionDiff_toAddSubgroup)

/-- **The dual-number kernel of the relative Picard functor, as an `AddSubgroup`** — the
prerequisite of clause (iii) of the geometric middle (run 0067).

`ker(Pic^♯_{C/k}(Spec k[ε]) →+ Pic^♯_{C/k}(Spec k))`, the tangent space of the Picard functor
at the identity in its functor-of-points form.

WHY THIS EXISTS AS A NAMED DEFINITION rather than being spelled inline. The
representability leg (`pointedDualNumberPointsEquivAddKernel`,
`Picard/Pic0DualNumberCocycle.lean`) delivers this kernel as the *subtype*
`{a // (map …).hom a = 0}`. That subtype **is** the coercion of this `AddSubgroup` — the
`rfl` below — but instance search does not see through the subtype spelling to find the
group structure, so an `≃+` stated against the subtype fails to elaborate with
`failed to synthesize Add {a // …}` while the same statement against this definition
elaborates. Spelled as the `AddSubgroup`, the group structure is free.

This is what makes clause (iii) of `semilinearComparison_cotangentSpaceDual_h1Cok`
*statable* as an additive equivalence rather than as a bare `Equiv` — and a bare `Equiv`
does not transport `finrank`, which is precisely the error the sibling project retracted on
this lane (inbox I-0495, 2026-07-28). The Čech side of the same comparison is
`AffineCoverMVSquare.h1CokAddEquivTruncExpCechKernel` below, already additive. -/
noncomputable def relPicDualKernel {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    AddSubgroup ((PicSharp.relPresheaf C).obj (Opposite.op (overDualNumber k))) :=
  ((PicSharp.relPresheaf C).map (overDualNumberZero k).op).hom.ker

/-- The `AddSubgroup` spelling of the dual-number kernel has the same carrier as the subtype
the representability leg produces — definitionally, so no transport is needed anywhere. Only
the *instance* behaviour differs (see `relPicDualKernel`). -/
theorem relPicDualKernel_eq_subtype {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    (relPicDualKernel C : Type (u + 1))
      = {a : (PicSharp.relPresheaf C).obj (Opposite.op (overDualNumber k)) //
          ((PicSharp.relPresheaf C).map (overDualNumberZero k).op).hom a = 0} :=
  rfl

/-- **The relative quotient leaves clause (iii)** (run 0067 r2): the dual-number kernel of
the *relative* Picard functor is additively the dual-number kernel of the **absolute** Picard
group `Pic(C ×_k Spec k[ε])`.

`Picard/OnePointRelPicCollapse.lean` proves the input: at a test object with a one-point
underlying space — and `Spec k[ε]` is one, `DualNumber k` being local with nilpotent maximal
ideal — the coset subgroup `π_T^* Pic(T)` that `relPresheaf` quotients by is *trivial*,
because a locally trivial module on a one-point scheme is globally trivial (every nonempty
open is `⊤`). So `relPicDualKernel C`, which is the left-hand side verbatim, may be replaced
by an honest kernel on the absolute Picard group.

WHY THIS MATTERS FOR THE `sorry` BELOW. The Čech side of the comparison
(`AffineCoverMVSquare.h1CokAddEquivTruncExpCechKernel`, and the whole §6 unit-cocycle engine
of `Picard/Pic0DualNumberCocycle.lean`) computes with *absolute* Picard classes of the
thickened curve — transition units on a two-chart cover. It never had a coset quotient in it.
Before this, clause (iii) had to bridge that mismatch as part of its own content; now the
`H_T`-quotient is gone from the problem and what remains is the cocycle identification alone.

Recorded as a named bridge rather than inlined, so the `sorry` below can be restated against
the absolute side by whoever builds the cocycle map, on either project (inbox I-0495). -/
noncomputable def relPicDualKernelAddEquivAbsKernel {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    relPicDualKernel C ≃+
      ((PicSharp C).map (overDualNumberZero k).op).hom.ker :=
  PicSharp.kerRelPresheafAddEquivKerAbs C

/-- **The Čech side of the Kleiman §5 Thm 5.11 cocycle leg, assembled**:
for any 2-affine cover `S` of the curve, the concrete Čech cokernel
`Ȟ¹(S, 𝒪_C)` — i.e. `H¹(C, 𝒪_C)`, by `hModuleOneEquivH1Cok_curve` — is
additively the kernel of the dual-number Čech-units reduction
`Ȟ¹ˣ(Γ(U₁ ⊓ U₂)[ε]) →* Ȟ¹ˣ(Γ(U₁ ⊓ U₂))` (the two-chart cocycle model of
`ker(Pic(C ×_k Spec k[ε]) → Pic(C))`), via the truncated exponential
`b ↦ [1 + b ε]` (`DualNumber.truncExpCechKernelAddEquiv`). -/
noncomputable def AffineCoverMVSquare.h1CokAddEquivTruncExpCechKernel {k : Type u}
    [Field k] {C : Over (Spec (CommRingCat.of k))} (S : C.left.AffineCoverMVSquare) :=
  (S.h1CokAddEquivCechQuotient).trans
    (DualNumber.truncExpCechKernelAddEquiv S.resLeft S.resRight)

/-! ## §1. The `Pic0` namespace

The blueprint chapter pins five Lean declarations under the
`AlgebraicGeometry.Scheme.Pic0` namespace. Their underlying scheme
`Pic⁰_{C/k}` is `Pic0Scheme C` from sibling `Picard/IdentityComponent.lean`;
the declarations below collect the curve-specific abelian-variety facts
about `Pic0Scheme C` (tangent space at the identity, smoothness, properness,
geometric irreducibility, abelian-variety assembly). -/

namespace Pic0

/-- **`Pic⁰_{C/k}` is a `k`-group scheme** — the group-object structure on
the identity component of the Picard scheme, inherited from `Pic_{C/k}` via
the clopen inclusion `Pic⁰_{C/k} ↪ Pic_{C/k}`.

Since `Pic0Scheme C` unwinds definitionally to
`GroupScheme.IdentityComponent (PicScheme C)` (run-0008 FGA rewire), this is
`GroupScheme.IdentityComponent.isSubgroupHomomorphism` applied to
`G = PicScheme C`, whose `GrpObj` instance is
`PicScheme.groupSchemeStructure` (Yoneda transport of the abelian-group
structure of the relative Picard presheaf) and whose local finiteness is the
`PicSchemeLocallyOfFiniteType` carrier (Kleiman §4 Thm `th:main`(1)). -/
theorem grpObj {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Nonempty (GrpObj (Pic0Scheme C)) :=
  GroupScheme.IdentityComponent.isSubgroupHomomorphism (PicScheme C)

/-! ### §1b. Harvested helper lemmas (from GitHub PR #1, Alex Nguyen)

Sorry-free scheme-general and `Pic⁰_{C/k}`-specific helpers adapted from the
PR: the `k`-rationality residue-field identification, finite-dimensionality of
the cotangent space over a field, the pointed dual-number tangent-space API,
the separatedness / local-finite-type / quasi-compactness transports of the
identity-component substrate, and the fpqc-descent reduction of universal
closedness. Each `Pic⁰`-specific helper carries the file's standard instance
hypotheses `[HasPicScheme C] [PicScheme.PicSchemeLocallyOfFiniteType C]` (rather
than the PR's `haveI := instHasPicScheme C` pattern, which needs the absent
`[HasRationalPoint C]`), exactly as every other pinned declaration here. -/

/-- **Sorry-free, scheme-general.** A section `e : Spec k ⟶ X` of a scheme over
`Spec k` is a `k`-rational point, so the residue field at `e` is canonically
`k`. The section `e` and structure map `π` induce residue-field maps
`sbar : κ(e) → κ(pt)` and `pbar : κ(pt') → κ(e)` with
`pbar ≫ sbar = (e ≫ π).residueFieldMap default`, an iso because `e ≫ π = 𝟙`
is an open immersion; hence `sbar` is a split epi, and being a field
homomorphism it is a mono, so `sbar` is an isomorphism
(`isIso_of_mono_of_isSplitEpi`). The base residue-field identification is
discharged by composing `Scheme.Spec.residueFieldIso` with
`Ideal.algEquivResidueFieldOfField`. -/
theorem residueFieldIso_of_section_over_field {k : Type u} [Field k]
    (X : Over (Spec (.of k))) (e : Spec (.of k) ⟶ X.left)
    (hsec : e ≫ X.hom = 𝟙 (Spec (.of k))) :
    Nonempty (X.left.residueField (e.base default) ≅ CommRingCat.of k) := by
  set sbar := e.residueFieldMap default with hsbar
  set pbar := X.hom.residueFieldMap (e.base default) with hpbar
  have hc : (e ≫ X.hom).residueFieldMap default = pbar ≫ sbar :=
    residueFieldMap_comp e X.hom default
  haveI : IsOpenImmersion (e ≫ X.hom) := by rw [hsec]; infer_instance
  haveI : IsIso (pbar ≫ sbar) :=
    hc ▸ (inferInstance : IsIso ((e ≫ X.hom).residueFieldMap default))
  haveI : IsSplitEpi sbar :=
    ⟨⟨inv (pbar ≫ sbar) ≫ pbar, by rw [Category.assoc, IsIso.inv_hom_id]⟩⟩
  haveI : Mono sbar :=
    ConcreteCategory.mono_of_injective sbar sbar.hom.injective
  haveI : IsIso sbar := isIso_of_mono_of_isSplitEpi sbar
  obtain ⟨hbase⟩ : Nonempty ((Spec (.of k)).residueField default ≅ CommRingCat.of k) := by
    let x : Spec (.of k) := default
    refine ⟨Scheme.Spec.residueFieldIso (.of k) default ≪≫ ?_⟩
    exact
      ((Ideal.algEquivResidueFieldOfField (k := k) x.asIdeal).toRingEquiv.toCommRingCatIso).symm
  exact ⟨asIso sbar ≪≫ hbase⟩

/-- **Sorry-free, scheme-general.** For a scheme locally of finite type over a
field, the cotangent space at any point is finite-dimensional over the residue
field — the local-Noetherianity input dimension arguments need. -/
theorem finiteDimensional_cotangentSpace_of_locallyOfFiniteType {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] (x : X.left) :
    FiniteDimensional (IsLocalRing.ResidueField (X.left.presheaf.stalk x))
      (IsLocalRing.CotangentSpace (X.left.presheaf.stalk x)) := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  infer_instance

/-- **Pointed dual-number points of `X` at `e`, over `Spec k`.** The
`k[ε]`-valued points of `X` lying over the closed point of `Spec k[ε]` and
landing at `e`; the functor-of-points model of the Zariski tangent space at
`e`. A named restatement of the anonymous subtype
`overDualNumberSectionEquivCotangentSpaceDual` targets, kept for readability
at the call sites below. -/
def pointedDualNumberPoints {k : Type u} [Field k] (X : Over (Spec (.of k)))
    (e : Spec (.of k) ⟶ X.left) :=
  {g : Spec (CommRingCat.of (DualNumber k)) ⟶ X.left //
      g ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
        ∧ g.base (IsLocalRing.closedPoint (DualNumber k)) = e.base default}

/-- **Axiom-clean.** The `k`-rational identity-section point of `Pic⁰_{C/k}`:
the lift of the Picard scheme's identity section `MonObj.one` through the open
immersion `Pic⁰_{C/k} ↪ Pic_{C/k}`, i.e. the sibling's
`GroupScheme.identityComponentSection` specialised to `G = PicScheme C`
(transported along the definitional identification
`Pic0Scheme C = GroupScheme.IdentityComponent (PicScheme C)`). This is the
`e`-witness of the Σ'-bundle in `tangentSpaceIso`. -/
noncomputable def identitySection {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Spec (.of k) ⟶ (Pic0Scheme C).left :=
  GroupScheme.identityComponentSection (PicScheme C)

/-- **Axiom-clean.** The identity-section point is a genuine section of the
structural morphism: `identitySection C ≫ (Pic0Scheme C).hom = 𝟙 (Spec k)`.
Transport of the sibling's `identityComponentSection_isSection`. -/
theorem identitySection_isSection {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    identitySection C ≫ (Pic0Scheme C).hom = 𝟙 (Spec (.of k)) :=
  GroupScheme.identityComponentSection_isSection (PicScheme C)

/-- **Axiom-clean.** The Stacks 0B28 dictionary at the identity point: pointed
dual-number points of `Pic⁰_{C/k}` at `e` biject with `κ(e)`-linear functionals
on the cotangent space `m_e/m_e²`. Direct specialisation of
`overDualNumberSectionEquivCotangentSpaceDual`
(`Picard/TangentSpaceIdentitySection.lean`) to `e = identitySection C`; the two
points `(identitySection C).base default` and
`(identitySection C).base (IsLocalRing.closedPoint k)` are bridged by
`Subsingleton (Spec k)`, the same idiom `tangentSpaceCotangentDual` uses. -/
theorem pointedDualNumberPoints_equiv_cotangentSpaceDual {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Nonempty (pointedDualNumberPoints (Pic0Scheme C) (identitySection C) ≃
      Module.Dual
        (IsLocalRing.ResidueField
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
        (IsLocalRing.CotangentSpace
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))) := by
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  exact ⟨overDualNumberSectionEquivCotangentSpaceDual (Pic0Scheme C)
    (identitySection_isSection C) (congrArg _ (Subsingleton.elim _ _))⟩

/-- **Axiom-clean.** The tangent space of `Pic⁰_{C/k}` at the identity is the
tangent space of `Pic_{C/k}` there (leg-(1) connector of the Kleiman §5
Thm.~5.11 dimension identity): along the clopen inclusion
`ι : Pic⁰_{C/k} ↪ Pic_{C/k}` (an open immersion by the sibling's
`IdentityComponent.isOpenSubgroupScheme`), composition identifies the pointed
dual-number points at the identity section with those of the ambient Picard
scheme at its image — `Spec k[ε]` is a one-point scheme, so dual-number
points landing in the open subscheme lift uniquely
(`pointedDualNumberPointsEquivOfOpenImmersion`,
`Picard/Pic0TangentSpace.lean`). This lets the representability leg compute
`T_e Pic⁰` on `Pic_{C/k}` itself, where `picSharp`-representability applies. -/
theorem pointedDualNumberPoints_equiv_picScheme {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Nonempty (Σ' (ι : Pic0Scheme C ⟶ PicScheme C),
      pointedDualNumberPoints (Pic0Scheme C) (identitySection C) ≃
        pointedDualNumberPoints (PicScheme C) (identitySection C ≫ ι.left)) := by
  obtain ⟨f, hopen, -⟩ :=
    GroupScheme.IdentityComponent.isOpenSubgroupScheme (PicScheme C)
  haveI := hopen
  exact ⟨⟨f, pointedDualNumberPointsEquivOfOpenImmersion f (identitySection C)⟩⟩

/-- **Axiom-clean (through the `HasPicScheme` gate).** The Kleiman §5
Thm.~5.11 **representability leg, applied**: the pointed dual-number points
of `Pic⁰_{C/k}` at the identity section — the Zariski tangent space
`T₀ Pic⁰_{C/k}` in functor-of-points form — biject with the **kernel** of the
restriction homomorphism

```
Pic^♯_{C/k}(Spec k[ε]) →+ Pic^♯_{C/k}(Spec k)
```

of the relative Picard presheaf along the `ε ↦ 0` point. Composite of

1. the open-immersion transport `T₀ Pic⁰ ≃ T₀ Pic` along the clopen inclusion
   `Pic⁰_{C/k} ↪ Pic_{C/k}` (`pointedDualNumberPointsEquivOfOpenImmersion`,
   `Picard/Pic0TangentSpace.lean`), and
2. the represented-functor kernel description
   (`pointedDualNumberPointsEquivAddKernel`,
   `Picard/Pic0DualNumberCocycle.lean`) at the FGA representability witness
   `PicScheme.representable C : picSharp C ≅ (T ⟶ Pic_{C/k})` — note
   `picSharp C` is *by definition* the set-valued shadow of the group-valued
   `PicSharp.relPresheaf C`, so the kernel of the group-valued restriction is
   meaningful.

⚠ This is a bijection of **sets** — it does not by itself transport `finrank`
(a bare `Equiv` does not determine dimension over an infinite field). The
`k`-linearity bookkeeping (Mumford's `a · [L_ε] := (ε ↦ aε)^* [L_ε]` module
structure, `overDualNumberScale` of `Picard/Pic0DualNumberCocycle.lean`)
remains with `finrank_cotangentSpace_eq_finrank_hModuleOne` below. -/
theorem pointedDualNumberPoints_equiv_relPicKernel {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Nonempty (pointedDualNumberPoints (Pic0Scheme C) (identitySection C) ≃
      {a : (PicSharp.relPresheaf C).obj (Opposite.op (overDualNumber k)) //
        ((PicSharp.relPresheaf C).map (overDualNumberZero k).op).hom a = 0}) := by
  obtain ⟨f, hopen, -⟩ :=
    GroupScheme.IdentityComponent.isOpenSubgroupScheme (PicScheme C)
  haveI := hopen
  have he' : (identitySection C ≫ f.left) ≫ (PicScheme C).hom
      = 𝟙 (Spec (.of k)) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t => identitySection C ≫ t) (Over.w f)).trans
        (identitySection_isSection C))
  exact ⟨(pointedDualNumberPointsEquivOfOpenImmersion f (identitySection C)).trans
    (pointedDualNumberPointsEquivAddKernel (PicScheme C)
      (PicSharp.relPresheaf C) (PicScheme.representable C) he')⟩

/-- **Axiom-clean (through the `HasPicScheme` gate).** The two proved halves
of Kleiman §5 Thm.~5.11 composed: the `κ(e)`-linear dual of the cotangent
space `m_e/m_e²` at the identity of `Pic⁰_{C/k}` bijects with the kernel of
`Pic^♯_{C/k}(Spec k[ε]) →+ Pic^♯_{C/k}(Spec k)` — the Stacks 0B28 dictionary
(`pointedDualNumberPoints_equiv_cotangentSpaceDual`) chained through the
tangent space with the representability leg
(`pointedDualNumberPoints_equiv_relPicKernel`). Same linearity caveat as the
latter: this is a bijection of sets. -/
theorem cotangentSpaceDual_equiv_relPicKernel {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Nonempty (Module.Dual
        (IsLocalRing.ResidueField
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
        (IsLocalRing.CotangentSpace
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
      ≃ {a : (PicSharp.relPresheaf C).obj (Opposite.op (overDualNumber k)) //
          ((PicSharp.relPresheaf C).map (overDualNumberZero k).op).hom a = 0}) := by
  obtain ⟨φ⟩ := pointedDualNumberPoints_equiv_cotangentSpaceDual C
  obtain ⟨ψ⟩ := pointedDualNumberPoints_equiv_relPicKernel C
  exact ⟨φ.symm.trans ψ⟩

/-- **Sorry-free source (carries the FGA existential's `sorryAx`).** The Picard
scheme `Pic_{C/k}` is separated over `k`. Kleiman delivers this as part of the
§4 representability package ("Then `Pic_{X/k}` is separated, ..."); its home is
the strengthened `HasPicScheme` existential in `FGAPicRepresentability.lean`,
which now bundles `IsSeparated X.hom` as its third conjunct; this helper is the
direct `Classical.choose_spec` extraction (same content as the global
`PicScheme.isSeparated` instance) consumed by the `isSeparated` assembly. -/
theorem picScheme_isSeparated {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] :
    IsSeparated (PicScheme C).hom :=
  (HasPicScheme.has_pic_scheme (C := C)).choose_spec.2.2

/-- **Axiom-clean.** Separatedness of `Pic⁰_{C/k}` over `k`: the structural
morphism factors as the clopen inclusion `Pic⁰_{C/k} ↪ Pic_{C/k}` (an open
immersion by the sibling's axiom-clean
`IdentityComponent.isOpenSubgroupScheme`, hence a monomorphism, hence
separated) followed by the separated `(PicScheme C).hom`
(`picScheme_isSeparated`); separatedness is stable under composition. This is
the `IsSeparated` conjunct of the pinned `proper`. -/
theorem isSeparated {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    IsSeparated (Pic0Scheme C).hom := by
  haveI : IsSeparated (PicScheme C).hom := picScheme_isSeparated C
  obtain ⟨⟨f, hopen, -⟩⟩ :=
    GroupScheme.IdentityComponent.isOpenSubgroupScheme (PicScheme C)
  haveI := hopen
  change IsSeparated (GroupScheme.IdentityComponent (PicScheme C)).hom
  rw [← Over.w f]
  infer_instance

/-- **Axiom-clean.** `Pic⁰_{C/k}` is locally of finite type over `k`: the first
(sorry-free) conjunct of the sibling's
`IdentityComponent.isFiniteTypeGeometricallyIrreducible`, transported along the
definitional identification. The `LocallyOfFiniteType` conjunct of the pinned
`proper`. -/
theorem locallyOfFiniteType {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    LocallyOfFiniteType (Pic0Scheme C).hom :=
  (GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible
    (PicScheme C)).1

/-- **Closed.** `Pic⁰_{C/k}` is quasi-compact over `k`: the second conjunct of
the sibling's `IdentityComponent.isFiniteTypeGeometricallyIrreducible` (Kleiman
§5 Lem.~`lem:agps`~(3): `α(U × U) = G⁰` is the image of the affine, hence
quasi-compact, `U × U`), fully proved since run 0009. Not needed for the
`proper` assembly (Mathlib's `IsProper` derives quasi-compactness from
universal closedness) but recorded for the blueprint's finite-type chain. -/
theorem quasiCompact {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    QuasiCompact (Pic0Scheme C).hom :=
  (GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible
    (PicScheme C)).2.1

/-- **Sorry-free.** Universal closedness of `Pic⁰_{C/k}` descends from its base
change to the algebraic closure `Spec k̄ → Spec k`. That base-change map is
faithfully flat and quasi-compact (a field extension `k → k̄` is injective and
flat, so `Spec.map` of it is surjective and flat; being a map of affines it is
quasi-compact), and `UniversallyClosed` is fpqc-local on the base (Stacks 02KS;
EGA IV₂ 2.6.4). The pinned Mathlib packages exactly this descent as the
`@[stacks 02KS]` instance
`descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`
(`Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean`), so the closure is a
one-line `of_pullback_snd_of_descendsAlong` application — the same
`MorphismProperty` descent pattern `smooth_of_grpObj` uses, with the three
`Surjective`/`Flat`/`QuasiCompact` facts about `Spec.map (algebraMap k k̄)`
supplied by `inferInstance`. -/
theorem universallyClosed_of_baseChange {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (h : UniversallyClosed (pullback.snd (Pic0Scheme C).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) :
    UniversallyClosed (Pic0Scheme C).hom := by
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h

/-- **Dual-number points of `Pic⁰_{C/k}` at the identity are the cotangent
dual** (Kleiman §5 Thm.~`thm:tgtsp`, LHS). Given the `k`-group-scheme
structure on `Pic0Scheme C` (supplied by `Pic0.grpObj`), the identity section
`e : Spec k ⟶ Pic⁰_{C/k}` hits a `k`-rational point, and the over-`Spec k`
dual-number points of `Pic⁰_{C/k}` at `e` — the Zariski tangent space
`T₀ Pic⁰_{C/k}` in its functor-of-points form — form the `κ(e)`-linear dual
of the cotangent space `m_e/m_e²`.

This is the geometric half of `tangentSpaceIso`; composing with the
`H¹(C, 𝒪_C)`-identification of `Dual (m_e/m_e²)` (gated on the `AJC.picrep`
representability cone) closes `thm:pic0_tangent_space_iso`. -/
theorem tangentSpaceCotangentDual {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Nonempty (Σ' (e : Spec (.of k) ⟶ (Pic0Scheme C).left),
      (e ≫ (Pic0Scheme C).hom = 𝟙 (Spec (.of k))) ×'
      ({g : Spec (CommRingCat.of (DualNumber k)) ⟶ (Pic0Scheme C).left //
          g ≫ (Pic0Scheme C).hom
              = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
            ∧ g.base (IsLocalRing.closedPoint (DualNumber k)) = e.base default} ≃
        Module.Dual
          (IsLocalRing.ResidueField ((Pic0Scheme C).left.presheaf.stalk (e.base default)))
          (IsLocalRing.CotangentSpace
            ((Pic0Scheme C).left.presheaf.stalk (e.base default))))) := by
  obtain ⟨i⟩ := grpObj C
  letI := i
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  exact ⟨GroupScheme.identitySection (Pic0Scheme C),
    GroupScheme.identitySection_comp (Pic0Scheme C),
    overDualNumberSectionEquivCotangentSpaceDual (Pic0Scheme C)
      (GroupScheme.identitySection_comp (Pic0Scheme C))
      (congrArg _ (Subsingleton.elim _ _))⟩

/-- **Sorry-free, fully general: a dimension count across a change of scalar
ring.** (Run 0067.) If `j : M ≃+ M₁` is additive, `i : R → R'` is a bijection
of the scalar rings, and `j` intertwines the two scalar actions along `i`, then
`M` and `M₁` have the same `finrank` over their respective rings.

This is the `finrank` form of mathlib's `rank_eq_of_equiv_equiv`
(`Mathlib/LinearAlgebra/Dimension/Basic.lean`), obtained by unfolding
`Module.finrank` as `toNat` of `Module.rank`. It is the right tool for the
Kleiman §5 Thm 5.11 dimension count, which compares a `κ(e)`-dimension with a
`k`-dimension across the residue-field isomorphism `κ(e) ≃+* k`: `i` need only
be a *bijection*, not a ring homomorphism, and the module structures live over
genuinely different rings, so neither `LinearEquiv.finrank_eq` nor a
`restrictScalars` argument applies. -/
theorem finrank_eq_of_addEquiv_of_bijective_smul
    {R : Type*} {R' : Type*} {M M₁ : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring R'] [AddCommMonoid M₁] [Module R' M₁]
    (i : R → R') (j : M ≃+ M₁) (hi : Function.Bijective i)
    (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    Module.finrank R M = Module.finrank R' M₁ := by
  unfold Module.finrank
  rw [rank_eq_of_equiv_equiv i j hi hc]

/-- **The one remaining input to the Kleiman §5 Thm 5.11 dimension identity**
(run 0067): the geometric cocycle comparison, packaged with exactly the
scalar-compatibility data a dimension count needs and no more.

The statement asks for a bijection `i` of scalars `κ(e) → k`, an additive
equivalence `j` from the tangent space `Dual_{κ(e)}(m_e/m_e²)` at the identity
of `Pic⁰_{C/k}` to the two-chart Čech cokernel `Ȟ¹(S, 𝒪_C)`, and the
intertwining law `j (r • x) = i r • j x`. Given those,
`finrank_cotangentSpaceDual_eq_finrank_h1Cok` follows outright by
`finrank_eq_of_addEquiv_of_bijective_smul` — so the former "linearity
bookkeeping" leg (step 2 of the old reduction) is discharged and this is the
whole residue.

Why this is the honest packaging rather than a weakening: a bare `Equiv` does
*not* determine `finrank`, and the older reduction knew that, which is why it
listed semilinearity as a separate obligation. Bundling the equivalence with its
compatibility square is precisely the strength required — no more, since `i` is
asked only to be bijective, and no less, since dropping `hc` would make the
statement insufficient.

WHAT IS ALREADY AVAILABLE towards it, none of which needs redoing:

* the set-level chain
  `Dual_{κ(e)}(m_e/m_e²) ≃ T₀ Pic⁰ ≃ T₀ Pic ≃ ker(Pic^♯(k[ε]) → Pic^♯(k))`
  — `cotangentSpaceDual_equiv_relPicKernel` above;
* the Mumford `ε ↦ aε` scaling on that kernel with its monoid-action laws
  (`relPicKernelSMul`, `Picard/Pic0DualNumberCocycle.lean`), which is the
  source of the `•` on the left-hand side;
* the two-chart Čech unit-cocycle engine
  `Γ(U₁ ⊓ U₂) ⧸ (Γ(U₁) + Γ(U₂)) ≃+ ker(Ȟ¹ˣ(B[ε]) → Ȟ¹ˣ(B))`
  (`DualNumber.truncExpCechKernelAddEquiv`) together with
  `AffineCoverMVSquare.h1CokAddEquivTruncExpCechKernel` above, which is the
  additive equivalence on the Čech side, and
  `DualNumber.unitsScale_mk_truncExpUnit`, which is exactly the `t • b`
  equivariance `hc` needs on that side;
* the scalar bijection: `residueFieldIso_of_section_over_field` gives
  `κ(e) ≅ k` as rings at a `k`-rational section point, so `i` is available and
  only has to be threaded.

WHAT IS GENUINELY OPEN is the geometric middle, whose three clauses are

  (i) an invertible sheaf on `C ×_k Spec k[ε]` trivial along `ε ↦ 0` is trivial
      on the two base-changed charts of `S`;
 (ii) `Γ(V × Spec k[ε], 𝒪) ≅ Γ(V, 𝒪)[ε]` for affine `V`;
(iii) under those identifications a kernel element goes to its transition unit.

CLAUSES (i) AND (ii) ARE NO LONGER OPEN (run 0067):

* (i) is `DualNumber.free_of_cyclic_mod_eps`
  (`Picard/DualNumberChartTriviality.lean`): on an affine chart `Spec A` the
  base change is `Spec A[ε]`, the augmentation ideal is square-zero
  (`DualNumber.augIdeal_mul_self_eq_bot`) hence nilpotent, and an invertible
  module over a nilpotent thickening which is cyclic modulo the ideal is free
  (`Module.Invertible.free_of_nilpotent_of_exists_sub_smul_mem`,
  `Picard/NilpotentThickeningFree.lean`). No finiteness of the sections is
  assumed — affine charts of a curve do not have finite-dimensional section
  spaces over `k`, so a version requiring that would be unusable here.
* (ii) is `DualNumber.baseChangeAlgEquiv` (`Picard/Pic0DualNumberCocycle.lean`),
  which was already available.

**WHAT CLAUSE (iii) ACTUALLY NEEDS, measured run 0067 r6 — and it is not a port.**
Three earlier sessions recorded the sibling project's two-chart Čech machinery
(`Tangent/TwoChartCechPic.lean`, `TwoChartNormalize.lean`,
`TwoChartRepresentable.lean` in `Algebraic-Jacobian-Challenge-Rebuild`) as the live
route here. It cannot close this clause, on either side of the workspace, and the
obstruction is the **carrier** rather than the price.

The sibling's `Scheme.CechPic` is a *self-contained definitional* Picard group — a
quotient of unit Čech cocycles over pointed covers. Its only bridge to invertible
*sheaves* is `Scheme.cechPicEquivPic`, and that carries `[IsAffine X]` irremovably:
the proof needs a trivializing basic open at every point together with
`Module.Invertible.span_tensor_free_eq_top` over `Γ(X, ⊤)`. No non-affine comparison
exists in either project, and none exists in mathlib, which has no Picard group of a
*scheme* at all (`CommRing.Pic` is ring-level).

But this clause compares a kernel of `PicSharp.relPresheaf` — a setoid quotient of
`LineBundle.OnProduct`, i.e. honest invertible sheaves — against a Čech `Ȟ¹` on
`C ×_k Spec k[ε]`, a **proper curve**. That is not affine, and it is not affine
precisely *because* the `ε`-kernel is nonzero; on an affine with trivial Picard group
there would be nothing to compute. So the one hypothesis the dictionary needs is the
one the problem structurally denies. Porting the carrier does not help: at the end of
17k sorry-free lines one holds a class in `X.CechPic` with no theorem relating it to
`LineBundle.OnProduct` at a non-affine `X`.

So the genuinely missing statement — absent from both projects and from mathlib — is

```
Ȟ¹(X, 𝒪ˣ) ≅ {isomorphism classes of invertible sheaves on X}   for non-affine X
```

which is new mathematics for this development rather than a port. Full measurement,
including the closure counts priced both ways, is inbox I-0689.

So the residue is clause (iii) alone: the cocycle-level identification. A
cross-project note from the AJCR side (inbox I-0495, 2026-07-28) confirms that
this leg does *not* require Hilbert 90 or any henselian cover-splitting brick:
after the truncated-exponential linearisation the descent condition is additive,
and for the square-zero thickening `k[ε] → k` mathlib's
`Algebra.FormallyEtale.comp_bijective` suffices. The square-zero-ness that note
relies on is exactly `DualNumber.augIdeal_mul_self_eq_bot`, now a theorem. The
sibling project restated its own T3/T4 target as this same comparison after
porting clauses (i) and (ii), so clause (iii) is the *joint* residue of both
developments and whichever side proves it hands it to the other.

STATING CLAUSE (iii) — the prerequisite, and the trap in it. Clause (iii) has to be
an *additive* equivalence out of the dual-number kernel: a bare `Equiv` does not
transport `finrank`, which is exactly the error the sibling project retracted on
this lane (inbox I-0495, 2026-07-28). The representability leg
(`pointedDualNumberPointsEquivAddKernel`) delivers that kernel as the *subtype*
`{a // (map …).hom a = 0}`, and an `≃+` stated against the subtype **fails to
elaborate** — `failed to synthesize Add {a // …}` — because instance search does
not see through the subtype spelling to the group structure.

The fix is not new mathematics, only the right spelling: `relPicDualKernel` above
names the same thing as an `AddSubgroup` (`rfl`-equal to the subtype, see
`relPicDualKernel_eq_subtype`), and against that the additive statement elaborates.
So clause (iii) is stateable as
`relPicDualKernel C ≃+ S.H1Cok (Scheme.toModuleKSheaf C)` plus the Mumford-scaling
intertwining, with the Čech side already additive
(`AffineCoverMVSquare.h1CokAddEquivTruncExpCechKernel`).

What is *not* yet done is the mathematics: exhibiting that equivalence, i.e. sending
a kernel class to its transition unit. That is why clause (iii) remains inside this
statement rather than sitting beside it as a second `sorry` — splitting it would add
a declaration without reducing the open content, and the reduction only becomes real
once the map exists. -/
theorem semilinearComparison_cotangentSpaceDual_h1Cok {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (S : C.left.AffineCoverMVSquare) :
    ∃ (i : (IsLocalRing.ResidueField
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default))) → k)
      (j : (Module.Dual
              (IsLocalRing.ResidueField
                ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
              (IsLocalRing.CotangentSpace
                ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default))))
            ≃+ S.H1Cok (Scheme.toModuleKSheaf C)),
      Function.Bijective i ∧ ∀ r x, j (r • x) = i r • j x :=
  sorry

/-- **The reduced Kleiman §5 Thm 5.11 core** (wave-5 W12-cocycle shrink; the
single remaining `sorry` of the tangent-space keystone `tangentSpaceIso`):
the `κ(e)`-dimension of the **dual** of the cotangent space `m_e/m_e²` at the
identity of `Pic⁰_{C/k}` — i.e. of the Zariski tangent space `T₀ Pic⁰_{C/k}`
in its linear-dual form, the side the Stacks 0B28 dictionary lands on —
equals the `k`-dimension of the concrete two-chart Čech cokernel
`Ȟ¹ = Γ(U₁ ⊓ U₂, 𝒪_C) ⧸ range(sectionDiff)` of **any** 2-affine cover `S`
of the curve `C`.

The statement is TRUE at this generality: the LHS is `dim T₀ Pic⁰ = g(C)`
(Kleiman §5 Thm 5.11) and the RHS is `dim_k Ȟ¹(S, 𝒪_C) = dim_k H¹(C, 𝒪_C)
= g(C)` for *every* 2-affine cover (`AffineCoverMVSquare.hModuleOneEquivH1Cok_curve`,
`RiemannRoch/Adelic/GenusUnconditional.lean`); no choice of cover is
privileged. The pinned dimension identity
`finrank_cotangentSpace_eq_finrank_hModuleOne` below is PROVED from this
statement (dual dimension + the gate-free `H¹ ≃ Ȟ¹` comparison), so this is
now the smallest named open statement of the W12 lane.

STATE OF THE REDUCTION (what is PROVED around this sorry):

* set-level, both directions:
  `Dual_{κ(e)}(m_e/m_e²) ≃ T₀ Pic⁰ ≃ T₀ Pic ≃
     ker(Pic^♯(Spec k[ε]) →+ Pic^♯(Spec k))`
  — `cotangentSpaceDual_equiv_relPicKernel` above (Stacks 0B28 dictionary +
  open-immersion transport + FGA representability leg);
* the Mumford `ε ↦ aε` scaling substrate on that kernel, with its
  multiplicative-monoid action laws (`overDualNumberScale`,
  `relPicKernelSMul`, `Picard/Pic0DualNumberCocycle.lean`);
* the truncated-exponential unit splitting `(R[ε])ˣ ≃* Rˣ × (R, +)` with its
  naturality (`Picard/DualNumberUnits.lean`);
* the **two-chart Čech unit-cocycle engine** (wave 5,
  `Picard/Pic0DualNumberCocycle.lean` §6): for the section rings of any
  2-affine cover, `Γ(U₁ ⊓ U₂) ⧸ (Γ(U₁) + Γ(U₂)) ≃+ ker(Ȟ¹ˣ(B[ε]) → Ȟ¹ˣ(B))`
  via the truncated exponential (`DualNumber.truncExpCechKernelAddEquiv`),
  with the Mumford `ε ↦ tε` scaling acting as `b ↦ t·b`
  (`DualNumber.unitsScale_mk_truncExpUnit`) — the whole algebra layer of
  the cocycle leg;
* the Čech target `H¹(C, 𝒪_C) ≃ₗ[k] H1Cok` on any 2-affine cover
  (`AffineCoverMVSquare.hModuleOneEquivH1Cok_curve`,
  `RiemannRoch/Adelic/GenusUnconditional.lean`) and finite-dimensionality of
  both sides (`finiteDimensional_cotangentSpace_of_locallyOfFiniteType`,
  `instModuleFiniteHModuleOne`).

REMAINING MATHEMATICAL CONTENT (Kleiman §5, proof of Thm 5.11):

1. **Geometric cocycle substrate**: an invertible sheaf on
   `C ×_k Spec k[ε]`, restricted trivial along `ε ↦ 0`, is trivial on the
   two base-changed charts of the 2-affine cover `S` (nilpotent thickening
   does not change the underlying space; units of the chart rings lift along
   the square-zero extension), and the chart sections identify as
   `Γ(V × Spec k[ε], 𝒪) ≅ Γ(V, 𝒪)[ε]` for affine `V`; the class of a kernel
   element is then its transition unit in `(Γ(U₁ ⊓ U₂, 𝒪_C)[ε])ˣ` up to the
   thickened coboundaries, which the (landed) unit-cocycle engine converts
   to `H1Cok`, additively and `k`-equivariantly for the `ε ↦ aε` action.
2. **Linearity bookkeeping**: the composite of
   `cotangentSpaceDual_equiv_relPicKernel` with the leg-1 identification is
   `k`-semilinear along `κ(e) ≃+* k`
   (`residueFieldIso_of_section_over_field`), where the kernel carries the
   Mumford structure (`relPicKernelSMul`); a dimension count then gives this
   statement, transporting bases along `κ(e) ≃+* k` as in
   `Module.nonempty_addEquiv_of_finrank_eq_of_ringEquiv`.

Neither step weakens the pinned `tangentSpaceIso`; both are multi-session.

REDUCED (run 0067) to exactly the semilinear comparison, via
`finrank_eq_of_addEquiv_of_bijective_smul` below: see
`semilinearComparison_cotangentSpaceDual_h1Cok`. Step 2 above — the
"linearity bookkeeping" and the dimension count — is now *discharged*, so the
remaining content is step 1 alone, packaged as the additive equivalence
together with its scalar-compatibility square. -/
theorem finrank_cotangentSpaceDual_eq_finrank_h1Cok {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (S : C.left.AffineCoverMVSquare) :
    Module.finrank
        (IsLocalRing.ResidueField
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
        (Module.Dual
          (IsLocalRing.ResidueField
            ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
          (IsLocalRing.CotangentSpace
            ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default))))
      = Module.finrank k (S.H1Cok (Scheme.toModuleKSheaf C)) := by
  obtain ⟨i, j, hi, hc⟩ := semilinearComparison_cotangentSpaceDual_h1Cok C S
  exact finrank_eq_of_addEquiv_of_bijective_smul i j hi hc

/-- **The Kleiman §5 Thm 5.11 dimension identity**
`dim_{κ(e)} m_e/m_e² = dim_k H¹(C, 𝒪_C)` at the identity section of
`Pic⁰_{C/k}` — the named sub-lemma the tangent-space keystone
`tangentSpaceIso` consumes (wave-4 W12-finrank reduction).

PROVED (wave-5 W12-cocycle) from the reduced core
`finrank_cotangentSpaceDual_eq_finrank_h1Cok` above by discharging the two
outer legs of the dimension chain:

* `dim_{κ(e)} m_e/m_e² = dim_{κ(e)} Dual(m_e/m_e²)` — reflexivity of finite-
  dimensional duality (`Subspace.dual_finrank_eq`; finite-dimensionality from
  `finiteDimensional_cotangentSpace_of_locallyOfFiniteType` via
  `Pic0.locallyOfFiniteType`);
* `dim_k Ȟ¹(S, 𝒪_C) = dim_k H¹(C, 𝒪_C)` — the gate-free Mayer–Vietoris
  comparison `AffineCoverMVSquare.hModuleOneEquivH1Cok_curve`
  (`RiemannRoch/Adelic/GenusUnconditional.lean`), at the 2-affine cover
  supplied by the genus lane's
  `Adelic.exists_affineCoverMVSquare_module_finite_H1Cok` (pullback of the
  standard ℙ¹ charts along a finite map, `RiemannRoch/Adelic/FinitenessP1.lean`). -/
theorem finrank_cotangentSpace_eq_finrank_hModuleOne {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Module.finrank
        (IsLocalRing.ResidueField
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
        (IsLocalRing.CotangentSpace
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
      = Module.finrank k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) := by
  haveI : LocallyOfFiniteType (Pic0Scheme C).hom := locallyOfFiniteType C
  haveI := finiteDimensional_cotangentSpace_of_locallyOfFiniteType (Pic0Scheme C)
    ((identitySection C).base default)
  obtain ⟨S, -⟩ := Adelic.exists_affineCoverMVSquare_module_finite_H1Cok C
  calc
    Module.finrank
        (IsLocalRing.ResidueField
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
        (IsLocalRing.CotangentSpace
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
      = Module.finrank
          (IsLocalRing.ResidueField
            ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
          (Module.Dual
            (IsLocalRing.ResidueField
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
            (IsLocalRing.CotangentSpace
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))) :=
        Subspace.dual_finrank_eq.symm
    _ = Module.finrank k (S.H1Cok (Scheme.toModuleKSheaf C)) :=
        finrank_cotangentSpaceDual_eq_finrank_h1Cok C S
    _ = Module.finrank k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) :=
        (LinearEquiv.finrank_eq (S.hModuleOneEquivH1Cok_curve)).symm

/-- **Tangent space at the identity: `T₀ Pic⁰_{C/k} ≅ H¹(C, 𝒪_C)`.**

The Kleiman §5 Thm.~`thm:tgtsp` tangent-space isomorphism. For a smooth
proper geometrically integral curve `C/k`, the Zariski tangent space at the
identity of `Pic⁰_{C/k}` is canonically isomorphic to the first sheaf
cohomology `H¹(C, 𝒪_C)`.

In Lean (skeleton form): we bundle existentially over a `k`-rational
identity-section point `e : Spec k ⟶ (Pic0Scheme C).left` and a `k`-module
structure on the cotangent space `m_e/m_e²` (the natural `k`-module structure
arising from the `k`-algebra structure on the stalk at a `k`-rational point;
for the file-skeleton this instance is supplied via Σ' to avoid hard-coding
a global instance prematurely). The substantive content is an `AddEquiv`
between the cotangent space and the project's `H¹(C, 𝒪_C)` module
`Scheme.HModule k (Scheme.toModuleKSheaf C) 1`.

A k-LinearEquiv refinement (iter-194+) replaces the `AddEquiv` once the
`k`-module structure on the cotangent space is consistently threaded through
downstream consumers; the underlying additive group structure is enough for
the dimension corollary `dim_k T₀ Pic⁰ = dim_k H¹ = g(C)`.

REDUCED (run 0015, W12-tangent): via the proved reduction
`nonempty_cotangentSpaceAddEquiv_of_finrank_eq`
(`Picard/Pic0TangentSpace.lean`, dimension-count transport of bases along
`κ(e) ≃+* k`; inputs: `Pic0.locallyOfFiniteType`, `identitySection_isSection`,
and the genus-lane finiteness `instModuleFiniteHModuleOne` of
`RiemannRoch/Adelic/GenusUnconditional.lean`), the remaining `sorry` is
exactly the Kleiman §5 Thm 5.11 **dimension identity**
`dim_{κ(e)} m_e/m_e² = dim_k H¹(C, 𝒪_C)` at the identity section. Its
intended proof: (1) `dim_{κ(e)} m_e/m_e² = dim_{κ(e)} Dual(m_e/m_e²)` and the
dual is the pointed dual-number points (`tangentSpaceCotangentDual`,
`pointedDualNumberPoints_equiv_cotangentSpaceDual`); (2) representability
identifies those points `κ(e)`-linearly with
`ker(Pic(C ×_k Spec k[ε]) / π^* → Pic(C))`; (3) the truncated-exponential
splitting (`Picard/DualNumberUnits.lean`) computes that kernel on a 2-affine
cover as the Čech carrier `AffineCoverMVSquare.H1Cok`, which is `H¹(C, 𝒪_C)`
by `AffineCoverMVSquare.hModuleOneEquivH1Cok_curve`
(`RiemannRoch/Adelic/GenusUnconditional.lean`). Steps (2)-(3) must be carried
out with enough (semi)linearity to preserve dimension — a bare `Equiv` does
not determine `finrank`. -/
theorem tangentSpaceIso {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Nonempty (Σ' (e : Spec (.of k) ⟶ (Pic0Scheme C).left),
      IsLocalRing.CotangentSpace ((Pic0Scheme C).left.presheaf.stalk (e.base default))
        ≃+ Scheme.HModule k (Scheme.toModuleKSheaf C) 1) := by
  haveI : LocallyOfFiniteType (Pic0Scheme C).hom := locallyOfFiniteType C
  refine (nonempty_cotangentSpaceAddEquiv_of_finrank_eq (Pic0Scheme C)
      (identitySection_isSection C)
      (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) ?_).map
    fun φ => ⟨identitySection C, φ⟩
  -- Kleiman §5 Thm 5.11 dimension identity `dim_{κ(e)} m_e/m_e² = dim_k H¹(C, 𝒪_C)`:
  -- the named sub-lemma above (its docstring records the reduction state).
  exact finrank_cotangentSpace_eq_finrank_hModuleOne C

/-- **Smoothness of `Pic⁰_{C/k}` from geometric reducedness — the whole
translation argument, discharged.** (Run 0067.)

Mathlib's `smooth_of_grpObj` (`Mathlib/AlgebraicGeometry/Group/Smooth.lean`)
already contains the entire geometric content that the older `smooth`
docstring described as remaining work: for a group scheme over an *arbitrary*
field which is locally of finite type and geometrically reduced, smoothness at
the identity is propagated everywhere by the translation isomorphisms
`GrpObj.mulRight`, and the descent to a non-closed base field is done by
`MorphismProperty.of_pullback_snd_of_descendsAlong` along `Spec k̄ → Spec k`.

So nothing about translation, and nothing about the tangent space, is owed
here. Both of `smooth_of_grpObj`'s structural hypotheses are landed in this
development:

* `[LocallyOfFiniteType (Pic0Scheme C).hom]` — `Pic0.locallyOfFiniteType`
  (the first conjunct of the sibling's
  `IdentityComponent.isFiniteTypeGeometricallyIrreducible`);
* `[GrpObj (Over.mk (Pic0Scheme C).hom)]` — `Pic0.grpObj`, keyed at the
  `Over.mk` spelling. `Over.mk X.hom` is definitionally `X` by structure eta
  for `Comma`, so the `letI` ascription is pure defeq and no transport lemma is
  needed; instance *search* alone will not unfold `Over.mk`, which is why the
  ascription is written out.

What remains is therefore exactly `GeometricallyReduced (Pic0Scheme C).hom`
and nothing else — see `geometricallyReduced` below for why that single residue
is a genuine theorem rather than a synthesis step.

"Exactly" is MEASURED, not estimated (run 0067). At a probe site with the
`HasPicScheme` gate *assumed* rather than synthesised (so the gate cannot
contribute) and `GeometricallyReduced` supplied as a hypothesis, this theorem's
conclusion reports `[propext, Classical.choice, Quot.sound]` — axiom-clean —
while the control `Pic0.smooth` at the same binders reports `sorryAx`. So
supplying geometric reducedness discharges smoothness outright, with no residual
leak elsewhere in the assembly, and the control confirms the probe would have
detected one. Same probe/control technique as
`scripts/axiom-frontier.lean` §0b. -/
theorem smooth_of_geometricallyReduced {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (h : GeometricallyReduced (Pic0Scheme C).hom) :
    Smooth (Pic0Scheme C).hom := by
  haveI : LocallyOfFiniteType (Pic0Scheme C).hom := locallyOfFiniteType C
  haveI := h
  letI : GrpObj (Over.mk (Pic0Scheme C).hom) := (grpObj C).some
  exact smooth_of_grpObj (Pic0Scheme C).hom

/-- **The sole remaining input to smoothness of `Pic⁰_{C/k}`: geometric
reducedness.** (Run 0067 — the shrunk residue of the former `smooth` sorry.)

`Pic⁰_{C/k}` is geometrically reduced over `k`. This is **not** a
bookkeeping step, and it is worth being precise about why, because the
surrounding development makes it look available when it is not:

* `Smooth.geometricallyReduced` (`Curve/GeometricallyReduced.lean`) derives
  geometric reducedness *from* smoothness, so using it here is circular — it is
  the converse direction of what `smooth_of_geometricallyReduced` consumes;
* no other producer of `GeometricallyReduced` exists in this import closure for
  a scheme that is not already known smooth, so the class does not synthesize.

The genuine mathematics, following Kleiman §5: in characteristic zero this is
Cartier's theorem — every group scheme locally of finite type over a field of
characteristic zero is reduced, hence smooth (Kleiman §5 Cor.~`cor:ch0`). In
characteristic `p` it is a real curve-specific statement, and the input is the
vanishing `H²(C, 𝒪_C) = 0` for a curve, which makes the deformation functor of
an invertible sheaf unobstructed so that `Pic_{C/k}` is smooth of dimension
`dim H¹(C, 𝒪_C)` (Kleiman §5 Cor.~`cor:sm`, Ex.~`ex:jac`). Since `dim C = 1`,
`H²` vanishes for dimension reasons on a curve — which is why the curve case
holds in *every* characteristic, unlike the general Picard scheme, where
`Pic_{X/k}` can be non-smooth in characteristic `p` (Igusa's surface).

Stated as its own named obligation so that `smooth` below is an assembly and
the open mathematical content sits at one site with its source attached. -/
theorem geometricallyReduced {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    GeometricallyReduced (Pic0Scheme C).hom :=
  sorry

/-- **Geometric reducedness from reducedness of every field base change** — proved (run 0067),
and this is the honest unfolding of the class rather than a shortcut.

`GeometricallyReduced f` is by definition `geometrically IsReduced f`, i.e. `X ×_Y Spec K` is
reduced for every field `K` and every `Spec K ⟶ Y`. Since `IsReduced` is closed under
isomorphisms, mathlib's `geometrically_iff_of_isClosedUnderIsomorphisms` lets the abstract
pullback in the definition be replaced by the concrete `Limits.pullback`, so supplying
reducedness of each `Limits.pullback (Pic0Scheme C).hom y` discharges the class.

WHAT THIS DOES AND DOES NOT BUY. It converts the class into a statement about honest
pullbacks, which is the form in which the deformation-theoretic argument (Kleiman §5
`cor:sm`: `H²(C, 𝒪_C) = 0` makes the deformation functor unobstructed) can be applied to each
base change. What it does *not* do is reduce to the algebraically closed case: I checked, and
`GeometricallyReduced` has **no** `MorphismProperty.DescendsAlong` instance in mathlib v4.31,
so the `of_pullback_snd_of_descendsAlong` trick that works for `UniversallyClosed`
(`universallyClosed_of_baseChange` above) and that `smooth_of_grpObj` uses internally is *not*
available here. That is worth recording because it is the natural first thing to try.

This confirms from the AJC side a cross-project negative reported on inbox I-0495
(ajcr-w5-av, 2026-07-28, machine-probed): "IsReduced after base change to `k̄` implies
`GeometricallyReduced`" is in neither mathlib nor either project — mathlib handles algebraic
`K/k` (`RingTheory/Nilpotent/GeometricallyReduced.lean`) and stops, and
`Algebra.IsGeometricallyReduced` has zero consumers under `Mathlib/AlgebraicGeometry/`. So the
transcendental case is the missing infrastructure, and the quantification over *all* field
extensions in the statement below is not laziness — it is what the class actually asks for. -/
theorem geometricallyReduced_of_forall_isReduced {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (h : ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ Spec (.of k)),
      IsReduced (Limits.pullback (Pic0Scheme C).hom y)) :
    GeometricallyReduced (Pic0Scheme C).hom := by
  rw [geometricallyReduced_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  exact h K y

/-- **Smoothness of `Pic⁰_{C/k}` from reducedness of every field base change** — proved
(run 0067): `geometricallyReduced_of_forall_isReduced` composed with
`smooth_of_geometricallyReduced`.

The whole of the structural assembly is now discharged, and the residue is one reducedness
statement per field extension of `k`. -/
theorem smooth_of_forall_isReduced {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (h : ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ Spec (.of k)),
      IsReduced (Limits.pullback (Pic0Scheme C).hom y)) :
    Smooth (Pic0Scheme C).hom :=
  smooth_of_geometricallyReduced C (geometricallyReduced_of_forall_isReduced C h)

/-- **Smoothness of `Pic⁰_{C/k}` from reducedness over `k̄` ALONE** — the sharpest form of
the reduction, and the one that removes a wall both projects had recorded.

The hypothesis is `IsReduced` of the **single** scheme `Pic⁰_{C/k} ×_{Spec k} Spec k̄`, with
no quantifier over field extensions and no `GeometricallyReduced` class. Compare
`smooth_of_forall_isReduced` directly above, which asks for one reducedness statement *per*
field extension of `k`: this asks for one, at the algebraic closure.

SAME STRENGTH, BETTER ATTACK SURFACE — corrected after review, because the first version of
this paragraph claimed a strict improvement and that was wrong. `GeometricallyReduced` is
*defined* by base change along every `Spec K ⟶ Spec k`, so it implies the `k̄` instance. The
converse is **absent from mathlib v4.31** (no producer, and no `MorphismProperty.DescendsAlong`
instance — checked here and independently by the sibling project, inbox I-0495), which is what
the original claim rested on. But **this project owns the converse anyway**, through
`Smooth.geometricallyReduced` (`Curve/GeometricallyReduced.lean`): the `k̄` hypothesis gives
smoothness by this theorem, and smoothness gives the class. So at these binders the two
hypotheses are *interprovable* and this is a restatement.

The methodological error is worth more than the lemma: the "absent from mathlib" measurement
was taken inside this file's import cone (99 modules), which excludes
`Curve/GeometricallyReduced`, while the root cone (215 modules) contains it. A synthesis probe
cannot see a bridge its own imports exclude. Measure at the root.

WHAT THE RESTATEMENT IS STILL FOR. Interprovable is not equally attackable.
`GeometricallyReduced` has no non-circular producer in this development, whereas reducedness of
one scheme over one algebraically closed field is exactly where Kleiman §5 Cor.~`cor:sm` and
Cartier's theorem speak. And it discharges *two* obligations rather than one — see
`geometricallyReduced_of_isReduced_algebraicClosureBaseChange` below.

HOW IT IS AVAILABLE AT ALL. Mathlib's own `smooth_of_grpObj` reduces to exactly the `k̄` case
internally, but through a `private` lemma, so the intermediate statement is unreachable by
name. Both projects had recorded "get `smooth_of_grpObj_of_isAlgClosed` made public" as the
cheap upstream route. That PR is unnecessary: `private` hides the name and not the proof, and
that proof uses only public API, so it is re-derived in
`Picard/GroupSchemeSmoothAlgClosed.lean` and the criterion assembled there
(`smooth_of_grpObj_of_isReduced_algebraicClosureBaseChange`). This theorem is that criterion
applied to `Pic⁰`, with the same finite-type and group-object inputs as
`smooth_of_geometricallyReduced`.

Consumers owing smoothness should discharge *this* hypothesis: Kleiman §5 Cor.~`cor:sm`
argues over an algebraically closed field, and in characteristic zero Cartier's theorem
gives reducedness of any group scheme locally of finite type — over `k̄` directly, with no
descent step to arrange. -/
theorem smooth_of_isReduced_algebraicClosureBaseChange {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (h : IsReduced (Limits.pullback (Pic0Scheme C).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) :
    Smooth (Pic0Scheme C).hom := by
  haveI : LocallyOfFiniteType (Pic0Scheme C).hom := locallyOfFiniteType C
  letI : GrpObj (Over.mk (Pic0Scheme C).hom) := (grpObj C).some
  exact smooth_of_grpObj_of_isReduced_algebraicClosureBaseChange (Pic0Scheme C).hom h

/-- **The `k̄` hypothesis discharges `geometricallyReduced` too** — the corollary the first
version of this section missed, found by fresh-context review (run 0067).

`geometricallyReduced` above is an open `sorry` of this file, and it is *implied* by the very
hypothesis `smooth_of_isReduced_algebraicClosureBaseChange` consumes: reducedness over `k̄`
gives smoothness (that theorem), and smoothness gives the class
(`Smooth.geometricallyReduced`, `Curve/GeometricallyReduced.lean`). So one statement discharges
**both** the smoothness leg and the reducedness sorry.

That is also why the "strictly weaker hypothesis" claim above had to be withdrawn: the same
in-tree instance that makes this corollary work makes the two hypotheses interprovable. The
corollary is the useful half of that correction — a reviewer's negative finding turning into a
positive one.

Note this does **not** close `geometricallyReduced`: that theorem is stated with no hypothesis,
and what is proved here is the implication from the `k̄` statement. What it does is collapse two
apparently independent obligations into one, so a consumer supplying reducedness over `k̄` owes
nothing further on either. Verified axiom-clean at the *root* import (not inside this file's
cone, where `Smooth.geometricallyReduced` is invisible — see the correction above). -/
theorem geometricallyReduced_of_isReduced_algebraicClosureBaseChange {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (h : IsReduced (Limits.pullback (Pic0Scheme C).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) :
    GeometricallyReduced (Pic0Scheme C).hom :=
  haveI := smooth_of_isReduced_algebraicClosureBaseChange C h
  inferInstance

/-- **Smoothness of `Pic⁰_{C/k}`.**

For a smooth proper geometrically integral curve `C/k`, the identity component
`Pic⁰_{C/k}` is smooth over `k` (Kleiman §5 Cor.~`cor:sm` + Cor.~`cor:ch0` in
characteristic zero + Ex.~`ex:jac` for the curve case).

REDUCED (run 0067): this is now an assembly, not an obligation. The
translation argument and the descent to a non-closed base field are mathlib's
(`smooth_of_grpObj`, via `smooth_of_geometricallyReduced` above), and the
finite-type and group-object inputs are landed in this file. The single open
input is `geometricallyReduced` above — Cartier in characteristic zero,
`H²(C, 𝒪_C) = 0` in characteristic `p`. -/
theorem smooth {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Smooth (Pic0Scheme C).hom :=
  smooth_of_geometricallyReduced C (geometricallyReduced C)

/-- The curve-projectivity premise used by Kleiman §5 `th:qpp&p`, discharged
from the binders of the Picard-zero lane.

This theorem does not assert the projectivity or properness of `Pic⁰`; it closes
only the theorem's input about the curve. -/
theorem isProjective_for_kleimanQppAndP {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] : C.hom.IsProjective :=
  Adelic.isProjective_of_smoothProperGeometricallyIntegral C

/-- **Properness of `Pic⁰_{C/k}`.**

For a smooth proper geometrically integral curve `C/k`, the identity component
`Pic⁰_{C/k}` is proper over `k` (Kleiman §5 Thm.~`th:qpp&p`; a smooth proper
curve is geometrically normal, hence the projectivity upgrade applies).

REDUCED (run 0067) to its universal-closedness conjunct alone. Mathlib's
`IsProper` is a three-field structure — `IsSeparated`, `UniversallyClosed`,
`LocallyOfFiniteType` (`Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`;
quasi-compactness is *not* a field, being implied by universal closedness) —
and two of the three are already theorems of this file:

* `isSeparated` — the clopen inclusion `Pic⁰ ↪ Pic` is a monomorphism, hence
  separated, and `picScheme_isSeparated` gives separatedness of the ambient
  `Pic_{C/k}` from the strengthened `HasPicScheme` existential; separatedness
  is stable under composition;
* `locallyOfFiniteType` — the first conjunct of the sibling's
  `IdentityComponent.isFiniteTypeGeometricallyIrreducible`.

So the entire open content of properness is `UniversallyClosed`, named as
`universallyClosed` below. This is a strictly better factoring than the old
single `sorry`: the two discharged conjuncts are now *used* rather than merely
present in the file, and `universallyClosed` may additionally be attacked by
base change to `k̄` through the already-proved
`universallyClosed_of_baseChange` (Stacks 02KS descent), which reduces it to
the algebraically closed case where Kleiman's projectivity argument lives.

MEASURED (run 0067), same probe/control as `smooth_of_geometricallyReduced`: at a
probe site with the `HasPicScheme` gate assumed rather than synthesised and
`UniversallyClosed` supplied as a hypothesis, this theorem's conclusion reports
`[propext, Classical.choice, Quot.sound]` — axiom-clean — so universal
closedness is the entire residue of properness, with nothing leaking through the
separatedness or finite-type conjuncts. -/
theorem proper_of_universallyClosed {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (h : UniversallyClosed (Pic0Scheme C).hom) :
    IsProper (Pic0Scheme C).hom := by
  haveI : IsSeparated (Pic0Scheme C).hom := isSeparated C
  haveI : LocallyOfFiniteType (Pic0Scheme C).hom := locallyOfFiniteType C
  haveI := h
  constructor

/-- **The sole remaining input to properness of `Pic⁰_{C/k}`: universal
closedness.** (Run 0067 — the shrunk residue of the former `proper` sorry.)

The curve-projectivity input is `isProjective_for_kleimanQppAndP`.  The remaining
mathematics, Kleiman §5 Thm.~`th:qpp&p`: `Pic⁰_{C/k}` is quasi-projective
(first conclusion of that theorem), and for `C/k` geometrically normal — which
a smooth proper curve is — the identity component is *projective*, hence
universally closed. The upgrade from quasi-projective to projective goes
through the Chevalley–Rosenlicht structure theorem, reducing to ruling out
non-constant `k̄`-morphisms `𝔾_m → Pic⁰_{C/k̄}`; that in turn follows from
normality of `C ×_k 𝔾_m` together with Hartshorne II Ex.~6.15 (on a normal
integral scheme invertible sheaves are sheaves of Cartier divisors).

Note the standing project caveat (inbox I-0074, Caveat 2) that
`PicScheme.smoothProperQuotient` is *weaker* than Kleiman lm:qt and is not
provable as stated, because mathlib v4.31 has no quasi-projectivity
vocabulary. That is exactly the vocabulary the first conclusion above needs, so
this obligation is expected to be discharged by base change to `k̄` via
`universallyClosed_of_baseChange` rather than by formalising quasi-projectivity
from scratch.

SUPERSEDED ROUTE ADVICE (run 0067 r3/r6). The paragraph above is retained for its
mathematics, but `universallyClosed_of_valuativeCriterion` below is the better target:
it needs no quasi-projectivity vocabulary at all, and the `QuasiCompact` side condition
mathlib's valuative criterion wants is already a theorem here (`quasiCompact`). Do
**not** attempt the ambient route via `universallyClosed_of_ambient` — its hypothesis is
unsatisfiable, see the retraction there. Note that this statement, about
`(Pic0Scheme C).hom`, is *not* affected by that: `Pic⁰` is quasi-compact, `Pic` is not. -/
theorem universallyClosed {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    UniversallyClosed (Pic0Scheme C).hom :=
  sorry

/-- **Universal closedness of `Pic⁰_{C/k}` from the VALUATIVE criterion** — proved (run 0067
r3), and this route needs no quasi-projectivity vocabulary at all.

The recorded expectation at `universallyClosed` above is that the obligation would have to be
discharged by base change to `k̄`, "rather than by formalising quasi-projectivity from
scratch" — the standing caveat (inbox I-0074, Caveat 2) being that mathlib v4.31 has no
quasi-projectivity API, which is exactly the vocabulary Kleiman §5 Thm.~`th:qpp&p` uses.

There is a third route, and it is the standard one for properness: the **valuative
criterion** (Stacks 01KF). Mathlib has it as
`UniversallyClosed.of_valuativeCriterion`, which needs

* `[QuasiCompact (Pic0Scheme C).hom]` — already a theorem of this file, `quasiCompact`
  (Kleiman §5 Lem.~`lem:agps`(3), landed since run 0009);
* `ValuativeCriterion.Existence (Pic0Scheme C).hom` — the hypothesis here.

So universal closedness needs no projectivity, no Chevalley–Rosenlicht structure theorem and
no ruling out of `𝔾_m → Pic⁰_{C/k̄}`; it needs *lifting*. Concretely
`ValuativeCriterion.Existence` says: for every valuation ring `R` with fraction field `K`,
every square

```
Spec K ⟶ Pic⁰_{C/k}
  |            |
  ↓            ↓
Spec R ⟶   Spec k
```

admits a lift `Spec R ⟶ Pic⁰_{C/k}`.

WHY THIS IS THE RIGHT SHAPE FOR THIS PROJECT, and the reason it is worth stating even though
the hypothesis is still open. Through representability (`PicScheme.representable`) a
`Spec R`-point of the Picard scheme *is* a relative Picard class on `C ×_k Spec R`, so the
lifting statement translates into the concrete algebraic assertion that an invertible sheaf on
`C ×_k Spec K` extends over the valuation ring — which is the classical content of properness
of the Picard scheme, and is the kind of statement the tangent/chart machinery of this chapter
already speaks about (compare `DualNumber.free_of_cyclic_mod_eps`, which is the same species
of extension statement for the square-zero thickening `k[ε] → k`). The quasi-projectivity
route, by contrast, requires vocabulary that does not exist in the pinned mathlib.

Not claimed: the existence half is *not* proved here. What is established is that properness
of `Pic⁰` reduces to it with nothing else outstanding — see `proper_of_valuativeCriterion`
below, where all three other conjuncts are discharged from theorems of this file. -/
theorem universallyClosed_of_valuativeCriterion {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (h : ValuativeCriterion.Existence (Pic0Scheme C).hom) :
    UniversallyClosed (Pic0Scheme C).hom := by
  haveI : QuasiCompact (Pic0Scheme C).hom := quasiCompact C
  exact UniversallyClosed.of_valuativeCriterion _ h

/-- **Properness of `Pic⁰_{C/k}` from the valuative existence criterion alone** — proved
(run 0067 r3). The sharpest properness reduction in this file, and the only one whose
hypothesis is a statement mathlib has vocabulary for.

Every conjunct of `IsProper` other than the valuative lifting is a theorem of this file:

* `IsSeparated` — `isSeparated` (clopen mono into the separated ambient `Pic`);
* `LocallyOfFiniteType` — `locallyOfFiniteType` (Kleiman §5 Lem.~`lem:agps`);
* `QuasiCompact` — `quasiCompact` (same lemma, second conjunct);
* `UniversallyClosed` — `universallyClosed_of_valuativeCriterion` above, from the hypothesis.

Compare the two earlier reductions in this file. `proper_of_universallyClosed` leaves
universal closedness of `Pic⁰` open; `proper_of_ambient_universallyClosed` moves it to the
ambient `Pic_{C/k}` — and **that move is now retracted** (run 0067 r6): universal closedness
of `Pic_{C/k}` is not merely hard to prove, it is *false*, since it would force
`CompactSpace (PicScheme C).left` while `Pic_{C/k}` is an infinite disjoint union over
`deg ∈ ℤ`. See `universallyClosed_of_ambient` and `Picard/AmbientPicNotProper.lean`.

**So this theorem is not one of three routes; it is the route.** Its hypothesis is about
`(Pic0Scheme C).hom`, whose source is quasi-compact (`quasiCompact` above), so nothing
here is obstructed the way the ambient version is. It also needs no quasi-projectivity
vocabulary — the residue is a lifting statement, formalisable in the pinned mathlib and
the classical content of properness. -/
theorem proper_of_valuativeCriterion {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (h : ValuativeCriterion.Existence (Pic0Scheme C).hom) :
    IsProper (Pic0Scheme C).hom := by
  haveI : IsSeparated (Pic0Scheme C).hom := isSeparated C
  haveI : LocallyOfFiniteType (Pic0Scheme C).hom := locallyOfFiniteType C
  haveI := universallyClosed_of_valuativeCriterion C h
  constructor

/-- **Universal closedness of `Pic⁰_{C/k}` from that of the ambient `Pic_{C/k}`** — proved
(run 0067), and this is the reduction that removes the identity component from the problem
entirely.

`Pic⁰_{C/k} ↪ Pic_{C/k}` is a **closed** immersion — the second conjunct of the sibling's
`IdentityComponent.isOpenSubgroupScheme`, which supplies the inclusion as an open *and*
closed immersion. A closed immersion is universally closed, `UniversallyClosed` is stable
under composition (`universallyClosed_isStableUnderComposition`), and the composite
`Pic⁰ ↪ Pic → Spec k` *is* `(Pic0Scheme C).hom` by `Over.w` of the inclusion. So universal
closedness of the structural morphism of `Pic⁰` follows from that of `Pic`.

Note the closed-immersion conjunct is doing real work: an *open* immersion is not
universally closed, so this argument needs the clopen-ness that
`isOpenSubgroupScheme` provides and would fail for a general open subgroup scheme.

⚠ **RETRACTED AS A REDUCTION (run 0067 r6). This theorem is true; its hypothesis is
not satisfiable at `PicScheme C`, so it reduces nothing.** The paragraph deleted from
here claimed this "moves the open content off the identity component and onto the
ambient Picard scheme, where Kleiman's argument actually lives", and the roadmap row
`AJC.pic0av.structure` accordingly called it "a SECOND, INDEPENDENT reduction … worth
trying first". Both were wrong, and no `sorry` census or axiom probe could detect it,
because a theorem with an unsatisfiable hypothesis is still a theorem.

Why the hypothesis fails: `UniversallyClosed` carries finiteness of the *source* over
an affine base. Mathlib derives `QuasiCompact` from it (the `priority := 900` instance
of `Morphisms/UniversallyClosed.lean` — precisely why `IsProper` has three fields and
no quasi-compactness one), and `Spec k` is compact, so `UniversallyClosed
(PicScheme C).hom` would give `CompactSpace (PicScheme C).left`. But `Pic_{C/k}` is a
**disjoint union over `deg ∈ ℤ`** (Kleiman §6 `ex:curves`), and an infinite disjoint
cover by nonempty opens has no finite subcover. `HasPicScheme` bundles only
representation, local finite type, and separatedness; the degree decomposition is not
formalised here. Kernel-checked at scheme generality in
`Picard/AmbientPicNotProper.lean`
(`Scheme.not_universallyClosed_of_infinite_disjoint_open_cover`).

Retained rather than deleted, for two reasons. The closed-immersion transport is
correct and is exactly what a *finite* ambient union would need — if a future
development produces a single `Pic^d` as the ambient object, this is the right lemma.
And `¬ UniversallyClosed (PicScheme C).hom` is not itself formalised here (it needs the
degree decomposition of the scheme, which this project lacks — it has `PicScheme.degree`
but not the fibrewise splitting), so the retraction is of the *route*, argued from a
general theorem, not a formalised refutation of this hypothesis.

USE INSTEAD: `proper_of_valuativeCriterion` / `universallyClosed_of_valuativeCriterion`,
which speak about `(Pic0Scheme C).hom`, whose source **is** quasi-compact
(`Pic0.quasiCompact`). What the roadmap called the fallback was the only route. -/
theorem universallyClosed_of_ambient {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (hPic : UniversallyClosed (PicScheme C).hom) :
    UniversallyClosed (Pic0Scheme C).hom := by
  obtain ⟨f, -, hclosed⟩ :=
    GroupScheme.IdentityComponent.isOpenSubgroupScheme (PicScheme C)
  haveI := hclosed
  haveI hfc : UniversallyClosed f.left := by infer_instance
  have hw : f.left ≫ (PicScheme C).hom = (Pic0Scheme C).hom := Over.w f
  rw [← hw]
  exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ hfc hPic

/-- **Properness of `Pic⁰_{C/k}` from universal closedness of the ambient `Pic_{C/k}`** —
proved (run 0067). The composite of `universallyClosed_of_ambient` with
`proper_of_universallyClosed`.

⚠ **RETRACTED AS A REDUCTION (run 0067 r6), for the reason given in full at
`universallyClosed_of_ambient` above.** This text used to call it "the sharpest form of
the properness reduction currently available … what remains is one property of
`Pic_{C/k}`". It is a true theorem whose hypothesis `UniversallyClosed (PicScheme C).hom`
cannot hold: universal closedness over an affine base implies `CompactSpace` of the
source, while `Pic_{C/k}` is an infinite disjoint union over `deg ∈ ℤ`. See
`Picard/AmbientPicNotProper.lean`.

The separatedness and finite-type conjuncts, and the closed-immersion passage from the
ambient scheme to the identity component, are genuinely discharged — the defect is
entirely in *which object* the remaining property is asked of. Use
`proper_of_valuativeCriterion` instead. -/
theorem proper_of_ambient_universallyClosed {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (hPic : UniversallyClosed (PicScheme C).hom) :
    IsProper (Pic0Scheme C).hom :=
  proper_of_universallyClosed C (universallyClosed_of_ambient C hPic)

/-- **Properness of `Pic⁰_{C/k}`** — assembly (run 0067) of the two landed
conjuncts `isSeparated` / `locallyOfFiniteType` with the single open conjunct
`universallyClosed`, via `proper_of_universallyClosed`. -/
theorem proper {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    IsProper (Pic0Scheme C).hom :=
  proper_of_universallyClosed C (universallyClosed C)

/-- **Geometric irreducibility of `Pic⁰_{C/k}`.**

For a smooth proper geometrically integral curve `C/k`, the identity component
`Pic⁰_{C/k}` is geometrically irreducible over `k` (Kleiman §5 Prp.~`prp:pic0`,
specialisation of the abstract identity-component substrate
`IdentityComponent.isFiniteTypeGeometricallyIrreducible` of
`Picard/IdentityComponent.lean` to `G = PicScheme C`).

The proof: apply `GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible`
to `G = PicScheme C` (locally of finite type by the
`PicSchemeLocallyOfFiniteType` carrier); `IdentityComponent (PicScheme C)`
is `Pic0Scheme C` definitionally. The specialisation is complete here, and
the mathematical content (Kleiman's translate-cover argument, EGA IV₂
4.5.8/4.6.1) was closed in the sibling's
`isFiniteTypeGeometricallyIrreducible` in run 0009. -/
theorem geometricallyIrreducible {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    GeometricallyIrreducible (Pic0Scheme C).hom :=
  (GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible
    (PicScheme C)).2.2

/-- **`Pic⁰_{C/k}` is an abelian variety (A.3.vii assembly).**

For a smooth proper geometrically integral curve `C/k`, the identity
component `Pic⁰_{C/k}` is an abelian variety over `k`: the underlying
`k`-scheme is smooth (`Pic0.smooth`), proper (`Pic0.proper`), and
geometrically irreducible (`Pic0.geometricallyIrreducible`), and it carries
a `k`-group-scheme structure inherited from `Pic_{C/k}` via the inclusion
`Pic⁰_{C/k} ↪ Pic_{C/k}`
(`GroupScheme.IdentityComponent.isSubgroupHomomorphism`). Commutativity is
automatic (Milne §I.1, Cor.~1.4).

Milne §I.1, p.~8: "A complete connected group variety is called an abelian
variety." This is the load-bearing A.3.vii gate of Route~A for
`thm:nonempty_jacobianWitness`.

The proof assembles the four conjuncts: `proper` (this file), `smooth`
(this file), `geometricallyIrreducible` (this file), and the
`Nonempty (GrpObj (Pic0Scheme C))` slot from `Pic0.grpObj` (this file,
via `GroupScheme.IdentityComponent.isSubgroupHomomorphism` applied to
`G = PicScheme C`). The assembly itself is sorry-free; the remaining
obligations live in the `smooth` / `proper` conjuncts and the
geometric-irreducibility substrate. -/
theorem isAbelianVariety {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    IsProper (Pic0Scheme C).hom ∧ Smooth (Pic0Scheme C).hom ∧
      GeometricallyIrreducible (Pic0Scheme C).hom ∧
      Nonempty (GrpObj (Pic0Scheme C)) :=
  ⟨proper C, smooth C, geometricallyIrreducible C, grpObj C⟩

end Pic0

namespace Pic0Scheme

/-- **`Pic⁰_{C/k}` is an abelian variety** — the `Pic0Scheme`-namespace form
pinned by the blueprint node `thm:pic_zero_is_abelian_variety`
(`Picard_IdentityComponent.tex`). Moved here (run 0008) from sibling
`Picard/IdentityComponent.lean` so it can consume the per-conjunct theorems
of this chapter; it is literally `Pic0.isAbelianVariety`. -/
theorem isAbelianVariety {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    IsProper (Pic0Scheme C).hom ∧ Smooth (Pic0Scheme C).hom ∧
      GeometricallyIrreducible (Pic0Scheme C).hom ∧
      Nonempty (GrpObj (Pic0Scheme C)) :=
  Pic0.isAbelianVariety C

end Pic0Scheme

end Scheme

end AlgebraicGeometry
