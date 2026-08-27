/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.LineBundlePullback
import AlgebraicJacobian.Picard.SheafOverEquivalence

/-!
# Coherence of locally trivial line bundles (A.2.c engine)

This file is the **iter-256 Lane engine** file-skeleton for the cheap, on-path
half of the line-bundle coherence requirement of the A.2.c Quot-scheme
embedding (`chap:Picard_QuotScheme`, `chap:Picard_FGAPicRepresentability`).

The Quot functor takes coherent quotients of a coherent sheaf; to feed it a line
bundle one must know that the line bundle is itself coherent, i.e. a finitely
presented `𝒪`-module. The embedding's input is a point of the relative Picard
scheme `Pic⁰_{C/k}`, whose carrier is the **locally trivial** predicate
`IsLocallyTrivial` of `chap:Picard_LineBundlePullback` (the project-side stand-in
for an invertible sheaf). The chapter proves
`IsLocallyTrivial M ⟹ M.IsFinitePresentation`, together with a rank-one /
flatness record. The general implication "`M` tensor-invertible `⟹` `M` locally
free of rank one" (the converse spreading-out, Stacks Lemma 0B8M when stalks are
local) is *not* crossed here: the carrier is already locally trivial, so the
finite-presentation spreading-out is never needed.

## Status (iter-258: 1 sorry → 0 locally; redirected to shared root)

The engine file is now **locally `sorry`-free**. The last remaining ingredient,
the over↔restrict bridge `chartOverIso`, has been redirected to the general
`Scheme.Modules.chartOverIso` of `AlgebraicJacobian.Picard.SheafOverEquivalence`
(the iter-258 shared-root pivot). That general bridge is a complete one-line
composite; its remaining mathematical content (the three isos `overEquivalence`,
`restrictOverIso`, `unitOverIso`) lives in the shared-root file, where the dual
lane (`DualInverse.lean`) consumes the same construction. Once those three close,
this engine becomes fully axiom-clean with no further edits here.

Of the five pinned declarations, four were closed axiom-clean and the fifth
(`chartPresentation`) is complete modulo the (now redirected) `chartOverIso`:

* `exists_trivializing_cover` — CLOSED (axiom-clean): repackage the pointwise
  `IsLocallyTrivial` existential as an indexed affine cover.
* `chart_free_rank_one` — CLOSED (axiom-clean): the chart-local trivialisation.
* `chartPresentation` — built as `unitPresentation.ofIsIso chartOverIso.inv`; its
  `IsFinite` rides on the `ofIsIso` instance. Reduces to `chartOverIso`.
* `isFinitePresentation` — CLOSED modulo `chartOverIso`: assembles the
  `QuasicoherentData` from the cover + `chartPresentation`, `shrink`s the index
  into the site-object universe, and feeds `IsFinitePresentation.mk`.
* `isFiniteType` — CLOSED modulo `chartOverIso`: the Mathlib
  `IsFinitePresentation → IsFiniteType` instance.

Two reusable axiom-clean bricks were added: `freeUnitIso` (`free PUnit ≅ unit R`)
and `unitPresentation` (the canonical finite presentation of the unit module,
one generator / no relations), with a `Presentation.IsFinite` instance.

**`chartOverIso` (now redirected, no local `sorry`)** — is the over↔restrict
trivialisation bridge: an isomorphism `M.over U ≅ unit (X.ringCatSheaf.over U)`
transporting the given scheme-level trivialisation
`e : M.restrict U.ι ≅ unit (↑U).ringCatSheaf`. The two source categories are
equivalent via the open-immersion site equivalence
`Opens.overEquivalence U : Over U ≌ Opens ↥U` (`Mathlib.Topology.Sheaves.Over`);
lifting that equivalence to the level of *sheaves of modules* is the shared root
`Scheme.Modules.overEquivalence` of `AlgebraicJacobian.Picard.SheafOverEquivalence`,
and the bridge is the general `Scheme.Modules.chartOverIso` built there. This file
now delegates to that construction (the same wall the dual lane consumes). See
`informal/chartOverIso.md`.

The 5 pinned declarations are:

1. `IsLocallyTrivial.exists_trivializing_cover` (`lem:lbc_trivializing_cover`) —
   repackage the pointwise existential of `IsLocallyTrivial` into an indexed
   trivialising affine cover.
2. `IsLocallyTrivial.chartPresentation` (`lem:lbc_chart_presentation`) — the
   trivial finite free presentation of `M.over U` on a trivialising chart.
3. `IsLocallyTrivial.isFinitePresentation` (`thm:lbc_isFinitePresentation`) —
   the main theorem: assemble a `QuasicoherentData` from the trivialising cover
   and feed it to `SheafOfModules.IsFinitePresentation.mk`.
4. `IsLocallyTrivial.isFiniteType` (`cor:lbc_isFiniteType`) — finite type +
   quasi-coherence, immediate from finite presentation.
5. `IsLocallyTrivial.chart_free_rank_one` (`lem:lbc_rank_flat`) — the chart-local
   rank-one free record.

## Site instances (the chief de-risk; see `rem:lbc_site_instances`)

Mathlib's `SheafOfModules.IsFinitePresentation` / `QuasicoherentData` are stated
under three site hypotheses on the slice topologies `J.over U` of the underlying
topology `J = Opens.grothendieckTopology X` of `X.ringCatSheaf`:

```
[∀ U, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
[∀ U, HasWeakSheafify (J.over U) AddCommGrpCat]     -- (resp. HasSheafify)
[∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
```

The de-risk outcome (whether these resolve for `X.ringCatSheaf`) is recorded in
the task result and probed by the `#check` commands at the end of this file.

## References

Blueprint: `blueprint/src/chapters/Picard_LineBundleCoherence.tex`.
Source: [Stacks Project], Modules on Ringed Spaces, Definition 17.25.1
(Tag 01CS, invertible modules), "Modules of finite presentation", and
Lemma 17.25.4 (Tag 0B8M).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

namespace LineBundle

variable {X : Scheme.{u}}

/-! ## §1. From pointwise triviality to a trivialising cover -/

/-- **Trivialising affine cover** (Stacks 01CS / Definition 17.25.1).
A locally trivial module `M` admits an indexed trivialising affine cover: an
index type `I`, a family of affine opens `U i` covering `X`, and for each `i` a
`𝒪_{U_i}`-module isomorphism `M|_{U_i} ≅ 𝒪_{U_i}`.

The witness repackages the pointwise existential `IsLocallyTrivial M` (take
`I := X` and assign each point its chosen neighbourhood). -/
theorem IsLocallyTrivial.exists_trivializing_cover {M : X.Modules}
    (hM : IsLocallyTrivial M) :
    ∃ (I : Type u) (U : I → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ ∧
        ∀ i, Nonempty (M.restrict (U i).ι ≅
          SheafOfModules.unit (U i : Scheme).ringCatSheaf) := by
  refine ⟨X, fun x => (hM x).choose, fun x => (hM x).choose_spec.2.1, ?_,
    fun x => (hM x).choose_spec.2.2⟩
  rw [eq_top_iff]
  intro x _
  rw [TopologicalSpace.Opens.mem_iSup]
  exact ⟨x, (hM x).choose_spec.1⟩

/-! ## §1b. The canonical finite presentation of the unit module -/

section UnitPresentation

universe u₁ v₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- The canonical isomorphism `free PUnit ≅ unit R`: the free module on a single
generator is the unit module. -/
noncomputable def freeUnitIso :
    SheafOfModules.free.{u} (R := R) PUnit.{u + 1} ≅ SheafOfModules.unit R :=
  Limits.coproductUniqueIso (fun (_ : PUnit.{u + 1}) ↦ SheafOfModules.unit R)

/-- The canonical generating sections of `unit R`: one generator (the image of
the free generator under `freeUnitIso`). -/
noncomputable def unitGenerators : (SheafOfModules.unit R).GeneratingSections where
  I := PUnit.{u + 1}
  s := (SheafOfModules.unit R).freeHomEquiv freeUnitIso.hom
  epi := by
    rw [Equiv.symm_apply_apply]
    infer_instance

/-- The canonical finite presentation of the unit module `unit R`: one generator,
no relations (its generating map is an isomorphism, so the relation kernel is the
zero object). -/
noncomputable def unitPresentation : (SheafOfModules.unit R).Presentation where
  generators := unitGenerators
  relations :=
    { I := PEmpty.{u + 1}
      s := PEmpty.elim
      epi := by
        have hiso : IsIso (unitGenerators (R := R)).π := by
          dsimp only [unitGenerators, SheafOfModules.GeneratingSections.π]
          rw [Equiv.symm_apply_apply]
          infer_instance
        have : Mono (unitGenerators (R := R)).π := inferInstance
        have hz : Limits.IsZero (Limits.kernel (unitGenerators (R := R)).π) :=
          Limits.isZero_kernel_of_mono _
        exact ⟨fun g h _ => hz.eq_of_src g h⟩ }

instance : (unitPresentation (R := R)).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite PUnit.{u + 1})⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite PEmpty.{u + 1})⟩

end UnitPresentation

/-! ## §2. The trivial presentation on a chart -/

/-- **The over↔restrict trivialisation bridge.** Transports the scheme-level
trivialisation `e : M.restrict U.ι ≅ 𝒪_U` (an isomorphism in
`SheafOfModules (↑U).ringCatSheaf`, the category of modules on the *open
subscheme* `U`) to a slice-level trivialisation
`M.over U ≅ 𝒪_U` (in `SheafOfModules (X.ringCatSheaf.over U)`, the category of
modules on the *slice site* `J.over U`).

The two source categories are equivalent — the open-immersion functor
`U.ι.opensFunctor : Opens ↥U ≌ {V ∈ Opens X | V ≤ U} = Over U` induces an
equivalence `SheafOfModules (↑U).ringCatSheaf ≌ SheafOfModules (X.ringCatSheaf.over U)`
identifying `M.restrict U.ι ↦ M.over U` and `unit ↦ unit`. That modules-level
lift of `Opens.overEquivalence` is the shared root `Scheme.Modules.overEquivalence`
of `AlgebraicJacobian.Picard.SheafOverEquivalence`, and the bridge is the general
`Scheme.Modules.chartOverIso` built there as the three-step composite
`(restrictOverIso).symm ≪≫ overEquivalence.functor.mapIso e ≪≫ unitOverIso`.

This local declaration now **redirects** to that general construction (the
iter-258 shared-root pivot), so it carries no `sorry` of its own; the remaining
mathematical content (the three isos `overEquivalence` / `restrictOverIso` /
`unitOverIso`) lives in the shared-root file where the dual lane consumes it too.
Everything else in this engine (`chartPresentation`, `isFinitePresentation`,
`isFiniteType`) was already complete modulo this isomorphism. -/
noncomputable def chartOverIso (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  Scheme.Modules.chartOverIso U M e

/-- **Finite free presentation on a chart** (Stacks, "Modules of finite
presentation"). On a trivialising chart `U` — i.e. with an isomorphism
`M|_U ≅ 𝒪_U` — the restriction `M.over U` admits the trivial finite free
presentation (one generator, no relations), obtained by transporting the
canonical presentation of `SheafOfModules.unit` along the trivialisation
(through the `chartOverIso` bridge). -/
noncomputable def IsLocallyTrivial.chartPresentation (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (M.over U).Presentation := by
  exact SheafOfModules.Presentation.ofIsIso (R := X.ringCatSheaf.over U)
    (M := SheafOfModules.unit (X.ringCatSheaf.over U)) (N := SheafOfModules.over M U)
    (chartOverIso M U e).inv (unitPresentation (R := X.ringCatSheaf.over U))

instance (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (IsLocallyTrivial.chartPresentation M U e).IsFinite := by
  dsimp only [IsLocallyTrivial.chartPresentation]
  infer_instance

/-! ## §3. Finite presentation of a locally trivial line bundle -/

set_option synthInstance.maxHeartbeats 400000 in -- v4.31.0: `sheafToPresheaf.IsRightAdjoint` synth is slow
/-- **Locally trivial `⟹` finitely presented** (Stacks 0B8M / Lemma 17.25.4).
A locally trivial module on a scheme is finitely presented: assemble a
`QuasicoherentData` from the trivialising affine cover
(`exists_trivializing_cover`), whose presentation at each index is the finite
free presentation of `chartPresentation`, and feed it to
`SheafOfModules.IsFinitePresentation.mk`. No stalk computation or
neighbourhood-spreading is involved. -/
theorem IsLocallyTrivial.isFinitePresentation {M : X.Modules}
    (hM : IsLocallyTrivial M) :
    M.IsFinitePresentation := by
  obtain ⟨I, U, hUaff, hUtop, hUiso⟩ := hM.exists_trivializing_cover
  -- assemble the quasi-coherent data, one finite chart presentation per index;
  -- `shrink` lands the index type in the site-object universe demanded by
  -- `IsFinitePresentation`'s existential.
  let q : M.QuasicoherentData :=
    { I := I
      X := U
      coversTop := by
        -- the trivialising affine opens cover the terminal object of the site
        intro W x hxW
        have hx : x ∈ iSup U := by rw [hUtop]; trivial
        rw [TopologicalSpace.Opens.mem_iSup] at hx
        obtain ⟨i, hi⟩ := hx
        exact ⟨U i ⊓ W, homOfLE inf_le_right, ⟨i, ⟨homOfLE inf_le_left⟩⟩, hi, hxW⟩
      presentation := fun i => IsLocallyTrivial.chartPresentation M (U i) (hUiso i).some }
  have hsh : q.shrink.IsFinitePresentation := by
    apply SheafOfModules.QuasicoherentData.IsFinitePresentation.mk
    intro i
    exact inferInstanceAs (IsLocallyTrivial.chartPresentation M _ _).IsFinite
  exact { exists_quasicoherentData := ⟨q.shrink, hsh⟩ }

/-- **Locally trivial `⟹` finite type and quasi-coherent** (corollary of
`isFinitePresentation`). Finite presentation implies finite type by Mathlib's
`SheafOfModules.instIsFiniteTypeOfIsFinitePresentation` and quasi-coherence by
`SheafOfModules.instIsQuasicoherentOfIsFinitePresentation`. -/
theorem IsLocallyTrivial.isFiniteType {M : X.Modules}
    (hM : IsLocallyTrivial M) :
    M.IsFiniteType := by
  haveI := hM.isFinitePresentation
  infer_instance

/-! ## §4. Rank one and flatness record -/

/-- **Chart-local rank one and flatness** (Stacks, "Locally free sheaves":
finite locally free of rank `r`). On a trivialising chart the restriction
`M|_U ≅ 𝒪_U` is free of rank one over `𝒪_U`; in particular flat (`𝒪_U` is a flat
module over itself, and flatness is preserved by the isomorphism). The fact is
recorded chart-locally — as the rank-one free model `M|_U ≅ 𝒪_U = ⊕_{*} 𝒪_U`
the Quot embedding consumes — because Mathlib has no `SheafOfModules`-level
locally-free / flat / rank predicate. -/
theorem IsLocallyTrivial.chart_free_rank_one {M : X.Modules}
    (hM : IsLocallyTrivial M) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      Nonempty (M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) := by
  exact hM x

end LineBundle

namespace Modules

/-- Sections over an open transport across an isomorphism after restriction.
The result is linear over the ambient section ring, so it can also be
restricted to any base ring acting through the ambient scheme. -/
noncomputable def sectionLinearEquivOfRestrictIso
    {X : Scheme.{u}} {M N : X.Modules} (W : X.Opens)
    (e : M.restrict W.ι ≅ N.restrict W.ι) :
    Γ(M, W) ≃ₗ[Γ(X, W)] Γ(N, W) := by
  set αM : Γ(M.restrict W.ι, ⊤) ≅ Γ(M, W.ι ''ᵁ ⊤) :=
    M.restrictAppIso W.ι ⊤ with hαM
  set αN : Γ(N.restrict W.ι, ⊤) ≅ Γ(N, W.ι ''ᵁ ⊤) :=
    N.restrictAppIso W.ι ⊤ with hαN
  let f : Γ(M, W.ι ''ᵁ ⊤) ≃ₗ[Γ(X, W.ι ''ᵁ ⊤)] Γ(N, W.ι ''ᵁ ⊤) :=
    { toFun := fun x => αN.hom (e.hom.app ⊤ (αM.inv x))
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun r x => by
        simp only [hαM, hαN, smul_restrictAppIso_inv_apply,
          smul_restrictAppIso_hom_apply, Scheme.Opens.ι_appIso,
          Iso.refl_hom, Hom.app_smul, RingHom.id_apply]
        rfl
      invFun := fun y => αM.hom (e.inv.app ⊤ (αN.inv y))
      left_inv := fun x => by
        have h1 : e.inv.app ⊤ (e.hom.app ⊤ (αM.inv x)) = αM.inv x := by
          change (e.hom ≫ e.inv).app ⊤ (αM.inv x) = αM.inv x
          rw [e.hom_inv_id]
          rfl
        change αM.hom (e.inv.app ⊤
          (αN.inv (αN.hom (e.hom.app ⊤ (αM.inv x))))) = x
        have hN : αN.inv (αN.hom (e.hom.app ⊤ (αM.inv x))) =
            e.hom.app ⊤ (αM.inv x) := αN.hom_inv_id_apply _
        rw [hN, h1]
        exact αM.inv_hom_id_apply x
      right_inv := fun y => by
        have h1 : e.hom.app ⊤ (e.inv.app ⊤ (αN.inv y)) = αN.inv y := by
          change (e.inv ≫ e.hom).app ⊤ (αN.inv y) = αN.inv y
          rw [e.inv_hom_id]
          rfl
        change αN.hom (e.hom.app ⊤
          (αM.inv (αM.hom (e.inv.app ⊤ (αN.inv y))))) = y
        have hM : αM.inv (αM.hom (e.inv.app ⊤ (αN.inv y))) =
            e.inv.app ⊤ (αN.inv y) := αM.hom_inv_id_apply _
        rw [hM, h1]
        exact αN.inv_hom_id_apply y }
  exact W.ι_image_top ▸ f

end Modules

end Scheme

end AlgebraicGeometry
