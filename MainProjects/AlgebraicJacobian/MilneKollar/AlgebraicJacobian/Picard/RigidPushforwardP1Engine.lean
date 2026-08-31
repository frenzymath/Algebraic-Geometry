/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.TwoTermFiniteFree
import AlgebraicJacobian.Picard.RigidPushforward
import AlgebraicJacobian.Picard.ChartSectionsFinite
import AlgebraicJacobian.RiemannRoch.CohomologyKit
import AlgebraicJacobian.RiemannRoch.Adelic.P1ChartData

/-!
# B3 — the ℙ¹_A engine: the base-linear Čech complex and its finiteness

This file instantiates the **abstract two-term finite replacement** of
`Picard/TwoTermFiniteFree.lean` (Mumford AV II §5 Lemma 1) on the explicit
2-chart Čech complex of the projective line `ℙ¹_A = ℙ¹_k ×_k Spec A`
(`Adelic.p1BaseChangeCoverSquare`), towards the pinned ℙ¹ engine
`Adelic.P1RigidPushforwardStatement` of `Picard/RigidPushforward.lean` §5.

## Contents

* **§1 — base-linear Čech bookkeeping** (work item 1(iii)/(ii)).  For a family
  `p : X ⟶ S` the section modules `Γ(M, W)` of a module `M` on the total
  space are `Γ(S, ⊤)`-modules via `Module.compHom` along `p.appLE ⊤ W`
  (`Scheme.Hom.baseSectionsModule` — the *same definitional spelling* as the
  pinned `CoherentSheafFlat` hypothesis, so flatness is consumed with zero
  transport, `flat_baseSections_of_coherentSheafFlat`).  Restriction maps are
  linear for these structures (`baseSections_res_smul`), whence the
  difference-of-restrictions map of a 2-affine cover upgrades to the
  `Γ(S, ⊤)`-linear two-term complex `moduleSectionDiffBase` with degree-0
  piece `moduleSectionResBase`.

* **§2 — the kernel identification** (work item 1(i)).  The sheaf condition
  of `M` on the 2-cover identifies the global sections with the kernel of
  the difference map, `Γ(S, ⊤)`-linearly:
  `AffineCoverMVSquare.globalSectionsEquivKerModuleSectionDiffBase`.
  (`X.Modules`-dialect of `AffineCoverMVSquare.globalSectionsEquivH0ₗ` of
  `RiemannRoch/CohomologyKit.lean`, over the affine base instead of `k`.)

* **§3 — the A-coefficient Laurent ladder** (work item 2).  The abstract
  two-lattice core of `RiemannRoch/Adelic/FinitenessP1.lean` is restated for
  *module* coefficients (`module_finite_quotient_of_laurent_endo_pair` — the
  Laurent pair acts through commuting `A`-linear endomorphisms, which is
  what the pulled-back coordinates of `ℙ¹_A` induce on the section modules
  of `M`), together with the module-coefficient chart-ladder producer
  (`exists_finset_forall_mem_span_pow_smul`) and the module-section
  extension lemma over a chart (`Scheme.Modules.exists_pow_smul_eq_res`,
  from the qcqs section-localization engine of `Picard/QuotScheme.lean`).
  The relative Laurent chart datum (`Scheme.RelLaurentChartData`) packages
  the base-linear chart structure; `RelLaurentChartData.module_finite_h1`
  is the **`H¹`-finiteness keystone**: the Čech cokernel of
  `moduleSectionDiffBase` for a finitely presented `M` is a finite
  `Γ(S, ⊤)`-module.

* **§4 — the ℙ¹_A instantiation**.  `Adelic.p1BaseChangeRelLaurentChartData`
  equips `p1BaseChangeCoverSquare` with a relative Laurent chart datum: the
  coordinates are the `pr₁`-pullbacks of the `ℙ¹_k` Laurent coordinates
  (`Adelic.p1LaurentChartData`), the chart-ring `Γ(S, ⊤)`-spans come from
  the ring-pushout description of the base-changed charts
  (`isIso_pushoutSection_of_isAffineOpen` on the defining pullback square of
  `ℙ¹_A`, the char-free Route B of `RiemannRoch/Adelic/P1ChartData.lean`).
  `Adelic.module_finite_h1_p1BaseChange` is the concrete `H¹`-finiteness of
  the ℙ¹_A Čech complex.

* **§5 — the endgame skeleton** (work item 3, as far as it goes).
  `p1Cech_h0_baseChange_of_fibrewise_h1_vanishing` applies the
  `TwoTermFiniteFree` endgame to the base-linear Čech complex: fibrewise
  `H¹`-vanishing at all maximal ideals + `H⁰` finite generation give `d`
  surjective, `H⁰ = ker d` finite projective (= locally free), and `H⁰`
  formation commuting with arbitrary base change.

## Statement audit (work items 1–2; recorded verdicts)

* **Base ring**: everything is stated over `R₀ := Γ(S, ⊤)` (for the engine
  `S = Spec A`, so `R₀ ≅ A` via `ΓSpecIso`), with all module structures the
  `Module.compHom` along `p.appLE ⊤ W _` — *definitionally* the spelling of
  the pinned `CoherentSheafFlat` hypothesis of
  `P1RigidPushforwardStatement`, so the flatness hypothesis is consumed
  as-is (`flat_baseSections_of_coherentSheafFlat`).
* **`H¹` finiteness needs only the ladder** (Weil/Stichtenoth two-lattice,
  generalized from field to arbitrary base-ring coefficients): no
  noetherian hypothesis enters `module_finite_h1`.
* **`H⁰` finite generation is NOT obtainable from the ladder.**  The kernel
  `H⁰ = Γ(X, M)` embeds in the chart module `Γ(M, U₁)`, which is finite
  over the chart *ring* but not over `R₀`; the classical proofs of
  `H⁰`-finiteness for coherent modules on `ℙ¹_A` (Serre FAC §66; EGA III
  3.2.1; Stacks 01YS) all run through global generation by twists and the
  long exact sequence — Serre-finiteness-grade machinery that is out of
  scope here (cf. the T14 memory note: `sectionGradedModule_fg` is a deep
  leaf).  The `H⁰`-side finite generation is therefore consumed as the
  *named hypothesis* `hH0` by the §5 endgame skeleton and recorded as the
  remaining leaf of the B3 ℙ¹ engine; everything else in this file is
  proved.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

/-! ## §1. Base-linear Čech bookkeeping for a family `p : X ⟶ S`

The `Γ(S, ⊤)`-module structure on the section modules of a sheaf of modules
on the total space of a family, pinned once in the *definitional spelling*
of the `CoherentSheafFlat` hypothesis (`Module.compHom` along `p.appLE`),
and the resulting `Γ(S, ⊤)`-linear two-term Čech complex of a 2-affine
cover. -/

variable {X S : Scheme.{u}}

/-- **The `Γ(S, ⊤)`-module structure on module sections over the total space
of a family** `p : X ⟶ S`: restriction of scalars along the pullback ring
map `p.appLE ⊤ W : Γ(S, ⊤) ⟶ Γ(X, W)` (every open `W` satisfies
`W ≤ p ⁻¹ᵁ ⊤` definitionally).  This is the definitional spelling of the
module structure in the pinned `CoherentSheafFlat` predicate (there stated
over a general affine `U ⊆ S`; the engine consumes it at `U = ⊤` of the
affine base `Spec A`), so flatness hypotheses transport by `rfl`.  Not an
instance (the family `p` is not inferable); activate with
`letI := p.baseSectionsModule M W` — the `Scheme.Hom.fiberSectionsModule`
pattern. -/
@[reducible] noncomputable def Hom.baseSectionsModule (p : X ⟶ S) (M : X.Modules)
    (W : X.Opens) :
    Module Γ(S, ⊤) Γ(M, W) :=
  Module.compHom _ (p.appLE ⊤ W (le_top : W ≤ p ⁻¹ᵁ ⊤)).hom

/-- The scalar action of `baseSectionsModule`, definitionally. -/
lemma Hom.baseSectionsModule_smul_def (p : X ⟶ S) (M : X.Modules) (W : X.Opens)
    (r : Γ(S, ⊤)) (m : Γ(M, W)) :
    letI := p.baseSectionsModule M W
    r • m = (p.appLE ⊤ W (le_top : W ≤ p ⁻¹ᵁ ⊤)).hom r • m :=
  rfl

/-- **The section restrictions of `M` are `Γ(S, ⊤)`-linear** for the
`baseSectionsModule` structures: the presheaf restriction is semilinear over
the restriction of `𝒪_X` (`Scheme.Modules.map_smul`), and the two `appLE`
composites agree (`Scheme.Hom.appLE_map`). -/
lemma Hom.baseSections_res_smul (p : X ⟶ S) (M : X.Modules) {W W' : X.Opens}
    (h : W' ≤ W) (r : Γ(S, ⊤)) (m : Γ(M, W)) :
    letI := p.baseSectionsModule M W
    letI := p.baseSectionsModule M W'
    M.presheaf.map (homOfLE h).op (r • m) =
      r • M.presheaf.map (homOfLE h).op m := by
  letI := p.baseSectionsModule M W
  letI := p.baseSectionsModule M W'
  rw [p.baseSectionsModule_smul_def M W r m, Scheme.Modules.map_smul,
    p.baseSectionsModule_smul_def M W' r]
  congr 1
  have h1 := congrArg (fun φ : Γ(S, ⊤) ⟶ Γ(X, W') => φ.hom r)
    (p.appLE_map (le_top : W ≤ p ⁻¹ᵁ ⊤) (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
  exact h1

/-- **The bundled `Γ(S, ⊤)`-linear section restriction** of a module on the
total space of the family `p : X ⟶ S`, for the `baseSectionsModule`
structures.  (`restrictₗ` of `Picard/QuotScheme.lean` is the sibling over
the section ring of the source open; this one is linear over the base.) -/
noncomputable def Hom.baseSectionsRes (p : X ⟶ S) (M : X.Modules) {W W' : X.Opens}
    (h : W' ≤ W) :
    letI := p.baseSectionsModule M W
    letI := p.baseSectionsModule M W'
    Γ(M, W) →ₗ[Γ(S, ⊤)] Γ(M, W') :=
  letI := p.baseSectionsModule M W
  letI := p.baseSectionsModule M W'
  { toFun := fun m => M.presheaf.map (homOfLE h).op m
    map_add' := map_add _
    map_smul' := fun r m => p.baseSections_res_smul M h r m }

/-- The underlying function of `baseSectionsRes` is the presheaf restriction. -/
lemma Hom.baseSectionsRes_apply (p : X ⟶ S) (M : X.Modules) {W W' : X.Opens}
    (h : W' ≤ W) (m : Γ(M, W)) :
    p.baseSectionsRes M h m = M.presheaf.map (homOfLE h).op m :=
  rfl

/-- **The `Γ(S, ⊤)`-linear difference-of-restrictions map** of a 2-affine
cover, for a module `M` on the total space of the family `p : X ⟶ S`: the
linear upgrade of `AffineCoverMVSquare.moduleSectionDiff` for the
`baseSectionsModule` structures.  This is the two-term complex `d : M⁰ → M¹`
that the finite replacement `TwoTermFiniteReplacement` consumes. -/
noncomputable def AffineCoverMVSquare.moduleSectionDiffBase (V : X.AffineCoverMVSquare)
    (p : X ⟶ S) (M : X.Modules) :
    letI := p.baseSectionsModule M V.U₁
    letI := p.baseSectionsModule M V.U₂
    letI := p.baseSectionsModule M (V.U₁ ⊓ V.U₂)
    (Γ(M, V.U₁) × Γ(M, V.U₂)) →ₗ[Γ(S, ⊤)] Γ(M, V.U₁ ⊓ V.U₂) :=
  letI := p.baseSectionsModule M V.U₁
  letI := p.baseSectionsModule M V.U₂
  letI := p.baseSectionsModule M (V.U₁ ⊓ V.U₂)
  { toFun := V.moduleSectionDiff M
    map_add' := map_add _
    map_smul' := fun r q => by
      rcases q with ⟨a, b⟩
      simp only [V.moduleSectionDiff_apply M, RingHom.id_apply, Prod.smul_fst,
        Prod.smul_snd]
      rw [p.baseSections_res_smul M (inf_le_left : V.U₁ ⊓ V.U₂ ≤ V.U₁) r a,
        p.baseSections_res_smul M (inf_le_right : V.U₁ ⊓ V.U₂ ≤ V.U₂) r b,
        smul_sub] }

/-- The underlying function of `moduleSectionDiffBase` is `moduleSectionDiff`. -/
lemma AffineCoverMVSquare.moduleSectionDiffBase_apply (V : X.AffineCoverMVSquare)
    (p : X ⟶ S) (M : X.Modules) (q : Γ(M, V.U₁) × Γ(M, V.U₂)) :
    V.moduleSectionDiffBase p M q = V.moduleSectionDiff M q :=
  rfl

/-- **The `Γ(S, ⊤)`-linear pair-of-restrictions map** (degree-0 piece of the
two-term Čech complex): linear upgrade of
`AffineCoverMVSquare.moduleSectionRes`. -/
noncomputable def AffineCoverMVSquare.moduleSectionResBase (V : X.AffineCoverMVSquare)
    (p : X ⟶ S) (M : X.Modules) :
    letI := p.baseSectionsModule M (⊤ : X.Opens)
    letI := p.baseSectionsModule M V.U₁
    letI := p.baseSectionsModule M V.U₂
    Γ(M, (⊤ : X.Opens)) →ₗ[Γ(S, ⊤)] Γ(M, V.U₁) × Γ(M, V.U₂) :=
  letI := p.baseSectionsModule M (⊤ : X.Opens)
  letI := p.baseSectionsModule M V.U₁
  letI := p.baseSectionsModule M V.U₂
  { toFun := V.moduleSectionRes M
    map_add' := map_add _
    map_smul' := fun r m => by
      simp only [RingHom.id_apply]
      refine Prod.ext ?_ ?_
      · exact p.baseSections_res_smul M (le_top : V.U₁ ≤ ⊤) r m
      · exact p.baseSections_res_smul M (le_top : V.U₂ ≤ ⊤) r m }

/-- The underlying function of `moduleSectionResBase` is `moduleSectionRes`. -/
lemma AffineCoverMVSquare.moduleSectionResBase_apply (V : X.AffineCoverMVSquare)
    (p : X ⟶ S) (M : X.Modules) (m : Γ(M, (⊤ : X.Opens))) :
    V.moduleSectionResBase p M m = V.moduleSectionRes M m :=
  rfl

/-- **Flatness of the Čech chart modules, consumed from the pinned
`CoherentSheafFlat` hypothesis with zero transport** (work item 1(ii)): for
an affine base and an affine open `W` of the total space, the
`baseSectionsModule` structure on `Γ(M, W)` *is* the module structure of the
`CoherentSheafFlat` predicate at the pair `(⊤, W)`, so flatness follows by
proof irrelevance of the `appLE` inclusion. -/
theorem flat_baseSections_of_coherentSheafFlat [IsAffine S] (p : X ⟶ S)
    (M : X.Modules) (hflat : CoherentSheafFlat p M) {W : X.Opens}
    (hW : IsAffineOpen W) :
    letI := p.baseSectionsModule M W
    Module.Flat Γ(S, ⊤) Γ(M, W) :=
  hflat (isAffineOpen_top S) hW (le_top : W ≤ p ⁻¹ᵁ ⊤)

/-! ## §2. The kernel identification `Γ(X, M) ≃ ker d` (sheaf condition)

The `X.Modules`-dialect, base-linear form of
`AffineCoverMVSquare.globalSectionsEquivH0ₗ` (`RiemannRoch/CohomologyKit.lean`):
restriction into the pair of charts is injective (separatedness of the sheaf
`M.presheaf`) and hits every pair agreeing on the overlap (gluing), both on
the 2-element cover `{U₁, U₂}` of `⊤` (`pairFamily`). -/

/-- The pair of restrictions of a global section lies in the kernel of the
difference map (the two-term complex property, elementwise). -/
lemma AffineCoverMVSquare.moduleSectionResBase_mem_ker (V : X.AffineCoverMVSquare)
    (p : X ⟶ S) (M : X.Modules) (m : Γ(M, (⊤ : X.Opens))) :
    letI := p.baseSectionsModule M (⊤ : X.Opens)
    letI := p.baseSectionsModule M V.U₁
    letI := p.baseSectionsModule M V.U₂
    letI := p.baseSectionsModule M (V.U₁ ⊓ V.U₂)
    V.moduleSectionResBase p M m ∈ LinearMap.ker (V.moduleSectionDiffBase p M) := by
  letI := p.baseSectionsModule M (⊤ : X.Opens)
  letI := p.baseSectionsModule M V.U₁
  letI := p.baseSectionsModule M V.U₂
  letI := p.baseSectionsModule M (V.U₁ ⊓ V.U₂)
  rw [LinearMap.mem_ker]
  have h := congrArg (fun f => f m) (V.moduleSectionDiff_comp_moduleSectionRes M)
  exact h

set_option maxHeartbeats 400000 in
-- Heartbeat headroom for the sheaf-condition gluing across the
-- `Scheme.Opens`/`Opens X.toTopCat` presentation diamond (fleet recipe, as in
-- `globalSectionsEquivH0ₗ`).
/-- **The kernel identification (work item 1(i)): global sections are the
degree-0 Čech cohomology of the 2-affine cover.**  The corestriction of the
pair-of-restrictions map is a `Γ(S, ⊤)`-linear equivalence
`Γ(X, M) ≃ₗ ker (moduleSectionDiffBase)`: injective by separatedness of the
sheaf `M.presheaf`, surjective onto the kernel by the gluing axiom, both on
the 2-element cover `{U₁, U₂}` of `⊤`.  This identifies the `H⁰` of the
two-term complex consumed by the finite replacement with the pushforward
sections `Γ(S, p_* M) = Γ(X, M)`. -/
noncomputable def AffineCoverMVSquare.globalSectionsEquivKerModuleSectionDiffBase
    (V : X.AffineCoverMVSquare) (p : X ⟶ S) (M : X.Modules) :
    letI := p.baseSectionsModule M (⊤ : X.Opens)
    letI := p.baseSectionsModule M V.U₁
    letI := p.baseSectionsModule M V.U₂
    letI := p.baseSectionsModule M (V.U₁ ⊓ V.U₂)
    Γ(M, (⊤ : X.Opens)) ≃ₗ[Γ(S, ⊤)] LinearMap.ker (V.moduleSectionDiffBase p M) :=
  letI := p.baseSectionsModule M (⊤ : X.Opens)
  letI := p.baseSectionsModule M V.U₁
  letI := p.baseSectionsModule M V.U₂
  letI := p.baseSectionsModule M (V.U₁ ⊓ V.U₂)
  LinearEquiv.ofBijective
    ((V.moduleSectionResBase p M).codRestrict (LinearMap.ker (V.moduleSectionDiffBase p M))
      fun m => V.moduleSectionResBase_mem_ker p M m)
    (by
      constructor
      · intro s t hst
        have h := Subtype.ext_iff.mp hst
        have h1 : (M.presheaf.map (homOfLE (le_top : V.U₁ ≤ ⊤)).op).hom s =
            (M.presheaf.map (homOfLE (le_top : V.U₁ ≤ ⊤)).op).hom t :=
          congrArg Prod.fst h
        have h2 : (M.presheaf.map (homOfLE (le_top : V.U₂ ≤ ⊤)).op).hom s =
            (M.presheaf.map (homOfLE (le_top : V.U₂ ≤ ⊤)).op).hom t :=
          congrArg Prod.snd h
        refine TopCat.Sheaf.eq_of_locally_eq'
          (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
          V.pairFamily ⊤ (fun i => homOfLE le_top) V.le_iSup_pairFamily s t ?_
        rintro ⟨(_ | _)⟩
        · exact h2
        · exact h1
      · rintro ⟨⟨a, b⟩, hab⟩
        have hab' : (M.presheaf.map
              (homOfLE (inf_le_left : V.U₁ ⊓ V.U₂ ≤ V.U₁)).op).hom a =
            (M.presheaf.map
              (homOfLE (inf_le_right : V.U₁ ⊓ V.U₂ ≤ V.U₂)).op).hom b := by
          have h := LinearMap.mem_ker.mp hab
          rw [V.moduleSectionDiffBase_apply p M, V.moduleSectionDiff_apply M] at h
          exact sub_eq_zero.mp h
        -- the compatible family indexed by `{U₁, U₂}`
        set sf : ∀ i : ULift.{u} Bool, Γ(M, V.pairFamily i) :=
          fun i => match i with
            | ⟨true⟩ => a
            | ⟨false⟩ => b with hsf
        have hcompat : TopCat.Presheaf.IsCompatible M.presheaf V.pairFamily sf := by
          intro i j
          have key : ∀ {U W W' : X.Opens} (hUV : W' ≤ U ⊓ W)
              (x : Γ(M, U)) (y : Γ(M, W)),
              (M.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op).hom x =
                (M.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op).hom y →
              (M.presheaf.map (homOfLE (hUV.trans inf_le_left)).op).hom x =
                (M.presheaf.map (homOfLE (hUV.trans inf_le_right)).op).hom y := by
            intro U W W' hUV x y hxy
            have hx : (M.presheaf.map (homOfLE (hUV.trans inf_le_left)).op).hom x =
                (M.presheaf.map (homOfLE hUV).op).hom
                  ((M.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op).hom x) := by
              have := M.presheaf.map_comp
                (homOfLE (inf_le_left : U ⊓ W ≤ U)).op (homOfLE hUV).op
              exact (congrArg (fun f => (ConcreteCategory.hom f) x) this).trans rfl
            have hy : (M.presheaf.map (homOfLE (hUV.trans inf_le_right)).op).hom y =
                (M.presheaf.map (homOfLE hUV).op).hom
                  ((M.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op).hom y) := by
              have := M.presheaf.map_comp
                (homOfLE (inf_le_right : U ⊓ W ≤ W)).op (homOfLE hUV).op
              exact (congrArg (fun f => (ConcreteCategory.hom f) y) this).trans rfl
            rw [hx, hy, hxy]
          obtain ⟨bi⟩ := i
          obtain ⟨bj⟩ := j
          cases bi <;> cases bj
          · -- (U₂, U₂): both maps agree by proof irrelevance of `≤`
            exact congrArg
              (fun g => (ConcreteCategory.hom (M.presheaf.map (Quiver.Hom.op g))) b)
              (Subsingleton.elim _ _)
          · -- (U₂, U₁): restrict the overlap agreement along `U₂ ⊓ U₁ ≤ U₁ ⊓ U₂`
            exact (key (le_inf inf_le_right inf_le_left) a b hab').symm
          · -- (U₁, U₂): the overlap agreement itself
            exact key le_rfl a b hab'
          · -- (U₁, U₁): both maps agree by proof irrelevance of `≤`
            exact congrArg
              (fun g => (ConcreteCategory.hom (M.presheaf.map (Quiver.Hom.op g))) a)
              (Subsingleton.elim _ _)
        obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing'
          (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
          V.pairFamily ⊤ (fun _ => homOfLE le_top) V.le_iSup_pairFamily sf hcompat
        refine ⟨s, ?_⟩
        apply Subtype.ext
        exact Prod.ext (hs ⟨true⟩) (hs ⟨false⟩))

end Scheme

namespace Adelic

/-! ## §3a. The abstract two-lattice core, module coefficients

The Weil/Stichtenoth two-lattice engine of
`RiemannRoch/Adelic/FinitenessP1.lean` (`module_finite_quotient_of_laurent_pair`)
generalized from a commutative `k`-algebra to a **module** `M` over a
commutative ring `C` containing the Laurent pair `t * u = 1`, with lattices
that are submodules over an auxiliary base ring `A` acting compatibly
(`SMulCommClass A C M`) — the shape induced on the overlap section module
`Γ(M, U₁ ⊓ U₂)` by the pulled-back ℙ¹ coordinates.  No noetherian or
finiteness hypothesis on `A` enters. -/

section SmulTwoLattice

variable {A : Type*} [CommRing A] {C : Type*} [CommRing C]
variable {M : Type*} [AddCommGroup M] [Module A M] [Module C M] [SMulCommClass A C M]

/-- Scalar multiplication by `c : C` as an `A`-linear endomorphism (the
compatibility `SMulCommClass A C M` is exactly its `A`-linearity). -/
def smulALinear (A : Type*) [CommRing A] {C : Type*} [CommRing C]
    {M : Type*} [AddCommGroup M] [Module A M] [Module C M] [SMulCommClass A C M]
    (c : C) : M →ₗ[A] M where
  toFun := fun m => c • m
  map_add' := smul_add c
  map_smul' := fun a m => (smul_comm a c m).symm

@[simp] lemma smulALinear_apply (c : C) (m : M) : smulALinear A c m = c • m := rfl

omit [SMulCommClass A C M] in
/-- Iterated stability, module coefficients: an `A`-submodule stable under
scalar multiplication by `t : C` is stable under every power `t ^ n`.
(`Adelic.pow_mul_mem`, module dialect.) -/
lemma pow_smul_mem {N : Submodule A M} {t : C} (h : ∀ a ∈ N, t • a ∈ N)
    (n : ℕ) {a : M} (ha : a ∈ N) : t ^ n • a ∈ N := by
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    have hrw : t ^ (n + 1) • a = t • (t ^ n • a) := by
      rw [smul_smul, pow_succ, mul_comm]
    rw [hrw]
    exact h _ ih

/-- **Ladder-spanning producer, module coefficients**
(`Adelic.span_ladder_of_pow_mul_mem_span`, module dialect): if `t * u = 1`
in `C` and every `m ∈ M` satisfies `t ^ n • m ∈ span_A {t^j • a : a ∈ s}`
for some `n`, then the full two-sided ladder spans `M` over `A`. -/
theorem span_smul_ladder_of_pow_smul_mem_span {t u : C} (htu : t * u = 1) (s : Set M)
    (H : ∀ m : M, ∃ n : ℕ,
      t ^ n • m ∈ Submodule.span A (⋃ j : ℕ, (fun z => t ^ j • z) '' s)) :
    ⊤ ≤ Submodule.span A
      ((⋃ j : ℕ, (fun z => t ^ j • z) '' s) ∪ (⋃ j : ℕ, (fun z => u ^ j • z) '' s)) := by
  have hpow : ∀ n : ℕ, u ^ n * t ^ n = 1 := fun n => by
    rw [← mul_pow, mul_comm u t, htu, one_pow]
  intro m _
  obtain ⟨n, hn⟩ := H m
  have hm : m = u ^ n • (t ^ n • m) := by
    rw [smul_smul, hpow, one_smul]
  have hmem : u ^ n • (t ^ n • m) ∈ Submodule.map (smulALinear A (u ^ n))
      (Submodule.span A (⋃ j : ℕ, (fun z => t ^ j • z) '' s)) :=
    Submodule.mem_map_of_mem hn
  rw [Submodule.map_span, ← hm] at hmem
  refine Submodule.span_le.mpr ?_ hmem
  rintro _ ⟨z, hz, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_image] at hz
  obtain ⟨j, a, ha, rfl⟩ := hz
  simp only [smulALinear_apply]
  rcases le_or_gt n j with hnj | hjn
  · -- `u^n • (t^j • a) = t^(j-n) • a`
    have key : u ^ n • (t ^ j • a) = t ^ (j - n) • a := by
      have hj : t ^ j = t ^ n * t ^ (j - n) := by
        rw [← pow_add]
        congr 1
        omega
      rw [smul_smul, hj, ← mul_assoc, hpow, one_mul]
    rw [key]
    exact Submodule.subset_span (Or.inl (Set.mem_iUnion.mpr
      ⟨j - n, Set.mem_image_of_mem _ ha⟩))
  · -- `u^n • (t^j • a) = u^(n-j) • a`
    have key : u ^ n • (t ^ j • a) = u ^ (n - j) • a := by
      have hn' : u ^ n = u ^ (n - j) * u ^ j := by
        rw [← pow_add]
        congr 1
        omega
      rw [smul_smul, hn', mul_assoc, hpow, mul_one]
    rw [key]
    exact Submodule.subset_span (Or.inr (Set.mem_iUnion.mpr
      ⟨n - j, Set.mem_image_of_mem _ ha⟩))

omit [SMulCommClass A C M] in
/-- **The abstract two-lattice core, module coefficients**
(`Adelic.module_finite_quotient_of_laurent_pair`, module dialect — the
algebraic heart of the A-coefficient `H¹`-finiteness of ℙ¹_A).  For a
Laurent pair `t * u = 1` in `C` acting on the `A`-module `M`, a `t`-stable
lattice `N₀` and a `u`-stable lattice `N₁`, a finite `s ⊆ N₀` whose
two-sided ladder spans `M` over `A`, and the extension property (`u`-powers
of `s` land in `N₁`), the cokernel `M ⧸ (N₀ ⊔ N₁)` is a finite `A`-module.
(As in the field-coefficient original, the Laurent relation `t * u = 1`
enters only through the spanning hypothesis `hspan`, produced by
`span_smul_ladder_of_pow_smul_mem_span`.) -/
theorem module_finite_quotient_of_smul_laurent_pair {t u : C}
    {N₀ N₁ : Submodule A M}
    (h₀ : ∀ a ∈ N₀, t • a ∈ N₀) (h₁ : ∀ a ∈ N₁, u • a ∈ N₁)
    {s : Set M} (hs : s.Finite) (hsN₀ : s ⊆ N₀)
    (hspan : ⊤ ≤ Submodule.span A
      ((⋃ j : ℕ, (fun z => t ^ j • z) '' s) ∪ (⋃ j : ℕ, (fun z => u ^ j • z) '' s)))
    (hext : ∀ a ∈ s, ∃ n : ℕ, u ^ n • a ∈ N₁) :
    Module.Finite A (M ⧸ (N₀ ⊔ N₁)) := by
  classical
  -- a uniform extension bound over the finite set `s`
  set B : M → ℕ := fun a => if h : a ∈ s then (hext a h).choose else 0 with hB
  set N : ℕ := hs.toFinset.sup B with hNdef
  have hBmem : ∀ a ∈ s, u ^ B a • a ∈ N₁ := by
    intro a ha
    simp only [hB, dif_pos ha]
    exact (hext a ha).choose_spec
  have hN₁ : ∀ a ∈ s, ∀ n : ℕ, B a ≤ n → u ^ n • a ∈ N₁ := by
    intro a ha n hn
    have hrw : u ^ n • a = u ^ (n - B a) • (u ^ B a • a) := by
      rw [smul_smul, ← pow_add]
      congr 2
      omega
    rw [hrw]
    exact pow_smul_mem h₁ _ (hBmem a ha)
  -- the finite middle band
  set T : Set M := ⋃ j ∈ Finset.range N, (fun z => u ^ j • z) '' s with hT
  have hTfin : T.Finite :=
    Set.Finite.biUnion (Finset.range N).finite_toSet fun j _ => hs.image _
  -- the middle band together with the two lattices spans everything
  have hkey : N₀ ⊔ N₁ ⊔ Submodule.span A T = ⊤ := by
    refine le_antisymm le_top (hspan.trans (Submodule.span_le.mpr ?_))
    rintro z (hz | hz) <;> simp only [Set.mem_iUnion, Set.mem_image] at hz
    · obtain ⟨j, a, ha, rfl⟩ := hz
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (pow_smul_mem h₀ j (hsN₀ ha)))
    · obtain ⟨j, a, ha, rfl⟩ := hz
      rcases lt_or_ge j N with hj | hj
      · refine Submodule.mem_sup_right (Submodule.subset_span ?_)
        simp only [hT, Set.mem_iUnion, Set.mem_image]
        exact ⟨j, Finset.mem_range.mpr hj, a, ha, rfl⟩
      · refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
        exact hN₁ a ha j (le_trans (Finset.le_sup (hs.mem_toFinset.mpr ha)) hj)
  -- pass to the quotient: the image of the middle band spans it
  have himg : Submodule.span A (⇑(N₀ ⊔ N₁).mkQ '' T) = ⊤ := by
    rw [Submodule.span_image]
    have h1 : Submodule.map (N₀ ⊔ N₁).mkQ (N₀ ⊔ N₁) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨y, hy, rfl⟩
      simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hy
    have h2 := congrArg (Submodule.map (N₀ ⊔ N₁).mkQ) hkey
    rw [Submodule.map_sup, h1, bot_sup_eq, Submodule.map_top, Submodule.range_mkQ] at h2
    exact h2
  have hfg : (⊤ : Submodule A (M ⧸ (N₀ ⊔ N₁))).FG :=
    ⟨(hTfin.image _).toFinset, by rw [Set.Finite.coe_toFinset]; exact himg⟩
  exact ⟨hfg⟩

end SmulTwoLattice

/-! ## §3b. The chart-ladder producer, module coefficients -/

section ChartSpan

variable {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
variable {MM : Type*} [AddCommGroup MM] [Module C MM] [Module A MM] [IsScalarTower A C MM]

/-- The `A`-span of a `⋃ₙ (xⁿ • ·)`-ladder is stable under scalars from the
`A`-span of the powers of `x` — the multiplicative step of the chart-ladder
producer, module coefficients. -/
lemma smul_mem_span_smul_ladder (x : C) {r : C}
    (hr : r ∈ Submodule.span A (Set.range fun n : ℕ => x ^ n))
    {G : Set MM} {m : MM}
    (hm : m ∈ Submodule.span A (⋃ n : ℕ, (fun z => x ^ n • z) '' G)) :
    r • m ∈ Submodule.span A (⋃ n : ℕ, (fun z => x ^ n • z) '' G) := by
  induction hr using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, rfl⟩ := hw
    induction hm using Submodule.span_induction with
    | mem z hz =>
      simp only [Set.mem_iUnion, Set.mem_image] at hz
      obtain ⟨b, g, hg, rfl⟩ := hz
      rw [smul_smul, ← pow_add]
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨a + b, ⟨g, hg, rfl⟩⟩)
    | zero => rw [smul_zero]; exact zero_mem _
    | add y z _ _ ihy ihz => rw [smul_add]; exact add_mem ihy ihz
    | smul a₀ y _ ihy =>
      rw [smul_comm]
      exact Submodule.smul_mem _ _ ihy
  | zero => rw [zero_smul]; exact zero_mem _
  | add r₁ r₂ _ _ ih₁ ih₂ => rw [add_smul]; exact add_mem ih₁ ih₂
  | smul a₀ r₁ _ ih₁ =>
    rw [smul_assoc]
    exact Submodule.smul_mem _ _ ih₁

/-- **Chart-ladder producer, module coefficients**
(`Adelic.exists_finset_forall_mem_span_pow_mul`, module dialect): if the
chart ring `C` is spanned over `A` by the powers of `x` and the section
module `MM` is module-finite over `C`, then `MM` is spanned over `A` by the
ladder `{xⁿ • g}` over a finite set of generators `g ∈ G`. -/
theorem exists_finset_forall_mem_span_pow_smul (x : C)
    (hx : ⊤ ≤ Submodule.span A (Set.range fun n : ℕ => x ^ n))
    [hfin : Module.Finite C MM] :
    ∃ G : Finset MM, ∀ m : MM,
      m ∈ Submodule.span A (⋃ n : ℕ, (fun z => x ^ n • z) '' (G : Set MM)) := by
  obtain ⟨G, hG⟩ := Module.finite_def.mp hfin
  refine ⟨G, fun m => ?_⟩
  have hm : m ∈ Submodule.span C (G : Set MM) := by rw [hG]; trivial
  induction hm using Submodule.span_induction with
  | mem z hz =>
    refine Submodule.subset_span (Set.mem_iUnion.mpr ⟨0, ⟨z, hz, ?_⟩⟩)
    rw [pow_zero]
    exact one_smul C z
  | zero => exact zero_mem _
  | add y z _ _ ihy ihz => exact add_mem ihy ihz
  | smul r z _ ihz => exact smul_mem_span_smul_ladder x (hx trivial) ihz

end ChartSpan

end Adelic

/-! ## §3c. The module-section extension lemma over an affine chart -/

namespace Scheme.Modules

/-- **The module-section extension lemma** (`Adelic.exists_pow_mul_eq_res`,
`X.Modules` dialect; Stacks 01PC-grade).  Let `U` be an affine open of `X`,
`f ∈ Γ(X, U)`, `W = D(f)` (recorded as an arbitrary open equal to the basic
open, so callers need not transport), and `M` quasi-coherent.  Then every
section `m ∈ Γ(M, W)` becomes, after scalar multiplication by a power of
`f|_W`, the restriction of a section over the chart: sections of the
localized module extend after multiplying by a power of `f`.  From the qcqs
section-localization engine `isLocalizedModule_basicOpen_of_isCompact`
(`Picard/QuotScheme.lean`) at the (compact, quasi-separated) affine `U`. -/
theorem exists_pow_smul_eq_res {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    {U W : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) (hW : W = X.basicOpen f)
    (hWU : W ≤ U) (m : Γ(M, W)) :
    ∃ (n : ℕ) (a : Γ(M, U)),
      (X.presheaf.map (homOfLE hWU).op).hom f ^ n • m
        = M.presheaf.map (homOfLE hWU).op a := by
  subst hW
  letI : Module Γ(X, U) Γ(M, X.basicOpen f) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
  letI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI := isLocalizedModule_basicOpen_of_isCompact M hU.isCompact
    hU.isQuasiSeparated f
  obtain ⟨⟨a, s⟩, hsurj⟩ := IsLocalizedModule.surj (Submonoid.powers f)
    (restrictBasicOpenₗ M f) m
  obtain ⟨n, hn⟩ := s.2
  refine ⟨n, a, ?_⟩
  -- `s • m = res a`, `s = f ^ n`, and the `Γ(X, U)`-action is through the
  -- restriction ring map, so `s • m = (f|_W)^n • m`.
  have hn' : (f ^ n : Γ(X, U)) = (s : Γ(X, U)) := hn
  have h1 : ((f ^ n : Γ(X, U)) • m : Γ(M, X.basicOpen f))
      = restrictBasicOpenₗ M f a := by
    rw [hn']
    exact hsurj
  have h2 : ((f ^ n : Γ(X, U)) • m : Γ(M, X.basicOpen f))
      = (X.presheaf.map (homOfLE hWU).op).hom f ^ n • m := by
    rw [← map_pow]
    rfl
  rw [← h2, h1]
  rfl

end Scheme.Modules

/-! ## §3d. Relative Laurent chart data and the `H¹`-finiteness keystone -/

namespace Scheme

/-- **Relative Laurent chart data for a family `p : X ⟶ S`** — the
base-linear dialect of `Adelic.LaurentChartData`: a 2-affine cover of the
total space with mutually inverse coordinates on the overlap, each chart
*ring* being spanned over the base ring `Γ(S, ⊤)` (acting through
`p.appLE`) by the powers of its coordinate.  For `X = ℙ¹_A ⟶ S = Spec A`
this is the standard two-chart structure with `Γ(U₁) = A[x]`,
`Γ(U₂) = A[y]`, `Γ(U₁ ⊓ U₂) = A[x, x⁻¹]`. -/
structure RelLaurentChartData {X S : Scheme.{u}} (p : X ⟶ S) : Type u where
  /-- The underlying 2-affine cover square. -/
  V : X.AffineCoverMVSquare
  /-- The coordinate on the first chart. -/
  x : Γ(X, V.U₁)
  /-- The coordinate on the second chart. -/
  y : Γ(X, V.U₂)
  /-- The overlap is the basic open of `x`. -/
  inf_eq_basicOpen_x : V.U₁ ⊓ V.U₂ = X.basicOpen x
  /-- The overlap is the basic open of `y`. -/
  inf_eq_basicOpen_y : V.U₁ ⊓ V.U₂ = X.basicOpen y
  /-- The coordinates are mutually inverse on the overlap: `x · y = 1`. -/
  res_x_mul_res_y :
    (X.presheaf.map (homOfLE (inf_le_left : V.U₁ ⊓ V.U₂ ≤ V.U₁)).op).hom x
      * (X.presheaf.map (homOfLE (inf_le_right : V.U₁ ⊓ V.U₂ ≤ V.U₂)).op).hom y = 1
  /-- The first chart ring is spanned over the base by the powers of `x`
  (`Γ(U₁) = Γ(S, ⊤)[x]` as a module). -/
  span_pow_x :
    letI := ((p.appLE ⊤ V.U₁ (le_top : V.U₁ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
    ⊤ ≤ Submodule.span Γ(S, ⊤) (Set.range fun n : ℕ => x ^ n)
  /-- The second chart ring is spanned over the base by the powers of `y`
  (`Γ(U₂) = Γ(S, ⊤)[y]` as a module). -/
  span_pow_y :
    letI := ((p.appLE ⊤ V.U₂ (le_top : V.U₂ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
    ⊤ ≤ Submodule.span Γ(S, ⊤) (Set.range fun n : ℕ => y ^ n)

set_option maxHeartbeats 800000 in
-- `maxHeartbeats`: the proof repeatedly crosses the `Γ`-carrier and
-- `Module.compHom` identifications, as in the field-coefficient original
-- (`LaurentChartData.module_finite_H1Cok`, fleet elaboration recipe).
/-- **The `H¹`-finiteness keystone, A-coefficients (work item 2, `H¹`
half).**  For a family `p : X ⟶ S` with relative Laurent chart data `D` and
a quasi-coherent module `M` on `X` whose chart section modules are finite
over the chart rings (true for any finitely presented `M`,
`module_finite_sections_of_isFinitePresentation`), the concrete Čech `Ȟ¹`
of the cover — the cokernel of the base-linear difference map — is a
**finite `Γ(S, ⊤)`-module**.

This is the Weil/Stichtenoth two-lattice argument of
`Adelic.LaurentChartData.module_finite_H1Cok` with the base field replaced
by the base ring: `Γ(M, U₁)` is spanned over `Γ(S, ⊤)` by the ladder
`{xⁿ • gᵢ}` (chart-ladder producer over `Γ(U₁) = Γ(S,⊤)[x]`), the overlap
module is its localization at `x` (extension lemma), positive rungs come
from `Γ(M, U₁)`, sufficiently negative rungs from `Γ(M, U₂)`, and the
finite middle band spans the cokernel.  No noetherian hypothesis on the
base enters. -/
theorem RelLaurentChartData.module_finite_h1 {X S : Scheme.{u}} {p : X ⟶ S}
    (D : RelLaurentChartData p) (M : X.Modules) [M.IsQuasicoherent]
    (hfin₁ : Module.Finite Γ(X, D.V.U₁) Γ(M, D.V.U₁)) :
    letI := p.baseSectionsModule M D.V.U₁
    letI := p.baseSectionsModule M D.V.U₂
    letI := p.baseSectionsModule M (D.V.U₁ ⊓ D.V.U₂)
    Module.Finite Γ(S, ⊤)
      (Γ(M, D.V.U₁ ⊓ D.V.U₂) ⧸ LinearMap.range (D.V.moduleSectionDiffBase p M)) := by
  classical
  letI := p.baseSectionsModule M D.V.U₁
  letI := p.baseSectionsModule M D.V.U₂
  letI := p.baseSectionsModule M (D.V.U₁ ⊓ D.V.U₂)
  -- ### The compatible base action on the overlap module
  haveI hscc : SMulCommClass Γ(S, ⊤) Γ(X, D.V.U₁ ⊓ D.V.U₂) Γ(M, D.V.U₁ ⊓ D.V.U₂) := by
    constructor
    intro r c m
    change (p.appLE ⊤ (D.V.U₁ ⊓ D.V.U₂) le_top).hom r • (c • m)
      = c • ((p.appLE ⊤ (D.V.U₁ ⊓ D.V.U₂) le_top).hom r • m)
    rw [smul_smul, smul_smul, mul_comm]
  -- ### Notation: the linear restrictions and the overlap Laurent pair
  set σ₀ := p.baseSectionsRes M (inf_le_left : D.V.U₁ ⊓ D.V.U₂ ≤ D.V.U₁) with hσ₀
  set σ₁ := p.baseSectionsRes M (inf_le_right : D.V.U₁ ⊓ D.V.U₂ ≤ D.V.U₂) with hσ₁
  set t := (X.presheaf.map
    (homOfLE (inf_le_left : D.V.U₁ ⊓ D.V.U₂ ≤ D.V.U₁)).op).hom D.x with ht
  set u := (X.presheaf.map
    (homOfLE (inf_le_right : D.V.U₁ ⊓ D.V.U₂ ≤ D.V.U₂)).op).hom D.y with hu
  have htu : t * u = 1 := D.res_x_mul_res_y
  -- ### Restrictions intertwine the coordinate actions with the Laurent pair
  have hres₀ : ∀ (j : ℕ) (b : Γ(M, D.V.U₁)), σ₀ (D.x ^ j • b) = t ^ j • σ₀ b := by
    intro j b
    rw [hσ₀, p.baseSectionsRes_apply, p.baseSectionsRes_apply,
      Scheme.Modules.map_smul, map_pow, ht]
  have hres₁ : ∀ (j : ℕ) (b : Γ(M, D.V.U₂)), σ₁ (D.y ^ j • b) = u ^ j • σ₁ b := by
    intro j b
    rw [hσ₁, p.baseSectionsRes_apply, p.baseSectionsRes_apply,
      Scheme.Modules.map_smul, map_pow, hu]
  -- ### The two lattices and their stability
  have h₀ : ∀ a ∈ LinearMap.range σ₀, t • a ∈ LinearMap.range σ₀ := by
    rintro _ ⟨b, rfl⟩
    refine ⟨D.x • b, ?_⟩
    have := hres₀ 1 b
    rw [pow_one, pow_one] at this
    exact this
  have h₁ : ∀ a ∈ LinearMap.range σ₁, u • a ∈ LinearMap.range σ₁ := by
    rintro _ ⟨b, rfl⟩
    refine ⟨D.y • b, ?_⟩
    have := hres₁ 1 b
    rw [pow_one, pow_one] at this
    exact this
  -- ### Chart-0 generators (ladder producer over `Γ(U₁) = Γ(S,⊤)[x]`)
  letI : Algebra Γ(S, ⊤) Γ(X, D.V.U₁) :=
    ((p.appLE ⊤ D.V.U₁ (le_top : D.V.U₁ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
  haveI : IsScalarTower Γ(S, ⊤) Γ(X, D.V.U₁) Γ(M, D.V.U₁) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI := hfin₁
  obtain ⟨G, hG⟩ := Adelic.exists_finset_forall_mem_span_pow_smul
    (A := Γ(S, ⊤)) (MM := Γ(M, D.V.U₁)) D.x D.span_pow_x
  -- ### The extension lemmas at the two charts
  have hext₀ : ∀ m : Γ(M, D.V.U₁ ⊓ D.V.U₂),
      ∃ (n : ℕ) (a : Γ(M, D.V.U₁)), t ^ n • m = σ₀ a := by
    intro m
    obtain ⟨n, a, ha⟩ := Scheme.Modules.exists_pow_smul_eq_res M
      D.V.isAffineOpen_U₁ D.x D.inf_eq_basicOpen_x inf_le_left m
    exact ⟨n, a, by rw [ht, hσ₀]; exact ha⟩
  have hext₁ : ∀ m : Γ(M, D.V.U₁ ⊓ D.V.U₂),
      ∃ (n : ℕ) (b : Γ(M, D.V.U₂)), u ^ n • m = σ₁ b := by
    intro m
    obtain ⟨n, b, hb⟩ := Scheme.Modules.exists_pow_smul_eq_res M
      D.V.isAffineOpen_U₂ D.y D.inf_eq_basicOpen_y inf_le_right m
    exact ⟨n, b, by rw [hu, hσ₁]; exact hb⟩
  -- ### The ladder over the images of the generators spans the overlap module
  have Hpow : ∀ m : Γ(M, D.V.U₁ ⊓ D.V.U₂), ∃ n : ℕ,
      t ^ n • m ∈ Submodule.span Γ(S, ⊤)
        (⋃ j : ℕ, (fun z => t ^ j • z) '' (⇑σ₀ '' (G : Set Γ(M, D.V.U₁)))) := by
    intro m
    obtain ⟨n, a, ha⟩ := hext₀ m
    refine ⟨n, ?_⟩
    rw [ha]
    have h1 : σ₀ a ∈ Submodule.map σ₀ (Submodule.span Γ(S, ⊤)
        (⋃ j : ℕ, (fun z => D.x ^ j • z) '' (G : Set Γ(M, D.V.U₁)))) :=
      Submodule.mem_map_of_mem (hG a)
    rw [Submodule.map_span] at h1
    refine Submodule.span_le.mpr ?_ h1
    rintro _ ⟨z, hz, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_image] at hz
    obtain ⟨j, g, hg, rfl⟩ := hz
    refine Submodule.subset_span (Set.mem_iUnion.mpr ⟨j, ⟨σ₀ g, ⟨g, hg, rfl⟩, ?_⟩⟩)
    exact (hres₀ j g).symm
  have hspan : ⊤ ≤ Submodule.span Γ(S, ⊤)
      ((⋃ j : ℕ, (fun z => t ^ j • z) '' (⇑σ₀ '' (G : Set Γ(M, D.V.U₁))))
        ∪ (⋃ j : ℕ, (fun z => u ^ j • z) '' (⇑σ₀ '' (G : Set Γ(M, D.V.U₁))))) :=
    Adelic.span_smul_ladder_of_pow_smul_mem_span htu _ Hpow
  -- ### The remaining hypotheses of the two-lattice core
  have hsfin : (⇑σ₀ '' (G : Set Γ(M, D.V.U₁))).Finite := G.finite_toSet.image _
  have hsN₀ : ⇑σ₀ '' (G : Set Γ(M, D.V.U₁)) ⊆ (LinearMap.range σ₀ : Set _) := by
    rintro _ ⟨g, _, rfl⟩
    exact ⟨g, rfl⟩
  have hext : ∀ a ∈ ⇑σ₀ '' (G : Set Γ(M, D.V.U₁)),
      ∃ n : ℕ, u ^ n • a ∈ LinearMap.range σ₁ := by
    intro a _
    obtain ⟨n, b, hb⟩ := hext₁ a
    exact ⟨n, b, hb.symm⟩
  -- ### The two-lattice core
  have hcore : Module.Finite Γ(S, ⊤)
      (Γ(M, D.V.U₁ ⊓ D.V.U₂) ⧸ (LinearMap.range σ₀ ⊔ LinearMap.range σ₁)) :=
    Adelic.module_finite_quotient_of_smul_laurent_pair h₀ h₁ hsfin hsN₀ hspan hext
  -- ### The Čech difference range is the sum of the two lattices
  have hrange : LinearMap.range σ₀ ⊔ LinearMap.range σ₁
      = LinearMap.range (D.V.moduleSectionDiffBase p M) := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · have hcomp₀ : σ₀ = (D.V.moduleSectionDiffBase p M).comp
            (LinearMap.inl Γ(S, ⊤) Γ(M, D.V.U₁) Γ(M, D.V.U₂)) := by
          ext a
          have : D.V.moduleSectionDiffBase p M (a, 0)
              = σ₀ a - σ₁ 0 := rfl
          rw [LinearMap.comp_apply, LinearMap.inl_apply, this, map_zero, sub_zero]
        rw [hcomp₀]
        exact LinearMap.range_comp_le_range _ _
      · have hcomp₁ : -σ₁ = (D.V.moduleSectionDiffBase p M).comp
            (LinearMap.inr Γ(S, ⊤) Γ(M, D.V.U₁) Γ(M, D.V.U₂)) := by
          ext b
          have : D.V.moduleSectionDiffBase p M (0, b)
              = σ₀ 0 - σ₁ b := rfl
          rw [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.inr_apply, this,
            map_zero, zero_sub]
        rw [← LinearMap.range_neg σ₁, hcomp₁]
        exact LinearMap.range_comp_le_range _ _
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      have : D.V.moduleSectionDiffBase p M (a, b) = σ₀ a - σ₁ b := rfl
      rw [this]
      exact sub_mem (Submodule.mem_sup_left ⟨a, rfl⟩) (Submodule.mem_sup_right ⟨b, rfl⟩)
  rw [hrange] at hcore
  exact hcore

end Scheme

/-! ## §4a. Transferring chart-ring spans along an affine base change

The `Γ(S, ⊤)`-span of the powers of a chart coordinate transfers along a
pullback square with affine (opposite) corners: the base-changed chart ring
is the ring pushout of the original chart ring and the new base ring
(`isIso_pushoutSection_of_isAffineOpen`, the char-free Route B of
`RiemannRoch/Adelic/P1ChartData.lean`), so it is ring-generated by the two
structural images, each of which lands in the span of the powers of the
pulled-back coordinate. -/

namespace Adelic

/-- **Bridging `k`-spans to base-ring spans**: for a `Spec k`-scheme `C` and
an open `U`, a subset spanning `Γ(C, U)` over `k` (structure-morphism
`algebraSection` action) spans it over the section ring `Γ(Spec k, ⊤)`
(acting through `C.hom.appLE`): the two actions are intertwined by the
(global-sections) ring isomorphism `ΓSpecIso`, definitionally. -/
theorem span_section_base_of_span_k {k : Type u} [CommRing k]
    {C : Over (Spec (CommRingCat.of k))} {U : C.left.Opens}
    (s : Set Γ(C.left, U)) (h : ⊤ ≤ Submodule.span k s) :
    letI := ((C.hom.appLE ⊤ U (le_top : U ≤ C.hom ⁻¹ᵁ ⊤)).hom).toAlgebra
    ⊤ ≤ Submodule.span Γ(Spec (CommRingCat.of k), ⊤) s := by
  letI := ((C.hom.appLE ⊤ U (le_top : U ≤ C.hom ⁻¹ᵁ ⊤)).hom).toAlgebra
  intro m hmtop
  clear hmtop
  have hm : m ∈ Submodule.span k s := h trivial
  induction hm using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span hz
  | zero => exact Submodule.zero_mem _
  | add y z _ _ ihy ihz => exact Submodule.add_mem _ ihy ihz
  | smul c w _ ih =>
    have hsm : c • w
        = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) • w := rfl
    rw [hsm]
    exact Submodule.smul_mem _ _ ih

/-- **Base change of a chart-ring power span along a pullback square**
(the relative, char-free Route B of `span_pow_p1XSection_scaffold`).  Given
a pullback square

```
  XA --g-→ Xk
  |iY       |iX
  ↓         ↓
  T ---f--→ S
```

with `S`, `T` affine, an affine chart `UX ⊆ Xk` and a coordinate
`x ∈ Γ(Xk, UX)` whose powers span the chart ring over `Γ(S, ⊤)`, the powers
of the pulled-back coordinate `g^♯x` span `Γ(XA, g ⁻¹ᵁ UX)` over
`Γ(T, ⊤)`: the base-changed chart ring is the ring pushout
`Γ(Xk, UX) ⊗_{Γ(S,⊤)} Γ(T, ⊤)` (`isIso_pushoutSection_of_isAffineOpen`),
ring-generated by the two structural images
(`closure_range_union_range_eq_top_of_isPushout`); `Xk`-side generators are
carried into the span by the hypothesis, `T`-side generators are base
scalars. -/
theorem span_pow_section_of_isPullback {XA Xk T S : Scheme.{u}}
    {g : XA ⟶ Xk} {iY : XA ⟶ T} {iX : Xk ⟶ S} {f : T ⟶ S}
    (H : IsPullback g iY iX f)
    (hS : IsAffineOpen (⊤ : S.Opens)) (hT : IsAffineOpen (⊤ : T.Opens))
    {UX : Xk.Opens} (hUX : IsAffineOpen UX) (x : Γ(Xk, UX))
    (hx : letI := ((iX.appLE ⊤ UX (le_top : UX ≤ iX ⁻¹ᵁ ⊤)).hom).toAlgebra
      ⊤ ≤ Submodule.span Γ(S, ⊤) (Set.range fun n : ℕ => x ^ n)) :
    letI := ((iY.appLE ⊤ (g ⁻¹ᵁ UX) (le_top : g ⁻¹ᵁ UX ≤ iY ⁻¹ᵁ ⊤)).hom).toAlgebra
    ⊤ ≤ Submodule.span Γ(T, ⊤)
      (Set.range fun n : ℕ => (g.app UX).hom x ^ n) := by
  letI : Algebra Γ(S, ⊤) Γ(Xk, UX) :=
    ((iX.appLE ⊤ UX (le_top : UX ≤ iX ⁻¹ᵁ ⊤)).hom).toAlgebra
  letI : Algebra Γ(T, ⊤) Γ(XA, g ⁻¹ᵁ UX) :=
    ((iY.appLE ⊤ (g ⁻¹ᵁ UX) (le_top : g ⁻¹ᵁ UX ≤ iY ⁻¹ᵁ ⊤)).hom).toAlgebra
  -- the two structural generator families land in the span
  have hXkSide : ∀ (pf : g ⁻¹ᵁ UX ≤ g ⁻¹ᵁ UX) (s : Γ(Xk, UX)),
      (g.appLE UX (g ⁻¹ᵁ UX) pf).hom s ∈ Submodule.span Γ(T, ⊤)
        (Set.range fun n : ℕ => (g.app UX).hom x ^ n) := by
    intro pf s
    have happ : g.appLE UX (g ⁻¹ᵁ UX) pf = g.app UX := Scheme.Hom.appLE_eq_app g
    rw [happ]
    have hs : s ∈ Submodule.span Γ(S, ⊤) (Set.range fun n : ℕ => x ^ n) :=
      hx trivial
    induction hs using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨n, rfl⟩ := hw
      rw [map_pow]
      exact Submodule.subset_span ⟨n, rfl⟩
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add y z _ _ ihy ihz =>
      rw [map_add]
      exact Submodule.add_mem _ ihy ihz
    | smul c w _ ih =>
      -- `g^♯(c • w) = f^♯c • g^♯w`: base scalars transform along `f`
      have hsc : (g.app UX).hom ((iX.appLE ⊤ UX (le_top : UX ≤ iX ⁻¹ᵁ ⊤)).hom c)
          = (iY.appLE ⊤ (g ⁻¹ᵁ UX)
              (le_top : g ⁻¹ᵁ UX ≤ iY ⁻¹ᵁ ⊤)).hom (f.appTop.hom c) := by
        have e0 : g.app UX = g.appLE UX (g ⁻¹ᵁ UX) le_rfl :=
          (Scheme.Hom.appLE_eq_app g).symm
        have e1 := congrArg (fun φ : Γ(S, ⊤) ⟶ Γ(XA, g ⁻¹ᵁ UX) => φ.hom c)
          (Scheme.Hom.appLE_comp_appLE g iX ⊤ UX (g ⁻¹ᵁ UX)
            (le_top : UX ≤ iX ⁻¹ᵁ ⊤) le_rfl)
        have e2 := congrArg (fun m : XA ⟶ S =>
          (m.appLE ⊤ (g ⁻¹ᵁ UX) (le_top : g ⁻¹ᵁ UX ≤ m ⁻¹ᵁ ⊤)).hom c) H.w
        have e3 := congrArg (fun φ : Γ(S, ⊤) ⟶ Γ(XA, g ⁻¹ᵁ UX) => φ.hom c)
          (Scheme.Hom.appLE_comp_appLE iY f ⊤ ⊤ (g ⁻¹ᵁ UX)
            (le_top : (⊤ : T.Opens) ≤ f ⁻¹ᵁ ⊤)
            (le_top : g ⁻¹ᵁ UX ≤ iY ⁻¹ᵁ ⊤))
        have e4 : f.appLE ⊤ (⊤ : T.Opens) (le_top : (⊤ : T.Opens) ≤ f ⁻¹ᵁ ⊤)
            = f.appTop := Scheme.Hom.appLE_eq_app f
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1 e3
        rw [e4] at e3
        rw [e0]
        exact (e1.trans e2).trans e3.symm
      have hcw1 : c • w
          = (iX.appLE ⊤ UX (le_top : UX ≤ iX ⁻¹ᵁ ⊤)).hom c * w :=
        Algebra.smul_def c w
      have hcw2 : (iY.appLE ⊤ (g ⁻¹ᵁ UX)
            (le_top : g ⁻¹ᵁ UX ≤ iY ⁻¹ᵁ ⊤)).hom (f.appTop.hom c) * (g.app UX).hom w
          = (f.appTop.hom c) • (g.app UX).hom w :=
        (Algebra.smul_def _ _).symm
      rw [hcw1, map_mul, hsc, hcw2]
      exact Submodule.smul_mem _ _ ih
  have hTSide : ∀ (pf : g ⁻¹ᵁ UX ≤ iY ⁻¹ᵁ ⊤) (t : Γ(T, ⊤)),
      (iY.appLE ⊤ (g ⁻¹ᵁ UX) pf).hom t ∈ Submodule.span Γ(T, ⊤)
        (Set.range fun n : ℕ => (g.app UX).hom x ^ n) := by
    intro pf t
    have ht1 : (iY.appLE ⊤ (g ⁻¹ᵁ UX) pf).hom t
        = t • (1 : Γ(XA, g ⁻¹ᵁ UX)) := by
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [ht1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, pow_zero _⟩)
  -- the ring-pushout description of the base-changed chart ring
  have hUST : (⊤ : T.Opens) ≤ f ⁻¹ᵁ ⊤ := le_top
  have hUSX : UX ≤ iX ⁻¹ᵁ ⊤ := le_top
  have hUY : g ⁻¹ᵁ UX = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ ⊤ := by
    rw [Scheme.Hom.preimage_top, inf_top_eq]
  have hIso : IsIso (pushoutSection H hUST hUSX hUY) :=
    isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hS hT hUX
  have hpoCat := (isIso_pushoutSection_iff H hUST hUSX hUY).mp hIso
  have hclos := CommRingCat.closure_range_union_range_eq_top_of_isPushout hpoCat
  intro b hbtop
  clear hbtop
  have hb : b ∈ Subring.closure _ := hclos.ge (Subring.mem_top b)
  induction hb using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨s, rfl⟩ | ⟨t, rfl⟩
    · exact hXkSide _ s
    · exact hTSide _ t
  | zero => exact Submodule.zero_mem _
  | one => exact Submodule.subset_span ⟨0, pow_zero _⟩
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | neg a _ ha => exact Submodule.neg_mem _ ha
  | mul a b _ _ ha hb => exact mul_mem_span_range_pow _ ha hb

/-! ## §4b. The ℙ¹_A relative Laurent chart datum -/

section P1BaseChange

open Scheme

variable {k : Type u} [Field k]
variable (A : Type u) [CommRing A] [Algebra k A]

/-- **The `Γ(Spec A, ⊤)`-span of the base-changed `x`-chart of `ℙ¹_A`**: the
powers of the pulled-back coordinate `pr₁^♯ x` span
`Γ(ℙ¹_A, pr₁ ⁻¹ᵁ V₀) = A[x]` over the base — `span_pow_section_of_isPullback`
on the defining pullback square of `ℙ¹_A`, fed with the `ℙ¹_k` chart span
`Γ(V₀) = k[x]` (`p1LaurentChartData`, bridged from `k` to `Γ(Spec k, ⊤)`). -/
theorem span_pow_p1BaseChangeX :
    letI := (((pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appLE
        ⊤ (pullback.fst (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⁻¹ᵁ
          (p1LaurentChartData k).V₀)
        le_top).hom).toAlgebra
    ⊤ ≤ Submodule.span Γ(Spec (CommRingCat.of A), ⊤)
      (Set.range fun n : ℕ =>
        ((pullback.fst (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).app
            (p1LaurentChartData k).V₀).hom (p1LaurentChartData k).x ^ n) :=
  span_pow_section_of_isPullback
    (IsPullback.of_hasPullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A))))
    (isAffineOpen_top _) (isAffineOpen_top _)
    (p1LaurentChartData k).isAffineOpen_V₀ (p1LaurentChartData k).x
    (span_section_base_of_span_k _ (p1LaurentChartData k).span_pow_x)

/-- The `y`-chart mirror of `span_pow_p1BaseChangeX`. -/
theorem span_pow_p1BaseChangeY :
    letI := (((pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appLE
        ⊤ (pullback.fst (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⁻¹ᵁ
          (p1LaurentChartData k).V₁)
        le_top).hom).toAlgebra
    ⊤ ≤ Submodule.span Γ(Spec (CommRingCat.of A), ⊤)
      (Set.range fun n : ℕ =>
        ((pullback.fst (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).app
            (p1LaurentChartData k).V₁).hom (p1LaurentChartData k).y ^ n) :=
  span_pow_section_of_isPullback
    (IsPullback.of_hasPullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A))))
    (isAffineOpen_top _) (isAffineOpen_top _)
    (p1LaurentChartData k).isAffineOpen_V₁ (p1LaurentChartData k).y
    (span_section_base_of_span_k _ (p1LaurentChartData k).span_pow_y)

set_option maxHeartbeats 800000 in
-- `maxHeartbeats`: the field checks cross the `p1BaseChangeCoverSquare` /
-- `preimage` / `p1LaurentChartData` presentation diamonds (fleet recipe).
/-- **The relative Laurent chart datum of `ℙ¹_A` over `Spec A`** (work item
2, geometric substrate): the standard 2-chart cover `p1BaseChangeCoverSquare`
of `ℙ¹_A` — the *same* cover square consumed by the pinned ℙ¹ engine
statement — carries relative Laurent chart data over `Spec A`: coordinates
are the `pr₁`-pullbacks of the `ℙ¹_k` Laurent coordinates
(`p1LaurentChartData`), overlap/basic-open identities and the unit relation
pull back along `pr₁`, and the chart-ring spans transfer by the ring-pushout
description of the base-changed charts (`span_pow_p1BaseChangeX/Y`). -/
noncomputable def p1BaseChangeRelLaurentChartData :
    RelLaurentChartData
      (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) where
  V := p1BaseChangeCoverSquare A
  x := ((pullback.fst (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).app
        (p1LaurentChartData k).V₀).hom (p1LaurentChartData k).x
  y := ((pullback.fst (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).app
        (p1LaurentChartData k).V₁).hom (p1LaurentChartData k).y
  inf_eq_basicOpen_x := by
    have h1 : (p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂
        = pullback.fst (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⁻¹ᵁ
            ((p1LaurentChartData k).V₀ ⊓ (p1LaurentChartData k).V₁) := rfl
    rw [h1, (p1LaurentChartData k).inf_eq_basicOpen_x, Scheme.preimage_basicOpen]
    rfl
  inf_eq_basicOpen_y := by
    have h1 : (p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂
        = pullback.fst (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⁻¹ᵁ
            ((p1LaurentChartData k).V₀ ⊓ (p1LaurentChartData k).V₁) := rfl
    rw [h1, (p1LaurentChartData k).inf_eq_basicOpen_y, Scheme.preimage_basicOpen]
    rfl
  res_x_mul_res_y := by
    -- naturality: the restricted pullbacks are the overlap pullbacks
    have hnat₀ : ((Limits.pullback (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).presheaf.map
          (homOfLE (inf_le_left : (p1BaseChangeCoverSquare A).U₁ ⊓
            (p1BaseChangeCoverSquare A).U₂ ≤ (p1BaseChangeCoverSquare A).U₁)).op).hom
          (((pullback.fst (p1Over k).hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))).app
              (p1LaurentChartData k).V₀).hom (p1LaurentChartData k).x)
        = ((pullback.fst (p1Over k).hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))).app
              ((p1LaurentChartData k).V₀ ⊓ (p1LaurentChartData k).V₁)).hom
            (((p1Over k).left.presheaf.map
              (homOfLE (inf_le_left : (p1LaurentChartData k).V₀ ⊓
                (p1LaurentChartData k).V₁ ≤ (p1LaurentChartData k).V₀)).op).hom
              (p1LaurentChartData k).x) := by
      have h := congrArg (fun g : Γ((p1Over k).left, (p1LaurentChartData k).V₀) ⟶
          Γ(Limits.pullback (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))),
            (p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂) =>
          g.hom (p1LaurentChartData k).x)
        ((pullback.fst (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).naturality
          (homOfLE (inf_le_left : (p1LaurentChartData k).V₀ ⊓
            (p1LaurentChartData k).V₁ ≤ (p1LaurentChartData k).V₀)).op)
      exact h.symm
    have hnat₁ : ((Limits.pullback (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).presheaf.map
          (homOfLE (inf_le_right : (p1BaseChangeCoverSquare A).U₁ ⊓
            (p1BaseChangeCoverSquare A).U₂ ≤ (p1BaseChangeCoverSquare A).U₂)).op).hom
          (((pullback.fst (p1Over k).hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))).app
              (p1LaurentChartData k).V₁).hom (p1LaurentChartData k).y)
        = ((pullback.fst (p1Over k).hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))).app
              ((p1LaurentChartData k).V₀ ⊓ (p1LaurentChartData k).V₁)).hom
            (((p1Over k).left.presheaf.map
              (homOfLE (inf_le_right : (p1LaurentChartData k).V₀ ⊓
                (p1LaurentChartData k).V₁ ≤ (p1LaurentChartData k).V₁)).op).hom
              (p1LaurentChartData k).y) := by
      have h := congrArg (fun g : Γ((p1Over k).left, (p1LaurentChartData k).V₁) ⟶
          Γ(Limits.pullback (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))),
            (p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂) =>
          g.hom (p1LaurentChartData k).y)
        ((pullback.fst (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).naturality
          (homOfLE (inf_le_right : (p1LaurentChartData k).V₀ ⊓
            (p1LaurentChartData k).V₁ ≤ (p1LaurentChartData k).V₁)).op)
      exact h.symm
    rw [hnat₀, hnat₁]
    exact ((map_mul _ _ _).symm.trans
      (congrArg _ (p1LaurentChartData k).res_x_mul_res_y)).trans (map_one _)
  span_pow_x := span_pow_p1BaseChangeX A
  span_pow_y := span_pow_p1BaseChangeY A

/-- **`H¹`-finiteness of the ℙ¹_A Čech complex** (work item 2, `H¹` half,
concrete form): for a finitely presented module `M` on `ℙ¹_A`, the cokernel
of the base-linear Čech difference map of the standard 2-chart cover
`p1BaseChangeCoverSquare` is a finite `Γ(Spec A, ⊤)`-module — the
`Module.Finite A (M1 ⧸ range d)` input of the two-term finite replacement
`exists_twoTermFiniteReplacement`.  No finiteness of `A` is needed. -/
theorem module_finite_h1_p1BaseChange
    (M : (Limits.pullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    [M.IsFinitePresentation] :
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₁
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₂
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
    Module.Finite Γ(Spec (CommRingCat.of A), ⊤)
      (Γ(M, (p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂) ⧸
        LinearMap.range ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
          (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M)) :=
  (p1BaseChangeRelLaurentChartData A).module_finite_h1 M
    (Scheme.Modules.module_finite_sections_of_isFinitePresentation M
      ⟨(p1BaseChangeCoverSquare A).U₁, (p1BaseChangeCoverSquare A).isAffineOpen_U₁⟩)

end P1BaseChange

/-! ## §5. The endgame skeleton: the two-term finite replacement on the
ℙ¹_A Čech complex

The abstract `TwoTermFiniteFree` machinery applied to the base-linear Čech
complex `d = moduleSectionDiffBase` of `p1BaseChangeCoverSquare`.  All the
module-theoretic hypotheses of the Mumford brick are now discharged for
finitely presented, base-flat `M`:

* flatness of `M⁰ = Γ(M, U₁) × Γ(M, U₂)` and `M¹ = Γ(M, U₁ ⊓ U₂)` — from
  the pinned `CoherentSheafFlat` hypothesis
  (`flat_baseSections_of_coherentSheafFlat` + `TwoTerm.flat_prod`);
* finite generation of `H¹ = coker d` — the A-coefficient Laurent ladder
  (`module_finite_h1_p1BaseChange`);
* noetherianity of the base ring `Γ(Spec A, ⊤) ≅ A` — Hilbert basis.

**Audited remaining leaf (see the module docstring)**: finite generation of
`H⁰ = ker d (= Γ(ℙ¹_A, M))` is Serre-finiteness-grade and is consumed as
the named hypothesis `hH0`; the geometric bridges (fibrewise
`FiberH1Vanishing` at scheme points ⟹ surjectivity of `d ⊗ κ(𝔪)` at maximal
ideals, and `ker d` finite projective ⟹ `p_* M` locally free of rank
`fiberH0`, shaped as `P1RigidPushforwardStatement`) are the remaining B3
sessions' work. -/

section Endgame

variable {k : Type u} [Field k]
variable (A : Type u) [CommRing A] [Algebra k A]

set_option maxHeartbeats 800000 in
-- Heartbeat headroom for the instance-heavy `letI` environment (fleet recipe).
/-- **The B3 ℙ¹-endgame on the Čech complex** (work item 3, algebraic half):
for a finitely presented `M` on `ℙ¹_A` (`A` a finitely generated
`k`-algebra), flat over the base in the pinned `CoherentSheafFlat` sense,
with `H⁰ = ker d` finitely generated (`hH0`, the audited Serre-finiteness
leaf) and `H¹` vanishing on every closed fibre (`hfib`), the Čech difference
map `d` is surjective, `H⁰ = ker d ≅ Γ(ℙ¹_A, M)` is a **finite projective**
(= locally free) `Γ(Spec A, ⊤)`-module, and the formation of `H⁰` commutes
with **arbitrary** base change `Γ(Spec A, ⊤) → B`.

This is `TwoTerm.h0_baseChange_of_fibrewise_h1_vanishing` (Mumford AV II §5
/ Nitsure §5) instantiated on the base-linear Čech complex; combined with
the kernel identification `globalSectionsEquivKerModuleSectionDiffBase` it
computes the pushforward sections `Γ(Spec A, p_* M) = Γ(ℙ¹_A, M) ≅ ker d`. -/
theorem p1Cech_h0_baseChange_of_fibrewise_h1_vanishing
    [Algebra.FiniteType k A]
    (M : (Limits.pullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    [M.IsFinitePresentation]
    (hflat : Scheme.CoherentSheafFlat
      (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M) :
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₁
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₂
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
    ∀ _hH0 : (LinearMap.ker ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
        (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M)).FG,
    ∀ _hfib : (∀ (m : Ideal Γ(Spec (CommRingCat.of A), ⊤)), m.IsMaximal →
      Function.Surjective
        (((p1BaseChangeCoverSquare A).moduleSectionDiffBase
          (pullback.snd (p1Over k).hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M).baseChange
          (Γ(Spec (CommRingCat.of A), ⊤) ⧸ m))),
    Function.Surjective ⇑((p1BaseChangeCoverSquare A).moduleSectionDiffBase
        (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M) ∧
      Module.Finite Γ(Spec (CommRingCat.of A), ⊤)
        (LinearMap.ker ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
          (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M)) ∧
      Module.Projective Γ(Spec (CommRingCat.of A), ⊤)
        (LinearMap.ker ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
          (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M)) ∧
      ∀ (B : Type u) [CommRing B] [Algebra Γ(Spec (CommRingCat.of A), ⊤) B],
        Function.Bijective (AlgebraicJacobian.TwoTerm.kerBaseChange
          ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
            (pullback.snd (p1Over k).hom
              (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M) B) := by
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      (p1BaseChangeCoverSquare A).U₁
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      (p1BaseChangeCoverSquare A).U₂
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
  intro hH0 hfib
  -- noetherianity of the base ring `Γ(Spec A, ⊤) ≅ A` (Hilbert basis)
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : IsNoetherianRing Γ(Spec (CommRingCat.of A), ⊤) :=
    isNoetherianRing_of_ringEquiv A
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm
  -- flatness of the two Čech terms, from the pinned `CoherentSheafFlat`
  haveI hflat₁ : Module.Flat Γ(Spec (CommRingCat.of A), ⊤)
      Γ(M, (p1BaseChangeCoverSquare A).U₁) :=
    Scheme.flat_baseSections_of_coherentSheafFlat _ M hflat
      (p1BaseChangeCoverSquare A).isAffineOpen_U₁
  haveI hflat₂ : Module.Flat Γ(Spec (CommRingCat.of A), ⊤)
      Γ(M, (p1BaseChangeCoverSquare A).U₂) :=
    Scheme.flat_baseSections_of_coherentSheafFlat _ M hflat
      (p1BaseChangeCoverSquare A).isAffineOpen_U₂
  haveI hflat₀ : Module.Flat Γ(Spec (CommRingCat.of A), ⊤)
      (Γ(M, (p1BaseChangeCoverSquare A).U₁) × Γ(M, (p1BaseChangeCoverSquare A).U₂)) :=
    AlgebraicJacobian.TwoTerm.flat_prod
  haveI hflatΓ : Module.Flat Γ(Spec (CommRingCat.of A), ⊤)
      Γ(M, (p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂) :=
    Scheme.flat_baseSections_of_coherentSheafFlat _ M hflat
      (p1BaseChangeCoverSquare A).isAffineOpen_inf
  -- `H¹` finite generation: the A-coefficient Laurent ladder
  haveI hH1 : Module.Finite Γ(Spec (CommRingCat.of A), ⊤)
      (Γ(M, (p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂) ⧸
        LinearMap.range ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
          (pullback.snd (p1Over k).hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M)) :=
    module_finite_h1_p1BaseChange A M
  -- the Mumford endgame brick
  exact AlgebraicJacobian.TwoTerm.h0_baseChange_of_fibrewise_h1_vanishing hH0 hfib

end Endgame

end Adelic

end AlgebraicGeometry
