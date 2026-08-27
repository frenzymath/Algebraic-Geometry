/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.SectionsFieldBaseChange
import AlgebraicJacobian.RiemannRoch.Ledger.ExtensionUniformity
import AlgebraicJacobian.RiemannRoch.Ledger.BaseDivisorEveryField
import AlgebraicJacobian.RiemannRoch.Adelic.FinitenessP1

/-!
# `Ȟ¹(𝒪)` commutes with field base change, and the genus is base-field invariant

This closes **input (1)** of the extension-uniformity reduction
`Ledger/ExtensionUniformity.uniformVanishing_of_uniform_base_of_genus_invariant`: base-field
invariance of the genus, `genus C_κ = genus C` for **every** field extension `κ/k`.

The engine is stated once and is not semicontinuity, not Mumford II.5, not the Exchange
property, and — worth saying because the cluster has been burned by assuming otherwise —
**not Serre duality** (which this workspace does not have in any form).  It is two facts:

1. the two-term Čech complex of a 2-affine cover base-changes **termwise**
   (`Ledger/SectionsFieldBaseChange.lean` §2–§3: the terms by the qcqs `pushoutSection`
   isomorphism, the maps by restriction-naturality);
2. `Ȟ¹` is the **cokernel** of that complex, and base change commutes with cokernels by
   right-exactness of `κ ⊗[k] −` (`quotRangeBaseChangeField` below).

Composing, `κ ⊗[k] Ȟ¹(S, 𝒪) ≃ₗ[κ] Ȟ¹(S_κ, 𝒪)`, and a `finrank` count gives the scalar.

## What each layer is, and where it is honest about its scope

* `sectionDiffₗ_baseChangeField` — §1: the base-changed difference map **is** the base change
  of the difference map.  This is where the two `κ`-dependencies could have hidden and do not.
* `h1CokₗBaseChangeField` — §2: the `κ`-linear cokernel comparison.
* `h1_unit_baseChangeField_eq_h1_unit` / `genus_baseChangeField` — §3: the scalars.
  `genus C_κ = genus C`
  with no hypothesis on `κ/k` at all.
* `chi_moduleKSheaf_baseChangeField_eq` — §4: the χ-ledger entry, `χ(𝒪_{C_κ}) = χ(𝒪_C) = 1 − g`.
* `uniformVanishing_of_uniformBaseDivisor` — §5: **the reduction with input (1) discharged.**
  Extension-uniform bounded vanishing now follows from the *single* remaining hypothesis
  `UniformBaseDivisor C d`.  That hypothesis is input (2) and **remains open**; see below.

## THE THREE STATEMENTS, STILL KEPT APART

1. **Single-field bounded vanishing** — closed at AJC's curve (`Ledger/FiberBound.lean`).
   Unchanged by this file.
2. **Extension-uniformity** — this file discharges **one of its two inputs**.  After it, the
   open half of extension-uniformity is *exactly* input (2): one degree bound `d` such that over
   every `κ` some divisor of degree `≤ d` already has vanishing `H¹`.  That is **still open**,
   in AJC.  **`UniformVanishing C` is not proved by this file.**

   **Update (`Ledger/VanishingFieldDescent.lean`): input (2) now has a producer, at genus 0
   only.**  The "no producer anywhere in AJC" verdict recorded below at
   `uniformVanishing_of_uniformBaseDivisor_curve` is superseded as a *fact* and stands as a
   *method*: `uniformBaseDivisor_zero_of_subsingleton` produces `UniformBaseDivisor C 0` from
   `Subsingleton (H¹(𝒪_C))`, and `uniformVanishing_of_subsingleton_h1` is the first
   `UniformVanishing` instance in AJC.  For AJC's curve that hypothesis *is* `genus C = 0`, so
   for `genus C ≥ 1` — the case that matters — input (2) is still a missing production from
   geometry and this file's reduction is still the honest statement of what remains.

   **On AJCR: I withdraw the stronger claim I made about it.**  Earlier versions of this and two
   sibling docstrings said AJCR's analogue is "a `Nat.find` per field", making input (2) look
   equally open next door.  A reviewer checked the arity and the constant, and the assertion does
   not survive: `WindowFieldTransport.deg_windowN` gives the degree over `K` as
   `windowM_choice π hπ g * windowδ π`, and **both factors are computed at `k`** —
   `windowM_choice` is a `Nat.find` taken once at `k` (`WindowLedger.lean:186`) and `windowδ` is
   `classDeg` of a `k`-fiber twist, with no `K` in either.  `subsingleton_h1_windowN` then gets
   `H¹` vanishing at `K` from a `k`-side hypothesis.  So the constant demonstrably *does* move;
   what is per-`K` there is the block of instance binders the transport section assumes.

   The honest statement is therefore narrower: input (2) is open **in AJC**, and whether AJCR
   already has it, or has something a `κ`-indexed version could be built from, is **unmeasured
   by me**.  It should not be cited as evidence that the input is hard.
3. **Global generation** — untouched.  Nothing here makes generation uniform over extensions;
   the generation statement of `FiberBound` is over a single field and stays that way.

## Provenance

**Argument adapted from AJCR, statements rederived at AJC's carriers.**  AJCR proves the
analogous `finrank_h1_baseField` / `genus_baseField` in
`AlgebraicJacobian/Cohomology/H1BaseFieldInvariance.lean` (sorry-free), and the shape of the
argument here is deliberately the same as theirs — that file is the reason this one is short,
and the reason its risk was known in advance.  What could not be reused:

* AJCR states its version over `AffineTwoCover` and `baseChangeBundle C K` (built from
  `overSpec`/monoidal `⊗` in `Over (Spec k)`); AJC has **`AffineCoverMVSquare`** and
  `Scheme.baseChangeField`, and `AffineTwoCover` does not occur anywhere in AJC.  Two distinct
  carrier boundaries, one of which (`AffineTwoCover` → `AffineCoverMVSquare`) has no bridge in
  either project.
* `LinearMap.quotRangeBaseChangeEquiv`, AJCR's right-exactness brick, is not in AJC either; it
  is rederived here as `quotRangeBaseChangeField` from mathlib's `lTensor_exact`.

A previous round of this lane recorded that the AJC/AJCR *base-change carriers* agree by `rfl`
at the object.  That remains true and is **not** what makes this file work: the object-level
agreement was never the obstacle, the cover carrier and the missing right-exactness brick were.
Recorded so the earlier measurement is not read as having settled more than it did.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace TensorProduct

namespace AlgebraicGeometry

/-! ## §0. Base change commutes with cokernels

Right-exactness of `κ ⊗[k] −` in the two-term form the Čech complex needs.  Rederived from
mathlib's `lTensor_exact` rather than imported: AJC has no analogue of AJCR's
`LinearMap.quotRangeBaseChangeEquiv`. -/

namespace LinearMap

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (f : M →ₗ[R] N)

private lemma ker_mkQ_baseChangeField :
    LinearMap.ker ((LinearMap.range f).mkQ.baseChange A) =
      LinearMap.range (f.baseChange A) := by
  apply LinearMap.exact_iff.mp
  rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
  exact lTensor_exact A (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _)

private lemma surjective_mkQ_baseChangeField :
    Function.Surjective ((LinearMap.range f).mkQ.baseChange A) := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective A (Submodule.mkQ_surjective _)

/-- **Base change commutes with cokernels**: `A ⊗[R] (N ⧸ range f) ≃ₗ[A] (A ⊗[R] N) ⧸ range (f_A)`.

Right-exactness of `A ⊗[R] −`, in exactly the two-term shape the Čech `Ȟ¹` carrier has.  This is
the AJC-local rederivation of AJCR's `LinearMap.quotRangeBaseChangeEquiv`; the proof is the same
`lTensor_exact` argument. -/
noncomputable def quotRangeBaseChangeField :
    A ⊗[R] (N ⧸ LinearMap.range f) ≃ₗ[A]
      (A ⊗[R] N) ⧸ LinearMap.range (f.baseChange A) :=
  ((Submodule.quotEquivOfEq _ _ (ker_mkQ_baseChangeField A f).symm).trans
    (((LinearMap.range f).mkQ.baseChange A).quotKerEquivOfSurjective
      (surjective_mkQ_baseChangeField A f))).symm

end LinearMap

namespace Scheme

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable (κ : Type u) [Field κ] [Algebra k κ]

/-! ## §1. The base-changed Čech complex is the base change of the Čech complex

The domain comparison is the product of the two chart comparisons (through
`TensorProduct.prodRight`), the codomain comparison is the overlap chart's.  The content is
`sectionDiffₗ_baseChangeField`: the square commutes.  It is checked on pure tensors — the
generators of the base change — and on those it is `sectionsBaseChangeField_res` at each of the
two inclusions `U₁ ⊓ U₂ ≤ U₁` and `U₁ ⊓ U₂ ≤ U₂`, plus additivity of the difference. -/

section Complex

variable (S : C.left.AffineCoverMVSquare)

/-- Shorthand: the unit module (structure sheaf in the `X.Modules` dialect) of `C`. -/
private noncomputable abbrev unitOf (C : Over (Spec (CommRingCat.of k))) :
    C.left.Modules :=
  SheafOfModules.unit C.left.ringCatSheaf

/-- The base change of the degree-zero term of the Čech complex: `κ ⊗[k] (Γ(U₁) × Γ(U₂))`
compared with `Γ(U₁ᵏ) × Γ(U₂ᵏ)`, the product of the two chart comparisons. -/
noncomputable def diffDomBaseChangeField :
    κ ⊗[k] (BaseSections C (unitOf C) S.U₁ × BaseSections C (unitOf C) S.U₂) ≃ₗ[κ]
      BaseSections (baseChangeField C κ) (unitOf (baseChangeField C κ))
          (S.baseChangeField κ).U₁ ×
        BaseSections (baseChangeField C κ) (unitOf (baseChangeField C κ))
          (S.baseChangeField κ).U₂ :=
  (TensorProduct.prodRight k κ κ _ _).trans
    ((sectionsBaseChangeFieldₗ κ S.isAffineOpen_U₁.isCompact
        S.isAffineOpen_U₁.isQuasiSeparated).prodCongr
      (sectionsBaseChangeFieldₗ κ S.isAffineOpen_U₂.isCompact
        S.isAffineOpen_U₂.isQuasiSeparated))

/-- The base change of the degree-one term: the overlap chart's comparison. -/
noncomputable def diffCodBaseChangeField :
    κ ⊗[k] BaseSections C (unitOf C) (S.U₁ ⊓ S.U₂) ≃ₗ[κ]
      BaseSections (baseChangeField C κ) (unitOf (baseChangeField C κ))
        ((S.baseChangeField κ).U₁ ⊓ (S.baseChangeField κ).U₂) :=
  sectionsBaseChangeFieldₗ κ S.isAffineOpen_inf.isCompact
    S.isAffineOpen_inf.isQuasiSeparated

/-- **The Čech difference map base-changes** (★): the difference map of the base-changed cover,
read through the term comparisons, is the base change of the original difference map.

This is the identity that makes `Ȟ¹` comparable rather than merely both-defined.  Checked on
pure tensors `a ⊗ (s₁, s₂)`: the base change of `(s₁, s₂) ↦ s₁|₁₂ − s₂|₁₂` is computed by
`sectionsBaseChangeField_res` at `U₁ ⊓ U₂ ≤ U₁` and at `U₁ ⊓ U₂ ≤ U₂`. -/
theorem sectionDiffₗ_baseChangeField :
    ((S.baseChangeField κ).sectionDiffₗ (baseChangeField C κ)
        (unitOf (baseChangeField C κ))).comp
        (diffDomBaseChangeField κ S).toLinearMap =
      (diffCodBaseChangeField κ S).toLinearMap.comp
        ((S.sectionDiffₗ C (unitOf C)).baseChange κ) := by
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  induction x with
  | zero => simp only [map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  | tmul a p =>
    obtain ⟨s₁, s₂⟩ := p
    rw [LinearMap.baseChange_tmul]
    have hdom : diffDomBaseChangeField κ S (a ⊗ₜ (s₁, s₂)) =
        (sectionsBaseChangeFieldₗ κ S.isAffineOpen_U₁.isCompact
            S.isAffineOpen_U₁.isQuasiSeparated (a ⊗ₜ s₁),
          sectionsBaseChangeFieldₗ κ S.isAffineOpen_U₂.isCompact
            S.isAffineOpen_U₂.isQuasiSeparated (a ⊗ₜ s₂)) := rfl
    -- Both sides, read on RAW sections.  Every step below is `rfl`-transparent at the unit
    -- module: `BaseSections` is a type synonym for `Γ`, its `Sub` is `Γ`'s, and
    -- `BaseSections.restrictₗ` is the ring presheaf's restriction (all three checked).
    have hL : (S.baseChangeField κ).sectionDiffₗ (baseChangeField C κ)
          (unitOf (baseChangeField C κ)) (diffDomBaseChangeField κ S (a ⊗ₜ (s₁, s₂)))
        = ((baseChangeField C κ).left.presheaf.map
              (homOfLE (inf_le_left :
                (S.baseChangeField κ).U₁ ⊓ (S.baseChangeField κ).U₂ ≤
                  (S.baseChangeField κ).U₁)).op).hom
            (sectionsBaseChangeField κ S.isAffineOpen_U₁.isCompact
              S.isAffineOpen_U₁.isQuasiSeparated (s₁ ⊗ₜ a)) -
          ((baseChangeField C κ).left.presheaf.map
              (homOfLE (inf_le_right :
                (S.baseChangeField κ).U₁ ⊓ (S.baseChangeField κ).U₂ ≤
                  (S.baseChangeField κ).U₂)).op).hom
            (sectionsBaseChangeField κ S.isAffineOpen_U₂.isCompact
              S.isAffineOpen_U₂.isQuasiSeparated (s₂ ⊗ₜ a)) := by
      show _ = _
      rfl
    have hR : diffCodBaseChangeField κ S (a ⊗ₜ S.sectionDiffₗ C (unitOf C) (s₁, s₂))
        = sectionsBaseChangeField κ S.isAffineOpen_inf.isCompact
            S.isAffineOpen_inf.isQuasiSeparated
            (((C.left.presheaf.map (homOfLE (inf_le_left : S.U₁ ⊓ S.U₂ ≤ S.U₁)).op).hom s₁ -
              (C.left.presheaf.map
                (homOfLE (inf_le_right : S.U₁ ⊓ S.U₂ ≤ S.U₂)).op).hom s₂) ⊗ₜ a) := by
      show _ = _
      rfl
    rw [hL, hR, sub_tmul, map_sub]
    -- Each summand is `sectionsBaseChangeField_res` at one of the two inclusions.  Combined with
    -- `congrArg₂` rather than `rw`: the `rw` motive is not type-correct at `instances`
    -- transparency through the `Modules`/`BaseSections` layers, which is a rewrite-elaboration
    -- artefact and not a mathematical gap — the two equations below *are* the two halves.
    exact congrArg₂ (· - ·)
      (sectionsBaseChangeField_res κ S.isAffineOpen_U₁.isCompact
        S.isAffineOpen_U₁.isQuasiSeparated S.isAffineOpen_inf.isCompact
        S.isAffineOpen_inf.isQuasiSeparated inf_le_left s₁ a)
      (sectionsBaseChangeField_res κ S.isAffineOpen_U₂.isCompact
        S.isAffineOpen_U₂.isQuasiSeparated S.isAffineOpen_inf.isCompact
        S.isAffineOpen_inf.isQuasiSeparated inf_le_right s₂ a)

/-! ## §2. `Ȟ¹` commutes with the base change

The cokernel of the base-changed complex is the base change of the cokernel.  Two steps:
right-exactness (`quotRangeBaseChangeField`) turns `κ ⊗ (Γ₁₂ ⧸ im d)` into
`(κ ⊗ Γ₁₂) ⧸ im (d_κ)`, and §1 identifies `im (d_κ)` with the image of the base-changed
difference map under the term comparison. -/

/-- The ranges match: the image of the base-changed difference map, pushed through the overlap
comparison, is the image of the difference map of the base-changed cover.

This is §1 read as an equality of submodules — the form the quotient comparison consumes. -/
theorem range_sectionDiffₗ_baseChangeField :
    Submodule.map (diffCodBaseChangeField κ S).toLinearMap
        (LinearMap.range ((S.sectionDiffₗ C (unitOf C)).baseChange κ)) =
      LinearMap.range ((S.baseChangeField κ).sectionDiffₗ (baseChangeField C κ)
        (unitOf (baseChangeField C κ))) := by
  -- Pointwise form of §1, with the `∘ₗ` unwrapped once and for all.
  have key : ∀ z, (S.baseChangeField κ).sectionDiffₗ (baseChangeField C κ)
        (unitOf (baseChangeField C κ)) (diffDomBaseChangeField κ S z) =
      diffCodBaseChangeField κ S (((S.sectionDiffₗ C (unitOf C)).baseChange κ) z) := by
    intro z
    have h := LinearMap.congr_fun (sectionDiffₗ_baseChangeField κ S) z
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using h
  apply le_antisymm
  · rintro y ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨diffDomBaseChangeField κ S z, key z⟩
  · rintro y ⟨p, rfl⟩
    refine ⟨((S.sectionDiffₗ C (unitOf C)).baseChange κ)
      ((diffDomBaseChangeField κ S).symm p), ⟨_, rfl⟩, ?_⟩
    have h := key ((diffDomBaseChangeField κ S).symm p)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

/-- **`Ȟ¹(𝒪)` commutes with field base change** (★): the `κ`-linear comparison
`κ ⊗[k] Ȟ¹(S, 𝒪_C) ≃ₗ[κ] Ȟ¹(S_κ, 𝒪_{C_κ})`, for every field extension `κ/k` and every 2-affine
cover `S` of `C`.

No hypothesis on `κ/k` and none on `C` beyond having the cover: not properness, not smoothness,
not finiteness of the cohomology.  The two ingredients are right-exactness of `κ ⊗[k] −` and §1. -/
noncomputable def h1CokₗBaseChangeField :
    κ ⊗[k] S.H1Cokₗ C (unitOf C) ≃ₗ[κ]
      (S.baseChangeField κ).H1Cokₗ (baseChangeField C κ) (unitOf (baseChangeField C κ)) :=
  (LinearMap.quotRangeBaseChangeField κ (S.sectionDiffₗ C (unitOf C))).trans
    ((Submodule.Quotient.equiv _ _ (diffCodBaseChangeField κ S)
      (range_sectionDiffₗ_baseChangeField κ S)))

end Complex

/-! ## §3. The scalars: `h¹(𝒪)` and the genus are base-field invariant

`Module.finrank_baseChange` on §2 gives the numerical identity, and `CohomologyKit`'s two
readings of `h¹` (`h1_unit_eq_genus` at `C`, `h1_unit_baseChangeField_eq_genus` at `C_κ`) turn it
into the genus statement.  This is where the two sides AJC already owned finally agree. -/

section Scalars

variable (S : C.left.AffineCoverMVSquare)

/-- **`h¹(𝒪_{C_κ}) = h¹(𝒪_C)` on the base-changed cover.**  The dimension form of §2. -/
theorem h1_unit_baseChangeField_eq_h1_unit :
    (S.baseChangeField κ).h1 (baseChangeField C κ) (unitOf (baseChangeField C κ)) =
      S.h1 C (unitOf C) := by
  change Module.finrank κ ((S.baseChangeField κ).H1Cokₗ (baseChangeField C κ)
    (unitOf (baseChangeField C κ))) = Module.finrank k (S.H1Cokₗ C (unitOf C))
  rw [← (h1CokₗBaseChangeField κ S).finrank_eq, Module.finrank_baseChange]

/-- **The genus is invariant under base field extension** (★★): `genus C_κ = genus C`, for a
smooth proper geometrically integral curve `C/k` and **every** field extension `κ/k` — finite or
infinite, separable or not, perfect or not, algebraically closed or not.

This is **input (1)** of the extension-uniformity reduction
(`Ledger/ExtensionUniformity.uniformVanishing_of_uniform_base_of_genus_invariant`), and it is now
a theorem of AJC rather than a hypothesis.

The proof composes three things AJC already had with the one it lacked: `h¹(𝒪_C) = genus C` on
any cover, `h¹(𝒪_{C_κ}) = genus C_κ` on the base-changed cover, and §2's comparison between the
two `h¹`s.  The cover is produced by the curve's own `AffineCoverMVSquare` — there is nothing to
choose, and the statement does not mention one. -/
theorem genus_baseChangeField [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] (S : C.left.AffineCoverMVSquare) :
    genus (baseChangeField C κ) = genus C := by
  have h₁ : (S.baseChangeField κ).h1 (baseChangeField C κ) (unitOf (baseChangeField C κ)) =
      genus (baseChangeField C κ) :=
    AffineCoverMVSquare.h1_unit_baseChangeField_eq_genus C κ S
  have h₂ : S.h1 C (unitOf C) = genus C := S.h1_unit_eq_genus C
  rw [← h₁, ← h₂]
  exact h1_unit_baseChangeField_eq_h1_unit κ S

end Scalars

/-! ## §4. The χ-ledger entry over `κ`

`Ledger/ExtensionUniformity.chi_moduleKSheaf_baseChangeField` already reads
`χ(𝒪_{C_κ}) = 1 − genus C_κ`.  With §3 the right-hand side is `1 − genus C`, so the χ-ledger
value does not move under base field extension either. -/

section Chi

/-- **`χ(𝒪_{C_κ}) = 1 − genus C`** — the `κ`-independent form.  This is the entry the vanishing
threshold `b(κ) = deg_κ D₀(κ) + genus C_κ` reads, with its genus dependence now discharged: the
whole `κ`-dependence of `b(κ)` has been reduced to `deg_κ D₀(κ)`. -/
theorem chi_moduleKSheaf_baseChangeField_eq [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [GeometricallyIrreducible C.hom]
    (S : C.left.AffineCoverMVSquare) :
    letI : (baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (baseChangeField C κ).hom
    Sheaf.chi ((baseChangeField C κ).left.moduleKSheaf κ) = 1 - (genus C : ℤ) := by
  rw [chi_moduleKSheaf_baseChangeField C κ, genus_baseChangeField κ S]

end Chi

end Scheme

/-! ## §5. The reduction with input (1) discharged

`Ledger/ExtensionUniformity.uniformVanishing_of_uniform_base_of_genus_invariant` needed two
antecedents.  §3 supplies one of them unconditionally, so extension-uniform bounded vanishing now
follows from **input (2) alone**.

Read the scope line and then read it again, because this is the exact place where the three
cluster-P statements have been conflated before:

* `UniformVanishing C` is **NOT proved here.**  `uniformVanishing_of_uniformBaseDivisor` is an
  implication whose hypothesis `UniformBaseDivisor C d` is genuinely open.
* What changed is the *size of the residue*, not its status: extension-uniformity was two open
  inputs, and is now exactly one, named, with no genus hypothesis anywhere in the statement.
* Nothing here touches global generation, and nothing here makes generation uniform over
  extensions.  That remains a single-field statement (`FiberBound`, item 3). -/

section Reduction

variable {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))

/-- **Non-vacuity: the cover argument is not a hidden hypothesis.**  `genus_baseChangeField` and
the reduction below take an `AffineCoverMVSquare` on `C.left`, and a statement taking a datum the
project cannot produce would be vacuous progress.  It can: on AJC's curve a 2-affine cover
follows from the three curve binders alone, via `Ledger/MapToP1`'s finite dominant `π : C ⟶ ℙ¹`
pulled back along the standard ℙ¹ charts (`Adelic.P1HasLaurentChartData` is a global instance
over every field, `Adelic.LaurentChartData.pullbackSquare` does the pullback).

Stated as a theorem rather than asserted in a docstring, because "the caller supplies a cover"
and "no caller can" look identical from the statement. -/
theorem nonempty_affineCoverMVSquare_of_curve [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [GeometricallyIntegral C.hom] :
    Nonempty C.left.AffineCoverMVSquare := by
  obtain ⟨S, -⟩ := Adelic.exists_affineCoverMVSquare_module_finite_H1Cok C
  exact ⟨S⟩

/-- **The genus identity with the cover discharged** (★★): `genus C_κ = genus C` for every field
extension, on the three curve binders and **nothing else** — no cover argument.

This is the form a downstream consumer should call.  It is `genus_baseChangeField` composed with
`nonempty_affineCoverMVSquare_of_curve`, and the composition is what makes "for every field
extension" an unqualified claim about AJC's curve rather than one about curves that happen to
come with a cover. -/
theorem genus_baseChangeField_curve [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom] [GeometricallyIntegral C.hom]
    (κ : Type u) [Field κ] [Algebra k κ] :
    genus (Scheme.baseChangeField C κ) = genus C := by
  obtain ⟨S⟩ := nonempty_affineCoverMVSquare_of_curve C
  exact Scheme.genus_baseChangeField κ S

/-- **The per-field fiber vanishing with the base-field genus exposed.** For the named finite
dominant map chosen on `C_κ`, the divisor `genus(C) • F_πκ` has vanishing `H¹`. This combines
the explicit quantitative fiber theorem with genus invariance and leaves only the degree of
`F_πκ` as the uniformity variable. -/
theorem subsingleton_genus_smul_fiber_perFieldFiniteMapToP1_curve
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom]
    (κ : Type u) [Field κ] [Algebra k κ] :
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    haveI : SmoothOfRelativeDimension 1
        ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
    Subsingleton (Sheaf.HModule ((Scheme.baseChangeField C κ).left.divisorSheaf κ
      (genus C • fiberWeilDivisor (perFieldFiniteMapToP1 C κ))) 1) := by
  letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
    .ofHom (Scheme.baseChangeField C κ).hom
  haveI : SmoothOfRelativeDimension 1
      ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
  haveI : GeometricallyIntegral C.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible C.hom
  have h := subsingleton_baseChangeFieldGenus_smul_fiber_perFieldFiniteMapToP1 C κ
  rw [genus_baseChangeField_curve C κ] at h
  exact h

/-- **The reduction with the cover discharged too** (★★): extension-uniform bounded vanishing
follows from `UniformBaseDivisor C d` alone, on the three curve binders.

`UniformBaseDivisor C d` is the **one** remaining open input.  Nothing else is assumed.

**The shape of that gap, measured rather than described.**  Applying the producer/consumer test
of I-0711 (from the AJCR certificate lane, which spent three sessions mis-pricing exactly this):
ask whether a declaration exists whose *conclusion* is the type in question, with primitive
inputs.  For every comparison in this file and its companion, one does — `sectionsBaseChangeField`
from a qcqs open, `h1CokₗBaseChangeField` from a cover, `nonempty_affineCoverMVSquare_of_curve`
from the three curve binders.  For `UniformBaseDivisor` **none does**: it is a `def` with five
consumers and no producer anywhere in AJC.

So the gap is not a missing consumer or a carrier mismatch — it is a missing **production from
geometry**, and that is the form the next attempt should take.

**That measurement has since been acted on, and its "no producer" clause is now false as
stated.**  `Ledger/VanishingFieldDescent.uniformBaseDivisor_zero_of_subsingleton` is a producer:
its conclusion is `UniformBaseDivisor C 0` and its input is a property of `C` alone.  The
prediction the paragraph made was right about the *form* — it came from geometry, via faithfully
flat descent of the `H¹` comparison this file builds — and wrong about the *difficulty*, since it
was one unused step away.  What it did not predict is how narrow the producer would be: its
hypothesis `Subsingleton (H¹(𝒪_C))` is `genus C = 0`.

**CORRECTION (2026-07-29, lane `ajc-p2`): the final clause above — that `genus C ≥ 1` is
untouched and "the gap is a missing production from geometry" still describes it — is WRONG, and
the diagnosis it carries is the load-bearing part.**  The production from geometry exists at
*every* genus: `Ledger/BaseDivisorEveryField.exists_base_subsingleton_baseChangeField` exhibits,
for every field extension `κ/k`, a divisor on `C_κ` with vanishing `H¹`, on the three curve
binders and nothing else (kernel-checked, axiom-clean).  It is one term, from
`Ledger/FiberBound.exists_base_subsingleton_of_isFinite_toP1` at `Scheme.baseChangeField C κ` —
whose inputs (a finite dominant map to `ℙ¹`, and both cohomology finiteness binders) are theorems
of this project on the curve, none of them genus-restricted.

So the genus-0 ceiling belongs to `VanishingFieldDescent`'s *route*, not to the obligation:
transporting the vanishing of the **unit** sheaf by faithful flatness forces the witness to be
the zero divisor, hence forces `H¹(𝒪_C)` itself to vanish.  The obligation never needed the unit
  sheaf. What `UniformBaseDivisor` still lacks is only its **degree clause**. The quantitative
  fiber theorem now makes the named witness
  `D₀(κ) = genus(C) • F_{πκ}` (`subsingleton_genus_smul_fiber_perFieldFiniteMapToP1_curve`), so
  the stabilization index is no longer a variable. The surviving problem is a uniform bound on
  `deg_κ F_{πκ}`. `Ledger/MapToP1FieldBaseChange.lean` constructs one fixed map and its finite
  surjective base change; the remaining bridge is transport of its source-side two-chart
  coordinate data and fiber-degree invariance. -/
theorem uniformVanishing_of_uniformBaseDivisor_curve [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [GeometricallyIntegral C.hom] {d : ℤ} (hbase : UniformBaseDivisor C d) :
    UniformVanishing C :=
  uniformVanishing_of_uniform_base_of_genus_invariant C (g := genus C) hbase
    (fun κ _ _ => genus_baseChangeField_curve C κ)

/-- **Extension-uniform bounded vanishing from the base-divisor bound alone** (★★): with base-field
invariance of the genus now a theorem (§3), the reduction of `Ledger/ExtensionUniformity.lean`
carries only its second antecedent.

`UniformBaseDivisor C d` — one degree bound `d` such that over *every* extension `κ/k` some
divisor of degree `≤ d` already has vanishing `H¹` — is **the single remaining gap** in
extension-uniformity.  Since 2026-07-29 its two clauses are separated: the **existence** of a
vanishing divisor over every `κ` is a theorem at every genus
(`Ledger/BaseDivisorEveryField.exists_base_subsingleton_baseChangeField`), so what is open is the
**degree bound on that divisor** and nothing else.  It is open in AJC **for `genus C ≥ 1`**; at
genus 0 the whole conjunction is discharged by
`Ledger/VanishingFieldDescent.uniformBaseDivisor_zero_of_genus_eq_zero` — and, since
`Ledger/P1Vanishing.lean`, *witnessed* there rather than only implied
(`P1Vanishing.uniformBaseDivisor_p1Over` at `ℙ¹`, where the hypothesis is a theorem).  The
threshold produced here is `d + genus C`, an honest constant of `C` with no `κ` in it.

**Two corrections to what this paragraph used to say**, both found by a fresh-context review of
the round that was itself correcting this file's gap index — which is how a stale claim survives a
correction pass. (i) It said the gap is flatly "open in AJC", with no genus qualifier. (ii) It said
"open in AJC and in AJCR both", which the same round withdrew twelve lines above and in
`Ledger/FiberBound.lean`: AJCR *does* have the content, on a carrier 88–139 files away. Grep the
claim's text, not the file you edited.

The cover argument is supplied by the caller, since `genus_baseChangeField` reads the genus on
one; on the challenge curve `Adelic.LaurentChartData.pullbackSquare` produces it. -/
theorem uniformVanishing_of_uniformBaseDivisor [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [GeometricallyIntegral C.hom] (S : C.left.AffineCoverMVSquare) {d : ℤ}
    (hbase : UniformBaseDivisor C d) :
    UniformVanishing C :=
  uniformVanishing_of_uniform_base_of_genus_invariant C (g := genus C) hbase
    (fun κ _ _ => Scheme.genus_baseChangeField κ S)

end Reduction

end AlgebraicGeometry
