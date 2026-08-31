/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.CohomologyKit

/-!
# Termwise base change of chart sections along a field extension

This is the **comparison map** that `Ledger/ExtensionUniformity.lean` names as the actual
deliverable for extension-uniformity input (1) (base-field invariance of the genus).  The
situation it repairs is precise: AJC already owns *both sides* of the genus comparison on
transported covers — `CohomologyKit.h1_unit_baseChangeField_eq_genus` reads `h¹(𝒪_{C_κ})` on
`S.baseChangeField κ` as `genus C_κ`, and `h1_unit_eq_genus` reads `h¹(𝒪_C)` on `S` as
`genus C` — but it owned no map making the two agree.  Both were *defined*; neither was
*compared*.

What is supplied here, for **every** field extension `κ/k` (no finiteness, no separability,
no perfectness, no algebraic closedness) and every qcqs open `V ⊆ C.left`:

`Γ(C.left, V) ⊗[k] κ ≃ₗ[κ] Γ(C_κ, fst ⁻¹ᵁ V)`

(`Scheme.sectionsBaseChangeFieldₗ`), where `C_κ = Scheme.baseChangeField C κ` is AJC's own
named base-changed curve and `fst ⁻¹ᵁ V` is exactly the chart spelling that
`AffineCoverMVSquare.baseChangeField` produces (`baseChangeField_U₁`/`_U₂` are `rfl`).

## Provenance, honestly

**Rederived in the AJC abstractions, not ported.**  The mathematics is the same as AJCR's
`Cohomology/SectionsBaseChange.lean` + `Cohomology/RelativeSectionsLinear.lean` (the engine in
both cases is mathlib's qcqs `pushoutSection` theorem
`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`), but a port was not taken and would
not have applied unchanged:

* AJCR states everything at `relCurve C R := (C ⊗ overSpec k R).left`, the monoidal product in
  `Over (Spec k)`, with charts `(fst C (overSpec k R)).left ⁻¹ᵁ V`.  AJC has **no** `overSpec`,
  no `Over.sectionsAlgebra`, no `Over.isPullback_left`; `C_κ` is the raw
  `Over.mk (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k κ))))`.
* The `k`-algebra structure on sections is a different named definition in each project.  AJC's
  is `toModuleKSheaf.algebraSection`, i.e. `RingHom.toAlgebra (kToSection C U).hom` — and
  `kToSection` is *definitionally* `ΓSpecIso.inv ≫ C.hom.app ⊤ ≫ res`, which is AJCR's
  `Over.sectionsAlgebra` up to `appLE` normal form.  That coincidence is what makes the
  rederivation short; it is checked here (`algebraMap_sections_eq`, `rfl`) rather than assumed.

So the provenance is: **argument adapted, statement rederived at AJC's carriers, and the
carrier agreement measured rather than reported.**  The one substantive difference from AJCR is
that this file and its companion need **no** `backward.isDefEq.respectTransparency` escape at all,
because AJC's `C_κ` is the pullback on the nose rather than a semireducible monoidal product.

That claim is stronger than the one first committed here, which said "no escape on the
*statements* (only inside two proofs)".  A reviewer flagged the two `set_option` lines as possibly
dead; I removed both and rebuilt, and the kernel agrees — 8699 jobs, exit 0, no diagnostics.  So
they were cargo carried over from the AJCR files this argument was adapted from, where the
`relCurve` product genuinely needs them.  Removed rather than left in place: a live `set_option`
tells a reader "there is a defeq wall here", and a dead one sends them looking for a wall that
does not exist.

## What this does and does not close

It closes the **map**.  It does *not* by itself close `genus C_κ = genus C`: that needs the
two-term Čech complex of the base-changed cover to be the base change of the original's, i.e.
this equivalence intertwined with the difference maps, and then right-exactness of `⊗` on the
cokernel.  §3 supplies the restriction-naturality (`sectionsBaseChangeField_res`) that
`Ledger/GenusFieldInvariance.sectionDiffₗ_baseChangeField` turns into the intertwining, and §4 the
termwise dimension consequence; the genus identity itself is
assembled in `Ledger/GenusFieldInvariance.lean`.

Three statements stay apart, as everywhere in this cluster:

1. **single-field bounded vanishing** — closed at AJC's curve (`Ledger/FiberBound.lean`),
   untouched here;
2. **extension-uniformity** — this file advances *one of its two inputs* and nothing else.  It
   says nothing about the base-divisor degree bound (input (2)), which remains open in AJC for
   `genus C ≥ 1`.  **Two clauses of this sentence were stale and are corrected here**: it said
   input (2) is open "in AJC and AJCR both", which was withdrawn elsewhere in the cluster (AJCR
   *has* the content, on a carrier 88–139 files away), and it gave no genus qualifier, though
   genus 0 is discharged by `Ledger/VanishingFieldDescent.lean` (and witnessed at `ℙ¹` by
   `Ledger/P1Vanishing.lean`).  This was the **fifth** surviving
   copy of the withdrawn claim and it was found by grepping the claim's *text* rather than the
   files being edited — the correction pass that withdrew it never opened this file;
3. **global generation** — untouched, and in particular nothing here makes generation uniform
   over extensions.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace TensorProduct

namespace AlgebraicGeometry

namespace Scheme

variable {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
variable (κ : Type u) [Field κ] [Algebra k κ]

/-! ## §1. The base-change morphism and the carrier agreement

`baseChangeFieldMap` names the field extension `Spec κ ⟶ Spec k` once, so that the two
projections out of `C_κ` can be spelled without repeating the `Spec.map (CommRingCat.ofHom …)`
tower.  `algebraMap_sections_eq` records the fact that makes this file short: AJC's
`k`-algebra structure on sections is the `appLE`-normal form of the structure morphism, so it
is the corner map of the mathlib pushout square with no translation. -/

/-- The field extension as a morphism of schemes, `Spec κ ⟶ Spec k`.  This is the morphism
`Scheme.baseChangeField C κ` is the pullback along. -/
noncomputable abbrev baseChangeFieldMap (k : Type u) [Field k] (κ : Type u) [Field κ]
    [Algebra k κ] : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k κ))

/-- The first projection `C_κ ⟶ C`.  Definitionally `pullback.fst`, named so that chart
preimages read the same way as in `AffineCoverMVSquare.baseChangeField`. -/
noncomputable abbrev baseChangeFieldFst {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k))) (κ : Type u) [Field κ] [Algebra k κ] :
    (baseChangeField C κ).left ⟶ C.left :=
  pullback.fst C.hom (baseChangeFieldMap k κ)

/-- **The `k`-algebra structure on sections is the structure morphism in `appLE` form.**

AJC's algebra instance on `Γ(C.left, V)` is `toModuleKSheaf.algebraSection`, whose structure
map is `kToSection C (op V) = ΓSpecIso.inv ≫ C.hom.app ⊤ ≫ res`.  Mathlib's pushout square has
`C.hom.appLE ⊤ V _` in that corner, and the two are equal by unfolding `appLE`.  Proved rather
than assumed: it is the single seam between AJC's section-algebra convention and the mathlib
engine, and the analogous seam in the sibling project needed a threading lemma of its own. -/
lemma algebraMap_sections_eq (V : C.left.Opens) :
    CommRingCat.ofHom (algebraMap k Γ(C.left, V)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        C.hom.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top C.hom).ge) :=
  rfl

/-- The same statement at `C_κ` and base field `κ`: the `κ`-algebra structure on sections of
the base-changed curve is the second projection in `appLE` form.  (Both sides are `rfl`; the
point of stating it is that the *second* projection is the structure morphism of `C_κ`, which
is what makes the pushout square's bottom-right corner the `κ`-algebra corner.) -/
lemma algebraMap_sections_baseChangeField_eq (W : (baseChangeField C κ).left.Opens) :
    CommRingCat.ofHom (algebraMap κ Γ((baseChangeField C κ).left, W)) =
      (Scheme.ΓSpecIso (CommRingCat.of κ)).inv ≫
        (pullback.snd C.hom (baseChangeFieldMap k κ)).appLE ⊤ W
          (le_top.trans (Scheme.Hom.preimage_top _).ge) :=
  rfl

/-! ## §2. The pushout square and the linear equivalence

`isPushout_algebraMap_sections_baseChangeField` is mathlib's qcqs flat-base-change theorem
transported to the `k`/`κ` corners; over a field base the flatness hypothesis is automatic
(`Spec k` is a subsingleton integral scheme, so every morphism into it is flat).

`sectionsBaseChangeFieldₗ` is then the `κ`-linear equivalence.  Note the tensor factor order:
`Γ(C.left, V) ⊗[k] κ`, matching the pushout, with the `κ`-action on the right factor. -/

section Pushout

variable {C}

/-- **The sections pushout square along a field extension.**

```
   k    ⟶ Γ(C.left, V)
   |            |
   ↓            ↓
   κ    ⟶ Γ(C_κ, fst ⁻¹ᵁ V)
```

is a pushout of commutative rings, for every qcqs open `V ⊆ C.left` and every field extension
`κ/k`.  The engine is mathlib's `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`; the
flatness of `Spec κ ⟶ Spec k` is automatic over a field base, and the two affine corners are
`⊤` on `Spec k` and `Spec κ`.

No hypothesis on `κ/k` beyond being a field extension, and no properness on `C`: the qcqs
hypothesis is asked of `V` directly, so this applies to a chart of a cover as well as to `⊤`. -/
theorem isPushout_algebraMap_sections_baseChangeField {V : C.left.Opens}
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left)) :
    IsPushout (CommRingCat.ofHom (algebraMap k Γ(C.left, V)))
      (CommRingCat.ofHom (algebraMap k κ))
      ((baseChangeFieldFst C κ).appLE V (baseChangeFieldFst C κ ⁻¹ᵁ V) le_rfl)
      (CommRingCat.ofHom (algebraMap κ
        Γ((baseChangeField C κ).left, baseChangeFieldFst C κ ⁻¹ᵁ V))) := by
  have hUST : (⊤ : (Spec (CommRingCat.of κ)).Opens) ≤ baseChangeFieldMap k κ ⁻¹ᵁ ⊤ := le_top
  have hUSX : V ≤ C.hom ⁻¹ᵁ ⊤ := le_top
  have hUY : (baseChangeFieldFst C κ ⁻¹ᵁ V) =
      baseChangeFieldFst C κ ⁻¹ᵁ V ⊓ pullback.snd C.hom (baseChangeFieldMap k κ) ⁻¹ᵁ ⊤ := by
    simp
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback C.hom (baseChangeFieldMap k κ))
    hUST hUSX hUY (isAffineOpen_top _) (isAffineOpen_top _) hV hV'
  have hpo := (isIso_pushoutSection_iff
    (IsPullback.of_hasPullback C.hom (baseChangeFieldMap k κ)) hUST hUSX hUY).mp hiso
  refine hpo.of_iso (Scheme.ΓSpecIso (CommRingCat.of k)) (Iso.refl _)
    (Scheme.ΓSpecIso (CommRingCat.of κ)) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    change _ = _ ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ _
    rw [Iso.hom_inv_id_assoc, Scheme.Hom.appLE]
    rfl
  · simp only [Scheme.Hom.appLE, Scheme.Hom.preimage_top, homOfLE_refl, op_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k κ))
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom]
    change _ = _ ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).inv ≫ _
    rw [Iso.hom_inv_id_assoc, Scheme.Hom.appLE]
    rfl

/-- **Base change of chart sections along a field extension, as a ring equivalence**:
`Γ(C.left, V) ⊗[k] κ ≃+* Γ(C_κ, fst ⁻¹ᵁ V)`. -/
noncomputable def sectionsBaseChangeField {V : C.left.Opens}
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left)) :
    Γ(C.left, V) ⊗[k] κ ≃+* Γ((baseChangeField C κ).left, baseChangeFieldFst C κ ⁻¹ᵁ V) :=
  ((CommRingCat.isPushout_tensorProduct k Γ(C.left, V) κ).isoIsPushout _ _
    (isPushout_algebraMap_sections_baseChangeField κ hV hV')).commRingCatIsoToRingEquiv

/-- The base-change equivalence on `s ⊗ 1`: it is the pullback of `s` along the first
projection `C_κ ⟶ C`.  The computation rule that makes §3 possible. -/
theorem sectionsBaseChangeField_tmul_one {V : C.left.Opens}
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
    (s : Γ(C.left, V)) :
    sectionsBaseChangeField κ hV hV' (s ⊗ₜ 1) =
      (baseChangeFieldFst C κ).appLE V (baseChangeFieldFst C κ ⁻¹ᵁ V) le_rfl s :=
  congr($((CommRingCat.isPushout_tensorProduct k Γ(C.left, V) κ).inl_isoIsPushout_hom _ _
    (isPushout_algebraMap_sections_baseChangeField κ hV hV')).hom s)

/-- The base-change equivalence on `1 ⊗ a`: it is the constant `a` of the base-changed curve,
i.e. the `κ`-algebra structure map of its sections. -/
theorem sectionsBaseChangeField_one_tmul {V : C.left.Opens}
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left)) (a : κ) :
    sectionsBaseChangeField κ hV hV' (1 ⊗ₜ a) =
      algebraMap κ Γ((baseChangeField C κ).left, baseChangeFieldFst C κ ⁻¹ᵁ V) a :=
  congr($((CommRingCat.isPushout_tensorProduct k Γ(C.left, V) κ).inr_isoIsPushout_hom _ _
    (isPushout_algebraMap_sections_baseChangeField κ hV hV')).hom a)

/-- The base-change equivalence on a pure tensor `s ⊗ a`: the constant `a` times the pullback
of `s`. -/
theorem sectionsBaseChangeField_tmul {V : C.left.Opens}
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
    (s : Γ(C.left, V)) (a : κ) :
    sectionsBaseChangeField κ hV hV' (s ⊗ₜ a) =
      (baseChangeFieldFst C κ).appLE V (baseChangeFieldFst C κ ⁻¹ᵁ V) le_rfl s *
        algebraMap κ Γ((baseChangeField C κ).left, baseChangeFieldFst C κ ⁻¹ᵁ V) a := by
  have h : (s ⊗ₜ[k] a : Γ(C.left, V) ⊗[k] κ) = (s ⊗ₜ 1) * (1 ⊗ₜ a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, sectionsBaseChangeField_tmul_one, sectionsBaseChangeField_one_tmul]

/-! ### The `κ`-linear form

`BaseSections C 𝒪 V` is *definitionally* `Γ(C.left, V)` (`BaseSections` is a type synonym) and
its `k`-module structure is restriction of scalars along `kToSection`, which is the same as the
`algebraMap` of `toModuleKSheaf.algebraSection` — so the ring equivalence above already carries
the `κ`-linear structure the Čech kit consumes.  `sectionsBaseChangeFieldₗ` records that as a
`≃ₗ[κ]` so consumers do not have to re-derive the scalar compatibility. -/

/-- **Base change of chart sections along a field extension, `κ`-linearly**:
`κ ⊗[k] Γ(C.left, V) ≃ₗ[κ] Γ(C_κ, fst ⁻¹ᵁ V)`.

Tensor order note, and it is not cosmetic: `κ` goes on the **left**.  That is the side mathlib's
`Module κ (κ ⊗[k] M)` instance and `Module.finrank_baseChange` are keyed on, whereas the pushout
of §2 produces the factors the other way round (`Γ ⊗[k] κ`), so the two are bridged by
`TensorProduct.comm`.  Writing the equivalence at `Γ ⊗[k] κ ≃ₗ[κ]` does not typecheck at all —
there is no `Module κ` on that spelling — which is worth recording because it is the kind of
order mismatch that reads like bookkeeping and is actually an instance wall.

On the target the `κ`-action is the structure action of `C_κ`'s own structure morphism, i.e.
exactly the `Scheme.BaseSections` action of `CohomologyKit` at base field `κ`. -/
noncomputable def sectionsBaseChangeFieldₗ {C : Over (Spec (CommRingCat.of k))}
    {V : C.left.Opens} (hV : IsCompact (V : Set C.left))
    (hV' : IsQuasiSeparated (V : Set C.left)) :
    κ ⊗[k] Γ(C.left, V) ≃ₗ[κ]
      Γ((baseChangeField C κ).left, baseChangeFieldFst C κ ⁻¹ᵁ V) where
  toFun x := sectionsBaseChangeField κ hV hV' (TensorProduct.comm k κ Γ(C.left, V) x)
  invFun y := (TensorProduct.comm k κ Γ(C.left, V)).symm
    ((sectionsBaseChangeField κ hV hV').symm y)
  left_inv x := by
    simp only [RingEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  right_inv y := by
    simp only [LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  map_add' x y := by rw [map_add, map_add]
  map_smul' a x := by
    rw [RingHom.id_apply]
    induction x with
    | zero => simp only [smul_zero, map_zero]
    | add u v hu hv => rw [smul_add, map_add, map_add, hu, hv, map_add, map_add, smul_add]
    | tmul b s =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.comm_tmul,
        TensorProduct.comm_tmul, sectionsBaseChangeField_tmul,
        sectionsBaseChangeField_tmul, map_mul, Algebra.smul_def]
      ring

/-- Computation rule for the `κ`-linear form on `1 ⊗ s`: the pullback of `s` along the first
projection. -/
@[simp] lemma sectionsBaseChangeFieldₗ_one_tmul {C : Over (Spec (CommRingCat.of k))}
    {V : C.left.Opens} (hV : IsCompact (V : Set C.left))
    (hV' : IsQuasiSeparated (V : Set C.left)) (s : Γ(C.left, V)) :
    sectionsBaseChangeFieldₗ κ hV hV' (1 ⊗ₜ s) =
      (baseChangeFieldFst C κ).appLE V (baseChangeFieldFst C κ ⁻¹ᵁ V) le_rfl s := by
  change sectionsBaseChangeField κ hV hV' (TensorProduct.comm k κ Γ(C.left, V) (1 ⊗ₜ s)) = _
  rw [TensorProduct.comm_tmul, sectionsBaseChangeField_tmul_one]

end Pushout

/-! ## §3. Compatibility with restriction

The one identity that makes the equivalence a *comparison of complexes* rather than a
coincidence of dimensions: base-changing then restricting is restricting then base-changing.
Both sides are ring maps out of a tensor product, so it suffices to check on pure tensors, and
on those it is the naturality of `appLE` in both projections.

This is what `Ledger/GenusFieldInvariance.lean` needs in order to identify the base-changed
two-term Čech complex of `S.baseChangeField κ` with the base change of the complex of `S`. -/

section Restriction

variable {C}

/-- **Restriction-naturality of the field base change of sections.**  For qcqs opens `W ≤ V` of
`C.left`, restricting a base-changed section from `fst ⁻¹ᵁ V` to `fst ⁻¹ᵁ W` is the base change
of the restricted section.

Stated on the tensor side as a composite with `Algebra.TensorProduct.map (res) (id κ)`, so it
can be used to rewrite either way. -/
theorem sectionsBaseChangeField_res {V W : C.left.Opens}
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
    (hW : IsCompact (W : Set C.left)) (hW' : IsQuasiSeparated (W : Set C.left))
    (hWV : W ≤ V) (s : Γ(C.left, V)) (a : κ) :
    ((baseChangeField C κ).left.presheaf.map
        (homOfLE (show baseChangeFieldFst C κ ⁻¹ᵁ W ≤ baseChangeFieldFst C κ ⁻¹ᵁ V by
          gcongr)).op).hom
      (sectionsBaseChangeField κ hV hV' (s ⊗ₜ a)) =
      sectionsBaseChangeField κ hW hW'
        ((C.left.presheaf.map (homOfLE hWV).op).hom s ⊗ₜ a) := by
  rw [sectionsBaseChangeField_tmul, sectionsBaseChangeField_tmul, map_mul]
  congr 1
  · -- the first-projection pullback is natural in the open: postcomposing the pullback with the
    -- downstairs restriction (`appLE_map`) is precomposing with the upstairs one (`map_appLE`)
    have h₁ := Scheme.Hom.appLE_map (baseChangeFieldFst C κ)
      (le_rfl : baseChangeFieldFst C κ ⁻¹ᵁ V ≤ baseChangeFieldFst C κ ⁻¹ᵁ V)
      (homOfLE (show baseChangeFieldFst C κ ⁻¹ᵁ W ≤ baseChangeFieldFst C κ ⁻¹ᵁ V by gcongr)).op
    have h₂ := Scheme.Hom.map_appLE (baseChangeFieldFst C κ)
      (show baseChangeFieldFst C κ ⁻¹ᵁ W ≤ baseChangeFieldFst C κ ⁻¹ᵁ W from le_rfl)
      (homOfLE hWV).op
    exact congr($(h₁.trans h₂.symm).hom s)
  · -- the constant `a` is unchanged by restriction (`algebraMap` naturality)
    exact toModuleKSheaf.algebraMap_naturality (C := baseChangeField C κ) _ a

end Restriction

/-! ## §4. The dimension consequence, and precisely what it is not

`finrank_sections_baseChangeField` is the numerical payoff available *from §2 alone*: the
`κ`-dimension of the base-changed chart sections equals the `k`-dimension of the original's,
whenever the latter is free (automatic over a field).  This is `Module.finrank_baseChange`
composed with the equivalence — no geometry beyond §2.

**Read the scope note.**  This is a statement about **chart sections**, i.e. about the terms of
the Čech complex.  It is *not* `h¹` invariance and it is *not* the genus identity: those need
§3 to identify the *maps*, and then right-exactness of `⊗` to pass to the cokernel.  Publishing
the termwise identity as if it were the cohomological one is exactly the conflation this
cluster's task exists to prevent, so it is named termwise and its limits are stated here. -/

section Dimension

variable {C}

/-- **The `κ`-dimension of base-changed chart sections is the `k`-dimension of the original's.**

Termwise only: `V` is one open, and this says nothing about `H¹`, whose comparison additionally
needs §3 and right-exactness.  Free-ness of `Γ(C.left, V)` over `k` is automatic (`k` is a
field), which is why there is no hypothesis for it. -/
theorem finrank_sections_baseChangeField {V : C.left.Opens}
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left)) :
    Module.finrank κ Γ((baseChangeField C κ).left, baseChangeFieldFst C κ ⁻¹ᵁ V) =
      Module.finrank k Γ(C.left, V) := by
  rw [← (sectionsBaseChangeFieldₗ κ hV hV').finrank_eq, Module.finrank_baseChange]

/-- Non-vacuity of §4 in the shape a consumer meets it: on a chart of a 2-affine cover the qcqs
hypotheses are discharged by affineness, so the dimension identity fires with no side condition.

Stated at `U₁`; `U₂` and `U₁ ⊓ U₂` are identical, and the overlap is the case the Čech `H¹`
carrier is built from — `(S.baseChangeField κ).U₁ ⊓ (S.baseChangeField κ).U₂` is `rfl`-equal to
`fst ⁻¹ᵁ (S.U₁ ⊓ S.U₂)`, so this covers every term of the base-changed complex. -/
theorem finrank_sections_baseChangeField_chart (S : C.left.AffineCoverMVSquare) :
    Module.finrank κ Γ((baseChangeField C κ).left, (S.baseChangeField κ).U₁) =
      Module.finrank k Γ(C.left, S.U₁) :=
  finrank_sections_baseChangeField κ S.isAffineOpen_U₁.isCompact
    S.isAffineOpen_U₁.isQuasiSeparated

/-- The same at the overlap `U₁ ⊓ U₂` — the term whose quotient *is* the Čech `Ȟ¹` carrier.
Recorded separately because it is the one §5 of a genus-invariance file would consume, and
because it makes explicit that the overlap chart of the base-changed cover is the preimage of
the overlap (`rfl`, by `AffineCoverMVSquare.preimage`). -/
theorem finrank_sections_baseChangeField_overlap (S : C.left.AffineCoverMVSquare) :
    Module.finrank κ
        Γ((baseChangeField C κ).left,
          (S.baseChangeField κ).U₁ ⊓ (S.baseChangeField κ).U₂) =
      Module.finrank k Γ(C.left, S.U₁ ⊓ S.U₂) :=
  finrank_sections_baseChangeField κ S.isAffineOpen_inf.isCompact
    S.isAffineOpen_inf.isQuasiSeparated

end Dimension

end Scheme

end AlgebraicGeometry
