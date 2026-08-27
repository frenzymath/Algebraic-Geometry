/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.FiberVanishing
import AlgebraicJacobian.RiemannRoch.Ledger.DegreeVanishing
import AlgebraicJacobian.RiemannRoch.Ledger.MapToP1
import AlgebraicJacobian.RiemannRoch.Ledger.GenusBridge

/-!
# The conditional layer discharged: bounded vanishing, Riemann–Roch and generation from `π`

`Ledger/DegreeVanishing.lean` proves the cluster-P statements — bounded `H¹` vanishing on a
degree half-space, exact Riemann–Roch above the bound, the exact section drop, and global
generation at every closed point — each **conditional on one base vanishing**
`Subsingleton H¹(𝒪(D₀))` at one divisor `D₀`.  Its own docstring records that AJC witnessed that
antecedent at no proper curve: the only producer of `Subsingleton H¹(𝒪_X)` in the project carries
`[IsAffine X]`, which a proper curve never satisfies.

This file removes that gap. `Ledger/FiberVanishing.lean` supplies a base vanishing on a genuine
curve bundle at the explicit divisor `D₀ = h¹(𝒪_Y) • F`, for the fiber divisor `F` of a finite
dominant `π : Y ⟶ ℙ¹`. Composing the two makes every statement above depend only on `(Y, π)`,
with no vanishing hypothesis at all.

## The composition, and why the bound is uniform in `D`

`subsingleton_hModule_divisorSheaf_one_h1_smul_fiber_of_isFinite_toP1` fixes **one** divisor
`D₀ = h¹(𝒪_Y) • F` depending only on `(Y, π)`. Feeding that `D₀` to
`DegreeVanishing.exists_bound_subsingleton_hModule_one` yields a threshold

`b = deg (h¹(𝒪_Y) • F) + 1 − χ(𝒪_Y)`

past which `H¹(𝒪(D)) = 0` for **every** `D`. The base divisor is fixed before `D` is seen, so `b`
does not depend on `D`. The degree slack is carried by the linear-equivalence translate inside
`DegreeVanishing.exists_le_subsingleton_of_deg_ge`, not by growing the twist.

## WHAT IS STILL OPEN — the three statements, kept apart

1. **Single-field bounded vanishing: CLOSED here**, for a curve bundle admitting a finite
   dominant map to `ℙ¹`, given the two `Module.Finite` binders on `H⁰`/`H¹` of `𝒪_Y`.
2. **Extension-uniformity: OPEN.** The multiplier is now `h¹(𝒪)`, hence `genus` on the challenge
   curve and invariant under field extension. What remains is a uniform bound on the degree of
   the fiber divisor when the finite map to `ℙ¹` is chosen over each extension.

   **Current status elsewhere, since this paragraph has been the project's index for the gap:**
   `Ledger/ExtensionUniformity.lean` split it and `Ledger/GenusFieldInvariance.lean` closed one
   of the two halves — `genus C_κ = genus C` is a theorem for every field extension, sorry-free.
   What remains open is the *base-divisor degree* half only: one degree bound `d` with a vanishing
   divisor of degree `≤ d` over every `κ`.
3. **Global generation: CLOSED here too, but by an independent route.**
   `exists_bound_generated_of_isFinite_toP1` below is not a corollary of (1): it comes from the
   dévissage slice in `DegreeVanishing`, whose evaluation map *is* the quotient map, and the
   vanishing enters only to make that quotient surjective on `H⁰`.  Neither statement implies the
   other without the exactness input.

## Main declarations

* `AlgebraicGeometry.subsingleton_hModule_divisorSheaf_one_h1_smul_fiber_of_isFinite_toP1` —
  explicit base vanishing at `h¹(𝒪_Y) • F`.
* `AlgebraicGeometry.subsingleton_hModule_divisorSheaf_one_genus_smul_fiber_curve` — its
  genus-multiple form on the challenge curve.
* `AlgebraicGeometry.exists_bound_subsingleton_hModule_one_of_isFinite_toP1` — the uniform
  degree threshold, no vanishing hypothesis.
* `AlgebraicGeometry.exists_bound_h0_eq_of_isFinite_toP1` — exact Riemann–Roch
  `h⁰(𝒪(D)) = χ(𝒪_Y) + deg D` above a threshold.
* `AlgebraicGeometry.exists_bound_section_drop_of_isFinite_toP1` — the exact section drop.
* `AlgebraicGeometry.exists_bound_generated_of_isFinite_toP1` — global generation at every
  closed point above a threshold.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open Scheme

section Unconditional

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]

/-- **Explicit base vanishing at `h¹(𝒪_Y) • F`.** The quantitative fiber-lattice theorem at
`D = 0`, with `𝒪(0)` identified with the structure sheaf. Unlike the former existential
stabilization threshold, the multiplier is intrinsic and can be compared across field
extensions. -/
theorem subsingleton_hModule_divisorSheaf_one_h1_smul_fiber_of_isFinite_toP1
    (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K)) :
    Subsingleton (Sheaf.HModule (Y.divisorSheaf K
      (Sheaf.h1 (Y.moduleKSheaf K) • fiberWeilDivisor π)) 1) := by
  have h := subsingleton_hModule_divisorSheaf_one_at_h1_of_isFinite_toP1
    π hπ (0 : Y.CurveDivisor)
  have hindex : Sheaf.h1 (Y.divisorSheaf K (0 : Y.CurveDivisor)) =
      Sheaf.h1 (Y.moduleKSheaf K) :=
    Sheaf.h1_congr (divisorSheafZeroIso K)
  rw [hindex] at h
  simpa only [zero_add] using h

/-- **A base vanishing at a divisor depending only on `(Y, π)`.** The witness is explicitly
`h¹(𝒪_Y) • F`, rather than an opaque Noetherian stabilization threshold. This is the single fact
that discharges the conditional layer of `Ledger/DegreeVanishing.lean`. -/
theorem exists_base_subsingleton_of_isFinite_toP1
    (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K)) :
    ∃ D₀ : Y.CurveDivisor, Subsingleton (Sheaf.HModule (Y.divisorSheaf K D₀) 1) :=
  ⟨Sheaf.h1 (Y.moduleKSheaf K) • fiberWeilDivisor π,
    subsingleton_hModule_divisorSheaf_one_h1_smul_fiber_of_isFinite_toP1 π hπ⟩

/-- **Bounded `H¹` vanishing, no vanishing hypothesis** (cluster-P item 1, unconditional form):
for a curve bundle carrying a finite dominant `π : Y ⟶ ℙ¹`, there is a degree threshold `b`
depending only on `(Y, π)` past which `H¹(𝒪(D))` vanishes for **every** Weil divisor `D`.

Read the module docstring on scope before consuming this: the threshold is over the single field
`K` and says nothing about uniformity across field extensions. -/
theorem exists_bound_subsingleton_hModule_one_of_isFinite_toP1
    (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K)) :
    ∃ b : ℤ, ∀ D : Y.CurveDivisor, b ≤ CurveDivisor.deg K D →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K D) 1) := by
  haveI : Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1) :=
    moduleFinite_hModule_one_of_isFinite_toP1 π hπ
  obtain ⟨D₀, hD₀⟩ := exists_base_subsingleton_of_isFinite_toP1 π hπ
  exact exists_bound_subsingleton_hModule_one K hD₀

/-- **Exact Riemann–Roch above a threshold, no vanishing hypothesis** (cluster-P item 2):
`h⁰(𝒪(D)) = χ(𝒪_Y) + deg D` for every `D` of large enough degree. -/
theorem exists_bound_h0_eq_of_isFinite_toP1
    (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K)) :
    ∃ b : ℤ, ∀ D : Y.CurveDivisor, b ≤ CurveDivisor.deg K D →
      (Sheaf.h0 (Y.divisorSheaf K D) : ℤ) =
        Sheaf.chi (Y.moduleKSheaf K) + CurveDivisor.deg K D := by
  haveI : Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1) :=
    moduleFinite_hModule_one_of_isFinite_toP1 π hπ
  obtain ⟨D₀, hD₀⟩ := exists_base_subsingleton_of_isFinite_toP1 π hπ
  exact exists_bound_h0_eq K hD₀

/-- **The exact section drop above a threshold, no vanishing hypothesis** (cluster-P item 2,
point form): past the threshold every closed point contributes its full residue degree to `h⁰`,
`h⁰(𝒪(D)) = h⁰(𝒪(D − x)) + [κ(x) : K]`.  The hypothesis is on `deg (D − x)`, so the peel applies
at both ends. -/
theorem exists_bound_section_drop_of_isFinite_toP1
    (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K)) :
    ∃ b : ℤ, ∀ {x : Y} (hx : x ≠ genericPoint Y) (D : Y.CurveDivisor),
      b ≤ CurveDivisor.deg K (D - CurveDivisor.single hx 1) →
      (Sheaf.h0 (Y.divisorSheaf K D) : ℤ) =
        Sheaf.h0 (Y.divisorSheaf K (D - CurveDivisor.single hx 1)) + Y.residueDeg K x := by
  haveI : Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1) :=
    moduleFinite_hModule_one_of_isFinite_toP1 π hπ
  obtain ⟨D₀, hD₀⟩ := exists_base_subsingleton_of_isFinite_toP1 π hπ
  refine ⟨CurveDivisor.deg K D₀ + 1 - Sheaf.chi (Y.moduleKSheaf K), fun hx D hD => ?_⟩
  exact h0_eq_h0_sub_point_add_residueDeg_of_deg_ge K hD₀ hx D hD

/-- **Global generation above a threshold, no vanishing hypothesis** (cluster-P item 3): past the
threshold the dévissage evaluation map at every closed point is surjective on `H⁰` — the sections
of `𝒪(D)` fill the fibre at `x`.

Not a corollary of the vanishing statements above: this comes from the dévissage slice, whose
quotient map *is* the evaluation, and the vanishing enters only to make that quotient surjective
on `H⁰` (see `Ledger/DegreeVanishing.lean` item 3, and the scope note in this file's module
docstring). -/
theorem exists_bound_generated_of_isFinite_toP1
    (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K)) :
    ∃ b : ℤ, ∀ {x : Y} (hx : x ≠ genericPoint Y) (D : Y.CurveDivisor),
      b ≤ CurveDivisor.deg K (D - CurveDivisor.single hx 1) →
      Function.Surjective (Sheaf.HModule.map (devissageSES K hx D).g 0) := by
  haveI : Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1) :=
    moduleFinite_hModule_one_of_isFinite_toP1 π hπ
  obtain ⟨D₀, hD₀⟩ := exists_base_subsingleton_of_isFinite_toP1 π hπ
  refine ⟨CurveDivisor.deg K D₀ + 1 - Sheaf.chi (Y.moduleKSheaf K), fun hx D hD => ?_⟩
  exact surjective_eval_of_deg_ge K hD₀ hx D hD

end Unconditional

/-! ## At AJC's own curve: no `π`, no vanishing, no finiteness hypothesis

The section above still asks the caller for a finite dominant `π` and for
`Module.Finite K (H⁰ 𝒪_Y)`.  On the challenge curve both are **theorems of this project**:
`Ledger/MapToP1.exists_isFinite_isDominant_toP1` constructs the `π` by spreading out a
transcendental rational function, and `Ledger/ChiCurve.lean` discharges both cohomology
finiteness binders.  So on `C` the statements below carry the three curve hypotheses and nothing
else — this is where the layer stops being conditional on anything a caller must supply.

The `letI : C.left.Over _ := .ofHom C.hom` in each statement is the standard `ChiCurve` idiom: it
makes the ambient structure morphism `C.left ↘ Spec k` *definitionally* `C.hom`, so the smoothness
and quasi-compactness binders transfer by `inferInstanceAs` rather than being assumed again. -/

section Curve

variable {k : Type u} [Field k]

/-- **Explicit genus-multiple base vanishing on a challenge curve.** For any finite dominant
map `π : C ⟶ ℙ¹`, compatible with the structure maps,
`H¹(𝒪_C(genus(C) • F_π)) = 0`. The multiplier is the base-change-invariant genus; no vanishing,
finiteness, rational-point, or genus hypothesis is added. -/
theorem subsingleton_hModule_divisorSheaf_one_genus_smul_fiber_curve
    (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (π : C.left ⟶ P1 k) [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.hom) :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
    Subsingleton (Sheaf.HModule (C.left.divisorSheaf k
      (genus C • fiberWeilDivisor π)) 1) := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (QuasiCompact C.hom)
  haveI : LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType C.hom)
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    moduleFinite_hModule_zero C
  have h := subsingleton_hModule_divisorSheaf_one_h1_smul_fiber_of_isFinite_toP1 π hπ
  have hgenus : Sheaf.h1 (C.left.moduleKSheaf k) = genus C := by
    change ledgerGenus C = genus C
    exact ledgerGenus_eq_genus C
  rwa [hgenus] at h

/-- **Bounded `H¹` vanishing on the challenge curve** (★): on a smooth proper geometrically
irreducible curve `C/k` there is a degree threshold past which `H¹(𝒪(D)) = 0` for **every** Weil
divisor `D`.  Three curve binders, nothing else: the `π`, the dominance, and both cohomology
finiteness instances are all *synthesised*.

Contrast `Ledger/DegreeVanishing.lean`, whose statements of the same shape carry a base-vanishing
hypothesis that AJC could witness at no proper curve.  This is that gap closed.

Scope unchanged and worth repeating: the threshold is over the single field `k`. See the module
docstring, item 2 — extension-uniformity does not follow. -/
theorem exists_bound_subsingleton_hModule_one_curve (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
    ∃ b : ℤ, ∀ D : C.left.CurveDivisor, b ≤ CurveDivisor.deg k D →
      Subsingleton (Sheaf.HModule (C.left.divisorSheaf k D) 1) := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (QuasiCompact C.hom)
  haveI : LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType C.hom)
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    moduleFinite_hModule_zero C
  obtain ⟨π, hfin, hdom, hcomp⟩ := exists_isFinite_isDominant_toP1 (k := k) (C := C)
  haveI := hfin
  haveI := hdom
  exact exists_bound_subsingleton_hModule_one_of_isFinite_toP1 π hcomp

/-- **Exact Riemann–Roch on the challenge curve** (★★): `h⁰(𝒪(D)) = 1 − genus C + deg D` for
every divisor of large enough degree, on three curve binders.

The equality is the `χ`-ledger's `χ(𝒪(D)) = 1 − genus C + deg D`
(`Ledger/GenusBridge.chi_divisorSheaf_genus`) with `h¹` known to vanish, so `χ = h⁰`. -/
theorem exists_bound_h0_eq_genus_curve (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
    ∃ b : ℤ, ∀ D : C.left.CurveDivisor, b ≤ CurveDivisor.deg k D →
      (Sheaf.h0 (C.left.divisorSheaf k D) : ℤ) = 1 - genus C + CurveDivisor.deg k D := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  obtain ⟨b, hb⟩ := exists_bound_subsingleton_hModule_one_curve C
  refine ⟨b, fun D hD => ?_⟩
  haveI := hb D hD
  have hchi : Sheaf.chi (C.left.divisorSheaf k D) = 1 - genus C + CurveDivisor.deg k D :=
    chi_divisorSheaf_genus C D
  have h1 : Sheaf.h1 (C.left.divisorSheaf k D) = 0 := Sheaf.h1_eq_zero (hb D hD)
  rw [Sheaf.chi, h1] at hchi
  omega

end Curve

/-! ## Extension-uniformity: the remaining degree problem

Object-level per-field vanishing is proved at `Scheme.baseChangeField C κ` in
`Ledger/BaseDivisorEveryField.lean`. The explicit theorem above improves its witness to

`D_κ = genus(C_κ) • F_{πκ}`.

The multiplier is independent of `κ` by `genus_baseChangeField_curve`. The current per-field proof
still chooses a fresh finite map and supplies no uniform bound on `deg_κ F_{πκ}`.
`Ledger/MapToP1FieldBaseChange.lean` now chooses one map over `k` and constructs its finite
surjective base change. What remains is to factor the fiber construction through its source-side
two-chart coordinate data, transport that data, and prove invariance of the resulting divisor
degree; a full comparison with Ledger's separate `P1 κ` model is not required. -/

section ExtensionUniformity

/-- **The curve binders are stable under field base change.**

Kept as a true statement about morphism classes, but **do not read it as the free half of
extension-uniformity** — that is what its previous docstring claimed and it does not follow.
Nothing here mentions the base-changed curve, so nothing here witnesses the vanishing theorem
re-firing anywhere.  For the free half proper, stated at `Scheme.baseChangeField C κ`, use
`Ledger/ExtensionUniformity.vanishing_baseChangeField`. -/
theorem baseChange_binders_stable :
    MorphismProperty.IsStableUnderBaseChange @IsProper ∧
      MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) ∧
        MorphismProperty.IsStableUnderBaseChange @GeometricallyIrreducible :=
  ⟨inferInstance, smoothOfRelativeDimension_isStableUnderBaseChange 1, inferInstance⟩

end ExtensionUniformity

end AlgebraicGeometry
