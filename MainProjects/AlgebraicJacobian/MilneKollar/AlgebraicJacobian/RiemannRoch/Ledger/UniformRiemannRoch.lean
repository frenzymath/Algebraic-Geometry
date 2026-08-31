/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.P1Vanishing

/-!
# The one open input serves all three cluster-P statements, not just vanishing

`Ledger/ExtensionUniformity.lean` and `Ledger/GenusFieldInvariance.lean` reduced
**extension-uniform `H¹` vanishing** to a single named input, `UniformBaseDivisor C d`, and
`Ledger/P1Vanishing.lean` witnessed the whole chain at `ℙ¹`.  Cluster P has **three** statements,
and the other two were left in a weaker place than they had to be:

* the *exact* Riemann–Roch formula over an extension was available only with the genus read at
  `κ` (`ExtensionUniformity.riemannRoch_baseChangeField`, `1 − genus C_κ + deg_κ D`, threshold
  per field);
* **global generation** was described in every file of this cluster as "untouched, single-field
  only", with no extension-uniform statement of any kind.

This file closes that asymmetry.  It shows that the *same* input `UniformBaseDivisor C d`, with
the *same* threshold `d + genus C`, gives extension-uniform forms of all three:

| cluster-P item | uniform statement | from |
|---|---|---|
| 1 vanishing | `UniformVanishing` | `GenusFieldInvariance` (already) |
| 2 Riemann–Roch / section drop | `UniformRiemannRoch`, `UniformSectionDrop` | §3 here |
| 3 global generation | `UniformGeneration` | §3 here |

Nothing here weakens or re-proves item 1, and nothing here closes `UniformBaseDivisor`.  The
residue is **unchanged and is still exactly one input**; what changes is how much it buys.

## Two curve-level statements that were missing over the base field too (§1)

`Ledger/FiberBound.lean` has curve-level forms (three curve binders, no `π` supplied by the
caller) for vanishing and for the `h⁰` formula, but its **section drop** and **generation**
statements are only stated with a finite dominant `π : Y ⟶ ℙ¹` as an argument.  So even over the
base field a consumer of cluster-P item 3 had to produce a `π`.  `exists_bound_section_drop_curve`
and `exists_bound_generated_curve` discharge it the way `FiberBound`'s two curve forms do, from
`Ledger/MapToP1.exists_isFinite_isDominant_toP1`.  These are single-field statements and are
labelled as such.

## THE THREE STATEMENTS, KEPT APART — and this file is where item 3 finally moves

1. **Single-field bounded vanishing** — closed at AJC's curve (`FiberBound`), unchanged here.
2. **Extension-uniformity of vanishing** — one open input, unchanged here.  `UniformVanishing` is
   `ExtensionUniformity`'s; this file neither strengthens nor re-proves it.
3. **Global generation** — was single-field only.  `UniformGeneration` below is its first
   extension-uniform *statement* in AJC, and `uniformGeneration_of_uniformBaseDivisor` reduces it
   to the same one input as item 1.  **This does not make generation unconditional over
   extensions**: the input is open for `genus C ≥ 1` exactly as before.  What is new is that item 3
   is no longer a *separate* gap — it costs nothing beyond item 2's residue.

That last point is the substantive claim of the file and it is worth stating negatively too: it
was *not* obvious, because generation is not a corollary of vanishing.  It comes from the
dévissage slice (`DegreeVanishing.surjective_eval_of_deg_ge`), and what this file checks is that
the slice's own hypothesis is the same base vanishing, evaluated at `C_κ`, that the uniform base
divisor supplies.

## Provenance

**Rederived in AJC's abstractions; nothing ported.**  Measured, not assumed: `UniformVanishing`,
`UniformBaseDivisor`, `UniformGeneration`, `UniformSectionDrop` and `UniformRiemannRoch` occur in
Algebraic-Jacobian-Challenge-Rebuild **zero** times, and AJCR derives no generation statement from
its slice at all (`Ledger/DegreeVanishing.lean` records that measurement: the only
`Function.Surjective (Sheaf.HModule.map …)` in AJCR is the *peel* `map … .f 1`, not the evaluation
`map … .g 0`).  So there is no uniform-generation result next door to port, on any carrier.

The ingredients are all AJC's: `Ledger/DegreeVanishing`'s `h0_eq_of_deg_ge`,
`h0_eq_h0_sub_point_add_residueDeg_of_deg_ge` and `surjective_eval_of_deg_ge` for the three
conclusions at `C_κ`; `GenusFieldInvariance.genus_baseChangeField_curve` for the `κ`-free genus;
`ExtensionUniformity.chi_moduleKSheaf_baseChangeField` for the χ entry; and
`P1Vanishing.uniformBaseDivisor_p1Over` for the witnesses of §4.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open Scheme

/-! ## §1. Two single-field curve forms that were only stated with a `π`

`FiberBound`'s section-drop and generation theorems take the finite dominant `π : Y ⟶ ℙ¹` as an
argument; its vanishing and `h⁰` theorems have curve forms that produce it internally.  These are
the two missing curve forms, discharged the same way.  **Single field `k` throughout** — they say
nothing about extensions; §2–§3 are where uniformity happens. -/

section CurveSingleField

variable {k : Type u} [Field k]

/-- **The exact section drop on the challenge curve** (★): past a threshold depending only on `C`,
every closed point contributes its full residue degree,
`h⁰(𝒪(D)) = h⁰(𝒪(D − x)) + [κ(x) : k]`.

`FiberBound.exists_bound_section_drop_of_isFinite_toP1` with the finite dominant `π` produced
internally by `Ledger/MapToP1.exists_isFinite_isDominant_toP1`, exactly as
`FiberBound.exists_bound_subsingleton_hModule_one_curve` does for the vanishing.  Three curve
binders and nothing else.

Single-field: the threshold is over `k`.  For the uniform form see `UniformSectionDrop` (§2). -/
theorem exists_bound_section_drop_curve (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
    ∃ b : ℤ, ∀ {x : C.left} (hx : x ≠ genericPoint C.left) (D : C.left.CurveDivisor),
      b ≤ CurveDivisor.deg k (D - CurveDivisor.single hx 1) →
      (Sheaf.h0 (C.left.divisorSheaf k D) : ℤ) =
        Sheaf.h0 (C.left.divisorSheaf k (D - CurveDivisor.single hx 1))
          + C.left.residueDeg k x := by
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
  exact exists_bound_section_drop_of_isFinite_toP1 π hcomp

/-- **Global generation on the challenge curve** (★, cluster-P item 3 at the curve): past a
threshold depending only on `C`, the dévissage evaluation map is surjective on `H⁰` at **every**
closed point.

The curve form `FiberBound` states only with a `π` supplied by the caller.  Three curve binders
and nothing else.

Single-field.  `UniformGeneration` (§2) is the extension-uniform statement, and §3 reduces it to
the same input as uniform vanishing. -/
theorem exists_bound_generated_curve (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
    ∃ b : ℤ, ∀ {x : C.left} (hx : x ≠ genericPoint C.left) (D : C.left.CurveDivisor),
      b ≤ CurveDivisor.deg k (D - CurveDivisor.single hx 1) →
      Function.Surjective (Sheaf.HModule.map (devissageSES k hx D).g 0) := by
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
  exact exists_bound_generated_of_isFinite_toP1 π hcomp

end CurveSingleField

/-! ## §2. The three uniform statements

Each is `ExtensionUniformity.UniformVanishing`'s quantifier shape — `∃ b, ∀ κ, ∀ D on C_κ` — with
the conclusion replaced.  Writing them as definitions rather than inlining them in §3 is the
convention of `ExtensionUniformity.lean` and it exists for the same reason: the quantifier order
*is* the content, and a reader must be able to see that `b` is chosen before `κ`.

None of the three is proved in this section.  §3 reduces all three to `UniformBaseDivisor`. -/

section UniformStatements

variable {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]

/-- **Extension-uniform exact Riemann–Roch**: one threshold `b`, chosen before the field, above
which `h⁰(𝒪(D)) = 1 − genus C + deg_κ D` holds on `C_κ` for **every** extension `κ/k`.

The genus on the right is `genus C`, over the **base** field, with no `κ` in the formula at all.
That is the difference from `ExtensionUniformity.riemannRoch_baseChangeField`, which is per-field
and reads `genus C_κ`; the two are reconciled by `GenusFieldInvariance.genus_baseChangeField_curve`,
so this statement is stronger in both the quantifier order *and* the shape of the constant. -/
def UniformRiemannRoch : Prop :=
  ∃ b : ℤ, ∀ (κ : Type u) [Field κ] [Algebra k κ],
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    haveI : SmoothOfRelativeDimension 1
        ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
    ∀ D : (Scheme.baseChangeField C κ).left.CurveDivisor,
      b ≤ CurveDivisor.deg κ D →
      (Sheaf.h0 ((Scheme.baseChangeField C κ).left.divisorSheaf κ D) : ℤ)
        = 1 - (genus C : ℤ) + CurveDivisor.deg κ D

/-- **Extension-uniform exact section drop**: one threshold serving every extension, above which
each closed point of `C_κ` contributes its full residue degree,
`h⁰(𝒪(D)) = h⁰(𝒪(D − x)) + [κ(x) : κ]`.

The hypothesis is on `deg_κ (D − x)`, as in every section-drop statement of this cluster, so the
peel applies at both ends. -/
def UniformSectionDrop : Prop :=
  ∃ b : ℤ, ∀ (κ : Type u) [Field κ] [Algebra k κ],
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    haveI : SmoothOfRelativeDimension 1
        ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
    ∀ {x : (Scheme.baseChangeField C κ).left}
      (hx : x ≠ genericPoint (Scheme.baseChangeField C κ).left)
      (D : (Scheme.baseChangeField C κ).left.CurveDivisor),
      b ≤ CurveDivisor.deg κ (D - CurveDivisor.single hx 1) →
      (Sheaf.h0 ((Scheme.baseChangeField C κ).left.divisorSheaf κ D) : ℤ)
        = Sheaf.h0 ((Scheme.baseChangeField C κ).left.divisorSheaf κ
            (D - CurveDivisor.single hx 1))
          + (Scheme.baseChangeField C κ).left.residueDeg κ x

/-- **Extension-uniform global generation** — cluster-P item 3, uniform: one threshold `b`, chosen
before the field, above which the dévissage evaluation map is surjective on `H⁰` at every closed
point of `C_κ`, for **every** extension `κ/k`.

**This is the first extension-uniform generation statement in AJC** (measured: no
`UniformGeneration` and no uniform generation statement in either project — see the module
docstring's provenance section).  Every other file of this cluster records generation as
"single-field only, and nothing here makes it uniform"; that was accurate and is what this
definition changes — as a *statement*.  It is not proved here; §3 reduces it. -/
def UniformGeneration : Prop :=
  ∃ b : ℤ, ∀ (κ : Type u) [Field κ] [Algebra k κ],
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    haveI : SmoothOfRelativeDimension 1
        ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
    ∀ {x : (Scheme.baseChangeField C κ).left}
      (hx : x ≠ genericPoint (Scheme.baseChangeField C κ).left)
      (D : (Scheme.baseChangeField C κ).left.CurveDivisor),
      b ≤ CurveDivisor.deg κ (D - CurveDivisor.single hx 1) →
      Function.Surjective (Sheaf.HModule.map (devissageSES κ hx D).g 0)

end UniformStatements

/-! ## §3. All three from the SAME one open input

The reductions.  Each takes `UniformBaseDivisor C d` and nothing else — no genus hypothesis (that
is `GenusFieldInvariance.genus_baseChangeField_curve`), no cover argument (that is
`nonempty_affineCoverMVSquare_of_curve`, used inside it), no vanishing supplied by the caller, and
no Serre duality, which this workspace does not have in any form.

The uniform threshold is `d + genus C` in all three cases — the same constant as
`ExtensionUniformity.uniformVanishing_of_uniform_base_of_genus_invariant` produces for item 1.
The shared arithmetic is isolated in `chi_bound_baseChangeField` so that the three reductions
differ only in which `DegreeVanishing` conclusion they invoke. -/

section Reductions

variable {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
variable [GeometricallyIntegral C.hom]

/-- **The χ entry at `C_κ`, with the `κ` eliminated**: `χ(𝒪_{C_κ}) = 1 − genus C`.

`ExtensionUniformity.chi_moduleKSheaf_baseChangeField` composed with
`GenusFieldInvariance.genus_baseChangeField_curve`.  Isolated because it is the *only* place the
genus identity enters §3, and because it is what turns the three `DegreeVanishing` thresholds
(each of the form `deg D₀ + 1 − χ`) into the single `κ`-free constant `d + genus C`. -/
theorem chi_baseChangeField_eq_curve (κ : Type u) [Field κ] [Algebra k κ] :
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    Sheaf.chi ((Scheme.baseChangeField C κ).left.moduleKSheaf κ) = 1 - (genus C : ℤ) := by
  rw [chi_moduleKSheaf_baseChangeField C κ, genus_baseChangeField_curve C κ]

/-- **Extension-uniform Riemann–Roch from the base-divisor bound** (★★): the exact formula
`h⁰(𝒪(D)) = 1 − genus C + deg_κ D`, one threshold `d + genus C` serving every extension.

Stronger than `ExtensionUniformity.riemannRoch_baseChangeField` in two independent ways: the
threshold is chosen before `κ`, and the constant on the right is the **base-field** genus rather
than `genus C_κ`.  Neither is free — the first is the base-divisor input, the second the genus
identity.

`UniformBaseDivisor C d` is the single hypothesis and it is **open for `genus C ≥ 1`**; see
`Ledger/VanishingFieldDescent.lean` §SCOPE.  This theorem does not narrow that gap and does not
claim to. -/
theorem uniformRiemannRoch_of_uniformBaseDivisor {d : ℤ} (hbase : UniformBaseDivisor C d) :
    UniformRiemannRoch C := by
  refine ⟨d + (genus C : ℤ), fun κ _ _ => ?_⟩
  letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
    .ofHom (Scheme.baseChangeField C κ).hom
  haveI : SmoothOfRelativeDimension 1
      ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
  intro D hD
  obtain ⟨D₀, hvan, hdeg⟩ := hbase κ
  have hchi : Sheaf.chi ((Scheme.baseChangeField C κ).left.moduleKSheaf κ)
      = 1 - (genus C : ℤ) := chi_baseChangeField_eq_curve C κ
  have hstep := h0_eq_of_deg_ge κ hvan D (by rw [hchi]; omega)
  rw [hstep, hchi]

/-- **Extension-uniform section drop from the base-divisor bound** (★★): past `d + genus C`, at
every closed point of `C_κ` and for every extension, `h⁰` drops by exactly the residue degree.

Same single hypothesis as the vanishing and the Riemann–Roch forms. -/
theorem uniformSectionDrop_of_uniformBaseDivisor {d : ℤ} (hbase : UniformBaseDivisor C d) :
    UniformSectionDrop C := by
  refine ⟨d + (genus C : ℤ), fun κ _ _ => ?_⟩
  letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
    .ofHom (Scheme.baseChangeField C κ).hom
  haveI : SmoothOfRelativeDimension 1
      ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
  intro x hx D hD
  obtain ⟨D₀, hvan, hdeg⟩ := hbase κ
  have hchi : Sheaf.chi ((Scheme.baseChangeField C κ).left.moduleKSheaf κ)
      = 1 - (genus C : ℤ) := chi_baseChangeField_eq_curve C κ
  exact h0_eq_h0_sub_point_add_residueDeg_of_deg_ge κ hvan hx D
    (by rw [hchi]; omega)

/-- **Extension-uniform global generation from the base-divisor bound** (★★★, cluster-P item 3
made uniform): one threshold `d + genus C`, chosen before the field, above which evaluation is
surjective at every closed point of `C_κ` for every extension `κ/k`.

**What is new here, precisely.**  Item 3 was single-field in every file of this cluster, and the
reason given was correct: generation is *not* a corollary of vanishing — it comes from the
dévissage slice, whose evaluation map is the quotient map
(`Ledger/DegreeVanishing.surjective_eval_of_deg_ge`).  What this theorem checks is that the
slice's hypothesis at `C_κ` is the *same* base vanishing the uniform base divisor already
supplies.  So item 3 costs **nothing beyond item 2's residue** — it is not a second gap.

**What is NOT new: the residue.**  `UniformBaseDivisor C d` is the same open input as before,
false-for-nothing but unproved for `genus C ≥ 1`.  This theorem is an implication.  Uniform
generation is *not* established here for any curve of positive genus, and the three cluster-P
statements stay distinguished: single-field generation is `exists_bound_generated_curve` (§1,
unconditional), uniform generation is this (conditional), and uniform vanishing is
`GenusFieldInvariance.uniformVanishing_of_uniformBaseDivisor_curve` (conditional on the same
input). -/
theorem uniformGeneration_of_uniformBaseDivisor {d : ℤ} (hbase : UniformBaseDivisor C d) :
    UniformGeneration C := by
  refine ⟨d + (genus C : ℤ), fun κ _ _ => ?_⟩
  letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
    .ofHom (Scheme.baseChangeField C κ).hom
  haveI : SmoothOfRelativeDimension 1
      ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
  intro x hx D hD
  obtain ⟨D₀, hvan, hdeg⟩ := hbase κ
  have hchi : Sheaf.chi ((Scheme.baseChangeField C κ).left.moduleKSheaf κ)
      = 1 - (genus C : ℤ) := chi_baseChangeField_eq_curve C κ
  exact surjective_eval_of_deg_ge κ hvan hx D (by rw [hchi]; omega)

end Reductions

/-! ## §4. Witnesses at `ℙ¹`

`Ledger/P1Vanishing.uniformBaseDivisor_p1Over` discharges the input at `ℙ¹_k` for every field, so
all three §3 implications have an exhibited instance rather than only a hypothesis.  This is the
same non-vacuity discipline `Ledger/NonVacuity.lean` and `P1Vanishing.lean` §4 apply, and it is
worth the four lines: this lane has twice shipped implications whose antecedent no object in the
project satisfied.

**Genus 0 is the whole of what is witnessed.**  The threshold is `0` because the curve is rational.
For `genus C ≥ 1` §4 supplies nothing and §3's hypothesis is unproved. -/

section P1Witnesses

variable (k : Type u) [Field k]

/-- **Extension-uniform Riemann–Roch holds at `ℙ¹_k`** (★★): `h⁰(𝒪(D)) = 1 + deg_κ D` above
degree `0`, over every extension `κ/k` simultaneously. -/
theorem uniformRiemannRoch_p1Over : UniformRiemannRoch (Adelic.p1Over k) :=
  uniformRiemannRoch_of_uniformBaseDivisor (Adelic.p1Over k) (Adelic.uniformBaseDivisor_p1Over k)

/-- **Extension-uniform section drop holds at `ℙ¹_k`** (★★). -/
theorem uniformSectionDrop_p1Over : UniformSectionDrop (Adelic.p1Over k) :=
  uniformSectionDrop_of_uniformBaseDivisor (Adelic.p1Over k) (Adelic.uniformBaseDivisor_p1Over k)

/-- **Extension-uniform global generation holds at `ℙ¹_k`** (★★★) — cluster-P item 3, uniform,
with a witness.  The first curve in AJC at which generation is known over every field extension
with a single threshold. -/
theorem uniformGeneration_p1Over : UniformGeneration (Adelic.p1Over k) :=
  uniformGeneration_of_uniformBaseDivisor (Adelic.p1Over k) (Adelic.uniformBaseDivisor_p1Over k)

end P1Witnesses

end AlgebraicGeometry
