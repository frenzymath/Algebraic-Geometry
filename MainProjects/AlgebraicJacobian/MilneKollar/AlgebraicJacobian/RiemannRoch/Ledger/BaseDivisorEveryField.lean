/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.ExtensionUniformity
import AlgebraicJacobian.RiemannRoch.Ledger.MapToP1FieldBaseChange

/-!
# The base divisor exists over every field, at every genus — the residue of
extension-uniformity is a degree bound and nothing else

`UniformBaseDivisor C d` (`Ledger/ExtensionUniformity.lean`) is the single remaining input of
extension-uniform `H¹` vanishing
(`Ledger/GenusFieldInvariance.uniformVanishing_of_uniformBaseDivisor`).
It asks for **one** degree bound `d`, chosen before any field, such that over every
extension `κ/k` some divisor of degree `≤ d` already has vanishing `H¹`.

Its two clauses have very different costs, and this file separates them, because the project's
own index for the gap does not.

* **The existence clause is FREE, at every genus.**  `exists_base_subsingleton_baseChangeField`
  below: for **every** field extension `κ/k` there is a divisor `D₀` on `C_κ` with
  `H¹(𝒪(D₀)) = 0`.  Three curve binders, no genus hypothesis, no hypothesis on `κ/k`, one term.
* **The degree clause is the whole residue.**  Nothing here bounds `deg_κ D₀` as `κ` varies, and
  that — not the production of a vanishing divisor — is what `UniformBaseDivisor` still needs.

## Why this is a re-pricing and not a restatement

`Ledger/GenusFieldInvariance.lean:426-430` prices the gap as a missing **production from
geometry**: "For `UniformBaseDivisor` none [no producer] does: it is a `def` with consumers and
no producer anywhere in AJC", concluding "the gap is not a missing consumer or a carrier mismatch
— it is a missing production from geometry, and that is the form the next attempt should take."
That paragraph then records its own partial refutation: `Ledger/VanishingFieldDescent.lean`
produced `UniformBaseDivisor C 0`, but only under `Subsingleton (H¹(𝒪_C))`, which
`subsingleton_hModule_one_iff_genus_eq_zero` shows is exactly `genus C = 0`.  So the standing
picture is that `genus C ≥ 1` still awaits a production from geometry.

That is measured here and it is wrong in a way worth naming: **the production from geometry
already exists, at every genus.**  `Ledger/FiberBound.exists_base_subsingleton_of_isFinite_toP1`
produces a vanishing divisor from a finite dominant `π : Y ⟶ ℙ¹`, and on AJC's curve the `π` and
both cohomology finiteness binders are theorems of the project
(`Ledger/MapToP1.exists_isFinite_isDominant_toP1`, `Ledger/ChiCurve.lean`) — with no genus
hypothesis anywhere in that chain.  Applying it at `Scheme.baseChangeField C κ`, whose three
curve binders are witnessed by `ExtensionUniformity` §1, gives the existence clause over every
`κ` outright.

The genus-0 restriction of `VanishingFieldDescent` is therefore a property of **that route** —
transporting the vanishing of the *unit* sheaf by faithful flatness, which forces the witness to
be the zero divisor and hence `H¹(𝒪_C)` itself to vanish — and not a property of the obligation.
The obligation never needed the unit sheaf.

## What remains open, stated exactly

The quantitative fiber-lattice theorem now proves the explicit vanishing

`H¹(𝒪(genus(C_κ) • F_{πκ})) = 0`.

Thus the stabilization multiplier is no longer open: it is `genus(C_κ) = genus(C)`. The remaining
integer is `deg_κ F_{πκ}`. The current proof constructs a fresh finite dominant map
`πκ : C_κ ⟶ ℙ¹_κ` at every extension, so it gives no uniform bound on this degree.

`Ledger/MapToP1FieldBaseChange.lean` now chooses one finite map over `k` and constructs its finite
surjective base change over every `κ`. The remaining producer must transport the two standard
chart coordinates and prove that the associated source-side fiber divisor has the original
degree. This can be done without identifying the entire pullback target with Ledger's `P1 κ`.
No rational point or other hypothesis on the curve is involved.

## Provenance

The per-field existence layer predates the quantitative result. The new content used here is
`FiberLattice.fiberLattice_stable` and the exact `h¹`-index vanishing theorem in
`Ledger/FiberVanishing.lean`, exposed on curves by
`subsingleton_hModule_divisorSheaf_one_genus_smul_fiber_curve`.

## Contents

* `exists_base_subsingleton_curve` — over `k`, at every genus: a divisor with vanishing `H¹`.
* `exists_base_subsingleton_baseChangeField` — the same over every extension `κ/k`.
* `uniformBaseDivisor_of_exists_deg_le` — the residue isolated: a per-field vanishing divisor of
  *bounded degree* gives `UniformBaseDivisor`.  Recorded so the degree clause is the only thing a
  consumer has to supply, and deliberately **not** advertised as progress: it is the definition
  with the existence clause discharged, which is exactly what the two theorems above buy.
* `finrank_stabilisationAmbient_eq_h1` — the quotient-dimension measurement consumed by the
  quantitative stabilization theorem.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))

section BaseDivisor

variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]

/-- **A divisor with vanishing `H¹` exists on the curve, at every genus** (★★).

Three curve binders and nothing else: no genus hypothesis, no vanishing hypothesis, no finite
map supplied by the caller.  The `π : C ⟶ ℙ¹` and both cohomology finiteness binders that
`Ledger/FiberBound.exists_base_subsingleton_of_isFinite_toP1` asks for are discharged here from
the curve itself (`Ledger/MapToP1.exists_isFinite_isDominant_toP1`,
`Ledger/ChiCurve.moduleFinite_hModule_zero`).

This is the existence clause of `UniformBaseDivisor` over the base field.  It is stated because
the project's index for that gap (`Ledger/GenusFieldInvariance.lean:426-430`) prices it as a
missing production from geometry restricted to `genus C = 0`; the production exists at every
genus, and only the degree bound is missing.  See the module docstring. -/
theorem exists_base_subsingleton_curve :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
    ∃ D₀ : C.left.CurveDivisor,
      Subsingleton (Sheaf.HModule (C.left.divisorSheaf k D₀) 1) := by
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
  refine ⟨genus C • fiberWeilDivisor π, ?_⟩
  exact subsingleton_hModule_divisorSheaf_one_genus_smul_fiber_curve C π hcomp

/-- The finite dominant map to Ledger's `P1 κ` chosen independently on the base-changed curve.
This is deliberately distinguished from `fixedFiniteMapToP1BaseChange`, which is the base change
of one map over `k` but presently lands in the pullback model `(P1 k)_κ`. -/
noncomputable abbrev perFieldFiniteMapToP1 (κ : Type u) [Field κ] [Algebra k κ] :
    (Scheme.baseChangeField C κ).left ⟶ P1 κ :=
  fixedFiniteMapToP1 (Scheme.baseChangeField C κ)

/-- **The per-field vanishing divisor with its multiplier exposed.** Over every extension `κ/k`,
the named fresh map `perFieldFiniteMapToP1 C κ` satisfies

`H¹(𝒪(genus(C_κ) • F_πκ)) = 0`.

The next layer, `GenusFieldInvariance.lean`, rewrites the coefficient to `genus(C)`. -/
theorem subsingleton_baseChangeFieldGenus_smul_fiber_perFieldFiniteMapToP1
    (κ : Type u) [Field κ] [Algebra k κ] :
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    haveI : SmoothOfRelativeDimension 1
        ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
    Subsingleton (Sheaf.HModule ((Scheme.baseChangeField C κ).left.divisorSheaf κ
      (genus (Scheme.baseChangeField C κ) •
        fiberWeilDivisor (perFieldFiniteMapToP1 C κ))) 1) := by
  letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
    .ofHom (Scheme.baseChangeField C κ).hom
  haveI : SmoothOfRelativeDimension 1
      ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
  exact subsingleton_hModule_divisorSheaf_one_genus_smul_fiber_curve
    (Scheme.baseChangeField C κ) (perFieldFiniteMapToP1 C κ)
      (fixedFiniteMapToP1_comp_structureMap (Scheme.baseChangeField C κ))

/-- **The existence clause of `UniformBaseDivisor`, over every field extension** (★★): for every
`κ/k`, finite or infinite, separable or not, there is a divisor on `C_κ` whose `H¹` vanishes.

One term: `exists_base_subsingleton_curve` at `Scheme.baseChangeField C κ`, whose three curve
binders are the instances of `Ledger/ExtensionUniformity.lean` §1.  Per the standing lesson that
class stability under base change witnesses nothing until an **object** carrying the base-changed
instances is exhibited in the spelling the consumer elaborates against (`FiberBound.lean` §
"SUPERSEDED"), this is stated at `C_κ` itself rather than as a stability claim.

What it does **not** give, and the whole of what `UniformBaseDivisor` still needs: any bound on
`CurveDivisor.deg κ D₀` as `κ` varies. The proof now chooses
`D₀ = genus(C_κ) • F_{πκ}`: the multiplier is uniform by genus invariance, but the construction
still chooses a fresh `πκ`, so the degree of `F_{πκ}` remains uncontrolled. -/
theorem exists_base_subsingleton_baseChangeField (κ : Type u) [Field κ] [Algebra k κ] :
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    haveI : SmoothOfRelativeDimension 1
        ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
    ∃ D₀ : (Scheme.baseChangeField C κ).left.CurveDivisor,
      Subsingleton
        (Sheaf.HModule ((Scheme.baseChangeField C κ).left.divisorSheaf κ D₀) 1) := by
  letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
    .ofHom (Scheme.baseChangeField C κ).hom
  haveI : SmoothOfRelativeDimension 1
      ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
  exact ⟨genus (Scheme.baseChangeField C κ) •
      fiberWeilDivisor (perFieldFiniteMapToP1 C κ),
    subsingleton_baseChangeFieldGenus_smul_fiber_perFieldFiniteMapToP1 C κ⟩

omit [IsProper C.hom] in
/-- **The residue isolated**: `UniformBaseDivisor C d` from a *degree-bounded* per-field vanishing
divisor.

**This is the IDENTITY, not even bookkeeping — established by a fresh-context audit,
2026-07-29.**  Its hypothesis is *definitionally* `UniformBaseDivisor C d` (`Iff.rfl` closes the
equivalence) and its body `fun κ _ _ => h κ` is η-expansion.  An earlier version of this docstring
called it "bookkeeping rather than progress", which was still too generous: the two clauses were
already conjuncts at `ExtensionUniformity.lean:356`, so this separates them typographically and in
no other sense.

Kept, rather than deleted, only as a signpost — a reader after the degree clause can see from the
statement that the vanishing half is discharged by `exists_base_subsingleton_baseChangeField` and
that `CurveDivisor.deg κ D₀ ≤ d` is all that remains.  Do not cite it as content. -/
theorem uniformBaseDivisor_of_exists_deg_le {d : ℤ}
    (h : ∀ (κ : Type u) [Field κ] [Algebra k κ],
      -- the per-field vanishing divisor, with its degree bounded — the open clause
      letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
        .ofHom (Scheme.baseChangeField C κ).hom
      haveI : SmoothOfRelativeDimension 1
          ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
        inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
      ∃ D₀ : (Scheme.baseChangeField C κ).left.CurveDivisor,
        Subsingleton
            (Sheaf.HModule ((Scheme.baseChangeField C κ).left.divisorSheaf κ D₀) 1)
          ∧ Scheme.CurveDivisor.deg κ D₀ ≤ d) :
    UniformBaseDivisor C d :=
  fun κ _ _ => h κ

end BaseDivisor

/-! ## The quantitative stabilization measurement -/

section Stabilisation

open Scheme

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  (π : Y ⟶ P1 K) [IsDominant π] [IsAffineHom π]

/-- **The stabilization quotient is exactly twisted `H¹`.** The former open strictness step is
now closed by `fiberLattice_stable` and
`Submodule.eq_top_at_finrank_quotient_of_monotone_of_iSup_eq_top_of_stable`, yielding the theorem
`subsingleton_hModule_divisorSheaf_one_at_h1_of_isDominant_toP1`. This identity remains useful for
reading every quotient dimension as the corresponding `h¹`.

At `D = 0`, the explicit index is `h¹(𝒪) = genus`, uniformly over field extensions. The remaining
uniform-degree issue is therefore not stabilization: it is controlling `deg F_π` while choosing
the maps `π` compatibly across extensions. -/
theorem finrank_stabilisationAmbient_eq_h1 (D : Y.CurveDivisor) (n : ℕ) :
    Module.finrank K
        (divisorSections K D (fiberChart₀ π ⊓ fiberChart₁ π) ⧸ fiberLatticeOverlap π D n)
      = Sheaf.h1 (Y.divisorSheaf K (D + n • fiberWeilDivisor π)) :=
  (LinearEquiv.finrank_eq (fiberLatticeH1Equiv π D n)).symm

end Stabilisation

end AlgebraicGeometry
