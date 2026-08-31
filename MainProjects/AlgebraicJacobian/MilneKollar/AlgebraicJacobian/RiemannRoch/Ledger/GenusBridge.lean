/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.ChiCurve
import AlgebraicJacobian.Genus
import AlgebraicJacobian.Cohomology.MayerVietorisCore

/-!
# The ported ledger speaks about *this* project's genus

The χ-ledger of `AlgebraicJacobian/RiemannRoch/Ledger/` was ported from the sibling project
`Algebraic-Jacobian-Challenge-Rebuild`, and its Euler characteristics are taken on the
sibling's cohomology carrier: `CategoryTheory.Sheaf.HModule` at `Type u`, over the *small*
Zariski site.  This project's frozen genus (`AlgebraicJacobian/Genus.lean`) is taken on
`AlgebraicGeometry.Scheme.HModule` at `Type (u+1)`, over a general site.  Those are the
`Ext`-modules of two *different* universe annotations, so `ChiCurve.lean` deliberately states
its results about a local `ledgerGenus` rather than silently reusing the name `genus`.

This file closes that gap, and the closure is genuinely cheap:

* `moduleKSheaf_eq_toModuleKSheaf` — the two structure sheaves are **definitionally equal**
  (`rfl`).  So only the universe annotation differs, not the sheaf being resolved.
* `ledgerGenus_eq_genus` — the two genera are **equal as natural numbers**, by
  `Abelian.Ext.chgUnivLinearEquiv` (`Cohomology/MayerVietorisCore.lean`), which is this
  project's `k`-linear refinement of mathlib's bare `Abelian.Ext.chgUniv`.  `finrank` of
  linearly equivalent modules agree.
* `chi_divisorSheaf_genus`, `riemann_inequality_genus` — the ledger's two headline curve
  statements, restated with `genus C`.

## What this does and does not settle

It settles the *numerical* comparison, which is all the ledger needs: the ledger's content is
Euler characteristics and section-space dimensions, and those are `finrank`s.  It does **not**
produce a `LinearEquiv` between `Scheme.HModule` and `Sheaf.HModule` as stated — the carriers
live in different universes, so no such equivalence is even statable — and it does not claim
the two cohomology theories agree in any structured (functorial, long-exact-sequence) sense.
Anything needing naturality across the two carriers still has real work to do.

The predecessor audit (`RiemannRoch/LedgerPortability.lean`, inbox `I-0495`) predicted exactly
this: the universe gap is an *annotation*, because the ledger is a ledger of dimensions.  This
file is that prediction discharged rather than asserted.

## THIS CONE IS NOT ROOTED, so the standing axiom probe does not cover it

`AlgebraicJacobian.lean` — the root roll-up — contains **no** `RiemannRoch.Ledger.*` import, and
nothing outside `Ledger/` imports anything inside it.  Consequently:

* `lake build` on the default target does not elaborate these 40 files, so a green root-build job
  count says nothing about them;
* `scripts/axiom-frontier.lean` imports only `AlgebraicJacobian`, so **none** of the results here
  appears in the workspace's standing axiom probe.

This is the project's own documented trap (5) (`TO_USER.md`): *an unrooted module is not probed at
all, because the root import never reaches it.*  The axiom lines quoted in these files' docstrings
and commit messages were measured directly, by elaborating scratch probes against each module, and
were independently re-measured by a fresh-context review and by `ajc-pic0av` against the full root.
They are real.  But they are **not** covered by the standing check, and a later session should not
assume the frontier script would have caught a regression here.

The cone *is* co-rootable: adding the import is one line, and a probe importing `AlgebraicJacobian`
together with all 40 modules elaborates cleanly (verified after fixing three name collisions, inbox
`I-0576`).  Rooting it was out of this lane's write scope — the roll-up belongs to nobody's
`RiemannRoch/**` — so it is left as the single outstanding integration step.

## Provenance

AJC-native.  Nothing here is ported; it is a comparison between the ported material and this
project's own frozen definition, proved with this project's own `chgUnivLinearEquiv`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **The two projects' structure sheaves are definitionally equal.**  The ledger resolves
cohomology against `Scheme.moduleKSheaf k` (small site, `Type u`) and this project's `genus`
against `Scheme.toModuleKSheaf` (general site, `Type (u+1)`); the *sheaf* is the same object,
and only the `Ext` universe annotation differs. -/
theorem moduleKSheaf_eq_toModuleKSheaf (C : Over (Spec (CommRingCat.of k))) :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    C.left.moduleKSheaf k = Scheme.toModuleKSheaf C := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  rfl

/-- **The ledger's genus is this project's genus** (★): `ledgerGenus C = genus C`.

Both are `Module.finrank k` of an `Abelian.Ext` in degree one, against the same constant sheaf
and the same structure sheaf (`moduleKSheaf_eq_toModuleKSheaf`); they differ only in the
universe at which `Ext` is annotated, and `Abelian.Ext.chgUnivLinearEquiv` is a `k`-linear
equivalence between those two annotations.  `finrank` does not distinguish linearly equivalent
modules, so the two natural numbers coincide.

This is what licenses reading the ported ledger's `1 - ledgerGenus C + deg D` as a statement
about the genus of `C` as this project defines it. -/
theorem ledgerGenus_eq_genus (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    ledgerGenus C = genus C := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  change Module.finrank k (Sheaf.HModule (C.left.moduleKSheaf k) 1)
      = Module.finrank k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1)
  exact (Abelian.Ext.chgUnivLinearEquiv (R := k)).finrank_eq

/-- **Riemann–Roch-lite for the challenge curve, on this project's genus** (★):
`χ(𝒪(D)) = 1 − genus C + deg D`.

This is `chi_divisorSheaf_curve` with `ledgerGenus` replaced by `genus` along
`ledgerGenus_eq_genus`.  The binders are the three curve hypotheses only: the two
`Module.Finite` cohomology binders of the conditional ledger are *synthesised* here
(`moduleFinite_hModule_zero`, `moduleFinite_hModule_one`), not assumed. -/
theorem chi_divisorSheaf_genus (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (D : C.left.CurveDivisor) :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
    Sheaf.chi (C.left.divisorSheaf k D) = 1 - genus C + Scheme.CurveDivisor.deg k D := by
  have h := chi_divisorSheaf_curve C D
  rw [ledgerGenus_eq_genus C] at h
  exact h

/-- **The Riemann inequality on this project's genus**: `deg D + 1 − genus C ≤ h⁰(𝒪(D))`.
Same discharge as `chi_divisorSheaf_genus`. -/
theorem riemann_inequality_genus (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (D : C.left.CurveDivisor) :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
    Scheme.CurveDivisor.deg k D + 1 - genus C
      ≤ (Sheaf.h0 (C.left.divisorSheaf k D) : ℤ) := by
  have h := riemann_inequality_curve C D
  rw [ledgerGenus_eq_genus C] at h
  exact h

/-- **`H¹(C, 𝒪_C)` is finite-dimensional on this project's carrier**, so `genus C` is the
dimension of an honestly finite-dimensional space rather than a `finrank` defaulting to zero.

This is the ledger's `moduleFinite_hModule_one` transported across the universe annotation.
It is worth stating separately: without it, `genus C = 0` would be consistent with every
statement above for the trivial reason that `Module.finrank` of an infinite-dimensional space
is `0`. -/
theorem moduleFinite_genus_carrier (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    Module.Finite k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI hfin : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    moduleFinite_hModule_one C
  -- the source instance must be passed positionally: `Module.Finite.equiv` takes it as an
  -- instance argument on `M`, and unifying `M` from the *target* leaves it unsolved
  exact @Module.Finite.equiv k (Sheaf.HModule (C.left.moduleKSheaf k) 1) _ _ _ _ _ _ hfin
    (Abelian.Ext.chgUnivLinearEquiv (R := k))

end AlgebraicGeometry
