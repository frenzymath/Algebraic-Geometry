/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.ChiLedger
import AlgebraicJacobian.RiemannRoch.Ledger.Finiteness
import AlgebraicJacobian.RiemannRoch.Ledger.Sections
import AlgebraicJacobian.RiemannRoch.Ledger.Basic
import AlgebraicJacobian.Curve.GeometricallyReduced
-- AJC has no `Challenge.lean`; `genus` is replaced by the ledger-local
-- `ledgerGenus` below and reconciled with `AlgebraicGeometry.genus` in `GenusBridge.lean`.

/-!
# The χ-ledger on the challenge curve: `χ(𝒪(D)) = 1 − g + deg D`

This file instantiates the conditional χ-ledger of `ChiLedger` on the bundled challenge
curve `C : Over (Spec k)` (smooth of relative dimension one, proper, geometrically
irreducible over the field `k`), connecting it to the frozen `AlgebraicGeometry.genus`:

* `AlgebraicGeometry.Scheme.overAlgebraMapTopLinear` / `overAlgebraMapTopEquiv`: the
  structure map `k → Γ(X, ⊤)` as a `k`-linear map, upgraded to a `k`-linear equivalence
  when the structure morphism is bijective on global sections — the seam between the
  ring-level `Γ(C, 𝒪) ≅ k` of `Curve/Sections` and the `Scheme.overModule` structure.
* `AlgebraicGeometry.moduleFinite_hModule_zero` (instance): `H⁰(C, 𝒪_C)` is a finite
  `k`-module — keyed on the same `letI : C.left.Over (Spec (.of k)) := .ofHom C.hom`
  spelling as `genus` and `moduleFinite_hModule_one`.
* `AlgebraicGeometry.h0_moduleKSheaf`: `h⁰(𝒪_C) = 1`.
* `AlgebraicGeometry.chi_moduleKSheaf`: `χ(𝒪_C) = 1 − ledgerGenus C`.
* `AlgebraicGeometry.chi_divisorSheaf_curve` (★, Riemann–Roch-lite):
  `χ(𝒪(D)) = 1 − ledgerGenus C + deg D`.
* `AlgebraicGeometry.riemann_inequality_curve`: `deg D + 1 − ledgerGenus C ≤ h⁰(𝒪(D))`.
* `AlgebraicGeometry.h0_nsmul_point_unbounded_curve`: `h⁰(𝒪(n·x))` is unbounded in `n`.

The two `Module.Finite` instances discharge the standing hypotheses of the conditional
ledger, so the curve statements carry no finiteness side conditions.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

attribute [local instance] AlgebraicGeometry.Scheme.overModule

namespace AlgebraicGeometry

open Scheme

/-! ## The `k`-linear `Γ(X, ⊤) ≅ k` seam -/

section GlobalSections

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]

/-- The structure map `k →+* Γ(X, ⊤)` as a `k`-linear map, for the `Scheme.overModule`
structure on the target (restriction of scalars along the very same map). -/
noncomputable def Scheme.overAlgebraMapTopLinear : k →ₗ[k] Γ(X, ⊤) where
  toFun := X.overAlgebraMap k ⊤
  map_add' := map_add _
  map_smul' r s := by
    simp only [RingHom.id_apply, smul_eq_mul, map_mul, Scheme.overModule_smul_def]

/-- If the structure morphism is bijective on global sections, so is the structure map
`k → Γ(X, ⊤)` (the two differ by the isomorphism `Γ(Spec k, ⊤) ≅ k` and an identity
restriction). -/
theorem Scheme.bijective_overAlgebraMap_top
    (hbij : Function.Bijective ((X ↘ Spec (CommRingCat.of k)).appTop)) :
    Function.Bijective (X.overAlgebraMap k ⊤) := by
  have hid : X.presheaf.map (homOfLE (le_top (a := (⊤ : X.Opens)))).op = 𝟙 _ :=
    X.presheaf.map_id (op (⊤ : X.Opens))
  have h3 : Function.Bijective (X.presheaf.map (homOfLE (le_top (a := (⊤ : X.Opens)))).op) := by
    rw [hid]
    exact Function.bijective_id
  have h1 : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hcomp : ⇑(X.overAlgebraMap k ⊤) =
      ⇑(X.presheaf.map (homOfLE (le_top (a := (⊤ : X.Opens)))).op) ∘
        ⇑((X ↘ Spec (CommRingCat.of k)).appTop) ∘
          ⇑((Scheme.ΓSpecIso (CommRingCat.of k)).inv) := rfl
  rw [show ⇑(X.overAlgebraMap k ⊤) = _ from hcomp]
  exact h3.comp (hbij.comp h1)

/-- **The `k`-linear `Γ(X, ⊤) ≅ k`**: for a scheme over `k` whose structure morphism is
bijective on global sections (e.g. proper and geometrically integral), the structure map
is a `k`-linear equivalence `k ≃ₗ[k] Γ(X, ⊤)`. -/
noncomputable def Scheme.overAlgebraMapTopEquiv
    (hbij : Function.Bijective ((X ↘ Spec (CommRingCat.of k)).appTop)) :
    k ≃ₗ[k] Γ(X, ⊤) :=
  LinearEquiv.ofBijective (Scheme.overAlgebraMapTopLinear k X)
    (Scheme.bijective_overAlgebraMap_top k X hbij)

/-- `h⁰(𝒪_X) = 1` for a scheme over `k` whose structure morphism is bijective on global
sections: `H⁰` is `Γ(X, ⊤)` (`moduleKSheafHZero`), which is `k` by the seam equivalence. -/
theorem Scheme.h0_moduleKSheaf_of_bijective
    (hbij : Function.Bijective ((X ↘ Spec (CommRingCat.of k)).appTop)) :
    Sheaf.h0 (X.moduleKSheaf k) = 1 := by
  have e : Sheaf.HModule (X.moduleKSheaf k) 0 ≃ₗ[k] k :=
    (X.moduleKSheafHZero k).trans (Scheme.overAlgebraMapTopEquiv k X hbij).symm
  rw [Sheaf.h0, e.finrank_eq, Module.finrank_self]

/-- `H⁰(𝒪_X)` is a finite `k`-module when the structure morphism is bijective on global
sections (it is one-dimensional). -/
theorem moduleFinite_hModule_zero_of_bijective
    (hbij : Function.Bijective ((X ↘ Spec (CommRingCat.of k)).appTop)) :
    Module.Finite k (Sheaf.HModule (X.moduleKSheaf k) 0) :=
  Module.Finite.equiv
    ((X.moduleKSheafHZero k).trans (Scheme.overAlgebraMapTopEquiv k X hbij).symm).symm

end GlobalSections

/-! ## The bundled challenge curve -/

section Curve

variable {k : Type u} [Field k]

/-- **The genus, on the ledger's own cohomology carrier**: `h¹` of the structure sheaf
computed as a `Sheaf.HModule` on the *small* Zariski site, at `Type u`.

This is the sibling project's `AlgebraicGeometry.genus` verbatim; it is spelled here
under a distinct name because Algebraic-Jacobian-Challenge already owns a `genus`
(`AlgebraicJacobian/Genus.lean`) taken on its own `Scheme.HModule` carrier at
`Type (u+1)`, over the general site.  The two are the `finrank` of two different
`Ext`-modules and are *not* definitionally equal, so silently reusing the name would
assert an identification that this file does not prove.  See
`AlgebraicJacobian/RiemannRoch/Ledger/GenusBridge.lean` for what the comparison needs
and what is proved of it. -/
noncomputable def ledgerGenus (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] : ℕ :=
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  Module.finrank k (Sheaf.HModule (C.left.moduleKSheaf k) 1)

/-- **Finiteness of `H⁰(C, 𝒪_C)` for the challenge curve** — indeed `H⁰ ≅ k` is
one-dimensional. Keyed on the same `letI : C.left.Over (Spec (.of k)) := .ofHom C.hom`
spelling as `genus` and `moduleFinite_hModule_one`, so instance resolution fires for
statements about the genus. -/
instance moduleFinite_hModule_zero (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI : GeometricallyIntegral C.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible C.hom
  have hbij : Function.Bijective ((C.left ↘ Spec (CommRingCat.of k)).appTop) :=
    bijective_appTop_of_isProper_of_geometricallyIntegral C.hom
  exact moduleFinite_hModule_zero_of_bijective k C.left hbij

/-- **`h⁰(C, 𝒪_C) = 1`** for the challenge curve: global sections of the structure sheaf
are the constants `k`. -/
theorem h0_moduleKSheaf (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    Sheaf.h0 (C.left.moduleKSheaf k) = 1 := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI : GeometricallyIntegral C.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible C.hom
  have hbij : Function.Bijective ((C.left ↘ Spec (CommRingCat.of k)).appTop) :=
    bijective_appTop_of_isProper_of_geometricallyIntegral C.hom
  exact Scheme.h0_moduleKSheaf_of_bijective k C.left hbij

/-- **`χ(𝒪_C) = 1 − ledgerGenus C`** for the challenge curve: `h⁰ = 1` and `h¹ = genus` by the
frozen definition of the genus. -/
theorem chi_moduleKSheaf (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    Sheaf.chi (C.left.moduleKSheaf k) = 1 - ledgerGenus C := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  have h0 : Sheaf.h0 (C.left.moduleKSheaf k) = 1 := h0_moduleKSheaf C
  have hg : (ledgerGenus C : ℤ) = (Sheaf.h1 (C.left.moduleKSheaf k) : ℤ) := rfl
  rw [Sheaf.chi, h0]
  omega

/-- **Riemann–Roch-lite for the challenge curve** (★): for every Weil divisor `D` on the
smooth proper curve `C`, the Euler characteristic of `𝒪(D)` is
`χ(𝒪(D)) = 1 − ledgerGenus C + deg D`. -/
theorem chi_divisorSheaf_curve (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (D : C.left.CurveDivisor) :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
    Sheaf.chi (C.left.divisorSheaf k D) = 1 - ledgerGenus C + CurveDivisor.deg k D := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (QuasiCompact C.hom)
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    moduleFinite_hModule_zero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    moduleFinite_hModule_one C
  have h := chi_divisorSheaf k D
  have hO : Sheaf.chi (C.left.moduleKSheaf k) = 1 - ledgerGenus C := chi_moduleKSheaf C
  omega

/-- **The Riemann inequality for the challenge curve**:
`deg D + 1 − ledgerGenus C ≤ h⁰(𝒪(D))` for every Weil divisor `D`. -/
theorem riemann_inequality_curve (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (D : C.left.CurveDivisor) :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
    CurveDivisor.deg k D + 1 - ledgerGenus C ≤ (Sheaf.h0 (C.left.divisorSheaf k D) : ℤ) := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (QuasiCompact C.hom)
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    moduleFinite_hModule_zero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    moduleFinite_hModule_one C
  have h := riemann_inequality k D
  have hO : Sheaf.chi (C.left.moduleKSheaf k) = 1 - ledgerGenus C := chi_moduleKSheaf C
  omega

/-- **Unbounded growth of `h⁰` along multiples of a closed point** on the challenge
curve: for every closed point `x` and every bound `N` there is `n` with
`N ≤ h⁰(𝒪(n · x))`. No rational point is needed. -/
theorem h0_nsmul_point_unbounded_curve (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    {x : C.left} (hx : x ≠ genericPoint C.left) (N : ℕ) :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
    ∃ n : ℕ, N ≤ Sheaf.h0 (C.left.divisorSheaf k (n • Scheme.CurveDivisor.single hx 1)) := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (QuasiCompact C.hom)
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    moduleFinite_hModule_zero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    moduleFinite_hModule_one C
  exact h0_nsmul_point_unbounded k hx N

end Curve

end AlgebraicGeometry
