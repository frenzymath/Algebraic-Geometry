/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAffPullIndep

/-!
# F5 — the `pull` field itself

`Picard/DivRepAffPullGlue.lean` glues the chart pulls of a *given* atlas factorization, and
`Picard/DivRepAffPullIndep.lean` shows the glued class does not depend on which factorization
was used.  This file takes the last step and *defines* the forward map:

* `AlgebraicGeometry.IsDivRepPullValue` — the characterizing property of the value: it
  restricts, over some atlas factorization of `v`, to the chart pull of every piece.
* `AlgebraicGeometry.divRepPullValue` — **the `pull` field**, `Classical.choice` over the
  factorization supplied by `divScheme_exists_chartFactor`.
* `AlgebraicGeometry.divRepPullValue_spec` / `_eq_of` — it satisfies the property, and it is
  the *unique* class satisfying it.  `_eq_of` is what makes the definition usable: a caller
  who has *any* factorization of `v` and *any* class restricting to its chart pulls knows that
  class is `divRepPullValue v`, without ever unfolding the choice.

**Why the choice is harmless, and this is the whole point of the two previous files.** The
value is pinned by `IsDivRepPullValue` up to nothing at all: two classes with the property
have factorizations, possibly different ones, and
`divRepPullGlue_eq_of_chartFactors` equates them across the cross-refinement.  So
`divRepPullValue` is a function of `v` alone, and the `Classical.choice` never leaks into a
statement.

The remaining fields of `DivRepAffinePullback` are `isDivRepClassify_pull` (the ε-gated one)
and `pull_naturality`, whose carrier transport is `Picard/DivRepAwayPush.lean`.  As everywhere
in this layer, all of it is conditional on a supplied chart family `U` and its compatibility
`hU` — see the header of `Picard/DivRepAffPullIndep.lean` for what that conditionality does and
does not buy.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Grassmannian Scheme

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftDivRepAffPullField :
    C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
  [IsDominant pi]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g : ℕ)
variable (r1 r2 : ℕ)
variable (b1 : Module.Basis (Fin r1) k
  ↥(divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(divisorSections k
    ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤))

local notation "DivOver" =>
  divSchemeOver k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm)

local notation "ChartRing" => fun i j =>
  DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm) i j

local notation "ChartMap" => fun i j =>
  divCarveChartToDivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm) i j

/-! ## The characterizing property -/

/-- **The characterizing property of the forward map's value at `v`**: for SOME atlas
factorization of `v` — a spanning family `f`, chart indices and chart maps `cw` presenting `v`
over each `Localization.Away (f t)` — the class `F₀` restricts to the chart pull of every
piece.

The existential over the factorization is what makes this usable as a specification: by
`divRepPullGlue_eq_of_chartFactors` the property already determines `F₀`, so no caller has to
match the particular factorization the definition happens to choose. -/
def IsDivRepPullValue
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    {S : Type u} [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver)
    (F₀ : DivFamZar C S pi g) : Prop :=
  ∃ (m : ℕ) (f : Fin m → S), Ideal.span (Set.range f) = ⊤ ∧
    ∃ (ci : Fin m → (glueData k g r1).J) (cj : Fin m → (glueData k g r2).J)
      (cw : ∀ t : Fin m, ChartRing (ci t) (cj t) →ₐ[k] Localization.Away (f t)),
      (∀ t : Fin m,
        Spec.map (CommRingCat.ofHom (cw t).toRingHom) ≫ ChartMap (ci t) (cj t)
          = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f t))))
            ≫ v.left) ∧
      ∀ t : Fin m,
        DivFamZar.mapAlgHom (IsScalarTower.toAlgHom k S (Localization.Away (f t))) F₀
          = divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U (ci t) (cj t) (cw t)

/-! ## Uniqueness -/

/-- **The property determines the value**: two classes with `IsDivRepPullValue` for the same
`v` are equal.  Each comes with its own factorization, and
`divRepPullGlue_eq_of_chartFactors` equates them over the cross-refinement — which is exactly
the U2-free independence statement, used here for the purpose it was proved for. -/
theorem isDivRepPullValue_unique
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hU : DivRepChartFamily.IsCompatible (hpi := hpi) g r1 r2 b1 b2 U)
    {S : Type u} [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver)
    {F₀ F₁ : DivFamZar C S pi g}
    (h₀ : IsDivRepPullValue (hpi := hpi) g r1 r2 b1 b2 U v F₀)
    (h₁ : IsDivRepPullValue (hpi := hpi) g r1 r2 b1 b2 U v F₁) :
    F₀ = F₁ := by
  obtain ⟨m, f, hspan, ci, cj, cw, hcw, hF₀⟩ := h₀
  obtain ⟨m', f', hspan', ci', cj', cw', hcw', hF₁⟩ := h₁
  exact divRepPullGlue_eq_of_chartFactors hpi g r1 r2 b1 b2 U hU v f f' hspan hspan'
    ci cj cw hcw ci' cj' cw' hcw' hF₀ hF₁

/-! ## Existence, and the definition -/

/-- **Existence of the value**: the atlas factorization `divScheme_exists_chartFactor` supplies
a factorization of `v`, and `exists_divRepPullGlue` glues its chart pulls. -/
theorem exists_isDivRepPullValue
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hU : DivRepChartFamily.IsCompatible (hpi := hpi) g r1 r2 b1 b2 U)
    {S : Type u} [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver) :
    ∃ F₀ : DivFamZar C S pi g,
      IsDivRepPullValue (hpi := hpi) g r1 r2 b1 b2 U v F₀ := by
  classical
  obtain ⟨m, f, hspan, hdata⟩ := divScheme_exists_chartFactor k
    (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm) S v
  choose ci cj cw hcw using hdata
  obtain ⟨F₀, hF₀⟩ := exists_divRepPullGlue hpi g r1 r2 b1 b2 U hU v f hspan ci cj cw hcw
  exact ⟨F₀, m, f, hspan, ci, cj, cw, hcw, hF₀⟩

/-- **The `pull` field of `DivRepAffinePullback`**: the forward map of DDR-9's F5, over a
supplied compatible chart family.  Defined by choice over the atlas factorization, and pinned
by `IsDivRepPullValue` — so the choice is invisible to every statement about it
(`divRepPullValue_eq_of`). -/
noncomputable def divRepPullValue
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hU : DivRepChartFamily.IsCompatible (hpi := hpi) g r1 r2 b1 b2 U)
    (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver) :
    DivFamZar C S pi g :=
  (exists_isDivRepPullValue hpi g r1 r2 b1 b2 U hU v).choose

/-- The forward map satisfies its characterizing property. -/
theorem divRepPullValue_spec
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hU : DivRepChartFamily.IsCompatible (hpi := hpi) g r1 r2 b1 b2 U)
    (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver) :
    IsDivRepPullValue (hpi := hpi) g r1 r2 b1 b2 U v
      (divRepPullValue hpi g r1 r2 b1 b2 U hU S v) :=
  (exists_isDivRepPullValue hpi g r1 r2 b1 b2 U hU v).choose_spec

/-- **The usable form**: ANY class satisfying the characterizing property for `v` IS the
forward map's value at `v`.  A caller with a factorization of their own never unfolds the
choice made in `divRepPullValue`. -/
theorem divRepPullValue_eq_of
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hU : DivRepChartFamily.IsCompatible (hpi := hpi) g r1 r2 b1 b2 U)
    (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver)
    {F₀ : DivFamZar C S pi g}
    (hF₀ : IsDivRepPullValue (hpi := hpi) g r1 r2 b1 b2 U v F₀) :
    divRepPullValue hpi g r1 r2 b1 b2 U hU S v = F₀ :=
  isDivRepPullValue_unique hpi g r1 r2 b1 b2 U hU v
    (divRepPullValue_spec hpi g r1 r2 b1 b2 U hU S v) hF₀

/-- **The value restricts to the chart pulls of any factorization**: the direct consequence of
`divRepPullValue_eq_of`, in the form the naturality and clause fields will consume. -/
theorem mapAlgHom_divRepPullValue
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hU : DivRepChartFamily.IsCompatible (hpi := hpi) g r1 r2 b1 b2 U)
    (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver)
    {m : ℕ} (f : Fin m → S) (hspan : Ideal.span (Set.range f) = ⊤)
    (ci : Fin m → (glueData k g r1).J) (cj : Fin m → (glueData k g r2).J)
    (cw : ∀ t : Fin m, ChartRing (ci t) (cj t) →ₐ[k] Localization.Away (f t))
    (hcw : ∀ t : Fin m,
      Spec.map (CommRingCat.ofHom (cw t).toRingHom) ≫ ChartMap (ci t) (cj t)
        = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f t)))) ≫ v.left)
    (t : Fin m) :
    DivFamZar.mapAlgHom (IsScalarTower.toAlgHom k S (Localization.Away (f t)))
        (divRepPullValue hpi g r1 r2 b1 b2 U hU S v)
      = divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U (ci t) (cj t) (cw t) := by
  obtain ⟨F₀, hF₀⟩ := exists_divRepPullGlue hpi g r1 r2 b1 b2 U hU v f hspan ci cj cw hcw
  rw [divRepPullValue_eq_of hpi g r1 r2 b1 b2 U hU S v
    ⟨m, f, hspan, ci, cj, cw, hcw, hF₀⟩]
  exact hF₀ t

end Curve

end AlgebraicGeometry
