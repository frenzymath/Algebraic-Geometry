/-
Copyright (c) 2026 Axel Delaval. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval
-/
import AlgebraicJacobian.Picard.Pic0Dimension

/-!
# Homogeneity of a group scheme: translations, and the invariants they move

A group scheme is **homogeneous**: any point can be carried to any other by an automorphism
of the underlying scheme, namely a translation. This file supplies the translation and the
consequence the dimension chapter needs — that a *pointwise* invariant of the local rings is
constant along the orbit of the translations, so a bound at one point is a bound at every
point in that orbit.

## Why this file exists

`Picard/Pic0Dimension.lean` reduces `dim Pic⁰_{C/k} = g(C)` to two halves. The `≥` half
needs the cotangent dimension at the **identity** only, and is front (a) of this chapter.
The `≤` half is
```
∀ z, dim_{κ(z)} (m_z / m_z²) ≤ g
```
— a bound at *every* point
(`Pic0.topologicalKrullDim_le_genus_of_forall_finrank_cotangentSpace_le`).
The previous reading of that hypothesis was that it is a genuinely new *uniform* statement,
different in kind from the one-point identity front (a) produces. On a **group** scheme that
reading is too pessimistic, and this file records why: translations act transitively on the
rational points, and they are isomorphisms of the underlying scheme, so the cotangent
dimension is the same at any two points connected by one.

What this does and does not buy, stated precisely because the distinction is the whole
content:

* it **does** turn the uniform hypothesis into a statement about *one* orbit representative
  plus a transitivity statement about the points — `finrank_cotangentSpace_eq_of_pointTranslation`
  is the transport, and it is unconditional;
* it does **not** by itself discharge the uniform hypothesis, because the translations here are
  indexed by *sections* `𝟙_ (Over S) ⟶ G`, i.e. by `S`-rational points, and a scheme over a
  non-closed field has points that are not rational. Over an algebraically closed field the
  closed points are all rational and the orbit is the whole closed-point set; in general the
  residue-field extension is the gap. So the honest statement of what remains is "every point
  of `Pic⁰` is a translate of the identity", which is a statement about *points*, not about
  dimension theory.

That is a strictly better place for the residue than "a uniform cotangent bound", which is
what the roadmap recorded before: it moves the open content out of dimension theory (where
this project had to build `Picard/EmbeddingDimensionBound.lean` to make progress) and into
the homogeneity of a group scheme, where the mathematics is standard.

## Provenance

`CategoryTheory.GrpObj.pointTranslation` and its scheme-level shadow are ported from the
sibling project `Algebraic-Jacobian-Challenge-Rebuild`,
`AlgebraicJacobian/AbelianVariety/Translation.lean` (sorry-free there). The port is free:
the general half is pure `CartesianMonoidalCategory` reasoning on top of mathlib's
`CategoryTheory.GrpObj.mulRight` (`Mathlib/CategoryTheory/Monoidal/Grp.lean:275`) and needs
no project-specific input at all. AJC had no `pointTranslation` of any kind before this file
(grep: zero occurrences).

## Main declarations

* `CategoryTheory.GrpObj.pointTranslation` — the automorphism `(· * x⁻¹y)` of a group object,
  carrying the point `x` to the point `y`.
* `CategoryTheory.GrpObj.pointTranslationIso` — the same, as an isomorphism of the underlying
  scheme of a group scheme `G : Over S`.
* `AlgebraicGeometry.finrank_cotangentSpace_eq_of_isIso` — the cotangent dimension is
  invariant under an isomorphism of schemes.
* `AlgebraicGeometry.Pic0.finrank_cotangentSpace_eq_of_pointTranslation` — the cotangent
  dimension of `Pic⁰_{C/k}` at a translate of a point equals that at the point.
-/

universe v₁ u₁ u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory.GrpObj

section Categorical

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {G : C} [GrpObj G] {X : C}

/-- Composing with a right translation is Hom-group multiplication:
`f ≫ (mulRight g).hom = f * (toUnit X ≫ g)` in the group `X ⟶ G`. -/
theorem comp_mulRight_hom (f : X ⟶ G) (g : 𝟙_ C ⟶ G) :
    f ≫ (mulRight g).hom = f * (toUnit X ≫ g) := by
  rw [mulRight_hom, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc, Hom.mul_def]

/-- Composing with the inverse of a right translation divides in the Hom-group:
`f ≫ (mulRight g).inv = f * (toUnit X ≫ g)⁻¹` in the group `X ⟶ G`. -/
theorem comp_mulRight_inv (f : X ⟶ G) (g : 𝟙_ C ⟶ G) :
    f ≫ (mulRight g).inv = f * (toUnit X ≫ g)⁻¹ := by
  rw [mulRight_inv, comp_lift_assoc, Category.comp_id, ← Category.assoc, comp_toUnit,
    Hom.mul_def, Hom.inv_def, Category.assoc]

variable (G) in
/-- **The translation carrying the point `x` to the point `y`**: the automorphism
`(· * x⁻¹y)` of a group object, `(mulRight x)⁻¹ ≪≫ mulRight y`. This is the homogeneity
automorphism, packaged. -/
def pointTranslation (x y : 𝟙_ C ⟶ G) : G ≅ G :=
  (mulRight x).symm ≪≫ mulRight y

/-- The translation `pointTranslation x y` does carry `x` to `y`. -/
@[reassoc (attr := simp)]
theorem comp_pointTranslation_hom (x y : 𝟙_ C ⟶ G) :
    x ≫ (pointTranslation G x y).hom = y := by
  rw [pointTranslation, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, comp_mulRight_inv,
    comp_mulRight_hom, toUnit_unit, Category.id_comp, Category.id_comp, mul_inv_cancel,
    _root_.one_mul]

end Categorical

section SchemeLevel

open AlgebraicGeometry

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- The translation carrying the section `x` to the section `y`, as an isomorphism of the
underlying scheme of the group scheme `G : Over S`. -/
noncomputable def pointTranslationIso (x y : 𝟙_ (Over S) ⟶ G) : G.left ≅ G.left :=
  (Over.forget S).mapIso (pointTranslation G x y)

@[simp]
theorem pointTranslationIso_hom (x y : 𝟙_ (Over S) ⟶ G) :
    (pointTranslationIso G x y).hom = (pointTranslation G x y).hom.left :=
  rfl

@[simp]
theorem pointTranslationIso_inv (x y : 𝟙_ (Over S) ⟶ G) :
    (pointTranslationIso G x y).inv = (pointTranslation G x y).inv.left :=
  rfl

/-- Translations commute with the structure morphism: `pointTranslationIso` is an
automorphism of `G.left` *over* `S`. -/
@[reassoc (attr := simp)]
theorem pointTranslationIso_hom_comp (x y : 𝟙_ (Over S) ⟶ G) :
    (pointTranslationIso G x y).hom ≫ G.hom = G.hom :=
  Over.w _

/-- The action of `pointTranslationIso G x y` on underlying points: it carries the points of
the section `x` to the points of the section `y`. -/
theorem pointTranslationIso_hom_apply (x y : 𝟙_ (Over S) ⟶ G) (s : S) :
    (pointTranslationIso G x y).hom (x.left s) = y.left s := by
  rw [pointTranslationIso_hom]
  conv_rhs => rw [← comp_pointTranslation_hom (G := G) x y]
  rfl

end SchemeLevel

end CategoryTheory.GrpObj

/-! ## The cotangent dimension is an isomorphism invariant

The embedding dimension `dim_{κ(z)} (m_z / m_z²)` at a point is what
`Picard/EmbeddingDimensionBound.lean` bounds `ringKrullDim` by, and it is what the `≤` half of
`dim Pic⁰ = g` needs uniformly in `z`. It is invariant under any isomorphism of schemes, and
the proof needs no functoriality of `IsLocalRing.CotangentSpace` — which mathlib does not have
at this pin (`Mathlib/RingTheory/Ideal/Cotangent.lean` provides the module structure and the
finite-dimensionality but no map along a ring homomorphism).

The route is through `Submodule.spanFinrank` instead, where mathlib *does* have the one
inequality needed (`Ideal.spanRank_map_le`, `Mathlib/Algebra/Module/SpanRank.lean:399`): a ring
isomorphism gives the inequality in both directions, so antisymmetry gives the equality, and
Nakayama (`IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`) converts back into
cotangent currency. Recording the `spanFinrank` statement separately because it needs no
Noetherian hypothesis, unlike the cotangent form. -/

namespace AlgebraicGeometry

/-- **The minimal number of generators of the maximal ideal is a ring-isomorphism invariant.**

`Ideal.spanRank_map_le` gives `spanRank (I.map φ) ≤ spanRank I` for any ring homomorphism `φ`.
For an isomorphism `e` apply it to `e` and to `e.symm`; since `e.symm ∘ e = id` the second
application bounds `spanRank I` by `spanRank (I.map e)`, and antisymmetry closes it. The
maximal ideal is carried to the maximal ideal because a bijective ring map sends a maximal
ideal to a maximal ideal (`Ideal.IsMaximal.map_bijective`) and a local ring has only one.

No Noetherian hypothesis: `spanRank` is defined as an infimum of cardinals of spanning sets
(`Mathlib/Algebra/Module/SpanRank.lean:64`), and the argument never needs it to be finite. -/
theorem spanFinrank_maximalIdeal_eq_of_ringEquiv
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) :
    (IsLocalRing.maximalIdeal A).spanFinrank
      = (IsLocalRing.maximalIdeal B).spanFinrank := by
  have hmap : (IsLocalRing.maximalIdeal A).map (e : A →+* B) = IsLocalRing.maximalIdeal B := by
    apply IsLocalRing.eq_maximalIdeal
    exact (IsLocalRing.maximalIdeal.isMaximal A).map_bijective _ e.bijective
  have h1 := Ideal.spanRank_map_le (e : A →+* B) (IsLocalRing.maximalIdeal A)
  have h2 := Ideal.spanRank_map_le (e.symm : B →+* A)
    ((IsLocalRing.maximalIdeal A).map (e : A →+* B))
  rw [Ideal.map_map] at h2
  rw [show ((e.symm : B →+* A).comp (e : A →+* B)) = RingHom.id A from by ext a; simp,
    Ideal.map_id] at h2
  rw [← hmap]
  unfold Submodule.spanFinrank
  rw [le_antisymm h2 h1]

/-- **The cotangent dimension is a ring-isomorphism invariant.**

`spanFinrank_maximalIdeal_eq_of_ringEquiv` in cotangent currency, via Nakayama
(`IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`), which is where the
Noetherian hypothesis enters. -/
theorem finrank_cotangentSpace_eq_of_ringEquiv
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (e : A ≃+* B) :
    Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A)
      = Module.finrank (IsLocalRing.ResidueField B) (IsLocalRing.CotangentSpace B) := by
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    ← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact spanFinrank_maximalIdeal_eq_of_ringEquiv e

/-- **The cotangent dimension at `f x` equals the one at `x`, for `f` an isomorphism of
schemes.** The stalk map of an isomorphism is an isomorphism of rings, so this is
`finrank_cotangentSpace_eq_of_ringEquiv` at `f.stalkMap x`. -/
theorem finrank_cotangentSpace_stalk_eq_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (x : X) [IsLocalRing (X.presheaf.stalk x)] [IsLocalRing (Y.presheaf.stalk (f.base x))]
    [IsNoetherianRing (X.presheaf.stalk x)]
    [IsNoetherianRing (Y.presheaf.stalk (f.base x))] :
    Module.finrank (IsLocalRing.ResidueField (Y.presheaf.stalk (f.base x)))
        (IsLocalRing.CotangentSpace (Y.presheaf.stalk (f.base x)))
      = Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) :=
  finrank_cotangentSpace_eq_of_ringEquiv ((asIso (f.stalkMap x)).commRingCatIsoToRingEquiv)

/-! ### The homogeneity reduction for `Pic⁰_{C/k}`

What the two theorems above buy the dimension chapter. The `≤` half of `dim Pic⁰ = g` needs
```
∀ z, dim_{κ(z)} (m_z / m_z²) ≤ g
```
(`Pic0.topologicalKrullDim_le_genus_of_forall_finrank_cotangentSpace_le`). Since `Pic⁰` is a
group scheme, the translations are automorphisms of the underlying scheme, so this uniform
statement follows from the bound at **one** point together with the statement that every point
is a translate of it. The theorem below is that reduction, stated with the orbit condition as
a hypothesis so that what remains open is visible and is a statement about *points*.

Why the hypothesis is phrased with an existential over `Over S`-sections rather than "the
translations act transitively": the translations available here are indexed by sections
`𝟙_ (Over (Spec k)) ⟶ Pic0Scheme C`, i.e. by `k`-rational points. Over a non-closed field a
scheme has points whose residue field is a proper extension of `k`, and those are *not* reached
by a `k`-rational translation. So the hypothesis is exactly the gap, and it is not a
formality — over `k̄` it holds for closed points, in general it is a descent question. Naming
it is the point: it moves the residue out of dimension theory.

**RETRACTED (run 0067 r8), and this is the FOURTH framing of this leg to be wrong. The orbit
condition is not a gap that a descent argument can close: it is CONTRADICTORY for every curve
of genus `≥ 1`, so the two theorems below are VACUOUS exactly where the A.3 leg needs them.**

`Picard/HomogeneityOrbitCollapse.lean` proves
`Pic0.topologicalKrullDim_eq_zero_of_homogeneous`: the `htrans` hypothesis alone forces
`topologicalKrullDim Pic⁰_{C/k} = 0`, hence (with `hid`, `hreg`)
`Pic0.genus_eq_zero_of_homogeneous` — `genus C = 0`.

The error is visible in the paragraph above, in the phrase "over `k̄` it holds **for closed
points**". The hypothesis quantifies over **all** points of `Pic⁰`, and translations are
*isomorphisms of schemes*, hence homeomorphisms; the identity point is closed (it is the image
of a section of a morphism to `Spec k`, so a closed immersion's range). A homeomorphism carries
closed points to closed points, so `htrans` says every point of `Pic⁰` is closed — `T1` — and a
nonempty sober `T1` space has topological Krull dimension `0`. Nothing about `k` or the descent
question enters; the collapse is unconditional.

The corroboration was already in this project: the sibling irreducibility proof
(`identityComponent_irreducibleSpace_of_isAlgClosed`, `Picard/IdentityComponent.lean:866`)
translates through **closed** points only and then needs *Jacobson density* to "sweep up the
non-closed points". That extra step is exactly what a `k`-rational orbit cannot supply.

So the `≤` half's uniform cotangent bound is still owed, and it needs a route that reaches
**non-closed** points — transport along a translation by a point valued in an extension of `k`,
or a generic-point/density argument in the shape the sibling proof uses. What the two theorems
below establish remains true and is worth keeping as the *shape* of the reduction; what is
withdrawn is the claim that their hypothesis set is satisfiable for `g ≥ 1`, and with it the
"one point suffices" reading recorded at
`Picard/EmbeddingDimensionBound.lean`, `Picard/Pic0Dimension.lean` and
`Picard/IdentityComponent.lean`. The cotangent-invariance theorems above
(`finrank_cotangentSpace_eq_of_ringEquiv`, `finrank_cotangentSpace_stalk_eq_of_isIso`) are
about a single isomorphism and are untouched. -/

namespace Scheme.Pic0

open CategoryTheory.GrpObj PicScheme

/-- **The uniform cotangent bound on `Pic⁰_{C/k}` follows from the bound at one point plus
homogeneity.**

Given a group-object structure on `Pic⁰_{C/k}`, a base point `z₀` whose cotangent dimension is
at most `g`, and — the hypothesis carrying all the content — a presentation of every point `z`
as the image of `z₀` under a translation, the uniform bound of
`Pic0.topologicalKrullDim_le_genus_of_forall_finrank_cotangentSpace_le` follows.

The proof is `finrank_cotangentSpace_stalk_eq_of_isIso` at the translation isomorphism: the
translation is an isomorphism of `(Pic0Scheme C).left`, so the cotangent dimension at `z` is
the cotangent dimension at `z₀`, which is bounded by hypothesis.

Stated over an arbitrary field, per the standing owner decision (inbox I-0491): no
`[PerfectField k]`, no rational-point binder on the curve. -/
theorem forall_finrank_cotangentSpace_le_of_homogeneous {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    [GrpObj (Pic0Scheme C)]
    (z₀ : (Pic0Scheme C).left)
    (hz₀ : Module.finrank
        (IsLocalRing.ResidueField ((Pic0Scheme C).left.presheaf.stalk z₀))
        (IsLocalRing.CotangentSpace ((Pic0Scheme C).left.presheaf.stalk z₀))
      ≤ AlgebraicGeometry.genus C)
    (htrans : ∀ z : (Pic0Scheme C).left,
      ∃ x y : 𝟙_ (Over (Spec (.of k))) ⟶ Pic0Scheme C,
        (pointTranslationIso (Pic0Scheme C) x y).hom.base z₀ = z) :
    ∀ z : (Pic0Scheme C).left,
      Module.finrank (IsLocalRing.ResidueField ((Pic0Scheme C).left.presheaf.stalk z))
        (IsLocalRing.CotangentSpace ((Pic0Scheme C).left.presheaf.stalk z))
        ≤ AlgebraicGeometry.genus C := by
  haveI := AlgebraicGeometry.Scheme.Pic0.isLocallyNoetherian C
  intro z
  obtain ⟨x, y, hxy⟩ := htrans z
  have h := finrank_cotangentSpace_stalk_eq_of_isIso
    (pointTranslationIso (Pic0Scheme C) x y).hom z₀
  rw [hxy] at h
  rw [h]
  exact hz₀

/-- **`dim Pic⁰_{C/k} = g(C)` from the identity point alone, plus homogeneity.**

This is what the homogeneity reduction is for, and it is the sharpest form of the dimension
statement this chapter can state: the *only* local input is at the identity section, where
front (a)'s tangent identity `Pic0.finrank_cotangentSpace_eq_finrank_hModuleOne` computes
`dim_{κ(e)} m_e/m_e² = dim_k H¹(C, 𝒪_C) = g(C)` exactly.

Compare `Pic0.topologicalKrullDim_eq_genus_of_forall_finrank_cotangentSpace_le`, which takes
the uniform bound as a hypothesis. That hypothesis is here *derived*, from:

* the exact value at the identity (`hid`, which front (a) supplies);
* regularity at the identity (`hreg`, which over a perfect field follows from smoothness by
  `Scheme.isRegularLocalRing_stalk_of_smooth_of_perfectField`, and which is taken as a
  hypothesis here so that the statement holds over an **arbitrary** field, per I-0491);
* the orbit condition `htrans`.

So the three remaining inputs are all statements this chapter already names, and the
dimension theory is fully consumed: nothing here is about Krull dimension any more.

Note that `hid` is an *equality*, not a bound. That is what makes one point enough for both
directions: the `≤` half needs it only as `≤` (transported around the orbit), and the `≥`
half needs the exact value together with regularity at that same point. -/
theorem topologicalKrullDim_eq_genus_of_homogeneous {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    [GrpObj (Pic0Scheme C)]
    (hid : Module.finrank
        (IsLocalRing.ResidueField ((Pic0Scheme C).left.presheaf.stalk
          ((identitySection C).base default)))
        (IsLocalRing.CotangentSpace ((Pic0Scheme C).left.presheaf.stalk
          ((identitySection C).base default)))
      = AlgebraicGeometry.genus C)
    (hreg : IsRegularLocalRing ((Pic0Scheme C).left.presheaf.stalk
      ((identitySection C).base default)))
    (htrans : ∀ z : (Pic0Scheme C).left,
      ∃ x y : 𝟙_ (Over (Spec (.of k))) ⟶ Pic0Scheme C,
        (pointTranslationIso (Pic0Scheme C) x y).hom.base
          ((identitySection C).base default) = z) :
    topologicalKrullDim (Pic0Scheme C).left
      = ((AlgebraicGeometry.genus C : ℕ) : WithBot ℕ∞) := by
  haveI := AlgebraicGeometry.Scheme.Pic0.isLocallyNoetherian C
  exact topologicalKrullDim_eq_of_forall_finrank_cotangentSpace_le_of_regular
    (Pic0Scheme C).left _
    (forall_finrank_cotangentSpace_le_of_homogeneous C _ hid.le htrans)
    _ hreg hid

/-- **`dim Pic⁰_{C/k} = g(C)`, with front (a) plugged in: the dimension statement now has
exactly TWO open inputs, both named.**

`topologicalKrullDim_eq_genus_of_homogeneous` above with `hid` discharged from front (a)'s
tangent-space identity `Pic0.finrank_cotangentSpace_eq_finrank_hModuleOne` composed with the
genus definition `dim_k H¹(C, 𝒪_C) = g(C)`. What is left is:

* `hreg` — regularity of the stalk at the identity (free over a perfect field from smoothness;
  a hypothesis here to keep the statement over an arbitrary field, per I-0491);
* `htrans` — the orbit condition: every point of `Pic⁰` is a `k`-rational translate of the
  identity.

**MEASURE BEFORE QUOTING.** Like everything consuming front (a), this reports `sorryAx` at the
full root, inherited from `Pic0.semilinearComparison_cotangentSpaceDual_h1Cok`. The homogeneity
machinery of this file is axiom-clean on its own; the leak is front (a)'s and nothing else's.
This theorem is a *reduction*, and the honest reading is: given the tangent identity, the
dimension statement costs one regularity fact and one statement about points — no dimension
theory, no equidimensionality, no uniform bound. -/
theorem topologicalKrullDim_eq_genus_of_homogeneous_of_regular {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    [GrpObj (Pic0Scheme C)]
    (hreg : IsRegularLocalRing ((Pic0Scheme C).left.presheaf.stalk
      ((identitySection C).base default)))
    (htrans : ∀ z : (Pic0Scheme C).left,
      ∃ x y : 𝟙_ (Over (Spec (.of k))) ⟶ Pic0Scheme C,
        (pointTranslationIso (Pic0Scheme C) x y).hom.base
          ((identitySection C).base default) = z) :
    topologicalKrullDim (Pic0Scheme C).left
      = ((AlgebraicGeometry.genus C : ℕ) : WithBot ℕ∞) :=
  topologicalKrullDim_eq_genus_of_homogeneous C
    (AlgebraicGeometry.Scheme.Pic0.finrank_cotangentSpace_eq_finrank_hModuleOne C) hreg htrans

/-! ### The whole A.3 leg over its honest inputs

`Pic0.isAbelianVariety` (`Picard/Pic0AbelianVariety.lean`) states the four conjuncts of the
abelian-variety conclusion, and it consumes `Pic0.proper` and `Pic0.smooth`, i.e. the two
`sorry`s of that file. The theorem below states the same conclusion **plus the dimension**
over the reductions instead, so that the leg's total open content is visible in one signature
and can be checked against a probe rather than read off four docstrings.

Its hypotheses are exactly, and only:

* `hval` — the valuative existence criterion for `(Pic0Scheme C).hom`. This is the *whole* of
  properness (`Pic0.proper_of_valuativeCriterion`; the other three `IsProper` conjuncts are
  theorems of that file, and the ambient-`Pic` route is refuted — `Pic_{C/k}` is an infinite
  disjoint union over `deg ∈ ℤ`, so universal closedness would force `CompactSpace`).
* `hred` — `IsReduced` of the **single** scheme `Pic⁰ ×_{Spec k} Spec k̄`. This is the whole of
  smoothness *and* of geometric reducedness: `Pic0.smooth_of_isReduced_algebraicClosureBaseChange`
  gives smoothness, and `Pic0.geometricallyReduced_of_isReduced_algebraicClosureBaseChange`
  shows the same hypothesis discharges the reducedness obligation too.
* `hid` — the cotangent value at the identity, which is front (a).
* `hreg`, `htrans` — regularity at the identity and the orbit condition, as above.

Nothing else. Geometric irreducibility and the group-object structure are already theorems.
So the A.3 leg is five statements, of which `hid` is the load-bearing one and `hreg` is free
over a perfect field.

**WARNING (run 0067 r8): this theorem is VACUOUS for `g(C) ≥ 1`, because of `htrans`.** It is
true, and its four other hypotheses are the honest content of their respective legs, but
`Pic0.genus_eq_zero_of_homogeneous` (`Picard/HomogeneityOrbitCollapse.lean`) derives
`genus C = 0` from `hid`, `hreg`, `htrans` alone — so on a positive-genus curve the hypothesis
set cannot be satisfied and the conclusion says nothing. Do **not** quote this signature as "the
A.3 leg over its honest inputs": the dimension conjunct is the one that spoils it. The
`IsProper ∧ Smooth ∧ GeometricallyIrreducible ∧ GrpObj` part, over `hval` and `hred` only, is
sound and is the reading to use — see the retraction above the section for what the dimension
half actually needs. -/
theorem isAbelianVariety_of_dimension_genus {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    [GrpObj (Pic0Scheme C)]
    (hval : ValuativeCriterion.Existence (Pic0Scheme C).hom)
    (hred : IsReduced (Limits.pullback (Pic0Scheme C).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
    (hid : Module.finrank
        (IsLocalRing.ResidueField ((Pic0Scheme C).left.presheaf.stalk
          ((identitySection C).base default)))
        (IsLocalRing.CotangentSpace ((Pic0Scheme C).left.presheaf.stalk
          ((identitySection C).base default)))
      = AlgebraicGeometry.genus C)
    (hreg : IsRegularLocalRing ((Pic0Scheme C).left.presheaf.stalk
      ((identitySection C).base default)))
    (htrans : ∀ z : (Pic0Scheme C).left,
      ∃ x y : 𝟙_ (Over (Spec (.of k))) ⟶ Pic0Scheme C,
        (pointTranslationIso (Pic0Scheme C) x y).hom.base
          ((identitySection C).base default) = z) :
    IsProper (Pic0Scheme C).hom ∧ Smooth (Pic0Scheme C).hom ∧
      GeometricallyIrreducible (Pic0Scheme C).hom ∧
      Nonempty (GrpObj (Pic0Scheme C)) ∧
      topologicalKrullDim (Pic0Scheme C).left
        = ((AlgebraicGeometry.genus C : ℕ) : WithBot ℕ∞) :=
  ⟨AlgebraicGeometry.Scheme.Pic0.proper_of_valuativeCriterion C hval,
   AlgebraicGeometry.Scheme.Pic0.smooth_of_isReduced_algebraicClosureBaseChange C hred,
   AlgebraicGeometry.Scheme.Pic0.geometricallyIrreducible C,
   AlgebraicGeometry.Scheme.Pic0.grpObj C,
   topologicalKrullDim_eq_genus_of_homogeneous C hid hreg htrans⟩

/-- **The A.3 abelian-variety conclusion over its two honest inputs — the NON-VACUOUS
capstone** (run 0067 r8).

`isAbelianVariety_of_dimension_genus` above adds the dimension conjunct, and pays for it with
the orbit condition `htrans`, which is contradictory for `g(C) ≥ 1`
(`Pic0.genus_eq_zero_of_homogeneous`, `Picard/HomogeneityOrbitCollapse.lean`). This theorem is
that statement with the spoiled conjunct and its hypothesis removed: the four defining
abelian-variety properties of Milne §I.1, over

* `hval` — valuative existence, the whole of properness;
* `hred` — `IsReduced` of the **single** scheme `Pic⁰ ×_{Spec k} Spec k̄`, the whole of
  smoothness;

and nothing else. Geometric irreducibility and the group-object structure are theorems of
`Picard/Pic0AbelianVariety.lean`. Both hypotheses are satisfiable — neither constrains the
genus — so unlike the five-input form this is the signature to quote for the A.3 leg, with the
dimension statement `dim Pic⁰ = g` tracked separately as still owing the uniform cotangent
bound.

Same caveat as everything in this lane: measure axioms at a SYNTHESIS site. Stated over
`[HasPicScheme C]`, which the caller discharges. -/
theorem isAbelianVariety_of_valuative_of_isReduced {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (hval : ValuativeCriterion.Existence (Pic0Scheme C).hom)
    (hred : IsReduced (Limits.pullback (Pic0Scheme C).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) :
    IsProper (Pic0Scheme C).hom ∧ Smooth (Pic0Scheme C).hom ∧
      GeometricallyIrreducible (Pic0Scheme C).hom ∧
      Nonempty (GrpObj (Pic0Scheme C)) :=
  ⟨AlgebraicGeometry.Scheme.Pic0.proper_of_valuativeCriterion C hval,
   AlgebraicGeometry.Scheme.Pic0.smooth_of_isReduced_algebraicClosureBaseChange C hred,
   AlgebraicGeometry.Scheme.Pic0.geometricallyIrreducible C,
   AlgebraicGeometry.Scheme.Pic0.grpObj C⟩

end Scheme.Pic0

end AlgebraicGeometry
