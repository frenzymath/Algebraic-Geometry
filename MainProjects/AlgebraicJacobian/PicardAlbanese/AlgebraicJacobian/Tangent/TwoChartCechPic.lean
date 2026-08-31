/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RefinementInjectivity
import AlgebraicJacobian.Cohomology.AffineCech
import AlgebraicJacobian.Tangent.TruncExpCech

/-!
# The two-chart Čech `Ȟ¹` of units embeds in the Picard group (W5-T4 clause (iii-a)/(iii-b))

For a scheme `X` with two opens `V₀ ⊔ V₁ = ⊤`, the two-chart Čech cohomology of units

```
Ȟ¹(V₀,V₁ ; 𝒪ˣ)  =  Γ(X, V₀ ⊓ V₁)ˣ ⧸ (im Γ(V₀)ˣ · im Γ(V₁)ˣ)
```

maps to the definitional Picard group `X.CechPic`, **injectively**
(`Scheme.twoChartClass_injective`). This file builds that map and proves the injectivity.

## Why this file exists: clauses (iii-a) and (iii-b), which are not about dual numbers

`informal/w5-t4-worksheet.md` §6 splits the Wave-5 residue "clause (iii)" — the last input to
the Kleiman §5 Thm. 5.11 dimension identity — into three parts, and observes that **two of
them contain no dual numbers, no curves and no `H¹`**. Those two are exactly this file:

* **(iii-a)** the comparison homomorphism `twoChartClass` exists;
* **(iii-b)** it is injective.

Both are general statements about a scheme with a two-open cover, so they are stated here at
that generality rather than at `C ×_k Spec k[ε]`. The remaining part, **(iii-c)**
(surjectivity onto the `ε`-kernel), is the only one that needs the thickening; it consumes
`DualNumber.free_of_cyclic_mod_eps` and lives elsewhere.

The two-chart Čech quotient here is the **same carrier** the truncated-exponential engine of
`Tangent/TruncExpCech.lean` computes: `TruncExpCech.cechCoboundaryUnits` of the two restriction
maps. So `twoChartClass` is precisely the arrow that connects the (landed) T2 engine to the
(definitional) Picard group, in the direction the tangent computation needs.

## Implementation notes

`CechPic` is built on **pointed** covers — one open per point — so a two-open cover enters
through a selector `sel : X → Bool` with `x ∈ V (sel x)`, exactly as
`BasicOpenCocycleDatum.pieceIndex` and `thetaFieldChartIndex` do elsewhere in the tree.
Indexing the charts by `Bool` (rather than by two named opens) is what makes the cocycle law a
`cases`-bash that closes uniformly.

The cocycle attached to an overlap unit `u` has pair values `1` on the diagonal, `u` at
`(0,1)` and the `inf_comm`-transport of `u⁻¹` at `(1,0)` (`Scheme.twoChartPairUnit`).

**A negative result, recorded so it is not retried** (worksheet §6.2): the slick spelling
`pairUnit s t = u ^ (δ t − δ s)`, which would close the cocycle law by `zpow_add` alone, does
**not** typecheck. On the diagonal the ambient open `T` need only be `≤ V s`, where `u` — a
section on `V₀ ⊓ V₁` — cannot be restricted at all. The exponent trick needs a unit on the
union and there is none. The eight-case `cases` bash is the honest route, and it is three
lines.

## Main declarations

* `AlgebraicGeometry.Scheme.twoChartPairUnit` — the pair values, with
  `twoChartPairUnit_trans` (the cocycle law, all eight `Bool` cases) and
  `twoChartPairUnit_mul` (multiplicativity in the overlap unit).
* `AlgebraicGeometry.Scheme.twoChartCover` — the pointed cover of a selector.
* `AlgebraicGeometry.Scheme.twoChartCocycle` — the unit Čech 1-cocycle of an overlap unit.
* `AlgebraicGeometry.Scheme.twoChartClassHom` — `Γ(V₀ ⊓ V₁)ˣ →* X.CechPic`, the map before
  passing to the quotient, with `twoChartClassHom_eq_one_iff` (the kernel computation, where
  refinement injectivity enters).
* `AlgebraicGeometry.Scheme.twoChartClass` — **(iii-a)**: the induced homomorphism
  `Γ(V₀ ⊓ V₁)ˣ ⧸ cechCoboundaryUnits → X.CechPic`.
* `AlgebraicGeometry.Scheme.twoChartClass_injective` — **(iii-b)**.

## What the surjectivity hypothesis is for

`twoChartClassHom_eq_one_iff` and everything downstream take `hsel : Function.Surjective sel`
— the selector must actually use both charts. This is not bookkeeping: the cobounding
`0`-cochain produced by refinement injectivity is indexed by *points*, and turning it into a
pair of *chart* units needs one point assigned to each chart. See that lemma's docstring.

A second trap recorded at `twoChartCoboundary_of_pairRelation`: transporting a chart unit
along `sel i = false` with `▸` produces an ill-typed motive, because the type of a section
depends on the open which depends on the `Bool`. Abstracting the chart indices as variables
and using `subst` avoids the transport entirely.

Reference: Kleiman, "The Picard scheme", §5, proof of Thm. 5.11 (arXiv:math/0504020).
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}} {V : Bool → X.Opens}

/-- `Units.map` of the section-restriction ring map **is** `unitsRestrict`, definitionally.
Named so that the two spellings — the one `TruncExpCech.cechCoboundaryUnits` is stated in and
the one the Čech cocycle API uses — can be rewritten into each other. -/
@[simp]
theorem unitsMap_resHom {U W : X.Opens} (h : W ≤ U) :
    Units.map (X.resHom h).toMonoidHom = X.unitsRestrict h :=
  rfl

/-! ## The pair values of an overlap unit -/

/-- **The pair values of the two-chart cocycle attached to an overlap unit `u`.** Trivial on
the diagonal, `u` at `(0,1)`, and the `inf_comm`-transport of `u⁻¹` at `(1,0)`.

The diagonal entries are forced to be `1`: a cocycle value at `(s,s)` lives on opens contained
in `V s` alone, where an overlap section has no meaning. This is also why the `zpow` spelling
of these values does not typecheck — see the module docstring. -/
noncomputable def twoChartPairUnit (u : Γ(X, V false ⊓ V true)ˣ) :
    ∀ s t : Bool, Γ(X, V s ⊓ V t)ˣ
  | false, false => 1
  | true,  true  => 1
  | false, true  => u
  | true,  false => X.unitsRestrict (le_of_eq (inf_comm _ _)) u⁻¹

/-- **The cocycle law for the two-chart pair values**, in the form
`PresheafOfGroups.OneCocycle.ofPairs` consumes: on any open `T` below the three relevant
overlaps, the product of the `(s,t)` and `(t,r)` values is the `(s,r)` value.

All eight `Bool` cases at once: the four with `s = r` cancel `u · u⁻¹`, the four others are
`1 · u = u` after the diagonal entries reduce. -/
theorem twoChartPairUnit_trans (u : Γ(X, V false ⊓ V true)ˣ) (s t r : Bool) (T : X.Opens)
    (h₀ : T ≤ V s ⊓ V t) (h₁ : T ≤ V t ⊓ V r) (h₂ : T ≤ V s ⊓ V r) :
    X.unitsRestrict h₀ (twoChartPairUnit u s t)
        * X.unitsRestrict h₁ (twoChartPairUnit u t r)
      = X.unitsRestrict h₂ (twoChartPairUnit u s r) := by
  cases s <;> cases t <;> cases r <;>
    simp only [twoChartPairUnit, map_one, one_mul, mul_one, unitsRestrict_unitsRestrict,
      map_inv] <;>
    first | rfl | exact mul_inv_cancel _

/-- The pair values are multiplicative in the overlap unit — the input to
`twoChartClassHom` being a group homomorphism. -/
theorem twoChartPairUnit_mul (u v : Γ(X, V false ⊓ V true)ˣ) (s t : Bool) :
    twoChartPairUnit (u * v) s t = twoChartPairUnit u s t * twoChartPairUnit v s t := by
  cases s <;> cases t <;>
    (simp only [twoChartPairUnit, mul_one, mul_inv_rev, map_mul, map_inv]
     try first | rfl | exact mul_comm _ _)

/-- The pair values of the unit `1` are trivial. -/
@[simp]
theorem twoChartPairUnit_one (s t : Bool) :
    twoChartPairUnit (V := V) 1 s t = 1 := by
  cases s <;> cases t <;> simp [twoChartPairUnit]

/-! ## The pointed cover of a selector -/

/-- **The pointed cover attached to a chart selector.** A two-open cover becomes a pointed
cover (one open per point) by choosing, for each `x`, a chart containing it — the same pattern
as `BasicOpenCocycleDatum.pieceIndex` and `thetaFieldChartIndex`. -/
noncomputable def twoChartCover (V : Bool → X.Opens) (sel : X → Bool)
    (hmem : ∀ x, x ∈ V (sel x)) : X.PointedCover where
  opens x := V (sel x)
  mem_opens := hmem

@[simp]
theorem twoChartCover_opens (V : Bool → X.Opens) (sel : X → Bool)
    (hmem : ∀ x, x ∈ V (sel x)) (x : X) :
    (twoChartCover V sel hmem).opens x = V (sel x) :=
  rfl

/-- The pair value of the two-chart cocycle at a pair of points, retyped on the overlap of
the pointed cover's members. -/
noncomputable def twoChartCoverUnit (u : Γ(X, V false ⊓ V true)ˣ) (sel : X → Bool)
    (hmem : ∀ x, x ∈ V (sel x)) (x y : X) :
    Γ(X, (twoChartCover V sel hmem).opens x ⊓ (twoChartCover V sel hmem).opens y)ˣ :=
  twoChartPairUnit u (sel x) (sel y)

/-- **The unit Čech 1-cocycle of an overlap unit** on the two-chart pointed cover. -/
noncomputable def twoChartCocycle (u : Γ(X, V false ⊓ V true)ˣ) (sel : X → Bool)
    (hmem : ∀ x, x ∈ V (sel x)) : X.unitsCocycle (twoChartCover V sel hmem) :=
  OneCocycle.ofPairs (G := X.unitsPresheaf ⋙ forget₂ CommGrpCat GrpCat)
    (U := (twoChartCover V sel hmem).opens)
    (fun x y => twoChartCoverUnit u sel hmem x y)
    (fun x y z => twoChartPairUnit_trans u (sel x) (sel y) (sel z) _ _ _ _)

@[simp]
theorem twoChartCocycle_unitsEvInf (u : Γ(X, V false ⊓ V true)ˣ) (sel : X → Bool)
    (hmem : ∀ x, x ∈ V (sel x)) (x y : X) :
    Scheme.unitsEvInf (twoChartCocycle u sel hmem) x y = twoChartPairUnit u (sel x) (sel y) :=
  OneCocycle.ofPairs_evInf (G := X.unitsPresheaf ⋙ forget₂ CommGrpCat GrpCat)
    (U := (twoChartCover V sel hmem).opens) _ _ x y

/-- Cocycles are determined by their pair values (`unitsEvInf`), so a two-chart cocycle
identity can be checked pointwise on pairs. -/
theorem twoChartCocycle_eq_iff (u v : Γ(X, V false ⊓ V true)ˣ) (sel : X → Bool)
    (hmem : ∀ x, x ∈ V (sel x)) :
    twoChartCocycle u sel hmem = twoChartCocycle v sel hmem
      ↔ ∀ x y : X, twoChartPairUnit u (sel x) (sel y) = twoChartPairUnit v (sel x) (sel y) := by
  constructor
  · intro h x y
    have h' := congrArg (fun γ => Scheme.unitsEvInf γ x y) h
    rw [twoChartCocycle_unitsEvInf, twoChartCocycle_unitsEvInf] at h'
    exact h'
  · intro h
    refine OneCocycle.ext (OneCochain.ext ?_)
    funext i j T a b
    change Scheme.unitsRestrict X _ (twoChartPairUnit u (sel i) (sel j))
      = Scheme.unitsRestrict X _ (twoChartPairUnit v (sel i) (sel j))
    rw [h i j]

/-- The two-chart cocycle of the unit `1` is trivial. -/
@[simp]
theorem twoChartCocycle_one (sel : X → Bool) (hmem : ∀ x, x ∈ V (sel x)) :
    twoChartCocycle (V := V) 1 sel hmem = 1 := by
  refine OneCocycle.ext (OneCochain.ext ?_)
  funext i j T a b
  change Scheme.unitsRestrict X _ (twoChartPairUnit (V := V) 1 (sel i) (sel j)) = 1
  rw [twoChartPairUnit_one, map_one]

/-- The two-chart cocycle is multiplicative in the overlap unit. -/
theorem twoChartCocycle_mul (u v : Γ(X, V false ⊓ V true)ˣ) (sel : X → Bool)
    (hmem : ∀ x, x ∈ V (sel x)) :
    twoChartCocycle (u * v) sel hmem = twoChartCocycle u sel hmem * twoChartCocycle v sel hmem := by
  refine OneCocycle.ext (OneCochain.ext ?_)
  funext i j T a b
  change Scheme.unitsRestrict X _ (twoChartPairUnit (u * v) (sel i) (sel j))
    = Scheme.unitsRestrict X _ (twoChartPairUnit u (sel i) (sel j))
      * Scheme.unitsRestrict X _ (twoChartPairUnit v (sel i) (sel j))
  rw [twoChartPairUnit_mul, map_mul]
  rfl

/-! ## The comparison homomorphism into the Picard group -/

/-- **The Čech Picard class of an overlap unit**, on the two-chart pointed cover: a group
homomorphism `Γ(V₀ ⊓ V₁)ˣ →* X.CechPic`. This is (iii-a) before passing to the quotient by
the coboundaries. -/
noncomputable def twoChartClassHom (V : Bool → X.Opens) (sel : X → Bool)
    (hmem : ∀ x, x ∈ V (sel x)) : Γ(X, V false ⊓ V true)ˣ →* X.CechPic where
  toFun u := Scheme.CechPic.mk (twoChartCover V sel hmem) (twoChartCocycle u sel hmem).class
  map_one' := by rw [twoChartCocycle_one]; exact Scheme.CechPic.mk_one _
  map_mul' u v := by
    rw [Scheme.CechPic.mk_mul_mk, twoChartCocycle_mul]
    rfl

@[simp]
theorem twoChartClassHom_apply (V : Bool → X.Opens) (sel : X → Bool)
    (hmem : ∀ x, x ∈ V (sel x)) (u : Γ(X, V false ⊓ V true)ˣ) :
    twoChartClassHom V sel hmem u
      = Scheme.CechPic.mk (twoChartCover V sel hmem) (twoChartCocycle u sel hmem).class :=
  rfl

/-! ## (iii-b): the kernel of the comparison is exactly the coboundaries -/

/-- **The `0`-cochain exhibiting a coboundary unit as a coboundary.** For chart units
`v₁ ∈ Γ(V₀)ˣ`, `v₂ ∈ Γ(V₁)ˣ`, the family `false ↦ v₁⁻¹`, `true ↦ v₂`.

Written as a dependent match on the `Bool` so that each branch has the *right type on the
nose* — no transport along an equality of opens is needed anywhere, which is the whole reason
the charts are indexed by `Bool` in this file. -/
noncomputable def twoChartCob (v₁ : Γ(X, V false)ˣ) (v₂ : Γ(X, V true)ˣ) :
    ∀ s : Bool, Γ(X, V s)ˣ
  | false => v₁⁻¹
  | true  => v₂

/-- **The coboundary relation for `twoChartCob`**: if `u = ρ₀(v₁) · ρ₁(v₂)` then the
`0`-cochain `twoChartCob v₁ v₂` conjugates the pair values of `u` to `1`. All four `Bool`
cases; the two off-diagonal ones are where the hypothesis is spent. -/
theorem twoChartCob_spec (v₁ : Γ(X, V false)ˣ) (v₂ : Γ(X, V true)ˣ)
    (u : Γ(X, V false ⊓ V true)ˣ)
    (hv : Units.map (X.resHom (inf_le_left : V false ⊓ V true ≤ V false)).toMonoidHom v₁
        * Units.map (X.resHom (inf_le_right : V false ⊓ V true ≤ V true)).toMonoidHom v₂ = u)
    (s t : Bool) (T : X.Opens) (h₀ : T ≤ V s ⊓ V t) (ha : T ≤ V s) (hb : T ≤ V t) :
    X.unitsRestrict ha (twoChartCob v₁ v₂ s) * X.unitsRestrict h₀ (twoChartPairUnit u s t)
      = X.unitsRestrict hb (twoChartCob v₁ v₂ t) := by
  subst hv
  cases s <;> cases t <;>
    (simp only [twoChartCob, twoChartPairUnit, map_one, mul_one, map_mul, map_inv,
       unitsMap_resHom, unitsRestrict_unitsRestrict]
     try first | rfl | (rw [inv_mul_cancel_left]) | group)

/-- **From a coboundary relation at a mixed pair of chart indices to membership in the
coboundary subgroup.**

The point of stating this with the chart indices `s`, `t` as **variables** constrained by
`hs : s = false`, `ht : t = true` — rather than substituting `false`/`true` directly — is that
the two chart units arrive as `α i : Γ(V (sel i))ˣ` for points `i`, and `sel i = false` is a
*propositional* equality. Rewriting the goal along it with `▸` produces an ill-typed motive
(the section type depends on the open, which depends on the Bool). With the indices abstract,
`subst` does the same work with no transport at all.

Recorded because the `▸` route looks obviously right and fails with a `motive is not type
correct` error that reads as though the statement were wrong. -/
theorem twoChartCoboundary_of_pairRelation {s t : Bool} (hs : s = false) (ht : t = true)
    (u : Γ(X, V false ⊓ V true)ˣ) (a : Γ(X, V s)ˣ) (b : Γ(X, V t)ˣ)
    (key : X.unitsRestrict (inf_le_left : V s ⊓ V t ≤ V s) a * twoChartPairUnit u s t
      = X.unitsRestrict inf_le_right b) :
    u ∈ TruncExpCech.cechCoboundaryUnits
      (X.resHom (inf_le_left : V false ⊓ V true ≤ V false))
      (X.resHom (inf_le_right : V false ⊓ V true ≤ V true)) := by
  subst hs
  subst ht
  refine TruncExpCech.mem_cechCoboundaryUnits.mpr ⟨a⁻¹, b, ?_⟩
  simp only [unitsMap_resHom, map_inv]
  rw [twoChartPairUnit] at key
  rw [← key]
  group

/-- **The Picard class of an overlap unit is trivial iff the unit is a Čech coboundary**
— (iii-b), and the heart of this file.

`←` is the coboundary computation. `→` is where **refinement injectivity** enters: by the
landed `CechPic.mk_eq_one_iff` a Picard class on a fixed cover is trivial only if its `H¹`
class already is, so the cobounding `0`-cochain `α : ∀ x, Γ(V (sel x))ˣ` exists *on the
two-chart cover itself*. Evaluating the coboundary relation at one point of each chart turns
`α` into a pair of chart units exhibiting `u` as a coboundary.

**The hypothesis `Function.Surjective sel` is genuinely needed, and is not bookkeeping.** The
`0`-cochain `α` is indexed by *points*; to extract the two chart units the argument needs a
point assigned to each chart. If `sel` misses a value, the cover is really a one-chart cover
and no chart unit for the missing chart is produced. (Note the missing-chart case is not a
counterexample to the statement — if `V false = ⊥` then `Γ(V false ⊓ V true)ˣ` is trivial
anyway — but it is not *provable* along this route, so the hypothesis stays.) -/
theorem twoChartClassHom_eq_one_iff (V : Bool → X.Opens) (sel : X → Bool)
    (hmem : ∀ x, x ∈ V (sel x)) (hsel : Function.Surjective sel)
    (u : Γ(X, V false ⊓ V true)ˣ) :
    twoChartClassHom V sel hmem u = 1
      ↔ u ∈ TruncExpCech.cechCoboundaryUnits
          (X.resHom (inf_le_left : V false ⊓ V true ≤ V false))
          (X.resHom (inf_le_right : V false ⊓ V true ≤ V true)) := by
  constructor
  · intro h
    -- refinement injectivity: the `H¹` class is already trivial on the two-chart cover
    rw [twoChartClassHom_apply, Scheme.CechPic.mk_eq_one_iff,
      show (1 : X.unitsH1 (twoChartCover V sel hmem)) = OneCocycle.class 1 from rfl] at h
    obtain ⟨α, hα⟩ :=
      (OneCocycle.isCohomologous_iff_evInf _ _).mp ((OneCocycle.class_eq_iff _ _).mp h)
    -- pick a point in each chart
    obtain ⟨i, hi⟩ := hsel false
    obtain ⟨j, hj⟩ := hsel true
    have key : X.unitsRestrict (inf_le_left : V (sel i) ⊓ V (sel j) ≤ V (sel i)) (α i)
        * twoChartPairUnit u (sel i) (sel j)
          = X.unitsRestrict inf_le_right (α j) := by
      have h1 := hα i j
      rw [OneCocycle.one_evInf, one_mul] at h1
      rw [← twoChartCocycle_unitsEvInf u sel hmem i j]
      exact h1
    exact twoChartCoboundary_of_pairRelation hi hj u (α i) (α j) key
  · intro h
    obtain ⟨v₁, v₂, hv⟩ := TruncExpCech.mem_cechCoboundaryUnits.mp h
    rw [twoChartClassHom_apply,
      show (1 : X.CechPic) = Scheme.CechPic.mk (twoChartCover V sel hmem) 1 from
        (Scheme.CechPic.mk_one _).symm]
    refine congrArg _ ?_
    rw [show (1 : X.unitsH1 (twoChartCover V sel hmem)) = OneCocycle.class 1 from rfl]
    refine (OneCocycle.class_eq_iff _ _).mpr
      ((OneCocycle.isCohomologous_iff_evInf _ _).mpr
        ⟨fun x => twoChartCob v₁ v₂ (sel x), fun x y => ?_⟩)
    rw [OneCocycle.one_evInf, one_mul]
    exact twoChartCob_spec v₁ v₂ u hv (sel x) (sel y) _ _ _ _

/-! ## Towards (iii-c1): extracting the overlap unit of a general two-chart cocycle

The remaining clause `(iii-c1)` (`informal/w5-t4-worksheet.md` §6.6) is a **normalization**:
a general `γ : X.unitsCocycle (twoChartCover V sel hmem)` need *not* be of the form
`twoChartCocycle u`, because at a pair `(x, x')` with `sel x = sel x'` its value lives on
`V s ⊓ V s = V s` and is an arbitrary unit there, whereas `twoChartPairUnit` is `1` on such
pairs.

**Why `OneCocycle.ev_refl` does not settle this**, which is the trap: it forces a value to `1`
only when the two *indices* coincide, not when their *opens* do — and on a pointed cover many
points share a chart. The same-chart values are genuine data to be normalized away (by
conjugating with the `0`-cochain `x ↦ γ.evInf x (base (sel x))`, which is where selector
surjectivity is used a second time).

What is provided here is the piece the worksheet says to write *first*: the `subst`-shaped
extractor of the mixed-pair value, so that no `rw` ever has to happen inside a type. -/

/-- **Transport of an overlap unit along the chart indices, by `subst` rather than by `▸`.**
With `s`, `t` abstract and constrained propositionally, `subst` retypes the unit with no
transport term; rewriting the type directly would produce the ill-typed motive described at
`twoChartCoboundary_of_pairRelation`. -/
noncomputable def mixedValue {s t : Bool} (hs : s = false) (ht : t = true)
    (w : Γ(X, V s ⊓ V t)ˣ) : Γ(X, V false ⊓ V true)ˣ := by
  subst hs
  subst ht
  exact w

@[simp]
theorem mixedValue_rfl (w : Γ(X, V false ⊓ V true)ˣ) :
    mixedValue (V := V) rfl rfl w = w :=
  rfl

/-- **The candidate overlap unit of a two-chart cocycle**: its value at a pair of points
lying in the two different charts. For a cocycle already in normal form this recovers the unit
it was built from (`twoChartCandidate_twoChartCocycle`); in general it is the `u` that the
`(iii-c1)` normalization must show `γ` is cohomologous to. -/
noncomputable def twoChartCandidate (sel : X → Bool) (hmem : ∀ x, x ∈ V (sel x))
    (γ : X.unitsCocycle (twoChartCover V sel hmem))
    {x₀ x₁ : X} (h₀ : sel x₀ = false) (h₁ : sel x₁ = true) : Γ(X, V false ⊓ V true)ˣ :=
  mixedValue h₀ h₁ (Scheme.unitsEvInf γ x₀ x₁)

/-- **The candidate is a left inverse on normalized cocycles**: extracting the overlap unit of
`twoChartCocycle u` returns `u`. So the normalization of `(iii-c1)`, once proved, will be a
genuine inverse rather than merely a surjection — and this lemma is what pins which `u` the
normalization must produce. -/
theorem twoChartCandidate_twoChartCocycle (sel : X → Bool) (hmem : ∀ x, x ∈ V (sel x))
    (u : Γ(X, V false ⊓ V true)ˣ) {x₀ x₁ : X} (h₀ : sel x₀ = false) (h₁ : sel x₁ = true) :
    twoChartCandidate sel hmem (twoChartCocycle u sel hmem) h₀ h₁ = u := by
  rw [twoChartCandidate, twoChartCocycle_unitsEvInf]
  revert h₀ h₁
  generalize sel x₀ = s
  generalize sel x₁ = t
  intro h₀ h₁
  subst h₀
  subst h₁
  rfl

/-! ## (iii-a) packaged: the comparison on the two-chart Čech quotient -/

/-- **(iii-a): the two-chart Čech `Ȟ¹` of units maps to the Picard group.** The comparison
homomorphism

```
Γ(X, V₀ ⊓ V₁)ˣ ⧸ (im Γ(V₀)ˣ · im Γ(V₁)ˣ)  →*  X.CechPic
```

descended from `twoChartClassHom` along `twoChartClassHom_eq_one_iff`. The source is exactly
the carrier the truncated-exponential engine of `Tangent/TruncExpCech.lean` computes, so this
is the arrow joining the (landed) T2 engine to the definitional Picard group. -/
noncomputable def twoChartClass (V : Bool → X.Opens) (sel : X → Bool)
    (hmem : ∀ x, x ∈ V (sel x)) (hsel : Function.Surjective sel) :
    (Γ(X, V false ⊓ V true)ˣ ⧸ TruncExpCech.cechCoboundaryUnits
        (X.resHom (inf_le_left : V false ⊓ V true ≤ V false))
        (X.resHom (inf_le_right : V false ⊓ V true ≤ V true))) →* X.CechPic :=
  QuotientGroup.lift _ (twoChartClassHom V sel hmem) fun u hu =>
    (twoChartClassHom_eq_one_iff V sel hmem hsel u).mpr hu

@[simp]
theorem twoChartClass_mk (V : Bool → X.Opens) (sel : X → Bool)
    (hmem : ∀ x, x ∈ V (sel x)) (hsel : Function.Surjective sel)
    (u : Γ(X, V false ⊓ V true)ˣ) :
    twoChartClass V sel hmem hsel (QuotientGroup.mk u) = twoChartClassHom V sel hmem u :=
  rfl

/-- **(iii-b): the comparison is injective** — `Ȟ¹(V₀,V₁ ; 𝒪ˣ) ↪ Pic(X)`.

Both halves come from `twoChartClassHom_eq_one_iff`: a quotient class dies in `X.CechPic`
exactly when its representative is a coboundary, i.e. when it was already trivial. The
mathematical content is the landed refinement injectivity, which is what makes the `→`
half of that iff true. -/
theorem twoChartClass_injective (V : Bool → X.Opens) (sel : X → Bool)
    (hmem : ∀ x, x ∈ V (sel x)) (hsel : Function.Surjective sel) :
    Function.Injective (twoChartClass V sel hmem hsel) := by
  refine (injective_iff_map_eq_one' _).mpr fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H u =>
    rw [twoChartClass_mk, twoChartClassHom_eq_one_iff V sel hmem hsel u,
      QuotientGroup.eq_one_iff]

end Scheme

end AlgebraicGeometry
