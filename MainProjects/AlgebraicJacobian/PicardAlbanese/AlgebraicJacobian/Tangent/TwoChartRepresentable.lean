/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.TwoChartNormalize
import AlgebraicJacobian.Picard.EffectivityTrivialization

/-!
# (iii-c2-Zar): chart-trivial classes are representable on the two-chart cover (W5-T4)

The **Zariski half** of clause `(iii-c2)` (`informal/w5-t4-worksheet.md` §6.9). For a scheme
`X` with two opens `V : Bool → X.Opens` covering it:

> `Scheme.twoChartClassHom_surjOn_of_chartTrivial` —
> if `L : X.CechPic` restricts trivially to each chart (`CechPic.map (V s).ι L = 1`), then
> `L = twoChartClassHom V sel hmem u` for an overlap unit `u : Γ(X, V₀ ⊓ V₁)ˣ`.

Composed with the landed `(iii-c1)` normalization this is the whole cohomological content of
`(iii-c2)`: **no `IsAffine`, no dual numbers, no curve hypothesis.** Everything geometric in
the T4 lane is thereby confined to the single remaining clause `(iii-c2-aff)`, "an `ε`-kernel
class is trivial on each *thickened* chart", for which `Picard/EffectivityMoving.lean` is the
correct tool (see the retraction in §6.9 — that file bridges *into* chart triviality, so it
belongs to `(iii-c2-aff)`, not here).

## The argument

Write `L = mk 𝒩 γ.class`.

1. **Per-chart cochains.** `CechPic.map (V s).ι L = 1` feeds the landed
   `exists_trimmed_trivializing_of_cechPicMap_ι_eq_one` — which carries **no affineness
   hypothesis** — giving units `t s b : Γ(X, 𝒩.opens b ⊓ V s)ˣ` with
   `t s b · γ(b,b') = t s b'` on trimmed pairwise overlaps.
2. **The overlap unit.** On `𝒩.opens b ⊓ V₀ ⊓ V₁` the ratio `t false b · (t true b)⁻¹` is
   **independent of `b`**: the two instances of step 1 contribute the same factor `γ(b,b')`,
   which cancels because units of a commutative ring of sections commute. These opens cover
   `V₀ ⊓ V₁`, so `exists_unitsRestrict_eq` glues them to `u : Γ(X, V₀ ⊓ V₁)ˣ`.
3. **The comparison.** On the refinement `𝒩 ⊓ twoChartCover V sel hmem`, whose member at `b`
   is `𝒩.opens b ⊓ V (sel b)`, the `0`-cochain `b ↦ t (sel b) b` conjugates `γ` into
   `twoChartCocycle u`. Note `t (sel b) b` typechecks at that member **on the nose**: the
   `Bool` index is instantiated, never transported — the §6.8 lesson once more.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite CategoryTheory.PresheafOfGroups TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}} {V : Bool → X.Opens}

/-! ## Step 1–2: the glued overlap unit -/

/-- **The trivializing relation of a chart cochain**, as a standalone predicate: `t` trivializes
the cocycle `γ` on the `W`-trimmings of the members of `𝒩`. This is exactly the conclusion of
the landed `exists_trimmed_trivializing_of_cechPicMap_ι_eq_one`, named so that the two chart
instances can be handled uniformly. -/
def IsTrimmedTrivializing {𝒩 : X.PointedCover} (γ : X.unitsCocycle 𝒩) (W : X.Opens)
    (t : ∀ b : X, Γ(X, 𝒩.opens b ⊓ W)ˣ) : Prop :=
  ∀ b b' : X,
    X.unitsRestrict (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        (𝒩.opens b ⊓ 𝒩.opens b') ⊓ W ≤ 𝒩.opens b ⊓ W) (t b)
      * X.unitsRestrict (inf_le_left :
          (𝒩.opens b ⊓ 𝒩.opens b') ⊓ W ≤ 𝒩.opens b ⊓ 𝒩.opens b')
          (Scheme.unitsEvInf γ b b')
    = X.unitsRestrict (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (t b')

/-- The landed trimmed-trivialization theorem, restated through `IsTrimmedTrivializing`. No
affineness hypothesis: this is Zariski sheaf theory on the open subscheme `W`. -/
theorem exists_isTrimmedTrivializing {𝒩 : X.PointedCover} (γ : X.unitsCocycle 𝒩)
    (W : X.Opens) (h : Scheme.CechPic.map W.ι (Scheme.CechPic.mk 𝒩 γ.class) = 1) :
    ∃ t : ∀ b : X, Γ(X, 𝒩.opens b ⊓ W)ˣ, IsTrimmedTrivializing γ W t :=
  Scheme.exists_trimmed_trivializing_of_cechPicMap_ι_eq_one 𝒩 γ W h

/-- **The `b`-independence of the chart-cochain ratio.** If `t₀`, `t₁` trivialize `γ` on the
`V false`- and `V true`-trimmings, then the ratios `t₀ b · (t₁ b)⁻¹` at two points agree on
their common overlap: both instances of the trivializing relation contribute the *same*
factor `γ(b,b')`, and units of a commutative section ring commute, so it cancels. -/
theorem ratio_agree {𝒩 : X.PointedCover} (γ : X.unitsCocycle 𝒩)
    {t₀ : ∀ b : X, Γ(X, 𝒩.opens b ⊓ V false)ˣ}
    {t₁ : ∀ b : X, Γ(X, 𝒩.opens b ⊓ V true)ˣ}
    (h₀ : IsTrimmedTrivializing γ (V false) t₀)
    (h₁ : IsTrimmedTrivializing γ (V true) t₁) (b b' : X) :
    X.unitsRestrict (le_inf (inf_le_left.trans inf_le_left)
          (inf_le_right.trans inf_le_left) :
        ((𝒩.opens b ⊓ 𝒩.opens b') ⊓ (V false ⊓ V true)) ≤ 𝒩.opens b ⊓ V false) (t₀ b)
        * (X.unitsRestrict (le_inf (inf_le_left.trans inf_le_left)
            (inf_le_right.trans inf_le_right)) (t₁ b))⁻¹
      = X.unitsRestrict (le_inf (inf_le_left.trans inf_le_right)
            (inf_le_right.trans inf_le_left)) (t₀ b')
        * (X.unitsRestrict (le_inf (inf_le_left.trans inf_le_right)
            (inf_le_right.trans inf_le_right)) (t₁ b'))⁻¹ := by
  set O : X.Opens := (𝒩.opens b ⊓ 𝒩.opens b') ⊓ (V false ⊓ V true) with hO
  have hnn : O ≤ 𝒩.opens b ⊓ 𝒩.opens b' := inf_le_left
  -- both trivializing relations, restricted to `O`
  have e₀ := congrArg (X.unitsRestrict (le_inf hnn (inf_le_right.trans inf_le_left) :
    O ≤ (𝒩.opens b ⊓ 𝒩.opens b') ⊓ V false)) (h₀ b b')
  have e₁ := congrArg (X.unitsRestrict (le_inf hnn (inf_le_right.trans inf_le_right) :
    O ≤ (𝒩.opens b ⊓ 𝒩.opens b') ⊓ V true)) (h₁ b b')
  simp only [map_mul, unitsRestrict_unitsRestrict] at e₀ e₁
  -- `t₀ b · g = t₀ b'` and `t₁ b · g = t₁ b'` with the SAME `g`, so the ratios agree:
  -- `(t₀ b')⁻¹ · t₁ b' = (t₀ b · g)⁻¹ · (t₁ b · g)` and `g` cancels by commutativity
  rw [← e₀, ← e₁, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]

/-- **The glued overlap unit.** The `b`-independent ratios of `ratio_agree` live on the opens
`𝒩.opens b ⊓ (V₀ ⊓ V₁)`, which cover `V₀ ⊓ V₁` because `𝒩` is a pointed cover; so they glue to
a single unit on the overlap. -/
theorem exists_overlapUnit {𝒩 : X.PointedCover} (γ : X.unitsCocycle 𝒩)
    {t₀ : ∀ b : X, Γ(X, 𝒩.opens b ⊓ V false)ˣ}
    {t₁ : ∀ b : X, Γ(X, 𝒩.opens b ⊓ V true)ˣ}
    (h₀ : IsTrimmedTrivializing γ (V false) t₀)
    (h₁ : IsTrimmedTrivializing γ (V true) t₁) :
    ∃ u : Γ(X, V false ⊓ V true)ˣ, ∀ b : X,
      X.unitsRestrict (inf_le_right : 𝒩.opens b ⊓ (V false ⊓ V true) ≤ V false ⊓ V true) u
        = X.unitsRestrict (le_inf inf_le_left (inf_le_right.trans inf_le_left)) (t₀ b)
          * (X.unitsRestrict (le_inf inf_le_left
              (inf_le_right.trans inf_le_right)) (t₁ b))⁻¹ := by
  refine exists_unitsRestrict_eq (V := V false ⊓ V true)
    (W := fun b : X => 𝒩.opens b ⊓ (V false ⊓ V true)) (fun b => inf_le_right)
    (fun w hw => Opens.mem_iSup.mpr ⟨w, 𝒩.mem_opens w, hw⟩) _ (fun b b' => ?_)
  have h := ratio_agree γ h₀ h₁ b b'
  have hle : (𝒩.opens b ⊓ (V false ⊓ V true)) ⊓ (𝒩.opens b' ⊓ (V false ⊓ V true))
      ≤ (𝒩.opens b ⊓ 𝒩.opens b') ⊓ (V false ⊓ V true) :=
    fun w hw => ⟨⟨hw.1.1, hw.2.1⟩, hw.1.2⟩
  have key := congrArg (X.unitsRestrict hle) h
  simp only [map_mul, map_inv, unitsRestrict_unitsRestrict] at key ⊢
  exact key

/-! ## Step 3: the comparison on the common refinement -/

/-- **The chart cochain, selected pointwise.** At `b` this is `t (sel b) b`, a unit on
`𝒩.opens b ⊓ V (sel b)` — which **is** the member of the refinement `𝒩 ⊓ twoChartCover` at `b`,
definitionally (`PointedCover.inf_opens`, `twoChartCover_opens`). The `Bool` index is
*instantiated*, never transported: the §6.8 lesson once more. -/
noncomputable def selCochain (sel : X → Bool) (hmem : ∀ x, x ∈ V (sel x))
    {𝒩 : X.PointedCover} (t : ∀ (s : Bool) (b : X), Γ(X, 𝒩.opens b ⊓ V s)ˣ) (b : X) :
    Γ(X, (𝒩 ⊓ twoChartCover V sel hmem).opens b)ˣ :=
  (t (sel b) b)⁻¹

/-- The two chart cochains, packaged as one `Bool`-indexed family so that `selCochain` can
select without a transport. -/
noncomputable def pairCochain {𝒩 : X.PointedCover}
    (t₀ : ∀ b : X, Γ(X, 𝒩.opens b ⊓ V false)ˣ)
    (t₁ : ∀ b : X, Γ(X, 𝒩.opens b ⊓ V true)ˣ) :
    ∀ (s : Bool) (b : X), Γ(X, 𝒩.opens b ⊓ V s)ˣ
  | false => t₀
  | true  => t₁

/-- Both components of `pairCochain` trivialize, uniformly in the `Bool` index. Proved by
`cases` on the index, where each branch is one of the two hypotheses **by definition** — the
index is the match scrutinee, so nothing is transported. -/
theorem isTrimmedTrivializing_pairCochain {𝒩 : X.PointedCover} (γ : X.unitsCocycle 𝒩)
    {t₀ : ∀ b : X, Γ(X, 𝒩.opens b ⊓ V false)ˣ}
    {t₁ : ∀ b : X, Γ(X, 𝒩.opens b ⊓ V true)ˣ}
    (h₀ : IsTrimmedTrivializing γ (V false) t₀)
    (h₁ : IsTrimmedTrivializing γ (V true) t₁) (s : Bool) :
    IsTrimmedTrivializing γ (V s) (pairCochain t₀ t₁ s) := by
  cases s
  · exact h₀
  · exact h₁

/-- **The pair-unit relation at a single point** — the genuine four-case core of (iii-c2-Zar).
On an open below `𝒩.opens b ⊓ V s ⊓ V r`, the glued overlap unit's `(s,r)` pair value conjugates
`t s b` into `t r b`.

Diagonal cases: `twoChartPairUnit` is `1` and both sides are `t s b`. Mixed cases: exactly the
glue property `hu` of `u` at the point `b`, forwards at `(false, true)` and inverted at
`(true, false)`. The chart indices are *variables*, so the pair values are compared without any
transport (the §6.8 lesson). -/
theorem pairCochain_pairUnit_at {𝒩 : X.PointedCover}
    {t : ∀ (s : Bool) (b : X), Γ(X, 𝒩.opens b ⊓ V s)ˣ}
    {u : Γ(X, V false ⊓ V true)ˣ}
    (hu : ∀ b : X,
      X.unitsRestrict (inf_le_right : 𝒩.opens b ⊓ (V false ⊓ V true) ≤ V false ⊓ V true) u
        = X.unitsRestrict (le_inf inf_le_left (inf_le_right.trans inf_le_left)) (t false b)
          * (X.unitsRestrict (le_inf inf_le_left
              (inf_le_right.trans inf_le_right)) (t true b))⁻¹)
    (s r : Bool) (b : X) {O : X.Opens} (hs : O ≤ V s ⊓ V r) (hbs : O ≤ 𝒩.opens b ⊓ V s)
    (hbr : O ≤ 𝒩.opens b ⊓ V r) :
    X.unitsRestrict hs (twoChartPairUnit u s r) * X.unitsRestrict hbr (t r b)
      = X.unitsRestrict hbs (t s b) := by
  cases s <;> cases r
  · -- (false, false): the pair unit is `1`
    simp only [twoChartPairUnit, map_one, one_mul]
  · -- (false, true): the glue property at `b`
    have hO : O ≤ 𝒩.opens b ⊓ (V false ⊓ V true) := fun w hw => ⟨(hbs hw).1, hs hw⟩
    have h := congrArg (X.unitsRestrict hO) (hu b)
    simp only [unitsRestrict_unitsRestrict, map_mul, map_inv] at h
    have hpair : X.unitsRestrict hs (twoChartPairUnit u false true)
        = X.unitsRestrict hbs (t false b) * (X.unitsRestrict hbr (t true b))⁻¹ := h
    rw [hpair]
    group
  · -- (true, false): the same, inverted
    have hO : O ≤ 𝒩.opens b ⊓ (V false ⊓ V true) := fun w hw => ⟨(hbs hw).1, (hs hw).symm⟩
    have h := congrArg (X.unitsRestrict hO) (hu b)
    simp only [unitsRestrict_unitsRestrict, map_mul, map_inv] at h
    have hpair : X.unitsRestrict hs (twoChartPairUnit u true false)
        = (X.unitsRestrict hbr (t false b))⁻¹ * X.unitsRestrict hbs (t true b) := by
      have e : X.unitsRestrict hs (twoChartPairUnit u true false)
          = (X.unitsRestrict (fun w hw => (hs hw).symm : O ≤ V false ⊓ V true) u)⁻¹ := by
        change X.unitsRestrict hs (X.unitsRestrict (le_of_eq (inf_comm _ _)) u⁻¹) = _
        rw [unitsRestrict_unitsRestrict, map_inv]
      rw [e, show X.unitsRestrict (fun w hw => (hs hw).symm : O ≤ V false ⊓ V true) u
          = X.unitsRestrict hbr (t false b) * (X.unitsRestrict hbs (t true b))⁻¹ from h,
        mul_inv, inv_inv, mul_comm]
    rw [hpair, mul_comm _ (X.unitsRestrict hbr (t false b)), mul_inv_cancel_left]
  · -- (true, true): the pair unit is `1`
    simp only [twoChartPairUnit, map_one, one_mul]

/-- **The conjugation identity at abstract chart indices** — the four-case heart of
(iii-c2-Zar), stated with `s`, `t` as *variables* so that instantiating at `sel b`, `sel b'`
needs no transport (the refinement member `(𝒩 ⊓ twoChartCover).opens b` is
`𝒩.opens b ⊓ V (sel b)` by `rfl`).

The four cases: on the diagonal `s = t` the pair unit is `1` and the identity is the
trivializing relation with its `γ(b,b')` factor cancelling against itself; at the mixed pairs
it is the glue property of `u` at the point `b`, read forwards and backwards. -/
theorem pairCochain_conj {𝒩 : X.PointedCover} (γ : X.unitsCocycle 𝒩)
    {t : ∀ (s : Bool) (b : X), Γ(X, 𝒩.opens b ⊓ V s)ˣ}
    (ht : ∀ s, IsTrimmedTrivializing γ (V s) (t s))
    {u : Γ(X, V false ⊓ V true)ˣ}
    (hu : ∀ b : X,
      X.unitsRestrict (inf_le_right : 𝒩.opens b ⊓ (V false ⊓ V true) ≤ V false ⊓ V true) u
        = X.unitsRestrict (le_inf inf_le_left (inf_le_right.trans inf_le_left)) (t false b)
          * (X.unitsRestrict (le_inf inf_le_left
              (inf_le_right.trans inf_le_right)) (t true b))⁻¹)
    (s r : Bool) (b b' : X)
    (hO : (𝒩.opens b ⊓ V s) ⊓ (𝒩.opens b' ⊓ V r) ≤ 𝒩.opens b ⊓ 𝒩.opens b')
    (hs : (𝒩.opens b ⊓ V s) ⊓ (𝒩.opens b' ⊓ V r) ≤ V s ⊓ V r) :
    X.unitsRestrict (inf_le_left) (t s b) * X.unitsRestrict hO (Scheme.unitsEvInf γ b b')
      = X.unitsRestrict hs (twoChartPairUnit u s r)
        * X.unitsRestrict (inf_le_right) (t r b') := by
  set O : X.Opens := (𝒩.opens b ⊓ V s) ⊓ (𝒩.opens b' ⊓ V r) with hOdef
  have hbs : O ≤ 𝒩.opens b ⊓ V s := inf_le_left
  have hbr : O ≤ 𝒩.opens b ⊓ V r := fun w hw => ⟨hw.1.1, (hs hw).2⟩
  -- the trivializing relation for the index `r` at `(b, b')`, restricted to `O`
  have er : X.unitsRestrict hbr (t r b)
        * X.unitsRestrict hO (Scheme.unitsEvInf γ b b')
      = X.unitsRestrict (inf_le_right : O ≤ 𝒩.opens b' ⊓ V r) (t r b') := by
    have h := congrArg (X.unitsRestrict (le_inf hO (hs.trans inf_le_right) :
      O ≤ (𝒩.opens b ⊓ 𝒩.opens b') ⊓ V r)) (ht r b b')
    simp only [map_mul, unitsRestrict_unitsRestrict] at h
    exact h
  -- and the pair-unit relation at the single point `b`
  have hpt := pairCochain_pairUnit_at hu s r b hs hbs hbr
  rw [← er, ← hpt, mul_assoc]

/-- **The conjugation identity in the orientation `unitsCocycle_isCohomologous` consumes.**
`Scheme.unitsCocycle_isCohomologous` wants `α b · γ₁(b,b') = γ₂(b,b') · α b'` with `γ₁` the
*normalized* cocycle; with `u = t₀ · t₁⁻¹` the conjugating cochain is therefore `t⁻¹`, not `t`.
Derived from `pairCochain_conj` by moving both `t`-factors across. -/
theorem pairCochain_conj_inv {𝒩 : X.PointedCover} (γ : X.unitsCocycle 𝒩)
    {t : ∀ (s : Bool) (b : X), Γ(X, 𝒩.opens b ⊓ V s)ˣ}
    (ht : ∀ s, IsTrimmedTrivializing γ (V s) (t s))
    {u : Γ(X, V false ⊓ V true)ˣ}
    (hu : ∀ b : X,
      X.unitsRestrict (inf_le_right : 𝒩.opens b ⊓ (V false ⊓ V true) ≤ V false ⊓ V true) u
        = X.unitsRestrict (le_inf inf_le_left (inf_le_right.trans inf_le_left)) (t false b)
          * (X.unitsRestrict (le_inf inf_le_left
              (inf_le_right.trans inf_le_right)) (t true b))⁻¹)
    (s r : Bool) (b b' : X)
    (hO : (𝒩.opens b ⊓ V s) ⊓ (𝒩.opens b' ⊓ V r) ≤ 𝒩.opens b ⊓ 𝒩.opens b')
    (hs : (𝒩.opens b ⊓ V s) ⊓ (𝒩.opens b' ⊓ V r) ≤ V s ⊓ V r) :
    X.unitsRestrict (inf_le_left) (t s b)⁻¹ * X.unitsRestrict hs (twoChartPairUnit u s r)
      = X.unitsRestrict hO (Scheme.unitsEvInf γ b b')
        * X.unitsRestrict (inf_le_right) (t r b')⁻¹ := by
  set O : X.Opens := (𝒩.opens b ⊓ V s) ⊓ (𝒩.opens b' ⊓ V r) with hOdef
  have hbs : O ≤ 𝒩.opens b ⊓ V s := inf_le_left
  have hbr : O ≤ 𝒩.opens b ⊓ V r := fun w hw => ⟨hw.1.1, (hs hw).2⟩
  have er : X.unitsRestrict hbr (t r b)
        * X.unitsRestrict hO (Scheme.unitsEvInf γ b b')
      = X.unitsRestrict (inf_le_right : O ≤ 𝒩.opens b' ⊓ V r) (t r b') := by
    have e := congrArg (X.unitsRestrict (le_inf hO (hs.trans inf_le_right) :
      O ≤ (𝒩.opens b ⊓ 𝒩.opens b') ⊓ V r)) (ht r b b')
    simp only [map_mul, unitsRestrict_unitsRestrict] at e
    exact e
  have hpt := pairCochain_pairUnit_at hu s r b hs hbs hbr
  -- both sides equal `(t r b)⁻¹`
  rw [map_inv, map_inv]
  have hR : X.unitsRestrict hO (Scheme.unitsEvInf γ b b')
        * (X.unitsRestrict (inf_le_right : O ≤ 𝒩.opens b' ⊓ V r) (t r b'))⁻¹
      = (X.unitsRestrict hbr (t r b))⁻¹ := by
    rw [← er, mul_inv, mul_comm (X.unitsRestrict hbr (t r b))⁻¹, ← mul_assoc,
      mul_inv_cancel, one_mul]
  have hL : (X.unitsRestrict hbs (t s b))⁻¹ * X.unitsRestrict hs (twoChartPairUnit u s r)
      = (X.unitsRestrict hbr (t r b))⁻¹ := by
    rw [← hpt, mul_inv, mul_comm (X.unitsRestrict hs (twoChartPairUnit u s r))⁻¹,
      mul_assoc, inv_mul_cancel, mul_one]
  exact hL.trans hR.symm

/-- **(iii-c2-Zar).** A class trivial on each of the two charts is `twoChartClassHom` of an
overlap unit. All the cohomological content of clause (iii-c2), with **no** affineness, dual
numbers, or curve hypothesis.

The remaining clause (iii-c2-aff) — that an `ε`-kernel class *is* trivial on each thickened
chart — is where the geometry lives; see `informal/w5-t4-worksheet.md` §6.9. -/
theorem twoChartClassHom_surjOn_of_chartTrivial (sel : X → Bool) (hmem : ∀ x, x ∈ V (sel x))
    (L : X.CechPic) (hL : ∀ s : Bool, Scheme.CechPic.map (V s).ι L = 1) :
    ∃ u : Γ(X, V false ⊓ V true)ˣ, twoChartClassHom V sel hmem u = L := by
  induction L using Scheme.CechPic.ind with
  | mk 𝒩 a =>
    induction a using Quot.ind with
    | _ γ =>
      obtain ⟨t₀, h₀⟩ := exists_isTrimmedTrivializing γ (V false) (hL false)
      obtain ⟨t₁, h₁⟩ := exists_isTrimmedTrivializing γ (V true) (hL true)
      obtain ⟨u, hu⟩ := exists_overlapUnit γ h₀ h₁
      refine ⟨u, ?_⟩
      -- compare on the common refinement `𝒲 := 𝒩 ⊓ twoChartCover`
      rw [twoChartClassHom_apply]
      refine Scheme.CechPic.mk_eq_mk_iff.mpr
        ⟨𝒩 ⊓ twoChartCover V sel hmem, inf_le_right, inf_le_left, ?_⟩
      -- `unitsRes h γ.class = (γ.res …).class` holds by `rfl`, so the goal is an equality of
      -- `H¹` classes of restricted cocycles
      change OneCocycle.class _ = OneCocycle.class _
      refine (OneCocycle.class_eq_iff _ _).mpr (Scheme.unitsCocycle_isCohomologous
        (selCochain sel hmem (pairCochain t₀ t₁)) fun b b' => ?_)
      rw [Scheme.res_unitsEvInf, Scheme.res_unitsEvInf, twoChartCocycle_unitsEvInf]
      exact pairCochain_conj_inv γ (isTrimmedTrivializing_pairCochain γ h₀ h₁) hu
        (sel b) (sel b') b b' _ _

end Scheme

end AlgebraicGeometry
