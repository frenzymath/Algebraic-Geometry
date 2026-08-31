/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafPair
import AlgebraicJacobian.Cohomology.RigidEngine4Relative

/-!
# The pinned cocycle datum on the relative curve (DAT-1, stage 1d-i, the datum)

The **cocycle datum over a `k`-algebra `B`** of the Wave-4 datum worksheet §3.2
(BINDING; `informal/spec-dat-1.md` §0), on the pinned relative cover
`relCover C B (fiberTwoCover π)` of the relative curve `C_B`:

* `AlgebraicGeometry.BasicOpenCoverData` — the two finite index types `J₀, J₁`, the
  basic-open generators `h_j ∈ Γ(Vᵢᴮ, 𝒪)` and the partition witnesses
  `∑ j, a_j · h_j = 1` per pinned chart; `pieces` sends `J₀ ⊕ J₁` to the basic opens
  `D(h_j)`.
* `AlgebraicGeometry.BasicOpenCocycleDatum` — the cover data together with the
  transition units on the pairwise basic-open overlaps (`Units` bundle the inverse
  witnesses) and the cocycle law `Scheme.IsGluingCocycle`.
* `BasicOpenCocycleDatum.sheaf` — the glued sheaf of `B`-modules of the datum
  (`gluedSheaf`), with the quasi-coherence packagings on **both pinned charts** and on
  the **overlap** as instances (`instQcohOn₀/₁/Inf`, from `gluedQcohOn`: side-`i`'s own
  family on chart `i`; side-0's family restricted along `V₀ᴮ ⊓ V₁ᴮ ≤ V₀ᴮ` on the
  overlap, through the subordinate-pieces interface).
* `BasicOpenCocycleDatum.pairData` — the two-cover pair data at the pinned relative
  coordinates `t₀ᴮ, t₁ᴮ` (`relFiberCoord₀/₁`), through `gluedPairData` (the
  componentwise-action hypotheses are `rfl` for the keyed instances).

The engine keystones fired on `pairData.pair` are in
`AlgebraicJacobian.Cohomology.GluedSheafEngine`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (B : Type u) [CommRing B] [Algebra k B]
variable (π : C.left ⟶ P1 k)

/-- **The basic-open cover data over `B`** (worksheet §3.2, first half): finite index
types `J₀, J₁`, for `j ∈ Jᵢ` a section `h_j` of the pinned chart `Vᵢᴮ` with partition
witnesses `∑ j, a_j · h_j = 1` in `Γ(Vᵢᴮ, 𝒪)` — so the basic opens `D(h_j)` cover the
chart (`le_iSup_basicOpen_of_sum_eq_one`). -/
structure BasicOpenCoverData [IsAffineHom π] : Type (u + 1) where
  /-- The chart-0 index. -/
  J₀ : Type u
  /-- The chart-1 index. -/
  J₁ : Type u
  /-- The chart-0 index is finite. -/
  fintype₀ : Fintype J₀
  /-- The chart-1 index is finite. -/
  fintype₁ : Fintype J₁
  /-- The chart-0 basic-open generators. -/
  h₀ : J₀ → Γ(relCurve C B, (relCover C B (fiberTwoCover π)).V₀)
  /-- The chart-1 basic-open generators. -/
  h₁ : J₁ → Γ(relCurve C B, (relCover C B (fiberTwoCover π)).V₁)
  /-- The chart-0 partition coefficients. -/
  a₀ : J₀ → Γ(relCurve C B, (relCover C B (fiberTwoCover π)).V₀)
  /-- The chart-1 partition coefficients. -/
  a₁ : J₁ → Γ(relCurve C B, (relCover C B (fiberTwoCover π)).V₁)
  /-- The chart-0 partition witness. -/
  partition₀ : ∑ j : J₀, a₀ j * h₀ j = 1
  /-- The chart-1 partition witness. -/
  partition₁ : ∑ j : J₁, a₁ j * h₁ j = 1

attribute [instance] BasicOpenCoverData.fintype₀ BasicOpenCoverData.fintype₁

namespace BasicOpenCoverData

variable {C B π} [IsAffineHom π] (D : BasicOpenCoverData C B π)

/-- The gluing index of the datum, `J = J₀ ⊕ J₁`. -/
abbrev index : Type u := D.J₀ ⊕ D.J₁

/-- The pieces of the datum: the basic opens `D(h_j)` of the two pinned charts. -/
noncomputable def pieces : D.index → (relCurve C B).Opens :=
  Sum.elim (fun j => (relCurve C B).basicOpen (D.h₀ j))
    (fun j => (relCurve C B).basicOpen (D.h₁ j))

@[simp]
lemma pieces_inl (j : D.J₀) :
    D.pieces (Sum.inl j) = (relCurve C B).basicOpen (D.h₀ j) := rfl

@[simp]
lemma pieces_inr (j : D.J₁) :
    D.pieces (Sum.inr j) = (relCurve C B).basicOpen (D.h₁ j) := rfl

/-- The chart-0 pieces cover the pinned chart `V₀ᴮ`. -/
lemma cover₀ : (relCover C B (fiberTwoCover π)).V₀ ≤
    ⨆ j : D.J₀, (relCurve C B).basicOpen (D.h₀ j) :=
  le_iSup_basicOpen_of_sum_eq_one D.a₀ D.h₀ D.partition₀

/-- The chart-1 pieces cover the pinned chart `V₁ᴮ`. -/
lemma cover₁ : (relCover C B (fiberTwoCover π)).V₁ ≤
    ⨆ j : D.J₁, (relCurve C B).basicOpen (D.h₁ j) :=
  le_iSup_basicOpen_of_sum_eq_one D.a₁ D.h₁ D.partition₁

/-- The chart-0 generators, restricted to the overlap of the pinned charts. -/
noncomputable def hInf (j : D.J₀) :
    Γ(relCurve C B,
      (relCover C B (fiberTwoCover π)).V₀ ⊓ (relCover C B (fiberTwoCover π)).V₁) :=
  (relCurve C B).resHom inf_le_left (D.h₀ j)

/-- The restricted chart-0 pieces are subordinate to the pieces of the datum. -/
lemma basicOpen_hInf_le (j : D.J₀) :
    (relCurve C B).basicOpen (D.hInf j) ≤ D.pieces (Sum.inl j) := by
  rw [hInf, Scheme.basicOpen_resHom, pieces_inl]
  exact inf_le_right

/-- The restricted chart-0 pieces cover the overlap of the pinned charts (the
partition witness restricts to a partition witness). -/
lemma coverInf : (relCover C B (fiberTwoCover π)).V₀ ⊓ (relCover C B (fiberTwoCover π)).V₁
    ≤ ⨆ j : D.J₀, (relCurve C B).basicOpen (D.hInf j) := by
  refine le_iSup_basicOpen_of_sum_eq_one
    (fun j => (relCurve C B).resHom inf_le_left (D.a₀ j)) D.hInf ?_
  have hres := congrArg
    ((relCurve C B).resHom (inf_le_left : (relCover C B (fiberTwoCover π)).V₀ ⊓
      (relCover C B (fiberTwoCover π)).V₁ ≤ (relCover C B (fiberTwoCover π)).V₀))
    D.partition₀
  rw [map_sum, map_one] at hres
  rw [← hres]
  exact Finset.sum_congr rfl fun j _ => (map_mul _ _ _).symm

end BasicOpenCoverData

/-- **The pinned cocycle datum over `B`** (worksheet §3.2, VERBATIM): the basic-open
cover data of the two pinned charts together with transition units on the pairwise
basic-open overlaps (with explicit inverse witnesses — `Units`) satisfying the cocycle
identities in the overlap section rings (`Scheme.IsGluingCocycle`, including the
normalization `g j j = 1`). This is the DAT-1 constructor input and the object RE-5
descends. -/
structure BasicOpenCocycleDatum [IsAffineHom π] : Type (u + 1) extends
    BasicOpenCoverData C B π where
  /-- The transition units on the pairwise piece overlaps. -/
  unit : ∀ i j : toBasicOpenCoverData.index,
    Γ(relCurve C B, toBasicOpenCoverData.pieces i ⊓ toBasicOpenCoverData.pieces j)ˣ
  /-- The cocycle law. -/
  isGluingCocycle : Scheme.IsGluingCocycle toBasicOpenCoverData.pieces unit

namespace BasicOpenCocycleDatum

variable {C B π} [IsAffineHom π] (D : BasicOpenCocycleDatum C B π)

/-- **The glued sheaf of the datum**: the m-chart cocycle-glued sheaf of `B`-modules on
the small Zariski site of the relative curve `C_B`. -/
@[reducible] noncomputable def sheaf :
    Sheaf (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
      (ModuleCat.{u} B) :=
  gluedSheaf B D.pieces D.unit

/-- The quasi-coherence packaging of the datum's glued sheaf on the pinned chart
`V₀ᴮ`, from the chart-0 family. -/
noncomputable instance instQcohOn₀ :
    Scheme.QcohOn D.sheaf (relCover C B (fiberTwoCover π)).V₀ :=
  gluedQcohOn B D.pieces D.unit D.isGluingCocycle (σ := Sum.inl) (h := D.h₀)
    (fun _ => le_rfl) D.cover₀

/-- The quasi-coherence packaging on the pinned chart `V₁ᴮ`, from the chart-1
family. -/
noncomputable instance instQcohOn₁ :
    Scheme.QcohOn D.sheaf (relCover C B (fiberTwoCover π)).V₁ :=
  gluedQcohOn B D.pieces D.unit D.isGluingCocycle (σ := Sum.inr) (h := D.h₁)
    (fun _ => le_rfl) D.cover₁

/-- The quasi-coherence packaging on the overlap of the pinned charts, from the
restricted chart-0 family (the subordinate-pieces interface). -/
noncomputable instance instQcohOnInf :
    Scheme.QcohOn D.sheaf
      ((relCover C B (fiberTwoCover π)).V₀ ⊓ (relCover C B (fiberTwoCover π)).V₁) :=
  gluedQcohOn B D.pieces D.unit D.isGluingCocycle
    (σ := fun j : D.J₀ => Sum.inl j) (h := D.hInf)
    (fun j => D.basicOpen_hInf_le j) D.coverInf

/-- **The two-cover pair data of the datum's glued sheaf** at the pinned relative chart
coordinates `t₀ᴮ, t₁ᴮ`: overlap-as-basic-open from the landed
`relCover_fiberTwoCover_inf_eq_basicOpen₀/₁`, mutual inverse from the pulled-back
`P1.chartCoord` relation `relFiberCoord_mul`. Its `pair` is the two-lattice pair of the
datum's sheaf that the rigid engine consumes. -/
noncomputable def pairData :
    Scheme.TwoCoverPairData D.sheaf (relCover C B (fiberTwoCover π)).V₀
      (relCover C B (fiberTwoCover π)).V₁ :=
  gluedPairData B D.pieces D.unit
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (relFiberCoord₀ C B π) (relFiberCoord₁ C B π)
    (relCover_fiberTwoCover_inf_eq_basicOpen₀ C B π)
    (relCover_fiberTwoCover_inf_eq_basicOpen₁ C B π)
    (relFiberCoord_mul C B π)

end BasicOpenCocycleDatum

end AlgebraicGeometry
