/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeCertZarChartPair
import AlgebraicJacobian.Picard.DivSchemeCertZarVerdict

/-!
# Chart confinement: a divisor invariant, and an open condition on the base

`DivSchemeCertZarC1.lean` proves the negative half of the certificate lane's gate: a certified
adaptation of a connected divisor confines that divisor to one pinned chart of `π`
(`supportLocus_subset_chart_of_isCertified`).  This file supplies the two facts that turn that
no-go into a *decision* about the interface rather than an open question.

**1. The obstruction is about the divisor, not the presentation.**  `DivFamZar` is a `DivEq`
quotient, so a no-go stated about a local-equation system only bites the functor if it is
`DivEq`-invariant.  `DivEq.supportLocus_eq` proves it is: the unit locus is defined by germ
invertibility, and `DivEq` changes germs by units.  Hence
`not_isCertified_of_divEq_of_isPreconnected_of_witnesses`: no representative of the divisor
class admits a certified adaptation.  Re-spelling the equations cannot escape the obstruction.

**2. Confinement is an OPEN condition on the base.**  The support is closed and the relative
curve is proper over the test ring, so the set of base points whose support fibre lies in the
chart overlap `V₀ ⊓ V₁` is open (`isOpen_setOf_fibre_subset_chartInter`), and confinement at a
single fibre spreads to a Zariski neighbourhood
(`exists_opens_supportLocus_subset_chartInter`, the chart instance of the landed support tube).

Fact 2 is the licence the lane needs.  `IsLocallyCertified` — hence `DivFamZar` — is a
Zariski-local-on-the-base condition, and an *open* condition on the base may legitimately be
imposed by an atlas: the charts still cover.  So the repair of the interface is not "assume the
divisor avoids the vertical fibres" (a hypothesis on an arbitrary divisor, which
`informal/spec-dd-r.md` §Discipline (2) rightly forbids) but "the chart of the atlas records
which vertical fibres its divisors avoid" — legitimate exactly because the recorded condition
is open.  What Fact 2 does *not* supply, and what the repair still owes, is that these opens
COVER: with the two pinned charts fixed once and for all they provably do not
(`not_isCertified_of_isPreconnected_of_witnesses` applies to a connected divisor meeting both
vertical fibres over a base point, and no Zariski shrink separates the witnesses).

Finally `supportLocus_subset_of_forall_fibre` converts the global confinement hypothesis of
`forall_finite_colength_of_pieces_eq_chart` into the fibrewise one the seed geometry actually
produces, so the chart-shaped adaptation's clause (c1) can be discharged fibre by fibre.

## Main declarations

* `AlgebraicGeometry.Scheme.LocalEquations.DivEq.unitLocus_eq` /
  `DivEq.supportLocus_eq` — the unit locus and the support locus are divisor invariants.
* `AlgebraicGeometry.DivisorAdaptation.isClosed_supportLocus_inter_chart_of_isCertified` /
  `not_isCertified_of_not_isClosed_inter_chart₀` — the obstruction with NO connectivity
  hypothesis: a certificate forces both chart traces closed.
* `AlgebraicGeometry.DivisorAdaptation.not_isCertified_of_divEq_of_isPreconnected_of_witnesses`
  — the obstruction descends to the `DivEq` quotient the functor is built from.
* `AlgebraicGeometry.Scheme.LocalEquations.exists_opens_supportLocus_subset_chartInter` —
  fibrewise chart confinement spreads to a Zariski neighbourhood of the base point.
* `AlgebraicGeometry.Scheme.LocalEquations.isOpen_setOf_fibre_subset_chartInter` — the
  confinement locus of the base is open.
* `AlgebraicGeometry.Scheme.LocalEquations.supportLocus_subset_of_forall_fibre` — fibrewise
  confinement at every base point is global confinement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161); pin in-file. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace Scheme.LocalEquations

/-! ## The support locus is a divisor invariant -/

variable {X : Scheme.{u}}

/-- **The unit locus only depends on the divisor.**  Two `DivEq` systems have equations that
agree up to a unit on a common refinement, and the unit locus is a germ-invertibility locus, so
it cannot see the unit. -/
theorem DivEq.unitLocus_eq {d₁ d₂ : X.LocalEquations} (h : DivEq d₁ d₂) :
    (d₁.unitLocus : Set X) = (d₂.unitLocus : Set X) := by
  obtain ⟨𝒲, h₁, h₂, H⟩ := h
  ext y
  have hyW : y ∈ 𝒲.opens y := 𝒲.mem_opens y
  have hy₁ : y ∈ d₁.cover.opens y := h₁ y hyW
  have hy₂ : y ∈ d₂.cover.opens y := h₂ y hyW
  obtain ⟨u, hu⟩ := H y
  have key := congrArg (X.presheaf.germ (𝒲.opens y) y hyW).hom hu
  rw [map_mul] at key
  rw [show (X.presheaf.germ (𝒲.opens y) y hyW).hom
      ((X.presheaf.map (homOfLE (h₁ y)).op).hom (d₁.eqn y))
      = (X.presheaf.germ (d₁.cover.opens y) y hy₁).hom (d₁.eqn y) from
    TopCat.Presheaf.germ_res_apply _ _ _ _ _] at key
  rw [show (X.presheaf.germ (𝒲.opens y) y hyW).hom
      ((X.presheaf.map (homOfLE (h₂ y)).op).hom (d₂.eqn y))
      = (X.presheaf.germ (d₂.cover.opens y) y hy₂).hom (d₂.eqn y) from
    TopCat.Presheaf.germ_res_apply _ _ _ _ _] at key
  simp only [SetLike.mem_coe]
  rw [d₁.mem_unitLocus_iff_isUnit_germ hy₁, d₂.mem_unitLocus_iff_isUnit_germ hy₂, key,
    IsUnit.mul_iff]
  exact and_iff_right (u.isUnit.map _)

/-- **The support locus only depends on the divisor** — the complement of
`DivEq.unitLocus_eq`.  This is what makes every no-go about `supportLocus` a statement about
the `DivFam`/`DivFamZar` quotient and not merely about a chosen representative. -/
theorem DivEq.supportLocus_eq {d₁ d₂ : X.LocalEquations} (h : DivEq d₁ d₂) :
    d₁.supportLocus = d₂.supportLocus := by
  rw [supportLocus, supportLocus, h.unitLocus_eq]

/-! ## Fibrewise confinement, and its base-open spread -/

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

omit [IsProper C.hom] in
/-- **Fibrewise confinement at every base point is global confinement**: the fibres of the
structure morphism cover the relative curve.  This is the form in which the chart-shaped
adaptation's clause (c1) hypothesis
(`DivisorAdaptation.forall_finite_colength_of_pieces_eq_chart`) meets the fibrewise geometry
the seed actually produces. -/
theorem supportLocus_subset_of_forall_fibre (d : (relCurve C R).LocalEquations)
    (U : (relCurve C R).Opens)
    (h : ∀ s : Spec (.of R), ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s} ∩ d.supportLocus ⊆
      (U : Set (relCurve C R))) :
    d.supportLocus ⊆ (U : Set (relCurve C R)) :=
  fun _ hx => h _ ⟨rfl, hx⟩

/-- **Chart confinement spreads from one fibre to a Zariski neighbourhood of the base.**  The
chart instance of the landed support tube (`exists_supportTube`), at the chart overlap
`V₀ ⊓ V₁` — the open in which a chart-shaped adaptation swallows the divisor. -/
theorem exists_opens_supportLocus_subset_chartInter (d : (relCurve C R).LocalEquations)
    (s : Spec (.of R))
    (hfib : ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s} ∩ d.supportLocus ⊆
      (((relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁ :
        (relCurve C R).Opens) : Set (relCurve C R))) :
    ∃ V : (Spec (.of R)).Opens, s ∈ V ∧
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' (V : Set (Spec (.of R))) ∩ d.supportLocus ⊆
        (((relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁ :
          (relCurve C R).Opens) : Set (relCurve C R)) :=
  d.exists_supportTube ((relCurve C R) ↘ Spec (.of R)) (Opens.isOpen _) hfib

/-- **Chart confinement is an OPEN condition on the base.**  The base points over which the
divisor is confined to the chart overlap form an open subset of `Spec R`.

This is the licence for an atlas to record chart avoidance: an open condition may be imposed
chart-wise without losing points, whereas a closed or arbitrary one may not.  It does not by
itself say the resulting opens cover — with the two pinned charts fixed they provably do not,
by `DivisorAdaptation.not_isCertified_of_isPreconnected_of_witnesses`. -/
theorem isOpen_setOf_fibre_subset_chartInter (d : (relCurve C R).LocalEquations) :
    IsOpen {s : Spec (.of R) |
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s} ∩ d.supportLocus ⊆
        (((relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁ :
          (relCurve C R).Opens) : Set (relCurve C R))} := by
  rw [isOpen_iff_forall_mem_open]
  intro s hs
  obtain ⟨V, hsV, hV⟩ := exists_opens_supportLocus_subset_chartInter d s hs
  refine ⟨(V : Set (Spec (.of R))), ?_, V.isOpen, hsV⟩
  intro s' hs' x hx
  refine hV ⟨?_, hx.2⟩
  have hxs : ((relCurve C R) ↘ Spec (.of R)).base x = s' := hx.1
  rw [Set.mem_preimage, hxs]
  exact hs'

end Scheme.LocalEquations

/-! ## The obstruction descends to the divisor class -/

namespace DivisorAdaptation

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

/-- **The chart obstruction in its strongest form: no connectivity hypothesis at all.**  A
certified adaptation forces BOTH pinned-chart traces of the support to be closed in the relative
curve — a statement in which neither the adaptation nor its pieces nor any connectivity
assumption appears.

This is the honest shape of the design failure.  `supportLocus_subset_chart_of_isCertified`
derives the chart *containment* from it, but needs the support preconnected; the closedness
itself does not, and already refutes certifiability for any divisor whose chart trace is dense
and not closed — for instance the degree-two divisor `V(t·x² + x·y + t·y²)` over `k[t]`, whose
fibre at `t = 0` is `{0, ∞}` (the model recorded at
`DivSchemeCertZarConn.not_forall_supportLeak_eq_empty_of_isPreconnected`), where
`supportLocus ∩ V₀` is the irreducible support minus one point. -/
theorem isClosed_supportLocus_inter_chart_of_isCertified {n : ℕ}
    {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R π d) (hc : A.IsCertified n) :
    IsClosed (d.supportLocus ∩ ((relCover C R (fiberTwoCover π)).V₀ : Set (relCurve C R))) ∧
      IsClosed (d.supportLocus ∩ ((relCover C R (fiberTwoCover π)).V₁ : Set (relCurve C R))) :=
  ⟨A.isClosed_supportLocus_inter_chart₀_of_forall_supportLeak_eq_empty fun j =>
      A.supportLeak_eq_empty_of_finite_colength _ (hc.finite_colength (Sum.inl j)),
    A.isClosed_supportLocus_inter_chart₁_of_forall_supportLeak_eq_empty fun j =>
      A.supportLeak_eq_empty_of_finite_colength _ (hc.finite_colength (Sum.inr j))⟩

/-- **The obstruction with no connectivity hypothesis, in refuting form.**  A divisor one of
whose pinned-chart traces fails to be closed admits no certified adaptation, in any degree. -/
theorem not_isCertified_of_not_isClosed_inter_chart₀ {n : ℕ}
    {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R π d)
    (h : ¬ IsClosed (d.supportLocus ∩
      ((relCover C R (fiberTwoCover π)).V₀ : Set (relCurve C R)))) :
    ¬ A.IsCertified n :=
  fun hc => h (A.isClosed_supportLocus_inter_chart_of_isCertified hc).1

/-- **The chart obstruction is a statement about the divisor class.**  If *some* representative
`d₁` of the class has connected support with a point off `V₀` and a point off `V₁`, then *no*
representative `d₂` of the same class admits a certified adaptation.

`DivFamZar` is a `DivEq` quotient, so this — not the representative-level statement — is what
tells the functor apart from the relative-divisor functor. -/
theorem not_isCertified_of_divEq_of_isPreconnected_of_witnesses {n : ℕ}
    {d₁ d₂ : (relCurve C R).LocalEquations} (h : Scheme.LocalEquations.DivEq d₁ d₂)
    (A : DivisorAdaptation C R π d₂)
    (hconn : _root_.IsPreconnected d₁.supportLocus)
    {x y : relCurve C R} (hx : x ∈ d₁.supportLocus) (hy : y ∈ d₁.supportLocus)
    (hx₀ : x ∉ ((relCover C R (fiberTwoCover π)).V₀ : Set (relCurve C R)))
    (hy₁ : y ∉ ((relCover C R (fiberTwoCover π)).V₁ : Set (relCurve C R))) :
    ¬ A.IsCertified n := by
  rw [h.supportLocus_eq] at hconn hx hy
  exact A.not_isCertified_of_isPreconnected_of_witnesses hconn hx hy hx₀ hy₁

end DivisorAdaptation

end AlgebraicGeometry
