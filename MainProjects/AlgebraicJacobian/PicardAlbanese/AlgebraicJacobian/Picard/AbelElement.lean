/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.GraphDegree
import AlgebraicJacobian.Picard.PicEtUnit
import AlgebraicJacobian.Picard.Pic0Functor

/-!
# The Abel element (G-D8)

For the challenge curve `C` over `k` with a rational point `P : 𝟙_ ⟶ C`, the **Abel
element** is the degree-zero family class on the test `T = C`

`abelElement P : pic0Subgroup C C`,

the étale-unit image of the Čech class `𝒪(Δ) · 𝒪(P × C)⁻¹` on `(C ⊗ C).left` — the graph
class of `𝟙 C` times the inverse graph class of the constant point `toUnit C ≫ P`
(`abelCechClass`, both factors through the *graph* API of `Curve/GraphDivisor.lean` so one
degree certificate serves both).  This is the element the frozen `ofCurve`
(`Challenge.lean:125`) consumes as `rep.homEquiv.symm (abelElement P)` once the Wave-4
`RepresentableBy` datum exists.

## Main declarations

* `AlgebraicGeometry.degAt_relPicToPicEt` — **the general-test unit seam** (complements the
  landed affine-test DAT-4): the degree at a field point of a unit-image class is the
  relative degree of the restricted class, `degAt (relPicToPicEt z) t = relPicDeg K
  (relPicMap C t z)`.  By `picEtMap_relPicToPicEt` + `picEtAffineEquiv_relPicToPicEt` +
  `degAff_unit`.
* `AlgebraicGeometry.abelCechClass`, `AlgebraicGeometry.abelPicEt` — the definitional
  assembly.
* `AlgebraicGeometry.degAt_abelPicEt` — **the degree-zero certificate**: at every field
  point both factors restrict to graph classes of `K`-points
  (`graphLocalEquations_base_change` + `toUnit_unique`), each of degree one by THE
  keystone `classDeg_graphPicClass`; so the degree is `1 − 1 = 0`.  A proved equality,
  never a choice (the campaign's (C2) discipline).
* `AlgebraicGeometry.abelElement` — the Abel element of `pic0Subgroup C C`.
* `AlgebraicGeometry.abelPicEt_map` — the functor-point formula: restriction along any
  `f : T ⟶ C` is the graph-minus-constant class of `f` on `T` (what Wave-6 evaluates).
* `AlgebraicGeometry.abelElement_map_point` — **the pointing law**: restriction along `P`
  itself kills the Abel element, `(pic0Functor C).map P.op (abelElement P) = 1` — both
  factors become the graph class of the same point of `𝟙_`.  This is the input the frozen
  `comp_ofCurve` (`Challenge.lean:130`) consumes.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The general-test unit seam -/

/-- **The unit seam at arbitrary tests** (complements the landed affine-test DAT-4 seam):
the degree at a field point `t : overSpec k K ⟶ T` of the étale-unit image of a relative
Picard class `z : relPic C T` is the relative degree over `K` of the restriction of `z`
along `t`.  Route: `picEtMap_relPicToPicEt` (naturality of the unit) collapses the
restriction, `picEtAffineEquiv_relPicToPicEt` (affine consistency) identifies the plus
class, and `PicEtAff.degAff_unit` reads the degree. -/
theorem degAt_relPicToPicEt {T : Over (Spec (.of k))} (z : relPic C T) {K : Type u}
    [Field K] [Algebra k K] (t : overSpec k K ⟶ T) :
    degAt (relPicToPicEt C T z) t = relPicDeg K (relPicMap C t z) := by
  change PicEtAff.degAff K
      (picEtAffineEquiv C K (picEtMap C t (relPicToPicEt C T z))) = _
  rw [picEtMap_relPicToPicEt, picEtAffineEquiv_relPicToPicEt, PicEtAff.degAff_unit]

/-! ## The definitional assembly -/

variable (C) in
/-- **The Abel Čech class** on the test `T = C`: the class `𝒪(Δ) · 𝒪(P × C)⁻¹` of the
diagonal minus the constant graph, both spelled through the graph API — the graph of
`𝟙 C` is the diagonal, the graph of `toUnit C ≫ P` is `P × C`. -/
def abelCechClass (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) : (C ⊗ C).left.CechPic :=
  Over.graphPicClass C (𝟙 C) * (Over.graphPicClass C (toUnit C ≫ P))⁻¹

variable (C) in
/-- The underlying étale Picard class of the Abel element: the unit image of the Abel
Čech class. -/
def abelPicEt (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) : picEt C C :=
  relPicToPicEt C C (relPicMk C C (abelCechClass C P))

/-! ## The degree-zero certificate -/

omit [GeometricallyIrreducible C.hom] in
/-- **The restriction of the Abel class at a point is a graph-minus-constant-graph class**
(the functor-point formula, Čech level): pulling the Abel Čech class back along `C ◁ f`
for any `f : T ⟶ C` gives the graph class of `f` times the inverse graph class of the
constant `toUnit T ≫ P`.  Base change of the graph (`graphLocalEquations_base_change`)
plus terminality of the unit (`toUnit_unique`). -/
theorem cechPicMap_abelCechClass {T : Over (Spec (.of k))} (f : T ⟶ C)
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    Scheme.CechPic.map (C ◁ f).left (abelCechClass C P)
      = Over.graphPicClass C f * (Over.graphPicClass C (toUnit T ≫ P))⁻¹ := by
  rw [abelCechClass, map_mul, map_inv, ← Over.graphLocalEquations_base_change C f (𝟙 C),
    ← Over.graphLocalEquations_base_change C f (toUnit C ≫ P), Category.comp_id,
    ← Category.assoc, toUnit_unique (f ≫ toUnit C) (toUnit T)]

/-- **The degree-zero certificate of the Abel class**: at every field point
`t : overSpec k K ⟶ C` the degree is `1 − 1 = 0` — both factors restrict to graph
classes of `K`-points, each of degree one by THE degree-1 keystone
`classDeg_graphPicClass`. -/
theorem degAt_abelPicEt (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) {K : Type u} [Field K]
    [Algebra k K] (t : overSpec k K ⟶ C) :
    degAt (abelPicEt C P) t = 0 := by
  rw [abelPicEt, degAt_relPicToPicEt, relPicMap_mk, relPicDeg_relPicMk,
    cechPicMap_abelCechClass, classDeg_mul, classDeg_inv, classDeg_graphPicClass,
    classDeg_graphPicClass]
  ring

/-! ## The Abel element -/

variable (C) in
/-- **The Abel element** (G-D8): the degree-zero family class
`𝒪(Δ) · 𝒪(P × C)⁻¹ ∈ pic0Subgroup C C`.  The frozen `ofCurve` (`Challenge.lean:125`) is
discharged as `rep.homEquiv.symm (abelElement P)` once the Wave-4 `RepresentableBy` datum
`rep` exists. -/
def abelElement (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) : pic0Subgroup C C :=
  ⟨abelPicEt C P, fun _ _ _ t => degAt_abelPicEt P t⟩

@[simp]
theorem abelElement_coe (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    (abelElement C P : picEt C C) = abelPicEt C P :=
  rfl

/-! ## The functor-point formula and the pointing law -/

/-- **The functor-point formula of the Abel element** (what Wave-6's Albanese universal
property evaluates): the underlying étale class of the restriction of the Abel element
along any point `f : T ⟶ C` is the unit image of the graph-minus-constant-graph class
of `f` on `T`. -/
theorem abelPicEt_map {T : Over (Spec (.of k))} (f : T ⟶ C)
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    picEtMap C f (abelPicEt C P)
      = relPicToPicEt C T (relPicMk C T
          (Over.graphPicClass C f * (Over.graphPicClass C (toUnit T ≫ P))⁻¹)) := by
  rw [abelPicEt, picEtMap_relPicToPicEt, relPicMap_mk, cechPicMap_abelCechClass]

/-- The functor-point formula, subfunctor form (`pic0Map` is the map part of
`pic0Functor`, `pic0Functor_map`). -/
theorem abelElement_map {T : Over (Spec (.of k))} (f : T ⟶ C)
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    (pic0Map C f (abelElement C P) : picEt C T)
      = relPicToPicEt C T (relPicMk C T
          (Over.graphPicClass C f * (Over.graphPicClass C (toUnit T ≫ P))⁻¹)) :=
  abelPicEt_map f P

/-- **The pointing law** (the `comp_ofCurve` input, design §4.6): restriction of the Abel
element along the rational point `P` itself is the trivial class — both graph factors
become the graph class of the same point of the unit test, so the Čech class is already
`1`. -/
theorem abelElement_map_point (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    (pic0Functor C).map P.op (abelElement C P) = 1 := by
  have h1 : Over.graphPicClass C P
        * (Over.graphPicClass C (toUnit (𝟙_ (Over (Spec (.of k)))) ≫ P))⁻¹ = 1 := by
    rw [toUnit_unique (toUnit (𝟙_ (Over (Spec (.of k))))) (𝟙 _), Category.id_comp,
      mul_inv_cancel]
  refine Subtype.ext ?_
  change picEtMap C P (abelPicEt C P) = 1
  rw [abelPicEt_map P P, h1, map_one, map_one]

end

end AlgebraicGeometry
