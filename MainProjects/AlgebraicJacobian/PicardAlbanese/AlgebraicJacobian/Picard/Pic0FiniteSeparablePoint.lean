/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicRepColimitMountain
import AlgebraicJacobian.Picard.FiniteStageData
import AlgebraicJacobian.Curve.SeparablyClosedPoints
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.FieldTheory.Galois.Basic

/-!
# Finite-separable points of a smooth curve

A point over an algebraic extension of a finitely presented `k`-scheme spreads to one finite
subextension.  Applying this to a point of a challenge curve over a separable closure produces a
point over a finite separable extension, without a rational-point or divisor-degree hypothesis.

The distinction is important over imperfect fields: an arbitrary closed point of a smooth curve
can have inseparable residue field, but a separable closed point can still be chosen.

## Main declarations

* `AlgebraicGeometry.exists_finiteSubextension_point_of_point` spreads a point over an algebraic
  extension to a finite subextension.
* `AlgebraicGeometry.FiniteSeparablePointData` retains the finite stage and its point map.
* `AlgebraicGeometry.FiniteGaloisPointData` retains the canonical normal-closure stage, its
  inclusion, the two point maps, and their transition compatibility.
* `AlgebraicGeometry.exists_separableClosure_finSubext_point` keeps the resulting finite stage
  inside a fixed separable closure.
* `AlgebraicGeometry.exists_finite_separable_point` produces a finite separable extension over
  which any challenge curve has a rational point.
* `AlgebraicGeometry.exists_finite_galois_point` enlarges that stage to its finite Galois normal
  closure while preserving the point.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open DatG0

noncomputable section

variable {k : Type u} [Field k]

variable (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom]
    (L : Type u) [Field L] [Algebra k L] in
/-- Smooth relative dimension one, keyed on the bundled base-changed curve. -/
instance instSmoothOfRelativeDimensionBaseChangeBundle :
    SmoothOfRelativeDimension 1 (baseChangeBundle C L).hom :=
  instSmoothOfRelativeDimensionSndLeft C L

variable (C : Over (Spec (.of k))) [IsProper C.hom]
    (L : Type u) [Field L] [Algebra k L] in
/-- Properness, keyed on the bundled base-changed curve. -/
instance instIsProperBaseChangeBundle : IsProper (baseChangeBundle C L).hom :=
  instIsProperSndLeft C L

variable (C : Over (Spec (.of k))) [GeometricallyIrreducible C.hom]
    (L : Type u) [Field L] [Algebra k L] in
/-- Geometric irreducibility, keyed on the bundled base-changed curve. -/
instance instGeometricallyIrreducibleBaseChangeBundle :
    GeometricallyIrreducible (baseChangeBundle C L).hom :=
  instGeometricallyIrreducibleSndLeft C L

/-- A point over an algebraic extension of a finitely presented `k`-scheme is already defined
over one finite subextension.

The finite subextensions form the cofiltered affine diagram `deltaSchemeDiagram`, whose limit is
`Spec Omega`.  Local finite presentation of `X/k` makes the point factor through one stage via
`Scheme.exists_pi_app_comp_eq_of_locallyOfFinitePresentation`.  If `Omega/k` is separable, the
returned stage is a finite separable extension by `DatG0.isSeparable_finSubext`. -/
theorem exists_finiteSubextension_point_of_point {k Omega : Type u} [Field k] [Field Omega]
    [Algebra k Omega] [Algebra.IsAlgebraic k Omega] [Algebra.IsSeparable k Omega]
    {X : Over (Spec (.of k))} [LocallyOfFinitePresentation X.hom]
    (a : Spec (.of Omega) ⟶ X.left)
    (ha : a ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k Omega))) :
    ∃ L : FinSubext k Omega, Nonempty (overSpec k L.1 ⟶ X) := by
  let E := deltaSchemeDiagram (k := k) (K := Omega)
  let D := E ⋙ Over.forget (Spec (.of k))
  let t : D ⟶ (Functor.const _).obj (Spec (.of k)) :=
    { app := fun i => (E.obj i).hom
      naturality := fun {i j} h => by
        change (E.map h).left ≫ (E.obj j).hom = (E.obj i).hom ≫ 𝟙 _
        rw [Category.comp_id]
        exact Over.w (E.map h) }
  let c : Cone D := Scheme.Spec.mapCone (deltaCocone (k := k) (K := Omega)).op
  have hc : IsLimit c :=
    isLimitOfPreserves Scheme.Spec (deltaIsColimit (k := k) (K := Omega)).op
  letI (i : (FinSubext k Omega)ᵒᵖ) : IsAffine (D.obj i) := by
    change IsAffine (Spec (.of (unop i).1))
    infer_instance
  letI (i : (FinSubext k Omega)ᵒᵖ) : CompactSpace (D.obj i) := by
    change CompactSpace (Spec (.of (unop i).1))
    infer_instance
  letI (i : (FinSubext k Omega)ᵒᵖ) : QuasiSeparatedSpace (D.obj i) := by
    change QuasiSeparatedSpace (Spec (.of (unop i).1))
    infer_instance
  letI {i j : (FinSubext k Omega)ᵒᵖ} (h : i ⟶ j) : IsAffineHom (D.map h) := by
    apply isAffineHom_of_isAffine
  have hct : c.π ≫ t = (Functor.const _).map (a ≫ X.hom) := by
    ext i
    change Spec.map (CommRingCat.ofHom (IntermediateField.val (unop i).1).toRingHom) ≫
      (overSpec k (unop i).1).hom = a ≫ X.hom
    rw [ha, overSpec_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  obtain ⟨i, g, _, hg⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t X.hom c hc a hct
  exact ⟨unop i, ⟨Over.homMk g hg⟩⟩

/-- A point together with the finite stage of `SeparableClosure k` over which it is defined.

Unlike the existential compatibility theorem below, this package retains the canonical map from
the stage to the separable closure through `stage.inclusion`. -/
structure FiniteSeparablePointData {k : Type u} [Field k]
    (C : Over (Spec (.of k))) where
  stage : FiniteStageData k (SeparableClosure k)
  point : overSpec k stage.stage ⟶ C

namespace FiniteSeparablePointData

/-- The finite-subextension index underlying a packaged separable point. -/
def finSubext {k : Type u} [Field k] {C : Over (Spec (.of k))}
    (D : FiniteSeparablePointData C) : FinSubext k (SeparableClosure k) :=
  D.stage.toFinSubext

@[simp]
theorem finSubext_field {k : Type u} [Field k] {C : Over (Spec (.of k))}
    (D : FiniteSeparablePointData C) : D.finSubext.1 = D.stage.stage := rfl

end FiniteSeparablePointData

/-- Every challenge curve has a point over a finite subextension of its separable closure.

First take a point of the base-changed curve over a separable closure, using smooth relative
dimension one and geometric irreducibility for nonemptiness.  Its projection to `C` spreads to a
finite stage by `exists_finiteSubextension_point_of_point`; every such stage inside the separable
closure is separable.  The returned package is the stable producer behind
`exists_separableClosure_finSubext_point`. -/
theorem exists_finiteSeparablePointData {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] : Nonempty (FiniteSeparablePointData C) := by
  let Omega := SeparableClosure k
  letI : Algebra.IsAlgebraic k Omega :=
    separableClosure.isAlgebraic k (AlgebraicClosure k)
  letI : Algebra.IsSeparable k Omega :=
    separableClosure.isSeparable k (AlgebraicClosure k)
  letI : SmoothOfRelativeDimension 1 (baseChangeBundle C Omega).hom :=
    instSmoothOfRelativeDimensionBaseChangeBundle C Omega
  letI : GeometricallyIrreducible (baseChangeBundle C Omega).hom :=
    instGeometricallyIrreducibleBaseChangeBundle C Omega
  obtain ⟨q, hq⟩ :=
    SeparablyClosed.exists_rationalPoint_of_smoothOfRelativeDimension_one
      (baseChangeBundle C Omega).hom
  let fst' : (baseChangeBundle C Omega).left ⟶ C.left :=
    pullback.fst C.hom (overSpec k Omega).hom
  let a : Spec (.of Omega) ⟶ C.left := q ≫ fst'
  have hcond : fst' ≫ C.hom =
      (baseChangeBundle C Omega).hom ≫ (overSpec k Omega).hom :=
    pullback.condition
  have haOver : a ≫ C.hom = (overSpec k Omega).hom := by
    dsimp only [a]
    rw [Category.assoc, hcond, ← Category.assoc]
    rw [hq, Category.id_comp]
  have ha : a ≫ C.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k Omega)) :=
    haOver.trans (overSpec_hom k Omega)
  obtain ⟨L, ⟨p⟩⟩ := exists_finiteSubextension_point_of_point a ha
  exact ⟨{
    stage := FiniteStageData.ofFinSubext L
    point := p }⟩

/-- A chosen packaged finite separable point.  Consumers that only need existence should use
`exists_finiteSeparablePointData`; consumers that need stable projections can use this choice. -/
noncomputable def finiteSeparablePointData {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] : FiniteSeparablePointData C :=
  Classical.choice (exists_finiteSeparablePointData C)

/-- Existential compatibility adapter for `finiteSeparablePointData`. -/
theorem exists_separableClosure_finSubext_point {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] :
    ∃ L : FinSubext k (SeparableClosure k), Nonempty (overSpec k L.1 ⟶ C) := by
  let D := finiteSeparablePointData C
  exact ⟨D.finSubext, ⟨D.point⟩⟩

/-- Every challenge curve acquires a rational point over a finite separable extension. -/
theorem exists_finite_separable_point {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
      (_ : Module.Finite k L) (_ : Algebra.IsSeparable k L),
      Nonempty (overSpec k L ⟶ C) := by
  let D := finiteSeparablePointData C
  letI : Module.Finite k D.stage.stage := D.stage.finiteWitness
  letI : Algebra.IsSeparable k D.stage.stage := isSeparable_finSubext D.finSubext
  exact ⟨D.stage.stage, inferInstance, inferInstance, inferInstance, inferInstance, ⟨D.point⟩⟩

/-- A finite separable point, its canonical normal-closure stage, and the induced Galois point.

The equality `normalClosure_eq` pins the second carrier to the normal closure rather than merely
some finite Galois extension.  `inclusion` retains the actual stage map and its ambient coherence;
`point_compatibility` records that the Galois point is obtained by pulling the separable point
along the corresponding morphism of affine schemes. -/
structure FiniteGaloisPointData {k : Type u} [Field k]
    (C : Over (Spec (.of k))) where
  separableStage : FiniteStageData k (SeparableClosure k)
  separablePoint : overSpec k separableStage.stage ⟶ C
  normalStage : FiniteStageData k (SeparableClosure k)
  normalClosure_eq : normalStage.stage =
    IntermediateField.normalClosure k separableStage.stage (SeparableClosure k)
  inclusion : FiniteStageInclusion separableStage normalStage
  isGalois : IsGalois k normalStage.stage
  galoisPoint : overSpec k normalStage.stage ⟶ C
  point_compatibility : galoisPoint =
    deltaSchemeMap (L₁ := separableStage.toFinSubext) (L₂ := normalStage.toFinSubext)
      inclusion.le ≫ separablePoint

namespace FiniteGaloisPointData

/-- The finite-subextension index of the separable point. -/
def separableFinSubext {k : Type u} [Field k] {C : Over (Spec (.of k))}
    (D : FiniteGaloisPointData C) : FinSubext k (SeparableClosure k) :=
  D.separableStage.toFinSubext

/-- The finite-subextension index of the normal-closure point. -/
def normalFinSubext {k : Type u} [Field k] {C : Over (Spec (.of k))}
    (D : FiniteGaloisPointData C) : FinSubext k (SeparableClosure k) :=
  D.normalStage.toFinSubext

@[simp]
theorem galoisPoint_eq {k : Type u} [Field k] {C : Over (Spec (.of k))}
    (D : FiniteGaloisPointData C) : D.galoisPoint =
    deltaSchemeMap (L₁ := D.separableFinSubext) (L₂ := D.normalFinSubext)
      D.inclusion.le ≫ D.separablePoint :=
  D.point_compatibility

end FiniteGaloisPointData

/-- Construct the packaged finite Galois point by taking the canonical normal closure of the
packaged separable stage. -/
noncomputable def finiteGaloisPointData {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] : FiniteGaloisPointData C := by
  let D := finiteSeparablePointData C
  letI : FiniteDimensional k D.stage.stage := D.stage.finiteWitness
  let N : FiniteStageData k (SeparableClosure k) := {
    stage := IntermediateField.normalClosure k D.stage.stage (SeparableClosure k)
    finiteWitness := inferInstance }
  let i : FiniteStageInclusion D.stage N :=
    FiniteStageInclusion.ofLE (IntermediateField.le_normalClosure D.stage.stage)
  letI : IsGalois k N.stage := by
    dsimp only [N]
    infer_instance
  exact {
    separableStage := D.stage
    separablePoint := D.point
    normalStage := N
    normalClosure_eq := rfl
    inclusion := i
    isGalois := inferInstance
    galoisPoint :=
      deltaSchemeMap (L₁ := D.finSubext) (L₂ := N.toFinSubext) i.le ≫ D.point
    point_compatibility := rfl }

/-- Every challenge curve acquires a rational point over a finite Galois extension.

Take the finite stage inside `SeparableClosure k` produced above and replace it by its normal
closure in the same ambient field.  Mathlib supplies finite dimensionality and the Galois
instance for this normal closure.  The original point pushes forward along the inclusion of
finite stages via `DatG0.deltaSchemeMap`.

No rational-point, divisor-degree, separability, or Galois hypothesis is added to the curve. -/
theorem exists_finite_galois_point {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
      (_ : Module.Finite k L) (_ : IsGalois k L),
      Nonempty (overSpec k L ⟶ C) := by
  let D := finiteGaloisPointData C
  letI : Module.Finite k D.normalStage.stage := D.normalStage.finiteWitness
  letI : IsGalois k D.normalStage.stage := D.isGalois
  exact ⟨D.normalStage.stage, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨D.galoisPoint⟩⟩

end

end AlgebraicGeometry
