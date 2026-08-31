/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0Pullback
import AlgebraicJacobian.Picard.JacobianData

/-!
# The `Grp`-level packaging of the curve transport (W7-F6, the `functor.map` layer)

Given Jacobian representability data `dX`/`dY` for two curve bundles `X`/`Y` over `k`
and a morphism `g : X ⟶ Y`, the degree-zero pullback transformation `pic0PullbackNat g`
(the EV-cor layer, `AlgebraicJacobian.Picard.Pic0Pullback`) conjugates through the
`yonedaGrp` embedding to a morphism of group objects `Grp.mk dY.J ⟶ Grp.mk dX.J` —
**the pinned probe-C `functor.map` construction** of the ratified
`informal/w7-worksheet.md` (§2.2 W7-F6, §5 probe C):

`yonedaGrpFullyFaithful.preimage ((yonedaGrpObjIsoOfRepresentableBy dY.J _ dY.rep).hom
  ≫ _ ≫ (yonedaGrpObjIsoOfRepresentableBy dX.J _ dX.rep).inv)`.

* `AlgebraicGeometry.JacobianData.pullbackHom dX dY g` — the construction.  The
  `IsMonHom` obligation is discharged by construction: the conjugate is a natural
  transformation of *group*-valued presheaves.
* `AlgebraicGeometry.JacobianData.yonedaGrp_map_pullbackHom` — the defining equation
  (`map_preimage`), through which everything else is proved.
* `AlgebraicGeometry.JacobianData.pullbackHom_id` /
  `AlgebraicGeometry.JacobianData.pullbackHom_comp` — the functor laws, by `yonedaGrp`
  faithfulness from the F-1..F-3 transport laws (`pic0PullbackNat_id`/`_comp`).  Per the
  ratified D1 datum idiom the statements repeat the datum argument at a shared curve
  (`pullbackHom dX dX (𝟙 X)`), so the frozen discharge is pure instantiation.
* `AlgebraicGeometry.JacobianData.comp_pullbackHom` /
  `AlgebraicGeometry.JacobianData.homEquiv_comp_pullbackHom` — the universal-element
  characterization: under the two `homEquiv`s, composition with `pullbackHom` *is*
  `pic0Pullback` — the "one pinned universal element" audit interface for the K-cluster
  and `baseChange_ofCurve`.

## The frozen consumer (DAT-J scope boundary)

The frozen `Jacobian.functor` fields of `Challenge.lean` wait on the DAT-J producer
`jacobianData` (Fleet A).  At discharge time, with `Jacobian C := (jacobianData C).J`
and `instGrpObj := (jacobianData C).grpObj`, the closure is pure instantiation:

* `map f := pullbackHom (jacobianData X.unop.carrier) (jacobianData Y.unop.carrier)
  f.unop` for `f : X ⟶ Y` in `(Curve k)ᵒᵖ` (so `f.unop : Y.unop ⟶ X.unop`, and the
  construction is applied at `X := Y.unop.carrier`, `Y := X.unop.carrier`);
* `map_id X := pullbackHom_id (jacobianData X.unop.carrier)`;
* `map_comp f g := pullbackHom_comp (jacobianData _) (jacobianData _) (jacobianData _)
  g.unop f.unop`.

Nothing here touches `Challenge.lean`; all statements take explicit per-curve
`JacobianData` arguments (ratified D1: one datum per named curve, no data at unnamed
curves), with group structures activated per statement by `letI := d.grpObj`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace JacobianData

variable {k : Type u} [Field k] {X Y Z : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] [GeometricallyIrreducible X.hom]
  [SmoothOfRelativeDimension 1 Y.hom] [IsProper Y.hom] [GeometricallyIrreducible Y.hom]

noncomputable section

/-- **The pinned `functor.map` construction** (W7-F6, probe C): the morphism of group
objects `Grp.mk dY.J ⟶ Grp.mk dX.J` induced by a curve morphism `g : X ⟶ Y` —
contravariantly, pullback of degree-zero line-bundle classes.  The `yonedaGrp`-conjugate
of the degree-zero pullback transformation `pic0PullbackNat g` by the two representing
isomorphisms; the `IsMonHom` obligation is discharged by construction. -/
def pullbackHom (dX : JacobianData X) (dY : JacobianData Y) (g : X ⟶ Y) :
    letI := dX.grpObj
    letI := dY.grpObj
    (Grp.mk dY.J ⟶ Grp.mk dX.J) :=
  letI := dX.grpObj
  letI := dY.grpObj
  yonedaGrpFullyFaithful.preimage
    ((yonedaGrpObjIsoOfRepresentableBy dY.J _ dY.rep).hom
      ≫ Functor.whiskerRight (pic0PullbackNat g) (forget₂ CommGrpCat GrpCat)
      ≫ (yonedaGrpObjIsoOfRepresentableBy dX.J _ dX.rep).inv)

/-- **The defining equation of `pullbackHom`** (`map_preimage`): its `yonedaGrp` image
is the conjugated degree-zero pullback transformation.  Everything about `pullbackHom`
is proved through this equation and `yonedaGrp` faithfulness. -/
theorem yonedaGrp_map_pullbackHom (dX : JacobianData X) (dY : JacobianData Y)
    (g : X ⟶ Y) :
    letI := dX.grpObj
    letI := dY.grpObj
    yonedaGrp.map (pullbackHom dX dY g)
      = (yonedaGrpObjIsoOfRepresentableBy dY.J _ dY.rep).hom
        ≫ Functor.whiskerRight (pic0PullbackNat g) (forget₂ CommGrpCat GrpCat)
        ≫ (yonedaGrpObjIsoOfRepresentableBy dX.J _ dX.rep).inv :=
  yonedaGrpFullyFaithful.map_preimage _

/-- **`map_id` at the datum level** (ratified D1 shape: the datum argument is repeated
at the shared curve, so the frozen `functor.map_id` discharge is pure instantiation):
pullback along the identity curve morphism is the identity of `Grp.mk dX.J`.  By
`yonedaGrp` faithfulness from `pic0PullbackNat_id`. -/
theorem pullbackHom_id (dX : JacobianData X) :
    letI := dX.grpObj
    pullbackHom dX dX (𝟙 X) = 𝟙 (Grp.mk dX.J) := by
  letI := dX.grpObj
  refine yonedaGrpFullyFaithful.map_injective ?_
  -- the conjugate collapses at the `yonedaGrpObj` level, where every composition is
  -- well-typed on the nose
  have hid : (yonedaGrpObjIsoOfRepresentableBy dX.J _ dX.rep).hom
        ≫ Functor.whiskerRight (pic0PullbackNat (𝟙 X)) (forget₂ CommGrpCat GrpCat)
        ≫ (yonedaGrpObjIsoOfRepresentableBy dX.J _ dX.rep).inv
      = 𝟙 (yonedaGrpObj dX.J) := by
    rw [pic0PullbackNat_id, Functor.whiskerRight_id', Category.id_comp, Iso.hom_inv_id]
  rw [yonedaGrp_map_pullbackHom, CategoryTheory.Functor.map_id]
  exact hid

variable [SmoothOfRelativeDimension 1 Z.hom] [IsProper Z.hom]
  [GeometricallyIrreducible Z.hom]

/-- **`map_comp` at the datum level** (ratified D1 shape: one datum per named curve,
each repeated wherever its curve recurs): pullback along a composite of curve morphisms
is the composite of the pullbacks, contravariantly.  By `yonedaGrp` faithfulness from
`pic0PullbackNat_comp`. -/
theorem pullbackHom_comp (dX : JacobianData X) (dY : JacobianData Y)
    (dZ : JacobianData Z) (g : X ⟶ Y) (g' : Y ⟶ Z) :
    letI := dX.grpObj
    letI := dY.grpObj
    letI := dZ.grpObj
    pullbackHom dX dZ (g ≫ g') = pullbackHom dY dZ g' ≫ pullbackHom dX dY g := by
  letI := dX.grpObj
  letI := dY.grpObj
  letI := dZ.grpObj
  refine yonedaGrpFullyFaithful.map_injective ?_
  -- the cocycle of conjugates, at the `yonedaGrpObj` level where every composition is
  -- well-typed on the nose
  have hcomp : (yonedaGrpObjIsoOfRepresentableBy dZ.J _ dZ.rep).hom
        ≫ Functor.whiskerRight (pic0PullbackNat (g ≫ g')) (forget₂ CommGrpCat GrpCat)
        ≫ (yonedaGrpObjIsoOfRepresentableBy dX.J _ dX.rep).inv
      = ((yonedaGrpObjIsoOfRepresentableBy dZ.J _ dZ.rep).hom
          ≫ Functor.whiskerRight (pic0PullbackNat g') (forget₂ CommGrpCat GrpCat)
          ≫ (yonedaGrpObjIsoOfRepresentableBy dY.J _ dY.rep).inv)
        ≫ (yonedaGrpObjIsoOfRepresentableBy dY.J _ dY.rep).hom
          ≫ Functor.whiskerRight (pic0PullbackNat g) (forget₂ CommGrpCat GrpCat)
          ≫ (yonedaGrpObjIsoOfRepresentableBy dX.J _ dX.rep).inv := by
    rw [pic0PullbackNat_comp, Functor.whiskerRight_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [CategoryTheory.Functor.map_comp, yonedaGrp_map_pullbackHom,
    yonedaGrp_map_pullbackHom, yonedaGrp_map_pullbackHom]
  exact hcomp

/-! ## The universal-element characterization

Under the two universal properties, composing with `pullbackHom` *is* the degree-zero
pullback: the value of the construction on test points is pinned, which is what the
K-cluster coherence audits and `baseChange_ofCurve` consume (the "one pinned universal
element" rule, w7-worksheet R-W7-6). -/

/-- The action of `pullbackHom` on test points, `symm` form: composition with the
underlying morphism `(pullbackHom dX dY g).hom.hom : dY.J ⟶ dX.J` sends the morphism
classified by a degree-zero class `λ` to the morphism classified by
`pic0Pullback g T λ`. -/
theorem comp_pullbackHom (dX : JacobianData X) (dY : JacobianData Y) (g : X ⟶ Y)
    {T : Over (Spec (.of k))} (f : T ⟶ dY.J) :
    f ≫ (pullbackHom dX dY g).hom.hom
      = dX.homEquiv.symm (pic0Pullback g T (dY.homEquiv f)) := by
  letI := dX.grpObj
  letI := dY.grpObj
  exact congrArg
    (fun (α : yonedaGrpObj dY.J ⟶ yonedaGrpObj dX.J) => (α.app (op T)) f)
    (yonedaGrp_map_pullbackHom dX dY g)

/-- **The universal-element characterization of `pullbackHom`**: under the two
`homEquiv`s, composition with `pullbackHom dX dY g` is `pic0Pullback g` — the value of
the pinned `functor.map` construction on functor points. -/
theorem homEquiv_comp_pullbackHom (dX : JacobianData X) (dY : JacobianData Y)
    (g : X ⟶ Y) {T : Over (Spec (.of k))} (f : T ⟶ dY.J) :
    dX.homEquiv (f ≫ (pullbackHom dX dY g).hom.hom)
      = pic0Pullback g T (dY.homEquiv f) := by
  rw [comp_pullbackHom, Equiv.apply_symm_apply]

end

end JacobianData

end AlgebraicGeometry
