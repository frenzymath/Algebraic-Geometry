/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ThetaAssembly
import AlgebraicJacobian.Picard.JacobianData

/-!
# Base change of the Jacobian representability datum (Wave 7, W7-B5/B6a/B6b)

For a field embedding `k → L`, the curve bundle `C` over `k`, and a Jacobian datum
`d : JacobianData C`, this file transports `d` across the base change `σ = Spec L → Spec k`
to a Jacobian datum on the base-changed curve `C_L = (baseChange k L).obj C`, and packages
the resulting canonical isomorphism as the datum-level input of the frozen `baseChangeIso`.

* `AlgebraicGeometry.JacobianData.baseChange` (**W7-B5**): the transported datum
  `JacobianData ((baseChange k L).obj C)` with representing object
  `(baseChange k L).obj d.J`.  Its universal datum is the verbatim mathlib
  adjunction-transport `(Over.mapPullbackAdj σ).representableBy d.J` moved by
  `RepresentableBy.ofIso` first along the whisker of `d.rep`'s Yoneda iso, then along the
  Type form of θ (`Picard/Pic0ThetaAssembly.lean`).  The two construction certificates
  transport by `MorphismProperty.baseChange_obj` (the frozen file's own pattern).

* `AlgebraicGeometry.grpObjObj_baseChange_eq` (**W7-B6a**): the group-object structure that the
  base-change functor transports onto `(baseChange k L).obj d.J` (`Functor.grpObjObj`) equals the
  one carried by the transported datum `d.baseChange L`.  Reduced by `GrpObj.ext` to a `MonObj`
  equality closed by the `monObjObj_eq_ofRepresentableBy` bridge and the general transport lemma
  `monObj_ofRepresentableBy_eq_of_iso`.

* `AlgebraicGeometry.baseChangeIsoOfData` (**W7-B6b**): the datum-level base-change isomorphism
  `(baseChange k L).mapGrp.obj (.mk d.J) ≅ .mk dL.J` for any Jacobian data `d`, `dL`, assembled from
  B-6a, `Grp.mkIso`, and the seam lemma `isMonHom_hom_of_representableBy`.  This is the datum-level
  input consumed (definitionally) by the frozen `AlgebraicGeometry.baseChangeIso`.

This file is the SOLE OWNER of the R-W7-4 instance-keying seams at the frozen spelling.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- **The transported Jacobian datum** (Wave-7 brick W7-B5): base change of the Jacobian
representability datum `d : JacobianData C` along a field embedding `k → L`.  The
representing object is `(baseChange k L).obj d.J`; its universal datum is the mathlib
adjunction transport `(Over.mapPullbackAdj σ).representableBy d.J` (representing
`T ↦ ((Over.map σ).obj T ⟶ d.J)`), moved by `RepresentableBy.ofIso` along the whisker of
`d.rep`'s Yoneda iso and then along θ's Type form `pic0ThetaType` to represent
`pic0TypeFunctor C_L`.  The certificates transport by base-change stability. -/
noncomputable def JacobianData.baseChange (d : JacobianData C)
    (L : Type u) [Field L] [Algebra k L] :
    JacobianData ((AlgebraicGeometry.baseChange k L).obj C) where
  J := (AlgebraicGeometry.baseChange k L).obj d.J
  rep :=
    (((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).representableBy
        d.J).ofIso
      (Functor.isoWhiskerLeft
          (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).op d.rep.toIso
        ≪≫ (pic0ThetaType k L C).symm))
  locallyOfFiniteType := by
    letI := d.locallyOfFiniteType
    exact MorphismProperty.baseChange_obj (Spec.map (CommRingCat.ofHom (algebraMap k L))) d.J
      inferInstance
  quasiCompact := by
    letI := d.quasiCompact
    exact MorphismProperty.baseChange_obj (Spec.map (CommRingCat.ofHom (algebraMap k L))) d.J
      inferInstance

/-! ## A general lemma: object isos intertwining two group-valued representations -/

section GeneralLemma

universe w u₁

open CartesianMonoidalCategory MonObj

/-- **The `IsMonHom` seam** (the one small general lemma the B-6b packaging needs): if an
object isomorphism `e : X ≅ X'` intertwines the universal `homEquiv`s of two representability
data `α`, `α'` for the *same* presheaf of monoids `F`, then `e.hom` is a morphism of the
induced `MonObj.ofRepresentableBy` monoid-object structures.  Proved elementwise through the
universal bijections, never diagram-chasing in `Mon _`/`Grp _` (R3 discipline). -/
theorem isMonHom_hom_of_representableBy {D : Type u₁} [Category.{w} D]
    [CartesianMonoidalCategory D] (F : Dᵒᵖ ⥤ MonCat.{w}) {X X' : D}
    (α : (F ⋙ CategoryTheory.forget _).RepresentableBy X)
    (α' : (F ⋙ CategoryTheory.forget _).RepresentableBy X')
    (e : X ≅ X')
    (h : ∀ {T : D} (f : T ⟶ X), α'.homEquiv (f ≫ e.hom) = α.homEquiv f) :
    letI := MonObj.ofRepresentableBy X F α
    letI := MonObj.ofRepresentableBy X' F α'
    IsMonHom e.hom := by
  letI := MonObj.ofRepresentableBy X F α
  letI := MonObj.ofRepresentableBy X' F α'
  constructor
  · apply α'.homEquiv.injective
    rw [h]
    simp only [MonObj.ofRepresentableBy_one, Functor.RepresentableBy.homEquiv']
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · have key : ∀ {T : D} (f : T ⟶ X), α'.homEquiv' (f ≫ e.hom) = α.homEquiv' f := fun f => h f
    apply α'.homEquiv'.injective
    rw [key, MonObj.ofRepresentableBy_mul, Equiv.apply_symm_apply, α'.homEquiv'_comp,
      MonObj.ofRepresentableBy_mul, Equiv.apply_symm_apply, map_mul, ← α'.homEquiv'_comp,
      ← α'.homEquiv'_comp, CartesianMonoidalCategory.tensorHom_fst,
      CartesianMonoidalCategory.tensorHom_snd, key, key]

end GeneralLemma

/-! ## B-6a: the mapGrp group structure agrees with the transported representation -/

section MonObjBridge

universe w u₁ u₂

open CartesianMonoidalCategory MonObj

/-- **The monoidal-transport ↔ adjunction-representation bridge** (the mathlib-gift-free core
of B-6a): for an adjunction `F ⊣ G` with `G` monoidal (cartesian) and a monoid object `Y`, the
monoid-object structure that `G` transports onto `G.obj Y` is exactly the one induced by the
adjunction representation `G.obj Y` represents `T ↦ (F.obj T ⟶ Y)`.  The `mul` diagram is a
`hom_ext` chase through the counit naturality and the lax-monoidal projection lemmas
`Functor.Monoidal.μ_fst`/`μ_snd`. -/
theorem monObjObj_eq_ofRepresentableBy {C₁ : Type u₁} {D₁ : Type u₂}
    [Category.{w} C₁] [Category.{w} D₁] [CartesianMonoidalCategory C₁]
    [CartesianMonoidalCategory D₁] {F : C₁ ⥤ D₁} {G : D₁ ⥤ C₁} (adj : F ⊣ G)
    [G.Monoidal] (Y : D₁) [MonObj Y] :
    Functor.monObjObj (F := G) (X := Y)
      = MonObj.ofRepresentableBy (G.obj Y) (F.op ⋙ yonedaMonObj Y) (adj.representableBy Y) := by
  refine MonObj.ext _ _ ?_
  rw [MonObj.ofRepresentableBy_mul, eq_comm, Equiv.symm_apply_eq]
  change (adj.homEquiv (MonoidalCategoryStruct.tensorObj (G.obj Y) (G.obj Y)) Y).symm
          (fst (G.obj Y) (G.obj Y))
        * (adj.homEquiv (MonoidalCategoryStruct.tensorObj (G.obj Y) (G.obj Y)) Y).symm
          (snd (G.obj Y) (G.obj Y))
      = (adj.homEquiv (MonoidalCategoryStruct.tensorObj (G.obj Y) (G.obj Y)) Y).symm
          (Functor.LaxMonoidal.μ G Y Y ≫ G.map μ[Y])
  rw [Hom.mul_def, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, Adjunction.counit_naturality,
    ← Category.assoc (F.map (Functor.LaxMonoidal.μ G Y Y))]
  congr 1
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [CartesianMonoidalCategory.lift_fst, ← Functor.Monoidal.μ_fst, Functor.map_comp,
      Category.assoc, adj.counit_naturality, Category.assoc]
  · rw [CartesianMonoidalCategory.lift_snd, ← Functor.Monoidal.μ_snd, Functor.map_comp,
      Category.assoc, adj.counit_naturality, Category.assoc]

end MonObjBridge

/-! ## A general lemma: `MonObj.ofRepresentableBy` transports along presheaf-of-monoid isos -/

section OfRepTransport

universe w u₁

open CartesianMonoidalCategory MonObj

/-- **`MonObj.ofRepresentableBy` is invariant under transport of the representing datum along a
presheaf-of-monoids isomorphism** (the reusable half of B-6a): if `Φ : F ≅ F'` is an isomorphism of
presheaves of monoids whose forgetful action intertwines the universal `homEquiv`s of two
representability data `α`, `α'` for a common representing object `X`, then the two induced
`MonObj X` structures coincide.  Proved elementwise through `homEquiv`'s injectivity and the
component multiplicativity of `Φ.hom`, never diagram-chasing in `Mon _` (the R3 term-mode
discipline). -/
theorem monObj_ofRepresentableBy_eq_of_iso {D : Type u₁} [Category.{w} D]
    [CartesianMonoidalCategory D] {F F' : Dᵒᵖ ⥤ MonCat.{w}} (Φ : F ≅ F') {X : D}
    (α : (F ⋙ CategoryTheory.forget _).RepresentableBy X)
    (α' : (F' ⋙ CategoryTheory.forget _).RepresentableBy X)
    (h : ∀ {T : D} (g : T ⟶ X), α'.homEquiv g = Φ.hom.app (op T) (α.homEquiv g)) :
    MonObj.ofRepresentableBy X F α = MonObj.ofRepresentableBy X F' α' := by
  refine MonObj.ext _ _ ?_
  simp only [MonObj.ofRepresentableBy_mul, Functor.RepresentableBy.homEquiv']
  apply α'.homEquiv.injective
  rw [Equiv.apply_symm_apply, h, Equiv.apply_symm_apply, map_mul, ← h, ← h]

end OfRepTransport

/-! ## B-6a / B-6b: the `mapGrp` group structure and the datum-level base-change isomorphism -/

section BaseChangeIso

open CartesianMonoidalCategory MonObj

/-- **W7-B6a — the `mapGrp` group structure agrees with the transported representation**: the group
object structure that the base-change functor transports onto `(baseChange k L).obj d.J`
(`Functor.grpObjObj`) equals the one carried by the B-5 transported datum `d.baseChange L`
(`GrpObj.ofRepresentableBy` of `pic0Functor C_L`).  Via `GrpObj.ext` the obligation is the
underlying `MonObj` equality; the `monObjObj_eq_ofRepresentableBy` bridge rewrites the `mapGrp`
side to the `Over.mapPullbackAdj σ` adjunction representation, and
`monObj_ofRepresentableBy_eq_of_iso` transports that along the monoid-presheaf iso
`θ⁻¹ ∘ (Yoneda of d.rep)` — whose forgetful action is `d`'s Type form of θ verbatim, so the
intertwining hypothesis is closed by `rfl`. -/
theorem grpObjObj_baseChange_eq (d : JacobianData C) (L : Type u) [Field L] [Algebra k L] :
    letI := d.grpObj
    Functor.grpObjObj (F := AlgebraicGeometry.baseChange k L) (G := d.J)
      = (d.baseChange L).grpObj := by
  letI := d.grpObj
  refine GrpObj.ext _ _ ?_
  refine (monObjObj_eq_ofRepresentableBy
    (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))) d.J).trans ?_
  exact monObj_ofRepresentableBy_eq_of_iso
    (Functor.isoWhiskerLeft (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).op
        (yonedaMonObjIsoOfRepresentableBy d.J
          (pic0Functor C ⋙ forget₂ CommGrpCat GrpCat ⋙ forget₂ GrpCat MonCat) d.rep)
      ≪≫ (Functor.isoWhiskerRight (pic0Theta k L C)
          (forget₂ CommGrpCat GrpCat ⋙ forget₂ GrpCat MonCat)).symm)
    ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).representableBy d.J)
    (d.baseChange L).rep
    (fun {T} g => rfl)

/-- **W7-B6b — the datum-level base-change isomorphism**: for any two Jacobian data `d` on `C` and
`dL` on `C_L = (baseChange k L).obj C`, the base-changed group scheme
`(baseChange k L).mapGrp.obj (Grp.mk d.J)` is isomorphic, as a group object over `L`, to
`Grp.mk dL.J`.  B-6a rewrites the `mapGrp` group structure to the transported datum's (via
`eqToIso`), and `Grp.mkIso` on the representing-object isomorphism
`(d.baseChange L).uniqueUpToIso dL` closes it, its `one`/`mul` compatibilities supplied by the
seam lemma
`isMonHom_hom_of_representableBy` fed with `homEquiv_uniqueUpToIso_hom`.  This is the datum-level
input consumed (definitionally, since `Jacobian C := (jacobianData C).J`) by the frozen
`AlgebraicGeometry.baseChangeIso`. -/
noncomputable def baseChangeIsoOfData (d : JacobianData C) {L : Type u} [Field L] [Algebra k L]
    (dL : JacobianData ((AlgebraicGeometry.baseChange k L).obj C)) :
    letI := d.grpObj
    letI := dL.grpObj
    (AlgebraicGeometry.baseChange k L).mapGrp.obj (.mk d.J) ≅ .mk dL.J :=
  letI := d.grpObj
  letI := dL.grpObj
  letI := (d.baseChange L).grpObj
  haveI him :
      letI := MonObj.ofRepresentableBy (d.baseChange L).J
        ((pic0Functor ((AlgebraicGeometry.baseChange k L).obj C) ⋙ forget₂ CommGrpCat GrpCat)
          ⋙ forget₂ GrpCat MonCat) (d.baseChange L).rep
      letI := MonObj.ofRepresentableBy dL.J
        ((pic0Functor ((AlgebraicGeometry.baseChange k L).obj C) ⋙ forget₂ CommGrpCat GrpCat)
          ⋙ forget₂ GrpCat MonCat) dL.rep
      IsMonHom ((d.baseChange L).uniqueUpToIso dL).hom :=
    isMonHom_hom_of_representableBy
      ((pic0Functor ((AlgebraicGeometry.baseChange k L).obj C) ⋙ forget₂ CommGrpCat GrpCat)
        ⋙ forget₂ GrpCat MonCat)
      (d.baseChange L).rep dL.rep ((d.baseChange L).uniqueUpToIso dL)
      (JacobianData.homEquiv_uniqueUpToIso_hom (d.baseChange L) dL)
  eqToIso (congrArg
      (fun gg => ({ X := (AlgebraicGeometry.baseChange k L).obj d.J, grp := gg } :
        Grp (Over (Spec (.of L)))))
      (grpObjObj_baseChange_eq d L))
    ≪≫ (Grp.mkIso ((d.baseChange L).uniqueUpToIso dL) him.one_hom him.mul_hom :
      (Grp.mk (d.baseChange L).J : Grp (Over (Spec (.of L)))) ≅ .mk dL.J)

end BaseChangeIso

end AlgebraicGeometry
