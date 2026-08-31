/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks
import AlgebraicJacobian.Descent.GluedMapData

/-!
# Gluing affine schemes from ring maps

This file packages affine ring data into `Scheme.GlueData`.  The overlap restriction
maps are the algebra maps `A i -> B i j`.  Thus an application with specified restriction
maps should install the corresponding `Algebra (A i) (B i j)` structures (for example via
`r.toRingHom.toAlgebra`) before invoking the constructor.

The only non-formal coherence assumptions are ring identities:

* each transition `tau i j : B j i -> B i j` is the identity on the diagonal;
* the triple transition `theta i j k` sends the right tensor inclusion to the left
  inclusion followed by `tau i j`;
* the three cyclic triple transitions compose to the identity.

The constructor conjugates `Spec.map theta` by Mathlib's `pullbackSpecIso`.  The face and
cocycle fields of `Scheme.GlueData` are then discharged from the displayed ring identities.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicJacobian

noncomputable section

variable {R J : Type u} [CommRing R]
variable (A : J → Type u) (B : J → J → Type u)
variable [∀ i, CommRing (A i)] [∀ i j, CommRing (B i j)]
variable [∀ i, Algebra R (A i)] [∀ i j, Algebra R (B i j)]
variable [∀ i j, Algebra (A i) (B i j)]
variable [∀ i j, IsScalarTower R (A i) (B i j)]

/-- The coordinate ring of the pullback of the two overlaps based at chart `i`. -/
abbrev AffineTripleTensor (i j k : J) : Type u :=
  B i j ⊗[A i] B i k

/-- The left overlap inclusion into an affine triple tensor, viewed over `R`. -/
def affineTensorIncludeLeft (i j k : J) :
    B i j →ₐ[R] AffineTripleTensor A B i j k :=
  (Algebra.TensorProduct.includeLeft :
    B i j →ₐ[A i] B i j ⊗[A i] B i k).restrictScalars R

/-- The right overlap inclusion into an affine triple tensor, viewed over `R`. -/
def affineTensorIncludeRight (i j k : J) :
    B i k →ₐ[R] AffineTripleTensor A B i j k :=
  (Algebra.TensorProduct.includeRight :
    B i k →ₐ[A i] B i j ⊗[A i] B i k).restrictScalars R

/-- The affine overlap inclusion induced contravariantly by `A i -> B i j`. -/
abbrev affineRestriction (i j : J) :
    Spec (CommRingCat.of (B i j)) ⟶ Spec (CommRingCat.of (A i)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (A i) (B i j)))

/-- The affine transition induced contravariantly by `tau i j : B j i -> B i j`. -/
abbrev affineTransition (tau : ∀ i j, B j i →ₐ[R] B i j) (i j : J) :
    Spec (CommRingCat.of (B i j)) ⟶ Spec (CommRingCat.of (B j i)) :=
  Spec.map (CommRingCat.ofHom (tau i j).toRingHom)

/-- The canonical affine chart for a triple pullback. -/
abbrev affineTriplePullbackIso (i j k : J) :
    pullback (affineRestriction A B i j) (affineRestriction A B i k) ≅
      Spec (CommRingCat.of (AffineTripleTensor A B i j k)) :=
  pullbackSpecIso (A i) (B i j) (B i k)

/-- A ring map between the rotated triple tensor rings, conjugated into a morphism between
the actual scheme pullbacks used by `Scheme.GlueData`. -/
def affineTripleTransition
    (theta : ∀ i j k,
      AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k)
    (i j k : J) :
    pullback (affineRestriction A B i j) (affineRestriction A B i k) ⟶
      pullback (affineRestriction A B j k) (affineRestriction A B j i) :=
  (affineTriplePullbackIso A B i j k).hom ≫
    Spec.map (CommRingCat.ofHom (theta i j k).toRingHom) ≫
      (affineTriplePullbackIso A B j k i).inv

variable (tau : ∀ i j, B j i →ₐ[R] B i j)
variable (theta : ∀ i j k,
  AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k)

/-- The right-face ring identity implies the factorization field of `Scheme.GlueData`. -/
@[reassoc]
theorem affineTripleTransition_fac
    (hfac : ∀ i j k,
      (theta i j k).comp (affineTensorIncludeRight A B j k i) =
        (affineTensorIncludeLeft A B i j k).comp (tau i j))
    (i j k : J) :
    affineTripleTransition A B theta i j k ≫
        pullback.snd (affineRestriction A B j k) (affineRestriction A B j i) =
      pullback.fst (affineRestriction A B i j) (affineRestriction A B i k) ≫
        affineTransition B tau i j := by
  have hfac' :
      CommRingCat.ofHom
          (((theta i j k).comp (affineTensorIncludeRight A B j k i)).toRingHom) =
        CommRingCat.ofHom
          (((affineTensorIncludeLeft A B i j k).comp (tau i j)).toRingHom) :=
    congrArg (fun f => CommRingCat.ofHom f.toRingHom) (hfac i j k)
  simp only [affineTripleTransition, Category.assoc]
  rw [pullbackSpecIso_inv_snd]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  change (pullbackSpecIso (A i) (B i j) (B i k)).hom ≫
      Spec.map (CommRingCat.ofHom
        (((theta i j k).comp
          (affineTensorIncludeRight A B j k i)).toRingHom)) =
      pullback.fst (affineRestriction A B i j) (affineRestriction A B i k) ≫
        affineTransition B tau i j
  rw [hfac']
  rw [show
      ((affineTensorIncludeLeft A B i j k).comp (tau i j)).toRingHom =
        (affineTensorIncludeLeft A B i j k).toRingHom.comp
          (tau i j).toRingHom by rfl]
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  change (pullbackSpecIso (A i) (B i j) (B i k)).hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          B i j →+* AffineTripleTensor A B i j k)) ≫
      Spec.map (CommRingCat.ofHom (tau i j).toRingHom) =
      pullback.fst (affineRestriction A B i j) (affineRestriction A B i k) ≫
        affineTransition B tau i j
  rw [← Category.assoc, pullbackSpecIso_hom_fst]

/-- A cyclic identity of triple-tensor ring maps implies the scheme-level cocycle. -/
theorem affineTripleTransition_cocycle
    (hcycle : ∀ i j k,
      (theta i j k).comp ((theta j k i).comp (theta k i j)) =
        AlgHom.id R (AffineTripleTensor A B i j k))
    (i j k : J) :
    affineTripleTransition A B theta i j k ≫
        affineTripleTransition A B theta j k i ≫
          affineTripleTransition A B theta k i j =
      𝟙 (pullback (affineRestriction A B i j) (affineRestriction A B i k)) := by
  have hmap :
      Spec.map (CommRingCat.ofHom (theta i j k).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (theta j k i).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (theta k i j).toRingHom) =
        𝟙 (Spec (CommRingCat.of (AffineTripleTensor A B i j k))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hcycle' :
        CommRingCat.ofHom
            (((theta i j k).comp
              ((theta j k i).comp (theta k i j))).toRingHom) =
          CommRingCat.ofHom
            ((AlgHom.id R (AffineTripleTensor A B i j k)).toRingHom) :=
      congrArg (fun f => CommRingCat.ofHom f.toRingHom) (hcycle i j k)
    change Spec.map (CommRingCat.ofHom
      (((theta i j k).comp
        ((theta j k i).comp (theta k i j))).toRingHom)) =
      𝟙 (Spec (CommRingCat.of (AffineTripleTensor A B i j k)))
    rw [hcycle']
    rw [show (AlgHom.id R (AffineTripleTensor A B i j k)).toRingHom =
      RingHom.id (AffineTripleTensor A B i j k) by rfl]
    rw [CommRingCat.ofHom_id, Spec.map_id]
  simp only [affineTripleTransition, Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hmap]
  exact Iso.hom_inv_id _

/-- A diagonal identity of overlap ring maps gives the diagonal transition identity. -/
theorem affineTransition_self
    (htau : ∀ i, tau i i = AlgHom.id R (B i i)) (i : J) :
    affineTransition B tau i i = 𝟙 (Spec (CommRingCat.of (B i i))) := by
  change Spec.map (CommRingCat.ofHom (tau i i).toRingHom) = _
  rw [htau]
  rw [show (AlgHom.id R (B i i)).toRingHom = RingHom.id (B i i) by rfl]
  rw [CommRingCat.ofHom_id, Spec.map_id]

/-- Construct `Scheme.GlueData` from affine ring charts, overlap maps, and algebraic
transition coherences.  Openness and the diagonal isomorphism remain geometric assumptions;
the transition identity, factorization, and cocycle are discharged from ring equations. -/
def affineRingGlueData
    (tau : ∀ i j, B j i →ₐ[R] B i j)
    (theta : ∀ i j k,
      AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k)
    (fId : ∀ i, IsIso (affineRestriction A B i i))
    (fOpen : ∀ i j, IsOpenImmersion (affineRestriction A B i j))
    (tauId : ∀ i, tau i i = AlgHom.id R (B i i))
    (thetaFac : ∀ i j k,
      (theta i j k).comp (affineTensorIncludeRight A B j k i) =
        (affineTensorIncludeLeft A B i j k).comp (tau i j))
    (thetaCocycle : ∀ i j k,
      (theta i j k).comp ((theta j k i).comp (theta k i j)) =
        AlgHom.id R (AffineTripleTensor A B i j k)) :
    Scheme.GlueData.{u} := by
  letI (i j : J) : IsOpenImmersion (affineRestriction A B i j) := fOpen i j
  exact
    { J := J
      U := fun i => Spec (CommRingCat.of (A i))
      V := fun p => Spec (CommRingCat.of (B p.1 p.2))
      f := affineRestriction A B
      f_id := fId
      f_open := fOpen
      t := affineTransition B tau
      t_id := affineTransition_self B tau tauId
      t' := affineTripleTransition A B theta
      t_fac := affineTripleTransition_fac A B tau theta thetaFac
      cocycle := affineTripleTransition_cocycle A B theta thetaCocycle }

/-- The algebra structure maps on the affine charts, together with their compatibility on
the overlap diagram.  Keeping this family in one record prevents callers from rebuilding a
second `Multicoequalizer.desc` against a propositionally equal glue datum. -/
noncomputable def affineRingGluedMapData
    (tau : ∀ i j, B j i →ₐ[R] B i j)
    (theta : ∀ i j k,
      AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k)
    (fId : ∀ i, IsIso (affineRestriction A B i i))
    (fOpen : ∀ i j, IsOpenImmersion (affineRestriction A B i j))
    (tauId : ∀ i, tau i i = AlgHom.id R (B i i))
    (thetaFac : ∀ i j k,
      (theta i j k).comp (affineTensorIncludeRight A B j k i) =
        (affineTensorIncludeLeft A B i j k).comp (tau i j))
    (thetaCocycle : ∀ i j k,
      (theta i j k).comp ((theta j k i).comp (theta k i j)) =
        AlgHom.id R (AffineTripleTensor A B i j k)) :
    GluedMapData
      (affineRingGlueData A B tau theta fId fOpen tauId thetaFac thetaCocycle)
      (Spec (CommRingCat.of R)) := by
  let chartMap : ∀ i : J, Spec (CommRingCat.of (A i)) ⟶
      Spec (CommRingCat.of R) := fun i =>
    Spec.map (CommRingCat.ofHom (algebraMap R (A i)))
  refine GluedMapData.ofChartMaps chartMap ?_
  intro i j
  change J at i j
  change
    Spec.map (CommRingCat.ofHom (algebraMap (A i) (B i j))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (A i))) =
      (Spec.map (CommRingCat.ofHom (tau i j).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (A j) (B j i)))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (A j)))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext r
  simp only [CommRingCat.ofHom_comp, CommRingCat.hom_comp,
    ConcreteCategory.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    AlgHom.toRingHom_eq_coe, Category.assoc, RingHom.coe_coe]
  rw [← IsScalarTower.algebraMap_apply R (A i) (B i j)]
  rw [← IsScalarTower.algebraMap_apply R (A j) (B j i)]
  exact (tau i j).commutes r |>.symm

/-- A complete affine glue presentation.  The map is stored together with the exact
`Scheme.GlueData` expression it was constructed from, so consumers do not have to
reconstruct a propositionally equal multicoequalizer map. -/
structure AffineRingGluePackage
    (tau : ∀ i j, B j i →ₐ[R] B i j)
    (theta : ∀ i j k,
      AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k)
    (fId : ∀ i, IsIso (affineRestriction A B i i))
    (fOpen : ∀ i j, IsOpenImmersion (affineRestriction A B i j))
    (tauId : ∀ i, tau i i = AlgHom.id R (B i i))
    (thetaFac : ∀ i j k,
      (theta i j k).comp (affineTensorIncludeRight A B j k i) =
        (affineTensorIncludeLeft A B i j k).comp (tau i j))
    (thetaCocycle : ∀ i j k,
      (theta i j k).comp ((theta j k i).comp (theta k i j)) =
        AlgHom.id R (AffineTripleTensor A B i j k)) where
  mapData : GluedMapData
    (affineRingGlueData A B tau theta fId fOpen tauId thetaFac thetaCocycle)
    (Spec (CommRingCat.of R))

/-- Construct the complete affine glue presentation in one elaboration scope. -/
noncomputable def affineRingGluePackage
    (tau : ∀ i j, B j i →ₐ[R] B i j)
    (theta : ∀ i j k,
      AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k)
    (fId : ∀ i, IsIso (affineRestriction A B i i))
    (fOpen : ∀ i j, IsOpenImmersion (affineRestriction A B i j))
    (tauId : ∀ i, tau i i = AlgHom.id R (B i i))
    (thetaFac : ∀ i j k,
      (theta i j k).comp (affineTensorIncludeRight A B j k i) =
        (affineTensorIncludeLeft A B i j k).comp (tau i j))
    (thetaCocycle : ∀ i j k,
      (theta i j k).comp ((theta j k i).comp (theta k i j)) =
        AlgHom.id R (AffineTripleTensor A B i j k)) :
    AffineRingGluePackage A B tau theta fId fOpen tauId thetaFac thetaCocycle :=
  ⟨affineRingGluedMapData A B tau theta fId fOpen tauId thetaFac thetaCocycle⟩

/-- The underlying structure map from the bundled affine glue/map datum. -/
def affineRingGluedMap
    (tau : ∀ i j, B j i →ₐ[R] B i j)
    (theta : ∀ i j k,
      AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k)
    (fId : ∀ i, IsIso (affineRestriction A B i i))
    (fOpen : ∀ i j, IsOpenImmersion (affineRestriction A B i j))
    (tauId : ∀ i, tau i i = AlgHom.id R (B i i))
    (thetaFac : ∀ i j k,
      (theta i j k).comp (affineTensorIncludeRight A B j k i) =
        (affineTensorIncludeLeft A B i j k).comp (tau i j))
    (thetaCocycle : ∀ i j k,
      (theta i j k).comp ((theta j k i).comp (theta k i j)) =
        AlgHom.id R (AffineTripleTensor A B i j k)) :
    (affineRingGlueData A B tau theta fId fOpen tauId thetaFac thetaCocycle).glued ⟶
      Spec (CommRingCat.of R) :=
  (affineRingGluePackage A B tau theta fId fOpen tauId thetaFac thetaCocycle).mapData.map

/-- Each affine chart inclusion lies over its canonical structure map. -/
@[reassoc]
theorem affineRingGlueData_ι_affineRingGluedMap
    (tau : ∀ i j, B j i →ₐ[R] B i j)
    (theta : ∀ i j k,
      AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k)
    (fId : ∀ i, IsIso (affineRestriction A B i i))
    (fOpen : ∀ i j, IsOpenImmersion (affineRestriction A B i j))
    (tauId : ∀ i, tau i i = AlgHom.id R (B i i))
    (thetaFac : ∀ i j k,
      (theta i j k).comp (affineTensorIncludeRight A B j k i) =
        (affineTensorIncludeLeft A B i j k).comp (tau i j))
    (thetaCocycle : ∀ i j k,
      (theta i j k).comp ((theta j k i).comp (theta k i j)) =
        AlgHom.id R (AffineTripleTensor A B i j k))
    (i : J) :
    (affineRingGlueData A B tau theta fId fOpen tauId thetaFac thetaCocycle).ι i ≫
        affineRingGluedMap A B tau theta fId fOpen tauId thetaFac thetaCocycle =
      Spec.map (CommRingCat.ofHom (algebraMap R (A i))) :=
  (affineRingGluePackage A B tau theta fId fOpen tauId thetaFac thetaCocycle).mapData.chartMap_factor i

/-- The scheme obtained by gluing affine `R`-algebras, retained as an object over
`Spec R`. -/
def affineRingGluedOver
    (tau : ∀ i j, B j i →ₐ[R] B i j)
    (theta : ∀ i j k,
      AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k)
    (fId : ∀ i, IsIso (affineRestriction A B i i))
    (fOpen : ∀ i j, IsOpenImmersion (affineRestriction A B i j))
    (tauId : ∀ i, tau i i = AlgHom.id R (B i i))
    (thetaFac : ∀ i j k,
      (theta i j k).comp (affineTensorIncludeRight A B j k i) =
        (affineTensorIncludeLeft A B i j k).comp (tau i j))
    (thetaCocycle : ∀ i j k,
      (theta i j k).comp ((theta j k i).comp (theta k i j)) =
        AlgHom.id R (AffineTripleTensor A B i j k)) :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (affineRingGluedMap A B tau theta fId fOpen tauId thetaFac thetaCocycle)

/-! ## Pinned presentation boundary

The historical `AffineRingGluePackage` stores only its map datum.  Consequently every
projection has to elaborate the full `affineRingGlueData ...` expression again.  The
presentation below retains the selected `Scheme.GlueData` and its map as one value.  It is
additive: the older package and projections remain available for clients that have not yet
migrated, while new clients can carry this value without reopening the gluing construction.
-/

/-- A chosen affine gluing and its structure map to the base scheme.

The glue datum is a field rather than a repeated constructor in the type of `mapData`.  This
is the important distinction for dependent consumers: changing a proof argument used to build
the gluing no longer changes the type of every projection in a client file.
-/
structure AffineRingGluePresentation (R : Type u) [CommRing R] where
  glueData : Scheme.GlueData.{u}
  mapData : GluedMapData glueData (Spec (CommRingCat.of R))

namespace AffineRingGluePresentation

/-! The constructor below is deliberately data-first.  Once a producer has selected its
`Scheme.GlueData` and map datum, later consumers no longer mention the proof arguments that
were used to construct them. -/

/-- Package an already selected glue datum and map without re-elaborating the gluing proof. -/
def ofData {R : Type u} [CommRing R]
    (D : Scheme.GlueData.{u})
    (M : GluedMapData D (Spec (CommRingCat.of R))) :
    AffineRingGluePresentation R :=
  { glueData := D, mapData := M }

/-- Package map data while inferring its glue datum from the dependent index.

This is the preferred adapter for an existing `GluedMapData`: it does not reconstruct the
proof-sensitive `Scheme.GlueData` term already fixed by the type of `M`.
-/
def ofMapData {R : Type u} [CommRing R]
    {D : Scheme.GlueData.{u}}
    (M : GluedMapData D (Spec (CommRingCat.of R))) :
    AffineRingGluePresentation R :=
  { glueData := D, mapData := M }

@[simp]
theorem ofData_glueData {R : Type u} [CommRing R]
    (D : Scheme.GlueData.{u})
    (M : GluedMapData D (Spec (CommRingCat.of R))) :
    (ofData D M).glueData = D :=
  rfl

@[simp]
theorem ofData_mapData {R : Type u} [CommRing R]
    (D : Scheme.GlueData.{u})
    (M : GluedMapData D (Spec (CommRingCat.of R))) :
    (ofData D M).mapData = M :=
  rfl

@[simp]
theorem ofMapData_glueData {R : Type u} [CommRing R]
    {D : Scheme.GlueData.{u}}
    (M : GluedMapData D (Spec (CommRingCat.of R))) :
    (ofMapData M).glueData = D :=
  rfl

@[simp]
theorem ofMapData_mapData {R : Type u} [CommRing R]
    {D : Scheme.GlueData.{u}}
    (M : GluedMapData D (Spec (CommRingCat.of R))) :
    (ofMapData M).mapData = M :=
  rfl

/-- The selected glued scheme. -/
abbrev glued (P : AffineRingGluePresentation R) : Scheme.{u} := P.glueData.glued

/-- The selected structure map from the glued scheme to `Spec R`. -/
abbrev map (P : AffineRingGluePresentation R) : P.glueData.glued ⟶
    Spec (CommRingCat.of R) := P.mapData.map

@[simp]
theorem chartMap_factor (P : AffineRingGluePresentation R) (i : P.glueData.J) :
    P.glueData.ι i ≫ P.map = P.mapData.chartMap i :=
  P.mapData.chartMap_factor i

/-- Repackage a presentation as an `Over` object without reconstructing its map. -/
abbrev over (P : AffineRingGluePresentation R) : Over (Spec (CommRingCat.of R)) :=
  Over.mk P.map

end AffineRingGluePresentation

namespace AffineRingGluePackage

/-! Upgrade the legacy map-only package to the pinned presentation API. -/
noncomputable def toPresentation
    (tau : ∀ i j, B j i →ₐ[R] B i j)
    (theta : ∀ i j k,
      AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k)
    (fId : ∀ i, IsIso (affineRestriction A B i i))
    (fOpen : ∀ i j, IsOpenImmersion (affineRestriction A B i j))
    (tauId : ∀ i, tau i i = AlgHom.id R (B i i))
    (thetaFac : ∀ i j k,
      (theta i j k).comp (affineTensorIncludeRight A B j k i) =
        (affineTensorIncludeLeft A B i j k).comp (tau i j))
    (thetaCocycle : ∀ i j k,
      (theta i j k).comp ((theta j k i).comp (theta k i j)) =
        AlgHom.id R (AffineTripleTensor A B i j k))
    (P : AffineRingGluePackage A B tau theta fId fOpen tauId thetaFac thetaCocycle) :
    AffineRingGluePresentation R :=
  AffineRingGluePresentation.ofMapData P.mapData

/-! The explicit-argument adapter above is retained for source compatibility.  `pin` is the
consumer-facing projection: all legacy parameters are inferred from one package value, while
the result has the proof-independent `AffineRingGluePresentation` type. -/

/-- Pin a legacy package once at the stable presentation boundary. -/
noncomputable def pin
    {A : J → Type u} {B : J → J → Type u}
    [∀ i, CommRing (A i)] [∀ i j, CommRing (B i j)]
    [∀ i, Algebra R (A i)] [∀ i j, Algebra R (B i j)]
    [∀ i j, Algebra (A i) (B i j)]
    [∀ i j, IsScalarTower R (A i) (B i j)]
    {tau : ∀ i j, B j i →ₐ[R] B i j}
    {theta : ∀ i j k,
      AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k}
    {fId : ∀ i, IsIso (affineRestriction A B i i)}
    {fOpen : ∀ i j, IsOpenImmersion (affineRestriction A B i j)}
    {tauId : ∀ i, tau i i = AlgHom.id R (B i i)}
    {thetaFac : ∀ i j k,
      (theta i j k).comp (affineTensorIncludeRight A B j k i) =
        (affineTensorIncludeLeft A B i j k).comp (tau i j)}
    {thetaCocycle : ∀ i j k,
      (theta i j k).comp ((theta j k i).comp (theta k i j)) =
        AlgHom.id R (AffineTripleTensor A B i j k)}
    (P : AffineRingGluePackage A B tau theta fId fOpen tauId thetaFac thetaCocycle) :
    AffineRingGluePresentation R :=
  AffineRingGluePresentation.ofMapData P.mapData

@[simp]
theorem pin_mapData
    {A : J → Type u} {B : J → J → Type u}
    [∀ i, CommRing (A i)] [∀ i j, CommRing (B i j)]
    [∀ i, Algebra R (A i)] [∀ i j, Algebra R (B i j)]
    [∀ i j, Algebra (A i) (B i j)]
    [∀ i j, IsScalarTower R (A i) (B i j)]
    {tau : ∀ i j, B j i →ₐ[R] B i j}
    {theta : ∀ i j k,
      AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k}
    {fId : ∀ i, IsIso (affineRestriction A B i i)}
    {fOpen : ∀ i j, IsOpenImmersion (affineRestriction A B i j)}
    {tauId : ∀ i, tau i i = AlgHom.id R (B i i)}
    {thetaFac : ∀ i j k,
      (theta i j k).comp (affineTensorIncludeRight A B j k i) =
        (affineTensorIncludeLeft A B i j k).comp (tau i j)}
    {thetaCocycle : ∀ i j k,
      (theta i j k).comp ((theta j k i).comp (theta k i j)) =
        AlgHom.id R (AffineTripleTensor A B i j k)}
    (P : AffineRingGluePackage A B tau theta fId fOpen tauId thetaFac thetaCocycle) :
    (P.pin).mapData = P.mapData :=
  rfl

@[simp]
theorem toPresentation_glueData
    (tau : ∀ i j, B j i →ₐ[R] B i j)
    (theta : ∀ i j k,
      AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k)
    (fId : ∀ i, IsIso (affineRestriction A B i i))
    (fOpen : ∀ i j, IsOpenImmersion (affineRestriction A B i j))
    (tauId : ∀ i, tau i i = AlgHom.id R (B i i))
    (thetaFac : ∀ i j k,
      (theta i j k).comp (affineTensorIncludeRight A B j k i) =
        (affineTensorIncludeLeft A B i j k).comp (tau i j))
    (thetaCocycle : ∀ i j k,
      (theta i j k).comp ((theta j k i).comp (theta k i j)) =
        AlgHom.id R (AffineTripleTensor A B i j k))
    (P : AffineRingGluePackage A B tau theta fId fOpen tauId thetaFac thetaCocycle) :
    (toPresentation A B tau theta fId fOpen tauId thetaFac thetaCocycle P).glueData =
      affineRingGlueData A B tau theta fId fOpen tauId thetaFac thetaCocycle :=
  rfl

@[simp]
theorem toPresentation_mapData
    (tau : ∀ i j, B j i →ₐ[R] B i j)
    (theta : ∀ i j k,
      AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k)
    (fId : ∀ i, IsIso (affineRestriction A B i i))
    (fOpen : ∀ i j, IsOpenImmersion (affineRestriction A B i j))
    (tauId : ∀ i, tau i i = AlgHom.id R (B i i))
    (thetaFac : ∀ i j k,
      (theta i j k).comp (affineTensorIncludeRight A B j k i) =
        (affineTensorIncludeLeft A B i j k).comp (tau i j))
    (thetaCocycle : ∀ i j k,
      (theta i j k).comp ((theta j k i).comp (theta k i j)) =
        AlgHom.id R (AffineTripleTensor A B i j k))
    (P : AffineRingGluePackage A B tau theta fId fOpen tauId thetaFac thetaCocycle) :
    (toPresentation A B tau theta fId fOpen tauId thetaFac thetaCocycle P).mapData = P.mapData :=
  rfl

end AffineRingGluePackage

/-- Build a pinned presentation from affine ring charts and the coherence certificates. -/
noncomputable def affineRingGluePresentation
    (A : J → Type u) (B : J → J → Type u)
    [∀ i, CommRing (A i)] [∀ i j, CommRing (B i j)]
    [∀ i, Algebra R (A i)] [∀ i j, Algebra R (B i j)]
    [∀ i j, Algebra (A i) (B i j)]
    [∀ i j, IsScalarTower R (A i) (B i j)]
    (tau : ∀ i j, B j i →ₐ[R] B i j)
    (theta : ∀ i j k,
      AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k)
    (fId : ∀ i, IsIso (affineRestriction A B i i))
    (fOpen : ∀ i j, IsOpenImmersion (affineRestriction A B i j))
    (tauId : ∀ i, tau i i = AlgHom.id R (B i i))
    (thetaFac : ∀ i j k,
      (theta i j k).comp (affineTensorIncludeRight A B j k i) =
        (affineTensorIncludeLeft A B i j k).comp (tau i j))
    (thetaCocycle : ∀ i j k,
      (theta i j k).comp ((theta j k i).comp (theta k i j)) =
        AlgHom.id R (AffineTripleTensor A B i j k)) :
    AffineRingGluePresentation R := by
  let D := affineRingGlueData A B tau theta fId fOpen tauId thetaFac thetaCocycle
  exact
    { glueData := D
      mapData := by
        simpa only [D] using
          (affineRingGluedMapData A B tau theta fId fOpen tauId thetaFac thetaCocycle) }

@[simp]
theorem affineRingGluePresentation_glueData
    (A : J → Type u) (B : J → J → Type u)
    [∀ i, CommRing (A i)] [∀ i j, CommRing (B i j)]
    [∀ i, Algebra R (A i)] [∀ i j, Algebra R (B i j)]
    [∀ i j, Algebra (A i) (B i j)]
    [∀ i j, IsScalarTower R (A i) (B i j)]
    (tau : ∀ i j, B j i →ₐ[R] B i j)
    (theta : ∀ i j k,
      AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k)
    (fId : ∀ i, IsIso (affineRestriction A B i i))
    (fOpen : ∀ i j, IsOpenImmersion (affineRestriction A B i j))
    (tauId : ∀ i, tau i i = AlgHom.id R (B i i))
    (thetaFac : ∀ i j k,
      (theta i j k).comp (affineTensorIncludeRight A B j k i) =
        (affineTensorIncludeLeft A B i j k).comp (tau i j))
    (thetaCocycle : ∀ i j k,
      (theta i j k).comp ((theta j k i).comp (theta k i j)) =
        AlgHom.id R (AffineTripleTensor A B i j k)) :
    (affineRingGluePresentation A B tau theta fId fOpen tauId thetaFac thetaCocycle).glueData =
      affineRingGlueData A B tau theta fId fOpen tauId thetaFac thetaCocycle :=
  rfl

@[simp]
theorem affineRingGluePresentation_mapData
    (A : J → Type u) (B : J → J → Type u)
    [∀ i, CommRing (A i)] [∀ i j, CommRing (B i j)]
    [∀ i, Algebra R (A i)] [∀ i j, Algebra R (B i j)]
    [∀ i j, Algebra (A i) (B i j)]
    [∀ i j, IsScalarTower R (A i) (B i j)]
    (tau : ∀ i j, B j i →ₐ[R] B i j)
    (theta : ∀ i j k,
      AffineTripleTensor A B j k i →ₐ[R] AffineTripleTensor A B i j k)
    (fId : ∀ i, IsIso (affineRestriction A B i i))
    (fOpen : ∀ i j, IsOpenImmersion (affineRestriction A B i j))
    (tauId : ∀ i, tau i i = AlgHom.id R (B i i))
    (thetaFac : ∀ i j k,
      (theta i j k).comp (affineTensorIncludeRight A B j k i) =
        (affineTensorIncludeLeft A B i j k).comp (tau i j))
    (thetaCocycle : ∀ i j k,
      (theta i j k).comp ((theta j k i).comp (theta k i j)) =
        AlgHom.id R (AffineTripleTensor A B i j k)) :
    (affineRingGluePresentation A B tau theta fId fOpen tauId thetaFac thetaCocycle).mapData =
      affineRingGluedMapData A B tau theta fId fOpen tauId thetaFac thetaCocycle := by
  rfl

end

end AlgebraicJacobian
