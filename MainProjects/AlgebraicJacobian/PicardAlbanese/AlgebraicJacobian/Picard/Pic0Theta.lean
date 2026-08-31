/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.CrossBaseSquare
import AlgebraicJacobian.RiemannRoch.ClassDegMapIso
import AlgebraicJacobian.Picard.Pic0Functor

/-!
# W7-B4a: field-point matching and the same-`K` degree comparison (θ groundwork)

Wave-7 brick B-4a (`informal/w7-worksheet.md` §D2 row W7-B4a): the two ingredients of the
degree-zero restriction of the base-field comparison θ (B-4b) that are independent of the
étale-plus shuffle (B-2).  Throughout, `k → L` is a field embedding,
`σ = Spec.map (algebraMap k L)`, `C_L = (baseChange k L).obj C`.

**1. The same-carrier comparison and its degree invariance.**  For a test algebra `A` in
a scalar tower `k → L → A`, B-1's `crossBaseIso` at `T = overSpec L A` composed with the
whiskered affine matching `mapOverSpecIso` gives `crossBaseAffineIso :
(C_L ⊗_L overSpec L A).left ≅ (C ⊗_k overSpec k A).left`, commuting with the second
projections (`crossBaseAffineIso_hom_snd`) and natural in `A` against `Over.overSpecMap`
(`crossBaseAffineIso_naturality`).  It descends to the relative Picard groups
(`relPicCrossBase`/`relPicCrossBaseEquiv`, with the `relPicAlgMap` square — the relPic
layer of the B-2 shuffle).  At a *field* `K` in the tower, both sides carry the
`Curve/BaseChangeInstances` snd-structure over `Spec K`, so B-3's engine applies:
`classDeg_cechPicMap_crossBaseAffineIso` and the **keystone
`relPicDeg_relPicCrossBase`** — `relPicDeg K` reads the same integer on the two
presentations of the fiber.  Per the deg-d5b D1 discipline this is the *only* licensed
cross-presentation degree seam: B-4b degree facts route through it and E-iv-alg.

**2. Field-point matching (the R5 brick).**  `k`-field-points of the pushed-forward test
`(Over.map σ).obj T` correspond to `L`-field-points of `T` plus the scalar-tower
structure: `pushFieldPoint` (pack, through `mapOverSpecIso`);
`fieldPointAlgebra`/`isScalarTower_fieldPointAlgebra`/`liftFieldPoint` (unpack, via
`Spec.preimage` of `t.left ≫ T.hom`); round trips with no heterogeneous equality
anywhere — the quantifier trap (recon risk R5) is dodged by quantifying over both
algebra structures plus the tower.  Consumable forms for B-4b's degree-zero restriction:
`mem_pic0Subgroup_iff_forall_pushFieldPoint` (the quantifier exchange) and the
**keystone `mem_pic0Subgroup_iff_of_degAt_pushFieldPoint_eq`** — classes matching in
degree at all pushed field-point pairs are simultaneously degree-zero, so θ's
restriction to `pic0Subgroup` reduces to the `degAt` matching that B-2 plus the degree
seam supply.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry.Scheme (CechPic)

namespace AlgebraicGeometry

/-! ## The same-`K` comparison isomorphism at affine tests -/

section CrossBaseAffine

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
variable (C : Over (Spec (.of k)))
variable (A : Type u) [CommRing A] [Algebra k A] [Algebra L A] [IsScalarTower k L A]

/-- **The same-carrier comparison at an affine test in the tower `k → L → A`**: the
base-changed curve tensored (over `L`) with `Spec A` is the original curve tensored
(over `k`) with `Spec A` — B-1's cross-base square `crossBaseIso` at `T = overSpec L A`,
composed with the whiskering of the affine matching `mapOverSpecIso`. -/
noncomputable def crossBaseAffineIso :
    (((baseChange k L).obj C) ⊗ overSpec L A).left ≅ (C ⊗ overSpec k A).left :=
  crossBaseIso k L C (overSpec L A) ≪≫
    (Over.forget (Spec (.of k))).mapIso (whiskerLeftIso C (mapOverSpecIso k L A))

/-- The `hom` of the same-carrier comparison, unfolded (each factor is definitional). -/
lemma crossBaseAffineIso_hom :
    (crossBaseAffineIso k L C A).hom
      = (crossBaseIso k L C (overSpec L A)).hom
          ≫ (C ◁ (mapOverSpecIso k L A).hom).left :=
  rfl

/-- **The same-carrier comparison commutes with the second projections**: it is a
morphism of curve bundles over `Spec A` (in particular, over `Spec K` at a field test,
which is what feeds B-3's degree engine). -/
@[reassoc (attr := simp)]
lemma crossBaseAffineIso_hom_snd :
    (crossBaseAffineIso k L C A).hom ≫ (snd C (overSpec k A)).left
      = (snd ((baseChange k L).obj C) (overSpec L A)).left := by
  have h1 : (C ◁ (mapOverSpecIso k L A).hom).left ≫ (snd C (overSpec k A)).left
      = (snd C ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj
          (overSpec L A))).left ≫ (mapOverSpecIso k L A).hom.left := by
    rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  rw [crossBaseAffineIso_hom, Category.assoc, h1]
  exact (Over.crossBaseIso_hom_snd_assoc
    (Spec.map (CommRingCat.ofHom (algebraMap k L))) C (overSpec L A)
    ((mapOverSpecIso k L A).hom.left)).trans (Category.comp_id _)

/-- The inverse of the same-carrier comparison commutes with the second projections. -/
@[reassoc (attr := simp)]
lemma crossBaseAffineIso_inv_snd :
    (crossBaseAffineIso k L C A).inv
        ≫ (snd ((baseChange k L).obj C) (overSpec L A)).left
      = (snd C (overSpec k A)).left :=
  (Iso.inv_comp_eq _).mpr (crossBaseAffineIso_hom_snd k L C A).symm

/-- **Naturality of the same-carrier comparison in the test algebra**: for an `L`-algebra
map `f : A →ₐ[L] B` in towers over `k`, the comparisons intertwine `Spec f` whiskered on
the two sides (`Over.overSpecMap` of `f` over `L`, resp. of its scalar restriction over
`k`). -/
theorem crossBaseAffineIso_naturality (B : Type u) [CommRing B] [Algebra k B]
    [Algebra L B] [IsScalarTower k L B] (f : A →ₐ[L] B) :
    (crossBaseAffineIso k L C B).hom
        ≫ (C ◁ Over.overSpecMap (f.restrictScalars k)).left
      = (((baseChange k L).obj C) ◁ Over.overSpecMap f).left
          ≫ (crossBaseAffineIso k L C A).hom := by
  have hsq : (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map
        (Over.overSpecMap f) ≫ (mapOverSpecIso k L A).hom
      = (mapOverSpecIso k L B).hom ≫ Over.overSpecMap (f.restrictScalars k) := by
    refine Over.OverMorphism.ext ?_
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  have hwhisker : (C ◁ (mapOverSpecIso k L B).hom).left
        ≫ (C ◁ Over.overSpecMap (f.restrictScalars k)).left
      = (C ◁ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map
            (Over.overSpecMap f)).left
          ≫ (C ◁ (mapOverSpecIso k L A).hom).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, hsq]
  rw [crossBaseAffineIso_hom, crossBaseAffineIso_hom, Category.assoc, hwhisker,
    ← Category.assoc, ← crossBaseIso_naturality k L C (Over.overSpecMap f),
    Category.assoc]

/-! ### Descent to the relative Picard groups -/

/-- Transport along the same-carrier comparison sends classes pulled back from `Spec A`
(over `k`) to classes pulled back from `Spec A` (over `L`): well-definedness of
`relPicCrossBase` on the `picFromBase` cosets. -/
lemma picFromBase_le_comap_crossBaseAffineIso :
    picFromBase C (overSpec k A)
      ≤ (picFromBase ((baseChange k L).obj C) (overSpec L A)).comap
          (CechPic.map (crossBaseAffineIso k L C A).hom) := by
  rintro _ ⟨N, rfl⟩
  refine ⟨N, ?_⟩
  show CechPic.map (snd ((baseChange k L).obj C) (overSpec L A)).left N
      = CechPic.map (crossBaseAffineIso k L C A).hom
          (CechPic.map (snd C (overSpec k A)).left N)
  calc CechPic.map (snd ((baseChange k L).obj C) (overSpec L A)).left N
      = CechPic.map ((crossBaseAffineIso k L C A).hom ≫ (snd C (overSpec k A)).left) N :=
        congrArg (fun φ => CechPic.map φ N) (crossBaseAffineIso_hom_snd k L C A).symm
    _ = CechPic.map (crossBaseAffineIso k L C A).hom
          (CechPic.map (snd C (overSpec k A)).left N) := by
        rw [Scheme.CechPic.map_comp]; rfl

/-- Transport along the inverse comparison sends classes pulled back from `Spec A`
(over `L`) to classes pulled back from `Spec A` (over `k`). -/
lemma picFromBase_le_comap_crossBaseAffineIso_inv :
    picFromBase ((baseChange k L).obj C) (overSpec L A)
      ≤ (picFromBase C (overSpec k A)).comap
          (CechPic.map (crossBaseAffineIso k L C A).inv) := by
  rintro _ ⟨N, rfl⟩
  refine ⟨N, ?_⟩
  show CechPic.map (snd C (overSpec k A)).left N
      = CechPic.map (crossBaseAffineIso k L C A).inv
          (CechPic.map (snd ((baseChange k L).obj C) (overSpec L A)).left N)
  calc CechPic.map (snd C (overSpec k A)).left N
      = CechPic.map ((crossBaseAffineIso k L C A).inv
          ≫ (snd ((baseChange k L).obj C) (overSpec L A)).left) N :=
        congrArg (fun φ => CechPic.map φ N) (crossBaseAffineIso_inv_snd k L C A).symm
    _ = CechPic.map (crossBaseAffineIso k L C A).inv
          (CechPic.map (snd ((baseChange k L).obj C) (overSpec L A)).left N) := by
        rw [Scheme.CechPic.map_comp]; rfl

/-- **The relPic-level base-field shuffle at an affine test** (the relPic layer of the
B-2 comparison): transport of relative Picard classes along the same-carrier comparison,
`relPic C (overSpec k A) →* relPic C_L (overSpec L A)`. -/
noncomputable def relPicCrossBase :
    relPic C (overSpec k A) →* relPic ((baseChange k L).obj C) (overSpec L A) :=
  QuotientGroup.map _ _ (CechPic.map (crossBaseAffineIso k L C A).hom)
    (picFromBase_le_comap_crossBaseAffineIso k L C A)

@[simp]
lemma relPicCrossBase_mk (Λ : (C ⊗ overSpec k A).left.CechPic) :
    relPicCrossBase k L C A (relPicMk C (overSpec k A) Λ)
      = relPicMk ((baseChange k L).obj C) (overSpec L A)
          (CechPic.map (crossBaseAffineIso k L C A).hom Λ) :=
  QuotientGroup.map_mk' _ _ _ _ Λ

/-- The inverse relPic-level shuffle, along the inverse comparison. -/
noncomputable def relPicCrossBaseInv :
    relPic ((baseChange k L).obj C) (overSpec L A) →* relPic C (overSpec k A) :=
  QuotientGroup.map _ _ (CechPic.map (crossBaseAffineIso k L C A).inv)
    (picFromBase_le_comap_crossBaseAffineIso_inv k L C A)

@[simp]
lemma relPicCrossBaseInv_mk
    (Λ : (((baseChange k L).obj C) ⊗ overSpec L A).left.CechPic) :
    relPicCrossBaseInv k L C A (relPicMk ((baseChange k L).obj C) (overSpec L A) Λ)
      = relPicMk C (overSpec k A) (CechPic.map (crossBaseAffineIso k L C A).inv Λ) :=
  QuotientGroup.map_mk' _ _ _ _ Λ

/-- **The relPic-level base-field shuffle is an isomorphism** — the two-sided form that
the B-2 étale-plus shuffle instantiates cover-wise. -/
noncomputable def relPicCrossBaseEquiv :
    relPic C (overSpec k A) ≃* relPic ((baseChange k L).obj C) (overSpec L A) where
  toFun := relPicCrossBase k L C A
  invFun := relPicCrossBaseInv k L C A
  left_inv x := by
    induction x using relPic.ind with
    | mk Λ =>
      rw [relPicCrossBase_mk, relPicCrossBaseInv_mk]
      refine congrArg (relPicMk C (overSpec k A)) ?_
      calc CechPic.map (crossBaseAffineIso k L C A).inv
            (CechPic.map (crossBaseAffineIso k L C A).hom Λ)
          = CechPic.map ((crossBaseAffineIso k L C A).inv
              ≫ (crossBaseAffineIso k L C A).hom) Λ := by
            rw [Scheme.CechPic.map_comp]; rfl
        _ = CechPic.map (𝟙 ((C ⊗ overSpec k A).left)) Λ := by rw [Iso.inv_hom_id]
        _ = Λ := by
            rw [Scheme.CechPic.map_id]; rfl
  right_inv x := by
    induction x using relPic.ind with
    | mk Λ =>
      rw [relPicCrossBaseInv_mk, relPicCrossBase_mk]
      refine congrArg (relPicMk ((baseChange k L).obj C) (overSpec L A)) ?_
      calc CechPic.map (crossBaseAffineIso k L C A).hom
            (CechPic.map (crossBaseAffineIso k L C A).inv Λ)
          = CechPic.map ((crossBaseAffineIso k L C A).hom
              ≫ (crossBaseAffineIso k L C A).inv) Λ := by
            rw [Scheme.CechPic.map_comp]; rfl
        _ = CechPic.map (𝟙 ((((baseChange k L).obj C) ⊗ overSpec L A).left)) Λ := by
            rw [Iso.hom_inv_id]
        _ = Λ := by
            rw [Scheme.CechPic.map_id]; rfl
  map_mul' := map_mul (relPicCrossBase k L C A)

@[simp]
lemma relPicCrossBaseEquiv_apply (x : relPic C (overSpec k A)) :
    relPicCrossBaseEquiv k L C A x = relPicCrossBase k L C A x :=
  rfl

@[simp]
lemma relPicCrossBaseEquiv_symm_apply
    (y : relPic ((baseChange k L).obj C) (overSpec L A)) :
    (relPicCrossBaseEquiv k L C A).symm y = relPicCrossBaseInv k L C A y :=
  rfl

/-- **Naturality of the relPic-level shuffle in the test algebra** against the
restriction maps `relPicAlgMap`: for `f : A →ₐ[L] B` in towers over `k`, restricting then
shuffling is shuffling then restricting.  This is the square the B-2 étale-plus shuffle
transports through `mk`/`descentMap`. -/
theorem relPicCrossBase_relPicAlgMap (B : Type u) [CommRing B] [Algebra k B]
    [Algebra L B] [IsScalarTower k L B] (f : A →ₐ[L] B) (x : relPic C (overSpec k A)) :
    relPicCrossBase k L C B (relPicAlgMap C (f.restrictScalars k) x)
      = relPicAlgMap ((baseChange k L).obj C) f (relPicCrossBase k L C A x) := by
  induction x using relPic.ind with
  | mk Λ =>
    have h1 : relPicAlgMap C (f.restrictScalars k) (relPicMk C (overSpec k A) Λ)
        = relPicMk C (overSpec k B)
            (CechPic.map ((C ◁ Over.overSpecMap (f.restrictScalars k)).left) Λ) :=
      relPicMap_mk C (Over.overSpecMap (f.restrictScalars k)) Λ
    have h2 : relPicAlgMap ((baseChange k L).obj C) f
          (relPicMk ((baseChange k L).obj C) (overSpec L A)
            (CechPic.map (crossBaseAffineIso k L C A).hom Λ))
        = relPicMk ((baseChange k L).obj C) (overSpec L B)
            (CechPic.map ((((baseChange k L).obj C) ◁ Over.overSpecMap f).left)
              (CechPic.map (crossBaseAffineIso k L C A).hom Λ)) :=
      relPicMap_mk ((baseChange k L).obj C) (Over.overSpecMap f) _
    rw [h1, relPicCrossBase_mk, relPicCrossBase_mk, h2]
    refine congrArg (relPicMk ((baseChange k L).obj C) (overSpec L B)) ?_
    calc CechPic.map (crossBaseAffineIso k L C B).hom
          (CechPic.map ((C ◁ Over.overSpecMap (f.restrictScalars k)).left) Λ)
        = CechPic.map ((crossBaseAffineIso k L C B).hom
            ≫ (C ◁ Over.overSpecMap (f.restrictScalars k)).left) Λ := by
          rw [Scheme.CechPic.map_comp]; rfl
      _ = CechPic.map ((((baseChange k L).obj C) ◁ Over.overSpecMap f).left
            ≫ (crossBaseAffineIso k L C A).hom) Λ := by
          rw [crossBaseAffineIso_naturality k L C A B f]
      _ = CechPic.map ((((baseChange k L).obj C) ◁ Over.overSpecMap f).left)
            (CechPic.map (crossBaseAffineIso k L C A).hom Λ) := by
          rw [Scheme.CechPic.map_comp]; rfl

end CrossBaseAffine

/-! ## The degree matching through B-3 -/

section DegreeMatching

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
variable (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable (K : Type u) [Field K] [Algebra k K] [Algebra L K] [IsScalarTower k L K]

/-- **Degree invariance along the same-carrier comparison** (B-3 fed with B-1): at a
field test `K` in the tower `k → L → K`, both fibers carry the `BaseChangeInstances`
snd-structure over `Spec K`, the comparison is an isomorphism over `Spec K`
(`crossBaseAffineIso_hom_snd`), and B-3's engine `classDeg_cechPicMap_of_isIso` gives
invariance of `classDeg K` under the transport. -/
theorem classDeg_cechPicMap_crossBaseAffineIso (Λ : (C ⊗ overSpec k K).left.CechPic) :
    classDeg K (CechPic.map (crossBaseAffineIso k L C K).hom Λ) = classDeg K Λ :=
  classDeg_cechPicMap_of_isIso K (crossBaseAffineIso k L C K).hom
    (crossBaseAffineIso_hom_snd k L C K) Λ

/-- **W7-B4a degree-matching keystone**: the relative degree over `K` is invariant under
the relPic-level base-field shuffle — a relative Picard class of the `k`-curve at the
test `K` and its shuffled presentation on the `L`-curve read the same integer.  This is
the degree seam through which the B-2/B-4b `degAt` matching routes (deg-d5b D1: through
B-3 + E-iv-alg only). -/
theorem relPicDeg_relPicCrossBase (x : relPic C (overSpec k K)) :
    relPicDeg K (relPicCrossBase k L C K x) = relPicDeg K x := by
  induction x using relPic.ind with
  | mk Λ =>
    rw [relPicCrossBase_mk, relPicDeg_relPicMk, relPicDeg_relPicMk,
      classDeg_cechPicMap_crossBaseAffineIso]

end DegreeMatching

/-! ## Field-point matching (the R5 brick) -/

section FieldPoint

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable {T : Over (Spec (.of L))} {K : Type u} [Field K]

variable (k) in
/-- **Pack direction of the field-point matching**: an `L`-field-point of `T` in a scalar
tower `k → L → K` pushes forward to a `k`-field-point of `(Over.map σ).obj T`, through
the affine matching `mapOverSpecIso`. -/
noncomputable def pushFieldPoint [Algebra k K] [Algebra L K] [IsScalarTower k L K]
    (s : overSpec L K ⟶ T) :
    overSpec k K ⟶ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T :=
  (mapOverSpecIso k L K).inv
    ≫ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map s

@[simp]
lemma pushFieldPoint_left [Algebra k K] [Algebra L K] [IsScalarTower k L K]
    (s : overSpec L K ⟶ T) :
    (pushFieldPoint k s).left = s.left :=
  Category.id_comp s.left

/-- **Unpack direction, the algebra structure**: a `k`-field-point
`t : overSpec k K ⟶ (Over.map σ).obj T` makes `K` an `L`-algebra, via `Spec.preimage` of
the composite `Spec K ⟶ T.left ⟶ Spec L`. -/
@[reducible]
noncomputable def fieldPointAlgebra [Algebra k K]
    (t : overSpec k K
      ⟶ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) :
    Algebra L K :=
  ((Spec.preimage (t.left ≫ T.hom)).hom).toAlgebra

/-- The algebra map of the unpacked `L`-algebra structure is the `Spec.preimage` of the
composite point (definitional anchor). -/
lemma fieldPointAlgebra_algebraMap [Algebra k K]
    (t : overSpec k K
      ⟶ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) :
    letI := fieldPointAlgebra t
    algebraMap L K = (Spec.preimage (t.left ≫ T.hom)).hom :=
  rfl

/-- **Unpack direction, the tower**: the unpacked `L`-algebra structure on `K` is
compatible with the given `k`-structures — `Spec` of the tower identity is the
`Over`-triangle of `t`. -/
theorem isScalarTower_fieldPointAlgebra [Algebra k K]
    (t : overSpec k K
      ⟶ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) :
    letI := fieldPointAlgebra t
    IsScalarTower k L K := by
  letI := fieldPointAlgebra t
  refine IsScalarTower.of_algebraMap_eq' ?_
  have hw : Spec.map (CommRingCat.ofHom (algebraMap k L)
        ≫ Spec.preimage (t.left ≫ T.hom))
      = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [Spec.map_comp, Spec.map_preimage, Category.assoc]
    exact Over.w t
  have hring := congrArg CommRingCat.Hom.hom (Spec.map_injective hw)
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at hring
  exact hring.symm

/-- **Unpack direction, the point**: a `k`-field-point of `(Over.map σ).obj T` is an
`L`-field-point of `T` on the same carrier morphism, over the unpacked `L`-algebra
structure. -/
noncomputable def liftFieldPoint [Algebra k K]
    (t : overSpec k K
      ⟶ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) :
    letI := fieldPointAlgebra t
    overSpec L K ⟶ T :=
  letI := fieldPointAlgebra t
  Over.homMk t.left (Spec.map_preimage (t.left ≫ T.hom)).symm

@[simp]
lemma liftFieldPoint_left [Algebra k K]
    (t : overSpec k K
      ⟶ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) :
    (liftFieldPoint t).left = t.left :=
  rfl

/-- **Round trip at a `k`-point**: pushing the lifted `L`-point forward recovers the
`k`-point (under the unpacked algebra structure and tower). -/
theorem pushFieldPoint_liftFieldPoint [Algebra k K]
    (t : overSpec k K
      ⟶ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) :
    letI := fieldPointAlgebra t
    haveI := isScalarTower_fieldPointAlgebra t
    pushFieldPoint k (liftFieldPoint t) = t := by
  letI := fieldPointAlgebra t
  haveI := isScalarTower_fieldPointAlgebra t
  refine Over.OverMorphism.ext ?_
  rw [pushFieldPoint_left, liftFieldPoint_left]

/-- **Round trip at an `L`-point, the algebra**: unpacking the pushed-forward point
recovers the given `L`-algebra structure. -/
theorem fieldPointAlgebra_pushFieldPoint [Algebra k K] [Algebra L K]
    [IsScalarTower k L K] (s : overSpec L K ⟶ T) :
    fieldPointAlgebra (pushFieldPoint k s) = ‹Algebra L K› := by
  have h : ((pushFieldPoint k s).left ≫ T.hom :
        Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of L))
      = Spec.map (CommRingCat.ofHom (algebraMap L K)) :=
    (congrArg (· ≫ T.hom) (pushFieldPoint_left s)).trans (Over.w s)
  have hpre : Spec.preimage ((pushFieldPoint k s).left ≫ T.hom :
        Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of L))
      = CommRingCat.ofHom (algebraMap L K) :=
    (congrArg Spec.preimage h).trans (Spec.preimage_map _)
  refine Algebra.algebra_ext _ _ fun r => ?_
  exact congrArg (fun φ : CommRingCat.of L ⟶ CommRingCat.of K => φ.hom r) hpre

/-- **Round trip at an `L`-point, the carrier**: lifting the pushed-forward point gives
back the same carrier morphism. -/
@[simp]
theorem liftFieldPoint_pushFieldPoint_left [Algebra k K] [Algebra L K]
    [IsScalarTower k L K] (s : overSpec L K ⟶ T) :
    (liftFieldPoint (pushFieldPoint k s)).left = s.left := by
  rw [liftFieldPoint_left, pushFieldPoint_left]

end FieldPoint

/-! ## The degree-zero restriction interface for θ -/

section Pic0Restriction

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {T : Over (Spec (.of L))}

/-- **The quantifier exchange** (the R5 content): a class on the pushed-forward test
`(Over.map σ).obj T` is degree-zero at *every* `k`-field-point iff it is degree-zero at
every *pushed* `L`-field-point — every `k`-field-point of `(Over.map σ).obj T` arises as
`pushFieldPoint` of its own lift, by the round trips. -/
theorem mem_pic0Subgroup_iff_forall_pushFieldPoint
    (lam : picEt C ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)) :
    lam ∈ pic0Subgroup C
        ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)
      ↔ ∀ (K : Type u) [Field K] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
          (s : overSpec L K ⟶ T), degAt lam (pushFieldPoint k s) = 0 := by
  constructor
  · intro h K _ _ _ _ s
    exact mem_pic0Subgroup_iff.mp h K (pushFieldPoint k s)
  · intro h
    refine mem_pic0Subgroup_iff.mpr ?_
    intro K _ _ t
    letI := fieldPointAlgebra t
    haveI := isScalarTower_fieldPointAlgebra t
    have heq : pushFieldPoint k (liftFieldPoint t) = t := by
      refine Over.OverMorphism.ext ?_
      rw [pushFieldPoint_left, liftFieldPoint_left]
    have h0 := h K (liftFieldPoint t)
    rwa [heq] at h0

/-- **The degree-zero restriction engine for θ** (the B-4a → B-4b handshake): if a class
`lam` of the `k`-curve on the pushed-forward test and a class `lamL` of the base-changed
curve on `T` match in degree at every pushed field-point pair, then they are
simultaneously degree-zero.  B-4b discharges the matching hypothesis from the B-2 shuffle
via the degree seam `relPicDeg_relPicCrossBase`, and this equivalence restricts θ to the
degree-zero subfunctors. -/
theorem mem_pic0Subgroup_iff_of_degAt_pushFieldPoint_eq
    {lam : picEt C ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)}
    {lamL : picEt ((baseChange k L).obj C) T}
    (hmatch : ∀ (K : Type u) [Field K] [Algebra k K] [Algebra L K]
      [IsScalarTower k L K] (s : overSpec L K ⟶ T),
      degAt lam (pushFieldPoint k s) = degAt lamL s) :
    lam ∈ pic0Subgroup C
        ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)
      ↔ lamL ∈ pic0Subgroup ((baseChange k L).obj C) T := by
  rw [mem_pic0Subgroup_iff_forall_pushFieldPoint C lam]
  constructor
  · intro h
    refine mem_pic0Subgroup_iff.mpr ?_
    intro K _ _ s
    letI : Algebra k K := ((algebraMap L K).comp (algebraMap k L)).toAlgebra
    haveI : IsScalarTower k L K := .of_algebraMap_eq fun _ => rfl
    rw [← hmatch K s]
    exact h K s
  · intro h K _ _ _ _ s
    rw [hmatch K s]
    exact mem_pic0Subgroup_iff.mp h K s

end Pic0Restriction

end AlgebraicGeometry
