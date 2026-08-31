/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtAffTransport
import AlgebraicJacobian.Picard.Pic0Theta

/-!
# The base-field shuffle of the étale plus construction (Wave 7, W7-B2)

For a field embedding `k → L` and a curve bundle `C` over `k`, étale-plus Picard classes
of `C` at an affine test `Spec A` in a scalar tower `k → L → A` shuffle to étale-plus
Picard classes of the base-changed curve `C_L = (baseChange k L).obj C` at the *same*
test — over the literally shared étale-cover index (`Algebra.EtaleCover A` never mentions
the base field).  This file instantiates the parameterized transport core
(`Picard/PicEtAffTransport.lean`, the F-2/B-2 shared D2-ii skeleton) at B-4a's
same-carrier comparison family `crossBaseAffineIso` (`Picard/Pic0Theta.lean`), in both
directions, and packages the two-sided collapse as a `MulEquiv`.

* `AlgebraicGeometry.crossBaseAffineIso_inv_naturality`: the inverse-side naturality of
  the same-carrier comparison in the test algebra (the `inv` face of B-4a's
  `crossBaseAffineIso_naturality`).
* `AlgebraicGeometry.crossBaseTransportFamily` / `crossBaseTransportFamilyInv`: the two
  transport families, with `hom := (crossBaseAffineIso k L C B).hom` (resp. `.inv`); the
  core's two-sided instance index collapses at the tower diagonal `kT = L` by
  `Algebra.algebra_ext`, so at a shared instance pack the families are definitionally
  the comparison itself (`crossBaseTransportFamily_hom`, `crossBaseTransportFamilyInv_hom`)
  and the induced relative Picard transports are definitionally B-4a's
  `relPicCrossBase`/`relPicCrossBaseInv` (`crossBaseTransportFamily_relPicHom`,
  `crossBaseTransportFamilyInv_relPicHom`) — the mk-level reconciliation through which
  the landed degree seam `relPicDeg_relPicCrossBase` transfers to the plus level.
* `AlgebraicGeometry.PicEtAff.baseFieldShuffle k L C A :
  PicEtAff C A ≃* PicEtAff ((baseChange k L).obj C) A`: the base-field shuffle, with the
  computation rules `baseFieldShuffle_mk`/`baseFieldShuffle_symm_mk` (descent-class
  representatives transport by `relPicCrossBase`/`relPicCrossBaseInv` on the same cover:
  `crossBaseTransportFamily_descentHom_coe`, `crossBaseTransportFamilyInv_descentHom_coe`),
  the `mk`-equality transport `baseFieldShuffle_mk_eq_mk`, naturality of the unit
  (`baseFieldShuffle_unit`, `baseFieldShuffle_symm_unit`), and the bilateral restriction
  squares `map_baseFieldShuffle`/`mapAlg_baseFieldShuffle` (and their `symm` faces).

B-4b (`θ`) consumes this interface componentwise over affine opens through
`picEtAffineEquiv`; nothing here unfolds the plus setoid beyond the landed
`mk`/`ind`/`mk_eq_mk_iff` API, and all cross-presentation degree facts route through
B-4a's `relPicDeg_relPicCrossBase` via the `descentHom` reconciliation.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry.Scheme (CechPic)

namespace AlgebraicGeometry

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
variable (C : Over (Spec (.of k)))

/-- Two `F`-algebra structures on the same ring sitting in a scalar tower over the
identity algebra `Algebra.id F` are equal — the seam that collapses the transport core's
two-sided instance index at the tower diagonal `kT = L` (the base-field-shuffle sibling
of the F-2 collapse at `kD = kE = kT = k`). -/
private lemma algebra_eq_of_tower {F B : Type u} [Field F] [CommRing B]
    (iT iD : Algebra F B)
    (tw : @IsScalarTower F F B (Algebra.id F).toSMul iT.toSMul iD.toSMul) :
    iD = iT := by
  refine Algebra.algebra_ext _ _ fun r => ?_
  rw [@IsScalarTower.algebraMap_eq F F B _ _ _ (Algebra.id F) iT iD tw]
  rfl

/-- **Inverse-side naturality of the same-carrier comparison in the test algebra**: for
an `L`-algebra map `f : A →ₐ[L] B` in towers over `k`, the inverse comparisons intertwine
`Spec f` whiskered on the two sides — the `inv` face of B-4a's
`crossBaseAffineIso_naturality`. -/
theorem crossBaseAffineIso_inv_naturality (A : Type u) [CommRing A] [Algebra k A]
    [Algebra L A] [IsScalarTower k L A] (B : Type u) [CommRing B] [Algebra k B]
    [Algebra L B] [IsScalarTower k L B] (f : A →ₐ[L] B) :
    (crossBaseAffineIso k L C B).inv
        ≫ (((baseChange k L).obj C) ◁ Over.overSpecMap f).left
      = (C ◁ Over.overSpecMap (f.restrictScalars k)).left
          ≫ (crossBaseAffineIso k L C A).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, crossBaseAffineIso_naturality k L C A B f,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The forward base-field transport family** (the D2-ii core instantiated at B-1/B-4a):
at every test algebra `B` in a scalar tower `k → L → B`, the same-carrier comparison
`(crossBaseAffineIso k L C B).hom`.  The `hom` field is stated across the two `L`-instance
slots of the transport core's index (`kD = kT = L`); the scalar tower collapses them
(`algebra_eq_of_tower`), and at a shared instance pack the field is definitionally the
comparison itself (`crossBaseTransportFamily_hom`). -/
noncomputable def crossBaseTransportFamily :
    RelPicTransportFamily L ((baseChange k L).obj C) C where
  hom B _ iD iE iT twD twE := by
    obtain rfl : iD = iT := algebra_eq_of_tower iT iD twD
    exact (crossBaseAffineIso k L C B).hom
  hom_snd B _ iD iE iT twD twE := by
    obtain rfl : iD = iT := algebra_eq_of_tower iT iD twD
    exact crossBaseAffineIso_hom_snd k L C B
  hom_naturality B B' _ iDB iEB iTB twDB twEB _ iDB' iEB' iTB' twDB' twEB' fD fE hf := by
    obtain rfl : iDB = iTB := algebra_eq_of_tower iTB iDB twDB
    obtain rfl : iDB' = iTB' := algebra_eq_of_tower iTB' iDB' twDB'
    obtain rfl : fE = fD.restrictScalars k := AlgHom.ext fun b => (hf b).symm
    exact crossBaseAffineIso_naturality k L C B B' fD

/-- **The backward base-field transport family**: the inverse comparisons
`(crossBaseAffineIso k L C B).inv`, collapsing the core's index at `kE = kT = L`.  At a
shared instance pack the field is definitionally the inverse comparison
(`crossBaseTransportFamilyInv_hom`). -/
noncomputable def crossBaseTransportFamilyInv :
    RelPicTransportFamily L C ((baseChange k L).obj C) where
  hom B _ iD iE iT twD twE := by
    obtain rfl : iE = iT := algebra_eq_of_tower iT iE twE
    exact (crossBaseAffineIso k L C B).inv
  hom_snd B _ iD iE iT twD twE := by
    obtain rfl : iE = iT := algebra_eq_of_tower iT iE twE
    exact crossBaseAffineIso_inv_snd k L C B
  hom_naturality B B' _ iDB iEB iTB twDB twEB _ iDB' iEB' iTB' twDB' twEB' fD fE hf := by
    obtain rfl : iEB = iTB := algebra_eq_of_tower iTB iEB twEB
    obtain rfl : iEB' = iTB' := algebra_eq_of_tower iTB' iEB' twEB'
    obtain rfl : fD = fE.restrictScalars k := AlgHom.ext hf
    exact crossBaseAffineIso_inv_naturality k L C B B' fE

section Anchors

variable (B : Type u) [CommRing B] [Algebra k B] [Algebra L B] [IsScalarTower k L B]

/-- At a shared instance pack, the forward family is the same-carrier comparison. -/
lemma crossBaseTransportFamily_hom :
    (crossBaseTransportFamily k L C).hom B = (crossBaseAffineIso k L C B).hom :=
  rfl

/-- At a shared instance pack, the backward family is the inverse comparison. -/
lemma crossBaseTransportFamilyInv_hom :
    (crossBaseTransportFamilyInv k L C).hom B = (crossBaseAffineIso k L C B).inv :=
  rfl

/-- **The mk-level reconciliation with B-4a** (forward): at a shared instance pack, the
relative Picard transport induced by the forward family is B-4a's relPic-level shuffle
`relPicCrossBase` — the identification through which the landed degree seam
`relPicDeg_relPicCrossBase` transfers to the plus level. -/
lemma crossBaseTransportFamily_relPicHom :
    (crossBaseTransportFamily k L C).relPicHom B = relPicCrossBase k L C B :=
  rfl

/-- The mk-level reconciliation with B-4a (backward): the relative Picard transport
induced by the backward family is `relPicCrossBaseInv`. -/
lemma crossBaseTransportFamilyInv_relPicHom :
    (crossBaseTransportFamilyInv k L C).relPicHom B = relPicCrossBaseInv k L C B :=
  rfl

end Anchors

namespace PicEtAff

variable (A : Type u) [CommRing A] [Algebra k A] [Algebra L A] [IsScalarTower k L A]

noncomputable section

/-- **The base-field shuffle of the étale plus construction** (Wave-7 brick B-2): for a
test algebra `A` in a scalar tower `k → L → A`, étale-plus Picard classes of the `k`-curve
`C` and of the base-changed curve `C_L = (baseChange k L).obj C` at the test `A`
correspond, over the literally shared étale-cover index — descent-class representatives
transport by B-4a's `relPicCrossBase` on the same cover.  The two directions are the
transport core's `picEtAffHom` at the forward and backward comparison families; the round
trips collapse by `picEtAffHom_picEtAffHom` since the underlying scheme morphisms are
pointwise inverse. -/
def baseFieldShuffle : PicEtAff C A ≃* PicEtAff ((baseChange k L).obj C) A where
  toFun := (crossBaseTransportFamily k L C).picEtAffHom A
  invFun := (crossBaseTransportFamilyInv k L C).picEtAffHom A
  left_inv a :=
    (crossBaseTransportFamily k L C).picEtAffHom_picEtAffHom
      (crossBaseTransportFamilyInv k L C)
      (fun B _ iD iE iT twD twE => by
        obtain rfl : iD = iT := algebra_eq_of_tower iT iD twD
        exact Iso.inv_hom_id _) a
  right_inv a :=
    (crossBaseTransportFamilyInv k L C).picEtAffHom_picEtAffHom
      (crossBaseTransportFamily k L C)
      (fun B _ iD iE iT twD twE => by
        obtain rfl : iE = iT := algebra_eq_of_tower iT iE twE
        exact Iso.hom_inv_id _) a
  map_mul' := map_mul ((crossBaseTransportFamily k L C).picEtAffHom A)

variable {A}

@[simp]
lemma baseFieldShuffle_apply (a : PicEtAff C A) :
    baseFieldShuffle k L C A a = (crossBaseTransportFamily k L C).picEtAffHom A a :=
  rfl

@[simp]
lemma baseFieldShuffle_symm_apply (b : PicEtAff ((baseChange k L).obj C) A) :
    (baseFieldShuffle k L C A).symm b
      = (crossBaseTransportFamilyInv k L C).picEtAffHom A b :=
  rfl

/-- The computation rule of the shuffle: representatives transport cover-by-cover, on the
literally shared cover. -/
@[simp]
theorem baseFieldShuffle_mk (U : Algebra.EtaleCover A) (x : descentClasses C U) :
    baseFieldShuffle k L C A (mk C U x)
      = mk ((baseChange k L).obj C) U
          ((crossBaseTransportFamily k L C).descentHom U x) :=
  rfl

/-- The computation rule of the inverse shuffle. -/
@[simp]
theorem baseFieldShuffle_symm_mk (U : Algebra.EtaleCover A)
    (x : descentClasses ((baseChange k L).obj C) U) :
    (baseFieldShuffle k L C A).symm (mk ((baseChange k L).obj C) U x)
      = mk C U ((crossBaseTransportFamilyInv k L C).descentHom U x) :=
  rfl

/-- The descent-class transport of the forward family is B-4a's `relPicCrossBase` on the
underlying relative Picard classes — the mk-level identification consumed by B-4b's
degree matching (route through `relPicDeg_relPicCrossBase`). -/
@[simp]
theorem crossBaseTransportFamily_descentHom_coe (U : Algebra.EtaleCover A)
    (x : descentClasses C U) :
    (((crossBaseTransportFamily k L C).descentHom U x)
        : relPic ((baseChange k L).obj C) (overSpec L U.Carrier))
      = relPicCrossBase k L C U.Carrier (x : relPic C (overSpec k U.Carrier)) :=
  rfl

/-- The descent-class transport of the backward family is `relPicCrossBaseInv` on the
underlying relative Picard classes. -/
@[simp]
theorem crossBaseTransportFamilyInv_descentHom_coe (U : Algebra.EtaleCover A)
    (x : descentClasses ((baseChange k L).obj C) U) :
    (((crossBaseTransportFamilyInv k L C).descentHom U x)
        : relPic C (overSpec k U.Carrier))
      = relPicCrossBaseInv k L C U.Carrier
          (x : relPic ((baseChange k L).obj C) (overSpec L U.Carrier)) :=
  rfl

/-- The shuffle transports `mk`-equalities: representatives identified in the plus of `C`
stay identified after the base-field shuffle — the plus-level face of the core's
`descentHom_descentMap`. -/
theorem baseFieldShuffle_mk_eq_mk {U V : Algebra.EtaleCover A} {x : descentClasses C U}
    {y : descentClasses C V} (h : mk C U x = mk C V y) :
    mk ((baseChange k L).obj C) U ((crossBaseTransportFamily k L C).descentHom U x)
      = mk ((baseChange k L).obj C) V
          ((crossBaseTransportFamily k L C).descentHom V y) := by
  rw [← baseFieldShuffle_mk, ← baseFieldShuffle_mk, h]

/-- The inverse shuffle transports `mk`-equalities. -/
theorem baseFieldShuffle_symm_mk_eq_mk {U V : Algebra.EtaleCover A}
    {x : descentClasses ((baseChange k L).obj C) U}
    {y : descentClasses ((baseChange k L).obj C) V}
    (h : mk ((baseChange k L).obj C) U x = mk ((baseChange k L).obj C) V y) :
    mk C U ((crossBaseTransportFamilyInv k L C).descentHom U x)
      = mk C V ((crossBaseTransportFamilyInv k L C).descentHom V y) := by
  rw [← baseFieldShuffle_symm_mk, ← baseFieldShuffle_symm_mk, h]

/-- The base-field shuffle is compatible with the unit of the plus construction: on
classes pulled back to the trivial cover it is B-4a's relPic-level shuffle. -/
theorem baseFieldShuffle_unit (x : relPic C (overSpec k A)) :
    baseFieldShuffle k L C A (unit C A x)
      = unit ((baseChange k L).obj C) A (relPicCrossBase k L C A x) :=
  (crossBaseTransportFamily k L C).picEtAffHom_unit x

/-- The inverse shuffle is compatible with the unit of the plus construction. -/
theorem baseFieldShuffle_symm_unit (y : relPic ((baseChange k L).obj C) (overSpec L A)) :
    (baseFieldShuffle k L C A).symm (unit ((baseChange k L).obj C) A y)
      = unit C A (relPicCrossBaseInv k L C A y) :=
  (crossBaseTransportFamilyInv k L C).picEtAffHom_unit y

section Bilateral

variable (A' : Type u) [CommRing A'] [Algebra k A'] [Algebra L A']
  [IsScalarTower k L A']

/-- The base-field shuffle commutes with restriction along a base extension of affine
tests (instance form). -/
theorem map_baseFieldShuffle [Algebra A A'] [IsScalarTower k A A']
    [IsScalarTower L A A'] (a : PicEtAff C A) :
    baseFieldShuffle k L C A' (map C A' a)
      = map ((baseChange k L).obj C) A' (baseFieldShuffle k L C A a) :=
  (crossBaseTransportFamily k L C).map_picEtAffHom a

/-- The inverse shuffle commutes with restriction along a base extension of affine tests
(instance form). -/
theorem map_baseFieldShuffle_symm [Algebra A A'] [IsScalarTower k A A']
    [IsScalarTower L A A'] (b : PicEtAff ((baseChange k L).obj C) A) :
    (baseFieldShuffle k L C A').symm (map ((baseChange k L).obj C) A' b)
      = map C A' ((baseFieldShuffle k L C A).symm b) :=
  (crossBaseTransportFamilyInv k L C).map_picEtAffHom b

variable {A'}

/-- **The `mapAlg` bilateral square**: the base-field shuffle commutes with restriction
along an explicit `L`-algebra map of affine tests (restricted to `k` on the `k`-curve
side). -/
theorem mapAlg_baseFieldShuffle (φ : A →ₐ[L] A') (a : PicEtAff C A) :
    baseFieldShuffle k L C A' (mapAlg C (φ.restrictScalars k) a)
      = mapAlg ((baseChange k L).obj C) φ (baseFieldShuffle k L C A a) :=
  (crossBaseTransportFamily k L C).mapAlg_picEtAffHom φ a

/-- The `mapAlg` bilateral square for the inverse shuffle. -/
theorem mapAlg_baseFieldShuffle_symm (φ : A →ₐ[L] A')
    (b : PicEtAff ((baseChange k L).obj C) A) :
    (baseFieldShuffle k L C A').symm (mapAlg ((baseChange k L).obj C) φ b)
      = mapAlg C (φ.restrictScalars k) ((baseFieldShuffle k L C A).symm b) :=
  (crossBaseTransportFamilyInv k L C).mapAlg_picEtAffHom φ b

end Bilateral

end

end PicEtAff

end AlgebraicGeometry
