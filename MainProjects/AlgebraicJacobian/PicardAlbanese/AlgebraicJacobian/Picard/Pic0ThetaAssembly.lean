/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtCrossBase
import AlgebraicJacobian.Picard.Pic0SigmaSheaf

/-!
# θ: the base-field comparison of the degree-zero Picard functor (Wave 7, W7-B4b)

For a field embedding `k → L` and the curve bundle `C` over `k` with base change
`C_L = (baseChange k L).obj C`, the componentwise lift of the B-2 shuffle
(`Picard/PicEtCrossBase.lean`) restricts to the degree-zero subfunctors and assembles
into the natural isomorphism θ of the ratified D2-i shape,
`θ : Pic⁰_{C_L/L} ≅ (Over.map σ)ᵒᵖ ⋙ Pic⁰_{C/k}` in `CommGrpCat`-valued functors
(`σ = Spec.map (algebraMap k L)`).

* `AlgebraicGeometry.degAff_baseFieldShuffle`: **degree invariance of the B-2 shuffle at
  a field test** — `degAff K (baseFieldShuffle x) = degAff K x` for `K` in the tower
  `k → L → K`.  Both sides are read by `degAff_mk` on a common finite separable
  refinement `M/K` of the representing cover; the readings match through the
  `relPicAlgMap` square `relPicCrossBase_relPicAlgMap` and B-4a's degree seam
  `relPicDeg_relPicCrossBase` at `M` (the deg-d5b D1 discipline: the only licensed
  cross-presentation degree route).
* `AlgebraicGeometry.degAt_pushFieldPoint_picEtCrossBase`: **the `degAt` matching** —
  the degree of a class on the pushed test at a pushed field point equals the degree of
  its lift at the field point itself, by naturality of the lift, the affine face, and
  the shuffle degree invariance.
* `AlgebraicGeometry.mem_pic0Subgroup_picEtCrossBase_iff`: **the degree-zero
  restriction** — a class and its lift are simultaneously degree-zero, by B-4a's engine
  `mem_pic0Subgroup_iff_of_degAt_pushFieldPoint_eq` fed with the `degAt` matching.
* `AlgebraicGeometry.pic0CrossBaseEquiv`: the induced isomorphism of degree-zero
  subgroups `pic⁰(C_L, T) ≃* pic⁰(C, (Over.map σ).obj T)`.
* `AlgebraicGeometry.pic0Theta`: **θ** (Wave-7 brick B-4b, worksheet §D2 W7-B4b row) —
  the `CommGrpCat`-valued natural isomorphism
  `pic0Functor C_L ≅ (Over.map σ).op ⋙ pic0Functor C`, with `rfl`-grade component
  anchors `pic0Theta_hom_app_coe`/`pic0Theta_inv_app_coe`.
* `AlgebraicGeometry.pic0ThetaType`: the Type-valued form, by whiskering with
  `forget₂ CommGrpCat GrpCat ⋙ forget GrpCat` against `pic0TypeFunctor` (the D2-i
  massage; consumed by B-5's `RepresentableBy.ofIso` transport).

Everything θ-shaped here is stated for an arbitrary `[Field L] [Algebra k L]` — no
finiteness, separability or Galois content — so composed shuffles at towers
`k → L → M` are legal inputs for the K-1 θ-cocycle.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
variable (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-! ## Degree invariance of the shuffle at a field test -/

/-- **Degree invariance of the base-field shuffle at a field test** (the B-4b degree
keystone): for a field `K` in the tower `k → L → K`, the B-2 shuffle preserves the
plus-class degree.  Both sides are read by `degAff_mk` on a common finite separable
refinement `M/K` of the representing cover; the readings match through the
`relPicAlgMap` square and B-4a's degree seam `relPicDeg_relPicCrossBase` at `M`. -/
theorem degAff_baseFieldShuffle (K : Type u) [Field K] [Algebra k K] [Algebra L K]
    [IsScalarTower k L K] (x : PicEtAff C K) :
    PicEtAff.degAff K (PicEtAff.baseFieldShuffle k L C K x) = PicEtAff.degAff K x := by
  induction x using PicEtAff.ind with
  | mk E y =>
    obtain ⟨M, _, _, _, _, ⟨j⟩⟩ := E.exists_finiteSeparableField_algHom
    letI : Algebra L M := ((algebraMap K M).comp (algebraMap L K)).toAlgebra
    haveI : IsScalarTower L K M := .of_algebraMap_eq fun _ => rfl
    letI : Algebra k M := ((algebraMap L M).comp (algebraMap k L)).toAlgebra
    haveI : IsScalarTower k L M := .of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower k K M := .of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply k L K r]; rfl
    rw [PicEtAff.baseFieldShuffle_mk,
      PicEtAff.degAff_mk E ((crossBaseTransportFamily k L C).descentHom E y) M j,
      PicEtAff.degAff_mk E y M j,
      PicEtAff.crossBaseTransportFamily_descentHom_coe,
      ← relPicCrossBase_relPicAlgMap k L C E.Carrier M (j.restrictScalars L),
      relPicDeg_relPicCrossBase]
    rfl

/-! ## The `degAt` matching at pushed field points -/

section DegAtMatching

variable {T : Over (Spec (.of L))}

/-- **The `degAt` matching at pushed field points**: the degree of an étale Picard class
of `C` on the pushed test `(Over.map σ).obj T` at a pushed field point is the degree of
its componentwise lift at the field point itself.  Naturality of the lift moves the
restriction to the affine test `overSpec L K`, the affine face identifies the lift with
the B-2 shuffle there, and the shuffle preserves the degree. -/
theorem degAt_pushFieldPoint_picEtCrossBase
    (s : picEt C ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T))
    {K : Type u} [Field K] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
    (t : overSpec L K ⟶ T) :
    degAt s (pushFieldPoint k t) = degAt (picEtCrossBase k L C T s) t :=
  calc degAt s (pushFieldPoint k t)
      = PicEtAff.degAff K (picEtAffineEquiv C K
          (picEtMap C (mapOverSpecIso k L K).inv
            (picEtMap C
              ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map t) s))) :=
        congrArg (fun z => PicEtAff.degAff K (picEtAffineEquiv C K z))
          (picEtMap_comp C
            ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map t)
            (mapOverSpecIso k L K).inv s)
    _ = PicEtAff.degAff K (PicEtAff.baseFieldShuffle k L C K
          (picEtAffineEquiv C K
            (picEtMap C (mapOverSpecIso k L K).inv
              (picEtMap C
                ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map t)
                s)))) :=
        (degAff_baseFieldShuffle k L C K _).symm
    _ = PicEtAff.degAff K (picEtAffineEquiv ((baseChange k L).obj C) K
          (picEtCrossBase k L C (overSpec L K)
            (picEtMap C
              ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map t) s))) :=
        congrArg (PicEtAff.degAff K)
          (picEtAffineEquiv_picEtCrossBase k L C K _).symm
    _ = degAt (picEtCrossBase k L C T s) t :=
        (congrArg (fun z => PicEtAff.degAff K
            (picEtAffineEquiv ((baseChange k L).obj C) K z))
          (picEtMap_picEtCrossBase k L C t s)).symm

/-! ## The degree-zero restriction -/

/-- **The degree-zero restriction of the componentwise lift** (the B-4a → B-4b
handshake discharged): an étale Picard class of `C` on the pushed test and its
componentwise lift to `C_L` are simultaneously degree-zero. -/
theorem mem_pic0Subgroup_picEtCrossBase_iff
    (s : picEt C ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)) :
    s ∈ pic0Subgroup C
        ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)
      ↔ picEtCrossBase k L C T s ∈ pic0Subgroup ((baseChange k L).obj C) T :=
  mem_pic0Subgroup_iff_of_degAt_pushFieldPoint_eq C
    (fun _ _ _ _ _ t => degAt_pushFieldPoint_picEtCrossBase k L C s t)

end DegAtMatching

/-! ## The degree-zero subgroup comparison -/

/-- **The base-field comparison of the degree-zero subgroups**: for an `L`-test `T`,
degree-zero classes of `C_L` on `T` correspond to degree-zero classes of `C` on the
pushed test `(Over.map σ).obj T` — the component of θ, in the direction the frozen
`baseChangeIso` consumes. -/
noncomputable def pic0CrossBaseEquiv (T : Over (Spec (.of L))) :
    pic0Subgroup ((baseChange k L).obj C) T
      ≃* pic0Subgroup C
          ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) where
  toFun lam :=
    ⟨picEtCrossBaseInv k L C T (lam : picEt ((baseChange k L).obj C) T), by
      refine (mem_pic0Subgroup_picEtCrossBase_iff k L C _).mpr ?_
      have h : picEtCrossBase k L C T
          (picEtCrossBaseInv k L C T (lam : picEt ((baseChange k L).obj C) T))
          = (lam : picEt ((baseChange k L).obj C) T) :=
        (picEtCrossBaseEquiv k L C T).apply_symm_apply _
      rw [h]
      exact lam.2⟩
  invFun mu :=
    ⟨picEtCrossBase k L C T (mu : picEt C
        ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)),
      (mem_pic0Subgroup_picEtCrossBase_iff k L C _).mp mu.2⟩
  left_inv lam := Subtype.ext ((picEtCrossBaseEquiv k L C T).apply_symm_apply _)
  right_inv mu := Subtype.ext ((picEtCrossBaseEquiv k L C T).symm_apply_apply _)
  map_mul' lam mu := Subtype.ext (map_mul (picEtCrossBaseInv k L C T) _ _)

@[simp]
lemma pic0CrossBaseEquiv_apply_coe (T : Over (Spec (.of L)))
    (lam : pic0Subgroup ((baseChange k L).obj C) T) :
    ((pic0CrossBaseEquiv k L C T lam :
        pic0Subgroup C
          ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T))
      : picEt C ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T))
      = picEtCrossBaseInv k L C T (lam : picEt ((baseChange k L).obj C) T) :=
  rfl

@[simp]
lemma pic0CrossBaseEquiv_symm_apply_coe (T : Over (Spec (.of L)))
    (mu : pic0Subgroup C
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)) :
    (((pic0CrossBaseEquiv k L C T).symm mu :
        pic0Subgroup ((baseChange k L).obj C) T)
      : picEt ((baseChange k L).obj C) T)
      = picEtCrossBase k L C T (mu : picEt C
          ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)) :=
  rfl

/-! ## θ -/

/-- **θ — the base-field comparison of the degree-zero Picard functor** (Wave-7 brick
B-4b, the ratified D2-i shape): the `CommGrpCat`-valued natural isomorphism
`pic0Functor C_L ≅ (Over.map σ).op ⋙ pic0Functor C` whose component at an `L`-test is
the degree-zero restriction of the componentwise lift of the B-2 base-field shuffle.
Naturality is the naturality of the lift in the test object.  Consumed by B-5/B-6
(`JacobianDataBaseChange`) through its Type form `pic0ThetaType`, and by the K-1
θ-cocycle (composed shuffles at towers `k → L → M` are legal inputs since nothing here
constrains `[Algebra k L]`). -/
noncomputable def pic0Theta :
    pic0Functor ((baseChange k L).obj C)
      ≅ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).op
          ⋙ pic0Functor C :=
  NatIso.ofComponents
    (fun T => (pic0CrossBaseEquiv k L C T.unop).toCommGrpIso)
    (fun {T T'} g => by
      ext lam
      exact Subtype.ext (picEtMap_picEtCrossBaseInv k L C g.unop lam.1).symm)

/-- The component anchor of θ: the `hom` component at `T` is the degree-zero subgroup
comparison (whose underlying class transport is `picEtCrossBaseInv`, by
`pic0CrossBaseEquiv_apply_coe`). -/
@[simp]
lemma pic0Theta_hom_app (T : (Over (Spec (.of L)))ᵒᵖ)
    (lam : pic0Subgroup ((baseChange k L).obj C) T.unop) :
    (pic0Theta k L C).hom.app T lam = pic0CrossBaseEquiv k L C T.unop lam :=
  rfl

/-- The component anchor of θ⁻¹: the `inv` component at `T` is the inverse subgroup
comparison (whose underlying class transport is `picEtCrossBase`, by
`pic0CrossBaseEquiv_symm_apply_coe`). -/
@[simp]
lemma pic0Theta_inv_app (T : (Over (Spec (.of L)))ᵒᵖ)
    (mu : pic0Subgroup C
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T.unop)) :
    (pic0Theta k L C).inv.app T mu = (pic0CrossBaseEquiv k L C T.unop).symm mu :=
  rfl

/-! ## The Type-valued form -/

/-- **The Type-valued form of θ** (the D2-i whiskering massage): the natural
isomorphism `pic0TypeFunctor C_L ≅ (Over.map σ).op ⋙ pic0TypeFunctor C` obtained from
θ by whiskering with `forget₂ CommGrpCat GrpCat ⋙ forget GrpCat` — the input of B-5's
`RepresentableBy.ofIso` transport of the Jacobian datum. -/
noncomputable def pic0ThetaType :
    pic0TypeFunctor ((baseChange k L).obj C)
      ≅ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).op
          ⋙ pic0TypeFunctor C :=
  Functor.isoWhiskerRight (pic0Theta k L C) (forget₂ CommGrpCat GrpCat ⋙ forget GrpCat)

/-- The Type form of θ has the components of the degree-zero subgroup comparison. -/
@[simp]
lemma pic0ThetaType_hom_app (T : (Over (Spec (.of L)))ᵒᵖ)
    (lam : pic0Subgroup ((baseChange k L).obj C) T.unop) :
    (pic0ThetaType k L C).hom.app T lam = pic0CrossBaseEquiv k L C T.unop lam :=
  rfl

/-- The Type form of θ⁻¹ has the components of the inverse subgroup comparison. -/
@[simp]
lemma pic0ThetaType_inv_app (T : (Over (Spec (.of L)))ᵒᵖ)
    (mu : pic0Subgroup C
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T.unop)) :
    (pic0ThetaType k L C).inv.app T mu = (pic0CrossBaseEquiv k L C T.unop).symm mu :=
  rfl

end AlgebraicGeometry
