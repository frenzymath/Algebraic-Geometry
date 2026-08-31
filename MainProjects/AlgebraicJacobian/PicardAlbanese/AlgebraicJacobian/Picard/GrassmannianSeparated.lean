/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GrassmannianDiagonal
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Separatedness of the Grassmannian over the base field (DD-3, stage 3d)

The structure morphism `Gr(d, r) → Spec k` is **separated**, by the route map's patch
computation (Nitsure §1; the Proj template): on each patch `U^I ×_k U^J` of the
product atlas, `pullbackDiagonalMapIdIso` rewrites the restricted diagonal to the
affine morphism `Spec.map δ_{I,J}`, a closed immersion because `δ_{I,J}` is surjective
(`Picard/GrassmannianDiagonal.lean`).

Frame-atlas exports for the DD-R chart plumbing (the §3.5 mechanism ruling: chart
plumbing, not an openness mechanism): the chart pieces of the glue-data atlas are
affine, and `k`-algebra maps out of a chart ring are exactly matrix data (the
`MvPolynomial.aeval` universal property).

* `AlgebraicGeometry.Grassmannian.isSeparated_grStructMap`: **separatedness** of the
  structure morphism; `isSeparated_grScheme`: the glued scheme is separated.
* `AlgebraicGeometry.Grassmannian.chartRingAlgHomEquiv`: `(R^I →ₐ[k] S) ≃` free-entry
  matrix data valued in `S`.
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory TensorProduct

namespace AlgebraicGeometry.Grassmannian

set_option maxHeartbeats 3200000 in
-- The patch computation traverses the `pullbackDiagonalMapIdIso` / `pullbackSpecIso`
-- instance diamonds over the heavy localised chart rings (defeq-expensive `erw`s);
-- elaboration cost, not a kernel raise — the route map carries the same raise.
set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Limits in
/-- The structure morphism `Gr(d, r) → Spec k` is **separated**.  Following the Proj
template: on each patch `U^I ×_k U^J` of the product atlas the restricted diagonal is,
via `pullbackDiagonalMapIdIso`, the affine morphism `Spec.map δ_{I,J}`, a closed
immersion because `δ_{I,J}` is surjective (`diagonalRingMap_surjective`).  The raised
heartbeat limit covers the defeq-expensive `erw`s through the pullback instance
diamonds on the heavy localised chart rings (elaboration cost, not a kernel raise —
the route map carries the same raise). -/
theorem isSeparated_grStructMap (k : Type u) [Field k] (d r : ℕ) :
    IsSeparated (grStructMap k d r) := by
  refine ⟨IsZariskiLocalAtTarget.of_openCover (Scheme.Pullback.openCoverOfLeftRight
    (glueData k d r).openCover (glueData k d r).openCover
    (grStructMap k d r) (grStructMap k d r)) ?_⟩
  intro ⟨i, j⟩
  dsimp only [Scheme.Cover.pullbackHom]
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (f := (pullbackDiagonalMapIdIso ..).inv) _).mp ?_
  let e₁ : pullback ((glueData k d r).openCover.f i ≫ grStructMap k d r)
        ((glueData k d r).openCover.f j ≫ grStructMap k d r) ≅
        Spec (.of (TensorProduct k
          (ChartRing k d r i.down.1) (ChartRing k d r j.down.1))) :=
    pullback.congrHom (ι_grStructMap k d r i) (ι_grStructMap k d r j) ≪≫
      pullbackSpecIso k _ _
  let e₂ : pullback ((glueData k d r).openCover.f i) ((glueData k d r).openCover.f j) ≅
        Spec (.of (Localization.Away (minorDet k d r i.down.1 j.down.1 i.down.2 j.down.2))) :=
    pullbackιIso k d r i j
  rw [← MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ e₁.hom,
    ← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) e₂.inv]
  let F : TensorProduct k (ChartRing k d r i.down.1) (ChartRing k d r j.down.1) →+*
        Localization.Away (minorDet k d r i.down.1 j.down.1 i.down.2 j.down.2) :=
    (diagonalRingMap k d r i.down.1 j.down.1 i.down.2 j.down.2).toRingHom
  have hsurj : Function.Surjective F :=
    diagonalRingMap_surjective k d r i.down.1 j.down.1 i.down.2 j.down.2
  convert IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom F) hsurj using 1
  rw [← cancel_mono (pullbackSpecIso k _ _).inv]
  apply pullback.hom_ext
  · simp only [e₂, e₁, Iso.trans_hom, pullback.congrHom_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, pullbackSpecIso_inv_fst, ← Spec.map_comp]
    rw [pullback.lift_fst, Category.comp_id]
    erw [pullbackDiagonalMapIdIso_inv_snd_fst]
    erw [pullbackιIso_inv_fst]
    rw [chartIncl]
    congr 1
    rw [← CommRingCat.ofHom_comp]
    congr 1
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
    exact (diagonalRingMap_left k d r i.down.1 j.down.1 i.down.2 j.down.2 a).symm
  · simp only [e₂, e₁, Iso.trans_hom, pullback.congrHom_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, pullbackSpecIso_inv_snd, ← Spec.map_comp]
    rw [pullback.lift_snd, Category.comp_id]
    erw [pullbackDiagonalMapIdIso_inv_snd_snd]
    erw [pullbackιIso_inv_snd]
    rw [chartTransition_comp_chartIncl]
    congr 1
    rw [← CommRingCat.ofHom_comp]
    congr 1
    refine RingHom.ext fun b => ?_
    exact (diagonalRingMap_right k d r i.down.1 j.down.1 i.down.2 j.down.2 b).symm

/-- **The Grassmannian scheme is separated** (absolutely): the structure morphism is
separated and `Spec k` is affine, hence separated over the terminal object. -/
theorem isSeparated_grScheme (k : Type u) [Field k] (d r : ℕ) :
    (grScheme k d r).IsSeparated := by
  have hsep : IsSeparated (grStructMap k d r) := isSeparated_grStructMap k d r
  rw [Scheme.isSeparated_iff]
  have he : Limits.terminal.from (grScheme k d r)
      = grStructMap k d r ≫ Limits.terminal.from (Spec (CommRingCat.of k)) :=
    Limits.terminal.hom_ext _ _
  rw [he]
  infer_instance

/-- The pieces of the Grassmannian chart atlas are affine (frame-atlas export). -/
instance isAffine_glueData_openCover_X (k : Type u) [Field k] (d r : ℕ)
    (i : (glueData k d r).J) : IsAffine ((glueData k d r).openCover.X i) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (ChartRing k d r i.down.1))))

/-- **`k`-algebra maps out of a chart ring are matrix data** (frame-atlas export, the
`MvPolynomial.aeval` universal property): an algebra map `R^I →ₐ[k] S` is exactly an
assignment of the `d(r-d)` free entries in `S`.  DD-R's chart-local work consumes
chart points in this spelling. -/
noncomputable def chartRingAlgHomEquiv (k : Type u) [Field k] (d r : ℕ)
    (I : Finset (Fin r)) (S : Type u) [CommRing S] [Algebra k S] :
    (ChartRing k d r I →ₐ[k] S) ≃ ((Fin d × {q : Fin r // q ∉ I}) → S) where
  toFun f := fun e => f (MvPolynomial.X e)
  invFun v := MvPolynomial.aeval v
  left_inv f := MvPolynomial.algHom_ext fun e =>
    MvPolynomial.aeval_X (fun e' => f (MvPolynomial.X e')) e
  right_inv v := funext fun e => MvPolynomial.aeval_X v e

end AlgebraicGeometry.Grassmannian
