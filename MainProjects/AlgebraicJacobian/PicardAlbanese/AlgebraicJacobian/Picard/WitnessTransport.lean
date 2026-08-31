/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.WitnessAway
import AlgebraicJacobian.Algebra.PiAssembly
import AlgebraicJacobian.Picard.AffineTwoCover

/-!
# Transport of the simplicial maps through the two-base identifications (ζ2·ii)

The restriction maps of the section rings along the diagonal `Δ = Spec (mul)` and the
three cofaces `f₁₂, f₁₃, f₂₃` of the tensor towers correspond, under the two-base
localization identifications `Over.pairAwayEquiv` / `Over.tripleAwayEquiv` of
`AlgebraicJacobian.Picard.WitnessAway`, to the index-wise collapse and faces of the
pi-assembly (`AlgebraicJacobian.Algebra.PiAssembly`,
`AlgebraicJacobian.Algebra.TensorAwayPi`):

* `AlgebraicGeometry.Over.pairAwayEquiv_appLE_diag`: `Δ^♯ ∘ pairAwayEquiv` is the
  index-wise collapse `IsLocalization.AwayCover.componentCollapse` onto the Zariski
  overlap ring `Γ(Spec B, D(P.r i ⋅ P.r j))`;
* `AlgebraicGeometry.Over.tripleAwayEquiv_faceA₂₃/₁₂/₁₃`: `fᵢⱼ^♯ ∘ pairAwayEquiv` is
  `tripleAwayEquiv ∘ faceAᵢⱼ`.

Each is an instance of the uniqueness of maps out of a localization
(`IsLocalization.ringHom_ext` over `B ⊗[A] B`, on the two-base structure maps): both
composites restrict to the same map of the base rings, computed through the elementwise
`ΓSpecIso`-naturality (`ΓSpecIso_inv_appTop`) and the pure-tensor face compatibilities
of `AlgebraicJacobian.Algebra.PiAssembly`.  This is where the pi-ext discipline of the
recon note is realized: extensionality is invoked over `B ⊗[A] B` — where the components
are `Away` localizations — never over `A`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

set_option quotPrecheck false in
local notation "XB" => (overSpec k B).left
set_option quotPrecheck false in
local notation "Sq" => (overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "Scb" => (overSpec k (B ⊗[A] (B ⊗[A] B))).left
set_option quotPrecheck false in
local notation "q₁" => (Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "q₂" => (Over.overSpecMap (tensorInr (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "f₁₂" => (Over.overSpecMap (tensorFace₁₂ (k := k) (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "f₁₃" => (Over.overSpecMap (tensorFace₁₃ (k := k) (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "f₂₃" => (Over.overSpecMap (tensorFace₂₃ (k := k) (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "Δs" => (Over.overSpecMap (tensorMul (k := k) (A := A) (B := B))).left


-- Reactivate the section-ring algebra structures of
-- `AlgebraicJacobian.Picard.WitnessAway` (they are `local instance`s there).
attribute [local instance] specSectionsAlgebra overSpecSectionsAlgebra
  overSpecSectionsAlgebraSq overSpecSectionsAlgebraScb algebraA_sections
  isScalarTower_sections isScalarTower_sections_basicOpen

namespace Over

variable {𝒩 : ((overSpec k B).left).PointedCover}
variable {γ : ((overSpec k B).left).unitsCocycle 𝒩}
variable (P : 𝒩.BasicRefinement)
/-! ## Intertwining of the section-ring restriction maps with the algebra-side maps -/

/-- The `Δ`-pullback between basic-open section rings intertwines the structure maps
over the multiplication `B ⊗[A] B → B`. -/
private lemma appLE_algebraMap_diag (i j : P.ι) (w : B ⊗[A] B) :
    ((Δs).appLE ((Sq).basicOpen (pairSection P i j)) ((XB).basicOpen (P.r i * P.r j))
        (basicOpen_mul_le_diag_pairSection P i j)).hom
        (algebraMap (B ⊗[A] B) Γ(Sq, (Sq).basicOpen (pairSection P i j)) w)
      = algebraMap B Γ(XB, (XB).basicOpen (P.r i * P.r j))
          (Algebra.TensorProduct.lmul' A (S := B) w) := by
  refine (appLE_restrict_top (Δs) (basicOpen_mul_le_diag_pairSection P i j)
    ((Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] B))).inv.hom w)).trans ?_
  refine (congrArg (((XB).presheaf.map (homOfLE le_top).op).hom)
    (ΓSpecIso_inv_appTop
      (CommRingCat.ofHom (tensorMul (k := k) (A := A) (B := B)).toRingHom) w)).trans ?_
  rfl

/-- The `f₂₃`-pullback between basic-open section rings intertwines the structure maps
over the coface `descentFace₂₃`. -/
private lemma appLE_algebraMap_face₂₃ (i j l : P.ι) (w : B ⊗[A] B) :
    ((f₂₃).appLE ((Sq).basicOpen (pairSection P j l)) ((Scb).basicOpen (tripleSection P i j l))
        (basicOpen_tripleSection_le_f₂₃ P i j l)).hom
        (algebraMap (B ⊗[A] B) Γ(Sq, (Sq).basicOpen (pairSection P j l)) w)
      = algebraMap (B ⊗[A] (B ⊗[A] B)) Γ(Scb, (Scb).basicOpen (tripleSection P i j l))
          (Module.descentFace₂₃ A B w) := by
  refine (appLE_restrict_top (f₂₃) (basicOpen_tripleSection_le_f₂₃ P i j l)
    ((Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] B))).inv.hom w)).trans ?_
  refine (congrArg (((Scb).presheaf.map (homOfLE le_top).op).hom)
    (ΓSpecIso_inv_appTop
      (CommRingCat.ofHom (tensorFace₂₃ (k := k) (A := A) (B := B)).toRingHom) w)).trans ?_
  rfl

/-- The `f₁₂`-pullback between basic-open section rings intertwines the structure maps
over the coface `descentFace₁₂`. -/
private lemma appLE_algebraMap_face₁₂ (i j l : P.ι) (w : B ⊗[A] B) :
    ((f₁₂).appLE ((Sq).basicOpen (pairSection P i j)) ((Scb).basicOpen (tripleSection P i j l))
        (basicOpen_tripleSection_le_f₁₂ P i j l)).hom
        (algebraMap (B ⊗[A] B) Γ(Sq, (Sq).basicOpen (pairSection P i j)) w)
      = algebraMap (B ⊗[A] (B ⊗[A] B)) Γ(Scb, (Scb).basicOpen (tripleSection P i j l))
          (Module.descentFace₁₂ A B w) := by
  refine (appLE_restrict_top (f₁₂) (basicOpen_tripleSection_le_f₁₂ P i j l)
    ((Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] B))).inv.hom w)).trans ?_
  refine (congrArg (((Scb).presheaf.map (homOfLE le_top).op).hom)
    (ΓSpecIso_inv_appTop
      (CommRingCat.ofHom (tensorFace₁₂ (k := k) (A := A) (B := B)).toRingHom) w)).trans ?_
  rfl

/-- The `f₁₃`-pullback between basic-open section rings intertwines the structure maps
over the coface `descentFace₁₃`. -/
private lemma appLE_algebraMap_face₁₃ (i j l : P.ι) (w : B ⊗[A] B) :
    ((f₁₃).appLE ((Sq).basicOpen (pairSection P i l)) ((Scb).basicOpen (tripleSection P i j l))
        (basicOpen_tripleSection_le_f₁₃ P i j l)).hom
        (algebraMap (B ⊗[A] B) Γ(Sq, (Sq).basicOpen (pairSection P i l)) w)
      = algebraMap (B ⊗[A] (B ⊗[A] B)) Γ(Scb, (Scb).basicOpen (tripleSection P i j l))
          (Module.descentFace₁₃ A B w) := by
  refine (appLE_restrict_top (f₁₃) (basicOpen_tripleSection_le_f₁₃ P i j l)
    ((Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] B))).inv.hom w)).trans ?_
  refine (congrArg (((Scb).presheaf.map (homOfLE le_top).op).hom)
    (ΓSpecIso_inv_appTop
      (CommRingCat.ofHom (tensorFace₁₃ (k := k) (A := A) (B := B)).toRingHom) w)).trans ?_
  rfl

set_option linter.unusedSectionVars false in
/-- The index-wise collapse `componentCollapse` on structure-map images: it is the
multiplication `B ⊗[A] B → B`, followed by the structure map. -/
private lemma componentCollapse_algebraMap (i j : P.ι) (w : B ⊗[A] B) :
    letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r i))
      Γ(XB, (XB).basicOpen (P.r j))
    IsLocalization.AwayCover.componentCollapse Γ(XB, ⊤) P.r
        (fun i' => Γ(XB, (XB).basicOpen (P.r i')))
        (fun i' j' => Γ(XB, (XB).basicOpen (P.r i' * P.r j'))) i j
        (algebraMap (B ⊗[A] B)
          (Γ(XB, (XB).basicOpen (P.r i)) ⊗[A] Γ(XB, (XB).basicOpen (P.r j))) w)
      = algebraMap B Γ(XB, (XB).basicOpen (P.r i * P.r j))
          (Algebra.TensorProduct.lmul' A (S := B) w) := by
  letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r i))
    Γ(XB, (XB).basicOpen (P.r j))
  induction w with
  | zero => simp only [map_zero]
  | tmul x y =>
      change IsLocalization.AwayCover.componentCollapse Γ(XB, ⊤) P.r
          (fun i' => Γ(XB, (XB).basicOpen (P.r i')))
          (fun i' j' => Γ(XB, (XB).basicOpen (P.r i' * P.r j'))) i j
          (algebraMap B Γ(XB, (XB).basicOpen (P.r i)) x
            ⊗ₜ[A] algebraMap B Γ(XB, (XB).basicOpen (P.r j)) y)
        = algebraMap B Γ(XB, (XB).basicOpen (P.r i * P.r j))
            (Algebra.TensorProduct.lmul' A (S := B) (x ⊗ₜ[A] y))
      rw [IsLocalization.AwayCover.componentCollapse_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul,
        show algebraMap B Γ(XB, (XB).basicOpen (P.r i)) x
            = algebraMap Γ(XB, ⊤) Γ(XB, (XB).basicOpen (P.r i))
                ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom x) from rfl,
        show algebraMap B Γ(XB, (XB).basicOpen (P.r j)) y
            = algebraMap Γ(XB, ⊤) Γ(XB, (XB).basicOpen (P.r j))
                ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom y) from rfl,
        AlgHom.commutes, AlgHom.commutes, ← map_mul]
      exact (congrArg (algebraMap Γ(XB, ⊤) Γ(XB, (XB).basicOpen (P.r i * P.r j)))
        (map_mul ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom) x y).symm).trans rfl
  | add x y hx hy =>
      rw [map_add, map_add, map_add, map_add, hx, hy]

/-- The `Δ`-pullback of the two-base identification is the index-wise collapse. -/
lemma pairAwayEquiv_appLE_diag (i j : P.ι)
    (t : Γ(XB, (XB).basicOpen (P.r i)) ⊗[A] Γ(XB, (XB).basicOpen (P.r j))) :
    ((Δs).appLE ((Sq).basicOpen (pairSection P i j)) ((XB).basicOpen (P.r i * P.r j))
        (basicOpen_mul_le_diag_pairSection P i j)).hom (pairAwayEquiv P i j t)
      = IsLocalization.AwayCover.componentCollapse Γ(XB, ⊤) P.r
          (fun i' => Γ(XB, (XB).basicOpen (P.r i')))
          (fun i' j' => Γ(XB, (XB).basicOpen (P.r i' * P.r j'))) i j t := by
  letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r i))
    Γ(XB, (XB).basicOpen (P.r j))
  haveI := isLocalization_awayElt P i
  haveI := isLocalization_awayElt P j
  haveI := IsLocalization.Away.isLocalization_away_tensor A B B (awayElt P i) (awayElt P j)
    Γ(XB, (XB).basicOpen (P.r i)) Γ(XB, (XB).basicOpen (P.r j))
  have key : (((Δs).appLE ((Sq).basicOpen (pairSection P i j))
        ((XB).basicOpen (P.r i * P.r j))
        (basicOpen_mul_le_diag_pairSection P i j)).hom).comp
        (pairAwayEquiv P i j).toAlgHom.toRingHom
      = (IsLocalization.AwayCover.componentCollapse Γ(XB, ⊤) P.r
          (fun i' => Γ(XB, (XB).basicOpen (P.r i')))
          (fun i' j' => Γ(XB, (XB).basicOpen (P.r i' * P.r j'))) i j).toRingHom := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers ((awayElt P i ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] awayElt P j)))
    refine RingHom.ext fun w => ?_
    change ((Δs).appLE ((Sq).basicOpen (pairSection P i j))
        ((XB).basicOpen (P.r i * P.r j)) (basicOpen_mul_le_diag_pairSection P i j)).hom
        (pairAwayEquiv P i j (algebraMap (B ⊗[A] B)
          (Γ(XB, (XB).basicOpen (P.r i)) ⊗[A] Γ(XB, (XB).basicOpen (P.r j))) w))
      = IsLocalization.AwayCover.componentCollapse Γ(XB, ⊤) P.r
          (fun i' => Γ(XB, (XB).basicOpen (P.r i')))
          (fun i' j' => Γ(XB, (XB).basicOpen (P.r i' * P.r j'))) i j
          (algebraMap (B ⊗[A] B)
            (Γ(XB, (XB).basicOpen (P.r i)) ⊗[A] Γ(XB, (XB).basicOpen (P.r j))) w)
    rw [(pairAwayEquiv P i j).commutes w, appLE_algebraMap_diag P i j w,
      componentCollapse_algebraMap P i j w]
  exact DFunLike.congr_fun key t

set_option linter.unusedSectionVars false in
/-- Elementwise form of the Layer-I face compatibility `faceA₂₃_comp_tensorMap`. -/
private lemma faceA₂₃_algebraMap (i j l : P.ι) (w : B ⊗[A] B) :
    letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r j))
      Γ(XB, (XB).basicOpen (P.r l))
    letI := IsLocalization.Away.tensorAwayAlgebra A B (B ⊗[A] B) Γ(XB, (XB).basicOpen (P.r i))
      (Γ(XB, (XB).basicOpen (P.r j)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l)))
    Algebra.TensorProduct.faceA₂₃ A (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l
        (algebraMap (B ⊗[A] B)
          (Γ(XB, (XB).basicOpen (P.r j)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l))) w)
      = algebraMap (B ⊗[A] (B ⊗[A] B))
          (Γ(XB, (XB).basicOpen (P.r i))
            ⊗[A] (Γ(XB, (XB).basicOpen (P.r j)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l))))
          (Module.descentFace₂₃ A B w) := by
  letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r j))
    Γ(XB, (XB).basicOpen (P.r l))
  exact DFunLike.congr_fun (IsLocalization.AwayCover.faceA₂₃_comp_tensorMap
    (A := A) B (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l) w

set_option linter.unusedSectionVars false in
/-- Elementwise form of the Layer-I face compatibility `faceA₁₂_comp_tensorMap`. -/
private lemma faceA₁₂_algebraMap (i j l : P.ι) (w : B ⊗[A] B) :
    letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r j))
      Γ(XB, (XB).basicOpen (P.r l))
    letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r i))
      Γ(XB, (XB).basicOpen (P.r j))
    letI := IsLocalization.Away.tensorAwayAlgebra A B (B ⊗[A] B) Γ(XB, (XB).basicOpen (P.r i))
      (Γ(XB, (XB).basicOpen (P.r j)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l)))
    Algebra.TensorProduct.faceA₁₂ A (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l
        (algebraMap (B ⊗[A] B)
          (Γ(XB, (XB).basicOpen (P.r i)) ⊗[A] Γ(XB, (XB).basicOpen (P.r j))) w)
      = algebraMap (B ⊗[A] (B ⊗[A] B))
          (Γ(XB, (XB).basicOpen (P.r i))
            ⊗[A] (Γ(XB, (XB).basicOpen (P.r j)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l))))
          (Module.descentFace₁₂ A B w) := by
  letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r j))
    Γ(XB, (XB).basicOpen (P.r l))
  exact DFunLike.congr_fun (IsLocalization.AwayCover.faceA₁₂_comp_tensorMap
    (A := A) B (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l) w

set_option linter.unusedSectionVars false in
/-- Elementwise form of the Layer-I face compatibility `faceA₁₃_comp_tensorMap`. -/
private lemma faceA₁₃_algebraMap (i j l : P.ι) (w : B ⊗[A] B) :
    letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r j))
      Γ(XB, (XB).basicOpen (P.r l))
    letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r i))
      Γ(XB, (XB).basicOpen (P.r l))
    letI := IsLocalization.Away.tensorAwayAlgebra A B (B ⊗[A] B) Γ(XB, (XB).basicOpen (P.r i))
      (Γ(XB, (XB).basicOpen (P.r j)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l)))
    Algebra.TensorProduct.faceA₁₃ A (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l
        (algebraMap (B ⊗[A] B)
          (Γ(XB, (XB).basicOpen (P.r i)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l))) w)
      = algebraMap (B ⊗[A] (B ⊗[A] B))
          (Γ(XB, (XB).basicOpen (P.r i))
            ⊗[A] (Γ(XB, (XB).basicOpen (P.r j)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l))))
          (Module.descentFace₁₃ A B w) := by
  letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r j))
    Γ(XB, (XB).basicOpen (P.r l))
  exact DFunLike.congr_fun (IsLocalization.AwayCover.faceA₁₃_comp_tensorMap
    (A := A) B (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l) w

/-- The `f₂₃`-pullback of the two-base identification is the index-wise face
`faceA₂₃`. -/
lemma tripleAwayEquiv_faceA₂₃ (i j l : P.ι)
    (t : Γ(XB, (XB).basicOpen (P.r j)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l))) :
    tripleAwayEquiv P i j l
        (Algebra.TensorProduct.faceA₂₃ A (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l t)
      = ((f₂₃).appLE ((Sq).basicOpen (pairSection P j l))
          ((Scb).basicOpen (tripleSection P i j l))
          (basicOpen_tripleSection_le_f₂₃ P i j l)).hom (pairAwayEquiv P j l t) := by
  letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r j))
    Γ(XB, (XB).basicOpen (P.r l))
  haveI := isLocalization_awayElt P j
  haveI := isLocalization_awayElt P l
  haveI := IsLocalization.Away.isLocalization_away_tensor A B B (awayElt P j) (awayElt P l)
    Γ(XB, (XB).basicOpen (P.r j)) Γ(XB, (XB).basicOpen (P.r l))
  letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r j))
    Γ(XB, (XB).basicOpen (P.r l))
  haveI := IsLocalization.Away.tensorAwayScalarTower A B B Γ(XB, (XB).basicOpen (P.r j))
    Γ(XB, (XB).basicOpen (P.r l))
  letI := IsLocalization.Away.tensorAwayAlgebra A B (B ⊗[A] B)
    Γ(XB, (XB).basicOpen (P.r i))
    (Γ(XB, (XB).basicOpen (P.r j)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l)))
  have key : ((tripleAwayEquiv (A := A) P i j l).toAlgHom.toRingHom).comp
        (Algebra.TensorProduct.faceA₂₃ A
          (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l).toRingHom
      = (((f₂₃).appLE ((Sq).basicOpen (pairSection P j l))
          ((Scb).basicOpen (tripleSection P i j l))
          (basicOpen_tripleSection_le_f₂₃ P i j l)).hom).comp
        (pairAwayEquiv P j l).toAlgHom.toRingHom := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers ((awayElt P j ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] awayElt P l)))
    refine RingHom.ext fun w => ?_
    change tripleAwayEquiv P i j l
        (Algebra.TensorProduct.faceA₂₃ A (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l
          (algebraMap (B ⊗[A] B) _ w))
      = ((f₂₃).appLE _ _ _).hom (pairAwayEquiv P j l (algebraMap (B ⊗[A] B) _ w))
    rw [(pairAwayEquiv P j l).commutes w, appLE_algebraMap_face₂₃ P i j l w,
      faceA₂₃_algebraMap P i j l w, (tripleAwayEquiv (A := A) P i j l).commutes]
  exact DFunLike.congr_fun key t

/-- The `f₁₂`-pullback of the two-base identification is the index-wise face
`faceA₁₂`. -/
lemma tripleAwayEquiv_faceA₁₂ (i j l : P.ι)
    (t : Γ(XB, (XB).basicOpen (P.r i)) ⊗[A] Γ(XB, (XB).basicOpen (P.r j))) :
    tripleAwayEquiv P i j l
        (Algebra.TensorProduct.faceA₁₂ A (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l t)
      = ((f₁₂).appLE ((Sq).basicOpen (pairSection P i j))
          ((Scb).basicOpen (tripleSection P i j l))
          (basicOpen_tripleSection_le_f₁₂ P i j l)).hom (pairAwayEquiv P i j t) := by
  letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r i))
    Γ(XB, (XB).basicOpen (P.r j))
  haveI := isLocalization_awayElt P i
  haveI := isLocalization_awayElt P j
  haveI := IsLocalization.Away.isLocalization_away_tensor A B B (awayElt P i) (awayElt P j)
    Γ(XB, (XB).basicOpen (P.r i)) Γ(XB, (XB).basicOpen (P.r j))
  letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r j))
    Γ(XB, (XB).basicOpen (P.r l))
  haveI := IsLocalization.Away.tensorAwayScalarTower A B B Γ(XB, (XB).basicOpen (P.r j))
    Γ(XB, (XB).basicOpen (P.r l))
  letI := IsLocalization.Away.tensorAwayAlgebra A B (B ⊗[A] B)
    Γ(XB, (XB).basicOpen (P.r i))
    (Γ(XB, (XB).basicOpen (P.r j)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l)))
  have key : ((tripleAwayEquiv (A := A) P i j l).toAlgHom.toRingHom).comp
        (Algebra.TensorProduct.faceA₁₂ A
          (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l).toRingHom
      = (((f₁₂).appLE ((Sq).basicOpen (pairSection P i j))
          ((Scb).basicOpen (tripleSection P i j l))
          (basicOpen_tripleSection_le_f₁₂ P i j l)).hom).comp
        (pairAwayEquiv P i j).toAlgHom.toRingHom := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers ((awayElt P i ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] awayElt P j)))
    refine RingHom.ext fun w => ?_
    change tripleAwayEquiv P i j l
        (Algebra.TensorProduct.faceA₁₂ A (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l
          (algebraMap (B ⊗[A] B) _ w))
      = ((f₁₂).appLE _ _ _).hom (pairAwayEquiv P i j (algebraMap (B ⊗[A] B) _ w))
    rw [(pairAwayEquiv P i j).commutes w, appLE_algebraMap_face₁₂ P i j l w,
      faceA₁₂_algebraMap P i j l w, (tripleAwayEquiv (A := A) P i j l).commutes]
  exact DFunLike.congr_fun key t

/-- The `f₁₃`-pullback of the two-base identification is the index-wise face
`faceA₁₃`. -/
lemma tripleAwayEquiv_faceA₁₃ (i j l : P.ι)
    (t : Γ(XB, (XB).basicOpen (P.r i)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l))) :
    tripleAwayEquiv P i j l
        (Algebra.TensorProduct.faceA₁₃ A (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l t)
      = ((f₁₃).appLE ((Sq).basicOpen (pairSection P i l))
          ((Scb).basicOpen (tripleSection P i j l))
          (basicOpen_tripleSection_le_f₁₃ P i j l)).hom (pairAwayEquiv P i l t) := by
  letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r i))
    Γ(XB, (XB).basicOpen (P.r l))
  haveI := isLocalization_awayElt P i
  haveI := isLocalization_awayElt P l
  haveI := IsLocalization.Away.isLocalization_away_tensor A B B (awayElt P i) (awayElt P l)
    Γ(XB, (XB).basicOpen (P.r i)) Γ(XB, (XB).basicOpen (P.r l))
  letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r j))
    Γ(XB, (XB).basicOpen (P.r l))
  haveI := IsLocalization.Away.tensorAwayScalarTower A B B Γ(XB, (XB).basicOpen (P.r j))
    Γ(XB, (XB).basicOpen (P.r l))
  letI := IsLocalization.Away.tensorAwayAlgebra A B (B ⊗[A] B)
    Γ(XB, (XB).basicOpen (P.r i))
    (Γ(XB, (XB).basicOpen (P.r j)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l)))
  have key : ((tripleAwayEquiv (A := A) P i j l).toAlgHom.toRingHom).comp
        (Algebra.TensorProduct.faceA₁₃ A
          (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l).toRingHom
      = (((f₁₃).appLE ((Sq).basicOpen (pairSection P i l))
          ((Scb).basicOpen (tripleSection P i j l))
          (basicOpen_tripleSection_le_f₁₃ P i j l)).hom).comp
        (pairAwayEquiv P i l).toAlgHom.toRingHom := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers ((awayElt P i ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] awayElt P l)))
    refine RingHom.ext fun w => ?_
    change tripleAwayEquiv P i j l
        (Algebra.TensorProduct.faceA₁₃ A (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l
          (algebraMap (B ⊗[A] B) _ w))
      = ((f₁₃).appLE _ _ _).hom (pairAwayEquiv P i l (algebraMap (B ⊗[A] B) _ w))
    rw [(pairAwayEquiv P i l).commutes w, appLE_algebraMap_face₁₃ P i j l w,
      faceA₁₃_algebraMap P i j l w, (tripleAwayEquiv (A := A) P i j l).commutes]
  exact DFunLike.congr_fun key t

end Over

end AlgebraicGeometry
