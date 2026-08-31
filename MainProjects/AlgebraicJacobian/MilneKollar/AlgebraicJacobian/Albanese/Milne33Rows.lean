/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.DifferenceMap

/-!
# Rows, the diagonal, and the explicit representative of Milne's difference map

Infrastructure for Milne Lemma 3.3 substep 2 (hard direction) and substep 3,
per `informal/m33-spec.md` (D3/D4). For the self-product `Y := X ×_{k̄} X` of a
smooth variety and the difference rational map `Φ = differenceRationalMap f hover`
(`Albanese/DifferenceMap.lean`), this file provides:

* `grpObjUnitPoint` — the unit section `e : Spec k̄ ⟶ G.left` of a group scheme,
  with `grpObjUnitPoint_comp_hom`;
* `GrpObj.lift_diff_self` / `pullback_lift_diff_self` — the group identity
  `a·a⁻¹ = e` for `T`-points, categorically and at scheme level (the diagonal
  triviality core of Milne's `Φ(x,x) = e`);
* `selfDiag`, `rowSnd` — the diagonal `x ↦ (x,x)` and, for a rational point
  `u`, the row `x ↦ (x,u)`, as honest scheme morphisms, with the point-collision
  lemmas identifying their `k̄`-point composites as `pullback.lift`s;
* `diffPairingRep` — the explicit partial-map representative
  `(precompDiffPairing f hover).compHom (grpObjDiffLeft G)` of `Φ`, defined on
  `pr₁⁻¹(Dom f₀) ⊓ pr₂⁻¹(Dom f₀)`, with `diffPairingRep_toRationalMap`;
* `toPartialMap_hom_eq_diffPairingRep` — the **representative agreement**: the
  maximal representative `Φ.toPartialMap` and `diffPairingRep` agree, as honest
  morphisms, on the full intersection of their domains (reduced source /
  separated target agreement, `PartialMap.equiv_iff_of_isSeparated`).

Blueprint reference: `lem:milne_codim1_indeterminacy` (Milne, *Abelian
Varieties*, §I.3 Lemma 3.3, pp. 17–18; `abelian-varieties:page-0023`).
-/

set_option autoImplicit false

universe u

open CategoryTheory CartesianMonoidalCategory MonoidalCategory Limits TopologicalSpace
open scoped CategoryTheory.MonObj

namespace CategoryTheory.GrpObj

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

/-- **The difference of a `T`-point with itself is the unit**: pairing `a : T ⟶ G`
with itself and applying `GrpObj.diff G = fst / snd` gives the unit point
`toUnit T ≫ η[G]`. This is the group-theoretic core of Milne's "`Φ` sends `(x, x)`
to `e` if it is defined there" (Milne, *Abelian Varieties*, §I.3 p. 17). -/
lemma lift_diff_self {T : C} (G : C) [GrpObj G] (a : T ⟶ G) :
    lift a a ≫ diff G = toUnit T ≫ η[G] := by
  rw [diff, GrpObj.comp_div, lift_fst, lift_snd, div_self']
  rfl

end CategoryTheory.GrpObj

namespace AlgebraicGeometry

variable {kbar : Type u} [Field kbar]

/-! ## §1. The unit point of a group scheme over `k̄` -/

/-- The underlying scheme morphism `Spec k̄ ⟶ G.left` of the unit section
`η[G] : 𝟙_ (Over (Spec k̄)) ⟶ G` of a group scheme, typed against `Spec k̄`
(definitionally `(𝟙_ (Over (Spec k̄))).left`). -/
noncomputable def grpObjUnitPoint (G : Over (Spec (.of kbar))) [GrpObj G] :
    Spec (.of kbar) ⟶ G.left :=
  η[G].left

/-- The unit point is a `k̄`-point: `e ≫ G.hom = 𝟙 (Spec k̄)`. -/
lemma grpObjUnitPoint_comp_hom (G : Over (Spec (.of kbar))) [GrpObj G] :
    grpObjUnitPoint G ≫ G.hom = 𝟙 (Spec (.of kbar)) :=
  Over.w η[G]

/-- **Scheme-level diagonal triviality core.** For an over-`k̄` morphism
`A : T ⟶ G.left` (structure map `t`), pairing `A` with itself and applying the
group difference gives the constant unit morphism: `⟨A, A⟩ ≫ (g,h ↦ g·h⁻¹) = t ≫ e`.
This is `CategoryTheory.GrpObj.lift_diff_self` transported through `Over.forget`. -/
lemma pullback_lift_diff_self (G : Over (Spec (.of kbar))) [GrpObj G]
    {T : Scheme.{u}} (t : T ⟶ Spec (.of kbar)) (A : T ⟶ G.left)
    (hA : A ≫ G.hom = t) :
    pullback.lift A A rfl ≫ grpObjDiffLeft G = t ≫ grpObjUnitPoint G := by
  have key := congrArg (fun m : Over.mk t ⟶ G => m.left)
    (GrpObj.lift_diff_self G (Over.homMk A hA))
  simp only [Over.comp_left, Over.lift_left, Over.homMk_left,
    Over.toUnit_left, Over.mk_hom] at key
  exact key

/-! ## §2. The diagonal and the rows of the self-product -/

variable (X : Over (Spec (.of kbar)))

/-- The diagonal morphism `x ↦ (x, x)` of the self-product `X ×_{k̄} X`. -/
noncomputable def selfDiag : X.left ⟶ pullback X.hom X.hom :=
  pullback.lift (𝟙 _) (𝟙 _) rfl

@[simp]
lemma selfDiag_fst : selfDiag X ≫ pullback.fst X.hom X.hom = 𝟙 X.left :=
  pullback.lift_fst _ _ _

@[simp]
lemma selfDiag_snd : selfDiag X ≫ pullback.snd X.hom X.hom = 𝟙 X.left :=
  pullback.lift_snd _ _ _

variable {X} in
/-- The row morphism `x ↦ (x, u)` through a rational point `u` (given as a
`k̄`-point `pt : Spec k̄ ⟶ X.left`): second coordinate frozen at `u`. -/
noncomputable def rowSnd (pt : Spec (.of kbar) ⟶ X.left) (hpt : pt ≫ X.hom = 𝟙 _) :
    X.left ⟶ pullback X.hom X.hom :=
  pullback.lift (𝟙 _) (X.hom ≫ pt)
    (by rw [Category.id_comp, Category.assoc, hpt, Category.comp_id])

variable {X} in
@[simp]
lemma rowSnd_fst (pt : Spec (.of kbar) ⟶ X.left) (hpt : pt ≫ X.hom = 𝟙 _) :
    rowSnd pt hpt ≫ pullback.fst X.hom X.hom = 𝟙 X.left :=
  pullback.lift_fst _ _ _

variable {X} in
@[simp]
lemma rowSnd_snd (pt : Spec (.of kbar) ⟶ X.left) (hpt : pt ≫ X.hom = 𝟙 _) :
    rowSnd pt hpt ≫ pullback.snd X.hom X.hom = X.hom ≫ pt :=
  pullback.lift_snd _ _ _

variable {X} in
/-- The row morphism `y ↦ (v, y)` through a rational point `v`: first coordinate
frozen at `v`. -/
noncomputable def rowFst (pt : Spec (.of kbar) ⟶ X.left) (hpt : pt ≫ X.hom = 𝟙 _) :
    X.left ⟶ pullback X.hom X.hom :=
  pullback.lift (X.hom ≫ pt) (𝟙 _)
    (by rw [Category.id_comp, Category.assoc, hpt, Category.comp_id])

variable {X} in
@[simp]
lemma rowFst_fst (pt : Spec (.of kbar) ⟶ X.left) (hpt : pt ≫ X.hom = 𝟙 _) :
    rowFst pt hpt ≫ pullback.fst X.hom X.hom = X.hom ≫ pt :=
  pullback.lift_fst _ _ _

variable {X} in
@[simp]
lemma rowFst_snd (pt : Spec (.of kbar) ⟶ X.left) (hpt : pt ≫ X.hom = 𝟙 _) :
    rowFst pt hpt ≫ pullback.snd X.hom X.hom = 𝟙 X.left :=
  pullback.lift_snd _ _ _

section PointCollision

variable {X}
variable (p q : Spec (.of kbar) ⟶ X.left)
  (hp : p ≫ X.hom = 𝟙 _) (hq : q ≫ X.hom = 𝟙 _)

/-- Composing a `k̄`-point `p` into the diagonal gives the pair-point `(p, p)`. -/
lemma comp_selfDiag :
    p ≫ selfDiag X = pullback.lift p p rfl := by
  apply pullback.hom_ext
  · rw [Category.assoc, selfDiag_fst, Category.comp_id, pullback.lift_fst]
  · rw [Category.assoc, selfDiag_snd, Category.comp_id, pullback.lift_snd]

/-- Composing a `k̄`-point `p` into the row through `q` gives the pair-point
`(p, q)`. -/
lemma comp_rowSnd :
    p ≫ rowSnd q hq = pullback.lift p q (by rw [hp, hq]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, rowSnd_fst, Category.comp_id, pullback.lift_fst]
  · rw [Category.assoc, rowSnd_snd, pullback.lift_snd, ← Category.assoc, hp,
      Category.id_comp]

/-- Composing a `k̄`-point `q` into the `rowFst` through `p` gives the pair-point
`(p, q)`. -/
lemma comp_rowFst :
    q ≫ rowFst p hp = pullback.lift p q (by rw [hp, hq]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, rowFst_fst, pullback.lift_fst, ← Category.assoc, hq,
      Category.id_comp]
  · rw [Category.assoc, rowFst_snd, Category.comp_id, pullback.lift_snd]

/-- **Point collision**: the image of the point of `p` under the row through `q`
equals the image of the point of `q` under the `rowFst` through `p` — both are
"the pair `(p, q)`". Stated on underlying points. -/
lemma rowSnd_base_eq_rowFst_base (s : ↥(Spec (.of kbar))) :
    (rowSnd q hq).base (p.base s) = (rowFst p hp).base (q.base s) := by
  have h : p ≫ rowSnd q hq = q ≫ rowFst p hp := by
    rw [comp_rowSnd p q hp hq, comp_rowFst p q hp hq]
  calc (rowSnd q hq).base (p.base s) = ((p ≫ rowSnd q hq).base) s := rfl
    _ = ((q ≫ rowFst p hp).base) s := by rw [h]
    _ = (rowFst p hp).base (q.base s) := rfl

/-- The image of the point of `p` under the diagonal equals its image under the
`rowFst` through `p` — both are "the pair `(p, p)`". -/
lemma selfDiag_base_eq_rowFst_base (s : ↥(Spec (.of kbar))) :
    (selfDiag X).base (p.base s) = (rowFst p hp).base (p.base s) := by
  have h : p ≫ selfDiag X = p ≫ rowFst p hp := by
    rw [comp_selfDiag p, comp_rowFst p p hp hp]
  calc (selfDiag X).base (p.base s) = ((p ≫ selfDiag X).base) s := rfl
    _ = ((p ≫ rowFst p hp).base) s := by rw [h]
    _ = (rowFst p hp).base (p.base s) := rfl

end PointCollision

/-! ## §3. The explicit representative of the difference map, and agreement -/

namespace Scheme.RationalMap

variable {X} {G : Over (Spec (.of kbar))}
  [Smooth X.hom] [GrpObj G] [LocallyOfFiniteType G.hom]

/-- **The explicit partial-map representative of Milne's difference map.**
`diffPairingRep f hover = precompDiffPairing ≫ (g,h ↦ g·h⁻¹)`, an honest
partial map with domain `Dom(f₀ ∘ pr₁) ⊓ Dom(f₀ ∘ pr₂) ⊇ Dom(f) ×_{k̄} Dom(f)`
representing `differenceRationalMap f hover`. -/
noncomputable def diffPairingRep
    (f : X.left.RationalMap G.left) (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsReduced X.left] [G.left.IsSeparated] :
    (pullback X.hom X.hom).PartialMap G.left :=
  (precompDiffPairing f hover).compHom (grpObjDiffLeft G)

/-- The explicit representative represents the difference map. -/
lemma diffPairingRep_toRationalMap
    (f : X.left.RationalMap G.left) (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsIntegral (pullback X.hom X.hom)] [IsReduced X.left] [G.left.IsSeparated] :
    (diffPairingRep f hover).toRationalMap = differenceRationalMap f hover := by
  rw [diffPairingRep, RationalMap.compHom_toRationalMap,
    precompDiffPairing_toRationalMap f hover]
  rfl

omit [LocallyOfFiniteType G.hom] in
/-- The domain of the explicit representative. -/
lemma diffPairingRep_domain
    (f : X.left.RationalMap G.left) (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsReduced X.left] [G.left.IsSeparated] :
    (diffPairingRep f hover).domain
      = (f.toPartialMap.precomp (pullback.fst X.hom X.hom)
          (isOpenMap_pullback_fst_self X)).domain
        ⊓ (f.toPartialMap.precomp (pullback.snd X.hom X.hom)
          (isOpenMap_pullback_snd_self X)).domain :=
  rfl

omit [LocallyOfFiniteType G.hom] in
/-- The `hom` of the explicit representative. -/
lemma diffPairingRep_hom
    (f : X.left.RationalMap G.left) (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsReduced X.left] [G.left.IsSeparated] :
    (diffPairingRep f hover).hom
      = (precompDiffPairing f hover).hom ≫ grpObjDiffLeft G :=
  rfl

/-- **Representative agreement.** The maximal representative
`(differenceRationalMap f hover).toPartialMap` of Milne's difference map and the
explicit pairing representative `diffPairingRep f hover` agree, as honest
morphisms, on *any* dense open contained in both domains (reduced source,
separated target: `PartialMap.equiv_iff_of_isSeparated_of_le`). This is the
bridge that lets rows and the diagonal be composed with the *maximal*
representative and still be computed by the explicit pairing formula. -/
lemma toPartialMap_restrict_hom_eq_diffPairingRep
    (f : X.left.RationalMap G.left) (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsIntegral (pullback X.hom X.hom)] [IsReduced X.left] [G.left.IsSeparated]
    [IsSeparated G.hom]
    (W : (pullback X.hom X.hom).Opens) (hW : Dense (W : Set ↥(pullback X.hom X.hom)))
    (h1 : W ≤ (differenceRationalMap f hover).toPartialMap.domain)
    (h2 : W ≤ (diffPairingRep f hover).domain) :
    ((differenceRationalMap f hover).toPartialMap.restrict W hW h1).hom
      = ((diffPairingRep f hover).restrict W hW h2).hom := by
  letI : X.left.Over (Spec (.of kbar)) := ⟨X.hom⟩
  letI : G.left.Over (Spec (.of kbar)) := ⟨G.hom⟩
  letI : (pullback X.hom X.hom).Over (Spec (.of kbar)) :=
    ⟨pullback.fst X.hom X.hom ≫ X.hom⟩
  letI : (pullback G.hom G.hom).Over (Spec (.of kbar)) :=
    ⟨pullback.fst G.hom G.hom ≫ G.hom⟩
  haveI : IsSeparated (G.left ↘ Spec (.of kbar)) := ‹IsSeparated G.hom›
  haveI : (differenceRationalMap f hover).IsOver (Spec (.of kbar)) :=
    Scheme.RationalMap.isOver_iff.mpr (differenceRationalMap_compHom_over f hover)
  haveI : f.IsOver (Spec (.of kbar)) := Scheme.RationalMap.isOver_iff.mpr hover
  haveI : (pullback.fst X.hom X.hom).IsOver (Spec (.of kbar)) := ⟨rfl⟩
  haveI : (pullback.snd X.hom X.hom).IsOver (Spec (.of kbar)) :=
    ⟨pullback.condition.symm⟩
  haveI : (grpObjDiffLeft G).IsOver (Spec (.of kbar)) := ⟨grpObjDiffLeft_comp_hom G⟩
  haveI hpair : (precompDiffPairing f hover).IsOver (Spec (.of kbar)) := by
    rw [Scheme.PartialMap.isOver_iff]
    have e₁ : (f.toPartialMap.precomp (pullback.fst X.hom X.hom)
          (isOpenMap_pullback_fst_self X)).hom ≫ G.hom
        = (f.toPartialMap.precomp (pullback.fst X.hom X.hom)
          (isOpenMap_pullback_fst_self X)).domain.ι
            ≫ (pullback.fst X.hom X.hom ≫ X.hom) :=
      (Scheme.PartialMap.isOver_iff (S := Spec (.of kbar))).mp inferInstance
    change (precompDiffPairing f hover).hom ≫ pullback.fst G.hom G.hom ≫ G.hom
        = (precompDiffPairing f hover).domain.ι ≫ pullback.fst X.hom X.hom ≫ X.hom
    simp only [precompDiffPairing, pullback.lift_fst_assoc]
    rw [Category.assoc, e₁, ← Category.assoc, Scheme.homOfLE_ι]
  haveI hrep : (diffPairingRep f hover).IsOver (Spec (.of kbar)) := by
    rw [diffPairingRep]
    infer_instance
  have hequiv : ((differenceRationalMap f hover).toPartialMap).equiv
      (diffPairingRep f hover) := by
    rw [← Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.RationalMap.toRationalMap_toPartialMap,
      diffPairingRep_toRationalMap f hover]
  exact (Scheme.PartialMap.equiv_iff_of_isSeparated_of_le
    (S := Spec (.of kbar)) hW h1 h2).mp hequiv

/-- **Evaluation of the maximal representative through the pairing.** If
`j : T ⟶ Dom Φ₀` and `q : T ⟶ Dom (pairing)` restrict to the same morphism
into `X ×_{k̄} X`, then composing `j` with the maximal representative of the
difference map equals composing `q` with the explicit pairing formula. This is
the type-homogeneous consumer interface of the representative agreement: every
object in the statement lives in the `precompDiffPairing` world. -/
theorem comp_toPartialMap_hom_of_fac
    (f : X.left.RationalMap G.left) (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsIntegral (pullback X.hom X.hom)] [IsReduced X.left] [G.left.IsSeparated]
    [IsSeparated G.hom]
    {T : Scheme.{u}}
    (j : T ⟶ ↑(differenceRationalMap f hover).toPartialMap.domain)
    (q : T ⟶ ↑(precompDiffPairing f hover).domain)
    (hfac : j ≫ (differenceRationalMap f hover).toPartialMap.domain.ι
      = q ≫ (precompDiffPairing f hover).domain.ι) :
    j ≫ (differenceRationalMap f hover).toPartialMap.hom
      = q ≫ (precompDiffPairing f hover).hom ≫ grpObjDiffLeft G := by
  -- Dense intersection of the two domains.
  have hW'dense : Dense (((differenceRationalMap f hover).toPartialMap.domain
      ⊓ (diffPairingRep f hover).domain : (pullback X.hom X.hom).Opens) :
        Set ↥(pullback X.hom X.hom)) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact ((differenceRationalMap f hover).toPartialMap.dense_domain).inter_of_isOpen_left
      (diffPairingRep f hover).dense_domain
      (differenceRationalMap f hover).toPartialMap.domain.isOpen
  -- Full-intersection agreement, retyped into the pairing world.
  have hfull := toPartialMap_restrict_hom_eq_diffPairingRep f hover
    ((differenceRationalMap f hover).toPartialMap.domain
      ⊓ (diffPairingRep f hover).domain) hW'dense inf_le_left inf_le_right
  simp only [Scheme.PartialMap.restrict_hom] at hfull
  have hle2 : ((differenceRationalMap f hover).toPartialMap.domain
      ⊓ (diffPairingRep f hover).domain : (pullback X.hom X.hom).Opens)
      ≤ (precompDiffPairing f hover).domain :=
    (inf_le_right : _ ≤ (diffPairingRep f hover).domain)
  have hfull' : (pullback X.hom X.hom).homOfLE
        (inf_le_left : _ ⊓ (diffPairingRep f hover).domain
          ≤ (differenceRationalMap f hover).toPartialMap.domain)
        ≫ (differenceRationalMap f hover).toPartialMap.hom
      = (pullback X.hom X.hom).homOfLE hle2
        ≫ ((precompDiffPairing f hover).hom ≫ grpObjDiffLeft G) := hfull
  -- Factor `j` through the intersection.
  have hrange : Set.range (j ≫ (differenceRationalMap f hover).toPartialMap.domain.ι).base
      ⊆ Set.range ((differenceRationalMap f hover).toPartialMap.domain
        ⊓ (diffPairingRep f hover).domain : (pullback X.hom X.hom).Opens).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    rw [TopologicalSpace.Opens.coe_inf]
    constructor
    · change (j ≫ (differenceRationalMap f hover).toPartialMap.domain.ι).base t
        ∈ (differenceRationalMap f hover).toPartialMap.domain
      rw [show (j ≫ (differenceRationalMap f hover).toPartialMap.domain.ι).base t
        = (differenceRationalMap f hover).toPartialMap.domain.ι.base (j.base t) from rfl]
      exact (j.base t).2
    · change (j ≫ (differenceRationalMap f hover).toPartialMap.domain.ι).base t
        ∈ (diffPairingRep f hover).domain
      rw [hfac,
        show (q ≫ (precompDiffPairing f hover).domain.ι).base t
        = (precompDiffPairing f hover).domain.ι.base (q.base t) from rfl]
      exact (q.base t).2
  have hjWι : IsOpenImmersion.lift
        ((differenceRationalMap f hover).toPartialMap.domain
          ⊓ (diffPairingRep f hover).domain : (pullback X.hom X.hom).Opens).ι
        (j ≫ (differenceRationalMap f hover).toPartialMap.domain.ι) hrange
      ≫ ((differenceRationalMap f hover).toPartialMap.domain
          ⊓ (diffPairingRep f hover).domain : (pullback X.hom X.hom).Opens).ι
      = j ≫ (differenceRationalMap f hover).toPartialMap.domain.ι :=
    IsOpenImmersion.lift_fac _ _ _
  have hj' : j = IsOpenImmersion.lift _ _ hrange
      ≫ (pullback X.hom X.hom).homOfLE
        (inf_le_left : _ ⊓ (diffPairingRep f hover).domain
          ≤ (differenceRationalMap f hover).toPartialMap.domain) := by
    rw [← cancel_mono (differenceRationalMap f hover).toPartialMap.domain.ι,
      Category.assoc, Scheme.homOfLE_ι, hjWι]
  have hq' : q = IsOpenImmersion.lift _ _ hrange
      ≫ (pullback X.hom X.hom).homOfLE hle2 := by
    rw [← cancel_mono (precompDiffPairing f hover).domain.ι,
      Category.assoc, Scheme.homOfLE_ι, hjWι, hfac]
  rw [hj', hq', Category.assoc, hfull', Category.assoc]

end Scheme.RationalMap

end AlgebraicGeometry
