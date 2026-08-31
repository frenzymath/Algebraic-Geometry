/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AlgebraicJacobian.Picard.DivSchemeFamilySide
import AlgebraicJacobian.Cohomology.RelativeSectionsLinear
import AlgebraicJacobian.Curve.BaseFieldTransition
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# A residue-field point over a relative-curve point

For a point `z` of `C_R`, this file records the canonical point of the residue-field
base-change `C_{κ(p)}` lying over `z`, where `p` is the image of `z` in `Spec R`.
The construction is point-free at the scheme level: the residue-field map of the structure
morphism supplies the second leg, and the relative-curve pullback square supplies the lift.
This is the small geometric bridge needed when a fibre-order statement is proved first over
`κ(p)` and then consumed at a total-space point.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits TopologicalSpace MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]

/-- The base point of `z : C_R`, viewed as a point of `Spec R`. -/
noncomputable def relCurveBasePoint (z : relCurve C R) : PrimeSpectrum R :=
  (snd C (overSpec k R)).left z

/-- The lift of `z` to the residue-field base-change of the relative curve. -/
noncomputable def relCurveResiduePoint
    (z : relCurve C R) :
    relCurve C (relCurveBasePoint C R z).asIdeal.ResidueField := by
  let f : relCurve C R ⟶ Spec (CommRingCat.of R) :=
    (snd C (overSpec k R)).left
  let p : Spec (CommRingCat.of R) := relCurveBasePoint C R z
  let K := p.asIdeal.ResidueField
  let e := Scheme.Spec.residueFieldIso (CommRingCat.of R) p
  let q : Spec ((relCurve C R).residueField z) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (e.inv ≫ f.residueFieldMap z)
  have hq :
      (relCurve C R).fromSpecResidueField z ≫ f =
        q ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    simp only [q, e, K, Category.assoc, ← Spec.map_comp]
    rfl
  let hpb := Over.isPullback_whiskerLeft_left C (overSpecMap (k := k) R K)
  let l : Spec ((relCurve C R).residueField z) ⟶ relCurve C K :=
    hpb.lift ((relCurve C R).fromSpecResidueField z) q hq
  exact l (default : Spec ((relCurve C R).residueField z))

/-- The residue-field point maps back to the original total-space point. -/
theorem relCurveMap_relCurveResiduePoint
    (z : relCurve C R) :
    (relCurveMap C R (relCurveBasePoint C R z).asIdeal.ResidueField)
        (relCurveResiduePoint C R z) = z := by
  let f : relCurve C R ⟶ Spec (CommRingCat.of R) :=
    (snd C (overSpec k R)).left
  let p : Spec (CommRingCat.of R) := relCurveBasePoint C R z
  let K := p.asIdeal.ResidueField
  let e := Scheme.Spec.residueFieldIso (CommRingCat.of R) p
  let q : Spec ((relCurve C R).residueField z) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (e.inv ≫ f.residueFieldMap z)
  have hq :
      (relCurve C R).fromSpecResidueField z ≫ f =
        q ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    simp only [q, e, K, Category.assoc, ← Spec.map_comp]
    rfl
  let hpb := Over.isPullback_whiskerLeft_left C (overSpecMap (k := k) R K)
  let l : Spec ((relCurve C R).residueField z) ⟶ relCurve C K :=
    hpb.lift ((relCurve C R).fromSpecResidueField z) q hq
  have hl : l ≫ relCurveMap C R K = (relCurve C R).fromSpecResidueField z :=
    hpb.lift_fst _ _ _
  change (relCurveMap C R K) (l default) = z
  rw [← Scheme.Hom.comp_apply, hl]
  exact Scheme.fromSpecResidueField_apply _ _

/-- The inclusion of a residue fibre in the relative curve is injective on points. -/
theorem relCurveMap_residueField_injective (p : PrimeSpectrum R) :
    Function.Injective
      (relCurveMap C R p.asIdeal.ResidueField).base := by
  let K := p.asIdeal.ResidueField
  let e := Scheme.Spec.residueFieldIso (CommRingCat.of R) p
  have hfac : Spec.map (CommRingCat.ofHom (algebraMap R K)) =
      Spec.map e.hom ≫ (Spec (CommRingCat.of R)).fromSpecResidueField p := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    simp [e, K, Category.assoc, ← Spec.map_comp]
  letI : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    rw [hfac]
    infer_instance
  letI : IsPreimmersion (overSpecMap (k := k) R K).left := by
    rw [overSpecMap_left]
    infer_instance
  let hpb := Over.isPullback_whiskerLeft_left C (overSpecMap (k := k) R K)
  haveI : IsPreimmersion (relCurveMap C R K) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) hpb.flip inferInstance
  exact (relCurveMap C R K).isEmbedding.injective

/-- A residue-fibre point maps to a total-space point lying over the chosen prime. -/
theorem relCurveBasePoint_relCurveMap_residueField (p : PrimeSpectrum R)
    (z : relCurve C p.asIdeal.ResidueField) :
    relCurveBasePoint C R
        ((relCurveMap C R p.asIdeal.ResidueField).base z) = p := by
  let K := p.asIdeal.ResidueField
  change (relCurveMap C R K ≫ (snd C (overSpec k R)).left) z = p
  rw [relCurveMap_snd]
  change (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      ((snd C (overSpec k K)).left z) = p
  letI : Subsingleton (PrimeSpectrum K) :=
    PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr (Field.toIsField K)
  have hz : (snd C (overSpec k K)).left z = IsLocalRing.closedPoint K := by
    change (_ : PrimeSpectrum K) = IsLocalRing.closedPoint K
    exact Subsingleton.elim _ _
  rw [hz]
  apply PrimeSpectrum.ext
  rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal]
  simp only [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot]
  rw [← RingHom.ker_eq_comap_bot]
  exact Ideal.ker_algebraMap_residueField (I := p.asIdeal)

/-- Transporting a residue-fibre point along an equality of base primes commutes with
its map to the total relative curve. -/
theorem relCurveMap_residueField_cast {q p : PrimeSpectrum R} (h : q = p)
    (z : relCurve C q.asIdeal.ResidueField) :
    (relCurveMap C R p.asIdeal.ResidueField).base (h ▸ z) =
      (relCurveMap C R q.asIdeal.ResidueField).base z := by
  cases h
  rfl

/-- Every point of a residue fibre is the canonical residue lift of its image in the
total relative curve, in an explicit dependent-cast spelling. -/
theorem relCurveResiduePoint_map_cast (p : PrimeSpectrum R)
    (z : relCurve C p.asIdeal.ResidueField) :
    let zR : relCurve C R := (relCurveMap C R p.asIdeal.ResidueField).base z
    let hp : relCurveBasePoint C R zR = p :=
      relCurveBasePoint_relCurveMap_residueField C R p z
    Eq.ndrec
        (motive := fun q : PrimeSpectrum R => relCurve C q.asIdeal.ResidueField)
        (relCurveResiduePoint C R zR) hp = z := by
  dsimp
  let zR : relCurve C R := (relCurveMap C R p.asIdeal.ResidueField).base z
  have hp : relCurveBasePoint C R zR = p :=
    relCurveBasePoint_relCurveMap_residueField C R p z
  let z' : relCurve C p.asIdeal.ResidueField :=
    Eq.ndrec
      (motive := fun q : PrimeSpectrum R => relCurve C q.asIdeal.ResidueField)
      (relCurveResiduePoint C R zR) hp
  have hz' : (relCurveMap C R p.asIdeal.ResidueField).base z' = zR := by
    rw [show (relCurveMap C R p.asIdeal.ResidueField).base z' =
        (relCurveMap C R (relCurveBasePoint C R zR).asIdeal.ResidueField).base
          (relCurveResiduePoint C R zR) by
      exact relCurveMap_residueField_cast C R hp (relCurveResiduePoint C R zR)]
    exact relCurveMap_relCurveResiduePoint C R zR
  apply relCurveMap_residueField_injective C R p
  calc
    (relCurveMap C R p.asIdeal.ResidueField).base z' = zR := hz'
    _ = (relCurveMap C R p.asIdeal.ResidueField).base z := rfl

/-- The heterogeneous-equality spelling of `relCurveResiduePoint_map_cast`. -/
theorem relCurveResiduePoint_map_heq (p : PrimeSpectrum R)
    (z : relCurve C p.asIdeal.ResidueField) :
    let zR : relCurve C R := (relCurveMap C R p.asIdeal.ResidueField).base z
    HEq (relCurveResiduePoint C R zR) z := by
  dsimp
  let zR : relCurve C R := (relCurveMap C R p.asIdeal.ResidueField).base z
  have hp : relCurveBasePoint C R zR = p :=
    relCurveBasePoint_relCurveMap_residueField C R p z
  let z' : relCurve C p.asIdeal.ResidueField :=
    Eq.ndrec
      (motive := fun q : PrimeSpectrum R => relCurve C q.asIdeal.ResidueField)
      (relCurveResiduePoint C R zR) hp
  have hz' : z' = z := by
    exact relCurveResiduePoint_map_cast C R p z
  have hcast : HEq (relCurveResiduePoint C R zR) z' := by
    symm
    change HEq
      (Eq.ndrec
        (motive := fun q : PrimeSpectrum R => relCurve C q.asIdeal.ResidueField)
        (relCurveResiduePoint C R zR) hp)
      (relCurveResiduePoint C R zR)
    exact eqRec_heq
      (φ := fun q : PrimeSpectrum R => relCurve C q.asIdeal.ResidueField)
      hp (relCurveResiduePoint C R zR)
  exact hcast.trans (heq_of_eq hz')

/-- Relative-curve base change pulls a pinned chart back to the corresponding pinned chart.
This is the Bool-indexed form of `relCurveMap_preimage`. -/
theorem relCurveMap_preimage_relPinnedChart
    {π : C.left ⟶ P1 k} [IsFinite π]
    (b : Bool) (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R']
    [IsScalarTower k R R'] :
    relCurveMap C R R' ⁻¹ᵁ relPinnedChart C R π b = relPinnedChart C R' π b := by
  cases b
  · exact relCurveMap_preimage C R R' (fiberChart₀ π)
  · exact relCurveMap_preimage C R R' (fiberChart₁ π)

/-- A point in a pinned chart lifts to the corresponding residue-field pinned chart. -/
theorem relCurveResiduePoint_mem_relPinnedChart
    {π : C.left ⟶ P1 k} [IsFinite π] (b : Bool)
    {z : relCurve C R} (hz : z ∈ relPinnedChart C R π b) :
    relCurveResiduePoint C R z ∈
      relPinnedChart C (relCurveBasePoint C R z).asIdeal.ResidueField π b := by
  rw [← relCurveMap_preimage_relPinnedChart C R b]
  change (relCurveMap C R (relCurveBasePoint C R z).asIdeal.ResidueField)
      (relCurveResiduePoint C R z) ∈ relPinnedChart C R π b
  rwa [relCurveMap_relCurveResiduePoint]

end AlgebraicGeometry
