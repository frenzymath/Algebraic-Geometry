/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.EffectivityTwist
import AlgebraicJacobian.Picard.EffectivityCanonicity
import AlgebraicJacobian.Picard.EffectivityInvertibleAvoid

/-!
# Trivialization independence and flat trivializations ((C2) effectivity, brick E4)

The (B) deliverable of the E4 close and its constructive upgrade:

* `Over.exists_ratio_unit` — two piece trivializations of the same cocycle on the same
  piece differ by a **glued global unit** of the cover piece (the `𝒪ˣ`-sheaf axiom on
  the ratio, whose Čech coboundary the trivializing relations cancel);
* `Over.pieceDescentClass_congr` — **trivialization independence**: the descended
  per-piece class does not depend on the chosen trivialization — the comparison units
  differ by a descent coboundary (`Over.comparisonDescentUnit_twist`), and `picClass`
  is coboundary-invariant (`Module.IsDescentCocycle.picClass_descentCoboundary_mul`);
* `Over.exists_pieceComparisonUnit_eq_one` — **flattening**: on a piece whose descended
  class is trivial, some trivialization has comparison unit `1` on the nose —
  `picClass_eq_one_iff` produces the cobounding unit, the seams of
  `AlgebraicJacobian.Picard.EffectivityTwist` pull it back to a geometric unit `e`, and
  twisting by `e⁻¹` kills the comparison;
* `Over.exists_flat_pieceTrivialization_of_le` — the **localize-and-flatten** step: any
  trivialized piece `V₁ ∋ x` contains a basic affine `V ∋ x` on which the restricted
  descended class is trivial (the avoidance brick at the germ prime of `x`, through the
  restriction canonicity `pieceDescentClass_res`), so `V` carries a **flat**
  trivialization.  These flat pieces are what the refinement-splice glues.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]
variable (C : Over (Spec (.of k)))

set_option quotPrecheck false in
local notation "XA" => (C ⊗ overSpec k A).left
set_option quotPrecheck false in
local notation "XB" => (C ⊗ overSpec k B).left
set_option quotPrecheck false in
local notation "Xq" => (C ⊗ overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "u₁" => (C ◁ Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "u₂" => (C ◁ Over.overSpecMap (tensorInr (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "cg" => (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left
set_option quotPrecheck false in
local notation "cgq" =>
  (C ◁ Over.overSpecMap ((Algebra.ofId A (B ⊗[A] B)).restrictScalars k)).left

namespace Over

-- The base-piece `A`-algebra structure and the cover-piece `Γ(V)`-algebra structure.
attribute [local instance] Over.sectionsAlgebraA Over.pieceCoverAlgebra

/-- Ratio core: `a₁ ⋅ γ = b₁` and `a₂ ⋅ γ = b₂` give `a₂ ⋅ a₁⁻¹ = b₂ ⋅ b₁⁻¹`. -/
private lemma ratio_core {G : Type u} [CommGroup G] {a₁ b₁ a₂ b₂ γ : G}
    (h₁ : a₁ * γ = b₁) (h₂ : a₂ * γ = b₂) : a₂ * a₁⁻¹ = b₂ * b₁⁻¹ := by
  subst h₁; subst h₂
  group

/-- **Two piece trivializations differ by a glued global unit of the cover piece**: the
member-by-member ratio is Čech-compatible (the trivializing relations cancel the
cocycle), so it glues along the trimmed cover of the piece. -/
theorem exists_ratio_unit {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    {V : (XA).Opens} (T T' : PieceTrivialization C 𝒩 γ V) :
    ∃ e : Γ(XB, (cg) ⁻¹ᵁ V)ˣ, ∀ b : XB,
      T'.triv b = T.triv b
        * (XB).unitsRestrict (inf_le_right : 𝒩.opens b ⊓ (cg) ⁻¹ᵁ V ≤ _) e := by
  have hcompat : ∀ b b' : XB,
      (XB).unitsRestrict (inf_le_left :
          (𝒩.opens b ⊓ (cg) ⁻¹ᵁ V) ⊓ (𝒩.opens b' ⊓ (cg) ⁻¹ᵁ V) ≤ 𝒩.opens b ⊓ (cg) ⁻¹ᵁ V)
          (T'.triv b * (T.triv b)⁻¹)
        = (XB).unitsRestrict inf_le_right (T'.triv b' * (T.triv b')⁻¹) := by
    intro b b'
    have hle : (𝒩.opens b ⊓ (cg) ⁻¹ᵁ V) ⊓ (𝒩.opens b' ⊓ (cg) ⁻¹ᵁ V)
        ≤ (𝒩.opens b ⊓ 𝒩.opens b') ⊓ (cg) ⁻¹ᵁ V :=
      le_inf (le_inf (inf_le_left.trans inf_le_left)
        (inf_le_right.trans inf_le_left)) (inf_le_left.trans inf_le_right)
    have h₁ := congrArg ((XB).unitsRestrict hle) (T.triv_rel b b')
    have h₂ := congrArg ((XB).unitsRestrict hle) (T'.triv_rel b b')
    rw [map_mul] at h₁ h₂
    simp only [map_mul, map_inv, Scheme.unitsRestrict_unitsRestrict] at h₁ h₂ ⊢
    exact ratio_core h₁ h₂
  obtain ⟨e, he⟩ := Scheme.exists_unitsRestrict_eq
    (W := fun b : XB => 𝒩.opens b ⊓ (cg) ⁻¹ᵁ V) (fun _ => inf_le_right)
    (fun v hv => Opens.mem_iSup.mpr ⟨v, ⟨𝒩.mem_opens v, hv⟩⟩)
    (fun b => T'.triv b * (T.triv b)⁻¹) hcompat
  refine ⟨e, fun b => ?_⟩
  rw [he b, mul_comm (T.triv b), mul_assoc, inv_mul_cancel, mul_one]

variable (σ : overSpec k A ⟶ C)

/-- **The descent-cocycle unit of a twisted trivialization**: through the seams, the
comparison descent unit of `T` twisted by `e` is the descent coboundary of the
identified unit times the unit of `T`. -/
theorem comparisonDescentUnit_twist
    {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ) {V : (XA).Opens} (hV : IsAffineOpen V)
    (T T' : PieceTrivialization C 𝒩 γ V) (e : Γ(XB, (cg) ⁻¹ᵁ V)ˣ)
    (h : ∀ b : XB, T'.triv b
      = T.triv b * (XB).unitsRestrict (inf_le_right : 𝒩.opens b ⊓ (cg) ⁻¹ᵁ V ≤ _) e) :
    Module.comparisonDescentUnit A Γ(XA, V) B (pieceComparisonTensorUnit C σ W hV T')
      = Module.descentCoboundary Γ(XA, V) (Γ(XA, V) ⊗[A] B)
          (Units.map (Over.pieceEquiv (A := A) (B := B) C
            hV).toAlgHom.toRingHom.toMonoidHom e)
        * Module.comparisonDescentUnit A Γ(XA, V) B
            (pieceComparisonTensorUnit C σ W hV T) := by
  have htw := pieceComparisonUnit_eq_of_triv_eq C σ W T T' e h
  have htensor : pieceComparisonTensorUnit C σ W hV T'
      = pieceComparisonTensorUnit C σ W hV T
        * Units.map (Over.pieceEquiv (A := A) (B := B ⊗[A] B) C
            hV).toAlgHom.toRingHom.toMonoidHom (geomCoboundary C e) := by
    rw [pieceComparisonTensorUnit, pieceComparisonTensorUnit, htw, map_mul]
  have hmul : Module.comparisonDescentUnit A Γ(XA, V) B
      (pieceComparisonTensorUnit C σ W hV T
        * Units.map (Over.pieceEquiv (A := A) (B := B ⊗[A] B) C
            hV).toAlgHom.toRingHom.toMonoidHom (geomCoboundary C e))
      = Module.comparisonDescentUnit A Γ(XA, V) B
          (pieceComparisonTensorUnit C σ W hV T)
        * Module.comparisonDescentUnit A Γ(XA, V) B
            (Units.map (Over.pieceEquiv (A := A) (B := B ⊗[A] B) C
              hV).toAlgHom.toRingHom.toMonoidHom (geomCoboundary C e)) :=
    map_mul _ _ _
  rw [htensor, hmul, map_pieceEquiv_geomCoboundary C hV e,
    Module.comparisonDescentUnit_coboundary, mul_comm]

/-- **Trivialization independence of the descended per-piece class** ((C2) effectivity,
brick E4 (B)): the descended class of a piece does not depend on the chosen
trivialization — descents of one fixed global comparison datum are canonical. -/
theorem pieceDescentClass_congr [Module.FaithfullyFlat A B]
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ) {V : (XA).Opens} (hV : IsAffineOpen V)
    (T T' : PieceTrivialization C 𝒩 γ V) :
    pieceDescentClass C σ W hV T' = pieceDescentClass C σ W hV T := by
  obtain ⟨e, he⟩ := exists_ratio_unit C T T'
  set β := Units.map (Over.pieceEquiv (A := A) (B := B) C
    hV).toAlgHom.toRingHom.toMonoidHom e with hβ
  have hu := Module.isDescentCocycle_comparisonDescentUnit A Γ(XA, V) B
    (pieceComparisonTensorUnit_lmul C σ W hV T)
    (pieceComparisonTensorUnit_cocycle C σ W hV T)
  calc pieceDescentClass C σ W hV T'
      = ((Module.isDescentCocycle_descentCoboundary β).mul hu).picClass :=
        Module.IsDescentCocycle.picClass_congr _ _
          (comparisonDescentUnit_twist C σ W hV T T' e he)
    _ = hu.picClass := Module.IsDescentCocycle.picClass_descentCoboundary_mul β hu
    _ = pieceDescentClass C σ W hV T := rfl

/-! ## Flattening a trivialization along a trivial descended class -/

/-- **Flattening**: if the descended class of a trivialized piece is trivial, the piece
carries a trivialization whose glued comparison unit is `1` on the nose.  The
`picClass_eq_one_iff` cobounding unit, pulled back through the seams, twists the
trivialization flat. -/
theorem exists_pieceComparisonUnit_eq_one [Module.FaithfullyFlat A B]
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ) {V : (XA).Opens} (hV : IsAffineOpen V)
    (T : PieceTrivialization C 𝒩 γ V) (h1 : pieceDescentClass C σ W hV T = 1) :
    ∃ T' : PieceTrivialization C 𝒩 γ V, pieceComparisonUnit C σ W T' = 1 := by
  have hu := Module.isDescentCocycle_comparisonDescentUnit A Γ(XA, V) B
    (pieceComparisonTensorUnit_lmul C σ W hV T)
    (pieceComparisonTensorUnit_cocycle C σ W hV T)
  obtain ⟨β, hβ⟩ := hu.picClass_eq_one_iff.mp h1
  -- pull the cobounding unit back to a geometric unit of the cover piece
  set e : Γ(XB, (cg) ⁻¹ᵁ V)ˣ := Units.map (Over.pieceEquiv (A := A) (B := B) C
    hV).symm.toAlgHom.toRingHom.toMonoidHom β with he
  have heβ : Units.map (Over.pieceEquiv (A := A) (B := B) C
      hV).toAlgHom.toRingHom.toMonoidHom e = β := by
    refine Units.ext ?_
    exact (Over.pieceEquiv (A := A) (B := B) C hV).apply_symm_apply β.val
  -- the comparison unit of `T` is the geometric coboundary of `e`
  have hvT : pieceComparisonUnit C σ W T = geomCoboundary C e := by
    have h2 : pieceComparisonTensorUnit C σ W hV T
        = Units.map (Over.pieceEquiv (A := A) (B := B ⊗[A] B) C
            hV).toAlgHom.toRingHom.toMonoidHom (geomCoboundary C e) := by
      rw [map_pieceEquiv_geomCoboundary C hV e, heβ]
      -- both sides are the image of the descent coboundary under the identification
      have h3 := congrArg (Units.map (Algebra.TensorProduct.pieceDescentEquiv A
        Γ(XA, V) B).toAlgHom.toRingHom.toMonoidHom) hβ
      -- `pieceDescentEquiv ∘ comparisonDescentUnit = id`
      have h4 : ∀ v : (Γ(XA, V) ⊗[A] (B ⊗[A] B))ˣ,
          Units.map (Algebra.TensorProduct.pieceDescentEquiv A
            Γ(XA, V) B).toAlgHom.toRingHom.toMonoidHom
            (Module.comparisonDescentUnit A Γ(XA, V) B v) = v := fun v =>
        Units.ext (Module.pieceDescentEquiv_comparisonDescentUnit_val
          A Γ(XA, V) B v)
      rw [h4] at h3
      rw [h3]
      -- the coboundary seam, transported forward
      have h5 := congrArg (Units.map (Algebra.TensorProduct.pieceDescentEquiv A
        Γ(XA, V) B).toAlgHom.toRingHom.toMonoidHom)
        (Module.comparisonDescentUnit_coboundary A Γ(XA, V) B β)
      rw [h4] at h5
      rw [← h5]
    have h6 := congrArg (Units.map (Over.pieceEquiv (A := A) (B := B ⊗[A] B) C
      hV).symm.toAlgHom.toRingHom.toMonoidHom) h2
    have h7 : ∀ v : Γ(Xq, (cgq) ⁻¹ᵁ V)ˣ,
        Units.map (Over.pieceEquiv (A := A) (B := B ⊗[A] B) C
            hV).symm.toAlgHom.toRingHom.toMonoidHom
          (Units.map (Over.pieceEquiv (A := A) (B := B ⊗[A] B) C
            hV).toAlgHom.toRingHom.toMonoidHom v) = v := fun v =>
      Units.ext ((Over.pieceEquiv (A := A) (B := B ⊗[A] B) C hV).symm_apply_apply v.val)
    rw [pieceComparisonTensorUnit, h7, h7] at h6
    exact h6
  -- twist by `e⁻¹`
  refine ⟨T.twist C e⁻¹, ?_⟩
  rw [pieceComparisonUnit_eq_of_triv_eq C σ W T (T.twist C e⁻¹) e⁻¹ fun b => rfl,
    hvT, geomCoboundary_inv, mul_inv_cancel]

/-! ## Localize and flatten: flat pieces through every point of a trivialized piece -/

/-- **Localize-and-flatten** ((C2) effectivity, brick E4): every point of a trivialized
piece lies in a basic affine subpiece carrying a **flat** trivialization — one whose
glued comparison unit is `1`.  The avoidance brick at the germ prime of the point makes
the descended class trivial after restriction (`pieceDescentClass_res`), and flattening
produces the trivialization. -/
theorem exists_flat_pieceTrivialization_of_le [Module.FaithfullyFlat A B]
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ) {V₁ : (XA).Opens}
    (hV₁ : IsAffineOpen V₁) (T₁ : PieceTrivialization C 𝒩 γ V₁) {x : XA}
    (hx : x ∈ V₁) :
    ∃ (V : (XA).Opens) (_ : IsAffineOpen V), x ∈ V ∧
      ∃ T : PieceTrivialization C 𝒩 γ V, pieceComparisonUnit C σ W T = 1 := by
  classical
  -- the germ prime of `x` over `V₁`
  set p : Ideal Γ(XA, V₁) :=
    Ideal.comap ((XA).presheaf.germ V₁ x hx).hom
      (IsLocalRing.maximalIdeal ((XA).presheaf.stalk x)) with hp
  haveI : p.IsPrime := Ideal.IsPrime.comap _
  -- the avoidance brick at the single prime `p`
  obtain ⟨f, hfp, hfree⟩ := Module.Invertible.exists_notMem_isUnit_free
    (pieceDescentClass C σ W hV₁ T₁).AsModule (fun _ : PUnit.{u+1} => p)
  set V : (XA).Opens := (XA).basicOpen f with hV'
  have hV : IsAffineOpen V := hV₁.basicOpen f
  have hle : V ≤ V₁ := (XA).basicOpen_le f
  have hxV : x ∈ V := by
    rw [hV', Scheme.mem_basicOpen (XA) f x hx]
    by_contra hnu
    exact hfp PUnit.unit (by
      rw [hp, Ideal.mem_comap]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu))
  -- the restricted descended class is trivial
  have hres : pieceDescentClass C σ W hV (T₁.res C hle) = 1 := by
    rw [pieceDescentClass_res C σ W hV₁ hV hle T₁]
    letI := sectionsResAlgebra C hle
    haveI := hfree Γ(XA, V) ((XA).toRingedSpace.isUnit_res_basicOpen f)
    rw [CommRing.Pic.mapAlgebra_apply]
    exact CommRing.Pic.mk_eq_one _ _
  obtain ⟨T, hT⟩ := exists_pieceComparisonUnit_eq_one C σ W hV (T₁.res C hle) hres
  exact ⟨V, hV, hxV, T, hT⟩

end Over

end AlgebraicGeometry
