/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.ComparisonCoherence

/-!
# The diagonal seed of the σ-normalized comparison ((C2) effectivity, brick E1: `lmul'`)

For a proper, geometrically irreducible and geometrically reduced curve, the pullback of
a σ-normalized comparison cochain along the **diagonal** of the curve over
`Spec (B ⊗[A] B)` — the whiskered `Spec` of the multiplication
`Algebra.TensorProduct.lmul' : B ⊗[A] B →ₐ[A] B` — is trivial
(`Over.normalizedComparison_diagonal_eq_one`).  This is the cochain-level source of the
`lmul'_eq_one` normalization of `Module.IsDescentCocycle`: the per-piece descent units
that E2 extracts from the packaged datum inherit their diagonal normalization from this
statement at zero cost.

The argument is again the `lm:aut` miniature:

* both coprojections retract the diagonal (`Δ ≫ u₁ = 𝟙 = Δ ≫ u₂`, from
  `Algebra.TensorProduct.lmul'_comp_includeLeft/Right`), so the two insertion terms of
  the Δ-pulled witness relation (N1) coincide and cancel: the Δ-pullback of `θ` is
  Čech-compatible and glues to a global unit `d̄` of `X_B`
  (`Over.exists_glued_diagonalSeed` — no geometric hypotheses);
* the σ-restriction of `d̄` is `1`: the section square `s_B ≫ Δ = ∇ ≫ s_q` turns it
  into the `∇`-pullback of the σ-restriction of `θ`, and the (N2) normalization makes
  that the `∇`-pullback of the ρ-comparison, whose two legs coincide on the diagonal
  (`∇ ≫ q₁ = 𝟙 = ∇ ≫ q₂`);
* G2 (`Over.unitsAppTop_sectionOfPoint_bijective` at the affine test `B`) kills `d̄`.

The composite-bound transfers reuse the abstract lemmas of the (N3) layer with
`t := 𝟙` — the identity is just another insertion.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace AlgebraicGeometry

/-- **Single-open composite bound transfer along a factorization**, over abstract
schemes: the pair-overlap-free companion of `Scheme.Hom.le_preimage_inf_of_comp`. -/
theorem Scheme.Hom.le_preimage_of_comp {X Y Z : Scheme.{u}}
    (φ : X ⟶ Y) (r : Y ⟶ Z) (t : X ⟶ Z) (h : φ ≫ r = t)
    (V : Z → Z.Opens) (W : Y → Y.Opens)
    (hW : ∀ y : Y, W y ≤ r ⁻¹ᵁ V (r.base y))
    (x : X) {O : X.Opens} (hO : O ≤ φ ⁻¹ᵁ W (φ.base x)) :
    O ≤ t ⁻¹ᵁ V (t.base x) := by
  subst h
  exact hO.trans (φ.preimage_mono (hW (φ.base x)))

/-- **Pullback of a glued global unit, in composite normal form**: if a global unit `W`
of `Y` restricts on `V` to the `m`-pullback of a cochain value, its `appTop`-pullback
along `φ : X ⟶ Y` restricts to the `t = φ ≫ m`-pullback of that value.  The single-term
companion of `unitsAppLE_defect_pullback`; the composite merge happens here, over
abstract schemes. -/
lemma Scheme.Hom.unitsAppLE_glued_pullback {X Y S : Scheme.{u}}
    (φ : X ⟶ Y) (m : Y ⟶ S) (t : X ⟶ S) (h : φ ≫ m = t)
    {𝒮 : S.PointedCover} (θ : ∀ s : S, Γ(S, 𝒮.opens s)ˣ)
    (W : Γ(Y, ⊤)ˣ) {V : Y.Opens} {O : X.Opens} (e : O ≤ φ ⁻¹ᵁ V) (x : X)
    (em : V ≤ m ⁻¹ᵁ 𝒮.opens (m.base (φ.base x)))
    (hW : Y.unitsRestrict (le_top : V ≤ ⊤) W
        = m.unitsAppLE (𝒮.opens (m.base (φ.base x))) V em (θ (m.base (φ.base x))))
    (etO : O ≤ t ⁻¹ᵁ 𝒮.opens (t.base x)) :
    X.unitsRestrict (le_top : O ≤ ⊤) (Units.map φ.appTop.hom.toMonoidHom W)
      = t.unitsAppLE (𝒮.opens (t.base x)) O etO (θ (t.base x)) := by
  subst h
  refine (Scheme.Hom.unitsAppLE_unitsRestrict_top φ e W).symm.trans ?_
  refine (congrArg (φ.unitsAppLE V O e) hW).trans ?_
  exact Scheme.unitsAppLE_unitsAppLE φ m em e (θ (m.base (φ.base x)))

/-- Cancellation of a common middle term in a commutative group: `a ⋅ E = E ⋅ b` gives
`a = b`. -/
private lemma eq_of_mul_comm_cancel {G : Type u} [CommGroup G] {a b E : G}
    (h : a * E = E * b) : a = b :=
  mul_right_cancel (h.trans (mul_comm E b))

/-- Absorption in a commutative group: `a ⋅ u = u` gives `a = 1`. -/
private lemma eq_one_of_mul_eq_right {G : Type u} [CommGroup G] {a u : G}
    (h : a * u = u) : a = 1 :=
  mul_right_cancel (h.trans (one_mul u).symm)

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

/-! ## The multiplication retracts the coprojections -/

/-- The `k`-restricted multiplication `B ⊗[A] B →ₐ[k] B` retracts the first
coprojection: `lmul' ∘ tensorInl = id`. -/
lemma tensorLmul'_comp_tensorInl :
    ((Algebra.TensorProduct.lmul' A (S := B)).restrictScalars k).comp
        (tensorInl (A := A) (B := B))
      = AlgHom.id k B := by
  refine AlgHom.ext fun b ↦ ?_
  change Algebra.TensorProduct.lmul' A (b ⊗ₜ[A] 1) = b
  rw [Algebra.TensorProduct.lmul'_apply_tmul, mul_one]

/-- The `k`-restricted multiplication `B ⊗[A] B →ₐ[k] B` retracts the second
coprojection: `lmul' ∘ tensorInr = id`. -/
lemma tensorLmul'_comp_tensorInr :
    ((Algebra.TensorProduct.lmul' A (S := B)).restrictScalars k).comp
        (tensorInr (A := A) (B := B))
      = AlgHom.id k B := by
  refine AlgHom.ext fun b ↦ ?_
  change Algebra.TensorProduct.lmul' A ((1 : B) ⊗ₜ[A] b) = b
  rw [Algebra.TensorProduct.lmul'_apply_tmul, one_mul]

variable (C : Over (Spec (.of k))) (σ : overSpec k A ⟶ C)

-- Spec-side objects and maps
set_option quotPrecheck false in
local notation "SB" => (overSpec k B).left
set_option quotPrecheck false in
local notation "Sq" => (overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "q₁" => (Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "q₂" => (Over.overSpecMap (tensorInr (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "Δs" => (Over.overSpecMap
  ((Algebra.TensorProduct.lmul' A (S := B)).restrictScalars k)).left
-- product-side objects and maps
set_option quotPrecheck false in
local notation "XB" => (C ⊗ overSpec k B).left
set_option quotPrecheck false in
local notation "Xq" => (C ⊗ overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "u₁" => (C ◁ Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "u₂" => (C ◁ Over.overSpecMap (tensorInr (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "Δx" => (C ◁ Over.overSpecMap
  ((Algebra.TensorProduct.lmul' A (S := B)).restrictScalars k)).left
-- the sections of the projections attached to the base changes of `σ`
set_option quotPrecheck false in
local notation "sB" => (Over.sectionOfPoint
  (Over.overSpecMap ((Algebra.ofId A B).restrictScalars k) ≫ σ)).left
set_option quotPrecheck false in
local notation "sq" => (Over.sectionOfPoint
  (Over.overSpecMap ((Algebra.ofId A (B ⊗[A] B)).restrictScalars k) ≫ σ)).left

namespace Over

/-! ## The diagonal retractions and the section square -/

/-- The `Spec`-side diagonal retracts the first coprojection: `∇ ≫ q₁ = 𝟙`. -/
lemma overSpecMap_left_lmul'_inl : Δs ≫ (q₁) = 𝟙 (SB) := by
  rw [← Over.comp_left, ← Over.overSpecMap_comp, tensorLmul'_comp_tensorInl,
    Over.overSpecMap_id]
  rfl

/-- The `Spec`-side diagonal retracts the second coprojection: `∇ ≫ q₂ = 𝟙`. -/
lemma overSpecMap_left_lmul'_inr : Δs ≫ (q₂) = 𝟙 (SB) := by
  rw [← Over.comp_left, ← Over.overSpecMap_comp, tensorLmul'_comp_tensorInr,
    Over.overSpecMap_id]
  rfl

/-- The curve-product diagonal retracts the first coprojection: `Δ ≫ u₁ = 𝟙`. -/
lemma whiskerLeft_lmul'_inl : Δx ≫ (u₁) = 𝟙 (XB) := by
  rw [← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← Over.overSpecMap_comp,
    tensorLmul'_comp_tensorInl, Over.overSpecMap_id, MonoidalCategory.whiskerLeft_id]
  rfl

/-- The curve-product diagonal retracts the second coprojection: `Δ ≫ u₂ = 𝟙`. -/
lemma whiskerLeft_lmul'_inr : Δx ≫ (u₂) = 𝟙 (XB) := by
  rw [← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← Over.overSpecMap_comp,
    tensorLmul'_comp_tensorInr, Over.overSpecMap_id, MonoidalCategory.whiskerLeft_id]
  rfl

/-- The section square over the diagonal: `s_B ≫ Δ = ∇ ≫ s_q`. -/
lemma sectionSq_comp_lmul' : sB ≫ Δx = Δs ≫ sq :=
  sectionOfPoint_left_comp_whiskerLeft C (Algebra.TensorProduct.lmul' A (S := B)) σ

/-! ## The glued diagonal seed -/

/-- **The diagonal pullback of a witness glues to a global unit of `X_B`.**  Both
coprojections retract the diagonal, so the two insertion terms of the Δ-pulled witness
relation (N1) coincide and cancel: the Δ-pullback of `θ₀` is Čech-compatible on the
pullback cover and glues by the `𝒪ˣ`-sheaf axiom.  No geometric hypotheses. -/
theorem exists_glued_diagonalSeed (𝒩 : (XB).PointedCover) (γ : (XB).unitsCocycle 𝒩)
    (𝒲 : (Xq).PointedCover)
    (hW₁ : ∀ x, 𝒲.opens x ≤ (u₁) ⁻¹ᵁ 𝒩.opens ((u₁).base x))
    (hW₂ : ∀ x, 𝒲.opens x ≤ (u₂) ⁻¹ᵁ 𝒩.opens ((u₂).base x))
    (θ₀ : ∀ x : Xq, Γ(Xq, 𝒲.opens x)ˣ)
    (hdown : ∀ x y : Xq,
      (Xq).unitsRestrict (inf_le_left : 𝒲.opens x ⊓ 𝒲.opens y ≤ 𝒲.opens x) (θ₀ x)
          * (u₁).unitsAppLE (𝒩.opens ((u₁).base x) ⊓ 𝒩.opens ((u₁).base y))
              (𝒲.opens x ⊓ 𝒲.opens y)
              ((u₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
                (inf_le_right.trans (hW₁ y)))
              (Scheme.unitsEvInf γ ((u₁).base x) ((u₁).base y))
        = (u₂).unitsAppLE (𝒩.opens ((u₂).base x) ⊓ 𝒩.opens ((u₂).base y))
              (𝒲.opens x ⊓ 𝒲.opens y)
              ((u₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
                (inf_le_right.trans (hW₂ y)))
              (Scheme.unitsEvInf γ ((u₂).base x) ((u₂).base y))
          * (Xq).unitsRestrict inf_le_right (θ₀ y)) :
    ∃ dbar : Γ(XB, ⊤)ˣ, ∀ b : XB,
      (XB).unitsRestrict le_top dbar
        = (Δx).unitsAppLE (𝒲.opens ((Δx).base b)) ((𝒲.pullback (Δx)).opens b)
            le_rfl (θ₀ ((Δx).base b)) := by
  apply Scheme.exists_global_unit_of_compatible (𝒰 := 𝒲.pullback (Δx))
    (fun b ↦ (Δx).unitsAppLE (𝒲.opens ((Δx).base b)) ((𝒲.pullback (Δx)).opens b)
      le_rfl (θ₀ ((Δx).base b)))
  intro b b'
  simp only [Scheme.Hom.unitsAppLE_map]
  have H := Scheme.Hom.unitsAppLE_coboundary_rel_comp (Δx) (u₁) (u₂)
    (𝟙 (XB)) (𝟙 (XB)) θ₀
    (fun v v' ↦ 𝒩.opens v ⊓ 𝒩.opens v') (fun v v' ↦ 𝒩.opens v ⊓ 𝒩.opens v')
    (fun v v' ↦ Scheme.unitsEvInf γ v v') (fun v v' ↦ Scheme.unitsEvInf γ v v')
    (fun x y ↦ (u₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
      (inf_le_right.trans (hW₁ y)))
    (fun x y ↦ (u₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
      (inf_le_right.trans (hW₂ y)))
    hdown (whiskerLeft_lmul'_inl C) (whiskerLeft_lmul'_inr C) b b'
    ((Δx).le_preimage_inf inf_le_left inf_le_right)
    (Scheme.Hom.le_preimage_inf_of_comp (Δx) (u₁) (𝟙 (XB)) (whiskerLeft_lmul'_inl C)
      𝒩.opens 𝒲.opens hW₁ b b' ((Δx).le_preimage_inf inf_le_left inf_le_right))
    (Scheme.Hom.le_preimage_inf_of_comp (Δx) (u₂) (𝟙 (XB)) (whiskerLeft_lmul'_inr C)
      𝒩.opens 𝒲.opens hW₂ b b' ((Δx).le_preimage_inf inf_le_left inf_le_right))
  exact eq_of_mul_comm_cancel H

/-! ## The diagonal seed is trivial -/

/-- **The `lmul'`-triviality of the diagonal seed.**  For a proper, geometrically
irreducible and geometrically reduced curve, the pullback of a σ-normalized comparison
cochain along the diagonal of the curve over `Spec (B ⊗[A] B)` is `1` on the pullback
cover: the glued diagonal seed has trivial σ-restriction by (N2) and the diagonal
retractions, and G2 (Kleiman's `lm:aut` rigidity at the affine test `B`) kills it.
This is the cochain-level source of the `lmul'_eq_one` normalization of the per-piece
descent data (brick E2). -/
theorem normalizedComparison_diagonal_eq_one
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    (𝒩 : (XB).PointedCover) (γ : (XB).unitsCocycle 𝒩) (𝒲 : (Xq).PointedCover)
    (hW₁ : ∀ x, 𝒲.opens x ≤ (u₁) ⁻¹ᵁ 𝒩.opens ((u₁).base x))
    (hW₂ : ∀ x, 𝒲.opens x ≤ (u₂) ⁻¹ᵁ 𝒩.opens ((u₂).base x))
    (ρ : ∀ b : SB, Γ(SB, (𝒩.pullback (sB)).opens b)ˣ)
    (θ₀ : ∀ x : Xq, Γ(Xq, 𝒲.opens x)ˣ)
    (hdown : ∀ x y : Xq,
      (Xq).unitsRestrict (inf_le_left : 𝒲.opens x ⊓ 𝒲.opens y ≤ 𝒲.opens x) (θ₀ x)
          * (u₁).unitsAppLE (𝒩.opens ((u₁).base x) ⊓ 𝒩.opens ((u₁).base y))
              (𝒲.opens x ⊓ 𝒲.opens y)
              ((u₁).le_preimage_inf (inf_le_left.trans (hW₁ x))
                (inf_le_right.trans (hW₁ y)))
              (Scheme.unitsEvInf γ ((u₁).base x) ((u₁).base y))
        = (u₂).unitsAppLE (𝒩.opens ((u₂).base x) ⊓ 𝒩.opens ((u₂).base y))
              (𝒲.opens x ⊓ 𝒲.opens y)
              ((u₂).le_preimage_inf (inf_le_left.trans (hW₂ x))
                (inf_le_right.trans (hW₂ y)))
              (Scheme.unitsEvInf γ ((u₂).base x) ((u₂).base y))
          * (Xq).unitsRestrict inf_le_right (θ₀ y))
    (hnorm : ∀ y : Sq,
      (sq).unitsAppLE (𝒲.opens ((sq).base y))
          ((normalizationCover C σ 𝒩 𝒲).opens y)
          (normalizationCover_le_section C σ 𝒩 𝒲 y) (θ₀ ((sq).base y))
        * (q₂).unitsAppLE ((𝒩.pullback (sB)).opens ((q₂).base y))
            ((normalizationCover C σ 𝒩 𝒲).opens y)
            (normalizationCover_le_inr C σ 𝒩 𝒲 y) (ρ ((q₂).base y))
      = (q₁).unitsAppLE ((𝒩.pullback (sB)).opens ((q₁).base y))
          ((normalizationCover C σ 𝒩 𝒲).opens y)
          (normalizationCover_le_inl C σ 𝒩 𝒲 y) (ρ ((q₁).base y)))
    (b : XB) :
    (Δx).unitsAppLE (𝒲.opens ((Δx).base b)) ((𝒲.pullback (Δx)).opens b) le_rfl
      (θ₀ ((Δx).base b)) = 1 := by
  obtain ⟨dbar, hdbar⟩ := exists_glued_diagonalSeed C 𝒩 γ 𝒲 hW₁ hW₂ θ₀ hdown
  -- ### the σ-restriction of the glued seed is `1`
  have hsec : Units.map (sB).appTop.hom.toMonoidHom dbar = 1 := by
    refine Scheme.global_unit_ext
      (𝒰 := ((𝒲.pullback (Δx)).pullback (sB))
        ⊓ (normalizationCover C σ 𝒩 𝒲).pullback (Δs)) _ _ fun s ↦ ?_
    rw [map_one]
    -- the pullback of the glued seed, in `∇ ≫ s_q` composite normal form
    have hLHS := Scheme.Hom.unitsAppLE_glued_pullback (sB) (Δx) (Δs ≫ (sq))
      (sectionSq_comp_lmul' C σ) θ₀ dbar
      (inf_le_left :
        (((𝒲.pullback (Δx)).pullback (sB))
            ⊓ (normalizationCover C σ 𝒩 𝒲).pullback (Δs)).opens s
          ≤ (sB) ⁻¹ᵁ (𝒲.pullback (Δx)).opens ((sB).base s)) s
      le_rfl (hdbar ((sB).base s))
      (Scheme.Hom.le_preimage_of_comp (Δs) (sq) (Δs ≫ (sq)) rfl
        𝒲.opens (normalizationCover C σ 𝒩 𝒲).opens
        (normalizationCover_le_section C σ 𝒩 𝒲) s inf_le_right)
    -- the (N2) normalization pulled along `∇`: both ρ-legs collapse onto the identity
    have hkill := unitsAppLE_normalization_pullback (Δs) (sq) (q₁) (q₂)
      (Δs ≫ (sq)) (𝟙 (SB)) (𝟙 (SB)) θ₀ ρ
      (normalizationCover_le_section C σ 𝒩 𝒲) (normalizationCover_le_inl C σ 𝒩 𝒲)
      (normalizationCover_le_inr C σ 𝒩 𝒲) hnorm rfl
      (overSpecMap_left_lmul'_inl (k := k) (A := A) (B := B))
      (overSpecMap_left_lmul'_inr (k := k) (A := A) (B := B)) s
      (inf_le_right :
        (((𝒲.pullback (Δx)).pullback (sB))
            ⊓ (normalizationCover C σ 𝒩 𝒲).pullback (Δs)).opens s
          ≤ (Δs) ⁻¹ᵁ (normalizationCover C σ 𝒩 𝒲).opens ((Δs).base s))
      (Scheme.Hom.le_preimage_of_comp (Δs) (sq) (Δs ≫ (sq)) rfl
        𝒲.opens (normalizationCover C σ 𝒩 𝒲).opens
        (normalizationCover_le_section C σ 𝒩 𝒲) s inf_le_right)
      (Scheme.Hom.le_preimage_of_comp (Δs) (q₁) (𝟙 (SB))
        (overSpecMap_left_lmul'_inl (k := k) (A := A) (B := B))
        (𝒩.pullback (sB)).opens (normalizationCover C σ 𝒩 𝒲).opens
        (normalizationCover_le_inl C σ 𝒩 𝒲) s inf_le_right)
      (Scheme.Hom.le_preimage_of_comp (Δs) (q₁) (𝟙 (SB))
        (overSpecMap_left_lmul'_inl (k := k) (A := A) (B := B))
        (𝒩.pullback (sB)).opens (normalizationCover C σ 𝒩 𝒲).opens
        (normalizationCover_le_inl C σ 𝒩 𝒲) s inf_le_right)
    exact hLHS.trans (eq_one_of_mul_eq_right hkill)
  -- ### G2 at the affine test `B` kills the glued seed
  have hone : dbar = 1 := by
    apply (Over.unitsAppTop_sectionOfPoint_bijective
      (Over.overSpecMap ((Algebra.ofId A B).restrictScalars k) ≫ σ)).injective
    rw [map_one, unitsAppLE_top_global, hsec, map_one]
  -- ### conclude pointwise
  exact ((map_one ((XB).unitsRestrict
      (le_top : (𝒲.pullback (Δx)).opens b ≤ ⊤))).symm.trans
    ((congrArg ((XB).unitsRestrict le_top) hone).symm.trans (hdbar b))).symm

end Over

end AlgebraicGeometry
