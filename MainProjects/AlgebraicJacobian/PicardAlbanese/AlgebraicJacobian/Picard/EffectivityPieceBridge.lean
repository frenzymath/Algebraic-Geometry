/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.EffectivityPieces

/-!
# The piece-identification bridge ((C2) effectivity, brick E3: naturality in the algebra)

The E0 section-ring identification `Γ(X_R, cg_R⁻¹ V) ≅ Γ(V) ⊗[A] R` (`Over.pieceRingEquiv`,
`R`-uniform in the base algebra `R`) is **natural in `R`**: for an `A`-algebra map
`j : R →ₐ[A] R'`, the whiskered map `W_j = (C ◁ Spec j).left : X_{R'} ⟶ X_R` lies over the
cover structure maps (`Over.whiskerLeft_overSpecMap_comp_cover`), and pulling sections back
along `W_j` is `id_{Γ(V)} ⊗ j` through the identification
(`Over.pieceRingEquiv_whiskerLeft_naturality`, the **master bridge**).

This is the seam through which the geometric statements about the per-piece comparison
unit — diagonal triviality along `Δ = (C ◁ Spec lmul').left`, Amitsur coherence along the
cofaces `w = (C ◁ Spec descentFace).left` — are transported to the exact `hlmul`/`hcoc`
hypotheses of the landed per-piece descent extraction
(`Module.isDescentCocycle_comparisonDescentUnit`,
`AlgebraicJacobian.Picard.EffectivityDescentDatum`): those are stated with
`Algebra.TensorProduct.map (AlgHom.id Γ(V) Γ(V)) j` for `j = lmul'` and the three
`descentFace`s, which is exactly the bridge's right leg.

The mirror of E0's restriction seam `pieceRingEquiv_naturality` (naturality in the open
`V`); here the open is fixed and the algebra moves.

## Kernel discipline

The composite pullback conversions happen once, over abstract schemes
(`Scheme.Hom.appLE_apply_congr_hom`, `appLE_comp_of_eq`, `appLE_appLE_of_square` — the
ring-level companions of the landed `unitsAppLE_congr_hom` calculus); the concrete
instantiations are single applications.  The master bridge is proved by tensor
induction, mirroring the landed `pieceRingEquiv_naturality`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry

/-! ## Composite conversions for `appLE`, over abstract schemes -/

/-- **Morphism-congruence for `appLE`**: equal morphisms with the same source and target
opens act identically on sections — the ring-level companion of
`Scheme.Hom.unitsAppLE_congr_hom`. -/
theorem Scheme.Hom.appLE_apply_congr_hom {X Z : Scheme.{u}} {f f' : X ⟶ Z} (hf : f = f')
    {V : Z.Opens} {O : X.Opens} (e : O ≤ f ⁻¹ᵁ V) (e' : O ≤ f' ⁻¹ᵁ V) (s : Γ(Z, V)) :
    f.appLE V O e s = f'.appLE V O e' s := by
  subst hf; rfl

/-- **Composite collapse for `appLE` along a factorization**: for `φ ≫ r = t`, pulling a
section back along `r` and then `φ` is pulling it back along `t`.  The
nested-versus-composite conversion happens here, over abstract schemes. -/
theorem Scheme.Hom.appLE_comp_of_eq {X Y Z : Scheme.{u}} (φ : X ⟶ Y) (r : Y ⟶ Z)
    (t : X ⟶ Z) (h : φ ≫ r = t) {V : Z.Opens} {P : Y.Opens} {O : X.Opens}
    (e₁ : P ≤ r ⁻¹ᵁ V) (e₂ : O ≤ φ ⁻¹ᵁ P) (e₃ : O ≤ t ⁻¹ᵁ V) (s : Γ(Z, V)) :
    φ.appLE P O e₂ (r.appLE V P e₁ s) = t.appLE V O e₃ s := by
  subst h
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/-- **Square conversion for `appLE`**: for a commutative square `φ ≫ r = φ' ≫ r'`, the
two nested pullbacks of a section along the two legs agree. -/
theorem Scheme.Hom.appLE_appLE_of_square {X Y Y' Z : Scheme.{u}} (φ : X ⟶ Y) (r : Y ⟶ Z)
    (φ' : X ⟶ Y') (r' : Y' ⟶ Z) (h : φ ≫ r = φ' ≫ r')
    {V : Z.Opens} {P : Y.Opens} {P' : Y'.Opens} {O : X.Opens}
    (e₁ : P ≤ r ⁻¹ᵁ V) (e₂ : O ≤ φ ⁻¹ᵁ P) (e₁' : P' ≤ r' ⁻¹ᵁ V) (e₂' : O ≤ φ' ⁻¹ᵁ P')
    (s : Γ(Z, V)) :
    φ.appLE P O e₂ (r.appLE V P e₁ s) = φ'.appLE P' O e₂' (r'.appLE V P' e₁' s) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact Scheme.Hom.appLE_apply_congr_hom h _ _ s

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]
variable (C : Over (Spec (.of k)))

set_option quotPrecheck false in
local notation "XA" => (C ⊗ overSpec k A).left

namespace Over

-- The base-piece `A`-algebra structure and the cover-piece `Γ(V)`-algebra structure of E0.
attribute [local instance] Over.sectionsAlgebraA Over.pieceCoverAlgebra

variable {R R' : Type u} [CommRing R] [Algebra k R] [Algebra A R] [IsScalarTower k A R]
  [CommRing R'] [Algebra k R'] [Algebra A R'] [IsScalarTower k A R']

/-! ## The cover-compatibility of the whiskered maps -/

/-- An `A`-algebra map composed with the structure map of `R` is the structure map of
`R'`: `j ∘ (ofId A R) = ofId A R'` as `k`-algebra maps. -/
lemma restrictScalars_comp_ofId (j : R →ₐ[A] R') :
    (j.restrictScalars k).comp ((Algebra.ofId A R).restrictScalars k)
      = (Algebra.ofId A R').restrictScalars k := by
  refine AlgHom.ext fun a => ?_
  change j (Algebra.ofId A R a) = Algebra.ofId A R' a
  rw [Algebra.ofId_apply, Algebra.ofId_apply]
  exact j.commutes a

/-- **The whiskered map of an `A`-algebra map lies over the cover inclusions**:
`W_j ≫ cg_R = cg_{R'}` on the curve products. -/
lemma whiskerLeft_overSpecMap_comp_cover (j : R →ₐ[A] R') :
    (C ◁ Over.overSpecMap (j.restrictScalars k)).left
        ≫ (C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left
      = (C ◁ Over.overSpecMap ((Algebra.ofId A R').restrictScalars k)).left := by
  rw [← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← Over.overSpecMap_comp,
    restrictScalars_comp_ofId (A := A) j]

/-- The `R'`-piece is the `W_j`-preimage of the `R`-piece. -/
lemma coverPreimage_le_whiskerLeft (j : R →ₐ[A] R') (U : (XA).Opens) :
    (C ◁ Over.overSpecMap ((Algebra.ofId A R').restrictScalars k)).left ⁻¹ᵁ U
      ≤ (C ◁ Over.overSpecMap (j.restrictScalars k)).left ⁻¹ᵁ
          ((C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left ⁻¹ᵁ U) :=
  le_of_eq (by rw [← Scheme.Hom.comp_preimage, whiskerLeft_overSpecMap_comp_cover C j])

/-! ## The master bridge -/

/-- Cancellation for the E0 identification: `pieceRingEquiv` applied to `pieceEquiv`. -/
lemma pieceRingEquiv_pieceEquiv {U : (XA).Opens} (hU : IsAffineOpen U)
    (ξ : Γ((C ⊗ overSpec k R).left,
      (C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left ⁻¹ᵁ U)) :
    Over.pieceRingEquiv (B := R) C hU (Over.pieceEquiv (B := R) C hU ξ) = ξ := by
  change Over.pieceTensorAlgEquiv (B := R) C hU
    ((Over.pieceTensorAlgEquiv (B := R) C hU).symm ξ) = ξ
  exact AlgEquiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
/-- **The master bridge** ((C2) effectivity, brick E3): the E0 section-ring
identification is natural in the base algebra.  For an `A`-algebra map `j : R →ₐ[A] R'`,
pulling identified sections back along the whiskered map `W_j : X_{R'} ⟶ X_R` is
`id_{Γ(V)} ⊗ j` through the identifications of the two pieces.  Instantiated at
`j = lmul'` and the three `descentFace`s, this transports the diagonal triviality and
the coherence of the per-piece comparison unit to the `hlmul`/`hcoc` hypotheses of the
landed per-piece descent extraction. -/
theorem pieceRingEquiv_whiskerLeft_naturality (j : R →ₐ[A] R') {U : (XA).Opens}
    (hU : IsAffineOpen U) (x : Γ(XA, U) ⊗[A] R) :
    (C ◁ Over.overSpecMap (j.restrictScalars k)).left.appLE
        ((C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left ⁻¹ᵁ U)
        ((C ◁ Over.overSpecMap ((Algebra.ofId A R').restrictScalars k)).left ⁻¹ᵁ U)
        (coverPreimage_le_whiskerLeft C j U)
        (Over.pieceRingEquiv (B := R) C hU x)
      = Over.pieceRingEquiv (B := R') C hU
          (Algebra.TensorProduct.map (AlgHom.id Γ(XA, U) Γ(XA, U)) j x) := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s r =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
      Over.pieceRingEquiv_tmul, Over.pieceRingEquiv_tmul, map_mul]
    congr 1
    · -- the `cg`-pullback factor
      exact Scheme.Hom.appLE_comp_of_eq
        (C ◁ Over.overSpecMap (j.restrictScalars k)).left
        (C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left
        (C ◁ Over.overSpecMap ((Algebra.ofId A R').restrictScalars k)).left
        (whiskerLeft_overSpecMap_comp_cover C j) le_rfl
        (coverPreimage_le_whiskerLeft C j U) le_rfl s
    · -- the projection factor
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
      refine (Scheme.Hom.appLE_appLE_of_square
        (C ◁ Over.overSpecMap (j.restrictScalars k)).left
        (snd C (overSpec k R)).left
        (snd C (overSpec k R')).left
        (Over.overSpecMap (j.restrictScalars k)).left
        (Over.snd_left_naturality C (Over.overSpecMap (j.restrictScalars k)))
        (le_top.trans (Scheme.Hom.preimage_top _).ge)
        (coverPreimage_le_whiskerLeft C j U)
        (le_top.trans (Scheme.Hom.preimage_top _).ge)
        (le_top.trans (Scheme.Hom.preimage_top _).ge)
        ((Scheme.ΓSpecIso (.of R)).inv r)).trans ?_
      refine congrArg
        ((snd C (overSpec k R')).left.appLE ⊤
          ((C ◁ Over.overSpecMap ((Algebra.ofId A R').restrictScalars k)).left ⁻¹ᵁ U)
          (le_top.trans (Scheme.Hom.preimage_top _).ge)) ?_
      -- the `Spec`-side factor: `ΓSpecIso`-naturality
      have happ : (Over.overSpecMap (j.restrictScalars k)).left.appLE ⊤ ⊤
          (le_top.trans (Scheme.Hom.preimage_top _).ge)
          = (Over.overSpecMap (j.restrictScalars k)).left.appTop :=
        Scheme.Hom.appLE_eq_app _
      rw [happ]
      have hnat := congr($(Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom j.toRingHom)).hom r)
      exact hnat.symm

/-- **The master bridge, `pieceEquiv` form**: through the `Γ(V)`-algebra identifications
of the two pieces, `id ⊗ j` is the pullback along the whiskered map `W_j`.  This is the
leg the `hlmul`/`hcoc` transports consume. -/
theorem map_pieceEquiv_eq_pieceEquiv_whiskerLeft (j : R →ₐ[A] R') {U : (XA).Opens}
    (hU : IsAffineOpen U)
    (ξ : Γ((C ⊗ overSpec k R).left,
      (C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left ⁻¹ᵁ U)) :
    Algebra.TensorProduct.map (AlgHom.id Γ(XA, U) Γ(XA, U)) j
        (Over.pieceEquiv (B := R) C hU ξ)
      = Over.pieceEquiv (B := R') C hU
          ((C ◁ Over.overSpecMap (j.restrictScalars k)).left.appLE
            ((C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left ⁻¹ᵁ U)
            ((C ◁ Over.overSpecMap ((Algebra.ofId A R').restrictScalars k)).left ⁻¹ᵁ U)
            (coverPreimage_le_whiskerLeft C j U) ξ) := by
  apply (Over.pieceRingEquiv (B := R') C hU).injective
  rw [pieceRingEquiv_pieceEquiv, ← pieceRingEquiv_whiskerLeft_naturality C j hU,
    pieceRingEquiv_pieceEquiv]

end Over

end AlgebraicGeometry
