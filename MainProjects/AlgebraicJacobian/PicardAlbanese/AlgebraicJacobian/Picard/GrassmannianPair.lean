/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GrassmannianScheme

/-!
# The Grassmannian pair over the base field (DD-3, stage 3e)

The fibre product of two Grassmannians over `Spec k` — the ambient scheme of DD-R's
`(♦)` carve (`informal/spec-dd-3.md` §2; worksheet §3.1: the campaign instantiates the
two windows `Gr(g, H_M)` and `Gr(g, H_{M+s})`), with its projections, structure
morphism, and the affine product atlas (`openCoverOfLeftRight` on the two chart
atlases, each patch identified with `Spec` of a tensor product of chart rings).

* `AlgebraicGeometry.Grassmannian.grPair`: the fibre product, with `grPairFst`,
  `grPairSnd`, `grPairStructMap`, `grPairOver`.
* `AlgebraicGeometry.Grassmannian.grPairCover`: the finite affine product atlas.
* `AlgebraicGeometry.Grassmannian.grPairPatchIso`: each patch is
  `Spec (R^I ⊗[k] R^J)`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Grassmannian

variable (k : Type u) [Field k] (d₁ r₁ d₂ r₂ : ℕ)

/-- **The Grassmannian pair**: the fibre product
`Gr(d₁, r₁) ×_{Spec k} Gr(d₂, r₂)` — the ambient scheme of the DD-R carve. -/
noncomputable def grPair : Scheme :=
  Limits.pullback (grStructMap k d₁ r₁) (grStructMap k d₂ r₂)

/-- First projection of the Grassmannian pair. -/
noncomputable def grPairFst : grPair k d₁ r₁ d₂ r₂ ⟶ grScheme k d₁ r₁ :=
  Limits.pullback.fst (grStructMap k d₁ r₁) (grStructMap k d₂ r₂)

/-- Second projection of the Grassmannian pair. -/
noncomputable def grPairSnd : grPair k d₁ r₁ d₂ r₂ ⟶ grScheme k d₂ r₂ :=
  Limits.pullback.snd (grStructMap k d₁ r₁) (grStructMap k d₂ r₂)

/-- The structure morphism of the Grassmannian pair. -/
noncomputable def grPairStructMap : grPair k d₁ r₁ d₂ r₂ ⟶ Spec (CommRingCat.of k) :=
  grPairFst k d₁ r₁ d₂ r₂ ≫ grStructMap k d₁ r₁

/-- The two projections agree over the base (the pullback square). -/
theorem grPairSnd_grStructMap :
    grPairSnd k d₁ r₁ d₂ r₂ ≫ grStructMap k d₂ r₂ = grPairStructMap k d₁ r₁ d₂ r₂ :=
  (Limits.pullback.condition (f := grStructMap k d₁ r₁) (g := grStructMap k d₂ r₂)).symm

/-- The Grassmannian pair as a test object of `Over (Spec k)`. -/
noncomputable def grPairOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (grPairStructMap k d₁ r₁ d₂ r₂)

/-- **The affine product atlas** of the Grassmannian pair: the finite open cover by
products of charts (`openCoverOfLeftRight` on the two chart atlases). -/
noncomputable def grPairCover : (grPair k d₁ r₁ d₂ r₂).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight
    (glueData k d₁ r₁).openCover (glueData k d₂ r₂).openCover
    (grStructMap k d₁ r₁) (grStructMap k d₂ r₂)

/-- The chart index of the affine product atlas is finite. -/
instance finite_grPairCover_index : Finite (grPairCover k d₁ r₁ d₂ r₂).I₀ :=
  inferInstanceAs (Finite ((glueData k d₁ r₁).J × (glueData k d₂ r₂).J))

/-- Each patch of the affine product atlas is the spectrum of a tensor product of
chart rings: `U^I ×_{Spec k} U^J = Spec (R^I ⊗[k] R^J)`. -/
noncomputable def grPairPatchIso (i : (glueData k d₁ r₁).J) (j : (glueData k d₂ r₂).J) :
    Limits.pullback ((glueData k d₁ r₁).openCover.f i ≫ grStructMap k d₁ r₁)
        ((glueData k d₂ r₂).openCover.f j ≫ grStructMap k d₂ r₂) ≅
      Spec (CommRingCat.of (TensorProduct k
        (ChartRing k d₁ r₁ i.down.1) (ChartRing k d₂ r₂ j.down.1))) :=
  Limits.pullback.congrHom (ι_grStructMap k d₁ r₁ i) (ι_grStructMap k d₂ r₂ j) ≪≫
    pullbackSpecIso k (ChartRing k d₁ r₁ i.down.1) (ChartRing k d₂ r₂ j.down.1)

end AlgebraicGeometry.Grassmannian
