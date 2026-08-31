/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import AlgebraicJacobian.Picard.Rigidification
import AlgebraicJacobian.Curve.ProductCharts

/-!
# The diagonal of the curve square is closed (deg-D4b, brick B3)

For `C : Over (Spec k)` with `[IsSeparated C.hom]`, the diagonal

`δ C := Over.diagonal C = Over.sectionOfPoint (𝟙 C) = lift (𝟙 C) (𝟙 C) : C ⟶ C ⊗ C`

— the graph of the identity (`Picard/Rigidification.lean`) — is a **closed immersion**:
it retracts the second projection (`δ ≫ snd = 𝟙`), the identity is a closed immersion, the
second projection is separated as the base change of `C.hom` along itself
(`Over.isPullback_left`), and `IsClosedImmersion.of_comp` cancels.  This is the
closed-immersion chain of `informal/deg-d4b-worksheet.md` §D4, together with the point-set
API of the diagonal `Δ := Set.range (δ C).left.base` that the per-chart kernel computation
(B4) and the assembly (B5) consume.

## Main declarations

* `AlgebraicGeometry.Over.diagonal` — the diagonal `δ C`, reusing the landed
  `Over.sectionOfPoint` at the identity point (`diagonal_def`), with the projection
  identities `diagonal_fst`/`diagonal_snd`, their scheme-level forms
  `diagonal_left_fst_left`/`diagonal_left_snd_left`, and the pointwise retractions
  `fst_base_diagonal_base`/`snd_base_diagonal_base`.
* `AlgebraicGeometry.Over.isClosedImmersion_diagonal_left` — `(δ C).left` is a closed
  immersion (hence affine, hence quasi-compact: `Scheme.Hom.ker` applies to it), with
  `isClosed_range_diagonal` (Δ is closed).
* `AlgebraicGeometry.Over.isSeparated_left_tensor` — the curve square `(C ⊗ C).left` is a
  separated *scheme*, so intersections of affine opens are affine (`IsAffineOpen.inf`) —
  the overlap calculus of the cross-chart ratio argument (worksheet D3).
* `AlgebraicGeometry.Over.diagonalComplement` — the complement `Δᶜ` as an open of the
  curve square (the off-diagonal member of the diagonal cover, worksheet D4), with the
  membership characterizations `mem_diagonalComplement_iff` and the `p ↦ z` bookkeeping
  `mem_range_diagonal_iff`.
* `AlgebraicGeometry.Over.coe_support_ker_diagonal` — the support of the kernel ideal
  sheaf `(δ C).left.ker` is exactly Δ (`Scheme.Hom.support_ker` plus closedness of the
  range); the set-level bridge between the ideal-theoretic and point-set pictures.
* `AlgebraicGeometry.Over.diagonal_preimage_productChart` — `δ ⁻¹ 𝔚(U, V) = U ⊓ V`, the
  chart bookkeeping along which B4 identifies the `δ`-preimage of the diagonal member.

## Design notes

Instance discipline: everything is keyed on the minimal hypothesis `[IsSeparated C.hom]`
(the challenge curve supplies it through `IsProper C.hom`); no smoothness, no geometric
conditions.  The `.left`-of-`⊗` vs `pullback` defeq is bridged only through
`Over.isPullback_left`; `tensorObj` is never unfolded.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace

namespace AlgebraicGeometry

namespace Over

variable {k : Type u} [Field k]

/-- **The diagonal of the curve square**: `δ C := lift (𝟙 C) (𝟙 C) : C ⟶ C ⊗ C`, the
graph of the identity, spelled through the landed section-of-a-point construction
`Over.sectionOfPoint` at the identity point (so all `sectionOfPoint` lemmas apply
verbatim). -/
noncomputable def diagonal (C : Over (Spec (.of k))) : C ⟶ C ⊗ C :=
  sectionOfPoint (𝟙 C)

variable (C : Over (Spec (.of k)))

/-- Unfolding lemma for `Over.diagonal`: the diagonal is the section of the projection
attached to the identity point. -/
lemma diagonal_def : diagonal C = sectionOfPoint (𝟙 C) :=
  rfl

/-- The diagonal followed by the first projection is the identity. -/
@[simp]
lemma diagonal_fst : diagonal C ≫ fst C C = 𝟙 C :=
  sectionOfPoint_fst (𝟙 C)

/-- The diagonal followed by the second projection is the identity. -/
@[simp]
lemma diagonal_snd : diagonal C ≫ snd C C = 𝟙 C :=
  sectionOfPoint_snd (𝟙 C)

/-- Scheme-level retraction: `(δ C).left ≫ (fst C C).left = 𝟙`. -/
lemma diagonal_left_fst_left : (diagonal C).left ≫ (fst C C).left = 𝟙 C.left := by
  rw [← Over.comp_left, diagonal_fst, Over.id_left]

/-- Scheme-level retraction: `(δ C).left ≫ (snd C C).left = 𝟙`. -/
lemma diagonal_left_snd_left : (diagonal C).left ≫ (snd C C).left = 𝟙 C.left := by
  rw [← Over.comp_left, diagonal_snd, Over.id_left]

/-- Pointwise retraction: the first projection undoes the diagonal on points. -/
lemma fst_base_diagonal_base (p : C.left) :
    (fst C C).left.base ((diagonal C).left.base p) = p := by
  have h : ((diagonal C).left ≫ (fst C C).left).base p = (𝟙 C.left : C.left ⟶ C.left).base p := by
    rw [diagonal_left_fst_left]
  exact h

/-- Pointwise retraction: the second projection undoes the diagonal on points. -/
lemma snd_base_diagonal_base (p : C.left) :
    (snd C C).left.base ((diagonal C).left.base p) = p := by
  have h : ((diagonal C).left ≫ (snd C C).left).base p = (𝟙 C.left : C.left ⟶ C.left).base p := by
    rw [diagonal_left_snd_left]
  exact h

/-- **The `p ↦ z` membership characterization** (worksheet D4): a point of the curve square
lies on the diagonal Δ iff it is the diagonal image of its own first projection.  The
witness point for `z ∈ Δ` is canonically `p := (fst C C).left.base z`. -/
theorem mem_range_diagonal_iff {z : (C ⊗ C).left} :
    z ∈ Set.range (diagonal C).left.base ↔
      (diagonal C).left.base ((fst C C).left.base z) = z :=
  ⟨fun ⟨p, hp⟩ => by rw [← hp, fst_base_diagonal_base], fun h => ⟨_, h⟩⟩

/-- The `δ`-preimage of a product chart is the intersection of its factors:
`δ ⁻¹ 𝔚(U, V) = U ⊓ V`.  This is the bookkeeping along which brick B4 computes the
`δ`-preimage of the diagonal member `𝔇(U) ⊆ 𝔚(U, U)`. -/
theorem diagonal_preimage_productChart (U V : C.left.Opens) :
    (diagonal C).left ⁻¹ᵁ productChart C C U V = U ⊓ V := by
  ext z
  change (diagonal C).left.base z ∈ productChart C C U V ↔ _
  rw [mem_productChart, fst_base_diagonal_base, snd_base_diagonal_base]
  rfl

section Separated

variable [IsSeparated C.hom]

/-- The second projection of the curve square is separated: it is the base change of the
separated `C.hom` along itself (through the bridge `Over.isPullback_left`). -/
instance isSeparated_snd_left : IsSeparated (snd C C).left :=
  MorphismProperty.of_isPullback (Over.isPullback_left C C) inferInstance

/-- **The diagonal is a closed immersion** (worksheet D4): `δ ≫ snd = 𝟙` is a closed
immersion, `(snd C C).left` is separated (base change of `C.hom`), and
`IsClosedImmersion.of_comp` cancels.  In particular `(δ C).left` is affine and
quasi-compact, so Mathlib's kernel ideal sheaf calculus (`Scheme.Hom.ker_apply`,
`Scheme.Hom.support_ker`) applies to it. -/
instance isClosedImmersion_diagonal_left : IsClosedImmersion (diagonal C).left := by
  haveI : IsClosedImmersion ((diagonal C).left ≫ (snd C C).left) := by
    rw [diagonal_left_snd_left]
    infer_instance
  exact IsClosedImmersion.of_comp (diagonal C).left (snd C C).left

/-- **The curve square is a separated scheme**: `(C ⊗ C).hom = snd ≫ C.hom` is a composite
of separated morphisms, and composing with the (affine, hence separated) structure morphism
of `Spec k` to the terminal scheme keeps it separated.  Consequence: intersections of
affine opens of `(C ⊗ C).left` are affine (`IsAffineOpen.inf`) — the overlap calculus of
the cross-chart ratio argument (worksheet D3). -/
instance isSeparated_left_tensor : Scheme.IsSeparated (C ⊗ C).left := by
  constructor
  haveI : IsSeparated ((C ⊗ C).hom) := by
    rw [← Over.w (snd C C)]
    infer_instance
  rw [← Limits.terminal.comp_from ((C ⊗ C).hom)]
  infer_instance

/-- **The diagonal Δ is closed** in the curve square. -/
theorem isClosed_range_diagonal : IsClosed (Set.range (diagonal C).left.base) :=
  (diagonal C).left.isClosedEmbedding.isClosed_range

/-- **The complement of the diagonal**, as an open of the curve square: the off-diagonal
member of the diagonal cover (worksheet D4), on which the local equation of the diagonal
divisor is `1`. -/
noncomputable def diagonalComplement : (C ⊗ C).left.Opens :=
  ⟨(Set.range (diagonal C).left.base)ᶜ, (isClosed_range_diagonal C).isOpen_compl⟩

/-- Membership in the diagonal complement is non-membership in the range of the
diagonal. -/
lemma mem_diagonalComplement_iff {z : (C ⊗ C).left} :
    z ∈ diagonalComplement C ↔ z ∉ Set.range (diagonal C).left.base :=
  Iff.rfl

/-- Membership in the diagonal complement, through the `p ↦ z` characterization: `z ∉ Δ`
iff the diagonal image of its first projection differs from `z`. -/
lemma mem_diagonalComplement_iff_ne {z : (C ⊗ C).left} :
    z ∈ diagonalComplement C ↔ (diagonal C).left.base ((fst C C).left.base z) ≠ z := by
  rw [mem_diagonalComplement_iff, mem_range_diagonal_iff]

/-- **The support of the kernel ideal sheaf of the diagonal is exactly Δ**: the support is
the closure of the range (`Scheme.Hom.support_ker`), and the range is closed.  This is the
set-level bridge between the intrinsic invariant `(δ C).left.ker` (worksheet D3) and the
point-set diagonal; B4 combines it with the per-chart kernel computation to identify
`𝔇(U) ⊓ Δᶜ` with the basic open of the local equation. -/
theorem coe_support_ker_diagonal :
    (((diagonal C).left.ker).support : Set (C ⊗ C).left)
      = Set.range (diagonal C).left.base := by
  rw [Scheme.Hom.support_ker, (isClosed_range_diagonal C).closure_eq]

end Separated

end Over

end AlgebraicGeometry
