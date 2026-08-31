/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.UnitDescentBaseChange
import AlgebraicJacobian.Picard.EffectivityPieces

/-!
# The per-piece descent datum ((C2) effectivity, brick E2 — the algebraic core)

The (C2) effectivity campaign descends a rigidified class `L` on the curve `X_B` over the
étale cover `Spec B` along the cover inclusion `cg`, piece by piece over a `cg`-saturated
affine cover `{V}` of the base curve `X_A` (`AlgebraicJacobian.Picard.EffectivityPieces`,
brick E0).  On a piece `V` the cover ring is `M := Γ(V) ⊗[A] B` (`Over.pieceEquiv`), and
the descent along `Γ(V) → M` is governed by the σ-normalized comparison cochain `θ` of
`AlgebraicGeometry.NormalizedCechComparison` (brick E1) restricted to the piece.  This
file supplies the **pure-algebra bridge** the per-piece descent runs on: the
identification of the descent-cocycle ring with the geometric double-base ring, and the
extraction of a `Module.IsDescentCocycle` from a comparison unit in geometric
coordinates.

For a commutative ring `A`, an `A`-algebra `S` (the base-piece ring `Γ(V)`) and an
`A`-algebra `B` (the étale cover), writing `M := S ⊗[A] B` for the cover-piece ring:

* `Algebra.TensorProduct.pieceDescentEquiv A S B : (M ⊗[S] M) ≃ₐ[S] S ⊗[A] (B ⊗[A] B)` —
  **the descent-cocycle ring identification** (D2's frontier item 1): the ring
  `M ⊗[S] M` in which a `Module.IsDescentCocycle` lives is, on the nose, the base change
  to `S` of the descent-cocycle ring `B ⊗[A] B` of the whole cover.  On pure tensors
  `(s₁ ⊗ b₁) ⊗ (s₂ ⊗ b₂) ↦ (s₂ * s₁) ⊗ (b₁ ⊗ b₂)` (`pieceDescentEquiv_tmul`);
* `Algebra.TensorProduct.pieceDescentTripleEquiv` — the triple analogue
  `M ⊗[S] (M ⊗[S] M) ≃ₐ[S] S ⊗[A] (B ⊗[A] (B ⊗[A] B))`, carrying the Amitsur cocycle
  identity;
* `pieceDescentEquiv_lmul'` / `pieceDescentTripleEquiv_descentFace₂₃/₁₂/₁₃` — **the
  coprojection–face compatibility**: the identification intertwines the multiplication
  `lmul'` and the three simplicial cofaces `descentFace` of `M ⊗[S] M` with the
  base-changed maps `id_S ⊗ lmul'` and `id_S ⊗ descentFace` of `S ⊗[A] (B ⊗[A] B)`.

The payload is the extraction:

* `Module.comparisonDescentUnit A S B v : (M ⊗[S] M)ˣ` for a **comparison unit**
  `v : (S ⊗[A] (B ⊗[A] B))ˣ` — the value `pieceEquiv` transports the piece restriction of
  the E1 comparison to — and
* `Module.isDescentCocycle_comparisonDescentUnit`: if `v` is diagonal-normalized
  (`id_S ⊗ lmul'` sends it to `1` — the cochain source is
  `Over.normalizedComparison_diagonal_eq_one`) and satisfies the Amitsur cocycle identity
  through the three cofaces (the cochain source is `NormalizedCechComparison.coherent`),
  then `comparisonDescentUnit A S B v` is a `Module.IsDescentCocycle` over `S → M`;
* `Module.comparisonDescentClass` — its Picard class `∈ CommRing.Pic S`, the descended
  per-piece class `M_V` (for faithfully flat `A → B`).

## The frontier consumed by E3

Producing the comparison unit `v` from the piece restriction of `θ` is a gluing step
(the restricted `θ`, twisted by a trivialization of `L` on the affine piece, glues to a
single unit of `Γ(cg⁻¹ V ×_{Spec A} Spec (B ⊗[A] B))` by the `𝒪ˣ`-sheaf axiom, exactly as
the (C1) `witnessBasicSection` construction of `AlgebraicJacobian.Picard.WitnessCorrection`
does for the trivial-on-cover case); the diagonal and Amitsur hypotheses on `v` are then
the restrictions of `Over.normalizedComparison_diagonal_eq_one` and
`NormalizedCechComparison.coherent`.  The restriction compatibility on overlaps `W ≤ V`
(D2 item 3b) is `Module.IsDescentCocycle.picClass_baseChange`
(`AlgebraicJacobian.Descent.UnitDescentBaseChange`) along `Over.resAlgHomA : Γ(V) →ₐ[A]
Γ(W)`, once the two comparison units are related by base change through
`Over.pieceRingEquiv_naturality`.
-/

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace Algebra.TensorProduct

variable (A S B : Type u) [CommRing A] [CommRing S] [CommRing B] [Algebra A S] [Algebra A B]

/-! ## The descent-cocycle ring identification -/

/-- **The descent-cocycle ring identification** ((C2) effectivity, brick E2): for an
`A`-algebra `S` (the base-piece ring) and an `A`-algebra `B` (the cover), the ring
`(S ⊗[A] B) ⊗[S] (S ⊗[A] B)` in which a `Module.IsDescentCocycle` over `S → S ⊗[A] B`
lives is the base change to `S` of the whole-cover descent-cocycle ring `B ⊗[A] B`:
`(S ⊗[A] B) ⊗[S] (S ⊗[A] B) ≃ₐ[S] S ⊗[A] (B ⊗[A] B)`.  The composite of mathlib's
`cancelBaseChange` (cancelling the middle `S`) and `assoc`. -/
noncomputable def pieceDescentEquiv :
    (S ⊗[A] B) ⊗[S] (S ⊗[A] B) ≃ₐ[S] S ⊗[A] (B ⊗[A] B) :=
  (Algebra.TensorProduct.cancelBaseChange A S S (S ⊗[A] B) B).trans
    (Algebra.TensorProduct.assoc A A S S B B)

@[simp]
lemma pieceDescentEquiv_tmul (s₁ s₂ : S) (b₁ b₂ : B) :
    pieceDescentEquiv A S B ((s₁ ⊗ₜ[A] b₁) ⊗ₜ[S] (s₂ ⊗ₜ[A] b₂))
      = (s₂ * s₁) ⊗ₜ[A] (b₁ ⊗ₜ[A] b₂) := by
  simp only [pieceDescentEquiv, AlgEquiv.trans_apply, cancelBaseChange_tmul,
    TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.assoc_tmul]

/-- The first coprojection step of `pieceDescentTripleEquiv`, on a pure `S`-tensor:
`congr (refl) pieceDescentEquiv (a ⊗ x) = a ⊗ pieceDescentEquiv x`. -/
private lemma congr_refl_pieceDescentEquiv (a : S ⊗[A] B)
    (x : (S ⊗[A] B) ⊗[S] (S ⊗[A] B)) :
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := S) (A₁ := S ⊗[A] B))
        (pieceDescentEquiv A S B)) (a ⊗ₜ[S] x)
      = a ⊗ₜ[S] pieceDescentEquiv A S B x := by
  rw [congr_apply, Algebra.TensorProduct.map_tmul]; rfl

/-- **The triple descent-cocycle ring identification**: the base of the Amitsur cocycle
identity, `(S ⊗[A] B) ⊗[S] ((S ⊗[A] B) ⊗[S] (S ⊗[A] B)) ≃ₐ[S] S ⊗[A] (B ⊗[A] (B ⊗[A] B))`. -/
noncomputable def pieceDescentTripleEquiv :
    (S ⊗[A] B) ⊗[S] ((S ⊗[A] B) ⊗[S] (S ⊗[A] B))
      ≃ₐ[S] S ⊗[A] (B ⊗[A] (B ⊗[A] B)) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (R := S) (A₁ := S ⊗[A] B))
      (pieceDescentEquiv A S B)).trans
    ((Algebra.TensorProduct.cancelBaseChange A S S (S ⊗[A] B) (B ⊗[A] B)).trans
      (Algebra.TensorProduct.assoc A A S S B (B ⊗[A] B)))

@[simp]
lemma pieceDescentTripleEquiv_tmul (s₀ s₁ s₂ : S) (b₀ b₁ b₂ : B) :
    pieceDescentTripleEquiv A S B
        ((s₀ ⊗ₜ[A] b₀) ⊗ₜ[S] ((s₁ ⊗ₜ[A] b₁) ⊗ₜ[S] (s₂ ⊗ₜ[A] b₂)))
      = (s₂ * s₁ * s₀) ⊗ₜ[A] (b₀ ⊗ₜ[A] (b₁ ⊗ₜ[A] b₂)) := by
  rw [pieceDescentTripleEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    congr_refl_pieceDescentEquiv, pieceDescentEquiv_tmul, cancelBaseChange_tmul,
    TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.assoc_tmul]

/-! ## The coprojection–face compatibility -/

/-- **`lmul'` compatibility**: the identification intertwines the multiplication of
`M ⊗[S] M` (`M := S ⊗[A] B`) with the base-changed multiplication `id_S ⊗ lmul'` of
`S ⊗[A] (B ⊗[A] B)`.  The cochain-level source of the `lmul'_eq_one` normalization. -/
lemma pieceDescentEquiv_lmul' (y : (S ⊗[A] B) ⊗[S] (S ⊗[A] B)) :
    Algebra.TensorProduct.lmul' S (S := S ⊗[A] B) y
      = Algebra.TensorProduct.map (AlgHom.id S S) (Algebra.TensorProduct.lmul' A)
          (pieceDescentEquiv A S B y) := by
  induction y with
  | tmul m₁ m₂ => induction m₁ with
    | tmul s₁ b₁ => induction m₂ with
      | tmul s₂ b₂ =>
        rw [pieceDescentEquiv_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.lmul'_apply_tmul]
        ring_nf
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | zero => simp only [map_zero]

/-- **`descentFace₂₃` compatibility**: the triple identification intertwines the coface
`descentFace₂₃` of `M ⊗[S] M` with the base-changed coface `id_S ⊗ descentFace₂₃`. -/
lemma pieceDescentTripleEquiv_descentFace₂₃ (y : (S ⊗[A] B) ⊗[S] (S ⊗[A] B)) :
    pieceDescentTripleEquiv A S B (Module.descentFace₂₃ S (S ⊗[A] B) y)
      = Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentFace₂₃ A B)
          (pieceDescentEquiv A S B y) := by
  induction y with
  | tmul m₁ m₂ => induction m₁ with
    | tmul s₁ b₁ => induction m₂ with
      | tmul s₂ b₂ =>
        rw [pieceDescentEquiv_tmul, Module.descentFace₂₃_apply,
          Algebra.TensorProduct.one_def, pieceDescentTripleEquiv_tmul,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Module.descentFace₂₃_apply]
        ring_nf
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | zero => simp only [map_zero]

/-- **`descentFace₁₂` compatibility**. -/
lemma pieceDescentTripleEquiv_descentFace₁₂ (y : (S ⊗[A] B) ⊗[S] (S ⊗[A] B)) :
    pieceDescentTripleEquiv A S B (Module.descentFace₁₂ S (S ⊗[A] B) y)
      = Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentFace₁₂ A B)
          (pieceDescentEquiv A S B y) := by
  induction y with
  | tmul m₁ m₂ => induction m₁ with
    | tmul s₁ b₁ => induction m₂ with
      | tmul s₂ b₂ =>
        rw [pieceDescentEquiv_tmul, Module.descentFace₁₂_tmul,
          Algebra.TensorProduct.one_def, pieceDescentTripleEquiv_tmul,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Module.descentFace₁₂_tmul]
        ring_nf
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | zero => simp only [map_zero]

/-- **`descentFace₁₃` compatibility**. -/
lemma pieceDescentTripleEquiv_descentFace₁₃ (y : (S ⊗[A] B) ⊗[S] (S ⊗[A] B)) :
    pieceDescentTripleEquiv A S B (Module.descentFace₁₃ S (S ⊗[A] B) y)
      = Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentFace₁₃ A B)
          (pieceDescentEquiv A S B y) := by
  induction y with
  | tmul m₁ m₂ => induction m₁ with
    | tmul s₁ b₁ => induction m₂ with
      | tmul s₂ b₂ =>
        rw [pieceDescentEquiv_tmul, Module.descentFace₁₃_tmul,
          Algebra.TensorProduct.one_def, pieceDescentTripleEquiv_tmul,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Module.descentFace₁₃_tmul]
        ring_nf
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | zero => simp only [map_zero]

end Algebra.TensorProduct

namespace Module

open Algebra.TensorProduct

/-! ## The cover-pullback triviality of a descended class

The image of the Picard class of a descent cocycle under base change to the cover is
trivial: the descended module base-changes back to the cover ring itself. -/

/-- **The cover-pullback of a descended class is trivial**: for a faithfully flat cover
`R → T`, base change of the Picard class of a descent cocycle back up to `T` is `1`, since
the descended module base-changes to `T` through `Module.DescentDatum.descentEquiv`.  On a
`cg`-saturated affine piece `V` (with `R = Γ(V)`, `T = Γ(V) ⊗[A] B ≅ Γ(cg⁻¹ V)`) this is
the provable half of the D2 item-3a cg-pullback recovery: the descended class `M_V` pulls
back to the trivial class on the cover piece. -/
theorem IsDescentCocycle.mapAlgebra_picClass_eq_one {R T : Type u} [CommRing R] [CommRing T]
    [Algebra R T] [Module.FaithfullyFlat R T] {u : (T ⊗[R] T)ˣ}
    (hu : Module.IsDescentCocycle u) :
    CommRing.Pic.mapAlgebra R T hu.picClass = 1 := by
  rw [Module.IsDescentCocycle.picClass, CommRing.Pic.mapAlgebra_apply,
    CommRing.Pic.mk_eq_one_iff]
  exact ⟨(LinearEquiv.baseChange R T (CommRing.Pic.mk R hu.descended).AsModule hu.descended
      (CommRing.Pic.mk.linearEquiv R hu.descended)).trans
    (Module.DescentDatum.ofUnit u hu).descentEquiv⟩

variable (A S B : Type u) [CommRing A] [CommRing S] [CommRing B] [Algebra A S] [Algebra A B]

/-! ## The per-piece descent unit and its cocycle property -/

/-- **The per-piece descent unit** ((C2) effectivity, brick E2): the unit of
`(S ⊗[A] B) ⊗[S] (S ⊗[A] B)` corresponding to a comparison unit
`v : (S ⊗[A] (B ⊗[A] B))ˣ` under the descent-cocycle ring identification
`pieceDescentEquiv`.  On a piece `V`, `v` is the value `Over.pieceEquiv` transports the
piece restriction of the E1 comparison `θ` to. -/
noncomputable def comparisonDescentUnit (v : (S ⊗[A] (B ⊗[A] B))ˣ) :
    ((S ⊗[A] B) ⊗[S] (S ⊗[A] B))ˣ :=
  Units.map (pieceDescentEquiv A S B).symm.toAlgHom.toRingHom.toMonoidHom v

@[simp]
lemma pieceDescentEquiv_comparisonDescentUnit_val (v : (S ⊗[A] (B ⊗[A] B))ˣ) :
    pieceDescentEquiv A S B (comparisonDescentUnit A S B v).val = v.val := by
  change pieceDescentEquiv A S B ((pieceDescentEquiv A S B).symm v.val) = v.val
  exact AlgEquiv.apply_symm_apply _ _

/-- **The per-piece descent unit of a coherent comparison unit is a descent 1-cocycle**
((C2) effectivity, brick E2).  The diagonal normalization is the `id_S ⊗ lmul'`
hypothesis `hlmul` — the cochain source is `Over.normalizedComparison_diagonal_eq_one`
restricted to the piece; the cocycle identity is the Amitsur identity through the three
cofaces `hcoc` — the cochain source is `NormalizedCechComparison.coherent`.  Both are
transported through the descent-cocycle ring identifications by the coprojection–face
compatibility lemmas. -/
theorem isDescentCocycle_comparisonDescentUnit {v : (S ⊗[A] (B ⊗[A] B))ˣ}
    (hlmul : Algebra.TensorProduct.map (AlgHom.id S S) (Algebra.TensorProduct.lmul' A) v.val
      = 1)
    (hcoc : Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentFace₂₃ A B) v.val
          * Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentFace₁₂ A B) v.val
        = Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentFace₁₃ A B) v.val) :
    Module.IsDescentCocycle (comparisonDescentUnit A S B v) where
  lmul'_eq_one := by
    change Algebra.TensorProduct.lmul' S (S := S ⊗[A] B)
      (comparisonDescentUnit A S B v).val = 1
    rw [pieceDescentEquiv_lmul', pieceDescentEquiv_comparisonDescentUnit_val, hlmul]
  cocycle := by
    apply (pieceDescentTripleEquiv A S B).injective
    rw [map_mul, pieceDescentTripleEquiv_descentFace₂₃,
      pieceDescentTripleEquiv_descentFace₁₂, pieceDescentTripleEquiv_descentFace₁₃,
      pieceDescentEquiv_comparisonDescentUnit_val, hcoc]

/-! ## The descended per-piece Picard class -/

variable [Module.FaithfullyFlat A B]

/-- **The descended per-piece class `M_V`** ((C2) effectivity, brick E2): for a faithfully
flat cover `A → B` and a coherent comparison unit `v`, the Picard class over the base
piece `S = Γ(V)` of the module descended from the per-piece descent cocycle.  Its image
under `CommRing.Pic S → CommRing.Pic (S ⊗[A] B)` is trivial (the descent recovers the
cover-piece ring `M = S ⊗[A] B` twisted by the comparison), so the tracked cg-pullback
recovery of D2 item 3a is the identification of `L` restricted to the piece with the
comparison twist; the restriction compatibility on overlaps (D2 item 3b) is
`Module.IsDescentCocycle.picClass_baseChange`. -/
noncomputable def comparisonDescentClass {v : (S ⊗[A] (B ⊗[A] B))ˣ}
    (hlmul : Algebra.TensorProduct.map (AlgHom.id S S) (Algebra.TensorProduct.lmul' A) v.val
      = 1)
    (hcoc : Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentFace₂₃ A B) v.val
          * Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentFace₁₂ A B) v.val
        = Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentFace₁₃ A B) v.val) :
    CommRing.Pic S :=
  (isDescentCocycle_comparisonDescentUnit A S B hlmul hcoc).picClass

/-- **The cg-pullback recovery of the descended per-piece class** (D2 item 3a, provable
half): the descended class `comparisonDescentClass` pulls back to the trivial class on the
cover-piece ring `S ⊗[A] B ≅ Γ(cg⁻¹ V)`.  The full D2 item-3a — that this trivial
cover-pullback *is* the class of `L` restricted to the piece — is the statement that the
comparison unit `v` trivializes `L` on the piece, established when `v` is produced from the
piece restriction of the E1 comparison (the frontier consumed by E3). -/
theorem mapAlgebra_comparisonDescentClass_eq_one {v : (S ⊗[A] (B ⊗[A] B))ˣ}
    (hlmul : Algebra.TensorProduct.map (AlgHom.id S S) (Algebra.TensorProduct.lmul' A) v.val
      = 1)
    (hcoc : Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentFace₂₃ A B) v.val
          * Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentFace₁₂ A B) v.val
        = Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentFace₁₃ A B) v.val) :
    CommRing.Pic.mapAlgebra S (S ⊗[A] B) (comparisonDescentClass A S B hlmul hcoc) = 1 :=
  (isDescentCocycle_comparisonDescentUnit A S B hlmul hcoc).mapAlgebra_picClass_eq_one

end Module

/-! ## The geometric descent-cocycle ring identification -/

namespace AlgebraicGeometry

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace

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
local notation "cg" => (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left
set_option quotPrecheck false in
local notation "cgq" =>
  (C ◁ Over.overSpecMap ((Algebra.ofId A (B ⊗[A] B)).restrictScalars k)).left

namespace Over

-- The base-piece `A`-algebra structure and the cover-piece `Γ(V)`-algebra structure of E0.
attribute [local instance] Over.sectionsAlgebraA Over.pieceCoverAlgebra

/-- **The geometric descent-cocycle ring identification** ((C2) effectivity, brick E2 —
the E0 → E2 frontier realized on the curve pieces).  For a `cg`-saturated affine piece
`V` of the base curve `X_A`, with cover-piece ring `Γ(cg⁻¹ V)` over the base-piece ring
`Γ(V)`, the descent-cocycle ring `Γ(cg⁻¹ V) ⊗[Γ(V)] Γ(cg⁻¹ V)` in which a
`Module.IsDescentCocycle` over `Γ(V) → Γ(cg⁻¹ V)` lives is `Γ(V) ⊗[A] (B ⊗[A] B)`, via
the E0 identification `Over.pieceEquiv` on each factor and the base-changed
`Algebra.TensorProduct.pieceDescentEquiv`. -/
noncomputable def pieceDescentTensorEquiv {U : (XA).Opens} (hU : IsAffineOpen U) :
    Γ(XB, (cg) ⁻¹ᵁ U) ⊗[Γ(XA, U)] Γ(XB, (cg) ⁻¹ᵁ U)
      ≃ₐ[Γ(XA, U)] Γ(XA, U) ⊗[A] (B ⊗[A] B) :=
  (Algebra.TensorProduct.congr (Over.pieceEquiv C hU) (Over.pieceEquiv C hU)).trans
    (Algebra.TensorProduct.pieceDescentEquiv A Γ(XA, U) B)

/-- **The geometric descent-cocycle ring identification, cover-piece form**: the
descent-cocycle ring `Γ(cg⁻¹ V) ⊗[Γ(V)] Γ(cg⁻¹ V)` is the section ring
`Γ(cgq⁻¹ V)` of the curve over the descent-cocycle base `Spec (B ⊗[A] B)`, through the
`R = B ⊗[A] B` instance of the E0 piece identification (`Over.pieceEquiv`, R-uniform).
This is the ring on whose spectrum the piece restriction of the E1 comparison lives. -/
noncomputable def pieceDescentCoverEquiv {U : (XA).Opens} (hU : IsAffineOpen U) :
    Γ(XB, (cg) ⁻¹ᵁ U) ⊗[Γ(XA, U)] Γ(XB, (cg) ⁻¹ᵁ U)
      ≃ₐ[Γ(XA, U)] Γ(Xq, (cgq) ⁻¹ᵁ U) :=
  (pieceDescentTensorEquiv C hU).trans
    (Over.pieceEquiv (A := A) (B := B ⊗[A] B) C hU).symm

end Over

end AlgebraicGeometry
