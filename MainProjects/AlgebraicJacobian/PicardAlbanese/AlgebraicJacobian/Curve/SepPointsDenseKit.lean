/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.SeparablyClosedPoints
import AlgebraicJacobian.Cohomology.RelativeTwoCover

/-!
# DAT-B B-2 (kit) — the base-changed rational point and its evaluations

The vocabulary half of the B-2 density brick (`informal/w4-datb-worksheet.md` §1.5;
keystone in `Curve/SepPointsDense.lean`):

* `AlgebraicGeometry.tensorPointEval` — the pure-algebra evaluation `A ⊗[k] L →ₐ[k] L`
  induced by a `k`-point `φ : A →ₐ[k] k`, with the coordinate reading
  `repr_tensorPointEval` and the **linear-independence heart**
  `exists_algHom_tensorPointEval_ne_zero` (a nonzero tensor has a coordinate `a ≠ 0`
  such that every evaluation with `φ a ≠ 0` is nonzero — via `Module.Basis.baseChange`
  coordinates in any `k`-basis of `L`).
* `AlgebraicGeometry.Over.rationalPointBaseChange` — the base change of a rational
  point `p : Spec k ⟶ C.left` (a section of the structure map) to an `L`-point of the
  relative curve, with the two characterizing triangles
  `rationalPointBaseChange_fst`/`_snd` (the I-0243 named-def pattern; `_snd` is the
  rationality certificate B-5 consumes).  The codomain is spelled
  `(C ⊗ overSpec k L).left` (definitionally `relCurve C L`) so every `appLE` composite
  stays in one spelling of the relative curve.
* `AlgebraicGeometry.Over.rationalPointEval` — evaluation of chart sections at a
  rational point, as a `k`-algebra map `Γ(C.left, U) →ₐ[k] k` (with the
  `Over.sectionsAlgebra` structure), nonvanishing on the section of a basic open
  containing the point (`rationalPointEval_ne_zero_of_mem_basicOpen`).
* the generic `appLE` transports `Scheme.Hom.appLE_congr_hom_kit` / `id_appLE_apply` and
  the one-point-spectrum inclusion `top_le_preimage_of_closedPoint_mem` — the
  equation-`have` discipline pieces (I-0232(b)/I-0238(d)).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra

/-! ## The tensor linear-independence heart (pure algebra) -/

section TensorHeart

variable {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  {L : Type u} [Field L] [Algebra k L]

/-- **Evaluation of a base-changed function at a `k`-point**: the `k`-algebra map
`A ⊗[k] L →ₐ[k] L` induced by `φ : A →ₐ[k] k` on the first factor,
`a ⊗ c ↦ φ(a) • c`.  The algebraic shadow of evaluating a section of the base-changed
chart at the base change of a rational point. -/
noncomputable def tensorPointEval (φ : A →ₐ[k] k) : A ⊗[k] L →ₐ[k] L :=
  (Algebra.TensorProduct.lid k L).toAlgHom.comp
    (Algebra.TensorProduct.map φ (AlgHom.id k L))

@[simp]
lemma tensorPointEval_tmul (φ : A →ₐ[k] k) (a : A) (c : L) :
    tensorPointEval φ (a ⊗ₜ c) = φ a • c := by
  simp [tensorPointEval]

/-- The `L`-coordinates of `tensorPointEval φ G` in a `k`-basis `b` of `L` are the
`φ`-images of the `A`-coordinates of `G` in the base-changed basis `b.baseChange A`. -/
lemma repr_tensorPointEval {ι : Type u} (b : Module.Basis ι k L) (φ : A →ₐ[k] k)
    (G : A ⊗[k] L) (i : ι) :
    b.repr (tensorPointEval φ G) i = φ ((b.baseChange A).repr G i) := by
  induction G with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul x y =>
    rw [tensorPointEval_tmul, Module.Basis.baseChange_repr_tmul, map_smul,
      Finsupp.smul_apply, map_smul]
    simp [smul_eq_mul, mul_comm]

/-- **The linear-independence heart** (worksheet §1.5 step 3): a nonzero
`F ∈ A ⊗[k] L` has a coordinate `a ≠ 0` in `A` such that every `k`-point evaluation
`φ : A →ₐ[k] k` with `φ a ≠ 0` sends `F` to a nonzero element of `L`.  Coordinates in
`Module.Basis.baseChange` of any `k`-basis of `L`; the evaluated coordinates are read
off by `repr_tensorPointEval`. -/
theorem exists_algHom_tensorPointEval_ne_zero {F : A ⊗[k] L} (hF : F ≠ 0) :
    ∃ a : A, a ≠ 0 ∧ ∀ φ : A →ₐ[k] k, φ a ≠ 0 → tensorPointEval (L := L) φ F ≠ 0 := by
  classical
  set b := Module.Basis.ofVectorSpace k L with hb
  have hrepr : (b.baseChange A).repr F ≠ 0 := fun h =>
    hF (by simpa using congrArg (b.baseChange A).repr.symm h)
  obtain ⟨i₀, hi₀⟩ := Finsupp.ne_iff.mp hrepr
  rw [Finsupp.coe_zero, Pi.zero_apply] at hi₀
  refine ⟨(b.baseChange A).repr F i₀, hi₀, fun φ hφ h0 => ?_⟩
  have hcoord := repr_tensorPointEval b φ F i₀
  rw [h0] at hcoord
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoord
  exact hφ hcoord.symm

end TensorHeart

/-! ## The base-changed rational point -/

section BaseChangePoint

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  (L : Type u) [Field L] [Algebra k L]

/-- **The base change of a rational point** `p : Spec k ⟶ C.left` (a section of the
structure map) to an `L`-point of the relative curve: the pairing
`⟨str ≫ p, 𝟙⟩ : Spec L ⟶ C ⊗ Spec L` in `Over (Spec k)`.  The codomain
`(C ⊗ overSpec k L).left` is definitionally `relCurve C L`.  Characterized by the two
triangles `rationalPointBaseChange_fst`/`_snd` (the I-0243 named-def pattern). -/
noncomputable def Over.rationalPointBaseChange (p : Spec (.of k) ⟶ C.left)
    (hp : p ≫ C.hom = 𝟙 (Spec (.of k))) : Spec (.of L) ⟶ (C ⊗ overSpec k L).left :=
  (CartesianMonoidalCategory.lift
    (Over.homMk ((overSpec k L).hom ≫ p)
      (by rw [Category.assoc, hp, Category.comp_id]))
    (𝟙 (overSpec k L))).left

/-- The base-changed point lies over `p`: composing with the first projection is the
structure map of `Spec L` followed by `p`. -/
@[reassoc]
lemma Over.rationalPointBaseChange_fst (p : Spec (.of k) ⟶ C.left)
    (hp : p ≫ C.hom = 𝟙 (Spec (.of k))) :
    Over.rationalPointBaseChange C L p hp ≫ (fst C (overSpec k L)).left =
      Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ p :=
  congrArg (fun φ : overSpec k L ⟶ C => φ.left)
    (CartesianMonoidalCategory.lift_fst _ _)

/-- **The rationality certificate**: the base-changed point is a section of the
structure map of the relative curve over `Spec L` (the second projection).  This is the
input from which B-5 extracts `residueDeg L = 1` at the point. -/
@[reassoc]
lemma Over.rationalPointBaseChange_snd (p : Spec (.of k) ⟶ C.left)
    (hp : p ≫ C.hom = 𝟙 (Spec (.of k))) :
    Over.rationalPointBaseChange C L p hp ≫ (snd C (overSpec k L)).left =
      𝟙 (Spec (.of L)) :=
  congrArg (fun φ : overSpec k L ⟶ overSpec k L => φ.left)
    (CartesianMonoidalCategory.lift_snd _ _)

end BaseChangePoint

/-! ## Evaluation at a rational point -/

section Eval

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

/-- `appLE` is invariant under an equality of morphisms (the inclusion witness is
proof-irrelevant); public form of the `RelativeSectionsLinear` private helper.  Named
`_kit` to avoid a full-root collision with the established
`AlgebraicGeometry.Scheme.Hom.appLE_congr_hom` in `Picard/PicEtSections`, which has a
different argument convention (explicit `V U e e'`). -/
lemma Scheme.Hom.appLE_congr_hom_kit {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    {U : Y.Opens} {W : X.Opens} (e : W ≤ f ⁻¹ᵁ U) :
    f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h; rfl

/-- The identity morphism acts trivially on top sections through `appLE`. -/
lemma Scheme.id_appLE (X : Scheme.{u}) (e : (⊤ : X.Opens) ≤ 𝟙 X ⁻¹ᵁ ⊤) :
    Scheme.Hom.appLE (𝟙 X) ⊤ ⊤ e = 𝟙 Γ(X, ⊤) :=
  (Scheme.Hom.appLE_eq_app (𝟙 X) (U := ⊤)).trans (Scheme.Hom.id_app ⊤)

/-- Elementwise form of `Scheme.id_appLE`. -/
lemma Scheme.id_appLE_apply {X : Scheme.{u}} (e : (⊤ : X.Opens) ≤ 𝟙 X ⁻¹ᵁ ⊤)
    (t : Γ(X, ⊤)) : Scheme.Hom.appLE (𝟙 X) ⊤ ⊤ e t = t :=
  DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Scheme.id_appLE X e)) t

/-- A morphism from the spectrum of a field lands inside any open containing the image
of the closed point. -/
lemma top_le_preimage_of_closedPoint_mem {K : Type u} [Field K] {X : Scheme.{u}}
    (p : Spec (.of K) ⟶ X) {U : X.Opens}
    (hmem : p.base (IsLocalRing.closedPoint K) ∈ U) : ⊤ ≤ p ⁻¹ᵁ U := by
  intro y _
  have hy : y = (IsLocalRing.closedPoint K) := Subsingleton.elim _ _
  subst hy
  exact hmem

/-- **Evaluation of chart sections at a rational point**: for a section
`p : Spec k ⟶ C.left` of the structure map with image in the open `U`, the `k`-algebra
map `Γ(C.left, U) →ₐ[k] k` reading a section at the point (with the
`Over.sectionsAlgebra` structure on the sections). -/
noncomputable def Over.rationalPointEval (p : Spec (.of k) ⟶ C.left)
    (hp : p ≫ C.hom = 𝟙 (Spec (.of k))) {U : C.left.Opens} (hple : ⊤ ≤ p ⁻¹ᵁ U) :
    Γ(C.left, U) →ₐ[k] k where
  toRingHom := (Scheme.ΓSpecIso (.of k)).hom.hom.comp (p.appLE U ⊤ hple).hom
  commutes' r := by
    change (Scheme.ΓSpecIso (.of k)).hom
      (p.appLE U ⊤ hple (algebraMap k Γ(C.left, U) r)) = algebraMap k k r
    have h1 : algebraMap k Γ(C.left, U) r =
        C.hom.appLE ⊤ U (le_top.trans (Scheme.Hom.preimage_top C.hom).ge)
          ((Scheme.ΓSpecIso (.of k)).inv r) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
        (Over.ofHom_algebraMap_sections C U)) r
    have hcomp : C.hom.appLE ⊤ U (le_top.trans (Scheme.Hom.preimage_top C.hom).ge) ≫
        p.appLE U ⊤ hple =
        Scheme.Hom.appLE (𝟙 (Spec (.of k))) ⊤ ⊤
          (Scheme.Hom.preimage_top (𝟙 (Spec (.of k)))).ge := by
      rw [Scheme.Hom.appLE_comp_appLE]
      exact Scheme.Hom.appLE_congr_hom_kit hp _
    have h2 : p.appLE U ⊤ hple
        (C.hom.appLE ⊤ U (le_top.trans (Scheme.Hom.preimage_top C.hom).ge)
          ((Scheme.ΓSpecIso (.of k)).inv r)) =
        Scheme.Hom.appLE (𝟙 (Spec (.of k))) ⊤ ⊤
          (Scheme.Hom.preimage_top (𝟙 (Spec (.of k)))).ge
          ((Scheme.ΓSpecIso (.of k)).inv r) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) _
    have h3 : (Scheme.ΓSpecIso (.of k)).hom ((Scheme.ΓSpecIso (.of k)).inv r) = r :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
        (Scheme.ΓSpecIso (.of k)).inv_hom_id) r
    calc (Scheme.ΓSpecIso (.of k)).hom
          (p.appLE U ⊤ hple (algebraMap k Γ(C.left, U) r))
        = (Scheme.ΓSpecIso (.of k)).hom
            (p.appLE U ⊤ hple
              (C.hom.appLE ⊤ U (le_top.trans (Scheme.Hom.preimage_top C.hom).ge)
                ((Scheme.ΓSpecIso (.of k)).inv r))) :=
          congrArg (fun t => (Scheme.ΓSpecIso (.of k)).hom (p.appLE U ⊤ hple t)) h1
      _ = (Scheme.ΓSpecIso (.of k)).hom
            (Scheme.Hom.appLE (𝟙 (Spec (.of k))) ⊤ ⊤
              (Scheme.Hom.preimage_top (𝟙 (Spec (.of k)))).ge
              ((Scheme.ΓSpecIso (.of k)).inv r)) :=
          congrArg (Scheme.ΓSpecIso (.of k)).hom h2
      _ = (Scheme.ΓSpecIso (.of k)).hom ((Scheme.ΓSpecIso (.of k)).inv r) :=
          congrArg (Scheme.ΓSpecIso (.of k)).hom (Scheme.id_appLE_apply _ _)
      _ = r := h3
      _ = algebraMap k k r := rfl

@[simp]
lemma Over.rationalPointEval_apply (p : Spec (.of k) ⟶ C.left)
    (hp : p ≫ C.hom = 𝟙 (Spec (.of k))) {U : C.left.Opens} (hple : ⊤ ≤ p ⁻¹ᵁ U)
    (s : Γ(C.left, U)) :
    Over.rationalPointEval C p hp hple s =
      (Scheme.ΓSpecIso (.of k)).hom (p.appLE U ⊤ hple s) :=
  rfl

/-- The evaluation at a rational point inside a basic open does not vanish on the
defining section: `p ∈ D(a)` forces `(ev_p) a ≠ 0`. -/
lemma Over.rationalPointEval_ne_zero_of_mem_basicOpen (p : Spec (.of k) ⟶ C.left)
    (hp : p ≫ C.hom = 𝟙 (Spec (.of k))) {U : C.left.Opens} (hple : ⊤ ≤ p ⁻¹ᵁ U)
    {a : Γ(C.left, U)}
    (hmem : p.base (IsLocalRing.closedPoint k) ∈ C.left.basicOpen a) :
    Over.rationalPointEval C p hp hple a ≠ 0 := by
  intro h0
  -- the section evaluates to zero, so its basic open on `Spec k` is empty …
  have happ : p.appLE U ⊤ hple a = 0 := by
    apply (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.injective
    rw [map_zero]
    exact h0
  -- … but it contains the closed point.
  have hpre : IsLocalRing.closedPoint k ∈ p ⁻¹ᵁ C.left.basicOpen a := hmem
  rw [Scheme.preimage_basicOpen] at hpre
  have hres : IsLocalRing.closedPoint k ∈
      (Spec (.of k)).basicOpen (p.appLE U ⊤ hple a) := by
    have heq : (Spec (.of k)).basicOpen (p.appLE U ⊤ hple a) =
        ⊤ ⊓ (Spec (.of k)).basicOpen (p.app U a) := by
      have h : p.appLE U ⊤ hple a =
          (Spec (.of k)).presheaf.map (homOfLE hple).op (p.app U a) := rfl
      rw [h, Scheme.basicOpen_res]
    rw [heq]
    exact ⟨trivial, hpre⟩
  rw [happ, Scheme.basicOpen_zero] at hres
  exact hres

end Eval

end AlgebraicGeometry
