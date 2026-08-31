/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.SepPointsDenseKit

/-!
# DAT-B B-2 — density of base-changed `K_s`-points in the relative curve

The separable-point density transfer of the DAT-B worksheet
(`informal/w4-datb-worksheet.md` §1.5, COV-3): over a **separably closed** base field `k`
and any field extension `L ⊇ k`, the base changes of the `k`-rational points of the curve
`C` are dense in the relative curve `C_L = relCurve C L`: every nonempty open contains
one (`Over.dense_baseChange_rationalPoints`, the keystone).

The pointwise coverage theorem (B-5, worksheet §1.2 step 5) instantiates the admissible
point oracle of B-1 (`RiemannRoch/CoverageDrop.lean`) with these points at the fibre
field `L`; the vocabulary (the base-changed point, its triangles, the evaluations, the
tensor linear-independence heart) is in `Curve/SepPointsDenseKit.lean`.

## Route (worksheet §1.5 — elementary, no flatness-openness)

1. `C(k)` is dense in `C.left`: DAT-P (`Over.exists_rationalPoint_mem`).
2. A `k`-rational point base-changes to an `L`-point of `C_L`
   (`Over.rationalPointBaseChange`, kit).
3. The trace argument: on an affine chart `U` the sections of the base-changed chart
   are `Γ(U) ⊗_k L` on the nose (`Over.sectionsBaseChange`); reading a base-changed
   section at the base-changed point is `tensorPointEval` of the `k`-valued evaluation
   at the point (`gammaSpecIso_appLE_sectionsBaseChange`, the crux — proved on pure
   tensors through the two projection triangles and `ΓSpecIso`-naturality); a nonempty
   open contains a chart basic open `D(f)`, the nonzero coordinate `a` of `f` has
   nonempty `D(a)` in the **reduced** (integral) curve, DAT-P puts a rational point
   there, and its base change lands in `D(f)`.

The residue-degree bookkeeping of the base-changed point (`residueDeg L = 1`, the `hP`
oracle input of B-1) is *not* proved here; B-5 extracts it from the rationality
certificate `rationalPointBaseChange_snd`.  Every `appLE` transport below is an
equation-`have` consumed by `exact`/`DFunLike.congr_fun (congrArg CommRingCat.Hom.hom _)`
— the recorded I-0232(b)/I-0238(a)/(d) discipline; no structural `rw` into the product
spellings.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra

/-! ## The evaluation crux -/

section Crux

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  (L : Type u) [Field L] [Algebra k L]

/-- **The evaluation crux** (worksheet §1.5 step 3): reading a base-changed section
`Over.sectionsBaseChange G` at the base-changed point of `p` is `tensorPointEval` of
the `k`-valued evaluation at `p`.  Proved on pure tensors through the two projection
triangles of `rationalPointBaseChange` and `ΓSpecIso`-naturality; every `appLE`
transport is an equation-`have` (the I-0232(b)/I-0238(d) discipline). -/
private lemma gammaSpecIso_appLE_sectionsBaseChange (p : Spec (.of k) ⟶ C.left)
    (hp : p ≫ C.hom = 𝟙 (Spec (.of k))) {U : C.left.Opens} (hU : IsAffineOpen U)
    (hple : ⊤ ≤ p ⁻¹ᵁ U)
    (hqle : ⊤ ≤ Over.rationalPointBaseChange C L p hp ⁻¹ᵁ
      ((fst C (overSpec k L)).left ⁻¹ᵁ U))
    (G : Γ(C.left, U) ⊗[k] L) :
    (Scheme.ΓSpecIso (.of L)).hom
        ((Over.rationalPointBaseChange C L p hp).appLE
          ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle
          (Over.sectionsBaseChange C L hU.isCompact hU.isQuasiSeparated G)) =
      tensorPointEval (Over.rationalPointEval C p hp hple) G := by
  induction G with
  | zero =>
    calc (Scheme.ΓSpecIso (.of L)).hom
          ((Over.rationalPointBaseChange C L p hp).appLE
            ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle
            (Over.sectionsBaseChange C L hU.isCompact hU.isQuasiSeparated 0))
        = (Scheme.ΓSpecIso (.of L)).hom
            ((Over.rationalPointBaseChange C L p hp).appLE
              ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle 0) :=
          congrArg (fun t => (Scheme.ΓSpecIso (.of L)).hom
            ((Over.rationalPointBaseChange C L p hp).appLE
              ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle t)) (map_zero _)
      _ = (Scheme.ΓSpecIso (.of L)).hom 0 :=
          congrArg (Scheme.ΓSpecIso (.of L)).hom (map_zero _)
      _ = 0 := map_zero _
      _ = tensorPointEval (Over.rationalPointEval C p hp hple) 0 := (map_zero _).symm
  | add x y hx hy =>
    calc (Scheme.ΓSpecIso (.of L)).hom
          ((Over.rationalPointBaseChange C L p hp).appLE
            ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle
            (Over.sectionsBaseChange C L hU.isCompact hU.isQuasiSeparated (x + y)))
        = (Scheme.ΓSpecIso (.of L)).hom
            ((Over.rationalPointBaseChange C L p hp).appLE
              ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle
              (Over.sectionsBaseChange C L hU.isCompact hU.isQuasiSeparated x +
                Over.sectionsBaseChange C L hU.isCompact hU.isQuasiSeparated y)) :=
          congrArg (fun t => (Scheme.ΓSpecIso (.of L)).hom
            ((Over.rationalPointBaseChange C L p hp).appLE
              ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle t)) (map_add _ _ _)
      _ = (Scheme.ΓSpecIso (.of L)).hom
            ((Over.rationalPointBaseChange C L p hp).appLE
              ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle
              (Over.sectionsBaseChange C L hU.isCompact hU.isQuasiSeparated x) +
            (Over.rationalPointBaseChange C L p hp).appLE
              ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle
              (Over.sectionsBaseChange C L hU.isCompact hU.isQuasiSeparated y)) :=
          congrArg (Scheme.ΓSpecIso (.of L)).hom (map_add _ _ _)
      _ = tensorPointEval (Over.rationalPointEval C p hp hple) x +
            tensorPointEval (Over.rationalPointEval C p hp hple) y := by
          rw [map_add, hx, hy]
      _ = tensorPointEval (Over.rationalPointEval C p hp hple) (x + y) :=
          (map_add _ _ _).symm
  | tmul s c =>
    -- leg 1: the first-projection pullback evaluates through `p`
    have hcle : (⊤ : (Spec (.of L)).Opens) ≤
        (Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ p) ⁻¹ᵁ U :=
      fun y _ => hple trivial
    have h1 : (fst C (overSpec k L)).left.appLE U
          ((fst C (overSpec k L)).left ⁻¹ᵁ U) le_rfl ≫
        (Over.rationalPointBaseChange C L p hp).appLE
          ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle =
        (Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ p).appLE U ⊤ hcle := by
      rw [Scheme.Hom.appLE_comp_appLE]
      exact Scheme.Hom.appLE_congr_hom_kit (Over.rationalPointBaseChange_fst C L p hp) _
    have h2 : p.appLE U ⊤ hple ≫
        (Spec.map (CommRingCat.ofHom (algebraMap k L))).appLE ⊤ ⊤
          (Scheme.Hom.preimage_top (Spec.map (CommRingCat.ofHom (algebraMap k L)))).ge =
        (Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ p).appLE U ⊤ hcle := by
      rw [Scheme.Hom.appLE_comp_appLE]
    have e1a : (Over.rationalPointBaseChange C L p hp).appLE
          ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle
          ((fst C (overSpec k L)).left.appLE U
            ((fst C (overSpec k L)).left ⁻¹ᵁ U) le_rfl s) =
        (Spec.map (CommRingCat.ofHom (algebraMap k L))).appLE ⊤ ⊤
          (Scheme.Hom.preimage_top (Spec.map (CommRingCat.ofHom (algebraMap k L)))).ge
          (p.appLE U ⊤ hple s) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (h1.trans h2.symm)) s
    have hnat0 : (Spec.map (CommRingCat.ofHom (algebraMap k L))).appLE ⊤ ⊤
          (Scheme.Hom.preimage_top (Spec.map (CommRingCat.ofHom (algebraMap k L)))).ge ≫
        (Scheme.ΓSpecIso (.of L)).hom =
        (Scheme.ΓSpecIso (.of k)).hom ≫ CommRingCat.ofHom (algebraMap k L) := by
      have happTop : (Spec.map (CommRingCat.ofHom (algebraMap k L))).appLE ⊤ ⊤
          (Scheme.Hom.preimage_top (Spec.map (CommRingCat.ofHom (algebraMap k L)))).ge =
          (Spec.map (CommRingCat.ofHom (algebraMap k L))).appTop :=
        Scheme.Hom.appLE_eq_app _
      rw [happTop]
      exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k L))
    have hnat : (Scheme.ΓSpecIso (.of L)).hom
        ((Spec.map (CommRingCat.ofHom (algebraMap k L))).appLE ⊤ ⊤
          (Scheme.Hom.preimage_top (Spec.map (CommRingCat.ofHom (algebraMap k L)))).ge
          (p.appLE U ⊤ hple s)) =
        algebraMap k L ((Scheme.ΓSpecIso (.of k)).hom (p.appLE U ⊤ hple s)) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hnat0) _
    have e1 : (Scheme.ΓSpecIso (.of L)).hom
        ((Over.rationalPointBaseChange C L p hp).appLE
          ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle
          ((fst C (overSpec k L)).left.appLE U
            ((fst C (overSpec k L)).left ⁻¹ᵁ U) le_rfl s)) =
        algebraMap k L (Over.rationalPointEval C p hp hple s) := by
      rw [e1a]
      exact hnat
    -- leg 2: the second-projection pullback is the identity of `Spec L`
    have h3 : (snd C (overSpec k L)).left.appLE ⊤
          ((fst C (overSpec k L)).left ⁻¹ᵁ U)
          (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k L)).left).ge) ≫
        (Over.rationalPointBaseChange C L p hp).appLE
          ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle =
        Scheme.Hom.appLE (𝟙 (Spec (.of L))) ⊤ ⊤
          (Scheme.Hom.preimage_top (𝟙 (Spec (.of L)))).ge := by
      rw [Scheme.Hom.appLE_comp_appLE]
      exact Scheme.Hom.appLE_congr_hom_kit (Over.rationalPointBaseChange_snd C L p hp) _
    have e3a : (Over.rationalPointBaseChange C L p hp).appLE
          ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle
          ((snd C (overSpec k L)).left.appLE ⊤
            ((fst C (overSpec k L)).left ⁻¹ᵁ U)
            (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k L)).left).ge)
            ((Scheme.ΓSpecIso (.of L)).inv c)) =
        Scheme.Hom.appLE (𝟙 (Spec (.of L))) ⊤ ⊤
          (Scheme.Hom.preimage_top (𝟙 (Spec (.of L)))).ge
          ((Scheme.ΓSpecIso (.of L)).inv c) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h3) _
    have e3 : (Scheme.ΓSpecIso (.of L)).hom
        ((Over.rationalPointBaseChange C L p hp).appLE
          ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle
          ((snd C (overSpec k L)).left.appLE ⊤
            ((fst C (overSpec k L)).left ⁻¹ᵁ U)
            (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k L)).left).ge)
            ((Scheme.ΓSpecIso (.of L)).inv c))) = c := by
      rw [e3a, Scheme.id_appLE_apply]
      exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
        (Scheme.ΓSpecIso (.of L)).inv_hom_id) c
    -- assemble the pure-tensor case
    have htmul0 : Over.sectionsBaseChange C L hU.isCompact hU.isQuasiSeparated
        (s ⊗ₜ c) =
        (fst C (overSpec k L)).left.appLE U
            ((fst C (overSpec k L)).left ⁻¹ᵁ U) le_rfl s *
          (snd C (overSpec k L)).left.appLE ⊤
            ((fst C (overSpec k L)).left ⁻¹ᵁ U)
            (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k L)).left).ge)
            ((Scheme.ΓSpecIso (.of L)).inv c) :=
      (Over.sectionsBaseChange_tmul C L hU.isCompact hU.isQuasiSeparated s c).trans
        (congrArg (fun t => (fst C (overSpec k L)).left.appLE U
          ((fst C (overSpec k L)).left ⁻¹ᵁ U) le_rfl s * t)
          (CommRingCat.comp_apply _ _ _))
    calc (Scheme.ΓSpecIso (.of L)).hom
          ((Over.rationalPointBaseChange C L p hp).appLE
            ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle
            (Over.sectionsBaseChange C L hU.isCompact hU.isQuasiSeparated (s ⊗ₜ c)))
        = (Scheme.ΓSpecIso (.of L)).hom
            ((Over.rationalPointBaseChange C L p hp).appLE
              ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle
              ((fst C (overSpec k L)).left.appLE U
                  ((fst C (overSpec k L)).left ⁻¹ᵁ U) le_rfl s *
                (snd C (overSpec k L)).left.appLE ⊤
                  ((fst C (overSpec k L)).left ⁻¹ᵁ U)
                  (le_top.trans
                    (Scheme.Hom.preimage_top (snd C (overSpec k L)).left).ge)
                  ((Scheme.ΓSpecIso (.of L)).inv c))) :=
          congrArg (fun t => (Scheme.ΓSpecIso (.of L)).hom
            ((Over.rationalPointBaseChange C L p hp).appLE
              ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle t)) htmul0
      _ = (Scheme.ΓSpecIso (.of L)).hom
            ((Over.rationalPointBaseChange C L p hp).appLE
              ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle
              ((fst C (overSpec k L)).left.appLE U
                ((fst C (overSpec k L)).left ⁻¹ᵁ U) le_rfl s) *
            (Over.rationalPointBaseChange C L p hp).appLE
              ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle
              ((snd C (overSpec k L)).left.appLE ⊤
                ((fst C (overSpec k L)).left ⁻¹ᵁ U)
                (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k L)).left).ge)
                ((Scheme.ΓSpecIso (.of L)).inv c))) :=
          congrArg (Scheme.ΓSpecIso (.of L)).hom (map_mul _ _ _)
      _ = (Scheme.ΓSpecIso (.of L)).hom
            ((Over.rationalPointBaseChange C L p hp).appLE
              ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle
              ((fst C (overSpec k L)).left.appLE U
                ((fst C (overSpec k L)).left ⁻¹ᵁ U) le_rfl s)) *
          (Scheme.ΓSpecIso (.of L)).hom
            ((Over.rationalPointBaseChange C L p hp).appLE
              ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle
              ((snd C (overSpec k L)).left.appLE ⊤
                ((fst C (overSpec k L)).left ⁻¹ᵁ U)
                (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k L)).left).ge)
                ((Scheme.ΓSpecIso (.of L)).inv c))) := map_mul _ _ _
      _ = algebraMap k L (Over.rationalPointEval C p hp hple s) * c := by
          rw [e1, e3]
      _ = tensorPointEval (Over.rationalPointEval C p hp hple) (s ⊗ₜ c) := by
          rw [tensorPointEval_tmul, Algebra.smul_def]

end Crux

/-! ## The density keystone -/

section Density

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  (L : Type u) [Field L] [Algebra k L]

/-- **COV-3, density of base-changed rational points** (★ B-2 keystone, worksheet
§1.5): over a separably closed base field `k`, for every field `L ⊇ k` and every
nonempty open `W` of the relative curve `C_L = relCurve C L`, some `k`-rational point
of `C` base-changes into `W`.

Route: pick an affine chart `U` of `C.left` under a point of `W`; its preimage chart of
`C_L` is affine with sections `Γ(U) ⊗_k L` (`Over.sectionsBaseChange`); a basic open
`D(f) ⊆ W` of the chart has a nonzero coordinate `a` in an `L`-basis
(`exists_algHom_tensorPointEval_ne_zero`); `D(a)` is nonempty in the reduced curve, and
DAT-P (`Over.exists_rationalPoint_mem`) supplies a rational point there whose base
change evaluates `f` to a nonzero element of `L`
(`gammaSpecIso_appLE_sectionsBaseChange`), hence lies in `D(f) ⊆ W`. -/
theorem Over.dense_baseChange_rationalPoints [IsSepClosed k]
    [SmoothOfRelativeDimension 1 C.hom] [IsIntegral C.left]
    (W : (relCurve C L).Opens) (hW : (W : Set (relCurve C L)).Nonempty) :
    ∃ (p : Spec (.of k) ⟶ C.left) (hp : p ≫ C.hom = 𝟙 (Spec (.of k))),
      (Over.rationalPointBaseChange C L p hp).base (IsLocalRing.closedPoint L) ∈ W := by
  classical
  obtain ⟨z, hzW⟩ := hW
  -- an affine chart of `C.left` under `z`, and its affine preimage chart of `C_L`
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := C.left) (U := ⊤) (x := (fst C (overSpec k L)).left.base z) trivial
  haveI : IsAffineHom (fst C (overSpec k L)).left :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (Over.isPullback_left C (overSpec k L)).flip
      (isAffineHom_of_isAffine (overSpec k L).hom)
  have hV : IsAffineOpen ((fst C (overSpec k L)).left ⁻¹ᵁ U) :=
    hU.preimage (fst C (overSpec k L)).left
  have hzV : z ∈ (fst C (overSpec k L)).left ⁻¹ᵁ U := hxU
  -- a basic open of the chart inside `W` around `z`
  obtain ⟨f, hfW, hzf⟩ := hV.exists_basicOpen_le
    (V := W ⊓ ((fst C (overSpec k L)).left ⁻¹ᵁ U)) ⟨z, ⟨hzW, hzV⟩⟩ hzV
  -- its tensor coordinates: `f` is nonzero, hence has a nonzero coordinate
  have hf0 : f ≠ 0 := by
    intro h0
    rw [h0, Scheme.basicOpen_zero] at hzf
    exact hzf
  have hF0 : (Over.sectionsBaseChange C L hU.isCompact hU.isQuasiSeparated).symm f
      ≠ 0 := fun h0 => hf0 (by
    rw [← (Over.sectionsBaseChange C L hU.isCompact hU.isQuasiSeparated).apply_symm_apply
      f, h0, map_zero])
  obtain ⟨a, ha0, hkey⟩ := exists_algHom_tensorPointEval_ne_zero hF0
  -- the coordinate's basic open is nonempty in the reduced curve; DAT-P fires there
  have hane : (C.left.basicOpen a : Set C.left).Nonempty := by
    by_contra h
    rw [TopologicalSpace.Opens.not_nonempty_iff_eq_bot, basicOpen_eq_bot_iff] at h
    exact ha0 h
  obtain ⟨p, hp, hpmem⟩ := Over.exists_rationalPoint_mem C (C.left.basicOpen a) hane
  have hple : ⊤ ≤ p ⁻¹ᵁ U :=
    top_le_preimage_of_closedPoint_mem p ((C.left.basicOpen_le a) hpmem)
  -- the base-changed point lies in the chart …
  have hqle : ⊤ ≤ Over.rationalPointBaseChange C L p hp ⁻¹ᵁ
      ((fst C (overSpec k L)).left ⁻¹ᵁ U) := by
    intro y _
    change (fst C (overSpec k L)).left.base
      ((Over.rationalPointBaseChange C L p hp).base y) ∈ U
    have hbase : (fst C (overSpec k L)).left.base
        ((Over.rationalPointBaseChange C L p hp).base y) =
        p.base ((Spec.map (CommRingCat.ofHom (algebraMap k L))).base y) :=
      congr(($(Over.rationalPointBaseChange_fst C L p hp)).base y)
    refine Set.mem_of_eq_of_mem hbase ?_
    have hy : (Spec.map (CommRingCat.ofHom (algebraMap k L))).base y =
        IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [hy]
    exact (C.left.basicOpen_le a) hpmem
  -- … and evaluates `f` to a nonzero element of `L`
  have hval := gammaSpecIso_appLE_sectionsBaseChange C L p hp hU hple hqle
    ((Over.sectionsBaseChange C L hU.isCompact hU.isQuasiSeparated).symm f)
  rw [(Over.sectionsBaseChange C L hU.isCompact hU.isQuasiSeparated).apply_symm_apply f]
    at hval
  have hne0 : (Over.rationalPointBaseChange C L p hp).appLE
      ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle f ≠ 0 := by
    intro h0
    exact hkey (Over.rationalPointEval C p hp hple)
      (Over.rationalPointEval_ne_zero_of_mem_basicOpen C p hp hple hpmem)
      (hval.symm.trans (by rw [h0, map_zero]))
  -- membership in the basic open upstairs, via the one-point space `Spec L`
  have hmemL : IsLocalRing.closedPoint L ∈ (Spec (.of L)).basicOpen
      ((Over.rationalPointBaseChange C L p hp).appLE
        ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle f) := by
    have hnonempty : ((Spec (.of L)).basicOpen
        ((Over.rationalPointBaseChange C L p hp).appLE
          ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle f) : Set (Spec (.of L))).Nonempty := by
      by_contra h
      rw [TopologicalSpace.Opens.not_nonempty_iff_eq_bot, basicOpen_eq_bot_iff] at h
      exact hne0 h
    obtain ⟨y, hy⟩ := hnonempty
    have hy' : y = (IsLocalRing.closedPoint L) := Subsingleton.elim _ _
    rwa [hy'] at hy
  -- transport down to the basic open of the chart, then into `W`
  have hmem2 : IsLocalRing.closedPoint L ∈
      Over.rationalPointBaseChange C L p hp ⁻¹ᵁ
        (C ⊗ overSpec k L).left.basicOpen f := by
    have heq : (Spec (.of L)).basicOpen
        ((Over.rationalPointBaseChange C L p hp).appLE
          ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle f) =
        ⊤ ⊓ (Spec (.of L)).basicOpen
          ((Over.rationalPointBaseChange C L p hp).app
            ((fst C (overSpec k L)).left ⁻¹ᵁ U) f) := by
      have h : (Over.rationalPointBaseChange C L p hp).appLE
          ((fst C (overSpec k L)).left ⁻¹ᵁ U) ⊤ hqle f =
          (Spec (.of L)).presheaf.map (homOfLE hqle).op
            ((Over.rationalPointBaseChange C L p hp).app
              ((fst C (overSpec k L)).left ⁻¹ᵁ U) f) := rfl
      rw [h, Scheme.basicOpen_res]
    rw [heq] at hmemL
    rw [Scheme.preimage_basicOpen]
    exact hmemL.2
  exact ⟨p, hp, (hfW hmem2).1⟩

end Density

end AlgebraicGeometry
