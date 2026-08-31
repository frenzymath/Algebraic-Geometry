/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafDatum

/-!
# Base change of the pinned cocycle datum (DAT-1, stage 1d-ii, the datum half)

The `relCocycleBaseChange`-style base change of the basic-open cocycle datum
(`informal/spec-dat-1.md` stage (1d-ii), first bullet; worksheet §3.2 — **this is the
RE-5 transport interface**): along a `k`-algebra map `B → B'`, the generators, partition
coefficients and transition units of a `Scheme.BasicOpenCocycleDatum C B π` push forward
through the relative-curve comparison morphism `relCurveMap C B B'` to a datum over `B'`,
with the pieces mapping to pieces (`Scheme.preimage_basicOpen`) and the partition/cocycle
identities carried by `map_*`.

* `AlgebraicGeometry.Scheme.Hom.appLE_resHom` — `appLE` commutes with restriction on
  both sides (the workhorse; both sides collapse to one `appLE` by
  `appLE_map`/`map_appLE` and proof irrelevance).
* `relSectionsMap_basicOpen` — basic opens of compared sections are preimages of basic
  opens.
* `relCurveMap_appLE_overAlgebraMap` — the comparison intertwines the structure algebra
  maps along `algebraMap B B'`, over **arbitrary** opens (the pullback-open case is the
  landed `relSectionsMap_overAlgebraMap`).
* `BasicOpenCoverData.baseChange` / `BasicOpenCocycleDatum.baseChange` — the datum base
  change, with `pieces_baseChange` (pieces map to pieces).
* `BasicOpenCocycleDatum.sectionsMap` — the componentwise comparison of glued sections
  `F_D(W) → F_{D'}(W')` for `W' ≤ relCurveMap ⁻¹ᵁ W`, additive
  (`sectionsMap_add`), semilinear along `algebraMap B B'` (`sectionsMap_smul`),
  commuting with restriction (`gluedRes_sectionsMap`), intertwining the piece
  trivializations with the section comparison (`gluedTriv_sectionsMap`) and the
  componentwise chart actions (`sectionsMap_gluedQsmul`) — the inputs of the stage
  (1d-ii) term identifications and the RE-5 transport.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C B, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k B).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite

namespace AlgebraicGeometry

/-! ## `appLE` against restriction, on arbitrary opens -/

/-- **`appLE` commutes with restriction**: for `f : X ⟶ Y`, restricting the `appLE`
image of a section equals the `appLE` image of the restricted section. Both sides are
`f.appLE W PW'` of the section, by `appLE_map`/`map_appLE` and proof irrelevance of the
inclusion witnesses. -/
lemma Scheme.Hom.appLE_resHom {X Y : Scheme.{u}} (f : X.Hom Y) {W' W : Y.Opens}
    {PW' PW : X.Opens} (hW : W' ≤ W) (ePW : PW ≤ f ⁻¹ᵁ W) (ePW' : PW' ≤ f ⁻¹ᵁ W')
    (hP : PW' ≤ PW) (s : Γ(Y, W)) :
    X.resHom hP ((f.appLE W PW ePW).hom s) =
      (f.appLE W' PW' ePW').hom (Y.resHom hW s) := by
  have h1 := congr((CommRingCat.Hom.hom
    $(Scheme.Hom.appLE_map f ePW (homOfLE hP).op)) s)
  have h2 := congr((CommRingCat.Hom.hom
    $(Scheme.Hom.map_appLE f ePW' (homOfLE hW).op)) s)
  exact h1.trans h2.symm

section BasicOpen

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (B : Type u) [CommRing B] [Algebra k B]
variable (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B'] [IsScalarTower k B B']

/-! ## Basic opens of compared sections -/

/-- **Basic opens base-change to basic opens**: the basic open of the compared section
`relSectionsMap s` is the `relCurveMap`-preimage of the basic open of `s`. -/
theorem relSectionsMap_basicOpen (V : C.left.Opens)
    (s : Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)) :
    (relCurve C B').basicOpen (relSectionsMap C B B' V s) =
      relCurveMap C B B' ⁻¹ᵁ ((relCurve C B).basicOpen s) := by
  have happ : relSectionsMap C B B' V s =
      (relCurve C B').resHom
        (le_of_eq (relCurveMap_preimage C B B' V).symm :
          (fst C (overSpec k B')).left ⁻¹ᵁ V ≤
            relCurveMap C B B' ⁻¹ᵁ ((fst C (overSpec k B)).left ⁻¹ᵁ V))
        (((relCurveMap C B B').app ((fst C (overSpec k B)).left ⁻¹ᵁ V)).hom s) := by
    have h := congr((CommRingCat.Hom.hom
      $(Scheme.Hom.appLE_map (relCurveMap C B B')
        (le_refl (relCurveMap C B B' ⁻¹ᵁ ((fst C (overSpec k B)).left ⁻¹ᵁ V)))
        (homOfLE (le_of_eq (relCurveMap_preimage C B B' V).symm)).op)) s)
    have h0 : ((relCurveMap C B B').appLE ((fst C (overSpec k B)).left ⁻¹ᵁ V)
        (relCurveMap C B B' ⁻¹ᵁ ((fst C (overSpec k B)).left ⁻¹ᵁ V)) le_rfl).hom s =
        (((relCurveMap C B B').app ((fst C (overSpec k B)).left ⁻¹ᵁ V)).hom s) :=
      congr((CommRingCat.Hom.hom
        $(Scheme.Hom.appLE_eq_app (relCurveMap C B B')
          (U := (fst C (overSpec k B)).left ⁻¹ᵁ V))) s)
    calc relSectionsMap C B B' V s
        = ((relCurveMap C B B').appLE ((fst C (overSpec k B)).left ⁻¹ᵁ V)
            ((fst C (overSpec k B')).left ⁻¹ᵁ V)
            (le_of_eq (relCurveMap_preimage C B B' V).symm)).hom s := rfl
      _ = (relCurve C B').resHom (le_of_eq (relCurveMap_preimage C B B' V).symm)
            (((relCurveMap C B B').appLE ((fst C (overSpec k B)).left ⁻¹ᵁ V)
              (relCurveMap C B B' ⁻¹ᵁ ((fst C (overSpec k B)).left ⁻¹ᵁ V))
              le_rfl).hom s) := h.symm
      _ = _ := by rw [h0]
  rw [happ, Scheme.basicOpen_resHom,
    ← Scheme.preimage_basicOpen (relCurveMap C B B') s,
    ← relCurveMap_preimage C B B' V, ← Scheme.Hom.preimage_inf]
  congr 1
  exact inf_eq_right.mpr ((relCurve C B).basicOpen_le s)

/-! ## The comparison intertwines the structure algebra maps (arbitrary opens) -/

/-- `appLE` is invariant under an equality of morphisms. -/
private lemma appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) {U : Y.Opens}
    {W : X.Opens} (e : W ≤ f ⁻¹ᵁ U) :
    f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h; rfl

attribute [local instance] Scheme.overModule

/-- **The comparison intertwines the structure actions, on arbitrary opens**: the
`appLE` image of the structure pullback of `r : B` is the structure pullback of
`algebraMap B B' r` (the landed `relSectionsMap_overAlgebraMap` is the pullback-open
case `W = V_B`). -/
theorem relCurveMap_appLE_overAlgebraMap {W : (relCurve C B).Opens}
    {W' : (relCurve C B').Opens} (hle : W' ≤ relCurveMap C B B' ⁻¹ᵁ W) (r : B) :
    ((relCurveMap C B B').appLE W W' hle).hom
        ((relCurve C B).overAlgebraMap B W r) =
      (relCurve C B').overAlgebraMap B' W' (algebraMap B B' r) := by
  have hmor : ((Scheme.ΓSpecIso (.of B)).inv ≫
        (snd C (overSpec k B)).left.appLE ⊤ W
          (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k B)).left).ge)) ≫
      (relCurveMap C B B').appLE W W' hle =
      CommRingCat.ofHom (algebraMap B B') ≫ (Scheme.ΓSpecIso (.of B')).inv ≫
        (snd C (overSpec k B')).left.appLE ⊤ W'
          (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k B')).left).ge) := by
    have hnat : (Scheme.ΓSpecIso (.of B)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap B B'))).appTop =
        CommRingCat.ofHom (algebraMap B B') ≫ (Scheme.ΓSpecIso (.of B')).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc,
        ← Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap B B')),
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hsplit : ((snd C (overSpec k B')).left ≫
          Spec.map (CommRingCat.ofHom (algebraMap B B'))).appLE ⊤ W'
          ((relCurveMap_snd C B B') ▸
            hle.trans (Scheme.Hom.preimage_mono _ (le_top.trans
              (Scheme.Hom.preimage_top (snd C (overSpec k B)).left).ge))) =
        (Spec.map (CommRingCat.ofHom (algebraMap B B'))).appLE ⊤ ⊤
            (Scheme.Hom.preimage_top _).ge ≫
          (snd C (overSpec k B')).left.appLE ⊤ W'
            (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k B')).left).ge) :=
      (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    have happ : (Spec.map (CommRingCat.ofHom (algebraMap B B'))).appLE ⊤ ⊤
        (Scheme.Hom.preimage_top _).ge =
        (Spec.map (CommRingCat.ofHom (algebraMap B B'))).appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [Category.assoc, Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom (relCurveMap_snd C B B'), hsplit, happ, ← Category.assoc,
      hnat, Category.assoc]
  have hoam : (relCurve C B).overAlgebraMap B W r =
      ((Scheme.ΓSpecIso (.of B)).inv ≫
        (snd C (overSpec k B)).left.appLE ⊤ W
          (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k B)).left).ge)).hom
        r := rfl
  have hoam' : (relCurve C B').overAlgebraMap B' W' (algebraMap B B' r) =
      ((Scheme.ΓSpecIso (.of B')).inv ≫
        (snd C (overSpec k B')).left.appLE ⊤ W'
          (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k B')).left).ge)).hom
        (algebraMap B B' r) := rfl
  rw [hoam, hoam']
  exact congr((CommRingCat.Hom.hom $hmor) r)

end BasicOpen

/-! ## Base change of the datum -/

section Datum

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B'] [IsScalarTower k B B']
variable {π : C.left ⟶ P1 k} [IsAffineHom π]

attribute [local instance] Scheme.overModule

namespace BasicOpenCoverData

variable (D : BasicOpenCoverData C B π)

/-- **Base change of the basic-open cover data** along `B → B'`: the generators and
partition coefficients push forward through the sections comparison map; the partition
witnesses are carried by `map_sum`/`map_mul`/`map_one`. -/
noncomputable def baseChange : BasicOpenCoverData C B' π where
  J₀ := D.J₀
  J₁ := D.J₁
  fintype₀ := D.fintype₀
  fintype₁ := D.fintype₁
  h₀ j := relSectionsMap C B B' (fiberChart₀ π) (D.h₀ j)
  h₁ j := relSectionsMap C B B' (fiberChart₁ π) (D.h₁ j)
  a₀ j := relSectionsMap C B B' (fiberChart₀ π) (D.a₀ j)
  a₁ j := relSectionsMap C B B' (fiberChart₁ π) (D.a₁ j)
  partition₀ := by
    have h := congrArg (relSectionsMap C B B' (fiberChart₀ π)) D.partition₀
    rw [map_sum, map_one] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => (map_mul _ _ _).symm
  partition₁ := by
    have h := congrArg (relSectionsMap C B B' (fiberChart₁ π)) D.partition₁
    rw [map_sum, map_one] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => (map_mul _ _ _).symm

@[simp]
lemma baseChange_h₀ (j : D.J₀) :
    (D.baseChange B').h₀ j = relSectionsMap C B B' (fiberChart₀ π) (D.h₀ j) := rfl

@[simp]
lemma baseChange_h₁ (j : D.J₁) :
    (D.baseChange B').h₁ j = relSectionsMap C B B' (fiberChart₁ π) (D.h₁ j) := rfl

/-- **Pieces base-change to pieces**: the pieces of the base-changed cover data are the
`relCurveMap`-preimages of the pieces. -/
theorem pieces_baseChange (j : D.index) :
    (D.baseChange B').pieces j = relCurveMap C B B' ⁻¹ᵁ D.pieces j := by
  cases j with
  | inl j => exact relSectionsMap_basicOpen C B B' (fiberChart₀ π) (D.h₀ j)
  | inr j => exact relSectionsMap_basicOpen C B B' (fiberChart₁ π) (D.h₁ j)

/-- The base-changed pieces are below the preimages of the pieces (the `≤`-form of
`pieces_baseChange` consumed by `appLE`). -/
lemma baseChange_pieces_le_preimage (j : D.index) :
    (D.baseChange B').pieces j ≤ relCurveMap C B B' ⁻¹ᵁ D.pieces j :=
  (D.pieces_baseChange B' j).le

/-- Double overlaps of base-changed pieces are below the preimages of the double
overlaps. -/
lemma baseChange_inf_le_preimage (i j : D.index) :
    (D.baseChange B').pieces i ⊓ (D.baseChange B').pieces j ≤
      relCurveMap C B B' ⁻¹ᵁ (D.pieces i ⊓ D.pieces j) := by
  rw [Scheme.Hom.preimage_inf]
  exact inf_le_inf (D.baseChange_pieces_le_preimage B' i)
    (D.baseChange_pieces_le_preimage B' j)

/-- **The overlap comparison map**: sections on a double overlap of pieces compare to
sections on the double overlap of the base-changed pieces, through `appLE` of the
relative-curve comparison. -/
noncomputable def overlapMap (i j : D.index) :
    Γ(relCurve C B, D.pieces i ⊓ D.pieces j) →+*
      Γ(relCurve C B', (D.baseChange B').pieces i ⊓ (D.baseChange B').pieces j) :=
  ((relCurveMap C B B').appLE (D.pieces i ⊓ D.pieces j)
    ((D.baseChange B').pieces i ⊓ (D.baseChange B').pieces j)
    (D.baseChange_inf_le_preimage B' i j)).hom

end BasicOpenCoverData

namespace BasicOpenCocycleDatum

variable (D : BasicOpenCocycleDatum C B π)

/-- **Base change of the pinned cocycle datum** along `B → B'` (stage (1d-ii), the
datum half; the RE-5 descent/transport interface): generators, partition coefficients
and transition units push forward through the relative-curve comparison; the cocycle
identities are carried by ring-hom functoriality (`Scheme.Hom.appLE_resHom`). -/
noncomputable def baseChange : BasicOpenCocycleDatum C B' π where
  toBasicOpenCoverData := D.toBasicOpenCoverData.baseChange B'
  unit i j := Units.map (D.toBasicOpenCoverData.overlapMap B' i j).toMonoidHom
    (D.unit i j)
  isGluingCocycle := by
    constructor
    · intro i
      have h := D.isGluingCocycle.unit_self i
      change (D.toBasicOpenCoverData.overlapMap B' i i)
        ((D.unit i i : Γ(relCurve C B, D.pieces i ⊓ D.pieces i))) = 1
      rw [h, map_one]
    · intro i j l
      -- the triple overlap of the base-changed pieces sits below the preimage of the
      -- triple overlap
      have htriple : (D.toBasicOpenCoverData.baseChange B').pieces i ⊓
            (D.toBasicOpenCoverData.baseChange B').pieces j ⊓
            (D.toBasicOpenCoverData.baseChange B').pieces l ≤
          relCurveMap C B B' ⁻¹ᵁ (D.pieces i ⊓ D.pieces j ⊓ D.pieces l) := by
        rw [Scheme.Hom.preimage_inf]
        exact inf_le_inf (D.toBasicOpenCoverData.baseChange_inf_le_preimage B' i j)
          (D.toBasicOpenCoverData.baseChange_pieces_le_preimage B' l)
      have key := congrArg
        (((relCurveMap C B B').appLE (D.pieces i ⊓ D.pieces j ⊓ D.pieces l)
          ((D.toBasicOpenCoverData.baseChange B').pieces i ⊓
            (D.toBasicOpenCoverData.baseChange B').pieces j ⊓
            (D.toBasicOpenCoverData.baseChange B').pieces l) htriple).hom)
        (D.isGluingCocycle.mul_res i j l)
      rw [map_mul] at key
      have e₁ := (relCurveMap C B B').appLE_resHom
        (inf_le_left : D.pieces i ⊓ D.pieces j ⊓ D.pieces l ≤ D.pieces i ⊓ D.pieces j)
        (D.toBasicOpenCoverData.baseChange_inf_le_preimage B' i j) htriple
        (inf_le_left : (D.toBasicOpenCoverData.baseChange B').pieces i ⊓
          (D.toBasicOpenCoverData.baseChange B').pieces j ⊓
          (D.toBasicOpenCoverData.baseChange B').pieces l ≤
          (D.toBasicOpenCoverData.baseChange B').pieces i ⊓
            (D.toBasicOpenCoverData.baseChange B').pieces j)
        ((D.unit i j : Γ(relCurve C B, D.pieces i ⊓ D.pieces j)))
      have e₂ := (relCurveMap C B B').appLE_resHom
        (gluedInclCoc D.pieces (D.pieces i) j l)
        (D.toBasicOpenCoverData.baseChange_inf_le_preimage B' j l) htriple
        (gluedInclCoc (D.toBasicOpenCoverData.baseChange B').pieces
          ((D.toBasicOpenCoverData.baseChange B').pieces i) j l)
        ((D.unit j l : Γ(relCurve C B, D.pieces j ⊓ D.pieces l)))
      have e₃ := (relCurveMap C B B').appLE_resHom
        (gluedInclSnd D.pieces (D.pieces i) j l)
        (D.toBasicOpenCoverData.baseChange_inf_le_preimage B' i l) htriple
        (gluedInclSnd (D.toBasicOpenCoverData.baseChange B').pieces
          ((D.toBasicOpenCoverData.baseChange B').pieces i) j l)
        ((D.unit i l : Γ(relCurve C B, D.pieces i ⊓ D.pieces l)))
      rw [← e₁, ← e₂, ← e₃] at key
      simp only [Units.coe_map]
      exact key

@[simp]
lemma baseChange_unit_coe (i j : D.index) :
    (((D.baseChange B').unit i j :
        Γ(relCurve C B',
          (D.baseChange B').pieces i ⊓ (D.baseChange B').pieces j)ˣ) :
      Γ(relCurve C B', (D.baseChange B').pieces i ⊓ (D.baseChange B').pieces j)) =
      D.toBasicOpenCoverData.overlapMap B' i j
        ((D.unit i j : Γ(relCurve C B, D.pieces i ⊓ D.pieces j))) := rfl

/-! ## The componentwise comparison of glued sections -/

section SectionsMap

variable {W : (relCurve C B).Opens} {W' : (relCurve C B').Opens}

/-- The component opens of the comparison sit below the preimages of the component
opens. -/
lemma sectionsMap_component_le (hW' : W' ≤ relCurveMap C B B' ⁻¹ᵁ W) (j : D.index) :
    W' ⊓ (D.baseChange B').pieces j ≤ relCurveMap C B B' ⁻¹ᵁ (W ⊓ D.pieces j) := by
  rw [Scheme.Hom.preimage_inf]
  exact inf_le_inf hW' (D.toBasicOpenCoverData.baseChange_pieces_le_preimage B' j)

/-- **The componentwise comparison of glued sections** along `B → B'`: apply `appLE` of
the relative-curve comparison to every component. Matching is carried by
`Scheme.Hom.appLE_resHom` and the base-changed units. -/
noncomputable def sectionsMap (hW' : W' ≤ relCurveMap C B B' ⁻¹ᵁ W)
    (s : ↥(gluedSubmodule B D.pieces D.unit W)) :
    ↥(gluedSubmodule B' (D.baseChange B').pieces (D.baseChange B').unit W') := by
  refine ⟨fun j => ((relCurveMap C B B').appLE (W ⊓ D.pieces j)
    (W' ⊓ (D.baseChange B').pieces j) (D.sectionsMap_component_le B' hW' j)).hom
    (s.val j), ?_⟩
  intro i j
  have hdouble : W' ⊓ (D.baseChange B').pieces i ⊓ (D.baseChange B').pieces j ≤
      relCurveMap C B B' ⁻¹ᵁ (W ⊓ D.pieces i ⊓ D.pieces j) := by
    rw [Scheme.Hom.preimage_inf]
    exact inf_le_inf (D.sectionsMap_component_le B' hW' i)
      (D.toBasicOpenCoverData.baseChange_pieces_le_preimage B' j)
  have key := congrArg
    (((relCurveMap C B B').appLE (W ⊓ D.pieces i ⊓ D.pieces j)
      (W' ⊓ (D.baseChange B').pieces i ⊓ (D.baseChange B').pieces j) hdouble).hom)
    ((mem_gluedSubmodule_iff B D.pieces D.unit
      (s.val : ∀ l : D.index, Γ(relCurve C B, W ⊓ D.pieces l))).mp s.property i j)
  rw [map_mul] at key
  have e₁ := (relCurveMap C B B').appLE_resHom
    (inf_le_left : W ⊓ D.pieces i ⊓ D.pieces j ≤ W ⊓ D.pieces i)
    (D.sectionsMap_component_le B' hW' i) hdouble
    (inf_le_left : W' ⊓ (D.baseChange B').pieces i ⊓ (D.baseChange B').pieces j ≤
      W' ⊓ (D.baseChange B').pieces i) (s.val i)
  have e₂ := (relCurveMap C B B').appLE_resHom
    (gluedInclCoc D.pieces W i j)
    (D.toBasicOpenCoverData.baseChange_inf_le_preimage B' i j) hdouble
    (gluedInclCoc (D.baseChange B').pieces W' i j)
    ((D.unit i j : Γ(relCurve C B, D.pieces i ⊓ D.pieces j)))
  have e₃ := (relCurveMap C B B').appLE_resHom
    (gluedInclSnd D.pieces W i j)
    (D.sectionsMap_component_le B' hW' j) hdouble
    (gluedInclSnd (D.baseChange B').pieces W' i j) (s.val j)
  rw [← e₁, ← e₂, ← e₃] at key
  exact key

@[simp]
lemma sectionsMap_coe (hW' : W' ≤ relCurveMap C B B' ⁻¹ᵁ W)
    (s : ↥(gluedSubmodule B D.pieces D.unit W)) (j : D.index) :
    (D.sectionsMap B' hW' s).val j =
      ((relCurveMap C B B').appLE (W ⊓ D.pieces j)
        (W' ⊓ (D.baseChange B').pieces j)
        (D.sectionsMap_component_le B' hW' j)).hom (s.val j) := rfl

/-- The comparison of glued sections is additive. -/
lemma sectionsMap_add (hW' : W' ≤ relCurveMap C B B' ⁻¹ᵁ W)
    (s t : ↥(gluedSubmodule B D.pieces D.unit W)) :
    D.sectionsMap B' hW' (s + t) = D.sectionsMap B' hW' s + D.sectionsMap B' hW' t := by
  refine Subtype.ext (funext fun j => ?_)
  have hst : (s + t).val j = s.val j + t.val j := rfl
  have hst' : (D.sectionsMap B' hW' s + D.sectionsMap B' hW' t).val j =
      (D.sectionsMap B' hW' s).val j + (D.sectionsMap B' hW' t).val j := rfl
  rw [hst', sectionsMap_coe, sectionsMap_coe, sectionsMap_coe, hst, map_add]

/-- **Semilinearity of the comparison of glued sections**: it intertwines the
coefficient actions along `algebraMap B B'`. -/
lemma sectionsMap_smul (hW' : W' ≤ relCurveMap C B B' ⁻¹ᵁ W) (b : B)
    (s : ↥(gluedSubmodule B D.pieces D.unit W)) :
    D.sectionsMap B' hW' (b • s) = algebraMap B B' b • D.sectionsMap B' hW' s := by
  refine Subtype.ext (funext fun j => ?_)
  have hbs : ((b • s : ↥(gluedSubmodule B D.pieces D.unit W))).val j = b • s.val j := rfl
  have hbs' : ((algebraMap B B' b • D.sectionsMap B' hW' s :
      ↥(gluedSubmodule B' (D.baseChange B').pieces (D.baseChange B').unit W'))).val j =
      algebraMap B B' b • (D.sectionsMap B' hW' s).val j := rfl
  rw [hbs', sectionsMap_coe, sectionsMap_coe, hbs, Scheme.overModule_smul_def,
    Scheme.overModule_smul_def, map_mul]
  congr 1
  exact relCurveMap_appLE_overAlgebraMap C B B' _ b

/-- The comparison of glued sections commutes with restriction. -/
lemma gluedRes_sectionsMap {V' V : (relCurve C B).Opens} (hV'V : V' ≤ V)
    {P' P : (relCurve C B').Opens} (hP : P ≤ relCurveMap C B B' ⁻¹ᵁ V)
    (hP' : P' ≤ relCurveMap C B B' ⁻¹ᵁ V') (hPP : P' ≤ P)
    (s : ↥(gluedSubmodule B D.pieces D.unit V)) :
    gluedRes B' (D.baseChange B').pieces (D.baseChange B').unit hPP
        (D.sectionsMap B' hP s) =
      D.sectionsMap B' hP' (gluedRes B D.pieces D.unit hV'V s) := by
  refine Subtype.ext (funext fun j => ?_)
  rw [gluedRes_coe, sectionsMap_coe, sectionsMap_coe, gluedRes_coe]
  exact (relCurveMap C B B').appLE_resHom
    (inf_le_inf_right (D.pieces j) hV'V) (D.sectionsMap_component_le B' hP j)
    (D.sectionsMap_component_le B' hP' j)
    (inf_le_inf_right ((D.baseChange B').pieces j) hPP) (s.val j)

/-- **The comparison intertwines the piece trivializations with `appLE`**: on an open
below a piece, trivializing the compared section is `appLE` of the trivialized
section. -/
lemma gluedTriv_sectionsMap (hW' : W' ≤ relCurveMap C B B' ⁻¹ᵁ W) {j : D.index}
    (hWj : W ≤ D.pieces j) (hW'j : W' ≤ (D.baseChange B').pieces j)
    (s : ↥(gluedSubmodule B D.pieces D.unit W)) :
    gluedTriv B' (D.baseChange B').isGluingCocycle j hW'j (D.sectionsMap B' hW' s) =
      ((relCurveMap C B B').appLE W W'
        (hW'.trans (Scheme.Hom.preimage_mono _ le_rfl))).hom
        (gluedTriv B D.isGluingCocycle j hWj s) := by
  rw [gluedTriv_apply, gluedTriv_apply, sectionsMap_coe]
  exact (relCurveMap C B B').appLE_resHom (le_inf le_rfl hWj)
    (D.sectionsMap_component_le B' hW' j) (hW'.trans (Scheme.Hom.preimage_mono _ le_rfl))
    (le_inf le_rfl hW'j) (s.val j)

/-- **The comparison intertwines the componentwise chart actions**: acting by
`r ∈ Γ(C_B, V)` then comparing equals comparing then acting by the compared scalar. -/
lemma sectionsMap_gluedQsmul {V : (relCurve C B).Opens} {V' : (relCurve C B').Opens}
    (hWV : W ≤ V) (hW' : W' ≤ relCurveMap C B B' ⁻¹ᵁ W)
    (hV' : V' ≤ relCurveMap C B B' ⁻¹ᵁ V) (hW'V' : W' ≤ V') (r : Γ(relCurve C B, V))
    (s : ↥(gluedSubmodule B D.pieces D.unit W)) :
    D.sectionsMap B' hW' (gluedQsmul B D.pieces D.unit hWV r s) =
      gluedQsmul B' (D.baseChange B').pieces (D.baseChange B').unit hW'V'
        (((relCurveMap C B B').appLE V V' hV').hom r) (D.sectionsMap B' hW' s) := by
  refine Subtype.ext (funext fun j => ?_)
  rw [sectionsMap_coe, gluedQsmul_coe, gluedQsmul_coe, sectionsMap_coe, map_mul]
  congr 1
  exact ((relCurveMap C B B').appLE_resHom (inf_le_left.trans hWV) hV'
    (D.sectionsMap_component_le B' hW' j) (inf_le_left.trans hW'V') r).symm

end SectionsMap

end BasicOpenCocycleDatum

end Datum

end AlgebraicGeometry
