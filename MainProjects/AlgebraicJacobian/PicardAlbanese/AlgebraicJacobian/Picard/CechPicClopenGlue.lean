/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.CechPicClopenSep

/-!
# Gluing Čech Picard classes along a clopen partition

The gluing half of the clopen decomposition of the Čech Picard group: given a scheme `Y`
partitioned by finitely many open immersions with pairwise disjoint ranges, every family
of Čech Picard classes on the pieces arises by restriction of a single class on `Y`
(`AlgebraicGeometry.Scheme.CechPic.exists_map_eq_of_clopen`).

The engine is the **one-piece extension** (`Scheme.CechPic.exists_extension_of_clopen`):
for a single open immersion `w : Z ⟶ Y` whose range is complemented by an open `Ω'`
(disjoint, jointly covering), a class on `Z` extends to a class on `Y` restricting to `1`
over `Ω'`.  The extension cover takes the `w`-image of the given cover on points of the
range and `Ω'` elsewhere; its pair values are the transported cocycle values on
range–range overlaps and `1` otherwise — every mixed overlap is empty, so the cocycle
identity degenerates there (`Scheme.subsingleton_units_of_le_bot`).  A general family is
then assembled as the product of the one-piece extensions.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite CategoryTheory.PresheafOfGroups TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

namespace CechPic

section extension

variable {Y Z : Scheme.{u}} (w : Z ⟶ Y) [IsOpenImmersion w] (Ω' : Y.Opens)
variable (𝒰₀ : Z.PointedCover)

open Classical in
/-- The members of the extension of a pointed cover across a clopen piece: the image of
the member at the chosen preimage point over the range of `w`, the complement `Ω'`
elsewhere. -/
noncomputable def extOpens (y : Y) : Y.Opens :=
  if hy : y ∈ w.opensRange then w ''ᵁ (𝒰₀.opens hy.choose) else Ω'

lemma extOpens_of_mem {y : Y} (hy : y ∈ w.opensRange) :
    extOpens w Ω' 𝒰₀ y = w ''ᵁ (𝒰₀.opens hy.choose) :=
  dif_pos hy

lemma extOpens_of_notMem {y : Y} (hy : y ∉ w.opensRange) : extOpens w Ω' 𝒰₀ y = Ω' :=
  dif_neg hy

lemma extOpens_le_opensRange {y : Y} (hy : y ∈ w.opensRange) :
    extOpens w Ω' 𝒰₀ y ≤ w.opensRange := by
  rw [extOpens_of_mem w Ω' 𝒰₀ hy]
  exact Scheme.Hom.image_le_opensRange w _

lemma preimage_extOpens_of_mem {y : Y} (hy : y ∈ w.opensRange) :
    w ⁻¹ᵁ extOpens w Ω' 𝒰₀ y = 𝒰₀.opens hy.choose := by
  rw [extOpens_of_mem w Ω' 𝒰₀ hy, Scheme.Hom.preimage_image_eq]

/-- The extension of a pointed cover across a clopen piece. -/
noncomputable def extCover (hcov : w.opensRange ⊔ Ω' = ⊤) : Y.PointedCover where
  opens := extOpens w Ω' 𝒰₀
  mem_opens y := by
    by_cases hy : y ∈ w.opensRange
    · rw [extOpens_of_mem w Ω' 𝒰₀ hy]
      have hmem : w hy.choose ∈ w ''ᵁ (𝒰₀.opens hy.choose) :=
        Set.mem_image_of_mem _ (𝒰₀.mem_opens hy.choose)
      rwa [hy.choose_spec] at hmem
    · rw [extOpens_of_notMem w Ω' 𝒰₀ hy]
      have hmem : y ∈ w.opensRange ⊔ Ω' := hcov ▸ trivial
      exact (Opens.mem_sup.mp hmem).resolve_left hy

@[simp]
lemma extCover_opens (hcov : w.opensRange ⊔ Ω' = ⊤) (y : Y) :
    (extCover w Ω' 𝒰₀ hcov).opens y = extOpens w Ω' 𝒰₀ y :=
  rfl

variable (γ₀ : Z.unitsCocycle 𝒰₀)

open Classical in
/-- The pair values of the extension cocycle: the transported values of `γ₀` on
range–range overlaps, `1` otherwise. -/
noncomputable def extPairs (y y' : Y) :
    Γ(Y, extOpens w Ω' 𝒰₀ y ⊓ extOpens w Ω' 𝒰₀ y')ˣ :=
  if hy : y ∈ w.opensRange then
    if hy' : y' ∈ w.opensRange then
      (Scheme.Hom.unitsPreimageEquiv w
        (inf_le_left.trans (extOpens_le_opensRange w Ω' 𝒰₀ hy))).symm
        (Z.unitsRestrict
          (le_inf
            ((w.preimage_mono inf_le_left).trans
              (le_of_eq (preimage_extOpens_of_mem w Ω' 𝒰₀ hy)))
            ((w.preimage_mono inf_le_right).trans
              (le_of_eq (preimage_extOpens_of_mem w Ω' 𝒰₀ hy'))))
          (Scheme.unitsEvInf γ₀ hy.choose hy'.choose))
    else 1
  else 1

lemma extPairs_of_mem {y y' : Y} (hy : y ∈ w.opensRange) (hy' : y' ∈ w.opensRange) :
    extPairs w Ω' 𝒰₀ γ₀ y y'
      = (Scheme.Hom.unitsPreimageEquiv w
          (inf_le_left.trans (extOpens_le_opensRange w Ω' 𝒰₀ hy))).symm
          (Z.unitsRestrict
            (le_inf
              ((w.preimage_mono inf_le_left).trans
                (le_of_eq (preimage_extOpens_of_mem w Ω' 𝒰₀ hy)))
              ((w.preimage_mono inf_le_right).trans
                (le_of_eq (preimage_extOpens_of_mem w Ω' 𝒰₀ hy'))))
            (Scheme.unitsEvInf γ₀ hy.choose hy'.choose)) := by
  unfold extPairs
  rw [dif_pos hy, dif_pos hy']

lemma extPairs_of_notMem_left {y y' : Y} (hy : y ∉ w.opensRange) :
    extPairs w Ω' 𝒰₀ γ₀ y y' = 1 := by
  unfold extPairs
  rw [dif_neg hy]

lemma extPairs_of_notMem_right {y y' : Y} (hy' : y' ∉ w.opensRange) :
    extPairs w Ω' 𝒰₀ γ₀ y y' = 1 := by
  unfold extPairs
  by_cases hy : y ∈ w.opensRange
  · rw [dif_pos hy, dif_neg hy']
  · rw [dif_neg hy]

/-- Any overlap between a range member and a non-range member of the extension cover is
empty. -/
lemma extOpens_overlap_le_bot (hdisj : w.opensRange ⊓ Ω' = ⊥) {y y' : Y}
    (hy : y ∈ w.opensRange) (hy' : y' ∉ w.opensRange) :
    extOpens w Ω' 𝒰₀ y ⊓ extOpens w Ω' 𝒰₀ y' ≤ ⊥ := by
  rw [extOpens_of_notMem w Ω' 𝒰₀ hy']
  exact le_of_le_of_eq
    (inf_le_inf_right Ω' (extOpens_le_opensRange w Ω' 𝒰₀ hy)) hdisj

/-- Witness independence of restricted pair values: the choice of preimage points does
not matter after restriction. -/
private lemma restrict_unitsEvInf_witness (γ₀ : Z.unitsCocycle 𝒰₀) {c z c' z' : Z}
    (h : c = z) (h' : c' = z') {T : Z.Opens}
    (pf : T ≤ 𝒰₀.opens c ⊓ 𝒰₀.opens c') (pf' : T ≤ 𝒰₀.opens z ⊓ 𝒰₀.opens z') :
    Z.unitsRestrict pf (Scheme.unitsEvInf γ₀ c c')
      = Z.unitsRestrict pf' (Scheme.unitsEvInf γ₀ z z') := by
  subst h h'
  rfl

/-- The cocycle identity for the extension pair values: on triple overlaps of range
members it is the transported cocycle identity of `γ₀`; every other triple overlap is
empty. -/
private lemma extPairs_cocycle (hdisj : w.opensRange ⊓ Ω' = ⊥) (y y' y'' : Y) :
    Y.unitsRestrict (inf_le_left :
        extOpens w Ω' 𝒰₀ y ⊓ extOpens w Ω' 𝒰₀ y' ⊓ extOpens w Ω' 𝒰₀ y''
          ≤ extOpens w Ω' 𝒰₀ y ⊓ extOpens w Ω' 𝒰₀ y') (extPairs w Ω' 𝒰₀ γ₀ y y')
        * Y.unitsRestrict (inf_le_inf_right _ inf_le_right)
            (extPairs w Ω' 𝒰₀ γ₀ y' y'')
      = Y.unitsRestrict (inf_le_inf_right _ inf_le_left)
          (extPairs w Ω' 𝒰₀ γ₀ y y'') := by
  by_cases hy : y ∈ w.opensRange
  · by_cases hy' : y' ∈ w.opensRange
    · by_cases hy'' : y'' ∈ w.opensRange
      · -- all three in the range: transport the cocycle identity of `γ₀`
        have hT : extOpens w Ω' 𝒰₀ y ⊓ extOpens w Ω' 𝒰₀ y' ⊓ extOpens w Ω' 𝒰₀ y''
            ≤ w.opensRange :=
          inf_le_left.trans (inf_le_left.trans (extOpens_le_opensRange w Ω' 𝒰₀ hy))
        apply (Scheme.Hom.unitsAppLE_bijective_of_le_opensRange w hT).injective
        rw [map_mul, extPairs_of_mem w Ω' 𝒰₀ γ₀ hy hy',
          extPairs_of_mem w Ω' 𝒰₀ γ₀ hy' hy'', extPairs_of_mem w Ω' 𝒰₀ γ₀ hy hy'']
        rw [Scheme.Hom.map_unitsAppLE, Scheme.Hom.map_unitsAppLE,
          Scheme.Hom.map_unitsAppLE, Scheme.Hom.unitsAppLE_unitsPreimageEquiv_symm,
          Scheme.Hom.unitsAppLE_unitsPreimageEquiv_symm,
          Scheme.Hom.unitsAppLE_unitsPreimageEquiv_symm,
          Scheme.unitsRestrict_unitsRestrict, Scheme.unitsRestrict_unitsRestrict,
          Scheme.unitsRestrict_unitsRestrict]
        have e := congrArg (Z.unitsRestrict
          (le_inf
            (le_inf
              ((w.preimage_mono (inf_le_left.trans inf_le_left)).trans
                (le_of_eq (preimage_extOpens_of_mem w Ω' 𝒰₀ hy)))
              ((w.preimage_mono (inf_le_left.trans inf_le_right)).trans
                (le_of_eq (preimage_extOpens_of_mem w Ω' 𝒰₀ hy'))))
            ((w.preimage_mono inf_le_right).trans
              (le_of_eq (preimage_extOpens_of_mem w Ω' 𝒰₀ hy''))) :
            w ⁻¹ᵁ (extOpens w Ω' 𝒰₀ y ⊓ extOpens w Ω' 𝒰₀ y' ⊓ extOpens w Ω' 𝒰₀ y'')
              ≤ 𝒰₀.opens hy.choose ⊓ 𝒰₀.opens hy'.choose ⊓ 𝒰₀.opens hy''.choose))
          (Scheme.unitsEvInf_trans γ₀ hy.choose hy'.choose hy''.choose)
        erw [map_mul] at e
        simp only [Scheme.unitsRestrict_unitsRestrict] at e
        exact e
      · -- `y''` off the range: the triple overlap is empty
        have hss : Subsingleton Γ(Y,
            extOpens w Ω' 𝒰₀ y ⊓ extOpens w Ω' 𝒰₀ y' ⊓ extOpens w Ω' 𝒰₀ y'')ˣ :=
          Y.subsingleton_units_of_le_bot
            ((le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
              (extOpens_overlap_le_bot w Ω' 𝒰₀ hdisj hy' hy''))
        exact @Subsingleton.elim _ hss _ _
    · -- `y'` off the range: the triple overlap is empty
      have hss : Subsingleton Γ(Y,
          extOpens w Ω' 𝒰₀ y ⊓ extOpens w Ω' 𝒰₀ y' ⊓ extOpens w Ω' 𝒰₀ y'')ˣ :=
        Y.subsingleton_units_of_le_bot
          ((inf_le_left).trans (extOpens_overlap_le_bot w Ω' 𝒰₀ hdisj hy hy'))
      exact @Subsingleton.elim _ hss _ _
  · by_cases hy'' : y'' ∈ w.opensRange
    · -- `y` off the range, `y''` in it: the triple overlap is empty
      have hss : Subsingleton Γ(Y,
          extOpens w Ω' 𝒰₀ y ⊓ extOpens w Ω' 𝒰₀ y' ⊓ extOpens w Ω' 𝒰₀ y'')ˣ :=
        Y.subsingleton_units_of_le_bot
          ((le_inf inf_le_right (inf_le_left.trans inf_le_left)).trans
            (extOpens_overlap_le_bot w Ω' 𝒰₀ hdisj hy'' hy))
      exact @Subsingleton.elim _ hss _ _
    · -- both `y` and `y''` off the range: all values are `1`
      rw [extPairs_of_notMem_left w Ω' 𝒰₀ γ₀ hy,
        extPairs_of_notMem_right w Ω' 𝒰₀ γ₀ hy'',
        extPairs_of_notMem_left w Ω' 𝒰₀ γ₀ hy, map_one, map_one, map_one, one_mul]

variable (hdisj : w.opensRange ⊓ Ω' = ⊥) (hcov : w.opensRange ⊔ Ω' = ⊤)

/-- The extension cocycle across a clopen piece, built from its pair values. -/
noncomputable def extCocycle : Y.unitsCocycle (extCover w Ω' 𝒰₀ hcov) :=
  OneCocycle.ofPairs (extPairs w Ω' 𝒰₀ γ₀)
    (fun y y' y'' => extPairs_cocycle w Ω' 𝒰₀ γ₀ hdisj y y' y'')

/-- **The one-piece extension of a Čech Picard class across a clopen decomposition.** -/
noncomputable def extendClass : Y.CechPic :=
  CechPic.mk (extCover w Ω' 𝒰₀ hcov)
    (OneCocycle.class (extCocycle w Ω' 𝒰₀ γ₀ hdisj hcov))

/-- The given cover refines the pullback of the extension cover. -/
lemma le_pullback_extCover : 𝒰₀ ≤ (extCover w Ω' 𝒰₀ hcov).pullback w := by
  intro z
  have hz : (w z : Y) ∈ w.opensRange := ⟨z, rfl⟩
  rw [PointedCover.pullback_opens, extCover_opens, preimage_extOpens_of_mem w Ω' 𝒰₀ hz,
    show hz.choose = z from w.isOpenEmbedding.injective hz.choose_spec]

/-- The extension restricts on the piece to the given class. -/
theorem map_extendClass :
    CechPic.map w (extendClass w Ω' 𝒰₀ γ₀ hdisj hcov)
      = CechPic.mk 𝒰₀ (OneCocycle.class γ₀) := by
  have hres : (w.pullbackUnitsCocycle (extCocycle w Ω' 𝒰₀ γ₀ hdisj hcov)).res
      (fun z => homOfLE (le_pullback_extCover w Ω' 𝒰₀ hcov z)) = γ₀ := by
    ext1
    ext z z' T a b
    rw [OneCocycle.res_ev, Scheme.Hom.pullbackUnitsCocycle_ev]
    have hz : (w z : Y) ∈ w.opensRange := ⟨z, rfl⟩
    have hz' : (w z' : Y) ∈ w.opensRange := ⟨z', rfl⟩
    have hpair : Scheme.unitsEvInf (extCocycle w Ω' 𝒰₀ γ₀ hdisj hcov) (w z) (w z')
        = extPairs w Ω' 𝒰₀ γ₀ (w z) (w z') :=
      OneCocycle.ofPairs_evInf (G := Y.unitsPresheaf ⋙ forget₂ CommGrpCat GrpCat)
        (U := (extCover w Ω' 𝒰₀ hcov).opens) (extPairs w Ω' 𝒰₀ γ₀) _ (w z) (w z')
    rw [hpair, extPairs_of_mem w Ω' 𝒰₀ γ₀ hz hz']
    simp only [extCover_opens]
    erw [Scheme.Hom.unitsAppLE_unitsPreimageEquiv_symm,
      Scheme.unitsRestrict_unitsRestrict,
      restrict_unitsEvInf_witness 𝒰₀ γ₀
        (show hz.choose = z from w.isOpenEmbedding.injective hz.choose_spec)
        (show hz'.choose = z' from w.isOpenEmbedding.injective hz'.choose_spec)
        _ (le_inf a.le b.le)]
    exact (γ₀.toOneCochain.ev_eq_evInf z z' a b).symm
  calc CechPic.map w (extendClass w Ω' 𝒰₀ γ₀ hdisj hcov)
      = CechPic.mk ((extCover w Ω' 𝒰₀ hcov).pullback w)
          ((w.pullbackUnitsCocycle (extCocycle w Ω' 𝒰₀ γ₀ hdisj hcov)).class) := rfl
    _ = CechPic.mk 𝒰₀ (unitsRes (le_pullback_extCover w Ω' 𝒰₀ hcov)
          ((w.pullbackUnitsCocycle (extCocycle w Ω' 𝒰₀ γ₀ hdisj hcov)).class)) :=
        (CechPic.mk_unitsRes (le_pullback_extCover w Ω' 𝒰₀ hcov) _).symm
    _ = CechPic.mk 𝒰₀ (OneCocycle.class γ₀) := by
        refine congrArg (CechPic.mk 𝒰₀) ?_
        change OneCocycle.class ((w.pullbackUnitsCocycle
          (extCocycle w Ω' 𝒰₀ γ₀ hdisj hcov)).res
            (fun z => homOfLE (le_pullback_extCover w Ω' 𝒰₀ hcov z))) = _
        rw [hres]

/-- The extension restricts trivially over the complement of the piece. -/
theorem map_extendClass_of_le_compl {W : Scheme.{u}} (v : W ⟶ Y)
    (hv : ∀ x : W, v.base x ∈ Ω') :
    CechPic.map v (extendClass w Ω' 𝒰₀ γ₀ hdisj hcov) = 1 := by
  have hnot : ∀ x : W, v.base x ∉ w.opensRange := by
    intro x hmem
    have hbot : v.base x ∈ w.opensRange ⊓ Ω' := ⟨hmem, hv x⟩
    rw [hdisj] at hbot
    exact hbot
  have hcoc : v.pullbackUnitsCocycle (extCocycle w Ω' 𝒰₀ γ₀ hdisj hcov) = 1 := by
    ext x x' T a b
    rw [Scheme.Hom.pullbackUnitsCocycle_ev]
    have hpair : Scheme.unitsEvInf (extCocycle w Ω' 𝒰₀ γ₀ hdisj hcov)
        (v.base x) (v.base x') = extPairs w Ω' 𝒰₀ γ₀ (v.base x) (v.base x') :=
      OneCocycle.ofPairs_evInf (G := Y.unitsPresheaf ⋙ forget₂ CommGrpCat GrpCat)
        (U := (extCover w Ω' 𝒰₀ hcov).opens) (extPairs w Ω' 𝒰₀ γ₀) _
        (v.base x) (v.base x')
    rw [hpair, extPairs_of_notMem_left w Ω' 𝒰₀ γ₀ (hnot x)]
    exact map_one _
  calc CechPic.map v (extendClass w Ω' 𝒰₀ γ₀ hdisj hcov)
      = CechPic.mk ((extCover w Ω' 𝒰₀ hcov).pullback v)
          ((v.pullbackUnitsCocycle (extCocycle w Ω' 𝒰₀ γ₀ hdisj hcov)).class) := rfl
    _ = CechPic.mk ((extCover w Ω' 𝒰₀ hcov).pullback v) (OneCocycle.class 1) := by
        rw [hcoc]
    _ = 1 := CechPic.mk_one _

end extension

/-! ## The finite assembly -/

section assembly

variable {ι : Type u} {Y : Scheme.{u}} {Z : ι → Scheme.{u}} (w : ∀ i, Z i ⟶ Y)
  [∀ i, IsOpenImmersion (w i)]

/-- **Gluing of Čech Picard classes along a finite clopen partition**: every family of
classes on the pieces of a finite clopen partition of `Y` is the family of restrictions
of a single class on `Y`. -/
theorem exists_map_eq_of_clopen [Finite ι]
    (hdisj : ∀ i j, i ≠ j → (w i).opensRange ⊓ (w j).opensRange = ⊥)
    (hcover : ∀ y : Y, ∃ i, y ∈ (w i).opensRange) (L : ∀ i, (Z i).CechPic) :
    ∃ M : Y.CechPic, ∀ i, CechPic.map (w i) M = L i := by
  classical
  haveI := Fintype.ofFinite ι
  -- represent the classes by cocycles
  have hrep : ∀ i, ∃ (𝒰 : (Z i).PointedCover) (γ : (Z i).unitsCocycle 𝒰),
      L i = CechPic.mk 𝒰 (OneCocycle.class γ) := by
    intro i
    induction L i using CechPic.ind with | _ 𝒰 a =>
    induction a using Quot.ind with | _ γ =>
    exact ⟨𝒰, γ, rfl⟩
  choose 𝒰s γs hL using hrep
  -- the complement of one piece is the union of the others
  set Ω' : ι → Y.Opens := fun i => ⨆ j ∈ ({i}ᶜ : Set ι), (w j).opensRange with hΩ'
  have hdisj' : ∀ i, (w i).opensRange ⊓ Ω' i = ⊥ := by
    intro i
    rw [hΩ', inf_iSup_eq]
    refine le_bot_iff.mp (iSup_le fun j => ?_)
    rw [inf_iSup_eq]
    refine iSup_le fun hj => ?_
    exact le_of_eq (hdisj i j (fun h => hj (h ▸ rfl)))
  have hcov' : ∀ i, (w i).opensRange ⊔ Ω' i = ⊤ := by
    intro i
    refine le_antisymm le_top (fun y _ => ?_)
    obtain ⟨j, hj⟩ := hcover y
    by_cases hij : j = i
    · exact Opens.mem_sup.mpr (Or.inl (hij ▸ hj))
    · refine Opens.mem_sup.mpr (Or.inr ?_)
      have hle : (w j).opensRange ≤ Ω' i := by
        rw [hΩ']
        exact le_iSup₂ (f := fun j _ => (w j).opensRange) j hij
      exact hle hj
  -- the one-piece extensions
  set M : ι → Y.CechPic := fun i =>
    CechPic.extendClass (w i) (Ω' i) (𝒰s i) (γs i) (hdisj' i) (hcov' i) with hM
  refine ⟨∏ i, M i, fun i => ?_⟩
  rw [map_prod]
  have hMii : CechPic.map (w i) (M i) = L i := by
    rw [hM, CechPic.map_extendClass, hL i]
  have hMij : ∀ j, j ≠ i → CechPic.map (w i) (M j) = 1 := by
    intro j hj
    rw [hM]
    refine CechPic.map_extendClass_of_le_compl (w j) (Ω' j) (𝒰s j) (γs j)
      (hdisj' j) (hcov' j) (w i) (fun x => ?_)
    have hle : (w i).opensRange ≤ Ω' j := by
      rw [hΩ']
      exact le_iSup₂ (f := fun k _ => (w k).opensRange) i (fun h => hj h.symm)
    exact hle ⟨x, rfl⟩
  calc ∏ j, CechPic.map (w i) (M j) = CechPic.map (w i) (M i) :=
        Finset.prod_eq_single_of_mem i (Finset.mem_univ i)
          (fun j _ hj => hMij j hj)
    _ = L i := hMii

end assembly

end CechPic

end Scheme

end AlgebraicGeometry
