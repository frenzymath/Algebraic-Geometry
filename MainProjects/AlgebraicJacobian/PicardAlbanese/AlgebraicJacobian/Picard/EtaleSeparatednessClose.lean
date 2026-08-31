/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.WitnessAssembly
import AlgebraicJacobian.Picard.CoherentWitnessExists
import AlgebraicJacobian.Picard.CechPicToPicNaturality
import AlgebraicJacobian.Picard.CechPicSurjective
import AlgebraicJacobian.Picard.PicEtAffMap

/-!
# The (C1) étale-separatedness close: reduction and the plus unfold (ζ3)

This file performs the class-level reduction of the (C1) étale-separatedness theorem
(Kleiman, *The Picard Scheme*, 2.5(1)) and the unfold of the étale plus construction,
against the **kernel property** of the base change
`cg^* : CechPic X_A → CechPic X_B` — that a class killed by `cg^*` is pulled back from
`Spec A` — which is proved in `AlgebraicJacobian.Picard.CechKernelLemma`:

* `AlgebraicGeometry.Over.exists_cechPic_map_snd_eq_of_ker`: **the reduction.** From
  ζ1's hypothesis `p_B^* N₀ = cg^* L`, the ζ2 machinery (coherent witness ζ2·i,
  pi-assembly ζ2·ii) descends the class of `N₀` to `M := cechPicEquivPic⁻¹` of the
  Picard class of the composite descent unit; the dictionary naturality (`toPic_map`)
  plus the ε2 corollary `mapAlgebra_picClass_assemblyUnit` give `g_S^* M = N₀` **on the
  nose** (classes on an affine scheme are determined by `toPic`, which is injective).
  Hence `L / p_A^* M` is killed by `cg^*`, and the kernel property finishes:
  `L = p_A^* (M ⋅ M₁)`.
* `AlgebraicGeometry.PicEtAff.unit_injective_of_ker`: **the unfold.** `unit C A x = 1`
  is unwound through `mk_eq_mk_iff`, essential uniqueness of `A`-algebra maps out of
  `A` (`AlgHom.subsingleton_id`), and the `relPicMk`-calculus, to exactly the ζ1
  hypothesis on some étale cover carrier; the reduction plus the kernel property give
  `x = 1`.

## Organization decision (ζ3)

ζ3 is organized around the **standalone kernel lemma** (the alternative organization of
the worksheet `informal/c1-etale-separatedness-assembly.md`, step 3): the by-construction
tracking of the ζ2 witness is consumed only through the *class equation* of
`Over.mapAlgebra_picClass_assemblyUnit`, and the on-the-nose equality `g_S^* M = N₀`
falls out of injectivity of the affine dictionary — no cocycle-level tracking of `θ'`
crosses this file.  The genuinely fppf content (the `descend_coboundary` analogue) is
isolated in the kernel lemma, where the class killed by `cg^*` comes with a *fresh*
trivialization and its own descent unit.  The two halves meet in
`AlgebraicJacobian.Picard.CechKernelLemma`, which supplies the kernel property and
derives the final `PicEtAff.unit_injective`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace
open AlgebraicGeometry.Scheme (CechPic)

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable (C : Over (Spec (.of k)))
  [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

-- Reactivate the section-ring algebra structures of
-- `AlgebraicJacobian.Picard.WitnessAway` (they are `local instance`s there).
attribute [local instance] specSectionsAlgebra overSpecSectionsAlgebra
  overSpecSectionsAlgebraSq overSpecSectionsAlgebraScb algebraA_sections
  isScalarTower_sections isScalarTower_sections_basicOpen

section reduction

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

set_option quotPrecheck false in
local notation "XA" => (C ⊗ overSpec k A).left
set_option quotPrecheck false in
local notation "XB" => (C ⊗ overSpec k B).left
set_option quotPrecheck false in
local notation "SA" => (overSpec k A).left
set_option quotPrecheck false in
local notation "SB" => (overSpec k B).left
set_option quotPrecheck false in
local notation "gS" => (Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left
set_option quotPrecheck false in
local notation "cg" =>
  (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left
set_option quotPrecheck false in
local notation "pA" => (snd C (overSpec k A)).left
set_option quotPrecheck false in
local notation "pB" => (snd C (overSpec k B)).left

variable [Module.FaithfullyFlat A B]

omit [Module.FaithfullyFlat A B] in
/-- The base-change ring map intertwines the `ΓSpecIso`-inverses with the canonical
`A`-algebra structure on the global sections of `Spec B`. -/
private lemma appTop_comp_ΓSpecIso_inv :
    (gS).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom
      = algebraMap A Γ(SB, ⊤) := by
  ext a
  change (gS).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv.hom a)
    = ((SB).presheaf.map (homOfLE (le_top : (⊤ : (SB).Opens) ≤ ⊤)).op).hom
        ((Scheme.ΓSpecIso (.of B)).inv.hom (algebraMap A B a))
  rw [show (homOfLE (le_top : (⊤ : (SB).Opens) ≤ ⊤)).op = 𝟙 (op (⊤ : (SB).Opens))
      from rfl, CategoryTheory.Functor.map_id]
  exact ΓSpecIso_inv_appTop (CommRingCat.ofHom (algebraMap A B)) a

/-- **The ζ3 reduction** (Kleiman 2.5(1), class-level half): given the kernel property
of `cg^*` and ζ1's hypothesis `p_B^* N₀ = cg^* L`, the class `L` is pulled back from the
base: the ζ2 descent class of `N₀` gives `M` with `g_S^* M = N₀` on the nose (by
injectivity of the affine Čech–Picard dictionary), so `L / p_A^* M` is killed by `cg^*`
and the kernel property produces the correction. -/
theorem Over.exists_cechPic_map_snd_eq_of_ker
    (hker : ∀ E : (XA).CechPic, CechPic.map (cg) E = 1
      → ∃ M₁ : (SA).CechPic, CechPic.map (pA) M₁ = E)
    (L : (XA).CechPic) (N₀ : (SB).CechPic)
    (h : CechPic.map (pB) N₀ = CechPic.map (cg) L) :
    ∃ M : (SA).CechPic, CechPic.map (pA) M = L := by
  classical
  induction N₀ using Scheme.CechPic.ind with | _ 𝒩 n =>
  induction n using Quot.ind with | _ γ =>
  rw [show (Quot.mk _ γ : (SB).unitsH1 𝒩)
    = CategoryTheory.PresheafOfGroups.OneCocycle.class γ from rfl] at h
  -- ### ζ2: the coherent witness and the composite descent unit
  obtain ⟨θ'⟩ := Over.exists_coherentCechWitness C L 𝒩 γ h
  obtain ⟨P⟩ := Scheme.PointedCover.BasicRefinement.nonempty 𝒩
  haveI hFF₁ := faithfullyFlat_sectionsTop (k := k) (A := A) (B := B)
  haveI hFF₂ := P.faithfullyFlat
  haveI hFF₃ := Module.FaithfullyFlat.trans A Γ(SB, ⊤)
    (∀ i, Γ(SB, (SB).basicOpen (P.r i)))
  -- the descended Picard class over `A`
  set c : CommRing.Pic A := (Over.isDescentCocycle_assemblyUnit P θ').picClass with hc
  -- ### the descended Čech class on `Spec A`
  set M : (SA).CechPic := (Scheme.cechPicEquivPic (SA)).symm
    (CommRing.Pic.mapRingHom (Scheme.ΓSpecIso (.of A)).inv.hom c) with hM
  -- ### `g_S^* M = N₀`, by injectivity of the dictionary
  have hgs : CechPic.map (gS) M = Scheme.CechPic.mk 𝒩
      (CategoryTheory.PresheafOfGroups.OneCocycle.class γ) := by
    apply Scheme.CechPic.toPic_injective
    rw [Scheme.CechPic.toPic_map, Scheme.CechPic.toPic_mk 𝒩 γ P]
    have h1 : Scheme.CechPic.toPic (SA) M
        = CommRing.Pic.mapRingHom (Scheme.ΓSpecIso (.of A)).inv.hom c := by
      rw [hM, ← Scheme.cechPicEquivPic_apply]
      exact (Scheme.cechPicEquivPic (SA)).apply_symm_apply _
    rw [h1]
    refine (CommRing.Pic.mapRingHom_mapRingHom
      (f := (Scheme.ΓSpecIso (.of A)).inv.hom) (g := (gS).appTop.hom)
      (M := c)).trans ?_
    refine (congrArg (fun φ : A →+* Γ(SB, ⊤) => CommRing.Pic.mapRingHom φ c)
      appTop_comp_ΓSpecIso_inv).trans ?_
    refine (congr($(CommRing.Pic.mapRingHom_algebraMap
      (R := A) (A := Γ(SB, ⊤))) c)).trans ?_
    exact Over.mapAlgebra_picClass_assemblyUnit P θ'
  -- ### the ratio is killed by `cg^*`; correct by the kernel property
  have hE : CechPic.map (cg) (L * (CechPic.map (pA) M)⁻¹) = 1 := by
    rw [map_mul, map_inv]
    have hcomp : CechPic.map (cg) (CechPic.map (pA) M) = CechPic.map (pB)
        (CechPic.map (gS) M) := by
      rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp,
        ← Scheme.CechPic.map_comp,
        Over.snd_left_naturality C
          (Over.overSpecMap ((Algebra.ofId A B).restrictScalars k))]
    rw [hcomp, hgs, h, mul_inv_cancel]
  obtain ⟨M₁, hM₁⟩ := hker (L * (CechPic.map (pA) M)⁻¹) hE
  refine ⟨M * M₁, ?_⟩
  rw [map_mul, hM₁, mul_comm L ((CechPic.map (pA) M)⁻¹), ← mul_assoc,
    mul_inv_cancel, one_mul]

end reduction

/-! ## The plus unfold -/

section unfold

variable (A : Type u) [CommRing A] [Algebra k A]

set_option quotPrecheck false in
local notation "XA" => (C ⊗ overSpec k A).left
set_option quotPrecheck false in
local notation "SA" => (overSpec k A).left
set_option quotPrecheck false in
local notation "pA" => (snd C (overSpec k A)).left

/-- **The unfold of the étale plus construction**: injectivity of the unit of
`PicEtAff`, given the kernel property of the base-change pullback for every tower
`A → B` with `A → B` faithfully flat.  A plus class killed by the unit is, after
`mk_eq_mk_iff` and essential uniqueness of `A`-algebra maps out of `A`, exactly ζ1's
hypothesis on some étale cover carrier; the reduction
`Over.exists_cechPic_map_snd_eq_of_ker` then pulls the representing class back from
`Spec A`. -/
theorem PicEtAff.unit_injective_of_ker
    (hker : ∀ (B : Type u) [CommRing B] [Algebra k B] [Algebra A B]
      [IsScalarTower k A B] [Module.FaithfullyFlat A B],
      ∀ E : (XA).CechPic,
        CechPic.map (C ◁ Over.overSpecMap
          ((Algebra.ofId A B).restrictScalars k)).left E = 1
        → ∃ M₁ : (SA).CechPic, CechPic.map (pA) M₁ = E) :
    Function.Injective (PicEtAff.unit C A) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using relPic.ind with | mk L =>
  -- ### unwind the plus-class equality to a single étale cover carrier
  rw [PicEtAff.one_def] at hx
  obtain ⟨G, f, g, hfg⟩ := (PicEtAff.mk_eq_mk_iff C).mp hx
  have hval := congrArg Subtype.val hfg
  rw [descentMap_coe, descentMap_coe, OneMemClass.coe_one, map_one] at hval
  -- the two-step transport is transport along `ofId A G.Carrier`
  have hcomp : (f.restrictScalars k).comp
        ((Algebra.ofId A (Algebra.EtaleCover.self A).Carrier).restrictScalars k)
      = (Algebra.ofId A G.Carrier).restrictScalars k := by
    have h1 : f.comp (Algebra.ofId A (Algebra.EtaleCover.self A).Carrier)
        = Algebra.ofId A G.Carrier := Subsingleton.elim _ _
    calc (f.restrictScalars k).comp
          ((Algebra.ofId A (Algebra.EtaleCover.self A).Carrier).restrictScalars k)
        = (f.comp (Algebra.ofId A (Algebra.EtaleCover.self A).Carrier)).restrictScalars
            k := AlgHom.ext fun _ => rfl
      _ = (Algebra.ofId A G.Carrier).restrictScalars k := by rw [h1]
  have hone : relPicAlgMap C ((Algebra.ofId A G.Carrier).restrictScalars k)
      (relPicMk C (overSpec k A) L) = 1 := by
    rw [← hcomp, relPicAlgMap_comp]
    exact hval
  -- ### the ζ1 hypothesis, in `CechPic` form
  rw [relPicAlgMap, relPicMap_mk] at hone
  have hmem : CechPic.map
      (C ◁ Over.overSpecMap ((Algebra.ofId A G.Carrier).restrictScalars k)).left L
      ∈ picFromBase C (overSpec k G.Carrier) :=
    (QuotientGroup.eq_one_iff _).mp hone
  obtain ⟨N₀, hN₀⟩ := (mem_picFromBase_iff (C := C)).mp hmem
  -- ### the reduction pulls `L` back from the base
  obtain ⟨M, hM⟩ := Over.exists_cechPic_map_snd_eq_of_ker C
    (hker G.Carrier) L N₀ hN₀
  exact (QuotientGroup.eq_one_iff L).mpr ⟨M, hM⟩

end unfold

end AlgebraicGeometry
