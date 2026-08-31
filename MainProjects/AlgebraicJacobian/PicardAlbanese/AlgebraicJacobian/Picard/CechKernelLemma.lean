/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.CechKernelGlue
import AlgebraicJacobian.Picard.KernelDescentUnit
import AlgebraicJacobian.Picard.DescentClassRepBuild
import AlgebraicJacobian.Picard.EtaleSeparatednessClose

/-!
# The Čech kernel lemma and étale separatedness (ζ3 bricks K and the close)

**The kernel lemma** (`AlgebraicGeometry.Over.exists_cechPic_map_snd_of_ker_whiskerLeft`):
for a proper, geometrically irreducible and geometrically reduced curve `C` over `k` and
a faithfully flat tower `A → B` of `k`-algebras, every Čech Picard class on
`X_A = (C ⊗ Spec A).left` killed by the base-change pullback `cg^*` is pulled back from
`Spec A`.  Route: extract a trivializing `0`-cochain `β` from the kernel hypothesis;
produce the descent unit `w` (ζ3 brick W, `exists_kernelDescentUnit`); represent its
descended class by a cover/cocycle/`μ` triple (ζ3 brick M, `descentClassRep`); glue and
descend the cobounding units on an affine refinement (ζ3 brick G,
`exists_kernelCobounding`); verify the coboundary relation by injectivity of `cg`-pullback
and the `transition` field (`kernelCobounding_rel`); conclude by `mk_eq_mk_iff`.

**The close** (`AlgebraicGeometry.PicEtAff.unit_injective`, Kleiman 2.5(1), axiom (C1)):
the unit of the étale plus construction of the relative Picard functor is injective on
every affine test algebra — the étale separatedness of `PicEtAff`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry

section kernel

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
local notation "cg" =>
  (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left
set_option quotPrecheck false in
local notation "u₁" => (C ◁ Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "u₂" => (C ◁ Over.overSpecMap (tensorInr (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "pA" => (snd C (overSpec k A)).left
set_option quotPrecheck false in
local notation "pB" => (snd C (overSpec k B)).left
set_option quotPrecheck false in
local notation "p₂" => (snd C (overSpec k (B ⊗[A] B))).left
set_option quotPrecheck false in
local notation "SA" => (overSpec k A).left
set_option quotPrecheck false in
local notation "SB" => (overSpec k B).left
set_option quotPrecheck false in
local notation "Sq" => (overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "gS" => (Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left
set_option quotPrecheck false in
local notation "q₁" => (Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "q₂" => (Over.overSpecMap (tensorInr (A := A) (B := B))).left

namespace Over

/-- The abelian telescope of the coboundary verification. -/
private lemma rel_telescope {G : Type u} [CommGroup G] {bx Lxs Lxt Lst ms mt D : G}
    (hμ : ms = D * mt) (hL : Lxs * Lst = Lxt) :
    bx⁻¹ * Lxs⁻¹ * ms⁻¹ * D = Lst * (bx⁻¹ * Lxt⁻¹ * mt⁻¹) := by
  subst hμ; rw [← hL, mul_inv D mt, mul_inv Lxs Lst,
    mul_assoc (bx⁻¹ * Lxs⁻¹) (D⁻¹ * mt⁻¹) D, mul_assoc D⁻¹ mt⁻¹ D,
    mul_comm mt⁻¹ D, ← mul_assoc D⁻¹ D mt⁻¹, inv_mul_cancel D, one_mul,
    mul_comm Lst (bx⁻¹ * (Lxs⁻¹ * Lst⁻¹) * mt⁻¹),
    mul_assoc (bx⁻¹ * (Lxs⁻¹ * Lst⁻¹)) mt⁻¹ Lst, mul_comm mt⁻¹ Lst,
    mul_assoc bx⁻¹ (Lxs⁻¹ * Lst⁻¹) (Lst * mt⁻¹),
    mul_assoc Lxs⁻¹ Lst⁻¹ (Lst * mt⁻¹), ← mul_assoc Lst⁻¹ Lst mt⁻¹,
    inv_mul_cancel Lst, one_mul, ← mul_assoc bx⁻¹ Lxs⁻¹ mt⁻¹]

set_option maxHeartbeats 1600000 in
-- the concrete product towers exceed the default budget
/-- **The coboundary relation of the descended units** (ζ3 brick K): the units `c`
produced by `exists_kernelCobounding` cobound `lam` against the `p_A`-pullback of the
representing cocycle `d`, by injectivity of the `cg`-pullback and the `transition`
field of the representative. -/
private lemma kernelCobounding_rel [Module.FaithfullyFlat A B]
    (ℰ : (XA).PointedCover) (lam : (XA).unitsCocycle ℰ)
    (β : ∀ v : XB, Γ(XB, (ℰ.pullback (cg)).opens v)ˣ)
    (𝒞 : (SA).PointedCover) (d : (SA).unitsCocycle 𝒞)
    (μ : ∀ a : SA, Γ(SB, (gS) ⁻¹ᵁ 𝒞.opens a)ˣ)
    (htrans : ∀ (a b : SA) (T : (SB).Opens)
      (ha : T ≤ (gS) ⁻¹ᵁ 𝒞.opens a) (hb : T ≤ (gS) ⁻¹ᵁ 𝒞.opens b),
      (SB).unitsRestrict ha (μ a)
        = (gS).unitsAppLE (𝒞.opens a ⊓ 𝒞.opens b) T ((gS).le_preimage_inf ha hb)
            (Scheme.unitsEvInf d a b)
          * (SB).unitsRestrict hb (μ b))
    (s t : XA) (Us Ut : (XA).Opens)
    (hUsE : Us ≤ ℰ.opens s) (hUsC : Us ≤ (pA) ⁻¹ᵁ 𝒞.opens ((pA).base s))
    (hUtE : Ut ≤ ℰ.opens t) (hUtC : Ut ≤ (pA) ⁻¹ᵁ 𝒞.opens ((pA).base t))
    (cs : Γ(XA, Us)ˣ) (ct : Γ(XA, Ut)ˣ)
    (hcs : ∀ (x : XB) (T : (XB).Opens)
      (hT𝒜 : T ≤ (ℰ.pullback (cg)).opens x) (hTU : T ≤ (cg) ⁻¹ᵁ Us),
      (cg).unitsAppLE Us T hTU cs
        = gluePiece C ℰ lam β 𝒞 μ s x T hT𝒜 (hTU.trans ((cg).preimage_mono hUsE))
            (hTU.trans (preimage_le_pB_gS C 𝒞 s Us hUsC)))
    (hct : ∀ (x : XB) (T : (XB).Opens)
      (hT𝒜 : T ≤ (ℰ.pullback (cg)).opens x) (hTU : T ≤ (cg) ⁻¹ᵁ Ut),
      (cg).unitsAppLE Ut T hTU ct
        = gluePiece C ℰ lam β 𝒞 μ t x T hT𝒜 (hTU.trans ((cg).preimage_mono hUtE))
            (hTU.trans (preimage_le_pB_gS C 𝒞 t Ut hUtC))) :
    (XA).unitsRestrict (inf_le_left : Us ⊓ Ut ≤ Us) cs
      * (pA).unitsAppLE (𝒞.opens ((pA).base s) ⊓ 𝒞.opens ((pA).base t)) (Us ⊓ Ut)
          ((pA).le_preimage_inf (inf_le_left.trans hUsC) (inf_le_right.trans hUtC))
          (Scheme.unitsEvInf d ((pA).base s) ((pA).base t))
      = (XA).unitsRestrict
          (le_inf (inf_le_left.trans hUsE) (inf_le_right.trans hUtE))
          (Scheme.unitsEvInf lam s t)
        * (XA).unitsRestrict (inf_le_right : Us ⊓ Ut ≤ Ut) ct := by
  have hinj : Function.Injective
      ((cg).unitsAppLE (Us ⊓ Ut) ((cg) ⁻¹ᵁ (Us ⊓ Ut)) le_rfl) := by
    intro a b hab
    exact Units.ext (appLE_whiskerLeft_injective (C := C) (Us ⊓ Ut)
      (congrArg Units.val hab))
  apply hinj
  rw [map_mul, map_mul]
  refine Scheme.unitsRestrict_eq_of_locally_eq
    (W := fun x : XB ↦ (ℰ.pullback (cg)).opens x ⊓ (cg) ⁻¹ᵁ (Us ⊓ Ut))
    (fun _ ↦ inf_le_right)
    (fun v hv ↦ TopologicalSpace.Opens.mem_iSup.mpr
      ⟨v, ⟨(ℰ.pullback (cg)).mem_opens v, hv⟩⟩)
    _ _ (fun x ↦ ?_)
  rw [map_mul, map_mul]
  -- the four factors, in glued normal form
  have hf1 : (XB).unitsRestrict
        (inf_le_right : (ℰ.pullback (cg)).opens x ⊓ (cg) ⁻¹ᵁ (Us ⊓ Ut)
          ≤ (cg) ⁻¹ᵁ (Us ⊓ Ut))
        ((cg).unitsAppLE (Us ⊓ Ut) ((cg) ⁻¹ᵁ (Us ⊓ Ut)) le_rfl
          ((XA).unitsRestrict inf_le_left cs))
      = gluePiece C ℰ lam β 𝒞 μ s x _ inf_le_left
          ((inf_le_right.trans ((cg).preimage_mono inf_le_left)).trans
            ((cg).preimage_mono hUsE))
          ((inf_le_right.trans ((cg).preimage_mono inf_le_left)).trans
            (preimage_le_pB_gS C 𝒞 s Us hUsC)) := by
    rw [Scheme.Hom.map_unitsAppLE, Scheme.Hom.unitsAppLE_map]
    exact hcs x _ inf_le_left (inf_le_right.trans ((cg).preimage_mono inf_le_left))
  have hf4 : (XB).unitsRestrict
        (inf_le_right : (ℰ.pullback (cg)).opens x ⊓ (cg) ⁻¹ᵁ (Us ⊓ Ut)
          ≤ (cg) ⁻¹ᵁ (Us ⊓ Ut))
        ((cg).unitsAppLE (Us ⊓ Ut) ((cg) ⁻¹ᵁ (Us ⊓ Ut)) le_rfl
          ((XA).unitsRestrict inf_le_right ct))
      = gluePiece C ℰ lam β 𝒞 μ t x _ inf_le_left
          ((inf_le_right.trans ((cg).preimage_mono inf_le_right)).trans
            ((cg).preimage_mono hUtE))
          ((inf_le_right.trans ((cg).preimage_mono inf_le_right)).trans
            (preimage_le_pB_gS C 𝒞 t Ut hUtC)) := by
    rw [Scheme.Hom.map_unitsAppLE, Scheme.Hom.unitsAppLE_map]
    exact hct x _ inf_le_left (inf_le_right.trans ((cg).preimage_mono inf_le_right))
  have hf2 : (XB).unitsRestrict
        (inf_le_right : (ℰ.pullback (cg)).opens x ⊓ (cg) ⁻¹ᵁ (Us ⊓ Ut)
          ≤ (cg) ⁻¹ᵁ (Us ⊓ Ut))
        ((cg).unitsAppLE (Us ⊓ Ut) ((cg) ⁻¹ᵁ (Us ⊓ Ut)) le_rfl
          ((pA).unitsAppLE (𝒞.opens ((pA).base s) ⊓ 𝒞.opens ((pA).base t)) (Us ⊓ Ut)
            ((pA).le_preimage_inf (inf_le_left.trans hUsC) (inf_le_right.trans hUtC))
            (Scheme.unitsEvInf d ((pA).base s) ((pA).base t))))
      = ((cg) ≫ (pA)).unitsAppLE
          (𝒞.opens ((pA).base s) ⊓ 𝒞.opens ((pA).base t)) _
          ((inf_le_right.trans
            ((cg).preimage_mono ((pA).le_preimage_inf (inf_le_left.trans hUsC)
              (inf_le_right.trans hUtC)))).trans
            (le_of_eq (Scheme.Hom.comp_preimage _ _ _).symm))
          (Scheme.unitsEvInf d ((pA).base s) ((pA).base t)) := by
    rw [Scheme.Hom.unitsAppLE_map, Scheme.unitsAppLE_unitsAppLE]
  have hf3 : (XB).unitsRestrict
        (inf_le_right : (ℰ.pullback (cg)).opens x ⊓ (cg) ⁻¹ᵁ (Us ⊓ Ut)
          ≤ (cg) ⁻¹ᵁ (Us ⊓ Ut))
        ((cg).unitsAppLE (Us ⊓ Ut) ((cg) ⁻¹ᵁ (Us ⊓ Ut)) le_rfl
          ((XA).unitsRestrict
            (le_inf (inf_le_left.trans hUsE) (inf_le_right.trans hUtE))
            (Scheme.unitsEvInf lam s t)))
      = (cg).unitsAppLE (ℰ.opens s ⊓ ℰ.opens t) _
          ((inf_le_right.trans ((cg).preimage_mono
            (le_inf (inf_le_left.trans hUsE) (inf_le_right.trans hUtE)))))
          (Scheme.unitsEvInf lam s t) := by
    rw [Scheme.Hom.map_unitsAppLE, Scheme.Hom.unitsAppLE_map]
  rw [hf1, hf2, hf3, hf4]
  -- the `μ`-transition, pulled to `X_B`
  have hμ := congrArg ((pB).unitsAppLE
    ((gS) ⁻¹ᵁ 𝒞.opens ((pA).base s) ⊓ (gS) ⁻¹ᵁ 𝒞.opens ((pA).base t))
    ((ℰ.pullback (cg)).opens x ⊓ (cg) ⁻¹ᵁ (Us ⊓ Ut))
    ((pB).le_preimage_inf
      ((inf_le_right.trans ((cg).preimage_mono inf_le_left)).trans
        (preimage_le_pB_gS C 𝒞 s Us hUsC))
      ((inf_le_right.trans ((cg).preimage_mono inf_le_right)).trans
        (preimage_le_pB_gS C 𝒞 t Ut hUtC))))
    (htrans ((pA).base s) ((pA).base t) _ inf_le_left inf_le_right)
  rw [map_mul, Scheme.Hom.map_unitsAppLE, Scheme.Hom.map_unitsAppLE,
    Scheme.unitsAppLE_unitsAppLE,
    unitsAppLE_congr_hom (cg_comp_pA C).symm _ _ _
      (Scheme.unitsEvInf d ((pA).base s) ((pA).base t))] at hμ
  -- the cocycle identity of `lam`, pulled to `X_B`
  have hL := pullback_pair_trans (cg) lam ((cg).base x) s t
    ((cg).le_preimage_inf inf_le_left
      (inf_le_right.trans ((cg).preimage_mono (inf_le_left.trans hUsE))))
    ((cg).le_preimage_inf
      (inf_le_right.trans ((cg).preimage_mono (inf_le_left.trans hUsE)))
      (inf_le_right.trans ((cg).preimage_mono (inf_le_right.trans hUtE))))
    ((cg).le_preimage_inf inf_le_left
      (inf_le_right.trans ((cg).preimage_mono (inf_le_right.trans hUtE))))
  exact rel_telescope hμ hL

/-- Extraction of a trivializing `0`-cochain from the kernel hypothesis. -/
private lemma exists_trivializing_cochain (ℰ : (XA).PointedCover)
    (lam : (XA).unitsCocycle ℰ)
    (hE : Scheme.CechPic.map (cg)
        (Scheme.CechPic.mk ℰ (CategoryTheory.PresheafOfGroups.OneCocycle.class lam))
      = 1) :
    ∃ β : ∀ v : XB, Γ(XB, (ℰ.pullback (cg)).opens v)ˣ, ∀ v v' : XB,
      (XB).unitsRestrict
          (inf_le_left : (ℰ.pullback (cg)).opens v ⊓ (ℰ.pullback (cg)).opens v'
            ≤ (ℰ.pullback (cg)).opens v) (β v)
          * (cg).unitsAppLE (ℰ.opens ((cg).base v) ⊓ ℰ.opens ((cg).base v'))
              ((ℰ.pullback (cg)).opens v ⊓ (ℰ.pullback (cg)).opens v')
              ((cg).le_preimage_inf inf_le_left inf_le_right)
              (Scheme.unitsEvInf lam ((cg).base v) ((cg).base v'))
        = (XB).unitsRestrict inf_le_right (β v') := by
  rw [Scheme.CechPic.map_mk, Scheme.Hom.pullbackUnitsH1_class,
    Scheme.CechPic.mk_eq_one_iff] at hE
  have hcoh : ((cg).pullbackUnitsCocycle lam).IsCohomologous
      (1 : (XB).unitsCocycle (ℰ.pullback (cg))) :=
    (CategoryTheory.PresheafOfGroups.OneCocycle.class_eq_iff _ _).mp hE
  obtain ⟨α, hα⟩ :=
    (CategoryTheory.PresheafOfGroups.OneCocycle.isCohomologous_iff_evInf _ _).mp hcoh
  refine ⟨α, fun v v' => ?_⟩
  have h := hα v v'
  rw [CategoryTheory.PresheafOfGroups.OneCocycle.one_evInf, one_mul] at h
  exact h

set_option maxHeartbeats 3200000 in
-- the concrete product towers exceed the default budget
/-- **The Čech kernel lemma** (ζ3): for a proper, geometrically irreducible and
geometrically reduced `C` over `k` and a faithfully flat tower `A → B`, the kernel of
the base-change pullback `cg^* : CechPic X_A → CechPic X_B` is contained in the image of
`p_A^* : CechPic (Spec A) → CechPic X_A`. -/
theorem exists_cechPic_map_snd_of_ker_whiskerLeft
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    [Module.FaithfullyFlat A B]
    (E : (XA).CechPic) (hE : Scheme.CechPic.map (cg) E = 1) :
    ∃ M₁ : (SA).CechPic, Scheme.CechPic.map (pA) M₁ = E := by
  classical
  induction E using Scheme.CechPic.ind with | _ ℰ e
  induction e using Quot.ind with | _ lam
  rw [show (Quot.mk _ lam : (XA).unitsH1 ℰ)
    = CategoryTheory.PresheafOfGroups.OneCocycle.class lam from rfl] at hE ⊢
  obtain ⟨β, hβ⟩ := exists_trivializing_cochain C ℰ lam hE
  obtain ⟨w, hwloc, hW⟩ := exists_kernelDescentUnit (C := C) ℰ lam (ℰ.pullback (cg))
    (fun _ => le_rfl) β hβ
  obtain ⟨𝒞, d, μ, hratio, htrans⟩ := descentClassRep (k := k) w hW
  -- the affine refinement
  have haff : ∀ s : XA, ∃ V : (XA).Opens,
      IsAffineOpen V ∧ s ∈ V ∧ V ≤ ℰ.opens s ⊓ (pA) ⁻¹ᵁ 𝒞.opens ((pA).base s) := by
    intro s
    obtain ⟨V, hVaff, hsV, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (XA).isBasis_affineOpens
      (show s ∈ ℰ.opens s ⊓ (pA) ⁻¹ᵁ 𝒞.opens ((pA).base s) from
        ⟨ℰ.mem_opens s, 𝒞.mem_opens ((pA).base s)⟩)
    exact ⟨V, hVaff, hsV, hVle⟩
  choose Uof hUaff hUmem hUle using haff
  have hUE : ∀ s, Uof s ≤ ℰ.opens s := fun s => (hUle s).trans inf_le_left
  have hUC : ∀ s, Uof s ≤ (pA) ⁻¹ᵁ 𝒞.opens ((pA).base s) :=
    fun s => (hUle s).trans inf_le_right
  -- the cobounding units
  choose c hc using fun s : XA =>
    exists_kernelCobounding C ℰ lam β hβ 𝒞 μ w hwloc hratio
      s (Uof s) (hUaff s) (hUE s) (hUC s)
  -- assemble the class equality on the refinement
  refine ⟨Scheme.CechPic.mk 𝒞 d.class, ?_⟩
  rw [Scheme.CechPic.map_mk, Scheme.Hom.pullbackUnitsH1_class]
  refine Scheme.CechPic.mk_eq_mk_iff.mpr
    ⟨⟨Uof, hUmem⟩, fun s => hUC s, fun s => hUE s, ?_⟩
  refine CategoryTheory.PresheafOfGroups.OneCocycle.IsCohomologous.class_eq ?_
  refine (CategoryTheory.PresheafOfGroups.OneCocycle.isCohomologous_iff_evInf
    (((pA).pullbackUnitsCocycle d).res
      (fun x => homOfLE ((fun s => hUC s : (⟨Uof, hUmem⟩ : (XA).PointedCover)
        ≤ 𝒞.pullback (pA)) x)))
    (lam.res
      (fun x => homOfLE ((fun s => hUE s : (⟨Uof, hUmem⟩ : (XA).PointedCover)
        ≤ ℰ) x)))).mpr ⟨c, fun s t => ?_⟩
  have e₁ : Scheme.unitsEvInf (𝒰 := (⟨Uof, hUmem⟩ : (XA).PointedCover))
      (((pA).pullbackUnitsCocycle d).res
        (fun x => homOfLE ((fun s => hUC s : (⟨Uof, hUmem⟩ : (XA).PointedCover)
          ≤ 𝒞.pullback (pA)) x))) s t
      = (pA).unitsAppLE (𝒞.opens ((pA).base s) ⊓ 𝒞.opens ((pA).base t))
          (Uof s ⊓ Uof t)
          ((pA).le_preimage_inf (inf_le_left.trans (hUC s))
            (inf_le_right.trans (hUC t)))
          (Scheme.unitsEvInf d ((pA).base s) ((pA).base t)) := by
    rw [Scheme.res_unitsEvInf
        (show (⟨Uof, hUmem⟩ : (XA).PointedCover) ≤ 𝒞.pullback (pA)
          from fun s => hUC s) ((pA).pullbackUnitsCocycle d) s t,
      Scheme.Hom.pullbackUnitsCocycle_unitsEvInf, Scheme.Hom.unitsAppLE_map]
  have e₂ : Scheme.unitsEvInf (𝒰 := (⟨Uof, hUmem⟩ : (XA).PointedCover))
      (lam.res (fun x => homOfLE ((fun s => hUE s : (⟨Uof, hUmem⟩ : (XA).PointedCover)
        ≤ ℰ) x))) s t
      = (XA).unitsRestrict
          (le_inf (inf_le_left.trans (hUE s)) (inf_le_right.trans (hUE t)))
          (Scheme.unitsEvInf lam s t) :=
    Scheme.res_unitsEvInf
      (show (⟨Uof, hUmem⟩ : (XA).PointedCover) ≤ ℰ from fun s => hUE s) lam s t
  calc (XA).unitsRestrict (inf_le_left : Uof s ⊓ Uof t ≤ Uof s) (c s)
        * Scheme.unitsEvInf (𝒰 := (⟨Uof, hUmem⟩ : (XA).PointedCover))
            (((pA).pullbackUnitsCocycle d).res
              (fun x => homOfLE ((fun s => hUC s :
                (⟨Uof, hUmem⟩ : (XA).PointedCover) ≤ 𝒞.pullback (pA)) x))) s t
      = (XA).unitsRestrict inf_le_left (c s)
          * (pA).unitsAppLE (𝒞.opens ((pA).base s) ⊓ 𝒞.opens ((pA).base t))
              (Uof s ⊓ Uof t)
              ((pA).le_preimage_inf (inf_le_left.trans (hUC s))
                (inf_le_right.trans (hUC t)))
              (Scheme.unitsEvInf d ((pA).base s) ((pA).base t)) := by
        rw [e₁]
    _ = (XA).unitsRestrict
          (le_inf (inf_le_left.trans (hUE s)) (inf_le_right.trans (hUE t)))
          (Scheme.unitsEvInf lam s t)
        * (XA).unitsRestrict (inf_le_right : Uof s ⊓ Uof t ≤ Uof t) (c t) :=
        kernelCobounding_rel C ℰ lam β 𝒞 d μ htrans s t (Uof s) (Uof t)
          (hUE s) (hUC s) (hUE t) (hUC t) (c s) (c t) (hc s) (hc t)
    _ = Scheme.unitsEvInf (𝒰 := (⟨Uof, hUmem⟩ : (XA).PointedCover))
          (lam.res (fun x => homOfLE ((fun s => hUE s :
            (⟨Uof, hUmem⟩ : (XA).PointedCover) ≤ ℰ) x))) s t
        * (XA).unitsRestrict (inf_le_right : Uof s ⊓ Uof t ≤ Uof t) (c t) := by
        rw [e₂]

end Over

end kernel

section close

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

/-- **Étale separatedness of the relative Picard functor** (Kleiman 2.5(1), axiom
(C1)): the unit of the étale plus construction `PicEtAff` is injective on every affine
test algebra.  This is the unconditional close of the ζ3 campaign: the kernel lemma
`Over.exists_cechPic_map_snd_of_ker_whiskerLeft` supplies the kernel hypothesis of the
plus unfold `PicEtAff.unit_injective_of_ker`. -/
theorem PicEtAff.unit_injective
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    (A : Type u) [CommRing A] [Algebra k A] :
    Function.Injective (PicEtAff.unit C A) :=
  PicEtAff.unit_injective_of_ker C A fun _ _ _ _ _ _ E hE =>
    Over.exists_cechPic_map_snd_of_ker_whiskerLeft C E hE

end close

end AlgebraicGeometry
