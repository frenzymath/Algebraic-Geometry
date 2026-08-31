/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.SectionsDescent
import AlgebraicJacobian.Picard.CoherentWitness

/-!
# The glued cobounding units of the Čech kernel lemma (ζ3 brick G)

Let `E = [lam]` be a Čech class on `X_A = (C ⊗ Spec A).left` killed by the base-change
pullback `cg^*`, trivialized by a `0`-cochain `β` on the pulled-back cover, with descent
unit `w` (ζ3 brick W) and Čech representative `(𝒞, d, μ)` of its descended class (ζ3
brick M).  For every point `s` and affine open `U ≤ ℰ_s ⊓ p_A⁻¹𝒞_{p_A s}`, this file
glues the local units

`gluePiece = β_x⁻¹ ⋅ (cg^♯ lam_{cg x, s})⁻¹ ⋅ (p_B^♯ μ_{p_A s})⁻¹`

over the cover `{𝒜_x ⊓ cg⁻¹U}` of `cg⁻¹U` (they agree on overlaps by the coboundary
relation of `β` and the cocycle identity of `lam`), shows the glued unit has equal
coprojection pullbacks (by the local ratio form of `w` and the `ratio` field of the
representative), and descends it through `cg` to a unit `c` on `U`
(`Over.exists_kernelCobounding`) — the cobounding `0`-cochain of the kernel lemma.

All data is carried in declaration signatures (never in `variable` commands with
local-notation types).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry

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
local notation "cg₂" =>
  (C ◁ Over.overSpecMap ((Algebra.ofId A (B ⊗[A] B)).restrictScalars k)).left
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

/-! ## Generic helpers -/

/-- Congruence in the morphism for `unitsAppLE` at fixed open and section. -/
lemma unitsAppLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (V : Y.Opens) (O : X.Opens) (e : O ≤ f ⁻¹ᵁ V) (u : Γ(Y, V)ˣ) :
    f.unitsAppLE V O e u = g.unitsAppLE V O (h ▸ e) u := by
  subst h; rfl

/-- Pullback of the cocycle identity of a unit Čech cocycle (local copy of the private
`pullback_pair_trans` of `UnitsCocycle`). -/
lemma pullback_pair_trans {X Y : Scheme.{u}} (f : X ⟶ Y) {𝒰 : Y.PointedCover}
    (γ : Y.unitsCocycle 𝒰) (i j l : Y) {T : X.Opens}
    (e₁ : T ≤ f ⁻¹ᵁ (𝒰.opens i ⊓ 𝒰.opens j)) (e₂ : T ≤ f ⁻¹ᵁ (𝒰.opens j ⊓ 𝒰.opens l))
    (e₃ : T ≤ f ⁻¹ᵁ (𝒰.opens i ⊓ 𝒰.opens l)) :
    f.unitsAppLE (𝒰.opens i ⊓ 𝒰.opens j) T e₁ (Scheme.unitsEvInf γ i j)
      * f.unitsAppLE (𝒰.opens j ⊓ 𝒰.opens l) T e₂ (Scheme.unitsEvInf γ j l)
      = f.unitsAppLE (𝒰.opens i ⊓ 𝒰.opens l) T e₃ (Scheme.unitsEvInf γ i l) := by
  have E : T ≤ f ⁻¹ᵁ (𝒰.opens i ⊓ 𝒰.opens j ⊓ 𝒰.opens l) :=
    fun t ht ↦ ⟨e₁ ht, (e₂ ht).2⟩
  have ht := congrArg (f.unitsAppLE (𝒰.opens i ⊓ 𝒰.opens j ⊓ 𝒰.opens l) T E)
    (Scheme.unitsEvInf_trans γ i j l)
  rw [map_mul, Scheme.Hom.map_unitsAppLE, Scheme.Hom.map_unitsAppLE,
    Scheme.Hom.map_unitsAppLE] at ht
  exact ht

/-- The overlap telescope of the glued pieces. -/
private lemma glue_telescope {G : Type u} [CommGroup G] {bx by' Lxy Lxs Lys m : G}
    (hb : bx * Lxy = by') (hL : Lxy * Lys = Lxs) :
    bx⁻¹ * Lxs⁻¹ * m⁻¹ = by'⁻¹ * Lys⁻¹ * m⁻¹ := by
  subst hb; rw [← hL]
  simp only [mul_inv, inv_inv]
  simp only [mul_comm, mul_left_comm, mul_assoc]

/-- The coprojection-ratio telescope of the glued pieces. -/
private lemma ratio_telescope {G : Type u} [CommGroup G] {b₁ b₂ L M₁ M₂ P : G}
    (hb : P = b₁ / b₂) (hm : M₂ = P * M₁) :
    b₁⁻¹ * L⁻¹ * M₁⁻¹ = b₂⁻¹ * L⁻¹ * M₂⁻¹ := by
  subst hm; subst hb
  rw [mul_inv (b₁ / b₂) M₁, inv_div b₁ b₂, div_eq_mul_inv b₂ b₁,
    mul_assoc b₂ b₁⁻¹ M₁⁻¹,
    mul_assoc b₂⁻¹ L⁻¹ (b₂ * (b₁⁻¹ * M₁⁻¹)),
    mul_left_comm L⁻¹ b₂ (b₁⁻¹ * M₁⁻¹),
    ← mul_assoc b₂⁻¹ b₂ (L⁻¹ * (b₁⁻¹ * M₁⁻¹)),
    inv_mul_cancel b₂, one_mul, mul_left_comm L⁻¹ b₁⁻¹ M₁⁻¹, ← mul_assoc]

/-- Transport of a preimage bound along an equality of morphisms, point-indexed. -/
private lemma le_preimage_point_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (z : X) (V : Y → Y.Opens) {O : X.Opens} (hle : O ≤ f ⁻¹ᵁ V (f.base z)) :
    O ≤ g ⁻¹ᵁ V (g.base z) := by
  subst h; exact hle

/-- Transport of a preimage bound along an equality of morphisms, fixed open. -/
private lemma le_preimage_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    {O : X.Opens} {W : Y.Opens} (hle : O ≤ f ⁻¹ᵁ W) : O ≤ g ⁻¹ᵁ W := by
  subst h; exact hle

/-! ## The glued pieces -/

/-- The naturality square `cg ≫ p_A = p_B ≫ g_S`. -/
lemma cg_comp_pA :
    (cg) ≫ (pA) = (pB) ≫ (gS) :=
  Over.snd_left_naturality C (Over.overSpecMap ((Algebra.ofId A B).restrictScalars k))

/-- The `μ`-bound of the glued pieces. -/
lemma preimage_le_pB_gS (𝒞 : (SA).PointedCover) (s : XA) (U : (XA).Opens)
    (hUC : U ≤ (pA) ⁻¹ᵁ 𝒞.opens ((pA).base s)) :
    (cg) ⁻¹ᵁ U ≤ (pB) ⁻¹ᵁ ((gS) ⁻¹ᵁ 𝒞.opens ((pA).base s)) := by
  rw [← Scheme.Hom.comp_preimage, ← cg_comp_pA C, Scheme.Hom.comp_preimage]
  exact (cg).preimage_mono hUC

/-- The local unit of the glue at `x`: `β_x⁻¹ ⋅ (cg^♯ lam_{cg x, s})⁻¹ ⋅ (p_B^♯ μ)⁻¹`. -/
noncomputable def gluePiece (ℰ : (XA).PointedCover)
    (lam : (XA).unitsCocycle ℰ)
    (β : ∀ v : XB, Γ(XB, (ℰ.pullback (cg)).opens v)ˣ)
    (𝒞 : (SA).PointedCover) (μ : ∀ a : SA, Γ(SB, (gS) ⁻¹ᵁ 𝒞.opens a)ˣ)
    (s : XA) (x : XB) (T : (XB).Opens)
    (hT𝒜 : T ≤ (ℰ.pullback (cg)).opens x) (hTE : T ≤ (cg) ⁻¹ᵁ ℰ.opens s)
    (hTμ : T ≤ (pB) ⁻¹ᵁ ((gS) ⁻¹ᵁ 𝒞.opens ((pA).base s))) : Γ(XB, T)ˣ :=
  ((XB).unitsRestrict hT𝒜 (β x))⁻¹
    * ((cg).unitsAppLE (ℰ.opens ((cg).base x) ⊓ ℰ.opens s) T
        ((cg).le_preimage_inf hT𝒜 hTE)
        (Scheme.unitsEvInf lam ((cg).base x) s))⁻¹
    * ((pB).unitsAppLE ((gS) ⁻¹ᵁ 𝒞.opens ((pA).base s)) T hTμ (μ ((pA).base s)))⁻¹

/-- Restriction of a glued piece is the glued piece on the smaller open. -/
private lemma unitsRestrict_gluePiece (ℰ : (XA).PointedCover)
    (lam : (XA).unitsCocycle ℰ)
    (β : ∀ v : XB, Γ(XB, (ℰ.pullback (cg)).opens v)ˣ)
    (𝒞 : (SA).PointedCover) (μ : ∀ a : SA, Γ(SB, (gS) ⁻¹ᵁ 𝒞.opens a)ˣ)
    (s : XA) (x : XB) {T T' : (XB).Opens} (hsub : T' ≤ T)
    (hT𝒜 : T ≤ (ℰ.pullback (cg)).opens x) (hTE : T ≤ (cg) ⁻¹ᵁ ℰ.opens s)
    (hTμ : T ≤ (pB) ⁻¹ᵁ ((gS) ⁻¹ᵁ 𝒞.opens ((pA).base s))) :
    (XB).unitsRestrict hsub (gluePiece C ℰ lam β 𝒞 μ s x T hT𝒜 hTE hTμ)
      = gluePiece C ℰ lam β 𝒞 μ s x T' (hsub.trans hT𝒜) (hsub.trans hTE)
          (hsub.trans hTμ) := by
  simp only [gluePiece, map_mul, map_inv, Scheme.unitsRestrict_unitsRestrict,
    Scheme.Hom.unitsAppLE_map]

/-- The coboundary relation of `β`, restricted to an arbitrary sub-open. -/
private lemma hβ_restrict (ℰ : (XA).PointedCover) (lam : (XA).unitsCocycle ℰ)
    (β : ∀ v : XB, Γ(XB, (ℰ.pullback (cg)).opens v)ˣ)
    (hβ : ∀ v v' : XB,
      (XB).unitsRestrict
          (inf_le_left : (ℰ.pullback (cg)).opens v ⊓ (ℰ.pullback (cg)).opens v'
            ≤ (ℰ.pullback (cg)).opens v) (β v)
          * (cg).unitsAppLE (ℰ.opens ((cg).base v) ⊓ ℰ.opens ((cg).base v'))
              ((ℰ.pullback (cg)).opens v ⊓ (ℰ.pullback (cg)).opens v')
              ((cg).le_preimage_inf inf_le_left inf_le_right)
              (Scheme.unitsEvInf lam ((cg).base v) ((cg).base v'))
        = (XB).unitsRestrict inf_le_right (β v'))
    (x y : XB) (T : (XB).Opens)
    (hTx : T ≤ (ℰ.pullback (cg)).opens x) (hTy : T ≤ (ℰ.pullback (cg)).opens y) :
    (XB).unitsRestrict hTx (β x)
        * (cg).unitsAppLE (ℰ.opens ((cg).base x) ⊓ ℰ.opens ((cg).base y)) T
            ((cg).le_preimage_inf hTx hTy)
            (Scheme.unitsEvInf lam ((cg).base x) ((cg).base y))
      = (XB).unitsRestrict hTy (β y) := by
  have h := congrArg ((XB).unitsRestrict (le_inf hTx hTy)) (hβ x y)
  rw [map_mul, Scheme.unitsRestrict_unitsRestrict, Scheme.unitsRestrict_unitsRestrict,
    Scheme.Hom.unitsAppLE_map] at h
  exact h

/-- The glued pieces agree on overlaps. -/
private lemma gluePiece_compat (ℰ : (XA).PointedCover) (lam : (XA).unitsCocycle ℰ)
    (β : ∀ v : XB, Γ(XB, (ℰ.pullback (cg)).opens v)ˣ)
    (hβ : ∀ v v' : XB,
      (XB).unitsRestrict
          (inf_le_left : (ℰ.pullback (cg)).opens v ⊓ (ℰ.pullback (cg)).opens v'
            ≤ (ℰ.pullback (cg)).opens v) (β v)
          * (cg).unitsAppLE (ℰ.opens ((cg).base v) ⊓ ℰ.opens ((cg).base v'))
              ((ℰ.pullback (cg)).opens v ⊓ (ℰ.pullback (cg)).opens v')
              ((cg).le_preimage_inf inf_le_left inf_le_right)
              (Scheme.unitsEvInf lam ((cg).base v) ((cg).base v'))
        = (XB).unitsRestrict inf_le_right (β v'))
    (𝒞 : (SA).PointedCover) (μ : ∀ a : SA, Γ(SB, (gS) ⁻¹ᵁ 𝒞.opens a)ˣ)
    (s : XA) (x y : XB) (T : (XB).Opens)
    (hTx : T ≤ (ℰ.pullback (cg)).opens x) (hTy : T ≤ (ℰ.pullback (cg)).opens y)
    (hTE : T ≤ (cg) ⁻¹ᵁ ℰ.opens s)
    (hTμ : T ≤ (pB) ⁻¹ᵁ ((gS) ⁻¹ᵁ 𝒞.opens ((pA).base s))) :
    gluePiece C ℰ lam β 𝒞 μ s x T hTx hTE hTμ
      = gluePiece C ℰ lam β 𝒞 μ s y T hTy hTE hTμ := by
  refine glue_telescope (hβ_restrict C ℰ lam β hβ x y T hTx hTy) ?_
  exact pullback_pair_trans (cg) lam ((cg).base x) ((cg).base y) s
    ((cg).le_preimage_inf hTx hTy) ((cg).le_preimage_inf hTy hTE)
    ((cg).le_preimage_inf hTx hTE)

/-- The glue: a unit on `cg⁻¹U` restricting to the pieces. -/
private lemma exists_glued (ℰ : (XA).PointedCover) (lam : (XA).unitsCocycle ℰ)
    (β : ∀ v : XB, Γ(XB, (ℰ.pullback (cg)).opens v)ˣ)
    (hβ : ∀ v v' : XB,
      (XB).unitsRestrict
          (inf_le_left : (ℰ.pullback (cg)).opens v ⊓ (ℰ.pullback (cg)).opens v'
            ≤ (ℰ.pullback (cg)).opens v) (β v)
          * (cg).unitsAppLE (ℰ.opens ((cg).base v) ⊓ ℰ.opens ((cg).base v'))
              ((ℰ.pullback (cg)).opens v ⊓ (ℰ.pullback (cg)).opens v')
              ((cg).le_preimage_inf inf_le_left inf_le_right)
              (Scheme.unitsEvInf lam ((cg).base v) ((cg).base v'))
        = (XB).unitsRestrict inf_le_right (β v'))
    (𝒞 : (SA).PointedCover) (μ : ∀ a : SA, Γ(SB, (gS) ⁻¹ᵁ 𝒞.opens a)ˣ)
    (s : XA) (U : (XA).Opens) (hUE : U ≤ ℰ.opens s)
    (hUC : U ≤ (pA) ⁻¹ᵁ 𝒞.opens ((pA).base s)) :
    ∃ G : Γ(XB, (cg) ⁻¹ᵁ U)ˣ, ∀ (x : XB) (T : (XB).Opens)
      (hT𝒜 : T ≤ (ℰ.pullback (cg)).opens x) (hTU : T ≤ (cg) ⁻¹ᵁ U),
      (XB).unitsRestrict hTU G
        = gluePiece C ℰ lam β 𝒞 μ s x T hT𝒜 (hTU.trans ((cg).preimage_mono hUE))
            (hTU.trans (preimage_le_pB_gS C 𝒞 s U hUC)) := by
  obtain ⟨G, hG⟩ := Scheme.exists_unitsRestrict_eq
    (W := fun x : XB ↦ (ℰ.pullback (cg)).opens x ⊓ (cg) ⁻¹ᵁ U)
    (fun _ ↦ inf_le_right)
    (fun v hv ↦ TopologicalSpace.Opens.mem_iSup.mpr
      ⟨v, ⟨(ℰ.pullback (cg)).mem_opens v, hv⟩⟩)
    (fun x ↦ gluePiece C ℰ lam β 𝒞 μ s x ((ℰ.pullback (cg)).opens x ⊓ (cg) ⁻¹ᵁ U)
      inf_le_left (inf_le_right.trans ((cg).preimage_mono hUE))
      (inf_le_right.trans (preimage_le_pB_gS C 𝒞 s U hUC)))
    (fun x y ↦ by
      rw [unitsRestrict_gluePiece C ℰ lam β 𝒞 μ s x, unitsRestrict_gluePiece C ℰ lam β 𝒞 μ s y]
      exact gluePiece_compat C ℰ lam β hβ 𝒞 μ s x y _
        (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) _ _)
  refine ⟨G, fun x T hT𝒜 hTU ↦ ?_⟩
  have h := congrArg ((XB).unitsRestrict (le_inf hT𝒜 hTU)) (hG x)
  rw [Scheme.unitsRestrict_unitsRestrict,
    unitsRestrict_gluePiece C ℰ lam β 𝒞 μ s x] at h
  exact h

/-! ## The coprojection pullbacks of the glue -/

set_option maxHeartbeats 1600000 in
-- the concrete product towers exceed the default budget
/-- Normal form of a coprojection pullback of the glued unit, for either coprojection
`v` with `v ≫ cg = cg₂` and `v ≫ p_B = p₂ ≫ t`. -/
private lemma pullback_gluePiece (ℰ : (XA).PointedCover) (lam : (XA).unitsCocycle ℰ)
    (β : ∀ v : XB, Γ(XB, (ℰ.pullback (cg)).opens v)ˣ)
    (𝒞 : (SA).PointedCover) (μ : ∀ a : SA, Γ(SB, (gS) ⁻¹ᵁ 𝒞.opens a)ˣ)
    (s : XA) (U : (XA).Opens) (hUE : U ≤ ℰ.opens s)
    (hUC : U ≤ (pA) ⁻¹ᵁ 𝒞.opens ((pA).base s))
    (v : Xq ⟶ XB) (t : Sq ⟶ SB) (hvc : v ≫ (cg) = (cg₂))
    (hvp : v ≫ (pB) = (p₂) ≫ t)
    (G : Γ(XB, (cg) ⁻¹ᵁ U)ˣ)
    (hG : ∀ (x : XB) (T : (XB).Opens)
      (hT𝒜 : T ≤ (ℰ.pullback (cg)).opens x) (hTU : T ≤ (cg) ⁻¹ᵁ U),
      (XB).unitsRestrict hTU G
        = gluePiece C ℰ lam β 𝒞 μ s x T hT𝒜 (hTU.trans ((cg).preimage_mono hUE))
            (hTU.trans (preimage_le_pB_gS C 𝒞 s U hUC)))
    (z : Xq) (O : (Xq).Opens)
    (hO𝒜 : O ≤ v ⁻¹ᵁ (ℰ.pullback (cg)).opens (v.base z))
    (hOU : O ≤ v ⁻¹ᵁ ((cg) ⁻¹ᵁ U))
    (e₂ : O ≤ (cg₂) ⁻¹ᵁ (ℰ.opens ((cg₂).base z) ⊓ ℰ.opens s))
    (e₃ : O ≤ ((p₂) ≫ t) ⁻¹ᵁ ((gS) ⁻¹ᵁ 𝒞.opens ((pA).base s))) :
    v.unitsAppLE ((cg) ⁻¹ᵁ U) O hOU G
      = (v.unitsAppLE ((ℰ.pullback (cg)).opens (v.base z)) O hO𝒜 (β (v.base z)))⁻¹
        * ((cg₂).unitsAppLE (ℰ.opens ((cg₂).base z) ⊓ ℰ.opens s) O e₂
            (Scheme.unitsEvInf lam ((cg₂).base z) s))⁻¹
        * (((p₂) ≫ t).unitsAppLE ((gS) ⁻¹ᵁ 𝒞.opens ((pA).base s)) O e₃
            (μ ((pA).base s)))⁻¹ := by
  have h0 : v.unitsAppLE ((cg) ⁻¹ᵁ U) O hOU G
      = v.unitsAppLE ((ℰ.pullback (cg)).opens (v.base z) ⊓ (cg) ⁻¹ᵁ U) O
          (v.le_preimage_inf hO𝒜 hOU)
          ((XB).unitsRestrict
            (inf_le_right : (ℰ.pullback (cg)).opens (v.base z) ⊓ (cg) ⁻¹ᵁ U
              ≤ (cg) ⁻¹ᵁ U) G) :=
    (Scheme.Hom.map_unitsAppLE v _ _ _).symm
  refine h0.trans ?_
  refine (congrArg (v.unitsAppLE _ O (v.le_preimage_inf hO𝒜 hOU))
    (hG (v.base z) _ inf_le_left inf_le_right)).trans ?_
  refine (map_mul _ _ _).trans ?_
  refine congrArg₂ (· * ·) ((map_mul _ _ _).trans ?_) ((map_inv _ _).trans ?_)
  · refine congrArg₂ (· * ·) ((map_inv _ _).trans ?_) ((map_inv _ _).trans ?_)
    · exact congrArg (·⁻¹) (Scheme.Hom.map_unitsAppLE v _ _ _)
    · refine congrArg (·⁻¹) ?_
      refine (Scheme.unitsAppLE_unitsAppLE v (cg) _ _ _).trans ?_
      exact Scheme.Hom.unitsAppLE_section_congr_hom hvc
        (fun y => ℰ.opens y ⊓ ℰ.opens s) (fun y => Scheme.unitsEvInf lam y s) z _
  · refine congrArg (·⁻¹) ?_
    refine (Scheme.unitsAppLE_unitsAppLE v (pB) _ _ _).trans ?_
    exact unitsAppLE_congr_hom hvp _ _ _ (μ ((pA).base s))

set_option maxHeartbeats 1600000 in
-- the concrete product towers exceed the default budget
/-- **The glued unit has equal coprojection pullbacks**, by the local ratio form of the
descent unit and the `ratio` field of the Čech representative. -/
private lemma glued_pullbacks_eq (ℰ : (XA).PointedCover) (lam : (XA).unitsCocycle ℰ)
    (β : ∀ v : XB, Γ(XB, (ℰ.pullback (cg)).opens v)ˣ)
    (𝒞 : (SA).PointedCover) (μ : ∀ a : SA, Γ(SB, (gS) ⁻¹ᵁ 𝒞.opens a)ˣ)
    (w : Γ(Sq, ⊤)ˣ)
    (hwloc : ∀ z : Xq,
      (Xq).unitsRestrict
          (le_top : ((ℰ.pullback (cg)).pullback (u₁)
            ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z ≤ ⊤)
          (Units.map (p₂).appTop.hom.toMonoidHom w)
        = (u₁).unitsAppLE ((ℰ.pullback (cg)).opens ((u₁).base z))
            (((ℰ.pullback (cg)).pullback (u₁)
              ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z)
            inf_le_left (β ((u₁).base z))
          / (u₂).unitsAppLE ((ℰ.pullback (cg)).opens ((u₂).base z))
            (((ℰ.pullback (cg)).pullback (u₁)
              ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z)
            inf_le_right (β ((u₂).base z)))
    (hratio : ∀ (a : SA) (O : (Sq).Opens)
      (e₁ : O ≤ (q₁) ⁻¹ᵁ ((gS) ⁻¹ᵁ 𝒞.opens a))
      (e₂ : O ≤ (q₂) ⁻¹ᵁ ((gS) ⁻¹ᵁ 𝒞.opens a)),
      (q₂).unitsAppLE ((gS) ⁻¹ᵁ 𝒞.opens a) O e₂ (μ a)
        = (Sq).unitsRestrict (le_top : O ≤ ⊤) w
          * (q₁).unitsAppLE ((gS) ⁻¹ᵁ 𝒞.opens a) O e₁ (μ a))
    (s : XA) (U : (XA).Opens) (hUE : U ≤ ℰ.opens s)
    (hUC : U ≤ (pA) ⁻¹ᵁ 𝒞.opens ((pA).base s))
    (G : Γ(XB, (cg) ⁻¹ᵁ U)ˣ)
    (hG : ∀ (x : XB) (T : (XB).Opens)
      (hT𝒜 : T ≤ (ℰ.pullback (cg)).opens x) (hTU : T ≤ (cg) ⁻¹ᵁ U),
      (XB).unitsRestrict hTU G
        = gluePiece C ℰ lam β 𝒞 μ s x T hT𝒜 (hTU.trans ((cg).preimage_mono hUE))
            (hTU.trans (preimage_le_pB_gS C 𝒞 s U hUC))) :
    (u₁).unitsAppLE ((cg) ⁻¹ᵁ U) ((cg₂) ⁻¹ᵁ U) (cg₂_preimage_eq_inl C U).le G
      = (u₂).unitsAppLE ((cg) ⁻¹ᵁ U) ((cg₂) ⁻¹ᵁ U) (cg₂_preimage_eq_inr C U).le G := by
  refine Scheme.unitsRestrict_eq_of_locally_eq
    (W := fun z : Xq ↦ ((ℰ.pullback (cg)).pullback (u₁)
      ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z ⊓ (cg₂) ⁻¹ᵁ U)
    (fun _ ↦ inf_le_right)
    (fun z' hz' ↦ TopologicalSpace.Opens.mem_iSup.mpr
      ⟨z', ⟨((ℰ.pullback (cg)).pullback (u₁)
        ⊓ (ℰ.pullback (cg)).pullback (u₂)).mem_opens z', hz'⟩⟩)
    _ _ (fun z ↦ ?_)
  -- the piece and its bounds
  have hOU₁ : ((ℰ.pullback (cg)).pullback (u₁)
        ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z ⊓ (cg₂) ⁻¹ᵁ U
      ≤ (u₁) ⁻¹ᵁ ((cg) ⁻¹ᵁ U) :=
    inf_le_right.trans (cg₂_preimage_eq_inl C U).le
  have hOU₂ : ((ℰ.pullback (cg)).pullback (u₁)
        ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z ⊓ (cg₂) ⁻¹ᵁ U
      ≤ (u₂) ⁻¹ᵁ ((cg) ⁻¹ᵁ U) :=
    inf_le_right.trans (cg₂_preimage_eq_inr C U).le
  have e₂a : ((ℰ.pullback (cg)).pullback (u₁)
        ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z ⊓ (cg₂) ⁻¹ᵁ U
      ≤ (cg₂) ⁻¹ᵁ ℰ.opens ((cg₂).base z) := by
    have h1 : ((ℰ.pullback (cg)).pullback (u₁)
          ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z ⊓ (cg₂) ⁻¹ᵁ U
        ≤ ((u₁) ≫ (cg)) ⁻¹ᵁ ℰ.opens (((u₁) ≫ (cg)).base z) := by
      rw [Scheme.Hom.comp_preimage]
      exact inf_le_left.trans inf_le_left
    exact le_preimage_point_congr (Over.whiskerLeft_inl_comp_ofId C) z ℰ.opens h1
  have e₂ : ((ℰ.pullback (cg)).pullback (u₁)
        ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z ⊓ (cg₂) ⁻¹ᵁ U
      ≤ (cg₂) ⁻¹ᵁ (ℰ.opens ((cg₂).base z) ⊓ ℰ.opens s) :=
    (cg₂).le_preimage_inf e₂a (inf_le_right.trans ((cg₂).preimage_mono hUE))
  have e₃₁ : ((ℰ.pullback (cg)).pullback (u₁)
        ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z ⊓ (cg₂) ⁻¹ᵁ U
      ≤ ((p₂) ≫ (q₁)) ⁻¹ᵁ ((gS) ⁻¹ᵁ 𝒞.opens ((pA).base s)) := by
    have h1 : ((ℰ.pullback (cg)).pullback (u₁)
          ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z ⊓ (cg₂) ⁻¹ᵁ U
        ≤ ((u₁) ≫ (pB)) ⁻¹ᵁ ((gS) ⁻¹ᵁ 𝒞.opens ((pA).base s)) := by
      rw [Scheme.Hom.comp_preimage]
      exact hOU₁.trans ((u₁).preimage_mono (preimage_le_pB_gS C 𝒞 s U hUC))
    exact le_preimage_congr_hom (Over.snd_left_naturality C
      (Over.overSpecMap (tensorInl (A := A) (B := B)))) h1
  have e₃₂ : ((ℰ.pullback (cg)).pullback (u₁)
        ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z ⊓ (cg₂) ⁻¹ᵁ U
      ≤ ((p₂) ≫ (q₂)) ⁻¹ᵁ ((gS) ⁻¹ᵁ 𝒞.opens ((pA).base s)) := by
    have h1 : ((ℰ.pullback (cg)).pullback (u₁)
          ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z ⊓ (cg₂) ⁻¹ᵁ U
        ≤ ((u₂) ≫ (pB)) ⁻¹ᵁ ((gS) ⁻¹ᵁ 𝒞.opens ((pA).base s)) := by
      rw [Scheme.Hom.comp_preimage]
      exact hOU₂.trans ((u₂).preimage_mono (preimage_le_pB_gS C 𝒞 s U hUC))
    exact le_preimage_congr_hom (Over.snd_left_naturality C
      (Over.overSpecMap (tensorInr (A := A) (B := B)))) h1
  -- the coboundary ratio of `β`, restricted
  have hw := congrArg ((Xq).unitsRestrict
    (inf_le_left : ((ℰ.pullback (cg)).pullback (u₁)
      ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z ⊓ (cg₂) ⁻¹ᵁ U
      ≤ ((ℰ.pullback (cg)).pullback (u₁)
        ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z)) (hwloc z)
  rw [Scheme.unitsRestrict_unitsRestrict, map_div, Scheme.Hom.unitsAppLE_map,
    Scheme.Hom.unitsAppLE_map] at hw
  -- the `μ`-ratio, pulled to the product
  have hr := congrArg ((p₂).unitsAppLE
    ((q₁) ⁻¹ᵁ ((gS) ⁻¹ᵁ 𝒞.opens ((pA).base s))
      ⊓ (q₂) ⁻¹ᵁ ((gS) ⁻¹ᵁ 𝒞.opens ((pA).base s)))
    (((ℰ.pullback (cg)).pullback (u₁)
      ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z ⊓ (cg₂) ⁻¹ᵁ U)
    ((p₂).le_preimage_inf
      (by rw [← Scheme.Hom.comp_preimage]; exact e₃₁)
      (by rw [← Scheme.Hom.comp_preimage]; exact e₃₂)))
    (hratio ((pA).base s) _ inf_le_left inf_le_right)
  rw [map_mul, Scheme.unitsAppLE_unitsAppLE, Scheme.unitsAppLE_unitsAppLE,
    Scheme.Hom.unitsAppLE_unitsRestrict_top] at hr
  -- assemble
  rw [Scheme.Hom.unitsAppLE_map, Scheme.Hom.unitsAppLE_map]
  refine (pullback_gluePiece C ℰ lam β 𝒞 μ s U hUE hUC (u₁) (q₁)
    (Over.whiskerLeft_inl_comp_ofId C)
    (Over.snd_left_naturality C (Over.overSpecMap (tensorInl (A := A) (B := B))))
    G hG z _ (inf_le_left.trans inf_le_left) hOU₁ e₂ e₃₁).trans ?_
  refine (ratio_telescope hw hr).trans ?_
  exact (pullback_gluePiece C ℰ lam β 𝒞 μ s U hUE hUC (u₂) (q₂)
    (Over.whiskerLeft_inr_comp_ofId C)
    (Over.snd_left_naturality C (Over.overSpecMap (tensorInr (A := A) (B := B))))
    G hG z _ (inf_le_left.trans inf_le_right) hOU₂ e₂ e₃₂).symm

set_option maxHeartbeats 1600000 in
-- the concrete product towers exceed the default budget
/-- **The cobounding unit of the kernel lemma at an affine chart** (ζ3 brick G): the
glued `β`-`lam`-`μ` unit descends through `cg` to a unit `c` on `U`, whose `cg`-pullback
has the glued local form on every sub-open of a member of the pulled-back cover. -/
theorem exists_kernelCobounding [Module.FaithfullyFlat A B]
    (ℰ : (XA).PointedCover) (lam : (XA).unitsCocycle ℰ)
    (β : ∀ v : XB, Γ(XB, (ℰ.pullback (cg)).opens v)ˣ)
    (hβ : ∀ v v' : XB,
      (XB).unitsRestrict
          (inf_le_left : (ℰ.pullback (cg)).opens v ⊓ (ℰ.pullback (cg)).opens v'
            ≤ (ℰ.pullback (cg)).opens v) (β v)
          * (cg).unitsAppLE (ℰ.opens ((cg).base v) ⊓ ℰ.opens ((cg).base v'))
              ((ℰ.pullback (cg)).opens v ⊓ (ℰ.pullback (cg)).opens v')
              ((cg).le_preimage_inf inf_le_left inf_le_right)
              (Scheme.unitsEvInf lam ((cg).base v) ((cg).base v'))
        = (XB).unitsRestrict inf_le_right (β v'))
    (𝒞 : (SA).PointedCover) (μ : ∀ a : SA, Γ(SB, (gS) ⁻¹ᵁ 𝒞.opens a)ˣ)
    (w : Γ(Sq, ⊤)ˣ)
    (hwloc : ∀ z : Xq,
      (Xq).unitsRestrict
          (le_top : ((ℰ.pullback (cg)).pullback (u₁)
            ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z ≤ ⊤)
          (Units.map (p₂).appTop.hom.toMonoidHom w)
        = (u₁).unitsAppLE ((ℰ.pullback (cg)).opens ((u₁).base z))
            (((ℰ.pullback (cg)).pullback (u₁)
              ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z)
            inf_le_left (β ((u₁).base z))
          / (u₂).unitsAppLE ((ℰ.pullback (cg)).opens ((u₂).base z))
            (((ℰ.pullback (cg)).pullback (u₁)
              ⊓ (ℰ.pullback (cg)).pullback (u₂)).opens z)
            inf_le_right (β ((u₂).base z)))
    (hratio : ∀ (a : SA) (O : (Sq).Opens)
      (e₁ : O ≤ (q₁) ⁻¹ᵁ ((gS) ⁻¹ᵁ 𝒞.opens a))
      (e₂ : O ≤ (q₂) ⁻¹ᵁ ((gS) ⁻¹ᵁ 𝒞.opens a)),
      (q₂).unitsAppLE ((gS) ⁻¹ᵁ 𝒞.opens a) O e₂ (μ a)
        = (Sq).unitsRestrict (le_top : O ≤ ⊤) w
          * (q₁).unitsAppLE ((gS) ⁻¹ᵁ 𝒞.opens a) O e₁ (μ a))
    (s : XA) (U : (XA).Opens) (hUaff : IsAffineOpen U) (hUE : U ≤ ℰ.opens s)
    (hUC : U ≤ (pA) ⁻¹ᵁ 𝒞.opens ((pA).base s)) :
    ∃ c : Γ(XA, U)ˣ, ∀ (x : XB) (T : (XB).Opens)
      (hT𝒜 : T ≤ (ℰ.pullback (cg)).opens x) (hTU : T ≤ (cg) ⁻¹ᵁ U),
      (cg).unitsAppLE U T (hTU.trans (le_of_eq rfl)) c
        = gluePiece C ℰ lam β 𝒞 μ s x T hT𝒜 (hTU.trans ((cg).preimage_mono hUE))
            (hTU.trans (preimage_le_pB_gS C 𝒞 s U hUC)) := by
  obtain ⟨G, hG⟩ := exists_glued C ℰ lam β hβ 𝒞 μ s U hUE hUC
  obtain ⟨c, hc⟩ := exists_unitsAppLE_eq (C := C) hUaff G
    (glued_pullbacks_eq C ℰ lam β 𝒞 μ w hwloc hratio s U hUE hUC G hG)
  refine ⟨c, fun x T hT𝒜 hTU ↦ ?_⟩
  have h := congrArg ((XB).unitsRestrict hTU) hc
  rw [Scheme.Hom.unitsAppLE_map] at h
  exact h.trans (hG x T hT𝒜 hTU)

end Over

end AlgebraicGeometry
