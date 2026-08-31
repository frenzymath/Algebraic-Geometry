/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RelativeTwoCover
import AlgebraicJacobian.Cohomology.AffineVanishingQcoh

/-!
# The cocycle-glued twisted sheaf on a two-cover

For a scheme `X` over `Spec k`, opens `V₀, V₁` and a **unit cocycle**
`g ∈ Γ(X, V₀ ⊓ V₁)ˣ`, the twisted sheaf `F_g` of design §6.1, as a sheaf of `k`-modules
on the small Zariski site of `X`:
`F_g(W) = {(s₀, s₁) ∈ Γ(W ⊓ V₀) × Γ(W ⊓ V₁) | s₀ = g · s₁ on W ⊓ V₀ ⊓ V₁}`
(`AlgebraicGeometry.twistSheaf`), together with

* its **chart trivializations** `F_g(W) ≃ₗ[k] Γ(X, W)` for `W ≤ V₀` (resp. `W ≤ V₁`),
  given by the first (resp. second) component (`AlgebraicGeometry.twistTriv₀/₁`),
  commuting with restriction (`twistTriv₀_res`, `twistTriv₁_res`);
* the **quasi-coherence packaging** `Scheme.QcohOn (twistSheaf k V₀ V₁ g) Vᵢ` on each
  chart, transported from the structure sheaf along the trivialization by the general
  transport `AlgebraicGeometry.Scheme.QcohOn.ofSectionsEquiv`;
* hence the **twisted affine vanishing** `Subsingleton (Sheaf.HModule' _ Vᵢ 1)` for
  affine `Vᵢ` (`subsingleton_hModule'_twistSheaf_one₀/₁`) and the **two-cover H¹ carrier
  firing on `F_g`** (`AlgebraicGeometry.twistTwoCoverH1` — CBC-0 for a
  two-cover-presented twisted line bundle);
* the instantiation on the **relative curve** over a test ring `R` with the base-changed
  affine two-cover `relCover C R D` (`AlgebraicGeometry.relTwistTwoCoverH1`), and the
  pullback `AlgebraicGeometry.relUnitCocycle` of a curve-level unit cocycle (e.g. the
  fiber-twist cocycle `t₀ⁿ` of `AlgebraicJacobian.RiemannRoch.FiberTwist`).

## Implementation notes

Sections of `F_g` are the kernel of the `k`-linear *defect map*
`(s₀, s₁) ↦ s₀|_{W ⊓ V₀ ⊓ V₁} - g·s₁|_{W ⊓ V₀ ⊓ V₁}` (`AlgebraicGeometry.twistDefect`),
so the carrier is a genuine submodule of a product of section modules and every element
computation is `Scheme.resHom` bookkeeping. The sheaf condition is the unique-gluing
criterion: both components glue in the structure sheaf of `k`-modules and the matching
relation is local. The `k`-module structure on section modules is `Scheme.overModule`,
activated locally per the house rule; the ring `k` is an explicit argument throughout
(it is not determined by the cocycle datum).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-! ## Transport of the quasi-coherence packaging along sections-level equivalences -/

section Transport

variable {k : Type u} [CommRing k] {X : Scheme.{u}}
variable {F G : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} k)}
variable {U : X.Opens}

/-- **Transport of the quasi-coherence packaging along a sections-level trivialization.**
If `F` and `G` have `k`-linearly equivalent sections over every open `W ≤ U`, compatibly
with restriction, then the packaging `Scheme.QcohOn G U` transports to `F`: the action
and both localization axioms are conjugated through the equivalences. This is the
mechanism by which a sheaf trivialized on a chart `U` (`F|_U ≅ 𝒪|_U` at sections level)
inherits the structure sheaf's packaging, hence Serre's affine `H¹`-vanishing, on `U`. -/
@[reducible] noncomputable def Scheme.QcohOn.ofSectionsEquiv [Scheme.QcohOn G U]
    (e : ∀ {W : X.Opens}, W ≤ U → (F.obj.obj (op W) ≃ₗ[k] G.obj.obj (op W)))
    (he : ∀ {W' W : X.Opens} (h : W' ≤ W) (hWU : W ≤ U) (m : F.obj.obj (op W)),
      e (h.trans hWU) (secRes F h m) = secRes G h (e hWU m)) :
    Scheme.QcohOn F U where
  qsmul {W} hWU r m := (e hWU).symm (Scheme.QcohOn.qsmul hWU r (e hWU m))
  one_qsmul {W} hWU m := by
    rw [Scheme.QcohOn.one_qsmul, LinearEquiv.symm_apply_apply]
  mul_qsmul {W} hWU r s m := by
    rw [Scheme.QcohOn.mul_qsmul, LinearEquiv.apply_symm_apply]
  add_qsmul {W} hWU r s m := by
    rw [Scheme.QcohOn.add_qsmul, map_add]
  qsmul_add {W} hWU r m n := by
    rw [map_add, Scheme.QcohOn.qsmul_add, map_add]
  secRes_qsmul {V W} hVW hWU r m := by
    apply (e (hVW.trans hWU)).injective
    rw [he hVW hWU, LinearEquiv.apply_symm_apply, Scheme.QcohOn.secRes_qsmul,
      LinearEquiv.apply_symm_apply, he hVW hWU]
  exists_secRes_eq_qsmul_pow {V} hV hVU g c := by
    obtain ⟨N, t, ht⟩ := Scheme.QcohOn.exists_secRes_eq_qsmul_pow (U := U) hV hVU g
      (e (inf_le_left.trans hVU) c)
    refine ⟨N, (e hVU).symm t, ?_⟩
    apply (e (inf_le_left.trans hVU)).injective
    rw [he inf_le_left hVU, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact ht
  exists_qsmul_pow_eq_zero {V} hV hVU g t ht := by
    obtain ⟨M, hM⟩ := Scheme.QcohOn.exists_qsmul_pow_eq_zero (U := U) hV hVU g (e hVU t)
      (by rw [← he inf_le_left hVU, ht, map_zero])
    exact ⟨M, by rw [hM, map_zero]⟩

end Transport

/-! ## The twisted sheaf -/

section Incl

variable {X : Scheme.{u}} (V₀ V₁ : X.Opens)

/-- The overlap `W ⊓ V₀ ⊓ V₁` is contained in the second piece `W ⊓ V₁`. -/
private lemma inclSnd (W : X.Opens) : W ⊓ V₀ ⊓ V₁ ≤ W ⊓ V₁ :=
  le_inf (inf_le_left.trans inf_le_left) inf_le_right

/-- The overlap `W ⊓ V₀ ⊓ V₁` is contained in the cocycle's home `V₀ ⊓ V₁`. -/
private lemma inclCoc (W : X.Opens) : W ⊓ V₀ ⊓ V₁ ≤ V₀ ⊓ V₁ :=
  le_inf (inf_le_left.trans inf_le_right) inf_le_right

end Incl

section TwistSheaf

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

attribute [local instance] Scheme.overModule

/-- Restriction of scheme sections commutes with the `Scheme.overModule` action. -/
private lemma resHom_smul {U V : X.Opens} (h : V ≤ U) (r : k) (s : Γ(X, U)) :
    X.resHom h (r • s) = r • X.resHom h s := by
  rw [Scheme.overModule_smul_def, map_mul, Scheme.overModule_smul_def]
  congr 1
  exact X.overAlgebraMap_apply_res k (homOfLE h).op r

/-- Multiplication by a fixed section, as a `k`-linear endomorphism of a section module
(with the `Scheme.overModule` structure). -/
private noncomputable def smulSection {U : X.Opens} (c : Γ(X, U)) :
    Γ(X, U) →ₗ[k] Γ(X, U) where
  toFun s := c * s
  map_add' := mul_add c
  map_smul' r s := by
    simp only [RingHom.id_apply, Scheme.overModule_smul_def, mul_left_comm]

variable (V₀ V₁ : X.Opens) (g : Γ(X, V₀ ⊓ V₁)ˣ)

/-- The **defect map** of the cocycle `g` over `W`: the `k`-linear map
`(s₀, s₁) ↦ s₀|_{W ⊓ V₀ ⊓ V₁} - g·s₁|_{W ⊓ V₀ ⊓ V₁}` whose kernel is the module of
twisted sections. -/
noncomputable def twistDefect (W : X.Opens) :
    (Γ(X, W ⊓ V₀) × Γ(X, W ⊓ V₁)) →ₗ[k] Γ(X, W ⊓ V₀ ⊓ V₁) :=
  (secRes (X.moduleKSheaf k) (inf_le_left : W ⊓ V₀ ⊓ V₁ ≤ W ⊓ V₀)).comp
      (LinearMap.fst k _ _) -
    (smulSection k (X.resHom (inclCoc V₀ V₁ W) ↑g)).comp
      ((secRes (X.moduleKSheaf k) (inclSnd V₀ V₁ W)).comp (LinearMap.snd k _ _))

lemma twistDefect_apply (W : X.Opens) (p : Γ(X, W ⊓ V₀) × Γ(X, W ⊓ V₁)) :
    twistDefect k V₀ V₁ g W p =
      X.resHom inf_le_left p.1 -
        X.resHom (inclCoc V₀ V₁ W) ↑g * X.resHom (inclSnd V₀ V₁ W) p.2 := rfl

/-- The module of **twisted sections** over `W`: pairs `(s₀, s₁)` of sections on
`W ⊓ V₀`, `W ⊓ V₁` matching through the cocycle `g` on the overlap `W ⊓ V₀ ⊓ V₁`. -/
noncomputable def twistSubmodule (W : X.Opens) :
    Submodule k (Γ(X, W ⊓ V₀) × Γ(X, W ⊓ V₁)) :=
  LinearMap.ker (twistDefect k V₀ V₁ g W)

lemma mem_twistSubmodule_iff {W : X.Opens} (p : Γ(X, W ⊓ V₀) × Γ(X, W ⊓ V₁)) :
    p ∈ twistSubmodule k V₀ V₁ g W ↔
      X.resHom inf_le_left p.1 =
        X.resHom (inclCoc V₀ V₁ W) ↑g * X.resHom (inclSnd V₀ V₁ W) p.2 := by
  rw [twistSubmodule, LinearMap.mem_ker, twistDefect_apply, sub_eq_zero]

/-- The twisted matching relation is stable under componentwise restriction. -/
lemma twistSubmodule_res {W' W : X.Opens} (h : W' ≤ W)
    {p : Γ(X, W ⊓ V₀) × Γ(X, W ⊓ V₁)} (hp : p ∈ twistSubmodule k V₀ V₁ g W) :
    (X.resHom (inf_le_inf_right V₀ h) p.1, X.resHom (inf_le_inf_right V₁ h) p.2) ∈
      twistSubmodule k V₀ V₁ g W' := by
  rw [mem_twistSubmodule_iff] at hp ⊢
  have key := congrArg
    (X.resHom (inf_le_inf_right V₁ (inf_le_inf_right V₀ h) :
      W' ⊓ V₀ ⊓ V₁ ≤ W ⊓ V₀ ⊓ V₁)) hp
  rw [map_mul] at key
  simp only [Scheme.resHom_resHom] at key ⊢
  exact key

/-- Componentwise restriction of twisted sections, as a `k`-linear map. -/
noncomputable def twistRes {W' W : X.Opens} (h : W' ≤ W) :
    ↥(twistSubmodule k V₀ V₁ g W) →ₗ[k] ↥(twistSubmodule k V₀ V₁ g W') :=
  LinearMap.restrict
    (LinearMap.prodMap (secRes (X.moduleKSheaf k) (inf_le_inf_right V₀ h))
      (secRes (X.moduleKSheaf k) (inf_le_inf_right V₁ h)))
    (fun _ hp ↦ twistSubmodule_res k V₀ V₁ g h hp)

@[simp]
lemma twistRes_coe_fst {W' W : X.Opens} (h : W' ≤ W)
    (p : ↥(twistSubmodule k V₀ V₁ g W)) :
    (twistRes k V₀ V₁ g h p).val.1 = X.resHom (inf_le_inf_right V₀ h) p.val.1 :=
  rfl

@[simp]
lemma twistRes_coe_snd {W' W : X.Opens} (h : W' ≤ W)
    (p : ↥(twistSubmodule k V₀ V₁ g W)) :
    (twistRes k V₀ V₁ g h p).val.2 = X.resHom (inf_le_inf_right V₁ h) p.val.2 :=
  rfl

/-- The presheaf of twisted sections of the cocycle `g` on the two-cover `V₀, V₁`. -/
noncomputable def twistPresheaf : X.Opensᵒᵖ ⥤ ModuleCat.{u} k where
  obj W := ModuleCat.of k ↥(twistSubmodule k V₀ V₁ g W.unop)
  map {A B} i := ModuleCat.ofHom (twistRes k V₀ V₁ g i.unop.le)
  map_id A := by
    ext p <;> exact Scheme.resHom_self _ _
  map_comp {A B D} i j := by
    ext p <;> exact (Scheme.resHom_resHom _ _ _).symm

/-- **The twisted sections form a sheaf.** Both components glue in the structure sheaf
over the covers `{Wᵢ ⊓ V₀}`, `{Wᵢ ⊓ V₁}`, and the matching relation is local. -/
theorem isSheaf_twistPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology (X : TopCat))
      (twistPresheaf k V₀ V₁ g) := by
  have h : TopCat.Presheaf.IsSheaf (C := ModuleCat.{u} k) (X := (X : TopCat))
      (twistPresheaf k V₀ V₁ g) := by
    rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
    intro ι U sf hsf
    -- the compatibility hypothesis, in `twistRes` form
    have hres : ∀ i j : ι,
        twistRes k V₀ V₁ g (inf_le_left : U i ⊓ U j ≤ U i) (sf i) =
          twistRes k V₀ V₁ g (inf_le_right : U i ⊓ U j ≤ U j) (sf j) := fun i j ↦ hsf i j
    -- glue the two components in the structure sheaf of `k`-modules
    have hcov₀ : (iSup U) ⊓ V₀ ≤ ⨆ i, U i ⊓ V₀ := by rw [iSup_inf_eq]
    have hcov₁ : (iSup U) ⊓ V₁ ≤ ⨆ i, U i ⊓ V₁ := by rw [iSup_inf_eq]
    have hcompat₀ : TopCat.Presheaf.IsCompatible (X.moduleKSheaf k).obj
        (fun i ↦ U i ⊓ V₀) (fun i ↦ (sf i).val.1) := by
      intro i j
      have key := congrArg (fun q : ↥(twistSubmodule k V₀ V₁ g (U i ⊓ U j)) ↦
        X.resHom (le_inf
          (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
          (inf_le_left.trans inf_le_right) :
            (U i ⊓ V₀) ⊓ (U j ⊓ V₀) ≤ (U i ⊓ U j) ⊓ V₀) q.val.1) (hres i j)
      simp only [twistRes_coe_fst, Scheme.resHom_resHom] at key
      exact key
    have hcompat₁ : TopCat.Presheaf.IsCompatible (X.moduleKSheaf k).obj
        (fun i ↦ U i ⊓ V₁) (fun i ↦ (sf i).val.2) := by
      intro i j
      have key := congrArg (fun q : ↥(twistSubmodule k V₀ V₁ g (U i ⊓ U j)) ↦
        X.resHom (le_inf
          (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
          (inf_le_left.trans inf_le_right) :
            (U i ⊓ V₁) ⊓ (U j ⊓ V₁) ≤ (U i ⊓ U j) ⊓ V₁) q.val.2) (hres i j)
      simp only [twistRes_coe_snd, Scheme.resHom_resHom] at key
      exact key
    obtain ⟨t₀, ht₀, ht₀u⟩ := TopCat.Sheaf.existsUnique_gluing'
      (X := (X : TopCat)) (C := ModuleCat.{u} k) (X.moduleKSheaf k)
      (fun i ↦ U i ⊓ V₀) ((iSup U) ⊓ V₀)
      (fun i ↦ homOfLE (inf_le_inf_right V₀ (le_iSup U i))) hcov₀
      (fun i ↦ (sf i).val.1) hcompat₀
    obtain ⟨t₁, ht₁, ht₁u⟩ := TopCat.Sheaf.existsUnique_gluing'
      (X := (X : TopCat)) (C := ModuleCat.{u} k) (X.moduleKSheaf k)
      (fun i ↦ U i ⊓ V₁) ((iSup U) ⊓ V₁)
      (fun i ↦ homOfLE (inf_le_inf_right V₁ (le_iSup U i))) hcov₁
      (fun i ↦ (sf i).val.2) hcompat₁
    have ht₀' : ∀ i, X.resHom (inf_le_inf_right V₀ (le_iSup U i)) t₀ = (sf i).val.1 :=
      fun i ↦ ht₀ i
    have ht₁' : ∀ i, X.resHom (inf_le_inf_right V₁ (le_iSup U i)) t₁ = (sf i).val.2 :=
      fun i ↦ ht₁ i
    -- the glued components match through the cocycle: check locally
    have hrel : (t₀, t₁) ∈ twistSubmodule k V₀ V₁ g (iSup U) := by
      refine (mem_twistSubmodule_iff k V₀ V₁ g
        ((t₀, t₁) : Γ(X, iSup U ⊓ V₀) × Γ(X, iSup U ⊓ V₁))).mpr ?_
      have hcovΩ : (iSup U) ⊓ V₀ ⊓ V₁ ≤ ⨆ i, U i ⊓ V₀ ⊓ V₁ := by
        rw [iSup_inf_eq, iSup_inf_eq]
      apply TopCat.Sheaf.eq_of_locally_eq' (X := (X : TopCat)) (C := ModuleCat.{u} k)
        (X.moduleKSheaf k) (fun i ↦ U i ⊓ V₀ ⊓ V₁) ((iSup U) ⊓ V₀ ⊓ V₁)
        (fun i ↦ homOfLE
          (inf_le_inf_right V₁ (inf_le_inf_right V₀ (le_iSup U i)))) hcovΩ
      intro i
      change X.resHom (inf_le_inf_right V₁ (inf_le_inf_right V₀ (le_iSup U i)))
          (X.resHom inf_le_left t₀) =
        X.resHom (inf_le_inf_right V₁ (inf_le_inf_right V₀ (le_iSup U i)))
          (X.resHom (inclCoc V₀ V₁ (iSup U)) ↑g *
            X.resHom (inclSnd V₀ V₁ (iSup U)) t₁)
      have hloc := (mem_twistSubmodule_iff k V₀ V₁ g
        ((sf i).val : Γ(X, U i ⊓ V₀) × Γ(X, U i ⊓ V₁))).mp (sf i).property
      have h₀i := congrArg
        (X.resHom (inf_le_left : U i ⊓ V₀ ⊓ V₁ ≤ U i ⊓ V₀)) (ht₀' i)
      have h₁i := congrArg (X.resHom (inclSnd V₀ V₁ (U i))) (ht₁' i)
      rw [map_mul]
      simp only [Scheme.resHom_resHom] at h₀i h₁i hloc ⊢
      rw [← h₀i, ← h₁i] at hloc
      exact hloc
    -- assemble the gluing and prove existence and uniqueness
    refine ⟨⟨(t₀, t₁), hrel⟩, fun i ↦ ?_, fun s hs ↦ ?_⟩
    · exact Subtype.ext (Prod.ext (ht₀' i) (ht₁' i))
    · have hs' : ∀ i, twistRes k V₀ V₁ g (le_iSup U i) s = sf i := fun i ↦ hs i
      refine Subtype.ext (Prod.ext ?_ ?_)
      · refine ht₀u s.val.1 fun i ↦ ?_
        change X.resHom (inf_le_inf_right V₀ (le_iSup U i)) s.val.1 = (sf i).val.1
        rw [← hs' i, twistRes_coe_fst]
      · refine ht₁u s.val.2 fun i ↦ ?_
        change X.resHom (inf_le_inf_right V₁ (le_iSup U i)) s.val.2 = (sf i).val.2
        rw [← hs' i, twistRes_coe_snd]
  exact h

/-- **The twisted sheaf `F_g`** of a unit cocycle `g ∈ Γ(X, V₀ ⊓ V₁)ˣ` on the two-cover
`V₀, V₁`: the sheaf of `k`-modules on the small Zariski site of `X` whose sections over
`W` are the pairs `(s₀, s₁) ∈ Γ(W ⊓ V₀) × Γ(W ⊓ V₁)` with `s₀ = g · s₁` on
`W ⊓ V₀ ⊓ V₁`. For `V₀ ⊔ V₁ = ⊤` this is a line bundle presented by the transition
cocycle `g`, trivialized on each chart by construction (`twistTriv₀`, `twistTriv₁`). -/
noncomputable def twistSheaf :
    Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} k) :=
  ⟨twistPresheaf k V₀ V₁ g, isSheaf_twistPresheaf k V₀ V₁ g⟩

@[simp]
lemma twistSheaf_obj (W : X.Opens) :
    (twistSheaf k V₀ V₁ g).obj.obj (op W) =
      ModuleCat.of k ↥(twistSubmodule k V₀ V₁ g W) := rfl

lemma secRes_twistSheaf {W' W : X.Opens} (h : W' ≤ W)
    (p : ↥(twistSubmodule k V₀ V₁ g W)) :
    secRes (twistSheaf k V₀ V₁ g) h p = twistRes k V₀ V₁ g h p := rfl

/-! ## The chart trivializations -/

/-- **Chart trivialization on the first chart**: over `W ≤ V₀`, the first component is
a `k`-linear equivalence `F_g(W) ≃ₗ[k] Γ(X, W)` (the inverse rebuilds the second
component through `g⁻¹`). -/
noncomputable def twistTriv₀ {W : X.Opens} (hW : W ≤ V₀) :
    ↥(twistSubmodule k V₀ V₁ g W) ≃ₗ[k] Γ(X, W) where
  toFun p := X.resHom (le_inf le_rfl hW) p.val.1
  map_add' p q := map_add _ _ _
  map_smul' r p := resHom_smul k _ r _
  invFun s := ⟨(X.resHom inf_le_left s,
    X.resHom (le_inf (inf_le_left.trans hW) inf_le_right : W ⊓ V₁ ≤ V₀ ⊓ V₁) ↑g⁻¹ *
      X.resHom inf_le_left s), by
    rw [mem_twistSubmodule_iff, map_mul]
    simp only [Scheme.resHom_resHom]
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]⟩
  left_inv p := by
    have hloc := (mem_twistSubmodule_iff k V₀ V₁ g
      (p.val : Γ(X, W ⊓ V₀) × Γ(X, W ⊓ V₁))).mp p.property
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change X.resHom inf_le_left (X.resHom (le_inf le_rfl hW) p.val.1) = p.val.1
      rw [Scheme.resHom_resHom, Scheme.resHom_self]
    · change X.resHom (le_inf (inf_le_left.trans hW) inf_le_right) ↑g⁻¹ *
          X.resHom inf_le_left (X.resHom (le_inf le_rfl hW) p.val.1) = p.val.2
      have key := congrArg
        (X.resHom (le_inf (le_inf inf_le_left (inf_le_left.trans hW)) inf_le_right :
          W ⊓ V₁ ≤ W ⊓ V₀ ⊓ V₁)) hloc
      rw [map_mul] at key
      simp only [Scheme.resHom_resHom] at key
      rw [Scheme.resHom_self] at key
      rw [Scheme.resHom_resHom, key, ← mul_assoc, ← map_mul, Units.inv_mul, map_one,
        one_mul]
  right_inv s := by
    change X.resHom (le_inf le_rfl hW) (X.resHom inf_le_left s) = s
    rw [Scheme.resHom_resHom, Scheme.resHom_self]

lemma twistTriv₀_apply {W : X.Opens} (hW : W ≤ V₀)
    (p : ↥(twistSubmodule k V₀ V₁ g W)) :
    twistTriv₀ k V₀ V₁ g hW p = X.resHom (le_inf le_rfl hW) p.val.1 :=
  rfl

/-- The first-chart trivialization commutes with restriction. -/
lemma twistTriv₀_res {W' W : X.Opens} (h : W' ≤ W) (hW : W ≤ V₀)
    (p : ↥(twistSubmodule k V₀ V₁ g W)) :
    twistTriv₀ k V₀ V₁ g (h.trans hW) (twistRes k V₀ V₁ g h p) =
      X.resHom h (twistTriv₀ k V₀ V₁ g hW p) := by
  rw [twistTriv₀_apply, twistTriv₀_apply, twistRes_coe_fst]
  simp only [Scheme.resHom_resHom]

/-- **Chart trivialization on the second chart**: over `W ≤ V₁`, the second component
is a `k`-linear equivalence `F_g(W) ≃ₗ[k] Γ(X, W)` (the inverse rebuilds the first
component through `g`). -/
noncomputable def twistTriv₁ {W : X.Opens} (hW : W ≤ V₁) :
    ↥(twistSubmodule k V₀ V₁ g W) ≃ₗ[k] Γ(X, W) where
  toFun p := X.resHom (le_inf le_rfl hW) p.val.2
  map_add' p q := map_add _ _ _
  map_smul' r p := resHom_smul k _ r _
  invFun s := ⟨(X.resHom (le_inf inf_le_right (inf_le_left.trans hW) : W ⊓ V₀ ≤ V₀ ⊓ V₁)
      ↑g * X.resHom inf_le_left s,
    X.resHom inf_le_left s), by
    rw [mem_twistSubmodule_iff, map_mul]
    simp only [Scheme.resHom_resHom]⟩
  left_inv p := by
    have hloc := (mem_twistSubmodule_iff k V₀ V₁ g
      (p.val : Γ(X, W ⊓ V₀) × Γ(X, W ⊓ V₁))).mp p.property
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change X.resHom (le_inf inf_le_right (inf_le_left.trans hW)) ↑g *
          X.resHom inf_le_left (X.resHom (le_inf le_rfl hW) p.val.2) = p.val.1
      have key := congrArg
        (X.resHom (le_inf le_rfl (inf_le_left.trans hW) :
          W ⊓ V₀ ≤ W ⊓ V₀ ⊓ V₁)) hloc
      rw [map_mul] at key
      simp only [Scheme.resHom_resHom] at key
      rw [Scheme.resHom_self] at key
      rw [Scheme.resHom_resHom, ← key]
    · change X.resHom inf_le_left (X.resHom (le_inf le_rfl hW) p.val.2) = p.val.2
      rw [Scheme.resHom_resHom, Scheme.resHom_self]
  right_inv s := by
    change X.resHom (le_inf le_rfl hW) (X.resHom inf_le_left s) = s
    rw [Scheme.resHom_resHom, Scheme.resHom_self]

lemma twistTriv₁_apply {W : X.Opens} (hW : W ≤ V₁)
    (p : ↥(twistSubmodule k V₀ V₁ g W)) :
    twistTriv₁ k V₀ V₁ g hW p = X.resHom (le_inf le_rfl hW) p.val.2 :=
  rfl

/-- The second-chart trivialization commutes with restriction. -/
lemma twistTriv₁_res {W' W : X.Opens} (h : W' ≤ W) (hW : W ≤ V₁)
    (p : ↥(twistSubmodule k V₀ V₁ g W)) :
    twistTriv₁ k V₀ V₁ g (h.trans hW) (twistRes k V₀ V₁ g h p) =
      X.resHom h (twistTriv₁ k V₀ V₁ g hW p) := by
  rw [twistTriv₁_apply, twistTriv₁_apply, twistRes_coe_snd]
  simp only [Scheme.resHom_resHom]

/-! ## The quasi-coherence packaging and the twisted affine vanishing -/

/-- The twisted sheaf carries the quasi-coherence packaging on the first chart,
transported from the structure sheaf along the trivialization. -/
noncomputable instance twistSheaf.instQcohOn₀ :
    Scheme.QcohOn (twistSheaf k V₀ V₁ g) V₀ :=
  Scheme.QcohOn.ofSectionsEquiv (G := X.moduleKSheaf k)
    (fun hWU ↦ twistTriv₀ k V₀ V₁ g hWU)
    (fun h hWU m ↦ twistTriv₀_res k V₀ V₁ g h hWU m)

/-- The twisted sheaf carries the quasi-coherence packaging on the second chart,
transported from the structure sheaf along the trivialization. -/
noncomputable instance twistSheaf.instQcohOn₁ :
    Scheme.QcohOn (twistSheaf k V₀ V₁ g) V₁ :=
  Scheme.QcohOn.ofSectionsEquiv (G := X.moduleKSheaf k)
    (fun hWU ↦ twistTriv₁ k V₀ V₁ g hWU)
    (fun h hWU m ↦ twistTriv₁_res k V₀ V₁ g h hWU m)

/-- **Twisted affine vanishing on the first chart** (G-CBC-3 for the cocycle-glued
sheaf): if `V₀` is affine, the degree-one cohomology of `V₀` with coefficients in `F_g`
vanishes. -/
theorem subsingleton_hModule'_twistSheaf_one₀ (h₀ : IsAffineOpen V₀) :
    Subsingleton (Sheaf.HModule' (twistSheaf k V₀ V₁ g) V₀ 1) :=
  h₀.subsingleton_hModule'_one_of_qcoh (twistSheaf k V₀ V₁ g)

/-- **Twisted affine vanishing on the second chart.** -/
theorem subsingleton_hModule'_twistSheaf_one₁ (h₁ : IsAffineOpen V₁) :
    Subsingleton (Sheaf.HModule' (twistSheaf k V₀ V₁ g) V₁ 1) :=
  h₁.subsingleton_hModule'_one_of_qcoh (twistSheaf k V₀ V₁ g)

/-- **The two-cover H¹ carrier fires on the twisted sheaf** (CBC-0 for `F_g`): for an
affine two-cover `V₀ ⊔ V₁ = ⊤`, the degree-one cohomology of `F_g` is the cokernel of
the Mayer–Vietoris restriction-difference map on twisted sections. The overlap sections
`F_g(V₀ ⊓ V₁)` are further identified with `Γ(X, V₀ ⊓ V₁)` by
`twistTriv₀ k V₀ V₁ g inf_le_left`. -/
noncomputable def twistTwoCoverH1 (hcov : V₀ ⊔ V₁ = ⊤)
    (h₀ : IsAffineOpen V₀) (h₁ : IsAffineOpen V₁) :
    Sheaf.HModule (twistSheaf k V₀ V₁ g) 1 ≃ₗ[k]
      ((twistSheaf k V₀ V₁ g).obj.obj (op (V₀ ⊓ V₁)) ⧸
        LinearMap.range
          ((X.twoCoverSquare V₀ V₁ hcov).moduleDiff (twistSheaf k V₀ V₁ g))) :=
  letI := subsingleton_hModule'_twistSheaf_one₀ k V₀ V₁ g h₀
  letI := subsingleton_hModule'_twistSheaf_one₁ k V₀ V₁ g h₁
  Scheme.twoCoverH1LinearEquiv k X V₀ V₁ (twistSheaf k V₀ V₁ g) hcov

end TwistSheaf

/-! ## Instantiation on the relative curve -/

section Relative

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (D : C.left.AffineTwoCover)

open MonoidalCategory CartesianMonoidalCategory

/-- **Pullback of a unit cocycle to the relative curve**: the image of a two-cover unit
cocycle on the curve (e.g. the fiber-twist cocycle `t₀ⁿ` of
`AlgebraicJacobian.RiemannRoch.FiberTwist`) under the first projection, a unit cocycle
on the base-changed two-cover of `relCurve C R`. -/
noncomputable def relUnitCocycle (gk : Γ(C.left, D.V₀ ⊓ D.V₁)ˣ) :
    Γ(relCurve C R, (relCover C R D).V₀ ⊓ (relCover C R D).V₁)ˣ :=
  Units.map ((fst C (overSpec k R)).left.appLE (D.V₀ ⊓ D.V₁)
    ((relCover C R D).V₀ ⊓ (relCover C R D).V₁)
    (le_of_eq (relCover_inf C R D))).hom.toMonoidHom gk

/-- **The relative twisted sheaf**: the cocycle-glued twisted sheaf of a unit cocycle on
the base-changed affine two-cover of the relative curve `C_R`, as a sheaf of
`R`-modules. -/
noncomputable def relTwistSheaf
    (g : Γ(relCurve C R, (relCover C R D).V₀ ⊓ (relCover C R D).V₁)ˣ) :
    Sheaf (Opens.grothendieckTopology ((relCurve C R : Scheme.{u}) : TopCat))
      (ModuleCat.{u} R) :=
  twistSheaf R (relCover C R D).V₀ (relCover C R D).V₁ g

/-- **The two-cover H¹ carrier fires relatively on the twisted sheaf** (CBC-0 for `F_g`
over the affine test ring `R`): the degree-one cohomology of the relative twisted sheaf
is the explicit two-cover cokernel of `R`-module sections. -/
noncomputable def relTwistTwoCoverH1
    (g : Γ(relCurve C R, (relCover C R D).V₀ ⊓ (relCover C R D).V₁)ˣ) :
    Sheaf.HModule (relTwistSheaf C R D g) 1 ≃ₗ[R]
      ((relTwistSheaf C R D g).obj.obj
          (op ((relCover C R D).V₀ ⊓ (relCover C R D).V₁)) ⧸
        LinearMap.range
          (((relCurve C R).twoCoverSquare (relCover C R D).V₀ (relCover C R D).V₁
              (relCover_sup C R D)).moduleDiff (relTwistSheaf C R D g))) :=
  twistTwoCoverH1 R (relCover C R D).V₀ (relCover C R D).V₁ g (relCover_sup C R D)
    (relCover_isAffineOpen₀ C R D) (relCover_isAffineOpen₁ C R D)

end Relative

end AlgebraicGeometry
