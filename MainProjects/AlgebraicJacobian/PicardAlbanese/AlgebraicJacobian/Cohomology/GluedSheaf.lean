/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RelativeTwoCover
import AlgebraicJacobian.Cohomology.AffineVanishingQcoh

/-!
# The m-chart cocycle-glued sheaf (DAT-1, stage 1a)

For a scheme `X` over `Spec k`, a family of opens `U : J → X.Opens` and **transition
multipliers** `g i j ∈ Γ(X, U i ⊓ U j)ˣ`, the glued sheaf of `informal/spec-dat-1.md`
(the m-chart generalization of the two-chart `AlgebraicGeometry.twistSheaf`), as a sheaf
of `k`-modules on the small Zariski site of `X`:
`F_g(W) = {s ∈ Π j, Γ(W ⊓ U j) | s i = g i j · s j on W ⊓ U i ⊓ U j for all i, j}`
(`AlgebraicGeometry.gluedSheaf`), together with

* the **cocycle law** `Scheme.IsGluingCocycle` (`g i i = 1` and
  `g i j · g j l = g i l` on triple overlaps) — a `Prop`-structure: the carrier needs no
  law (the matching relation is restriction-stable for arbitrary multipliers), the
  trivializations consume it;
* the **piece trivializations** `F_g(W) ≃ₗ[k] Γ(X, W)` for `W ≤ U j`, given by the
  `j`-th component (`AlgebraicGeometry.gluedTriv`), commuting with restriction
  (`gluedTriv_res`), with the cross-piece comparison `gluedTriv_eq_unit_mul`
  (`triv_i = g i j · triv_j` on opens below both pieces — the m-chart mirror of
  `twistTriv₀_inf_eq`).

The quasi-coherence packaging on a chart covered by finitely many basic-open pieces
(DAT-1 stage 1b) is in `AlgebraicJacobian.Cohomology.GluedSheafQcoh`.

## Implementation notes

Sections are a genuine `Submodule` of the product of section modules (no defect map: the
m-chart defect target would be a product-of-products); every element computation is
`Scheme.resHom` bookkeeping, and restriction-path independence is definitional by proof
irrelevance of `≤` after `Scheme.resHom_resHom` collapse. The sheaf condition glues each
component in the structure sheaf of `k`-modules over the covers `{Wₐ ⊓ U j}ₐ` and checks
the matching relation locally, mirroring `isSheaf_twistPresheaf`. The `k`-module
structure on section modules is `Scheme.overModule`, activated locally per the house
rule; `k` is an explicit argument throughout.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-! ## The inclusion lattice of the pieces -/

section Incl

variable {X : Scheme.{u}} {J : Type u} (U : J → X.Opens)

/-- The double overlap `W ⊓ U i ⊓ U j` is contained in the second piece part `W ⊓ U j`. -/
lemma gluedInclSnd (W : X.Opens) (i j : J) : W ⊓ U i ⊓ U j ≤ W ⊓ U j :=
  le_inf (inf_le_left.trans inf_le_left) inf_le_right

/-- The double overlap `W ⊓ U i ⊓ U j` is contained in the multiplier's home
`U i ⊓ U j`. -/
lemma gluedInclCoc (W : X.Opens) (i j : J) : W ⊓ U i ⊓ U j ≤ U i ⊓ U j :=
  le_inf (inf_le_left.trans inf_le_right) inf_le_right

end Incl

/-! ## The cocycle law -/

/-- **The gluing cocycle law** for a family of transition units
`g i j ∈ Γ(X, U i ⊓ U j)ˣ`: the normalization `g i i = 1` and the cocycle identity
`g i j · g j l = g i l` as an equality in the triple-overlap section ring
`Γ(X, U i ⊓ U j ⊓ U l)`. A `Prop`-mixin: the glued carrier (`gluedSubmodule`) needs no
law; the piece trivializations (`gluedTriv`) consume it. -/
structure Scheme.IsGluingCocycle {X : Scheme.{u}} {J : Type u} (U : J → X.Opens)
    (g : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ) : Prop where
  /-- The diagonal units are `1`. -/
  unit_self : ∀ i : J, (g i i : Γ(X, U i ⊓ U i)) = 1
  /-- The cocycle identity on the triple overlap `U i ⊓ U j ⊓ U l`. -/
  mul_res : ∀ i j l : J,
    X.resHom (inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U j) (g i j : Γ(X, U i ⊓ U j)) *
        X.resHom (gluedInclCoc U (U i) j l) (g j l : Γ(X, U j ⊓ U l)) =
      X.resHom (gluedInclSnd U (U i) j l) (g i l : Γ(X, U i ⊓ U l))

/-- The cocycle identity restricted to any open below the triple overlap. -/
lemma Scheme.IsGluingCocycle.mul_res_of_le {X : Scheme.{u}} {J : Type u}
    {U : J → X.Opens} {g : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ} (hc : Scheme.IsGluingCocycle U g)
    {i j l : J} {O : X.Opens} (hO : O ≤ U i ⊓ U j ⊓ U l) :
    X.resHom (hO.trans (inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U j))
          (g i j : Γ(X, U i ⊓ U j)) *
        X.resHom (hO.trans (gluedInclCoc U (U i) j l)) (g j l : Γ(X, U j ⊓ U l)) =
      X.resHom (hO.trans (gluedInclSnd U (U i) j l)) (g i l : Γ(X, U i ⊓ U l)) := by
  have key := congrArg (X.resHom hO) (hc.mul_res i j l)
  rw [map_mul] at key
  simp only [Scheme.resHom_resHom] at key
  exact key

/-! ## The glued submodule of matching families -/

section GluedSheaf

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

attribute [local instance] Scheme.overModule

/-- Restriction of scheme sections commutes with the `Scheme.overModule` action. -/
private lemma resHom_smul' {V W : X.Opens} (h : V ≤ W) (r : k) (s : Γ(X, W)) :
    X.resHom h (r • s) = r • X.resHom h s := by
  rw [Scheme.overModule_smul_def, map_mul, Scheme.overModule_smul_def]
  congr 1
  exact X.overAlgebraMap_apply_res k (homOfLE h).op r

/-- Multiplication by a fixed section commutes with the `Scheme.overModule` action. -/
private lemma mul_smul_section {W : X.Opens} (c : Γ(X, W)) (r : k) (s : Γ(X, W)) :
    c * (r • s) = r • (c * s) := by
  rw [Scheme.overModule_smul_def, Scheme.overModule_smul_def, mul_left_comm]

variable {J : Type u} (U : J → X.Opens) (g : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ)

/-- The module of **glued sections** over `W`: families `s` of sections on the pieces
`W ⊓ U j` matching through the multipliers `g i j` on every double overlap
`W ⊓ U i ⊓ U j`. -/
noncomputable def gluedSubmodule (W : X.Opens) :
    Submodule k (∀ j : J, Γ(X, W ⊓ U j)) where
  carrier := {s | ∀ i j : J,
    X.resHom (inf_le_left : W ⊓ U i ⊓ U j ≤ W ⊓ U i) (s i) =
      X.resHom (gluedInclCoc U W i j) (g i j : Γ(X, U i ⊓ U j)) *
        X.resHom (gluedInclSnd U W i j) (s j)}
  add_mem' {p q} hp hq := fun i j => by
    change X.resHom _ (p i + q i) = _ * X.resHom _ (p j + q j)
    rw [map_add, map_add, mul_add, hp i j, hq i j]
  zero_mem' := fun i j => by
    change X.resHom _ (0 : Γ(X, _)) = _ * X.resHom _ (0 : Γ(X, _))
    rw [map_zero, map_zero, mul_zero]
  smul_mem' r p hp := fun i j => by
    change X.resHom _ (r • p i) = _ * X.resHom _ (r • p j)
    rw [resHom_smul' k, resHom_smul' k, mul_smul_section k, hp i j]

lemma mem_gluedSubmodule_iff {W : X.Opens} (s : ∀ j : J, Γ(X, W ⊓ U j)) :
    s ∈ gluedSubmodule k U g W ↔ ∀ i j : J,
      X.resHom (inf_le_left : W ⊓ U i ⊓ U j ≤ W ⊓ U i) (s i) =
        X.resHom (gluedInclCoc U W i j) (g i j : Γ(X, U i ⊓ U j)) *
          X.resHom (gluedInclSnd U W i j) (s j) :=
  Iff.rfl

/-- The matching relation is stable under componentwise restriction. -/
lemma gluedSubmodule_res {W' W : X.Opens} (h : W' ≤ W)
    {s : ∀ j : J, Γ(X, W ⊓ U j)} (hs : s ∈ gluedSubmodule k U g W) :
    (fun j => X.resHom (inf_le_inf_right (U j) h) (s j)) ∈ gluedSubmodule k U g W' := by
  intro i j
  have key := congrArg
    (X.resHom (inf_le_inf_right (U j) (inf_le_inf_right (U i) h) :
      W' ⊓ U i ⊓ U j ≤ W ⊓ U i ⊓ U j)) (hs i j)
  rw [map_mul] at key
  simp only [Scheme.resHom_resHom] at key ⊢
  exact key

/-- Componentwise restriction of glued sections, as a `k`-linear map. -/
noncomputable def gluedRes {W' W : X.Opens} (h : W' ≤ W) :
    ↥(gluedSubmodule k U g W) →ₗ[k] ↥(gluedSubmodule k U g W') :=
  LinearMap.restrict
    (LinearMap.pi fun j => (secRes (X.moduleKSheaf k) (inf_le_inf_right (U j) h)).comp
      (LinearMap.proj j))
    (fun _ hs => gluedSubmodule_res k U g h hs)

@[simp]
lemma gluedRes_coe {W' W : X.Opens} (h : W' ≤ W)
    (s : ↥(gluedSubmodule k U g W)) (j : J) :
    (gluedRes k U g h s).val j = X.resHom (inf_le_inf_right (U j) h) (s.val j) :=
  rfl

/-! ## The presheaf and the sheaf condition -/

/-- The presheaf of glued sections of the multipliers `g` on the pieces `U`. -/
noncomputable def gluedPresheaf : (X.Opens)ᵒᵖ ⥤ ModuleCat.{u} k where
  obj W := ModuleCat.of k ↥(gluedSubmodule k U g W.unop)
  map {A B} i := ModuleCat.ofHom (gluedRes k U g i.unop.le)
  map_id A := by
    ext s j
    change X.resHom (inf_le_inf_right (U j) le_rfl) (s.val j) = s.val j
    exact Scheme.resHom_self _ _
  map_comp {A B D} i j := by
    ext s l
    change X.resHom (inf_le_inf_right (U l) (j.unop.le.trans i.unop.le)) (s.val l) =
      X.resHom (inf_le_inf_right (U l) j.unop.le)
        (X.resHom (inf_le_inf_right (U l) i.unop.le) (s.val l))
    exact (Scheme.resHom_resHom _ _ _).symm

/-- **The glued sections form a sheaf.** Each component glues in the structure sheaf of
`k`-modules over the covers `{Wₐ ⊓ U j}ₐ`, and the matching relation is local. -/
theorem isSheaf_gluedPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology (X : TopCat)) (gluedPresheaf k U g) := by
  have h : TopCat.Presheaf.IsSheaf (C := ModuleCat.{u} k) (X := (X : TopCat))
      (gluedPresheaf k U g) := by
    rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
    intro ι W sf hsf
    -- the compatibility hypothesis, in `gluedRes` form
    have hres : ∀ a b : ι,
        gluedRes k U g (inf_le_left : W a ⊓ W b ≤ W a) (sf a) =
          gluedRes k U g (inf_le_right : W a ⊓ W b ≤ W b) (sf b) := fun a b => hsf a b
    -- glue each component in the structure sheaf of `k`-modules
    have hcov : ∀ j : J, (iSup W) ⊓ U j ≤ ⨆ a, W a ⊓ U j := fun j => by
      rw [iSup_inf_eq]
    have hcompat : ∀ j : J, TopCat.Presheaf.IsCompatible (X.moduleKSheaf k).obj
        (fun a => W a ⊓ U j) (fun a => (sf a).val j) := by
      intro j a b
      have key := congrArg (fun q : ↥(gluedSubmodule k U g (W a ⊓ W b)) =>
        X.resHom (le_inf
          (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
          (inf_le_left.trans inf_le_right) :
            (W a ⊓ U j) ⊓ (W b ⊓ U j) ≤ (W a ⊓ W b) ⊓ U j) (q.val j)) (hres a b)
      simp only [gluedRes_coe, Scheme.resHom_resHom] at key
      exact key
    have H : ∀ j : J, ∃! tj : Γ(X, (iSup W) ⊓ U j),
        ∀ a : ι, X.resHom (inf_le_inf_right (U j) (le_iSup W a)) tj = (sf a).val j := by
      intro j
      obtain ⟨tj, htj, htju⟩ := TopCat.Sheaf.existsUnique_gluing'
        (X := (X : TopCat)) (C := ModuleCat.{u} k) (X.moduleKSheaf k)
        (fun a => W a ⊓ U j) ((iSup W) ⊓ U j)
        (fun a => homOfLE (inf_le_inf_right (U j) (le_iSup W a))) (hcov j)
        (fun a => (sf a).val j) (hcompat j)
      exact ⟨tj, fun a => htj a, fun y hy => htju y fun a => hy a⟩
    choose t ht htu using H
    -- the glued components match through the multipliers: check locally
    have hrel : t ∈ gluedSubmodule k U g (iSup W) := by
      intro i j
      have hcovΩ : (iSup W) ⊓ U i ⊓ U j ≤ ⨆ a, W a ⊓ U i ⊓ U j := by
        rw [iSup_inf_eq, iSup_inf_eq]
      apply TopCat.Sheaf.eq_of_locally_eq' (X := (X : TopCat)) (C := ModuleCat.{u} k)
        (X.moduleKSheaf k) (fun a => W a ⊓ U i ⊓ U j) ((iSup W) ⊓ U i ⊓ U j)
        (fun a => homOfLE
          (inf_le_inf_right (U j) (inf_le_inf_right (U i) (le_iSup W a)))) hcovΩ
      intro a
      change X.resHom (inf_le_inf_right (U j) (inf_le_inf_right (U i) (le_iSup W a)))
          (X.resHom inf_le_left (t i)) =
        X.resHom (inf_le_inf_right (U j) (inf_le_inf_right (U i) (le_iSup W a)))
          (X.resHom (gluedInclCoc U (iSup W) i j) (g i j : Γ(X, U i ⊓ U j)) *
            X.resHom (gluedInclSnd U (iSup W) i j) (t j))
      have hloc := (mem_gluedSubmodule_iff k U g ((sf a).val :
        ∀ l : J, Γ(X, W a ⊓ U l))).mp (sf a).property i j
      have hti := congrArg
        (X.resHom (inf_le_left : W a ⊓ U i ⊓ U j ≤ W a ⊓ U i)) (ht i a)
      have htj := congrArg
        (X.resHom (gluedInclSnd U (W a) i j)) (ht j a)
      rw [map_mul]
      simp only [Scheme.resHom_resHom] at hti htj hloc ⊢
      rw [← hti, ← htj] at hloc
      exact hloc
    -- assemble the gluing and prove existence and uniqueness
    refine ⟨⟨t, hrel⟩, fun a => ?_, fun s hs => ?_⟩
    · exact Subtype.ext (funext fun j => ht j a)
    · have hs' : ∀ a, gluedRes k U g (le_iSup W a) s = sf a := fun a => hs a
      refine Subtype.ext (funext fun j => ?_)
      refine htu j (s.val j) fun a => ?_
      rw [← hs' a, gluedRes_coe]
  exact h

/-- **The m-chart glued sheaf** of transition units `g i j ∈ Γ(X, U i ⊓ U j)ˣ` on the
pieces `U : J → X.Opens`: the sheaf of `k`-modules on the small Zariski site of `X`
whose sections over `W` are the families `s ∈ Π j, Γ(W ⊓ U j)` with `s i = g i j · s j`
on every double overlap. For a cocycle (`Scheme.IsGluingCocycle`) on a covering family
this is the line bundle presented by the cocycle, trivialized on each piece
(`gluedTriv`). -/
noncomputable def gluedSheaf :
    Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} k) :=
  ⟨gluedPresheaf k U g, isSheaf_gluedPresheaf k U g⟩

@[simp]
lemma gluedSheaf_obj (W : X.Opens) :
    (gluedSheaf k U g).obj.obj (op W) = ModuleCat.of k ↥(gluedSubmodule k U g W) := rfl

lemma secRes_gluedSheaf {W' W : X.Opens} (h : W' ≤ W)
    (s : ↥(gluedSubmodule k U g W)) :
    secRes (gluedSheaf k U g) h s = gluedRes k U g h s := rfl

/-! ## The piece trivializations -/

section Triv

variable {U} {g}
variable (hc : Scheme.IsGluingCocycle U g)

/-- **Piece trivialization**: over `W ≤ U j`, the `j`-th component is a `k`-linear
equivalence `F_g(W) ≃ₗ[k] Γ(X, W)` (the inverse rebuilds every component through the
transition units `g i j`; the cocycle law makes the rebuilt family match). -/
noncomputable def gluedTriv (j : J) {W : X.Opens} (hW : W ≤ U j) :
    ↥(gluedSubmodule k U g W) ≃ₗ[k] Γ(X, W) where
  toFun s := X.resHom (le_inf le_rfl hW) (s.val j)
  map_add' s t := map_add _ _ _
  map_smul' r s := resHom_smul' k _ r _
  invFun t := ⟨fun i =>
    X.resHom (le_inf inf_le_right (inf_le_left.trans hW) : W ⊓ U i ≤ U i ⊓ U j)
        (g i j : Γ(X, U i ⊓ U j)) *
      X.resHom (inf_le_left : W ⊓ U i ≤ W) t, by
    intro i i'
    have hO : W ⊓ U i ⊓ U i' ≤ U i ⊓ U i' ⊓ U j :=
      le_inf (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        ((inf_le_left.trans inf_le_left).trans hW)
    have hcoc := hc.mul_res_of_le hO
    rw [map_mul, map_mul]
    simp only [Scheme.resHom_resHom]
    rw [← hcoc, mul_assoc]⟩
  left_inv s := by
    refine Subtype.ext (funext fun i => ?_)
    have hloc := (mem_gluedSubmodule_iff k U g (s.val :
      ∀ l : J, Γ(X, W ⊓ U l))).mp s.property i j
    have key := congrArg
      (X.resHom (le_inf le_rfl (inf_le_left.trans hW) :
        W ⊓ U i ≤ W ⊓ U i ⊓ U j)) hloc
    rw [map_mul] at key
    simp only [Scheme.resHom_resHom] at key
    rw [Scheme.resHom_self] at key
    change X.resHom (le_inf inf_le_right (inf_le_left.trans hW))
        (g i j : Γ(X, U i ⊓ U j)) *
        X.resHom (inf_le_left : W ⊓ U i ≤ W)
          (X.resHom (le_inf le_rfl hW) (s.val j)) = s.val i
    rw [Scheme.resHom_resHom, ← key]
  right_inv t := by
    change X.resHom (le_inf le_rfl hW)
        (X.resHom (le_inf inf_le_right (inf_le_left.trans hW) : W ⊓ U j ≤ U j ⊓ U j)
            (g j j : Γ(X, U j ⊓ U j)) *
          X.resHom (inf_le_left : W ⊓ U j ≤ W) t) = t
    rw [map_mul, hc.unit_self j, map_one, map_one, one_mul, Scheme.resHom_resHom,
      Scheme.resHom_self]

lemma gluedTriv_apply (j : J) {W : X.Opens} (hW : W ≤ U j)
    (s : ↥(gluedSubmodule k U g W)) :
    gluedTriv k hc j hW s = X.resHom (le_inf le_rfl hW) (s.val j) :=
  rfl

@[simp]
lemma gluedTriv_symm_coe (j : J) {W : X.Opens} (hW : W ≤ U j) (t : Γ(X, W)) (i : J) :
    ((gluedTriv k hc j hW).symm t).val i =
      X.resHom (le_inf inf_le_right (inf_le_left.trans hW) : W ⊓ U i ≤ U i ⊓ U j)
          (g i j : Γ(X, U i ⊓ U j)) *
        X.resHom (inf_le_left : W ⊓ U i ≤ W) t :=
  rfl

/-- The piece trivialization commutes with restriction. -/
lemma gluedTriv_res (j : J) {W' W : X.Opens} (h : W' ≤ W) (hW : W ≤ U j)
    (s : ↥(gluedSubmodule k U g W)) :
    gluedTriv k hc j (h.trans hW) (gluedRes k U g h s) =
      X.resHom h (gluedTriv k hc j hW s) := by
  rw [gluedTriv_apply, gluedTriv_apply, gluedRes_coe]
  simp only [Scheme.resHom_resHom]

/-- **Cross-piece comparison of the trivializations**: on an open below two pieces the
trivializations differ by the transition unit, `triv_i = g i j · triv_j` — the m-chart
mirror of `twistTriv₀_inf_eq`. -/
lemma gluedTriv_eq_unit_mul (i j : J) {W : X.Opens} (hWi : W ≤ U i) (hWj : W ≤ U j)
    (s : ↥(gluedSubmodule k U g W)) :
    gluedTriv k hc i hWi s =
      X.resHom (le_inf hWi hWj : W ≤ U i ⊓ U j) (g i j : Γ(X, U i ⊓ U j)) *
        gluedTriv k hc j hWj s := by
  have hloc := (mem_gluedSubmodule_iff k U g (s.val :
    ∀ l : J, Γ(X, W ⊓ U l))).mp s.property i j
  have key := congrArg
    (X.resHom (le_inf (le_inf le_rfl hWi) hWj : W ≤ W ⊓ U i ⊓ U j)) hloc
  rw [map_mul] at key
  simp only [Scheme.resHom_resHom] at key
  rw [gluedTriv_apply, gluedTriv_apply]
  exact key

end Triv

end GluedSheaf

end AlgebraicGeometry
