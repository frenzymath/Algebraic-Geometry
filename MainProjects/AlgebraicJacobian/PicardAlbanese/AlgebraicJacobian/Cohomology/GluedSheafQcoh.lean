/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheaf

/-!
# The componentwise action on the m-chart glued sheaf (DAT-1, stage 1b, vocabulary)

The quasi-coherence vocabulary of the glued sheaf `gluedSheaf k U g` on a chart open
`V` (`informal/spec-dat-1.md`, decision (D3)):

* `AlgebraicGeometry.le_iSup_basicOpen_of_sum_eq_one` — **coverage from a partition of
  unity**: if `∑ i, a i · h i = 1` in `Γ(X, V)` then the basic opens `D(h i)` cover `V`
  (the worksheet §3.2 partition witnesses feed the trivializing-family interface
  through this lemma).
* `AlgebraicGeometry.gluedSubmodule_ext` — **a glued section is determined by its
  covering-piece components**: if opens `U (σ i)` cover `W`, two glued sections with
  equal `σ i`-components are equal (the matching relation propagates equality to every
  component, structure-sheaf separation globalizes it). No cocycle law, no finiteness,
  no affineness.
* `AlgebraicGeometry.gluedQsmul` — the **componentwise action** of `Γ(X, V)` on glued
  sections over `W ≤ V`, `(r • s) j = r↾ · s j`, with the (P1) lemma set
  (`gluedQsmul_one/_mul/_add_left/_add/_smul`, `gluedRes_gluedQsmul`) and the
  trivialization compatibility `gluedTriv_gluedQsmul`
  (`triv_j (r • s) = r↾ · triv_j s`).

The (P2) localization axioms and the packaging assembly
(`Scheme.QcohOn (gluedSheaf k U g) V`) are in
`AlgebraicJacobian.Cohomology.GluedSheafQcohAssembly`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-! ## Coverage from a partition of unity -/

/-- **Coverage from a partition of unity**: sections `h i` of `V` admitting a partition
`∑ i, a i · h i = 1` have basic opens covering `V` — at a point of `V` not all germs of
the `h i` can be non-units, else `1` would lie in the maximal ideal of the stalk. -/
theorem le_iSup_basicOpen_of_sum_eq_one {X : Scheme.{u}} {V : X.Opens}
    {ι : Type*} [Fintype ι] (a h : ι → Γ(X, V)) (hpart : ∑ i, a i * h i = 1) :
    V ≤ ⨆ i, X.basicOpen (h i) := by
  intro x hx
  rw [TopologicalSpace.Opens.mem_iSup]
  by_contra hcon
  push Not at hcon
  have hnu : ∀ i : ι, ¬ IsUnit (X.presheaf.germ V x hx (h i)) := by
    intro i hu
    exact hcon i ((X.mem_basicOpen (h i) x hx).mpr hu)
  have h1 : (1 : X.presheaf.stalk x) ∈ IsLocalRing.maximalIdeal _ := by
    have hg := congrArg (X.presheaf.germ V x hx).hom hpart
    rw [map_one, map_sum] at hg
    rw [← hg]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).mpr (hnu i))
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

section Glued

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

attribute [local instance] Scheme.overModule

variable {J : Type u} (U : J → X.Opens) (g : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ)

/-! ## Glued sections are determined by their covering-piece components -/

/-- **Extensionality over a subordinate piece cover**: for a family of opens `P i`
below the gluing pieces `U (σ i)` and covering `W`, two glued sections over `W` whose
`σ i`-components agree on each `W ⊓ P i` are equal. The matching relation writes every
component locally as a multiple of a covering component, and the structure sheaf
separates. -/
theorem gluedSubmodule_ext {W : X.Opens} {ι : Type u} (σ : ι → J) (P : ι → X.Opens)
    (hP : ∀ i : ι, P i ≤ U (σ i)) (hWcov : W ≤ ⨆ i, P i)
    {s t : ↥(gluedSubmodule k U g W)}
    (hst : ∀ i : ι,
      X.resHom (inf_le_inf_left W (hP i) : W ⊓ P i ≤ W ⊓ U (σ i)) (s.val (σ i)) =
      X.resHom (inf_le_inf_left W (hP i)) (t.val (σ i))) : s = t := by
  refine Subtype.ext (funext fun j => ?_)
  have hcovj : W ⊓ U j ≤ ⨆ i, W ⊓ U j ⊓ P i := by
    have h1 : W ⊓ U j ≤ (W ⊓ U j) ⊓ ⨆ i, P i :=
      le_inf le_rfl (inf_le_left.trans hWcov)
    rwa [inf_iSup_eq] at h1
  apply TopCat.Sheaf.eq_of_locally_eq' (X := (X : TopCat)) (C := ModuleCat.{u} k)
    (X.moduleKSheaf k) (fun i => W ⊓ U j ⊓ P i) (W ⊓ U j)
    (fun i => homOfLE inf_le_left) hcovj
  intro i
  change X.resHom (inf_le_left : W ⊓ U j ⊓ P i ≤ W ⊓ U j) (s.val j) =
    X.resHom (inf_le_left : W ⊓ U j ⊓ P i ≤ W ⊓ U j) (t.val j)
  have hs := congrArg (X.resHom (le_inf (le_inf (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right)) (inf_le_right.trans (hP i)) :
    W ⊓ U j ⊓ P i ≤ W ⊓ U j ⊓ U (σ i)))
    ((mem_gluedSubmodule_iff k U g (s.val : ∀ l : J, Γ(X, W ⊓ U l))).mp
      s.property j (σ i))
  have ht := congrArg (X.resHom (le_inf (le_inf (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right)) (inf_le_right.trans (hP i)) :
    W ⊓ U j ⊓ P i ≤ W ⊓ U j ⊓ U (σ i)))
    ((mem_gluedSubmodule_iff k U g (t.val : ∀ l : J, Γ(X, W ⊓ U l))).mp
      t.property j (σ i))
  have hcomp := congrArg (X.resHom (le_inf (inf_le_left.trans inf_le_left)
      inf_le_right : W ⊓ U j ⊓ P i ≤ W ⊓ P i)) (hst i)
  rw [map_mul] at hs ht
  simp only [Scheme.resHom_resHom] at hs ht hcomp ⊢
  rw [hs, ht, hcomp]

/-! ## The componentwise action of a chart section ring -/

/-- The **componentwise action** of `r ∈ Γ(X, V)` on glued sections over `W ≤ V`:
`(r • s) j := r↾_{W ⊓ U j} · s j`. The (P1) half of the quasi-coherence packaging of
the glued sheaf on the chart `V`. -/
noncomputable def gluedQsmul {V W : X.Opens} (hWV : W ≤ V) (r : Γ(X, V))
    (s : ↥(gluedSubmodule k U g W)) : ↥(gluedSubmodule k U g W) :=
  ⟨fun j => X.resHom (inf_le_left.trans hWV : W ⊓ U j ≤ V) r * s.val j, by
    intro i j
    have hs := (mem_gluedSubmodule_iff k U g (s.val : ∀ l : J, Γ(X, W ⊓ U l))).mp
      s.property i j
    rw [map_mul, map_mul]
    simp only [Scheme.resHom_resHom]
    rw [hs]
    ring⟩

@[simp]
lemma gluedQsmul_coe {V W : X.Opens} (hWV : W ≤ V) (r : Γ(X, V))
    (s : ↥(gluedSubmodule k U g W)) (j : J) :
    (gluedQsmul k U g hWV r s).val j =
      X.resHom (inf_le_left.trans hWV : W ⊓ U j ≤ V) r * s.val j :=
  rfl

/-- The action of `1`. -/
lemma gluedQsmul_one {V W : X.Opens} (hWV : W ≤ V)
    (s : ↥(gluedSubmodule k U g W)) : gluedQsmul k U g hWV 1 s = s :=
  Subtype.ext (funext fun j => by rw [gluedQsmul_coe, map_one, one_mul])

/-- The action of a product. -/
lemma gluedQsmul_mul {V W : X.Opens} (hWV : W ≤ V) (r r' : Γ(X, V))
    (s : ↥(gluedSubmodule k U g W)) :
    gluedQsmul k U g hWV (r * r') s =
      gluedQsmul k U g hWV r (gluedQsmul k U g hWV r' s) :=
  Subtype.ext (funext fun j => by
    simp only [gluedQsmul_coe]
    rw [map_mul, mul_assoc])

/-- The action distributes over addition of scalars. -/
lemma gluedQsmul_add_left {V W : X.Opens} (hWV : W ≤ V) (r r' : Γ(X, V))
    (s : ↥(gluedSubmodule k U g W)) :
    gluedQsmul k U g hWV (r + r') s =
      gluedQsmul k U g hWV r s + gluedQsmul k U g hWV r' s :=
  Subtype.ext (funext fun j => by
    have hadd : (gluedQsmul k U g hWV r s + gluedQsmul k U g hWV r' s).val j =
        (gluedQsmul k U g hWV r s).val j + (gluedQsmul k U g hWV r' s).val j := rfl
    rw [hadd, gluedQsmul_coe, gluedQsmul_coe, gluedQsmul_coe, map_add, add_mul])

/-- The action distributes over addition of sections. -/
lemma gluedQsmul_add {V W : X.Opens} (hWV : W ≤ V) (r : Γ(X, V))
    (s t : ↥(gluedSubmodule k U g W)) :
    gluedQsmul k U g hWV r (s + t) =
      gluedQsmul k U g hWV r s + gluedQsmul k U g hWV r t :=
  Subtype.ext (funext fun j => by
    have hadd : (gluedQsmul k U g hWV r s + gluedQsmul k U g hWV r t).val j =
        (gluedQsmul k U g hWV r s).val j + (gluedQsmul k U g hWV r t).val j := rfl
    have hst : (s + t).val j = s.val j + t.val j := rfl
    rw [hadd, gluedQsmul_coe, gluedQsmul_coe, gluedQsmul_coe, hst, mul_add])

/-- The action commutes with the `k`-module structure (the `smul_qsmul` datum of the
two-cover pair). -/
lemma gluedQsmul_smul {V W : X.Opens} (hWV : W ≤ V) (r : Γ(X, V)) (c : k)
    (s : ↥(gluedSubmodule k U g W)) :
    gluedQsmul k U g hWV r (c • s) = c • gluedQsmul k U g hWV r s :=
  Subtype.ext (funext fun j => by
    have hcs : ((c • s : ↥(gluedSubmodule k U g W))).val j = c • s.val j := rfl
    have hcs' : ((c • gluedQsmul k U g hWV r s :
        ↥(gluedSubmodule k U g W))).val j = c • (gluedQsmul k U g hWV r s).val j := rfl
    rw [hcs', gluedQsmul_coe, gluedQsmul_coe, hcs, Scheme.overModule_smul_def,
      Scheme.overModule_smul_def, mul_left_comm])

/-- The action is natural under restriction of glued sections (the `secRes_qsmul`
axiom of the packaging). -/
lemma gluedRes_gluedQsmul {V W' W : X.Opens} (hW'W : W' ≤ W) (hWV : W ≤ V)
    (r : Γ(X, V)) (s : ↥(gluedSubmodule k U g W)) :
    gluedRes k U g hW'W (gluedQsmul k U g hWV r s) =
      gluedQsmul k U g (hW'W.trans hWV) r (gluedRes k U g hW'W s) :=
  Subtype.ext (funext fun j => by
    rw [gluedRes_coe, gluedQsmul_coe, gluedQsmul_coe, gluedRes_coe, map_mul]
    simp only [Scheme.resHom_resHom])

/-- The piece trivializations intertwine the componentwise action with
restrict-and-multiply. -/
lemma gluedTriv_gluedQsmul (hc : Scheme.IsGluingCocycle U g) {V W : X.Opens}
    (hWV : W ≤ V) {j : J} (hWj : W ≤ U j) (r : Γ(X, V))
    (s : ↥(gluedSubmodule k U g W)) :
    gluedTriv k hc j hWj (gluedQsmul k U g hWV r s) =
      X.resHom hWV r * gluedTriv k hc j hWj s := by
  rw [gluedTriv_apply, gluedTriv_apply, gluedQsmul_coe, map_mul]
  simp only [Scheme.resHom_resHom]

end Glued

end AlgebraicGeometry
