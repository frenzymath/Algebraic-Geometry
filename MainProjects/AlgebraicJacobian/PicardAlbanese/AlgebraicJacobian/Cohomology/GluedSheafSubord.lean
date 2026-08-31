/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafClass

/-!
# Subordination invariance of the glued sheaf (the W6-full fibre-restriction bridge)

For a scheme `X` over `Spec k`, pieces `U : J → X.Opens` carrying a gluing cocycle `g`,
and a second covering family `V : I → X.Opens` subordinated to the pieces along
`σ : I → J` (`V i ≤ U (σ i)`), the glued sheaf of the restricted transition units on
`V` is isomorphic to the glued sheaf of `g` on `U`:

* `AlgebraicGeometry.gluedSubordFwd` — componentwise restriction of glued sections
  `F_g(W) → F_{g'}(W)`, `s ↦ (res s_{σ i})_i`;
* `AlgebraicGeometry.gluedSubordSection` — the inverse assembly: the `j`-th component
  of a `V`-glued family `t` glues from the candidates `g j (σ i) · t_i` over the cover
  `{W ⊓ U j ⊓ V i}_i` (the cocycle law makes them compatible);
* `AlgebraicGeometry.gluedSubordEquiv` — the `k`-linear equivalence of glued sections,
  natural in `W` (`gluedSubordEquiv_res`);
* `AlgebraicGeometry.gluedSheafSubord` — **the sheaf isomorphism**
  `gluedSheaf k U g ≅ gluedSheaf k V g'`;
* `AlgebraicGeometry.subsingleton_hModule_gluedSheaf_subord` — cohomology-vanishing
  transport across the isomorphism.

The target multipliers `g'` are abstract — the hypothesis `hg'` pins their underlying
sections to the restricted transition units `g (σ i) (σ i')` — so the isomorphism
instantiates on the nose at the subordinated unit cocycle of a pinned basic-open
cocycle datum (`gluedSubordUnit`, `gluedSubordCocycle_evInf`): the datum's glued sheaf
against the glued sheaf of the meromorphic presentation
`MeromorphicPresentation.ofCocycle` of its Čech Picard class. That instantiation — the
step-(c) bridge of the W6-full fibre-restriction seam — is in
`AlgebraicJacobian.Cohomology.GluedSheafDatumFibre`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

section Subord

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

attribute [local instance] Scheme.overModule

variable {J I : Type u} {U : J → X.Opens} {g : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ}
variable {V : I → X.Opens} {g' : ∀ i i' : I, Γ(X, V i ⊓ V i')ˣ} {σ : I → J}

/-! ## The forward map: componentwise restriction -/

/-- **Componentwise restriction preserves matching**: restricting the `σ i`-th
component of a `U`-glued family to `W ⊓ V i` yields a `V`-glued family for the
restricted multipliers. -/
lemma gluedSubordFwd_mem (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    {W : X.Opens} {s : ∀ j : J, Γ(X, W ⊓ U j)} (hs : s ∈ gluedSubmodule k U g W) :
    (fun i => X.resHom (inf_le_inf_left W (hσ i)) (s (σ i)))
      ∈ gluedSubmodule k V g' W := by
  intro i i'
  have key := congrArg (X.resHom (le_inf (le_inf (inf_le_left.trans inf_le_left)
      ((inf_le_left.trans inf_le_right).trans (hσ i)))
      (inf_le_right.trans (hσ i')) :
      W ⊓ V i ⊓ V i' ≤ W ⊓ U (σ i) ⊓ U (σ i'))) (hs (σ i) (σ i'))
  rw [map_mul] at key
  rw [hg' i i']
  simp only [Scheme.resHom_resHom] at key ⊢
  exact key

/-- **The forward map of the subordination**: componentwise restriction of glued
sections along `W ⊓ V i ≤ W ⊓ U (σ i)`, as a `k`-linear map. -/
noncomputable def gluedSubordFwd (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (W : X.Opens) :
    ↥(gluedSubmodule k U g W) →ₗ[k] ↥(gluedSubmodule k V g' W) where
  toFun s := ⟨fun i =>
      secRes (X.moduleKSheaf k) (inf_le_inf_left W (hσ i)) (s.val (σ i)),
    gluedSubordFwd_mem k hσ hg' s.property⟩
  map_add' s t := Subtype.ext (funext fun i =>
    map_add (secRes (X.moduleKSheaf k) (inf_le_inf_left W (hσ i)))
      (s.val (σ i)) (t.val (σ i)))
  map_smul' r s := Subtype.ext (funext fun i =>
    map_smul (secRes (X.moduleKSheaf k) (inf_le_inf_left W (hσ i))) r
      (s.val (σ i)))

@[simp]
lemma gluedSubordFwd_coe (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    {W : X.Opens} (s : ↥(gluedSubmodule k U g W)) (i : I) :
    (gluedSubordFwd k hσ hg' W s).val i
      = X.resHom (inf_le_inf_left W (hσ i)) (s.val (σ i)) :=
  rfl

/-! ## The inverse assembly -/

variable (g) in
/-- The `(j, i)`-th candidate of the inverse assembly: over `W ⊓ U j ⊓ V i`, the
`j`-th component of the assembled `U`-glued family is `g j (σ i) · t i`. -/
noncomputable def gluedSubordCand (hσ : ∀ i : I, V i ≤ U (σ i)) {W : X.Opens}
    (t : ∀ i : I, Γ(X, W ⊓ V i)) (j : J) (i : I) : Γ(X, W ⊓ U j ⊓ V i) :=
  X.resHom (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans (hσ i)) :
      W ⊓ U j ⊓ V i ≤ U j ⊓ U (σ i)) (g j (σ i) : Γ(X, U j ⊓ U (σ i)))
    * X.resHom (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        W ⊓ U j ⊓ V i ≤ W ⊓ V i) (t i)

/-- **The candidates are compatible** (the cocycle law at `(j, σ i, σ i')` against the
matching of `t`): the candidates `g j (σ i) · t i` agree on the pairwise overlaps of
the cover `{W ⊓ U j ⊓ V i}_i`. -/
lemma gluedSubordCand_compatible (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : Scheme.IsGluingCocycle U g)
    {W : X.Opens} {t : ∀ i : I, Γ(X, W ⊓ V i)}
    (ht : t ∈ gluedSubmodule k V g' W) (j : J) (i i' : I) :
    X.resHom (inf_le_left : (W ⊓ U j ⊓ V i) ⊓ (W ⊓ U j ⊓ V i') ≤ W ⊓ U j ⊓ V i)
        (gluedSubordCand g hσ t j i)
      = X.resHom inf_le_right (gluedSubordCand g hσ t j i') := by
  -- the matching of `t`, restricted to the overlap and rewritten through `hg'`
  have hmatch := congrArg (X.resHom (le_inf (le_inf
      (inf_le_left.trans (inf_le_left.trans inf_le_left)) (inf_le_left.trans inf_le_right))
      (inf_le_right.trans inf_le_right) :
      (W ⊓ U j ⊓ V i) ⊓ (W ⊓ U j ⊓ V i') ≤ W ⊓ V i ⊓ V i')) (ht i i')
  rw [map_mul, hg' i i'] at hmatch
  simp only [Scheme.resHom_resHom] at hmatch
  -- the cocycle law at `(j, σ i, σ i')`, restricted to the overlap
  have hcoc := hc.mul_res_of_le (le_inf (le_inf
      (inf_le_left.trans (inf_le_left.trans inf_le_right))
      ((inf_le_left.trans inf_le_right).trans (hσ i)))
      ((inf_le_right.trans inf_le_right).trans (hσ i')) :
      (W ⊓ U j ⊓ V i) ⊓ (W ⊓ U j ⊓ V i') ≤ U j ⊓ U (σ i) ⊓ U (σ i'))
  rw [gluedSubordCand, gluedSubordCand, map_mul, map_mul]
  simp only [Scheme.resHom_resHom]
  rw [hmatch, ← mul_assoc, hcoc]

/-- **Existence and uniqueness of the assembled component**: the candidates
`g j (σ i) · t i` glue to a unique section over `W ⊓ U j` (the family `V` covers). -/
lemma gluedSubordSection_existsUnique (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : Scheme.IsGluingCocycle U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} {t : ∀ i : I, Γ(X, W ⊓ V i)}
    (ht : t ∈ gluedSubmodule k V g' W) (j : J) :
    ∃! sj : Γ(X, W ⊓ U j), ∀ i : I,
      X.resHom (inf_le_left : W ⊓ U j ⊓ V i ≤ W ⊓ U j) sj
        = gluedSubordCand g hσ t j i := by
  have hcover : W ⊓ U j ≤ ⨆ i : I, W ⊓ U j ⊓ V i := fun z hz => by
    obtain ⟨i, hi⟩ := hcov z
    exact Opens.mem_iSup.mpr ⟨i, hz, hi⟩
  have hcompat : TopCat.Presheaf.IsCompatible (X.moduleKSheaf k).obj
      (fun i : I => W ⊓ U j ⊓ V i) (fun i => gluedSubordCand g hσ t j i) := by
    intro i i'
    exact gluedSubordCand_compatible k hσ hg' hc ht j i i'
  obtain ⟨sj, hsj, hsju⟩ := TopCat.Sheaf.existsUnique_gluing'
    (X := (X : TopCat)) (C := ModuleCat.{u} k) (X.moduleKSheaf k)
    (fun i : I => W ⊓ U j ⊓ V i) (W ⊓ U j)
    (fun i => homOfLE inf_le_left) hcover
    (fun i => gluedSubordCand g hσ t j i) hcompat
  exact ⟨sj, fun i => hsj i, fun y hy => hsju y fun i => hy i⟩

/-- The assembled `j`-th component of the inverse of the subordination map. -/
noncomputable def gluedSubordSection (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : Scheme.IsGluingCocycle U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} {t : ∀ i : I, Γ(X, W ⊓ V i)}
    (ht : t ∈ gluedSubmodule k V g' W) (j : J) : Γ(X, W ⊓ U j) :=
  (gluedSubordSection_existsUnique k hσ hg' hc hcov ht j).exists.choose

/-- The defining property of the assembled component. -/
lemma gluedSubordSection_res (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : Scheme.IsGluingCocycle U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} {t : ∀ i : I, Γ(X, W ⊓ V i)}
    (ht : t ∈ gluedSubmodule k V g' W) (j : J) (i : I) :
    X.resHom (inf_le_left : W ⊓ U j ⊓ V i ≤ W ⊓ U j)
        (gluedSubordSection k hσ hg' hc hcov ht j)
      = gluedSubordCand g hσ t j i :=
  (gluedSubordSection_existsUnique k hσ hg' hc hcov ht j).exists.choose_spec i

/-- Uniqueness of the assembled component. -/
lemma gluedSubordSection_unique (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : Scheme.IsGluingCocycle U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} {t : ∀ i : I, Γ(X, W ⊓ V i)}
    (ht : t ∈ gluedSubmodule k V g' W) (j : J) {sj : Γ(X, W ⊓ U j)}
    (hsj : ∀ i : I, X.resHom (inf_le_left : W ⊓ U j ⊓ V i ≤ W ⊓ U j) sj
      = gluedSubordCand g hσ t j i) :
    sj = gluedSubordSection k hσ hg' hc hcov ht j :=
  (gluedSubordSection_existsUnique k hσ hg' hc hcov ht j).unique hsj
    (gluedSubordSection_res k hσ hg' hc hcov ht j)

include k in
/-- Separation over the subordinated cover: two sections of an open agreeing on every
`· ⊓ V i` agree. -/
private lemma sectionExt (hcov : ∀ z : X, ∃ i : I, z ∈ V i) {O : X.Opens}
    {s s' : Γ(X, O)}
    (h : ∀ i : I, X.resHom (inf_le_left : O ⊓ V i ≤ O) s
      = X.resHom inf_le_left s') : s = s' := by
  apply TopCat.Sheaf.eq_of_locally_eq' (X := (X : TopCat)) (C := ModuleCat.{u} k)
    (X.moduleKSheaf k) (fun i : I => O ⊓ V i) O (fun i => homOfLE inf_le_left)
    (fun z hz => by
      obtain ⟨i, hi⟩ := hcov z
      exact Opens.mem_iSup.mpr ⟨i, hz, hi⟩)
  exact h

/-- **The assembled components match through `g`**: the inverse assembly is a
`U`-glued family (checked on the subordinated cover through the cocycle law at
`(j, j', σ i)`). -/
lemma gluedSubordSection_mem (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : Scheme.IsGluingCocycle U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} {t : ∀ i : I, Γ(X, W ⊓ V i)}
    (ht : t ∈ gluedSubmodule k V g' W) :
    (fun j => gluedSubordSection k hσ hg' hc hcov ht j)
      ∈ gluedSubmodule k U g W := by
  intro j j'
  refine sectionExt k hcov (fun i => ?_)
  -- the left side restricts to the `(j, i)`-th candidate
  have hL := congrArg (X.resHom (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      W ⊓ U j ⊓ U j' ⊓ V i ≤ W ⊓ U j ⊓ V i))
    (gluedSubordSection_res k hσ hg' hc hcov ht j i)
  -- the right side restricts to the `(j', i)`-th candidate
  have hR := congrArg (X.resHom (le_inf (le_inf
      (inf_le_left.trans (inf_le_left.trans inf_le_left))
      (inf_le_left.trans inf_le_right)) inf_le_right :
      W ⊓ U j ⊓ U j' ⊓ V i ≤ W ⊓ U j' ⊓ V i))
    (gluedSubordSection_res k hσ hg' hc hcov ht j' i)
  rw [gluedSubordCand, map_mul] at hL hR
  simp only [Scheme.resHom_resHom] at hL hR
  -- the cocycle law at `(j, j', σ i)`
  have hcoc := hc.mul_res_of_le (le_inf (le_inf
      (inf_le_left.trans (inf_le_left.trans inf_le_right)) (inf_le_left.trans inf_le_right))
      (inf_le_right.trans (hσ i)) :
      W ⊓ U j ⊓ U j' ⊓ V i ≤ U j ⊓ U j' ⊓ U (σ i))
  change X.resHom _ (X.resHom (inf_le_left : W ⊓ U j ⊓ U j' ≤ W ⊓ U j)
      (gluedSubordSection k hσ hg' hc hcov ht j))
    = X.resHom _ (X.resHom (gluedInclCoc U W j j') (g j j' : Γ(X, U j ⊓ U j'))
        * X.resHom (gluedInclSnd U W j j') (gluedSubordSection k hσ hg' hc hcov ht j'))
  rw [map_mul]
  simp only [Scheme.resHom_resHom]
  rw [hL, hR, ← mul_assoc, hcoc]

/-! ## The equivalence -/

/-- **Left inverse**: the assembly of the componentwise restriction of a `U`-glued
family recovers its components (by the uniqueness of the gluing — `s j` restricts to
every candidate of its own image, through the matching of `s` at `(j, σ i)`). -/
lemma gluedSubordSection_fwd (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : Scheme.IsGluingCocycle U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} (s : ↥(gluedSubmodule k U g W)) (j : J) :
    gluedSubordSection k hσ hg' hc hcov
        (gluedSubordFwd_mem k hσ hg' s.property) j = s.val j := by
  refine (gluedSubordSection_unique k hσ hg' hc hcov
    (gluedSubordFwd_mem k hσ hg' s.property) j (fun i => ?_)).symm
  have key := congrArg (X.resHom (le_inf (le_inf
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right))
      (inf_le_right.trans (hσ i)) :
      W ⊓ U j ⊓ V i ≤ W ⊓ U j ⊓ U (σ i))) (s.property j (σ i))
  rw [map_mul] at key
  rw [gluedSubordCand]
  simp only [Scheme.resHom_resHom] at key ⊢
  exact key

/-- **Right inverse**: the componentwise restriction of the assembly recovers the
`V`-glued family (by separation — over `W ⊓ V i ⊓ V i'` both sides are
`g (σ i) (σ i') · t i'`, through the defining property of the assembly and the
matching of `t`). -/
lemma gluedSubordFwd_section (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : Scheme.IsGluingCocycle U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} (t : ↥(gluedSubmodule k V g' W)) (i : I) :
    X.resHom (inf_le_inf_left W (hσ i))
        (gluedSubordSection k hσ hg' hc hcov t.property (σ i)) = t.val i := by
  refine sectionExt k hcov (fun i' => ?_)
  -- the restriction of the assembly is `g (σ i) (σ i') · t i'`
  have hL := congrArg (X.resHom (le_inf
      (le_inf (inf_le_left.trans inf_le_left)
        ((inf_le_left.trans inf_le_right).trans (hσ i))) inf_le_right :
      W ⊓ V i ⊓ V i' ≤ W ⊓ U (σ i) ⊓ V i'))
    (gluedSubordSection_res k hσ hg' hc hcov t.property (σ i) i')
  rw [gluedSubordCand, map_mul] at hL
  simp only [Scheme.resHom_resHom] at hL
  -- the matching of `t` gives the same value
  have hmatch := t.property i i'
  rw [hg' i i'] at hmatch
  simp only [Scheme.resHom_resHom] at hmatch
  simp only [Scheme.resHom_resHom]
  rw [hL, hmatch]

/-- **The subordination equivalence of glued sections**: componentwise restriction
along `σ`, with inverse the candidate assembly. -/
noncomputable def gluedSubordEquiv (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : Scheme.IsGluingCocycle U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    (W : X.Opens) :
    ↥(gluedSubmodule k U g W) ≃ₗ[k] ↥(gluedSubmodule k V g' W) :=
  LinearEquiv.ofBijective (gluedSubordFwd k hσ hg' W)
    (Function.bijective_iff_has_inverse.mpr
      ⟨fun t => ⟨fun j => gluedSubordSection k hσ hg' hc hcov t.property j,
          gluedSubordSection_mem k hσ hg' hc hcov t.property⟩,
        fun s => Subtype.ext (funext fun j =>
          gluedSubordSection_fwd k hσ hg' hc hcov s j),
        fun t => Subtype.ext (funext fun i =>
          gluedSubordFwd_section k hσ hg' hc hcov t i)⟩)

@[simp]
lemma gluedSubordEquiv_apply_coe (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : Scheme.IsGluingCocycle U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W : X.Opens} (s : ↥(gluedSubmodule k U g W)) (i : I) :
    (gluedSubordEquiv k hσ hg' hc hcov W s).val i
      = X.resHom (inf_le_inf_left W (hσ i)) (s.val (σ i)) :=
  rfl

/-- The subordination equivalence commutes with restriction (the forward map is
componentwise restriction). -/
lemma gluedSubordEquiv_res (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : Scheme.IsGluingCocycle U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i)
    {W' W : X.Opens} (h : W' ≤ W) (s : ↥(gluedSubmodule k U g W)) :
    gluedSubordEquiv k hσ hg' hc hcov W' (gluedRes k U g h s)
      = gluedRes k V g' h (gluedSubordEquiv k hσ hg' hc hcov W s) := by
  refine Subtype.ext (funext fun i => ?_)
  rw [gluedSubordEquiv_apply_coe, gluedRes_coe, gluedRes_coe,
    gluedSubordEquiv_apply_coe]
  simp only [Scheme.resHom_resHom]

/-- **The subordination isomorphism of glued presheaves.** -/
noncomputable def gluedSubordPresheafIso (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : Scheme.IsGluingCocycle U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i) :
    gluedPresheaf k U g ≅ gluedPresheaf k V g' :=
  NatIso.ofComponents
    (fun W => (gluedSubordEquiv k hσ hg' hc hcov W.unop).toModuleIso)
    (fun {A B} i => by
      ext s
      exact gluedSubordEquiv_res k hσ hg' hc hcov i.unop.le s)

/-- **Subordination invariance of the glued sheaf**: a covering family subordinated to
the pieces of a gluing cocycle glues an isomorphic sheaf through the restricted
transition units. -/
noncomputable def gluedSheafSubord (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : Scheme.IsGluingCocycle U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i) :
    gluedSheaf k U g ≅ gluedSheaf k V g' :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (gluedSubordPresheafIso k hσ hg' hc hcov)

/-- **Cohomology vanishing transports across the subordination** in every degree. -/
theorem subsingleton_hModule_gluedSheaf_subord (hσ : ∀ i : I, V i ≤ U (σ i))
    (hg' : ∀ i i' : I, (g' i i' : Γ(X, V i ⊓ V i')) =
      X.resHom (le_inf (inf_le_left.trans (hσ i)) (inf_le_right.trans (hσ i')))
        (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))))
    (hc : Scheme.IsGluingCocycle U g) (hcov : ∀ z : X, ∃ i : I, z ∈ V i) (n : ℕ) :
    Subsingleton (Sheaf.HModule (gluedSheaf k U g) n) ↔
      Subsingleton (Sheaf.HModule (gluedSheaf k V g') n) :=
  (Sheaf.HModule.mapEquiv (gluedSheafSubord k hσ hg' hc hcov)
    n).toEquiv.subsingleton_congr

end Subord

end AlgebraicGeometry
