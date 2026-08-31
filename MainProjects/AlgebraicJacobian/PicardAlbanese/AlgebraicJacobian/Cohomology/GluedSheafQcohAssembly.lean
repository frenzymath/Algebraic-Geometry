/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafQcoh

/-!
# QcohOn for the m-chart glued sheaf (DAT-1, stage 1b, assembly)

The (P2) localization axioms and the quasi-coherence packaging of the glued sheaf
`gluedSheaf k U g` on a chart `V` under the **trivializing-family interface**
(`informal/spec-dat-1.md` decision (D3), in subordinate form): a finite family of basic
opens `D(h i)` (`h : ι → Γ(X, V)`) covering `V`, each contained in a gluing piece
`U (σ i)` (`hP : D(h i) ≤ U (σ i)` — containment, not equality, so that restricted
families serve smaller charts such as the pinned overlap).

* `exists_gluedRes_eq_gluedQsmul_pow` — **(P2) denominator clearing**: per-piece
  clearing (`IsAffineOpen.exists_res_eq_pow_mul`), finite uniformization of the
  exponent, defect annihilation on the affine double overlaps
  (`IsAffineOpen.exists_pow_mul_eq_zero_of_res_eq_zero`), regluing in the sheaf, and a
  local comparison through `gluedSubmodule_ext`.
* `exists_gluedQsmul_pow_eq_zero` — **(P2) defect annihilation**: per-piece
  annihilation, finite uniformization, `gluedSubmodule_ext` against `0`.
* `gluedQcohOn` — the assembled packaging `Scheme.QcohOn (gluedSheaf k U g) V`
  (a `def`; keyed `instance`s are declared only at the pinned datum, stage 1d).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

section Assembly

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

attribute [local instance] Scheme.overModule

variable {J : Type u} (U : J → X.Opens) (g : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ)
variable {V : X.Opens} {ι : Type u} [Finite ι] {σ : ι → J} {h : ι → Γ(X, V)}

/-- **(P2) denominator clearing for the glued sheaf** on a chart with a trivializing
subordinate basic-open family: a glued section over `V' ⊓ D(q)` extends to `V'` after
scaling by a power of `q`. -/
theorem exists_gluedRes_eq_gluedQsmul_pow (hc : Scheme.IsGluingCocycle U g)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i))
    (hcov : V ≤ ⨆ i : ι, X.basicOpen (h i))
    {V' : X.Opens} (hV' : IsAffineOpen V') (hV'V : V' ≤ V) (q : Γ(X, V))
    (c : ↥(gluedSubmodule k U g (V' ⊓ X.basicOpen q))) :
    ∃ (N : ℕ) (e : ↥(gluedSubmodule k U g V')),
      gluedRes k U g inf_le_left e =
        gluedQsmul k U g ((inf_le_left : V' ⊓ X.basicOpen q ≤ V').trans hV'V)
          (q ^ N) c := by
  classical
  haveI := Fintype.ofFinite ι
  -- the pieces and double overlaps are affine
  have hPaff : ∀ i : ι, IsAffineOpen (V' ⊓ X.basicOpen (h i)) := by
    intro i
    rw [← Scheme.basicOpen_resHom hV'V (h i)]
    exact hV'.basicOpen _
  have hOaff : ∀ i i' : ι,
      IsAffineOpen (V' ⊓ X.basicOpen (h i) ⊓ X.basicOpen (h i')) := by
    intro i i'
    rw [inf_assoc, ← Scheme.basicOpen_mul, ← Scheme.basicOpen_resHom hV'V]
    exact hV'.basicOpen _
  -- the components of `c`, reshuffled onto the pieces
  have hpc : ∀ i : ι,
      (V' ⊓ X.basicOpen (h i)) ⊓ X.basicOpen q ≤
        (V' ⊓ X.basicOpen q) ⊓ U (σ i) := fun i =>
    le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      ((inf_le_left.trans inf_le_right).trans (hP i))
  -- per-piece denominator clearing
  have hden : ∀ i : ι, ∃ (N : ℕ) (e : Γ(X, V' ⊓ X.basicOpen (h i))),
      X.resHom inf_le_left e =
        X.resHom (inf_le_left.trans (inf_le_left.trans hV'V)) q ^ N *
          X.resHom (hpc i) (c.val (σ i)) := fun i =>
    (hPaff i).exists_res_eq_pow_mul (inf_le_left.trans hV'V) q
      (X.resHom (hpc i) (c.val (σ i)))
  choose N₁ e₁ he₁ using hden
  set N := Finset.univ.sup N₁ with hNdef
  -- the uniformized clears
  have hden₂ : ∀ i : ι, ∃ e₂ : Γ(X, V' ⊓ X.basicOpen (h i)),
      X.resHom inf_le_left e₂ =
        X.resHom (inf_le_left.trans (inf_le_left.trans hV'V)) q ^ N *
          X.resHom (hpc i) (c.val (σ i)) := by
    intro i
    refine ⟨X.resHom (inf_le_left.trans hV'V) q ^ (N - N₁ i) * e₁ i, ?_⟩
    rw [map_mul, map_pow, Scheme.resHom_resHom, he₁ i, ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ i))]
  choose E hE using hden₂
  -- defect annihilation on the affine double overlaps
  have hann : ∀ i i' : ι, ∃ M : ℕ,
      X.resHom ((inf_le_left.trans inf_le_left).trans hV'V) q ^ M *
        (X.resHom (inf_le_left :
            V' ⊓ X.basicOpen (h i) ⊓ X.basicOpen (h i') ≤ V' ⊓ X.basicOpen (h i))
            (E i) -
          X.resHom (le_inf ((inf_le_left.trans inf_le_right).trans (hP i))
                (inf_le_right.trans (hP i')) :
              V' ⊓ X.basicOpen (h i) ⊓ X.basicOpen (h i') ≤ U (σ i) ⊓ U (σ i'))
              (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))) *
            X.resHom (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
              V' ⊓ X.basicOpen (h i) ⊓ X.basicOpen (h i') ≤ V' ⊓ X.basicOpen (h i'))
              (E i')) = 0 := by
    intro i i'
    refine (hOaff i i').exists_pow_mul_eq_zero_of_res_eq_zero
      ((inf_le_left.trans inf_le_left).trans hV'V) q _ ?_
    have k₁ := congrArg (X.resHom (inf_le_inf_right (X.basicOpen q)
      (inf_le_left : V' ⊓ X.basicOpen (h i) ⊓ X.basicOpen (h i') ≤
        V' ⊓ X.basicOpen (h i)))) (hE i)
    have k₂ := congrArg (X.resHom (inf_le_inf_right (X.basicOpen q)
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        V' ⊓ X.basicOpen (h i) ⊓ X.basicOpen (h i') ≤
          V' ⊓ X.basicOpen (h i')))) (hE i')
    have k₃ := congrArg
      (X.resHom (le_inf (le_inf (le_inf
          (inf_le_left.trans (inf_le_left.trans inf_le_left)) inf_le_right)
          ((inf_le_left.trans (inf_le_left.trans inf_le_right)).trans (hP i)))
          ((inf_le_left.trans inf_le_right).trans (hP i')) :
        (V' ⊓ X.basicOpen (h i) ⊓ X.basicOpen (h i')) ⊓ X.basicOpen q ≤
          (V' ⊓ X.basicOpen q) ⊓ U (σ i) ⊓ U (σ i')))
      ((mem_gluedSubmodule_iff k U g
        (c.val : ∀ l : J, Γ(X, (V' ⊓ X.basicOpen q) ⊓ U l))).mp
        c.property (σ i) (σ i'))
    rw [map_mul, map_pow] at k₁ k₂
    rw [map_mul] at k₃
    simp only [Scheme.resHom_resHom] at k₁ k₂ k₃
    rw [map_sub, map_mul]
    simp only [Scheme.resHom_resHom]
    rw [k₁, k₂, k₃]
    ring
  choose M₁ hM₁ using hann
  set M := Finset.univ.sup fun i => Finset.univ.sup (M₁ i) with hMdef
  -- the sections to reglue, through the piece trivializations
  have hglue₀ : ∀ i : ι, ∃ f : ↥(gluedSubmodule k U g (V' ⊓ X.basicOpen (h i))),
      gluedTriv k hc (σ i) (inf_le_right.trans (hP i)) f =
        X.resHom (inf_le_left.trans hV'V) q ^ M * E i := fun i =>
    ⟨(gluedTriv k hc (σ i) (inf_le_right.trans (hP i))).symm _,
      (gluedTriv k hc (σ i) (inf_le_right.trans (hP i))).apply_symm_apply _⟩
  choose F' hF' using hglue₀
  -- the M-power defect equation, restricted to the gluing overlaps
  have hover : ∀ i i' : ι,
      X.resHom (inf_le_left :
          (V' ⊓ X.basicOpen (h i)) ⊓ (V' ⊓ X.basicOpen (h i')) ≤
            V' ⊓ X.basicOpen (h i))
        (X.resHom (inf_le_left.trans hV'V) q ^ M * E i) =
      X.resHom (le_inf ((inf_le_left.trans inf_le_right).trans (hP i))
            ((inf_le_right.trans inf_le_right).trans (hP i')) :
          (V' ⊓ X.basicOpen (h i)) ⊓ (V' ⊓ X.basicOpen (h i')) ≤
            U (σ i) ⊓ U (σ i'))
          (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))) *
        X.resHom (inf_le_right :
            (V' ⊓ X.basicOpen (h i)) ⊓ (V' ⊓ X.basicOpen (h i')) ≤
              V' ⊓ X.basicOpen (h i'))
          (X.resHom (inf_le_left.trans hV'V) q ^ M * E i') := by
    intro i i'
    have hMle : M₁ i i' ≤ M :=
      le_trans (Finset.le_sup (Finset.mem_univ i'))
        (Finset.le_sup (f := fun l => Finset.univ.sup (M₁ l)) (Finset.mem_univ i))
    have hM' : X.resHom ((inf_le_left.trans inf_le_left).trans hV'V) q ^ M *
        (X.resHom (inf_le_left :
            V' ⊓ X.basicOpen (h i) ⊓ X.basicOpen (h i') ≤ V' ⊓ X.basicOpen (h i))
            (E i) -
          X.resHom (le_inf ((inf_le_left.trans inf_le_right).trans (hP i))
                (inf_le_right.trans (hP i')))
              (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))) *
            X.resHom (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
              (E i')) = 0 := by
      calc X.resHom ((inf_le_left.trans inf_le_left).trans hV'V) q ^ M *
            (X.resHom inf_le_left (E i) -
              X.resHom (le_inf ((inf_le_left.trans inf_le_right).trans (hP i))
                    (inf_le_right.trans (hP i')))
                  (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))) *
                X.resHom (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
                  (E i'))
          = X.resHom ((inf_le_left.trans inf_le_left).trans hV'V) q ^ (M - M₁ i i') *
            (X.resHom ((inf_le_left.trans inf_le_left).trans hV'V) q ^ (M₁ i i') *
              (X.resHom inf_le_left (E i) -
                X.resHom (le_inf ((inf_le_left.trans inf_le_right).trans (hP i))
                      (inf_le_right.trans (hP i')))
                    (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))) *
                  X.resHom (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
                    (E i'))) := by
            rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hMle]
        _ = 0 := by rw [hM₁ i i', mul_zero]
    have hres := congrArg (X.resHom (le_inf (le_inf
        (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right))
        (inf_le_right.trans inf_le_right) :
      (V' ⊓ X.basicOpen (h i)) ⊓ (V' ⊓ X.basicOpen (h i')) ≤
        V' ⊓ X.basicOpen (h i) ⊓ X.basicOpen (h i'))) hM'
    rw [map_zero, map_mul, map_sub, map_mul, map_pow] at hres
    simp only [Scheme.resHom_resHom] at hres
    rw [map_mul, map_mul, map_pow, map_pow]
    simp only [Scheme.resHom_resHom]
    linear_combination hres
  -- reglue over the piece cover of `V'`
  have hcovV' : V' ≤ ⨆ i : ι, V' ⊓ X.basicOpen (h i) := by
    have h1 : V' ≤ V' ⊓ ⨆ i : ι, X.basicOpen (h i) :=
      le_inf le_rfl (hV'V.trans hcov)
    rwa [inf_iSup_eq] at h1
  have hcompat : ∀ i i' : ι,
      gluedRes k U g (inf_le_left :
        (V' ⊓ X.basicOpen (h i)) ⊓ (V' ⊓ X.basicOpen (h i')) ≤
          V' ⊓ X.basicOpen (h i)) (F' i) =
      gluedRes k U g (inf_le_right :
        (V' ⊓ X.basicOpen (h i)) ⊓ (V' ⊓ X.basicOpen (h i')) ≤
          V' ⊓ X.basicOpen (h i')) (F' i') := by
    intro i i'
    apply (gluedTriv k hc (σ i)
      (inf_le_left.trans (inf_le_right.trans (hP i)) :
        (V' ⊓ X.basicOpen (h i)) ⊓ (V' ⊓ X.basicOpen (h i')) ≤ U (σ i))).injective
    have hL : gluedTriv k hc (σ i)
        (inf_le_left.trans (inf_le_right.trans (hP i)) :
          (V' ⊓ X.basicOpen (h i)) ⊓ (V' ⊓ X.basicOpen (h i')) ≤ U (σ i))
        (gluedRes k U g (inf_le_left :
          (V' ⊓ X.basicOpen (h i)) ⊓ (V' ⊓ X.basicOpen (h i')) ≤
            V' ⊓ X.basicOpen (h i)) (F' i)) =
        X.resHom (inf_le_left :
            (V' ⊓ X.basicOpen (h i)) ⊓ (V' ⊓ X.basicOpen (h i')) ≤
              V' ⊓ X.basicOpen (h i))
          (X.resHom (inf_le_left.trans hV'V) q ^ M * E i) := by
      rw [gluedTriv_res k hc (σ i) inf_le_left (inf_le_right.trans (hP i)), hF' i]
    have hR : gluedTriv k hc (σ i)
        (inf_le_left.trans (inf_le_right.trans (hP i)) :
          (V' ⊓ X.basicOpen (h i)) ⊓ (V' ⊓ X.basicOpen (h i')) ≤ U (σ i))
        (gluedRes k U g (inf_le_right :
          (V' ⊓ X.basicOpen (h i)) ⊓ (V' ⊓ X.basicOpen (h i')) ≤
            V' ⊓ X.basicOpen (h i')) (F' i')) =
        X.resHom (le_inf ((inf_le_left.trans inf_le_right).trans (hP i))
              ((inf_le_right.trans inf_le_right).trans (hP i')) :
            (V' ⊓ X.basicOpen (h i)) ⊓ (V' ⊓ X.basicOpen (h i')) ≤
              U (σ i) ⊓ U (σ i'))
            (g (σ i) (σ i') : Γ(X, U (σ i) ⊓ U (σ i'))) *
          X.resHom (inf_le_right :
              (V' ⊓ X.basicOpen (h i)) ⊓ (V' ⊓ X.basicOpen (h i')) ≤
                V' ⊓ X.basicOpen (h i'))
            (X.resHom (inf_le_left.trans hV'V) q ^ M * E i') := by
      rw [gluedTriv_eq_unit_mul k hc (σ i) (σ i')
          (inf_le_left.trans (inf_le_right.trans (hP i)))
          (inf_le_right.trans (inf_le_right.trans (hP i'))),
        gluedTriv_res k hc (σ i') inf_le_right (inf_le_right.trans (hP i')), hF' i']
    rw [hL, hR]
    exact hover i i'
  obtain ⟨e, he, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (X := (X : TopCat)) (C := ModuleCat.{u} k)
    (⟨gluedPresheaf k U g, isSheaf_gluedPresheaf k U g⟩ :
      TopCat.Sheaf (ModuleCat.{u} k) (X : TopCat))
    (fun i => V' ⊓ X.basicOpen (h i)) V' (fun i => homOfLE inf_le_left) hcovV' F'
    (fun i i' => hcompat i i')
  refine ⟨N + M, e, ?_⟩
  -- compare over the subordinate piece cover of `V' ⊓ D(q)`
  refine gluedSubmodule_ext k U g σ (fun i => X.basicOpen (h i)) hP
    ((inf_le_left.trans hV'V).trans hcov :
      V' ⊓ X.basicOpen q ≤ ⨆ i : ι, X.basicOpen (h i)) fun i => ?_
  have he'i : gluedRes k U g
      (inf_le_left : V' ⊓ X.basicOpen (h i) ≤ V') e = F' i := he i
  -- the `(σ i)`-component of the glue, trivialized
  have htriv := congrArg (gluedTriv k hc (σ i)
    (inf_le_right.trans (hP i) : V' ⊓ X.basicOpen (h i) ≤ U (σ i))) he'i
  rw [hF' i] at htriv
  -- restrict the trivialized equation to `(V' ⊓ D(q)) ⊓ D(h i)`
  have hle : (V' ⊓ X.basicOpen q) ⊓ X.basicOpen (h i) ≤ V' ⊓ X.basicOpen (h i) :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hres := congrArg (X.resHom hle) htriv
  rw [gluedTriv_apply, gluedRes_coe] at hres
  simp only [Scheme.resHom_resHom] at hres
  rw [map_mul, map_pow] at hres
  simp only [Scheme.resHom_resHom] at hres
  -- the uniformized clear, restricted to the same open
  have hEq := congrArg (X.resHom (le_inf
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (inf_le_left.trans inf_le_right) :
    (V' ⊓ X.basicOpen q) ⊓ X.basicOpen (h i) ≤
      (V' ⊓ X.basicOpen (h i)) ⊓ X.basicOpen q)) (hE i)
  rw [map_mul, map_pow] at hEq
  simp only [Scheme.resHom_resHom] at hEq
  -- assemble
  rw [gluedRes_coe]
  simp only [Scheme.resHom_resHom]
  rw [gluedQsmul_coe, map_mul, map_pow, map_pow]
  simp only [Scheme.resHom_resHom]
  rw [hres, hEq, ← mul_assoc, ← pow_add, add_comm M N]

/-- **(P2) defect annihilation for the glued sheaf** on a chart with a trivializing
subordinate basic-open family: a glued section over `V'` restricting to zero on
`V' ⊓ D(q)` is killed by a power of `q`. -/
theorem exists_gluedQsmul_pow_eq_zero
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i))
    (hcov : V ≤ ⨆ i : ι, X.basicOpen (h i))
    {V' : X.Opens} (hV' : IsAffineOpen V') (hV'V : V' ≤ V) (q : Γ(X, V))
    (t : ↥(gluedSubmodule k U g V'))
    (ht : gluedRes k U g (inf_le_left : V' ⊓ X.basicOpen q ≤ V') t = 0) :
    ∃ M : ℕ, gluedQsmul k U g hV'V (q ^ M) t = 0 := by
  classical
  haveI := Fintype.ofFinite ι
  have hPaff : ∀ i : ι, IsAffineOpen (V' ⊓ X.basicOpen (h i)) := by
    intro i
    rw [← Scheme.basicOpen_resHom hV'V (h i)]
    exact hV'.basicOpen _
  -- per-piece annihilation of the restricted components
  have hann : ∀ i : ι, ∃ M : ℕ,
      X.resHom (inf_le_left.trans hV'V) q ^ M *
        X.resHom (inf_le_inf_left V' (hP i) :
          V' ⊓ X.basicOpen (h i) ≤ V' ⊓ U (σ i)) (t.val (σ i)) = 0 := by
    intro i
    refine (hPaff i).exists_pow_mul_eq_zero_of_res_eq_zero (inf_le_left.trans hV'V) q
      (X.resHom (inf_le_inf_left V' (hP i)) (t.val (σ i))) ?_
    have hz := congrArg (fun z : ↥(gluedSubmodule k U g (V' ⊓ X.basicOpen q)) =>
      z.val (σ i)) ht
    simp only [gluedRes_coe, ZeroMemClass.coe_zero, Pi.zero_apply] at hz
    have hz2 := congrArg (X.resHom (le_inf (le_inf (inf_le_left.trans inf_le_left)
      inf_le_right) ((inf_le_left.trans inf_le_right).trans (hP i)) :
        (V' ⊓ X.basicOpen (h i)) ⊓ X.basicOpen q ≤
          (V' ⊓ X.basicOpen q) ⊓ U (σ i))) hz
    rw [map_zero] at hz2
    simp only [Scheme.resHom_resHom] at hz2
    rw [Scheme.resHom_resHom]
    exact hz2
  choose M₁ hM₁ using hann
  refine ⟨Finset.univ.sup M₁, ?_⟩
  refine gluedSubmodule_ext k U g σ (fun i => X.basicOpen (h i)) hP
    (hV'V.trans hcov) fun i => ?_
  have hz : (0 : ↥(gluedSubmodule k U g V')).val (σ i) = 0 := rfl
  rw [gluedQsmul_coe, hz, map_zero, map_mul, map_pow, map_pow]
  simp only [Scheme.resHom_resHom]
  rw [← Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ i) :
      M₁ i ≤ Finset.univ.sup M₁),
    pow_add, mul_assoc, hM₁ i, mul_zero]

/-- **The quasi-coherence packaging of the glued sheaf** on a chart carrying a finite
trivializing subordinate basic-open family (DAT-1 stage 1b): the componentwise (P1)
action together with the two (P2) localization axioms. A `def`: keyed `instance`s are
declared only at the pinned datum (stage 1d), per the house instance discipline. -/
@[reducible] noncomputable def gluedQcohOn (hc : Scheme.IsGluingCocycle U g)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i))
    (hcov : V ≤ ⨆ i : ι, X.basicOpen (h i)) :
    Scheme.QcohOn (gluedSheaf k U g) V where
  qsmul hWV r s := gluedQsmul k U g hWV r s
  one_qsmul hWV s := gluedQsmul_one k U g hWV s
  mul_qsmul hWV r r' s := gluedQsmul_mul k U g hWV r r' s
  add_qsmul hWV r r' s := gluedQsmul_add_left k U g hWV r r' s
  qsmul_add hWV r s t := gluedQsmul_add k U g hWV r s t
  secRes_qsmul hW'W hWV r s := gluedRes_gluedQsmul k U g hW'W hWV r s
  exists_secRes_eq_qsmul_pow hV' hV'V q c :=
    exists_gluedRes_eq_gluedQsmul_pow k U g hc hP hcov hV' hV'V q c
  exists_qsmul_pow_eq_zero hV' hV'V q t ht :=
    exists_gluedQsmul_pow_eq_zero k U g hP hcov hV' hV'V q t ht

end Assembly

end AlgebraicGeometry
