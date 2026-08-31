/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.FiberLattice
import AlgebraicJacobian.RiemannRoch.Ledger.DivisorSheafQcoh
import AlgebraicJacobian.RiemannRoch.Ledger.ChiFiniteness
import AlgebraicJacobian.RiemannRoch.Ledger.Finiteness

/-!
# The H¹-quotient identification and the fibrewise large-twist vanishing

For the curve bundle `Y` (integral, smooth of relative dimension one and quasi-compact over a
field `K`) with a dominant affine morphism `π : Y ⟶ ℙ¹` and its fiber divisor
`F = fiberWeilDivisor π` (`Ledger/FiberDivisor.lean`): `H¹(𝒪(D + n·F))` vanishes for all large
`n`, for every Weil divisor `D`.

## WHAT THIS IS AND IS NOT — read before consuming it

This is **single-field** vanishing, in the twist direction of one fixed `π`.  Three statements
are routinely conflated; this file supplies the first and neither of the other two.

1. **Single-field bounded vanishing (this file, plus `Ledger/DegreeVanishing.lean`).**  For a
   fixed `K` and a fixed curve, `H¹(𝒪(D)) = 0` once `D` is large.  Here "large" means far
   enough along the tower `D + n·F`; `DegreeVanishing.subsingleton_hModule_one_of_deg_ge`
   converts that into a **degree** half-space once any single base vanishing is in hand, and
   `Ledger/FiberBound.lean` performs that conversion with the base supplied from here.
2. **Extension-uniformity.**  A bound *uniform over field extensions* `κ/K` — one threshold
   serving `C_κ` for every finite `κ`.  **Nothing here provides this**, and nothing in AJC or
   AJCR does: the AJCR analogue (`RiemannRoch/WindowFieldTransport.lean`) transports vanishing
   *facts* one field at a time precisely because the ledger constants are per-field
   `Classical.choose` values that do not transport.  The `n₀` below is existential and depends
   on `D` and `π`; the degree bound of item 1 depends on `χ(𝒪_Y)` and `deg`, both over the one
   field `K`.
3. **Global generation.**  Surjectivity of evaluation `H⁰(𝒪(D)) → 𝒪(D)⊗κ(x)`.  Independent of
   both: it is proved in `Ledger/DegreeVanishing.lean` off the dévissage slice, and neither
   implies nor follows from vanishing without the exactness input.

## The identification

On the affine two-cover `V₀ = π⁻¹ D₊(X₀)`, `V₁ = π⁻¹ D₊(X₁)`, the general-coefficients
two-cover carrier `Scheme.twoCoverH1LinearEquiv` — its two affine vanishing instances
discharged by the quasi-coherence packaging of `Ledger/DivisorSheafQcoh.lean` —
computes `H¹` of the twisted sheaf `𝒪(D + n·F)` as a cokernel of section modules. This
file identifies that cokernel with a quotient of the **fixed** ambient overlap lattice
`N = 𝒪(D)(V₀ ⊓ V₁)` (constant in `n`, by the landed overlap-constancy
`divisorSections_add_nsmul_fiberWeilDivisor_overlap`) by the fiber lattice `Aₙ` of
`Ledger/FiberLattice.lean`, comapped through `N.subtype` — the one
submodule-of-submodule bridge, paid once behind the named submodule
`AlgebraicGeometry.fiberLatticeOverlap`:

`AlgebraicGeometry.fiberLatticeH1Equiv :
  HModule (𝒪(D + n·F)) 1 ≃ₗ[K] N ⧸ fiberLatticeOverlap π D n`.

## The endgame

`Submodule.eventually_eq_top_of_monotone_of_iSup_eq_top` is the qualitative linear-algebra
stabilization. The quantitative refinement
`Submodule.eq_top_at_finrank_quotient_of_monotone_of_iSup_eq_top_of_stable` reaches the top by
the dimension of the initial quotient whenever one plateau propagates to the next. Instantiated
with `Aₙ` inside `N`:

* the chain is increasing (`fiberLattice_mono`) and exhausts `N` (`iSup_fiberLattice`,
  THE EXHAUSTION — pole clearing at the finite fiber over `[1 : 0]`);
* `N ⧸ A₀` is finite-dimensional: it is `H¹(𝒪(D + 0·F))` through the identification, and
  every divisor sheaf has finite `H¹` by the landed dévissage
  (`moduleFinite_hModule_divisorSheaf_one`, `Ledger/ChiFiniteness.lean`)
  — the only place the base finiteness (properness) inputs enter;
* multiplication by the inverse fiber coordinate advances the chart-zero summand and preserves
  the chart-one summand, so a plateau propagates (`fiberLattice_stable`).

Thus `Aₙ = ⊤` by `n = dim (N ⧸ A₀) = h¹(𝒪(D))`, yielding the explicit theorem
`subsingleton_hModule_divisorSheaf_one_at_h1_of_isDominant_toP1`. The qualitative
**fibrewise large-twist vanishing**
(`AlgebraicGeometry.subsingleton_hModule_divisorSheaf_one_of_isDominant_toP1`): per-`D`
`n₀`, no duality, no `R¹f_*`, remains as a compatibility interface. The finite-map forms
(`subsingleton_hModule_divisorSheaf_one_of_isFinite_toP1` and
`subsingleton_hModule_divisorSheaf_one_at_h1_of_isFinite_toP1`) discharge the base
`H¹(𝒪_Y)`-finiteness input from finiteness of `π`
(`moduleFinite_hModule_one_of_isFinite_toP1`).

## Provenance

The quotient carrier and qualitative stabilization originated in AJCR
`RiemannRoch/FLVVanishing.lean`. AJC adds the plateau-propagation and explicit `h¹` bound here;
the carrier substitution is described in `Ledger/DivisorSheafQcoh.lean` and the result is read
against AJC's own χ-ledger in `Ledger/FiberBound.lean`.
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits Opposite TopologicalSpace

section Stabilization

/-- **Noetherian stabilization of an exhausting chain.** An increasing `ℕ`-chain of
submodules whose join is everything and whose base term has Noetherian quotient is
eventually everything: the images of the chain in the quotient by the base term stabilize,
and the stabilized image must be the whole quotient. This is the pure linear-algebra
endgame of the fibrewise large-twist vanishing. -/
theorem Submodule.eventually_eq_top_of_monotone_of_iSup_eq_top {R : Type u} {M : Type v}
    [Ring R] [AddCommGroup M] [Module R M] {A : ℕ → Submodule R M} (hmono : Monotone A)
    (hsup : ⨆ n, A n = ⊤) [IsNoetherian R (M ⧸ A 0)] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, A n = ⊤ := by
  set f : ℕ →o Submodule R (M ⧸ A 0) :=
    ⟨fun n => (A n).map (A 0).mkQ, fun a b hab => Submodule.map_mono (hmono hab)⟩ with hf
  obtain ⟨n₀, hn₀⟩ :=
    monotone_stabilizes_iff_noetherian.mpr ‹IsNoetherian R (M ⧸ A 0)› f
  have hftop : f n₀ = ⊤ := by
    have h1 : ⨆ n, f n = ⊤ := by
      have h2 : ⨆ n, f n = Submodule.map (A 0).mkQ (⨆ n, A n) :=
        (Submodule.map_iSup _ _).symm
      rw [h2, hsup, Submodule.map_top, Submodule.range_mkQ]
    have h3 : ∀ m, f m ≤ f n₀ := fun m => by
      rcases le_total m n₀ with h | h
      · exact f.mono h
      · exact (hn₀ m h).ge
    have h4 : (⊤ : Submodule R (M ⧸ A 0)) ≤ f n₀ := by
      rw [← h1]; exact iSup_le h3
    exact le_antisymm le_top h4
  refine ⟨n₀, fun n hn => ?_⟩
  have hfn : (A n).map (A 0).mkQ = ⊤ := by
    have h5 : f n = ⊤ := by rw [← hn₀ n hn]; exact hftop
    exact h5
  have hcomap := congrArg (Submodule.comap (A 0).mkQ) hfn
  rwa [Submodule.comap_map_mkQ, Submodule.comap_top,
    sup_eq_right.mpr (hmono (Nat.zero_le n))] at hcomap

/-- **Quantitative stabilization of a plateau-propagating chain.** An exhausting increasing
chain in a finite-dimensional space reaches the top by the ambient dimension, provided any
equality between consecutive terms propagates to the following step. Indeed, before the top is
reached every inclusion is strict, so each step raises finrank. -/
theorem Submodule.eq_top_at_finrank_of_monotone_of_iSup_eq_top_of_stable
    {K : Type u} {M : Type v} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] {A : ℕ → Submodule K M}
    (hmono : Monotone A) (hsup : ⨆ n, A n = ⊤)
    (hstable : ∀ n, A n = A n.succ → A n.succ = A n.succ.succ) :
    A (Module.finrank K M) = ⊤ := by
  have hplateau_top (n : ℕ) (h : A n = A n.succ) : A n = ⊤ := by
    have hstep : ∀ k : ℕ, A (n + k) = A (n + k).succ := by
      intro k
      induction k with
      | zero => simpa only [Nat.add_zero] using h
      | succ k ih =>
        rw [Nat.add_succ]
        exact hstable (n + k) ih
    have htail : ∀ k : ℕ, A (n + k) = A n := by
      intro k
      induction k with
      | zero => simp only [Nat.add_zero]
      | succ k ih =>
        rw [Nat.add_succ, ← hstep k, ih]
    apply eq_top_iff.mpr
    rw [← hsup]
    refine iSup_le (fun m => ?_)
    rcases le_total m n with hmn | hnm
    · exact hmono hmn
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
      rw [htail k]
  have hstrict (n : ℕ) (hn : A n ≠ ⊤) : A n < A n.succ := by
    refine lt_of_le_of_ne (hmono (Nat.le_succ n)) ?_
    exact fun h => hn (hplateau_top n h)
  by_contra htop
  have hdim : ∀ n ≤ Module.finrank K M, n ≤ Module.finrank K (A n) := by
    intro n hn
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have hn' : n ≤ Module.finrank K M := Nat.le_trans (Nat.le_succ n) hn
      have hne : A n ≠ ⊤ := by
        intro hAn
        have hle : A n ≤ A (Module.finrank K M) := hmono hn'
        exact htop (eq_top_mono hle hAn)
      have hlt := Submodule.finrank_lt_finrank_of_lt (hstrict n hne)
      exact Nat.succ_le_of_lt (ih hn' |>.trans_lt hlt)
  have hlt := Submodule.finrank_lt htop
  exact (not_lt_of_ge (hdim _ le_rfl)) hlt

/-- Quotient form of quantitative stabilization. The bound is the dimension of the initial
quotient rather than the generally much larger ambient module. -/
theorem Submodule.eq_top_at_finrank_quotient_of_monotone_of_iSup_eq_top_of_stable
    {K : Type u} {M : Type v} [Field K] [AddCommGroup M] [Module K M]
    {A : ℕ → Submodule K M} (hmono : Monotone A) (hsup : ⨆ n, A n = ⊤)
    [FiniteDimensional K (M ⧸ A 0)]
    (hstable : ∀ n, A n = A n.succ → A n.succ = A n.succ.succ) :
    A (Module.finrank K (M ⧸ A 0)) = ⊤ := by
  let B : ℕ → Submodule K (M ⧸ A 0) := fun n => (A n).map (A 0).mkQ
  have hmonoB : Monotone B := fun _ _ h => Submodule.map_mono (hmono h)
  have hsupB : ⨆ n, B n = ⊤ := by
    calc
      (⨆ n, B n) = Submodule.map (A 0).mkQ (⨆ n, A n) :=
        (Submodule.map_iSup _ _).symm
      _ = ⊤ := by rw [hsup, Submodule.map_top, Submodule.range_mkQ]
  have hstableB : ∀ n, B n = B n.succ → B n.succ = B n.succ.succ := by
    intro n h
    have hc := congrArg (Submodule.comap (A 0).mkQ) h
    change Submodule.comap (A 0).mkQ (Submodule.map (A 0).mkQ (A n)) =
      Submodule.comap (A 0).mkQ (Submodule.map (A 0).mkQ (A n.succ)) at hc
    rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ,
      sup_eq_right.mpr (hmono (Nat.zero_le n)),
      sup_eq_right.mpr (hmono (Nat.zero_le n.succ))] at hc
    exact congrArg (Submodule.map (A 0).mkQ) (hstable n hc)
  have hB := Submodule.eq_top_at_finrank_of_monotone_of_iSup_eq_top_of_stable
    hmonoB hsupB hstableB
  change Submodule.map (A 0).mkQ (A (Module.finrank K (M ⧸ A 0))) = ⊤ at hB
  have hc := congrArg (Submodule.comap (A 0).mkQ) hB
  rwa [Submodule.comap_map_mkQ, Submodule.comap_top,
    sup_eq_right.mpr (hmono (Nat.zero_le _))] at hc

end Stabilization

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

section Carrier

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  (π : Y ⟶ P1 K) [IsDominant π]

/-- **The fiber lattice inside the fixed ambient overlap module** (the bridge
submodule): the Čech `H¹` denominator `Aₙ = 𝒪(D + n·F)(V₀) ⊔ 𝒪(D + n·F)(V₁)` of
`Ledger/FiberLattice.lean`, viewed as a submodule of the fixed ambient
`N = 𝒪(D)(V₀ ⊓ V₁)` through `N.subtype` (`fiberLattice_le_overlap` certifies the
containment). All submodule-of-submodule bookkeeping of the campaign is sealed behind
this definition. -/
noncomputable def fiberLatticeOverlap (D : Y.CurveDivisor) (n : ℕ) :
    Submodule K (divisorSections K D (fiberChart₀ π ⊓ fiberChart₁ π)) :=
  (fiberLattice π D n).comap
    (divisorSections K D (fiberChart₀ π ⊓ fiberChart₁ π)).subtype

lemma mem_fiberLatticeOverlap {D : Y.CurveDivisor} {n : ℕ}
    {s : divisorSections K D (fiberChart₀ π ⊓ fiberChart₁ π)} :
    s ∈ fiberLatticeOverlap π D n ↔ (s : Y.functionField) ∈ fiberLattice π D n :=
  Iff.rfl

/-- The fiber lattice inside the ambient overlap module is an increasing chain
(`fiberLattice_mono` comapped). -/
lemma fiberLatticeOverlap_mono (D : Y.CurveDivisor) :
    Monotone (fiberLatticeOverlap π D) := fun _ _ h =>
  Submodule.comap_mono ((monotone_nat_of_le_succ (fiberLattice_mono π D)) h)

/-- **Exhaustion inside the ambient** (`iSup_fiberLattice` comapped): the increasing chain
`Aₙ` fills the whole of `N = 𝒪(D)(V₀ ⊓ V₁)`. -/
theorem iSup_fiberLatticeOverlap (D : Y.CurveDivisor) :
    ⨆ n, fiberLatticeOverlap π D n = ⊤ := by
  rw [eq_top_iff]
  rintro s -
  have hs : (s : Y.functionField) ∈ ⨆ n, fiberLattice π D n := by
    rw [iSup_fiberLattice π D]
    exact s.2
  obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _
    (monotone_nat_of_le_succ (fiberLattice_mono π D)).directed_le).mp hs
  exact Submodule.mem_iSup_of_mem m hm

/-- A plateau in the fiber lattice remains a plateau after passing to the fixed overlap
ambient. This is the stability input for quantitative finite-dimensional stabilization. -/
theorem fiberLatticeOverlap_stable (D : Y.CurveDivisor) (n : ℕ)
    (h : fiberLatticeOverlap π D n = fiberLatticeOverlap π D n.succ) :
    fiberLatticeOverlap π D n.succ = fiberLatticeOverlap π D n.succ.succ := by
  have hfull : fiberLattice π D n = fiberLattice π D n.succ := by
    apply le_antisymm
    · exact fiberLattice_mono π D n
    · intro s hs
      have hsN : s ∈ divisorSections K D (fiberChart₀ π ⊓ fiberChart₁ π) :=
        fiberLattice_le_overlap π D n.succ hs
      have hs' : (⟨s, hsN⟩ : divisorSections K D (fiberChart₀ π ⊓ fiberChart₁ π)) ∈
          fiberLatticeOverlap π D n.succ := hs
      rw [← h] at hs'
      exact hs'
  unfold fiberLatticeOverlap
  rw [fiberLattice_stable π D n hfull]

variable [IsAffineHom π]

omit [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] in
/-- The underlying rational function of a difference of `𝒪(D)`-sections. -/
private lemma divisorVal_sub {D : Y.CurveDivisor} {W : Y.Opens}
    (a b : (Y.divisorSheaf K D).obj.obj (op W)) :
    divisorVal K (a - b) = divisorVal K a - divisorVal K b := rfl

omit [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsAffineHom π] in
/-- The underlying rational function of the two-cover restriction-difference of a pair of
sections of `𝒪(D')` on the π-charts: restriction preserves values, so the difference map
computes the literal difference in `K(Y)`. -/
private lemma divisorVal_moduleDiff (D' : Y.CurveDivisor)
    (t : ((Y.divisorSheaf K D').obj.obj (op (fiberChart₀ π)))
      × ((Y.divisorSheaf K D').obj.obj (op (fiberChart₁ π)))) :
    divisorVal K ((Y.twoCoverSquare (fiberChart₀ π) (fiberChart₁ π)
        (preimage_chartOpen_sup π)).moduleDiff (Y.divisorSheaf K D') t)
      = divisorVal K t.1 - divisorVal K t.2 := by
  have hov : ((fiberChart₀ π ⊓ fiberChart₁ π : Y.Opens) : Set Y).Nonempty :=
    ⟨genericPoint Y, genericPoint_mem_preimage_inf π⟩
  have h1 : divisorVal K
      (((Y.divisorSheaf K D').obj.map
        (Y.twoCoverSquare (fiberChart₀ π) (fiberChart₁ π)
          (preimage_chartOpen_sup π)).f₁₂.op).hom t.1) = divisorVal K t.1 :=
    divisorPresheaf_map_val K _ hov t.1
  have h2 : divisorVal K
      (((Y.divisorSheaf K D').obj.map
        (Y.twoCoverSquare (fiberChart₀ π) (fiberChart₁ π)
          (preimage_chartOpen_sup π)).f₁₃.op).hom t.2) = divisorVal K t.2 :=
    divisorPresheaf_map_val K _ hov t.2
  rw [GrothendieckTopology.MayerVietorisSquare.moduleDiff_apply, divisorVal_sub, h1, h2]

omit [IsAffineHom π] in
/-- **The range of the two-cover difference map is the fiber lattice** (the general-`F`
restatement of the landed structure-sheaf `range_diff_eq` of
`Ledger/Finiteness.lean`): a
section of `𝒪(D + n·F)` on the overlap is a difference of restrictions from `V₀` and `V₁`
exactly when its underlying rational function lies in
`Aₙ = 𝒪(D + n·F)(V₀) ⊔ 𝒪(D + n·F)(V₁)`. -/
private lemma range_moduleDiff_eq_comap (D : Y.CurveDivisor) (n : ℕ) :
    LinearMap.range ((Y.twoCoverSquare (fiberChart₀ π) (fiberChart₁ π)
        (preimage_chartOpen_sup π)).moduleDiff
        (Y.divisorSheaf K (D + n • fiberWeilDivisor π)))
      = (fiberLattice π D n).comap
          (divisorSections K (D + n • fiberWeilDivisor π)
            (fiberChart₀ π ⊓ fiberChart₁ π)).subtype := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨t, rfl⟩
    have hmem : divisorVal K ((Y.twoCoverSquare (fiberChart₀ π) (fiberChart₁ π)
          (preimage_chartOpen_sup π)).moduleDiff
          (Y.divisorSheaf K (D + n • fiberWeilDivisor π)) t) ∈ fiberLattice π D n := by
      rw [divisorVal_moduleDiff π (D + n • fiberWeilDivisor π) t]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (divisorVal_mem K t.1))
        (Submodule.mem_sup_right (divisorVal_mem K t.2))
    exact hmem
  · intro y hy
    have hy' : divisorVal K y ∈ fiberLattice π D n := hy
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy'
    refine ⟨((⟨a, ha⟩ : divisorSections K (D + n • fiberWeilDivisor π) (fiberChart₀ π)),
      (⟨-b, Submodule.neg_mem _ hb⟩ :
        divisorSections K (D + n • fiberWeilDivisor π) (fiberChart₁ π))), ?_⟩
    refine divisorSection_ext K ?_
    rw [divisorVal_moduleDiff π (D + n • fiberWeilDivisor π)]
    have hfin : a - (-b) = divisorVal K y := by
      rw [sub_neg_eq_add]
      exact hab
    exact hfin

/-- Mapping the comap of a submodule along `LinearEquiv.ofEq` of equal submodules is the
comap along the other subtype. -/
private lemma map_ofEq_comap_subtype {R : Type u} {M : Type v} [Ring R] [AddCommGroup M]
    [Module R M] {p q : Submodule R M} (h : p = q) (A : Submodule R M) :
    Submodule.map (LinearEquiv.ofEq p q h : p →ₗ[R] q) (A.comap p.subtype)
      = A.comap q.subtype := by
  subst h
  rw [LinearEquiv.ofEq_rfl]
  simp

/-- **The H¹-quotient identification** (the carrier): the degree-one cohomology
of the twisted divisor sheaf `𝒪(D + n·F)` is the quotient of the **fixed** ambient overlap
lattice `N = 𝒪(D)(V₀ ⊓ V₁)` by the fiber lattice `Aₙ` viewed inside `N`. Composite of the
two-cover carrier `Scheme.twoCoverH1LinearEquiv` (its affine vanishing instances
discharged by the `QcohOn` packaging of `Ledger/DivisorSheafQcoh.lean`), the
range identification `range (moduleDiff) = Aₙ`, and the overlap-constancy
`𝒪(D + n·F)(V₀ ⊓ V₁) = N` of `Ledger/FiberLattice.lean`. -/
noncomputable def fiberLatticeH1Equiv (D : Y.CurveDivisor) (n : ℕ) :
    Sheaf.HModule (Y.divisorSheaf K (D + n • fiberWeilDivisor π)) 1 ≃ₗ[K]
      (divisorSections K D (fiberChart₀ π ⊓ fiberChart₁ π)
        ⧸ fiberLatticeOverlap π D n) :=
  haveI : Subsingleton (Sheaf.HModule'
      (Y.divisorSheaf K (D + n • fiberWeilDivisor π)) (fiberChart₀ π) 1) :=
    (isAffineOpen_preimage_chartOpen π 0).subsingleton_hModule'_divisorSheaf_one K _
  haveI : Subsingleton (Sheaf.HModule'
      (Y.divisorSheaf K (D + n • fiberWeilDivisor π)) (fiberChart₁ π) 1) :=
    (isAffineOpen_preimage_chartOpen π 1).subsingleton_hModule'_divisorSheaf_one K _
  (Scheme.twoCoverH1LinearEquiv K Y (fiberChart₀ π) (fiberChart₁ π)
      (Y.divisorSheaf K (D + n • fiberWeilDivisor π)) (preimage_chartOpen_sup π)).trans
    ((Submodule.quotEquivOfEq _ _ (range_moduleDiff_eq_comap π D n)).trans
      (Submodule.Quotient.equiv _ _
        (LinearEquiv.ofEq _ _ (divisorSections_add_nsmul_fiberWeilDivisor_overlap π D n))
        (map_ofEq_comap_subtype
          (divisorSections_add_nsmul_fiberWeilDivisor_overlap π D n)
          (fiberLattice π D n))))

/-- **Explicit fiber-twist vanishing at the initial `h¹`.** The fiber lattice reaches the
overlap ambient after at most
`h¹(𝒪(D)) = dim (N / A₀)` strict steps. Consequently twisting `D` by exactly that many copies
of the fiber divisor kills `H¹`. This is the quantitative form needed for field-uniform
arguments: its index is intrinsic to `D`, rather than an independently chosen stabilization
threshold. -/
theorem subsingleton_hModule_divisorSheaf_one_at_h1_of_isDominant_toP1
    [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
    [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]
    (D : Y.CurveDivisor) :
    Subsingleton (Sheaf.HModule (Y.divisorSheaf K
      (D + Sheaf.h1 (Y.divisorSheaf K D) • fiberWeilDivisor π)) 1) := by
  haveI hfin : Module.Finite K
      (divisorSections K D (fiberChart₀ π ⊓ fiberChart₁ π)
        ⧸ fiberLatticeOverlap π D 0) :=
    Module.Finite.equiv (fiberLatticeH1Equiv π D 0)
  have htop :=
    Submodule.eq_top_at_finrank_quotient_of_monotone_of_iSup_eq_top_of_stable
      (fiberLatticeOverlap_mono π D) (iSup_fiberLatticeOverlap π D)
      (fiberLatticeOverlap_stable π D)
  have hindex : Module.finrank K
      (divisorSections K D (fiberChart₀ π ⊓ fiberChart₁ π)
        ⧸ fiberLatticeOverlap π D 0) = Sheaf.h1 (Y.divisorSheaf K D) := by
    have hzero : D + (0 : ℕ) • fiberWeilDivisor π = D := by
      simp
    change Module.finrank K
      (divisorSections K D (fiberChart₀ π ⊓ fiberChart₁ π)
        ⧸ fiberLatticeOverlap π D 0) =
          Module.finrank K (Sheaf.HModule (Y.divisorSheaf K D) 1)
    have heq := (LinearEquiv.finrank_eq (fiberLatticeH1Equiv π D 0)).symm
    rw [hzero] at heq
    exact heq
  rw [hindex] at htop
  haveI : Subsingleton
      (divisorSections K D (fiberChart₀ π ⊓ fiberChart₁ π)
        ⧸ fiberLatticeOverlap π D (Sheaf.h1 (Y.divisorSheaf K D))) :=
    Submodule.Quotient.subsingleton_iff.mpr htop
  exact (fiberLatticeH1Equiv π D (Sheaf.h1 (Y.divisorSheaf K D))).toEquiv.subsingleton

/-- **Fibrewise large-twist vanishing** (the headline; conditional form
for a dominant affine `π : Y ⟶ ℙ¹`): for every Weil divisor `D` on the curve bundle `Y`,
the degree-one cohomology of the twisted divisor sheaf `𝒪(D + n·F)`, `F` the fiber divisor
of `π`, vanishes for all sufficiently large `n`. The bound `n₀` is per-class and
non-effective — Noetherian stabilization of the exhausting fiber-lattice chain inside the
finite-codimension ambient `N`; no duality, no
`R¹f_*`. The two `Module.Finite` hypotheses are the structure-sheaf properness inputs of
the landed dévissage (`moduleFinite_hModule_divisorSheaf_one`). -/
theorem subsingleton_hModule_divisorSheaf_one_of_isDominant_toP1
    [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
    [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]
    (D : Y.CurveDivisor) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Subsingleton
        (Sheaf.HModule (Y.divisorSheaf K (D + n • fiberWeilDivisor π)) 1) := by
  haveI hfin : Module.Finite K
      (divisorSections K D (fiberChart₀ π ⊓ fiberChart₁ π)
        ⧸ fiberLatticeOverlap π D 0) :=
    Module.Finite.equiv (fiberLatticeH1Equiv π D 0)
  obtain ⟨n₀, hn₀⟩ := Submodule.eventually_eq_top_of_monotone_of_iSup_eq_top
    (fiberLatticeOverlap_mono π D) (iSup_fiberLatticeOverlap π D)
  refine ⟨n₀, fun n hn => ?_⟩
  haveI : Subsingleton (divisorSections K D (fiberChart₀ π ⊓ fiberChart₁ π)
      ⧸ fiberLatticeOverlap π D n) :=
    Submodule.Quotient.subsingleton_iff.mpr (hn₀ n hn)
  exact (fiberLatticeH1Equiv π D n).toEquiv.subsingleton

end Carrier

section Main

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]

/-- **Fibrewise large-twist vanishing along a finite map**: for a **finite** dominant
`π : Y ⟶ ℙ¹` compatible
with the structure morphisms, the base `H¹(𝒪_Y)`-finiteness input is discharged from
finiteness of `π` (`moduleFinite_hModule_one_of_isFinite_toP1`); only the `H⁰` properness
input remains a hypothesis. -/
theorem subsingleton_hModule_divisorSheaf_one_of_isFinite_toP1
    [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
    (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K)) (D : Y.CurveDivisor) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Subsingleton
        (Sheaf.HModule (Y.divisorSheaf K (D + n • fiberWeilDivisor π)) 1) :=
  haveI : Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1) :=
    moduleFinite_hModule_one_of_isFinite_toP1 π hπ
  subsingleton_hModule_divisorSheaf_one_of_isDominant_toP1 π D

/-- Finite-map form of explicit fiber-twist vanishing at the initial `h¹`; finiteness of `π`
supplies the structure-sheaf `H¹` finiteness input. -/
theorem subsingleton_hModule_divisorSheaf_one_at_h1_of_isFinite_toP1
    [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
    (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K)) (D : Y.CurveDivisor) :
    Subsingleton (Sheaf.HModule (Y.divisorSheaf K
      (D + Sheaf.h1 (Y.divisorSheaf K D) • fiberWeilDivisor π)) 1) := by
  haveI : Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1) :=
    moduleFinite_hModule_one_of_isFinite_toP1 π hπ
  exact subsingleton_hModule_divisorSheaf_one_at_h1_of_isDominant_toP1 π D

end Main

end AlgebraicGeometry
