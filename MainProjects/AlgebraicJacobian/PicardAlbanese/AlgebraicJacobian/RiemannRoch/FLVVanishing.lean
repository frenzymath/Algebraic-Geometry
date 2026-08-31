/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.FLVLattice
import AlgebraicJacobian.RiemannRoch.FLVQcoh
import AlgebraicJacobian.RiemannRoch.ChiFiniteness
import AlgebraicJacobian.Cohomology.Finiteness

/-!
# FLV-2(b) + FLV-3 — the H¹-quotient identification and the fibrewise large-twist vanishing

The heart of the Wave-4 fibrewise-large-twist-vanishing campaign
(`informal/w4-flv-worksheet.md` §§2.1, 2.3, bricks FLV-2(b) and FLV-3), for the curve
bundle `Y` (integral, smooth of relative dimension one and quasi-compact over a field `K`)
with a dominant affine morphism `π : Y ⟶ ℙ¹` and its fiber divisor
`F = fiberWeilDivisor π` (`AlgebraicJacobian.RiemannRoch.FLVFiberToolkit`).

## The identification (FLV-2(b))

On the affine two-cover `V₀ = π⁻¹ D₊(X₀)`, `V₁ = π⁻¹ D₊(X₁)`, the general-coefficients
two-cover carrier `Scheme.twoCoverH1LinearEquiv` — its two affine vanishing instances
discharged by the quasi-coherence packaging of `AlgebraicJacobian.RiemannRoch.FLVQcoh` —
computes `H¹` of the twisted sheaf `𝒪(D + n·F)` as a cokernel of section modules. This
file identifies that cokernel with a quotient of the **fixed** ambient overlap lattice
`N = 𝒪(D)(V₀ ⊓ V₁)` (constant in `n`, by the landed overlap-constancy
`divisorSections_add_nsmul_fiberWeilDivisor_overlap`) by the fiber lattice `Aₙ` of
`AlgebraicJacobian.RiemannRoch.FLVLattice`, comapped through `N.subtype` — the one
submodule-of-submodule bridge of the campaign, paid once behind the named submodule
`AlgebraicGeometry.fiberLatticeOverlap` (worksheet discipline (2)):

`AlgebraicGeometry.fiberLatticeH1Equiv :
  HModule (𝒪(D + n·F)) 1 ≃ₗ[K] N ⧸ fiberLatticeOverlap π D n`.

## The endgame (FLV-3)

`Submodule.eventually_eq_top_of_monotone_of_iSup_eq_top` is the pure linear-algebra
stabilization: an increasing `ℕ`-chain of submodules with join `⊤` whose base has
Noetherian quotient is eventually `⊤` (images in the quotient by the base stabilize by
`monotone_stabilizes_iff_noetherian`, and the stabilized value must be everything).
Instantiated with `Aₙ` inside `N`:

* the chain is increasing (`fiberLattice_mono`) and exhausts `N` (`iSup_fiberLattice`,
  THE EXHAUSTION of FLV-1 — pole clearing at the finite fiber over `[1 : 0]`);
* `N ⧸ A₀` is finite-dimensional: it is `H¹(𝒪(D + 0·F))` through the identification, and
  every divisor sheaf has finite `H¹` by the landed dévissage
  (`moduleFinite_hModule_divisorSheaf_one`, `AlgebraicJacobian.RiemannRoch.ChiFiniteness`)
  — the only place the base finiteness (properness) inputs enter;

so `Aₙ = ⊤` for all large `n`, and through the identification the twisted `H¹` is a
subsingleton — **the fibrewise large-twist vanishing**
(`AlgebraicGeometry.subsingleton_hModule_divisorSheaf_one_of_isDominant_toP1`): per-class
`n₀`, no duality, no `R¹f_*`. The worksheet-shaped form for a finite dominant `π`
compatible with the structure morphisms
(`subsingleton_hModule_divisorSheaf_one_of_isFinite_toP1`) discharges the base
`H¹(𝒪_Y)`-finiteness input from finiteness of `π`
(`moduleFinite_hModule_one_of_isFinite_toP1`).
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits Opposite TopologicalSpace

section Stabilization

/-- **Noetherian stabilization of an exhausting chain.** An increasing `ℕ`-chain of
submodules whose join is everything and whose base term has Noetherian quotient is
eventually everything: the images of the chain in the quotient by the base term stabilize,
and the stabilized image must be the whole quotient. This is the pure linear-algebra
endgame of the fibrewise large-twist vanishing (`informal/w4-flv-worksheet.md` §2.1). -/
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

/-- **The fiber lattice inside the fixed ambient overlap module** (the FLV-2(b) bridge
submodule): the Čech `H¹` denominator `Aₙ = 𝒪(D + n·F)(V₀) ⊔ 𝒪(D + n·F)(V₁)` of
`AlgebraicJacobian.RiemannRoch.FLVLattice`, viewed as a submodule of the fixed ambient
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
`AlgebraicJacobian.Cohomology.Finiteness`, assigned to FLV-2 by the worksheet §2.3): a
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

/-- **The H¹-quotient identification** (FLV-2(b), the carrier): the degree-one cohomology
of the twisted divisor sheaf `𝒪(D + n·F)` is the quotient of the **fixed** ambient overlap
lattice `N = 𝒪(D)(V₀ ⊓ V₁)` by the fiber lattice `Aₙ` viewed inside `N`. Composite of the
two-cover carrier `Scheme.twoCoverH1LinearEquiv` (its affine vanishing instances
discharged by the `QcohOn` packaging of `AlgebraicJacobian.RiemannRoch.FLVQcoh`), the
range identification `range (moduleDiff) = Aₙ`, and the overlap-constancy
`𝒪(D + n·F)(V₀ ⊓ V₁) = N` of `AlgebraicJacobian.RiemannRoch.FLVLattice`. -/
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

/-- **Fibrewise large-twist vanishing** (FLV-fiber, the Wave-4 headline; conditional form
for a dominant affine `π : Y ⟶ ℙ¹`): for every Weil divisor `D` on the curve bundle `Y`,
the degree-one cohomology of the twisted divisor sheaf `𝒪(D + n·F)`, `F` the fiber divisor
of `π`, vanishes for all sufficiently large `n`. The bound `n₀` is per-class and
non-effective — Noetherian stabilization of the exhausting fiber-lattice chain inside the
finite-codimension ambient `N`, per `informal/w4-flv-worksheet.md` §2.1; no duality, no
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

/-- **Fibrewise large-twist vanishing along a finite map** (the worksheet-shaped form,
`informal/w4-flv-worksheet.md` §1.2): for a **finite** dominant `π : Y ⟶ ℙ¹` compatible
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

end Main

end AlgebraicGeometry
