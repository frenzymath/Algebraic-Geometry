/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowRelationFlat
import AlgebraicJacobian.Picard.FlatCokernel

/-!
# Canonical syzygies in a high-window multiplication presentation

The high-window relation criterion is deliberately stated with a residue-fibre
kernel-spanning hypothesis.  This file constructs the canonical candidate, the
actual kernel of the multiplication presentation, proves it finite, and identifies
its spanning condition with fibrewise injectivity of the injectivized map.

Flatness of the target cokernel implies that condition.  Conversely, the landed
flattening criterion shows that the condition implies target-cokernel flatness.
Consequently, merely choosing the actual kernel does not evade the nonreduced-base
gate: its fibre-spanning law is equivalent to the flatness one is trying to prove.
No fibrewise image-persistence statement is used as a substitute for this law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

/-! ## The `rTensor` form of flat-cokernel purity -/

section KernelSpan

variable {R : Type u} [CommRing R]
variable {M N : Type u} [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

/-- Kernel spanning after base change is equivalent to injectivity after first
dividing the source by the global kernel.  This is pure linear algebra and holds
for an arbitrary coefficient module `A`.

The forward direction lifts through the right-exact base change of the quotient
map.  The reverse direction observes that an element in the fibre kernel has zero
image in the fibre of the injectivization, hence already lies in the fibre image
of the global kernel. -/
theorem ker_rTensor_le_range_subtype_iff_liftQ_rTensor_injective
    (f : M →ₗ[R] N) (A : Type u) [AddCommGroup A] [Module R A] :
    LinearMap.ker (f.rTensor A) ≤
        LinearMap.range ((LinearMap.ker f).subtype.rTensor A) ↔
      Function.Injective
        (((LinearMap.ker f).liftQ f le_rfl).rTensor A) := by
  let L := LinearMap.ker f
  have hcomp : f.rTensor A =
      (L.liftQ f le_rfl).rTensor A ∘ₗ L.mkQ.rTensor A := by
    rw [← LinearMap.rTensor_comp, Submodule.liftQ_mkQ]
  have hexact : Function.Exact (L.subtype.rTensor A) (L.mkQ.rTensor A) :=
    rTensor_exact A (LinearMap.exact_subtype_mkQ L) (Submodule.mkQ_surjective L)
  constructor
  · intro hspan
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨x, rfl⟩ := LinearMap.rTensor_surjective A
      (Submodule.mkQ_surjective L) w
    have hfx : f.rTensor A x = 0 := by
      rw [hcomp, LinearMap.comp_apply]
      exact hw
    have hx := hspan (LinearMap.mem_ker.mpr hfx)
    rw [← LinearMap.exact_iff.mp hexact, LinearMap.mem_ker] at hx
    exact hx
  · intro hinj x hx
    have hzero : L.mkQ.rTensor A x = 0 := by
      apply hinj
      rw [map_zero]
      have hfx := LinearMap.mem_ker.mp hx
      rw [hcomp, LinearMap.comp_apply] at hfx
      exact hfx
    rw [← LinearMap.exact_iff.mp hexact, LinearMap.mem_ker]
    exact hzero

variable {P : Type u} [AddCommGroup P] [Module R P]

/-- An independent boundary presentation of every base-changed kernel makes
the injectivized map remain injective after that base change.  This is the
non-circular bridge from a fibrewise Koszul theorem to the relative flatness
criterion: no flatness of the cokernel is assumed.

The proof lifts through the right-exact base change of `ker(f).mkQ`.  A lift
in the fibre kernel is a base-changed boundary by `hspan`, and the global
identity `f ∘ d = 0` makes its quotient class vanish. -/
theorem liftQ_baseChange_injective_of_boundary
    (f : M →ₗ[R] N) (d : P →ₗ[R] M) (hfd : f.comp d = 0)
    (S : Type u) [CommRing S] [Algebra R S]
    (hspan : LinearMap.ker (LinearMap.baseChange S f) ≤
      LinearMap.range (LinearMap.baseChange S d)) :
    Function.Injective
      (LinearMap.baseChange S ((LinearMap.ker f).liftQ f le_rfl)) := by
  let L := LinearMap.ker f
  let fbar := L.liftQ f le_rfl
  have hfcomp : LinearMap.baseChange S f =
      (LinearMap.baseChange S fbar).comp (LinearMap.baseChange S L.mkQ) := by
    rw [← LinearMap.baseChange_comp, Submodule.liftQ_mkQ]
  have hdL : ∀ y : P, d y ∈ L := by
    intro y
    apply LinearMap.mem_ker.mpr
    have hy := LinearMap.congr_fun hfd y
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hy
  have hqd : L.mkQ.comp d = 0 := by
    apply LinearMap.ext
    intro y
    rw [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hdL y
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨x, rfl⟩ := LinearMap.baseChange_surjective S
    (Submodule.mkQ_surjective L) w
  have hfx : LinearMap.baseChange S f x = 0 := by
    rw [hfcomp, LinearMap.comp_apply]
    exact hw
  obtain ⟨y, hy⟩ := hspan (LinearMap.mem_ker.mpr hfx)
  rw [← hy, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hqd,
    LinearMap.baseChange_zero, LinearMap.zero_apply]

set_option maxHeartbeats 800000 in
-- Elaborating the quotient injectivization through tensor purity exceeds the default budget.
/-- Flatness of the target cokernel forces the fibre kernel to be generated by
the base-changed global kernel.  Indeed, the injectivization
`M ⧸ ker δ → N` has cokernel `N ⧸ range δ`; flatness of that cokernel makes the
injectivization universally injective. -/
theorem ker_rTensor_le_range_subtype_of_flat_range_quotient
    (δ : M →ₗ[R] N)
    [Module.Flat R (N ⧸ LinearMap.range δ)]
    (A : Type u) [AddCommGroup A] [Module R A] :
    LinearMap.ker (δ.rTensor A) ≤
      LinearMap.range ((LinearMap.ker δ).subtype.rTensor A) := by
  apply (ker_rTensor_le_range_subtype_iff_liftQ_rTensor_injective δ A).mpr
  set fbar := (LinearMap.ker δ).liftQ δ le_rfl with hfbar
  have hfbar_inj : Function.Injective fbar := by
    rw [← LinearMap.ker_eq_bot, hfbar]
    exact Submodule.ker_liftQ_eq_bot' _ δ rfl
  have hexact : Function.Exact fbar (LinearMap.range δ).mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, hfbar, Submodule.range_liftQ]
  have hleft : Function.Injective (fbar.lTensor A) :=
    LinearMap.lTensor_injective_of_exact_of_flat
      (LinearMap.range δ).mkQ (Submodule.mkQ_surjective _)
      fbar hfbar_inj hexact A
  exact (LinearMap.lTensor_inj_iff_rTensor_inj (M := A) (f := fbar)).mp hleft

end KernelSpan

/-! ## Specialization to the recursive high-window map -/

section HighWindowSyzygy

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowSyzygy :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k ((windowS_choice pi hpi g • fiberWeilDivisor pi) +
    (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j

set_option maxHeartbeats 1600000 in
-- The dependent high-window multiplication kernel exceeds the default elaboration budget.
set_option synthInstance.maxHeartbeats 400000 in
-- Its carve-ring module instances require deeper synthesis than the global default.
/-- The canonical finite candidate for the high-window syzygy module: the
actual kernel of the multiplication presentation. -/
noncomputable abbrev divUniversalHighWindowKernelSyzygy (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n)) :
    Submodule RZ
      (DivUniversalHighWindowMulSource (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K) :=
  LinearMap.ker (divUniversalHighWindowMulMap (C := C) (pi := pi)
    hpi g r1 r2 b1 b2 i j n K)

set_option maxHeartbeats 1600000 in
-- Finiteness unfolds the dependent multiplication source and kernel.
set_option synthInstance.maxHeartbeats 400000 in
-- Noetherian submodule finiteness traverses the full carve-ring instance chain.
/-- The canonical kernel syzygy is finite at every high window.  This uses only
Noetherianity of the carve-chart ring and finiteness of the preceding relation
module; it does not assert that its formation commutes with residue fields. -/
theorem finite_divUniversalHighWindowKernelSyzygy (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n))
    [Module.Finite RZ K] :
    Module.Finite RZ
      (divUniversalHighWindowKernelSyzygy (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K) := by
  letI := finite_divUniversalHighWindowMulSource
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n K
  infer_instance

set_option maxHeartbeats 1600000 in
-- The fibrewise equivalence elaborates a dependent quotient map at every prime.
set_option synthInstance.maxHeartbeats 400000 in
-- Residue-field tensor instances over the carve ring need the larger local budget.
/-- For the canonical kernel candidate, `DivUniversalHighWindowSyzygySpans` is
equivalent to residue-fibre injectivity of the injectivized multiplication map.
This is the precise rank/minor condition a relative persistence argument must
establish; fieldwise image persistence alone does not imply it. -/
theorem divUniversalHighWindowKernelSyzygySpans_iff (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n)) :
    DivUniversalHighWindowSyzygySpans (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K
        (divUniversalHighWindowKernelSyzygy (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n K) ↔
      ∀ p : PrimeSpectrum RZ,
        Function.Injective
          (((divUniversalHighWindowKernelSyzygy (C := C) (pi := pi)
              hpi g r1 r2 b1 b2 i j n K).liftQ
            (divUniversalHighWindowMulMap (C := C) (pi := pi)
              hpi g r1 r2 b1 b2 i j n K) le_rfl).rTensor
            p.asIdeal.ResidueField) := by
  constructor
  · intro h p
    exact (ker_rTensor_le_range_subtype_iff_liftQ_rTensor_injective
      (divUniversalHighWindowMulMap (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K) p.asIdeal.ResidueField).mp (h.2 p)
  · intro h
    refine ⟨le_rfl, fun p => ?_⟩
    exact (ker_rTensor_le_range_subtype_iff_liftQ_rTensor_injective
      (divUniversalHighWindowMulMap (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K) p.asIdeal.ResidueField).mpr (h p)

set_option maxHeartbeats 1600000 in
-- Specializing tensor purity to the dependent high-window map is elaboration-heavy.
set_option synthInstance.maxHeartbeats 400000 in
-- The target quotient's flatness instance unfolds the complete high-window ambient.
/-- The actual kernel of a high-window multiplication presentation is a valid
relative syzygy module if its target quotient is flat.  This is the purity
direction and does not infer flatness from fibrewise persistence. -/
theorem divUniversalHighWindowSyzygySpans_of_flat_quotient
    (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n))
    [Module.Flat RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
          (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) (n + 1) ⧸
        LinearMap.range (divUniversalHighWindowMulMap (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n K))] :
    DivUniversalHighWindowSyzygySpans (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n K
      (divUniversalHighWindowKernelSyzygy (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K) := by
  constructor
  · exact le_rfl
  · intro p
    exact ker_rTensor_le_range_subtype_of_flat_range_quotient
      (divUniversalHighWindowMulMap (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K) p.asIdeal.ResidueField

set_option maxHeartbeats 1600000 in
-- Comparing the syzygy criterion with the dependent successor quotient is expensive.
set_option synthInstance.maxHeartbeats 400000 in
-- The forward flattening theorem synthesizes finiteness and flatness of nested ambients.
/-- For a finite high-window relation module, the canonical kernel spans every
residue-fibre kernel if and only if the successor relation quotient is flat.

This equivalence is the `k[ε]` guard in its sharpest form: selecting the global
kernel as the syzygy module is finite and canonical, but its base-change law is
not a consequence of fieldwise image persistence.  A forward proof still needs
an independent relative syzygy/Gotzmann argument, or a flattening-locus refinement. -/
theorem divUniversalHighWindowKernelSyzygySpans_iff_flat_quotient
    (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n))
    [Module.Finite RZ K] :
    DivUniversalHighWindowSyzygySpans (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K
        (divUniversalHighWindowKernelSyzygy (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n K) ↔
      Module.Flat RZ
        (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
            (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) (n + 1) ⧸
          LinearMap.range (divUniversalHighWindowMulMap (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j n K)) := by
  constructor
  · intro h
    exact flat_divUniversalHighWindowMulSpanQuotient_of_syzygies
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n K
        (divUniversalHighWindowKernelSyzygy (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n K) h
  · intro hflat
    letI := hflat
    exact divUniversalHighWindowSyzygySpans_of_flat_quotient
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n K

end HighWindowSyzygy

end AlgebraicGeometry
