/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import AlgebraicJacobian.Cohomology.QcohRestrictBasicOpen

/-!
# Quasi-coherent sheaves on an affine are sections-tilde (Stacks 01HV/01I8)

Project-local: the affine quasi-coherent structure theorem.  For an `𝒪_X`-module `F`
on an affine `X = Spec R`, with `M = Γ(X, F)`, there is a natural isomorphism
`F ≅ M^~`, under which `Γ(D(f), F) = M_f`.

## The Mathlib gradient

Mathlib's `AlgebraicGeometry.Modules.Tilde` development provides:

* `Scheme.Modules.fromTildeΓ F : tilde (Γ F) ⟶ F` — the counit of the
  tilde ⊣ global-sections adjunction;
* `isIso_fromTildeΓ_iff : IsIso F.fromTildeΓ ↔ (tilde.functor R).essImage F`;
* `isIso_fromTildeΓ_of_presentation F (P : F.Presentation) : IsIso F.fromTildeΓ` —
  the counit is an isomorphism whenever `F` admits a **global** presentation
  (a global generating family together with a global generating family of relations).

The genuine remaining gap — **Stacks Tag 01I8**, the affine equivalence
`QCoh(Spec R) ≃ Mod R` — is the implication

  `[IsQuasicoherent F]  ⟹  IsIso F.fromTildeΓ`   (on the affine `Spec R`).

`IsQuasicoherent F` only supplies *local* presentation data on a cover
(`QuasicoherentData`); turning that into a *global* presentation on the affine base
(or directly into membership of the essential image of `tilde`) is the content of the
affine equivalence and is not yet in Mathlib.  See the `## Handoff` section at the
bottom of this file for the precise decomposition.

This file therefore delivers the structure theorem **conditioned on the counit being
an isomorphism** (`qcoh_iso_tilde_sections`), and a ready-to-use **presentation form**
(`qcoh_iso_tilde_sections_of_presentation`) that discharges that condition via the
Mathlib presentation lemma.  Once the 01I8 instance
`[IsQuasicoherent F] → IsIso F.fromTildeΓ` lands, the conditional form upgrades to the
unconditional quasi-coherent statement with no further work.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-! ## Project-local Mathlib supplement — affine quasi-coherent structure theorem -/

/-- **Affine structure theorem, conditional form (Stacks 01HV).**  If the tilde–Γ counit
`tilde (Γ F) ⟶ F` of an `𝒪_{Spec R}`-module `F` is an isomorphism — which holds for every
quasi-coherent `F` (the 01I8 globalisation `[IsQuasicoherent F] → IsIso F.fromTildeΓ` is the
sole remaining gap; see `qcoh_iso_tilde_sections_of_presentation` for the presentation-based
discharge) — then `F` is isomorphic to the sheaf associated with its module of global
sections `M = Γ(Spec R, F)`.  Project-local because Mathlib exposes only the counit and the
`IsIso`-criterion, not this packaged `F ≅ M^~` form. -/
noncomputable def qcoh_iso_tilde_sections (F : (Spec R).Modules) [IsIso F.fromTildeΓ] :
    F ≅ tilde (moduleSpecΓFunctor.obj F) :=
  (asIso F.fromTildeΓ).symm

/-- **Affine structure theorem, presentation form (Stacks 01HV).**  An `𝒪_{Spec R}`-module
`F` that admits a *global* presentation (`F.Presentation`) is isomorphic to the sheaf
associated with its module of global sections `M = Γ(Spec R, F)`.  This discharges the
`IsIso F.fromTildeΓ` hypothesis of `qcoh_iso_tilde_sections` via Mathlib's
`isIso_fromTildeΓ_of_presentation`.  Project-local for the same packaging reason. -/
noncomputable def qcoh_iso_tilde_sections_of_presentation (F : (Spec R).Modules)
    (P : F.Presentation) : F ≅ tilde (moduleSpecΓFunctor.obj F) :=
  haveI := isIso_fromTildeΓ_of_presentation F P
  (asIso F.fromTildeΓ).symm

/-- The hom of `qcoh_iso_tilde_sections` is the inverse of the tilde–Γ counit. -/
@[simp]
lemma qcoh_iso_tilde_sections_hom (F : (Spec R).Modules) [IsIso F.fromTildeΓ] :
    (qcoh_iso_tilde_sections F).hom = inv F.fromTildeΓ :=
  rfl

/-- The inverse of `qcoh_iso_tilde_sections` is the tilde–Γ counit `tilde (Γ F) ⟶ F`. -/
@[simp]
lemma qcoh_iso_tilde_sections_inv (F : (Spec R).Modules) [IsIso F.fromTildeΓ] :
    (qcoh_iso_tilde_sections F).inv = F.fromTildeΓ :=
  rfl

/-! ### Reduction to global generation (Stacks 01I8, steps 2–3)

The unconditional quasi-coherent instance `[IsQuasicoherent F] → IsIso F.fromTildeΓ` is, by the
three-step 01I8 decomposition (`rem:o1i8_decomposition`), reduced to producing two *global*
generating families: one for `F` itself and one for the kernel of the resulting epimorphism.  The
declarations below formalise steps (2)–(3) — assembling those two families into a global
presentation and feeding it to Mathlib's `isIso_fromTildeΓ_of_presentation` — turning what were
prose steps in the Handoff into axiom-clean Lean.  The single remaining mathematical input is the
affine global-generation theorem (step (1)), which supplies the two `GeneratingSections`.
-/

/-- A finite-free / free `𝒪_{Spec R}`-module is quasi-coherent: it is the tilde of `ι →₀ R`
(`tildeFinsupp`), and quasi-coherence is closed under isomorphism.  Project-local supplement; used
to recognise the kernel-side coefficient sheaf of the 01I8 presentation route as quasi-coherent. -/
instance free_isQuasicoherent (ι : Type u) :
    (SheafOfModules.free.{u} (R := (Spec R).ringCatSheaf) ι).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent.{u} (Spec R).ringCatSheaf).prop_of_iso
    (tildeFinsupp (R := R) ι) inferInstance

/-- **01I8 steps (2)–(3), packaged.**  If an `𝒪_{Spec R}`-module `F` is globally generated
(`σ : F.GeneratingSections`, a global epimorphism `free σ.I ⟶ F`) and the kernel of that
epimorphism is itself globally generated (`τ : (kernel σ.π).GeneratingSections`), then the
tilde–Γ counit `tilde (Γ F) ⟶ F` is an isomorphism.  This bundles the two generating families
into a global `F.Presentation` and feeds it to Mathlib's `isIso_fromTildeΓ_of_presentation`; it is
the formal content of steps (2)–(3) of the 01I8 decomposition.  The single remaining mathematical
input is the affine global-generation theorem (step (1)) producing `σ` and `τ` for a quasi-coherent
`F`.  Project-local because it repackages the Mathlib presentation criterion in the
two-generating-families form the 01I8 route consumes. -/
lemma isIso_fromTildeΓ_of_genSections (F : (Spec R).Modules)
    (σ : F.GeneratingSections) (τ : (kernel σ.π).GeneratingSections) :
    IsIso F.fromTildeΓ := by
  have P : F.Presentation := { generators := σ, relations := τ }
  exact isIso_fromTildeΓ_of_presentation F P

/-- **Affine structure theorem from global generation (Stacks 01HV/01I8).**  An `𝒪_{Spec R}`-module
`F` that is globally generated (`σ`) together with a globally generated kernel of the generating
epimorphism (`τ`) is isomorphic to the sheaf associated with its module of global sections
`M = Γ(Spec R, F)`.  Discharges the `IsIso F.fromTildeΓ` hypothesis of `qcoh_iso_tilde_sections`
via `isIso_fromTildeΓ_of_genSections`.  Project-local for the same packaging reason; once the
affine global-generation theorem supplies `σ`/`τ` for quasi-coherent `F` the named
`qcoh_iso_tilde_sections` upgrades to the unconditional statement. -/
noncomputable def qcoh_iso_tilde_sections_of_genSections (F : (Spec R).Modules)
    (σ : F.GeneratingSections) (τ : (kernel σ.π).GeneratingSections) :
    F ≅ tilde (moduleSpecΓFunctor.obj F) :=
  haveI := isIso_fromTildeΓ_of_genSections F σ τ
  (asIso F.fromTildeΓ).symm

/-! ### Route P, step 0 — finite trivialising standard cover

The pure-topology brick of the global-generation route: any open cover of an affine
`Spec R` refines to a *finite* cover by basic opens, each contained in a cover member,
with the defining elements generating the unit ideal.  This is the common prerequisite
of the localisation-of-sections and global-generation steps. -/

/-- **Finite basic-open refinement of a cover of `Spec R` (Stacks 01I8, topology brick).**
Given a family of opens `U : ι → (Spec R).Opens` covering the whole space
(`⨆ i, U i = ⊤`), there are finitely many elements `f : Fin n → R` and indices
`φ : Fin n → ι` such that each basic open `D(f j)` lies inside `U (φ j)` and the `f j`
generate the unit ideal (equivalently the `D(f j)` already cover `Spec R`).  Project-local
because it packages the basis-refinement + quasicompactness of `Spec R` in the exact form
the Route-P localisation/global-generation lanes consume. -/
lemma exists_finite_basicOpen_subcover {ι : Type*} (U : ι → (Spec R).Opens)
    (hU : ⨆ i, U i = ⊤) :
    ∃ (n : ℕ) (f : Fin n → R) (φ : Fin n → ι),
      (∀ j, PrimeSpectrum.basicOpen (f j) ≤ U (φ j)) ∧ Ideal.span (Set.range f) = ⊤ := by
  classical
  -- pointwise: each `x` lies in a basic open contained in some cover member
  have hpt : ∀ x : PrimeSpectrum R, ∃ (g : R) (i : ι),
      x ∈ PrimeSpectrum.basicOpen g ∧ PrimeSpectrum.basicOpen g ≤ U i := by
    intro x
    have hxtop : x ∈ (⊤ : (Spec R).Opens) := trivial
    rw [← hU] at hxtop
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hxtop
    obtain ⟨V, hV, hxV, hVU⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.1
        (PrimeSpectrum.isBasis_basic_opens (R := R))) hi
    obtain ⟨g, rfl⟩ := hV
    exact ⟨g, i, hxV, hVU⟩
  choose g φ' hxg hgU using hpt
  -- quasicompactness: extract a finite subcover of the pointwise basic opens
  have hcover : (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ x, (PrimeSpectrum.basicOpen (g x) : Set (PrimeSpectrum R)) :=
    fun x _ => Set.mem_iUnion.2 ⟨x, hxg x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (PrimeSpectrum.basicOpen (g x) : Set (PrimeSpectrum R)))
    (fun x => (PrimeSpectrum.basicOpen (g x)).isOpen) hcover
  set e := t.equivFin with he
  refine ⟨t.card, fun j => g (e.symm j).val, fun j => φ' (e.symm j).val, fun j => hgU _, ?_⟩
  -- the chosen finite family of basic opens already covers `Spec R`
  rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff, eq_top_iff]
  intro x _
  rw [TopologicalSpace.Opens.mem_iSup]
  have hxu := ht (Set.mem_univ x)
  rw [Set.mem_iUnion₂] at hxu
  obtain ⟨y, hy, hxy⟩ := hxu
  refine ⟨e ⟨y, hy⟩, ?_⟩
  rw [Equiv.symm_apply_apply]
  exact hxy

/-! ## Project-local Mathlib supplement — `IsLocalizedModule` is local on a finite spanning cover

`isLocalizedModule_of_span_cover` (Stacks 01I8, P1b): the pure commutative-algebra patching
primitive feeding the localisation-of-sections step.  If an `R`-linear map `g : M → N` becomes a
localisation at the powers of `f` after localising at the powers of each member `s j` of a finite
unit-ideal-spanning family, then `g` is itself a localisation at the powers of `f`.  Proved directly
from the three defining clauses of `IsLocalizedModule` by descent along the spanning cover (the
partition-of-unity argument of the blueprint).  Project-local: Mathlib has the analogous
`Module.Finite`/`Module.FinitePresentation` span-descent lemmas but not this one for the
`IsLocalizedModule` predicate itself.
-/

section SpanCoverLocalization

variable {R : Type*} [CommRing R] {M N : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Partition of unity for a finite unit-ideal-spanning family raised to a uniform power:
if `s : Fin n → R` spans the unit ideal then so do the `A`-th powers, giving coefficients
`c` with `∑ j, c j * (s j) ^ A = 1`.  Project-local helper for `isLocalizedModule_of_span_cover`. -/
private lemma exists_sum_pow_eq_one {n : ℕ} (s : Fin n → R)
    (hs : Ideal.span (Set.range s) = ⊤) (A : ℕ) :
    ∃ c : Fin n → R, ∑ j, c j * (s j) ^ A = 1 := by
  have hspan : Ideal.span (Set.range fun j => (s j) ^ A) = ⊤ := by
    have h := Ideal.span_pow_eq_top (Set.range s) hs A
    rwa [← Set.range_comp] at h
  have h1 : (1 : R) ∈ Ideal.span (Set.range fun j => (s j) ^ A) := by rw [hspan]; trivial
  rw [Ideal.mem_span_range_iff_exists_fun] at h1
  exact h1

/-- Span-cover descent for membership in the range of a linear map: if `(s j) ^ A • w` lies in the
range of `g` for every member of a unit-ideal-spanning family, then `w` itself does.  Project-local
helper for the surjectivity clause of `isLocalizedModule_of_span_cover`. -/
private lemma mem_range_of_span_pow {n : ℕ} (s : Fin n → R)
    (hs : Ideal.span (Set.range s) = ⊤) (g : M →ₗ[R] N) (A : ℕ) (w : N)
    (hj : ∀ j, ∃ m : M, (s j) ^ A • w = g m) : ∃ m : M, w = g m := by
  obtain ⟨c, hc⟩ := exists_sum_pow_eq_one s hs A
  choose m hm using hj
  refine ⟨∑ j, c j • m j, ?_⟩
  rw [map_sum]
  calc w = (∑ j, c j * (s j) ^ A) • w := by rw [hc, one_smul]
    _ = ∑ j, (c j * (s j) ^ A) • w := by rw [Finset.sum_smul]
    _ = ∑ j, c j • ((s j) ^ A • w) := by simp_rw [mul_smul]
    _ = ∑ j, c j • g (m j) := by simp_rw [hm]
    _ = ∑ j, g (c j • m j) := by simp_rw [map_smul]

/-- Span-cover descent for vanishing: if `(s j) ^ A • w = 0` for every member of a
unit-ideal-spanning family, then `w = 0`.  Project-local helper for the equaliser clause of
`isLocalizedModule_of_span_cover`. -/
private lemma eq_zero_of_span_pow {n : ℕ} (s : Fin n → R)
    (hs : Ideal.span (Set.range s) = ⊤) (A : ℕ) (w : N)
    (hj : ∀ j, (s j) ^ A • w = 0) : w = 0 := by
  obtain ⟨c, hc⟩ := exists_sum_pow_eq_one s hs A
  calc w = (∑ j, c j * (s j) ^ A) • w := by rw [hc, one_smul]
    _ = ∑ j, c j • ((s j) ^ A • w) := by rw [Finset.sum_smul]; simp_rw [mul_smul]
    _ = 0 := by simp_rw [hj, smul_zero, Finset.sum_const_zero]

/-- Localising the multiplication-by-`c` endomorphism of `N` at `S` is multiplication by `c` on the
localised module (as underlying functions).  Project-local helper for the `map_units` clause of
`isLocalizedModule_of_span_cover`. -/
private lemma map_smul_endFun (S : Submonoid R) (c : R) :
    ⇑(LocalizedModule.map S (algebraMap R (Module.End R N) c))
      = ⇑(algebraMap R (Module.End R (LocalizedModule S N)) c) := by
  funext x
  induction x using LocalizedModule.induction_on with
  | _ m t =>
    rw [LocalizedModule.map_mk]
    simp [Module.algebraMap_end_apply, LocalizedModule.smul'_mk]

/-- Arithmetic of "bumping" two scalar powers up to uniform exponents.  Project-local helper for the
surjectivity/equaliser clauses of `isLocalizedModule_of_span_cover`. -/
private lemma bump_eq {P : Type*} [AddCommGroup P] [Module R P] (c d : R) (y : P)
    {a k A K : ℕ} (ha : a ≤ A) (hk : k ≤ K) :
    c ^ A • d ^ K • y = c ^ (A - a) • d ^ (K - k) • (c ^ a • d ^ k • y) := by
  simp only [smul_smul]
  congr 1
  have hc : c ^ A = c ^ (A - a) * c ^ a := by rw [← pow_add, Nat.sub_add_cancel ha]
  have hd : d ^ K = d ^ (K - k) * d ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
  rw [hc, hd]; ring

/-- Per-cover-member surjectivity datum: from the hypothesis that the `(s j)`-localised map is a
localisation at the powers of `f`, every `y : N` is hit by `g` up to a power of `s j` and a power of
`f`.  Project-local helper for the surjectivity clause of `isLocalizedModule_of_span_cover`. -/
private lemma per_j_surj (g : M →ₗ[R] N) (f : R) (c : R)
    (hj : IsLocalizedModule (Submonoid.powers f)
      (IsLocalizedModule.map (Submonoid.powers c)
        (LocalizedModule.mkLinearMap (Submonoid.powers c) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers c) N) g))
    (y : N) : ∃ (a k : ℕ) (m : M), c ^ a • f ^ k • y = g m := by
  haveI := hj
  obtain ⟨p, hxj⟩ := IsLocalizedModule.surj (Submonoid.powers f)
      (IsLocalizedModule.map (Submonoid.powers c)
        (LocalizedModule.mkLinearMap (Submonoid.powers c) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers c) N) g)
      (LocalizedModule.mk y 1)
  obtain ⟨xj, ⟨tf, kk, (rfl : f ^ kk = tf)⟩⟩ := p
  rw [Submonoid.smul_def, LocalizedModule.smul'_mk] at hxj
  revert hxj
  induction xj using LocalizedModule.induction_on with
  | _ m u =>
    intro hxj
    rw [IsLocalizedModule.map_LocalizedModules] at hxj
    obtain ⟨⟨u', uu, (rfl : c ^ uu = u')⟩, hu'⟩ := (LocalizedModule.mk_eq).1 hxj
    obtain ⟨u2, vv, (rfl : c ^ vv = u2)⟩ := u
    simp only [Submonoid.smul_def, one_smul] at hu'
    refine ⟨vv + uu, kk, c ^ uu • m, ?_⟩
    rw [map_smul]
    rw [show c ^ (vv + uu) • f ^ kk • y = c ^ uu • c ^ vv • (f ^ kk • y) by
          rw [pow_add]; simp only [smul_smul]; ring_nf]
    exact hu'

/-- Per-cover-member equaliser datum: from the hypothesis that the `(s j)`-localised map is a
localisation at the powers of `f`, any `z` with `g z = 0` is annihilated by a power of `s j` times a
power of `f`.  Project-local helper for the equaliser clause. -/
private lemma per_j_eq (g : M →ₗ[R] N) (f : R) (c : R)
    (hj : IsLocalizedModule (Submonoid.powers f)
      (IsLocalizedModule.map (Submonoid.powers c)
        (LocalizedModule.mkLinearMap (Submonoid.powers c) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers c) N) g))
    (z : M) (hz : g z = 0) : ∃ (a k : ℕ), c ^ a • f ^ k • z = 0 := by
  haveI := hj
  have key : (IsLocalizedModule.map (Submonoid.powers c)
        (LocalizedModule.mkLinearMap (Submonoid.powers c) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers c) N) g) (LocalizedModule.mk z 1)
      = (IsLocalizedModule.map (Submonoid.powers c)
        (LocalizedModule.mkLinearMap (Submonoid.powers c) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers c) N) g) 0 := by
    rw [map_zero, IsLocalizedModule.map_LocalizedModules, hz, LocalizedModule.zero_mk]
  obtain ⟨⟨cc, kk, (rfl : f ^ kk = cc)⟩, hcc⟩ := hj.exists_of_eq key
  rw [Submonoid.smul_def, LocalizedModule.smul'_mk, smul_zero] at hcc
  rw [← LocalizedModule.zero_mk (1 : Submonoid.powers c), LocalizedModule.mk_eq] at hcc
  obtain ⟨⟨u, aa, (rfl : c ^ aa = u)⟩, hu⟩ := hcc
  simp only [Submonoid.smul_def, one_smul, smul_zero] at hu
  exact ⟨aa, kk, hu⟩

/-- **`IsLocalizedModule` is local on a finite spanning cover (Stacks 01I8, P1b).**  If an
`R`-linear map `g : M → N` becomes a localisation at the powers of `f` after localising at the
powers of each member `s j` of a finite family spanning the unit ideal, then `g` is itself a
localisation at the powers of `f`.  Proved by descent of the three defining clauses of
`IsLocalizedModule` along the spanning cover (the partition-of-unity argument).  Project-local:
Mathlib has analogous span-descent lemmas for `Module.Finite`/`Module.FinitePresentation` but not
for the `IsLocalizedModule` predicate itself. -/
theorem isLocalizedModule_of_span_cover
    (g : M →ₗ[R] N) (f : R) {n : ℕ} (s : Fin n → R)
    (hs : Ideal.span (Set.range s) = ⊤)
    (h : ∀ j, IsLocalizedModule (Submonoid.powers f)
      (IsLocalizedModule.map (Submonoid.powers (s j))
        (LocalizedModule.mkLinearMap (Submonoid.powers (s j)) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers (s j)) N) g)) :
    IsLocalizedModule (Submonoid.powers f) g := by
  refine ⟨?_, ?_, ?_⟩
  · -- `f` acts invertibly on `N`
    intro x
    obtain ⟨k, hk⟩ := x.2
    rw [show ((x : R)) = f ^ k from hk.symm, map_pow]
    apply IsUnit.pow
    rw [Module.End.isUnit_iff]
    apply bijective_of_localized_span (Set.range s) hs
    rintro ⟨r, j, rfl⟩
    rw [show ⇑(LocalizedModule.map (Submonoid.powers (s j)) (algebraMap R (Module.End R N) f))
        = ⇑(algebraMap R (Module.End R (LocalizedModule (Submonoid.powers (s j)) N)) f)
        from map_smul_endFun _ _, ← Module.End.isUnit_iff]
    exact (h j).map_units ⟨f, 1, by simp⟩
  · -- every `y : N` is hit by `g` up to a power of `f`
    intro y
    choose a k m hm using fun j => per_j_surj g f (s j) (h j) y
    set K := Finset.univ.sup k
    set A := Finset.univ.sup a
    have hw : ∀ j, ∃ mm : M, (s j) ^ A • (f ^ K • y) = g mm := by
      intro j
      have ha : a j ≤ A := Finset.le_sup (Finset.mem_univ j)
      have hkk : k j ≤ K := Finset.le_sup (Finset.mem_univ j)
      refine ⟨(s j) ^ (A - a j) • f ^ (K - k j) • m j, ?_⟩
      rw [bump_eq (s j) f y ha hkk, hm j, map_smul, map_smul]
    obtain ⟨mm, hmm⟩ := mem_range_of_span_pow s hs g A (f ^ K • y) hw
    exact ⟨⟨mm, ⟨f ^ K, K, rfl⟩⟩, hmm⟩
  · -- `g`-equal elements agree up to a power of `f`
    intro x₁ x₂ he
    have hgz : g (x₁ - x₂) = 0 := by rw [map_sub, he, sub_self]
    choose a k hk using fun j => per_j_eq g f (s j) (h j) (x₁ - x₂) hgz
    set K := Finset.univ.sup k
    set A := Finset.univ.sup a
    have hw : ∀ j, (s j) ^ A • (f ^ K • (x₁ - x₂)) = 0 := by
      intro j
      have ha : a j ≤ A := Finset.le_sup (Finset.mem_univ j)
      have hkk : k j ≤ K := Finset.le_sup (Finset.mem_univ j)
      rw [bump_eq (s j) f (x₁ - x₂) ha hkk, hk j, smul_zero, smul_zero]
    have hzero : f ^ K • (x₁ - x₂) = 0 := eq_zero_of_span_pow s hs A _ hw
    refine ⟨⟨f ^ K, K, rfl⟩, ?_⟩
    rw [← sub_eq_zero, ← smul_sub]
    exact hzero

end SpanCoverLocalization

/-! ## Project-local Mathlib supplement — Route B local model: section restriction localizes

The Route B keystone (`qcoh_section_isLocalizedModule`) asserts that for a *quasi-coherent*
`F` the section-restriction `Γ(Spec R, F) → Γ(D(f), F)` exhibits the target as the localization
of the source at the powers of `f`.  The two declarations here are the **local model** of that
statement — the case where `F` is already (isomorphic to) the associated sheaf `M^~` of an
`R`-module.  This is the load-bearing brick the keystone descends over its trivialising cover: on
each piece `D(g_j)` of a finite standard cover, the quasi-coherent `F` becomes `tilde`-of-a-module
(via the local presentation and right-exactness of `tilde`), and the section-restriction there is an
`IsLocalizedModule` precisely by these lemmas.

`tilde_section_isLocalizedModule` is the pure `tilde` case; the `[IsIso F.fromTildeΓ]` corollary
`section_isLocalizedModule_of_isIso_fromTildeΓ` transports it across the canonical isomorphism
`F ≅ Γ(F)^~`.  Project-local because Mathlib states `toOpen` (the localization of `M` itself into
`Γ(D(f), M^~)`) but not the *section-restriction* form `Γ(⊤, F) → Γ(D(f), F)` that the keystone and
the `fromTildeΓ` counit consume. -/

section LocalModel

/-- **Route B local model (pure `tilde` case).**  For an `R`-module `M`, the section-restriction map
`Γ(Spec R, M^~) → Γ(D(f), M^~)` of the associated sheaf exhibits its target as the localization of
its source at the powers of `f`: `IsLocalizedModule (powers f)` of that restriction.  This is the
section-restriction form of Mathlib's `tilde.toOpen` localization instance (which localizes `M`
itself, not the global sections `Γ(⊤, M^~)`), obtained by transporting along the global-sections
isomorphism `tilde.isoTop`.  Project-local; the load-bearing local model of the keystone
`qcoh_section_isLocalizedModule`. -/
lemma tilde_section_isLocalizedModule (M : ModuleCat.{u} R) (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by
  have key := tilde.toOpen_res M ⊤ (PrimeSpectrum.basicOpen f) (homOfLE le_top)
  -- `toOpen M ⊤` is an isomorphism; view it as a linear equivalence `eTop : M ≃ₗ Γ(⊤, M^~)`
  set eTop : M ≃ₗ[R] _ := (asIso (tilde.toOpen M ⊤)).toLinearEquiv with heTop
  -- the section-restriction equals `toOpen (D f) ∘ eTop⁻¹` as linear maps
  have hmap : ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom
      = (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom ∘ₗ eTop.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    have hk := congrArg (fun (m : M ⟶ _) => m.hom (eTop.symm x)) key
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hk
    have heq : ⇑eTop = ⇑(tilde.toOpen M ⊤).hom := by rw [heTop]; ext y; simp
    have htop : (tilde.toOpen M ⊤).hom (eTop.symm x) = x := by
      rw [← heq]; exact eTop.apply_symm_apply x
    conv_lhs => rw [← htop]
    exact hk
  rw [hmap]
  exact IsLocalizedModule.of_linearEquiv_right (Submonoid.powers f)
    (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom eTop.symm

/-- **Route B local model (counit-isomorphism case).**  If the tilde–Γ counit of an
`𝒪_{Spec R}`-module `F` is an isomorphism (equivalently `F ≅ M^~` for `M = Γ(Spec R, F)`), then the
section-restriction `Γ(Spec R, F) → Γ(D(f), F)` exhibits its target as the localization of its
source at the powers of `f`.  Obtained by transporting `tilde_section_isLocalizedModule` along the
isomorphism `F ≅ Γ(F)^~` (naturality of the section restriction under `modulesSpecToSheaf`).
Project-local; this is the per-piece engine of the keystone `qcoh_section_isLocalizedModule`: on
each `D(g_j)` of a trivialising cover the quasi-coherent `F` has an isomorphic counit (it carries a
global presentation there), so this lemma supplies the `IsLocalizedModule` datum the span-cover
descent consumes. -/
lemma section_isLocalizedModule_of_isIso_fromTildeΓ (F : (Spec R).Modules)
    [IsIso F.fromTildeΓ] (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj F).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by
  set M := moduleSpecΓFunctor.obj F with hM
  set α : F ≅ tilde M := qcoh_iso_tilde_sections F with hα
  -- the underlying presheaf morphism of `modulesSpecToSheaf.map α.hom`
  set β := (TopCat.Sheaf.forget (ModuleCat R) (Spec R)).map (modulesSpecToSheaf.map α.hom) with hβ
  haveI : IsIso (modulesSpecToSheaf.map α.hom) := inferInstance
  haveI : IsIso β := inferInstance
  haveI : IsIso (β.app (Opposite.op (⊤ : (Spec R).Opens))) :=
    CategoryTheory.NatIso.isIso_app_of_isIso β _
  haveI : IsIso (β.app (Opposite.op (PrimeSpectrum.basicOpen f))) :=
    CategoryTheory.NatIso.isIso_app_of_isIso β _
  -- the two `β`-components as linear equivalences
  set eTop : _ ≃ₗ[R] _ :=
    (asIso (β.app (Opposite.op (⊤ : (Spec R).Opens)))).toLinearEquiv with heTop
  set eDf : _ ≃ₗ[R] _ :=
    (asIso (β.app (Opposite.op (PrimeSpectrum.basicOpen f)))).toLinearEquiv with heDf
  -- the `tilde M` restriction localizes (the local model), conjugate it by `eTop` on the source
  haveI hbrick := tilde_section_isLocalizedModule M f
  set φ : _ →ₗ[R] _ := ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
      (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom ∘ₗ eTop.toLinearMap with hφ
  haveI hφloc : IsLocalizedModule (Submonoid.powers f) φ := by
    rw [hφ]
    exact IsLocalizedModule.of_linearEquiv_right (Submonoid.powers f)
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom eTop
  -- naturality of `β`, read at `.hom` level: `eDf ∘ ρ_F = ρ_{tilde M} ∘ eTop = φ`
  have hnat := β.naturality (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op
  have hnat' : ∀ x, eDf (((modulesSpecToSheaf.obj F).presheaf.map
      (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom x) = φ x := by
    intro x
    have hx := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hnat) x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx
    exact hx
  -- so `ρ_F = eDf⁻¹ ∘ φ`, hence localizes (post-compose a localization with a linear equiv)
  have hF : ((modulesSpecToSheaf.obj F).presheaf.map
      (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom
      = eDf.symm.toLinearMap ∘ₗ φ := by
    apply LinearMap.ext
    intro x
    change _ = eDf.symm (φ x)
    rw [← hnat' x, eDf.symm_apply_apply]
  rw [hF]
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers f) φ eDf.symm

/-- **Route B keystone, globally-presented case.**  If an `𝒪_{Spec R}`-module `F` admits a *global*
presentation (`F.Presentation`), then the section-restriction `Γ(Spec R, F) → Γ(D(f), F)` exhibits
its target as the localization of its source at the powers of `f`.  This is the keystone
`qcoh_section_isLocalizedModule` for the special — but key — case of a global presentation: it is
exactly the situation on each affine piece `D(g_j) ≅ Spec R_{g_j}` of a trivialising cover of a
quasi-coherent `F`, where the local quasi-coherence datum supplies a global presentation.  Proved by
discharging `[IsIso F.fromTildeΓ]` via Mathlib's `isIso_fromTildeΓ_of_presentation` and applying
`section_isLocalizedModule_of_isIso_fromTildeΓ`.  Project-local; the unconditional quasi-coherent
keystone descends from this case over the cover via `isLocalizedModule_of_span_cover`. -/
lemma section_isLocalizedModule_of_presentation (F : (Spec R).Modules)
    (P : F.Presentation) (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj F).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by
  haveI := isIso_fromTildeΓ_of_presentation F P
  exact section_isLocalizedModule_of_isIso_fromTildeΓ F f

end LocalModel

/-! ## Project-local Mathlib supplement — Route B step B1: finite presentation cover

`qcoh_finite_presentation_cover` (Stacks 01I8, Route B step B1): for a quasi-coherent `F` on
`Spec R`, the local quasi-coherence datum (`QuasicoherentData`) refines to a *finite* standard
cover `D(g_j) ⊆ U_{φ(j)}` with `span{g_j} = ⊤`, each member `U_{φ(j)}` carrying a presentation of
`F.over U_{φ(j)}`.  This is the entry point of the keystone descent: per `g_j` the attached
presentation restricts (B2) and bridges (B3/B4) to a global presentation of the affine restriction,
which the `IsLocalizedModule` local model then consumes.

`coversTop_iSup_eq_top` is the topological translation feeding `exists_finite_basicOpen_subcover`:
the cover-of-terminal-object condition of a `QuasicoherentData` on the opens-Grothendieck-topology
of a space is the honest `⨆ U_i = ⊤`. -/

section FinitePresentationCover

/-- A family of opens that covers the terminal object of the opens-Grothendieck-topology of a space
has supremum `⊤`.  Project-local: translates the categorical `J.CoversTop` condition carried by a
`QuasicoherentData` into the lattice-theoretic `⨆ = ⊤` that `exists_finite_basicOpen_subcover`
consumes. -/
private lemma coversTop_iSup_eq_top {T : Type*} [TopologicalSpace T] {I : Type*}
    (Y : I → TopologicalSpace.Opens T)
    (hY : (Opens.grothendieckTopology T).CoversTop Y) :
    ⨆ i, Y i = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [TopologicalSpace.Opens.mem_iSup]
  obtain ⟨U, f, hf, hU⟩ := hY ⊤ x (TopologicalSpace.Opens.mem_top x)
  obtain ⟨i, ⟨g⟩⟩ := hf
  exact ⟨i, (leOfHom g) hU⟩

/-- **Finite presentation cover from quasi-coherence (Stacks 01I8, Route B step B1).**  For a
quasi-coherent `𝒪_{Spec R}`-module `F`, there is a quasi-coherence datum `q` (a cover `q.X` of
`Spec R` together with a presentation of `F.over (q.X i)` for each `i`) and a *finite* standard
refinement of it: finitely many `g : Fin n → R` with `span (range g) = ⊤` and indices
`φ : Fin n → q.I` such that each basic open `D(g j)` lies inside the cover member `q.X (φ j)`.  The
presentation of `F.over (q.X (φ j))` carried by `q` is what steps B2–B4 restrict to `D(g j)`.
Project-local: packages Mathlib's `QuasicoherentData` (local generation) with the affine finite
basic-open refinement (`exists_finite_basicOpen_subcover`) in the exact form the Route B keystone
descent consumes. -/
lemma qcoh_finite_presentation_cover (F : (Spec R).Modules)
    [hF : F.IsQuasicoherent] :
    ∃ (q : SheafOfModules.QuasicoherentData.{u, u, u, u} F)
      (n : ℕ) (g : Fin n → R) (φ : Fin n → q.I),
      (∀ j, PrimeSpectrum.basicOpen (g j) ≤ q.X (φ j)) ∧ Ideal.span (Set.range g) = ⊤ := by
  obtain ⟨q⟩ := hF.nonempty_quasicoherentData
  have htop : ⨆ i, q.X i = ⊤ := coversTop_iSup_eq_top q.X q.coversTop
  obtain ⟨n, g, φ, hgU, hspan⟩ := exists_finite_basicOpen_subcover q.X htop
  exact ⟨q, n, g, φ, hgU, hspan⟩

end FinitePresentationCover

/-! ## Project-local Mathlib supplement — Route B keystone: degree-0/1 sheaf-axiom equalizer

`qcoh_section_equalizer` (Stacks 01HV(4)/01I8, sheaf-axiom equalizer route) is the degree-`0/1`
{\v C}ech equalizer of a sheaf of modules `F` on `Spec R`, read off the sheaf condition for a finite
(in fact arbitrary) family `U` covering an open `W`:
`0 → Γ(W,F) → ∏ⱼ Γ(Uⱼ,F) → ∏ⱼₖ Γ(Uⱼ ⊓ Uₖ,F)` is exact at both non-zero terms.  It is the entry
point of the keystone kernel comparison: instantiated at `W = ⊤` and `W = D(f)` (with `Uⱼ = D(gⱼ)`
resp. `Uⱼ = D(f gⱼ)`) it exhibits `Γ(X,F)` and `Γ(D(f),F)` as the kernels of the two overlap
differentials, which the localisation comparison then matches.  Non-circular: only the sheaf
condition of `F` is used, never a section-localisation identity. -/

section SectionEqualizer

/-- Restriction of a section across a composite inclusion `A ≤ B ≤ C` equals the single restriction
along `A ≤ C` (presheaf functoriality in the thin opens category).  Project-local helper for the
degree-0/1 differential computation of `qcoh_section_equalizer`. -/
private lemma res_trans_apply (P : TopCat.Presheaf (ModuleCat R) (Spec R))
    {A B C : (Spec R).Opens} (h1 : A ≤ B) (h2 : B ≤ C) (s : P.obj (.op C)) :
    (P.map (homOfLE h1).op).hom ((P.map (homOfLE h2).op).hom s)
      = (P.map (homOfLE (h1.trans h2)).op).hom s := by
  rw [← ModuleCat.comp_apply, ← P.map_comp]; rfl

/-- **Degree-0/1 sheaf-axiom equalizer (Stacks 01HV(4)/01I8).**  For a sheaf of `𝒪_{Spec R}`-modules
`F`, an open `W`, and a family `U : ι → Opens` with `U i ≤ W` for all `i` and `W ≤ ⨆ U i`, the
augmented two-term {\v C}ech sequence
`0 → Γ(W,F) →[ρ] ∏ᵢ Γ(U i,F) →[δ] ∏_{i,k} Γ(U i ⊓ U k,F)` is exact: the restriction product `ρ` is
injective and its range is exactly the kernel of the overlap differential `δ` (the difference of the
two restriction-to-overlap maps).  This is the sheaf condition of `F` read in degrees `0` and `1`,
proved from `TopCat.Presheaf.IsSheaf.section_ext` (injectivity) and
`TopCat.Sheaf.existsUnique_gluing'` (gluing of a matching family).  Project-local: Mathlib packages
the sheaf condition as a categorical limit / unique-gluing statement, not in the explicit
`Function.Exact` form on the section modules that the keystone kernel comparison consumes. -/
theorem qcoh_section_equalizer (F : (Spec R).Modules) {ι : Type u}
    (W : (Spec R).Opens) (U : ι → (Spec R).Opens)
    (hUW : ∀ i, U i ≤ W) (hWU : W ≤ iSup U) :
    Function.Injective
        ((LinearMap.pi fun i =>
          ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE (hUW i)).op).hom) :
          (modulesSpecToSheaf.obj F).presheaf.obj (.op W) →ₗ[R]
            (Π i, (modulesSpecToSheaf.obj F).presheaf.obj (.op (U i)))) ∧
      Function.Exact
        ((LinearMap.pi fun i =>
          ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE (hUW i)).op).hom) :
          (modulesSpecToSheaf.obj F).presheaf.obj (.op W) →ₗ[R] _)
        ((LinearMap.pi fun p : ι × ι =>
          ((modulesSpecToSheaf.obj F).presheaf.map
              (homOfLE (inf_le_right : U p.1 ⊓ U p.2 ≤ U p.2)).op).hom ∘ₗ LinearMap.proj p.2
          - ((modulesSpecToSheaf.obj F).presheaf.map
              (homOfLE (inf_le_left : U p.1 ⊓ U p.2 ≤ U p.1)).op).hom ∘ₗ LinearMap.proj p.1)) := by
  set P := modulesSpecToSheaf.obj F with hP
  have hsheaf : P.presheaf.IsSheaf := P.2
  refine ⟨?_, ?_⟩
  · -- injectivity: a section is determined by its restrictions to the cover (`section_ext`)
    intro s s' hss
    have hcomp : ∀ i, (P.presheaf.map (homOfLE (hUW i)).op).hom s
        = (P.presheaf.map (homOfLE (hUW i)).op).hom s' := fun i => congrFun hss i
    apply hsheaf.section_ext
    intro x hx
    have hxU : x ∈ iSup U := hWU hx
    rw [TopologicalSpace.Opens.mem_iSup] at hxU
    obtain ⟨i, hi⟩ := hxU
    exact ⟨U i, hUW i, hi, hcomp i⟩
  · -- exactness at the middle: `δ t = 0 ↔ t` glues to a section over `W`
    intro t
    constructor
    · intro ht
      have hcompat : TopCat.Presheaf.IsCompatible P.presheaf U t := by
        intro i j
        have hij := congrFun ht (i, j)
        simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.proj_apply, Pi.zero_apply, sub_eq_zero] at hij
        exact hij.symm
      obtain ⟨s, hs, _⟩ := P.existsUnique_gluing' U W (fun i => homOfLE (hUW i)) hWU t hcompat
      exact ⟨s, funext fun i => hs i⟩
    · rintro ⟨s, rfl⟩
      funext p
      simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.proj_apply, Pi.zero_apply, sub_eq_zero]
      rw [res_trans_apply, res_trans_apply]

end SectionEqualizer

/-! ## Project-local Mathlib supplement — base-ring descent of `IsLocalizedModule`

`isLocalizedModule_powers_restrictScalars_of_algebraMap` is the converse of Mathlib's
`IsLocalizedModule.of_restrictScalars`: an `A`-linear map that is a localization at the powers of
`algebraMap R A f` (over the larger base `A`) is, viewed `R`-linearly, a localization at the powers
of `f` (over the smaller base `R`).  This is the base-ring descent the Route B keystone needs: the
per-tile localizations produced over `R_g = Localization.Away g` (the tile's base ring) must be read
as `R`-localizations at the powers of `f ∈ R` to feed the kernel comparison, which localizes the
`X`-cover equalizer at `powers f ⊆ R`.  Project-local: Mathlib supplies only the ascent
direction. -/

section BaseRingDescent

/-- **Base-ring descent of `IsLocalizedModule` (converse of `of_restrictScalars`).**  Let `A` be an
`R`-algebra, let `M N` be `A`-modules with the compatible `R`-module structures (`IsScalarTower`),
and let `φ : M →ₗ[A] N`.  If `φ` is a localization at the powers of `algebraMap R A f` *over `A`*,
then its `R`-linear restriction `φ.restrictScalars R` is a localization at the powers of `f` *over
`R`*.  Proved directly from the three defining clauses of `IsLocalizedModule`, using that
`(algebraMap R A f) ^ k • x = f ^ k • x` by the scalar tower.  Project-local: Mathlib has only the
ascent `IsLocalizedModule.of_restrictScalars`, not this descent. -/
lemma isLocalizedModule_powers_restrictScalars_of_algebraMap
    {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module A M] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N] (f : R) (φ : M →ₗ[A] N)
    (h : IsLocalizedModule (Submonoid.powers (algebraMap R A f)) φ) :
    IsLocalizedModule (Submonoid.powers f) (φ.restrictScalars R) := by
  have hsmul : ∀ (k : ℕ) (n : N), (algebraMap R A f) ^ k • n = f ^ k • n := by
    intro k n; rw [← map_pow, algebraMap_smul]
  have hsmulM : ∀ (k : ℕ) (m : M), (algebraMap R A f) ^ k • m = f ^ k • m := by
    intro k m; rw [← map_pow, algebraMap_smul]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, k, rfl⟩
    rw [Module.End.isUnit_iff]
    have hb := h.map_units ⟨(algebraMap R A f) ^ k, k, rfl⟩
    rw [Module.End.isUnit_iff] at hb
    convert hb using 1
    ext n
    simp only [Module.algebraMap_end_apply]
    exact (hsmul k n).symm
  · intro y
    obtain ⟨⟨m, s⟩, hs⟩ := h.surj y
    obtain ⟨k, hk⟩ := s.2
    simp only [] at hk
    refine ⟨⟨m, ⟨f ^ k, k, rfl⟩⟩, ?_⟩
    rw [Submonoid.smul_def] at hs ⊢
    calc f ^ k • y = (algebraMap R A f) ^ k • y := (hsmul k y).symm
      _ = (s : A) • y := by rw [hk]
      _ = φ m := hs
  · intro x₁ x₂ he
    obtain ⟨s, hs⟩ := h.exists_of_eq he
    obtain ⟨k, hk⟩ := s.2
    simp only [] at hk
    refine ⟨⟨f ^ k, k, rfl⟩, ?_⟩
    rw [Submonoid.smul_def] at hs ⊢
    calc f ^ k • x₁ = (algebraMap R A f) ^ k • x₁ := (hsmulM k x₁).symm
      _ = (s : A) • x₁ := by rw [hk]
      _ = (s : A) • x₂ := hs
      _ = (algebraMap R A f) ^ k • x₂ := by rw [hk]
      _ = f ^ k • x₂ := hsmulM k x₂

end BaseRingDescent

/-! ## Project-local Mathlib supplement — Route B keystone: per-tile section localization

`tile_section_localization` (Stacks 01HV(4)/01I8, the last keystone leaf) shows that for a
quasi-coherent `F` on `Spec R` and elements `f g : R` with the tile `F_{(g)}` globally presented,
the section-restriction `Γ(D(g), F) → Γ(D(gf), F)` exhibits its target as the localization of its
source at the powers of `f`.  It is the per-tile localization datum the sheaf-axiom kernel
comparison consumes (`analogies/keystone-descent.md`).

The naive recipe "the section comparison is the `restrict_obj` rfl" is UNSOUND:
`restrict_obj` is rfl only for the local-ring `SheafOfModules` section functor `Γ(M,-)`, whereas
the localization lives in the global-ring functor `modulesSpecToSheaf.obj`, which does NOT commute
with restriction
definitionally.  Hence the honest base-ring descent: Sub-lemma A (opens identities,
`tile_image_opens_identities`) + Sub-lemma B (the load-bearing natural section comparison,
`tile_section_comparison`) + the DONE base-ring descent
`isLocalizedModule_powers_restrictScalars_of_algebraMap`. -/

section TileSectionLocalization

open TopologicalSpace

/-- The `R`-action of the global-ring section functor `modulesSpecToSheaf` on a section reduces to
the structure-sheaf scalar action of the restricted global-sections element.  This is the rfl bridge
between the `ModuleCat R`-level action (via restriction of scalars along `globalSectionsIso`) and
the genuine `Γ(W, 𝒪)`-module action of `F.val`.  Project-local: the entry point of the tile scalar
reconciliation. -/
lemma modulesSpecToSheaf_smul_eq (F : (Spec R).Modules) (W : (Spec R).Opens) (r : R)
    (x : (modulesSpecToSheaf.obj F).presheaf.obj (Opposite.op W)) :
    r • x = (((Spec R).ringCatSheaf.obj.map (homOfLE (le_top : W ≤ ⊤)).op).hom
              ((StructureSheaf.globalSectionsIso R).hom.hom r)
            • (show F.val.obj (Opposite.op W) from x)) :=
  rfl

/-- The module action on the affine tile `modulesRestrictBasicOpen g F` transports rfl-style to the
`F.val` structure-sheaf action via the two open-immersion `appIso` ring maps of the iterated
restriction.  Project-local: the second rfl bridge of the tile scalar reconciliation. -/
lemma modulesRestrictBasicOpen_smul_eq (F : (Spec R).Modules) (g : R)
    (c : (Spec (.of (Localization.Away g))).ringCatSheaf.obj.obj
          (Opposite.op (⊤ : (Spec (.of (Localization.Away g))).Opens)))
    (m : (modulesRestrictBasicOpen g F).val.obj
          (Opposite.op (⊤ : (Spec (.of (Localization.Away g))).Opens))) :
    c • m = (((specBasicOpen g).ι.appIso _).inv.hom
              (((basicOpenIsoSpecAway g).inv.appIso _).inv.hom c))
            • (show F.val.obj (Opposite.op ((specBasicOpen g).ι ''ᵁ
                ((basicOpenIsoSpecAway g).inv ''ᵁ
                  (⊤ : (Spec (.of (Localization.Away g))).Opens)))) from m) :=
  rfl

/-- General-open version of `modulesRestrictBasicOpen_smul_eq`: the tile module action over an
arbitrary open `V` of `Spec R_g` transports rfl-style to the `F.val` structure-sheaf action over the
iterated image open `ι ''ᵁ V`.  Project-local: needed for the scalar reconciliation at the target
open `V = D(f̄)` of the per-tile section localization. -/
lemma modulesRestrictBasicOpen_smul_eq' (F : (Spec R).Modules) (g : R)
    (V : (Spec (.of (Localization.Away g))).Opens)
    (c : (Spec (.of (Localization.Away g))).ringCatSheaf.obj.obj (Opposite.op V))
    (m : (modulesRestrictBasicOpen g F).val.obj (Opposite.op V)) :
    c • m = (((specBasicOpen g).ι.appIso _).inv.hom
              (((basicOpenIsoSpecAway g).inv.appIso _).inv.hom c))
            • (show F.val.obj (Opposite.op ((specBasicOpen g).ι ''ᵁ
                ((basicOpenIsoSpecAway g).inv ''ᵁ V))) from m) :=
  rfl

/-- **Sub-lemma A (Stacks 01I8): image opens of the affine tile identification.**  Let `g f : R`,
let `R_g = Localization.Away g`, and let `ι = specAwayToSpec g : Spec R_g ⟶ Spec R` be the
localization morphism identifying `Spec R_g` with `D(g) ⊆ Spec R`.  Then the image opens of the two
relevant opens of `Spec R_g` are `ι ''ᵁ ⊤ = D(g)` and `ι ''ᵁ D(f̄) = D(gf)` (with
`f̄ = algebraMap R R_g f`), where the images are taken in the iterated-restriction form
`(specBasicOpen g).ι ''ᵁ ((iso).inv ''ᵁ -)` matching `modulesRestrictBasicOpen`.  Project-local: the
opens bookkeeping that lets the `R_g`-section localization on the tile be matched against the
`R`-section restriction `Γ(D(g),F) → Γ(D(gf),F)`. -/
lemma tile_image_opens_identities (g f : R) :
    (specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ
        (⊤ : (Spec (.of (Localization.Away g))).Opens)) = specBasicOpen g ∧
      (specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ
          (PrimeSpectrum.basicOpen (algebraMap R (Localization.Away g) f)))
        = specBasicOpen (g * f) := by
  constructor
  · rw [show ((basicOpenIsoSpecAway g).inv ''ᵁ
        (⊤ : (Spec (.of (Localization.Away g))).Opens)) = ⊤ from by
          rw [Scheme.Hom.image_top_eq_opensRange]; exact Scheme.Hom.opensRange_of_isIso _]
    simp [Scheme.Hom.image_top_eq_opensRange]
  · have hcomp : (specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ
        (PrimeSpectrum.basicOpen (algebraMap R (Localization.Away g) f)))
        = specAwayToSpec g ''ᵁ (PrimeSpectrum.basicOpen (algebraMap R (Localization.Away g) f)) :=
      (Scheme.Hom.comp_image _ _ _).symm
    rw [hcomp]
    apply Opens.ext
    rw [Scheme.Hom.coe_image]
    rw [show ⇑(specAwayToSpec g)
        = PrimeSpectrum.comap (algebraMap R (Localization.Away g)) from by
          rw [specAwayToSpec_eq]; rfl]
    ext x
    simp only [SetLike.mem_coe, PrimeSpectrum.basicOpen_mul, Set.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hpr : p.asIdeal.IsPrime := p.isPrime
      refine ⟨?_, hp⟩
      change (algebraMap R (Localization.Away g)) g ∉ p.asIdeal
      intro hmem
      exact hpr.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
        (IsLocalization.Away.algebraMap_isUnit g))
    · rintro ⟨hg, hf⟩
      have hx : x ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away g))) := by
        rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]; exact hg
      obtain ⟨p, rfl⟩ := hx
      exact ⟨p, hf, rfl⟩

/-- For an open immersion `f : X ⟶ Y`, post-composing the global-sections map `f.appTop` with the
inverse of the section iso `f.appIso ⊤` recovers the structure-sheaf restriction from `⊤` to the
image open `f ''ᵁ ⊤`.  Project-local: the section-restriction reading of the open-immersion
`appIso`,
the geometric brick of the structure-sheaf ring identity inside `tile_scalar_compat`. -/
theorem appTop_appIso_inv_eq_res {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] :
    Scheme.Hom.appTop f ≫ (Scheme.Hom.appIso f ⊤).inv
      = Y.presheaf.map (homOfLE (le_top : f ''ᵁ ⊤ ≤ ⊤)).op := by
  rw [Iso.comp_inv_eq, Scheme.Hom.appIso_hom, Scheme.Hom.appTop, ← Category.assoc,
    Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp]
  trans (Scheme.Hom.app f ⊤ ≫ X.presheaf.map (𝟙 _))
  · rw [CategoryTheory.Functor.map_id, Category.comp_id]
  · congr 1

/-- **`ΓSpec` naturality of `specAwayToSpec g`, section form.**  Restricting the global-sections
identification along `D(g) ↪ Spec R` equals the localization map `R → R_g` followed by the
global-sections identification of `Spec R_g` and the (inverse) section iso of
`ι = specAwayToSpec g = Spec.map (algebraMap R R_g)`.  Project-local: the structure-sheaf naturality
that powers `tile_scalar_compat`; route (A) of the blueprint sketch. -/
theorem key_morph (g : R) :
    (Scheme.ΓSpecIso R).inv
      ≫ (Spec R).presheaf.map (homOfLE (le_top : specAwayToSpec g ''ᵁ ⊤ ≤ ⊤)).op
    = CommRingCat.ofHom (algebraMap R (Localization.Away g))
      ≫ (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away g))).inv
      ≫ ((specAwayToSpec g).appIso ⊤).inv := by
  have h1 : CommRingCat.ofHom (algebraMap R (Localization.Away g))
        ≫ (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away g))).inv
      = (Scheme.ΓSpecIso R).inv ≫ Scheme.Hom.appTop (specAwayToSpec g) := by
    rw [specAwayToSpec_eq]; exact Scheme.ΓSpecIso_inv_naturality _
  rw [reassoc_of% h1, appTop_appIso_inv_eq_res]

/-- The two (inverse) open-immersion section isos of the tile identification compose, via
`comp_appIso`, into the single section iso of `ι = specAwayToSpec g`, up to the structure-sheaf
transport along the image-opens identity `ι ''ᵁ ⊤ = (specBasicOpen g).ι ''ᵁ (iso ''ᵁ ⊤)`.
Project-local: the `comp_appIso` bookkeeping consumed by `tile_scalar_compat`. -/
theorem tile_appIso_comp (g : R) :
    (Scheme.Hom.appIso (basicOpenIsoSpecAway g).inv ⊤).inv
      ≫ (Scheme.Hom.appIso (specBasicOpen g).ι ((basicOpenIsoSpecAway g).inv ''ᵁ ⊤)).inv
    = ((specAwayToSpec g).appIso ⊤).inv
        ≫ (Spec R).presheaf.map (eqToHom (Scheme.Hom.comp_image
            (basicOpenIsoSpecAway g).inv (specBasicOpen g).ι ⊤).symm).op := by
  have hc := Scheme.Hom.comp_appIso (basicOpenIsoSpecAway g).inv (specBasicOpen g).ι ⊤
  rw [Scheme.Opens.ι_appIso] at hc
  rw [hc]; simp [Iso.trans_inv, eqToHom_map, eqToHom_op]

/-- **The structure-sheaf ring identity of Sub-lemma B (morphism form).**  Combining `key_morph`
(`ΓSpec` naturality) and `tile_appIso_comp` (`comp_appIso` bookkeeping): restriction to the tile
image open `D(g)` of the `Spec R` global-sections identification equals the localization map
`R → R_g`, followed by the `Spec R_g` global-sections identification and the two inverse
open-immersion section isomorphisms of the tile.  Project-local: the morphism-level content closed
elementwise in
`tile_scalar_compat`. -/
theorem tile_section_ring_identity (g : R) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE (le_top :
        ((specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ
          (⊤ : (Spec (.of (Localization.Away g))).Opens))) ≤ ⊤)).op
    = CommRingCat.ofHom (algebraMap R (Localization.Away g))
      ≫ (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away g))).inv
      ≫ (Spec (.of (Localization.Away g))).presheaf.map
          (homOfLE (le_top : (⊤ : (Spec (.of (Localization.Away g))).Opens) ≤ ⊤)).op
      ≫ ((basicOpenIsoSpecAway g).inv.appIso ⊤).inv
      ≫ ((specBasicOpen g).ι.appIso ((basicOpenIsoSpecAway g).inv ''ᵁ ⊤)).inv := by
  rw [show (Spec (.of (Localization.Away g))).presheaf.map
        (homOfLE (le_top : (⊤ : (Spec (.of (Localization.Away g))).Opens) ≤ ⊤)).op = 𝟙 _ from by
      rw [Subsingleton.elim (homOfLE (le_top : (⊤ : (Spec (.of (Localization.Away g))).Opens) ≤ ⊤))
        (𝟙 ⊤)]; simp, Category.id_comp]
  have hr := reassoc_of% key_morph (R := R) g
  rw [tile_appIso_comp, ← hr, ← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- **Sub-lemma B scalar compatibility (Stacks 01I8).**  For a quasi-coherent `F` on `Spec R` and
`g r : R`, the native `R`-action of `r` on a section of `F` over the tile image open `D(g)`
coincides with the `R_g`-action of `algebraMap R R_g r` on the corresponding section of the affine
tile `modulesRestrictBasicOpen g F`.  This is the load-bearing scalar reconciliation of the tile
section comparison: the two `rfl` bridges (`modulesSpecToSheaf_smul_eq`,
`modulesRestrictBasicOpen_smul_eq`) reduce both actions to a structure-sheaf scalar action, and the
remaining ring identity is `tile_section_ring_identity`.  Project-local; consumed by
`tile_section_localization`. -/
lemma tile_scalar_compat (F : (Spec R).Modules) (g r : R)
    (x : (modulesSpecToSheaf.obj (modulesRestrictBasicOpen g F)).presheaf.obj
          (Opposite.op (⊤ : (Spec (.of (Localization.Away g))).Opens))) :
    (r • (show (modulesSpecToSheaf.obj F).presheaf.obj
            (Opposite.op ((specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ
              (⊤ : (Spec (.of (Localization.Away g))).Opens)))) from x))
      = (algebraMap R (Localization.Away g) r) • x := by
  rw [modulesSpecToSheaf_smul_eq F]
  rw [show (algebraMap R (Localization.Away g) r) • x
        = _ from modulesSpecToSheaf_smul_eq (modulesRestrictBasicOpen g F) ⊤
            (algebraMap R (Localization.Away g) r) x]
  rw [modulesRestrictBasicOpen_smul_eq]
  congr 1
  have hG := congrArg (fun m : CommRingCat.of (R : Type _) ⟶ _ => m.hom r)
    (tile_section_ring_identity (R := R) g)
  simp only [CommRingCat.comp_apply] at hG
  exact hG

/-- Section-restriction form of `Scheme.Hom.appIso_inv_naturality`, stated with explicit `homOfLE`
restrictions and image opens so it rewrites cleanly: for an open immersion `f` and `U' ≤ U`, the
inverse section iso at `U` followed by the `Y`-restriction `f ''ᵁ U' ≤ f ''ᵁ U` equals the
`X`-restriction `U' ≤ U` followed by the inverse section iso at `U'`.  Project-local glue for
`tile_section_ring_identity'`. -/
private lemma appIso_inv_res {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] {U' U : X.Opens}
    (h : U' ≤ U) (h' : f ''ᵁ U' ≤ f ''ᵁ U) :
    (f.appIso U).inv ≫ Y.presheaf.map (homOfLE h').op
      = X.presheaf.map (homOfLE h).op ≫ (f.appIso U').inv := by
  rw [Scheme.Hom.appIso_inv_naturality f (homOfLE h).op]
  congr 1

/-- `Category.assoc`-folded form of `appIso_inv_res` for rewriting inside a longer composite.
Project-local glue for `tile_section_ring_identity'`. -/
private lemma appIso_inv_res_assoc {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] {U' U : X.Opens}
    (h : U' ≤ U) (h' : f ''ᵁ U' ≤ f ''ᵁ U) {Z : CommRingCat}
    (k : Y.presheaf.obj (.op (f ''ᵁ U')) ⟶ Z) :
    (f.appIso U).inv ≫ Y.presheaf.map (homOfLE h').op ≫ k
      = X.presheaf.map (homOfLE h).op ≫ (f.appIso U').inv ≫ k := by
  rw [← Category.assoc, appIso_inv_res, Category.assoc]

/-- General-open form of `tile_section_ring_identity`: the same structure-sheaf ring identity for
the restriction to the image of an arbitrary open `V ⊆ Spec R_g`.  Obtained from the `V = ⊤` case by
post-composing with the restriction `ι ''ᵁ V ≤ ι ''ᵁ ⊤` and pushing it through the two
open-immersion section isos via `Scheme.Hom.appIso_inv_naturality`.  Project-local: supplies the
ring identity at the target open `V = D(f̄)` for the scalar reconciliation `tile_scalar_compat'`. -/
theorem tile_section_ring_identity' (g : R) (V : (Spec (.of (Localization.Away g))).Opens) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE (le_top :
        ((specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ V)) ≤ ⊤)).op
    = CommRingCat.ofHom (algebraMap R (Localization.Away g))
      ≫ (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away g))).inv
      ≫ (Spec (.of (Localization.Away g))).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
      ≫ ((basicOpenIsoSpecAway g).inv.appIso V).inv
      ≫ ((specBasicOpen g).ι.appIso ((basicOpenIsoSpecAway g).inv ''ᵁ V)).inv := by
  have hV1 : (basicOpenIsoSpecAway g).inv ''ᵁ V ≤ (basicOpenIsoSpecAway g).inv ''ᵁ ⊤ :=
    leOfHom ((Scheme.Hom.opensFunctor _).map (homOfLE (le_top : V ≤ ⊤)))
  have hV : (specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ V)
      ≤ (specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ ⊤) :=
    leOfHom ((Scheme.Hom.opensFunctor _).map (homOfLE hV1))
  have base := tile_section_ring_identity (R := R) g
  -- abbreviations for the two open-immersion section isos
  calc (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE (le_top :
          ((specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ V)) ≤ ⊤)).op
      = ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE (le_top :
            ((specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ ⊤)) ≤ ⊤)).op)
          ≫ (Spec R).presheaf.map (homOfLE hV).op := by
        rw [Category.assoc, ← Functor.map_comp]; congr 2
    _ = (CommRingCat.ofHom (algebraMap R (Localization.Away g))
          ≫ (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away g))).inv
          ≫ (Spec (.of (Localization.Away g))).presheaf.map
              (homOfLE (le_top : (⊤ : (Spec (.of (Localization.Away g))).Opens) ≤ ⊤)).op
          ≫ ((basicOpenIsoSpecAway g).inv.appIso ⊤).inv
          ≫ ((specBasicOpen g).ι.appIso ((basicOpenIsoSpecAway g).inv ''ᵁ ⊤)).inv)
          ≫ (Spec R).presheaf.map (homOfLE hV).op := by rw [base]
    _ = CommRingCat.ofHom (algebraMap R (Localization.Away g))
          ≫ (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away g))).inv
          ≫ (Spec (.of (Localization.Away g))).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
          ≫ ((basicOpenIsoSpecAway g).inv.appIso V).inv
          ≫ ((specBasicOpen g).ι.appIso ((basicOpenIsoSpecAway g).inv ''ᵁ V)).inv := by
        rw [show (Spec (.of (Localization.Away g))).presheaf.map
              (homOfLE
                (le_top : (⊤ : (Spec (.of (Localization.Away g))).Opens) ≤ ⊤)).op = 𝟙 _ from by
            rw [Subsingleton.elim (homOfLE (le_top :
              (⊤ : (Spec (.of (Localization.Away g))).Opens) ≤ ⊤)) (𝟙 ⊤)]; simp, Category.id_comp]
        simp only [Category.assoc]
        rw [appIso_inv_res (specBasicOpen g).ι hV1 hV,
          appIso_inv_res_assoc (basicOpenIsoSpecAway g).inv (le_top : V ≤ ⊤) hV1]

set_option backward.isDefEq.respectTransparency false in
/-- **General-open form of `tile_scalar_compat` (Stacks 01I8).**  For a quasi-coherent `F` on
`Spec R`, `g r : R`, and an arbitrary open `V ⊆ Spec R_g`, the native `R`-action of `r` on a section
of `F` over
the tile image open `ι ''ᵁ V` coincides with the `R_g`-action of `algebraMap R R_g r` on the
corresponding section of the affine tile `modulesRestrictBasicOpen g F` over `V`.  The `V = D(f̄)`
instance is the scalar-tower compatibility at the *target* open of the per-tile section localization
(`tile_section_localization`); the `V = ⊤` case is `tile_scalar_compat`.  Proved by two `rfl`
smul bridges (now `modulesRestrictBasicOpen_smul_eq'`) reducing to the structure-sheaf ring identity
`tile_section_ring_identity'` at `V`.  Project-local. -/
lemma tile_scalar_compat' (F : (Spec R).Modules) (g r : R)
    (V : (Spec (.of (Localization.Away g))).Opens)
    (x : (modulesSpecToSheaf.obj (modulesRestrictBasicOpen g F)).presheaf.obj (Opposite.op V)) :
    (r • (show (modulesSpecToSheaf.obj F).presheaf.obj
            (Opposite.op ((specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ V))) from x))
      = (algebraMap R (Localization.Away g) r) • x := by
  rw [modulesSpecToSheaf_smul_eq F]
  rw [show (algebraMap R (Localization.Away g) r) • x
        = _ from modulesSpecToSheaf_smul_eq (modulesRestrictBasicOpen g F) V
            (algebraMap R (Localization.Away g) r) x]
  rw [modulesRestrictBasicOpen_smul_eq']
  congr 1
  have hG := congrArg (fun m : CommRingCat.of (R : Type _) ⟶ _ => m.hom r)
    (tile_section_ring_identity' (R := R) g V)
  simp only [CommRingCat.comp_apply] at hG
  exact hG

/-- `IsScalarTower R S` on a bundled restriction-of-scalars module object, supplied as a `Prop`
(a proof, hence no code generation or noncomputable auxiliary definition).  Project-local: lets the
base-ring descent `isLocalizedModule_powers_restrictScalars_of_algebraMap` find its scalar-tower
argument structurally on the `ModuleCat.restrictScalars (algebraMap R S)` carrier, without
installing a noncomputable local instance. -/
instance isScalarTower_restrictScalars_obj {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{u} S) :
    IsScalarTower R S ((ModuleCat.restrictScalars (algebraMap R S)).obj M) :=
  IsScalarTower.of_algebraMap_smul fun r m =>
    (ModuleCat.restrictScalars.smul_def' (algebraMap R S) r m).symm

-- The `toFun := id` carrier identity unifies the tile section against `F.val.obj (op (ι ''ᵁ V))`
set_option backward.isDefEq.respectTransparency false in
/-- The reconciliation `R`-linear equivalence underlying the tile section comparison: on the common
underlying carrier `F.val.obj (op (ι ''ᵁ V))` (the tile section over `V` IS `F`'s section over the
image open `ι ''ᵁ V`, by the restriction `rfl`), the `R`-module structure obtained by restriction of
scalars `R → R_g` from the tile coincides with the native `R`-action of `modulesSpecToSheaf.obj F`.
The map is the identity on elements; `R`-linearity is exactly the scalar-tower compatibility
`tile_scalar_compat'`.  Project-local: the structure-reconciliation half of the transport step of
`tile_section_localization` (the opens half is a presheaf `mapIso`). -/
noncomputable def tileReconcileEquiv (F : (Spec R).Modules) (g : R)
    (V : (Spec (CommRingCat.of (Localization.Away g))).Opens) :
    (ModuleCat.restrictScalars (algebraMap (R : Type u) (Localization.Away g))).obj
        ((modulesSpecToSheaf.obj (modulesRestrictBasicOpen g F)).presheaf.obj (Opposite.op V))
      ≃ₗ[(R : Type u)]
      (modulesSpecToSheaf.obj F).presheaf.obj (Opposite.op
        ((specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ V))) where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' r x := (tile_scalar_compat' F g r V x).symm
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] private lemma tileReconcileEquiv_apply (F : (Spec R).Modules) (g : R)
    (V : (Spec (CommRingCat.of (Localization.Away g))).Opens)
    (z : (ModuleCat.restrictScalars (algebraMap (R : Type u) (Localization.Away g))).obj
      ((modulesSpecToSheaf.obj (modulesRestrictBasicOpen g F)).presheaf.obj (Opposite.op V))) :
    tileReconcileEquiv F g V z = z := rfl

@[simp] private lemma tileReconcileEquiv_symm_apply (F : (Spec R).Modules) (g : R)
    (V : (Spec (CommRingCat.of (Localization.Away g))).Opens)
    (z : (modulesSpecToSheaf.obj F).presheaf.obj (Opposite.op
      ((specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ V)))) :
    (tileReconcileEquiv F g V).symm z = z := rfl

-- The `rfl` checks the tile restriction against `F`'s restriction over the iterated image opens
set_option backward.isDefEq.respectTransparency false in
/-- The tile restriction map IS `F`'s restriction over the iterated image opens (the restriction
`rfl` underlying the smul bridges, read at the level of the section-restriction morphism).
Project-local glue for the transport step of `tile_section_localization`. -/
private lemma tile_restrict_map_apply (F : (Spec R).Modules) (g : R)
    {V' V : (Spec (CommRingCat.of (Localization.Away g))).Opens} (h : V' ≤ V)
    (himg : (specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ V')
        ≤ (specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ V))
    (y : (modulesSpecToSheaf.obj (modulesRestrictBasicOpen g F)).presheaf.obj (Opposite.op V)) :
    ((modulesSpecToSheaf.obj (modulesRestrictBasicOpen g F)).presheaf.map (homOfLE h).op).hom y
      = ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE himg).op).hom y :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Per-tile section localisation at `f` (Stacks 01HV(4)/01I8, the last keystone leaf).**  Let
`F` be an `𝒪_{Spec R}`-module, `f g : R`, and suppose `D(g) ⊆ U` with `F.over U` globally presented.
Then the section-restriction `Γ(D(g), F) → Γ(D(gf), F)` exhibits its target as the localisation of
its source at the powers of `f`.  Proved by the base-ring descent of the recipe
`analogies/tile-descent-instance-shape.md`: the tile `F_{(g)}` is globally presented over `R_g`
(B4), so its section-restriction localises over `R_g` (`section_isLocalizedModule_of_presentation`);
descend the base ring `R_g → R` (`isLocalizedModule_powers_restrictScalars_of_algebraMap`) through
the bundled `ModuleCat.restrictScalars` carrier, then transport along the tile image-open identities
and the scalar-tower compatibilities.  Project-local; the per-tile localisation datum the keystone
kernel comparison consumes (non-circular: the localisation lives entirely on the globally-presented
tile, never on global `Γ(X, F)`). -/
lemma tile_section_localization (F : (Spec R).Modules) (U : (Spec R).Opens)
    (P : (F.over U).Presentation) (f g : R) (hg : specBasicOpen g ≤ U) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj F).presheaf.map
        (homOfLE (show specBasicOpen (g * f) ≤ specBasicOpen g from by
          rw [show specBasicOpen (g * f) = specBasicOpen g ⊓ specBasicOpen f from
            PrimeSpectrum.basicOpen_mul g f]; exact inf_le_left)).op).hom := by
  have Ptile : (modulesRestrictBasicOpen g F).Presentation :=
    presentationModulesRestrictBasicOpen F U P g hg
  have hσ := section_isLocalizedModule_of_presentation
    (R := CommRingCat.of (Localization.Away g)) (modulesRestrictBasicOpen g F) Ptile
    (algebraMap (R : Type u) (Localization.Away g) f)
  -- retype σ between the bundled restriction-of-scalars carriers
  let σ' : (ModuleCat.restrictScalars (algebraMap (R : Type u) (Localization.Away g))).obj
        ((modulesSpecToSheaf.obj (modulesRestrictBasicOpen g F)).presheaf.obj
          (Opposite.op (⊤ : (Spec (CommRingCat.of (Localization.Away g))).Opens)))
            →ₗ[Localization.Away g]
      (ModuleCat.restrictScalars (algebraMap (R : Type u) (Localization.Away g))).obj
        ((modulesSpecToSheaf.obj (modulesRestrictBasicOpen g F)).presheaf.obj
          (Opposite.op (PrimeSpectrum.basicOpen
            (algebraMap (R : Type u) (Localization.Away g) f)))) :=
    ((modulesSpecToSheaf.obj (modulesRestrictBasicOpen g F)).presheaf.map
      (homOfLE (le_top : PrimeSpectrum.basicOpen
        (algebraMap (R : Type u) (Localization.Away g) f) ≤ ⊤)).op).hom
  have hσ' : IsLocalizedModule
      (Submonoid.powers (algebraMap (R : Type u) (Localization.Away g) f)) σ' := hσ
  have hdesc := isLocalizedModule_powers_restrictScalars_of_algebraMap
    (A := Localization.Away g) f σ' hσ'
  haveI := hdesc
  have hop := tile_image_opens_identities g f
  -- the image-opens inclusion `ι ''ᵁ D(f̄) ≤ ι ''ᵁ ⊤`, by monotonicity of the image functors
  have himg : (specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ
        (PrimeSpectrum.basicOpen (algebraMap (R : Type u) (Localization.Away g) f)))
      ≤ (specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv ''ᵁ
        (⊤ : (Spec (CommRingCat.of (Localization.Away g))).Opens)) :=
    leOfHom ((Scheme.Hom.opensFunctor _).map (homOfLE
      (leOfHom ((Scheme.Hom.opensFunctor _).map (homOfLE le_top)))))
  -- transport: pure restriction-of-scalars reconciliation (identity on the common carrier;
  -- `R`-linearity is `tile_scalar_compat'`), NO opens transport — the opens are matched on the goal
  let eSrc := (tileReconcileEquiv F g
    (⊤ : (Spec (CommRingCat.of (Localization.Away g))).Opens)).symm
  let eTgt := tileReconcileEquiv F g
    (PrimeSpectrum.basicOpen (algebraMap (R : Type u) (Localization.Away g) f))
  have h1 := IsLocalizedModule.of_linearEquiv_right (Submonoid.powers f)
    (LinearMap.restrictScalars (R : Type u) σ') eSrc
  haveI := h1
  have h2 := IsLocalizedModule.of_linearEquiv (Submonoid.powers f)
    (LinearMap.restrictScalars (R : Type u) σ' ∘ₗ eSrc.toLinearMap) eTgt
  -- The reconciled composite is `F`'s restriction over `ι ''ᵁ D(f̄) ≤ ι ''ᵁ ⊤`.
  have key : (eTgt.toLinearMap ∘ₗ
        (LinearMap.restrictScalars (R : Type u) σ' ∘ₗ eSrc.toLinearMap))
      = ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE himg).op).hom := by
    apply LinearMap.ext; intro x
    simp only [eSrc, eTgt, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.restrictScalars_apply, tileReconcileEquiv_apply, tileReconcileEquiv_symm_apply]
    exact tile_restrict_map_apply F g
      (le_top : PrimeSpectrum.basicOpen (algebraMap (R : Type u) (Localization.Away g) f) ≤ ⊤)
      himg x
  -- `F`'s restriction over the image opens localizes at the powers of `f`
  have hμ : IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE himg).op).hom := key ▸ h2
  haveI := hμ
  -- Identify the image opens `ι ''ᵁ ⊤ = D(g)` and `ι ''ᵁ D(f̄) = D(gf)` via `mapIso`.
  let eqSrc := ((modulesSpecToSheaf.obj F).presheaf.mapIso
    (eqToIso (congrArg Opposite.op hop.1.symm))).toLinearEquiv
  let eqTgt := ((modulesSpecToSheaf.obj F).presheaf.mapIso
    (eqToIso (congrArg Opposite.op hop.2))).toLinearEquiv
  have h3 := IsLocalizedModule.of_linearEquiv_right (Submonoid.powers f)
    ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE himg).op).hom eqSrc
  haveI := h3
  have h4 := IsLocalizedModule.of_linearEquiv (Submonoid.powers f)
    (((modulesSpecToSheaf.obj F).presheaf.map (homOfLE himg).op).hom ∘ₗ eqSrc.toLinearMap) eqTgt
  have keyB : (eqTgt.toLinearMap ∘ₗ
        (((modulesSpecToSheaf.obj F).presheaf.map (homOfLE himg).op).hom ∘ₗ eqSrc.toLinearMap))
      = ((modulesSpecToSheaf.obj F).presheaf.map
          (homOfLE (show specBasicOpen (g * f) ≤ specBasicOpen g from by
            rw [show specBasicOpen (g * f) = specBasicOpen g ⊓ specBasicOpen f from
              PrimeSpectrum.basicOpen_mul g f]; exact inf_le_left)).op).hom := by
    simp only [eqSrc, eqTgt, CategoryTheory.Iso.toLinearMap_toLinearEquiv, Functor.mapIso_hom,
      eqToIso.hom]
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun m => ((modulesSpecToSheaf.obj F).presheaf.map m).hom)
      (Subsingleton.elim _ _)
  rw [← keyB]
  exact h4

end TileSectionLocalization

/-! ## Project-local Mathlib supplement — localization kernel comparison (left-exact ladder)

`isLocalizedModule_of_exact` is the abstract algebra at the heart of the keystone kernel
comparison: given a commutative ladder of `R`-modules with both rows left-exact and the two
right-hand vertical maps localizations at a submonoid `S`, the left-hand vertical map is itself a
localization at `S`.  It is the converse of `IsLocalizedModule.map_exact` (localization preserves
exactness), proved directly by chasing the three defining clauses of `IsLocalizedModule`.  The
keystone instantiates it with the two degree-`0/1` {\v C}ech equalizers (`qcoh_section_equalizer`)
of `F` on the cover `{D(gⱼ)}` (at `W = ⊤`) and `{D(gⱼf)}` (at `W = D(f)`), whose middle/overlap
vertical maps are the per-tile section localizations (`tile_section_localization`). -/

section LocalizationKernelComparison

/-- **Kernel comparison for localization (left-exact ladder).**  Given a commutative ladder of
`R`-modules
```
A --i--> B --p--> C
|a       |b       |c
A'--i'-> B'--p'-> C'
```
with both rows left-exact (`i`, `i'` injective and `Function.Exact i p`, `Function.Exact i' p'`)
and the two right-hand vertical maps `b`, `c` localizations at `S`, the left-hand vertical map `a`
is itself a localization at `S`.  Proved directly from the three defining clauses of
`IsLocalizedModule` by diagram chasing.  Project-local: Mathlib has `IsLocalizedModule.map_exact`
(localization preserves exactness) but not this kernel-comparison converse. -/
lemma isLocalizedModule_of_exact {R : Type*} [CommRing R] (S : Submonoid R)
    {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [Module R A] [Module R B] [Module R C]
    [Module R A'] [Module R B'] [Module R C']
    (i : A →ₗ[R] B) (p : B →ₗ[R] C) (i' : A' →ₗ[R] B') (p' : B' →ₗ[R] C')
    (a : A →ₗ[R] A') (b : B →ₗ[R] B') (c : C →ₗ[R] C')
    (hi : Function.Injective i) (hi' : Function.Injective i')
    (hp : Function.Exact i p) (hp' : Function.Exact i' p')
    (hb : IsLocalizedModule S b) (hc : IsLocalizedModule S c)
    (sq1 : i'.comp a = b.comp i) (sq2 : p'.comp b = c.comp p) :
    IsLocalizedModule S a := by
  have hbInj : ∀ (s : S) (x y : B'), (s : R) • x = (s : R) • y → x = y := by
    intro s x y h
    exact ((Module.End.isUnit_iff _).mp (hb.map_units s)).1
      (by simpa only [Module.algebraMap_end_apply] using h)
  have hbSurj : ∀ (s : S) (x : B'), ∃ z, (s : R) • z = x := by
    intro s x
    obtain ⟨z, hz⟩ := ((Module.End.isUnit_iff _).mp (hb.map_units s)).2 x
    exact ⟨z, by simpa only [Module.algebraMap_end_apply] using hz⟩
  have hcInj : ∀ (s : S) (x y : C'), (s : R) • x = (s : R) • y → x = y := by
    intro s x y h
    exact ((Module.End.isUnit_iff _).mp (hc.map_units s)).1
      (by simpa only [Module.algebraMap_end_apply] using h)
  have hsq1 : ∀ x : A, i' (a x) = b (i x) := fun x => LinearMap.congr_fun sq1 x
  have hsq2 : ∀ x : B, p' (b x) = c (p x) := fun x => LinearMap.congr_fun sq2 x
  refine ⟨?_, ?_, ?_⟩
  · intro s
    refine (Module.End.isUnit_iff _).mpr ⟨?_, ?_⟩
    · intro x y hxy
      simp only [Module.algebraMap_end_apply] at hxy
      apply hi'
      apply hbInj s
      rw [← map_smul, ← map_smul, hxy]
    · intro y
      simp only [Module.algebraMap_end_apply]
      obtain ⟨b0, hb0⟩ := hbSurj s (i' y)
      have hzero : (s : R) • p' b0 = 0 := by
        rw [← map_smul, hb0, hp'.apply_apply_eq_zero y]
      have hpb0 : p' b0 = 0 := hcInj s _ 0 (by rw [hzero, smul_zero])
      obtain ⟨a0, ha0⟩ := (hp' b0).mp hpb0
      refine ⟨a0, ?_⟩
      apply hi'
      rw [map_smul, ha0, hb0]
  · intro y
    obtain ⟨xs, hs⟩ := hb.surj (i' y)
    rw [Submonoid.smul_def] at hs
    have hc0 : c (p xs.1) = 0 := by
      rw [← hsq2 xs.1, ← hs, map_smul, hp'.apply_apply_eq_zero y, smul_zero]
    obtain ⟨s', hs'⟩ := hc.exists_of_eq (show c (p xs.1) = c 0 by rw [hc0, map_zero])
    simp only [Submonoid.smul_def, smul_zero] at hs'
    have hpz : p ((s' : R) • xs.1) = 0 := by rw [map_smul, hs']
    obtain ⟨x0, hx0⟩ := (hp ((s' : R) • xs.1)).mp hpz
    refine ⟨⟨x0, s' * xs.2⟩, ?_⟩
    rw [Submonoid.smul_def]
    apply hi'
    rw [hsq1 x0, hx0]
    simp only [map_smul, ← hs, Submonoid.coe_mul, mul_smul]
  · intro x₁ x₂ he
    have hbeq : b (i x₁) = b (i x₂) := by rw [← hsq1, ← hsq1, he]
    obtain ⟨s, hs⟩ := hb.exists_of_eq hbeq
    refine ⟨s, ?_⟩
    simp only [Submonoid.smul_def] at hs ⊢
    apply hi
    rw [map_smul, map_smul, hs]

end LocalizationKernelComparison

/-! ## Project-local Mathlib supplement — Route B keystone: kernel comparison assembly

`qcoh_section_isLocalizedModule` (Stacks 01HV(4)/01I8, the Route B keystone) and its packaged
isomorphism form `qcoh_section_kernel_comparison`: for a quasi-coherent `F` on `Spec R` and `f ∈ R`,
the section-restriction `ρ_f : Γ(X,F) → Γ(D(f),F)` exhibits `Γ(D(f),F)` as the localization of
`Γ(X,F)` at the powers of `f`.  Assembled from the two degree-`0/1` sheaf-axiom equalizers
(`qcoh_section_equalizer` at `W = ⊤` over `{D(gⱼ)}` and at `W = D(f)` over `{D(gⱼf)}`), the per-tile
section localizations (`tile_section_localization`) as the middle/overlap vertical maps, and the
abstract kernel comparison `isLocalizedModule_of_exact`. -/

section KernelComparisonAssembly

open TopologicalSpace

/-- Overlap target-opens identity: `D((a·b)·f) = D(a·f) ⊓ D(b·f)`.  Project-local bookkeeping for
the overlap vertical map of the keystone kernel comparison. -/
private lemma overlap_target_eq (a b f : R) :
    specBasicOpen ((a * b) * f) = specBasicOpen (a * f) ⊓ specBasicOpen (b * f) := by
  simp only [specBasicOpen, PrimeSpectrum.basicOpen_mul]
  exact le_antisymm
    (le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
    (le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
      (inf_le_left.trans inf_le_right))

/-- Pointwise folding of a triple composite of presheaf-restriction maps into a single one.  With
the presheaf `Q` abstracted (as in `res_trans_apply`), `← ModuleCat.comp_apply` matches cleanly,
avoiding the `↑R`-Semiring instance diamond that an inline `∘ₗ` over `basicOpen` sections triggers.
Project-local glue for the overlap-opens transport of `overlap_section_localization`. -/
private lemma presheaf_map_comp₂_apply (Q : TopCat.Presheaf (ModuleCat R) (Spec R))
    {A B C D : (Spec R).Opensᵒᵖ} (m1 : A ⟶ B) (m2 : B ⟶ C) (m3 : C ⟶ D) (x : Q.obj A) :
    (Q.map m3).hom ((Q.map m2).hom ((Q.map m1).hom x)) = (Q.map (m1 ≫ m2 ≫ m3)).hom x := by
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← Q.map_comp, ← Q.map_comp]

/-- **Per-overlap section localisation.**  For a quasi-coherent `F`, elements `f a b : R` with
`D(a) ⊆ U` and `F.over U` globally presented, the section-restriction
`Γ(D(a) ⊓ D(b), F) → Γ(D(af) ⊓ D(bf), F)` exhibits its target as the localisation of its source at
the powers of `f`.  This is `tile_section_localization` for `g = a·b` transported along the overlap
opens identities `D(a·b) = D(a) ⊓ D(b)` and `D((a·b)·f) = D(af) ⊓ D(bf)`.  Project-local: the
overlap vertical map of the keystone kernel comparison (`qcoh_section_isLocalizedModule`). -/
private lemma overlap_section_localization (F : (Spec R).Modules) (U : (Spec R).Opens)
    (P : (F.over U).Presentation) (f a b : R) (ha : specBasicOpen a ≤ U) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj F).presheaf.map
        (homOfLE (inf_le_inf ((PrimeSpectrum.basicOpen_mul a f).le.trans inf_le_left)
          ((PrimeSpectrum.basicOpen_mul b f).le.trans inf_le_left) :
          specBasicOpen (a * f) ⊓ specBasicOpen (b * f)
            ≤ specBasicOpen a ⊓ specBasicOpen b)).op).hom := by
  have hab : specBasicOpen (a * b) ≤ U :=
    ((PrimeSpectrum.basicOpen_mul a b).le.trans inf_le_left).trans ha
  -- the tile restriction `Γ(D(a·b),F) → Γ(D((a·b)·f),F)` localises at `powers f`
  haveI hμ0 : IsLocalizedModule (Submonoid.powers f)
      (((modulesSpecToSheaf.obj F).presheaf.map
        (homOfLE ((PrimeSpectrum.basicOpen_mul (a * b) f).le.trans inf_le_left :
          specBasicOpen (a * b * f) ≤ specBasicOpen (a * b))).op).hom) :=
    tile_section_localization F U P f (a * b) hab
  -- transport source `D(a·b) = D a ⊓ D b` and target `D((a·b)·f) = D(af) ⊓ D(bf)`
  let eqSrc := ((modulesSpecToSheaf.obj F).presheaf.mapIso
    (eqToIso (congrArg Opposite.op (PrimeSpectrum.basicOpen_mul a b).symm))).toLinearEquiv
  let eqTgt := ((modulesSpecToSheaf.obj F).presheaf.mapIso
    (eqToIso (congrArg Opposite.op (overlap_target_eq a b f)))).toLinearEquiv
  have h4 := IsLocalizedModule.of_linearEquiv (Submonoid.powers f)
    (((modulesSpecToSheaf.obj F).presheaf.map
      (homOfLE ((PrimeSpectrum.basicOpen_mul (a * b) f).le.trans inf_le_left :
        specBasicOpen (a * b * f) ≤ specBasicOpen (a * b))).op).hom ∘ₗ eqSrc.toLinearMap) eqTgt
  have keyB : (eqTgt.toLinearMap ∘ₗ
        (((modulesSpecToSheaf.obj F).presheaf.map
          (homOfLE ((PrimeSpectrum.basicOpen_mul (a * b) f).le.trans inf_le_left :
            specBasicOpen (a * b * f) ≤ specBasicOpen (a * b))).op).hom ∘ₗ eqSrc.toLinearMap))
      = ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE (inf_le_inf
            ((PrimeSpectrum.basicOpen_mul a f).le.trans inf_le_left)
            ((PrimeSpectrum.basicOpen_mul b f).le.trans inf_le_left) :
          specBasicOpen (a * f) ⊓ specBasicOpen (b * f)
            ≤ specBasicOpen a ⊓ specBasicOpen b)).op).hom := by
    apply LinearMap.ext; intro x
    simp only [eqSrc, eqTgt, CategoryTheory.Iso.toLinearMap_toLinearEquiv, Functor.mapIso_hom,
      eqToIso.hom, LinearMap.comp_apply]
    refine (presheaf_map_comp₂_apply (modulesSpecToSheaf.obj F).presheaf _ _ _ x).trans ?_
    exact congrArg (fun m => ((modulesSpecToSheaf.obj F).presheaf.map m).hom x)
      (Subsingleton.elim _ _)
  rw [← keyB]
  exact h4

set_option backward.isDefEq.respectTransparency false in
/-- **Route B keystone (Stacks 01HV(4)/01I8).**  For a quasi-coherent `F` on `Spec R` and `f ∈ R`,
the section-restriction `ρ_f : Γ(X, F) → Γ(D(f), F)` exhibits its target as the localisation of its
source at the powers of `f`.  This is the generalisation of `Γ(D(f), M^~) = M_f` from the associated
sheaf `M^~` to an arbitrary quasi-coherent `F`, and the single load-bearing input of Route B.
Assembled from the two degree-`0/1` sheaf-axiom equalizers (`qcoh_section_equalizer` at `W = ⊤` over
`{D(gⱼ)}` and at `W = D(f)` over `{D(gⱼf)}`), the per-tile section localisations
(`tile_section_localization`, `overlap_section_localization`) as the middle/overlap vertical maps,
and the abstract kernel comparison `isLocalizedModule_of_exact`.  Non-circular: every
"sections-localise" input lives on a globally-presented tile, never on the global object. -/
lemma qcoh_section_isLocalizedModule (F : (Spec R).Modules) [F.IsQuasicoherent] (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj F).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by
  obtain ⟨q, n, g, φ, hgU, hspan⟩ := qcoh_finite_presentation_cover F
  -- the two finite covers (indexed by `ULift (Fin n)` for the universe of `qcoh_section_equalizer`)
  set U1 : ULift.{u} (Fin n) → (Spec R).Opens := fun i => specBasicOpen (g i.down) with hU1
  set U2 : ULift.{u} (Fin n) → (Spec R).Opens := fun i => specBasicOpen (g i.down * f) with hU2
  -- `U2 i = D(gᵢ) ⊓ D(f) ≤ D(f)`, and `U2 i ≤ U1 i`
  have hU2le : ∀ i, U2 i ≤ specBasicOpen f := fun i =>
    (PrimeSpectrum.basicOpen_mul (g i.down) f).le.trans inf_le_right
  have hble : ∀ i, U2 i ≤ U1 i := fun i =>
    (PrimeSpectrum.basicOpen_mul (g i.down) f).le.trans inf_le_left
  -- covering facts
  have hcov1 : (⊤ : (Spec R).Opens) ≤ ⨆ i, U1 i := by
    have hre : ⨆ i, U1 i = ⨆ j : Fin n, specBasicOpen (g j) :=
      le_antisymm (iSup_le fun i => le_iSup (fun j => specBasicOpen (g j)) i.down)
        (iSup_le fun j => le_iSup U1 (ULift.up j))
    rw [hre]
    exact le_of_eq (PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hspan).symm
  have hcov2 : specBasicOpen f ≤ ⨆ i, U2 i := by
    intro x hx
    rw [TopologicalSpace.Opens.mem_iSup]
    have hxtop : x ∈ ⨆ i, U1 i := hcov1 trivial
    rw [TopologicalSpace.Opens.mem_iSup] at hxtop
    obtain ⟨i, hi⟩ := hxtop
    refine ⟨i, ?_⟩
    have hmem : U2 i = specBasicOpen (g i.down) ⊓ specBasicOpen f :=
      PrimeSpectrum.basicOpen_mul (g i.down) f
    rw [hmem]
    exact ⟨hi, hx⟩
  -- the two degree-0/1 equalizers
  obtain ⟨hi1, hp1⟩ := qcoh_section_equalizer F ⊤ U1 (fun _ => le_top) hcov1
  obtain ⟨hi2, hp2⟩ := qcoh_section_equalizer F (specBasicOpen f) U2 hU2le hcov2
  -- middle vertical `b`: product of per-tile localisations
  haveI hbtile : ∀ i, IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE (hble i)).op).hom :=
    fun i => tile_section_localization F (q.X (φ i.down)) (q.presentation (φ i.down)) f
      (g i.down) (hgU i.down)
  have hb : IsLocalizedModule (Submonoid.powers f)
      (LinearMap.pi fun i =>
        ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE (hble i)).op).hom ∘ₗ LinearMap.proj i) :=
    IsLocalizedModule.pi (Submonoid.powers f)
      (fun i => ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE (hble i)).op).hom)
  -- overlap vertical `c`: product of per-overlap localisations
  have hcle : ∀ pp : ULift.{u} (Fin n) × ULift.{u} (Fin n), U2 pp.1 ⊓ U2 pp.2 ≤ U1 pp.1 ⊓ U1 pp.2 :=
    fun pp => inf_le_inf (hble pp.1) (hble pp.2)
  haveI hctile : ∀ pp : ULift.{u} (Fin n) × ULift.{u} (Fin n),
      IsLocalizedModule (Submonoid.powers f)
        ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE (hcle pp)).op).hom :=
    fun pp => overlap_section_localization F (q.X (φ pp.1.down)) (q.presentation (φ pp.1.down)) f
      (g pp.1.down) (g pp.2.down) (hgU pp.1.down)
  have hc : IsLocalizedModule (Submonoid.powers f)
      (LinearMap.pi fun pp : ULift.{u} (Fin n) × ULift.{u} (Fin n) =>
        ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE (hcle pp)).op).hom
          ∘ₗ LinearMap.proj pp) :=
    IsLocalizedModule.pi (Submonoid.powers f)
      (fun pp => ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE (hcle pp)).op).hom)
  refine isLocalizedModule_of_exact (Submonoid.powers f) _ _ _ _ _ _ _ hi1 hi2 hp1 hp2 hb hc ?_ ?_
  · -- sq1 : `ρ' ∘ ρ_f = b ∘ ρ` (`change` reduces the `LinearMap.pi` applications by defeq, then
    -- presheaf functoriality `res_trans_apply` folds both composites to `Γ(⊤) → Γ(D(gⱼf))`)
    apply LinearMap.ext; intro s; funext i
    change ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE (hU2le i)).op).hom
          (((modulesSpecToSheaf.obj F).presheaf.map
            (homOfLE (le_top : specBasicOpen f ≤ ⊤)).op).hom s)
        = ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE (hble i)).op).hom
          (((modulesSpecToSheaf.obj F).presheaf.map (homOfLE (le_top : U1 i ≤ ⊤)).op).hom s)
    rw [res_trans_apply, res_trans_apply]
  · -- sq2 : `δ' ∘ b = c ∘ δ` (same idea; `map_sub` distributes the overlap differential, then
    -- four `res_trans_apply` folds match the two routes to `Γ(D(gⱼ)) → Γ(D(gⱼgₖf))`)
    apply LinearMap.ext; intro y; funext pp
    change ((modulesSpecToSheaf.obj F).presheaf.map
            (homOfLE (inf_le_right : U2 pp.1 ⊓ U2 pp.2 ≤ U2 pp.2)).op).hom
          (((modulesSpecToSheaf.obj F).presheaf.map (homOfLE (hble pp.2)).op).hom (y pp.2))
        - ((modulesSpecToSheaf.obj F).presheaf.map
            (homOfLE (inf_le_left : U2 pp.1 ⊓ U2 pp.2 ≤ U2 pp.1)).op).hom
          (((modulesSpecToSheaf.obj F).presheaf.map (homOfLE (hble pp.1)).op).hom (y pp.1))
      = ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE (hcle pp)).op).hom
          (((modulesSpecToSheaf.obj F).presheaf.map
              (homOfLE (inf_le_right : U1 pp.1 ⊓ U1 pp.2 ≤ U1 pp.2)).op).hom (y pp.2)
            - ((modulesSpecToSheaf.obj F).presheaf.map
                (homOfLE (inf_le_left : U1 pp.1 ⊓ U1 pp.2 ≤ U1 pp.1)).op).hom (y pp.1))
    rw [map_sub, res_trans_apply, res_trans_apply, res_trans_apply, res_trans_apply]

/-- **Kernel comparison (Stacks 01HV(4)/01I8), packaged form.**  For a quasi-coherent `F` on
`Spec R` and `f ∈ R`, the canonical `R`-linear localisation lift `Γ(X, F)_f → Γ(D(f), F)` of the
section-restriction `ρ_f` is an isomorphism: explicitly, `LocalizedModule (powers f) Γ(X, F)` is
linearly equivalent to `Γ(D(f), F)`.  This is the `IsLocalizedModule.iso` repackaging of the
keystone `qcoh_section_isLocalizedModule`; it is the form the blueprint kernel-comparison node
names and that the `D(f)`-component of `fromTildeΓ` consumes.  Project-local. -/
noncomputable def qcoh_section_kernel_comparison (F : (Spec R).Modules) [F.IsQuasicoherent]
    (f : R) :
    LocalizedModule (Submonoid.powers f)
        ((modulesSpecToSheaf.obj F).presheaf.obj (Opposite.op (⊤ : (Spec R).Opens)))
      ≃ₗ[R] (modulesSpecToSheaf.obj F).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen f)) :=
  @IsLocalizedModule.iso _ _ (Submonoid.powers f) _ _ _ _ _ _ _
    (qcoh_section_isLocalizedModule F f)

end KernelComparisonAssembly

/-! ## Project-local Mathlib supplement — Route B assembly: the tilde–Γ counit is an iso (01I8)

`isIso_fromTildeΓ_of_quasicoherent` is the LAST step of Stacks 01I8: for a quasi-coherent `F` on
`Spec R` the tilde–Γ counit `fromTildeΓ : tilde(Γ F) ⟶ F` is an isomorphism.  It is checked on the
basis of distinguished opens `{D(r)}`: the `D(r)`-component of the underlying sheaf morphism is the
localization lift of the section-restriction `ρ_r` along `tilde.toOpen` (Mathlib's
`toOpen_fromTildeΓ_app`).  Both `tilde.toOpen` (Mathlib instance) and `ρ_r` (the keystone
`qcoh_section_isLocalizedModule`) localize `Γ(X,F)` at the powers of `r`, so that lift is an
isomorphism (`IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp`).  Registered as an
`instance`, it makes `qcoh_iso_tilde_sections F` available unconditionally for quasi-coherent
`F`. -/

section IsoFromTildeGammaAssembly

open PrimeSpectrum

/-- The `D(r)`-component of the underlying sheaf morphism of `fromTildeΓ` is an isomorphism, for a
quasi-coherent `F`.  By Mathlib's `toOpen_fromTildeΓ_app` this component `c` satisfies
`c ∘ tilde.toOpen = ρ_r`, the section-restriction `Γ(X,F) → Γ(D(r),F)`.  Both `tilde.toOpen`
(Mathlib instance) and `ρ_r` (keystone `qcoh_section_isLocalizedModule`) are localizations at the
powers of `r`, so `c` is the linear equivalence between the two localizations
(`IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp`), hence an iso.  Project-local
component step of `isIso_fromTildeΓ_of_quasicoherent`. -/
private lemma isIso_fromTildeΓ_app_basicOpen (F : (Spec R).Modules) [F.IsQuasicoherent] (r : R) :
    IsIso ((modulesSpecToSheaf.map F.fromTildeΓ).hom.app
      (Opposite.op (PrimeSpectrum.basicOpen r))) := by
  set c := (modulesSpecToSheaf.map F.fromTildeΓ).hom.app
    (Opposite.op (PrimeSpectrum.basicOpen r)) with hc
  -- `tilde.toOpen` is itself a localization at the powers of `r` (Mathlib instance)
  haveI hlf : IsLocalizedModule (Submonoid.powers r)
      (tilde.toOpen ((modulesSpecToSheaf.obj F).presheaf.obj (.op ⊤))
        (PrimeSpectrum.basicOpen r)).hom := inferInstance
  -- `ρ_r` is a localization at the powers of `r` (the keystone)
  haveI hlg : IsLocalizedModule (Submonoid.powers r)
      ((modulesSpecToSheaf.obj F).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen r ≤ ⊤)).op).hom :=
    qcoh_section_isLocalizedModule F r
  -- `tilde.toOpen ≫ c = ρ_r` (Mathlib), read at the linear-map level as `c.hom ∘ₗ toOpen.hom = ρ_r`
  have hcomp := Scheme.Modules.toOpen_fromTildeΓ_app F (PrimeSpectrum.basicOpen r)
  have hcomp' : c.hom ∘ₗ
        (tilde.toOpen ((modulesSpecToSheaf.obj F).presheaf.obj (.op ⊤))
          (PrimeSpectrum.basicOpen r)).hom
      = ((modulesSpecToSheaf.obj F).presheaf.map
          (homOfLE (le_top : PrimeSpectrum.basicOpen r ≤ ⊤)).op).hom := by
    rw [← ModuleCat.hom_comp]
    exact congrArg ModuleCat.Hom.hom hcomp
  haveI hcl : IsLocalizedModule (Submonoid.powers r)
      (c.hom ∘ₗ
        (tilde.toOpen ((modulesSpecToSheaf.obj F).presheaf.obj (.op ⊤))
          (PrimeSpectrum.basicOpen r)).hom) := by
    rw [hcomp']; exact hlg
  -- `c.hom` agrees with the canonical equiv between the two localizations of `Γ(X,F)`
  set e := IsLocalizedModule.linearEquiv (Submonoid.powers r)
    (tilde.toOpen ((modulesSpecToSheaf.obj F).presheaf.obj (.op ⊤))
      (PrimeSpectrum.basicOpen r)).hom
    (c.hom ∘ₗ (tilde.toOpen ((modulesSpecToSheaf.obj F).presheaf.obj (.op ⊤))
      (PrimeSpectrum.basicOpen r)).hom) with he
  have hce : c.hom = e.toLinearMap := by
    apply IsLocalizedModule.ext (Submonoid.powers r)
      (tilde.toOpen ((modulesSpecToSheaf.obj F).presheaf.obj (.op ⊤))
        (PrimeSpectrum.basicOpen r)).hom hcl.map_units
    ext x
    simp only [he, LinearMap.comp_apply, LinearEquiv.coe_coe, IsLocalizedModule.linearEquiv_apply]
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective ⇑c.hom
  rw [hce]
  exact e.bijective

/-- **The tilde–Γ counit is an isomorphism for quasi-coherent `F` (Stacks 01I8).**  For
`X = Spec R` and a quasi-coherent `𝒪_X`-module `F`, the tilde–Γ counit
`fromTildeΓ : tilde(Γ(X,F)) ⟶ F` is an isomorphism.  Proved by checking on the basis of
distinguished opens (`isIso_fromTildeΓ_app_basicOpen`) and reflecting through the fully faithful
`modulesSpecToSheaf` and the cover-dense basic-open subsite.  Registered as an `instance` so that
`qcoh_iso_tilde_sections F` becomes unconditional for quasi-coherent `F`.  Project-local: this is
the affine structure theorem 01I8, the implication absent from Mathlib. -/
instance isIso_fromTildeΓ_of_quasicoherent (F : (Spec R).Modules) [F.IsQuasicoherent] :
    IsIso F.fromTildeΓ := by
  suffices h : IsIso (modulesSpecToSheaf.map F.fromTildeΓ) from
    SpecModulesToSheafFullyFaithful.isIso_of_isIso_map F.fromTildeΓ
  haveI hcd : (inducedFunctor (fun r : R => specBasicOpen r)).IsCoverDense
      (Opens.grothendieckTopology ↥(Spec R)) :=
    TopCat.Opens.coverDense_inducedFunctor PrimeSpectrum.isBasis_basic_opens
  apply Functor.IsCoverDense.iso_of_restrict_iso
    (G := inducedFunctor (fun r : R => specBasicOpen r))
  haveI : ∀ X, IsIso (((inducedFunctor (fun r : R => specBasicOpen r)).op.whiskerLeft
      (modulesSpecToSheaf.map F.fromTildeΓ).hom).app X) :=
    fun X => isIso_fromTildeΓ_app_basicOpen F X.unop
  exact NatIso.isIso_of_isIso_app _

end IsoFromTildeGammaAssembly

/-! ## Handoff — closing the 01I8 gap

The unconditional quasi-coherent statement

```
theorem qcoh_iso_tilde_sections_qcoh (F : (Spec R).Modules) [IsQuasicoherent F] :
    F ≅ tilde (moduleSpecΓFunctor.obj F)
```

is obtained from `qcoh_iso_tilde_sections` the instant the following instance is available:

```
instance (F : (Spec R).Modules) [IsQuasicoherent F] : IsIso F.fromTildeΓ
```

equivalently (by `isIso_fromTildeΓ_iff`) `(tilde.functor R).essImage F`, equivalently a
**global** `F.Presentation` (fed to `qcoh_iso_tilde_sections_of_presentation`).

The needed Mathlib-gradient sub-steps (all on the affine base `Spec R`):

1. `IsQuasicoherent F` ⟹ `F` is generated by global sections: produce
   `F.GeneratingSections` (a global epi `free I ⟶ F`).  On `Spec R` this is the affine
   global-generation statement (Hartshorne II.5.16 / Stacks 01I8); `QuasicoherentData`
   only gives generation locally on a basic-open cover, which must be globalised using
   `PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen`-style partition-of-unity /
   the compactness of `Spec R` and the localisation-of-sections property of qcoh sheaves.
   **This is the single genuine remaining blocker** (sections of qcoh `F` over `D(f)`
   localise — `Γ(D(f), F) = Γ(X, F)_f`, Stacks 01HV(4)/01I8 — is itself absent from Mathlib:
   `grep` confirms the only `IsQuasicoherent` content in `Mathlib/AlgebraicGeometry/` is
   `Modules/Tilde.lean`, with no localisation-of-sections and no abelian-subcategory closure).
2. The kernel of `free I ⟶ F` is again quasi-coherent on `Spec R` (NB: not yet a Mathlib
   instance — `kernel σ.π` is not automatically qcoh; this needs the qcoh-is-abelian-subcategory
   fact, itself downstream of step 1's local structure), hence again globally generated by
   step 1; this yields the two `GeneratingSections` `σ`, `τ` of `F.Presentation`.
3. Feed those two generating families to `isIso_fromTildeΓ_of_genSections` (below), which
   bundles them into `F.Presentation` and applies Mathlib's `isIso_fromTildeΓ_of_presentation`,
   producing the `IsIso F.fromTildeΓ` instance above.

**Steps 2–3 are now formalised** as the axiom-clean `isIso_fromTildeΓ_of_genSections` and
`qcoh_iso_tilde_sections_of_genSections` (the structure theorem directly from the two generating
families), with `free_isQuasicoherent` recording that free coefficient sheaves are qcoh.  Step 1 —
the load-bearing ~few-hundred-LOC affine global-generation / localisation-of-sections input — is
the single genuine mathematical blocker; once it supplies `σ : F.GeneratingSections` and
`τ : (kernel σ.π).GeneratingSections` for a quasi-coherent `F`, the instance and the unconditional
upgrade of `qcoh_iso_tilde_sections` follow with no further work.
-/

end AlgebraicGeometry
