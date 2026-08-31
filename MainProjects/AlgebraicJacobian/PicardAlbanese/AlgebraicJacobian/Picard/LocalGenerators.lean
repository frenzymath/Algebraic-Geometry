/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Local generators of a finite projective module (DAT-A generators corollary)

Worksheet §2.2.3a (`informal/spec-dat-a.md` §4): for a finite projective module `Q`
over `B` — the engine's `H⁰` on the fibrewise-vanishing locus (`datumRigidEngine`) —
and a prime `p` where the fibre `Q ⊗ κ(p)` is nontrivial, there is a basic open
`D(f) ∋ p` and a GLOBAL element `q : Q` whose image in `Q ⊗ κ(q')` is nonzero for
EVERY `q' ∈ D(f)`:

> Zariski-locally on `Spec B`, a fibrewise-nonzero section exists.

Route: finite + projective ⟹ finitely presented + flat; `Module.freeLocus_eq_univ`
gives freeness at `p`; `Module.FinitePresentation.exists_free_localizedModule_powers`
localizes the freeness to a basic open `D(f)`; a basis element of the localized module
has numerator `q`; at every `q' ∈ D(f)` the coordinate functional of the basis,
composed with the away-lift `B_f →+* κ(q')` (legal since `f ∉ q'` makes `f` invertible
in the residue field), evaluates the fibre image of `q` to a nonzero power of the image
of `f` — no localized tensor products are formed.

Consumers (stated for verbatim consumption): DAT-B's coverage (a local divisor
presentation of an arbitrary functor point through DAT-A's `sectionLocalEquations`) and
DD-R's local generators (dat-d-worksheet §3.4). The `Nontrivial` fibre input is the
rank clause consumers hold through FLV/DAT-3.
-/

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace Module

variable {B : Type u} [CommRing B] {Q : Type u} [AddCommGroup Q] [Module B Q]

/-- If some localization of `Q` away from an element of `p.primeCompl` is trivial, the
residue-field fibre at `p` is trivial: the annihilating power of `f` is invertible in
`κ(p)`. -/
private lemma subsingleton_tensor_residueField_of_subsingleton_away
    (p : PrimeSpectrum B) (f : B) (hf : f ∉ p.asIdeal)
    (hsub : Subsingleton (LocalizedModule.Away f Q)) :
    Subsingleton (Q ⊗[B] p.asIdeal.ResidueField) := by
  have hx : algebraMap B p.asIdeal.ResidueField f ≠ 0 := fun h0 =>
    hf (Ideal.algebraMap_residueField_eq_zero.mp h0)
  refine subsingleton_of_forall_eq 0 (fun z => ?_)
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | add u v hu hv => rw [hu, hv, add_zero]
  | tmul q c =>
      -- the localized image of `q` vanishes, so a power of `f` kills `q`
      have hmk : (LocalizedModule.mk q 1 : LocalizedModule.Away f Q)
          = LocalizedModule.mk 0 1 := Subsingleton.elim _ _
      obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp hmk
      rw [one_smul, one_smul, smul_zero] at hu
      -- transfer `u • q = 0` through the tensor, inverting `u` in the residue field
      have hu_ne : algebraMap B p.asIdeal.ResidueField (u : B) ≠ 0 := by
        obtain ⟨n, hn⟩ := u.2
        intro h0
        rw [← hn, map_pow] at h0
        exact hx (pow_eq_zero_iff' .. |>.mp h0).1
      have hu' : (u : B) • q = 0 := hu
      have hkill : q ⊗ₜ[B] ((algebraMap B p.asIdeal.ResidueField (u : B))
          * ((algebraMap B p.asIdeal.ResidueField (u : B))⁻¹ * c)) = 0 := by
        have hz : ((u : B) • q) ⊗ₜ[B]
            ((algebraMap B p.asIdeal.ResidueField (u : B))⁻¹ * c) = 0 := by
          rw [hu', TensorProduct.zero_tmul]
        rw [TensorProduct.smul_tmul, Algebra.smul_def] at hz
        exact hz
      rwa [mul_inv_cancel_left₀ hu_ne] at hkill

/-- **The generators corollary** (worksheet §2.2.3a; DAT-B/DD-R's local generators):
for a finite projective `B`-module `Q` with nontrivial residue-field fibre at `p`,
there are `f ∉ p` and a global `q : Q` whose image in `Q ⊗ κ(q')` is nonzero for
**every** prime `q'` of the basic open `D(f)` — Zariski-locally, a fibrewise-nonzero
section of `Q` exists. -/
theorem exists_fibrewise_tmul_ne_zero_of_projective
    [Module.Finite B Q] [Module.Projective B Q] (p : PrimeSpectrum B)
    (hp : Nontrivial (Q ⊗[B] p.asIdeal.ResidueField)) :
    ∃ f : B, f ∉ p.asIdeal ∧ ∃ q : Q, ∀ q' : PrimeSpectrum B, f ∉ q'.asIdeal →
      (q ⊗ₜ (1 : q'.asIdeal.ResidueField) : Q ⊗[B] q'.asIdeal.ResidueField) ≠ 0 := by
  classical
  haveI : Module.FinitePresentation B Q := Module.finitePresentation_of_projective B Q
  -- freeness at `p`, localized to a basic open `D(f)`
  haveI hfree_p : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal Q) := by
    have hmem : p ∈ Module.freeLocus B Q := by
      rw [Module.freeLocus_eq_univ]
      trivial
    exact Module.mem_freeLocus.mp hmem
  obtain ⟨f, hf, hfree, -⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl Q)
      (Localization.AtPrime p.asIdeal)
  haveI := hfree
  -- the localized module is nontrivial (else the fibre at `p` would be trivial)
  haveI hnt : Nontrivial (LocalizedModule.Away f Q) := by
    by_contra hns
    rw [not_nontrivial_iff_subsingleton] at hns
    exact (not_subsingleton _)
      (subsingleton_tensor_residueField_of_subsingleton_away p f hf hns)
  -- a basis element, with numerator `q` and denominator a power of `f`
  let b := Module.Free.chooseBasis (Localization (.powers f)) (LocalizedModule.Away f Q)
  obtain ⟨i₀⟩ := b.index_nonempty
  obtain ⟨⟨q, s⟩, hqs⟩ : ∃ ms : Q × (Submonoid.powers f),
      (LocalizedModule.mk ms.1 ms.2 : LocalizedModule.Away f Q) = b i₀ :=
    LocalizedModule.induction_on (fun m s => ⟨(m, s), rfl⟩) (b i₀)
  refine ⟨f, hf, q, fun q' hq' => ?_⟩
  -- the residue field of `q'` receives the away-localization
  have hx : algebraMap B q'.asIdeal.ResidueField f ≠ 0 := fun h0 =>
    hq' (Ideal.algebraMap_residueField_eq_zero.mp h0)
  have hxu : IsUnit (algebraMap B q'.asIdeal.ResidueField f) :=
    isUnit_iff_ne_zero.mpr hx
  set g' : Localization (Submonoid.powers f) →+* q'.asIdeal.ResidueField :=
    IsLocalization.Away.lift f hxu with hg'
  -- the evaluation functional: coordinate of the basis at `i₀`, pushed to `κ(q')`
  set Λ : Q ⊗[B] q'.asIdeal.ResidueField →ₗ[B] q'.asIdeal.ResidueField :=
    TensorProduct.lift (LinearMap.mk₂ B
      (fun m c => g' ((b.coord i₀) (LocalizedModule.mk m 1)) * c)
      (fun m m' c => by
        rw [show (LocalizedModule.mk (m + m') 1 : LocalizedModule.Away f Q)
            = LocalizedModule.mk m 1 + LocalizedModule.mk m' 1 from
          (LocalizedModule.mkLinearMap (.powers f) Q).map_add m m', map_add, map_add,
          add_mul])
      (fun a m c => by
        rw [show (LocalizedModule.mk (a • m) 1 : LocalizedModule.Away f Q)
            = a • LocalizedModule.mk m 1 from
          (LocalizedModule.mkLinearMap (.powers f) Q).map_smul a m,
          ← algebraMap_smul (Localization (Submonoid.powers f)) a, map_smul,
          smul_eq_mul, map_mul, IsLocalization.Away.lift_eq, ← Algebra.smul_def,
          smul_mul_assoc])
      (fun m c c' => by rw [mul_add])
      (fun a m c => by rw [mul_smul_comm])) with hΛ
  -- `Λ` evaluates the fibre image of `q` to a nonzero power of the image of `f`
  intro h0
  have hval := congrArg Λ h0
  rw [map_zero, hΛ, TensorProduct.lift.tmul] at hval
  -- compute the coordinate: `mk q 1 = s • b i₀`, and `coord i₀ (b i₀) = 1`
  have hmk1 : (LocalizedModule.mk q 1 : LocalizedModule.Away f Q) = (s : B) • b i₀ := by
    rw [← hqs]
    change _ = (s : B) • (LocalizedModule.mk q s : LocalizedModule.Away f Q)
    rw [LocalizedModule.smul'_mk, ← Submonoid.smul_def, LocalizedModule.mk_cancel]
  have hcoord : (b.coord i₀) (LocalizedModule.mk q 1)
      = algebraMap B (Localization (Submonoid.powers f)) (s : B) := by
    rw [hmk1, ← algebraMap_smul (Localization (Submonoid.powers f)) (s : B) (b i₀),
      map_smul, smul_eq_mul, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_eq_same, mul_one]
  rw [LinearMap.mk₂_apply, hcoord, IsLocalization.Away.lift_eq, mul_one] at hval
  -- the value is a nonzero power of the image of `f`
  obtain ⟨n, hn⟩ := s.2
  rw [← hn, map_pow] at hval
  exact pow_ne_zero n hx hval

end Module
