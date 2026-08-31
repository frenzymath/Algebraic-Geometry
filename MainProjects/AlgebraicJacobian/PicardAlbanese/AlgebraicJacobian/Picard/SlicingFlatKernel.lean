/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# The kernel-flattening brick (certificate clauses (c3)/(c4), G-4)

**Pure commutative algebra** (mathlib-only imports; no project geometry). Two layers:

## The fibrewise-injectivity engine (`ψ : P → N` injective on every residue fibre)

For a linear map `ψ : P →ₗ[R] N` with `P` finite (resp. finitely presented) and `N` finite
flat, such that `ψ ⊗ κ(p)` is injective for **every** prime `p`:

* `Module.Projective.of_forall_rTensor_residueField_injective` — `P` is projective;
* `LinearMap.injective_of_forall_rTensor_residueField_injective` — `ψ` is injective;
* `Module.Flat.quotient_range_of_forall_rTensor_residueField_injective` —
  `N ⧸ range ψ` is flat.

Route: at each maximal ideal, `ψ` localizes to a **split** injection between a finite and
a finite free module over the local ring
(`IsLocalRing.split_injective_iff_lTensor_residueField_injective`, with the cokernel free
by `Module.free_of_lTensor_residueField_injective` — Matsumura 22.5-style, but with an
elementary basis-lifting proof in mathlib, no local criterion of flatness);
projectivity, injectivity and flatness then globalize
(`Module.projective_of_localization_maximal`, `injective_of_localized_maximal`,
`Module.flat_of_localized_maximal`). The residue fibre of the localized map is identified
with the original residue fibre through `LocalizedModule.equivTensorProduct` and
`AlgebraTensorModule.cancelBaseChange` (`residueFieldLocEquiv`).

## The kernel-flattening keystones (the (c3)/(c4) table row of `w4-g4-worksheet` §3)

For `f : M →ₗ[R] N` between finite flat modules over a **Noetherian** `R` and a submodule
`L ≤ ker f` whose residue-fibre images span every fibre kernel —

`hspan : ∀ p, ker (f ⊗ κ(p)) ≤ range (L.subtype ⊗ κ(p))`

(the **fibrewise-spanning** hypothesis; the fibre kernels are spanned by *relative* elements)
— the k[ε]-trap is ruled out and the naive constant-fibre-rank pin becomes true:

* `Module.Projective.quotient_of_forall_ker_rTensor_residueField_le` — `M ⧸ L` projective;
* `Submodule.eq_ker_of_forall_ker_rTensor_residueField_le` — `L = ker f`;
* `Module.Flat.quotient_ker_of_forall_ker_rTensor_residueField_le` — `M ⧸ ker f` flat (**c3**);
* `Module.Flat.quotient_range_of_forall_ker_rTensor_residueField_le` — `N ⧸ range f` flat (**c4**);
* `Module.Projective.ker_of_forall_ker_rTensor_residueField_le` — `ker f` finite projective
  (finiteness is automatic: submodule of a finite module over a Noetherian ring);
* `LinearMap.rTensor_subtype_injective_of_forall_ker_rTensor_residueField_le` and
  `LinearMap.range_rTensor_subtype_eq_ker_of_forall_ker_rTensor_residueField_le` — formation
  of `ker f` commutes with residue fields: `L ⊗ κ(p) ≅ ker (f ⊗ κ(p))`;
* `Module.rankAtStalk_ker_eq_finrank_ker_baseChange` /
  `Module.rankAtStalk_ker_eq_of_forall_finrank_eq` — `rankAtStalk (ker f) p` equals the
  fibre-kernel dimension (`= g` when the fibres are `g`-dimensional) (**c2** rank clause).

Route: `hspan` says exactly that the induced map `M ⧸ L → N` is injective on every residue
fibre (right-exactness of `− ⊗ κ(p)`), so the engine applies to it; `L = ker f` and the split
SES `0 → L → M → M ⧸ L → 0` (projective quotient) give the rest.

## The `k[ε]` guard

Constant fibre-kernel dimension alone is FALSE: `R = k[ε]`, `f = (ε •) : R → R` has
`ker (f ⊗ κ) = κ` at the unique prime (constant dimension 1), but `ker f = (ε)` is not
projective and `R ⧸ (ε)` is not flat. `hspan` fails there: every element of `(ε)` maps to
zero in the fibre `R ⊗ κ = k`, so the fibre kernel is *not* spanned by relative elements.
Any weakening of `hspan` must keep this example excluded.
-/

set_option autoImplicit false

universe u v w

open scoped TensorProduct

/-! ## Residue fibres of localized modules -/

section LocalizedFibre

variable {R : Type u} [CommRing R]

/-- The residue fibre of the localized module at `q` is the residue fibre of the module:
`κ(q) ⊗[R_q] X_q ≃ κ(q) ⊗[R] X`. -/
private noncomputable def residueFieldLocEquiv (q : Ideal R) [q.IsPrime]
    (X : Type*) [AddCommGroup X] [Module R X] :
    q.ResidueField ⊗[Localization.AtPrime q] LocalizedModule q.primeCompl X
      ≃ₗ[q.ResidueField] q.ResidueField ⊗[R] X :=
  (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl q.ResidueField q.ResidueField)
      (LocalizedModule.equivTensorProduct q.primeCompl X)) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime q)
      q.ResidueField q.ResidueField X

/-- Naturality of `residueFieldLocEquiv` against `LocalizedModule.map`. -/
private lemma residueFieldLocEquiv_map {X : Type v} {Y : Type w}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (q : Ideal R) [q.IsPrime] (φ : X →ₗ[R] Y)
    (t : q.ResidueField ⊗[Localization.AtPrime q] LocalizedModule q.primeCompl X) :
    residueFieldLocEquiv q Y
        (((LocalizedModule.map q.primeCompl φ).lTensor q.ResidueField) t)
      = (φ.lTensor q.ResidueField) (residueFieldLocEquiv q X t) := by
  induction t with
  | zero => simp
  | tmul c x =>
      induction x using LocalizedModule.induction_on with
      | _ m s =>
          simp [residueFieldLocEquiv, LocalizedModule.equivTensorProduct_apply_mk]
  | add x y hx hy => simp [hx, hy]

/-- Fibrewise injectivity transports to the localized map: if `φ ⊗ κ(q)` is injective, so
is `κ(q) ⊗ (φ_q)`. -/
private lemma injective_lTensor_residueField_localizedMap {X : Type v} {Y : Type w}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (q : Ideal R) [q.IsPrime] (φ : X →ₗ[R] Y)
    (hfib : Function.Injective (φ.rTensor q.ResidueField)) :
    Function.Injective ((LocalizedModule.map q.primeCompl φ).lTensor q.ResidueField) := by
  have hl : Function.Injective (φ.lTensor q.ResidueField) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj _ _).mpr hfib
  intro a b hab
  refine (residueFieldLocEquiv q X).injective (hl ?_)
  rw [← residueFieldLocEquiv_map q φ a, ← residueFieldLocEquiv_map q φ b, hab]

end LocalizedFibre

/-! ## The fibrewise-injectivity engine -/

section FibrewiseInjective

variable {R : Type u} [CommRing R]
variable {P : Type v} {N : Type w} [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]

/-- The local heart: at a maximal ideal, a fibrewise-injective map from a finite module to
a finite flat module localizes to a **split** injection. -/
private lemma exists_comp_localizedMap_eq_id [Module.Finite R P] [Module.Finite R N]
    [Module.Flat R N] (ψ : P →ₗ[R] N) (J : Ideal R) [J.IsMaximal]
    (hfib : Function.Injective (ψ.rTensor J.ResidueField)) :
    ∃ l' : LocalizedModule J.primeCompl N →ₗ[Localization.AtPrime J]
        LocalizedModule J.primeCompl P,
      l' ∘ₗ LocalizedModule.map J.primeCompl ψ = LinearMap.id := by
  haveI : Module.Finite (Localization.AtPrime J) (LocalizedModule J.primeCompl P) :=
    Module.Finite.of_isLocalizedModule J.primeCompl (LocalizedModule.mkLinearMap J.primeCompl P)
  haveI : Module.Finite (Localization.AtPrime J) (LocalizedModule J.primeCompl N) :=
    Module.Finite.of_isLocalizedModule J.primeCompl (LocalizedModule.mkLinearMap J.primeCompl N)
  haveI : Module.Free (Localization.AtPrime J) (LocalizedModule J.primeCompl N) :=
    Module.free_of_flat_of_isLocalRing
  exact (IsLocalRing.split_injective_iff_lTensor_residueField_injective
    (LocalizedModule.map J.primeCompl ψ)).mpr
    (injective_lTensor_residueField_localizedMap J ψ hfib)

/-- **Fibrewise injective into finite flat ⟹ projective**: a finitely presented module
admitting a linear map to a finite flat module that is injective on every residue-field
fibre is projective (hence flat). Mathlib-general; no Noetherian hypothesis. -/
theorem Module.Projective.of_forall_rTensor_residueField_injective
    [Module.FinitePresentation R P] [Module.Finite R N] [Module.Flat R N] (ψ : P →ₗ[R] N)
    (hfib : ∀ p : PrimeSpectrum R,
      Function.Injective (ψ.rTensor p.asIdeal.ResidueField)) :
    Module.Projective R P := by
  refine Module.projective_of_localization_maximal (fun J hJ => ?_)
  haveI : Module.Projective (Localization.AtPrime J) (LocalizedModule J.primeCompl N) := by
    haveI : Module.Finite (Localization.AtPrime J) (LocalizedModule J.primeCompl N) :=
      Module.Finite.of_isLocalizedModule J.primeCompl
        (LocalizedModule.mkLinearMap J.primeCompl N)
    haveI : Module.Free (Localization.AtPrime J) (LocalizedModule J.primeCompl N) :=
      Module.free_of_flat_of_isLocalRing
    infer_instance
  obtain ⟨l', hl'⟩ := exists_comp_localizedMap_eq_id ψ J (hfib ⟨J, hJ.isPrime⟩)
  exact Module.Projective.of_split _ _ hl'

/-- **Fibrewise injective ⟹ injective** for a map from a finite module to a finite flat
module (injectivity is checked at maximal localizations, where the map splits). -/
theorem LinearMap.injective_of_forall_rTensor_residueField_injective
    [Module.Finite R P] [Module.Finite R N] [Module.Flat R N] (ψ : P →ₗ[R] N)
    (hfib : ∀ p : PrimeSpectrum R,
      Function.Injective (ψ.rTensor p.asIdeal.ResidueField)) :
    Function.Injective ψ := by
  apply injective_of_localized_maximal
  intro J hJ
  obtain ⟨l', hl'⟩ := exists_comp_localizedMap_eq_id ψ J (hfib ⟨J, hJ.isPrime⟩)
  exact Function.HasLeftInverse.injective ⟨l', LinearMap.congr_fun hl'⟩

/-- **Fibrewise injective ⟹ flat cokernel**: for `ψ : P → N` with `P` finite, `N` finite
flat and `ψ ⊗ κ(p)` injective at every prime, the cokernel `N ⧸ range ψ` is flat (locally
it is even free, by `Module.free_of_lTensor_residueField_injective`). -/
theorem Module.Flat.quotient_range_of_forall_rTensor_residueField_injective
    [Module.Finite R P] [Module.Finite R N] [Module.Flat R N] (ψ : P →ₗ[R] N)
    (hfib : ∀ p : PrimeSpectrum R,
      Function.Injective (ψ.rTensor p.asIdeal.ResidueField)) :
    Module.Flat R (N ⧸ LinearMap.range ψ) := by
  apply Module.flat_of_localized_maximal
  intro J hJ
  haveI : Module.Finite (Localization.AtPrime J) (LocalizedModule J.primeCompl P) :=
    Module.Finite.of_isLocalizedModule J.primeCompl (LocalizedModule.mkLinearMap J.primeCompl P)
  haveI : Module.Finite (Localization.AtPrime J) (LocalizedModule J.primeCompl N) :=
    Module.Finite.of_isLocalizedModule J.primeCompl (LocalizedModule.mkLinearMap J.primeCompl N)
  haveI : Module.Free (Localization.AtPrime J) (LocalizedModule J.primeCompl N) :=
    Module.free_of_flat_of_isLocalRing
  haveI : Module.Free (Localization.AtPrime J)
      (LocalizedModule J.primeCompl (N ⧸ LinearMap.range ψ)) :=
    Module.free_of_lTensor_residueField_injective
      (LocalizedModule.map J.primeCompl ψ)
      (LocalizedModule.map J.primeCompl (LinearMap.range ψ).mkQ)
      (LocalizedModule.map_surjective _ _ (Submodule.mkQ_surjective _))
      (LocalizedModule.map_exact _ _ _ ψ.exact_map_mkQ_range)
      (injective_lTensor_residueField_localizedMap J ψ (hfib ⟨J, hJ.isPrime⟩))
  exact Module.Flat.trans R (Localization.AtPrime J) _

end FibrewiseInjective

/-! ## The kernel-flattening keystones -/

section KernelFlattening

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [Module.Finite R M] [Module.Finite R N] [Module.Flat R N]
variable (f : M →ₗ[R] N) (L : Submodule R M)

omit [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N] [Module.Flat R N] in
/-- `f` kills `L` as a composite. -/
private lemma comp_subtype_eq_zero (hle : L ≤ LinearMap.ker f) : f ∘ₗ L.subtype = 0 :=
  LinearMap.ext fun x => LinearMap.mem_ker.mp (hle x.2)

omit [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N] [Module.Flat R N] in
/-- The fibrewise-spanning hypothesis says exactly that the induced map
`M ⧸ L → N` is injective on every residue-field fibre (right-exactness of `− ⊗ κ(p)`). -/
private lemma liftQ_rTensor_residueField_injective (hle : L ≤ LinearMap.ker f)
    (hspan : ∀ p : PrimeSpectrum R,
      LinearMap.ker (f.rTensor p.asIdeal.ResidueField) ≤
        LinearMap.range ((L.subtype).rTensor p.asIdeal.ResidueField))
    (p : PrimeSpectrum R) :
    Function.Injective ((L.liftQ f hle).rTensor p.asIdeal.ResidueField) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective p.asIdeal.ResidueField
    (Submodule.mkQ_surjective L) t
  have hy : y ∈ LinearMap.ker (f.rTensor p.asIdeal.ResidueField) := by
    rw [LinearMap.mem_ker, ← L.liftQ_mkQ f hle, LinearMap.rTensor_comp, LinearMap.comp_apply]
    exact ht
  obtain ⟨u, hu⟩ := hspan p hy
  exact (rTensor_exact p.asIdeal.ResidueField (LinearMap.exact_subtype_mkQ L)
    (Submodule.mkQ_surjective L) y).mpr ⟨u, hu⟩

/-- **The flattening keystone, quotient form**: over a Noetherian ring, if the residue
fibres of the kernel of `f : M → N` (`M` finite, `N` finite flat) are spanned by a
submodule `L ≤ ker f`, then `M ⧸ L` is finite projective (in particular flat). -/
theorem Module.Projective.quotient_of_forall_ker_rTensor_residueField_le
    (hle : L ≤ LinearMap.ker f)
    (hspan : ∀ p : PrimeSpectrum R,
      LinearMap.ker (f.rTensor p.asIdeal.ResidueField) ≤
        LinearMap.range ((L.subtype).rTensor p.asIdeal.ResidueField)) :
    Module.Projective R (M ⧸ L) := by
  haveI : Module.FinitePresentation R (M ⧸ L) := Module.finitePresentation_of_finite R _
  exact Module.Projective.of_forall_rTensor_residueField_injective (L.liftQ f hle)
    (liftQ_rTensor_residueField_injective f L hle hspan)

omit [IsNoetherianRing R] in
/-- **The kernel is no larger than its fibrewise-spanning submodule**: `L = ker f`. This is
the relative-elements completeness clause (conclusion (4) of the G-4 brick). -/
theorem Submodule.eq_ker_of_forall_ker_rTensor_residueField_le
    (hle : L ≤ LinearMap.ker f)
    (hspan : ∀ p : PrimeSpectrum R,
      LinearMap.ker (f.rTensor p.asIdeal.ResidueField) ≤
        LinearMap.range ((L.subtype).rTensor p.asIdeal.ResidueField)) :
    L = LinearMap.ker f := by
  refine le_antisymm hle fun x hx => ?_
  have hinj : Function.Injective (L.liftQ f hle) :=
    LinearMap.injective_of_forall_rTensor_residueField_injective (L.liftQ f hle)
      (liftQ_rTensor_residueField_injective f L hle hspan)
  have h0 : L.liftQ f hle (Submodule.Quotient.mk x) = 0 := by
    rw [Submodule.liftQ_apply]
    exact LinearMap.mem_ker.mp hx
  have hmk : (Submodule.Quotient.mk x : M ⧸ L) = 0 := hinj (by rw [h0, map_zero])
  rwa [Submodule.Quotient.mk_eq_zero] at hmk

/-- **Certificate clause (c3)**: `M ⧸ ker f` is flat (indeed projective, being `M ⧸ L`). -/
theorem Module.Flat.quotient_ker_of_forall_ker_rTensor_residueField_le
    (hle : L ≤ LinearMap.ker f)
    (hspan : ∀ p : PrimeSpectrum R,
      LinearMap.ker (f.rTensor p.asIdeal.ResidueField) ≤
        LinearMap.range ((L.subtype).rTensor p.asIdeal.ResidueField)) :
    Module.Flat R (M ⧸ LinearMap.ker f) := by
  haveI := Module.Projective.quotient_of_forall_ker_rTensor_residueField_le f L hle hspan
  rw [← Submodule.eq_ker_of_forall_ker_rTensor_residueField_le f L hle hspan]
  infer_instance

omit [IsNoetherianRing R] in
/-- **Certificate clause (c4)**: `N ⧸ range f` is flat. -/
theorem Module.Flat.quotient_range_of_forall_ker_rTensor_residueField_le
    (hle : L ≤ LinearMap.ker f)
    (hspan : ∀ p : PrimeSpectrum R,
      LinearMap.ker (f.rTensor p.asIdeal.ResidueField) ≤
        LinearMap.range ((L.subtype).rTensor p.asIdeal.ResidueField)) :
    Module.Flat R (N ⧸ LinearMap.range f) := by
  have hrange : LinearMap.range f = LinearMap.range (L.liftQ f hle) :=
    (Submodule.range_liftQ L f hle).symm
  rw [hrange]
  exact Module.Flat.quotient_range_of_forall_rTensor_residueField_injective (L.liftQ f hle)
    (liftQ_rTensor_residueField_injective f L hle hspan)

/-- The split retraction of `L ↪ M` (from projectivity of `M ⧸ L`). -/
private lemma exists_comp_subtype_eq_id [Module.Flat R M] (hle : L ≤ LinearMap.ker f)
    (hspan : ∀ p : PrimeSpectrum R,
      LinearMap.ker (f.rTensor p.asIdeal.ResidueField) ≤
        LinearMap.range ((L.subtype).rTensor p.asIdeal.ResidueField)) :
    ∃ r : M →ₗ[R] L, r ∘ₗ L.subtype = LinearMap.id := by
  haveI := Module.Projective.quotient_of_forall_ker_rTensor_residueField_le f L hle hspan
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property L.mkQ LinearMap.id
    (Submodule.mkQ_surjective L)
  have hmem : ∀ x : M, x - σ (L.mkQ x) ∈ L := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
    rw [show L.mkQ (σ (L.mkQ x)) = L.mkQ x from LinearMap.congr_fun hσ (L.mkQ x)]
    exact sub_self _
  refine ⟨(LinearMap.id - σ ∘ₗ L.mkQ).codRestrict L (fun x => by simpa using hmem x), ?_⟩
  ext x
  have hx0 : L.mkQ (x : M) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact x.2
  simp [hx0]

/-- The submodule `L` (equivalently `ker f`) is projective — with finiteness automatic over
the Noetherian base, this is the finite-projective half of certificate clause (c2). -/
theorem Module.Projective.ker_of_forall_ker_rTensor_residueField_le [Module.Flat R M]
    (hle : L ≤ LinearMap.ker f)
    (hspan : ∀ p : PrimeSpectrum R,
      LinearMap.ker (f.rTensor p.asIdeal.ResidueField) ≤
        LinearMap.range ((L.subtype).rTensor p.asIdeal.ResidueField)) :
    Module.Projective R (LinearMap.ker f) := by
  obtain ⟨r, hr⟩ := exists_comp_subtype_eq_id f L hle hspan
  haveI : Module.Projective R M := by
    haveI := Module.finitePresentation_of_finite R M
    exact Module.Flat.projective_of_finitePresentation
  have hL : Module.Projective R L := Module.Projective.of_split L.subtype r hr
  rw [← Submodule.eq_ker_of_forall_ker_rTensor_residueField_le f L hle hspan]
  exact hL

/-- **Base change of the kernel, injectivity half**: `L ⊗ κ(p) → M ⊗ κ(p)` is injective
(`L ↪ M` is split by `exists_comp_subtype_eq_id`, and split injections are universally
injective). -/
theorem LinearMap.rTensor_subtype_injective_of_forall_ker_rTensor_residueField_le
    [Module.Flat R M] (hle : L ≤ LinearMap.ker f)
    (hspan : ∀ p : PrimeSpectrum R,
      LinearMap.ker (f.rTensor p.asIdeal.ResidueField) ≤
        LinearMap.range ((L.subtype).rTensor p.asIdeal.ResidueField))
    (p : PrimeSpectrum R) :
    Function.Injective ((L.subtype).rTensor p.asIdeal.ResidueField) := by
  obtain ⟨r, hr⟩ := exists_comp_subtype_eq_id f L hle hspan
  have hcomp : (r.rTensor p.asIdeal.ResidueField) ∘ₗ
      ((L.subtype).rTensor p.asIdeal.ResidueField) = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, hr, LinearMap.rTensor_id]
  exact Function.HasLeftInverse.injective ⟨_, LinearMap.congr_fun hcomp⟩

omit [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N] [Module.Flat R N] in
/-- **Base change of the kernel, image half**: the image of `L ⊗ κ(p)` in `M ⊗ κ(p)` is
exactly `ker (f ⊗ κ(p))` (no flatness of `M` needed: `≤` is `L ≤ ker f`, `≥` is `hspan`).
With the injectivity half this identifies `L ⊗ κ(p) ≅ ker (f ⊗ κ(p))` — formation of
`ker f = L` commutes with residue fields. -/
theorem LinearMap.range_rTensor_subtype_eq_ker_of_forall_ker_rTensor_residueField_le
    (hle : L ≤ LinearMap.ker f)
    (hspan : ∀ p : PrimeSpectrum R,
      LinearMap.ker (f.rTensor p.asIdeal.ResidueField) ≤
        LinearMap.range ((L.subtype).rTensor p.asIdeal.ResidueField))
    (p : PrimeSpectrum R) :
    LinearMap.range ((L.subtype).rTensor p.asIdeal.ResidueField)
      = LinearMap.ker (f.rTensor p.asIdeal.ResidueField) := by
  refine le_antisymm ?_ (hspan p)
  rintro _ ⟨u, rfl⟩
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
    comp_subtype_eq_zero f L hle, LinearMap.rTensor_zero, LinearMap.zero_apply]

/-- **The rank dictionary**: the stalk rank of `ker f` at `p` is the `κ(p)`-dimension of
the fibre kernel `ker (f ⊗ κ(p))` (spelled with the `κ(p)`-linear `f.baseChange`). -/
theorem Module.rankAtStalk_ker_eq_finrank_ker_baseChange [Module.Flat R M]
    (hle : L ≤ LinearMap.ker f)
    (hspan : ∀ p : PrimeSpectrum R,
      LinearMap.ker (f.rTensor p.asIdeal.ResidueField) ≤
        LinearMap.range ((L.subtype).rTensor p.asIdeal.ResidueField))
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (LinearMap.ker f) p
      = Module.finrank p.asIdeal.ResidueField
          (LinearMap.ker (f.baseChange p.asIdeal.ResidueField)) := by
  haveI hLproj : Module.Projective R L := by
    obtain ⟨r, hr⟩ := exists_comp_subtype_eq_id f L hle hspan
    haveI : Module.Projective R M := by
      haveI := Module.finitePresentation_of_finite R M
      exact Module.Flat.projective_of_finitePresentation
    exact Module.Projective.of_split L.subtype r hr
  rw [← Submodule.eq_ker_of_forall_ker_rTensor_residueField_le f L hle hspan,
    Module.rankAtStalk_eq]
  -- the `κ(p)`-linear inclusion of the fibre of `L`
  refine LinearEquiv.finrank_eq
    (((LinearEquiv.ofInjective ((L.subtype).baseChange p.asIdeal.ResidueField) ?_).trans
      (LinearEquiv.ofEq _ _ ?_)))
  · -- injectivity: the `rTensor` statement, transported through `TensorProduct.comm`
    have hcoe : ⇑((L.subtype).baseChange p.asIdeal.ResidueField)
        = ⇑((L.subtype).lTensor p.asIdeal.ResidueField) := LinearMap.baseChange_eq_ltensor _
    rw [hcoe]
    exact (LinearMap.lTensor_inj_iff_rTensor_inj _ _).mpr
      (LinearMap.rTensor_subtype_injective_of_forall_ker_rTensor_residueField_le
        f L hle hspan p)
  · -- range identification: transport the `rTensor` identity through `TensorProduct.comm`
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
        comp_subtype_eq_zero f L hle]
      have : ((0 : L →ₗ[R] N).baseChange p.asIdeal.ResidueField) u = 0 := by
        have hcoe : ⇑((0 : L →ₗ[R] N).baseChange p.asIdeal.ResidueField)
            = ⇑((0 : L →ₗ[R] N).lTensor p.asIdeal.ResidueField) :=
          LinearMap.baseChange_eq_ltensor _
        rw [hcoe, LinearMap.lTensor_zero, LinearMap.zero_apply]
      exact this
    · intro y hy
      -- push into the `rTensor` picture through `TensorProduct.comm`
      have hy' : (TensorProduct.comm R p.asIdeal.ResidueField M) y
          ∈ LinearMap.ker (f.rTensor p.asIdeal.ResidueField) := by
        rw [LinearMap.mem_ker, LinearMap.rTensor_comm]
        have h0 : (f.lTensor p.asIdeal.ResidueField) y = 0 := by
          have hcoe : ⇑(f.baseChange p.asIdeal.ResidueField)
              = ⇑(f.lTensor p.asIdeal.ResidueField) := LinearMap.baseChange_eq_ltensor _
          rw [← hcoe]
          exact hy
        rw [h0, map_zero]
      rw [← LinearMap.range_rTensor_subtype_eq_ker_of_forall_ker_rTensor_residueField_le
        f L hle hspan p] at hy'
      obtain ⟨u, hu⟩ := hy'
      refine ⟨(TensorProduct.comm R L p.asIdeal.ResidueField) u, ?_⟩
      have h2 : ((L.subtype).lTensor p.asIdeal.ResidueField)
            ((TensorProduct.comm R L p.asIdeal.ResidueField) u)
          = (TensorProduct.comm R M p.asIdeal.ResidueField)
            (((L.subtype).rTensor p.asIdeal.ResidueField) u) :=
        LinearMap.lTensor_comm _ _
      rw [hu] at h2
      have hcoe : ⇑((L.subtype).baseChange p.asIdeal.ResidueField)
          = ⇑((L.subtype).lTensor p.asIdeal.ResidueField) :=
        LinearMap.baseChange_eq_ltensor _
      rw [hcoe, h2, ← TensorProduct.comm_symm, LinearEquiv.symm_apply_apply]

/-- **Certificate clause (c2), rank form**: if every fibre kernel is `g`-dimensional, then
`ker f` has constant `rankAtStalk` equal to `g`. -/
theorem Module.rankAtStalk_ker_eq_of_forall_finrank_eq [Module.Flat R M]
    (hle : L ≤ LinearMap.ker f)
    (hspan : ∀ p : PrimeSpectrum R,
      LinearMap.ker (f.rTensor p.asIdeal.ResidueField) ≤
        LinearMap.range ((L.subtype).rTensor p.asIdeal.ResidueField))
    (g : ℕ)
    (hdim : ∀ p : PrimeSpectrum R,
      Module.finrank p.asIdeal.ResidueField
        (LinearMap.ker (f.baseChange p.asIdeal.ResidueField)) = g)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (LinearMap.ker f) p = g := by
  rw [Module.rankAtStalk_ker_eq_finrank_ker_baseChange f L hle hspan p]
  exact hdim p

end KernelFlattening
