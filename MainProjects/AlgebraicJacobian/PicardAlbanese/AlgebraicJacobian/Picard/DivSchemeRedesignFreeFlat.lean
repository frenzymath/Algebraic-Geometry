/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# The free-codomain kernel-flattening brick (infinite-rank `N`)

**Pure commutative algebra** (mathlib-only imports; no project geometry).  A free-codomain
generalization of the `(c4)` flattening keystone of `Picard/SlicingFlatKernel.lean`.

The landed `SlicingFlatKernel` engine
(`Module.Flat.quotient_range_of_forall_rTensor_residueField_injective`) proves `N ⧸ range ψ`
flat for `ψ : M → N` with `M` finite and `N` **finite** flat and `ψ ⊗ κ(p)` injective at
every prime.  At the *chart* level the codomain is `N = Γ(V)`, which is `Module.Free R` but
of **infinite rank** (`flat_sections_relPinnedChart`), so the finite hypothesis fails.  The
finiteness of `N` enters mathlib's `Module.free_of_lTensor_residueField_injective` /
`IsLocalRing.split_injective_iff_lTensor_residueField_injective` only through
`Module.finitePresentation_of_free_of_surjective`, which needs a *finite* basis; for an
infinite-rank free codomain the cokernel is not finitely presented (nor finitely generated),
so those lemmas do not apply.

The mathematical content that survives is the **finite free summand**: a finitely generated
submodule of a free module (here `range ψ`, finitely generated because `M` is finite) is
contained in a **finite free direct summand** `F ≤ N` (`exists_finite_free_summand_of_fg`).
The map `ψ` then factors through `F`, the mathlib finite split criterion applies to
`M → F`, and `ψ` is a split injection into `N` — so `N ⧸ range ψ` is a retract of the flat
`N` (`Module.Flat.of_retract`).  Everything is checked at maximal localizations (where
`N` localizes to a free module by `Module.free_of_isLocalizedModule`), then globalized by
`Module.flat_of_localized_maximal`, exactly as the finite engine does.

## Main results

* `exists_finite_free_summand_of_fg` — a finitely generated submodule of a free module sits
  in a finite free direct summand (with an explicit retraction);
* `Module.Flat.of_lTensor_residueField_injective_of_free` — the local heart: over a local
  ring, a presentation `M → N → Q → 0` with `M` finite, `N` free (any rank) and `κ ⊗ (M→N)`
  injective has `Q` flat;
* `Module.Flat.quotient_range_of_forall_rTensor_residueField_injective_free` — the global
  keystone: `N ⧸ range ψ` is flat for `ψ : M → N` with `M` finite, `N` free (any rank) and
  `ψ ⊗ κ(p)` injective at every prime.
-/

set_option autoImplicit false

universe u v w

open scoped TensorProduct

/-! ## The finite free summand of a finitely generated submodule -/

section Summand

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M]

/-- **A finitely generated submodule of a free module sits in a finite free direct summand.**
For `L ≤ M` finitely generated with `M` free, there is a finite free submodule `F` with
`L ≤ F` and a retraction `pr : M → F` of the inclusion (`pr ∘ F.subtype = id`), witnessing
`F` as a direct summand.  Take `F` to be the span of the finitely many basis vectors that
carry the coordinates of a finite generating set of `L`; the retraction is the coordinate
projection. -/
theorem exists_finite_free_summand_of_fg {L : Submodule R M} (hL : L.FG) :
    ∃ (F : Submodule R M) (pr : M →ₗ[R] F),
      Module.Finite R F ∧ Module.Free R F ∧ L ≤ F ∧ pr ∘ₗ F.subtype = LinearMap.id := by
  classical
  obtain ⟨t, ht⟩ := hL
  let b := Module.Free.chooseBasis R M
  let s : Finset (Module.Free.ChooseBasisIndex R M) :=
    t.biUnion (fun x => (b.repr x).support)
  let v : (↑s : Set (Module.Free.ChooseBasisIndex R M)) → M := fun i => b i
  have hli : LinearIndependent R v := b.linearIndependent.comp _ Subtype.val_injective
  have hrange : Set.range v = ⇑b '' (↑s : Set (Module.Free.ChooseBasisIndex R M)) := by
    have hv : v = ⇑b ∘ ((↑·) : (↑s : Set (Module.Free.ChooseBasisIndex R M)) → _) := rfl
    rw [hv, Set.range_comp, Subtype.range_coe_subtype, Set.setOf_mem_eq]
  let F : Submodule R M := Submodule.span R (Set.range v)
  let bF : Module.Basis (↑s : Set (Module.Free.ChooseBasisIndex R M)) R F :=
    Module.Basis.span hli
  let g : Module.Free.ChooseBasisIndex R M → F :=
    fun j => if h : j ∈ s then bF ⟨j, h⟩ else 0
  refine ⟨F, b.constr R g, ?_, ?_, ?_, ?_⟩
  · rw [Module.Finite.iff_fg]
    exact Submodule.fg_span (Set.finite_range v)
  · exact Module.Free.of_basis bF
  · rw [← ht, Submodule.span_le]
    intro x hx
    change x ∈ Submodule.span R (Set.range v)
    rw [hrange, b.mem_span_image]
    intro i hi
    simp only [Finset.mem_coe] at hi ⊢
    exact Finset.mem_biUnion.mpr ⟨x, hx, hi⟩
  · apply bF.ext
    intro i
    have hcoe : F.subtype (bF i) = b i.1 := by
      rw [Submodule.subtype_apply]
      exact Module.Basis.coe_span_apply hli i
    simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq]
    rw [hcoe, Module.Basis.constr_basis]
    change (if h : (i.1 ∈ s) then bF ⟨i.1, h⟩ else 0) = bF i
    rw [dif_pos (Finset.mem_coe.mp i.2)]

end Summand

/-! ## Residue fibres of localized modules (re-derivation of the local-splitting core) -/

section LocalizedFibre

variable {R : Type u} [CommRing R]

/-- The residue fibre of the localized module at `q` is the residue fibre of the module:
`κ(q) ⊗[R_q] X_q ≃ κ(q) ⊗[R] X`.  (Re-derivation of the private helper of
`Picard/SlicingFlatKernel.lean`, needed here for a free — possibly infinite — codomain.) -/
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

/-! ## The local heart: free (possibly infinite-rank) codomain -/

section LocalHeart

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **Split injection into a free module from the residue-fibre injectivity** (free codomain,
any rank).  Over a local ring, a map `ψ : M → N` with `M` finite, `N` free and `κ ⊗ ψ`
injective is a split injection.  Route: `range ψ` is finitely generated, hence contained in a
finite free direct summand `F` (`exists_finite_free_summand_of_fg`); `ψ` factors through `F`;
the mathlib finite split criterion applies to `M → F`; compose the retractions. -/
private lemma exists_comp_eq_id_of_lTensor_residueField_injective
    [Module.Finite R M] [Module.Free R N] (ψ : M →ₗ[R] N)
    (hf : Function.Injective (ψ.lTensor (IsLocalRing.ResidueField R))) :
    ∃ r : N →ₗ[R] M, r ∘ₗ ψ = LinearMap.id := by
  have hfg : (LinearMap.range ψ).FG := by
    rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map ψ
  obtain ⟨F, pr, hFfin, hFfree, hle, hpr⟩ := exists_finite_free_summand_of_fg hfg
  -- `ψ` corestricts to `F`
  have hmem : ∀ m, ψ m ∈ F := fun m => hle (LinearMap.mem_range_self ψ m)
  set ψ₀ : M →ₗ[R] F := LinearMap.codRestrict F ψ hmem with hψ₀def
  have hfac : F.subtype ∘ₗ ψ₀ = ψ := by
    ext m
    simp only [hψ₀def, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.codRestrict_apply]
  -- `κ ⊗ ψ₀` is injective (the split `F.subtype` is universally injective after `⊗ κ`)
  have hf₀ : Function.Injective (ψ₀.lTensor (IsLocalRing.ResidueField R)) := by
    have hcomp : (F.subtype.lTensor (IsLocalRing.ResidueField R)) ∘ₗ
        (ψ₀.lTensor (IsLocalRing.ResidueField R))
          = ψ.lTensor (IsLocalRing.ResidueField R) := by
      rw [← LinearMap.lTensor_comp, hfac]
    have h2 := hf
    rw [← hcomp, LinearMap.coe_comp] at h2
    exact h2.of_comp
  -- the mathlib finite split criterion on `M → F`
  obtain ⟨r₀, hr₀⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective ψ₀).mpr hf₀
  refine ⟨r₀ ∘ₗ pr, ?_⟩
  ext m
  have e1 : pr (F.subtype (ψ₀ m)) = ψ₀ m := by
    have := LinearMap.congr_fun hpr (ψ₀ m); simpa using this
  have e2 : F.subtype (ψ₀ m) = ψ m := by
    have := LinearMap.congr_fun hfac m; simpa using this
  have e3 : r₀ (ψ₀ m) = m := by
    have := LinearMap.congr_fun hr₀ m; simpa using this
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [← e2, e1]; exact e3

/-- **The local free-codomain flattening heart** (mirrors
`Module.free_of_lTensor_residueField_injective` but with `Flat` conclusion and a free — not
necessarily finite — codomain).  Over a local ring, if `M → N → Q → 0` is a presentation of
`Q` with `M` finite, `N` free (any rank) and `κ ⊗ (M → N)` injective, then `Q` is flat. -/
theorem Module.Flat.of_lTensor_residueField_injective_of_free
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    [Module.Finite R M] [Module.Free R N] (f : M →ₗ[R] N) (g : N →ₗ[R] Q)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hf : Function.Injective (f.lTensor (IsLocalRing.ResidueField R))) :
    Module.Flat R Q := by
  -- `f` is a split injection into the flat (free) `N`
  obtain ⟨r, hr⟩ := exists_comp_eq_id_of_lTensor_residueField_injective f hf
  have hrf : ∀ x, r (f x) = x := fun x => by
    have := LinearMap.congr_fun hr x; simpa using this
  -- hence `N ⧸ range f` is a retract of `N`
  have hker : LinearMap.range f ≤ LinearMap.ker (LinearMap.id - f ∘ₗ r) := by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      hrf, sub_self]
  set sec : (N ⧸ LinearMap.range f) →ₗ[R] N :=
    (LinearMap.range f).liftQ (LinearMap.id - f ∘ₗ r) hker with hsecdef
  have hretract : (LinearMap.range f).mkQ ∘ₗ sec = LinearMap.id := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨n, rfl⟩ := (LinearMap.range f).mkQ_surjective q
    have hsec : sec ((LinearMap.range f).mkQ n) = n - f (r n) := by
      rw [hsecdef, Submodule.mkQ_apply, Submodule.liftQ_apply]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    have hz : (LinearMap.range f).mkQ (f (r n)) = 0 := by
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self f (r n))
    rw [LinearMap.comp_apply, LinearMap.id_apply, hsec, map_sub, hz, sub_zero]
  haveI : Module.Flat R (N ⧸ LinearMap.range f) :=
    Module.Flat.of_retract sec (LinearMap.range f).mkQ hretract
  -- transport across `Q ≃ N ⧸ range f`
  have hkereq : LinearMap.ker g = LinearMap.range f := hfg.linearMap_ker_eq
  exact Module.Flat.of_linearEquiv
    ((LinearMap.quotKerEquivOfSurjective g hg).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hkereq)

end LocalHeart

/-! ## The global free-codomain (c4) keystone -/

section Global

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **The free-codomain (c4) flattening keystone**: for `ψ : M → N` with `M` finite, `N`
free (any rank — infinite rank permitted) and `ψ ⊗ κ(p)` injective at every prime `p`, the
cokernel `N ⧸ range ψ` is flat.  This drops the `[Module.Finite R N]` hypothesis of
`Module.Flat.quotient_range_of_forall_rTensor_residueField_injective` (Picard/SlicingFlatKernel),
keeping only `[Module.Free R N]`, so it applies at the infinite-rank chart codomain `Γ(V)`.
Route: at each maximal ideal `N` localizes to a free module (`Module.free_of_isLocalizedModule`)
and the local heart `Module.Flat.of_lTensor_residueField_injective_of_free` gives flatness of
the localized cokernel; `Module.flat_of_localized_maximal` globalizes. -/
theorem Module.Flat.quotient_range_of_forall_rTensor_residueField_injective_free
    [Module.Finite R M] [Module.Free R N] (ψ : M →ₗ[R] N)
    (hfib : ∀ p : PrimeSpectrum R,
      Function.Injective (ψ.rTensor p.asIdeal.ResidueField)) :
    Module.Flat R (N ⧸ LinearMap.range ψ) := by
  apply Module.flat_of_localized_maximal
  intro J hJ
  haveI : Module.Finite (Localization.AtPrime J) (LocalizedModule J.primeCompl M) :=
    Module.Finite.of_isLocalizedModule J.primeCompl (LocalizedModule.mkLinearMap J.primeCompl M)
  haveI : Module.Free (Localization.AtPrime J) (LocalizedModule J.primeCompl N) :=
    Module.free_of_isLocalizedModule J.primeCompl (LocalizedModule.mkLinearMap J.primeCompl N)
  haveI : Module.Flat (Localization.AtPrime J)
      (LocalizedModule J.primeCompl (N ⧸ LinearMap.range ψ)) :=
    Module.Flat.of_lTensor_residueField_injective_of_free
      (LocalizedModule.map J.primeCompl ψ)
      (LocalizedModule.map J.primeCompl (LinearMap.range ψ).mkQ)
      (LocalizedModule.map_surjective _ _ (Submodule.mkQ_surjective _))
      (LocalizedModule.map_exact _ _ _ ψ.exact_map_mkQ_range)
      (injective_lTensor_residueField_localizedMap J ψ (hfib ⟨J, hJ.isPrime⟩))
  exact Module.Flat.trans R (Localization.AtPrime J) _

end Global
