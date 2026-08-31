/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.FibrewiseRegular
import AlgebraicJacobian.Picard.FlatCokernel
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# The slicing criterion, flat-quotient form (Kleiman `lm:ctn` (iii)⟹(i), the Tor half)

**The third Tor-lemma home** of the DAT-D campaign, completing the pair
`Picard/FibrewiseRegular` (fibrewise-regular + flat ⟹ regular) and
`Picard/FlatCokernel` (regular + flat quotient ⟹ regular after any base change):

> over a Noetherian ring `R`, if `B` is a flat `R`-algebra and `f ∈ B` is a
> nonzerodivisor in every residue-field fibre `B ⊗[R] κ(p)`, then the quotient
> `B ⧸ (f)` is **flat** over `R`.

This is the missing flat-QUOTIENT conclusion of Kleiman's `lm:ctn`
(`references/kleiman-picard-src/kleiman-picard.tex` 1786–1815): the paper's
`Tor₁(B/(f), κ) = 0` computation is replaced by the ideal criterion of flatness plus the
Noetherian ideal-division engine already underlying `FibrewiseRegular`. Concretely, for
`Q = coker φ` of an endomorphism `φ` of a flat module `M`, injectivity of the canonical
map `I ⊗ Q → Q` is chased through the right-exact ladder `I ⊗ M → I ⊗ Q` using only

* injectivity of `I ⊗ M → M` (flatness of `M`, `iff_lift_lsmul_comp_subtype_injective`),
* the **ideal-division property** `φ x ∈ I·M ⟹ x ∈ I·M` — which over a Noetherian `R` is
  produced from fibrewise injectivity by the same Noetherian induction (prime fibres +
  flat colon lemma) as `Module.Flat.injective_of_forall_rTensor_residueField_injective`,
  here exposed as the public `Module.Flat.mem_smul_top_of_apply_mem_smul_top`.

No `Tor`, no local criterion of flatness, no finiteness hypothesis on `B`.

## Main declarations

* `Module.Flat.mem_smul_top_of_apply_mem_smul_top` — the ideal-division engine
  (fibrewise-injective endomorphism of a flat module divides ideal memberships);
* `Module.Flat.of_surjective_exact_of_forall_mem_smul_top` — flatness of a cokernel from
  the ideal-division property (no Noetherian hypothesis);
* `Module.Flat.of_surjective_exact_of_forall_rTensor_residueField_injective` — the
  module-form keystone;
* `Module.Flat.quotient_span_singleton_of_forall_tmul_residueField` — **the slicing
  criterion, ring form**: fibrewise-regular + flat `B` over Noetherian `R` ⟹
  `Module.Flat R (B ⧸ Ideal.span {f})` — the DDR-4 certificate clause (c1) flatness
  input on each chart-local colength `Γ(D(h_j)) ⧸ (f_j)`;
* `Module.Projective.quotient_span_singleton_of_forall_tmul_residueField` — the (c1)
  glue: with `Module.Finite` of the colength (the support-tube input), the colength is
  finite **projective**;
* `Algebra.TensorProduct.includeRight_mem_nonZeroDivisors_of_forall_tmul_residueField` —
  the composite with `FlatCokernel`: a fibrewise-regular element of a flat algebra over
  a Noetherian ring stays regular in `R' ⊗[R] B` for EVERY `R`-algebra `R'` (the
  relative-divisibility engine of the seed `dvd` brick, Kleiman (ii)⟹(iii)'s Tor input).
-/

set_option autoImplicit false

universe u v w

open scoped TensorProduct

/-! ## The ideal-division engine (the public `key` of the Noetherian induction) -/

section IdealDivision

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- **The ideal-division engine** (Kleiman `lm:ctn` (iii)⟹(i), the quantified form):
over a Noetherian ring, an endomorphism `φ` of a flat module that is injective on every
residue-field fibre divides ideal memberships — `φ x ∈ I·M ⟹ x ∈ I·M` for every ideal
`I`. This is the inner induction of
`Module.Flat.injective_of_forall_rTensor_residueField_injective` (`FibrewiseRegular`),
exposed because the flat-quotient conclusion (`of_surjective_exact_of_forall_mem_smul_top`)
consumes the full ideal-quantified statement, not just injectivity (`I = ⊥`).
Noetherian induction on ideals: the fibre hypothesis fires at the primes, the flat colon
lemma `Module.Flat.mem_colon_smul_top_of_smul_mem_smul_top` splices the non-primes. -/
theorem Module.Flat.mem_smul_top_of_apply_mem_smul_top
    [IsNoetherianRing R] [Module.Flat R M] (φ : M →ₗ[R] M)
    (hfib : ∀ p : PrimeSpectrum R,
      Function.Injective (φ.rTensor p.asIdeal.ResidueField))
    (I₀ : Ideal R) {x₀ : M} (hx₀ : φ x₀ ∈ I₀ • (⊤ : Submodule R M)) :
    x₀ ∈ I₀ • (⊤ : Submodule R M) := by
  refine IsNoetherian.induction
    (P := fun I : Ideal R => ∀ x : M,
      φ x ∈ I • (⊤ : Submodule R M) → x ∈ I • (⊤ : Submodule R M))
    (fun I IH => ?_) I₀ x₀ hx₀
  intro x hx
  by_cases htop : I = ⊤
  · rw [htop, Submodule.top_smul]
    exact Submodule.mem_top
  by_cases hp : Ideal.IsPrime I
  · -- the prime case: the fibre hypothesis, no inductive hypothesis
    haveI := hp
    have h1 : (φ.rTensor (Ideal.ResidueField I))
        (x ⊗ₜ[R] (1 : Ideal.ResidueField I)) = 0 := by
      rw [LinearMap.rTensor_tmul]
      exact tmul_residueField_one_eq_zero_of_mem_smul_top I hx
    have h2 : (x ⊗ₜ[R] (1 : Ideal.ResidueField I) :
        M ⊗[R] Ideal.ResidueField I) = 0 :=
      hfib ⟨I, hp⟩ (by rw [h1, map_zero] :
        (φ.rTensor (Ideal.ResidueField I)) (x ⊗ₜ[R] (1 : Ideal.ResidueField I)) =
          (φ.rTensor (Ideal.ResidueField I)) 0)
    exact Module.Flat.mem_smul_top_of_tmul_residueField_one_eq_zero I h2
  · -- the non-prime case: splice two strictly larger ideals
    obtain ⟨a, b, hab, ha, hb⟩ : ∃ a b : R, a * b ∈ I ∧ a ∉ I ∧ b ∉ I := by
      by_contra hcon
      refine hp ⟨htop, fun {u v} huv => ?_⟩
      by_cases hu : u ∈ I
      · exact Or.inl hu
      by_cases hv : v ∈ I
      · exact Or.inr hv
      exact absurd ⟨u, v, huv, hu, hv⟩ hcon
    -- `J₁ = I ⊔ (a) > I`
    have hJ₁gt : I < I ⊔ Ideal.span {a} :=
      lt_of_le_of_ne le_sup_left (fun h => ha (by
        rw [h]
        exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)))
    -- `J₂ = (I : a) > I`
    have hJ₂le : I ≤ Submodule.colon I {a} := fun r hr =>
      Submodule.mem_colon_singleton.mpr
        (by rw [smul_eq_mul]; exact Ideal.mul_mem_right a I hr)
    have hJ₂gt : I < Submodule.colon I {a} :=
      lt_of_le_of_ne hJ₂le (fun h => hb (by
        rw [h]
        exact Submodule.mem_colon_singleton.mpr
          (by rw [smul_eq_mul, mul_comm]; exact hab)))
    -- split `x = y + a•z` with `y ∈ I•⊤` through `P (I ⊔ (a))`
    have hx₁ : x ∈ (I ⊔ Ideal.span {a}) • (⊤ : Submodule R M) :=
      IH _ hJ₁gt x (Submodule.smul_mono_left le_sup_left hx)
    rw [Submodule.sup_smul, Submodule.ideal_span_singleton_smul] at hx₁
    obtain ⟨y, hy, z', hz', rfl⟩ := Submodule.mem_sup.mp hx₁
    obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists z' a
      (⊤ : Submodule R M)).mp hz'
    -- `φ y ∈ I•⊤`, hence `a • φ z ∈ I•⊤`
    have hφy : φ y ∈ I • (⊤ : Submodule R M) := by
      have hmap := Submodule.map_smul'' I (⊤ : Submodule R M) φ
      have : φ y ∈ Submodule.map φ (I • (⊤ : Submodule R M)) :=
        Submodule.mem_map_of_mem hy
      rw [hmap] at this
      exact smul_mono_right I
        (le_top : Submodule.map φ (⊤ : Submodule R M) ≤ ⊤) this
    have haz : a • φ z ∈ I • (⊤ : Submodule R M) := by
      have hsum : φ y + a • φ z ∈ I • (⊤ : Submodule R M) := by
        have : φ (y + a • z) = φ y + a • φ z := by rw [map_add, map_smul]
        rwa [this] at hx
      simpa using Submodule.sub_mem _ hsum hφy
    -- the flat colon lemma + `P ((I : a))`
    have hz₂ : z ∈ Submodule.colon I {a} • (⊤ : Submodule R M) :=
      IH _ hJ₂gt z
        (Module.Flat.mem_colon_smul_top_of_smul_mem_smul_top I a haz)
    -- `a • ((I : a)•⊤) ≤ I•⊤`
    have haz₂ : a • z ∈ I • (⊤ : Submodule R M) := by
      have hsub : ∀ w ∈ Submodule.colon I {a} • (⊤ : Submodule R M),
          a • w ∈ I • (⊤ : Submodule R M) := by
        intro w hw
        refine Submodule.smul_induction_on hw (fun r hr m _ => ?_)
          (fun u v hu hv => ?_)
        · have hra : r * a ∈ I := by
            have := Submodule.mem_colon_singleton.mp hr
            rwa [smul_eq_mul] at this
          rw [smul_smul, mul_comm a r]
          exact Submodule.smul_mem_smul hra Submodule.mem_top
        · rw [smul_add]
          exact Submodule.add_mem _ hu hv
      exact hsub z hz₂
    exact Submodule.add_mem _ hy haz₂

end IdealDivision

/-! ## Flatness of a cokernel from the ideal-division property -/

section FlatOfExact

variable {R : Type u} [CommRing R] {M : Type v} {Q : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]

/-- Naturality of the canonical map `I ⊗ M → M`, `a ⊗ m ↦ a • m`, against an `R`-linear
map applied on the right tensor factor. -/
private lemma lift_lsmul_lTensor_apply {I : Ideal R} (f : M →ₗ[R] Q) (t : I ⊗[R] M) :
    TensorProduct.lift ((LinearMap.lsmul R Q).comp I.subtype) (f.lTensor I t)
      = f (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype) t) := by
  induction t with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a m =>
      rw [LinearMap.lTensor_tmul, TensorProduct.lift.tmul, TensorProduct.lift.tmul]
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
        LinearMap.lsmul_apply]
      rw [map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The canonical map `I ⊗ M → M` lands in `I • ⊤`. -/
private lemma lift_lsmul_mem_smul_top {I : Ideal R} (t : I ⊗[R] M) :
    TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype) t
      ∈ I • (⊤ : Submodule R M) := by
  induction t with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul a m =>
      rw [TensorProduct.lift.tmul]
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
        LinearMap.lsmul_apply]
      exact Submodule.smul_mem_smul a.2 Submodule.mem_top
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- Elements of `I • ⊤` lift through the canonical map `I ⊗ M → M`. -/
private lemma exists_lift_lsmul_of_mem_smul_top {I : Ideal R} {z : M}
    (hz : z ∈ I • (⊤ : Submodule R M)) :
    ∃ t : I ⊗[R] M, TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype) t = z := by
  refine Submodule.smul_induction_on hz (fun a ha m _ => ⟨⟨a, ha⟩ ⊗ₜ[R] m, ?_⟩)
    (fun u v hu hv => ?_)
  · rw [TensorProduct.lift.tmul]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      LinearMap.lsmul_apply]
  · obtain ⟨t, ht⟩ := hu
    obtain ⟨t', ht'⟩ := hv
    exact ⟨t + t', by rw [map_add, ht, ht']⟩

/-- **Flatness of a cokernel from the ideal-division property** (no Noetherian
hypothesis): if `M` is flat, `π : M → Q` is a surjection with `ker π = range φ` for an
endomorphism `φ` of `M`, and `φ` divides membership in `I·M` for every finitely
generated ideal `I` (`φ x ∈ I·M ⟹ x ∈ I·M`), then `Q` is flat.

The ideal criterion (`iff_lift_lsmul_comp_subtype_injective`) reduces flatness of `Q`
to injectivity of `I ⊗ Q → Q`; a kernel element lifts along the right-exact
`I ⊗ M → I ⊗ Q`, its image in `M` lands in `I·M ∩ ker π = φ(I·M)` by ideal division,
and injectivity of `I ⊗ M → M` (flatness of `M`) pushes the factorization back up to
`I ⊗ M`, where `π ∘ φ = 0` kills it. This is the connecting-map chase of Kleiman's
`Tor₁` argument, done by hand. -/
theorem Module.Flat.of_surjective_exact_of_forall_mem_smul_top [Module.Flat R M]
    (φ : M →ₗ[R] M) (π : M →ₗ[R] Q) (hsurj : Function.Surjective π)
    (hexact : Function.Exact φ π)
    (hdvd : ∀ (I : Ideal R), I.FG → ∀ x : M,
      φ x ∈ I • (⊤ : Submodule R M) → x ∈ I • (⊤ : Submodule R M)) :
    Module.Flat R Q := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I hI
  rw [injective_iff_map_eq_zero]
  intro ξ hξ
  -- lift `ξ` along the surjection `I ⊗ M → I ⊗ Q`
  obtain ⟨η, rfl⟩ := LinearMap.lTensor_surjective I hsurj ξ
  -- its image `m := μ η ∈ M` dies in `Q`, so `m = φ z`
  have hπ : π (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype) η) = 0 := by
    rw [← lift_lsmul_lTensor_apply π η]
    exact hξ
  obtain ⟨z, hz⟩ := (hexact _).mp hπ
  -- `φ z = m ∈ I·M`, so `z ∈ I·M` by ideal division; lift `z` back to `I ⊗ M`
  have hzmem : z ∈ I • (⊤ : Submodule R M) :=
    hdvd I hI z (by rw [hz]; exact lift_lsmul_mem_smul_top η)
  obtain ⟨η', hη'⟩ := exists_lift_lsmul_of_mem_smul_top hzmem
  -- flatness of `M`: `I ⊗ M → M` is injective, so `η = φ_I η'`
  have hinj : Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)) :=
    Module.Flat.iff_lift_lsmul_comp_subtype_injective.mp inferInstance hI
  have hη : φ.lTensor I η' = η := by
    refine hinj ?_
    rw [lift_lsmul_lTensor_apply φ η', hη', hz]
  -- `π_I ∘ φ_I = (π ∘ φ)_I = 0`
  have hcomp : π.comp φ = 0 := LinearMap.ext fun m => (hexact (φ m)).mpr ⟨m, rfl⟩
  calc π.lTensor I η = π.lTensor I (φ.lTensor I η') := by rw [hη]
    _ = (π.comp φ).lTensor I η' := by rw [LinearMap.lTensor_comp, LinearMap.comp_apply]
    _ = 0 := by rw [hcomp, LinearMap.lTensor_zero, LinearMap.zero_apply]

/-- **The slicing criterion, module form** (Kleiman `lm:ctn` (iii)⟹(i), flat-quotient
conclusion): over a Noetherian ring `R`, if `φ` is an endomorphism of a flat module `M`
that is injective on every residue-field fibre, then any quotient of `M` by the image of
`φ` (presented as a surjection `π` exact against `φ`) is flat. -/
theorem Module.Flat.of_surjective_exact_of_forall_rTensor_residueField_injective
    [IsNoetherianRing R] [Module.Flat R M] (φ : M →ₗ[R] M) (π : M →ₗ[R] Q)
    (hsurj : Function.Surjective π) (hexact : Function.Exact φ π)
    (hfib : ∀ p : PrimeSpectrum R,
      Function.Injective (φ.rTensor p.asIdeal.ResidueField)) :
    Module.Flat R Q :=
  Module.Flat.of_surjective_exact_of_forall_mem_smul_top φ π hsurj hexact
    (fun I _ _ hx => Module.Flat.mem_smul_top_of_apply_mem_smul_top φ hfib I hx)

end FlatOfExact

/-! ## The ring form: flatness and projectivity of the principal colength -/

section RingForm

variable {R : Type u} [CommRing R] {B : Type u} [CommRing B] [Algebra R B]

/-- Multiplication by `f` and the quotient projection `B → B ⧸ (f)` form an exact
pair (no regularity of `f` needed). -/
private lemma exact_mulLeft_mkQuotient (f : B) :
    Function.Exact (LinearMap.mulLeft R f)
      (Ideal.Quotient.mkₐ R (Ideal.span {f})).toLinearMap := by
  intro y
  constructor
  · intro hy
    have hmem : y ∈ Ideal.span {f} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨c, by rw [LinearMap.mulLeft_apply, mul_comm, hc]⟩
  · rintro ⟨c, rfl⟩
    have hmem : f * c ∈ Ideal.span {f} :=
      Ideal.mem_span_singleton'.mpr ⟨c, mul_comm c f⟩
    simp only [AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
      Ideal.Quotient.mkₐ_eq_mk]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hmem

/-- **The slicing criterion, ring form** (fibrewise-regular + flat base ⟹ flat
quotient; Kleiman `lm:ctn` (iii)⟹(i), the Tor half; DDR-4 (c1) flatness): over a
Noetherian ring `R`, if `B` is a flat `R`-algebra and the image of `f : B` in every
residue-field fibre `B ⊗[R] κ(p)` is a nonzerodivisor, then the colength `B ⧸ (f)` is
flat over `R`.

Instantiated by DDR-4 at `B = Γ(D(h_j))`, `f =` the adaptation equation `f_j` (the
fibrewise hypothesis is the seed's `fibre_regular` clause transported through
`eqn_rel`); combined with `Module.Finite` (the support tube) it yields the certificate
clause (c1) via `Module.Projective.quotient_span_singleton_of_forall_tmul_residueField`.
Note the `k[ε]` trap: fibrewise regularity of `f` alone (without flatness of `B`) does
NOT suffice, and the conclusion genuinely fails for non-flat `B`. -/
theorem Module.Flat.quotient_span_singleton_of_forall_tmul_residueField
    [IsNoetherianRing R] [Module.Flat R B] {f : B}
    (hfib : ∀ p : PrimeSpectrum R,
      (f ⊗ₜ[R] (1 : p.asIdeal.ResidueField) : B ⊗[R] p.asIdeal.ResidueField) ∈
        nonZeroDivisors (B ⊗[R] p.asIdeal.ResidueField)) :
    Module.Flat R (B ⧸ Ideal.span {f}) := by
  refine Module.Flat.of_surjective_exact_of_forall_rTensor_residueField_injective
    (LinearMap.mulLeft R f) (Ideal.Quotient.mkₐ R (Ideal.span {f})).toLinearMap
    (fun y => ?_) (exact_mulLeft_mkQuotient f) (fun p => ?_)
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨x, hx⟩
  · rw [rTensor_mulLeft_eq_mulLeft_tmul p.asIdeal.ResidueField f]
    intro u v huv
    have hzero : (u - v) * (f ⊗ₜ[R] (1 : p.asIdeal.ResidueField)) = 0 := by
      rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply] at huv
      rw [sub_mul, mul_comm u, mul_comm v, huv, sub_self]
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp (hfib p)).2 (u - v) hzero)

/-- **The certificate-(c1) glue**: fibrewise-regular + flat base + finite colength ⟹
finite **projective** colength. Over the Noetherian `R` the flat colength
(`Module.Flat.quotient_span_singleton_of_forall_tmul_residueField`) is finitely
presented as soon as it is finite (the support-tube input), hence projective. -/
theorem Module.Projective.quotient_span_singleton_of_forall_tmul_residueField
    [IsNoetherianRing R] [Module.Flat R B] {f : B}
    (hfib : ∀ p : PrimeSpectrum R,
      (f ⊗ₜ[R] (1 : p.asIdeal.ResidueField) : B ⊗[R] p.asIdeal.ResidueField) ∈
        nonZeroDivisors (B ⊗[R] p.asIdeal.ResidueField))
    [Module.Finite R (B ⧸ Ideal.span {f})] :
    Module.Projective R (B ⧸ Ideal.span {f}) := by
  haveI := Module.Flat.quotient_span_singleton_of_forall_tmul_residueField hfib
  haveI := Module.finitePresentation_of_finite R (B ⧸ Ideal.span {f})
  exact Module.Flat.projective_of_finitePresentation

/-- **Relative regularity from fibrewise regularity** (Kleiman `lm:ctn` (iii)⟹(i)
composed with (i)⟹ base-change stability; the seed-`dvd` brick's Tor engine): over a
Noetherian ring `R`, a fibrewise-regular element `f` of a flat `R`-algebra `B` stays a
nonzerodivisor in `R' ⊗[R] B` for EVERY `R`-algebra `R'` — no flatness or Noetherian
hypothesis on `R'`. Chains the slicing criterion into
`Algebra.TensorProduct.includeRight_mem_nonZeroDivisors_of_flat_coker`. -/
theorem Algebra.TensorProduct.includeRight_mem_nonZeroDivisors_of_forall_tmul_residueField
    [IsNoetherianRing R] [Module.Flat R B] {f : B}
    (hfib : ∀ p : PrimeSpectrum R,
      (f ⊗ₜ[R] (1 : p.asIdeal.ResidueField) : B ⊗[R] p.asIdeal.ResidueField) ∈
        nonZeroDivisors (B ⊗[R] p.asIdeal.ResidueField))
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := B)) f
      ∈ nonZeroDivisors (R' ⊗[R] B) := by
  haveI := Module.Flat.quotient_span_singleton_of_forall_tmul_residueField hfib
  exact Algebra.TensorProduct.includeRight_mem_nonZeroDivisors_of_flat_coker R' f
    (Module.Flat.mem_nonZeroDivisors_of_forall_tmul_residueField hfib)

end RingForm
