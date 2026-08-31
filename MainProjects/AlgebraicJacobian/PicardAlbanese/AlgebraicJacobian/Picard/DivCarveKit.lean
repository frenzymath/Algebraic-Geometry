/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.Grassmannian
import AlgebraicJacobian.Picard.EntriesIdeal

/-!
# DD-R kit: the carve-pair arrow and its base-change transport (DDR-1 support)

The module-algebra substrate of the DD-R carve locus (`informal/spec-dd-r.md` §3 item 1);
the Grassmannian-pair chart layer is `Picard/DivCarvePairChart.lean`.

* **The projective-quotient retraction** (`quotRetract`,
  `finite_submodule_of_projective_quotient`, `ker_baseChange_mkQ`): a submodule with
  projective quotient is a retract of the ambient module, so its short exact sequence
  splits and stays exact under every base change — `ker (mkQ ⊗ S) = Km.baseChange S`.
* **The generic carve-pair arrow** `carvePairArrow μ Km K' = mkQ ∘ (μ ⊗ R) ∘ incl` — the
  shape of the `(♦)` condition at one multiplier `μ`; `carveArrow` (SectionMul) is the
  instance `μ := sectionMulBilin K A B a`.
* **The carve transport (L1)**: `baseChange_carvePairArrow_eq_zero_iff` — the base change
  of the carve arrow along `R → S` vanishes iff the carve arrow of the *pushed-forward*
  pair (`ker (baseChangeMkQ)`, the submodule of mathlib's `Module.Grassmannian.map`)
  vanishes.  Mechanism: the splitting `ker_baseChange_mkQ` plus the `cancelBaseChange`
  naturality square.
* **Kills-determined ideals**: `ideal_eq_of_forall_le_ker_iff` — two ideals killed by the
  same test algebras are equal (quotient trick), the bridge between `entriesIdeal`
  spellings of the same closed condition.
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgebraicGeometry.Grassmannian

/-! ## The projective-quotient retraction -/

section Retract

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
variable (N : Submodule R M) [Module.Projective R (M ⧸ N)]

/-- A chosen splitting of the quotient map of a projective-quotient submodule. -/
noncomputable def quotSection : (M ⧸ N) →ₗ[R] M :=
  (Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective).choose

lemma mkQ_comp_quotSection : N.mkQ ∘ₗ quotSection N = LinearMap.id :=
  (Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective).choose_spec

lemma sub_quotSection_mem (y : M) : y - quotSection N (N.mkQ y) ∈ N := by
  have h1 := LinearMap.congr_fun (mkQ_comp_quotSection N) (N.mkQ y)
  rw [LinearMap.comp_apply, LinearMap.id_apply] at h1
  rw [← Submodule.Quotient.mk_eq_zero N,
    show Submodule.Quotient.mk (p := N) (y - quotSection N (N.mkQ y))
      = N.mkQ (y - quotSection N (N.mkQ y)) from rfl,
    map_sub, h1, sub_self]

/-- The retraction of the ambient module onto a projective-quotient submodule:
`x ↦ x - σ(mkQ x)`. -/
noncomputable def quotRetract : M →ₗ[R] ↥N :=
  ((LinearMap.id : M →ₗ[R] M) - quotSection N ∘ₗ N.mkQ).codRestrict N fun c => by
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    exact sub_quotSection_mem N c

lemma subtype_comp_quotRetract :
    N.subtype ∘ₗ quotRetract N + quotSection N ∘ₗ N.mkQ = LinearMap.id := by
  rw [quotRetract, LinearMap.subtype_comp_codRestrict, sub_add_cancel]

lemma quotRetract_apply_of_mem {x : M} (hx : x ∈ N) : quotRetract N x = ⟨x, hx⟩ := by
  apply Subtype.ext
  have hx0 : N.mkQ x = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hx
  rw [quotRetract, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.comp_apply, hx0, map_zero, sub_zero]

/-- A submodule of a finite module with projective quotient is finite: the retraction
`quotRetract` is a surjection from the ambient module. -/
theorem finite_submodule_of_projective_quotient [Module.Finite R M] :
    Module.Finite R ↥N :=
  Module.Finite.of_surjective (quotRetract N) fun x =>
    ⟨x.1, by rw [quotRetract_apply_of_mem N x.2]⟩

/-- **The projective-quotient splitting of base change**: for a submodule `N ⊆ M` with
projective quotient, the kernel of the base-changed quotient map `mkQ ⊗ S` is exactly
the base change `N.baseChange S` (the `S`-span of the image of `N`).  The SES
`0 → N → M → M⧸N → 0` splits, and split exact sequences stay exact under base change. -/
theorem ker_baseChange_mkQ (S : Type u) [CommRing S] [Algebra R S] :
    LinearMap.ker (LinearMap.baseChange S N.mkQ) = N.baseChange S := by
  rw [Submodule.baseChange]
  refine le_antisymm ?_ ?_
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    have h2 := LinearMap.congr_fun
      (congrArg (LinearMap.baseChange S) (subtype_comp_quotRetract N)) z
    rw [LinearMap.baseChange_add, LinearMap.baseChange_comp, LinearMap.baseChange_comp,
      LinearMap.baseChange_id, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, hz, map_zero, add_zero, LinearMap.id_apply] at h2
    exact LinearMap.mem_range.mpr ⟨LinearMap.baseChange S (quotRetract N) z, h2⟩
  · rw [LinearMap.range_le_ker_iff, ← LinearMap.baseChange_comp,
      show N.mkQ ∘ₗ N.subtype = 0 from LinearMap.ext fun x => by
        simp [Submodule.Quotient.mk_eq_zero],
      LinearMap.baseChange_zero]

end Retract

/-! ## The generic carve-pair arrow and its base-change transport -/

section CarvePair

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R]
variable {H₁ H₂ : Type u} [AddCommGroup H₁] [Module k H₁] [AddCommGroup H₂] [Module k H₂]

/-- **The generic carve-pair arrow** at a single multiplier `μ : H₁ →ₗ[k] H₂`: the
composite `Km ↪ R ⊗ H₁ → (μ ⊗ R) → R ⊗ H₂ ↠ (R ⊗ H₂) ⧸ K'`.  The DAT-D carve arrow
`carveArrow` (SectionMul) is the instance `μ := sectionMulBilin K A B a`. -/
noncomputable def carvePairArrow (μ : H₁ →ₗ[k] H₂) (Km : Submodule R (TensorProduct k R H₁))
    (K' : Submodule R (TensorProduct k R H₂)) :
    ↥Km →ₗ[R] (TensorProduct k R H₂) ⧸ K' :=
  K'.mkQ ∘ₗ LinearMap.baseChange R μ ∘ₗ Km.subtype

/-- The carve-pair arrow vanishes iff the multiplier maps `Km` into `K'`. -/
theorem carvePairArrow_eq_zero_iff (μ : H₁ →ₗ[k] H₂) (Km : Submodule R (TensorProduct k R H₁))
    (K' : Submodule R (TensorProduct k R H₂)) :
    carvePairArrow μ Km K' = 0 ↔ ∀ x ∈ Km, LinearMap.baseChange R μ x ∈ K' := by
  constructor
  · intro h x hx
    have h1 := LinearMap.congr_fun h ⟨x, hx⟩
    rwa [carvePairArrow, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
  · intro h
    refine LinearMap.ext fun x => ?_
    rw [carvePairArrow, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h x.1 x.2

variable (S : Type u) [CommRing S] [Algebra k S] [Algebra R S] [IsScalarTower k R S]

/-- Naturality of `cancelBaseChange` against the twice-base-changed multiplier:
`cancel ∘ (μ ⊗ R ⊗ S) = (μ ⊗ S) ∘ cancel`. -/
theorem cancelBaseChange_comp_baseChange_baseChange (μ : H₁ →ₗ[k] H₂) :
    (AlgebraTensorModule.cancelBaseChange k R S S H₂).toLinearMap
        ∘ₗ LinearMap.baseChange S (LinearMap.baseChange R μ)
      = LinearMap.baseChange S μ
          ∘ₗ (AlgebraTensorModule.cancelBaseChange k R S S H₁).toLinearMap := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at ha hb
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_add, ha, hb]
  | tmul s x =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at ha hb
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.tmul_add,
        map_add, ha, hb]
    | tmul r h =>
      simp [AlgebraTensorModule.cancelBaseChange_tmul]

/-- The kernel of `baseChangeMkQ` is the `cancelBaseChange`-image of the base-changed
submodule (projective quotient): the concrete span description of the submodule of
mathlib's `Module.Grassmannian.map`. -/
theorem ker_baseChangeMkQ_eq_map_baseChange {H : Type u} [AddCommGroup H] [Module k H]
    (N : Submodule R (TensorProduct k R H))
    [Module.Projective R (TensorProduct k R H ⧸ N)] :
    LinearMap.ker (Module.Grassmannian.baseChangeMkQ S N)
      = Submodule.map (AlgebraTensorModule.cancelBaseChange k R S S H).toLinearMap
          (N.baseChange S) := by
  have hval : ∀ x, Module.Grassmannian.baseChangeMkQ S N x
      = LinearMap.baseChange S N.mkQ
          ((AlgebraTensorModule.cancelBaseChange k R S S H).symm x) := fun _ => rfl
  ext x
  rw [LinearMap.mem_ker, hval, ← LinearMap.mem_ker, ker_baseChange_mkQ]
  constructor
  · intro hx
    exact ⟨(AlgebraTensorModule.cancelBaseChange k R S S H).symm x, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

/-- **The carve transport (L1)**: for a projective-quotient pair `(Km, K')` over `R`, the
base change of the carve-pair arrow to `S` vanishes iff the carve-pair arrow of the
pushed-forward pair (`ker (baseChangeMkQ)`, i.e. the submodule of mathlib's
`Module.Grassmannian.map`) vanishes over `S`.  The `(♦)` condition is functorial in the
test ring. -/
theorem baseChange_carvePairArrow_eq_zero_iff (μ : H₁ →ₗ[k] H₂)
    (Km : Submodule R (TensorProduct k R H₁)) (K' : Submodule R (TensorProduct k R H₂))
    [Module.Projective R (TensorProduct k R H₁ ⧸ Km)]
    [Module.Projective R (TensorProduct k R H₂ ⧸ K')] :
    LinearMap.baseChange S (carvePairArrow μ Km K') = 0 ↔
      carvePairArrow μ (LinearMap.ker (Module.Grassmannian.baseChangeMkQ S Km))
        (LinearMap.ker (Module.Grassmannian.baseChangeMkQ S K')) = 0 := by
  have hnat : ∀ y : S ⊗[R] TensorProduct k R H₁,
      (AlgebraTensorModule.cancelBaseChange k R S S H₂).toLinearMap
          (LinearMap.baseChange S (LinearMap.baseChange R μ) y)
        = LinearMap.baseChange S μ
            ((AlgebraTensorModule.cancelBaseChange k R S S H₁).toLinearMap y) := by
    intro y
    have h1 := LinearMap.congr_fun (cancelBaseChange_comp_baseChange_baseChange
      (k := k) (R := R) S μ) y
    rwa [LinearMap.comp_apply, LinearMap.comp_apply] at h1
  have hLHS : LinearMap.baseChange S (carvePairArrow μ Km K') = 0 ↔
      Submodule.map (LinearMap.baseChange S (LinearMap.baseChange R μ)) (Km.baseChange S)
        ≤ K'.baseChange S := by
    rw [carvePairArrow, LinearMap.baseChange_comp, LinearMap.baseChange_comp,
      ← LinearMap.comp_assoc, ← LinearMap.range_le_ker_iff, LinearMap.ker_comp,
      ker_baseChange_mkQ,
      show LinearMap.range (LinearMap.baseChange S Km.subtype) = Km.baseChange S from rfl,
      ← Submodule.map_le_iff_le_comap]
  rw [hLHS, carvePairArrow_eq_zero_iff, ker_baseChangeMkQ_eq_map_baseChange,
    ker_baseChangeMkQ_eq_map_baseChange]
  constructor
  · rintro h _ ⟨y, hy, rfl⟩
    rw [← hnat y]
    exact ⟨LinearMap.baseChange S (LinearMap.baseChange R μ) y,
      h (Submodule.mem_map_of_mem hy), rfl⟩
  · intro h
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_comap]
    have h1 := h _ (Submodule.mem_map_of_mem
      (f := (AlgebraTensorModule.cancelBaseChange k R S S H₁).toLinearMap) hy)
    rw [← hnat y] at h1
    obtain ⟨w, hw, hweq⟩ := h1
    have h2 : w = LinearMap.baseChange S (LinearMap.baseChange R μ) y := by
      have := congrArg (AlgebraTensorModule.cancelBaseChange k R S S H₂).symm hweq
      simpa using this
    rwa [h2] at hw

end CarvePair

/-! ## Kills-determined ideals -/

section KillsDetermined

/-- An ideal is killed by a ring map iff the map factors (uniquely) through the
quotient: the representing property of `Spec (R ⧸ I) → Spec R`, at the level of ring
maps (the `entriesIdeal_le_ker_iff_factors` argument, for an arbitrary ideal). -/
theorem ideal_le_ker_iff_factors {R : Type u} [CommRing R] (I : Ideal R) {S : Type u}
    [CommRing S] (f : R →+* S) :
    I ≤ RingHom.ker f ↔
      ∃! g : R ⧸ I →+* S, g.comp (Ideal.Quotient.mk I) = f := by
  constructor
  · intro h
    have hker : ∀ a ∈ I, f a = 0 := fun x hx => RingHom.mem_ker.mp (h hx)
    refine ⟨Ideal.Quotient.lift I f hker,
      RingHom.ext fun x => Ideal.Quotient.lift_mk I f hker, ?_⟩
    intro g hg
    refine RingHom.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [show g (Ideal.Quotient.mk I x) = (g.comp (Ideal.Quotient.mk I)) x from rfl, hg]
    exact (Ideal.Quotient.lift_mk I f hker).symm
  · rintro ⟨g, hg, -⟩ x hx
    rw [RingHom.mem_ker, ← hg, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- **Two ideals killed by the same test algebras are equal** (the quotient trick): if
for every algebra `S`, `I` dies in `S` iff `J` dies in `S`, then `I = J`.  The bridge
between `entriesIdeal` spellings of the same closed condition. -/
theorem ideal_eq_of_forall_le_ker_iff {R : Type u} [CommRing R] {I J : Ideal R}
    (h : ∀ (S : Type u) [CommRing S] [Algebra R S],
      I ≤ RingHom.ker (algebraMap R S) ↔ J ≤ RingHom.ker (algebraMap R S)) : I = J := by
  have hI : I ≤ RingHom.ker (algebraMap R (R ⧸ I)) := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  have hJ : J ≤ RingHom.ker (algebraMap R (R ⧸ J)) := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  refine le_antisymm ?_ ?_
  · have := (h (R ⧸ J)).mpr hJ
    rwa [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] at this
  · have := (h (R ⧸ I)).mp hI
    rwa [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] at this

end KillsDetermined
end AlgebraicGeometry.Grassmannian
