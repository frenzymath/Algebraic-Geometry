/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Devissage
import AlgebraicJacobian.RiemannRoch.PrincipalDivisor

/-!
# Short exactness of the dévissage complex

For the curve bundle `X` (integral, smooth of relative dimension one over a field `K`), a Weil
divisor `D : X.CurveDivisor` and a closed point `x` (`hx : x ≠ η`), `Devissage.lean` assembles the
dévissage short complex

    0 ⟶ 𝒪(D − x) ⟶ 𝒪(D) ⟶ sky_x J ⟶ 0

of sheaves of `K`-modules (`AlgebraicGeometry.devissageSES`), with its left-exactness certificate
`devissageSES_mono_f`. This file supplies the two missing certificates and packages them into

* `AlgebraicGeometry.devissageSES_epi_g`: the projection `π : 𝒪(D) ⟶ sky_x J` is an
  epimorphism. It is proved locally surjective (`devissageπ_isLocallySurjective`): away from `x`
  the target skyscraper sections vanish, while at `x` a representative `g` of a jump class has
  poles bounded outside a *finite* bad locus, which is excised to produce a local `D`-section.
* `AlgebraicGeometry.devissageSES_exact`: the complex is exact in the middle. Exactness is
  reflected from the sections short complexes: over each open the sequence of `K`-modules is exact
  (`devissageSES_map_exact`), and `sheafToPresheaf` (creating limits) together with the evaluation
  functors (jointly reflecting limits) transport the sectionwise kernel forks to a kernel fork of
  sheaves.
* `AlgebraicGeometry.devissageSES_shortExact`: the resulting `ShortComplex.ShortExact`.

The quasi-compactness hypothesis `[QuasiCompact (X ↘ Spec K)]` enters only through the epimorphism,
via the finiteness of the principal-divisor support (`Scheme.ordZ_support_finite`).

## Conventions

The skyscraper sheaf `skyModule` and the projection `devissageπ` are only ever manipulated through
the sealed behaviour lemmas of `Devissage.lean`/`Skyscraper.lean`; the `eqToHom` identifications of
the skyscraper are chased once, in `devissageπ_app_eq_restrict`.
-/

set_option autoImplicit false
set_option linter.style.openClassical false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

attribute [local instance] AlgebraicGeometry.Scheme.functionFieldOverModule
  AlgebraicGeometry.Scheme.overModule

namespace AlgebraicGeometry

open Scheme

open scoped Classical

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  {x : X} (hx : x ≠ genericPoint X) (D : X.CurveDivisor)

/-- `LocallyOfFiniteType` of the structure morphism, derived from smoothness of relative
dimension one (needed to invoke `Scheme.ordZ_support_finite`). -/
instance locallyOfFiniteType_structureMorphism :
    LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (X ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (CommRingCat.of K))
  inferInstance

/-! ## Part 1: the dévissage projection is a local epimorphism -/

/-- **The eqToHom bridge.** For opens `W ≤ U` both containing `x` and a global-jump datum
`t` over `U`, a `D`-section `s` over `W` whose jump class `jumpProj s` matches the transported
value of `t` maps under `π` to the restriction `t|_W`. This is the sole place the skyscraper
`eqToHom` seams are chased; downstream local-lift constructions only need to produce such an `s`. -/
lemma devissageπ_app_eq_restrict {U W : X.Opens} (hxU : x ∈ U) (hxW : x ∈ W) (i : W ⟶ U)
    (t : (skyModule x (jumpModule K hx D)).obj.obj (op U))
    (s : (divisorPresheaf K D).obj (op W))
    (hst : jumpProj K hx D W hxW s
      = (eqToHom (skyModule_obj_of_mem' (jumpModule K hx D) hxU)).hom t) :
    ((devissageπ K hx D).hom.app (op W)).hom s
      = ((skyModule x (jumpModule K hx D)).obj.map i.op).hom t := by
  rw [devissageπ_app_hom_apply_of_mem K hx D (op W) hxW s, hst,
    skyModule_map_eq (jumpModule K hx D) i.op hxU hxW,
    ← eqToHom_trans (skyModule_obj_of_mem' (jumpModule K hx D) hxU)
      (skyModule_obj_of_mem' (jumpModule K hx D) hxW).symm]
  rfl

/-- **Local surjectivity away from `x`.** Over any open `W` avoiding `x` the target skyscraper
sections are trivial, so every arrow `W ⟶ U` lies in the image sieve (with the zero witness). -/
lemma imageSieve_of_not_mem {U W : X.Opens} (i : W ⟶ U) (hxW : x ∉ W)
    (t : (skyModule x (jumpModule K hx D)).obj.obj (op U)) :
    (Presheaf.imageSieve (devissageπ K hx D).hom t) i := by
  haveI := skyModule_obj_subsingleton (jumpModule K hx D) hxW
  exact ⟨0, Subsingleton.elim _ _⟩

/-- **The substantive local lift at `x`.** For `x ∈ U` and a jump datum `t` over `U`, some
open neighbourhood `W ∋ x` inside `U` carries a `D`-section mapping to `t|_W`: a representative
rational function `g` of the jump class of `t` has controlled poles away from a finite bad set,
which we excise from `U`. -/
lemma devissage_local_lift [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    {U : X.Opens} (hxU : x ∈ U)
    (t : (skyModule x (jumpModule K hx D)).obj.obj (op U)) :
    ∃ (W : X.Opens) (i : W ⟶ U),
      (Presheaf.imageSieve (devissageπ K hx D).hom t) i ∧ x ∈ W := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    ((eqToHom (skyModule_obj_of_mem' (jumpModule K hx D) hxU)).hom t)
  have hgP : (y : X.functionField) ∈ pointLattice K hx (coeffAt hx D) := y.2
  by_cases hg0 : (y : X.functionField) = 0
  · -- the class is zero: the zero section over `U` itself does the job
    refine ⟨U, 𝟙 U, ⟨(0 : divisorSections K D U), ?_⟩, hxU⟩
    have hst : jumpProj K hx D U hxU (0 : divisorSections K D U)
        = (eqToHom (skyModule_obj_of_mem' (jumpModule K hx D) hxU)).hom t := by
      have hy0 : y = 0 := Subtype.ext (by rw [ZeroMemClass.coe_zero]; exact hg0)
      rw [map_zero, ← hy, hy0]
      rfl
    exact devissageπ_app_eq_restrict K hx D hxU hxU (𝟙 U) t _ hst
  · -- nonzero class: excise the finite bad locus of poles
    set g : X.functionField := (y : X.functionField) with hg_def
    set gu : X.functionFieldˣ := Units.mk0 g hg0 with hgu
    have hguv : (gu : X.functionField) = g := rfl
    set Bad : Set X := {z | ∃ (hz : z ≠ genericPoint X),
        ¬ (Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz g ≤ divisorBound D hz)} with hBad
    have hfin : Bad.Finite := by
      apply Set.Finite.subset
        (((Scheme.ordZ_support_finite (X ↘ Spec (CommRingCat.of K)) gu).image Subtype.val).union
          ((toFinsupp D).support.finite_toSet.image Subtype.val))
      intro z hz
      obtain ⟨hzne, hzbad⟩ := hz
      by_contra hcon
      simp only [Set.mem_union, not_or] at hcon
      obtain ⟨hc1, hc2⟩ := hcon
      have hord1 : Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hzne gu = 1 := by
        by_contra hne
        exact hc1 ⟨⟨z, hzne⟩, hne, rfl⟩
      have hsupp : (toFinsupp D) ⟨z, hzne⟩ = 0 := by
        by_contra hne
        exact hc2 ⟨⟨z, hzne⟩, Finsupp.mem_support_iff.mpr hne, rfl⟩
      apply hzbad
      have hordg : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hzne g = 1 := by
        rw [← hguv, ← Scheme.ordZ_eq_one_iff]; exact hord1
      have hdb : divisorBound D hzne
          = ((Multiplicative.ofAdd ((toFinsupp D) ⟨z, hzne⟩) : Multiplicative ℤ) :
              WithZero (Multiplicative ℤ)) := rfl
      rw [hordg, hdb, hsupp]
      simp
    have hBadClosed : IsClosed Bad := by
      rw [← Set.biUnion_of_singleton Bad]
      exact hfin.isClosed_biUnion
        (fun z hz => isClosed_singleton_of_ne_genericPoint
          (X ↘ Spec (CommRingCat.of K)) hz.choose)
    set W : X.Opens := U ⊓ ⟨Badᶜ, hBadClosed.isOpen_compl⟩ with hW
    have hxbound : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g ≤ divisorBound D hx := by
      rw [divisorBound_eq_coeffAt]; exact (mem_pointLattice K hx).mp hgP
    have hxBad : x ∉ Bad := fun ⟨_, hbad⟩ => hbad hxbound
    have hxW : x ∈ W := ⟨hxU, hxBad⟩
    have hWne : (W : Set X).Nonempty := ⟨x, hxW⟩
    have hgmem : g ∈ divisorSections K D W := by
      rw [mem_divisorSections_of_nonempty K hWne]
      intro z hz hzW
      by_contra h
      exact hzW.2 ⟨hz, h⟩
    refine ⟨W, homOfLE inf_le_left, ⟨⟨g, hgmem⟩, ?_⟩, hxW⟩
    have hst : jumpProj K hx D W hxW ⟨g, hgmem⟩
        = (eqToHom (skyModule_obj_of_mem' (jumpModule K hx D) hxU)).hom t := by
      rw [jumpProj_apply, ← hy]
    exact devissageπ_app_eq_restrict K hx D hxU hxW (homOfLE inf_le_left) t _ hst

/-- **`π` is a local epimorphism.** Every jump section is locally in the image: at `x` via
`devissage_local_lift`, and everywhere else the target skyscraper sections vanish. -/
instance devissageπ_isLocallySurjective [QuasiCompact (X ↘ Spec (CommRingCat.of K))] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (X : TopCat))
      (devissageπ K hx D).hom where
  imageSieve_mem {U} t := by
    intro p hp
    by_cases hxU : x ∈ U
    · by_cases hpx : p = x
      · subst hpx
        obtain ⟨W, i, hsieve, hxW⟩ := devissage_local_lift K hx D hxU t
        exact ⟨W, i, hsieve, hxW⟩
      · refine ⟨U ⊓ ⟨{x}ᶜ, (isClosed_singleton_of_ne_genericPoint
            (X ↘ Spec (CommRingCat.of K)) hx).isOpen_compl⟩,
          homOfLE inf_le_left,
          imageSieve_of_not_mem K hx D (homOfLE inf_le_left) ?_ t, ⟨hp, hpx⟩⟩
        exact fun hxW => hxW.2 rfl
    · exact ⟨U, 𝟙 U, imageSieve_of_not_mem K hx D _ hxU t, hp⟩

/-- **The dévissage projection is an epimorphism of sheaves.** Local surjectivity implies epi
in the sheaf category of `K`-modules. -/
instance devissageSES_epi_g [QuasiCompact (X ↘ Spec (CommRingCat.of K))] :
    Epi (devissageSES K hx D).g := by
  have hls : Sheaf.IsLocallySurjective (devissageπ K hx D) :=
    devissageπ_isLocallySurjective K hx D
  exact (Sheaf.isLocallySurjective_iff_epi' (A := ModuleCat.{u} K) (devissageπ K hx D)).mp hls

/-! ## Part 2: middle exactness -/

/-- A `D`-section over `W ∋ x` has vanishing jump class iff its pole order at `x` is bounded by
`D x − 1` (both directions of `jumpProj_eq_zero_of_mem`). -/
lemma jumpProj_eq_zero_iff {W : X.Opens} (hxW : x ∈ W) (s : divisorSections K D W) :
    jumpProj K hx D W hxW s = 0 ↔
      (s : X.functionField) ∈ pointLattice K hx (coeffAt hx D - 1) := by
  constructor
  · intro h
    rw [jumpProj_apply] at h
    have hm : (⟨(s : X.functionField), divisorSections_le_pointLattice K hx D W hxW s.2⟩ :
        pointLattice K hx (coeffAt hx D))
        ∈ (pointLattice K hx (coeffAt hx D - 1)).submoduleOf (pointLattice K hx (coeffAt hx D)) :=
      (Submodule.Quotient.mk_eq_zero _).mp h
    exact hm
  · exact jumpProj_eq_zero_of_mem K hx D W hxW s

/-- Away from `x`, the divisor bound of `D − x` equals that of `D`. -/
lemma divisorBound_devissageDivisor_of_ne {z : X} (hz : z ≠ genericPoint X)
    (hzx : (⟨z, hz⟩ : {p : X // p ≠ genericPoint X}) ≠ ⟨x, hx⟩) :
    divisorBound (devissageDivisor hx D) hz = divisorBound D hz := by
  change ((Multiplicative.ofAdd ((toFinsupp (devissageDivisor hx D)) ⟨z, hz⟩) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ))
      = ((Multiplicative.ofAdd ((toFinsupp D) ⟨z, hz⟩) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ))
  rw [coeffAt_devissageDivisor_of_ne hx D hzx]

/-- For `x ∈ W`, a `D`-section whose pole at `x` is bounded by `D x − 1` is a `(D − x)`-section. -/
lemma coe_mem_divisorSections_devissage {W : X.Opens} (hxW : x ∈ W) (s : divisorSections K D W)
    (hmem : (s : X.functionField) ∈ pointLattice K hx (coeffAt hx D - 1)) :
    (s : X.functionField) ∈ divisorSections K (devissageDivisor hx D) W := by
  have hne : (W : Set X).Nonempty := ⟨x, hxW⟩
  rw [mem_divisorSections_of_nonempty K hne]
  intro z hz hzW
  by_cases hzx : (⟨z, hz⟩ : {p : X // p ≠ genericPoint X}) = ⟨x, hx⟩
  · have hzeq : z = x := congrArg Subtype.val hzx
    subst hzeq
    have hb : divisorBound (devissageDivisor hx D) hz
        = ((Multiplicative.ofAdd (coeffAt hx D - 1) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
      rw [← coeffAt_devissageDivisor hx D]; rfl
    rw [hb]
    exact (mem_pointLattice K hx).mp hmem
  · rw [divisorBound_devissageDivisor_of_ne hx D hz hzx]
    exact (mem_divisorSections_of_nonempty K hne).mp s.2 z hz hzW

/-- For `x ∉ W`, every `D`-section is a `(D − x)`-section (the bounds agree on `W`). -/
lemma divisorSections_le_devissage_of_not_mem {W : X.Opens} (hxW : x ∉ W) :
    divisorSections K D W ≤ divisorSections K (devissageDivisor hx D) W := by
  by_cases hne : (W : Set X).Nonempty
  · rw [divisorSections_of_nonempty K hne, divisorSections_of_nonempty K hne]
    intro v hv z hz hzW
    have hzx : (⟨z, hz⟩ : {p : X // p ≠ genericPoint X}) ≠ ⟨x, hx⟩ := by
      intro h
      have hzeq : z = x := congrArg Subtype.val h
      exact hxW (hzeq ▸ hzW)
    rw [divisorBound_devissageDivisor_of_ne hx D hz hzx]
    exact hv z hz hzW
  · rw [divisorSections_of_empty K hne]
    exact bot_le

/-- **Sectionwise exactness.** Over every open `W`, the sections short complex of the dévissage
complex is exact in `K`-modules: a `D`-section killed by `π` at `W` differs from a `(D − x)`-section
only in bookkeeping. -/
lemma devissageSES_map_exact (W : (X.Opens)ᵒᵖ) :
    ((devissageSES K hx D).map (sheafToPresheaf (Opens.grothendieckTopology (X : TopCat))
      (ModuleCat.{u} K) ⋙ (evaluation _ (ModuleCat.{u} K)).obj W)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro s hs
  change (divisorSections K D (unop W) : Type _) at s
  have hgs : ((devissageπ K hx D).hom.app W).hom s = 0 := hs
  have hmem : (s : X.functionField) ∈ divisorSections K (devissageDivisor hx D) (unop W) := by
    by_cases hxW : x ∈ (unop W : X.Opens)
    · have hjump : jumpProj K hx D (unop W) hxW s = 0 := by
        have heq := hgs
        rw [devissageπ_app_hom_apply_of_mem K hx D W hxW s] at heq
        have hinj : Function.Injective (eqToHom (skyModule_obj_of_mem'
            (jumpModule K hx D) hxW).symm).hom :=
          (ModuleCat.mono_iff_injective _).mp inferInstance
        apply hinj
        rw [heq, map_zero]
      exact coe_mem_divisorSections_devissage K hx D hxW s
        ((jumpProj_eq_zero_iff K hx D hxW s).mp hjump)
    · exact divisorSections_le_devissage_of_not_mem K hx D hxW s.2
  refine ⟨⟨(s : X.functionField), hmem⟩, ?_⟩
  apply Subtype.ext
  change (((divisorSheafLE K (devissageDivisor_le hx D)).hom.app W).hom
      ⟨(s : X.functionField), hmem⟩).1 = (s : X.functionField)
  rw [divisorSheafLE_app_hom_apply]

theorem devissageSES_exact :
    (devissageSES K hx D).Exact := by
  have hsec : ∀ W : (X.Opens)ᵒᵖ,
      IsLimit (KernelFork.ofι
        ((devissageSES K hx D).map (sheafToPresheaf (Opens.grothendieckTopology (X : TopCat))
          (ModuleCat.{u} K) ⋙ (evaluation _ (ModuleCat.{u} K)).obj W)).f
        ((devissageSES K hx D).map (sheafToPresheaf (Opens.grothendieckTopology (X : TopCat))
          (ModuleCat.{u} K) ⋙ (evaluation _ (ModuleCat.{u} K)).obj W)).zero) := by
    intro W
    haveI : Mono ((devissageSES K hx D).map (sheafToPresheaf
        (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} K) ⋙
          (evaluation _ (ModuleCat.{u} K)).obj W)).f :=
      (ModuleCat.mono_iff_injective _).mpr
        (Sheaf.app_injective_of_mono (devissageSES K hx D).f W)
    exact (devissageSES_map_exact K hx D W).fIsKernel
  have hlim : IsLimit (KernelFork.ofι (devissageSES K hx D).f (devissageSES K hx D).zero) := by
    apply isLimitOfReflects (sheafToPresheaf (Opens.grothendieckTopology (X : TopCat))
      (ModuleCat.{u} K))
    refine (Limits.isLimitMapConeForkEquiv' _ (devissageSES K hx D).zero).symm ?_
    apply evaluationJointlyReflectsLimits
    intro W
    exact (Limits.isLimitMapConeForkEquiv' ((evaluation _ (ModuleCat.{u} K)).obj W) _).symm (hsec W)
  exact (devissageSES K hx D).exact_of_f_is_kernel hlim

/-! ## Assembly: the dévissage short exact sequence -/

/-- **The dévissage short exact sequence.** `0 ⟶ 𝒪(D − x) ⟶ 𝒪(D) ⟶ sky_x J ⟶ 0` is a short
exact sequence of sheaves of `K`-modules: the inclusion is a monomorphism (`devissageSES_mono_f`),
the projection is an epimorphism (`devissageSES_epi_g`), and the complex is exact in the middle
(`devissageSES_exact`). -/
theorem devissageSES_shortExact [QuasiCompact (X ↘ Spec (CommRingCat.of K))] :
    (devissageSES K hx D).ShortExact where
  exact := devissageSES_exact K hx D
  mono_f := devissageSES_mono_f K hx D
  epi_g := devissageSES_epi_g K hx D

end AlgebraicGeometry
