/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.DivisorSheaf
import AlgebraicJacobian.RiemannRoch.Ledger.Skyscraper
import AlgebraicJacobian.RiemannRoch.Ledger.PrincipalDivisor

/-!
# The dévissage complex at a closed point

For the curve bundle `X` (integral, smooth of relative dimension one over a field `K`), a Weil
divisor `D : X.CurveDivisor`, and a closed point `x` (a non-generic point `hx : x ≠ η`), this
file builds the **dévissage short complex**

    0 ⟶ 𝒪(D − x) ⟶ 𝒪(D) ⟶ sky_x J ⟶ 0

of sheaves of `K`-modules, where `J = jumpModule` is the one-point *jump module* and `sky_x` is
the skyscraper sheaf at `x`. Writing `x̂ = ⟨x, hx⟩` and `D' = D − single x̂ 1`:

* `AlgebraicGeometry.pointLattice`: the `K`-submodule of `K(X)` of rational functions whose pole
  order at the single closed point `x` is bounded by `ofAdd n` (the one-point analogue of
  `Scheme.boundedSections`).
* `AlgebraicGeometry.jumpModule`: the *jump module* `pointLattice (D x̂) ⧸ pointLattice (D x̂ − 1)`,
  the associated-graded piece of the valuation filtration at `x`.
* `AlgebraicGeometry.jumpProj`: for an open `U ∋ x`, the `K`-linear projection
  `𝒪(D)(U) → jumpModule`, `g ↦ ⟦g⟧`.
* `AlgebraicGeometry.devissageπ`: the morphism of sheaves `𝒪(D) ⟶ sky_x J`.
* `AlgebraicGeometry.devissageSES`: the `ShortComplex` assembled from the inclusion
  `𝒪(D − x) ↪ 𝒪(D)` and `devissageπ` (their composite is `0`, `devissage_comp_eq_zero`), with the
  monomorphism certificate `devissageSES_mono_f`. The remaining exactness/epimorphism certificates
  (`ShortExact`) are not established here.

## Conventions

The `K`-module structure on `K(X)` is `Scheme.functionFieldOverModule`, activated as a local
instance (never a global `Algebra`), matching `DivisorSheaf.lean`. The skyscraper sheaf is the
sealed `AlgebraicGeometry.skyModule` of `Skyscraper.lean`; downstream rewriting always routes
through its behaviour lemmas, never the raw `if`/`terminal`-tower.
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

/-! ## S1: the jump module -/

/-- The underlying finitely supported function of a Weil divisor (`CurveDivisor` is definitionally
a `Finsupp`, but the wrapper blocks `FunLike`/`Sub`; this genuine coercion re-exposes them). -/
def toFinsupp (D : X.CurveDivisor) : {p : X // p ≠ genericPoint X} →₀ ℤ := D

/-- The integer coefficient of the Weil divisor `D` at the closed point `x = ⟨x, hx⟩`. -/
def coeffAt : ℤ :=
  toFinsupp D ⟨x, hx⟩

/-- **The one-point valuation lattice.** The `K`-submodule of `K(X)` of rational functions whose
pole order at the single closed point `x` is bounded by `ofAdd n`:
`{g | ord_x g ≤ ofAdd n}`. This is the one-point analogue of `Scheme.boundedSections`; the same
closure proofs apply (a valuation is submultiplicative, the `K`-structure map has order `≤ 1`). -/
noncomputable def pointLattice (n : ℤ) : Submodule K X.functionField where
  carrier := {g | Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g ≤
    ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ))}
  zero_mem' := by rw [Set.mem_setOf_eq, map_zero]; exact zero_le
  add_mem' := fun {g₁ g₂} h₁ h₂ => by
    simp only [Set.mem_setOf_eq] at h₁ h₂ ⊢
    exact le_trans (Valuation.map_add _ g₁ g₂) (max_le h₁ h₂)
  smul_mem' := fun r g hg => by
    simp only [Set.mem_setOf_eq] at hg ⊢
    rw [functionFieldOverModule_smul_def, map_mul]
    calc Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (functionFieldOverAlgebraMap K X r)
            * Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g
        ≤ 1 * Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g := by
          gcongr; exact ord_functionFieldOverAlgebraMap_le_one K hx r
      _ = Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g := one_mul _
      _ ≤ _ := hg

lemma mem_pointLattice {n : ℤ} {g : X.functionField} :
    g ∈ pointLattice K hx n ↔
      Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g ≤
        ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
  Iff.rfl

/-- The one-point lattices are monotone: a larger bound admits more functions. -/
lemma pointLattice_mono {m n : ℤ} (h : m ≤ n) : pointLattice K hx m ≤ pointLattice K hx n := by
  intro g hg
  rw [mem_pointLattice] at hg ⊢
  refine le_trans hg ?_
  exact_mod_cast Multiplicative.ofAdd_le.mpr h

/-- The divisor bound at `x` is the one-point bound `ofAdd (D x̂)`. -/
lemma divisorBound_eq_coeffAt :
    divisorBound D hx =
      ((Multiplicative.ofAdd (coeffAt hx D) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
  rfl

/-- **The jump module** `J = 𝒪(D)ₓ ⧸ 𝒪(D − x)ₓ` at the closed point `x`: the associated-graded
piece of the one-point valuation filtration, `pointLattice (D x̂) ⧸ pointLattice (D x̂ − 1)`. -/
noncomputable def jumpModule : ModuleCat.{u} K :=
  ModuleCat.of K
    (pointLattice K hx (coeffAt hx D) ⧸
      (pointLattice K hx (coeffAt hx D - 1)).submoduleOf (pointLattice K hx (coeffAt hx D)))

/-- Sections of `𝒪(D)` over an open `U ∋ x` are bounded by `D` at `x`: they lie in the
one-point lattice `pointLattice (D x̂)`. -/
lemma divisorSections_le_pointLattice (U : X.Opens) (hxU : x ∈ U) :
    divisorSections K D U ≤ pointLattice K hx (coeffAt hx D) := by
  have hne : (U : Set X).Nonempty := ⟨x, hxU⟩
  intro g hg
  rw [mem_divisorSections_of_nonempty K hne] at hg
  rw [mem_pointLattice]
  have hgx := hg x hx hxU
  rwa [divisorBound_eq_coeffAt] at hgx

/-- **The quotient projection** `𝒪(D)(U) → J`, `g ↦ ⟦g⟧`, for an open `U ∋ x`: a section of
`𝒪(D)` over `U` is bounded by `D` at `x`, hence defines a class in the jump module. -/
noncomputable def jumpProj (U : X.Opens) (hxU : x ∈ U) :
    divisorSections K D U →ₗ[K] jumpModule K hx D :=
  (Submodule.mkQ ((pointLattice K hx (coeffAt hx D - 1)).submoduleOf
      (pointLattice K hx (coeffAt hx D)))).comp
    (Submodule.inclusion (divisorSections_le_pointLattice K hx D U hxU))

lemma jumpProj_apply (U : X.Opens) (hxU : x ∈ U) (s : divisorSections K D U) :
    jumpProj K hx D U hxU s =
      Submodule.Quotient.mk ⟨(s : X.functionField),
        divisorSections_le_pointLattice K hx D U hxU s.2⟩ :=
  rfl

/-- `jumpProj` depends only on the underlying rational function: two sections (over possibly
different opens both containing `x`) with the same value in `K(X)` project to the same class. -/
lemma jumpProj_eq_of_coe_eq {U V : X.Opens} (hxU : x ∈ U) (hxV : x ∈ V)
    (s : divisorSections K D U) (t : divisorSections K D V)
    (h : (s : X.functionField) = (t : X.functionField)) :
    jumpProj K hx D U hxU s = jumpProj K hx D V hxV t := by
  rw [jumpProj_apply, jumpProj_apply]
  exact congrArg _ (Subtype.ext h)

/-! ## S2: the skyscraper morphism `π : 𝒪(D) ⟶ sky_x J` -/

variable {K}

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X] in
/-- The value of `skyModule x M` over an opposite-indexed open containing `x` is `M`
(opposite-indexed restatement of `skyModule_obj_of_mem`, avoiding `op ∘ unop` friction). -/
lemma skyModule_obj_of_mem' (M : ModuleCat.{u} K) {W : (X.Opens)ᵒᵖ} (h : x ∈ unop W) :
    (skyModule x M).obj.obj W = M :=
  skyModule_obj_of_mem x M h

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X] in
/-- **Sealed skyscraper restriction lemma.** The restriction map of `skyModule x M` between two
opens both containing `x` is the canonical `eqToHom` identification `M → M`. Proved once through
`skyscraperSheaf_obj_map`; downstream code routes through this rather than the raw tower. -/
lemma skyModule_map_eq (M : ModuleCat.{u} K) {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V)
    (hU : x ∈ unop U) (hV : x ∈ unop V) :
    (skyModule x M).obj.map i =
      eqToHom ((skyModule_obj_of_mem' M hU).trans (skyModule_obj_of_mem' M hV).symm) := by
  change (skyscraperSheaf x M).obj.map i = _
  rw [skyscraperSheaf_obj_map]
  exact dif_pos hV

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X] in
/-- Sections of `skyModule x M` over an open avoiding `x` form a subsingleton (terminal). -/
lemma skyModule_obj_subsingleton (M : ModuleCat.{u} K) {V : X.Opens} (hV : x ∉ V) :
    Subsingleton ((skyModule x M).obj.obj (op V)) := by
  rw [skyModule_obj_of_not_mem x M hV]
  exact ModuleCat.subsingleton_of_isZero terminalIsTerminal.isZero

variable (K)

/-- **The component of `π` over an open `W` (opposite-indexed).** On `unop W ∋ x` it is the
quotient projection `jumpProj` (landed in the skyscraper value `M` via the sealed `eqToHom`); on
`unop W ∌ x` it is the zero map into the terminal (zero) sections. -/
noncomputable def skyComponent (W : (X.Opens)ᵒᵖ) :
    (divisorPresheaf K D).obj W ⟶ (skyModule x (jumpModule K hx D)).obj.obj W :=
  if h : x ∈ unop W then
    ModuleCat.ofHom (jumpProj K hx D (unop W) h) ≫
      eqToHom (skyModule_obj_of_mem' (jumpModule K hx D) h).symm
  else 0

lemma skyComponent_of_mem (W : (X.Opens)ᵒᵖ) (hxW : x ∈ unop W) :
    skyComponent K hx D W =
      ModuleCat.ofHom (jumpProj K hx D (unop W) hxW) ≫
        eqToHom (skyModule_obj_of_mem' (jumpModule K hx D) hxW).symm := by
  rw [skyComponent]
  exact dif_pos hxW

/-- Element behaviour of `skyComponent` over `unop W ∋ x`: it is `jumpProj` followed by the
skyscraper `eqToHom` identification. -/
lemma skyComponent_hom_apply_of_mem (W : (X.Opens)ᵒᵖ) (hxW : x ∈ unop W)
    (s : (divisorPresheaf K D).obj W) :
    (skyComponent K hx D W).hom s =
      (eqToHom (skyModule_obj_of_mem' (jumpModule K hx D) hxW).symm).hom
        (jumpProj K hx D (unop W) hxW s) := by
  rw [skyComponent_of_mem K hx D W hxW]
  rfl

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X] in
/-- The skyscraper restriction map, precomposed with the `eqToHom` identification at `U`, is the
`eqToHom` identification at `V` (both opens containing `x`). Sealed consequence of
`skyModule_map_eq`. -/
lemma eqToHom_comp_skyModule_map (M : ModuleCat.{u} K) {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V)
    (hU : x ∈ unop U) (hV : x ∈ unop V) :
    eqToHom (skyModule_obj_of_mem' M hU).symm ≫ (skyModule x M).obj.map i
      = eqToHom (skyModule_obj_of_mem' M hV).symm := by
  rw [skyModule_map_eq M i hU hV, eqToHom_trans]

/-- **The presheaf morphism `π` underlying the skyscraper map.** -/
noncomputable def devissagePresheafπ :
    divisorPresheaf K D ⟶ (skyModule x (jumpModule K hx D)).obj where
  app W := skyComponent K hx D W
  naturality := by
    intro U V i
    by_cases hV : x ∈ unop V
    · have hU : x ∈ unop U := leOfHom i.unop hV
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      change (skyComponent K hx D V).hom (((divisorPresheaf K D).map i).hom s)
        = ((skyModule x (jumpModule K hx D)).obj.map i).hom ((skyComponent K hx D U).hom s)
      rw [skyComponent_hom_apply_of_mem K hx D V hV, skyComponent_hom_apply_of_mem K hx D U hU]
      have hjump : jumpProj K hx D (unop V) hV (((divisorPresheaf K D).map i).hom s)
          = jumpProj K hx D (unop U) hU s := by
        refine jumpProj_eq_of_coe_eq K hx D hV hU _ s ?_
        exact divisorSectionsRes_coe K (leOfHom i.unop) ⟨x, hV⟩ s
      rw [hjump]
      exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (eqToHom_comp_skyModule_map K (jumpModule K hx D) i hU hV))
        (jumpProj K hx D (unop U) hU s)).symm
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      haveI := skyModule_obj_subsingleton (jumpModule K hx D) hV
      exact Subsingleton.elim _ _

/-- **The dévissage skyscraper morphism** `π : 𝒪(D) ⟶ sky_x J` of sheaves of `K`-modules,
sending a section `g` over `U ∋ x` to its class `⟦g⟧` in the jump module (and to `0` away from
`x`). -/
noncomputable def devissageπ :
    divisorSheaf K D ⟶ skyModule x (jumpModule K hx D) :=
  (fullyFaithfulSheafToPresheaf _ _).preimage (devissagePresheafπ K hx D)

lemma devissageπ_hom :
    (devissageπ K hx D).hom = devissagePresheafπ K hx D :=
  (fullyFaithfulSheafToPresheaf _ _).map_preimage
    (X := divisorSheaf K D) (Y := skyModule x (jumpModule K hx D)) (devissagePresheafπ K hx D)

/-- The component of `π` over an open `W` is `skyComponent`. -/
lemma devissageπ_app (W : (X.Opens)ᵒᵖ) :
    (devissageπ K hx D).hom.app W = skyComponent K hx D W := by
  rw [devissageπ_hom]; rfl

/-- **Section behaviour of `π` over `U ∋ x`:** a section `s` of `𝒪(D)` maps to the jump class
`⟦s⟧`, transported into the skyscraper value via the sealed `eqToHom`. -/
lemma devissageπ_app_hom_apply_of_mem (W : (X.Opens)ᵒᵖ) (hxW : x ∈ unop W)
    (s : (divisorPresheaf K D).obj W) :
    ((devissageπ K hx D).hom.app W).hom s =
      (eqToHom (skyModule_obj_of_mem' (jumpModule K hx D) hxW).symm).hom
        (jumpProj K hx D (unop W) hxW s) := by
  rw [← skyComponent_hom_apply_of_mem K hx D W hxW s]
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (devissageπ_app K hx D W)) s

/-! ## S3: the dévissage short exact sequence -/

/-- The divisor `D' = D − x` obtained by subtracting the closed point `x` with multiplicity one. -/
noncomputable def devissageDivisor : X.CurveDivisor :=
  toFinsupp D - Finsupp.single (⟨x, hx⟩ : {p : X // p ≠ genericPoint X}) 1

lemma toFinsupp_devissageDivisor :
    toFinsupp (devissageDivisor hx D) =
      toFinsupp D - Finsupp.single (⟨x, hx⟩ : {p : X // p ≠ genericPoint X}) 1 :=
  rfl

/-- The coefficient of `D − x` at the point `x` is one less than that of `D`. -/
lemma coeffAt_devissageDivisor : coeffAt hx (devissageDivisor hx D) = coeffAt hx D - 1 := by
  change toFinsupp (devissageDivisor hx D) ⟨x, hx⟩ = toFinsupp D ⟨x, hx⟩ - 1
  rw [toFinsupp_devissageDivisor, Finsupp.sub_apply, Finsupp.single_eq_same]

/-- At a point `z ≠ x`, the divisors `D − x` and `D` agree. -/
lemma coeffAt_devissageDivisor_of_ne {z : {p : X // p ≠ genericPoint X}} (hz : z ≠ ⟨x, hx⟩) :
    toFinsupp (devissageDivisor hx D) z = toFinsupp D z := by
  rw [toFinsupp_devissageDivisor, Finsupp.sub_apply, Finsupp.single_eq_of_ne hz, sub_zero]

/-- `D − x ≤ D`: subtracting an effective point divisor decreases the divisor. -/
lemma devissageDivisor_le : devissageDivisor hx D ≤ D := by
  change toFinsupp (devissageDivisor hx D) ≤ toFinsupp D
  rw [toFinsupp_devissageDivisor, Finsupp.le_def]
  intro z
  rw [Finsupp.sub_apply]
  have hnn : (0 : ℤ) ≤ Finsupp.single (⟨x, hx⟩ : {p : X // p ≠ genericPoint X}) 1 z := by
    rw [Finsupp.single_apply]
    split <;> norm_num
  omega

/-- A `D`-section whose pole order at `x` is bounded by `D x − 1` has vanishing jump class. -/
lemma jumpProj_eq_zero_of_mem (W : X.Opens) (hxW : x ∈ W) (t : divisorSections K D W)
    (ht : (t : X.functionField) ∈ pointLattice K hx (coeffAt hx D - 1)) :
    jumpProj K hx D W hxW t = 0 := by
  rw [jumpProj_apply]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ht

/-- Sections of `𝒪(D − x)` over `U ∋ x` land in the tighter lattice `pointLattice (D x − 1)`. -/
lemma coe_mem_pointLattice_of_devissageSection (W : X.Opens) (hxW : x ∈ W)
    (s : divisorSections K (devissageDivisor hx D) W) :
    (s : X.functionField) ∈ pointLattice K hx (coeffAt hx D - 1) := by
  have hne : (W : Set X).Nonempty := ⟨x, hxW⟩
  have hb := (mem_divisorSections_of_nonempty K hne).mp s.2 x hx hxW
  rw [divisorBound_eq_coeffAt, coeffAt_devissageDivisor] at hb
  rw [mem_pointLattice]
  exact hb

lemma divisorSheafLE_hom {D₁ D₂ : X.CurveDivisor} (h : D₁ ≤ D₂) :
    (divisorSheafLE K h).hom = divisorPresheafLE K h :=
  (fullyFaithfulSheafToPresheaf _ _).map_preimage
    (X := divisorSheaf K D₁) (Y := divisorSheaf K D₂) (divisorPresheafLE K h)

lemma divisorSheafLE_app_hom_apply {D₁ D₂ : X.CurveDivisor} (h : D₁ ≤ D₂) (W : (X.Opens)ᵒᵖ)
    (s : (divisorSheaf K D₁).obj.obj W) :
    (((divisorSheafLE K h).hom.app W).hom s).1 = s.1 := by
  rw [divisorSheafLE_hom]
  rfl

lemma skyComponent_of_not_mem (W : (X.Opens)ᵒᵖ) (hxW : x ∉ unop W) :
    skyComponent K hx D W = 0 := by
  rw [skyComponent]; exact dif_neg hxW

/-- **The dévissage complex vanishes:** `𝒪(D − x) ↪ 𝒪(D) → sky_x J` composes to zero — a section
of `𝒪(D − x)` has a strictly smaller pole at `x`, so its jump class is trivial. -/
lemma devissage_comp_eq_zero :
    divisorSheafLE K (devissageDivisor_le hx D) ≫ devissageπ K hx D = 0 := by
  ext W s
  change ((devissageπ K hx D).hom.app W).hom
      (((divisorSheafLE K (devissageDivisor_le hx D)).hom.app W).hom s) = 0
  by_cases hxW : x ∈ unop W
  · have hmem : (((divisorSheafLE K (devissageDivisor_le hx D)).hom.app W).hom s).1
        ∈ pointLattice K hx (coeffAt hx D - 1) := by
      rw [divisorSheafLE_app_hom_apply]
      exact coe_mem_pointLattice_of_devissageSection K hx D (unop W) hxW s
    rw [devissageπ_app_hom_apply_of_mem K hx D W hxW,
      jumpProj_eq_zero_of_mem K hx D (unop W) hxW
        (((divisorSheafLE K (devissageDivisor_le hx D)).hom.app W).hom s) hmem, map_zero]
  · rw [devissageπ_app, skyComponent_of_not_mem K hx D W hxW]
    rfl

/-- **The dévissage short complex** `0 ⟶ 𝒪(D − x) ⟶ 𝒪(D) ⟶ sky_x J ⟶ 0`, as a `ShortComplex`
of sheaves of `K`-modules. -/
noncomputable def devissageSES :
    ShortComplex (Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} K)) :=
  ShortComplex.mk (divisorSheafLE K (devissageDivisor_le hx D)) (devissageπ K hx D)
    (devissage_comp_eq_zero K hx D)

/-- **Left exactness certificate.** The inclusion `𝒪(D − x) ↪ 𝒪(D)` is a monomorphism, so the
dévissage complex is exact at its left term (landed `divisorSheafLE_mono`). -/
instance devissageSES_mono_f : Mono (devissageSES K hx D).f :=
  divisorSheafLE_mono K (devissageDivisor_le hx D)

end AlgebraicGeometry
