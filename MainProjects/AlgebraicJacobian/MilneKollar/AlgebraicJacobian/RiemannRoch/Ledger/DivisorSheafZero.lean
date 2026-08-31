/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.DivisorSheaf

/-!
# The identification `𝒪(0) ≅ 𝒪_X`

For the curve bundle `X` — integral and smooth of relative dimension one over a field `K` — this
file identifies the divisor sheaf of the zero divisor with the structure sheaf, as sheaves of
`K`-modules on the small Zariski site of `X`:

* `AlgebraicGeometry.Scheme.divisorSheafZeroIso : divisorSheaf K 0 ≅ X.moduleKSheaf K`.

This is the keystone making `χ(𝒪(0)) = χ(𝒪)`: `𝒪(0)` is by definition the rational functions with
poles bounded by `0`, i.e. with `ord_x ≤ 1` at every closed point, which is precisely the condition
"integral at `x`". On the irreducible curve `X` a section of the structure sheaf `s : Γ(X, U)` maps
to its germ at the generic point `η`, a rational function that is integral at every closed point of
`U`; conversely a rational function integral on all of `U` is glued from local regular
representatives. The map is an isomorphism on every nonempty open, and both sides are terminal over
the empty open, so it upgrades to an isomorphism of sheaves.

## Design

The section-wise morphism `Γ(X, U) → 𝒪(0)(U)`, `s ↦ germ_η s`, is only meaningful when `η ∈ U`,
i.e. when `U` is nonempty. We seal the empty-open branch behind a `dite`
(`moduleToDivisorZeroPresheafApp`) with a behaviour lemma for the nonempty case; naturality and
bijectivity in the empty case are discharged by subsingleton-ness of both source and target. The
central geometric input is the *germ/stalk seam* `germ_generic_eq_algebraMap_germ`: the germ at `η`
of a section equals the image, under `𝒪_{X,x} → K(X)`, of its germ at any other point `x` of `U`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

namespace Scheme

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]

/-! ### Geometric seams -/

/-- The generic point lies in every nonempty open of the irreducible space `X`. -/
lemma genericPoint_mem_of_nonempty {U : X.Opens} (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff (U := (↑U : Set X)) U.isOpen).mpr (by simpa using hU)

/-- **The germ/stalk seam.** For a section `s : Γ(X, U)` over an open containing both the generic
point `η` and a point `x`, the germ at `η` is the image, along the structure map
`𝒪_{X,x} → K(X)` of the local ring at `x`, of the germ at `x`. This is the identity through which
the local pole bounds `ord_x (germ_η s) ≤ 1` are read off from integrality at `x`. -/
lemma germ_generic_eq_algebraMap_germ {U : X.Opens} (hηU : genericPoint X ∈ U) {x : X}
    (hxU : x ∈ U) (s : Γ(X, U)) :
    (X.presheaf.germ U (genericPoint X) hηU).hom s
      = algebraMap (X.presheaf.stalk x) X.functionField
          ((X.presheaf.germ U x hxU).hom s) := by
  have hspec : genericPoint X ⤳ x := (genericPoint_spec X).specializes (Set.mem_univ x)
  have hcomp := X.presheaf.germ_stalkSpecializes (U := U) (y := x) hxU hspec
  have happ := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) s
  rw [CommRingCat.hom_comp, RingHom.comp_apply] at happ
  exact happ.symm

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] in
/-- The germ at `η` of the image of `r : K` under the structure map `K → Γ(X, U)` is the canonical
image of `r` in the function field `K(X)`; this is the naturality that makes `s ↦ germ_η s`
`K`-linear. -/
lemma germ_generic_overAlgebraMap {U : X.Opens} (hηU : genericPoint X ∈ U) (r : K) :
    (X.presheaf.germ U (genericPoint X) hηU).hom (X.overAlgebraMap K U r)
      = functionFieldOverAlgebraMap K X r := by
  have hres := X.presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) (genericPoint X) hηU
    (X.overAlgebraMap K ⊤ r)
  rw [X.overAlgebraMap_apply_res K (homOfLE (le_top : U ≤ ⊤)).op r] at hres
  rw [hres]
  rfl

/-! ### The section-wise morphism `Γ(X, U) → 𝒪(0)(U)` -/

/-- The `K`-linear map `Γ(X, U) →ₗ[K] K(X)` sending a section to its germ at the generic point,
for an open `U` containing `η`. `K`-linearity uses `germ_generic_overAlgebraMap`. -/
noncomputable def germGenericLinear {U : X.Opens} (hηU : genericPoint X ∈ U) :
    Γ(X, U) →ₗ[K] X.functionField where
  toFun := (X.presheaf.germ U (genericPoint X) hηU).hom
  map_add' := map_add _
  map_smul' r s := by
    simp only [RingHom.id_apply, Scheme.overModule_smul_def, map_mul,
      germ_generic_overAlgebraMap K hηU r, functionFieldOverModule_smul_def]

/-- The germ-at-`η` of a section of `𝒪_X` over a nonempty open has poles bounded by the zero
divisor: it is integral at every closed point, i.e. lies in `𝒪(0)(U) = divisorSections K 0 U`. -/
lemma germGenericLinear_mem {U : X.Opens} (hηU : genericPoint X ∈ U) (s : Γ(X, U)) :
    germGenericLinear K hηU s ∈ divisorSections K 0 U := by
  rw [mem_divisorSections_of_nonempty K ⟨genericPoint X, hηU⟩]
  intro x hx hxU
  rw [divisorBound_zero]
  change Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx
      ((X.presheaf.germ U (genericPoint X) hηU).hom s) ≤ 1
  rw [germ_generic_eq_algebraMap_germ hηU hxU s]
  exact ord_algebraMap_stalk_le_one K hx _

/-- The section-wise morphism `Γ(X, U) → 𝒪(0)(U)`, `s ↦ germ_η s`, for a nonempty open `U`. -/
noncomputable def moduleToDivisorZeroApp {U : X.Opens} (hηU : genericPoint X ∈ U) :
    Γ(X, U) →ₗ[K] divisorSections K 0 U :=
  LinearMap.codRestrict (divisorSections K 0 U) (germGenericLinear K hηU)
    (germGenericLinear_mem K hηU)

/-- The underlying rational function of `moduleToDivisorZeroApp` is the germ at `η`. -/
lemma moduleToDivisorZeroApp_coe {U : X.Opens} (hηU : genericPoint X ∈ U) (s : Γ(X, U)) :
    ((moduleToDivisorZeroApp K hηU s : divisorSections K 0 U) : X.functionField)
      = (X.presheaf.germ U (genericPoint X) hηU).hom s := rfl

open Classical in
/-- The section-wise morphism `Γ(X, U) → 𝒪(0)(U)` for *all* opens: `s ↦ germ_η s` when `U` is
nonempty, and the zero map into the terminal sections when `U` is empty. -/
noncomputable def moduleToDivisorZeroPresheafApp (U : X.Opens) :
    Γ(X, U) →ₗ[K] divisorSections K 0 U :=
  if hU : (U : Set X).Nonempty then moduleToDivisorZeroApp K (genericPoint_mem_of_nonempty hU)
  else 0

/-- On a nonempty open the presheaf component is the germ-at-`η` map. -/
lemma moduleToDivisorZeroPresheafApp_of_nonempty {U : X.Opens} (hU : (U : Set X).Nonempty) :
    moduleToDivisorZeroPresheafApp K U
      = moduleToDivisorZeroApp K (genericPoint_mem_of_nonempty hU) :=
  dif_pos hU

/-- The underlying rational function of the presheaf component over a nonempty open. -/
lemma moduleToDivisorZeroPresheafApp_coe_of_nonempty {U : X.Opens} (hU : (U : Set X).Nonempty)
    (s : Γ(X, U)) :
    ((moduleToDivisorZeroPresheafApp K U s : divisorSections K 0 U) : X.functionField)
      = (X.presheaf.germ U (genericPoint X) (genericPoint_mem_of_nonempty hU)).hom s := by
  rw [moduleToDivisorZeroPresheafApp_of_nonempty K hU]; rfl

/-! ### Surjectivity: gluing local regular representatives -/

/-- **Local representability.** A rational function `g` with poles bounded by the zero divisor on
`U` is, near every point `x ∈ U`, the germ at `η` of a genuine regular section over a neighbourhood
of `x` inside `U`. At `x = η` this is a direct representative; at a closed point `x` the bound
`ord_x g ≤ 1` puts `g` in the image of the stalk `𝒪_{X,x}`, whose representative has the required
germ at `η` via `germ_generic_eq_algebraMap_germ`. -/
lemma exists_local_section {U : X.Opens} (hηU : genericPoint X ∈ U)
    {g : X.functionField} (hg : g ∈ divisorSections K 0 U) {x : X} (hxU : x ∈ U) :
    ∃ (W : X.Opens) (_ : x ∈ W) (_ : W ≤ U) (s : Γ(X, W)) (hηW : genericPoint X ∈ W),
      (X.presheaf.germ W (genericPoint X) hηW).hom s = g := by
  by_cases hx : x = genericPoint X
  · obtain ⟨W₀, hηW₀, s₀, hs₀⟩ := X.presheaf.exists_germ_eq (x := genericPoint X) g
    have hxW : x ∈ W₀ ⊓ U := hx ▸ ⟨hηW₀, hηU⟩
    have hηW : genericPoint X ∈ W₀ ⊓ U := ⟨hηW₀, hηU⟩
    refine ⟨W₀ ⊓ U, hxW, inf_le_right,
      (X.presheaf.map (homOfLE (inf_le_left : W₀ ⊓ U ≤ W₀)).op).hom s₀, hηW, ?_⟩
    rw [X.presheaf.germ_res_apply (homOfLE (inf_le_left : W₀ ⊓ U ≤ W₀)) (genericPoint X) hηW s₀]
    exact hs₀
  · have hord : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g ≤ 1 := by
      have hmem := (mem_divisorSections_of_nonempty K ⟨genericPoint X, hηU⟩).mp hg x hx hxU
      rwa [divisorBound_zero] at hmem
    obtain ⟨y, hy⟩ := exists_stalk_of_ord_le_one K hx hord
    obtain ⟨W₀, hxW₀, s₀, hs₀⟩ := X.presheaf.exists_germ_eq (x := x) y
    have hxW : x ∈ W₀ ⊓ U := ⟨hxW₀, hxU⟩
    have hηW : genericPoint X ∈ W₀ ⊓ U := genericPoint_mem_of_nonempty ⟨x, hxW⟩
    refine ⟨W₀ ⊓ U, hxW, inf_le_right,
      (X.presheaf.map (homOfLE (inf_le_left : W₀ ⊓ U ≤ W₀)).op).hom s₀, hηW, ?_⟩
    rw [germ_generic_eq_algebraMap_germ hηW hxW,
      X.presheaf.germ_res_apply (homOfLE (inf_le_left : W₀ ⊓ U ≤ W₀)) x hxW s₀, hs₀]
    exact hy

/-- **Surjectivity of `s ↦ germ_η s`.** Every rational function with poles bounded by the zero
divisor on a nonempty open `U` is the germ at `η` of a section of `𝒪_X` over `U`, obtained by
gluing the local regular representatives of `exists_local_section`. -/
lemma exists_section_germ_eq {U : X.Opens} (hηU : genericPoint X ∈ U)
    {g : X.functionField} (hg : g ∈ divisorSections K 0 U) :
    ∃ s : Γ(X, U), (X.presheaf.germ U (genericPoint X) hηU).hom s = g := by
  choose W hxW hWU s hηW hs using
    fun p : ↥U => exists_local_section K hηU hg (x := p.1) p.2
  have hcover : U ≤ ⨆ p, W p := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj W s := by
    intro p q
    have hη : genericPoint X ∈ W p ⊓ W q := ⟨hηW p, hηW q⟩
    apply germ_injective_of_isIntegral X (genericPoint X) hη
    change (X.presheaf.germ (W p ⊓ W q) (genericPoint X) hη).hom
          ((X.presheaf.map (Opens.infLELeft (W p) (W q)).op).hom (s p))
        = (X.presheaf.germ (W p ⊓ W q) (genericPoint X) hη).hom
          ((X.presheaf.map (Opens.infLERight (W p) (W q)).op).hom (s q))
    rw [X.presheaf.germ_res_apply (Opens.infLELeft (W p) (W q)) (genericPoint X) hη (s p),
      X.presheaf.germ_res_apply (Opens.infLERight (W p) (W q)) (genericPoint X) hη (s q),
      hs p, hs q]
  obtain ⟨sU, hsU, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf W U
    (fun p => homOfLE (hWU p)) hcover s hcompat
  refine ⟨sU, ?_⟩
  set p₀ : ↥U := ⟨genericPoint X, hηU⟩ with hp₀
  have hsU' : (X.presheaf.map (homOfLE (hWU p₀)).op).hom sU = s p₀ := hsU p₀
  have key := X.presheaf.germ_res_apply (homOfLE (hWU p₀)) (genericPoint X) (hηW p₀) sU
  have heq : (X.presheaf.germ U (genericPoint X) hηU).hom sU
      = (X.presheaf.germ (W p₀) (genericPoint X) (hηW p₀)).hom (s p₀) := by
    rw [← hsU']; exact key.symm
  rw [heq]; exact hs p₀

/-! ### Bijectivity and the isomorphism of sheaves -/

/-- The section-wise morphism is injective on a nonempty open: two sections with the same germ at
`η` agree, since `X` is integral. -/
lemma moduleToDivisorZeroApp_injective {U : X.Opens} (hηU : genericPoint X ∈ U) :
    Function.Injective (moduleToDivisorZeroApp K hηU) := by
  intro a b hab
  apply germ_injective_of_isIntegral X (genericPoint X) hηU
  exact Subtype.ext_iff.mp hab

/-- The section-wise morphism is surjective on a nonempty open (by `exists_section_germ_eq`). -/
lemma moduleToDivisorZeroApp_surjective {U : X.Opens} (hηU : genericPoint X ∈ U) :
    Function.Surjective (moduleToDivisorZeroApp K hηU) := by
  intro t
  obtain ⟨s, hs⟩ := exists_section_germ_eq K hηU t.2
  exact ⟨s, Subtype.ext hs⟩

/-- The presheaf component `Γ(X, U) → 𝒪(0)(U)` is bijective for every open `U`: an isomorphism on
nonempty opens, and a map of subsingletons (both sides terminal) on the empty open. -/
lemma moduleToDivisorZeroPresheafApp_bijective (U : X.Opens) :
    Function.Bijective (moduleToDivisorZeroPresheafApp K U) := by
  by_cases hU : (U : Set X).Nonempty
  · rw [moduleToDivisorZeroPresheafApp_of_nonempty K hU]
    exact ⟨moduleToDivisorZeroApp_injective K _, moduleToDivisorZeroApp_surjective K _⟩
  · have hbot : U = ⊥ := by
      apply Opens.ext
      rw [Set.not_nonempty_iff_eq_empty.mp hU, Opens.coe_bot]
    haveI hsub_dom : Subsingleton Γ(X, U) := by rw [hbot]; infer_instance
    haveI hsub_cod : Subsingleton (divisorSections K 0 U) :=
      divisorSections_subsingleton_of_empty K hU
    exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-- **The presheaf morphism `𝒪_X → 𝒪(0)`** of `K`-modules, section-wise `s ↦ germ_η s`. -/
noncomputable def moduleToDivisorZeroPresheaf :
    X.moduleKPresheaf K ⟶ divisorPresheaf K 0 where
  app U := ModuleCat.ofHom (moduleToDivisorZeroPresheafApp K U.unop)
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    by_cases hV : (V.unop : Set X).Nonempty
    · have hU : (U.unop : Set X).Nonempty := hV.mono (leOfHom i.unop)
      apply Subtype.ext
      change ((moduleToDivisorZeroPresheafApp K V.unop ((X.presheaf.map i).hom s) :
              divisorSections K 0 V.unop) : X.functionField)
          = ((divisorSectionsRes K 0 (leOfHom i.unop)
              (moduleToDivisorZeroPresheafApp K U.unop s) : divisorSections K 0 V.unop) :
              X.functionField)
      rw [moduleToDivisorZeroPresheafApp_coe_of_nonempty K hV,
        divisorSectionsRes_coe K (leOfHom i.unop) hV,
        moduleToDivisorZeroPresheafApp_coe_of_nonempty K hU]
      have hgr := X.presheaf.germ_res_apply i.unop (genericPoint X)
        (genericPoint_mem_of_nonempty hV) s
      simpa using hgr
    · haveI := divisorPresheaf_obj_subsingleton K (D := 0) (W := V.unop) hV
      exact Subsingleton.elim _ _

/-- Every component of `moduleToDivisorZeroPresheaf` is an isomorphism. -/
lemma moduleToDivisorZeroPresheaf_app_isIso (U : (X.Opens)ᵒᵖ) :
    IsIso ((moduleToDivisorZeroPresheaf K).app U) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact moduleToDivisorZeroPresheafApp_bijective K U.unop

/-- **The presheaf isomorphism `𝒪_X ≅ 𝒪(0)`** of `K`-modules. -/
noncomputable def moduleToDivisorZeroPresheafIso :
    X.moduleKPresheaf K ≅ divisorPresheaf K 0 :=
  NatIso.ofComponents
    (fun U => by
      haveI := moduleToDivisorZeroPresheaf_app_isIso K U
      exact asIso ((moduleToDivisorZeroPresheaf K).app U))
    (fun i => (moduleToDivisorZeroPresheaf K).naturality i)

/-- **The isomorphism of sheaves `𝒪_X ≅ 𝒪(0)`** of `K`-modules, from the presheaf isomorphism via
the fully faithful `sheafToPresheaf`. -/
noncomputable def moduleKSheafDivisorSheafZeroIso :
    X.moduleKSheaf K ≅ divisorSheaf K 0 :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (moduleToDivisorZeroPresheafIso K)

/-- **The anchor isomorphism `𝒪(0) ≅ 𝒪_X`**: the divisor sheaf of the zero divisor is the
structure sheaf of `X` as a sheaf of `K`-modules. This is the keystone identifying
`χ(𝒪(0))` with `χ(𝒪)`. -/
noncomputable def divisorSheafZeroIso :
    divisorSheaf K (0 : X.CurveDivisor) ≅ X.moduleKSheaf K :=
  (moduleKSheafDivisorSheafZeroIso K).symm

end Scheme

end AlgebraicGeometry
