/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Std.Tactic.BVDecide.LRAT.Internal.Clause
import AlgebraicJacobian.Cohomology.OpenImmersionPushforward
import AlgebraicJacobian.Cohomology.AcyclicResolution
import AlgebraicJacobian.Cohomology.CechSectionIdentificationBase

/-! # Čech term acyclicity for the pushforward

## Separatedness of the base

The conclusion of `cechTerm_pushforward_acyclic` is false without a hypothesis on `S`.
For a counterexample, let `S` be the affine plane with a doubled origin,
`X = 𝔸²` and `f : X ⟶ S` the open immersion onto the first copy (an open immersion is separated,
and `f` is quasi-compact since everything is noetherian); `X` is affine and separated, so the
one-element cover `𝒰 = {𝟙 X}` is a finite affine cover.  Every Čech term is then isomorphic to
`F`, so the claimed conclusion specializes to `R^k f_* F = 0` for `k ≥ 1` — but for `F = O_X`
the stalk of `R^1 f_* O_X` at the doubled origin `o₂` is
`colim_{W ∋ 0} H^1(W \ {0}, O) ≅ H²_𝔪(A) ≠ 0` (`A` the local ring of the plane at the origin).
For affine `U ⊆ X` and affine `V ⊆ S`,
`U ∩ f⁻¹(V) ≅ U ×_S V` is affine only when the *diagonal of `S`* is affine (e.g. `S`
separated); `f` separated does not suffice. The lemma therefore assumes `[S.IsSeparated]`
(what is really used is that `S` has affine diagonal, so any
morphism from an affine scheme to `S` is affine).  The same hypothesis is consequently REQUIRED
by the capstone `cech_computes_higherDirectImage` (same counterexample: the Čech
complex of the trivial cover is `f_* F` in degree 0, with vanishing `H^1`, while
`R^1 f_* F ≠ 0`).

In addition, the proof must pass through the category of modules on the intersection schemes
`U_σ = (coverInterOpen 𝒰 σ).toScheme`, whose `HasInjectiveResolutions` instance is NOT available
in Mathlib (`IsGrothendieckAbelian (SheafOfModules R)` is absent — see CechToCohomology.lean);
exactly as the frozen target carries `[HasInjectiveResolutions X.Modules]` as a hypothesis, this
lemma carries the corresponding hypothesis `hres` for the (finitely many) intersection opens. -/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.Modules

variable {X S : Scheme.{u}}

/-! ## Auxiliary: additivity of the right-derived functor

Mathlib defines `Functor.rightDerived` but registers no `Additive` instance for it (nor for
`injectiveResolutions`).  We supply both here: two descents of `f + g` between chosen injective
resolutions are homotopic, so in the homotopy category the descent of a sum is the sum of the
descents; additivity of the right-derived functor follows by composition. -/

section RightDerivedAdditive

variable {𝒜 ℬ : Type*} [Category 𝒜] [Abelian 𝒜] [HasInjectiveResolutions 𝒜]
  [Category ℬ] [Abelian ℬ]

/-- The chosen-injective-resolutions functor `𝒜 ⥤ HomotopyCategory 𝒜` is additive: `desc f +
desc g` is also a descent of `f + g`, and any two descents are homotopic
(`InjectiveResolution.descHomotopy`). Project-local Mathlib supplement. -/
instance injectiveResolutions_additive : (injectiveResolutions 𝒜).Additive where
  map_add {Z W f g} := by
    dsimp only [injectiveResolutions]
    refine Eq.trans ?_ ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℕ)).map_add
      (f := InjectiveResolution.desc f (injectiveResolution W) (injectiveResolution Z))
      (g := InjectiveResolution.desc g (injectiveResolution W) (injectiveResolution Z)))
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descHomotopy (f + g)
    · exact InjectiveResolution.desc_commutes _ _ _
    · rw [Preadditive.comp_add, InjectiveResolution.desc_commutes,
        InjectiveResolution.desc_commutes, ← Preadditive.add_comp, ← Functor.map_add]

/-- The right-derived functor of an additive functor is additive (composite of the additive
`injectiveResolutions`, `mapHomotopyCategory` and homotopy-category homology functors).
Project-local Mathlib supplement. -/
lemma rightDerived_additive (G : 𝒜 ⥤ ℬ) [G.Additive] (n : ℕ) : (G.rightDerived n).Additive :=
  letI : G.rightDerivedToHomotopyCategory.Additive :=
    inferInstanceAs (injectiveResolutions 𝒜 ⋙
      G.mapHomotopyCategory (ComplexShape.up ℕ)).Additive
  inferInstanceAs (G.rightDerivedToHomotopyCategory ⋙
    HomotopyCategory.homologyFunctor ℬ (ComplexShape.up ℕ) n).Additive

/-- A biproduct of zero objects is zero: the identity equals zero because every component map
into a zero object is unique. Project-local helper. -/
lemma isZero_biproduct {C : Type*} [Category C] [HasZeroMorphisms C] {J : Type*}
    (Z : J → C) [HasBiproduct Z] (h : ∀ j, IsZero (Z j)) : IsZero (⨁ Z) := by
  rw [IsZero.iff_id_eq_zero]
  apply biproduct.hom_ext
  intro j
  exact (h j).eq_of_tgt _ _

/-- Right-`G`-acyclicity transports along an isomorphism. Project-local helper. -/
lemma isRightAcyclic_of_iso (G : 𝒜 ⥤ ℬ) [G.Additive] {A B : 𝒜} (e : A ≅ B)
    [G.IsRightAcyclic A] : G.IsRightAcyclic B where
  vanish k := (Functor.IsRightAcyclic.vanish (G := G) (J := A) k).of_iso
    ((G.rightDerived (k + 1)).mapIso e).symm

end RightDerivedAdditive

/-! ## Auxiliary: finite products of acyclic objects -/

/- Planner strategy: lem:rightAcyclic_finite_prod ·
A finite categorical product (= finite biproduct in an abelian category) of right-G-acyclic
objects is right-G-acyclic.  Since `G.rightDerived (k+1)` is additive it preserves finite
biproducts; each factor `(G.rightDerived (k+1)).obj (X i)` is zero by the per-factor acyclicity
instance, so their finite product/biproduct is zero.
Proof route: `Functor.IsRightAcyclic.vanish` on the product reduces to
`IsZero (∏ᶜ i, (G.rightDerived (k+1)).obj (X i))` (additive right-derived preserves ∏ᶜ), then
each factor is zero by `Functor.IsRightAcyclic.vanish i`, and a finite product of zero objects is
zero (`IsZero.prod` / `Limits.IsZero.pi`). -/
/-- **A finite product of right-`G`-acyclic objects is right-`G`-acyclic**
(blueprint `lem:rightAcyclic_finite_prod`).

Let `G : 𝒜 ⥤ ℬ` be an additive functor between abelian categories with injective resolutions,
and let `(X i)_{i : ι}` be a finite family of objects each right `G`-acyclic.  Then the
categorical product `∏ᶜ i, X i` is also right `G`-acyclic. -/
lemma rightAcyclic_finite_prod
    {𝒜 ℬ : Type*} [Category 𝒜] [Abelian 𝒜] [HasInjectiveResolutions 𝒜]
    [HasFiniteProducts 𝒜] [Category ℬ] [Abelian ℬ]
    (G : 𝒜 ⥤ ℬ) [G.Additive] {ι : Type*} [Finite ι]
    (Xf : ι → 𝒜) [∀ i, G.IsRightAcyclic (Xf i)] :
    G.IsRightAcyclic (∏ᶜ fun i => Xf i) := by
  constructor
  intro k
  haveI : (G.rightDerived (k + 1)).Additive := rightDerived_additive G (k + 1)
  -- Finite biproducts in abelian categories (a `local instance` in Mathlib, not global).
  haveI : HasFiniteBiproducts 𝒜 := Abelian.hasFiniteBiproducts
  haveI : HasFiniteBiproducts ℬ := Abelian.hasFiniteBiproducts
  -- Reindex along an equivalence `ι ≃ Fin n` so the `Type 0` finite-biproduct instances apply.
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  haveI : ∀ j : Fin n, G.IsRightAcyclic ((Xf ∘ e.symm) j) :=
    fun j => inferInstanceAs (G.IsRightAcyclic (Xf (e.symm j)))
  -- `∏ᶜ Xf ≅ ∏ᶜ (Xf ∘ e.symm) ≅ ⨁ (Xf ∘ e.symm)`, and the additive right-derived functor
  -- takes the biproduct to the biproduct of the (vanishing) per-factor values.
  refine IsZero.of_iso ?_
    ((G.rightDerived (k + 1)).mapIso
      (Pi.whiskerEquiv (f := fun i => Xf i) (g := Xf ∘ e.symm) e
          (fun i => eqToIso (congrArg Xf (e.symm_apply_apply i))) ≪≫
        (biproduct.isoProduct (Xf ∘ e.symm)).symm) ≪≫
      (G.rightDerived (k + 1)).mapBiproduct (Xf ∘ e.symm))
  exact isZero_biproduct _ fun j =>
    Functor.IsRightAcyclic.vanish (G := G) (J := (Xf ∘ e.symm) j) k

/-! ## Auxiliary: a morphism from an affine scheme to a separated scheme is affine -/

/-- **A morphism from an affine scheme to a separated scheme is affine** (Stacks 01S7).
`g ≫ terminal.from S = terminal.from U` is affine because `U` is affine, and `terminal.from S`
is separated, so the cancellation property of affine morphisms applies. Project-local (the
identical statement exists as a `private` lemma in `OpenImmersionPushforward.lean`). -/
lemma isAffineHom_of_isAffine_of_isSeparated {U Z : Scheme.{u}} (g : U ⟶ Z)
    [IsAffine U] [Z.IsSeparated] : IsAffineHom g := by
  haveI hcomp : IsAffineHom (g ≫ terminal.from Z) := by
    have he : g ≫ terminal.from Z = terminal.from U := terminal.hom_ext _ _
    rw [he]; infer_instance
  exact IsAffineHom.of_comp g (terminal.from Z)

/-! ## Relative Serre vanishing for an affine morphism from an affine scheme

This is the generalization of `higherDirectImage_openImmersion_acyclic` from affine open
immersions into a separated scheme to arbitrary affine morphisms from an affine scheme: the
open-immersion hypothesis was only used there to derive `IsAffineHom j`, so we take the latter
as the hypothesis.  The proof is the same Stacks 01XJ + Serre-vanishing argument: `R^q j_* H`
is the sheafification of `V ↦ H^q(j⁻¹V, H)`, which dies sectionwise on the affine basis since
`j⁻¹V` is affine for affine `V`. -/

-- Re-activate the (file-local) `HasExt` instance from `AbsoluteCohomology.lean` (same pattern
-- as `OpenImmersionPushforward.lean:111`) so the `Ext`-based transport below resolves it without
-- the slow `HasSmallLocalizedHom` search (which exceeds even a 1000000-heartbeat budget).
attribute [local instance] hasExtModules

section AffineHomAcyclic

variable {U Z : Scheme.{u}}

set_option synthInstance.maxHeartbeats 1000000 in
-- The Ext/sheafification transport expands localized-hom and affine-basis instances.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
/-- **Higher direct images along an affine morphism from an affine scheme vanish**
(Stacks `lemma-relative-affine-vanishing`, project-local generalization of
`higherDirectImage_openImmersion_acyclic` from open immersions to affine morphisms). -/
theorem higherDirectImage_affineHom_acyclic [HasInjectiveResolutions U.Modules]
    (j : U ⟶ Z) [IsAffineHom j] [IsAffine U]
    (H : U.Modules) (hH : H.IsQuasicoherent) (q : ℕ) (hq : 0 < q) :
    IsZero (higherDirectImage j q H) := by
  -- Presheaf description (Stacks 01XJ): `Rᵠ j_* H ≅ sheafify(V ↦ Hᵠ((j_* I•)(V)))`
  -- for any injective resolution `I` of `H`. Reduce to the vanishing of that sheafification.
  refine IsZero.of_iso ?_
    (higherDirectImage_iso_sheafify_presheafHomology j q (injectiveResolution H))
  set α : Z.ringCatSheaf.obj ⟶ Z.ringCatSheaf.obj := 𝟙 Z.ringCatSheaf.obj with hα
  set P := (pushforwardResolutionPresheafComplex j (injectiveResolution H)).homology q with hP
  -- Reflect `IsZero` through the faithful, zero-preserving forgetful functor `toSheaf`.
  apply Functor.isZero_of_faithful_preservesZeroMorphisms (SheafOfModules.toSheaf Z.ringCatSheaf)
  -- Transport across the sheafification square
  -- `toSheaf ∘ sheafification ≅ presheafToSheaf ∘ toPresheaf`.
  refine IsZero.of_iso ?_ ((PresheafOfModules.sheafificationCompToSheaf α).app P)
  set Q := (PresheafOfModules.toPresheaf Z.ringCatSheaf.obj).obj P with hQ
  -- KEY VANISHING: the presheaf homology `Q` is a *zero object* over every affine open
  -- `W ⊆ Z`, because `j⁻¹W` is affine (`j` is an affine morphism) and Serre vanishing
  -- (via the `Ext`-transport to the spectrum) kills `Hᵠ(j⁻¹W, H)` for `q ≥ 1`.
  have hSec : ∀ (W : TopologicalSpace.Opens Z), IsAffineOpen W →
      IsZero (Q.obj (Opposite.op W)) := by
    intro W hW
    -- Evaluate-at-`W` the presheaf complex; this functor preserves homology, so
    -- `Q.obj (op W) ≅ Hᵠ(Γ(W, j_* I•)) = Hᵠ(j⁻¹W, H)`, which vanishes for affine `j⁻¹W`.
    set GW := PresheafOfModules.toPresheaf Z.ringCatSheaf.obj ⋙
      (evaluation (TopologicalSpace.Opens Z)ᵒᵖ AddCommGrpCat).obj (Opposite.op W) with hGW
    set Kp := pushforwardResolutionPresheafComplex j (injectiveResolution H) with hKp
    refine IsZero.of_iso ?_ (GW.mapHomologyIso' (ComplexShape.up ℕ) Kp q).symm
    -- The section complex `n ↦ Γ(W, j_* I^n) = Γ(j⁻¹W, I^n)` is the image of the chosen
    -- injective resolution of `H` under the additive sections-over-`j⁻¹W` functor.
    have hcomplex : (GW.mapHomologicalComplex (ComplexShape.up ℕ)).obj Kp
        = ((pushforwardSectionsFunctor j W).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution H).cocomplex :=
      rfl
    rw [hcomplex]
    -- `isoRightDerivedObj` recognises this homology as the `q`-th right derived sections
    -- functor `Rᵠ Γ(j⁻¹W, -)` applied to `H`, i.e. the absolute cohomology `Hᵠ(j⁻¹W, H)`.
    refine IsZero.of_iso ?_ ((injectiveResolution H).isoRightDerivedObj
      (pushforwardSectionsFunctor j W) q).symm
    -- The sections functor `Γ(j⁻¹W, -)` is corepresented by `jShriekOU (j ⁻¹ᵁ W)`, so its
    -- `q`-th right derived functor agrees with that of `Hom(jShriekOU (j ⁻¹ᵁ W), -)`.
    refine IsZero.of_iso ?_ ((rightDerivedNatIso (sectionsFunctorCorepIso (j ⁻¹ᵁ W)) q).app H)
    -- `isZero_coyoneda_rightDerived_of_forall_ext_eq_zero` reduces the right-derived vanishing
    -- of `Hom(jShriekOU (j⁻¹W), -)` to the `Ext`-vanishing.
    refine isZero_coyoneda_rightDerived_of_forall_ext_eq_zero (jShriekOU (j ⁻¹ᵁ W)) H q hq ?_
    intro e
    -- Discharged by `ext_jShriekOU_eq_zero_of_specIso` (the spectrum `Ext`-transport).
    refine ext_jShriekOU_eq_zero_of_specIso U U.isoSpec (j ⁻¹ᵁ W) H q hq
      (U.isoSpec.inv ⁻¹ᵁ (j ⁻¹ᵁ W)) ?hV' ?hjt ?hqc e
    -- `j⁻¹W` is affine (`j` is an affine morphism, `W` affine), and its preimage along the
    -- iso `U.isoSpec.inv` is affine.
    case hV' => exact (hW.preimage j).preimage_of_isIso U.isoSpec.inv
    case hjt => exact jShriekOU_transport_along_iso U.isoSpec (j ⁻¹ᵁ W)
    case hqc => exact pushforward_iso_preserves_qcoh U.isoSpec H hH
  -- Since affine opens form a basis of `Z`, every section of `Q` restricts to `0` on the
  -- affine opens contained in its domain, so `Q` is sectionwise locally zero and its
  -- sheafification vanishes.
  apply CategoryTheory.GrothendieckTopology.isZero_presheafToSheaf_of_sections_locally_zero
    (Opens.grothendieckTopology Z) (Q := Q)
  intro V s
  refine ⟨{ arrows := fun {W'} _ => ∃ W : TopologicalSpace.Opens Z,
              IsAffineOpen W ∧ W' ≤ W ∧ W ≤ V,
            downward_closed := ?_ }, ?_, ?_⟩
  · rintro W' W'' g ⟨A, hA, hWA, hAV⟩ h
    exact ⟨A, hA, le_trans (leOfHom h) hWA, hAV⟩
  · -- membership in the opens topology: every point of `V` has an affine basis neighbourhood
    intro x hx
    obtain ⟨W, hWmem, hxW, hWV⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Z)) hx
    exact ⟨W, homOfLE hWV, ⟨W, hWmem, le_refl W, hWV⟩, hxW⟩
  · -- the restriction of `s` to a sieve member `W' ≤ A ≤ V` (with `A` affine) factors through
    -- `Q.obj (op A) = 0`, hence vanishes.
    rintro W' g ⟨A, hA, hWA, hAV⟩
    haveI : Subsingleton (ToType (Q.obj (Opposite.op A))) :=
      AddCommGrpCat.subsingleton_of_isZero (hSec A hA)
    have hgfac : g.op = (homOfLE hAV).op ≫ (homOfLE hWA).op := by
      rw [← op_comp]; congr 1
    rw [hgfac, Q.map_comp, ConcreteCategory.comp_apply,
      Subsingleton.elim ((ConcreteCategory.hom (Q.map (homOfLE hAV).op)) s) 0, map_zero]

end AffineHomAcyclic

/-! ## Affineness of the intersection opens of an affine cover of a separated scheme -/

/-- A finite (nonempty-indexed) infimum of affine opens of a separated scheme is affine.
Induction on the index bound via `IsAffineOpen.inf` (which needs the affine diagonal of `X`,
available since `X` is separated). Project-local helper. -/
private lemma isAffineOpen_iInf_fin [X.IsSeparated] :
    ∀ (p : ℕ) (W : Fin (p + 1) → X.Opens), (∀ k, IsAffineOpen (W k)) →
      IsAffineOpen (⨅ k, W k) := by
  haveI : IsClosedImmersion (pullback.diagonal (terminal.from X)) :=
    IsSeparated.isClosedImmersion_diagonal
  intro p
  induction p with
  | zero =>
    intro W hW
    have heq : (⨅ k, W k) = W 0 :=
      le_antisymm (iInf_le _ 0) (le_iInf fun k =>
        le_of_eq (congrArg W (Fin.ext (Nat.lt_one_iff.mp k.isLt)).symm))
    rw [heq]; exact hW 0
  | succ p ih =>
    intro W hW
    have hsplit : (⨅ k, W k) = W 0 ⊓ ⨅ k : Fin (p + 1), W k.succ := by
      refine le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun k => iInf_le _ k.succ))
        (le_iInf fun k => ?_)
      rcases Fin.eq_zero_or_eq_succ k with hk | ⟨j, hj⟩
      · subst hk; exact inf_le_left
      · subst hj; exact inf_le_of_right_le (iInf_le _ j)
    rw [hsplit]
    exact (hW 0).inf (ih (fun k => W k.succ) (fun k => hW k.succ))

/-- The intersection open `U_σ = U_{σ 0} ∩ ⋯ ∩ U_{σ p}` of an affine open cover of a separated
scheme is affine. Project-local helper for `cechTerm_pushforward_acyclic`. -/
lemma isAffineOpen_coverInterOpen [X.IsSeparated] (𝒰 : X.OpenCover)
    (h𝒰 : ∀ i, IsAffine (𝒰.X i)) {p : ℕ} (σ : Fin (p + 1) → 𝒰.I₀) :
    IsAffineOpen (coverInterOpen 𝒰 σ) := by
  have hco : ∀ i, IsAffineOpen (coverOpen 𝒰 i) := by
    intro i
    haveI : IsAffine (𝒰.X i) := h𝒰 i
    exact isAffineOpen_opensRange (𝒰.f i)
  exact isAffineOpen_iInf_fin p (fun k => coverOpen 𝒰 (σ k)) (fun k => hco (σ k))

/-! ## Quasi-coherence of the restriction to an open subscheme

The general-opens restrict–over bridge: the port of the `QcohRestrictBasicOpen.lean` Route-B
bridge (B2–B4) from the basic opens `D(g) ⊆ Spec R` to an arbitrary open `W` of an arbitrary
scheme.  Every proof in that file is generic in the open; we re-instantiate them here (that
file is outside this lane's write domain).  The continuity instances
`Opens.overEquivalence_functor_isContinuous` / `_inverse_isContinuous` are already general
(any topological space) and are imported from there. -/

section RestrictOverBridge

open TopologicalSpace

variable (W : X.Opens)

/-- The image under `W.ι` of the `overEquivalence`-transport of `V' : Over W` is `V'.left`
(general-opens port of `specBasicOpen_ι_image_overEquivalence_functor`). -/
private lemma opens_ι_image_overEquivalence_functor (V' : Over W) :
    W.ι ''ᵁ (Opens.overEquivalence W).functor.obj V' = V'.left := by
  apply Opens.ext
  exact Set.image_preimage_eq_of_subset (fun x hx => ⟨⟨x, leOfHom V'.hom hx⟩, rfl⟩)

/-- Continuity of `overEquivalence.functor` phrased for the open-subscheme carrier
(general-opens port of `overEquivalence_functor_isContinuous_toScheme`). -/
instance overEquivalence_functor_isContinuous_opens :
    (Opens.overEquivalence W).functor.IsContinuous
      ((Opens.grothendieckTopology ↥X).over W)
      (Opens.grothendieckTopology ↥W.toScheme) :=
  Opens.overEquivalence_functor_isContinuous W

/-- Continuity of `overEquivalence.inverse` phrased for the open-subscheme carrier. -/
instance overEquivalence_inverse_isContinuous_opens :
    (Opens.overEquivalence W).inverse.IsContinuous
      (Opens.grothendieckTopology ↥W.toScheme)
      ((Opens.grothendieckTopology ↥X).over W) :=
  Opens.overEquivalence_inverse_isContinuous W

/-- The forgetful functor `Over W ⥤ Opens X` agrees with the over-site equivalence followed by
the open-immersion `opensFunctor` (general-opens port of `overForgetIso`). -/
noncomputable def overOpensForgetIso :
    Over.forget W ≅ (Opens.overEquivalence W).functor ⋙ W.ι.opensFunctor :=
  NatIso.ofComponents
    (fun V' => eqToIso (opens_ι_image_overEquivalence_functor W V').symm)
    (fun {_ _} _ => Subsingleton.elim _ _)

/-- The structure-sheaf comparison `φ` feeding `pushforwardPushforwardEquivalence`
(general-opens port of `overBasicOpenRingHom`). -/
noncomputable def overOpensRingHom :
    Sheaf.over X.ringCatSheaf W ⟶
      ((Opens.overEquivalence W).functor.sheafPushforwardContinuous RingCat
        ((Opens.grothendieckTopology ↥X).over W)
        (Opens.grothendieckTopology ↥W.toScheme)).obj
      W.toScheme.ringCatSheaf :=
  ⟨Functor.whiskerRight (NatTrans.op (overOpensForgetIso W).inv) X.ringCatSheaf.obj⟩

/-- The inverse over-site equivalence followed by `Over.forget` is definitionally the
open-immersion `opensFunctor` (general-opens port of `overForgetInvIso`). -/
noncomputable def overOpensForgetInvIso :
    (Opens.overEquivalence W).inverse ⋙ Over.forget W ≅ W.ι.opensFunctor :=
  Iso.refl _

/-- The reverse structure-sheaf comparison `ψ` (general-opens port of
`overBasicOpenRingInvHom`). -/
noncomputable def overOpensRingInvHom :
    W.toScheme.ringCatSheaf ⟶
      ((Opens.overEquivalence W).inverse.sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology ↥W.toScheme)
        ((Opens.grothendieckTopology ↥X).over W)).obj
      (Sheaf.over X.ringCatSheaf W) :=
  ⟨Functor.whiskerRight (NatTrans.op (overOpensForgetInvIso W).inv) X.ringCatSheaf.obj⟩

/-- **The general-opens restrict–over bridge engine** (port of
`modulesOverBasicOpenEquivalence`): the equivalence between modules on the open subscheme
`W.toScheme` and sheaves of modules on the over-site `X.ringCatSheaf.over W`. -/
noncomputable def modulesOverOpensEquivalence :
    W.toScheme.Modules ≌ SheafOfModules.{u} (X.ringCatSheaf.over W) :=
  SheafOfModules.pushforwardPushforwardEquivalence (Opens.overEquivalence W)
    (overOpensRingHom W) (overOpensRingInvHom W)
    (by
      refine NatTrans.ext (funext fun (V' : (Opens ↥W)ᵒᵖ) => ?_)
      simp only [overOpensRingHom, overOpensRingInvHom, NatTrans.comp_app,
        Functor.whiskerRight_app, NatTrans.op_app, Functor.whiskerLeft_app]
      erw [← Functor.map_comp]
      exact congrArg X.ringCatSheaf.obj.map (Subsingleton.elim _ _))
    (by
      refine NatTrans.ext (funext fun (V' : (Over W)ᵒᵖ) => ?_)
      simp only [overOpensRingHom, overOpensRingInvHom, NatTrans.comp_app,
        Functor.whiskerRight_app, NatTrans.op_app, Functor.whiskerLeft_app,
        NatTrans.id_app, overOpensForgetInvIso, Iso.refl_inv]
      erw [← Functor.map_comp, ← Functor.map_comp]
      exact (congrArg X.ringCatSheaf.obj.map (Subsingleton.elim _ (𝟙 _))).trans
        (X.ringCatSheaf.obj.map_id _))

set_option backward.isDefEq.respectTransparency false in
/-- **Bridge object iso** (general-opens port of `overBasicOpenIsoRestrict`): the inverse engine
applied to the over-picture restriction `M.over W` is the subscheme restriction
`M.restrict W.ι`. -/
noncomputable def overOpensIsoRestrict (M : X.Modules) :
    (modulesOverOpensEquivalence W).inverse.obj (M.over W) ≅ M.restrict W.ι := by
  haveI iinv := overEquivalence_inverse_isContinuous_opens (X := X) W
  haveI icomp := CategoryTheory.Functor.isContinuous_comp
    (Opens.overEquivalence W).inverse (Over.forget W)
    (Opens.grothendieckTopology ↥W.toScheme)
    ((Opens.grothendieckTopology ↥X).over W)
    (Opens.grothendieckTopology ↥X)
  refine (SheafOfModules.pushforwardComp (G := Over.forget W)
    (R' := X.ringCatSheaf)
    (overOpensRingInvHom W)
    (𝟙 (X.ringCatSheaf.over W))).app M ≪≫ ?_
  refine (SheafOfModules.pushforwardCongr (F := W.ι.opensFunctor) ?heq).app M
  ext U' : 3
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Opposite.op_unop,
    Scheme.Opens.ι_appIso, Iso.refl_inv, Functor.whiskerRight_app]
  exact congrArg (forget₂ CommRingCat RingCat).map
    ((congrArg X.sheaf.obj.map (Subsingleton.elim _ (𝟙 _))).trans (X.sheaf.obj.map_id _))

set_option backward.isDefEq.respectTransparency false in
/-- **Over-restriction of presentations** (general-opens port of `presentationOverBasicOpen`,
Route B step B2): if `M.over U` carries a presentation and `W ≤ U`, then the further
over-restriction `M.over W` admits a presentation. -/
noncomputable def presentationOverOpens
    (M : X.Modules) (U : X.Opens)
    (P : (M.over U).Presentation) (hWU : W ≤ U) :
    (M.over W).Presentation :=
  letI Wo : Over U := Over.mk (homOfLE hWU)
  letI e : SheafOfModules.{u} (X.ringCatSheaf.over Wo.left) ≌
      SheafOfModules.{u} ((X.ringCatSheaf.over U).over Wo) :=
    SheafOfModules.pushforwardPushforwardEquivalence
    (Over.iteratedSliceEquiv Wo)
    (S := (X.ringCatSheaf.over U).over Wo)
    (R := X.ringCatSheaf.over Wo.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact X.ringCatSheaf.1.map_id _)
    (by ext : 2; exact X.ringCatSheaf.1.map_id _)
  letI P1 : ((M.over U).over Wo).Presentation :=
    P.map (SheafOfModules.pushforward (𝟙 ((X.ringCatSheaf.over U).over Wo))) (by rfl)
  letI P2 : (e.inverse.obj ((M.over U).over Wo)).Presentation :=
    P1.map e.inverse (.refl _)
  letI iso : e.inverse.obj ((M.over U).over Wo) ≅ M.over Wo.left :=
    e.fullyFaithfulFunctor.preimageIso
      (by exact e.counitIso.app ((M.over U).over Wo))
  show (M.over Wo.left).Presentation from
    SheafOfModules.Presentation.ofIsIso.{u, u, u} iso.hom P2

/-- The engine's functor `pushforward (overOpensRingHom W)` is a right adjoint (it is an
equivalence functor). Project-local instance enabling `pullback (overOpensRingHom W)`. -/
instance pushforward_overOpensRingHom_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (F := (Opens.overEquivalence W).functor)
      (overOpensRingHom W)).IsRightAdjoint := by
  haveI := overEquivalence_functor_isContinuous_opens (X := X) W
  haveI := overEquivalence_inverse_isContinuous_opens (X := X) W
  exact ⟨⟨(modulesOverOpensEquivalence W).inverse,
    ⟨(modulesOverOpensEquivalence W).symm.toAdjunction⟩⟩⟩

/-- The engine's inverse `pushforward (overOpensRingInvHom W)` is a right adjoint. -/
instance pushforward_overOpensRingInvHom_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (F := (Opens.overEquivalence W).inverse)
      (overOpensRingInvHom W)).IsRightAdjoint := by
  haveI := overEquivalence_functor_isContinuous_opens (X := X) W
  haveI := overEquivalence_inverse_isContinuous_opens (X := X) W
  exact ⟨⟨(modulesOverOpensEquivalence W).functor,
    ⟨(modulesOverOpensEquivalence W).toAdjunction⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Unit comparison for the engine inverse**: the inverse engine sends the over-picture
structure-sheaf unit to the subscheme structure-sheaf unit.  Built by identifying the inverse
(a left adjoint of the engine functor) with `pullback (overOpensRingHom W)` via uniqueness of
left adjoints, then applying Mathlib's `pullbackObjUnitToUnit` (an iso since the over-site
equivalence functor is final). -/
noncomputable def overOpensInverseUnitIso :
    (modulesOverOpensEquivalence W).inverse.obj
        (SheafOfModules.unit (Sheaf.over X.ringCatSheaf W)) ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf := by
  haveI := overEquivalence_functor_isContinuous_opens (X := X) W
  haveI := overEquivalence_inverse_isContinuous_opens (X := X) W
  haveI hFinal : (Opens.overEquivalence W).functor.Final := inferInstance
  haveI hIso : IsIso (SheafOfModules.pullbackObjUnitToUnit.{u}
      (F := (Opens.overEquivalence W).functor) (overOpensRingHom W)) := inferInstance
  exact (Adjunction.leftAdjointUniq
      (modulesOverOpensEquivalence W).symm.toAdjunction
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (F := (Opens.overEquivalence W).functor) (overOpensRingHom W))).app _ ≪≫
    @asIso _ _ _ _ _ hIso

set_option backward.isDefEq.respectTransparency false in
/-- **Unit comparison for the engine functor**: the forward engine sends the subscheme
structure-sheaf unit to the over-picture structure-sheaf unit (same `leftAdjointUniq` +
`pullbackObjUnitToUnit` route, with the roles of the two ring comparisons swapped). -/
noncomputable def overOpensFunctorUnitIso :
    (modulesOverOpensEquivalence W).functor.obj
        (SheafOfModules.unit W.toScheme.ringCatSheaf) ≅
      SheafOfModules.unit (Sheaf.over X.ringCatSheaf W) := by
  haveI := overEquivalence_functor_isContinuous_opens (X := X) W
  haveI := overEquivalence_inverse_isContinuous_opens (X := X) W
  haveI hFinal : (Opens.overEquivalence W).inverse.Final := inferInstance
  haveI hIso : IsIso (SheafOfModules.pullbackObjUnitToUnit.{u}
      (F := (Opens.overEquivalence W).inverse) (overOpensRingInvHom W)) := inferInstance
  exact (Adjunction.leftAdjointUniq
      (modulesOverOpensEquivalence W).toAdjunction
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (F := (Opens.overEquivalence W).inverse) (overOpensRingInvHom W))).app _ ≪≫
    @asIso _ _ _ _ _ hIso

set_option backward.isDefEq.respectTransparency false in
/-- **Presentation of a restriction from an over-presentation** (general-opens port of
`presentationModulesRestrictBasicOpen` minus the affine identification step): if `M.over U`
carries a presentation and `W ≤ U`, the subscheme restriction `M.restrict W.ι` admits a global
presentation. -/
noncomputable def presentationRestrictOfOver
    (M : X.Modules) (U : X.Opens)
    (P : (M.over U).Presentation) (hWU : W ≤ U) :
    (M.restrict W.ι).Presentation :=
  letI P2 : (M.over W).Presentation := presentationOverOpens W M U P hWU
  letI P3 : ((modulesOverOpensEquivalence W).inverse.obj (M.over W)).Presentation :=
    P2.map (modulesOverOpensEquivalence W).inverse (overOpensInverseUnitIso W).symm
  SheafOfModules.Presentation.ofIsIso.{u, u, u} (overOpensIsoRestrict W M).hom P3

end RestrictOverBridge

/-! ## Presentation transport along a scheme isomorphism -/

/-- An isomorphism of schemes has a `Final` opens-pullback functor, so the unit comparison
`pullbackObjUnitToUnit` of its module pullback is an isomorphism (generalization of
`pullbackObjUnitToUnit_isIso_basicOpen` from `(basicOpenIsoSpecAway g).inv` to an arbitrary
isomorphism). -/
instance pullbackObjUnitToUnit_isIso_of_isIso {T T' : Scheme.{u}} (φ : T ⟶ T') [IsIso φ] :
    IsIso (SheafOfModules.pullbackObjUnitToUnit φ.toRingCatSheafHom) := by
  haveI : IsIso φ.base := inferInstance
  haveI : (TopologicalSpace.Opens.map φ.base).Final := by
    haveI : (TopologicalSpace.Opens.map φ.base).IsEquivalence :=
      (TopologicalSpace.Opens.mapMapIso (asIso φ.base)).isEquivalence_functor
    infer_instance
  infer_instance

/-- Restriction along a scheme isomorphism sends the structure-sheaf unit to the
structure-sheaf unit (generalization of `restrictBasicOpenUnitIso`). -/
noncomputable def restrictIsoUnitIso {T T' : Scheme.{u}} (φ : T ⟶ T') [IsIso φ] :
    (Scheme.Modules.restrictFunctor.{u} φ).obj (SheafOfModules.unit T'.ringCatSheaf) ≅
      SheafOfModules.unit T.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback φ).app _ ≪≫
    @asIso _ _ _ _ _ (pullbackObjUnitToUnit_isIso_of_isIso φ)

/-! ## The per-slice presentation of a restriction -/

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
-- Two restriction equivalences and their unit comparisons elaborate simultaneously.
set_option maxHeartbeats 2000000 in
/-- **The per-slice presentation of the restriction to an open subscheme**: a presentation of
`F.over A` induces a presentation of the slice `(F.restrict V.ι).over (V.ι ⁻¹ᵁ A)`.

Route: let `Wv := V.ι ⁻¹ᵁ A` and `Wx := V.ι ''ᵁ Wv` (so `Wx ≤ A`).  The X-side bridge
(`presentationRestrictOfOver`) presents `F.restrict Wx.ι`; the canonical scheme isomorphism
`φ : Wv.toScheme ≅ Wx.toScheme` (both are the open `V ∩ A`) transports it to
`(F.restrict V.ι).restrict Wv.ι` via `restrictFunctorComp`/`restrictFunctorCongr`; the V-side
bridge engine (`modulesOverOpensEquivalence` over `V.toScheme`) carries it back to the
over-slice. -/
noncomputable def presentationRestrictSliceOfOver (V : X.Opens) (F : X.Modules)
    (A : X.Opens) (P : (F.over A).Presentation) :
    ((F.restrict V.ι).over (V.ι ⁻¹ᵁ A)).Presentation := by
  set Wv : V.toScheme.Opens := V.ι ⁻¹ᵁ A with hWv
  set Wx : X.Opens := V.ι ''ᵁ Wv with hWx
  -- X-side: present the restriction to the image open `Wx ≤ A`.
  letI P3 : (F.restrict Wx.ι).Presentation :=
    presentationRestrictOfOver Wx F A P (V.ι.image_preimage_le A)
  -- The canonical iso between the V-side and X-side carriers of `V ∩ A`.
  letI φ : Wv.toScheme ≅ Wx.toScheme :=
    IsOpenImmersion.isoOfRangeEq (Wv.ι ≫ V.ι) Wx.ι (by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
        Scheme.Opens.range_ι]
      rfl)
  have hfac : φ.hom ≫ Wx.ι = Wv.ι ≫ V.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  -- Transport across `restrictFunctor φ.hom` (colimit-preserving; unit ↦ unit).
  haveI hpc : Limits.PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      (Scheme.Modules.restrictFunctor.{u} φ.hom) := inferInstance
  letI P4 : ((Scheme.Modules.restrictFunctor.{u} φ.hom).obj (F.restrict Wx.ι)).Presentation :=
    @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P3
      (Scheme.Modules.restrictFunctor.{u} φ.hom) hpc (restrictIsoUnitIso φ.hom).symm
  -- Identify with the iterated restriction `(F.restrict V.ι).restrict Wv.ι`.
  letI e45 : (Scheme.Modules.restrictFunctor.{u} φ.hom).obj (F.restrict Wx.ι) ≅
      (F.restrict V.ι).restrict Wv.ι :=
    ((Scheme.Modules.restrictFunctorComp φ.hom Wx.ι).app F).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hfac).app F ≪≫
      (Scheme.Modules.restrictFunctorComp Wv.ι V.ι).app F
  letI P5 : ((F.restrict V.ι).restrict Wv.ι).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{u, u, u} e45.hom P4
  -- V-side: carry the restriction presentation back to the over-slice through the engine.
  letI eV := modulesOverOpensEquivalence (X := V.toScheme) Wv
  letI P6 : (eV.inverse.obj ((F.restrict V.ι).over Wv)).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{u, u, u}
      (overOpensIsoRestrict Wv (F.restrict V.ι)).symm.hom P5
  letI ηV : eV.functor.obj (SheafOfModules.unit Wv.toScheme.ringCatSheaf) ≅
      SheafOfModules.unit (V.toScheme.ringCatSheaf.over Wv) :=
    overOpensFunctorUnitIso (X := V.toScheme) Wv
  letI P7 : (eV.functor.obj (eV.inverse.obj ((F.restrict V.ι).over Wv))).Presentation :=
    P6.map eV.functor ηV.symm
  exact SheafOfModules.Presentation.ofIsIso.{u, u, u}
    (eV.counitIso.app ((F.restrict V.ι).over Wv)).hom P7

/-! ## Quasi-coherence of the restriction to an open subscheme -/

set_option synthInstance.maxHeartbeats 1000000 in
-- `of_coversTop` synthesizes doubly sliced `HasSheafify` instances beyond the default budget.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- Elaborating the resulting slice presentations also exceeds the default heartbeat budget.
/-- **Restriction of a quasi-coherent module to an open subscheme is quasi-coherent**
(Stacks 01XZ-adjacent; project-local Mathlib supplement — Mathlib's `IsQuasicoherent` has no
restriction stability lemma).

Route: quasi-coherence is local (`SheafOfModules.IsQuasicoherent.of_coversTop`), and the
preimages under `V.ι` of the quasi-coherence cover of `X` cover `V.toScheme`.  The per-slice
obligation is `presentationRestrictSliceOfOver` (the general-opens restrict–over bridge); the
statement transports from `F.restrict V.ι` to `(pullback V.ι).obj F` along
`restrictFunctorIsoPullback` since quasi-coherence is closed under isomorphisms. -/
theorem isQuasicoherent_pullback_opens (V : X.Opens) (F : X.Modules)
    (hF : F.IsQuasicoherent) :
    ((Scheme.Modules.pullback V.ι).obj F).IsQuasicoherent := by
  obtain ⟨⟨q⟩⟩ := hF
  -- The preimages of the quasi-coherence cover of `X` cover the open subscheme.
  have hcov : (Opens.grothendieckTopology V.toScheme).CoversTop
      (fun i => V.ι ⁻¹ᵁ q.X i) := by
    intro W x hx
    obtain ⟨U', f, hf, hU'⟩ := q.coversTop ⊤ (V.ι.base x) (by trivial)
    obtain ⟨i, ⟨g⟩⟩ := hf
    refine ⟨W ⊓ (V.ι ⁻¹ᵁ q.X i), homOfLE inf_le_left, ⟨i, ⟨homOfLE inf_le_right⟩⟩,
      ⟨hx, ?_⟩⟩
    exact (leOfHom g) hU'
  -- Per-slice presentations through the general-opens restrict–over bridge.
  haveI hslice : ∀ i, ((F.restrict V.ι).over (V.ι ⁻¹ᵁ q.X i)).IsQuasicoherent := fun i =>
    (presentationRestrictSliceOfOver V F (q.X i) (q.presentation i)).isQuasicoherent
  have hres : (F.restrict V.ι).IsQuasicoherent :=
    SheafOfModules.IsQuasicoherent.of_coversTop
      (F.restrict V.ι) (fun i => V.ι ⁻¹ᵁ q.X i) hcov
  exact (SheafOfModules.isQuasicoherent.{u} V.toScheme.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app F) hres

/-! ## The per-factor acyclicity -/

/-- **Each single push–pull factor `(j_V)_* (F|_V)` over an affine open `V` is right
`f_*`-acyclic** (the single-σ case of `cechTerm_pushforward_acyclic`).

`R^k f_* ((j_V)_* (F|_V)) ≅ R^k (j_V ≫ f)_* (F|_V)` by the open-immersion composition formula;
`j_V ≫ f : V ⟶ S` is a morphism from an affine scheme to the separated scheme `S`, hence an
affine morphism, and the relative Serre vanishing `higherDirectImage_affineHom_acyclic` kills
all `k ≥ 1`. Project-local. -/
lemma pushPullObj_opens_pushforward_acyclic [HasInjectiveResolutions X.Modules]
    (f : X ⟶ S) [X.IsSeparated] [S.IsSeparated]
    (V : X.Opens) (hV : IsAffineOpen V)
    [HasInjectiveResolutions V.toScheme.Modules]
    (F : X.Modules) (hFV : ((Scheme.Modules.pullback V.ι).obj F).IsQuasicoherent) :
    (Scheme.Modules.pushforward f).IsRightAcyclic
      (pushPullObj F (Over.mk V.ι)) := by
  haveI : IsAffine V.toScheme := hV
  constructor
  intro k
  -- `pushPullObj F (Over.mk V.ι)` is definitionally `(V.ι)_* ((V.ι)^* F)`.
  change IsZero (((Scheme.Modules.pushforward f).rightDerived (k + 1)).obj
    ((Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.pullback V.ι).obj F)))
  haveI : IsAffineHom (V.ι ≫ f) := isAffineHom_of_isAffine_of_isSeparated _
  exact (higherDirectImage_affineHom_acyclic (V.ι ≫ f) _ hFV (k + 1) k.succ_pos).of_iso
    (higherDirectImage_openImmersion_comp V.ι f _ hFV (k + 1))

/-! ## Čech term acyclicity for the pushforward -/

/- Planner strategy: lem:cech_term_pushforward_acyclic ·
Each degree-`p` Čech term `(cechComplexOnX 𝒰 F).X p` decomposes (via `lem:pushPull_sigma_iso`)
as a finite product `∏_σ (j_σ)_*(F|_{U_σ})` over multi-indices `σ = (i₀,…,i_p)`, with each
`U_σ` affine (X separated + all U_i affine).  By `rightAcyclic_finite_prod` it suffices to treat
a single factor `(j_s)_*(F|_{U_s})`.
By `higherDirectImage_openImmersion_comp` (OpenImmersionPushforward.lean):
  `R^k f_*((j_s)_*(F|_{U_s})) ≅ R^k (f∘j_s)_*(F|_{U_s})`.
The composite `f∘j_s : U_s → S` is a morphism from the affine `U_s` to the separated `S`,
hence an AFFINE morphism (this is where `[S.IsSeparated]` is REQUIRED — see the module
docstring for the counterexample without it).  Relative Serre vanishing for affine morphisms
(`higherDirectImage_affineHom_acyclic`) kills `H^k` for `k ≥ 1`.
Assembling: `R^k f_*(Cᵖ) = 0` for all `k ≥ 1`. -/
set_option synthInstance.maxHeartbeats 800000 in
-- The `σ`-indexed Čech product exceeds the default instance-synthesis budget.
/-- **Each Čech term is right-`(f_*)`-acyclic** (blueprint `lem:cech_term_pushforward_acyclic`;
Stacks `lemma-relative-affine-vanishing`).

For a quasi-compact separated morphism `f : X ⟶ S` with `X` separated, **`S` separated** (see
the module docstring: the statement is false without an `S`-side hypothesis), and a finite
affine open cover `𝒰` of `X`, every term `(cechComplexOnX 𝒰 F).X p` of the un-augmented Čech
complex on `X` is right-acyclic for the pushforward functor `f_*`.

`hres` threads the `HasInjectiveResolutions` instances of the intersection subschemes, which
Mathlib cannot yet synthesize (same gap as the `[HasInjectiveResolutions X.Modules]` hypothesis
of the frozen capstone). -/
lemma cechTerm_pushforward_acyclic [HasInjectiveResolutions X.Modules]
    (f : X ⟶ S) [QuasiCompact f] [IsSeparated f] [X.IsSeparated] [S.IsSeparated]
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (h𝒰 : ∀ i, IsAffine (𝒰.X i))
    (F : X.Modules) (hF : F.IsQuasicoherent) (p : ℕ)
    (hres : ∀ σ : Fin (p + 1) → 𝒰.I₀,
      HasInjectiveResolutions (Scheme.Opens.toScheme (coverInterOpen 𝒰 σ)).Modules) :
    (Scheme.Modules.pushforward f).IsRightAcyclic ((cechComplexOnX 𝒰 F).X p) := by
  -- Step 1: the degree-`p` term is (definitionally) the push–pull object of the backbone.
  have hX : (cechComplexOnX 𝒰 F).X p =
      pushPullObj F ((coverCechNerveOver 𝒰).obj (Opposite.op (SimplexCategory.mk p))) := rfl
  rw [hX]
  -- Step 2: each σ-factor is acyclic (composition formula + affine relative Serre vanishing).
  haveI hfac : ∀ σ : Fin (p + 1) → 𝒰.I₀,
      (Scheme.Modules.pushforward f).IsRightAcyclic
        (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) := by
    intro σ
    haveI := hres σ
    exact pushPullObj_opens_pushforward_acyclic f (coverInterOpen 𝒰 σ)
      (isAffineOpen_coverInterOpen 𝒰 h𝒰 σ) F
      (isQuasicoherent_pullback_opens (coverInterOpen 𝒰 σ) F hF)
  -- Step 3: a finite product of acyclic objects is acyclic; transport along the σ-product
  -- decomposition `pushPull_sigma_iso`.
  haveI : (Scheme.Modules.pushforward f).IsRightAcyclic
      (∏ᶜ fun σ : Fin (p + 1) → 𝒰.I₀ =>
        pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) :=
    rightAcyclic_finite_prod (Scheme.Modules.pushforward f) _
  exact isRightAcyclic_of_iso (Scheme.Modules.pushforward f) (pushPull_sigma_iso 𝒰 F p).symm

end AlgebraicGeometry
