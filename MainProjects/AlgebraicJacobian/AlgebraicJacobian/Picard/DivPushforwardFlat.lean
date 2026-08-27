/-
Copyright (c) 2026 Axel Delaval. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AlgebraicJacobian.Picard.DivDegree
import AlgebraicJacobian.Picard.SchematicSupport
import AlgebraicJacobian.Picard.RigidPushforwardTransfer
import AlgebraicJacobian.Picard.FlatteningStratificationUniversal

/-!
# Pushing a divisor family down to the base, flatly

Campaign milestone **D3'** (`informal/pic-representability-campaign.md:305`) asks
for the locus over which a Grassmannian `T`-point arises from a degree-`d`
`DivFamily` to be locally closed *universally*, by extending
`AlgebraicGeometry.flatLocusStratification_universal`
(`Picard/FlatteningStratificationUniversal.lean`) "to the family `C × G → G`".

This file supplies the object that extension has to be about, and records why the
extension has to be phrased this way rather than by relativising the machine.

## The shape of the reduction, and why it is forced

`flatLocusStratification_universal` is stated for a module **on the base**,
`F : S.Modules`, with `π = 𝟙 S`. That is not an accident of its proof that a
later session can relax: the whole stratification machine is built on
`Scheme.Modules.pointRank : (X : Scheme) → X.Modules → ↥X → ℕ`, which takes a
module on *one* scheme and a point of *that* scheme. There is no relative
`pointRank` over a morphism, and `chartLocus`, `rankStratum`,
`isOpen_pointRank_pullback_eq` and `existsUnique_factor_rankStratum` all inherit
that shape. So a general-`π` universal property cannot be obtained by adding a
`π` to those statements; the family has to be *moved to the base* first.

For a divisor family that move is available, and cheaply, because a relative
effective divisor is finite over the base — where a general proper family is not.
Concretely: `Scheme.Modules.HasProperSupport` is by definition
`IsProper (schematicSupportι F ≫ f)` (`Picard/QuotScheme.lean`), and
`DivFamily.properSupport` is exactly that datum for `f = pullback.snd π T.hom`.
A proper *quasi-finite* morphism is finite (`IsFinite.of_isProper_of_locallyQuasiFinite`),
hence affine, and `Scheme.CoherentSheafFlat` transfers along an affine
pushforward. Since `O_D` is the pushforward of its own restriction to the support
(`schematicSupportDescentIso`), the family's flatness over `T` becomes flatness of
`q_* O_D` over `T` *itself* — the `n = 0` shape the universal property consumes.

## What is proved here, and what is assumed

* `Scheme.CoherentSheafFlat.of_pushforward_of_isAffineHom` — the **converse** of
  `Scheme.CoherentSheafFlat.pushforward_of_isAffineHom`
  (`Picard/RigidPushforwardTransfer.lean`), which did not exist. Both directions
  are the same chart computation read in opposite directions; the content is that
  the two `Γ(T, U)`-module structures on `Γ(F, π ⁻¹ᵁ V)` agree, which is
  `Scheme.Hom.appLE_comp_appLE`.

* `Scheme.DivFamily.coherentSheafFlat_id_pushforward` — for a divisor family whose
  divisor is quasi-finite over the base, `q_* O_D` is flat over `T` in the
  `CoherentSheafFlat (𝟙 T.left)` sense.

**The quasi-finiteness is a hypothesis, not a theorem, and this file does not
pretend otherwise.** `LocallyQuasiFinite (schematicSupportι x.F ≫ pullback.snd π T.hom)`
says the divisor `D ⊆ X_T` has finite fibres over `T`. Mathematically it is
relative-dimension-1 content: on the curve fibre `C_t`, `D_t` is the zero scheme
of a regular section of an invertible ideal, hence `0`-dimensional. It has no
producer in this project, and `LocallyQuasiFinite` occurs nowhere else in
`Picard/`. It is stated as an instance binder so that a later producer discharges
every consumer at once.

Worth recording for whoever prices the next step: this hypothesis is *cleaner*
than the one it replaces. `Picard/DivDegree.lean` gates its clopen degree
decomposition on `HasLocallyConstantDivDeg`, a `Prop`-class carrying local
constancy of `fiberDeg` as an assumption and also without a producer. With
quasi-finiteness instead, local constancy is downstream of a stratification
theorem rather than assumed beside it — the same missing geometry, but bought
once and in a form the machine can use.

## What remains for D3'

`flatLocusStratification_universal` has exactly **two** binders:
`[IsNoetherian S]` and `[F.IsFinitePresentation]`. `IsQuasicoherent` is a mathlib
instance *from* finite presentation, so it is not a separate requirement;
`DivFamily.isQuasicoherent_pushforward` below is kept because it is the cheap half
and is wanted in its own right, not because `:876` asks for it.

Finite presentation of `q_* O_D` is `DivFamily.isFinitePresentation_pushforward`,
proved here. `isFinitePresentation_of_finite_sections`
(`Picard/RigidPushforwardTransfer.lean`) reduces it to `Module.Finite Γ(T,V)
Γ(q_* O_D, V)` on affine `V`, and that tower is:

* `Module.Finite Γ(T,V) Γ(D,W)` for `W := (i ≫ q) ⁻¹ᵁ V`, from
  `IsFinite.finite_app` — this is where the finiteness of the support map is spent,
  and it is exactly what quasi-finiteness bought;
* `Module.Finite Γ(D,W) Γ(N,W)` from `finite_sections_preimage_of_isAffineHom`
  together with `isFinitePresentation_pullback_schematicSupportι`;
* the two compose by `Module.Finite.trans`, and the result transports back across
  `schematicSupportDescentIso` because `Γ(q_* F, V) = Γ(F, q ⁻¹ᵁ V)` and
  `Γ(i_* N, q ⁻¹ᵁ V) = Γ(N, (i ≫ q) ⁻¹ᵁ V)` are both `rfl`, and the native
  `Γ(T,V)`-action on `Γ(q_* F, V)` *is* `compHom` along `q.app V`, also `rfl`. The
  semilinearity is `Scheme.Modules.Hom.app_smul`.

## What remains for D3'

Two things, and neither is supplied here.

**A stated bridge, not a free fit.** `:876` stratifies a module on the base and
quantifies its universal property over test morphisms `φ : T' ⟶ S`; its antecedent
asks for `CoherentSheafFlat (𝟙 T') ((Modules.pullback φ).obj F)`. What
`coherentSheafFlat_id_pushforward` gives is the `φ = 𝟙` case *before* the identity
pullback is reduced, so feeding it needs
`(Scheme.Modules.pullbackId T.left).app _` through `coherentSheafFlat_of_iso` —
one line, but a line, and it discharges the `φ = 𝟙` **instance** rather than the
antecedent as a family. Whether that instance is what D3' needs is not settled in
this file and should be settled before D3' is priced as "inputs done".

**The `∃!` statement about the Grassmannian locus itself**, which is D3' proper.

Nothing in this file closes D3'.

## Honest status of every antecedent

`Scheme.DivFamily` itself has **no producer anywhere in this project** — 135
mention sites, all consumers (measured 2026-07-29, inbox `I-0957`). So the
theorems here, like the rest of Cluster D', are true statements about a carrier
nobody has yet inhabited; that is a property of the cluster, not of this file, and
it is recorded rather than hidden. The `LocallyQuasiFinite` binder has no producer
either, and is *not* derivable from `DivFamily`'s other fields (kernel-checked),
so it is genuine content and not a restatement of `properSupport`.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Coherent-sheaf flatness descends along an affine pushforward** — the
converse of `Scheme.CoherentSheafFlat.pushforward_of_isAffineHom`.

For affine `π : X ⟶ Y` over `p : Y ⟶ T`, flatness of `π_* F` over `T` gives
flatness of `F` over `T` along the composite. Read on an affine `V ⊆ Y`: the
sections of `π_* F` over `V` *are* `Γ(F, π ⁻¹ᵁ V)` definitionally, with `π ⁻¹ᵁ V`
affine because `π` is, and the two `Γ(T, U)`-module structures agree because
`(π ≫ p).appLE = p.appLE ≫ π.appLE`.

Flatness on the preimage charts `π ⁻¹ᵁ V` of an affine cover of `Y` is what the
hypothesis gives directly; `flat_section_of_affine_cover` globalises it to every
affine pair of `X`, which is where quasi-coherence of `F` is used. -/
theorem Scheme.CoherentSheafFlat.of_pushforward_of_isAffineHom
    {X Y T : Scheme.{u}} (π : X ⟶ Y) [IsAffineHom π] (p : Y ⟶ T)
    (F : X.Modules) [F.IsQuasicoherent]
    (h : Scheme.CoherentSheafFlat p ((Scheme.Modules.pushforward π).obj F)) :
    Scheme.CoherentSheafFlat (π ≫ p) F := by
  classical
  -- For each point of `X` pick an affine `V ⊆ Y` around its image together with an
  -- affine `U ⊆ T` above it; `π ⁻¹ᵁ V` is then affine because `π` is.
  have hchart : ∀ x : X, ∃ (V : Y.Opens) (U : T.Opens) (_ : IsAffineOpen V)
      (_ : IsAffineOpen U), π.base x ∈ V ∧ V ≤ p ⁻¹ᵁ U := by
    intro x
    obtain ⟨U, hUaff, hU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := p.base (π.base x)) (U := ⊤) trivial
    obtain ⟨V, hVaff, hxV, hVU⟩ :=
      exists_isAffineOpen_mem_and_subset (x := π.base x) (U := p ⁻¹ᵁ U) hU
    exact ⟨V, U, hVaff, hUaff, hxV, hVU⟩
  choose Vc Uc hVc hUc hmem hle using hchart
  intro U₀ hU₀ V₀ hV₀ e₀
  refine flat_section_of_affine_cover (π ≫ p) F
    (fun x => π ⁻¹ᵁ Vc x) (fun x => (hVc x).preimage π)
    Uc hUc (fun x => ?_) (fun x => ⟨x, hmem x⟩) (fun x => ?_) hU₀ hV₀ e₀
  · -- `π ⁻¹ᵁ Vc x ≤ (π ≫ p) ⁻¹ᵁ Uc x`
    rw [Scheme.Hom.comp_preimage]
    exact fun z hz => hle x hz
  · -- the chart flatness, read off the hypothesis at `Vc x`
    have base := h (hUc x) (hVc x) (hle x)
    have hφ : ((π ≫ p).appLE (Uc x) (π ⁻¹ᵁ Vc x)
          (by rw [Scheme.Hom.comp_preimage]; exact fun z hz => hle x hz)).hom =
        ((π.app (Vc x)).hom).comp ((p.appLE (Uc x) (Vc x) (hle x)).hom) := by
      have h1 := Scheme.Hom.appLE_comp_appLE π p (Uc x) (Vc x) (π ⁻¹ᵁ Vc x)
        (hle x) le_rfl
      refine RingHom.ext fun r => ?_
      have h2 := congrArg
        (fun (φ : Γ(T, Uc x) ⟶ Γ(X, π ⁻¹ᵁ Vc x)) => φ.hom r) h1
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
      rw [RingHom.comp_apply, Scheme.Hom.app_eq_appLE]
      exact h2.symm
    change @Module.Flat _ _ _ _ (Module.compHom Γ(F, π ⁻¹ᵁ Vc x)
      ((π ≫ p).appLE (Uc x) (π ⁻¹ᵁ Vc x) _).hom)
    rw [hφ]
    exact base

/-- **The pushforward of `O_D` is flat over the base itself.**

For a divisor family `x` whose divisor is quasi-finite over `T`, the pushforward
`q_* O_D` along `q = pullback.snd π T.hom` is flat over `T` in the
`CoherentSheafFlat (𝟙 T.left)` sense.

This is the `n = 0` shape, but **not literally what
`AlgebraicGeometry.flatLocusStratification_universal` asks for**: its antecedent
carries a pullback along the test morphism, which at `φ = 𝟙` is not reduced away.
The bridged form is `coherentSheafFlat_id_pullbackId_pushforward` below.

Route: `x.properSupport` is `IsProper (i ≫ q)` by definition, so with
quasi-finiteness `i ≫ q` is finite, hence affine; `schematicSupportDescentIso`
presents `x.F` as `i_*` of its restriction to the support, whose flatness over
`T` follows from `x.flat` by the converse above; pushing forward along the affine
`i ≫ q` over `𝟙 T.left` and transporting along `pushforwardComp` gives the
claim. -/
theorem Scheme.DivFamily.coherentSheafFlat_id_pushforward
    {S X : Scheme.{u}} {π : X ⟶ S} {T : Over S} (x : Scheme.DivFamily π T)
    [LocallyQuasiFinite
      (Scheme.Modules.schematicSupportι x.F ≫ pullback.snd π T.hom)] :
    Scheme.CoherentSheafFlat (𝟙 (T.left : Scheme.{u}))
      ((Scheme.Modules.pushforward (pullback.snd π T.hom)).obj x.F) := by
  letI := x.isFinitePresentation
  haveI : x.F.IsQuasicoherent := inferInstance
  set q := pullback.snd π T.hom with hq
  set i := Scheme.Modules.schematicSupportι x.F with hi
  -- `i ≫ q` is proper by the divisor family's own support datum, hence finite,
  -- hence affine.
  haveI : IsProper (i ≫ q) := x.properSupport
  haveI : IsFinite (i ≫ q) := IsFinite.of_isProper_of_locallyQuasiFinite _
  haveI : IsAffineHom (i ≫ q) := inferInstance
  haveI : IsAffineHom i :=
    inferInstanceAs (IsAffineHom (Scheme.Modules.annihilator x.F).subschemeι)
  -- present `O_D` as `i_*` of its restriction to the support
  set N := (Scheme.Modules.pullback i).obj x.F with hN
  have hdesc : x.F ≅ (Scheme.Modules.pushforward i).obj N :=
    Scheme.Modules.schematicSupportDescentIso x.F
  haveI : N.IsQuasicoherent := pullback_isQuasicoherent_hom i x.F inferInstance
  -- flatness of `i_* N` over `T`, transported from the family's flatness
  have h1 : Scheme.CoherentSheafFlat q ((Scheme.Modules.pushforward i).obj N) :=
    coherentSheafFlat_of_iso q hdesc x.flat
  -- descend it to `N` along the affine `i`
  have h2 : Scheme.CoherentSheafFlat (i ≫ q) N :=
    Scheme.CoherentSheafFlat.of_pushforward_of_isAffineHom i q N h1
  -- push forward along the affine `i ≫ q`, over the identity of the base
  have h3 : Scheme.CoherentSheafFlat (𝟙 (T.left : Scheme.{u}))
      ((Scheme.Modules.pushforward (i ≫ q)).obj N) :=
    Scheme.CoherentSheafFlat.pushforward_of_isAffineHom (i ≫ q)
      (𝟙 (T.left : Scheme.{u})) N (by rwa [Category.comp_id])
  -- and identify `(i ≫ q)_* N ≅ q_* (i_* N) ≅ q_* O_D`
  intro U hU V hV eV
  exact coherentSheafFlat_of_iso (𝟙 (T.left : Scheme.{u}))
    ((Scheme.Modules.pushforwardComp i q).app N ≪≫
      (Scheme.Modules.pushforward q).mapIso hdesc.symm) h3 hU hV eV

/-- **`q_* O_D` is quasi-coherent** when the ambient family is proper.

Free: properness of `π` gives `QuasiCompact` and `QuasiSeparated` of the projection
`q = pullback.snd π T.hom` by base change, and pushforward along a qcqs morphism
preserves quasi-coherence.

Not a binder of `AlgebraicGeometry.flatLocusStratification_universal`, which asks
only for `[IsNoetherian S]` and `[F.IsFinitePresentation]` — quasi-coherence is a
mathlib instance from the latter. Kept because it is wanted in its own right and is
the cheap half of the pair. -/
theorem Scheme.DivFamily.isQuasicoherent_pushforward
    {S X : Scheme.{u}} {π : X ⟶ S} [IsProper π] {T : Over S}
    (x : Scheme.DivFamily π T) :
    ((Scheme.Modules.pushforward (pullback.snd π T.hom)).obj x.F).IsQuasicoherent := by
  letI := x.isFinitePresentation
  exact Scheme.Modules.pushforward_isQuasicoherent _ x.F

/-- **The `φ = 𝟙` instance of `flatLocusStratification_universal`'s antecedent.**

`:876` asks, for a test morphism `φ : T' ⟶ S`, for
`CoherentSheafFlat (𝟙 T') ((Modules.pullback φ).obj F)`. At `φ = 𝟙` that is *not*
literally `coherentSheafFlat_id_pushforward`: the identity pullback is not reduced
away, so the carrier is `Γ((pullback (𝟙 T.left)).obj (q_* O_D), V)` where the
theorem above supplies `Γ(q_* O_D, V)`. This states the bridged form, so that
consumers do not have to rediscover which of the two shapes they hold.

Note what this does and does not give: the `φ = 𝟙` **instance** of the antecedent,
not the antecedent as a family over all `φ`. -/
theorem Scheme.DivFamily.coherentSheafFlat_id_pullbackId_pushforward
    {S X : Scheme.{u}} {π : X ⟶ S} {T : Over S} (x : Scheme.DivFamily π T)
    [LocallyQuasiFinite
      (Scheme.Modules.schematicSupportι x.F ≫ pullback.snd π T.hom)] :
    Scheme.CoherentSheafFlat (𝟙 (T.left : Scheme.{u}))
      ((Scheme.Modules.pullback (𝟙 (T.left : Scheme.{u}))).obj
        ((Scheme.Modules.pushforward (pullback.snd π T.hom)).obj x.F)) := by
  intro U hU V hV eV
  exact coherentSheafFlat_of_iso (𝟙 (T.left : Scheme.{u}))
    (((Scheme.Modules.pullbackId (T.left : Scheme.{u})).app
      ((Scheme.Modules.pushforward (pullback.snd π T.hom)).obj x.F)).symm)
    x.coherentSheafFlat_id_pushforward hU hV eV

set_option maxHeartbeats 1600000 in
-- Heartbeat headroom: the finiteness tower provisions three module structures under
-- binders and transports across the descent iso, whose `Γ`-identifications are `rfl`
-- but only after unfolding pushforward-of-pushforward — the same budget
-- `flat_section_of_affine_cover` needs for the analogous per-chart provisioning.
/-- **`q_* O_D` is finitely presented** — the input
`flatLocusStratification_universal` actually asks for.

Reduced by `isFinitePresentation_of_finite_sections` to `Module.Finite` of the
sections over each affine `V`, where the finiteness of the support map is spent:
`Γ(T,V) → Γ(D,W)` is finite by `IsFinite.finite_app` (this is what quasi-finiteness
bought), `Γ(D,W) → Γ(N,W)` by `finite_sections_preimage_of_isAffineHom`, and the two
compose. The transport back to `Γ(q_* O_D, V)` is available because the two `Γ`
identifications are `rfl` and the ambient action is `compHom` along `q.app V`. -/
theorem Scheme.DivFamily.isFinitePresentation_pushforward
    {S X : Scheme.{u}} {π : X ⟶ S} [IsProper π] {T : Over S}
    [IsLocallyNoetherian (T.left : Scheme.{u})] (x : Scheme.DivFamily π T)
    [LocallyQuasiFinite
      (Scheme.Modules.schematicSupportι x.F ≫ pullback.snd π T.hom)] :
    ((Scheme.Modules.pushforward (pullback.snd π T.hom)).obj x.F).IsFinitePresentation := by
  letI := x.isFinitePresentation
  haveI := x.isQuasicoherent_pushforward
  refine Scheme.Modules.isFinitePresentation_of_finite_sections _ (fun V hV => ?_)
  let q := pullback.snd π T.hom
  let i := Scheme.Modules.schematicSupportι x.F
  haveI : IsProper (i ≫ q) := x.properSupport
  haveI : IsFinite (i ≫ q) := IsFinite.of_isProper_of_locallyQuasiFinite _
  haveI : IsAffineHom i :=
    inferInstanceAs (IsAffineHom (Scheme.Modules.annihilator x.F).subschemeι)
  let D := Scheme.Modules.schematicSupport x.F
  let W : D.Opens := (i ≫ q) ⁻¹ᵁ V
  let N : D.Modules := (Scheme.Modules.pullback i).obj x.F
  haveI : N.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_schematicSupportι x.F x.isFinitePresentation
  -- the finiteness tower over the affine `V`
  letI : Algebra Γ(T.left, V) Γ(D, W) := (Scheme.Hom.app (i ≫ q) V).hom.toAlgebra
  letI : Module Γ(T.left, V) Γ(N, W) :=
    Module.compHom _ (Scheme.Hom.app (i ≫ q) V).hom
  haveI : Module.Finite Γ(T.left, V) Γ(D, W) := IsFinite.finite_app (i ≫ q) V hV
  haveI : Module.Finite Γ(D, W) Γ(N, W) :=
    Scheme.Modules.finite_sections_preimage_of_isAffineHom (i ≫ q) N hV
  haveI : IsScalarTower Γ(T.left, V) Γ(D, W) Γ(N, W) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI htrans : Module.Finite Γ(T.left, V) Γ(N, W) :=
    Module.Finite.trans Γ(D, W) _
  -- transport along the descent isomorphism; both `Γ`-identifications are `rfl`
  have hdesc : x.F ≅ (Scheme.Modules.pushforward i).obj N :=
    Scheme.Modules.schematicSupportDescentIso x.F
  -- the two directions of the descent iso, at the section level over `V`
  have hcomp : (((Scheme.Modules.pushforward q).map hdesc.hom).app V ≫
      ((Scheme.Modules.pushforward q).map hdesc.inv).app V) =
      𝟙 Γ((Scheme.Modules.pushforward q).obj x.F, V) := by
    rw [← Scheme.Modules.Hom.comp_app, ← Functor.map_comp, hdesc.hom_inv_id]
    simp
  refine Module.Finite.of_surjective
    ({ toFun := fun n => ((Scheme.Modules.pushforward q).map hdesc.inv).app V n
       map_add' := fun a b => map_add _ a b
       map_smul' := fun r n =>
         Scheme.Modules.Hom.app_smul
           ((Scheme.Modules.pushforward q).map hdesc.inv) r n } :
      Γ(N, W) →ₗ[Γ(T.left, V)]
        Γ((Scheme.Modules.pushforward q).obj x.F, V)) (fun z => ?_)
  exact ⟨((Scheme.Modules.pushforward q).map hdesc.hom).app V z,
    congrArg (fun f => f z) hcomp⟩

end AlgebraicGeometry
