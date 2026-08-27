/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.QuotFunctorDef
import AlgebraicJacobian.Picard.ZariskiDescentRepresentability
import AlgebraicJacobian.Picard.GrassmannianQuot

/-!
# The Grassmannian functor is a Zariski sheaf (`lem:grassmannian_zariski_sheaf`)

This file proves `AlgebraicGeometry.Scheme.Grassmannian.isZariskiSheaf`
(consumed by `GrassmannianRepresentability.lean`): families of rank-`d`
locally free quotients of `V_T` glue along an open cover of the parameter
scheme `T`, uniquely up to the equivalence of quotients.

## Strategy

*Separation/uniqueness*: an isomorphism of quotients commuting with the (epi)
quotient maps is unique when it exists, and existence is local: if the two
restrictions of a pair of quotients to every member of an open cover are
equivalent, the two kernels annihilate each other's quotient map
(`Grassmannian.pullback_map_cover_faithful`), and the two `Abelian.epiDesc`
descents are mutually inverse by epi-cancellation
(`Scheme.Modules.exists_iso_of_cover_iso`, the pattern of
`Grassmannian.rqPullback_grPointOfRankQuotient_rel`).

*Gluing/existence*: choose representatives `y k` of the compatible family;
the overlap comparisons are unique epi-commuting isomorphisms, so they
satisfy the cocycle conditions of the module-descent engine
(`Scheme.Modules.glue`, `GlueDescent.lean`) over the glue datum of the open
cover; the quotient maps glue through `Scheme.Modules.glueLift`, and the
glued sheaf is transported back to `T` along the canonical isomorphism
`fromGlued`.  Epi-ness and rank-`d` local freeness of the glued quotient are
detected on the cover (`Scheme.Modules.epi_of_cover_epi`,
`Scheme.Modules.isLocallyFreeOfRank_of_cover`).

## References

Blueprint: `lem:grassmannian_zariski_sheaf`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
Source: [Nitsure] §1 (FGA Explained Ch. 5, arXiv:math/0504020); EGA 0_I 4.5.4.
-/

set_option autoImplicit false

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

/-! ## §1. Cover-local detection toolkit

Epi-ness, quotient equivalence, and rank-`d` local freeness of sheaves of
modules are all detected on an open cover of the base scheme.  The engine is
the cover-faithfulness of the pullbacks
(`Grassmannian.pullback_map_cover_faithful`, `GrassmannianQuot.lean`). -/

/-- **Epimorphy of a morphism of sheaves of modules is detected on an open
cover**: if the pullback of `m` to every member of an open cover of `T` is an
epimorphism, then `m` is an epimorphism.  (Reflection through the
cover-faithfulness of the pullbacks, as in
`Grassmannian.tautologicalQuotient_epi`.) -/
lemma epi_of_cover_epi {T : Scheme.{0}} {ι : Type} {V : ι → T.Opens}
    (hV : TopologicalSpace.IsOpenCover V) {M N : T.Modules} (m : M ⟶ N)
    (h : ∀ i, Epi ((Scheme.Modules.pullback (V i).ι).map m)) : Epi m := by
  constructor
  intro Z u v huv
  refine Grassmannian.pullback_map_cover_faithful hV (fun i => ?_)
  haveI := h i
  rw [← cancel_epi ((Scheme.Modules.pullback (V i).ι).map m),
    ← Functor.map_comp, ← Functor.map_comp, huv]

/-- **Equivalence of quotients is local on the base** (the separation half of
the Grassmannian sheaf axiom, module form): two epimorphisms out of the same
sheaf of modules on `T` whose restrictions to the members of an open cover
are intertwined by isomorphisms admit a global intertwining isomorphism.
The kernels annihilate each other's quotient map cover-locally, hence
globally (`Grassmannian.pullback_map_cover_faithful`), and the two
`Abelian.epiDesc` descents are mutually inverse by epi-cancellation. -/
lemma exists_iso_of_cover_iso {T : Scheme.{0}} {ι : Type} {V : ι → T.Opens}
    (hV : TopologicalSpace.IsOpenCover V) {A F F' : T.Modules}
    (q : A ⟶ F) (q' : A ⟶ F') [Epi q] [Epi q']
    (e : ∀ i, (Scheme.Modules.pullback (V i).ι).obj F ≅
      (Scheme.Modules.pullback (V i).ι).obj F')
    (he : ∀ i, (Scheme.Modules.pullback (V i).ι).map q ≫ (e i).hom
      = (Scheme.Modules.pullback (V i).ι).map q') :
    ∃ f : F ≅ F', q ≫ f.hom = q' := by
  have hker1 : kernel.ι q ≫ q' = 0 := by
    refine Grassmannian.pullback_map_cover_faithful hV (fun i => ?_)
    rw [Functor.map_comp, ← he i, ← Category.assoc, ← Functor.map_comp,
      kernel.condition, Functor.map_zero, zero_comp, Functor.map_zero]
  have hker2 : kernel.ι q' ≫ q = 0 := by
    refine Grassmannian.pullback_map_cover_faithful hV (fun i => ?_)
    have hq : (Scheme.Modules.pullback (V i).ι).map q
        = (Scheme.Modules.pullback (V i).ι).map q' ≫ (e i).inv := by
      rw [← he i, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [Functor.map_comp, hq, ← Category.assoc, ← Functor.map_comp,
      kernel.condition, Functor.map_zero, zero_comp, Functor.map_zero]
  refine ⟨⟨Abelian.epiDesc q q' hker1, Abelian.epiDesc q' q hker2, ?_, ?_⟩,
    Abelian.comp_epiDesc _ _ _⟩
  · rw [← cancel_epi q, ← Category.assoc, Abelian.comp_epiDesc,
      Abelian.comp_epiDesc, Category.comp_id]
  · rw [← cancel_epi q', ← Category.assoc, Abelian.comp_epiDesc,
      Abelian.comp_epiDesc, Category.comp_id]

/-- Rank-`d` local freeness transports along isomorphisms of sheaves of
modules. -/
lemma isLocallyFreeOfRank_of_iso {X : Scheme.{0}} {M N : X.Modules} (e : M ≅ N)
    {d : ℕ} (h : SheafOfModules.IsLocallyFreeOfRank N d) :
    SheafOfModules.IsLocallyFreeOfRank M d := by
  obtain ⟨ι, U, hU, hloc⟩ := h
  exact ⟨ι, U, hU, fun i =>
    ⟨(Scheme.Modules.pullback (U i).ι).mapIso e ≪≫ (hloc i).some⟩⟩

/-- **An epi-commuting isomorphism of quotients is unique when it exists.**
The uniqueness principle behind the cocycle conditions of the gluing half of
the Grassmannian sheaf axiom. -/
lemma comm_iso_unique {C : Type*} [Category C] {A F F' : C}
    (q : A ⟶ F) [Epi q] {q' : A ⟶ F'} {f g : F ≅ F'}
    (hf : q ≫ f.hom = q') (hg : q ≫ g.hom = q') : f = g :=
  Iso.ext ((cancel_epi q).mp (hf.trans hg.symm))

/-- **Rank-`d` local freeness is local on the base**: if the restriction of
`F` to every member of an open cover of `T` is locally free of rank `d`, so
is `F`.  The trivialising cover is assembled from the ranges of the composite
open immersions, and the trivialising isomorphisms are transported through
`isoOpensRange` and the pullback pseudofunctor comparisons (the pattern of
`Grassmannian.universalQuotient_isLocallyFreeOfRank`). -/
lemma isLocallyFreeOfRank_of_cover {T : Scheme.{0}} {ι : Type} {V : ι → T.Opens}
    (hV : ⨆ i, V i = ⊤) {F : T.Modules} {d : ℕ}
    (h : ∀ i, SheafOfModules.IsLocallyFreeOfRank
      ((Scheme.Modules.pullback (V i).ι).obj F) d) :
    SheafOfModules.IsLocallyFreeOfRank F d := by
  choose κ U hU hloc using h
  refine ⟨(i : ι) × κ i, fun p => ((U p.1 p.2).ι ≫ (V p.1).ι).opensRange, ?_, fun p => ?_⟩
  · rw [eq_top_iff]
    intro t _
    have ht : t ∈ ⨆ i, V i := by rw [hV]; trivial
    obtain ⟨i, hti⟩ := TopologicalSpace.Opens.mem_iSup.mp ht
    have ht' : (⟨t, hti⟩ : (V i).toScheme) ∈ ⨆ j, U i j := by rw [hU i]; trivial
    obtain ⟨j, htj⟩ := TopologicalSpace.Opens.mem_iSup.mp ht'
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, j⟩, ⟨⟨t, hti⟩, htj⟩, rfl⟩
  · obtain ⟨e⟩ := hloc p.1 p.2
    refine ⟨?_⟩
    letI ii : (U p.1 p.2).toScheme ⟶ T := (U p.1 p.2).ι ≫ (V p.1).ι
    letI eo := ii.isoOpensRange
    exact (Scheme.Modules.pullbackId _).symm.app _ ≪≫
      (Scheme.Modules.pullbackCongr (Iso.inv_hom_id eo).symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp eo.inv eo.hom).app _).symm ≪≫
      (Scheme.Modules.pullback eo.inv).mapIso
        ((Scheme.Modules.pullbackComp eo.hom ii.opensRange.ι).app F ≪≫
          (Scheme.Modules.pullbackCongr ii.isoOpensRange_hom_ι).app F ≪≫
          ((Scheme.Modules.pullbackComp (U p.1 p.2).ι (V p.1).ι).app F).symm ≪≫ e) ≪≫
      Scheme.Modules.pullbackFreeIso eo.inv (ULift.{0} (Fin d))

end Modules

/-! ## §2. Restricted chart quotients and the compatibility predicate

For the gluing half we work with a fixed family of chart quotients
`y k : LocallyFreeQuotient V d (T|_{W k})` over the members of an open cover
`W` of `T.left`.  A morphism `ρ : Z ⟶ W k` (over a total map `u : Z ⟶ T.left`
with `ρ ≫ ι_k = u`) restricts the `k`-th chart quotient to `Z` through the
`Over S`-morphism `chartRes`; an isomorphism `α` between two such restricted
targets is a *gluing isomorphism* (`IsGlueIso`) if it commutes with the two
restricted quotient maps.  Because the quotient maps are epimorphisms, a
gluing isomorphism is unique when it exists (`IsGlueIso.eq`), which yields
the cocycle conditions of the descent engine for free. -/

section ChartRes

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {V : S.Modules} {d : ℕ} {T : Over S}

/-- The `Over S`-morphism restricting along `p : Z' ⟶ Z` between the objects
attached to total maps `p ≫ u` and `u` into `T.left`. -/
noncomputable def glueResHom {Z' Z : Scheme.{0}} (p : Z' ⟶ Z) (u : Z ⟶ T.left) :
    (Over.mk ((p ≫ u) ≫ T.hom) : Over S) ⟶ Over.mk (u ≫ T.hom) :=
  Over.homMk p (Category.assoc p u T.hom).symm

set_option backward.isDefEq.respectTransparency false in
omit [IsLocallyNoetherian S] in
/-- **Composite restriction of a quotient family** — the reusable content of
the `map_comp` law of the Grassmannian functor: restricting along `φ ≫ ψ` is,
through the pseudofunctor comparison, the double restriction. -/
lemma pullbackAlong_comp_q {T₁ T₂ T₃ : Over S} (φ : T₃ ⟶ T₂) (ψ : T₂ ⟶ T₁)
    (x : Scheme.LocallyFreeQuotient V d T₁) :
    (Scheme.LocallyFreeQuotient.pullbackAlong (φ ≫ ψ) x).q ≫
        ((Scheme.Modules.pullbackCongr (Over.comp_left T₃ T₂ T₁ φ ψ)).hom.app x.F ≫
          (Scheme.Modules.pullbackComp φ.left ψ.left).inv.app x.F)
      = (Scheme.LocallyFreeQuotient.pullbackAlong φ
          (Scheme.LocallyFreeQuotient.pullbackAlong ψ x)).q := by
  change ((pullbackTriangleIso (Over.w (φ ≫ ψ)) V).inv ≫
      (Scheme.Modules.pullback (Over.Hom.left (φ ≫ ψ))).map x.q) ≫
      (Scheme.Modules.pullbackCongr (Over.comp_left T₃ T₂ T₁ φ ψ)).hom.app x.F ≫
      (Scheme.Modules.pullbackComp φ.left ψ.left).inv.app x.F
    = (pullbackTriangleIso (Over.w φ) V).inv ≫
      (Scheme.Modules.pullback φ.left).map
        ((pullbackTriangleIso (Over.w ψ) V).inv ≫
          (Scheme.Modules.pullback ψ.left).map x.q)
  rw [Category.assoc,
    (Scheme.Modules.pullbackCongr (Over.comp_left T₃ T₂ T₁ φ ψ)).hom.naturality_assoc x.q,
    (Scheme.Modules.pullbackComp φ.left ψ.left).inv.naturality x.q]
  have key := Scheme.Modules.pullback_comp_app_coherence_inv
    φ.left ψ.left (Over.comp_left T₃ T₂ T₁ φ ψ) T₁.hom
    (Over.w ψ) (Over.w (φ ≫ ψ)) (Over.w φ) V
  simp only [pullbackTriangleIso, Iso.trans_inv, Iso.app_inv, Category.assoc,
    Functor.map_comp]
  rw [reassoc_of% key]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Cast coherence of restricted triangles** (the pseudofunctor core of the
`glueLift` overlap condition): for a square `σ ≫ ι' = f ≫ ι` over a base
morphism `a` and matching triangle collapses, the two ways of re-presenting
the doubly-restricted module agree.  Pure cast algebra — no quotient data. -/
lemma triangleIso_cast_coherence {P Uk Ul G Sb : Scheme.{0}}
    (f : P ⟶ Uk) (ι : Uk ⟶ G) (σ : P ⟶ Ul) (ι' : Ul ⟶ G) (a : G ⟶ Sb)
    {wk : Uk ⟶ Sb} (ek : ι ≫ a = wk) {wl : Ul ⟶ Sb} (el : ι' ≫ a = wl)
    (hpc : σ ≫ ι' = f ≫ ι) {v : P ⟶ Sb} (hk : f ≫ wk = v) (hl : σ ≫ wl = v)
    (M : Sb.Modules) :
    (Scheme.Modules.pullbackComp f ι).inv.app ((Scheme.Modules.pullback a).obj M) ≫
      (Scheme.Modules.pullback f).map (pullbackTriangleIso ek M).hom ≫
      (pullbackTriangleIso hk M).hom ≫ (pullbackTriangleIso hl M).inv
    = (Scheme.Modules.pullbackCongr hpc).inv.app ((Scheme.Modules.pullback a).obj M) ≫
      (Scheme.Modules.pullbackComp σ ι').inv.app ((Scheme.Modules.pullback a).obj M) ≫
      (Scheme.Modules.pullback σ).map (pullbackTriangleIso el M).hom := by
  subst ek el hk
  have cohf := Scheme.Modules.pullback_comp_app_coherence f ι rfl a rfl
    (Category.assoc f ι a) rfl M
  have cohσ := Scheme.Modules.pullback_comp_app_coherence σ ι' rfl a rfl
    (Category.assoc σ ι' a) rfl M
  simp only [Scheme.Modules.pullbackCongr_hom_app, Scheme.Modules.pullbackCongr_inv_app,
    eqToHom_refl, Category.comp_id, Category.id_comp] at cohf cohσ
  simp only [pullbackTriangleIso, Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv,
    Scheme.Modules.pullbackCongr_hom_app, Scheme.Modules.pullbackCongr_inv_app,
    eqToHom_refl, Category.comp_id]
  -- fold the two coherence squares in
  rw [← reassoc_of% cohf]
  -- solve `cohσ` for the pulled-back triangle
  have cohσ' : (Scheme.Modules.pullback σ).map
        ((Scheme.Modules.pullbackComp ι' a).hom.app M)
      = (Scheme.Modules.pullbackComp σ ι').hom.app
          ((Scheme.Modules.pullback a).obj M) ≫
        (Scheme.Modules.pullbackComp (σ ≫ ι') a).hom.app M ≫
        eqToHom (by rw [Category.assoc]) ≫
        (Scheme.Modules.pullbackComp σ (ι' ≫ a)).inv.app M := by
    have h1 := congrArg
      (· ≫ (Scheme.Modules.pullbackComp σ (ι' ≫ a)).inv.app M) cohσ
    simp only [Category.assoc, Iso.hom_inv_id_app] at h1
    exact h1.symm
  rw [cohσ']
  simp only [Iso.inv_hom_id_app_assoc]
  -- transport `pullbackComp` along the square `hpc`
  rw [Scheme.Modules.pullbackComp_hom_app_congr_fst hpc a M]
  simp only [Scheme.Modules.pullbackCongr_hom_app, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]

variable {κ : Type} (W : κ → T.left.Opens)

/-- The `Over S`-morphism restricting the `k`-th chart `T|_{W k}` along
`ρ : Z ⟶ W k`, recorded against a chosen total map `u = ρ ≫ ι_k`. -/
noncomputable def chartRes {Z : Scheme.{0}} (k : κ) (ρ : Z ⟶ (W k).toScheme)
    {u : Z ⟶ T.left} (h : ρ ≫ (W k).ι = u) :
    (Over.mk (u ≫ T.hom) : Over S) ⟶ Scheme.overRes T (W k) :=
  Over.homMk ρ (by subst h; exact (Category.assoc ρ (W k).ι T.hom).symm)

variable (y : ∀ k, Scheme.LocallyFreeQuotient V d (Scheme.overRes T (W k)))

/-- **The gluing-isomorphism predicate**: `α` intertwines the restrictions of
the chart quotients `y k` and `y l` along `ρ` and `σ` over the common total
map `u`.  Such an `α` is unique when it exists (`IsGlueIso.eq`) since the
quotient maps are epimorphisms. -/
def IsGlueIso (k l : κ) {Z : Scheme.{0}} {ρ : Z ⟶ (W k).toScheme}
    {σ : Z ⟶ (W l).toScheme} {u : Z ⟶ T.left}
    (hρ : ρ ≫ (W k).ι = u) (hσ : σ ≫ (W l).ι = u)
    (α : (Scheme.Modules.pullback ρ).obj (y k).F ≅
      (Scheme.Modules.pullback σ).obj (y l).F) : Prop :=
  (Scheme.LocallyFreeQuotient.pullbackAlong (chartRes W k ρ hρ) (y k)).q ≫ α.hom
    = (Scheme.LocallyFreeQuotient.pullbackAlong (chartRes W l σ hσ) (y l)).q

namespace IsGlueIso

variable {W y}

omit [IsLocallyNoetherian S] in
/-- Uniqueness of gluing isomorphisms: the restricted quotient map is an
epimorphism, so at most one isomorphism intertwines. -/
lemma eq {k l : κ} {Z : Scheme.{0}} {ρ : Z ⟶ (W k).toScheme}
    {σ : Z ⟶ (W l).toScheme} {u : Z ⟶ T.left}
    {hρ : ρ ≫ (W k).ι = u} {hσ : σ ≫ (W l).ι = u}
    {α β : (Scheme.Modules.pullback ρ).obj (y k).F ≅
      (Scheme.Modules.pullback σ).obj (y l).F}
    (hα : IsGlueIso W y k l hρ hσ α) (hβ : IsGlueIso W y k l hρ hσ β) : α = β := by
  haveI := (Scheme.LocallyFreeQuotient.pullbackAlong (chartRes W k ρ hρ) (y k)).epi
  exact Scheme.Modules.comm_iso_unique
    (Scheme.LocallyFreeQuotient.pullbackAlong (chartRes W k ρ hρ) (y k)).q hα hβ

omit [IsLocallyNoetherian S] in
/-- Gluing isomorphisms compose. -/
lemma trans {k l m : κ} {Z : Scheme.{0}} {ρ : Z ⟶ (W k).toScheme}
    {σ : Z ⟶ (W l).toScheme} {τ : Z ⟶ (W m).toScheme} {u : Z ⟶ T.left}
    {hρ : ρ ≫ (W k).ι = u} {hσ : σ ≫ (W l).ι = u} {hτ : τ ≫ (W m).ι = u}
    {α : (Scheme.Modules.pullback ρ).obj (y k).F ≅
      (Scheme.Modules.pullback σ).obj (y l).F}
    {β : (Scheme.Modules.pullback σ).obj (y l).F ≅
      (Scheme.Modules.pullback τ).obj (y m).F}
    (hα : IsGlueIso W y k l hρ hσ α) (hβ : IsGlueIso W y l m hσ hτ β) :
    IsGlueIso W y k m hρ hτ (α ≪≫ β) :=
  (Category.assoc
      (Scheme.LocallyFreeQuotient.pullbackAlong (chartRes W k ρ hρ) (y k)).q
      α.hom β.hom).symm.trans ((congrArg (· ≫ β.hom) hα).trans hβ)

omit [IsLocallyNoetherian S] in
/-- Gluing isomorphisms invert. -/
lemma symm {k l : κ} {Z : Scheme.{0}} {ρ : Z ⟶ (W k).toScheme}
    {σ : Z ⟶ (W l).toScheme} {u : Z ⟶ T.left}
    {hρ : ρ ≫ (W k).ι = u} {hσ : σ ≫ (W l).ι = u}
    {α : (Scheme.Modules.pullback ρ).obj (y k).F ≅
      (Scheme.Modules.pullback σ).obj (y l).F}
    (hα : IsGlueIso W y k l hρ hσ α) : IsGlueIso W y l k hσ hρ α.symm :=
  (Iso.comp_inv_eq α).mpr (Eq.symm hα)

end IsGlueIso

variable {W} {y}

omit [IsLocallyNoetherian S] in
/-- The canonical cast is a gluing isomorphism (diagonal case): transporting
along an equality `ρ = σ` of restriction maps to the *same* chart. -/
lemma isGlueIso_eqToIso (k : κ) {Z : Scheme.{0}} {ρ σ : Z ⟶ (W k).toScheme}
    (hρσ : ρ = σ) {u : Z ⟶ T.left}
    (hρ : ρ ≫ (W k).ι = u) (hσ : σ ≫ (W k).ι = u) :
    IsGlueIso W y k k hρ hσ (eqToIso
      (congrArg (fun φ => (Scheme.Modules.pullback φ).obj (y k).F) hρσ)) := by
  subst hρσ
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
omit [IsLocallyNoetherian S] in
/-- **Base change of gluing isomorphisms**: the `pullbackBaseChangeTransport`
of a gluing isomorphism along `p : Z' ⟶ Z` is again a gluing isomorphism
(over the total map `p ≫ u`).  This is the naturality input to the
triple-overlap cocycle condition of the descent engine. -/
lemma IsGlueIso.baseChange {k l : κ} {Z : Scheme.{0}} {ρ : Z ⟶ (W k).toScheme}
    {σ : Z ⟶ (W l).toScheme} {u : Z ⟶ T.left}
    {hρ : ρ ≫ (W k).ι = u} {hσ : σ ≫ (W l).ι = u}
    {α : (Scheme.Modules.pullback ρ).obj (y k).F ≅
      (Scheme.Modules.pullback σ).obj (y l).F}
    (hα : IsGlueIso W y k l hρ hσ α) {Z' : Scheme.{0}} (p : Z' ⟶ Z) :
    IsGlueIso W y k l
      (show (p ≫ ρ) ≫ (W k).ι = p ≫ u by rw [Category.assoc, hρ])
      (show (p ≫ σ) ≫ (W l).ι = p ≫ u by rw [Category.assoc, hσ])
      (Scheme.Modules.pullbackBaseChangeTransport p ρ σ α) := by
  -- restate both restricted quotients through the composite restriction
  have hAk := pullbackAlong_comp_q (glueResHom p u) (chartRes W k ρ hρ) (y k)
  have hAl := pullbackAlong_comp_q (glueResHom p u) (chartRes W l σ hσ) (y l)
  -- move the comparison isos of `hAk`/`hAl` to the right-hand side
  have hk' : (Scheme.LocallyFreeQuotient.pullbackAlong
        (glueResHom p u ≫ chartRes W k ρ hρ) (y k)).q
      = (Scheme.LocallyFreeQuotient.pullbackAlong (glueResHom p u)
          (Scheme.LocallyFreeQuotient.pullbackAlong (chartRes W k ρ hρ) (y k))).q ≫
        ((Scheme.Modules.pullbackComp (glueResHom p u).left
            (chartRes W k ρ hρ).left).hom.app (y k).F ≫
          (Scheme.Modules.pullbackCongr
            (Over.comp_left _ _ _ (glueResHom p u) (chartRes W k ρ hρ))).inv.app (y k).F) := by
    rw [← hAk]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have hl' : (Scheme.LocallyFreeQuotient.pullbackAlong
        (glueResHom p u ≫ chartRes W l σ hσ) (y l)).q
      = (Scheme.LocallyFreeQuotient.pullbackAlong (glueResHom p u)
          (Scheme.LocallyFreeQuotient.pullbackAlong (chartRes W l σ hσ) (y l))).q ≫
        ((Scheme.Modules.pullbackComp (glueResHom p u).left
            (chartRes W l σ hσ).left).hom.app (y l).F ≫
          (Scheme.Modules.pullbackCongr
            (Over.comp_left _ _ _ (glueResHom p u) (chartRes W l σ hσ))).inv.app (y l).F) := by
    rw [← hAl]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  -- restate the goal through the composite restrictions
  change (Scheme.LocallyFreeQuotient.pullbackAlong
      (glueResHom p u ≫ chartRes W k ρ hρ) (y k)).q ≫
      (Scheme.Modules.pullbackBaseChangeTransport p ρ σ α).hom
    = (Scheme.LocallyFreeQuotient.pullbackAlong
      (glueResHom p u ≫ chartRes W l σ hσ) (y l)).q
  rw [hk', hl']
  -- expose the double restriction and the transport
  change ((pullbackTriangleIso (Over.w (glueResHom p u)) V).inv ≫
      (Scheme.Modules.pullback (glueResHom p u).left).map
        (Scheme.LocallyFreeQuotient.pullbackAlong (chartRes W k ρ hρ) (y k)).q) ≫
      ((Scheme.Modules.pullbackComp (glueResHom p u).left
          (chartRes W k ρ hρ).left).hom.app (y k).F ≫
        (Scheme.Modules.pullbackCongr
          (Over.comp_left _ _ _ (glueResHom p u) (chartRes W k ρ hρ))).inv.app (y k).F) ≫
      ((Scheme.Modules.pullbackComp p ρ).inv.app (y k).F ≫
        (Scheme.Modules.pullback p).map α.hom ≫
        (Scheme.Modules.pullbackComp p σ).hom.app (y l).F)
    = ((pullbackTriangleIso (Over.w (glueResHom p u)) V).inv ≫
      (Scheme.Modules.pullback (glueResHom p u).left).map
        (Scheme.LocallyFreeQuotient.pullbackAlong (chartRes W l σ hσ) (y l)).q) ≫
      ((Scheme.Modules.pullbackComp (glueResHom p u).left
          (chartRes W l σ hσ).left).hom.app (y l).F ≫
        (Scheme.Modules.pullbackCongr
          (Over.comp_left _ _ _ (glueResHom p u) (chartRes W l σ hσ))).inv.app (y l).F)
  -- collapse the congruence casts (their endpoints are definitionally equal)
  rw [show (Scheme.Modules.pullbackCongr
      (Over.comp_left _ _ _ (glueResHom p u) (chartRes W k ρ hρ))).inv.app (y k).F
    = 𝟙 _ from rfl]
  rw [show (Scheme.Modules.pullbackCongr
      (Over.comp_left _ _ _ (glueResHom p u) (chartRes W l σ hσ))).inv.app (y l).F
    = 𝟙 _ from rfl]
  simp only [Category.comp_id, Category.assoc]
  -- cancel `pullbackComp` against its inverse and fuse the pullback maps
  rw [show (Scheme.Modules.pullbackComp (glueResHom p u).left
      (chartRes W k ρ hρ).left).hom.app (y k).F
    = (Scheme.Modules.pullbackComp p ρ).hom.app (y k).F from rfl]
  rw [Iso.hom_inv_id_app_assoc]
  rw [show (Scheme.Modules.pullback (glueResHom p u).left).map
      (Scheme.LocallyFreeQuotient.pullbackAlong (chartRes W k ρ hρ) (y k)).q
    = (Scheme.Modules.pullback p).map
      (Scheme.LocallyFreeQuotient.pullbackAlong (chartRes W k ρ hρ) (y k)).q from rfl]
  rw [show (Scheme.Modules.pullback (glueResHom p u).left).map
      (Scheme.LocallyFreeQuotient.pullbackAlong (chartRes W l σ hσ) (y l)).q
    = (Scheme.Modules.pullback p).map
      (Scheme.LocallyFreeQuotient.pullbackAlong (chartRes W l σ hσ) (y l)).q from rfl]
  rw [← Functor.map_comp_assoc, hα]
  rfl

omit [IsLocallyNoetherian S] in
/-- Reindexing the total map of a gluing isomorphism along an equality. -/
lemma IsGlueIso.reindex {k l : κ} {Z : Scheme.{0}} {ρ : Z ⟶ (W k).toScheme}
    {σ : Z ⟶ (W l).toScheme} {u u' : Z ⟶ T.left}
    {hρ : ρ ≫ (W k).ι = u} {hσ : σ ≫ (W l).ι = u}
    {α : (Scheme.Modules.pullback ρ).obj (y k).F ≅
      (Scheme.Modules.pullback σ).obj (y l).F}
    (hα : IsGlueIso W y k l hρ hσ α) (hu : u = u') :
    IsGlueIso W y k l (hρ.trans hu) (hσ.trans hu) α := by
  subst hu
  exact hα

/-- The component of `pullbackCongr` at a module is the canonical cast. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.pullbackCongr_app_eqToIso
    {X Y : Scheme.{0}} {φ ψ : X ⟶ Y} (h : φ = ψ) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).app M
      = eqToIso (congrArg (fun m => (Scheme.Modules.pullback m).obj M) h) := by
  subst h
  exact Iso.ext (Scheme.Modules.pullbackCongr_hom_app rfl M)

omit [IsLocallyNoetherian S] in
/-- The `pullbackCongr` cast attached to an equality of restriction maps to the
same chart is a gluing isomorphism. -/
lemma isGlueIso_pullbackCongr (k : κ) {Z : Scheme.{0}} {ρ σ : Z ⟶ (W k).toScheme}
    (hρσ : ρ = σ) {u : Z ⟶ T.left}
    (hρ : ρ ≫ (W k).ι = u) (hσ : σ ≫ (W k).ι = u) :
    IsGlueIso W y k k hρ hσ ((Scheme.Modules.pullbackCongr hρσ).app (y k).F) := by
  rw [Scheme.Modules.pullbackCongr_app_eqToIso hρσ (y k).F]
  exact isGlueIso_eqToIso (y := y) k hρσ hρ hσ

end ChartRes

/-! ## §3. The glue datum of the cover and the transition isomorphisms

The open cover `W` of `T.left` yields the mathlib glue datum
`(covGD W hW)`, whose glued scheme maps isomorphically
onto `T.left` via `fromGlued`.  The compatibility of the chart quotients over
the scheme-theoretic overlaps `V (k,l) = W k ×_{T.left} W l` provides — by
uniqueness of gluing isomorphisms — transition isomorphisms satisfying the
cocycle conditions (C1)/(C2) of the module-descent engine
(`Scheme.Modules.glue`, `GlueDescent.lean`). -/

section CoverGlue

/-- The glue condition of the glued cover, pushed down to the base. -/
lemma gluedCover_glue_base {X : Scheme.{0}} (𝒰 : Scheme.OpenCover.{0} X) (k l : 𝒰.I₀) :
    (𝒰.gluedCover.t k l ≫ 𝒰.gluedCover.f l k) ≫ 𝒰.f l
      = 𝒰.gluedCover.f k l ≫ 𝒰.f k := by
  have h1 := congrArg (· ≫ 𝒰.fromGlued) (𝒰.gluedCover.glue_condition k l)
  simpa only [Category.assoc, Scheme.Cover.ι_fromGlued] using h1

/-- The chart immersions of a glued cover, composed into a base through
`fromGlued ≫ w`, are the cover maps composed with `w`. -/
lemma gluedCover_ι_w {X : Scheme.{0}} (𝒰 : Scheme.OpenCover.{0} X) (k : 𝒰.I₀)
    {S' : Scheme.{0}} (w : X ⟶ S') :
    𝒰.gluedCover.ι k ≫ (𝒰.fromGlued ≫ w) = 𝒰.f k ≫ w := by
  rw [← Category.assoc, Scheme.Cover.ι_fromGlued]
  rfl

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {V : S.Modules} {d : ℕ} {T : Over S}
variable {κ : Type} (W : κ → T.left.Opens) (hW : ⨆ k, W k = ⊤)

/-- The glue datum attached to the open cover `W` of the total space of `T`. -/
@[reducible] noncomputable def covGD : Scheme.GlueData.{0} :=
  (opensCover T.left W hW).gluedCover

omit [IsLocallyNoetherian S] in
/-- The second projection of the cover overlap, composed with the inclusion of
its chart, agrees with the first: the glue condition of the cover glue datum
over `T.left`. -/
lemma glueSnd_ι (k l : κ) :
    ((covGD W hW).t k l ≫
        (covGD W hW).f l k) ≫ (W l).ι
      = (covGD W hW).f k l ≫ (W k).ι :=
  gluedCover_glue_base (opensCover T.left W hW) k l

omit [IsLocallyNoetherian S] in
/-- The chart immersions of the cover glue datum, composed into `S` through
`fromGlued ≫ T.hom`, are the chart structure maps. -/
lemma glueChart_w (k : κ) :
    (covGD W hW).ι k ≫
        ((opensCover T.left W hW).fromGlued ≫ T.hom)
      = (W k).ι ≫ T.hom :=
  gluedCover_ι_w (opensCover T.left W hW) k T.hom

omit [IsLocallyNoetherian S] in
/-- The canonical isomorphism `fromGlued` of the cover glue datum is an
isomorphism (named access to the mathlib instance). -/
lemma fromGlued_isIso : IsIso ((opensCover T.left W hW).fromGlued) :=
  inferInstance

/-- The inverse of the canonical isomorphism `fromGlued` of the cover glue
datum. -/
noncomputable def fromGluedInv :=
  @inv Scheme _ _ _ ((opensCover T.left W hW).fromGlued) (fromGlued_isIso W hW)

omit [IsLocallyNoetherian S] in
@[reassoc]
lemma fromGluedInv_fromGlued :
    fromGluedInv W hW ≫ (opensCover T.left W hW).fromGlued = 𝟙 T.left :=
  @IsIso.inv_hom_id _ _ _ _ _ (fromGlued_isIso W hW)

/-- The `Over S`-morphism `T ⟶ (glued base)` induced by the inverse of
`fromGlued`. -/
noncomputable def fromGluedHom :
    T ⟶ Over.mk ((opensCover T.left W hW).fromGlued ≫ T.hom) :=
  Over.homMk (fromGluedInv W hW)
    (by
      change fromGluedInv W hW ≫ (opensCover T.left W hW).fromGlued ≫ T.hom = T.hom
      rw [← Category.assoc, fromGluedInv_fromGlued, Category.id_comp])

/-- The `k`-th chart morphism `T|_{W k} ⟶ (glued base)` in `Over S`. -/
noncomputable def glueChartHom (k : κ) :
    Scheme.overRes T (W k) ⟶ Over.mk ((opensCover T.left W hW).fromGlued ≫ T.hom) :=
  Over.homMk ((covGD W hW).ι k) (glueChart_w W hW k)

variable (y : ∀ k, Scheme.LocallyFreeQuotient V d (Scheme.overRes T (W k)))

/-- **The transition-data hypothesis**: over every scheme-theoretic overlap of
the cover, the two restricted chart quotients are intertwined by a (then
unique) gluing isomorphism.  Derived from the sheaf-axiom compatibility
hypothesis in `isZariskiSheaf` below. -/
def GlueCompat : Prop :=
  ∀ k l : κ, ∃ α :
    (Scheme.Modules.pullback ((covGD W hW).f k l)).obj (y k).F ≅
    (Scheme.Modules.pullback ((covGD W hW).t k l ≫
      (covGD W hW).f l k)).obj (y l).F,
    IsGlueIso W y k l rfl (glueSnd_ι W hW k l) α

/-- The chart component of the glued quotient: the tautological source
`(fromGlued ≫ T.hom)^* V`, restricted to the `k`-th chart, is re-presented
through the triangle collapse and mapped by the chart quotient `(y k).q`. -/
noncomputable def glueChartQuot (k : κ) :
    (Scheme.Modules.pullback ((covGD W hW).ι k)).obj
      ((Scheme.Modules.pullback ((opensCover T.left W hW).fromGlued ≫ T.hom)).obj V)
      ⟶ (y k).F :=
  (pullbackTriangleIso (glueChart_w W hW k) V).hom ≫ (y k).q

/-- The transposed chart component, as a morphism into the pushforward — the
input to the descent-equalizer lift `Scheme.Modules.glueLift`. -/
noncomputable def glueLiftComponent (k : κ) :
    (Scheme.Modules.pullback ((opensCover T.left W hW).fromGlued ≫ T.hom)).obj V ⟶
      (Scheme.Modules.pushforward ((covGD W hW).ι k)).obj (y k).F :=
  ((Scheme.Modules.pullbackPushforwardAdjunction ((covGD W hW).ι k)).homEquiv _ _)
    (glueChartQuot W hW y k)

variable {W hW y} (hcpt : GlueCompat W hW y)

/-- The transition isomorphism over the overlap `V (k,l)` — the unique gluing
isomorphism provided by `GlueCompat`. -/
noncomputable def glueTransition (k l : κ) :
    (Scheme.Modules.pullback ((covGD W hW).f k l)).obj (y k).F ≅
    (Scheme.Modules.pullback ((covGD W hW).t k l ≫
      (covGD W hW).f l k)).obj (y l).F :=
  (hcpt k l).choose

omit [IsLocallyNoetherian S] in
lemma glueTransition_isGlueIso (k l : κ) :
    IsGlueIso W y k l rfl (glueSnd_ι W hW k l) (glueTransition hcpt k l) :=
  (hcpt k l).choose_spec

omit [IsLocallyNoetherian S] in
/-- **(C1)**: the diagonal transition isomorphism is the canonical cast.  Both
sides are gluing isomorphisms for the same pair of restrictions, and gluing
isomorphisms are unique. -/
lemma glueTransition_self (k : κ) :
    glueTransition hcpt k k = eqToIso (congrArg
      (fun φ => (Scheme.Modules.pullback φ).obj (y k).F)
      (show (covGD W hW).f k k
          = (covGD W hW).t k k ≫
            (covGD W hW).f k k by
        rw [(covGD W hW).t_id k, Category.id_comp])) :=
  IsGlueIso.eq (glueTransition_isGlueIso hcpt k k)
    (isGlueIso_eqToIso (y := y) k
      (show (covGD W hW).f k k
          = (covGD W hW).t k k ≫
            (covGD W hW).f k k by
        rw [(covGD W hW).t_id k, Category.id_comp])
      rfl (glueSnd_ι W hW k k))

omit [IsLocallyNoetherian S] in
/-- **(C2)**: the triple-overlap cocycle condition of the descent engine for
the transition isomorphisms.  Both sides of the cocycle square are gluing
isomorphisms between the same pair of restricted chart quotients over the
triple overlap (by base change, cast absorption and composition of gluing
isomorphisms), hence equal by uniqueness. -/
lemma glueTransition_cocycle (i j k : κ) :
    Scheme.Modules.pullbackBaseChangeTransport
        (pullback.fst ((covGD W hW).f i j) ((covGD W hW).f i k))
        ((covGD W hW).f i j)
        ((covGD W hW).t i j ≫ (covGD W hW).f j i)
        (glueTransition hcpt i j) ≪≫
      (Scheme.Modules.pullbackCongr
        (Scheme.Modules.glueData_bridge_mid (covGD W hW) i j k)).app (y j).F ≪≫
      Scheme.Modules.pullbackBaseChangeTransport
        ((covGD W hW).t' i j k ≫
          pullback.fst ((covGD W hW).f j k) ((covGD W hW).f j i))
        ((covGD W hW).f j k) ((covGD W hW).t j k ≫ (covGD W hW).f k j)
        (glueTransition hcpt j k) ≪≫
      (Scheme.Modules.pullbackCongr
        (Scheme.Modules.glueData_bridge_tgt (covGD W hW) i j k)).app (y k).F
    = (Scheme.Modules.pullbackCongr
        (Scheme.Modules.glueData_bridge_src (covGD W hW) i j k)).app (y i).F ≪≫
      Scheme.Modules.pullbackBaseChangeTransport
        (pullback.snd ((covGD W hW).f i j) ((covGD W hW).f i k))
        ((covGD W hW).f i k) ((covGD W hW).t i k ≫ (covGD W hW).f k i)
        (glueTransition hcpt i k) := by
  have h1 := (glueTransition_isGlueIso hcpt i j).baseChange
    (pullback.fst ((covGD W hW).f i j) ((covGD W hW).f i k))
  have hσ₁ :
      (pullback.fst ((covGD W hW).f i j) ((covGD W hW).f i k) ≫
          ((covGD W hW).t i j ≫ (covGD W hW).f j i)) ≫ (W j).ι =
        pullback.fst ((covGD W hW).f i j) ((covGD W hW).f i k) ≫
          ((covGD W hW).f i j ≫ (W i).ι) := by
    rw [Category.assoc, glueSnd_ι W hW i j]
  have hσ₂ :
      (((covGD W hW).t' i j k ≫
          pullback.fst ((covGD W hW).f j k) ((covGD W hW).f j i)) ≫
        (covGD W hW).f j k) ≫ (W j).ι =
        pullback.fst ((covGD W hW).f i j) ((covGD W hW).f i k) ≫
          ((covGD W hW).f i j ≫ (W i).ι) := by
    rw [← Scheme.Modules.glueData_bridge_mid (covGD W hW) i j k]
    exact hσ₁
  have h2 := isGlueIso_pullbackCongr (y := y) j
    (Scheme.Modules.glueData_bridge_mid (covGD W hW) i j k) hσ₁ hσ₂
  have hu₃ :
      ((covGD W hW).t' i j k ≫
        pullback.fst ((covGD W hW).f j k) ((covGD W hW).f j i)) ≫
          ((covGD W hW).f j k ≫ (W j).ι) =
        pullback.fst ((covGD W hW).f i j) ((covGD W hW).f i k) ≫
          ((covGD W hW).f i j ≫ (W i).ι) := by
    rw [← Category.assoc]
    exact hσ₂
  have h3 := ((glueTransition_isGlueIso hcpt j k).baseChange
    ((covGD W hW).t' i j k ≫
      pullback.fst ((covGD W hW).f j k) ((covGD W hW).f j i))).reindex hu₃
  have hρ₄ :
      (((covGD W hW).t' i j k ≫
          pullback.fst ((covGD W hW).f j k) ((covGD W hW).f j i)) ≫
        ((covGD W hW).t j k ≫ (covGD W hW).f k j)) ≫ (W k).ι =
        pullback.fst ((covGD W hW).f i j) ((covGD W hW).f i k) ≫
          ((covGD W hW).f i j ≫ (W i).ι) := by
    rw [Category.assoc, glueSnd_ι W hW j k, ← Category.assoc]
    exact hσ₂
  have hσ₄ :
      (pullback.snd ((covGD W hW).f i j) ((covGD W hW).f i k) ≫
        ((covGD W hW).t i k ≫ (covGD W hW).f k i)) ≫ (W k).ι =
        pullback.fst ((covGD W hW).f i j) ((covGD W hW).f i k) ≫
          ((covGD W hW).f i j ≫ (W i).ι) := by
    rw [← Scheme.Modules.glueData_bridge_tgt (covGD W hW) i j k]
    exact hρ₄
  have h4 := isGlueIso_pullbackCongr (y := y) k
    (Scheme.Modules.glueData_bridge_tgt (covGD W hW) i j k) hρ₄ hσ₄
  have hL := h1.trans (h2.trans (h3.trans h4))
  have hρs :
      (pullback.fst ((covGD W hW).f i j) ((covGD W hW).f i k) ≫
        (covGD W hW).f i j) ≫ (W i).ι =
        pullback.fst ((covGD W hW).f i j) ((covGD W hW).f i k) ≫
          ((covGD W hW).f i j ≫ (W i).ι) := by
    rw [Category.assoc]
  have hσs :
      (pullback.snd ((covGD W hW).f i j) ((covGD W hW).f i k) ≫
        (covGD W hW).f i k) ≫ (W i).ι =
        pullback.fst ((covGD W hW).f i j) ((covGD W hW).f i k) ≫
          ((covGD W hW).f i j ≫ (W i).ι) := by
    rw [← Scheme.Modules.glueData_bridge_src (covGD W hW) i j k]
    exact hρs
  have hs := isGlueIso_pullbackCongr (y := y) i
    (Scheme.Modules.glueData_bridge_src (covGD W hW) i j k) hρs hσs
  have hu' :
      pullback.snd ((covGD W hW).f i j) ((covGD W hW).f i k) ≫
          ((covGD W hW).f i k ≫ (W i).ι) =
        pullback.fst ((covGD W hW).f i j) ((covGD W hW).f i k) ≫
          ((covGD W hW).f i j ≫ (W i).ι) := by
    rw [← Category.assoc]
    exact hσs
  have hbc := ((glueTransition_isGlueIso hcpt i k).baseChange
    (pullback.snd ((covGD W hW).f i j) ((covGD W hW).f i k))).reindex hu'
  exact IsGlueIso.eq hL (hs.trans hbc)

set_option backward.isDefEq.respectTransparency false in
omit [IsLocallyNoetherian S] in
/-- **The overlap condition of the glued quotient**, in the pullback-level form
of `Scheme.Modules.glueLift_cond_iff`: over the overlap `V (k,l)`, the two
restrictions of the chart components agree through the transition
isomorphism.  Combines the intertwining property of the transition
isomorphism with the cast coherence `triangleIso_cast_coherence`. -/
lemma glueQuot_overlap (k l : κ) :
    (Scheme.Modules.pullbackComp ((covGD W hW).f k l) ((covGD W hW).ι k)).inv.app
        ((Scheme.Modules.pullback ((opensCover T.left W hW).fromGlued ≫ T.hom)).obj V) ≫
      (Scheme.Modules.pullback ((covGD W hW).f k l)).map (glueChartQuot W hW y k)
    = (Scheme.Modules.pullbackCongr
        (show ((covGD W hW).t k l ≫ (covGD W hW).f l k) ≫ (covGD W hW).ι l
            = (covGD W hW).f k l ≫ (covGD W hW).ι k by
          rw [Category.assoc]; exact (covGD W hW).glue_condition k l)).inv.app
        ((Scheme.Modules.pullback ((opensCover T.left W hW).fromGlued ≫ T.hom)).obj V) ≫
      (Scheme.Modules.pullbackComp ((covGD W hW).t k l ≫ (covGD W hW).f l k)
        ((covGD W hW).ι l)).inv.app
        ((Scheme.Modules.pullback ((opensCover T.left W hW).fromGlued ≫ T.hom)).obj V) ≫
      (Scheme.Modules.pullback ((covGD W hW).t k l ≫ (covGD W hW).f l k)).map
        (glueChartQuot W hW y l) ≫ (glueTransition hcpt k l).inv := by
  have spec := glueTransition_isGlueIso hcpt k l
  change ((pullbackTriangleIso
        (Over.w (chartRes W k ((covGD W hW).f k l) rfl)) V).inv ≫
      (Scheme.Modules.pullback ((covGD W hW).f k l)).map (y k).q) ≫
      (glueTransition hcpt k l).hom
    = (pullbackTriangleIso (Over.w (chartRes W l
        ((covGD W hW).t k l ≫ (covGD W hW).f l k) (glueSnd_ι W hW k l))) V).inv ≫
      (Scheme.Modules.pullback ((covGD W hW).t k l ≫ (covGD W hW).f l k)).map (y l).q
    at spec
  have hqk : (Scheme.Modules.pullback ((covGD W hW).f k l)).map (y k).q
      = (pullbackTriangleIso
          (Over.w (chartRes W k ((covGD W hW).f k l) rfl)) V).hom ≫
        (((pullbackTriangleIso (Over.w (chartRes W l
              ((covGD W hW).t k l ≫ (covGD W hW).f l k) (glueSnd_ι W hW k l))) V).inv ≫
          (Scheme.Modules.pullback ((covGD W hW).t k l ≫ (covGD W hW).f l k)).map
            (y l).q) ≫ (glueTransition hcpt k l).inv) := by
    rw [← spec]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have tcc := triangleIso_cast_coherence
    ((covGD W hW).f k l) ((covGD W hW).ι k)
    ((covGD W hW).t k l ≫ (covGD W hW).f l k) ((covGD W hW).ι l)
    ((opensCover T.left W hW).fromGlued ≫ T.hom)
    (glueChart_w W hW k) (glueChart_w W hW l)
    (show ((covGD W hW).t k l ≫ (covGD W hW).f l k) ≫ (covGD W hW).ι l
        = (covGD W hW).f k l ≫ (covGD W hW).ι k by
      rw [Category.assoc]; exact (covGD W hW).glue_condition k l)
    (Over.w (chartRes W k ((covGD W hW).f k l) rfl))
    (Over.w (chartRes W l ((covGD W hW).t k l ≫ (covGD W hW).f l k)
      (glueSnd_ι W hW k l))) V
  change (Scheme.Modules.pullbackComp ((covGD W hW).f k l) ((covGD W hW).ι k)).inv.app
        ((Scheme.Modules.pullback ((opensCover T.left W hW).fromGlued ≫ T.hom)).obj V) ≫
      (Scheme.Modules.pullback ((covGD W hW).f k l)).map
        ((pullbackTriangleIso (glueChart_w W hW k) V).hom ≫ (y k).q)
    = _
  rw [Functor.map_comp, hqk]
  rw [show (Scheme.Modules.pullback ((covGD W hW).t k l ≫ (covGD W hW).f l k)).map
      (glueChartQuot W hW y l)
    = (Scheme.Modules.pullback ((covGD W hW).t k l ≫ (covGD W hW).f l k)).map
        ((pullbackTriangleIso (glueChart_w W hW l) V).hom ≫ (y l).q) from rfl]
  rw [Functor.map_comp]
  simp only [Category.assoc] at tcc ⊢
  rw [reassoc_of% tcc]

/-! ### The glued module, quotient and family -/

/-- The glued module over the glued scheme of the cover: the value of the
module-descent engine on the chart sheaves and the transition isomorphisms. -/
noncomputable def gluedModule : (covGD W hW).glued.Modules :=
  Scheme.Modules.glue (covGD W hW) (fun k => (y k).F) (glueTransition hcpt)
    (fun k => glueTransition_self hcpt k)
    (fun i j k => glueTransition_cocycle hcpt i j k)

/-- The glued quotient map out of the tautological source, assembled from the
transposed chart components through the descent-equalizer lift. -/
noncomputable def gluedQuot :
    (Scheme.Modules.pullback ((opensCover T.left W hW).fromGlued ≫ T.hom)).obj V ⟶
      gluedModule hcpt :=
  Scheme.Modules.glueLift (covGD W hW) (fun k => (y k).F) (glueTransition hcpt)
    (fun k => glueTransition_self hcpt k)
    (fun i j k => glueTransition_cocycle hcpt i j k)
    (fun k => glueLiftComponent W hW y k)
    (fun p => (Scheme.Modules.glueLift_cond_iff (covGD W hW) (fun k => (y k).F)
      (glueTransition hcpt) (fun k => glueChartQuot W hW y k) p.1 p.2).mpr
      (glueQuot_overlap hcpt p.1 p.2))

set_option backward.isDefEq.respectTransparency false in
omit [IsLocallyNoetherian S] in
/-- **Chart recovery of the glued quotient**: restricting the glued quotient
to the `k`-th chart and projecting through the descent restriction recovers
the chart component. -/
lemma gluedQuot_restrict (k : κ) :
    (Scheme.Modules.pullback ((covGD W hW).ι k)).map (gluedQuot hcpt) ≫
      Scheme.Modules.glueRestrictionHom (covGD W hW) (fun k => (y k).F)
        (glueTransition hcpt) (fun k => glueTransition_self hcpt k)
        (fun i j k => glueTransition_cocycle hcpt i j k) k
    = glueChartQuot W hW y k := by
  unfold gluedQuot
  rw [Scheme.Modules.pullback_map_glueLift_glueRestrictionHom]
  exact Equiv.symm_apply_apply _ _

set_option backward.isDefEq.respectTransparency false in
omit [IsLocallyNoetherian S] in
/-- The glued quotient map is an epimorphism: its chart restrictions are (up
to the chart isomorphisms) the chart quotients, and epimorphy is detected on
the chart cover by joint faithfulness. -/
lemma gluedQuot_epi : Epi (gluedQuot hcpt) := by
  have hchart : ∀ k, Epi ((Scheme.Modules.pullback ((covGD W hW).ι k)).map
      (gluedQuot hcpt)) := by
    intro k
    haveI := (y k).epi
    haveI hcq : Epi (glueChartQuot W hW y k) := by
      unfold glueChartQuot
      infer_instance
    haveI := Scheme.Modules.isIso_glueRestrictionHom (covGD W hW) (fun k => (y k).F)
      (glueTransition hcpt) (fun k => glueTransition_self hcpt k)
      (fun i j k => glueTransition_cocycle hcpt i j k) k
    have hmap : (Scheme.Modules.pullback ((covGD W hW).ι k)).map (gluedQuot hcpt)
        = glueChartQuot W hW y k ≫ inv (Scheme.Modules.glueRestrictionHom (covGD W hW)
            (fun k => (y k).F) (glueTransition hcpt)
            (fun k => glueTransition_self hcpt k)
            (fun i j k => glueTransition_cocycle hcpt i j k) k) := by
      rw [← gluedQuot_restrict hcpt k, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
    rw [hmap]
    infer_instance
  constructor
  intro Z u v huv
  apply Scheme.Modules.pullback_map_jointly_faithful (covGD W hW)
  intro k
  haveI := hchart k
  rw [← cancel_epi ((Scheme.Modules.pullback ((covGD W hW).ι k)).map (gluedQuot hcpt)),
    ← Functor.map_comp, ← Functor.map_comp, huv]

set_option backward.isDefEq.respectTransparency false in
omit [IsLocallyNoetherian S] in
/-- The glued module is locally free of rank `d`: its chart restrictions are
the chart sheaves (by effective descent), and rank-`d` local freeness is
local. -/
lemma gluedModule_locFree :
    SheafOfModules.IsLocallyFreeOfRank (gluedModule hcpt) d := by
  refine Scheme.Modules.isLocallyFreeOfRank_of_cover (T := (covGD W hW).glued)
    (V := fun k => ((covGD W hW).ι k).opensRange) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨k, z, rfl⟩ := (covGD W hW).ι_jointly_surjective x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, z, rfl⟩
  · intro k
    haveI := Scheme.Modules.isIso_glueRestrictionHom (covGD W hW) (fun k => (y k).F)
      (glueTransition hcpt) (fun k => glueTransition_self hcpt k)
      (fun i j k => glueTransition_cocycle hcpt i j k) k
    refine Scheme.Modules.isLocallyFreeOfRank_of_iso
      ((((Scheme.Modules.pullbackCongr
          (((covGD W hW).ι k).isoOpensRange_inv_comp)).app (gluedModule hcpt)).symm ≪≫
        ((Scheme.Modules.pullbackComp ((covGD W hW).ι k).isoOpensRange.inv
          ((covGD W hW).ι k)).app (gluedModule hcpt)).symm))
      (Scheme.Modules.pullback_isLocallyFreeOfRank _
        (Scheme.Modules.isLocallyFreeOfRank_of_iso
          (asIso (Scheme.Modules.glueRestrictionHom (covGD W hW) (fun k => (y k).F)
            (glueTransition hcpt) (fun k => glueTransition_self hcpt k)
            (fun i j k => glueTransition_cocycle hcpt i j k) k))
          (y k).locFree))

/-- The glued family over the glued base object of `Over S`. -/
noncomputable def gluedOverFamily :
    Scheme.LocallyFreeQuotient V d
      (Over.mk ((opensCover T.left W hW).fromGlued ≫ T.hom)) where
  F := gluedModule hcpt
  q := gluedQuot hcpt
  epi := gluedQuot_epi hcpt
  locFree := gluedModule_locFree hcpt

/-- The **glued rank-`d` locally free quotient family on `T`**: transport of
the glued family along the inverse of `fromGlued`. -/
noncomputable def gluedFamily : Scheme.LocallyFreeQuotient V d T :=
  Scheme.LocallyFreeQuotient.pullbackAlong (fromGluedHom W hW) (gluedOverFamily hcpt)

set_option backward.isDefEq.respectTransparency false in
omit [IsLocallyNoetherian S] in
/-- The structure morphism of `T|_{W k}` composed with the inverse of
`fromGlued` is the `k`-th chart morphism of the glue datum. -/
lemma overResHom_fromGluedHom (k : κ) :
    Scheme.overResHom T (W k) ≫ fromGluedHom W hW = glueChartHom W hW k := by
  apply Over.OverMorphism.ext
  change (W k).ι ≫ inv (opensCover T.left W hW).fromGlued = (covGD W hW).ι k
  rw [IsIso.comp_inv_eq]
  exact (Scheme.Cover.ι_fromGlued (opensCover T.left W hW) k).symm

set_option backward.isDefEq.respectTransparency false in
omit [IsLocallyNoetherian S] in
/-- **Restriction recovery**: the glued family restricts on each member of
the cover to the given chart family, up to the equivalence of quotients. -/
lemma gluedFamily_restrict (k : κ) :
    (Scheme.LocallyFreeQuotient.pullbackAlong (Scheme.overResHom T (W k))
      (gluedFamily hcpt)).Rel (y k) := by
  refine Scheme.LocallyFreeQuotient.rel_trans ?_
    (?_ : (Scheme.LocallyFreeQuotient.pullbackAlong (glueChartHom W hW k)
      (gluedOverFamily hcpt)).Rel (y k))
  · -- collapse the double restriction along the composite, then rewrite it
    have hrel : (Scheme.LocallyFreeQuotient.pullbackAlong
        (Scheme.overResHom T (W k) ≫ fromGluedHom W hW) (gluedOverFamily hcpt)).Rel
        (Scheme.LocallyFreeQuotient.pullbackAlong (Scheme.overResHom T (W k))
          (Scheme.LocallyFreeQuotient.pullbackAlong (fromGluedHom W hW)
            (gluedOverFamily hcpt))) :=
      ⟨(Scheme.Modules.pullbackCongr (Over.comp_left _ _ _ (Scheme.overResHom T (W k))
          (fromGluedHom W hW))).app (gluedOverFamily hcpt).F ≪≫
        ((Scheme.Modules.pullbackComp (Scheme.overResHom T (W k)).left
          (fromGluedHom W hW).left).app (gluedOverFamily hcpt).F).symm,
        pullbackAlong_comp_q (Scheme.overResHom T (W k)) (fromGluedHom W hW)
          (gluedOverFamily hcpt)⟩
    have hrel' := Scheme.LocallyFreeQuotient.rel_symm hrel
    rw [overResHom_fromGluedHom] at hrel'
    exact hrel'
  · -- the chart restriction is the chart family, through the descent iso
    haveI := Scheme.Modules.isIso_glueRestrictionHom (covGD W hW) (fun k => (y k).F)
      (glueTransition hcpt) (fun k => glueTransition_self hcpt k)
      (fun i j k => glueTransition_cocycle hcpt i j k) k
    refine ⟨asIso (Scheme.Modules.glueRestrictionHom (covGD W hW) (fun k => (y k).F)
      (glueTransition hcpt) (fun k => glueTransition_self hcpt k)
      (fun i j k => glueTransition_cocycle hcpt i j k) k), ?_⟩
    change ((pullbackTriangleIso (glueChart_w W hW k) V).inv ≫
        (Scheme.Modules.pullback ((covGD W hW).ι k)).map (gluedQuot hcpt)) ≫
        Scheme.Modules.glueRestrictionHom (covGD W hW) (fun k => (y k).F)
          (glueTransition hcpt) (fun k => glueTransition_self hcpt k)
          (fun i j k => glueTransition_cocycle hcpt i j k) k
      = (y k).q
    rw [Category.assoc, gluedQuot_restrict hcpt k]
    change (pullbackTriangleIso (glueChart_w W hW k) V).inv ≫
        ((pullbackTriangleIso (glueChart_w W hW k) V).hom ≫ (y k).q) = (y k).q
    rw [Iso.inv_hom_id_assoc]

end CoverGlue

/-! ## §4. The sheaf axiom

The compatibility hypothesis of `IsZariskiSheafOver` — stated on the
intersections `W k ⊓ W l` — transports to the scheme-theoretic overlaps of
the cover glue datum through the canonical factorisation of the overlap
projection, yielding the `GlueCompat` input of the gluing construction; the
separation half is `Scheme.Modules.exists_iso_of_cover_iso`. -/

section SheafAxiom

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {V : S.Modules} {d : ℕ} {T : Over S}
variable {κ : Type} {W : κ → T.left.Opens}

set_option backward.isDefEq.respectTransparency false in
omit [IsLocallyNoetherian S] in
/-- **Separation**: two rank-`d` locally free quotient families on `T` whose
restrictions to every member of an open cover of `T.left` are equivalent are
equivalent. -/
lemma LocallyFreeQuotient.rel_of_restrict_rel (hW : ⨆ k, W k = ⊤)
    {z z' : Scheme.LocallyFreeQuotient V d T}
    (h : ∀ k, (Scheme.LocallyFreeQuotient.pullbackAlong
        (Scheme.overResHom T (W k)) z).Rel
      (Scheme.LocallyFreeQuotient.pullbackAlong (Scheme.overResHom T (W k)) z')) :
    z.Rel z' := by
  haveI := z.epi
  haveI := z'.epi
  choose f hf using h
  have he : ∀ k, (Scheme.Modules.pullback (W k).ι).map z.q ≫ (f k).hom
      = (Scheme.Modules.pullback (W k).ι).map z'.q := by
    intro k
    have hk : ((pullbackTriangleIso (Over.w (Scheme.overResHom T (W k))) V).inv ≫
        (Scheme.Modules.pullback (W k).ι).map z.q) ≫ (f k).hom
        = (pullbackTriangleIso (Over.w (Scheme.overResHom T (W k))) V).inv ≫
          (Scheme.Modules.pullback (W k).ι).map z'.q := hf k
    rw [Category.assoc] at hk
    exact (Iso.cancel_iso_inv_left _ _ _).mp hk
  exact Scheme.Modules.exists_iso_of_cover_iso hW z.q z'.q (fun k => f k) he

set_option backward.isDefEq.respectTransparency false in
omit [IsLocallyNoetherian S] in
/-- **Compatibility transport**: the sheaf-axiom compatibility of a family of
classes over the intersections `W k ⊓ W l` yields the `GlueCompat` input of
the gluing construction over the scheme-theoretic overlaps. -/
lemma glueCompat_of_map_eq (hW : ⨆ k, W k = ⊤)
    (x : ∀ k, (Scheme.Grassmannian V d).obj (Opposite.op (Scheme.overRes T (W k))))
    (hx : ∀ k l, (Scheme.Grassmannian V d).map
        (Scheme.overResLE T (inf_le_left : W k ⊓ W l ≤ W k)).op (x k)
      = (Scheme.Grassmannian V d).map
        (Scheme.overResLE T (inf_le_right : W k ⊓ W l ≤ W l)).op (x l)) :
    GlueCompat W hW (fun k => (x k).out) := by
  intro k l
  -- the canonical factorisation of the overlap through the intersection
  obtain ⟨c, hc⟩ : ∃ c : (covGD W hW).V (k, l) ⟶ ((W k ⊓ W l : T.left.Opens)).toScheme,
      c ≫ (W k ⊓ W l).ι = (covGD W hW).f k l ≫ (W k).ι := by
    have hrange : Set.range ⇑((covGD W hW).f k l ≫ (W k).ι)
        ⊆ Set.range ⇑(W k ⊓ W l).ι := by
      change Set.range ⇑(pullback.fst ((W k).ι) ((W l).ι) ≫ (W k).ι)
        ⊆ Set.range ⇑(W k ⊓ W l).ι
      rw [IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι,
        Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact le_of_eq (TopologicalSpace.Opens.coe_inf _ _).symm
    exact ⟨IsOpenImmersion.lift (W k ⊓ W l).ι _ hrange,
      IsOpenImmersion.lift_fac (W k ⊓ W l).ι _ hrange⟩
  -- the Over-morphism into the intersection chart
  have hm : c ≫ (W k ⊓ W l).ι ≫ T.hom = ((covGD W hW).f k l ≫ (W k).ι) ≫ T.hom := by
    rw [← Category.assoc, hc]
  obtain ⟨m, hml⟩ : ∃ m' : (Over.mk (((covGD W hW).f k l ≫ (W k).ι) ≫ T.hom) :
      Over S) ⟶ Scheme.overRes T (W k ⊓ W l), m'.left = c :=
    ⟨Over.homMk c hm, rfl⟩
  -- the two factorisations of the restricted charts
  have hA : chartRes W k ((covGD W hW).f k l) rfl
      = m ≫ Scheme.overResLE T (inf_le_left : W k ⊓ W l ≤ W k) := by
    apply Over.OverMorphism.ext
    simp only [chartRes, Scheme.overResLE, Over.comp_left, Over.homMk_left]
    rw [hml, ← cancel_mono (W k).ι, Category.assoc c, Scheme.homOfLE_ι, hc]
  have hB : chartRes W l ((covGD W hW).t k l ≫ (covGD W hW).f l k)
        (glueSnd_ι W hW k l)
      = m ≫ Scheme.overResLE T (inf_le_right : W k ⊓ W l ≤ W l) := by
    apply Over.OverMorphism.ext
    simp only [chartRes, Scheme.overResLE, Over.comp_left, Over.homMk_left]
    rw [hml, ← cancel_mono (W l).ι, Category.assoc c, Scheme.homOfLE_ι, hc]
    exact glueSnd_ι W hW k l
  -- the class-level compatibility over the overlap
  have hclass : (Scheme.Grassmannian V d).map
        (chartRes W k ((covGD W hW).f k l) rfl).op (x k)
      = (Scheme.Grassmannian V d).map
        (chartRes W l ((covGD W hW).t k l ≫ (covGD W hW).f l k)
          (glueSnd_ι W hW k l)).op (x l) := by
    calc (Scheme.Grassmannian V d).map
          (chartRes W k ((covGD W hW).f k l) rfl).op (x k)
        = (Scheme.Grassmannian V d).map
            (m ≫ Scheme.overResLE T inf_le_left).op (x k) :=
          Scheme.ZariskiDescent.map_congr (F := Scheme.Grassmannian V d) hA (x k)
      _ = (Scheme.Grassmannian V d).map m.op
            ((Scheme.Grassmannian V d).map (Scheme.overResLE T inf_le_left).op
              (x k)) :=
          (Scheme.ZariskiDescent.map_map (F := Scheme.Grassmannian V d) m
            (Scheme.overResLE T inf_le_left) (x k)).symm
      _ = (Scheme.Grassmannian V d).map m.op
            ((Scheme.Grassmannian V d).map (Scheme.overResLE T inf_le_right).op
              (x l)) := by rw [hx k l]
      _ = (Scheme.Grassmannian V d).map
            (m ≫ Scheme.overResLE T inf_le_right).op (x l) :=
          Scheme.ZariskiDescent.map_map (F := Scheme.Grassmannian V d) m
            (Scheme.overResLE T inf_le_right) (x l)
      _ = _ :=
          (Scheme.ZariskiDescent.map_congr (F := Scheme.Grassmannian V d) hB (x l)).symm
  -- convert the class equality into a gluing isomorphism
  have h1 : (Scheme.Grassmannian V d).map
        (chartRes W k ((covGD W hW).f k l) rfl).op (x k)
      = Quotient.mk _ (Scheme.LocallyFreeQuotient.pullbackAlong
          (chartRes W k ((covGD W hW).f k l) rfl) ((x k).out)) := by
    conv_lhs => rw [← Quotient.out_eq (x k)]
    rfl
  have h2 : (Scheme.Grassmannian V d).map
        (chartRes W l ((covGD W hW).t k l ≫ (covGD W hW).f l k)
          (glueSnd_ι W hW k l)).op (x l)
      = Quotient.mk _ (Scheme.LocallyFreeQuotient.pullbackAlong
          (chartRes W l ((covGD W hW).t k l ≫ (covGD W hW).f l k)
            (glueSnd_ι W hW k l)) ((x l).out)) := by
    conv_lhs => rw [← Quotient.out_eq (x l)]
    rfl
  obtain ⟨α, hα⟩ := Quotient.exact ((h1.symm.trans hclass).trans h2)
  exact ⟨α, hα⟩

set_option backward.isDefEq.respectTransparency false in
omit [IsLocallyNoetherian S] in
/-- **The Grassmannian functor is a Zariski sheaf** ([Nitsure] §1; the
locality behind the chart construction): families of rank-`d` locally free
quotients of `V_T` glue uniquely along open covers of the parameter scheme.
Existence is the module-descent gluing (`gluedFamily`), separation is
`LocallyFreeQuotient.rel_of_restrict_rel`. -/
theorem grassmannian_isZariskiSheafOver (V : S.Modules) (d : ℕ) :
    Scheme.IsZariskiSheafOver (Scheme.Grassmannian V d) := by
  intro T κ W hW x hx
  refine ⟨Quotient.mk _ (gluedFamily (glueCompat_of_map_eq hW x hx)), fun k => ?_, ?_⟩
  · -- the glued family restricts to the given classes
    change Quotient.mk _ (Scheme.LocallyFreeQuotient.pullbackAlong
        (Scheme.overResHom T (W k)) (gluedFamily (glueCompat_of_map_eq hW x hx)))
      = x k
    rw [← Quotient.out_eq (x k)]
    exact Quotient.sound (gluedFamily_restrict (glueCompat_of_map_eq hW x hx) k)
  · -- separation: any two glued classes agree
    intro z hz
    induction z using Quotient.ind with
    | _ zz =>
      refine Quotient.sound (LocallyFreeQuotient.rel_of_restrict_rel hW (fun k => ?_))
      have hz2 : (Scheme.Grassmannian V d).map (Scheme.overResHom T (W k)).op
          (Quotient.mk _ (gluedFamily (glueCompat_of_map_eq hW x hx))) = x k := by
        change Quotient.mk _ (Scheme.LocallyFreeQuotient.pullbackAlong
            (Scheme.overResHom T (W k)) (gluedFamily (glueCompat_of_map_eq hW x hx)))
          = x k
        rw [← Quotient.out_eq (x k)]
        exact Quotient.sound (gluedFamily_restrict (glueCompat_of_map_eq hW x hx) k)
      exact Quotient.exact ((hz k).trans hz2.symm)

end SheafAxiom

end Scheme

end AlgebraicGeometry
