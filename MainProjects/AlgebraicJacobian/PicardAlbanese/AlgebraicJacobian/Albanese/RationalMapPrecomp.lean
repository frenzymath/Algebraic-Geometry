/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Precomposition of a rational map with an open morphism

Mathlib's `AlgebraicGeometry.Scheme.RationalMap` API provides only `compHom`,
the composition of a rational map with a *morphism on the right*
(`f : X ⤏ Y`, `g : Y ⟶ Z` ↦ `X ⤏ Z`). The dual operation — precomposing a
rational map with a morphism *on the left* — is missing.

For a morphism `p : W ⟶ X` whose underlying continuous map is **open**, and a
rational map `f : X ⤏ Y`, the composite `f ∘ p : W ⤏ Y` is a well-defined
rational map. Openness of `p` is exactly what guarantees that the preimage
`p⁻¹(f.domain)` of the (dense open) domain of definition stays dense
(`Dense.preimage`), so that the pulled-back partial map is again a partial map,
and that the construction descends to equivalence classes.

This is the first missing brick in Milne's difference-map construction
`Φ = m ∘ (f × f) : X × X ⤏ G` (Milne, *Abelian Varieties*, Lemma 3.3): the two
projections `prᵢ : X × X ⟶ X` are open (flat, locally of finite presentation,
being base changes of the smooth structure morphism `X ⟶ Spec k̄`), so
`f.precomp prᵢ` is the pullback of `f` along a projection.

## Main definitions

* `Scheme.PartialMap.precomp` — precomposition of a partial map with an open
  morphism.
* `Scheme.RationalMap.precomp` — precomposition of a rational map with an open
  morphism, descended from `PartialMap.precomp`.

## Main results

* `Scheme.RationalMap.precomp_compHom` — precomposition commutes with
  right-composition, `(f.precomp p hp).compHom g = (f.compHom g).precomp p hp`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

variable {W X Y Z : Scheme.{u}}

namespace PartialMap

/-- **Auxiliary restriction square.** For a morphism `p : W ⟶ X` and opens
`V ≤ U` of `X`, restricting `p ∣_ U` to the smaller preimage `p ⁻¹ᵁ V` agrees
with `p ∣_ V` followed by the inclusion `V ↪ U`. Both sides are pinned down by
composing with the mono `U.ι`. -/
lemma homOfLE_comp_morphismRestrict (p : W ⟶ X) {U V : X.Opens} (hUV : V ≤ U)
    (h : p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U) :
    W.homOfLE h ≫ (p ∣_ U) = (p ∣_ V) ≫ X.homOfLE hUV := by
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι,
    ← Category.assoc (W.homOfLE h), Scheme.homOfLE_ι, Category.assoc,
    Scheme.homOfLE_ι, morphismRestrict_ι]

/-- **Precomposition of a partial map with an open morphism.** For `f : X ⤏ Y`
(as a partial map) and a morphism `p : W ⟶ X` whose underlying map is open, the
composite `f ∘ p : W ⤏ Y` is defined on `p⁻¹(f.domain)`, which is dense because
open maps pull dense sets back to dense sets. -/
@[simps domain hom]
noncomputable def precomp (f : X.PartialMap Y) (p : W ⟶ X) (hp : IsOpenMap p.base) :
    W.PartialMap Y where
  domain := p ⁻¹ᵁ f.domain
  dense_domain := f.dense_domain.preimage hp
  hom := (p ∣_ f.domain) ≫ f.hom

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition respects the equivalence of partial maps, hence descends to
rational maps. -/
lemma precomp_equiv {f g : X.PartialMap Y} (p : W ⟶ X) (hp : IsOpenMap p.base)
    (h : f.equiv g) : (f.precomp p hp).equiv (g.precomp p hp) := by
  obtain ⟨V, hV, hVl, hVr, e⟩ := h
  have hVd : Dense ((p ⁻¹ᵁ V : W.Opens) : Set W) := by
    rw [TopologicalSpace.Opens.map_coe]; exact hV.preimage hp
  refine ⟨p ⁻¹ᵁ V, hVd, p.preimage_mono hVl, p.preimage_mono hVr, ?_⟩
  simp only [restrict_hom, precomp_hom] at e ⊢
  rw [← Category.assoc, ← Category.assoc,
    homOfLE_comp_morphismRestrict p hVl, homOfLE_comp_morphismRestrict p hVr,
    Category.assoc, Category.assoc, e]

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition with an `S`-morphism preserves being an `S`-map: if `f` is an
`S`-rational map and `p : W ⟶ X` is an `S`-morphism, then `f ∘ p` is an
`S`-rational map. In Milne's setting all schemes live over `k̄`, so the difference
map is automatically a `k̄`-map. -/
instance precomp_isOver {S : Scheme.{u}} [W.Over S] [X.Over S] [Y.Over S]
    (f : X.PartialMap Y) [f.IsOver S] (p : W ⟶ X) [p.IsOver S] (hp : IsOpenMap p.base) :
    (f.precomp p hp).IsOver S := by
  haveI hrestr : (p ∣_ f.domain).IsOver S := by
    rw [Hom.isOver_iff]
    change (p ∣_ f.domain) ≫ (f.domain.ι ≫ X ↘ S) = (p ⁻¹ᵁ f.domain).ι ≫ W ↘ S
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, comp_over]
  change ((p ∣_ f.domain) ≫ f.hom).IsOver S
  infer_instance

end PartialMap

/-- **Precomposition of a rational map with an open morphism.** For `f : X ⤏ Y`
and a morphism `p : W ⟶ X` whose underlying map is open, `f.precomp p hp : W ⤏ Y`
is the composite `f ∘ p`, obtained by pulling any representative partial map back
along `p`. -/
noncomputable def RationalMap.precomp (f : X ⤏ Y) (p : W ⟶ X) (hp : IsOpenMap p.base) :
    W ⤏ Y :=
  Quotient.map (PartialMap.precomp · p hp) (fun _ _ ↦ PartialMap.precomp_equiv p hp) f

@[simp]
lemma RationalMap.precomp_toRationalMap (f : X.PartialMap Y) (p : W ⟶ X)
    (hp : IsOpenMap p.base) :
    (f.precomp p hp).toRationalMap = f.toRationalMap.precomp p hp := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition on the left commutes with right-composition by a morphism.
This is what lets Milne's difference map be assembled as
`(f.precomp prᵢ).compHom (m ∘ (id × inv))`. -/
lemma RationalMap.precomp_compHom (f : X ⤏ Y) (p : W ⟶ X) (hp : IsOpenMap p.base)
    (g : Y ⟶ Z) :
    (f.precomp p hp).compHom g = (f.compHom g).precomp p hp := by
  obtain ⟨f, rfl⟩ := f.exists_rep
  simp only [← RationalMap.precomp_toRationalMap, ← RationalMap.compHom_toRationalMap]
  refine congrArg PartialMap.toRationalMap (PartialMap.ext _ _ rfl ?_)
  rw [Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp,
    PartialMap.compHom_hom, PartialMap.precomp_hom, PartialMap.precomp_hom,
    PartialMap.compHom_hom, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Precomposing the rational map of a *morphism* `g : X ⟶ Y` with an open morphism
`p : W ⟶ X` is the rational map of the composite `p ≫ g`. This produces the over-`S`
hypotheses feeding the pairing of Milne's difference map:
`(X.hom.toRationalMap).precomp prᵢ = (prᵢ ≫ X.hom).toRationalMap`. -/
@[simp]
lemma RationalMap.precomp_hom_toRationalMap (g : X ⟶ Y) (p : W ⟶ X)
    (hp : IsOpenMap p.base) :
    (g.toRationalMap).precomp p hp = (p ≫ g).toRationalMap := by
  rw [show (g.toRationalMap : X ⤏ Y) = g.toPartialMap.toRationalMap from rfl,
    ← RationalMap.precomp_toRationalMap]
  refine congrArg PartialMap.toRationalMap (PartialMap.ext _ _ rfl ?_)
  simp only [Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp, PartialMap.precomp_hom,
    Scheme.Hom.toPartialMap_hom]
  have key : (p ∣_ (g.toPartialMap).domain) ≫ X.topIso.hom = W.topIso.hom ≫ p :=
    morphismRestrict_ι p _
  rw [← Category.assoc, key, Category.assoc]

/-- **Precomposition enlarges the domain by (at least) the preimage.** For a rational
map `f : X ⤏ Y` and an open morphism `p : W ⟶ X`, every point of `W` mapping into
the domain of definition `f.domain` lies in the domain of `f.precomp p`: pull any
representative `F₀` of `f` defined at `p w` back along `p` to a representative
`F₀.precomp p` of `f.precomp p` defined at `w`.

This is the domain half of the reflection `Dom(f ∘ p) = p⁻¹(Dom f)` (the reverse
inclusion is genuine descent and needs flatness of `p`); the easy inclusion here is
what feeds Milne Lemma 3.3 Sub-step 2, where `p = prᵢ` and `f ∘ prᵢ` must be defined
wherever `f` is defined on the `i`-th factor. -/
theorem RationalMap.le_domain_precomp (f : X ⤏ Y) (p : W ⟶ X) (hp : IsOpenMap p.base) :
    p ⁻¹ᵁ f.domain ≤ (f.precomp p hp).domain := by
  intro w hw
  have hw' : p.base w ∈ f.domain := hw
  rw [RationalMap.mem_domain] at hw'
  obtain ⟨F₀, hwF₀, hF₀⟩ := hw'
  rw [RationalMap.mem_domain]
  exact ⟨F₀.precomp p hp, hwF₀, by rw [RationalMap.precomp_toRationalMap, hF₀]⟩

end Scheme

end AlgebraicGeometry
