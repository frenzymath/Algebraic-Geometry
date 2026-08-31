/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Albanese.CodimOneIndeterminacy

/-!
# Extension and uniqueness from an empty indeterminacy locus

Ported from §4 (second half) of `Albanese/CodimOneExtension.lean` of the
previous Algebraic-Jacobian tree (identical toolchain and mathlib pin),
re-kernel-verified here. Sixth file of the codim-one extension layer.

* `hom_ext_of_toRationalMap_eq` — morphisms from a reduced scheme to a
  separated scheme are determined by their rational-map class.
* `existsUnique_hom_of_indeterminacyLocus_eq_empty` — a rational map with
  `Z(f) = ∅` is uniquely represented by a regular morphism.

**Historical trap (preserved from the source tree).** A former lemma
`extend_of_codimOneFree_of_smooth` claimed "`CodimOneFree f` alone implies a
regular extension, for an arbitrary complete target". That statement is
**false**: the projection `ℙ² ⇢ ℙ¹` away from a point satisfies every
hypothesis (smooth integral source, complete smooth integral target,
indeterminacy a single codim-2 closed point, hence `CodimOneFree`), yet
admits no regular extension. Milne 3.1 asserts only the codim-≥2 conclusion;
the everywhere-extension in Milne 3.2 needs the *group-variety* input of
Lemma 3.3 to force `Z(f) = ∅` first. The honest chain therefore runs through
`Z(f) = ∅` — this file's `existsUnique_hom_of_indeterminacyLocus_eq_empty`
(see its docstring for the full statement-correction note).

Blueprint pin: `thm:codim_one_extension`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

namespace RationalMap

/-- The maximal representative `RationalMap.toPartialMap` of a rational map
is defined exactly on `f.domain` (definitional; recorded as a `simp` lemma so
rewrites can cross the `toPartialMap` boundary). -/
@[simp]
theorem toPartialMap_domain {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated]
    (f : X.RationalMap Y) : f.toPartialMap.domain = f.domain := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms from a reduced scheme to a separated scheme are determined by
their rational-map class: if `g₁.toRationalMap = g₂.toRationalMap` then
`g₁ = g₂`. This is the reduced-and-separated agreement principle
(`AlgebraicGeometry.ext_of_isDominant`) routed through the `PartialMap`
equivalence: the two morphisms agree on a common dense open. -/
theorem hom_ext_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced X]
    [Y.IsSeparated] {g₁ g₂ : X ⟶ Y}
    (e : g₁.toRationalMap = g₂.toRationalMap) : g₁ = g₂ := by
  obtain ⟨W, hW, hle₁, hle₂, he⟩ := PartialMap.toRationalMap_eq_iff.mp e
  haveI : IsDominant W.ι := Opens.isDominant_ι hW
  exact ext_of_isDominant W.ι (by simpa [Scheme.Hom.toPartialMap] using he)

set_option backward.isDefEq.respectTransparency false in
/-- **Extension of a rational map with empty indeterminacy locus.** If the
indeterminacy locus of a rational map `f : X ⇢ Y` from a reduced scheme to a
separated scheme is empty, then `f` is (uniquely) represented by a regular
morphism `g : X ⟶ Y`.

This is the honest "extension" content of the Milne §I.3 chain: once
`Z(f) = ∅` — which for an abelian-variety target follows from combining
Milne Lemma 3.3 (`indeterminacy_pure_codim_one_into_grpScheme`) with the
codim-≥2 conclusion of Milne Theorem 3.1
(`indeterminacy_codimGe2_of_smooth_of_complete`) — the maximal representative
`f.toPartialMap` is defined on all of `X`, and its composite with the
isomorphism `X ≅ (⊤ : X.Opens)` is the required morphism. Uniqueness is the
reduced-and-separated agreement principle (`hom_ext_of_toRationalMap_eq`).

**Statement-correction note (run-0006 T6, session 0015).** This lemma
*replaces* the former `extend_of_codimOneFree_of_smooth`, whose statement —
"`CodimOneFree f` alone implies a regular extension, for an arbitrary
complete target" — was **false as stated**: the projection `ℙ² ⇢ ℙ¹` away
from a point satisfies every hypothesis (smooth integral source, complete
smooth integral target, indeterminacy a single codim-2 closed point, hence
`CodimOneFree`), yet admits no regular extension (any extension `g` would
force `⊤ = g.toPartialMap.domain ≤ f.domain` via
`PartialMap.le_domain_toRationalMap`, but `f.domain = ℙ² ∖ {pt}`). Milne 3.1
asserts only the codim-≥2 conclusion; the everywhere-extension in Milne 3.2
needs the *group-variety* input of Lemma 3.3 to force `Z(f) = ∅` first.

Blueprint reference: `thm:codim_one_extension`. -/
theorem existsUnique_hom_of_indeterminacyLocus_eq_empty
    {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated]
    (f : X.RationalMap Y) (h : indeterminacyLocus f = ∅) :
    ∃! (g : X ⟶ Y), g.toRationalMap = f := by
  -- The domain of definition is all of `X`.
  have hdom : f.toPartialMap.domain = ⊤ := by
    rw [toPartialMap_domain, ← TopologicalSpace.Opens.coe_inj,
      TopologicalSpace.Opens.coe_top, ← Set.compl_empty_iff]
    exact h
  -- The candidate morphism: transport the maximal representative along
  -- `X ≅ ⊤ ≅ f.toPartialMap.domain`.
  have hwit : (X.topIso.inv ≫ X.homOfLE hdom.ge
      ≫ f.toPartialMap.hom).toRationalMap = f := by
    conv_rhs => rw [← f.toRationalMap_toPartialMap]
    refine PartialMap.toRationalMap_eq_iff.mpr ?_
    refine ⟨⊤, by rw [TopologicalSpace.Opens.coe_top]; exact dense_univ,
      le_top, hdom.ge, ?_⟩
    simp only [PartialMap.restrict_hom, Scheme.Hom.toPartialMap,
      Scheme.topIso_hom, Scheme.ι_toIso_inv_assoc,
      Scheme.homOfLE_homOfLE_assoc]
  exact ⟨_, hwit, fun g hg => hom_ext_of_toRationalMap_eq (hg.trans hwit.symm)⟩

end RationalMap

end Scheme

end AlgebraicGeometry
