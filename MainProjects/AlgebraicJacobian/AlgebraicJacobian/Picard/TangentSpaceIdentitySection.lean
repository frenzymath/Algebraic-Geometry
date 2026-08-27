/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.TangentSpaceStalkAlgebra

/-!
# Tangent-space substrate: rational sections and the identity section (A.3.iii substrate)

The last generic layer of the Kleiman §5 tangent-space computation before it
lands on `Pic⁰_{C/k}`: a *section* of the structure morphism of a `k`-scheme
hits a `k`-rational point, so the tangent-space description
`overDualNumberAtEquivCotangentSpaceDual` of
`Picard/TangentSpaceStalkAlgebra.lean` applies at it unconditionally. For a
`k`-group scheme (an `Over (Spec k)`-object with a `MonObj`/`GrpObj`
instance) the unit `η : 𝟙_ ⟶ G` is such a section, giving the tangent space
at the identity.

## Main declarations

- `AlgebraicGeometry.stalkStructureHom_comp_stalkClosedPointTo` — a section
  `e : Spec k ⟶ X` of the structure morphism retracts the structure
  homomorphism `k ⟶ 𝒪_{X,e(*)}` via the induced stalk map `𝒪_{X,e(*)} ⟶ k`.
- `AlgebraicGeometry.bijective_algebraMap_residueField_of_section` — **the
  image of a section is a `k`-rational point**: `k → κ(e(*))` is bijective.
  Injectivity is automatic (field source); surjectivity follows from the
  retraction because a field homomorphism `κ(e(*)) → k` is injective.
- `AlgebraicGeometry.overDualNumberSectionEquivCotangentSpaceDual` — at the
  image of a section, the over-`Spec k` dual-number points of `X` form the
  `κ(x)`-linear dual of the cotangent space `m_x/m_x²`; no rationality
  hypothesis left.
- `AlgebraicGeometry.GroupScheme.identitySection` — the identity section
  `e : Spec k ⟶ G` of a `k`-monoid/group scheme, the `.left` of the unit
  `η[G] : 𝟙_ (Over (Spec k)) ⟶ G`; `identitySection_comp` says it is a
  section of `G.hom`.
- `AlgebraicGeometry.GroupScheme.identityDualNumberEquivCotangentSpaceDual`
  — **the tangent space of a `k`-group scheme at the identity**: over-`Spec k`
  dual-number points at the identity-section point are the `κ(e)`-linear dual
  of `m_e/m_e²`. This is the generic LHS of Kleiman §5 Thm. 5.11 for
  `G = Pic⁰_{C/k}`; the wiring to `Pic0Scheme C` lives in
  `Picard/Pic0AbelianVariety.lean` (`Pic0.tangentSpaceCotangentDual`), and
  only the `H¹(C, 𝒪_C)` identification of `thm:pic0_tangent_space_iso`
  remains (gated on the `AJC.picrep` cone).

Blueprint: `blueprint/src/chapters/Picard_Pic0AbelianVariety.tex`,
§ `sec:pic0_tangent_space` (`lem:tangent_section_retraction`,
`lem:tangent_section_rational`, `cor:tangent_section_cotangent_dual`,
`def:tangent_identity_section`, `thm:tangent_identity_cotangent_dual`).
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

section RationalSection

variable {k : Type u} [Field k]

/-- **A section retracts the structure homomorphism on stalks.** For a
scheme `X` over `Spec k` and a section `e : Spec k ⟶ X.left` of the
structure morphism, the stalk map of `e` at the closed point retracts the
structure homomorphism `k ⟶ 𝒪_{X, e(*)}`. Immediate from
`comp_eq_spec_iff` applied to `ψ = 𝟙 k`. -/
lemma stalkStructureHom_comp_stalkClosedPointTo
    (X : Over (Spec (CommRingCat.of k))) {e : Spec (CommRingCat.of k) ⟶ X.left}
    (he : e ≫ X.hom = 𝟙 (Spec (CommRingCat.of k))) :
    stalkStructureHom X.hom (e.base (closedPoint k)) ≫ Scheme.stalkClosedPointTo e
      = 𝟙 (CommRingCat.of k) :=
  (comp_eq_spec_iff X.hom e (𝟙 (CommRingCat.of k))).mp (by rwa [Spec.map_id])

/-- **The image of a section is a `k`-rational point.** For a scheme `X`
over `Spec k`, a section `e : Spec k ⟶ X.left` of the structure morphism and
`x` the image of the closed point under `e`, the structure map
`k → κ(x)` to the residue field is bijective. Injectivity is automatic
(`k` is a field); for surjectivity, the retraction
`stalkStructureHom_comp_stalkClosedPointTo` descends to a field
homomorphism `φ : κ(x) → k` splitting `k → κ(x)`, and a splitting by an
injective map is forced to be an inverse: `a = algebraMap k κ(x) (φ a)`
because `φ` kills the difference. -/
theorem bijective_algebraMap_residueField_of_section
    (X : Over (Spec (CommRingCat.of k))) {e : Spec (CommRingCat.of k) ⟶ X.left}
    (he : e ≫ X.hom = 𝟙 (Spec (CommRingCat.of k))) {x : X.left}
    (hx : e.base (closedPoint k) = x) :
    Function.Bijective
      (algebraMap k (ResidueField (X.left.presheaf.stalk x))) := by
  subst hx
  have hretr := stalkStructureHom_comp_stalkClosedPointTo X he
  have hcomp : ∀ c : k,
      (Scheme.stalkClosedPointTo e).hom
        ((stalkStructureHom X.hom (e.base (closedPoint k))).hom c) = c := fun c => by
    simpa using DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hretr) c
  set φ := IsLocalRing.ResidueField.lift (Scheme.stalkClosedPointTo e).hom with hφdef
  have hφ : ∀ c : k,
      φ (algebraMap k
        (ResidueField (X.left.presheaf.stalk (e.base (closedPoint k)))) c) = c := by
    intro c
    rw [← residue_algebraMap, hφdef, IsLocalRing.ResidueField.lift_residue_apply]
    exact hcomp c
  constructor
  · exact (algebraMap k
      (ResidueField (X.left.presheaf.stalk (e.base (closedPoint k))))).injective
  · intro a
    refine ⟨φ a, ?_⟩
    have h0 : φ (algebraMap k
        (ResidueField (X.left.presheaf.stalk (e.base (closedPoint k)))) (φ a) - a)
          = 0 := by
      rw [map_sub, hφ, sub_self]
    exact sub_eq_zero.mp (φ.injective (h0.trans (map_zero φ).symm))

open TrivSqZeroExt in
/-- **The tangent space at the image of a section.** For a scheme `X` over
`Spec k` and a section `e` of the structure morphism, the over-`Spec k`
dual-number points of `X` at `x = e(*)` form the `κ(x)`-linear dual of the
cotangent space `m_x/m_x²` — `overDualNumberAtEquivCotangentSpaceDual` with
the rationality hypothesis discharged by
`bijective_algebraMap_residueField_of_section`. -/
noncomputable def overDualNumberSectionEquivCotangentSpaceDual
    (X : Over (Spec (CommRingCat.of k))) {e : Spec (CommRingCat.of k) ⟶ X.left}
    (he : e ≫ X.hom = 𝟙 (Spec (CommRingCat.of k))) {x : X.left}
    (hx : e.base (closedPoint k) = x) :
    {g : Spec (CommRingCat.of (DualNumber k)) ⟶ X.left //
        g ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
          ∧ g.base (closedPoint (DualNumber k)) = x} ≃
      Module.Dual (ResidueField (X.left.presheaf.stalk x))
        (CotangentSpace (X.left.presheaf.stalk x)) :=
  overDualNumberAtEquivCotangentSpaceDual X x
    (bijective_algebraMap_residueField_of_section X he hx)

end RationalSection

namespace GroupScheme

variable {k : Type u} [Field k]

/-- **The identity section of a `k`-monoid/group scheme.** For an
`Over (Spec k)`-object `G` with a monoid-object structure, the underlying
scheme morphism `Spec k ⟶ G.left` of the unit `η[G] : 𝟙_ ⟶ G`. (For a group
scheme, `[GrpObj G]` supplies the `MonObj G` instance.) -/
noncomputable def identitySection (G : Over (Spec (CommRingCat.of k))) [MonObj G] :
    Spec (CommRingCat.of k) ⟶ G.left :=
  (MonObj.one (X := G)).left

/-- The identity section is a section of the structure morphism: the unit is
a morphism in `Over (Spec k)` out of the monoidal unit `Over.mk (𝟙 (Spec k))`. -/
lemma identitySection_comp (G : Over (Spec (CommRingCat.of k))) [MonObj G] :
    identitySection G ≫ G.hom = 𝟙 (Spec (CommRingCat.of k)) :=
  Over.w (MonObj.one (X := G))

open TrivSqZeroExt in
/-- **The tangent space of a `k`-group scheme at the identity** (Kleiman §5
Thm. 5.11, LHS, generic form): for a `k`-monoid/group scheme `G`, the
over-`Spec k` dual-number points of `G` at the identity-section point
`e(*)` form the `κ(e(*))`-linear dual of the cotangent space
`m_{e(*)}/m_{e(*)}²`. No rationality hypothesis: the identity section makes
`e(*)` automatically `k`-rational. -/
noncomputable def identityDualNumberEquivCotangentSpaceDual
    (G : Over (Spec (CommRingCat.of k))) [MonObj G] :
    {g : Spec (CommRingCat.of (DualNumber k)) ⟶ G.left //
        g ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
          ∧ g.base (closedPoint (DualNumber k))
              = (identitySection G).base (closedPoint k)} ≃
      Module.Dual
        (ResidueField (G.left.presheaf.stalk ((identitySection G).base (closedPoint k))))
        (CotangentSpace (G.left.presheaf.stalk ((identitySection G).base (closedPoint k)))) :=
  overDualNumberSectionEquivCotangentSpaceDual G (identitySection_comp G) rfl

end GroupScheme

end AlgebraicGeometry
