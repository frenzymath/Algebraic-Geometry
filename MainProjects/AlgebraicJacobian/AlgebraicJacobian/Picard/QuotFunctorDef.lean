/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.GenericFlatnessGeometric
import AlgebraicJacobian.Picard.GlueDescent
import AlgebraicJacobian.Picard.PullbackFinitePresentation
import AlgebraicJacobian.Picard.QuotFlatBaseChange
import AlgebraicJacobian.Picard.QuotSupportBaseChange
import AlgebraicJacobian.Picard.SchematicSupport
import AlgebraicJacobian.Picard.TensorObjSubstrate

/-!
# The Quot functor and the relative Grassmannian functor

This file constructs the two headline *definitions* of the A.2.b Quot-scheme
chapter (`blueprint/src/chapters/Picard_QuotScheme.tex`):

* `AlgebraicGeometry.Scheme.QuotFunctor` (`def:quot_functor`) — the Quot
  functor `Quot^{Φ,L}_{E/X/S} : (Sch/S)ᵒᵖ ⥤ Type (u+1)` of `T`-flat, finitely
  presented quotients `q : E_T ↠ F` on `X_T = X ×_S T` with proper support
  and fibrewise Hilbert polynomial `Φ`, modulo `ker q = ker q'`;
* `AlgebraicGeometry.Scheme.Grassmannian` (`def:grassmannian_scheme`) — the
  relative Grassmannian functor `Grass(V, d) : (Sch/S)ᵒᵖ ⥤ Type (u+1)` of
  rank-`d` locally free quotients of `V_T` on `T`.

Universe note: the value category is `Type (u+1)`, not `Type u` — a sheaf of
modules on a scheme in `Scheme.{u}` is a large object, so the quotient sets
live one universe up.  The same shift occurs for the absolute Grassmannian
functor (`AlgebraicGeometry.Grassmannian.functor`, `GrassmannianQuot.lean`)
and for `picSharp` (`FGAPicRepresentability.lean`); `Functor.RepresentableBy`
is universe-polymorphic, so the representability statements are unaffected.

## Design

A single family of quotients over `T : Over S` is the structure
`Scheme.QuotFamily π L E Φ T` (Nitsure §1, "family of quotients of `E`
parametrised by `T`"): a sheaf `F` on the relative product
`X_T := pullback π T.hom` that is finitely presented
(`SheafOfModules.IsFinitePresentation` — the coherence encoding used by the
flattening-stratification input), flat over `T`
(`Scheme.CoherentSheafFlat (pullback.snd π T.hom) F`), with proper support
(`Scheme.Modules.HasProperSupport`), together with an epimorphism
`q : E_T ⟶ F` from `E_T := (pullback.fst π T.hom)^* E`, such that at every
`t : T` the graded Hilbert function of the fibre `F_t` twisted by `L_t`
*eventually agrees* with `Φ` (`Scheme.hilbertFunction`; by
`Scheme.hilbertPolynomial_eq_of_eventually` this eventual-match encoding is
exactly the statement "the Hilbert polynomial of `F|_{X_t}` equals `Φ`" of
`def:quot_functor`, and it excludes the junk-value coincidence `Φ = 0`).

Two families are equivalent when an isomorphism of the targets commutes with
the quotient maps (equivalently, `ker q = ker q'` — same convention as the
absolute Grassmannian `RankQuotient.Rel`).  The functor value at `T` is
the quotient by this relation; the morphism action pulls a family back along
the induced morphism on relative products `Scheme.quotBaseMap π ψ` (with the
`E`-side matched through the pullback pseudofunctor comparisons
`Scheme.Modules.pullbackComp` / `pullbackCongr`).

The well-definedness of the pullback action rests on four base-change
preservation facts (Nitsure §1: "as properness and flatness are preserved by
base-change, and as tensor-product is right exact, the pull-back of
`⟨F, q⟩` … is well-defined"):

1. surjectivity: pullback is a left adjoint, hence preserves epimorphisms
   (proved inline);
2. finite presentation: `Scheme.Modules.pullback_isFinitePresentation`
   (right-exactness of pullback; the per-slice transport of
   `Cohomology/PullbackQuasicoherent.lean` with finiteness tracking);
3. flatness: `Scheme.CoherentSheafFlat.of_isPullback` (Stacks 01U9 lifted to
   the sheaf predicate);
4. proper support: `Scheme.Modules.HasProperSupport.of_isPullback`
   (properness is stable under base change; the schematic support of the
   pullback closed-immerses into the base change of the schematic support);
5. fibrewise Hilbert polynomials: `Scheme.hilbertFunction_quotBaseMap`
   (the fibre of `X_{T'} → T'` at `t'` is the base change of the fibre of
   `X_T → T` at `ψ(t')` along the residue extension `κ(ψ t') → κ(t')`, and
   `H⁰` of a module with proper support is invariant under base field
   extension — flat base change over a field).

Item 1 is proved inline; item 2 is proved in
`Picard/PullbackFinitePresentation.lean` (per-layer `IsFinite` instances for
the presentation transports); item 3 is proved in
`Picard/QuotFlatBaseChange.lean` (assembly of the pullback-piece and
affine-cover flatness engines of `GenericFlatnessGeometric.lean`); item 4 is
proved in `Picard/QuotSupportBaseChange.lean`
(`Scheme.Modules.HasProperSupport.of_isPullback`, re-exported by the import);
item 5 is proved by the fibre-pasting assembly of §2, modulo the two
obligations this file still leaves open (`sorry`): the tensor–pullback
compatibility `Scheme.Modules.pullbackTensorMap_isIso` (invertibility of the
canonical comparison, to which the twist statement
`Scheme.Modules.pullback_moduleTensorPow_iso` is reduced by the `m`-recursion
assembly of §2) and the `Γ`-base-change core
`Scheme.gammaFiber_finrank_baseChange_field`.  Both are standard facts of
[Stacks] / [Nitsure], cited at their declarations.

The functor identities reduce to the pseudofunctor coherence laws of
`Scheme.Modules.pullback` (`pseudofunctor_right_unitality` /
`pseudofunctor_associativity`), packaged once as the app-level lemmas
`Scheme.Modules.pullback_id_app_coherence` and
`Scheme.Modules.pullback_comp_app_coherence` and consumed by both functors.

## References

Blueprint: `def:quot_functor`, `def:grassmannian_scheme`,
`thm:grassmannian_representable`, `thm:quot_representable`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
Source: [Nitsure], §1 (FGA Explained Ch. 5, arXiv:math/0504020).
-/

set_option autoImplicit false

universe u u₁ u₂ v₁ v₂

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-! ## §0. App-level pseudofunctor coherence for the module pullback

Mathlib provides the pseudofunctor coherence laws for
`Scheme.Modules.pullback` at the natural-transformation level
(`Scheme.Modules.pseudofunctor_right_unitality`,
`Scheme.Modules.pseudofunctor_associativity`).  The functor laws of the Quot
and Grassmannian functors need them in *component* form, conjugated by the
`eqToIso`-valued comparison `Scheme.Modules.pullbackCongr` along the triangle
identities of the relevant scheme morphisms.  We package the two required
shapes once. -/

namespace Modules

/-- Component form of `Scheme.Modules.pullbackCongr`: it is an `eqToHom`. -/
lemma pullbackCongr_hom_app {Y X : Scheme.{u}} {f g : Y ⟶ X} (h : f = g)
    (M : X.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M = eqToHom (by rw [h]) := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- Component form of `Scheme.Modules.pullbackCongr`, inverse direction. -/
lemma pullbackCongr_inv_app {Y X : Scheme.{u}} {f g : Y ⟶ X} (h : f = g)
    (M : X.Modules) :
    (Scheme.Modules.pullbackCongr h).inv.app M = eqToHom (by rw [h]) := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

set_option backward.isDefEq.respectTransparency false in
/-- **Identity coherence, component form.**  For a scheme endomorphism `f'`
equal to the identity and a morphism `g` with `f' ≫ g = g`, the composite of
the pseudofunctor comparisons collapsing `f'^* g^* V` back to `g^* V` is the
identity.  This is `pseudofunctor_right_unitality` conjugated by
`pullbackCongr`; it discharges the `map_id` law of both the Quot and the
Grassmannian functor. -/
lemma pullback_id_app_coherence {Y W : Scheme.{u}} {f' : Y ⟶ Y} (hf : f' = 𝟙 Y)
    {g : Y ⟶ W} (hgc : f' ≫ g = g) (V : W.Modules) :
    (Scheme.Modules.pullbackCongr hgc).inv.app V ≫
      (Scheme.Modules.pullbackComp f' g).inv.app V ≫
      (Scheme.Modules.pullbackCongr hf).hom.app ((Scheme.Modules.pullback g).obj V) ≫
      (Scheme.Modules.pullbackId Y).hom.app ((Scheme.Modules.pullback g).obj V) =
    𝟙 ((Scheme.Modules.pullback g).obj V) := by
  subst hf
  have law := Scheme.Modules.pseudofunctor_right_unitality (f := g)
  have lawV := congrArg (fun η => η.app V) law
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at lawV
  rw [pullbackCongr_inv_app hgc, pullbackCongr_hom_app rfl]
  simp only [eqToHom_refl, Category.id_comp]
  simp only [eqToHom_refl] at lawV
  exact lawV

set_option backward.isDefEq.respectTransparency false in
/-- **Composition coherence, component form.**  For composable scheme
morphisms `a`, `b`, a morphism `c` equal to `a ≫ b`, and a reference morphism
`g`, the two ways of collapsing `a^* b^* g^* V` to `(c ≫ g)^* V` through the
pseudofunctor comparisons agree.  This is `pseudofunctor_associativity`
conjugated by `pullbackCongr`; it discharges the `map_comp` law of both the
Quot and the Grassmannian functor. -/
lemma pullback_comp_app_coherence {W Xs Y Z : Scheme.{u}} (a : Z ⟶ Y) (b : Y ⟶ Xs)
    {c : Z ⟶ Xs} (hc : c = a ≫ b) (g : Xs ⟶ W) {gb : Y ⟶ W} {gc : Z ⟶ W}
    (h₁ : b ≫ g = gb) (h₂ : c ≫ g = gc) (h₃ : a ≫ gb = gc) (V : W.Modules) :
    (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback g).obj V) ≫
      (Scheme.Modules.pullbackCongr hc).inv.app ((Scheme.Modules.pullback g).obj V) ≫
      (Scheme.Modules.pullbackComp c g).hom.app V ≫
      (Scheme.Modules.pullbackCongr h₂).hom.app V =
    (Scheme.Modules.pullback a).map
        ((Scheme.Modules.pullbackComp b g).hom.app V ≫
          (Scheme.Modules.pullbackCongr h₁).hom.app V) ≫
      (Scheme.Modules.pullbackComp a gb).hom.app V ≫
      (Scheme.Modules.pullbackCongr h₃).hom.app V := by
  subst hc
  subst h₁
  subst h₃
  -- the associativity law, in component form at `V`
  have law := Scheme.Modules.pseudofunctor_associativity (f := a) (g := b) (h := g)
  have lawV := congrArg (fun η => η.app V) law
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, eqToHom_app] at lawV
  simp only [Category.id_comp] at lawV
  -- `lawV : (pullbackComp a (b ≫ g)).inv.app V ≫
  --   (pullback a).map ((pullbackComp b g).inv.app V) ≫
  --   (pullbackComp a b).hom.app (g^* V) ≫ (pullbackComp (a ≫ b) g).hom.app V
  --   = eqToHom _`
  -- move the two invertible prefixes of `lawV` to the right-hand side
  have h1 := congrArg
    (fun m => (Scheme.Modules.pullbackComp a (b ≫ g)).hom.app V ≫ m) lawV
  simp only [Iso.hom_inv_id_app_assoc] at h1
  have h2 := congrArg
    (fun m => (Scheme.Modules.pullback a).map
      ((Scheme.Modules.pullbackComp b g).hom.app V) ≫ m) h1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at h2
  -- `h2 : (pullbackComp a b).hom.app (g^* V) ≫ (pullbackComp (a ≫ b) g).hom.app V
  --   = (pullback a).map ((pullbackComp b g).hom.app V) ≫
  --     (pullbackComp a (b ≫ g)).hom.app V ≫ eqToHom _`
  -- normalize all `pullbackCongr` occurrences to `eqToHom`s and conclude
  simp only [pullbackCongr_hom_app, pullbackCongr_inv_app, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  simpa using h2

set_option backward.isDefEq.respectTransparency false in
/-- Inverse-composite form of `pullback_comp_app_coherence`, in the exact shape
consumed by the `map_comp` law of the Quot and Grassmannian functors. -/
lemma pullback_comp_app_coherence_inv {W Xs Y Z : Scheme.{u}} (a : Z ⟶ Y) (b : Y ⟶ Xs)
    {c : Z ⟶ Xs} (hc : c = a ≫ b) (g : Xs ⟶ W) {gb : Y ⟶ W} {gc : Z ⟶ W}
    (h₁ : b ≫ g = gb) (h₂ : c ≫ g = gc) (h₃ : a ≫ gb = gc) (V : W.Modules) :
    (Scheme.Modules.pullbackCongr h₂).inv.app V ≫
      (Scheme.Modules.pullbackComp c g).inv.app V ≫
      (Scheme.Modules.pullbackCongr hc).hom.app ((Scheme.Modules.pullback g).obj V) ≫
      (Scheme.Modules.pullbackComp a b).inv.app ((Scheme.Modules.pullback g).obj V) =
    (Scheme.Modules.pullbackCongr h₃).inv.app V ≫
      (Scheme.Modules.pullbackComp a gb).inv.app V ≫
      (Scheme.Modules.pullback a).map
        ((Scheme.Modules.pullbackCongr h₁).inv.app V ≫
          (Scheme.Modules.pullbackComp b g).inv.app V) := by
  subst hc
  subst h₁
  subst h₃
  have law := Scheme.Modules.pseudofunctor_associativity (f := a) (g := b) (h := g)
  have lawV := congrArg (fun η => η.app V) law
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, eqToHom_app] at lawV
  simp only [Category.id_comp] at lawV
  -- compose `lawV` on the right with the two inverses to isolate the prefix
  have k1 := congrArg
    (fun m => m ≫ (Scheme.Modules.pullbackComp (a ≫ b) g).inv.app V) lawV
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at k1
  have k2 := congrArg
    (fun m => m ≫ (Scheme.Modules.pullbackComp a b).inv.app
      ((Scheme.Modules.pullback g).obj V)) k1
  simp only [Category.assoc, Iso.hom_inv_id_app] at k2
  -- normalize all `pullbackCongr` occurrences to `eqToHom`s and conclude
  simp only [pullbackCongr_hom_app, pullbackCongr_inv_app, eqToHom_refl,
    Category.id_comp]
  exact k2.symm

end Modules

/-! ## §1. The induced morphism on relative products

For the Quot functor over `T : Over S`, the family lives on the relative
product `X_T := pullback π T.hom`; a morphism `ψ : T' ⟶ T` of `Over S`
induces `Scheme.quotBaseMap π ψ : X_{T'} ⟶ X_T` (the map `id_X ×_S ψ`),
functorially, compatibly with both projections, and cartesian over
`ψ.left : T' ⟶ T` (`Scheme.quotBaseSquare`). -/

variable {S X : Scheme.{u}}

/-- The morphism `X ×_S T' ⟶ X ×_S T` induced by `ψ : T' ⟶ T` in `Over S`
(the map `id_X ×_S ψ.left`). -/
noncomputable def quotBaseMap (π : X ⟶ S) {T T' : Over S} (ψ : T' ⟶ T) :
    (Limits.pullback π T'.hom : Scheme.{u}) ⟶ Limits.pullback π T.hom :=
  Limits.pullback.map π T'.hom π T.hom (𝟙 X) ψ.left (𝟙 S) (by simp)
    (by simp)

@[reassoc]
lemma quotBaseMap_fst (π : X ⟶ S) {T T' : Over S} (ψ : T' ⟶ T) :
    quotBaseMap π ψ ≫ pullback.fst π T.hom = pullback.fst π T'.hom := by
  simp [quotBaseMap, pullback.lift_fst]

@[reassoc]
lemma quotBaseMap_snd (π : X ⟶ S) {T T' : Over S} (ψ : T' ⟶ T) :
    quotBaseMap π ψ ≫ pullback.snd π T.hom = pullback.snd π T'.hom ≫ ψ.left := by
  simp [quotBaseMap, pullback.lift_snd]

lemma quotBaseMap_id (π : X ⟶ S) (T : Over S) :
    quotBaseMap π (𝟙 T) = 𝟙 (Limits.pullback π T.hom) := by
  apply pullback.hom_ext <;>
    simp [quotBaseMap]

lemma quotBaseMap_comp (π : X ⟶ S) {T T' T'' : Over S} (ψ : T' ⟶ T) (φ : T'' ⟶ T') :
    quotBaseMap π (φ ≫ ψ) = quotBaseMap π φ ≫ quotBaseMap π ψ := by
  apply pullback.hom_ext <;>
    simp [quotBaseMap, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_snd_assoc]

/-- The square
```
X ×_S T' ──quotBaseMap──→ X ×_S T
   │                         │
  snd                       snd
   ↓                         ↓
   T' ────────ψ.left───────→ T
```
is cartesian: `X ×_S T' = (X ×_S T) ×_T T'`.  This is the square along which
flatness and proper support of a Quot family base-change. -/
lemma quotBaseSquare (π : X ⟶ S) {T T' : Over S} (ψ : T' ⟶ T) :
    IsPullback (quotBaseMap π ψ) (pullback.snd π T'.hom)
      (pullback.snd π T.hom) ψ.left := by
  have s : IsPullback (quotBaseMap π ψ ≫ pullback.fst π T.hom)
      (pullback.snd π T'.hom) π (ψ.left ≫ T.hom) := by
    rw [quotBaseMap_fst, Over.w]
    exact IsPullback.of_hasPullback π T'.hom
  exact IsPullback.of_right s (quotBaseMap_snd π ψ) (IsPullback.of_hasPullback π T.hom)

/-- The comparison isomorphism `b^* g^* V ≅ (gb)^* V` attached to a commuting
triangle `b ≫ g = gb` of schemes: the pullback pseudofunctor comparison
`pullbackComp` followed by transport `pullbackCongr` along the triangle.
Instantiated with `Over.w ψ` it matches the test modules `V_T` of the
Grassmannian functor, and with `quotBaseMap_fst` the pulled-back sheaves
`E_T`, `L_T` of the Quot functor. -/
noncomputable def pullbackTriangleIso {Z Y W : Scheme.{u}} {b : Z ⟶ Y} {g : Y ⟶ W}
    {gb : Z ⟶ W} (h : b ≫ g = gb) (V : W.Modules) :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback g).obj V) ≅
      (Scheme.Modules.pullback gb).obj V :=
  (Scheme.Modules.pullbackComp b g).app V ≪≫ (Scheme.Modules.pullbackCongr h).app V

/-! ## §2. Base-change preservation of the Quot-family conditions

Nitsure §1: "as properness and flatness are preserved by base-change, and as
tensor-product is right exact, the pull-back of `⟨F, q⟩` … is well-defined."
The four preservation facts, in the forms consumed by the pullback action of
the Quot functor.  Finite presentation
(`Scheme.Modules.pullback_isFinitePresentation`, together with the per-slice
transport `Modules.pullbackSlicePresentation` and its finiteness) is proved in
`Picard/PullbackFinitePresentation.lean`; flatness
(`Scheme.CoherentSheafFlat.of_isPullback`) is proved in
`Picard/QuotFlatBaseChange.lean`; proper support
(`Scheme.Modules.HasProperSupport.of_isPullback`) is proved in
`Picard/QuotSupportBaseChange.lean` (blueprint node
`lem:proper_support_base_change`); all three are re-exported here by the
imports.  The Hilbert-function invariance (item 5, blueprint node
`lem:hilbert_fibre_base_change`) is proved below by pasting the fibre squares
(`Scheme.fiberBaseChange`) and transporting dimensions across the comparison
isomorphisms, modulo the two obligations left open in this file (blueprint
nodes `lem:pullback_tensor_map_isiso` — the canonical-comparison
invertibility to which `lem:pullback_moduleTensorPow` is reduced — and
`lem:gamma_fiber_baseChange_field`). -/

/- **Proper support is stable under base change** (Nitsure §1; Stacks 01W4 +
056H; blueprint `lem:proper_support_base_change`) is
`Scheme.Modules.HasProperSupport.of_isPullback` of
`AlgebraicJacobian/Picard/QuotSupportBaseChange.lean`, re-exported here by
the import. -/

/-! ### Base change of the fibrewise graded Hilbert function

Ingredients for `Scheme.hilbertFunction_quotBaseMap` below: the fibre of
`X_{T'} → T'` at `t'` is the base change of the fibre of `X_T → T` at
`t := ψ(t')` along the residue field extension `κ(t) → κ(t')`
(`Scheme.fiberBaseChange`, cartesian by `Scheme.isPullback_fiberBaseChange` —
the pasting of `Scheme.quotBaseSquare` with Mathlib's residue-field square).
The two restrictions are matched across this identification by pseudofunctor
coherence (`Scheme.pullbackSquareIso`); their twists by the congruence isos
of the sheaf tensor product (`Scheme.Modules.moduleTensorPowCongr`) together
with the tensor-compatibility statement
(`Scheme.Modules.pullback_moduleTensorPow_iso`, obtained from the canonical
comparison `Scheme.Modules.pullbackTensorMap_isIso` by induction on the
twisting exponent); and the dimension count is transported along the
resulting isomorphism (`Scheme.hilbertFunction_eq_finrank_of_iso`) and
delegated to the base-change statement for `Γ`
(`Scheme.gammaFiber_finrank_baseChange_field`). -/

section HilbertFunctionBaseChange

/-- The comparison isomorphism `b^* g^* V ≅ b'^* g'^* V` attached to a
commuting square `b ≫ g = b' ≫ g'` of schemes: two `pullbackTriangleIso`s
through the common composite.  Pure pseudofunctor coherence, in the rw-free
form consumed by the fibrewise base-change bookkeeping below. -/
noncomputable def pullbackSquareIso {Z Y Y' W : Scheme.{u}} {b : Z ⟶ Y} {g : Y ⟶ W}
    {b' : Z ⟶ Y'} {g' : Y' ⟶ W} (h : b ≫ g = b' ≫ g') (V : W.Modules) :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback g).obj V) ≅
      (Scheme.Modules.pullback b').obj ((Scheme.Modules.pullback g').obj V) :=
  pullbackTriangleIso (rfl : b ≫ g = b ≫ g) V ≪≫
    (Scheme.Modules.pullbackCongr h).app V ≪≫
    (pullbackTriangleIso (rfl : b' ≫ g' = b' ≫ g') V).symm

set_option backward.isDefEq.respectTransparency false in
/-- Congruence of the sheaf tensor product (`Scheme.Modules.sheafTensorObj`)
along isomorphisms of the two factors: the image under sheafification of the
presheaf-level tensor product of the isomorphisms. -/
noncomputable def Modules.sheafTensorObjCongr {Z : Scheme.{u}} {A A' B B' : Z.Modules}
    (e : A ≅ A') (f : B ≅ B') :
    Modules.sheafTensorObj A B ≅ Modules.sheafTensorObj A' B' :=
  Modules.sheafification.mapIso
    (MonoidalCategory.tensorIso
      (C := _root_.PresheafOfModules.{u} (Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
      ((Modules.toPresheafOfModules Z).mapIso e) ((Modules.toPresheafOfModules Z).mapIso f))

/-- Congruence of the tensor powers (`Scheme.Modules.tensorPow`) along an
isomorphism of the base module. -/
noncomputable def Modules.tensorPowCongr {Z : Scheme.{u}} {L L' : Z.Modules} (e : L ≅ L') :
    (m : ℕ) → (Modules.tensorPow L m ≅ Modules.tensorPow L' m)
  | 0 => Iso.refl _
  | (m + 1) => Modules.sheafTensorObjCongr (Modules.tensorPowCongr e m) e

/-- Congruence of the twists `F ⊗ L^{⊗m}` (`Scheme.Modules.moduleTensorPow`)
along isomorphisms of both modules. -/
noncomputable def Modules.moduleTensorPowCongr {Z : Scheme.{u}} {F F' L L' : Z.Modules}
    (eF : F ≅ F') (eL : L ≅ L') (m : ℕ) :
    Modules.moduleTensorPow F L m ≅ Modules.moduleTensorPow F' L' m :=
  Modules.sheafTensorObjCongr eF (Modules.tensorPowCongr eL m)

/-! #### Reduction of the tensor–pullback compatibility to the canonical comparison

The tensor–pullback compatibility `Scheme.Modules.pullback_moduleTensorPow_iso`
below (Stacks 01CD for the twists `F ⊗ L^{⊗m}`) reduces, by induction on `m`,
to the *binary* case — invertibility of the canonical sheaf-level
pullback–tensor comparison `Scheme.Modules.pullbackTensorMap` built in
`Picard/TensorObjSubstrate.lean` (the sheafified mate of the lax monoidal
structure of the pushforward) — together with the unit case `f^*𝒪_Z ≅ 𝒪_Y`,
which is `Scheme.Modules.pullbackUnitIso` (the comparison functor on opens is
always `Final`).  The tensor `Scheme.Modules.tensorObj` is definitionally
equal to the section-graded `Scheme.Modules.sheafTensorObj` (both sheafify
the presheaf-level tensor of the underlying presheaves), so `asIso` of the
canonical comparison re-types at `sheafTensorObj` directly.  Invertibility of
that comparison, `Scheme.Modules.pullbackTensorMap_isIso` just below, is the
one statement of this section that remains unproved (blueprint
`lem:pullback_tensor_map_isiso`). -/

set_option backward.isDefEq.respectTransparency false in
/-- **The canonical pullback–tensor comparison is an isomorphism**
([Stacks 01CD] = Modules, Lemma `tensor-product-pullback`, which is
unconditional: the canonical comparison map is invertible for arbitrary
sheaves of modules on ringed spaces; stalkwise it is the base-change
isomorphism of tensor products, via [Stacks 01CB] + [Stacks 0098]): for a
morphism of schemes `f : Y ⟶ Z` and `A B : Z.Modules`, the sheaf-level
comparison `Scheme.Modules.pullbackTensorMap f A B :
f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` of `Picard/TensorObjSubstrate.lean` is an
isomorphism.

This statement is not proved here; it is one of the two obligations this file
leaves open.  The obstruction is that the Lean pullback functor is an
*abstract* left adjoint with no sectionwise value, so invertibility cannot be
checked on sections directly.  Three reductions of the statement are
available: (i) a chart-chase generalizing
`Modules.pullbackTensorIsoOfLocallyTrivial` from trivializing charts to
affine charts, using `Modules.pullback_app_isoTensor` on the pullback side
and a `Γ(affine, tensorObj)` section formula for quasi-coherent factors, then
globalized by `isIso_of_isIso_restrict` through the restriction coherence
`Modules.pullbackTensorMap_restrict`; (ii) the concrete inverse-image model
`extendScalars ⋙ pullback₀` as a left Kan extension
(`sec:tensorobj_pullback_monoidality`); (iii) stalkwise, which needs stalk
machinery for `SheafOfModules` that Mathlib does not currently have (the
presheaf-level comparison map is in `TensorObjSubstrate/StalkTensor.lean`).
Blueprint: `lem:pullback_tensor_map_isiso`. -/
theorem Modules.pullbackTensorMap_isIso {Z Y : Scheme.{u}} (f : Y ⟶ Z) (A B : Z.Modules) :
    IsIso (Modules.pullbackTensorMap f A B) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **Pullback commutes with the binary sheaf tensor product**: the
`sheafTensorObj`-typed `Iso` packaging of `Modules.pullbackTensorMap_isIso`.
The tensor `Modules.tensorObj` and the section-graded
`Modules.sheafTensorObj` are definitionally equal, so `asIso` of the canonical
comparison `Modules.pullbackTensorMap` re-types at `sheafTensorObj` without a
bridge.  (The `IsIso` witness is passed explicitly to `asIso`, so that no
instance synthesis runs on it.) -/
noncomputable def Modules.pullbackSheafTensorIso {Z Y : Scheme.{u}} (f : Y ⟶ Z)
    (A B : Z.Modules) :
    (Scheme.Modules.pullback f).obj (Modules.sheafTensorObj A B) ≅
      Modules.sheafTensorObj ((Scheme.Modules.pullback f).obj A)
        ((Scheme.Modules.pullback f).obj B) :=
  @asIso _ _ _ _ (Modules.pullbackTensorMap f A B) (Modules.pullbackTensorMap_isIso f A B)

set_option backward.isDefEq.respectTransparency false in
/-- **Pullback commutes with tensor powers**: `f^*(L^{⊗m}) ≅ (f^*L)^{⊗m}`, by
induction on `m` from the unit case (`Modules.pullbackUnitIso`, from
`TensorObjSubstrate.lean`) and the binary case
(`Modules.pullbackSheafTensorIso`, which rests on
`Modules.pullbackTensorMap_isIso`), the isomorphisms being pushed through
the recursion `L^{⊗(m+1)} = L^{⊗m} ⊗ L` by the tensor congruence
`Modules.sheafTensorObjCongr`. -/
noncomputable def Modules.pullbackTensorPowIso {Z Y : Scheme.{u}} (f : Y ⟶ Z)
    (L : Z.Modules) :
    (m : ℕ) → ((Scheme.Modules.pullback f).obj (Modules.tensorPow L m) ≅
      Modules.tensorPow ((Scheme.Modules.pullback f).obj L) m)
  | 0 => Modules.pullbackUnitIso f
  | (m + 1) =>
      Modules.pullbackSheafTensorIso f (Modules.tensorPow L m) L ≪≫
        Modules.sheafTensorObjCongr (Modules.pullbackTensorPowIso f L m) (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- **Pullback commutes with the sheaf tensor product and its twists**
([Stacks 01CD] = Modules, Lemma `tensor-product-pullback`; the stalkwise
description is [Stacks 01CB] + [Stacks 0098]): for a morphism of schemes
`f : Y ⟶ X` and quasi-coherent modules `F`, `L` on `X`, the pullback of the
`m`-th twist `F ⊗ L^{⊗m}` (`Scheme.Modules.moduleTensorPow`) is isomorphic to
the twist of the pullbacks.  The cited Stacks lemma is stronger — the
canonical comparison map is an isomorphism for arbitrary sheaves of modules
on ringed spaces — but the quasi-coherent `Nonempty`-of-isomorphism form
recorded here is all the Hilbert-function base-change argument needs.

The proof is the recursion on `m` built from
`Modules.pullbackSheafTensorIso` (binary case),
`Modules.pullbackTensorPowIso` (powers) and `Modules.sheafTensorObjCongr`
(congruence); it therefore rests on the single narrower unproved statement
`Modules.pullbackTensorMap_isIso` above (invertibility of the canonical
comparison).  The quasi-coherence hypotheses are not consumed by this
argument; they are kept because the statement is fixed by its callers.
Blueprint: `lem:pullback_moduleTensorPow`. -/
theorem Modules.pullback_moduleTensorPow_iso {Z Y : Scheme.{u}} (f : Y ⟶ Z)
    (F L : Z.Modules) [F.IsQuasicoherent] [L.IsQuasicoherent] (m : ℕ) :
    Nonempty ((Scheme.Modules.pullback f).obj (Modules.moduleTensorPow F L m) ≅
      Modules.moduleTensorPow ((Scheme.Modules.pullback f).obj F)
        ((Scheme.Modules.pullback f).obj L) m) :=
  ⟨Modules.pullbackSheafTensorIso f F (Modules.tensorPow L m) ≪≫
    Modules.sheafTensorObjCongr (Iso.refl _) (Modules.pullbackTensorPowIso f L m)⟩

/-- The canonical morphism from the fibre of `X_{T'} → T'` at `t'` to the
fibre of `X_T → T` at `t := ψ(t')`, induced by `quotBaseMap π ψ` on total
spaces and by the residue field extension `κ(t) ⟶ κ(t')` on the bases.  By
`Scheme.isPullback_fiberBaseChange` it exhibits its source as the base change
of its target along `Spec κ(t') ⟶ Spec κ(t)`. -/
noncomputable def fiberBaseChange (π : X ⟶ S) {T T' : Over S} (ψ : T' ⟶ T)
    (t' : (T'.left : Scheme.{u})) :
    (pullback.snd π T'.hom).fiber t' ⟶ (pullback.snd π T.hom).fiber (ψ.left.base t') :=
  pullback.map (pullback.snd π T'.hom) (T'.left.fromSpecResidueField t')
    (pullback.snd π T.hom) (T.left.fromSpecResidueField (ψ.left.base t'))
    (quotBaseMap π ψ) (Spec.map (ψ.left.residueFieldMap t')) ψ.left
    (quotBaseSquare π ψ).w.symm (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- **Fibre pasting**: the fibre of `X_{T'} → T'` at `t'` is the base change
of the fibre of `X_T → T` at `t = ψ(t')` along the residue field extension
`κ(t) → κ(t')`.  Pasting of the cartesian square `Scheme.quotBaseSquare` with
Mathlib's residue-field square
(`AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback`). -/
lemma isPullback_fiberBaseChange (π : X ⟶ S) {T T' : Over S} (ψ : T' ⟶ T)
    (t' : (T'.left : Scheme.{u})) :
    IsPullback (fiberBaseChange π ψ t')
      ((pullback.snd π T'.hom).fiberToSpecResidueField t')
      ((pullback.snd π T.hom).fiberToSpecResidueField (ψ.left.base t'))
      (Spec.map (ψ.left.residueFieldMap t')) :=
  isPullback_fiberToSpecResidueField_of_isPullback (quotBaseSquare π ψ) t'

@[reassoc]
lemma fiberBaseChange_fiberι (π : X ⟶ S) {T T' : Over S} (ψ : T' ⟶ T)
    (t' : (T'.left : Scheme.{u})) :
    fiberBaseChange π ψ t' ≫ (pullback.snd π T.hom).fiberι (ψ.left.base t')
      = (pullback.snd π T'.hom).fiberι t' ≫ quotBaseMap π ψ :=
  pullback.lift_fst _ _ _

lemma fiberBaseChange_fiberι_fst (π : X ⟶ S) {T T' : Over S} (ψ : T' ⟶ T)
    (t' : (T'.left : Scheme.{u})) :
    (pullback.snd π T'.hom).fiberι t' ≫ pullback.fst π T'.hom
      = fiberBaseChange π ψ t' ≫
          ((pullback.snd π T.hom).fiberι (ψ.left.base t') ≫ pullback.fst π T.hom) := by
  rw [← Category.assoc, fiberBaseChange_fiberι, Category.assoc, quotBaseMap_fst]

set_option backward.isDefEq.respectTransparency false in
/-- Transport of the graded Hilbert function along an isomorphism of the
twisted fibre module: an isomorphism of sheaves of modules on the fibre
induces a `κ(s)`-linear equivalence on global sections (evaluation at `⊤` is
functorial, and the `κ(s)`-scalar action factors through
`Scheme.Hom.fiberResidueMap`), so the `κ(s)`-dimensions agree. -/
lemma hilbertFunction_eq_finrank_of_iso {W B : Scheme.{u}} (π₀ : W ⟶ B)
    (L₀ F₀ : W.Modules) (s : B) (m : ℕ) {G : (π₀.fiber s).Modules}
    (e : Scheme.Modules.moduleTensorPow (π₀.fiberModule s F₀) (π₀.fiberModule s L₀) m ≅ G) :
    hilbertFunction π₀ L₀ F₀ s m
      = (letI := π₀.fiberSectionsModule s G
         Module.finrank (B.residueField s) Γ(G, ⊤)) := by
  letI := π₀.fiberSectionsModule s
    (Scheme.Modules.moduleTensorPow (π₀.fiberModule s F₀) (π₀.fiberModule s L₀) m)
  letI := π₀.fiberSectionsModule s G
  have γe := ((Modules.toPresheafOfModules (π₀.fiber s) ⋙
    PresheafOfModules.evaluation (π₀.fiber s).ringCatSheaf.obj (Opposite.op ⊤)).mapIso
      e).toLinearEquiv
  exact LinearEquiv.finrank_eq
    { toFun := γe
      map_add' := γe.map_add
      map_smul' := fun c x => γe.map_smul ((π₀.fiberResidueMap s).hom c) x
      invFun := γe.symm
      left_inv := γe.left_inv
      right_inv := γe.right_inv }

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- fibre-square properness transfer + defeq instantiation of the Γ-fibre core
/-- **Flat base change of the global sections of the twisted fibre module,
conditional on quasi-coherence of the twist** — the scheme-level content of
`lem:gamma_fiber_baseChange_field`, of which this carries the whole geometric
argument:

* proper support transfers from `F/T` to the fibre restriction `F_t/κ(t)`
  (`Modules.HasProperSupport.of_isPullback` on Mathlib's fibre square) and on
  to the twist `F_t ⊗ L_t^{⊗m}` (`hasProperSupport_moduleTensorPow`, by
  monotonicity of the annihilator);
* the flat base-change statement for `Γ` on a fibre
  (`Scheme.finrank_gammaTop_baseChange_of_hasProperSupport` — support descent
  `G ≅ i_* i^* G`, the [Stacks 02KH] exchange across the closed-immersion
  square, [Stacks 02KE] at `⊤` on the pasted proper-support square, and the
  `ΓSpecIso` dimension bookkeeping) applies to Mathlib's cartesian fibre
  square `Scheme.isPullback_fiberBaseChange`, whose corners instantiate
  `K := κ(t)`, `K' := κ(t')`, `φ := ψ.residueFieldMap`; the
  `fiberSectionsModule`/`fiberResidueMap` scalar actions are *definitionally*
  the `ΓSpecIso⁻¹ ≫ appTop` composites of that statement.

The remaining input, taken here as the hypothesis `hGqc`, is quasi-coherence
of the twisted fibre module.  It follows from `[L.IsQuasicoherent]` and finite
presentation of `F` once the affine section formula for `sheafTensorObj` of
quasi-coherent modules ([Stacks 01CB], `Picard/TensorSectionFormula.lean`) is
available; that formula is also what `lem:pullback_tensor_map_isiso` needs. -/
theorem gammaFiber_finrank_baseChange_field_of_quasicoherent (π : X ⟶ S)
    (L : X.Modules) {T T' : Over S} (ψ : T' ⟶ T)
    (F : (Limits.pullback π T.hom).Modules) (hfp : F.IsFinitePresentation)
    (hps : Modules.HasProperSupport (pullback.snd π T.hom) F)
    (t' : (T'.left : Scheme.{u})) (m : ℕ)
    (hGqc : (Scheme.Modules.moduleTensorPow
        ((pullback.snd π T.hom).fiberModule (ψ.left.base t') F)
        ((pullback.snd π T.hom).fiberModule (ψ.left.base t')
          ((Scheme.Modules.pullback (pullback.fst π T.hom)).obj L))
        m).IsQuasicoherent) :
    (letI := (pullback.snd π T'.hom).fiberSectionsModule t'
        ((Scheme.Modules.pullback (fiberBaseChange π ψ t')).obj
          (Scheme.Modules.moduleTensorPow
            ((pullback.snd π T.hom).fiberModule (ψ.left.base t') F)
            ((pullback.snd π T.hom).fiberModule (ψ.left.base t')
              ((Scheme.Modules.pullback (pullback.fst π T.hom)).obj L)) m))
     Module.finrank (T'.left.residueField t')
        Γ((Scheme.Modules.pullback (fiberBaseChange π ψ t')).obj
          (Scheme.Modules.moduleTensorPow
            ((pullback.snd π T.hom).fiberModule (ψ.left.base t') F)
            ((pullback.snd π T.hom).fiberModule (ψ.left.base t')
              ((Scheme.Modules.pullback (pullback.fst π T.hom)).obj L)) m), ⊤))
      = hilbertFunction (pullback.snd π T.hom)
          ((Scheme.Modules.pullback (pullback.fst π T.hom)).obj L) F
          (ψ.left.base t') m := by
  haveI := hGqc
  -- proper support of the fibre restriction `F_t` over `κ(t)` (fibre square
  -- base change), then of the twist (annihilator monotonicity)
  have hpsFt : Modules.HasProperSupport
      ((pullback.snd π T.hom).fiberToSpecResidueField (ψ.left.base t'))
      ((pullback.snd π T.hom).fiberModule (ψ.left.base t') F) :=
    Modules.HasProperSupport.of_isPullback
      (IsPullback.of_hasPullback (pullback.snd π T.hom)
        (T.left.fromSpecResidueField (ψ.left.base t'))) F hfp hps
  have hpsG : Modules.HasProperSupport
      ((pullback.snd π T.hom).fiberToSpecResidueField (ψ.left.base t'))
      (Scheme.Modules.moduleTensorPow
        ((pullback.snd π T.hom).fiberModule (ψ.left.base t') F)
        ((pullback.snd π T.hom).fiberModule (ψ.left.base t')
          ((Scheme.Modules.pullback (pullback.fst π T.hom)).obj L)) m) :=
    Scheme.Modules.hasProperSupport_moduleTensorPow _ _ m hpsFt
  -- the Γ-fibre flat base-change core on the cartesian fibre square; the
  -- `fiberSectionsModule`/`hilbertFunction` scalar actions are definitionally
  -- the `ΓSpecIso⁻¹ ≫ appTop` composites of the core statement
  exact Scheme.finrank_gammaTop_baseChange_of_hasProperSupport
    (Field.toIsField (T.left.residueField (ψ.left.base t')))
    (Field.toIsField (T'.left.residueField t'))
    (isPullback_fiberBaseChange π ψ t') _ hpsG

set_option backward.isDefEq.respectTransparency false in
/-- **Flat base change of the global sections of the twisted fibre module over
the residue field extension** ([Stacks 02KH], `i = 0`, via the schematic
support reduction; [Nitsure] §1): in the setting of
`Scheme.hilbertFunction_quotBaseMap`, with `t := ψ(t')`, the `κ(t')`-dimension
of the global sections of the pullback of the twisted module
`F_t ⊗ L_t^{⊗m}` along `Scheme.fiberBaseChange π ψ t'` equals the
`κ(t)`-dimension of the global sections of the twisted module itself — the
right-hand side being the graded Hilbert function of `F` at `t`.  Proper
support of `F` over `T` makes the (schematic) support of the twisted module
proper, in particular quasi-compact and separated, over the residue field, so
that [Stacks 02KH] applies to it; quasi-coherence of `L` (hence of the twist)
is likewise required.  In the infinite-dimensional case both sides carry the
junk value `0` of `Module.finrank`, matching the equality of infinite
dimensions.  Blueprint: `lem:gamma_fiber_baseChange_field`.

The scheme-level content is carried by
`Scheme.gammaFiber_finrank_baseChange_field_of_quasicoherent` above (transfer
of properness to the fibre, monotonicity of the support under twisting, and
the flat base-change statement for `Γ`,
`finrank_gammaTop_baseChange_of_hasProperSupport` of
`Picard/SchematicSupport.lean`).  What is left unproved here, and is the
reason this declaration still uses `sorry`, is quasi-coherence of the
sheafified tensor `moduleTensorPow F_t L_t^{⊗m}` of quasi-coherent modules —
the affine tensor-section formula of `Picard/TensorSectionFormula.lean`
([Stacks 01CB]), the same input `lem:pullback_tensor_map_isiso` needs. -/
theorem gammaFiber_finrank_baseChange_field (π : X ⟶ S) (L : X.Modules)
    [L.IsQuasicoherent] {T T' : Over S} (ψ : T' ⟶ T)
    (F : (Limits.pullback π T.hom).Modules) (hfp : F.IsFinitePresentation)
    (hps : Modules.HasProperSupport (pullback.snd π T.hom) F)
    (t' : (T'.left : Scheme.{u})) (m : ℕ) :
    (letI := (pullback.snd π T'.hom).fiberSectionsModule t'
        ((Scheme.Modules.pullback (fiberBaseChange π ψ t')).obj
          (Scheme.Modules.moduleTensorPow
            ((pullback.snd π T.hom).fiberModule (ψ.left.base t') F)
            ((pullback.snd π T.hom).fiberModule (ψ.left.base t')
              ((Scheme.Modules.pullback (pullback.fst π T.hom)).obj L)) m))
     Module.finrank (T'.left.residueField t')
        Γ((Scheme.Modules.pullback (fiberBaseChange π ψ t')).obj
          (Scheme.Modules.moduleTensorPow
            ((pullback.snd π T.hom).fiberModule (ψ.left.base t') F)
            ((pullback.snd π T.hom).fiberModule (ψ.left.base t')
              ((Scheme.Modules.pullback (pullback.fst π T.hom)).obj L)) m), ⊤))
      = hilbertFunction (pullback.snd π T.hom)
          ((Scheme.Modules.pullback (pullback.fst π T.hom)).obj L) F
          (ψ.left.base t') m := by
  refine gammaFiber_finrank_baseChange_field_of_quasicoherent π L ψ F hfp hps t' m ?_
  -- Remaining obligation (`lem:gamma_fiber_baseChange_field`): quasi-coherence
  -- of the sheafified tensor of quasi-coherent modules (Stacks 01CB), i.e. the
  -- affine tensor-section formula for `sheafTensorObj` of
  -- `Picard/TensorSectionFormula.lean`.
  sorry

end HilbertFunctionBaseChange

/-- **The fibrewise graded Hilbert function is invariant under base change**
(Nitsure §1, the implicit invariance behind the decomposition
`Quot = ∐_Φ Quot^Φ`).  For `t' : T'` over `t := ψ(t')`, the fibre of
`X_{T'} → T'` at `t'` is the base change of the fibre of `X_T → T` at `t`
along the residue extension `κ(t) → κ(t')` (`quotBaseSquare` pasting), and
`H⁰` of the twists of a finitely presented module with proper support
commutes with base field extension (flat base change over a field, Stacks
02KH), so the `κ`-dimensions agree.  Quasi-coherence of the twisting module
`L` is required for the flat-base-change step (for an arbitrary sheaf of
modules the statement can fail), matching the line-bundle `L` of
`def:quot_functor`. -/
theorem hilbertFunction_quotBaseMap (π : X ⟶ S) (L : X.Modules)
    [L.IsQuasicoherent]
    {T T' : Over S} (ψ : T' ⟶ T) (F : (Limits.pullback π T.hom).Modules)
    (hfp : F.IsFinitePresentation)
    (hps : Modules.HasProperSupport (pullback.snd π T.hom) F)
    (t' : (T'.left : Scheme.{u})) (m : ℕ) :
    hilbertFunction (pullback.snd π T'.hom)
        ((Scheme.Modules.pullback (pullback.fst π T'.hom)).obj L)
        ((Scheme.Modules.pullback (quotBaseMap π ψ)).obj F) t' m
      = hilbertFunction (pullback.snd π T.hom)
        ((Scheme.Modules.pullback (pullback.fst π T.hom)).obj L) F
        (ψ.left.base t') m := by
  -- quasi-coherence of the two restrictions on the `T`-side fibre
  haveI hFqc : F.IsQuasicoherent := letI := hfp; inferInstance
  haveI : ((pullback.snd π T.hom).fiberModule (ψ.left.base t') F).IsQuasicoherent :=
    pullback_isQuasicoherent_hom _ F hFqc
  haveI : ((pullback.snd π T.hom).fiberModule (ψ.left.base t')
      ((Scheme.Modules.pullback (pullback.fst π T.hom)).obj L)).IsQuasicoherent :=
    pullback_isQuasicoherent_hom _ _ (pullback_isQuasicoherent_hom _ L inferInstance)
  -- Steps 1–2 (fibre pasting + module bookkeeping): match the two restrictions
  -- across the fibre comparison `fiberBaseChange` by pseudofunctor coherence
  have eF : (pullback.snd π T'.hom).fiberModule t'
        ((Scheme.Modules.pullback (quotBaseMap π ψ)).obj F)
      ≅ (Scheme.Modules.pullback (fiberBaseChange π ψ t')).obj
          ((pullback.snd π T.hom).fiberModule (ψ.left.base t') F) :=
    pullbackSquareIso (fiberBaseChange_fiberι π ψ t').symm F
  have eL : (pullback.snd π T'.hom).fiberModule t'
        ((Scheme.Modules.pullback (pullback.fst π T'.hom)).obj L)
      ≅ (Scheme.Modules.pullback (fiberBaseChange π ψ t')).obj
          ((pullback.snd π T.hom).fiberModule (ψ.left.base t')
            ((Scheme.Modules.pullback (pullback.fst π T.hom)).obj L)) :=
    pullbackSquareIso (fiberBaseChange_fiberι_fst π ψ t') L ≪≫
      (Scheme.Modules.pullback (fiberBaseChange π ψ t')).mapIso
        (pullbackTriangleIso (rfl : (pullback.snd π T.hom).fiberι (ψ.left.base t')
            ≫ pullback.fst π T.hom = _) L).symm
  -- Step 3 (twist compatibility): pull the tensor operations through
  -- `fiberBaseChange` (`Modules.pullback_moduleTensorPow_iso`, which rests on
  -- `Modules.pullbackTensorMap_isIso`)
  obtain ⟨eT⟩ := Modules.pullback_moduleTensorPow_iso (fiberBaseChange π ψ t')
    ((pullback.snd π T.hom).fiberModule (ψ.left.base t') F)
    ((pullback.snd π T.hom).fiberModule (ψ.left.base t')
      ((Scheme.Modules.pullback (pullback.fst π T.hom)).obj L)) m
  -- Step 4 (dimension transport along the composite isomorphism), then
  -- Step 5 (Γ-base change over the residue field extension,
  -- `gammaFiber_finrank_baseChange_field`)
  exact (hilbertFunction_eq_finrank_of_iso (pullback.snd π T'.hom)
      ((Scheme.Modules.pullback (pullback.fst π T'.hom)).obj L)
      ((Scheme.Modules.pullback (quotBaseMap π ψ)).obj F) t' m
      (Modules.moduleTensorPowCongr eF eL m ≪≫ eT.symm)).trans
    (gammaFiber_finrank_baseChange_field π L ψ F hfp hps t' m)

/-! ## §3. Families of quotients and the Quot functor -/

section QuotFunctor

variable [IsLocallyNoetherian S]

/-- A **family of quotients of `E` parametrised by `T`** with Hilbert
polynomial `Φ` (Nitsure §1; the unbundled datum whose equivalence classes
form the value of the Quot functor `def:quot_functor` at `T`):

* a finitely presented sheaf of modules `F` on the relative product
  `X_T = X ×_S T` (the coherence encoding of the flattening-stratification
  input; over the locally noetherian regime finite presentation ⟺
  coherence), flat over `T` and with schematic support proper over `T`;
* an epimorphism `q : E_T ⟶ F` from the pullback of `E` along the first
  projection;
* at every point `t : T`, the graded Hilbert function
  `m ↦ dim_{κ(t)} Γ((X_T)_t, F_t ⊗ L_t^{⊗m})` eventually agrees with `Φ` —
  by `Scheme.hilbertPolynomial_eq_of_eventually` this says exactly that the
  Hilbert polynomial of `F|_{X_t}` relative to `L|_{X_t}`
  (`def:hilbert_polynomial`) *is* `Φ`, and it excludes the junk-value
  coincidence when no polynomial matches. -/
structure QuotFamily (π : X ⟶ S) [LocallyOfFiniteType π] (L E : X.Modules)
    (Φ : Polynomial ℚ) (T : Over S) : Type (u + 1) where
  /-- The quotient sheaf on the relative product `X ×_S T`. -/
  F : (Limits.pullback π T.hom).Modules
  /-- `F` is finitely presented (coherent, in the locally noetherian regime). -/
  isFinitePresentation : F.IsFinitePresentation
  /-- `F` is flat over `T`. -/
  flat : CoherentSheafFlat (pullback.snd π T.hom) F
  /-- The schematic support of `F` is proper over `T`. -/
  properSupport : Modules.HasProperSupport (pullback.snd π T.hom) F
  /-- The quotient map from the pullback of `E`. -/
  q : (Scheme.Modules.pullback (pullback.fst π T.hom)).obj E ⟶ F
  /-- The quotient map is an epimorphism. -/
  epi : Epi q
  /-- At every `t : T`, the graded Hilbert function of the fibre of `F`
  twisted by `L` eventually agrees with `Φ`. -/
  hilb : ∀ t : (T.left : Scheme.{u}), ∃ N : ℕ, ∀ m : ℕ, N < m →
    Φ.eval (m : ℚ) = (hilbertFunction (pullback.snd π T.hom)
      ((Scheme.Modules.pullback (pullback.fst π T.hom)).obj L) F t m : ℚ)

namespace QuotFamily

variable {π : X ⟶ S} [LocallyOfFiniteType π] {L E : X.Modules} {Φ : Polynomial ℚ}

/- The quasi-coherence of the twisting module `L` (part of the line-bundle
hypothesis of `def:quot_functor`) enters only through the base-change
invariance of the fibrewise Hilbert function
(`Scheme.hilbertFunction_quotBaseMap`), i.e. through the pullback action. -/

/-- Two families of quotients are **equivalent** when an isomorphism of the
target sheaves commutes with the quotient maps — equivalently, when
`ker q = ker q'` (`def:quot_functor`; same convention as the absolute
Grassmannian `RankQuotient.Rel`). -/
def Rel {T : Over S} (x y : QuotFamily π L E Φ T) : Prop :=
  ∃ f : x.F ≅ y.F, x.q ≫ f.hom = y.q

omit [IsLocallyNoetherian S] in
lemma rel_refl {T : Over S} (x : QuotFamily π L E Φ T) : x.Rel x :=
  ⟨Iso.refl _, Category.comp_id _⟩

omit [IsLocallyNoetherian S] in
lemma rel_symm {T : Over S} {x y : QuotFamily π L E Φ T} (h : x.Rel y) : y.Rel x := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f.symm, by rw [Iso.symm_hom, Iso.comp_inv_eq]; exact hf.symm⟩

omit [IsLocallyNoetherian S] in
lemma rel_trans {T : Over S} {x y z : QuotFamily π L E Φ T}
    (h1 : x.Rel y) (h2 : y.Rel z) : x.Rel z := by
  obtain ⟨f, hf⟩ := h1; obtain ⟨g, hg⟩ := h2
  exact ⟨f ≪≫ g,
    (congrArg (x.q ≫ ·) (Iso.trans_hom f g)).trans <|
      (Category.assoc x.q f.hom g.hom).symm.trans <|
        (congrArg (· ≫ g.hom) hf).trans hg⟩

/-- The equivalence-of-families setoid. -/
instance setoid (π : X ⟶ S) [LocallyOfFiniteType π] (L E : X.Modules)
    (Φ : Polynomial ℚ) (T : Over S) : Setoid (QuotFamily π L E Φ T) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

/-- The **pullback action** on a family of quotients along `ψ : T' ⟶ T` of
`Over S`: pull the sheaf and the quotient map back along
`quotBaseMap π ψ : X_{T'} ⟶ X_T`, matching the `E`-side through
`pullbackTriangleIso (quotBaseMap_fst π ψ)`.  Well-definedness of the four
conditions is the content of §2. -/
noncomputable def pullbackAlong [L.IsQuasicoherent] {T T' : Over S} (ψ : T' ⟶ T)
    (x : QuotFamily π L E Φ T) : QuotFamily π L E Φ T' where
  F := (Scheme.Modules.pullback (quotBaseMap π ψ)).obj x.F
  isFinitePresentation :=
    Modules.pullback_isFinitePresentation _ x.F x.isFinitePresentation
  flat := fun {U} hU {V} hV e =>
    CoherentSheafFlat.of_isPullback (quotBaseSquare π ψ) x.F
      (letI := x.isFinitePresentation; inferInstance) x.flat hU hV e
  properSupport :=
    Modules.HasProperSupport.of_isPullback (quotBaseSquare π ψ) x.F
      x.isFinitePresentation x.properSupport
  q := (pullbackTriangleIso (quotBaseMap_fst π ψ) E).inv ≫
    (Scheme.Modules.pullback (quotBaseMap π ψ)).map x.q
  epi :=
    @CategoryTheory.epi_comp _ _ _ _ _
      (pullbackTriangleIso (quotBaseMap_fst π ψ) E).inv inferInstance
      ((Scheme.Modules.pullback (quotBaseMap π ψ)).map x.q)
      (@CategoryTheory.Functor.map_epi _ _ _ _
        (Scheme.Modules.pullback (quotBaseMap π ψ)) inferInstance _ _ x.q x.epi)
  hilb := fun t' => by
    obtain ⟨N, hN⟩ := x.hilb (ψ.left.base t')
    exact ⟨N, fun m hm => (hN m hm).trans (congrArg (Nat.cast : ℕ → ℚ)
      (hilbertFunction_quotBaseMap π L ψ x.F x.isFinitePresentation
        x.properSupport t' m).symm)⟩

omit [IsLocallyNoetherian S] in
/-- The pullback action respects the equivalence relation. -/
lemma pullbackAlong_rel [L.IsQuasicoherent] {T T' : Over S} (ψ : T' ⟶ T)
    {x y : QuotFamily π L E Φ T} (h : x.Rel y) :
    (pullbackAlong ψ x).Rel (pullbackAlong ψ y) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨(Scheme.Modules.pullback (quotBaseMap π ψ)).mapIso f, ?_⟩
  change ((pullbackTriangleIso (quotBaseMap_fst π ψ) E).inv ≫
      (Scheme.Modules.pullback (quotBaseMap π ψ)).map x.q) ≫
      (Scheme.Modules.pullback (quotBaseMap π ψ)).map f.hom
    = (pullbackTriangleIso (quotBaseMap_fst π ψ) E).inv ≫
      (Scheme.Modules.pullback (quotBaseMap π ψ)).map y.q
  rw [Category.assoc, ← (Scheme.Modules.pullback (quotBaseMap π ψ)).map_comp]
  exact congrArg
    (fun m => (pullbackTriangleIso (quotBaseMap_fst π ψ) E).inv ≫
      (Scheme.Modules.pullback (quotBaseMap π ψ)).map m) hf

end QuotFamily

set_option backward.isDefEq.respectTransparency false in
/-- The **Quot functor** `Quot^{Φ,L}_{E/X/S}` of coherent quotients of `E`
on `X ×_S -` with Hilbert polynomial `Φ` (`def:quot_functor`, [Nitsure] §1):
the contravariant functor `(Sch/S)ᵒᵖ ⥤ Type (u+1)` sending an `S`-scheme
`T → S` to the set of equivalence classes `⟨F, q⟩` of families of quotients
of `E` parametrised by `T` (`Scheme.QuotFamily`), and a morphism to the
pullback of families (`QuotFamily.pullbackAlong`).  The identity and
composition laws are the pseudofunctor coherence laws of the module
pullback, packaged as `Scheme.Modules.pullback_id_app_coherence` and
`Scheme.Modules.pullback_comp_app_coherence_inv`.

The Hilbert scheme is the special case `E = O_X`:
`Hilb^{Φ,L}_{X/S} = Quot^{Φ,L}_{O_X/X/S}`. -/
noncomputable def QuotFunctor (π : X ⟶ S) [LocallyOfFiniteType π] (L E : X.Modules)
    [L.IsQuasicoherent] (Φ : Polynomial ℚ) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Quotient (QuotFamily.setoid π L E Φ T.unop)
  map {T T'} g := TypeCat.ofHom (Quotient.map (QuotFamily.pullbackAlong g.unop)
    (fun _ _ h => QuotFamily.pullbackAlong_rel g.unop h))
  map_id T := by
    ext z
    induction z using Quotient.ind with
    | _ x =>
      change Quotient.mk _ (QuotFamily.pullbackAlong (𝟙 T.unop) x) = Quotient.mk _ x
      refine Quotient.sound ⟨(Scheme.Modules.pullbackCongr (quotBaseMap_id π T.unop)).app x.F ≪≫
        (Scheme.Modules.pullbackId _).app x.F, ?_⟩
      change ((pullbackTriangleIso (quotBaseMap_fst π (𝟙 T.unop)) E).inv ≫
          (Scheme.Modules.pullback (quotBaseMap π (𝟙 T.unop))).map x.q) ≫
          (Scheme.Modules.pullbackCongr (quotBaseMap_id π T.unop)).hom.app x.F ≫
          (Scheme.Modules.pullbackId _).hom.app x.F
        = x.q
      rw [Category.assoc,
        (Scheme.Modules.pullbackCongr (quotBaseMap_id π T.unop)).hom.naturality_assoc x.q,
        (Scheme.Modules.pullbackId _).hom.naturality x.q]
      have key := Scheme.Modules.pullback_id_app_coherence (quotBaseMap_id π T.unop)
        (quotBaseMap_fst π (𝟙 T.unop)) E
      simp only [pullbackTriangleIso, Iso.trans_inv, Iso.app_inv, Category.assoc]
      rw [reassoc_of% key]
      rfl
  map_comp {T T' T''} g h := by
    ext z
    induction z using Quotient.ind with
    | _ x =>
      change Quotient.mk _ (QuotFamily.pullbackAlong (h.unop ≫ g.unop) x)
        = Quotient.mk _ (QuotFamily.pullbackAlong h.unop (QuotFamily.pullbackAlong g.unop x))
      refine Quotient.sound
        ⟨(Scheme.Modules.pullbackCongr (quotBaseMap_comp π g.unop h.unop)).app x.F ≪≫
          ((Scheme.Modules.pullbackComp (quotBaseMap π h.unop) (quotBaseMap π g.unop)).app
            x.F).symm, ?_⟩
      change ((pullbackTriangleIso (quotBaseMap_fst π (h.unop ≫ g.unop)) E).inv ≫
          (Scheme.Modules.pullback (quotBaseMap π (h.unop ≫ g.unop))).map x.q) ≫
          (Scheme.Modules.pullbackCongr (quotBaseMap_comp π g.unop h.unop)).hom.app x.F ≫
          (Scheme.Modules.pullbackComp (quotBaseMap π h.unop) (quotBaseMap π g.unop)).inv.app
            x.F
        = (pullbackTriangleIso (quotBaseMap_fst π h.unop) E).inv ≫
          (Scheme.Modules.pullback (quotBaseMap π h.unop)).map
            ((pullbackTriangleIso (quotBaseMap_fst π g.unop) E).inv ≫
              (Scheme.Modules.pullback (quotBaseMap π g.unop)).map x.q)
      rw [Category.assoc,
        (Scheme.Modules.pullbackCongr (quotBaseMap_comp π g.unop h.unop)).hom.naturality_assoc
          x.q,
        (Scheme.Modules.pullbackComp (quotBaseMap π h.unop)
          (quotBaseMap π g.unop)).inv.naturality x.q]
      have key := Scheme.Modules.pullback_comp_app_coherence_inv
        (quotBaseMap π h.unop) (quotBaseMap π g.unop)
        (quotBaseMap_comp π g.unop h.unop) (pullback.fst π T.unop.hom)
        (quotBaseMap_fst π g.unop) (quotBaseMap_fst π (h.unop ≫ g.unop))
        (quotBaseMap_fst π h.unop) E
      simp only [pullbackTriangleIso, Iso.trans_inv, Iso.app_inv, Category.assoc,
        Functor.map_comp]
      rw [reassoc_of% key]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rfl

end QuotFunctor

/-! ## §4. The relative Grassmannian functor -/

section Grassmannian

variable [IsLocallyNoetherian S]

/-- A **rank-`d` locally free quotient of `V_T`** over `T : Over S`
(`def:grassmannian_scheme`, [Nitsure] §1, Exercise (2)): a sheaf of modules
`F` on `T`, locally free of rank `d`, with an epimorphism from the pullback
`V_T` of `V` along the structure morphism. -/
structure LocallyFreeQuotient (V : S.Modules) (d : ℕ) (T : Over S) : Type (u + 1) where
  /-- The quotient sheaf on `T`. -/
  F : (T.left : Scheme.{u}).Modules
  /-- The quotient map out of the pulled-back bundle `V_T`. -/
  q : (Scheme.Modules.pullback T.hom).obj V ⟶ F
  /-- The quotient map is an epimorphism. -/
  epi : Epi q
  /-- The quotient sheaf is locally free of rank `d`. -/
  locFree : SheafOfModules.IsLocallyFreeOfRank F d

namespace LocallyFreeQuotient

variable {V : S.Modules} {d : ℕ}

/-- Equivalence of rank-`d` quotients: an isomorphism of the targets
commuting with the quotient maps (equivalently, `ker q = ker q'`). -/
def Rel {T : Over S} (x y : LocallyFreeQuotient V d T) : Prop :=
  ∃ f : x.F ≅ y.F, x.q ≫ f.hom = y.q

omit [IsLocallyNoetherian S] in
lemma rel_refl {T : Over S} (x : LocallyFreeQuotient V d T) : x.Rel x :=
  ⟨Iso.refl _, Category.comp_id _⟩

omit [IsLocallyNoetherian S] in
lemma rel_symm {T : Over S} {x y : LocallyFreeQuotient V d T} (h : x.Rel y) :
    y.Rel x := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f.symm, by rw [Iso.symm_hom, Iso.comp_inv_eq]; exact hf.symm⟩

omit [IsLocallyNoetherian S] in
lemma rel_trans {T : Over S} {x y z : LocallyFreeQuotient V d T}
    (h1 : x.Rel y) (h2 : y.Rel z) : x.Rel z := by
  obtain ⟨f, hf⟩ := h1; obtain ⟨g, hg⟩ := h2
  exact ⟨f ≪≫ g,
    (congrArg (x.q ≫ ·) (Iso.trans_hom f g)).trans <|
      (Category.assoc x.q f.hom g.hom).symm.trans <|
        (congrArg (· ≫ g.hom) hf).trans hg⟩

/-- The equivalence-of-quotients setoid. -/
instance setoid (V : S.Modules) (d : ℕ) (T : Over S) :
    Setoid (LocallyFreeQuotient V d T) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

/-- The pullback action on a rank-`d` quotient along `ψ : T' ⟶ T` of
`Over S`: pull the sheaf and the quotient map back along `ψ.left`, matching
the `V`-side through `pullbackTriangleIso (Over.w ψ)`. -/
noncomputable def pullbackAlong {T T' : Over S} (ψ : T' ⟶ T)
    (x : LocallyFreeQuotient V d T) : LocallyFreeQuotient V d T' where
  F := (Scheme.Modules.pullback ψ.left).obj x.F
  q := (pullbackTriangleIso (Over.w ψ) V).inv ≫
    (Scheme.Modules.pullback ψ.left).map x.q
  epi :=
    @CategoryTheory.epi_comp _ _ _ _ _
      (pullbackTriangleIso (Over.w ψ) V).inv inferInstance
      ((Scheme.Modules.pullback ψ.left).map x.q)
      (@CategoryTheory.Functor.map_epi _ _ _ _
        (Scheme.Modules.pullback ψ.left) inferInstance _ _ x.q x.epi)
  locFree := Scheme.Modules.pullback_isLocallyFreeOfRank ψ.left x.locFree

omit [IsLocallyNoetherian S] in
/-- The pullback action respects the equivalence relation. -/
lemma pullbackAlong_rel {T T' : Over S} (ψ : T' ⟶ T)
    {x y : LocallyFreeQuotient V d T} (h : x.Rel y) :
    (pullbackAlong ψ x).Rel (pullbackAlong ψ y) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨(Scheme.Modules.pullback ψ.left).mapIso f, ?_⟩
  change ((pullbackTriangleIso (Over.w ψ) V).inv ≫
      (Scheme.Modules.pullback ψ.left).map x.q) ≫
      (Scheme.Modules.pullback ψ.left).map f.hom
    = (pullbackTriangleIso (Over.w ψ) V).inv ≫
      (Scheme.Modules.pullback ψ.left).map y.q
  rw [Category.assoc, ← (Scheme.Modules.pullback ψ.left).map_comp]
  exact congrArg
    (fun m => (pullbackTriangleIso (Over.w ψ) V).inv ≫
      (Scheme.Modules.pullback ψ.left).map m) hf

end LocallyFreeQuotient

set_option backward.isDefEq.respectTransparency false in
/-- The **Grassmannian functor** `Grass(V, d) : (Sch/S)ᵒᵖ ⥤ Type (u+1)` of
rank-`d` locally free quotients of a module `V` on a noetherian base `S`
(`def:grassmannian_scheme`, [Nitsure] §1, Exercise (2)): an `S`-scheme
`T → S` is sent to the set of equivalence classes `⟨F, q⟩` of rank-`d`
locally free quotients `q : V_T ↠ F` (`Scheme.LocallyFreeQuotient`), and a
morphism to the pullback of quotients.  In the locally noetherian regime
this agrees with the Quot-functor special case
`Grass(V, d) = Quot^{d, O_S}_{V/S/S}` of the blueprint (a flat finitely
presented module with constant fibre dimension `d` is locally free of rank
`d`); the locally-free encoding is the form valid over an arbitrary base and
the one matched by the absolute chart construction
(`AlgebraicGeometry.Grassmannian.functor`, `GrassmannianQuot.lean`). -/
noncomputable def Grassmannian (V : S.Modules) (d : ℕ) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Quotient (LocallyFreeQuotient.setoid V d T.unop)
  map {T T'} g := TypeCat.ofHom (Quotient.map (LocallyFreeQuotient.pullbackAlong g.unop)
    (fun _ _ h => LocallyFreeQuotient.pullbackAlong_rel g.unop h))
  map_id T := by
    ext z
    induction z using Quotient.ind with
    | _ x =>
      change Quotient.mk _ (LocallyFreeQuotient.pullbackAlong (𝟙 T.unop) x)
        = Quotient.mk _ x
      refine Quotient.sound ⟨(Scheme.Modules.pullbackCongr (Over.id_left T.unop)).app x.F ≪≫
        (Scheme.Modules.pullbackId _).app x.F, ?_⟩
      change ((pullbackTriangleIso (Over.w (𝟙 T.unop)) V).inv ≫
          (Scheme.Modules.pullback (Over.Hom.left (𝟙 T.unop))).map x.q) ≫
          (Scheme.Modules.pullbackCongr (Over.id_left T.unop)).hom.app x.F ≫
          (Scheme.Modules.pullbackId _).hom.app x.F
        = x.q
      rw [Category.assoc,
        (Scheme.Modules.pullbackCongr (Over.id_left T.unop)).hom.naturality_assoc x.q,
        (Scheme.Modules.pullbackId _).hom.naturality x.q]
      have key := Scheme.Modules.pullback_id_app_coherence (Over.id_left T.unop)
        (Over.w (𝟙 T.unop)) V
      simp only [pullbackTriangleIso, Iso.trans_inv, Iso.app_inv, Category.assoc]
      rw [reassoc_of% key]
      rfl
  map_comp {T T' T''} g h := by
    ext z
    induction z using Quotient.ind with
    | _ x =>
      change Quotient.mk _ (LocallyFreeQuotient.pullbackAlong (h.unop ≫ g.unop) x)
        = Quotient.mk _
          (LocallyFreeQuotient.pullbackAlong h.unop (LocallyFreeQuotient.pullbackAlong g.unop x))
      refine Quotient.sound
        ⟨(Scheme.Modules.pullbackCongr (Over.comp_left _ _ _ h.unop g.unop)).app x.F ≪≫
          ((Scheme.Modules.pullbackComp h.unop.left g.unop.left).app x.F).symm, ?_⟩
      change ((pullbackTriangleIso (Over.w (h.unop ≫ g.unop)) V).inv ≫
          (Scheme.Modules.pullback (Over.Hom.left (h.unop ≫ g.unop))).map x.q) ≫
          (Scheme.Modules.pullbackCongr (Over.comp_left _ _ _ h.unop g.unop)).hom.app x.F ≫
          (Scheme.Modules.pullbackComp h.unop.left g.unop.left).inv.app x.F
        = (pullbackTriangleIso (Over.w h.unop) V).inv ≫
          (Scheme.Modules.pullback h.unop.left).map
            ((pullbackTriangleIso (Over.w g.unop) V).inv ≫
              (Scheme.Modules.pullback g.unop.left).map x.q)
      rw [Category.assoc,
        (Scheme.Modules.pullbackCongr (Over.comp_left _ _ _ h.unop g.unop)).hom.naturality_assoc
          x.q,
        (Scheme.Modules.pullbackComp h.unop.left g.unop.left).inv.naturality x.q]
      have key := Scheme.Modules.pullback_comp_app_coherence_inv
        h.unop.left g.unop.left (Over.comp_left _ _ _ h.unop g.unop) T.unop.hom
        (Over.w g.unop) (Over.w (h.unop ≫ g.unop)) (Over.w h.unop) V
      simp only [pullbackTriangleIso, Iso.trans_inv, Iso.app_inv, Category.assoc,
        Functor.map_comp]
      rw [reassoc_of% key]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rfl

/- **Representability of the Grassmannian** (`thm:grassmannian_representable`)
is `AlgebraicGeometry.Scheme.Grassmannian.representable` of
`AlgebraicJacobian/Picard/GrassmannianRepresentability.lean`, stated with the
blueprint hypotheses (`V` locally free of rank `r`, `1 ≤ d ≤ r`); without them
the bare statement quantifies over arbitrary sheaves of modules `V`, which is
not the [Nitsure] §1 theorem and is not known to be true.  Its proof consumes
the absolute chart construction (`AlgebraicGeometry.Grassmannian.represents`,
`GrassmannianQuot.lean`), which this file deliberately does not import. -/

end Grassmannian

/-! ## §5. Representability of the Quot scheme -/

/- **Representability of the Quot scheme** (`thm:quot_representable`) is
`AlgebraicGeometry.Scheme.QuotScheme` of
`AlgebraicJacobian/Picard/QuotRepresentability.lean`, stated with the
[Nitsure] §5 hypotheses: `π` projective carrying the relatively very ample
line bundle `L` (`Scheme.Hom.IsProjectiveWith`,
`Picard/ProjectiveMorphism.lean` — that file imports this one, which forces
the statement out of this file) and `E` coherent, at `Scheme.{0}`.  Merely
assuming `[IsProper π] [LocallyOfFiniteType π]` over quasi-coherent `L` and
arbitrary `E` would not do: for a proper `π` that is not projective the Quot
functor is in general only an algebraic space, Hironaka's smooth proper
non-projective 3-folds being the standard counterexamples.  This is the same
split as `Grassmannian.representable` above. -/

end Scheme

end AlgebraicGeometry
