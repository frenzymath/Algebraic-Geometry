/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.SmallComplete
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.SetNotationForOrder
import Mathlib.Topology.Sheaves.Over
import AlgebraicJacobian.Picard.LocallyFreeOfRank
import AlgebraicJacobian.Picard.HilbertPolynomial
import AlgebraicJacobian.Picard.SectionBaseChange
import AlgebraicJacobian.Cohomology.FlatBaseChange

/-!
# Flat base change of cohomology, and quasi-coherent descent

This file develops the sheaf theory entering the Grothendieck–Altman–Kleiman construction of
the Quot scheme `Quot^{Φ,L}_{E/X/S}`, the projective `S`-scheme representing the functor
sending an `S`-scheme `T` to the `T`-flat coherent quotients of `E_T` on `X_T = X ×_S T` whose
fibres have Hilbert polynomial `Φ`. Cohomology and base change enters that construction twice,
in the boundedness step and in the embedding of `Quot` into a Grassmannian.

Let

```
     g'
X' ─────→ X
│         │
f'        f
↓         ↓
S' ─────→ S
     g
```

be a cartesian square of schemes and `F` a sheaf of `O_X`-modules. There is a canonical
base-change morphism `g^* (f_* F) ⟶ f'_* ((g')^* F)`, the Beck–Chevalley mate of the
`pullback ⊣ pushforward` adjunctions, which requires no hypotheses; it is an isomorphism as
soon as `g` is flat, `f` is quasi-compact and quasi-separated, and `F` is quasi-coherent. Only
this `i = 0` case of flat base change is treated: the corresponding statement for the higher
direct images `R^i f_*`, `i ≥ 1`, is not proved here.

The proof rests on a body of quasi-coherent descent, developed here from scratch and of
independent use: on `Spec R` a quasi-coherent sheaf of modules is the `tilde` of its global
sections, hence its sections localize on basic opens — first over an affine open, then over any
quasi-compact quasi-separated open — and pushforward along a quasi-compact quasi-separated
morphism preserves quasi-coherence. The file also builds the annihilator ideal sheaf, the
schematic support and the rank-`d` local freeness predicate for sheaves of modules on a scheme,
which the Quot functor consumes, and promotes the site equivalence `Over U ≌ Opens ↥U` to an
equivalence of sheaf categories.

The Hilbert polynomial `AlgebraicGeometry.Scheme.hilbertPolynomial` is constructed in
`AlgebraicJacobian.Picard.HilbertPolynomial`; the Quot functor, the Grassmannian functor and
their representability statements live in `AlgebraicJacobian.Picard.QuotFunctorDef`.

## Main results

* `AlgebraicGeometry.canonicalBaseChangeMap`: the base-change transformation
  `g^* (f_* -) ⟶ f'_* ((g')^* -)` of a cartesian square.
* `AlgebraicGeometry.canonicalBaseChangeMap_isIso` and
  `AlgebraicGeometry.flatBaseChangeCohomology`: it is an isomorphism for `g` flat and `f`
  quasi-compact quasi-separated (Stacks 02KH, `i = 0`).
* `AlgebraicGeometry.pullback_baseMap_sectionLinearEquiv_of_quasiCompact`: the underlying H⁰
  statement (Stacks 02KE) — over a compatible pair of affine opens `U ⊆ S'`, `V ⊆ S`, the
  sections of `(g')^* F` over `f' ⁻¹ᵁ U` are `Γ(S', U) ⊗_{Γ(S, V)} Γ(F, f ⁻¹ᵁ V)`.
* `AlgebraicGeometry.Scheme.Modules.pullback_app_isoTensor`: the affine-open section formula
  `Γ(g^* N, U) ≃ Γ(Y, U) ⊗_{Γ(X, V)} Γ(N, V)` for quasi-coherent `N` (Stacks 01HQ).
* `AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`: a quasi-coherent
  sheaf of modules on `Spec R` lies in the essential image of `tilde` (Stacks 01I8).
* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpen`: for quasi-coherent `M`, an
  affine open `U` and `f : Γ(X, U)`, the restriction `Γ(M, U) → Γ(M, D(f))` exhibits the
  target as the localization at the powers of `f` (Hartshorne II.5.3).
* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpen_of_isCompact`: the same
  conclusion over a quasi-compact quasi-separated open (Stacks 01P0).
* `AlgebraicGeometry.Scheme.Modules.pushforward_isQuasicoherent`: pushforward along a
  quasi-compact quasi-separated morphism preserves quasi-coherence (Stacks 01XJ).
* `AlgebraicGeometry.Scheme.Modules.module_finite_sections_of_quasicoherentData` and
  `AlgebraicGeometry.Scheme.Modules.exists_affine_finite_sections_nhds`: sections of a
  finitely presented sheaf of modules over a small enough affine open are a finite module
  (Stacks 01PC).
* `AlgebraicGeometry.overEquivalence_sheafCongr`: the equivalence of sheaf categories induced
  by `Opens.overEquivalence U : Over U ≌ Opens ↥U`.
* `AlgebraicGeometry.SheafOfModules.IsLocallyFreeOfRank`,
  `AlgebraicGeometry.Scheme.Modules.annihilator`,
  `AlgebraicGeometry.Scheme.Modules.schematicSupport`,
  `AlgebraicGeometry.Scheme.Modules.HasProperSupport`: the predicates and constructions on
  sheaves of modules used by the Quot functor, together with the identification
  `AlgebraicGeometry.Scheme.Modules.annihilator_ideal` of the annihilator ideal sheaf on
  affine opens.
* `Module.annihilator_isLocalizedModule_eq_map`: for a finitely generated module the
  annihilator commutes with localization.

## References

* Nitsure, *Construction of Hilbert and Quot schemes*, §§1, 5 (FGA Explained, Ch. 5).
* Grothendieck, FGA, TDTE IV.
* Hartshorne, *Algebraic Geometry*, II.5.3 and III.5.2.
* Stacks Project, tags 01HQ, 01I8, 01P0, 01PC, 01XJ, 02KE, 02KH.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-! ## The Hilbert polynomial of a coherent sheaf

The Hilbert polynomial `AlgebraicGeometry.Scheme.hilbertPolynomial` is constructed in
`AlgebraicJacobian.Picard.HilbertPolynomial` (imported above): it is the unique
`Φ_{F,s} ∈ ℚ[λ]` agreeing for `m ≫ 0` with the graded Hilbert function
`m ↦ dim_{κ(s)} Γ(X_s, F_s ⊗ L_s^{⊗m})` of the fibre section module. This is the `H⁰`-only
encoding; it agrees with the Euler-characteristic form `χ(F(m))` by Serre vanishing, for
proper `X_s` and ample `L_s`. See `Scheme.hilbertPolynomial_eq_of_eventually` for uniqueness
and `Scheme.existsUnique_hilbertPolynomial_of_isRatHilb` for existence, the latter resting on
the graded Hilbert–Serre theorem of `AlgebraicJacobian.Picard.GradedHilbertSerre`.

Reference: Nitsure §1; cf. Hartshorne III.5.2. -/

/-! ## The Quot functor, the Grassmannian, and representability

The functor definitions `Scheme.QuotFunctor` and `Scheme.Grassmannian` — Setoid quotients of
families of quotients, with their pullback functoriality — and the representability statements
`Scheme.Grassmannian.representable` and `Scheme.QuotScheme` live in
`AlgebraicJacobian.Picard.QuotFunctorDef`. That functor-of-points layer consumes the
flattening-stratification flatness predicate `Scheme.CoherentSheafFlat`, the support and
freeness predicates built below in this file, and the Hilbert-function machinery of
`AlgebraicJacobian.Picard.HilbertPolynomial`, so it sits above this file,
`FlatteningStratification` and `GlueDescent` in the import order. -/
end Scheme

/-! ## Cohomology and base change

The Quot construction uses cohomology and base change in two places: the boundedness step
(Nitsure §5, "Use of m-regularity") and the Grassmannian embedding (Nitsure §5, "Embedding
Quot into Grassmannian").

Stacks 02KH states flat base change for all higher direct images `R^i f_*` of quasi-coherent
sheaves. What is proved here is the `i = 0` form on `Scheme.Modules`, the substantive content
of part (ii) of that statement; the `R^i` form for `i ≥ 1` is not proved. -/

/-! ### Flat base change of cohomology (Stacks tag 02KH, `i = 0` form)

Let
```
   g'
X' ───→ X
│       │
f'      f
↓       ↓
S' ───→ S
   g
```
be a cartesian square of schemes with `g` flat and `f` quasi-compact
quasi-separated. Let `F` be a sheaf of `O_X`-modules. Then the canonical
base-change map `g* (f_* F) ⟶ f'_* ((g')* F)` is an isomorphism in
`S'.Modules`.

(The full Stacks 02KH statement covers all higher direct images
`R^i f_* F` for `i ≥ 0`; what is proved here is the `i = 0` form, the
substantive content of part (ii) of that statement.)

The base-change natural transformation itself is the mate of the
`pullback ⊣ pushforward` adjunction (Mathlib's `mateEquiv` applied to
`Scheme.Modules.pullbackPushforwardAdjunction`); that it is an isomorphism
is `canonicalBaseChangeMap_isIso`. The deep content (Stacks 02KH / 02KE /
00H8) lies entirely in that step: it reduces affine-locally to the claim
that, for a flat ring map `A → B`, the canonical map
`B ⊗_A H^i(X, F) → H^i(X_B, F_B)` is an isomorphism for quasi-coherent
`F`, here in its `i = 0` form. The affine-local reduction runs through the
section formula of Stacks 01HQ (`pullback_app_isoTensor`) and a
quasi-compact open-cover Mayer–Vietoris induction. -/

/-- The canonical base-change natural transformation `g* (f_* -) ⟶ f'_* ((g')* -)`
associated to a cartesian square
```
     g'
X' ─────→ X
│         │
f'        f
↓         ↓
S' ─────→ S
     g
```
in `Scheme`. Constructed as the *mate* (Beck–Chevalley transform)
under the `pullback ⊣ pushforward` adjunctions on sheaves of modules
of the canonical 2-isomorphism
`pullback g ⋙ pullback f' ≅ pullback f ⋙ pullback g'` coming from
`g' ≫ f = f' ≫ g`.

This natural transformation always exists (no flatness needed). The
content of the flat base-change theorem (Stacks tag 02KH) is the
*isomorphism* claim under the hypotheses
`[QuasiCompact f] [QuasiSeparated f] [Flat g]`; that claim is the
helper `canonicalBaseChangeMap_isIso`. -/
noncomputable def canonicalBaseChangeMap
    {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback g ⟶
      Scheme.Modules.pullback g' ⋙ Scheme.Modules.pushforward f' :=
  CategoryTheory.mateEquiv
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f')
      (((Scheme.Modules.pullbackComp f' g) ≪≫
        Scheme.Modules.pullbackCongr sq.w.symm ≪≫
        (Scheme.Modules.pullbackComp g' f).symm).hom)

/-- Sections of `(pushforward f').obj ((pullback g').obj F)` over an open
`U ⊆ S'` are definitionally the sections of `(pullback g').obj F` over the
preimage `f' ⁻¹ᵁ U`, by `Scheme.Modules.pushforward_obj_obj`. -/
private lemma pushforward_pullback_section_eq_pullback_section
    {X X' S' : Scheme.{u}} (f' : X' ⟶ S') (g' : X' ⟶ X)
    (F : X.Modules) (U : S'.Opens) :
    Γ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F), U) =
      Γ((Scheme.Modules.pullback g').obj F, f' ⁻¹ᵁ U) := rfl

/-! ### Affine-open section formula for `Scheme.Modules.pullback`

The section formula identifies

  `Γ((pullback g).obj N, U)  ≃  Γ(Y, U) ⊗_{Γ(X, V)} Γ(N, V)`

for any compatible affine pair `(V ⊆ X, U ⊆ Y)` of a morphism `g : Y ⟶ X`
of schemes and a quasi-coherent sheaf of `O_X`-modules `N` (Stacks 01HQ).
The pullback functor `Scheme.Modules.pullback g` is built as
`SheafOfModules.pullback` via the partial-adjoint machinery, so no
closed-form description of its sections is available and the formula has to
be established by hand. The substantive claim is
`pullback_app_isoTensor_isBaseChange`, proved by the `tilde` route on `Spec`
(`pullback_tildeIso` together with
`pullback_app_isoTensor_baseMap_sectionLinearEquiv`), then promoted to a
general affine open of `Y`. -/

/-- The base linear map underlying `pullback_app_isoTensor`.

It is built from the unit of the `pullback ⊣ pushforward` adjunction at the
`V`-section level: the unit is a morphism of `𝒪_X`-modules
`N ⟶ (pushforward g).obj ((pullback g).obj N)`, and evaluating its
underlying `PresheafOfModules`-val at `V` gives a `Γ(X, V)`-linear map
`Γ(N, V) →ₗ[Γ(X, V)] Γ((pushforward g).obj ((pullback g).obj N), V)`.
By `pushforward_obj_obj` (definitional), the codomain is the same data as
`Γ((pullback g).obj N, g ⁻¹ᵁ V)` with `Γ(X, V)` acting through restriction
of scalars along `g.app V`.

That this map exhibits the target as a base change — the algebraic content of
Stacks 02KE / 01HQ — is the separate statement
`pullback_app_isoTensor_isBaseChange`, from which the section formula follows
by `IsBaseChange.equiv.symm`. -/
private noncomputable def pullback_app_isoTensor_unitAtV
    {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules) (V : X.Opens) :
    Γ(N, V) →ₗ[Γ(X, V)]
      Γ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj N), V) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).val.app (.op V)).hom

/-- The `Γ(X, V)`-linear base map for the affine-open section formula.

Combining the unit `pullback_app_isoTensor_unitAtV` with the
presheaf-restriction `((pullback g).obj N).presheaf.map (homOfLE e).op` (from
the larger open `g ⁻¹ᵁ V` to the smaller open `U`) gives a `Γ(X, V)`-linear
map
`Γ(N, V) →ₗ[Γ(X, V)] Γ((pullback g).obj N, U)`,
where the `Γ(X, V)`-action on the target is via the algebra map
`(g.appLE V U e).hom : Γ(X, V) ⟶ Γ(Y, U)`.

The codomain of `unitAtV`,
`Γ((pushforward g).obj ((pullback g).obj N), V)`, is definitionally equal
to `Γ((pullback g).obj N, g ⁻¹ᵁ V)` by `pushforward_obj_obj` (rfl), which is
what makes the composition with the presheaf restriction typecheck.

`Γ(X, V)`-linearity uses the defining decomposition
`g.appLE V U e = g.app V ≫ Y.presheaf.map (homOfLE e).op`
(definitional from `AlgebraicGeometry.Scheme.Hom.appLE`): linearity in the
source over `Γ(X, V)` is inherited from `unitAtV` (via `g.app V`),
linearity in the target's restriction-of-scalars action is the
`Γ(Y, g ⁻¹ᵁ V)`-linearity of the presheaf-restriction map, and the two
chain definitionally to give `Γ(X, V)`-linearity.

That this map is a base change is the separate statement
`pullback_app_isoTensor_baseMap_isBaseChange`. -/
noncomputable def pullback_app_isoTensor_baseMap
    {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules)
    {U : Y.Opens} {V : X.Opens} (e : U ≤ g ⁻¹ᵁ V) :
    letI : Algebra Γ(X, V) Γ(Y, U) := (g.appLE V U e).hom.toAlgebra
    letI : Module Γ(X, V) Γ((Scheme.Modules.pullback g).obj N, U) :=
      Module.compHom _ (g.appLE V U e).hom
    Γ(N, V) →ₗ[Γ(X, V)] Γ((Scheme.Modules.pullback g).obj N, U) := by
  letI algInst : Algebra Γ(X, V) Γ(Y, U) := (g.appLE V U e).hom.toAlgebra
  letI modInst : Module Γ(X, V) Γ((Scheme.Modules.pullback g).obj N, U) :=
    Module.compHom _ (g.appLE V U e).hom
  -- The presheaf restriction map (Γ(Y, g ⁻¹ᵁ V)-linear; the source's
  -- underlying type matches the codomain of `unitAtV` definitionally).
  let restr := (((Scheme.Modules.pullback g).obj N).presheaf.map (homOfLE e).op).hom
  -- The Γ(X, V)-linear adjunction unit at the V section.
  let unit := pullback_app_isoTensor_unitAtV g N V
  refine
    { toFun := fun x => restr (unit x)
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    change restr (unit (x + y)) = restr (unit x) + restr (unit y)
    rw [unit.map_add]
    exact restr.map_add _ _
  · intro r x
    change restr (unit (r • x)) = (g.appLE V U e).hom r • restr (unit x)
    -- `unit.map_smul` is over `Γ(X, V)`; the codomain action equals the
    -- `Γ(Y, g ⁻¹ᵁ V)`-action via `g.app V` (definitional from
    -- `Scheme.Modules.pushforward`). Then `restr` is `Γ(Y, g ⁻¹ᵁ V)`-linear
    -- (via `Scheme.Modules.map_smul` applied to the Y-side). The chain
    -- gives action through
    -- `Y.presheaf.map (homOfLE e).op ∘ g.app V = g.appLE V U e` (definitional
    -- from `Scheme.Hom.appLE`).
    rw [unit.map_smul]
    exact ((Scheme.Modules.pullback g).obj N).map_smul (homOfLE e) _ _

/-! #### `baseMap` coherence lemmas (T12, 2026-07-03)

The (N1)/(N2)/(N3) substrate helpers for the Beck-Chevalley intertwining at
`pullback_app_isoTensor_baseMap_sectionLinearEquiv` (see the 6-stage plan in
its body). All three are proved elementwise by `congrArg`/`Eq.trans` chains
from unit naturality, `unit_conjugateEquiv` + Mathlib's
`conjugateEquiv_pullbackComp_inv`, and proof irrelevance of `Opens`-homs. -/

set_option backward.isDefEq.respectTransparency false in
/-- Composition collapse for section restrictions of a sheaf of modules. -/
private lemma modules_res_res {Y : Scheme.{u}} (N : Y.Modules) {W₁ W₂ W₃ : Y.Opens}
    (i₁ : W₁ ≤ W₂) (i₂ : W₂ ≤ W₃) (i₃ : W₁ ≤ W₃) (ξ : Γ(N, W₃)) :
    (N.presheaf.map (homOfLE i₁).op).hom ((N.presheaf.map (homOfLE i₂).op).hom ξ) =
      (N.presheaf.map (homOfLE i₃).op).hom ξ := by
  rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp, ← op_comp]
  exact (congrArg (fun (i : W₁ ⟶ W₃) =>
    (AddCommGrpCat.Hom.hom (N.presheaf.map i.op)) ξ) (Subsingleton.elim _ _)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Hom-generic variant of `modules_res_res` (for non-`homOfLE` opens homs, e.g.
`opensFunctor`-images and `eqToHom`s; `Opens`-homs are proof-irrelevant). -/
private lemma modules_res_res_hom {Y : Scheme.{u}} (N : Y.Modules) {W₁ W₂ W₃ : Y.Opens}
    (i₁ : W₁ ⟶ W₂) (i₂ : W₂ ⟶ W₃) (i₃ : W₁ ⟶ W₃) (ξ : Γ(N, W₃)) :
    (N.presheaf.map i₁.op).hom ((N.presheaf.map i₂.op).hom ξ) =
      (N.presheaf.map i₃.op).hom ξ := by
  rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp, ← op_comp]
  exact (congrArg (fun (i : W₁ ⟶ W₃) =>
    (AddCommGrpCat.Hom.hom (N.presheaf.map i.op)) ξ) (Subsingleton.elim _ _)).symm

set_option backward.isDefEq.respectTransparency false in
/-- **(N1) `baseMap` naturality in the sheaf argument**: the canonical base map
commutes with morphisms of sheaves of modules, via naturality of the
`pullback ⊣ pushforward` adjunction unit. -/
private lemma pullback_app_isoTensor_baseMap_naturality
    {X Y : Scheme.{u}} (g : Y ⟶ X) {N N' : X.Modules}
    (h : N ⟶ N') {U : Y.Opens} {V : X.Opens} (e : U ≤ g ⁻¹ᵁ V) (x : Γ(N, V)) :
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g).map h) U).hom
        (pullback_app_isoTensor_baseMap g N e x) =
      pullback_app_isoTensor_baseMap g N' e ((Scheme.Modules.Hom.app h V).hom x) := by
  -- (b) unit naturality at `V`-sections:
  have hb := congrArg
    (fun (k : N ⟶ (Scheme.Modules.pushforward g).obj
        ((Scheme.Modules.pullback g).obj N')) =>
      (Scheme.Modules.Hom.app k V).hom x)
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality h)
  -- (a) naturality of `(pullback g).map h` against the restriction `U ≤ g ⁻¹ᵁ V`:
  have ha := congrArg
    (fun (k : Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ V) ⟶
        Γ((Scheme.Modules.pullback g).obj N', U)) =>
      (AddCommGrpCat.Hom.hom k) (pullback_app_isoTensor_unitAtV g N V x))
    ((Scheme.Modules.Hom.mapPresheaf ((Scheme.Modules.pullback g).map h)).naturality
      (homOfLE e).op)
  exact ha.trans (congrArg
    (fun w => ((((Scheme.Modules.pullback g).obj N').presheaf.map (homOfLE e).op).hom) w)
    hb.symm)

set_option backward.isDefEq.respectTransparency false in
/-- **(N3) `baseMap` transport along `pullbackCongr`** (propositional equality of
morphisms). -/
private lemma pullback_app_isoTensor_baseMap_congr
    {X Y : Scheme.{u}} {g g' : Y ⟶ X} (hgg' : g = g')
    (N : X.Modules) {U : Y.Opens} {V : X.Opens} (e : U ≤ g ⁻¹ᵁ V) (e' : U ≤ g' ⁻¹ᵁ V)
    (x : Γ(N, V)) :
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hgg').hom.app N) U).hom
        (pullback_app_isoTensor_baseMap g N e x) =
      pullback_app_isoTensor_baseMap g' N e' x := by
  subst hgg'
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- The composed-adjunction unit expands nested pullback and restriction transports.
/-- **(N2) `baseMap` compatibility with `pullbackComp`**: iterated base maps along a
composable pair compose (through `pullbackComp`) to the base map of the composite.
From `unit_conjugateEquiv` and Mathlib's `conjugateEquiv_pullbackComp_inv`. -/
private lemma pullback_app_isoTensor_baseMap_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Modules)
    {T : X.Opens} {V : Y.Opens} {U : Z.Opens}
    (eV : V ≤ g ⁻¹ᵁ U) (eT : T ≤ f ⁻¹ᵁ V) (eTU : T ≤ (f ≫ g) ⁻¹ᵁ U) (x : Γ(N, U)) :
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f g).hom.app N) T).hom
        (pullback_app_isoTensor_baseMap f ((Scheme.Modules.pullback g).obj N) eT
          (pullback_app_isoTensor_baseMap g N eV x)) =
      pullback_app_isoTensor_baseMap (f ≫ g) N eTU x := by
  -- (s1) naturality of the `f`-unit component against the restriction `V ≤ g ⁻¹ᵁ U`:
  have hs1 := congrArg
    (fun (k : Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ U) ⟶
        Γ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj
          ((Scheme.Modules.pullback g).obj N)), V)) =>
      (AddCommGrpCat.Hom.hom k) (pullback_app_isoTensor_unitAtV g N U x))
    ((Scheme.Modules.Hom.mapPresheaf
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback g).obj N))).naturality (homOfLE eV).op)
  -- (s2) the composed-adjunction unit is the `pullbackComp.inv`-twist of the
  -- `(f ≫ g)`-unit.
  have hconj := Scheme.Modules.conjugateEquiv_pullbackComp_inv f g
  have hunit := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    ((Scheme.Modules.pullbackComp f g).inv) N
  rw [hconj] at hunit
  have hs2 := congrArg
    (fun (k : N ⟶ (Scheme.Modules.pushforward (f ≫ g)).obj
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N))) =>
      (Scheme.Modules.Hom.app k U).hom x) hunit
  -- (s3) naturality of `pullbackComp.inv.app N` against the restriction
  -- `T ≤ (f ≫ g) ⁻¹ᵁ U`:
  have hs3 := congrArg
    (fun (k : Γ((Scheme.Modules.pullback (f ≫ g)).obj N, (f ≫ g) ⁻¹ᵁ U) ⟶
        Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N), T)) =>
      (AddCommGrpCat.Hom.hom k) (pullback_app_isoTensor_unitAtV (f ≫ g) N U x))
    ((Scheme.Modules.Hom.mapPresheaf
      ((Scheme.Modules.pullbackComp f g).inv.app N)).naturality (homOfLE eTU).op)
  -- (s4) hom-inv cancellation of `pullbackComp` at `T`-sections:
  have hs4 : ∀ (ξ : Γ((Scheme.Modules.pullback (f ≫ g)).obj N, T)),
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f g).hom.app N) T).hom
        ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f g).inv.app N) T).hom ξ)
        = ξ := fun ξ => congrArg
    (fun (k : (Scheme.Modules.pullback (f ≫ g)).obj N ⟶
        (Scheme.Modules.pullback (f ≫ g)).obj N) =>
      (Scheme.Modules.Hom.app k T).hom ξ)
    (Iso.inv_hom_id_app (Scheme.Modules.pullbackComp f g) N)
  refine (congrArg (fun w =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f g).hom.app N) T).hom
      ((((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N)).presheaf.map
        (homOfLE eT).op).hom w)) hs1).trans ?_
  refine (congrArg (fun w =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f g).hom.app N) T).hom w)
    (modules_res_res ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N))
      eT ((fun _ ha => eV ha) : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U))
      eTU (pullback_app_isoTensor_unitAtV f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ U)
        (pullback_app_isoTensor_unitAtV g N U x)))).trans ?_
  refine (congrArg (fun w =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f g).hom.app N) T).hom
      ((((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N)).presheaf.map
        (homOfLE eTU).op).hom w)) hs2).trans ?_
  refine (congrArg (fun w =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f g).hom.app N) T).hom w)
    hs3.symm).trans ?_
  exact hs4 _



/-! ============================================================================
  UNION MERGE (2026-06-22, from subproject `GR-quot_closure`)

  Everything below this banner is the Grassmannian/Quot *quasi-coherent descent*
  development imported verbatim from the subproject's `Picard/QuotScheme.lean`
  (its post-`Grassmannian.representable` body). It is the rider machinery that
  the imported files `GrassmannianCells`, `GlueDescent`, `GrassmannianQuot`
  depend on (localized-module / quasicoherent descent: `isLocalizedModule_*`,
  `isIso_fromTildeΓ_*`, `annihilator`, `schematicSupport`, presentation-pullback
  machinery). The base-change cohomology lane above the banner is this project's
  own; both are preserved in full.
============================================================================ -/

/-! ## Project-local Mathlib supplement — annihilator ideal sheaf and schematic support

These declarations build the annihilator ideal sheaf of a sheaf of modules and the
support/properness predicates of `blueprint/src/chapters/Picard_QuotScheme.tex`,
§"Support and freeness predicates". Mathlib (at the pinned commit) carries no
annihilator ideal sheaf for sheaves of modules on a scheme, nor a schematic-support
or proper-support predicate, so they are built here.

The annihilator is packaged via `Scheme.IdealSheafData.ofIdeals`, exactly mirroring
Mathlib's `Scheme.Hom.ker` (which is `ofIdeals fun U ↦ RingHom.ker (f.app U).hom`):
`ofIdeals` produces *the largest ideal sheaf contained in* an arbitrary affine-local
family of ideals, so the structure's `map_ideal_basicOpen` coherence is discharged
internally and need not be supplied at definition time. The basic-open coherence that
makes the local annihilators agree with `ofIdeals` (the analogue of `Hom.ker_apply`,
`def:modules_annihilator`) is the separate characterization lemma `annihilator_ideal`,
which depends on the not-yet-closed QCoh→localization bridge
`isLocalizedModule_basicOpen` (`lem:qcoh_section_localization_basicOpen`) together with
the algebra engine `Module.annihilator_isLocalizedModule_eq_map`
(`lem:annihilator_localization_eq_map`); see the handoff in
`task_results/.../QuotScheme.md`. -/

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- The **annihilator ideal sheaf** of a sheaf of modules `F` on a scheme `X`
(`def:modules_annihilator`).

On each affine open `U`, the intended section is the annihilator
`Ann_{Γ(X,U)}(Γ(F,U))` of the `Γ(X,U)`-module of sections `Γ(F,U)`. The ideal sheaf
is assembled with `Scheme.IdealSheafData.ofIdeals`, the largest ideal sheaf contained
in that affine-local family — exactly the construction used for `Scheme.Hom.ker`. This
sidesteps proving the basic-open coherence (`map_ideal_basicOpen`) at definition time;
the identity `(annihilator F).ideal U = Ann_{Γ(X,U)}(Γ(F,U))` is the downstream
characterization lemma (`annihilator_ideal`, blocked on the QCoh localization bridge).

This is a project-local primitive: Mathlib does not carry an annihilator ideal sheaf
for sheaves of modules on a scheme. -/
noncomputable def annihilator (F : X.Modules) : X.IdealSheafData :=
  IdealSheafData.ofIdeals fun U => Module.annihilator Γ(X, U.1) Γ(F, U.1)

/-- The component of the annihilator ideal sheaf at an affine open is contained in the
module annihilator of the sections. This is the always-available (`ofIdeals`) direction
of the characterization; the reverse inclusion is the basic-open coherence blocked on
`isLocalizedModule_basicOpen`. Project-local because `annihilator` is. -/
lemma annihilator_ideal_le (F : X.Modules) (U : X.affineOpens) :
    (annihilator F).ideal U ≤ Module.annihilator Γ(X, U.1) Γ(F, U.1) :=
  IdealSheafData.ideal_ofIdeals_le _ _

/-- The **schematic support** of a sheaf of modules `F` on a scheme `X`
(`def:schematic_support`): the closed subscheme of `X` cut out by the annihilator
ideal sheaf `annihilator F`. Project-local because `annihilator` is. -/
noncomputable def schematicSupport (F : X.Modules) : Scheme.{u} :=
  (annihilator F).subscheme

/-- The canonical closed immersion of the schematic support into the ambient scheme,
realizing `schematicSupport F` as a closed subscheme of `X` (`def:schematic_support`).
This is the `IdealSheafData.subschemeι` of the annihilator ideal sheaf; it is a
`IsPreimmersion` + `QuasiCompact` immersion onto the support. Project-local because
`annihilator` is. -/
noncomputable def schematicSupportι (F : X.Modules) : schematicSupport F ⟶ X :=
  (annihilator F).subschemeι

/-- The sheaf of modules `F` **has proper support over `S` along `f`**
(`def:has_proper_support`): the composite of the schematic-support immersion with
`f : X ⟶ S` is a proper morphism. Since `AlgebraicGeometry.IsProper` is stable under
base change, this condition is preserved by pullback, as required by the Quot functor's
pullback action. Project-local because `schematicSupport` is. -/
def HasProperSupport {S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) : Prop :=
  IsProper (schematicSupportι F ≫ f)

end Scheme.Modules

end AlgebraicGeometry

/-! ## Project-local Mathlib supplement — annihilator under localization

The annihilator ideal sheaf `def:modules_annihilator` of a coherent sheaf is
built from the affine-local data `U ↦ Ann_{O(U)}(F(U))`, packaged as a
`Scheme.IdealSheafData`. The structure's coherence field `map_ideal_basicOpen`
requires the algebraic fact that, for a *finitely generated* module, the
annihilator commutes with localization:
`Ann(S⁻¹M) = (Ann M)·S⁻¹R`. Mathlib (at the pinned commit) does not carry this
lemma, so it is supplied here as the load-bearing engine for that construction.
-/

namespace Module

/-- For a finitely generated module `M` over a commutative ring `R`, the
annihilator commutes with localization: if `Rₚ` localizes `R` at a submonoid
`S` and `f : M →ₗ[R] Mₚ` localizes `M` at `S`, then the annihilator of `Mₚ`
over `Rₚ` is the extension (`Ideal.map` along `algebraMap R Rₚ`) of the
annihilator of `M` over `R`.

This is the abstract `IsLocalization`/`IsLocalizedModule` form, matching the
shape needed for the affine-basic-open coherence of the annihilator ideal sheaf
(`AlgebraicGeometry.Scheme.Modules.annihilator`, `def:modules_annihilator`):
the structure-sheaf restriction `Γ(X,U) → Γ(X, D(f))` is
`IsLocalization (powers f)`, and for a quasi-coherent `F` the section
restriction is `IsLocalizedModule (powers f)`.

Mathlib has no annihilator-localization lemma, so this is project-local. -/
theorem annihilator_isLocalizedModule_eq_map
    {R : Type*} [CommRing R] (S : Submonoid R)
    {Rₚ : Type*} [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization S Rₚ]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {Mₚ : Type*} [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule S f] :
    Module.annihilator Rₚ Mₚ = (Module.annihilator R M).map (algebraMap R Rₚ) := by
  classical
  obtain ⟨t, htop⟩ := (Module.Finite.fg_top (R := R) (M := M))
  -- annihilating a spanning finset suffices for membership in the annihilator
  have key : ∀ (r : R), (∀ m ∈ t, r • m = 0) → r ∈ Module.annihilator R M := by
    intro r h
    rw [Module.mem_annihilator]
    intro x
    have hx : x ∈ Submodule.span R (t : Set M) := htop ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add, ha, hb, add_zero]
    | smul c a _ ha => rw [smul_comm, ha, smul_zero]
  apply le_antisymm
  · -- `Ann Rₚ Mₚ ⊆ (Ann R M).map`: clear one common denominator over the generators
    intro y hy
    rw [Module.mem_annihilator] at hy
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S y
    dsimp only at hy ⊢
    have hgen : ∀ m ∈ t, ∃ u : S, (u : R) • a • m = 0 := by
      intro m hm
      have hz := hy (IsLocalizedModule.mk' f m (1 : S))
      rw [IsLocalizedModule.mk'_smul_mk' Rₚ f, IsLocalizedModule.mk'_eq_zero,
        IsLocalizedModule.eq_zero_iff S f] at hz
      obtain ⟨u, hu⟩ := hz
      exact ⟨u, hu⟩
    choose u hu using hgen
    obtain ⟨U, hU⟩ : ∃ U : S, ∀ m ∈ t, (U : R) • a • m = 0 := by
      refine ⟨∏ x ∈ t.attach, u x.1 x.2, ?_⟩
      intro m hm
      obtain ⟨c, hc⟩ :=
        Finset.dvd_prod_of_mem (fun x : t => u x.1 x.2) (Finset.mem_attach t ⟨m, hm⟩)
      have hcoe : ((∏ x ∈ t.attach, u x.1 x.2 : S) : R) = (u m hm : R) * (c : R) := by
        rw [hc]; push_cast; ring
      rw [hcoe, mul_smul, smul_comm, hu m hm, smul_zero]
    have hUa : (U : R) * a ∈ Module.annihilator R M := by
      apply key; intro m hm; rw [mul_smul]; exact hU m hm
    have heq : IsLocalization.mk' Rₚ a s
        = (algebraMap R Rₚ ((U : R) * a)) * IsLocalization.mk' Rₚ 1 (U * s) := by
      rw [← IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_eq_iff_eq]
      push_cast; ring
    rw [heq]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hUa)
  · -- `(Ann R M).map ⊆ Ann Rₚ Mₚ`: the image of an annihilator annihilates
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Module.mem_annihilator]
    rw [Module.mem_annihilator] at ha
    intro x
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
    dsimp only [Function.uncurry]
    rw [← IsLocalization.mk'_one (M := S) Rₚ a, IsLocalizedModule.mk'_smul_mk' Rₚ f, ha m,
      IsLocalizedModule.mk'_zero]

end Module

/-! ## Project-local Mathlib supplement — quasi-coherent sections localize on a basic open

This section builds, bottom-up, toward the keystone
`lem:qcoh_section_localization_basicOpen`: for a quasi-coherent sheaf of modules `M`
on a scheme `X`, an affine open `U`, and `f ∈ Γ(X,U)`, the restriction
`M(U) → M(D(f))` exhibits `M(D(f))` as `IsLocalizedModule (powers f)` over `Γ(X,U)`.

The substance is the affine (Spec-local) computation: over `Spec R`, a quasi-coherent
sheaf is `Ñ = tilde N` for `N = Γ(M)`, and the basic-open restriction of `Ñ` is the
module localization map. Mathlib's `AlgebraicGeometry.tilde` namespace already carries
the localization fact for `tilde N` *as the map out of `N`* (the instance
`IsLocalizedModule (.powers f) (tilde.toOpen N (basicOpen f)).hom`). The first building
block below repackages this as a statement about the *presheaf restriction map* of `Ñ`
itself (from global sections to `D(f)`), which is the form the downstream scheme-level
argument consumes after the affine identification `M|_U ≅ Ñ`.

Mathlib (at the pinned commit) does **not** prove that an arbitrary quasi-coherent sheaf
on `Spec R` lies in the essential image of `tilde` (the comment in
`Mathlib/AlgebraicGeometry/Modules/Tilde.lean` says this "will later be shown"); the
equivalence `QCoh(Spec R) ≃ Mod R` is a genuine gap. Consequently the keystone for an
*arbitrary* quasi-coherent `M` is gated on that bridge (`IsQuasicoherent M → IsIso
M.fromTildeΓ`); the building blocks here are stated for `tilde N` directly, and for a
general `M : (Spec R).Modules` under the explicit hypothesis `[IsIso M.fromTildeΓ]`
(equivalently, `M` in the essential image of `tilde`). -/

namespace AlgebraicGeometry

open CategoryTheory Limits

/-- **Basic-open restriction of a `tilde` sheaf is a module localization.**

For `N : ModuleCat R` and `f : R`, the presheaf restriction map of the associated sheaf
`Ñ = tilde N` from global sections `Γ(Ñ, ⊤)` to the basic open `Γ(Ñ, D(f))` exhibits the
latter as `IsLocalizedModule (powers f)` over `R`.

This is the affine, Spec-local heart of `lem:qcoh_section_localization_basicOpen`. Mathlib
carries the localization fact for the map `tilde.toOpen N (D f) : N → Γ(Ñ, D(f))` out of
`N`; since `tilde.toOpen N ⊤ : N → Γ(Ñ, ⊤)` is an isomorphism and
`tilde.toOpen N (D f) = tilde.toOpen N ⊤ ≫ restriction` (`tilde.toOpen_res`), precomposing
the localization map with the inverse isomorphism (`IsLocalizedModule.of_linearEquiv_right`)
transfers the property to the restriction map. Project-local: Mathlib states the fact only
for the map out of `N`, not for the presheaf restriction of `Ñ`. -/
theorem isLocalizedModule_tilde_restrict {R : CommRingCat.{u}} (N : ModuleCat.{u} R) (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj (tilde N)).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by
  set res := (modulesSpecToSheaf.obj (tilde N)).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op with hresdef
  have hres := tilde.toOpen_res N ⊤ (PrimeSpectrum.basicOpen f)
    (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤))
  -- `e : N ≃ₗ Γ(Ñ, ⊤)` is the global-sections isomorphism of the tilde sheaf.
  set e : N ≃ₗ[R] _ := (tilde.isoTop N).toLinearEquiv with hedef
  have key : (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom = res.hom ∘ₗ e.toLinearMap := by
    rw [hedef, ← hres]; rfl
  have hinst0 : IsLocalizedModule (Submonoid.powers f)
      (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom := inferInstance
  rw [key] at hinst0
  set g := res.hom ∘ₗ e.toLinearMap with hg
  haveI : IsLocalizedModule (Submonoid.powers f) g := hinst0
  have h2 := IsLocalizedModule.of_linearEquiv_right (S := Submonoid.powers f) (f := g) e.symm
  have he : g ∘ₗ e.symm.toLinearMap = res.hom := by
    apply LinearMap.ext; intro x
    change res.hom (e (e.symm x)) = res.hom x
    rw [e.apply_symm_apply]
  rw [he] at h2
  exact h2

/-- **Basic-open restriction localizes, for a sheaf in the essential image of `tilde`.**

For a sheaf of modules `M` on `Spec R` whose tilde-Gamma counit `M.fromTildeΓ` is an
isomorphism (equivalently, `M` lies in the essential image of the `tilde` functor — the
honest Spec-affine stand-in for quasi-coherence, see the section header), the presheaf
restriction map of `M` from global sections `Γ(M, ⊤)` to the basic open `Γ(M, D(f))`
exhibits the latter as `IsLocalizedModule (powers f)` over `R`.

This transports `isLocalizedModule_tilde_restrict` across the isomorphism
`M.fromTildeΓ : tilde N ⟶ M` (where `N = Γ(M, ⊤)`): the induced presheaf isomorphism is
natural in the open, so on each of `⊤` and `D(f)` it provides an `R`-linear isomorphism
intertwining the two restriction maps. Post- and pre-composing the localization map for
`tilde N` with these isomorphisms (`IsLocalizedModule.of_linearEquiv`,
`IsLocalizedModule.of_linearEquiv_right`) yields the property for `M`.

Project-local: it is the affine engine of `lem:qcoh_section_localization_basicOpen`. The
general quasi-coherent case additionally requires the (currently Mathlib-absent) bridge
`IsQuasicoherent M → IsIso M.fromTildeΓ`. -/
theorem isLocalizedModule_restrict_of_isIso_fromTildeΓ {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ] (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by
  -- the presheaf-level isomorphism induced by the (iso) counit `M.fromTildeΓ`
  let ψ := (TopCat.Sheaf.forget (ModuleCat R) (Spec R)).map (modulesSpecToSheaf.map M.fromTildeΓ)
  haveI : IsIso ψ := inferInstance
  haveI : IsIso (ψ.app (.op (⊤ : (Spec R).Opens))) := inferInstance
  haveI : IsIso (ψ.app (.op (PrimeSpectrum.basicOpen f))) := inferInstance
  -- the component isomorphisms as `R`-linear equivalences
  let eTop : _ ≃ₗ[R] _ := (asIso (ψ.app (.op (⊤ : (Spec R).Opens)))).toLinearEquiv
  let eDf : _ ≃ₗ[R] _ := (asIso (ψ.app (.op (PrimeSpectrum.basicOpen f)))).toLinearEquiv
  -- the restriction map of `tilde N` (localizes by `isLocalizedModule_tilde_restrict`)
  let rt := ((modulesSpecToSheaf.obj
        (tilde ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)))).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom
  -- naturality square of `ψ` for `D(f) ⟶ ⊤`
  have hnat := ψ.naturality (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op
  have hnathom := congrArg ModuleCat.Hom.hom hnat
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hnathom
  haveI hrt : IsLocalizedModule (Submonoid.powers f) rt :=
    isLocalizedModule_tilde_restrict ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) f
  haveI step1 : IsLocalizedModule (Submonoid.powers f) (eDf.toLinearMap ∘ₗ rt) :=
    IsLocalizedModule.of_linearEquiv (S := Submonoid.powers f) (f := rt) (e := eDf)
  haveI step2 : IsLocalizedModule (Submonoid.powers f)
      ((eDf.toLinearMap ∘ₗ rt) ∘ₗ eTop.symm.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (S := Submonoid.powers f)
      (f := eDf.toLinearMap ∘ₗ rt) (e := eTop.symm)
  -- identify the target restriction map with `(eDf ∘ rt) ∘ eTop⁻¹`
  convert step2 using 1 <;> try rfl
  refine heq_of_eq ?_
  apply LinearMap.ext; intro x
  have hc := LinearMap.congr_fun hnathom (eTop.symm x)
  simp only [LinearMap.comp_apply] at hc ⊢
  refine (?_ : _ = _).trans hc.symm
  congr 1
  exact (eTop.apply_symm_apply x).symm

/-- A morphism of sheaves of `R`-modules on `Spec R` that is an isomorphism on every basic open
`D(f)` is an isomorphism. This is the "isomorphism on a basis ⟹ isomorphism" reduction specialised
to the basic-open basis of `Spec R` (`PrimeSpectrum.isBasis_basic_opens`): injectivity on stalks is
`stalkFunctor_map_injective_of_isBasis`, surjectivity on stalks is the basic-open germ lift, and
`isIso_of_stalkFunctor_map_iso` concludes. Project-local glue used to assemble `IsIso M.fromTildeΓ`
from per-basic-open section data. -/
private theorem isIso_sheaf_of_isIso_app_basicOpen {R : CommRingCat.{u}}
    {F G : TopCat.Sheaf (ModuleCat.{u} R) (Spec R)} (α : F ⟶ G)
    (h : ∀ f : R, IsIso (α.1.app (.op (PrimeSpectrum.basicOpen f)))) : IsIso α := by
  have hB : TopologicalSpace.Opens.IsBasis (Set.range (@PrimeSpectrum.basicOpen R _)) :=
    PrimeSpectrum.isBasis_basic_opens
  have hinj : ∀ U ∈ Set.range (@PrimeSpectrum.basicOpen R _),
      Function.Injective (α.1.app (.op U)) := by
    rintro U ⟨f, rfl⟩
    exact ((ConcreteCategory.isIso_iff_bijective _).mp (h f)).1
  have hstalk : ∀ x, IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map α.1) := by
    intro x
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB hinj x, ?_⟩
    intro t
    obtain ⟨U, hxU, hUB, s, rfl⟩ := TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB G.presheaf x t
    obtain ⟨f, rfl⟩ := hUB
    obtain ⟨s', rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).mp (h f)).2 s
    exact ⟨F.presheaf.germ _ x hxU s', by rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]⟩
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso α

/-- A linear map intertwining two localizations of the same module at the same submonoid is
bijective: if `f : M →ₗ M'` and `g : M →ₗ M''` both exhibit a localization at `S` and
`h : M' →ₗ M''` satisfies `h ∘ₗ f = g`, then `h` is bijective (it is the canonical localization
isomorphism `IsLocalizedModule.linearEquiv`). Stated with the two `IsLocalizedModule` facts as
explicit hypotheses to avoid typeclass-diamond ambiguity at the call site. -/
private theorem bijective_comp_of_localizations {R : Type u} [CommRing R] (S : Submonoid R)
    {M M' M'' : Type u} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M''] {f : M →ₗ[R] M'} {g : M →ₗ[R] M''} {h : M' →ₗ[R] M''}
    (hf : IsLocalizedModule S f) (hg : IsLocalizedModule S g) (hh : h ∘ₗ f = g) :
    Function.Bijective h := by
  haveI := hf; haveI := hg
  have heq : h = (IsLocalizedModule.linearEquiv S f g).toLinearMap := by
    apply IsLocalizedModule.linearMap_ext S (f := f) (f' := g)
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← LinearMap.comp_apply, hh,
      LinearEquiv.coe_toLinearMap, IsLocalizedModule.linearEquiv_apply]
  rw [heq]
  exact (IsLocalizedModule.linearEquiv S f g).bijective

/-- **`IsIso M.fromTildeΓ` from per-basic-open section localization** (the cheap stalk/section
assembly of `lem:qcoh_affine_isIso_fromTildeΓ`, the blueprint "G1-assemble" step). If for every
`f : R` the section restriction `Γ(M, ⊤) → Γ(M, D(f))` of a sheaf of modules `M` on `Spec R`
exhibits the target as `IsLocalizedModule (powers f)` over `R` — exactly the conclusion of G1-core
(`lem:qcoh_affine_section_localization`,
`isLocalizedModule_basicOpen_of_isQuasicoherent`) — then the tilde-Gamma counit `M.fromTildeΓ` is
an isomorphism (equivalently `M` lies in the essential image of `tilde`).

On each basic open `D(f)` the component of `modulesSpecToSheaf.map M.fromTildeΓ` is a map between
two localizations of `N = Γ(M, ⊤)` at `powers f`: the source `Γ(tilde N, D(f))` localizes via the
instance `tilde.toOpen N (D f)` and the target `Γ(M, D(f))` localizes by hypothesis, and the two
localization maps are intertwined by `Scheme.Modules.toOpen_fromTildeΓ_app`. Hence the component is
the canonical localization isomorphism (`IsLocalizedModule.linearEquiv`);
`isIso_sheaf_of_isIso_app_basicOpen` upgrades this to an isomorphism of sheaves, and
`modulesSpecToSheaf` being fully faithful reflects it to `IsIso M.fromTildeΓ`.

This turns the remaining keystone obligation into exactly G1-core: combined with the converse engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ`, the per-basic-open localization hypothesis is
*equivalent* to `IsIso M.fromTildeΓ`. Project-local: Mathlib has no `IsQuasicoherent → IsIso
fromTildeΓ` bridge. -/
theorem isIso_fromTildeΓ_of_isLocalizedModule_restrict {R : CommRingCat.{u}}
    (M : (Spec R).Modules)
    (H : ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom) :
    IsIso M.fromTildeΓ := by
  haveI hmain : IsIso (modulesSpecToSheaf.map M.fromTildeΓ) := by
    apply isIso_sheaf_of_isIso_app_basicOpen
    intro f
    set N := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤) with hN
    -- target localizes by hypothesis; source localizes by the `tilde.toOpen` instance
    haveI htgt : IsLocalizedModule (Submonoid.powers f)
        ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := H f
    set comp := (modulesSpecToSheaf.map M.fromTildeΓ).1.app (.op (PrimeSpectrum.basicOpen f))
      with hcomp
    rw [ConcreteCategory.isIso_iff_bijective]
    have hcompose := Scheme.Modules.toOpen_fromTildeΓ_app M (PrimeSpectrum.basicOpen f)
    -- the component intertwines the two localization maps of `N` at `powers f`
    have h1 : comp.hom ∘ₗ (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom
        = ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by
      have e := congrArg ModuleCat.Hom.hom hcompose
      rwa [ModuleCat.hom_comp] at e
    change Function.Bijective (⇑comp.hom)
    exact bijective_comp_of_localizations (Submonoid.powers f)
      (inferInstance : IsLocalizedModule _ (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom)
      (H f) h1
  exact SpecModulesToSheafFullyFaithful.isIso_of_isIso_map M.fromTildeΓ

/-- **Characterization of `IsIso M.fromTildeΓ` by section localization.** For a sheaf of modules
`M` on `Spec R`, the tilde-Gamma counit `M.fromTildeΓ` is an isomorphism iff for every `f : R` the
section restriction `Γ(M, ⊤) → Γ(M, D(f))` exhibits the target as `IsLocalizedModule (powers f)`.

The forward direction is the affine engine `isLocalizedModule_restrict_of_isIso_fromTildeΓ`; the
reverse is `isIso_fromTildeΓ_of_isLocalizedModule_restrict`. Combined with G1-core
(`isLocalizedModule_basicOpen_of_isQuasicoherent`, `lem:qcoh_affine_section_localization`, not yet
formalized) — which supplies the right-hand side for any quasi-coherent `M` — this yields gap1
(`lem:qcoh_affine_isIso_fromTildeΓ`). Project-local. -/
theorem isIso_fromTildeΓ_iff_isLocalizedModule_restrict {R : CommRingCat.{u}}
    (M : (Spec R).Modules) :
    IsIso M.fromTildeΓ ↔ ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom :=
  ⟨fun h f => by haveI := h; exact isLocalizedModule_restrict_of_isIso_fromTildeΓ M f,
    isIso_fromTildeΓ_of_isLocalizedModule_restrict M⟩

/-! ## Project-local Mathlib supplement — G1-core (Route F) building blocks

The keystone G1-core `lem:qcoh_affine_section_localization` asks: for a *quasi-coherent*
`M : (Spec R).Modules` and `f : R`, the section restriction `Γ(M,⊤) → Γ(M,D(f))` is
`IsLocalizedModule (powers f)`. Via `isIso_fromTildeΓ_iff_isLocalizedModule_restrict` this is
*equivalent* to `IsIso M.fromTildeΓ` — i.e. to the statement that a quasi-coherent sheaf on an
affine scheme lies in the essential image of `tilde` (the `QCoh(Spec R) ≃ Mod R` equivalence). That
equivalence is a genuine Mathlib gap at the pinned commit (Tilde.lean only proves the *globally
presented* case, `isIso_fromTildeΓ_of_presentation`).

The composition lemma below discharges the **globally-presented** sub-case end to end (it is the
Route-F endpoint once a global presentation/tilde identification is in hand). The residual gap is
exactly the production of a global presentation/tilde from local (quasi-coherent) data on `Spec R`;
see the handoff in `task_results/.../QuotScheme.md`. -/

/-- **Basic-open restriction localizes, for a globally presented module.** If `M : (Spec R).Modules`
admits a global `SheafOfModules.Presentation`, then for every `f : R` the section restriction
`Γ(M,⊤) → Γ(M,D(f))` exhibits the target as `IsLocalizedModule (powers f)` over `R`.

This is the composition of Mathlib's `isIso_fromTildeΓ_of_presentation` (a global presentation
forces `M.fromTildeΓ` to be an isomorphism, i.e. `M` is a `tilde`) with the affine engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ`. It is the Route-F endpoint for the
globally-presented case; the general quasi-coherent case additionally requires producing a global
presentation/tilde identification from the (Mathlib-absent) affine `QCoh(Spec R) ≃ Mod R` bridge.
Project-local. -/
theorem isLocalizedModule_basicOpen_of_presentation {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (_P : M.Presentation) (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by
  haveI : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_presentation M _P
  exact isLocalizedModule_restrict_of_isIso_fromTildeΓ M f

/-- **`map_units` field of G1-core (Route F), for any sheaf of modules.** For `M : (Spec R).Modules`
and `f : R`, every element of `Submonoid.powers f` acts invertibly on the sections `Γ(M, D(f))` over
`R`. This is exactly the first field `IsLocalizedModule.map_units` of the target
`isLocalizedModule_basicOpen_of_isQuasicoherent`, in the shape the 3-field constructor consumes.

It holds for an *arbitrary* `M` (no quasi-coherence needed): on `D(f)` the element `f` already maps
to a unit of the structure ring `Γ(O_{Spec R}, D(f))` (the away-localization
`IsLocalization.Away.algebraMap_isUnit`), and the `R`-action on `Γ(M, D(f))` factors through it via
the scalar tower `R → Γ(O, D(f)) → Γ(M, D(f))`. Packaged from Mathlib's
`AlgebraicGeometry.tilde.isUnit_algebraMap_end_basicOpen`. Project-local only as the *named* field
of the Route-F decomposition; the substance of G1-core is `surj`/`exists_of_eq` (see handoff). -/
theorem map_units_restrict_basicOpen {R : CommRingCat.{u}} (M : (Spec R).Modules) (f : R) :
    ∀ x : Submonoid.powers f, IsUnit (algebraMap R (Module.End R
      ((modulesSpecToSheaf.obj M).presheaf.obj
        (.op (PrimeSpectrum.basicOpen f)))) (x : R)) := by
  rintro ⟨x, n, rfl⟩
  rw [map_pow]
  exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := M) f le_rfl).pow n

/-- **Finite basic-open cover refining a quasi-coherent presentation cover.** Given a
sheaf of modules `M` on `Spec R` together with quasi-coherent data `q` (a — possibly
infinite — open cover `q.X : q.I → (Spec R).Opens` of `⊤` with a presentation of
`M.over (q.X i)` on each member), there is a *finite* family of elements `t : Finset R`
whose basic opens cover `Spec R` (`Ideal.span t = ⊤`), with each basic open `D(r)`
(`r ∈ t`) contained in some member `q.X i` of the presentation cover.

This is the topological "finite-cover front" of `lem:exists_isIso_fromTildeΓ_basicOpen_cover`:
quasi-compactness of `Spec R` plus the basic-open basis (`PrimeSpectrum.isBasis_basic_opens`)
refine `q.X` to a finite basic-open subcover; the cover condition `q.coversTop` is read off the
`Opens.grothendieckTopology` sieve via `Sieve.mem_ofObjects_iff`, and finiteness is extracted
through `Ideal.span_eq_top_iff_finite`. To obtain `q` from `[M.IsQuasicoherent]`, take
`‹M.IsQuasicoherent›.nonempty_quasicoherentData.some`.

The remaining (heavy) step toward gap1 — transporting each presentation `q.presentation i`
of `M.over (q.X i)` across `D(r) ≅ Spec R_r` to `IsIso ((M|_{D(r)}).fromTildeΓ)` — is the
site-slice ↔ scheme-pullback transport, which has no Mathlib support at the pinned commit.
Project-local: Mathlib has no affine quasi-coherent → finite presentation cover lemma. -/
theorem exists_finite_basicOpen_cover_le_quasicoherentData {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) :
    ∃ t : Finset R, Ideal.span (t : Set R) = ⊤ ∧
      ∀ r ∈ t, ∃ i, (PrimeSpectrum.basicOpen r : (Spec R).Opens) ≤ q.X i := by
  classical
  set G : Set R := {r | ∃ i, (PrimeSpectrum.basicOpen r : (Spec R).Opens) ≤ q.X i} with hG
  have hspanG : Ideal.span G = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff']
    rw [eq_top_iff]
    intro x _
    simp only [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨U, f, hf, hxU⟩ := q.coversTop ⊤ x (by trivial)
    rw [Sieve.mem_ofObjects_iff] at hf
    obtain ⟨i, ⟨hUi⟩⟩ := hf
    have hxXi : x ∈ q.X i := (leOfHom hUi) hxU
    obtain ⟨V, ⟨r, rfl⟩, hxV, hVle⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) hxXi
    exact ⟨r, ⟨i, hVle⟩, hxV⟩
  obtain ⟨t, htsub, htspan⟩ := (Ideal.span_eq_top_iff_finite G).mp hspanG
  exact ⟨t, htspan, fun r hr => htsub hr⟩

/-! ## Project-local Mathlib supplement — the over-site ↔ open-subspace sheaf equivalence

The gap1 slice-to-geometric bridge `lem:over_restrict_iso` (`overRestrictIso`) rests on an
equivalence of *sheaf* categories
`Sheaf ((Opens.grothendieckTopology X).over U) A ≌ Sheaf (Opens.grothendieckTopology ↥U) A`
induced by the equivalence of underlying sites
`Opens.overEquivalence U : Over U ≌ Opens ↥U`. Mathlib carries `Opens.overEquivalence` but leaves
the *continuity* of its two functors and the induced sheaf-category equivalence as an explicit TODO
(see `Mathlib/Topology/Sheaves/Over.lean`: "show that both functors of the equivalence
`overEquivalence U` are continuous and induce an equivalence between
`Sheaf ((Opens.grothendieckTopology X).over U) A` and `Sheaf (Opens.grothendieckTopology U) A`").

This section fills that TODO. The two cover-lifting (`IsCocontinuous`) facts are the substance:
a sieve covers in the Grothendieck-topology-over-`U` exactly when its image under the slice
forgetful functor covers in the ambient space, and that condition matches the pointwise covering
condition on the open subspace `↥U` because `Subtype.val : ↥U → X` is an injective open embedding.
From the two cocontinuities, `Equivalence.isDenseSubsite_inverse_of_isCocontinuous` produces the
dense-subsite hypothesis and `Equivalence.sheafCongr` produces the sheaf equivalence.

It is the foundational (purely topological / topos-theoretic) layer of the slice-to-geometric
transport; the remaining steps toward `overRestrictIso` (identifying the sliced structure sheaf
`O_X.over U` with the open subscheme's structure sheaf `U.toScheme.ringCatSheaf` under this
equivalence, then lifting to sheaves of modules via `pushforwardPushforwardEquivalence` and relating
to `Scheme.Modules.restrictFunctor U.ι`) are the geometric layer above it. -/

section OverSiteSheafEquivalence

open TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X] (U : Opens X)

/-- The functor of `Opens.overEquivalence U` is cocontinuous (cover-lifting) from the
`U`-slice of the ambient Grothendieck topology to the Grothendieck topology of the open
subspace `↥U`. Foundational layer of the gap1 slice-to-geometric bridge `overRestrictIso`;
fills the `Mathlib/Topology/Sheaves/Over.lean` TODO. Project-local. -/
instance overEquivalence_functor_isCocontinuous :
    (Opens.overEquivalence U).functor.IsCocontinuous
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U) where
  cover_lift := by
    intro Y S hS
    rw [GrothendieckTopology.mem_over_iff]
    intro x hx
    have hxU : x ∈ U := leOfHom Y.hom hx
    have hmem : (⟨x, hxU⟩ : ↥U) ∈ (Opens.overEquivalence U).functor.obj Y := hx
    obtain ⟨V, h, hSh, hxV⟩ := hS ⟨x, hxU⟩ hmem
    have hVle : (V : Set ↥U) ⊆ Subtype.val ⁻¹' (Y.left : Set X) := leOfHom h
    set W : Opens X := ⟨Subtype.val '' (V : Set ↥U),
      (U.isOpenEmbedding'.isOpen_iff_image_isOpen).1 V.isOpen⟩ with hWdef
    have hWle : W ≤ Y.left := by
      intro y hy; obtain ⟨z, hzV, rfl⟩ := hy; exact hVle hzV
    refine ⟨W, homOfLE hWle, ?_, ⟨⟨x, hxU⟩, hxV, rfl⟩⟩
    rw [Sieve.overEquiv_iff]
    change S ((Opens.overEquivalence U).functor.map (Over.homMk (homOfLE hWle)))
    have hdomle :
        (Opens.overEquivalence U).functor.obj (Over.mk ((homOfLE hWle) ≫ Y.hom)) ≤ V := by
      intro z hz
      obtain ⟨z', hz'V, hz'eq⟩ := (hz : (z : X) ∈ (W : Set X))
      exact (Subtype.val_injective hz'eq) ▸ hz'V
    convert S.downward_closed hSh (homOfLE hdomle) using 1
    all_goals apply Subsingleton.elim

/-- The inverse of `Opens.overEquivalence U` is cocontinuous (cover-lifting) from the
Grothendieck topology of the open subspace `↥U` to the `U`-slice of the ambient Grothendieck
topology. Foundational layer of the gap1 slice-to-geometric bridge `overRestrictIso`;
fills the `Mathlib/Topology/Sheaves/Over.lean` TODO. Project-local. -/
instance overEquivalence_inverse_isCocontinuous :
    (Opens.overEquivalence U).inverse.IsCocontinuous
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X).over U) where
  cover_lift := by
    intro W S hS
    rw [GrothendieckTopology.mem_over_iff] at hS
    intro y hy
    have hpy : (y : X) ∈ ((Opens.overEquivalence U).inverse.obj W).left := ⟨y, hy, rfl⟩
    obtain ⟨P, f, hSf0, hpP⟩ := hS (y : X) hpy
    rw [Sieve.overEquiv_iff] at hSf0
    have hPle : (P : Set X) ⊆ ((Opens.overEquivalence U).inverse.obj W).left := leOfHom f
    set V : Opens ↥U :=
      ⟨Subtype.val ⁻¹' (P : Set X), P.isOpen.preimage continuous_subtype_val⟩ with hVdef
    have hVle : V ≤ W := by
      intro z hz
      obtain ⟨z', hz'W, hz'eq⟩ := hPle (hz : (z : X) ∈ (P : Set X))
      exact (Subtype.val_injective hz'eq) ▸ hz'W
    refine ⟨V, homOfLE hVle, ?_, hpP⟩
    change S ((Opens.overEquivalence U).inverse.map (homOfLE hVle))
    have hdomle : ((Opens.overEquivalence U).inverse.obj V).left ≤ P := by
      intro p hp; obtain ⟨p', hp'V, rfl⟩ := hp; exact hp'V
    convert S.downward_closed hSf0 (Over.homMk (homOfLE hdomle) ?_) using 1
    all_goals apply Subsingleton.elim

/-- The dense-subsite witness for the inverse of `Opens.overEquivalence U`, assembled from the two
cover-lifting facts above. Project-local glue for `overEquivalence_sheafCongr`. -/
instance overEquivalence_inverse_isDenseSubsite :
    (Opens.overEquivalence U).inverse.IsDenseSubsite
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X).over U) :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ _

/-- The functor of `Opens.overEquivalence U` is continuous. Derived from the cocontinuity of the
inverse and the equivalence adjunction `inverse ⊣ functor`. Needed downstream of `overRestrictIso`
for `SheafOfModules.pushforwardPushforwardEquivalence`. Project-local. -/
instance overEquivalence_functor_isContinuous :
    (Opens.overEquivalence U).functor.IsContinuous
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U) := by
  haveI : (Opens.overEquivalence U).symm.functor.IsCocontinuous
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X).over U) :=
    inferInstanceAs ((Opens.overEquivalence U).inverse.IsCocontinuous _ _)
  exact (Opens.overEquivalence U).symm.toAdjunction.isContinuous_of_isCocontinuous _ _

/-- The inverse of `Opens.overEquivalence U` is continuous. Derived from the cocontinuity of the
functor and the equivalence adjunction `functor ⊣ inverse`. Needed downstream of `overRestrictIso`
for `SheafOfModules.pushforwardPushforwardEquivalence`. Project-local. -/
instance overEquivalence_inverse_isContinuous :
    (Opens.overEquivalence U).inverse.IsContinuous
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X).over U) :=
  (Opens.overEquivalence U).toAdjunction.isContinuous_of_isCocontinuous _ _

/-- **The over-site ↔ open-subspace sheaf equivalence.** For a topological space `X`, an open
`U ⊆ X`, and any category `A`, the equivalence of sites
`Opens.overEquivalence U : Over U ≌ Opens ↥U`
lifts to an equivalence of sheaf categories
`Sheaf ((Opens.grothendieckTopology X).over U) A ≌ Sheaf (Opens.grothendieckTopology ↥U) A`.

This is exactly the equivalence left as a TODO in `Mathlib/Topology/Sheaves/Over.lean`. It is the
foundational layer of the gap1 slice-to-geometric bridge (`lem:over_restrict_iso`,
`overRestrictIso`): once the sliced structure sheaf `O_X.over U` is identified with the structure
sheaf of the open subscheme `U.toScheme` under this equivalence, a presentation of `M.over U`
transports (via `pushforwardPushforwardEquivalence` + `restrictFunctorIsoPullback`) to a geometric
presentation of `M|_U`. Project-local: Mathlib supplies only the underlying site equivalence. -/
noncomputable def overEquivalence_sheafCongr (A : Type*) [Category A] :
    Sheaf ((Opens.grothendieckTopology X).over U) A ≌ Sheaf (Opens.grothendieckTopology ↥U) A :=
  (Opens.overEquivalence U).sheafCongr
    ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U) A

end OverSiteSheafEquivalence

/-! ## Project-local Mathlib supplement — the slice-to-geometric module bridge (gap1, C)

This section builds the geometric layer of the gap1 slice-to-geometric bridge
`lem:over_restrict_iso` on top of the topological `overEquivalence_sheafCongr` of the previous
section. It identifies, on the level of *sheaves of modules*, the abstract Grothendieck-slice
restriction `M.over U` (a sheaf of modules over the sliced structure sheaf `O_X.over U` on the slice
site `J.over U`) with the geometric restriction `(restrictFunctor U.ι).obj M` on the small Zariski
site of the open subscheme `U.toScheme`.

The key structural facts, all holding *definitionally* at the pinned commit, are:
* `(Opens.overEquivalence U).inverse ⋙ Over.forget U = U.ι.opensFunctor` (`rfl`): the inverse leg
  of the site equivalence, post-composed with the slice-forgetful functor, is the opens functor of
  the open immersion `U.ι`;
* consequently `U.toScheme.ringCatSheaf = (overEquivalence_sheafCongr U RingCat).functor.obj
  (X.ringCatSheaf.over U)` (`rfl`): the structure sheaf of the open subscheme is the transport of
  the sliced structure sheaf across the ring-valued sheaf equivalence (this is *step 2*, the
  geometric ring-sheaf identification, discharged by `rfl`).

From these, `SheafOfModules.pushforwardPushforwardEquivalence` lifts the site equivalence to an
equivalence of categories of sheaves of modules (`overRestrictEquiv`, *step 3*), under whose functor
the sliced module `M.over U` corresponds to the geometric restriction (`overRestrictIso`, *step 4*).

Mathlib (at the pinned commit) supplies only the underlying site equivalence and the
`pushforward`/`restrictFunctor` machinery; the assembly is project-local. -/

section OverRestrictBridge

open TopologicalSpace Topology

namespace Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens)

/-- **The slice-to-geometric equivalence of categories of sheaves of modules** (gap1, C, step 3).

For a scheme `X` and an open `U ⊆ X`, the category of sheaves of modules over the sliced structure
sheaf `O_X.over U` on the slice site `J.over U` is equivalent to the category `U.toScheme.Modules`
of sheaves of modules on the open subscheme `U.toScheme`. The equivalence is obtained by lifting the
topological site equivalence `Opens.overEquivalence U` (and its ring-valued sheaf congruence
`overEquivalence_sheafCongr`) to sheaves of modules via
`SheafOfModules.pushforwardPushforwardEquivalence`; the two ring-sheaf comparison morphisms it
consumes are the (co)unit of `Opens.overEquivalence U` whiskered into the structure presheaf, and
the identity (the geometric structure sheaf being *definitionally* the transport of the sliced one).

Project-local: it is the module-level layer of the gap1 bridge `lem:over_restrict_iso`; Mathlib
supplies only the underlying site equivalence. -/
noncomputable def overRestrictEquiv :
    SheafOfModules.{u} (X.ringCatSheaf.over U) ≌ U.toScheme.Modules :=
  letI eqv := Opens.overEquivalence U
  (SheafOfModules.pushforwardPushforwardEquivalence
      (J := (Opens.grothendieckTopology ↥X).over U) (K := Opens.grothendieckTopology ↥U) eqv
    (S := X.ringCatSheaf.over U) (R := U.toScheme.ringCatSheaf)
    (ObjectProperty.homMk
      (Functor.whiskerRight (NatTrans.op eqv.unitIso.inv) (X.ringCatSheaf.over U).obj))
    (ObjectProperty.homMk (𝟙 _))
    (by ext : 2
        simp only [Functor.whiskerLeft_app,
          Functor.whiskerRight_app, NatTrans.op_app, NatTrans.id_app,
          ObjectProperty.homMk_hom, NatTrans.comp_app]
        exact congrArg (Sheaf.over X.ringCatSheaf U).obj.map
          (congrArg Quiver.Hom.op (Equivalence.unitInv_app_inverse eqv _).symm))
    (by ext : 2
        simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app,
          NatTrans.op_app, ObjectProperty.homMk_hom, NatTrans.comp_app, NatTrans.id_app]
        erw [Category.id_comp, ← Functor.map_comp]
        rename_i x
        have h : (eqv.unitIso.inv.app (Opposite.unop x)).op ≫ (eqv.unit.app (Opposite.unop x)).op
            = 𝟙 _ := by
          rw [← op_comp]
          simp only [CategoryTheory.Equivalence.unit, Iso.hom_inv_id_app, op_id]
        exact (congrArg (Sheaf.over X.ringCatSheaf U).obj.map h).trans
          (CategoryTheory.Functor.map_id _ _))).symm

/-- **Step-4 functor identification of the gap1 bridge.** The composite of `SheafOfModules.over · U`
with the slice-to-geometric equivalence `overRestrictEquiv U` is the geometric restriction functor
`restrictFunctor U.ι` along the open immersion `U.ι`. Both are pushforwards along the immersion's
opens functor (`(Opens.overEquivalence U).inverse ⋙ Over.forget U = U.ι.opensFunctor`, `rfl`); the
two ring-sheaf comparison morphisms agree, so the identification is `pushforwardComp` followed by
`pushforwardCongr`. Project-local. -/
noncomputable def overRestrictFunctorIso :
    (SheafOfModules.pushforward (S := X.ringCatSheaf.over U) (𝟙 _)) ⋙
        (overRestrictEquiv U).functor ≅ restrictFunctor U.ι :=
  haveI : ((Opens.overEquivalence U).inverse ⋙ Over.forget U).IsContinuous
      (Opens.grothendieckTopology ↥U) (Opens.grothendieckTopology ↥X) :=
    Functor.isContinuous_comp (Opens.overEquivalence U).inverse (Over.forget U)
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology ↥X).over U)
      (Opens.grothendieckTopology ↥X)
  SheafOfModules.pushforwardComp _ _ ≪≫ SheafOfModules.pushforwardCongr (by cat_disch)

/-- **The slice-to-geometric isomorphism on an object** (gap1, C, step 4): for a sheaf of modules
`M` on `X`, the transport of the abstract Grothendieck-slice restriction `M.over U` under the
slice-to-geometric equivalence `overRestrictEquiv U` is canonically isomorphic to the geometric
restriction `(restrictFunctor U.ι).obj M`. This is the object-level form of
`overRestrictFunctorIso`; composed with `restrictFunctorIsoPullback` it lands the geometric
restriction as the pullback `U.ι^* M`. Project-local: the load-bearing slice-touching ingredient of
the gap1 transport `lem:over_restrict_iso`. -/
noncomputable def overRestrictIso (M : X.Modules) :
    (overRestrictEquiv U).functor.obj (M.over U) ≅ (restrictFunctor U.ι).obj M :=
  (overRestrictFunctorIso U).app M

/-- **The slice-to-geometric isomorphism in pullback form** (gap1, C, step 4'): the transport of the
abstract Grothendieck-slice restriction `M.over U` under `overRestrictEquiv U` is canonically
isomorphic to the inverse-image (pullback) `U.ι^* M` of `M` along the open immersion `U.ι`. This is
`overRestrictIso` composed with Mathlib's `restrictFunctorIsoPullback`; it is the form a
presentation of `M.over U` transports into a presentation of the geometric pullback `U.ι^* M`.
Project-local. -/
noncomputable def overRestrictPullbackIso (M : X.Modules) :
    (overRestrictEquiv U).functor.obj (M.over U) ≅ (Scheme.Modules.pullback U.ι).obj M :=
  overRestrictIso U M ≪≫ (restrictFunctorIsoPullback U.ι).app M

end Scheme.Modules

end OverRestrictBridge

/-! ## Project-local Mathlib supplement — slice-to-geometric presentation transport (gap1, P1)

This section builds the geometric milestone of the gap1 per-element transport
`lem:isIso_fromTildeΓ_basicOpen_of_quasicoherent` (P1): a `SheafOfModules.Presentation` of the
abstract Grothendieck-slice restriction `M.over U` is transported, across the slice-to-geometric
bridge `overRestrictPullbackIso` (gap1, C), into a `SheafOfModules.Presentation` of the *geometric*
restriction `(Scheme.Modules.pullback U.ι).obj M = U.ι^* M` on the open subscheme `U.toScheme`.

The load-bearing ingredient is the unit-iso `overRestrictUnitIso`: the slice-to-geometric
equivalence functor `(overRestrictEquiv U).functor` (definitionally a `SheafOfModules.pushforward`
along the equivalence-of-sites inverse with the *identity* ring comparison) sends the
structure-sheaf module `unit` to `unit`. This is exactly the `F.obj (unit R) ≅ unit S` datum that
`SheafOfModules.Presentation.map` consumes; once it is in hand, `Presentation.map` +
`Presentation.ofIsIso` (across `overRestrictPullbackIso`) realise the transport. The unit-iso rests
on the general fact `isIso_unitToPushforwardObjUnit_of_isIso'`: the canonical map
`unit S ⟶ (pushforward ψ).obj (unit R)` is an iso whenever the ring-sheaf comparison `ψ` is
(here `ψ = 𝟙`).

Mathlib (at the pinned commit) supplies `SheafOfModules.unitToPushforwardObjUnit` and proves it iso
only under a finality hypothesis on the site functor (`PullbackFree.lean`); the
`IsIso ψ ⟹ IsIso (unitToPushforwardObjUnit ψ)` route used here, and the slice transport, are
project-local. -/

section SliceGeometricPresentation

open CategoryTheory Limits TopologicalSpace Topology

/-- **`unitToPushforwardObjUnit` is an isomorphism when the ring-sheaf comparison is.**

For a continuous functor `F` of sites and a morphism of ring sheaves
`ψ : S ⟶ (F.sheafPushforwardContinuous …).obj R` that is an isomorphism, the canonical map
`unitToPushforwardObjUnit ψ : unit S ⟶ (pushforward ψ).obj (unit R)` is an isomorphism. Its
component on each object is `(forget₂ RingCat AddCommGrpCat).map (ψ.hom.app _)`, iso as `ψ` is;
the conclusion follows by the reflect-isomorphism functors `SheafOfModules.toSheaf` and
`sheafToPresheaf` together with `NatTrans.isIso_iff_isIso_app`.

Project-local: Mathlib proves `unitToPushforwardObjUnit` iso only under a finality hypothesis on `F`
(`SheafOfModules.PullbackFree`); this `IsIso ψ`-driven form is the one the slice-to-geometric
unit-iso `overRestrictUnitIso` (gap1, P1) consumes (with `ψ = 𝟙`). -/
private theorem isIso_unitToPushforwardObjUnit_of_isIso' {C : Type u} [Category.{u} C]
    {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {Fu : C ⥤ D}
    {S : Sheaf J RingCat.{u}} {Rr : Sheaf K RingCat.{u}} [Fu.IsContinuous J K]
    (ψ : S ⟶ (Fu.sheafPushforwardContinuous RingCat.{u} J K).obj Rr)
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    (hψ : IsIso ψ) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit ψ) := by
  haveI := hψ
  haveI hmap : IsIso ((sheafToPresheaf J RingCat).map ψ) := inferInstance
  rw [NatTrans.isIso_iff_isIso_app] at hmap
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  haveI hiso : IsIso (ψ.hom.app V) := hmap V
  haveI : IsIso ((forget₂ RingCat AddCommGrpCat).map (ψ.hom.app V)) := inferInstance
  exact this

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- **The slice-to-geometric equivalence functor sends `unit` to `unit`** (gap1, P1).

For an open `U ⊆ X`, the functor of the slice-to-geometric equivalence `overRestrictEquiv U`
(definitionally `SheafOfModules.pushforward` along `(Opens.overEquivalence U).inverse` with the
identity ring comparison) carries the sliced structure-sheaf module `unit (O_X.over U)` to the
structure-sheaf module `unit (U.toScheme.ringCatSheaf)` of the open subscheme. This is the
`F.obj (unit R) ≅ unit S` datum consumed by `SheafOfModules.Presentation.map` in
`overRestrictPresentation`. Project-local. -/
noncomputable def overRestrictUnitIso (U : X.Opens) :
    (overRestrictEquiv U).functor.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf := by
  unfold overRestrictEquiv
  try dsimp only [Equivalence.symm_functor]
  refine (@asIso _ _ _ _ (SheafOfModules.unitToPushforwardObjUnit
      (F := (Opens.overEquivalence U).inverse) (J := Opens.grothendieckTopology ↥U)
      (S := U.toScheme.ringCatSheaf) (R := X.ringCatSheaf.over U)
      (ObjectProperty.homMk (𝟙 _)))
    (isIso_unitToPushforwardObjUnit_of_isIso' _ ?hpsi)).symm
  exact inferInstanceAs (IsIso (𝟙 U.toScheme.ringCatSheaf))

/-- **Slice presentation ⟹ geometric-restriction presentation** (gap1, P1).

Given a sheaf of modules `M` on `X`, an open `U ⊆ X`, and a `SheafOfModules.Presentation` of the
abstract Grothendieck-slice restriction `M.over U`, there is a `SheafOfModules.Presentation` of the
*geometric* restriction `(pullback U.ι).obj M = U.ι^* M` on the open subscheme `U.toScheme`. The
transport is `Presentation.map` along the slice-to-geometric equivalence functor (using the unit-iso
`overRestrictUnitIso`) followed by `Presentation.ofIsIso` across the bridge
`overRestrictPullbackIso` (gap1, C).

This closes the slice-touching step of the gap1 per-element transport
`lem:isIso_fromTildeΓ_basicOpen_of_quasicoherent` (P1): with `U = q.X i` and
`P = q.presentation i` it produces a global presentation of `U.ι^* M`; the remaining geometric step
restricts further to a basic affine `D(r) ≅ Spec R_r` and concludes via
`isIso_fromTildeΓ_of_presentation`. Project-local. -/
noncomputable def overRestrictPresentation (U : X.Opens) (M : X.Modules)
    (P : (M.over U).Presentation) : ((Scheme.Modules.pullback U.ι).obj M).Presentation :=
  SheafOfModules.Presentation.ofIsIso.{u} (overRestrictPullbackIso U M).hom
    (SheafOfModules.Presentation.map.{u} P (overRestrictEquiv U).functor (overRestrictUnitIso U))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- Reconstructing a global presentation expands the cover colimit and sheafification instances.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Geometric restriction to a cover member is globally presented** (gap1, P1).

For a sheaf of modules `M` on `X` with quasi-coherence data `q` and an index `i`, the geometric
restriction `(pullback (q.X i).ι).obj M = (q.X i).ι^* M` of `M` to the open subscheme
`(q.X i).toScheme` admits a `SheafOfModules.Presentation`. It is `overRestrictPresentation` applied
to the slice presentation `q.presentation i : (M.over (q.X i)).Presentation` supplied by the
quasi-coherence datum.

This is the per-cover-member output that feeds the affine descent of the gap1 transport
`lem:isIso_fromTildeΓ_basicOpen_of_quasicoherent` (P1): for `D(r) ≤ q.X i` one further
restricts this
presentation to the basic affine `D(r) ≅ Spec R_r` and concludes via
`isIso_fromTildeΓ_of_presentation`. The heartbeat headroom tames the slice-site
`IsRightAdjoint`/`HasSheafify` synthesis blow-up that `Presentation.map` triggers across the
equivalence functor (the same `backward.isDefEq.respectTransparency false` incantation Mathlib's own
`QuasicoherentData.bind` uses). Project-local. -/
noncomputable def presentationPullbackιOfQuasicoherentData (M : X.Modules)
    (q : M.QuasicoherentData) (i : q.I) :
    ((Scheme.Modules.pullback (Scheme.Opens.ι (q.X i))).obj M).Presentation :=
  overRestrictPresentation (q.X i) M (q.presentation i)

end Scheme.Modules

end SliceGeometricPresentation

/-! ## Project-local Mathlib supplement — basic-open presentation descent (gap1, P1 keystone)

This section assembles the gap1 per-element keystone
`lem:isIso_fromTildeΓ_basicOpen_of_quasicoherent`
(`isIso_fromTildeΓ_restrict_basicOpen`): on a basic open `D(r)` contained in a cover member
`q.X i` of the quasi-coherence data, the restricted sheaf `M|_{D(r)}` is a geometric tilde, i.e.
its `fromTildeΓ` counit is an isomorphism.

The route follows the affine descent of the recipe, building on the slice-to-geometric presentation
transport of the previous section:

1. `presentationPullbackιOfQuasicoherentData M q i` is a *global* `Presentation` of the geometric
   restriction `N := (q.X i).ι^* M` on the open subscheme `Z := (q.X i).toScheme`.
2. For any open `W ⊆ Z`, the global presentation `PN` slices to a slice presentation `N.over W` via
   the single `Presentation.map` of the over-functor `pushforward (𝟙 …)` (the
   `QuasicoherentData.ofPresentation` template — no iterated-slice equivalence is needed because
   `PN` is already a global presentation on the genuine scheme `Z`).
3. `overRestrictPresentation W N PNW` transports it to a global presentation of the geometric
   restriction `(pullback W.ι).obj N` on the open subscheme `W.toScheme`.
4. For `W` *affine*, `IsAffineOpen.isoSpec` identifies `W.toScheme ≅ Spec Γ(Z, W)`; transporting the
   presentation across this iso (whose `Opens.map` is `Final`, so `pullbackObjUnitToUnit` is an iso)
   lands a global presentation on the genuine affine `Spec Γ(Z, W)`.
5. A global presentation forces `fromTildeΓ` to be an isomorphism
   (`isIso_fromTildeΓ_of_presentation`).

Mathlib (at the pinned commit) carries no `QCoh(Spec R) ≃ Mod R` essential-image bridge;
this descent
is project-local. -/

section BasicOpenPresentationDescent

open CategoryTheory Limits TopologicalSpace Topology

namespace Scheme.Modules

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- Transporting a presentation through the slice/open equivalence unfolds both sites.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Presentation of the geometric restriction of `M` to an open `W` of a cover member**
(gap1, P1).

For a sheaf of modules `M` on `X` with quasi-coherence data `q`, an index `i`, and *any* open
`W ⊆ (q.X i).toScheme` of the cover-member subscheme, the geometric restriction
`(pullback W.ι).obj ((pullback (q.X i).ι).obj M)` of `M` (pulled back to `Z := (q.X i).toScheme`,
then to `W`) admits a `SheafOfModules.Presentation` on the open subscheme `W.toScheme`.

It slices the *global* presentation `presentationPullbackιOfQuasicoherentData M q i` of
`N := (q.X i).ι^* M` on `Z` down to the slice `N.over W` (a single `Presentation.map` of the
over-functor — the `QuasicoherentData.ofPresentation` template, no iterated-slice equivalence
needed since `PN` is global on the genuine scheme `Z`), then geometrizes via
`overRestrictPresentation`. Project-local: feeds the affine descent of the gap1 keystone
`isIso_fromTildeΓ_restrict_basicOpen`. -/
noncomputable def presentationPullbackιRestrict (M : X.Modules)
    (q : M.QuasicoherentData) (i : q.I) (W : (show X.Opens from q.X i).toScheme.Opens) :
    ((Scheme.Modules.pullback (Scheme.Opens.ι W)).obj
      ((Scheme.Modules.pullback (Scheme.Opens.ι (q.X i))).obj M)).Presentation :=
  overRestrictPresentation W ((Scheme.Modules.pullback (Scheme.Opens.ι (q.X i))).obj M)
    (SheafOfModules.Presentation.map.{u}
      (presentationPullbackιOfQuasicoherentData M q i)
      (SheafOfModules.pushforward
        (𝟙 ((show X.Opens from q.X i).toScheme.ringCatSheaf.over W))) (by rfl))

/-- **The opens functor of an iso of schemes is an equivalence of opens sites.** For `φ : Y ≅ Z`,
the inverse-image functor `Opens.map φ.inv.base : Opens ↥Y ⥤ Opens ↥Z` is an equivalence (with
inverse `Opens.map φ.hom.base`), assembled from the pseudofunctoriality isos `Opens.mapComp` /
`Opens.mapId`. Its purpose is to supply the `Final` instance that makes `pullbackObjUnitToUnit` an
isomorphism in `pullbackSchemeIsoUnitIso`. Project-local. -/
noncomputable def opensMapEquivOfIso {Y Z : Scheme.{u}} (φ : Y ≅ Z) :
    TopologicalSpace.Opens ↥Y ≌ TopologicalSpace.Opens ↥Z where
  functor := Opens.map φ.inv.base
  inverse := Opens.map φ.hom.base
  unitIso := (Opens.mapId _).symm ≪≫
      Opens.mapIso (𝟙 _) (φ.hom.base ≫ φ.inv.base)
        (show (𝟙 _) = φ.hom.base ≫ φ.inv.base by
          rw [← AlgebraicGeometry.Scheme.Hom.comp_base, φ.hom_inv_id]; rfl) ≪≫
      Opens.mapComp φ.hom.base φ.inv.base
  counitIso := (Opens.mapComp φ.inv.base φ.hom.base).symm ≪≫
      Opens.mapIso (φ.inv.base ≫ φ.hom.base) (𝟙 _)
        (show φ.inv.base ≫ φ.hom.base = 𝟙 _ by
          rw [← AlgebraicGeometry.Scheme.Hom.comp_base, φ.inv_hom_id]; rfl) ≪≫
      Opens.mapId _

/-- **The opens functor of an iso of schemes is final.** Immediate from
`opensMapEquivOfIso` (an equivalence is final); the `Final` fact needed by
`pullbackObjUnitToUnit`. Supplied via `haveI` at use sites (instance resolution cannot invert
`φ.inv.base`). Project-local. -/
theorem opensMap_final_of_schemeIso {Y Z : Scheme.{u}} (φ : Y ≅ Z) :
    (Opens.map φ.inv.base).Final := by
  haveI : (Opens.map φ.inv.base).IsEquivalence := (opensMapEquivOfIso φ).isEquivalence_functor
  infer_instance

/-- **Pullback along an iso of schemes sends the unit module to the unit module** (gap1, P1).

For an isomorphism of schemes `φ : Y ≅ Z`, the pullback functor along `φ.inv : Z ⟶ Y` carries the
structure-sheaf (unit) module of `Y` to that of `Z`. The underlying canonical comparison
`pullbackObjUnitToUnit` is an isomorphism because the site functor `Opens.map φ.inv.base` of an iso
of schemes is `Final` (`opensMap_final_of_schemeIso`). This is the `F.obj (unit R) ≅ unit S` datum
consumed by `Presentation.map` along `pullback φ.inv` in `presentationPullbackOfSchemeIso`.
Project-local. -/
noncomputable def pullbackSchemeIsoUnitIso {Y Z : Scheme.{u}} (φ : Y ≅ Z) :
    (SheafOfModules.pullback (φ.inv.toRingCatSheafHom)).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit Z.ringCatSheaf := by
  haveI : (Opens.map φ.inv.base).Final := opensMap_final_of_schemeIso φ
  haveI : (SheafOfModules.pushforward (φ.inv.toRingCatSheafHom)).IsRightAdjoint := inferInstance
  exact asIso (SheafOfModules.pullbackObjUnitToUnit (φ.inv.toRingCatSheafHom))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- Mapping the presentation through pullback requires the colimit-preservation instance chain.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **A presentation transports across the pullback by an iso of schemes** (gap1, P1, step 4).

Given an isomorphism of schemes `φ : Y ≅ Z` and a `SheafOfModules.Presentation` of a module `N` on
`Y`, the geometric pullback `(pullback φ.inv).obj N` of `N` to `Z` admits a presentation. It is
`Presentation.map` along the colimit-preserving pullback functor `pullback φ.inv`, using
the unit-iso
`pullbackSchemeIsoUnitIso φ`. This is the affine-identification transport step of the gap1 keystone:
applied with `φ` the `IsAffineOpen.isoSpec` of the affine restriction, it moves the
presentation onto
a genuine `Spec`. Project-local. -/
noncomputable def presentationPullbackOfSchemeIso {Y Z : Scheme.{u}} (φ : Y ≅ Z)
    (N : Y.Modules) (P : N.Presentation) :
    ((Scheme.Modules.pullback φ.inv).obj N).Presentation :=
  haveI : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} (Scheme.Modules.pullback φ.inv) :=
    (Scheme.Modules.pullbackPushforwardAdjunction φ.inv).leftAdjoint_preservesColimits
  SheafOfModules.Presentation.map.{u} P (Scheme.Modules.pullback φ.inv)
    (pullbackSchemeIsoUnitIso φ).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- The affine counit comparison unfolds the transported presentation and tilde equivalence.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Quasi-coherent restricts to a tilde on every affine open of a cover member** (gap1, P1).

For a sheaf of modules `M` on `X` with quasi-coherence data `q`, an index `i`, and an *affine* open
`W ⊆ (q.X i).toScheme` of the cover-member subscheme, the geometric restriction of `M` to the affine
`Spec Γ((q.X i).toScheme, W) ≅ W` (pulled back to `Z := (q.X i).toScheme`, then to `W`, then across
the affine identification `IsAffineOpen.isoSpec`) has an isomorphism `fromTildeΓ` counit;
that is, it is
a geometric tilde.

This is the geometric heart of the gap1 per-element transport: the slice presentation supplied by
the quasi-coherence datum geometrizes (`presentationPullbackιRestrict`) to a global presentation on
`W.toScheme`, which transports across the affine iso (`presentationPullbackOfSchemeIso`) to a global
presentation on the genuine affine `Spec Γ(Z, W)`; a global presentation forces
`fromTildeΓ` to be an
isomorphism (`isIso_fromTildeΓ_of_presentation`). Project-local: Mathlib has no
`QCoh(Spec R) ≃ Mod R` essential-image bridge. -/
theorem isIso_fromTildeΓ_presentationPullback (M : X.Modules)
    (q : M.QuasicoherentData) (i : q.I)
    (W : (show X.Opens from q.X i).toScheme.Opens) (hW : IsAffineOpen W) :
    IsIso ((Scheme.Modules.pullback hW.isoSpec.inv).obj
      ((Scheme.Modules.pullback (Scheme.Opens.ι W)).obj
        ((Scheme.Modules.pullback (Scheme.Opens.ι (q.X i))).obj M))).fromTildeΓ :=
  isIso_fromTildeΓ_of_presentation _
    (presentationPullbackOfSchemeIso hW.isoSpec
      ((Scheme.Modules.pullback (Scheme.Opens.ι W)).obj
        ((Scheme.Modules.pullback (Scheme.Opens.ι (q.X i))).obj M))
      (presentationPullbackιRestrict M q i W))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- Specializing the counit comparison to a basic open triggers the slice-site instance search.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Quasi-coherent restricts to a tilde on each basic open of the cover** (gap1, P1 keystone,
`lem:isIso_fromTildeΓ_basicOpen_of_quasicoherent`).

Let `M` be a sheaf of modules on `Spec R` with quasi-coherence data `q`, and let `r : R` with
`D(r) ≤ q.X i` for some cover member. Then the geometric restriction of `M` to the affine basic open
`D(r)` — realised as the preimage `W := (q.X i).ι ⁻¹ᵁ D(r)` inside the cover-member subscheme
`Z := (q.X i).toScheme`, transported across the affine identification `W ≅ Spec Γ(Z, W)` (which is
`Spec R_r` since `D(r)` is affine) — has an isomorphism `fromTildeΓ` counit, i.e. `M|_{D(r)}` is a
geometric tilde.

This is the per-element step of gap1: it is the affine instance `W = (q.X i).ι ⁻¹ᵁ D(r)` of
`isIso_fromTildeΓ_presentationPullback`, with affineness of `W` from
`IsAffineOpen.Spec_basicOpen` (`D(r)` is affine in `Spec R`) and
`IsAffineOpen.preimage_of_isOpenImmersion` (its preimage under the open immersion `(q.X i).ι` is
affine, using `D(r) ≤ q.X i = (q.X i).ι.opensRange`). Project-local. -/
theorem isIso_fromTildeΓ_restrict_basicOpen {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) (r : R) (i : q.I)
    (hr : (PrimeSpectrum.basicOpen r : (Spec R).Opens) ≤ q.X i) :
    IsIso (@Scheme.Modules.fromTildeΓ
      (Γ(↑(q.X i), (Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen r)))
      ((Scheme.Modules.pullback
          (((IsAffineOpen.Spec_basicOpen r).preimage_of_isOpenImmersion (Scheme.Opens.ι (q.X i))
            (by rw [Scheme.Opens.opensRange_ι]; exact hr)).isoSpec.inv)).obj
        ((Scheme.Modules.pullback (Scheme.Opens.ι
            ((Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen r)))).obj
          ((Scheme.Modules.pullback (Scheme.Opens.ι (q.X i))).obj M)))) :=
  isIso_fromTildeΓ_presentationPullback M q i
    ((Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen r))
    ((IsAffineOpen.Spec_basicOpen r).preimage_of_isOpenImmersion (Scheme.Opens.ι (q.X i))
      (by rw [Scheme.Opens.opensRange_ι]; exact hr))

/-! ## Project-local Mathlib supplement — gap1-D: the section-localization descent

The keystone `isLocalizedModule_basicOpen_descent` reduces (Hartshorne II.5.3 / Stacks
`lemma-invert-f-sections`) to a finite-cover sheaf-gluing argument.  The single geometric input
is the **per-cover-element** fact that on each `D(r)` of a finite cover `{D(r_j)}` of `Spec R`
(with `D(r_j) ≤ q.X i`), the basic-open restriction `Γ(M, D(r)) → Γ(M, D(f) ⊓ D(r))` is a
localization at `powers f` — this is exactly the P1 local-tilde data transported to sections, and
is the gated hypothesis `Hfr` below.  Given `Hfr` (for every `r` whose `D(r)` sits inside a cover
member, hence also for the overlaps `D(r r')`), the descent is pure sheaf theory: separatedness
gives the `exists_of_eq` field, gluing the patched compatible family gives `surj'`, and the global
`map_units` field holds for arbitrary `M` (`map_units_restrict_basicOpen`). -/

/-- A finite family `t` spanning `R` gives a basic-open cover of `Spec R`: the supremum of the
`D(r)` over `r ∈ t` is `⊤`.  Project-local glue feeding the sheaf-gluing reduction of the
section-localization descent. -/
private lemma iSup_basicOpen_subtype_eq_top {R : CommRingCat.{u}} {t : Finset R}
    (hspan : Ideal.span (t : Set R) = ⊤) :
    (⨆ r : {x // x ∈ t}, (PrimeSpectrum.basicOpen (r : R) : (Spec R).Opens)) = ⊤ := by
  rw [iSup_subtype]
  have h := (PrimeSpectrum.iSup_basicOpen_eq_top_iff' (s := (t : Set R))).mpr hspan
  simpa using h

/-- Restriction maps of `modulesSpecToSheaf.obj M` compose: restricting `A → B → C` equals the
direct restriction `A → C`.  Poset-hom uniqueness makes the two intermediate morphisms compose to
the direct one.  Project-local bookkeeping for the section-localization descent. -/
private lemma res_comp {R : CommRingCat.{u}}
    (F : TopCat.Sheaf (ModuleCat.{u} ↑R) ↑(Spec R).toPresheafedSpace)
    {A B C : (Spec R).Opens} (hBA : B ≤ A) (hCB : C ≤ B) (hCA : C ≤ A)
    (y : ToType (F.presheaf.obj (.op A))) :
    (F.presheaf.map (homOfLE hCB).op).hom ((F.presheaf.map (homOfLE hBA).op).hom y)
      = (F.presheaf.map (homOfLE hCA).op).hom y := by
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← op_comp]; rfl

/-- **Separatedness/torsion field of the section-localization descent.**  Given the
per-cover-element localization data `Hfr` (on each `D(r)` of a finite basic-open cover `{D(r)}` of
`Spec R`, the restriction `Γ(M, D(r)) → Γ(M, D(f) ⊓ D(r))` is a localization at `powers f`), any
global section `x` that restricts to `0` on `D(f)` is killed by a power of `f`.  This is the
`exists_of_eq` engine of `isLocalizedModule_basicOpen_descent`: per cover element a power of `f`
kills `x|_{D(r)}` (`IsLocalizedModule.exists_of_eq` of `Hfr`), the finite sup of these powers kills
every `x|_{D(r)}`, and sheaf separatedness over the cover (`TopCat.Sheaf.eq_of_locally_eq'`) lifts
this to `f^n • x = 0`.  Project-local: the geometric content (`Hfr`) is the gated P1 tilde data. -/
private lemma descent_smul_eq_zero {R : CommRingCat.{u}} (M : (Spec R).Modules) (f : R)
    (t : Finset R) (hspan : Ideal.span (t : Set R) = ⊤)
    (Hfr : ∀ r ∈ t, IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_right :
          PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r
            ≤ PrimeSpectrum.basicOpen r)).op).hom)
    (x : ToType ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)))
    (hx : ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom x = 0) :
    ∃ n : ℕ, f ^ n • x = 0 := by
  classical
  have key : ∀ r : {x // x ∈ t}, ∃ k : ℕ, f ^ k •
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen (r:R) ≤ ⊤)).op).hom x = 0 := by
    rintro ⟨r, hr⟩
    have e1 := res_comp (modulesSpecToSheaf.obj M)
        (A := ⊤) (B := PrimeSpectrum.basicOpen r)
        (C := PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r) le_top inf_le_right le_top x
    have e2 := res_comp (modulesSpecToSheaf.obj M)
        (A := ⊤) (B := PrimeSpectrum.basicOpen f)
        (C := PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r) le_top inf_le_left le_top x
    have hzero := e1.trans (e2.symm.trans
      ((congrArg (((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_left :
            PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r
              ≤ PrimeSpectrum.basicOpen f)).op).hom) hx).trans
        (map_zero _)))
    obtain ⟨c, hc⟩ := (Hfr r hr).exists_of_eq (hzero.trans (map_zero _).symm)
    obtain ⟨k, hk⟩ := c.2
    have hk' : f ^ k = (c : R) := hk
    refine ⟨k, ?_⟩
    have h2 : c • (((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (le_top : PrimeSpectrum.basicOpen (r:R) ≤ ⊤)).op).hom x) = 0 :=
      hc.trans (smul_zero c)
    rw [hk']; exact h2
  choose k hk using key
  refine ⟨Finset.univ.sup k, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (modulesSpecToSheaf.obj M)
    (fun r : {x // x ∈ t} => (PrimeSpectrum.basicOpen (r:R) : (Spec R).Opens)) ⊤
    (fun r => homOfLE le_top) (le_of_eq (iSup_basicOpen_subtype_eq_top hspan).symm)
    (f ^ Finset.univ.sup k • x) 0 ?_
  intro r
  have hle : k r ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ r)
  set g := ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen (r:R) ≤ ⊤)).op).hom with hg
  have hms : g (f ^ Finset.univ.sup k • x) = f ^ Finset.univ.sup k • g x := LinearMap.map_smul g _ x
  have hsplit : f ^ Finset.univ.sup k • g x
      = f ^ (Finset.univ.sup k - k r) • (f ^ (k r) • g x) := by
    rw [← mul_smul, ← pow_add, Nat.sub_add_cancel hle]
  have hzero : g (f ^ Finset.univ.sup k • x) = 0 :=
    hms.trans (hsplit.trans ((congrArg (fun y => f ^ (Finset.univ.sup k - k r) • y) (hk r)).trans
      (smul_zero _)))
  change g (f ^ Finset.univ.sup k • x) = g 0
  rw [hzero, map_zero]

/-- **Overlap agreement for the surjectivity field.**  If a section `br` on `D(r)` satisfies the
normalized identity `ρ[D(r), D(f) ⊓ D(r)] br = f^N • (y|_{D(f) ⊓ D(r)})`, then for any open
`U ≤ D(r)` its restriction to `U`, pushed down to `D(f) ⊓ U`, equals `f^N • (y|_{D(f) ⊓ U})`.
Specializing `U` to an overlap `D(r) ⊓ D(r')` shows the normalized sections of two cover members
agree there after restriction to `D(f) ⊓ (D(r) ⊓ D(r'))`, which (via the per-overlap localization)
makes a common `f`-power glue them.  Project-local bookkeeping for `descent_surj`. -/
private lemma descent_overlap_agree {R : CommRingCat.{u}} (M : (Spec R).Modules) (f : R) (r : R)
    (N : ℕ) (U : (Spec R).Opens) (hUr : U ≤ PrimeSpectrum.basicOpen r)
    (y : ToType ((modulesSpecToSheaf.obj M).presheaf.obj (.op (PrimeSpectrum.basicOpen f))))
    (br : ToType ((modulesSpecToSheaf.obj M).presheaf.obj (.op (PrimeSpectrum.basicOpen r))))
    (hbr : ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r
            ≤ PrimeSpectrum.basicOpen r)).op).hom br
        = f ^ N • (((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r
            ≤ PrimeSpectrum.basicOpen f)).op).hom y)) :
    ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ U ≤ U)).op).hom
      (((modulesSpecToSheaf.obj M).presheaf.map (homOfLE hUr).op).hom br)
    = f ^ N • (((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ U
          ≤ PrimeSpectrum.basicOpen f)).op).hom y) := by
  have hCB : PrimeSpectrum.basicOpen f ⊓ U
      ≤ PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r := inf_le_inf_left _ hUr
  have e1 := res_comp (modulesSpecToSheaf.obj M)
      (A := PrimeSpectrum.basicOpen r) (B := U) (C := PrimeSpectrum.basicOpen f ⊓ U)
      hUr inf_le_right (inf_le_right.trans hUr) br
  have e2 := res_comp (modulesSpecToSheaf.obj M) (A := PrimeSpectrum.basicOpen r)
      (B := PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r)
      (C := PrimeSpectrum.basicOpen f ⊓ U) inf_le_right hCB (inf_le_right.trans hUr) br
  have e3 := res_comp (modulesSpecToSheaf.obj M) (A := PrimeSpectrum.basicOpen f)
      (B := PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r)
      (C := PrimeSpectrum.basicOpen f ⊓ U) inf_le_left hCB inf_le_left y
  have hms := LinearMap.map_smul ((modulesSpecToSheaf.obj M).presheaf.map (homOfLE hCB).op).hom
      (f ^ N) (((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r
          ≤ PrimeSpectrum.basicOpen f)).op).hom y)
  exact e1.trans (e2.symm.trans ((congrArg _ hbr).trans (hms.trans (congrArg (f ^ N • ·) e3))))

/-- **Surjectivity field of the section-localization descent.**  With the per-cover-element (and
per-overlap) localization data `Hfr`, every section `y` over `D(f)` becomes, after multiplying by a
power of `f`, the restriction of a global section.  The classical Hartshorne II.5.3 argument: each
`D(r)` of a finite basic-open cover `{D(r)}` of `Spec R`, `y|_{D(f) ⊓ D(r)}` is `f^{-N}` times the
restriction of a section `b_r` on `D(r)` (`IsLocalizedModule.surj` of `Hfr` at `D(r)`, with a common
power `N`); on overlaps the `b_r` agree after a further power `f^P` (`descent_overlap_agree` +
`IsLocalizedModule.exists_of_eq` of `Hfr` at `D(r) ⊓ D(r')`), so `f^P • b_r` glue
(`TopCat.Sheaf.existsUnique_gluing'`) to a global `x` with `x|_{D(f)} = f^{N+P} • y` (by sheaf
separatedness over the cover `{D(f) ⊓ D(r)}` of `D(f)`).  Project-local: `Hfr` is the gated P1
local-tilde data. -/
private lemma descent_surj {R : CommRingCat.{u}} (M : (Spec R).Modules) (f : R)
    (t : Finset R) (hspan : Ideal.span (t : Set R) = ⊤)
    (Hfr : ∀ U : (Spec R).Opens, (∃ s : R, U = PrimeSpectrum.basicOpen s) →
      (∃ r ∈ t, U ≤ PrimeSpectrum.basicOpen r) →
      IsLocalizedModule (Submonoid.powers f)
        ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ U ≤ U)).op).hom)
    (y : ToType ((modulesSpecToSheaf.obj M).presheaf.obj (.op (PrimeSpectrum.basicOpen f)))) :
    ∃ (x : ToType ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤))) (n : ℕ),
      f ^ n • y = ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom x := by
  classical
  -- Stage 1: per cover element a section `a r` and a power `m r`.
  have perr : ∀ r : {x // x ∈ t}, ∃ (a : ToType ((modulesSpecToSheaf.obj M).presheaf.obj
        (.op (PrimeSpectrum.basicOpen (r:R))))) (m : ℕ),
        f ^ m • (((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
            ≤ PrimeSpectrum.basicOpen f)).op).hom y)
        = ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
            ≤ PrimeSpectrum.basicOpen (r:R))).op).hom a := by
    rintro ⟨r, hr⟩
    have hloc := Hfr (PrimeSpectrum.basicOpen r) ⟨r, rfl⟩ ⟨r, hr, le_refl _⟩
    obtain ⟨⟨a, s⟩, hs⟩ := hloc.surj (((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r
            ≤ PrimeSpectrum.basicOpen f)).op).hom y)
    obtain ⟨m, hm⟩ := s.2
    refine ⟨a, m, ?_⟩
    have hsR : (s : R) • (((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r
            ≤ PrimeSpectrum.basicOpen f)).op).hom y)
        = ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen r
            ≤ PrimeSpectrum.basicOpen r)).op).hom a := hs
    rw [← hm] at hsR; exact hsR
  choose a m hm using perr
  -- Stage 2: common power N and normalized sections b r := f^(N - m r) • a r.
  set N := Finset.univ.sup m with hN
  have hb : ∀ r : {x // x ∈ t},
      ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
            ≤ PrimeSpectrum.basicOpen (r:R))).op).hom (f ^ (N - m r) • a r)
        = f ^ N • (((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
            ≤ PrimeSpectrum.basicOpen f)).op).hom y) := by
    intro r
    have hle : m r ≤ N := Finset.le_sup (Finset.mem_univ r)
    set g := ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
            ≤ PrimeSpectrum.basicOpen (r:R))).op).hom with hg
    have hms : g (f ^ (N - m r) • a r) = f ^ (N - m r) • g (a r) := LinearMap.map_smul g _ (a r)
    rw [hms, ← hm r, ← mul_smul, ← pow_add, Nat.sub_add_cancel hle]
  -- Stage 3: overlaps — common further power exists pairwise.
  have hover : ∀ i j : {x // x ∈ t}, ∃ p : ℕ,
      f ^ p • ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_left : PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)
          ≤ PrimeSpectrum.basicOpen (i:R))).op).hom (f ^ (N - m i) • a i)
      = f ^ p • ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_right : PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)
          ≤ PrimeSpectrum.basicOpen (j:R))).op).hom (f ^ (N - m j) • a j) := by
    intro i j
    have ai := descent_overlap_agree M f i N
      (PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)) inf_le_left y _ (hb i)
    have aj := descent_overlap_agree M f j N
      (PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)) inf_le_right y _ (hb j)
    have hloc := Hfr (PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R))
      ⟨(i:R) * (j:R), (PrimeSpectrum.basicOpen_mul (i:R) (j:R)).symm⟩ ⟨i, i.2, inf_le_left⟩
    obtain ⟨c, hc⟩ := hloc.exists_of_eq (ai.trans aj.symm)
    obtain ⟨p, hp⟩ := c.2
    have hp' : f ^ p = (c : R) := hp
    exact ⟨p, by rw [hp']; exact hc⟩
  choose p hp using hover
  -- Stage 4: global further power P, glue the compatible family.
  set P := Finset.univ.sup (fun i => Finset.univ.sup (fun j => p i j)) with hP
  have hPle : ∀ i j : {x // x ∈ t}, p i j ≤ P := fun i j =>
    le_trans (Finset.le_sup (f := fun j => p i j) (Finset.mem_univ j))
      (Finset.le_sup (f := fun i => Finset.univ.sup (fun j => p i j)) (Finset.mem_univ i))
  have hcompat : TopCat.Presheaf.IsCompatible (modulesSpecToSheaf.obj M).presheaf
      (fun r : {x // x ∈ t} => (PrimeSpectrum.basicOpen (r:R) : (Spec R).Opens))
      (fun r => f ^ P • (f ^ (N - m r) • a r)) := by
    intro i j
    change ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_left : PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)
          ≤ PrimeSpectrum.basicOpen (i:R))).op).hom (f ^ P • (f ^ (N - m i) • a i))
      = ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_right : PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)
          ≤ PrimeSpectrum.basicOpen (j:R))).op).hom (f ^ P • (f ^ (N - m j) • a j))
    have ms_i := LinearMap.map_smul ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_left : PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)
          ≤ PrimeSpectrum.basicOpen (i:R))).op).hom (f ^ P) (f ^ (N - m i) • a i)
    have ms_j := LinearMap.map_smul ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_right : PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)
          ≤ PrimeSpectrum.basicOpen (j:R))).op).hom (f ^ P) (f ^ (N - m j) • a j)
    have X : f ^ P • ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_left : PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)
          ≤ PrimeSpectrum.basicOpen (i:R))).op).hom (f ^ (N - m i) • a i)
      = f ^ P • ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_right : PrimeSpectrum.basicOpen (i:R) ⊓ PrimeSpectrum.basicOpen (j:R)
          ≤ PrimeSpectrum.basicOpen (j:R))).op).hom (f ^ (N - m j) • a j) := by
      rw [← Nat.sub_add_cancel (hPle i j), pow_add, mul_smul, mul_smul, hp i j]
    exact ms_i.trans (X.trans ms_j.symm)
  obtain ⟨x, hx, -⟩ := TopCat.Sheaf.existsUnique_gluing' (modulesSpecToSheaf.obj M)
    (fun r : {x // x ∈ t} => (PrimeSpectrum.basicOpen (r:R) : (Spec R).Opens)) ⊤
    (fun r => homOfLE le_top) (le_of_eq (iSup_basicOpen_subtype_eq_top hspan).symm)
    (fun r => f ^ P • (f ^ (N - m r) • a r)) hcompat
  -- Stage 5: x|_{D(f)} = f^(N+P) • y, by separatedness over the cover {D(f) ⊓ D(r)} of D(f).
  refine ⟨x, P + N, ?_⟩
  have hcoverDf : (PrimeSpectrum.basicOpen f : (Spec R).Opens)
      ≤ ⨆ r : {x // x ∈ t}, (PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)) := by
    rw [← inf_iSup_eq, iSup_basicOpen_subtype_eq_top hspan, inf_top_eq]
  refine TopCat.Sheaf.eq_of_locally_eq' (modulesSpecToSheaf.obj M)
    (fun r : {x // x ∈ t} => (PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)))
    (PrimeSpectrum.basicOpen f) (fun r => homOfLE inf_le_left) hcoverDf
    (f ^ (P + N) • y)
    (((modulesSpecToSheaf.obj M).presheaf.map
      (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom x) ?_
  intro r
  -- LHS = f^(N+P) • (y|_{D(f) ⊓ D(r)})
  change ((modulesSpecToSheaf.obj M).presheaf.map
      (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
        ≤ PrimeSpectrum.basicOpen f)).op).hom (f ^ (P + N) • y)
    = ((modulesSpecToSheaf.obj M).presheaf.map
      (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
        ≤ PrimeSpectrum.basicOpen f)).op).hom
      (((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom x)
  -- compute the right-hand side via x|_{D(r)} = f^P • b r
  have ex := res_comp (modulesSpecToSheaf.obj M) (A := ⊤) (B := PrimeSpectrum.basicOpen f)
      (C := PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R))
      le_top inf_le_left le_top x
  have ex2 := res_comp (modulesSpecToSheaf.obj M) (A := ⊤) (B := PrimeSpectrum.basicOpen (r:R))
      (C := PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R))
      le_top inf_le_right le_top x
  have hxr : ((modulesSpecToSheaf.obj M).presheaf.map
      (homOfLE (le_top : PrimeSpectrum.basicOpen (r:R) ≤ ⊤)).op).hom x
      = f ^ P • (f ^ (N - m r) • a r) := hx r
  -- ρ[D(f),Dfr] (x|_{D(f)}) = ρ[⊤,Dfr] x = ρ[D(r),Dfr] (x|_{D(r)}) = ρ[D(r),Dfr] (f^P • b r)
  have hRHS : ((modulesSpecToSheaf.obj M).presheaf.map
      (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
        ≤ PrimeSpectrum.basicOpen f)).op).hom
      (((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom x)
    = f ^ (P + N) • (((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen (r:R)
          ≤ PrimeSpectrum.basicOpen f)).op).hom y) :=
    ex.trans (ex2.symm.trans ((congrArg _ hxr).trans
      ((LinearMap.map_smul _ (f ^ P) (f ^ (N - m r) • a r)).trans
        ((congrArg (f ^ P • ·) (hb r)).trans
          ((mul_smul (f ^ P) (f ^ N) _).symm.trans (congrArg (· • _) (pow_add f P N).symm))))))
  exact (LinearMap.map_smul _ (f ^ (P + N)) y).trans hRHS.symm

/-- **Section-localization descent from a local-tilde cover (gap1 keystone, D), cover form.**  Let
`M` be a sheaf of modules on `Spec R` and `f : R`.  Suppose `{D(r)}_{r ∈ t}` is a finite basic-open
cover of `Spec R` (`Ideal.span t = ⊤`) and for every open `U` contained in some cover member `D(r)`
(in particular each `D(r)` and each overlap `D(r) ⊓ D(r')`) the basic-open restriction
`Γ(M, U) → Γ(M, D(f) ⊓ U)` is a localization at `powers f` (`Hfr` — the gated P1 local-tilde data).
Then the section restriction `Γ(M, ⊤) → Γ(M, D(f))` is `IsLocalizedModule (powers f)` over `R`.

This is the project-internal finite-equalizer/flatness descent of Stacks `lemma-invert-f-sections`
(Hartshorne II.5.3), built without the global affine `QCoh(Spec R) ≃ Mod R` equivalence (which is
gap1 itself): `map_units` holds for arbitrary `M` (`map_units_restrict_basicOpen`), `surj'` is
`descent_surj`, and `exists_of_eq` is `descent_smul_eq_zero`.  The named gap1 keystone
`isLocalizedModule_basicOpen_descent` for quasi-coherent `M` is this lemma instantiated at the cover
`exists_finite_basicOpen_cover_le_quasicoherentData` once `Hfr` is produced from
`isIso_fromTildeΓ_restrict_basicOpen` (the slice→Spec-`R_r` section transport, the remaining gated
step).  Project-local. -/
theorem isLocalizedModule_basicOpen_descent_of_cover {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (f : R) (t : Finset R) (hspan : Ideal.span (t : Set R) = ⊤)
    (Hfr : ∀ U : (Spec R).Opens, (∃ r ∈ t, U ≤ PrimeSpectrum.basicOpen r) →
      IsLocalizedModule (Submonoid.powers f)
        ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ U ≤ U)).op).hom) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom where
  map_units := map_units_restrict_basicOpen M f
  surj y := by
    obtain ⟨x, n, hxn⟩ := descent_surj M f t hspan (fun U _ hcov => Hfr U hcov) y
    exact ⟨⟨x, ⟨f ^ n, n, rfl⟩⟩, hxn⟩
  exists_of_eq {x₁ x₂} h := by
    have hθ : ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom (x₁ - x₂) = 0 := by
      rw [map_sub, h, sub_self]
    obtain ⟨n, hn⟩ := descent_smul_eq_zero M f t hspan
      (fun r hr => Hfr (PrimeSpectrum.basicOpen r) ⟨r, hr, le_refl _⟩) (x₁ - x₂) hθ
    exact ⟨⟨f ^ n, n, rfl⟩, sub_eq_zero.mp ((smul_sub (f ^ n) x₁ x₂).symm.trans hn)⟩

/-- **Section-localization descent from a local-tilde cover, basic-open hypothesis form.**

Same conclusion as `isLocalizedModule_basicOpen_descent_of_cover`, but the per-cover-element
localization data `Hfr` need only be supplied for *basic* opens `D(s) ≤ D(r)` (rather than every
open `U ≤ D(r)`).  This is the **instantiable** form of the cover-descent: the per-element P1
transport produces a localization only on the basic opens of the affine slice `Spec R_r` — a general
open of `Spec R_r` need not be quasi-compact, so the global Stacks `lemma-invert-f-sections` is
unavailable for it — while the sheaf-gluing engines `descent_surj`/`descent_smul_eq_zero` only ever
consult `Hfr` at the basic opens `D(r)` and the overlaps `D(r) ⊓ D(r') = D(r·r')`.

It rebuilds the three `IsLocalizedModule` fields directly: `map_units` is
`map_units_restrict_basicOpen` (holds for arbitrary `M`), `surj` is `descent_surj` fed
the basic-open
`Hfr` (the open `U` it consults is always `D(s)`, so `Hfr s` supplies the datum after `U = D(s)` is
substituted), and `exists_of_eq` is `descent_smul_eq_zero` fed `Hfr` at each `D(r)`.  Project-local:
the named gap1 keystone `isLocalizedModule_basicOpen_descent` for quasi-coherent `M` is this lemma
instantiated at the cover `exists_finite_basicOpen_cover_le_quasicoherentData`, with the basic-open
`Hfr` produced from the P1 transport `isIso_fromTildeΓ_restrict_basicOpen`. -/
theorem isLocalizedModule_basicOpen_descent_of_basicOpen_cover {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (f : R) (t : Finset R) (hspan : Ideal.span (t : Set R) = ⊤)
    (Hfr : ∀ s : R, (∃ r ∈ t, (PrimeSpectrum.basicOpen s : (Spec R).Opens)
        ≤ PrimeSpectrum.basicOpen r) →
      IsLocalizedModule (Submonoid.powers f)
        ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen s
            ≤ PrimeSpectrum.basicOpen s)).op).hom) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom where
  map_units := map_units_restrict_basicOpen M f
  surj y := by
    obtain ⟨x, n, hxn⟩ := descent_surj M f t hspan
      (fun U hbo hcov => by obtain ⟨s, rfl⟩ := hbo; exact Hfr s hcov) y
    exact ⟨⟨x, ⟨f ^ n, n, rfl⟩⟩, hxn⟩
  exists_of_eq {x₁ x₂} h := by
    have hθ : ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom (x₁ - x₂) = 0 := by
      rw [map_sub, h, sub_self]
    obtain ⟨n, hn⟩ := descent_smul_eq_zero M f t hspan
      (fun r hr => Hfr r ⟨r, hr, le_refl _⟩) (x₁ - x₂) hθ
    exact ⟨⟨f ^ n, n, rfl⟩, sub_eq_zero.mp ((smul_sub (f ^ n) x₁ x₂).symm.trans hn)⟩

/-! ## Project-local Mathlib supplement — `IsLocalizedModule` transport for gap1-D Hfr

The section-transport iso `gammaPullbackImageIso` is only an additive-group (`Ab`) isomorphism,
semilinear over the *source-scheme* section ring, whereas the `Hfr` hypothesis of
`isLocalizedModule_basicOpen_descent_of_cover` is an `IsLocalizedModule` statement `R`-linear over
the base ring `R`. Two Mathlib-absent transport ingredients bridge the gap:

* **(I)** `isLocalizedModule_of_ringEquiv_semilinear` — transport `IsLocalizedModule S g` across a
  ring-iso-`σ`-semilinear `AddEquiv` pair. Mathlib only has the same-ring `of_linearEquiv` /
  `of_linearEquiv_right`; the section iso crosses a ring iso, so this is the genuine gap.
* **(II)** `isLocalizedModule_restrictScalars_powers_algebraMap` — a localization at
  `powers (algebraMap R Rr f)` over a base-changed ring `Rr` (here `R` localized at `r`) is, after
  restriction of scalars, a localization at `powers f` over `R`.

Both are pure module algebra and Mathlib-absent at the pinned commit; project-bespoke. -/

/-- **(I) Ring-iso-semilinear `IsLocalizedModule` transport.** Given a ring isomorphism
`σ : R ≃+* R'`, two `σ`-semilinear additive isomorphisms `e₁ : M₁ ≃+ N₁`, `e₂ : M₂ ≃+ N₂` (i.e.
`eᵢ (a • x) = σ a • eᵢ x`), and an `R'`-linear map `h : N₁ →ₗ[R'] N₂` intertwining a localization
map `g` with the `eᵢ` (`h (e₁ x) = e₂ (g x)`), the map `h` is a localization at the image submonoid
`S.map σ`. Mathlib only provides the same-ring `IsLocalizedModule.of_linearEquiv`; this crosses a
ring iso, the form needed to turn the `Ab`/semilinear section iso `gammaPullbackImageIso` into the
`R`-linear `Hfr` data. Project-local. -/
theorem isLocalizedModule_of_ringEquiv_semilinear
    {R R' : Type*} [CommRing R] [CommRing R'] (σ : R ≃+* R')
    {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₁] [Module R' N₁] [AddCommGroup N₂] [Module R' N₂]
    (S : Submonoid R)
    (g : M₁ →ₗ[R] M₂) [IsLocalizedModule S g]
    (e₁ : M₁ ≃+ N₁) (e₂ : M₂ ≃+ N₂)
    (he₁ : ∀ (a : R) (x : M₁), e₁ (a • x) = σ a • e₁ x)
    (he₂ : ∀ (a : R) (x : M₂), e₂ (a • x) = σ a • e₂ x)
    (h : N₁ →ₗ[R'] N₂)
    (hh : ∀ x, h (e₁ x) = e₂ (g x)) :
    IsLocalizedModule (S.map (σ : R →+* R')) h where
  map_units x := by
    obtain ⟨s, hs, hsx⟩ := x.2
    rw [Module.End.isUnit_iff]
    have hsrc := IsLocalizedModule.map_units g ⟨s, hs⟩
    rw [Module.End.isUnit_iff] at hsrc
    have hfun : (⇑(algebraMap R' (Module.End R' N₂) (↑x : R')))
        = ⇑e₂ ∘ ⇑(algebraMap R (Module.End R M₂) (⟨s, hs⟩ : S)) ∘ ⇑e₂.symm := by
      funext y
      rw [Module.algebraMap_end_apply, Function.comp_apply, Function.comp_apply,
        Module.algebraMap_end_apply, he₂, e₂.apply_symm_apply]
      congr 1
      exact hsx.symm
    rw [hfun]
    exact e₂.bijective.comp (hsrc.comp e₂.symm.bijective)
  surj y := by
    obtain ⟨⟨x, s⟩, hx⟩ := IsLocalizedModule.surj S g (e₂.symm y)
    refine ⟨⟨e₁ x, ⟨σ ↑s, ↑s, s.2, rfl⟩⟩, ?_⟩
    have he : e₂ ((↑s : R) • e₂.symm y) = e₂ (g x) := congrArg e₂ hx
    rw [he₂, e₂.apply_symm_apply, ← hh] at he
    exact he
  exists_of_eq {y₁ y₂} heq := by
    have h1 : e₂ (g (e₁.symm y₁)) = e₂ (g (e₁.symm y₂)) := by
      rw [← hh, ← hh, e₁.apply_symm_apply, e₁.apply_symm_apply]; exact heq
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := g) (e₂.injective h1)
    refine ⟨⟨σ ↑c, ↑c, c.2, rfl⟩, ?_⟩
    have hc' : (↑c : R) • e₁.symm y₁ = (↑c : R) • e₁.symm y₂ := hc
    have hcc := congrArg e₁ hc'
    rw [he₁, he₁, e₁.apply_symm_apply, e₁.apply_symm_apply] at hcc
    exact hcc

/-- **(II) Localization at a base-changed submonoid descends to the base ring.** If `g` is
`Rr`-linear and exhibits a localization at `powers (algebraMap R Rr f)` over a base-changed ring
`Rr` (an algebra over `R` — here `R` localized at some `r`), then its restriction of scalars to `R`
is a localization
at `powers f` over `R`. This lets the `R_r`-level localization that P1 (`IsIso fromTildeΓ`) produces
on the slice `Spec R_r` be read back as the `R`-level `Hfr` data the cover-form descent consumes.
Mathlib-absent; project-local. -/
theorem isLocalizedModule_restrictScalars_powers_algebraMap
    {R Rr : Type*} [CommRing R] [CommRing Rr] [Algebra R Rr]
    {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [Module Rr M₁] [IsScalarTower R Rr M₁]
    [AddCommGroup M₂] [Module R M₂] [Module Rr M₂] [IsScalarTower R Rr M₂]
    (f : R) (g : M₁ →ₗ[Rr] M₂)
    [IsLocalizedModule (Submonoid.powers (algebraMap R Rr f)) g] :
    IsLocalizedModule (Submonoid.powers f) (g.restrictScalars R) where
  map_units x := by
    obtain ⟨n, hn⟩ := x.2
    have hn' : f ^ n = ↑x := hn
    rw [Module.End.isUnit_iff]
    have hmem : (algebraMap R Rr f) ^ n ∈ Submonoid.powers (algebraMap R Rr f) := ⟨n, rfl⟩
    have hsrc := IsLocalizedModule.map_units g ⟨_, hmem⟩
    rw [Module.End.isUnit_iff] at hsrc
    have hfun : ⇑(algebraMap R (Module.End R M₂) (↑x : R))
        = ⇑(algebraMap Rr (Module.End Rr M₂) ((algebraMap R Rr f) ^ n)) := by
      funext z
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← hn', ← map_pow,
        algebraMap_smul]
    rw [hfun]; exact hsrc
  surj y := by
    obtain ⟨⟨x, s⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers (algebraMap R Rr f)) g y
    obtain ⟨n, hn⟩ := s.2
    have hn' : (algebraMap R Rr f) ^ n = ↑s := hn
    refine ⟨⟨x, ⟨f ^ n, n, rfl⟩⟩, ?_⟩
    have hsmul : (f ^ n : R) • y = (↑s : Rr) • y := by
      rw [← hn', ← map_pow, algebraMap_smul]
    change (f ^ n : R) • y = (g.restrictScalars R) x
    rw [hsmul, LinearMap.coe_restrictScalars]; exact hx
  exists_of_eq {x₁ x₂} heq := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (algebraMap R Rr f))
      (f := g) heq
    obtain ⟨n, hn⟩ := c.2
    have hn' : (algebraMap R Rr f) ^ n = ↑c := hn
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    have e1 : (f ^ n : R) • x₁ = (↑c : Rr) • x₁ := by rw [← hn', ← map_pow, algebraMap_smul]
    have e2 : (f ^ n : R) • x₂ = (↑c : Rr) • x₂ := by rw [← hn', ← map_pow, algebraMap_smul]
    change (f ^ n : R) • x₁ = (f ^ n : R) • x₂
    rw [e1, e2]; exact hc

/-! ## Project-local Mathlib supplement — gap1-D Hfr: pullback-section transport

The remaining gated ingredient of the named gap1 keystone
`isLocalizedModule_basicOpen_descent` is the **section-level** analogue of P1's object-level
transport: for an open immersion `f : X ⟶ Y` and a sheaf of modules `M` on `Y`, the sections of the
geometric pullback `(pullback f).obj M` over an open `U ⊆ X` are canonically identified with the
sections of `M` over the image `f ''ᵁ U`.

The construction is `Γ(-, U)` applied to the inverse of Mathlib's `restrictFunctorIsoPullback f`
(`restrictFunctor f ≅ pullback f`) at `M`, using the *definitional* identity
`Γ((restrictFunctor f).obj M, U) = Γ(M, f ''ᵁ U)` (`Scheme.Modules.restrict_obj`, `rfl`). Because
both sides are `Γ(-, U)` of a single fixed module isomorphism, naturality in `U` (intertwining the
presheaf restriction maps) is free: it is the naturality of the underlying abelian-presheaf
morphism. Mathlib-absent at the pinned commit; project-bespoke. -/

/-- **Global sections of a pullback along an open immersion are sections over the image**
(gap1, Hfr section transport, general open). For an open immersion `f : X ⟶ Y`, a sheaf of modules
`M` on `Y`, and an open `U ⊆ X`, the additive groups of sections satisfy
`Γ((pullback f).obj M, U) ≅ Γ(M, f ''ᵁ U)`. This is `Γ(-, U)` of `(restrictFunctorIsoPullback f)⁻¹`
at `M`; the codomain is `Γ((restrictFunctor f).obj M, U) = Γ(M, f ''ᵁ U)` definitionally. Naturality
in `U` is `gammaPullbackImageIso_hom_naturality`. -/
noncomputable def gammaPullbackImageIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : X.Opens) :
    Γ((Scheme.Modules.pullback f).obj M, U) ≅ Γ(M, f ''ᵁ U) :=
  (Scheme.Modules.toPresheaf X ⋙ (CategoryTheory.evaluation _ _).obj (Opposite.op U)).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback f).symm.app M)

/-- **The pullback-section comparison intertwines the restriction maps** (gap1, Hfr, naturality).
For opens `V ≤ U` of `X`, `gammaPullbackImageIso` commutes with the presheaf restriction maps of
`(pullback f).obj M` and of `M` (along the image inclusion `f ''ᵁ V ≤ f ''ᵁ U`). This is the
naturality of the underlying morphism of abelian presheaves. -/
theorem gammaPullbackImageIso_hom_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) {U V : X.Opens} (i : V ⟶ U) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map i.op ≫ (gammaPullbackImageIso f M V).hom
      = (gammaPullbackImageIso f M U).hom ≫ M.presheaf.map (f.opensFunctor.map i).op := by
  exact (((Scheme.Modules.restrictFunctorIsoPullback f).symm.app M).hom.mapPresheaf).naturality i.op

/-- **Global sections of a pullback along an open immersion are sections over the range**
(gap1, Hfr section transport). The `U = ⊤` instance of `gammaPullbackImageIso`:
`Γ((pullback f).obj M, ⊤) ≅ Γ(M, f.opensRange)`, using `f ''ᵁ ⊤ = f.opensRange`. Once this lands the
named-form descent `isLocalizedModule_basicOpen_descent` and gap1 follow. -/
noncomputable def gammaPullbackTopIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) :
    Γ((Scheme.Modules.pullback f).obj M, ⊤) ≅ Γ(M, f.opensRange) :=
  gammaPullbackImageIso f M ⊤ ≪≫ eqToIso (by rw [Scheme.Hom.image_top_eq_opensRange])

/-- **Open-immersion structure-sheaf ring iso on an image open** (gap1, Hfr semilinearity).
For an open immersion `j : X ⟶ Y` and an open `V ⊆ X`, the immersion is an isomorphism onto its
image `j ''ᵁ V`, so pulling structure-sheaf sections back gives a ring isomorphism
`σ_V : Γ(X, V) ≃+* Γ(Y, j ''ᵁ V)`. This is `(j.appIso V)⁻¹` packaged as a `RingEquiv`; it is the
`σ` along which `gammaPullbackImageIso_hom_semilinear` is semilinear, the form bridge (I)
`isLocalizedModule_of_ringEquiv_semilinear` consumes.

The direction is source `→` image (so `σ_V a` lands in `Γ(Y, j ''ᵁ V)` for `a : Γ(X, V)`, the
section ring acting on the pullback module's sections). Project-local. -/
noncomputable def gammaImageRingEquiv {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (V : X.Opens) : Γ(X, V) ≃+* Γ(Y, j ''ᵁ V) :=
  (j.appIso V).commRingCatIsoToRingEquiv.symm

/-- **Semilinearity of the pullback section transport** (gap1 semilinearity wall). The forward map
of `gammaPullbackImageIso` is `σ_V`-semilinear (`σ_V = gammaImageRingEquiv`): for `a : Γ(X, V)` a
section of the structure sheaf and `x` a section of the pullback module,
`hom (a • x) = σ_V a • hom x`. The pullback-side action is the structure-sheaf action through
the pullback's `mapPresheaf`; the action on the `M` side is `M`'s action through `σ_V`.
Project-local. -/
theorem gammaPullbackImageIso_hom_semilinear {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) (V : X.Opens) (a : Γ(X, V))
    (x : Γ((Scheme.Modules.pullback j).obj M, V)) :
    (gammaPullbackImageIso j M V).hom (a • x)
      = gammaImageRingEquiv j V a • (gammaPullbackImageIso j M V).hom x := by
  -- `gammaPullbackImageIso j M V`'s forward map is `Γ(-, V)` of the `Ab`-morphism
  -- `ψ := ((restrictFunctorIsoPullback j).symm.app M).hom`, i.e. the section map `ψ.app V`.
  simp only [gammaPullbackImageIso, Functor.mapIso_hom, Functor.comp_map,
    Scheme.Modules.toPresheaf_map, CategoryTheory.evaluation_obj_map,
    Scheme.Modules.mapPresheaf_app]
  -- `ψ.app V` is `Γ(X, V)`-linear (`Hom.app_smul`): `ψ.app V (a • x) = a • ψ.app V x`, the
  -- `Γ(X, V)`-action being `restrictFunctor`'s `restrictScalars`-action along `(j.appIso V).inv`.
  erw [Scheme.Modules.Hom.app_smul]
  -- The `restrictScalars` action `a •_{restrict} m` is defeq to `(j.appIso V).inv a •_M m`,
  -- and `σ_V a = gammaImageRingEquiv j V a = (j.appIso V).inv a`, so the two sides agree by `rfl`.
  rfl

/-! ## Project-local Mathlib supplement — gap1-D Hfr: combined algebra transport

The two `IsLocalizedModule` bridges (I) `isLocalizedModule_of_ringEquiv_semilinear` and (II)
`isLocalizedModule_restrictScalars_powers_algebraMap` are chained into a single transport lemma:
the localization that P1 (`IsIso fromTildeΓ`) produces on the slice `Spec R_r` (a localization at
`powers f'` over the section ring `S`) is read back, across the `σ`-semilinear section isos and the
base change `R → A` (`A = R_r`), as a localization at `powers f` over the base ring `R`. -/

/-- **(I)+(II) combined: ring-iso-semilinear localization transport descending to the base ring.**

Given a base ring `R`, an `R`-algebra `A`, a ring iso `σ : S ≃+* A` carrying `f' : S` to
`algebraMap R A f`, a localization `g` at `powers f'` over `S`, two `σ`-semilinear additive
isomorphisms `e₁, e₂` onto `A`-modules (also `R`-modules via the scalar tower `R → A`), and an
`A`-linear map `h` intertwining `g` with the `eᵢ` (`h (e₁ x) = e₂ (g x)`), the restriction of
scalars of `h` to `R` is a localization at `powers f` over `R`.

This is the algebra core of the gap1 `Hfr` transport: bridge (I)
(`isLocalizedModule_of_ringEquiv_semilinear`) moves the localization across the ring iso to
`powers (algebraMap R A f)` over `A`, then bridge (II)
(`isLocalizedModule_restrictScalars_powers_algebraMap`) descends it to `powers f` over `R`.
Project-local. -/
theorem isLocalizedModule_powers_transport
    {R A S : Type*} [CommRing R] [CommRing A] [CommRing S] [Algebra R A]
    (σ : S ≃+* A) (f : R) (f' : S) (hf : σ f' = algebraMap R A f)
    {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module S M₁] [AddCommGroup M₂] [Module S M₂]
    [AddCommGroup N₁] [Module A N₁] [Module R N₁] [IsScalarTower R A N₁]
    [AddCommGroup N₂] [Module A N₂] [Module R N₂] [IsScalarTower R A N₂]
    (g : M₁ →ₗ[S] M₂) [IsLocalizedModule (Submonoid.powers f') g]
    (e₁ : M₁ ≃+ N₁) (e₂ : M₂ ≃+ N₂)
    (he₁ : ∀ (a : S) (x : M₁), e₁ (a • x) = σ a • e₁ x)
    (he₂ : ∀ (a : S) (x : M₂), e₂ (a • x) = σ a • e₂ x)
    (h : N₁ →ₗ[A] N₂)
    (hh : ∀ x, h (e₁ x) = e₂ (g x)) :
    IsLocalizedModule (Submonoid.powers f) (h.restrictScalars R) := by
  have hI : IsLocalizedModule ((Submonoid.powers f').map (σ : S →+* A)) h :=
    isLocalizedModule_of_ringEquiv_semilinear σ (Submonoid.powers f') g e₁ e₂ he₁ he₂ h hh
  have key : (Submonoid.powers f').map (σ : S →+* A) = Submonoid.powers (algebraMap R A f) := by
    rw [Submonoid.map_powers]; exact congrArg Submonoid.powers hf
  rw [key] at hI
  haveI := hI
  exact isLocalizedModule_restrictScalars_powers_algebraMap f h

/-- **`IsIso M.fromTildeΓ` is invariant under isomorphism of modules.** If `M ≅ M'` as sheaves of
modules on `Spec R` and `M.fromTildeΓ` is an isomorphism, then so is `M'.fromTildeΓ`.

Immediate from `isIso_fromTildeΓ_iff`
(`IsIso M.fromTildeΓ ↔ M ∈ essImage (tilde.functor R)`) and the
fact that the essential image is closed under isomorphism (`Functor.essImage.ofIso`). This is the
transport that lets P1's `IsIso fromTildeΓ` for the iterated-pullback module
`(pullback isoSpec.inv).obj ((pullback ι_W).obj ((pullback ι).obj M))` be carried to the pullback
`(pullback j).obj M` along the single composite open immersion `j = isoSpec.inv ≫ ι_W ≫ ι` (which is
isomorphic to the iterated one via the `pullbackComp` coherences). Project-local. -/
theorem isIso_fromTildeΓ_of_iso {R : CommRingCat.{u}} {M M' : (Spec R).Modules}
    (e : M ≅ M') [IsIso M.fromTildeΓ] : IsIso M'.fromTildeΓ := by
  rw [isIso_fromTildeΓ_iff] at *
  exact Functor.essImage.ofIso e ‹_›

/-! ## Project-local Mathlib supplement — gap1 section-transport producer

The geometric producer chain manufacturing the basic-open `Hfr` datum from the per-element P1
transport. See blueprint subsection "Section-transport producer for the basic-open Hfr". -/

/-- **Composite open immersion `j : Spec Γ(q.X i, ι⁻¹ᵁ D(s)) ⟶ Spec R`** identifying the affine
slice with the basic open `D(s)`.  It is `isoSpec.inv ≫ ι_W ≫ ι_{q.X i}` where
`W := ι_{q.X i}⁻¹ᵁ D(s)`; the domain is the genuine affine `Spec` of the slice's section ring.
Project-local: the geometric backbone of the section-transport producer. -/
noncomputable def compositeBasicOpenImmersion {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) (s : R) (i : q.I)
    (hs : (PrimeSpectrum.basicOpen s : (Spec R).Opens) ≤ q.X i) :
    Spec Γ(↑(q.X i), (Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen s)) ⟶ Spec R :=
  ((IsAffineOpen.Spec_basicOpen s).preimage_of_isOpenImmersion (Scheme.Opens.ι (q.X i))
      (by rw [Scheme.Opens.opensRange_ι]; exact hs)).isoSpec.inv ≫
    Scheme.Opens.ι ((Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen s)) ≫
    Scheme.Opens.ι (q.X i)

/-- **(producer, a) `fromTildeΓ` iso of the composite-immersion pullback.** For a quasi-coherent
`M` on `Spec R` and a basic open `D(s) ≤ q.X i`, the pullback module `(pullback j).obj M` along the
composite immersion `j = compositeBasicOpenImmersion` has an isomorphism `fromTildeΓ` counit.

The geometric content is the P1 keystone `isIso_fromTildeΓ_restrict_basicOpen`, which supplies
`IsIso fromTildeΓ` for the *iterated* pullback
`(pullback isoSpec.inv).obj ((pullback ι_W).obj ((pullback ι_{q.X i}).obj M))`; the iterated and the
composite pullbacks are identified by the `pullbackComp` pseudofunctor coherences, and
`isIso_fromTildeΓ_of_iso` transports the isomorphism across. Project-local: the critical first
ingredient of the section-transport producer. -/
theorem pullback_composite_immersion_isIso_fromTildeΓ {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) (s : R) (i : q.I)
    (hs : (PrimeSpectrum.basicOpen s : (Spec R).Opens) ≤ q.X i) :
    IsIso (@Scheme.Modules.fromTildeΓ
      (Γ(↑(q.X i), (Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen s)))
      ((Scheme.Modules.pullback (compositeBasicOpenImmersion M q s i hs)).obj M)) := by
  exact @isIso_fromTildeΓ_of_iso _ _ _
    ((Scheme.Modules.pullback (((IsAffineOpen.Spec_basicOpen s).preimage_of_isOpenImmersion
          (Scheme.Opens.ι (q.X i))
          (by rw [Scheme.Opens.opensRange_ι]; exact hs)).isoSpec.inv)).mapIso
        ((Scheme.Modules.pullbackComp
          (Scheme.Opens.ι ((Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen s)))
          (Scheme.Opens.ι (q.X i))).app M) ≪≫
      (Scheme.Modules.pullbackComp
        (((IsAffineOpen.Spec_basicOpen s).preimage_of_isOpenImmersion (Scheme.Opens.ι (q.X i))
          (by rw [Scheme.Opens.opensRange_ι]; exact hs)).isoSpec.inv)
        (Scheme.Opens.ι ((Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen s)) ≫
          Scheme.Opens.ι (q.X i))).app M)
    (isIso_fromTildeΓ_restrict_basicOpen M q s i hs)

/-- The composite immersion `j = compositeBasicOpenImmersion` is an open immersion (composite of an
iso and two open immersions). Needed for `.opensRange`, `''ᵁ`, and `gammaImageRingEquiv` on `j`. -/
instance compositeBasicOpenImmersion_isOpenImmersion {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) (s : R) (i : q.I)
    (hs : (PrimeSpectrum.basicOpen s : (Spec R).Opens) ≤ q.X i) :
    IsOpenImmersion (compositeBasicOpenImmersion M q s i hs) := by
  unfold compositeBasicOpenImmersion
  infer_instance

/-- **(producer, b) Range of the composite immersion is `D(s)`.** The open range of
`j = compositeBasicOpenImmersion` is exactly the basic open `D(s)`: `isoSpec.inv` is an iso (its
range is `⊤`), so the range is `ι_{q.X i} ''ᵁ (ι_{q.X i}⁻¹ᵁ D(s)) = (q.X i) ⊓ D(s) = D(s)` using
`D(s) ≤ q.X i`. Project-local image bookkeeping for the section-transport producer. -/
theorem compositeBasicOpenImmersion_opensRange {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) (s : R) (i : q.I)
    (hs : (PrimeSpectrum.basicOpen s : (Spec R).Opens) ≤ q.X i) :
    (compositeBasicOpenImmersion M q s i hs).opensRange
      = (PrimeSpectrum.basicOpen s : (Spec R).Opens) := by
  unfold compositeBasicOpenImmersion
  rw [Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr hs

/-! ## Project-local Mathlib supplement — gap1 section-transport producer (b-flocus/c/d/TOP)

The remaining producer chain assembling the basic-open `Hfr` datum (consumed by
`isLocalizedModule_basicOpen_descent_of_basicOpen_cover`) from the per-element P1 transport
`pullback_composite_immersion_isIso_fromTildeΓ` via the algebra combiner
`isLocalizedModule_powers_transport`.  See blueprint "Section-transport producer for the basic-open
Hfr". -/

/-- **Image of an affine basic open under an open immersion of affines.** For an open immersion
`j : Spec S ⟶ Spec R` and `f' : S`, the image `j ''ᵁ D(f')` is the `Spec R` scheme basic open of the
transported global section `(j.appIso ⊤).inv ((ΓSpecIso S).inv f')`.  Pure geometry:
`basicOpen_eq_of_affine` turns `D(f')` into the scheme basic open of a global structure section of
`Spec S`, and `Scheme.image_basicOpen` transports it across `j`.  Stated with `j` opaque so the
`rw` does not unfold a concrete composite immersion.  Project-local. -/
theorem image_basicOpen_of_affine {S R : CommRingCat.{u}} (j : Spec S ⟶ Spec R)
    [IsOpenImmersion j] (f' : S) :
    j ''ᵁ (PrimeSpectrum.basicOpen f')
      = (Spec R).basicOpen ((j.appIso ⊤).inv ((Scheme.ΓSpecIso S).inv f')) := by
  rw [← basicOpen_eq_of_affine f', Scheme.image_basicOpen j ((Scheme.ΓSpecIso S).inv f')]

/-- **(producer, b-flocus, image of a basic open).** The image under
`j = compositeBasicOpenImmersion`
of a basic open `D(f')` of the affine slice is the `Spec R` basic open of the transported section
`(j.appIso ⊤).inv ((ΓSpecIso _).inv f')`.  Instantiates `image_basicOpen_of_affine` at the concrete
composite immersion.  Project-local. -/
theorem compositeBasicOpenImmersion_image_basicOpen {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) (s : R) (i : q.I)
    (hs : (PrimeSpectrum.basicOpen s : (Spec R).Opens) ≤ q.X i)
    (f' : Γ(↑(q.X i), (Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen s))) :
    (compositeBasicOpenImmersion M q s i hs) ''ᵁ (PrimeSpectrum.basicOpen f')
      = (Spec R).basicOpen
          (((compositeBasicOpenImmersion M q s i hs).appIso ⊤).inv ((Scheme.ΓSpecIso _).inv f')) :=
  image_basicOpen_of_affine (compositeBasicOpenImmersion M q s i hs) f'

/-- **Image of an affine basic open as an intersection with the range.** If the appIso-transport of
`f'` agrees with the restriction to `j ''ᵁ ⊤` of a global section `g : Γ(Spec R, ⊤)`, then
`j ''ᵁ D(f') = (j ''ᵁ ⊤) ⊓ (Spec R).basicOpen g`.  Combines `image_basicOpen_of_affine` with the
structure-sheaf identity `Scheme.basicOpen_res`.  Project-local. -/
theorem image_basicOpen_eq_inf {S R : CommRingCat.{u}} (j : Spec S ⟶ Spec R)
    [IsOpenImmersion j] (f' : S) (g : Γ(Spec R, ⊤))
    (hfg : (j.appIso ⊤).inv ((Scheme.ΓSpecIso S).inv f')
        = (Spec R).presheaf.map (homOfLE (le_top : (j ''ᵁ ⊤) ≤ ⊤)).op g) :
    j ''ᵁ (PrimeSpectrum.basicOpen f') = (j ''ᵁ ⊤) ⊓ (Spec R).basicOpen g := by
  rw [image_basicOpen_of_affine, hfg, Scheme.basicOpen_res]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- Large multi-step assembly (localization combiner + `eqToHom` open-transport); needs headroom.
/-- **(producer, TOP-aux) Basic-open `Hfr` along an abstract affine open immersion.**  For an open
immersion `j : Spec S ⟶ Spec R` with `IsIso (fromTildeΓ ((pullback j).obj M))` (the P1 datum), a
ring element `f : R` and a slice element `f' : S` whose appIso-transport is the restriction of `f`
(`hf'`), and target opens `U = j ''ᵁ ⊤`, `V = j ''ᵁ D(f')`, the section restriction
`Γ(M, U) → Γ(M, V)` is `IsLocalizedModule (powers f)` over `R`.

The proof assembles the P1 object-level `IsIso fromTildeΓ` into a section-level localization via the
algebra combiner `isLocalizedModule_powers_transport`: the engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ` localizes `Γ(M',⊤) → Γ(M', D(f'))` over the slice
ring `S`; the `σ`-semilinear section isos `e₁ = gammaPullbackImageIso ⊤`,
`e₂ = gammaPullbackImageIso D(f')` (over `σ = (ΓSpecIso S)⁻¹ ≪≫ gammaImageRingEquiv ⊤`) and the
restriction map `h` intertwine it, and the combiner descends the result to `powers f` over `R`.
Finally the `j ''ᵁ`-form opens are transported to `U` / `V` via `eT`, `eB`.  `j` is kept abstract so
the section-ring defeqs stay cheap.
Project-local: the abstract core of the gap1 keystone `Hfr` producer. -/
theorem section_localization_hfr_aux {R S : CommRingCat.{u}} (M : (Spec R).Modules)
    (j : Spec S ⟶ Spec R) [IsOpenImmersion j]
    (hP1 : IsIso (Scheme.Modules.fromTildeΓ ((Scheme.Modules.pullback j).obj M)))
    (f : R) (f' : S) (U V : (Spec R).Opens) (hUV : V ≤ U)
    (eT : (j ''ᵁ (⊤ : (Spec S).Opens)) = U)
    (eB : (j ''ᵁ (PrimeSpectrum.basicOpen f')) = V)
    (hf' : (j.appIso ⊤).inv ((Scheme.ΓSpecIso S).inv f')
        = (Spec R).presheaf.map (homOfLE (le_top : (j ''ᵁ ⊤) ≤ ⊤)).op
            ((Scheme.ΓSpecIso R).inv f)) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map (homOfLE hUV).op).hom := by
  set M' := (Scheme.Modules.pullback j).obj M with hM'
  haveI : IsIso (Scheme.Modules.fromTildeΓ M') := hP1
  set A := Γ(Spec R, j ''ᵁ (⊤ : (Spec S).Opens)) with hA
  let algRA : (R : Type _) →+* (A : Type _) :=
    ((Spec R).presheaf.map (homOfLE (le_top : (j ''ᵁ ⊤) ≤ ⊤)).op).hom.comp
      (Scheme.ΓSpecIso R).inv.hom
  letI instAlg : Algebra (R : Type _) (A : Type _) := RingHom.toAlgebra algRA
  let σ : (S : Type _) ≃+* (A : Type _) :=
    (Scheme.ΓSpecIso S).symm.commRingCatIsoToRingEquiv.trans (gammaImageRingEquiv j ⊤)
  have hf : σ f' = algebraMap (R : Type _) (A : Type _) f := hf'
  let ii : (j ''ᵁ (PrimeSpectrum.basicOpen f') : (Spec R).Opens) ⟶ j ''ᵁ (⊤ : (Spec S).Opens) :=
    j.opensFunctor.map (homOfLE le_top)
  let N₁ := Γ(M, j ''ᵁ (⊤ : (Spec S).Opens))
  let N₂ := Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f'))
  letI iAN₂ : Module (A : Type _) (ToType N₂) :=
    Module.compHom (ToType N₂) ((Spec R).presheaf.map ii.op).hom
  letI iRN₁ : Module (R : Type _) (ToType N₁) :=
    Module.compHom _ (algebraMap (R : Type _) (A : Type _))
  letI iRN₂ : Module (R : Type _) (ToType N₂) :=
    Module.compHom _ (algebraMap (R : Type _) (A : Type _))
  haveI iST₁ : IsScalarTower (R : Type _) (A : Type _) (ToType N₁) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI iST₂ : IsScalarTower (R : Type _) (A : Type _) (ToType N₂) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let e₁ := (gammaPullbackImageIso j M ⊤).addCommGroupIsoToAddEquiv
  let e₂ := (gammaPullbackImageIso j M (PrimeSpectrum.basicOpen f')).addCommGroupIsoToAddEquiv
  let g := ((modulesSpecToSheaf.obj M').presheaf.map
    (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)).op).hom
  haveI : IsLocalizedModule (Submonoid.powers f') g :=
    isLocalizedModule_restrict_of_isIso_fromTildeΓ M' f'
  let h : ToType N₁ →ₗ[(A : Type _)] ToType N₂ :=
    { toFun := fun m => (M.presheaf.map ii.op) m
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a m => Scheme.Modules.map_smul M ii a m }
  have he₁ : ∀ (a : (S : Type _))
      (x : ToType ((modulesSpecToSheaf.obj M').presheaf.obj (.op ⊤))),
      e₁ (a • x) = σ a • e₁ x :=
    fun a x => gammaPullbackImageIso_hom_semilinear j M ⊤ ((Scheme.ΓSpecIso S).inv a) x
  have key0 := j.appIso_inv_naturality (U := (⊤ : (Spec S).Opens))
    (V := PrimeSpectrum.basicOpen f') (homOfLE le_top).op
  have he₂ : ∀ (a : (S : Type _))
      (x : ToType ((modulesSpecToSheaf.obj M').presheaf.obj (.op (PrimeSpectrum.basicOpen f')))),
      e₂ (a • x) = σ a • e₂ x := by
    intro a x
    have h1 := gammaPullbackImageIso_hom_semilinear j M (PrimeSpectrum.basicOpen f')
      ((Spec S).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso S).inv a)) x
    have key : (gammaImageRingEquiv j (PrimeSpectrum.basicOpen f'))
          ((Spec S).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso S).inv a))
        = ((Spec R).presheaf.map ii.op).hom (σ a) :=
      congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso S).inv a)) key0
    exact h1.trans (congrArg (· • e₂ x) key)
  have hh : ∀ x, h (e₁ x) = e₂ (g x) := by
    intro x
    have hn := ConcreteCategory.congr_hom
      (gammaPullbackImageIso_hom_naturality j M
        (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤))) x
    simp only [CategoryTheory.comp_apply] at hn
    exact hn.symm
  have RESULT : IsLocalizedModule (Submonoid.powers f) (h.restrictScalars (R : Type _)) :=
    isLocalizedModule_powers_transport σ f f' hf g e₁ e₂ he₁ he₂ h hh
  -- transport the `j ''ᵁ`-form localization to the `D(s)` / `D(f) ⊓ D(s)` Hfr form
  -- the combiner's map is, by defeq, the `modulesSpecToSheaf` restriction along `ii`
  have RESULT' : IsLocalizedModule (Submonoid.powers f)
      (((modulesSpecToSheaf.obj M).presheaf.map ii.op).hom) := RESULT
  -- eqToHom open isos transporting `j ''ᵁ ⊤ → U` and `j ''ᵁ D(f') → V`
  have hUop : (Opposite.op U : (Spec R).Opensᵒᵖ)
      = Opposite.op (j ''ᵁ (⊤ : (Spec S).Opens)) := congrArg Opposite.op eT.symm
  have hVop : (Opposite.op V : (Spec R).Opensᵒᵖ)
      = Opposite.op (j ''ᵁ (PrimeSpectrum.basicOpen f')) := congrArg Opposite.op eB.symm
  let αU := (asIso ((modulesSpecToSheaf.obj M).presheaf.map (eqToHom hUop))).toLinearEquiv
  let αV := (asIso ((modulesSpecToSheaf.obj M).presheaf.map (eqToHom hVop))).toLinearEquiv
  haveI hRES := RESULT'
  have step1 : IsLocalizedModule (Submonoid.powers f)
      ((((modulesSpecToSheaf.obj M).presheaf.map ii.op).hom) ∘ₗ αU.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (S := Submonoid.powers f)
      (f := ((modulesSpecToSheaf.obj M).presheaf.map ii.op).hom) αU
  haveI hS1 := step1
  have step : IsLocalizedModule (Submonoid.powers f)
      (αV.symm.toLinearMap ∘ₗ
        ((((modulesSpecToSheaf.obj M).presheaf.map ii.op).hom) ∘ₗ αU.toLinearMap)) :=
    IsLocalizedModule.of_linearEquiv (S := Submonoid.powers f)
      (f := (((modulesSpecToSheaf.obj M).presheaf.map ii.op).hom) ∘ₗ αU.toLinearMap) αV.symm
  -- forward naturality square (uses only the forward eqToHom isos, both `rfl`-identified)
  have hsq : ((((modulesSpecToSheaf.obj M).presheaf.map ii.op).hom) ∘ₗ αU.toLinearMap)
      = (αV.toLinearMap ∘ₗ
          ((modulesSpecToSheaf.obj M).presheaf.map (homOfLE hUV).op).hom) := by
    rw [show αU.toLinearMap = ((modulesSpecToSheaf.obj M).presheaf.map (eqToHom hUop)).hom from rfl,
      show αV.toLinearMap = ((modulesSpecToSheaf.obj M).presheaf.map (eqToHom hVop)).hom from rfl,
      ← ModuleCat.hom_comp, ← ModuleCat.hom_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun m => ((modulesSpecToSheaf.obj M).presheaf.map m).hom)
      (Subsingleton.elim _ _)
  have hcancel : αV.symm.toLinearMap ∘ₗ αV.toLinearMap = LinearMap.id := by
    ext y; simp
  -- the transported composite equals the Hfr restriction map
  have hcomp : ((modulesSpecToSheaf.obj M).presheaf.map (homOfLE hUV).op).hom
      = αV.symm.toLinearMap ∘ₗ
        ((((modulesSpecToSheaf.obj M).presheaf.map ii.op).hom) ∘ₗ αU.toLinearMap) := by
    rw [hsq, ← LinearMap.comp_assoc, hcancel, LinearMap.id_comp]
  rw [hcomp]
  exact step

/-- **(producer, TOP) Basic-open `Hfr` from the per-element P1 transport.**  For a quasi-coherent
`M` on `Spec R`, a basic open `D(s) ≤ q.X i`, and `f : R`, the section restriction
`Γ(M, D(s)) → Γ(M, D(f) ⊓ D(s))` is `IsLocalizedModule (powers f)` over `R`.  This is the gated
basic-open `Hfr` datum consumed by `isLocalizedModule_basicOpen_descent_of_basicOpen_cover`.

Thin wrapper around `section_localization_hfr_aux`: it instantiates the abstract open immersion at
the concrete composite immersion `j = compositeBasicOpenImmersion`, supplies the P1 datum
`pullback_composite_immersion_isIso_fromTildeΓ`, picks `f' = σ⁻¹(algebraMap R A f)` (so `hf'` is
`σ.apply_symm_apply`), and identifies the `j ''ᵁ`-form opens with `D(s)` (`opensRange`) and
`D(f) ⊓ D(s)` (`image_basicOpen_eq_inf`).  Project-local: the geometric producer of the gap1
keystone `Hfr`. -/
theorem section_localization_hfr_basicOpen {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) (f s : R) (i : q.I)
    (hs : (PrimeSpectrum.basicOpen s : (Spec R).Opens) ≤ q.X i) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen s
          ≤ PrimeSpectrum.basicOpen s)).op).hom := by
  set S := Γ(↑(q.X i), (Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen s)) with hS
  set j := compositeBasicOpenImmersion M q s i hs with hj
  set A := Γ(Spec R, j ''ᵁ (⊤ : (Spec S).Opens)) with hA
  let algRA : (R : Type _) →+* (A : Type _) :=
    ((Spec R).presheaf.map (homOfLE (le_top : (j ''ᵁ ⊤) ≤ ⊤)).op).hom.comp
      (Scheme.ΓSpecIso R).inv.hom
  letI instAlg : Algebra (R : Type _) (A : Type _) := RingHom.toAlgebra algRA
  let σ : (S : Type _) ≃+* (A : Type _) :=
    (Scheme.ΓSpecIso S).symm.commRingCatIsoToRingEquiv.trans (gammaImageRingEquiv j ⊤)
  let f' : (S : Type _) := σ.symm (algebraMap (R : Type _) (A : Type _) f)
  have hf' : (j.appIso ⊤).inv ((Scheme.ΓSpecIso S).inv f')
      = (Spec R).presheaf.map (homOfLE (le_top : (j ''ᵁ ⊤) ≤ ⊤)).op
          ((Scheme.ΓSpecIso R).inv f) := σ.apply_symm_apply _
  have eT : (j ''ᵁ (⊤ : (Spec S).Opens)) = PrimeSpectrum.basicOpen s :=
    (Scheme.Hom.image_top_eq_opensRange j).trans
      (compositeBasicOpenImmersion_opensRange M q s i hs)
  have eB : (j ''ᵁ (PrimeSpectrum.basicOpen f'))
      = PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen s := by
    rw [image_basicOpen_eq_inf j f' ((Scheme.ΓSpecIso R).inv f) hf', eT, basicOpen_eq_of_affine]
    exact inf_comm _ _
  exact section_localization_hfr_aux M j
    (pullback_composite_immersion_isIso_fromTildeΓ M q s i hs) f f'
    (PrimeSpectrum.basicOpen s) (PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen s)
    inf_le_right eT eB hf'

/-! ## Project-local Mathlib supplement — gap2 single-chart transport

The general-scheme keystone `lem:qcoh_section_localization_basicOpen`
(`isLocalizedModule_basicOpen`): for a quasi-coherent sheaf of modules `M` on an *arbitrary* scheme
`X`, an affine open `U`, and `f : Γ(X, U)`, the section restriction `Γ(M, U) → Γ(M, D(f))` is
`IsLocalizedModule (powers f)` over `Γ(X, U)`.

It is the single-chart affine transport on top of G1-core: pull `M` back along the affine immersion
`hU.fromSpec : Spec Γ(X, U) ⟶ X` (range `U`), so the pullback `M'` is quasi-coherent on
`Spec Γ(X, U)`, where gap1 gives `IsIso M'.fromTildeΓ`; the engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ` localizes the slice restriction over `Γ(X, U)`, and
the `σ`-semilinear section comparison `gammaPullbackImageIso` (bridge (I)
`isLocalizedModule_of_ringEquiv_semilinear`) transports it to the `M`-side restriction. No
cover-and-glue: `U` is already affine, so there is a single chart. -/

/-- **The `Γ(X,U)`-linear section restriction map of a sheaf of modules.** For `M : X.Modules` and
an inclusion of opens `i : V ⟶ U`, the presheaf restriction `Γ(M, U) → Γ(M, V)` is `Γ(X, U)`-linear
when `Γ(M, V)` carries the `Γ(X, U)`-module structure restricted along `X.presheaf.map i.op`
(`Module.compHom`). Linearity is `Scheme.Modules.map_smul`. Project-local: the linear-map packaging
of the section restriction needed to state `IsLocalizedModule` for a general scheme (Mathlib's
presheaf-of-modules restriction is semilinear, not bundled this way). -/
noncomputable def restrictₗ {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    letI : Module Γ(X, U) Γ(M, V) := Module.compHom _ (X.presheaf.map i.op).hom
    Γ(M, U) →ₗ[Γ(X, U)] Γ(M, V) :=
  letI : Module Γ(X, U) Γ(M, V) := Module.compHom _ (X.presheaf.map i.op).hom
  { toFun := fun x => M.presheaf.map i.op x
    map_add' := map_add _
    map_smul' := fun r x => Scheme.Modules.map_smul M i r x }

/-- **The `Γ(X,U)`-linear restriction of sections to a basic open `D(f)`** (`f : Γ(X, U)`). The
section restriction `Γ(M, U) → Γ(M, X.basicOpen f)` is `Γ(X, U)`-linear, where `Γ(M, X.basicOpen f)`
carries any `Γ(X, U)`-module structure compatible (via `IsScalarTower`) with its native
`Γ(X, X.basicOpen f)`-module structure and the canonical `Γ(X, U)`-algebra map
`Γ(X, U) → Γ(X, X.basicOpen f)` (the restriction `X.presheaf.map`). Linearity combines
`Scheme.Modules.map_smul` with the scalar tower. This is the consumer-facing shape of the gap2
keystone (instances supplied by the caller, matching `Module.annihilator_isLocalizedModule_eq_map`).
Project-local. -/
noncomputable def restrictBasicOpenₗ {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (f : Γ(X, U))
    [Module Γ(X, U) Γ(M, X.basicOpen f)]
    [IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)] :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f) where
  toFun := fun x => M.presheaf.map (homOfLE (X.basicOpen_le f)).op x
  map_add' := map_add _
  map_smul' := fun r x => by
    change M.presheaf.map (homOfLE (X.basicOpen_le f)).op (r • x) = r • _
    rw [Scheme.Modules.map_smul M (homOfLE (X.basicOpen_le f)) r x,
      ← algebraMap_smul Γ(X, X.basicOpen f) r (M.presheaf.map (homOfLE (X.basicOpen_le f)).op x)]
    rfl

/-- **`fromSpec`-section coherence** (gap2 transport crux). For an affine open `U` of a scheme `X`,
the `eqToHom`-transport `Γ(X, hU.fromSpec ''ᵁ ⊤) → Γ(X, U)` (along the equality
`hU.fromSpec ''ᵁ ⊤ = U`) equals the composite ring iso
`(hU.fromSpec.appIso ⊤).hom ≫ (ΓSpecIso Γ(X, U)).hom`. Equivalently, the section ring iso
`σ = (ΓSpecIso)⁻¹ ≫ gammaImageRingEquiv (fromSpec) ⊤` underlying the gap2 section
comparison is, up to
this `eqToHom` transport, the identity. This is the coherence needed to read the gap2-core
localization (over `Γ(X, hU.fromSpec ''ᵁ ⊤)`, at `powers (σ f)`) back as a localization over
`Γ(X, U)` at `powers f`. Proof: `fromSpec_app_self` + `appIso_hom'` + cancellation of the
`Spec Γ(X, U)`-presheaf maps (all between `⊤`, hence forced by `Subsingleton`). Project-local. -/
theorem fromSpec_image_top_section_coherence {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (eT : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U) :
    X.presheaf.map (eqToHom eT.symm).op
      = (hU.fromSpec.appIso (⊤ : (Spec Γ(X, U)).Opens)).hom ≫ (Scheme.ΓSpecIso Γ(X, U)).hom := by
  rw [← cancel_epi (X.presheaf.map (eqToHom eT).op),
    ← X.presheaf.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id, X.presheaf.map_id]
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE]
  have hnat := hU.fromSpec.naturality (eqToHom eT).op
  simp only [Category.assoc]
  rw [reassoc_of% hnat, hU.fromSpec_app_self]
  simp only [eqToHom_unop, eqToHom_map, eqToHom_op]
  simp only [Category.assoc]
  rw [eqToHom_trans_assoc, ← eqToHom_map (Spec Γ(X, U)).presheaf,
    ← (Spec Γ(X, U)).presheaf.map_comp_assoc]
  · rw [Subsingleton.elim (eqToHom _ ≫ (homOfLE _).op)
      (𝟙 (Opposite.op (⊤ : (Spec Γ(X, U)).Opens))),
      (Spec Γ(X, U)).presheaf.map_id, Category.id_comp, Iso.inv_hom_id]
  · rw [eT, hU.fromSpec_preimage_self]

/-- **(gap2 core) Basic-open section localization along an abstract affine open immersion.** For an
open immersion `j : Spec S ⟶ X` with the P1 datum `IsIso (fromTildeΓ ((pullback j).obj M))`, a slice
element `f' : S`, and `f : Γ(X, j ''ᵁ ⊤)` with `σ f' = f` (`σ = (ΓSpecIso S)⁻¹ ≫ gammaImageRingEquiv
j ⊤`), the section restriction `Γ(M, j ''ᵁ ⊤) → Γ(M, j ''ᵁ D(f'))` is
`IsLocalizedModule (powers f)` over `Γ(X, j ''ᵁ ⊤)`.

The proof mirrors `section_localization_hfr_aux` but over an arbitrary ambient scheme `X` (so the
localization ring is the *local* section ring `A = Γ(X, j ''ᵁ ⊤)`, not a global `R`): the engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ` localizes the slice restriction `g` over `S`, the
`σ`-semilinear section comparisons `e₁, e₂` (`gammaPullbackImageIso`) intertwine `g` with the
`M`-side restriction `h = restrictₗ M ii`, and bridge (I)
`isLocalizedModule_of_ringEquiv_semilinear` transports the localization across `σ`, landing
`powers ((powers f').map σ) = powers (σ f') = powers f`. Because the base and target rings coincide
(`R = A`), no `restrictScalars` base-change (bridge II) is needed. Project-local. -/
theorem section_localization_hfr_aux_general {X : Scheme.{u}} {S : CommRingCat.{u}}
    (M : X.Modules) (j : Spec S ⟶ X) [IsOpenImmersion j]
    (hP1 : IsIso (Scheme.Modules.fromTildeΓ ((Scheme.Modules.pullback j).obj M)))
    (f : Γ(X, j ''ᵁ (⊤ : (Spec S).Opens))) (f' : S)
    (hf' : (gammaImageRingEquiv j ⊤) ((Scheme.ΓSpecIso S).inv f') = f) :
    letI : Module Γ(X, j ''ᵁ (⊤ : (Spec S).Opens)) Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f')) :=
      Module.compHom _ (X.presheaf.map (j.opensFunctor.map (homOfLE le_top)).op).hom
    IsLocalizedModule (Submonoid.powers f)
      (show Γ(M, j ''ᵁ (⊤ : (Spec S).Opens)) →ₗ[Γ(X, j ''ᵁ (⊤ : (Spec S).Opens))]
          Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f')) from
        restrictₗ M (j.opensFunctor.map (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)))) := by
  let M' := (Scheme.Modules.pullback j).obj M
  haveI : IsIso (Scheme.Modules.fromTildeΓ M') := hP1
  let σ : (S : Type _) ≃+* (Γ(X, j ''ᵁ (⊤ : (Spec S).Opens)) : Type _) :=
    (Scheme.ΓSpecIso S).symm.commRingCatIsoToRingEquiv.trans (gammaImageRingEquiv j ⊤)
  have hf : σ f' = f := hf'
  let ii : (j ''ᵁ (PrimeSpectrum.basicOpen f') : X.Opens) ⟶ j ''ᵁ (⊤ : (Spec S).Opens) :=
    j.opensFunctor.map (homOfLE le_top)
  letI iAN₂ : Module (Γ(X, j ''ᵁ (⊤ : (Spec S).Opens)) : Type _)
      (ToType Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f'))) :=
    Module.compHom _ (X.presheaf.map ii.op).hom
  let e₁ := (gammaPullbackImageIso j M ⊤).addCommGroupIsoToAddEquiv
  let e₂ := (gammaPullbackImageIso j M (PrimeSpectrum.basicOpen f')).addCommGroupIsoToAddEquiv
  let g := ((modulesSpecToSheaf.obj M').presheaf.map
    (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)).op).hom
  haveI : IsLocalizedModule (Submonoid.powers f') g :=
    isLocalizedModule_restrict_of_isIso_fromTildeΓ M' f'
  let h : ToType Γ(M, j ''ᵁ (⊤ : (Spec S).Opens)) →ₗ[(Γ(X, j ''ᵁ (⊤ : (Spec S).Opens)) : Type _)]
      ToType Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f')) :=
    { toFun := fun m => (M.presheaf.map ii.op) m
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a m => Scheme.Modules.map_smul M ii a m }
  have he₁ : ∀ (a : (S : Type _))
      (x : ToType ((modulesSpecToSheaf.obj M').presheaf.obj (.op ⊤))),
      e₁ (a • x) = σ a • e₁ x :=
    fun a x => gammaPullbackImageIso_hom_semilinear j M ⊤ ((Scheme.ΓSpecIso S).inv a) x
  have key0 := j.appIso_inv_naturality (U := (⊤ : (Spec S).Opens))
    (V := PrimeSpectrum.basicOpen f') (homOfLE le_top).op
  have he₂ : ∀ (a : (S : Type _))
      (x : ToType ((modulesSpecToSheaf.obj M').presheaf.obj (.op (PrimeSpectrum.basicOpen f')))),
      e₂ (a • x) = σ a • e₂ x := by
    intro a x
    have h1 := gammaPullbackImageIso_hom_semilinear j M (PrimeSpectrum.basicOpen f')
      ((Spec S).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso S).inv a)) x
    have key : (gammaImageRingEquiv j (PrimeSpectrum.basicOpen f'))
          ((Spec S).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso S).inv a))
        = (X.presheaf.map ii.op).hom (σ a) :=
      congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso S).inv a)) key0
    exact h1.trans (congrArg (· • e₂ x) key)
  have hh : ∀ x, h (e₁ x) = e₂ (g x) := by
    intro x
    have hn := ConcreteCategory.congr_hom
      (gammaPullbackImageIso_hom_naturality j M
        (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤))) x
    simp only [CategoryTheory.comp_apply] at hn
    exact hn.symm
  have RESULT : IsLocalizedModule
      ((Submonoid.powers f').map (σ : S →+* Γ(X, j ''ᵁ (⊤ : (Spec S).Opens)))) h :=
    isLocalizedModule_of_ringEquiv_semilinear σ (Submonoid.powers f') g e₁ e₂ he₁ he₂ h hh
  have key : (Submonoid.powers f').map (σ : S →+* Γ(X, j ''ᵁ (⊤ : (Spec S).Opens)))
      = Submonoid.powers f := by
    rw [Submonoid.map_powers]; exact congrArg Submonoid.powers hf
  rw [key] at RESULT
  exact RESULT

/-- **(gap1 keystone) Section-localization descent for quasi-coherent `M`.**  For a quasi-coherent
sheaf of modules `M` on `Spec R` and `f : R`, the global-to-`D(f)` section restriction
`Γ(M, ⊤) → Γ(M, D(f))` is `IsLocalizedModule (powers f)` over `R`.

Instantiates the cover-form descent `isLocalizedModule_basicOpen_descent_of_basicOpen_cover` at the
finite basic-open cover `exists_finite_basicOpen_cover_le_quasicoherentData` refining the
quasi-coherent data `q`, with the per-element basic-open `Hfr` supplied by the producer
`section_localization_hfr_basicOpen` (each cover overlap `D(s) ≤ D(r) ≤ q.X i` feeds the producer at
`i`).  Project-local: the named gap1 keystone (Hartshorne II.5.3 / Stacks
`lemma-invert-f-sections`), built without the global affine `QCoh ≃ Mod` equivalence. -/
theorem isLocalizedModule_basicOpen_descent {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [hqc : M.IsQuasicoherent] (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by
  obtain ⟨q⟩ := hqc.nonempty_quasicoherentData
  obtain ⟨t, hspan, hcov⟩ := exists_finite_basicOpen_cover_le_quasicoherentData M q
  refine isLocalizedModule_basicOpen_descent_of_basicOpen_cover M f t hspan ?_
  intro s hs_ex
  obtain ⟨r, hr, hsr⟩ := hs_ex
  obtain ⟨i, hri⟩ := hcov r hr
  exact section_localization_hfr_basicOpen M q f s i (le_trans hsr hri)

/-- **(gap1) `IsIso M.fromTildeΓ` for quasi-coherent `M`.**  The tilde-Gamma counit of a
quasi-coherent sheaf of modules on `Spec R` is an isomorphism (equivalently, `M` lies in the
essential image of `tilde`).  This is the affine quasi-coherent ⟺ `tilde` bridge that Mathlib leaves
open at the pinned commit.

Immediate from the keystone `isLocalizedModule_basicOpen_descent` (per-basic-open section
localization for quasi-coherent `M`) via the section-to-counit assembly
`isIso_fromTildeΓ_of_isLocalizedModule_restrict`.  Project-local: closes gap1. -/
theorem isIso_fromTildeΓ_of_isQuasicoherent {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] : IsIso M.fromTildeΓ :=
  isIso_fromTildeΓ_of_isLocalizedModule_restrict M
    (fun f => isLocalizedModule_basicOpen_descent M f)

/-- **G1-core: section-localization for a quasi-coherent sheaf on `Spec R`**
(`lem:qcoh_affine_section_localization`). For a quasi-coherent sheaf of modules `M` on `Spec R` and
`f : R`, the section restriction `Γ(M, ⊤) → Γ(M, D(f))` exhibits the target as the localized module
`(powers f)⁻¹ Γ(M, ⊤)`, i.e. it is `IsLocalizedModule (powers f)` over `R`.

This is the clean named form of gap1's downstream corollary: gap1
(`isIso_fromTildeΓ_of_isQuasicoherent`) makes `M.fromTildeΓ` an isomorphism, and the affine engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ` then delivers all three `IsLocalizedModule` fields
at once. Project-local: Mathlib has no `QCoh(Spec R) → section-localization` bridge. It is the
affine `X = Spec R`, `U = ⊤` instance of the general-scheme keystone
`isLocalizedModule_basicOpen` (gap2). -/
theorem isLocalizedModule_basicOpen_of_isQuasicoherent {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom :=
  haveI := isIso_fromTildeΓ_of_isQuasicoherent M
  isLocalizedModule_restrict_of_isIso_fromTildeΓ M f

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- The multi-step eqToHom open-transport + bridge-(I) ring-iso assembly needs heartbeat headroom.
/-- **(gap2, Piece B — the eqToHom bridge)** Basic-open section localization from the gap2-core,
given the P1 datum directly.  For a sheaf of modules `M` on a scheme `X`, an affine open `U`, the P1
hypothesis `hP1 : IsIso (fromTildeΓ ((pullback hU.fromSpec).obj M))`, and `f : Γ(X, U)`, the
consumer-facing basic-open section restriction `restrictBasicOpenₗ M f` is
`IsLocalizedModule (powers f)` over `Γ(X, U)`.

This is the mechanical eqToHom bridge from `section_localization_hfr_aux_general` (instantiated at
the affine immersion `j = hU.fromSpec`, slice element `f' = f`, image section `f_im = σ f`) to
`restrictBasicOpenₗ`: the open identifications `j ''ᵁ ⊤ = U` (`eT`) and
`j ''ᵁ D(f) = X.basicOpen f` (`IsAffineOpen.fromSpec_image_basicOpen`) plus the section ring iso
`ρ = X.presheaf.map (eqToHom eT.symm).op : Γ(X, j ''ᵁ ⊤) ≃+* Γ(X, U)` transport the localization
across (bridge (I) `isLocalizedModule_of_ringEquiv_semilinear`), the only non-trivial coherence
being `ρ (σ f) = f`, supplied by the crux `fromSpec_image_top_section_coherence`.  Project-local:
separates the genuinely-new QC-pullback (Piece A) from the mechanical transport. -/
theorem isLocalizedModule_basicOpen_of_hP1 {X : Scheme.{u}} (M : X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U)
    (hP1 : IsIso (Scheme.Modules.fromTildeΓ ((Scheme.Modules.pullback hU.fromSpec).obj M)))
    (f : Γ(X, U))
    [Module Γ(X, U) Γ(M, X.basicOpen f)]
    [IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)] :
    IsLocalizedModule (Submonoid.powers f) (restrictBasicOpenₗ M f) := by
  set j := hU.fromSpec with hj
  have eT : (j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) = U :=
    (Scheme.Hom.image_top_eq_opensRange j).trans hU.opensRange_fromSpec
  have eB : (j ''ᵁ (PrimeSpectrum.basicOpen f)) = X.basicOpen f := hU.fromSpec_image_basicOpen f
  -- the image section `f_im = σ f` and the `hf'` discharge (rfl)
  set f_im : Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) :=
    (gammaImageRingEquiv j ⊤) ((Scheme.ΓSpecIso Γ(X, U)).inv f) with hf_im
  have hf' : (gammaImageRingEquiv j ⊤) ((Scheme.ΓSpecIso Γ(X, U)).inv f) = f_im := rfl
  -- `ii : j ''ᵁ D(f) ⟶ j ''ᵁ ⊤` and the core localization over `A = Γ(X, j ''ᵁ ⊤)`
  set ii : (j ''ᵁ (PrimeSpectrum.basicOpen f) : X.Opens) ⟶ j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) :=
    j.opensFunctor.map (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)) with hii
  letI : Module Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens))
      Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f)) :=
    Module.compHom _ (X.presheaf.map ii.op).hom
  have core : IsLocalizedModule (Submonoid.powers f_im)
      (show Γ(M, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) →ₗ[Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens))]
          Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f)) from restrictₗ M ii) :=
    section_localization_hfr_aux_general M j hP1 f_im f hf'
  -- the ring iso `ρ : Γ(X, j ''ᵁ ⊤) ≃+* Γ(X, U)`
  haveI : IsIso (X.presheaf.map (eqToHom eT.symm).op) := inferInstance
  set ρ : Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) ≃+* Γ(X, U) :=
    (asIso (X.presheaf.map (eqToHom eT.symm).op)).commRingCatIsoToRingEquiv with hρ
  -- `ρ (σ f) = f`, the crux coherence
  have hρf : ρ f_im = f := by
    have hcrux := fromSpec_image_top_section_coherence hU eT
    change (X.presheaf.map (eqToHom eT.symm).op).hom f_im = f
    rw [hcrux, hf_im, CommRingCat.comp_apply]
    change (Scheme.ΓSpecIso Γ(X, U)).hom.hom ((j.appIso ⊤).hom.hom
        ((j.appIso ⊤).inv.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom f))) = f
    rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  -- additive isos `e₁ : Γ(M, j ''ᵁ ⊤) ≃+ Γ(M, U)`, `e₂ : Γ(M, j ''ᵁ D(f)) ≃+ Γ(M, X.basicOpen f)`
  haveI : IsIso (M.presheaf.map (eqToHom eT.symm).op) := inferInstance
  haveI : IsIso (M.presheaf.map (eqToHom eB.symm).op) := inferInstance
  set e₁ := (asIso (M.presheaf.map (eqToHom eT.symm).op)).addCommGroupIsoToAddEquiv with he₁def
  set e₂ := (asIso (M.presheaf.map (eqToHom eB.symm).op)).addCommGroupIsoToAddEquiv with he₂def
  -- semilinearity of `e₁`, `e₂` over `ρ`
  have he₁ : ∀ (a : Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)))
      (x : ToType Γ(M, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens))),
      e₁ (a • x) = ρ a • e₁ x := by
    intro a x
    exact Scheme.Modules.map_smul M (eqToHom eT.symm) a x
  have he₂ : ∀ (a : Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)))
      (x : ToType Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f))),
      e₂ (a • x) = ρ a • e₂ x := by
    intro a x
    change (M.presheaf.map (eqToHom eB.symm).op).hom
        ((X.presheaf.map ii.op).hom a • x) = ρ a • e₂ x
    rw [Scheme.Modules.map_smul M (eqToHom eB.symm) ((X.presheaf.map ii.op).hom a) x,
      ← algebraMap_smul Γ(X, X.basicOpen f) (ρ a) (e₂ x)]
    refine congrArg (· • (e₂ x)) ?_
    change (X.presheaf.map (eqToHom eB.symm).op).hom ((X.presheaf.map ii.op).hom a)
      = (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (ρ a)
    change ((X.presheaf.map ii.op) ≫ (X.presheaf.map (eqToHom eB.symm).op)).hom a
      = ((X.presheaf.map (eqToHom eT.symm).op) ≫
          (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)).hom a
    rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    exact congrArg (fun m => (X.presheaf.map m).hom a) (Subsingleton.elim _ _)
  -- the intertwining `restrictBasicOpenₗ M f (e₁ x) = e₂ (g x)`
  have hh : ∀ x, restrictBasicOpenₗ M f (e₁ x)
      = e₂ ((show Γ(M, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) →ₗ[Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens))]
          Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f)) from restrictₗ M ii) x) := by
    intro x
    change (M.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
        ((M.presheaf.map (eqToHom eT.symm).op).hom x)
      = (M.presheaf.map (eqToHom eB.symm).op).hom ((M.presheaf.map ii.op).hom x)
    change ((M.presheaf.map (eqToHom eT.symm).op) ≫
          (M.presheaf.map (homOfLE (X.basicOpen_le f)).op)).hom x
      = ((M.presheaf.map ii.op) ≫ (M.presheaf.map (eqToHom eB.symm).op)).hom x
    rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
    exact congrArg (fun m => (M.presheaf.map m).hom x) (Subsingleton.elim _ _)
  -- assemble bridge (I)
  haveI := core
  have RESULT : IsLocalizedModule ((Submonoid.powers f_im).map (ρ : _ →+* Γ(X, U)))
      (restrictBasicOpenₗ M f) :=
    isLocalizedModule_of_ringEquiv_semilinear ρ (Submonoid.powers f_im)
      (show Γ(M, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) →ₗ[Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens))]
          Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f)) from restrictₗ M ii)
      e₁ e₂ he₁ he₂ (restrictBasicOpenₗ M f) hh
  have key : (Submonoid.powers f_im).map (ρ : _ →+* Γ(X, U)) = Submonoid.powers f := by
    rw [Submonoid.map_powers]; exact congrArg Submonoid.powers hρf
  rwa [key] at RESULT

/-! ## Project-local Mathlib supplement — pullback of QC along an open immersion (gap2, Piece A)

Route-1 chain L1–L6 building `isQuasicoherent_pullback_fromSpec`: the pullback of a quasi-coherent
sheaf of modules along the affine immersion `hU.fromSpec : Spec Γ(X, U) → X` is again
quasi-coherent.
This is the QC-pullback input the gap2 final close `isLocalizedModule_basicOpen` feeds to gap1
(`isIso_fromTildeΓ_of_isQuasicoherent`). -/

/-- **(Piece A, L1) The inverse slice-equivalence functor sends `unit` to `unit`.**
Dual to `overRestrictUnitIso`: the inverse functor of `overRestrictEquiv V` carries the
structure-sheaf (unit) module of the open subscheme `V.toScheme` to the unit module of the
over-site `X.ringCatSheaf.over V`. Built by transport across the equivalence: apply the inverse
functor to `(overRestrictUnitIso V).symm`, then collapse the `functor ⋙ inverse` round trip via the
unit isomorphism of the equivalence. This avoids the `unitToPushforwardObjUnit`/`IsContinuous`
coercion friction of a direct construction. Project-local. -/
noncomputable def overRestrictUnitIsoInv (V : X.Opens) :
    (overRestrictEquiv V).inverse.obj (SheafOfModules.unit V.toScheme.ringCatSheaf) ≅
      SheafOfModules.unit (X.ringCatSheaf.over V) :=
  (overRestrictEquiv V).inverse.mapIso (overRestrictUnitIso V).symm ≪≫
    (overRestrictEquiv V).unitIso.symm.app _

/-- **(Piece A, L2) Geometric presentation back-transported to a slice presentation.**
Dual to `overRestrictPresentation`: a presentation of the geometric pullback `(V.ι^*) M` yields a
presentation of the abstract Grothendieck slice `M.over V`. Transport the given presentation across
`(overRestrictPullbackIso V M).inv` (`Presentation.ofIsIso`), `Presentation.map` along the inverse
slice-equivalence functor (using `overRestrictUnitIsoInv V`), then collapse the round trip
across the
equivalence unit iso. Project-local. -/
noncomputable def overRestrictPresentationInv (V : X.Opens) (M : X.Modules)
    (P : ((Scheme.Modules.pullback V.ι).obj M).Presentation) : (M.over V).Presentation :=
  SheafOfModules.Presentation.ofIsIso.{u}
    ((overRestrictEquiv V).unitIso.symm.app (M.over V)).hom
    (SheafOfModules.Presentation.map.{u}
      (SheafOfModules.Presentation.ofIsIso.{u} (overRestrictPullbackIso V M).inv P)
      (overRestrictEquiv V).inverse (overRestrictUnitIsoInv V).symm)

/-- **(Piece A helper) Pullback along an open immersion sends `unit` to `unit`.**
For an open immersion `k : A ⟶ B`, the pullback functor `pullback k` carries the structure-sheaf
(unit) module of `B` to that of `A`. The canonical comparison `pullbackObjUnitToUnit` is an iso
because the site functor `Opens.map k.base` is `Final` — it is a right adjoint, since `k.base` is an
open map (`IsOpenMap.adjunction`). Generalizes `pullbackSchemeIsoUnitIso` from isos to open
immersions. Project-local. -/
noncomputable def pullbackOpenImmersionUnitIso {A B : Scheme.{u}} (k : A ⟶ B)
    [IsOpenImmersion k] :
    (SheafOfModules.pullback k.toRingCatSheafHom).obj (SheafOfModules.unit B.ringCatSheaf) ≅
      SheafOfModules.unit A.ringCatSheaf := by
  haveI hopen : IsOpenMap k.base := k.isOpenEmbedding.isOpenMap
  haveI : (Opens.map k.base).Final :=
    haveI : (Opens.map k.base).IsRightAdjoint := hopen.adjunction.isRightAdjoint
    inferInstance
  haveI : (SheafOfModules.pushforward (k.toRingCatSheafHom)).IsRightAdjoint := inferInstance
  exact asIso (SheafOfModules.pullbackObjUnitToUnit (k.toRingCatSheafHom))

/-- **(Piece A, L3 helper) Pseudofunctoriality iso for the preimage square.**
For an open immersion `g : Y ⟶ X`, `M` on `X`, and `U ⊆ X`, the induced open immersion
`k := g.resLE U (g ⁻¹ᵁ U)` (with `k ≫ U.ι = (g ⁻¹ᵁ U).ι ≫ g`) gives, by pseudofunctoriality of
pullback (`pullbackComp` / `pullbackCongr`), a natural iso
`(pullback k).obj ((pullback U.ι).obj M) ≅ (pullback (g ⁻¹ᵁ U).ι).obj ((pullback g).obj M)`.
Project-local. -/
noncomputable def pullbackPreimageιIso {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    (M : X.Modules) (U : X.Opens) :
    (Scheme.Modules.pullback (g.resLE U (g ⁻¹ᵁ U) le_rfl)).obj
        ((Scheme.Modules.pullback U.ι).obj M) ≅
      (Scheme.Modules.pullback (Scheme.Opens.ι (g ⁻¹ᵁ U))).obj
        ((Scheme.Modules.pullback g).obj M) :=
  (Scheme.Modules.pullbackComp (g.resLE U (g ⁻¹ᵁ U) le_rfl) U.ι).app M ≪≫
    (Scheme.Modules.pullbackCongr
      (Scheme.Hom.resLE_comp_ι g (U := U) (V := g ⁻¹ᵁ U) le_rfl)).app M ≪≫
    ((Scheme.Modules.pullbackComp (Scheme.Opens.ι (g ⁻¹ᵁ U)) g).app M).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- Heartbeat headroom for the slice-site presentation transport, as elsewhere in this file.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **(Piece A, L3) Presentation of the pullback's restriction to a preimage cover member.**
For an open immersion `g : Y ⟶ X`, `M` quasi-coherent with datum `q`, and index `i`, the geometric
restriction `(W_i.ι^*) ((pullback g).obj M)` of `N := (pullback g).obj M` to the preimage
`W_i := g ⁻¹ᵁ (q.X i)` admits a presentation. Build it by mapping the global presentation
`presentationPullbackιOfQuasicoherentData M q i` of `(q.X i).ι^* M` along the pullback
of the induced
open immersion `k := g.resLE (q.X i) W_i` (unit datum `pullbackOpenImmersionUnitIso`), then
transporting across the pseudofunctoriality iso `pullbackPreimageιIso`. Project-local. -/
noncomputable def presentationPullbackιPreimage {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    (M : X.Modules) (q : M.QuasicoherentData) (i : q.I) :
    ((Scheme.Modules.pullback (Scheme.Opens.ι (g ⁻¹ᵁ (q.X i)))).obj
        ((Scheme.Modules.pullback g).obj M)).Presentation :=
  haveI hk : IsOpenImmersion (g.resLE (q.X i) (g ⁻¹ᵁ (q.X i)) le_rfl) := by
    delta Scheme.Hom.resLE; infer_instance
  haveI : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      (Scheme.Modules.pullback (g.resLE (q.X i) (g ⁻¹ᵁ (q.X i)) le_rfl)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction _).leftAdjoint_preservesColimits
  SheafOfModules.Presentation.ofIsIso.{u}
    (pullbackPreimageιIso g M (q.X i)).hom
    (SheafOfModules.Presentation.map.{u}
      (presentationPullbackιOfQuasicoherentData M q i)
      (Scheme.Modules.pullback (g.resLE (q.X i) (g ⁻¹ᵁ (q.X i)) le_rfl))
      (pullbackOpenImmersionUnitIso (g.resLE (q.X i) (g ⁻¹ᵁ (q.X i)) le_rfl)).symm)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- Heartbeat headroom for the slice-site `HasSheafify` synthesis triggered by `over`.
set_option synthInstance.maxHeartbeats 800000 in
/-- **(Piece A, L4) The pulled-back sheaf is quasi-coherent on each preimage cover member.**
For an open immersion `g : Y ⟶ X`, `M` quasi-coherent with datum `q`, and index `i`, the abstract
Grothendieck slice `((pullback g).obj M).over (g ⁻¹ᵁ (q.X i))` is quasi-coherent: feed the geometric
presentation `presentationPullbackιPreimage` into the geometric→slice back-transport
`overRestrictPresentationInv` and apply `Presentation.isQuasicoherent`. Project-local. -/
theorem isQuasicoherent_over_preimage {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    (M : X.Modules) (q : M.QuasicoherentData) (i : q.I) :
    (((Scheme.Modules.pullback g).obj M).over (g ⁻¹ᵁ (q.X i))).IsQuasicoherent :=
  (overRestrictPresentationInv (g ⁻¹ᵁ (q.X i)) ((Scheme.Modules.pullback g).obj M)
    (presentationPullbackιPreimage g M q i)).isQuasicoherent

/-- **(Piece A, L5) The preimage family of a quasi-coherence cover covers the source.**
For a morphism `g : Y ⟶ X` and quasi-coherence datum `q` for `M` on `X` (whose cover
`{q.X i}` covers
`X`), the preimage family `{g ⁻¹ᵁ (q.X i)}` covers `Y`. Direct from the opens-topology covering
characterization: any `y ∈ W` has `g y ∈ q.X i` for some `i` (since `{q.X i}` covers `⊤`), so
`W ⊓ g ⁻¹ᵁ (q.X i)` is a neighbourhood of `y` in the sieve. Project-local. -/
theorem coversTop_preimage {Y : Scheme.{u}} (g : Y ⟶ X)
    (M : X.Modules) (q : M.QuasicoherentData) :
    (Opens.grothendieckTopology ↥Y).CoversTop (fun i => g ⁻¹ᵁ (q.X i)) := by
  intro W' y hy
  obtain ⟨U_X, _fX, hsieve, hgyU⟩ := q.coversTop ⊤ (g.base y) (by trivial)
  rw [Sieve.mem_ofObjects_iff] at hsieve
  obtain ⟨i, ⟨hUi⟩⟩ := hsieve
  refine ⟨W' ⊓ (g ⁻¹ᵁ (q.X i)), homOfLE inf_le_left, ?_, hy, ?_⟩
  · rw [Sieve.mem_ofObjects_iff]
    exact ⟨i, ⟨homOfLE inf_le_right⟩⟩
  · change g.base y ∈ q.X i
    exact leOfHom hUi hgyU

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- Heartbeat headroom for the slice-site `of_coversTop` `bind` synthesis.
set_option synthInstance.maxHeartbeats 800000 in
/-- **(Piece A, L6) Pullback of a quasi-coherent sheaf along an open immersion is quasi-coherent.**
For an open immersion `g : Y ⟶ X` and `M` quasi-coherent on `X`, the pullback
`(pullback g).obj M` is
quasi-coherent. Choose quasi-coherence data `q` for `M` (index shrunk to the site universe); the
preimage family `{g ⁻¹ᵁ (q.X i)}` covers `Y` (`coversTop_preimage`) and on each member the slice is
quasi-coherent (`isQuasicoherent_over_preimage`), so `IsQuasicoherent.of_coversTop` applies.
Project-local: Mathlib has no QC-pullback lemma. -/
theorem isQuasicoherent_pullback_of_isOpenImmersion {Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback g).obj M).IsQuasicoherent := by
  obtain ⟨q⟩ : Nonempty M.QuasicoherentData :=
    SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData
  set qs := q.shrink with hqs
  haveI : ∀ i, (((Scheme.Modules.pullback g).obj M).over (g ⁻¹ᵁ (qs.X i))).IsQuasicoherent :=
    fun i => isQuasicoherent_over_preimage g M qs i
  exact SheafOfModules.IsQuasicoherent.of_coversTop ((Scheme.Modules.pullback g).obj M)
    (fun i => g ⁻¹ᵁ (qs.X i)) (coversTop_preimage g M qs)

/-- **(Piece A, target) Quasi-coherence is preserved under pullback along `fromSpec`.**
For `M` quasi-coherent on `X` and an affine open `U`, the pullback of `M` along the affine immersion
`hU.fromSpec : Spec Γ(X, U) ⟶ X` is quasi-coherent. The `g := hU.fromSpec` instance of
`isQuasicoherent_pullback_of_isOpenImmersion` (`fromSpec` is an open immersion). This is the
QC-pullback input the gap2 close feeds to gap1. Project-local. -/
theorem isQuasicoherent_pullback_fromSpec (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) :
    ((Scheme.Modules.pullback hU.fromSpec).obj M).IsQuasicoherent :=
  isQuasicoherent_pullback_of_isOpenImmersion hU.fromSpec M

/-- **gap2 keystone (`lem:qcoh_section_localization_basicOpen`): basic-open section localization for
a quasi-coherent sheaf on an arbitrary scheme.** For `M` quasi-coherent on `X`, an affine open `U`,
and `f : Γ(X, U)`, the section restriction `Γ(M, U) → Γ(M, X.basicOpen f)` is
`IsLocalizedModule (powers f)` over `Γ(X, U)`. Assembles the QC-pullback (Piece A,
`isQuasicoherent_pullback_fromSpec`) → gap1 (`isIso_fromTildeΓ_of_isQuasicoherent`) → the eqToHom
bridge (Piece B, `isLocalizedModule_basicOpen_of_hP1`). Project-local: closes gap2. -/
theorem isLocalizedModule_basicOpen (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    [Module Γ(X, U) Γ(M, X.basicOpen f)]
    [IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)] :
    IsLocalizedModule (Submonoid.powers f) (restrictBasicOpenₗ M f) :=
  haveI := isQuasicoherent_pullback_fromSpec M hU
  isLocalizedModule_basicOpen_of_hP1 M hU
    (isIso_fromTildeΓ_of_isQuasicoherent ((Scheme.Modules.pullback hU.fromSpec).obj M)) f

/-- Restriction maps of the underlying abelian presheaf of a sheaf of modules compose:
restricting `A → B → C` equals the direct restriction `A → C`. -/
private lemma res_res (M : X.Modules) {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B)
    (hCA : C ≤ A) (x : Γ(M, A)) :
    M.presheaf.map (homOfLE hCB).op (M.presheaf.map (homOfLE hBA).op x)
      = M.presheaf.map (homOfLE hCA).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- Structure-sheaf version of `res_res`. -/
private lemma resRing_res {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B)
    (hCA : C ≤ A) (g : Γ(X, A)) :
    X.presheaf.map (homOfLE hCB).op (X.presheaf.map (homOfLE hBA).op g)
      = X.presheaf.map (homOfLE hCA).op g := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- A section of a sheaf of modules over an open contained in `⊥` vanishes (separation over
the empty cover). -/
private lemma section_eq_zero_of_le_bot (M : X.Modules) {V : X.Opens} (hV : V ≤ ⊥)
    (x : Γ(M, V)) : x = 0 :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : PEmpty.{u + 1} => i.elim) V (fun i => i.elim) (hV.trans bot_le) x 0
    (fun i => i.elim)

/-- **Torsion half of qcqs section localization** (Stacks 01P0-style, `exists_of_eq` engine).
For a quasi-coherent sheaf of modules `M` on a scheme `X`, a section `g` of the structure sheaf
over an open `W`, and a *quasi-compact* open `U ≤ W`, any section `x ∈ Γ(M, U)` that restricts
to zero on `U ⊓ D(g)` is killed by a power of `g|_U`. Induction on the compact open `U`
(`compact_open_induction_on`): the affine case is the gap2 keystone
`isLocalizedModule_basicOpen`, and the step glues by sheaf separation over the two-element
cover `{S, V}`. Project-local (Mathlib has no qcqs section-localization). -/
theorem exists_pow_smul_res_eq_zero_of_isCompact
    (M : X.Modules) [M.IsQuasicoherent] {W : X.Opens} (g : Γ(X, W))
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    ∀ (hUW : U ≤ W) (x : Γ(M, U)),
      M.presheaf.map (homOfLE (inf_le_left : U ⊓ X.basicOpen g ≤ U)).op x = 0 →
      ∃ n : ℕ, X.presheaf.map (homOfLE hUW).op g ^ n • x = 0 := by
  refine compact_open_induction_on (P := fun U => ∀ (hUW : U ≤ W) (x : Γ(M, U)),
      M.presheaf.map (homOfLE (inf_le_left : U ⊓ X.basicOpen g ≤ U)).op x = 0 →
      ∃ n : ℕ, X.presheaf.map (homOfLE hUW).op g ^ n • x = 0) U hU ?_ ?_
  · intro _ x _
    exact ⟨0, by rw [pow_zero, one_smul]; exact section_eq_zero_of_le_bot M le_rfl x⟩
  · intro S hS V IH hUW x hx
    have hSW : S ≤ W := le_sup_left.trans hUW
    have hVW : V.1 ≤ W := le_sup_right.trans hUW
    set gV : Γ(X, V.1) := X.presheaf.map (homOfLE hVW).op g with hgV
    have hB1eq : X.basicOpen gV = V.1 ⊓ X.basicOpen g := X.basicOpen_res g (homOfLE hVW).op
    set xS : Γ(M, S) := M.presheaf.map (homOfLE (le_sup_left : S ≤ S ⊔ V.1)).op x with hxS
    set xV : Γ(M, V.1) := M.presheaf.map (homOfLE (le_sup_right : V.1 ≤ S ⊔ V.1)).op x
      with hxV
    -- the restriction of `xS` to `S ⊓ D(g)` vanishes
    have hxS0 : M.presheaf.map (homOfLE (inf_le_left : S ⊓ X.basicOpen g ≤ S)).op xS = 0 := by
      have h1 := res_res M (le_sup_left : S ≤ S ⊔ V.1)
        (inf_le_left : S ⊓ X.basicOpen g ≤ S) (inf_le_left.trans le_sup_left) x
      have h2 := res_res M (inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1)
        (inf_le_inf le_sup_left le_rfl : S ⊓ X.basicOpen g ≤ (S ⊔ V.1) ⊓ X.basicOpen g)
        (inf_le_left.trans le_sup_left) x
      rw [hxS, h1, ← h2, hx, map_zero]
    obtain ⟨n₁, hn₁⟩ := IH hSW xS hxS0
    -- affine keystone on `V`
    letI : Module Γ(X, V.1) Γ(M, X.basicOpen gV) :=
      Module.compHom _ (algebraMap Γ(X, V.1) Γ(X, X.basicOpen gV))
    haveI : IsScalarTower Γ(X, V.1) Γ(X, X.basicOpen gV) Γ(M, X.basicOpen gV) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    haveI := isLocalizedModule_basicOpen M V.2 gV
    have hB1A : X.basicOpen gV ≤ (S ⊔ V.1) ⊓ X.basicOpen g :=
      hB1eq.trans_le (inf_le_inf le_sup_right le_rfl)
    have hxV0 : restrictBasicOpenₗ M gV xV = 0 := by
      have h1 := res_res M (le_sup_right : V.1 ≤ S ⊔ V.1)
        (X.basicOpen_le gV) ((X.basicOpen_le gV).trans le_sup_right) x
      have h2 := res_res M (inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1)
        hB1A ((X.basicOpen_le gV).trans le_sup_right) x
      change M.presheaf.map (homOfLE (X.basicOpen_le gV)).op xV = 0
      rw [hxV, h1, ← h2, hx, map_zero]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
      (S := Submonoid.powers gV) (f := restrictBasicOpenₗ M gV)
      (x₁ := xV) (x₂ := 0) (by rw [hxV0, map_zero])
    have hn₂ : gV ^ c.2.choose = (c : Γ(X, V.1)) := c.2.choose_spec
    have hcV : gV ^ c.2.choose • xV = 0 := by
      rw [hn₂]; rw [smul_zero] at hc; exact hc
    set n₂ := c.2.choose with hn₂def
    -- combine over the two-element cover
    refine ⟨max n₁ n₂, ?_⟩
    refine TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
      (fun b : Bool => cond b S V.1) (S ⊔ V.1)
      (fun b => homOfLE (show cond b S V.1 ≤ S ⊔ V.1 by
        cases b
        · exact le_sup_right
        · exact le_sup_left))
      (sup_le (le_iSup (fun b : Bool => cond b S V.1) true)
        (le_iSup (fun b : Bool => cond b S V.1) false))
      _ 0 ?_
    intro b
    cases b
    · -- on V
      change M.presheaf.map (homOfLE (le_sup_right : V.1 ≤ S ⊔ V.1)).op
        (X.presheaf.map (homOfLE hUW).op g ^ max n₁ n₂ • x) = M.presheaf.map _ 0
      rw [map_zero, map_smul, map_pow, resRing_res hUW le_sup_right hVW g, ← hgV,
        ← hxV, ← Nat.sub_add_cancel (le_max_right n₁ n₂), pow_add, mul_smul, hcV, smul_zero]
    · -- on S
      change M.presheaf.map (homOfLE (le_sup_left : S ≤ S ⊔ V.1)).op
        (X.presheaf.map (homOfLE hUW).op g ^ max n₁ n₂ • x) = M.presheaf.map _ 0
      rw [map_zero, map_smul, map_pow, resRing_res hUW le_sup_left hSW g, ← hxS,
        ← Nat.sub_add_cancel (le_max_left n₁ n₂), pow_add, mul_smul, hn₁, smul_zero]

/-- **Surjectivity half of qcqs section localization** (Stacks 01P0-style, `surj` engine).
For a quasi-coherent `M` on `X`, `g ∈ Γ(X, W)`, and a quasi-compact open `U ≤ W` inside the
quasi-separated open `W`, every section `y ∈ Γ(M, U ⊓ D(g))` is, after multiplication by a
power of `g`, the restriction of a section over `U`. Induction on the compact open `U`: the
affine case is the gap2 keystone's `surj`, and the step glues the two normalized candidate
sections over `{S, V}` after killing their difference on the quasi-compact overlap `S ⊓ V`
with the torsion half. Project-local. -/
theorem exists_res_eq_pow_smul_of_isCompact
    (M : X.Modules) [M.IsQuasicoherent] {W : X.Opens} (g : Γ(X, W))
    (hsep : IsQuasiSeparated (W : Set X))
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    ∀ (hUW : U ≤ W) (y : Γ(M, U ⊓ X.basicOpen g)),
      ∃ (x : Γ(M, U)) (n : ℕ),
        M.presheaf.map (homOfLE (inf_le_left : U ⊓ X.basicOpen g ≤ U)).op x
          = X.presheaf.map (homOfLE ((inf_le_left : U ⊓ X.basicOpen g ≤ U).trans hUW)).op g ^ n
            • y := by
  refine compact_open_induction_on (P := fun U => ∀ (hUW : U ≤ W)
      (y : Γ(M, U ⊓ X.basicOpen g)),
      ∃ (x : Γ(M, U)) (n : ℕ),
        M.presheaf.map (homOfLE (inf_le_left : U ⊓ X.basicOpen g ≤ U)).op x
          = X.presheaf.map (homOfLE ((inf_le_left : U ⊓ X.basicOpen g ≤ U).trans hUW)).op g ^ n
            • y) U hU ?_ ?_
  · intro _ y
    refine ⟨0, 0, ?_⟩
    rw [map_zero, pow_zero, one_smul]
    exact (section_eq_zero_of_le_bot M inf_le_left y).symm
  · intro S hS V IH hUW y
    have hSW : S ≤ W := le_sup_left.trans hUW
    have hVW : V.1 ≤ W := le_sup_right.trans hUW
    set gV : Γ(X, V.1) := X.presheaf.map (homOfLE hVW).op g with hgV
    have hB1eq : X.basicOpen gV = V.1 ⊓ X.basicOpen g := X.basicOpen_res g (homOfLE hVW).op
    have hB1W : X.basicOpen gV ≤ W := (X.basicOpen_le gV).trans hVW
    have hB1A : X.basicOpen gV ≤ (S ⊔ V.1) ⊓ X.basicOpen g :=
      hB1eq.trans_le (inf_le_inf le_sup_right le_rfl)
    -- S side: the induction hypothesis
    set yS : Γ(M, S ⊓ X.basicOpen g) :=
      M.presheaf.map (homOfLE (inf_le_inf le_sup_left le_rfl :
        S ⊓ X.basicOpen g ≤ (S ⊔ V.1) ⊓ X.basicOpen g)).op y with hyS
    obtain ⟨xS, n₁, hn₁⟩ := IH hSW yS
    -- V side: the affine keystone's surjectivity
    letI : Module Γ(X, V.1) Γ(M, X.basicOpen gV) :=
      Module.compHom _ (algebraMap Γ(X, V.1) Γ(X, X.basicOpen gV))
    haveI : IsScalarTower Γ(X, V.1) Γ(X, X.basicOpen gV) Γ(M, X.basicOpen gV) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    haveI := isLocalizedModule_basicOpen M V.2 gV
    set yV : Γ(M, X.basicOpen gV) := M.presheaf.map (homOfLE hB1A).op y with hyV
    obtain ⟨⟨xV, c⟩, hc⟩ := IsLocalizedModule.surj (S := Submonoid.powers gV)
      (f := restrictBasicOpenₗ M gV) yV
    have hn₂ : gV ^ c.2.choose = (c : Γ(X, V.1)) := c.2.choose_spec
    set n₂ := c.2.choose with hn₂def
    -- the compHom action unfolds to the restricted scalar acting through the native action
    have hc' : X.presheaf.map (homOfLE (X.basicOpen_le gV)).op (c : Γ(X, V.1)) • yV
        = M.presheaf.map (homOfLE (X.basicOpen_le gV)).op xV := hc
    have hres : X.presheaf.map (homOfLE (X.basicOpen_le gV)).op gV
        = X.presheaf.map (homOfLE hB1W).op g :=
      (congrArg (X.presheaf.map (homOfLE (X.basicOpen_le gV)).op) hgV).trans
        (resRing_res hVW (X.basicOpen_le gV) hB1W g)
    have hcV : X.presheaf.map (homOfLE hB1W).op g ^ n₂ • yV
        = M.presheaf.map (homOfLE (X.basicOpen_le gV)).op xV := by
      rw [← hc', ← hn₂, map_pow, hres]
    -- normalize both candidates to the common exponent `n = max n₁ n₂`
    set n := max n₁ n₂ with hn
    set xS' : Γ(M, S) := X.presheaf.map (homOfLE hSW).op g ^ (n - n₁) • xS with hxS'
    set xV' : Γ(M, V.1) := gV ^ (n - n₂) • xV with hxV'
    have hS' : M.presheaf.map (homOfLE (inf_le_left : S ⊓ X.basicOpen g ≤ S)).op xS'
        = X.presheaf.map (homOfLE ((inf_le_left : S ⊓ X.basicOpen g ≤ S).trans hSW)).op g ^ n
          • yS := by
      rw [hxS', map_smul, map_pow,
        resRing_res hSW (inf_le_left : S ⊓ X.basicOpen g ≤ S)
          ((inf_le_left : S ⊓ X.basicOpen g ≤ S).trans hSW) g,
        hn₁, ← mul_smul, ← pow_add, Nat.sub_add_cancel (le_max_left n₁ n₂)]
    have hV' : M.presheaf.map (homOfLE (X.basicOpen_le gV)).op xV'
        = X.presheaf.map (homOfLE hB1W).op g ^ n • yV := by
      rw [hxV', map_smul, map_pow, hres, ← hcV, ← mul_smul, ← pow_add,
        Nat.sub_add_cancel (le_max_right n₁ n₂)]
    clear_value xS' xV'
    -- the overlap `O = S ⊓ V` is quasi-compact inside the quasi-separated `W`
    have hO : IsCompact ((S ⊓ V.1 : X.Opens) : Set X) := by
      rw [TopologicalSpace.Opens.coe_inf]
      exact hsep (S : Set X) (V.1 : Set X) (fun a ha => hSW ha) S.isOpen hS
        (fun a ha => hVW ha) V.1.isOpen V.2.isCompact
    have hOW : S ⊓ V.1 ≤ W := inf_le_left.trans hSW
    -- the difference of the two normalized candidates dies on `O ⊓ D(g)` …
    set δ : Γ(M, S ⊓ V.1) :=
      M.presheaf.map (homOfLE (inf_le_left : S ⊓ V.1 ≤ S)).op xS'
        - M.presheaf.map (homOfLE (inf_le_right : S ⊓ V.1 ≤ V.1)).op xV' with hδ
    have hODB1 : (S ⊓ V.1) ⊓ X.basicOpen g ≤ X.basicOpen gV :=
      (inf_le_inf inf_le_right le_rfl).trans hB1eq.ge
    have hδ0 : M.presheaf.map
        (homOfLE (inf_le_left : (S ⊓ V.1) ⊓ X.basicOpen g ≤ S ⊓ V.1)).op δ = 0 := by
      rw [hδ, map_sub]
      have eS : M.presheaf.map
          (homOfLE (inf_le_left : (S ⊓ V.1) ⊓ X.basicOpen g ≤ S ⊓ V.1)).op
            (M.presheaf.map (homOfLE (inf_le_left : S ⊓ V.1 ≤ S)).op xS')
          = X.presheaf.map (homOfLE ((inf_le_left.trans hOW) :
              (S ⊓ V.1) ⊓ X.basicOpen g ≤ W)).op g ^ n
            • M.presheaf.map (homOfLE ((inf_le_inf inf_le_left le_rfl).trans
                (inf_le_inf le_sup_left le_rfl)) :
                (S ⊓ V.1) ⊓ X.basicOpen g ⟶ (S ⊔ V.1) ⊓ X.basicOpen g).op y := by
        rw [res_res M (inf_le_left : S ⊓ V.1 ≤ S)
          (inf_le_left : (S ⊓ V.1) ⊓ X.basicOpen g ≤ S ⊓ V.1)
          ((inf_le_inf inf_le_left le_rfl).trans inf_le_left), ← res_res M
          (inf_le_left : S ⊓ X.basicOpen g ≤ S)
          (inf_le_inf inf_le_left le_rfl :
            (S ⊓ V.1) ⊓ X.basicOpen g ≤ S ⊓ X.basicOpen g)
          ((inf_le_inf inf_le_left le_rfl).trans inf_le_left), hS', map_smul, map_pow,
          resRing_res (inf_le_left.trans hSW) (inf_le_inf inf_le_left le_rfl)
            (inf_le_left.trans hOW) g, hyS, res_res M _ _ ((inf_le_inf inf_le_left le_rfl).trans
              (inf_le_inf le_sup_left le_rfl))]
      have eV : M.presheaf.map
          (homOfLE (inf_le_left : (S ⊓ V.1) ⊓ X.basicOpen g ≤ S ⊓ V.1)).op
            (M.presheaf.map (homOfLE (inf_le_right : S ⊓ V.1 ≤ V.1)).op xV')
          = X.presheaf.map (homOfLE ((inf_le_left.trans hOW) :
              (S ⊓ V.1) ⊓ X.basicOpen g ≤ W)).op g ^ n
            • M.presheaf.map (homOfLE ((inf_le_inf inf_le_left le_rfl).trans
                (inf_le_inf le_sup_left le_rfl)) :
                (S ⊓ V.1) ⊓ X.basicOpen g ⟶ (S ⊔ V.1) ⊓ X.basicOpen g).op y := by
        rw [res_res M (inf_le_right : S ⊓ V.1 ≤ V.1)
          (inf_le_left : (S ⊓ V.1) ⊓ X.basicOpen g ≤ S ⊓ V.1)
          ((inf_le_left : (S ⊓ V.1) ⊓ X.basicOpen g ≤ S ⊓ V.1).trans inf_le_right), ← res_res M
          (X.basicOpen_le gV) hODB1
          ((inf_le_left : (S ⊓ V.1) ⊓ X.basicOpen g ≤ S ⊓ V.1).trans inf_le_right), hV',
          map_smul, map_pow,
          resRing_res hB1W hODB1 (inf_le_left.trans hOW) g, hyV,
          res_res M hB1A hODB1 ((inf_le_inf inf_le_left le_rfl).trans
            (inf_le_inf le_sup_left le_rfl))]
      rw [eS, eV, sub_self]
    -- … so a power of `g` equalizes them on the overlap (torsion half)
    obtain ⟨m, hm⟩ := exists_pow_smul_res_eq_zero_of_isCompact M g (S ⊓ V.1) hO hOW δ hδ0
    have hglue : M.presheaf.map (homOfLE (inf_le_left : S ⊓ V.1 ≤ S)).op
          (X.presheaf.map (homOfLE hSW).op g ^ m • xS')
        = M.presheaf.map (homOfLE (inf_le_right : S ⊓ V.1 ≤ V.1)).op
          (gV ^ m • xV') := by
      have h1 : X.presheaf.map (homOfLE hOW).op g ^ m
            • M.presheaf.map (homOfLE (inf_le_left : S ⊓ V.1 ≤ S)).op xS'
          - X.presheaf.map (homOfLE hOW).op g ^ m
            • M.presheaf.map (homOfLE (inf_le_right : S ⊓ V.1 ≤ V.1)).op xV' = 0 := by
        rw [← smul_sub, ← hδ]; exact hm
      have h2 := sub_eq_zero.mp h1
      have hL : M.presheaf.map (homOfLE (inf_le_left : S ⊓ V.1 ≤ S)).op
            (X.presheaf.map (homOfLE hSW).op g ^ m • xS')
          = X.presheaf.map (homOfLE hOW).op g ^ m
            • M.presheaf.map (homOfLE (inf_le_left : S ⊓ V.1 ≤ S)).op xS' := by
        rw [map_smul, map_pow, resRing_res hSW (inf_le_left : S ⊓ V.1 ≤ S) hOW g]
      have hR : M.presheaf.map (homOfLE (inf_le_right : S ⊓ V.1 ≤ V.1)).op
            (gV ^ m • xV')
          = X.presheaf.map (homOfLE hOW).op g ^ m
            • M.presheaf.map (homOfLE (inf_le_right : S ⊓ V.1 ≤ V.1)).op xV' := by
        rw [map_smul, map_pow,
          (congrArg (X.presheaf.map (homOfLE (inf_le_right : S ⊓ V.1 ≤ V.1)).op) hgV).trans
            (resRing_res hVW (inf_le_right : S ⊓ V.1 ≤ V.1) hOW g)]
      rw [hL, hR]
      exact h2
    -- compatibility of the two candidates on the overlaps
    have hcompat : TopCat.Presheaf.IsCompatible M.presheaf
        (fun b : Bool => cond b S V.1)
        (fun b => Bool.rec (motive := fun b => Γ(M, cond b S V.1))
          (gV ^ m • xV') (X.presheaf.map (homOfLE hSW).op g ^ m • xS') b) := by
      intro i j
      cases i <;> cases j
      · exact congrArg (fun (h : V.1 ⊓ V.1 ⟶ V.1) => M.presheaf.map h.op (gV ^ m • xV'))
          (Subsingleton.elim _ _)
      · -- `V` against `S`: transport `hglue` along `V ⊓ S ≤ S ⊓ V`
        change M.presheaf.map (homOfLE (inf_le_left : V.1 ⊓ S ≤ V.1)).op (gV ^ m • xV')
          = M.presheaf.map (homOfLE (inf_le_right : V.1 ⊓ S ≤ S)).op
              (X.presheaf.map (homOfLE hSW).op g ^ m • xS')
        rw [← res_res M (inf_le_right : S ⊓ V.1 ≤ V.1)
            (le_inf inf_le_right inf_le_left : V.1 ⊓ S ≤ S ⊓ V.1) inf_le_left,
          ← res_res M (inf_le_left : S ⊓ V.1 ≤ S)
            (le_inf inf_le_right inf_le_left : V.1 ⊓ S ≤ S ⊓ V.1) inf_le_right, hglue]
      · -- `S` against `V`: `hglue`
        change M.presheaf.map (homOfLE (inf_le_left : S ⊓ V.1 ≤ S)).op
              (X.presheaf.map (homOfLE hSW).op g ^ m • xS')
          = M.presheaf.map (homOfLE (inf_le_right : S ⊓ V.1 ≤ V.1)).op (gV ^ m • xV')
        exact hglue
      · exact congrArg (fun (h : S ⊓ S ⟶ S) => M.presheaf.map h.op
            (X.presheaf.map (homOfLE hSW).op g ^ m • xS'))
          (Subsingleton.elim _ _)
    -- glue the two candidates over the cover `{S, V}` of `S ⊔ V`
    obtain ⟨x', hx', -⟩ := TopCat.Sheaf.existsUnique_gluing'
      (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
      (fun b : Bool => cond b S V.1) (S ⊔ V.1)
      (fun b => homOfLE (show cond b S V.1 ≤ S ⊔ V.1 by
        cases b
        · exact le_sup_right
        · exact le_sup_left))
      (sup_le (le_iSup (fun b : Bool => cond b S V.1) true)
        (le_iSup (fun b : Bool => cond b S V.1) false))
      (fun b => Bool.rec (motive := fun b => Γ(M, cond b S V.1))
        (gV ^ m • xV') (X.presheaf.map (homOfLE hSW).op g ^ m • xS') b) hcompat
    -- the glued section is the required witness at exponent `n + m`
    refine ⟨x', n + m, ?_⟩
    have hxS'' := hx' true
    have hxV'' := hx' false
    refine TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
      (fun b : Bool => cond b (S ⊓ X.basicOpen g) (X.basicOpen gV))
      ((S ⊔ V.1) ⊓ X.basicOpen g)
      (fun b => homOfLE (show cond b (S ⊓ X.basicOpen g) (X.basicOpen gV)
          ≤ (S ⊔ V.1) ⊓ X.basicOpen g by
        cases b
        · exact hB1A
        · exact inf_le_inf le_sup_left le_rfl))
      (by
        refine le_trans (le_of_eq ?_) (sup_le
          (le_iSup (fun b : Bool => cond b (S ⊓ X.basicOpen g) (X.basicOpen gV)) true)
          (le_iSup (fun b : Bool => cond b (S ⊓ X.basicOpen g) (X.basicOpen gV)) false))
        rw [hB1eq, inf_sup_right]
        rfl)
      _ _ ?_
    intro b
    cases b
    · -- on `D(g|_V)`
      change M.presheaf.map (homOfLE hB1A).op
          (M.presheaf.map (homOfLE (inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1)).op x')
        = M.presheaf.map (homOfLE hB1A).op
          (X.presheaf.map (homOfLE ((inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1).trans
            hUW)).op g ^ (n + m) • y)
      rw [res_res M (inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1) hB1A
          ((X.basicOpen_le gV).trans le_sup_right),
        ← res_res M (le_sup_right : V.1 ≤ S ⊔ V.1) (X.basicOpen_le gV)
          ((X.basicOpen_le gV).trans le_sup_right)]
      rw [show M.presheaf.map (homOfLE (le_sup_right : V.1 ≤ S ⊔ V.1)).op x'
        = gV ^ m • xV' from hxV'']
      rw [map_smul, map_pow, hres, hV', ← mul_smul, ← pow_add, map_smul, map_pow,
        resRing_res ((inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1).trans hUW) hB1A
          hB1W g, ← hyV, Nat.add_comm m n]
    · -- on `S ⊓ D(g)`
      change M.presheaf.map (homOfLE (inf_le_inf le_sup_left le_rfl :
            S ⊓ X.basicOpen g ≤ (S ⊔ V.1) ⊓ X.basicOpen g)).op
          (M.presheaf.map (homOfLE (inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1)).op x')
        = M.presheaf.map (homOfLE (inf_le_inf le_sup_left le_rfl)).op
          (X.presheaf.map (homOfLE ((inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1).trans
            hUW)).op g ^ (n + m) • y)
      rw [res_res M (inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1)
          (inf_le_inf le_sup_left le_rfl) (inf_le_left.trans le_sup_left),
        ← res_res M (le_sup_left : S ≤ S ⊔ V.1)
          (inf_le_left : S ⊓ X.basicOpen g ≤ S) (inf_le_left.trans le_sup_left)]
      rw [show M.presheaf.map (homOfLE (le_sup_left : S ≤ S ⊔ V.1)).op x'
        = X.presheaf.map (homOfLE hSW).op g ^ m • xS' from hxS'']
      rw [map_smul, map_pow,
        resRing_res hSW (inf_le_left : S ⊓ X.basicOpen g ≤ S)
          ((inf_le_left : S ⊓ X.basicOpen g ≤ S).trans hSW) g,
        hS', ← mul_smul, ← pow_add, map_smul, map_pow,
        resRing_res ((inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1).trans hUW)
          (inf_le_inf le_sup_left le_rfl)
          ((inf_le_left : S ⊓ X.basicOpen g ≤ S).trans hSW) g, ← hyS, Nat.add_comm m n]

/-- The identity restriction acts as the identity on sections. -/
private lemma res_self (M : X.Modules) {A : X.Opens} (x : Γ(M, A)) :
    M.presheaf.map (homOfLE (le_rfl : A ≤ A)).op x = x := by
  rw [Subsingleton.elim (homOfLE (le_rfl : A ≤ A)) (𝟙 A), op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Structure-sheaf version of `res_self`. -/
private lemma resRing_self {A : X.Opens} (g : Γ(X, A)) :
    X.presheaf.map (homOfLE (le_rfl : A ≤ A)).op g = g := by
  rw [Subsingleton.elim (homOfLE (le_rfl : A ≤ A)) (𝟙 A), op_id, CategoryTheory.Functor.map_id]
  rfl

/-- If `r` maps to a unit of `S`, it acts invertibly on any module in a scalar tower
`R → S → N`. Pure algebra helper for the `map_units` field. -/
private lemma isUnit_algebraMap_end_of_isUnit_algebraMap
    {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {r : R} (h : IsUnit (algebraMap R S r)) :
    IsUnit (algebraMap R (Module.End R N) r) := by
  obtain ⟨u, hu⟩ := h
  have hcomm : ∀ (c : R) (m : N), (↑u⁻¹ : S) • c • m = c • (↑u⁻¹ : S) • m := by
    intro c m
    rw [← algebraMap_smul S c ((↑u⁻¹ : S) • m), ← mul_smul, mul_comm, mul_smul,
      algebraMap_smul S c m]
  refine isUnit_iff_exists.mpr
    ⟨{ toFun := fun m => (↑u⁻¹ : S) • m,
       map_add' := fun a b => smul_add _ a b,
       map_smul' := fun c m => by simpa using hcomm c m }, ?_, ?_⟩
  · ext m
    change algebraMap R (Module.End R N) r ((↑u⁻¹ : S) • m) = m
    rw [Module.algebraMap_end_apply, ← algebraMap_smul S r, ← hu, ← mul_smul,
      Units.mul_inv, one_smul]
  · ext m
    change (↑u⁻¹ : S) • (algebraMap R (Module.End R N) r m) = m
    rw [Module.algebraMap_end_apply, ← algebraMap_smul S r m, ← hu, ← mul_smul,
      Units.inv_mul, one_smul]

/-- **qcqs section localization** (the quasi-compact generalization of the gap2 keystone;
Stacks 01P0 / `lemma-invert-f-sections` beyond the affine case). For a quasi-coherent sheaf
of modules `M` on a scheme `X` and a *quasi-compact, quasi-separated* open `W ⊆ X`, the
section restriction `Γ(M, W) → Γ(M, D(g))` at any `g : Γ(X, W)` exhibits the target as the
localization `Γ(M, W)[1/g]` over `Γ(X, W)`. `map_units` holds because `g` restricts to a
unit of `Γ(X, D(g))` (`RingedSpace.isUnit_res_basicOpen`); `surj`/`exists_of_eq` are the
Mayer–Vietoris induction engines `exists_res_eq_pow_smul_of_isCompact` /
`exists_pow_smul_res_eq_zero_of_isCompact` instantiated at `U := W`. Project-local:
Mathlib has no qcqs section-localization at the pinned commit. -/
theorem isLocalizedModule_basicOpen_of_isCompact
    (M : X.Modules) [M.IsQuasicoherent] {W : X.Opens}
    (hW : IsCompact (W : Set X)) (hsep : IsQuasiSeparated (W : Set X))
    (g : Γ(X, W))
    [Module Γ(X, W) Γ(M, X.basicOpen g)]
    [IsScalarTower Γ(X, W) Γ(X, X.basicOpen g) Γ(M, X.basicOpen g)] :
    IsLocalizedModule (Submonoid.powers g) (restrictBasicOpenₗ M g) where
  map_units s := by
    obtain ⟨k, hk⟩ := s.2
    have hu : IsUnit (algebraMap Γ(X, W) Γ(X, X.basicOpen g) (s : Γ(X, W))) := by
      rw [← hk, map_pow]
      exact (X.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen g).pow k
    exact isUnit_algebraMap_end_of_isUnit_algebraMap hu
  surj y := by
    have hDW : X.basicOpen g ≤ W ⊓ X.basicOpen g := le_inf (X.basicOpen_le g) le_rfl
    obtain ⟨x, k, hx⟩ := exists_res_eq_pow_smul_of_isCompact M g hsep W hW le_rfl
      (M.presheaf.map (homOfLE (inf_le_right : W ⊓ X.basicOpen g ≤ X.basicOpen g)).op y)
    refine ⟨⟨x, ⟨g ^ k, k, rfl⟩⟩, ?_⟩
    have e1 : (g ^ k : Γ(X, W)) • y
        = X.presheaf.map (homOfLE (X.basicOpen_le g)).op g ^ k • y := by
      rw [← algebraMap_smul Γ(X, X.basicOpen g) (g ^ k) y, map_pow]
      rfl
    have e2 := congrArg (M.presheaf.map (homOfLE hDW).op) hx
    rw [res_res M (inf_le_left : W ⊓ X.basicOpen g ≤ W) hDW (X.basicOpen_le g) x,
      map_smul, map_pow,
      resRing_res ((inf_le_left : W ⊓ X.basicOpen g ≤ W).trans le_rfl) hDW
        (X.basicOpen_le g) g,
      res_res M (inf_le_right : W ⊓ X.basicOpen g ≤ X.basicOpen g) hDW le_rfl y,
      res_self M y] at e2
    change (g ^ k : Γ(X, W)) • y = M.presheaf.map (homOfLE (X.basicOpen_le g)).op x
    rw [e1, e2]
  exists_of_eq {x₁ x₂} h := by
    have h' := congrArg
      (M.presheaf.map (homOfLE (inf_le_right : W ⊓ X.basicOpen g ≤ X.basicOpen g)).op) h
    rw [show restrictBasicOpenₗ M g x₁
        = M.presheaf.map (homOfLE (X.basicOpen_le g)).op x₁ from rfl,
      show restrictBasicOpenₗ M g x₂
        = M.presheaf.map (homOfLE (X.basicOpen_le g)).op x₂ from rfl,
      res_res M (X.basicOpen_le g) (inf_le_right : W ⊓ X.basicOpen g ≤ X.basicOpen g)
        (inf_le_left : W ⊓ X.basicOpen g ≤ W) x₁,
      res_res M (X.basicOpen_le g) (inf_le_right : W ⊓ X.basicOpen g ≤ X.basicOpen g)
        (inf_le_left : W ⊓ X.basicOpen g ≤ W) x₂] at h'
    have h0 : M.presheaf.map (homOfLE (inf_le_left : W ⊓ X.basicOpen g ≤ W)).op
        (x₁ - x₂) = 0 := by
      rw [map_sub, h', sub_self]
    obtain ⟨k, hk⟩ := exists_pow_smul_res_eq_zero_of_isCompact M g W hW le_rfl (x₁ - x₂) h0
    rw [resRing_self g, smul_sub] at hk
    exact ⟨⟨g ^ k, k, rfl⟩, sub_eq_zero.mp hk⟩

/-- **Per-affine coherence of the annihilator family** (the `map_ideal_basicOpen` content for
`def:modules_annihilator`, `lem:modules_annihilator_ideal`). For a quasi-coherent `F`, an affine
open `V`, and `f : Γ(X, V)` with `Γ(F, V)` finitely generated over `Γ(X, V)`, the module annihilator
`Ann_{Γ(X,V)}(Γ(F,V))` maps, under the basic-open restriction `Γ(X, V) → Γ(X, D(f))`, onto
`Ann_{Γ(X,D(f))}(Γ(F,D(f)))`. This is the localized-annihilator identity
(`Module.annihilator_isLocalizedModule_eq_map`, `lem:annihilator_localization_eq_map`) transported
across the quasi-coherent basic-open section localization (gap2, `isLocalizedModule_basicOpen`,
`lem:qcoh_section_localization_basicOpen`). It is exactly the structure field
`Scheme.IdealSheafData.map_ideal_basicOpen` for the annihilator data. Project-local because
`annihilator` is. -/
lemma annihilator_map_basicOpen (F : X.Modules) [F.IsQuasicoherent]
    (V : X.affineOpens) (f : Γ(X, V.1)) [Module.Finite Γ(X, V.1) Γ(F, V.1)] :
    (Module.annihilator Γ(X, V.1) Γ(F, V.1)).map
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
      = Module.annihilator Γ(X, X.basicOpen f) Γ(F, X.basicOpen f) := by
  haveI := V.2.isLocalization_basicOpen f
  letI : Module Γ(X, V.1) Γ(F, X.basicOpen f) :=
    Module.compHom _ (algebraMap Γ(X, V.1) Γ(X, X.basicOpen f))
  haveI : IsScalarTower Γ(X, V.1) Γ(X, X.basicOpen f) Γ(F, X.basicOpen f) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI := isLocalizedModule_basicOpen F V.2 f
  exact (Module.annihilator_isLocalizedModule_eq_map (Submonoid.powers f)
    (restrictBasicOpenₗ F f)).symm

set_option backward.isDefEq.respectTransparency false in
/-- **The annihilator ideal sheaf agrees with the module annihilator on affine opens**
(`lem:modules_annihilator_ideal`). For a quasi-coherent `F` whose section module `Γ(F, V)` is
finitely generated over `Γ(X, V)` on every affine open `V` (the affine-local finiteness supplied,
for a finite-type `F`, by the G1 base case `lem:gf_qcoh_fintype_finite_sections`), the section over
an affine open `U` of the annihilator ideal sheaf equals the module annihilator of the sections:
`(annihilator F).ideal U = Ann_{Γ(X,U)}(Γ(F,U))`.

The forward inclusion `≤` is `annihilator_ideal_le` (always available from `ofIdeals`). The reverse
inclusion is genuinely *global*: `annihilator F = ofIdeals (V ↦ Ann_{Γ(X,V)}(Γ(F,V)))` is the
**largest** ideal sheaf contained in the annihilator family, and its value at `U` reaches the full
`Ann_{Γ(X,U)}(Γ(F,U))` precisely when that family is itself a coherent ideal sheaf — i.e. when it
satisfies `IdealSheafData.map_ideal_basicOpen` at *every* affine open. That coherence is
`annihilator_map_basicOpen`, which needs finite generation of `Γ(F, V)` at each `V`; hence the
`hfin` hypothesis. With it the family assembles into an honest `IdealSheafData I` whose `ideal` is
the annihilator family, and `IdealSheafData.ofIdeals_ideal` gives `ofIdeals I.ideal = I`, whence the
claim at every `U` at once. This mirrors Mathlib's `Scheme.Hom.ker_apply`, which likewise builds the
full ideal sheaf and reads off the affine value (using `QuasiCompact f` as its global hypothesis).
Project-local because `annihilator` is. -/
theorem annihilator_ideal (F : X.Modules) [F.IsQuasicoherent]
    (hfin : ∀ V : X.affineOpens, Module.Finite Γ(X, V.1) Γ(F, V.1)) (U : X.affineOpens) :
    (annihilator F).ideal U = Module.annihilator Γ(X, U.1) Γ(F, U.1) := by
  let I : X.IdealSheafData :=
    ⟨fun V => Module.annihilator Γ(X, V.1) Γ(F, V.1), ?_, _, rfl⟩
  · exact congr($(IdealSheafData.ofIdeals_ideal I).ideal U)
  · intro V f
    haveI := hfin V
    exact annihilator_map_basicOpen F V f

variable {Y : Scheme.{u}}

private lemma resRing_res_hom {A B C : Y.Opens} (hBA : B ≤ A) (i : C ⟶ B)
    (hCA : C ≤ A) (g : Γ(Y, A)) :
    Y.presheaf.map i.op (Y.presheaf.map (homOfLE hBA).op g)
      = Y.presheaf.map (homOfLE hCA).op g := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  exact congrArg (fun (k : C ⟶ A) => Y.presheaf.map k.op g) (Subsingleton.elim _ _)

/-- Additive section transport across an equality of opens, by mutual restriction. -/
private noncomputable def resAddEquivOfEq (N : Y.Modules) {A B : Y.Opens} (h : A = B) :
    Γ(N, A) ≃+ Γ(N, B) where
  toFun := N.presheaf.map (homOfLE h.ge).op
  invFun := N.presheaf.map (homOfLE h.le).op
  left_inv x := by rw [res_res N h.ge h.le le_rfl, res_self N x]
  right_inv x := by rw [res_res N h.le h.ge le_rfl, res_self N x]
  map_add' := map_add _

/-- Inverse-direction semilinearity of the pullback section transport. -/
private lemma gammaPullbackImageIso_symm_semilinear {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) (V : X.Opens) (a : Γ(X, V))
    (t : ToType Γ(M, j ''ᵁ V)) :
    (gammaPullbackImageIso j M V).addCommGroupIsoToAddEquiv.symm
        (gammaImageRingEquiv j V a • t)
      = a • (gammaPullbackImageIso j M V).addCommGroupIsoToAddEquiv.symm t := by
  apply (gammaPullbackImageIso j M V).addCommGroupIsoToAddEquiv.injective
  rw [AddEquiv.apply_symm_apply]
  exact ((gammaPullbackImageIso_hom_semilinear j M V a
    ((gammaPullbackImageIso j M V).addCommGroupIsoToAddEquiv.symm t)).trans
    (congrArg (gammaImageRingEquiv j V a • ·)
      ((gammaPullbackImageIso j M V).addCommGroupIsoToAddEquiv.apply_symm_apply t))).symm

/-- **Converse transport: section localization on the ambient scheme forces the P1 datum.**
For an affine open `U ⊆ Y` with `j = hU.fromSpec` and a sheaf of modules `N` on `Y`, if for
every `f' : Γ(Y, U)` the section restriction `Γ(N, U) → Γ(N, D(f'))` is
`IsLocalizedModule (powers f')` over `Γ(Y, U)`, then the tilde–Γ counit of the pullback
`j^* N` is an isomorphism. This is the reverse of the gap2 chain
(`section_localization_hfr_aux_general` + `isLocalizedModule_basicOpen_of_hP1` run backwards):
the `gammaPullbackImageIso` section comparisons and the `fromSpec` open identifications
(`fromSpec_image_basicOpen`, `image_top = U`) transport the localization to the `Spec`-side
sections, where the affine engine `isIso_fromTildeΓ_of_isLocalizedModule_restrict` applies.
Project-local. -/
theorem isIso_fromTildeΓ_pullback_fromSpec_of_isLocalizedModule
    (N : Y.Modules) {U : Y.Opens} (hU : IsAffineOpen U)
    (H : ∀ f' : Γ(Y, U),
      letI : Module Γ(Y, U) Γ(N, Y.basicOpen f') :=
        Module.compHom _ (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f'))
      letI : IsScalarTower Γ(Y, U) Γ(Y, Y.basicOpen f') Γ(N, Y.basicOpen f') :=
        IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
      IsLocalizedModule (Submonoid.powers f') (restrictBasicOpenₗ N f')) :
    IsIso (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pullback hU.fromSpec).obj N)) := by
  set j := hU.fromSpec with hj
  apply isIso_fromTildeΓ_of_isLocalizedModule_restrict
  intro f'
  set M' := (Scheme.Modules.pullback j).obj N with hM'
  have eT : (j ''ᵁ (⊤ : (Spec Γ(Y, U)).Opens)) = U :=
    (Scheme.Hom.image_top_eq_opensRange j).trans hU.opensRange_fromSpec
  have eB : (j ''ᵁ (PrimeSpectrum.basicOpen f')) = Y.basicOpen f' :=
    hU.fromSpec_image_basicOpen f'
  -- module instances on the ambient side
  letI : Module Γ(Y, U) Γ(N, Y.basicOpen f') :=
    Module.compHom _ (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f'))
  haveI : IsScalarTower Γ(Y, U) Γ(Y, Y.basicOpen f') Γ(N, Y.basicOpen f') :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI hloc := H f'
  -- the additive section comparisons
  let E₁ : ToType Γ(N, U) ≃+
      ToType ((modulesSpecToSheaf.obj M').presheaf.obj (.op ⊤)) :=
    ((resAddEquivOfEq N eT.symm).trans
      (gammaPullbackImageIso j N ⊤).addCommGroupIsoToAddEquiv.symm)
  let E₂ : ToType Γ(N, Y.basicOpen f') ≃+
      ToType ((modulesSpecToSheaf.obj M').presheaf.obj (.op (PrimeSpectrum.basicOpen f'))) :=
    ((resAddEquivOfEq N eB.symm).trans
      (gammaPullbackImageIso j N (PrimeSpectrum.basicOpen f')).addCommGroupIsoToAddEquiv.symm)
  -- the Spec-side restriction, R-linearly
  let h : ToType ((modulesSpecToSheaf.obj M').presheaf.obj (.op ⊤))
      →ₗ[Γ(Y, U)]
        ToType ((modulesSpecToSheaf.obj M').presheaf.obj (.op (PrimeSpectrum.basicOpen f'))) :=
    ((modulesSpecToSheaf.obj M').presheaf.map
      (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)).op).hom
  -- semilinearity (over the identity of `Γ(Y, U)`)
  -- the top-level coherence: `Y`-restriction `U → j''ᵁ⊤` matches the ring comparison
  have C1 : ∀ a : Γ(Y, U), Y.presheaf.map (homOfLE eT.le).op a
      = (gammaImageRingEquiv j ⊤) ((Scheme.ΓSpecIso Γ(Y, U)).inv a) := by
    intro a
    have hcoh := fromSpec_image_top_section_coherence hU eT
    have happ := congrArg (fun (φ : Γ(Y, j ''ᵁ (⊤ : (Spec Γ(Y, U)).Opens)) ⟶ Γ(Y, U)) =>
      φ.hom (Y.presheaf.map (homOfLE eT.le).op a)) hcoh
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at happ
    have hres : (Y.presheaf.map (eqToHom eT.symm).op).hom
        (Y.presheaf.map (homOfLE eT.le).op a) = a := by
      rw [Subsingleton.elim (eqToHom eT.symm) (homOfLE eT.ge)]
      change Y.presheaf.map (homOfLE eT.ge).op (Y.presheaf.map (homOfLE eT.le).op a) = a
      rw [resRing_res eT.le eT.ge le_rfl a, resRing_self a]
    rw [hres] at happ
    -- happ : a = ΓSpecIso.hom (appIso.hom (res a))
    refine (gammaImageRingEquiv j ⊤).symm.injective ?_
    rw [RingEquiv.symm_apply_apply]
    refine (Scheme.ΓSpecIso Γ(Y, U)).commRingCatIsoToRingEquiv.injective ?_
    have hcancel := congrArg (fun (φ : Γ(Y, U) ⟶ Γ(Y, U)) => φ.hom a)
      (Scheme.ΓSpecIso Γ(Y, U)).inv_hom_id
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] at hcancel
    change (Scheme.ΓSpecIso Γ(Y, U)).hom.hom ((j.appIso ⊤).hom.hom
        (Y.presheaf.map (homOfLE eT.le).op a))
      = (Scheme.ΓSpecIso Γ(Y, U)).hom.hom ((Scheme.ΓSpecIso Γ(Y, U)).inv.hom a)
    rw [← happ, hcancel]
  have he₁ : ∀ (a : Γ(Y, U)) (x : ToType Γ(N, U)),
      E₁ (a • x) = a • E₁ x := by
    intro a x
    simp only [E₁, AddEquiv.trans_apply]
    have hN : (N.resAddEquivOfEq eT.symm) (a • x)
        = (gammaImageRingEquiv j ⊤) ((Scheme.ΓSpecIso Γ(Y, U)).inv a)
          • (N.resAddEquivOfEq eT.symm) x := by
      change N.presheaf.map (homOfLE eT.le).op (a • x)
        = _ • N.presheaf.map (homOfLE eT.le).op x
      rw [Scheme.Modules.map_smul N (homOfLE eT.le) a x, C1 a]
    rw [hN]
    exact gammaPullbackImageIso_symm_semilinear j N ⊤ ((Scheme.ΓSpecIso Γ(Y, U)).inv a) _
  have hjDU : (j ''ᵁ (PrimeSpectrum.basicOpen f')) ≤ U := eB.trans_le (Y.basicOpen_le f')
  have hsub : (j.opensFunctor.map (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)))
      = homOfLE (leOfHom (j.opensFunctor.map (homOfLE le_top))) := Subsingleton.elim _ _
  have C2 : ∀ a : Γ(Y, U), Y.presheaf.map (homOfLE hjDU).op a
      = (gammaImageRingEquiv j (PrimeSpectrum.basicOpen f'))
          ((Spec Γ(Y, U)).presheaf.map (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)).op
            ((Scheme.ΓSpecIso Γ(Y, U)).inv a)) := by
    intro a
    have key0 := j.appIso_inv_naturality (U := (⊤ : (Spec Γ(Y, U)).Opens))
      (V := PrimeSpectrum.basicOpen f') (homOfLE le_top).op
    have key : (gammaImageRingEquiv j (PrimeSpectrum.basicOpen f'))
        ((Spec Γ(Y, U)).presheaf.map (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)).op
          ((Scheme.ΓSpecIso Γ(Y, U)).inv a))
        = (Y.presheaf.map (j.opensFunctor.map (homOfLE le_top)).op).hom
          ((gammaImageRingEquiv j ⊤) ((Scheme.ΓSpecIso Γ(Y, U)).inv a)) :=
      congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso Γ(Y, U)).inv a)) key0
    rw [key, ← C1 a]
    exact (resRing_res_hom eT.le (j.opensFunctor.map (homOfLE le_top)) hjDU a).symm
  have he₂ : ∀ (a : Γ(Y, U)) (x : ToType Γ(N, Y.basicOpen f')),
      E₂ (a • x) = a • E₂ x := by
    intro a x
    simp only [E₂, AddEquiv.trans_apply]
    have hN : (N.resAddEquivOfEq eB.symm) (a • x)
        = (gammaImageRingEquiv j (PrimeSpectrum.basicOpen f'))
            ((Spec Γ(Y, U)).presheaf.map
              (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)).op
              ((Scheme.ΓSpecIso Γ(Y, U)).inv a))
          • (N.resAddEquivOfEq eB.symm) x := by
      change N.presheaf.map (homOfLE eB.le).op
          ((Y.presheaf.map (homOfLE (Y.basicOpen_le f')).op a) • x)
        = _ • N.presheaf.map (homOfLE eB.le).op x
      rw [Scheme.Modules.map_smul N (homOfLE eB.le), resRing_res (Y.basicOpen_le f')
        eB.le hjDU a, C2 a]
    rw [hN]
    exact gammaPullbackImageIso_symm_semilinear j N (PrimeSpectrum.basicOpen f')
      ((Spec Γ(Y, U)).presheaf.map (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)).op
        ((Scheme.ΓSpecIso Γ(Y, U)).inv a)) _
  -- intertwining
  have hh : ∀ x, h (E₁ x) = E₂ (restrictBasicOpenₗ N f' x) := by
    intro x
    apply (gammaPullbackImageIso j N
      (PrimeSpectrum.basicOpen f')).addCommGroupIsoToAddEquiv.injective
    have hn := ConcreteCategory.congr_hom
      (gammaPullbackImageIso_hom_naturality j N
        (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)))
      (((gammaPullbackImageIso j N ⊤).addCommGroupIsoToAddEquiv.symm
        ((N.resAddEquivOfEq eT.symm) x)))
    simp only [CategoryTheory.comp_apply] at hn
    -- LHS: naturality then the unit-cancellation of `gamma ∘ gamma.symm`
    have hL : (gammaPullbackImageIso j N
        (PrimeSpectrum.basicOpen f')).addCommGroupIsoToAddEquiv (h (E₁ x))
        = N.presheaf.map (homOfLE (leOfHom (j.opensFunctor.map
            (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤))))).op
          ((N.resAddEquivOfEq eT.symm) x) := by
      refine hn.trans ?_
      rw [hsub]
      exact congrArg _ ((gammaPullbackImageIso j
        N ⊤).addCommGroupIsoToAddEquiv.apply_symm_apply _)
    have hR : (gammaPullbackImageIso j N
        (PrimeSpectrum.basicOpen f')).addCommGroupIsoToAddEquiv
          (E₂ (restrictBasicOpenₗ N f' x))
        = (N.resAddEquivOfEq eB.symm) (restrictBasicOpenₗ N f' x) := by
      simp only [E₂, AddEquiv.trans_apply]
      exact (gammaPullbackImageIso j N
        (PrimeSpectrum.basicOpen f')).addCommGroupIsoToAddEquiv.apply_symm_apply _
    rw [hL, hR]
    change N.presheaf.map (homOfLE (leOfHom (j.opensFunctor.map
          (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤))))).op
        (N.presheaf.map (homOfLE eT.le).op x)
      = N.presheaf.map (homOfLE eB.le).op
        (N.presheaf.map (homOfLE (Y.basicOpen_le f')).op x)
    exact (res_res N eT.le (leOfHom (j.opensFunctor.map (homOfLE le_top))) hjDU x).trans
      (res_res N (Y.basicOpen_le f') eB.le hjDU x).symm
  have RESULT : IsLocalizedModule
      ((Submonoid.powers f').map ((RingEquiv.refl Γ(Y, U)) : Γ(Y, U) →+* Γ(Y, U))) h :=
    isLocalizedModule_of_ringEquiv_semilinear (RingEquiv.refl Γ(Y, U))
      (Submonoid.powers f') (restrictBasicOpenₗ N f') E₁ E₂ he₁ he₂ h hh
  have key : (Submonoid.powers f').map ((RingEquiv.refl Γ(Y, U)) : Γ(Y, U) →+* Γ(Y, U))
      = Submonoid.powers f' := by
    rw [Submonoid.map_powers]
    rfl
  rw [key] at RESULT
  exact RESULT

/-- Module version of `resRing_res_hom`: composite of a `homOfLE`-restriction with an
arbitrary poset hom collapses to the direct restriction. -/
private lemma res_res_hom (N : Y.Modules) {A B C : Y.Opens} (hBA : B ≤ A) (i : C ⟶ B)
    (hCA : C ≤ A) (x : Γ(N, A)) :
    N.presheaf.map i.op (N.presheaf.map (homOfLE hBA).op x)
      = N.presheaf.map (homOfLE hCA).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  exact congrArg (fun (k : C ⟶ A) => N.presheaf.map k.op x) (Subsingleton.elim _ _)

/-- Restriction along an arbitrary poset hom equals restriction along `homOfLE`. -/
private lemma res_hom_eq_res (N : Y.Modules) {A B : Y.Opens} (i : B ⟶ A) (x : Γ(N, A)) :
    N.presheaf.map i.op x = N.presheaf.map (homOfLE (leOfHom i)).op x :=
  congrArg (fun (k : B ⟶ A) => N.presheaf.map k.op x) (Subsingleton.elim _ _)

private lemma resRing_hom_eq_res {A B : Y.Opens} (i : B ⟶ A) (g : Γ(Y, A)) :
    Y.presheaf.map i.op g = Y.presheaf.map (homOfLE (leOfHom i)).op g :=
  congrArg (fun (k : B ⟶ A) => Y.presheaf.map k.op g) (Subsingleton.elim _ _)


/-- **Pushforward-level basic-open section localization.** For a quasi-compact
quasi-separated `π : X ⟶ S`, a quasi-coherent `F` on `X`, and an affine open `U ⊆ S`, the
section restriction of the pushforward `Γ(π_*F, U) → Γ(π_*F, D(f'))` at any `f' : Γ(S, U)` is
a localization at `powers f'` over `Γ(S, U)`. The qcqs section-localization engine
`isLocalizedModule_basicOpen_of_isCompact` applies on `X` at `g = π♯ f'` over the compact
quasi-separated preimage `π ⁻¹ᵁ U`, and `π ⁻¹ᵁ D_S(f') = D_X(g)` (`preimage_basicOpen`)
identifies the two restriction maps. Project-local (the sheaf-level heart of Stacks 01XJ). -/
theorem isLocalizedModule_basicOpen_pushforward
    {X S : Scheme.{u}} (π : X ⟶ S) [QuasiCompact π] [QuasiSeparated π]
    (F : X.Modules) [F.IsQuasicoherent]
    {U : S.Opens} (hU : IsAffineOpen U) (f' : Γ(S, U)) :
    letI : Module Γ(S, U) Γ((Scheme.Modules.pushforward π).obj F, S.basicOpen f') :=
      Module.compHom _ (algebraMap Γ(S, U) Γ(S, S.basicOpen f'))
    letI : IsScalarTower Γ(S, U) Γ(S, S.basicOpen f')
        Γ((Scheme.Modules.pushforward π).obj F, S.basicOpen f') :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    IsLocalizedModule (Submonoid.powers f')
      (restrictBasicOpenₗ ((Scheme.Modules.pushforward π).obj F) f') := by
  letI : Module Γ(S, U) Γ((Scheme.Modules.pushforward π).obj F, S.basicOpen f') :=
    Module.compHom _ (algebraMap Γ(S, U) Γ(S, S.basicOpen f'))
  letI : IsScalarTower Γ(S, U) Γ(S, S.basicOpen f')
      Γ((Scheme.Modules.pushforward π).obj F, S.basicOpen f') :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have hW : IsCompact ((π ⁻¹ᵁ U : X.Opens) : Set X) :=
    π.isCompact_preimage hU.isCompact
  have hsep : IsQuasiSeparated ((π ⁻¹ᵁ U : X.Opens) : Set X) :=
    π.isQuasiSeparated_preimage hU.isQuasiSeparated
  set g : Γ(X, π ⁻¹ᵁ U) := π.app U f' with hg
  letI : Module Γ(X, π ⁻¹ᵁ U) Γ(F, X.basicOpen g) :=
    Module.compHom _ (algebraMap Γ(X, π ⁻¹ᵁ U) Γ(X, X.basicOpen g))
  haveI : IsScalarTower Γ(X, π ⁻¹ᵁ U) Γ(X, X.basicOpen g) Γ(F, X.basicOpen g) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI hXloc := isLocalizedModule_basicOpen_of_isCompact F hW hsep g
  have hpre : π ⁻¹ᵁ (S.basicOpen f') = X.basicOpen g := Scheme.preimage_basicOpen π f'
  have hle : π ⁻¹ᵁ (S.basicOpen f') ≤ π ⁻¹ᵁ U := hpre.le.trans (X.basicOpen_le g)
  -- ring coherence: restricting `π♯ f'` matches `π♯` of the restriction
  have hring : X.presheaf.map (homOfLE hle).op g
      = π.app (S.basicOpen f') (algebraMap Γ(S, U) Γ(S, S.basicOpen f') f') := by
    change X.presheaf.map (homOfLE hle).op g
      = π.app (S.basicOpen f') (S.presheaf.map (homOfLE (S.basicOpen_le f')).op f')
    have hnat := congrArg
      (fun (φ : Γ(S, U) ⟶ Γ(X, π ⁻¹ᵁ (S.basicOpen f'))) => φ.hom f')
      (π.naturality (homOfLE (S.basicOpen_le f')).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
    rw [hg]
    refine Eq.trans ?_ hnat.symm
    exact (resRing_hom_eq_res ((Opens.map π.base).map (homOfLE (S.basicOpen_le f')))
      (π.app U f')).symm
  refine ⟨?_, ?_, ?_⟩
  · -- map_units
    intro s
    obtain ⟨k, hk⟩ := s.2
    have hu : IsUnit (algebraMap Γ(S, U) Γ(S, S.basicOpen f') (s : Γ(S, U))) := by
      rw [← hk, map_pow]
      exact (S.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen f').pow k
    exact isUnit_algebraMap_end_of_isUnit_algebraMap hu
  · -- surj
    intro y
    let yF : ToType Γ(F, π ⁻¹ᵁ (S.basicOpen f')) := y
    obtain ⟨⟨x, c⟩, hc⟩ := IsLocalizedModule.surj (S := Submonoid.powers g)
      (f := restrictBasicOpenₗ F g) (F.presheaf.map (homOfLE hpre.ge).op yF)
    have hk : g ^ c.2.choose = (c : Γ(X, π ⁻¹ᵁ U)) := c.2.choose_spec
    refine ⟨⟨x, ⟨f' ^ c.2.choose, c.2.choose, rfl⟩⟩, ?_⟩
    -- push `hc` back along the opens identity `π ⁻¹ᵁ D_S(f') = D_X(g)`
    have hc0 : (c : Γ(X, π ⁻¹ᵁ U)) • (F.presheaf.map (homOfLE hpre.ge).op yF)
        = restrictBasicOpenₗ F g x := hc
    have hc' := congrArg (F.presheaf.map (homOfLE hpre.le).op) hc0
    -- expand the compHom action of `c` on the `X`-side
    have hcL : F.presheaf.map (homOfLE hpre.le).op
        ((c : Γ(X, π ⁻¹ᵁ U)) • (F.presheaf.map (homOfLE hpre.ge).op yF))
        = (X.presheaf.map (homOfLE hle).op (c : Γ(X, π ⁻¹ᵁ U))) • yF := by
      change F.presheaf.map (homOfLE hpre.le).op
          ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op (c : Γ(X, π ⁻¹ᵁ U)))
            • (F.presheaf.map (homOfLE hpre.ge).op yF))
        = (X.presheaf.map (homOfLE hle).op (c : Γ(X, π ⁻¹ᵁ U))) • yF
      rw [Scheme.Modules.map_smul F (homOfLE hpre.le),
        resRing_res (X.basicOpen_le g) hpre.le hle (c : Γ(X, π ⁻¹ᵁ U)),
        res_res F hpre.ge hpre.le le_rfl yF, res_self F yF]
    have hcR : F.presheaf.map (homOfLE hpre.le).op (restrictBasicOpenₗ F g x)
        = F.presheaf.map (homOfLE hle).op x := by
      change F.presheaf.map (homOfLE hpre.le).op
          (F.presheaf.map (homOfLE (X.basicOpen_le g)).op x)
        = F.presheaf.map (homOfLE hle).op x
      exact res_res F (X.basicOpen_le g) hpre.le hle x
    rw [hcL, hcR] at hc'
    -- identify with the pushforward-side statement
    change (f' ^ c.2.choose : Γ(S, U)) • y
      = ((Scheme.Modules.pushforward π).obj F).presheaf.map
          (homOfLE (S.basicOpen_le f')).op x
    have hact : (f' ^ c.2.choose : Γ(S, U)) • y
        = (X.presheaf.map (homOfLE hle).op (c : Γ(X, π ⁻¹ᵁ U))) • yF := by
      change (π.app (S.basicOpen f')
          (algebraMap Γ(S, U) Γ(S, S.basicOpen f') (f' ^ c.2.choose))) • yF
        = (X.presheaf.map (homOfLE hle).op (c : Γ(X, π ⁻¹ᵁ U))) • yF
      rw [map_pow, map_pow, ← hring, ← map_pow]
      exact congrArg (fun t => (X.presheaf.map (homOfLE hle).op t) • yF) hk
    rw [hact, hc']
    exact (show ((Scheme.Modules.pushforward π).obj F).presheaf.map
        (homOfLE (S.basicOpen_le f')).op x = F.presheaf.map (homOfLE hle).op x from
      res_hom_eq_res F ((Opens.map π.base).map (homOfLE (S.basicOpen_le f'))) x).symm
  · -- exists_of_eq
    intro x₁ x₂ h
    have h' : F.presheaf.map (homOfLE hle).op x₁ = F.presheaf.map (homOfLE hle).op x₂ := by
      have e1 : ((Scheme.Modules.pushforward π).obj F).presheaf.map
          (homOfLE (S.basicOpen_le f')).op x₁ = F.presheaf.map (homOfLE hle).op x₁ :=
        res_hom_eq_res F ((Opens.map π.base).map (homOfLE (S.basicOpen_le f'))) x₁
      have e2 : ((Scheme.Modules.pushforward π).obj F).presheaf.map
          (homOfLE (S.basicOpen_le f')).op x₂ = F.presheaf.map (homOfLE hle).op x₂ :=
        res_hom_eq_res F ((Opens.map π.base).map (homOfLE (S.basicOpen_le f'))) x₂
      exact e1.symm.trans (h.trans e2)
    have h'' : restrictBasicOpenₗ F g x₁ = restrictBasicOpenₗ F g x₂ := by
      change F.presheaf.map (homOfLE (X.basicOpen_le g)).op x₁
        = F.presheaf.map (homOfLE (X.basicOpen_le g)).op x₂
      have r1 := res_res F hle hpre.ge (X.basicOpen_le g) x₁
      have r2 := res_res F hle hpre.ge (X.basicOpen_le g) x₂
      rw [← r1, ← r2, h']
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
      (S := Submonoid.powers g) (f := restrictBasicOpenₗ F g) h''
    have hk : g ^ c.2.choose = (c : Γ(X, π ⁻¹ᵁ U)) := c.2.choose_spec
    refine ⟨⟨f' ^ c.2.choose, c.2.choose, rfl⟩, ?_⟩
    let xF₁ : ToType Γ(F, π ⁻¹ᵁ U) := x₁
    let xF₂ : ToType Γ(F, π ⁻¹ᵁ U) := x₂
    change (π.app U (f' ^ c.2.choose)) • xF₁ = (π.app U (f' ^ c.2.choose)) • xF₂
    rw [map_pow]
    change (g : Γ(X, π ⁻¹ᵁ U)) ^ c.2.choose • xF₁ = g ^ c.2.choose • xF₂
    rw [hk]
    exact hc

/-- The family of all affine opens covers a scheme (for the opens Grothendieck topology). -/
private theorem coversTop_affineOpens (S : Scheme.{u}) :
    (Opens.grothendieckTopology ↥S).CoversTop
      (fun U : S.affineOpens => U.1) := by
  intro W y hy
  obtain ⟨V, hVaff, hyV, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens S) hy
  refine ⟨V, homOfLE hVW, ?_, hyV⟩
  rw [CategoryTheory.Sieve.mem_ofObjects_iff]
  exact ⟨⟨V, hVaff⟩, ⟨𝟙 V⟩⟩

set_option maxHeartbeats 1600000 in
-- The affine pushforward slice proof combines localization with the tilde counit transport.
set_option synthInstance.maxHeartbeats 800000 in
/-- **Per-affine slice quasi-coherence of a qcqs pushforward.** For qcqs `π : X ⟶ S`, `F`
quasi-coherent on `X`, and an affine open `U ⊆ S`, the slice `(π_* F).over U` is
quasi-coherent: the pushforward-level section localization
(`isLocalizedModule_basicOpen_pushforward`) feeds the converse transport
(`isIso_fromTildeΓ_pullback_fromSpec_of_isLocalizedModule`) to produce the P1 datum, whose
tilde presentation transports along `U.ι = isoSpec.hom ≫ fromSpec` back to the geometric
restriction and then to the slice (`overRestrictPresentationInv`). Project-local. -/
theorem pushforward_isQuasicoherent_over_affine
    {X S : Scheme.{u}} (π : X ⟶ S) [QuasiCompact π] [QuasiSeparated π]
    (F : X.Modules) [F.IsQuasicoherent] {U : S.Opens} (hU : IsAffineOpen U) :
    (((Scheme.Modules.pushforward π).obj F).over U).IsQuasicoherent := by
  set N := (Scheme.Modules.pushforward π).obj F with hN
  haveI hP1 : IsIso (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pullback hU.fromSpec).obj N)) :=
    isIso_fromTildeΓ_pullback_fromSpec_of_isLocalizedModule N hU
      (fun f' => isLocalizedModule_basicOpen_pushforward π F hU f')
  -- global presentation of the `fromSpec`-pullback, via the tilde presentation
  let eT' : tilde ((modulesSpecToSheaf.obj
        ((Scheme.Modules.pullback hU.fromSpec).obj N)).presheaf.obj (Opposite.op ⊤))
      ≅ (Scheme.Modules.pullback hU.fromSpec).obj N :=
    @asIso _ _ _ _
      (Scheme.Modules.fromTildeΓ ((Scheme.Modules.pullback hU.fromSpec).obj N)) hP1
  have P_M' : ((Scheme.Modules.pullback hU.fromSpec).obj N).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{u} eT'.hom
      (AlgebraicGeometry.presentationTilde.{u} _ Set.univ (by simp) _ (Submodule.span_eq _))
  -- transport along `U.ι = isoSpec.hom ≫ fromSpec`
  have hcomp : hU.isoSpec.hom ≫ hU.fromSpec = U.ι := by
    rw [← hU.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have P_ι : ((Scheme.Modules.pullback U.ι).obj N).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{u, u, u}
      ((Scheme.Modules.pullbackComp hU.isoSpec.hom hU.fromSpec).app N ≪≫
        (Scheme.Modules.pullbackCongr hcomp).app N).hom
      (presentationPullbackOfSchemeIso hU.isoSpec.symm
        ((Scheme.Modules.pullback hU.fromSpec).obj N) P_M')
  exact (Scheme.Modules.overRestrictPresentationInv U N P_ι).isQuasicoherent

set_option maxHeartbeats 1600000 in
-- Cover-wise quasi-coherence assembly synthesizes the affine-slice sheafification data.
set_option synthInstance.maxHeartbeats 800000 in
/-- **Pushforward preserves quasi-coherence** (Stacks tag 01XJ). For a quasi-compact
quasi-separated morphism of schemes `π : X ⟶ S` and a quasi-coherent sheaf of modules `F` on
`X`, the pushforward `π_* F` is quasi-coherent. Quasi-coherence is checked on the affine-opens
cover of `S` (`IsQuasicoherent.of_coversTop`), where the slice statement is
`pushforward_isQuasicoherent_over_affine`. Project-local (Mathlib gap at the pinned commit). -/
theorem pushforward_isQuasicoherent
    {X S : Scheme.{u}} (π : X ⟶ S) [QuasiCompact π] [QuasiSeparated π]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward π).obj F).IsQuasicoherent := by
  haveI : ∀ U : S.affineOpens,
      (((Scheme.Modules.pushforward π).obj F).over U.1).IsQuasicoherent :=
    fun U => pushforward_isQuasicoherent_over_affine π F U.2
  exact SheafOfModules.IsQuasicoherent.of_coversTop
    ((Scheme.Modules.pushforward π).obj F)
    (fun U : S.affineOpens => U.1) (coversTop_affineOpens S)

end Scheme.Modules

end BasicOpenPresentationDescent

end AlgebraicGeometry


/-! ============================================================================
  RELOCATED LANE F BLOCK (2026-07-03, T12 session)

  The Lane F affine-section-formula chain (`pullback_tildeIso`,
  `tildeIso_of_isQuasicoherent_isAffineOpen`, `pullback_of_openImmersion_iso_restrict`,
  `pullback_app_isoTensor*`, `canonicalBaseChangeMap_*`, `flatBaseChangeCohomology`)
  was moved below the GR-quot union-merge machinery so that it can consume the
  sorry-free gap1/gap2 substrate (`Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`,
  `Scheme.Modules.isQuasicoherent_pullback_fromSpec`, ...) which is declared there.
  Nothing below the union-merge banner references this block, so the relocation is
  order-safe; the declarations are otherwise verbatim.
============================================================================ -/

namespace AlgebraicGeometry

/-! #### Substrate for `pullback_tildeIso` (Stacks 01HQ): adjoint-uniqueness route.

The Spec-level "pullback of tilde = tilde of base change" identification is
proved by uniqueness of left adjoints: both `tilde.functor A ⋙ pullback (Spec.map φ)`
and `extendScalars φ ⋙ tilde.functor B` are left adjoint to "global sections as an
`A`-module" — the first via `tilde.adjunction ∘ pullbackPushforwardAdjunction`, the
second via `extendRestrictScalarsAdj ∘ tilde.adjunction` — once the two right adjoints
`pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor` and
`moduleSpecΓFunctor ⋙ restrictScalars φ` are identified (`pullbackTilde_gammaBridge`:
on carriers this is restriction along the equality of opens `⊤ = (Spec.map φ) ⁻¹ᵁ ⊤`;
the `A`-action match is `ΓSpecIso_inv_naturality`). The Σ-pair section-level identity
is then the unit-compatibility `Adjunction.unit_leftAdjointUniq_hom_app`, which the
elaborator checks by definitional unfolding of both composed adjunction units
(`toOpen`/`1 ⊗ₜ ·` on the two sides). -/

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of a sheaf-of-modules along `⊤ ≤ g ⁻¹ᵁ ⊤` (an equality of opens) is
the identity: the hom `homOfLE e : ⊤ ⟶ g ⁻¹ᵁ ⊤` is definitionally `𝟙 ⊤` by proof
irrelevance since `g ⁻¹ᵁ ⊤` is definitionally `⊤`. -/
private lemma modules_restr_preimage_top_eq_id {X Y : Scheme.{u}} (g : Y ⟶ X)
    (N : Y.Modules) (e : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ ⊤) :
    N.presheaf.map (homOfLE e).op = 𝟙 _ :=
  (congrArg N.presheaf.map
    (show (homOfLE e).op = 𝟙 (Opposite.op (⊤ : Y.Opens)) from rfl)).trans
    (N.presheaf.map_id _)

set_option backward.isDefEq.respectTransparency false in
/-- Ring-sheaf analogue of `modules_restr_preimage_top_eq_id`. -/
private lemma ring_restr_preimage_top_eq_id {X Y : Scheme.{u}} (g : Y ⟶ X)
    (e : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ ⊤) :
    Y.presheaf.map (homOfLE e).op = 𝟙 _ :=
  (congrArg Y.presheaf.map
    (show (homOfLE e).op = 𝟙 (Opposite.op (⊤ : Y.Opens)) from rfl)).trans
    (Y.presheaf.map_id _)

set_option backward.isDefEq.respectTransparency false in
/-- Component hom of `pullbackTilde_gammaBridge`: restriction of global sections along
`⊤ ≤ (Spec.map φ) ⁻¹ᵁ ⊤` (an equality of opens), bridging `Γ_A(π_* N)` (with the
`A`-action through `π♯`) and `Γ_B(N)` (with the `A`-action through `φ`). `A`-linearity
is `Scheme.Modules.map_smul` plus `ΓSpecIso_inv_naturality`. -/
private noncomputable def pullbackTilde_gammaBridgeHom {A B : CommRingCat.{u}}
    (φ : A ⟶ B) (N : (Spec B).Modules) :
    (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := ↑A)).obj N ⟶
      (moduleSpecΓFunctor (R := ↑B) ⋙ ModuleCat.restrictScalars φ.hom).obj N :=
  ConcreteCategory.ofHom
    { toFun := fun x =>
        (N.presheaf.map (homOfLE (le_top :
          (⊤ : (Spec B).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤)).op).hom x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x =>
        (Scheme.Modules.map_smul N (homOfLE (le_top :
            (⊤ : (Spec B).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤))
          (((Spec.map φ).app ⊤).hom ((Scheme.ΓSpecIso A).inv.hom a)) x).trans
        (congrArg (fun r => r • (N.presheaf.map (homOfLE (le_top :
            (⊤ : (Spec B).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤)).op).hom x)
          ((congrArg (fun (k : Γ(Spec B, Spec.map φ ⁻¹ᵁ ⊤) ⟶ Γ(Spec B, ⊤)) =>
              k.hom (((Spec.map φ).app ⊤).hom ((Scheme.ΓSpecIso A).inv.hom a)))
            (ring_restr_preimage_top_eq_id (Spec.map φ) le_top)).trans
           ((congrArg (fun (ψ : A ⟶ Γ(Spec B, ⊤)) => ψ.hom a)
              (Scheme.ΓSpecIso_inv_naturality φ)).symm))) }

set_option backward.isDefEq.respectTransparency false in
private lemma pullbackTilde_gammaBridgeHom_isIso {A B : CommRingCat.{u}}
    (φ : A ⟶ B) (N : (Spec B).Modules) : IsIso (pullbackTilde_gammaBridgeHom φ N) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (fun x => (N.presheaf.map (homOfLE (le_top :
    (⊤ : (Spec B).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤)).op).hom x)
  rw [modules_restr_preimage_top_eq_id (Spec.map φ) N le_top]
  exact Function.bijective_id

set_option backward.isDefEq.respectTransparency false in
/-- The right adjoints of the two composed adjunctions agree: global sections of the
pushforward along `Spec.map φ` (as an `A`-module via `π♯`) is naturally isomorphic to
global sections restricted along `φ`. This is the bridge that makes
`tilde.functor A ⋙ pullback (Spec.map φ)` and `extendScalars φ.hom ⋙ tilde.functor B`
left adjoints of the SAME functor. -/
private noncomputable def pullbackTilde_gammaBridge {A B : CommRingCat.{u}}
    (φ : A ⟶ B) :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := ↑A)
      ≅ moduleSpecΓFunctor (R := ↑B) ⋙ ModuleCat.restrictScalars φ.hom := by
  refine NatIso.ofComponents
    (fun N => @asIso _ _ _ _ _ (pullbackTilde_gammaBridgeHom_isIso φ N))
    (fun {N N'} h => ?_)
  ext x
  exact (congrArg (fun (k : Γ(N, Spec.map φ ⁻¹ᵁ ⊤) ⟶ Γ(N', ⊤)) => k.hom x)
    ((Scheme.Modules.Hom.mapPresheaf h).naturality (homOfLE (le_top :
      (⊤ : (Spec B).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤)).op)).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- The Spec pullback formula normalizes tensor, tilde, and pullback comparison isomorphisms.
/-- **Spec-level pullback-of-tilde formula** (iter-187 Lane F NAMED HELPER,
PROVED axiom-clean this session).

For a ring map `φ : A ⟶ B` of commutative rings, the module-sheaf pullback
along `Spec.map φ : Spec B ⟶ Spec A` sends `tilde M` to (the `tilde` of)
the base-change module `M ⊗_A B` on `Spec B`. This is the substantive
Mathlib gap (Stacks tag 01HQ / 0BJ8): the "pullback of tilde = tilde of
base change" identification.

Direct LSP searches (iter-187 analogist, `quotscheme-isbasechange-tilde.md`)
confirm Mathlib (pinned commit `b80f227`) has no such lemma; the only
pullback formula at all is `pullbackObjFreeIso` on *free* sheaves
(`PullbackFree.lean:122`), too restrictive for general modules.

PROVED (T12 session, 2026-07-03), axiom-clean, by uniqueness of left adjoints:
`tilde.functor A ⋙ pullback (Spec.map φ)` and `extendScalars φ.hom ⋙ tilde.functor B`
are both left adjoint to `pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
moduleSpecΓFunctor ⋙ restrictScalars φ.hom` (`pullbackTilde_gammaBridge`), so
`Adjunction.leftAdjointUniq` produces the iso, whose evaluation at `M` is the
required `(Spec.map φ)^* (tilde M) ≅ tilde (B ⊗_A M)`. The Σ-pair section identity
is `Adjunction.unit_leftAdjointUniq_hom_app` applied at `m`: the unit of the first
composed adjunction traced through the bridge is definitionally
`pullback_app_isoTensor_baseMap ∘ tilde.toOpen`, while the unit of the second is
definitionally `tilde.toOpen ∘ (1 ⊗ₜ ·)`. -/
private theorem pullback_tildeIso
    {A B : CommRingCat.{u}} (φ : A ⟶ B) (M : ModuleCat.{u} A) :
    letI : Algebra A B := φ.hom.toAlgebra
    letI : Algebra Γ(Spec A, ⊤) Γ(Spec B, ⊤) :=
      ((Spec.map φ).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module Γ(Spec A, ⊤)
        Γ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde M), ⊤) :=
      Module.compHom _ ((Spec.map φ).appLE ⊤ ⊤ le_top).hom
    Nonempty {iso : (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ≅
        tilde (ModuleCat.of B (TensorProduct A B M)) //
      -- Canonical Spec base-change iso identity (Stacks 01HQ / 0BJ8): the
      -- iso, evaluated at ⊤-sections, sends the canonical pullback-section
      -- image of `tilde.toOpen M ⊤ m` (built via the adjunction-unit base map
      -- `pullback_app_isoTensor_baseMap` on `tilde M`) to `tilde.toOpen … ⊤`
      -- applied to `1 ⊗ₜ m`. This characterizes the iso as the canonical
      -- "pullback of tilde = tilde of base change" identification.
      ∀ (m : M),
        (Scheme.Modules.Hom.app iso.hom ⊤).hom
            (pullback_app_isoTensor_baseMap (Spec.map φ) (tilde M) le_top
              ((tilde.toOpen M ⊤).hom m)) =
          (tilde.toOpen (ModuleCat.of B (TensorProduct A B M)) ⊤).hom
            (1 ⊗ₜ[A] m)} := by
  letI : Algebra A B := φ.hom.toAlgebra
  letI : Algebra Γ(Spec A, ⊤) Γ(Spec B, ⊤) :=
    ((Spec.map φ).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI : Module Γ(Spec A, ⊤)
      Γ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde M), ⊤) :=
    Module.compHom _ ((Spec.map φ).appLE ⊤ ⊤ le_top).hom
  -- The two composed adjunctions with the SAME right adjoint
  -- `moduleSpecΓFunctor (R := ↑B) ⋙ restrictScalars φ.hom` (via the bridge).
  let adj1 : (tilde.functor ↑A ⋙ Scheme.Modules.pullback (Spec.map φ)) ⊣
      (moduleSpecΓFunctor (R := ↑B) ⋙ ModuleCat.restrictScalars φ.hom) :=
    ((tilde.adjunction (R := ↑A)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
      (pullbackTilde_gammaBridge φ)
  let adj2 : (ModuleCat.extendScalars φ.hom ⋙ tilde.functor ↑B) ⊣
      (moduleSpecΓFunctor (R := ↑B) ⋙ ModuleCat.restrictScalars φ.hom) :=
    (ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := ↑B))
  -- Uniqueness of left adjoints.
  let mainIso : (tilde.functor ↑A ⋙ Scheme.Modules.pullback (Spec.map φ)) ≅
      (ModuleCat.extendScalars φ.hom ⋙ tilde.functor ↑B) :=
    Adjunction.leftAdjointUniq adj1 adj2
  refine ⟨⟨mainIso.app M, fun m => ?_⟩⟩
  -- The unit-compatibility of `leftAdjointUniq`, applied at `m`; both sides
  -- reduce definitionally to the stated Σ-pair identity (the first unit is
  -- `baseMap ∘ toOpen` through the bridge; the second is `toOpen ∘ (1 ⊗ₜ ·)`).
  have key := Adjunction.unit_leftAdjointUniq_hom_app adj1 adj2 M
  exact congrArg (fun (f : M ⟶ (moduleSpecΓFunctor (R := ↑B) ⋙
    ModuleCat.restrictScalars φ.hom).obj ((ModuleCat.extendScalars φ.hom ⋙
      tilde.functor ↑B).obj M)) => f.hom m) key

/-- **Pushforward preserves quasi-coherence** (Stacks tag 01XJ) — project-side
helper named pin (iter-187 Lane F).

For a quasi-compact quasi-separated morphism `f : X ⟶ S` of schemes, the
pushforward of a quasi-coherent sheaf is quasi-coherent. Required to thread
`[IsQuasicoherent]` through the consumer chain: at the call site
`canonicalBaseChangeMap_app_app_isIso_of_isAffineOpen_of_isAffineBase`, the
argument `N := (pushforward f).obj F` is fed into `pullback_app_isoTensor`,
which (per the iter-187 analogist verdict) requires `[N.IsQuasicoherent]`;
this helper produces the instance from `[F.IsQuasicoherent]` + qcqs `f`.

PROVED (T12 session, 2026-07-03), axiom-clean. The substantive content is
Stacks 01XJ, delegated to `Scheme.Modules.pushforward_isQuasicoherent` in the
union-merge section: quasi-coherence is checked on the affine-opens cover of
`S`; on each affine `U` the qcqs section-localization engine
(`isLocalizedModule_basicOpen_of_isCompact`, Stacks 01P0 beyond the affine
case) applied on `X` over the compact quasi-separated preimage `π ⁻¹ᵁ U`
supplies the pushforward-level basic-open localization, the converse
`fromTildeΓ` transport turns it into the P1 datum for the `fromSpec`
pullback, and the tilde presentation transports back to the slice. (The old
"right adjoints preserve quasi-coherence" proof sketch here was wrong —
adjointness gives colimit preservation, not this.) -/
private theorem pushforward_isQuasicoherent
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
  -- Stacks 01XJ, proved in the union-merge section above (T12 session, 2026-07-03):
  -- the qcqs section-localization engine + the converse fromTildeΓ transport.
  Scheme.Modules.pushforward_isQuasicoherent f F

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- The unit-comparison and section-trace steps unify `Γ`-objects through the
-- `𝟭`/`⋙`-composite functor forms (v4.31 instances-transparency wall).
/-- **Step 1 pin (Stacks 01I8)**: quasi-coherent sheaf on an affine open is
`tilde` of its sections.

iter-189 Lane F unbundling (per `analogies/lane-f-isbasechange.md`
Decision 4): pinned as a separately-named typed sorry parallel to
`pullback_tildeIso` (Step 2). This breaks the iter-186/187/188 STUCK
pattern in which Steps 1, 2, 3 were bundled into the single body sorry
of `_sectionLinearEquiv`.

For a quasi-coherent sheaf `N` on `X` and an affine open `V ⊆ X`, the
pullback of `N` along `IsAffineOpen.fromSpec : Spec Γ(X, V) ⟶ X` is
canonically isomorphic to `tilde Γ(N, V)` on `Spec Γ(X, V)`.

PROVED (T12 session, 2026-07-03). The body assembles the union-merge
substrate: quasi-coherence of the pullback (`isQuasicoherent_pullback_fromSpec`,
Piece A) feeds the affine structure theorem (`isIso_fromTildeΓ_of_isQuasicoherent`,
gap1) to invert the tilde–Γ counit; the Σ-pair base map is bijective because,
through Mathlib's `Adjunction.unit_leftAdjointUniq_hom_app` (the two adjunctions
share the right adjoint `pushforward j`), it factors as (restriction-adjunction
unit component = presheaf restriction along `j ''ᵁ j ⁻¹ᵁ V = V`) ∘ (component of
the `restrictFunctorIsoPullback` natural isomorphism) ∘ (restriction along
`⊤ ≤ j ⁻¹ᵁ V = ⊤`). The iso is `(tilde.map b' ≫ fromTildeΓ)⁻¹`, and the
Σ-pair identity is `toOpen`-naturality (`tilde.toOpen_map_app`) plus the
counit computation at `⊤` (`toOpen_fromTildeΓ_app`). -/
private theorem tildeIso_of_isQuasicoherent_isAffineOpen
    {X : Scheme.{u}} (N : X.Modules) [N.IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, V) Γ(Spec Γ(X, V), ⊤) :=
      (hV.fromSpec.appLE V ⊤
        (le_of_eq hV.fromSpec_preimage_self.symm)).hom.toAlgebra
    letI : Module Γ(X, V) Γ((Scheme.Modules.pullback hV.fromSpec).obj N, ⊤) :=
      Module.compHom _
        (hV.fromSpec.appLE V ⊤
          (le_of_eq hV.fromSpec_preimage_self.symm)).hom
    Nonempty {iso : (Scheme.Modules.pullback hV.fromSpec).obj N ≅
        tilde (ModuleCat.of Γ(X, V) Γ(N, V)) //
      -- Canonical iso identity (Stacks 01I8 — `step1 = (asIso fromTildeΓ).symm`):
      -- iso.inv at ⊤-sections sends `tilde.toOpen Γ(N, V) ⊤ s` to the canonical
      -- pullback-section image of `s` produced by `pullback_app_isoTensor_baseMap`
      -- (the adjunction-unit-based base map). This characterizes the iso as the
      -- inverse of the `fromTildeΓ` counit at the affine open V.
      ∀ (s : Γ(N, V)),
        (Scheme.Modules.Hom.app iso.inv ⊤).hom
            ((tilde.toOpen (ModuleCat.of Γ(X, V) Γ(N, V)) ⊤).hom s) =
          pullback_app_isoTensor_baseMap hV.fromSpec N
            (le_of_eq hV.fromSpec_preimage_self.symm) s} := by
  letI : Algebra Γ(X, V) Γ(Spec Γ(X, V), ⊤) :=
    (hV.fromSpec.appLE V ⊤
      (le_of_eq hV.fromSpec_preimage_self.symm)).hom.toAlgebra
  letI : Module Γ(X, V) Γ((Scheme.Modules.pullback hV.fromSpec).obj N, ⊤) :=
    Module.compHom _
      (hV.fromSpec.appLE V ⊤
        (le_of_eq hV.fromSpec_preimage_self.symm)).hom
  -- Step 0 (gap1 substrate, above): the pullback is quasi-coherent, so its
  -- tilde–Γ counit is an isomorphism (Stacks 01I8).
  haveI hGqc : ((Scheme.Modules.pullback hV.fromSpec).obj N).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pullback_fromSpec N hV
  haveI hP1 : IsIso (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pullback hV.fromSpec).obj N)) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _
  -- Step 1: the base map `b` is bijective. By definition `b` is the composite of
  -- the `V`-sections of the pullback–pushforward adjunction unit with the
  -- presheaf restriction along `⊤ ≤ j ⁻¹ᵁ V` (an equality of opens). The unit
  -- component is identified, through `unit_leftAdjointUniq_hom_app` (the two
  -- adjunctions share the right adjoint `pushforward j`), with the
  -- restriction-adjunction unit component — a presheaf restriction along the
  -- equality `j ''ᵁ (j ⁻¹ᵁ V) = V` — followed by a component of the natural
  -- isomorphism `restrictFunctorIsoPullback`. All three factors are bijective.
  have him : hV.fromSpec ''ᵁ (hV.fromSpec ⁻¹ᵁ V) = V := by
    rw [hV.fromSpec_preimage_self, Scheme.Hom.image_top_eq_opensRange,
      hV.opensRange_fromSpec]
  have hrestr : Function.Bijective
      ((((Scheme.Modules.pullback hV.fromSpec).obj N).presheaf.map
        (homOfLE (le_of_eq hV.fromSpec_preimage_self.symm)).op).hom) := by
    rw [Subsingleton.elim
      (homOfLE (le_of_eq hV.fromSpec_preimage_self.symm))
      (eqToHom hV.fromSpec_preimage_self.symm),
      eqToHom_op, eqToHom_map]
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have h1 : Function.Bijective ((Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictAdjunction hV.fromSpec).unit.app N) V).hom) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    refine Function.bijective_iff_has_inverse.mpr
      ⟨(N.presheaf.map (eqToHom him.symm).op).hom, fun y => ?_, fun y => ?_⟩
    · change (AddCommGrpCat.Hom.hom (N.presheaf.map (eqToHom him.symm).op))
          ((AddCommGrpCat.Hom.hom
            (N.presheaf.map (homOfLE (hV.fromSpec.image_preimage_le V)).op)) y) = y
      have hcomp1 : N.presheaf.map (homOfLE (hV.fromSpec.image_preimage_le V)).op ≫
          N.presheaf.map (eqToHom him.symm).op = 𝟙 _ := by
        rw [← Functor.map_comp, ← op_comp,
          Subsingleton.elim
            (eqToHom him.symm ≫ homOfLE (hV.fromSpec.image_preimage_le V)) (𝟙 V),
          op_id, CategoryTheory.Functor.map_id]
      exact congrArg (fun φ => (AddCommGrpCat.Hom.hom φ) y) hcomp1
    · change (AddCommGrpCat.Hom.hom
            (N.presheaf.map (homOfLE (hV.fromSpec.image_preimage_le V)).op))
          ((AddCommGrpCat.Hom.hom (N.presheaf.map (eqToHom him.symm).op)) y) = y
      have hcomp2 : N.presheaf.map (eqToHom him.symm).op ≫
          N.presheaf.map (homOfLE (hV.fromSpec.image_preimage_le V)).op = 𝟙 _ := by
        rw [← Functor.map_comp, ← op_comp,
          Subsingleton.elim
            (homOfLE (hV.fromSpec.image_preimage_le V) ≫ eqToHom him.symm)
            (𝟙 (hV.fromSpec ''ᵁ (hV.fromSpec ⁻¹ᵁ V))),
          op_id, CategoryTheory.Functor.map_id]
      exact congrArg (fun φ => (AddCommGrpCat.Hom.hom φ) y) hcomp2
  have h2 : Function.Bijective ((Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).hom.app N)
      (hV.fromSpec ⁻¹ᵁ V)).hom) := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨((Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).inv.app N)
        (hV.fromSpec ⁻¹ᵁ V)).hom), fun y => ?_, fun y => ?_⟩
    · simp only [← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app,
        Iso.hom_inv_id_app, Scheme.Modules.Hom.id_app, AddCommGrpCat.hom_id,
        AddMonoidHom.id_apply]
    · simp only [← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app,
        Iso.inv_hom_id_app, Scheme.Modules.Hom.id_app, AddCommGrpCat.hom_id,
        AddMonoidHom.id_apply]
  -- Unit comparison: the two left adjoints of `pushforward j` have canonically
  -- identified units.
  have hcomp : (Scheme.Modules.restrictAdjunction hV.fromSpec).unit.app N ≫
      (Scheme.Modules.pushforward hV.fromSpec).map
        ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).hom.app N) =
      (Scheme.Modules.pullbackPushforwardAdjunction hV.fromSpec).unit.app N :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ N
  have hunit : Function.Bijective (pullback_app_isoTensor_unitAtV hV.fromSpec N V) := by
    have hfun : ∀ x : Γ(N, V), pullback_app_isoTensor_unitAtV hV.fromSpec N V x =
        (Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).hom.app N)
          (hV.fromSpec ⁻¹ᵁ V)).hom
        ((Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictAdjunction hV.fromSpec).unit.app N) V).hom x) :=
      fun x => (congrArg (fun φ => (Scheme.Modules.Hom.app φ V).hom x) hcomp.symm)
    have : ⇑(pullback_app_isoTensor_unitAtV hV.fromSpec N V) =
        (fun y => (Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).hom.app N)
          (hV.fromSpec ⁻¹ᵁ V)).hom y) ∘
        (fun x => (Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictAdjunction hV.fromSpec).unit.app N) V).hom x) :=
      funext hfun
    rw [this]
    exact h2.comp h1
  have hbij : Function.Bijective
      (pullback_app_isoTensor_baseMap hV.fromSpec N
        (le_of_eq hV.fromSpec_preimage_self.symm)) := by
    have : ⇑(pullback_app_isoTensor_baseMap hV.fromSpec N
        (le_of_eq hV.fromSpec_preimage_self.symm)) =
        (fun y => (((Scheme.Modules.pullback hV.fromSpec).obj N).presheaf.map
          (homOfLE (le_of_eq hV.fromSpec_preimage_self.symm)).op).hom y) ∘
        (fun x => pullback_app_isoTensor_unitAtV hV.fromSpec N V x) := rfl
    rw [this]
    exact hrestr.comp hunit
  -- Step 2: the compHom ring map is the canonical `(ΓSpecIso _).inv`, so `b`
  -- packages as a morphism of `ModuleCat Γ(X, V)` into the module of global
  -- sections of the pullback.
  have hact : hV.fromSpec.appLE V ⊤ (le_of_eq hV.fromSpec_preimage_self.symm)
      = (Scheme.ΓSpecIso Γ(X, V)).inv := by
    rw [Scheme.Hom.appLE, hV.fromSpec_app_self, Category.assoc,
      ← Functor.map_comp, ← op_comp,
      Subsingleton.elim (homOfLE (le_of_eq hV.fromSpec_preimage_self.symm) ≫
        eqToHom hV.fromSpec_preimage_self) (𝟙 (⊤ : (Spec Γ(X, V)).Opens)),
      op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  let b' : ModuleCat.of Γ(X, V) Γ(N, V) ⟶
      (modulesSpecToSheaf.obj ((Scheme.Modules.pullback hV.fromSpec).obj N)).presheaf.obj
        (Opposite.op ⊤) :=
    ConcreteCategory.ofHom
      { toFun := fun t => pullback_app_isoTensor_baseMap hV.fromSpec N
          (le_of_eq hV.fromSpec_preimage_self.symm) t
        map_add' := fun t u => map_add _ t u
        map_smul' := fun r t => by
          have h1 := (pullback_app_isoTensor_baseMap hV.fromSpec N
            (le_of_eq hV.fromSpec_preimage_self.symm)).map_smul r t
          change pullback_app_isoTensor_baseMap hV.fromSpec N
              (le_of_eq hV.fromSpec_preimage_self.symm) (r • t) =
            ((Scheme.ΓSpecIso Γ(X, V)).inv.hom r) •
              pullback_app_isoTensor_baseMap hV.fromSpec N
                (le_of_eq hV.fromSpec_preimage_self.symm) t
          rw [← hact]
          exact h1 }
  have hb'app : ∀ t : Γ(N, V), b'.hom t = pullback_app_isoTensor_baseMap hV.fromSpec N
      (le_of_eq hV.fromSpec_preimage_self.symm) t := fun t => rfl
  have hb'bij : Function.Bijective ⇑(ConcreteCategory.hom b') := by
    have h : ⇑(ConcreteCategory.hom b') = ⇑(pullback_app_isoTensor_baseMap hV.fromSpec N
        (le_of_eq hV.fromSpec_preimage_self.symm)) := funext hb'app
    rw [h]; exact hbij
  haveI hb : IsIso b' := (ConcreteCategory.isIso_iff_bijective b').mpr hb'bij
  -- Step 3: assemble the iso `j^* N ≅ tilde Γ(N, V)` as the inverse of
  -- `tilde.map b' ≫ fromTildeΓ` and verify the Σ-pair section identity by
  -- `toOpen` naturality plus the counit computation at `⊤`.
  haveI hmb : IsIso (tilde.map b') := inferInstanceAs (IsIso ((tilde.functor _).map b'))
  refine ⟨⟨((asIso (tilde.map b')) ≪≫ (asIso (Scheme.Modules.fromTildeΓ
    ((Scheme.Modules.pullback hV.fromSpec).obj N)))).symm, fun s => ?_⟩⟩
  have hinv : (((asIso (tilde.map b')) ≪≫ (asIso (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pullback hV.fromSpec).obj N)))).symm).inv =
      tilde.map b' ≫ Scheme.Modules.fromTildeΓ
        ((Scheme.Modules.pullback hV.fromSpec).obj N) := rfl
  rw [hinv]
  have hnat := congrArg (fun (φ : ModuleCat.of Γ(X, V) Γ(N, V) ⟶ _) => φ.hom s)
    (tilde.toOpen_map_app b' ⊤)
  have hcounit := congrArg
    (fun (φ : (modulesSpecToSheaf.obj
        ((Scheme.Modules.pullback hV.fromSpec).obj N)).presheaf.obj (Opposite.op ⊤) ⟶ _) =>
      φ.hom (b'.hom s))
    (Scheme.Modules.toOpen_fromTildeΓ_app
      ((Scheme.Modules.pullback hV.fromSpec).obj N) ⊤)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat hcounit
  have step1 : (Scheme.Modules.Hom.app (tilde.map b' ≫ Scheme.Modules.fromTildeΓ
        ((Scheme.Modules.pullback hV.fromSpec).obj N)) ⊤).hom
        ((tilde.toOpen (ModuleCat.of Γ(X, V) Γ(N, V)) ⊤).hom s) =
      (Scheme.Modules.Hom.app (Scheme.Modules.fromTildeΓ
        ((Scheme.Modules.pullback hV.fromSpec).obj N)) ⊤).hom
        ((tilde.toOpen ((modulesSpecToSheaf.obj
          ((Scheme.Modules.pullback hV.fromSpec).obj N)).presheaf.obj (Opposite.op ⊤)) ⊤).hom
          (b'.hom s)) := congrArg _ hnat
  have hid : ((modulesSpecToSheaf.obj
      ((Scheme.Modules.pullback hV.fromSpec).obj N)).1.map
      (homOfLE (le_top : (⊤ : (Spec Γ(X, V)).Opens) ≤ ⊤)).op).hom (b'.hom s) =
      b'.hom s := by
    rw [Subsingleton.elim (homOfLE (le_top : (⊤ : (Spec Γ(X, V)).Opens) ≤ ⊤))
      (𝟙 (⊤ : (Spec Γ(X, V)).Opens)), op_id, CategoryTheory.Functor.map_id]
    rfl
  have step2 : (Scheme.Modules.Hom.app (Scheme.Modules.fromTildeΓ
        ((Scheme.Modules.pullback hV.fromSpec).obj N)) ⊤).hom
        ((tilde.toOpen ((modulesSpecToSheaf.obj
          ((Scheme.Modules.pullback hV.fromSpec).obj N)).presheaf.obj (Opposite.op ⊤)) ⊤).hom
          (b'.hom s)) =
      pullback_app_isoTensor_baseMap hV.fromSpec N
        (le_of_eq hV.fromSpec_preimage_self.symm) s :=
    hcounit.trans (hid.trans (hb'app s))
  exact step1.trans step2

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- Section transport through `fromSpec` expands the affine tilde equivalence and open transports.
/-- **Step 3 pin (transport)**: section-level transport for pullback along
the affine-open's `fromSpec` map.

iter-189 Lane F unbundling (per `analogies/lane-f-isbasechange.md`
Decision 4): pinned as a separately-named typed sorry parallel to
`pullback_tildeIso` (Step 2) and `tildeIso_of_isQuasicoherent_isAffineOpen`
(Step 1).

This pin captures the Step 3 transport content of the Tilde-isoTop route:
the top section of a sheaf pulled back along
`IsAffineOpen.fromSpec : Spec Γ(Y, U) ⟶ Y` is canonically `Γ(Y, U)`-linearly
identified with the section over `U` itself. Substantive content combines
`AlgebraicGeometry.tilde.isoTop` (Mathlib HAS) with the `hU.isoSpec`
transport (Mathlib gap at `b80f227`).

iter-190 closure (Lane F Step 3 HARD BAR): the body chains
`Scheme.Modules.restrictFunctorIsoPullback` (Mathlib's identification of the
`pullback` functor with the `restrict` functor along an open immersion;
applicable since `hU.fromSpec` carries `IsOpenImmersion` via
`IsAffineOpen.isOpenImmersion_fromSpec`) with the definitional
`Scheme.Modules.restrict_obj` (sections of `N.restrict f` over `V` equal
sections of `N` over `f ''ᵁ V`, by `rfl`) and the propositional
`Scheme.Hom.image_top_eq_opensRange` + `IsAffineOpen.opensRange_fromSpec`
to identify `hU.fromSpec ''ᵁ ⊤ = U`. -/
private theorem pullback_of_openImmersion_iso_restrict
    {Y : Scheme.{u}} (N : Y.Modules) {U : Y.Opens} (hU : IsAffineOpen U) :
    -- `Γ(Y, U)`-linear identification between the top section of the pullback
    -- (along `hU.fromSpec : Spec Γ(Y, U) ⟶ Y`) and `Γ(N, U)` itself. The
    -- module-action ring on the LHS is set up via the canonical algebra
    -- `Γ(Y, U) → Γ((Spec Γ(Y, U)), ⊤)`, which is the structure-sheaf
    -- equivalence on the affine scheme.
    letI : Algebra Γ(Y, U) Γ((Spec Γ(Y, U)), ⊤) :=
      (Scheme.ΓSpecIso _).inv.hom.toAlgebra
    letI : Module Γ(Y, U) Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤) :=
      Module.compHom _ (Scheme.ΓSpecIso _).inv.hom
    -- (N4) Σ-pair characterization (T12, 2026-07-03): the inverse of the equiv is
    -- the canonical base map `pullback_app_isoTensor_baseMap` at `V = U`, `U = ⊤`.
    Nonempty {f : Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤) ≃ₗ[Γ(Y, U)]
        Γ(N, U) //
      ∀ (y : Γ(N, U)),
        f.symm y = pullback_app_isoTensor_baseMap hU.fromSpec N
          (le_of_eq hU.fromSpec_preimage_self.symm) y} := by
  letI algInst : Algebra Γ(Y, U) Γ((Spec Γ(Y, U)), ⊤) :=
    (Scheme.ΓSpecIso _).inv.hom.toAlgebra
  letI modInst : Module Γ(Y, U) Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤) :=
    Module.compHom _ (Scheme.ΓSpecIso _).inv.hom
  -- Step 1: Identify pullback along `hU.fromSpec` with the restriction functor.
  -- Mathlib's `restrictFunctorIsoPullback` gives this for any open immersion;
  -- `hU.fromSpec` is an open immersion by `IsAffineOpen.isOpenImmersion_fromSpec`.
  -- (`let`, not `have`: the (N4) characterization below needs its value.)
  let isoSheaf : (Scheme.Modules.pullback hU.fromSpec).obj N ≅ N.restrict hU.fromSpec :=
    ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app N).symm
  -- Step 2: The image of ⊤ under hU.fromSpec equals U (Stacks 01HH-style bridge).
  have hImg : (hU.fromSpec ''ᵁ (⊤ : (Spec Γ(Y, U)).Opens) : Y.Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange]; exact hU.opensRange_fromSpec
  -- Step 3: section-level map from the iso, then the rfl identification
  -- `Γ(N.restrict hU.fromSpec, ⊤) = Γ(N, hU.fromSpec ''ᵁ ⊤)` (per
  -- `Scheme.Modules.restrict_obj`), then a presheaf restriction along the
  -- propositional equality `hU.fromSpec ''ᵁ ⊤ = U` to land in `Γ(N, U)`.
  -- Define the additive equivalence.
  let toFun : Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤) → Γ(N, U) := fun x =>
    (N.presheaf.map (eqToHom hImg.symm).op).hom ((Scheme.Modules.Hom.app isoSheaf.hom ⊤).hom x)
  let invFun : Γ(N, U) → Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤) := fun y =>
    (Scheme.Modules.Hom.app isoSheaf.inv ⊤).hom ((N.presheaf.map (eqToHom hImg).op).hom y)
  have left_inv : Function.LeftInverse invFun toFun := by
    intro x
    simp only [invFun, toFun, ← AddCommGrpCat.comp_apply, ← Functor.map_comp, ← op_comp,
      eqToHom_trans, eqToHom_refl, op_id, CategoryTheory.Functor.map_id,
      AddCommGrpCat.hom_id, AddMonoidHom.id_apply,
      ← Scheme.Modules.Hom.comp_app, isoSheaf.hom_inv_id, Scheme.Modules.Hom.id_app]
  have right_inv : Function.RightInverse invFun toFun := by
    intro y
    simp only [invFun, toFun, ← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app,
      isoSheaf.inv_hom_id, Scheme.Modules.Hom.id_app,
      AddCommGrpCat.hom_id, AddMonoidHom.id_apply,
      ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id,
      CategoryTheory.Functor.map_id]
  have map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y := by
    intro x y
    change (AddCommGrpCat.Hom.hom (N.presheaf.map (eqToHom hImg.symm).op))
      ((AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app isoSheaf.hom ⊤)) (x + y)) =
      _ + _
    rw [show ((AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app isoSheaf.hom ⊤)) (x + y)) =
      (AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app isoSheaf.hom ⊤)) x +
      (AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app isoSheaf.hom ⊤)) y from
      AddMonoidHom.map_add _ _ _]
    exact AddMonoidHom.map_add _ _ _
  let addEq : Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤) ≃+ Γ(N, U) :=
    { toFun := toFun
      invFun := invFun
      left_inv := left_inv
      right_inv := right_inv
      map_add' := map_add' }
  -- Upgrade to a `Γ(Y, U)`-LinearEquiv via the smul compatibility.
  refine ⟨⟨addEq.toLinearEquiv ?_, ?_⟩⟩
  · -- Smul-compatibility:
    intro r x
    -- The LHS `r • x` is `Module.compHom`-action: `r • x = (ΓSpecIso _).inv.hom r • x`
    -- with the natural Γ(Spec Γ(Y, U), ⊤)-action on the pullback module sheaf at ⊤.
    -- Step A: Reduce r • x on the LHS to (ΓSpecIso).inv.hom r • x with natural action.
    change (AddCommGrpCat.Hom.hom (N.presheaf.map (eqToHom hImg.symm).op))
      ((AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app isoSheaf.hom ⊤))
        ((CommRingCat.Hom.hom (Scheme.ΓSpecIso _).inv) r • x)) = _
    -- Step B: Apply Hom.app_smul (Γ(Spec ⊤)-linearity of the SheafOfModules iso),
    -- which migrates the scalar through `Scheme.Modules.Hom.app isoSheaf.hom ⊤`.
    rw [Scheme.Modules.Hom.app_smul]
    -- Step C (iter-192 Lane F closure): the residual identity is the substantive
    -- Stacks 01HH-style ring compatibility:
    --   Y.presheaf.map (eqToHom hImg.symm).op
    --     ((hU.fromSpec.appIso ⊤).inv ((ΓSpecIso _).inv.hom r)) = r,
    -- combined with `Scheme.Modules.map_smul` to pull the algebra-map image
    -- through the presheaf restriction.
    --
    -- The recipe (per `analogies/lane-f-restrictscalars-smul.md`):
    -- Step A: aliasing-`let` `y : Γ(N, hU.fromSpec ''ᵁ ⊤)` to make the smul-unfold
    -- on the restrict-of-N section visible as a Y-side action via
    -- `restrictFunctor`'s definition (smul is `(appIso ⊤).inv.hom s` on Y-side).
    -- Step B: `Scheme.Modules.map_smul` to migrate the scalar through the
    -- presheaf restriction.
    -- Step C: the categorical key identity
    --   (ΓSpecIso _).inv ≫ (hU.fromSpec.appIso ⊤).inv ≫
    --     Y.presheaf.map (eqToHom hImg.symm).op = 𝟙 _
    -- via `appLE_appIso_inv` + `fromSpec_app_self` + `Hom.appLE` unfolding.
    -- Step A: aliasing-`let` to bring the Y-side smul into instance scope.
    set y : ↑Γ(N, hU.fromSpec ''ᵁ ⊤) := (Scheme.Modules.Hom.app isoSheaf.hom ⊤).hom x
      with hy
    -- Step A continued: the Γ(Spec _, ⊤)-smul on `y` (under its restrict-of-N
    -- view) is rfl-equal to the Y-side smul via `(hU.fromSpec.appIso ⊤).inv`.
    change (N.presheaf.map (eqToHom hImg.symm).op).hom
      (((hU.fromSpec.appIso ⊤).inv.hom ((Scheme.ΓSpecIso Γ(Y, U)).inv.hom r)) • y) =
      r • (N.presheaf.map (eqToHom hImg.symm).op).hom y
    -- Step B: migrate the Y-side scalar through `N.presheaf.map`.
    rw [Scheme.Modules.map_smul]
    -- Step C: reduce the scalar identity to the categorical key identity.
    congr 1
    -- Goal: (Y.presheaf.map (eqToHom hImg.symm).op).hom
    --        ((hU.fromSpec.appIso ⊤).inv.hom ((Scheme.ΓSpecIso _).inv.hom r)) = r.
    -- Build the key categorical identity:
    --   (ΓSpecIso _).inv ≫ (hU.fromSpec.appIso ⊤).inv ≫
    --     Y.presheaf.map (eqToHom hImg.symm).op = 𝟙 _.
    have e₀ : (⊤ : (Spec Γ(Y, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U :=
      le_of_eq hU.fromSpec_preimage_self.symm
    -- Sub-key: `hU.fromSpec.appLE U ⊤ e₀ = (ΓSpecIso _).inv` (via fromSpec_app_self).
    have h_appLE : hU.fromSpec.appLE U ⊤ e₀ = (Scheme.ΓSpecIso Γ(Y, U)).inv := by
      simp [Scheme.Hom.appLE, hU.fromSpec_app_self, ← Functor.map_comp]
    -- Apply `appLE_appIso_inv` and combine.
    have h_combine :
        (Scheme.ΓSpecIso Γ(Y, U)).inv ≫ (hU.fromSpec.appIso ⊤).inv =
          Y.presheaf.map (homOfLE (le_of_eq hImg)).op := by
      rw [← h_appLE]
      exact Scheme.Hom.appLE_appIso_inv hU.fromSpec e₀
    -- Post-compose with `Y.presheaf.map (eqToHom hImg.symm).op` to collapse to 𝟙.
    have h_key :
        (Scheme.ΓSpecIso Γ(Y, U)).inv ≫ (hU.fromSpec.appIso ⊤).inv ≫
          Y.presheaf.map (eqToHom hImg.symm).op = 𝟙 _ := by
      rw [← Category.assoc, h_combine, ← Functor.map_comp, ← op_comp]
      -- The composite `eqToHom hImg.symm ≫ homOfLE _ : U ⟶ U` in `Y.Opens` is `𝟙 U`
      -- by `Subsingleton` of the poset structure on `Opens Y`.
      simp
    -- Apply h_key elementwise to r.
    exact congr($h_key r)
  · -- (N4) characterization: the inverse of the equiv is the canonical base map.
    -- Route: the unit-compatibility `Adjunction.unit_leftAdjointUniq_hom_app` for
    -- `restrictAdjunction` vs `pullbackPushforwardAdjunction` (whose `leftAdjointUniq`
    -- IS `restrictFunctorIsoPullback`), then naturality of the comparison against the
    -- restriction `⊤ ≤ fromSpec ⁻¹ᵁ U`, then collapse of the two `N`-restrictions
    -- (`restrictAdjunction`'s unit component is a plain presheaf restriction, rfl).
    intro y
    have hk := congrArg
      (fun (k : N ⟶ (Scheme.Modules.pushforward hU.fromSpec).obj
          ((Scheme.Modules.pullback hU.fromSpec).obj N)) =>
        (Scheme.Modules.Hom.app k U).hom y)
      (Adjunction.unit_leftAdjointUniq_hom_app
        (Scheme.Modules.restrictAdjunction hU.fromSpec)
        (Scheme.Modules.pullbackPushforwardAdjunction hU.fromSpec) N)
    have hnat := congrArg
      (fun (k : Γ(N.restrict hU.fromSpec, hU.fromSpec ⁻¹ᵁ U) ⟶
          Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤)) =>
        (AddCommGrpCat.Hom.hom k)
          ((N.presheaf.map (homOfLE (hU.fromSpec.image_preimage_le U)).op).hom y))
      ((Scheme.Modules.Hom.mapPresheaf
        ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).hom.app N)).naturality
        (homOfLE (le_of_eq hU.fromSpec_preimage_self.symm)).op)
    have hcol := modules_res_res_hom N
      (hU.fromSpec.opensFunctor.map (homOfLE (le_of_eq hU.fromSpec_preimage_self.symm)))
      (homOfLE (hU.fromSpec.image_preimage_le U)) (eqToHom hImg) y
    exact (congrArg (fun w =>
        (Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).hom.app N) ⊤).hom w)
      hcol.symm).trans
      (hnat.trans (congrArg (fun w =>
        ((((Scheme.Modules.pullback hU.fromSpec).obj N).presheaf.map
          (homOfLE (le_of_eq hU.fromSpec_preimage_self.symm)).op).hom) w) hk))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
-- Building the section linear equivalence unfolds both tilde routes and their scalar actions.
/-- **Section-level LinearEquiv via the Tilde route** (iter-188 Lane F NAMED
HELPER, iter-189 unbundling refactor).

The substantive transport-and-intertwining helper: given a morphism `g : Y ⟶ X`
of schemes, a quasi-coherent module `N` on `X`, and affine opens
`V ⊆ X`, `U ⊆ Y` with `U ⊆ g⁻¹ V`, produces:
- a `Γ(Y, U)`-linear equiv between `TensorProduct Γ(X, V) Γ(Y, U) Γ(N, V)`
  and `Γ((pullback g).obj N, U)`, and
- a proof that this equiv sends `1 ⊗ x` to `pullback_app_isoTensor_baseMap g N e x`
  (the Beck-Chevalley compatibility).

The construction follows the iter-187 analogist-licensed Tilde route
(`analogies/quotscheme-isbasechange-tilde.md`):
  Step 1: identify `N|_V ≅ tilde Γ(N, V)` on `Spec Γ(X, V)` using
    `[N.IsQuasicoherent]` (extract a presentation on the affine open
    after transporting via `hV.isoSpec`).
  Step 2: pull back via `Spec.map φ : Spec Γ(Y, U) ⟶ Spec Γ(X, V)`,
    where `φ = g.appLE V U e`; apply `pullback_tildeIso` to obtain
    `(pullback (Spec.map φ)).obj (tilde Γ(N, V)) ≅
      tilde (Γ(Y, U) ⊗ Γ(N, V))` on `Spec Γ(Y, U)`.
  Step 3: transport via `hU.isoSpec` back to `U`-sections of
    `(pullback g).obj N`.
  Step 4: evaluate at `⊤` via `tilde.isoTop` to extract the section-level
    linear equiv.
  Step 5: verify the intertwining via naturality of the adjunction unit
    (the Beck-Chevalley compatibility check; ~30-50 LOC).

The substantive Mathlib gap content (Stacks 01HQ "pullback of tilde =
tilde of base change", plus the affine-open / Spec transport) is now
fully assembled in the body from `pullback_tildeIso`,
`tildeIso_of_isQuasicoherent_isAffineOpen`,
`pullback_of_openImmersion_iso_restrict`, and the N1-N4 naturality
helpers — all sorry-free. This helper is closed axiom-clean. -/
theorem pullback_app_isoTensor_baseMap_sectionLinearEquiv
    {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules) [N.IsQuasicoherent]
    {U : Y.Opens} {V : X.Opens}
    (_hU : IsAffineOpen U) (_hV : IsAffineOpen V)
    (e : U ≤ g ⁻¹ᵁ V) :
    letI : Algebra Γ(X, V) Γ(Y, U) := (g.appLE V U e).hom.toAlgebra
    letI : Module Γ(X, V) Γ((Scheme.Modules.pullback g).obj N, U) :=
      Module.compHom _ (g.appLE V U e).hom
    Nonempty {f : TensorProduct Γ(X, V) Γ(Y, U) Γ(N, V) ≃ₗ[Γ(Y, U)]
                Γ((Scheme.Modules.pullback g).obj N, U) //
      ∀ x : Γ(N, V),
        f (1 ⊗ₜ[Γ(X, V)] x) = pullback_app_isoTensor_baseMap g N e x} := by
  letI : Algebra Γ(X, V) Γ(Y, U) := (g.appLE V U e).hom.toAlgebra
  letI : Module Γ(X, V) Γ((Scheme.Modules.pullback g).obj N, U) :=
    Module.compHom _ (g.appLE V U e).hom
  -- iter-189 Lane F unbundle (per `analogies/lane-f-isbasechange.md`
  -- Decision 4): three Mathlib gaps are now pinned as separately-named
  -- typed sorries; the body of `_sectionLinearEquiv` is reduced to
  -- compositional bookkeeping over the chain.
  --
  -- Step 1 (Stacks 01I8 — `tildeIso_of_isQuasicoherent_isAffineOpen`):
  --   `N|_{Spec Γ(X, V)} ≅ tilde Γ(N, V)`  on  `Spec Γ(X, V)`.
  -- Pulling back along `Spec.map φ : Spec Γ(Y, U) ⟶ Spec Γ(X, V)`
  -- (where `φ = g.appLE V U e`) and applying Step 2 (`pullback_tildeIso`,
  -- Stacks 01HQ) gives `(Spec.map φ)^* tilde Γ(N, V) ≅
  --   tilde (Γ(Y, U) ⊗_{Γ(X, V)} Γ(N, V))`.
  -- Identifying the two compositions via the commutative square
  -- `hU.fromSpec ≫ g = Spec.map φ ≫ hV.fromSpec` and applying Step 3
  -- transport (`pullback_of_openImmersion_iso_restrict`) brings the
  -- section back to `U` itself. Evaluating tilde at `⊤` via
  -- `tilde.isoTop` extracts the section-level data; the underlying
  -- module of `tilde (Γ(Y, U) ⊗ Γ(N, V))` at `⊤` is exactly
  -- `Γ(Y, U) ⊗_{Γ(X, V)} Γ(N, V)`. The intertwining at `1 ⊗ x` (the
  -- Beck-Chevalley check) follows from naturality of the adjunction
  -- unit `pullback_app_isoTensor_unitAtV`.
  obtain ⟨⟨step1, _step1_apply⟩⟩ :=
    tildeIso_of_isQuasicoherent_isAffineOpen N _hV
  obtain ⟨⟨step2, _step2_apply⟩⟩ :=
    pullback_tildeIso (g.appLE V U e) (ModuleCat.of Γ(X, V) Γ(N, V))
  obtain ⟨⟨step3, _step3_symm_apply⟩⟩ :=
    pullback_of_openImmersion_iso_restrict
      ((Scheme.Modules.pullback g).obj N) _hU
  -- iter-193 Lane F: assemble the iso chain at the sheaf level.
  -- The commutative square `hU.fromSpec ≫ g = Spec.map φ ≫ hV.fromSpec`
  -- (where `φ = g.appLE V U e`) comes from Mathlib's
  -- `IsAffineOpen.SpecMap_appLE_fromSpec`.
  have h_eq : _hU.fromSpec ≫ g = Spec.map (g.appLE V U e) ≫ _hV.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec g _hV _hU e).symm
  -- Sheaf-level iso chain (5-step compositional transport):
  --   (pullback hU.fromSpec).obj ((pullback g).obj N)
  -- = (pullback g ⋙ pullback hU.fromSpec).obj N                         [defeq]
  -- ≅ (pullback (hU.fromSpec ≫ g)).obj N             [pullbackComp]
  -- ≅ (pullback (Spec.map φ ≫ hV.fromSpec)).obj N    [pullbackCongr h_eq]
  -- ≅ (pullback (Spec.map φ)).obj ((pullback hV.fromSpec).obj N)
  --                                                   [(pullbackComp).symm]
  -- ≅ (pullback (Spec.map φ)).obj (tilde Γ(N, V))    [step1 (Stacks 01I8)]
  -- ≅ tilde (TensorProduct Γ(X,V) Γ(Y,U) Γ(N,V))     [step2 (Stacks 01HQ)]
  let composedIso :=
    ((Scheme.Modules.pullbackComp _hU.fromSpec g).app N ≪≫
      (Scheme.Modules.pullbackCongr h_eq).app N ≪≫
      ((Scheme.Modules.pullbackComp (Spec.map (g.appLE V U e)) _hV.fromSpec).app N).symm ≪≫
      (Scheme.Modules.pullback (Spec.map (g.appLE V U e))).mapIso step1 ≪≫
      step2)
  -- iter-193 Lane F partial: the AddEquiv from sheaf-level `composedIso` at
  -- ⊤-sections is established below. The remaining residual (iter-194+) is:
  -- (a) chain `topAdd` with `tilde.isoTop.symm` to land in TensorProduct;
  -- (b) upgrade AddEquiv → Γ(Y, U)-LinearEquiv via Hom.app_smul + ΓSpecIso;
  -- (c) compose with `step3` to reach Γ((pullback g).obj N, U);
  -- (d) verify the Beck-Chevalley intertwining `1 ⊗ x ↦ baseMap g N e x`
  --     using naturality of the adjunction unit `pullback_app_isoTensor_unitAtV`.
  let topAdd :=
    { toFun := fun x => (Scheme.Modules.Hom.app composedIso.hom ⊤).hom x
      invFun := fun y => (Scheme.Modules.Hom.app composedIso.inv ⊤).hom y
      left_inv := fun x => by
        simp only [← AddCommGrpCat.comp_apply,
          ← Scheme.Modules.Hom.comp_app, composedIso.hom_inv_id,
          Scheme.Modules.Hom.id_app, AddCommGrpCat.hom_id, AddMonoidHom.id_apply]
      right_inv := fun y => by
        simp only [← AddCommGrpCat.comp_apply,
          ← Scheme.Modules.Hom.comp_app, composedIso.inv_hom_id,
          Scheme.Modules.Hom.id_app, AddCommGrpCat.hom_id, AddMonoidHom.id_apply]
      map_add' := fun x y =>
        (Scheme.Modules.Hom.app composedIso.hom ⊤).hom.map_add x y
      : Γ((Scheme.Modules.pullback _hU.fromSpec).obj ((Scheme.Modules.pullback g).obj N), ⊤) ≃+ _ }
  -- iter-194 Lane F LinearEquiv extraction (PUSH-BEYOND, axiom-clean):
  -- (a) Upgrade `topAdd` to a `Γ(Y, U)`-LinearEquiv via `Hom.app_smul` and the
  --     `Module.compHom _ (Scheme.ΓSpecIso _).inv.hom` recipe.
  -- (b) Compose with `(tilde.isoTop _).symm.toLinearEquiv` to land in the
  --     TensorProduct module (the underlying type is the same as
  --     `(modulesSpecToSheaf.obj (tilde _)).presheaf.obj (.op ⊤)`, and the
  --     `Γ(Y, U)`-module structures agree by `Module.compHom`/`restrictScalars`
  --     defeq).
  -- (c) Compose with `step3` to land in `Γ((pullback g).obj N, U)`.
  -- (d) Beck-Chevalley intertwining: typed sorry (see ARCHITECTURAL NOTE below).
  -- Introduce a local alias for the target ModuleCat to avoid Γ-notation
  -- ambiguity inside type ascriptions.
  let TR : ModuleCat (Γ(Y, U)) :=
    ModuleCat.of (Γ(Y, U)) (TensorProduct Γ(X, V) Γ(Y, U) Γ(N, V))
  letI algSpecΓ : Algebra Γ(Y, U) Γ((Spec Γ(Y, U)), ⊤) :=
    (Scheme.ΓSpecIso _).inv.hom.toAlgebra
  letI modTilde : Module Γ(Y, U) Γ(tilde TR, ⊤) :=
    Module.compHom _ (Scheme.ΓSpecIso Γ(Y, U)).inv.hom
  -- We also need the same Module.compHom-instance on the source of `topAdd`,
  -- matching the one used by `step3` (it is set up there via a `letI` inside
  -- the theorem signature; we restate it here so it is in scope for `topLin`).
  letI modSrc : Module Γ(Y, U) Γ((Scheme.Modules.pullback _hU.fromSpec).obj
      ((Scheme.Modules.pullback g).obj N), ⊤) :=
    Module.compHom _ (Scheme.ΓSpecIso Γ(Y, U)).inv.hom
  -- Step (a): upgrade `topAdd` to Γ(Y, U)-linear via `Hom.app_smul`.
  let topLin : Γ((Scheme.Modules.pullback _hU.fromSpec).obj
        ((Scheme.Modules.pullback g).obj N), ⊤)
        ≃ₗ[Γ(Y, U)] Γ(tilde TR, ⊤) := by
    refine topAdd.toLinearEquiv ?_
    intro r x
    -- Module.compHom on both sides: r • _ = (ΓSpecIso _).inv.hom r • _.
    change (Scheme.Modules.Hom.app composedIso.hom ⊤).hom
      ((Scheme.ΓSpecIso _).inv.hom r • x) =
      (Scheme.ΓSpecIso _).inv.hom r • (Scheme.Modules.Hom.app composedIso.hom ⊤).hom x
    exact Scheme.Modules.Hom.app_smul composedIso.hom _ x
  -- Step (b): chain with `(tilde.isoTop _).symm.toLinearEquiv`.
  let toTensor : Γ((Scheme.Modules.pullback _hU.fromSpec).obj
        ((Scheme.Modules.pullback g).obj N), ⊤) ≃ₗ[Γ(Y, U)]
        TensorProduct Γ(X, V) Γ(Y, U) Γ(N, V) :=
    topLin.trans (tilde.isoTop TR).symm.toLinearEquiv
  -- Step (c): compose with `step3`.
  let f : TensorProduct Γ(X, V) Γ(Y, U) Γ(N, V) ≃ₗ[Γ(Y, U)]
          Γ((Scheme.Modules.pullback g).obj N, U) :=
    toTensor.symm.trans step3
  refine ⟨⟨f, ?_⟩⟩
  intro x
  -- Step (d): Beck-Chevalley intertwining at `1 ⊗ₜ x`.
  --
  -- ARCHITECTURAL UPDATE (iter-195 Σ-pair refactor). With `step1` and
  -- `step2` now carrying iso-characterizing identities `_step1_apply`
  -- and `_step2_apply` as Σ-pair components (the iter-195 plan-phase
  -- refactor `lane-f-step12-sigma-pair`), the LHS unfolds in 6 stages:
  --
  --   Stage 1 (closed via `_step2_apply` + inv_hom_id):
  --     (step2.inv .app ⊤) (tilde.toOpen TR ⊤ (1 ⊗ x))
  --       = baseMap (Spec.map φ) (tilde Γ(N,V)) le_top (tilde.toOpen Γ(N,V) ⊤ x).
  --   Stage 2 ((N1) baseMap naturality + `_step1_apply`):
  --     ((pullback (Spec.map φ)).map step1.inv .app ⊤) (stage 1's RHS)
  --       = baseMap (Spec.map φ) ((pullback _hV.fromSpec) N) le_top
  --         (baseMap _hV.fromSpec N _ x).
  --   Stage 3 ((N2) baseMap composition via pullbackComp):
  --     ((pullbackComp (Spec.map φ) _hV.fromSpec) N .hom .app ⊤) (stage 2's RHS)
  --       = baseMap (Spec.map φ ≫ _hV.fromSpec) N _ x.
  --   Stage 4 ((N3) baseMap transport via pullbackCongr h_eq):
  --     ((pullbackCongr h_eq) N .inv .app ⊤) (stage 3's RHS)
  --       = baseMap (_hU.fromSpec ≫ g) N _ x.
  --   Stage 5 ((N2) baseMap composition via pullbackComp, again):
  --     ((pullbackComp _hU.fromSpec g) N .inv .app ⊤) (stage 4's RHS)
  --       = baseMap _hU.fromSpec ((pullback g) N) le_top' (baseMap g N e x).
  --   Stage 6 ((N4) step3 inversion of baseMap _hU.fromSpec on open imm):
  --     step3 (baseMap _hU.fromSpec ((pullback g) N) le_top' y) = y.
  --
  -- The four substrate helpers (N1)-(N4) are PROVED (T12, 2026-07-03):
  --   (N1) `pullback_app_isoTensor_baseMap_naturality`,
  --   (N2) `pullback_app_isoTensor_baseMap_comp`,
  --   (N3) `pullback_app_isoTensor_baseMap_congr`,
  --   (N4) the Σ-pair characterization `_step3_symm_apply` of
  --        `pullback_of_openImmersion_iso_restrict`.
  -- The stages are assembled below as `congrArg`/`Eq.trans` chains.
  --
  -- Local abbreviations:
  --   ΓNV := ModuleCat.of ↑Γ(X, V) ↑Γ(N, V)
  --   φ := Scheme.Hom.appLE g V U e
  --   ι1 := (pullbackComp _hU.fromSpec g) .app N
  --   ι2 := (pullbackCongr h_eq) .app N
  --   ι3 := ((pullbackComp (Spec.map φ) _hV.fromSpec) .app N).symm
  --   ι4 := (pullback (Spec.map φ)).mapIso step1
  --   ι5 := step2
  -- composedIso = ι1 ≪≫ ι2 ≪≫ ι3 ≪≫ ι4 ≪≫ ι5.
  --
  -- ## Stage 1: invert `_step2_apply` via `step2.hom_inv_id` elementwise.
  have hcancel2 : ∀ (w : Γ((Scheme.Modules.pullback (Spec.map (g.appLE V U e))).obj
      (tilde (ModuleCat.of Γ(X, V) Γ(N, V))), ⊤)),
      (Scheme.Modules.Hom.app step2.inv ⊤).hom
        ((Scheme.Modules.Hom.app step2.hom ⊤).hom w) = w := fun w =>
    congrArg (fun (k : (Scheme.Modules.pullback (Spec.map (g.appLE V U e))).obj
        (tilde (ModuleCat.of Γ(X, V) Γ(N, V))) ⟶
        (Scheme.Modules.pullback (Spec.map (g.appLE V U e))).obj
        (tilde (ModuleCat.of Γ(X, V) Γ(N, V)))) =>
      (Scheme.Modules.Hom.app k ⊤).hom w) step2.hom_inv_id
  have h1 := (congrArg (fun w => (Scheme.Modules.Hom.app step2.inv ⊤).hom w)
    (_step2_apply x).symm).trans (hcancel2 _)
  -- ## Stage 2: (N1) naturality along `step1.inv`, then `_step1_apply`.
  -- (The `⊤`-opens must be pinned explicitly: a bare `le_top` collapses
  -- `Spec.map φ ⁻¹ᵁ ⊤` to `⊤` and leaves the lemma's opens as metavariables.)
  have h2 := (pullback_app_isoTensor_baseMap_naturality (Spec.map (g.appLE V U e))
      step1.inv (U := (⊤ : (Spec Γ(Y, U)).Opens)) (V := (⊤ : (Spec Γ(X, V)).Opens))
      le_top ((tilde.toOpen (ModuleCat.of Γ(X, V) Γ(N, V)) ⊤).hom x)).trans
    (congrArg (fun w => pullback_app_isoTensor_baseMap (Spec.map (g.appLE V U e))
      ((Scheme.Modules.pullback _hV.fromSpec).obj N)
      (U := (⊤ : (Spec Γ(Y, U)).Opens)) (V := (⊤ : (Spec Γ(X, V)).Opens))
      le_top w) (_step1_apply x))
  -- ## Stage 3: (N2) composition through `pullbackComp (Spec.map φ) hV.fromSpec`.
  have eTU3 : (⊤ : (Spec Γ(Y, U)).Opens) ≤
      (Spec.map (g.appLE V U e) ≫ _hV.fromSpec) ⁻¹ᵁ V := by
    rw [Scheme.Hom.comp_preimage, _hV.fromSpec_preimage_self]
    exact le_top
  have h3 := pullback_app_isoTensor_baseMap_comp (Spec.map (g.appLE V U e)) _hV.fromSpec N
    (le_of_eq _hV.fromSpec_preimage_self.symm) le_top eTU3 x
  -- ## Stage 4: (N3) transport along `pullbackCongr h_eq.symm`.
  have eTU4 : (⊤ : (Spec Γ(Y, U)).Opens) ≤ (_hU.fromSpec ≫ g) ⁻¹ᵁ V := by
    rw [Scheme.Hom.comp_preimage]
    exact le_trans (le_of_eq _hU.fromSpec_preimage_self.symm) (fun a ha => e ha)
  have h4 := pullback_app_isoTensor_baseMap_congr h_eq.symm N eTU3 eTU4 x
  -- ## Stage 5: (N2) inverted, through `pullbackComp hU.fromSpec g`.
  have h5' := pullback_app_isoTensor_baseMap_comp _hU.fromSpec g N e
    (le_of_eq _hU.fromSpec_preimage_self.symm) eTU4 x
  have hcancel1 : ∀ (w : Γ((Scheme.Modules.pullback _hU.fromSpec).obj
      ((Scheme.Modules.pullback g).obj N), ⊤)),
      (Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackComp _hU.fromSpec g).inv.app N) ⊤).hom
        ((Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackComp _hU.fromSpec g).hom.app N) ⊤).hom w) = w :=
    fun w => congrArg (fun (k : (Scheme.Modules.pullback g ⋙
        Scheme.Modules.pullback _hU.fromSpec).obj N ⟶
        (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback _hU.fromSpec).obj N) =>
      (Scheme.Modules.Hom.app k ⊤).hom w)
      (Iso.hom_inv_id_app (Scheme.Modules.pullbackComp _hU.fromSpec g) N)
  have h5 := (congrArg (fun w =>
    (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackComp _hU.fromSpec g).inv.app N) ⊤).hom w)
    h5'.symm).trans (hcancel1 _)
  -- ## Stage 6: (N4) `step3` inversion via `_step3_symm_apply`.
  have h6 := (congrArg (fun w => step3 w)
    (_step3_symm_apply (pullback_app_isoTensor_baseMap g N e x)).symm).trans
    (step3.apply_symm_apply (pullback_app_isoTensor_baseMap g N e x))
  -- ## Assembly: decompose `f (1 ⊗ x)` through the iso chain and chain the stages.
  change step3
    ((Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackComp _hU.fromSpec g).inv.app N) ⊤).hom
      ((Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackCongr h_eq).inv.app N) ⊤).hom
        ((Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackComp (Spec.map (g.appLE V U e))
              _hV.fromSpec).hom.app N) ⊤).hom
          ((Scheme.Modules.Hom.app
              ((Scheme.Modules.pullback (Spec.map (g.appLE V U e))).map step1.inv) ⊤).hom
            ((Scheme.Modules.Hom.app step2.inv ⊤).hom
              ((tilde.toOpen TR ⊤).hom (1 ⊗ₜ[Γ(X, V)] x))))))) =
    pullback_app_isoTensor_baseMap g N e x
  exact (congrArg (fun w => step3
      ((Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackComp _hU.fromSpec g).inv.app N) ⊤).hom
        ((Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackCongr h_eq).inv.app N) ⊤).hom
          ((Scheme.Modules.Hom.app
              ((Scheme.Modules.pullbackComp (Spec.map (g.appLE V U e))
                _hV.fromSpec).hom.app N) ⊤).hom
            ((Scheme.Modules.Hom.app
                ((Scheme.Modules.pullback (Spec.map (g.appLE V U e))).map
                  step1.inv) ⊤).hom w))))) h1).trans
    ((congrArg (fun w => step3
      ((Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackComp _hU.fromSpec g).inv.app N) ⊤).hom
        ((Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackCongr h_eq).inv.app N) ⊤).hom
          ((Scheme.Modules.Hom.app
              ((Scheme.Modules.pullbackComp (Spec.map (g.appLE V U e))
                _hV.fromSpec).hom.app N) ⊤).hom w)))) h2).trans
      ((congrArg (fun w => step3
        ((Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackComp _hU.fromSpec g).inv.app N) ⊤).hom
          ((Scheme.Modules.Hom.app
              ((Scheme.Modules.pullbackCongr h_eq).inv.app N) ⊤).hom w))) h3).trans
        ((congrArg (fun w => step3
          ((Scheme.Modules.Hom.app
              ((Scheme.Modules.pullbackComp _hU.fromSpec g).inv.app N) ⊤).hom w))
            h4).trans
          ((congrArg (fun w => step3 w) h5).trans h6))))

/-- **Substantive `IsBaseChange` claim** for the affine-open section formula
(iter-187 Lane F — analogist-informed refactor; iter-188 closes axiom-clean
via the named section-LinearEquiv helper).

Per iter-187 analogist verdict (`analogies/quotscheme-isbasechange-tilde.md`):
the iso comes from the named Spec-level helper `pullback_tildeIso`
combined with `TensorProduct.isBaseChange` + `IsBaseChange.of_equiv`; the
substantive Mathlib gap (Stacks tag 01HQ / 0BJ8: "pullback of tilde =
tilde of base change") is *factored* into the standalone helper
`pullback_tildeIso` above.

The hypothesis `[N.IsQuasicoherent]` is added per analogist Decision 3:
the Tilde-route strictly requires `N|_V ∈ essImage tilde` on
`Spec(Γ(X, V))`, which follows from quasi-coherence + `hV.isoSpec`.

**iter-188 closure**: body assembled via the named helper
`pullback_app_isoTensor_baseMap_sectionLinearEquiv` (which packages the
LinearEquiv with the intertwining property) combined with
`IsBaseChange.of_equiv`. The body itself is axiom-clean; the residual
Mathlib gap (Stacks 01HQ transport) is fully localized in the named
helper's typed sorry. -/
private theorem pullback_app_isoTensor_baseMap_isBaseChange
    {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules) [N.IsQuasicoherent]
    {U : Y.Opens} {V : X.Opens}
    (_hU : IsAffineOpen U) (_hV : IsAffineOpen V)
    (e : U ≤ g ⁻¹ᵁ V) :
    letI : Algebra Γ(X, V) Γ(Y, U) := (g.appLE V U e).hom.toAlgebra
    letI : Module Γ(X, V) Γ((Scheme.Modules.pullback g).obj N, U) :=
      Module.compHom _ (g.appLE V U e).hom
    haveI : IsScalarTower Γ(X, V) Γ(Y, U) Γ((Scheme.Modules.pullback g).obj N, U) :=
      .of_algebraMap_smul fun _ _ ↦ rfl
    IsBaseChange Γ(Y, U) (pullback_app_isoTensor_baseMap g N e) := by
  letI : Algebra Γ(X, V) Γ(Y, U) := (g.appLE V U e).hom.toAlgebra
  letI : Module Γ(X, V) Γ((Scheme.Modules.pullback g).obj N, U) :=
    Module.compHom _ (g.appLE V U e).hom
  haveI : IsScalarTower Γ(X, V) Γ(Y, U) Γ((Scheme.Modules.pullback g).obj N, U) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  -- Extract the section-level LinearEquiv with its intertwining property
  -- from the named helper. The substantive Mathlib-gap content
  -- (Stacks 01HQ transport) is fully localized inside the helper.
  obtain ⟨equiv, hApp⟩ := pullback_app_isoTensor_baseMap_sectionLinearEquiv g N _hU _hV e
  -- Apply `IsBaseChange.of_equiv`: from an equiv `TensorProduct R S M ≃ N`
  -- that intertwines the canonical `m ↦ 1 ⊗ m` with `f`, conclude
  -- `IsBaseChange S f`.
  exact IsBaseChange.of_equiv equiv hApp

/-- **Combined Tilde-isoTop content**: the IsBaseChange witness `.equiv.symm`
gives the desired affine-open section formula iso.

iter-187 Lane F: `[N.IsQuasicoherent]` hypothesis added per analogist
Decision 3 — required by the Tilde route and natural for the Stacks 02KH
consumer chain. -/
private theorem pullback_app_isoTensor_isBaseChange
    {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules) [N.IsQuasicoherent]
    {U : Y.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ g ⁻¹ᵁ V) :
    letI : Algebra Γ(X, V) Γ(Y, U) := (g.appLE V U e).hom.toAlgebra
    Nonempty (Γ((Scheme.Modules.pullback g).obj N, U) ≃ₗ[Γ(Y, U)]
      TensorProduct Γ(X, V) Γ(Y, U) Γ(N, V)) := by
  letI : Algebra Γ(X, V) Γ(Y, U) := (g.appLE V U e).hom.toAlgebra
  letI : Module Γ(X, V) Γ((Scheme.Modules.pullback g).obj N, U) :=
    Module.compHom _ (g.appLE V U e).hom
  haveI : IsScalarTower Γ(X, V) Γ(Y, U) Γ((Scheme.Modules.pullback g).obj N, U) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  -- iter-186 Lane F Step 2 (DONE axiom-clean): baseMap built above.
  -- iter-187+ Lane F Step 3+4: the IsBaseChange Prop carries the
  -- Tilde-isoTop substantive content in
  -- `pullback_app_isoTensor_baseMap_isBaseChange`. Once that closes,
  -- `.equiv.symm` axiom-cleans this theorem.
  exact ⟨(pullback_app_isoTensor_baseMap_isBaseChange g N hU hV e).equiv.symm⟩

/-- **Affine-open section formula for the module pullback** (iter-185 Lane F:
PIVOT — body discharges via `pullback_app_isoTensor_isBaseChange`).

Closes axiom-clean given the named substantive helper above. The pre-iter-185
unnamed body sorry has been *replaced* by the named typed sorry inside
`pullback_app_isoTensor_isBaseChange`, plus the axiom-clean construction of
the underlying base linear map in `pullback_app_isoTensor_unitAtV`.

iter-187 Lane F: `[N.IsQuasicoherent]` hypothesis added (analogist
Decision 3). -/
noncomputable def Scheme.Modules.pullback_app_isoTensor
    {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules) [N.IsQuasicoherent]
    {U : Y.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ g ⁻¹ᵁ V) :
    letI : Algebra Γ(X, V) Γ(Y, U) := (g.appLE V U e).hom.toAlgebra
    Γ((Scheme.Modules.pullback g).obj N, U) ≃ₗ[Γ(Y, U)]
      TensorProduct Γ(X, V) Γ(Y, U) Γ(N, V) := by
  letI : Algebra Γ(X, V) Γ(Y, U) := (g.appLE V U e).hom.toAlgebra
  -- iter-185 Lane F substantive step: body closes via the named helper
  -- `pullback_app_isoTensor_isBaseChange` (typed sorry on the algebraic
  -- Stacks 02KE / 01HQ content). The `unitAtV` linear map factoring
  -- through the adjunction is built axiom-clean as
  -- `pullback_app_isoTensor_unitAtV`. Iter-186+ closes the helper body
  -- via the Tilde-isoTop route.
  exact (pullback_app_isoTensor_isBaseChange g N hU hV e).some

/-! ### Lane F endgame (T12 fbc-leaves front, 2026-07-06)

The three `canonicalBaseChangeMap_app_app_isIso_*` leaves close through ONE
workhorse (`canonicalBaseChangeMap_app_app_isIso_of_le_preimage`): the
section of the canonical mate is an iso at every affine `U ⊆ S'` compatible
with an affine `V ⊆ S` (`U ≤ g ⁻¹ᵁ V`).  The workhorse compares two
witnesses trivializing `Γ(g^* f_* F, U)` and `Γ(f'_* g'^* F, U)` as
`Γ(S', U) ⊗_{Γ(S, V)} Γ(F, f ⁻¹ᵁ V)`:

* the LHS witness is the (sorry-free) Tilde-route section formula
  `pullback_app_isoTensor_baseMap_sectionLinearEquiv` applied to the
  quasi-coherent pushforward `f_* F` (Stacks 01XJ);
* the RHS witness is the **H⁰ flat-base-change heart** (Stacks 02KE),
  `pullback_baseMap_sectionLinearEquiv_of_quasiCompact` (CLOSED, T13
  2026-07-07, via the finite-affine-cover equalizer ladder);
* the canonical mate intertwines the two witnesses on the tensor
  generators `1 ⊗ x` by the PROVED elementwise Beck-Chevalley
  compatibility `canonicalBaseChangeMap_app_baseMap_compat` (KEY-BC),
  hence everywhere by `Γ(S', U)`-linearity; being a two-sided composite
  of bijections it is bijective.

The affine-base leaf is the specialization `V := ⊤`; the general
affine-open leaf follows because the compatible affine pairs form a basis
of `S'` (no square-restriction/Mayer-Vietoris needed — the historically
walled mate-restriction naturality is bypassed). -/

set_option backward.isDefEq.respectTransparency false in
/-- **`baseMap` at a reflexive inclusion is the raw adjunction unit** (the
`homOfLE le_rfl = 𝟙` restriction collapses by `Functor.map_id`). Bridges the
unit stage of the canonical mate to the `pullback_app_isoTensor_baseMap` form
consumed by the (N1)/(N2)/(N3) coherence lemmas. Project-local. -/
private lemma pullback_app_isoTensor_baseMap_le_refl
    {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules) (V : X.Opens) (x : Γ(N, V)) :
    pullback_app_isoTensor_baseMap g N (le_refl (g ⁻¹ᵁ V)) x =
      (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N) V).hom x := by
  change ((((Scheme.Modules.pullback g).obj N).presheaf.map
      (homOfLE (le_refl (g ⁻¹ᵁ V))).op).hom)
      ((Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N) V).hom x) = _
  rw [show (homOfLE (le_refl (g ⁻¹ᵁ V))).op = 𝟙 (Opposite.op (g ⁻¹ᵁ V)) from rfl,
    CategoryTheory.Functor.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
-- The Beck--Chevalley calculation expands the mate, adjunction units, and restriction transports.
/-- **KEY-BC: elementwise Beck-Chevalley compatibility of the canonical
base-change mate with the adjunction-unit base maps** (T12 fbc-leaves front,
PROVED 2026-07-06).

For a cartesian square `sq : IsPullback g' f' f g` and opens `V ⊆ S`,
`U ⊆ S'` with `U ≤ g ⁻¹ᵁ V`, the `U`-section of the canonical mate
`canonicalBaseChangeMap sq` sends the canonical base-map image
`baseMap_g(t) ∈ Γ(g^* f_* F, U)` of a section `t ∈ Γ(f_* F, V) = Γ(F, f ⁻¹ᵁ V)`
to the canonical base-map image `baseMap_{g'}(t) ∈ Γ(g'^* F, f' ⁻¹ᵁ U) =
Γ(f'_* g'^* F, U)` along the primed leg. **No flatness, quasi-compactness or
affineness is needed** — this is pure unit/counit/pseudofunctor coherence of
the mate (`CategoryTheory.mateEquiv`).

Proof: the mate's component at `F` unfolds (definitionally, all `Cat`
unitor/associator components being identities) to
`unit_{f'} ≫ f'_*(pullbackComp/pullbackCongr chain at f_* F) ≫ f'_*(g'^*(counit_f))`.
Evaluating elementwise on `baseMap_g(t)`: the unit stage is the reflexive base
map (`pullback_app_isoTensor_baseMap_le_refl`); the `pullbackComp f' g` stage
composes the iterated base maps to `baseMap_{f' ≫ g}(t)` ((N2)
`pullback_app_isoTensor_baseMap_comp`); the `pullbackCongr sq.w.symm` stage
transports to `baseMap_{g' ≫ f}(t)` ((N3) `..._congr`); the inverse
`pullbackComp g' f` stage splits it as `baseMap_{g'}(baseMap_f(t))` ((N2) +
hom-inv cancellation); naturality of the base map along the counit ((N1)
`..._naturality`) and the right-triangle identity
`unit_f ≫ f_*(counit_f) = 𝟙` collapse the inner layer to `t`.

Source: Stacks Project 02KH (construction of the base-change map);
the statement is the mate-vs-unit compatibility square of the
Beck-Chevalley transform, cf. `CategoryTheory.unit_mateEquiv`. -/
theorem canonicalBaseChangeMap_app_baseMap_compat
    {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g)
    (F : X.Modules) {V : S.Opens} {U : S'.Opens}
    (e : U ≤ g ⁻¹ᵁ V) (e'' : f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ V))
    (t : Γ((Scheme.Modules.pushforward f).obj F, V)) :
    (((canonicalBaseChangeMap sq).app F).app U).hom
        (pullback_app_isoTensor_baseMap g ((Scheme.Modules.pushforward f).obj F) e t) =
      pullback_app_isoTensor_baseMap g' F e'' t := by
  -- Preimage inclusions along the two legs of the square.
  have e₂ : f' ⁻¹ᵁ U ≤ (f' ≫ g) ⁻¹ᵁ V := by
    rw [Scheme.Hom.comp_preimage]
    exact fun a ha => e ha
  have e₃ : f' ⁻¹ᵁ U ≤ (g' ≫ f) ⁻¹ᵁ V := by
    rw [sq.w, Scheme.Hom.comp_preimage]
    exact fun a ha => e ha
  -- Stage 1: the `f'`-unit stage is the reflexive-inclusion base map.
  have h1 := pullback_app_isoTensor_baseMap_le_refl f'
    ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F)) U
    (pullback_app_isoTensor_baseMap g ((Scheme.Modules.pushforward f).obj F) e t)
  -- Stage 2 (N2): compose the iterated base maps through `pullbackComp f' g`.
  have h2 := pullback_app_isoTensor_baseMap_comp f' g
    ((Scheme.Modules.pushforward f).obj F) e (le_refl (f' ⁻¹ᵁ U)) e₂ t
  -- Stage 3 (N3): transport along `pullbackCongr sq.w.symm`.
  have h3 := pullback_app_isoTensor_baseMap_congr sq.w.symm
    ((Scheme.Modules.pushforward f).obj F) e₂ e₃ t
  -- Stage 4 (N2 inverted): split `baseMap (g' ≫ f)` through `pullbackComp g' f`.
  have h4' := pullback_app_isoTensor_baseMap_comp g' f
    ((Scheme.Modules.pushforward f).obj F) (le_refl (f ⁻¹ᵁ V)) e'' e₃ t
  have hcancel : ∀ w : Γ((Scheme.Modules.pullback g').obj
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj F)),
        f' ⁻¹ᵁ U),
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g' f).inv.app
          ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom
        ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g' f).hom.app
          ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom w) = w :=
    fun w => congrArg
      (fun (k : (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g').obj
          ((Scheme.Modules.pushforward f).obj F) ⟶
          (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g').obj
          ((Scheme.Modules.pushforward f).obj F)) =>
        (Scheme.Modules.Hom.app k (f' ⁻¹ᵁ U)).hom w)
      (Iso.hom_inv_id_app (Scheme.Modules.pullbackComp g' f)
        ((Scheme.Modules.pushforward f).obj F))
  have h4 := (congrArg (fun w =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g' f).inv.app
      ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom w) h4'.symm).trans
    (hcancel _)
  -- Stage 5 (N1): naturality of the base map along the `f`-counit.
  have h5 := pullback_app_isoTensor_baseMap_naturality g'
    ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F) e''
    (pullback_app_isoTensor_baseMap f ((Scheme.Modules.pushforward f).obj F)
      (le_refl (f ⁻¹ᵁ V)) t)
  -- Stage 6: the right-triangle identity collapses counit ∘ unit to the identity.
  have h6a := pullback_app_isoTensor_baseMap_le_refl f
    ((Scheme.Modules.pushforward f).obj F) V t
  have h6b := congrArg
    (fun (k : (Scheme.Modules.pushforward f).obj F ⟶
        (Scheme.Modules.pushforward f).obj F) =>
      (Scheme.Modules.Hom.app k V).hom t)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).right_triangle_components F)
  have h6 : (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F) (f ⁻¹ᵁ V)).hom
      (pullback_app_isoTensor_baseMap f ((Scheme.Modules.pushforward f).obj F)
        (le_refl (f ⁻¹ᵁ V)) t) = t :=
    (congrArg (fun w => (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F)
      (f ⁻¹ᵁ V)).hom w) h6a).trans h6b
  -- Decompose the canonical mate elementwise (all unitor/associator components
  -- are identities in `Cat`; compositions of section maps are definitional).
  change (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g').map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F)) (f' ⁻¹ᵁ U)).hom
      ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g' f).inv.app
          ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom
        ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr sq.w.symm).hom.app
            ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom
          ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f' g).hom.app
              ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom
            ((Scheme.Modules.Hom.app
                ((Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
                  ((Scheme.Modules.pullback g).obj
                    ((Scheme.Modules.pushforward f).obj F))) U).hom
              (pullback_app_isoTensor_baseMap g
                ((Scheme.Modules.pushforward f).obj F) e t))))) =
    pullback_app_isoTensor_baseMap g' F e'' t
  -- Assemble the stages.
  refine (congrArg (fun w =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g').map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F)) (f' ⁻¹ᵁ U)).hom
      ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g' f).inv.app
          ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom
        ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr sq.w.symm).hom.app
            ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom
          ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f' g).hom.app
              ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom w))))
    h1.symm).trans ?_
  refine (congrArg (fun w =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g').map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F)) (f' ⁻¹ᵁ U)).hom
      ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g' f).inv.app
          ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom
        ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr sq.w.symm).hom.app
            ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom w)))
    h2).trans ?_
  refine (congrArg (fun w =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g').map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F)) (f' ⁻¹ᵁ U)).hom
      ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g' f).inv.app
          ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom w))
    h3).trans ?_
  refine (congrArg (fun w =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g').map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F)) (f' ⁻¹ᵁ U)).hom w)
    h4).trans ?_
  exact h5.trans
    (congrArg (fun w => pullback_app_isoTensor_baseMap g' F e'' w) h6)

set_option backward.isDefEq.respectTransparency false in
/-- **Cover pieces of the 02KE ladder are affine**: for a cartesian square and
affine opens `V ⊆ S`, `U ⊆ S'`, `V' ⊆ X` with `U ≤ g ⁻¹ᵁ V` and
`V' ≤ f ⁻¹ᵁ V`, the open `g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U ⊆ X'` is affine (it is the
fibre product `V' ×_V U` of affines over an affine, via the restricted
cartesian square `Scheme.Hom.isPullback_resLE`). Brick for
`pullback_baseMap_sectionLinearEquiv_of_quasiCompact` (Stacks 02KE). -/
private lemma isAffineOpen_preimage_inf_preimage_of_isPullback
    {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g)
    {V : S.Opens} {U : S'.Opens} {V' : X.Opens}
    (hV : IsAffineOpen V) (hU : IsAffineOpen U) (hV' : IsAffineOpen V')
    (e : U ≤ g ⁻¹ᵁ V) (hle : V' ≤ f ⁻¹ᵁ V) :
    IsAffineOpen (g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) := by
  have : IsAffine _ := hV
  have : IsAffine _ := hU
  have : IsAffine _ := hV'
  exact .of_isIso (Scheme.Hom.isPullback_resLE sq e hle rfl).isoPullback.hom

/-- **Flatness of the section algebra of a flat morphism at a compatible
affine pair**: `Γ(S', U)` is a flat `Γ(S, V)`-algebra (affine-locality of
flatness, `Scheme.Hom.flat_appLE`). Brick for
`pullback_baseMap_sectionLinearEquiv_of_quasiCompact` (Stacks 02KE). -/
private lemma flat_gamma_appLE_of_flat
    {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g]
    {V : S.Opens} {U : S'.Opens}
    (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ g ⁻¹ᵁ V) :
    letI : Algebra Γ(S, V) Γ(S', U) := (g.appLE V U e).hom.toAlgebra
    Module.Flat Γ(S, V) Γ(S', U) :=
  g.flat_appLE hV hU e

/-! #### The 02KE ladder (T13, 2026-07-07): geometric instantiation of
`SectionBaseChange.exists_linearEquiv_of_gluing`.

The bricks below feed the abstract equalizer ladder of
`AlgebraicJacobian.Picard.SectionBaseChange` with the geometric data of the
cartesian square: `appLE_square_comm` (the section-ring square commutes),
`appLE_smul_res`/`pushforwardResₗ`/`appLEResₗ` (restriction maps as linear maps
over the affine ground rings), `pullback_app_isoTensor_baseMap_res` (the
canonical base map commutes with restriction — unit naturality), `baseMapALin`/
`sectionBaseChangeθ` (the comparison map `B ⊗_A Γ(F, V') → Γ(g'^*F, W')`),
`sectionBaseChangeθ_bijective` (affine pieces: ring pushout + pinned affine
section formula) and `sectionBaseChangeθ_injective_of_isCompact` (overlaps:
one further finite affine descent). `pullback_baseMap_sectionLinearEquiv_of_cover`
assembles the ladder over a given finite affine cover. -/

section SectionBaseChangeLadder

open TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
/-- **The section-ring square of a cartesian square commutes at compatible opens**:
`g'♯ ∘ f♯ = f'♯ ∘ g♯` on `appLE` section maps, from `sq.w` and
`Scheme.Hom.appLE_comp_appLE`. Brick for the 02KE ladder. -/
private lemma appLE_square_comm {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g)
    {V : S.Opens} {U : S'.Opens} {V' : X.Opens} {W' : X'.Opens}
    (e : U ≤ g ⁻¹ᵁ V) (h1 : V' ≤ f ⁻¹ᵁ V) (h2 : W' ≤ g' ⁻¹ᵁ V') (h3 : W' ≤ f' ⁻¹ᵁ U) :
    (g'.appLE V' W' h2).hom.comp (f.appLE V V' h1).hom
      = (f'.appLE U W' h3).hom.comp (g.appLE V U e).hom := by
  have hL := Scheme.Hom.appLE_comp_appLE g' f V V' W' h1 h2
  have hR := Scheme.Hom.appLE_comp_appLE f' g V U W' e h3
  have hmid : (g' ≫ f).appLE V W' (h2.trans ((Opens.map g'.base).map (homOfLE h1)).le)
      = (f' ≫ g).appLE V W' (h3.trans ((Opens.map f'.base).map (homOfLE e)).le) := by
    congr 1
    exact sq.w
  exact congrArg CommRingCat.Hom.hom (hL.trans (hmid.trans hR.symm))

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of module sections is semilinear over the ground ring acting through
`appLE` at both levels. Brick for the `A`-linear restriction maps of the 02KE ladder. -/
private lemma appLE_smul_res {X S : Scheme.{u}} (f : X ⟶ S) (N : X.Modules) {V : S.Opens}
    {W₂ W₁ : X.Opens} (p₂ : W₂ ≤ f ⁻¹ᵁ V) (p₁ : W₁ ≤ f ⁻¹ᵁ V) (h : W₁ ≤ W₂)
    (r : Γ(S, V)) (ξ : Γ(N, W₂)) :
    N.presheaf.map (homOfLE h).op ((f.appLE V W₂ p₂).hom r • ξ)
      = (f.appLE V W₁ p₁).hom r • N.presheaf.map (homOfLE h).op ξ := by
  rw [Scheme.Modules.map_smul N (homOfLE h) ((f.appLE V W₂ p₂).hom r) ξ]
  refine congrArg (· • N.presheaf.map (homOfLE h).op ξ) ?_
  change X.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE p₂).op ((f.app V).hom r))
      = X.presheaf.map (homOfLE p₁).op ((f.app V).hom r)
  exact Scheme.Modules.resRing_res p₂ h p₁ ((f.app V).hom r)

set_option backward.isDefEq.respectTransparency false in
/-- The section restriction from the pushforward level `Γ(f_*F, V) = Γ(F, f ⁻¹ᵁ V)` to a
smaller open `W ≤ f ⁻¹ᵁ V`, as a `Γ(S, V)`-linear map (native pushforward action upstairs,
`appLE`-restricted action downstairs). -/
private noncomputable def pushforwardResₗ {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    {V : S.Opens} {W : X.Opens} (hW : W ≤ f ⁻¹ᵁ V) :
    letI : Module Γ(S, V) Γ(F, W) := Module.compHom _ (f.appLE V W hW).hom
    Γ((Scheme.Modules.pushforward f).obj F, V) →ₗ[Γ(S, V)] Γ(F, W) :=
  letI : Module Γ(S, V) Γ(F, W) := Module.compHom _ (f.appLE V W hW).hom
  { toFun := fun x => F.presheaf.map (homOfLE hW).op x
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r x => Scheme.Modules.map_smul F (homOfLE hW) ((f.app V).hom r) x }

set_option backward.isDefEq.respectTransparency false in
/-- The section restriction between two opens below `f ⁻¹ᵁ V`, as a `Γ(S, V)`-linear map
for the `appLE`-restricted scalar actions. -/
private noncomputable def appLEResₗ {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    {V : S.Opens} {W₂ W₁ : X.Opens} (p₂ : W₂ ≤ f ⁻¹ᵁ V) (p₁ : W₁ ≤ f ⁻¹ᵁ V) (h : W₁ ≤ W₂) :
    letI : Module Γ(S, V) Γ(F, W₂) := Module.compHom _ (f.appLE V W₂ p₂).hom
    letI : Module Γ(S, V) Γ(F, W₁) := Module.compHom _ (f.appLE V W₁ p₁).hom
    Γ(F, W₂) →ₗ[Γ(S, V)] Γ(F, W₁) :=
  letI : Module Γ(S, V) Γ(F, W₂) := Module.compHom _ (f.appLE V W₂ p₂).hom
  letI : Module Γ(S, V) Γ(F, W₁) := Module.compHom _ (f.appLE V W₁ p₁).hom
  { toFun := fun x => F.presheaf.map (homOfLE h).op x
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r x => appLE_smul_res f F p₂ p₁ h r x }

set_option backward.isDefEq.respectTransparency false in
/-- **`baseMap` commutes with restriction** (step (6) of the 02KE plan): for
`V'' ≤ V'`, `W'' ≤ W'` with `W' ≤ g ⁻¹ᵁ V'`, `W'' ≤ g ⁻¹ᵁ V''`, restricting the
canonical base-map image equals the base-map image of the restriction. From
naturality of the adjunction unit in the open + restriction collapse. -/
private lemma pullback_app_isoTensor_baseMap_res {X Y : Scheme.{u}} (g : Y ⟶ X)
    (N : X.Modules) {V' V'' : X.Opens} {W' W'' : Y.Opens}
    (hW' : W' ≤ g ⁻¹ᵁ V') (hW'' : W'' ≤ g ⁻¹ᵁ V'')
    (hV : V'' ≤ V') (hW : W'' ≤ W') (x : Γ(N, V')) :
    (((Scheme.Modules.pullback g).obj N).presheaf.map (homOfLE hW).op).hom
        (pullback_app_isoTensor_baseMap g N hW' x)
      = pullback_app_isoTensor_baseMap g N hW'' ((N.presheaf.map (homOfLE hV).op).hom x) := by
  have hnat := congrArg
    (fun (k : Γ(N, V') ⟶
        Γ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj N), V'')) =>
      (AddCommGrpCat.Hom.hom k) x)
    ((Scheme.Modules.Hom.mapPresheaf
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N)).naturality
      (homOfLE hV).op)
  have hL := modules_res_res_hom ((Scheme.Modules.pullback g).obj N)
    (homOfLE hW) (homOfLE hW') (homOfLE (hW.trans hW'))
    ((Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N) V').hom x)
  have hR := modules_res_res_hom ((Scheme.Modules.pullback g).obj N)
    (homOfLE hW'') ((Opens.map g.base).map (homOfLE hV)) (homOfLE (hW.trans hW'))
    ((Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N) V').hom x)
  change (((Scheme.Modules.pullback g).obj N).presheaf.map (homOfLE hW).op).hom
      ((((Scheme.Modules.pullback g).obj N).presheaf.map (homOfLE hW').op).hom
        ((Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N) V').hom x))
    = (((Scheme.Modules.pullback g).obj N).presheaf.map (homOfLE hW'').op).hom
        ((Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N) V'').hom
          ((N.presheaf.map (homOfLE hV).op).hom x))
  rw [hL]
  refine hR.symm.trans ?_
  exact (congrArg
    (fun w => (((Scheme.Modules.pullback g).obj N).presheaf.map (homOfLE hW'').op).hom w)
    hnat).symm

set_option backward.isDefEq.respectTransparency false in
/-- The canonical base map `Γ(F, V') → Γ(g'^*F, W')` as a `Γ(S, V)`-linear map,
`Γ(S, V)` acting through `f.appLE` on the source and through `f'.appLE ∘ g.appLE` on
the target (the two routes around the cartesian square agree by `appLE_square_comm`). -/
private noncomputable def baseMapALin {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) (F : X.Modules)
    {V : S.Opens} {U : S'.Opens} (e : U ≤ g ⁻¹ᵁ V)
    {V' : X.Opens} {W' : X'.Opens}
    (hV' : V' ≤ f ⁻¹ᵁ V) (hW'V : W' ≤ g' ⁻¹ᵁ V') (hW'U : W' ≤ f' ⁻¹ᵁ U) :
    letI : Module Γ(S, V) Γ(F, V') := Module.compHom _ (f.appLE V V' hV').hom
    letI : Module Γ(S, V) Γ((Scheme.Modules.pullback g').obj F, W') :=
      Module.compHom _ ((f'.appLE U W' hW'U).hom.comp (g.appLE V U e).hom)
    Γ(F, V') →ₗ[Γ(S, V)] Γ((Scheme.Modules.pullback g').obj F, W') := by
  letI : Module Γ(S, V) Γ(F, V') := Module.compHom _ (f.appLE V V' hV').hom
  letI : Module Γ(X, V') Γ((Scheme.Modules.pullback g').obj F, W') :=
    Module.compHom _ (g'.appLE V' W' hW'V).hom
  letI : Module Γ(S, V) Γ((Scheme.Modules.pullback g').obj F, W') :=
    Module.compHom _ ((f'.appLE U W' hW'U).hom.comp (g.appLE V U e).hom)
  refine
    { toFun := fun m => pullback_app_isoTensor_baseMap g' F hW'V m
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r m => ?_ }
  have hsm := (pullback_app_isoTensor_baseMap g' F hW'V).map_smul
    ((f.appLE V V' hV').hom r) m
  have hring : (g'.appLE V' W' hW'V).hom ((f.appLE V V' hV').hom r)
      = (f'.appLE U W' hW'U).hom ((g.appLE V U e).hom r) :=
    congrArg (fun (ρ : Γ(S, V) →+* Γ(X', W')) => ρ r)
      (appLE_square_comm sq e hV' hW'V hW'U)
  change pullback_app_isoTensor_baseMap g' F hW'V ((f.appLE V V' hV').hom r • m)
      = (f'.appLE U W' hW'U).hom ((g.appLE V U e).hom r) •
          pullback_app_isoTensor_baseMap g' F hW'V m
  exact hsm.trans
    (congrArg (· • pullback_app_isoTensor_baseMap g' F hW'V m) hring)

set_option backward.isDefEq.respectTransparency false in
/-- **The canonical 02KE comparison map**
`Γ(S', U) ⊗_{Γ(S, V)} Γ(F, V') →ₗ[Γ(S', U)] Γ(g'^*F, W')` (lift of the base map along
the flat base ring extension). -/
private noncomputable def sectionBaseChangeθ {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) (F : X.Modules)
    {V : S.Opens} {U : S'.Opens} (e : U ≤ g ⁻¹ᵁ V)
    {V' : X.Opens} {W' : X'.Opens}
    (hV' : V' ≤ f ⁻¹ᵁ V) (hW'V : W' ≤ g' ⁻¹ᵁ V') (hW'U : W' ≤ f' ⁻¹ᵁ U) :
    letI : Algebra Γ(S, V) Γ(S', U) := (g.appLE V U e).hom.toAlgebra
    letI : Module Γ(S, V) Γ(F, V') := Module.compHom _ (f.appLE V V' hV').hom
    letI : Module Γ(S', U) Γ((Scheme.Modules.pullback g').obj F, W') :=
      Module.compHom _ (f'.appLE U W' hW'U).hom
    TensorProduct Γ(S, V) Γ(S', U) Γ(F, V') →ₗ[Γ(S', U)]
      Γ((Scheme.Modules.pullback g').obj F, W') := by
  letI : Algebra Γ(S, V) Γ(S', U) := (g.appLE V U e).hom.toAlgebra
  letI : Module Γ(S, V) Γ(F, V') := Module.compHom _ (f.appLE V V' hV').hom
  letI : Module Γ(S', U) Γ((Scheme.Modules.pullback g').obj F, W') :=
    Module.compHom _ (f'.appLE U W' hW'U).hom
  letI : Module Γ(S, V) Γ((Scheme.Modules.pullback g').obj F, W') :=
    Module.compHom _ ((f'.appLE U W' hW'U).hom.comp (g.appLE V U e).hom)
  haveI : IsScalarTower Γ(S, V) Γ(S', U) Γ((Scheme.Modules.pullback g').obj F, W') :=
    .of_algebraMap_smul fun _ _ => rfl
  exact (baseMapALin sq F e hV' hW'V hW'U).liftBaseChange Γ(S', U)

set_option backward.isDefEq.respectTransparency false in
/-- `sectionBaseChangeθ` sends `1 ⊗ m` to the canonical base-map image of `m`. -/
private lemma sectionBaseChangeθ_one_tmul {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) (F : X.Modules)
    {V : S.Opens} {U : S'.Opens} (e : U ≤ g ⁻¹ᵁ V)
    {V' : X.Opens} {W' : X'.Opens}
    (hV' : V' ≤ f ⁻¹ᵁ V) (hW'V : W' ≤ g' ⁻¹ᵁ V') (hW'U : W' ≤ f' ⁻¹ᵁ U)
    (m : Γ(F, V')) :
    letI : Algebra Γ(S, V) Γ(S', U) := (g.appLE V U e).hom.toAlgebra
    letI : Module Γ(S, V) Γ(F, V') := Module.compHom _ (f.appLE V V' hV').hom
    letI : Module Γ(S', U) Γ((Scheme.Modules.pullback g').obj F, W') :=
      Module.compHom _ (f'.appLE U W' hW'U).hom
    sectionBaseChangeθ sq F e hV' hW'V hW'U ((1 : Γ(S', U)) ⊗ₜ[Γ(S, V)] m)
      = pullback_app_isoTensor_baseMap g' F hW'V m := by
  letI : Algebra Γ(S, V) Γ(S', U) := (g.appLE V U e).hom.toAlgebra
  letI : Module Γ(S, V) Γ(F, V') := Module.compHom _ (f.appLE V V' hV').hom
  letI : Module Γ(S', U) Γ((Scheme.Modules.pullback g').obj F, W') :=
    Module.compHom _ (f'.appLE U W' hW'U).hom
  change (1 : Γ(S', U)) • pullback_app_isoTensor_baseMap g' F hW'V m
      = pullback_app_isoTensor_baseMap g' F hW'V m
  exact one_smul _ _

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- The affine comparison combines a ring pushout with scalar-extension associativity.
set_option synthInstance.maxHeartbeats 800000 in
/-- **`sectionBaseChangeθ` is bijective on an affine piece**: `W' = V' ×_V U` is affine,
`Γ(X', W')` is the ring pushout of the section square
(`isIso_pushoutSection_of_isAffineOpen` + `CommRingCat.isPushout_iff_isPushout`), so the
comparison factors as scalar-extension associativity
(`SectionBaseChange.bijective_addHom_of_isPushout`) followed by the pinned affine
section formula (`pullback_app_isoTensor_baseMap_sectionLinearEquiv`). -/
private theorem sectionBaseChangeθ_bijective {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g)
    (F : X.Modules) [F.IsQuasicoherent]
    {V : S.Opens} {U : S'.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (e : U ≤ g ⁻¹ᵁ V) {V' : X.Opens} (hV' : V' ≤ f ⁻¹ᵁ V) (hV'aff : IsAffineOpen V') :
    Function.Bijective (sectionBaseChangeθ sq F e hV'
      (inf_le_left : g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ V') inf_le_right) := by
  -- ring/algebra structures on the four corners
  letI algAB : Algebra Γ(S, V) Γ(S', U) := (g.appLE V U e).hom.toAlgebra
  letI algAC : Algebra Γ(S, V) Γ(X, V') := (f.appLE V V' hV').hom.toAlgebra
  letI algCD : Algebra Γ(X, V') Γ(X', g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) :=
    (g'.appLE V' (g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) inf_le_left).hom.toAlgebra
  letI algBD : Algebra Γ(S', U) Γ(X', g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) :=
    (f'.appLE U (g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) inf_le_right).hom.toAlgebra
  letI algAD : Algebra Γ(S, V) Γ(X', g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) :=
    ((f'.appLE U (g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) inf_le_right).hom.comp
      (g.appLE V U e).hom).toAlgebra
  haveI towABD : IsScalarTower Γ(S, V) Γ(S', U) Γ(X', g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) :=
    .of_algebraMap_eq' rfl
  haveI towACD : IsScalarTower Γ(S, V) Γ(X, V') Γ(X', g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) :=
    .of_algebraMap_eq' (appLE_square_comm sq e hV' inf_le_left inf_le_right).symm
  -- the ring pushout (mathlib, Spec-faithfulness of the restricted square)
  have hIso : IsIso (pushoutSection sq e hV' rfl) :=
    isIso_pushoutSection_of_isAffineOpen sq e hV' rfl hV hU hV'aff
  have hpoCat := (isIso_pushoutSection_iff sq e hV' rfl).mp hIso
  haveI hpo : Algebra.IsPushout Γ(S, V) Γ(X, V') Γ(S', U) Γ(X', g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) :=
    CommRingCat.isPushout_iff_isPushout.mp hpoCat
  -- module structures on the section modules
  letI modAM : Module Γ(S, V) Γ(F, V') := Module.compHom _ (f.appLE V V' hV').hom
  haveI towACM : IsScalarTower Γ(S, V) Γ(X, V') Γ(F, V') :=
    .of_algebraMap_smul fun _ _ => rfl
  letI modCP : Module Γ(X, V')
      Γ((Scheme.Modules.pullback g').obj F, g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) :=
    Module.compHom _ (g'.appLE V' (g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) inf_le_left).hom
  letI modBP : Module Γ(S', U)
      Γ((Scheme.Modules.pullback g').obj F, g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) :=
    Module.compHom _ (f'.appLE U (g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) inf_le_right).hom
  -- the pinned affine section formula
  have hW'aff : IsAffineOpen (g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) :=
    isAffineOpen_preimage_inf_preimage_of_isPullback sq hV hU hV'aff e hV'
  obtain ⟨⟨ψ, hψ⟩⟩ :=
    pullback_app_isoTensor_baseMap_sectionLinearEquiv g' F
      (U := g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) (V := V') hW'aff hV'aff inf_le_left
  -- the comparison through the C-side tensor product
  let s : TensorProduct Γ(S, V) Γ(S', U) Γ(F, V') →+
      TensorProduct Γ(X, V') Γ(X', g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) Γ(F, V') :=
    AddMonoidHom.comp ψ.symm.toLinearMap.toAddMonoidHom
      (sectionBaseChangeθ sq F e hV' inf_le_left inf_le_right).toAddMonoidHom
  have hs : ∀ (b : Γ(S', U)) (m : Γ(F, V')),
      s (b ⊗ₜ[Γ(S, V)] m) =
        algebraMap Γ(S', U) Γ(X', g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) b ⊗ₜ[Γ(X, V')] m := by
    intro b m
    have h1 : sectionBaseChangeθ sq F e hV' inf_le_left inf_le_right
        (b ⊗ₜ[Γ(S, V)] m) =
        algebraMap Γ(S', U) Γ(X', g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) b •
          pullback_app_isoTensor_baseMap g' F inf_le_left m := rfl
    have h3 : ψ.symm (pullback_app_isoTensor_baseMap g' F inf_le_left m) =
        (1 : Γ(X', g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U)) ⊗ₜ[Γ(X, V')] m := by
      rw [LinearEquiv.symm_apply_eq]
      exact (hψ m).symm
    change ψ.symm (sectionBaseChangeθ sq F e hV' inf_le_left inf_le_right
        (b ⊗ₜ[Γ(S, V)] m)) = _
    rw [h1, map_smul, h3, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hsbij : Function.Bijective s :=
    SectionBaseChange.bijective_addHom_of_isPushout s hs
  have hcomp : ∀ z, sectionBaseChangeθ sq F e hV' inf_le_left inf_le_right z
      = ψ (s z) := fun z =>
    (ψ.apply_symm_apply (sectionBaseChangeθ sq F e hV' inf_le_left inf_le_right z)).symm
  rw [show ⇑(sectionBaseChangeθ sq F e hV' inf_le_left inf_le_right) = ⇑ψ ∘ ⇑s
    from funext hcomp]
  exact ψ.bijective.comp hsbij

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Finite-cover injectivity combines tensor flatness with separatedness on every overlap.
set_option synthInstance.maxHeartbeats 800000 in
/-- **`sectionBaseChangeθ` is injective on a quasi-compact piece**: cover by finitely
many affines, compare with the bijective affine comparisons, and use sheaf
separatedness plus flatness of `Γ(S', U)` over `Γ(S, V)`
(`SectionBaseChange.injective_of_injective_cover`). -/
private theorem sectionBaseChangeθ_injective_of_isCompact {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) [Flat g]
    (F : X.Modules) [F.IsQuasicoherent]
    {V : S.Opens} {U : S'.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (e : U ≤ g ⁻¹ᵁ V) {V' : X.Opens} (hV' : V' ≤ f ⁻¹ᵁ V)
    (hc : IsCompact (V' : Set X)) :
    Function.Injective (sectionBaseChangeθ sq F e hV'
      (inf_le_left : g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ V') inf_le_right) := by
  letI algAB : Algebra Γ(S, V) Γ(S', U) := (g.appLE V U e).hom.toAlgebra
  haveI hflat : Module.Flat Γ(S, V) Γ(S', U) := flat_gamma_appLE_of_flat g hV hU e
  -- finite affine cover of the compact piece
  obtain ⟨sc, hscfin, hscsup⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hc
  haveI := hscfin.to_subtype
  have hTle : ∀ t : sc, ((t : X.affineOpens) : X.Opens) ≤ V' := fun t =>
    (le_iSup₂ (f := fun (i : X.affineOpens) (_ : i ∈ sc) => (i : X.Opens)) t.1 t.2).trans
      hscsup.ge
  have hTfV : ∀ t : sc, ((t : X.affineOpens) : X.Opens) ≤ f ⁻¹ᵁ V := fun t =>
    (hTle t).trans hV'
  have hWt : ∀ t : sc, g' ⁻¹ᵁ ((t : X.affineOpens) : X.Opens) ⊓ f' ⁻¹ᵁ U ≤
      g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U := fun t =>
    inf_le_inf (fun a ha => hTle t ha) le_rfl
  -- module structures
  letI modAM : Module Γ(S, V) Γ(F, V') := Module.compHom _ (f.appLE V V' hV').hom
  letI modAMt : ∀ t : sc, Module Γ(S, V) Γ(F, ((t : X.affineOpens) : X.Opens)) :=
    fun t => Module.compHom _ (f.appLE V _ (hTfV t)).hom
  letI modBP : Module Γ(S', U)
      Γ((Scheme.Modules.pullback g').obj F, g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) :=
    Module.compHom _ (f'.appLE U (g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U) inf_le_right).hom
  letI modBPt : ∀ t : sc, Module Γ(S', U)
      Γ((Scheme.Modules.pullback g').obj F,
        g' ⁻¹ᵁ ((t : X.affineOpens) : X.Opens) ⊓ f' ⁻¹ᵁ U) :=
    fun t => Module.compHom _
      (f'.appLE U (g' ⁻¹ᵁ ((t : X.affineOpens) : X.Opens) ⊓ f' ⁻¹ᵁ U) inf_le_right).hom
  refine SectionBaseChange.injective_of_injective_cover
    (res := fun t : sc => appLEResₗ f F hV' (hTfV t) (hTle t))
    (fun m hm => ?_)
    (res' := fun t : sc => appLEResₗ f' ((Scheme.Modules.pullback g').obj F)
      inf_le_right inf_le_right (hWt t))
    (ε := fun t : sc => sectionBaseChangeθ sq F e (hTfV t) inf_le_left inf_le_right)
    (fun t => (sectionBaseChangeθ_bijective sq F hV hU e (hTfV t)
      (t : X.affineOpens).2).injective)
    (sectionBaseChangeθ sq F e hV' inf_le_left inf_le_right)
    (fun t m => ?_)
  · -- joint injectivity of the cover restrictions (sheaf separatedness)
    refine TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X)
      (fun t : sc => ((t : X.affineOpens) : X.Opens)) V'
      (fun t => homOfLE (hTle t))
      (by
        rw [hscsup]
        exact iSup₂_le fun i hi =>
          le_iSup (fun t : sc => ((t : X.affineOpens) : X.Opens)) ⟨i, hi⟩)
      m 0 (fun t => ?_)
    have h0 : (F.presheaf.map (homOfLE (hTle t)).op).hom (0 : Γ(F, V')) = 0 := map_zero _
    exact (hm t).trans h0.symm
  · -- generator intertwining: restriction of θ(1 ⊗ m) is θ_t(1 ⊗ m|_t)
    have h1 := sectionBaseChangeθ_one_tmul sq F e hV'
      (inf_le_left : g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ V') inf_le_right m
    have h2 := sectionBaseChangeθ_one_tmul sq F e (hTfV t)
      (inf_le_left : g' ⁻¹ᵁ ((t : X.affineOpens) : X.Opens) ⊓ f' ⁻¹ᵁ U ≤
        g' ⁻¹ᵁ ((t : X.affineOpens) : X.Opens)) inf_le_right
      ((F.presheaf.map (homOfLE (hTle t)).op).hom m)
    have h3 := pullback_app_isoTensor_baseMap_res g' F
      (inf_le_left : g' ⁻¹ᵁ V' ⊓ f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ V')
      (inf_le_left : g' ⁻¹ᵁ ((t : X.affineOpens) : X.Opens) ⊓ f' ⁻¹ᵁ U ≤
        g' ⁻¹ᵁ ((t : X.affineOpens) : X.Opens))
      (hTle t) (hWt t) m
    change (((Scheme.Modules.pullback g').obj F).presheaf.map (homOfLE (hWt t)).op).hom
        (sectionBaseChangeθ sq F e hV' inf_le_left inf_le_right
          ((1 : Γ(S', U)) ⊗ₜ[Γ(S, V)] m))
      = sectionBaseChangeθ sq F e (hTfV t) inf_le_left inf_le_right
          ((1 : Γ(S', U)) ⊗ₜ[Γ(S, V)] (F.presheaf.map (homOfLE (hTle t)).op).hom m)
    rw [h1, h2]
    exact h3

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- The equalizer ladder elaborates both finite affine covers and all pairwise restrictions.
set_option synthInstance.maxHeartbeats 800000 in
/-- **The 02KE ladder over a given finite affine cover** of `f ⁻¹ᵁ V` with
quasi-compact pairwise overlaps: instantiates the abstract equalizer ladder
`SectionBaseChange.exists_linearEquiv_of_gluing` with the sheaf-condition
presentations of `Γ(F, f ⁻¹ᵁ V)` and `Γ(g'^*F, f' ⁻¹ᵁ U)`, the bijective affine
comparisons `sectionBaseChangeθ_bijective` on the pieces and the injective
comparisons `sectionBaseChangeθ_injective_of_isCompact` on the overlaps, and pins
the resulting equivalence on the generators `1 ⊗ t` by sheaf separatedness. -/
private theorem pullback_baseMap_sectionLinearEquiv_of_cover {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) [Flat g]
    (F : X.Modules) [F.IsQuasicoherent]
    {V : S.Opens} {U : S'.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (e : U ≤ g ⁻¹ᵁ V) (e'' : f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ V))
    {ι : Type u} [Finite ι] (VV : ι → X.Opens)
    (hVVaff : ∀ i, IsAffineOpen (VV i)) (hle : ∀ i, VV i ≤ f ⁻¹ᵁ V)
    (hcov : f ⁻¹ᵁ V ≤ ⨆ i, VV i)
    (hcpt : ∀ k : ι × ι, IsCompact ((VV k.1 ⊓ VV k.2 : X.Opens) : Set X)) :
    letI : Algebra Γ(S, V) Γ(S', U) := (g.appLE V U e).hom.toAlgebra
    Nonempty {h : TensorProduct Γ(S, V) Γ(S', U)
          Γ((Scheme.Modules.pushforward f).obj F, V) ≃ₗ[Γ(S', U)]
          Γ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F), U) //
      ∀ t : Γ((Scheme.Modules.pushforward f).obj F, V),
        h (1 ⊗ₜ[Γ(S, V)] t) = pullback_app_isoTensor_baseMap g' F e'' t} := by
  letI algAB : Algebra Γ(S, V) Γ(S', U) := (g.appLE V U e).hom.toAlgebra
  haveI hflat : Module.Flat Γ(S, V) Γ(S', U) := flat_gamma_appLE_of_flat g hV hU e
  -- inclusion bookkeeping for the cover, overlaps, and their primed companions
  have hleK : ∀ k : ι × ι, VV k.1 ⊓ VV k.2 ≤ f ⁻¹ᵁ V := fun k => inf_le_left.trans (hle k.1)
  have hWkW1 : ∀ k : ι × ι, g' ⁻¹ᵁ (VV k.1 ⊓ VV k.2) ⊓ f' ⁻¹ᵁ U ≤
      g' ⁻¹ᵁ VV k.1 ⊓ f' ⁻¹ᵁ U := fun k =>
    inf_le_inf (fun a ha => (inf_le_left : VV k.1 ⊓ VV k.2 ≤ VV k.1) ha) le_rfl
  have hWkW2 : ∀ k : ι × ι, g' ⁻¹ᵁ (VV k.1 ⊓ VV k.2) ⊓ f' ⁻¹ᵁ U ≤
      g' ⁻¹ᵁ VV k.2 ⊓ f' ⁻¹ᵁ U := fun k =>
    inf_le_inf (fun a ha => (inf_le_right : VV k.1 ⊓ VV k.2 ≤ VV k.2) ha) le_rfl
  have hWWk : ∀ k : ι × ι, (g' ⁻¹ᵁ VV k.1 ⊓ f' ⁻¹ᵁ U) ⊓ (g' ⁻¹ᵁ VV k.2 ⊓ f' ⁻¹ᵁ U) ≤
      g' ⁻¹ᵁ (VV k.1 ⊓ VV k.2) ⊓ f' ⁻¹ᵁ U := fun k =>
    le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
      (inf_le_left.trans inf_le_right)
  have hWsup : f' ⁻¹ᵁ U ≤ ⨆ i, (g' ⁻¹ᵁ VV i ⊓ f' ⁻¹ᵁ U) := by
    intro a ha
    have hga : g'.base a ∈ (⨆ i, VV i : X.Opens) := hcov (e'' ha)
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hga
    exact Opens.mem_iSup.mpr ⟨i, hi, ha⟩
  -- module structures on the cover pieces
  letI instMi : ∀ i : ι, Module Γ(S, V) Γ(F, VV i) :=
    fun i => Module.compHom _ (f.appLE V (VV i) (hle i)).hom
  letI instMk : ∀ k : ι × ι, Module Γ(S, V) Γ(F, VV k.1 ⊓ VV k.2) :=
    fun k => Module.compHom _ (f.appLE V (VV k.1 ⊓ VV k.2) (hleK k)).hom
  letI instPi : ∀ i : ι, Module Γ(S', U)
      Γ((Scheme.Modules.pullback g').obj F, g' ⁻¹ᵁ VV i ⊓ f' ⁻¹ᵁ U) :=
    fun i => Module.compHom _ (f'.appLE U (g' ⁻¹ᵁ VV i ⊓ f' ⁻¹ᵁ U) inf_le_right).hom
  letI instPk : ∀ k : ι × ι, Module Γ(S', U)
      Γ((Scheme.Modules.pullback g').obj F, g' ⁻¹ᵁ (VV k.1 ⊓ VV k.2) ⊓ f' ⁻¹ᵁ U) :=
    fun k => Module.compHom _
      (f'.appLE U (g' ⁻¹ᵁ (VV k.1 ⊓ VV k.2) ⊓ f' ⁻¹ᵁ U) inf_le_right).hom
  -- the equalizer ladder
  obtain ⟨Φ, hΦ⟩ := SectionBaseChange.exists_linearEquiv_of_gluing
    (A := Γ(S, V)) (B := Γ(S', U))
    (res := fun i : ι => pushforwardResₗ f F (hle i))
    (l := fun k : ι × ι =>
      (appLEResₗ f F (hle k.1) (hleK k) inf_le_left).comp (LinearMap.proj k.1))
    (r := fun k : ι × ι =>
      (appLEResₗ f F (hle k.2) (hleK k) inf_le_right).comp (LinearMap.proj k.2))
    (res' := fun i : ι => pushforwardResₗ f' ((Scheme.Modules.pullback g').obj F)
      (inf_le_right : g' ⁻¹ᵁ VV i ⊓ f' ⁻¹ᵁ U ≤ f' ⁻¹ᵁ U))
    (l' := fun k : ι × ι =>
      (appLEResₗ f' ((Scheme.Modules.pullback g').obj F) inf_le_right inf_le_right
        (hWkW1 k)).comp (LinearMap.proj k.1))
    (r' := fun k : ι × ι =>
      (appLEResₗ f' ((Scheme.Modules.pullback g').obj F) inf_le_right inf_le_right
        (hWkW2 k)).comp (LinearMap.proj k.2))
    (hMinj := fun m hm => by
      refine TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X)
        VV (f ⁻¹ᵁ V) (fun i => homOfLE (hle i)) hcov m 0 (fun i => ?_)
      exact (hm i).trans (map_zero ((F.presheaf.map (homOfLE (hle i)).op).hom)).symm)
    (hMglue := fun sf hsf => by
      have hcompat : TopCat.Presheaf.IsCompatible F.presheaf VV sf := by
        intro i j
        have h := hsf (i, j)
        have hL := congrArg
          (fun (m : (VV i ⊓ VV j) ⟶ VV i) => (F.presheaf.map m.op).hom (sf i))
          (Subsingleton.elim (Opens.infLELeft (VV i) (VV j)) (homOfLE inf_le_left))
        have hR := congrArg
          (fun (m : (VV i ⊓ VV j) ⟶ VV j) => (F.presheaf.map m.op).hom (sf j))
          (Subsingleton.elim (Opens.infLERight (VV i) (VV j)) (homOfLE inf_le_right))
        exact hL.trans (h.trans hR.symm)
      obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing'
        (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X) VV (f ⁻¹ᵁ V)
        (fun i => homOfLE (hle i)) hcov sf hcompat
      exact ⟨s, fun i => hs i⟩)
    (hMcpt := fun m k => by
      exact (modules_res_res F inf_le_left (hle k.1) (hleK k) m).trans
        (modules_res_res F inf_le_right (hle k.2) (hleK k) m).symm)
    (hPinj := fun p hp => by
      refine TopCat.Sheaf.eq_of_locally_eq'
        (⟨((Scheme.Modules.pullback g').obj F).presheaf,
          ((Scheme.Modules.pullback g').obj F).isSheaf⟩ : TopCat.Sheaf Ab X')
        (fun i => g' ⁻¹ᵁ VV i ⊓ f' ⁻¹ᵁ U) (f' ⁻¹ᵁ U)
        (fun i => homOfLE inf_le_right) hWsup p 0 (fun i => ?_)
      exact (hp i).trans (map_zero
        ((((Scheme.Modules.pullback g').obj F).presheaf.map
          (homOfLE (inf_le_right : g' ⁻¹ᵁ VV i ⊓ f' ⁻¹ᵁ U ≤ f' ⁻¹ᵁ U)).op).hom)).symm)
    (hPglue := fun sf hsf => by
      have hcompat : TopCat.Presheaf.IsCompatible
          ((Scheme.Modules.pullback g').obj F).presheaf
          (fun i => g' ⁻¹ᵁ VV i ⊓ f' ⁻¹ᵁ U) sf := by
        intro i j
        have h := hsf (i, j)
        have hL := modules_res_res_hom ((Scheme.Modules.pullback g').obj F)
          (homOfLE (hWWk (i, j))) (homOfLE (hWkW1 (i, j)))
          (Opens.infLELeft (g' ⁻¹ᵁ VV i ⊓ f' ⁻¹ᵁ U) (g' ⁻¹ᵁ VV j ⊓ f' ⁻¹ᵁ U)) (sf i)
        have hR := modules_res_res_hom ((Scheme.Modules.pullback g').obj F)
          (homOfLE (hWWk (i, j))) (homOfLE (hWkW2 (i, j)))
          (Opens.infLERight (g' ⁻¹ᵁ VV i ⊓ f' ⁻¹ᵁ U) (g' ⁻¹ᵁ VV j ⊓ f' ⁻¹ᵁ U)) (sf j)
        exact hL.symm.trans ((congrArg
          (fun w => ((((Scheme.Modules.pullback g').obj F).presheaf.map
            (homOfLE (hWWk (i, j))).op).hom) w) h).trans hR)
      obtain ⟨p, hp, -⟩ := TopCat.Sheaf.existsUnique_gluing'
        (⟨((Scheme.Modules.pullback g').obj F).presheaf,
          ((Scheme.Modules.pullback g').obj F).isSheaf⟩ : TopCat.Sheaf Ab X')
        (fun i => g' ⁻¹ᵁ VV i ⊓ f' ⁻¹ᵁ U) (f' ⁻¹ᵁ U)
        (fun i => homOfLE inf_le_right) hWsup sf hcompat
      exact ⟨p, fun i => hp i⟩)
    (hPcpt := fun p k => by
      exact (modules_res_res ((Scheme.Modules.pullback g').obj F) (hWkW1 k)
          inf_le_right inf_le_right p).trans
        (modules_res_res ((Scheme.Modules.pullback g').obj F) (hWkW2 k)
          inf_le_right inf_le_right p).symm)
    (ε := fun i : ι => sectionBaseChangeθ sq F e (hle i) inf_le_left inf_le_right)
    (hε := fun i => sectionBaseChangeθ_bijective sq F hV hU e (hle i) (hVVaff i))
    (μ := fun k : ι × ι => sectionBaseChangeθ sq F e (hleK k) inf_le_left inf_le_right)
    (hμ := fun k => sectionBaseChangeθ_injective_of_isCompact sq F hV hU e (hleK k)
      (hcpt k))
    (hl := fun k sf => by
      have h1 := sectionBaseChangeθ_one_tmul sq F e (hleK k)
        (inf_le_left : g' ⁻¹ᵁ (VV k.1 ⊓ VV k.2) ⊓ f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ (VV k.1 ⊓ VV k.2))
        inf_le_right
        ((F.presheaf.map (homOfLE (inf_le_left : VV k.1 ⊓ VV k.2 ≤ VV k.1)).op).hom
          (sf k.1))
      have h2 := sectionBaseChangeθ_one_tmul sq F e (hle k.1)
        (inf_le_left : g' ⁻¹ᵁ VV k.1 ⊓ f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ VV k.1) inf_le_right (sf k.1)
      have h3 := pullback_app_isoTensor_baseMap_res g' F
        (inf_le_left : g' ⁻¹ᵁ VV k.1 ⊓ f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ VV k.1)
        (inf_le_left : g' ⁻¹ᵁ (VV k.1 ⊓ VV k.2) ⊓ f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ (VV k.1 ⊓ VV k.2))
        (inf_le_left : VV k.1 ⊓ VV k.2 ≤ VV k.1) (hWkW1 k) (sf k.1)
      exact h1.trans (h3.symm.trans (congrArg
        (fun w => ((((Scheme.Modules.pullback g').obj F).presheaf.map
          (homOfLE (hWkW1 k)).op).hom) w) h2.symm)))
    (hr := fun k sf => by
      have h1 := sectionBaseChangeθ_one_tmul sq F e (hleK k)
        (inf_le_left : g' ⁻¹ᵁ (VV k.1 ⊓ VV k.2) ⊓ f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ (VV k.1 ⊓ VV k.2))
        inf_le_right
        ((F.presheaf.map (homOfLE (inf_le_right : VV k.1 ⊓ VV k.2 ≤ VV k.2)).op).hom
          (sf k.2))
      have h2 := sectionBaseChangeθ_one_tmul sq F e (hle k.2)
        (inf_le_left : g' ⁻¹ᵁ VV k.2 ⊓ f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ VV k.2) inf_le_right (sf k.2)
      have h3 := pullback_app_isoTensor_baseMap_res g' F
        (inf_le_left : g' ⁻¹ᵁ VV k.2 ⊓ f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ VV k.2)
        (inf_le_left : g' ⁻¹ᵁ (VV k.1 ⊓ VV k.2) ⊓ f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ (VV k.1 ⊓ VV k.2))
        (inf_le_right : VV k.1 ⊓ VV k.2 ≤ VV k.2) (hWkW2 k) (sf k.2)
      exact h1.trans (h3.symm.trans (congrArg
        (fun w => ((((Scheme.Modules.pullback g').obj F).presheaf.map
          (homOfLE (hWkW2 k)).op).hom) w) h2.symm)))
  -- pin the equivalence on the generators `1 ⊗ t` by separatedness of the primed sheaf
  refine ⟨⟨Φ, fun t => ?_⟩⟩
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨((Scheme.Modules.pullback g').obj F).presheaf,
      ((Scheme.Modules.pullback g').obj F).isSheaf⟩ : TopCat.Sheaf Ab X')
    (fun i => g' ⁻¹ᵁ VV i ⊓ f' ⁻¹ᵁ U) (f' ⁻¹ᵁ U)
    (fun i => homOfLE inf_le_right) hWsup _ _ (fun i => ?_)
  have h1 := hΦ ((1 : Γ(S', U)) ⊗ₜ[Γ(S, V)] t) i
  have h2 := sectionBaseChangeθ_one_tmul sq F e (hle i)
    (inf_le_left : g' ⁻¹ᵁ VV i ⊓ f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ VV i) inf_le_right
    ((F.presheaf.map (homOfLE (hle i)).op).hom t)
  have h3 := pullback_app_isoTensor_baseMap_res g' F e''
    (inf_le_left : g' ⁻¹ᵁ VV i ⊓ f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ VV i)
    (hle i) (inf_le_right : g' ⁻¹ᵁ VV i ⊓ f' ⁻¹ᵁ U ≤ f' ⁻¹ᵁ U) t
  exact h1.trans (h2.trans h3.symm)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- The H⁰ comparison packages the finite-cover ladder into the canonical section map.
/-- **H⁰ flat base change over a compatible affine pair** (Stacks tag 02KE,
`i = 0` form; Σ-pair dialect). CLOSED (T13, 2026-07-07): proof via the
finite-affine-cover equalizer ladder `pullback_baseMap_sectionLinearEquiv_of_cover`
(geometric instantiation of `SectionBaseChange.exists_linearEquiv_of_gluing`).

For a cartesian square `sq : IsPullback g' f' f g` with `f` quasi-compact
quasi-separated, `g` flat, `F` quasi-coherent on `X`, and affine opens
`V ⊆ S`, `U ⊆ S'` with `U ≤ g ⁻¹ᵁ V`, write `A := Γ(S, V)`,
`B := Γ(S', U)` (a flat `A`-algebra via `g.appLE`, by affine-locality of
flatness). The claim: there is a `B`-linear equivalence

  `B ⊗_A Γ(F, f ⁻¹ᵁ V)  ≃ₗ[B]  Γ(g'^* F, f' ⁻¹ᵁ U)`

sending `1 ⊗ x` to the canonical adjunction-unit base-map image
`pullback_app_isoTensor_baseMap g' F e'' x` (which pins the equivalence on
the `B`-generators, hence everywhere). Here `Γ(f_* F, V) = Γ(F, f ⁻¹ᵁ V)`
and `Γ(f'_* g'^* F, U) = Γ(g'^* F, f' ⁻¹ᵁ U)` definitionally.

This is the substantive algebraic heart of Stacks 02KH: `f' ⁻¹ᵁ U =
(f ⁻¹ᵁ V) ×_V U` is qcqs but NOT affine (for non-affine `X`), so the
affine section formula `pullback_app_isoTensor` cannot be applied to it
directly. Reference proof (Stacks 02KE, transcribed to the eqLocus dialect):
choose a finite affine cover `{V_i}` of `f ⁻¹ᵁ V` (quasi-compactness of `f`)
with quasi-compact pairwise intersections (quasi-separatedness); the sheaf
axiom presents `Γ(F, f ⁻¹ᵁ V)` as the finite equalizer (eqLocus) of
`∏_i Γ(F, V_i) ⇉ ∏_{ij} Γ(F, V_i ⊓ V_j)`; tensoring with the flat
`A`-algebra `B` preserves the finite equalizer
(`LinearMap.tensorEqLocusEquiv` + `TensorProduct.piRight`); on the primed
side `W_i := g' ⁻¹ᵁ V_i ⊓ f' ⁻¹ᵁ U` is AFFINE (`= V_i ×_V U`, pullback of
affines over an affine base, via `Scheme.Hom.isPullback_resLE` +
`isoPullback`), the `W_i` cover `f' ⁻¹ᵁ U`, and the sheaf axiom presents
`Γ(g'^* F, f' ⁻¹ᵁ U)` as the analogous finite equalizer; the per-term
comparisons `B ⊗_A Γ(F, V_i) ≃ Γ(g'^* F, W_i)` are
`AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen` (affine fibre
product = ring pushout) + `Scheme.Modules.pullback_app_isoTensor` +
tensor cancellation; on pairwise overlaps only INJECTIVITY is needed (same
argument one level down: finite affine cover, flat tensoring preserves
injections, sheaf separatedness); an equalizer-ladder chase gives the middle
equivalence, and evaluating on `1 ⊗ x` (unit naturality, (N1)/(N2)) shows it
is induced by the canonical base map. Mathlib's
`AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq` /
`mono_pushoutSection_of_iSup_eq` (Morphisms/Flat.lean) is the complete
structure-sheaf template of this ladder.

Source: Stacks Project, Tags 02KE and 02KH (ii), `i = 0`. -/
theorem pullback_baseMap_sectionLinearEquiv_of_quasiCompact
    {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    (F : X.Modules) [F.IsQuasicoherent]
    {V : S.Opens} {U : S'.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (e : U ≤ g ⁻¹ᵁ V) (e'' : f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ V)) :
    letI : Algebra Γ(S, V) Γ(S', U) := (g.appLE V U e).hom.toAlgebra
    Nonempty {h : TensorProduct Γ(S, V) Γ(S', U)
          Γ((Scheme.Modules.pushforward f).obj F, V) ≃ₗ[Γ(S', U)]
          Γ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F), U) //
      ∀ t : Γ((Scheme.Modules.pushforward f).obj F, V),
        h (1 ⊗ₜ[Γ(S, V)] t) = pullback_app_isoTensor_baseMap g' F e'' t} := by
  -- finite affine cover of the compact quasi-separated preimage `f ⁻¹ᵁ V`
  have hVc : IsCompact ((f ⁻¹ᵁ V : X.Opens) : Set X) := f.isCompact_preimage hV.isCompact
  have hsep : IsQuasiSeparated ((f ⁻¹ᵁ V : X.Opens) : Set X) :=
    f.isQuasiSeparated_preimage hV.isQuasiSeparated
  obtain ⟨sc, hscfin, hscsup⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hVc
  haveI := hscfin.to_subtype
  have hle : ∀ i : sc, ((i : X.affineOpens) : X.Opens) ≤ f ⁻¹ᵁ V := fun i =>
    (le_iSup₂ (f := fun (j : X.affineOpens) (_ : j ∈ sc) => (j : X.Opens)) i.1 i.2).trans
      hscsup.ge
  have hcov : f ⁻¹ᵁ V ≤ ⨆ i : sc, ((i : X.affineOpens) : X.Opens) := by
    refine hscsup.le.trans ?_
    exact iSup₂_le fun i hi =>
      le_iSup (fun t : sc => ((t : X.affineOpens) : X.Opens)) ⟨i, hi⟩
  have hcpt : ∀ k : sc × sc,
      IsCompact ((((k.1 : X.affineOpens) : X.Opens) ⊓ ((k.2 : X.affineOpens) : X.Opens) :
        X.Opens) : Set X) := by
    intro k
    rw [TopologicalSpace.Opens.coe_inf]
    exact hsep _ _ (hle k.1) ((k.1 : X.affineOpens) : X.Opens).isOpen
      (k.1 : X.affineOpens).2.isCompact (hle k.2)
      ((k.2 : X.affineOpens) : X.Opens).isOpen (k.2 : X.affineOpens).2.isCompact
  exact pullback_baseMap_sectionLinearEquiv_of_cover sq F hV hU e e''
    (fun i : sc => ((i : X.affineOpens) : X.Opens)) (fun i => (i : X.affineOpens).2)
    hle hcov hcpt

end SectionBaseChangeLadder

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- Identifying the canonical mate at an affine pair unfolds both section trivializations.
/-- **Workhorse: the canonical base-change section map is an iso at every
compatible affine pair** (Stacks 02KH(ii) at `i = 0`, affine-pair form;
T12 fbc-leaves front, 2026-07-06).

`Γ(g^* f_* F, U)` and `Γ(f'_* g'^* F, U)` are both trivialized as
`Γ(S', U) ⊗_{Γ(S, V)} Γ(F, f ⁻¹ᵁ V)` — the former by the sorry-free Tilde
route (`pullback_app_isoTensor_baseMap_sectionLinearEquiv` applied to the
quasi-coherent `f_* F`, Stacks 01XJ), the latter by the 02KE heart
(`pullback_baseMap_sectionLinearEquiv_of_quasiCompact`). The canonical mate
is `Γ(S', U)`-linear on sections (`Hom.app_smul`) and matches the two
witnesses on the generators `1 ⊗ t` by KEY-BC
(`canonicalBaseChangeMap_app_baseMap_compat`), hence everywhere by linearity
(`TensorProduct.induction_on`); it is therefore the composite bijection
`eqR ∘ eqL⁻¹`. -/
private theorem canonicalBaseChangeMap_app_app_isIso_of_le_preimage
    {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    (F : X.Modules) [F.IsQuasicoherent]
    {V : S.Opens} {U : S'.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (e : U ≤ g ⁻¹ᵁ V) :
    IsIso (((canonicalBaseChangeMap sq).app F).app U) := by
  have e'' : f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, sq.w, Scheme.Hom.comp_preimage]
    exact fun a ha => e ha
  haveI : ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    Scheme.Modules.pushforward_isQuasicoherent f F
  letI algInst : Algebra Γ(S, V) Γ(S', U) := (g.appLE V U e).hom.toAlgebra
  letI modInst : Module Γ(S, V)
      Γ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F), U) :=
    Module.compHom _ (g.appLE V U e).hom
  obtain ⟨eqL, heqL⟩ := (pullback_app_isoTensor_baseMap_sectionLinearEquiv g
    ((Scheme.Modules.pushforward f).obj F) hU hV e).some
  obtain ⟨eqR, heqR⟩ :=
    (pullback_baseMap_sectionLinearEquiv_of_quasiCompact sq F hV hU e e'').some
  -- The canonical map as a `Γ(S', U)`-linear map on sections.
  let χ : Γ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F), U)
      →ₗ[Γ(S', U)]
      Γ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F), U) :=
    { toFun := (((canonicalBaseChangeMap sq).app F).app U).hom
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a =>
        Scheme.Modules.Hom.app_smul ((canonicalBaseChangeMap sq).app F) r a }
  -- χ intertwines the two Σ-pair witnesses on the generators `1 ⊗ t` (KEY-BC) …
  have hgen : ∀ t, χ (eqL (1 ⊗ₜ[Γ(S, V)] t)) = eqR (1 ⊗ₜ[Γ(S, V)] t) := by
    intro t
    rw [heqL t, heqR t]
    exact canonicalBaseChangeMap_app_baseMap_compat sq F e e'' t
  -- … hence everywhere (`b ⊗ t = b • (1 ⊗ t)` and all three maps are `B`-linear).
  have hall : ∀ z, χ (eqL z) = eqR z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b t =>
      have hb : (b ⊗ₜ[Γ(S, V)] t :
          TensorProduct Γ(S, V) Γ(S', U)
            Γ((Scheme.Modules.pushforward f).obj F, V)) =
          b • ((1 : Γ(S', U)) ⊗ₜ[Γ(S, V)] t) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hb, map_smul, map_smul, map_smul, hgen t]
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  -- The canonical map is the bijection `eqR ∘ eqL.symm`.
  have hbij : Function.Bijective
      ⇑(((canonicalBaseChangeMap sq).app F).app U).hom := by
    have hfun : ∀ p, (((canonicalBaseChangeMap sq).app F).app U).hom p =
        eqR (eqL.symm p) := by
      intro p
      have h := hall (eqL.symm p)
      rwa [LinearEquiv.apply_symm_apply] at h
    rw [show ⇑(((canonicalBaseChangeMap sq).app F).app U).hom = ⇑eqR ∘ ⇑eqL.symm
      from funext hfun]
    exact eqR.bijective.comp eqL.symm.bijective
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

/-- **Affine-base case of flat base change at affine opens** (Stacks tag 02KH).

Specialization of `canonicalBaseChangeMap_app_app_isIso_of_isAffineOpen` to
the case where the *base* `S` is affine, so we may take `V := ⊤ : S.Opens`
as the (trivially affine) compatible open: every affine `U ⊆ S'` satisfies
`U ≤ (Opens.map g.base).obj ⊤ = ⊤`.

iter-187 Lane F (analogist-informed REFACTOR, per
`analogies/quotscheme-isbasechange-tilde.md` Decision 1): the
prior iter-186 framing routed through `Module.Flat.isBaseChange`,
which is a **category mistake** — that Mathlib lemma is a *consumer*
of `IsBaseChange` (it propagates flatness *across* a given IsBaseChange
witness, Stacks 00H8 in the conclusion direction), NOT a producer.
The corrected route uses `pullback_app_isoTensor g' …` directly: the
section-level iso is `(pullback_app_isoTensor g' …).symm`, and the
residual gap is *Beck–Chevalley compatibility* (the canonical BC arrow
agrees with the section-formula iso under the `pushforward_obj_obj`-rfl
identification) plus the section-vs-tensor-product Tilde-isoTop content
(now factored into `pullback_tildeIso`).

iter-187 Lane F adds `[F.IsQuasicoherent]` per analogist Decision 3:
this is the standard Stacks 02KH hypothesis on the input sheaf `F`. Via
`pushforward_isQuasicoherent` (named project-side helper for Stacks
01XJ), it propagates to `((pushforward f).obj F).IsQuasicoherent`, which
is what `pullback_app_isoTensor` needs.

CLOSED (T12 fbc-leaves front, 2026-07-06): specialization `V := ⊤` of the
affine-pair workhorse `canonicalBaseChangeMap_app_app_isIso_of_le_preimage`
(every `U` satisfies `U ≤ g ⁻¹ᵁ ⊤`). NOTE the earlier docstring plan
("~30-50 LOC of Beck-Chevalley route-stitching" against
`pullback_app_isoTensor` on `f' ⁻¹ᵁ U`) was NOT viable for non-affine `X`
— `f' ⁻¹ᵁ U` is not affine, so the RHS trivialization is genuinely the
qcqs finite-cover 02KE content, factored into
`pullback_baseMap_sectionLinearEquiv_of_quasiCompact` (now CLOSED). -/
private theorem canonicalBaseChangeMap_app_app_isIso_of_isAffineOpen_of_isAffineBase
    {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g)
    [IsAffine S]
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : S'.Opens) (_hU : IsAffineOpen U) :
    IsIso (((canonicalBaseChangeMap sq).app F).app U) :=
  -- `V := ⊤ : S.Opens` is affine via `[IsAffine S]`, and `U ≤ g ⁻¹ᵁ ⊤`.
  canonicalBaseChangeMap_app_app_isIso_of_le_preimage sq F
    (isAffineOpen_top S) _hU le_top

/-- **Affine-open form of flat base change** (Stacks tag 00H8 / 02KE).

Restriction of `canonicalBaseChangeMap_app_app_isIso` to the case where the
open `U ⊆ S'` is affine.

CLOSED (T12 fbc-leaves front, 2026-07-06). Route: the affine opens
`W ⊆ S'` *compatible with an affine `V ⊆ S`* (`W ≤ g ⁻¹ᵁ V`) form a basis
of `S'` — given `x ∈ O`, pick an affine `V ∋ g(x)` in `S`, then an affine
`W ≤ O ⊓ g ⁻¹ᵁ V` around `x`. On each such pair the affine-pair workhorse
`canonicalBaseChangeMap_app_app_isIso_of_le_preimage` (Stacks 02KE) gives
the section iso; the basis-locality engine
`Modules.isIso_of_isIso_app_of_isBasis` upgrades this to an iso of sheaf
morphisms, and Mathlib's `IsIso φ → IsIso (φ.app U)` instance evaluates it
back at the given (indeed at ANY) `U`. No base-side Mayer-Vietoris and no
square restriction is needed — the historically walled mate-restriction
naturality is bypassed entirely. (The earlier docstring's steps 1-4
base-side descent plan is superseded by this basis argument.) -/
private theorem canonicalBaseChangeMap_app_app_isIso_of_isAffineOpen
    {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : S'.Opens) (_hU : IsAffineOpen U) :
    IsIso (((canonicalBaseChangeMap sq).app F).app U) := by
  -- The compatible affine pairs form a basis of `S'`.
  have hB : TopologicalSpace.Opens.IsBasis (Set.range
      (fun i : {W : S'.Opens × S.Opens //
        IsAffineOpen W.1 ∧ IsAffineOpen W.2 ∧ W.1 ≤ g ⁻¹ᵁ W.2} => i.1.1)) := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro O x hxO
    obtain ⟨_, ⟨Vb, hVb, rfl⟩, hgxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (g.base x)) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWle⟩ :=
      S'.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ ((O ⊓ g ⁻¹ᵁ Vb : S'.Opens) : Set S') from ⟨hxO, hgxV⟩)
        (O ⊓ g ⁻¹ᵁ Vb).2
    exact ⟨W, ⟨⟨(W, Vb), hW, hVb, le_trans hWle inf_le_right⟩, rfl⟩, hxW,
      le_trans hWle inf_le_left⟩
  -- Iso on the basis (via the affine-pair workhorse) ⟹ iso of sheaf morphisms
  -- ⟹ iso at `U`.
  haveI : IsIso ((canonicalBaseChangeMap sq).app F) :=
    Modules.isIso_of_isIso_app_of_isBasis hB ((canonicalBaseChangeMap sq).app F)
      (fun i => canonicalBaseChangeMap_app_app_isIso_of_le_preimage sq F
        i.2.2.1 i.2.1 i.2.2.2)
  infer_instance

/-- **Open-cover gluing for the section-wise flat base change**
(basis-locality reduction, Stacks 02KH(ii) corollary).

If the section of the canonical base-change map is an iso over *every*
affine open `V ⊆ S'`, then it is an iso over every open `U ⊆ S'` as well.

PROVED (T12 session, 2026-07-06, Lane F fbc-leaves front). Route: the
affine opens form a basis of `S'` (`Scheme.isBasis_affineOpens`); a
morphism of sheaves of modules that is an iso on sections over every
basic open is an iso of sheaves
(`Modules.isIso_of_isIso_app_of_isBasis`, the sorry-free basis-locality
engine from `AlgebraicJacobian.Cohomology.FlatBaseChange`, built on
Mathlib's stalkwise criterion `isIso_of_stalkFunctor_map_iso` plus
`stalkFunctor_map_injective_of_isBasis` / `exists_mem_germ_eq_of_isBasis`);
and Mathlib's instance `IsIso φ → IsIso (φ.app U)` restores the
section-wise claim at an arbitrary open `U`. No Mayer-Vietoris gluing and
no `QuasiSeparated f` input is needed for this reduction step (the
hypothesis is kept for signature stability with the consumer chain). -/
private theorem canonicalBaseChangeMap_app_app_isIso_of_affineCover
    {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    (F : X.Modules) [F.IsQuasicoherent]
    (h_affine : ∀ V : S'.Opens, IsAffineOpen V →
        IsIso (((canonicalBaseChangeMap sq).app F).app V))
    (U : S'.Opens) :
    IsIso (((canonicalBaseChangeMap sq).app F).app U) := by
  -- Iso on the affine-opens basis ⟹ iso of sheaf morphisms ⟹ iso at `U`.
  haveI : IsIso ((canonicalBaseChangeMap sq).app F) :=
    Modules.isIso_of_isIso_app_of_isBasis
      (B := (Subtype.val : S'.affineOpens → S'.Opens))
      (by simpa [Subtype.range_val] using S'.isBasis_affineOpens)
      ((canonicalBaseChangeMap sq).app F)
      (fun V => h_affine V.1 V.2)
  infer_instance

/-- **Section-wise form of flat base change** (Stacks tag 02KH(ii)).

For every open `U` of `S'`, the section over `U` of the canonical base-change
map `(pullback g).obj ((pushforward f).obj F) ⟶ (pushforward f').obj ((pullback g').obj F)`
is an isomorphism.

This is the substantive content of Stacks 02KH(ii) (the `i = 0` form), and
splits into two named helpers (both PROVED, T12 fbc-leaves front 2026-07-06):
* `canonicalBaseChangeMap_app_app_isIso_of_isAffineOpen` — the affine case,
  via the affine-pair workhorse
  `canonicalBaseChangeMap_app_app_isIso_of_le_preimage` (Stacks 02KE
  witnesses + KEY-BC intertwining) on the basis of compatible affine pairs;
* `canonicalBaseChangeMap_app_app_isIso_of_affineCover` — the reduction from
  affine opens to arbitrary opens via basis locality
  (`Modules.isIso_of_isIso_app_of_isBasis`).

The whole chain rests on `pullback_baseMap_sectionLinearEquiv_of_quasiCompact`
(the 02KE H⁰ heart), CLOSED (T13, 2026-07-07) — the chain is sorry-free. -/
theorem canonicalBaseChangeMap_app_app_isIso {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    (F : X.Modules) [F.IsQuasicoherent] (U : S'.Opens) :
    IsIso (((canonicalBaseChangeMap sq).app F).app U) :=
  -- Composition of the two named helpers: the affine-open case via the
  -- affine-pair workhorse on the compatible-pairs basis, then basis
  -- locality from affine opens to all opens.
  canonicalBaseChangeMap_app_app_isIso_of_affineCover sq F
    (fun V hV => canonicalBaseChangeMap_app_app_isIso_of_isAffineOpen sq F V hV)
    U

/-- **Flat base-change is an isomorphism** (Stacks tag 02KH, `i = 0`).

The canonical base-change natural transformation `canonicalBaseChangeMap`
is an isomorphism at every coherent sheaf `F` under the hypotheses
`[QuasiCompact f]`, `[QuasiSeparated f]`, `[Flat g]`.

The proof reduces section-wise via `Scheme.Modules.Hom.isIso_iff_isIso_app`
to the section-form helper `canonicalBaseChangeMap_app_app_isIso`,
which captures Stacks 02KH(ii) — the affine-pair workhorse (02KE witnesses
+ the KEY-BC intertwining) plus basis locality; the 02KE leaf
`pullback_baseMap_sectionLinearEquiv_of_quasiCompact` is CLOSED, so the
whole chain is sorry-free. -/
theorem canonicalBaseChangeMap_isIso {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIso ((canonicalBaseChangeMap sq).app F) :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    (fun U => canonicalBaseChangeMap_app_app_isIso sq F U)

theorem flatBaseChangeCohomology {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    (F : X.Modules) [F.IsQuasicoherent] :
    Nonempty ((Scheme.Modules.pullback g).obj
                ((Scheme.Modules.pushforward f).obj F) ≅
              (Scheme.Modules.pushforward f').obj
                ((Scheme.Modules.pullback g').obj F)) :=
  -- Build the canonical Beck-Chevalley base-change map and wrap it in `asIso`
  -- using the iso-claim from `canonicalBaseChangeMap_isIso`.
  ⟨@asIso _ _ _ _ _ (canonicalBaseChangeMap_isIso sq F)⟩

/-! ## Finite generation of affine sections (Stacks 01PC, finite-type half)

For a sheaf of modules of finite presentation `F` on a scheme `X`
(Mathlib's `SheafOfModules.IsFinitePresentation`), the module of sections
`Γ(F, V)` over any affine open `V` contained in a member of the presenting
cover is a *finite* `Γ(X, V)`-module.  This is the chart-level input that
Nitsure §4 generic flatness (`AlgebraicGeometry.genericFlatness`, file
`GenericFlatnessGeometric.lean`) feeds to the algebraic generic-freeness
theorem `GenericFreeness.genericFlatnessAlgebraic`.

Route (every bridge already exists in this file):
1. the slice generating sections of `F.over (q.X i)` geometrize across the
   slice-to-geometric equivalence (`overRestrictEquiv` / `overRestrictPullbackIso`,
   via Mathlib's `GeneratingSections.map`) to the open subscheme `(q.X i).toScheme`;
2. they pull back along the open-immersion factorization
   `k : Spec Γ(X, V) ⟶ (q.X i).toScheme` of `hV.fromSpec` (unit datum
   `pullbackOpenImmersionUnitIso`), and the pseudofunctor isos
   `pullbackComp`/`pullbackCongr` carry them onto `(pullback hV.fromSpec).obj F`;
3. the Stacks 01I8 identification `tildeIso_of_isQuasicoherent_isAffineOpen`
   lands them on `tilde Γ(F, V)`;
4. a finite generating epimorphism onto a tilde forces finite generation of the
   underlying module (`module_finite_of_tilde_genSections`): transposing the
   epimorphism through the tilde–Γ adjunction gives a module map out of a finite
   free module which is epi, because the adjunction counit at a tilde is
   invertible and `tilde.functor` is faithful. -/

namespace Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 400000 in
-- Headroom for the `IsIso`/`Epi` instance chains through the tilde–Γ adjunction
-- (`NatTrans.app` iso components, functor-map isos), as elsewhere in this file.
set_option maxHeartbeats 800000 in
/-- **Finite generation from a finite generating family of the tilde** (Stacks 01PC,
module-side heart). If `tilde N` on `Spec R` admits finitely many generating
sections, then `N` is a finite `R`-module: the generating epimorphism
`free σ.I ⟶ tilde N` transposes through the tilde–Γ adjunction to a module map
`(σ.I →₀ R) ⟶ N` (after inverting the adjunction unit), which is an epimorphism
because the counit at a tilde is invertible and `tilde.functor` is faithful.
Project-local. -/
theorem module_finite_of_tilde_genSections {R : CommRingCat.{u}} (N : ModuleCat.{u} R)
    (σ : (tilde N).GeneratingSections) [σ.IsFiniteType] :
    Module.Finite R N := by
  haveI hσπ : Epi σ.π := σ.epi
  -- the generating epimorphism, sourced at the tilde of a finite free module
  let π' : (tilde.functor R).obj (ModuleCat.of R (σ.I →₀ R)) ⟶ tilde N :=
    (tildeFinsupp σ.I).hom ≫ σ.π
  haveI hπ' : Epi π' := epi_comp _ _
  -- transpose through the adjunction
  let t : ModuleCat.of R (σ.I →₀ R) ⟶ moduleSpecΓFunctor.obj (tilde N) :=
    (tilde.adjunction.homEquiv _ _) π'
  have hfac : (tilde.functor R).map t ≫ tilde.adjunction.counit.app (tilde N) = π' :=
    (Adjunction.homEquiv_counit tilde.adjunction _ _ t).symm.trans
      ((tilde.adjunction.homEquiv _ _).symm_apply_apply π')
  -- the counit at a tilde is invertible (triangle identity + invertible unit)
  haveI hu : IsIso (tilde.adjunction.unit.app N) := inferInstance
  haveI hmu : IsIso ((tilde.functor R).map (tilde.adjunction.unit.app N)) :=
    inferInstance
  haveI hcomp : IsIso ((tilde.functor R).map (tilde.adjunction.unit.app N) ≫
      tilde.adjunction.counit.app ((tilde.functor R).obj N)) := by
    rw [tilde.adjunction.left_triangle_components N]
    infer_instance
  haveI hcu : IsIso (tilde.adjunction.counit.app (tilde N)) :=
    IsIso.of_isIso_comp_left
      ((tilde.functor R).map (tilde.adjunction.unit.app N))
      (tilde.adjunction.counit.app ((tilde.functor R).obj N))
  haveI hmt : Epi ((tilde.functor R).map t) := by
    have hre : (tilde.functor R).map t =
        π' ≫ inv (tilde.adjunction.counit.app (tilde N)) := by
      rw [← hfac, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [hre]
    exact epi_comp _ _
  haveI ht : Epi t := (tilde.functor R).epi_of_epi_map hmt
  -- invert the unit and conclude by surjectivity
  haveI : Epi (t ≫ inv (tilde.adjunction.unit.app N)) := epi_comp _ _
  exact Module.Finite.of_surjective
    (ModuleCat.Hom.hom (t ≫ inv (tilde.adjunction.unit.app N)))
    ((ModuleCat.epi_iff_surjective _).mp ‹_›)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- Mapping generating sections across the slice equivalence triggers `HasSheafify` synthesis.
set_option synthInstance.maxHeartbeats 800000 in
/-- **Affine sections of a finitely presented module sheaf are finitely generated**
(Stacks 01PC, finite-type half; chart-level form). If `F` is quasi-coherent, `q` is
a quasi-coherence datum with finite presentations, and `V ≤ q.X i` is an affine
open, then `Γ(F, V)` is a finite `Γ(X, V)`-module. The generating sections of the
slice `F.over (q.X i)` geometrize, pull back to `Spec Γ(X, V)` along the
factorization of `hV.fromSpec` through the cover member, land on `tilde Γ(F, V)`
by the 01I8 identification, and force finite generation via
`module_finite_of_tilde_genSections`. Project-local. -/
theorem module_finite_sections_of_quasicoherentData {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (q : SheafOfModules.QuasicoherentData.{u, u, u, u} F)
    [q.IsFinitePresentation] (i : q.I) {V : X.Opens} (hV : IsAffineOpen V)
    (hle : V ≤ q.X i) :
    Module.Finite Γ(X, V) Γ(F, V) := by
  -- slice generators of the cover member, with their finiteness
  haveI hσ₀ : (q.presentation i).generators.IsFiniteType := inferInstance
  -- the open-immersion factorization `k` of `fromSpec` through the cover member
  have hrange : Set.range hV.fromSpec.base ⊆ Set.range (Scheme.Opens.ι (q.X i)).base := by
    rw [hV.range_fromSpec, Scheme.Opens.range_ι]
    exact hle
  haveI hklift : IsOpenImmersion
      (IsOpenImmersion.lift (Scheme.Opens.ι (q.X i)) hV.fromSpec hrange ≫
        Scheme.Opens.ι (q.X i)) := by
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  haveI hk : IsOpenImmersion
      (IsOpenImmersion.lift (Scheme.Opens.ι (q.X i)) hV.fromSpec hrange) :=
    IsOpenImmersion.of_comp _ (Scheme.Opens.ι (q.X i))
  haveI : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      (Scheme.Modules.pullback
        (IsOpenImmersion.lift (Scheme.Opens.ι (q.X i)) hV.fromSpec hrange)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction _).leftAdjoint_preservesColimits
  -- pseudofunctoriality: composite pullback = pullback of `fromSpec`
  let e₄ : (Scheme.Modules.pullback
      (IsOpenImmersion.lift (Scheme.Opens.ι (q.X i)) hV.fromSpec hrange)).obj
        ((Scheme.Modules.pullback (Scheme.Opens.ι (q.X i))).obj F) ≅
      (Scheme.Modules.pullback hV.fromSpec).obj F :=
    (Scheme.Modules.pullbackComp
        (IsOpenImmersion.lift (Scheme.Opens.ι (q.X i)) hV.fromSpec hrange)
        (Scheme.Opens.ι (q.X i))).app F ≪≫
      (Scheme.Modules.pullbackCongr (IsOpenImmersion.lift_fac _ _ hrange)).app F
  -- the 01I8 tilde identification of the pullback along `fromSpec`
  obtain ⟨⟨e₅, -⟩⟩ := tildeIso_of_isQuasicoherent_isAffineOpen F hV
  -- transport the generators all the way onto the tilde
  let σ₆ : (tilde (ModuleCat.of Γ(X, V) Γ(F, V))).GeneratingSections :=
    (((((q.presentation i).generators.map
        (overRestrictEquiv (q.X i)).functor (overRestrictUnitIso (q.X i))).ofEpi
          (overRestrictPullbackIso (q.X i) F).hom).map
        (Scheme.Modules.pullback
          (IsOpenImmersion.lift (Scheme.Opens.ι (q.X i)) hV.fromSpec hrange))
        (pullbackOpenImmersionUnitIso
          (IsOpenImmersion.lift (Scheme.Opens.ι (q.X i)) hV.fromSpec hrange)).symm).ofEpi
      e₄.hom).ofEpi e₅.hom
  haveI : σ₆.IsFiniteType := inferInstanceAs
    ((((((q.presentation i).generators.map _ _).ofEpi _).map _ _).ofEpi _).ofEpi
      e₅.hom).IsFiniteType
  exact module_finite_of_tilde_genSections (ModuleCat.of Γ(X, V) Γ(F, V)) σ₆

/-- **Every point has arbitrarily small affine neighbourhoods with finitely
generated sections** (Stacks 01PC, finite-type half; chart-supply form). For a
finitely presented sheaf of modules `F` on `X`, every point `x` in an open `O` has
an affine open neighbourhood `V ≤ O` with `Γ(F, V)` a finite `Γ(X, V)`-module.
This is the chart supply consumed by generic flatness (Nitsure §4).
Project-local. -/
theorem exists_affine_finite_sections_nhds {X : Scheme.{u}} (F : X.Modules)
    [F.IsFinitePresentation] (x : X) (O : X.Opens) (hxO : x ∈ O) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ O ∧
      Module.Finite Γ(X, V) Γ(F, V) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  haveI := hq
  -- `x` lies in some member of the presenting cover
  obtain ⟨U', f, hf, hxU'⟩ := q.coversTop ⊤ x (TopologicalSpace.Opens.mem_top x)
  obtain ⟨i, ⟨g⟩⟩ := hf
  have hxi : x ∈ q.X i := leOfHom g hxU'
  -- shrink to an affine open inside `O ⊓ q.X i`
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((O ⊓ q.X i : X.Opens) : Set X) from ⟨hxO, hxi⟩) (O ⊓ q.X i).2
  have hVle' : V ≤ O ⊓ q.X i := hVle
  exact ⟨V, hV, hxV, hVle'.trans inf_le_left,
    module_finite_sections_of_quasicoherentData F q i hV (hVle'.trans inf_le_right)⟩

end Scheme.Modules

end AlgebraicGeometry
