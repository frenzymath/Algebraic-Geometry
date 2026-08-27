/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.FGAPicRepresentability
import AlgebraicJacobian.Picard.RigidPushforward
import AlgebraicJacobian.Cohomology.MayerVietorisCover

/-!
# Filtered-colimit reduction over affine bases (campaign `B2`)

Milestone `B2` of the `instHasPicScheme` campaign
(`informal/pic-representability-campaign.md`, Part II): on an affine base
`T = Spec A` with `A` a `k`-algebra, `A` is the filtered union of its finitely
generated `k`-subalgebras, and the finitely-presented data feeding the Picard
campaign descend to a finite stage (Stacks `0B8W`-grade statements, pinned in
elementary `∃`-form).  This is the systematic reduction from arbitrary affine
bases to *noetherian* affine bases that `B4` (degree decomposition) and `G1`
(spread-to-finite-Galois-level) consume against the noetherian-pinned engines
(`B3`, flattening stratification).

## Statement audits (campaign house rule: recorded BEFORE proving)

* **Exhaustion pin (all provable statements below).**  VERDICT: TRUE, and
  *stronger than the generic filtered-colimit form*: since `k` is a field,
  every stage map `R ⊗[k] S → R ⊗[k] A` (for `S ≤ A` a subalgebra) is
  **injective** (`⊗` over a field preserves injections), so the colimit
  `A = colim A_i` over finitely generated subalgebras is literally a directed
  *union* and equalities reflect at *every* stage — no "equal at a later
  stage" bookkeeping is needed for equalities of descended elements, only for
  descended *properties* (unit-ness, coboundary relations).  The literal
  categorical statement "`A = colim A_i` in `CommAlg k`" is not formalized;
  the pinned form (every element lies in a f.g. stage + stage maps injective +
  transition triangles) is the exact content Stacks `0B8W`/EGA IV 8.5 proofs
  consume.  Over a general (non-field) base ring injectivity FAILS and the
  statements below would need genuine re-pinning — the `Field k` hypothesis is
  load-bearing, not cosmetic.

* **(a) invertible sheaves as 2-affine cocycle data — HONEST-PRESENTATION
  AUDIT.**  VERDICT: TRUE at the *pinned cocycle-datum level* and FALSE at the
  naive "every invertible sheaf on `C_A`" level **for the fixed standard
  cover**: a Čech `1`-cocycle for the 2-chart cover `{U₁, U₂}` presents
  exactly the bundles trivial on both (base-changed) charts, and these form a
  *proper* subgroup of `Pic(C_A)` in general, already at `A = k`.
  Counterexample: `C = E` an elliptic curve, `U₁ = E ∖ {0}`; for a rational
  point `P ≠ 0`, `O_{U₁}(P)` is trivial iff some `f ∈ k(E)` has
  `div f = P − 0` (the only missing point is `0` and degrees force the
  coefficient), iff `O_E(P − 0)` is already trivial on `E`; so every
  nontrivial degree-`0` class stays nontrivial on the chart `U₁`, and its
  bundle admits NO cocycle presentation on the standard cover.  Hence `B2(a)`
  is pinned as: **every 2-affine MV cocycle datum over `A` descends to a
  finitely generated stage** (`exists_fg_mvCocycle_descent`, proved), while
  the sheaf-level "every invertible sheaf descends" is the separate TRUE
  statement gated in `PicScheme.HasPicSharpFgDescent` (its proof needs
  bundle-dependent trivializing covers, i.e. the `AffineTransitionLimit`
  tower for `C_A = lim C_{A_i}` plus finitely-presented-module descent — the
  mathlib gap recorded in the W1-F dossier §5).

* **(b) `DivFamily` descent.**  VERDICT: TRUE as pinned (`∃`-form up to
  `DivFamily.Rel`): all fields of `Scheme.DivFamily` are finitely-presented
  data over the finitely presented `C_A → Spec A` (`C` is of finite type over
  the field `k`), so EGA IV 8.5.2 (f.p. modules and homs descend through the
  limit), 11.2.6 (flatness of a f.p. module descends to a finite stage —
  needs `C_A/Spec A` of finite presentation, satisfied), 8.10.5(xii)
  (properness of the support descends), plus finite-locally-free descent for
  the invertible kernel (Stacks `0B8W`; kernels commute with the transition
  base changes at flat stages by the in-tree flat-kernel base change
  `Modules.mono_pullback_map_kernel_ι`) give the finite stage.  GATED as
  `HasDivFamilyFgDescent` (Prop-class, NO instance): the in-tree wall is the
  absence of any presentation of sheaves of modules on `C_A` as colimits of
  stage pullbacks; mathlib's f.p.-module filtered-colimit descent is
  localization-shaped only (`Algebra/Module/FinitePresentation.lean`, W1-F §5).

* **(c) picSharp-class equality descent.**  VERDICT: TRUE: an `H_T`-coset
  equality over `A` is witnessed by finitely-presented data (an invertible
  `N` on `Spec A` and an iso `L ≅ π^*N ⊗ L'`), which descends by the same
  engines.  At the cocycle level this is PROVED unconditionally
  (`exists_fg_le_mvCoboundaryRel_transitionMap`); at the sheaf level it is
  the second clause of the `HasPicSharpFgDescent` gate.

* **(d) package.**  VERDICT: TRUE.  "The restriction of `picSharp`/`DivFunctor`
  to affines preserves the filtered colimit `A = colim A_i`" is pinned in
  elementary `∃`-form as the two clauses (descend + equalize at a finite
  stage) of the two gates — the same `∃`-form mathlib's own
  `AffineTransitionLimit` engines use (Stacks `01ZC`) and the form the
  consumers `B4`/`G1` cite.  The cocycle-level package is proved
  unconditionally in §2.  No categorical `colim`-carrier is introduced: the
  `∃`-form is strictly stronger for consumers (it names the stage).

## Contents

* §1 (`AlgebraicJacobian.FGDescent`): the directed exhaustion of `A` by
  finitely generated `k`-subalgebras and the stage/transition maps
  `R ⊗[k] S →ₐ[k] R ⊗[k] A` — injectivity, element descent, finite-family
  descent, unit descent, unit reflection.
* §2: two-chart Čech cocycle descent for an abstract chart triple
  `ρ₀ : R₀ →ₐ[k] R₀₁ ← R₁ : ρ₁` (in the campaign instantiation: the section
  rings of the standard `AffineCoverMVSquare` of `C` and its restrictions,
  base-changed to `A` through `globalSectionsBaseChangeAlgEquiv`): cocycle
  descent (a), coboundary-relation calculus and descent (c)/(d).
* §3 (`AlgebraicGeometry.Scheme`): geometric anchors — `specOver`/`specOverMap`
  (Spec of a `k`-algebra as an object of `Over (Spec k)`, functorially in
  algebra maps), `AffineCoverMVSquare.preimage` (a 2-affine MV cover pulls
  back along any affine morphism), and the base-changed standard cover
  `AffineCoverMVSquare.baseChangeSpecOver` of `C_A`.
* §4: the two sheaf-level gates `HasDivFamilyFgDescent` (b) and
  `PicScheme.HasPicSharpFgDescent` (c)+(d), Prop-classes with NO instances,
  plus the `DivFunctor`-level consumer corollaries and the
  reduce-to-noetherian helper `Subalgebra.FG.isNoetherianRing`.

Campaign reference: `informal/pic-representability-campaign.md` Part II `B2`
(plan lines 99–101), W1-F dossier §5 (mathlib engine inventory; the engines
`Algebra/Category/Ring/FinitePresentation.lean` and
`AlgebraicGeometry/AffineTransitionLimit.lean` remain available for the gate
discharges but are NOT needed for the subalgebra-union layer below, which is
elementary and yields stage-exact equalities).
-/

universe u v w

open TensorProduct

namespace AlgebraicJacobian.FGDescent

/-! ## §1. Directed exhaustion by finitely generated subalgebras -/

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]

/-- Every element of a commutative `k`-algebra lies in a finitely generated
`k`-subalgebra (namely `Algebra.adjoin k {a}`).  Together with
`Subalgebra.FG.sup` (directedness) this is the exhaustion
`A = ⋃ (S : Subalgebra k A) (_ : S.FG), S` underlying the whole `B2` brick. -/
theorem exists_fg_mem (a : A) : ∃ S : Subalgebra k A, S.FG ∧ a ∈ S :=
  ⟨Algebra.adjoin k {a}, by simpa using Subalgebra.fg_adjoin_finset {a},
    Algebra.self_mem_adjoin_singleton k a⟩

variable (R : Type w) [CommRing R] [Algebra k R]

/-- The **stage map** of the filtered-colimit presentation: the canonical
`k`-algebra map `R ⊗[k] S → R ⊗[k] A` induced by a subalgebra `S ≤ A`.
In the campaign instantiation `R` is a section ring of the standard 2-affine
cover of the curve `C` and `S` runs over the finitely generated stages of the
base ring `A`.  Injective because `k` is a field (`stageMap_injective`). -/
def stageMap (S : Subalgebra k A) : R ⊗[k] S →ₐ[k] R ⊗[k] A :=
  Algebra.TensorProduct.map (AlgHom.id k R) S.val

@[simp]
lemma stageMap_tmul (S : Subalgebra k A) (r : R) (s : S) :
    stageMap R S (r ⊗ₜ s) = r ⊗ₜ (s : A) :=
  rfl

/-- The **transition map** between two stages `S ≤ T` of the filtered-colimit
presentation, `R ⊗[k] S → R ⊗[k] T`. -/
def transitionMap {S T : Subalgebra k A} (h : S ≤ T) :
    R ⊗[k] S →ₐ[k] R ⊗[k] T :=
  Algebra.TensorProduct.map (AlgHom.id k R) (Subalgebra.inclusion h)

@[simp]
lemma transitionMap_tmul {S T : Subalgebra k A} (h : S ≤ T) (r : R) (s : S) :
    transitionMap R h (r ⊗ₜ s) = r ⊗ₜ Subalgebra.inclusion h s :=
  rfl

/-- Transition triangle: the stage maps are compatible with the transitions,
`stageMap T ∘ transitionMap (S ≤ T) = stageMap S`. -/
theorem stageMap_comp_transitionMap {S T : Subalgebra k A} (h : S ≤ T) :
    (stageMap R T).comp (transitionMap R h) = stageMap R S := by
  rw [stageMap, stageMap, transitionMap, ← Algebra.TensorProduct.map_comp]
  simp

/-- Pointwise transition triangle. -/
theorem stageMap_transitionMap_apply {S T : Subalgebra k A} (h : S ≤ T)
    (x : R ⊗[k] S) :
    stageMap R T (transitionMap R h x) = stageMap R S x := by
  rw [← AlgHom.comp_apply, stageMap_comp_transitionMap]

/-- **Stage maps are injective.**  Because `k` is a field, `R` is a flat
(indeed free) `k`-module, so tensoring the injection `S ↪ A` with `R`
preserves injectivity.  This is what upgrades the filtered colimit to a
directed *union*: equalities of descended elements reflect at every stage
(no later-stage equalization needed), which is strictly stronger than the
generic Stacks `0B8W` bookkeeping. -/
theorem stageMap_injective (S : Subalgebra k A) :
    Function.Injective (stageMap R S) := by
  have h : (stageMap R S).toLinearMap = LinearMap.lTensor R S.val.toLinearMap :=
    TensorProduct.ext' fun r s => rfl
  intro x y hxy
  refine Module.Flat.lTensor_preserves_injective_linearMap (M := R)
    S.val.toLinearMap (fun a b hab => Subtype.ext hab) ?_
  rw [← h]
  exact hxy

/-- **Element descent** (Stacks `0B8W`, elementary form): every element of
`R ⊗[k] A` comes from `R ⊗[k] S` for some finitely generated `k`-subalgebra
`S ≤ A`. -/
theorem exists_fg_mem_range_stageMap (x : R ⊗[k] A) :
    ∃ S : Subalgebra k A, S.FG ∧ ∃ y : R ⊗[k] S, stageMap R S y = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · exact ⟨⊥, Subalgebra.fg_bot, 0, map_zero _⟩
  · intro r a
    exact ⟨Algebra.adjoin k {a}, by simpa using Subalgebra.fg_adjoin_finset {a},
      r ⊗ₜ ⟨a, Algebra.self_mem_adjoin_singleton k a⟩, rfl⟩
  · rintro x y ⟨S₁, hS₁, x₁, hx₁⟩ ⟨S₂, hS₂, y₂, hy₂⟩
    refine ⟨S₁ ⊔ S₂, hS₁.sup hS₂,
      transitionMap R (le_sup_left : S₁ ≤ S₁ ⊔ S₂) x₁
        + transitionMap R (le_sup_right : S₂ ≤ S₁ ⊔ S₂) y₂, ?_⟩
    rw [map_add, stageMap_transitionMap_apply, stageMap_transitionMap_apply,
      hx₁, hy₂]

/-- Monotonicity of the stage images: anything descended to `S` is descended
to every larger stage `T ≥ S`. -/
theorem exists_stageMap_eq_of_le {S T : Subalgebra k A} (h : S ≤ T)
    {x : R ⊗[k] A} (hx : ∃ y : R ⊗[k] S, stageMap R S y = x) :
    ∃ y : R ⊗[k] T, stageMap R T y = x := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨transitionMap R h y, stageMap_transitionMap_apply R h y⟩

/-- **Finite-family descent**: finitely many elements of `R ⊗[k] A` descend
to a *common* finitely generated stage (directedness via `Finset.sup`).
This is the form `G1` uses to spread a finite glueing datum to a finite
level. -/
theorem exists_fg_forall_mem_range_stageMap {ι : Type*} [Finite ι]
    (f : ι → R ⊗[k] A) :
    ∃ S : Subalgebra k A, S.FG ∧ ∀ i, ∃ y : R ⊗[k] S, stageMap R S y = f i := by
  cases nonempty_fintype ι
  choose Sf hSf hmem using fun i => exists_fg_mem_range_stageMap R (f i)
  refine ⟨Finset.univ.sup Sf, ?_, fun i =>
    exists_stageMap_eq_of_le R (Finset.le_sup (Finset.mem_univ i)) (hmem i)⟩
  exact Finset.sup_induction Subalgebra.fg_bot (fun a ha b hb => ha.sup hb)
    fun i _ => hSf i

/-- **Unit descent** (Stacks `0B8W` for `𝔾ₘ`-valued data): a unit of
`R ⊗[k] A` descends, *as a unit*, to a finitely generated stage — descend the
element and its inverse to a common stage and reflect the equation
`x·y = 1` by injectivity of the stage map. -/
theorem exists_fg_isUnit_stageMap_eq {u : R ⊗[k] A} (hu : IsUnit u) :
    ∃ S : Subalgebra k A, S.FG ∧
      ∃ x : R ⊗[k] S, IsUnit x ∧ stageMap R S x = u := by
  obtain ⟨S, hS, hmem⟩ := exists_fg_forall_mem_range_stageMap R
    ![u, ((hu.unit⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A)]
  obtain ⟨x, hx⟩ := hmem 0
  obtain ⟨y, hy⟩ := hmem 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
  have hxy : x * y = 1 := by
    apply stageMap_injective R S
    rw [map_mul, map_one, hx, hy, IsUnit.mul_val_inv]
  exact ⟨S, hS, x, IsUnit.of_mul_eq_one y hxy, hx⟩

/-- **Unit reflection at a larger stage**: if a stage element becomes a unit
over `A`, it is already a unit at some larger finitely generated stage.
(At the *same* stage this is false — the inverse need not live there — which
is exactly the "descend the property, not just the element" phenomenon of
filtered colimits.) -/
theorem exists_fg_le_isUnit_transitionMap {S : Subalgebra k A} (hS : S.FG)
    {x : R ⊗[k] S} (hx : IsUnit (stageMap R S x)) :
    ∃ (T : Subalgebra k A) (hle : S ≤ T), T.FG ∧
      IsUnit (transitionMap R hle x) := by
  obtain ⟨S', hS', y, hy, hy'⟩ := exists_fg_isUnit_stageMap_eq R hx
  refine ⟨S ⊔ S', le_sup_left, hS.sup hS', ?_⟩
  have heq : transitionMap R (le_sup_left : S ≤ S ⊔ S') x
      = transitionMap R (le_sup_right : S' ≤ S ⊔ S') y := by
    apply stageMap_injective R (S ⊔ S')
    rw [stageMap_transitionMap_apply, stageMap_transitionMap_apply, hy']
  rw [heq]
  exact hy.map (transitionMap R le_sup_right)

/-! ## §2. Two-chart Čech cocycle descent (campaign `B2(a)`, `(c)`, `(d)`)

An invertible sheaf on `C_A` that is trivial on the two charts of the standard
`AffineCoverMVSquare` (base-changed to `A`) *is* a unit of the overlap section
ring `Γ((U₁ ⊓ U₂)_A) ≅ Γ(U₁ ⊓ U₂) ⊗[k] A` (the identification is `B0`'s
`globalSectionsBaseChangeAlgEquiv`; see the honest-presentation audit in the
module docstring), and two cocycles present `H_T`-equal `picSharp` classes iff
they differ by a Čech coboundary `(ρ₀ a)·(ρ₁ b)⁻¹` with `a`, `b` units of the
base-changed chart rings.  We work with an abstract chart triple
`ρ₀ : R₀ →ₐ[k] R₀₁ ← R₁ : ρ₁` — for the standard cover, `R₀ = Γ(C, U₁)`,
`R₁ = Γ(C, U₂)`, `R₀₁ = Γ(C, U₁ ⊓ U₂)` with the restriction maps — so the
descent theorems below apply verbatim to any finite refinement as well. -/

section Cocycle

/-- Base change `R ⊗[k] B → R' ⊗[k] B` of a `k`-algebra map `ρ : R → R'` (a
chart restriction map of the MV cover) along the identity of the base factor
`B`. -/
def rTensorAlgHom {R R' : Type w} [CommRing R] [CommRing R']
    [Algebra k R] [Algebra k R'] (ρ : R →ₐ[k] R')
    (B : Type v) [CommRing B] [Algebra k B] :
    R ⊗[k] B →ₐ[k] R' ⊗[k] B :=
  Algebra.TensorProduct.map ρ (AlgHom.id k B)

@[simp]
lemma rTensorAlgHom_tmul {R R' : Type w} [CommRing R] [CommRing R']
    [Algebra k R] [Algebra k R'] (ρ : R →ₐ[k] R')
    (B : Type v) [CommRing B] [Algebra k B] (r : R) (b : B) :
    rTensorAlgHom ρ B (r ⊗ₜ b) = ρ r ⊗ₜ b :=
  rfl

/-- Naturality of the chart base change against base-factor maps: base-changing
the chart map `ρ` commutes with applying `φ` on the base factor. -/
theorem rTensorAlgHom_comm {R R' : Type w} [CommRing R] [CommRing R']
    [Algebra k R] [Algebra k R'] (ρ : R →ₐ[k] R')
    {B B' : Type v} [CommRing B] [CommRing B'] [Algebra k B] [Algebra k B']
    (φ : B →ₐ[k] B') :
    (Algebra.TensorProduct.map (AlgHom.id k R') φ).comp (rTensorAlgHom ρ B)
      = (rTensorAlgHom ρ B').comp
          (Algebra.TensorProduct.map (AlgHom.id k R) φ) := by
  rw [rTensorAlgHom, rTensorAlgHom, ← Algebra.TensorProduct.map_comp,
    ← Algebra.TensorProduct.map_comp]
  simp

/-- Stage-level naturality: the chart base change commutes with the stage
maps of §1. -/
theorem stageMap_rTensorAlgHom {R R' : Type w} [CommRing R] [CommRing R']
    [Algebra k R] [Algebra k R'] (ρ : R →ₐ[k] R')
    (S : Subalgebra k A) (x : R ⊗[k] S) :
    stageMap R' S (rTensorAlgHom ρ S x)
      = rTensorAlgHom ρ A (stageMap R S x) :=
  AlgHom.congr_fun (rTensorAlgHom_comm ρ S.val) x

variable {R₀ R₁ R₀₁ : Type w} [CommRing R₀] [CommRing R₁] [CommRing R₀₁]
  [Algebra k R₀] [Algebra k R₁] [Algebra k R₀₁]
  (ρ₀ : R₀ →ₐ[k] R₀₁) (ρ₁ : R₁ →ₐ[k] R₀₁)

/-- The **Čech coboundary relation** for the two-chart cover, base-changed to
the `k`-algebra `B`: two overlap elements `u`, `v` (in the cocycle reading:
transition data of chart-trivial invertible sheaves) differ by a coboundary
when `u · ρ₁(b) = ρ₀(a) · v` for units `a`, `b` of the base-changed chart
rings.  In multiplicative unit-free form (the two `IsUnit` witnesses carry the
invertibility), so the relation makes sense for all ring elements and no
`Units`-transport is needed; on units it is the usual
`u = ρ₀(a) · v · ρ₁(b)⁻¹`, i.e. `Ȟ¹`-class equality for the 2-chart cover. -/
def MVCoboundaryRel (B : Type v) [CommRing B] [Algebra k B]
    (u v : R₀₁ ⊗[k] B) : Prop :=
  ∃ a : R₀ ⊗[k] B, ∃ b : R₁ ⊗[k] B, IsUnit a ∧ IsUnit b ∧
    u * rTensorAlgHom ρ₁ B b = rTensorAlgHom ρ₀ B a * v

/-- Reflexivity of the coboundary relation (`a = b = 1`). -/
theorem mvCoboundaryRel_refl (B : Type v) [CommRing B] [Algebra k B]
    (u : R₀₁ ⊗[k] B) : MVCoboundaryRel ρ₀ ρ₁ B u u :=
  ⟨1, 1, isUnit_one, isUnit_one, by simp⟩

/-- Symmetry of the coboundary relation (invert the two chart units). -/
theorem MVCoboundaryRel.symm {B : Type v} [CommRing B] [Algebra k B]
    {u v : R₀₁ ⊗[k] B} (h : MVCoboundaryRel ρ₀ ρ₁ B u v) :
    MVCoboundaryRel ρ₀ ρ₁ B v u := by
  obtain ⟨a, b, ha, hb, heq⟩ := h
  refine ⟨((ha.unit⁻¹ : (R₀ ⊗[k] B)ˣ) : R₀ ⊗[k] B),
    ((hb.unit⁻¹ : (R₁ ⊗[k] B)ˣ) : R₁ ⊗[k] B),
    Units.isUnit _, Units.isUnit _, ?_⟩
  have h₀ : rTensorAlgHom ρ₀ B ((ha.unit⁻¹ : (R₀ ⊗[k] B)ˣ) : R₀ ⊗[k] B)
      * rTensorAlgHom ρ₀ B a = 1 := by
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  have h₁ : rTensorAlgHom ρ₁ B b
      * rTensorAlgHom ρ₁ B ((hb.unit⁻¹ : (R₁ ⊗[k] B)ˣ) : R₁ ⊗[k] B) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  linear_combination
    (-(v * rTensorAlgHom ρ₁ B ((hb.unit⁻¹ : (R₁ ⊗[k] B)ˣ) : R₁ ⊗[k] B))) * h₀
    + (rTensorAlgHom ρ₀ B ((ha.unit⁻¹ : (R₀ ⊗[k] B)ˣ) : R₀ ⊗[k] B) * u) * h₁
    + (-(rTensorAlgHom ρ₀ B ((ha.unit⁻¹ : (R₀ ⊗[k] B)ˣ) : R₀ ⊗[k] B)
        * rTensorAlgHom ρ₁ B ((hb.unit⁻¹ : (R₁ ⊗[k] B)ˣ) : R₁ ⊗[k] B))) * heq

/-- Transitivity of the coboundary relation (multiply the chart units). -/
theorem MVCoboundaryRel.trans {B : Type v} [CommRing B] [Algebra k B]
    {u v w : R₀₁ ⊗[k] B} (h : MVCoboundaryRel ρ₀ ρ₁ B u v)
    (h' : MVCoboundaryRel ρ₀ ρ₁ B v w) :
    MVCoboundaryRel ρ₀ ρ₁ B u w := by
  obtain ⟨a, b, ha, hb, heq⟩ := h
  obtain ⟨a', b', ha', hb', heq'⟩ := h'
  refine ⟨a * a', b * b', ha.mul ha', hb.mul hb', ?_⟩
  rw [map_mul, map_mul]
  linear_combination (rTensorAlgHom ρ₁ B b') * heq
    + (rTensorAlgHom ρ₀ B a) * heq'

/-- Pushforward of the coboundary relation along any base-factor map
`φ : B → B'` (in the campaign: further base change, stage inclusions,
transition maps). -/
theorem MVCoboundaryRel.map {B B' : Type v} [CommRing B] [CommRing B']
    [Algebra k B] [Algebra k B'] (φ : B →ₐ[k] B') {u v : R₀₁ ⊗[k] B}
    (h : MVCoboundaryRel ρ₀ ρ₁ B u v) :
    MVCoboundaryRel ρ₀ ρ₁ B'
      (Algebra.TensorProduct.map (AlgHom.id k R₀₁) φ u)
      (Algebra.TensorProduct.map (AlgHom.id k R₀₁) φ v) := by
  obtain ⟨a, b, ha, hb, heq⟩ := h
  refine ⟨Algebra.TensorProduct.map (AlgHom.id k R₀) φ a,
    Algebra.TensorProduct.map (AlgHom.id k R₁) φ b, ha.map _, hb.map _, ?_⟩
  have h₀ := AlgHom.congr_fun (rTensorAlgHom_comm (k := k) ρ₀ φ) a
  have h₁ := AlgHom.congr_fun (rTensorAlgHom_comm (k := k) ρ₁ φ) b
  simp only [AlgHom.comp_apply] at h₀ h₁
  rw [← h₀, ← h₁, ← map_mul, ← map_mul, heq]

/-- **Campaign `B2(a)` — cocycle descent** (Stacks `0B8W`-grade, cocycle
form): every invertible sheaf on `C_A` *presented as a 2-affine cocycle datum
on the standard cover* — i.e. every unit `u` of the base-changed overlap ring
`R₀₁ ⊗[k] A ≅ Γ((U₁ ⊓ U₂)_A)` — descends, as a unit, to `R₀₁ ⊗[k] S` for
some finitely generated `k`-subalgebra `S ≤ A`.  See the module docstring for
the honest-presentation audit (why "presented as a cocycle datum" is the
correct and maximal pin for the fixed cover). -/
theorem exists_fg_mvCocycle_descent {u : R₀₁ ⊗[k] A} (hu : IsUnit u) :
    ∃ S : Subalgebra k A, S.FG ∧
      ∃ u' : R₀₁ ⊗[k] S, IsUnit u' ∧ stageMap R₀₁ S u' = u :=
  exists_fg_isUnit_stageMap_eq R₀₁ hu

/-- **Campaign `B2(c)`/`(d)` — coboundary descent** (cocycle form): if two
stage cocycles become cohomologous over `A`, they are already cohomologous at
some larger finitely generated stage `T` — descend the two coboundary units
and reflect the coboundary equation by injectivity of the stage map.
Together with `exists_fg_mvCocycle_descent` (surjectivity) and
`stageMap_injective` (stage-exactness of element equalities) this says the
2-chart Čech `H¹` of the standard cover, restricted to affines, preserves the
filtered colimit `A = colim A_i` — the cocycle-level `B2(d)` package. -/
theorem exists_fg_le_mvCoboundaryRel_transitionMap {S : Subalgebra k A}
    (hS : S.FG) {u v : R₀₁ ⊗[k] S}
    (h : MVCoboundaryRel ρ₀ ρ₁ A (stageMap R₀₁ S u) (stageMap R₀₁ S v)) :
    ∃ (T : Subalgebra k A) (hle : S ≤ T), T.FG ∧
      MVCoboundaryRel ρ₀ ρ₁ T
        (transitionMap R₀₁ hle u) (transitionMap R₀₁ hle v) := by
  obtain ⟨a, b, ha, hb, heq⟩ := h
  obtain ⟨Sa, hSa, a', ha', haa⟩ := exists_fg_isUnit_stageMap_eq R₀ ha
  obtain ⟨Sb, hSb, b', hb', hbb⟩ := exists_fg_isUnit_stageMap_eq R₁ hb
  refine ⟨S ⊔ Sa ⊔ Sb, le_sup_left.trans le_sup_left, (hS.sup hSa).sup hSb,
    transitionMap R₀ (le_sup_right.trans le_sup_left : Sa ≤ S ⊔ Sa ⊔ Sb) a',
    transitionMap R₁ (le_sup_right : Sb ≤ S ⊔ Sa ⊔ Sb) b',
    ha'.map _, hb'.map _, ?_⟩
  apply stageMap_injective R₀₁ (S ⊔ Sa ⊔ Sb)
  rw [map_mul, map_mul, stageMap_transitionMap_apply,
    stageMap_transitionMap_apply, stageMap_rTensorAlgHom,
    stageMap_rTensorAlgHom, stageMap_transitionMap_apply,
    stageMap_transitionMap_apply, haa, hbb]
  exact heq

end Cocycle

end AlgebraicJacobian.FGDescent

/-! ## §3. Geometric anchors -/

namespace AlgebraicGeometry.Scheme

open CategoryTheory Limits

section SpecOver

variable (k : Type u) [CommRing k]

/-- `Spec` of a `k`-algebra `A`, as an object of `Over (Spec k)` with the
structure morphism `Spec (algebraMap k A)`.  The affine stage objects of the
`B2` filtered-colimit reduction (`A` itself and its finitely generated
subalgebras) all enter the campaign functors through this constructor. -/
noncomputable def specOver (A : Type u) [CommRing A] [Algebra k A] :
    Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))

@[simp]
lemma specOver_left (A : Type u) [CommRing A] [Algebra k A] :
    (specOver k A).left = Spec (CommRingCat.of A) :=
  rfl

@[simp]
lemma specOver_hom (A : Type u) [CommRing A] [Algebra k A] :
    (specOver k A).hom = Spec.map (CommRingCat.ofHom (algebraMap k A)) :=
  rfl

/-- The morphism of `Over (Spec k)` induced contravariantly by a `k`-algebra
map `f : B →ₐ[k] A`; for the subalgebra inclusions `S.val` and
`Subalgebra.inclusion` these are the stage/transition morphisms of the
affine tower `Spec A → Spec S`. -/
noncomputable def specOverMap {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (f : B →ₐ[k] A) :
    specOver k A ⟶ specOver k B :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom)
        ≫ Spec.map (CommRingCat.ofHom (algebraMap k B))
      = Spec.map (CommRingCat.ofHom (algebraMap k A))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg Spec.map
      (CommRingCat.hom_ext (RingHom.ext fun b => f.commutes b)))

@[simp]
lemma specOverMap_left {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (f : B →ₐ[k] A) :
    (specOverMap k f).left = Spec.map (CommRingCat.ofHom f.toRingHom) :=
  rfl

/-- `specOverMap` sends the identity algebra map to the identity. -/
lemma specOverMap_id (A : Type u) [CommRing A] [Algebra k A] :
    specOverMap k (AlgHom.id k A) = 𝟙 (specOver k A) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (AlgHom.id k A).toRingHom) = 𝟙 _
  rw [show (AlgHom.id k A).toRingHom = RingHom.id A from rfl,
    CommRingCat.ofHom_id, Spec.map_id]

/-- `specOverMap` is contravariantly functorial: transitions compose. -/
lemma specOverMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (f : B →ₐ[k] A) (g : C →ₐ[k] B) :
    specOverMap k f ≫ specOverMap k g = specOverMap k (f.comp g) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom f.toRingHom)
      ≫ Spec.map (CommRingCat.ofHom g.toRingHom)
    = Spec.map (CommRingCat.ofHom (f.comp g).toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end SpecOver

section MVPreimage

/- `AffineCoverMVSquare.preimage` (a 2-affine MV cover pulls back along any
affine morphism, `IsAffineOpen.preimage`) is provided by
`AlgebraicJacobian.Picard.RigidPushforward` (imported above). -/

/-- **The standard cover, base-changed to `A`** (campaign `B2(a)` geometric
anchor): the 2-affine MV cover of `C_A = C ×_k Spec A` obtained by pulling
the standard `AffineCoverMVSquare` of `C` back along the first projection.
The projection is affine because `Spec A → Spec k` is (affine morphisms are
stable under base change), so the base-changed charts and overlap are affine
and their section rings are identified with `Γ(C, U) ⊗[k] A` by `B0`'s
`globalSectionsBaseChangeAlgEquiv` — the identification under which the §2
cocycle-descent theorems are the `B2(a)`/`(c)` statements for `C_A`. -/
noncomputable def AffineCoverMVSquare.baseChangeSpecOver
    {k : Type u} [CommRing k] (C : Over (Spec (CommRingCat.of k)))
    (S : C.left.AffineCoverMVSquare)
    (A : Type u) [CommRing A] [Algebra k A] :
    (Limits.pullback C.hom (specOver k A).hom).AffineCoverMVSquare :=
  haveI : IsAffineHom ((specOver k A).hom) :=
    inferInstanceAs (IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
  haveI : IsAffineHom (Limits.pullback.fst C.hom (specOver k A).hom) :=
    MorphismProperty.pullback_fst _ _ ‹_›
  S.preimage (Limits.pullback.fst C.hom (specOver k A).hom)

end MVPreimage

/-! ## §4. The sheaf-level gates and consumer corollaries -/

section Gates

variable {k : Type u} [Field k]

/-- Reduce-to-noetherian helper (the point of `B2` for the `B4`/`B3`
consumers): a finitely generated subalgebra stage of a `k`-algebra is a
noetherian ring (Hilbert basis via `Algebra.FiniteType`), so the
noetherian-pinned engines (`B3` rigid pushforward, flattening stratification)
apply over `Spec S` after descending. -/
theorem _root_.Subalgebra.FG.isNoetherianRing {A : Type u} [CommRing A]
    [Algebra k A] {S : Subalgebra k A} (hS : S.FG) :
    IsNoetherianRing S := by
  have : Algebra.FiniteType k S := by
    rw [← Subalgebra.fg_iff_finiteType]
    exact hS
  exact Algebra.FiniteType.isNoetherianRing k S

/-- **Campaign `B2(b)` gate** (Prop-class, NO instance — house wall pattern):
every `DivFamily` on `C_A/Spec A` descends, up to `DivFamily.Rel`, to a
finitely generated stage `Spec S`, and stage families identified over `A` are
identified at a larger finitely generated stage.

AUDIT (recorded before any discharge attempt): both clauses are TRUE — the
fields of `Scheme.DivFamily` are finitely presented data over the finitely
presented morphism `C_A → Spec A` (`C` is of finite type over the field `k`),
so they descend through the filtered colimit by EGA IV 8.5.2 (f.p. modules
and homs), 11.2.6 (flatness at a finite stage), 8.10.5(xii) (properness of
the support), and Stacks `0B8W` finite-locally-free descent for the
invertible kernel (kernel formation commutes with the transition base changes
at flat stages by `Modules.mono_pullback_map_kernel_ι`).  WALL: no in-tree
presentation of modules on `C_A` as colimits of stage pullbacks; mathlib's
f.p.-module filtered-colimit descent is localization-shaped only (W1-F §5).
DISCHARGE ROUTE: the `AffineTransitionLimit` tower `C_A = lim C_S`
(`Scheme.exists_isOpenCover_and_isAffine`, Stacks `01ZC`) + a f.p.-module
descent brick, or a cocycle-level presentation of divisor families through
§2.  The two clauses are the `∃`-form of "`DivFunctor` restricted to affines
preserves the filtered colimit `A = colim A_i`" (`B2(d)` for `Div`). -/
class HasDivFamilyFgDescent (C : Over (Spec (CommRingCat.of k))) : Prop where
  /-- Every divisor family over `Spec A` descends, up to `Rel`, to a
  finitely generated stage. -/
  exists_fg_descent :
    ∀ (A : Type u) [CommRing A] [Algebra k A]
      (x : DivFamily C.hom (specOver k A)),
      ∃ S : Subalgebra k A, S.FG ∧
        ∃ y : DivFamily C.hom (specOver k S),
          (DivFamily.pullbackAlong (specOverMap k S.val) y).Rel x
  /-- Stage families identified over `A` are identified at a larger finitely
  generated stage. -/
  exists_fg_le_rel :
    ∀ (A : Type u) [CommRing A] [Algebra k A] (S : Subalgebra k A), S.FG →
      ∀ y y' : DivFamily C.hom (specOver k S),
        (DivFamily.pullbackAlong (specOverMap k S.val) y).Rel
          (DivFamily.pullbackAlong (specOverMap k S.val) y') →
        ∃ (T : Subalgebra k A) (hle : S ≤ T), T.FG ∧
          (DivFamily.pullbackAlong (specOverMap k (Subalgebra.inclusion hle)) y).Rel
            (DivFamily.pullbackAlong (specOverMap k (Subalgebra.inclusion hle)) y')

/-- Consumer corollary of the `B2(b)` gate at the `DivFunctor` level
(the form `B4`/`D1'` cite): every `T`-point of `Div_{C/k}` over `T = Spec A`
comes from a finitely generated stage. -/
theorem DivFunctor.exists_fg_descent (C : Over (Spec (CommRingCat.of k)))
    [HasDivFamilyFgDescent C]
    (A : Type u) [CommRing A] [Algebra k A]
    (x : (DivFunctor C.hom).obj (Opposite.op (specOver k A))) :
    ∃ S : Subalgebra k A, S.FG ∧
      ∃ y : (DivFunctor C.hom).obj (Opposite.op (specOver k S)),
        (DivFunctor C.hom).map (specOverMap k S.val).op y = x := by
  induction x using Quotient.ind with
  | _ x =>
    obtain ⟨S, hS, y, hy⟩ := HasDivFamilyFgDescent.exists_fg_descent A x
    refine ⟨S, hS, Quotient.mk _ y, ?_⟩
    exact Quotient.sound hy

/-- Consumer corollary of the `B2(b)` gate at the `DivFunctor` level, second
clause: stage classes equalized over `A` are equal at a larger finitely
generated stage. -/
theorem DivFunctor.exists_fg_le_map_eq (C : Over (Spec (CommRingCat.of k)))
    [HasDivFamilyFgDescent C]
    (A : Type u) [CommRing A] [Algebra k A] (S : Subalgebra k A) (hS : S.FG)
    (y y' : (DivFunctor C.hom).obj (Opposite.op (specOver k S)))
    (h : (DivFunctor C.hom).map (specOverMap k S.val).op y
      = (DivFunctor C.hom).map (specOverMap k S.val).op y') :
    ∃ (T : Subalgebra k A) (hle : S ≤ T), T.FG ∧
      (DivFunctor C.hom).map (specOverMap k (Subalgebra.inclusion hle)).op y
        = (DivFunctor C.hom).map
            (specOverMap k (Subalgebra.inclusion hle)).op y' := by
  induction y using Quotient.ind with
  | _ x =>
    induction y' using Quotient.ind with
    | _ x' =>
      have h' : (DivFamily.pullbackAlong (specOverMap k S.val) x).Rel
          (DivFamily.pullbackAlong (specOverMap k S.val) x') := by
        apply Quotient.exact (s := DivFamily.setoid C.hom (specOver k A))
        exact h
      obtain ⟨T, hle, hT, hrel⟩ :=
        HasDivFamilyFgDescent.exists_fg_le_rel A S hS x x' h'
      exact ⟨T, hle, hT, Quotient.sound hrel⟩

open PicScheme in
/-- **Campaign `B2(c)`+`(d)` gate for `picSharp`** (Prop-class, NO instance —
house wall pattern): the restriction of the relative Picard functor
`picSharp C` to affine bases preserves the filtered colimit
`A = colim A_i` over finitely generated `k`-subalgebras, pinned in
elementary `∃`-form: (1) every `picSharp`-class over `Spec A` descends to a
finitely generated stage; (2) two stage classes equalized over `A` are equal
at a larger finitely generated stage.

AUDIT (recorded before any discharge attempt): both clauses are TRUE — an
invertible sheaf on the qcqs `C_A` is a finitely presented quasi-coherent
module, and Stacks `0B8W` (limits of qcqs schemes: f.p. modules over
`X = lim X_i` form the colimit of the stage categories, with invertibility
and isos descending) applied to the affine tower `C_A = lim C_S` gives clause
(1); the `H_T`-coset witness (an invertible `N` on `Spec A` and an iso
`L ≅ π^* N ⊗ L'`, `PicSharp.relPicRel`) is itself f.p. data and descends the
same way, giving clause (2).  Clause (2) is exactly `B2(c)` ("two bundles
isomorphic over `A` are isomorphic over some `A_i`", in the honest
`H_T`-quotient form the campaign uses).  WALL: sheaf-level descent needs
bundle-dependent trivializing covers — the fixed standard cover does NOT
suffice (elliptic-curve counterexample, module docstring) — i.e. the
`AffineTransitionLimit` tower + f.p.-module descent (mathlib gap, W1-F §5).
The cocycle-level analogues are PROVED unconditionally in §2
(`exists_fg_mvCocycle_descent`, `exists_fg_le_mvCoboundaryRel_transitionMap`).
DISCHARGE ROUTE: `AlgebraicGeometry/AffineTransitionLimit.lean` (Stacks
`01ZC`) + `Algebra/Category/Ring/FinitePresentation.lean` engines + a
f.p.-module descent brick; consumers: `B4` (descend `L`, apply the noetherian
`B3` engine at the f.g. — hence noetherian, `Subalgebra.FG.isNoetherianRing`
— stage, pull back), `G1` (spread the `J5` finite datum to a finite Galois
level over `k^s = colim` of finite subextensions). -/
class HasPicSharpFgDescent (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] : Prop where
  /-- Every `picSharp`-class over `Spec A` descends to a finitely generated
  stage. -/
  exists_fg_descent :
    ∀ (A : Type u) [CommRing A] [Algebra k A]
      (x : (picSharp C).obj (Opposite.op (specOver k A))),
      ∃ S : Subalgebra k A, S.FG ∧
        ∃ y : (picSharp C).obj (Opposite.op (specOver k S)),
          (picSharp C).map (specOverMap k S.val).op y = x
  /-- Stage classes equalized over `A` are equal at a larger finitely
  generated stage (`B2(c)`). -/
  exists_fg_le_map_eq :
    ∀ (A : Type u) [CommRing A] [Algebra k A] (S : Subalgebra k A), S.FG →
      ∀ y y' : (picSharp C).obj (Opposite.op (specOver k S)),
        (picSharp C).map (specOverMap k S.val).op y
          = (picSharp C).map (specOverMap k S.val).op y' →
        ∃ (T : Subalgebra k A) (hle : S ≤ T), T.FG ∧
          (picSharp C).map (specOverMap k (Subalgebra.inclusion hle)).op y
            = (picSharp C).map (specOverMap k (Subalgebra.inclusion hle)).op y'

end Gates

end AlgebraicGeometry.Scheme
