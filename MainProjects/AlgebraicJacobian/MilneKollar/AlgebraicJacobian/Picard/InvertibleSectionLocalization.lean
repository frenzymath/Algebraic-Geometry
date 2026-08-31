/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.QuotScheme
import AlgebraicJacobian.Picard.SectionGradedRing

/-!
# The invertible-section localization engine (Serre D2/D3, twisted halves)

The qcqs section-localization engine of `Picard/QuotScheme.lean`
(`exists_pow_smul_res_eq_zero_of_isCompact`, `exists_res_eq_pow_smul_of_isCompact`,
Stacks 01P0) is stated for basic opens of **global functions** `g ∈ Γ(X, 𝒪)`.  The
Serre D2/D3 heart ([Hartshorne] II.5.14, Stacks 01PW) needs it for the
**non-vanishing locus** `U_s` of a section `s` of an **invertible** sheaf `L`, with
the conclusion twisted by tensor powers of `L`:

* **(D3, vanishing half)** a global section `u ∈ Γ(X, F ⊗ L^{⊗m})` vanishing on
  `U_s` is annihilated by a power of `s` — `s^{⊗N} ⊗ u = 0` in `Γ(X, F ⊗ L^{⊗(N+m)})`;
* **(D2, extension half)** a section `t ∈ Γ(U_s, F ⊗ L^{⊗m})` becomes, after
  multiplication by a power `s^{⊗N}`, the restriction of a **global** section of
  `F ⊗ L^{⊗(N+m)}`.

## Vocabulary

The statements use only the section graded vocabulary of
`Picard/SectionGradedRing.lean` extended from the top open to **every** open:

* `twistedSMul` — the local graded action
  `Γ(U, L^{⊗i}) × Γ(U, F ⊗ L^{⊗j}) → Γ(U, F ⊗ L^{⊗(i+j)})`, the component at `op U`
  of the sheafification unit followed by the action comparison `moduleTensorPowAdd`.
  At `U = ⊤` it is *definitionally* the `GradedMonoid.GSMul` action of the section
  graded module (`sectionGradedModule_gmodule`).
* `smulIter` — the `N`-fold iterate `x ↦ s|_U ⋆ (s|_U ⋆ ⋯ (s|_U ⋆ x))` of the
  degree-one action of a global `s ∈ Γ(X, L^{⊗1})`, landing in degree
  `smulIterDeg N j = 1 + (1 + ⋯ + j)` (cast-free by construction;
  `smulIterDeg_eq : smulIterDeg N j = N + j`).  This is the shape in which the
  finite-generation endgame (D4, `lem:sectionGradedModule_fg`) iterates the
  coordinate action on the section graded module.
* `LineBundle.GammaTriv L V` — a **section-level trivialization** of `L` on `V`: a
  compatible family of `Γ(X, W)`-linear bijections `Γ(W, L) ≃ Γ(X, W)` for all
  opens `W ≤ V`.  It is produced from a sheaf-level trivialization
  `L|_V ≅ 𝒪_V` (the `IsLocallyTrivial` chart data) by `GammaTriv.ofRestrictIso`,
  and transported across isomorphisms by `GammaTriv.ofIso` (in particular from
  `L` to `L^{⊗1}` via `tensorPowOneIso`).
* `LineBundle.nonvanishingLocus L s` — the non-vanishing locus `U_s`: the union,
  over all section-level trivialized opens `(V, T)`, of the basic opens
  `D(T(s|_V))`.  On any trivialized chart it agrees with the basic open of the
  trivialized coordinate (`nonvanishingLocus_inf_chart` — well-definedness is the
  transition-unit argument: two trivializations differ by multiplication by a
  unit, which does not move basic opens).

## The engine

The chartwise reduction is `smulIter_res_eq_gen_pow_smul`: on a trivialized chart
`(V, T)` the iterated `s`-action is `s^{⊗N} ⋆ x = g^N • (ε^{⊗N} ⋆ x)` where
`g := T(s|_V) ∈ Γ(X, V)` and `ε := T⁻¹(1)` is the local generator — so the twisted
action is the *untwisted* module action of `g` composed with the (injective-on-charts,
but never inverted) generator multiplication.  The untwisted qcqs engine applied to
`g` then yields, on each chart of a finite trivializing cover:

* `smulIter_eq_zero_of_res_eq_zero_of_gammaTriv` (D3 on a chart), assembled into
* `exists_smulIter_eq_zero_of_res_eq_zero` (**D3, global**) by sheaf separation
  over the finite cover, and
* `exists_smulIter_res_eq` (**D2, global**) by the normalize–kill–glue
  Mayer–Vietoris pattern of Stacks 01P0, with the overlap differences killed by
  the chartwise D3.

Blueprint: `lem:sectionGradedModule_fg` (`blueprint/src/chapters/Picard_QuotScheme.tex`).
Source: [Hartshorne] II.5.14 (a)/(b); Stacks 01PW, 01P0; [Nitsure] §1.
-/

set_option autoImplicit false
-- Graded-carrier coercion normalization exceeds the default depth at the localization and
-- finite-generation declarations; `1000` is sufficient for the whole file.
set_option maxRecDepth 1000

universe u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-! ## §0. Restriction bookkeeping (local clones of the `QuotScheme.lean` privates) -/

/-- Restriction maps of the underlying abelian presheaf of a sheaf of modules compose. -/
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

/-! ## §1. The local (any-open) graded action -/

/-- **The local graded action** (`def:twistedSMul`): the pairing
`Γ(U, L^{⊗i}) × Γ(U, F ⊗ L^{⊗j}) → Γ(U, F ⊗ L^{⊗(i+j)})` given by the component at
`op U` of the sheafification unit on the presheaf tensor product, followed by the
component of the action comparison isomorphism `moduleTensorPowAdd`.  This extends
the degreewise action of the section graded module (the `GradedMonoid.GSMul`
instance of `SectionGradedRing.lean`, which is this definition at `U = ⊤`,
`twistedSMul_top`) from the top open to every open — the multiplication map
"`x ↦ s ⊗ x`" of Serre's D2/D3 ([Hartshorne] II.5.14). -/
noncomputable def twistedSMul (F L : X.Modules) (i j : ℕ) (U : X.Opens)
    (r : Γ(tensorPow L i, U)) (x : Γ(moduleTensorPow F L j, U)) :
    Γ(moduleTensorPow F L (i + j), U) :=
  ((moduleTensorPowAdd F L i j).hom.val.app (op U)).hom
    ((((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (MonoidalCategory.tensorObj
          (C := _root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
          ((toPresheafOfModules X).obj (tensorPow L i))
          ((toPresheafOfModules X).obj (moduleTensorPow F L j)))).app (op U)).hom
      ((r : ↥(((toPresheafOfModules X).obj (tensorPow L i)).obj (op U)))
        ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]
        (x : ↥(((toPresheafOfModules X).obj (moduleTensorPow F L j)).obj (op U)))))

/-- At the top open the local graded action is definitionally the degreewise
action of the section graded module (`sectionGradedModule_gmodule`). -/
lemma twistedSMul_top (F L : X.Modules) (i j : ℕ)
    (r : sectionDeg L i) (x : moduleSectionDeg F L j) :
    twistedSMul F L i j ⊤ r x = GradedMonoid.GSMul.smul r x :=
  rfl

/-- The local graded action is compatible with restriction: restricting the product
is the product of the restrictions.  This is naturality of the sheafification unit
(a morphism of presheaves of modules) together with the objectwise formula for the
restriction of an elementary tensor. -/
lemma twistedSMul_res (F L : X.Modules) (i j : ℕ) {U V : X.Opens} (hVU : V ≤ U)
    (r : Γ(tensorPow L i, U)) (x : Γ(moduleTensorPow F L j, U)) :
    (moduleTensorPow F L (i + j)).presheaf.map (homOfLE hVU).op
        (twistedSMul F L i j U r x)
      = twistedSMul F L i j V
          ((tensorPow L i).presheaf.map (homOfLE hVU).op r)
          ((moduleTensorPow F L j).presheaf.map (homOfLE hVU).op x) := by
  -- Naturality of the comparison `moduleTensorPowAdd` (a morphism of sheaves of
  -- modules) moves the restriction inside; naturality of the sheafification unit
  -- then computes the restriction of the elementary tensor.
  have h1 := PresheafOfModules.naturality_apply
    ((moduleTensorPowAdd F L i j).hom.val) (homOfLE hVU).op
    ((((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (MonoidalCategory.tensorObj
          (C := _root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
          ((toPresheafOfModules X).obj (tensorPow L i))
          ((toPresheafOfModules X).obj (moduleTensorPow F L j)))).app (op U)).hom
      (r ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)] x))
  have h2 := PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (MonoidalCategory.tensorObj
          (C := _root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
          ((toPresheafOfModules X).obj (tensorPow L i))
          ((toPresheafOfModules X).obj (moduleTensorPow F L j))))
    (homOfLE hVU).op
    (r ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)] x)
  refine (h1.symm).trans ?_
  refine congrArg (((moduleTensorPowAdd F L i j).hom.val.app (op V)).hom) ?_
  exact h2.symm.trans
    (congrArg _ (PresheafOfModules.Monoidal.tensorObj_map_tmul (homOfLE hVU).op r x))

section SMulLinearity

/-- The `ModuleCat`-carrier module structure of a sheaf of modules over the
objectwise ring `𝒪_X(V)`, pulled directly from the underlying `ModuleCat` object.
Bare instance synthesis cannot see this structure — the objectwise ring
`(X.sheaf.obj ⋙ forget₂ …).obj (op V)` is presented as a `RingCat`, not the
`CommRingCat` `Γ(X, V)` that the section-module structure is keyed on — yet it is
*exactly* the structure the elementary presheaf tensor `⊗ₜ` is formed over.  Made a
section-local instance so the `ModuleCat`-carrier statements of the linearity aux
lemmas below elaborate; outside this section the untouched section-module
structure is the one in scope. -/
local instance moduleObjBridge (M : X.Modules) (V : X.Opens) :
    Module ↥((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ↥(((toPresheafOfModules X).obj M).obj (op V)) :=
  (((toPresheafOfModules X).obj M).obj (op V)).isModule

/-- Fully general form of `moduleObjBridge`: the same `ModuleCat`-carrier module
structure over the objectwise ring, for an **arbitrary** presheaf of modules.  The
rewrite motives of the linearity aux lemmas below mention the objectwise carriers of
several presheaves that are only *defeq* to `(toPresheafOfModules X).obj M` spellings
(the `𝟭`-applied and `sheafification ⋙ forget`-applied tensor presheaf from the
adjunction unit, and the `.val`-spellings of the sheaf objects), so instance search
needs the bridge keyed on a bare presheaf variable. -/
local instance moduleObjBridgeGen
    (P : _root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
    (V : X.Opens) :
    Module ↥((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) ↥(P.obj (op V)) :=
  (P.obj (op V)).isModule

/-- The same `ModuleCat`-carrier module structure, keyed on the *section* spelling
`Γ(M, V)` (the return spelling of `twistedSMul`), so that the outer scalar
multiplications of the linearity aux lemmas over the objectwise ring elaborate. -/
local instance moduleObjBridge' (M : X.Modules) (V : X.Opens) :
    Module ↥((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) Γ(M, V) :=
  (((toPresheafOfModules X).obj M).obj (op V)).isModule

/-- `𝒪_X(U)`-linearity of the local graded action in the module slot, `ModuleCat`
-carrier spelling: over the objectwise ring the action `twistedSMul U r` is the
composite of the two objectwise module maps (sheafification unit, action
comparison) with `r ⊗ₜ ·`, so linearity is `TensorProduct.tmul_smul` followed by
`_root_.map_smul` of the two `ModuleCat` morphisms.  (The qualification matters:
inside this namespace the bare name `map_smul` is `Scheme.Modules.map_smul`, whose
`M.presheaf.map`-headed LHS sends `erw`'s defeq matcher into a `whnf` blowup
against the categorical composite.) -/
private lemma twistedSMul_smul_right_aux (F L : X.Modules) (i j : ℕ) (U : X.Opens)
    (a : ↥((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)))
    (r : ↥(((toPresheafOfModules X).obj (tensorPow L i)).obj (op U)))
    (x : ↥(((toPresheafOfModules X).obj (moduleTensorPow F L j)).obj (op U))) :
    twistedSMul F L i j U r (a • x)
      = a • (twistedSMul F L i j U r x :
          ↥(((toPresheafOfModules X).obj (moduleTensorPow F L (i + j))).obj (op U))) := by
  unfold twistedSMul
  erw [TensorProduct.tmul_smul, _root_.map_smul, _root_.map_smul]
  rfl

/-- The local graded action is `Γ(X, U)`-linear in the module slot. -/
lemma twistedSMul_smul_right (F L : X.Modules) (i j : ℕ) (U : X.Opens)
    (a : Γ(X, U)) (r : Γ(tensorPow L i, U)) (x : Γ(moduleTensorPow F L j, U)) :
    twistedSMul F L i j U r (a • x)
      = a • twistedSMul F L i j U r x :=
  twistedSMul_smul_right_aux F L i j U a r x

/-- `𝒪_X(U)`-linearity of the local graded action in the line-bundle slot,
`ModuleCat`-carrier spelling.  (Same `_root_.map_smul` qualification as in
`twistedSMul_smul_right_aux`.) -/
private lemma twistedSMul_smul_left_aux (F L : X.Modules) (i j : ℕ) (U : X.Opens)
    (a : ↥((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)))
    (r : ↥(((toPresheafOfModules X).obj (tensorPow L i)).obj (op U)))
    (x : ↥(((toPresheafOfModules X).obj (moduleTensorPow F L j)).obj (op U))) :
    twistedSMul F L i j U (a • r) x
      = a • (twistedSMul F L i j U r x :
          ↥(((toPresheafOfModules X).obj (moduleTensorPow F L (i + j))).obj (op U))) := by
  unfold twistedSMul
  erw [← TensorProduct.smul_tmul', _root_.map_smul, _root_.map_smul]
  rfl

/-- The local graded action is `Γ(X, U)`-linear in the line-bundle slot. -/
lemma twistedSMul_smul_left (F L : X.Modules) (i j : ℕ) (U : X.Opens)
    (a : Γ(X, U)) (r : Γ(tensorPow L i, U)) (x : Γ(moduleTensorPow F L j, U)) :
    twistedSMul F L i j U (a • r) x
      = a • twistedSMul F L i j U r x :=
  twistedSMul_smul_left_aux F L i j U a r x

end SMulLinearity

/-- The local graded action is additive in the module slot. -/
lemma twistedSMul_add_right (F L : X.Modules) (i j : ℕ) (U : X.Opens)
    (r : Γ(tensorPow L i, U)) (x y : Γ(moduleTensorPow F L j, U)) :
    twistedSMul F L i j U r (x + y)
      = twistedSMul F L i j U r x + twistedSMul F L i j U r y := by
  unfold twistedSMul
  erw [TensorProduct.tmul_add, map_add, map_add]
  rfl

/-- The local graded action annihilates zero in the module slot. -/
lemma twistedSMul_zero_right (F L : X.Modules) (i j : ℕ) (U : X.Opens)
    (r : Γ(tensorPow L i, U)) :
    twistedSMul F L i j U r (0 : Γ(moduleTensorPow F L j, U)) = 0 := by
  unfold twistedSMul
  erw [TensorProduct.tmul_zero, map_zero, map_zero]
  rfl

/-- The local graded action is additive in the line-bundle slot. -/
lemma twistedSMul_add_left (F L : X.Modules) (i j : ℕ) (U : X.Opens)
    (r r' : Γ(tensorPow L i, U)) (x : Γ(moduleTensorPow F L j, U)) :
    twistedSMul F L i j U (r + r') x
      = twistedSMul F L i j U r x + twistedSMul F L i j U r' x := by
  unfold twistedSMul
  erw [TensorProduct.add_tmul, map_add, map_add]
  rfl

/-- The local graded action is subtractive in the module slot. -/
lemma twistedSMul_sub_right (F L : X.Modules) (i j : ℕ) (U : X.Opens)
    (r : Γ(tensorPow L i, U)) (x y : Γ(moduleTensorPow F L j, U)) :
    twistedSMul F L i j U r (x - y)
      = twistedSMul F L i j U r x - twistedSMul F L i j U r y := by
  have h := twistedSMul_add_right F L i j U r (x - y) y
  rw [sub_add_cancel] at h
  rw [h]
  abel

/-! ## §2. The iterated degree-one action -/

/-- Degree bookkeeping for the iterated degree-one action: `smulIterDeg N j` is the
`N`-fold application of `1 + ·` to `j`, the degree in which the `N`-fold action of a
degree-one section on a degree-`j` twisted section lands.  Kept in iterated form (rather
than `N + j`) so that the iterate `smulIter` is **cast-free**; `smulIterDeg_eq`
identifies it with `N + j`. -/
def smulIterDeg (N j : ℕ) : ℕ :=
  Nat.rec j (fun _ d => 1 + d) N

@[simp] lemma smulIterDeg_zero (j : ℕ) : smulIterDeg 0 j = j := rfl

@[simp] lemma smulIterDeg_succ (N j : ℕ) : smulIterDeg (N + 1) j = 1 + smulIterDeg N j := rfl

lemma smulIterDeg_eq (N j : ℕ) : smulIterDeg N j = N + j := by
  induction N with
  | zero => simp
  | succ N ih => rw [smulIterDeg_succ, ih]; omega

/-- **The iterated degree-one action** (`def:smulIter`): the `N`-fold iterate
`x ↦ s|_U ⋆ (s|_U ⋆ ⋯ (s|_U ⋆ x))` of the local graded action of a **global**
degree-one section `s ∈ Γ(X, L^{⊗1})` on twisted sections over `U`.  This is the
element `s^{⊗N} ⊗ x` of Serre's D2/D3 in the cast-free iterated form: each step is
the honest degree-`(1, ·)` action `twistedSMul`, and the degree ledger is
`smulIterDeg`. -/
noncomputable def smulIter (F L : X.Modules) (s : sectionDeg L 1) (U : X.Opens) :
    ∀ (N : ℕ) {j : ℕ},
      Γ(moduleTensorPow F L j, U) → Γ(moduleTensorPow F L (smulIterDeg N j), U)
  | 0, _, x => x
  | (N + 1), j, x =>
      twistedSMul F L 1 (smulIterDeg N j) U
        ((tensorPow L 1).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)
        (smulIter F L s U N x)

@[simp] lemma smulIter_zero (F L : X.Modules) (s : sectionDeg L 1) (U : X.Opens)
    {j : ℕ} (x : Γ(moduleTensorPow F L j, U)) :
    smulIter F L s U 0 x = x := rfl

lemma smulIter_succ (F L : X.Modules) (s : sectionDeg L 1) (U : X.Opens) (N : ℕ)
    {j : ℕ} (x : Γ(moduleTensorPow F L j, U)) :
    smulIter F L s U (N + 1) x
      = twistedSMul F L 1 (smulIterDeg N j) U
          ((tensorPow L 1).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)
          (smulIter F L s U N x) := rfl

/-- The iterated action is compatible with restriction. -/
lemma smulIter_res (F L : X.Modules) (s : sectionDeg L 1) {U V : X.Opens} (hVU : V ≤ U)
    (N : ℕ) {j : ℕ} (x : Γ(moduleTensorPow F L j, U)) :
    (moduleTensorPow F L (smulIterDeg N j)).presheaf.map (homOfLE hVU).op
        (smulIter F L s U N x)
      = smulIter F L s V N
          ((moduleTensorPow F L j).presheaf.map (homOfLE hVU).op x) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [smulIter_succ, smulIter_succ]
      refine (twistedSMul_res F L 1 (smulIterDeg N j) hVU _ _).trans ?_
      rw [ih, res_res (tensorPow L 1) le_top hVU le_top]

/-- The iterated action annihilates zero. -/
lemma smulIter_zero_right (F L : X.Modules) (s : sectionDeg L 1) (U : X.Opens)
    (N : ℕ) {j : ℕ} :
    smulIter F L s U N (0 : Γ(moduleTensorPow F L j, U)) = 0 := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [smulIter_succ, ih]
      exact twistedSMul_zero_right F L 1 (smulIterDeg N j) U _


/-- The iterated action is additive. -/
lemma smulIter_add (F L : X.Modules) (s : sectionDeg L 1) (U : X.Opens)
    (N : ℕ) {j : ℕ} (x y : Γ(moduleTensorPow F L j, U)) :
    smulIter F L s U N (x + y) = smulIter F L s U N x + smulIter F L s U N y := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [smulIter_succ, smulIter_succ, smulIter_succ, ih]
      exact twistedSMul_add_right F L 1 (smulIterDeg N j) U _ _ _

/-- The iterated action is subtractive. -/
lemma smulIter_sub (F L : X.Modules) (s : sectionDeg L 1) (U : X.Opens)
    (N : ℕ) {j : ℕ} (x y : Γ(moduleTensorPow F L j, U)) :
    smulIter F L s U N (x - y) = smulIter F L s U N x - smulIter F L s U N y := by
  have h := smulIter_add F L s U N (x - y) y
  rw [sub_add_cancel] at h
  rw [h]
  abel

/-- The iterated action commutes with the `Γ(X, U)`-scalar action. -/
lemma smulIter_smul (F L : X.Modules) (s : sectionDeg L 1) (U : X.Opens)
    (N : ℕ) {j : ℕ} (a : Γ(X, U)) (x : Γ(moduleTensorPow F L j, U)) :
    smulIter F L s U N (a • x)
      = a • smulIter F L s U N x := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [smulIter_succ, smulIter_succ, ih]
      exact twistedSMul_smul_right F L 1 (smulIterDeg N j) U a _ _

/-- **Vanishing propagates up the iteration ladder**: once some iterate of the
`s`-action kills a section over `U`, all higher iterates do. -/
lemma smulIter_eq_zero_mono (F L : X.Modules) (s : sectionDeg L 1) (U : X.Opens)
    {n N : ℕ} (hnN : n ≤ N) {j : ℕ} {x : Γ(moduleTensorPow F L j, U)}
    (hx : smulIter F L s U n x = 0) :
    smulIter F L s U N x = 0 := by
  induction N with
  | zero =>
      obtain rfl : n = 0 := Nat.le_zero.mp hnN
      exact hx
  | succ N ih =>
      rcases Nat.lt_or_ge n (N + 1) with h | h
      · rw [smulIter_succ, ih (Nat.lt_succ_iff.mp h)]
        exact twistedSMul_zero_right F L 1 (smulIterDeg N j) U _
      · obtain rfl : n = N + 1 := le_antisymm hnN h
        exact hx

end Scheme.Modules

end AlgebraicGeometry
