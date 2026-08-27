/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RigidPushforwardTransfer
import AlgebraicJacobian.Cohomology.PullbackQuasicoherent

/-!
# Affine-target descent for the pushforward base-change mate

The B3 campaign gate `Scheme.HasRigidPushforward` (`Picard/RigidPushforward.lean`:373) has two
fields.  `Picard/RigidPushforwardGate.lean` ("Caveat on the `baseChange` field") and
`Picard/RigidPushforwardFrontier.lean` (item 3 of "What remains") both record that the second
one, `Scheme.RigidPushforwardBaseChange` (`Picard/RigidPushforward.lean`:342), has **no
infrastructure at all**: every `IsIso` theorem for the adjoint mate `pushforwardBaseChangeMap`
in this tree (`isIso_pushforwardBaseChangeMap_of_isPullback`,
`Picard/RigidPushforwardTransfer.lean`:1108, and its chart form :949) assumes `[IsAffineHom f]`,
whereas the gate's family `q : C_A ⟶ Spec A` is proper and emphatically not affine.

This file replaces "no infrastructure" by a named, honest **reduction**: the whole field follows
from a single classical `H⁰`-base-change bijectivity of `Γ(Spec A, ⊤)`-modules.  It does not
prove that bijectivity; `Picard/RigidPushforwardGammaBaseChange.lean` does
(`Adelic.rigidPushforwardGammaBaseChange_proved`), by the route sketched below.  It does not
smuggle in the non-affine case either: only the two *bases* of the square are assumed affine,
the fibre map `f` is arbitrary.

## The reduction, in four steps

* **§1 — affine-target descent.**  `Scheme.Modules.isIso_of_isIso_moduleSpecΓFunctor_map` and
  `Scheme.Modules.isIso_of_bijective_appTop`: a morphism `φ : M ⟶ N` of quasi-coherent modules
  on an affine scheme is an isomorphism as soon as it is *bijective on global sections*.  The
  input is the affine structure theorem `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`
  (Stacks 01I8, `Picard/QuotScheme.lean`:2693) — the counit `Γ(M, ⊤)~ ⟶ M` is an isomorphism
  for quasi-coherent `M` — together with naturality of `Scheme.Modules.fromTildeΓNatTrans`.
  Naturality rewrites `φ` as `fromTildeΓ_M⁻¹ ≫ (Γφ)~ ≫ fromTildeΓ_N`, a composite of three
  isomorphisms, and the resulting `Iso` has `φ` as its `hom` by `rfl`.

* **§2 — the mate on global sections.**  `isIso_pushforwardBaseChangeMap_appTop_of_bijective`:
  over affine bases the `Γ(⊤)`-component of `pushforwardBaseChangeMap` *is* the canonical map
  `Γ(Y', ⊤) ⊗_{Γ(Y, ⊤)} Γ(f_* F, ⊤) → Γ(f'_* (g'^* F), ⊤)`, `b ⊗ x ↦ b · baseMap x`.  The
  source side is identified with the tensor product by
  `pullback_app_isoTensor_baseMap_sectionLinearEquiv` (`Picard/QuotScheme.lean`:4611) and the
  formula for the mate on the image of `baseMap` is `pushforwardBaseChangeMap_app_baseMap`
  (`Picard/RigidPushforwardTransfer.lean`:828) taken at `V = O = ⊤`; simple tensors are handled
  by `b ⊗ x = b • (1 ⊗ x)` and `Scheme.Modules.Hom.app_smul`, and `TensorProduct.induction_on`
  propagates.

  **Caveat, stated once and meant.**  §2 and §3 assume only `comm : g' ≫ f = f' ≫ g`; the square
  is *not* assumed cartesian.  They are therefore exactly as strong as the bijectivity `hbij`
  handed to them, and must **not** be read as an unconditional Beck–Chevalley/base-change
  theorem: all the mathematical content of a base-change theorem still sits inside `hbij`, and
  without a cartesian square there is no reason for `hbij` to hold at all.

* **§3 — the two combined.**  `isIso_pushforwardBaseChangeMap_of_bijective_gamma`: with `Y`
  affine and the target of `g` of the form `Spec R'`, quasi-coherence of both mate ends is
  automatic (`pullback_isQuasicoherent_hom`, `Scheme.Modules.pushforward_isQuasicoherent`), so
  §1 upgrades the `Γ(⊤)`-bijectivity of §2 to `IsIso` of the mate itself.  **`f` is still not
  assumed affine** — this is precisely the case the two frontier docstrings report as missing.

* **§4 — the gate's field.**  `Adelic.RigidPushforwardGammaBaseChange` names the residual
  `Γ`-level statement for the constant curve `C_A`, and
  `Adelic.rigidPushforwardBaseChange_of_gamma` derives `Scheme.RigidPushforwardBaseChange C A`
  from it.  Properness of `C.hom` enters only through
  `MorphismProperty.pullback_snd`, to know that the two pullback families are proper (hence qcqs)
  and that `q_* L` is quasi-coherent.

## The route the probe identified — EXECUTED, with one simplification

`RigidPushforwardGammaBaseChange C A` is not proved *here*; it is proved in
`Picard/RigidPushforwardGammaBaseChange.lean`.  The route below is what that file follows, with
one departure worth reading before trusting the corrections in the next section: steps 1–2 were
taken in the *opposite* order to correction 1's advice, and correction 4 turned out to be
unnecessary (see the note at the end of this section).  The route as found:

1. Work on the 2-affine cover `(p1BaseChangeCoverSquare A).preimage π_A` of `C_A`, the preimage
   under the finite (hence affine) `π_A := finiteMapToP1BaseChange A C` of the standard 2-chart
   cover of `ℙ¹_A`.  Its Čech differential is **definitionally** the `ℙ¹_A` differential of
   `(π_A)_* L`: `Scheme.AffineCoverMVSquare.moduleSectionDiff_pushforward`
   (`Picard/RigidPushforwardTransfer.lean`:577) is proved by `rfl`.  So surjectivity of `d`
   obtained on `ℙ¹_A` transports to `C_A` by `exact`, with no transport lemma at all.

2. Feed that surjectivity to `bijective_kerBaseChange_of_surjective`
   (`Picard/TwoTermFiniteFree.lean`:392) to get bijectivity of the kernel base-change map, and
   convert kernels to global sections on *both* sides with
   `Scheme.AffineCoverMVSquare.globalSectionsEquivKerModuleSectionDiffBase`
   (`Picard/RigidPushforwardP1Engine.lean`:287).

3. **This step is now DONE** — see `Picard/RigidPushforwardChartBaseChange.lean`, which proves
   the **Čech square for an arbitrary affine base change**, i.e. the generalisation of
   `Picard/RigidPushforwardFiberChart.lean` §5–§7 from the fibre embedding `Spec κ(t) ⟶ Spec A`
   to an arbitrary `Spec A' ⟶ Spec A`:

   * `isPushout_appLE_chartBaseChange` — the general-square replacement for
     `isPushout_appLE_fiberChart` (a one-liner from `isPushout_appLE_of_isPullback'`);
   * `exists_chartTensorEquiv` (↝ `exists_fiberChartTensorEquiv`) and
     `chart_smul_baseMap_res` (↝ `fiberChart_smul_baseMap_res`);
   * `exists_kerChartTensorEquiv` — the two-chart Čech square concluded on **kernels**,
     `Γ(Y',⊤) ⊗_{Γ(Y,⊤)} ker d ≃+ ker d'`, taking the `hker` of correction 1 directly and
     therefore carrying **no** flatness hypothesis.

   All four are sorry-free and axiom-clean, and none of them needed the heartbeat headroom the
   fibre originals carry.  What is left of this route is therefore assembly: instantiate the
   engine's fourth conjunct at `B := Γ(Spec A', ⊤)`, feed `exists_kerChartTensorEquiv`, and
   convert kernels to global sections on both sides — with correction 4 below the remaining
   piece of real Lean engineering.  For the record, the intended signatures were:

   ```
   theorem exists_chartTensorEquiv {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
       (h : IsPullback g' f' f g) [IsAffine Y] [IsAffine Y']
       (M : X.Modules) [M.IsQuasicoherent] {W : X.Opens} (hW : IsAffineOpen W)
       (hW' : IsAffineOpen (g' ⁻¹ᵁ W)) :
       letI : Algebra Γ(Y, ⊤) Γ(Y', ⊤) := (g.appLE ⊤ ⊤ le_top).hom.toAlgebra
       letI := f.baseSectionsModule M W
       Nonempty { Θ : TensorProduct Γ(Y, ⊤) Γ(Y', ⊤) Γ(M, W) ≃+
           Γ((Scheme.Modules.pullback g').obj M, g' ⁻¹ᵁ W) //
         ∀ (b : Γ(Y', ⊤)) (x : Γ(M, W)),
           Θ (b ⊗ₜ[Γ(Y, ⊤)] x) =
             (f'.appLE (⊤ : Y'.Opens) (g' ⁻¹ᵁ W) le_top).hom b •
               pullback_app_isoTensor_baseMap g' M (le_refl (g' ⁻¹ᵁ W)) x }

   lemma chart_smul_baseMap_res {f' : X' ⟶ Y'} {g' : X' ⟶ X} (M : X.Modules)
       {W W₀ : X.Opens} {W'' : X'.Opens}
       (hWW₀ : W₀ ≤ W) (hW'' : W'' ≤ g' ⁻¹ᵁ W₀) (hle : W'' ≤ g' ⁻¹ᵁ W)
       (b : Γ(Y', ⊤)) (x : Γ(M, W)) :
       (((((Scheme.Modules.pullback g').obj M).presheaf.map (homOfLE hle).op).hom
           ((f'.appLE (⊤ : Y'.Opens) (g' ⁻¹ᵁ W) le_top).hom b •
             pullback_app_isoTensor_baseMap g' M (le_refl (g' ⁻¹ᵁ W)) x)) :
           Γ((Scheme.Modules.pullback g').obj M, W'')) =
         (f'.appLE (⊤ : Y'.Opens) W'' le_top).hom b •
           pullback_app_isoTensor_baseMap g' M hW''
             ((M.presheaf.map (homOfLE hWW₀).op).hom x)
   ```

   Both are the affine-base-change analogues of bricks already proved for fibres; the first is
   Stacks 02KG in degree `0` on a single affine chart, the second its restriction naturality.

3b. **What actually happened (read this before corrections 1 and 4).**  The executed proof took
   step 1's surjectivity and step 2's `bijective_kerBaseChange_of_surjective` after all, rather
   than the engine's fourth conjunct — because the flatness that correction 1 calls an
   unnecessary obligation is *free* on the campaign (`CoherentSheafFlat q L` for an invertible
   `L` on the flat family `q`, read at the pair `(⊤, U₁ ⊓ U₂)` by
   `flat_baseSections_of_coherentSheafFlat`), and taking it avoids moving the whole `letI`
   dictionary off `p` and the pushforward module.  With that choice, correction 4's congruence
   helper is **not needed at all**: `Function.Surjective ⇑d` mentions only the underlying
   function of `d`, the module structures are instance arguments, and
   `moduleSectionDiff_pushforward` is `rfl` — so the ℙ¹ statement and the `C_A` statement are
   literally the same proposition and `exact` crosses `q = π_A ≫ p` for free.  Correction 3's
   two-scalar-action glue is real, but is confined to one `map_smul` through
   `pushforwardTopEquivBaseSections`.

4. **Dependency warning.**  This route puts the `baseChange` field *downstream* of the
   `IsIntegral (ℙ¹_k)` leaf of `Picard/RigidPushforwardFrontier.lean`: step 1 consumes the
   engine's **global** surjectivity of the Čech differential `d`, not merely the fibrewise
   `h¹ = 0` hypothesis that the gate carries.  Global surjectivity comes out of
   `p1Cech_h0_baseChange_of_fibrewise_h1_vanishing`, whose `H⁰`-finiteness anchor is exactly
   that leaf.  So the two fields of the gate are not independent along this route.  (That leaf
   is now proved — `Adelic.instIsIntegralP1OverLeft`, `Picard/RigidPushforwardInstance.lean` —
   so the dependency is discharged, not blocking.)

## Four corrections to that route, from an adversarial re-check

The route above survived an independent verification of §1–§4, but four of its *unproved*
steps were found to be booked at less than they cost.  Recorded so the next session does not
rediscover them:

1. **Take the engine's fourth conjunct directly; do not re-derive it.**  Step 1 above proposes
   feeding global surjectivity of `d` to `bijective_kerBaseChange_of_surjective`
   (`Picard/TwoTermFiniteFree.lean`:392), which then also demands
   `Module.Flat Γ(Spec A, ⊤) Γ(M, U₁ ⊓ U₂)`.  That is unnecessary: the fourth conjunct of
   `p1Cech_h0_baseChange_of_fibrewise_h1_vanishing_of_isIntegral`
   (`Picard/RigidPushforwardP1Constants.lean`:540-544) is already
   `∀ B, Function.Bijective (TwoTerm.kerBaseChange (…) B)` for *every*
   `Γ(Spec A, ⊤)`-algebra `B`; instantiate `B := Γ(Spec A', ⊤)`.  This deletes the flatness
   obligation entirely, so the intended `Γ`-level statement should take
   `hker : ∀ B …, Function.Bijective (kerBaseChange (𝒰.moduleSectionDiffBase f M) B)` rather
   than a flatness-plus-surjectivity pair.

2. **Get the `letI` binder list right, and elaborate the statement before writing any proof.**
   A `Module Γ(Y, ⊤) Γ(M, ·)` instance exists only through `letI := f.baseSectionsModule M ·`,
   so every hypothesis mentioning `Γ(M, ·)` as a `Γ(Y, ⊤)`-module needs one — *in addition to*
   the `Algebra Γ(Y, ⊤) Γ(Y', ⊤)` binder, which is never replaced.  How many depends on the
   statement, so copy from the closest existing one rather than guessing:
   `surjective_moduleSectionDiffBase_baseChange_residueField`
   (`Picard/RigidPushforwardFiberChart.lean`:508-518) is about the whole Čech complex and
   carries the `Algebra` binder plus **three** `baseSectionsModule` binders (`U₁`, `U₂`,
   `U₁ ⊓ U₂` — there is no `⊤` binder); a statement about a *single* chart needs the `Algebra`
   binder plus **one**, at that chart; and the kernel comparison
   `exists_kerChartTensorEquiv` (`Picard/RigidPushforwardChartBaseChange.lean`) needs **seven**
   — the `Algebra` binder, three on `X`, three on `X'`.  (An earlier draft of this paragraph
   said "four binders, not the `Algebra` binder", which describes none of them; corrected after
   a fresh-context review checked it against the source, and the counts above are measured.)
   Two traps found while writing the seven-binder version: instance search does **not** see
   `g' ⁻¹ᵁ 𝒰.U₁` as `(𝒰.preimage g').U₁`, so the target-side binders must be spelled with
   `(𝒰.preimage g').Uᵢ`; and after `TensorProduct.induction_on` a goal that is syntactically
   `X = X` may still need an explicit `rfl`, because the two sides carry different-but-defeq
   module instances from the `letI` dictionary.  Either way: write the statement with a
   placeholder body and get it to elaborate first — that is where the time goes.

3. **The glue to §3 is not free.**  §3's map lives on the tensor product formed with the
   *native* pushforward module structure (that is what
   `pullback_app_isoTensor_baseMap_sectionLinearEquiv` returns), while the Čech statement
   delivers the `baseSectionsModule` structure.  The tree proves these are only
   propositionally equal: `Scheme.Modules.pushforwardTopEquivBaseSections`
   (`Picard/RigidPushforwardP1Sheaf.lean`:408-421) is the identity on carriers but proves
   `map_smul'` via `Scheme.Hom.appLE_eq_app`.  So the two must be joined by a
   `TensorProduct` transport along that equivalence plus one `appLE_eq_app` rewrite for the
   target-side scalar.

4. **Moving surjectivity from `π_A ≫ p` to `q` needs a lemma.**  The preimage-cover
   observation lands the Čech differential at the family `π_A ≫ p`, and `q` equals it only
   propositionally (`Adelic.finiteMapToP1BaseChange_snd`, `Picard/RigidPushforward.lean`:595,
   proved by `(pullback.lift_snd _ _ _).trans (Category.comp_id _)`).  Since the module
   structures sit inside the *type* of `moduleSectionDiffBase`, a naive `rw` on the morphism
   equality risks a "motive is not type correct" failure; a `subst`-style congruence helper is
   needed.  "Transports by `exact`" is true only within a fixed family.

## Vacuity audit

`RigidPushforwardGammaBaseChange` is of the shape `∃ s, (value of s on simple tensors) ∧
Function.Bijective s`.  This cannot be discharged by choosing a convenient `s`: simple tensors
generate `Γ(Spec A', ⊤) ⊗_{Γ(Spec A, ⊤)} Γ(q_* L, ⊤)` as an abelian group, and `s` is required
to be additive, so the prescribed values on simple tensors determine `s` **uniquely**.  The
existential is therefore a genuine bijectivity assertion about the canonical base-change map,
not an unconstrained choice.

Sources: Stacks 01I8 (quasi-coherent modules on an affine scheme), Stacks 02KG (cohomology and
base change), Mumford, *Abelian Varieties*, II §5; EGA III 7.9.9; Hartshorne III 12.11.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

open Scheme Scheme.Modules

/-! ## §1. Affine-target descent -/

-- The `calc` step identifying `e.hom` with a composite is `rfl` only below reducible
-- transparency, since `Iso.trans`/`asIso`/`Functor.mapIso` must all unfold.
set_option backward.isDefEq.respectTransparency false in
/-- **A morphism of quasi-coherent modules on `Spec R` is an isomorphism as soon as its
image under the global-sections functor is.** -/
theorem Scheme.Modules.isIso_of_isIso_moduleSpecΓFunctor_map {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    (h : IsIso ((moduleSpecΓFunctor (R := R)).map φ)) : IsIso φ := by
  have hM : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  have hN : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  have key : M.fromTildeΓ ≫ φ =
      (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map φ) ≫ N.fromTildeΓ :=
    ((Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality φ).symm
  let iM := @asIso _ _ _ _ M.fromTildeΓ hM
  let iN := @asIso _ _ _ _ N.fromTildeΓ hN
  let iG := @asIso _ _ _ _ ((moduleSpecΓFunctor (R := R)).map φ) h
  let e : M ≅ N := iM.symm ≪≫ (tilde.functor R).mapIso iG ≪≫ iN
  have he : e.hom = φ :=
    calc e.hom
        = iM.inv ≫ ((tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map φ)
            ≫ N.fromTildeΓ) := rfl
      _ = iM.inv ≫ (M.fromTildeΓ ≫ φ) := by rw [key]
      _ = φ := Iso.inv_hom_id_assoc iM φ
  rw [← he]
  exact e.isIso_hom

-- The `rfl` bridging `(moduleSpecΓFunctor).map φ` with `φ.app ⊤` needs the functor's `map`
-- field unfolded, which is not reducible.
set_option backward.isDefEq.respectTransparency false in
/-- Affine-target descent, section form: a morphism of quasi-coherent modules on `Spec R`
which is **bijective on global sections** is an isomorphism. -/
theorem Scheme.Modules.isIso_of_bijective_appTop {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    (h : Function.Bijective (Scheme.Modules.Hom.app φ (⊤ : (Spec R).Opens))) : IsIso φ := by
  refine Scheme.Modules.isIso_of_isIso_moduleSpecΓFunctor_map φ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  have hfun : ⇑(ConcreteCategory.hom ((moduleSpecΓFunctor (R := R)).map φ)) =
      ⇑(ConcreteCategory.hom (Scheme.Modules.Hom.app φ (⊤ : (Spec R).Opens))) := rfl
  rw [hfun]
  exact h

/-! ## §2. The mate on global sections over affine bases -/

section MateAppTop

variable {Y Y' X X' : Scheme.{u}}

-- The tensor induction rewrites whole `Scheme.Modules` section types at each step.
set_option maxHeartbeats 1600000 in
-- `pushforwardBaseChangeMap_app_baseMap` matches the goal only after the `appLE`-algebra
-- structure and the `Hom.app` coercion are unfolded past reducible transparency.
set_option backward.isDefEq.respectTransparency false in
/-- **The base-change mate is an isomorphism on global sections over affine bases as
soon as the canonical `Γ`-level base-change map is bijective.**  No cartesian hypothesis,
no affineness of `f`.

The hypotheses say that `s` is *the* canonical map
`Γ(Y', ⊤) ⊗_{Γ(Y, ⊤)} Γ(f_* F, ⊤) → Γ(f'_* (g'^* F), ⊤)`, `b ⊗ x ↦ b · baseMap x`, and that it
is bijective; the conclusion is that the `Γ(⊤)`-component of the mate is an isomorphism.

**This is not a Beck–Chevalley statement.**  The square is only assumed to commute, so the
theorem is exactly as strong as the bijectivity `hbij` supplied to it: all the content of a
base-change theorem still sits in `hbij`, which without a cartesian square has no reason to
hold. -/
theorem isIso_pushforwardBaseChangeMap_appTop_of_bijective
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (comm : g' ≫ f = f' ≫ g) [IsAffine Y] [IsAffine Y']
    (F : X.Modules) [((Scheme.Modules.pushforward f).obj F).IsQuasicoherent]
    (e' : f' ⁻¹ᵁ (⊤ : Y'.Opens) ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ (⊤ : Y.Opens)))
    (s : letI : Algebra Γ(Y, ⊤) Γ(Y', ⊤) :=
            (g.appLE (⊤ : Y.Opens) (⊤ : Y'.Opens) le_top).hom.toAlgebra
         TensorProduct Γ(Y, ⊤) Γ(Y', ⊤)
             Γ((Scheme.Modules.pushforward f).obj F, (⊤ : Y.Opens)) →+
           Γ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F),
             (⊤ : Y'.Opens)))
    (hs : letI : Algebra Γ(Y, ⊤) Γ(Y', ⊤) :=
            (g.appLE (⊤ : Y.Opens) (⊤ : Y'.Opens) le_top).hom.toAlgebra
          ∀ (b : Γ(Y', ⊤)) (x : Γ((Scheme.Modules.pushforward f).obj F, (⊤ : Y.Opens))),
            s (b ⊗ₜ[Γ(Y, ⊤)] x) =
              b • (show Γ((Scheme.Modules.pushforward f').obj
                  ((Scheme.Modules.pullback g').obj F), (⊤ : Y'.Opens)) from
                pullback_app_isoTensor_baseMap g' F e' x))
    (hbij : Function.Bijective s) :
    IsIso (Scheme.Modules.Hom.app
      (pushforwardBaseChangeMap f g f' g' comm F) (⊤ : Y'.Opens)) := by
  letI : Algebra Γ(Y, ⊤) Γ(Y', ⊤) :=
    (g.appLE (⊤ : Y.Opens) (⊤ : Y'.Opens) le_top).hom.toAlgebra
  obtain ⟨⟨eL, heL⟩⟩ := pullback_app_isoTensor_baseMap_sectionLinearEquiv g
    ((Scheme.Modules.pushforward f).obj F) (isAffineOpen_top Y') (isAffineOpen_top Y)
    (le_top : (⊤ : Y'.Opens) ≤ g ⁻¹ᵁ (⊤ : Y.Opens))
  have hcomm : ∀ w : TensorProduct Γ(Y, ⊤) Γ(Y', ⊤)
      Γ((Scheme.Modules.pushforward f).obj F, (⊤ : Y.Opens)),
      (Scheme.Modules.Hom.app (pushforwardBaseChangeMap f g f' g' comm F)
        (⊤ : Y'.Opens)).hom (eL w) = s w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul b x =>
      have hb : (b ⊗ₜ[Γ(Y, ⊤)] x :
          TensorProduct Γ(Y, ⊤) Γ(Y', ⊤)
            Γ((Scheme.Modules.pushforward f).obj F, (⊤ : Y.Opens))) =
          b • ((1 : Γ(Y', ⊤)) ⊗ₜ[Γ(Y, ⊤)] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hsm : eL (b ⊗ₜ[Γ(Y, ⊤)] x) =
          b • pullback_app_isoTensor_baseMap g ((Scheme.Modules.pushforward f).obj F)
            (le_top : (⊤ : Y'.Opens) ≤ g ⁻¹ᵁ (⊤ : Y.Opens)) x := by
        rw [hb, _root_.map_smul, heL]
      rw [hsm]
      have hlin : (Scheme.Modules.Hom.app (pushforwardBaseChangeMap f g f' g' comm F)
            (⊤ : Y'.Opens)).hom
            (b • pullback_app_isoTensor_baseMap g ((Scheme.Modules.pushforward f).obj F)
              (le_top : (⊤ : Y'.Opens) ≤ g ⁻¹ᵁ (⊤ : Y.Opens)) x) =
          b • (Scheme.Modules.Hom.app (pushforwardBaseChangeMap f g f' g' comm F)
            (⊤ : Y'.Opens)).hom
            (pullback_app_isoTensor_baseMap g ((Scheme.Modules.pushforward f).obj F)
              (le_top : (⊤ : Y'.Opens) ≤ g ⁻¹ᵁ (⊤ : Y.Opens)) x) :=
        Scheme.Modules.Hom.app_smul _ b _
      rw [hlin, pushforwardBaseChangeMap_app_baseMap f g f' g' comm F
        (le_top : (⊤ : Y'.Opens) ≤ g ⁻¹ᵁ (⊤ : Y.Opens)) e' x]
      exact (hs b x).symm
  rw [ConcreteCategory.isIso_iff_bijective]
  have hfun : ⇑(ConcreteCategory.hom (Scheme.Modules.Hom.app
      (pushforwardBaseChangeMap f g f' g' comm F) (⊤ : Y'.Opens))) =
      ⇑s ∘ ⇑eL.symm := by
    funext z
    obtain ⟨w, rfl⟩ := eL.surjective z
    have hz : eL.symm (eL w) = w := eL.symm_apply_apply w
    simp only [Function.comp_apply, hz]
    exact hcomm w
  rw [hfun]
  exact hbij.comp (EquivLike.bijective eL.symm)

end MateAppTop

/-! ## §3. The combined descent -/

section Combined

variable {Y X X' : Scheme.{u}} {R' : CommRingCat.{u}}

-- Discharging the three quasi-coherence side goals elaborates the mate's ends in full.
set_option maxHeartbeats 1600000 in
-- The `Γ(⊤)`-level statement of §2 has to be recognised as the `app ⊤` of the mate up to
-- non-reducible unfolding of the `Modules` hom structure.
set_option backward.isDefEq.respectTransparency false in
/-- **Affine-target descent for the mate.**  If the target of `g` is `Spec R'`, the source
`Y` is affine, `f'` is qcqs and `F` is quasi-coherent with quasi-coherent pushforward, then
the base-change mate is an isomorphism as soon as the canonical `Γ`-level base-change map is
bijective.  **`f` is not assumed affine.**

As in §2 the square is only assumed to commute, so the statement is exactly as strong as
`hbij`; it is not an unconditional base-change theorem. -/
theorem isIso_pushforwardBaseChangeMap_of_bijective_gamma
    (f : X ⟶ Y) (g : Spec R' ⟶ Y) (f' : X' ⟶ Spec R') (g' : X' ⟶ X)
    (comm : g' ≫ f = f' ≫ g) [IsAffine Y]
    [QuasiCompact f'] [QuasiSeparated f']
    (F : X.Modules) [F.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj F).IsQuasicoherent]
    (e' : f' ⁻¹ᵁ (⊤ : (Spec R').Opens) ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ (⊤ : Y.Opens)))
    (s : letI : Algebra Γ(Y, ⊤) Γ(Spec R', ⊤) :=
            (g.appLE (⊤ : Y.Opens) (⊤ : (Spec R').Opens) le_top).hom.toAlgebra
         TensorProduct Γ(Y, ⊤) Γ(Spec R', ⊤)
             Γ((Scheme.Modules.pushforward f).obj F, (⊤ : Y.Opens)) →+
           Γ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F),
             (⊤ : (Spec R').Opens)))
    (hs : letI : Algebra Γ(Y, ⊤) Γ(Spec R', ⊤) :=
            (g.appLE (⊤ : Y.Opens) (⊤ : (Spec R').Opens) le_top).hom.toAlgebra
          ∀ (b : Γ(Spec R', ⊤)) (x : Γ((Scheme.Modules.pushforward f).obj F, (⊤ : Y.Opens))),
            s (b ⊗ₜ[Γ(Y, ⊤)] x) =
              b • (show Γ((Scheme.Modules.pushforward f').obj
                  ((Scheme.Modules.pullback g').obj F), (⊤ : (Spec R').Opens)) from
                pullback_app_isoTensor_baseMap g' F e' x))
    (hbij : Function.Bijective s) :
    IsIso (pushforwardBaseChangeMap f g f' g' comm F) := by
  haveI : ((Scheme.Modules.pullback g).obj
      ((Scheme.Modules.pushforward f).obj F)).IsQuasicoherent :=
    pullback_isQuasicoherent_hom g ((Scheme.Modules.pushforward f).obj F) inferInstance
  haveI : ((Scheme.Modules.pullback g').obj F).IsQuasicoherent :=
    pullback_isQuasicoherent_hom g' F inferInstance
  haveI : ((Scheme.Modules.pushforward f').obj
      ((Scheme.Modules.pullback g').obj F)).IsQuasicoherent :=
    Scheme.Modules.pushforward_isQuasicoherent f' ((Scheme.Modules.pullback g').obj F)
  refine Scheme.Modules.isIso_of_bijective_appTop _ ?_
  have hmt := isIso_pushforwardBaseChangeMap_appTop_of_bijective f g f' g' comm F e' s hs hbij
  rw [ConcreteCategory.isIso_iff_bijective] at hmt
  exact hmt

end Combined

/-! ## §4. The gate's `baseChange` field, reduced to a `Γ`-level statement -/

namespace Adelic

variable {k : Type u} [Field k]

/-- **The `Γ`-level base-change leaf.**  For the constant curve `C_A`, an invertible `L`
with fibrewise `h¹ = 0`, and every ring map `φ : A → A'`, the canonical additive map
`Γ(Spec A', ⊤) ⊗_{Γ(Spec A, ⊤)} Γ(C_A, L) → Γ(C_{A'}, (g')^* L)`,
`b ⊗ x ↦ b · (base-map image of x)`, is bijective.  This is the module-level residue of
`Scheme.RigidPushforwardBaseChange` after affine-target descent.

The existential over `s` is not a loophole: `s` is additive and its values are prescribed on
simple tensors, which generate the tensor product as an abelian group, so `s` is determined
uniquely and the statement really asserts bijectivity of the canonical map. -/
def RigidPushforwardGammaBaseChange (C : Over (Spec (CommRingCat.of k)))
    (A : Type u) [CommRing A] [Algebra k A] : Prop :=
  ∀ (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules),
    LineBundle.IsLocallyTrivial L →
    (∀ t : Spec (CommRingCat.of A),
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing L t) →
    ∀ (A' : Type u) [CommRing A'] (φ : A →+* A')
      (e' : (pullback.snd (pullback.snd C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A))))
          (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A')).Opens) ≤
        (pullback.fst (pullback.snd C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A))))
          (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ
          ((pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) ⁻¹ᵁ
            (⊤ : (Spec (CommRingCat.of A)).Opens))),
      letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of A'), ⊤) :=
        ((Spec.map (CommRingCat.ofHom φ)).appLE
          (⊤ : (Spec (CommRingCat.of A)).Opens)
          (⊤ : (Spec (CommRingCat.of A')).Opens) le_top).hom.toAlgebra
      ∃ s : TensorProduct Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of A'), ⊤)
          Γ((Scheme.Modules.pushforward (pullback.snd C.hom
              (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj L,
            (⊤ : (Spec (CommRingCat.of A)).Opens)) →+
        Γ((Scheme.Modules.pushforward (pullback.snd (pullback.snd C.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A))))
            (Spec.map (CommRingCat.ofHom φ)))).obj
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd C.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A))))
            (Spec.map (CommRingCat.ofHom φ)))).obj L),
          (⊤ : (Spec (CommRingCat.of A')).Opens)),
        (∀ b x, s (b ⊗ₜ[Γ(Spec (CommRingCat.of A), ⊤)] x) =
          b • (show Γ((Scheme.Modules.pushforward (pullback.snd (pullback.snd C.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap k A))))
                  (Spec.map (CommRingCat.ofHom φ)))).obj
                ((Scheme.Modules.pullback (pullback.fst (pullback.snd C.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap k A))))
                  (Spec.map (CommRingCat.ofHom φ)))).obj L),
                (⊤ : (Spec (CommRingCat.of A')).Opens)) from
            pullback_app_isoTensor_baseMap
              (pullback.fst (pullback.snd C.hom
                (Spec.map (CommRingCat.ofHom (algebraMap k A))))
                (Spec.map (CommRingCat.ofHom φ))) L e' x)) ∧
        Function.Bijective s

-- Unfolding `RigidPushforwardBaseChange` exposes two nested pullback squares of schemes.
set_option maxHeartbeats 1600000 in
-- The `Γ`-level data supplied by `hgamma` is stated for the tautological square and must be
-- matched with the mate's arguments below reducible transparency.
set_option backward.isDefEq.respectTransparency false in
/-- **The gate's `baseChange` field from the `Γ`-level leaf.**  For a proper `C`, the second
field of `Scheme.HasRigidPushforward` follows from the single `Γ`-level bijectivity
`RigidPushforwardGammaBaseChange C A`, by affine-target descent (§1–§3). -/
theorem rigidPushforwardBaseChange_of_gamma
    (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    (A : Type u) [CommRing A] [Algebra k A]
    (hgamma : RigidPushforwardGammaBaseChange C A) :
    Scheme.RigidPushforwardBaseChange C A := by
  intro L hL h1 A' _ φ
  haveI : IsProper (pullback.snd C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  haveI : IsProper (pullback.snd (pullback.snd C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A))))
      (Spec.map (CommRingCat.ofHom φ))) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  haveI := hL.isFinitePresentation
  haveI : L.IsQuasicoherent := inferInstance
  haveI : ((Scheme.Modules.pushforward (pullback.snd C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj L).IsQuasicoherent :=
    Scheme.Modules.pushforward_isQuasicoherent _ L
  have e' : (pullback.snd (pullback.snd C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A))))
      (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A')).Opens) ≤
      (pullback.fst (pullback.snd C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A))))
        (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ
        ((pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) ⁻¹ᵁ
          (⊤ : (Spec (CommRingCat.of A)).Opens)) := by simp
  obtain ⟨s, hs, hbij⟩ := hgamma L hL h1 A' φ e'
  exact isIso_pushforwardBaseChangeMap_of_bijective_gamma _ _ _ _ pullback.condition L e' s hs hbij

end Adelic

end AlgebraicGeometry
