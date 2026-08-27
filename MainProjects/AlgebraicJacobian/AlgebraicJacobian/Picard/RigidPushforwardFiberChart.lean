/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.RigidPushforwardTransfer
import AlgebraicJacobian.Picard.RigidPushforwardP1Engine

/-!
# B3 — the fibre chart comparison: `hfib` from fibrewise `h¹`-vanishing

The frozen wave-4 ℙ¹ engine
`AlgebraicGeometry.Adelic.p1Cech_h0_baseChange_of_fibrewise_h1_vanishing`
(`Picard/RigidPushforwardP1Engine.lean` §5) consumes a hypothesis `hfib`
phrased *algebraically*: for every maximal ideal `𝔪` of the base ring
`R₀ = Γ(Spec A, ⊤)` the base-changed Čech difference map
`d ⊗_{R₀} (R₀ ⧸ 𝔪)` is surjective, where `d` is the two-term Čech complex
of the standard 2-chart cover `𝒰 = p1BaseChangeCoverSquare A` of `ℙ¹_A`.

The *geometric* input available on the campaign is instead the fibrewise
Čech `h¹`-vanishing `Scheme.Hom.FiberH1Vanishing` on the scheme-theoretic
fibres `ℙ¹_t = p⁻¹(t)`.  Bridging the two is the classical "cohomology and
base change" chart computation (Mumford, *Abelian Varieties* II §5; EGA III
7.7; Stacks 02KG at `i = 0`): the section ring square of the cartesian
fibre square is a **pushout**, so the Čech complex of the fibre cover is the
scalar extension of the Čech complex of `𝒰` along `R₀ → κ(t)`.

This file builds that bridge in the following layers.

* **§1 (Brick 1).**  `isPushout_appLE_of_isPullback'` — the section-ring
  pushout of a cartesian square on *arbitrary* compatible affine opens.
  The pre-existing `isPushout_appLE_of_isPullback`
  (`Picard/RigidPushforwardTransfer.lean`) is pinned to the open `f ⁻¹ᵁ V`,
  which for the projection `p : ℙ¹_A ⟶ Spec A` and `V = ⊤` is all of `ℙ¹_A`
  and hence *not affine*; the generalisation below takes any affine
  `U ≤ f ⁻¹ᵁ V`, which is what the chart-by-chart computation needs.

* **§2 (Brick 2).**  `Scheme.Hom.isPullback_fiberι` — the fibre square
  `X_t → X`, `X_t → Spec κ(t)`, `f`, `fromSpecResidueField t` is cartesian
  (it *is* the defining pullback of `Scheme.Hom.fiber`).

* **§3 (Brick 3).**  `isPushout_appLE_fiberChart` — combining §1 and §2 at
  `V = O = ⊤`: for an affine open `W ⊆ X` of the total space of a family
  `f : X ⟶ Y` over an affine base,
  `Γ(X_t, W_t) = Γ(X, W) ⊗_{Γ(Y, ⊤)} Γ(Spec κ(t), ⊤)`.

* **§4.**  `pullback_app_isoTensor_baseMap_res'` — a public re-derivation of
  the `private` QuotScheme lemma saying that the canonical base map commutes
  with restriction.

* **§5 (Brick 4).**  `exists_fiberChartTensorEquiv` — the chart fibre
  comparison `Θ_W : Γ(Spec κ(t), ⊤) ⊗_{Γ(Y, ⊤)} Γ(M, W) ≃+ Γ(M_t, W_t)`,
  assembled from the affine section formula of `Picard/QuotScheme.lean` and
  the associativity bridge of `Picard/SectionBaseChange.lean` along the §3
  pushout.

* **§6 (Brick 5).**  `fiberChart_smul_baseMap_res` — the comparisons `Θ_W`
  are natural in `W`, so they form a map of Čech complexes.

* **§7 (Brick 6).**  `exists_fiberCechLinearEquiv` exports the chart
  comparison as an isomorphism of two-term complexes.  Its first consumer,
  `Scheme.AffineCoverMVSquare.surjective_moduleSectionDiffBase_baseChange_residueField`,
  transports fibrewise Čech `h¹`-vanishing to surjectivity of the `κ(t)`-base
  change of the Čech difference map.

* **§8 (Brick 8).**  `surjective_baseChange_of_algEquiv` — base-changed
  surjectivity only depends on the isomorphism class of the scalar algebra.

* **§9 (Brick 7).**  `exists_point_appLE_fromSpecResidueField_of_isMaximal` —
  every maximal ideal of `Γ(Spec R, ⊤)` is the kernel of a (surjective)
  residue-field evaluation, so `Γ(Spec R, ⊤) ⧸ 𝔪 ≅ Γ(Spec κ(t), ⊤)`.

* **§10.**  `Adelic.p1_hfib_of_fiberH1Vanishing` — the consumer form: the
  hypothesis `_hfib` of the wave-4 ℙ¹ engine, verbatim, deduced from
  fibrewise `h¹`-vanishing on the fibres of `ℙ¹_A ⟶ Spec A`.

Source: Stacks 02KG / 01HQ; Mumford, *Abelian Varieties* II §5;
EGA III 7.7.5.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

/-! ## §1 (Brick 1). The section-ring pushout on arbitrary affine opens -/

section SectionRingPushoutGeneral

variable {Y Y' X X' : Scheme.{u}}

/-- **The section-ring square of a cartesian square is a pushout, on
arbitrary compatible affine opens.**

For a cartesian square

```
  X' --g'--> X
  |f'        |f
  v          v
  Y' --g---> Y
```

affine opens `V ⊆ Y`, `O ⊆ Y'`, `U ⊆ X` with `O ≤ g ⁻¹ᵁ V`, `U ≤ f ⁻¹ᵁ V`,
and `U' = g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ O`, the induced square of section rings

```
  Γ(Y, V) ----> Γ(X, U)
     |             |
     v             v
  Γ(Y', O) ---> Γ(X', U')
```

is a pushout in `CommRingCat`, i.e. `Γ(X', U') = Γ(X, U) ⊗_{Γ(Y, V)} Γ(Y', O)`
(Stacks 01HQ / EGA I 3.2.5 in the affine-chart form).  Affineness of `U'` is
*not* a hypothesis: the restricted square `U' → U`, `U' → O`, `U → V`,
`O → V` is cartesian (`Scheme.Hom.isPullback_resLE`), so `U'` is a fibre
product of affine schemes and hence affine, and Mathlib's
`isPushout_appTop_of_isPullback` applies; the resulting pushout of `appTop`s
is transported to the `appLE` maps along the four `Scheme.Opens.topIso`s
(`Scheme.Hom.resLE_app_top`).

This is the `U ≤ f ⁻¹ᵁ V` generalisation of
`AlgebraicGeometry.isPushout_appLE_of_isPullback`
(`Picard/RigidPushforwardTransfer.lean`), which is pinned to `U = f ⁻¹ᵁ V`.
The generalisation is what the ℙ¹ fibre-chart computation needs: there
`f = p : ℙ¹_A ⟶ Spec A`, `V = ⊤`, and `f ⁻¹ᵁ V = ℙ¹_A` is not affine, while
the individual charts of the standard 2-chart cover are. -/
theorem isPushout_appLE_of_isPullback'
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g)
    {V : Y.Opens} {O : Y'.Opens} {U : X.Opens} {U' : X'.Opens}
    (eO : O ≤ g ⁻¹ᵁ V) (eU : U ≤ f ⁻¹ᵁ V)
    (hU'eq : U' = g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ O)
    (hV : IsAffineOpen V) (hO : IsAffineOpen O) (hU : IsAffineOpen U) :
    CategoryTheory.IsPushout (f.appLE V U eU) (g.appLE V O eO)
      (g'.appLE U U' (hU'eq.le.trans inf_le_left))
      (f'.appLE O U' (hU'eq.le.trans inf_le_right)) := by
  have hpb := Scheme.Hom.isPullback_resLE h (US := V) (UT := O) (UX := U) eO eU hU'eq
  haveI : IsAffine V.toScheme := hV
  haveI : IsAffine O.toScheme := hO
  haveI : IsAffine U.toScheme := hU
  have hpush := isPushout_appTop_of_isPullback hpb
  have key : ∀ {A B : Scheme.{u}} (φ : A ⟶ B) (W₀ : B.Opens) (W : A.Opens)
      (ew : W ≤ φ ⁻¹ᵁ W₀),
      (φ.resLE W₀ W ew).appTop ≫ W.topIso.hom = W₀.topIso.hom ≫ φ.appLE W₀ W ew := by
    intro A B φ W₀ W ew
    rw [show (φ.resLE W₀ W ew).appTop = (φ.resLE W₀ W ew).app ⊤ from rfl,
      Scheme.Hom.resLE_app_top]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact hpush.of_iso (Scheme.Opens.topIso V) (Scheme.Opens.topIso U)
    (Scheme.Opens.topIso O) (Scheme.Opens.topIso U')
    (key f V U eU) (key g V O eO)
    (key g' U U' (hU'eq.le.trans inf_le_left))
    (key f' O U' (hU'eq.le.trans inf_le_right))

end SectionRingPushoutGeneral

/-! ## §2 (Brick 2). The fibre square is cartesian -/

section FiberSquare

variable {X Y : Scheme.{u}}

/-- **The scheme-theoretic fibre square is cartesian.**  By definition
`f.fiber t = pullback f (Y.fromSpecResidueField t)` with `f.fiberι t` the
first and `f.fiberToSpecResidueField t` the second projection, so the square

```
  X_t --fiberι--> X
   |               |f
   v               v
 Spec κ(t) -----> Y
```

is the defining cartesian square (Stacks 01JW). -/
theorem Scheme.Hom.isPullback_fiberι (f : X ⟶ Y) (t : Y) :
    IsPullback (f.fiberι t) (f.fiberToSpecResidueField t) f
      (Y.fromSpecResidueField t) :=
  IsPullback.of_hasPullback _ _

end FiberSquare

/-! ## §3 (Brick 3). The chart-level pushout at a fibre -/

section FiberChartPushout

variable {X Y : Scheme.{u}}

/-- **The fibre chart section-ring pushout.**  For a family `f : X ⟶ Y` over
an *affine* base `Y`, a point `t : Y` and an affine open `W ⊆ X`, the square

```
  Γ(Y, ⊤) --------> Γ(X, W)
     |                 |
     v                 v
  Γ(Spec κ(t), ⊤) -> Γ(X_t, fiberι ⁻¹ᵁ W)
```

is a pushout of commutative rings.  Brick 1 applied to the cartesian fibre
square of Brick 2 at `V = O = ⊤`, `U = W`,
`U' = f.fiberι t ⁻¹ᵁ W = (f.fiberι t ⁻¹ᵁ W) ⊓ (f.fiberToSpecResidueField t ⁻¹ᵁ ⊤)`.

Geometrically: the chart of the fibre over `t` cut out by `W` is the base
change of the chart `W` along `Spec κ(t) → Y` (Stacks 01HQ). -/
theorem isPushout_appLE_fiberChart (f : X ⟶ Y) [IsAffine Y] (t : Y)
    {W : X.Opens} (hW : IsAffineOpen W) :
    CategoryTheory.IsPushout
      (f.appLE ⊤ W le_top)
      ((Y.fromSpecResidueField t).appLE ⊤ ⊤ le_top)
      ((f.fiberι t).appLE W (f.fiberι t ⁻¹ᵁ W) le_rfl)
      ((f.fiberToSpecResidueField t).appLE ⊤ (f.fiberι t ⁻¹ᵁ W) le_top) :=
  isPushout_appLE_of_isPullback' (f.isPullback_fiberι t) le_top le_top
    (inf_top_eq _).symm (isAffineOpen_top Y) (isAffineOpen_top _) hW

end FiberChartPushout

/-! ## §4 (Brick 5, core). Restriction naturality of the canonical base map -/

section BaseMapRes

set_option backward.isDefEq.respectTransparency false in
/-- **The canonical base map commutes with restriction.**  For `g : Y ⟶ X`,
a module `N` on `X`, opens `V'' ≤ V'` of `X` and `W'' ≤ W'` of `Y` with
`W' ≤ g ⁻¹ᵁ V'` and `W'' ≤ g ⁻¹ᵁ V''`, restricting the canonical base-map
image `Γ(N, V') → Γ(g^* N, W')` to `W''` equals the base-map image of the
restriction of the section to `V''`:

`(g^* N)(W'' ← W') ∘ baseMap = baseMap ∘ N(V'' ← V')`.

Naturality of the `pullback ⊣ pushforward` adjunction unit in the open,
followed by collapse of the two composite restrictions
(`Scheme.Modules.sections_map_map`).

This is a **public** re-derivation of the `private` QuotScheme lemma
`pullback_app_isoTensor_baseMap_res` (`Picard/QuotScheme.lean` §02KE step
(6)); the precedent for such a re-derivation is
`AlgebraicGeometry.pullback_map_app_isoTensor_baseMap`
(`Picard/RigidPushforwardTransfer.lean`), which likewise replaces the
private restriction-collapse lemma `modules_res_res_hom` by the public
`Scheme.Modules.sections_map_map`. -/
lemma pullback_app_isoTensor_baseMap_res' {X Y : Scheme.{u}} (g : Y ⟶ X)
    (N : X.Modules) {V' V'' : X.Opens} {W' W'' : Y.Opens}
    (hW' : W' ≤ g ⁻¹ᵁ V') (hW'' : W'' ≤ g ⁻¹ᵁ V'')
    (hV : V'' ≤ V') (hW : W'' ≤ W') (x : Γ(N, V')) :
    (((Scheme.Modules.pullback g).obj N).presheaf.map (homOfLE hW).op).hom
        (pullback_app_isoTensor_baseMap g N hW' x)
      = pullback_app_isoTensor_baseMap g N hW''
        ((N.presheaf.map (homOfLE hV).op).hom x) := by
  have hnat := congrArg
    (fun (k : Γ(N, V') ⟶
        Γ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj N), V'')) =>
      (AddCommGrpCat.Hom.hom k) x)
    ((Scheme.Modules.Hom.mapPresheaf
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N)).naturality
      (homOfLE hV).op)
  have hL := Scheme.Modules.sections_map_map ((Scheme.Modules.pullback g).obj N)
    (homOfLE hW) (homOfLE hW') (homOfLE (hW.trans hW'))
    ((Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N) V').hom x)
  have hR := Scheme.Modules.sections_map_map ((Scheme.Modules.pullback g).obj N)
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

end BaseMapRes

/-! ## §5 (Brick 4). The chart fibre comparison `Θ_W` -/

section FiberChartComparison

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- Heartbeat headroom for the five-algebra `letI` dictionary of the fibre-chart
-- square and the section-formula transports, as in the Lane-F layer of
-- `Picard/RigidPushforwardTransfer.lean`.
set_option synthInstance.maxHeartbeats 800000 in
/-- **The chart fibre comparison isomorphism** (Stacks 02KG at `i = 0`, chart
form; Mumford AV II §5).  Let `f : X ⟶ Y` be a family over an affine base,
`M` a quasi-coherent module on `X`, `t : Y` a point and `W ⊆ X` an affine
open whose fibre chart `W_t = f.fiberι t ⁻¹ᵁ W` is again affine.  Then the
sections of the fibre restriction `M_t` over `W_t` are the scalar extension
of `Γ(M, W)` along `Γ(Y, ⊤) → κ(t)`:

`Γ(Spec κ(t), ⊤) ⊗_{Γ(Y, ⊤)} Γ(M, W) ≅ Γ(M_t, W_t)`,

as additive groups, the isomorphism sending `b ⊗ x` to
`b · (canonical base-map image of x)`.

The proof composes two existing pieces:

* the **affine section formula**
  `pullback_app_isoTensor_baseMap_sectionLinearEquiv` (`Picard/QuotScheme.lean`,
  Stacks 01HQ) applied to the fibre embedding, giving
  `Γ(X_t, W_t) ⊗_{Γ(X, W)} Γ(M, W) ≅ Γ(M_t, W_t)`;
* the **associativity bridge** `SectionBaseChange.bijective_addHom_of_isPushout`
  (`Picard/SectionBaseChange.lean`) along the fibre-chart section-ring pushout
  of Brick 3 (`isPushout_appLE_fiberChart`), which rewrites the tensor factor
  `Γ(X_t, W_t) = Γ(X, W) ⊗_{Γ(Y, ⊤)} Γ(Spec κ(t), ⊤)` and cancels.

Only additivity is asserted: the source is a `Γ(Spec κ(t), ⊤)`-module and the
target a `Γ(X_t, W_t)`-module, and the comparison is semilinear over the
structural map between them — which is exactly the content of the displayed
formula for `Θ (b ⊗ₜ x)`.

The assembly mirrors `isIso_pushforwardBaseChangeMap_app_of_isPullback`
(`Picard/RigidPushforwardTransfer.lean`), which performs the same two-step
identification for the pushforward base-change mate. -/
theorem exists_fiberChartTensorEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] (t : Y)
    (M : X.Modules) [M.IsQuasicoherent] {W : X.Opens} (hW : IsAffineOpen W)
    (hWt : IsAffineOpen (f.fiberι t ⁻¹ᵁ W)) :
    letI : Algebra Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤) :=
      ((Y.fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI := f.baseSectionsModule M W
    Nonempty { Θ : TensorProduct Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤) Γ(M, W) ≃+
        Γ(f.fiberModule t M, f.fiberι t ⁻¹ᵁ W) //
      ∀ (b : Γ(Spec (Y.residueField t), ⊤)) (x : Γ(M, W)),
        Θ (b ⊗ₜ[Γ(Y, ⊤)] x) =
          ((f.fiberToSpecResidueField t).appLE ⊤ (f.fiberι t ⁻¹ᵁ W) le_top).hom b •
            pullback_app_isoTensor_baseMap (f.fiberι t) M
              (le_refl (f.fiberι t ⁻¹ᵁ W)) x } := by
  letI aAB : Algebra Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤) :=
    ((Y.fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI mAM := f.baseSectionsModule M W
  -- the algebra dictionary of the fibre-chart section-ring square
  letI aAC : Algebra Γ(Y, ⊤) Γ(X, W) := (f.appLE ⊤ W le_top).hom.toAlgebra
  letI aCD : Algebra Γ(X, W) Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W) :=
    ((f.fiberι t).appLE W (f.fiberι t ⁻¹ᵁ W) le_rfl).hom.toAlgebra
  letI aBD : Algebra Γ(Spec (Y.residueField t), ⊤) Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W) :=
    ((f.fiberToSpecResidueField t).appLE ⊤ (f.fiberι t ⁻¹ᵁ W) le_top).hom.toAlgebra
  letI aAD : Algebra Γ(Y, ⊤) Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W) :=
    ((f.appLE ⊤ W le_top) ≫
      ((f.fiberι t).appLE W (f.fiberι t ⁻¹ᵁ W) le_rfl)).hom.toAlgebra
  have hsq := (isPushout_appLE_fiberChart f t hW).w
  haveI tACD : IsScalarTower Γ(Y, ⊤) Γ(X, W) Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI tABD : IsScalarTower Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤)
      Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      have h0 := congrArg
        (fun (φ : Γ(Y, ⊤) ⟶ Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W)) => φ.hom r) hsq
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h0
      exact h0)
  haveI pushAlg : Algebra.IsPushout Γ(Y, ⊤) Γ(X, W) Γ(Spec (Y.residueField t), ⊤)
      Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W) :=
    (CommRingCat.isPushout_iff_isPushout).mp (isPushout_appLE_fiberChart f t hW)
  haveI tACM : IsScalarTower Γ(Y, ⊤) Γ(X, W) Γ(M, W) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  -- the affine section formula for the fibre embedding
  obtain ⟨⟨eL, heL⟩⟩ :=
    pullback_app_isoTensor_baseMap_sectionLinearEquiv (f.fiberι t) M hWt hW
      (le_refl (f.fiberι t ⁻¹ᵁ W))
  -- the scalar-extension bridge along the fibre-chart pushout
  let s : TensorProduct Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤) Γ(M, W) →+
      TensorProduct Γ(X, W) Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W) Γ(M, W) :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun b => AddMonoidHom.mk'
        (fun m => algebraMap Γ(Spec (Y.residueField t), ⊤)
          Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W) b ⊗ₜ[Γ(X, W)] m)
        (fun m₁ m₂ => TensorProduct.tmul_add _ m₁ m₂))
        (fun b₁ b₂ => by
          ext m
          simp [TensorProduct.add_tmul]))
      (fun r b m => by
        change algebraMap Γ(Spec (Y.residueField t), ⊤)
            Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W) (r • b) ⊗ₜ[Γ(X, W)] m =
          algebraMap Γ(Spec (Y.residueField t), ⊤)
            Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W) b ⊗ₜ[Γ(X, W)] (r • m)
        rw [Algebra.smul_def, map_mul,
          ← IsScalarTower.algebraMap_apply Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤)
            Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W),
          IsScalarTower.algebraMap_apply Γ(Y, ⊤) Γ(X, W)
            Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W),
          ← Algebra.smul_def, TensorProduct.smul_tmul,
          IsScalarTower.algebraMap_smul Γ(X, W) r m])
  have hs : ∀ (b : Γ(Spec (Y.residueField t), ⊤)) (m : Γ(M, W)),
      s (b ⊗ₜ[Γ(Y, ⊤)] m) = algebraMap Γ(Spec (Y.residueField t), ⊤)
        Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W) b ⊗ₜ[Γ(X, W)] m :=
    fun b m => TensorProduct.liftAddHom_tmul _ _ b m
  have hs_bij : Function.Bijective s :=
    SectionBaseChange.bijective_addHom_of_isPushout s hs
  refine ⟨⟨AddEquiv.ofBijective (eL.toAddEquiv.toAddMonoidHom.comp s)
    ((EquivLike.bijective eL).comp hs_bij), ?_⟩⟩
  intro b x
  change eL (s (b ⊗ₜ[Γ(Y, ⊤)] x)) = _
  rw [hs b x]
  have hsm : (algebraMap Γ(Spec (Y.residueField t), ⊤)
      Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W) b ⊗ₜ[Γ(X, W)] x :
      TensorProduct Γ(X, W) Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W) Γ(M, W)) =
      algebraMap Γ(Spec (Y.residueField t), ⊤) Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W) b •
        ((1 : Γ(f.fiber t, f.fiberι t ⁻¹ᵁ W)) ⊗ₜ[Γ(X, W)] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hsm, map_smul, heL]
  rfl

end FiberChartComparison

/-! ## §6 (Brick 5). Restriction naturality of the chart comparison -/

section FiberChartRes

set_option backward.isDefEq.respectTransparency false in
/-- **The chart fibre comparison is compatible with restriction.**  In terms
of the explicit formula `Θ_W (b ⊗ x) = b · baseMap_W x` of Brick 4
(`exists_fiberChartTensorEquiv`), restricting along `W'' ≤ f.fiberι t ⁻¹ᵁ W`
turns `Θ_W (b ⊗ x)` into `Θ_{W'} (b ⊗ x|_{W'})` for any `W' ≤ W` with
`W'' ≤ f.fiberι t ⁻¹ᵁ W'`:

`(Θ_W (b ⊗ x))|_{W''} = b · baseMap_{W''} (x|_{W'})`.

Two ingredients: the section restriction of a sheaf of modules is semilinear
(`Scheme.Modules.map_smul`) and the structural scalar restricts correctly
(`Scheme.Hom.appLE_map`); and the canonical base map commutes with
restriction (`pullback_app_isoTensor_baseMap_res'`, §4).

This is the naturality that makes the family `(Θ_W)_W` a map of *complexes*,
and hence Brick 6 (the Čech square) possible. -/
lemma fiberChart_smul_baseMap_res {X Y : Scheme.{u}} (f : X ⟶ Y) (t : Y)
    (M : X.Modules) {W W' : X.Opens} {W'' : (f.fiber t).Opens}
    (hWW' : W' ≤ W) (hW'' : W'' ≤ f.fiberι t ⁻¹ᵁ W')
    (hle : W'' ≤ f.fiberι t ⁻¹ᵁ W)
    (b : Γ(Spec (Y.residueField t), ⊤)) (x : Γ(M, W)) :
    (((f.fiberModule t M).presheaf.map (homOfLE hle).op).hom
        (((f.fiberToSpecResidueField t).appLE ⊤ (f.fiberι t ⁻¹ᵁ W) le_top).hom b •
          pullback_app_isoTensor_baseMap (f.fiberι t) M
            (le_refl (f.fiberι t ⁻¹ᵁ W)) x) : Γ(f.fiberModule t M, W'')) =
      ((f.fiberToSpecResidueField t).appLE ⊤ W'' le_top).hom b •
        pullback_app_isoTensor_baseMap (f.fiberι t) M hW''
          ((M.presheaf.map (homOfLE hWW').op).hom x) := by
  have hms := Scheme.Modules.map_smul (f.fiberModule t M)
    (homOfLE hle)
    (((f.fiberToSpecResidueField t).appLE ⊤ (f.fiberι t ⁻¹ᵁ W) le_top).hom b)
    (pullback_app_isoTensor_baseMap (f.fiberι t) M (le_refl (f.fiberι t ⁻¹ᵁ W)) x)
  have hr : ((f.fiber t).presheaf.map (homOfLE hle).op).hom
        (((f.fiberToSpecResidueField t).appLE ⊤ (f.fiberι t ⁻¹ᵁ W) le_top).hom b) =
      ((f.fiberToSpecResidueField t).appLE ⊤ W'' le_top).hom b := by
    have h0 := congrArg
      (fun (φ : Γ(Spec (Y.residueField t), ⊤) ⟶ Γ(f.fiber t, W'')) => φ.hom b)
      ((f.fiberToSpecResidueField t).appLE_map
        (le_top : (f.fiberι t ⁻¹ᵁ W) ≤ (f.fiberToSpecResidueField t) ⁻¹ᵁ ⊤)
        (homOfLE hle).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h0
    exact h0
  have hb := pullback_app_isoTensor_baseMap_res' (f.fiberι t) M
    (le_refl (f.fiberι t ⁻¹ᵁ W)) hW'' hWW' hle x
  refine hms.trans ?_
  exact Eq.trans (congrArg (fun z => ((f.fiber t).presheaf.map (homOfLE hle).op).hom
      (((f.fiberToSpecResidueField t).appLE ⊤ (f.fiberι t ⁻¹ᵁ W) le_top).hom b) • z) hb)
    (congrArg (fun r => r • pullback_app_isoTensor_baseMap (f.fiberι t) M hW''
      ((M.presheaf.map (homOfLE hWW').op).hom x)) hr)

end FiberChartRes

/-! ## §7 (Brick 6). The Čech square and fibrewise surjectivity -/

section CechFiberSquare

variable {X Y : Scheme.{u}}

set_option maxHeartbeats 1600000 in
-- The six local module structures and three chart comparisons make the final
-- commuting-square elaboration exceed the default heartbeat budget.
/-- **The fibre-chart comparison as an isomorphism of two-term complexes.**
For a quasicoherent module on a family over an affine base, residue-field base
change of the two-chart Cech complex is linearly equivalent to the Cech complex
of the induced fibre cover.

The degree-zero equivalence combines tensor/base-change on the two charts; the
degree-one equivalence is the corresponding comparison on their intersection.
Restriction naturality makes the resulting square commute.  This is the
reusable geometric input for surjectivity, kernel, and quotient-by-range
comparisons. -/
theorem exists_fiberCechLinearEquiv
    (𝒰 : X.AffineCoverMVSquare) (f : X ⟶ Y) [IsAffine Y]
    (M : X.Modules) [M.IsQuasicoherent] (t : Y) [IsAffineHom (f.fiberι t)] :
    letI : Algebra Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤) :=
      ((Y.fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI := f.baseSectionsModule M 𝒰.U₁
    letI := f.baseSectionsModule M 𝒰.U₂
    letI := f.baseSectionsModule M (𝒰.U₁ ⊓ 𝒰.U₂)
    letI := (f.fiberToSpecResidueField t).baseSectionsModule (f.fiberModule t M)
      ((𝒰.preimage (f.fiberι t)).U₁)
    letI := (f.fiberToSpecResidueField t).baseSectionsModule (f.fiberModule t M)
      ((𝒰.preimage (f.fiberι t)).U₂)
    letI := (f.fiberToSpecResidueField t).baseSectionsModule (f.fiberModule t M)
      ((𝒰.preimage (f.fiberι t)).U₁ ⊓ (𝒰.preimage (f.fiberι t)).U₂)
    ∃ (e0 : TensorProduct Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤)
          (Γ(M, 𝒰.U₁) × Γ(M, 𝒰.U₂)) ≃ₗ[Γ(Spec (Y.residueField t), ⊤)]
          (Γ(f.fiberModule t M, (𝒰.preimage (f.fiberι t)).U₁) ×
            Γ(f.fiberModule t M, (𝒰.preimage (f.fiberι t)).U₂)))
      (e1 : TensorProduct Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤)
          Γ(M, 𝒰.U₁ ⊓ 𝒰.U₂) ≃ₗ[Γ(Spec (Y.residueField t), ⊤)]
          Γ(f.fiberModule t M,
            (𝒰.preimage (f.fiberι t)).U₁ ⊓ (𝒰.preimage (f.fiberι t)).U₂)),
      ((𝒰.preimage (f.fiberι t)).moduleSectionDiffBase
          (f.fiberToSpecResidueField t) (f.fiberModule t M)) ∘ₗ e0.toLinearMap =
        e1.toLinearMap ∘ₗ ((𝒰.moduleSectionDiffBase f M).baseChange
          Γ(Spec (Y.residueField t), ⊤)) := by
  letI aAB : Algebra Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤) :=
    ((Y.fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI mA1 := f.baseSectionsModule M 𝒰.U₁
  letI mA2 := f.baseSectionsModule M 𝒰.U₂
  letI mA0 := f.baseSectionsModule M (𝒰.U₁ ⊓ 𝒰.U₂)
  letI nB1 := (f.fiberToSpecResidueField t).baseSectionsModule (f.fiberModule t M)
    ((𝒰.preimage (f.fiberι t)).U₁)
  letI nB2 := (f.fiberToSpecResidueField t).baseSectionsModule (f.fiberModule t M)
    ((𝒰.preimage (f.fiberι t)).U₂)
  letI nB0 := (f.fiberToSpecResidueField t).baseSectionsModule (f.fiberModule t M)
    ((𝒰.preimage (f.fiberι t)).U₁ ⊓ (𝒰.preimage (f.fiberι t)).U₂)
  obtain ⟨⟨Θ₁, hΘ₁⟩⟩ := exists_fiberChartTensorEquiv f t M 𝒰.isAffineOpen_U₁
    (𝒰.isAffineOpen_U₁.preimage (f.fiberι t))
  obtain ⟨⟨Θ₂, hΘ₂⟩⟩ := exists_fiberChartTensorEquiv f t M 𝒰.isAffineOpen_U₂
    (𝒰.isAffineOpen_U₂.preimage (f.fiberι t))
  obtain ⟨⟨Θ₀, hΘ₀⟩⟩ := exists_fiberChartTensorEquiv f t M 𝒰.isAffineOpen_inf
    (𝒰.isAffineOpen_inf.preimage (f.fiberι t))
  haveI : (f.fiberModule t M).IsQuasicoherent := Scheme.Hom.fiberModule_isQuasicoherent f t M
  have hsm1 : ∀ (c : Γ(Spec (Y.residueField t), ⊤))
      (z : TensorProduct Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤) Γ(M, 𝒰.U₁)),
      Θ₁ (c • z) =
        ((f.fiberToSpecResidueField t).appLE ⊤ (f.fiberι t ⁻¹ᵁ 𝒰.U₁) le_top).hom c • Θ₁ z := by
    intro c z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, smul_add]
    | tmul b x =>
      rw [TensorProduct.smul_tmul', hΘ₁, hΘ₁, smul_eq_mul, map_mul, mul_smul]
      rfl
  have hsm2 : ∀ (c : Γ(Spec (Y.residueField t), ⊤))
      (z : TensorProduct Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤) Γ(M, 𝒰.U₂)),
      Θ₂ (c • z) =
        ((f.fiberToSpecResidueField t).appLE ⊤ (f.fiberι t ⁻¹ᵁ 𝒰.U₂) le_top).hom c • Θ₂ z := by
    intro c z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, smul_add]
    | tmul b x =>
      rw [TensorProduct.smul_tmul', hΘ₂, hΘ₂, smul_eq_mul, map_mul, mul_smul]
      rfl
  have hsm0 : ∀ (c : Γ(Spec (Y.residueField t), ⊤))
      (z : TensorProduct Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤)
        Γ(M, 𝒰.U₁ ⊓ 𝒰.U₂)),
      Θ₀ (c • z) =
        ((f.fiberToSpecResidueField t).appLE ⊤
          (f.fiberι t ⁻¹ᵁ (𝒰.U₁ ⊓ 𝒰.U₂)) le_top).hom c • Θ₀ z := by
    intro c z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, smul_add]
    | tmul b x =>
      rw [TensorProduct.smul_tmul', hΘ₀, hΘ₀, smul_eq_mul, map_mul, mul_smul]
      rfl
  have hsquare : ∀ w : TensorProduct Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤)
      (Γ(M, 𝒰.U₁) × Γ(M, 𝒰.U₂)),
      Θ₀ ((𝒰.moduleSectionDiffBase f M).baseChange Γ(Spec (Y.residueField t), ⊤) w) =
        (𝒰.preimage (f.fiberι t)).moduleSectionDiff (f.fiberModule t M)
          (Θ₁ (TensorProduct.prodRight Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤)
              Γ(Spec (Y.residueField t), ⊤) Γ(M, 𝒰.U₁) Γ(M, 𝒰.U₂) w).1,
           Θ₂ (TensorProduct.prodRight Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤)
              Γ(Spec (Y.residueField t), ⊤) Γ(M, 𝒰.U₁) Γ(M, 𝒰.U₂) w).2) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
      exact (map_zero _).symm
    | add w₁ w₂ ih₁ ih₂ =>
      simp only [map_add, Prod.fst_add, Prod.snd_add]
      rw [ih₁, ih₂]
      exact (map_add _ _ _).symm
    | tmul b p =>
      obtain ⟨x₁, x₂⟩ := p
      rw [LinearMap.baseChange_tmul, hΘ₀ b _]
      simp only [TensorProduct.prodRight_tmul, hΘ₁, hΘ₂,
        Scheme.AffineCoverMVSquare.moduleSectionDiffBase_apply,
        Scheme.AffineCoverMVSquare.moduleSectionDiff_apply]
      have e₁ := fiberChart_smul_baseMap_res f t M
        (inf_le_left : 𝒰.U₁ ⊓ 𝒰.U₂ ≤ 𝒰.U₁) (le_refl (f.fiberι t ⁻¹ᵁ (𝒰.U₁ ⊓ 𝒰.U₂)))
        ((f.fiberι t).preimage_mono (inf_le_left : 𝒰.U₁ ⊓ 𝒰.U₂ ≤ 𝒰.U₁)) b x₁
      have e₂ := fiberChart_smul_baseMap_res f t M
        (inf_le_right : 𝒰.U₁ ⊓ 𝒰.U₂ ≤ 𝒰.U₂) (le_refl (f.fiberι t ⁻¹ᵁ (𝒰.U₁ ⊓ 𝒰.U₂)))
        ((f.fiberι t).preimage_mono (inf_le_right : 𝒰.U₁ ⊓ 𝒰.U₂ ≤ 𝒰.U₂)) b x₂
      rw [map_sub, smul_sub]
      exact congrArg₂ (· - ·) e₁.symm e₂.symm
  set PR := TensorProduct.prodRight Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤)
      Γ(Spec (Y.residueField t), ⊤) Γ(M, 𝒰.U₁) Γ(M, 𝒰.U₂) with hPR
  set Φ : TensorProduct Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤)
        (Γ(M, 𝒰.U₁) × Γ(M, 𝒰.U₂)) ≃+
      (Γ(f.fiberModule t M, (𝒰.preimage (f.fiberι t)).U₁) ×
        Γ(f.fiberModule t M, (𝒰.preimage (f.fiberι t)).U₂)) :=
    PR.toAddEquiv.trans (Θ₁.prodCongr Θ₂) with hΦdef
  have hΦsmul : ∀ (c : Γ(Spec (Y.residueField t), ⊤)) w, Φ (c • w) = c • Φ w := by
    intro c w
    rw [hΦdef]
    change (Θ₁ (PR (c • w)).1, Θ₂ (PR (c • w)).2) = _
    rw [map_smul]
    exact Prod.ext (hsm1 c (PR w).1) (hsm2 c (PR w).2)
  let e0 : TensorProduct Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤)
        (Γ(M, 𝒰.U₁) × Γ(M, 𝒰.U₂)) ≃ₗ[Γ(Spec (Y.residueField t), ⊤)]
      (Γ(f.fiberModule t M, (𝒰.preimage (f.fiberι t)).U₁) ×
        Γ(f.fiberModule t M, (𝒰.preimage (f.fiberι t)).U₂)) :=
    { Φ with map_smul' := hΦsmul }
  let e1 : TensorProduct Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤)
        Γ(M, 𝒰.U₁ ⊓ 𝒰.U₂) ≃ₗ[Γ(Spec (Y.residueField t), ⊤)]
      Γ(f.fiberModule t M,
        (𝒰.preimage (f.fiberι t)).U₁ ⊓ (𝒰.preimage (f.fiberι t)).U₂) :=
    { Θ₀ with map_smul' := hsm0 }
  refine ⟨e0, e1, ?_⟩
  ext w
  exact (hsquare w).symm

/-- **The base-changed Čech difference map at a fibre is surjective.**

Let `f : X ⟶ Y` be a family over an affine base, `𝒰 = {U₁, U₂}` a bundled
2-affine cover of `X`, `M` a quasi-coherent module on `X`, and `t : Y` a
point at which the fibre Čech `Ȟ¹` of `M_t` vanishes
(`Scheme.Hom.FiberH1Vanishing`).  Then the `κ(t)`-base change of the
`Γ(Y, ⊤)`-linear Čech difference map
`d : Γ(M, U₁) × Γ(M, U₂) → Γ(M, U₁ ⊓ U₂)` is surjective.

Proof (Stacks 02KG, `i = 0` and `i = 1` in the two-term Čech guise): the
chart comparisons of Brick 4 fit into a commuting square

```
  κ(t) ⊗ (Γ(M,U₁) × Γ(M,U₂)) --d ⊗ κ(t)--> κ(t) ⊗ Γ(M, U₁ ⊓ U₂)
      |  Θ₁ × Θ₂ ∘ prodRight                    |  Θ₀
      v                                          v
  Γ(M_t, U₁ᵗ) × Γ(M_t, U₂ᵗ) ------d_t--------> Γ(M_t, U₁ᵗ ⊓ U₂ᵗ)
```

whose commutativity is checked on pure tensors using the restriction
naturality of Brick 5, and whose three vertical maps are bijections.  The
bottom map is surjective because the fibre restriction `M_t` is
quasi-coherent (`Scheme.Hom.fiberModule_isQuasicoherent`), so the ∃-form
fibrewise vanishing transfers to the specific preimage cover
`𝒰_t = 𝒰.preimage (f.fiberι t)`
(`Scheme.Hom.FiberH1Vanishing.surjective_moduleSectionDiff`).  Surjectivity
of the top map follows. -/
theorem Scheme.AffineCoverMVSquare.surjective_moduleSectionDiffBase_baseChange_residueField
    (𝒰 : X.AffineCoverMVSquare) (f : X ⟶ Y) [IsAffine Y]
    (M : X.Modules) [M.IsQuasicoherent] (t : Y) [IsAffineHom (f.fiberι t)]
    (h1 : f.FiberH1Vanishing M t) :
    letI : Algebra Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤) :=
      ((Y.fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI := f.baseSectionsModule M 𝒰.U₁
    letI := f.baseSectionsModule M 𝒰.U₂
    letI := f.baseSectionsModule M (𝒰.U₁ ⊓ 𝒰.U₂)
    Function.Surjective ((𝒰.moduleSectionDiffBase f M).baseChange
      Γ(Spec (Y.residueField t), ⊤)) := by
  letI aAB : Algebra Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤) :=
    ((Y.fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI mA1 := f.baseSectionsModule M 𝒰.U₁
  letI mA2 := f.baseSectionsModule M 𝒰.U₂
  letI mA0 := f.baseSectionsModule M (𝒰.U₁ ⊓ 𝒰.U₂)
  letI nB1 := (f.fiberToSpecResidueField t).baseSectionsModule (f.fiberModule t M)
    ((𝒰.preimage (f.fiberι t)).U₁)
  letI nB2 := (f.fiberToSpecResidueField t).baseSectionsModule (f.fiberModule t M)
    ((𝒰.preimage (f.fiberι t)).U₂)
  letI nB0 := (f.fiberToSpecResidueField t).baseSectionsModule (f.fiberModule t M)
    ((𝒰.preimage (f.fiberι t)).U₁ ⊓ (𝒰.preimage (f.fiberι t)).U₂)
  haveI : (f.fiberModule t M).IsQuasicoherent :=
    Scheme.Hom.fiberModule_isQuasicoherent f t M
  obtain ⟨e0, e1, hcomm⟩ := exists_fiberCechLinearEquiv 𝒰 f M t
  have hdt : Function.Surjective
      ⇑((𝒰.preimage (f.fiberι t)).moduleSectionDiff (f.fiberModule t M)) :=
    h1.surjective_moduleSectionDiff (𝒰.preimage (f.fiberι t))
  intro z
  obtain ⟨u, hu⟩ := hdt (e1 z)
  refine ⟨e0.symm u, e1.injective ?_⟩
  have hc := DFunLike.congr_fun hcomm (e0.symm u)
  exact hc.symm.trans ((congrArg _ (e0.apply_symm_apply u)).trans hu)

end CechFiberSquare

/-! ## §8 (Brick 8). Transport of surjectivity along an algebra isomorphism -/

section BaseChangeTransport

/-- **Base-changed surjectivity only depends on the isomorphism class of the
scalar-extension algebra.**  If `S ≃ₐ[R] T` and `d ⊗_R S` is surjective, then
so is `d ⊗_R T`: the square

```
  S ⊗ M₀ --d ⊗ S--> S ⊗ M₁
     |                  |
  e⊗1|                  |e⊗1
     v                  v
  T ⊗ M₀ --d ⊗ T--> T ⊗ M₁
```

commutes (checked on pure tensors) and its vertical maps are bijections. -/
theorem surjective_baseChange_of_algEquiv {R : Type u} [CommRing R]
    {M₀ M₁ : Type u} [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁]
    (d : M₀ →ₗ[R] M₁) {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (e : S ≃ₐ[R] T) (h : Function.Surjective (d.baseChange S)) :
    Function.Surjective (d.baseChange T) := by
  have hsq : ∀ z : TensorProduct R S M₀,
      TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M₁) (d.baseChange S z) =
        d.baseChange T (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M₀) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul s x => simp [LinearMap.baseChange_tmul]
  intro y
  obtain ⟨z, hz⟩ := h ((TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M₁)).symm y)
  refine ⟨TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M₀) z, ?_⟩
  rw [← hsq, hz, LinearEquiv.apply_symm_apply]

end BaseChangeTransport

/-! ## §9 (Brick 7). Maximal ideals of `Γ(Spec R, ⊤)` are residue fields -/

section MaximalToPoint

/-- **Every maximal ideal of the section ring of an affine scheme is the
kernel of a residue-field evaluation.**  For `R : CommRingCat` and a maximal
ideal `m` of `Γ(Spec R, ⊤)` there is a point `t : Spec R` such that the
structural map

`Γ(Spec R, ⊤) ⟶ Γ(Spec κ(t), ⊤)`,  `(Spec R).fromSpecResidueField t` on
global sections,

is surjective with kernel exactly `m`.  Concretely `t` is the prime
`ε⁻¹(m) ⊆ R` obtained by transporting `m` across the canonical
`ε : Γ(Spec R, ⊤) ≃+* R` (`Scheme.ΓSpecIso`), and the structural map
factors as

`Γ(Spec R, ⊤) --ε--> R --algebraMap--> κ(t.asIdeal) --≅--> Γ(Spec κ(t), ⊤)`

by `Spec.map_residueFieldIso_inv_eq_fromSpecResidueField` together with the
naturality of `Scheme.ΓSpecIso`.  Surjectivity is
`Ideal.algebraMap_residueField_surjective` (valid because `t.asIdeal` is
maximal) and the kernel computation is `Ideal.ker_algebraMap_residueField`
(Stacks 00DY / EGA I 1.1.1). -/
theorem exists_point_appLE_fromSpecResidueField_of_isMaximal (R : CommRingCat.{u})
    (m : Ideal Γ(Spec R, ⊤)) (hm : m.IsMaximal) :
    ∃ t : Spec R,
      Function.Surjective
          ⇑(((Spec R).fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom ∧
        RingHom.ker (((Spec R).fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom = m := by
  letI := hm
  let ε : Γ(Spec R, ⊤) ≃+* R := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  haveI hmax : (Ideal.comap (ε.symm : R →+* Γ(Spec R, ⊤)) m).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ ε.symm.surjective
  set t : Spec R :=
    ⟨Ideal.comap (ε.symm : R →+* Γ(Spec R, ⊤)) m, hmax.isPrime⟩ with ht
  -- the residue-field comparison, as a ring isomorphism onto the section ring
  let uiso : CommRingCat.of t.asIdeal.ResidueField ≅
      Γ(Spec ((Spec R).residueField t), ⊤) :=
    (Scheme.Spec.residueFieldIso R t).symm ≪≫
      (Scheme.ΓSpecIso ((Spec R).residueField t)).symm
  have hnat : ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B),
      (Spec.map φ).appTop =
        (Scheme.ΓSpecIso A).hom ≫ φ ≫ (Scheme.ΓSpecIso B).inv := by
    intro A B φ
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality φ, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hfac : ((Spec R).fromSpecResidueField t).appTop =
      (Scheme.ΓSpecIso R).hom ≫
        CommRingCat.ofHom (algebraMap R t.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso R t).inv ≫
        (Scheme.ΓSpecIso ((Spec R).residueField t)).inv := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R t,
      Scheme.Hom.comp_appTop, hnat, hnat]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  have happ : ∀ x : Γ(Spec R, ⊤),
      (((Spec R).fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom x =
        uiso.commRingCatIsoToRingEquiv
          (algebraMap R t.asIdeal.ResidueField (ε x)) := by
    intro x
    have hLE : ((Spec R).fromSpecResidueField t).appLE ⊤ ⊤ le_top =
        ((Spec R).fromSpecResidueField t).appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [hLE, hfac]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    rfl
  refine ⟨t, ?_, ?_⟩
  · -- surjectivity
    intro y
    obtain ⟨y₁, rfl⟩ := uiso.commRingCatIsoToRingEquiv.surjective y
    obtain ⟨y₂, rfl⟩ := Ideal.algebraMap_residueField_surjective t.asIdeal y₁
    obtain ⟨x, rfl⟩ := ε.surjective y₂
    exact ⟨x, happ x⟩
  · -- the kernel is `m`
    refine Ideal.ext fun x => ?_
    rw [RingHom.mem_ker, happ x, map_eq_zero_iff _ uiso.commRingCatIsoToRingEquiv.injective,
      Ideal.algebraMap_residueField_eq_zero]
    change ε x ∈ Ideal.comap (ε.symm : R →+* Γ(Spec R, ⊤)) m ↔ x ∈ m
    rw [Ideal.mem_comap, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]

end MaximalToPoint

/-! ## §10. The consumer form: `hfib` for the ℙ¹ engine -/

section P1Hfib

set_option maxHeartbeats 1600000 in
-- Heartbeat headroom for the pinned ℙ¹ spelling: the `baseSectionsModule`
-- `letI` block plus the `Γ(Spec A, ⊤)`-algebra dictionary of the residue field.
set_option synthInstance.maxHeartbeats 800000 in
/-- **`hfib` for the wave-4 ℙ¹ engine, from fibrewise `h¹`-vanishing.**

This is the hypothesis `_hfib` of
`Adelic.p1Cech_h0_baseChange_of_fibrewise_h1_vanishing`
(`Picard/RigidPushforwardP1Engine.lean` §5), verbatim: for every maximal
ideal `𝔪` of `R₀ = Γ(Spec A, ⊤)`, the base change along `R₀ → R₀ ⧸ 𝔪` of the
two-term Čech difference map of the standard 2-chart cover of `ℙ¹_A` is
surjective.

It is deduced from the *geometric* hypothesis of fibrewise Čech
`h¹`-vanishing on the scheme-theoretic fibres `ℙ¹_t` (Mumford AV II §5;
Stacks 02KG; EGA III 7.7.5) in two moves:

* every maximal ideal `𝔪 ⊆ R₀` is the kernel of the residue-field
  evaluation at a point `t ∈ Spec A`, and that evaluation is surjective
  (`exists_point_appLE_fromSpecResidueField_of_isMaximal`), so
  `R₀ ⧸ 𝔪 ≅ Γ(Spec κ(t), ⊤)` as `R₀`-algebras;
* the `κ(t)`-base change of the Čech difference map *is* the Čech
  difference map of the fibre cover of `ℙ¹_t`, by the chart pushout
  `Γ(ℙ¹_t, W_t) = Γ(ℙ¹_A, W) ⊗_{R₀} κ(t)`, hence is surjective
  (`Scheme.AffineCoverMVSquare.surjective_moduleSectionDiffBase_baseChange_residueField`);

and the two are glued by `surjective_baseChange_of_algEquiv`. -/
theorem Adelic.p1_hfib_of_fiberH1Vanishing {k : Type u} [Field k]
    (A : Type u) [CommRing A] [Algebra k A]
    (M : (Limits.pullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    [M.IsFinitePresentation]
    (h1 : ∀ t : Spec (CommRingCat.of A),
      (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing M t) :
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (Adelic.p1BaseChangeCoverSquare A).U₁
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (Adelic.p1BaseChangeCoverSquare A).U₂
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        ((Adelic.p1BaseChangeCoverSquare A).U₁ ⊓ (Adelic.p1BaseChangeCoverSquare A).U₂)
    ∀ (m : Ideal Γ(Spec (CommRingCat.of A), ⊤)), m.IsMaximal →
      Function.Surjective
        (((Adelic.p1BaseChangeCoverSquare A).moduleSectionDiffBase
          (pullback.snd (p1Over k).hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M).baseChange
          (Γ(Spec (CommRingCat.of A), ⊤) ⧸ m)) := by
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      (Adelic.p1BaseChangeCoverSquare A).U₁
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      (Adelic.p1BaseChangeCoverSquare A).U₂
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      ((Adelic.p1BaseChangeCoverSquare A).U₁ ⊓ (Adelic.p1BaseChangeCoverSquare A).U₂)
  intro m hm
  obtain ⟨t, hsurj, hker⟩ :=
    exists_point_appLE_fromSpecResidueField_of_isMaximal (CommRingCat.of A) m hm
  letI aAB : Algebra Γ(Spec (CommRingCat.of A), ⊤)
      Γ(Spec ((Spec (CommRingCat.of A)).residueField t), ⊤) :=
    (((Spec (CommRingCat.of A)).fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom.toAlgebra
  -- the fibre computation: surjectivity after base change to `κ(t)`
  have hbc :=
    Scheme.AffineCoverMVSquare.surjective_moduleSectionDiffBase_baseChange_residueField
      (Adelic.p1BaseChangeCoverSquare A)
      (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
      M t (h1 t)
  -- `R₀ ⧸ 𝔪 ≅ κ(t)` as `R₀`-algebras
  let e' : (Γ(Spec (CommRingCat.of A), ⊤) ⧸ m) ≃ₐ[Γ(Spec (CommRingCat.of A), ⊤)]
      Γ(Spec ((Spec (CommRingCat.of A)).residueField t), ⊤) :=
    { (Ideal.quotEquivOfEq hker.symm).trans
        (RingHom.quotientKerEquivOfSurjective hsurj) with
      commutes' := fun r => by
        change (RingHom.quotientKerEquivOfSurjective hsurj)
          (Ideal.quotEquivOfEq hker.symm (Ideal.Quotient.mk m r)) = _
        rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
        rfl }
  exact surjective_baseChange_of_algEquiv _ e'.symm hbc

end P1Hfib

end AlgebraicGeometry
