/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAffPullField
import AlgebraicJacobian.Picard.DivRepAwayPush

/-!
# F5 — `pull_naturality`

`Picard/DivRepAffPullField.lean` defines the forward map `divRepPullValue`, pinned by
`IsDivRepPullValue`.  This file proves the last **ε-free** field of
`DivRepAffinePullback`:

* `AlgebraicGeometry.divRepPullValue_naturality` —
  `divRepPullValue (Over.overSpecMap φ ≫ v) = DivFamZar.mapAlgHom φ (divRepPullValue v)`
  for a `k`-algebra map `φ : A →ₐ[k] B`.

**The whole proof is "push the factorization forward and use `_eq_of`".**  Nothing is
glued a second time.  Given an atlas factorization of `v` over a spanning family
`f : Fin m → A`, the pushed family `φ ∘ f` spans `B` (`DivFamZar.span_range_map_eq_top`)
and each piece's chart map composes with the pushed carrier comparison
`Localization.awayMapₐ φ (f t)` to present `Over.overSpecMap φ ≫ v` over
`Localization.Away (φ (f t))`.  So `DivFamZar.mapAlgHom φ (divRepPullValue v)` satisfies
`IsDivRepPullValue` for `Over.overSpecMap φ ≫ v`, and `divRepPullValue_eq_of` finishes.

The two identities that make the bookkeeping close are exactly the two lemmas of
`Picard/DivRepAwayPush.lean`: the carrier square `awayMapₐ_comp_toAlgHom` (restrict then
push = push then restrict) and the spanning statement.  The chart side needs one
`Spec.map` translation of the same square, `specMap_awayMapₐ_comp`, proved here.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Grassmannian Scheme

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftDivRepAffPullNat :
    C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
  [IsDominant pi]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g : ℕ)
variable (r1 r2 : ℕ)
variable (b1 : Module.Basis (Fin r1) k
  ↥(divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(divisorSections k
    ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤))

local notation "DivOver" =>
  divSchemeOver k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm)

local notation "ChartRing" => fun i j =>
  DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm) i j

local notation "ChartMap" => fun i j =>
  divCarveChartToDivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm) i j

/-! ## The pushed factorization -/

section Push

variable {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

/-- **The carrier square on the scheme side**: `Spec` of the structure map of the pushed
carrier, followed by `Spec φ`, is `Spec` of the structure map of the original carrier
followed by `Spec` of the pushed comparison map.  This is `awayMapₐ_comp_toAlgHom` of
`Picard/DivRepAwayPush.lean` read through `Spec.map`, and it is what turns a chart
presentation of `v` into a chart presentation of `Over.overSpecMap φ ≫ v`. -/
theorem specMap_awayMapₐ_comp (φ : A →ₐ[k] B) (a : A) :
    Spec.map (CommRingCat.ofHom (Localization.awayMapₐ φ a).toRingHom)
        ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a)))
      = Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (φ a))))
        ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  refine congrArg Spec.map (CommRingCat.hom_ext ?_)
  exact RingHom.ext fun x => DivFamZar.awayMapₐ_algebraMap φ a x

end Push

/-! ## Naturality of the forward map -/

set_option maxHeartbeats 1600000 in
-- The pushed factorization's chart clause is checked against the `IsScalarTower`
-- structure maps of two away localizations at once, as in `divRepPullAt_awayMul_compat`.
/-- **`pull_naturality`, the last ε-free field of `DivRepAffinePullback`**: the forward
map commutes with base change along a `k`-algebra map.

Proof: take the atlas factorization of `v` that `divRepPullValue`'s specification hands
back, push it along `φ`, and observe that `DivFamZar.mapAlgHom φ (divRepPullValue v)`
restricts to the chart pulls of the pushed factorization — the chart maps are the
composites `Localization.awayMapₐ φ (f t) ∘ cw t`, and the restriction identity is the
carrier square of `Picard/DivRepAwayPush.lean` transported by `divRepPullAt_comp`.  Then
`divRepPullValue_eq_of` identifies the two values, so no second glue is performed. -/
theorem divRepPullValue_naturality
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hU : DivRepChartFamily.IsCompatible (hpi := hpi) g r1 r2 b1 b2 U)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (phi : A →ₐ[k] B) (v : overSpec k A ⟶ DivOver) :
    divRepPullValue hpi g r1 r2 b1 b2 U hU B (Over.overSpecMap phi ≫ v)
      = DivFamZar.mapAlgHom phi
        (divRepPullValue hpi g r1 r2 b1 b2 U hU A v) := by
  classical
  obtain ⟨m, f, hspan, ci, cj, cw, hcw, hF⟩ :=
    divRepPullValue_spec hpi g r1 r2 b1 b2 U hU A v
  refine divRepPullValue_eq_of hpi g r1 r2 b1 b2 U hU B _
    ⟨m, fun t => phi (f t), DivFamZar.span_range_map_eq_top phi f hspan, ci, cj,
      fun t => (Localization.awayMapₐ phi (f t)).comp (cw t), ?_, ?_⟩
  · -- the pushed chart maps present `Over.overSpecMap phi ≫ v`
    intro t
    have hchart : Spec.map (CommRingCat.ofHom
          ((Localization.awayMapₐ phi (f t)).comp (cw t)).toRingHom)
        = Spec.map (CommRingCat.ofHom (Localization.awayMapₐ phi (f t)).toRingHom)
          ≫ Spec.map (CommRingCat.ofHom (cw t).toRingHom) := by
      rw [← Spec.map_comp]
      rfl
    rw [hchart, Category.assoc, hcw t, Over.comp_left, Over.overSpecMap_left,
      ← Category.assoc, ← Category.assoc, specMap_awayMapₐ_comp phi (f t)]
  · -- and the pushed class restricts to their chart pulls
    intro t
    have hsq : (IsScalarTower.toAlgHom k B (Localization.Away (phi (f t)))).comp phi
        = (Localization.awayMapₐ phi (f t)).comp
          (IsScalarTower.toAlgHom k A (Localization.Away (f t))) :=
      (DivFamZar.awayMapₐ_comp_toAlgHom phi (f t)).symm
    rw [← DivFamZar.mapAlgHom_comp, hsq, DivFamZar.mapAlgHom_comp, hF t,
      divRepPullAt_comp (hpi := hpi) g r1 r2 b1 b2 U (ci t) (cj t) (cw t)
        (Localization.awayMapₐ phi (f t))]

end Curve

end AlgebraicGeometry
