/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAffPullNat
import AlgebraicJacobian.Picard.DivRepGlobalClassify

/-!
# F5 — `isDivRepClassify_pull` from the per-chart clause, and the whole package from U2

`Picard/DivRepAffPullField.lean` defines `pull` and `Picard/DivRepAffPullNat.lean` proves
`pull_naturality`.  The third field of `DivRepAffinePullback.ofPull` is
`isDivRepClassify_pull`, and this file discharges it — **from the same hypothesis
`IsCompatible` already needs**:

> `IsChartClause U` : for every chart `(i, j)` and every `ω : R_Z(i,j) →ₐ[k] S`, the chart
> pull `divRepPullAt U i j ω` satisfies `IsDivRepClassify` for the chart morphism
> `Spec ω ≫ ChartMap i j`.

That is precisely the hypothesis `isCompatible_of_isDivRepClassify_divRepPullAt`
(`Picard/DivRepAffPullbackReduce.lean`) consumes, i.e. the DDR9-U ε-identity in clause
form.  So the two obligations the round-5 framing listed side by side —
`isDivRepClassify_pull` **and** `IsCompatible` — are **one** obligation, and this file
proves that:

* `AlgebraicGeometry.DivRepChartFamily.IsChartClause` — the named U2 interface.
* `AlgebraicGeometry.isDivRepClassify_divRepPullValue` — **the third field**: the glued
  pulled class satisfies the characterizing clause for the morphism it came from.
* `AlgebraicGeometry.divRepAffinePullback_ofChartClause` — **a producer of
  `DivRepAffinePullback` from `IsChartClause` alone**, hence (with
  `DivRepAffinePullback.representableBy`) of the divisor-representability endpoint.

**Why the clause is local on the base, which is the whole content.** `IsDivRepClassify F₀ v`
quantifies over tower tests `T` carrying a certified representative of `F₀`'s restriction
and a chart framing of its ε pair, and concludes an equality of morphisms out of `Spec T`.
Both the hypothesis data and the conclusion restrict along `T → T ⊗ …`; and a chart framing
over `T` together with the atlas factorization over the spanning family `f` gives, on each
`Localization.Away (f t)`-overlap, two chart presentations of the same morphism.  The
already-landed `pullback_chart_divClassifyClause_compat` is exactly that comparison, so the
`Scheme.Cover.hom_ext` chase is the same one `exists_isDivRepClassify` runs — this file
runs it against the *pulled* class rather than a classified one.

**What this does NOT do.** It produces no `IsChartClause`.  U2 — the ε-identity at the
universal point — is still unproved, and per the roadmap leaf it is gated on the G-4
certificate discharge (`ThetaGeneratorSeed.certifiedFamily` wants a global `IsCertified`
over the chart ring).  What changes is the *shape* of the remaining debt: a producer of the
divisor-representability endpoint now owes exactly one statement, stated in one place, with
no cover bookkeeping left around it.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Grassmannian Scheme

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftDivRepAffPullClause :
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
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
variable (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
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

/-! ## The named U2 interface -/

namespace DivRepChartFamily

/-- **The DDR9-U interface in clause form** (`informal/w4-ddr9-worksheet.md` §3.1 U2, as
consumed rather than as stated): each chart pull of the supplied family satisfies the
backward classifier's characterizing clause for its own chart morphism.

This is *verbatim* the hypothesis `isCompatible_of_isDivRepClassify_divRepPullAt` takes, so
naming it costs nothing and buys the observation this file is for: the same statement also
gives `isDivRepClassify_pull`, hence the entire `DivRepAffinePullback`. -/
def IsChartClause
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g) : Prop :=
  ∀ {S : Type u} [CommRing S] [Algebra k S]
    (i : (glueData k g r1).J) (j : (glueData k g r2).J)
    (omega : ChartRing i j →ₐ[k] S),
    IsDivRepClassify hpi g r1 r2 b1 b2
      (divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U i j omega)
      (Spec.map (CommRingCat.ofHom omega.toRingHom) ≫ ChartMap i j)

set_option maxHeartbeats 1600000 in
-- The `letI` re-topologization of the tower test as a `ChartRing`-algebra makes the
-- elaborator unify TWO algebra structures on `T` (through `omega`, and the ambient
-- `k`/`S`-tower) while `divRepPullAt` unfolds `mapAlgHom`; same defeq profile as
-- `divRepPullAt_awayMul_compat`, well past the default budget.
set_option linter.unusedSectionVars false in
/-- **The `ω`-quantifier of `IsChartClause` adds no strength**: it suffices to have the
clause at the *identity point* of every chart, which is exactly U2 as the worksheet states
it (`informal/w4-ddr9-worksheet.md` §3.1: `S = R_Z`, `ω = id`, `w = divCarveChartMk`).

`IsDivRepClassify` already quantifies over all `k`/`S`-tower tests, so base-changing the
chart point is free: retopologize a tower test `T` over `S` as a `ChartRing`-algebra through
`ω`, and a certified representative of `divRepPullAt U i j ω` over `T` *is* one of `U i j`
over `T`, because `divRepPullAt` is `mapAlgHom ω` and `mapAlgHom_comp` collapses the two
restrictions.  The framing is untouched, and the conclusion transports because
`algebraMap (ChartRing i j) T` factors as `(algebraMap S T).comp ω`.

So a producer owes the identity-point statement only, whose left-hand side is
`divUniversalFst` definitionally (`Picard/DivSchemeFamilyUniv.lean`).  Found by a
fresh-context review of this file (inbox `I-0561`), which correctly observed that the
interface as written advertises a *larger* debt than is owed.

**A NAME CORRECTION, review-ajcr r6.**  This paragraph used to say the identity-point
statement is "the one `divUniversalFamily` is built to satisfy".  There is no
`divUniversalFamily` anywhere: a workspace-wide grep over `MainProjects` and `SubProjects`
returns exactly one hit, the sentence itself, and `horizon search` returns only
differently-named declarations.  The prescription a lane reads here therefore named a
nonexistent witness for the debt it prices — and grep cannot distinguish that from a name
merely out of scope, which is why it survived.  The surviving claim is the one about
`divUniversalFst`, which does exist and is what the definitional identity is against.

Note the curve-properness/irreducibility instances are genuinely unused here: the collapse is
a base-change bookkeeping fact about the clause, with no curve geometry in it (the linter is
silenced rather than `omit`-ed, because the ambient curve instances of this section are
mutually referenced and cannot be dropped individually). -/
theorem IsChartClause.of_id
    {U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g}
    (hid : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      IsDivRepClassify hpi g r1 r2 b1 b2 (U i j) (ChartMap i j)) :
    IsChartClause (hpi := hpi) g r1 r2 b1 b2 U := by
  intro S _ _ i j omega T _ _ _ _ GT hGT i' j' w hw1 hw2
  -- read `T` as a `ChartRing i j`-algebra through `omega`
  letI algCT : Algebra (ChartRing i j) T :=
    ((IsScalarTower.toAlgHom k S T).comp omega).toRingHom.toAlgebra
  haveI towkCT : IsScalarTower k (ChartRing i j) T :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact (((IsScalarTower.toAlgHom k S T).comp omega).commutes x).symm)
  -- the same certified family represents the unpulled class over `T`
  have hGT' : (DivFam.mk GT).toZar = DivFamZar.mapAlg T g (U i j) := by
    rw [hGT, divRepPullAt, ← DivFamZar.mapAlgHom_eq_mapAlg
        ((IsScalarTower.toAlgHom k S T).comp omega) (fun _ => rfl) (U i j),
      DivFamZar.mapAlgHom_comp omega (IsScalarTower.toAlgHom k S T) (U i j),
      DivFamZar.mapAlgHom_eq_mapAlg (IsScalarTower.toAlgHom k S T) (fun _ => rfl)]
  -- and the chart morphism composes: `algebraMap (ChartRing i j) T = (algebraMap S T) ∘ omega`
  have hfac : Spec.map (CommRingCat.ofHom (algebraMap S T))
        ≫ Spec.map (CommRingCat.ofHom omega.toRingHom)
      = Spec.map (CommRingCat.ofHom (algebraMap (ChartRing i j) T)) := by
    rw [← Spec.map_comp]
    rfl
  have hmain := hid i j T GT hGT' i' j' w hw1 hw2
  rw [← Category.assoc] at hmain
  rw [← Category.assoc, ← Category.assoc, hfac]
  exact hmain

include hO hchi in
/-- The clause interface gives the compatibility the `pull` field is conditional on:
this is `isCompatible_of_isDivRepClassify_divRepPullAt` under its new name. -/
theorem IsChartClause.isCompatible
    {U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g}
    (hU : IsChartClause (hpi := hpi) g r1 r2 b1 b2 U) :
    IsCompatible (hpi := hpi) g r1 r2 b1 b2 U :=
  isCompatible_of_isDivRepClassify_divRepPullAt hpi g hO hchi r1 r2 b1 b2 U
    (fun i j omega => hU i j omega)

end DivRepChartFamily

/-! ## The clause is local on the base -/

set_option maxHeartbeats 1600000 in
-- A tower test is compared with each away carrier of the cover through
-- `TensorProduct S T (Localization.Away (f t))`; the window transports unfold
-- `divFamEps`/`DivFam.window` defeq, as in `pullback_chart_divClassifyClause_compat`.
set_option maxRecDepth 8000 in
include hO hchi in
/-- **`IsDivRepClassify` is local on the base** — the tool this file is really about, and
it mentions no chart family.  If a spanning family `f : Fin m → S` is such that every
restriction of `F₀` to `Localization.Away (f t)` is classified by the corresponding
restriction of `v`, then `F₀` is classified by `v`.

The clause quantifies over tower tests, so both its data and its conclusion restrict: given
a framing over `T`, compare with the `t`-th piece over
`TensorProduct S T (Localization.Away (f t))`, where the framing pushes along the left leg
(`map_window_frame_toSubmodule` at the identity tower — the `hβ` trick of
`pullback_chart_divClassifyClause_compat`) and the certified representative pushes with it.
`pullbackSpecIso` conjugates the two legs into that ring and `Scheme.Cover.hom_ext` over the
pulled-back cover globalizes.

This is what makes the ε-identity a *per-chart* obligation: the pulled class is only ever
known piecewise, and this lemma says knowing the clause piecewise is knowing it. -/
theorem pullback_isDivRepClassify_compat {S : Type u} [CommRing S] [Algebra k S]
    (F₀ : DivFamZar C S pi g)
    {v : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
        (b2.map (windowShiftEquiv hpi g).symm)}
    {T : Type u} [CommRing T] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (GT : CertifiedDivisorFamily C T pi g)
    (hGT : (DivFam.mk GT).toZar = DivFamZar.mapAlg T g F₀)
    {i : (glueData k g r1).J} {j : (glueData k g r2).J}
    (w : PairChartRing k g r1 g r2 i j →ₐ[k] T)
    (hw1 : (Module.Grassmannian.map w (pairTautFst k g r1 r2 i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange T b1.equivFun.toLinearMap)
          (divFamEps hpi g (DivFam.mk GT)).1)
    (hw2 : (Module.Grassmannian.map w (pairTautSnd k g r1 r2 i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange T b2.equivFun.toLinearMap)
          (divFamEps hpi g (DivFam.mk GT)).2)
    {A : Type u} [CommRing A] [Algebra k A] [Algebra S A] [IsScalarTower k S A]
    (hA : IsDivRepClassify hpi g r1 r2 b1 b2
      (DivFamZar.mapAlg A g F₀)
      (Spec.map (CommRingCat.ofHom (algebraMap S A)) ≫ v)) :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S T)))
        (Spec.map (CommRingCat.ofHom (algebraMap S A)))
        ≫ Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r1 g r2 i j
      = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S T)))
          (Spec.map (CommRingCat.ofHom (algebraMap S A)))
          ≫ Spec.map (CommRingCat.ofHom (algebraMap S A))
          ≫ v ≫ divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
            (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
            (b2.map (windowShiftEquiv hpi g).symm) := by
  classical
  -- the overlap ring of the two tower tests
  letI algR : Algebra A (TensorProduct S T A) :=
    (Algebra.TensorProduct.includeRight (R := S) (A := T)
      (B := A)).toRingHom.toAlgebra
  haveI : IsScalarTower k S (TensorProduct S T A) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [Algebra.TensorProduct.algebraMap_def, Algebra.TensorProduct.algebraMap_def,
        RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq])
  haveI : IsScalarTower S T (TensorProduct S T A) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k T (TensorProduct S T A) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower S A (TensorProduct S T A) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra]
      exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)
  haveI : IsScalarTower k A (TensorProduct S T A) :=
    isScalarTower_left_of_isScalarTower (R₀ := S)
  -- the certified representative over `T` pushes to the overlap, still a representative
  -- of the class restricted from `A`
  have hZ' : (DivFam.mk (GT.mapAlg (TensorProduct S T A) g)).toZar
      = DivFamZar.mapAlg (TensorProduct S T A) g (DivFamZar.mapAlg A g F₀) := by
    rw [← DivFam.mapAlg_mk, DivFam.toZar_mapAlg, hGT,
      DivFamZar.mapAlg_comp (R' := T) (R'' := TensorProduct S T A),
      DivFamZar.mapAlg_comp (R' := A) (R'' := TensorProduct S T A)]
  -- the framing pushes along the left leg (identity tower at `T`)
  have hβ : (IsScalarTower.toAlgHom k T (TensorProduct S T A)).toRingHom.comp
        (algebraMap T T)
      = algebraMap T (TensorProduct S T A) := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
    rfl
  have hy1 : (Module.Grassmannian.map w (pairTautFst k g r1 r2 i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange T b1.equivFun.toLinearMap)
          (divFamEps hpi g (DivFam.mapAlg T g (DivFam.mk GT))).1 :=
    hw1.trans (congrArg (fun F' => Submodule.map
      (LinearMap.baseChange T b1.equivFun.toLinearMap) (divFamEps hpi g F').1)
      (DivFam.mapAlg_id g (DivFam.mk GT)).symm)
  have hy2 : (Module.Grassmannian.map w (pairTautSnd k g r1 r2 i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange T b2.equivFun.toLinearMap)
          (divFamEps hpi g (DivFam.mapAlg T g (DivFam.mk GT))).2 :=
    hw2.trans (congrArg (fun F' => Submodule.map
      (LinearMap.baseChange T b2.equivFun.toLinearMap) (divFamEps hpi g F').2)
      (DivFam.mapAlg_id g (DivFam.mk GT)).symm)
  have hwB1 := map_window_frame_toSubmodule hpi g hO hchi (windowM_choice pi hpi g)
    (relThetaPairH1_windowM C pi hpi g) le_rfl b1 (DivFam.mk GT)
    (IsScalarTower.toAlgHom k T (TensorProduct S T A)) hβ
    (Module.Grassmannian.map w (pairTautFst k g r1 r2 i j)) hy1
  have hwB2 := map_window_frame_toSubmodule hpi g hO hchi
    (windowM_choice pi hpi g + windowS_choice pi hpi g)
    (relThetaPairH1_windowMS C pi hpi g) (Nat.le_add_right _ _) b2 (DivFam.mk GT)
    (IsScalarTower.toAlgHom k T (TensorProduct S T A)) hβ
    (Module.Grassmannian.map w (pairTautSnd k g r1 r2 i j)) hy2
  have hcomp1 : Module.Grassmannian.map
        ((IsScalarTower.toAlgHom k T (TensorProduct S T A)).comp w)
        (pairTautFst k g r1 r2 i j)
      = Module.Grassmannian.map (IsScalarTower.toAlgHom k T (TensorProduct S T A))
          (Module.Grassmannian.map w (pairTautFst k g r1 r2 i j)) :=
    Module.Grassmannian.map_comp (f := w)
      (g := IsScalarTower.toAlgHom k T (TensorProduct S T A))
      (N := pairTautFst k g r1 r2 i j)
  have hcomp2 : Module.Grassmannian.map
        ((IsScalarTower.toAlgHom k T (TensorProduct S T A)).comp w)
        (pairTautSnd k g r1 r2 i j)
      = Module.Grassmannian.map (IsScalarTower.toAlgHom k T (TensorProduct S T A))
          (Module.Grassmannian.map w (pairTautSnd k g r1 r2 i j)) :=
    Module.Grassmannian.map_comp (f := w)
      (g := IsScalarTower.toAlgHom k T (TensorProduct S T A))
      (N := pairTautSnd k g r1 r2 i j)
  have hmk : DivFam.mapAlg (TensorProduct S T A) g (DivFam.mk GT)
      = DivFam.mk (GT.mapAlg (TensorProduct S T A) g) :=
    DivFam.mapAlg_mk _ _ _
  have hext1 : (Module.Grassmannian.map
        ((IsScalarTower.toAlgHom k T (TensorProduct S T A)).comp w)
        (pairTautFst k g r1 r2 i j)).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (TensorProduct S T A) b1.equivFun.toLinearMap)
          (divFamEps hpi g (DivFam.mk (GT.mapAlg (TensorProduct S T A) g))).1 :=
    (congrArg Module.Grassmannian.toSubmodule hcomp1).trans (hwB1.trans
      (congrArg (fun F' => Submodule.map
        (LinearMap.baseChange (TensorProduct S T A) b1.equivFun.toLinearMap)
        (divFamEps hpi g F').1) hmk))
  have hext2 : (Module.Grassmannian.map
        ((IsScalarTower.toAlgHom k T (TensorProduct S T A)).comp w)
        (pairTautSnd k g r1 r2 i j)).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (TensorProduct S T A) b2.equivFun.toLinearMap)
          (divFamEps hpi g (DivFam.mk (GT.mapAlg (TensorProduct S T A) g))).2 :=
    (congrArg Module.Grassmannian.toSubmodule hcomp2).trans (hwB2.trans
      (congrArg (fun F' => Submodule.map
        (LinearMap.baseChange (TensorProduct S T A) b2.equivFun.toLinearMap)
        (divFamEps hpi g F').2) hmk))
  -- the clause over `A`, applied at the overlap tower
  have hmain := hA (TensorProduct S T A) (GT.mapAlg (TensorProduct S T A) g) hZ' i j
    ((IsScalarTower.toAlgHom k T (TensorProduct S T A)).comp w) hext1 hext2
  have hL : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        T →+* TensorProduct S T A))
        ≫ Spec.map (CommRingCat.ofHom w.toRingHom)
      = Spec.map (CommRingCat.ofHom
          (((IsScalarTower.toAlgHom k T (TensorProduct S T A)).comp w).toRingHom)) := by
    rw [← Spec.map_comp]
    rfl
  -- the right leg's structure map IS `includeRight`, by the `letI` algebra
  have hRalg : (algebraMap A (TensorProduct S T A))
      = (Algebra.TensorProduct.includeRight (R := S) (A := T) (B := A)).toRingHom :=
    RingHom.algebraMap_toAlgebra _
  rw [hRalg] at hmain
  rw [← cancel_epi (pullbackSpecIso S T A).inv, pullbackSpecIso_inv_fst_assoc,
    pullbackSpecIso_inv_snd_assoc, ← Category.assoc, hL]
  exact hmain.symm

set_option maxHeartbeats 800000 in
-- The `Scheme.Cover.hom_ext` chase runs over the factorization cover pulled back along
-- `Spec T ⟶ Spec S`, so each piece re-elaborates the `pullback₁` carrier against
-- `pullback_isDivRepClassify_compat`'s tensor overlap; past the default budget, and cheaper
-- than the per-piece lemma above because the window transports are already discharged there.
include hO hchi in
/-- **`IsDivRepClassify` is local on the base** — the tool this file is really about, and it
mentions no chart family.  If every restriction of `F₀` to `Localization.Away (f t)` along a
spanning family is classified by the corresponding restriction of `v`, then `F₀` is
classified by `v`.

`Scheme.Cover.hom_ext` over the factorization cover pulled back along `Spec T ⟶ Spec S`,
with `pullback_isDivRepClassify_compat` on each piece.  This is what makes the ε-identity a
*per-chart* obligation: the pulled class is only ever known piecewise, and this says knowing
the clause piecewise is knowing it. -/
theorem isDivRepClassify_of_forall_away {S : Type u} [CommRing S] [Algebra k S]
    (F₀ : DivFamZar C S pi g)
    (v : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
        (b2.map (windowShiftEquiv hpi g).symm))
    {m : ℕ} (f : Fin m → S) (hspan : Ideal.span (Set.range f) = ⊤)
    (hloc : ∀ t : Fin m,
      IsDivRepClassify hpi g r1 r2 b1 b2
        (DivFamZar.mapAlg (Localization.Away (f t)) g F₀)
        (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f t)))) ≫ v)) :
    IsDivRepClassify hpi g r1 r2 b1 b2 F₀ v := by
  classical
  intro T _ _ _ _ GT hGT i j w hw1 hw2
  refine Scheme.Cover.hom_ext
    ((Scheme.affineOpenCoverOfSpanRangeEqTop
      (R := CommRingCat.of S) f hspan).openCover.pullback₁
      (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    _ _ fun t => ?_
  change pullback.fst _ _ ≫ _ = pullback.fst _ _ ≫ _
  rw [← Category.assoc, pullback.condition, Category.assoc]
  exact (pullback_isDivRepClassify_compat hpi g hO hchi r1 r2 b1 b2 F₀ GT hGT w hw1 hw2
    (A := Localization.Away (f t)) (hloc t)).symm

/-! ## The third field -/

section Clause

set_option maxHeartbeats 1600000 in
-- The clause is checked at a tower test against the away carriers of the factorization;
-- the defeq budget is the one of `exists_isDivRepClassify`, whose cover chase this mirrors.
include hO hchi in
/-- **`isDivRepClassify_pull`, the ε-gated field, from the per-chart clause**: the glued
pulled class of `v` satisfies the backward classifier's characterizing clause for `v`.

The proof is the cover chase of `exists_isDivRepClassify` run against the *pulled* class.
Fix a tower test `T` with a certified representative `G` of the restriction of
`divRepPullValue v` and a chart framing of `ε (DivFam.mk G)`.  Over each piece
`Localization.Away (f t)` of the atlas factorization of `v`, the value restricts to the
chart pull `divRepPullAt U (ci t) (cj t) (cw t)` (`mapAlgHom_divRepPullValue`), and the
chart clause supplies `IsDivRepClassify` for the chart morphism there.  So both the framing
over `T` and the chart data over `Localization.Away (f t)` classify the same restricted
class, and `pullback_chart_divClassifyClause_compat` identifies their morphisms on the
overlap; `Scheme.Cover.hom_ext` over the pulled-back factorization cover globalizes. -/
theorem isDivRepClassify_divRepPullValue
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hU : DivRepChartFamily.IsChartClause (hpi := hpi) g r1 r2 b1 b2 U)
    (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver) :
    IsDivRepClassify hpi g r1 r2 b1 b2
      (divRepPullValue hpi g r1 r2 b1 b2 U
        (DivRepChartFamily.IsChartClause.isCompatible hpi g hO hchi r1 r2 b1 b2 hU)
        S v) v.left := by
  classical
  obtain ⟨m, f, hspan, ci, cj, cw, hcw, hF⟩ :=
    divRepPullValue_spec hpi g r1 r2 b1 b2 U
      (DivRepChartFamily.IsChartClause.isCompatible hpi g hO hchi r1 r2 b1 b2 hU) S v
  refine isDivRepClassify_of_forall_away hpi g hO hchi r1 r2 b1 b2 _ _ f hspan fun t => ?_
  -- on the `t`-th piece the value IS the chart pull, and the chart morphism IS the
  -- restriction of `v.left` — so the chart clause is literally the piecewise statement.
  -- The face-change bridge moves `hF`'s explicit `mapAlgHom` onto the instance face.
  rw [← DivFamZar.mapAlgHom_eq_mapAlg
      (IsScalarTower.toAlgHom k S (Localization.Away (f t))) (fun _ => rfl), hF t,
    ← hcw t]
  exact hU (ci t) (cj t) (cw t)

/-! ## The producer: `IsChartClause` is the whole remaining debt -/

include hO hchi in
/-- **A `DivRepAffinePullback` from `IsChartClause` alone** — the point of this file.

`DivRepAffinePullback.ofPull` asks for three fields; all three are now available from the
single per-chart ε clause:

* `pull` is `divRepPullValue`, whose conditionality on `IsCompatible` is discharged by
  `IsChartClause.isCompatible`;
* `isDivRepClassify_pull` is `isDivRepClassify_divRepPullValue`;
* `pull_naturality` is `divRepPullValue_naturality` (ε-free);

and `pull_classify` is derived by the separation theorem.  Composing with
`DivRepAffinePullback.representableBy` (`Picard/DivRepGlobalClassify.lean`) this turns the
DDR9-U ε-identity into the *only* remaining input of divisor representability. -/
noncomputable def divRepAffinePullback_ofChartClause
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hU : DivRepChartFamily.IsChartClause (hpi := hpi) g r1 r2 b1 b2 U) :
    DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2 :=
  DivRepAffinePullback.ofPull hpi g hO hchi r1 r2 b1 b2
    (fun S _ _ => divRepPullValue hpi g r1 r2 b1 b2 U
      (DivRepChartFamily.IsChartClause.isCompatible hpi g hO hchi r1 r2 b1 b2 hU) S)
    (fun S _ _ v =>
      isDivRepClassify_divRepPullValue hpi g hO hchi r1 r2 b1 b2 U hU S v)
    (fun phi v => divRepPullValue_naturality hpi g r1 r2 b1 b2 U
      (DivRepChartFamily.IsChartClause.isCompatible hpi g hO hchi r1 r2 b1 b2 hU) phi v)

include hO hchi in
/-- **Divisor representability from the ε-identity**: `divFunctor C π g` is represented by
`divSchemeOver` as soon as some chart family satisfies the per-chart clause.

This is the DDR-9 endpoint with its remaining hypothesis made explicit and singular.  Read
the honest form: nothing here *proves* U2, and per roadmap `…divrep.u2` the clause is still
gated on the G-4 certificate discharge.  What is now true is that a producer of U2 needs to
supply nothing else. -/
noncomputable def divFunctor_representableBy_of_chartClause
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hU : DivRepChartFamily.IsChartClause (hpi := hpi) g r1 r2 b1 b2 U) :
    (divFunctor C pi g).RepresentableBy DivOver :=
  DivRepAffinePullback.representableBy (hpi := hpi) (g := g) (hO := hO) (hchi := hchi)
    (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
    (divRepAffinePullback_ofChartClause hpi g hO hchi r1 r2 b1 b2 U hU)

include hO hchi in
/-- **Divisor representability from U2 exactly as the worksheet states it** — the form a
producer should quote.

`informal/w4-ddr9-worksheet.md` §3.1 states U2 at the *identity point* of each chart
(`S = R_Z`, `ω = id`), and `IsChartClause.of_id` shows the `ω`-quantifier of the interface
adds nothing.  So the whole divisor-representability chain rests on: *for each pair chart,
the supplied chart class is classified by that chart's own morphism to `DivScheme`*.

Nothing below the endpoint is left to do.  What is left is that statement, which is U2, and
which is gated on the G-4 certificate discharge. -/
noncomputable def divFunctor_representableBy_of_id
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hid : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      IsDivRepClassify hpi g r1 r2 b1 b2 (U i j) (ChartMap i j)) :
    (divFunctor C pi g).RepresentableBy DivOver :=
  divFunctor_representableBy_of_chartClause hpi g hO hchi r1 r2 b1 b2 U
    (DivRepChartFamily.IsChartClause.of_id hpi g r1 r2 b1 b2 hid)

end Clause

end Curve

end AlgebraicGeometry
