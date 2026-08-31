/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheaf
import AlgebraicJacobian.Picard.PresentationDivisor
import AlgebraicJacobian.Picard.OpenImmersionUnits

/-!
# W6-full: the glued sheaf of a meromorphic presentation is the divisor sheaf (DAT-3 (c))

For the curve bundle `X` — integral, smooth of relative dimension one and quasi-compact
over a field `K` — and a meromorphic presentation `P` (`Scheme.MeromorphicPresentation`:
a pointed cover, a unit cocycle on it, and trivializing elements `P.elem x ∈ K(X)ˣ` whose
ratios are the germs at `η` of the cocycle values), this file identifies the m-chart
cocycle-glued sheaf of `P` with the divisor sheaf of its presentation divisor — the core
of the W6-full seam (`informal/w4-datum-worksheet.md` §3.1(c), spec FROZEN there):

* `Scheme.MeromorphicPresentation.isGluingCocycle` — the presentation's cocycle satisfies
  the gluing cocycle law (`unit_self` from the ratio property at `(x, x)` through the
  injective germ embedding; `mul_res` is the landed `unitsEvInf_trans`);
* `Scheme.MeromorphicPresentation.gluedSheaf` — the glued sheaf of `K`-modules of the
  presentation, `AlgebraicGeometry.gluedSheaf` on `P.cover.opens` with multipliers the
  pair values of `P.cocycle`;
* `Scheme.MeromorphicPresentation.gluedDivisorSheafIso` —
  **`glued(P) ≅ 𝒪(presentationDivisor P)`**: over a nonempty open the components send a
  matching family `s` to the rational function `(P.elem x)⁻¹ · germ_η (s x)` (independent
  of the piece `x` — `gluedVal_eq_elem_inv_mul`); the inverse trivializes a bounded
  rational function `h` chartwise as the section with germ `P.elem x · h` (the
  `mulEquivDivisorSheaf` mechanism, chartwise, through the `𝒪(0) ≅ 𝒪_X` gluing engine
  `exists_section_germ_eq`).

## The pole-bound bridge

At a closed point `z` of a piece, the divisor bound of `presentationDivisor K P` is the
coerced order `ordZ_z (P.elem z)` (`divisorBound_presentationDivisor`), and every piece
element `P.elem x` with `z` in its piece has the same order (`ordZ_elem_eq`). So
multiplication by `P.elem x` converts the pole bound `D` into the pole bound `0` exactly,
and integrality glues to honest sections by the landed `𝒪(0) ≅ 𝒪_X` machinery.

The `Subsingleton`/`h⁰`/FLV consequences (the `hfib` sheaf-form discharge and the rank
export) are assembled in `AlgebraicJacobian.RiemannRoch.W6Full`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

namespace Scheme

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

omit [IsIntegral X] in
/-- Germs at a point commute with `resHom`: the germ of a restricted section is the germ
of the section. -/
private lemma germ_resHom {V W : X.Opens} (h : W ≤ V) (x : X) (hx : x ∈ W)
    (t : Γ(X, V)) :
    (X.presheaf.germ W x hx).hom (X.resHom h t) =
      (X.presheaf.germ V x (h hx)).hom t :=
  X.presheaf.germ_res_apply (homOfLE h) x hx t

/-- Multiplication by a fixed rational function, as a `K`-linear endomorphism of the
function field (with the `Scheme.functionFieldOverModule` structure). -/
private noncomputable def mulFunctionField (q : X.functionField) :
    X.functionField →ₗ[K] X.functionField where
  toFun s := q * s
  map_add' := mul_add q
  map_smul' r s := by
    rw [RingHom.id_apply, functionFieldOverModule_smul_def,
      functionFieldOverModule_smul_def, mul_left_comm]

namespace MeromorphicPresentation

variable (P : X.MeromorphicPresentation)

/-! ## The gluing cocycle law of the presentation -/

/-- **The presentation's cocycle satisfies the gluing cocycle law**: `g x x = 1` because
its germ at `η` is `elem x / elem x = 1` and the germ embedding is injective; the triple
identity is the landed `unitsEvInf_trans`. -/
theorem isGluingCocycle :
    Scheme.IsGluingCocycle P.cover.opens (fun x y => unitsEvInf P.cocycle x y) where
  unit_self x := by
    have h1 : germGenericUnits (P.cover.genericPoint_mem_inf x x)
        (unitsEvInf P.cocycle x x) = 1 := by
      rw [← P.ratio x x, mul_inv_cancel]
    have h2 : unitsEvInf P.cocycle x x = 1 :=
      germGenericUnits_injective (P.cover.genericPoint_mem_inf x x)
        (by rw [h1, map_one])
    exact congrArg Units.val h2
  mul_res i j l := congrArg Units.val (unitsEvInf_trans P.cocycle i j l)

/-- **The glued sheaf of a meromorphic presentation**: the m-chart cocycle-glued sheaf
of `K`-modules on the pieces of `P.cover`, with multipliers the pair values of
`P.cocycle` (w4-1's constructor on the presentation, per the frozen W6-full spec). -/
noncomputable def gluedSheaf :
    Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} K) :=
  AlgebraicGeometry.gluedSheaf K P.cover.opens (fun x y => unitsEvInf P.cocycle x y)

/-! ## The value of a glued section -/

section Val

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- Sections of the glued sheaf over an empty open form a subsingleton (each component
ring does). -/
lemma gluedSubmodule_subsingleton_of_empty {W : X.Opens} (hW : ¬ (W : Set X).Nonempty) :
    Subsingleton
      ↥(gluedSubmodule K P.cover.opens (fun x y => unitsEvInf P.cocycle x y) W) := by
  have hbot : W = ⊥ := by
    apply Opens.ext
    rw [Set.not_nonempty_iff_eq_empty.mp hW, Opens.coe_bot]
  refine ⟨fun a b => Subtype.ext (funext fun x => ?_)⟩
  haveI : Subsingleton Γ(X, W ⊓ P.cover.opens x) :=
    X.subsingleton_sections_of_le_bot (inf_le_left.trans hbot.le)
  exact Subsingleton.elim _ _

/-- **The underlying rational function of a glued section** over a nonempty open: the
germ at `η` of the component at the canonical index (the generic point itself), divided
by the trivializing element there. Piece-independent by `gluedVal_eq_elem_inv_mul`. -/
noncomputable def gluedVal {W : X.Opens} (hηW : genericPoint X ∈ W)
    (s : ↥(gluedSubmodule K P.cover.opens (fun x y => unitsEvInf P.cocycle x y) W)) :
    X.functionField :=
  (((P.elem (genericPoint X))⁻¹ : X.functionFieldˣ) : X.functionField) *
    (X.presheaf.germ (W ⊓ P.cover.opens (genericPoint X)) (genericPoint X)
      ⟨hηW, P.cover.genericPoint_mem_opens (genericPoint X)⟩).hom
      (s.val (genericPoint X))

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- **Piece-independence of the value**: the value of a glued section can be read off
any piece, `gluedVal s = (P.elem x)⁻¹ · germ_η (s x)` — the matching relation and the
ratio property cancel the transition unit. -/
lemma gluedVal_eq_elem_inv_mul (x : X) {W : X.Opens} (hηW : genericPoint X ∈ W)
    (s : ↥(gluedSubmodule K P.cover.opens (fun x y => unitsEvInf P.cocycle x y) W)) :
    gluedVal K P hηW s =
      (((P.elem x)⁻¹ : X.functionFieldˣ) : X.functionField) *
        (X.presheaf.germ (W ⊓ P.cover.opens x) (genericPoint X)
          ⟨hηW, P.cover.genericPoint_mem_opens x⟩).hom (s.val x) := by
  have hηT : genericPoint X ∈
      W ⊓ P.cover.opens x ⊓ P.cover.opens (genericPoint X) :=
    ⟨⟨hηW, P.cover.genericPoint_mem_opens x⟩,
      P.cover.genericPoint_mem_opens (genericPoint X)⟩
  -- the matching relation at `(x, η)`, in beta-reduced form
  have hmatch : X.resHom (inf_le_left : W ⊓ P.cover.opens x ⊓
        P.cover.opens (genericPoint X) ≤ W ⊓ P.cover.opens x) (s.val x) =
      X.resHom (gluedInclCoc P.cover.opens W x (genericPoint X))
          ((unitsEvInf P.cocycle x (genericPoint X) :
            Γ(X, P.cover.opens x ⊓ P.cover.opens (genericPoint X)))) *
        X.resHom (gluedInclSnd P.cover.opens W x (genericPoint X))
          (s.val (genericPoint X)) :=
    s.property x (genericPoint X)
  -- push it to the generic point
  have hg := congrArg
    (X.presheaf.germ (W ⊓ P.cover.opens x ⊓ P.cover.opens (genericPoint X))
      (genericPoint X) hηT).hom hmatch
  rw [map_mul, germ_resHom, germ_resHom, germ_resHom] at hg
  -- the ratio property, at the level of values
  have hrg : (X.presheaf.germ (P.cover.opens x ⊓ P.cover.opens (genericPoint X))
      (genericPoint X) (P.cover.genericPoint_mem_inf x (genericPoint X))).hom
        ((unitsEvInf P.cocycle x (genericPoint X) :
          Γ(X, P.cover.opens x ⊓ P.cover.opens (genericPoint X)))) =
      ((P.elem x : X.functionField)) *
        (((P.elem (genericPoint X))⁻¹ : X.functionFieldˣ) : X.functionField) := by
    have hr := congrArg Units.val (P.ratio x (genericPoint X))
    rw [Units.val_mul, germGenericUnits_val] at hr
    exact hr.symm
  -- germ (s x) = elem x · gluedVal s
  have key : (X.presheaf.germ (W ⊓ P.cover.opens x) (genericPoint X)
      ⟨hηW, P.cover.genericPoint_mem_opens x⟩).hom (s.val x) =
      (P.elem x : X.functionField) * gluedVal K P hηW s := by
    rw [gluedVal]
    calc (X.presheaf.germ (W ⊓ P.cover.opens x) (genericPoint X)
          ⟨hηW, P.cover.genericPoint_mem_opens x⟩).hom (s.val x)
        = (X.presheaf.germ (P.cover.opens x ⊓ P.cover.opens (genericPoint X))
            (genericPoint X) (P.cover.genericPoint_mem_inf x (genericPoint X))).hom
              ((unitsEvInf P.cocycle x (genericPoint X) :
                Γ(X, P.cover.opens x ⊓ P.cover.opens (genericPoint X)))) *
          (X.presheaf.germ (W ⊓ P.cover.opens (genericPoint X)) (genericPoint X)
            ⟨hηW, P.cover.genericPoint_mem_opens (genericPoint X)⟩).hom
            (s.val (genericPoint X)) := hg
      _ = (P.elem x : X.functionField) *
            ((((P.elem (genericPoint X))⁻¹ : X.functionFieldˣ) : X.functionField) *
              (X.presheaf.germ (W ⊓ P.cover.opens (genericPoint X)) (genericPoint X)
                ⟨hηW, P.cover.genericPoint_mem_opens (genericPoint X)⟩).hom
                (s.val (genericPoint X))) := by
          rw [hrg, mul_assoc]
  rw [key, ← mul_assoc, Units.inv_mul, one_mul]

/-- **The divisor bound of the presentation divisor is the coerced order of the local
trivializing element**: `divisorBound (presentationDivisor P) z = ordZ_z (P.elem z)` in
`ℤᵐ⁰`. -/
lemma divisorBound_presentationDivisor {z : X} (hz : z ≠ genericPoint X) :
    divisorBound (presentationDivisor K P) hz =
      ((Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz (P.elem z) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
  rw [divisorBound]
  congr 1

/-- The order of the inverse trivializing element is the divisor bound: multiplication
by `(P.elem z)⁻¹` realizes the pole allowance of `presentationDivisor P` at `z`
exactly. -/
lemma ord_elem_inv (z : X) (hz : z ≠ genericPoint X) :
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
        ((((P.elem z)⁻¹ : X.functionFieldˣ) : X.functionField)) =
      divisorBound (presentationDivisor K P) hz := by
  rw [divisorBound_presentationDivisor K P hz,
    ← coe_inv_ordZ K ((P.elem z)⁻¹) hz, map_inv, inv_inv]

/-- **The pole bound of the value**: the value of a glued section lies in
`𝒪(presentationDivisor P)(W)`. At a closed point `z ∈ W`, read the value off the piece
indexed by `z` itself: the germ factor is integral there and the `(P.elem z)⁻¹` factor
is exactly the allowed pole. -/
lemma gluedVal_mem {W : X.Opens} (hηW : genericPoint X ∈ W)
    (s : ↥(gluedSubmodule K P.cover.opens (fun x y => unitsEvInf P.cocycle x y) W)) :
    gluedVal K P hηW s ∈ divisorSections K (presentationDivisor K P) W := by
  rw [mem_divisorSections_of_nonempty K ⟨genericPoint X, hηW⟩]
  intro z hz hzW
  have hηWz : genericPoint X ∈ W ⊓ P.cover.opens z :=
    ⟨hηW, P.cover.genericPoint_mem_opens z⟩
  have hzWz : z ∈ W ⊓ P.cover.opens z := ⟨hzW, P.cover.mem_opens z⟩
  rw [gluedVal_eq_elem_inv_mul K P z hηW s, map_mul]
  have hgerm : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
      ((X.presheaf.germ (W ⊓ P.cover.opens z) (genericPoint X) hηWz).hom
        (s.val z)) ≤ 1 := by
    rw [germ_generic_eq_algebraMap_germ hηWz hzWz (s.val z)]
    exact ord_algebraMap_stalk_le_one K hz _
  calc Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
        ((((P.elem z)⁻¹ : X.functionFieldˣ) : X.functionField)) *
        Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
          ((X.presheaf.germ (W ⊓ P.cover.opens z) (genericPoint X) hηWz).hom
            (s.val z))
      ≤ Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
          ((((P.elem z)⁻¹ : X.functionFieldˣ) : X.functionField)) * 1 :=
        mul_le_mul_right hgerm _
    _ = divisorBound (presentationDivisor K P) hz := by
        rw [mul_one, ord_elem_inv]

end Val

/-! ## The section-wise map and its bijectivity -/

section App

/-- **The section-wise `K`-linear map `glued(P)(W) → 𝒪(presentationDivisor P)(W)`** for
a nonempty open: `s ↦ (P.elem η)⁻¹ · germ_η (s η)`. -/
noncomputable def gluedToDivisorApp {W : X.Opens} (hηW : genericPoint X ∈ W) :
    ↥(gluedSubmodule K P.cover.opens (fun x y => unitsEvInf P.cocycle x y) W) →ₗ[K]
      ↥(divisorSections K (presentationDivisor K P) W) :=
  LinearMap.codRestrict (divisorSections K (presentationDivisor K P) W)
    ((mulFunctionField K (((P.elem (genericPoint X))⁻¹ : X.functionFieldˣ) :
        X.functionField)).comp
      ((germGenericLinear K
          (⟨hηW, P.cover.genericPoint_mem_opens (genericPoint X)⟩ :
            genericPoint X ∈ W ⊓ P.cover.opens (genericPoint X))).comp
        ((LinearMap.proj (genericPoint X)).comp
          (gluedSubmodule K P.cover.opens
            (fun x y => unitsEvInf P.cocycle x y) W).subtype)))
    (fun s => gluedVal_mem K P hηW s)

lemma gluedToDivisorApp_coe {W : X.Opens} (hηW : genericPoint X ∈ W)
    (s : ↥(gluedSubmodule K P.cover.opens (fun x y => unitsEvInf P.cocycle x y) W)) :
    ((gluedToDivisorApp K P hηW s :
      divisorSections K (presentationDivisor K P) W) : X.functionField) =
      gluedVal K P hηW s :=
  rfl

/-- The section-wise map is injective: the value determines every component germ (by
piece-independence), and germs at `η` determine sections on the integral `X`. -/
lemma gluedToDivisorApp_injective {W : X.Opens} (hηW : genericPoint X ∈ W) :
    Function.Injective (gluedToDivisorApp K P hηW) := by
  intro a b hab
  have hval : gluedVal K P hηW a = gluedVal K P hηW b := by
    have := congrArg
      (fun t : ↥(divisorSections K (presentationDivisor K P) W) =>
        (t : X.functionField)) hab
    rwa [gluedToDivisorApp_coe, gluedToDivisorApp_coe] at this
  refine Subtype.ext (funext fun x => ?_)
  have ha := gluedVal_eq_elem_inv_mul K P x hηW a
  have hb := gluedVal_eq_elem_inv_mul K P x hηW b
  rw [hval, hb] at ha
  have hgerm := mul_left_cancel₀ (Units.ne_zero ((P.elem x)⁻¹)) ha.symm
  exact germ_injective_of_isIntegral X (genericPoint X)
    (⟨hηW, P.cover.genericPoint_mem_opens x⟩ :
      genericPoint X ∈ W ⊓ P.cover.opens x) hgerm

/-- **Chartwise trivialization of a bounded rational function**: for `h` with poles
bounded by `presentationDivisor P` on `W`, the product `P.elem x · h` is integral on
`W ⊓ P.cover.opens x` — the pole of `h` at each closed point `z` of the piece is
cancelled by the zero of `P.elem x`, whose order there equals that of `P.elem z`
(piece-independence). -/
lemma elem_mul_mem_divisorSections_zero {W : X.Opens} (hηW : genericPoint X ∈ W)
    {h : X.functionField}
    (hh : h ∈ divisorSections K (presentationDivisor K P) W) (x : X) :
    (P.elem x : X.functionField) * h ∈
      divisorSections K (0 : X.CurveDivisor) (W ⊓ P.cover.opens x) := by
  have hηWx : genericPoint X ∈ W ⊓ P.cover.opens x :=
    ⟨hηW, P.cover.genericPoint_mem_opens x⟩
  rw [mem_divisorSections_of_nonempty K ⟨genericPoint X, hηWx⟩]
  intro z hz hzWx
  rw [divisorBound_zero, map_mul]
  have hordx : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz (P.elem x : X.functionField)
      = (((Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz (P.elem z))⁻¹ :
          Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [← coe_inv_ordZ K (P.elem x) hz, P.ordZ_elem_eq K hz hzWx.2]
  have hordh : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz h ≤
      ((Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz (P.elem z) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [← divisorBound_presentationDivisor K P hz]
    exact (mem_divisorSections_of_nonempty K ⟨genericPoint X, hηW⟩).mp hh z hz hzWx.1
  calc Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz (P.elem x : X.functionField) *
        Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz h
      ≤ Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz (P.elem x : X.functionField) *
          ((Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz (P.elem z) :
            Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
        mul_le_mul_right hordh _
    _ = 1 := by
        rw [hordx, ← WithZero.coe_mul, inv_mul_cancel, WithZero.coe_one]

/-- The section-wise map is surjective: a bounded rational function is trivialized
chartwise (`P.elem x · h` is integral on the piece, hence a genuine section by the
`𝒪(0) ≅ 𝒪_X` gluing engine), and the resulting family matches through the cocycle. -/
lemma gluedToDivisorApp_surjective {W : X.Opens} (hηW : genericPoint X ∈ W) :
    Function.Surjective (gluedToDivisorApp K P hηW) := by
  intro t
  have hηWx : ∀ x : X, genericPoint X ∈ W ⊓ P.cover.opens x := fun x =>
    ⟨hηW, P.cover.genericPoint_mem_opens x⟩
  -- chartwise regular representatives
  choose s hs using fun x : X =>
    exists_section_germ_eq K (U := W ⊓ P.cover.opens x) (hηWx x)
      (elem_mul_mem_divisorSections_zero K P hηW t.property x)
  -- the family matches through the cocycle
  have hmem : s ∈ gluedSubmodule K P.cover.opens
      (fun x y => unitsEvInf P.cocycle x y) W := by
    intro x y
    change X.resHom (inf_le_left : W ⊓ P.cover.opens x ⊓ P.cover.opens y ≤
          W ⊓ P.cover.opens x) (s x) =
        X.resHom (gluedInclCoc P.cover.opens W x y)
            ((unitsEvInf P.cocycle x y : Γ(X, P.cover.opens x ⊓ P.cover.opens y))) *
          X.resHom (gluedInclSnd P.cover.opens W x y) (s y)
    have hηT : genericPoint X ∈ W ⊓ P.cover.opens x ⊓ P.cover.opens y :=
      ⟨⟨hηW, P.cover.genericPoint_mem_opens x⟩, P.cover.genericPoint_mem_opens y⟩
    apply germ_injective_of_isIntegral X (genericPoint X) hηT
    rw [map_mul, germ_resHom, germ_resHom, germ_resHom, hs x, hs y]
    have hrg : (X.presheaf.germ (P.cover.opens x ⊓ P.cover.opens y) (genericPoint X)
        (P.cover.genericPoint_mem_inf x y)).hom
          ((unitsEvInf P.cocycle x y : Γ(X, P.cover.opens x ⊓ P.cover.opens y))) =
        ((P.elem x : X.functionField)) *
          (((P.elem y)⁻¹ : X.functionFieldˣ) : X.functionField) := by
      have hr := congrArg Units.val (P.ratio x y)
      rw [Units.val_mul, germGenericUnits_val] at hr
      exact hr.symm
    rw [hrg, mul_assoc, ← mul_assoc (((P.elem y)⁻¹ : X.functionFieldˣ) :
      X.functionField), Units.inv_mul, one_mul]
  refine ⟨⟨s, hmem⟩, ?_⟩
  apply Subtype.ext
  rw [gluedToDivisorApp_coe, gluedVal]
  rw [show (⟨s, hmem⟩ : ↥(gluedSubmodule K P.cover.opens
      (fun x y => unitsEvInf P.cocycle x y) W)).val (genericPoint X) =
    s (genericPoint X) from rfl]
  rw [hs (genericPoint X), ← mul_assoc, Units.inv_mul, one_mul]

end App

/-! ## The presheaf morphism and the isomorphism of sheaves -/

section Iso

open Classical in
/-- The section-wise map for all opens: the value map on nonempty opens, the zero map
into the terminal sections on the empty open. -/
noncomputable def gluedToDivisorPresheafApp (W : X.Opens) :
    ↥(gluedSubmodule K P.cover.opens (fun x y => unitsEvInf P.cocycle x y) W) →ₗ[K]
      ↥(divisorSections K (presentationDivisor K P) W) :=
  if hW : (W : Set X).Nonempty then
    gluedToDivisorApp K P (genericPoint_mem_of_nonempty hW)
  else 0

lemma gluedToDivisorPresheafApp_of_nonempty {W : X.Opens} (hW : (W : Set X).Nonempty) :
    gluedToDivisorPresheafApp K P W =
      gluedToDivisorApp K P (genericPoint_mem_of_nonempty hW) :=
  dif_pos hW

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- Restriction does not move the value of a glued section. -/
lemma gluedVal_res {W' W : X.Opens} (h : W' ≤ W) (hηW' : genericPoint X ∈ W')
    (s : ↥(gluedSubmodule K P.cover.opens (fun x y => unitsEvInf P.cocycle x y) W)) :
    gluedVal K P hηW'
        (gluedRes K P.cover.opens (fun x y => unitsEvInf P.cocycle x y) h s) =
      gluedVal K P (h hηW') s := by
  rw [gluedVal, gluedVal]
  congr 1
  rw [gluedRes_coe K P.cover.opens (fun x y => unitsEvInf P.cocycle x y) h s
    (genericPoint X), germ_resHom]

/-- **The presheaf morphism `glued(P) → 𝒪(presentationDivisor P)`** of `K`-modules. -/
noncomputable def gluedToDivisorPresheaf :
    gluedPresheaf K P.cover.opens (fun x y => unitsEvInf P.cocycle x y) ⟶
      divisorPresheaf K (presentationDivisor K P) where
  app W := ModuleCat.ofHom (gluedToDivisorPresheafApp K P W.unop)
  naturality {A B} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    by_cases hB : (B.unop : Set X).Nonempty
    · have hA : (A.unop : Set X).Nonempty := hB.mono (leOfHom i.unop)
      apply Subtype.ext
      change ((gluedToDivisorPresheafApp K P B.unop
          (gluedRes K P.cover.opens (fun x y => unitsEvInf P.cocycle x y)
            (leOfHom i.unop) s) :
          divisorSections K (presentationDivisor K P) B.unop) : X.functionField) =
        ((divisorSectionsRes K (presentationDivisor K P) (leOfHom i.unop)
          (gluedToDivisorPresheafApp K P A.unop s) :
          divisorSections K (presentationDivisor K P) B.unop) : X.functionField)
      rw [divisorSectionsRes_coe K (leOfHom i.unop) hB,
        gluedToDivisorPresheafApp_of_nonempty K P hB,
        gluedToDivisorPresheafApp_of_nonempty K P hA, gluedToDivisorApp_coe,
        gluedToDivisorApp_coe, gluedVal_res]
    · haveI := divisorPresheaf_obj_subsingleton K
        (D := presentationDivisor K P) (W := B.unop) hB
      exact Subsingleton.elim _ _

/-- The section-wise map is bijective on every open: an isomorphism on nonempty opens,
a map of subsingletons on the empty open. -/
lemma gluedToDivisorPresheafApp_bijective (W : X.Opens) :
    Function.Bijective (gluedToDivisorPresheafApp K P W) := by
  by_cases hW : (W : Set X).Nonempty
  · rw [gluedToDivisorPresheafApp_of_nonempty K P hW]
    exact ⟨gluedToDivisorApp_injective K P _, gluedToDivisorApp_surjective K P _⟩
  · haveI := gluedSubmodule_subsingleton_of_empty K P (W := W) hW
    haveI := divisorSections_subsingleton_of_empty K
      (D := presentationDivisor K P) (U := W) hW
    exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

lemma gluedToDivisorPresheaf_app_isIso (W : (X.Opens)ᵒᵖ) :
    IsIso ((gluedToDivisorPresheaf K P).app W) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact gluedToDivisorPresheafApp_bijective K P W.unop

/-- The presheaf isomorphism `glued(P) ≅ 𝒪(presentationDivisor P)`. -/
noncomputable def gluedDivisorPresheafIso :
    gluedPresheaf K P.cover.opens (fun x y => unitsEvInf P.cocycle x y) ≅
      divisorPresheaf K (presentationDivisor K P) :=
  NatIso.ofComponents
    (fun W => by
      haveI := gluedToDivisorPresheaf_app_isIso K P W
      exact asIso ((gluedToDivisorPresheaf K P).app W))
    (fun i => (gluedToDivisorPresheaf K P).naturality i)

/-- **W6-full, the core isomorphism (DAT-3 (c), frozen spec §3.1)**: the glued sheaf of
a meromorphic presentation is the divisor sheaf of its presentation divisor, as sheaves
of `K`-modules — over a nonempty open, a matching family `s` corresponds to the
rational function `(P.elem x)⁻¹ · germ_η (s x)` (any piece `x`), with inverse the
chartwise trivialization `h ↦ (P.elem x · h)_x` (the `mulEquivDivisorSheaf` mechanism,
chartwise). -/
noncomputable def gluedDivisorSheafIso :
    P.gluedSheaf K ≅ X.divisorSheaf K (presentationDivisor K P) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (gluedDivisorPresheafIso K P)

end Iso

end MeromorphicPresentation

end Scheme

end AlgebraicGeometry
