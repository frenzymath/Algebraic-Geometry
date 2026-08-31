/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0VanishingRigidityReduction

/-!
# FIELD-POINT RIGIDITY IS A STATEMENT ABOUT TEST ALGEBRAS

`Picard/Pic0VanishingRigidityReduction.lean` proved that at `genus C = 0` the `pic⁰` vanishing
`hvan` — the hypothesis both live routes to a `rep` producer pass through — is **equivalent** to
field-point rigidity of `picEt`:

  `hrig`: a `picEt C T` class restricting to `1` at every field point of `T` is `1`.

`hrig` still quantifies over all test *objects*.  This file removes that quantifier: it is
enough to have the statement at affine tests, in the plus-class spelling

  `hrigAff`: a `PicEtAff C A` class with `PicEtAff.mapAlg C φ q = 1` for every `φ : A →ₐ[k] K`
  into a field is `1`,

and the reduction is `rigidity_of_rigidityAff` below — with its converse
`rigidityAff_of_rigidity`, so the two are the **same** hypothesis
(`rigidity_iff_rigidityAff`).  Composed with the equivalence of the previous file,
`subsingleton_pic0Subgroup_of_rigidityAff` derives the vanishing at **every** test object from a
statement in which no scheme, no open and no morphism of schemes occurs — only commutative
`k`-algebras and algebra maps into fields.

## The mechanism

Two independent halves, and neither is a quantifier trick.

**The componentwise half** is the same observation that makes `subsingleton_picEt_of_affine`
one line: `picEt C T` is a subgroup of the *product* of the `PicEtAff C Γ(T.left, U)` over the
affine opens `U` of `T.left`, so `picEt.ext` reduces `lam = 1` to `lam.1 U = 1` at each `U`.

**The field-point half is the content**, and it runs the other way: `hrigAff` at
`A := Γ(T.left, U)` needs the hypothesis at every algebra map `φ : Γ(T.left, U) →ₐ[k] K`, and
what `hrig`'s hypothesis supplies are field points of `T`.  The bridge is the *composite*

  `Over.overSpecMap φ ≫ Over.fromSpecAffine T U : overSpec k K ⟶ T`,

a genuine field point of `T`, together with three coherences: `picEtMap_comp` splits the
restriction; `picEtAffineEquiv_naturality` turns the outer leg into `PicEtAff.mapAlg C φ`; and
`picEtMapVal_eq_mapAlg` identifies the inner leg's value at the *top* affine open of
`overSpec k Γ(T.left, U)` with `mapAlg` of `Over.appLEAlgHom` applied to `lam.1 U` — legitimate
because `⊤ ≤ fromSpec ⁻¹ᵁ U` (`IsAffineOpen.fromSpec_preimage_self`,
`top_le_preimage_fromSpecAffine` here).

What is left is the bookkeeping identity `fromSpecAffine_ΓTop_comp_appLEAlgHom`:
`Γ`-`Spec` transport composed with the `appLE` of `fromSpec` is the identity on
`Γ(T.left, U)`.  That is `IsAffineOpen.fromSpec_app_of_le` at `le_rfl` plus
`ΓSpecIso.inv_hom_id`, and it is worth its own name because it is the only place where the
`Spec`-`Γ` adjunction enters — a consumer relating an evaluation of `picEt` to a restriction
along `fromSpecAffine` will need it again.

## What this does NOT do

* **It does not prove `hrigAff`, at any curve.**  The statement remains without a producer; what
  changes is that the surviving obligation is now spelled entirely in commutative algebra.  Per
  `I-1650` this is a **statability** gain, not a shrinking of the obligation — the imported
  equivalence one layer down is between two spellings of one hypothesis.
* **The bookkeeping is not what carries the headline.**  Recorded because an audit (`I-1652`)
  measured it: `subsingleton_pic0Subgroup_of_rigidityAff` also follows from the *pre-session*
  `Pic0VanishingAffineReduction` + `Pic0VanishingFieldTest` pair, bypassing
  `top_le_preimage_fromSpecAffine`, `fromSpecAffine_ΓTop_comp_appLEAlgHom` and
  `picEtMapVal_eq_mapAlg` entirely.  What those three buy is the **general-`T`** form of
  `rigidity_of_rigidityAff` (and hence `rigidity_iff_rigidityAff`), which the affine-only route
  does not give.  That is a real generality gain and it is not the vanishing.
* It says nothing at positive genus; the genus hypothesis enters only through the imported
  equivalence, not through anything in this file.

## Main declarations

* `AlgebraicGeometry.top_le_preimage_fromSpecAffine` — the top affine open of
  `overSpec k Γ(T.left, U)` lies in the `fromSpecAffine`-preimage of `U`.
* `AlgebraicGeometry.fromSpecAffine_ΓTop_comp_appLEAlgHom` — the `Spec`-`Γ` bookkeeping
  identity, isolated.
* `AlgebraicGeometry.rigidity_of_rigidityAff` — **the reduction**: rigidity at test algebras
  gives rigidity at test objects.
* `AlgebraicGeometry.rigidityAff_of_rigidity` — the converse, and
  `AlgebraicGeometry.rigidity_iff_rigidityAff` the equivalence, so the affine form is not
  stronger.
* `AlgebraicGeometry.subsingleton_pic0Subgroup_of_rigidityAff` — the `pic⁰` vanishing at every
  test object from a purely ring-level hypothesis, at genus `0`.
* `AlgebraicGeometry.P1.subsingleton_pic0Subgroup_of_rigidityAff` — the same at `ℙ¹`, with the
  genus hypothesis discharged.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra

noncomputable section

/-! ## The two coherences the reduction needs -/

/-- The top affine open of `overSpec k Γ(T.left, U)` lies in the `fromSpecAffine`-preimage of
`U`: `IsAffineOpen.fromSpec_preimage_self` says that preimage is *all* of it. -/
theorem top_le_preimage_fromSpecAffine {k : Type u} [Field k] (T : Over (Spec (.of k)))
    (U : T.left.affineOpens) :
    (overSpecTopAffine Γ(T.left, U.1)).1 ≤ (Over.fromSpecAffine T U).left ⁻¹ᵁ U.1 :=
  le_of_eq U.2.fromSpec_preimage_self.symm

/-- **The `Spec`-`Γ` bookkeeping identity**: transporting a section of `U` along the `appLE` of
`fromSpec` into the top of `Spec Γ(T.left, U)` and back through `ΓSpecIso` returns it.

`IsAffineOpen.fromSpec_app_of_le` at `le_rfl` computes the `appLE` as
`ΓSpecIso.inv` up to restrictions along `⊤ ≤ ⊤`, which are identities; `ΓSpecIso.inv_hom_id`
finishes.  Isolated with a name because it is the only appearance of the adjunction in this
file's argument and any consumer comparing a `picEt` evaluation with a restriction along
`fromSpecAffine` needs it. -/
theorem fromSpecAffine_ΓTop_comp_appLEAlgHom {k : Type u} [Field k]
    (T : Over (Spec (.of k))) (U : T.left.affineOpens) :
    (Over.overSpecΓTopAlgEquiv k Γ(T.left, U.1)).toAlgHom.comp
        (Over.appLEAlgHom (Over.fromSpecAffine T U) U.1
          (overSpecTopAffine Γ(T.left, U.1)).1 (top_le_preimage_fromSpecAffine T U))
      = AlgHom.id k Γ(T.left, U.1) := by
  refine AlgHom.ext fun a => ?_
  show (Scheme.ΓSpecIso Γ(T.left, U.1)).hom
    (U.2.fromSpec.appLE U.1 ⊤ (top_le_preimage_fromSpecAffine T U) a) = a
  rw [Scheme.Hom.appLE]
  simp only [U.2.fromSpec_app_of_le U.1 le_rfl, CommRingCat.comp_apply, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso Γ(T.left, U.1)).inv_hom_id a

/-! ## The reduction -/

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
variable [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- **THE REDUCTION**: field-point rigidity at every test *algebra* gives it at every test
*object*.

Componentwise through `picEt.ext`; the field-point hypothesis at `Γ(T.left, U)` is supplied by
the composite field point `overSpecMap φ ≫ fromSpecAffine T U` of `T`, read through
`picEtMap_comp`, `picEtAffineEquiv_naturality`, `picEtMapVal_eq_mapAlg` and the bookkeeping
identity above.

`SmoothOfRelativeDimension 1` is unused (the linter reports it): this half is `picEt`
bookkeeping, and the geometry enters only through the imported genus-`0` equivalence. -/
theorem rigidity_of_rigidityAff
    (hA : ∀ (A : Type u) [CommRing A] [Algebra k A] (q : PicEtAff C A),
      (∀ (K : Type u) [Field K] [Algebra k K] (φ : A →ₐ[k] K),
        PicEtAff.mapAlg C φ q = 1) → q = 1)
    (T : Over (Spec (.of k))) (lam : picEt C T)
    (h : ∀ (K : Type u) [Field K] [Algebra k K] (t : overSpec k K ⟶ T),
      picEtMap C t lam = 1) : lam = 1 := by
  refine picEt.ext fun U => ?_
  rw [picEt.one_val]
  refine hA Γ(T.left, U.1) (lam.1 U) fun K _ _ φ => ?_
  -- the composite field point of `T`
  have h1 : picEtMap C (Over.overSpecMap φ ≫ Over.fromSpecAffine T U) lam = 1 :=
    h K (Over.overSpecMap φ ≫ Over.fromSpecAffine T U)
  rw [picEtMap_comp] at h1
  have h3 := congrArg (picEtAffineEquiv C K) h1
  rw [picEtAffineEquiv_naturality, map_one, picEtAffineEquiv_apply, picEtMap_val,
    picEtMapVal_eq_mapAlg C (Over.fromSpecAffine T U) lam
      (top_le_preimage_fromSpecAffine T U)] at h3
  refine Eq.trans ?_ h3
  refine congrArg (PicEtAff.mapAlg C φ) ?_
  set ψ := Over.appLEAlgHom (Over.fromSpecAffine T U) U.1
    (overSpecTopAffine Γ(T.left, U.1)).1 (top_le_preimage_fromSpecAffine T U) with hψ
  set e := (Over.overSpecΓTopAlgEquiv k Γ(T.left, U.1)).toAlgHom with he
  have hcomp : e.comp ψ = AlgHom.id k Γ(T.left, U.1) := by
    rw [he, hψ]
    exact fromSpecAffine_ΓTop_comp_appLEAlgHom T U
  calc lam.1 U = PicEtAff.mapAlg C (AlgHom.id k Γ(T.left, U.1)) (lam.1 U) :=
        (PicEtAff.mapAlg_id C (lam.1 U)).symm
    _ = PicEtAff.mapAlg C (e.comp ψ) (lam.1 U) := by rw [hcomp]
    _ = PicEtAff.mapAlg C e (PicEtAff.mapAlg C ψ (lam.1 U)) :=
        PicEtAff.mapAlg_comp C ψ e (lam.1 U)

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- **THE CONVERSE**, so the reduction is an equivalence and not a weakening.

Instantiate `hrig` at the affine test `overSpec k A` on `(picEtAffineEquiv C A).symm q`: every
field point of an affine test **is** `Spec` of an algebra map
(`exists_algHom_eq_of_overSpec_hom`), and `picEtAffineEquiv_naturality` turns the restriction
along it into `PicEtAff.mapAlg C φ`, which the hypothesis kills.

**Added after a fresh-context audit (`I-1649`) pointed out that this file's original "not the
converse" caveat understated its own result.**  The caveat was honest about direction — it did
not dress a weakening as a reduction — but it left an eight-line theorem unproved and left a
reader believing the affine form might be strictly stronger.  It is not: the two are the same
hypothesis. -/
theorem rigidityAff_of_rigidity
    (hrig : ∀ (T : Over (Spec (.of k))) (lam : picEt C T),
      (∀ (K : Type u) [Field K] [Algebra k K] (t : overSpec k K ⟶ T),
        picEtMap C t lam = 1) → lam = 1)
    (A : Type u) [CommRing A] [Algebra k A] (q : PicEtAff C A)
    (h : ∀ (K : Type u) [Field K] [Algebra k K] (φ : A →ₐ[k] K),
      PicEtAff.mapAlg C φ q = 1) : q = 1 := by
  have hlam : (picEtAffineEquiv C A).symm q = 1 := by
    refine hrig (overSpec k A) _ fun K _ _ t => ?_
    obtain ⟨φ, rfl⟩ := exists_algHom_eq_of_overSpec_hom (k := k) A K t
    refine (picEtAffineEquiv C K).injective ?_
    rw [picEtAffineEquiv_naturality, MulEquiv.apply_symm_apply, map_one, h K φ]
  rw [← MulEquiv.apply_symm_apply (picEtAffineEquiv C A) q, hlam, map_one]

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- **The equivalence**: field-point rigidity at test objects and at test algebras are the
same hypothesis. -/
theorem rigidity_iff_rigidityAff :
    (∀ (T : Over (Spec (.of k))) (lam : picEt C T),
        (∀ (K : Type u) [Field K] [Algebra k K] (t : overSpec k K ⟶ T),
          picEtMap C t lam = 1) → lam = 1)
      ↔ ∀ (A : Type u) [CommRing A] [Algebra k A] (q : PicEtAff C A),
          (∀ (K : Type u) [Field K] [Algebra k K] (φ : A →ₐ[k] K),
            PicEtAff.mapAlg C φ q = 1) → q = 1 :=
  ⟨fun hrig A _ _ q h => rigidityAff_of_rigidity C hrig A q h,
   fun hA => rigidity_of_rigidityAff C hA⟩

/-- **THE `pic⁰` VANISHING FROM A PURELY RING-LEVEL HYPOTHESIS**, at genus `0`.

The hypothesis mentions no scheme, no open and no morphism of schemes: only commutative
`k`-algebras `A`, plus classes of `A`, and algebra maps `A →ₐ[k] K` into fields.  Composite of
`rigidity_of_rigidityAff` with `subsingleton_pic0Subgroup_of_rigidity`. -/
theorem subsingleton_pic0Subgroup_of_rigidityAff (hg : genus C = 0)
    (hA : ∀ (A : Type u) [CommRing A] [Algebra k A] (q : PicEtAff C A),
      (∀ (K : Type u) [Field K] [Algebra k K] (φ : A →ₐ[k] K),
        PicEtAff.mapAlg C φ q = 1) → q = 1)
    (T : Over (Spec (.of k))) : Subsingleton (pic0Subgroup C T) :=
  subsingleton_pic0Subgroup_of_rigidity C hg (rigidity_of_rigidityAff C hA) T

/-- **`JacobianData` from the ring-level rigidity hypothesis**, at genus `0`.

`Pic0VanishingRoute.jacobianData_of_subsingleton` consumes the vanishing with no atlas, no
chart certificate, no coverage and no divisor representability, so this is the whole distance
from `hrigAff` to the goal object at a genus-`0` curve. -/
def jacobianData_of_rigidityAff (hg : genus C = 0)
    (hA : ∀ (A : Type u) [CommRing A] [Algebra k A] (q : PicEtAff C A),
      (∀ (K : Type u) [Field K] [Algebra k K] (φ : A →ₐ[k] K),
        PicEtAff.mapAlg C φ q = 1) → q = 1) : JacobianData C :=
  jacobianData_of_subsingleton C (subsingleton_pic0Subgroup_of_rigidityAff C hg hA)

end

/-- **The ring-level reduction at `ℙ¹`, with the genus hypothesis discharged.** -/
theorem P1.subsingleton_pic0Subgroup_of_rigidityAff (k' : Type u) [Field k']
    (hA : ∀ (A : Type u) [CommRing A] [Algebra k' A] (q : PicEtAff (P1.asOver k') A),
      (∀ (K : Type u) [Field K] [Algebra k' K] (φ : A →ₐ[k'] K),
        PicEtAff.mapAlg (P1.asOver k') φ q = 1) → q = 1)
    (T : Over (Spec (.of k'))) : Subsingleton (pic0Subgroup (P1.asOver k') T) :=
  AlgebraicGeometry.subsingleton_pic0Subgroup_of_rigidityAff (C := P1.asOver k')
    (P1.genus_asOver_eq_zero k') hA T

end AlgebraicGeometry
