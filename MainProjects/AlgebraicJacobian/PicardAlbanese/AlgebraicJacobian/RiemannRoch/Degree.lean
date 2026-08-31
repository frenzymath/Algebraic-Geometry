/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorClassCompat
import AlgebraicJacobian.RiemannRoch.ChiCurve

/-!
# The degree homomorphism on the Čech Picard group

For the curve bundle `X` (integral, smooth of relative dimension one and quasi-compact over
a field `K`, with finite `H⁰`/`H¹` of the structure sheaf — the two instance hypotheses
through which properness enters), this file builds the **degree homomorphism** on the Čech
Picard group and records the E-i..E-iii interface of the degree lane
(`informal/degree-pic0-recon.md` §3 G-D3, `informal/deg-d2-meromorphic-worksheet.md` W5).

The anchored class map `CurveDivisor.picClass K : X.CurveDivisor → X.CechPic` of the
meromorphic bridge (`Picard/DivisorClassMeromorphic.lean`) is surjective, with fibres the
principal divisors. The degree of a Weil divisor is class-invariant: two divisors of equal
class differ by a principal divisor (extraction `(X)`, `CurveDivisor.exists_divOf_of_picClass_eq`)
and principal divisors have degree zero (`deg_divOf`, the χ-ledger), so `deg` descends to a
homomorphism on classes.

## Main declarations

* `AlgebraicGeometry.classDeg` — the degree homomorphism `Additive X.CechPic →+ ℤ`:
  `classDeg 𝒪(D) = deg D` for any Weil divisor `D`. The carrier `Additive X.CechPic →+ ℤ`
  is chosen so that a *value* `classDeg L` is a genuine integer: `X.CechPic` is a `CommGroup`
  (line-bundle tensor) and the degrees form the additive group `ℤ`, so the idiomatic
  packaging of "a group homomorphism from the multiplicative Picard group to the additive
  group `ℤ`" is an `AddMonoidHom` out of `Additive X.CechPic`. Because `Additive X.CechPic`
  is definitionally `X.CechPic`, the interface statements below read literally, and
  `map_zero`/`map_add`/`map_neg`/`map_zsmul` come for free from the bundled hom.
* `AlgebraicGeometry.classDeg_picClass` (**E-i**, normalization): `classDeg 𝒪(D) = deg D`,
  the definitional anchor, for *every* Weil divisor `D`.
* `AlgebraicGeometry.classDeg_mul` (**E-ii**, homomorphism):
  `classDeg (L · L') = classDeg L + classDeg L'`.
* `AlgebraicGeometry.chi_divisorSheaf_classDeg` (**E-iii**, χ-connection):
  `χ(𝒪(D)) = χ(𝒪_X) + classDeg 𝒪(D)`.
* `AlgebraicGeometry.chi_divisorSheaf_eq_of_picClass_eq`: the Euler characteristic of a class
  is well-defined — `𝒪(D) = 𝒪(D') → χ(𝒪(D)) = χ(𝒪(D'))` — via the multiplication
  isomorphism `mulEquivDivisorSheaf` and `chi_congr` (no finiteness needed).
* `AlgebraicGeometry.classDeg_divisorClass`: the deg-D1 divisor class map has the same degree,
  `classDeg (divisorClass K D) = deg D`, through the collapse `divisorClass_eq_picClass`.
* `AlgebraicGeometry.chi_divisorSheaf_classDeg_curve`: the curve form
  `χ(𝒪(D)) = 1 − genus C + classDeg 𝒪(D)` on the challenge curve.

The recon's E-i pushforward-rank reading (`classDeg 𝒪(D) = dim_K Γ(𝒪_D)` for *effective*
`D`, the Dedekind colength of the structure sheaf of the subscheme `D`) is a separate
statement about global sections of `𝒪_D`; it is *not* this brick's definitional anchor
(`classDeg 𝒪(D) = deg D`) and is deferred to a later node.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

/-! ## χ of a class is well-defined (no finiteness hypotheses) -/

omit [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- **The Euler characteristic of a Čech Picard class is well-defined**: Weil divisors of
equal class have the same `χ(𝒪(D))`. If `𝒪(D) = 𝒪(D')` then `D − D' = div g` for a rational
function `g` (extraction `(X)`), and multiplication by `g` is an isomorphism of divisor
sheaves `𝒪(D) ≅ 𝒪(D − div g) = 𝒪(D')` (`mulEquivDivisorSheaf`), so the Euler
characteristics agree by `chi_congr`. Needs no finiteness hypotheses. -/
theorem chi_divisorSheaf_eq_of_picClass_eq {D D' : X.CurveDivisor}
    (h : CurveDivisor.picClass K D = CurveDivisor.picClass K D') :
    Sheaf.chi (X.divisorSheaf K D) = Sheaf.chi (X.divisorSheaf K D') := by
  obtain ⟨g, hg⟩ := CurveDivisor.exists_divOf_of_picClass_eq K h
  have hD' : D - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g = D' := by
    rw [← hg]; abel
  have hiso := mulEquivDivisorSheaf K g D
  rw [hD'] at hiso
  exact Sheaf.chi_congr hiso

/-! ## Well-definedness of the degree -/

/-- **Well-definedness of the degree**: Weil divisors of equal Čech Picard class have equal
degree. The class difference is a principal divisor `div g` (extraction `(X)`), and principal
divisors have degree zero (`deg_divOf`, the χ-ledger). -/
theorem deg_eq_deg_of_picClass_eq {D D' : X.CurveDivisor}
    (h : CurveDivisor.picClass K D = CurveDivisor.picClass K D') :
    CurveDivisor.deg K D = CurveDivisor.deg K D' := by
  obtain ⟨g, hg⟩ := CurveDivisor.exists_divOf_of_picClass_eq K h
  have hzero : CurveDivisor.deg K (D - D') = 0 := by
    rw [hg]; exact deg_divOf K g
  have hsub : CurveDivisor.deg K (D - D')
      = CurveDivisor.deg K D - CurveDivisor.deg K D' := by
    rw [sub_eq_add_neg, CurveDivisor.deg_add, CurveDivisor.deg_neg, ← sub_eq_add_neg]
  omega

/-! ## The underlying degree function -/

/-- The underlying function of the degree homomorphism: the degree of any Weil divisor
realizing the class (`CurveDivisor.exists_picClass_eq`). Well-defined by
`deg_eq_deg_of_picClass_eq`; bundled as `classDeg`. -/
private noncomputable def classDegFun (L : X.CechPic) : ℤ :=
  CurveDivisor.deg K (CurveDivisor.exists_picClass_eq K L).choose

omit [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- The chosen divisor realizes the class it was picked for. -/
private theorem picClass_classDegFun_choose (L : X.CechPic) :
    CurveDivisor.picClass K (CurveDivisor.exists_picClass_eq K L).choose = L :=
  (CurveDivisor.exists_picClass_eq K L).choose_spec

/-- The degree function evaluates a divisor's own class to its degree. -/
private theorem classDegFun_picClass (D : X.CurveDivisor) :
    classDegFun K (CurveDivisor.picClass K D) = CurveDivisor.deg K D :=
  deg_eq_deg_of_picClass_eq K
    (picClass_classDegFun_choose K (CurveDivisor.picClass K D))

/-- The degree function vanishes on the trivial class. -/
private theorem classDegFun_one : classDegFun K (1 : X.CechPic) = 0 := by
  rw [← CurveDivisor.picClass_zero K, classDegFun_picClass, CurveDivisor.deg_zero]

/-- The degree function turns the Picard product into a sum. -/
private theorem classDegFun_mul (L L' : X.CechPic) :
    classDegFun K (L * L') = classDegFun K L + classDegFun K L' := by
  obtain ⟨D, rfl⟩ := CurveDivisor.exists_picClass_eq K L
  obtain ⟨D', rfl⟩ := CurveDivisor.exists_picClass_eq K L'
  rw [← CurveDivisor.picClass_add, classDegFun_picClass, classDegFun_picClass,
    classDegFun_picClass, CurveDivisor.deg_add]

/-! ## The degree homomorphism -/

/-- **The degree homomorphism on the Čech Picard group.** For the curve bundle `X`, the
degree of a Weil divisor descends to a group homomorphism `classDeg K : Additive X.CechPic →+ ℤ`
on Picard classes: `classDeg K 𝒪(D) = deg K D`. Well-defined because equal classes differ by
a principal divisor and principal divisors have degree zero (`deg_eq_deg_of_picClass_eq`).

The value `classDeg K L` is a genuine integer (`Additive X.CechPic` is definitionally
`X.CechPic`), so E-i (`classDeg_picClass`) and E-ii (`classDeg_mul`) read as literal integer
equalities. The full `AddMonoidHom` API (`map_zero`, `map_add`, `map_neg`, `map_zsmul`) is
available on `classDeg K`. -/
noncomputable def classDeg : Additive X.CechPic →+ ℤ where
  toFun L := classDegFun K L
  map_zero' := classDegFun_one K
  map_add' L L' := classDegFun_mul K L L'

/-- **(E-i) Normalization** (the definitional anchor): the degree of the class `𝒪(D)` of a
Weil divisor `D` is `deg D`, for *every* `D`. -/
theorem classDeg_picClass (D : X.CurveDivisor) :
    classDeg K (CurveDivisor.picClass K D) = CurveDivisor.deg K D :=
  classDegFun_picClass K D

/-- **(E-ii) Homomorphism property**: the degree of a product of Picard classes is the sum of
the degrees, `classDeg (L · L') = classDeg L + classDeg L'`. Immediate from `map_add` of the
bundled `classDeg`; stated on the multiplicative Picard product for direct use. -/
theorem classDeg_mul (L L' : X.CechPic) :
    classDeg K (L * L') = classDeg K L + classDeg K L' :=
  classDegFun_mul K L L'

/-- The degree of the trivial class is zero. -/
@[simp]
theorem classDeg_one : classDeg K (1 : X.CechPic) = 0 :=
  classDegFun_one K

/-- The degree of an inverse class is the negation of the degree. -/
theorem classDeg_inv (L : X.CechPic) : classDeg K (L⁻¹ : X.CechPic) = -classDeg K L := by
  have h := classDeg_mul K L (L⁻¹ : X.CechPic)
  rw [mul_inv_cancel, classDeg_one] at h
  omega

/-! ## The χ-connection -/

/-- **(E-iii) The χ-connection**: the Euler characteristic of the class `𝒪(D)` is the Euler
characteristic of the structure sheaf plus the degree of the class,
`χ(𝒪(D)) = χ(𝒪_X) + classDeg 𝒪(D)`. A restatement of the landed χ-ledger `chi_divisorSheaf`
through the E-i normalization `classDeg_picClass`. -/
theorem chi_divisorSheaf_classDeg (D : X.CurveDivisor) :
    Sheaf.chi (X.divisorSheaf K D)
      = Sheaf.chi (X.moduleKSheaf K) + classDeg K (CurveDivisor.picClass K D) := by
  rw [classDeg_picClass]
  exact chi_divisorSheaf K D

/-! ## Compatibility with the deg-D1 divisor class map -/

/-- **Compatibility with `divisorClass`**: the deg-D1 divisor class map has the same degree,
`classDeg (divisorClass K D) = deg D`, via the collapse `divisorClass_eq_picClass`. -/
theorem classDeg_divisorClass (D : X.CurveDivisor) :
    classDeg K (divisorClass K D) = CurveDivisor.deg K D := by
  rw [divisorClass_eq_picClass, classDeg_picClass]

end AlgebraicGeometry

/-! ## The curve layer -/

namespace AlgebraicGeometry

open Scheme

section Curve

variable {k : Type u} [Field k]

/-- **The degree homomorphism on the challenge curve** (Riemann–Roch-lite, class form): for
every Weil divisor `D` on the smooth proper geometrically-irreducible curve `C`, the Euler
characteristic of `𝒪(D)` is `χ(𝒪(D)) = 1 − genus C + classDeg 𝒪(D)`. The structure-sheaf
finiteness hypotheses of the conditional ledger are discharged on the curve, so this carries
no finiteness side conditions. -/
theorem chi_divisorSheaf_classDeg_curve (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (D : C.left.CurveDivisor) :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
    haveI : QuasiCompact (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (QuasiCompact C.hom)
    haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
      moduleFinite_hModule_zero C
    haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
      moduleFinite_hModule_one C
    Sheaf.chi (C.left.divisorSheaf k D)
      = 1 - genus C + classDeg k (CurveDivisor.picClass k D) := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (QuasiCompact C.hom)
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    moduleFinite_hModule_zero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    moduleFinite_hModule_one C
  rw [classDeg_picClass]
  exact chi_divisorSheaf_curve C D

end Curve

end AlgebraicGeometry
