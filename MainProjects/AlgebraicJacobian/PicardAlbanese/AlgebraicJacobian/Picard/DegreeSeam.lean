/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0Functor

/-!
# The degree seam (DAT-4): `degAt` of a cocycle-presented class at a field point

For the challenge curve `C` over `k`, a plus class on an affine test `Spec A` is
`picEtAffineEquiv`-represented in `PicEtAff C A`; a *cocycle-presented* class is the
`unit`/`relPicMk` image of an honest Čech Picard class `L` on `C_A`.  This file computes
the degree of such a class at a field point of `A` — the point where the campaign spends
degree-zero-ness (worksheet `informal/w4-datum-worksheet.md` §3.3).

A field point of the affine test `overSpec k A` is `Over.overSpecMap φ` for a `k`-algebra
map `φ : A →ₐ[k] K` into a field extension `K = κ(p)`.  The degree of the class at this
point collapses:

* restriction along `Over.overSpecMap φ` through `picEtAffineEquiv_naturality`
  (`Picard/PicEtMap.lean`) and `PicEtAff.mapAlg_unit` sends the plus class to the unit of
  the *fibre* class `relPicAlgMap C φ z`;
* `PicEtAff.degAff_unit` (`Picard/DegreeZero.lean`) reads the relative degree;
* `relPicDeg_relPicMk` (`RiemannRoch/RelPicDegree.lean`) reads `classDeg`.

## Main results

* `AlgebraicGeometry.degAt_of_affineEquiv_eq_unit` — the seam, unit form:
  `degAt lam (Over.overSpecMap φ) = relPicDeg K (relPicAlgMap C φ z)`.
* `AlgebraicGeometry.degAt_of_affineEquiv_eq_unit_relPicMk` — **the keystone**: `degAt`
  of the plus class at the field point equals `classDeg κ(p)` of the fibre Čech class.
* `AlgebraicGeometry.degAt_of_affineEquiv_eq_unit_baseChange` /
  `AlgebraicGeometry.degAt_eq_classDeg_of_affineEquiv_eq_unit_baseChange` — the
  base-field-constancy corollary: a class pulled back from `overSpec k k` has the same
  `degAt` at every field point, equal to `relPicDeg k` / `classDeg k` of the base class
  (E-iv-alg descended).  This is the mechanism DAT-5 consumes for `degAt θ_T = d₁`.
* `AlgebraicGeometry.degAt_pow` and `AlgebraicGeometry.degAt_pic0_mul_pow` — the fibre
  degree of `lam · θ ^ m` for `lam ∈ pic0Subgroup` is `m · degAt θ` on the nose.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The degree seam at a field point -/

section Keystone

variable {A : Type u} [CommRing A] [Algebra k A] {K : Type u} [Field K] [Algebra k K]

/-- **The degree seam, unit form**: if a class `lam` on the affine test `overSpec k A`
collapses under the affine comparison to the plus unit of a relative Picard class `z`,
then its degree at the field point `Over.overSpecMap φ` (for `φ : A →ₐ[k] K`) is the
relative degree over `K` of the fibre class `relPicAlgMap C φ z`.  Route:
`picEtAffineEquiv_naturality` collapses the restriction to `PicEtAff.mapAlg`, which is
natural on units (`PicEtAff.mapAlg_unit`), and `PicEtAff.degAff_unit` reads `relPicDeg`. -/
theorem degAt_of_affineEquiv_eq_unit (φ : A →ₐ[k] K) (lam : picEt C (overSpec k A))
    (z : relPic C (overSpec k A))
    (h : picEtAffineEquiv C A lam = PicEtAff.unit C A z) :
    degAt lam (Over.overSpecMap φ) = relPicDeg K (relPicAlgMap C φ z) := by
  change PicEtAff.degAff K (picEtAffineEquiv C K (picEtMap C (Over.overSpecMap φ) lam))
      = relPicDeg K (relPicAlgMap C φ z)
  rw [picEtAffineEquiv_naturality, h, PicEtAff.mapAlg_unit, PicEtAff.degAff_unit]

/-- **The keystone of the degree seam** (worksheet §3.3): for a cocycle-presented class
`lam` on the affine test `overSpec k A` — one whose affine collapse is the plus unit of
`relPicMk C (overSpec k A) L` for a Čech Picard class `L` on `C_A` — and a field point
`Over.overSpecMap φ` (`φ : A →ₐ[k] K`), the degree at the point equals `classDeg K` of the
fibre Čech class, the pullback of `L` along the point.  This is where the strata and
coverage arguments spend degree-zero-ness. -/
theorem degAt_of_affineEquiv_eq_unit_relPicMk (φ : A →ₐ[k] K)
    (lam : picEt C (overSpec k A)) (L : (C ⊗ overSpec k A).left.CechPic)
    (h : picEtAffineEquiv C A lam = PicEtAff.unit C A (relPicMk C (overSpec k A) L)) :
    degAt lam (Over.overSpecMap φ)
      = classDeg K (Scheme.CechPic.map ((C ◁ Over.overSpecMap φ).left) L) := by
  rw [degAt_of_affineEquiv_eq_unit φ lam _ h,
    show relPicAlgMap C φ (relPicMk C (overSpec k A) L)
        = relPicMk C (overSpec k K)
            (Scheme.CechPic.map ((C ◁ Over.overSpecMap φ).left) L)
      from relPicMap_mk C (Over.overSpecMap φ) L,
    relPicDeg_relPicMk]

end Keystone

/-! ## Base-field constancy: the pulled-back Θ-family -/

section BaseChange

variable {A : Type u} [CommRing A] [Algebra k A] {K : Type u} [Field K] [Algebra k K]

/-- **Base-field constancy, relative form**: a class on `overSpec k A` whose affine
collapse is the plus unit of the pullback (`relPicAlgMap C (Algebra.ofId k A)`) of a base
class `w : relPic C (overSpec k k)` has degree `relPicDeg k w` at *every* field point,
independent of the point.  The pullback commutes with the field point by
`relPicAlgMap_comp`, and E-iv-alg descended (`relPicDeg_relPicAlgMap`) reads off the base
degree. -/
theorem degAt_of_affineEquiv_eq_unit_baseChange (φ : A →ₐ[k] K)
    (lam : picEt C (overSpec k A)) (w : relPic C (overSpec k k))
    (h : picEtAffineEquiv C A lam
          = PicEtAff.unit C A (relPicAlgMap C (Algebra.ofId k A) w)) :
    degAt lam (Over.overSpecMap φ) = relPicDeg k w := by
  rw [degAt_of_affineEquiv_eq_unit φ lam _ h, ← relPicAlgMap_comp, relPicDeg_relPicAlgMap]

/-- **Base-field constancy, `classDeg` form** (the DAT-5 mechanism for `degAt θ_T = d₁`):
a class pulled back from a Čech class `L₀` on `C_k` has degree `classDeg k L₀` at every
field point — a base-field-invariant constant.  When `L₀` is the Θ-class, this constant
is `d₁ := classDeg k Θ` (identified with `deg (fiberWeilDivisor π) > 0` by DAT-0b). -/
theorem degAt_eq_classDeg_of_affineEquiv_eq_unit_baseChange (φ : A →ₐ[k] K)
    (lam : picEt C (overSpec k A)) (L₀ : (C ⊗ overSpec k k).left.CechPic)
    (h : picEtAffineEquiv C A lam
          = PicEtAff.unit C A (relPicAlgMap C (Algebra.ofId k A)
              (relPicMk C (overSpec k k) L₀))) :
    degAt lam (Over.overSpecMap φ) = classDeg k L₀ := by
  rw [degAt_of_affineEquiv_eq_unit_baseChange φ lam _ h, relPicDeg_relPicMk]

end BaseChange

/-! ## The fibre degree of `lam · θ ^ m` -/

section Pic0

variable {T : Over (Spec (.of k))} {K : Type u} [Field K] [Algebra k K]

/-- The degree at a field point of a power is the multiple of the degree. -/
theorem degAt_pow (θ : picEt C T) (m : ℕ) (t : overSpec k K ⟶ T) :
    degAt (θ ^ m) t = (m : ℤ) * degAt θ t := by
  induction m with
  | zero => rw [pow_zero, degAt_one, Nat.cast_zero, zero_mul]
  | succ n ih => rw [pow_succ, degAt_mul, ih]; push_cast; ring

/-- **The fibre degree of `lam · θ ^ m`** (worksheet §3.3): for a degree-zero class
`lam ∈ pic0Subgroup C T` and any class `θ`, the degree of `lam · θ ^ m` at a field point
is `m · degAt θ` on the nose — `lam` contributes nothing.  The FLV threshold input and the
rank-normalization consumer. -/
theorem degAt_pic0_mul_pow (lam : picEt C T) (hlam : lam ∈ pic0Subgroup C T)
    (θ : picEt C T) (m : ℕ) (t : overSpec k K ⟶ T) :
    degAt (lam * θ ^ m) t = (m : ℤ) * degAt θ t := by
  rw [degAt_mul, mem_pic0Subgroup_iff.mp hlam K t, degAt_pow, zero_add]

end Pic0

end

end AlgebraicGeometry
