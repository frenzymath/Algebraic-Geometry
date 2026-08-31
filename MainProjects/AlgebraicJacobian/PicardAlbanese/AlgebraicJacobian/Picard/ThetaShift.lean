/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DegreeSeam
import AlgebraicJacobian.RiemannRoch.ThetaDegree
import AlgebraicJacobian.Curve.BaseChangeInstances

/-!
# The shift ε⁺ (DAT-5): the Θ-family and the multiplication-by-θ isomorphism

For the challenge curve `C` over `k`, this file packages the twist normalization
`ε⁺` of the Wave-4 datum campaign (worksheet `informal/w4-datum-worksheet.md` §2.4,
§4 DAT-5).  Fix a Čech Picard class `L₀` on the base-changed curve
`C_k = (C ⊗ overSpec k k).left` — the pinned Θ-class (concretely `fiberTwist π 1`,
§ below).  The deliverables:

1. **The θ-family `thetaFamily C L₀ T : picEt C T`**, natural in the test object `T`:
   the plus class over `T` obtained by pulling the base plus class
   `PicEtAff.unit C k (relPicMk C (overSpec k k) L₀)` back along the canonical
   structure map `toBaseTest T : T ⟶ overSpec k k`.  Naturality is
   `thetaFamily_natural`: `θ` pulls back to `θ` under every test map, so DAT-C/DAT-B
   twist by `θ_T ^ m` uniformly.

2. **`degAt_thetaFamily`**: `degAt (thetaFamily C L₀ T) t = classDeg k L₀` at *every*
   field point `t`, via DAT-4's `degAt_eq_classDeg_of_affineEquiv_eq_unit_baseChange`
   (base-field-invariant).  With `L₀ = thetaCechClass C = fiberTwist π 1` this constant
   is `d₁ := classDeg k (fiberTwist π 1)`, and `1 ≤ d₁` is `one_le_classDeg_thetaCechClass`
   (DAT-0b).

3. **The multiplication-by-`θ_T ^ m` natural isomorphism `mulThetaPowNatIso`**, as
   `Type`-valued functors:
   `(pic0Functor C ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat ≅ picDegLayerFunctor C (m·d₁)`.
   The group structure lives **only** on the `pic0` side (worksheet §5 risk 6:
   `pic^d` is a coset, not a subgroup — `picDegLayer` is a subtype, not a subgroup).
   `representableByOfShift` transports a `RepresentableBy` datum for the shifted layer
   to one for the `pic0` functor mechanically (via `RepresentableBy.ofIso`) — the ε⁺
   shift of the final `rep` that DAT-J consumes.

## The pinned Θ-class `thetaCechClass` (DAT-0b)

`(C ⊗ overSpec k k).left` is a curve over `k` via the second projection
(`Curve/BaseChangeInstances.lean`), so `exists_isFinite_isDominant_toP1` produces a
finite dominant `π : (C ⊗ overSpec k k).left ⟶ ℙ¹` on it, and
`thetaCechClass C := fiberTwist π 1` is a class of that curve's Čech Picard group with
`1 ≤ classDeg k (thetaCechClass C)` (`one_le_classDeg_fiberTwist_one`, DAT-0b).  This is
the canonical `L₀`; `thetaFamily C (thetaCechClass C)` is the pinned `θ_T`.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The canonical structure map to the base test object `overSpec k k` -/

/-- The base test object `overSpec k k` has identity structure morphism (`algebraMap k k`
is the identity ring map). -/
private lemma overSpecSelf_hom : (overSpec k k).hom = 𝟙 (Spec (.of k)) := by
  rw [overSpec_hom, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- The canonical morphism from a test object `T` to the base test object `overSpec k k`,
given by the structure morphism `T.hom` (which lands in `(overSpec k k).left = Spec k`). -/
def toBaseTest (T : Over (Spec (.of k))) : T ⟶ overSpec k k :=
  Over.homMk T.hom (by
    have h : (overSpec k k).hom = 𝟙 (overSpec k k).left := overSpecSelf_hom
    rw [h]; exact Category.comp_id T.hom)

@[simp]
lemma toBaseTest_left (T : Over (Spec (.of k))) : (toBaseTest T).left = T.hom := rfl

/-- Naturality of the canonical map to the base: it is the terminal cocone leg. -/
lemma toBaseTest_naturality {T T' : Over (Spec (.of k))} (f : T' ⟶ T) :
    f ≫ toBaseTest T = toBaseTest T' :=
  Over.OverMorphism.ext (by rw [Over.comp_left, toBaseTest_left, toBaseTest_left, Over.w])

/-- On an affine test the canonical map to the base is `Spec` of the structure algebra
map `k → A`. -/
lemma toBaseTest_overSpec (A : Type u) [CommRing A] [Algebra k A] :
    toBaseTest (overSpec k A) = Over.overSpecMap (Algebra.ofId k A) :=
  Over.OverMorphism.ext rfl

/-! ## The θ-family -/

variable (C) in
/-- The base plus class over `overSpec k k` determined by a Čech class `L₀` on the
base-changed curve: the affine-comparison preimage of the plus unit of `relPicMk L₀`. -/
def thetaBase (L₀ : (C ⊗ overSpec k k).left.CechPic) : picEt C (overSpec k k) :=
  (picEtAffineEquiv C k).symm (PicEtAff.unit C k (relPicMk C (overSpec k k) L₀))

variable (C) in
/-- **The θ-family `θ_T` (DAT-5.1).** The image of the pinned Θ-class `L₀` in
`picEt C T`, pulled back from the base along the canonical structure map.  Natural in `T`
(`thetaFamily_natural`): `θ` pulls back to `θ` under every test map. -/
def thetaFamily (L₀ : (C ⊗ overSpec k k).left.CechPic) (T : Over (Spec (.of k))) :
    picEt C T :=
  picEtMap C (toBaseTest T) (thetaBase C L₀)

variable (C) in
/-- **Naturality of the θ-family**: `θ` pulls back to `θ` under every test map — the
key that lets DAT-C/DAT-B twist by `θ_T ^ m` uniformly. -/
theorem thetaFamily_natural (L₀ : (C ⊗ overSpec k k).left.CechPic)
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) :
    picEtMap C f (thetaFamily C L₀ T) = thetaFamily C L₀ T' := by
  change picEtMap C f (picEtMap C (toBaseTest T) (thetaBase C L₀))
      = picEtMap C (toBaseTest T') (thetaBase C L₀)
  rw [← picEtMap_comp, toBaseTest_naturality]

variable (C) in
/-- **The affine collapse of the θ-family** at an affine test `overSpec k A`: it is the
plus unit of the base-changed base class, in the exact shape DAT-4's degree seam
consumes. -/
theorem thetaFamily_overSpec_affineEquiv (L₀ : (C ⊗ overSpec k k).left.CechPic)
    (A : Type u) [CommRing A] [Algebra k A] :
    picEtAffineEquiv C A (thetaFamily C L₀ (overSpec k A))
      = PicEtAff.unit C A
          (relPicAlgMap C (Algebra.ofId k A) (relPicMk C (overSpec k k) L₀)) := by
  change picEtAffineEquiv C A (picEtMap C (toBaseTest (overSpec k A)) (thetaBase C L₀)) = _
  rw [toBaseTest_overSpec, picEtAffineEquiv_naturality, thetaBase,
    MulEquiv.apply_symm_apply, PicEtAff.mapAlg_unit]

variable (C) in
/-- **The degree of the θ-family at every field point (DAT-5.2)**: `degAt (θ_T) t` equals
`classDeg k L₀`, the base-field-invariant θ-degree `d₁`.  Route: naturality reduces the
field point at `T` to the identity point at `overSpec k K`, and DAT-4's
`degAt_eq_classDeg_of_affineEquiv_eq_unit_baseChange` reads off `classDeg k L₀`. -/
theorem degAt_thetaFamily (L₀ : (C ⊗ overSpec k k).left.CechPic)
    {T : Over (Spec (.of k))} {K : Type u} [Field K] [Algebra k K]
    (t : overSpec k K ⟶ T) :
    degAt (thetaFamily C L₀ T) t = classDeg k L₀ := by
  have key : degAt (thetaFamily C L₀ (overSpec k K)) (Over.overSpecMap (AlgHom.id k K))
      = classDeg k L₀ :=
    degAt_eq_classDeg_of_affineEquiv_eq_unit_baseChange (AlgHom.id k K)
      (thetaFamily C L₀ (overSpec k K)) L₀ (thetaFamily_overSpec_affineEquiv C L₀ K)
  rw [Over.overSpecMap_id] at key
  rw [← key, ← thetaFamily_natural C L₀ t, degAt_picEtMap, Category.id_comp]

variable (C) in
/-- The degree of `θ_T ^ m` at every field point is `m · d₁`. -/
theorem degAt_thetaFamily_pow (L₀ : (C ⊗ overSpec k k).left.CechPic)
    {T : Over (Spec (.of k))} {K : Type u} [Field K] [Algebra k K] (m : ℕ)
    (t : overSpec k K ⟶ T) :
    degAt (thetaFamily C L₀ T ^ m) t = (m : ℤ) * classDeg k L₀ := by
  rw [degAt_pow, degAt_thetaFamily]

/-! ## The degree-`d` layer as a `Type`-valued subfunctor -/

variable (C) in
/-- **The degree-`d` layer `pic^d` (worksheet §5 risk 6)**: the classes of `picEt C T` of
degree `d` at *every* field point.  A **subtype**, not a subgroup — for `d ≠ 0` it is a
coset, so it carries no group structure.  This is the shifted target the chart functors
land in. -/
abbrev picDegLayer (d : ℤ) (T : Over (Spec (.of k))) : Type u :=
  {lam : picEt C T // ∀ (K : Type u) [Field K] [Algebra k K] (t : overSpec k K ⟶ T),
    degAt lam t = d}

variable (C) in
/-- **The degree-`d` layer functor** `pic^d : (Over (Spec k))ᵒᵖ ⥤ Type u`: the
`Type`-valued subfunctor of `picEtFunctor C` cut out by the degree-`d` condition.
Contravariant, no group structure. -/
def picDegLayerFunctor (d : ℤ) : (Over (Spec (.of k)))ᵒᵖ ⥤ Type u where
  obj T := picDegLayer C d T.unop
  map {T T'} g := ↾fun (lam : picDegLayer C d T.unop) =>
    (⟨picEtMap C g.unop lam.1, fun K _ _ t => by
      rw [degAt_picEtMap]; exact lam.2 K (t ≫ g.unop)⟩ : picDegLayer C d T'.unop)
  map_id T := by
    ext lam U
    exact congrArg (fun z : picEt C T.unop => z.1 U) (picEtMap_id C lam.1)
  map_comp {T T' T''} g h := by
    ext lam U
    exact congrArg (fun z : picEt C T''.unop => z.1 U) (picEtMap_comp C g.unop h.unop lam.1)

/-! ## The multiplication-by-`θ_T ^ m` isomorphism (DAT-5.3) -/

variable (C) in
/-- **Multiplication by `θ_T ^ m`, per object**: the bijection between the degree-zero
classes and the degree-`m·d₁` layer.  Forward: `λ ↦ λ · θ_T ^ m`
(`degAt_pic0_mul_pow`); backward: `μ ↦ μ · (θ_T ^ m)⁻¹`.  The group structure is used
only on the `pic0` side. -/
def mulThetaPowEquiv (L₀ : (C ⊗ overSpec k k).left.CechPic) (m : ℕ)
    (T : Over (Spec (.of k))) :
    pic0Subgroup C T ≃ picDegLayer C ((m : ℤ) * classDeg k L₀) T where
  toFun lam := ⟨(lam : picEt C T) * thetaFamily C L₀ T ^ m, fun K _ _ t => by
    rw [degAt_pic0_mul_pow (lam : picEt C T) lam.2 (thetaFamily C L₀ T) m t,
      degAt_thetaFamily]⟩
  invFun mu := ⟨mu.1 * (thetaFamily C L₀ T ^ m)⁻¹,
    mem_pic0Subgroup_iff.mpr fun K _ _ t => by
      rw [degAt_mul, degAt_inv, degAt_pow, degAt_thetaFamily, mu.2 K t]; ring⟩
  left_inv lam := Subtype.ext (mul_inv_cancel_right _ _)
  right_inv mu := Subtype.ext (inv_mul_cancel_right _ _)

variable (C) in
/-- **The ε⁺ shift (DAT-5.3): the multiplication-by-`θ_T ^ m` natural isomorphism**, as
`Type`-valued functors:
`(pic0Functor C ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat ≅ picDegLayerFunctor C (m·d₁)`.
Naturality is `thetaFamily_natural` (θ pulls back to θ).  The group structure lives only
on the `pic0` side, exactly what `ofRepresentableBy` needs (worksheet §5 risk 6). -/
def mulThetaPowNatIso (L₀ : (C ⊗ overSpec k k).left.CechPic) (m : ℕ) :
    (pic0Functor C ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat
      ≅ picDegLayerFunctor C ((m : ℤ) * classDeg k L₀) :=
  NatIso.ofComponents (fun T => (mulThetaPowEquiv C L₀ m T.unop).toIso) (by
    intro T T' g
    ext lam
    refine Subtype.ext ?_
    have key : picEtMap C g.unop ((pic0Subgroup C T.unop).subtype lam)
          * thetaFamily C L₀ T'.unop ^ m
        = picEtMap C g.unop ((pic0Subgroup C T.unop).subtype lam
          * thetaFamily C L₀ T.unop ^ m) := by
      rw [map_mul, map_pow, thetaFamily_natural]
    exact key)

variable (C) in
/-- **The ε⁺ transport of a `RepresentableBy` datum (DAT-J consumer)**: a representing
object for the shifted degree-`m·d₁` layer is a representing object for the degree-zero
Picard functor.  Precomposition with `mulThetaPowNatIso` via `RepresentableBy.ofIso`. -/
def representableByOfShift {J : Over (Spec (.of k))}
    (L₀ : (C ⊗ overSpec k k).left.CechPic) (m : ℕ)
    (rep : (picDegLayerFunctor C ((m : ℤ) * classDeg k L₀)).RepresentableBy J) :
    ((pic0Functor C ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat).RepresentableBy J :=
  rep.ofIso (mulThetaPowNatIso C L₀ m).symm

/-! ## The pinned Θ-class and its positivity (DAT-0b) -/

variable (C) in
/-- The base-changed curve `C_k = (C ⊗ overSpec k k).left`, bundled as an object of
`Over (Spec k)` via the second projection — the input shape of
`exists_isFinite_isDominant_toP1`. -/
def baseCurveObj : Over (Spec (.of k)) := Over.mk (snd C (overSpec k k)).left

instance : SmoothOfRelativeDimension 1 (baseCurveObj C).hom :=
  inferInstanceAs (SmoothOfRelativeDimension 1 (snd C (overSpec k k)).left)

instance : IsProper (baseCurveObj C).hom :=
  inferInstanceAs (IsProper (snd C (overSpec k k)).left)

instance : GeometricallyIrreducible (baseCurveObj C).hom :=
  inferInstanceAs (GeometricallyIrreducible (snd C (overSpec k k)).left)

variable (C) in
/-- A finite dominant map `π : C_k ⟶ ℙ¹` on the base-changed curve
`C_k = (C ⊗ overSpec k k).left`, from `exists_isFinite_isDominant_toP1`. -/
def thetaP1 : (C ⊗ overSpec k k).left ⟶ P1 k :=
  (exists_isFinite_isDominant_toP1 (C := baseCurveObj C)).choose

lemma isFinite_thetaP1 : IsFinite (thetaP1 C) :=
  (exists_isFinite_isDominant_toP1 (C := baseCurveObj C)).choose_spec.1

lemma isDominant_thetaP1 : IsDominant (thetaP1 C) :=
  (exists_isFinite_isDominant_toP1 (C := baseCurveObj C)).choose_spec.2.1

variable (C) in
/-- **The pinned Θ-class** `thetaCechClass C = fiberTwist π 1` on the base-changed curve
`C_k = (C ⊗ overSpec k k).left`: the canonical `L₀` of the ε⁺ shift. -/
def thetaCechClass : (C ⊗ overSpec k k).left.CechPic :=
  haveI := isDominant_thetaP1 (C := C)
  fiberTwist (thetaP1 C) 1

/-- **DAT-0b consumed: `d₁ ≥ 1`.** The degree of the pinned Θ-class is at least one at the
base field, hence (by DAT-4 base-field invariance) `degAt (thetaFamily C (thetaCechClass C) T)`
is `≥ 1` at every field point. -/
theorem one_le_classDeg_thetaCechClass : 1 ≤ classDeg k (thetaCechClass C) := by
  haveI := isFinite_thetaP1 (C := C)
  haveI := isDominant_thetaP1 (C := C)
  exact one_le_classDeg_fiberTwist_one (thetaP1 C)

end

end AlgebraicGeometry
