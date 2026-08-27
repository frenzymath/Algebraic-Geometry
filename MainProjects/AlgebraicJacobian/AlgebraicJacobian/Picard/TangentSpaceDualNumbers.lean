/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Tangent-space substrate: derivations and the cotangent dual (A.3.iii substrate)

Commutative-algebra substrate for the Kleiman §5 tangent-space theorem
`thm:pic0_tangent_space_iso` (`Picard/Pic0AbelianVariety.lean`,
`Scheme.Pic0.tangentSpaceIso`): the identification of the Zariski tangent
space of a `k`-scheme at a `k`-rational point with the dual of the cotangent
space `m/m²`, expressed at the level of the local ring at the point.

Throughout, `R` is a local `k`-algebra. The `k`-rational-point hypothesis is
`Function.Bijective (algebraMap k (ResidueField R))` — the structure map to
the residue field is an isomorphism.

## Main declarations

- `AlgebraicGeometry.maximalIdeal_smul_residueField` — elements of the
  maximal ideal act by zero on the residue field.
- `AlgebraicGeometry.derivationCotangentDual` — a `k`-derivation
  `R → ResidueField R` kills `m²`, hence descends to an `R`-linear map
  `CotangentSpace R →ₗ[R] ResidueField R` on `m/m²`.
- `AlgebraicGeometry.derivationEquivCotangentDual` — for a `k`-rational
  local `k`-algebra, descent is an additive equivalence
  `Derivation k R (ResidueField R) ≃+ (CotangentSpace R →ₗ[R] ResidueField R)`,
  with inverse built from the canonical splitting `R = k ⊕ m`.
- `AlgebraicGeometry.localDualNumberHomEquivDerivation` — local `k`-algebra
  maps `R → k[ε]` are `k`-derivations `R → ResidueField R` (`ε`-coefficient).
- `AlgebraicGeometry.localDualNumberHomEquivCotangentSpaceDual` — the
  capstone: dual-number points of the closed point form the `κ`-linear dual
  of the cotangent space, `Module.Dual (ResidueField R) (CotangentSpace R)`.

This is the "tangent space via dual numbers" paragraph of Kleiman §5
Thm. 5.11: points of a scheme over the dual numbers lifting a `k`-rational
point `e` correspond to local `k`-algebra maps `𝒪_e → k[ε]`, i.e. to
`k`-derivations `𝒪_e → k`, i.e. by this file to `Hom(m_e/m_e², k)`.

Blueprint: `blueprint/src/chapters/Picard_Pic0AbelianVariety.tex`,
§ `sec:pic0_tangent_space` (`lem:tangent_derivation_cotangent_dual` and
friends), feeding `thm:pic0_tangent_space_iso`.
-/

set_option autoImplicit false

universe u v

namespace AlgebraicGeometry

open IsLocalRing

section MaximalIdealAction

variable {R : Type v} [CommRing R] [IsLocalRing R]

/-- Elements of the maximal ideal act by zero on the residue field. -/
lemma maximalIdeal_smul_residueField {x : R} (hx : x ∈ maximalIdeal R)
    (c : ResidueField R) : x • c = 0 := by
  rw [Algebra.smul_def]
  have hx0 : algebraMap R (ResidueField R) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hx
  rw [hx0, zero_mul]

end MaximalIdealAction

section DerivationCotangent

variable {k : Type u} [Field k] {R : Type v} [CommRing R] [IsLocalRing R]
  [Algebra k R]

/-- The restriction of a `k`-derivation `d : R → ResidueField R` to the
maximal ideal, as an `R`-linear map `m →ₗ[R] ResidueField R`. Linearity over
`R` (not merely `k`) holds because the second Leibniz term `x • d r` dies:
`x ∈ m` acts by zero on the residue field. -/
noncomputable def derivationRestrictMaximalIdeal (d : Derivation k R (ResidueField R)) :
    maximalIdeal R →ₗ[R] ResidueField R where
  toFun x := d (x : R)
  map_add' x y := by simp
  map_smul' r x := by
    have hrx : ((r • x : maximalIdeal R) : R) = r * (x : R) := rfl
    rw [hrx, Derivation.leibniz, maximalIdeal_smul_residueField x.2 (d r),
      add_zero, RingHom.id_apply]

@[simp]
lemma derivationRestrictMaximalIdeal_apply (d : Derivation k R (ResidueField R))
    (x : maximalIdeal R) :
    derivationRestrictMaximalIdeal d x = d (x : R) := rfl

/-- A `k`-derivation `R → ResidueField R` kills `m • m`, hence descends to the
cotangent space `m/m²`, `R`-linearly. -/
noncomputable def derivationCotangentDual (d : Derivation k R (ResidueField R)) :
    CotangentSpace R →ₗ[R] ResidueField R :=
  Submodule.liftQ _ (derivationRestrictMaximalIdeal d) (by
    rw [Submodule.smul_le]
    intro r hr x _
    simp only [LinearMap.mem_ker, LinearMap.map_smul,
      derivationRestrictMaximalIdeal_apply]
    exact maximalIdeal_smul_residueField hr _)

@[simp]
lemma derivationCotangentDual_toCotangent (d : Derivation k R (ResidueField R))
    (x : maximalIdeal R) :
    derivationCotangentDual d ((maximalIdeal R).toCotangent x) = d (x : R) := rfl

section Rational

variable (hres : Function.Bijective (algebraMap k (ResidueField R)))

/-- The `k`-rational-point hypothesis packaged as a ring equivalence
`k ≃+* ResidueField R`. -/
noncomputable def residueFieldEquivOfBijective : k ≃+* ResidueField R :=
  RingEquiv.ofBijective _ hres

@[simp]
lemma residueFieldEquivOfBijective_apply (c : k) :
    residueFieldEquivOfBijective (R := R) hres c
      = algebraMap k (ResidueField R) c := rfl

lemma residue_algebraMap (c : k) :
    residue R (algebraMap k R c) = algebraMap k (ResidueField R) c := by
  rw [IsScalarTower.algebraMap_apply k R (ResidueField R) c]
  rfl

/-- The canonical "constant part" of `r : R` at a `k`-rational point: the
image in `R` of the residue class of `r`, along the inverse of the residue
isomorphism. Subtracting it lands in the maximal ideal. -/
noncomputable def sectOfBijective (r : R) : R :=
  algebraMap k R ((residueFieldEquivOfBijective (R := R) hres).symm (residue R r))

lemma residue_sectOfBijective (r : R) :
    residue R (sectOfBijective hres r) = residue R r := by
  unfold sectOfBijective
  rw [residue_algebraMap]
  exact (residueFieldEquivOfBijective (R := R) hres).apply_symm_apply _

lemma sub_sectOfBijective_mem_maximalIdeal (r : R) :
    r - sectOfBijective hres r ∈ maximalIdeal R := by
  have h : residue R (r - sectOfBijective hres r) = 0 := by
    rw [map_sub, residue_sectOfBijective, sub_self]
  exact Ideal.Quotient.eq_zero_iff_mem.mp h

lemma sectOfBijective_algebraMap (c : k) :
    sectOfBijective hres (algebraMap k R c) = algebraMap k R c := by
  unfold sectOfBijective
  rw [residue_algebraMap]
  congr 1
  exact (residueFieldEquivOfBijective (R := R) hres).symm_apply_apply c

lemma sectOfBijective_of_mem {x : R} (hx : x ∈ maximalIdeal R) :
    sectOfBijective hres x = 0 := by
  have h0 : residue R x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  unfold sectOfBijective
  rw [h0, map_zero, map_zero]

lemma sectOfBijective_add (r s : R) :
    sectOfBijective hres (r + s)
      = sectOfBijective hres r + sectOfBijective hres s := by
  unfold sectOfBijective
  rw [map_add, map_add, map_add]

lemma sectOfBijective_mul (r s : R) :
    sectOfBijective hres (r * s)
      = sectOfBijective hres r * sectOfBijective hres s := by
  unfold sectOfBijective
  rw [map_mul, map_mul, map_mul]

lemma sectOfBijective_one : sectOfBijective hres (1 : R) = 1 := by
  unfold sectOfBijective
  rw [map_one, map_one, map_one]

/-- If `r - sect r ∈ m`, then `r` and its constant part act identically on the
residue field. -/
lemma smul_residueField_eq_sectOfBijective_smul (r : R) (c : ResidueField R) :
    r • c = sectOfBijective hres r • c := by
  have h : r • c - sectOfBijective hres r • c = (r - sectOfBijective hres r) • c :=
    (sub_smul r (sectOfBijective hres r) c).symm
  have h0 : (r - sectOfBijective hres r) • c = 0 :=
    maximalIdeal_smul_residueField (sub_sectOfBijective_mem_maximalIdeal hres r) c
  exact sub_eq_zero.mp (h.trans h0)

/-- The element of the maximal ideal cut out by `r : R` under the canonical
splitting `R = k ⊕ m` at a `k`-rational point. -/
noncomputable def maximalIdealPart (r : R) : maximalIdeal R :=
  ⟨r - sectOfBijective hres r, sub_sectOfBijective_mem_maximalIdeal hres r⟩

@[simp]
lemma maximalIdealPart_coe (r : R) :
    (maximalIdealPart hres r : R) = r - sectOfBijective hres r := rfl

lemma maximalIdealPart_of_mem {x : R} (hx : x ∈ maximalIdeal R) :
    maximalIdealPart hres x = ⟨x, hx⟩ := by
  ext
  rw [maximalIdealPart_coe, sectOfBijective_of_mem hres hx, sub_zero]

lemma maximalIdealPart_add (r s : R) :
    maximalIdealPart hres (r + s)
      = maximalIdealPart hres r + maximalIdealPart hres s := by
  ext
  simp only [maximalIdealPart_coe, Submodule.coe_add, sectOfBijective_add]
  ring

/-- The Leibniz decomposition of the maximal-ideal part of a product. The
last summand lies in `m²`. -/
lemma maximalIdealPart_mul (r s : R) :
    maximalIdealPart hres (r * s)
      = sectOfBijective hres r • maximalIdealPart hres s
        + sectOfBijective hres s • maximalIdealPart hres r
        + ⟨(r - sectOfBijective hres r) * (s - sectOfBijective hres s),
           Ideal.mul_mem_right _ _ (sub_sectOfBijective_mem_maximalIdeal hres r)⟩ := by
  ext
  simp only [maximalIdealPart_coe, Submodule.coe_add, SetLike.val_smul,
    smul_eq_mul, sectOfBijective_mul]
  ring

/-- The inverse construction: an `R`-linear functional on the cotangent space
`m/m²` extends to a `k`-derivation `R → ResidueField R` via the canonical
splitting `R = k ⊕ m` at a `k`-rational point. -/
noncomputable def cotangentDualToDerivation
    (φ : CotangentSpace R →ₗ[R] ResidueField R) :
    Derivation k R (ResidueField R) where
  toFun r := φ ((maximalIdeal R).toCotangent (maximalIdealPart hres r))
  map_add' r s := by
    rw [maximalIdealPart_add, map_add, map_add]
  map_smul' c r := by
    have hpart : maximalIdealPart hres (c • r)
        = algebraMap k R c • maximalIdealPart hres r := by
      ext
      simp only [maximalIdealPart_coe, SetLike.val_smul, smul_eq_mul]
      have hsm : (c • r : R) = algebraMap k R c * r := Algebra.smul_def c r
      rw [hsm, sectOfBijective_mul, sectOfBijective_algebraMap]
      ring
    rw [hpart, map_smul, map_smul, RingHom.id_apply, algebraMap_smul]
  map_one_eq_zero' := by
    change φ ((maximalIdeal R).toCotangent (maximalIdealPart hres (1 : R))) = 0
    have h1 : maximalIdealPart hres (1 : R) = 0 := by
      ext
      rw [maximalIdealPart_coe, sectOfBijective_one, sub_self,
        ZeroMemClass.coe_zero]
    rw [h1, map_zero, map_zero]
  leibniz' r s := by
    change φ ((maximalIdeal R).toCotangent (maximalIdealPart hres (r * s)))
        = r • φ ((maximalIdeal R).toCotangent (maximalIdealPart hres s))
          + s • φ ((maximalIdeal R).toCotangent (maximalIdealPart hres r))
    have hsq : (maximalIdeal R).toCotangent
        ⟨(r - sectOfBijective hres r) * (s - sectOfBijective hres s),
         Ideal.mul_mem_right _ _ (sub_sectOfBijective_mem_maximalIdeal hres r)⟩
          = 0 := by
      rw [Ideal.toCotangent_eq_zero, pow_two]
      exact Ideal.mul_mem_mul
        (sub_sectOfBijective_mem_maximalIdeal hres r)
        (sub_sectOfBijective_mem_maximalIdeal hres s)
    rw [maximalIdealPart_mul]
    simp only [map_add, map_smul, hsq, add_zero]
    rw [← smul_residueField_eq_sectOfBijective_smul hres r,
      ← smul_residueField_eq_sectOfBijective_smul hres s]

@[simp]
lemma cotangentDualToDerivation_apply
    (φ : CotangentSpace R →ₗ[R] ResidueField R) (r : R) :
    cotangentDualToDerivation hres φ r
      = φ ((maximalIdeal R).toCotangent (maximalIdealPart hres r)) := rfl

/-- **Derivations are the cotangent dual** (Kleiman §5, tangent space via dual
numbers, algebraic core). For a local `k`-algebra `R` whose residue field is
`k` (a `k`-rational point), descent to `m/m²` is an additive equivalence
between `k`-derivations `R → ResidueField R` and `R`-linear functionals on
the cotangent space. -/
noncomputable def derivationEquivCotangentDual :
    Derivation k R (ResidueField R) ≃+ (CotangentSpace R →ₗ[R] ResidueField R) where
  toFun d := derivationCotangentDual d
  invFun φ := cotangentDualToDerivation hres φ
  left_inv d := by
    ext r
    simp only [cotangentDualToDerivation_apply, derivationCotangentDual_toCotangent,
      maximalIdealPart_coe, map_sub]
    have : d (sectOfBijective hres r) = 0 := by
      unfold sectOfBijective
      exact d.map_algebraMap _
    rw [this, sub_zero]
  right_inv φ := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective (maximalIdeal R) x
    rw [derivationCotangentDual_toCotangent, cotangentDualToDerivation_apply,
      maximalIdealPart_of_mem hres y.2]
  map_add' d₁ d₂ := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective (maximalIdeal R) x
    simp [derivationCotangentDual_toCotangent]

/-- `r • c = residue r * c` on the residue field. -/
lemma smul_residueField_def (r : R) (c : ResidueField R) :
    r • c = residue R r * c := by
  rw [Algebra.smul_def]; rfl

lemma algebraMap_residueFieldEquiv_symm (y : ResidueField R) :
    algebraMap k (ResidueField R)
      ((residueFieldEquivOfBijective (R := R) hres).symm y) = y :=
  (residueFieldEquivOfBijective (R := R) hres).apply_symm_apply y

lemma residueFieldEquiv_symm_algebraMap (c : k) :
    (residueFieldEquivOfBijective (R := R) hres).symm
      (algebraMap k (ResidueField R) c) = c :=
  (residueFieldEquivOfBijective (R := R) hres).symm_apply_apply c

section DualNumbers

open TrivSqZeroExt

/-- A `k`-algebra map `R → k[ε]` that kills the maximal ideal in the constant
component (equivalently: a local homomorphism, since the maximal ideal of
`k[ε]` is `(ε) = ker fst`) has constant component the residue class:
`fst (f r)` is `residue r` read through `k ≅ ResidueField R`. -/
lemma fst_dualNumberHom_eq (f : R →ₐ[k] DualNumber k)
    (hf : ∀ x ∈ maximalIdeal R, fst (f x) = 0) (r : R) :
    fst (f r) = (residueFieldEquivOfBijective (R := R) hres).symm (residue R r) := by
  have hsplit : r = algebraMap k R
      ((residueFieldEquivOfBijective (R := R) hres).symm (residue R r))
      + (r - sectOfBijective hres r) := by
    unfold sectOfBijective
    ring
  calc fst (f r)
      = fst (f (algebraMap k R
            ((residueFieldEquivOfBijective (R := R) hres).symm (residue R r))))
        + fst (f (r - sectOfBijective hres r)) := by
        conv_lhs => rw [hsplit]
        rw [map_add, fst_add]
    _ = (residueFieldEquivOfBijective (R := R) hres).symm (residue R r) := by
        rw [hf _ (sub_sectOfBijective_mem_maximalIdeal hres r), add_zero,
          AlgHom.commutes]
        simp [TrivSqZeroExt.algebraMap_eq_inl']

/-- The `ε`-coefficient of a local `k`-algebra map `R → k[ε]`, as a
`k`-derivation `R → ResidueField R`. -/
noncomputable def dualNumberHomToDerivation (f : R →ₐ[k] DualNumber k)
    (hf : ∀ x ∈ maximalIdeal R, fst (f x) = 0) :
    Derivation k R (ResidueField R) where
  toFun r := algebraMap k (ResidueField R) (snd (f r))
  map_add' r s := by rw [map_add, snd_add, map_add]
  map_smul' c r := by
    rw [map_smul, snd_smul, RingHom.id_apply, smul_eq_mul, map_mul,
      ← Algebra.smul_def]
  map_one_eq_zero' := by
    change algebraMap k (ResidueField R) (snd (f 1)) = 0
    rw [map_one, snd_one, map_zero]
  leibniz' r s := by
    change algebraMap k (ResidueField R) (snd (f (r * s)))
        = r • algebraMap k (ResidueField R) (snd (f s))
          + s • algebraMap k (ResidueField R) (snd (f r))
    rw [map_mul, snd_mul, map_add, smul_eq_mul, op_smul_eq_mul,
      map_mul, map_mul,
      fst_dualNumberHom_eq hres f hf r, fst_dualNumberHom_eq hres f hf s,
      algebraMap_residueFieldEquiv_symm hres, algebraMap_residueFieldEquiv_symm hres,
      smul_residueField_def, smul_residueField_def]
    ring

@[simp]
lemma dualNumberHomToDerivation_apply (f : R →ₐ[k] DualNumber k)
    (hf : ∀ x ∈ maximalIdeal R, fst (f x) = 0) (r : R) :
    dualNumberHomToDerivation hres f hf r
      = algebraMap k (ResidueField R) (snd (f r)) := rfl

/-- The `k`-algebra map `R → k[ε]` attached to a `k`-derivation
`D : R → ResidueField R`: constant component the residue class, `ε`-component
`D`. -/
noncomputable def derivationToDualNumberHom (D : Derivation k R (ResidueField R)) :
    R →ₐ[k] DualNumber k where
  toFun r := inl ((residueFieldEquivOfBijective (R := R) hres).symm (residue R r))
    + inr ((residueFieldEquivOfBijective (R := R) hres).symm (D r))
  map_one' := by
    rw [map_one, map_one, Derivation.map_one_eq_zero, map_zero, inr_zero, add_zero,
      inl_one]
  map_mul' r s := by
    have hD : (residueFieldEquivOfBijective (R := R) hres).symm (D (r * s))
        = (residueFieldEquivOfBijective (R := R) hres).symm (residue R r)
            * (residueFieldEquivOfBijective (R := R) hres).symm (D s)
          + (residueFieldEquivOfBijective (R := R) hres).symm (D r)
            * (residueFieldEquivOfBijective (R := R) hres).symm (residue R s) := by
      rw [Derivation.leibniz, smul_residueField_def, smul_residueField_def,
        map_add, map_mul, map_mul]
      ring
    rw [map_mul, map_mul, hD]
    rw [add_mul, mul_add, mul_add, inl_mul_inl, inl_mul_inr, inr_mul_inl,
      inr_mul_inr, add_zero, inr_add, smul_eq_mul, op_smul_eq_mul]
    abel
  map_zero' := by
    rw [map_zero, map_zero, map_zero, map_zero, inl_zero, inr_zero, add_zero]
  map_add' r s := by
    rw [map_add, map_add, map_add, map_add, inl_add, inr_add]
    abel
  commutes' c := by
    rw [residue_algebraMap, residueFieldEquiv_symm_algebraMap hres,
      Derivation.map_algebraMap, map_zero, inr_zero, add_zero,
      TrivSqZeroExt.algebraMap_eq_inl']
    simp

@[simp]
lemma derivationToDualNumberHom_apply (D : Derivation k R (ResidueField R)) (r : R) :
    derivationToDualNumberHom hres D r
      = inl ((residueFieldEquivOfBijective (R := R) hres).symm (residue R r))
        + inr ((residueFieldEquivOfBijective (R := R) hres).symm (D r)) := rfl

lemma derivationToDualNumberHom_fst_of_mem (D : Derivation k R (ResidueField R))
    {x : R} (hx : x ∈ maximalIdeal R) :
    fst (derivationToDualNumberHom hres D x) = 0 := by
  have h0 : residue R x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  rw [derivationToDualNumberHom_apply, fst_add, fst_inl, fst_inr, add_zero,
    h0, map_zero]

/-- **Dual-number points are derivations** (Kleiman §5, tangent space via
dual numbers). For a local `k`-algebra `R` with residue field `k`, the local
`k`-algebra maps `R → k[ε]` (those killing the maximal ideal in the constant
component) correspond to `k`-derivations `R → ResidueField R`. -/
noncomputable def localDualNumberHomEquivDerivation :
    {f : R →ₐ[k] DualNumber k // ∀ x ∈ maximalIdeal R, fst (f x) = 0}
      ≃ Derivation k R (ResidueField R) where
  toFun f := dualNumberHomToDerivation hres f.1 f.2
  invFun D := ⟨derivationToDualNumberHom hres D,
    fun _ hx => derivationToDualNumberHom_fst_of_mem hres D hx⟩
  left_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    intro r
    rw [derivationToDualNumberHom_apply, dualNumberHomToDerivation_apply,
      residueFieldEquiv_symm_algebraMap hres,
      ← fst_dualNumberHom_eq hres f.1 f.2 r]
    exact inl_fst_add_inr_snd_eq (f.1 r)
  right_inv D := by
    ext r
    rw [dualNumberHomToDerivation_apply, derivationToDualNumberHom_apply,
      snd_add, snd_inl, snd_inr, zero_add,
      algebraMap_residueFieldEquiv_symm hres]

/-- **The tangent space is the cotangent dual** (Kleiman §5 Thm. 5.11,
"tangent space via dual numbers", algebraic form): for a local `k`-algebra
`R` with residue field `k`, the set of local `k`-algebra maps `R → k[ε]`
(the dual-number points of `Spec R` over the closed point) is in bijection
with the `R`-linear functionals on the cotangent space `m/m²`. -/
noncomputable def localDualNumberHomEquivCotangentDual :
    {f : R →ₐ[k] DualNumber k // ∀ x ∈ maximalIdeal R, fst (f x) = 0}
      ≃ (CotangentSpace R →ₗ[R] ResidueField R) :=
  (localDualNumberHomEquivDerivation hres).trans
    (derivationEquivCotangentDual hres).toEquiv

/-- `R`-linear functionals on the cotangent space are automatically
`ResidueField R`-linear: both sides are annihilated by the maximal ideal and
the residue map is surjective. -/
noncomputable def cotangentDualExtendScalars :
    (CotangentSpace R →ₗ[R] ResidueField R)
      ≃ₗ[R] Module.Dual (ResidueField R) (CotangentSpace R) :=
  LinearMap.extendScalarsOfSurjectiveEquiv Ideal.Quotient.mk_surjective

/-- **The tangent space is the dual of the cotangent space** (Kleiman §5,
Thm. 5.11, first step), in its `κ`-linear form: the dual-number points of a
`k`-rational point of a local `k`-algebra `R` form the
`ResidueField R`-linear dual of `m/m²`. -/
noncomputable def localDualNumberHomEquivCotangentSpaceDual :
    {f : R →ₐ[k] DualNumber k // ∀ x ∈ maximalIdeal R, fst (f x) = 0}
      ≃ Module.Dual (ResidueField R) (CotangentSpace R) :=
  (localDualNumberHomEquivCotangentDual hres).trans
    (cotangentDualExtendScalars (R := R)).toEquiv

end DualNumbers

end Rational

end DerivationCotangent

end AlgebraicGeometry
