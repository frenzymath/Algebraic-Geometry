/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.DualNumber
import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# Units of the dual numbers: the truncated-exponential splitting

The opening algebra brick of Kleiman §5 Thm.~`thm:tgtsp` (5.11): for a
commutative ring `R`, the unit group of the dual numbers `R[ε]` sits in a
**split short exact sequence**

```
1 → (R, +) → (R[ε])ˣ → Rˣ → 1
```

where the kernel embedding is the *truncated exponential*
`b ↦ 1 + b ε` (a group homomorphism from the additive group of `R`, since
`(1 + bε)(1 + cε) = 1 + (b + c)ε`), the projection is `fst` on units, and
`inl : R → R[ε]` splits it. Consequently

```
(R[ε])ˣ ≃* Rˣ × (R, +).
```

Sheafified over the dual-number thickening `C_ε` of a curve `C` (whose
structure sheaf has section rings `O_C(U)[ε]`), this sequence becomes the
truncated-exponential sequence `0 → O_C → O^×_{C_ε} → O^×_C → 1` whose `H¹`
comparison computes `ker(Pic(C_ε) → Pic(C)) ≅ H¹(C, O_C)` — the tangent-space
identification `T₀ Pic⁰_{C/k} ≅ H¹(C, O_C)` (`Pic0.tangentSpaceIso`, sibling
`Picard/Pic0AbelianVariety.lean`). Everything here is natural in `R`, which is
what the sheaf-level upgrade consumes; the functorial ring map
`mapRingHom : R[ε] →+* S[ε]` and its compatibilities are provided at the end.

## Main declarations

* `DualNumber.truncExpUnit : R → (R[ε])ˣ` — `1 + b ε` as a unit.
* `DualNumber.truncExp : Multiplicative R →* (R[ε])ˣ` — the truncated
  exponential as a group homomorphism, injective (`truncExp_injective`).
* `DualNumber.unitsFst : (R[ε])ˣ →* Rˣ` — reduction mod `ε` on units,
  surjective with section `unitsInl` (`unitsFst_comp_unitsInl`).
* `DualNumber.truncExp_range_eq_ker_unitsFst` — exactness in the middle.
* `DualNumber.unitsEquivProd : (R[ε])ˣ ≃* Rˣ × Multiplicative R` — the
  splitting.
* `DualNumber.mapRingHom : (R →+* S) → (R[ε] →+* S[ε])` — functoriality,
  with `mapRingHom_id`, `mapRingHom_comp`, and the naturality lemmas
  `unitsFst_map_mapRingHom`, `map_mapRingHom_truncExpUnit`.

## References

Kleiman, "The Picard scheme", §5, proof of Thm.~5.11 (arXiv:math/0504020);
Hartshorne, "Algebraic Geometry", GTM 52, Ex. III.4.6 / IV proof patterns.

Blueprint: `blueprint/src/chapters/Picard_Pic0AbelianVariety.tex`,
§`sec:pic0_trunc_exp`.
-/

set_option autoImplicit false

universe u v w

namespace DualNumber

open TrivSqZeroExt

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]

/-! ## §1. The truncated exponential -/

/-- Squares of infinitesimals vanish: `(b ε) * (c ε) = 0` in `R[ε]`. -/
theorem inr_mul_inr_eq_zero (b c : R) : (inr b : R[ε]) * inr c = 0 :=
  inr_mul_inr R b c

/-- **The truncated exponential is a unit**: `1 + b ε` is invertible in
`R[ε]`, with inverse `1 - b ε`. -/
def truncExpUnit (b : R) : (R[ε])ˣ :=
  Units.mkOfMulEqOne (1 + inr b) (1 - inr b) <| by
    calc (1 + inr b) * (1 - inr b)
        = 1 - (inr b : R[ε]) * inr b := by ring
      _ = 1 := by rw [inr_mul_inr_eq_zero, sub_zero]

@[simp]
theorem truncExpUnit_val (b : R) : (truncExpUnit b : R[ε]) = 1 + inr b :=
  rfl

@[simp]
theorem fst_truncExpUnit (b : R) : (truncExpUnit b : R[ε]).fst = 1 := by
  simp

@[simp]
theorem snd_truncExpUnit (b : R) : (truncExpUnit b : R[ε]).snd = b := by
  simp

/-- Additivity of the truncated exponential:
`(1 + b ε)(1 + c ε) = 1 + (b + c) ε`. -/
theorem truncExpUnit_add (b c : R) :
    truncExpUnit (b + c) = truncExpUnit b * truncExpUnit c :=
  Units.ext <| by
    calc (1 + inr (b + c) : R[ε])
        = 1 + (inr b + inr c) + inr b * inr c := by
          rw [inr_mul_inr_eq_zero, add_zero, inr_add]
      _ = (1 + inr b) * (1 + inr c) := by ring

/-- **The truncated exponential** `b ↦ 1 + b ε` as a group homomorphism from
the additive group of `R` (written multiplicatively) to the unit group of the
dual numbers. -/
def truncExp : Multiplicative R →* (R[ε])ˣ where
  toFun b := truncExpUnit b.toAdd
  map_one' := Units.ext <| by simp
  map_mul' b c := truncExpUnit_add b.toAdd c.toAdd

@[simp]
theorem truncExp_apply (b : Multiplicative R) :
    truncExp b = truncExpUnit b.toAdd :=
  rfl

/-- The truncated exponential is injective. -/
theorem truncExp_injective : Function.Injective (truncExp (R := R)) := by
  intro b c h
  have : (truncExpUnit b.toAdd : R[ε]).snd = (truncExpUnit c.toAdd : R[ε]).snd := by
    rw [truncExp_apply, truncExp_apply] at h
    rw [h]
  simpa using this

/-! ## §2. Reduction mod `ε` on units, and exactness -/

/-- Reduction mod `ε`, `fst : R[ε] → R`, as a ring homomorphism. -/
def fstRingHom : R[ε] →+* R where
  toFun := fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero
  map_add' := fst_add

@[simp]
theorem fstRingHom_apply (x : R[ε]) : fstRingHom x = x.fst :=
  rfl

/-- The inclusion `inl : R → R[ε]` as a ring homomorphism (Mathlib's
`TrivSqZeroExt.inlHom`, re-exported at the dual numbers). -/
def inlRingHom : R →+* R[ε] :=
  inlHom R R

@[simp]
theorem inlRingHom_apply (r : R) : inlRingHom r = (inl r : R[ε]) :=
  rfl

/-- **Reduction mod `ε` on unit groups**: the group homomorphism
`(R[ε])ˣ →* Rˣ` induced by `fst`. -/
def unitsFst : (R[ε])ˣ →* Rˣ :=
  Units.map (fstRingHom (R := R)).toMonoidHom

@[simp]
theorem unitsFst_apply_val (u : (R[ε])ˣ) : (unitsFst u : R) = (u : R[ε]).fst :=
  rfl

/-- The section of `unitsFst` induced by `inl`. -/
def unitsInl : Rˣ →* (R[ε])ˣ :=
  Units.map (inlRingHom (R := R)).toMonoidHom

@[simp]
theorem unitsInl_apply_val (a : Rˣ) : (unitsInl a : R[ε]) = inl (a : R) :=
  rfl

/-- `unitsFst` is split by `unitsInl`; in particular it is surjective. -/
theorem unitsFst_comp_unitsInl :
    (unitsFst (R := R)).comp unitsInl = MonoidHom.id Rˣ := by
  ext a
  simp

theorem unitsFst_surjective : Function.Surjective (unitsFst (R := R)) :=
  fun a => ⟨unitsInl a, congrFun (congrArg (·.toFun) unitsFst_comp_unitsInl) a⟩

/-- The fundamental unit-inverse projection: `fst` of the inverse unit is
inverse to `fst` of the unit. -/
theorem fst_inv_mul_fst (u : (R[ε])ˣ) :
    ((u⁻¹ : (R[ε])ˣ) : R[ε]).fst * ((u : R[ε])).fst = 1 := by
  rw [← fst_mul, ← Units.val_mul, inv_mul_cancel u, Units.val_one, fst_one]

theorem fst_mul_fst_inv (u : (R[ε])ˣ) :
    ((u : R[ε])).fst * ((u⁻¹ : (R[ε])ˣ) : R[ε]).fst = 1 := by
  rw [mul_comm]
  exact fst_inv_mul_fst u

/-- **Exactness in the middle**: the range of the truncated exponential is
exactly the kernel of reduction mod `ε` on units — a unit of `R[ε]` reduces
to `1` iff it is `1 + b ε` for a (unique) `b : R`. -/
theorem truncExp_range_eq_ker_unitsFst :
    (truncExp (R := R)).range = (unitsFst (R := R)).ker := by
  ext u
  constructor
  · rintro ⟨b, rfl⟩
    exact Units.ext <| by simp
  · intro hu
    have hfst : (u : R[ε]).fst = 1 := by
      simpa [Units.ext_iff] using hu
    refine ⟨Multiplicative.ofAdd (u : R[ε]).snd, Units.ext ?_⟩
    refine TrivSqZeroExt.ext ?_ ?_
    · simpa using hfst.symm
    · simp

/-! ## §3. The splitting `(R[ε])ˣ ≃* Rˣ × (R, +)` -/

/-- **The truncated-exponential splitting** of the unit group of the dual
numbers: `(R[ε])ˣ ≃* Rˣ × (R, +)`, sending a unit `u = a + m ε` (with
`a ∈ Rˣ`) to `(a, a⁻¹ m)`; the inverse sends `(a, b)` to
`inl a · (1 + b ε) = a + (a b) ε`. This is the group-theoretic content of the
split exact sequence `1 → (R,+) → (R[ε])ˣ → Rˣ → 1`. -/
def unitsEquivProd : (R[ε])ˣ ≃* Rˣ × Multiplicative R where
  toFun u :=
    (unitsFst u,
      Multiplicative.ofAdd (((u⁻¹ : (R[ε])ˣ) : R[ε]).fst * (u : R[ε]).snd))
  invFun p := unitsInl p.1 * truncExp p.2
  left_inv u := by
    apply Units.ext
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [fst_mul]
    · simp only [Units.val_mul, unitsInl_apply_val, truncExp_apply,
        truncExpUnit_val, snd_mul, fst_inl, snd_inl, fst_add, snd_add,
        fst_one, snd_one, fst_inr, snd_inr, unitsFst_apply_val,
        toAdd_ofAdd]
      calc (u : R[ε]).fst * (0 + (((u⁻¹ : (R[ε])ˣ) : R[ε]).fst * (u : R[ε]).snd))
            + 0 * (1 + 0)
          = ((u : R[ε]).fst * ((u⁻¹ : (R[ε])ˣ) : R[ε]).fst) * (u : R[ε]).snd := by
            ring
        _ = (u : R[ε]).snd := by rw [fst_mul_fst_inv, one_mul]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    have hval : ((unitsInl a * truncExp b : (R[ε])ˣ) : R[ε])
        = inl (a : R) * (1 + inr b.toAdd) := by
      simp
    refine Prod.ext (Units.ext ?_) ?_
    · simp
    · have hsnd : ((unitsInl a * truncExp b : (R[ε])ˣ) : R[ε]).snd
          = (a : R) * b.toAdd := by
        simp
      have hfst₁ : (((unitsInl a * truncExp b)⁻¹ : (R[ε])ˣ) : R[ε]).fst * (a : R)
          = 1 := by
        have h := fst_inv_mul_fst (unitsInl a * truncExp b)
        rw [hval] at h
        simpa [fst_mul] using h
      change Multiplicative.ofAdd
          ((((unitsInl a * truncExp b)⁻¹ : (R[ε])ˣ) : R[ε]).fst
            * ((unitsInl a * truncExp b : (R[ε])ˣ) : R[ε]).snd) = b
      rw [hsnd, ← mul_assoc, hfst₁, one_mul]
      exact ofAdd_toAdd b
  map_mul' u v := by
    refine Prod.ext (map_mul _ u v) ?_
    have hkey : (((u * v)⁻¹ : (R[ε])ˣ) : R[ε]).fst * ((u * v : (R[ε])ˣ) : R[ε]).snd
        = ((u⁻¹ : (R[ε])ˣ) : R[ε]).fst * (u : R[ε]).snd
          + ((v⁻¹ : (R[ε])ˣ) : R[ε]).fst * (v : R[ε]).snd := by
      have hinv : (((u * v)⁻¹ : (R[ε])ˣ) : R[ε]).fst
          = ((v⁻¹ : (R[ε])ˣ) : R[ε]).fst * ((u⁻¹ : (R[ε])ˣ) : R[ε]).fst := by
        rw [mul_inv_rev u v, Units.val_mul, fst_mul]
      rw [hinv, Units.val_mul, DualNumber.snd_mul]
      calc ((v⁻¹ : (R[ε])ˣ) : R[ε]).fst * ((u⁻¹ : (R[ε])ˣ) : R[ε]).fst
            * ((u : R[ε]).fst * (v : R[ε]).snd + (u : R[ε]).snd * (v : R[ε]).fst)
          = (((u⁻¹ : (R[ε])ˣ) : R[ε]).fst * (u : R[ε]).fst)
              * (((v⁻¹ : (R[ε])ˣ) : R[ε]).fst * (v : R[ε]).snd)
            + (((v⁻¹ : (R[ε])ˣ) : R[ε]).fst * (v : R[ε]).fst)
              * (((u⁻¹ : (R[ε])ˣ) : R[ε]).fst * (u : R[ε]).snd) := by ring
        _ = ((u⁻¹ : (R[ε])ˣ) : R[ε]).fst * (u : R[ε]).snd
            + ((v⁻¹ : (R[ε])ˣ) : R[ε]).fst * (v : R[ε]).snd := by
            rw [fst_inv_mul_fst, fst_inv_mul_fst, one_mul, one_mul, add_comm]
    simp only [hkey]
    rfl

@[simp]
theorem unitsEquivProd_apply_fst (u : (R[ε])ˣ) :
    (unitsEquivProd u).1 = unitsFst u :=
  rfl

@[simp]
theorem unitsEquivProd_symm_apply (p : Rˣ × Multiplicative R) :
    unitsEquivProd.symm p = unitsInl p.1 * truncExp p.2 :=
  rfl

/-! ## §4. Functoriality in `R`

The sheaf-level upgrade (the truncated-exponential sequence of sheaves on the
dual-number thickening `C_ε`) needs everything above to be natural in the
base ring; `mapRingHom` is the underlying functorial ring map
`R[ε] →+* S[ε]`, applying `f` to both components. -/

/-- The functorial ring homomorphism `R[ε] →+* S[ε]` induced by a ring
homomorphism `f : R →+* S` (applies `f` to both components). -/
def mapRingHom (f : R →+* S) : R[ε] →+* S[ε] where
  toFun x := inl (f x.fst) + inr (f x.snd)
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [fst_mul]
    · simp [smul_eq_mul, mul_comm]
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp

@[simp]
theorem fst_mapRingHom (f : R →+* S) (x : R[ε]) :
    (mapRingHom f x).fst = f x.fst := by
  simp [mapRingHom]

@[simp]
theorem snd_mapRingHom (f : R →+* S) (x : R[ε]) :
    (mapRingHom f x).snd = f x.snd := by
  simp [mapRingHom]

/-- `mapRingHom` is functorial: identity. -/
theorem mapRingHom_id : mapRingHom (RingHom.id R) = RingHom.id R[ε] :=
  RingHom.ext fun _ => TrivSqZeroExt.ext (by simp) (by simp)

/-- `mapRingHom` is functorial: composition. -/
theorem mapRingHom_comp (g : S →+* T) (f : R →+* S) :
    mapRingHom (g.comp f) = (mapRingHom g).comp (mapRingHom f) :=
  RingHom.ext fun _ => TrivSqZeroExt.ext (by simp) (by simp)

/-- Naturality of the truncated exponential: `mapRingHom f` carries
`1 + b ε` to `1 + f(b) ε`. -/
theorem map_mapRingHom_truncExpUnit (f : R →+* S) (b : R) :
    Units.map (mapRingHom f).toMonoidHom (truncExpUnit b) = truncExpUnit (f b) :=
  Units.ext <| TrivSqZeroExt.ext (by simp) (by simp)

/-- Naturality of reduction mod `ε` on units: the square

```
(R[ε])ˣ → (S[ε])ˣ
   ↓          ↓
   Rˣ    →    Sˣ
```

commutes. -/
theorem unitsFst_map_mapRingHom (f : R →+* S) (u : (R[ε])ˣ) :
    unitsFst (Units.map (mapRingHom f).toMonoidHom u)
      = Units.map f.toMonoidHom (unitsFst u) :=
  Units.ext <| by simp

end DualNumber
