/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib

/-!
# Units of the dual numbers: the truncated-exponential layer (W5-T2, unit layer)

The opening algebra brick of the Kleiman §5 Thm 5.11 tangent-space computation: for a
commutative ring `R`, the unit group of the dual numbers `R[ε]` sits in a split short
exact sequence

```
1 → (R, +) → (R[ε])ˣ → Rˣ → 1
```

where the kernel embedding is the *truncated exponential* `b ↦ 1 + b ε` (a group
homomorphism from the additive group of `R`, since `(1 + bε)(1 + cε) = 1 + (b + c)ε`),
the projection is `fst` on units, and `inl : R → R[ε]` splits it. Everything is natural
in `R` (`mapRingHom` and its compatibility lemmas), which is what the two-chart Čech
engine (`AlgebraicJacobian.Tangent.TruncExpCech`) consumes; the Mumford `ε ↦ aε`
scaling (`scaleRingHom`) provides the `k`-scalar action on truncated-exponential
classes.

Ported (Wave-5 brick T2, stage 1) from the old draft's
`Algebraic-Jacobian-Challenge/AlgebraicJacobian/Picard/DualNumberUnits.lean` and the
§0/§6-helper layer of `.../Picard/Pic0DualNumberCocycle.lean`, re-proved against the
Rebuild's pin. **Namespace note**: everything lives in the project-local namespace
`TruncExpCech` (NOT `DualNumber`) so that a concurrent verbatim port of the old
`DualNumberUnits.lean` by the T1 lane cannot collide with these declarations at the
project root; consumers (T3/T5) should use the `TruncExpCech.*` names.

## Main declarations

* `TruncExpCech.truncExpUnit : R → (R[ε])ˣ` — `1 + b ε` as a unit, additive-to-
  multiplicative (`truncExpUnit_add`), packaged as `TruncExpCech.truncExp :
  Multiplicative R →* (R[ε])ˣ`.
* `TruncExpCech.unitsFst : (R[ε])ˣ →* Rˣ` — reduction mod `ε` on units, split by
  `TruncExpCech.unitsInl`.
* `TruncExpCech.truncExp_range_eq_ker_unitsFst` — exactness in the middle.
* `TruncExpCech.unitsInl_unitsFst_mul_truncExpUnit` — the unit decomposition
  `u = inl(u₀) · (1 + c ε)` with `u₀ = fst u`, `c = fst(u⁻¹) · snd(u)`.
* `TruncExpCech.mapRingHom : (R →+* S) → (R[ε] →+* S[ε])` — functoriality, with the
  naturality lemmas `unitsFst_map_mapRingHom`, `map_mapRingHom_truncExpUnit`.
* `TruncExpCech.scaleRingHom : R → (R[ε] →+* R[ε])` — the Mumford `ε ↦ aε` scaling,
  acting on truncated exponentials by `b ↦ a·b` (`unitsScale_truncExpUnit`).

## References

Kleiman, "The Picard scheme", §5, proof of Thm 5.11 (arXiv:math/0504020); Mumford,
"Abelian varieties", §II.4.
-/

set_option autoImplicit false

universe u v w

namespace TruncExpCech

open TrivSqZeroExt DualNumber

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]

/-! ## §1. The truncated exponential -/

/-- Squares of infinitesimals vanish: `(b ε) * (c ε) = 0` in `R[ε]`. -/
theorem inr_mul_inr_eq_zero (b c : R) : (inr b : R[ε]) * inr c = 0 :=
  inr_mul_inr R b c

/-- **The truncated exponential is a unit**: `1 + b ε` is invertible in `R[ε]`, with
inverse `1 - b ε`. -/
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

/-- The truncated exponential at `0` is the unit `1`. -/
@[simp]
theorem truncExpUnit_zero : truncExpUnit (0 : R) = 1 :=
  Units.ext <| by simp

/-- Additivity of the truncated exponential: `(1 + b ε)(1 + c ε) = 1 + (b + c) ε`. -/
theorem truncExpUnit_add (b c : R) :
    truncExpUnit (b + c) = truncExpUnit b * truncExpUnit c :=
  Units.ext <| by
    calc (1 + inr (b + c) : R[ε])
        = 1 + (inr b + inr c) + inr b * inr c := by
          rw [inr_mul_inr_eq_zero, add_zero, inr_add]
      _ = (1 + inr b) * (1 + inr c) := by ring

/-- The truncated exponential is injective. -/
theorem truncExpUnit_injective : Function.Injective (truncExpUnit (R := R)) := by
  intro b c h
  have hsnd := congrArg (fun u : (R[ε])ˣ => ((u : (R[ε])ˣ) : R[ε]).snd) h
  simpa using hsnd

/-- **The truncated exponential** `b ↦ 1 + b ε` as a group homomorphism from the
additive group of `R` (written multiplicatively) to the unit group of the dual
numbers. -/
def truncExp : Multiplicative R →* (R[ε])ˣ where
  toFun b := truncExpUnit b.toAdd
  map_one' := Units.ext <| by simp
  map_mul' b c := truncExpUnit_add b.toAdd c.toAdd

@[simp]
theorem truncExp_apply (b : Multiplicative R) :
    truncExp b = truncExpUnit b.toAdd :=
  rfl

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

/-- **Reduction mod `ε` on unit groups**: the group homomorphism `(R[ε])ˣ →* Rˣ`
induced by `fst`. -/
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

/-- Reduction mod `ε` on units retracts the constant inclusion:
`unitsFst (unitsInl a) = a`. -/
@[simp]
theorem unitsFst_unitsInl (a : Rˣ) : unitsFst (unitsInl a) = a :=
  Units.ext (by simp)

/-- Truncated-exponential units reduce to `1` mod `ε`. -/
@[simp]
theorem unitsFst_truncExpUnit (b : R) : unitsFst (truncExpUnit b) = 1 :=
  Units.ext (by simp)

/-- The fundamental unit-inverse projection: `fst` of the inverse unit is inverse to
`fst` of the unit. -/
theorem fst_inv_mul_fst (u : (R[ε])ˣ) :
    ((u⁻¹ : (R[ε])ˣ) : R[ε]).fst * ((u : R[ε])).fst = 1 := by
  rw [← fst_mul, ← Units.val_mul, inv_mul_cancel u, Units.val_one, fst_one]

theorem fst_mul_fst_inv (u : (R[ε])ˣ) :
    ((u : R[ε])).fst * ((u⁻¹ : (R[ε])ˣ) : R[ε]).fst = 1 := by
  rw [mul_comm]
  exact fst_inv_mul_fst u

/-- **Exactness in the middle**: the range of the truncated exponential is exactly the
kernel of reduction mod `ε` on units — a unit of `R[ε]` reduces to `1` iff it is
`1 + b ε` for a (unique) `b : R`. -/
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

/-- **The unit decomposition of the dual numbers, equational form**: every unit of
`R[ε]` is the constant inclusion of its reduction times a truncated exponential —
`u = inl(u₀) · (1 + c ε)` with `u₀ = unitsFst u` and `c = fst(u⁻¹) · snd(u)`. -/
theorem unitsInl_unitsFst_mul_truncExpUnit (u : (R[ε])ˣ) :
    unitsInl (unitsFst u)
        * truncExpUnit (((u⁻¹ : (R[ε])ˣ) : R[ε]).fst * ((u : (R[ε])ˣ) : R[ε]).snd)
      = u := by
  apply Units.ext
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [fst_mul]
  · simp only [Units.val_mul, unitsInl_apply_val, truncExpUnit_val,
      DualNumber.snd_mul, unitsFst_apply_val]
    calc (u : R[ε]).fst * (0 + ((u⁻¹ : (R[ε])ˣ) : R[ε]).fst * (u : R[ε]).snd)
          + 0 * (1 + 0)
        = ((u : R[ε]).fst * ((u⁻¹ : (R[ε])ˣ) : R[ε]).fst) * (u : R[ε]).snd := by ring
      _ = (u : R[ε]).snd := by rw [fst_mul_fst_inv, one_mul]

/-! ## §3. Functoriality in `R` -/

/-- The functorial ring homomorphism `R[ε] →+* S[ε]` induced by a ring homomorphism
`f : R →+* S` (applies `f` to both components). -/
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

/-- `mapRingHom` intertwines the constant inclusions:
`mapRingHom f (inl a) = inl (f a)`. -/
theorem mapRingHom_inl (f : R →+* S) (a : R) :
    mapRingHom f (inl a : R[ε]) = (inl (f a) : S[ε]) :=
  TrivSqZeroExt.ext (by simp) (by simp)

/-- `mapRingHom` intertwines the unit-level constant inclusions `unitsInl`. -/
theorem unitsMap_mapRingHom_unitsInl (f : R →+* S) (v : Rˣ) :
    Units.map (mapRingHom f).toMonoidHom (unitsInl v)
      = unitsInl (Units.map f.toMonoidHom v) :=
  Units.ext (by simpa using mapRingHom_inl f (v : R))

/-- Naturality of the truncated exponential: `mapRingHom f` carries `1 + b ε` to
`1 + f(b) ε`. -/
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

/-! ## §4. The Mumford `ε ↦ aε` scaling -/

/-- **The `ε ↦ aε` scaling of the dual numbers**: `TrivSqZeroExt.map` of scalar
multiplication by `a` on the infinitesimal part, as a ring homomorphism
`R[ε] →+* R[ε]`, `r + m ε ↦ r + (a m) ε`. Mumford's `k`-module structure on the tangent
space `T_e F` of a functor at a rational point scales tangent vectors by functoriality
along it ("Abelian varieties", §II.4). -/
def scaleRingHom (a : R) : R[ε] →+* R[ε] :=
  (TrivSqZeroExt.map (a • (LinearMap.id : R →ₗ[R] R))).toRingHom

@[simp]
theorem fst_scaleRingHom (a : R) (x : R[ε]) : (scaleRingHom a x).fst = x.fst := by
  simp [scaleRingHom]

@[simp]
theorem snd_scaleRingHom (a : R) (x : R[ε]) : (scaleRingHom a x).snd = a * x.snd := by
  simp [scaleRingHom]

/-- Scalings compose multiplicatively: `(ε ↦ aε) ∘ (ε ↦ bε) = (ε ↦ (ab)ε)`. -/
theorem scaleRingHom_comp_scaleRingHom (a b : R) :
    (scaleRingHom a).comp (scaleRingHom b) = scaleRingHom (a * b) :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp) (by simp [mul_assoc])

/-- Scaling by `1` is the identity. -/
theorem scaleRingHom_one : scaleRingHom (1 : R) = RingHom.id R[ε] :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp) (by simp)

/-- The Mumford `ε ↦ aε` scaling acts on truncated-exponential units by scaling the
infinitesimal: `(1 + b ε) ↦ (1 + (a b) ε)`. -/
theorem unitsScale_truncExpUnit (a b : R) :
    Units.map (scaleRingHom a).toMonoidHom (truncExpUnit b) = truncExpUnit (a * b) :=
  Units.ext (TrivSqZeroExt.ext (by simp) (by simp))

/-- The Mumford scaling is compatible with the functorial map of dual-number rings:
`mapRingHom ρ ∘ scaleRingHom s = scaleRingHom (ρ s) ∘ mapRingHom ρ`. -/
theorem mapRingHom_comp_scaleRingHom (ρ : R →+* S) (s : R) :
    (mapRingHom ρ).comp (scaleRingHom s) = (scaleRingHom (ρ s)).comp (mapRingHom ρ) :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp) (by simp)

end TruncExpCech
