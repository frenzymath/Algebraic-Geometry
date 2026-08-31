/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.BaseFieldTransition
import AlgebraicJacobian.RiemannRoch.ChartColength

/-!
# EV-2: the generic-rank dictionary for a finite dominant morphism (E-v campaign)

For a finite morphism `f : X ⟶ Y` of integral schemes hitting the generic point
(`f(η_X) = η_Y`) and an affine chart `V ∋ η_Y`, this file proves the **generic-rank
dictionary** of the E-v campaign (`informal/w7-ev-worksheet.md` §2 EV-2): the degree of
the function-field extension equals the rank of the chart extension,

`[K(X) : K(Y)] = finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V)`.

Pinned route (ratified, probe EV-D′): the single mathlib lemma
`Algebra.IsAlgebraic.finrank_of_isFractionRing` applied to the square

```
Γ(Y, V)  ⟶  Γ(X, f ⁻¹ᵁ V)
   |               |
  germ            germ
   ↓               ↓
  K(Y)   ⟶      K(X)
```

with the four `[S]` legs: module finiteness of the chart extension
(`f.appLE` is integral + of finite type, glued by
`RingHom.finite_iff_isIntegral_and_finiteType`), faithfulness (injectivity of `f.appLE`
through the function-field seams `functionFieldMap_germ`/`functionFieldMap_injective`),
the mathlib fraction-ring identifications
(`functionField_isFractionRing_of_isAffineOpen` on both curves), and the scalar towers.

## The `letI` tower discipline (R-EV-1)

All morphism-dependent algebra structures are **owned by named defs in this file**, with
`algebraMap` unfolding lemmas; consumers (EV-3/EV-4, `RiemannRoch/DegreePullback.lean`)
activate the same named defs by `letI` and never inline `toAlgebra`:

* `Scheme.Hom.pullbackSectionsAlgebra` — `Γ(Y, V)`-algebra on `Γ(X, f ⁻¹ᵁ V)` via
  `f.appLE`;
* `Scheme.Hom.functionFieldAlgebra` — `K(Y)`-algebra on `K(X)` via `f.functionFieldMap`;
* `Scheme.Hom.pullbackSectionsFunctionFieldAlgebra` — the composite
  `Γ(Y, V) → Γ(X, f ⁻¹ᵁ V) → K(X)`, making the first tower leg definitional.

The `K`-structure seam is the landed `Scheme.Hom.appLE_overAlgebraMap`
(`Cohomology/FinitenessP1.lean`): pullback of sections commutes with the structure maps
`Scheme.overAlgebraMap` of two schemes over `Spec K`; EV-3 builds its residue-field
towers from it against the SB-3 conventions.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.moduleFinite_pullbackSections` — the chart extension is
  module-finite for finite `f`.
* `AlgebraicGeometry.Scheme.Hom.faithfulSMul_pullbackSections` — the chart extension is
  injective for dominant `f` (through the generic germ).
* `AlgebraicGeometry.Scheme.Hom.finrank_functionField_eq_finrank_pullbackSections` —
  **EV-2**, the keystone.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-! ## The named algebra towers (owned here, R-EV-1) -/

section Towers

variable {X Y : Scheme.{u}}

/-- **The chart-extension algebra**: for `f : X ⟶ Y` and an open `V` of `Y`, the
`Γ(Y, V)`-algebra structure on `Γ(X, f ⁻¹ᵁ V)` by restriction of scalars along the
pullback of sections `f.appLE`.  Deliberately not an instance (it depends on `f`);
consumers activate it with `letI := f.pullbackSectionsAlgebra V` — always through this
named def, never by inlining `toAlgebra` (R-EV-1). -/
@[reducible] noncomputable def Scheme.Hom.pullbackSectionsAlgebra (f : X ⟶ Y)
    (V : Y.Opens) : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) :=
  (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.toAlgebra

/-- Unfolding lemma: the structure map of `pullbackSectionsAlgebra` is `f.appLE`. -/
lemma Scheme.Hom.algebraMap_pullbackSectionsAlgebra (f : X ⟶ Y) (V : Y.Opens) :
    letI := f.pullbackSectionsAlgebra V
    algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V) = (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom :=
  rfl

/-- **The function-field-extension algebra**: the `K(Y)`-algebra structure on `K(X)` by
restriction of scalars along the landed `Scheme.Hom.functionFieldMap`.  This is the
algebra in which the EV-main multiplier `n = [K(X) : K(Y)]` is stated. -/
@[reducible] noncomputable def Scheme.Hom.functionFieldAlgebra [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y)
    (hf : f.base (genericPoint X) = genericPoint Y) :
    Algebra Y.functionField X.functionField :=
  (f.functionFieldMap hf).hom.toAlgebra

/-- Unfolding lemma: the structure map of `functionFieldAlgebra` is `functionFieldMap`. -/
lemma Scheme.Hom.algebraMap_functionFieldAlgebra [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) (hf : f.base (genericPoint X) = genericPoint Y) :
    letI := f.functionFieldAlgebra hf
    algebraMap Y.functionField X.functionField = (f.functionFieldMap hf).hom :=
  rfl

/-- **The mixed tower corner**: the `Γ(Y, V)`-algebra structure on `K(X)`, defined as the
literal composite of the chart extension with the generic germ of the source, so that the
tower `Γ(Y, V) → Γ(X, f ⁻¹ᵁ V) → K(X)` holds definitionally. -/
@[reducible] noncomputable def Scheme.Hom.pullbackSectionsFunctionFieldAlgebra
    [IrreducibleSpace X] (f : X ⟶ Y) (V : Y.Opens) [Nonempty (f ⁻¹ᵁ V)] :
    Algebra Γ(Y, V) X.functionField :=
  ((X.germToFunctionField (f ⁻¹ᵁ V)).hom.comp (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom).toAlgebra

/-- **First tower leg** (definitional): `Γ(Y, V) → Γ(X, f ⁻¹ᵁ V) → K(X)` commutes, where
the last leg is mathlib's canonical generic-germ algebra. -/
theorem Scheme.Hom.isScalarTower_pullbackSections_functionField [IrreducibleSpace X]
    (f : X ⟶ Y) (V : Y.Opens) [Nonempty (f ⁻¹ᵁ V)] :
    letI := f.pullbackSectionsAlgebra V
    letI := f.pullbackSectionsFunctionFieldAlgebra V
    IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) X.functionField := by
  letI := f.pullbackSectionsAlgebra V
  letI := f.pullbackSectionsFunctionFieldAlgebra V
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- **Second tower leg** (the germ-naturality seam `functionFieldMap_germ`):
`Γ(Y, V) → K(Y) → K(X)` commutes, where `Γ(Y, V) → K(Y)` is mathlib's canonical
generic-germ algebra. -/
theorem Scheme.Hom.isScalarTower_functionFieldAlgebra [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) (hf : f.base (genericPoint X) = genericPoint Y)
    {V : Y.Opens} (hη : genericPoint Y ∈ V) [Nonempty V] [Nonempty (f ⁻¹ᵁ V)] :
    letI := f.functionFieldAlgebra hf
    letI := f.pullbackSectionsFunctionFieldAlgebra V
    IsScalarTower Γ(Y, V) Y.functionField X.functionField := by
  letI := f.functionFieldAlgebra hf
  letI := f.pullbackSectionsFunctionFieldAlgebra V
  have hηW : genericPoint X ∈ f ⁻¹ᵁ V := by
    change f.base (genericPoint X) ∈ V
    rw [hf]
    exact hη
  refine IsScalarTower.of_algebraMap_eq fun s => ?_
  have happ : f.appLE V (f ⁻¹ᵁ V) le_rfl = f.app V := Scheme.Hom.appLE_eq_app f
  have hgerm := f.functionFieldMap_germ hf V hη hηW s
  calc (X.germToFunctionField (f ⁻¹ᵁ V)).hom ((f.appLE V (f ⁻¹ᵁ V) le_rfl).hom s)
      = (X.presheaf.germ (f ⁻¹ᵁ V) (genericPoint X) hηW).hom ((f.app V).hom s) := by
        rw [happ]
    _ = (f.functionFieldMap hf).hom
          ((Y.presheaf.germ V (genericPoint Y) hη).hom s) := hgerm.symm
    _ = (f.functionFieldMap hf).hom (algebraMap Γ(Y, V) Y.functionField s) := rfl

end Towers

/-! ## The four legs -/

section Legs

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Module finiteness of the chart extension** (EV-2 leg 1): for a finite morphism `f`
and an affine chart `V`, the pullback of sections `Γ(Y, V) → Γ(X, f ⁻¹ᵁ V)` is module
finite — `f.appLE` is integral (`IsIntegralHom` from `IsFinite`) and of finite type
(`LocallyOfFiniteType` from `IsFinite`), glued by
`RingHom.finite_iff_isIntegral_and_finiteType`. -/
theorem Scheme.Hom.moduleFinite_pullbackSections [IsFinite f] {V : Y.Opens}
    (hV : IsAffineOpen V) :
    letI := f.pullbackSectionsAlgebra V
    Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := by
  letI := f.pullbackSectionsAlgebra V
  have happ : f.appLE V (f ⁻¹ᵁ V) le_rfl = f.app V := Scheme.Hom.appLE_eq_app f
  have hint : RingHom.IsIntegral (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom := by
    rw [happ]
    exact f.isIntegral_app V hV
  have hft : RingHom.FiniteType (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom :=
    f.finiteType_appLE hV (hV.preimage f) le_rfl
  exact RingHom.finite_iff_isIntegral_and_finiteType.mpr ⟨hint, hft⟩

/-- **Injectivity of the chart extension** (EV-2 leg 2): for a morphism of integral
schemes hitting the generic point, the pullback of sections on a chart around `η_Y` is
injective — the generic germ of the pulled section is the function-field image of the
generic germ, `functionFieldMap` is injective, and generic germs on integral schemes are
injective. -/
theorem Scheme.Hom.faithfulSMul_pullbackSections [IsIntegral X] [IsIntegral Y]
    (hf : f.base (genericPoint X) = genericPoint Y) {V : Y.Opens}
    (hη : genericPoint Y ∈ V) :
    letI := f.pullbackSectionsAlgebra V
    FaithfulSMul Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := by
  letI := f.pullbackSectionsAlgebra V
  have hηW : genericPoint X ∈ f ⁻¹ᵁ V := by
    change f.base (genericPoint X) ∈ V
    rw [hf]
    exact hη
  refine (faithfulSMul_iff_algebraMap_injective Γ(Y, V) Γ(X, f ⁻¹ᵁ V)).mpr ?_
  have happ : f.appLE V (f ⁻¹ᵁ V) le_rfl = f.app V := Scheme.Hom.appLE_eq_app f
  intro a b hab
  change (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom a = (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom b at hab
  rw [happ] at hab
  have hgerm : (f.functionFieldMap hf).hom
        ((Y.presheaf.germ V (genericPoint Y) hη).hom a)
      = (f.functionFieldMap hf).hom
        ((Y.presheaf.germ V (genericPoint Y) hη).hom b) := by
    rw [f.functionFieldMap_germ hf V hη hηW a, f.functionFieldMap_germ hf V hη hηW b, hab]
  exact germ_injective_of_isIntegral Y (genericPoint Y) hη
    (f.functionFieldMap_injective hf hgerm)

end Legs

/-! ## EV-2: the generic-rank dictionary -/

section Keystone

variable {X Y : Scheme.{u}}

/-- **EV-2, the generic-rank dictionary** (`informal/w7-ev-worksheet.md` §2, keystone):
for a finite morphism `f : X ⟶ Y` of integral schemes hitting the generic point and an
affine chart `V ∋ η_Y`,

`[K(X) : K(Y)] = finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V)`,

with the function-field degree taken along `f.functionFieldMap` and the chart rank along
`f.appLE`.  Pinned route (probe EV-D′): mathlib's
`Algebra.IsAlgebraic.finrank_of_isFractionRing` at the fraction-ring square
`Γ(Y, V) → Γ(X, f ⁻¹ᵁ V)`, `K(Y) → K(X)` — the finiteness and faithfulness legs are
`moduleFinite_pullbackSections`/`faithfulSMul_pullbackSections`, the fraction-ring legs
are mathlib's `functionField_isFractionRing_of_isAffineOpen` on both schemes, and the
towers are the file's named legs. -/
theorem Scheme.Hom.finrank_functionField_eq_finrank_pullbackSections
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsFinite f]
    (hf : f.base (genericPoint X) = genericPoint Y)
    {V : Y.Opens} (hV : IsAffineOpen V) (hη : genericPoint Y ∈ V) :
    letI := f.functionFieldAlgebra hf
    letI := f.pullbackSectionsAlgebra V
    Module.finrank Y.functionField X.functionField
      = Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := by
  letI := f.functionFieldAlgebra hf
  letI := f.pullbackSectionsAlgebra V
  have hηW : genericPoint X ∈ f ⁻¹ᵁ V := by
    change f.base (genericPoint X) ∈ V
    rw [hf]
    exact hη
  haveI : Nonempty V := ⟨⟨_, hη⟩⟩
  haveI : Nonempty (f ⁻¹ᵁ V) := ⟨⟨_, hηW⟩⟩
  letI := f.pullbackSectionsFunctionFieldAlgebra V
  haveI := f.moduleFinite_pullbackSections hV
  haveI := f.faithfulSMul_pullbackSections hf hη
  haveI : IsFractionRing Γ(Y, V) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y V hV
  haveI : IsFractionRing Γ(X, f ⁻¹ᵁ V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (f ⁻¹ᵁ V) (hV.preimage f)
  haveI := f.isScalarTower_pullbackSections_functionField V
  haveI := f.isScalarTower_functionFieldAlgebra hf hη
  exact Algebra.IsAlgebraic.finrank_of_isFractionRing _ _ _ _

end Keystone

end AlgebraicGeometry
