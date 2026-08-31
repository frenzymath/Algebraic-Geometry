/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Algebra.DirectLimitQuotient
import AlgebraicJacobian.Picard.DivSchemeHighWindowChartExhaustion
import AlgebraicJacobian.Picard.DivSchemeHighWindowRelations
import AlgebraicJacobian.Picard.DivSchemeRedesignChartReadIdeal

/-!
# The high-window colimit and the genuine chart quotient

The high divisor-scheme windows have changing finite ambient modules, so the fixed-ambient
result `Submodule.directLimitQuotientEquivISup` does not apply directly.  This file supplies
its varying-ambient counterpart.  Compatible quotients `G i / K i` map to a fixed ideal
quotient `B / J`; the induced map from their direct limit is an equivalence provided that

* the readings of the ambients exhaust `B`, and
* an element whose reading lies in `J` enters `K` at some later stage.

For the universal divisor chart, the first condition follows from denominator clearing in
`DivSchemeHighWindowChartExhaustion`.  The second is exactly the relative saturation/kernel
statement: it is not inferred from residue-field persistence.

Consequently the final theorem below reduces flatness of the genuine chart quotient to
flatness of all finite high-window quotients plus that explicit saturation statement.  It
does not assume that the recursively generated relation modules are Grassmannian points.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 8000

universe u v w

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace Submodule

section VaryingAmbient

variable {R : Type u} [CommRing R]
variable {B : Type v} [CommRing B] [Algebra R B]
variable {ι : Type w} [Preorder ι]
variable {G : ι → Type v} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
variable (K : ∀ i, Submodule R (G i))
variable (hK : ∀ i j (hij : i ≤ j), Submodule.map (f i j hij) (K i) ≤ K j)

/-- The quotient transition induced by a compatible map between changing ambient modules. -/
noncomputable def directedQuotientMapOfCompatible (i j : ι) (hij : i ≤ j) :
    (G i ⧸ K i) →ₗ[R] (G j ⧸ K j) :=
  (K i).mapQ (K j) (f i j hij) (by
    intro x hx
    exact hK i j hij ⟨x, hx, rfl⟩)

@[simp]
theorem directedQuotientMapOfCompatible_mk (i j : ι) (hij : i ≤ j) (x : G i) :
    directedQuotientMapOfCompatible f K hK i j hij (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f i j hij x) := by
  rw [directedQuotientMapOfCompatible, Submodule.mapQ_apply]

noncomputable instance directedSystem_directedQuotientMapOfCompatible
    [DirectedSystem G (f · · ·)] :
    DirectedSystem (fun i ↦ G i ⧸ K i)
      (directedQuotientMapOfCompatible f K hK · · ·) where
  map_self i y := by
    induction y using Submodule.Quotient.induction_on with
    | _ x =>
      rw [directedQuotientMapOfCompatible_mk,
        DirectedSystem.map_self' f x]
  map_map k j i hij hjk y := by
    induction y using Submodule.Quotient.induction_on with
    | _ x =>
      rw [directedQuotientMapOfCompatible_mk,
        directedQuotientMapOfCompatible_mk,
        directedQuotientMapOfCompatible_mk,
        DirectedSystem.map_map' f hij hjk x]

variable (read : ∀ i, G i →ₗ[R] B) (J : Ideal B)
variable (hreadK : ∀ i, K i ≤ LinearMap.ker
  ((Ideal.Quotient.mkₐ R J).toLinearMap.comp (read i)))

/-- Read one bounded quotient into the fixed ideal quotient. -/
noncomputable def quotientReadMap (i : ι) : (G i ⧸ K i) →ₗ[R] (B ⧸ J) :=
  (K i).liftQ ((Ideal.Quotient.mkₐ R J).toLinearMap.comp (read i)) (hreadK i)

omit [Preorder ι] in
@[simp]
theorem quotientReadMap_mk (i : ι) (x : G i) :
    quotientReadMap K read J hreadK i (Submodule.Quotient.mk x) =
      Ideal.Quotient.mk J (read i x) := by
  rw [quotientReadMap, Submodule.liftQ_apply, LinearMap.comp_apply]
  rfl

variable (hread : ∀ i j (hij : i ≤ j) (x : G i),
  read j (f i j hij x) = read i x)

include hread in
theorem quotientReadMap_compat (i j : ι) (hij : i ≤ j) (y : G i ⧸ K i) :
    quotientReadMap K read J hreadK j
        (directedQuotientMapOfCompatible f K hK i j hij y) =
      quotientReadMap K read J hreadK i y := by
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    rw [directedQuotientMapOfCompatible_mk, quotientReadMap_mk,
      quotientReadMap_mk, hread]

variable [Nonempty ι] [IsDirectedOrder ι]

noncomputable local instance instDecidableEqVaryingAmbient : DecidableEq ι :=
  Classical.decEq ι

include hreadK hread in
/-- The map from the direct limit of bounded quotients to the fixed ideal quotient. -/
noncomputable def directLimitQuotientToIdeal :
    Module.DirectLimit (fun i ↦ G i ⧸ K i)
        (directedQuotientMapOfCompatible f K hK) →ₗ[R] (B ⧸ J) :=
  Module.DirectLimit.lift R ι _ _
    (quotientReadMap K read J hreadK)
    (quotientReadMap_compat f K hK read J hreadK hread)

omit [Nonempty ι] [IsDirectedOrder ι] in
@[simp]
theorem directLimitQuotientToIdeal_of_mk (i : ι) (x : G i) :
    directLimitQuotientToIdeal f K hK read J hreadK hread
        (Module.DirectLimit.of R ι _
          (directedQuotientMapOfCompatible f K hK) i
          (Submodule.Quotient.mk x)) =
      Ideal.Quotient.mk J (read i x) := by
  rw [directLimitQuotientToIdeal, Module.DirectLimit.lift_of,
    quotientReadMap_mk]

include hreadK hread in
/-- A varying-ambient quotient system has colimit `B / J` when readings exhaust `B`
and membership in `J` is detected by eventual membership in the bounded kernels. -/
noncomputable def directLimitQuotientEquivIdeal
    [DirectedSystem G (f · · ·)]
    (hcover : ∀ b : B, ∃ i : ι, ∃ x : G i, read i x = b)
    (hsaturation : ∀ i (x : G i), read i x ∈ J →
      ∃ j : ι, ∃ hij : i ≤ j, f i j hij x ∈ K j) :
    Module.DirectLimit (fun i ↦ G i ⧸ K i)
        (directedQuotientMapOfCompatible f K hK) ≃ₗ[R] (B ⧸ J) :=
  LinearEquiv.ofBijective
    (directLimitQuotientToIdeal f K hK read J hreadK hread) ⟨by
      have hker : ∀ z,
          directLimitQuotientToIdeal f K hK read J hreadK hread z = 0 → z = 0 := by
        intro z hz
        obtain ⟨i, y, hy⟩ := Module.DirectLimit.exists_of z
        obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (K i) y
        rw [← hy, ← hx] at hz ⊢
        simp only [Submodule.mkQ_apply] at hz ⊢
        rw [directLimitQuotientToIdeal_of_mk] at hz
        have hxJ : read i x ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hz
        obtain ⟨j, hij, hxK⟩ := hsaturation i x hxJ
        rw [← Module.DirectLimit.of_f (hij := hij),
          directedQuotientMapOfCompatible_mk,
          (Submodule.Quotient.mk_eq_zero _).mpr hxK, map_zero]
      intro z w hzw
      apply sub_eq_zero.mp (hker (z - w) ?_)
      rw [map_sub, hzw, sub_self],
    by
      intro y
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨i, x, hx⟩ := hcover b
      refine ⟨Module.DirectLimit.of R ι _
        (directedQuotientMapOfCompatible f K hK) i
        (Submodule.Quotient.mk x), ?_⟩
      rw [directLimitQuotientToIdeal_of_mk, hx]⟩

include hK hreadK hread in
/-- Flat bounded quotients give a flat ideal quotient once the varying-ambient colimit
conditions are available. -/
theorem flat_quotient_of_directLimit
    [DirectedSystem G (f · · ·)]
    (hcover : ∀ b : B, ∃ i : ι, ∃ x : G i, read i x = b)
    (hsaturation : ∀ i (x : G i), read i x ∈ J →
      ∃ j : ι, ∃ hij : i ≤ j, f i j hij x ∈ K j)
    [∀ i, Module.Flat R (G i ⧸ K i)] : Module.Flat R (B ⧸ J) := by
  letI : Module.Flat R
      (Module.DirectLimit (fun i ↦ G i ⧸ K i)
        (directedQuotientMapOfCompatible f K hK)) :=
    Module.Flat.directLimit (directedQuotientMapOfCompatible f K hK)
  exact Module.Flat.of_linearEquiv
    (directLimitQuotientEquivIdeal f K hK read J hreadK hread
      hcover hsaturation).symm

end VaryingAmbient

end Submodule

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section UniversalHighWindowDirectLimit

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [hSmoothC : SmoothOfRelativeDimension 1 C.hom] [hProperC : IsProper C.hom]
  [hGeometricallyIrreducibleC : GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowDirectLimit :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k ((windowS_choice pi hpi g • fiberWeilDivisor pi)
    + (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j

/-- Read the `n`-th high-window ambient into one pinned affine chart. -/
noncomputable def divUniversalHighWindowChartRead (n : Nat) (side : Bool) :
    divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n →ₗ[RZ]
      Γ(relCurve C RZ, relPinnedChart C RZ pi side) :=
  (relThetaResSide
      (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n)
      side le_rfl).comp
    (divUniversalHighWindowThetaEquiv (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n).toLinearMap

set_option maxHeartbeats 800000 in
-- Expanding the high-window theta equivalence exceeds the default elaboration budget.
set_option synthInstance.maxHeartbeats 400000 in
-- The relative theta restriction map requires additional instance-synthesis time.
omit hSmoothC hProperC hGeometricallyIrreducibleC in
/-- Every pinned-chart section is read from one of the finite high-window ambients. -/
theorem exists_divUniversalHighWindowChartRead_eq
    (hb : 0 < windowBound pi hpi) (side : Bool)
    (x : Γ(relCurve C RZ, relPinnedChart C RZ pi side)) :
    ∃ n : Nat, ∃ y : divUniversalHighWindowAmbient (C := C) (pi := pi)
        (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
        (i := i) (j := j) n,
      divUniversalHighWindowChartRead (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n side y = x := by
  obtain ⟨n, s, hs⟩ :=
    exists_highWindow_relThetaResSide_eq_of_windowBound_pos
      C pi hpi RZ g hb side x
  refine ⟨n, (divUniversalHighWindowThetaEquiv (C := C) (pi := pi)
    hpi g r1 r2 b1 b2 i j n).symm s, ?_⟩
  change relThetaResSide
      (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n)
      side le_rfl
      ((divUniversalHighWindowThetaEquiv (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n)
        ((divUniversalHighWindowThetaEquiv (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n).symm s)) = x
  rw [LinearEquiv.apply_symm_apply, hs]

/-- The ideal generated by readings of the recursive relation module at stage `n`. -/
noncomputable def divUniversalHighWindowRelationReadIdeal (n : Nat) (side : Bool) :
    Ideal Γ(relCurve C RZ, relPinnedChart C RZ pi side) :=
  Ideal.span (Set.range
    ((divUniversalHighWindowChartRead (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n side).comp
        (divUniversalHighWindowRelation (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n).subtype))

end UniversalHighWindowDirectLimit

end AlgebraicGeometry
