/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integral elements and towers

This file packages the element-level transport statements used throughout the
finite and integral extension sections of the Stacks Project.  The underlying
predicates are Mathlib's `RingHom.IsIntegralElem` and `IsIntegral`.
-/

namespace StacksPart01

/-! ### Transport of integral elements -/

/-- Integral elements remain integral after applying a ring homomorphism. -/
theorem integralElem_map
    {R S T : Type*} [CommRing R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) {x : S}
    (hx : f.IsIntegralElem x) :
    (g.comp f).IsIntegralElem (g x) := by
  exact hx.map g

/-- Along an injective ring map, integrality of an image is equivalent to
integrality of the original element. -/
theorem integralElem_map_iff_of_injective
    {R S T : Type*} [CommRing R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) (hg : Function.Injective g) {x : S} :
    (g.comp f).IsIntegralElem (g x) ↔ f.IsIntegralElem x := by
  exact RingHom.IsIntegralElem.map_iff hg

/-- If an element is integral for a composite map, it is integral for the
second map. -/
theorem integralElem_of_comp
    {R S T : Type*} [CommRing R] [CommRing S] [Ring T]
    (f : R →+* S) (g : S →+* T) {x : T}
    (hx : (g.comp f).IsIntegralElem x) :
    g.IsIntegralElem x := by
  exact RingHom.IsIntegralElem.of_comp hx

/-! ### Cancellation in towers -/

/-- If a composite ring map is integral, then its second factor is integral
(Stacks, Tag 02JM). -/
theorem ringHom_isIntegral_of_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (h : (g.comp f).IsIntegral) : g.IsIntegral := by
  exact RingHom.IsIntegral.tower_top f g h

/-- If the second map is injective and a composite is integral, then the first
map is integral. -/
theorem ringHom_isIntegral_of_comp_injective
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hg : Function.Injective g)
    (h : (g.comp f).IsIntegral) : f.IsIntegral := by
  exact RingHom.IsIntegral.tower_bot f g hg h

/-! ### Towers and integral closures -/

/-- Integrality is transitive in an algebra tower. -/
theorem isIntegral_tower
    {R A B : Type*} [CommRing R] [CommRing A] [Ring B]
    [Algebra A B] [Algebra R B] [Algebra R A]
    [IsScalarTower R A B] [Algebra.IsIntegral R A]
    (x : B) (hx : IsIntegral A x) : IsIntegral R x := by
  exact isIntegral_trans x hx

/-- For an injective algebra map, an element of the lower algebra is integral
over the base exactly when its image in the upper algebra is. -/
theorem isIntegral_algebraMap_iff_of_injective
    {R A B : Type*} [CommRing R] [CommRing A] [Ring B]
    [Algebra R A] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (hAB : Function.Injective (algebraMap A B))
    {x : A} :
    IsIntegral R ((algebraMap A B) x) ↔ IsIntegral R x := by
  exact isIntegral_algebraMap_iff hAB

/-- An integral element in an integrally closed extension comes from the base
ring. -/
theorem exists_algebraMap_eq_of_integral
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsIntegrallyClosedIn R A] {x : A} (hx : IsIntegral R x) :
    ∃ y : R, algebraMap R A y = x := by
  exact IsIntegrallyClosedIn.algebraMap_eq_of_integral hx

end StacksPart01
