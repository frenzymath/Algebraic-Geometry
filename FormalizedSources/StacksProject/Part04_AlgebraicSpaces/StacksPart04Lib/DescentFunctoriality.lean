/-
Copyright (c) 2026 The StacksPart04Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart04Lib Contributors
-/

import StacksPart04Lib.Descent

/-!
# Functoriality of pointwise descent sections

The descent section construction is functorial both in the coefficient
diagram and in the indexing category.  These elementary identities are the
categorical bookkeeping used when descent data are pulled back or compared.
-/

namespace StacksPart04Lib

open CategoryTheory

universe u v w

namespace DescentSection

variable {C : Type u} [Category.{v} C] {F G H : C ⥤ Type w}

/-- Transport along an identity natural transformation does not change a
descent section. -/
@[simp]
theorem transport_id (s : DescentSection F) :
    map (𝟙 F) s = s := by
  apply ext
  intro X
  simp [map_value]

/-- Transport along a composite is the composite of the transports. -/
@[simp]
theorem transport_comp (α : F ⟶ G) (β : G ⟶ H) (s : DescentSection F) :
    map (α ≫ β) s = map β (map α s) := by
  apply ext
  intro X
  simp [map_value, NatTrans.comp_app]

/-- Pointwise equal natural transformations induce the same transport on
descent sections. -/
theorem map_congr {α β : F ⟶ G} (h : ∀ X : C, α.app X = β.app X)
    (s : DescentSection F) :
    map α s = map β s := by
  apply ext
  intro X
  rw [map_value, map_value, h]

/-- Pullback of a transported section agrees with transport after pulling back
the natural transformation. -/
theorem pullback_map {D : Type u} [Category.{v} D]
    (K : D ⥤ C) (α : F ⟶ G) (s : DescentSection F) :
    pullback K (map α s) = map (K.whiskerLeft α) (pullback K s) := by
  apply ext
  intro X
  rfl

/-- Pullback respects transport along a composite natural transformation. -/
theorem pullback_transport_comp {D : Type u} [Category.{v} D]
    (K : D ⥤ C) (α : F ⟶ G) (β : G ⟶ H) (s : DescentSection F) :
    pullback K (map (α ≫ β) s) =
      map (K.whiskerLeft β) (map (K.whiskerLeft α) (pullback K s)) := by
  rw [pullback_map, K.whiskerLeft_comp, transport_comp]

/-! ### Coefficient isomorphisms -/

/-- Transport along the two directions of a coefficient isomorphism cancels. -/
theorem map_iso_hom_inv (e : F ≅ G) (s : DescentSection F) :
    map e.inv (map e.hom s) = s := by
  apply ext
  intro X
  simp [map_value]

/-- Transport along the inverse directions of a coefficient isomorphism cancels. -/
theorem map_iso_inv_hom (e : F ≅ G) (t : DescentSection G) :
    map e.hom (map e.inv t) = t := by
  apply ext
  intro X
  simp [map_value]

end DescentSection

end StacksPart04Lib
