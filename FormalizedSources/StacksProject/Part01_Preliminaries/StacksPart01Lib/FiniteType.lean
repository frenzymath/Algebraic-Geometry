/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import Mathlib.RingTheory.FinitePresentation

/-!
# Finite type and finite presentation

The permanence properties of finite-type and finitely presented ring maps
(Stacks Project, Tag 00F4).
-/

namespace StacksPart01Lib

/-- Finite-type ring maps are stable under composition.

This is the first permanence assertion in the Stacks Project's composition
lemma (Tag `00F4`): if `R ⟶ S` and `S ⟶ T` are finite type, then the composite
`R ⟶ T` is finite type. -/
theorem ringHom_finiteType_comp {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] (f : R →+* S) (g : S →+* T) (hf : f.FiniteType)
    (hg : g.FiniteType) : (g.comp f).FiniteType := by
  exact RingHom.FiniteType.comp hg hf

/-- Finitely presented ring maps are stable under composition
(Stacks, Tag `00F4`, part 2). -/
theorem ringHom_finitePresentation_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hf : f.FinitePresentation)
    (hg : g.FinitePresentation) : (g.comp f).FinitePresentation := by
  exact RingHom.FinitePresentation.comp hg hf

/-- If a composite ring map is of finite type, then its second factor is of
finite type (Stacks, Tag `00F4`, part 3). -/
theorem ringHom_finiteType_of_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : (g.comp f).FiniteType) :
    g.FiniteType := by
  exact RingHom.FiniteType.of_comp_finiteType h

/-- A finitely presented composite has finitely presented second factor when
the first factor is of finite type (Stacks, Tag `00F4`, part 4). -/
theorem ringHom_finitePresentation_of_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hgf : (g.comp f).FinitePresentation)
    (hf : f.FiniteType) : g.FinitePresentation := by
  exact RingHom.FinitePresentation.of_comp_finiteType f hgf hf

end StacksPart01Lib
