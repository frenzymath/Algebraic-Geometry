/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianDataAbel

/-!
# Canonicality of the datum-level Abel map

The representability producer is intentionally independent of the frozen
`Challenge.Jacobian` declaration.  Once a `JacobianData` is available, however,
the Abel map is canonical: the canonical isomorphism between any two representing
objects carries the Abel map of one datum to the Abel map of the other.

This is the useful cycle-free headline bridge.  It uses only the stabilized
finite-stage consumer API (`homEquiv`, `ofCurve`, and `uniqueUpToIso`), so it does
not assert an unconditional producer or hide the remaining arbitrary-field
representability obligation behind an instance.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

namespace JacobianData

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-- The canonical comparison isomorphism between two Jacobian data carries the
Abel-Jacobi map of every rational point to the corresponding map for the second
datum.  Both sides classify the same `abelElement`. -/
theorem uniqueUpToIso_hom_comp_ofCurve (d d' : JacobianData C)
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    d.ofCurve P ≫ (d.uniqueUpToIso d').hom = d'.ofCurve P := by
  apply d'.homEquiv.injective
  rw [d.homEquiv_uniqueUpToIso_hom, d'.homEquiv_ofCurve, d.homEquiv_ofCurve]

/-- The inverse canonical comparison carries the second datum's Abel map back to
the first one.  This is a convenient orientation for base-change consumers. -/
theorem uniqueUpToIso_inv_comp_ofCurve (d d' : JacobianData C)
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    d'.ofCurve P ≫ (d.uniqueUpToIso d').inv = d.ofCurve P := by
  have h := congrArg (fun q => q ≫ (d.uniqueUpToIso d').inv)
    (uniqueUpToIso_hom_comp_ofCurve d d' P)
  simpa [Category.assoc] using h.symm

/-! ## Definitional API checks

These examples keep the comparison theorem's intended use visible at the exact
`Over`/`JacobianData` types, without introducing any new assumptions or instances.
-/

example (d : JacobianData C) (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    d.ofCurve P ≫ (d.uniqueUpToIso d).hom = d.ofCurve P := by
  simpa using uniqueUpToIso_hom_comp_ofCurve d d P

example (d d' : JacobianData C) (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    d'.ofCurve P ≫ (d.uniqueUpToIso d').inv = d.ofCurve P := by
  exact uniqueUpToIso_inv_comp_ofCurve d d' P

end JacobianData

end AlgebraicGeometry
