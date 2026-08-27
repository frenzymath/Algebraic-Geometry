/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.Presheaf
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.SheafProperty
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.Carriers

/-!
# Sheaves of `k`-modules: sheafification, Ext, and the structure sheaf (re-export)

Phase A step 5 (per `STRATEGY.md`) is split across three sub-files:

* `StructureSheafModuleK/Presheaf.lean` — categorical gap-fills (the
  `CategoryTheory.Functor.const_*` / `CategoryTheory.Adjunction.*` instances),
  the `HasSheafify` / `HasExt` typeclass prerequisites, the per-open ring-map
  helpers (1)–(5), and the presheaf `toModuleKPresheaf` (6).
* `StructureSheafModuleK/SheafProperty.lean` — the sheaf condition
  `toModuleKPresheaf_isSheaf` (7), the bundled `toModuleKSheaf` (8), and the
  forget-and-recover natural iso to the `AddCommGrpCat`-valued structure sheaf.
* `StructureSheafModuleK/Carriers.lean` — the `HModule` / `HModule'` abbrevs,
  the H⁰ `LinearEquiv` transport companions, the `IsAffineHModuleVanishing` and
  `IsHModuleHomFinite` carriers, the Stein-finiteness input, the constant-sheaf-Γ
  adjunction upgrade, the `instIsHModuleHomFinite_toModuleKSheaf` producer
  instance, and the Čech-side carriers `Scheme.cechCochain[_OC]`,
  `Scheme.cechCohomology[_OC]`, `Scheme.IsCechAcyclicCover`.

See `blueprint/src/chapters/Cohomology_StructureSheafModuleK.tex`.
-/
