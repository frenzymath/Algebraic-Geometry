/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.FiniteStagePullbackData
import AlgebraicJacobian.Descent.GluedMapData
import AlgebraicJacobian.Descent.RepresenterData
import AlgebraicJacobian.Descent.TensorProductPushoutData
import AlgebraicJacobian.Descent.AffineRingGlueData
import AlgebraicJacobian.Picard.FiniteStageData
import AlgebraicJacobian.Picard.Pic0FiniteStageCanonicalGlueContext
import AlgebraicJacobian.Picard.Pic0FiniteStageStableGluePackage
import AlgebraicJacobian.Picard.Pic0FiniteStageStableGlueProducer
import AlgebraicJacobian.Picard.Pic0FiniteStageStableGluedOver
import AlgebraicJacobian.Picard.Pic0FiniteStageStableRestrictionBaseChange

/-!
# Public finite-stage API

This import-light facade is the migration boundary for finite-stage consumers.  New
files should import it instead of rebuilding tensor, pullback, representer, and stage
infrastructure from local `letI` blocks.

The legacy flat-package conversion is intentionally separate: import
`AlgebraicJacobian.Picard.Pic0FiniteStageLegacyAdapter` when an existing
`Pic0FiniteStageGluePackage` must be converted.  Keeping that dependent reconstruction out
of this facade preserves the bounded import surface for ordinary stable consumers.

The final-stage comparison has the same dependent tensor boundary and is exposed through
`AlgebraicJacobian.Picard.Pic0FiniteStageFinalBaseChangeApi`; keeping that import separate
lets clients opt into the pinned comparison functions without widening this lightweight
facade.
-/
