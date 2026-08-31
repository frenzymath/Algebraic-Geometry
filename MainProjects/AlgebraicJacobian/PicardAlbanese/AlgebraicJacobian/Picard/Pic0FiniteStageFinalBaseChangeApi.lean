/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageFinalBaseChange

/-!
# Public final-stage comparison API

This module is the explicit import boundary for the final finite-stage comparison.  The
implementation module also retains compatibility declarations, but new consumers should use
the pinned carrier and class-free function projections:

* `pic0FiniteStageFinalBaseChangeEquivPinned` and
  `pic0FiniteStageFinalBaseChangeEquivPinnedFun`;
* `pic0FiniteStageFinalScalarExtensionMapPinned` and
  `pic0FiniteStageFinalScalarExtensionMapPinnedFun`;
* `pic0FiniteStageFinalBaseChangeEquivPinned_naturality`.

The separate boundary keeps the ordinary `FiniteStageApi` import light while making the
stable final-stage surface discoverable and reproducible for downstream files.
-/
