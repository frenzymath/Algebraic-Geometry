/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RepresentableByTransport

/-!
# Exact-carrier finite-stage representer boundary

The finite-stage gluing API deliberately keeps its carrier opaque.  The missing geometric
input is therefore an isomorphism from the scalar pullback of a known representer to that
selected carrier.  This module records the producer at precisely that boundary: once the
carrier isomorphism is supplied, the Yoneda representer is obtained by the established
base-change transport, with no additional choice or axiom.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

noncomputable section

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- Produce a Picard-zero representation on an exact selected finite-stage carrier.

The explicit isomorphism `carrierIso` is the entire finite-stage/Yoneda obligation: it
identifies the selected carrier `J'` with the pullback of the supplied representer.  The
resulting representation is otherwise canonical transport through `pic0ThetaType`.
-/
noncomputable def pic0RepresentableBy_of_exactCarrierIso
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom]
    {J : Over (Spec (.of k))}
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    {J' : Over (Spec (.of L))}
    (carrierIso :
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj J ≅ J') :
    (pic0TypeFunctor ((baseChange k L).obj C)).RepresentableBy J' :=
  pic0RepresentableBy_of_baseChangeObjectIso C rep carrierIso

end

end AlgebraicGeometry
