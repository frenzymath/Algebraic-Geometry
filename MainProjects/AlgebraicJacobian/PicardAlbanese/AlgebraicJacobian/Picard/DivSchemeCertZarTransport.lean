/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeCertZarLeak

/-!
# The support of a pulled-back system is the preimage of the support

The pointwise certificate gate (`DivSchemeCertZarPointwise.lean`) asks, at each base prime,
for a certificate over `Localization.Away r` of an adaptation of the **pulled** system
`d.pullback (relCurveMap C R (Localization.Away r))`.  Every support/no-leak/clopen lemma of
the lane, however, is stated for a system on `relCurve C R`.  Composing the two needs the
transport recorded here: the support locus of a pulled system is the preimage of the support
locus.

Both inclusions come from the same fact: `f.stalkMap z` is a **local** ring homomorphism
(`AlgebraicGeometry.LocallyRingedSpace.isLocalHomStalkMap`), so it both preserves and
reflects unit-ness, and the germ of a pulled equation is the `stalkMap` image of the germ of
the original (`germ_appLE_apply`, re-derived here since it is `private` upstream).

## Main declarations

* `AlgebraicGeometry.Scheme.LocalEquations.unitLocus_pullback` — the unit locus pulls back.
* `AlgebraicGeometry.Scheme.LocalEquations.supportLocus_pullback` — the support locus pulls
  back; the hinge the certificate lane needs.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

namespace Scheme.LocalEquations

variable {X Y : Scheme.{u}}

/-- The germ of a pulled-back equation is the `stalkMap` image of the germ of the original.
(The upstream `germ_appLE_apply` is `private`; this is the instance of it the transport
needs, spelled for `pullbackEqn`.) -/
lemma germ_pullbackEqn_eq_stalkMap (f : Y ⟶ X) (E : X.LocalEquations) (y : Y)
    {z : Y} (hz : z ∈ (E.cover.pullback f).opens y) :
    (Y.presheaf.germ ((E.cover.pullback f).opens y) z hz).hom (pullbackEqn f E y)
      = (f.stalkMap z).hom
        ((X.presheaf.germ (E.cover.opens (f.base y)) (f.base z)
          (by exact hz)).hom (E.eqn (f.base y))) := by
  simp only [pullbackEqn, Scheme.Hom.appLE, CommRingCat.comp_apply,
    Scheme.Hom.germ_stalkMap_apply, TopCat.Presheaf.germ_res_apply]

/-- **The unit locus pulls back.** A point of `Y` is in the unit locus of the pulled system
exactly when its image is in the unit locus of the original: the germ of the pulled equation
is the `stalkMap` image of the germ of the original, and `stalkMap` is a local hom, so it
preserves and reflects unit-ness. -/
theorem unitLocus_pullback (f : Y ⟶ X) (E : X.LocalEquations) (hreg) :
    ((E.pullback f hreg).unitLocus : Set Y) = f.base ⁻¹' (E.unitLocus : Set X) := by
  ext z
  have hzmem : z ∈ (E.pullback f hreg).cover.opens z := (E.cover.pullback f).mem_opens z
  have hfz : f.base z ∈ E.cover.opens (f.base z) := E.cover.mem_opens (f.base z)
  rw [Set.mem_preimage, SetLike.mem_coe, SetLike.mem_coe,
    (E.pullback f hreg).mem_unitLocus_iff_isUnit_germ hzmem,
    E.mem_unitLocus_iff_isUnit_germ hfz]
  have hgerm : (Y.presheaf.germ ((E.pullback f hreg).cover.opens z) z hzmem).hom
      ((E.pullback f hreg).eqn z)
      = (f.stalkMap z).hom
        ((X.presheaf.germ (E.cover.opens (f.base z)) (f.base z) hfz).hom
          (E.eqn (f.base z))) :=
    germ_pullbackEqn_eq_stalkMap f E z hzmem
  rw [hgerm]
  exact ⟨fun hu => isUnit_of_map_unit (f.stalkMap z).hom _ hu,
    fun hu => hu.map (f.stalkMap z).hom⟩

/-- **The support locus pulls back** — the hinge of the certificate lane: it lets every
support/no-leak/clopen statement proved for a system on `relCurve C R` be read on the pulled
system over an `Away` chart, which is what the pointwise gate consumes. -/
theorem supportLocus_pullback (f : Y ⟶ X) (E : X.LocalEquations) (hreg) :
    (E.pullback f hreg).supportLocus = f.base ⁻¹' E.supportLocus := by
  rw [supportLocus, supportLocus, unitLocus_pullback f E hreg, Set.preimage_compl]

end Scheme.LocalEquations

end AlgebraicGeometry
