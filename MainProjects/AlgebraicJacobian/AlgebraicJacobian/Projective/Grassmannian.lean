/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GrassmannianRepresentability
import AlgebraicJacobian.Picard.ProjectiveMorphismBasic
import AlgebraicJacobian.Picard.OnePointRelPicCollapse
import AlgebraicJacobian.Projective.GrassmannianProjective
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts

/-!
# H-quasi-projectivity transport for Grassmannian representers

This file isolates the transport needed by the D4' divisor route. An
H-quasi-projectivity certificate for the absolute Grassmannian over `Spec Z`
base-changes to the explicit relative free Grassmannian. Over a field, a
locally free module is globally free, so uniqueness of representing objects
then transports the certificate to the chosen `Scheme.Grassmannian`
representer.

The absolute certificate is constructed by the Plucker embedding in
`Projective/GrassmannianProjective.lean`. The conditional transport theorem is
retained to isolate the base-change argument, and the unconditional theorem at
the end consumes the absolute certificate.
-/

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry
namespace Scheme
namespace Grassmannian

private noncomputable def pullbackTopFreeIso {T : Scheme.{0}}
    (N : T.Modules) (I : Type)
    (e : (Scheme.Modules.pullback (⊤ : T.Opens).ι).obj N ≅
      SheafOfModules.free (R := (⊤ : T.Opens).toScheme.ringCatSheaf) I) :
    N ≅ SheafOfModules.free (R := T.ringCatSheaf) I :=
  (Scheme.Modules.pullbackTopIsoSelf N).symm ≪≫
    (Scheme.Modules.pullback T.topIso.inv).mapIso e ≪≫
    Scheme.Modules.pullbackFreeIso T.topIso.inv I

private theorem globallyFreeSpecField {K : Type} [Field K]
    {V : (Spec (CommRingCat.of K)).Modules} {r : ℕ}
    (hV : SheafOfModules.IsLocallyFreeOfRank V r) :
    Nonempty (V ≅ SheafOfModules.free
      (R := (Spec (CommRingCat.of K)).ringCatSheaf) (Fin r)) := by
  let S : Scheme.{0} := Spec (CommRingCat.of K)
  obtain ⟨ι, U, hU, htriv⟩ := hV
  let x : S := Classical.arbitrary S
  have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨i, hxi⟩ := hx
  let W : S.Opens := U i
  have hxW : x ∈ W := hxi
  have hW : W = ⊤ := Scheme.Opens.eq_top_of_subsingleton W hxW
  have htrivW : Nonempty ((Scheme.Modules.pullback W.ι).obj V ≅
      SheafOfModules.free (R := W.toScheme.ringCatSheaf)
        (ULift.{0} (Fin r))) := htriv i
  clear_value W
  subst W
  obtain ⟨e⟩ := htrivW
  refine ⟨pullbackTopFreeIso V _ e ≪≫ ?_⟩
  exact (SheafOfModules.freeFunctor (R := S.ringCatSheaf)).mapIso
    (Equiv.toIso Equiv.ulift)

private theorem productHQuasiProjectiveOfAbsolute (d r : ℕ)
    (habs : (AlgebraicGeometry.Grassmannian.toSpecZ d r).IsHQuasiProjective)
    (S : Scheme.{0}) :
    (((Over.star S).obj
      (AlgebraicGeometry.Grassmannian.scheme d r)).hom).IsHQuasiProjective := by
  let G : Scheme.{0} := AlgebraicGeometry.Grassmannian.scheme d r
  let hc : IsLimit (PullbackCone.mk
      (prod.snd : S ⨯ G ⟶ G) (prod.fst : S ⨯ G ⟶ S)
      (specZIsTerminal.hom_ext
        ((prod.snd : S ⨯ G ⟶ G) ≫
          AlgebraicGeometry.Grassmannian.toSpecZ d r)
        ((prod.fst : S ⨯ G ⟶ S) ≫ specZIsTerminal.from S))) :=
    isPullbackOfIsTerminalIsProduct
      (AlgebraicGeometry.Grassmannian.toSpecZ d r)
      (specZIsTerminal.from S)
      (prod.snd : S ⨯ G ⟶ G) (prod.fst : S ⨯ G ⟶ S)
      specZIsTerminal (prodIsProd S G).binaryFanSwap
  let e : (S ⨯ G) ≅ pullback
      (AlgebraicGeometry.Grassmannian.toSpecZ d r)
      (specZIsTerminal.from S) :=
    hc.conePointUniqueUpToIso (limit.isLimit _)
  have he : e.hom ≫ pullback.snd
      (AlgebraicGeometry.Grassmannian.toSpecZ d r)
      (specZIsTerminal.from S) = (prod.fst : S ⨯ G ⟶ S) :=
    hc.conePointUniqueUpToIso_hom_comp
      (limit.isLimit _) WalkingCospan.right
  have hprod : (prod.fst : S ⨯ G ⟶ S).IsHQuasiProjective := by
    rw [← he]
    exact (habs.baseChange (specZIsTerminal.from S)).comp_isImmersion e.hom
  change (prod.lift prod.fst (𝟙 (S ⨯ G)) ≫
    prod.fst).IsHQuasiProjective
  rw [prod.lift_fst]
  exact hprod

/-- Over a field, H-quasi-projectivity of the absolute Grassmannian transports
to the chosen scheme representing locally free rank-`d` quotients of `V`.

This theorem isolates the exact reduction used by D4'. Its only projective
input is the certificate for `Grassmannian.toSpecZ`; no explicit
`RepresentableBy` witness is added to the consumer signature. -/
theorem representingScheme_isHQuasiProjective_of_field_of_absolute
    {K : Type} [Field K]
    {V : (Spec (CommRingCat.of K)).Modules} {r d : ℕ}
    (hV : SheafOfModules.IsLocallyFreeOfRank V r)
    (hd : 1 ≤ d) (hdr : d ≤ r)
    (habs : (AlgebraicGeometry.Grassmannian.toSpecZ d r).IsHQuasiProjective) :
    (representingScheme hV hd hdr).hom.IsHQuasiProjective := by
  obtain ⟨eV⟩ := globallyFreeSpecField hV
  let S : Scheme.{0} := Spec (CommRingCat.of K)
  let Y : Over S := (Over.star S).obj
    (AlgebraicGeometry.Grassmannian.scheme d r)
  let repY : (Scheme.Grassmannian V d).RepresentableBy Y :=
    (prodRepresentableBy S d r hd hdr).ofIso
      ((Scheme.Grassmannian.congrIso eV d ≪≫ freeCompare d r).symm)
  let E : representingScheme hV hd hdr ≅ Y :=
    (representation hV hd hdr).uniqueUpToIso repY
  rw [← E.hom.w]
  exact (productHQuasiProjectiveOfAbsolute d r habs S).comp_isImmersion
    E.hom.left

/-- Over a field, the chosen scheme representing locally free rank-`d`
quotients of `V` is H-quasi-projective. -/
theorem representingScheme_isHQuasiProjective_of_field
    {K : Type} [Field K]
    {V : (Spec (CommRingCat.of K)).Modules} {r d : ℕ}
    (hV : SheafOfModules.IsLocallyFreeOfRank V r)
    (hd : 1 ≤ d) (hdr : d ≤ r) :
    (representingScheme hV hd hdr).hom.IsHQuasiProjective := by
  exact representingScheme_isHQuasiProjective_of_field_of_absolute hV hd hdr
    (AlgebraicGeometry.Grassmannian.isHQuasiProjective_toSpecZ d r)

end Grassmannian
end Scheme
end AlgebraicGeometry
