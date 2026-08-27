/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.FiberEulerIndex
import AlgebraicJacobian.Picard.RigidPushforwardRank
import AlgebraicJacobian.Picard.TwoTermEulerIndex

/-!
# Scheme fibres and two-term Euler indices

This file joins the scheme-theoretic fibre Euler index to the affine two-term
finite-replacement machinery.  For a quasicoherent module on a family with a
two-affine cover, the intrinsic index of a fibre is the signed kernel/cokernel
index of the family Cech differential after residue-field base change.

There are two scalar changes in the comparison.  First, the fibre index is
defined over the scheme residue field `kappa(t)`, while the chart comparison
uses `Gamma(Spec kappa(t), top)`.  Second, for a base `Spec R`, the family Cech
differential is linear over `Gamma(Spec R, top)`, so its algebraic fibre is at
the point transported from `t` along `Gamma(Spec R, top) equiv R`.

The final theorem consumes an actual `TwoTermFiniteReplacement`.  Thus its
right-hand side is the virtual rank of a finite projective module rather than
an unpriced totalized finrank.  The left-hand side remains named an *index*:
identifying it with geometric degree still requires cohomological finiteness,
finite-pushforward Euler transfer, and Riemann--Roch.  Nothing here constructs
a PicEt degree function or a representability consumer.

## Main declarations

* `AffineCoverMVSquare.chi_eq_moduleSectionDiffBase`: scalar-normalized Cech
  index over global sections of the coefficient field.
* `Hom.fiberEulerIndex_eq_baseChangedCechIndex`: comparison with the
  residue-field base change of the family Cech differential.
* `Hom.fiberEulerIndex_eq_baseChangedCechIndex_spec`: the same comparison at
  the corresponding point of `Spec Gamma(Spec R, top)`.
* `Hom.fiberEulerIndex_eq_virtualRank`: the finite-replacement virtual-rank
  formula for the scheme-theoretic fibre index.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Module TensorProduct

namespace AlgebraicGeometry

noncomputable section

namespace Scheme

variable {X Y : Scheme.{u}}

/-- The concrete Cech index over a field agrees with the signed finranks of
the base-linear section differential over `Gamma(Spec k, top)`.

The underlying kernel and quotient modules are definitionally the same; only
their scalar actions are transported along `Scheme.GammaSpecIso`.  No
finite-dimensionality is asserted. -/
theorem AffineCoverMVSquare.chi_eq_moduleSectionDiffBase
    {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    (V : C.left.AffineCoverMVSquare) (M : C.left.Modules) :
    letI := C.hom.baseSectionsModule M V.U₁
    letI := C.hom.baseSectionsModule M V.U₂
    letI := C.hom.baseSectionsModule M (V.U₁ ⊓ V.U₂)
    V.chi C M =
      (Module.finrank Γ(Spec (CommRingCat.of k), ⊤)
        (LinearMap.ker (V.moduleSectionDiffBase C.hom M)) : ℤ) -
      (Module.finrank Γ(Spec (CommRingCat.of k), ⊤)
        (Γ(M, V.U₁ ⊓ V.U₂) ⧸
          LinearMap.range (V.moduleSectionDiffBase C.hom M)) : ℤ) := by
  letI m1 := C.hom.baseSectionsModule M V.U₁
  letI m2 := C.hom.baseSectionsModule M V.U₂
  letI m0 := C.hom.baseSectionsModule M (V.U₁ ⊓ V.U₂)
  have h0 : Module.finrank k (V.H0ₗ C M) =
      Module.finrank Γ(Spec (CommRingCat.of k), ⊤)
        (LinearMap.ker (V.moduleSectionDiffBase C.hom M)) := by
    refine finrank_eq_of_ringEquiv_addEquiv
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm
      (AddEquiv.refl _) ?_
    intro r x
    rfl
  have h1 : Module.finrank k (V.H1Cokₗ C M) =
      Module.finrank Γ(Spec (CommRingCat.of k), ⊤)
        (Γ(M, V.U₁ ⊓ V.U₂) ⧸
          LinearMap.range (V.moduleSectionDiffBase C.hom M)) := by
    refine finrank_eq_of_ringEquiv_addEquiv
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm
      (AddEquiv.refl _) ?_
    intro r x
    rfl
  rw [V.chi_def]
  unfold AffineCoverMVSquare.h0 AffineCoverMVSquare.h1
  rw [h0, h1]

/-- The intrinsic fibre Euler index is the signed kernel/cokernel index of the
family Cech differential after base change to
`Gamma(Spec kappa(t), top)`.

This combines the derived-to-Cech comparison on the fibre with the
isomorphism of family and fibre Cech complexes.  It imposes no finiteness
hypothesis, so its finranks retain their totalized meaning. -/
theorem Hom.fiberEulerIndex_eq_baseChangedCechIndex
    (f : X ⟶ Y) [IsAffine Y] (V : X.AffineCoverMVSquare)
    (M : X.Modules) [M.IsQuasicoherent] (t : Y)
    [hfi : IsAffineHom (f.fiberι t)] :
    letI : Algebra Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤) :=
      ((Y.fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI := f.baseSectionsModule M V.U₁
    letI := f.baseSectionsModule M V.U₂
    letI := f.baseSectionsModule M (V.U₁ ⊓ V.U₂)
    f.fiberEulerIndex t M =
      (Module.finrank Γ(Spec (Y.residueField t), ⊤)
        (LinearMap.ker ((V.moduleSectionDiffBase f M).baseChange
          Γ(Spec (Y.residueField t), ⊤))) : ℤ) -
      (Module.finrank Γ(Spec (Y.residueField t), ⊤)
        (TensorProduct Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤)
          Γ(M, V.U₁ ⊓ V.U₂) ⧸
            LinearMap.range ((V.moduleSectionDiffBase f M).baseChange
              Γ(Spec (Y.residueField t), ⊤))) : ℤ) := by
  letI aAB : Algebra Γ(Y, ⊤) Γ(Spec (Y.residueField t), ⊤) :=
    ((Y.fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI m1 := f.baseSectionsModule M V.U₁
  letI m2 := f.baseSectionsModule M V.U₂
  letI m0 := f.baseSectionsModule M (V.U₁ ⊓ V.U₂)
  let W := @AffineCoverMVSquare.preimage _ _ V (f.fiberι t) hfi
  letI n1 := (f.fiberToSpecResidueField t).baseSectionsModule
    (f.fiberModule t M) W.U₁
  letI n2 := (f.fiberToSpecResidueField t).baseSectionsModule
    (f.fiberModule t M) W.U₂
  letI n0 := (f.fiberToSpecResidueField t).baseSectionsModule
    (f.fiberModule t M) (W.U₁ ⊓ W.U₂)
  rw [f.fiberEulerIndex_eq_cech t M W]
  rw [W.chi_eq_moduleSectionDiffBase
    (Over.mk (f.fiberToSpecResidueField t)) (f.fiberModule t M)]
  change
    (Module.finrank Γ(Spec (Y.residueField t), ⊤)
      (LinearMap.ker (W.moduleSectionDiffBase
        (f.fiberToSpecResidueField t) (f.fiberModule t M))) : ℤ) -
      (Module.finrank Γ(Spec (Y.residueField t), ⊤)
        (Γ(f.fiberModule t M, W.U₁ ⊓ W.U₂) ⧸
          LinearMap.range (W.moduleSectionDiffBase
            (f.fiberToSpecResidueField t) (f.fiberModule t M))) : ℤ) =
    _
  rw [← finrank_ker_baseChange_residueField V f M t,
    ← finrank_quotient_range_baseChange_residueField V f M t]

/-- Over `Spec R`, the intrinsic fibre Euler index is the two-term family
index at the corresponding point of `Spec Gamma(Spec R, top)`.

Besides the geometric Cech comparison, this transports both the kernel and
the quotient by the range across the residue-field algebra equivalence. -/
theorem Hom.fiberEulerIndex_eq_baseChangedCechIndex_spec
    {R : CommRingCat.{u}} (p : X ⟶ Spec R)
    (V : X.AffineCoverMVSquare) (M : X.Modules) [M.IsQuasicoherent]
    (t : Spec R) [IsAffineHom (p.fiberι t)] :
    let B := Γ(Spec R, ⊤)
    let ε : B ≃+* R :=
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
    let H : PrimeSpectrum B ≃ₜ PrimeSpectrum R :=
      PrimeSpectrum.homeomorphOfRingEquiv ε
    let s := H.symm t
    letI := p.baseSectionsModule M V.U₁
    letI := p.baseSectionsModule M V.U₂
    letI := p.baseSectionsModule M (V.U₁ ⊓ V.U₂)
    p.fiberEulerIndex t M =
      (Module.finrank s.asIdeal.ResidueField
        (LinearMap.ker ((V.moduleSectionDiffBase p M).baseChange
          s.asIdeal.ResidueField)) : ℤ) -
      (Module.finrank s.asIdeal.ResidueField
        (TensorProduct B s.asIdeal.ResidueField Γ(M, V.U₁ ⊓ V.U₂) ⧸
          LinearMap.range ((V.moduleSectionDiffBase p M).baseChange
            s.asIdeal.ResidueField)) : ℤ) := by
  let B := Γ(Spec R, ⊤)
  let ε : B ≃+* R :=
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  let H : PrimeSpectrum B ≃ₜ PrimeSpectrum R :=
    PrimeSpectrum.homeomorphOfRingEquiv ε
  let s := H.symm t
  let Kt := Γ(Spec ((Spec R).residueField t), ⊤)
  letI : Field Kt :=
    (MulEquiv.isField (Field.toIsField t.asIdeal.ResidueField)
      (specResidueFieldRingEquiv R t).symm.toMulEquiv).toField
  letI aBK : Algebra B Kt :=
    (((Spec R).fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI m1 := p.baseSectionsModule M V.U₁
  letI m2 := p.baseSectionsModule M V.U₂
  letI m0 := p.baseSectionsModule M (V.U₁ ⊓ V.U₂)
  let hs : s.asIdeal = Ideal.comap ε.toRingHom t.asIdeal := rfl
  let kappaMap := Ideal.ResidueField.map s.asIdeal t.asIdeal ε.toRingHom hs
  have hkappaMap : Function.Bijective kappaMap :=
    (RingEquiv.surjectiveOnStalks ε).residueFieldMap_bijective
      s.asIdeal t.asIdeal hs
  let kappaEquiv := RingEquiv.ofBijective kappaMap hkappaMap
  let tau := kappaEquiv.trans (specResidueFieldRingEquiv R t)
  let tauAlg : s.asIdeal.ResidueField ≃ₐ[B] Kt :=
    AlgEquiv.ofRingEquiv fun b => by
      change tau ((algebraMap B s.asIdeal.ResidueField) b) = _
      change specResidueFieldRingEquiv R t
        (kappaMap ((algebraMap B s.asIdeal.ResidueField) b)) = _
      rw [Ideal.ResidueField.map_algebraMap]
      exact (appLE_fromSpecResidueField_apply R t b).symm
  let d := V.moduleSectionDiffBase p M
  have hindex := p.fiberEulerIndex_eq_baseChangedCechIndex V M t
  have h0 := finrank_ker_baseChange_of_algEquiv d tauAlg
  have h1 := finrank_quotient_range_baseChange_of_algEquiv d tauAlg
  exact hindex.trans (congrArg₂ (fun a b : ℕ => (a : ℤ) - (b : ℤ))
    h0.symm h1.symm)

/-- A finite replacement computes the intrinsic scheme-theoretic fibre Euler
index as the virtual rank of its finite projective degree-zero term.

The `TwoTermFiniteReplacement` hypothesis packages universal kernel and
cokernel comparisons, so this result consumes both cohomological degrees.  It
does not by itself identify the index with line-bundle degree. -/
theorem Hom.fiberEulerIndex_eq_virtualRank
    {R : CommRingCat.{u}} (p : X ⟶ Spec R)
    (V : X.AffineCoverMVSquare) (M : X.Modules) [M.IsQuasicoherent]
    (t : Spec R) [IsAffineHom (p.fiberι t)] :
    letI := p.baseSectionsModule M V.U₁
    letI := p.baseSectionsModule M V.U₂
    letI := p.baseSectionsModule M (V.U₁ ⊓ V.U₂)
    ∀ F : AlgebraicJacobian.TwoTermFiniteReplacement
        (V.moduleSectionDiffBase p M),
    let B := Γ(Spec R, ⊤)
    let ε : B ≃+* R :=
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
    let H : PrimeSpectrum B ≃ₜ PrimeSpectrum R :=
      PrimeSpectrum.homeomorphOfRingEquiv ε
    let s := H.symm t
    p.fiberEulerIndex t M =
      (s.asIdeal.fiberRank F.K0 : ℤ) - (F.n : ℤ) := by
  letI m1 := p.baseSectionsModule M V.U₁
  letI m2 := p.baseSectionsModule M V.U₂
  letI m0 := p.baseSectionsModule M (V.U₁ ⊓ V.U₂)
  intro F
  rw [p.fiberEulerIndex_eq_baseChangedCechIndex_spec V M t]
  exact F.fiberEulerIndex_eq_virtualRank _

end Scheme

end

end AlgebraicGeometry
