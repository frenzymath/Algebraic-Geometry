/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RigidPushforwardInstance
import AlgebraicJacobian.Picard.RigidPushforwardTransfer
import AlgebraicJacobian.Picard.SchemeEulerIndex

/-!
# A finite replacement for a family line bundle on a curve

For a smooth proper geometrically integral curve `C/k`, a finite type affine
test `Spec A`, and a line bundle `L` on `C_A`, this file constructs the finite
two-term replacement of the standard Cech complex after pushing `L` forward
along the finite map `C_A -> P^1_A`.

Unlike the abstract existence theorem, the result below discharges every input
for the campaign object: noetherianity of the affine base, flatness of the three
chart-section modules, and finiteness of both Cech cohomology modules.  It is the
reusable finite-complex input for the fibre Euler and Picard degree-piece route.

Nothing here constructs a Picard representer or assumes a rational point on
`C`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Module TensorProduct

namespace AlgebraicGeometry

noncomputable section

namespace Adelic

open Scheme

variable {k : Type u} [Field k]

/-- The standard two-chart Cech complex of the finite pushforward of a family
line bundle admits a finite replacement.

The hypotheses are exactly those of the challenge curve and a finite type
affine test.  In particular, the resulting `TwoTermFiniteReplacement` is
available without a rational point on `C` and without an extra representability
hypothesis. -/
theorem exists_twoTermFiniteReplacement_finiteMapToP1BaseChange
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom]
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (L : (Limits.pullback C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hL : LineBundle.IsLocallyTrivial L) :
    let M := (Modules.pushforward (finiteMapToP1BaseChange A C)).obj L
    let p := pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    let U := p1BaseChangeCoverSquare (k := k) A
    letI := p.baseSectionsModule M U.U₁
    letI := p.baseSectionsModule M U.U₂
    letI := p.baseSectionsModule M (U.U₁ ⊓ U.U₂)
    Nonempty (AlgebraicJacobian.TwoTermFiniteReplacement
      (U.moduleSectionDiffBase p M)) := by
  haveI : HasFiniteMapToP1 C := inferInstance
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : IsNoetherianRing Γ(Spec (CommRingCat.of A), ⊤) :=
    isNoetherianRing_of_ringEquiv A
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm
  haveI := hL.isFinitePresentation
  let M := (Modules.pushforward (finiteMapToP1BaseChange A C)).obj L
  haveI : M.IsFinitePresentation :=
    pushforward_finiteMapToP1BaseChange_isFinitePresentation A C L hL
  haveI : M.IsQuasicoherent := by
    haveI : IsFinite (finiteMapToP1BaseChange A C) :=
      isFinite_finiteMapToP1BaseChange A C
    exact Modules.pushforward_isQuasicoherent (finiteMapToP1BaseChange A C) L
  let p := pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  let U := p1BaseChangeCoverSquare (k := k) A
  letI := p.baseSectionsModule M U.U₁
  letI := p.baseSectionsModule M U.U₂
  letI := p.baseSectionsModule M (U.U₁ ⊓ U.U₂)
  have hflat : CoherentSheafFlat p M :=
    pushforward_finiteMapToP1BaseChange_coherentSheafFlat A C L hL
  haveI : Module.Flat Γ(Spec (CommRingCat.of A), ⊤) Γ(M, U.U₁) :=
    flat_baseSections_of_coherentSheafFlat p M hflat U.isAffineOpen_U₁
  haveI : Module.Flat Γ(Spec (CommRingCat.of A), ⊤) Γ(M, U.U₂) :=
    flat_baseSections_of_coherentSheafFlat p M hflat U.isAffineOpen_U₂
  haveI : Module.Flat Γ(Spec (CommRingCat.of A), ⊤)
      (Γ(M, U.U₁) × Γ(M, U.U₂)) :=
    AlgebraicJacobian.TwoTerm.flat_prod
  haveI : Module.Flat Γ(Spec (CommRingCat.of A), ⊤) Γ(M, U.U₁ ⊓ U.U₂) :=
    flat_baseSections_of_coherentSheafFlat p M hflat U.isAffineOpen_inf
  haveI : IsIntegral (p1Over k).left := inferInstance
  have hH₀ : (LinearMap.ker (U.moduleSectionDiffBase p M)).FG :=
    p1Cech_h0_fg_of_isIntegral A M
  haveI : Module.Finite Γ(Spec (CommRingCat.of A), ⊤)
      (Γ(M, U.U₁ ⊓ U.U₂) ⧸ LinearMap.range (U.moduleSectionDiffBase p M)) :=
    module_finite_h1_p1BaseChange A M
  exact AlgebraicJacobian.exists_twoTermFiniteReplacement
    (U.moduleSectionDiffBase p M) hH₀

/-- The campaign finite replacement computes the fibre Euler index of the
finite pushforward on `P^1_A` by a virtual rank.

This is an interface composition of
`exists_twoTermFiniteReplacement_finiteMapToP1BaseChange` with the existing
`Scheme.Hom.fiberEulerIndex_eq_virtualRank`; it removes a caller-supplied
replacement but adds no new Euler or Riemann--Roch comparison.  Comparing this
index with the Euler index of `L` on `C_A` is a separate finite-pushforward
cohomology step, and is not asserted here. -/
theorem exists_fiberEulerIndex_eq_virtualRank_finiteMapToP1BaseChange
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom]
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (L : (Limits.pullback C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hL : LineBundle.IsLocallyTrivial L) (t : Spec (CommRingCat.of A)) :
    let M := (Modules.pushforward (finiteMapToP1BaseChange A C)).obj L
    let p := pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    let U := p1BaseChangeCoverSquare (k := k) A
    letI := p.baseSectionsModule M U.U₁
    letI := p.baseSectionsModule M U.U₂
    letI := p.baseSectionsModule M (U.U₁ ⊓ U.U₂)
    ∃ F : AlgebraicJacobian.TwoTermFiniteReplacement
        (U.moduleSectionDiffBase p M),
      let B := Γ(Spec (CommRingCat.of A), ⊤)
      let ε : B ≃+* CommRingCat.of A :=
        (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
      let H : PrimeSpectrum B ≃ₜ PrimeSpectrum (CommRingCat.of A) :=
        PrimeSpectrum.homeomorphOfRingEquiv ε
      let s := H.symm t
      p.fiberEulerIndex t M =
        (s.asIdeal.fiberRank F.K0 : ℤ) - (F.n : ℤ) := by
  haveI : HasFiniteMapToP1 C := inferInstance
  haveI := hL.isFinitePresentation
  let M := (Modules.pushforward (finiteMapToP1BaseChange A C)).obj L
  haveI : IsFinite (finiteMapToP1BaseChange A C) :=
    isFinite_finiteMapToP1BaseChange A C
  haveI : M.IsQuasicoherent :=
    Modules.pushforward_isQuasicoherent (finiteMapToP1BaseChange A C) L
  let p := pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  let U := p1BaseChangeCoverSquare (k := k) A
  letI := p.baseSectionsModule M U.U₁
  letI := p.baseSectionsModule M U.U₂
  letI := p.baseSectionsModule M (U.U₁ ⊓ U.U₂)
  obtain ⟨F⟩ :=
    exists_twoTermFiniteReplacement_finiteMapToP1BaseChange C A L hL
  refine ⟨F, ?_⟩
  exact p.fiberEulerIndex_eq_virtualRank U M t F

/-- The intrinsic fibre Euler index of the finite pushforward on `P^1_A` is
locally constant on the affine base.

One finite replacement works over all of `Spec A`.  Its finite-projective
degree-zero term has locally constant fibre rank, and
`Scheme.Hom.fiberEulerIndex_eq_virtualRank` transports that statement to the
scheme-theoretic fibre Euler index.  This still does not compare the result
with the Euler characteristic or degree of `L` on `C_A`. -/
theorem isLocallyConstant_fiberEulerIndex_finiteMapToP1BaseChange
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom]
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (L : (Limits.pullback C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hL : LineBundle.IsLocallyTrivial L) :
    let M := (Modules.pushforward (finiteMapToP1BaseChange A C)).obj L
    let p := pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    IsLocallyConstant (fun t : Spec (CommRingCat.of A) =>
      p.fiberEulerIndex t M) := by
  haveI : HasFiniteMapToP1 C := inferInstance
  haveI := hL.isFinitePresentation
  let M := (Modules.pushforward (finiteMapToP1BaseChange A C)).obj L
  haveI : IsFinite (finiteMapToP1BaseChange A C) :=
    isFinite_finiteMapToP1BaseChange A C
  haveI : M.IsQuasicoherent :=
    Modules.pushforward_isQuasicoherent (finiteMapToP1BaseChange A C) L
  let p := pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  let U := p1BaseChangeCoverSquare (k := k) A
  letI := p.baseSectionsModule M U.U₁
  letI := p.baseSectionsModule M U.U₂
  letI := p.baseSectionsModule M (U.U₁ ⊓ U.U₂)
  obtain ⟨F⟩ :=
    exists_twoTermFiniteReplacement_finiteMapToP1BaseChange C A L hL
  let B := Γ(Spec (CommRingCat.of A), ⊤)
  let ε : B ≃+* CommRingCat.of A :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  let H : PrimeSpectrum B ≃ₜ PrimeSpectrum (CommRingCat.of A) :=
    PrimeSpectrum.homeomorphOfRingEquiv ε
  letI : Module.Flat B F.K0 := Module.Flat.of_projective
  letI : Module.FinitePresentation B F.K0 :=
    Module.finitePresentation_of_projective B F.K0
  have hRank : IsLocallyConstant (fun s : PrimeSpectrum B =>
      (s.asIdeal.fiberRank F.K0 : ℤ) - (F.n : ℤ)) := by
    exact (Ideal.isLocallyConstant_fiberRank (A := B) (K := F.K0)).comp
      fun r => (r : ℤ) - (F.n : ℤ)
  have hVirtual : IsLocallyConstant (fun t : Spec (CommRingCat.of A) =>
      ((H.symm t).asIdeal.fiberRank F.K0 : ℤ) - (F.n : ℤ)) := by
    exact hRank.comp_continuous H.symm.continuous
  convert hVirtual using 1
  funext t
  exact p.fiberEulerIndex_eq_virtualRank U M t F

end Adelic

end

end AlgebraicGeometry
