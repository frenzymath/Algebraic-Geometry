/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeCertificate
import AlgebraicJacobian.Picard.DivisorThetaSurjectivity

/-!
# DDR-4 (certificate transport) — the junction equivalence and the engine transport

Continuation of `AlgebraicJacobian.Picard.DivSchemeCertificate` (the 500-line cap forced
the split): the two junctions are mutually inverse `R`-linear maps, and the rigid
engine's outputs transport across the resulting equivalence.

* `DivisorAdaptation.gluedToVanishingₗ` — the forward junction as an `R`-linear map
  (`gluedToIdeal₀/₁` are additive and `R`-homogeneous by uniqueness of assemblies);
* `DivisorAdaptation.gluedEquivVanishing` — **the junction equivalence**
  `F_{Θᵃ−d}(⊤) ≃ₗ[R] K_a(d)` (mutually inverse by uniqueness of cofactors);
* `DivisorAdaptation.datumH0EquivVanishing` — the engine's `H⁰`-carrier form
  `H⁰(C_R, F_{Θᵃ−d}) ≃ₗ[R] K_a(d)`;
* `DivisorAdaptation.finite_vanishingSubmodule` / `projective_vanishingSubmodule` —
  **the certificate transport, first output** (`informal/spec-dd-r.md` §3 item 4): over
  a Noetherian test ring, given the complex-form fibrewise `h¹`-data of the theta-ideal
  datum (the P-fib fibrewise boundary, same shape as `thetaGluedEval_surjective`), the
  vanishing submodule `K_a(d)` is a finite projective `R`-module — the engine fired on
  the constructed family's twisted glued sheaf (`datumRigidEngine`), transported along
  the junction;
* `DivisorAdaptation.divisorWindowEquivVanishing`, `finite_divisorWindow`,
  `projective_divisorWindow` — the same for the window submodule
  `K_a(d) ⊆ R ⊗[k] H_a` of `AlgebraicJacobian.Picard.DivisorFamilyWindow` (the
  `grFunctorAff`-ambient carrier that DDR-5/DDR-9 consume).

ANTI-CIRCULARITY (binding, spec §3 item 4): the fibrewise inputs are hypotheses on the
CARVE-PAIR side (P-fib on fibres of the universal pair, certificate-free); the engine
UPGRADES them; `IsCertified` clauses are OUTPUTS — nothing here assumes a certificate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} {R : Type u} [CommRing R]
  [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations} {A : DivisorAdaptation C R π d} {a : ℕ}

/-! ## The junction equivalence -/

section Equiv

variable (A a) in
/-- The forward junction, as an `R`-linear map. -/
noncomputable def gluedToVanishingₗ :
    A.ThetaIdealSections a ⊤ →ₗ[R]
      ↥(d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a)) where
  toFun := gluedToVanishing A a
  map_add' s t := by
    refine Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))
    · change gluedToIdeal₀ A a
          (inf_le_right : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀
            ≤ (relCover C R (fiberTwoCover π)).V₀)
          (secRes ((A.thetaIdealDatum a).sheaf)
            (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ≤ ⊤) (s + t))
        = gluedToIdeal₀ A a inf_le_right
            (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s)
          + gluedToIdeal₀ A a inf_le_right
              (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left t)
      rw [map_add, gluedToIdeal₀_add]
    · change gluedToIdeal₁ A a
          (inf_le_right : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁
            ≤ (relCover C R (fiberTwoCover π)).V₁)
          (secRes ((A.thetaIdealDatum a).sheaf)
            (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁ ≤ ⊤) (s + t))
        = gluedToIdeal₁ A a inf_le_right
            (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s)
          + gluedToIdeal₁ A a inf_le_right
              (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left t)
      rw [map_add, gluedToIdeal₁_add]
  map_smul' r s := by
    refine Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))
    · change gluedToIdeal₀ A a
          (inf_le_right : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀
            ≤ (relCover C R (fiberTwoCover π)).V₀)
          (secRes ((A.thetaIdealDatum a).sheaf)
            (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ≤ ⊤) (r • s))
        = r • gluedToIdeal₀ A a inf_le_right
            (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s)
      rw [map_smul, gluedToIdeal₀_smul]
    · change gluedToIdeal₁ A a
          (inf_le_right : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁
            ≤ (relCover C R (fiberTwoCover π)).V₁)
          (secRes ((A.thetaIdealDatum a).sheaf)
            (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁ ≤ ⊤) (r • s))
        = r • gluedToIdeal₁ A a inf_le_right
            (secRes ((A.thetaIdealDatum a).sheaf) inf_le_left s)
      rw [map_smul, gluedToIdeal₁_smul]

/-- **Roundtrip**: assembling the cofactor family of a vanishing pair returns the
pair. -/
lemma gluedToVanishing_vanishingToGlued
    (x : ↥(d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
      (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a))) :
    gluedToVanishing A a (vanishingToGlued A a x) = x := by
  refine Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))
  · refine ((gluedToIdeal₀_unique
      (inf_le_right : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀
        ≤ (relCover C R (fiberTwoCover π)).V₀)
      (secRes ((A.thetaIdealDatum a).sheaf)
        (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ≤ ⊤)
        (vanishingToGlued A a x)) (β := x.1.1.1) (fun i => ?_)).symm : _)
    have hkey := congrArg ((relCurve C R).resHom
      (le_inf le_top inf_le_right :
        ((⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀) ⊓ A.pieces (Sum.inl i) :
          (relCurve C R).Opens) ≤ ⊤ ⊓ A.pieces (Sum.inl i)))
      (A.eqn_mul_eqnDiv (Sum.inl i) inf_le_right
        (vanishingSide A a x (Sum.inl i)) (vanishingSide_germ_mem x (Sum.inl i)))
    rw [map_mul] at hkey
    simp only [vanishingSide_inl, Scheme.resHom_resHom] at hkey
    exact hkey.symm
  · refine ((gluedToIdeal₁_unique
      (inf_le_right : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁
        ≤ (relCover C R (fiberTwoCover π)).V₁)
      (secRes ((A.thetaIdealDatum a).sheaf)
        (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁ ≤ ⊤)
        (vanishingToGlued A a x)) (β := x.1.1.2) (fun j => ?_)).symm : _)
    have hkey := congrArg ((relCurve C R).resHom
      (le_inf le_top inf_le_right :
        ((⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁) ⊓ A.pieces (Sum.inr j) :
          (relCurve C R).Opens) ≤ ⊤ ⊓ A.pieces (Sum.inr j)))
      (A.eqn_mul_eqnDiv (Sum.inr j) inf_le_right
        (vanishingSide A a x (Sum.inr j)) (vanishingSide_germ_mem x (Sum.inr j)))
    rw [map_mul] at hkey
    simp only [vanishingSide_inr, Scheme.resHom_resHom] at hkey
    exact hkey.symm

/-- **Roundtrip**: dividing the assembled pair of a global datum section returns the
section (by uniqueness of cofactors over the regular equations). -/
lemma vanishingToGlued_gluedToVanishing (s : A.ThetaIdealSections a ⊤) :
    vanishingToGlued A a (gluedToVanishing A a s) = s := by
  refine Subtype.ext (funext fun p => ?_)
  rcases p with i | j
  · -- expose the datum component of `s` under the chart-0 assembly
    have hcomp : A.gluedComp₀ (secRes ((A.thetaIdealDatum a).sheaf)
        (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ≤ ⊤) s) i.down
        = (relCurve C R).resHom
            (le_inf le_top inf_le_right :
              ((⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀) ⊓ A.pieces (Sum.inl i.down) :
                (relCurve C R).Opens) ≤ ⊤ ⊓ A.pieces (Sum.inl i.down))
            (s.val (Sum.inl i)) := rfl
    have hres := congrArg ((relCurve C R).resHom
      (le_inf (le_inf le_top (inf_le_right.trans (A.pieces_inl_le i.down)))
        inf_le_right :
        (⊤ ⊓ A.pieces (Sum.inl i.down) : (relCurve C R).Opens)
          ≤ (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀) ⊓ A.pieces (Sum.inl i.down)))
      (res_gluedToIdeal₀
        (inf_le_right : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀
          ≤ (relCover C R (fiberTwoCover π)).V₀)
        (secRes ((A.thetaIdealDatum a).sheaf)
          (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ≤ ⊤) s) i.down)
    rw [map_mul, hcomp] at hres
    simp only [Scheme.resHom_resHom] at hres
    have hself : (relCurve C R).resHom
        ((le_inf (le_inf le_top (inf_le_right.trans (A.pieces_inl_le i.down)))
          inf_le_right).trans
          (le_inf le_top inf_le_right) :
          (⊤ ⊓ A.pieces (Sum.inl i.down) : (relCurve C R).Opens)
            ≤ ⊤ ⊓ A.pieces (Sum.inl i.down)) (s.val (Sum.inl i))
        = s.val (Sum.inl i) := Scheme.resHom_self _ _
    rw [hself] at hres
    -- conclude by uniqueness of the cofactor
    exact (A.eqnDiv_unique (Sum.inl i.down)
      (inf_le_right : ⊤ ⊓ A.pieces (Sum.inl i.down) ≤ A.pieces (Sum.inl i.down))
      (vanishingSide_germ_mem (gluedToVanishing A a s) (Sum.inl i.down))
      (hres.symm)).symm
  · have hcomp : A.gluedComp₁ (secRes ((A.thetaIdealDatum a).sheaf)
        (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁ ≤ ⊤) s) j.down
        = (relCurve C R).resHom
            (le_inf le_top inf_le_right :
              ((⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁) ⊓ A.pieces (Sum.inr j.down) :
                (relCurve C R).Opens) ≤ ⊤ ⊓ A.pieces (Sum.inr j.down))
            (s.val (Sum.inr j)) := rfl
    have hres := congrArg ((relCurve C R).resHom
      (le_inf (le_inf le_top (inf_le_right.trans (A.pieces_inr_le j.down)))
        inf_le_right :
        (⊤ ⊓ A.pieces (Sum.inr j.down) : (relCurve C R).Opens)
          ≤ (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁) ⊓ A.pieces (Sum.inr j.down)))
      (res_gluedToIdeal₁
        (inf_le_right : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁
          ≤ (relCover C R (fiberTwoCover π)).V₁)
        (secRes ((A.thetaIdealDatum a).sheaf)
          (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁ ≤ ⊤) s) j.down)
    rw [map_mul, hcomp] at hres
    simp only [Scheme.resHom_resHom] at hres
    have hself : (relCurve C R).resHom
        ((le_inf (le_inf le_top (inf_le_right.trans (A.pieces_inr_le j.down)))
          inf_le_right).trans
          (le_inf le_top inf_le_right) :
          (⊤ ⊓ A.pieces (Sum.inr j.down) : (relCurve C R).Opens)
            ≤ ⊤ ⊓ A.pieces (Sum.inr j.down)) (s.val (Sum.inr j))
        = s.val (Sum.inr j) := Scheme.resHom_self _ _
    rw [hself] at hres
    exact (A.eqnDiv_unique (Sum.inr j.down)
      (inf_le_right : ⊤ ⊓ A.pieces (Sum.inr j.down) ≤ A.pieces (Sum.inr j.down))
      (vanishingSide_germ_mem (gluedToVanishing A a s) (Sum.inr j.down))
      (hres.symm)).symm

variable (A a) in
/-- **THE JUNCTION EQUIVALENCE** (`informal/spec-dd-r.md` §3 item 4, the probed seam):
the global sections of the theta-ideal datum sheaf are `R`-linearly the vanishing
submodule `K_a(d) = H⁰(𝒪(Θᵃ − d))` — DD-1's carrier vocabulary meets the engine's glued
sheaf, mutually inverse by uniqueness of cofactors over the regular equations. -/
noncomputable def gluedEquivVanishing :
    A.ThetaIdealSections a ⊤ ≃ₗ[R]
      ↥(d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a)) :=
  { gluedToVanishingₗ A a with
    invFun := vanishingToGlued A a
    left_inv := vanishingToGlued_gluedToVanishing
    right_inv := gluedToVanishing_vanishingToGlued }

variable (A a) in
/-- The junction in the engine's `H⁰`-carrier form: `H⁰(C_R, F_{Θᵃ−d}) ≃ₗ[R] K_a(d)`. -/
noncomputable def datumH0EquivVanishing :
    Sheaf.HModule (A.thetaIdealDatum a).sheaf 0 ≃ₗ[R]
      ↥(d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a)) :=
  (Sheaf.HModule.linearEquiv₀
    (Opens.grothendieckTopology ((relCurve C R : Scheme.{u}) : TopCat))
    (isTerminalTop) ((A.thetaIdealDatum a).sheaf)).trans (gluedEquivVanishing A a)

end Equiv

/-! ## The engine transport: `K_a(d)` is finite projective (the certificate seam)

The rigid engine fired on the theta-ideal datum (`datumRigidEngine`, all standing
hypotheses discharged) under the complex-form fibrewise `h¹`-data — the P-fib fibrewise
boundary, in exactly the shape `thetaGluedEval_surjective` consumes — transported along
the junction. -/

section Engine

variable (A a) in
/-- **`H¹(C_R, 𝒪(Θᵃ − d)) = 0`** under the fibrewise `h¹`-data of the theta-ideal
datum (Noetherian test ring). -/
theorem subsingleton_hModule_thetaIdealDatum_one [IsNoetherianRing R]
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hfib : ∀ p : PrimeSpectrum R,
      Subsingleton ((datumPair (A.thetaIdealDatum a)).H1 ⊗[R]
        p.asIdeal.ResidueField)) :
    Subsingleton (Sheaf.HModule (A.thetaIdealDatum a).sheaf 1) :=
  (datumRigidEngine (A.thetaIdealDatum a) hπ hfib).1

variable (A a) in
/-- **The certificate transport, finiteness**: the vanishing submodule
`K_a(d) = H⁰(𝒪(Θᵃ − d))` is a finite `R`-module — the engine's finiteness on the datum
`H⁰`, transported along the junction. -/
theorem finite_vanishingSubmodule [IsNoetherianRing R]
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hfib : ∀ p : PrimeSpectrum R,
      Subsingleton ((datumPair (A.thetaIdealDatum a)).H1 ⊗[R]
        p.asIdeal.ResidueField)) :
    Module.Finite R ↥(d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
      (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a)) := by
  haveI := (datumRigidEngine (A.thetaIdealDatum a) hπ hfib).2.1
  exact Module.Finite.equiv (datumH0EquivVanishing A a)

variable (A a) in
/-- **The certificate transport, projectivity**: `K_a(d)` is a projective `R`-module. -/
theorem projective_vanishingSubmodule [IsNoetherianRing R]
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hfib : ∀ p : PrimeSpectrum R,
      Subsingleton ((datumPair (A.thetaIdealDatum a)).H1 ⊗[R]
        p.asIdeal.ResidueField)) :
    Module.Projective R ↥(d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
      (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a)) := by
  haveI := (datumRigidEngine (A.thetaIdealDatum a) hπ hfib).2.2
  exact Module.Projective.of_equiv (datumH0EquivVanishing A a)

end Engine

end DivisorAdaptation

/-! ## The window transport: `K_a(d) ⊆ R ⊗[k] H_a` is finite projective -/

section Window

noncomputable local instance instOverCleftCert : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]

variable {d : (relCurve C R).LocalEquations} {a : ℕ}

/-- **The window form of the junction**: the window submodule `K_a(d) ⊆ R ⊗[k] H_a` is
`R`-linearly the vanishing submodule, through the window identification
(`relThetaWindowEquiv` maps one onto the other). -/
noncomputable def divisorWindowEquivVanishing
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1) :
    ↥(divisorWindow d hH1) ≃ₗ[R]
      ↥(d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a)) :=
  LinearEquiv.ofSubmodules (relThetaWindowEquiv C R π a hH1) _ _
    (Submodule.map_comap_eq_of_surjective
      (relThetaWindowEquiv C R π a hH1).surjective _)

variable {A : DivisorAdaptation C R π d}

variable (A a) in
/-- **The certificate transport on the window carrier, finiteness**: the window
submodule `K_a(d) ⊆ R ⊗[k] H_a` is a finite `R`-module. -/
theorem finite_divisorWindow [IsNoetherianRing R]
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hfib : ∀ p : PrimeSpectrum R,
      Subsingleton ((datumPair (A.thetaIdealDatum a)).H1 ⊗[R]
        p.asIdeal.ResidueField)) :
    Module.Finite R ↥(divisorWindow d hH1) := by
  haveI := DivisorAdaptation.finite_vanishingSubmodule A a hπ hfib
  exact Module.Finite.equiv (divisorWindowEquivVanishing hH1).symm

variable (A a) in
/-- **The certificate transport on the window carrier, projectivity**: `K_a(d)` is a
projective `R`-module — with finiteness, exactly the shape `divisorWindowGr`'s ambient
comparisons and the DDR-5 rank argument consume. -/
theorem projective_divisorWindow [IsNoetherianRing R]
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hfib : ∀ p : PrimeSpectrum R,
      Subsingleton ((datumPair (A.thetaIdealDatum a)).H1 ⊗[R]
        p.asIdeal.ResidueField)) :
    Module.Projective R ↥(divisorWindow d hH1) := by
  haveI := DivisorAdaptation.projective_vanishingSubmodule A a hπ hfib
  exact Module.Projective.of_equiv (divisorWindowEquivVanishing hH1).symm

variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]

variable (A a) in
/-- **(c2)-finiteness of the Θ-twisted colength module**: under the fibrewise `h¹`-data
of the theta-ideal datum, `W(d)^{Θᵃ}` is a finite `R`-module — the surjective image of
the free window `R ⊗[k] H_a` under the (engine-fired) window carve arrow.  The
projectivity and rank clauses of (c2) are the remaining DDR-4 obligations (they need
the ambient identification of DDR-5's equality input). -/
theorem finite_thetaGlued
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hfib : ∀ p : PrimeSpectrum R,
      Subsingleton ((datumPair (A.thetaIdealDatum a)).H1 ⊗[R]
        p.asIdeal.ResidueField)) :
    Module.Finite R (A.ThetaGlued a) :=
  Module.Finite.of_surjective (windowCarve A hH1)
    (windowCarve_surjective A hH1
      (DivisorAdaptation.thetaGluedEval_surjective hπ hfib))

end Window

end AlgebraicGeometry
