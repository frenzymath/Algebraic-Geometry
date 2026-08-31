/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GrassmannianChartFrame
import AlgebraicJacobian.Picard.DivCarveKit
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing

/-!
# G-5 kit: ambient transport, matrix presentations from free quotients, frame selection
(DDR-9 support)

The module-algebra kit of the G-5 frame-locus cover (`informal/w4-g5-worksheet.md` §1.1;
parent `informal/spec-w4-gates.md` Addendum 1 §G-5).  No curve, no scheme: everything
here is linear algebra over commutative rings, consumed by
`Picard/DivSchemeFrameCover.lean`.

* **K1 — ambient coordinate transport** (`congrAmbient`): a `k`-linear identification of
  ambient spaces `H ≃ₗ[k] H'` moves Grassmannian points of `grFunctorAff k H g T` to
  points of `grFunctorAff k H' g T` by `Submodule.map` of the base-changed equivalence;
  the quotient certificate travels along `congrAmbientQuotEquiv`.
* **K4 — naturality of K1** (`map_congrAmbient`): ambient transport commutes with
  mathlib's `Module.Grassmannian.map` along any test map.  Submodule content:
  `ker_baseChangeMkQ_eq_map_baseChange` (DivCarveKit) on both sides plus the
  `cancelBaseChange` naturality square, with the base-change/`Submodule.map` exchange
  `baseChange_map_submodule`.
* **K2 — matrix presentation from a free quotient**
  (`exists_matrixPoint_eq_of_free`): a coordinate Grassmannian point with FREE quotient
  is a matrix point — the matrix reads the quotient-basis coordinates of the images of
  the ambient generators through `LinearMap.toMatrix'` (quotient frame convention,
  worksheet §0.1: no submodule-side generators are ever chosen).
* **K5 — frame-minor selection** (`exists_isUnit_det_submatrix_of_mul_eq_one`,
  `exists_det_submatrix_notMem_of_mul_eq_one`): a right-invertible `d × r` matrix over a
  field has an invertible column `I`-minor (transcription of GR-Quot's private
  `exists_isUnit_submatrix`, `GrassmannianQuot.lean:2586`); over any ring, at any prime
  `q` the minor can be chosen with determinant outside `q` (residue-field argument
  through `FractionRing (T ⧸ q)`).
* **K3 — free localization of a finite projective module**
  (`exists_away_free_pair`): for finite projective `Q₁, Q₂` and a prime `p` there is
  `h ∉ p` with both `(Localization.Away h) ⊗[S] Qᵢ` free — mathlib's
  `Module.FinitePresentation.exists_free_localizedModule_powers` bridged to the tensor
  spelling and pushed up the localization tower (`free_baseChange_away_mul`).
* **K6 — the numerator stage** (`exists_away_isUnit_of_notMem`): from `c ∉ q` over
  `Localization.Away h` (`q` a prime over `p`), an element `u ∉ p` divisible by `h`
  such that EVERY factoring `Localization.Away h →+* T` over an away-`u` localization
  sends `c` to a unit.
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgebraicGeometry.Grassmannian

/-! ## K1/K4: ambient coordinate transport and its naturality -/

section CongrAmbient

variable {k : Type u} [Field k]
variable {H H' : Type u} [AddCommGroup H] [Module k H] [AddCommGroup H'] [Module k H']
variable {g : ℕ} {T : Type u} [CommRing T] [Algebra k T]

/-- The quotient comparison of the ambient transport: quotients by a submodule and by
its image under the base-changed ambient equivalence agree. -/
noncomputable def congrAmbientQuotEquiv (e : H ≃ₗ[k] H') (x : grFunctorAff k H g T) :
    (TensorProduct k T H ⧸ x.toSubmodule) ≃ₗ[T]
      (TensorProduct k T H' ⧸
        Submodule.map (LinearMap.baseChange T e.toLinearMap) x.toSubmodule) :=
  Submodule.Quotient.equiv x.toSubmodule _ (LinearEquiv.baseChange k T H H' e) rfl

/-- **K1 — ambient coordinate transport**: a `k`-linear identification of ambient
spaces carries Grassmannian points across, by `Submodule.map` of the base-changed
equivalence.  Packages the coordinate points `K^c` of the G-5 worksheet (§1.1): the
window points of `ε` read through the DD-4 boundary bases. -/
noncomputable def congrAmbient (e : H ≃ₗ[k] H') (x : grFunctorAff k H g T) :
    grFunctorAff k H' g T where
  toSubmodule := Submodule.map (LinearMap.baseChange T e.toLinearMap) x.toSubmodule
  finite_quotient := Module.Finite.equiv (congrAmbientQuotEquiv e x)
  projective_quotient := Module.Projective.of_equiv (congrAmbientQuotEquiv e x)
  rankAtStalk_eq p := by
    rw [← congrFun (Module.rankAtStalk_eq_of_equiv (congrAmbientQuotEquiv e x)) p]
    exact x.rankAtStalk_eq p

@[simp]
lemma congrAmbient_toSubmodule (e : H ≃ₗ[k] H') (x : grFunctorAff k H g T) :
    (congrAmbient e x).toSubmodule
      = Submodule.map (LinearMap.baseChange T e.toLinearMap) x.toSubmodule :=
  rfl

/-- Freeness of the quotient transports across the ambient identification. -/
theorem free_quotient_congrAmbient (e : H ≃ₗ[k] H') (x : grFunctorAff k H g T)
    (hfree : Module.Free T (TensorProduct k T H ⧸ x.toSubmodule)) :
    Module.Free T (TensorProduct k T H' ⧸ (congrAmbient e x).toSubmodule) :=
  haveI := hfree
  Module.Free.of_equiv (congrAmbientQuotEquiv e x)

/-- `Submodule.baseChange` exchanges with `Submodule.map`: the base change of a mapped
submodule is the image of the base-changed submodule under the base-changed map. -/
theorem baseChange_map_submodule {R : Type u} [CommRing R] {M M' : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (A : Type u) [CommRing A] [Algebra R A] (f : M →ₗ[R] M') (N : Submodule R M) :
    (Submodule.map f N).baseChange A
      = Submodule.map (LinearMap.baseChange A f) (N.baseChange A) := by
  have hcomp : f ∘ₗ N.subtype = (Submodule.map f N).subtype ∘ₗ f.submoduleMap N :=
    LinearMap.ext fun x => rfl
  have h1 : (Submodule.map f N).baseChange A
      = LinearMap.range (LinearMap.baseChange A (Submodule.map f N).subtype) := rfl
  have h2 : N.baseChange A = LinearMap.range (LinearMap.baseChange A N.subtype) := rfl
  rw [h1, h2, ← LinearMap.range_comp, ← LinearMap.baseChange_comp, hcomp,
    LinearMap.baseChange_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (LinearMap.baseChange_surjective A
      (LinearMap.submoduleMap_surjective f N)), Submodule.map_top]

/-- **K4 — naturality of the ambient transport**: `congrAmbient` commutes with
mathlib's `Module.Grassmannian.map` along any `k`-algebra map.  Submodule content: the
`ker (baseChangeMkQ)` description of both sides (`ker_baseChangeMkQ_eq_map_baseChange`,
projective-quotient instances are the points' own) plus the `cancelBaseChange`
naturality square. -/
theorem map_congrAmbient {T' : Type u} [CommRing T'] [Algebra k T'] (α : T →ₐ[k] T')
    (e : H ≃ₗ[k] H') (x : grFunctorAff k H g T) :
    Module.Grassmannian.map α (congrAmbient e x)
      = congrAmbient e (Module.Grassmannian.map α x) := by
  letI : Algebra T T' := α.toAlgebra
  letI : IsScalarTower k T T' :=
    IsScalarTower.of_algebraMap_eq' (IsScalarTower.algebraMap_eq k T T')
  haveI hproj : Module.Projective T (TensorProduct k T H' ⧸
      Submodule.map (LinearMap.baseChange T e.toLinearMap) x.toSubmodule) :=
    (congrAmbient e x).projective_quotient
  refine Module.Grassmannian.ext ?_
  have h1 := Module.Grassmannian.map_toSubmodule α (congrAmbient e x)
  have h2 := Module.Grassmannian.map_toSubmodule α x
  rw [h1, congrAmbient_toSubmodule, congrAmbient_toSubmodule, h2,
    Grassmannian.ker_baseChangeMkQ_eq_map_baseChange T'
      (Submodule.map (LinearMap.baseChange T e.toLinearMap) x.toSubmodule),
    Grassmannian.ker_baseChangeMkQ_eq_map_baseChange T' x.toSubmodule,
    baseChange_map_submodule, ← Submodule.map_comp, ← Submodule.map_comp,
    cancelBaseChange_comp_baseChange_baseChange T' e.toLinearMap]

/-- Ambient transport composes along linear equivalences. -/
theorem congrAmbient_trans {H'' : Type u} [AddCommGroup H''] [Module k H'']
    (e : H ≃ₗ[k] H') (e' : H' ≃ₗ[k] H'') (x : grFunctorAff k H g T) :
    congrAmbient e' (congrAmbient e x) = congrAmbient (e.trans e') x := by
  apply Module.Grassmannian.ext
  rw [congrAmbient_toSubmodule, congrAmbient_toSubmodule,
    congrAmbient_toSubmodule, ← Submodule.map_comp, ← LinearMap.baseChange_comp]
  rfl

/-- Transporting an ambient Grassmannian point through an equivalence and back is trivial. -/
theorem congrAmbient_symm_cancel (e : H ≃ₗ[k] H') (x : grFunctorAff k H' g T) :
    congrAmbient e (congrAmbient e.symm x) = x := by
  rw [congrAmbient_trans]
  exact Module.Grassmannian.ext (by simp)

end CongrAmbient

/-! ## K2: a matrix presentation from a free quotient -/

section MatrixFromFree

variable {k : Type u} [Field k]

/-- **K2 — matrix presentation from a free quotient** (quotient frame convention,
worksheet §0.1): a coordinate Grassmannian point over a nontrivial ring whose quotient
is FREE is a matrix point.  The matrix is `LinearMap.toMatrix'` of the composite
"quotient map then quotient-basis coordinates", read through the coordinate
identification — its columns are the quotient-basis coordinates of the images of the
standard ambient generators; no submodule-side generators are chosen. -/
theorem exists_matrixPoint_eq_of_free {T : Type u} [CommRing T] [Algebra k T]
    [Nontrivial T] {g r : ℕ} (x : grFunctorAff k (Fin r → k) g T)
    (hfree : Module.Free T (TensorProduct k T (Fin r → k) ⧸ x.toSubmodule)) :
    ∃ (X : Matrix (Fin g) (Fin r) T) (hX : Function.Surjective (matrixProj k g r T X)),
      matrixPoint k g r T X hX = x := by
  haveI := hfree
  -- the free quotient has rank `g`: the point's own stalk-rank clause at any prime
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum T) := inferInstance
  have hfin : Module.finrank T (TensorProduct k T (Fin r → k) ⧸ x.toSubmodule) = g := by
    have h1 := x.rankAtStalk_eq p
    rwa [congrFun (Module.rankAtStalk_eq_finrank_of_free
      (R := T) (M := TensorProduct k T (Fin r → k) ⧸ x.toSubmodule)) p] at h1
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex T
      (TensorProduct k T (Fin r → k) ⧸ x.toSubmodule)) = g := by
    rw [← Module.finrank_eq_card_chooseBasisIndex]
    exact hfin
  set b : Module.Basis (Fin g) T (TensorProduct k T (Fin r → k) ⧸ x.toSubmodule) :=
    (Module.Free.chooseBasis T _).reindex (Fintype.equivFinOfCardEq hcard) with hb
  set φ : TensorProduct k T (Fin r → k) →ₗ[T] (Fin g → T) :=
    b.equivFun.toLinearMap ∘ₗ x.toSubmodule.mkQ with hφ
  set X : Matrix (Fin g) (Fin r) T := LinearMap.toMatrix'
    (φ ∘ₗ (TensorProduct.piScalarRight k T T (Fin r)).symm.toLinearMap) with hXdef
  -- the matrix presentation IS `φ`
  have hproj : matrixProj k g r T X = φ := by
    have hcancel : (TensorProduct.piScalarRight k T T (Fin r)).symm.toLinearMap ∘ₗ
        (TensorProduct.piScalarRight k T T (Fin r)).toLinearMap = LinearMap.id :=
      LinearMap.ext fun z => by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
          LinearEquiv.symm_apply_apply, LinearMap.id_apply]
    rw [matrixProj, hXdef, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix',
      LinearMap.comp_assoc, hcancel, LinearMap.comp_id]
  have hXs : Function.Surjective (matrixProj k g r T X) := by
    rw [hproj, hφ, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap]
    exact b.equivFun.surjective.comp x.toSubmodule.mkQ_surjective
  refine ⟨X, hXs, Module.Grassmannian.ext ?_⟩
  rw [matrixPoint_toSubmodule, hproj, hφ, LinearMap.ker_comp,
    show LinearMap.ker b.equivFun.toLinearMap = ⊥ from LinearEquiv.ker b.equivFun]
  exact x.toSubmodule.ker_mkQ

end MatrixFromFree

/-! ## K5: frame-minor selection -/

section MinorSelect

/-- **K5, field form — right-invertible matrices over a field have an invertible column
minor**: a `d × r` matrix with a right inverse has an invertible `d × d` submatrix on
the columns of some size-`d` subset `I`, enumerated by `I.orderIsoOfFin` (the
`frameMinor` spelling).  Pure linear algebra: the columns span `F^d`, a spanning set
contains a basis, and a square matrix with independent columns is invertible.
Transcription of GR-Quot's private `exists_isUnit_submatrix`
(`GrassmannianQuot.lean:2586`). -/
theorem exists_isUnit_det_submatrix_of_mul_eq_one {F : Type u} [Field F] {d r : ℕ}
    (X : Matrix (Fin d) (Fin r) F) (Y : Matrix (Fin r) (Fin d) F) (hXY : X * Y = 1) :
    ∃ (I : Finset (Fin r)) (hI : I.card = d),
      IsUnit (X.submatrix id fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)).det := by
  classical
  -- the columns of `X` span `F^d` (a right inverse makes `mulVec` surjective)
  have hspan : Submodule.span F (Set.range X.col) = ⊤ := by
    rw [← Matrix.range_mulVecLin, LinearMap.range_eq_top]
    intro v
    refine ⟨Y.mulVec v, ?_⟩
    change X.mulVec (Y.mulVec v) = v
    rw [Matrix.mulVec_mulVec, hXY, Matrix.one_mulVec]
  -- extract a linearly independent spanning subset `b` of the column set
  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent F (Set.range X.col)
  rw [hspan] at hbspan
  haveI : Fintype b := ((Set.finite_range X.col).subset hbsub).fintype
  -- `b` is a basis, so it has exactly `d` elements
  let B : Module.Basis b F (Fin d → F) :=
    Module.Basis.mk hbind (by rw [Subtype.range_coe, hbspan])
  have hcard : Fintype.card b = d := by
    have h1 := Module.finrank_eq_card_basis B
    rw [Module.finrank_pi F, Fintype.card_fin] at h1
    exact h1.symm
  -- choose a column index for each element of `b`
  have hchoice : ∀ v : b, ∃ j : Fin r, X.col j = (v : Fin d → F) := fun v => hbsub v.2
  choose φ hφ using hchoice
  have hφinj : Function.Injective φ := fun u v huv => by
    apply Subtype.ext
    rw [← hφ u, ← hφ v, huv]
  have hIcard : (Finset.univ.image φ).card = d := by
    rw [Finset.card_image_of_injective _ hφinj, Finset.card_univ, hcard]
  refine ⟨Finset.univ.image φ, hIcard, ?_⟩
  -- each enumerated column lies in `b`
  have hcol : ∀ j : Fin d,
      X.col (((Finset.univ.image φ).orderIsoOfFin hIcard j : Fin r)) ∈ b := by
    intro j
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp
      ((Finset.univ.image φ).orderIsoOfFin hIcard j).2
    rw [← hv, hφ v]
    exact v.2
  set c : Fin d → b :=
    fun j => ⟨X.col (((Finset.univ.image φ).orderIsoOfFin hIcard j : Fin r)), hcol j⟩
    with hcdef
  have hcinj : Function.Injective c := by
    intro j j' hjj
    have hcols : X.col (((Finset.univ.image φ).orderIsoOfFin hIcard j : Fin r))
        = X.col (((Finset.univ.image φ).orderIsoOfFin hIcard j' : Fin r)) :=
      congrArg Subtype.val hjj
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp
      ((Finset.univ.image φ).orderIsoOfFin hIcard j).2
    obtain ⟨v', -, hv'⟩ := Finset.mem_image.mp
      ((Finset.univ.image φ).orderIsoOfFin hIcard j').2
    have hvv' : v = v' := by
      apply Subtype.ext
      calc (v : Fin d → F)
          = X.col (φ v) := (hφ v).symm
        _ = X.col (((Finset.univ.image φ).orderIsoOfFin hIcard j : Fin r)) := by rw [hv]
        _ = X.col (((Finset.univ.image φ).orderIsoOfFin hIcard j' : Fin r)) := hcols
        _ = X.col (φ v') := by rw [hv']
        _ = (v' : Fin d → F) := hφ v'
    have hee : (((Finset.univ.image φ).orderIsoOfFin hIcard j : Fin r))
        = (((Finset.univ.image φ).orderIsoOfFin hIcard j' : Fin r)) := by
      rw [← hv, ← hv', hvv']
    exact ((Finset.univ.image φ).orderIsoOfFin hIcard).injective (Subtype.ext hee)
  -- the columns of the submatrix are the inclusion of `b` along the injective `c`
  have hSind : LinearIndependent F
      (X.submatrix id fun j : Fin d =>
        (((Finset.univ.image φ).orderIsoOfFin hIcard j : Fin r))).col := by
    have heq : (X.submatrix id fun j : Fin d =>
        (((Finset.univ.image φ).orderIsoOfFin hIcard j : Fin r))).col
        = fun j => ((c j : Fin d → F)) := by
      funext j
      rfl
    rw [heq]
    exact hbind.comp c hcinj
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hSind)

/-- **K5, prime form**: over any commutative ring, a right-invertible `d × r` matrix
has, at each prime `q`, a column `I`-minor whose determinant lies OUTSIDE `q` — apply
the field form over the residue field `FractionRing (T ⧸ q)`. -/
theorem exists_det_submatrix_notMem_of_mul_eq_one {T : Type u} [CommRing T]
    (q : Ideal T) [q.IsPrime] {d r : ℕ} (X : Matrix (Fin d) (Fin r) T)
    (Y : Matrix (Fin r) (Fin d) T) (hXY : X * Y = 1) :
    ∃ (I : Finset (Fin r)) (hI : I.card = d),
      (X.submatrix id fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)).det ∉ q := by
  set φ : T →+* FractionRing (T ⧸ q) :=
    (algebraMap (T ⧸ q) (FractionRing (T ⧸ q))).comp (Ideal.Quotient.mk q) with hφdef
  have hker : ∀ z : T, φ z = 0 ↔ z ∈ q := fun z => by
    rw [hφdef, RingHom.comp_apply,
      map_eq_zero_iff _ (IsFractionRing.injective (T ⧸ q) (FractionRing (T ⧸ q))),
      Ideal.Quotient.eq_zero_iff_mem]
  have hmap : (X.map φ) * (Y.map φ) = 1 := by
    rw [← Matrix.map_mul, hXY, Matrix.map_one φ (map_zero φ) (map_one φ)]
  obtain ⟨I, hI, hu⟩ := exists_isUnit_det_submatrix_of_mul_eq_one (X.map φ) (Y.map φ) hmap
  refine ⟨I, hI, fun hmem => ?_⟩
  rw [Matrix.submatrix_map] at hu
  have hdet : ((X.submatrix id fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)).map φ).det
      = φ (X.submatrix id fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  rw [hdet] at hu
  exact hu.ne_zero ((hker _).mpr hmem)

end MinorSelect

/-! ## K3: free localization of a finite projective module -/

section AwayFree

variable {S : Type u} [CommRing S] {Q : Type u} [AddCommGroup Q] [Module S Q]

/-- The tensor spelling of localized-module freeness: if `LocalizedModule.Away h Q` is
free then so is `(Localization.Away h) ⊗[S] Q`. -/
theorem free_baseChange_of_free_localizedModule (h : S)
    (hfree : Module.Free (Localization.Away h) (LocalizedModule.Away h Q)) :
    Module.Free (Localization.Away h) (TensorProduct S (Localization.Away h) Q) := by
  haveI := hfree
  exact Module.Free.of_equiv
    ((IsLocalizedModule.iso (Submonoid.powers h)
        (TensorProduct.mk S (Localization.Away h) Q 1)).extendScalarsOfIsLocalization
      (Submonoid.powers h) (Localization.Away h))

set_option maxHeartbeats 400000 in
-- The scalar-tower check unfolds `Localization` quotient structure; elaboration cost.
/-- Freeness of the away-localized module survives a further away localization:
`(Away h) ⊗ Q` free implies `(Away (h·s)) ⊗ Q` free, along `awayToAwayRight`. -/
theorem free_baseChange_away_mul (h s : S)
    (hfree : Module.Free (Localization.Away h) (TensorProduct S (Localization.Away h) Q)) :
    Module.Free (Localization.Away (h * s))
      (TensorProduct S (Localization.Away (h * s)) Q) := by
  haveI := hfree
  letI : Algebra (Localization.Away h) (Localization.Away (h * s)) :=
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away h) h s).toAlgebra
  haveI : IsScalarTower S (Localization.Away h) (Localization.Away (h * s)) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [RingHom.algebraMap_toAlgebra]
    exact (IsLocalization.Away.lift_comp h _).symm
  exact Module.Free.of_equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S (Localization.Away h)
      (Localization.Away (h * s)) (Localization.Away (h * s)) Q)

/-- **K3, single module**: a finite projective module over `S` becomes free on a basic
open neighbourhood of any prime — mathlib's spread-out
(`Module.FinitePresentation.exists_free_localizedModule_powers`) in the tensor
spelling. -/
theorem exists_away_free (p : PrimeSpectrum S) [Module.Finite S Q]
    [Module.Projective S Q] :
    ∃ h : S, h ∉ p.asIdeal ∧
      Module.Free (Localization.Away h) (TensorProduct S (Localization.Away h) Q) := by
  haveI := Module.finitePresentation_of_projective S Q
  have hp : p ∈ Module.freeLocus S Q := by
    rw [Module.freeLocus_eq_univ_iff.mpr ‹Module.Projective S Q›]
    trivial
  haveI hfree : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl Q) := Module.mem_freeLocus.mp hp
  obtain ⟨h, hh, hfree', -⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl Q)
      (Localization.AtPrime p.asIdeal)
  exact ⟨h, hh, free_baseChange_of_free_localizedModule h hfree'⟩

/-- **K3 — free localization of a pair**: for finite projective `Q₁, Q₂` and a prime
`p` there is a single `h ∉ p` with both `(Localization.Away h) ⊗[S] Qᵢ` free — take the
product of the two per-module choices. -/
theorem exists_away_free_pair (p : PrimeSpectrum S) (Q₁ Q₂ : Type u) [AddCommGroup Q₁]
    [Module S Q₁] [AddCommGroup Q₂] [Module S Q₂] [Module.Finite S Q₁]
    [Module.Projective S Q₁] [Module.Finite S Q₂] [Module.Projective S Q₂] :
    ∃ h : S, h ∉ p.asIdeal ∧
      Module.Free (Localization.Away h) (TensorProduct S (Localization.Away h) Q₁) ∧
      Module.Free (Localization.Away h) (TensorProduct S (Localization.Away h) Q₂) := by
  obtain ⟨h₁, hh₁, hf₁⟩ := exists_away_free (Q := Q₁) p
  obtain ⟨h₂, hh₂, hf₂⟩ := exists_away_free (Q := Q₂) p
  refine ⟨h₁ * h₂, fun hmem => ?_, free_baseChange_away_mul h₁ h₂ hf₁, ?_⟩
  · rcases p.isPrime.mem_or_mem hmem with hin | hin
    exacts [hh₁ hin, hh₂ hin]
  · rw [mul_comm]
    exact free_baseChange_away_mul h₂ h₁ hf₂

end AwayFree

/-! ## K6: the numerator stage -/

section AwayNumerator

/-- **K6 — the numerator stage** (basic-open bookkeeping): let `q` be a prime of
`Localization.Away h` over `p` (with `h ∉ p`) and `c ∉ q`.  Writing `c = a / hⁿ`, the
element `u := h·a` lies outside `p`, and every ring map `Localization.Away h →+* T`
into an away-`u` localization that commutes with the structure maps sends `c` to a
unit. -/
theorem exists_away_isUnit_of_notMem {S : Type u} [CommRing S] (h : S) {p : Ideal S}
    [p.IsPrime] (hh : h ∉ p) {q : Ideal (Localization.Away h)} [q.IsPrime]
    (hq : Ideal.comap (algebraMap S (Localization.Away h)) q = p)
    (c : Localization.Away h) (hc : c ∉ q) :
    ∃ u : S, u ∉ p ∧ h ∣ u ∧
      ∀ (T : Type u) [CommRing T] [Algebra S T] [IsLocalization.Away u T]
        (β : Localization.Away h →+* T),
        β.comp (algebraMap S (Localization.Away h)) = algebraMap S T → IsUnit (β c) := by
  obtain ⟨⟨a, s⟩, hspec⟩ := IsLocalization.surj (M := Submonoid.powers h) c
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  -- the numerator avoids `p`
  have hanp : a ∉ p := by
    intro hain
    have haq : algebraMap S (Localization.Away h) a ∈ q := by
      rw [← hq] at hain
      exact hain
    rw [← hspec] at haq
    rcases (Ideal.IsPrime.mem_or_mem ‹q.IsPrime› haq) with hcq | hsq
    · exact hc hcq
    · have hus : IsUnit (algebraMap S (Localization.Away h) s.1) := by
        rw [← hn, map_pow]
        exact (IsLocalization.Away.algebraMap_isUnit h).pow n
      exact (Ideal.IsPrime.ne_top ‹q.IsPrime›) (q.eq_top_of_isUnit_mem hsq hus)
  refine ⟨h * a, fun hmem => ?_, Dvd.intro a rfl, ?_⟩
  · rcases ‹p.IsPrime›.mem_or_mem hmem with hin | hin
    exacts [hh hin, hanp hin]
  · intro T _ _ _ β hβ
    -- the defining relation of `c`, pushed into `T`
    have h1 : β c * algebraMap S T s.1 = algebraMap S T a := by
      have h2 := congrArg β hspec
      rwa [map_mul,
        show β (algebraMap S (Localization.Away h) s.1) = algebraMap S T s.1 from by
          rw [← RingHom.comp_apply, hβ],
        show β (algebraMap S (Localization.Away h) a) = algebraMap S T a from by
          rw [← RingHom.comp_apply, hβ]] at h2
    have hmulunit : IsUnit (algebraMap S T h * algebraMap S T a) := by
      rw [← map_mul]
      exact IsLocalization.Away.algebraMap_isUnit (h * a)
    have hua : IsUnit (algebraMap S T a) := isUnit_of_mul_isUnit_right hmulunit
    rw [← h1] at hua
    exact isUnit_of_mul_isUnit_left hua

end AwayNumerator

end AlgebraicGeometry.Grassmannian
