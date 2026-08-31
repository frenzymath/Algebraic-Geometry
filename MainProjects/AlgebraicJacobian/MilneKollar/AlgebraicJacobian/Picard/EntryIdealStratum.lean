/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.EntryIdeal
import AlgebraicJacobian.Picard.QuotScheme
import AlgebraicJacobian.Cohomology.PullbackQuasicoherent

/-!
# Rank strata of a coherent module: geometric substrate (Nitsure §4, `n = 0`)

This file builds the geometric layer between the entry-ideal commutative
algebra of `AlgebraicJacobian.Picard.EntryIdeal` and the universal property
of the flat-locus stratification
(`AlgebraicGeometry.flatLocusStratification_universal` in
`AlgebraicJacobian.Picard.GenericFlatnessGeometric`), following the special
case `n = 0` of the flattening-stratification theorem in [Nitsure, §4].

## Contents

* §1 — presentation transport (`Module.MatrixPresentation.congr`) and the
  basic properties of the fiber rank: monotonicity under `e`-generator
  presentations (`fiberRank_le`), invariance under linear equivalences
  (`Ideal.fiberRank_congr`), base change
  (`Ideal.fiberRank_baseChange`: the fiber of `A ⊗[R] M` at a prime `q`
  has the same dimension as the fiber of `M` at `q ∩ R`), and the
  localized-module corollary (`Ideal.fiberRank_of_isLocalizedModule`).
* §2 — the point ↔ prime dictionary for affine opens:
  membership in `Scheme.zeroLocus`/`Scheme.basicOpen` in terms of
  `IsAffineOpen.primeIdealOf`.
* §3 — presentation charts: affine opens `V` on which the section module
  `Γ(G, V)` admits an `e`-generator matrix presentation; stability under
  basic-open localization (via the quasi-coherent section-localization
  engine `Scheme.Modules.isLocalizedModule_basicOpen` of
  `AlgebraicJacobian.Picard.QuotScheme`); the point-rank function and its
  chart-independence.

Blueprint chapter: `Picard_FlatteningStratification.tex`,
§`sec:flatstrat_universal`.
Source: [Nitsure], §4, proof of the flattening-stratification theorem,
special case `n = 0` (`references/nitsure-hilbert-quot-src/`
`nitsure-hilbert-quot.tex`, L1849–L1885).
-/

universe u

open TensorProduct

/-! ## §1 Presentation transport and basic properties of the fiber rank -/

namespace Module.MatrixPresentation

section Congr

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
variable {N : Type u} [AddCommGroup N] [Module R N] {e m : ℕ}

/-- Transport of a matrix presentation along a linear equivalence of the
presented module; the relation matrix — hence the entry ideal — is
unchanged. -/
noncomputable def congr (P : MatrixPresentation R M e m) (σ : M ≃ₗ[R] N) :
    MatrixPresentation R N e m where
  relMatrix := P.relMatrix
  proj := σ.toLinearMap ∘ₗ P.proj
  surjective_proj := σ.surjective.comp P.surjective_proj
  exact_mulVecLin_proj := fun y => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.map_eq_zero_iff]
    exact P.exact_mulVecLin_proj y

@[simp] lemma congr_relMatrix (P : MatrixPresentation R M e m)
    (σ : M ≃ₗ[R] N) : (P.congr σ).relMatrix = P.relMatrix := rfl

@[simp] lemma congr_entryIdeal (P : MatrixPresentation R M e m)
    (σ : M ≃ₗ[R] N) : (P.congr σ).entryIdeal = P.entryIdeal := rfl

/-- An `e`-generator presentation bounds the fiber rank at every prime by
`e`: the base-changed projection is a surjection `κ(p)^e ↠ κ(p) ⊗ M`. -/
theorem fiberRank_le (P : MatrixPresentation R M e m) (p : Ideal R)
    [p.IsPrime] : p.fiberRank M ≤ e := by
  have hsurj := (P.baseChange p.ResidueField).surjective_proj
  have h := LinearMap.finrank_le_finrank_of_surjective
    (f := (P.baseChange p.ResidueField).proj) hsurj
  simpa [Ideal.fiberRank] using h

end Congr

end Module.MatrixPresentation

namespace Ideal

section FiberRankCongr

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
variable {N : Type u} [AddCommGroup N] [Module R N]

/-- The fiber rank is invariant under linear equivalences. -/
lemma fiberRank_congr (p : Ideal R) [p.IsPrime] (σ : M ≃ₗ[R] N) :
    p.fiberRank M = p.fiberRank N :=
  LinearEquiv.finrank_eq (LinearEquiv.baseChange R p.ResidueField M N σ)

/-- Congruence of the fiber rank in the prime (avoids the dependent-motive
failure of `rw` through the `IsPrime` instance). -/
lemma fiberRank_congr_ideal {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (h : p = q) : p.fiberRank M = q.fiberRank M := by
  subst h; rfl

end FiberRankCongr

section FiberRankBaseChange

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- **Base-change invariance of the fiber rank**: for an `R`-algebra `A`
and a prime `q` of `A` lying over `p = q ∩ R`, the fiber of `A ⊗[R] M` at
`q` is the base change of the fiber of `M` at `p` along the residue-field
extension `κ(p) → κ(q)`; in particular the fiber dimensions agree.  No
flatness or finiteness hypotheses. -/
theorem fiberRank_baseChange (q : Ideal A) [q.IsPrime] :
    q.fiberRank (A ⊗[R] M) = (q.comap (algebraMap R A)).fiberRank M := by
  set p := q.comap (algebraMap R A) with hp
  -- the residue-field extension `κ(p) → κ(q)`; the `R`- and `A`-algebra
  -- structures on the residue fields are the canonical ones
  letI : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap R A) rfl).toAlgebra
  haveI : IsScalarTower R p.ResidueField q.ResidueField := by
    refine .of_algebraMap_eq fun r => ?_
    change algebraMap R q.ResidueField r =
      Ideal.ResidueField.map p q (algebraMap R A) rfl (algebraMap R p.ResidueField r)
    rw [Ideal.ResidueField.map_algebraMap,
      IsScalarTower.algebraMap_apply R A q.ResidueField]
  -- cancel the two base changes
  have e1 : q.Fiber (A ⊗[R] M) ≃ₗ[q.ResidueField]
      q.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R A q.ResidueField q.ResidueField M
  have e2 : q.ResidueField ⊗[R] M ≃ₗ[q.ResidueField]
      q.ResidueField ⊗[p.ResidueField] (p.Fiber M) :=
    (AlgebraTensorModule.cancelBaseChange R p.ResidueField q.ResidueField
      q.ResidueField M).symm
  rw [Ideal.fiberRank, LinearEquiv.finrank_eq (e1.trans e2),
    Module.finrank_baseChange, Ideal.fiberRank]

end FiberRankBaseChange

section FiberRankLocalized

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
variable {R' : Type u} [CommRing R'] [Algebra R R'] (S : Submonoid R)
variable [IsLocalization S R']
variable {N : Type u} [AddCommGroup N] [Module R N] [Module R' N]
variable [IsScalarTower R R' N]

/-- Localized modules have the same fiber ranks: for a localization
`R' = S⁻¹R`, a localized module `N = S⁻¹M` and a prime `q` of `R'`, the
fiber rank of `N` at `q` equals that of `M` at the contraction `q ∩ R`. -/
theorem fiberRank_of_isLocalizedModule (l : M →ₗ[R] N)
    [IsLocalizedModule S l] (q : Ideal R') [q.IsPrime] :
    q.fiberRank N = (q.comap (algebraMap R R')).fiberRank M := by
  have hbc := IsLocalizedModule.isBaseChange S R' l
  exact (Ideal.fiberRank_congr q hbc.equiv.symm).trans
    (Ideal.fiberRank_baseChange M q)

end FiberRankLocalized

end Ideal

/-! ## §2 The point ↔ prime dictionary on affine opens -/

namespace AlgebraicGeometry.IsAffineOpen

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

include hU in
/-- A point of an affine open lies in the zero locus of an ideal of
sections iff its prime contains the ideal. -/
lemma mem_zeroLocus_iff_le_primeIdealOf (I : Ideal Γ(X, U)) (x : U) :
    (x : X) ∈ X.zeroLocus (U := U) (I : Set Γ(X, U)) ↔
      I ≤ (hU.primeIdealOf x).asIdeal := by
  constructor
  · intro hx
    have h4 : (x : X) ∈ hU.fromSpec '' PrimeSpectrum.zeroLocus (I : Set Γ(X, U)) := by
      rw [hU.fromSpec_image_zeroLocus]
      exact ⟨hx, x.2⟩
    obtain ⟨y, hy, hyx⟩ := h4
    have hinj : Function.Injective hU.fromSpec :=
      hU.fromSpec.isOpenEmbedding.injective
    have hyeq : y = hU.primeIdealOf x :=
      hinj (by rw [hyx, hU.fromSpec_primeIdealOf x])
    subst hyeq
    exact fun s hs => (PrimeSpectrum.mem_zeroLocus _ _).mp hy hs
  · intro hle
    have h1 : hU.primeIdealOf x ∈ PrimeSpectrum.zeroLocus (I : Set Γ(X, U)) :=
      (PrimeSpectrum.mem_zeroLocus _ _).mpr fun s hs => hle hs
    have h2 : (x : X) ∈ hU.fromSpec '' PrimeSpectrum.zeroLocus (I : Set Γ(X, U)) :=
      ⟨_, h1, hU.fromSpec_primeIdealOf x⟩
    rw [hU.fromSpec_image_zeroLocus] at h2
    exact h2.1

include hU in
/-- A point of an affine open lies in a basic open iff the section avoids
its prime. -/
lemma mem_basicOpen_iff_notMem_primeIdealOf (f : Γ(X, U)) (x : U) :
    (x : X) ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf x).asIdeal := by
  have hpre : hU.primeIdealOf x ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f ↔
      f ∉ (hU.primeIdealOf x).asIdeal := by
    rw [hU.fromSpec_preimage_basicOpen]
    exact PrimeSpectrum.mem_basicOpen _ _
  refine Iff.trans ?_ hpre
  change _ ↔ hU.fromSpec (hU.primeIdealOf x) ∈ X.basicOpen f
  rw [hU.fromSpec_primeIdealOf x]

end AlgebraicGeometry.IsAffineOpen

/-! ## §3 Presentation charts and the point rank -/

namespace AlgebraicGeometry

open Module CategoryTheory

/-- The `appLE` of the identity morphism is the plain restriction map. -/
lemma Scheme.id_appLE {X : Scheme.{u}} {U V : X.Opens}
    (e : V ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) :
    (𝟙 X : X ⟶ X).appLE U V e =
      X.presheaf.map (homOfLE (show V ≤ U from e)).op := by
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  exact Category.id_comp _

namespace Scheme.Modules

variable {X : Scheme.{u}} (G : X.Modules)

/-- The canonical `Γ(X, U)`-module structure on the sections of `G` over a
basic open of `U` (restriction of scalars along the restriction map);
matches the canonical algebra instance
`Scheme.algebra_section_section_basicOpen`. -/
noncomputable local instance moduleSectionBasicOpen
    {U : X.Opens} (f : Γ(X, U)) :
    Module Γ(X, U) Γ(G, X.basicOpen f) :=
  Module.compHom _ (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom

local instance isScalarTowerSectionBasicOpen {U : X.Opens} (f : Γ(X, U)) :
    IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(G, X.basicOpen f) :=
  .of_algebraMap_smul fun _ _ => rfl

/-- An affine open `V` is an **`e`-presentation chart** for the module `G`
if the section module `Γ(G, V)` admits a matrix presentation with `e`
generators [Nitsure §4, `n = 0`: the local right-exact presentation
`𝒪_V^{⊕m} →ψ 𝒪_V^{⊕e} → F|_V → 0`]. -/
def IsPresentationChart (e : ℕ) (V : X.affineOpens) : Prop :=
  ∃ mm : ℕ, Nonempty (MatrixPresentation Γ(X, V.1) Γ(G, V.1) e mm)

variable [G.IsQuasicoherent]

/-- The section module of a quasi-coherent module over a basic open, as a
matrix presentation: an `e`-generator presentation over an affine open
localizes to an `e`-generator presentation over each basic open, with the
restricted relation matrix. -/
noncomputable def MatrixPresentationBasicOpen {e mm : ℕ} {V : X.affineOpens}
    (P : MatrixPresentation Γ(X, V.1) Γ(G, V.1) e mm) (f : Γ(X, V.1)) :
    MatrixPresentation Γ(X, X.basicOpen f) Γ(G, X.basicOpen f) e mm :=
  haveI := V.2.isLocalization_basicOpen f
  haveI := Scheme.Modules.isLocalizedModule_basicOpen G V.2 f
  (P.baseChange Γ(X, X.basicOpen f)).congr
    (IsLocalizedModule.isBaseChange (Submonoid.powers f) Γ(X, X.basicOpen f)
      (restrictBasicOpenₗ G f)).equiv

@[simp] lemma matrixPresentationBasicOpen_relMatrix {e mm : ℕ}
    {V : X.affineOpens} (P : MatrixPresentation Γ(X, V.1) Γ(G, V.1) e mm)
    (f : Γ(X, V.1)) :
    (MatrixPresentationBasicOpen G P f).relMatrix =
      P.relMatrix.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom :=
  rfl

/-- Presentation charts are stable under passing to basic opens. -/
theorem IsPresentationChart.basicOpen {e : ℕ} {V : X.affineOpens}
    (h : IsPresentationChart G e V) (f : Γ(X, V.1)) :
    IsPresentationChart G e (X.affineBasicOpen f) := by
  obtain ⟨mm, ⟨P⟩⟩ := h
  exact ⟨mm, ⟨MatrixPresentationBasicOpen G P f⟩⟩

/-- The dimension of the fiber of `G` at a point `x` of an affine open
chart `V`: the fiber rank of the section module `Γ(G, V)` at the prime of
`x` [Nitsure §4: `e = dim_{κ(s)} F(s)`]. -/
noncomputable def chartFiberRank {V : X.affineOpens} (x : X)
    (hx : x ∈ V.1) : ℕ :=
  ((V.2.primeIdealOf ⟨x, hx⟩).asIdeal).fiberRank Γ(G, V.1)

omit [SheafOfModules.IsQuasicoherent G] in
lemma chartFiberRank_congr_chart {V W : X.affineOpens} (h : V = W) (x : X)
    (hxV : x ∈ V.1) (hxW : x ∈ W.1) :
    chartFiberRank G x hxV = chartFiberRank G x hxW := by
  subst h; rfl

/-- The chart fiber rank is unchanged by passing to a basic open of the
chart. -/
theorem chartFiberRank_basicOpen {V : X.affineOpens} (f : Γ(X, V.1))
    (x : X) (hx : x ∈ X.basicOpen f) :
    chartFiberRank G (V := V) x (X.basicOpen_le f hx) =
      chartFiberRank G (V := X.affineBasicOpen f) x hx := by
  haveI := V.2.isLocalization_basicOpen f
  haveI := Scheme.Modules.isLocalizedModule_basicOpen G V.2 f
  have hloc := Ideal.fiberRank_of_isLocalizedModule (Submonoid.powers f)
    (restrictBasicOpenₗ G f)
    (((V.2.basicOpen f).primeIdealOf ⟨x, hx⟩).asIdeal)
  have hle : X.basicOpen f ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ V.1 := X.basicOpen_le f
  have h1 := IsAffineOpen.comap_primeIdealOf_appLE (f := (𝟙 X : X ⟶ X))
    V.1 V.2 (X.basicOpen f) (V.2.basicOpen f) hle hx
  rw [Scheme.id_appLE] at h1
  have hpt : V.2.primeIdealOf ⟨(𝟙 X : X ⟶ X) x, hle hx⟩ =
      V.2.primeIdealOf ⟨x, X.basicOpen_le f hx⟩ := by
    congr 1
  have hcomap :
      (((V.2.basicOpen f).primeIdealOf ⟨x, hx⟩).asIdeal).comap
          (algebraMap Γ(X, V.1) Γ(X, X.basicOpen f)) =
        (V.2.primeIdealOf ⟨x, X.basicOpen_le f hx⟩).asIdeal := by
    have h2 : algebraMap Γ(X, V.1) Γ(X, X.basicOpen f) =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom := rfl
    rw [h2, ← hpt]
    exact congrArg PrimeSpectrum.asIdeal h1
  calc chartFiberRank G (V := V) x (X.basicOpen_le f hx)
      = ((((V.2.basicOpen f).primeIdealOf ⟨x, hx⟩).asIdeal).comap
          (algebraMap Γ(X, V.1) Γ(X, X.basicOpen f))).fiberRank Γ(G, V.1) :=
        Ideal.fiberRank_congr_ideal hcomap.symm
    _ = (((V.2.basicOpen f).primeIdealOf ⟨x, hx⟩).asIdeal).fiberRank
          Γ(G, X.basicOpen f) := hloc.symm
    _ = chartFiberRank G (V := X.affineBasicOpen f) x hx := rfl

/-- **Chart-independence of the fiber rank**: two affine charts through the
same point give the same fiber rank.  Proof: refine to a common basic open
(`exists_basicOpen_le_affine_inter`) and localize both sides. -/
theorem chartFiberRank_eq {V W : X.affineOpens} (x : X)
    (hxV : x ∈ V.1) (hxW : x ∈ W.1) :
    chartFiberRank G x hxV = chartFiberRank G x hxW := by
  obtain ⟨f, g, hfg, hxf⟩ :=
    exists_basicOpen_le_affine_inter V.2 W.2 x ⟨hxV, hxW⟩
  have hxg : x ∈ X.basicOpen g := by rw [← hfg]; exact hxf
  have h1 := chartFiberRank_basicOpen G (V := V) f x hxf
  have h2 := chartFiberRank_basicOpen G (V := W) g x hxg
  have h3 : chartFiberRank G (V := X.affineBasicOpen f) x hxf =
      chartFiberRank G (V := X.affineBasicOpen g) x hxg :=
    chartFiberRank_congr_chart G (Subtype.ext hfg) x hxf hxg
  calc chartFiberRank G x hxV
      = chartFiberRank G (V := V) x (X.basicOpen_le f hxf) := rfl
    _ = chartFiberRank G (V := X.affineBasicOpen f) x hxf := h1
    _ = chartFiberRank G (V := X.affineBasicOpen g) x hxg := h3
    _ = chartFiberRank G (V := W) x (X.basicOpen_le g hxg) := h2.symm
    _ = chartFiberRank G x hxW := rfl

variable (X) in
/-- The **point rank** of a quasi-coherent module: the dimension of its
fiber at the point, computed through any affine chart
(`pointRank_eq_chartFiberRank`). -/
noncomputable def pointRank (x : X) : ℕ :=
  chartFiberRank G x (V := ⟨(exists_isAffineOpen_mem_and_subset
      (x := x) (U := ⊤) trivial).choose,
      (exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤)
        trivial).choose_spec.1⟩)
    (exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤)
      trivial).choose_spec.2.1

theorem pointRank_eq_chartFiberRank {V : X.affineOpens} (x : X)
    (hx : x ∈ V.1) : pointRank X G x = chartFiberRank G x hx :=
  chartFiberRank_eq G x _ hx

/-! ## §4 Locality and chart-independence of entry-ideal membership -/

omit [SheafOfModules.IsQuasicoherent G] in
/-- Restriction of sections is transitive (any parallel pair of `Opens`
homs agree, so the composite collapses). -/
lemma presheaf_res_res {A B C : X.Opens} (j : B ⟶ A) (i : C ⟶ B)
    (k : C ⟶ A) (x : Γ(X, A)) :
    X.presheaf.map i.op (X.presheaf.map j.op x) = X.presheaf.map k.op x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
    Subsingleton.elim (i ≫ j) k]

/-- Transport of a matrix presentation of the sections of `G` along an
equality of opens. -/
def transportOpens {U V : X.Opens} (h : U = V) {e mm : ℕ}
    (P : MatrixPresentation Γ(X, U) Γ(G, U) e mm) :
    MatrixPresentation Γ(X, V) Γ(G, V) e mm := h ▸ P

omit [SheafOfModules.IsQuasicoherent G] in
/-- The entry ideal of a transported presentation is the image of the
entry ideal under the `eqToHom` restriction. -/
lemma entryIdeal_transportOpens {U V : X.Opens} (h : U = V) {e mm : ℕ}
    (P : MatrixPresentation Γ(X, U) Γ(G, U) e mm) :
    (transportOpens G h P).entryIdeal =
      P.entryIdeal.map (X.presheaf.map (eqToHom h.symm).op).hom := by
  subst h
  simp only [transportOpens, eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  exact (Ideal.map_id _).symm

variable {e : ℕ}

/-- The entry ideal of the basic-open restriction of a presentation is the
image ideal of the entry ideal. -/
lemma entryIdeal_matrixPresentationBasicOpen {mm : ℕ} {V : X.affineOpens}
    (P : MatrixPresentation Γ(X, V.1) Γ(G, V.1) e mm) (f : Γ(X, V.1)) :
    (MatrixPresentationBasicOpen G P f).entryIdeal =
      P.entryIdeal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom := by
  haveI := V.2.isLocalization_basicOpen f
  haveI := Scheme.Modules.isLocalizedModule_basicOpen G V.2 f
  rw [MatrixPresentationBasicOpen, Module.MatrixPresentation.congr_entryIdeal,
    Module.MatrixPresentation.entryIdeal_baseChange]
  rfl

/-- **Locality of entry-ideal membership on a chart**: if every point of
the chart has a basic open on which the restriction of `r` lands in the
entry ideal of the restricted presentation, then `r` is in the entry
ideal. -/
theorem mem_entryIdeal_of_locally {mm : ℕ} {V : X.affineOpens}
    (P : MatrixPresentation Γ(X, V.1) Γ(G, V.1) e mm) (r : Γ(X, V.1))
    (H : ∀ x ∈ V.1, ∃ g : Γ(X, V.1), x ∈ X.basicOpen g ∧
      X.presheaf.map (homOfLE (X.basicOpen_le g)).op r ∈
        (MatrixPresentationBasicOpen G P g).entryIdeal) :
    r ∈ P.entryIdeal := by
  classical
  choose g hxg hgmem using H
  -- the chosen basic opens cover the chart, so the `g x` span the unit
  -- ideal
  have hspan : Ideal.span (Set.range fun x : V.1 => g x.1 x.2) = ⊤ := by
    rw [← V.2.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun r => X.basicOpen_le _) fun y hy => ?_
    refine TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨_, ⟨⟨y, hy⟩, rfl⟩⟩, hxg y hy⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem P.entryIdeal _ hspan r
    (fun ⟨_, x, rfl⟩ => ?_)
  -- membership after localization at `g x` gives a power `g x ^ n • r ∈ I`
  haveI := V.2.isLocalization_basicOpen (g x.1 x.2)
  have h1 := hgmem x.1 x.2
  rw [entryIdeal_matrixPresentationBasicOpen] at h1
  have h2 : algebraMap Γ(X, V.1) Γ(X, X.basicOpen (g x.1 x.2)) r ∈
      P.entryIdeal.map (algebraMap Γ(X, V.1) Γ(X, X.basicOpen (g x.1 x.2))) := h1
  obtain ⟨s, hs, hmem⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers (g x.1 x.2)) _ _ _).mp h2
  obtain ⟨n, rfl⟩ := hs
  exact ⟨n, by simpa [smul_eq_mul] using hmem⟩

omit [SheafOfModules.IsQuasicoherent G] in
/-- Restriction along `U ≤ U` is the identity. -/
lemma presheaf_map_self {U : X.Opens} (h : U ≤ U) (r : Γ(X, U)) :
    X.presheaf.map (homOfLE h).op r = r := by
  rw [Subsingleton.elim (homOfLE h) (𝟙 U), op_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- **Chart-to-chart transfer of the entry-ideal condition**: if the
restriction of `r : Γ(X, U)` to a presentation chart `W ≤ U` lies in the
entry ideal of `P_W`, then at every point of `W ⊓ V` for a second chart
`V ≤ U` there is a basic open of `V` on which the restriction of `r` lies
in the entry ideal of the restricted `P_V`.  Presentation-independence of
the entry ideal (`Module.MatrixPresentation.entryIdeal_eq`) at a common
basic open is the engine. -/
theorem exists_basicOpen_mem_entryIdeal_of_chart {U : X.Opens}
    (r : Γ(X, U)) {V W : X.affineOpens} (hVU : V.1 ≤ U) (hWU : W.1 ≤ U)
    {mmV mmW : ℕ}
    (PV : MatrixPresentation Γ(X, V.1) Γ(G, V.1) e mmV)
    (PW : MatrixPresentation Γ(X, W.1) Γ(G, W.1) e mmW)
    (hW : X.presheaf.map (homOfLE hWU).op r ∈ PW.entryIdeal)
    (x : X) (hxV : x ∈ V.1) (hxW : x ∈ W.1) :
    ∃ g : Γ(X, V.1), x ∈ X.basicOpen g ∧
      X.presheaf.map (homOfLE (X.basicOpen_le g)).op
          (X.presheaf.map (homOfLE hVU).op r) ∈
        (MatrixPresentationBasicOpen G PV g).entryIdeal := by
  obtain ⟨f, g, hfg, hxf⟩ :=
    exists_basicOpen_le_affine_inter W.2 V.2 x ⟨hxW, hxV⟩
  have hbofU : X.basicOpen f ≤ U := (X.basicOpen_le f).trans hWU
  have hbogU : X.basicOpen g ≤ U := (X.basicOpen_le g).trans hVU
  refine ⟨g, hfg ▸ hxf, ?_⟩
  -- rewrite the doubly-restricted section as an `eqToHom`-transport of the
  -- `W`-side restriction
  have hz : X.presheaf.map (homOfLE (X.basicOpen_le g)).op
      (X.presheaf.map (homOfLE hVU).op r) =
      X.presheaf.map (eqToHom hfg.symm).op
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op
          (X.presheaf.map (homOfLE hWU).op r)) := by
    rw [presheaf_res_res (homOfLE hVU)
      (homOfLE (X.basicOpen_le g)) (homOfLE hbogU),
      presheaf_res_res (homOfLE hWU)
      (homOfLE (X.basicOpen_le f)) (homOfLE hbofU),
      presheaf_res_res (homOfLE hbofU)
      (eqToHom hfg.symm) (homOfLE hbogU)]
  rw [hz,
    ← Module.MatrixPresentation.entryIdeal_eq
      (transportOpens G hfg (MatrixPresentationBasicOpen G PW f))
      (MatrixPresentationBasicOpen G PV g),
    entryIdeal_transportOpens]
  refine Ideal.mem_map_of_mem _ ?_
  rw [entryIdeal_matrixPresentationBasicOpen]
  exact Ideal.mem_map_of_mem _ hW

/-! ## §5 The strata ideal -/

variable (e) in
/-- The rank-`e` **strata ideal** at an affine open `U`: the intersection,
over all `e`-generator presentation charts `V ≤ U`, of the preimages of the
entry ideals under restriction [Nitsure §4, `n = 0`: the ideal sheaf of the
canonical scheme structure on the rank-`e` locus]. -/
noncomputable def strataIdeal (U : X.affineOpens) : Ideal Γ(X, U.1) :=
  ⨅ (V : X.affineOpens) (h : V.1 ≤ U.1) (mm : ℕ)
    (P : MatrixPresentation Γ(X, V.1) Γ(G, V.1) e mm),
    P.entryIdeal.comap (X.presheaf.map (homOfLE h).op).hom

omit [SheafOfModules.IsQuasicoherent G] in
lemma mem_strataIdeal_iff {U : X.affineOpens} {r : Γ(X, U.1)} :
    r ∈ strataIdeal G e U ↔ ∀ (V : X.affineOpens) (h : V.1 ≤ U.1) (mm : ℕ)
      (P : MatrixPresentation Γ(X, V.1) Γ(G, V.1) e mm),
      X.presheaf.map (homOfLE h).op r ∈ P.entryIdeal := by
  simp only [strataIdeal, Submodule.mem_iInf, Ideal.mem_comap]

/-- **Evaluation of the strata ideal on a presentation chart**: on an
`e`-presentation chart the strata ideal is the entry ideal of any (hence
every) `e`-generator presentation. -/
theorem strataIdeal_eq_entryIdeal {V : X.affineOpens} {mm : ℕ}
    (P : MatrixPresentation Γ(X, V.1) Γ(G, V.1) e mm) :
    strataIdeal G e V = P.entryIdeal := by
  refine le_antisymm ?_ ?_
  · intro r hr
    have h := (mem_strataIdeal_iff G).mp hr V le_rfl mm P
    rwa [presheaf_map_self] at h
  · intro r hr
    rw [mem_strataIdeal_iff]
    intro W hWV mmW Q
    refine mem_entryIdeal_of_locally G Q _ (fun x hx => ?_)
    exact exists_basicOpen_mem_entryIdeal_of_chart G r hWV le_rfl Q P
      (by rwa [presheaf_map_self]) x hx (hWV hx)

/-- Membership in the strata ideal follows from membership at a family of
charts covering `U`. -/
theorem mem_strataIdeal_of_charts {U : X.affineOpens} (r : Γ(X, U.1))
    {ι : Type*} (Vc : ι → X.affineOpens) (hVcU : ∀ i, (Vc i).1 ≤ U.1)
    (mmc : ι → ℕ)
    (Pc : ∀ i, MatrixPresentation Γ(X, (Vc i).1) Γ(G, (Vc i).1) e (mmc i))
    (hmem : ∀ i, X.presheaf.map (homOfLE (hVcU i)).op r ∈ (Pc i).entryIdeal)
    (hcov : ∀ x ∈ U.1, ∃ i, x ∈ (Vc i).1) :
    r ∈ strataIdeal G e U := by
  rw [mem_strataIdeal_iff]
  intro W hWU mmW Q
  refine mem_entryIdeal_of_locally G Q _ (fun x hx => ?_)
  obtain ⟨i, hxi⟩ := hcov x (hWU hx)
  exact exists_basicOpen_mem_entryIdeal_of_chart G r hWU (hVcU i) Q (Pc i)
    (hmem i) x hx hxi

variable (e) in
/-- The standing hypothesis of the strata construction: every point of `X`
lies in an `e`-presentation chart.  Holds on the union of all
`e`-presentation charts, the ambient space of the rank-`e` stratum. -/
def ChartsCover : Prop :=
  ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 ∧ IsPresentationChart G e V

/-- Under `ChartsCover`, every affine open of `X` is covered by finitely
many `e`-presentation charts contained in it. -/
theorem ChartsCover.exists_finite_charts (hcov : ChartsCover G e)
    (U : X.affineOpens) :
    ∃ (n : ℕ) (Vc : Fin n → X.affineOpens) (mmc : Fin n → ℕ)
      (_Pc : ∀ i, MatrixPresentation Γ(X, (Vc i).1) Γ(G, (Vc i).1) e (mmc i)),
      (∀ i, (Vc i).1 ≤ U.1) ∧ ∀ x ∈ U.1, ∃ i, x ∈ (Vc i).1 := by
  classical
  -- the subtype of presentation charts contained in `U`
  set J := {V : X.affineOpens // V.1 ≤ U.1 ∧ IsPresentationChart G e V}
  -- they cover `U`: shrink a global chart through a simultaneous basic open
  have hJcov : (U.1 : Set X) ⊆ ⋃ j : J, ((j.1.1 : TopologicalSpace.Opens X) : Set X) := by
    intro x hx
    obtain ⟨V, hxV, hVchart⟩ := hcov x
    obtain ⟨f, g, hfg, hxf⟩ :=
      exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hx, hxV⟩
    have hle : (X.affineBasicOpen g).1 ≤ U.1 := by
      change X.basicOpen g ≤ U.1
      rw [← hfg]; exact X.basicOpen_le f
    refine Set.mem_iUnion.mpr
      ⟨⟨X.affineBasicOpen g, hle, hVchart.basicOpen G g⟩, ?_⟩
    change x ∈ X.basicOpen g
    rw [← hfg]; exact hxf
  -- extract a finite subcover by quasi-compactness of the affine open
  obtain ⟨T, hT⟩ := U.2.isCompact.elim_finite_subcover
    (fun j : J => ((j.1.1 : TopologicalSpace.Opens X) : Set X))
    (fun j => j.1.1.2) hJcov
  -- enumerate and choose presentations
  obtain ⟨n, eT⟩ : ∃ n, Nonempty (T ≃ Fin n) := ⟨T.card, ⟨T.equivFin⟩⟩
  obtain ⟨eT⟩ := eT
  choose mmc Pc using fun j : T => (j.1.2.2 : IsPresentationChart G e j.1.1)
  refine ⟨n, fun i => (eT.symm i).1.1, fun i => mmc (eT.symm i),
    fun i => (Pc (eT.symm i)).some, fun i => (eT.symm i).1.2.1,
    fun x hx => ?_⟩
  obtain ⟨j, hjT, hxj⟩ := Set.mem_iUnion₂.mp (hT hx)
  exact ⟨eT ⟨j, hjT⟩, by simpa using hxj⟩

/-- Restriction to the relative basic open computes the localization
fraction: restricting `mk' y (f₀ ^ n)` from `X.basicOpen f₀` to the basic
open of `f₀|_V` inside a smaller affine `V` gives
`mk' (y|_V) ((f₀|_V) ^ n)`. -/
theorem res_mk'_basicOpen {U : X.affineOpens} (f₀ : Γ(X, U.1))
    {V : X.affineOpens} (hVU : V.1 ≤ U.1) (y : Γ(X, U.1)) (n : ℕ)
    (h₁ : X.basicOpen (X.presheaf.map (homOfLE hVU).op f₀) ≤ X.basicOpen f₀) :
    haveI := U.2.isLocalization_basicOpen f₀
    haveI := V.2.isLocalization_basicOpen (X.presheaf.map (homOfLE hVU).op f₀)
    X.presheaf.map (homOfLE h₁).op
        (IsLocalization.mk' Γ(X, X.basicOpen f₀) y
          (⟨f₀ ^ n, pow_mem (Submonoid.mem_powers f₀) n⟩ :
            Submonoid.powers f₀)) =
      IsLocalization.mk' Γ(X, X.basicOpen (X.presheaf.map (homOfLE hVU).op f₀))
        (X.presheaf.map (homOfLE hVU).op y)
        (⟨(X.presheaf.map (homOfLE hVU).op f₀) ^ n,
          pow_mem (Submonoid.mem_powers _) n⟩ :
          Submonoid.powers (X.presheaf.map (homOfLE hVU).op f₀)) := by
  haveI := U.2.isLocalization_basicOpen f₀
  haveI := V.2.isLocalization_basicOpen (X.presheaf.map (homOfLE hVU).op f₀)
  set fv := X.presheaf.map (homOfLE hVU).op f₀ with hfv
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul]
  -- both sides are restrictions from `Γ(X, X.basicOpen f₀)`
  have hbase : (algebraMap Γ(X, V.1) Γ(X, X.basicOpen fv)) =
      (X.presheaf.map (homOfLE (X.basicOpen_le fv)).op).hom := rfl
  have hcalc : ∀ z : Γ(X, U.1),
      algebraMap Γ(X, V.1) Γ(X, X.basicOpen fv)
          (X.presheaf.map (homOfLE hVU).op z) =
        X.presheaf.map (homOfLE h₁).op
          (X.presheaf.map (homOfLE (X.basicOpen_le f₀)).op z) := by
    intro z
    rw [hbase]
    change X.presheaf.map (homOfLE (X.basicOpen_le fv)).op
        (X.presheaf.map (homOfLE hVU).op z) = _
    rw [presheaf_res_res (homOfLE hVU) (homOfLE (X.basicOpen_le fv))
        (homOfLE ((X.basicOpen_le fv).trans hVU)),
      presheaf_res_res (homOfLE (X.basicOpen_le f₀)) (homOfLE h₁)
        (homOfLE ((X.basicOpen_le fv).trans hVU))]
  rw [hcalc y]
  have hmul : (algebraMap Γ(X, V.1) Γ(X, X.basicOpen fv)) ↑(⟨fv ^ n,
      pow_mem (Submonoid.mem_powers _) n⟩ : Submonoid.powers fv) =
      X.presheaf.map (homOfLE h₁).op
        (X.presheaf.map (homOfLE (X.basicOpen_le f₀)).op (f₀ ^ n)) := by
    change algebraMap Γ(X, V.1) Γ(X, X.basicOpen fv) (fv ^ n) = _
    rw [map_pow, hcalc f₀, ← map_pow, ← map_pow]
  rw [hmul, ← map_mul]
  congr 1
  -- `mk' y (f₀^n) * (f₀^n)|_{D₀} = y|_{D₀}` is the defining property
  have hspec := IsLocalization.mk'_spec Γ(X, X.basicOpen f₀) y
    (⟨f₀ ^ n, pow_mem (Submonoid.mem_powers f₀) n⟩ : Submonoid.powers f₀)
  calc X.presheaf.map (homOfLE (X.basicOpen_le f₀)).op y
      = IsLocalization.mk' Γ(X, X.basicOpen f₀) y
          (⟨f₀ ^ n, pow_mem (Submonoid.mem_powers f₀) n⟩ :
            Submonoid.powers f₀) *
        algebraMap Γ(X, U.1) Γ(X, X.basicOpen f₀) (f₀ ^ n) := hspec.symm
    _ = _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The strata ideal localizes along basic opens** (quasi-coherence of
the strata ideal; the `map_ideal_basicOpen` field of the ideal-sheaf
datum).  [Nitsure §4, `n = 0`: the local strata glue by their universal
property.] -/
theorem map_strataIdeal_basicOpen (hcov : ChartsCover G e)
    (U : X.affineOpens) (f₀ : Γ(X, U.1)) :
    (strataIdeal G e U).map
        (X.presheaf.map (homOfLE (X.basicOpen_le f₀)).op).hom =
      strataIdeal G e (X.affineBasicOpen f₀) := by
  haveI := U.2.isLocalization_basicOpen f₀
  refine le_antisymm ?_ ?_
  · -- restriction preserves the chart conditions
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    refine (mem_strataIdeal_iff G).mpr (fun W hWD mmW Q => ?_)
    have hWU : W.1 ≤ U.1 := hWD.trans (X.basicOpen_le f₀)
    have h := (mem_strataIdeal_iff G).mp hr W hWU mmW Q
    have heq := presheaf_res_res (X := X) (homOfLE (X.basicOpen_le f₀))
      (homOfLE hWD) (homOfLE hWU) r
    change X.presheaf.map (homOfLE hWD).op
      (X.presheaf.map (homOfLE (X.basicOpen_le f₀)).op r) ∈ Q.entryIdeal
    exact heq.symm ▸ h
  · -- a section satisfying the conditions over the basic open comes from
    -- the strata ideal after clearing a power of `f₀`
    intro r' hr'
    obtain ⟨⟨y, s⟩, hys⟩ := IsLocalization.mk'_surjective
      (M := Submonoid.powers f₀) (S := Γ(X, X.basicOpen f₀)) r'
    dsimp only at hys
    obtain ⟨n, hn⟩ := s.2
    have hs : s = ⟨f₀ ^ n, pow_mem (Submonoid.mem_powers f₀) n⟩ :=
      Subtype.ext hn.symm
    rw [hs] at hys
    -- finitely many charts covering `U`
    obtain ⟨N, Vc, mmc, Pc, hVcU, hcovU⟩ :=
      ChartsCover.exists_finite_charts G hcov U
    -- per chart, a power of `f₀` clears the denominator
    have hper : ∀ i : Fin N, ∃ m : ℕ,
        X.presheaf.map (homOfLE (hVcU i)).op (f₀ ^ m * y) ∈
          (Pc i).entryIdeal := by
      intro i
      haveI := (Vc i).2.isLocalization_basicOpen
        (X.presheaf.map (homOfLE (hVcU i)).op f₀)
      have h₁ : X.basicOpen (X.presheaf.map (homOfLE (hVcU i)).op f₀) ≤
          X.basicOpen f₀ := by
        rw [Scheme.basicOpen_res]
        exact inf_le_right
      -- the strata condition at the chart `D(f₀|_V) ≤ D(f₀)`
      have hi := (mem_strataIdeal_iff G).mp hr'
        (X.affineBasicOpen (X.presheaf.map (homOfLE (hVcU i)).op f₀)) h₁
        (mmc i) (MatrixPresentationBasicOpen G (Pc i)
          (X.presheaf.map (homOfLE (hVcU i)).op f₀))
      rw [← hys] at hi
      have hres := res_mk'_basicOpen f₀ (hVcU i) y n h₁
      have hi' := (congrArg (fun z =>
        z ∈ (MatrixPresentationBasicOpen G (Pc i)
          (X.presheaf.map (homOfLE (hVcU i)).op f₀)).entryIdeal) hres).mp hi
      have hE := entryIdeal_matrixPresentationBasicOpen G (Pc i)
        (X.presheaf.map (homOfLE (hVcU i)).op f₀)
      have hi'' := (congrArg (fun I => IsLocalization.mk'
        Γ(X, X.basicOpen (X.presheaf.map (homOfLE (hVcU i)).op f₀))
        (X.presheaf.map (homOfLE (hVcU i)).op y)
        (⟨(X.presheaf.map (homOfLE (hVcU i)).op f₀) ^ n,
          pow_mem (Submonoid.mem_powers _) n⟩ :
          Submonoid.powers (X.presheaf.map (homOfLE (hVcU i)).op f₀)) ∈ I)
        hE).mp hi'
      obtain ⟨t, ht, hmem⟩ :=
        (IsLocalization.mk'_mem_map_algebraMap_iff
          (Submonoid.powers (X.presheaf.map (homOfLE (hVcU i)).op f₀))
          _ _ _ _).mp hi''
      obtain ⟨m, rfl⟩ := ht
      refine ⟨m, ?_⟩
      rw [map_mul, map_pow]
      exact hmem
    choose mc hmc using hper
    set m := Finset.univ.sup mc with hm
    have hmem : ∀ i : Fin N,
        X.presheaf.map (homOfLE (hVcU i)).op (f₀ ^ m * y) ∈
          (Pc i).entryIdeal := by
      intro i
      have hle : mc i ≤ m := Finset.le_sup (Finset.mem_univ i)
      have hsplit : f₀ ^ m * y = f₀ ^ (m - mc i) * (f₀ ^ mc i * y) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      rw [hsplit, map_mul]
      exact Ideal.mul_mem_left _ _ (hmc i)
    have hfin : f₀ ^ m * y ∈ strataIdeal G e U :=
      mem_strataIdeal_of_charts G _ Vc hVcU mmc Pc hmem hcovU
    have := (IsLocalization.mk'_mem_map_algebraMap_iff (Submonoid.powers f₀)
      Γ(X, X.basicOpen f₀) (strataIdeal G e U) y
      (⟨f₀ ^ n, pow_mem (Submonoid.mem_powers f₀) n⟩ :
        Submonoid.powers f₀)).mpr
      ⟨f₀ ^ m, pow_mem (Submonoid.mem_powers f₀) m, hfin⟩
    rw [hys] at this
    exact this

/-! ## §6 The rank stratum as a closed subscheme -/

variable (e) in
/-- The rank-`e` **strata ideal sheaf datum** [Nitsure §4, `n = 0`: the
canonical scheme structure on the rank-`e` stratum]. -/
noncomputable def strataData (hcov : ChartsCover G e) : X.IdealSheafData where
  ideal := strataIdeal G e
  map_ideal_basicOpen U f₀ := map_strataIdeal_basicOpen G hcov U f₀

@[simp] lemma strataData_ideal (hcov : ChartsCover G e) (U : X.affineOpens) :
    (strataData G e hcov).ideal U = strataIdeal G e U := rfl

variable (e) in
/-- The **rank-`e` stratum** of a quasi-coherent module `G`: the closed
subscheme of `X` cut out by the entry ideals of local `e`-generator
presentations. -/
noncomputable def stratum (hcov : ChartsCover G e) : Scheme.{u} :=
  (strataData G e hcov).subscheme

variable (e) in
/-- The closed immersion of the rank-`e` stratum. -/
noncomputable def stratumι (hcov : ChartsCover G e) :
    stratum G e hcov ⟶ X :=
  (strataData G e hcov).subschemeι

instance (hcov : ChartsCover G e) :
    IsClosedImmersion (stratumι G e hcov) :=
  inferInstanceAs (IsClosedImmersion (strataData G e hcov).subschemeι)

/-- **The support of the rank-`e` stratum is the rank-`e` locus**: a point
lies in the image of the stratum iff the fiber of `G` there has dimension
exactly `e` [Nitsure §4, part (i), `n = 0` case]. -/
theorem mem_range_stratumι_iff (hcov : ChartsCover G e) (x : X) :
    x ∈ Set.range (stratumι G e hcov) ↔ pointRank X G x = e := by
  obtain ⟨V, hxV, hchart⟩ := hcov x
  obtain ⟨mm, ⟨P⟩⟩ := hchart
  have h0 : x ∈ Set.range (stratumι G e hcov) ↔
      x ∈ (strataData G e hcov).support := by
    change x ∈ Set.range ((strataData G e hcov).subschemeι) ↔ _
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Iff.rfl
  have h1 : x ∈ (strataData G e hcov).support ↔
      x ∈ X.zeroLocus (U := V.1)
        (((strataData G e hcov).ideal V : Ideal Γ(X, V.1)) :
          Set Γ(X, V.1)) :=
    Scheme.IdealSheafData.mem_support_iff_of_mem hxV
  have hIP : ((strataData G e hcov).ideal V : Ideal Γ(X, V.1)) =
      P.entryIdeal := strataIdeal_eq_entryIdeal G P
  have h2 : x ∈ X.zeroLocus (U := V.1)
      (((strataData G e hcov).ideal V : Ideal Γ(X, V.1)) : Set Γ(X, V.1)) ↔
      P.entryIdeal ≤ (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    rw [hIP]
    exact V.2.mem_zeroLocus_iff_le_primeIdealOf P.entryIdeal ⟨x, hxV⟩
  have h3 : P.entryIdeal ≤ (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal ↔
      pointRank X G x = e := by
    rw [P.entryIdeal_le_prime_iff, pointRank_eq_chartFiberRank G x hxV]
    exact Iff.rfl
  exact ((h0.trans h1).trans h2).trans h3

end Scheme.Modules

end AlgebraicGeometry
