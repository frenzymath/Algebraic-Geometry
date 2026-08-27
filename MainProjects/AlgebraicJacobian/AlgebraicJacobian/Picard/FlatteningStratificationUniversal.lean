/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.EntryIdealStratum
import AlgebraicJacobian.Picard.GenericFlatnessGeometric

/-!
# Universal property of the flat-locus stratification (Nitsure §4, `n = 0`)

This file proves the *representability* layer of the flat-locus
stratification and assembles it into the universal theorem
`AlgebraicGeometry.flatLocusStratification_universal` (sorry-free): a
morphism `q : T ⟶ X` whose pulled-back module is flat of constant fiber
rank `e` factors uniquely through the rank-`e` stratum
`stratumι : stratum G e hcov ⟶ X` of
`AlgebraicJacobian.Picard.EntryIdealStratum`, the stratum itself carries a
flat pullback, and over a noetherian base the finitely many rank strata
form the universal flattening stratification — parts (i)+(ii) of the
special case `n = 0` of the flattening-stratification theorem in
[Nitsure §4].

## Contents

* §1 — bridges: matrix presentations of pullback section modules
  (`exists_matrixPresentation_pullback_sections`, via the Lane F section
  formula `pullback_app_isoTensor_baseMap_sectionLinearEquiv`), transport of
  flatness between the natural and the `appLE`-restriction module structures
  (`flat_compHom_congr`), and extraction of section flatness from
  `CoherentSheafFlat (𝟙 T)` (`flat_sections_of_coherentSheafFlat_id`,
  `coherentSheafFlat_id_of_charts`).
* §2 — the rank dictionary: `rankAtStalk` of an affine section module
  computes the `pointRank` (`rankAtStalk_sections_eq_pointRank`), and the
  point rank of a pullback module is the point rank at the image point
  (`pointRank_pullback`; no flatness hypotheses, via
  `Ideal.fiberRank_baseChange`).
* §3 — Stage D1: the kernel bound `strataData_le_ker` (a flat
  constant-rank-`e` pullback kills the strata ideal) and the unique
  factorization `existsUnique_stratumLift` through the closed immersion
  `stratumι` (`IsClosedImmersion.lift`).
* §4 — Stage D2: the stratum pullback is flat over the stratum
  (`coherentSheafFlat_stratum`): on chart preimages the section module is
  presented with vanishing relation matrix, hence free.
* §5 — chart supply on a locally noetherian base
  (`exists_presentationChart_mem`, via the Nakayama prolongation) and the
  chart locus `chartLocus` with its rank bounds.
* §6 — the rank stratum `rankStratum`/`rankStratumι` over the chart locus:
  a locally closed immersion with support exactly the rank-`e` locus
  (`mem_range_rankStratumι_iff`) and flat pullback
  (`coherentSheafFlat_rankStratum`); flatness is stable under arbitrary
  pullback (`coherentSheafFlat_id_pullback`).
* §7 — the rank bound on a noetherian base (`exists_pointRank_le`) and
  openness of the rank fibers of a flat pullback
  (`isOpen_pointRank_pullback_eq`).
* §8 — unique factorization of a constant-rank flat morphism through the
  rank stratum (`existsUnique_factor_rankStratum`).
* §9 — the universal theorem `flatLocusStratification_universal`.

Blueprint chapter: `Picard_FlatteningStratification.tex`,
§`sec:flatstrat_universal`.
Source: [Nitsure], §4, proof of the flattening-stratification theorem,
special case `n = 0` (`references/nitsure-hilbert-quot-src/`
`nitsure-hilbert-quot.tex`, L1849–L1885).
-/

universe u

open TensorProduct CategoryTheory

namespace AlgebraicGeometry

open Module

namespace Scheme.Modules

/-! ## §1 Presentations of pullback sections and flatness bridges -/

section PullbackPresentation

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (G : X.Modules) [G.IsQuasicoherent]

/-- Elementwise fibre-side `appLE` coherence: restricting the image of
`appLE` equals `appLE` into the smaller open. -/
private lemma appLE_res_apply' {W W' : Y.Opens} {V : X.Opens}
    (e : W ≤ g ⁻¹ᵁ V) (h : W' ≤ W) (u : Γ(X, V)) :
    (Y.presheaf.map (homOfLE h).op).hom ((g.appLE V W e).hom u) =
      (g.appLE V W' (h.trans e)).hom u := by
  have h1 := congrArg (fun (φ : Γ(X, V) ⟶ Γ(Y, W')) => φ.hom u)
    (Scheme.Hom.appLE_map (f := g) e (homOfLE h).op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h1

/-- Elementwise base-side `appLE` coherence: `appLE` of a restricted base
section equals `appLE` from the larger base open. -/
private lemma appLE_base_res_apply' {V' V : X.Opens} {W : Y.Opens}
    (h : V' ≤ V) (e' : W ≤ g ⁻¹ᵁ V') (e : W ≤ g ⁻¹ᵁ V) (u : Γ(X, V)) :
    (g.appLE V' W e').hom ((X.presheaf.map (homOfLE h).op).hom u) =
      (g.appLE V W e).hom u := by
  have h1 := congrArg (fun (φ : Γ(X, V) ⟶ Γ(Y, W)) => φ.hom u)
    (Scheme.Hom.map_appLE (f := g) e' (homOfLE h).op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h1

/-- **Matrix presentations pull back to section modules** (the geometric
base-change of a local presentation, [Nitsure §4]: "the pulled-back
sequence is exact by right-exactness of tensor products").  For a morphism
`g : Y ⟶ X`, an affine `V ⊆ X`, an affine `W ⊆ g⁻¹V` and an `ee`-generator
presentation `P` of `Γ(G, V)`, the section module `Γ(g^*G, W)` admits an
`ee`-generator presentation whose relation matrix is the image of that of
`P` under `g.appLE`. -/
theorem exists_matrixPresentation_pullback_sections
    {V : X.Opens} (hV : IsAffineOpen V) {W : Y.Opens} (hW : IsAffineOpen W)
    (e : W ≤ g ⁻¹ᵁ V) {ee mm : ℕ}
    (P : MatrixPresentation Γ(X, V) Γ(G, V) ee mm) :
    ∃ P' : MatrixPresentation Γ(Y, W)
      Γ((Scheme.Modules.pullback g).obj G, W) ee mm,
      P'.relMatrix = P.relMatrix.map (g.appLE V W e).hom := by
  letI : Algebra Γ(X, V) Γ(Y, W) := (g.appLE V W e).hom.toAlgebra
  letI : Module Γ(X, V) Γ((Scheme.Modules.pullback g).obj G, W) :=
    Module.compHom _ (g.appLE V W e).hom
  obtain ⟨⟨eqv, -⟩⟩ :=
    pullback_app_isoTensor_baseMap_sectionLinearEquiv g G hW hV e
  refine ⟨(P.baseChange Γ(Y, W)).congr eqv, ?_⟩
  rw [Module.MatrixPresentation.congr_relMatrix,
    Module.MatrixPresentation.baseChange_relMatrix,
    RingHom.algebraMap_toAlgebra]

end PullbackPresentation

section FlatBridge

/-- Transport of `Module.Flat` between the canonical module structure and a
`Module.compHom` structure along a pointwise-identity ring endomorphism
(the `appLE` of the identity morphism is the identity restriction, but not
definitionally the identity ring hom). -/
private lemma flat_compHom_congr {R : Type u} [CommRing R] {M : Type u}
    [AddCommGroup M] [Module R M] (f : R →+* R) (hf : ∀ r, f r = r) :
    (letI : Module R M := Module.compHom M f
     Module.Flat R M) ↔ Module.Flat R M := by
  have h : (Module.compHom M f : Module R M) = ‹Module R M› :=
    Module.ext' _ _ fun r m => by
      change f r • m = r • m
      rw [hf r]
  exact (congrArg (fun i : Module R M => @Module.Flat R M _ _ i) h).to_iff

variable {T : Scheme.{u}}

/-- The `appLE` of the identity morphism at equal opens is pointwise the
identity. -/
private lemma id_appLE_apply {W : T.Opens}
    (e : W ≤ (𝟙 T : T ⟶ T) ⁻¹ᵁ W) (r : Γ(T, W)) :
    ((𝟙 T : T ⟶ T).appLE W W e).hom r = r := by
  rw [Scheme.id_appLE]
  exact presheaf_map_self (X := T) e r

/-- **Extraction of section flatness from flatness over the identity**: if
`G` is flat over `T` via `𝟙 T` (the encoding of "the coherent sheaf `G` is
flat" in `Scheme.CoherentSheafFlat`), then the sections over every affine
open form a flat module over the section ring. -/
theorem flat_sections_of_coherentSheafFlat_id {G : T.Modules}
    (h : Scheme.CoherentSheafFlat (𝟙 T) G) {W : T.Opens}
    (hW : IsAffineOpen W) : Module.Flat Γ(T, W) Γ(G, W) :=
  (flat_compHom_congr ((𝟙 T : T ⟶ T).appLE W W (le_refl W)).hom
    (id_appLE_apply _)).mp (h hW hW (le_refl W))

/-- **Flatness over the identity from an affine cover of flat sections**:
if the sections of `G` over each member of an affine open cover of `T` are
flat over the respective section rings, then `G` is flat over `T` via
`𝟙 T`. -/
theorem coherentSheafFlat_id_of_charts (G : T.Modules) [G.IsQuasicoherent]
    {ι : Type u} (Wc : ι → T.Opens) (hWc : ∀ j, IsAffineOpen (Wc j))
    (hcover : ∀ y : T, ∃ j, y ∈ Wc j)
    (hflat : ∀ j, Module.Flat Γ(T, Wc j) Γ(G, Wc j)) :
    Scheme.CoherentSheafFlat (𝟙 T) G := by
  intro U hU V hV eV
  exact flat_section_of_affine_cover (𝟙 T) G Wc hWc Wc hWc
    (fun j => le_refl _) hcover
    (fun j => (flat_compHom_congr
      ((𝟙 T : T ⟶ T).appLE (Wc j) (Wc j) (le_refl _)).hom
      (id_appLE_apply _)).mpr (hflat j)) hU hV eV

end FlatBridge

/-! ## §2 The rank dictionary -/

section RankDictionary

variable {T : Scheme.{u}} (G : T.Modules) [G.IsQuasicoherent]

/-- A prime of the section ring of an affine open is the prime ideal of
the corresponding point. -/
private lemma primeIdealOf_fromSpec {W : T.Opens} (hW : IsAffineOpen W)
    (p : PrimeSpectrum Γ(T, W)) (hmem : (hW.fromSpec p : T) ∈ W) :
    hW.primeIdealOf ⟨hW.fromSpec p, hmem⟩ = p := by
  have hinj : Function.Injective hW.fromSpec :=
    hW.fromSpec.isOpenEmbedding.injective
  exact hinj (by rw [hW.fromSpec_primeIdealOf])

/-- **The stalk rank of an affine section module computes the point rank**:
for a quasi-coherent `G` with flat, finite sections `Γ(G, W)` over an
affine `W`, the rank of `Γ(G, W)` at a prime `p` is the point rank of `G`
at the corresponding point `fromSpec p` [Nitsure §4: flatness plus finite
presentation make the fibre dimension compute the local rank]. -/
theorem rankAtStalk_sections_eq_pointRank {W : T.Opens}
    (hW : IsAffineOpen W) [Module.Flat Γ(T, W) Γ(G, W)]
    [Module.Finite Γ(T, W) Γ(G, W)] (p : PrimeSpectrum Γ(T, W)) :
    Module.rankAtStalk Γ(G, W) p = pointRank T G (hW.fromSpec p) := by
  have hmem : (hW.fromSpec p : T) ∈ W := by
    have h0 : (hW.fromSpec p : T) ∈ Set.range hW.fromSpec :=
      Set.mem_range_self p
    rwa [hW.range_fromSpec] at h0
  rw [Module.rankAtStalk_eq,
    pointRank_eq_chartFiberRank G (V := ⟨W, hW⟩) _ hmem]
  change p.asIdeal.fiberRank Γ(G, W) = chartFiberRank G _ hmem
  rw [chartFiberRank]
  exact Ideal.fiberRank_congr_ideal
    (congrArg PrimeSpectrum.asIdeal (primeIdealOf_fromSpec hW p hmem)).symm

end RankDictionary

section PointRankPullback

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (G : X.Modules) [G.IsQuasicoherent]

/-- **The point rank of a pullback module is the point rank at the image
point** (no flatness or finiteness hypotheses; the geometric form of
`Ideal.fiberRank_baseChange`): for any morphism `g : Y ⟶ X` and
quasi-coherent `G` on `X`,
`pointRank (g^*G) y = pointRank G (g y)`. -/
theorem pointRank_pullback (y : Y) :
    haveI := pullback_isQuasicoherent_hom g G ‹_›
    pointRank Y ((Scheme.Modules.pullback g).obj G) y = pointRank X G (g y) := by
  haveI := pullback_isQuasicoherent_hom g G ‹_›
  -- affine charts around the image point and the point
  obtain ⟨V, hV, hgyV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := g y) (U := ⊤) trivial
  have hyV : y ∈ g ⁻¹ᵁ V := hgyV
  obtain ⟨W, hW, hyW, hWle⟩ :=
    exists_isAffineOpen_mem_and_subset (x := y) (U := g ⁻¹ᵁ V) hyV
  -- both sides through the two charts
  rw [pointRank_eq_chartFiberRank _ (V := ⟨W, hW⟩) y hyW,
    pointRank_eq_chartFiberRank G (V := ⟨V, hV⟩) (g y) hgyV]
  -- the section formula for the pullback module over the affine pair
  letI : Algebra Γ(X, V) Γ(Y, W) := (g.appLE V W hWle).hom.toAlgebra
  letI : Module Γ(X, V) Γ((Scheme.Modules.pullback g).obj G, W) :=
    Module.compHom _ (g.appLE V W hWle).hom
  obtain ⟨⟨eqv, -⟩⟩ :=
    pullback_app_isoTensor_baseMap_sectionLinearEquiv g G hW hV hWle
  -- fiber rank through the equivalence, then base change
  have h1 : ((hW.primeIdealOf ⟨y, hyW⟩).asIdeal).fiberRank
      Γ((Scheme.Modules.pullback g).obj G, W) =
      ((hW.primeIdealOf ⟨y, hyW⟩).asIdeal).fiberRank
        (TensorProduct Γ(X, V) Γ(Y, W) Γ(G, V)) :=
    Ideal.fiberRank_congr _ eqv.symm
  have h2 := Ideal.fiberRank_baseChange (R := Γ(X, V)) (A := Γ(Y, W))
    Γ(G, V) ((hW.primeIdealOf ⟨y, hyW⟩).asIdeal)
  -- identify the contracted prime with the prime of the image point
  have h3 : ((hW.primeIdealOf ⟨y, hyW⟩).asIdeal).comap
      (algebraMap Γ(X, V) Γ(Y, W)) =
      (hV.primeIdealOf ⟨g y, hgyV⟩).asIdeal := by
    have h4 := IsAffineOpen.comap_primeIdealOf_appLE (f := g)
      V hV W hW hWle hyW
    have h5 : algebraMap Γ(X, V) Γ(Y, W) = (g.appLE V W hWle).hom := rfl
    rw [h5]
    exact congrArg PrimeSpectrum.asIdeal h4
  change ((hW.primeIdealOf ⟨y, hyW⟩).asIdeal).fiberRank
      Γ((Scheme.Modules.pullback g).obj G, W) =
    ((hV.primeIdealOf ⟨g y, hgyV⟩).asIdeal).fiberRank Γ(G, V)
  rw [h1, h2]
  exact Ideal.fiberRank_congr_ideal h3

end PointRankPullback

/-! ## §3 Stage D1: unique factorization through the stratum -/

section StageD1

variable {X T : Scheme.{u}} (G : X.Modules) [G.IsQuasicoherent] {e : ℕ}

/-- **The kernel bound** (the hard half of Nitsure's universal property,
`n = 0`, [Nitsure §4]: "`f^*𝓕` is locally free of rank `e` iff `f^*ψ = 0`
iff `f` factors through `V_e`"): if the pullback of `G` along `q : T ⟶ X`
is flat over `T` of constant point rank `e`, then the strata ideal sheaf is
contained in the kernel of `q` — every local relation matrix pulls back to
the zero matrix, so its entries die in `Γ(T, ·)`. -/
theorem strataData_le_ker (hcov : ChartsCover G e) (q : T ⟶ X)
    (hflat : Scheme.CoherentSheafFlat (𝟙 T)
      ((Scheme.Modules.pullback q).obj G))
    (hrank : ∀ t : T,
      haveI := pullback_isQuasicoherent_hom q G ‹_›
      pointRank T ((Scheme.Modules.pullback q).obj G) t = e) :
    strataData G e hcov ≤ q.ker := by
  haveI := pullback_isQuasicoherent_hom q G ‹_›
  refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr fun U => ?_
  intro r hr
  rw [RingHom.mem_ker]
  -- a finite family of `e`-presentation charts covering `U`
  obtain ⟨N, Vc, mmc, Pc, hVcU, hcovU⟩ :=
    ChartsCover.exists_finite_charts G hcov U
  -- the pulled-back section dies on an affine neighbourhood of each point
  apply T.IsSheaf.section_ext fun t ht => ?_
  obtain ⟨i, hti⟩ := hcovU (q.base t) ht
  have htVc : t ∈ q ⁻¹ᵁ (Vc i).1 := hti
  obtain ⟨W, hW, htW, hWle⟩ :=
    exists_isAffineOpen_mem_and_subset (x := t) (U := q ⁻¹ᵁ (Vc i).1) htVc
  have hV : W ≤ q ⁻¹ᵁ U.1 := fun y hy => hVcU i (hWle hy)
  refine ⟨W, hV, htW, ?_⟩
  -- the relation matrix of the chart pulls back to zero on `W`
  haveI hFlatW : Module.Flat Γ(T, W)
      Γ((Scheme.Modules.pullback q).obj G, W) :=
    flat_sections_of_coherentSheafFlat_id hflat hW
  obtain ⟨P', hP'⟩ := exists_matrixPresentation_pullback_sections q G
    (Vc i).2 hW hWle (Pc i)
  haveI : Module.Finite Γ(T, W) Γ((Scheme.Modules.pullback q).obj G, W) :=
    Module.Finite.of_surjective P'.proj P'.surjective_proj
  have h0 : P'.relMatrix = 0 :=
    P'.relMatrix_eq_zero_of_flat fun p =>
      (rankAtStalk_sections_eq_pointRank _ hW p).trans (hrank _)
  -- hence the entry ideal is killed by `q.appLE (Vc i) W`
  letI : Algebra Γ(X, (Vc i).1) Γ(T, W) := (q.appLE (Vc i).1 W hWle).hom.toAlgebra
  have hker : (Pc i).entryIdeal ≤
      RingHom.ker (algebraMap Γ(X, (Vc i).1) Γ(T, W)) :=
    (_root_.Module.MatrixPresentation.relMatrix_map_eq_zero_iff
      (A := Γ(T, W))).mp (hP' ▸ h0)
  -- the strata-ideal condition at the chart
  have hmem : X.presheaf.map (homOfLE (hVcU i)).op r ∈ (Pc i).entryIdeal :=
    (mem_strataIdeal_iff G).mp hr (Vc i) (hVcU i) (mmc i) (Pc i)
  have hzero : (q.appLE (Vc i).1 W hWle).hom
      (X.presheaf.map (homOfLE (hVcU i)).op r) = 0 :=
    RingHom.mem_ker.mp (hker hmem)
  -- assemble: restriction of `q.app U r` to `W` is `q.appLE (Vc i) W` of
  -- the restricted section
  have hres : (T.presheaf.map (homOfLE hV).op).hom ((q.app U.1).hom r) =
      (q.appLE U.1 W hV).hom r := rfl
  change (T.presheaf.map (homOfLE hV).op).hom ((q.app U.1).hom r) =
    (T.presheaf.map (homOfLE hV).op).hom 0
  rw [map_zero, hres, ← appLE_base_res_apply' q (hVcU i) hWle hV r, hzero]

/-- **Unique factorization through the rank-`e` stratum** [Nitsure §4,
part (ii), `n = 0` case]: a morphism `q : T ⟶ X` whose pulled-back module
is flat over `T` of constant point rank `e` factors uniquely through the
closed immersion of the rank-`e` stratum. -/
theorem existsUnique_stratumLift (hcov : ChartsCover G e) (q : T ⟶ X)
    (hflat : Scheme.CoherentSheafFlat (𝟙 T)
      ((Scheme.Modules.pullback q).obj G))
    (hrank : ∀ t : T,
      haveI := pullback_isQuasicoherent_hom q G ‹_›
      pointRank T ((Scheme.Modules.pullback q).obj G) t = e) :
    ∃! l : T ⟶ stratum G e hcov, l ≫ stratumι G e hcov = q := by
  have hker : (stratumι G e hcov).ker ≤ q.ker := by
    have h1 : (stratumι G e hcov).ker = strataData G e hcov :=
      Scheme.IdealSheafData.ker_subschemeι (strataData G e hcov)
    rw [h1]
    exact strataData_le_ker G hcov q hflat hrank
  refine ⟨IsClosedImmersion.lift (stratumι G e hcov) q hker,
    IsClosedImmersion.lift_fac _ _ hker, fun l' hl' => ?_⟩
  rw [← cancel_mono (stratumι G e hcov), hl',
    IsClosedImmersion.lift_fac]

end StageD1

/-! ## §4 Stage D2: the stratum pullback is flat -/

section StageD2

variable {X : Scheme.{u}} (G : X.Modules) [G.IsQuasicoherent] {e : ℕ}

/-- **The rank-`e` stratum flattens `G`** [Nitsure §4, `n = 0`: on `V_e`
the pulled-back presentation has vanishing relation matrix, so `𝓕|_{V_e}`
is free of rank `e`]: the pullback of `G` along the stratum immersion is
flat over the stratum. -/
theorem coherentSheafFlat_stratum (hcov : ChartsCover G e) :
    Scheme.CoherentSheafFlat (𝟙 (stratum G e hcov))
      ((Scheme.Modules.pullback (stratumι G e hcov)).obj G) := by
  haveI := pullback_isQuasicoherent_hom (stratumι G e hcov) G ‹_›
  -- the chart preimages cover the stratum
  have hcover : ∀ z : stratum G e hcov,
      ∃ j : {V : X.affineOpens // IsPresentationChart G e V},
        z ∈ stratumι G e hcov ⁻¹ᵁ j.1.1 := by
    intro z
    obtain ⟨V, hzV, hchart⟩ := hcov ((stratumι G e hcov).base z)
    exact ⟨⟨V, hchart⟩, hzV⟩
  -- flat sections on each chart preimage: the pulled-back presentation
  -- has vanishing relation matrix, so the section module is free
  have hflatj : ∀ j : {V : X.affineOpens // IsPresentationChart G e V},
      Module.Flat Γ(stratum G e hcov, stratumι G e hcov ⁻¹ᵁ j.1.1)
        Γ((Scheme.Modules.pullback (stratumι G e hcov)).obj G,
          stratumι G e hcov ⁻¹ᵁ j.1.1) := by
    intro j
    obtain ⟨mm, ⟨P⟩⟩ := j.2
    obtain ⟨P', hP'⟩ := exists_matrixPresentation_pullback_sections
      (stratumι G e hcov) G j.1.2 (j.1.2.preimage (stratumι G e hcov))
      le_rfl P
    have h0 : P'.relMatrix = 0 := by
      rw [hP']
      ext a b
      simp only [Matrix.map_apply, Matrix.zero_apply]
      -- the entry lies in the strata ideal, the kernel of `stratumι.app`
      have hmem : ((stratumι G e hcov).app j.1.1).hom (P.relMatrix a b) = 0 := by
        have h1 : P.relMatrix a b ∈
            RingHom.ker (((strataData G e hcov).subschemeι.app j.1.1).hom) := by
          rw [Scheme.IdealSheafData.ker_subschemeι_app]
          change P.relMatrix a b ∈ strataIdeal G e j.1
          rw [strataIdeal_eq_entryIdeal G P]
          exact P.relMatrix_mem_entryIdeal a b
        exact RingHom.mem_ker.mp h1
      -- `appLE` at `le_rfl` is `app` followed by the trivial restriction
      change ((stratumι G e hcov).appLE j.1.1
        (stratumι G e hcov ⁻¹ᵁ j.1.1) le_rfl).hom (P.relMatrix a b) = 0
      have happ : ((stratumι G e hcov).appLE j.1.1
          (stratumι G e hcov ⁻¹ᵁ j.1.1) le_rfl).hom (P.relMatrix a b) =
          ((stratum G e hcov).presheaf.map (homOfLE le_rfl).op).hom
            (((stratumι G e hcov).app j.1.1).hom (P.relMatrix a b)) := rfl
      rw [happ, hmem, map_zero]
    haveI := P'.free_of_relMatrix_eq_zero h0
    infer_instance
  intro U hU V hV eV
  exact coherentSheafFlat_id_of_charts
    ((Scheme.Modules.pullback (stratumι G e hcov)).obj G)
    (fun j : {V : X.affineOpens // IsPresentationChart G e V} =>
      stratumι G e hcov ⁻¹ᵁ j.1.1)
    (fun j => j.1.2.preimage (stratumι G e hcov)) hcover hflatj hU hV eV

end StageD2

/-! ## §5 Stage E: chart supply and the chart locus (noetherian base) -/

section ChartSupply

/-- Any finitely presented module admits a matrix presentation (the
generators of the finitely generated kernel of a finite free surjection
are the columns of the relation matrix). -/
theorem _root_.Module.FinitePresentation.exists_matrixPresentation
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] :
    ∃ (ee mm : ℕ), Nonempty (MatrixPresentation R M ee mm) := by
  classical
  obtain ⟨n, K, eqv, hK⟩ :=
    Module.FinitePresentation.exists_fin R M
  obtain ⟨T, hT⟩ := hK
  refine ⟨n, T.card, ⟨MatrixPresentation.congr (N := M) {
    relMatrix := Matrix.of fun i j ↦ (T.equivFin.symm j : Fin n → R) i
    proj := K.mkQ
    surjective_proj := Submodule.mkQ_surjective K
    exact_mulVecLin_proj := ?_ } eqv.symm⟩⟩
  rw [LinearMap.exact_iff, Submodule.ker_mkQ, ← hT]
  apply le_antisymm
  · -- each generator is a column of the matrix
    rw [Submodule.span_le]
    intro t ht
    obtain ⟨j, hj⟩ := T.equivFin.symm.surjective ⟨t, ht⟩
    refine ⟨Pi.single j 1, ?_⟩
    funext i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.of_apply]
    rw [dotProduct_single, mul_one, hj]
  · -- every matrix-vector product is a combination of the columns
    rintro _ ⟨x, rfl⟩
    have hcol : (Matrix.of fun i j ↦ (T.equivFin.symm j : Fin n → R) i).mulVecLin x =
        ∑ j, x j • ((T.equivFin.symm j : Fin n → R)) := by
      funext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [hcol]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span (T.equivFin.symm j).2)

variable {S : Scheme.{u}}

-- the `Γ(S, U)`-module structure on sections over a basic open, from
-- `AlgebraicJacobian.Picard.EntryIdealStratum` (declared there as local
-- instances)
attribute [local instance] moduleSectionBasicOpen isScalarTowerSectionBasicOpen

/-- **Chart supply at every point** ([Nitsure §4], Nakayama prolongation of
a fibre basis; the geometric form of
`Module.FinitePresentation.exists_matrixPresentation_of_isLocalizedModule`):
on a locally noetherian scheme, every point of a finitely presented module
sheaf has an `e`-presentation chart around it with `e` its own point
rank. -/
theorem exists_presentationChart_mem [IsLocallyNoetherian S]
    (F : S.Modules) [F.IsFinitePresentation] (s : S) :
    ∃ V : S.affineOpens, s ∈ V.1 ∧
      IsPresentationChart F (pointRank S F s) V := by
  obtain ⟨V, hV, hsV, -, hfin⟩ := exists_affine_finite_sections_nhds F s ⊤ trivial
  haveI : IsNoetherianRing Γ(S, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : Module.Finite Γ(S, V) Γ(F, V) := hfin
  haveI : Module.FinitePresentation Γ(S, V) Γ(F, V) :=
    Module.finitePresentation_of_finite _ _
  obtain ⟨g, hgp, hloc⟩ :=
    Module.FinitePresentation.exists_matrixPresentation_of_isLocalizedModule
      (M := Γ(F, V)) (hV.primeIdealOf ⟨s, hsV⟩).asIdeal
  haveI := hV.isLocalization_basicOpen g
  haveI := Scheme.Modules.isLocalizedModule_basicOpen F hV g
  obtain ⟨mm, ⟨P⟩⟩ := hloc Γ(S, S.basicOpen g) Γ(F, S.basicOpen g)
    (restrictBasicOpenₗ F g)
  have hrank : ((hV.primeIdealOf ⟨s, hsV⟩).asIdeal).fiberRank Γ(F, V) =
      pointRank S F s :=
    (pointRank_eq_chartFiberRank F (V := ⟨V, hV⟩) s hsV).symm
  refine ⟨S.affineBasicOpen (U := ⟨V, hV⟩) g, ?_, mm, ⟨hrank ▸ P⟩⟩
  exact (hV.mem_basicOpen_iff_notMem_primeIdealOf g ⟨s, hsV⟩).mpr hgp

variable (F : S.Modules) (e : ℕ)

/-- The **chart locus**: the union of all `e`-presentation charts — the
open locus on which the rank-`e` stratum is a closed subscheme
[Nitsure §4: the ambient open `V` of the local construction]. -/
noncomputable def chartLocus : S.Opens :=
  ⨆ V : {V : S.affineOpens // IsPresentationChart F e V}, V.1.1

/-- Points of point rank exactly `e` lie in the chart locus. -/
theorem mem_chartLocus_of_pointRank_eq [IsLocallyNoetherian S]
    [F.IsFinitePresentation] {s : S} (h : pointRank S F s = e) :
    s ∈ chartLocus F e := by
  obtain ⟨V, hsV, hchart⟩ := exists_presentationChart_mem F s
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, h ▸ hchart⟩, hsV⟩

/-- Points of the chart locus have point rank at most `e` (an
`e`-generator presentation bounds every fibre dimension). -/
theorem pointRank_le_of_mem_chartLocus [F.IsQuasicoherent] {s : S}
    (h : s ∈ chartLocus F e) : pointRank S F s ≤ e := by
  obtain ⟨⟨V, hchart⟩, hsV⟩ := TopologicalSpace.Opens.mem_iSup.mp h
  obtain ⟨mm, ⟨P⟩⟩ := hchart
  rw [pointRank_eq_chartFiberRank F (V := V) s hsV]
  exact P.fiberRank_le _

end ChartSupply

/-! ## §6 Stage E: the rank stratum over the chart locus -/

section FlatPullback

/-- **Flatness is stable under arbitrary pullback**: if `G` is flat over
`T` (via `𝟙 T`), then `g^*G` is flat over `T'` for any morphism
`g : T' ⟶ T` — affine-locally the sections are a base change of a flat
module. -/
theorem coherentSheafFlat_id_pullback {T' T : Scheme.{u}} (g : T' ⟶ T)
    (G : T.Modules) [G.IsQuasicoherent]
    (h : Scheme.CoherentSheafFlat (𝟙 T) G) :
    Scheme.CoherentSheafFlat (𝟙 T') ((Scheme.Modules.pullback g).obj G) := by
  haveI := pullback_isQuasicoherent_hom g G ‹_›
  -- cover `T'` by affine opens lying over affine opens of `T`
  set J := {p : T'.Opens × T.Opens //
    IsAffineOpen p.1 ∧ IsAffineOpen p.2 ∧ p.1 ≤ g ⁻¹ᵁ p.2} with hJ
  have hcover : ∀ t' : T', ∃ j : J, t' ∈ j.1.1 := by
    intro t'
    obtain ⟨V, hV, hgt', -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := g.base t') (U := ⊤) trivial
    have ht' : t' ∈ g ⁻¹ᵁ V := hgt'
    obtain ⟨W, hW, htW, hWle⟩ :=
      exists_isAffineOpen_mem_and_subset (x := t') (U := g ⁻¹ᵁ V) ht'
    exact ⟨⟨(W, V), hW, hV, hWle⟩, htW⟩
  have hflatj : ∀ j : J, Module.Flat Γ(T', j.1.1)
      Γ((Scheme.Modules.pullback g).obj G, j.1.1) := by
    intro ⟨⟨W, V⟩, hW, hV, hle⟩
    haveI : Module.Flat Γ(T, V) Γ(G, V) :=
      flat_sections_of_coherentSheafFlat_id h hV
    letI : Algebra Γ(T, V) Γ(T', W) := (g.appLE V W hle).hom.toAlgebra
    letI : Module Γ(T, V) Γ((Scheme.Modules.pullback g).obj G, W) :=
      Module.compHom _ (g.appLE V W hle).hom
    obtain ⟨⟨eqv, -⟩⟩ :=
      pullback_app_isoTensor_baseMap_sectionLinearEquiv g G hW hV hle
    exact Module.Flat.of_linearEquiv eqv.symm
  intro U hU V hV eV
  exact flat_section_of_affine_cover (𝟙 T') ((Scheme.Modules.pullback g).obj G)
    (fun j : J => j.1.1) (fun j => j.2.1) (fun j : J => j.1.1) (fun j => j.2.1)
    (fun j => le_refl _) hcover
    (fun j => (flat_compHom_congr
      ((𝟙 T' : T' ⟶ T').appLE j.1.1 j.1.1 (le_refl _)).hom
      (id_appLE_apply _)).mpr (hflatj j)) hU hV eV

end FlatPullback

section RankStratum

variable {S : Scheme.{u}} (F : S.Modules) (e : ℕ) [F.IsQuasicoherent]

/-- The restriction of `F` to the chart locus is chart-covered: the charts
of `S` inside the chart locus pull back to charts of the open subscheme
(the pullback of an `e`-generator presentation is an `e`-generator
presentation). -/
theorem chartsCover_chartLocus :
    ChartsCover ((Scheme.Modules.pullback (chartLocus F e).ι).obj F) e := by
  intro x
  have hx : ((chartLocus F e).ι.base x) ∈ chartLocus F e := by
    have h0 : ((chartLocus F e).ι.base x) ∈ Set.range (chartLocus F e).ι :=
      Set.mem_range_self x
    rwa [Scheme.Opens.range_ι] at h0
  obtain ⟨⟨V, hchart⟩, hxV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hVle : V.1 ≤ (chartLocus F e).ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    exact le_iSup
      (fun W : {V : S.affineOpens // IsPresentationChart F e V} => W.1.1)
      ⟨V, hchart⟩
  have hpre : IsAffineOpen ((chartLocus F e).ι ⁻¹ᵁ V.1) :=
    V.2.preimage_of_isOpenImmersion (chartLocus F e).ι hVle
  refine ⟨⟨(chartLocus F e).ι ⁻¹ᵁ V.1, hpre⟩, hxV, ?_⟩
  obtain ⟨mm, ⟨P⟩⟩ := hchart
  obtain ⟨P', -⟩ := exists_matrixPresentation_pullback_sections
    (chartLocus F e).ι F V.2 hpre le_rfl P
  exact ⟨mm, ⟨P'⟩⟩

/-- The **rank-`e` stratum of `F`**: the canonical closed subscheme of the
chart locus cut out by the entry ideals [Nitsure §4, `n = 0`: the closed
subscheme `V_e ⊆ V`]. -/
noncomputable def rankStratum : Scheme.{u} :=
  haveI := pullback_isQuasicoherent_hom (chartLocus F e).ι F ‹_›
  stratum ((Scheme.Modules.pullback (chartLocus F e).ι).obj F) e
    (chartsCover_chartLocus F e)

/-- The locally closed immersion of the rank-`e` stratum into the base. -/
noncomputable def rankStratumι : rankStratum F e ⟶ S :=
  haveI := pullback_isQuasicoherent_hom (chartLocus F e).ι F ‹_›
  stratumι ((Scheme.Modules.pullback (chartLocus F e).ι).obj F) e
    (chartsCover_chartLocus F e) ≫ (chartLocus F e).ι

instance : IsImmersion (rankStratumι F e) := by
  haveI := pullback_isQuasicoherent_hom (chartLocus F e).ι F ‹_›
  change IsImmersion
    (stratumι ((Scheme.Modules.pullback (chartLocus F e).ι).obj F) e
      (chartsCover_chartLocus F e) ≫ (chartLocus F e).ι)
  infer_instance

/-- **The support of the rank-`e` stratum is the rank-`e` locus**
[Nitsure §4, part (i)]. -/
theorem mem_range_rankStratumι_iff [IsLocallyNoetherian S]
    [F.IsFinitePresentation] (s : S) :
    s ∈ Set.range (rankStratumι F e).base ↔ pointRank S F s = e := by
  haveI := pullback_isQuasicoherent_hom (chartLocus F e).ι F ‹_›
  constructor
  · rintro ⟨z, rfl⟩
    have hz : (rankStratumι F e).base z = ((chartLocus F e).ι.base)
        ((stratumι ((Scheme.Modules.pullback (chartLocus F e).ι).obj F) e
          (chartsCover_chartLocus F e)).base z) := rfl
    rw [hz, ← pointRank_pullback (chartLocus F e).ι F]
    exact (mem_range_stratumι_iff _ (chartsCover_chartLocus F e) _).mp
      ⟨z, rfl⟩
  · intro h
    have hs : s ∈ chartLocus F e := mem_chartLocus_of_pointRank_eq F e h
    have hs' : s ∈ Set.range (chartLocus F e).ι := by
      rwa [Scheme.Opens.range_ι]
    obtain ⟨x, hx⟩ := hs'
    have hrx : pointRank ((chartLocus F e) : Scheme.{u})
        ((Scheme.Modules.pullback (chartLocus F e).ι).obj F) x = e := by
      rw [pointRank_pullback (chartLocus F e).ι F x, hx]
      exact h
    obtain ⟨z, hz⟩ := (mem_range_stratumι_iff _
      (chartsCover_chartLocus F e) x).mpr hrx
    refine ⟨z, ?_⟩
    change ((chartLocus F e).ι.base)
      ((stratumι ((Scheme.Modules.pullback (chartLocus F e).ι).obj F) e
        (chartsCover_chartLocus F e)).base z) = s
    rw [show ((stratumι ((Scheme.Modules.pullback (chartLocus F e).ι).obj F) e
      (chartsCover_chartLocus F e)).base z) = x from hz, hx]

/-- **The rank-`e` stratum flattens `F`** [Nitsure §4, part (i)]: the
pullback of `F` along the stratum immersion is flat over the stratum. -/
theorem coherentSheafFlat_rankStratum :
    Scheme.CoherentSheafFlat (𝟙 (rankStratum F e))
      ((Scheme.Modules.pullback (rankStratumι F e)).obj F) := by
  haveI := pullback_isQuasicoherent_hom (chartLocus F e).ι F ‹_›
  intro U hU V hV eV
  exact coherentSheafFlat_of_iso (𝟙 (rankStratum F e))
    ((Scheme.Modules.pullbackComp
      (stratumι ((Scheme.Modules.pullback (chartLocus F e).ι).obj F) e
        (chartsCover_chartLocus F e)) (chartLocus F e).ι).app F)
    (coherentSheafFlat_stratum
      ((Scheme.Modules.pullback (chartLocus F e).ι).obj F)
      (chartsCover_chartLocus F e)) hU hV eV

end RankStratum

/-! ## §7 Stage E: rank bound and openness of the rank fibers -/

section RankBound

variable {S : Scheme.{u}}

/-- **The point rank is bounded on a noetherian scheme**: finitely many
presentation charts cover `S` by quasi-compactness, and each caps the rank
by its generator count. -/
theorem exists_pointRank_le [IsNoetherian S] (F : S.Modules)
    [F.IsFinitePresentation] : ∃ N : ℕ, ∀ s : S, pointRank S F s ≤ N := by
  classical
  choose Vc hVc hchart using exists_presentationChart_mem (S := S) F
  have hcov : (Set.univ : Set S) ⊆ ⋃ s : S, ((Vc s).1 : Set S) := fun x _ =>
    Set.mem_iUnion.mpr ⟨x, hVc x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun s : S => ((Vc s).1 : Set S)) (fun s => (Vc s).1.isOpen) hcov
  refine ⟨t.sup fun s => pointRank S F s, fun x => ?_⟩
  obtain ⟨s, hst, hxs⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  calc pointRank S F x ≤ pointRank S F s := by
        obtain ⟨mm, ⟨P⟩⟩ := hchart s
        rw [pointRank_eq_chartFiberRank F (V := Vc s) x hxs]
        exact P.fiberRank_le _
    _ ≤ t.sup (fun s => pointRank S F s) := Finset.le_sup hst

/-- **The rank fibers of a flat pullback are open** (local constancy of the
rank of a flat, finitely presented module, geometrized through `fromSpec`):
if `φ^*F` is flat over `T`, the locus where its point rank equals `e` is
open in `T`. -/
theorem isOpen_pointRank_pullback_eq {T : Scheme.{u}} [IsLocallyNoetherian S]
    (F : S.Modules) [F.IsFinitePresentation] (φ : T ⟶ S)
    (hflat : Scheme.CoherentSheafFlat (𝟙 T)
      ((Scheme.Modules.pullback φ).obj F)) (e : ℕ) :
    haveI := pullback_isQuasicoherent_hom φ F inferInstance
    IsOpen {t : T | pointRank T ((Scheme.Modules.pullback φ).obj F) t = e} := by
  haveI := pullback_isQuasicoherent_hom φ F inferInstance
  rw [isOpen_iff_forall_mem_open]
  intro t₀ ht₀
  -- affine charts: `V ∋ φ t₀` with finitely presented sections, `W ∋ t₀`
  obtain ⟨V, hV, hφt, -, hfin⟩ :=
    exists_affine_finite_sections_nhds F (φ.base t₀) ⊤ trivial
  haveI : IsNoetherianRing Γ(S, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : Module.Finite Γ(S, V) Γ(F, V) := hfin
  haveI : Module.FinitePresentation Γ(S, V) Γ(F, V) :=
    Module.finitePresentation_of_finite _ _
  have ht' : t₀ ∈ φ ⁻¹ᵁ V := hφt
  obtain ⟨W, hW, htW, hWle⟩ :=
    exists_isAffineOpen_mem_and_subset (x := t₀) (U := φ ⁻¹ᵁ V) ht'
  -- section module over `W`: flat and finitely presented
  haveI : Module.Flat Γ(T, W) Γ((Scheme.Modules.pullback φ).obj F, W) :=
    flat_sections_of_coherentSheafFlat_id hflat hW
  obtain ⟨ee, mm, ⟨P⟩⟩ := Module.FinitePresentation.exists_matrixPresentation
    (R := Γ(S, V)) (M := Γ(F, V))
  obtain ⟨P', -⟩ := exists_matrixPresentation_pullback_sections φ F hV hW hWle P
  haveI : Module.FinitePresentation Γ(T, W)
      Γ((Scheme.Modules.pullback φ).obj F, W) := P'.finitePresentation
  -- transport the locally constant stalk rank through `fromSpec`
  have hlc := Module.isLocallyConstant_rankAtStalk
    (R := Γ(T, W)) (M := Γ((Scheme.Modules.pullback φ).obj F, W))
  refine ⟨hW.fromSpec.base ''
    (Module.rankAtStalk Γ((Scheme.Modules.pullback φ).obj F, W) ⁻¹' {e}),
    ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    change pointRank T ((Scheme.Modules.pullback φ).obj F)
      (hW.fromSpec.base p) = e
    rw [← rankAtStalk_sections_eq_pointRank
      ((Scheme.Modules.pullback φ).obj F) hW p]
    exact hp
  · exact hW.fromSpec.isOpenEmbedding.isOpenMap _ (hlc.isOpen_fiber e)
  · refine ⟨hW.primeIdealOf ⟨t₀, htW⟩, ?_, ?_⟩
    · change Module.rankAtStalk Γ((Scheme.Modules.pullback φ).obj F, W)
        (hW.primeIdealOf ⟨t₀, htW⟩) = e
      rw [rankAtStalk_sections_eq_pointRank
        ((Scheme.Modules.pullback φ).obj F) hW]
      have hfs : (hW.fromSpec.base (hW.primeIdealOf ⟨t₀, htW⟩) : T) = t₀ :=
        hW.fromSpec_primeIdealOf ⟨t₀, htW⟩
      rw [hfs]
      exact ht₀
    · exact hW.fromSpec_primeIdealOf ⟨t₀, htW⟩

end RankBound

/-! ## §8 Stage E: the universal factorization through a single stratum -/

section FactorRankStratum

variable {S : Scheme.{u}} (F : S.Modules) [F.IsQuasicoherent]

/-- **Unique factorization through the rank-`e` stratum of the base**
[Nitsure §4, part (ii), `n = 0`, single-rank case]: a morphism `φ : T ⟶ S`
whose pulled-back module is flat with *constant* point rank `e` (measured
on the base) factors uniquely through the locally closed immersion
`rankStratumι`. -/
theorem existsUnique_factor_rankStratum [IsLocallyNoetherian S]
    [F.IsFinitePresentation] (e : ℕ) {T : Scheme.{u}} (φ : T ⟶ S)
    (hflat : Scheme.CoherentSheafFlat (𝟙 T)
      ((Scheme.Modules.pullback φ).obj F))
    (hrank : ∀ t : T, pointRank S F (φ.base t) = e) :
    ∃! l : T ⟶ rankStratum F e, l ≫ rankStratumι F e = φ := by
  haveI := pullback_isQuasicoherent_hom (chartLocus F e).ι F inferInstance
  -- `φ` lands in the chart locus
  have hrange : Set.range φ.base ⊆ Set.range (chartLocus F e).ι.base := by
    rintro _ ⟨t, rfl⟩
    have h1 : φ.base t ∈ chartLocus F e :=
      mem_chartLocus_of_pointRank_eq F e (hrank t)
    have h2 : (chartLocus F e : Set S) ⊆ Set.range (chartLocus F e).ι.base := by
      rw [Scheme.Opens.range_ι]
    exact h2 h1
  set q : T ⟶ (chartLocus F e : Scheme.{u}) :=
    IsOpenImmersion.lift (chartLocus F e).ι φ hrange with hq
  have hqfac : q ≫ (chartLocus F e).ι = φ :=
    IsOpenImmersion.lift_fac (chartLocus F e).ι φ hrange
  -- flatness of the pullback along `q`
  have hflat_q : Scheme.CoherentSheafFlat (𝟙 T)
      ((Scheme.Modules.pullback q).obj
        ((Scheme.Modules.pullback (chartLocus F e).ι).obj F)) := by
    intro U hU V hV eV
    exact coherentSheafFlat_of_iso (𝟙 T)
      (((Scheme.Modules.pullbackComp q (chartLocus F e).ι).app F ≪≫
        (Scheme.Modules.pullbackCongr hqfac).app F).symm) hflat hU hV eV
  -- constant rank of the pullback along `q`
  have hrank_q : ∀ t : T,
      haveI := pullback_isQuasicoherent_hom q
        ((Scheme.Modules.pullback (chartLocus F e).ι).obj F) ‹_›
      pointRank T ((Scheme.Modules.pullback q).obj
        ((Scheme.Modules.pullback (chartLocus F e).ι).obj F)) t = e := by
    intro t
    rw [pointRank_pullback q ((Scheme.Modules.pullback (chartLocus F e).ι).obj F) t,
      pointRank_pullback (chartLocus F e).ι F]
    have hpt : (chartLocus F e).ι.base (q.base t) = φ.base t := by
      have := congrArg (fun m : T ⟶ S => m.base t) hqfac
      simpa using this
    rw [hpt]
    exact hrank t
  obtain ⟨l, hl, hluniq⟩ := existsUnique_stratumLift
    ((Scheme.Modules.pullback (chartLocus F e).ι).obj F)
    (chartsCover_chartLocus F e) q hflat_q hrank_q
  refine ⟨l, ?_, ?_⟩
  · change l ≫ (stratumι ((Scheme.Modules.pullback (chartLocus F e).ι).obj F) e
      (chartsCover_chartLocus F e) ≫ (chartLocus F e).ι) = φ
    rw [← Category.assoc, hl, hqfac]
  · intro l' hl'
    refine hluniq l' ?_
    change l' ≫ stratumι ((Scheme.Modules.pullback (chartLocus F e).ι).obj F) e
      (chartsCover_chartLocus F e) = q
    rw [← cancel_mono (chartLocus F e).ι, Category.assoc]
    show l' ≫ (stratumι ((Scheme.Modules.pullback (chartLocus F e).ι).obj F) e
      (chartsCover_chartLocus F e) ≫ (chartLocus F e).ι) = q ≫ (chartLocus F e).ι
    rw [hqfac]
    exact hl'

end FactorRankStratum

end Scheme.Modules

/-! ## §9 The universal property of the flat-locus stratification -/

section UniversalTheorem

open Scheme.Modules Limits

set_option maxHeartbeats 1600000 in
-- Dependent coproduct uniqueness expands `Sigma.ι`/`Sigma.desc` and open-immersion
-- transports; the default budget times out in definitional equality checking.
/-- **Universal property of the flat-locus stratification (the `n = 0`
flattening stratification)** [Nitsure §4, special case, parts (i) + (ii)].

For `S` noetherian and `𝓕` a coherent `𝓞_S`-module there is a *finite*
locally-closed stratification `{S_f}` of `S` — immersions, set-theoretically
covering `|S|`, pairwise disjoint, `𝓕|_{S_f}` flat over `S_f` — such that,
writing `i : ∐ S_f ⟶ S` for `Sigma.desc` of the inclusions, every morphism
`φ : T ⟶ S` for which `φ^*𝓕` is flat over `T` factors *uniquely* through
`i`.

Source: [Nitsure], §4, proof of the flattening-stratification theorem,
special case `n = 0` (Nakayama prolongation of a fibre basis to a local
presentation `𝓞_V^{⊕m} →ψ 𝓞_V^{⊕e} → 𝓕|_V → 0`, the closed subscheme
`V_e ⊆ V` cut out by the entry ideal of `ψ`, base change: `f^*𝓕` is locally
free of rank `e` iff `f^*ψ = 0` iff `f` factors through `V_e`; the local
strata glue by their universal property).  Flatness replaces
locally-free-of-rank-`e`: for finitely presented `𝓕` they agree, with the
rank decomposing `T` into clopen pieces.

Statement repair (run 0010, T12 r7): the statement is specialized to
`π = 𝟙 S` — exactly Nitsure's special case, which his general-case proof
consumes; see the git history of
`AlgebraicJacobian.Picard.GenericFlatnessGeometric` for the discussion.

Proof (run 0010, T12): the strata are the canonical rank-`e` strata
`rankStratum F e` — closed subschemes of the open chart loci cut out by the
entry ideals (`AlgebraicJacobian.Picard.EntryIdealStratum`) — for
`e ≤ N` a rank bound (`exists_pointRank_le`, noetherian compactness).
Support, disjointness and covering are `mem_range_rankStratumι_iff`;
flatness over the strata is `coherentSheafFlat_rankStratum` (the pulled
back presentation has vanishing relation matrix).  For the universal
property, `T` decomposes into *open* rank pieces (local constancy of the
rank of a flat finitely presented module, `isOpen_pointRank_pullback_eq`),
giving a colimit cofan; each piece factors uniquely through its stratum
(`existsUnique_factor_rankStratum`, via `IsClosedImmersion.lift` and the
vanishing of the pulled-back relation matrices, `strataData_le_ker`), and
the factorizations assemble.  Uniqueness: any competing factorization
lands, piecewise, in the same summand (the summand ranges have distinct
ranks), where it agrees by the monomorphism property of immersions. -/
theorem flatLocusStratification_universal {S : Scheme.{u}} [IsNoetherian S]
    (F : S.Modules) [F.IsFinitePresentation] :
    ∃ (I : Type u) (_ : Finite I) (S_ : I → Scheme.{u}) (ι : ∀ f, S_ f ⟶ S),
      (∀ f, IsImmersion (ι f)) ∧
      (∀ s : S, ∃ f, s ∈ Set.range (ι f).base) ∧
      (∀ f g, f ≠ g → Disjoint (Set.range (ι f).base) (Set.range (ι g).base)) ∧
      (∀ f, Scheme.CoherentSheafFlat (𝟙 (S_ f))
        ((Scheme.Modules.pullback (ι f)).obj F)) ∧
      (∀ {T : Scheme.{u}} (φ : T ⟶ S),
        Scheme.CoherentSheafFlat (𝟙 T) ((Scheme.Modules.pullback φ).obj F) →
        ∃! ψ : T ⟶ ∐ S_, ψ ≫ Sigma.desc ι = φ) := by
  classical
  obtain ⟨N, hN⟩ := exists_pointRank_le F
  refine ⟨ULift.{u} (Fin (N + 1)), inferInstance,
    fun i => rankStratum F i.down.1, fun i => rankStratumι F i.down.1,
    fun i => inferInstance, ?_, ?_,
    fun i => coherentSheafFlat_rankStratum F i.down.1, ?_⟩
  · -- covering: every point lies in the stratum of its own rank
    intro s
    exact ⟨⟨⟨pointRank S F s, Nat.lt_succ_of_le (hN s)⟩⟩,
      (mem_range_rankStratumι_iff F _ s).mpr rfl⟩
  · -- disjointness: the strata have distinct ranks
    intro i j hij
    rw [Set.disjoint_left]
    intro s hsi hsj
    have hi := (mem_range_rankStratumι_iff F i.down.1 s).mp hsi
    have hj := (mem_range_rankStratumι_iff F j.down.1 s).mp hsj
    exact hij (ULift.down_injective (Fin.val_injective (hi.symm.trans hj)))
  · -- the universal property
    intro T φ hφ
    haveI := pullback_isQuasicoherent_hom φ F inferInstance
    have hρle : ∀ t : T,
        pointRank T ((Scheme.Modules.pullback φ).obj F) t ≤ N := by
      intro t
      rw [pointRank_pullback φ F t]
      exact hN _
    -- the open rank pieces of `T`
    set Tp : ULift.{u} (Fin (N + 1)) → T.Opens := fun i =>
      ⟨{t : T | pointRank T ((Scheme.Modules.pullback φ).obj F) t = i.down.1},
        isOpen_pointRank_pullback_eq F φ hφ i.down.1⟩ with hTp
    have hcovT : ⨆ i, (Tp i).ι.opensRange = ⊤ := by
      rw [eq_top_iff]
      intro t _
      rw [TopologicalSpace.Opens.mem_iSup]
      refine ⟨⟨⟨pointRank T ((Scheme.Modules.pullback φ).obj F) t,
        Nat.lt_succ_of_le (hρle t)⟩⟩, ?_⟩
      rw [Scheme.Opens.opensRange_ι]
      exact rfl
    have hdisjT : Pairwise (Function.onFun Disjoint
        fun i => (Tp i).ι.opensRange) := by
      intro i j hij
      simp only [Function.onFun, Scheme.Opens.opensRange_ι]
      intro W hWi hWj t ht
      exact absurd (ULift.down_injective (Fin.val_injective
        ((hWi ht).symm.trans (hWj ht)))) hij
    obtain ⟨hcolim⟩ := nonempty_isColimit_cofanMk_of
      (fun i => (Tp i).ι) hcovT hdisjT
    -- unique factorization of each piece through its stratum
    have hfac_data : ∀ i : ULift.{u} (Fin (N + 1)),
        ∃! l : ((Tp i) : Scheme.{u}) ⟶ rankStratum F i.down.1,
          l ≫ rankStratumι F i.down.1 = (Tp i).ι ≫ φ := by
      intro i
      refine existsUnique_factor_rankStratum F i.down.1 ((Tp i).ι ≫ φ)
        ?_ ?_
      · intro U hU V hV eV
        exact coherentSheafFlat_of_iso (𝟙 _)
          ((Scheme.Modules.pullbackComp (Tp i).ι φ).app F)
          (coherentSheafFlat_id_pullback (Tp i).ι
            ((Scheme.Modules.pullback φ).obj F) hφ) hU hV eV
      · intro t
        have hmem : ((Tp i).ι.base t : T) ∈ Tp i := by
          have h0 : ((Tp i).ι.base t : T) ∈ Set.range (Tp i).ι :=
            Set.mem_range_self t
          rwa [Scheme.Opens.range_ι] at h0
        have hcomp : ((Tp i).ι ≫ φ).base t = φ.base ((Tp i).ι.base t) := rfl
        rw [hcomp, ← pointRank_pullback φ F]
        exact hmem
    choose l hlfac hluniq using hfac_data
    haveI : ∀ j : ULift.{u} (Fin (N + 1)), IsOpenImmersion
        (Sigma.ι (fun i : ULift.{u} (Fin (N + 1)) =>
          rankStratum F i.down.1) j) :=
      fun j => (sigmaOpenCover (fun i : ULift.{u} (Fin (N + 1)) =>
        rankStratum F i.down.1)).map_prop j
    -- assemble the factorization through the coproduct
    set ψ : T ⟶ ∐ (fun i : ULift.{u} (Fin (N + 1)) => rankStratum F i.down.1) :=
      hcolim.desc (Cofan.mk
        (∐ fun i : ULift.{u} (Fin (N + 1)) => rankStratum F i.down.1)
        (fun i => l i ≫ Sigma.ι
          (fun i : ULift.{u} (Fin (N + 1)) => rankStratum F i.down.1) i))
      with hψdef
    have hψfac : ∀ i, (Tp i).ι ≫ ψ = l i ≫ Sigma.ι
        (fun i : ULift.{u} (Fin (N + 1)) => rankStratum F i.down.1) i :=
      fun i => hcolim.fac (Cofan.mk
        (∐ fun i : ULift.{u} (Fin (N + 1)) => rankStratum F i.down.1)
        (fun i => l i ≫ Sigma.ι
          (fun i : ULift.{u} (Fin (N + 1)) => rankStratum F i.down.1) i)) ⟨i⟩
    refine ⟨ψ, ?_, ?_⟩
    · -- `ψ` recovers `φ`
      apply hcolim.hom_ext
      rintro ⟨i⟩
      simp only [Cofan.mk_ι_app]
      calc (Tp i).ι ≫ ψ ≫ Sigma.desc (fun i => rankStratumι F i.down.1)
          = ((Tp i).ι ≫ ψ) ≫ Sigma.desc (fun i => rankStratumι F i.down.1) :=
            (Category.assoc _ _ _).symm
        _ = (l i ≫ Sigma.ι
              (fun i : ULift.{u} (Fin (N + 1)) => rankStratum F i.down.1) i) ≫
              Sigma.desc (fun i => rankStratumι F i.down.1) :=
            congrArg (fun m => m ≫ Sigma.desc
              (fun i => rankStratumι F i.down.1)) (hψfac i)
        _ = l i ≫ Sigma.ι
              (fun i : ULift.{u} (Fin (N + 1)) => rankStratum F i.down.1) i ≫
              Sigma.desc (fun i => rankStratumι F i.down.1) :=
            Category.assoc _ _ _
        _ = l i ≫ rankStratumι F i.down.1 :=
            congrArg (fun m => l i ≫ m) (Sigma.ι_desc _ _)
        _ = (Tp i).ι ≫ φ := hlfac i
    · -- uniqueness
      intro ψ' hψ'
      apply hcolim.hom_ext
      rintro ⟨i⟩
      simp only [Cofan.mk_ι_app]
      have hχdesc : ((Tp i).ι ≫ ψ') ≫
          Sigma.desc (fun i => rankStratumι F i.down.1) = (Tp i).ι ≫ φ :=
        (Category.assoc _ _ _).trans (congrArg (fun m => (Tp i).ι ≫ m) hψ')
      -- the composite lands in the summand of rank `i`
      have hχrange : Set.range ((Tp i).ι ≫ ψ').base ⊆ Set.range (Sigma.ι
          (fun i : ULift.{u} (Fin (N + 1)) => rankStratum F i.down.1) i).base := by
        rintro _ ⟨t, rfl⟩
        obtain ⟨e', z, hz⟩ := (sigmaOpenCover
          (fun i : ULift.{u} (Fin (N + 1)) =>
            rankStratum F i.down.1)).exists_eq (((Tp i).ι ≫ ψ').base t)
        have hzb : Sigma.ι (fun i : ULift.{u} (Fin (N + 1)) =>
            rankStratum F i.down.1) e' z = ((Tp i).ι ≫ ψ') t := hz
        have hpt : (rankStratumι F e'.down.1).base z =
            φ.base ((Tp i).ι.base t) := by
          have h2 := congrArg
            (fun m : ((Tp i) : Scheme.{u}) ⟶ S => m t) hχdesc
          dsimp only at h2
          rw [Scheme.Hom.comp_apply ((Tp i).ι ≫ ψ')
              (Sigma.desc fun i => rankStratumι F i.down.1) t,
            Scheme.Hom.comp_apply (Tp i).ι φ t, ← hzb,
            ← Scheme.Hom.comp_apply
              (Sigma.ι (fun i : ULift.{u} (Fin (N + 1)) =>
                rankStratum F i.down.1) e')
              (Sigma.desc fun i => rankStratumι F i.down.1) z,
            Sigma.ι_desc] at h2
          exact h2
        have hmem : ((Tp i).ι.base t : T) ∈ Tp i := by
          have h0 : ((Tp i).ι.base t : T) ∈ Set.range (Tp i).ι :=
            Set.mem_range_self t
          rwa [Scheme.Opens.range_ι] at h0
        have hrk1 : pointRank S F (φ.base ((Tp i).ι.base t)) = e'.down.1 :=
          (mem_range_rankStratumι_iff F e'.down.1 _).mp ⟨z, hpt⟩
        have hrk2 : pointRank S F (φ.base ((Tp i).ι.base t)) = i.down.1 := by
          rw [← pointRank_pullback φ F]
          exact hmem
        have he : e' = i := ULift.down_injective
          (Fin.val_injective (hrk1.symm.trans hrk2))
        subst he
        exact ⟨z, hzb⟩
      have hχ₀fac : IsOpenImmersion.lift (Sigma.ι
          (fun i : ULift.{u} (Fin (N + 1)) => rankStratum F i.down.1) i)
          ((Tp i).ι ≫ ψ') hχrange ≫ Sigma.ι
          (fun i : ULift.{u} (Fin (N + 1)) => rankStratum F i.down.1) i =
          (Tp i).ι ≫ ψ' :=
        IsOpenImmersion.lift_fac _ _ hχrange
      have hχ₀st : IsOpenImmersion.lift (Sigma.ι
          (fun i : ULift.{u} (Fin (N + 1)) => rankStratum F i.down.1) i)
          ((Tp i).ι ≫ ψ') hχrange ≫ rankStratumι F i.down.1 =
          (Tp i).ι ≫ φ := by
        have h3 := congrArg
          (fun m : ((rankStratum F i.down.1) : Scheme.{u}) ⟶ S =>
            IsOpenImmersion.lift (Sigma.ι
              (fun i : ULift.{u} (Fin (N + 1)) => rankStratum F i.down.1) i)
              ((Tp i).ι ≫ ψ') hχrange ≫ m)
          (Sigma.ι_desc
            (fun i : ULift.{u} (Fin (N + 1)) => rankStratumι F i.down.1) i)
        rw [← Category.assoc, hχ₀fac] at h3
        exact h3.symm.trans hχdesc
      exact hχ₀fac.symm.trans
        ((congrArg (fun m => m ≫ Sigma.ι
          (fun i : ULift.{u} (Fin (N + 1)) => rankStratum F i.down.1) i)
          (hluniq i _ hχ₀st)).trans (hψfac i).symm)

end UniversalTheorem

end AlgebraicGeometry
