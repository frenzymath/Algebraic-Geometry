/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RigidEngine5Toolkit
import AlgebraicJacobian.Cohomology.GluedSheafEngine
import AlgebraicJacobian.Cohomology.GluedSheafClass

/-!
# RE-5: presentation descent of the cocycle datum (worksheet §3.2)

**The keystone** (`BasicOpenCocycleDatum.exists_fg_subalgebra_baseChange_eq`): a pinned
cocycle datum over an arbitrary commutative `k`-algebra `B` descends to a finitely
generated `k`-subalgebra `B₀ ⊆ B` — there is a datum over `B₀` whose base change
(`GluedSheafDatumBaseChange.lean`, DAT-1 stage 1d-ii) along `B₀ → B` is **equal to**
the given datum. The engine-ready form `exists_fg_isNoetherianRing_baseChange_eq` adds
the Noetherian certificate for `B₀`, so `datumRigidEngine` fires over the stage
verbatim (`descentRigidEngine`).

**Mechanism** (worksheet §3.2, pinned): the chart sections `h_j, a_j` live in
`Γ(Vᵢᴮ, 𝒪) ≅ Γ(Vᵢ) ⊗_k B` and descend by the stage-(i) skeleton
(`DescentSkeleton.lean`); the transition units live in `Away`-localizations of the
chart(-overlap) rings and are FIRST cleared into the affine ambients
`fst⁻¹(chartAt i ⊓ chartAt j)` (`RigidEngine5Toolkit.lean`: two-sided fraction data
`u, v, N, N', e` with `u·v·σ^e = σ^(e+N+N')`), whose numerators descend; the descended
unit is reconstructed by `exists_unit_val_appLE_eq`, and all identities (partition,
unit, cocycle) descend FOR FREE because every comparison map is injective over the
field `k` (`relSectionsMap_injective` on the ambients,
`injective_appLE_of_eq_basicOpen` on the basic-open overlaps).

**Consequences (stage iii)** and the seams:

* **the classes correspond under `CechPic.map`**
  (`BasicOpenCocycleDatum.descent_cechPicClass`): the stage (1e) naturality
  `cechPicClass_baseChange` rewritten along the certificate `D₀.baseChange B = D`;
* the engine output transports to `B` through the landed ABSTRACT ring-map clause
  `datumH0BaseChangeEquiv D₀ hH1 B : B ⊗[B₀] H⁰(D₀) ≃ₗ[B] ker(δ_{D₀} ⊗ B)`
  (`GluedSheafEngine.lean`); the componentwise transport interface is the (1d-ii)
  `BasicOpenCocycleDatum.sectionsMap` kit — threading the kernel onto
  `H⁰((D₀.baseChange B).sheaf) = H⁰(D.sheaf)` ON THE NOSE is the remaining (1d-ii)
  clause (`datumH0BaseChange`), still with the DAT-1 lane (the one open SEAM).

**Consumer** (worksheet §2.3, V-rel-B step 2, DAT-B only): extract a datum from an
arbitrary `CechPic` class by the stage-(1f) keystone `exists_cechPicClass_eq`, apply
`exists_fg_isNoetherianRing_baseChange_eq` to it verbatim, fire
`datumRigidEngine`/`descentRigidEngine` over `B₀` (hypotheses from FLV + DAT-4 at the
stage's fibres), and transport along `B₀ → B` by `datumH0BaseChangeEquiv`,
`descent_cechPicClass` and the certificate.
-/

set_option autoImplicit false
/- The statements mix `Γ(relCurve C B, ·)` with the `relCover`/`pullbackProd` chart
spellings (definitionally equal through semireducible definitions), as in
`GluedSheafDatum.lean`. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {π : C.left ⟶ P1 k}

/-! ## Constructor congruence for the cover data -/

/-- (Implementation) **The subst-safe endgame of the descent**: over fully destructured
components, a stage datum whose generators, coefficients and units map to the given
ones has base change equal to the given datum. Stated over plain variables so that the
component certificates can be substituted; the descent theorem calls it through the
definitional transparency of its `let`-bound stage. -/
private theorem baseChange_eq_of_certs [IsAffineHom π] {J₀ J₁ : Type u}
    (ft₀ : Fintype J₀) (ft₁ : Fintype J₁)
    {B₀ : Type u} [CommRing B₀] [Algebra k B₀] [Algebra B₀ B] [IsScalarTower k B₀ B]
    (h₀' a₀' : J₀ → Γ(relCurve C B₀, (relCover C B₀ (fiberTwoCover π)).V₀))
    (h₁' a₁' : J₁ → Γ(relCurve C B₀, (relCover C B₀ (fiberTwoCover π)).V₁))
    (q₀ : ∑ j ∈ @Finset.univ J₀ ft₀, a₀' j * h₀' j = 1)
    (q₁ : ∑ j ∈ @Finset.univ J₁ ft₁, a₁' j * h₁' j = 1)
    (h₀c a₀c : J₀ → Γ(relCurve C B, (relCover C B (fiberTwoCover π)).V₀))
    (h₁c a₁c : J₁ → Γ(relCurve C B, (relCover C B (fiberTwoCover π)).V₁))
    (p₀ : ∑ j ∈ @Finset.univ J₀ ft₀, a₀c j * h₀c j = 1)
    (p₁ : ∑ j ∈ @Finset.univ J₁ ft₁, a₁c j * h₁c j = 1)
    (unit : ∀ i j : (⟨J₀, J₁, ft₀, ft₁, h₀c, h₁c, a₀c, a₁c, p₀, p₁⟩ :
        BasicOpenCoverData C B π).index,
      Γ(relCurve C B, (⟨J₀, J₁, ft₀, ft₁, h₀c, h₁c, a₀c, a₁c, p₀, p₁⟩ :
          BasicOpenCoverData C B π).pieces i ⊓
        (⟨J₀, J₁, ft₀, ft₁, h₀c, h₁c, a₀c, a₁c, p₀, p₁⟩ :
          BasicOpenCoverData C B π).pieces j)ˣ)
    (coc : Scheme.IsGluingCocycle
      (⟨J₀, J₁, ft₀, ft₁, h₀c, h₁c, a₀c, a₁c, p₀, p₁⟩ :
        BasicOpenCoverData C B π).pieces unit)
    (û : ∀ i j : (⟨J₀, J₁, ft₀, ft₁, h₀', h₁', a₀', a₁', q₀, q₁⟩ :
        BasicOpenCoverData C B₀ π).index,
      Γ(relCurve C B₀, (⟨J₀, J₁, ft₀, ft₁, h₀', h₁', a₀', a₁', q₀, q₁⟩ :
          BasicOpenCoverData C B₀ π).pieces i ⊓
        (⟨J₀, J₁, ft₀, ft₁, h₀', h₁', a₀', a₁', q₀, q₁⟩ :
          BasicOpenCoverData C B₀ π).pieces j)ˣ)
    (hcoc₀ : Scheme.IsGluingCocycle
      (⟨J₀, J₁, ft₀, ft₁, h₀', h₁', a₀', a₁', q₀, q₁⟩ :
        BasicOpenCoverData C B₀ π).pieces û)
    (hh₀ : ∀ j : J₀, relSectionsMap C B₀ B (fiberTwoCover π).V₀ (h₀' j) = h₀c j)
    (ha₀ : ∀ j : J₀, relSectionsMap C B₀ B (fiberTwoCover π).V₀ (a₀' j) = a₀c j)
    (hh₁ : ∀ j : J₁, relSectionsMap C B₀ B (fiberTwoCover π).V₁ (h₁' j) = h₁c j)
    (ha₁ : ∀ j : J₁, relSectionsMap C B₀ B (fiberTwoCover π).V₁ (a₁' j) = a₁c j)
    (hleO : ∀ i j : (⟨J₀, J₁, ft₀, ft₁, h₀c, h₁c, a₀c, a₁c, p₀, p₁⟩ :
        BasicOpenCoverData C B π).index,
      (⟨J₀, J₁, ft₀, ft₁, h₀c, h₁c, a₀c, a₁c, p₀, p₁⟩ :
          BasicOpenCoverData C B π).pieces i ⊓
        (⟨J₀, J₁, ft₀, ft₁, h₀c, h₁c, a₀c, a₁c, p₀, p₁⟩ :
          BasicOpenCoverData C B π).pieces j ≤
      relCurveMap C B₀ B ⁻¹ᵁ
        ((⟨J₀, J₁, ft₀, ft₁, h₀', h₁', a₀', a₁', q₀, q₁⟩ :
            BasicOpenCoverData C B₀ π).pieces i ⊓
          (⟨J₀, J₁, ft₀, ft₁, h₀', h₁', a₀', a₁', q₀, q₁⟩ :
            BasicOpenCoverData C B₀ π).pieces j))
    (hcert : ∀ i j, ((relCurveMap C B₀ B).appLE _ _ (hleO i j)).hom
        ((û i j : Γ(relCurve C B₀, _))) =
      ((unit i j : Γ(relCurve C B, _)))) :
    BasicOpenCocycleDatum.baseChange (B' := B)
        (⟨⟨J₀, J₁, ft₀, ft₁, h₀', h₁', a₀', a₁', q₀, q₁⟩, û, hcoc₀⟩ :
          BasicOpenCocycleDatum C B₀ π) =
      ⟨⟨J₀, J₁, ft₀, ft₁, h₀c, h₁c, a₀c, a₁c, p₀, p₁⟩, unit, coc⟩ := by
  have hfun₀ : (fun j : J₀ =>
      relSectionsMap C B₀ B (fiberTwoCover π).V₀ (h₀' j)) = h₀c := funext hh₀
  have hfuna₀ : (fun j : J₀ =>
      relSectionsMap C B₀ B (fiberTwoCover π).V₀ (a₀' j)) = a₀c := funext ha₀
  have hfun₁ : (fun j : J₁ =>
      relSectionsMap C B₀ B (fiberTwoCover π).V₁ (h₁' j)) = h₁c := funext hh₁
  have hfuna₁ : (fun j : J₁ =>
      relSectionsMap C B₀ B (fiberTwoCover π).V₁ (a₁' j)) = a₁c := funext ha₁
  subst hfun₀ hfuna₀ hfun₁ hfuna₁
  exact BasicOpenCocycleDatum.ext_units fun i j => Units.ext (hcert i j)

/-! ## The RE-5 keystone -/

set_option maxHeartbeats 1600000 in
-- The proof crosses the `relCover`/product/`chartAt` spellings through semireducible
-- definitions many times (the standing heartbeat pattern of the DAT-1 lane).
/-- **RE-5 (worksheet §3.2): presentation descent of the pinned cocycle datum.** A
cocycle datum over an arbitrary commutative `k`-algebra `B` descends to a finitely
generated `k`-subalgebra `B₀ ⊆ B`: there is a datum over `B₀` whose base change along
`B₀ → B` **is** the given datum. -/
theorem BasicOpenCocycleDatum.exists_fg_subalgebra_baseChange_eq [IsAffineHom π]
    (D : BasicOpenCocycleDatum C B π) :
    ∃ B₀ : Subalgebra k B, B₀.FG ∧
      ∃ D₀ : BasicOpenCocycleDatum C (↥B₀) π, D₀.baseChange (B' := B) = D := by
  classical
  obtain ⟨⟨J₀, J₁, ft₀, ft₁, h₀c, h₁c, a₀c, a₁c, p₀, p₁⟩, unit, coc⟩ := D
  letI := ft₀
  letI := ft₁
  -- the cover datum of the destructured input, as a term
  let covB : BasicOpenCoverData C B π :=
    ⟨J₀, J₁, ft₀, ft₁, h₀c, h₁c, a₀c, a₁c, p₀, p₁⟩
  -- ambient affineness facts, typed at the relative curve
  have hV₀ := (fiberTwoCover π).isAffineOpen₀
  have hV₁ := (fiberTwoCover π).isAffineOpen₁
  have hWaff : ∀ i j : covB.index, IsAffineOpen (covB.chartAt i ⊓ covB.chartAt j) :=
    covB.isAffineOpen_chartAt_inf
  have hW₃aff : ∀ i j l : covB.index,
      IsAffineOpen (covB.chartAt i ⊓ covB.chartAt j ⊓ covB.chartAt l) :=
    covB.isAffineOpen_chartAt_inf₃
  have hUaffB : ∀ i j : covB.index, IsAffineOpen
      ((fst C (overSpec k B)).left ⁻¹ᵁ (covB.chartAt i ⊓ covB.chartAt j) :
        (relCurve C B).Opens) := fun i j => (hWaff i j).preimage _
  have hU₃affB : ∀ i j l : covB.index, IsAffineOpen
      ((fst C (overSpec k B)).left ⁻¹ᵁ
          (covB.chartAt i ⊓ covB.chartAt j ⊓ covB.chartAt l) :
        (relCurve C B).Opens) := fun i j l => (hW₃aff i j l).preimage _
  -- the piece overlaps under their affine ambients
  have hPle : ∀ i j : covB.index, covB.pieces i ⊓ covB.pieces j ≤
      (fst C (overSpec k B)).left ⁻¹ᵁ (covB.chartAt i ⊓ covB.chartAt j) := fun i j =>
    (covB.pieces_inf_eq_basicOpen_sigmaAt i j).le.trans (Scheme.basicOpen_le _ _)
  -- (1) clear the unit denominators into the affine chart-overlap ambients over `B`
  have hclear : ∀ i j : covB.index,
      ∃ (uB vB : Γ(relCurve C B,
          (fst C (overSpec k B)).left ⁻¹ᵁ (covB.chartAt i ⊓ covB.chartAt j)))
        (N N' e : ℕ),
        (relCurve C B).resHom (hPle i j) (covB.sigmaAt i j) ^ N *
            ((unit i j : Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j))) =
          (relCurve C B).resHom (hPle i j) uB ∧
        (relCurve C B).resHom (hPle i j) (covB.sigmaAt i j) ^ N' *
            (((unit i j)⁻¹ : Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j)ˣ) :
              Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j)) =
          (relCurve C B).resHom (hPle i j) vB ∧
        uB * vB * covB.sigmaAt i j ^ e = covB.sigmaAt i j ^ (e + N + N') := by
    intro i j
    obtain ⟨uB, N, hu⟩ := (hUaffB i j).exists_pow_mul_eq_resHom (covB.sigmaAt i j)
      (covB.pieces_inf_eq_basicOpen_sigmaAt i j) (hPle i j)
      ((unit i j : Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j)))
    obtain ⟨vB, N', hv⟩ := (hUaffB i j).exists_pow_mul_eq_resHom (covB.sigmaAt i j)
      (covB.pieces_inf_eq_basicOpen_sigmaAt i j) (hPle i j)
      ((((unit i j)⁻¹ : Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j)ˣ) :
        Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j)))
    have hzero : (relCurve C B).resHom (hPle i j)
        (uB * vB - covB.sigmaAt i j ^ (N + N')) = 0 := by
      have hgg : ((unit i j : Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j))) *
          (((unit i j)⁻¹ : Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j)ˣ) :
            Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j)) = 1 :=
        (unit i j).mul_inv
      have hexp : (relCurve C B).resHom (hPle i j) (covB.sigmaAt i j) ^ N *
            ((unit i j : Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j))) *
            ((relCurve C B).resHom (hPle i j) (covB.sigmaAt i j) ^ N' *
              (((unit i j)⁻¹ : Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j)ˣ) :
                Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j))) =
          (relCurve C B).resHom (hPle i j) (covB.sigmaAt i j) ^ (N + N') *
            (((unit i j : Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j))) *
              (((unit i j)⁻¹ : Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j)ˣ) :
                Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j))) := by
        rw [pow_add]
        ring
      rw [map_sub, map_mul, ← hu, ← hv, map_pow, hexp, hgg, mul_one, sub_self]
    obtain ⟨e, he⟩ := (hUaffB i j).exists_pow_mul_eq_zero_of_resHom_eq_zero
      (covB.sigmaAt i j) (covB.pieces_inf_eq_basicOpen_sigmaAt i j) (hPle i j) _ hzero
    refine ⟨uB, vB, N, N', e, hu, hv, ?_⟩
    calc uB * vB * covB.sigmaAt i j ^ e
        = covB.sigmaAt i j ^ e * (uB * vB - covB.sigmaAt i j ^ (N + N')) +
            covB.sigmaAt i j ^ e * covB.sigmaAt i j ^ (N + N') := by ring
      _ = covB.sigmaAt i j ^ (e + N + N') := by
          rw [he, zero_add, ← pow_add, add_assoc]
  choose uB vB Nu Nv Ne hu hv hE3 using hclear
  -- (2) the descent finsets of all datum elements
  choose sh₀ hsh₀ using fun j : J₀ =>
    exists_finset_forall_mem_range_relSectionsMap hV₀.isCompact hV₀.isQuasiSeparated
      (h₀c j)
  choose sh₁ hsh₁ using fun j : J₁ =>
    exists_finset_forall_mem_range_relSectionsMap hV₁.isCompact hV₁.isQuasiSeparated
      (h₁c j)
  choose sa₀ hsa₀ using fun j : J₀ =>
    exists_finset_forall_mem_range_relSectionsMap hV₀.isCompact hV₀.isQuasiSeparated
      (a₀c j)
  choose sa₁ hsa₁ using fun j : J₁ =>
    exists_finset_forall_mem_range_relSectionsMap hV₁.isCompact hV₁.isQuasiSeparated
      (a₁c j)
  choose su hsu using fun i j : covB.index =>
    exists_finset_forall_mem_range_relSectionsMap (hWaff i j).isCompact
      (hWaff i j).isQuasiSeparated (uB i j)
  choose sv hsv using fun i j : covB.index =>
    exists_finset_forall_mem_range_relSectionsMap (hWaff i j).isCompact
      (hWaff i j).isQuasiSeparated (vB i j)
  -- (3) the finitely generated stage
  let s : Finset B :=
    (((Finset.univ : Finset J₀).biUnion fun j => sh₀ j ∪ sa₀ j) ∪
      ((Finset.univ : Finset J₁).biUnion fun j => sh₁ j ∪ sa₁ j)) ∪
      ((Finset.univ : Finset (covB.index × covB.index)).biUnion fun p =>
        su p.1 p.2 ∪ sv p.1 p.2)
  refine ⟨Algebra.adjoin k (s : Set B), Subalgebra.fg_adjoin_finset s, ?_⟩
  let B₀ : Subalgebra k B := Algebra.adjoin k (s : Set B)
  have hmem : ∀ t : Finset B, t ⊆ s → (t : Set B) ⊆ (B₀ : Set B) := fun t hts x hx =>
    Algebra.subset_adjoin (hts hx)
  -- (4) descend the datum elements to the stage
  choose h₀' hh₀ using fun j : J₀ => hsh₀ j B₀ (hmem _
    ((Finset.subset_union_left.trans
      (Finset.subset_biUnion_of_mem (fun j : J₀ => sh₀ j ∪ sa₀ j)
        (Finset.mem_univ j))).trans
      (Finset.subset_union_left.trans Finset.subset_union_left)))
  choose a₀' ha₀ using fun j : J₀ => hsa₀ j B₀ (hmem _
    ((Finset.subset_union_right.trans
      (Finset.subset_biUnion_of_mem (fun j : J₀ => sh₀ j ∪ sa₀ j)
        (Finset.mem_univ j))).trans
      (Finset.subset_union_left.trans Finset.subset_union_left)))
  choose h₁' hh₁ using fun j : J₁ => hsh₁ j B₀ (hmem _
    ((Finset.subset_union_left.trans
      (Finset.subset_biUnion_of_mem (fun j : J₁ => sh₁ j ∪ sa₁ j)
        (Finset.mem_univ j))).trans
      (Finset.subset_union_right.trans Finset.subset_union_left)))
  choose a₁' ha₁ using fun j : J₁ => hsa₁ j B₀ (hmem _
    ((Finset.subset_union_right.trans
      (Finset.subset_biUnion_of_mem (fun j : J₁ => sh₁ j ∪ sa₁ j)
        (Finset.mem_univ j))).trans
      (Finset.subset_union_right.trans Finset.subset_union_left)))
  choose u' hu' using fun i j : covB.index => hsu i j B₀ (hmem _
    ((Finset.subset_union_left.trans
      (Finset.subset_biUnion_of_mem
        (fun p : covB.index × covB.index => su p.1 p.2 ∪ sv p.1 p.2)
        (Finset.mem_univ (i, j)))).trans Finset.subset_union_right))
  choose v' hv' using fun i j : covB.index => hsv i j B₀ (hmem _
    ((Finset.subset_union_right.trans
      (Finset.subset_biUnion_of_mem
        (fun p : covB.index × covB.index => su p.1 p.2 ∪ sv p.1 p.2)
        (Finset.mem_univ (i, j)))).trans Finset.subset_union_right))
  -- (5) injectivity of the stage comparison on qcqs opens
  have halg : Function.Injective (algebraMap (↥B₀) B) := fun a b hab => Subtype.ext hab
  have hmapinj : ∀ V : C.left.Opens, IsCompact (V : Set C.left) →
      IsQuasiSeparated (V : Set C.left) →
      Function.Injective (relSectionsMap C (↥B₀) B V) := fun V hc hq =>
    relSectionsMap_injective C (↥B₀) B halg hc hq
  -- (6) the descended cover datum
  have hpart₀' : ∑ j : J₀, a₀' j * h₀' j = 1 := by
    apply hmapinj (fiberTwoCover π).V₀ hV₀.isCompact hV₀.isQuasiSeparated
    rw [map_sum, map_one]
    calc ∑ j : J₀, relSectionsMap C (↥B₀) B (fiberTwoCover π).V₀ (a₀' j * h₀' j)
        = ∑ j : J₀, a₀c j * h₀c j :=
          Finset.sum_congr rfl fun j _ => by rw [map_mul, hh₀ j, ha₀ j]
      _ = 1 := p₀
  have hpart₁' : ∑ j : J₁, a₁' j * h₁' j = 1 := by
    apply hmapinj (fiberTwoCover π).V₁ hV₁.isCompact hV₁.isQuasiSeparated
    rw [map_sum, map_one]
    calc ∑ j : J₁, relSectionsMap C (↥B₀) B (fiberTwoCover π).V₁ (a₁' j * h₁' j)
        = ∑ j : J₁, a₁c j * h₁c j :=
          Finset.sum_congr rfl fun j _ => by rw [map_mul, hh₁ j, ha₁ j]
      _ = 1 := p₁
  let cov₀ : BasicOpenCoverData C (↥B₀) π :=
    ⟨J₀, J₁, ft₀, ft₁, h₀', h₁', a₀', a₁', hpart₀', hpart₁'⟩
  -- the stage overlap generators, retyped at the shared chart spelling
  let σ₀ : ∀ i j : covB.index, Γ(relCurve C (↥B₀),
      (fst C (overSpec k (↥B₀))).left ⁻¹ᵁ (covB.chartAt i ⊓ covB.chartAt j)) :=
    fun i j => cov₀.sigmaAt i j
  let σ₃₀ : ∀ i j l : covB.index, Γ(relCurve C (↥B₀),
      (fst C (overSpec k (↥B₀))).left ⁻¹ᵁ
        (covB.chartAt i ⊓ covB.chartAt j ⊓ covB.chartAt l)) :=
    fun i j l => cov₀.sigma₃At i j l
  -- (7) mapping compatibilities: generators, σ's, and pieces
  have hgen : ∀ i : covB.index,
      relSectionsMap C (↥B₀) B (covB.chartAt i) (cov₀.genAt i) = covB.genAt i := by
    intro i
    cases i with
    | inl j => exact hh₀ j
    | inr j => exact hh₁ j
  have hσ : ∀ i j : covB.index,
      relSectionsMap C (↥B₀) B (covB.chartAt i ⊓ covB.chartAt j) (σ₀ i j) =
        covB.sigmaAt i j := by
    intro i j
    change relSectionsMap C (↥B₀) B (covB.chartAt i ⊓ covB.chartAt j)
        ((relCurve C (↥B₀)).resHom
            (Scheme.Hom.preimage_mono (fst C (overSpec k (↥B₀))).left
              (inf_le_left : covB.chartAt i ⊓ covB.chartAt j ≤ covB.chartAt i))
            (cov₀.genAt i) *
          (relCurve C (↥B₀)).resHom
            (Scheme.Hom.preimage_mono (fst C (overSpec k (↥B₀))).left
              (inf_le_right : covB.chartAt i ⊓ covB.chartAt j ≤ covB.chartAt j))
            (cov₀.genAt j)) = covB.sigmaAt i j
    rw [map_mul,
      relSectionsMap_resHom C (↥B₀) B
        (inf_le_left : covB.chartAt i ⊓ covB.chartAt j ≤ covB.chartAt i)
        (cov₀.genAt i),
      relSectionsMap_resHom C (↥B₀) B
        (inf_le_right : covB.chartAt i ⊓ covB.chartAt j ≤ covB.chartAt j)
        (cov₀.genAt j),
      hgen i, hgen j]
    rfl
  have hσ₃ : ∀ i j l : covB.index,
      relSectionsMap C (↥B₀) B (covB.chartAt i ⊓ covB.chartAt j ⊓ covB.chartAt l)
          (σ₃₀ i j l) = covB.sigma₃At i j l := by
    intro i j l
    change relSectionsMap C (↥B₀) B (covB.chartAt i ⊓ covB.chartAt j ⊓ covB.chartAt l)
        ((relCurve C (↥B₀)).resHom
            (Scheme.Hom.preimage_mono (fst C (overSpec k (↥B₀))).left
              (inf_le_left.trans inf_le_left :
                covB.chartAt i ⊓ covB.chartAt j ⊓ covB.chartAt l ≤ covB.chartAt i))
            (cov₀.genAt i) *
          (relCurve C (↥B₀)).resHom
            (Scheme.Hom.preimage_mono (fst C (overSpec k (↥B₀))).left
              (inf_le_left.trans inf_le_right :
                covB.chartAt i ⊓ covB.chartAt j ⊓ covB.chartAt l ≤ covB.chartAt j))
            (cov₀.genAt j) *
          (relCurve C (↥B₀)).resHom
            (Scheme.Hom.preimage_mono (fst C (overSpec k (↥B₀))).left
              (inf_le_right :
                covB.chartAt i ⊓ covB.chartAt j ⊓ covB.chartAt l ≤ covB.chartAt l))
            (cov₀.genAt l)) = covB.sigma₃At i j l
    rw [map_mul, map_mul,
      relSectionsMap_resHom C (↥B₀) B
        (inf_le_left.trans inf_le_left :
          covB.chartAt i ⊓ covB.chartAt j ⊓ covB.chartAt l ≤ covB.chartAt i)
        (cov₀.genAt i),
      relSectionsMap_resHom C (↥B₀) B
        (inf_le_left.trans inf_le_right :
          covB.chartAt i ⊓ covB.chartAt j ⊓ covB.chartAt l ≤ covB.chartAt j)
        (cov₀.genAt j),
      relSectionsMap_resHom C (↥B₀) B
        (inf_le_right :
          covB.chartAt i ⊓ covB.chartAt j ⊓ covB.chartAt l ≤ covB.chartAt l)
        (cov₀.genAt l),
      hgen i, hgen j, hgen l]
    rfl
  have hpre : ∀ V : C.left.Opens, (fst C (overSpec k B)).left ⁻¹ᵁ V ≤
      relCurveMap C (↥B₀) B ⁻¹ᵁ ((fst C (overSpec k (↥B₀))).left ⁻¹ᵁ V) := fun V =>
    le_of_eq (relCurveMap_preimage C (↥B₀) B V).symm
  have hpieces_pre : ∀ i : covB.index,
      covB.pieces i ≤ relCurveMap C (↥B₀) B ⁻¹ᵁ cov₀.pieces i := by
    intro i
    rw [covB.pieces_eq_basicOpen_genAt i, cov₀.pieces_eq_basicOpen_genAt i, ← hgen i]
    exact (relSectionsMap_basicOpen C (↥B₀) B (covB.chartAt i) (cov₀.genAt i)).le
  have hleO : ∀ i j : covB.index, covB.pieces i ⊓ covB.pieces j ≤
      relCurveMap C (↥B₀) B ⁻¹ᵁ (cov₀.pieces i ⊓ cov₀.pieces j) := by
    intro i j
    rw [Scheme.Hom.preimage_inf]
    exact inf_le_inf (hpieces_pre i) (hpieces_pre j)
  have hleO₃ : ∀ i j l : covB.index,
      covB.pieces i ⊓ covB.pieces j ⊓ covB.pieces l ≤
      relCurveMap C (↥B₀) B ⁻¹ᵁ (cov₀.pieces i ⊓ cov₀.pieces j ⊓ cov₀.pieces l) := by
    intro i j l
    rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf]
    exact inf_le_inf (inf_le_inf (hpieces_pre i) (hpieces_pre j)) (hpieces_pre l)
  -- (8) descend the two-sided certificates to the stage
  have hE3' : ∀ i j : covB.index,
      u' i j * v' i j * σ₀ i j ^ Ne i j = σ₀ i j ^ (Ne i j + Nu i j + Nv i j) := by
    intro i j
    apply hmapinj (covB.chartAt i ⊓ covB.chartAt j) (hWaff i j).isCompact
      (hWaff i j).isQuasiSeparated
    rw [map_mul, map_mul, map_pow, map_pow, hu' i j, hv' i j, hσ i j]
    exact hE3 i j
  -- (9) the descended units
  have hUnits : ∀ i j : covB.index,
      ∃ ĝ : Γ(relCurve C (↥B₀), cov₀.pieces i ⊓ cov₀.pieces j)ˣ,
        ((relCurveMap C (↥B₀) B).appLE (cov₀.pieces i ⊓ cov₀.pieces j)
          (covB.pieces i ⊓ covB.pieces j) (hleO i j)).hom
            (ĝ : Γ(relCurve C (↥B₀), cov₀.pieces i ⊓ cov₀.pieces j)) =
          ((unit i j : Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j))) := by
    intro i j
    refine (relCurveMap C (↥B₀) B).exists_unit_val_appLE_eq
      (hpre (covB.chartAt i ⊓ covB.chartAt j)) (σ₀ i j) (u' i j) (v' i j)
      (Nu i j) (Nv i j) (Ne i j) (hE3' i j)
      (cov₀.pieces_inf_eq_basicOpen_sigmaAt i j)
      ((cov₀.pieces_inf_eq_basicOpen_sigmaAt i j).le.trans (Scheme.basicOpen_le _ _))
      (hPle i j) (hleO i j) (unit i j) ?_
    change (relCurve C B).resHom (hPle i j)
        (relSectionsMap C (↥B₀) B (covB.chartAt i ⊓ covB.chartAt j) (u' i j)) =
      (relCurve C B).resHom (hPle i j)
        (relSectionsMap C (↥B₀) B (covB.chartAt i ⊓ covB.chartAt j)
          (σ₀ i j)) ^ Nu i j *
        ((unit i j : Γ(relCurve C B, covB.pieces i ⊓ covB.pieces j)))
    rw [hu' i j, hσ i j]
    exact (hu i j).symm
  choose û hcert using hUnits
  -- (10) injectivity of the overlap comparisons at the stage
  have hUaff₀ : ∀ i j : covB.index, IsAffineOpen
      ((fst C (overSpec k (↥B₀))).left ⁻¹ᵁ (covB.chartAt i ⊓ covB.chartAt j) :
        (relCurve C (↥B₀)).Opens) := fun i j => (hWaff i j).preimage _
  have hU₃aff₀ : ∀ i j l : covB.index, IsAffineOpen
      ((fst C (overSpec k (↥B₀))).left ⁻¹ᵁ
          (covB.chartAt i ⊓ covB.chartAt j ⊓ covB.chartAt l) :
        (relCurve C (↥B₀)).Opens) := fun i j l => (hW₃aff i j l).preimage _
  have hφinj : ∀ i j : covB.index, Function.Injective
      (((relCurveMap C (↥B₀) B).appLE (cov₀.pieces i ⊓ cov₀.pieces j)
        (covB.pieces i ⊓ covB.pieces j) (hleO i j)).hom) := by
    intro i j
    refine (relCurveMap C (↥B₀) B).injective_appLE_of_eq_basicOpen
      (hUaff₀ i j) (hUaffB i j)
      (hpre (covB.chartAt i ⊓ covB.chartAt j)) ?_ (σ₀ i j)
      (cov₀.pieces_inf_eq_basicOpen_sigmaAt i j) ?_ (hleO i j)
    · exact hmapinj (covB.chartAt i ⊓ covB.chartAt j) (hWaff i j).isCompact
        (hWaff i j).isQuasiSeparated
    · rw [covB.pieces_inf_eq_basicOpen_sigmaAt i j]
      exact congrArg (relCurve C B).basicOpen (hσ i j).symm
  have hφ₃inj : ∀ i j l : covB.index, Function.Injective
      (((relCurveMap C (↥B₀) B).appLE
        (cov₀.pieces i ⊓ cov₀.pieces j ⊓ cov₀.pieces l)
        (covB.pieces i ⊓ covB.pieces j ⊓ covB.pieces l) (hleO₃ i j l)).hom) := by
    intro i j l
    refine (relCurveMap C (↥B₀) B).injective_appLE_of_eq_basicOpen
      (hU₃aff₀ i j l) (hU₃affB i j l)
      (hpre (covB.chartAt i ⊓ covB.chartAt j ⊓ covB.chartAt l)) ?_
      (σ₃₀ i j l) (cov₀.pieces_inf₃_eq_basicOpen_sigma₃At i j l) ?_
      (hleO₃ i j l)
    · exact hmapinj (covB.chartAt i ⊓ covB.chartAt j ⊓ covB.chartAt l)
        (hW₃aff i j l).isCompact (hW₃aff i j l).isQuasiSeparated
    · rw [covB.pieces_inf₃_eq_basicOpen_sigma₃At i j l]
      exact congrArg (relCurve C B).basicOpen (hσ₃ i j l).symm
  -- (11) the cocycle law at the stage, by injectivity
  have hcoc₀ : Scheme.IsGluingCocycle cov₀.pieces û := by
    constructor
    · intro i
      apply hφinj i i
      rw [hcert i i, map_one]
      exact coc.unit_self i
    · intro i j l
      apply hφ₃inj i j l
      rw [map_mul]
      have e₁ := ((relCurveMap C (↥B₀) B).appLE_resHom
        (inf_le_left : cov₀.pieces i ⊓ cov₀.pieces j ⊓ cov₀.pieces l ≤
          cov₀.pieces i ⊓ cov₀.pieces j)
        (hleO i j) (hleO₃ i j l)
        (inf_le_left : covB.pieces i ⊓ covB.pieces j ⊓ covB.pieces l ≤
          covB.pieces i ⊓ covB.pieces j)
        ((û i j : Γ(relCurve C (↥B₀), cov₀.pieces i ⊓ cov₀.pieces j)))).symm
      have e₂ := ((relCurveMap C (↥B₀) B).appLE_resHom
        (gluedInclCoc cov₀.pieces (cov₀.pieces i) j l) (hleO j l) (hleO₃ i j l)
        (gluedInclCoc covB.pieces (covB.pieces i) j l)
        ((û j l : Γ(relCurve C (↥B₀), cov₀.pieces j ⊓ cov₀.pieces l)))).symm
      have e₃ := ((relCurveMap C (↥B₀) B).appLE_resHom
        (gluedInclSnd cov₀.pieces (cov₀.pieces i) j l) (hleO i l) (hleO₃ i j l)
        (gluedInclSnd covB.pieces (covB.pieces i) j l)
        ((û i l : Γ(relCurve C (↥B₀), cov₀.pieces i ⊓ cov₀.pieces l)))).symm
      rw [e₁, e₂, e₃, hcert i j, hcert j l, hcert i l]
      exact coc.mul_res i j l
  -- (12) assembly and the base-change certificate (the subst-safe endgame lemma)
  exact ⟨⟨cov₀, û, hcoc₀⟩,
    baseChange_eq_of_certs ft₀ ft₁ h₀' a₀' h₁' a₁' hpart₀' hpart₁'
      h₀c a₀c h₁c a₁c p₀ p₁ unit coc û hcoc₀ hh₀ ha₀ hh₁ ha₁ hleO hcert⟩

/-! ## Stage (iii): the engine over the descent stage -/

/-- A finitely generated subalgebra of a commutative algebra over a field is a
Noetherian ring (Hilbert basis through `Algebra.FiniteType`). -/
theorem _root_.Subalgebra.FG.isNoetherianRing {B₀ : Subalgebra k B} (hfg : B₀.FG) :
    IsNoetherianRing (↥B₀) := by
  haveI : Algebra.FiniteType k (↥B₀) := (Subalgebra.fg_iff_finiteType B₀).mp hfg
  exact Algebra.FiniteType.isNoetherianRing k (↥B₀)

/-- **RE-5, engine-ready form** (the DAT-B keystone; worksheet §2.3 step 2): a cocycle
datum over an arbitrary commutative `k`-algebra `B` descends to a finitely generated —
hence **Noetherian** — subalgebra stage `B₀ ⊆ B`, with the base-change certificate.
`datumRigidEngine` fires over the stage verbatim; its output transports along `B₀ → B`
through `datumH0BaseChangeEquiv` and the certificate. -/
theorem BasicOpenCocycleDatum.exists_fg_isNoetherianRing_baseChange_eq [IsAffineHom π]
    (D : BasicOpenCocycleDatum C B π) :
    ∃ B₀ : Subalgebra k B, B₀.FG ∧ IsNoetherianRing (↥B₀) ∧
      ∃ D₀ : BasicOpenCocycleDatum C (↥B₀) π, D₀.baseChange (B' := B) = D := by
  obtain ⟨B₀, hfg, D₀, hbc⟩ := D.exists_fg_subalgebra_baseChange_eq
  exact ⟨B₀, hfg, hfg.isNoetherianRing, D₀, hbc⟩

/-- **The classes correspond under `CechPic.map`** (worksheet §3.2, the "consequently"
half): for a descended datum, the class of the given datum on `C_B` is the pullback of
the stage class along the relative-curve comparison — the stage-(1e) naturality
rewritten along the descent certificate. -/
theorem BasicOpenCocycleDatum.descent_cechPicClass [IsAffineHom π]
    {B₀ : Subalgebra k B} {D₀ : BasicOpenCocycleDatum C (↥B₀) π}
    {D : BasicOpenCocycleDatum C B π} (hbc : D₀.baseChange (B' := B) = D) :
    D.cechPicClass = Scheme.CechPic.map (relCurveMap C (↥B₀) B) D₀.cechPicClass := by
  rw [← hbc]
  exact D₀.cechPicClass_baseChange B

set_option synthInstance.maxHeartbeats 400000 in
-- The sheaf-of-modules instances over the subalgebra stage exceed the default
-- synthesis budget (the standing pattern of the engine files).
/-- **The rigid engine over a descent stage** (stage-(iii) wrapper): for a datum over a
finitely generated stage `B₀ ⊆ B` — e.g. one produced by
`exists_fg_isNoetherianRing_baseChange_eq` — the Noetherian hypothesis of
`datumRigidEngine` is automatic: fibrewise vanishing of `H¹` of the stage pair gives
`H¹(C_{B₀}, F) = 0` and `H⁰(C_{B₀}, F)` finite projective over `B₀`.

Transport to `B`: with `hH1 := (datum_subsingleton_pairH1 D₀ hπ hfib)`, the abstract
ring-map clause `datumH0BaseChangeEquiv D₀ hH1 B` identifies `B ⊗[B₀] H⁰(D₀.sheaf)`
with the kernel of the base-changed Čech differential of the stage pair, and the
certificate `D₀.baseChange B = D` rewrites every statement about `D` into one about
`D₀.baseChange B`. Threading the kernel onto `H⁰(D.sheaf)` on the nose is DAT-1 stage
(1d-ii) — the recorded seam. -/
theorem BasicOpenCocycleDatum.descentRigidEngine [IsFinite π]
    {B₀ : Subalgebra k B} (hfg : B₀.FG) (D₀ : BasicOpenCocycleDatum C (↥B₀) π)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hfib : ∀ p : PrimeSpectrum (↥B₀),
      Subsingleton ((datumPair D₀).H1 ⊗[↥B₀] p.asIdeal.ResidueField)) :
    Subsingleton (Sheaf.HModule D₀.sheaf 1) ∧
      Module.Finite (↥B₀) (Sheaf.HModule D₀.sheaf 0) ∧
      Module.Projective (↥B₀) (Sheaf.HModule D₀.sheaf 0) := by
  haveI : IsNoetherianRing (↥B₀) := hfg.isNoetherianRing
  exact datumRigidEngine D₀ hπ hfib

end AlgebraicGeometry
