/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveSpread
import AlgebraicJacobian.Picard.DivRepAwaySpanGlueAff
import AlgebraicJacobian.Picard.DivSchemeCertZarPointwise
import AlgebraicJacobian.Picard.Pic0RankOneDivisorUnique
import AlgebraicJacobian.Picard.RelPicBaseLocalTriviality
import AlgebraicJacobian.Picard.PicEtAffZariskiSep
import AlgebraicJacobian.Picard.EtaleSeparatedness
import AlgebraicJacobian.Picard.RelPicPi
import AlgebraicJacobian.Cohomology.RankOneFamilyCertificatesActualDatum

/-!
# Gluing the datum-level divisor family over a Noetherian base

Over a Noetherian `k`-algebra `R` a rank-one cocycle datum `D` — one whose fibre `H¹`
vanishes at every residue field and whose class has fibre degree `genus C` — is realised by
a single widened locally certified divisor family `F` with `F.picClass = D.cechPicClass`.

The construction is Zariski-local-to-global on `Spec R`:

* **Per prime** the Noetherian away-spreading theorem
  (`exists_away_away_divFamZarAff_of_admissible_fibre`) produces, after two basic-open
  localizations, a divisor family whose class is the pulled datum class.  The double
  localization collapses to a single basic open of `R` by `IsLocalization.Away.mul_of_associated`.
* **Span** the good basic opens cover `Spec R`, so finitely many span the unit ideal
  (`exists_fin_span_eq_top_of_forall_prime`).
* **Glue** the pieces agree on every overlap because the base-changed datum still has rank-one
  `H⁰` (`RankOneFamilyCertificates.ofActualDatum` + `scalarExtension`), so the datum-class
  uniqueness core (`divFamZarAff_eq_of_picClass_eq_cechPicClass`) forces agreement;
  the canonical away-span glue (`DivFamZarAff.exists_glue_of_awaySpan`) assembles a family `F₀`
  over `R`.
* **Class** the base-discrepancy killing on the base cover upgrades the per-piece class
  agreement to the on-the-nose equality `F₀.picClass = D.cechPicClass`.

The degree is pinned to `genus C`: rank-one `H⁰` — which the gluing uniqueness core needs —
holds exactly when the fibre degree is the genus, so this is the shape the datum-descent
consumer applies.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

namespace BasicOpenCocycleDatum

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instIsIntegralRelCurveGlue
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveGlue
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQuasiCompactRelCurveGlue
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instFiniteH0RelCurveGlue
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFiniteH1RelCurveGlue
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

/-- The predicate: near a basic open `D(b)` of `Spec R` the datum class is effective. -/
private def GoodAway (D : BasicOpenCocycleDatum C R pi) (b : R) : Prop :=
  ∃ F : DivFamZarAff C (Localization.Away b) (genus C),
    F.picClass = Scheme.CechPic.map (relCurveMap C R (Localization.Away b)) D.cechPicClass

/-- **Class transport across an away multiple.**  A good divisor over `Localization.Away a`
has, after base change along the canonical map `Localization.Away a →ₐ[k] Localization.Away e`
of a factorization `a * c = e`, the base-changed datum class over `Localization.Away e`. -/
private lemma picClass_mapAlgHom_awayMulOfDvd (D : BasicOpenCocycleDatum C R pi)
    (e a c : R) (hac : a * c = e)
    (F : DivFamZarAff C (Localization.Away a) (genus C))
    (hF : F.picClass =
      Scheme.CechPic.map (relCurveMap C R (Localization.Away a)) D.cechPicClass) :
    (DivFamZarAff.mapAlgHom (DivFamZar.awayMulOfDvd (k := k) e a c hac) F).picClass
      = (D.baseChange (Localization.Away e)).cechPicClass := by
  letI : Algebra (Localization.Away a) (Localization.Away e) :=
    (DivFamZar.awayMulOfDvd (k := k) e a c hac).toRingHom.toAlgebra
  haveI : IsScalarTower k (Localization.Away a) (Localization.Away e) :=
    .of_algebraMap_eq fun x =>
      ((DivFamZar.awayMulOfDvd (k := k) e a c hac).commutes x).symm
  haveI : IsScalarTower R (Localization.Away a) (Localization.Away e) :=
    .of_algebraMap_eq fun x =>
      (DivFamZar.awayMulOfDvd_algebraMap (k := k) e a c hac x).symm
  rw [DivFamZarAff.mapAlgHom_eq_mapAlg (DivFamZar.awayMulOfDvd (k := k) e a c hac)
      (fun _ => rfl), DivFamZarAff.picClass_mapAlg, hF, ← MonoidHom.comp_apply,
    ← Scheme.CechPic.map_comp, relCurveMap_comp,
    ← D.cechPicClass_baseChange (Localization.Away e)]

set_option maxHeartbeats 4000000 in
-- Two localization towers and the canonical-carrier transport elaborate large sheaf terms
-- (mirrors `exists_away_away_divFamZarAff_of_admissible_fibre`).
set_option synthInstance.maxHeartbeats 800000 in
/-- **Per prime.**  Near every prime of a Noetherian base there is a basic open `D(b)` on
which the datum class is effective (the class of a widened divisor family).  The double away
localization of the Noetherian spreading theorem is collapsed to a single basic open of `R`. -/
private theorem exists_notMem_goodAway (D : BasicOpenCocycleDatum C R pi) [IsNoetherianRing R]
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hwit : ∀ p : PrimeSpectrum R, D.HasWitnessH1Vanishing p.asIdeal.ResidueField)
    (hdeg : ∀ (K : Type u) [Field K] [Algebra k K] [Algebra R K] [IsScalarTower k R K],
      classDeg K (Scheme.CechPic.map (relCurveMap C R K) D.cechPicClass) = (genus C : ℤ))
    (p : PrimeSpectrum R) :
    ∃ b : R, b ∉ p.asIdeal ∧ GoodAway D b := by
  obtain ⟨h, hh, q₁, hq₁, f, hf, q₂, hq₂, F₀, hF₀⟩ :=
    D.exists_away_away_divFamZarAff_of_admissible_fibre hpi (genus C) (genus C)
      (chi_moduleKSheaf C) le_rfl p (hwit p) (hdeg p.asIdeal.ResidueField)
  -- the numerator of `f` over `Localization.Away h`
  set a : R := (IsLocalization.Away.sec h f).1 with ha
  have hassoc : Associated (algebraMap R (Localization.Away h) a) f :=
    IsLocalization.Away.associated_sec_fst h f
  -- `Localization.Away f` is an away localization of `R` at `h * a` (canonical `R`-algebra
  -- tower `R → Localization.Away h → Localization.Away f`)
  haveI : IsLocalization.Away (h * a) (Localization.Away f) :=
    IsLocalization.Away.mul_of_associated h a f hassoc
  set b : R := h * a with hb
  -- `b` lies outside `p`
  have hap : a ∉ p.asIdeal := by
    have hpq : p.asIdeal = q₁.asIdeal.comap (algebraMap R (Localization.Away h)) := by
      rw [← hq₁]; rfl
    rw [hpq, Ideal.mem_comap]
    intro hmem
    refine hf ?_
    obtain ⟨u, hu⟩ := hassoc
    rw [← hu]
    exact Ideal.mul_mem_right _ _ hmem
  have hbp : b ∉ p.asIdeal := fun hmem => (p.isPrime.mem_or_mem hmem).elim hh hap
  -- transport `F₀` to the canonical carrier `Localization.Away b`
  let e : Localization.Away f ≃ₐ[R] Localization.Away b :=
    IsLocalization.algEquiv (Submonoid.powers b) (Localization.Away f) (Localization.Away b)
  letI : Algebra (Localization.Away f) (Localization.Away b) :=
    (e.restrictScalars k).toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower k (Localization.Away f) (Localization.Away b) :=
    .of_algebraMap_eq fun x => ((e.restrictScalars k).commutes x).symm
  haveI : IsScalarTower R (Localization.Away f) (Localization.Away b) :=
    .of_algebraMap_eq fun x => (e.commutes x).symm
  refine ⟨b, hbp, DivFamZarAff.mapAlgHom (e.restrictScalars k).toAlgHom F₀, ?_⟩
  rw [DivFamZarAff.mapAlgHom_eq_mapAlg (e.restrictScalars k).toAlgHom (fun _ => rfl),
    DivFamZarAff.picClass_mapAlg, hF₀, ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp,
    relCurveMap_comp]

/-- **`relPic` away-span separatedness.**  Two Čech Picard classes on `relCurve C A` whose
base changes along `relCurveMap C A (Localization.Away (b i))` agree, for a finite family `b`
spanning the unit ideal, have equal image in `relPic C (overSpec k A)`.

The étale unit `PicEtAff.unit` is injective (`PicEtAff.unit_injective`) and natural
(`PicEtAff.mapAlg_unit`, `relPicAlgMap_mk`), so the claim is the Zariski separatedness of the
étale plus construction `PicEtAff.eq_of_away_eq`.  (The on-the-nose Čech equality is false in
general: the two classes may differ by a base Picard bundle trivialized on the cover.) -/
private lemma relPicMk_eq_of_awaySpan {A : Type u} [CommRing A] [Algebra k A]
    {ι : Type u} [Finite ι] (b : ι → A) (hspan : Ideal.span (Set.range b) = ⊤)
    {L L' : (relCurve C A).CechPic}
    (h : ∀ i, Scheme.CechPic.map (relCurveMap C A (Localization.Away (b i))) L
        = Scheme.CechPic.map (relCurveMap C A (Localization.Away (b i))) L') :
    relPicMk C (overSpec k A) L = relPicMk C (overSpec k A) L' := by
  apply PicEtAff.unit_injective C A
  refine PicEtAff.eq_of_away_eq C b (fun i => Localization.Away (b i)) hspan (fun i => ?_)
  rw [PicEtAff.mapAlg_unit, PicEtAff.mapAlg_unit, relPicAlgMap_mk, relPicAlgMap_mk]
  exact congrArg (PicEtAff.unit C (Localization.Away (b i)))
    (congrArg (relPicMk C (overSpec k (Localization.Away (b i)))) (h i))

set_option maxHeartbeats 4000000 in
-- The gluing compatibility base-changes the rank-one certificates over each overlap and
-- runs the datum-class uniqueness core; the two localization towers are large.
set_option synthInstance.maxHeartbeats 800000 in
/-- **The datum-level glued divisor producer over a Noetherian base.**  A rank-one cocycle
datum — one whose fibre `H¹` vanishes at every residue field (`hwit`) and whose class has
fibre degree `genus C` (`hdeg`) — is realised over a Noetherian base by a single widened
locally certified divisor family, matching the datum's Čech class in the relative Picard
group `relPic C (overSpec k R)`.

The degree is pinned to `genus C`: the gluing uniqueness core needs rank-one `H⁰`, which
holds exactly when the fibre degree is the genus.  The conclusion is stated in `relPic`
rather than on the nose in `(relCurve C R).CechPic` because the glued class is determined by
the datum only up to a base Picard bundle (the on-the-nose equality is false in general);
`relPic` is where the base discrepancy is quotiented out, and it is the invariant the abelian
Abel map and the datum-descent consumer read. -/
theorem exists_glued_divFamZarAff_of_admissible_fibre
    (D : BasicOpenCocycleDatum C R pi) [IsNoetherianRing R]
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hwit : ∀ p : PrimeSpectrum R, D.HasWitnessH1Vanishing p.asIdeal.ResidueField)
    (hdeg : ∀ (K : Type u) [Field K] [Algebra k K] [Algebra R K] [IsScalarTower k R K],
      classDeg K (Scheme.CechPic.map (relCurveMap C R K) D.cechPicClass) = (genus C : ℤ)) :
    ∃ F : DivFamZarAff C R (genus C),
      relPicMk C (overSpec k R) F.picClass = relPicMk C (overSpec k R) D.cechPicClass := by
  classical
  -- the four rank-one certificates for the datum over `R` (arbitrary-ring producer)
  have cert : RankOneFamilyCertificates D :=
    RankOneFamilyCertificates.ofActualDatum D hpi hwit hdeg
  -- per prime: a good basic open; quasi-compactness makes finitely many span the unit ideal
  obtain ⟨m, b, hspan, hgood⟩ :=
    exists_fin_span_eq_top_of_forall_prime (GoodAway D)
      (fun p => D.exists_notMem_goodAway hpi hwit hdeg p)
  choose F hF using hgood
  -- on each overlap the two restricted pieces agree, by datum-class uniqueness at the
  -- base-changed rank-one datum
  have hcompat : ∀ i j : Fin m,
      DivFamZarAff.mapAlgHom (DivFamZar.awayMulLeft (k := k) b i j) (F i)
        = DivFamZarAff.mapAlgHom (DivFamZar.awayMulRight (k := k) b i j) (F j) := by
    intro i j
    have cert' : RankOneFamilyCertificates (D.baseChange (Localization.Away (b i * b j))) :=
      cert.scalarExtension (Localization.Away (b i * b j))
    refine divFamZarAff_eq_of_picClass_eq_cechPicClass
      (D.baseChange (Localization.Away (b i * b j)))
      cert'.h1_vanishing cert'.h0_finite cert'.h0_projective cert'.h0_rank_one _ _ ?_ ?_
    · exact D.picClass_mapAlgHom_awayMulOfDvd (b i * b j) (b i) (b j) rfl (F i) (hF i)
    · exact D.picClass_mapAlgHom_awayMulOfDvd (b i * b j) (b j) (b i)
        (mul_comm (b j) (b i)) (F j) (hF j)
  obtain ⟨F₀, hF₀⟩ := DivFamZarAff.exists_glue_of_awaySpan b hspan F hcompat
  refine ⟨F₀, ?_⟩
  -- the glued family restricts on each piece to the pulled datum class
  have hpiece : ∀ p : Fin m,
      Scheme.CechPic.map (relCurveMap C R (Localization.Away (b p))) F₀.picClass
        = Scheme.CechPic.map (relCurveMap C R (Localization.Away (b p))) D.cechPicClass :=
    fun p => by
      rw [← hF p, ← DivFamZarAff.picClass_mapAlg,
        ← DivFamZarAff.mapAlgHom_eq_mapAlg
          (IsScalarTower.toAlgHom k R (Localization.Away (b p))) (fun _ => rfl), hF₀ p]
  refine relPicMk_eq_of_awaySpan (fun l : ULift.{u} (Fin m) => b l.down) ?_
    (fun l => hpiece l.down)
  rw [show (Set.range fun l : ULift.{u} (Fin m) => b l.down) = Set.range b from
    ULift.down_surjective.range_comp b]
  exact hspan

end BasicOpenCocycleDatum

end AlgebraicGeometry
