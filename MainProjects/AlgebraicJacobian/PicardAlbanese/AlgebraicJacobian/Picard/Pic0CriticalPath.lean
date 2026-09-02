/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAffChallenge
import AlgebraicJacobian.Picard.DivRankOneOpen
import AlgebraicJacobian.Picard.Pic0EndgameContract
import AlgebraicJacobian.Picard.Pic0HighDegreeRouteGuard
import AlgebraicJacobian.Picard.Pic0RankOneLocus
import AlgebraicJacobian.Picard.Pic0RankOneOpenProducer
import AlgebraicJacobian.Picard.Pic0SepClosedRepresentable
import AlgebraicJacobian.Picard.Pic0SepClosedJacobianData
import AlgebraicJacobian.Picard.Pic0RankOneLocalDivisor
import AlgebraicJacobian.Picard.Pic0RankOneEvaluationZeroLocus
import AlgebraicJacobian.Picard.Pic0RankOneFibrePresentedProducerAffineEvaluation
import AlgebraicJacobian.Picard.Pic0RankOneFamilyCertificates
import AlgebraicJacobian.Picard.Pic0RankOneNativePresentation
import AlgebraicJacobian.Picard.Pic0RankOneNativePresentationOfLocal
import AlgebraicJacobian.Picard.Pic0RankOneFibrePresentedProducer
import AlgebraicJacobian.Picard.Pic0RankOneFibrePresentedProducerFiniteGlue
import AlgebraicJacobian.Picard.Pic0RankOneTranslatedCoverPicZero
import AlgebraicJacobian.Picard.Pic0RankOneTranslatedCoverMembership
import AlgebraicJacobian.Picard.RelPicBaseLocalTriviality
import AlgebraicJacobian.Picard.Pic0RankOneCanonicalDivisorDescent
import AlgebraicJacobian.Picard.Pic0RankOneSplitMembership
import AlgebraicJacobian.Picard.Pic0RankOneSectionFibreNonzero
import AlgebraicJacobian.Picard.DivisorDatumSectionOfClass
import AlgebraicJacobian.Picard.Pic0RankOneDivisorUnique
import AlgebraicJacobian.Picard.Pic0RankOneUniquenessDischarge
import AlgebraicJacobian.Picard.Pic0RankOneAbelInverse
import AlgebraicJacobian.Picard.Pic0RankOneCanonicalEvaluation
import AlgebraicJacobian.Picard.Pic0RankOneDatumGluedDivisor
import AlgebraicJacobian.Picard.Pic0RankOneCanonicalDivisorStageCert
import AlgebraicJacobian.Picard.Pic0FiniteGaloisDescent
import AlgebraicJacobian.Picard.Pic0GaloisInvariantComparison
import AlgebraicJacobian.Picard.Pic0FiniteGaloisRepresentable
import AlgebraicJacobian.Picard.Pic0FiniteGaloisJacobianData
import AlgebraicJacobian.Descent.AffineRingGlueData
import AlgebraicJacobian.Descent.OpenImmersionFieldDescent
import AlgebraicJacobian.Descent.OpenImmersionScalarExtension
import AlgebraicJacobian.Descent.IsomorphismFieldTowerDescent
import AlgebraicJacobian.Descent.TensorProductFieldTowerMap
import AlgebraicJacobian.Descent.TensorProductFiniteType
import AlgebraicJacobian.Descent.TensorProductPushoutBaseChange
import AlgebraicJacobian.Picard.TensorFiniteSubextension
import AlgebraicJacobian.Picard.FinitePresentationAlgebraFiniteStage
import AlgebraicJacobian.Picard.FinitePresentationAlgebraMapFiniteStage
import AlgebraicJacobian.Picard.FinitePresentationAlgebraMapTripleReflection
import AlgebraicJacobian.Picard.FinitePresentationAlgebraMapModels
import AlgebraicJacobian.Picard.PicEtFiniteStageCover
import AlgebraicJacobian.Picard.CechPicFiniteStage
import AlgebraicJacobian.Picard.RelPicFiniteStage
import AlgebraicJacobian.Picard.PicEtAffFiniteStage
import AlgebraicJacobian.Picard.Pic0FiniteStageAtlas
import AlgebraicJacobian.Picard.Pic0FiniteStageAffineIntersections
import AlgebraicJacobian.Picard.Pic0FiniteStageOverlapRings
import AlgebraicJacobian.Picard.Pic0FiniteStageRestrictionModels
import AlgebraicJacobian.Picard.Pic0FiniteStageRestrictionOpenImmersions
import AlgebraicJacobian.Picard.Pic0FiniteStageTransitionModels
import AlgebraicJacobian.Picard.Pic0FiniteStageTransitionIdentity
import AlgebraicJacobian.Picard.Pic0FiniteStageDiagonalRestrictions
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleOverlapRings
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleModelScalarExtension
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleModelScalarExtensionFaces
import AlgebraicJacobian.Picard.Pic0FiniteStageTensorPushoutUniversal
import AlgebraicJacobian.Picard.Pic0FiniteStageTensorPushoutComparison
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleModelComparison
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleModelComparisonNamed
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleTransitions
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleTransitionModels
import AlgebraicJacobian.Picard.Pic0FiniteStageTransportedTripleTransitionFace
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleTransitionEquations
import AlgebraicJacobian.Picard.Pic0FiniteStageGluePackage
import AlgebraicJacobian.Picard.Pic0FiniteStageGluedOver
import AlgebraicJacobian.Picard.Pic0FiniteStageFinalBaseChange
import AlgebraicJacobian.Picard.Pic0FiniteStageChartBaseChange
import AlgebraicJacobian.Picard.Pic0FiniteStageAffineBaseChange
import AlgebraicJacobian.Picard.Pic0FiniteStageGluingBaseChange
import AlgebraicJacobian.Picard.Pic0FiniteStageRestrictionBaseChange
import AlgebraicJacobian.Picard.Pic0FiniteStageAffineBaseChangeTrans
import AlgebraicJacobian.Picard.Pic0FiniteStageRestrictionNaturality
import AlgebraicJacobian.Picard.Pic0FiniteStageOverlapBaseChange
import AlgebraicJacobian.Picard.Pic0FiniteStageGluedComparison
import AlgebraicJacobian.Picard.Pic0FiniteStageRightLegEquality
import AlgebraicJacobian.Picard.Pic0FiniteStageRightRestrictionAlgHom
import AlgebraicJacobian.Picard.Pic0FiniteStageRightRestrictionNaturality
import AlgebraicJacobian.Picard.Pic0FiniteStageDatum
import AlgebraicJacobian.Picard.RelPicTensorStageFiniteStage
import AlgebraicJacobian.Picard.Pic0FiniteStageUniversalClass
import AlgebraicJacobian.Picard.Pic0RepresentableColimit
import AlgebraicJacobian.Picard.Pic0RepresentableByTransport

/-!
# Narrow root for the AJCR-first Picard strategy

This root deliberately imports only the current route modules and contracts. Every later
contract endpoint must be checked here before it receives critical-path credit.

The tied local rank-one presentation, its canonical evaluation map, datum-side local-away
divisor equations, and the pullback-stable presentation locus are present. The conditional
`DivRankOneOpenData` representer and its open-immersion/base-change consumers are rooted. The
native evaluation section and the tied datum section have the same restriction-vanishing
predicate on every open, without a Noetherian hypothesis; their piece coordinates and principal
piece ideals agree, and those native-coordinate ideals commute with arbitrary affine
coefficient extension.

The native rank-one route now closes from certificates to public membership on the field fibre.
`RankOneFamilyCertificates.ofActualDatum` produces all four family certificates from a single
per-residue-field H1 witness plus a fibre class-degree law, with rank one computed
Noetherian-freely by `rankAtStalk_hModule_zero_eq_one_of_actualPairH1`. Arbitrary-cartesian
native base change is internalized by `isIso_canonicalBaseChangeMap_nativeModule`, so
`ofCertificatesWithNativeBaseChange` and `ofLocalPresentation` build native presentations with
no extra base-change certificate. Consequently `mem_picRankOneOpen_of_isSplitWitness` places
every split genus-degree field class in `PicRankOneOpen`, and the Pic0 separably closed
translated-cover feeder lands its translated layer element in the public locus:
`exists_sepClosedTranslated_mem_picRankOneOpen` is the phase-5 membership endpoint.

On the divisor side, the tied local presentation's finite principal-open evaluation divisors
glue: `exists_glued_rankOne_away_divisor_with_abel_evaluation` produces a `DivFamZarAff` over
the Noetherian etale carrier with the global Abel and relative-Picard identities, resting on
`baseOpenRankOneDivisor_awayMul_compat`. The big-site consumer scaffold reduces
`PicRankOneOpen.IsOpen` to one canonical evaluation-divisor classifier and per-test pullback
squares: `picRankOneOpen_isOpen_of_evaluationDivisorPullbackFamilies`.

The glued divisor now descends: `existsUnique_abel_divFamZarAff_of_localPresentation` consumes
the finite-glue output and returns the unique Abel-correct `DivFamZarAff` over the original
affine base, conditional only on the named `RankOneDivisorUniqueness` interface (the
tensor-square cocycle is manufactured from uniqueness, the descended class is pinned by étale
separatedness); `canonicalRankOneDivisorOfPresentation` names that divisor. Toward discharging
the uniqueness interface, `exists_notMem_cechPicMap_eq_of_relPicMk_eq` localizes
`relPicMk`-equality to on-the-nose `picClass` equality near every prime (base Picard classes
die Zariski-locally). The public locus is fibrewise split:
`mem_picRankOneOpen_iff_isSplitWitness` at field bases, and
`isSplitWitness_testPoint_of_mem` at every point of an arbitrary test.

Fibre nonvanishing toward that discharge is landed:
`sectionsMapTop_ne_zero_of_divEq_certified` and its tensor-form consumer say a datum section
cutting a certified divisor is nonzero on every residue-field fibre — the exact input shape of
the rank-one unit-extraction engine.

Datum-section extraction is landed, Noetherian-free:
`exists_gluedSection_sectionLocalEquations_divEq` cuts any `LocalEquations` divisor whose
Picard class matches the datum's Čech class from a germ-regular global section of the glued
sheaf, up to `DivEq` on every subordinated pointed cover — the α-corrected gluing through the
glued sheaf's own sheaf property; and `sectionLocalEquations_smul_divEq` records that global
unit rescalings of the section do not move the cut divisor.

The uniqueness interface is now DISCHARGED: `divFamZarAff_eq_of_picClass_eq_cechPicClass`
proves at most one certified divisor family per rank-one datum class (extraction + fibre
nonvanishing + the unit-extraction engine), and `rankOneDivisorUniqueness` assembles it with
the base-discrepancy localization, away-span separatedness, and faithfully-flat descent into
an unconditional proof of `RankOneDivisorUniqueness`. The canonical rank-one divisor and its
Abel/uniqueness accessors are re-exported without the interface hypothesis
(`canonicalRankOneDivisor`).

The Abel inverse law is also discharged: `divFamZarAff_eq_of_rankOne` upgrades the affine
uniqueness to arbitrary tests through the vehicle's affine-open separatedness, so the
restricted Abel map is componentwise injective on the big site
(`rankOneAbelSigma_app_injective`) and every evaluation-divisor classifier is automatically a
two-sided inverse (`abelInverse_of_uniqueness`); `rankOneAbelIso` packages the isomorphism,
gated only on an inhabitant of `PicRankOneEvaluationDivisorData`.

The noetherian-free canonical divisor theorem is now integrated at family level:
`canonicalRankOneSection` is natural on every test scheme, its representer transport is
`canonicalRankOneRepresenterTrans`, and `canonicalRankOneEvaluationDivisorData` is a genuine
inhabitant of the evaluator contract.  The finite-stage degree, admissibility, glued-divisor,
carrier transport, arbitrary-affine canonical divisor, and family integration milestones are
independently kernel-checked.  Consequently `canonicalRankOneAbelIso` is a root-reachable
two-sided inverse to the restricted Abel map on the big site.

The geometric open-locus producer is now unconditional.  `picRankOneSplitLocus` is open on an
arbitrary test, pointwise splitting constructs the native presentation of the same pulled-back
class, and `picRankOneOpen_fibrePresented` identifies this open with the pullback of the public
rank-one locus along an arbitrary Yoneda family.  Thus `picRankOneOpen_isOpen`, specialized to
`divRepAffP1Map C`, supplies the actual `DivRankOneOpenData` consumed by the canonical Abel chart.

The generic finite-Galois quotient engine is also complete through non-affine stable-chart
gluing.  `galoisQuotientWitnessOfInvariantProjection` supplies the effective universal
property, while `StableAffineOpen.isGaloisQuotient_glued` and
`StableAffineOpen.hasGaloisQuotient_of_orbitsInAffineOpen` construct the quotient under the
honest orbit-in-affine-open condition.  `GaloisQuotientWitness.overHomEquiv` and
`StableAffineOpen.gluedQuotientOverHomEquiv` now identify arbitrary maps into those quotients
with equivariant maps after base change, naturally under precomposition.  The Picard-zero
comparison is now matched on both sides: `pic0GaloisInvariantEquivGaloisEquivariantOver`
identifies deck-invariant classes with equivariant maps for the semilinear action on a chosen
finite-level representer, and its `_precomp` theorem supplies the needed naturality.  Thus
`pic0RepresentableBy_finiteGaloisDescent` immediately turns a finite-Galois Picard-zero
representer into a descended `RepresentableBy` certificate, under the explicit
`OrbitsInAffineOpen` hypothesis.  The quotient geometry now descends too:
`locallyOfFiniteType_pic0FiniteGaloisDescent` and
`quasiCompact_pic0FiniteGaloisDescent` package the same carrier as
`picRepDatum_finiteGaloisDescent` and `jacobianData_finiteGaloisDescent`.  These producers are
deliberately conditional: they do not manufacture either the finite-stage representer or the
orbit-in-affine-open input.

The separably closed endpoint is now complete.  The exact translator returned by
`exists_sepClosedTranslated_mem_picRankOneOpen` indexes a translated canonical Abel chart;
these charts are open immersions and cover every residue-field point.  Consequently
`pic0_sepClosed_representableBy` is unconditional and represents the same pinned
`pic0TypeFunctor` over every separably closed base field.  The widened admissible Abel chart
is etale-locally surjective onto this exact carrier, so its quasi-compact source proves
`quasiCompact_pic0SepClosedRepresenter`; `picRepDatumSepClosed` and
`jacobianDataSepClosed` package that same carrier and the same representation without
changing either component.  The same carrier is also finitely presented and quasi-separated,
the exact geometric hypotheses needed by a future finite-subextension object-spread theorem.

The finite-stage algebraic substrate is now rooted too.  Finitely presented algebras, tensor
coefficients and equalities, etale algebras and covers, Cech and relative-Picard classes, and a
representative PicEt cover all descend to finite subextensions.  A basic-open cocycle datum over
a tensor coefficient ring descends to one finite tensor stage.  The exact separably closed
representer has a chosen finite affine atlas with finitely presented chart rings and finite
affine presentations of pairwise overlaps, and all of its chart rings are simultaneously
modeled over one finite subextension.  A finite family of maps between scalar-extended algebras,
including maps transported through chosen finite-presentation models, also descends to one common
finite subextension when every source is of finite type.  Equality, two-map composition, and
three-map composition identities between finite-stage maps are reflected by their identities
after the ambient algebraic extension,
and an affine map whose scalar extension is an open immersion is itself an open immersion by fpqc
descent.  The parallel fpqc argument also reflects affine isomorphisms through a single field
extension, conjugated model comparisons, and iterated field towers.  The atlas
is now also rooted as an actual finite open cover whose pairwise intersections are affine, and
Mathlib's `gluedCover` packages its canonical restriction maps, transition maps, and cocycle as
an affine `Scheme.GlueData`.  A single finite tag contains every chart ring and every ordered
pair-overlap ring, and all rings in that family are simultaneously modeled over one finite
subextension.  The two canonical restrictions from each chart to its overlap are also rooted
as one finite dependent family.  After choosing the ring presentations at that stage, one
further finite subextension simultaneously supplies descended restriction maps and explicit
transported commuting squares for every leg.  Canonical chart-to-overlap restrictions induce
open immersions on spectra, and tensor-tower fpqc descent proves that every one of those
finite-stage restriction legs is an open immersion as well.  The ordered pair-overlap
transitions descend simultaneously with those restrictions, and equation reflection proves
that the two transition directions are inverse at the same finite stage.  The exact diagonal
transition is the identity, and injectivity of scalar extension reflects that identity to every
compatible finite-stage transition model.  On diagonal chart pairs, the exact restriction and
every descended model restriction induce isomorphisms on spectra, supplying the diagonal
open-leg condition needed by the gluing datum.  Scalar extension of an arbitrary algebra map
is now identified with the corresponding affine pushout and Spec pullback; consequently both
open immersions and diagonal isomorphisms ascend to every later scalar stage.  Scalar extension
also commutes with the tensor-product pushouts that present affine triple-overlap pullbacks,
with explicit pure-tensor comparison laws.  Instance-stable generic left and right faces,
arbitrary scalar extension, and both scalar-extended face laws are rooted for those pushouts,
including their map-level forms needed for composition with descended transitions.  Their named
ring interface now carries the canonical pushout property, its comparison equivalence to any
other pushout with both faces pinned, and a named scalar-extension equivalence that preserves
the selected tensor instances.  Given component equivalences and their two naturality squares,
the generic comparison now identifies that scalar-extended named pushout with the exact target
and pins both forward faces without reconstructing dependent tensor instances.  The concrete
Picard specialization supplies this comparison for every ordered triple of atlas charts, with
opaque left and right model faces and their exact transported equations;
cancellation through a field tower is natural for every descended map, and compatible
component equivalences transport tensor pushouts with both factor faces pinned.  In particular,
the component comparison square for every descended left restriction is rooted.  The literal
triple intersections are affine, their
section rings are those tensor pushouts with both face formulas pinned, and the corresponding
pushouts of the descended restriction legs carry an explicit scalar-extension comparison.
The exact cyclic transition between the three presentations of a triple intersection is a
canonical restriction map; its face equation and three-cycle identity are now proved directly
on section rings.
Those relative tensor-product rings are finite type over the finite-stage ground field whenever
their two overlap rings are.  Given comparison equivalences from their scalar extensions to the
exact triple section rings, the exact cyclic transitions therefore descend simultaneously through
one further finite subextension, with explicit comparison squares for every triple index.  The
three-cycle identity survives the comparison conjugations and reflects through those squares to
every compatible family of descended triple transitions.  The exact cyclic transition transported
through the concrete model comparisons also carries the rotated right face to the original left
face after the component-conjugated pair transition.  Scalar extension to the final finite stage
reflects that face equation without rebuilding the dependent tensor-product carriers.  Canonical
pushout equivalences then conjugate the descended transitions onto the literal triple tensor rings,
preserving both the face equation and the three-cycle identity.  The simultaneous pair- and
triple-transition descent producers inhabit one dependent package carrying all of these inputs;
its computed `glueData` applies `affineRingGlueData` and therefore produces an actual finite-stage
`Scheme.GlueData` from the descended chart and overlap rings.  The resulting glued scheme retains
its map to the finite-stage field spectrum.  After extension to the separably closed field, its
  global pullback is identified with the gluing of the pulled-back charts.  The chart and overlap
  objects have typed comparisons with the exact Picard atlas, and the descended restriction legs
  have explicit base-changed morphisms between them.  The affine comparison transitivity lemma
  now turns the final ring naturality square into a Scheme-level square, and
  `restrictionBaseChangeMap_naturality` discharges that square for every left restriction.  The
  generic nested pullback produced by first base-changing a chart and then intersecting it with a
  second chart is now flattened by a kernel-clean categorical isomorphism, with all three
  projection equations exposed for the scheme-level overlap comparison.  On rings, transition
  from the reversed overlap followed by its left restriction is now identified with the forward
  right restriction on the exact atlas, reflected to the finite model stage, and preserved by
  scalar extension to the package's final finite subextension.  The corresponding composite
  scalar-extended right restriction is now named on the dependent carrier and identified with
  the directly descended right restriction.  Finally,
`pic0PreservesFilteredBaseColimit_of_representableBy` proves the filtered-colimit statement once
an arbitrary-field locally finitely presented representer has actually been produced.

At the assembly boundary, `affineRingGlueData` now turns chart rings, overlap rings, open
restriction legs, pair transitions, and triple-tensor transitions into an actual
`Scheme.GlueData`; its diagonal, face, and cocycle fields follow from the corresponding ring
identities.  Thus no additional scheme-level gluing axiom is needed once those finite-stage
ring equations have been reflected.

These inputs do not yet constitute object descent.  Still missing, and NOT replaced here by
  axioms or local hypotheses: a kernel-clean specialization of the generic flattening isomorphism
  to the dependent finite-stage overlap package, the scheme-level comparison for the now-identified
  right overlap leg, and assembly of those local comparisons into the global glued-scheme base-change
  isomorphism; descent of the universal
  Picard natural equivalence; preservation of
Picard zero under the original-base filtered colimit;
the orbit-in-affine-open (or projectivity) input for the finite-level Picard quotient; and the
arbitrary-base-field `pic0_representableBy` and `JacobianData` endpoints.
-/

open AlgebraicGeometry.Pic0FiniteStageGluePackage

#check AlgebraicGeometry.divFunctorAff_representableBy_at
#check AlgebraicGeometry.divFunctorAff_genus_representableBy
#check AlgebraicGeometry.divFunctorAff_admissible_representableBy
#check AlgebraicGeometry.relCurve.isIntegral
#check AlgebraicGeometry.abelDivAffTrans
#check AlgebraicGeometry.abelDivAffSigma
#check AlgebraicGeometry.abelDivAffGenusSigma
#check AlgebraicGeometry.Scheme.toModuleKSheafOfModules
#check AlgebraicGeometry.canonicalBaseChangeMap
#check AlgebraicGeometry.canonicalBaseChangeMap_pullback_counit
#check AlgebraicGeometry.canonicalBaseChangeMap_counit_cancel
#check AlgebraicGeometry.PicRankOneLocalPresentation
#check AlgebraicGeometry.PicRankOneLocalPresentation.h0BaseChange
#check AlgebraicGeometry.PicRankOneLocalPresentation.baseChangeRankOneCertificates
#check AlgebraicGeometry.RankOneFamilyCertificates.sectionsMap_tower
#check AlgebraicGeometry.RankOneFamilyCertificates.h0BaseChange_tower
#check AlgebraicGeometry.BasicOpenCocycleDatum.sectionsMap_tower
#check AlgebraicGeometry.BasicOpenCocycleDatum.sectionsMapTop_tower
#check AlgebraicGeometry.PicRankOneLocalPresentation.datumSectionBaseChange_tower
#check AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenRankOneDivisor_mul_eq
#check AlgebraicGeometry.PicRankOneNativePresentation.ofCertificates
#check AlgebraicGeometry.PicRankOneLocalPresentation.evaluation
#check AlgebraicGeometry.PicRankOneLocalPresentation.nativeBaseChangeIso
#check AlgebraicGeometry.PicRankOneLocalPresentation.nativeBaseChangeIsoAffine
#check AlgebraicGeometry.PicRankOneLocalPresentation.evaluationSourceBaseChangeIso
#check AlgebraicGeometry.PicRankOneLocalPresentation.evaluationSourceBaseChangeIso_hom_evaluation
#check
  AlgebraicGeometry.PicRankOneLocalPresentation.evaluationSourceBaseChangeIsoAffine_hom_evaluation
#check AlgebraicGeometry.PicRankOneLocalPresentation.datumSection
#check AlgebraicGeometry.PicRankOneLocalPresentation.datumSectionBaseChange
#check AlgebraicGeometry.PicRankOneLocalPresentation.datumSectionBaseChange_one_tmul
#check AlgebraicGeometry.PicRankOneLocalPresentation.datumSectionBaseChangeLinearMap
#check
  AlgebraicGeometry.PicRankOneLocalPresentation.datumSectionBaseChange_eq_smul_of_tensor_eq
#check
  AlgebraicGeometry.PicRankOneLocalPresentation.tensorAwayGenerator_fibre_ne_zero
#check Module.bijective_toSpanSingleton_of_forall_tmul_ne_zero
#check Module.existsUnique_unit_smul_of_forall_tmul_ne_zero
#check AlgebraicGeometry.PicRankOneLocalPresentation.sectionLocalEquationsOfDatumSectionBaseChange
#check AlgebraicGeometry.PicRankOneLocalPresentation.moduleSectionsEquiv
#check AlgebraicGeometry.PicRankOneLocalPresentation.module_iso_inv_datumSection
#check AlgebraicGeometry.PicRankOneLocalPresentation.module_iso_inv_restrict
#check AlgebraicGeometry.PicRankOneLocalPresentation.module_iso_inv_restrict_eq_zero_iff
#check AlgebraicGeometry.PicRankOneLocalPresentation.evaluationLiftOfH0
#check AlgebraicGeometry.PicRankOneLocalPresentation.evaluation_evaluationLiftOfH0
#check
  AlgebraicGeometry.PicRankOneLocalPresentation.evaluation_evaluationLiftOfH0_eq_moduleSectionsEquiv
#check AlgebraicGeometry.PicRankOneLocalPresentation.evaluationLift_restrict_eq_zero_iff
#check AlgebraicGeometry.PicRankOneLocalPresentation.exists_baseOpen_evaluation_generator
#check
  AlgebraicGeometry.PicRankOneLocalPresentation.sectionsMapTop_datumSectionBaseChange_away_ne_zero
#check AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenDatumSectionLocalEquations
#check
  AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenDatumSectionLocalEquations_picClass
#check
  AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenDatumSectionLocalEquations_fibrewiseRegular
#check AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenDatumSectionLocalEquations_classDeg
#check
  AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenDatumSectionLocalEquations_divEq_of_unit
#check
  AlgebraicGeometry.PicRankOneLocalPresentation.sectionLocalEquationsOfDatumSectionBaseChange_divEq_of_unit
#check
  AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenDatumSectionLocalEquations_divEq
#check AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenRankOneDivisor
#check AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenRankOneDivisor_eq
#check AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenRankOneDivisor_picClass
#check
  AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenRankOneDivisor_abelAff
#check
  AlgebraicGeometry.PicRankOneLocalPresentation.exists_baseOpen_rankOne_divisor_with_evaluation
#check
  AlgebraicGeometry.PicRankOneLocalPresentation.exists_baseOpen_rankOne_divisor_with_abel_evaluation
#check
  AlgebraicGeometry.PicRankOneLocalPresentation.datum_classDeg_baseChange_of_representation
#check AlgebraicGeometry.PicRankOneLocalPresentation.datum_classDeg_baseChange
#check AlgebraicGeometry.PicRankOneOpen
#check AlgebraicGeometry.PicRankOneOpen.IsOpen
#check AlgebraicGeometry.DivRankOneOpenData
#check AlgebraicGeometry.divRankOneOpenData_of_picRankOneOpen_isOpen
#check AlgebraicGeometry.DivRankOneOpen
#check AlgebraicGeometry.divRankOneOpen_isOpenImmersion
#check AlgebraicGeometry.divRankOneOpen_mem_iff
#check AlgebraicGeometry.divRankOneOpen_baseChange_mem
#check AlgebraicGeometry.PicRankOneNativePresentation
#check AlgebraicGeometry.PicRankOneNativePresentation.toLocalPresentation
#check AlgebraicGeometry.PicRankOneNativePresentation.evaluationLift_restrict_eq_zero_iff
#check AlgebraicGeometry.BasicOpenCocycleDatum.nativePieceCoordinate
#check AlgebraicGeometry.BasicOpenCocycleDatum.nativePieceCoordinate_sectionsMapTop
#check AlgebraicGeometry.BasicOpenCocycleDatum.nativePieceIdeal_sectionsMapTop
#check
  AlgebraicGeometry.PicRankOneNativePresentation.evaluationLift_nativePieceIdeal_eq_componentIdeal
#check AlgebraicGeometry.BasicOpenCocycleDatum.nativeModulePieceSectionsEquiv
#check AlgebraicGeometry.BasicOpenCocycleDatum.nativeModulePieceSheafIso
#check AlgebraicGeometry.BasicOpenCocycleDatum.nativeModule_isLineBundle
#check AlgebraicGeometry.mem_picRankOneOpen_of_nativePresentations
#check AlgebraicGeometry.exists_sepClosedTranslatedRankOneLayer_pic0
#check AlgebraicGeometry.SepClosedTranslatedDropResult.translator_classDeg_of_pic0
#check AlgebraicGeometry.SepClosedTranslatedDropResult.baseSubtraction_compatibility
#check AlgebraicGeometry.divRankOnePresentationPreimageRepresenter
#check AlgebraicGeometry.rankOneAbelRepresented
#check AlgebraicGeometry.not_injective_abelSigmaChart_of_divFamZar
#check AlgebraicGeometry.not_isOpenImmersion_abelSigmaChart_of_not_injective_chartValue
#check AlgebraicGeometry.not_isOpenImmersion_abelSigmaChart_of_genus_lt_degree
#check AlgebraicGeometry.not_injective_abelSigmaChartAff_of_divFamZarAff
#check AlgebraicGeometry.not_injective_chartValueAff_of_not_injective_chartValue
#check AlgebraicGeometry.not_isOpenImmersion_abelSigmaChartAff_of_not_injective_chartValueAff
#check AlgebraicGeometry.not_isOpenImmersion_abelSigmaChartAff_of_genus_lt_degree

#print axioms AlgebraicGeometry.divFunctorAff_representableBy_at
#print axioms AlgebraicGeometry.divFunctorAff_genus_representableBy
#print axioms AlgebraicGeometry.divFunctorAff_admissible_representableBy
#print axioms AlgebraicGeometry.abelDivAffGenusSigma
#print axioms AlgebraicGeometry.PicRankOneLocalPresentation.h0BaseChange
#print axioms AlgebraicGeometry.PicRankOneLocalPresentation.baseChangeRankOneCertificates
#print axioms AlgebraicGeometry.RankOneFamilyCertificates.sectionsMap_tower
#print axioms AlgebraicGeometry.RankOneFamilyCertificates.h0BaseChange_tower
#print axioms AlgebraicGeometry.BasicOpenCocycleDatum.sectionsMap_tower
#print axioms AlgebraicGeometry.BasicOpenCocycleDatum.sectionsMapTop_tower
#print axioms AlgebraicGeometry.PicRankOneLocalPresentation.datumSectionBaseChange_tower
#print axioms AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenRankOneDivisor_mul_eq
#print axioms AlgebraicGeometry.PicRankOneNativePresentation.ofCertificates
#print axioms AlgebraicGeometry.PicRankOneLocalPresentation.evaluation
#print axioms AlgebraicGeometry.divRankOneOpenData_of_picRankOneOpen_isOpen
#print axioms AlgebraicGeometry.divRankOneOpen_isOpenImmersion
#print axioms AlgebraicGeometry.divRankOneOpen_baseChange_mem
#print axioms AlgebraicGeometry.PicRankOneNativePresentation.toLocalPresentation
#print axioms AlgebraicGeometry.BasicOpenCocycleDatum.nativeModulePieceSheafIso
#print axioms AlgebraicGeometry.BasicOpenCocycleDatum.nativeModule_isLineBundle
#print axioms AlgebraicGeometry.mem_picRankOneOpen_of_nativePresentations
#print axioms AlgebraicGeometry.exists_sepClosedTranslatedRankOneLayer_pic0
#print axioms AlgebraicGeometry.SepClosedTranslatedDropResult.translator_classDeg_of_pic0
#print axioms AlgebraicGeometry.SepClosedTranslatedDropResult.baseSubtraction_compatibility
#print axioms AlgebraicGeometry.canonicalBaseChangeMap_pullback_counit
#print axioms AlgebraicGeometry.canonicalBaseChangeMap_counit_cancel
#print axioms AlgebraicGeometry.PicRankOneLocalPresentation.nativeBaseChangeIsoAffine
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.evaluationSourceBaseChangeIso_hom_evaluation
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.evaluationSourceBaseChangeIsoAffine_hom_evaluation
#print axioms AlgebraicGeometry.PicRankOneLocalPresentation.module_iso_inv_datumSection
#print axioms AlgebraicGeometry.PicRankOneLocalPresentation.module_iso_inv_restrict
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.module_iso_inv_restrict_eq_zero_iff
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.evaluation_evaluationLiftOfH0_eq_moduleSectionsEquiv
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.evaluationLift_restrict_eq_zero_iff
#print axioms
  AlgebraicGeometry.PicRankOneNativePresentation.evaluationLift_restrict_eq_zero_iff
#print axioms AlgebraicGeometry.BasicOpenCocycleDatum.nativePieceCoordinate
#print axioms AlgebraicGeometry.BasicOpenCocycleDatum.nativePieceCoordinate_eq_component
#print axioms AlgebraicGeometry.BasicOpenCocycleDatum.nativePieceCoordinate_sectionsMapTop
#print axioms AlgebraicGeometry.BasicOpenCocycleDatum.nativePieceIdeal_sectionsMapTop
#print axioms AlgebraicGeometry.BasicOpenCocycleDatum.nativeModuleKSectionsEquiv_symm_apply
#print axioms AlgebraicGeometry.BasicOpenCocycleDatum.nativeModuleKSheafIso_inv_app
#print axioms
  AlgebraicGeometry.PicRankOneNativePresentation.moduleSectionsEquiv_nativePieceCoordinate_eq_component
#print axioms
  AlgebraicGeometry.PicRankOneNativePresentation.evaluationLift_nativePieceCoordinate_eq_component
#print axioms
  AlgebraicGeometry.PicRankOneNativePresentation.evaluationLift_nativePieceIdeal_eq_componentIdeal
#print axioms AlgebraicGeometry.PicRankOneLocalPresentation.datumSectionBaseChange_one_tmul
#print axioms AlgebraicGeometry.PicRankOneLocalPresentation.datumSectionBaseChangeLinearMap
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.datumSectionBaseChange_eq_smul_of_tensor_eq
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.tensorAwayGenerator_fibre_ne_zero
#print axioms Module.bijective_toSpanSingleton_of_forall_tmul_ne_zero
#print axioms Module.existsUnique_unit_smul_of_forall_tmul_ne_zero
namespace AlgebraicGeometry.PicRankOneLocalPresentation
#print axioms sectionLocalEquationsOfDatumSectionBaseChange_picClass
end AlgebraicGeometry.PicRankOneLocalPresentation
#print axioms AlgebraicGeometry.PicRankOneLocalPresentation.evaluation_evaluationLiftOfH0
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.exists_baseOpen_evaluation_generator
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.sectionsMapTop_datumSectionBaseChange_away_ne_zero
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenDatumSectionLocalEquations_picClass
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenDatumSectionLocalEquations_fibrewiseRegular
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenDatumSectionLocalEquations_classDeg
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenDatumSectionLocalEquations_divEq_of_unit
namespace AlgebraicGeometry.PicRankOneLocalPresentation
#print axioms sectionLocalEquationsOfDatumSectionBaseChange_divEq_of_unit
end AlgebraicGeometry.PicRankOneLocalPresentation
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenDatumSectionLocalEquations_divEq
#print axioms AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenRankOneDivisor
#print axioms AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenRankOneDivisor_eq
#print axioms AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenRankOneDivisor_picClass
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenRankOneDivisor_abelAff
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.exists_baseOpen_rankOne_divisor_with_evaluation
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.exists_baseOpen_rankOne_divisor_with_abel_evaluation
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.datum_classDeg_baseChange_of_representation
#print axioms AlgebraicGeometry.PicRankOneLocalPresentation.datum_classDeg_baseChange
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.existsUnique_unit_tensorAway_rankOne_generators
#print axioms AlgebraicGeometry.rankOneAbelRepresented
#print axioms AlgebraicGeometry.not_isOpenImmersion_abelSigmaChart_of_genus_lt_degree
#print axioms AlgebraicGeometry.not_isOpenImmersion_abelSigmaChartAff_of_genus_lt_degree

-- Native datum layer (Pic0RankOneNativePresentationDatum.lean)
#check AlgebraicGeometry.PicRankOneNativeDatum
#check AlgebraicGeometry.PicRankOneNativeDatum.nonempty
#check AlgebraicGeometry.PicRankOneNativeDatum.classDeg_baseChange
#check AlgebraicGeometry.PicRankOneNativeDatum.residueH1Witness_of_isSplitWitness
-- Native datum from a field pullback (Pic0RankOneNativePresentationField.lean)
#check AlgebraicGeometry.PicRankOneNativeDatum.residueH1Witness_of_fieldPullback
#check AlgebraicGeometry.isSplitWitness_map_overSpecMap_of_algHom
-- Arbitrary-cartesian native base change (Pic0RankOneNativeBaseChangeCartesian.lean)
#check AlgebraicGeometry.BasicOpenCocycleDatum.isIso_canonicalBaseChangeMap_nativeModule
#check AlgebraicGeometry.PicRankOneNativePresentation.ofCertificatesWithNativeBaseChange
-- Four-certificate producer from the actual datum (Cohomology/RankOneFamilyCertificatesActualDatum.lean)
#check AlgebraicGeometry.BasicOpenCocycleDatum.ResidueH1Witness
#check AlgebraicGeometry.BasicOpenCocycleDatum.FibreClassDegree
#check AlgebraicGeometry.RankOneFamilyCertificates.ofActualDatum
-- Rank one without a Noetherian hypothesis (Cohomology/RankOneFamilyCertificatesActualDatumRank.lean)
#check AlgebraicGeometry.BasicOpenCocycleDatum.rankAtStalk_hModule_zero_eq_one_of_actualPairH1
-- Datum-to-certificates-to-native-presentation wrappers (Pic0RankOneFamilyCertificatesActualDatum.lean)
#check AlgebraicGeometry.PicRankOneNativeDatum.familyCertificates
#check AlgebraicGeometry.PicRankOneNativeDatum.familyCertificatesBaseChange
#check AlgebraicGeometry.PicRankOneNativePresentation.ofNativeDatum
-- Local-to-native presentation converter (Pic0RankOneNativePresentationOfLocal.lean)
#check AlgebraicGeometry.PicRankOneNativePresentation.ofLocalPresentation
#check AlgebraicGeometry.PicRankOneNativePresentation.nonempty_of_localPresentation
#check AlgebraicGeometry.PicRankOneNativePresentation.nonempty_of_localPresentations
-- Split field class gives membership in PicRankOneOpen (Pic0RankOneNativePresentationSplit.lean)
#check AlgebraicGeometry.exists_algHom_eq_of_overSpec_hom_of_commRing
#check AlgebraicGeometry.PicRankOneNativeDatum.toNativePresentation_of_residueH1Witness
#check AlgebraicGeometry.PicRankOneNativePresentation.nonempty_of_fieldPullback
#check AlgebraicGeometry.mem_picRankOneOpen_of_isSplitWitness
-- Datum-side away-divisor naturality (Pic0RankOneFibrePresentedProducerAwayNaturality.lean)
#check AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenRankOneDivisor_mapAlgHom_mul_left
#check AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenRankOneDivisor_mapAlgHom_mul_right
#check AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenRankOneDivisor_awayMul_compat
-- Section/divisor equality helpers (Pic0RankOneFibrePresentedProducerSectionDivEq.lean)
#check AlgebraicGeometry.BasicOpenCocycleDatum.sectionLocalEquations_divEq_of_same_section
#check
  AlgebraicGeometry.BasicOpenCocycleDatum.pullback_sectionLocalEquationsOfFibrewiseRegular_divEq_sectionsMapTop
-- Finite gluing of away-divisors to a family divisor (Pic0RankOneFibrePresentedProducerFiniteGlue.lean)
#check
  AlgebraicGeometry.PicRankOneLocalPresentation.exists_glued_rankOne_away_divisor_with_abel_evaluation
-- Big-site consumer scaffold (Pic0RankOneFibrePresentedProducer.lean)
#check AlgebraicGeometry.rankOneAbelSigma
#check AlgebraicGeometry.rankOneDivisorToAmbient
#check AlgebraicGeometry.PicRankOneEvaluationDivisorData
#check AlgebraicGeometry.PicRankOneFibrePresentationInput
#check AlgebraicGeometry.PicRankOneFibrePresentationInput.EvaluationDivisorPullback
#check AlgebraicGeometry.PicRankOneFibrePresentationInput.toFibrePresented_of_evaluationDivisorPullback
#check
  AlgebraicGeometry.PicRankOneFibrePresentationInput.picRankOneOpen_isOpen_of_evaluationDivisorPullbackFamilies
-- Phase-5 translated-cover membership endpoint (Pic0RankOneTranslatedCoverMembership.lean)
#check AlgebraicGeometry.exists_sepClosedTranslated_mem_picRankOneOpen
-- Base-discrepancy localization (RelPicBaseLocalTriviality.lean)
#check CommRing.Pic.exists_notMem_mapAlgebra_eq_one
#check AlgebraicGeometry.exists_notMem_cechPicMap_specMap_eq_one
#check AlgebraicGeometry.exists_notMem_cechPicMap_eq_of_relPicMk_eq
#check AlgebraicGeometry.DivFamZarAff.exists_notMem_picClass_map_eq_of_relPicMk_eq
-- Canonical divisor descent to the affine base (Pic0RankOneCanonicalDivisorDescent.lean)
#check AlgebraicGeometry.RankOneDivisorUniqueness
#check AlgebraicGeometry.existsUnique_abel_divFamZarAff_of_etale_witness
#check AlgebraicGeometry.existsUnique_abel_divFamZarAff_of_localPresentation
#check AlgebraicGeometry.canonicalRankOneDivisorOfPresentation
#check AlgebraicGeometry.canonicalRankOneDivisorOfPresentation_abel
#check AlgebraicGeometry.canonicalRankOneDivisorOfPresentation_unique
-- Fibrewise split characterization of the public locus (Pic0RankOneSplitMembership.lean)
#check AlgebraicGeometry.isSplitWitness_of_mem_picRankOneOpen_field
#check AlgebraicGeometry.mem_picRankOneOpen_iff_isSplitWitness
#check AlgebraicGeometry.isSplitWitness_testPoint_of_mem
-- Fibre nonvanishing of a class-matched datum section (Pic0RankOneSectionFibreNonzero.lean)
#check AlgebraicGeometry.BasicOpenCocycleDatum.sectionsMapTop_ne_zero_of_divEq_certified
#check AlgebraicGeometry.BasicOpenCocycleDatum.tmul_residueField_ne_zero_of_divEq_certified
-- Datum-section extraction from a class-matched divisor (DivisorDatumSectionOfClass.lean)
#check AlgebraicGeometry.BasicOpenCocycleDatum.exists_gluedSection_sectionLocalEquations_divEq
#check AlgebraicGeometry.BasicOpenCocycleDatum.component_smul
#check AlgebraicGeometry.BasicOpenCocycleDatum.germ_component_smul_mem_nonZeroDivisors
#check AlgebraicGeometry.BasicOpenCocycleDatum.sectionLocalEquations_smul_divEq
-- Uniqueness of the divisor family in a rank-one datum class (Pic0RankOneDivisorUnique.lean)
#check AlgebraicGeometry.BasicOpenCocycleDatum.divFamZarAff_eq_of_picClass_eq_cechPicClass
-- Uniqueness interface discharged; canonical divisor unconditional
-- (Pic0RankOneUniquenessDischarge.lean)
#check AlgebraicGeometry.PicRankOneLocalPresentation.exists_notMem_mapAlgHom_eq
#check AlgebraicGeometry.rankOneDivisorUniqueness
#check AlgebraicGeometry.existsUnique_abel_divFamZarAff_of_presentation
#check AlgebraicGeometry.canonicalRankOneDivisor
#check AlgebraicGeometry.canonicalRankOneDivisor_abel
#check AlgebraicGeometry.canonicalRankOneDivisor_unique
-- Noetherian-free canonical evaluation pipeline
#check AlgebraicGeometry.stage_classDeg_all_fields
#check AlgebraicGeometry.PicRankOneNoetherianStage.admissibility
#check AlgebraicGeometry.PicRankOneNoetherianStage.exists_glued_divFamZarAff
#check AlgebraicGeometry.PicRankOneLocalPresentation.exists_carrier_divFamZarAff_abel
#check AlgebraicGeometry.existsUnique_abel_divFamZarAff_of_mem
-- Abel inverse law and the packaged rank-one iso (Pic0RankOneAbelInverse.lean)
#check AlgebraicGeometry.divFamZarAff_eq_of_rankOne
#check AlgebraicGeometry.rankOneAbelSigma_app_injective
#check AlgebraicGeometry.PicRankOneEvaluationDivisorData.abelInverse_of_uniqueness
#check AlgebraicGeometry.PicRankOneEvaluationDivisorData.rankOneAbelIso
#check AlgebraicGeometry.canonicalRankOneSection
#check AlgebraicGeometry.canonicalRankOneRepresenterTrans
#check AlgebraicGeometry.canonicalRankOneEvaluationDivisorData
#check AlgebraicGeometry.canonicalRankOneAbelIso
#check AlgebraicGeometry.rankOneAbel_isOpenImmersion
-- Unconditional arbitrary-family rank-one open producer
#check AlgebraicGeometry.isOpen_picRankOneSplitLocus_overSpec
#check AlgebraicGeometry.PicRankOneNativePresentation.nonempty_of_pointwiseSplit
#check AlgebraicGeometry.mem_picRankOneOpen_of_pointwiseSplit
#check AlgebraicGeometry.picRankOneOpen_fibrePresented
#check AlgebraicGeometry.picRankOneOpen_isOpen
-- Separably closed representability from the exact translated rank-one cover
#check AlgebraicGeometry.exists_picRankOneTranslatedChart_fieldFactorization
#check AlgebraicGeometry.picRankOneTranslatedChart_pointwiseCoverage
#check AlgebraicGeometry.pic0_sepClosed_representableBy
#check AlgebraicGeometry.locallyOfFiniteType_pic0_sepClosed_representableBy
#check AlgebraicGeometry.quasiCompact_pic0SepClosedRepresenter
#check AlgebraicGeometry.locallyOfFinitePresentation_pic0_sepClosed_representableBy
#check AlgebraicGeometry.quasiSeparatedSpace_pic0SepClosedRepresenter
#check AlgebraicGeometry.picRepDatumSepClosed
#check AlgebraicGeometry.picRepDatumSepClosed_J
#check AlgebraicGeometry.picRepDatumSepClosed_rep
#check AlgebraicGeometry.jacobianDataSepClosed
#check AlgebraicGeometry.jacobianDataSepClosed_J
#check AlgebraicGeometry.jacobianDataSepClosed_rep
-- Generic non-affine finite-Galois quotient engine
#check AlgebraicJacobian.GaloisDescent.galoisQuotientUniversal_of_equivariant
#check AlgebraicJacobian.GaloisDescent.galoisQuotientWitnessOfInvariantProjection
#check AlgebraicJacobian.GaloisDescent.StableAffineOpen.isGaloisQuotient_glued
#check AlgebraicJacobian.GaloisDescent.StableAffineOpen.hasGaloisQuotient_of_orbitsInAffineOpen
#check AlgebraicJacobian.GaloisDescent.GaloisQuotientWitness.overHomEquiv
#check AlgebraicJacobian.GaloisDescent.GaloisQuotientWitness.overHomEquiv_precomp
#check AlgebraicJacobian.GaloisDescent.StableAffineOpen.gluedQuotientOverHomEquiv
#check AlgebraicJacobian.GaloisDescent.StableAffineOpen.gluedQuotientOverHomEquiv_precomp
-- Picard-zero finite-Galois fixed-point comparison on arbitrary tests
#check AlgebraicGeometry.Pic0GaloisInvariant
#check AlgebraicGeometry.pic0GaloisInvariant_existsUnique_descend
#check AlgebraicGeometry.pic0RestrictToGaloisInvariant_bijective
#check AlgebraicGeometry.pic0GaloisInvariantEquiv
#check AlgebraicGeometry.pic0GaloisInvariantEquiv_precomp
-- Invariant/equivariant comparison and the conditional descended representer
#check AlgebraicGeometry.pic0GaloisInvariantEquivGaloisEquivariantOver
#check AlgebraicGeometry.pic0GaloisInvariantEquivGaloisEquivariantOver_precomp
#check AlgebraicGeometry.pic0RepresentableBy_finiteGaloisDescent
#check AlgebraicJacobian.GaloisDescent.IsGaloisQuotient.locallyOfFiniteType
#check AlgebraicJacobian.GaloisDescent.IsGaloisQuotient.quasiCompact
#check AlgebraicGeometry.locallyOfFiniteType_pic0FiniteGaloisDescent
#check AlgebraicGeometry.quasiCompact_pic0FiniteGaloisDescent
#check AlgebraicGeometry.picRepDatum_finiteGaloisDescent
#check AlgebraicGeometry.jacobianData_finiteGaloisDescent
#check AlgebraicGeometry.isOpenImmersion_of_fpqc_pushout
#check AlgebraicGeometry.isOpenImmersion_of_tensorProduct
#check AlgebraicJacobian.isPushout_scalarExtensionMapOfAlgHom
#check AlgebraicGeometry.isPullback_specMap_scalarExtensionMapOfAlgHom
#check AlgebraicGeometry.isOpenImmersion_scalarExtensionMapOfAlgHom
#check AlgebraicGeometry.isIso_specMap_scalarExtensionMapOfAlgHom
#check AlgebraicJacobian.scalarExtensionMap
#check AlgebraicJacobian.tensorProductPushoutBaseChange
#check AlgebraicJacobian.tensorProductPushoutBaseChange_tmul
#check AlgebraicJacobian.tensorProductPushoutBaseChange_symm_tmul
#check AlgebraicJacobian.finiteType_tensorProduct_over
-- Finite-stage algebra, cover, class, datum, atlas, and colimit substrate
#check AlgebraicGeometry.DatG0.exists_finSubext_tensorProduct_preimage
#check AlgebraicGeometry.DatG0.exists_finSubext_tensorProduct_eq
#check AlgebraicGeometry.DatG0.exists_finSubext_tensorProduct_preimage_finite
#check AlgebraicGeometry.DatG0.exists_finSubext_tensorProduct_eq_finite
#check AlgebraicGeometry.DatG0.tensorProduct_map_finSubext_injective
#check AlgebraicGeometry.DatG0.exists_finSubext_fg_subalgebra_tensorProduct_factor
#check AlgebraicGeometry.DatG0.FiniteRelationAlgebra
#check
  AlgebraicGeometry.DatG0.exists_finSubext_finitePresentation_algebra_model
#check
  AlgebraicGeometry.DatG0.exists_finSubext_finitePresentation_algebra_model_finite
#check AlgebraicGeometry.DatG0.exists_finSubext_tensorProduct_algHom
#check AlgebraicGeometry.DatG0.tensorProduct_algHom_eq_of_map_comp_eq
#check AlgebraicGeometry.DatG0.tensorProduct_algHom_comp_eq_of_baseChange
#check AlgebraicGeometry.DatG0.tensorProduct_algHom_triple_comp_eq_of_baseChange
#check AlgebraicGeometry.DatG0.exists_finSubext_tensorProduct_algHom_finite
#check AlgebraicGeometry.DatG0.exists_finSubext_tensorProduct_algHom_finite_of_models
#check AlgebraicGeometry.DatG0.exists_finSubext_etale_model
#check AlgebraicGeometry.DatG0.exists_finSubext_etaleCover_model
#check AlgebraicGeometry.exists_finSubext_cechPic_model
#check AlgebraicGeometry.exists_finSubext_relPic_model
#check AlgebraicGeometry.exists_finSubext_baseChanged_cover_representation
#check AlgebraicGeometry.BasicOpenCocycleDatum.exists_finSubext_tensorStage
#check AlgebraicGeometry.exists_finSubext_relPic_tensorStage
#check AlgebraicGeometry.exists_finSubext_relPic_tensorStage_finite
#check AlgebraicGeometry.pic0SepClosedUniversalClass
#check AlgebraicGeometry.pic0FiniteStageUniversalChartClass_restrict_left
#check AlgebraicGeometry.pic0FiniteStageUniversalChartClass_restrict_right
#check AlgebraicGeometry.Pic0FiniteStageUniversalAtlasClass
#check AlgebraicGeometry.pic0FiniteStageUniversalAtlasClass
#check AlgebraicGeometry.Scheme.exists_finite_affineCover_inter_isQuasiCompact
#check AlgebraicGeometry.Scheme.FiniteAffineOverlapPresentation
#check AlgebraicGeometry.Scheme.finiteAffineOverlapPresentation
#check AlgebraicGeometry.Pic0FiniteStageAtlas
#check AlgebraicGeometry.pic0FiniteStageAtlas
#check AlgebraicGeometry.Pic0FiniteStageChartRing
#check AlgebraicGeometry.finitePresentation_pic0FiniteStageChartRing
#check AlgebraicGeometry.exists_finSubext_pic0FiniteStageAtlas_chartRing_models
#check AlgebraicGeometry.Pic0FiniteStageChartIndex
#check AlgebraicGeometry.pic0FiniteStageAtlas_inter_isAffine
#check AlgebraicGeometry.pic0FiniteStageAffineOverlap
#check AlgebraicGeometry.pic0SepClosedAtlasOpenCover
#check AlgebraicGeometry.pic0SepClosedAtlasGlueData
#check AlgebraicGeometry.Pic0FiniteStageOverlapRing
#check AlgebraicGeometry.finitePresentation_pic0FiniteStageOverlapRing
#check AlgebraicGeometry.Pic0FiniteStageRingIndex
#check AlgebraicGeometry.Pic0FiniteStageRing
#check AlgebraicGeometry.finitePresentation_pic0FiniteStageRing
#check AlgebraicGeometry.exists_finSubext_pic0FiniteStageAtlas_ring_models
#check AlgebraicGeometry.pic0FiniteStageRestrictionLeft
#check AlgebraicGeometry.pic0FiniteStageRestrictionRight
#check AlgebraicGeometry.Pic0FiniteStageRestrictionIndex
#check AlgebraicGeometry.pic0FiniteStageRestriction
#check AlgebraicGeometry.exists_finSubext_pic0FiniteStageRestriction_models
#check AlgebraicGeometry.tensorProductFieldTowerEquiv
#check AlgebraicGeometry.isOpenImmersion_of_tensorProduct_conjugate
#check AlgebraicGeometry.isOpenImmersion_of_fieldTower_tensorProducts
#check AlgebraicGeometry.isOpenImmersion_specMap_affineRestriction
#check AlgebraicGeometry.isOpenImmersion_pic0FiniteStageRestriction
#check AlgebraicGeometry.exists_finSubext_pic0FiniteStageRestriction_openImmersion_models
#check AlgebraicGeometry.Pic0FiniteStageTransitionIndex
#check AlgebraicGeometry.pic0FiniteStageTransition
#check AlgebraicGeometry.pic0FiniteStageTransition_inverse
#check AlgebraicGeometry.Pic0FiniteStageMapIndex
#check AlgebraicGeometry.Pic0FiniteStageModelRing
#check AlgebraicGeometry.exists_finSubext_pic0FiniteStageTransition_models
#check AlgebraicGeometry.isIso_specMap_pic0FiniteStageRestriction_diagonal_left
#check AlgebraicGeometry.isIso_specMap_pic0FiniteStageModelRestriction_diagonal_left
#check AlgebraicGeometry.pic0FiniteStageTransportedTransition_self
#check AlgebraicGeometry.pic0FiniteStageTransitionModel_self
#check AlgebraicGeometry.Pic0FiniteStageTripleOpen
#check AlgebraicGeometry.pic0FiniteStageTripleOpen_isAffine
#check AlgebraicGeometry.Pic0FiniteStageTripleRing
#check AlgebraicGeometry.isPushout_pic0FiniteStageTripleRing
#check AlgebraicGeometry.pic0FiniteStageTripleTensorEquiv
#check AlgebraicGeometry.pic0FiniteStageTripleTensorEquiv_tmul_one
#check AlgebraicGeometry.pic0FiniteStageTripleTensorEquiv_one_tmul
#check AlgebraicGeometry.finiteType_pic0FiniteStageTensorPushoutRing
#check AlgebraicGeometry.Pic0FiniteStageTripleModelRing
#check AlgebraicGeometry.finiteType_pic0FiniteStageTripleModelRing
#check AlgebraicGeometry.pic0FiniteStageTripleModelBaseChange
#check AlgebraicGeometry.finiteStageTensorPushoutFaceLeft
#check AlgebraicGeometry.finiteStageTensorPushoutFaceRight
#check AlgebraicGeometry.finiteStageTensorPushoutScalarExtension
#check AlgebraicGeometry.finiteStageTensorPushoutScalarExtension_tmul
#check AlgebraicGeometry.finiteStageTensorPushoutScalarExtension_faceLeft
#check AlgebraicGeometry.finiteStageTensorPushoutScalarExtension_faceRight
#check AlgebraicGeometry.finiteStageTensorPushoutScalarExtension_faceLeft_map
#check AlgebraicGeometry.finiteStageTensorPushoutScalarExtension_faceRight_map
#check AlgebraicGeometry.finiteStageTensorPushout_isPushout
#check AlgebraicGeometry.finiteStageTensorPushoutAlgEquivOfIsPushout
#check AlgebraicGeometry.finiteStageTensorPushoutAlgEquivOfIsPushout_faceLeft
#check AlgebraicGeometry.finiteStageTensorPushoutAlgEquivOfIsPushout_faceRight
#check AlgebraicGeometry.finiteStageTensorPushoutScalarExtension_named
#check AlgebraicGeometry.finiteStageTensorPushoutComparisonSquare
#check AlgebraicGeometry.finiteStageTensorPushoutMiddleComparison
#check AlgebraicGeometry.finiteStageTensorPushoutComparison
#check AlgebraicGeometry.finiteStageTensorPushoutComparison_faceLeft
#check AlgebraicGeometry.finiteStageTensorPushoutComparison_faceRight
#check AlgebraicGeometry.pic0FiniteStageTripleModelComparison
#check AlgebraicGeometry.pic0FiniteStageTripleModelFaceLeft
#check AlgebraicGeometry.pic0FiniteStageTripleModelFaceRight
#check AlgebraicGeometry.pic0FiniteStageTripleModelComparison_faceLeft
#check AlgebraicGeometry.pic0FiniteStageTripleModelComparison_faceRight
#check AlgebraicGeometry.pic0FiniteStageTripleModelComparisonFamily
#check AlgebraicGeometry.pic0FiniteStageTransportedTripleTransitionOfModels
#check AlgebraicGeometry.pic0FiniteStagePairModelComparisonTransition
#check AlgebraicGeometry.pic0FiniteStageTransportedTripleTransition_fac
#check AlgebraicGeometry.pic0FiniteStageModelBaseChangeEquiv
#check AlgebraicGeometry.pic0FiniteStageModelBaseChangeEquiv_naturality
#check AlgebraicGeometry.tensorPushoutAlgEquivCongr
#check AlgebraicGeometry.tensorPushoutAlgEquivCongr_faces
#check AlgebraicGeometry.pic0FiniteStageModelBaseChangeEquiv_restrictionLeft
#check AlgebraicGeometry.Pic0FiniteStageTripleTransitionIndex
#check AlgebraicGeometry.Pic0FiniteStageTripleTransitionModelSource
#check AlgebraicGeometry.Pic0FiniteStageTripleTransitionModelTarget
#check AlgebraicGeometry.pic0FiniteStageTransportedTripleTransition
#check
  AlgebraicGeometry.exists_finSubext_pic0FiniteStageTripleTransition_models_of_comparisons
#check AlgebraicGeometry.pic0FiniteStageTransportedTripleTransition_cocycle
#check AlgebraicGeometry.pic0FiniteStageTripleTransitionModel_cocycle
#check AlgebraicGeometry.scalarExtensionMapOfAlgHom_tower_finSubext
#check AlgebraicGeometry.scalarExtensionMapOfPairModel_eq_pairModelComparisonTransition
#check AlgebraicGeometry.pic0FiniteStageTripleTransitionModel_fac
#check AlgebraicGeometry.conjugateAlgHom_threeCycle
#check AlgebraicGeometry.pic0FiniteStageAffineTripleTransition_cocycle
#check AlgebraicGeometry.conjugateAlgHom_face_of_squares
#check AlgebraicGeometry.pic0FiniteStageAffineTripleTransition_fac
#check AlgebraicGeometry.pic0FiniteStageAffineRingGlueData
#check AlgebraicGeometry.Pic0FiniteStageGluePackage
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.glueData
#check AlgebraicGeometry.exists_pic0FiniteStageGluePackage
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.affineBaseChangeIso_trans_naturality
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.restrictionBaseChangeMap_naturality
#check AlgebraicGeometry.nestedPullbackFlatteningIso
#check AlgebraicGeometry.nestedPullbackFlatteningIso_hom_comp_fst_comp_a
#check AlgebraicGeometry.nestedPullbackFlatteningIso_hom_comp_fst_comp_b
#check AlgebraicGeometry.nestedPullbackFlatteningIso_hom_comp_snd
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingOverlapFlatteningIso
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingOverlapFlatteningIso_hom_comp_fst_comp_f
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingOverlapFlatteningIso_hom_comp_fst_comp_t_f
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingOverlapFlatteningIso_hom_comp_snd
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.glueData_f_comp_inclusion_comp_gluedMap
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.exactRestrictionAlgHom_fromSpec
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.restrictionBaseChangeRingHom
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.chartBaseChangeMap
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.overlapBaseChangeMap
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.finitePresentation_pic0FiniteStageChartBaseChangeRing
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.finiteType_pic0FiniteStageChartBaseChangeRing
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.restrictionBaseChangeMap_fst
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.restrictionBaseChangeMap_snd
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingChartIso_hom_ι
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.overlapBaseChangeIso_hom_atlas_t_f_ι
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingOverlapIso_pre_fst
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingOverlapIso
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingOverlapIso_fst
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.transition_comp_restrictionLeft_eq_restrictionRight
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.transportedMap_transition_comp_restrictionLeft_eq_right
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.mapM_transition_comp_restrictionLeft_eq_right
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.scalarExtension_transition_comp_restrictionLeft_eq_right
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.rightRestrictionBaseChangeAlgHom
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.rightRestrictionBaseChangeAlgHomPinned
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.rightRestrictionBaseChangeRingHom
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.rightRestrictionBaseChangeAlgHom_eq_direct
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.exactRightRestrictionAlgHom
#check
  AlgebraicGeometry.Pic0FiniteStageGluePackage.rightRestrictionFinalBaseChangeEquiv_naturality
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.rightRestrictionBaseChangeMap
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.rightRestrictionBaseChangeMap_naturality
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.rightRestrictionBaseChangeMap_fromSpec
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingOverlapIso_snd
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingGluedIso
#check AlgebraicGeometry.Pic0FiniteStageGluePackage.finiteStageBaseChangeIso
#check AlgebraicGeometry.pic0PreservesFilteredBaseColimit_of_representableBy
#check AlgebraicGeometry.pic0RepresentableBy_of_baseChangeObjectIso
-- Datum-level glued divisor over a Noetherian base (Pic0RankOneDatumGluedDivisor.lean)
#check AlgebraicGeometry.BasicOpenCocycleDatum.exists_glued_divFamZarAff_of_admissible_fibre

#print axioms AlgebraicGeometry.BasicOpenCocycleDatum.isIso_canonicalBaseChangeMap_nativeModule
#print axioms AlgebraicGeometry.PicRankOneNativePresentation.ofCertificatesWithNativeBaseChange
#print axioms AlgebraicGeometry.RankOneFamilyCertificates.ofActualDatum
#print axioms
  AlgebraicGeometry.BasicOpenCocycleDatum.rankAtStalk_hModule_zero_eq_one_of_actualPairH1
#print axioms AlgebraicGeometry.PicRankOneNativePresentation.nonempty_of_localPresentations
#print axioms AlgebraicGeometry.mem_picRankOneOpen_of_isSplitWitness
#print axioms AlgebraicGeometry.PicRankOneLocalPresentation.baseOpenRankOneDivisor_awayMul_compat
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.exists_glued_rankOne_away_divisor_with_abel_evaluation
#print axioms
  AlgebraicGeometry.PicRankOneFibrePresentationInput.picRankOneOpen_isOpen_of_evaluationDivisorPullbackFamilies
#print axioms AlgebraicGeometry.exists_sepClosedTranslated_mem_picRankOneOpen
#print axioms AlgebraicGeometry.exists_notMem_cechPicMap_eq_of_relPicMk_eq
#print axioms AlgebraicGeometry.DivFamZarAff.exists_notMem_picClass_map_eq_of_relPicMk_eq
#print axioms AlgebraicGeometry.existsUnique_abel_divFamZarAff_of_etale_witness
#print axioms AlgebraicGeometry.existsUnique_abel_divFamZarAff_of_localPresentation
#print axioms AlgebraicGeometry.canonicalRankOneDivisorOfPresentation_abel
#print axioms AlgebraicGeometry.canonicalRankOneDivisorOfPresentation_unique
#print axioms AlgebraicGeometry.isSplitWitness_of_mem_picRankOneOpen_field
#print axioms AlgebraicGeometry.mem_picRankOneOpen_iff_isSplitWitness
#print axioms AlgebraicGeometry.isSplitWitness_testPoint_of_mem
#print axioms AlgebraicGeometry.BasicOpenCocycleDatum.sectionsMapTop_ne_zero_of_divEq_certified
#print axioms AlgebraicGeometry.BasicOpenCocycleDatum.tmul_residueField_ne_zero_of_divEq_certified
#print axioms
  AlgebraicGeometry.BasicOpenCocycleDatum.exists_gluedSection_sectionLocalEquations_divEq
#print axioms AlgebraicGeometry.BasicOpenCocycleDatum.sectionLocalEquations_smul_divEq
#print axioms
  AlgebraicGeometry.BasicOpenCocycleDatum.divFamZarAff_eq_of_picClass_eq_cechPicClass
#print axioms AlgebraicGeometry.rankOneDivisorUniqueness
#print axioms AlgebraicGeometry.canonicalRankOneDivisor_abel
#print axioms AlgebraicGeometry.canonicalRankOneDivisor_unique
#print axioms AlgebraicGeometry.stage_classDeg_all_fields
#print axioms AlgebraicGeometry.PicRankOneNoetherianStage.admissibility
#print axioms AlgebraicGeometry.PicRankOneNoetherianStage.exists_glued_divFamZarAff
#print axioms
  AlgebraicGeometry.PicRankOneLocalPresentation.exists_carrier_divFamZarAff_abel
#print axioms AlgebraicGeometry.existsUnique_abel_divFamZarAff_of_mem
#print axioms AlgebraicGeometry.divFamZarAff_eq_of_rankOne
#print axioms
  AlgebraicGeometry.PicRankOneEvaluationDivisorData.abelInverse_of_uniqueness
#print axioms AlgebraicGeometry.PicRankOneEvaluationDivisorData.rankOneAbelIso
#print axioms AlgebraicGeometry.canonicalRankOneSection
#print axioms AlgebraicGeometry.canonicalRankOneRepresenterTrans
#print axioms AlgebraicGeometry.canonicalRankOneEvaluationDivisorData
#print axioms AlgebraicGeometry.canonicalRankOneAbelIso
#print axioms AlgebraicGeometry.rankOneAbel_isOpenImmersion
#print axioms AlgebraicGeometry.isOpen_picRankOneSplitLocus_overSpec
#print axioms AlgebraicGeometry.PicRankOneNativePresentation.nonempty_of_pointwiseSplit
#print axioms AlgebraicGeometry.mem_picRankOneOpen_of_pointwiseSplit
#print axioms AlgebraicGeometry.picRankOneOpen_fibrePresented
#print axioms AlgebraicGeometry.picRankOneOpen_isOpen
#print axioms AlgebraicGeometry.exists_picRankOneTranslatedChart_fieldFactorization
#print axioms AlgebraicGeometry.picRankOneTranslatedChart_pointwiseCoverage
#print axioms AlgebraicGeometry.pic0_sepClosed_representableBy
#print axioms AlgebraicGeometry.locallyOfFiniteType_pic0_sepClosed_representableBy
#print axioms AlgebraicGeometry.quasiCompact_pic0SepClosedRepresenter
#print axioms AlgebraicGeometry.locallyOfFinitePresentation_pic0_sepClosed_representableBy
#print axioms AlgebraicGeometry.quasiSeparatedSpace_pic0SepClosedRepresenter
#print axioms AlgebraicGeometry.picRepDatumSepClosed
#print axioms AlgebraicGeometry.jacobianDataSepClosed
#print axioms AlgebraicJacobian.GaloisDescent.galoisQuotientUniversal_of_equivariant
#print axioms AlgebraicJacobian.GaloisDescent.galoisQuotientWitnessOfInvariantProjection
#print axioms AlgebraicJacobian.GaloisDescent.StableAffineOpen.isGaloisQuotient_glued
#print axioms
  AlgebraicJacobian.GaloisDescent.StableAffineOpen.hasGaloisQuotient_of_orbitsInAffineOpen
#print axioms AlgebraicJacobian.GaloisDescent.GaloisQuotientWitness.overHomEquiv
#print axioms AlgebraicJacobian.GaloisDescent.GaloisQuotientWitness.overHomEquiv_precomp
#print axioms AlgebraicJacobian.GaloisDescent.StableAffineOpen.gluedQuotientOverHomEquiv
#print axioms
  AlgebraicJacobian.GaloisDescent.StableAffineOpen.gluedQuotientOverHomEquiv_precomp
#print axioms AlgebraicGeometry.pic0GaloisInvariant_existsUnique_descend
#print axioms AlgebraicGeometry.pic0RestrictToGaloisInvariant_bijective
#print axioms AlgebraicGeometry.pic0GaloisInvariantEquiv
#print axioms AlgebraicGeometry.pic0GaloisInvariantEquiv_precomp
#print axioms AlgebraicGeometry.pic0GaloisInvariantEquivGaloisEquivariantOver
#print axioms AlgebraicGeometry.pic0GaloisInvariantEquivGaloisEquivariantOver_precomp
#print axioms AlgebraicGeometry.pic0RepresentableBy_finiteGaloisDescent
#print axioms AlgebraicJacobian.GaloisDescent.IsGaloisQuotient.locallyOfFiniteType
#print axioms AlgebraicJacobian.GaloisDescent.IsGaloisQuotient.quasiCompact
#print axioms AlgebraicGeometry.locallyOfFiniteType_pic0FiniteGaloisDescent
#print axioms AlgebraicGeometry.quasiCompact_pic0FiniteGaloisDescent
#print axioms AlgebraicGeometry.picRepDatum_finiteGaloisDescent
#print axioms AlgebraicGeometry.jacobianData_finiteGaloisDescent
#print axioms AlgebraicJacobian.affineRingGlueData
#print axioms AlgebraicGeometry.isOpenImmersion_of_fpqc_pushout
#print axioms AlgebraicGeometry.isOpenImmersion_of_tensorProduct
#print axioms AlgebraicJacobian.isPushout_scalarExtensionMapOfAlgHom
#print axioms AlgebraicGeometry.isPullback_specMap_scalarExtensionMapOfAlgHom
#print axioms AlgebraicGeometry.isOpenImmersion_scalarExtensionMapOfAlgHom
#print axioms AlgebraicGeometry.isIso_specMap_scalarExtensionMapOfAlgHom
#print axioms AlgebraicGeometry.isIso_specMap_of_fpqc_pushout
#print axioms AlgebraicGeometry.isIso_specMap_of_tensorProduct
#print axioms AlgebraicGeometry.isIso_specMap_of_tensorProduct_conjugate
#print axioms AlgebraicGeometry.isIso_specMap_of_fieldTower_tensorProducts
#print axioms AlgebraicJacobian.scalarExtensionMapOfAlgHom
#print axioms AlgebraicJacobian.scalarExtensionMapOfAlgHom_tower
#print axioms AlgebraicJacobian.scalarExtensionMapOfAlgHom_comp
#print axioms AlgebraicJacobian.scalarExtensionMapOfAlgHom_id
#print axioms AlgebraicJacobian.cancelBaseChange_tmul_baseChange
#print axioms AlgebraicJacobian.cancelBaseChange_naturality
#print axioms AlgebraicJacobian.tensorProductPushoutBaseChange
#print axioms AlgebraicJacobian.tensorProductPushoutBaseChange_tmul
#print axioms AlgebraicJacobian.tensorProductPushoutBaseChange_symm_tmul
#print axioms AlgebraicJacobian.finiteType_tensorProduct_over
#print axioms AlgebraicGeometry.DatG0.exists_finSubext_tensorProduct_preimage_finite
#print axioms AlgebraicGeometry.DatG0.exists_finSubext_tensorProduct_eq_finite
#print axioms AlgebraicGeometry.DatG0.tensorProduct_map_finSubext_injective
#print axioms
  AlgebraicGeometry.DatG0.exists_finSubext_fg_subalgebra_tensorProduct_factor
#print axioms
  AlgebraicGeometry.DatG0.exists_finSubext_finitePresentation_algebra_model
#print axioms
  AlgebraicGeometry.DatG0.exists_finSubext_finitePresentation_algebra_model_finite
#print axioms AlgebraicGeometry.DatG0.exists_finSubext_tensorProduct_algHom
#print axioms AlgebraicGeometry.DatG0.tensorProduct_algHom_eq_of_map_comp_eq
#print axioms AlgebraicGeometry.DatG0.tensorProduct_algHom_comp_eq_of_baseChange
#print axioms AlgebraicGeometry.DatG0.tensorProduct_algHom_triple_comp_eq_of_baseChange
#print axioms AlgebraicGeometry.DatG0.exists_finSubext_tensorProduct_algHom_finite
#print axioms AlgebraicGeometry.DatG0.exists_finSubext_tensorProduct_algHom_finite_of_models
#print axioms AlgebraicGeometry.DatG0.exists_finSubext_etale_model
#print axioms AlgebraicGeometry.DatG0.exists_finSubext_etaleCover_model
#print axioms AlgebraicGeometry.exists_finSubext_cechPic_model
#print axioms AlgebraicGeometry.exists_finSubext_relPic_model
#print axioms AlgebraicGeometry.exists_finSubext_baseChanged_cover_representation
#print axioms AlgebraicGeometry.BasicOpenCocycleDatum.exists_finSubext_tensorStage
#print axioms AlgebraicGeometry.exists_finSubext_relPic_tensorStage
#print axioms AlgebraicGeometry.exists_finSubext_relPic_tensorStage_finite
#print axioms AlgebraicGeometry.pic0FiniteStageUniversalChartClass_restrict_left
#print axioms AlgebraicGeometry.pic0FiniteStageUniversalChartClass_restrict_right
#print axioms AlgebraicGeometry.pic0FiniteStageUniversalAtlasClass
#print axioms AlgebraicGeometry.Scheme.exists_finite_affineCover_inter_isQuasiCompact
#print axioms AlgebraicGeometry.Scheme.finiteAffineOverlapPresentation
#print axioms AlgebraicGeometry.pic0FiniteStageAtlas
#print axioms AlgebraicGeometry.finitePresentation_pic0FiniteStageChartRing
#print axioms AlgebraicGeometry.exists_finSubext_pic0FiniteStageAtlas_chartRing_models
#print axioms AlgebraicGeometry.pic0FiniteStageAtlas_inter_isAffine
#print axioms AlgebraicGeometry.pic0FiniteStageAffineOverlap
#print axioms AlgebraicGeometry.pic0SepClosedAtlasOpenCover
#print axioms AlgebraicGeometry.pic0SepClosedAtlasGlueData
#print axioms AlgebraicGeometry.finitePresentation_pic0FiniteStageOverlapRing
#print axioms AlgebraicGeometry.finitePresentation_pic0FiniteStageRing
#print axioms AlgebraicGeometry.exists_finSubext_pic0FiniteStageAtlas_ring_models
#print axioms AlgebraicGeometry.pic0FiniteStageRestrictionLeft
#print axioms AlgebraicGeometry.pic0FiniteStageRestrictionRight
#print axioms AlgebraicGeometry.pic0FiniteStageRestriction
#print axioms AlgebraicGeometry.exists_finSubext_pic0FiniteStageRestriction_models
#print axioms AlgebraicGeometry.isOpenImmersion_of_tensorProduct_conjugate
#print axioms AlgebraicGeometry.isOpenImmersion_of_fieldTower_tensorProducts
#print axioms AlgebraicGeometry.isOpenImmersion_specMap_affineRestriction
#print axioms AlgebraicGeometry.isOpenImmersion_pic0FiniteStageRestriction
#print axioms
  AlgebraicGeometry.exists_finSubext_pic0FiniteStageRestriction_openImmersion_models
#print axioms AlgebraicGeometry.pic0FiniteStageTransition_inverse
#print axioms AlgebraicGeometry.pic0FiniteStageTransportedTransition_inverse
#print axioms AlgebraicGeometry.exists_finSubext_pic0FiniteStageTransition_models
#print axioms AlgebraicGeometry.isIso_specMap_pic0FiniteStageRestriction_diagonal_left
#print axioms AlgebraicGeometry.isIso_specMap_pic0FiniteStageModelRestriction_diagonal_left
#print axioms AlgebraicGeometry.pic0FiniteStageTransportedTransition_self
#print axioms AlgebraicGeometry.pic0FiniteStageTransitionModel_self
#print axioms AlgebraicGeometry.pic0FiniteStageTripleOpen_isAffine
#print axioms AlgebraicGeometry.isPushout_pic0FiniteStageTripleRing
#print axioms AlgebraicGeometry.pic0FiniteStageTripleTensorEquiv
#print axioms AlgebraicGeometry.pic0FiniteStageTripleTensorEquiv_tmul_one
#print axioms AlgebraicGeometry.pic0FiniteStageTripleTensorEquiv_one_tmul
#print axioms AlgebraicGeometry.finiteType_pic0FiniteStageTensorPushoutRing
#print axioms AlgebraicGeometry.finiteType_pic0FiniteStageTripleModelRing
#print axioms AlgebraicGeometry.pic0FiniteStageTripleModelBaseChange
#print axioms AlgebraicGeometry.finiteStageTensorPushoutFaceLeft
#print axioms AlgebraicGeometry.finiteStageTensorPushoutFaceRight
#print axioms AlgebraicGeometry.finiteStageTensorPushoutScalarExtension
#print axioms AlgebraicGeometry.finiteStageTensorPushoutScalarExtension_tmul
#print axioms AlgebraicGeometry.finiteStageTensorPushoutScalarExtension_faceLeft
#print axioms AlgebraicGeometry.finiteStageTensorPushoutScalarExtension_faceRight
#print axioms AlgebraicGeometry.finiteStageTensorPushoutScalarExtension_faceLeft_map
#print axioms AlgebraicGeometry.finiteStageTensorPushoutScalarExtension_faceRight_map
#print axioms AlgebraicGeometry.finiteStageTensorPushout_isPushout
#print axioms AlgebraicGeometry.finiteStageTensorPushoutAlgEquivOfIsPushout
#print axioms AlgebraicGeometry.finiteStageTensorPushoutAlgEquivOfIsPushout_faceLeft
#print axioms AlgebraicGeometry.finiteStageTensorPushoutAlgEquivOfIsPushout_faceRight
#print axioms AlgebraicGeometry.finiteStageTensorPushoutScalarExtension_named
#print axioms AlgebraicGeometry.finiteStageTensorPushoutComparisonSquare
#print axioms AlgebraicGeometry.finiteStageTensorPushoutMiddleComparison
#print axioms AlgebraicGeometry.finiteStageTensorPushoutComparison
#print axioms AlgebraicGeometry.finiteStageTensorPushoutComparison_faceLeft
#print axioms AlgebraicGeometry.finiteStageTensorPushoutComparison_faceRight
#print axioms AlgebraicGeometry.pic0FiniteStageTripleModelComparison
#print axioms AlgebraicGeometry.pic0FiniteStageTripleModelFaceLeft
#print axioms AlgebraicGeometry.pic0FiniteStageTripleModelFaceRight
#print axioms AlgebraicGeometry.pic0FiniteStageTripleModelComparison_faceLeft
#print axioms AlgebraicGeometry.pic0FiniteStageTripleModelComparison_faceRight
#print axioms AlgebraicGeometry.pic0FiniteStageTripleModelComparisonFamily
#print axioms AlgebraicGeometry.pic0FiniteStageTransportedTripleTransitionOfModels
#print axioms AlgebraicGeometry.pic0FiniteStagePairModelComparisonTransition
#print axioms AlgebraicGeometry.pic0FiniteStageTransportedTripleTransition_fac
#print axioms AlgebraicGeometry.pic0FiniteStageModelBaseChangeEquiv
#print axioms AlgebraicGeometry.pic0FiniteStageModelBaseChangeEquiv_naturality
#print axioms AlgebraicGeometry.tensorPushoutAlgEquivCongr
#print axioms AlgebraicGeometry.tensorPushoutAlgEquivCongr_faces
#print axioms AlgebraicGeometry.pic0FiniteStageModelBaseChangeEquiv_restrictionLeft
#print axioms AlgebraicGeometry.pic0FiniteStageTripleTransition
#print axioms AlgebraicGeometry.pic0FiniteStageTripleTransition_fac
#print axioms AlgebraicGeometry.pic0FiniteStageTripleTransition_cocycle
#print axioms AlgebraicGeometry.pic0FiniteStageTransition_self
#print axioms AlgebraicGeometry.pic0FiniteStageTransportedTripleTransition
#print axioms
  AlgebraicGeometry.exists_finSubext_pic0FiniteStageTripleTransition_models_of_comparisons
#print axioms AlgebraicGeometry.pic0FiniteStageTransportedTripleTransition_cocycle
#print axioms AlgebraicGeometry.pic0FiniteStageTripleTransitionModel_cocycle
#print axioms AlgebraicGeometry.scalarExtensionMapOfAlgHom_tower_finSubext
#print axioms
  AlgebraicGeometry.scalarExtensionMapOfPairModel_eq_pairModelComparisonTransition
#print axioms AlgebraicGeometry.pic0FiniteStageTripleTransitionModel_fac
#print axioms AlgebraicGeometry.conjugateAlgHom_threeCycle
#print axioms AlgebraicGeometry.pic0FiniteStageAffineTripleTransition_cocycle
#print axioms AlgebraicGeometry.conjugateAlgHom_face_of_squares
#print axioms AlgebraicGeometry.pic0FiniteStageAffineTripleTransition_fac
#print axioms AlgebraicGeometry.pic0FiniteStageAffineRingGlueData
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.glueData
#print axioms AlgebraicGeometry.exists_pic0FiniteStageGluePackage
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.gluedMap
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.gluedOver
#print axioms AlgebraicGeometry.pic0FiniteStageFinalBaseChangeEquiv
#print axioms AlgebraicGeometry.pic0FiniteStageFinalBaseChangeEquiv_naturality
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.glueData_ι_gluedMap
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.chartBaseChangeIso
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.affineBaseChangeIso_naturality
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.baseChangeGluingIso
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingChartIso
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.overlapBaseChangeIso
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.glueData_f
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.restrictionBaseChangeMap
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.chartRingBaseChangeIso
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.overlapRingBaseChangeIso
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.affineBaseChangeIso_trans_naturality
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.restrictionBaseChangeMap_naturality
#print axioms AlgebraicGeometry.nestedPullbackFlatteningIso
#print axioms AlgebraicGeometry.nestedPullbackFlatteningIso_hom_comp_fst_comp_a
#print axioms AlgebraicGeometry.nestedPullbackFlatteningIso_hom_comp_fst_comp_b
#print axioms AlgebraicGeometry.nestedPullbackFlatteningIso_hom_comp_snd
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingOverlapFlatteningIso
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingOverlapFlatteningIso_hom_comp_fst_comp_f
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingOverlapFlatteningIso_hom_comp_fst_comp_t_f
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingOverlapFlatteningIso_hom_comp_snd
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.glueData_f_comp_inclusion_comp_gluedMap
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.exactRestrictionAlgHom_fromSpec
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.restrictionBaseChangeRingHom
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.finitePresentation_pic0FiniteStageChartBaseChangeRing
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.finiteType_pic0FiniteStageChartBaseChangeRing
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.restrictionBaseChangeMap_fst
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.restrictionBaseChangeMap_snd
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingChartIso_hom_ι
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.overlapBaseChangeIso_hom_atlas_t_f_ι
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingOverlapIso_pre_fst
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingOverlapIso
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingOverlapIso_fst
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.transition_comp_restrictionLeft_eq_restrictionRight
#print axioms
  transportedMap_transition_comp_restrictionLeft_eq_right
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.mapM_transition_comp_restrictionLeft_eq_right
#print axioms
  scalarExtension_transition_comp_restrictionLeft_eq_right
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.rightRestrictionBaseChangeAlgHom
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.rightRestrictionBaseChangeAlgHomPinned
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.rightRestrictionBaseChangeRingHom
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.rightRestrictionBaseChangeAlgHom_eq_direct
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.exactRightRestrictionAlgHom
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.rightRestrictionFinalBaseChangeEquiv_naturality
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.rightRestrictionBaseChangeMap
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.rightRestrictionBaseChangeMap_naturality
#print axioms
  AlgebraicGeometry.Pic0FiniteStageGluePackage.rightRestrictionBaseChangeMap_fromSpec
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingOverlapIso_snd
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.gluingGluedIso
#print axioms AlgebraicGeometry.Pic0FiniteStageGluePackage.finiteStageBaseChangeIso
#print axioms AlgebraicGeometry.pic0PreservesFilteredBaseColimit_of_representableBy
#print axioms AlgebraicGeometry.pic0RepresentableBy_of_baseChangeObjectIso
#print axioms
  AlgebraicGeometry.BasicOpenCocycleDatum.exists_glued_divFamZarAff_of_admissible_fibre
