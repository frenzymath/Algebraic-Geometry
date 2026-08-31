import AlgebraicJacobian.Cohomology.FlatBaseChange
import AlgebraicJacobian.Cohomology.FlatBaseChangeGlobal
import AlgebraicJacobian.Cohomology.RegroupHelper
import AlgebraicJacobian.Cohomology.SheafCompose
import AlgebraicJacobian.Cohomology.StructureSheafAb
import AlgebraicJacobian.Cohomology.StructureSheafModuleK
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.SectionsBridge
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.AffineDegreeOneVanishing
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.QuasicoherentDegreeOneVanishing
import AlgebraicJacobian.Cohomology.MayerVietorisCore
import AlgebraicJacobian.Cohomology.MayerVietorisCover
-- Čech-cohomology development merged from the Cech-Cohomology subproject
-- (enrich merge, 2026-06-18). Closes the formerly-orphaned CechNerve / Rⁱf_*
-- Čech lane: pushPullFunctor + pushPullMap_comp + cech_computes_higherDirectImage.
import AlgebraicJacobian.Cohomology.HigherDirectImage
import AlgebraicJacobian.Cohomology.HigherDirectImagePresheaf
import AlgebraicJacobian.Cohomology.CechHigherDirectImage
import AlgebraicJacobian.Cohomology.CechAcyclic
import AlgebraicJacobian.Cohomology.CechCoboundarySplitting
import AlgebraicJacobian.Cohomology.AcyclicResolution
import AlgebraicJacobian.Cohomology.PresheafCech
import AlgebraicJacobian.Cohomology.FreePresheafComplex
import AlgebraicJacobian.Cohomology.CechBridge
import AlgebraicJacobian.Cohomology.AbsoluteCohomology
import AlgebraicJacobian.Cohomology.CechToCohomology
import AlgebraicJacobian.Cohomology.TildeExactness
import AlgebraicJacobian.Cohomology.AffineSerreVanishing
import AlgebraicJacobian.Cohomology.QcohRestrictBasicOpen
import AlgebraicJacobian.Cohomology.QcohTildeSections
import AlgebraicJacobian.Cohomology.CechSectionComplex
import AlgebraicJacobian.Cohomology.CechSectionIdentificationBase
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLeg
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLegMid1
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLegMid2
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLegTop
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLegAux
import AlgebraicJacobian.Cohomology.CechSectionAugmentationComparison
import AlgebraicJacobian.Cohomology.CechSectionIdentification
import AlgebraicJacobian.Cohomology.CechSectionContractibility
import AlgebraicJacobian.Cohomology.CechAugmentedResolution
import AlgebraicJacobian.Cohomology.OpenImmersionPushforward
import AlgebraicJacobian.Cohomology.CechTermAcyclic
import AlgebraicJacobian.Cohomology.CechToHigherDirectImage
import AlgebraicJacobian.Cohomology.ModulesCoverConservativity
-- Affine essential-image heart of the open-immersion Beck–Chevalley (Stacks 02KG)
import AlgebraicJacobian.Cohomology.AffinePushPullEssImage
-- Pullback of quasi-coherent modules along an arbitrary morphism (Stacks 01BG)
import AlgebraicJacobian.Cohomology.PullbackQuasicoherent
-- Target-local roadmap nodes preserved across the merge (unconditional Rⁱf_*
-- packaging + Čech flat base change, Stacks 02KH) — see file header.
import AlgebraicJacobian.Cohomology.CechHigherDirectImageUnconditional
import AlgebraicJacobian.Cohomology.CechTwistedCoherenceReduction
import AlgebraicJacobian.Genus
import AlgebraicJacobian.RigidityLemma
-- Smooth ⟹ geometrically reduced (mathlib-general, upstreaming candidate). Supplies
-- `GeometricallyIntegral` for the challenge's curve hypotheses, which is what the whole
-- Picard/FGA development runs under.
import AlgebraicJacobian.Curve.GeometricallyReduced
import AlgebraicJacobian.Curve.FiniteLevelRationalPoint
import AlgebraicJacobian.Curve.GaloisLevelRationalPoint
import AlgebraicJacobian.Curve.SeparablyClosedRationalPoint
import AlgebraicJacobian.Jacobian
import AlgebraicJacobian.AbelJacobi
import AlgebraicJacobian.Picard.RelativeSpec
import AlgebraicJacobian.Picard.SectionRingUniversal
import AlgebraicJacobian.Picard.StructureSheafPushforward
import AlgebraicJacobian.Picard.RigidPushforward
import AlgebraicJacobian.Picard.RigidPushforwardTransfer
import AlgebraicJacobian.Picard.RigidPushforwardP1Engine
-- Rigid-pushforward gate cone (run 0053, task ajc-gate). The gate is DISCHARGED (see the
-- Instance/GammaBaseChange/P1Witness entries below); `hasRigidPushforward_of_leaves` is a
-- four-leaf factorization of it, kept as a decomposition, no longer a frontier.
-- The gate is NOT the top of its own cone: RigidPushforwardP1Sheaf imports it and
-- RigidPushforwardFiberChart sits beside it (over Transfer + P1Engine), so both are
-- ABOVE the gate. RigidPushforwardFrontier imports all three and is the single entry
-- point; the other entries are kept explicit so that retiring Frontier cannot silently
-- unroot them.
import AlgebraicJacobian.Picard.RigidPushforwardGate
import AlgebraicJacobian.Picard.RigidPushforwardFiberChart
import AlgebraicJacobian.Picard.RigidPushforwardP1Sheaf
import AlgebraicJacobian.Picard.RigidPushforwardFrontier
-- Aimed at the gate's H0-finiteness leaf: the P^1 chart-ring identification over the
-- integral model. Sits over Adelic.P1ChartData, beside the cone rather than under it.
import AlgebraicJacobian.Picard.RigidPushforwardP1ChartRing
-- Second wave of the same cone (run 0053, task ajc-gate). None of these is below
-- another: AffineDescent sits over Transfer + PullbackQuasicoherent, P1Topology over
-- Adelic.FinitenessP1, P1ChartSections over P1ChartRing, and Rank over P1Sheaf +
-- FiberChart. Four separate entries, for the same reason the first wave needed them.
import AlgebraicJacobian.Picard.RigidPushforwardAffineDescent
import AlgebraicJacobian.Picard.RigidPushforwardP1Topology
import AlgebraicJacobian.Picard.RigidPushforwardP1ChartSections
import AlgebraicJacobian.Picard.RigidPushforwardRank
-- The assembly above all four: `IsIntegral ℙ¹_k` and the rank identity are theorems, so the
-- gate's `locallyFree` field is unconditional.
import AlgebraicJacobian.Picard.RigidPushforwardInstance
-- The gate's second field and its chart-level input. ChartBaseChange sits over FiberChart;
-- GammaBaseChange imports it and Instance, proves the residual Γ-level base-change statement,
-- and carries the resulting `instHasRigidPushforwardOfCurve` — a real global instance, measured
-- clean AT THE SYNTHESIS SITE together with the three extraction theorems that now synthesize
-- rather than assume it (scripts/axiom-frontier.lean §6c).
import AlgebraicJacobian.Picard.RigidPushforwardChartBaseChange
import AlgebraicJacobian.Picard.RigidPushforwardGammaBaseChange
-- Non-vacuity of that instance, which is not a formality: a theorem quantified over three
-- hypotheses is worth nothing if nothing satisfies them, and §6c trap (c) is exactly this
-- failure mode. ℙ¹ over an arbitrary field satisfies all three, and the gate fires at it.
import AlgebraicJacobian.Picard.RigidPushforwardP1Witness
import AlgebraicJacobian.Picard.P1SectionsFinite
import AlgebraicJacobian.Picard.TwoTermFiniteFree
import AlgebraicJacobian.Picard.SemicontinuityH0
-- The B5 (h⁰ upper semicontinuity) cluster.  Rooted 2026-07-29 (`ajc-p4`) after `ajc-p2`
-- found the six modules formed a closed island with no importer outside itself (I-1058,
-- I-1061): every one of them compiled under `lake env lean`, but no build from this
-- umbrella ever saw them, so an axiom measurement "from the root" could not reach their
-- declarations.  Rooting them is what makes the earlier per-file measurements mean at the
-- umbrella what they were reported to mean.
import AlgebraicJacobian.Picard.PointRankSemicontinuity
import AlgebraicJacobian.Picard.PointRankSemicontinuityWitness
import AlgebraicJacobian.Picard.FiberRankSemicontinuity
import AlgebraicJacobian.Picard.TwoTermKernelSemicontinuity
import AlgebraicJacobian.Picard.FiberH0Comparison
import AlgebraicJacobian.Picard.FiberH0CechKernel
import AlgebraicJacobian.Picard.H0SemicontinuityInstance
-- The degree-at-most-one analogue: identify the intrinsic scheme-fibre Euler index with
-- the base-changed family Cech complex and consume a finite two-term replacement.
import AlgebraicJacobian.Picard.SchemeEulerIndex
-- Milne §I.1 Cor 1.2 and 1.4 over an ARBITRARY base field: the two geometric inputs the
-- (already field-agnostic) Albanese engine consumes, with the `IsAlgClosed` binder removed.
import AlgebraicJacobian.Albanese.AVRigidityArbitraryField
-- Milne III.6.1 and `IsAlbanese` over an arbitrary base field: headline obligation 5's
-- field hypothesis is not owed.  Its content (Sym^g C, the descent datum, Abel-Jacobi) is.
import AlgebraicJacobian.Albanese.AlbaneseArbitraryField
import AlgebraicJacobian.Picard.DivDegree
import AlgebraicJacobian.Picard.DivFamilyZero
import AlgebraicJacobian.Picard.DivFamilyZeroAbel
import AlgebraicJacobian.Picard.FinitePresentationFunctor
import AlgebraicJacobian.Picard.FiniteGaloisQuotient
import AlgebraicJacobian.Picard.FiniteGaloisQuotientAffine
import AlgebraicJacobian.Picard.StableAffineCover
import AlgebraicJacobian.Picard.GaloisQuotientNonVacuity
import AlgebraicJacobian.Picard.GaloisQuotientGlue
import AlgebraicJacobian.Picard.GaloisDescent.InvariantQuotientOpen
import AlgebraicJacobian.Picard.GaloisDescent.GaloisQuotientUniqueness
import AlgebraicJacobian.Picard.GaloisDescent.GaloisQuotientRestrict
import AlgebraicJacobian.Picard.GaloisDescent.GaloisQuotientOverlap
import AlgebraicJacobian.Picard.PicEtGaloisQuotient
import AlgebraicJacobian.Picard.GaloisQuotientAffineGeneral
import AlgebraicJacobian.Picard.LineBundlePullback
import AlgebraicJacobian.Picard.TensorObjSubstrate
import AlgebraicJacobian.Picard.TensorObjSubstrate.DualInverse
-- Comparison-iso substrate merged from the Line-Bundle-Comparison-Iso
-- subproject (T1 merge, 2026-07-02). Headline: exists_tensorObj_inverse
-- (the L ⊗ L⁻¹ ≅ O_C keystone) proved sorry-free in TensorObjInverse,
-- via the DUAL/D3′ route (PresheafDualPullback* + PullbackTensorMapIso +
-- TrivialisationRestrict). PullbackTensorComp.lean was retired in the
-- merge: its D3′ lemma set was absorbed into TensorObjSubstrate.lean
-- (proved), and its remaining helpers had no consumers.
import AlgebraicJacobian.Picard.TensorObjSubstrate.DualInverse.PresheafDualPullback
import AlgebraicJacobian.Picard.TensorObjSubstrate.DualInverse.PresheafDualUnitPullback
import AlgebraicJacobian.Picard.TensorObjSubstrate.DualInverse.PresheafDualPullbackNatural
import AlgebraicJacobian.Picard.TensorObjSubstrate.PullbackTensorMapIso
import AlgebraicJacobian.Picard.TensorObjSubstrate.PullbackTensorIso
import AlgebraicJacobian.Picard.PullbackTensorOneSided
import AlgebraicJacobian.Picard.TensorObjSubstrate.TrivialisationRestrict
import AlgebraicJacobian.Picard.TensorObjInverse
import AlgebraicJacobian.Picard.RelPicFunctor
import AlgebraicJacobian.Picard.GeometricallyConnectedSection
import AlgebraicJacobian.Picard.FGAPicRepresentability
import AlgebraicJacobian.Picard.PicEtSubcanonical
import AlgebraicJacobian.Picard.EtaleFieldCover
import AlgebraicJacobian.Picard.PicEtCrossBase
import AlgebraicJacobian.Picard.PicEtDescentAssembly
import AlgebraicJacobian.Picard.PicEtDescentExistence
import AlgebraicJacobian.Picard.PicEtDescentGoal
import AlgebraicJacobian.Picard.PicEtDescentNecessity
import AlgebraicJacobian.Picard.PicEtDescentRepresentability
import AlgebraicJacobian.Picard.PicEtInvariantMatch
import AlgebraicJacobian.Picard.PicEtPointedReduction
import AlgebraicJacobian.Picard.PicEtQuotientHom
import AlgebraicJacobian.Picard.QuasiProjectiveFiniteInAffine
import AlgebraicJacobian.Picard.RepresentableByTerminal
import AlgebraicJacobian.Picard.PicEtSeparated
import AlgebraicJacobian.Picard.RigidifiedPic
import AlgebraicJacobian.Picard.IdentityComponent
import AlgebraicJacobian.Picard.TangentSpaceDualNumbers
import AlgebraicJacobian.Picard.TangentSpaceSchemePoints
import AlgebraicJacobian.Picard.TangentSpaceStalkAlgebra
import AlgebraicJacobian.Picard.TangentSpaceIdentitySection
import AlgebraicJacobian.Picard.DualNumberUnits
import AlgebraicJacobian.Picard.NilpotentThickeningFree
import AlgebraicJacobian.Picard.DualNumberChartTriviality
import AlgebraicJacobian.Picard.GroupSchemeSmoothAlgClosed
import AlgebraicJacobian.Picard.Pic0AbelianVariety
-- The A.3 dimension leg and the ambient-properness refutation (run 0067 r5/r6).
-- Rooted here per inbox I-0600 / I-0659: an unrooted module is invisible to the
-- workspace axiom probe, which walks the cone of THIS file. `Pic0Dimension`
-- transitively pulls in `SchemeKrullDimStalk`.
import AlgebraicJacobian.Picard.EmbeddingDimensionBound
import AlgebraicJacobian.Picard.Pic0Dimension
-- The ETALE tangent-space/dimension leg (run 0084, ajc-p2): the same Kleiman §5
-- `thm:tgtsp` chain at `Pic0SchemeEt`, the object the headline binds. Rooted here
-- for the same reason as `Pic0Dimension` above -- the axiom probe walks this cone.
import AlgebraicJacobian.Picard.Pic0EtTangentSpace
-- The ETALE smoothness/properness leg (run 0085, ajc-p3): the `k̄` and valuative
-- reductions of `Pic0Et.geometricallyReduced` / `Pic0Et.universallyClosed`, the two
-- `Pic0Et` obligations of `picardJacobianWitness`. Rooted here for the same reason.
import AlgebraicJacobian.Picard.Pic0EtStructure
-- Cluster D' pushforward-flatness inputs (run 0085 r0, ajc-p3). Rooted late, in r1:
-- the module was verified only by `lake env lean` on the file itself, and my r0 note
-- cited a root `lake build` job count that never compiled it (measured by ajc-p2,
-- I-1058 / I-1060). Rooting it makes the axiom probe's cone honest for these five
-- declarations, per the same I-0600 / I-0659 reason as `Pic0Dimension` above.
import AlgebraicJacobian.Picard.DivPushforwardFlat
-- D3' substrate: the matrix-defined rank stratum is locally free of its indexed rank;
-- in rank one it is an immersed universal locus carrying an invertible sheaf.
import AlgebraicJacobian.Picard.DivLocallyClosed
import AlgebraicJacobian.Picard.DivGrassmannianCandidate
-- The quasi-finiteness binder that every `DivPushforwardFlat` theorem carries, reduced
-- to fibre finiteness (run 0095 r5, pic-e): two of the three inputs mathlib's criteria
-- want are free from `DivFamily.properSupport`, so the binder is one topological
-- statement about the fibres of `D -> T`, not an affine-local `RingHom.QuasiFinite`
-- condition. Rooted so the axiom probe sees the whole cone.
import AlgebraicJacobian.Picard.DivSupportQuasiFinite
-- Carrier bridge (a) for `divzero` (pic-e 0105 r4): support commutes with base change for
-- a finite module, `Supp_B (B ⊗ M) = comap⁻¹ (Supp_A M)`. Supplies the REVERSE support
-- inclusion that `QuotSupportBaseChange`'s forward annihilator inclusion lacks, identifying
-- the support-of-fibre and fibre-of-support carriers of `isFinite_support_of_fibers`.
-- Rooted so the axiom probe sees it in the cone.
import AlgebraicJacobian.Picard.SupportBaseChange
-- The geometric input left by the reduction above: an effective Cartier divisor on a
-- proper smooth geometrically integral curve has finite fibres. This module consumes
-- that fact and registers the exact instance required by `DivPushforwardFlat`.
import AlgebraicJacobian.Projective.EffectiveCartierSupport
-- Headline leaf B in the etale formulation (run 0084 r2, ajc-p2): leaf B implies the
-- reducedness obligation, so the headline's five are not independent; plus what leaf
-- B's own residue is (an affine-chart Omega-rank count, not a tangent space).
import AlgebraicJacobian.Picard.Pic0EtRelativeDimension
-- Headline obligation 3, costed (run 0086 r3, ajc-p4): the two ingredients of the
-- properness residue that are FREE (compactness of Pic^0, and specialization-lifting
-- at the one-point base -- so the whole obligation is in the `universally`), plus two
-- reformulations proved to be RENAMINGS by exhibiting their converses. Rooted next to
-- `AmbientPicNotProper` because `compactSpace` is the invariant that file's refutation
-- turns on: it checks that Pic^0 escapes, where the ambient object does not.
import AlgebraicJacobian.Picard.Pic0EtProperImage
import AlgebraicJacobian.Picard.AmbientPicNotProper
import AlgebraicJacobian.Picard.GroupSchemeHomogeneity
import AlgebraicJacobian.Picard.HomogeneityOrbitCollapse
import AlgebraicJacobian.Picard.FlatteningStratification
import AlgebraicJacobian.Picard.EntryIdeal
import AlgebraicJacobian.Picard.EntryIdealStratum
import AlgebraicJacobian.Picard.FlatteningStratificationUniversal
import AlgebraicJacobian.Picard.GenericFlatnessGeometric
import AlgebraicJacobian.Picard.HilbertPolynomial
import AlgebraicJacobian.Picard.QuotScheme
-- Grassmannian/Quot representability development merged from the
-- GR-quot_closure subproject (union merge, 2026-06-22). Headline:
-- AlgebraicGeometry.Grassmannian.represents (rank-d quotient functor
-- representability) + the section graded ring/module lane, all sorry-free.
import AlgebraicJacobian.Picard.GradedHilbertSerre
import AlgebraicJacobian.Picard.SectionGradedRing
import AlgebraicJacobian.Picard.GrassmannianCells
import AlgebraicJacobian.Picard.GlueDescent
import AlgebraicJacobian.Picard.GrassmannianQuot
import AlgebraicJacobian.Picard.ScalarEndFaithful
import AlgebraicJacobian.Picard.QuotFunctorDef
-- T14 ampleness / projective-morphism / Serre-finiteness foundation:
-- relative projective space, Serre twist O(m), projective-with-L predicate.
import AlgebraicJacobian.Picard.ProjectiveSpace
import AlgebraicJacobian.Picard.SerreTwist
-- Option-B Phase 0 (Serre-finiteness lane): the glued-sheaf Γ-section API —
-- Γ(glue D M g, ⊤) ≅ compatible families, instantiated at O(m).
import AlgebraicJacobian.Picard.SerreTwistSections
import AlgebraicJacobian.Picard.InvertibleGrBridge
import AlgebraicJacobian.Picard.GradedPiecesFinite
import AlgebraicJacobian.Picard.ChartSectionsFinite
import AlgebraicJacobian.Picard.ProjectiveMorphism
import AlgebraicJacobian.Picard.FiniteMorphismEmbedding
import AlgebraicJacobian.Picard.FiniteMapProjectiveGluing
import AlgebraicJacobian.Picard.CurveProjectivity
import AlgebraicJacobian.Picard.SerreFiniteness
import AlgebraicJacobian.Picard.ZariskiDescentRepresentability
import AlgebraicJacobian.Picard.GrassmannianZariskiSheaf
import AlgebraicJacobian.Picard.GrassmannianRepresentability
-- I-0118 honest restatement of thm:quot_representable (projective π with
-- very ample L via IsProjectiveWith, coherent E), split out of QuotFunctorDef.
import AlgebraicJacobian.Picard.QuotRepresentability
-- Wave-2 leaf bricks (2026-07-07): schematic-support / annihilator lane for
-- gammaFiber, and the tensor section-comparison lane for pullbackTensorMap_isIso.
import AlgebraicJacobian.Picard.SchematicSupport
import AlgebraicJacobian.Picard.TensorSectionFormula
import AlgebraicJacobian.Picard.TensorStalkLocalization
import AlgebraicJacobian.Picard.AffineOpenStalkLocalization
import AlgebraicJacobian.Picard.LineBundleCoherence
import AlgebraicJacobian.RiemannRoch.WeilDivisor
-- AJC.rr.principal carrier comparisons (2026-07-28): the two index sets used for
-- divisors on a curve agree (X.PrimeDivisor ≃ non-generic points, ajc-rr), lifted to
-- divisors and their degree — the first of the two mismatches costing the sibling
-- χ-ledger port. Rooted here per I-0362: a module with no importer is never elaborated.
import AlgebraicJacobian.RiemannRoch.CurveCoheight
import AlgebraicJacobian.RiemannRoch.CurveDivisorIndexBridge
-- Adelic Riemann-Roch lane (2026-07-07): Weil repartitions as the concrete
-- 2-affine-cover cokernel; keystone = H^1(C, O_C) finiteness via a finite map
-- to P^1 (design: RiemannRoch_Adelic blueprint chapter).
import AlgebraicJacobian.RiemannRoch.Adelic.Substrate
import AlgebraicJacobian.RiemannRoch.Adelic.Cokernel
import AlgebraicJacobian.RiemannRoch.Adelic.P1BaseCase
import AlgebraicJacobian.RiemannRoch.Adelic.FinitenessP1
import AlgebraicJacobian.RiemannRoch.Adelic.FiniteMapToP1
import AlgebraicJacobian.RiemannRoch.Adelic.P1ChartData
import AlgebraicJacobian.RiemannRoch.Adelic.ChiLedger
import AlgebraicJacobian.RiemannRoch.Adelic.NonconstantToP1
import AlgebraicJacobian.RiemannRoch.Adelic.GenusFiniteness
import AlgebraicJacobian.RiemannRoch.Adelic.CechComparisonGate
import AlgebraicJacobian.RiemannRoch.Adelic.CechAcyclicInstance
import AlgebraicJacobian.RiemannRoch.Adelic.GateInstances
import AlgebraicJacobian.RiemannRoch.Adelic.GenusUnconditional
-- Cluster-P χ-ledger extensions (run 0055, task ajc-rr). Each imports the
-- previous; ClassInvariance sits over the already-rooted Adelic.ChiLedger.
-- NB several keystones here are axiom-clean but CONDITIONAL in their statements:
-- they take the closed ledger and/or a peel-surjectivity datum as named
-- hypotheses, so `#print axioms` alone overstates them.
import AlgebraicJacobian.RiemannRoch.Adelic.ClassInvariance
import AlgebraicJacobian.RiemannRoch.Adelic.SectionBounds
import AlgebraicJacobian.RiemannRoch.Adelic.BoundedVanishing
-- Global generation and the ledger closure (run 0055, task ajc-rr). LedgerClosure
-- imports GlobalGeneration, so the second entry alone would root both; both are kept
-- explicit so retiring either cannot silently unroot the other. Same caveat as above:
-- the generation lane takes the closed χ-ledger as a named hypothesis, so a clean
-- `#print axioms` on it is not an unconditional theorem. There is NO exception here:
-- `hasRationalResidues_of_isAlgClosed` takes no ledger, but its obligations sit in three
-- instance binders that nothing constructs for a bare `Scheme`, so it is a relocation
-- rather than a discharge (scripts/axiom-frontier.lean §6e).
import AlgebraicJacobian.RiemannRoch.Adelic.GlobalGeneration
import AlgebraicJacobian.RiemannRoch.Adelic.LedgerClosure
-- Residue degree one on the curve's own hypotheses. This is the module that turned the
-- retracted "discharge" above into a real one: it routes around the stalk residue-field
-- finiteness binder via mathlib's `residueFieldIsoBase`, so the obligation is no longer
-- parked in an instance nothing constructs (scripts/axiom-frontier.lean §6e).
import AlgebraicJacobian.RiemannRoch.Adelic.ResidueField
-- The UNGATED Čech Euler characteristic and its consequences (run 0055, task ajc-rr).
-- `ChiUnconditional` is where `χ` is computed as inclusion–exclusion over the two charts with
-- no exact sequence and no exactness hypotheses, which is what makes its conclusions
-- independent of the `chi_add` machinery. That independence is the point: a refutation of a
-- hypothesis routed through `chi_add` measures `chi_add`, not the hypothesis
-- (scripts/axiom-frontier.lean §2b records a retraction of exactly that shape).
import AlgebraicJacobian.RiemannRoch.Adelic.ChiUnconditional
-- 2026-07-28 (ajc-rr, request I-0547): the chart-finiteness binder of those refutations is
-- UNSATISFIABLE on a curve — one instance at D = 0 forces K(X)/k finite — so `hbump` and the
-- closed ledger are OPEN there rather than refuted. Rooted so the refutation-of-the-refutation
-- is elaborated alongside what it corrects.
import AlgebraicJacobian.RiemannRoch.Adelic.ChartFinitenessRefuted
import AlgebraicJacobian.RiemannRoch.Adelic.UniformChartVanishing
import AlgebraicJacobian.RiemannRoch.CurveBaseChange
import AlgebraicJacobian.RiemannRoch.CohomologyKit
-- The RiemannRoch/Ledger cone and the homogeneity collapse, rooted 2026-07-29 on the
-- standing request of inbox I-0600 (filed by ajc-rr, whose own write scope excludes this
-- roll-up).  Until these lines landed, 21 committed modules were outside the root import
-- closure, so `lake build AlgebraicJacobian` never elaborated them and no `#print axioms`
-- line in `scripts/axiom-frontier.lean` -- which imports only `AlgebraicJacobian` -- could
-- even be written for their declarations.  That is trap (5) of TO_USER.md, and it applied
-- to the project's strongest Riemann-Roch statements: `chi_divisorSheaf_genus`
-- (Ledger.GenusBridge) and `FiberBound.exists_bound_h0_eq_genus_curve` carry the three
-- curve binders and nothing else.
--
-- FOUR LEAVES, NOT TWENTY-ONE.  These are exactly the modules of the unrooted set that no
-- other unrooted module imports; their transitive closure covers all 21, verified by
-- import walk rather than assumed.  Adding the dominated modules explicitly would be
-- redundant, and the redundancy would rot as the cone's internal edges change.  The
-- converse risk -- that retiring one of these four silently unroots a subtree -- is the
-- reason each is named with its cone below rather than folded into one line.
--
-- `Ledger.P1Vanishing` drags the vanishing/section-drop/qcoh layer (VanishingFieldDescent,
-- NonVacuity, DegreeVanishing, SectionDrop, AffineVanishingQcoh, DivisorSheafQcoh,
-- QcohSections, SectionsFieldBaseChange, GenusFieldInvariance) and is itself the first
-- *witnessed* `UniformVanishing`: `h¹(𝒪_{ℙ¹}) = 0` over every field, no gate.
import AlgebraicJacobian.RiemannRoch.Ledger.P1Vanishing
-- `Ledger.PrincipalTransport` drags PrincipalCompare and carries
-- `degree_principal_eq_zero_of_isAlgClosed`, the `k = k̄` case of `WeilDivisor.principal_degree_zero`.
import AlgebraicJacobian.RiemannRoch.Ledger.PrincipalTransport
-- `Ledger.FiberBound` drags the fibrewise large-twist layer (FiberChart, FiberDivisor,
-- FiberLattice, FiberVanishing, ExtensionUniformity) and `LedgerPortability` the
-- universe-gap record plus `GenusBridge`'s χ-ledger headline.
import AlgebraicJacobian.RiemannRoch.Ledger.FiberBound
-- Source-side fiber coordinates, factored out of the choice of a projective-line model and
-- stable under arbitrary field base change.
import AlgebraicJacobian.RiemannRoch.Ledger.FiberCoordinateData
import AlgebraicJacobian.RiemannRoch.Ledger.FiberCoordinateDivisor
import AlgebraicJacobian.RiemannRoch.Ledger.FiberCoordinateLattice
-- `Ledger.BaseDivisorEveryField` splits `UniformBaseDivisor` into its existence and degree
-- clauses. `Ledger.FixedFiberDegree` closes the latter: one fixed source coordinate divisor
-- base-changes to every field, its H0 kernel and H1 vanishing commute with that base change,
-- and Riemann--Roch makes its degree independent of the extension. Thus it produces both
-- `UniformBaseDivisor` and `UniformVanishing` without an additional hypothesis.
import AlgebraicJacobian.RiemannRoch.Ledger.BaseDivisorEveryField
import AlgebraicJacobian.RiemannRoch.Ledger.FixedFiberDegree
import AlgebraicJacobian.RiemannRoch.LedgerPortability
-- Not Riemann-Roch: the orbit condition of the A.3 dimension leg is strong enough to force
-- `dim = 0`, so it is a refutation of its own predecessor's reading rather than a step.
import AlgebraicJacobian.Picard.HomogeneityOrbitCollapse
import AlgebraicJacobian.Picard.InvertibleSectionLocalization
import AlgebraicJacobian.Picard.GaloisDescent.SemilinearModules
import AlgebraicJacobian.Picard.GaloisDescent.SemilinearAlgebras
-- Campaign `G2(c)` layer 2, algebra half: the semilinear action descends to a
-- localization at an INVARIANT element, and is still semilinear there — so the
-- Speiser engine above applies to a localized chart with no new descent argument.
-- Invariance of the element is spent exactly once, on `powers_map_eq`.
import AlgebraicJacobian.Picard.GaloisDescent.InvariantsLocalization
-- The Galois splitting `L ⊗[K] L ≃ₐ[L] Gal(L/K) → L`: the algebra input of the
-- invariance half of étale Galois descent, and the one brick `AJC.picrep.etale-rep.invariance`
-- measured absent from Mathlib and from both projects.
import AlgebraicJacobian.Picard.GaloisDescent.GaloisSelfTensor
-- The Galois bridge: `γ`-invariance of a `picEt`-class versus agreement of the
-- descent cover's two projections. Agreement ⟹ invariance is unconditional; the
-- converse is an implication whose one named antecedent is that the `Gal`-indexed
-- sections generate a covering sieve.
import AlgebraicJacobian.Picard.GaloisDescent.PicEtGaloisBridge
import AlgebraicJacobian.Picard.GaloisDescent.PicEtGaloisCover
import AlgebraicJacobian.Picard.GaloisDescent.PicEtGaloisAction
import AlgebraicJacobian.Albanese.AlbaneseUP
import AlgebraicJacobian.Albanese.AuslanderBuchsbaum
import AlgebraicJacobian.Albanese.CodimOneExtension
import AlgebraicJacobian.Albanese.CoheightBridge
import AlgebraicJacobian.Albanese.DifferenceMap
import AlgebraicJacobian.Albanese.PolePurity
-- The g-fold sum `C^g ⟶ A` into a commutative group object and its
-- permutation symmetry: Milne's "clearly this is symmetric" (III.6.1).
import AlgebraicJacobian.Albanese.GrpObjFoldSum
-- Milne I.1.4: an abelian variety is commutative. Supplies the `IsCommMonObj`
-- instance that the g-fold sum above needs at its intended target.
import AlgebraicJacobian.Albanese.AVCommutative
import AlgebraicJacobian.Albanese.AVSelfProduct
import AlgebraicJacobian.Albanese.SymPowInterface
import AlgebraicJacobian.Albanese.SymPowColimit
-- The affine symmetric-power carrier, rooted so the workspace axiom probe covers it
-- (it did not until run 0069 r5; see inbox I-0659). `SymPowInvariants` names the carrier
-- of a ring-action quotient, `SymPowTensorAction` the `S_n`-action on the tensor power that
-- makes it Milne's `(A^{⊗ n})^{S_n}`, and `SymPowInvariantsUnder` restates the identification
-- over the base. For the chart-overlap comparison the split is: `SymPowInvariantsLocalization`
-- proves the substantive HALF (a fixed element of `A_b` has an invariant numerator) and
-- explicitly disclaims the equality in its own scope section; `SymPowInvariantsAwayEquiv` adds
-- the action on `A_b`, the converse direction, and the biconditional. An earlier revision of
-- this comment credited the equality `(A_b)^G = (A^G)_b` to the first file alone, which its
-- header contradicts.
import AlgebraicJacobian.Albanese.SymPowInvariants
import AlgebraicJacobian.Albanese.SymPowInvariantsLocalization
import AlgebraicJacobian.Albanese.SymPowInvariantsAwayEquiv
import AlgebraicJacobian.Albanese.SymPowTensorAction
import AlgebraicJacobian.Albanese.SymPowInvariantsUnder
-- The `G`-stable affine cover for a bare finite group action: the same proof as
-- `Picard/StableAffineCover.lean`, whose Galois binder its body never uses. Since run 0069 r6
-- it also carries the `S_n` instantiation, via `MonObj.permAutHom` in `GrpObjFoldSum`.
import AlgebraicJacobian.Albanese.StableAffineCoverGroup
-- The `n`-fold tensor power IS the `n`-ary coproduct of commutative algebras, with the
-- factor-permutation action matched to `permAlgHom`. Item 3 of the four-item glue-data bill
-- for `Sym^n C`; both halves of the universal property were already in mathlib unbundled
-- (`liftAlgHom` / `algHom_ext`) rather than absent, as two earlier sessions had recorded.
import AlgebraicJacobian.Albanese.TensorPowerCoproduct
-- …and that comparison packaged as a `Cofan`/`IsColimit` in `Under k`, which is what makes
-- item 3 consumable rather than merely proved: the affine chart's carrier is now a NAMED
-- object of `Under k` with its universal property in categorical form. Closes the last
-- categorical crossing of the bill; the one trap is that `CommRingCat.toAlgHom` is typed
-- over the rebuilt algebra instance, not the ambient one.
import AlgebraicJacobian.Albanese.TensorPowerCofan
-- Naming the affine carrier's INPUT: the n-fold product in `(Under k)ᵒᵖ` that `permDiagram`
-- is built on IS `op (mkUnder k (⨂[k] _ : Fin n, A))`, i.e. `(Spec_k A)^n = Spec_k (A^{⊗n})`,
-- with the S_n-actions matched (and the match carries `e⁻¹` — the kernel forced it). The
-- QUOTIENT carrier is still anonymous; see that file's Scope section for what separates them.
import AlgebraicJacobian.Albanese.SymPowAffineCarrier
-- …and the composition that names the QUOTIENT: the colimit of the S_n-action on (Spec_k A)^n
-- IS Spec_k ((A^{⊗n})^{S_n}) -- Milne III.3 Prop 3.1's affine half with the object identified,
-- which is what SymPowColimit §5's bold caveat asked for. Note that the accompanying HasColimit
-- is NOT a new fact (cocompleteness gives it); the deliverable is the iso, because only an
-- equation mentioning the object can name it.
import AlgebraicJacobian.Albanese.SymPowAffineQuotient
import AlgebraicJacobian.Albanese.AlbaneseFromData
import AlgebraicJacobian.Albanese.AlbaneseFromColimit
import AlgebraicJacobian.Albanese.AlbaneseJacobian
import AlgebraicJacobian.Albanese.Milne33Substeps
-- Milne Lemma 3.3 (`lem:milne_codim1_indeterminacy`) and its substep layers:
-- ported sorry-free from the sibling Rebuild tree in run 0069, closing the last
-- open obligation of the codim-one extension chapter and making Milne Theorem
-- 3.2 (`extend_to_av`) unconditional.
import AlgebraicJacobian.Albanese.Milne33CMEquidim
import AlgebraicJacobian.Albanese.Milne33KernelGen
import AlgebraicJacobian.Albanese.Milne33TransportLocal
import AlgebraicJacobian.Albanese.Milne33Rows
import AlgebraicJacobian.Albanese.Milne33Diagonal
import AlgebraicJacobian.Albanese.Milne33RowSection
import AlgebraicJacobian.Albanese.Milne33Pullback
import AlgebraicJacobian.Albanese.Milne33Transport
import AlgebraicJacobian.Albanese.Milne33
-- Descent of a morphism from a dense open into an abelian variety: the
-- extension half of Milne III.6.1's "it therefore defines a rational map
-- psi : J -> A, which (I 3.2) shows to be a regular map".
import AlgebraicJacobian.Albanese.DenseOpenDescent
import AlgebraicJacobian.Albanese.RationalMapFunctionField
import AlgebraicJacobian.Albanese.RationalMapPrecomp
import AlgebraicJacobian.Albanese.RationalMapProd
import AlgebraicJacobian.Albanese.SmoothPrimeRegularity
import AlgebraicJacobian.Albanese.StandardSmoothDimension
import AlgebraicJacobian.Albanese.Thm32RationalMapExtension
-- The Milne section I.3 chain over a PERFECT field, and the measured negative
-- saying which single link is not field-agnostic (Milne 3.3's closed-point row
-- argument).  Corrects I-1115, which localised the chain's IsAlgClosed to the
-- regularity input -- a step that was already discharged over perfect fields --
-- and reported Milne 3.3 as carrying no such binder.
import AlgebraicJacobian.Albanese.CodimOnePerfectField
-- and its non-vacuity, by instantiation at P^1 over Q and over F_5: fields that
-- are perfect and NOT algebraically closed, so the weakened binder is not
-- forced closed again by the remaining ones.
import AlgebraicJacobian.Albanese.CodimOnePerfectFieldWitness
-- and the localisation one step further: Milne 3.3's row step holds over an
-- ARBITRARY field from RATIONAL-POINT hypotheses, so its obstruction is a
-- statement about the curve, not about the base field.
import AlgebraicJacobian.Albanese.Milne33RowSectionRational

/-!
## Conditional bridge for the étale headline

The unconditional headline in `AlgebraicJacobian.Jacobian` deliberately has no
`SymPowData` or rational-point hypothesis.  The arbitrary-field Albanese engine is
already axiom-clean, but it consumes the symmetric-power carrier and a descent datum.
This theorem exposes that exact interface at `Pic0SchemeEt`; it is a reduction of the
headline leaf, not an unconditional representability claim.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The étale Picard identity component is Albanese once the symmetric-power and
descent inputs required by the arbitrary-field Milne engine are supplied.

This is intentionally conditional: no construction of `SymPowData C g` or of the
uniform target-wise descent datum is asserted here.  Supplying those inputs gives the
exact `IsAlbanese` conclusion consumed by `JacobianWitness.isAlbaneseFor`. -/
theorem isAlbanese_pic0Et_of_symPowData
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] [GeometricallyIntegral C.hom]
    (g : ℕ) (D : SymPowData C g)
    (hproj : ∀ σ : Equiv.Perm (Fin g),
      permAut C σ ≫ D.proj = D.proj)
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) (i₀ : Fin g)
    [GrpObj (Scheme.Pic0SchemeEt C)]
    [IsProper (Scheme.Pic0SchemeEt C).hom]
    [Smooth (Scheme.Pic0SchemeEt C).hom]
    [GeometricallyIrreducible (Scheme.Pic0SchemeEt C).hom]
    (aj : C ⟶ Scheme.Pic0SchemeEt C)
    (f : D.carrier ⟶ Scheme.Pic0SchemeEt C)
    (hf : letI : IsCommMonObj (Scheme.Pic0SchemeEt C) :=
      isCommMonObj_of_package_arbitraryField (Scheme.Pic0SchemeEt C)
      D.proj ≫ f = powSum g aj)
    (haj0 : P ≫ aj = η[Scheme.Pic0SchemeEt C])
    (hdesc : ∀ (A : Over (Spec (.of k))) [GrpObj A] [IsProper A.hom]
      [Smooth A.hom] [GeometricallyIrreducible A.hom] (φ : C ⟶ A),
      letI : IsCommMonObj A := isCommMonObj_of_package_arbitraryField A
      ∃! ψ : Scheme.Pic0SchemeEt C ⟶ A,
        D.symAVMap φ = f ≫ ψ) :
    IsAlbanese C P (Scheme.Pic0SchemeEt C) := by
  exact isAlbanese_of_symPowData_arbitraryField C g D hproj P i₀
    (Scheme.Pic0SchemeEt C) aj f hf haj0 hdesc

end AlgebraicGeometry
