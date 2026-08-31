/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAffChallenge
import AlgebraicJacobian.Picard.Pic0AtlasFromDivRepAff
import AlgebraicJacobian.Picard.Pic0ChartAtlasCoupling

/-!
# The widened divisor representer at the Picard atlas seam

The widened divisor functor of a challenge curve is represented at the genus parameter.  This
module inserts that representation into the Abel construction and then into the Zariski-local
representability theorem for the degree-zero Picard functor.

The resulting chart family has no assumed divisor representation.  Its remaining inputs are the
two geometric conditions of the local-representability theorem: every restricted Abel map is a
representable open immersion, and the restricted maps cover the Picard sheaf pointwise.

This is not an unconditional Picard representability result: the final declaration below retains
both geometric inputs.  Moreover, at the larger admissible coverage parameter the raw Abel map has
positive-dimensional linear-system fibres in positive genus, so the larger divisor representer
cannot simply be substituted as an open chart source.  The remaining datum-tail construction is
the corrected Altman--Kleiman step: represent the quotient by equality of the induced Picard class,
thereby removing those fibres before applying the Picard representability seam.

## Main declarations

* `AlgebraicGeometry.abelSigmaChartAffGenus` is the widened Abel chart formed from the chosen
  genus-parameter divisor representer.
* `AlgebraicGeometry.universalDivFamAffGenus` is its universal widened divisor family.
* `AlgebraicGeometry.abelSigmaChartAffAdmissible` is the no-argument widened Abel map at the
  unconditional admissible coverage parameter; its legal chart index is chosen internally.
* `AlgebraicGeometry.universalDivFamAffAdmissible` is the corresponding universal family.
* `AlgebraicGeometry.affineGenusChart` restricts a multi-index family of these maps to chosen
  source opens.
* `AlgebraicGeometry.pic0RepresentableByOfAffineGenusCharts` is the conditional final assembly
  once the restricted charts are open immersions and cover pointwise.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

/-- The universal widened divisor family carried by the chosen genus-parameter representer. -/
def universalDivFamAffGenus :
    divFamZarAff C (genus C) (divRepAffGenusScheme C) :=
  (divFunctorAff_genus_representableBy C).homEquiv (𝟙 _)

/-- Pulling back the chosen universal family gives the widened family classified by the
corresponding morphism into the genus representer. -/
theorem universalDivFamAffGenus_map {T : Over (Spec (.of k))}
    (q : T ⟶ divRepAffGenusScheme C) :
    divFamZarAff.map C (genus C) q (universalDivFamAffGenus C)
      = (divFunctorAff_genus_representableBy C).homEquiv q := by
  have h := (divFunctorAff_genus_representableBy C).homEquiv_comp q
    (𝟙 (divRepAffGenusScheme C))
  rw [Category.comp_id] at h
  exact h.symm

/-- The universal widened divisor family carried by the unconditional representer at the
admissible coverage parameter. -/
def universalDivFamAffAdmissible :
    divFamZarAff C (divRepAffAdmissibleParameter C) (divRepAffAdmissibleScheme C) :=
  (divFunctorAff_admissible_representableBy C).homEquiv (𝟙 _)

/-- Pullback of the admissible universal family agrees with classification by the unconditional
admissible representer. -/
theorem universalDivFamAffAdmissible_map {T : Over (Spec (.of k))}
    (q : T ⟶ divRepAffAdmissibleScheme C) :
    divFamZarAff.map C (divRepAffAdmissibleParameter C) q
        (universalDivFamAffAdmissible C)
      = (divFunctorAff_admissible_representableBy C).homEquiv q := by
  have h := (divFunctorAff_admissible_representableBy C).homEquiv_comp q
    (𝟙 (divRepAffAdmissibleScheme C))
  rw [Category.comp_id] at h
  exact h.symm

/-- The widened Abel chart at the genus parameter, using the challenge curve's chosen divisor
representer rather than accepting a representability witness as an argument. -/
def abelSigmaChartAffGenus
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (genus C : ℤ)) :
    yoneda.obj (divRepAffGenusScheme C).left ⟶ (pic0SigmaSheaf C).1 :=
  abelSigmaChartAff C (genus C) (divFunctorAff_genus_representableBy C) m Z hdeg

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra in
attribute [local instance 10000] relCurve.instOver in
/-- The widened Abel map at the unconditional admissible coverage parameter.  A legal chart
index whose locus is universal is chosen internally; this declaration does not assert that the
raw Abel map is an open immersion or an atlas. -/
def abelSigmaChartAffAdmissible :
    yoneda.obj (divRepAffAdmissibleScheme C).left ⟶ (pic0SigmaSheaf C).1 := by
  classical
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : IsIntegral C.left := isIntegral_left_of_geometricallyReduced C
  haveI : LocallyOfFiniteType (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact C.hom)
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    moduleFinite_hModule_zero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    moduleFinite_hModule_one C
  let hchart := exists_uniform_admissibleCoverageChart_eq_univ
    (C := C) (divRepAffP1Map_comp C) (genus C) (chi_moduleKSheaf C)
  let m : ℕ := Classical.choose hchart
  let hZ := Classical.choose_spec hchart
  let Z : (C ⊗ overSpec k k).left.CurveDivisor := Classical.choose hZ
  have hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C)
        - (divRepAffAdmissibleParameter C : ℤ) := by
    change Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C)
        - (admissibleCoverageParameter
            (C := C) (divRepAffP1Map_comp C) (genus C) : ℤ)
    exact (Classical.choose_spec hZ).1
  exact abelSigmaChartAff C (divRepAffAdmissibleParameter C)
    (divFunctorAff_admissible_representableBy C) m Z hdeg

/-- The structure morphism read from a genus-parameter widened Abel chart is the structure
morphism of the chosen divisor representer. -/
lemma chartHom_abelSigmaChartAffGenus
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (genus C : ℤ))
    {ι : Type u} (i : ι) :
    chartHom C (fun _ : ι => abelSigmaChartAffGenus C m Z hdeg) i
      = (divRepAffGenusScheme C).hom :=
  chartHom_abelSigmaChartAff (divFunctorAff_genus_representableBy C) m Z hdeg i

/-- The structure morphism read from the admissible Abel map is the structure morphism of the
unconditional admissible divisor representer. -/
lemma chartHom_abelSigmaChartAffAdmissible {ι : Type u} (i : ι) :
    chartHom C (fun _ : ι => abelSigmaChartAffAdmissible C) i
      = (divRepAffAdmissibleScheme C).hom := by
  dsimp only [abelSigmaChartAffAdmissible]
  exact chartHom_abelSigmaChartAff
    (divFunctorAff_admissible_representableBy C) _ _ _ i

/-- A multi-index family of genus-parameter widened Abel charts, restricted to source opens.
Different indices may use different twists and different opens, but they all use the same
unconditional divisor representer. -/
def affineGenusChart {ι : Type u}
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (genus C : ℤ))
    (V : ∀ _ : ι, (divRepAffGenusScheme C).left.Opens) (i : ι) :
    yoneda.obj (V i : Scheme) ⟶ (pic0SigmaSheaf C).1 :=
  restrictChart (abelSigmaChartAffGenus C (m i) (Z i) (hdeg i)) (V i)

/-- The structure morphism of a restricted genus chart is the inclusion of its source open
followed by the structure morphism of the chosen divisor representer. -/
lemma chartHom_affineGenusChart {ι : Type u}
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (genus C : ℤ))
    (V : ∀ _ : ι, (divRepAffGenusScheme C).left.Opens) (i : ι) :
    chartHom C (affineGenusChart C m Z hdeg V) i
      = (V i).ι ≫ (divRepAffGenusScheme C).hom := by
  have hrestrict := chartHom_restrictChart (C := C)
    (abelSigmaChartAffGenus C (m i) (Z i) (hdeg i)) (V i) i
  have hgenus := chartHom_abelSigmaChartAffGenus C (m i) (Z i) (hdeg i) i
  simpa only [chartHom, affineGenusChart] using
    hrestrict.trans (congrArg ((V i).ι ≫ ·) hgenus)

/-- The degree-zero Picard functor is represented by the glued object of any pointwise-covering
family of open genus-parameter widened Abel charts.

The divisor representation is construction data, not a hypothesis: it is supplied by
`divFunctorAff_genus_representableBy`.  The two hypotheses are exactly the geometric inputs of
Zariski local representability. -/
def pic0RepresentableByOfAffineGenusCharts {ι : Type u}
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (genus C : ℤ))
    (V : ∀ _ : ι, (divRepAffGenusScheme C).left.Opens)
    (hf : ∀ i, IsOpenImmersion.presheaf (affineGenusChart C m Z hdeg V i))
    (hcov : PointwiseCoverage C (affineGenusChart C m Z hdeg V)) :
    Σ J : Over (Spec (.of k)), (pic0TypeFunctor C).RepresentableBy J := by
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (affineGenusChart C m Z hdeg V)) :=
    isLocallySurjective_sigmaDesc_of_pointwise C _ hcov
  exact ⟨_, pic0RepresentableByOfCharts C (affineGenusChart C m Z hdeg V) hf⟩

end

end AlgebraicGeometry
