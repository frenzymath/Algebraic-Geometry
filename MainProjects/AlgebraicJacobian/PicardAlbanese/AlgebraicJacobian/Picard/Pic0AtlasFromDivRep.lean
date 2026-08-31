/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianDataCharts
import AlgebraicJacobian.Picard.DivSchemeAbel

/-!
# The Abel chart map of the degree-zero Picard sheaf

`JacobianData.ofCharts` consumes a family of morphisms of big-site presheaves
`yoneda.obj (X i) ⟶ pic0SigmaFunctor C`.  This file builds such a morphism out of the two
things the tree already has: the Abel transformation of divisor families into the degree-zero
Picard functor on the slice, and a representation of the divisor functor by a scheme.

The passage from the slice to the big site is the Σ-extension, and it is functorial in two
independent ways, both established here in the general categorical setting:

* `CategoryTheory.Over.sigmaExtensionNat` — the Σ-extension is functorial in the extended
  presheaf: a natural transformation `F ⟶ G` of presheaves on the slice `Over S` induces one
  of presheaves on the ambient category.
* `CategoryTheory.Functor.RepresentableBy.toSigmaExtension` — a representation of `F` by an
  object `J` of the slice induces a morphism `yoneda.obj J.left ⟶ sigmaExtension S F` from the
  ambient yoneda presheaf of the underlying object.  A point of `J.left` over a test `V` is a
  map `v : V ⟶ J.left`, and it names the Σ-element whose structure morphism is `v ≫ J.hom` and
  whose fibre component is the universal element pulled back along `v`.

Composing the second with the first at the Abel transformation gives the chart map.

## Main declarations

* `AlgebraicGeometry.chartValueTrans` — **the Abel transformation into the degree-zero Picard
  functor**: under the chart-index degree constraint `deg Z = m·d₁ − n`, the chart value
  `abelDiv s · sigmaFamily Z · (θ^m)⁻¹` of `DivSchemeAbel.lean` is a natural transformation
  `divFunctor C π n ⟶ pic0TypeFunctor C`.  Naturality is `picEtMap_chartValue`, membership is
  `chartValue_mem_pic0Subgroup`.
* `AlgebraicGeometry.abelSigmaChart` — **the Abel chart map**: given a representation of the
  divisor functor by a scheme `D` over `k` (a section variable — this file never constructs
  one), the morphism of big-site presheaves
  `yoneda.obj D.left ⟶ (pic0SigmaSheaf C).1` sending a `D`-point to the class of the divisor
  family it names, twisted into degree zero.
* `AlgebraicGeometry.chartHom_abelSigmaChart` — the structure morphism of the single chart of
  this family is the structure morphism of the representing object, so the chart hypothesis
  `LocallyOfFiniteType (chartHom …)` of `JacobianData.ofCharts` is exactly
  `LocallyOfFiniteType D.hom` for it.

## What this is NOT

This is the chart *map*, not a chart *atlas*.  Neither of the two properties
`JacobianData.ofCharts` needs is established here, and neither is available anywhere in the
tree today:

* `IsOpenImmersion.presheaf (abelSigmaChart …)` is **false as stated for the whole divisor
  scheme** — the Abel map of a degree-`n` divisor scheme onto the Picard functor has projective
  spaces `|D|` as its fibres, so it is not a monomorphism, let alone an open immersion.  It
  becomes an open immersion only after restricting to the open locus where the fibre is a single
  point, i.e. where `h⁰ = 1`; that locus is the reserved `chartLocus` of `w4-datc` §3.3.

  Two updates to this bullet, both 2026-07-29.  `chartLocus` **now exists in Lean**
  (`Picard/Pic0ChartLocus.lean`, and open at a general test unconditionally), so the closing
  clause above — that it does not — is stale.  And the implication "not a monomorphism, hence
  not `IsOpenImmersion.presheaf`" is a **derivation**, not an extra fact: it is
  `mono_of_isOpenImmersion_presheaf` (`Picard/Pic0ChartOpenImmersionCriterion.lean`), from
  mathlib's `presheaf_mono_of_le` at `IsOpenImmersion.le_monomorphisms`.  The same file gives
  the criterion that makes the restricted statement provable, and
  `Picard/Pic0ChartUnivReduce.lean` instantiates it here.
* `Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc …)` is the statement that
  every degree-zero class is Zariski-locally the twisted class of a divisor family in the
  window.  Over a field this is Riemann–Roch; the relative statement is DAT-B's coverage row.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe v u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

/-! ## Σ-extension plumbing (general category theory)

Both constructions below are stated for presheaves valued in `Type v`, the hom-universe of the
ambient category, because that is where the ambient yoneda presheaf lives and the Σ-extension
must meet it. -/

namespace CategoryTheory

namespace Over

variable {C : Type u} [Category.{v} C] {S : C} {F G : (Over S)ᵒᵖ ⥤ Type v}

/-- **The Σ-extension is functorial in the extended presheaf**: a natural transformation of
presheaves on the slice induces one of their Σ-extensions, acting as the identity on the
structure-morphism component. -/
def sigmaExtensionNat (φ : F ⟶ G) : sigmaExtension S F ⟶ sigmaExtension S G where
  app T := TypeCat.ofHom fun x => ⟨x.1, φ.app _ x.2⟩
  naturality T T' g := by
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    obtain ⟨a, ξ⟩ := x
    exact congrArg (Sigma.mk (g.unop ≫ a))
      (ConcreteCategory.congr_hom (φ.naturality (Over.homMk g.unop rfl :
        Over.mk (g.unop ≫ a) ⟶ Over.mk a).op) ξ)

@[simp]
lemma sigmaExtensionNat_app_fst (φ : F ⟶ G) (T : Cᵒᵖ) (x : (sigmaExtension S F).obj T) :
    ((sigmaExtensionNat φ).app T x).1 = x.1 :=
  rfl

end Over

namespace Functor.RepresentableBy

open Over

variable {C : Type u} [Category.{v} C] {S : C} {F : (Over S)ᵒᵖ ⥤ Type v}

/-- The elementwise naturality identity behind `toSigmaExtension`, stated on the raw
Σ-extension transition function so that no bundled-hom coercion intervenes. -/
private lemma toSigmaExtension_aux {J : Over S} (α : F.RepresentableBy J)
    {T T' : C} (g : T' ⟶ T) (v : T ⟶ J.left) :
    (⟨(g ≫ v) ≫ J.hom, α.homEquiv (Over.homMk (g ≫ v) rfl)⟩ :
        Σ a : T' ⟶ S, F.obj (op (Over.mk a)))
      = Over.sigmaExtensionMap S F g ⟨v ≫ J.hom, α.homEquiv (Over.homMk v rfl)⟩ := by
  refine sigmaExtension_ext F (Category.assoc g v J.hom) ?_
  show F.map (mkCongr (Category.assoc g v J.hom)).op
      (F.map (Over.homMk g rfl :
        Over.mk (g ≫ (v ≫ J.hom)) ⟶ Over.mk (v ≫ J.hom)).op
        (α.homEquiv (Over.homMk v rfl))) = _
  rw [← Functor.map_comp_apply, ← op_comp, ← α.homEquiv_comp]
  refine congrArg α.homEquiv (Over.OverMorphism.ext ?_)
  exact congrArg (fun z : T' ⟶ T => z ≫ v) (Category.id_comp g)

/-- **The ambient presheaf map of a slice representation**: if `F` on the slice `Over S` is
represented by `J`, then the ambient yoneda presheaf of `J.left` maps to the Σ-extension of `F`.
A `V`-point `v : V ⟶ J.left` is sent to the Σ-element with structure morphism `v ≫ J.hom` and
fibre component the universal element restricted along `v`.

This is the input shape of mathlib's 01JJ engine: a scheme mapping to a big-site presheaf. -/
def toSigmaExtension {J : Over S} (α : F.RepresentableBy J) :
    yoneda.obj J.left ⟶ sigmaExtension S F where
  app _ := TypeCat.ofHom fun v => ⟨v ≫ J.hom, α.homEquiv (Over.homMk v rfl)⟩
  naturality _ _ g :=
    ConcreteCategory.hom_ext _ _ fun v => toSigmaExtension_aux α g.unop v

@[simp]
lemma toSigmaExtension_app_fst {J : Over S} (α : F.RepresentableBy J) (T : Cᵒᵖ)
    (v : T.unop ⟶ J.left) :
    ((α.toSigmaExtension).app T v).1 = v ≫ J.hom :=
  rfl

end Functor.RepresentableBy

end CategoryTheory

/-! ## The Abel transformation into the degree-zero Picard functor -/

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

variable (C π n) in
/-- **The Abel transformation into the degree-zero Picard functor**: under the chart-index
degree constraint `deg Z = m·d₁ − n`, the chart value of `DivSchemeAbel.lean` — the Abel class
of the divisor family, shifted by the Σ-family of `Z` and by `m` inverse powers of the pinned
θ-family — is a natural transformation `divFunctor C π n ⟶ pic0TypeFunctor C`.

The degree ledger of `degAt_chartValue` is what makes the target the degree-*zero* functor:
the three factors contribute `n`, `deg Z` and `−m·d₁`, which the constraint sums to zero. -/
def chartValueTrans (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ)) :
    divFunctor C π n ⟶ pic0TypeFunctor C where
  app T := TypeCat.ofHom fun s => ⟨chartValue C π n m Z T.unop s,
    chartValue_mem_pic0Subgroup C π n m Z hdeg T.unop s⟩
  naturality T T' g := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    exact Subtype.ext ((picEtMap_chartValue C π n m Z g.unop s).symm)

@[simp]
lemma chartValueTrans_app_coe (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (T : (Over (Spec (.of k)))ᵒᵖ) (s : divFamZar C π n T.unop) :
    ((chartValueTrans C π n m Z hdeg).app T s).1 = chartValue C π n m Z T.unop s :=
  rfl

/-! ## The Abel chart map -/

variable (C π n) in
/-- **The Abel chart map** of a representation of the divisor functor: the morphism of big-site
presheaves `yoneda.obj D.left ⟶ pic0SigmaFunctor C` sending a `D`-point to the degree-zero class
of the divisor family that point names.

`rep` is a *hypothesis* — this file never constructs a representation of the divisor functor;
that is the divisor-representability obligation of the `DivRep…` lane.  Given one, this is the
Abel–Jacobi map at the level of the Σ-extension, and it is the only kind of object
`JacobianData.ofCharts` accepts. -/
def abelSigmaChart {D : Over (Spec (.of k))} (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ)) :
    yoneda.obj D.left ⟶ (pic0SigmaSheaf C).1 :=
  rep.toSigmaExtension ≫ Over.sigmaExtensionNat (chartValueTrans C π n m Z hdeg)

/-- **The structure morphism of the Abel chart is that of the representing object**: for the
one-element family consisting of the Abel chart map, the chart structure morphism `chartHom`
that `JacobianData.ofCharts` reads off is `D.hom` itself.

So the finiteness hypotheses of the producer, specialised to this chart, are exactly
`LocallyOfFiniteType D.hom` and `CompactSpace D.left` — properties of the divisor scheme, with
no reference to the Picard functor. -/
lemma chartHom_abelSigmaChart {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    {ι : Type u} (i : ι) :
    chartHom C (fun _ : ι => abelSigmaChart C π n rep m Z hdeg) i = D.hom :=
  Category.id_comp _

end

end AlgebraicGeometry
