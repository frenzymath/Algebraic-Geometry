/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyZarMapAlg
import AlgebraicJacobian.Picard.DivisorFamilyZariskiGlueClass

/-!
# Zariski gluing kit for locally certified classes (DD-2 stage S5b)

The bricks of the S5b gluing keystone (`informal/spec-dd-2.md`, Addendum 2):

* `AlgebraicGeometry.Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_pullback`
  — regularity of the two-stage pulled equations from regularity of the composite
  pullback (the Kit's composite germ collapse, member-normalized).
* `AlgebraicGeometry.span_range_num_mul_eq_top` — **the composite-cover span**: for a
  span-⊤ family `g` with away carriers `S i` and span-⊤ families `h i` on each `S i`
  with numerators `a i l` (`algebraMap R (S i) (a i l)` associated to `h i l`), the
  products `a i l * g i` span `⊤` in `R` — by prime avoidance: a prime missing some
  `g i` lifts to `Spec (S i)`, misses some `h i l` there, hence misses the numerator.
* `AlgebraicGeometry.isScalarTower_away` / `isScalarTower_left_of_isScalarTower` —
  tower-coherence helpers: maps out of a localization agree once they agree on the
  base (`IsLocalization.ringHom_ext`), and `k`-towers follow from `R`-towers.
* `AlgebraicGeometry.DivFamZar.exists_glue_of_certified_away_compat` — **the
  certified-input gluing core**: compatible CERTIFIED families over an away cover of
  `R` glue to a LOCALLY certified class over `R` restricting to them. The divisor
  assembly is the landed `awayGluedEquations`; local certifiability of the glue is
  witnessed by `mapAlg` of the input families along the identification of each
  carrier with `Localization.Away (r κ)` (`IsLocalization.algEquiv`), divisor-equal
  to the pulled glue by witness transport at the landed chart restriction
  `divEq_pullback_awayGluedEquations`.

The pinned keystone `DivFamZar.exists_glue_of_away_compat` is
`AlgebraicJacobian.Picard.DivisorFamilyZarGlue`.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## Two-stage regularity from composite regularity -/

namespace Scheme.LocalEquations

/-- **Two-stage pulled-equation regularity from composite regularity**: if the pulled
equations along the composite `h = g ≫ f` have nonzerodivisor germs, so do the pulled
equations of the two-stage pullback — their own-member germs agree
(`germ_pullbackEqn_comp`), and own-member regularity spreads
(`germ_pullbackEqn_mem_nonZeroDivisors_of_forall_self`). -/
theorem germ_pullbackEqn_mem_nonZeroDivisors_pullback {X Y Z : Scheme.{u}}
    {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X} (hgf : g ≫ f = h) (E : X.LocalEquations)
    (hregf)
    (hregh : ∀ (y z : Z) (hz : z ∈ (E.cover.pullback h).opens y),
      (Z.presheaf.germ ((E.cover.pullback h).opens y) z hz).hom (pullbackEqn h E y)
        ∈ nonZeroDivisors (Z.presheaf.stalk z)) :
    ∀ (y z : Z) (hz : z ∈ ((E.pullback f hregf).cover.pullback g).opens y),
      (Z.presheaf.germ (((E.pullback f hregf).cover.pullback g).opens y) z hz).hom
          (pullbackEqn g (E.pullback f hregf) y)
        ∈ nonZeroDivisors (Z.presheaf.stalk z) :=
  germ_pullbackEqn_mem_nonZeroDivisors_of_forall_self g (E.pullback f hregf) fun ζ =>
    germ_pullbackEqn_comp hgf E hregf ζ ▸
      hregh ζ ζ ((E.cover.pullback h).mem_opens ζ)

end Scheme.LocalEquations

/-! ## Tower-coherence helpers -/

/-- **Tower coherence over a localization**: a scalar tower `A → B → D` commutes as
soon as the three `R₀`-towers do, when `A` is a localization of `R₀` — two algebra
maps out of `A` agree once they agree on `R₀` (`IsLocalization.ringHom_ext`). -/
theorem isScalarTower_away {R₀ A B D : Type u} [CommRing R₀] [CommRing A] [CommRing B]
    [CommRing D] [Algebra R₀ A] [Algebra R₀ B] [Algebra R₀ D] [Algebra A B]
    [Algebra A D] [Algebra B D] (M : Submonoid R₀) [IsLocalization M A]
    [IsScalarTower R₀ A B] [IsScalarTower R₀ B D] [IsScalarTower R₀ A D] :
    IsScalarTower A B D :=
  IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext M (by
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R₀ A B,
      ← IsScalarTower.algebraMap_eq R₀ B D, ← IsScalarTower.algebraMap_eq R₀ A D]))

/-- **Base-field tower coherence**: a scalar tower `k₀ → B → D` commutes as soon as
the two `k₀ → R₀`-factored towers and the `R₀`-tower do. -/
theorem isScalarTower_left_of_isScalarTower {k₀ R₀ B D : Type u} [CommRing k₀]
    [CommRing R₀] [CommRing B] [CommRing D] [Algebra k₀ R₀] [Algebra k₀ B]
    [Algebra k₀ D] [Algebra R₀ B] [Algebra R₀ D] [Algebra B D]
    [IsScalarTower k₀ R₀ B] [IsScalarTower k₀ R₀ D] [IsScalarTower R₀ B D] :
    IsScalarTower k₀ B D :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq k₀ R₀ D, IsScalarTower.algebraMap_eq R₀ B D,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq k₀ R₀ B])

/-! ## The composite-cover span -/

/-- **The composite-cover span** (`informal/spec-dd-2.md`, Addendum 2): for a span-⊤
family `g : ι → R` with away carriers `S i`, span-⊤ families `h i` on the `S i`, and
numerators `a i l` of the `h i l` (their images associated to the `h i l`), the
products `a i l * g i` span the unit ideal of `R`. Prime avoidance: a prime `M`
missing some `g i` is the trace of a prime `Q` of `S i`
(`PrimeSpectrum.localization_away_comap_range`); `Q` misses some `h i l`, hence `M`
misses the numerator `a i l`, hence the product. -/
theorem span_range_num_mul_eq_top {R : Type u} [CommRing R] {ι : Type u} (g : ι → R)
    (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, IsLocalization.Away (g i) (S i)]
    (hg : Ideal.span (Set.range g) = ⊤)
    {m : ι → ℕ} (h : ∀ i, Fin (m i) → S i)
    (hspan : ∀ i, Ideal.span (Set.range (h i)) = ⊤)
    (a : ∀ i, Fin (m i) → R)
    (hassoc : ∀ i l, Associated (algebraMap R (S i) (a i l)) (h i l)) :
    Ideal.span (Set.range fun p : Σ i, Fin (m i) => a p.1 p.2 * g p.1) = ⊤ := by
  by_contra hne
  obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI hMprime : M.IsPrime := hMmax.isPrime
  -- some `g i` avoids `M`
  obtain ⟨i, hgi⟩ : ∃ i, g i ∉ M := by
    by_contra hall
    push Not at hall
    have hM : Ideal.span (Set.range g) ≤ M := Ideal.span_le.mpr (by
      rintro - ⟨i, rfl⟩
      exact hall i)
    rw [hg] at hM
    exact hMmax.ne_top (top_le_iff.mp hM)
  -- `M` is the trace of a prime `Q` of `S i`
  have hmem : (⟨M, hMprime⟩ : PrimeSpectrum R)
      ∈ Set.range (PrimeSpectrum.comap (algebraMap R (S i))) := by
    rw [PrimeSpectrum.localization_away_comap_range (S := S i) (g i)]
    exact hgi
  obtain ⟨Q, hQ⟩ := hmem
  have hQM : Q.asIdeal.comap (algebraMap R (S i)) = M :=
    congrArg PrimeSpectrum.asIdeal hQ
  -- some `h i l` avoids `Q`
  obtain ⟨l, hhl⟩ : ∃ l, h i l ∉ Q.asIdeal := by
    by_contra hall
    push Not at hall
    have hQ' : Ideal.span (Set.range (h i)) ≤ Q.asIdeal := Ideal.span_le.mpr (by
      rintro - ⟨l, rfl⟩
      exact hall l)
    rw [hspan i] at hQ'
    exact Q.isPrime.ne_top (top_le_iff.mp hQ')
  -- the numerator avoids `M`
  have hal : a i l ∉ M := by
    intro hmem'
    have h1 : algebraMap R (S i) (a i l) ∈ Q.asIdeal :=
      Ideal.mem_comap.mp (hQM.symm ▸ hmem')
    obtain ⟨u, hu⟩ := hassoc i l
    exact hhl (hu ▸ Ideal.mul_mem_right (u : S i) Q.asIdeal h1)
  -- primality contradiction on the product
  have hmemM : a i l * g i ∈ M := hle (Ideal.subset_span ⟨⟨i, l⟩, rfl⟩)
  rcases hMprime.mem_or_mem hmemM with hc | hc
  · exact hal hc
  · exact hgi hc

/-! ## The certified-input gluing core -/

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}

/-- **The certified-input gluing core** (S5b): a family of CERTIFIED divisor families
over a finite away cover of `R`, compatible on the overlap carriers, glues to a
LOCALLY certified class over `R` restricting to the given classes. The divisor
assembly is the landed `awayGluedEquations`; the glue is locally certified over the
same cover — each certified family transports along the identification of its carrier
with `Localization.Away (r κ)` (`IsLocalization.algEquiv`) and stays divisor-equal to
the pulled glue by witness transport at the landed chart restriction. -/
theorem DivFamZar.exists_glue_of_certified_away_compat
    {κ : Type u} [Finite κ] (r : κ → R) (S' : κ → Type u)
    [∀ q, CommRing (S' q)] [∀ q, Algebra k (S' q)] [∀ q, Algebra R (S' q)]
    [∀ q, IsScalarTower k R (S' q)] [∀ q, IsLocalization.Away (r q) (S' q)]
    (V : κ → κ → Type u) [∀ p q, CommRing (V p q)] [∀ p q, Algebra k (V p q)]
    [∀ p q, Algebra R (V p q)] [∀ p q, IsScalarTower k R (V p q)]
    [∀ p q, Algebra (S' p) (V p q)] [∀ p q, Algebra (S' q) (V p q)]
    [∀ p q, IsScalarTower k (S' p) (V p q)] [∀ p q, IsScalarTower k (S' q) (V p q)]
    [∀ p q, IsScalarTower R (S' p) (V p q)] [∀ p q, IsScalarTower R (S' q) (V p q)]
    [∀ p q, IsLocalization.Away (r p * r q) (V p q)]
    (hr : Ideal.span (Set.range r) = ⊤)
    (E : ∀ q, CertifiedDivisorFamily C (S' q) π n)
    (hcompat : AwayCompatDivEq S' E V) :
    ∃ F₀ : DivFamZar C R π n,
      ∀ q, DivFamZar.mapAlg (S' q) n F₀ = (DivFam.mk (E q)).toZar := by
  classical
  haveI himm : ∀ q, IsOpenImmersion (relCurveMap C R (S' q)) := fun q =>
    isOpenImmersion_relCurveMap_away C R (S' q) (r q)
  -- the glued local-equation system (S5, landed)
  set glue := awayGluedEquations r S' E V hr hcompat with hglue
  -- the glue is locally certified over the same cover
  have hloc : IsLocallyCertified C R π n glue := by
    obtain ⟨M, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
    refine ⟨M, fun j => r (e.symm j), ?_, fun j => ?_⟩
    · have hrange : (Set.range fun j : Fin M => r (e.symm j)) = Set.range r :=
        e.symm.surjective.range_comp r
      rw [hrange, hr]
    · -- identify the carrier with the pinned localization and transport the witness
      set q := e.symm j with hq
      set B := Localization.Away (r q) with hB
      haveI : IsOpenImmersion (relCurveMap C R B) :=
        isOpenImmersion_relCurveMap_away C R B (r q)
      letI : Algebra (S' q) B :=
        ((IsLocalization.algEquiv (Submonoid.powers (r q)) (S' q)
          B).toAlgHom.toRingHom).toAlgebra
      haveI : IsScalarTower R (S' q) B :=
        IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x =>
          ((IsLocalization.algEquiv (Submonoid.powers (r q)) (S' q) B).commutes
            x).symm)
      haveI : IsScalarTower k (S' q) B :=
        isScalarTower_left_of_isScalarTower (R₀ := R)
      -- the chart restriction of the glue, transported along the identification
      have hdiv0 := (divEq_pullback_awayGluedEquations r S' E V hr hcompat q
        (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
          (relCurveMap C R (S' q)) glue)).symm
      exact ⟨(E q).mapAlg B n,
        (E q).divEq_mapAlg_pullback B
          (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
            (relCurveMap C R B) glue) hdiv0⟩
  refine ⟨DivFamZar.mk glue hloc, fun q => ?_⟩
  -- the restriction law: the pulled glue is divisor-equal to the chart family
  exact DivFamZar.mk_eq_mk_iff.mpr
    (divEq_pullback_awayGluedEquations r S' E V hr hcompat q _)

end AlgebraicGeometry
