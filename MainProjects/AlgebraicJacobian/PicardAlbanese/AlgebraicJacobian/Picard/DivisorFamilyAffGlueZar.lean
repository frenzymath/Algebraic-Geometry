/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffGlueZarKit

/-!
# Zariski gluing of WIDENED locally certified divisor classes (R2 keystone, I-0492)

**The pinned keystone, ported to the widened carrier** (`informal/spec-dd-2.md`, Addendum 2 at
`DivFamZarAff`): compatible widened locally certified divisor classes over a finite away cover of
`R` glue to a widened class over `R` restricting to them.

## Why this ports, and where the only real work was

R2 (human decision I-0492) widened where the certificate's pieces live ON THE CURVE — arbitrary
affine opens instead of basic opens of two pinned `P¹` charts.  It changed NOTHING about the
Zariski cover of the BASE, and the gluing argument is entirely about the base: it assembles a
divisor with `awayGluedEquationsLoc` and witnesses local certifiability by `mapAlg` of the input
families.  So the route below is the chart-typed `DivFamZar.exists_glue_of_away_compat` with three
mechanical substitutions — `DivFamZar → DivFamZarAff`, `CertifiedDivisorFamily →
CertifiedDivisorFamilyAff`, and no `π` anywhere — plus two real costs:

* the assembly had to be **restated at bare local-equation systems** first, because its
  chart-typed statement demands `CertifiedDivisorFamily` input that a widened class provably
  cannot supply.  That is `DivisorFamilyAffGlueZarKit.lean`; the proof there is verbatim.
* every `CertifiedDivisorFamilyAff.mapAlg` carries the overlap-affineness argument `hinf`, free
  here from `[IsProper C.hom]` via `AffCoverData.hasAffineOverlaps_of_isProper`, which is also
  what `DivFamZarAff.mapAlg` itself needs.  Hence `[IsProper C.hom]` in the statement — the DD-R
  lane has it everywhere, the challenge curve being proper over `k`.

## The route, unchanged from the chart-typed keystone

Representatives `d i` carry widened local certificate covers `h i : Fin (m i) → S i` with
certified families `G i l` over `Localization.Away (h i l)`.  The composite cover
`r ⟨i, l⟩ := a i l * g i` (numerators `a i l` of the `h i l`, `IsLocalization.Away.sec`) spans `⊤`
(`span_range_num_mul_eq_top`), and the fine carriers `Localization.Away (h i l)` are
`r ⟨i, l⟩`-away localizations of `R`.  The fine overlap carriers receive the coarse overlap
carriers `T i j` by `IsLocalization.Away.lift`; the fine compatibility follows from the class-level
compatibility pulled to the fine overlaps through the two factorizations of each comparison.  The
widened certified-input gluing core produces the glued class, and the restriction law at the
coarse level follows by Zariski separation (`DivFamZarAff.eq_of_away_eq`) over each `S i` against
its fine cover.

## Main declarations

* `AlgebraicGeometry.DivFamZarAff.exists_glue_of_away_compat` — the keystone.
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

/-- Bottom face of a triple tower: `R₀ → A → D` commutes when `R₀ → A → B`,
`R₀ → B → D` and `A → B → D` do. -/
private lemma isScalarTower_bot {R₀ A B D : Type u} [CommRing R₀] [CommRing A]
    [CommRing B] [CommRing D] [Algebra R₀ A] [Algebra R₀ B] [Algebra R₀ D]
    [Algebra A B] [Algebra A D] [Algebra B D]
    [IsScalarTower R₀ A B] [IsScalarTower R₀ B D] [IsScalarTower A B D] :
    IsScalarTower R₀ A D :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R₀ B D, IsScalarTower.algebraMap_eq R₀ A B,
      ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq A B D])

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R] {n : ℕ}

/-- **THE PINNED KEYSTONE AT THE WIDENED CARRIER — Zariski gluing of widened locally certified
divisor classes** (`informal/spec-dd-2.md`, Addendum 2, at the R2 value of I-0492): for a finite
span-⊤ family `g : ι → R` with away carriers `S i` and overlap carriers `T i j`, widened locally
certified classes `F i : DivFamZarAff C (S i) n` compatible on the overlaps glue: there is
`F₀ : DivFamZarAff C R n` with `DivFamZarAff.mapAlg (S i) n F₀ = F i` for all `i`.
(Uniqueness is `DivFamZarAff.eq_of_away_eq`.)

This is what makes the widened value a Zariski SHEAF value rather than merely a functor value, and
it is field-uniform: no hypothesis on `|P¹(k)|` occurs anywhere in the statement or its route. -/
theorem DivFamZarAff.exists_glue_of_away_compat
    {ι : Type u} [Finite ι] (g : ι → R) (S : ι → Type u)
    [∀ i, CommRing (S i)] [∀ i, Algebra k (S i)] [∀ i, Algebra R (S i)]
    [∀ i, IsScalarTower k R (S i)] [∀ i, IsLocalization.Away (g i) (S i)]
    (T : ι → ι → Type u) [∀ i j, CommRing (T i j)] [∀ i j, Algebra k (T i j)]
    [∀ i j, Algebra R (T i j)] [∀ i j, IsScalarTower k R (T i j)]
    [∀ i j, Algebra (S i) (T i j)] [∀ i j, Algebra (S j) (T i j)]
    [∀ i j, IsScalarTower k (S i) (T i j)] [∀ i j, IsScalarTower k (S j) (T i j)]
    [∀ i j, IsScalarTower R (S i) (T i j)] [∀ i j, IsScalarTower R (S j) (T i j)]
    [∀ i j, IsLocalization.Away (g i * g j) (T i j)]
    (hg : Ideal.span (Set.range g) = ⊤)
    (F : ∀ i, DivFamZarAff C (S i) n)
    (hcompat : ∀ i j,
      DivFamZarAff.mapAlg (T i j) n (F i) = DivFamZarAff.mapAlg (T i j) n (F j)) :
    ∃ F₀ : DivFamZarAff C R n, ∀ i, DivFamZarAff.mapAlg (S i) n F₀ = F i := by
  classical
  -- representatives and their widened local certificate covers
  have hrep := fun i => Quotient.exists_rep (F i)
  choose dp hdp using hrep
  choose m h hspan hGs using fun i => (dp i).2
  haveI hImmU : ∀ (i : ι) (l : Fin (m i)),
      IsOpenImmersion (relCurveMap C (S i) (Localization.Away (h i l))) := fun i l =>
    isOpenImmersion_relCurveMap_away C (S i) (Localization.Away (h i l)) (h i l)
  have hGs' : ∀ (i : ι) (l : Fin (m i)),
      ∃ G : CertifiedDivisorFamilyAff C (Localization.Away (h i l)) n,
        Scheme.LocalEquations.DivEq G.eqns
          ((dp i).1.pullback (relCurveMap C (S i) (Localization.Away (h i l)))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C (S i) (Localization.Away (h i l))) (dp i).1)) :=
    fun i l => hGs i l
  choose G hGdiv using hGs'
  -- the numerators and the composite cover
  have hassoc : ∀ (i : ι) (l : Fin (m i)),
      Associated (algebraMap R (S i) ((IsLocalization.Away.sec (g i) (h i l)).1))
        (h i l) :=
    fun i l => IsLocalization.Away.associated_sec_fst (g i) (h i l)
  have hr : Ideal.span (Set.range fun p : Σ i : ι, Fin (m i) =>
      (IsLocalization.Away.sec (g p.1) (h p.1 p.2)).1 * g p.1) = ⊤ :=
    span_range_num_mul_eq_top g S hg h hspan
      (fun i l => (IsLocalization.Away.sec (g i) (h i l)).1) hassoc
  -- the fine carriers are away localizations of `R` at the composite cover
  haveI hAway : ∀ p : Σ i : ι, Fin (m i),
      IsLocalization.Away ((IsLocalization.Away.sec (g p.1) (h p.1 p.2)).1 * g p.1)
        (Localization.Away (h p.1 p.2)) := fun p => by
    haveI : IsLocalization.Away
        (algebraMap R (S p.1) ((IsLocalization.Away.sec (g p.1) (h p.1 p.2)).1))
        (Localization.Away (h p.1 p.2)) :=
      IsLocalization.Away.of_associated (hassoc p.1 p.2).symm
    exact IsLocalization.Away.mul (S p.1) (Localization.Away (h p.1 p.2)) (g p.1)
      ((IsLocalization.Away.sec (g p.1) (h p.1 p.2)).1)
  -- notation for the composite cover and the fine overlap carriers
  set r : (Σ i : ι, Fin (m i)) → R :=
    fun p => (IsLocalization.Away.sec (g p.1) (h p.1 p.2)).1 * g p.1 with hrdef
  -- the fine overlap carriers and their instance pack
  haveI hVaway : ∀ p q : Σ i : ι, Fin (m i),
      IsLocalization.Away (r p * r q)
        (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) :=
    fun p q => mul_comm (r q) (r p) ▸ inferInstance
  letI algSq : ∀ p q : Σ i : ι, Fin (m i),
      Algebra (Localization.Away (h q.1 q.2))
        (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) :=
    fun p q =>
      (IsLocalization.Away.lift (r q) (S := Localization.Away (h q.1 q.2))
        (g := algebraMap R
          (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))))
        (IsLocalization.Away.isUnit_of_dvd (x := r p * r q)
          ⟨r p, mul_comm (r p) (r q)⟩)).toAlgebra
  haveI towSqR : ∀ p q : Σ i : ι, Fin (m i),
      IsScalarTower R (Localization.Away (h q.1 q.2))
        (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) :=
    fun p q => IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_comp])
  haveI towSqk : ∀ p q : Σ i : ι, Fin (m i),
      IsScalarTower k (Localization.Away (h q.1 q.2))
        (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) :=
    fun p q => isScalarTower_left_of_isScalarTower (R₀ := R)
  letI algSj : ∀ p q : Σ i : ι, Fin (m i),
      Algebra (S q.1)
        (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) :=
    fun p q =>
      ((algebraMap (Localization.Away (h q.1 q.2))
          (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q)))).comp
        (algebraMap (S q.1) (Localization.Away (h q.1 q.2)))).toAlgebra
  haveI towSjSq : ∀ p q : Σ i : ι, Fin (m i),
      IsScalarTower (S q.1) (Localization.Away (h q.1 q.2))
        (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) :=
    fun p q => IsScalarTower.of_algebraMap_eq' (RingHom.algebraMap_toAlgebra _)
  haveI towSjR : ∀ p q : Σ i : ι, Fin (m i),
      IsScalarTower R (S q.1)
        (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) :=
    fun p q => isScalarTower_bot (B := Localization.Away (h q.1 q.2))
  haveI towSjk : ∀ p q : Σ i : ι, Fin (m i),
      IsScalarTower k (S q.1)
        (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) :=
    fun p q => isScalarTower_left_of_isScalarTower (R₀ := R)
  letI algT : ∀ p q : Σ i : ι, Fin (m i),
      Algebra (T p.1 q.1)
        (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) :=
    fun p q =>
      (IsLocalization.Away.lift (g p.1 * g q.1) (S := T p.1 q.1)
        (g := algebraMap R
          (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))))
        (IsLocalization.Away.isUnit_of_dvd (x := r p * r q)
          ⟨(IsLocalization.Away.sec (g p.1) (h p.1 p.2)).1
            * (IsLocalization.Away.sec (g q.1) (h q.1 q.2)).1, by
              simp only [hrdef]
              ring⟩)).toAlgebra
  haveI towTR : ∀ p q : Σ i : ι, Fin (m i),
      IsScalarTower R (T p.1 q.1)
        (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) :=
    fun p q => IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_comp])
  haveI towTk : ∀ p q : Σ i : ι, Fin (m i),
      IsScalarTower k (T p.1 q.1)
        (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) :=
    fun p q => isScalarTower_left_of_isScalarTower (R₀ := R)
  haveI towSiT : ∀ p q : Σ i : ι, Fin (m i),
      IsScalarTower (S p.1) (T p.1 q.1)
        (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) :=
    fun p q => isScalarTower_away (M := Submonoid.powers (g p.1))
  haveI towSjT : ∀ p q : Σ i : ι, Fin (m i),
      IsScalarTower (S q.1) (T p.1 q.1)
        (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) :=
    fun p q => isScalarTower_away (M := Submonoid.powers (g q.1))
  -- the fine compatibility, from the coarse one through the overlap carriers
  have hcompatFine : AwayCompatPullDivEq
      (fun p : Σ i : ι, Fin (m i) => Localization.Away (h p.1 p.2))
      (fun p => (G p.1 p.2).eqns)
      (fun p q =>
        Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) := by
    intro p q
    -- the regularity witnesses `AwayCompatPullDivEq` binds existentially are the CERTIFICATE's
    -- own: `AffAdaptation.germ_pullbackEqn_mem_nonZeroDivisors`.  With them,
    -- `(G _).eqns.pullback _ _` IS `((G _).mapAlg _ n _).eqns`, since
    -- `AffAdaptation.pulledEquations` is that very `pullback` (and `regular` is a `Prop`, so
    -- the choice of witness is invisible).
    refine ⟨(G p.1 p.2).adaptation.germ_pullbackEqn_mem_nonZeroDivisors
        (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q)))
        (G p.1 p.2).certified.projective_colength,
      (G q.1 q.2).adaptation.germ_pullbackEqn_mem_nonZeroDivisors
        (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q)))
        (G q.1 q.2).certified.projective_colength, ?_⟩
    -- the two factorizations of the fine-overlap comparisons
    have hgf_i : relCurveMap C (T p.1 q.1)
          (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q)))
        ≫ relCurveMap C (S p.1) (T p.1 q.1)
        = relCurveMap C (S p.1)
            (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) :=
      relCurveMap_comp (R' := T p.1 q.1)
        (R'' := Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q)))
    have hgf_j : relCurveMap C (T p.1 q.1)
          (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q)))
        ≫ relCurveMap C (S q.1) (T p.1 q.1)
        = relCurveMap C (S q.1)
            (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) :=
      relCurveMap_comp (R' := T p.1 q.1)
        (R'' := Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q)))
    -- the coarse compatibility at the representatives
    have hd := hcompat p.1 q.1
    rw [← hdp p.1, ← hdp q.1] at hd
    have hd_compat := DivFamZarAff.mk_eq_mk_iff.mp hd
    -- regularity discharges (the widened mapAlg-hreg engine)
    have hreg_iT := (dp p.1).2.germ_pullbackEqn_mem_nonZeroDivisors (T p.1 q.1) n
    have hreg_jT := (dp q.1).2.germ_pullbackEqn_mem_nonZeroDivisors (T p.1 q.1) n
    have hreg_iV := (dp p.1).2.germ_pullbackEqn_mem_nonZeroDivisors
      (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) n
    have hreg_jV := (dp q.1).2.germ_pullbackEqn_mem_nonZeroDivisors
      (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))) n
    have h_two_i := Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_pullback
      hgf_i (dp p.1).1 hreg_iT hreg_iV
    have h_two_j := Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_pullback
      hgf_j (dp q.1).1 hreg_jT hreg_jV
    -- witness transport on both sides
    have hbp := (G p.1 p.2).divEq_mapAlg_pullback n
      (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q)))
      (G p.1 p.2).cover.hasAffineOverlaps_of_isProper
      hreg_iV (hGdiv p.1 p.2)
    have hbq := (G q.1 q.2).divEq_mapAlg_pullback n
      (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q)))
      (G q.1 q.2).cover.hasAffineOverlaps_of_isProper
      hreg_jV (hGdiv q.1 q.2)
    -- the composite collapses and the pulled coarse compatibility
    have collapse_i := Scheme.LocalEquations.divEq_pullback_pullback hgf_i
      (dp p.1).1 hreg_iT h_two_i hreg_iV
    have collapse_j := Scheme.LocalEquations.divEq_pullback_pullback hgf_j
      (dp q.1).1 hreg_jT h_two_j hreg_jV
    have hstep := Scheme.LocalEquations.divEq_pullback
      (relCurveMap C (T p.1 q.1)
        (Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q))))
      hd_compat h_two_i h_two_j
    exact hbp.trans (collapse_i.symm.trans (hstep.trans (collapse_j.trans hbq.symm)))
  -- the widened certified-input gluing core produces the glued class
  obtain ⟨F₀, hF₀⟩ := DivFamZarAff.exists_glue_of_certified_away_compat r
    (fun p : Σ i : ι, Fin (m i) => Localization.Away (h p.1 p.2))
    (fun p q =>
      Localization.Away (algebraMap R (Localization.Away (h p.1 p.2)) (r q)))
    hr (fun p => G p.1 p.2) hcompatFine
  refine ⟨F₀, fun i => ?_⟩
  -- the restriction law, by Zariski separation over `S i` against the fine cover
  -- NOTE: the widened `eq_of_away_eq` takes `n` as an EXPLICIT leading argument, unlike its
  -- chart-typed counterpart where it is implicit; omitting it makes the cover family elaborate
  -- against `ℕ` and the error surfaces as an unresolvable `l.down`.
  refine DivFamZarAff.eq_of_away_eq n (fun l : ULift.{u} (Fin (m i)) => h i l.down)
    (fun l => Localization.Away (h i l.down)) ?_ fun l => ?_
  · have hrange : (Set.range fun l : ULift.{u} (Fin (m i)) => h i l.down)
        = Set.range (h i) := ULift.down_surjective.range_comp (h i)
    rw [hrange, hspan i]
  · -- both sides restrict to the fine certified family
    rw [DivFamZarAff.mapAlg_comp, hF₀ ⟨i, l.down⟩, ← hdp i]
    exact DivFamZarAff.mk_eq_mk_iff.mpr (hGdiv i l.down)

end AlgebraicGeometry
