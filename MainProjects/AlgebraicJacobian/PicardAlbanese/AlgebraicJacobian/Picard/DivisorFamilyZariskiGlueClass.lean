/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyZariskiGlue

/-!
# Zariski gluing of the divisor functor: chart restriction and class assembly (DD-2 S5)

The class-level half of the divisor-functor Zariski gluing
(`informal/spec-dd-2.md` §5) on top of the glued local-equation system
`AlgebraicGeometry.awayGluedEquations`:

* `AlgebraicGeometry.divEq_pullback_awayGluedEquations` — **chart restriction**: the
  pullback of the glued system along the open immersion `relCurveMap C R (S i)` is
  divisor-equal to the `i`-th local system.  The members and equations restrict back
  by construction (the immersion round trip); across the chart choice the pointwise
  cross units spread to the full overlaps by the Kit engines.
* `AlgebraicGeometry.DivFam.mapAlg_mk_eq_of_divEq_awayGluedEquations` — any certified
  family over `R` divisor-equal to the glued system restricts to the given classes
  under `DivFam.mapAlg`.
* `AlgebraicGeometry.DivFam.exists_glue_of_away_compat_of_certifiedRep` — **the
  conditional keystone**: compatible classes over a finite covering family of
  localizations glue to a class over `R`, GIVEN a certified representative of the
  glued system.

## The open certificate seam (the S5 wall, recorded)

The unconditional keystone `DivFam.exists_glue_of_away_compat` needs a certified
adaptation over `R` of (a system divisor-equal to) `awayGluedEquations`.  The
spec-dd-2 §5 route — pieces = the `A_i`-pieces cleared of denominators
(`D(h̃·g̃ᵢᴺ)`), certificate by localization-span descent through the landed
base-change transports — is NOT viable: a cleared piece lies inside the `g̃ᵢ`-locus,
so its colength `Γ(D(h̃·g̃ᵢᴺ))⧸(f̃)` is a module over the localization `S i`, and its
further localization at `g j` (`j ≠ i`) is an `S i ⊗ S j`-module that is not finite
over `S j` (already for the zero-section divisor over `R = k[u]`, `g = (u, 1-u)`:
the cleared piece `D(ũ)` has colength `R_u`, and `(R_u)_{1-u}` is not module-finite
over `R_{1-u}`) — the hypotheses of `Module.Finite.of_localizationSpan`-shaped
descent fail, clause (c1) is false for such pieces.  A certified adaptation over `R`
must instead have pieces whose divisor traces are clopen in the divisor
(the `π`-fibre tri-partition of the divisor, whose clopenness IS Zariski-local and
descends from the `A_i`-certificates); building that extraction is a separate brick
— hence the certificate-provider hypothesis `hcert` below, which that brick will
discharge.  Uniqueness needs no condition (`DivFam.eq_of_away_eq`, S4).
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

variable {k : Type u} [Field k]
variable {C : Over (Spec (.of k))} {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsAffineHom π]
variable {ι : Type u} (g : ι → R) (S : ι → Type u) [∀ i, CommRing (S i)]
  [∀ i, Algebra k (S i)] [∀ i, Algebra R (S i)] [∀ i, IsScalarTower k R (S i)]
  [∀ i, IsLocalization.Away (g i) (S i)]
variable [∀ i, IsOpenImmersion (relCurveMap C R (S i))]
variable {n : ℕ} (E : ∀ i, CertifiedDivisorFamily C (S i) π n)
variable (T : ι → ι → Type u) [∀ i j, CommRing (T i j)] [∀ i j, Algebra k (T i j)]
  [∀ i j, Algebra R (T i j)] [∀ i j, IsScalarTower k R (T i j)]
  [∀ i j, Algebra (S i) (T i j)] [∀ i j, Algebra (S j) (T i j)]
  [∀ i j, IsScalarTower k (S i) (T i j)] [∀ i j, IsScalarTower k (S j) (T i j)]
  [∀ i j, IsScalarTower R (S i) (T i j)] [∀ i j, IsScalarTower R (S j) (T i j)]
  [∀ i j, IsLocalization.Away (g i * g j) (T i j)]

/-- Restriction of a section along `W ≤ V ≤ U` composes to restriction along `W ≤ U`. -/
private lemma res_res {X : Scheme.{u}} {W V U : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom s)
      = (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

@[simp]
lemma awayGluedEquations_cover_opens (hg : Ideal.span (Set.range g) = ⊤)
    (hcompat : AwayCompatDivEq S E T) (y : relCurve C R) :
    (awayGluedEquations g S E T hg hcompat).cover.opens y
      = relCurveMap C R (S (awayGlueIndex g S hg y)) ''ᵁ
          (E (awayGlueIndex g S hg y)).eqns.cover.opens (awayGlueLift g S hg y) :=
  rfl

@[simp]
lemma awayGluedEquations_eqn (hg : Ideal.span (Set.range g) = ⊤)
    (hcompat : AwayCompatDivEq S E T) (y : relCurve C R) :
    (awayGluedEquations g S E T hg hcompat).eqn y
      = ((relCurveMap C R (S (awayGlueIndex g S hg y))).appIso
          ((E (awayGlueIndex g S hg y)).eqns.cover.opens
            (awayGlueLift g S hg y))).inv.hom
        ((E (awayGlueIndex g S hg y)).eqns.eqn (awayGlueLift g S hg y)) :=
  rfl

/-- **Chart restriction of the glued system** (`informal/spec-dd-2.md` §5): the pullback
of `awayGluedEquations` along the open immersion `relCurveMap C R (S i)` is
divisor-equal to the `i`-th local system.  Pointwise: on the overlap of the glued
member with the image of the chart member, the transported equations differ by a unit
(the cross unit spread by the Kit engine), and the relation pulls back up the
immersion, where the transported equation restricts back to the chart equation (the
immersion round trip). -/
theorem divEq_pullback_awayGluedEquations (hg : Ideal.span (Set.range g) = ⊤)
    (hcompat : AwayCompatDivEq S E T) (i : ι) (hreg) :
    Scheme.LocalEquations.DivEq
      ((awayGluedEquations g S E T hg hcompat).pullback (relCurveMap C R (S i)) hreg)
      (E i).eqns := by
  classical
  refine ⟨((awayGluedEquations g S E T hg hcompat).cover.pullback
      (relCurveMap C R (S i))) ⊓ (E i).eqns.cover,
    fun z' => inf_le_left, fun z' => inf_le_right, fun z' => ?_⟩
  -- the downstairs overlap of the glued member with the image of the chart member
  obtain ⟨uO, huO⟩ := Scheme.exists_unit_mul_of_locally_unit_mul
    (X := relCurve C R)
    (V := (awayGluedEquations g S E T hg hcompat).cover.opens
        ((relCurveMap C R (S i)).base z')
      ⊓ relCurveMap C R (S i) ''ᵁ (E i).eqns.cover.opens z')
    (s := ((relCurve C R).presheaf.map (homOfLE inf_le_left).op).hom
      ((awayGluedEquations g S E T hg hcompat).eqn ((relCurveMap C R (S i)).base z')))
    (t := ((relCurve C R).presheaf.map (homOfLE inf_le_right).op).hom
      (((relCurveMap C R (S i)).appIso ((E i).eqns.cover.opens z')).inv.hom
        ((E i).eqns.eqn z')))
    (fun z hz => by
      rw [(relCurve C R).presheaf.germ_res_apply]
      exact germ_awayTransport_mem_nonZeroDivisors S E i z' z hz.2)
    (fun z hz => by
      obtain ⟨W, hWO, hzW, u, hu⟩ := exists_res_awayTransport_eq_unit_mul g S E T
        hcompat
        (inf_le_left :
          (awayGluedEquations g S E T hg hcompat).cover.opens
              ((relCurveMap C R (S i)).base z')
            ⊓ relCurveMap C R (S i) ''ᵁ (E i).eqns.cover.opens z' ≤ _)
        (inf_le_right :
          (awayGluedEquations g S E T hg hcompat).cover.opens
              ((relCurveMap C R (S i)).base z')
            ⊓ relCurveMap C R (S i) ''ᵁ (E i).eqns.cover.opens z' ≤ _)
        z hz
      refine ⟨W, hWO, hzW, u, ?_⟩
      rw [res_res, res_res]
      exact hu)
  -- pull the overlap unit up the immersion
  have hpre : ((awayGluedEquations g S E T hg hcompat).cover.pullback
        (relCurveMap C R (S i))).opens z' ⊓ (E i).eqns.cover.opens z'
      ≤ relCurveMap C R (S i) ⁻¹ᵁ
        ((awayGluedEquations g S E T hg hcompat).cover.opens
            ((relCurveMap C R (S i)).base z')
          ⊓ relCurveMap C R (S i) ''ᵁ (E i).eqns.cover.opens z') :=
    (relCurveMap C R (S i)).le_preimage_inf inf_le_left
      (inf_le_right.trans ((relCurveMap C R (S i)).preimage_image_eq _).ge)
  refine ⟨(relCurveMap C R (S i)).unitsAppLE _ _ hpre uO, ?_⟩
  -- transport the unit relation through `appLE`
  have hkey := congrArg ((relCurveMap C R (S i)).appLE _ _ hpre).hom huO
  rw [map_mul] at hkey
  -- the left factor: the restricted pulled equation
  have hL : ((relCurveMap C R (S i)).appLE _ _ hpre).hom
      (((relCurve C R).presheaf.map (homOfLE inf_le_left).op).hom
        ((awayGluedEquations g S E T hg hcompat).eqn
          ((relCurveMap C R (S i)).base z')))
      = ((relCurve C (S i)).presheaf.map (homOfLE (inf_le_left :
          ((awayGluedEquations g S E T hg hcompat).cover.pullback
              (relCurveMap C R (S i))).opens z' ⊓ (E i).eqns.cover.opens z'
            ≤ _)).op).hom
        (Scheme.LocalEquations.pullbackEqn (relCurveMap C R (S i))
          (awayGluedEquations g S E T hg hcompat) z') := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
      Scheme.LocalEquations.pullbackEqn_res]
  -- the right factor: the immersion round trip back to the chart equation
  have hR : ((relCurveMap C R (S i)).appLE _ _ hpre).hom
      (((relCurve C R).presheaf.map (homOfLE inf_le_right).op).hom
        (((relCurveMap C R (S i)).appIso ((E i).eqns.cover.opens z')).inv.hom
          ((E i).eqns.eqn z')))
      = ((relCurve C (S i)).presheaf.map (homOfLE (inf_le_right :
          ((awayGluedEquations g S E T hg hcompat).cover.pullback
              (relCurveMap C R (S i))).opens z' ⊓ (E i).eqns.cover.opens z'
            ≤ _)).op).hom ((E i).eqns.eqn z') := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
      Scheme.Hom.appIso_inv_appLE_apply]
  rw [hL, hR] at hkey
  exact hkey

/-! ## The class-level assembly -/

/-- **Chart restriction of a divisor-equal certified family**: any certified family `G`
over `R` whose system is divisor-equal to the glued system restricts, under
`DivFam.mapAlg`, to the given local classes.  The pullback of `G.eqns` along the
comparison is divisor-equal to the pullback of the glued system (`divEq_pullback`),
which is divisor-equal to the local system (`divEq_pullback_awayGluedEquations`); the
`hreg` discharges are the certificate on the `G`-side and the open-immersion stalk
isomorphism on the glued side (Kit). -/
theorem DivFam.mapAlg_mk_eq_of_divEq_awayGluedEquations
    (hg : Ideal.span (Set.range g) = ⊤) (hcompat : AwayCompatDivEq S E T)
    (G : CertifiedDivisorFamily C R π n)
    (hG : Scheme.LocalEquations.DivEq G.eqns (awayGluedEquations g S E T hg hcompat))
    (i : ι) :
    DivFam.mapAlg (S i) n (DivFam.mk G) = DivFam.mk (E i) := by
  rw [DivFam.mapAlg_mk]
  refine DivFam.mk_eq_mk_iff.mpr ?_
  exact Scheme.LocalEquations.DivEq.trans
    (Scheme.LocalEquations.divEq_pullback (relCurveMap C R (S i)) hG
      (G.adaptation.germ_pullbackEqn_mem_nonZeroDivisors (S i)
        G.certified.projective_colength)
      (fun y z hz =>
        Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
          (relCurveMap C R (S i)) (awayGluedEquations g S E T hg hcompat) y z hz))
    (divEq_pullback_awayGluedEquations g S E T hg hcompat i _)

/-- **Zariski gluing of the divisor functor, conditional form**
(`informal/spec-dd-2.md` §5): a family of divisor classes on a covering family of
localizations of `R`, compatible on the pairwise overlap carriers, is the family of
restrictions of a class over `R` — GIVEN a certified representative of the glued
system over `R` (the hypothesis `hcert`; see the module docstring for the open
certificate seam this isolates).  Uniqueness of the glued class is S4's
`DivFam.eq_of_away_eq`. -/
theorem DivFam.exists_glue_of_away_compat_of_certifiedRep
    (hg : Ideal.span (Set.range g) = ⊤) (F : ∀ i, DivFam C (S i) π n)
    (hcompat : ∀ i j, DivFam.mapAlg (T i j) n (F i) = DivFam.mapAlg (T i j) n (F j))
    (hcert : ∀ (E : ∀ i, CertifiedDivisorFamily C (S i) π n),
      (∀ i, DivFam.mk (E i) = F i) → ∀ hdiv : AwayCompatDivEq S E T,
      ∃ G : CertifiedDivisorFamily C R π n,
        Scheme.LocalEquations.DivEq G.eqns (awayGluedEquations g S E T hg hdiv)) :
    ∃ F₀ : DivFam C R π n, ∀ i, DivFam.mapAlg (S i) n F₀ = F i := by
  classical
  -- representatives of the local classes
  have hrep : ∀ i, ∃ Ei : CertifiedDivisorFamily C (S i) π n, DivFam.mk Ei = F i :=
    fun i => Quotient.exists_rep (F i)
  choose E hE using hrep
  -- the representative-level compatibility
  have hdiv : AwayCompatDivEq S E T := by
    intro i j
    have h := hcompat i j
    rw [← hE i, ← hE j, DivFam.mapAlg_mk, DivFam.mapAlg_mk] at h
    exact DivFam.mk_eq_mk_iff.mp h
  -- the certified representative of the glued system, and its restrictions
  obtain ⟨G, hG⟩ := hcert E hE hdiv
  exact ⟨DivFam.mk G, fun i =>
    (DivFam.mapAlg_mk_eq_of_divEq_awayGluedEquations g S E T hg hdiv G hG i).trans
      (hE i)⟩

end AlgebraicGeometry
