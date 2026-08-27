/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.ProjectiveMorphism
import AlgebraicJacobian.Picard.HilbertPolynomial
import AlgebraicJacobian.Picard.PullbackFinitePresentation

/-!
# Serre finiteness for the section graded module (statement)

The deep remaining input of the Hilbert-polynomial lane
(`lem:sectionGradedModule_fg`, inbox `I-0109`): for a projective scheme over
a field carrying a very ample line bundle `L` and a coherent sheaf `F`, the
section graded ring `R(X, L) = ⊕ₘ Γ(X, L^{⊗m})` is Noetherian, the section
graded module `M(X, F, L) = ⊕ₘ Γ(X, F ⊗ L^{⊗m})` is a finite module over it,
and each graded component is a finite-dimensional `κ`-vector space.

This file gives the **honest statement** against the projectivity vocabulary
of `Picard/ProjectiveMorphism.lean` (the `IsProjectiveWith` closed-immersion
predicate — very ampleness in the encoding settled in inbox `I-0118`), as a
named typed `sorry` leaf: the proof is Serre's theorem ([Hartshorne] II.5.17
ff., [Nitsure] §1) and is genuinely deep (multi-session; it needs the
pushforward-to-projective-space reduction and cohomological finiteness on
`ℙⁿ`).

Compared with the blueprint node, which hypothesises an *ample* `L` and
passes to a Veronese power, the Lean statement hypothesises the very ample
form directly (`IsProjectiveWith`) — this is the form in which the
Quot-scheme endgame ([Nitsure] §5) consumes it.

Blueprint: `lem:sectionGradedModule_fg`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The structural `κ`-algebra structure on the global sections of a scheme
over `Spec κ` (the absolute analogue of `Scheme.Hom.fiberResidueMap`). -/
def Scheme.Hom.structuralSectionsHom {X : Scheme.{0}} {κ : Type} [CommRing κ]
    (π : X ⟶ Spec (CommRingCat.of κ)) : κ →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv ≫ π.appTop).hom

/-- **Serre finiteness for the section graded module**
(`lem:sectionGradedModule_fg`; [Nitsure] §1, [Hartshorne] II.5.17 ff.):
for `π : X ⟶ Spec κ` projective carrying the very ample line bundle `L`
and a coherent (finitely presented) sheaf `F` on `X`,

1. the section graded ring `⊕ₘ Γ(X, L^{⊗m})` is Noetherian;
2. the section graded module `⊕ₘ Γ(X, F ⊗ L^{⊗m})` is a finite module
   over it;
3. each component `Γ(X, F ⊗ L^{⊗m})` is a finite-dimensional `κ`-vector
   space (via the structural `κ`-action).

NAMED LEAF (`sorry`): the geometric heart of the Hilbert-polynomial lane
(inbox `I-0109`), awaiting the pushforward-to-`ℙⁿ` reduction and
cohomological finiteness of coherent sheaves on projective space. -/
theorem sectionGradedModule_fg {X : Scheme.{0}} {κ : Type} [Field κ]
    (π : X ⟶ Spec (CommRingCat.of κ)) (L F : X.Modules)
    (hproj : π.IsProjectiveWith L) (hF : F.IsFinitePresentation) :
    (letI := Scheme.Modules.sectionGradedRing_gsemiring L
     IsNoetherianRing (DirectSum ℕ (Scheme.Modules.sectionDeg L)))
    ∧ (letI := Scheme.Modules.sectionGradedRing_gsemiring L
       letI := Scheme.Modules.sectionGradedModule_gmodule F L
       Module.Finite (DirectSum ℕ (Scheme.Modules.sectionDeg L))
         (DirectSum ℕ (Scheme.Modules.moduleSectionDeg F L)))
    ∧ ∀ m : ℕ,
        letI := Module.compHom (Scheme.Modules.moduleSectionDeg F L m)
          π.structuralSectionsHom
        FiniteDimensional κ (Scheme.Modules.moduleSectionDeg F L m) := by
  sorry

/-! ## Descent to scheme-theoretic fibres — the Hilbert-lane connector

The absolute leaf `sectionGradedModule_fg` is stated over a *field*; the Hilbert
polynomial `Scheme.hilbertPolynomial` and its graded Hilbert function
`Scheme.hilbertFunction` (`Picard/HilbertPolynomial.lean`) live at the
scheme-theoretic fibre `X_s = π.fiber s` over the residue field `κ(s)`, which is
a field.  The lemmas below are the sorry-free geometric glue that transports
`IsProjectiveWith` and finite presentation to a fibre (both via the already
proved `IsProjectiveWith.baseChange` and `Modules.pullback_isFinitePresentation`),
so the deep Serre leaf applies fibrewise; the corollary
`hilbertFunction_finiteDimensional` then shows the graded Hilbert function is a
genuine (finite) dimension for projective fibres — the finiteness half of the
bridge to `AlgebraicGeometry.gradedModule_hilbertSeries_rational`
(inbox `I-0109`).  The remaining step — packaging finite generation as the
`MvPolynomial`-finiteness input of that engine — is documented there. -/

variable {X S : Scheme.{0}}

/-- **`IsProjectiveWith` descends to scheme-theoretic fibres**: if `π : X ⟶ S`
is projective carrying `L`, then the structural morphism of the fibre
`X_s = π.fiber s`, namely `π.fiberToSpecResidueField s : X_s ⟶ Spec κ(s)`, is
projective carrying the restriction `L_s = π.fiberModule s L`.  Immediate from
`IsProjectiveWith.baseChange` along `S.fromSpecResidueField s`, since the fibre
is the base change of `π` along that morphism (`Scheme.Hom.fiber`). -/
theorem Scheme.Hom.IsProjectiveWith.fiber {π : X ⟶ S} {L : X.Modules}
    (h : π.IsProjectiveWith L) (s : S) :
    (π.fiberToSpecResidueField s).IsProjectiveWith (π.fiberModule s L) :=
  h.baseChange (S.fromSpecResidueField s)

/-- **Finite presentation descends to scheme-theoretic fibres**: the restriction
`F_s = π.fiberModule s F` of a finitely presented sheaf `F` to the fibre is
finitely presented (pullback of a finitely presented sheaf along the fibre
embedding `π.fiberι s`). -/
theorem Scheme.Hom.fiberModule_isFinitePresentation (π : X ⟶ S) (s : S)
    {F : X.Modules} (hF : F.IsFinitePresentation) :
    (π.fiberModule s F).IsFinitePresentation :=
  Scheme.Modules.pullback_isFinitePresentation (π.fiberι s) F hF

/-- **Serre finiteness along a fibre** (`lem:sectionGradedModule_fg` specialised
to the fibre over `s`): for `π : X ⟶ S` projective carrying `L` and `F` finitely
presented, the section graded ring of the fibre restriction `L_s` is Noetherian,
and the section graded module of `F_s` is finite over it.  This is the deep leaf
`sectionGradedModule_fg` applied to the fibre morphism via
`IsProjectiveWith.fiber` and `fiberModule_isFinitePresentation`; it inherits the
single named `sorry` of that leaf and no other.  The finite-dimensionality of
each graded component — the third conclusion of `sectionGradedModule_fg`,
matching the graded Hilbert function — is recorded separately as
`hilbertFunction_finiteDimensional` (stated with the `Scheme.hilbertFunction`
residue-field module structure). -/
theorem sectionGradedModule_fg_fiber (π : X ⟶ S) (L F : X.Modules) (s : S)
    (hproj : π.IsProjectiveWith L) (hF : F.IsFinitePresentation) :
    (letI := Scheme.Modules.sectionGradedRing_gsemiring (π.fiberModule s L)
     IsNoetherianRing (DirectSum ℕ (Scheme.Modules.sectionDeg (π.fiberModule s L))))
    ∧ (letI := Scheme.Modules.sectionGradedRing_gsemiring (π.fiberModule s L)
       letI := Scheme.Modules.sectionGradedModule_gmodule
         (π.fiberModule s F) (π.fiberModule s L)
       Module.Finite (DirectSum ℕ (Scheme.Modules.sectionDeg (π.fiberModule s L)))
         (DirectSum ℕ (Scheme.Modules.moduleSectionDeg
           (π.fiberModule s F) (π.fiberModule s L)))) :=
  ⟨(sectionGradedModule_fg (π.fiberToSpecResidueField s) (π.fiberModule s L)
      (π.fiberModule s F) (hproj.fiber s)
      (Scheme.Hom.fiberModule_isFinitePresentation π s hF)).1,
   (sectionGradedModule_fg (π.fiberToSpecResidueField s) (π.fiberModule s L)
      (π.fiberModule s F) (hproj.fiber s)
      (Scheme.Hom.fiberModule_isFinitePresentation π s hF)).2.1⟩

/-- **The graded Hilbert function is a genuine (finite) dimension for projective
fibres**: for `π : X ⟶ S` projective carrying `L` and `F` finitely presented,
each twisted-section space `Γ(X_s, F_s ⊗ L_s^{⊗m})` whose `κ(s)`-dimension is
`Scheme.hilbertFunction π L F s m` is finite-dimensional — so the graded Hilbert
function is not merely the `Module.finrank` junk value.  This is the
finite-dimensionality half of the input to the graded Hilbert–Serre rationality
engine (`AlgebraicGeometry.gradedModule_hilbertSeries_rational`, inbox
`I-0109`). -/
theorem hilbertFunction_finiteDimensional (π : X ⟶ S) (L F : X.Modules) (s : S)
    (hproj : π.IsProjectiveWith L) (hF : F.IsFinitePresentation) (m : ℕ) :
    letI := π.fiberSectionsModule s
      (Scheme.Modules.moduleTensorPow (π.fiberModule s F) (π.fiberModule s L) m)
    FiniteDimensional (S.residueField s)
      Γ(Scheme.Modules.moduleTensorPow (π.fiberModule s F) (π.fiberModule s L) m, ⊤) :=
  (sectionGradedModule_fg (π.fiberToSpecResidueField s) (π.fiberModule s L)
    (π.fiberModule s F) (hproj.fiber s)
    (Scheme.Hom.fiberModule_isFinitePresentation π s hF)).2.2 m

/-! ## Engine-ready packaging and the rationality of the Hilbert function

The graded Hilbert–Serre rationality engine
`AlgebraicGeometry.gradedModule_hilbertSeries_rational`
(`Picard/GradedHilbertSerre.lean`, sorry-free) turns an abstract finitely
generated `ℕ`-graded `κ`-vector space — one carrying `r` commuting degree-one
endomorphisms and finite over the polynomial ring `κ[X₀,…,X_{r-1}]` — into a
rational Hilbert function (`AlgebraicGeometry.IsRatHilb`).  To feed the geometric
fibre section module `⊕ₘ Γ(X_s, F_s ⊗ L_s^{⊗m})` into that engine we package its
input as the structure `GradedHilbert` and factor Serre finiteness **in
engine-ready form** as the single honest leaf `gradedHilbert_fiber` (a companion
to `sectionGradedModule_fg`: it additionally records the degree-one coordinate
action from the very-ample embedding `X_s ↪ ℙ^d`, the `MvPolynomial` reshaping of
inbox `I-0109`).  The rationality of the graded Hilbert function
`Scheme.hilbertFunction`, and hence the genuineness of the Hilbert polynomial
`Scheme.hilbertPolynomial` (`hilbertPolynomial_eval_eventually_of_projective`),
then follow as **sorry-free glue** — the `DirectSum`-decomposition bridge of
inbox `I-0109`. -/

/-- **Engine-ready packaging of Serre finiteness** for a Hilbert function
`f : ℕ → ℕ` over a field `κ`: a finitely generated (over a polynomial ring in `r`
degree-one variables) `ℕ`-graded `κ`-vector space whose `n`-th graded piece has
dimension `f n`.  This bundles exactly the data and hypotheses consumed by the
graded Hilbert–Serre rationality engine
`AlgebraicGeometry.gradedModule_hilbertSeries_rational`; the engine call is
`GradedHilbert.isRatHilb`.  Geometrically `M` is the fibre section module
`⊕ₘ Γ(X_s, F_s ⊗ L_s^{⊗m})`, `grading n` is its `n`-th piece, and `gen` are the
`d+1` multiplications by the homogeneous coordinate sections. -/
structure GradedHilbert (κ : Type u) [Field κ] (f : ℕ → ℕ) where
  /-- Number of degree-one polynomial generators (`d+1` homogeneous coordinates). -/
  r : ℕ
  /-- The ambient graded `κ`-vector space. -/
  M : Type u
  [addCommGroup : AddCommGroup M]
  [module : Module κ M]
  /-- The internal `ℕ`-grading. -/
  grading : ℕ → Submodule κ M
  [decomposition : DirectSum.Decomposition grading]
  /-- Each graded piece is finite-dimensional. -/
  finiteDimensional : ∀ n, FiniteDimensional κ (grading n)
  /-- The `r` commuting degree-one endomorphisms (coordinate multiplications). -/
  gen : Fin r → Module.End κ M
  /-- The generators commute. -/
  gen_comm : ∀ i j, Commute (gen i) (gen j)
  /-- Each generator raises the grading degree by one. -/
  gen_raisesDegree : ∀ i, GradedModule.RaisesDegree grading (gen i)
  /-- The graded pieces realise the prescribed dimensions `f`. -/
  finrank_grading : ∀ n, Module.finrank κ (grading n) = f n
  /-- `M` is finite over the polynomial ring `κ[X₀,…,X_{r-1}]` acting via `gen`. -/
  finite : letI := GradedModule.polyModule gen gen_comm
    Module.Finite (MvPolynomial (Fin r) κ) M

-- Register the carried instances as the *projection* instances of the structure, so
-- typeclass search returns exactly the terms appearing in `GradedHilbert.finite`'s type
-- (avoids the `polyModule`/`compHom` `whnf` blow-up that fresh `haveI` fvars would cause).
attribute [instance] GradedHilbert.addCommGroup GradedHilbert.module
  GradedHilbert.decomposition GradedHilbert.finiteDimensional

/-- The Hilbert function packaged by a `GradedHilbert` datum is a rational Hilbert
function of order `r`: the sorry-free graded Hilbert–Serre engine call
(`AlgebraicGeometry.gradedModule_hilbertSeries_rational`) followed by the
dimension identification `GradedHilbert.finrank_grading`. -/
theorem GradedHilbert.isRatHilb {κ : Type u} [Field κ] {f : ℕ → ℕ}
    (H : GradedHilbert κ f) : IsRatHilb (fun n => (f n : ℚ)) H.r := by
  -- The carried instances are found via the structure's projection instances
  -- (registered above), matching the terms in `H.finite`'s type exactly, so the
  -- finiteness argument unifies without a `polyModule`/`compHom` `whnf` blow-up.
  have h : IsRatHilb (fun n => (Module.finrank κ (H.grading n) : ℚ)) H.r :=
    gradedModule_hilbertSeries_rational H.grading H.gen H.gen_comm
      H.gen_raisesDegree H.finite
  have hfun : (fun n => (f n : ℚ))
      = fun n => (Module.finrank κ (H.grading n) : ℚ) := by
    funext n; rw [H.finrank_grading]
  rw [hfun]; exact h

variable {X S : Scheme.{0}}

/-- **Serre finiteness in engine-ready form** (companion to
`sectionGradedModule_fg`; `lem:sectionGradedModule_fg`, [Nitsure] §1): for
`π : X ⟶ S` projective carrying the very ample line bundle `L` and a coherent
(finitely presented) sheaf `F`, the graded Hilbert function
`m ↦ dim_{κ(s)} Γ(X_s, F_s ⊗ L_s^{⊗m})` at each fibre over `s : S` is packaged by
a `GradedHilbert` datum over the residue field `κ(s)`.

NAMED LEAF (`sorry`): this is `sectionGradedModule_fg` (Serre) restated in the
form the graded Hilbert–Serre rationality engine consumes.  Taking `M` to be the
fibre section module `⊕ₘ Γ(X_s, F_s ⊗ L_s^{⊗m})` and the `d+1` generators to be
the coordinate sections of the very-ample embedding `X_s ↪ ℙ^d`, its content is
the finite generation of that module over the homogeneous coordinate ring
`κ(s)[x₀,…,x_d]` — the `MvPolynomial` reshaping documented in inbox `I-0109`.
Compared with the abstract-section-ring finiteness of `sectionGradedModule_fg`,
this form additionally records the degree-one coordinate action, which is what
makes the Hilbert polynomial genuine
(`hilbertPolynomial_eval_eventually_of_projective`). -/
theorem gradedHilbert_fiber (π : X ⟶ S) (L F : X.Modules) (s : S)
    (hproj : π.IsProjectiveWith L) (hF : F.IsFinitePresentation) :
    Nonempty (GradedHilbert (S.residueField s) (Scheme.hilbertFunction π L F s)) :=
  sorry

/-- **The graded Hilbert function of a projective morphism is a rational Hilbert
function**: from the engine-ready Serre finiteness `gradedHilbert_fiber` via
`GradedHilbert.isRatHilb`.  Inherits the single leaf `gradedHilbert_fiber` and no
other. -/
theorem hilbertFunction_isRatHilb (π : X ⟶ S) (L F : X.Modules) (s : S)
    (hproj : π.IsProjectiveWith L) (hF : F.IsFinitePresentation) :
    ∃ d : ℕ, IsRatHilb (fun m => (Scheme.hilbertFunction π L F s m : ℚ)) d :=
  let ⟨H⟩ := gradedHilbert_fiber π L F s hproj hF
  ⟨H.r, H.isRatHilb⟩

/-- **The Hilbert polynomial genuinely computes the Hilbert function** for a
projective morphism over a locally noetherian base: for all `m ≫ 0`,
`Scheme.hilbertPolynomial π L F s` evaluated at `m` equals
`dim_{κ(s)} Γ(X_s, F_s ⊗ L_s^{⊗m})` (`Scheme.hilbertFunction π L F s m`).
Combines `hilbertFunction_isRatHilb` with the polynomial-extraction API
`Scheme.hilbertPolynomial_eval_of_isRatHilb`; this is the point at which the
Hilbert polynomial ceases to be a formal `Classical.choice` and becomes the
Snapper/Hilbert polynomial of the fibre.  Inherits the single leaf
`gradedHilbert_fiber`. -/
theorem hilbertPolynomial_eval_eventually_of_projective [IsLocallyNoetherian S]
    (π : X ⟶ S) [LocallyOfFiniteType π] (L F : X.Modules) (s : S)
    (hproj : π.IsProjectiveWith L) (hF : F.IsFinitePresentation) :
    ∃ N : ℕ, ∀ m : ℕ, N < m →
      (Scheme.hilbertPolynomial π L F s).eval (m : ℚ)
        = (Scheme.hilbertFunction π L F s m : ℚ) := by
  obtain ⟨d, hrat⟩ := hilbertFunction_isRatHilb π L F s hproj hF
  exact Scheme.hilbertPolynomial_eval_of_isRatHilb π L F s hrat

end AlgebraicGeometry
