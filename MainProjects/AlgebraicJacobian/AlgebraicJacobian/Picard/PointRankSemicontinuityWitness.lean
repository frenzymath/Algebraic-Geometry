/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PointRankSemicontinuity
import AlgebraicJacobian.Picard.RigidPushforwardTransfer

/-!
# Non-vacuity of the B5 sublevel openness, on the campaign's own data

`Scheme.Modules.isOpen_pointRank_le` (`Picard/PointRankSemicontinuity.lean`)
quantifies over a finitely presented quasi-coherent module on a locally
noetherian scheme.  This file exhibits the campaign's own datum satisfying
those binders, so the theorem is known to have a consumer rather than merely
to be true.

The witness is the pushforward `(π_A)_* L` of a line bundle `L` on `C_A` along
the finite map `π_A : C_A ⟶ ℙ¹_A` — exactly the object the B3 engine is built
from.  Two things are worth stating about it:

* **No `h¹`-vanishing hypothesis occurs.**  The only hypothesis on `L` is
  `Scheme.LineBundle.IsLocallyTrivial`.  This is the point of the B5
  statement, and it is why the B3 headlines cannot serve it: those carry
  `∀ t, q.FiberH1Vanishing L t`, whose antecedent has **no producer anywhere
  in the tree** (recorded at `Picard/RigidPushforwardP1Witness.lean`:50, :264).
  So a `FiberH1Vanishing`-gated statement has never been applied to concrete
  data, whereas the theorem witnessed here has.
* **Finite presentation of the pushforward is itself `h¹`-free.**  It is
  `Adelic.pushforward_finiteMapToP1BaseChange_isFinitePresentation`, which
  needs only local triviality of `L` (Stacks 01PC/01WG plus the noetherian
  coherence criterion `Scheme.Modules.isFinitePresentation_of_finite_sections`).

## What this does *not* witness

It does not witness `Scheme.HasH0Semicontinuity`
(`Picard/SemicontinuityH0.lean`).  That class is about `q.fiberH0 L t`, the
dimension of the global sections of `L` on the scheme-theoretic fibre
*curve*, whereas `pointRank` here is the fibre dimension of a module on
`ℙ¹_A`.  The gap between them is recorded in the module docstring of
`Picard/PointRankSemicontinuity.lean` and, with the measurement, in the inbox
issue filed by lane `ajc-p4`.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Module Limits

namespace AlgebraicGeometry

namespace Adelic

variable {k : Type u} [Field k]

/-- **The B5 sublevel openness fires on the campaign's own datum**: for a
curve `C/k` with a finite map to `ℙ¹` and a *locally trivial* `L` on `C_A`,
the fibre-dimension sublevel loci of `(π_A)_* L` are open on `ℙ¹_A`.

No `h¹`-vanishing hypothesis appears — contrast the B3 headlines, whose
`FiberH1Vanishing` antecedent has no producer in the tree. -/
theorem isOpen_pointRank_pushforward_finiteMapToP1_le
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    [HasFiniteMapToP1 C]
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hL : Scheme.LineBundle.IsLocallyTrivial L) (e : ℕ) :
    IsOpen {t : (Limits.pullback (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A))) : Scheme.{u}) |
      Scheme.Modules.pointRank _
        ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L) t ≤ e} := by
  haveI := hL.isFinitePresentation
  haveI : IsFinite (finiteMapToP1BaseChange A C) := isFinite_finiteMapToP1BaseChange A C
  haveI := Scheme.Modules.pushforward_isQuasicoherent (finiteMapToP1BaseChange A C) L
  haveI := pushforward_finiteMapToP1BaseChange_isFinitePresentation A C L hL
  -- `ℙ¹_A` is locally noetherian: `A` is noetherian (Hilbert basis) and
  -- `ℙ¹_A ⟶ Spec A` is locally of finite type as a base change.
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : LocallyOfFiniteType (p1Over k).hom :=
    inferInstanceAs (LocallyOfFiniteType
      ((ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k))) ↘ Spec (CommRingCat.of k)))
  haveI : LocallyOfFiniteType
      (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
    MorphismProperty.pullback_snd _ _ ‹_›
  haveI : IsLocallyNoetherian
      (Limits.pullback (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
  exact Scheme.Modules.isOpen_pointRank_le _ e

/-- The same, closed form: the superlevel loci are closed.  This is the shape
milestone B6 consumes. -/
theorem isClosed_le_pointRank_pushforward_finiteMapToP1
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    [HasFiniteMapToP1 C]
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hL : Scheme.LineBundle.IsLocallyTrivial L) (e : ℕ) :
    IsClosed {t : (Limits.pullback (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A))) : Scheme.{u}) |
      e + 1 ≤ Scheme.Modules.pointRank _
        ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L) t} := by
  have hcompl : {t : (Limits.pullback (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A))) : Scheme.{u}) |
        e + 1 ≤ Scheme.Modules.pointRank _
          ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L) t}
      = {t : (Limits.pullback (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A))) : Scheme.{u}) |
        Scheme.Modules.pointRank _
          ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L) t ≤ e}ᶜ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    omega
  rw [hcompl]
  exact (isOpen_pointRank_pushforward_finiteMapToP1_le C A L hL e).isClosed_compl

end Adelic

end AlgebraicGeometry
