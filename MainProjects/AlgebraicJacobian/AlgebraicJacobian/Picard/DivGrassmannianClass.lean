/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivPushforwardFlat
import AlgebraicJacobian.Picard.GrassmannianRepresentability

/-!
# Core divisor-to-Grassmannian classifying objects

This file contains the small representation-facing core of D2: the twisted
divisor sheaf, its evaluation map, and the resulting locally free quotient and
Grassmannian class.  The longer analytic proofs live in
`DivGrassmannianEmbedding`; keeping this core separate lets the D3 universal
candidate import it without recompiling that large module.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

namespace Scheme

namespace DivFamily

variable {S X : Scheme.{u}} {π : X ⟶ S} {T : Over S}

/-- The twist of the divisor structure sheaf by a module on the original
family.  For the D2 embedding, `L` is the chosen sufficiently positive
projective twist. -/
noncomputable def twist (L : X.Modules) (x : DivFamily π T) :
    (pullback π T.hom).Modules :=
  Modules.tensorObj ((Modules.pullback (pullback.fst π T.hom)).obj L) x.F

/-- Tensor the divisor quotient `O -> O_D` with the pulled-back twist. -/
noncomputable def twistQuotientMap (L : X.Modules) (x : DivFamily π T) :
    (Modules.pullback (pullback.fst π T.hom)).obj L ⟶ x.twist L :=
  (Modules.tensorObj_right_unitor _).inv ≫
    Modules.tensorObj_functoriality (𝟙 _)
      ((Modules.pullbackUnitIso (pullback.fst π T.hom)).inv ≫ x.q)

/-- The canonical D2 evaluation morphism.  It first base-changes `π_* L`
from `S` to `T`, then pushes forward the twisted divisor quotient along
`X_T -> T`. -/
noncomputable def grassmannianEval (L : X.Modules) (x : DivFamily π T) :
    (Modules.pullback T.hom).obj ((Modules.pushforward π).obj L) ⟶
      (Modules.pushforward (pullback.snd π T.hom)).obj (x.twist L) :=
  pushforwardBaseChangeMap π T.hom (pullback.snd π T.hom)
      (pullback.fst π T.hom) pullback.condition L ≫
    (Modules.pushforward (pullback.snd π T.hom)).map (x.twistQuotientMap L)

/-- The evaluation map is epi as soon as its two displayed factors are epi. -/
theorem grassmannianEval_epi (L : X.Modules) (x : DivFamily π T)
    (hbase : Epi (pushforwardBaseChangeMap π T.hom
      (pullback.snd π T.hom) (pullback.fst π T.hom) pullback.condition L))
    (hquot : Epi ((Modules.pushforward (pullback.snd π T.hom)).map
      (x.twistQuotientMap L))) :
    Epi (x.grassmannianEval L) := by
  letI := hbase
  letI := hquot
  dsimp [grassmannianEval]
  infer_instance

/-- Package the D2 evaluation as a rank-`d` locally free quotient. -/
noncomputable def grassmannianQuotient (L : X.Modules) (x : DivFamily π T)
    [IsLocallyNoetherian S] {d : ℕ} (hEpi : Epi (x.grassmannianEval L))
    (hLocFree : SheafOfModules.IsLocallyFreeOfRank
      ((Modules.pushforward (pullback.snd π T.hom)).obj (x.twist L)) d) :
    LocallyFreeQuotient ((Modules.pushforward π).obj L) d T := by
  letI := hEpi
  exact {
    F := (Modules.pushforward (pullback.snd π T.hom)).obj (x.twist L)
    q := x.grassmannianEval L
    epi := inferInstance
    locFree := hLocFree }

/-- The quotient-class value of the D2 comparison in the relative
Grassmannian functor. -/
noncomputable def grassmannianClass (L : X.Modules) (x : DivFamily π T)
    [IsLocallyNoetherian S] {d : ℕ} (hEpi : Epi (x.grassmannianEval L))
    (hLocFree : SheafOfModules.IsLocallyFreeOfRank
      ((Modules.pushforward (pullback.snd π T.hom)).obj (x.twist L)) d) :
    (Grassmannian ((Modules.pushforward π).obj L) d).obj (Opposite.op T) :=
  Quotient.mk _ (grassmannianQuotient L x hEpi hLocFree)

/-- The componentwise form of `grassmannianClass`: once the base-change and
divisor-quotient factors are epi, only the target's rank condition remains. -/
noncomputable def grassmannianClassOfComponents (L : X.Modules) (x : DivFamily π T)
    [IsLocallyNoetherian S] {d : ℕ}
    (hbase : Epi (pushforwardBaseChangeMap π T.hom
      (pullback.snd π T.hom) (pullback.fst π T.hom) pullback.condition L))
    (hquot : Epi ((Modules.pushforward (pullback.snd π T.hom)).map
      (x.twistQuotientMap L)))
    (hLocFree : SheafOfModules.IsLocallyFreeOfRank
      ((Modules.pushforward (pullback.snd π T.hom)).obj (x.twist L)) d) :
    (Grassmannian ((Modules.pushforward π).obj L) d).obj (Opposite.op T) :=
  grassmannianClass L x (grassmannianEval_epi L x hbase hquot) hLocFree

end DivFamily

end Scheme

end AlgebraicGeometry
