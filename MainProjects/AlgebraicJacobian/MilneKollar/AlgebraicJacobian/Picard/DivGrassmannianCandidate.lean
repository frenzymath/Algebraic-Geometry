/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivGrassmannianClass
import AlgebraicJacobian.Picard.DivLocallyClosed

/-!
# The universal Grassmannian candidate for a divisor

This file connects the D2 divisor-to-Grassmannian class to the D3
curve-side candidate quotient.  It is kept downstream of both constructions
so changes to this bridge do not force the large D2 development to recompile.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

namespace Scheme

namespace DivFamily

variable {S X : Scheme.{u}} {π : X ⟶ S} {T : Over S}

/-- The reconstructed Grassmannian evaluation kills the relations of an
actual divisor family.  The proof is the adjunction transpose of
`kernel.ι (grassmannianEval L x) ≫ grassmannianEval L x = 0`; it uses no
additional hypothesis beyond the data already needed to form that quotient. -/
theorem grassmannianKernelEvaluation_comp_twistQuotientMap
    (L : X.Modules) (x : DivFamily π T) [IsLocallyNoetherian S] {d : ℕ}
    (hEpi : Epi (x.grassmannianEval L))
    (hLocFree : SheafOfModules.IsLocallyFreeOfRank
      ((Modules.pushforward (pullback.snd π T.hom)).obj (x.twist L)) d) :
    LocallyFreeQuotient.kernelEvaluation L
        (x.grassmannianQuotient L hEpi hLocFree) ≫
      x.twistQuotientMap L = 0 := by
  let q := x.grassmannianQuotient L hEpi hLocFree
  change LocallyFreeQuotient.kernelEvaluation L q ≫
    x.twistQuotientMap L = 0
  apply ((Modules.pullbackPushforwardAdjunction
    (pullback.snd π T.hom)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [LocallyFreeQuotient.kernelEvaluation, Equiv.apply_symm_apply]
  change (kernel.ι q.q ≫
      pushforwardBaseChangeMap π T.hom (pullback.snd π T.hom)
        (pullback.fst π T.hom) pullback.condition L) ≫
      (Modules.pushforward (pullback.snd π T.hom)).map
        (x.twistQuotientMap L) = _
  rw [Category.assoc]
  change kernel.ι q.q ≫ q.q = _
  rw [kernel.condition, Adjunction.homAddEquiv_zero]
  rfl

/-- The canonical comparison from the Grassmannian candidate cokernel to the
twisted sheaf of an actual divisor family. -/
noncomputable def grassmannianCandidateToTwist
    (L : X.Modules) (x : DivFamily π T) [IsLocallyNoetherian S] {d : ℕ}
    (hEpi : Epi (x.grassmannianEval L))
    (hLocFree : SheafOfModules.IsLocallyFreeOfRank
      ((Modules.pushforward (pullback.snd π T.hom)).obj (x.twist L)) d) :
    cokernel (LocallyFreeQuotient.kernelEvaluation L
      (x.grassmannianQuotient L hEpi hLocFree)) ⟶ x.twist L :=
  cokernel.desc _ (x.twistQuotientMap L)
    (grassmannianKernelEvaluation_comp_twistQuotientMap
      L x hEpi hLocFree)

/-- The candidate quotient followed by its comparison is the original
twisted divisor quotient. -/
theorem grassmannianCandidateQuotient_comp_candidateToTwist
    (L : X.Modules) (x : DivFamily π T) [IsLocallyNoetherian S] {d : ℕ}
    (hEpi : Epi (x.grassmannianEval L))
    (hLocFree : SheafOfModules.IsLocallyFreeOfRank
      ((Modules.pushforward (pullback.snd π T.hom)).obj (x.twist L)) d) :
    LocallyFreeQuotient.candidateQuotient L
        (x.grassmannianQuotient L hEpi hLocFree) ≫
      grassmannianCandidateToTwist L x hEpi hLocFree =
        x.twistQuotientMap L :=
  cokernel.π_desc _ _ _

end DivFamily

namespace Grassmannian

variable {S X : Scheme.{0}} {π : X ⟶ S} [IsLocallyNoetherian S]

/-- The curve-side evaluation map attached to the universal quotient on the
chosen scheme representing `Grassmannian (π_* L) d`. -/
noncomputable def universalKernelEvaluation (L : X.Modules) {r d : ℕ}
    (hV : SheafOfModules.IsLocallyFreeOfRank
      ((Modules.pushforward π).obj L) r)
    (hd : 1 ≤ d) (hdr : d ≤ r) :=
  LocallyFreeQuotient.kernelEvaluation L
    (universalQuotient hV hd hdr)

/-- The universal candidate quotient on
`X ×_S representingScheme (Grassmannian (π_*L) d)`. -/
noncomputable def universalCandidateQuotient (L : X.Modules) {r d : ℕ}
    (hV : SheafOfModules.IsLocallyFreeOfRank
      ((Modules.pushforward π).obj L) r)
    (hd : 1 ≤ d) (hdr : d ≤ r) :=
  LocallyFreeQuotient.candidateQuotient L
    (universalQuotient hV hd hdr)

/-- The kernel of the universal candidate quotient.  This is the actual
curve-side module whose invertible locus D3 must carve out; the kernel of the
Grassmannian quotient itself lives on the base and has the wrong rank.  Its
ordinary `lineBundleLocus` lies in the total space `X_G`; D3 must still descend
the whole-fibre condition to a locus in the Grassmannian base `G`. -/
noncomputable def universalCandidateIdeal (L : X.Modules) {r d : ℕ}
    (hV : SheafOfModules.IsLocallyFreeOfRank
      ((Modules.pushforward π).obj L) r)
    (hd : 1 ≤ d) (hdr : d ≤ r) :=
  LocallyFreeQuotient.candidateIdeal L
    (universalQuotient hV hd hdr)

/-- The universal candidate quotient is epimorphic by its cokernel
construction. -/
theorem universalCandidateQuotient_epi (L : X.Modules) {r d : ℕ}
    (hV : SheafOfModules.IsLocallyFreeOfRank
      ((Modules.pushforward π).obj L) r)
    (hd : 1 ≤ d) (hdr : d ≤ r) :
    Epi (universalCandidateQuotient L hV hd hdr) :=
  LocallyFreeQuotient.candidateQuotient_epi L
    (universalQuotient hV hd hdr)

end Grassmannian

end Scheme

end AlgebraicGeometry
