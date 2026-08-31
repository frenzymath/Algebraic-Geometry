/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeSeedUnivFacts
import AlgebraicJacobian.Picard.SupportTubeFinite

/-!
# G-4 — the ambient colength finiteness `hcolFin` at `seedUniv` (I-0283 residual)

The capstone `ThetaGeneratorSeed.isGenerator_of_fibrewise_ker_span_of_field_vanishing`
(`Picard/DivSchemeSeedUnivClose.lean`) needs, at `seedUniv` (`R = R_Z`, `K = K_univ`), the
**ambient per-point colength finiteness**

```
hcolFin : ∀ z, Module.Finite R_Z (Γ(relCurve C R_Z, D.piece z) ⧸ Ideal.span {D.eqn z})
```

the third genuine geometry obligation of the seed close (alongside the sibling
`hspan`/`hfield`).

## The reduction to the closed-trace

The landed abstract engine `IsAffineOpen.finite_quotient_span_singleton_of_isClosed`
(`Picard/SupportTubeFinite.lean`) reduces per-point finiteness to the **closed-trace**

```
hclosed z : IsClosed ((D.piece z : Set) \ ((relCurve C R_Z).basicOpen (D.eqn z) : Set))
```

using the properness licence `instIsProperRelCurveHom` (which supplies the
`UniversallyClosed`/`LocallyOfFiniteType` structure-morphism instances).  This is the
**abstract** engine — it consumes no `DivisorAdaptation`, so the route is not circular
(`hcolFin` is an *input* to `IsGenerator`).

## The closed-trace from the fibre no-leak

`D.piece z \ D(D.eqn z)` is the trace, on the affine piece, of the vanishing locus of the
seed section `sec z` — a set that lies inside the closed set `(D(eqn z))ᶜ`, so its closure
is automatically inside `(D(eqn z))ᶜ`; it is closed in the whole relative curve exactly
when it does not **leak** out of the piece, i.e. when its closure stays inside the piece
(`isClosed_sdiff_basicOpen_of_closure_subset`).  Since the structure morphism is proper
the leak is controlled fibrewise (`isClosed_sdiff_basicOpen_of_forall_fibre`): over every
base point the fibre part of the closure must stay in the piece.  This is the topological
shadow of `d_p`'s finite fibre support combined with the seed's `h z` piece choice
(`D(h z)` contains the whole fibre branch of `d_p`, I-0280).

## Main declarations

* `AlgebraicGeometry.isClosed_sdiff_basicOpen_of_closure_subset` /
  `isClosed_sdiff_basicOpen_of_forall_fibre` — the closed-trace topology: `V \ D(g)` is
  closed once its closure stays in `V` (fibrewise sufficient);
* `AlgebraicGeometry.IsAffineOpen.finite_quotient_span_singleton_of_closure_subset` — the
  engine in closure-subset spelling;
* `seedUniv_hcolFin_of_forall_closure_subset` — `hcolFin` at `seedUniv` reduced to the
  pure topological no-leak on the seed pieces.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

/-! ## The closed-trace topology: no leak ⟹ closed -/

/-- **The closed-trace from an empty leak**: the trace `V \ D(g)` of the vanishing locus of
a section `g` on an open `V` is closed in the whole scheme as soon as its closure stays
inside `V`.  (The other inclusion, `closure (V \ D(g)) ⊆ (D(g))ᶜ`, is automatic since
`V \ D(g)` already lies in the closed set `(D(g))ᶜ`.) -/
theorem isClosed_sdiff_basicOpen_of_closure_subset {X : Scheme.{u}} {V : X.Opens}
    (g : Γ(X, V))
    (hcl : closure ((V : Set X) \ (X.basicOpen g : Set X)) ⊆ (V : Set X)) :
    IsClosed ((V : Set X) \ (X.basicOpen g : Set X)) := by
  apply isClosed_of_closure_subset
  intro x hx
  refine ⟨hcl hx, ?_⟩
  exact closure_minimal (fun _ h => h.2) (X.basicOpen g).isOpen.isClosed_compl hx

/-- **The closed-trace from a fibrewise no-leak**: if, over every base point `s`, the part
of the closure of the trace `V \ D(g)` lying over `s` stays inside `V`, then the trace is
closed.  The fibrewise hypothesis is the topological shadow of the finite fibre support of
the divisor cut by `g` (produced Zariski-locally on the base by the properness of the
structure morphism). -/
theorem isClosed_sdiff_basicOpen_of_forall_fibre {X S : Scheme.{u}} (φ : X ⟶ S)
    {V : X.Opens} (g : Γ(X, V))
    (hfib : ∀ s : S, φ.base ⁻¹' {s} ∩ closure ((V : Set X) \ (X.basicOpen g : Set X))
      ⊆ (V : Set X)) :
    IsClosed ((V : Set X) \ (X.basicOpen g : Set X)) :=
  isClosed_sdiff_basicOpen_of_closure_subset g (fun x hx => hfib (φ.base x) ⟨rfl, hx⟩)

/-! ## The abstract engine in closure-subset spelling -/

/-- **The abstract (c1)-finiteness engine, closure-subset spelling**: for an affine open
`V` of a scheme `X` over `Spec R` with universally-closed and locally-of-finite-type
structure morphism, if the closure of `V \ D(g)` stays inside `V`, then `Γ(X, V) ⧸ (g)` is
a finite `R`-module.  A thin closure-subset wrapper over
`IsAffineOpen.finite_quotient_span_singleton_of_isClosed`; consumes no `DivisorAdaptation`
(anti-circular). -/
theorem IsAffineOpen.finite_quotient_span_singleton_of_closure_subset
    {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    {R : Type u} [CommRing R] [X.Over (Spec (CommRingCat.of R))]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of R))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of R))]
    (g : Γ(X, V))
    (hcl : closure ((V : Set X) \ (X.basicOpen g : Set X)) ⊆ (V : Set X)) :
    Module.Finite R (Γ(X, V) ⧸ Ideal.span {g}) :=
  hV.finite_quotient_span_singleton_of_isClosed g
    (isClosed_sdiff_basicOpen_of_closure_subset g hcl)

/-! ## `hcolFin` for a theta generator seed, reduced to the fibre no-leak -/

section Seed

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}
variable {K : Submodule R (relThetaSections C R π a)}

namespace ThetaGeneratorSeed

variable (D : ThetaGeneratorSeed C R π a K)
variable [UniversallyClosed ((relCurve C R) ↘ Spec (CommRingCat.of R))]
variable [LocallyOfFiniteType ((relCurve C R) ↘ Spec (CommRingCat.of R))]

/-- **The ambient colength finiteness `hcolFin` from an empty leak** (the `hcolFin`
hypothesis of `isGenerator_of_fibrewise_ker_span_of_field_vanishing`, reduced to the
topological closed-trace): if on every piece the closure of the trace
`piece z \ D(eqn z)` of the vanishing locus of the seed equation stays inside the piece,
then each ambient colength `Γ(D(h z)) ⧸ (eqn z)` is a finite `R`-module.  Uses the abstract
engine directly (the piece is affine, the structure morphism is universally closed and
locally of finite type), so it consumes no `DivisorAdaptation` — the route stays
anti-circular. -/
theorem hcolFin_of_forall_closure_subset
    (hnoleak : ∀ z : relCurve C R,
      closure ((D.piece z : Set (relCurve C R)) \
          ((relCurve C R).basicOpen (D.eqn z) : Set (relCurve C R)))
        ⊆ (D.piece z : Set (relCurve C R))) :
    ∀ z : relCurve C R,
      Module.Finite R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}) :=
  fun z => (D.isAffineOpen_piece z).finite_quotient_span_singleton_of_closure_subset
    (D.eqn z) (hnoleak z)

/-- **The ambient colength finiteness `hcolFin` from a fibrewise no-leak**: the fibrewise
spelling of `hcolFin_of_forall_closure_subset`, in which the leak is controlled over each
base point separately — the topological shadow of the finite fibre support of the divisor
cut by `eqn z` (produced Zariski-locally on the base by the properness of the relative
curve).  This is the slot the seed design fills (`d_p`'s finite fibre branch inside the
piece `D(h z)`). -/
theorem hcolFin_of_forall_fibre
    (hfib : ∀ (z : relCurve C R) (s : Spec (CommRingCat.of R)),
      ((relCurve C R) ↘ Spec (CommRingCat.of R)).base ⁻¹' {s}
          ∩ closure ((D.piece z : Set (relCurve C R)) \
            ((relCurve C R).basicOpen (D.eqn z) : Set (relCurve C R)))
        ⊆ (D.piece z : Set (relCurve C R))) :
    ∀ z : relCurve C R,
      Module.Finite R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}) :=
  D.hcolFin_of_forall_closure_subset
    (fun z x hx => hfib z (((relCurve C R) ↘ Spec (CommRingCat.of R)).base x) ⟨rfl, hx⟩)

end ThetaGeneratorSeed

end Seed

/-! ## `hcolFin` at `seedUniv`, reduced to the topological fibre no-leak -/

section SeedUnivColFin

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftColFin : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(Scheme.divisorSections k ((windowS_choice π hπ g • fiberWeilDivisor π)
    + (windowM_choice π hπ g • fiberWeilDivisor π)) ⊤))
variable (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

set_option maxHeartbeats 2400000 in
-- the seed structure fields carry the huge `DivCarveChartRing`/window/`relThetaSections`
-- types; the colength quotient over the `κ(p)` tower re-elaborates them (recorded hatch)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
include hO hχ in
/-- **`hcolFin` at `seedUniv`, reduced to the topological fibre no-leak** (I-0283 residual):
the ambient colength `Γ(D(h z)) ⧸ (eqn z)` at `seedUniv` is a finite `R_Z`-module as soon
as, on every piece, the closure of the trace `piece z \ D(eqn z)` of the seed-equation
vanishing locus stays inside the piece.  This is exactly the `hcolFin` hypothesis of
`isGenerator_of_fibrewise_ker_span_of_field_vanishing` at `seedUniv`, with all the
instance plumbing discharged: the pieces are affine (`isAffineOpen_piece`) and the
structure morphism `relCurve C R_Z ↘ Spec R_Z` is universally closed and locally of finite
type (the properness licence `instIsProperRelCurveHom`).  Anti-circular: the abstract
engine consumes no `DivisorAdaptation`.  The single residual is the pure topological
no-leak `hnoleak`, the topological shadow of `d_p`'s finite fibre support combined with the
seed's `h z` piece choice (`D(h z)` contains the whole fibre branch, I-0280). -/
theorem seedUniv_hcolFin_of_forall_closure_subset
    (hnoleak : ∀ z : relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
      closure (((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).piece z :
            Set (relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))) \
          ((relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)).basicOpen
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).eqn z) :
            Set (relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))))
        ⊆ ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).piece z :
            Set (relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)))) :
    ∀ z : relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
      Module.Finite
        (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
        (Γ(relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
            (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).piece z)
          ⧸ Ideal.span {(seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).eqn z}) :=
  (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).hcolFin_of_forall_closure_subset hnoleak

end SeedUnivColFin

end AlgebraicGeometry
