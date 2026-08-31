/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.AbelianVariety.GroupSeparated

/-!
# The Abel-source interface: properness and irreducibility of the Jacobian
(Wave-5 D3, routes P-B / GI-(a))

`AbelSourceData d` packages a proper, geometrically irreducible source scheme `D` over
`k` together with an *Abel morphism* `abel : D ⟶ d.J` into the representing object of
the Jacobian datum whose underlying scheme map is surjective.  Two of the three frozen
Wave-5 targets are theorems **conditional on this interface** (w5-worksheet §1 D3):

* `universallyClosed_of_abelSource` (**P2**): `UniversallyClosed d.J.hom` — `d.J` is
  the image of the proper source: `abel.left ≫ d.J.hom = D.hom` (`Over.w`) is
  universally closed and `abel.left` is surjective, so mathlib's
  `UniversallyClosed.of_comp_surjective` applies.
* `isProper_of_abelSource` (**P3**): `IsProper d.J.hom` — assembly of X1
  separatedness (`JacobianData.isSeparated`), P2, and the datum's
  `locallyOfFiniteType` certificate (quasi-compactness is implied, `UC → QC`).
* `geometricallyIrreducible_of_abelSource` (**G1**, route GI-(a)): for every field
  `K/k` the base change `D_K` is irreducible (the certificate), the base-changed Abel
  morphism `D_K ⟶ J_K` is surjective (`Surjective` is stable under base change), and
  a continuous surjective image of an irreducible space is irreducible
  (`Function.Surjective.irreducibleSpace`) — so `J_K` is irreducible, uniformly in
  `K`, which is exactly the `geometrically` quantifier.

## Design decisions recorded (the interface spelling)

* **Geometric-irreducibility certificate.**  `GeometricallyIrreducible D.hom` alone:
  G1 consumes exactly per-`K` irreducibility of `D_K`, and neither P2 nor P3 consumes
  reducedness — so no `GeometricallyReduced`/`GeometricallyIntegral` field is carried.
  (The eventual producer has integrality available anyway and mathlib's
  `GeometricallyIntegral → GeometricallyIrreducible` instance bridges,
  `Geometrically/Integral.lean`.)
* **Surjectivity certificate.**  The single field `Surjective abel.left` (mathlib's
  topological surjectivity class) suffices for BOTH consumers.  Probe result: the
  pinned mathlib has `MorphismProperty.IsStableUnderBaseChange @Surjective`
  (`AlgebraicGeometry/PullbackCarrier.lean:431`), so surjectivity base-changes to
  every field `K/k` — no `∀ K`-quantified field is needed.
* **Topology bridge.**  The "continuous surjective image of an irreducible space is
  irreducible" brick anticipated by the recon (§3.3) already exists in the pinned
  mathlib: `Function.Surjective.irreducibleSpace` (`Topology/Irreducible.lean:540`).
  No project-side topology infrastructure is required.

## The P1 discharge route (recorded for the GATED producer; do NOT build here)

No instance of `AbelSourceData` is constructed in this file — the producer (brick P1)
is gated on the DD lanes' shapes freezing (w5-worksheet §1 D3).  Its recorded route:

* `D` := the proper degree-`n` divisor scheme (`Div^n`, `n ≥ genus C`) from the
  DD-Q/DD-R quasi-projectivity campaign; `isProper` from that construction;
  `geometricallyIrreducible` from geometric integrality of `C^n_K` (iterated
  `isIntegral_tensorObj_left`, `AbelianVariety/Rigidity.lean:160`, over the landed
  `Curve/BaseChangeInstances.lean` stack) pushed to `Div^n` along the quotient/chart
  presentation.
* `abel` := `d.rep.homEquiv.symm` (through `JacobianData.homEquiv`) of the universal
  degree-`n` divisor-family class shifted into `pic0Subgroup` by the `fiberTwist`
  degree shifter (`RiemannRoch/FiberTwist.lean:301`, `classDeg_fiberTwist :393` — no
  rational point needed).
* `surjective` := field-point coverage from `riemann_inequality_curve`
  (`RiemannRoch/ChiCurve.lean:183`): for every point of `d.J.left`, its residue-field
  point is a degree-0 class `λ` on `C_K`; the `fiberTwist` shift makes it degree
  `n ≥ genus C`, so `h⁰ ≥ deg + 1 - genus C ≥ 1` produces an effective representative,
  i.e. a `Div^n`-point over (an extension of) `K` hitting the given point — hence
  `Function.Surjective abel.left` on topological points.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- **The Abel-source interface** (Wave-5 D3, one substrate for routes P-B and
GI-(a)): a proper, geometrically irreducible scheme over `k` mapping onto the
representing object of the Jacobian datum `d`.  Produced once by the gated brick P1
(proper `Div^n` + Abel morphism via `d.rep.homEquiv.symm` + `fiberTwist` shift +
`riemann_inequality_curve` coverage — see the file docstring); consumed by the
conditional theorems P2/P3/G1 below.  NEVER a sorried instance. -/
structure AbelSourceData (d : JacobianData C) : Type (u + 1) where
  /-- The source scheme over `k` (the proper divisor scheme `Div^n`-to-be). -/
  D : Over (Spec (.of k))
  /-- Properness certificate for the source (from the `Div^n` construction). -/
  isProper : IsProper D.hom
  /-- Geometric-irreducibility certificate for the source: `D_K` is irreducible for
  every field `K/k`.  This is all G1 consumes; the producer may derive it from
  geometric integrality via mathlib's bridge instance. -/
  geometricallyIrreducible : GeometricallyIrreducible D.hom
  /-- The Abel morphism, over `Spec k`. -/
  abel : D ⟶ d.J
  /-- Surjectivity certificate on underlying schemes.  Mathlib's `Surjective` class
  is stable under base change, so this single field base-changes to every field
  `K/k` (no `∀ K` quantifier needed). -/
  surjective : Surjective abel.left

variable {d : JacobianData C}

/-- **P2 (Wave-5 target 2, universal closedness; route P-B)**: the structure morphism
of the representing object of a Jacobian datum is universally closed, given any Abel
source.  Milne's completeness step: `abel.left ≫ d.J.hom = a.D.hom` (`Over.w`) is
universally closed since `a.D` is proper, and `abel.left` is surjective, so
`UniversallyClosed.of_comp_surjective` applies. -/
theorem universallyClosed_of_abelSource (a : AbelSourceData d) :
    UniversallyClosed d.J.hom := by
  haveI : UniversallyClosed (a.abel.left ≫ d.J.hom) := by
    rw [Over.w a.abel]
    exact a.isProper.toUniversallyClosed
  haveI : Surjective a.abel.left := a.surjective
  exact UniversallyClosed.of_comp_surjective a.abel.left d.J.hom

/-- **P3 (Wave-5 target 2, properness assembly)**: the representing object of a
Jacobian datum is proper over `k`, given any Abel source.  Assembly of the three
`IsProper` constituents: separatedness is X1 (`JacobianData.isSeparated`, group-
theoretic), universal closedness is P2, local finite-typeness is the datum's
construction certificate; quasi-compactness is implied (`UC → QC`). -/
theorem isProper_of_abelSource (a : AbelSourceData d) : IsProper d.J.hom :=
  haveI : IsSeparated d.J.hom := d.isSeparated
  haveI : UniversallyClosed d.J.hom := universallyClosed_of_abelSource a
  haveI : LocallyOfFiniteType d.J.hom := d.locallyOfFiniteType
  ⟨⟩

/-- **G1 (Wave-5 target 3, geometric irreducibility; route GI-(a))**: the structure
morphism of the representing object of a Jacobian datum is geometrically irreducible,
given any Abel source.  For each field `K/k` and each pullback `Z` of `d.J.hom` along
`y : Spec K ⟶ Spec k`: the base-changed source `D_K` is irreducible (the
certificate), the comparison morphism `D_K ⟶ Z` induced by `abel` is the base change
of `abel.left` along `Z ⟶ d.J.left` (pullback pasting), hence surjective, and the
continuous surjective image of an irreducible space is irreducible. -/
theorem geometricallyIrreducible_of_abelSource (a : AbelSourceData d) :
    GeometricallyIrreducible d.J.hom := by
  constructor
  intro K _ y Z fst snd h
  -- the base-changed source `D_K` is irreducible
  haveI : IrreducibleSpace ↥(pullback a.D.hom y) :=
    a.geometricallyIrreducible.geometrically_irreducibleSpace y
      (pullback.fst a.D.hom y) (pullback.snd a.D.hom y)
      (IsPullback.of_hasPullback a.D.hom y)
  -- `D_K` is also the pullback of the composite `abel.left ≫ d.J.hom` along `y`
  have s : IsPullback (pullback.fst a.D.hom y) (pullback.snd a.D.hom y)
      (a.abel.left ≫ d.J.hom) y := by
    rw [Over.w a.abel]
    exact IsPullback.of_hasPullback a.D.hom y
  -- pasting: the induced comparison `D_K ⟶ Z` is the base change of `abel.left`
  -- along `fst : Z ⟶ d.J.left`, hence surjective
  have hsurj := MorphismProperty.of_isPullback (P := @Surjective)
    (IsPullback.of_bot' s h) a.surjective
  exact Function.Surjective.irreducibleSpace (Scheme.Hom.continuous _) hsurj.surj

end AlgebraicGeometry
