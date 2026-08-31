/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.SupportTube
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The support-tube finiteness engine: the (c1)-finite production brick (G-4)

The algebraic half of the DDR-4 certificate clause (c1) (`informal/w4-g4-worksheet.md`
§3, the one row with no landed engine): for a divisor adaptation over a test ring `R`,
the chart-local colength `Γ(D(h_j)) ⧸ (f_j)` is a **finite** `R`-module — Kleiman's
finiteness-of-the-divisor-subscheme step, per piece.

## The honest hypothesis (probe finding)

The colength is the section ring of the piece trace of the family support
(`supportLocus_inter_pieces`): the closed subscheme of the affine piece `D(h_j)` cut by
`f_j`, whose underlying set is `D(h_j) \ D(f_j) = supportLocus ∩ D(h_j)`.  The engine
input is that this trace is **closed in the whole relative curve**; universal closedness
of the curve over the base (the landed licence `instIsProperRelCurveHom`) then makes the
trace universally closed over `Spec R`, and a universally closed affine morphism of
finite type is finite (`IsIntegralHom.iff_universallyClosed_and_isAffineHom` +
`IsFinite.iff_isIntegralHom_and_locallyOfFiniteType` — the mathlib heart, the
`SlicingFlatKernel` luck again).  No Noetherian hypothesis anywhere.

Fibrewise finiteness data alone (each fibre colength artinian, even of constant total
dimension) canNOT replace the closed-trace input.  Guard examples:

* `Γ(𝔸¹) = k[x]` over `k` with `f = 0`: excluded by `[UniversallyClosed]` on the
  structure morphism (the affine line is not proper).
* the hyperbola `k[t,x]⧸(tx−1)` over `k[t]` inside `X = ℙ¹_{k[t]}`, piece the affine
  chart: every fibre colength is artinian, the module is even flat, yet not finite —
  the closure of the trace leaks into `(∞, t=0)`, so the closed-trace hypothesis fails
  exactly where it must.
* two disjoint base sections with a piece missing one point of one section: piece
  colength `k[t] × k[t,t⁻¹]`, all fibre colengths artinian of constant total dimension
  `2` on the glued module — the PER-PIECE trace leaks.  Hence the certificate's
  per-piece clause genuinely constrains the adaptation, and the fibrewise input of
  P-fib-N enters this brick only through its topological shadow, the **no-leak fibre
  criterion** threaded below (`hfib` of
  `finite_colength_of_forall_fibre_closure_subset`).

## Main declarations

* `Scheme.LocalEquations.supportLeak` — the leak locus of a support trace out of an
  open `U`: `closure (supportLocus ∩ U) \ U`, closed
  (`isClosed_supportLeak`), with `isClosed_supportLocus_inter_iff_supportLeak_eq_empty`
  and the fibre criterion `supportLeak_eq_empty_of_forall_fibre`;
* `Scheme.LocalEquations.isClosed_image_supportLeak` — the tube-side product: the base
  image of the leak locus is closed under a universally closed structure morphism, so
  its complement is the Zariski-open base locus where the trace is closed;
* `AlgebraicGeometry.IsAffineOpen.finite_quotient_span_singleton_of_isClosed` — **the
  abstract engine**: `V` affine open in `X` over `Spec R`, structure morphism
  universally closed and locally of finite type, `V \ D(g)` closed in `X` ⟹
  `Γ(X, V) ⧸ (g)` is a finite `R`-module (via the closed immersion
  `Spec (Γ(X, V) ⧸ (g)) ⟶ X` and mathlib's integral = universally closed + affine);
* `DivisorAdaptation.finite_colength_of_isClosed_supportLocus_inter` /
  `finite_colength_of_supportLeak_eq_empty` /
  `finite_colength_of_forall_fibre_closure_subset` /
  `finite_colength_of_supportLocus_subset` — **the (c1)-finite clause** for the piece
  `j`, in the closed-trace, leak-locus, fibrewise no-leak, and dominant-piece
  spellings.  CertUniv consumes the fibrewise form with `hfib` produced from the seed
  design + P-fib-N fibre data, or the closed-trace form directly.

The `R`-algebra structure on section rings is `Scheme.overSectionsAlgebra` through the
`Over` structure (LOCAL instances, house rule) — consumers must activate the same
instances.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## The leak locus of a support trace -/

namespace Scheme.LocalEquations

variable {X S : Scheme.{u}} (d : X.LocalEquations)

/-- **The leak locus of a support trace**: the part of the closure of
`supportLocus ∩ U` that escapes `U`.  The trace `supportLocus ∩ U` is closed in `X`
iff the leak locus is empty (`isClosed_supportLocus_inter_iff_supportLeak_eq_empty`);
its base image under a universally closed structure morphism is closed
(`isClosed_image_supportLeak`), so the trace is closed over the complementary base
open — the Zariski-local piece-isolation mechanism of the DDR-4 finiteness input. -/
def supportLeak (U : X.Opens) : Set X :=
  closure (d.supportLocus ∩ (U : Set X)) \ (U : Set X)

lemma isClosed_supportLeak (U : X.Opens) : IsClosed (d.supportLeak U) :=
  isClosed_closure.sdiff U.isOpen

/-- The leak locus lies in the support outside the open: leaks are support points. -/
lemma supportLeak_subset_sdiff (U : X.Opens) :
    d.supportLeak U ⊆ d.supportLocus \ (U : Set X) := fun _ hx =>
  ⟨closure_minimal Set.inter_subset_left d.isClosed_supportLocus hx.1, hx.2⟩

/-- The support trace on an open is closed in the whole space iff nothing leaks. -/
lemma isClosed_supportLocus_inter_iff_supportLeak_eq_empty (U : X.Opens) :
    IsClosed (d.supportLocus ∩ (U : Set X)) ↔ d.supportLeak U = ∅ := by
  constructor
  · intro h
    rw [supportLeak, h.closure_eq, Set.sdiff_eq_empty]
    exact Set.inter_subset_right
  · intro h
    rw [supportLeak, Set.sdiff_eq_empty] at h
    exact isClosed_of_closure_subset fun x hx =>
      ⟨closure_minimal Set.inter_subset_left d.isClosed_supportLocus hx, h hx⟩

/-- **The fibre no-leak criterion** — the named threading slot for the fibrewise data
of the (c1)-finite clause: if over every base point the fibre of the closure of the
trace stays inside `U`, the leak locus is empty.  In the CertUniv instantiation the
hypothesis is produced from the seed design and the P-fib-N fibre analysis (the fibre
support is a finite set of pairwise-incomparable closed points, each isolated inside
its piece). -/
lemma supportLeak_eq_empty_of_forall_fibre (f : X ⟶ S) {U : X.Opens}
    (hfib : ∀ s : S, f.base ⁻¹' {s} ∩ closure (d.supportLocus ∩ (U : Set X))
      ⊆ (U : Set X)) :
    d.supportLeak U = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hxc, hxU⟩
  exact hxU (hfib (f.base x) ⟨rfl, hxc⟩)

/-- **The base image of the leak locus is closed** under a universally closed morphism
(the properness licence): its complement is the Zariski-open locus of the base over
which the support trace on `U` is closed — the tube-side mechanism for producing the
closed-trace input Zariski-locally on the base. -/
theorem isClosed_image_supportLeak (f : X ⟶ S) [UniversallyClosed f] (U : X.Opens) :
    IsClosed (f.base '' d.supportLeak U) :=
  f.isClosedMap _ (d.isClosed_supportLeak U)

end Scheme.LocalEquations

/-! ## The abstract finiteness engine -/

namespace IsAffineOpen

variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)

/-- The underlying set of the closed subscheme of an affine open cut by an ideal of its
section ring, embedded in the ambient scheme: `Spec (Γ(X, V) ⧸ I) ⟶ Spec Γ(X, V) ⟶ X`
has range the vanishing set of `I` on `V`. -/
lemma range_specMap_quotient_mk_fromSpec (I : Ideal Γ(X, V)) :
    Set.range ⇑(Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec)
      = X.zeroLocus (I : Set Γ(X, V)) ∩ (V : Set X) := by
  have hcomp : ⇑(Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec)
      = ⇑hV.fromSpec ∘ ⇑(Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
    ext x
    exact Scheme.Hom.comp_apply _ _ x
  have hq : Set.range ⇑(Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      = PrimeSpectrum.zeroLocus (I : Set Γ(X, V)) := by
    have h := range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := I))
    rw [Ideal.mk_ker] at h
    exact h
  rw [hcomp, Set.range_comp, hq]
  exact hV.fromSpec_image_zeroLocus _

variable {R : Type u} [CommRing R] [X.Over (Spec (CommRingCat.of R))]

/-- **The structure triangle of the chart-local closed subscheme**: composing
`Spec (Γ(X, V) ⧸ I) ⟶ X` with the structure morphism is `Spec` of the structure map
`R → Γ(X, V) ⧸ I` (the `Scheme.overSectionsAlgebra` algebra, quotient structure). -/
lemma specMap_quotient_mk_fromSpec_over (I : Ideal Γ(X, V)) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec
        ≫ (X ↘ Spec (CommRingCat.of R))
      = Spec.map (CommRingCat.ofHom (algebraMap R (Γ(X, V) ⧸ I))) := by
  have h1 : hV.fromSpec ≫ (X ↘ Spec (CommRingCat.of R))
      = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv
          ≫ (X ↘ Spec (CommRingCat.of R)).appLE ⊤ V le_top) := by
    have h2 := (SpecMap_appLE_fromSpec (X ↘ Spec (CommRingCat.of R))
      (isAffineOpen_top (Spec (CommRingCat.of R))) hV le_top).symm
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h2
    exact h2
  have halg : CommRingCat.ofHom (algebraMap R (Γ(X, V) ⧸ I))
      = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv
          ≫ (X ↘ Spec (CommRingCat.of R)).appLE ⊤ V le_top)
        ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    have happ : X.overAlgebraMap R V
        = ((X ↘ Spec (CommRingCat.of R)).appLE ⊤ V le_top).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
      rw [Scheme.overAlgebraMap, CommRingCat.hom_comp]
      rfl
    have hmk : algebraMap R (Γ(X, V) ⧸ I)
        = (Ideal.Quotient.mk I).comp (X.overAlgebraMap R V) := by
      rw [← Scheme.algebraMap_overSectionsAlgebra, Ideal.Quotient.mk_comp_algebraMap]
    ext r
    simp only [CommRingCat.hom_ofHom, hmk, happ, RingHom.comp_apply,
      CommRingCat.hom_comp]
  rw [h1, ← Spec.map_comp, halg]

include hV in
/-- **Ideal-valued support finiteness.**  If the closed subscheme cut out by an
arbitrary ideal `I` on an affine open `V` has closed image in the proper ambient
scheme, then its coordinate ring is finite over the base.  This is the
non-principal form needed for chart-reading ideals; the proof is the same
universally-closed affine-morphism argument as the principal engine below. -/
theorem finite_quotient_of_isClosed
    [UniversallyClosed (X ↘ Spec (CommRingCat.of R))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of R))]
    (I : Ideal Γ(X, V))
    (hclosed : IsClosed (X.zeroLocus (I : Set Γ(X, V)) ∩ (V : Set X))) :
    Module.Finite R (Γ(X, V) ⧸ I) := by
  haveI hci : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec) :=
    IsClosedImmersion.of_isPreimmersion _
      ((hV.range_specMap_quotient_mk_fromSpec I) ▸ hclosed)
  have hfin : IsFinite ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
      hV.fromSpec) ≫ (X ↘ Spec (CommRingCat.of R))) := by
    rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType,
      IsIntegralHom.iff_universallyClosed_and_isAffineHom]
    exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  rw [Category.assoc, hV.specMap_quotient_mk_fromSpec_over] at hfin
  exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hfin)

include hV in
/-- **The abstract (c1)-finiteness engine** (Kleiman's finiteness of the divisor
subscheme, chart-local form): for an affine open `V` of a scheme `X` over `Spec R`
whose structure morphism is universally closed and locally of finite type, and a
section `g` whose non-vanishing complement `V \ D(g)` is CLOSED in `X`, the quotient
`Γ(X, V) ⧸ (g)` is a finite `R`-module.

Route: `Spec (Γ(X, V) ⧸ (g)) ⟶ X` is a preimmersion with closed range, hence a closed
immersion; composing with the structure morphism is universally closed, affine (a
morphism of affine schemes) and locally of finite type, hence integral
(`IsIntegralHom.iff_universallyClosed_and_isAffineHom`) and finite
(`IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`); the composite IS `Spec` of the
structure map (`specMap_quotient_mk_fromSpec_over`), so `IsFinite.SpecMap_iff` reads
off `RingHom.Finite`.  No Noetherian hypothesis.  The universal-closedness input
excludes the affine-line guard example; the closedness input excludes the hyperbola
and leaking-piece guards (file header). -/
theorem finite_quotient_span_singleton_of_isClosed
    [UniversallyClosed (X ↘ Spec (CommRingCat.of R))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of R))]
    (g : Γ(X, V))
    (hclosed : IsClosed ((V : Set X) \ (X.basicOpen g : Set X))) :
    Module.Finite R (Γ(X, V) ⧸ Ideal.span {g}) := by
  have hrange : Set.range ⇑(Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {g}))) ≫ hV.fromSpec)
      = (V : Set X) \ (X.basicOpen g : Set X) := by
    rw [hV.range_specMap_quotient_mk_fromSpec, Scheme.zeroLocus_span]
    ext x
    simp only [Set.mem_inter_iff, Scheme.mem_zeroLocus_iff, Set.mem_singleton_iff,
      forall_eq, Set.mem_sdiff, SetLike.mem_coe]
    exact and_comm
  haveI hci : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {g})))
        ≫ hV.fromSpec) :=
    IsClosedImmersion.of_isPreimmersion _ (hrange ▸ hclosed)
  have hfin : IsFinite ((Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {g}))) ≫ hV.fromSpec)
        ≫ (X ↘ Spec (CommRingCat.of R))) := by
    rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType,
      IsIntegralHom.iff_universallyClosed_and_isAffineHom]
    exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  rw [Category.assoc, hV.specMap_quotient_mk_fromSpec_over] at hfin
  exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hfin)

end IsAffineOpen

/-! ## The adaptation corollaries: the (c1)-finite clause per piece -/

section Adaptation

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k}

namespace DivisorAdaptation

variable [IsFinite π] {d : (relCurve C R).LocalEquations}
variable (A : DivisorAdaptation C R π d)

/-- **The (c1)-finite clause from a closed support trace** (the core adaptation
corollary): if the piece trace of the family support is closed in the relative curve,
the chart-local colength `Γ(D(h_j)) ⧸ (f_j)` is a finite `R`-module — the
`IsCertified.finite_colength` clause at `j`, and the `[Module.Finite]` input of the
landed `projective_colength_of_forall_tmul_residueField`.  Consumes the properness
licence (`instIsProperRelCurveHom`); no Noetherian hypothesis. -/
theorem finite_colength_of_isClosed_supportLocus_inter (j : A.index)
    (hclosed : IsClosed (d.supportLocus ∩ (A.pieces j : Set (relCurve C R)))) :
    Module.Finite R (A.colength j) := by
  rw [A.supportLocus_inter_pieces j] at hclosed
  exact (A.toFinCoverData.isAffineOpen_pieces j).finite_quotient_span_singleton_of_isClosed
    (A.eqn j) hclosed

/-- The (c1)-finite clause in the leak-locus spelling: nothing leaks out of the piece
`j`, so the trace is closed and the colength is finite. -/
theorem finite_colength_of_supportLeak_eq_empty (j : A.index)
    (hleak : d.supportLeak (A.pieces j) = ∅) :
    Module.Finite R (A.colength j) :=
  A.finite_colength_of_isClosed_supportLocus_inter j
    ((d.isClosed_supportLocus_inter_iff_supportLeak_eq_empty (A.pieces j)).mpr hleak)

/-- **The (c1)-finite clause from fibrewise no-leak data** (the CertUniv threading
slot): if over every base point the fibre of the closure of the piece trace stays in
the piece — the topological shadow of the P-fib-N fibrewise finiteness data combined
with the seed design — then the colength of the piece `j` is a finite `R`-module. -/
theorem finite_colength_of_forall_fibre_closure_subset (j : A.index)
    (hfib : ∀ s : Spec (CommRingCat.of R),
      ((relCurve C R) ↘ Spec (CommRingCat.of R)).base ⁻¹' {s}
          ∩ closure (d.supportLocus ∩ (A.pieces j : Set (relCurve C R)))
        ⊆ (A.pieces j : Set (relCurve C R))) :
    Module.Finite R (A.colength j) :=
  A.finite_colength_of_supportLeak_eq_empty j
    (d.supportLeak_eq_empty_of_forall_fibre
      ((relCurve C R) ↘ Spec (CommRingCat.of R)) hfib)

/-- The (c1)-finite clause when the piece dominates the support: if the whole family
support lies in the piece `j` (the shape the support tube produces after shrinking the
base), the colength is finite.  The fibrewise form `∀ s, fibre ∩ supportLocus ⊆ piece`
reduces to this hypothesis by `fun x hx => hfib _ ⟨rfl, hx⟩`. -/
theorem finite_colength_of_supportLocus_subset (j : A.index)
    (hsub : d.supportLocus ⊆ (A.pieces j : Set (relCurve C R))) :
    Module.Finite R (A.colength j) :=
  A.finite_colength_of_isClosed_supportLocus_inter j (by
    rw [Set.inter_eq_left.mpr hsub]
    exact d.isClosed_supportLocus)

end DivisorAdaptation

end Adaptation

end AlgebraicGeometry
