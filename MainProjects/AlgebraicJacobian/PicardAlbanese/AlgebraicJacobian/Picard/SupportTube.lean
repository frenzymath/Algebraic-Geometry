/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyPullbackMap
import AlgebraicJacobian.Picard.DivSchemeFamilySide
import AlgebraicJacobian.Picard.SlicingFlat
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The support tube: the family support is closed over the base (DDR-4 finiteness input)

The geometric half of the DDR-4 certificate clause (c1) (`informal/spec-dd-r.md` §3
item 4): for a local-equation system `d` on a scheme `X`, the **support locus** — the
set of points where the (well-defined, by the ratio law) germ of the local equation is
not a unit — is closed in `X`; over a base `S` with `X → S` universally closed (the
standing `IsProper C.hom`, base-changed to the relative curve over every test ring),
its image in `S` is closed, and the **tube lemma** holds: if the support fibre over a
base point `s` is contained in an open `U` (e.g. a union of adaptation pieces), then so
is the whole support over a Zariski neighbourhood of `s` — piece isolation Zariski-locally
on the base.

## Main declarations

* `IsClosedMap.exists_isOpen_preimage_inter_subset` — the topological tube core: a
  closed map, a closed set `T`, an open `U` containing the `T`-fibre over `y` ⟹ an open
  neighbourhood `V ∋ y` with `f⁻¹(V) ∩ T ⊆ U` (via `Set.kernImage`);
* `Scheme.LocalEquations.unitLocus` / `supportLocus` — the (open) locus where the
  equations are germwise units, and its closed complement;
* `Scheme.LocalEquations.mem_unitLocus_iff_isUnit_germ` — membership reads on ANY
  covering member through the ratio law;
* `Scheme.LocalEquations.supportLocus_inter_opens` — the per-member trace
  `supp ∩ U_x = U_x \ D(eqn x)`;
* `Scheme.LocalEquations.isClosed_image_supportLocus`,
  `Scheme.LocalEquations.exists_supportTube` — closed image and the tube, for any
  `f : X ⟶ S` with `[UniversallyClosed f]`;
* `AlgebraicGeometry.instIsProperRelSndLeft`, `instIsProperRelCurveHom` — **the
  licence**: `IsProper C.hom` base-changes to the relative curve over an arbitrary test
  ring `R` (the field-keyed instances of `Curve/BaseChangeInstances` generalised), so
  `UniversallyClosed (relCurve C R ↘ Spec R)` fires by resolution;
* `DivisorAdaptation.mem_basicOpen_eqn_of_mem_unitLocus` / `unitLocus_eq` /
  `supportLocus_inter_pieces` — the adaptation reads the SAME support: on a piece,
  `d`'s support trace is `D(h_j) \ D(f_j)` (through `eqn_rel`, both ways);
* `FinCoverData.flat_sections_pieces` — the pieces' section rings are `R`-flat;
* `DivisorAdaptation.flat_colength_of_forall_tmul_residueField` /
  `projective_colength_of_forall_tmul_residueField` — **the (c1) junction**: a
  fibrewise-regular adaptation equation has flat colength over the Noetherian test
  ring (the `SlicingFlat` keystone on the piece ring), and a finite colength (the
  support-tube finiteness input) is then projective — the two clauses of
  `IsCertified` (c1) for the piece `j`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite
open scoped TensorProduct

/-! ## The topological tube core -/

section TubeCore

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The closed-map tube lemma**: for a closed map `f`, a closed `T ⊆ X` and an open
`U ⊆ X`, if the `T`-fibre over `y` is contained in `U` then so is `f⁻¹(V) ∩ T` for some
open neighbourhood `V` of `y`. Take `V := Set.kernImage f (U ∪ Tᶜ)`, open by
`isClosedMap_iff_kernImage`. -/
theorem IsClosedMap.exists_isOpen_preimage_inter_subset {f : X → Y}
    (hf : IsClosedMap f) {T U : Set X} (hT : IsClosed T) (hU : IsOpen U) {y : Y}
    (hfib : f ⁻¹' {y} ∩ T ⊆ U) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ f ⁻¹' V ∩ T ⊆ U := by
  refine ⟨Set.kernImage f (U ∪ Tᶜ),
    isClosedMap_iff_kernImage.mp hf (hU.union hT.isOpen_compl), ?_, ?_⟩
  · intro x hx
    by_cases hxT : x ∈ T
    · exact Or.inl (hfib ⟨hx, hxT⟩)
    · exact Or.inr hxT
  · rintro x ⟨hxV, hxT⟩
    rcases hxV (rfl : f x = f x) with h | h
    · exact h
    · exact absurd hxT h

end TubeCore

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## The support locus of a local-equation system -/

namespace Scheme.LocalEquations

variable {X S : Scheme.{u}} (d : X.LocalEquations)

/-- **The unit locus** of a local-equation system: the (open) union of the basic opens
of the equations — the locus where the divisor cut by `d` is trivial. -/
def unitLocus : X.Opens := ⨆ x, X.basicOpen (d.eqn x)

lemma basicOpen_le_unitLocus (x : X) : X.basicOpen (d.eqn x) ≤ d.unitLocus :=
  le_iSup (fun x => X.basicOpen (d.eqn x)) x

/-- Membership in the unit locus reads on ANY covering member containing the point:
`y ∈ unitLocus` iff the germ of `eqn x` at `y` is a unit, for every member `x` with
`y ∈ cover.opens x` (well-definedness across members is the ratio law). -/
lemma mem_unitLocus_iff_isUnit_germ {x y : X} (hy : y ∈ d.cover.opens x) :
    y ∈ d.unitLocus
      ↔ IsUnit ((X.presheaf.germ (d.cover.opens x) y hy).hom (d.eqn x)) := by
  constructor
  · intro h
    obtain ⟨x', hx'⟩ := Opens.mem_iSup.mp h
    have hy' : y ∈ d.cover.opens x' := X.basicOpen_le _ hx'
    have hu' : IsUnit ((X.presheaf.germ (d.cover.opens x') y hy').hom (d.eqn x')) :=
      (X.mem_basicOpen _ y hy').mp hx'
    obtain ⟨u, hu⟩ := d.ratio_isUnit x x'
    have hyW : y ∈ d.cover.opens x ⊓ d.cover.opens x' := ⟨hy, hy'⟩
    have h := congrArg
      ((X.presheaf.germ (d.cover.opens x ⊓ d.cover.opens x') y hyW).hom) hu
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h
    rw [h, IsUnit.mul_iff]
    exact ⟨u.isUnit.map _, hu'⟩
  · intro h
    exact Opens.mem_iSup.mpr ⟨x, (X.mem_basicOpen _ y hy).mpr h⟩

/-- **The support locus** of a local-equation system: the closed set of points where
the (well-defined) germ of the local equation fails to be a unit — the underlying set
of the divisor cut by `d`. -/
def supportLocus : Set X := (d.unitLocus : Set X)ᶜ

lemma isClosed_supportLocus : IsClosed d.supportLocus :=
  d.unitLocus.isOpen.isClosed_compl

lemma mem_supportLocus_iff_not_isUnit_germ {x y : X} (hy : y ∈ d.cover.opens x) :
    y ∈ d.supportLocus
      ↔ ¬ IsUnit ((X.presheaf.germ (d.cover.opens x) y hy).hom (d.eqn x)) :=
  not_congr (d.mem_unitLocus_iff_isUnit_germ hy)

/-- **The per-member trace of the support**: on a covering member, the support locus is
the member minus the basic open of its equation. -/
lemma supportLocus_inter_opens (x : X) :
    d.supportLocus ∩ (d.cover.opens x : Set X)
      = (d.cover.opens x : Set X) \ (X.basicOpen (d.eqn x) : Set X) := by
  ext y
  constructor
  · rintro ⟨hsupp, hy⟩
    refine ⟨hy, fun hyb => hsupp (d.basicOpen_le_unitLocus x hyb)⟩
  · rintro ⟨hy, hyb⟩
    refine ⟨fun hyU => hyb ?_, hy⟩
    exact (X.mem_basicOpen _ y hy).mpr ((d.mem_unitLocus_iff_isUnit_germ hy).mp hyU)

/-- **The support is closed over the base**: the image of the support locus under a
universally closed morphism (e.g. the structure morphism of the relative curve, from
the standing `IsProper C.hom`) is closed. -/
theorem isClosed_image_supportLocus (f : X ⟶ S) [UniversallyClosed f] :
    IsClosed (f.base '' d.supportLocus) :=
  f.isClosedMap _ d.isClosed_supportLocus

/-- **The support tube** (piece isolation, Zariski-locally on the base): for a
universally closed `f : X ⟶ S`, if the support fibre over a base point `s` is contained
in an open `U` (a union of adaptation pieces, in the DDR-4 instantiation), then there
is a Zariski neighbourhood `V` of `s` such that the whole support over `V` is contained
in `U`. -/
theorem exists_supportTube (f : X ⟶ S) [UniversallyClosed f] {U : Set X}
    (hU : IsOpen U) {s : S} (hfib : f.base ⁻¹' {s} ∩ d.supportLocus ⊆ U) :
    ∃ V : S.Opens, s ∈ V ∧ f.base ⁻¹' (V : Set S) ∩ d.supportLocus ⊆ U := by
  obtain ⟨V, hVopen, hsV, hV⟩ := (f.isClosedMap).exists_isOpen_preimage_inter_subset
    d.isClosed_supportLocus hU hfib
  exact ⟨⟨V, hVopen⟩, hsV, hV⟩

end Scheme.LocalEquations

/-! ## The licence: properness of the relative curve over an arbitrary test ring -/

section RelCurveProper

variable {k : Type u} [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
variable (R : Type u) [CommRing R] [Algebra k R]

/-- **Base change of properness to an arbitrary test ring**: the second projection of
`C ⊗ Spec R` is proper, for every commutative `k`-algebra `R` — the general-`R` form of
`Curve/BaseChangeInstances.instIsProperSndLeft` (which is keyed on field extensions).
This is the DDR-4 support-tube licence over the `Z(♦)`-chart rings `R_Z`. -/
instance instIsProperRelSndLeft : IsProper (snd C (overSpec k R)).left :=
  MorphismProperty.of_isPullback (P := @IsProper)
    (Over.isPullback_left C (overSpec k R)) inferInstance

/-- The properness instance, keyed on the `relCurve C R ↘ Spec R` spelling installed by
`relCurve.instOver` (definitionally the second projection). In particular
`UniversallyClosed (relCurve C R ↘ Spec R)` fires by resolution, which is what
`Scheme.LocalEquations.exists_supportTube` consumes. -/
instance instIsProperRelCurveHom :
    IsProper ((relCurve C R) ↘ Spec (CommRingCat.of R)) :=
  inferInstanceAs (IsProper (snd C (overSpec k R)).left)

/-- Acceptance smoke test: the support tube applies to the relative curve over an
arbitrary test ring with the universally-closed instance found by resolution. -/
private theorem supportTube_smoke (d : (relCurve C R).LocalEquations)
    {U : Set (relCurve C R)} (hU : IsOpen U) {s : Spec (CommRingCat.of R)}
    (hfib : ((relCurve C R) ↘ Spec (CommRingCat.of R)).base ⁻¹' {s} ∩ d.supportLocus
      ⊆ U) :
    ∃ V : (Spec (CommRingCat.of R)).Opens, s ∈ V ∧
      ((relCurve C R) ↘ Spec (CommRingCat.of R)).base ⁻¹' (V : Set (Spec (CommRingCat.of R)))
        ∩ d.supportLocus ⊆ U :=
  d.exists_supportTube _ hU hfib

end RelCurveProper

/-! ## The adaptation reads the same support, and the (c1) junction -/

section Adaptation

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k}

namespace FinCoverData

variable [IsFinite π] (D : FinCoverData C R π)

/-- **Flatness of the piece section rings over the test ring**: each `Γ(D(h_j))` is a
localization of a pinned-chart ring, which is free over `R`; the `FinCoverData`
companion of `ThetaGeneratorSeed.flat_sections_piece`. -/
theorem flat_sections_pieces (j : D.index) :
    Module.Flat R Γ(relCurve C R, D.pieces j) := by
  cases j with
  | inl j =>
      exact flat_sections_basicOpen R (relCover_isAffineOpen₀ C R (fiberTwoCover π))
        (flat_sections_relPinnedChart C R π false) (D.h₀ j)
  | inr j =>
      exact flat_sections_basicOpen R (relCover_isAffineOpen₁ C R (fiberTwoCover π))
        (flat_sections_relPinnedChart C R π true) (D.h₁ j)

end FinCoverData

namespace DivisorAdaptation

variable [IsAffineHom π] {d : (relCurve C R).LocalEquations}
variable (A : DivisorAdaptation C R π d)

/-- On a piece, the germ of the adaptation equation is a unit iff the germ of `d`'s
tautological equation is (the pointwise refinement clause `eqn_rel`, read at germs). -/
lemma isUnit_germ_eqn_iff (j : A.index) {w : relCurve C R} (hwj : w ∈ A.pieces j) :
    IsUnit (((relCurve C R).presheaf.germ (A.pieces j) w hwj).hom (A.eqn j))
      ↔ IsUnit (((relCurve C R).presheaf.germ (d.cover.opens w) w
          (d.cover.mem_opens w)).hom (d.eqn w)) := by
  obtain ⟨u, hu⟩ := A.eqn_rel j w
  have hwW : w ∈ A.pieces j ⊓ d.cover.opens w := ⟨hwj, d.cover.mem_opens w⟩
  have h := congrArg
    (((relCurve C R).presheaf.germ (A.pieces j ⊓ d.cover.opens w) w hwW).hom) hu
  rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h
  rw [h, IsUnit.mul_iff]
  exact and_iff_right (u.isUnit.map _)

/-- On a piece, membership in `d`'s unit locus is membership in the basic open of the
adaptation equation. -/
lemma mem_basicOpen_eqn_iff_mem_unitLocus (j : A.index) {w : relCurve C R}
    (hwj : w ∈ A.pieces j) :
    w ∈ (relCurve C R).basicOpen (A.eqn j) ↔ w ∈ d.unitLocus := by
  rw [(relCurve C R).mem_basicOpen _ w hwj, A.isUnit_germ_eqn_iff j hwj]
  exact (d.mem_unitLocus_iff_isUnit_germ (d.cover.mem_opens w)).symm

/-- The adaptation's basic opens land in `d`'s unit locus. -/
lemma basicOpen_eqn_le_unitLocus (j : A.index) :
    (relCurve C R).basicOpen (A.eqn j) ≤ d.unitLocus := fun _ hw =>
  (A.mem_basicOpen_eqn_iff_mem_unitLocus j
    ((relCurve C R).basicOpen_le (A.eqn j) hw)).mp hw

/-- **The adaptation computes the unit locus**: the union of the basic opens of the
adaptation equations IS `d`'s unit locus (so the adaptation and the system cut the same
support). Uses that the pieces cover the relative curve (`exists_mem_pieces`). -/
lemma iSup_basicOpen_eqn_eq_unitLocus :
    (⨆ j, (relCurve C R).basicOpen (A.eqn j)) = d.unitLocus := by
  refine le_antisymm (iSup_le fun j => A.basicOpen_eqn_le_unitLocus j) ?_
  intro w hw
  obtain ⟨j, hwj⟩ := A.toFinCoverData.exists_mem_pieces w
  exact Opens.mem_iSup.mpr ⟨j, (A.mem_basicOpen_eqn_iff_mem_unitLocus j hwj).mpr hw⟩

/-- **The per-piece trace of the family support**: on the piece `D(h_j)`, the support
locus of the family is exactly `D(h_j) \ D(f_j)` — the underlying set of the colength
`Γ(D(h_j)) ⧸ (f_j)`. This is the shape the DDR-4 finiteness argument consumes: the
piece trace of the globally closed (and, over the base, properly closed) support. -/
lemma supportLocus_inter_pieces (j : A.index) :
    d.supportLocus ∩ (A.pieces j : Set (relCurve C R))
      = (A.pieces j : Set (relCurve C R))
        \ ((relCurve C R).basicOpen (A.eqn j) : Set (relCurve C R)) := by
  ext w
  constructor
  · rintro ⟨hsupp, hwj⟩
    exact ⟨hwj, fun hwb => hsupp (A.basicOpen_eqn_le_unitLocus j hwb)⟩
  · rintro ⟨hwj, hwb⟩
    exact ⟨fun hwU => hwb ((A.mem_basicOpen_eqn_iff_mem_unitLocus j hwj).mpr hwU), hwj⟩

end DivisorAdaptation

namespace DivisorAdaptation

/-! ### The (c1) junction: flat, then finite projective, colengths -/

section Junction

variable [IsFinite π] {d : (relCurve C R).LocalEquations}
variable (A : DivisorAdaptation C R π d)

/-- **The (c1) flatness clause from fibrewise regularity** (the `SlicingFlat` keystone
on the piece ring): if the adaptation equation `f_j` is a nonzerodivisor in every
residue-field fibre `Γ(D(h_j)) ⊗ κ(p)`, then the chart-local colength
`Γ(D(h_j)) ⧸ (f_j)` is flat over the Noetherian test ring. The fibrewise hypothesis is
the seed's `fibre_regular` clause transported through `eqn_rel` (the I-0203 open
transport item). -/
theorem flat_colength_of_forall_tmul_residueField [IsNoetherianRing R]
    (j : A.index)
    (hfib : ∀ p : PrimeSpectrum R,
      (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
          Γ(relCurve C R, A.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
        nonZeroDivisors
          (Γ(relCurve C R, A.pieces j) ⊗[R] p.asIdeal.ResidueField)) :
    Module.Flat R (A.colength j) := by
  haveI : Module.Flat R Γ(relCurve C R, A.pieces j) :=
    A.toFinCoverData.flat_sections_pieces j
  exact Module.Flat.quotient_span_singleton_of_forall_tmul_residueField hfib

/-- **The certificate clause (c1) for the piece `j`**: fibrewise-regular equation +
finite colength (the support-tube finiteness input) ⟹ the colength is finite
projective over the Noetherian test ring — `IsCertified.finite_colength` and
`IsCertified.projective_colength` at `j`. -/
theorem projective_colength_of_forall_tmul_residueField [IsNoetherianRing R]
    (j : A.index)
    (hfib : ∀ p : PrimeSpectrum R,
      (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
          Γ(relCurve C R, A.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
        nonZeroDivisors
          (Γ(relCurve C R, A.pieces j) ⊗[R] p.asIdeal.ResidueField))
    [Module.Finite R (A.colength j)] :
    Module.Projective R (A.colength j) := by
  haveI : Module.Flat R Γ(relCurve C R, A.pieces j) :=
    A.toFinCoverData.flat_sections_pieces j
  exact Module.Projective.quotient_span_singleton_of_forall_tmul_residueField hfib

end Junction

end DivisorAdaptation

end Adaptation

end AlgebraicGeometry
