/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeFamilySide
import AlgebraicJacobian.Picard.DivisorFamilyExtraction
import AlgebraicJacobian.Picard.FibrewiseRegular

/-!
# DDR-3 — the relative local-generator construction (`informal/spec-dd-r.md` §3 item 3)

Kleiman `lm:ctn` (ii)⟹(iii)⟹(i) on the relative curve `C_R = relCurve C R` over a
Noetherian test ring `R` (the `Z(♦)`-chart rings): from a **theta generator seed** — a
choice, at every point `z` of `C_R`, of a pinned chart side, a basic-open neighbourhood
piece, and a section of a submodule `K ⊆ H⁰(𝒪(Θᵃ))` whose chart component *generates the
subsheaf `K·𝒪` on the piece* (`IsGenerator.dvd`, the Nakayama-neighbourhood clause) and is
*fibrewise regular* (`IsGenerator.fibre_regular`, the P-fib input at every `κ(p)`) — this
file constructs a `LocalEquations` system with a `DivisorAdaptation` refining it:

The flatness ladder and the side-uniform theta components live in
`AlgebraicJacobian.Picard.DivSchemeFamilySide`; this file assembles them:

* `AlgebraicGeometry.ThetaGeneratorSeed`, `ThetaGeneratorSeed.IsGenerator` — the seed and
  the two `lm:ctn` clauses, stated so that the fibrewise inputs are exactly what P-fib at
  `κ(p)` produces (spec §7 risk 2: one named boundary for the DD-4 transport seam);
* `ThetaGeneratorSeed.res_eqn_mem_nonZeroDivisors` /
  `ThetaGeneratorSeed.germ_eqn_mem_nonZeroDivisors` — **the germ-regularity law**
  ((iii)⟹(i)): fibrewise-regular + flat ⟹ regular, through
  `Module.Flat.mem_nonZeroDivisors_of_forall_tmul_residueField` on the basic-open
  section rings;
* `ThetaGeneratorSeed.exists_ratioUnit` — the overlap units: two local generators of the
  same subsheaf `K·𝒪` divide each other, and mutual divisibility against a regular
  section is a unit ratio;
* `ThetaGeneratorSeed.localEquations` / `ThetaGeneratorSeed.divisorAdaptation` — **the
  DDR-3 deliverable**: the local-equation system of the seed and a finite chart
  adaptation refining it (through the `exists_divisorAdaptation` extraction — no anchor
  field of `DivisorAdaptation` is consumed, per the DD-2 carrier-surgery freeze);
* `ThetaGeneratorSeed.le_vanishingSubmodule` — **the divisibility law for DDR-4/DDR-5**:
  `K ⊆ H⁰(𝒪(Θᵃ − d))` for the constructed system `d` (every element of `K` vanishes
  along `d`, germwise).

The construction of a seed from the universal carve pair (P-fib achiever choice at each
`κ(p)` + `exists_fibrewise_tmul_ne_zero_of_projective`) is the gated follow-up recorded
in the DDR-3 lane memory; it consumes `RiemannRoch/DegreeBaseFieldInvariance` and the
DD-4 base-field-transport seam and produces exactly a `ThetaGeneratorSeed` with
`IsGenerator`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra


/-! ## The theta generator seed and the `lm:ctn` clauses -/

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}

/-- **A theta generator seed for a submodule `K ⊆ H⁰(𝒪(Θᵃ))`** (worksheet §3.4.1): at
every point `z` of the relative curve, a pinned chart side containing `z`, a basic-open
neighbourhood piece `D(h z)` of the chart, and a global section `sec z ∈ K` — the
candidate local generator.  The two `lm:ctn` clauses on a seed are
`ThetaGeneratorSeed.IsGenerator`. -/
structure ThetaGeneratorSeed (C : Over (Spec (.of k))) (R : Type u) [CommRing R]
    [Algebra k R] (π : C.left ⟶ P1 k) [IsFinite π] (a : ℕ)
    (K : Submodule R (relThetaSections C R π a)) : Type u where
  /-- The pinned chart side of the piece at `z`. -/
  side : relCurve C R → Bool
  /-- The basic-open generator of the piece at `z`. -/
  h : ∀ z : relCurve C R, Γ(relCurve C R, relPinnedChart C R π (side z))
  /-- The point lies in its piece. -/
  mem_basicOpen : ∀ z : relCurve C R, z ∈ (relCurve C R).basicOpen (h z)
  /-- The candidate local generator at `z`. -/
  sec : relCurve C R → relThetaSections C R π a
  /-- The candidate generators are drawn from `K`. -/
  sec_mem : ∀ z, sec z ∈ K

namespace ThetaGeneratorSeed

variable {K : Submodule R (relThetaSections C R π a)} (D : ThetaGeneratorSeed C R π a K)

/-- The neighbourhood piece at `z`: the basic open `D(h z)` of the pinned chart. -/
noncomputable def piece (z : relCurve C R) : (relCurve C R).Opens :=
  (relCurve C R).basicOpen (D.h z)

lemma mem_piece (z : relCurve C R) : z ∈ D.piece z := D.mem_basicOpen z

lemma piece_le (z : relCurve C R) : D.piece z ≤ relPinnedChart C R π (D.side z) :=
  (relCurve C R).basicOpen_le (D.h z)

/-- The pieces are affine (basic opens of the affine pinned charts). -/
lemma isAffineOpen_piece (z : relCurve C R) : IsAffineOpen (D.piece z) :=
  (isAffineOpen_relPinnedChart C R π (D.side z)).basicOpen (D.h z)

/-- **Flatness of the piece sections over the test ring** (the (iii)⟹(i) licence). -/
theorem flat_sections_piece (z : relCurve C R) :
    Module.Flat R Γ(relCurve C R, D.piece z) :=
  flat_sections_basicOpen R (isAffineOpen_relPinnedChart C R π (D.side z))
    (flat_sections_relPinnedChart C R π (D.side z)) (D.h z)

/-- **The candidate local equation at `z`**: the side component of the chosen generator,
restricted to the piece. -/
noncomputable def eqn (z : relCurve C R) : Γ(relCurve C R, D.piece z) :=
  relThetaResSide a (D.side z) (D.piece_le z) (D.sec z)

/-- **The `lm:ctn` clauses on a seed** (Kleiman (ii)⟹(iii) packaged as its output, plus
the fibrewise-regularity input of (iii)⟹(i)):

* `dvd` — the chosen generator generates the subsheaf `K·𝒪` on its piece: the side
  component of every element of `K` is a multiple of the equation (the Nakayama
  neighbourhood clause, produced fibrewise by the P-fib achiever +
  `exists_fibrewise_tmul_ne_zero_of_projective`);
* `fibre_regular` — the equation is a nonzerodivisor in every residue-field fibre of
  every basic sub-open of the piece (produced by P-fib: the fibre of the equation is a
  nonzero section of an integral curve over `κ(p)`).

Both clauses are stated relative to the test ring only, so the DD-4 base-field-transport
seam moves a single boundary (spec-dd-r §7 risk 2). -/
structure IsGenerator : Prop where
  dvd : ∀ (z : relCurve C R) ⦃ψ : relThetaSections C R π a⦄, ψ ∈ K →
    relThetaResSide a (D.side z) (D.piece_le z) ψ ∈ Ideal.span {D.eqn z}
  fibre_regular : ∀ (z : relCurve C R) (p : PrimeSpectrum R)
      (f : Γ(relCurve C R, D.piece z)),
    ((relCurve C R).resHom ((relCurve C R).basicOpen_le f) (D.eqn z) ⊗ₜ[R]
        (1 : p.asIdeal.ResidueField)) ∈
      nonZeroDivisors
        (Γ(relCurve C R, (relCurve C R).basicOpen f) ⊗[R] p.asIdeal.ResidueField)

variable {D}

/-! ### The germ-regularity law ((iii)⟹(i): fibrewise-regular + flat ⟹ regular) -/

/-- **Section-level regularity on basic sub-opens of the piece**: the restriction of the
equation to any basic open `D(f) ⊆ D(h z)` is a nonzerodivisor — the slicing criterion
`Module.Flat.mem_nonZeroDivisors_of_forall_tmul_residueField` over the Noetherian test
ring, fed by the seed's fibrewise regularity. -/
theorem res_eqn_mem_nonZeroDivisors [IsNoetherianRing R] (hD : D.IsGenerator)
    (z : relCurve C R) (f : Γ(relCurve C R, D.piece z)) :
    (relCurve C R).resHom ((relCurve C R).basicOpen_le f) (D.eqn z)
      ∈ nonZeroDivisors Γ(relCurve C R, (relCurve C R).basicOpen f) := by
  haveI : Module.Flat R Γ(relCurve C R, (relCurve C R).basicOpen f) :=
    flat_sections_basicOpen R (D.isAffineOpen_piece z) (D.flat_sections_piece z) f
  exact Module.Flat.mem_nonZeroDivisors_of_forall_tmul_residueField
    (fun p => hD.fibre_regular z p f)

/-- **The germ-regularity law** ((iii)⟹(i), the `LocalEquations.regular` clause): every
germ of the equation on its piece is a nonzerodivisor.  A zerodivisor relation at the
stalk descends to a basic sub-open of the piece, where the flat slicing criterion
applies. -/
theorem germ_eqn_mem_nonZeroDivisors [IsNoetherianRing R] (hD : D.IsGenerator)
    (z : relCurve C R) {y : relCurve C R} (hy : y ∈ D.piece z) :
    ((relCurve C R).presheaf.germ (D.piece z) y hy).hom (D.eqn z)
      ∈ nonZeroDivisors ((relCurve C R).presheaf.stalk y) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro τ hτ
  obtain ⟨V', hyV', t, ht⟩ := (relCurve C R).presheaf.exists_germ_eq τ
  -- push the product relation into sections over `V' ⊓ piece z`
  have hyW₀ : y ∈ V' ⊓ D.piece z := ⟨hyV', hy⟩
  have hprod : ((relCurve C R).presheaf.germ (V' ⊓ D.piece z) y hyW₀).hom
      ((relCurve C R).resHom inf_le_left t
        * (relCurve C R).resHom inf_le_right (D.eqn z)) = 0 := by
    rw [map_mul]
    rw [show ((relCurve C R).presheaf.germ (V' ⊓ D.piece z) y hyW₀).hom
        ((relCurve C R).resHom inf_le_left t)
        = ((relCurve C R).presheaf.germ V' y hyV').hom t from
      TopCat.Presheaf.germ_res_apply _ _ _ _ _]
    rw [show ((relCurve C R).presheaf.germ (V' ⊓ D.piece z) y hyW₀).hom
        ((relCurve C R).resHom inf_le_right (D.eqn z))
        = ((relCurve C R).presheaf.germ (D.piece z) y hy).hom (D.eqn z) from
      TopCat.Presheaf.germ_res_apply _ _ _ _ _]
    rw [ht]
    exact hτ
  -- the product vanishes on a neighbourhood of `y`
  obtain ⟨W₁, hyW₁, i₁, i₂, heq⟩ := (relCurve C R).presheaf.germ_eq y hyW₀ hyW₀
    ((relCurve C R).resHom inf_le_left t
      * (relCurve C R).resHom inf_le_right (D.eqn z)) 0
    (by rw [hprod, map_zero])
  rw [map_zero] at heq
  -- shrink to a basic sub-open of the piece
  obtain ⟨f, hfle, hyf⟩ := (D.isAffineOpen_piece z).exists_basicOpen_le
    (⟨y, hyW₁⟩ : W₁) hy
  have hres := congrArg ((relCurve C R).resHom hfle) heq
  rw [map_zero, show i₁ = homOfLE i₁.le from Subsingleton.elim _ _] at hres
  rw [show (relCurve C R).resHom hfle
      (((relCurve C R).presheaf.map (homOfLE i₁.le).op).hom
        ((relCurve C R).resHom inf_le_left t
          * (relCurve C R).resHom inf_le_right (D.eqn z)))
      = (relCurve C R).resHom (hfle.trans i₁.le)
        ((relCurve C R).resHom inf_le_left t
          * (relCurve C R).resHom inf_le_right (D.eqn z)) from
    Scheme.resHom_resHom _ _ _] at hres
  rw [map_mul, Scheme.resHom_resHom, Scheme.resHom_resHom] at hres
  -- regularity on the basic sub-open kills the cofactor
  have ht0 : (relCurve C R).resHom ((hfle.trans i₁.le).trans inf_le_left) t = 0 :=
    (mul_right_mem_nonZeroDivisors_eq_zero_iff
      (D.res_eqn_mem_nonZeroDivisors hD z f)).mp hres
  -- the original stalk element was zero
  rw [← ht, show ((relCurve C R).presheaf.germ V' y hyV').hom t
      = ((relCurve C R).presheaf.germ ((relCurve C R).basicOpen f) y hyf).hom
        ((relCurve C R).resHom ((hfle.trans i₁.le).trans inf_le_left) t) from
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm, ht0, map_zero]

/-! ### The overlap ratio units -/

/-- **The ratio law of the seed's equations** (the `LocalEquations.ratio_isUnit` clause):
on the overlap of two pieces the equations differ by a unit.  Each equation divides the
other generator's component (`dvd` crosswise), the side matching transports components
across the charts, and mutual divisibility against a regular section is a unit ratio. -/
theorem exists_ratioUnit [IsNoetherianRing R] (hD : D.IsGenerator) (z z' : relCurve C R) :
    ∃ u : Γ(relCurve C R, D.piece z ⊓ D.piece z')ˣ,
      (relCurve C R).resHom inf_le_left (D.eqn z)
        = (u : Γ(relCurve C R, D.piece z ⊓ D.piece z'))
          * (relCurve C R).resHom inf_le_right (D.eqn z') := by
  have hWle : D.piece z ⊓ D.piece z'
      ≤ relPinnedChart C R π (D.side z) ⊓ relPinnedChart C R π (D.side z') :=
    inf_le_inf (D.piece_le z) (D.piece_le z')
  -- crosswise divisibility on the pieces
  obtain ⟨c₁, hc₁⟩ := Ideal.mem_span_singleton.mp (hD.dvd z (D.sec_mem z'))
  obtain ⟨c₂, hc₂⟩ := Ideal.mem_span_singleton.mp (hD.dvd z' (D.sec_mem z))
  -- the restricted equations are the side components of the generators on the overlap
  have hF1 : (relCurve C R).resHom
        (inf_le_left : D.piece z ⊓ D.piece z' ≤ D.piece z) (D.eqn z)
      = relThetaResSide a (D.side z) (hWle.trans inf_le_left) (D.sec z) :=
    resHom_relThetaResSide a (D.side z) (D.piece_le z) inf_le_left (D.sec z)
  have hF2 : (relCurve C R).resHom
        (inf_le_right : D.piece z ⊓ D.piece z' ≤ D.piece z') (D.eqn z')
      = relThetaResSide a (D.side z') (hWle.trans inf_le_right) (D.sec z') :=
    resHom_relThetaResSide a (D.side z') (D.piece_le z') inf_le_right (D.sec z')
  -- the crosswise divisibilities, restricted to the overlap
  have hF3 : relThetaResSide a (D.side z) (hWle.trans inf_le_left) (D.sec z')
      = (relCurve C R).resHom (inf_le_left : D.piece z ⊓ D.piece z' ≤ D.piece z) (D.eqn z)
        * (relCurve C R).resHom inf_le_left c₁ := by
    have h := congrArg ((relCurve C R).resHom
      (inf_le_left : D.piece z ⊓ D.piece z' ≤ D.piece z)) hc₁
    rw [map_mul] at h
    exact (resHom_relThetaResSide a (D.side z) (D.piece_le z)
      inf_le_left (D.sec z')).symm.trans h
  have hF4 : relThetaResSide a (D.side z') (hWle.trans inf_le_right) (D.sec z)
      = (relCurve C R).resHom
          (inf_le_right : D.piece z ⊓ D.piece z' ≤ D.piece z') (D.eqn z')
        * (relCurve C R).resHom inf_le_right c₂ := by
    have h := congrArg ((relCurve C R).resHom
      (inf_le_right : D.piece z ⊓ D.piece z' ≤ D.piece z')) hc₂
    rw [map_mul] at h
    exact (resHom_relThetaResSide a (D.side z') (D.piece_le z')
      inf_le_right (D.sec z)).symm.trans h
  -- the side matching for both generators
  have hM : ∀ ψ : relThetaSections C R π a,
      relThetaResSide a (D.side z) (hWle.trans inf_le_left) ψ
        = (relThetaSideUnit a (D.side z) (D.side z') hWle :
              Γ(relCurve C R, D.piece z ⊓ D.piece z'))
          * relThetaResSide a (D.side z') (hWle.trans inf_le_right) ψ :=
    fun ψ => relThetaResSide_matching a (D.side z) (D.side z') hWle ψ
  -- eqn z |_W = (θ · c₂|_W) · eqn z' |_W
  have h₁ : (relCurve C R).resHom
        (inf_le_left : D.piece z ⊓ D.piece z' ≤ D.piece z) (D.eqn z)
      = ((relThetaSideUnit a (D.side z) (D.side z') hWle :
            Γ(relCurve C R, D.piece z ⊓ D.piece z'))
          * (relCurve C R).resHom inf_le_right c₂)
        * (relCurve C R).resHom
            (inf_le_right : D.piece z ⊓ D.piece z' ≤ D.piece z') (D.eqn z') := by
    calc (relCurve C R).resHom
          (inf_le_left : D.piece z ⊓ D.piece z' ≤ D.piece z) (D.eqn z)
        = relThetaResSide a (D.side z) (hWle.trans inf_le_left) (D.sec z) := hF1
      _ = (relThetaSideUnit a (D.side z) (D.side z') hWle :
            Γ(relCurve C R, D.piece z ⊓ D.piece z'))
          * relThetaResSide a (D.side z') (hWle.trans inf_le_right) (D.sec z) :=
        hM (D.sec z)
      _ = (relThetaSideUnit a (D.side z) (D.side z') hWle :
            Γ(relCurve C R, D.piece z ⊓ D.piece z'))
          * ((relCurve C R).resHom
              (inf_le_right : D.piece z ⊓ D.piece z' ≤ D.piece z') (D.eqn z')
            * (relCurve C R).resHom inf_le_right c₂) := by rw [hF4]
      _ = ((relThetaSideUnit a (D.side z) (D.side z') hWle :
            Γ(relCurve C R, D.piece z ⊓ D.piece z'))
          * (relCurve C R).resHom inf_le_right c₂)
          * (relCurve C R).resHom
              (inf_le_right : D.piece z ⊓ D.piece z' ≤ D.piece z') (D.eqn z') := by
        ring
  -- eqn z' |_W = (θ⁻¹ · c₁|_W) · eqn z |_W
  have hQ : relThetaResSide a (D.side z') (hWle.trans inf_le_right) (D.sec z')
      = (((relThetaSideUnit a (D.side z) (D.side z') hWle)⁻¹ :
            Γ(relCurve C R, D.piece z ⊓ D.piece z')ˣ) :
            Γ(relCurve C R, D.piece z ⊓ D.piece z'))
        * relThetaResSide a (D.side z) (hWle.trans inf_le_left) (D.sec z') := by
    rw [Units.eq_inv_mul_iff_mul_eq]
    exact (hM (D.sec z')).symm
  have h₂ : (relCurve C R).resHom
        (inf_le_right : D.piece z ⊓ D.piece z' ≤ D.piece z') (D.eqn z')
      = ((((relThetaSideUnit a (D.side z) (D.side z') hWle)⁻¹ :
              Γ(relCurve C R, D.piece z ⊓ D.piece z')ˣ) :
              Γ(relCurve C R, D.piece z ⊓ D.piece z'))
          * (relCurve C R).resHom inf_le_left c₁)
        * (relCurve C R).resHom
            (inf_le_left : D.piece z ⊓ D.piece z' ≤ D.piece z) (D.eqn z) := by
    calc (relCurve C R).resHom
          (inf_le_right : D.piece z ⊓ D.piece z' ≤ D.piece z') (D.eqn z')
        = relThetaResSide a (D.side z') (hWle.trans inf_le_right) (D.sec z') := hF2
      _ = (((relThetaSideUnit a (D.side z) (D.side z') hWle)⁻¹ :
              Γ(relCurve C R, D.piece z ⊓ D.piece z')ˣ) :
              Γ(relCurve C R, D.piece z ⊓ D.piece z'))
          * relThetaResSide a (D.side z) (hWle.trans inf_le_left) (D.sec z') := hQ
      _ = (((relThetaSideUnit a (D.side z) (D.side z') hWle)⁻¹ :
              Γ(relCurve C R, D.piece z ⊓ D.piece z')ˣ) :
              Γ(relCurve C R, D.piece z ⊓ D.piece z'))
          * ((relCurve C R).resHom
              (inf_le_left : D.piece z ⊓ D.piece z' ≤ D.piece z) (D.eqn z)
            * (relCurve C R).resHom inf_le_left c₁) := by rw [hF3]
      _ = ((((relThetaSideUnit a (D.side z) (D.side z') hWle)⁻¹ :
              Γ(relCurve C R, D.piece z ⊓ D.piece z')ˣ) :
              Γ(relCurve C R, D.piece z ⊓ D.piece z'))
          * (relCurve C R).resHom inf_le_left c₁)
          * (relCurve C R).resHom
              (inf_le_left : D.piece z ⊓ D.piece z' ≤ D.piece z) (D.eqn z) := by
        ring
  -- germwise regularity of the restricted equation
  have hreg : ∀ (y : relCurve C R) (hy : y ∈ D.piece z ⊓ D.piece z'),
      ((relCurve C R).presheaf.germ (D.piece z ⊓ D.piece z') y hy).hom
        ((relCurve C R).resHom
          (inf_le_left : D.piece z ⊓ D.piece z' ≤ D.piece z) (D.eqn z))
        ∈ nonZeroDivisors ((relCurve C R).presheaf.stalk y) := by
    intro y hy
    rw [show ((relCurve C R).presheaf.germ (D.piece z ⊓ D.piece z') y hy).hom
        ((relCurve C R).resHom
          (inf_le_left : D.piece z ⊓ D.piece z' ≤ D.piece z) (D.eqn z))
        = ((relCurve C R).presheaf.germ (D.piece z) y hy.1).hom (D.eqn z) from
      TopCat.Presheaf.germ_res_apply _ _ _ _ _]
    exact D.germ_eqn_mem_nonZeroDivisors hD z hy.1
  exact exists_unit_mul_of_mutual_dvd hreg h₁ h₂

/-! ### The DDR-3 deliverable: the local-equation system and its adaptation -/

variable (D)

/-- **The local-equation system of a theta generator seed** (the DDR-3 family): the
pieces are the pointed cover, the equations are the side components of the chosen
generators; regularity is the germ-regularity law, the overlap units are the ratio
law. -/
noncomputable def localEquations [IsNoetherianRing R] (hD : D.IsGenerator) :
    (relCurve C R).LocalEquations where
  cover := { opens := D.piece, mem_opens := D.mem_piece }
  eqn := D.eqn
  regular := fun z _ hy => D.germ_eqn_mem_nonZeroDivisors hD z hy
  ratio_isUnit := fun z z' => D.exists_ratioUnit hD z z'

@[simp]
lemma localEquations_cover_opens [IsNoetherianRing R] (hD : D.IsGenerator)
    (z : relCurve C R) : (D.localEquations hD).cover.opens z = D.piece z := rfl

@[simp]
lemma localEquations_eqn [IsNoetherianRing R] (hD : D.IsGenerator) (z : relCurve C R) :
    (D.localEquations hD).eqn z = D.eqn z := rfl

/-- **The finite chart adaptation of the seed's local-equation system**, through the
DD-1 extraction (`exists_divisorAdaptation`); no anchor field of `DivisorAdaptation` is
consumed here (DD-2 carrier-surgery freeze discipline). -/
noncomputable def divisorAdaptation [IsNoetherianRing R] (hD : D.IsGenerator) :
    DivisorAdaptation C R π (D.localEquations hD) :=
  (exists_divisorAdaptation C R π (D.localEquations hD)).some

/-! ### The divisibility laws for DDR-4/DDR-5 -/

/-- **The stalk ideal of the constructed system is spanned by the seed equation** at the
tautological covering member. -/
lemma stalkIdeal_localEquations [IsNoetherianRing R] (hD : D.IsGenerator)
    (z : relCurve C R) :
    (D.localEquations hD).stalkIdeal z
      = Ideal.span {((relCurve C R).presheaf.germ (D.piece z) z (D.mem_piece z)).hom
          (D.eqn z)} := rfl

/-- **The germ divisibility law**: at any point `y` of the piece of `z`, the germ of the
side component of every element of `K` lies in the span of the germ of the equation. -/
theorem germ_relThetaResSide_mem_span [IsNoetherianRing R] (hD : D.IsGenerator)
    (z : relCurve C R) {ψ : relThetaSections C R π a} (hψ : ψ ∈ K)
    {y : relCurve C R} (hy : y ∈ D.piece z) :
    ((relCurve C R).presheaf.germ (D.piece z) y hy).hom
        (relThetaResSide a (D.side z) (D.piece_le z) ψ)
      ∈ Ideal.span
        {((relCurve C R).presheaf.germ (D.piece z) y hy).hom (D.eqn z)} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (hD.dvd z hψ)
  rw [hc, map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- **The vanishing law (the DDR-5 containment half)**: every element of `K` vanishes
along the constructed local-equation system — `K ⊆ H⁰(𝒪(Θᵃ − d))` in the DD-4 spelling
`Scheme.LocalEquations.vanishingSubmodule`. -/
theorem le_vanishingSubmodule [IsNoetherianRing R] (hD : D.IsGenerator) :
    K ≤ (D.localEquations hD).vanishingSubmodule R
      (relCover C R (fiberTwoCover π)).V₀ (relCover C R (fiberTwoCover π)).V₁
      (relThetaCocycle C R π a) := by
  intro ψ hψ
  rw [Scheme.LocalEquations.mem_vanishingSubmodule_iff]
  constructor
  · -- chart-0 component
    intro z hz
    have hz₀ : z ∈ relPinnedChart C R π false := hz.2
    -- work on the overlap of the piece of `z` with the pinned chart 0
    have hWle : D.piece z ⊓ relPinnedChart C R π false
        ≤ relPinnedChart C R π (D.side z) ⊓ relPinnedChart C R π false :=
      inf_le_inf (D.piece_le z) le_rfl
    have hzW : z ∈ D.piece z ⊓ relPinnedChart C R π false := ⟨D.mem_piece z, hz₀⟩
    -- the chart-0 component matches the side component through the side unit
    have hmatch := relThetaResSide_matching a false (D.side z) (le_inf
      (inf_le_right : D.piece z ⊓ relPinnedChart C R π false ≤ _)
      (inf_le_left.trans (D.piece_le z))) ψ
    -- germ of the side component lies in the stalk ideal
    have hside := D.germ_relThetaResSide_mem_span hD z hψ (D.mem_piece z)
    have hgermside : ((relCurve C R).presheaf.germ
        (D.piece z ⊓ relPinnedChart C R π false) z hzW).hom
          (relThetaResSide a (D.side z)
            ((le_inf (inf_le_right : D.piece z ⊓ relPinnedChart C R π false ≤ _)
              (inf_le_left.trans (D.piece_le z))).trans inf_le_right) ψ)
        ∈ (D.localEquations hD).stalkIdeal z := by
      rw [show relThetaResSide a (D.side z)
          ((le_inf (inf_le_right : D.piece z ⊓ relPinnedChart C R π false ≤ _)
            (inf_le_left.trans (D.piece_le z))).trans inf_le_right) ψ
          = (relCurve C R).resHom (inf_le_left : D.piece z ⊓ relPinnedChart C R π false
              ≤ D.piece z)
            (relThetaResSide a (D.side z) (D.piece_le z) ψ) from
        (resHom_relThetaResSide a (D.side z) (D.piece_le z) inf_le_left ψ).symm]
      rw [show ((relCurve C R).presheaf.germ
          (D.piece z ⊓ relPinnedChart C R π false) z hzW).hom
            ((relCurve C R).resHom (inf_le_left : D.piece z ⊓ relPinnedChart C R π false
              ≤ D.piece z) (relThetaResSide a (D.side z) (D.piece_le z) ψ))
          = ((relCurve C R).presheaf.germ (D.piece z) z (D.mem_piece z)).hom
            (relThetaResSide a (D.side z) (D.piece_le z) ψ) from
        TopCat.Presheaf.germ_res_apply _ _ _ _ _]
      rw [stalkIdeal_localEquations]
      exact D.germ_relThetaResSide_mem_span hD z hψ (D.mem_piece z)
    -- transport across the side unit
    have hkey := congrArg ((relCurve C R).presheaf.germ
      (D.piece z ⊓ relPinnedChart C R π false) z hzW).hom hmatch
    rw [map_mul] at hkey
    have hgerm₀ : ((relCurve C R).presheaf.germ
        (D.piece z ⊓ relPinnedChart C R π false) z hzW).hom
          (relThetaResSide a false ((le_inf
            (inf_le_right : D.piece z ⊓ relPinnedChart C R π false ≤ _)
            (inf_le_left.trans (D.piece_le z))).trans inf_le_left) ψ)
        = ((relCurve C R).presheaf.germ
            (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀) z hz).hom ψ.val.1 := by
      rw [relThetaResSide_false]
      exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hgerm₀] at hkey
    rw [hkey]
    exact Ideal.mul_mem_left _ _ hgermside
  · -- chart-1 component
    intro z hz
    have hz₁ : z ∈ relPinnedChart C R π true := hz.2
    have hzW : z ∈ D.piece z ⊓ relPinnedChart C R π true := ⟨D.mem_piece z, hz₁⟩
    have hmatch := relThetaResSide_matching a true (D.side z) (le_inf
      (inf_le_right : D.piece z ⊓ relPinnedChart C R π true ≤ _)
      (inf_le_left.trans (D.piece_le z))) ψ
    have hgermside : ((relCurve C R).presheaf.germ
        (D.piece z ⊓ relPinnedChart C R π true) z hzW).hom
          (relThetaResSide a (D.side z)
            ((le_inf (inf_le_right : D.piece z ⊓ relPinnedChart C R π true ≤ _)
              (inf_le_left.trans (D.piece_le z))).trans inf_le_right) ψ)
        ∈ (D.localEquations hD).stalkIdeal z := by
      rw [show relThetaResSide a (D.side z)
          ((le_inf (inf_le_right : D.piece z ⊓ relPinnedChart C R π true ≤ _)
            (inf_le_left.trans (D.piece_le z))).trans inf_le_right) ψ
          = (relCurve C R).resHom (inf_le_left : D.piece z ⊓ relPinnedChart C R π true
              ≤ D.piece z)
            (relThetaResSide a (D.side z) (D.piece_le z) ψ) from
        (resHom_relThetaResSide a (D.side z) (D.piece_le z) inf_le_left ψ).symm]
      rw [show ((relCurve C R).presheaf.germ
          (D.piece z ⊓ relPinnedChart C R π true) z hzW).hom
            ((relCurve C R).resHom (inf_le_left : D.piece z ⊓ relPinnedChart C R π true
              ≤ D.piece z) (relThetaResSide a (D.side z) (D.piece_le z) ψ))
          = ((relCurve C R).presheaf.germ (D.piece z) z (D.mem_piece z)).hom
            (relThetaResSide a (D.side z) (D.piece_le z) ψ) from
        TopCat.Presheaf.germ_res_apply _ _ _ _ _]
      rw [stalkIdeal_localEquations]
      exact D.germ_relThetaResSide_mem_span hD z hψ (D.mem_piece z)
    have hkey := congrArg ((relCurve C R).presheaf.germ
      (D.piece z ⊓ relPinnedChart C R π true) z hzW).hom hmatch
    rw [map_mul] at hkey
    have hgerm₁ : ((relCurve C R).presheaf.germ
        (D.piece z ⊓ relPinnedChart C R π true) z hzW).hom
          (relThetaResSide a true ((le_inf
            (inf_le_right : D.piece z ⊓ relPinnedChart C R π true ≤ _)
            (inf_le_left.trans (D.piece_le z))).trans inf_le_left) ψ)
        = ((relCurve C R).presheaf.germ
            (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁) z hz).hom ψ.val.2 := by
      rw [relThetaResSide_true]
      exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hgerm₁] at hkey
    rw [hkey]
    exact Ideal.mul_mem_left _ _ hgermside

end ThetaGeneratorSeed

end AlgebraicGeometry
