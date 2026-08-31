/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorThetaGlue
import AlgebraicJacobian.Picard.DivisorFamilyWindow
import AlgebraicJacobian.Cohomology.GluedSheafEngine

/-!
# DDR-4 (certificate transport) — the window–engine junction `H⁰(𝒪(Θᵃ − d)) ≅ K_a(d)`

THE seam brick of the DD-R endgame (`informal/spec-dd-r.md` §3 item 4, probe verdict
GREEN): the bridge between DD-1's `gluedSubmodule`-style carriers and the rigid engine's
Čech `H⁰` of the constructed family's twisted glued sheaf.  For a divisor family `d`
with finite chart adaptation `A` on the relative curve `C_R` and a twist exponent `a`,
the global sections of the theta-ideal datum sheaf (`DivisorAdaptation.thetaIdealDatum`,
the engine-ready presentation of `𝒪(Θᵃ − d)`) are identified `R`-linearly with the
vanishing submodule `K_a(d) = H⁰(𝒪(Θᵃ − d)) ⊆ H⁰(𝒪(Θᵃ))`:

* `DivisorAdaptation.vanishingSide` / `vanishingDiv` — a global twisted pair vanishing
  along `d`, read on the piece `D(h_p)` through its pinned-chart side, and its unique
  cofactor over the adaptation equation `f_p`;
* `DivisorAdaptation.vanishingToGlued` — **the backward junction**: the cofactor family
  is a matched family of the theta-ideal datum (transition units `(f_q/f_p)·θ^{±a}`) —
  a global section of the datum sheaf, with NO sheaf gluing (datum sections are
  definitionally matched families);
* `DivisorAdaptation.gluedVanishingFst/Snd`, `gluedToVanishing` — **the forward
  junction**: the two chart assemblies `gluedToIdeal₀/₁` of a global datum section form
  a twisted pair vanishing along `d`.

The junction equivalence `gluedEquivVanishing`/`datumH0EquivVanishing` (mutually
inverse by uniqueness of cofactors) and the engine transport (`datumRigidEngine` ⟹
`K_a(d)`/`divisorWindow` finite projective over a Noetherian test ring, given the
fibrewise `h¹`-data of the theta-ideal datum) are in
`AlgebraicJacobian.Picard.DivSchemeCertificateEngine` (the 500-line cap).

Everything is stated for an arbitrary adaptation, so the DDR-3 universal family
(`ThetaGeneratorSeed.divisorAdaptation`) and DD-4's Task-4 residual both consume it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} {R : Type u} [CommRing R]
  [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations} {A : DivisorAdaptation C R π d} {a : ℕ}

/-- Restriction of scheme sections commutes with the `Scheme.overModule` action. -/
private lemma resHom_smul {V W : (relCurve C R).Opens} (h : V ≤ W) (r : R)
    (s : Γ(relCurve C R, W)) :
    (relCurve C R).resHom h (r • s) = r • (relCurve C R).resHom h s := by
  rw [Scheme.overModule_smul_def, map_mul, Scheme.overModule_smul_def]
  congr 1
  exact (relCurve C R).overAlgebraMap_apply_res R (homOfLE h).op r

/-! ## The backward junction: from a vanishing pair to a global datum section -/

section Backward

variable (x : ↥(d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
    (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a)))

variable (A a) in
/-- **The side reading of a vanishing pair on a piece**: the pinned-chart component of
the pair on the part of the chart cut by `⊤ ⊓ D(h_p)`. -/
noncomputable def vanishingSide : ∀ p : A.index, Γ(relCurve C R, ⊤ ⊓ A.pieces p)
  | Sum.inl i => (relCurve C R).resHom
      (inf_le_inf le_rfl (A.pieces_inl_le i)) x.1.1.1
  | Sum.inr j => (relCurve C R).resHom
      (inf_le_inf le_rfl (A.pieces_inr_le j)) x.1.1.2

@[simp]
lemma vanishingSide_inl (i : Fin A.m₀) :
    vanishingSide A a x (Sum.inl i)
      = (relCurve C R).resHom (inf_le_inf le_rfl (A.pieces_inl_le i)) x.1.1.1 := rfl

@[simp]
lemma vanishingSide_inr (j : Fin A.m₁) :
    vanishingSide A a x (Sum.inr j)
      = (relCurve C R).resHom (inf_le_inf le_rfl (A.pieces_inr_le j)) x.1.1.2 := rfl

/-- The side readings vanish along `d` germwise. -/
lemma vanishingSide_germ_mem (p : A.index) :
    ∀ (z : relCurve C R) (hz : z ∈ (⊤ ⊓ A.pieces p : (relCurve C R).Opens)),
      ((relCurve C R).presheaf.germ (⊤ ⊓ A.pieces p) z hz).hom
        (vanishingSide A a x p) ∈ d.stalkIdeal z := by
  rcases p with i | j
  · intro z hz
    have hswap : ((relCurve C R).presheaf.germ (⊤ ⊓ A.pieces (Sum.inl i)) z hz).hom
        ((relCurve C R).resHom (inf_le_inf le_rfl (A.pieces_inl_le i)) x.1.1.1)
        = ((relCurve C R).presheaf.germ
            (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀) z
            ⟨trivial, A.pieces_inl_le i hz.2⟩).hom x.1.1.1 :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [vanishingSide_inl, hswap]
    exact x.2.1 z _
  · intro z hz
    have hswap : ((relCurve C R).presheaf.germ (⊤ ⊓ A.pieces (Sum.inr j)) z hz).hom
        ((relCurve C R).resHom (inf_le_inf le_rfl (A.pieces_inr_le j)) x.1.1.2)
        = ((relCurve C R).presheaf.germ
            (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁) z
            ⟨trivial, A.pieces_inr_le j hz.2⟩).hom x.1.1.2 :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [vanishingSide_inr, hswap]
    exact x.2.2 z _

/-- **The side matching**: on the double overlap `⊤ ⊓ D(h_p) ⊓ D(h_q)` the side
readings match through the theta twisting unit of the pair — same-chart pairs on the
nose, cross-chart pairs through the (inverse) theta cocycle, exactly the twisted-pair
matching of the underlying global section. -/
lemma vanishingSide_matching (p q : A.index) :
    (relCurve C R).resHom
        (le_inf le_top (inf_le_left.trans inf_le_right) :
          (⊤ ⊓ A.pieces p ⊓ A.pieces q : (relCurve C R).Opens) ≤ ⊤ ⊓ A.pieces p)
        (vanishingSide A a x p)
      = (relCurve C R).resHom
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            (⊤ ⊓ A.pieces p ⊓ A.pieces q : (relCurve C R).Opens)
              ≤ A.pieces p ⊓ A.pieces q)
          ((A.thetaOvlUnit a p q : Γ(relCurve C R, A.pieces p ⊓ A.pieces q)ˣ) :
            Γ(relCurve C R, A.pieces p ⊓ A.pieces q))
        * (relCurve C R).resHom
            (le_inf le_top inf_le_right :
              (⊤ ⊓ A.pieces p ⊓ A.pieces q : (relCurve C R).Opens) ≤ ⊤ ⊓ A.pieces q)
            (vanishingSide A a x q) := by
  -- the twisted matching of the underlying pair, restricted to the double overlap
  have hx := (mem_twistSubmodule_iff R (relCover C R (fiberTwoCover π)).V₀
    (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) x.1.1).mp x.1.2
  rcases p with i | i <;> rcases q with j | j
  · -- chart 0 / chart 0: the twisting unit is `1`
    have hovl : ((A.thetaOvlUnit a (Sum.inl i) (Sum.inl j) :
        Γ(relCurve C R, A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j))ˣ) :
        Γ(relCurve C R, A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j))) = 1 := rfl
    rw [hovl, map_one, one_mul]
    simp only [vanishingSide_inl, Scheme.resHom_resHom]
  · -- chart 0 / chart 1: the theta matching of the pair
    have key := congrArg ((relCurve C R).resHom
      (le_inf (le_inf le_top ((inf_le_left.trans inf_le_right).trans
          (A.pieces_inl_le i))) (inf_le_right.trans (A.pieces_inr_le j)) :
        (⊤ ⊓ A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j) : (relCurve C R).Opens)
          ≤ ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁)) hx
    rw [map_mul] at key
    simp only [Scheme.resHom_resHom] at key
    have hovl : ((A.thetaOvlUnit a (Sum.inl i) (Sum.inr j) :
        Γ(relCurve C R, A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j))ˣ) :
        Γ(relCurve C R, A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j)))
        = (relCurve C R).resHom
            (inf_le_inf (A.pieces_inl_le i) (A.pieces_inr_le j))
            ((relThetaCocycle C R π a :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)ˣ) :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)) := rfl
    rw [hovl]
    simp only [vanishingSide_inl, vanishingSide_inr, Scheme.resHom_resHom]
    exact key
  · -- chart 1 / chart 0: the inverse theta matching
    have key := congrArg ((relCurve C R).resHom
      (le_inf (le_inf le_top (inf_le_right.trans (A.pieces_inl_le j)))
          ((inf_le_left.trans inf_le_right).trans (A.pieces_inr_le i)) :
        (⊤ ⊓ A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inl j) : (relCurve C R).Opens)
          ≤ ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁)) hx
    rw [map_mul] at key
    simp only [Scheme.resHom_resHom] at key
    -- the inverse cocycle cancels against the cocycle
    have hcancel := congrArg ((relCurve C R).resHom
      (le_inf (inf_le_right.trans (A.pieces_inl_le j))
          ((inf_le_left.trans inf_le_right).trans (A.pieces_inr_le i)) :
        (⊤ ⊓ A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inl j) : (relCurve C R).Opens)
          ≤ (relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁))
      (Units.inv_mul (relThetaCocycle C R π a))
    rw [map_mul, map_one] at hcancel
    have hovl : ((A.thetaOvlUnit a (Sum.inr i) (Sum.inl j) :
        Γ(relCurve C R, A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inl j))ˣ) :
        Γ(relCurve C R, A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inl j)))
        = (relCurve C R).resHom
            (le_inf (inf_le_right.trans (A.pieces_inl_le j))
              (inf_le_left.trans (A.pieces_inr_le i)))
            (((relThetaCocycle C R π a)⁻¹ :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)ˣ).val) := rfl
    rw [hovl]
    simp only [vanishingSide_inl, vanishingSide_inr, Scheme.resHom_resHom]
    linear_combination (- (relCurve C R).resHom
        (le_inf (inf_le_right.trans (A.pieces_inl_le j))
          ((inf_le_left.trans inf_le_right).trans (A.pieces_inr_le i)) :
          (⊤ ⊓ A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inl j) : (relCurve C R).Opens)
            ≤ (relCover C R (fiberTwoCover π)).V₀ ⊓
              (relCover C R (fiberTwoCover π)).V₁)
        (((relThetaCocycle C R π a)⁻¹ :
          Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁)ˣ).val)) * key
      - (relCurve C R).resHom
          (le_inf le_top ((inf_le_left.trans inf_le_right).trans
            (A.pieces_inr_le i)) :
            (⊤ ⊓ A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inl j) : (relCurve C R).Opens)
              ≤ ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁) x.1.1.2 * hcancel
  · -- chart 1 / chart 1: the twisting unit is `1`
    have hovl : ((A.thetaOvlUnit a (Sum.inr i) (Sum.inr j) :
        Γ(relCurve C R, A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j))ˣ) :
        Γ(relCurve C R, A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j))) = 1 := rfl
    rw [hovl, map_one, one_mul]
    simp only [vanishingSide_inr, Scheme.resHom_resHom]

variable (A a) in
/-- **The cofactor family of a vanishing pair**: on each piece, the unique cofactor of
the side reading over the adaptation equation (`s = f_p · (s/f_p)` on `⊤ ⊓ D(h_p)`). -/
noncomputable abbrev vanishingDiv (p : A.index) : Γ(relCurve C R, ⊤ ⊓ A.pieces p) :=
  A.eqnDiv p (inf_le_right : ⊤ ⊓ A.pieces p ≤ A.pieces p) (vanishingSide A a x p)
    (vanishingSide_germ_mem x p)

/-- **The cofactor family matches through the theta-ideal transition units**
(`u_{pq} = (f_q/f_p) · θ^{±a}`): cancelling the regular equation `f_p` reduces the
matching to the side matching against the ratio law. -/
lemma vanishingDiv_matching (p q : A.index) :
    (relCurve C R).resHom
        (inf_le_left : (⊤ ⊓ A.pieces p ⊓ A.pieces q : (relCurve C R).Opens)
          ≤ ⊤ ⊓ A.pieces p) (vanishingDiv A a x p)
      = (relCurve C R).resHom
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            (⊤ ⊓ A.pieces p ⊓ A.pieces q : (relCurve C R).Opens)
              ≤ A.pieces p ⊓ A.pieces q)
          ((A.thetaIdealUnit a p q : Γ(relCurve C R, A.pieces p ⊓ A.pieces q)ˣ) :
            Γ(relCurve C R, A.pieces p ⊓ A.pieces q))
        * (relCurve C R).resHom
            (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
              (⊤ ⊓ A.pieces p ⊓ A.pieces q : (relCurve C R).Opens)
                ≤ ⊤ ⊓ A.pieces q) (vanishingDiv A a x q) := by
  refine A.eqn_res_cancel p (inf_le_left.trans inf_le_right) ?_
  -- `f_p · (s_p/f_p) = s_p` restricted to the double overlap
  have hL := congrArg ((relCurve C R).resHom
    (inf_le_left : (⊤ ⊓ A.pieces p ⊓ A.pieces q : (relCurve C R).Opens)
      ≤ ⊤ ⊓ A.pieces p))
    (A.eqn_mul_eqnDiv p inf_le_right (vanishingSide A a x p)
      (vanishingSide_germ_mem x p))
  -- `f_q · (s_q/f_q) = s_q` restricted to the double overlap
  have hR := congrArg ((relCurve C R).resHom
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      (⊤ ⊓ A.pieces p ⊓ A.pieces q : (relCurve C R).Opens) ≤ ⊤ ⊓ A.pieces q))
    (A.eqn_mul_eqnDiv q inf_le_right (vanishingSide A a x q)
      (vanishingSide_germ_mem x q))
  -- the ratio law `f_p · (f_q/f_p) = f_q` restricted to the double overlap
  have hratio := congrArg ((relCurve C R).resHom
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      (⊤ ⊓ A.pieces p ⊓ A.pieces q : (relCurve C R).Opens)
        ≤ A.pieces p ⊓ A.pieces q))
    (A.eqn_mul_eqnRatio p q)
  -- the side matching
  have hside := vanishingSide_matching x p q
  -- the ideal unit is the ratio unit times the twisting unit
  have hunit := congrArg ((relCurve C R).resHom
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      (⊤ ⊓ A.pieces p ⊓ A.pieces q : (relCurve C R).Opens)
        ≤ A.pieces p ⊓ A.pieces q))
    (show ((A.thetaIdealUnit a p q : Γ(relCurve C R, A.pieces p ⊓ A.pieces q)ˣ) :
        Γ(relCurve C R, A.pieces p ⊓ A.pieces q))
      = ((A.eqnRatio p q : Γ(relCurve C R, A.pieces p ⊓ A.pieces q)ˣ) :
          Γ(relCurve C R, A.pieces p ⊓ A.pieces q))
        * ((A.thetaOvlUnit a p q : Γ(relCurve C R, A.pieces p ⊓ A.pieces q)ˣ) :
            Γ(relCurve C R, A.pieces p ⊓ A.pieces q)) from rfl)
  rw [map_mul] at hL hR hratio hunit
  simp only [Scheme.resHom_resHom] at hL hR hratio hunit
  linear_combination hL + hside
    - (relCurve C R).resHom
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          (⊤ ⊓ A.pieces p ⊓ A.pieces q : (relCurve C R).Opens)
            ≤ A.pieces p ⊓ A.pieces q)
        ((A.thetaOvlUnit a p q : Γ(relCurve C R, A.pieces p ⊓ A.pieces q)ˣ) :
          Γ(relCurve C R, A.pieces p ⊓ A.pieces q)) * hR
    - (relCurve C R).resHom
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          (⊤ ⊓ A.pieces p ⊓ A.pieces q : (relCurve C R).Opens)
            ≤ A.pieces p ⊓ A.pieces q)
        ((A.thetaOvlUnit a p q : Γ(relCurve C R, A.pieces p ⊓ A.pieces q)ˣ) :
          Γ(relCurve C R, A.pieces p ⊓ A.pieces q))
      * (relCurve C R).resHom
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            (⊤ ⊓ A.pieces p ⊓ A.pieces q : (relCurve C R).Opens) ≤ ⊤ ⊓ A.pieces q)
          (vanishingDiv A a x q) * hratio
    - (relCurve C R).resHom
        (inf_le_left.trans inf_le_right :
          (⊤ ⊓ A.pieces p ⊓ A.pieces q : (relCurve C R).Opens) ≤ A.pieces p)
        (A.eqn p)
      * (relCurve C R).resHom
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            (⊤ ⊓ A.pieces p ⊓ A.pieces q : (relCurve C R).Opens) ≤ ⊤ ⊓ A.pieces q)
          (vanishingDiv A a x q) * hunit

variable (A a) in
/-- **The backward junction**: the cofactor family of a vanishing pair is a matched
family of the theta-ideal datum — a global section of the datum sheaf over `⊤`.  No
sheaf gluing is involved: datum sections are definitionally matched families. -/
noncomputable def vanishingToGlued : A.ThetaIdealSections a ⊤ :=
  ⟨fun p => match p with
    | Sum.inl i => vanishingDiv A a x (Sum.inl i.down)
    | Sum.inr j => vanishingDiv A a x (Sum.inr j.down), by
    intro p q
    rcases p with i | i <;> rcases q with j | j
    · exact vanishingDiv_matching x (Sum.inl i.down) (Sum.inl j.down)
    · exact vanishingDiv_matching x (Sum.inl i.down) (Sum.inr j.down)
    · exact vanishingDiv_matching x (Sum.inr i.down) (Sum.inl j.down)
    · exact vanishingDiv_matching x (Sum.inr i.down) (Sum.inr j.down)⟩

@[simp]
lemma vanishingToGlued_val_inl (i : ULift.{u} (Fin A.m₀)) :
    (vanishingToGlued A a x).val (Sum.inl i) = vanishingDiv A a x (Sum.inl i.down) :=
  rfl

@[simp]
lemma vanishingToGlued_val_inr (j : ULift.{u} (Fin A.m₁)) :
    (vanishingToGlued A a x).val (Sum.inr j) = vanishingDiv A a x (Sum.inr j.down) :=
  rfl

end Backward

/-! ## The forward junction: from a global datum section to a vanishing pair -/

section Forward

variable (A a) in
/-- The chart-0 assembly of a global datum section, on `⊤ ⊓ V₀`. -/
noncomputable def gluedVanishingFst (s : A.ThetaIdealSections a ⊤) :
    Γ(relCurve C R, ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀) :=
  gluedToIdeal₀ A a
    (inf_le_right : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀
      ≤ (relCover C R (fiberTwoCover π)).V₀)
    (secRes ((A.thetaIdealDatum a).sheaf)
      (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ≤ ⊤) s)

variable (A a) in
/-- The chart-1 assembly of a global datum section, on `⊤ ⊓ V₁`. -/
noncomputable def gluedVanishingSnd (s : A.ThetaIdealSections a ⊤) :
    Γ(relCurve C R, ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁) :=
  gluedToIdeal₁ A a
    (inf_le_right : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁
      ≤ (relCover C R (fiberTwoCover π)).V₁)
    (secRes ((A.thetaIdealDatum a).sheaf)
      (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁ ≤ ⊤) s)

/-- The two assemblies form a Θ-twisted pair (`gluedToIdeal₀ = θᵃ · gluedToIdeal₁` on
the chart overlap). -/
lemma gluedVanishing_mem_twist (s : A.ThetaIdealSections a ⊤) :
    (gluedVanishingFst A a s, gluedVanishingSnd A a s) ∈
      twistSubmodule R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) ⊤ := by
  rw [mem_twistSubmodule_iff]
  have hΩ : (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ⊓
      (relCover C R (fiberTwoCover π)).V₁ : (relCurve C R).Opens) ≤
      (relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁ :=
    inf_le_inf inf_le_right le_rfl
  have h₀ := gluedToIdeal₀_secRes
    (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ⊓
      (relCover C R (fiberTwoCover π)).V₁ ≤ ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀)
    (inf_le_right : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀
      ≤ (relCover C R (fiberTwoCover π)).V₀)
    (secRes ((A.thetaIdealDatum a).sheaf)
      (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ≤ ⊤) s)
  have h₁ := gluedToIdeal₁_secRes
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁
        ≤ ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁)
    (inf_le_right : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁
      ≤ (relCover C R (fiberTwoCover π)).V₁)
    (secRes ((A.thetaIdealDatum a).sheaf)
      (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁ ≤ ⊤) s)
  rw [secRes_secRes] at h₀ h₁
  have hcmp := gluedToIdeal₀_eq_theta_mul_gluedToIdeal₁ (A := A) (a := a) hΩ
    (secRes ((A.thetaIdealDatum a).sheaf)
      (le_top : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ⊓
        (relCover C R (fiberTwoCover π)).V₁ ≤ ⊤) s)
  exact h₀.symm.trans (hcmp.trans (congrArg
    (fun t => (relCurve C R).resHom hΩ
      ((relThetaCocycle C R π a :
        Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
          (relCover C R (fiberTwoCover π)).V₁)ˣ) :
        Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
          (relCover C R (fiberTwoCover π)).V₁)) * t) h₁))

variable (A a) in
/-- **The forward junction**: the twisted pair assembled from a global datum section
vanishes along `d` — an element of the vanishing submodule `K_a(d)`. -/
noncomputable def gluedToVanishing (s : A.ThetaIdealSections a ⊤) :
    ↥(d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
      (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a)) :=
  ⟨⟨(gluedVanishingFst A a s, gluedVanishingSnd A a s),
    gluedVanishing_mem_twist s⟩,
    ⟨fun z hz => germ_gluedToIdeal₀_mem
      (inf_le_right : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀
        ≤ (relCover C R (fiberTwoCover π)).V₀)
      (secRes ((A.thetaIdealDatum a).sheaf)
        (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ≤ ⊤) s) z hz,
     fun z hz => germ_gluedToIdeal₁_mem
      (inf_le_right : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁
        ≤ (relCover C R (fiberTwoCover π)).V₁)
      (secRes ((A.thetaIdealDatum a).sheaf)
        (inf_le_left : ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁ ≤ ⊤) s) z hz⟩⟩

end Forward
end DivisorAdaptation

end AlgebraicGeometry
