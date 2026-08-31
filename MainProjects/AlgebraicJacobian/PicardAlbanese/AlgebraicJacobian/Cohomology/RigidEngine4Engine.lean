/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RigidEngine4Relative

/-!
# RE-4 — the rigid engine fired on the relative twisted sheaf

The Layer-2 keystones of the sheaf-level rigid engine (worksheet
`informal/w4-rigid-engine-worksheet.md` §1.2 Level 2): the abstract engine of
`RigidEngine4Assembly` instantiated on the **relative twisted sheaf**
`relTwistSheaf C R (fiberTwoCover π) g` on the pinned relative cover, with **every**
hypothesis discharged from the landed inputs:

* the pair data (`relTwistPairData`) from the relative chart coordinates
  (`relFiberCoord₀/₁`, `RigidEngine4Relative`) through the generic twisted pair data
  (`twistPairData`, `RigidEngine4Twist`);
* the pinned `AEval'` chart finiteness through the trivializations and the relative E-i
  (`moduleFinite_aeval'_relTwistPair_t₀/₁`, = RE-4b assembled);
* flatness/projectivity of the section modules from freeness (`k`-bases are `R`-bases:
  `free_relSections` + `free_twistSheafSections₀/₁`).

## Main declarations

* `relTwistRigidEngine` — **Kleiman 3.10 (v)⟹(i)+(iii), curve-lite, relative**: under
  the complex-form fibrewise-vanishing hypothesis, `H¹(C_R, F_g) = 0` and
  `H⁰(C_R, F_g)` is a finite projective `R`-module.
* `relTwistRigidEngine_isOpen_vanishing` — the strata openness export.
* `relTwistH0TensorEquiv` — the module-coefficient clause (Kleiman `eq:Q`):
  `H⁰(C_R, F_g) ⊗[R] P ≃ₗ[R] ker (δ ⊗ P)` for every `R`-module `P`.
* `relTwistH0BaseChangeEquiv` — the ring-map clause, abstract half:
  `R' ⊗[R] H⁰(C_R, F_g) ≃ₗ[R'] ker (δ.baseChange R')` for every `R`-algebra `R'`
  (threading through CBC-1 onto `H⁰` of the base-changed sheaf composes this with
  `RigidEngine.kerCongr` along `relTwistTermBaseChange₀/₁`/`relTwistOverlapBaseChange`
  and the twisted δ-naturality — the `RelativeH1BaseChange` frontier).

**Staging note (worksheet §3.2, BINDING).** The fibre hypothesis `hfib` is consumed in
COMPLEX form (`Subsingleton (H¹(pair) ⊗ κ(p))`); its sheaf-level discharge (glued fibre
sheaf ≅ divisor sheaf of a witness + the FLV class form) and the rank export
(`finrank κ(p) (H⁰ ⊗ κ(p)) = deg + χ`) gate on the W6-full seam and are deliberately NOT
attempted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite Polynomial

open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule

variable {k : Type u} [Field k] (C : Over (Spec (.of k))) (R : Type u) [CommRing R]
  [Algebra k R]
variable (π : C.left ⟶ P1 k)

/-- The relative twisted sheaf inherits the quasi-coherence packaging on the first chart
of the base-changed cover (delegation of `twistSheaf.instQcohOn₀`, keyed on
`relTwistSheaf`). -/
noncomputable instance relTwistSheaf.instQcohOn₀ (D : C.left.AffineTwoCover)
    (g : Γ(relCurve C R, (relCover C R D).V₀ ⊓ (relCover C R D).V₁)ˣ) :
    Scheme.QcohOn (relTwistSheaf C R D g) (relCover C R D).V₀ :=
  twistSheaf.instQcohOn₀ R (relCover C R D).V₀ (relCover C R D).V₁ g

/-- The relative twisted sheaf inherits the quasi-coherence packaging on the second
chart of the base-changed cover. -/
noncomputable instance relTwistSheaf.instQcohOn₁ (D : C.left.AffineTwoCover)
    (g : Γ(relCurve C R, (relCover C R D).V₀ ⊓ (relCover C R D).V₁)ˣ) :
    Scheme.QcohOn (relTwistSheaf C R D g) (relCover C R D).V₁ :=
  twistSheaf.instQcohOn₁ R (relCover C R D).V₀ (relCover C R D).V₁ g

variable [IsFinite π]
variable (g : Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
  (relCover C R (fiberTwoCover π)).V₁)ˣ)

/-- **The two-cover pair data of the relative twisted sheaf** on the pinned relative
cover: chart coordinates the pulled-back `t₀ᴿ, t₁ᴿ`, overlap-as-basic-open from
`Scheme.preimage_basicOpen` on the pinned cover, mutual inverse law from the pulled-back
`P1.chartCoord` relation. Its `pair` is the two-lattice pair of `F_g` that the rigid
engine consumes. -/
noncomputable def relTwistPairData :
    Scheme.TwoCoverPairData (relTwistSheaf C R (fiberTwoCover π) g)
      (relCover C R (fiberTwoCover π)).V₀ (relCover C R (fiberTwoCover π)).V₁ :=
  twistPairData R g (relFiberCoord₀ C R π) (relFiberCoord₁ C R π)
    (relCover_fiberTwoCover_inf_eq_basicOpen₀ C R π)
    (relCover_fiberTwoCover_inf_eq_basicOpen₁ C R π)
    (relFiberCoord_mul C R π)

/-- **RE-4b assembled, chart 0**: the pinned `AEval'` finiteness of the relative twist
pair's chart-0 lattice, from the relative E-i through the trivialization. -/
theorem moduleFinite_aeval'_relTwistPair_t₀ (hπ : π ≫ P1.structureMap k = C.hom) :
    Module.Finite (Polynomial R) (Module.AEval'
      (((relTwistPairData C R π g).pair (relCover_isAffineOpen₀ C R (fiberTwoCover π))
        (relCover_isAffineOpen₁ C R (fiberTwoCover π))).t₀)) := by
  haveI := moduleFinite_aeval'_mulSectionEnd_relFiberCoord₀ C R π hπ
  exact moduleFinite_aeval'_twistPair_t₀ R g (relFiberCoord₀ C R π)
    (relFiberCoord₁ C R π) (relCover_fiberTwoCover_inf_eq_basicOpen₀ C R π)
    (relCover_fiberTwoCover_inf_eq_basicOpen₁ C R π) (relFiberCoord_mul C R π)
    (relCover_isAffineOpen₀ C R (fiberTwoCover π))
    (relCover_isAffineOpen₁ C R (fiberTwoCover π))

/-- **RE-4b assembled, chart 1**. -/
theorem moduleFinite_aeval'_relTwistPair_t₁ (hπ : π ≫ P1.structureMap k = C.hom) :
    Module.Finite (Polynomial R) (Module.AEval'
      (((relTwistPairData C R π g).pair (relCover_isAffineOpen₀ C R (fiberTwoCover π))
        (relCover_isAffineOpen₁ C R (fiberTwoCover π))).t₁)) := by
  haveI := moduleFinite_aeval'_mulSectionEnd_relFiberCoord₁ C R π hπ
  exact moduleFinite_aeval'_twistPair_t₁ R g (relFiberCoord₀ C R π)
    (relFiberCoord₁ C R π) (relCover_fiberTwoCover_inf_eq_basicOpen₀ C R π)
    (relCover_fiberTwoCover_inf_eq_basicOpen₁ C R π) (relFiberCoord_mul C R π)
    (relCover_isAffineOpen₀ C R (fiberTwoCover π))
    (relCover_isAffineOpen₁ C R (fiberTwoCover π))

/-- **Freeness of the twisted section modules on the pinned relative cover** — chart 0:
a `k`-basis of `Γ(C, V₀)` is an `R`-basis, transported through the trivialization. -/
theorem free_relTwistSections₀ :
    Module.Free R ((relTwistSheaf C R (fiberTwoCover π) g).obj.obj
      (op (relCover C R (fiberTwoCover π)).V₀)) := by
  haveI : Module.Free R Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀) :=
    free_relSections C R (fiberChart₀ π)
      (isAffineOpen_preimage_chartOpen π 0).isCompact
      (isAffineOpen_preimage_chartOpen π 0).isQuasiSeparated
  exact free_twistSheafSections₀ R g (le_refl (relCover C R (fiberTwoCover π)).V₀)

/-- Freeness of the twisted section modules — chart 1. -/
theorem free_relTwistSections₁ :
    Module.Free R ((relTwistSheaf C R (fiberTwoCover π) g).obj.obj
      (op (relCover C R (fiberTwoCover π)).V₁)) := by
  haveI : Module.Free R Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₁) :=
    free_relSections C R (fiberChart₁ π)
      (isAffineOpen_preimage_chartOpen π 1).isCompact
      (isAffineOpen_preimage_chartOpen π 1).isQuasiSeparated
  exact free_twistSheafSections₁ R g (le_refl (relCover C R (fiberTwoCover π)).V₁)

/-- Freeness of the twisted section modules — the overlap (the pair's overlap module is
free, hence flat and projective: the split/flat rigidity inputs of RE-3). -/
theorem free_relTwistSectionsOverlap :
    Module.Free R ((relTwistSheaf C R (fiberTwoCover π) g).obj.obj
      (op ((relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁))) := by
  haveI : Module.Free R Γ(relCurve C R,
      (relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁) :=
    free_relSections C R (fiberChart₀ π ⊓ fiberChart₁ π)
      (fiberTwoCover π).isAffineOpen_inf.isCompact
      (fiberTwoCover π).isAffineOpen_inf.isQuasiSeparated
  exact free_twistSheafSections₀ R g
    (inf_le_left : (relCover C R (fiberTwoCover π)).V₀ ⊓
      (relCover C R (fiberTwoCover π)).V₁ ≤ (relCover C R (fiberTwoCover π)).V₀)

/-! ## The keystones -/

section Keystones

variable (hπ : π ≫ P1.structureMap k = C.hom)

/-- (Implementation) The two-lattice pair of the relative twisted sheaf. -/
noncomputable abbrev relTwistPair := (relTwistPairData C R π g).pair
  (relCover_isAffineOpen₀ C R (fiberTwoCover π))
  (relCover_isAffineOpen₁ C R (fiberTwoCover π))

include hπ in
/-- **The rigid engine on the relative twisted sheaf** (Kleiman 3.10 (v)⟹(i)+(iii),
curve-lite; worksheet §1.2 Level 2, all hypotheses discharged): if every residue-field
fibre of `H¹` of the two-lattice pair of `F_g` vanishes (complex form — the sheaf-level
discharge is the W6-full seam), then

* `H¹(C_R, F_g) = 0`,
* `H⁰(C_R, F_g)` is a finite projective `R`-module. -/
theorem relTwistRigidEngine [IsNoetherianRing R]
    (hfib : ∀ p : PrimeSpectrum R,
      Subsingleton ((relTwistPair C R π g).H1 ⊗[R] p.asIdeal.ResidueField)) :
    Subsingleton (Sheaf.HModule (relTwistSheaf C R (fiberTwoCover π) g) 1) ∧
      Module.Finite R (Sheaf.HModule (relTwistSheaf C R (fiberTwoCover π) g) 0) ∧
      Module.Projective R (Sheaf.HModule (relTwistSheaf C R (fiberTwoCover π) g) 0) := by
  haveI := moduleFinite_aeval'_relTwistPair_t₀ C R π g hπ
  haveI := moduleFinite_aeval'_relTwistPair_t₁ C R π g hπ
  haveI := free_relTwistSections₀ C R π g
  haveI := free_relTwistSections₁ C R π g
  haveI := free_relTwistSectionsOverlap C R π g
  exact (relTwistPairData C R π g).rigidEngine
    (relCover_isAffineOpen₀ C R (fiberTwoCover π))
    (relCover_isAffineOpen₁ C R (fiberTwoCover π))
    (relCover_sup C R (fiberTwoCover π)) hfib

include hπ in
/-- **The openness export on the relative twisted sheaf** (the strata gift, worksheet
§3.3): the fibrewise-vanishing locus of `H¹` of the pair of `F_g` is open in `Spec R`.
Noetherian-free (COH-1 + RE-2). -/
theorem relTwistRigidEngine_isOpen_vanishing :
    IsOpen {p : PrimeSpectrum R |
      Subsingleton ((relTwistPair C R π g).H1 ⊗[R] p.asIdeal.ResidueField)} := by
  haveI := moduleFinite_aeval'_relTwistPair_t₀ C R π g hπ
  haveI := moduleFinite_aeval'_relTwistPair_t₁ C R π g hπ
  exact (relTwistPairData C R π g).rigidEngine_isOpen_vanishing
    (relCover_isAffineOpen₀ C R (fiberTwoCover π))
    (relCover_isAffineOpen₁ C R (fiberTwoCover π))

/-- **The module-coefficient clause on the relative twisted sheaf** (Kleiman `eq:Q`;
worksheet §1.2 `h0_baseChange`): on the vanishing locus, formation of `H⁰(C_R, F_g)`
commutes with `⊗_R P` for **every** `R`-module `P`. -/
noncomputable def relTwistH0TensorEquiv
    (hH1 : Subsingleton (relTwistPair C R π g).H1)
    (P : Type u) [AddCommGroup P] [Module R P] :
    (Sheaf.HModule (relTwistSheaf C R (fiberTwoCover π) g) 0) ⊗[R] P ≃ₗ[R]
      ↥(LinearMap.ker ((relTwistPair C R π g).diff.rTensor P)) := by
  haveI := free_relTwistSectionsOverlap C R π g
  exact (relTwistPairData C R π g).h0TensorEquiv
    (relCover_isAffineOpen₀ C R (fiberTwoCover π))
    (relCover_isAffineOpen₁ C R (fiberTwoCover π))
    (relCover_sup C R (fiberTwoCover π)) hH1 P

/-- **The ring-map base-change clause on the relative twisted sheaf, abstract half**
(worksheet §1.2 `rigidEngine_baseChange`): on the vanishing locus,
`R' ⊗[R] H⁰(C_R, F_g)` is `R'`-linearly the kernel of the base-changed Čech
differential, for **every** `R`-algebra `R'`. Threading onto `H⁰` of the base-changed
sheaf on the nose composes this with `RigidEngine.kerCongr` along the CBC-1 term
identifications (`relTwistTermBaseChange₀/₁`, `relTwistOverlapBaseChange`) and the
twisted δ-naturality square — the `RelativeH1BaseChange` frontier. -/
noncomputable def relTwistH0BaseChangeEquiv
    (hH1 : Subsingleton (relTwistPair C R π g).H1)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    R' ⊗[R] (Sheaf.HModule (relTwistSheaf C R (fiberTwoCover π) g) 0) ≃ₗ[R']
      ↥(LinearMap.ker ((relTwistPair C R π g).diff.baseChange R')) := by
  haveI := free_relTwistSectionsOverlap C R π g
  exact (relTwistPairData C R π g).h0BaseChangeEquiv
    (relCover_isAffineOpen₀ C R (fiberTwoCover π))
    (relCover_isAffineOpen₁ C R (fiberTwoCover π))
    (relCover_sup C R (fiberTwoCover π)) hH1 R'

include hπ in
/-- **The vanishing hypothesis in pair form from the fibre form** — convenience wrapper:
COH-1 + Nakayama propagation for the pair of `F_g` (Noetherian-free). Consumers holding
the fibrewise hypothesis can use this to feed `relTwistH0TensorEquiv`/
`relTwistH0BaseChangeEquiv`. -/
theorem relTwist_subsingleton_pairH1
    (hfib : ∀ p : PrimeSpectrum R,
      Subsingleton ((relTwistPair C R π g).H1 ⊗[R] p.asIdeal.ResidueField)) :
    Subsingleton (relTwistPair C R π g).H1 := by
  haveI := moduleFinite_aeval'_relTwistPair_t₀ C R π g hπ
  haveI := moduleFinite_aeval'_relTwistPair_t₁ C R π g hπ
  haveI : Module.Finite R (relTwistPair C R π g).H1 :=
    (relTwistPair C R π g).moduleFinite_h1
  exact AlgebraicJacobian.RigidEngine.subsingleton_of_forall_subsingleton_residueField_tensor
    hfib

end Keystones

end AlgebraicGeometry
