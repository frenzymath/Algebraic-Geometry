/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Albanese.Milne33RowSection

/-!
# Milne 3.3's row step needs RATIONAL POINTS, not an algebraically closed field

`Albanese/CodimOnePerfectField.lean` measures that Milne 3.1 and its neighbours
widen to a perfect base field, and that the one link of the §I.3 chain which does
**not** widen is Milne 3.3 — specifically
`Scheme.RationalMap.mem_domain_of_selfDiag_mem_domain`
(`Albanese/Milne33RowSection.lean`), whose row argument calls mathlib's
`pointOfClosedPoint`.  That construction needs the residue field at a closed
point to *be* the base field, which fails already over `ℚ`.

This file localises that obstruction one step further, and the localisation is
sharper than "the row step needs `k̄`".

## What is measured here

`mem_domain_of_selfDiag_of_sections` is the row step over an **arbitrary** field,
with `pointOfClosedPoint` replaced by explicit hypotheses supplying what it was
used for.  Reading the original proof, the closed-point construction is consumed
at exactly two places and both times only to produce a morphism
`pt : Spec k ⟶ X.left` with `pt ≫ X.hom = 𝟙` whose base map hits a prescribed
point — i.e. a **`k`-rational point of `X` at that point**.  Algebraic closure
enters only as a *supplier* of such points: over `k̄` every closed point is
`k̄`-rational, so `pointOfClosedPoint` exists at every closed point and the
Jacobson-density selection can be used unchanged.

Making that supply explicit gives two hypotheses — a rational point at `x₀`, and a
rational point in every nonempty open — under which the row argument goes through
verbatim over any field.  Note that the Jacobson-density lemma the original uses,
`exists_isClosed_singleton_mem_of_isOpen`, needs only `[Field kbar]` and
`[LocallyOfFiniteType]`; it never wanted algebraic closure either.  The whole
field dependence of the row step is the upgrade from "closed point" to "rational
point".

## What this does and does not buy

* It **does** replace "Milne 3.3 needs `[IsAlgClosed k]`" by a named, weaker
  obligation: *`X` has enough `k`-rational points* (one at the given point, and
  one in each nonempty open).  That is a statement about the curve, not about the
  field, and it is the shape the rest of this project already reasons about —
  `Scheme.HasRationalPoint`, `hasRationalPoint_of_isSepClosed`
  (`Curve/SeparablyClosedRationalPoint.lean`), and `ajc-p3`'s finite-Galois-level
  version all concern exactly this.
* It does **not** discharge anything.  The hypotheses are strictly hypotheses:
  nothing here produces them at a curve over `ℚ` or over `𝔽_q`, and over such
  fields the second one is **false in general** — a smooth curve over `ℚ` need not
  have a rational point in every nonempty open, and need not have one at all
  (protection `I-0491` turns on exactly that: the pointless real conic).  So this
  is a **reduction of the obstruction to a named input**, not a removal of it.
* Consequently it does **not** widen Milne 3.3, `extend_to_av`, or headline
  obligation 5.  What it changes is *what a lane attacking them owes*: rational
  points on the source, rather than a different proof of the row step.

**Why the reduction is still worth having.** Over `k̄` the two hypotheses are free
(that is the original theorem).  Over a general `k` they are the honest price, and
they are *localised on the source curve* rather than on the ambient field — which
means the sepclosed/finite-Galois line already in this project (`AJC.picrep.sepclosed-*`)
is the machinery that would pay them, not new geometry.  Whether that line reaches
the *every nonempty open* clause is open and is not claimed here.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry

namespace Scheme.RationalMap

variable {k : Type u} [Field k]
variable {X G : Over (Spec (.of k))}
  [Smooth X.hom] [GrpObj G] [LocallyOfFiniteType G.hom] [LocallyOfFiniteType X.hom]

set_option linter.unusedSectionVars false in
/-- **Milne 3.3's row step over an arbitrary field, from rational points.**

The `[IsAlgClosed]` version is `mem_domain_of_selfDiag_mem_domain`
(`Albanese/Milne33RowSection.lean`).  Its proof uses algebraic closure at exactly
two points, both times only to turn a *closed* point into a *`k`-rational* one via
mathlib's `pointOfClosedPoint`.  Here that supply is a hypothesis:

* `pt₀` is a `k`-rational point of `X` sitting at `x₀`;
* `hsec` supplies one in every nonempty open — the upgrade of the Jacobson-density
  selection the original performs (`exists_isClosed_singleton_mem_of_isOpen`,
  which itself needs no algebraic closure).

Everything after that is Milne's row argument unchanged: represent `f` near `x₀`
by `ψ(v) = Φ(v, u) · f(u)` on `σ_u⁻¹(Dom Φ₀)`, and check on a common dense open
that `ψ` and `f` agree.

**This is a reduction, not a discharge.**  Over `k̄` both hypotheses are free.
Over `ℚ` or `𝔽_q` they are genuine and `hsec` is false in general — a smooth curve
over a non-closed field need not have a rational point at all.  See the module
docstring.

`LocallyOfFiniteType X.hom` is retained in the signature but unused in the proof:
the original consumed it only through the Jacobson-density selection, which is
now the `hsec` hypothesis.  It is kept so the binder set matches the rest of the
Milne 3.3 cone, and the linter is silenced rather than the binder dropped. -/
theorem mem_domain_of_selfDiag_of_sections
    (f : X.left.RationalMap G.left) (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsIntegral (Limits.pullback X.hom X.hom)] [IsReduced X.left]
    [G.left.IsSeparated] [IsSeparated G.hom] [IrreducibleSpace ↥X.left]
    (x₀ : ↥X.left)
    -- a k-rational point AT x₀ (what pointOfClosedPoint supplies over k-bar)
    (pt₀ : Spec (CommRingCat.of k) ⟶ X.left)
    (hpt₀ : pt₀ ≫ X.hom = 𝟙 _)
    (hpt₀x : ∀ s, pt₀.base s = x₀)
    -- and a k-rational point in EVERY nonempty open (Jacobson density's output,
    -- upgraded from "closed point" to "rational point")
    (hsec : ∀ (O : X.left.Opens), (O : Set ↥X.left).Nonempty →
      ∃ (u : ↥X.left) (_ : u ∈ O) (ptu : Spec (CommRingCat.of k) ⟶ X.left),
        ptu ≫ X.hom = 𝟙 _ ∧ ∀ s, ptu.base s = u)
    (hδ : (AlgebraicGeometry.selfDiag X).base x₀
      ∈ (Scheme.RationalMap.differenceRationalMap f hover).toPartialMap.domain) :
    x₀ ∈ f.domain := by
  have s₀ : ↥(Spec (CommRingCat.of k)) := (default : PrimeSpectrum k)
  have hx₀A : (AlgebraicGeometry.rowFst pt₀ hpt₀).base x₀
      ∈ (Scheme.RationalMap.differenceRationalMap f hover).toPartialMap.domain := by
    have hcol := AlgebraicGeometry.selfDiag_base_eq_rowFst_base pt₀ hpt₀ s₀
    rw [hpt₀x s₀] at hcol
    rw [← hcol]
    exact hδ
  have hOne : (((AlgebraicGeometry.rowFst pt₀ hpt₀
        ⁻¹ᵁ (Scheme.RationalMap.differenceRationalMap f hover).toPartialMap.domain)
      ⊓ f.toPartialMap.domain : X.left.Opens) : Set ↥X.left).Nonempty := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact f.toPartialMap.dense_domain.inter_open_nonempty _
      (TopologicalSpace.Opens.isOpen _) ⟨x₀, hx₀A⟩
  obtain ⟨u, huO, ptu, hptu, hptux⟩ := hsec _ hOne
  have huA : (AlgebraicGeometry.rowFst pt₀ hpt₀).base u
      ∈ (Scheme.RationalMap.differenceRationalMap f hover).toPartialMap.domain := huO.1
  have huf : u ∈ f.toPartialMap.domain := huO.2
  have hx₀V : (AlgebraicGeometry.rowSnd ptu hptu).base x₀
      ∈ (Scheme.RationalMap.differenceRationalMap f hover).toPartialMap.domain := by
    have hcol := AlgebraicGeometry.rowSnd_base_eq_rowFst_base pt₀ ptu hpt₀ hptu s₀
    rw [hpt₀x s₀, hptux s₀] at hcol
    rw [hcol]
    exact huA
  set V₁ : X.left.Opens :=
    AlgebraicGeometry.rowSnd ptu hptu
      ⁻¹ᵁ (Scheme.RationalMap.differenceRationalMap f hover).toPartialMap.domain
    with hV₁def
  have hrV : Set.range (V₁.ι ≫ AlgebraicGeometry.rowSnd ptu hptu).base
      ⊆ Set.range (Scheme.RationalMap.differenceRationalMap f
          hover).toPartialMap.domain.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact t.2
  set σV := IsOpenImmersion.lift
    (Scheme.RationalMap.differenceRationalMap f hover).toPartialMap.domain.ι
    (V₁.ι ≫ AlgebraicGeometry.rowSnd ptu hptu) hrV with hσVdef
  have hσV : σV ≫ (Scheme.RationalMap.differenceRationalMap f
        hover).toPartialMap.domain.ι
      = V₁.ι ≫ AlgebraicGeometry.rowSnd ptu hptu := IsOpenImmersion.lift_fac _ _ _
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hru : Set.range ptu.base ⊆ Set.range f.toPartialMap.domain.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    rw [hptux s]
    exact huf
  set uD := IsOpenImmersion.lift f.toPartialMap.domain.ι ptu hru with huDdef
  have huD : uD ≫ f.toPartialMap.domain.ι = ptu := IsOpenImmersion.lift_fac _ _ _
  -- §4. Over-`k̄` structure of the two legs of `ψ`.
  have hΦG : (σV ≫ (Scheme.RationalMap.differenceRationalMap f hover).toPartialMap.hom) ≫ G.hom
      = V₁.ι ≫ X.hom := by
    rw [Category.assoc, Scheme.RationalMap.diff_toPartialMap_hom_comp_hom f hover, ← Category.assoc,
      hσV, Category.assoc,
      ← Category.assoc (rowSnd ptu hptu) (pullback.fst X.hom X.hom) X.hom,
      rowSnd_fst, Category.id_comp]
  have hcG : (V₁.ι ≫ X.hom ≫ uD ≫ f.toPartialMap.hom) ≫ G.hom
      = V₁.ι ≫ X.hom := by
    rw [Category.assoc, Category.assoc, Category.assoc,
      Scheme.RationalMap.toPartialMap_hom_comp_hom f hover,
      ← Category.assoc uD f.toPartialMap.domain.ι X.hom, huD, hptu,
      Category.comp_id]
  -- §5. Milne's row section `ψ := μ ∘ ⟨Φ ∘ σ_u, f(u)⟩` as a partial map on `V₁`.
  set ψ : (↑V₁ : Scheme.{u}) ⟶ G.left :=
    pullback.lift (σV ≫ (Scheme.RationalMap.differenceRationalMap f hover).toPartialMap.hom)
      (V₁.ι ≫ X.hom ≫ uD ≫ f.toPartialMap.hom) (hΦG.trans hcG.symm)
      ≫ AlgebraicGeometry.grpObjMulLeft G with hψdef
  have hV₁dense : Dense ((V₁ : X.left.Opens) : Set ↥X.left) :=
    V₁.isOpen.dense ⟨x₀, hx₀V⟩
  set ψP : X.left.PartialMap G.left := ⟨V₁, hV₁dense, ψ⟩ with hψPdef
  -- §6. The common dense open `W := V₁ ⊓ Dom f₀` and its coordinates.
  set W : X.left.Opens := V₁ ⊓ f.toPartialMap.domain with hWdef
  have hle1 : W ≤ V₁ := inf_le_left
  have hle2 : W ≤ f.toPartialMap.domain := inf_le_right
  have hWdense : Dense ((W : X.left.Opens) : Set ↥X.left) := by
    rw [hWdef, TopologicalSpace.Opens.coe_inf]
    exact hV₁dense.inter_of_isOpen_left f.toPartialMap.dense_domain V₁.isOpen
  set aD : (↑W : Scheme.{u}) ⟶ (↑f.toPartialMap.domain : Scheme.{u}) :=
    X.left.homOfLE hle2 with haDdef
  set bD : (↑W : Scheme.{u}) ⟶ (↑f.toPartialMap.domain : Scheme.{u}) :=
    W.ι ≫ X.hom ≫ uD with hbDdef
  have hwc : (aD ≫ f.toPartialMap.domain.ι) ≫ X.hom
      = (bD ≫ f.toPartialMap.domain.ι) ≫ X.hom := by
    rw [haDdef, Scheme.homOfLE_ι, hbDdef, Category.assoc, Category.assoc,
      Category.assoc, ← Category.assoc uD f.toPartialMap.domain.ι X.hom, huD,
      hptu, Category.comp_id]
  -- §7. `W`'s inclusion into `Dom Φ₀` is the pair `⟨incl, u⟩`.
  set j := X.left.homOfLE hle1 ≫ σV with hjdef
  have hjι : j ≫ (Scheme.RationalMap.differenceRationalMap f hover).toPartialMap.domain.ι
      = W.ι ≫ rowSnd ptu hptu := by
    rw [hjdef, Category.assoc, hσV, ← Category.assoc, Scheme.homOfLE_ι]
  have hj : j ≫ (Scheme.RationalMap.differenceRationalMap f hover).toPartialMap.domain.ι
      = pullback.lift (aD ≫ f.toPartialMap.domain.ι)
          (bD ≫ f.toPartialMap.domain.ι) hwc := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hjι, Category.assoc, rowSnd_fst, Category.comp_id,
        haDdef, Scheme.homOfLE_ι]
    · rw [pullback.lift_snd, hjι, Category.assoc, rowSnd_snd, hbDdef,
        Category.assoc, Category.assoc, huD]
  -- §8. The evaluation formula on `W`: `Φ₀(v, u) = f(v)·f(u)⁻¹`.
  have heval := Scheme.RationalMap.comp_toPartialMap_hom_eq_diff f hover aD bD hwc j hj
  have hA : (aD ≫ f.toPartialMap.hom) ≫ G.hom = W.ι ≫ X.hom := by
    rw [Category.assoc, Scheme.RationalMap.toPartialMap_hom_comp_hom f hover,
      ← Category.assoc, haDdef, Scheme.homOfLE_ι]
  have hB : (bD ≫ f.toPartialMap.hom) ≫ G.hom = W.ι ≫ X.hom := by
    rw [Category.assoc, Scheme.RationalMap.toPartialMap_hom_comp_hom f hover, hbDdef,
      Category.assoc, Category.assoc,
      ← Category.assoc uD f.toPartialMap.domain.ι X.hom, huD, hptu,
      Category.comp_id]
  -- §9. On `W`, the row section collapses to `f`: `(f(v)·f(u)⁻¹)·f(u) = f(v)`.
  have hagree : X.left.homOfLE hle1 ≫ ψ
      = X.left.homOfLE hle2 ≫ f.toPartialMap.hom := by
    have hlc : X.left.homOfLE hle1 ≫ pullback.lift
        (σV ≫ (Scheme.RationalMap.differenceRationalMap f hover).toPartialMap.hom)
        (V₁.ι ≫ X.hom ≫ uD ≫ f.toPartialMap.hom) (hΦG.trans hcG.symm)
        = pullback.lift
            (pullback.lift (aD ≫ f.toPartialMap.hom) (bD ≫ f.toPartialMap.hom)
                (hA.trans hB.symm)
              ≫ AlgebraicGeometry.grpObjDiffLeft G)
            (bD ≫ f.toPartialMap.hom)
            (by rw [Category.assoc, AlgebraicGeometry.grpObjDiffLeft_comp_hom, ← Category.assoc,
              pullback.lift_fst, hA, hB]) := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst,
          ← Category.assoc, ← hjdef, heval]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd,
          ← Category.assoc, Scheme.homOfLE_ι, hbDdef, Category.assoc,
          Category.assoc]
    rw [hψdef, ← Category.assoc, hlc,
      AlgebraicGeometry.pullback_lift_diff_lift_mul G (W.ι ≫ X.hom) (aD ≫ f.toPartialMap.hom)
        (bD ≫ f.toPartialMap.hom) hA hB, haDdef]
  -- §10. `ψ` represents `f`, hence `x₀ ∈ V₁ ≤ Dom f`.
  have hψf : ψP.toRationalMap = f := by
    refine (Scheme.PartialMap.toRationalMap_eq_iff.mpr ?_).trans
      f.toRationalMap_toPartialMap
    refine ⟨W, hWdense, hle1, hle2, ?_⟩
    simp only [Scheme.PartialMap.restrict_hom]
    exact hagree
  have hmem : x₀ ∈ ψP.toRationalMap.domain :=
    Scheme.PartialMap.le_domain_toRationalMap ψP hx₀V
  rw [hψf] at hmem
  exact hmem

end Scheme.RationalMap

end AlgebraicGeometry
