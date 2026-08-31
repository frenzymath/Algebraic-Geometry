/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Albanese.Milne33Diagonal

/-!
# Milne Lemma 3.3, Substep 2 (hard direction): the row section

Per `informal/m33-spec.md` (D3), at closed rational points. Main result:

* `mem_domain_of_selfDiag_mem_domain` — if `x₀` is a closed point of the
  smooth irreducible variety `X` over `k̄ = k̄` and Milne's difference map
  `Φ(x, y) = f(x)·f(y)⁻¹` is defined at the diagonal point `(x₀, x₀)`, then
  `f` itself is defined at `x₀`.

Milne's row argument `f(x) = Φ(x, u)·f(u)`: by Jacobson density and
irreducibility there is a closed (hence `k̄`-rational, `pointOfClosedPoint`)
point `u ∈ Dom f` with `(x₀, u) ∈ Dom Φ`; the honest morphism
`ψ(v) := Φ(v, u)·f(u)` is defined on the open `V₁ := σ_u⁻¹(Dom Φ₀) ∋ x₀`
(where `σ_u(v) = (v, u)` is the row through `u`) and agrees with `f` on
`V₁ ⊓ Dom f` by the evaluation formula (`comp_toPartialMap_hom_eq_diff`) and
the scheme-level group identity `(a·b⁻¹)·b = a`
(`pullback_lift_diff_lift_mul`). Hence `ψ` represents `f` and
`x₀ ∈ V₁ ≤ Dom f`. No fppf descent and no UFD input (spec D1/D3).

Also here: `exists_isClosed_singleton_mem_of_isOpen`, the Jacobson density of
closed points in a scheme locally of finite type over a field (spec R5).

Blueprint reference: `lem:milne_codim1_indeterminacy` (Milne, *Abelian
Varieties*, §I.3 Lemma 3.3, p. 17; `abelian-varieties:page-0023`).
-/

set_option autoImplicit false

universe u

open CategoryTheory CartesianMonoidalCategory MonoidalCategory Limits TopologicalSpace

namespace AlgebraicGeometry

variable {kbar : Type u} [Field kbar]

/-- **Jacobson density of closed points.** Every nonempty open subset of a
scheme locally of finite type over a field contains a closed point. -/
lemma exists_isClosed_singleton_mem_of_isOpen {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of kbar)) [LocallyOfFiniteType g]
    {O : Set ↥Z} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ u ∈ O, IsClosed ({u} : Set ↥Z) := by
  have hJ : JacobsonSpace ↥Z := LocallyOfFiniteType.jacobsonSpace g
  by_contra hc
  push Not at hc
  have hemp : O ∩ closedPoints ↥Z = ∅ := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun h1 h2 => hc v h1 h2
  have h := JacobsonSpace.closure_inter_closedPoints_eq_closure (X := ↥Z)
    hO.isLocallyClosed
  rw [hemp, closure_empty] at h
  obtain ⟨x, hx⟩ := hne
  have hx' : x ∈ closure O := subset_closure hx
  rw [← h] at hx'
  simp at hx'

namespace Scheme.RationalMap

variable [IsAlgClosed kbar]
variable {X G : Over (Spec (.of kbar))}
  [Smooth X.hom] [GrpObj G] [LocallyOfFiniteType G.hom] [LocallyOfFiniteType X.hom]

/-- **Milne Lemma 3.3, Substep 2, hard direction (at closed points).** If the
difference map `Φ(x, y) = f(x)·f(y)⁻¹` of a rational map `f : X ⇢ G` over
`k̄ = k̄` is defined at the diagonal point `(x₀, x₀)` of a *closed* point `x₀`
of the smooth irreducible variety `X`, then `f` is defined at `x₀`.

Milne's row argument: choose a closed rational point `u ∈ Dom f` with
`(x₀, u) ∈ Dom Φ` (Jacobson density in the row through `x₀`), and represent
`f` near `x₀` by the honest morphism `ψ(v) := Φ(v, u)·f(u)` on
`σ_u⁻¹(Dom Φ₀) ∋ x₀` (Milne, *Abelian Varieties*, §I.3 p. 17). -/
theorem mem_domain_of_selfDiag_mem_domain
    (f : X.left.RationalMap G.left) (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsIntegral (pullback X.hom X.hom)] [IsReduced X.left] [G.left.IsSeparated]
    [IsSeparated G.hom] [IrreducibleSpace ↥X.left]
    (x₀ : ↥X.left) (hx₀ : IsClosed ({x₀} : Set ↥X.left))
    (hδ : (selfDiag X).base x₀
      ∈ (differenceRationalMap f hover).toPartialMap.domain) :
    x₀ ∈ f.domain := by
  -- §0. The `k̄`-point at `x₀`.
  have s₀ : ↥(Spec (CommRingCat.of kbar)) := (default : PrimeSpectrum kbar)
  set pt₀ := pointOfClosedPoint X.hom x₀ hx₀ with hpt₀def
  have hpt₀ : pt₀ ≫ X.hom = 𝟙 _ := pointOfClosedPoint_comp X.hom x₀ hx₀
  have hpt₀x : pt₀.base s₀ = x₀ := pointOfClosedPoint_apply X.hom x₀ hx₀ s₀
  -- §1. The row through `x₀` meets `Dom Φ₀` at `(x₀, x₀)`.
  have hx₀A : (rowFst pt₀ hpt₀).base x₀
      ∈ (differenceRationalMap f hover).toPartialMap.domain := by
    have hcol := selfDiag_base_eq_rowFst_base pt₀ hpt₀ s₀
    rw [hpt₀x] at hcol
    rw [← hcol]
    exact hδ
  -- §2. A closed point `u` in the nonempty open `τ_{x₀}⁻¹(Dom Φ₀) ⊓ Dom f`.
  have hOne : (((rowFst pt₀ hpt₀
        ⁻¹ᵁ (differenceRationalMap f hover).toPartialMap.domain)
      ⊓ f.toPartialMap.domain : X.left.Opens) : Set ↥X.left).Nonempty := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact f.toPartialMap.dense_domain.inter_open_nonempty _
      (TopologicalSpace.Opens.isOpen _) ⟨x₀, hx₀A⟩
  obtain ⟨u, huO, hu⟩ := exists_isClosed_singleton_mem_of_isOpen X.hom
    (TopologicalSpace.Opens.isOpen _) hOne
  have huA : (rowFst pt₀ hpt₀).base u
      ∈ (differenceRationalMap f hover).toPartialMap.domain := huO.1
  have huf : u ∈ f.toPartialMap.domain := huO.2
  set ptu := pointOfClosedPoint X.hom u hu with hptudef
  have hptu : ptu ≫ X.hom = 𝟙 _ := pointOfClosedPoint_comp X.hom u hu
  have hptux : ptu.base s₀ = u := pointOfClosedPoint_apply X.hom u hu s₀
  -- §3. The row through `u`: `σ_u(v) = (v, u)`, with `x₀ ∈ V₁ := σ_u⁻¹(Dom Φ₀)`.
  have hx₀V : (rowSnd ptu hptu).base x₀
      ∈ (differenceRationalMap f hover).toPartialMap.domain := by
    have hcol := rowSnd_base_eq_rowFst_base pt₀ ptu hpt₀ hptu s₀
    rw [hpt₀x, hptux] at hcol
    rw [hcol]
    exact huA
  set V₁ : X.left.Opens :=
    rowSnd ptu hptu ⁻¹ᵁ (differenceRationalMap f hover).toPartialMap.domain
    with hV₁def
  -- The section of `Dom Φ₀` over `V₁`.
  have hrV : Set.range (V₁.ι ≫ rowSnd ptu hptu).base
      ⊆ Set.range (differenceRationalMap f hover).toPartialMap.domain.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact t.2
  set σV := IsOpenImmersion.lift
    (differenceRationalMap f hover).toPartialMap.domain.ι
    (V₁.ι ≫ rowSnd ptu hptu) hrV with hσVdef
  have hσV : σV ≫ (differenceRationalMap f hover).toPartialMap.domain.ι
      = V₁.ι ≫ rowSnd ptu hptu := IsOpenImmersion.lift_fac _ _ _
  -- The `k̄`-point `u` factored through `Dom f`.
  haveI : Subsingleton ↥(Spec (CommRingCat.of kbar)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum kbar))
  have hru : Set.range ptu.base ⊆ Set.range f.toPartialMap.domain.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    rw [Subsingleton.elim s s₀, hptux]
    exact huf
  set uD := IsOpenImmersion.lift f.toPartialMap.domain.ι ptu hru with huDdef
  have huD : uD ≫ f.toPartialMap.domain.ι = ptu := IsOpenImmersion.lift_fac _ _ _
  -- §4. Over-`k̄` structure of the two legs of `ψ`.
  have hΦG : (σV ≫ (differenceRationalMap f hover).toPartialMap.hom) ≫ G.hom
      = V₁.ι ≫ X.hom := by
    rw [Category.assoc, diff_toPartialMap_hom_comp_hom f hover, ← Category.assoc,
      hσV, Category.assoc,
      ← Category.assoc (rowSnd ptu hptu) (pullback.fst X.hom X.hom) X.hom,
      rowSnd_fst, Category.id_comp]
  have hcG : (V₁.ι ≫ X.hom ≫ uD ≫ f.toPartialMap.hom) ≫ G.hom
      = V₁.ι ≫ X.hom := by
    rw [Category.assoc, Category.assoc, Category.assoc,
      toPartialMap_hom_comp_hom f hover,
      ← Category.assoc uD f.toPartialMap.domain.ι X.hom, huD, hptu,
      Category.comp_id]
  -- §5. Milne's row section `ψ := μ ∘ ⟨Φ ∘ σ_u, f(u)⟩` as a partial map on `V₁`.
  set ψ : (↑V₁ : Scheme.{u}) ⟶ G.left :=
    pullback.lift (σV ≫ (differenceRationalMap f hover).toPartialMap.hom)
      (V₁.ι ≫ X.hom ≫ uD ≫ f.toPartialMap.hom) (hΦG.trans hcG.symm)
      ≫ grpObjMulLeft G with hψdef
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
  have hjι : j ≫ (differenceRationalMap f hover).toPartialMap.domain.ι
      = W.ι ≫ rowSnd ptu hptu := by
    rw [hjdef, Category.assoc, hσV, ← Category.assoc, Scheme.homOfLE_ι]
  have hj : j ≫ (differenceRationalMap f hover).toPartialMap.domain.ι
      = pullback.lift (aD ≫ f.toPartialMap.domain.ι)
          (bD ≫ f.toPartialMap.domain.ι) hwc := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hjι, Category.assoc, rowSnd_fst, Category.comp_id,
        haDdef, Scheme.homOfLE_ι]
    · rw [pullback.lift_snd, hjι, Category.assoc, rowSnd_snd, hbDdef,
        Category.assoc, Category.assoc, huD]
  -- §8. The evaluation formula on `W`: `Φ₀(v, u) = f(v)·f(u)⁻¹`.
  have heval := comp_toPartialMap_hom_eq_diff f hover aD bD hwc j hj
  have hA : (aD ≫ f.toPartialMap.hom) ≫ G.hom = W.ι ≫ X.hom := by
    rw [Category.assoc, toPartialMap_hom_comp_hom f hover,
      ← Category.assoc, haDdef, Scheme.homOfLE_ι]
  have hB : (bD ≫ f.toPartialMap.hom) ≫ G.hom = W.ι ≫ X.hom := by
    rw [Category.assoc, toPartialMap_hom_comp_hom f hover, hbDdef,
      Category.assoc, Category.assoc,
      ← Category.assoc uD f.toPartialMap.domain.ι X.hom, huD, hptu,
      Category.comp_id]
  -- §9. On `W`, the row section collapses to `f`: `(f(v)·f(u)⁻¹)·f(u) = f(v)`.
  have hagree : X.left.homOfLE hle1 ≫ ψ
      = X.left.homOfLE hle2 ≫ f.toPartialMap.hom := by
    have hlc : X.left.homOfLE hle1 ≫ pullback.lift
        (σV ≫ (differenceRationalMap f hover).toPartialMap.hom)
        (V₁.ι ≫ X.hom ≫ uD ≫ f.toPartialMap.hom) (hΦG.trans hcG.symm)
        = pullback.lift
            (pullback.lift (aD ≫ f.toPartialMap.hom) (bD ≫ f.toPartialMap.hom)
                (hA.trans hB.symm)
              ≫ grpObjDiffLeft G)
            (bD ≫ f.toPartialMap.hom)
            (by rw [Category.assoc, grpObjDiffLeft_comp_hom, ← Category.assoc,
              pullback.lift_fst, hA, hB]) := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst,
          ← Category.assoc, ← hjdef, heval]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd,
          ← Category.assoc, Scheme.homOfLE_ι, hbDdef, Category.assoc,
          Category.assoc]
    rw [hψdef, ← Category.assoc, hlc,
      pullback_lift_diff_lift_mul G (W.ι ≫ X.hom) (aD ≫ f.toPartialMap.hom)
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
