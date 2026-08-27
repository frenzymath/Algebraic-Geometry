/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Noetherian
import AlgebraicJacobian.Albanese.Milne33Transport

/-!
# Milne Lemma 3.3: the indeterminacy locus of a rational map into a group
variety is empty or pure of codimension one

The keystone of the Milne-3.3 campaign (spec `informal/m33-spec.md`, D6):

* `AlgebraicGeometry.Scheme.RationalMap.indeterminacy_pure_codim_one_into_grpScheme`
  — for a rational map `f : X ⇢ G` over `k̄` from a smooth
  geometrically-irreducible variety to a group variety, compatible with the
  structure maps, the disjunction `Milne33Indeterminacy f` holds: the
  indeterminacy locus `Z(f)` is empty, or every `x ∈ Z(f)` lies in the closure
  of a point `z ∈ Z(f)` of coheight one.

This discharges the D2 hypothesis of `informal/w6-port-worksheet.md`: the
Theorem-3.2 extension chain (`Albanese/Thm32RationalMapExtension.lean`)
threads `Milne33Indeterminacy f` as an explicit hypothesis, and this theorem
supplies it.

## Route (D6 component reduction)

Fix `x ∈ Z(f)`. Choose an affine (hence topologically Noetherian) open window
`W ∋ x` and let `Z₀ := Z(f) ∩ W`, a closed subset of `W` with finitely many
irreducible components. Let `C` be the component of `x` and pick — by Jacobson
density of ambient-closed points in nonempty locally closed subsets
(`exists_isClosed_singleton_mem_of_isLocallyClosed`) — a point `x₀ ∈ C` closed
in `X` and avoiding all other components. The 4b-transport
(`exists_notMem_domain_specializes_coheight_eq_one`, spec D5) yields
`z ∈ Z(f)` with `z ⤳ x₀` and `coheight z = 1`. The closure of `z` in `W` is
an irreducible subset of `Z₀` through `x₀`, so it lies in a component — which
must be `C`, as `x₀` avoids the others. Hence the generic point `ζ` of `C`
generises `z`; since `ζ ∈ Z(f)` is not the generic point of `X` (which is in
`dom f`), `coheight ζ ≥ 1`, and coheight strictness along `ζ ⤳ z` forces
`ζ = z`. Therefore `x ∈ C ⊆ closure {z}`, as required.

Blueprint reference: `lem:milne_codim1_indeterminacy` (Milne, *Abelian
Varieties*, §I.3 Lemma 3.3, pp. 17–18; `abelian-varieties:page-0023/0024`).
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace IsLocalRing

namespace AlgebraicGeometry

namespace Scheme.RationalMap

variable {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
variable {X G : Over (Spec (.of kbar))}
  [Smooth X.hom] [GrpObj G] [LocallyOfFiniteType G.hom] [LocallyOfFiniteType X.hom]

/-- **Milne Lemma 3.3** (Milne, *Abelian Varieties*, §I.3, pp. 17–18). For a
rational map `f : X ⇢ G` over `k̄` from a smooth geometrically-irreducible
variety to a group variety, compatible with the structure maps, the
indeterminacy locus is empty or pure of codimension one.

This is the **proof core**, stated with the explicit `IrreducibleSpace ↥X.left`
and `G.left.IsSeparated` binders that the component-reduction argument uses
directly. The consumer-facing form, whose binder set matches the rest of the
Milne §I.3 chain in `Albanese/CodimOneExtension.lean`, is
`indeterminacy_pure_codim_one_into_grpScheme` below; it derives those two
instances and delegates here.

Route: fix `x ∈ Z(f)`, take a Noetherian affine window `W ∋ x`, let `C` be the
irreducible component of `x` in `Z(f) ∩ W`, Jacobson-select an ambient-closed
`x₀ ∈ C` avoiding the other components, apply the 4b-transport
(`exists_notMem_domain_specializes_coheight_eq_one`) at `x₀` to get
`z ∈ Z(f)` with `z ⤳ x₀` and `coheight z = 1`, then identify `z` with the
generic point of `C` by coheight strictness. -/
theorem indeterminacy_pure_codim_one_into_grpScheme_core
    (f : X.left.RationalMap G.left) (hover : f.compHom G.hom = X.hom.toRationalMap)
    [GeometricallyIrreducible X.hom] [IsSeparated X.hom]
    [IsIntegral X.left] [IsReduced X.left] [IrreducibleSpace ↥X.left]
    [G.left.IsSeparated] [IsSeparated G.hom] :
    indeterminacyLocus f = ∅ ∨
      ∀ x ∈ indeterminacyLocus f,
        ∃ z ∈ indeterminacyLocus f,
          Order.coheight z = 1 ∧ x ∈ closure ({z} : Set X.left) := by
  rcases eq_or_ne (indeterminacyLocus f) ∅ with hemp | hne
  · exact Or.inl hemp
  refine Or.inr fun x hx => ?_
  -- `Z(f)` is closed; the generic point of `X` is in the domain.
  have hZclosed : IsClosed (indeterminacyLocus f) := f.domain.2.isClosed_compl
  have hηX : genericPoint ↥X.left ∈ f.toPartialMap.domain :=
    (genericPoint_specializes _).mem_open f.toPartialMap.domain.2
      f.toPartialMap.dense_domain.nonempty.choose_spec
  -- §a. The Noetherian affine window `W ∋ x`.
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.left.Opens) from trivial)
  haveI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  haveI : IsNoetherianRing Γ(X.left, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  haveI : NoetherianSpace ↥W := noetherianSpace_of_isAffineOpen W hW
  haveI : QuasiSober ↥W := W.2.isOpenEmbedding_subtypeVal.quasiSober
  -- §b. The trace of `Z(f)` on the window and its components.
  set Z₀ : Set ↥W := Subtype.val ⁻¹' indeterminacyLocus f with hZ₀def
  have hZ₀closed : IsClosed Z₀ := hZclosed.preimage continuous_subtype_val
  have hvalZ : Topology.IsClosedEmbedding (Subtype.val : Z₀ → ↥W) :=
    hZ₀closed.isClosedEmbedding_subtypeVal
  set xW : ↥W := ⟨x, hxW⟩ with hxWdef
  have hxZ₀ : xW ∈ Z₀ := hx
  set xZ : Z₀ := ⟨xW, hxZ₀⟩ with hxZdef
  set C' : Set Z₀ := _root_.irreducibleComponent xZ with hC'def
  set others : Set (Set Z₀) := _root_.irreducibleComponents ↥Z₀ \ {C'} with hothersdef
  have hothersfin : others.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset Set.sdiff_subset
  -- §c. The component and the union of the others, as subsets of the window.
  set Cw : Set ↥W := Subtype.val '' C' with hCwdef
  have hCwirr : IsIrreducible Cw :=
    isIrreducible_irreducibleComponent.image _ continuous_subtype_val.continuousOn
  have hCwclosed : IsClosed Cw := hvalZ.isClosedMap _ isClosed_irreducibleComponent
  have hCwZ₀ : Cw ⊆ Z₀ := by
    rintro - ⟨c, -, rfl⟩
    exact c.2
  set Ow : Set ↥W := ⋃ T ∈ others, Subtype.val '' T with hOwdef
  have hOwclosed : IsClosed Ow :=
    Set.Finite.isClosed_biUnion hothersfin fun T hT =>
      hvalZ.isClosedMap _ (isClosed_of_mem_irreducibleComponents T hT.1)
  -- §d. The component is not covered by the others.
  have hCnotsub : ¬ Cw ⊆ Ow := by
    intro hsub
    have hsub' : C' ⊆ ⋃ T ∈ others, T := by
      intro c hc
      have hmem : (c : ↥W) ∈ Ow := hsub ⟨c, hc, rfl⟩
      simp only [hOwdef, Set.mem_iUnion] at hmem
      obtain ⟨T, hT, c₂, hc₂T, hc₂val⟩ := hmem
      exact Set.mem_biUnion hT (Subtype.val_injective hc₂val ▸ hc₂T)
    obtain ⟨T, hTmem, hCT⟩ :=
      (isIrreducible_iff_sUnion_isClosed.mp isIrreducible_irreducibleComponent)
        hothersfin.toFinset
        (fun T hT =>
          isClosed_of_mem_irreducibleComponents T (hothersfin.mem_toFinset.mp hT).1)
        (by rwa [Set.Finite.coe_toFinset, Set.sUnion_eq_biUnion])
    have hT' : T ∈ others := hothersfin.mem_toFinset.mp hTmem
    have hTC : T = C' :=
      le_antisymm
        ((irreducibleComponent_mem_irreducibleComponents xZ).2 hT'.1.1 hCT) hCT
    exact hT'.2 hTC
  -- §e. Jacobson selection of an ambient-closed `x₀ ∈ C ∖ (others)`.
  have hSlc : IsLocallyClosed (Subtype.val '' (Cw \ Ow) : Set ↥X.left) := by
    have h1 : IsLocallyClosed (Cw \ Ow) := by
      rw [Set.sdiff_eq]
      exact hCwclosed.isLocallyClosed.inter hOwclosed.isOpen_compl.isLocallyClosed
    exact h1.image W.2.isOpenEmbedding_subtypeVal.toIsInducing
      W.2.isOpenEmbedding_subtypeVal.isOpen_range.isLocallyClosed
  have hSne : (Subtype.val '' (Cw \ Ow) : Set ↥X.left).Nonempty := by
    obtain ⟨w', hw'C, hw'O⟩ := Set.not_subset.mp hCnotsub
    exact ⟨w', ⟨w', ⟨hw'C, hw'O⟩, rfl⟩⟩
  obtain ⟨x₀, hx₀S, hx₀closed⟩ :=
    exists_isClosed_singleton_mem_of_isLocallyClosed X.hom hSlc hSne
  obtain ⟨x₀', hx₀'CO, hx₀'val⟩ := hx₀S
  have hx₀'Z₀ : x₀' ∈ Z₀ := hCwZ₀ hx₀'CO.1
  have hx₀f : x₀ ∉ f.domain := by
    have : (x₀' : ↥X.left) ∈ indeterminacyLocus f := hx₀'Z₀
    rwa [hx₀'val] at this
  -- §f. The 4b-transport at `x₀`.
  obtain ⟨z, hzf, hzx₀, hzcoh⟩ :=
    exists_notMem_domain_specializes_coheight_eq_one f hover x₀ hx₀closed hx₀f
  -- §g. `z` in the window, and its closure lands in the component `C`.
  have hx₀W : x₀ ∈ W := hx₀'val ▸ x₀'.2
  have hzW : z ∈ W := hzx₀.mem_open W.2 hx₀W
  set zW : ↥W := ⟨z, hzW⟩ with hzWdef
  have hz'x₀' : zW ⤳ x₀' := by
    refine W.2.isOpenEmbedding_subtypeVal.toIsInducing.specializes_iff.mp ?_
    change z ⤳ (x₀' : ↥X.left)
    rw [hx₀'val]
    exact hzx₀
  have hz'Z₀ : zW ∈ Z₀ := hzf
  set zZ : Z₀ := ⟨zW, hz'Z₀⟩ with hzZdef
  set x₀Z : Z₀ := ⟨x₀', hx₀'Z₀⟩ with hx₀Zdef
  have hz''x₀'' : zZ ⤳ x₀Z := hvalZ.toIsInducing.specializes_iff.mp hz'x₀'
  obtain ⟨C₁, hC₁mem, hTC₁⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure {zZ}) isIrreducible_singleton.closure
  have hC₁eq : C₁ = C' := by
    by_contra hneq
    have hx₀''T : x₀Z ∈ closure {zZ} := specializes_iff_mem_closure.mp hz''x₀''
    exact hx₀'CO.2 (Set.mem_biUnion ⟨hC₁mem, hneq⟩ ⟨_, hTC₁ hx₀''T, rfl⟩)
  -- §h. The generic point `ζ` of `C` generises `z` and every point of `C`.
  have hgen : IsGenericPoint hCwirr.genericPoint Cw := by
    have h := hCwirr.isGenericPoint_genericPoint_closure
    rwa [hCwclosed.closure_eq] at h
  have hzCw : zW ∈ Cw :=
    ⟨zZ, by rw [← hC₁eq]; exact hTC₁ (subset_closure rfl), rfl⟩
  have hζz : (hCwirr.genericPoint : ↥X.left) ⤳ z :=
    (hgen.specializes hzCw).map continuous_subtype_val
  -- §i. `ζ ∈ Z(f)` forces `coheight ζ ≥ 1`, and strictness forces `ζ = z`.
  have hζZ : (hCwirr.genericPoint : ↥X.left) ∈ indeterminacyLocus f :=
    hCwZ₀ hgen.mem
  have hζcoh : 1 ≤ Order.coheight (hCwirr.genericPoint : ↥X.left) :=
    Scheme.one_le_coheight_of_ne_genericPoint fun he => hζZ (by rw [he]; exact hηX)
  have hζeq : (hCwirr.genericPoint : ↥X.left) = z := by
    by_contra hneqz
    have hstrict := Scheme.coheight_add_one_le_of_specializes hζz hneqz
    rw [hzcoh] at hstrict
    have h11 : (1 : ℕ∞) + 1 ≤ 1 := by
      calc (1 : ℕ∞) + 1 ≤ Order.coheight (hCwirr.genericPoint : ↥X.left) + 1 := by gcongr
        _ ≤ 1 := hstrict
    exact lt_irrefl (1 : ℕ∞) ((ENat.add_one_le_iff (by simp)).mp h11)
  -- §j. Conclusion: `x ∈ C = closure {ζ} = closure {z}`.
  refine ⟨z, hzf, hzcoh, ?_⟩
  have hxCw : xW ∈ Cw := ⟨xZ, mem_irreducibleComponent, rfl⟩
  have hζx : (hCwirr.genericPoint : ↥X.left) ⤳ x :=
    (hgen.specializes hxCw).map continuous_subtype_val
  have hxcl : x ∈ closure {(hCwirr.genericPoint : ↥X.left)} :=
    specializes_iff_mem_closure.mp hζx
  rwa [hζeq] at hxcl

/-- **Milne Lemma 3.3 — indeterminacy into a group variety is empty or pure
codim 1.**

For `X` a nonsingular variety over `k̄`, `G` a group variety over `k̄`
(a smooth group scheme of finite type, separated), and `f : X ⇢ G` a
rational map over `k̄`, the indeterminacy locus `Z(f) := indeterminacyLocus f`
is either empty (`f` is defined on all of `X`) or of *pure codimension 1*,
encoded as: every point of `Z(f)` lies in the closure of a codim-1 point
*of `Z(f)` itself*. (The `z ∈ indeterminacyLocus f` conjunct is essential:
without it the disjunct is nearly vacuous — on a variety every non-generic
point specialises from *some* codim-1 point — and, in particular, too weak
to combine with the codim-≥2 conclusion of Milne 3.1 to force `Z(f) = ∅`
in Theorem 3.2.)

This is the form consumed by `av_indeterminacyLocus_eq_empty` and hence
`extend_to_av` (Milne Theorem 3.2,
`Albanese/Thm32RationalMapExtension.lean`). Its binder set is the one carried
by the rest of the Milne §I.3 chain in `Albanese/CodimOneExtension.lean`; the
two extra instances used by the proof core are derived here:
`IrreducibleSpace ↥X.left` from `IsIntegral X.left`, and scheme-level
separatedness of `G.left` from `IsSeparated G.hom` composed with the affine
`Spec k̄ ⟶ ⊤_ Scheme`.

The mathematical content is `indeterminacy_pure_codim_one_into_grpScheme_core`
above (Milne's difference-map argument, via the pole-purity and
Hauptidealsatz-transport layers of `Albanese/Milne33*.lean`).

**THIS THEOREM IS THE LOAD-BEARING `IsAlgClosed` LINK OF THE MILNE §I.3 CHAIN**
(`ajc-p4`, 2026-07-30, measured).  The binder is on the section `variable` line
above, not in this declaration's own header, so `#check` shows it but reading the
header does not — inbox `I-1115` reported this theorem as carrying no
`IsAlgClosed` in either project, and that was wrong for exactly that reason.

Restating this statement over `[PerfectField k]` and closing it by
`indeterminacy_pure_codim_one_into_grpScheme_core` **fails**, with
`failed to synthesize instance of type class IsAlgClosed k`.  The consumption
site is `mem_domain_of_selfDiag_mem_domain` (`Albanese/Milne33RowSection.lean`),
whose row argument builds a base-field point at a *closed* point of `X` via
mathlib's `pointOfClosedPoint`; that construction needs the residue field at the
closed point to **be** the base field (`residueFieldIsoBase`, through
`IsAlgClosed.ringHom_bijective_of_isIntegral`), which is false already over `ℚ`.
Only three of the twelve modules in this cone carry the binder at all — this one,
`Milne33RowSection.lean` and `Milne33Transport.lean` — and the latter two are the
closed-point layers.

By contrast Milne **3.1** and its whole chain widen to a perfect field with the
proof bodies unchanged (`Albanese/CodimOnePerfectField.lean`).  So a lane pricing
"Milne §I.3 over an arbitrary field" owes this theorem's closed-point row
argument and nothing else in the chain.

Blueprint reference: `lem:milne_codim1_indeterminacy` (Milne, *Abelian
Varieties*, Lemma 3.3, §I.3, p. 17). -/
theorem indeterminacy_pure_codim_one_into_grpScheme
    (f : X.left.RationalMap G.left) (hover : f.compHom G.hom = X.hom.toRationalMap)
    [GeometricallyIrreducible X.hom] [IsSeparated X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    [GeometricallyIrreducible G.hom] [IsSeparated G.hom]
    [IsIntegral G.left] [IsReduced G.left] :
    indeterminacyLocus f = ∅ ∨
      ∀ x ∈ indeterminacyLocus f,
        ∃ z ∈ indeterminacyLocus f,
          Order.coheight z = 1 ∧ x ∈ closure ({z} : Set X.left) := by
  -- `IsIntegral` on the source gives irreducibility of its space.
  haveI : IrreducibleSpace ↥X.left := inferInstance
  -- Scheme-level separatedness of the target: `G.hom` is separated, and
  -- `Spec k̄` is affine, hence separated over the terminal scheme.
  haveI : G.left.IsSeparated := by
    rw [Scheme.isSeparated_iff]
    have heq : terminal.from G.left = G.hom ≫ terminal.from _ :=
      Subsingleton.elim _ _
    rw [heq]; infer_instance
  exact indeterminacy_pure_codim_one_into_grpScheme_core f hover

end Scheme.RationalMap

end AlgebraicGeometry
