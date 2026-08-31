/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.FiniteInAffine
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Finite subsets of irreducible algebraic groups lie in affine opens

This file formalizes the irreducible, algebraically closed core of
[Stacks, Lemma 39.8.6](https://stacks.math.columbia.edu/tag/0B7S). Translation
turns one affine neighborhood of the identity into finitely many dense open
subsets. Irreducibility gives a common closed point, and translating back gives
one affine open containing the prescribed rational points.

The final theorem applies this argument to arbitrary finite sets of topological
points: local finite type over a field makes the scheme Jacobson, so each point
specializes to a closed point. It deliberately does not assert the remaining
arbitrary-field or reducible-component descent.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

variable {K : Type u} [Field K]

/-- Right translation by a rational point of a group scheme. -/
noncomputable def rightMul (G : Over (Spec (.of K))) [GrpObj G]
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ G) : G ⟶ G :=
  lift (𝟙 G) (toUnit G ≫ p) ≫ μ

lemma comp_rightMul {G Z : Over (Spec (.of K))} [GrpObj G]
    (x : Z ⟶ G) (p : 𝟙_ (Over (Spec (.of K))) ⟶ G) :
    x ≫ rightMul G p = x * (toUnit Z ≫ p) := by
  rw [rightMul, ← Category.assoc, comp_lift, Category.comp_id, comp_toUnit_assoc,
    CategoryTheory.Hom.mul_def]

/-- Right translation is inverted by translation by the inverse point. -/
noncomputable def rightMulIso (G : Over (Spec (.of K))) [GrpObj G]
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ G) : G ≅ G where
  hom := rightMul G p
  inv := rightMul G (p ≫ ι)
  hom_inv_id := by
    rw [comp_rightMul, rightMul, ← CategoryTheory.Hom.mul_def]
    change ((𝟙 G) * (toUnit G ≫ p)) * (toUnit G ≫ p)⁻¹ = 𝟙 G
    simp
  inv_hom_id := by
    rw [comp_rightMul, rightMul, ← CategoryTheory.Hom.mul_def]
    change ((𝟙 G) * (toUnit G ≫ p)⁻¹) * (toUnit G ≫ p) = 𝟙 G
    simp

/-- Left translation by a rational point of a group scheme. -/
noncomputable def leftMul (G : Over (Spec (.of K))) [GrpObj G]
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ G) : G ⟶ G :=
  lift (toUnit G ≫ p) (𝟙 G) ≫ μ

lemma comp_leftMul {G Z : Over (Spec (.of K))} [GrpObj G]
    (x : Z ⟶ G) (p : 𝟙_ (Over (Spec (.of K))) ⟶ G) :
    x ≫ leftMul G p = (toUnit Z ≫ p) * x := by
  rw [leftMul, ← Category.assoc, comp_lift, Category.comp_id, comp_toUnit_assoc,
    CategoryTheory.Hom.mul_def]

/-- Left translation is inverted by translation by the inverse point. -/
noncomputable def leftMulIso (G : Over (Spec (.of K))) [GrpObj G]
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ G) : G ≅ G where
  hom := leftMul G p
  inv := leftMul G (p ≫ ι)
  hom_inv_id := by
    rw [comp_leftMul, leftMul, ← CategoryTheory.Hom.mul_def]
    change (toUnit G ≫ p)⁻¹ * ((toUnit G ≫ p) * (𝟙 G)) = 𝟙 G
    simp
  inv_hom_id := by
    rw [comp_leftMul, leftMul, ← CategoryTheory.Hom.mul_def]
    change (toUnit G ≫ p) * ((toUnit G ≫ p)⁻¹ * (𝟙 G)) = 𝟙 G
    simp

lemma point_comp_rightMul_eq_point_comp_leftMul
    (G : Over (Spec (.of K))) [GrpObj G]
    (p q : 𝟙_ (Over (Spec (.of K))) ⟶ G) :
    p ≫ rightMul G q = q ≫ leftMul G p := by
  rw [comp_rightMul, comp_leftMul]
  simp

/-- A connected space with irreducible open neighborhoods is irreducible. -/
private lemma irreducibleSpace_of_connectedSpace_of_nhds
    {α : Type*} [TopologicalSpace α] [ConnectedSpace α]
    (h : ∀ x : α, ∃ V : Set α, IsOpen V ∧ x ∈ V ∧ IsIrreducible V) :
    IrreducibleSpace α := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty α)
  have hZmem : Maximal IsIrreducible (irreducibleComponent x₀) :=
    irreducibleComponent_mem_irreducibleComponents x₀
  have hZopen : IsOpen (irreducibleComponent x₀) := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨V, hVopen, hzV, hVirr⟩ := h z
    have h₁ : irreducibleComponent x₀ ⊆ closure V :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen hZmem.prop.2 hVopen
        ⟨z, hz, hzV⟩).trans (closure_mono Set.inter_subset_right)
    have h₂ : closure V = irreducibleComponent x₀ :=
      hZmem.eq_of_superset hVirr.closure h₁
    exact mem_nhds_iff.mpr ⟨V, h₂ ▸ subset_closure, hVopen, hzV⟩
  have hZuniv : irreducibleComponent x₀ = Set.univ :=
    (isClopen_iff.mp ⟨isClosed_irreducibleComponent, hZopen⟩).resolve_left
      (Set.Nonempty.ne_empty ⟨x₀, mem_irreducibleComponent⟩)
  haveI : PreirreducibleSpace α := ⟨hZuniv ▸ hZmem.prop.2⟩
  exact ⟨⟨x₀⟩⟩

/-- A locally algebraic group has a nonempty irreducible open subset. -/
private lemma exists_isOpen_nonempty_isIrreducible
    (G : Over (Spec (.of K))) [GrpObj G] [LocallyOfFiniteType G.hom] :
    ∃ U : Set G.left, IsOpen U ∧ U.Nonempty ∧ IsIrreducible U := by
  haveI : IsLocallyNoetherian G.left :=
    LocallyOfFiniteType.isLocallyNoetherian G.hom
  let e : G.left := η[G].left (IsLocalRing.closedPoint K)
  obtain ⟨W, hW, heW, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := G.left) (U := ⊤) (TopologicalSpace.Opens.mem_top e)
  haveI : IsNoetherianRing Γ(G.left, W) :=
    IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hNW : TopologicalSpace.NoetherianSpace ↑W :=
    noetherianSpace_of_isAffineOpen W hW
  obtain ⟨o, hoOpen, hoNe, hoZ⟩ :=
    @TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (↑W) _ hNW
      (irreducibleComponent (⟨e, heW⟩ : ↑W))
      (irreducibleComponent_mem_irreducibleComponents _)
  have hoIrr : IsIrreducible o :=
    ⟨hoNe, (isIrreducible_irreducibleComponent
      (x := (⟨e, heW⟩ : ↑W))).2.open_subset hoOpen hoZ⟩
  exact ⟨(Subtype.val : ↑W → G.left) '' o,
    W.isOpen.isOpenMap_subtype_val _ hoOpen, hoNe.image _,
    hoIrr.image _ continuous_subtype_val.continuousOn⟩

/-- A connected locally algebraic group over an algebraically closed field is
irreducible. -/
theorem irreducibleSpace_of_isAlgClosed_of_connected
    (G : Over (Spec (.of K))) [GrpObj G] [IsAlgClosed K]
    [LocallyOfFiniteType G.hom] [ConnectedSpace G.left] :
    IrreducibleSpace G.left := by
  classical
  letI : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  obtain ⟨U, hUopen, hUne, hUirr⟩ :=
    exists_isOpen_nonempty_isIrreducible G
  obtain ⟨g, hgU, hgc⟩ :=
    nonempty_inter_closedPoints hUne hUopen.isLocallyClosed
  let g' : 𝟙_ (Over (Spec (.of K))) ⟶ G :=
    Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨g, hgc⟩).2
  have hg' : ∀ a, g'.left a = g := fun a ↦ by
    exact pointOfClosedPoint_apply G.hom g hgc a
  let pt : ↑(𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    (default : ↑(Spec (CommRingCat.of K)))
  have hcover : ∀ z ∈ closedPoints G.left,
      ∃ V : Set G.left, IsOpen V ∧ z ∈ V ∧ IsIrreducible V := by
    intro z hzc
    let z' : 𝟙_ (Over (Spec (.of K))) ⟶ G :=
      Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨z, hzc⟩).2
    have hz' : ∀ a, z'.left a = z := fun a ↦ by
      exact pointOfClosedPoint_apply G.hom z hzc a
    let τ : G ⟶ G := rightMul G (g'⁻¹ * z')
    haveI : IsIso τ := by
      change IsIso (rightMulIso G (g'⁻¹ * z')).hom
      infer_instance
    haveI : IsIso τ.left :=
      inferInstanceAs (IsIso ((Over.forget (Spec (.of K))).map τ))
    have hτ : g' ≫ τ = z' := by
      rw [show g' ≫ τ = g' ≫ rightMul G (g'⁻¹ * z') from rfl,
        comp_rightMul]
      simp
    have hτl : g'.left ≫ τ.left = z'.left := by
      simpa using congrArg
        (fun q : 𝟙_ (Over (Spec (.of K))) ⟶ G ↦ q.left) hτ
    have hτ' : τ.left g = z := by
      calc
        τ.left g = τ.left (g'.left pt) := by rw [hg' pt]
        _ = (g'.left ≫ τ.left) pt := (Scheme.Hom.comp_apply _ _ _).symm
        _ = z'.left pt := by rw [hτl]
        _ = z := hz' pt
    exact ⟨⇑τ.left '' U, τ.left.isOpenEmbedding.isOpenMap _ hUopen,
      ⟨g, hgU, hτ'⟩,
      hUirr.image _ (Scheme.Hom.continuous τ.left).continuousOn⟩
  have hAllOpen : IsOpen (⋃₀ {V : Set G.left | IsOpen V ∧ IsIrreducible V}) :=
    isOpen_sUnion fun _ hV ↦ hV.1
  have hAll : ⋃₀ {V : Set G.left | IsOpen V ∧ IsIrreducible V} = Set.univ := by
    by_contra hne
    obtain ⟨w, hw, hwc⟩ := nonempty_inter_closedPoints
      (Set.nonempty_compl.mpr hne) hAllOpen.isClosed_compl.isLocallyClosed
    obtain ⟨V, hVopen, hwV, hVirr⟩ := hcover w hwc
    exact hw ⟨V, ⟨hVopen, hVirr⟩, hwV⟩
  apply irreducibleSpace_of_connectedSpace_of_nhds
  intro x
  have hx : x ∈ ⋃₀ {V : Set G.left | IsOpen V ∧ IsIrreducible V} := by
    rw [hAll]
    trivial
  obtain ⟨V, ⟨hVopen, hVirr⟩, hxV⟩ := hx
  exact ⟨V, hVopen, hxV, hVirr⟩

/-- Over an algebraically closed field, finitely many rational points of an
irreducible locally algebraic group lie in one affine open. -/
theorem exists_affineOpen_finset_points_of_irreducible
    (G : Over (Spec (.of K))) [GrpObj G] [IsAlgClosed K]
    [LocallyOfFiniteType G.hom] [IrreducibleSpace G.left]
    (s : Finset (𝟙_ (Over (Spec (.of K))) ⟶ G)) :
    ∃ A : G.left.affineOpens,
      ∀ p ∈ s, p.left (IsLocalRing.closedPoint K) ∈ A.1 := by
  classical
  let e : G.left := η[G].left (IsLocalRing.closedPoint K)
  obtain ⟨U, hUa, heU, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens)
      (show e ∈ (⊤ : G.left.Opens) from trivial)
  let A : G.left.affineOpens := ⟨U, hUa⟩
  let V : (𝟙_ (Over (Spec (.of K))) ⟶ G) → Set G.left :=
    fun p ↦ ((leftMulIso G p).hom.left ⁻¹ᵁ A.1 : Set G.left)
  let F : Finset (Set G.left) := s.image V
  have hVopen (p : 𝟙_ (Over (Spec (.of K))) ⟶ G) : IsOpen (V p) :=
    A.1.isOpen.preimage (Scheme.Hom.continuous (leftMulIso G p).hom.left)
  have hVnonempty (p : 𝟙_ (Over (Spec (.of K))) ⟶ G) : (V p).Nonempty := by
    let x := (p ≫ ι).left (IsLocalRing.closedPoint K)
    refine ⟨x, ?_⟩
    change (leftMul G p).left ((p ≫ ι).left (IsLocalRing.closedPoint K)) ∈ U
    have h : (p ≫ ι) ≫ leftMul G p = η[G] := by
      rw [comp_leftMul]
      change p * p⁻¹ = η[G]
      exact (mul_inv_cancel p).trans (by
        rw [CategoryTheory.Hom.one_def]
        simp)
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h]
    exact heU
  have hFopen : ∀ W ∈ F, IsOpen W := by
    intro W hW
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hW
    exact hVopen p
  have hFnonempty : ∀ W ∈ F, W.Nonempty := by
    intro W hW
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hW
    exact hVnonempty p
  have hIrr := (isIrreducible_iff_sInter.mp
    (IrreducibleSpace.isIrreducible_univ G.left)) F hFopen (by
      intro W hW
      simpa using hFnonempty W hW)
  have hInter : (⋂₀ (↑F : Set (Set G.left))).Nonempty := by
    simpa using hIrr
  have hInterOpen : IsOpen (⋂₀ (↑F : Set (Set G.left))) :=
    F.finite_toSet.isOpen_sInter hFopen
  letI : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  obtain ⟨g, hgF, hgc⟩ :=
    nonempty_inter_closedPoints hInter hInterOpen.isLocallyClosed
  let q0 := (pointEquivClosedPoint G.hom).symm ⟨g, hgc⟩
  let q : 𝟙_ (Over (Spec (.of K))) ⟶ G := Over.homMk q0.1 q0.2
  have hq : q.left (IsLocalRing.closedPoint K) = g := by
    dsimp [q, q0]
    exact pointOfClosedPoint_apply G.hom g hgc (IsLocalRing.closedPoint K)
  refine ⟨⟨(rightMulIso G q).hom.left ⁻¹ᵁ A.1,
    A.2.preimage (rightMulIso G q).hom.left⟩, ?_⟩
  intro p hp
  have hpF : V p ∈ F := Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hgp : g ∈ V p := Set.mem_sInter.mp hgF _ hpF
  change (rightMul G q).left (p.left (IsLocalRing.closedPoint K)) ∈ U
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left,
    point_comp_rightMul_eq_point_comp_leftMul G p q,
    Over.comp_left, Scheme.Hom.comp_apply, hq]
  exact hgp

/-- Every finite set of topological points of an irreducible locally algebraic
group over an algebraically closed field lies in one affine open. -/
theorem finiteInAffine_of_isAlgClosed_of_irreducible
    (G : Over (Spec (.of K))) [GrpObj G] [IsAlgClosed K]
    [LocallyOfFiniteType G.hom] [IrreducibleSpace G.left] :
    Scheme.FiniteInAffine G.left := by
  classical
  intro s hs
  lift s to Finset G.left using hs with t ht
  letI : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  have hclosed (x : G.left) :
      ∃ y : G.left, y ∈ closure {x} ∧ y ∈ closedPoints G.left := by
    have hnonempty : (closure ({x} : Set G.left)).Nonempty :=
      ⟨x, subset_closure (Set.mem_singleton x)⟩
    obtain ⟨y, hy, hyc⟩ :=
      nonempty_inter_closedPoints hnonempty isClosed_closure.isLocallyClosed
    exact ⟨y, hy, hyc⟩
  choose y hy using hclosed
  let p0 (x : G.left) := (pointEquivClosedPoint G.hom).symm ⟨y x, (hy x).2⟩
  let p (x : G.left) : 𝟙_ (Over (Spec (.of K))) ⟶ G :=
    Over.homMk (p0 x).1 (p0 x).2
  obtain ⟨A, hA⟩ :=
    exists_affineOpen_finset_points_of_irreducible G (t.image p)
  refine ⟨A, ?_⟩
  intro x hx
  have hxt : x ∈ t := by
    exact_mod_cast hx
  have hp : p x ∈ t.image p := Finset.mem_image.mpr ⟨x, hxt, rfl⟩
  have hpx : (p x).left (IsLocalRing.closedPoint K) = y x := by
    dsimp [p, p0]
    exact pointOfClosedPoint_apply G.hom (y x) (hy x).2
      (IsLocalRing.closedPoint K)
  have hpy : y x ∈ A.1 := hpx ▸ hA (p x) hp
  exact (specializes_iff_mem_closure.mpr (hy x).1).mem_open A.1.isOpen hpy

/-- Every finite set of topological points of a connected locally algebraic
group over an algebraically closed field lies in one affine open. -/
theorem finiteInAffine_of_isAlgClosed_of_connected
    (G : Over (Spec (.of K))) [GrpObj G] [IsAlgClosed K]
    [LocallyOfFiniteType G.hom] [ConnectedSpace G.left] :
    Scheme.FiniteInAffine G.left := by
  letI : IrreducibleSpace G.left :=
    irreducibleSpace_of_isAlgClosed_of_connected G
  exact finiteInAffine_of_isAlgClosed_of_irreducible G

end AlgebraicGeometry.GroupScheme
