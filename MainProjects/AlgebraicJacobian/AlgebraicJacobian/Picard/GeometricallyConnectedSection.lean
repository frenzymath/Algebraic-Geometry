/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Std.Tactic.BVDecide.LRAT.Internal.Clause

/-!
# Connected + rational section ⟹ geometrically connected (Stacks 04KV / 037Q)

This file proves the descent substrate needed by `Picard/IdentityComponent.lean`:
a connected `k`-scheme `X` admitting a `k`-rational section `s : Spec k ⟶ X` of its
structural morphism `f : X ⟶ Spec k` is **geometrically connected** (Stacks 04KV,
EGA IV₂ 4.5.14). This unblocks the `AJC.picrep` identity-component cone
(`identityComponent_geometricallyConnected` and its consumers).

## Architecture

* **§A Algebra (Stacks 05P3-flavoured).** Over an algebraically closed field `k`,
  the tensor product `A ⊗[k] B` of two field extensions is a domain.
  - `exists_algHom_ker_eq`: maximal ideals of finite-type `k`-algebras have residue
    field `k` (Zariski's lemma + `IsAlgClosed`), packaged as evaluation `k`-algebra
    homomorphisms.
  - `isDomain_tensorProduct_of_finiteType`: for `R` a finite-type `k`-domain and `A/k`
    a field extension, `R ⊗[k] A` is a domain. The classical argument: coordinates of
    a zero-divisor pair multiply into every maximal ideal (evaluate via
    `exists_algHom_ker_eq` and use linear independence of a `k`-basis of `A`), hence
    into the Jacobson radical `= 0` (`R` is a Jacobson domain).
  - `Algebra.TensorProduct.isDomain_of_isAlgClosed`: the general case by exhausting
    the first factor by finite-type subalgebras (flatness over a field gives
    injectivity of `R ⊗[k] B ⟶ A ⊗[k] B`).

* **§B Geometry.**
  - `connectedSpace_pullback_of_isAlgClosed` (Stacks 0363): for `k` **algebraically
    closed** and `X/k` connected, `X ×ₖ Spec L` is connected for every extension
    `L/k`. Proof: the projection `X ×ₖ Spec L ⟶ X` is geometrically connected (its
    field-valued fibers are `Spec (K ⊗[k] L)`, connected by §A) and open (`Spec L ⟶
    Spec k` is universally open, being a morphism to the spectrum of a field), so
    Mathlib's `GeometricallyConnected.connectedSpace` applies.
  - `connectedSpace_pullback_algebraicClosure` (Stacks 04KV, algebraic step): for `X/k`
    connected with a rational section, `X ×ₖ Spec k̄` is connected. The projection
    `p : X ×ₖ Spec k̄ ⟶ X` is open, closed (integral) and surjective, and the fiber
    over the section point `x₀` is a single point (`κ(x₀) = k`); a nontrivial clopen
    partition upstairs would give two clopen sets downstairs both equal to `X`,
    contradicting the singleton fiber at `x₀`.
  - `geometricallyConnected_of_connectedSpace_of_section` (Stacks 04KV): assembly.
    For arbitrary `L/k`, embed `k̄ ↪ L̄ := (AlgebraicClosure L)` over `k`, apply the
    two previous steps to get `X ×ₖ Spec L̄` connected, and descend along the
    surjection `X ×ₖ Spec L̄ ⟶ X ×ₖ Spec L`.

## References

- Stacks: 04KV (section ⟹ geometrically connected), 0363 (separably closed base),
  05P3 (tensor product of extensions over algebraically closed field is a domain),
  0383 (schemes over a field are universally open over it).
- EGA IV₂ 4.5.13, 4.5.14.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

/-! ## §A. Algebra: tensor products of field extensions over an algebraically
closed field -/

section Algebra

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- **Nullstellensatz evaluation**: a maximal ideal `m` of a finite-type algebra `R`
over an algebraically closed field `k` is the kernel of a `k`-algebra homomorphism
`R →ₐ[k] k` (the residue field of `m` is `k` by Zariski's lemma). -/
theorem exists_algHom_ker_eq (R : Type*) [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (m : Ideal R) [m.IsMaximal] :
    ∃ φ : R →ₐ[k] k, RingHom.ker φ = m := by
  -- Install the field structure on the quotient FIRST (instance-ordering trap).
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m)
      (Ideal.Quotient.mkₐ_surjective k m)
  -- Zariski's lemma: a finite-type field extension is finite, hence integral.
  haveI : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  haveI : Algebra.IsIntegral k (R ⧸ m) := Algebra.IsIntegral.of_finite k (R ⧸ m)
  have hbij : Function.Bijective (algebraMap k (R ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] (R ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m)) hbij
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  ext r
  rw [RingHom.mem_ker]
  change e.symm (Ideal.Quotient.mk m r) = 0 ↔ r ∈ m
  rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

/-- **Stacks 05P3, finite-type case**: for `k` algebraically closed, `R` a
finite-type `k`-algebra which is a domain, and `A/k` a field extension, the tensor
product `R ⊗[k] A` is a domain. -/
theorem isDomain_tensorProduct_of_finiteType
    (R A : Type*) [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    [Field A] [Algebra k A] : IsDomain (R ⊗[k] A) := by
  classical
  haveI : Nontrivial (R ⊗[k] A) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k R A
      (RingHom.injective _) (RingHom.injective _)
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k) (B := R)
  haveI : NoZeroDivisors (R ⊗[k] A) := by
    refine ⟨@fun x y hxy => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hx, hy⟩ := hcon
    -- Coordinates with respect to a `k`-basis of `A`.
    let bA := Module.Basis.ofVectorSpace k A
    let B := Algebra.TensorProduct.basis R bA
    -- Any two coordinates (one of `x`, one of `y`) multiply to zero in `R`.
    have key : ∀ i j, B.repr x i * B.repr y j = 0 := by
      intro i j
      -- The product lies in every maximal ideal of `R`.
      have hmax : ∀ (m : Ideal R), m.IsMaximal → B.repr x i * B.repr y j ∈ m := by
        intro m hm
        obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (k := k) R m
        have hmem : ∀ c : R, φ c = 0 → c ∈ m := fun c hc => by
          rw [← hφ]; exact RingHom.mem_ker.mpr hc
        -- Evaluation `Ψ : R ⊗[k] A →ₐ[k] A` at `m` in the first factor.
        let ψR : R →ₐ[k] A := (Algebra.ofId k A).comp φ
        let Ψ : R ⊗[k] A →ₐ[k] A :=
          Algebra.TensorProduct.lift ψR (AlgHom.id k A) fun r a => Commute.all _ _
        -- Ψ in coordinates.
        have hΨ : ∀ z : R ⊗[k] A, Ψ z = (B.repr z).sum fun i r => φ r • bA i := by
          intro z
          conv_lhs => rw [← B.linearCombination_repr z, Finsupp.linearCombination_apply]
          rw [map_finsuppSum]
          refine Finsupp.sum_congr fun i _ => ?_
          rw [Algebra.TensorProduct.basis_repr_symm_apply']
          rw [Algebra.TensorProduct.lift_tmul]
          simp only [AlgHom.coe_id, id_eq, ψR, AlgHom.coe_comp, Function.comp_apply]
          rw [Algebra.ofId_apply, ← Algebra.smul_def]
        -- If Ψ z = 0 then every coordinate of `z` is killed by φ.
        have hzero : ∀ z : R ⊗[k] A, Ψ z = 0 → ∀ i, φ (B.repr z i) = 0 := by
          intro z hz i
          by_cases hsupp : i ∈ (B.repr z).support
          · have hli := bA.linearIndependent
            rw [linearIndependent_iff'] at hli
            refine hli (B.repr z).support (fun i => φ (B.repr z i)) ?_ i hsupp
            have : ((B.repr z).sum fun i r => φ r • bA i) = 0 := (hΨ z).symm.trans hz
            simpa [Finsupp.sum] using this
          · rw [Finsupp.notMem_support_iff.mp hsupp, map_zero]
        have hmul : Ψ x * Ψ y = 0 := by rw [← map_mul, hxy, map_zero]
        rcases mul_eq_zero.mp hmul with h | h
        · exact Ideal.mul_mem_right _ _ (hmem _ (hzero x h i))
        · exact Ideal.mul_mem_left _ _ (hmem _ (hzero y h j))
      -- Jacobson: the intersection of all maximal ideals of `R` is zero.
      have hj : B.repr x i * B.repr y j ∈ (⊥ : Ideal R).jacobson :=
        Ideal.mem_sInf.mpr fun {J} hJ => hmax J hJ.2
      rwa [‹IsJacobsonRing R›.out Ideal.isPrime_bot.isRadical, Ideal.mem_bot] at hj
    -- Conclude: `x = 0` or `y = 0`.
    obtain ⟨i₀, hi₀⟩ : ∃ i, B.repr x i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hx (B.repr.map_eq_zero_iff.mp (Finsupp.ext hall))
    refine hy (B.repr.map_eq_zero_iff.mp (Finsupp.ext fun j => ?_))
    rcases mul_eq_zero.mp (key i₀ j) with h | h
    · exact absurd h hi₀
    · exact h
  exact NoZeroDivisors.to_isDomain _

/-- **Stacks 05P3**: for `k` algebraically closed and `A/k`, `B/k` field
extensions, the tensor product `A ⊗[k] B` is a domain. In particular
`Spec (A ⊗[k] B)` is irreducible, hence connected. -/
theorem _root_.Algebra.TensorProduct.isDomain_of_isAlgClosed
    (A B : Type*) [Field A] [Algebra k A] [Field B] [Algebra k B] :
    IsDomain (A ⊗[k] B) := by
  classical
  haveI : Nontrivial (A ⊗[k] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k A B
      (RingHom.injective _) (RingHom.injective _)
  haveI : NoZeroDivisors (A ⊗[k] B) := by
    refine ⟨@fun x y hxy => ?_⟩
    obtain ⟨sx, hsx⟩ := TensorProduct.exists_finset x
    obtain ⟨sy, hsy⟩ := TensorProduct.exists_finset y
    -- Adjoin the (finitely many) first components appearing in `x` and `y`.
    set S : Finset A := sx.image Prod.fst ∪ sy.image Prod.fst with hS
    set R : Subalgebra k A := Algebra.adjoin k (S : Set A) with hRdef
    haveI : Algebra.FiniteType k R :=
      (Subalgebra.fg_iff_finiteType R).mp (Subalgebra.fg_adjoin_finset S)
    -- `R ⊗[k] B ⟶ A ⊗[k] B` is injective (`B` is flat over the field `k`).
    let Φ : R ⊗[k] B →ₐ[k] A ⊗[k] B :=
      Algebra.TensorProduct.map R.val (AlgHom.id k B)
    have hΦinj : Function.Injective Φ := by
      have h := Module.Flat.rTensor_preserves_injective_linearMap
        (M := B) R.val.toLinearMap Subtype.val_injective
      intro a b hab
      apply h
      simpa [Φ, Algebra.TensorProduct.map, LinearMap.rTensor,
        TensorProduct.AlgebraTensorModule.map_eq] using hab
    -- Preimages of `x` and `y` in `R ⊗[k] B`.
    have hmemx : ∀ p ∈ sx, p.1 ∈ R := fun p hp =>
      Algebra.subset_adjoin (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp))
    have hmemy : ∀ p ∈ sy, p.1 ∈ R := fun p hp =>
      Algebra.subset_adjoin (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))
    let x' : R ⊗[k] B := ∑ p ∈ sx.attach, (⟨p.1.1, hmemx p.1 p.2⟩ : R) ⊗ₜ[k] p.1.2
    let y' : R ⊗[k] B := ∑ p ∈ sy.attach, (⟨p.1.1, hmemy p.1 p.2⟩ : R) ⊗ₜ[k] p.1.2
    have hx' : Φ x' = x := by
      rw [hsx]
      simp only [x', map_sum]
      rw [← Finset.sum_attach sx fun p => p.1 ⊗ₜ[k] p.2]
      rfl
    have hy' : Φ y' = y := by
      rw [hsy]
      simp only [y', map_sum]
      rw [← Finset.sum_attach sy fun p => p.1 ⊗ₜ[k] p.2]
      rfl
    -- Push the relation into the finite-type case.
    haveI : IsDomain (R ⊗[k] B) := isDomain_tensorProduct_of_finiteType R B
    have h0 : x' * y' = 0 := hΦinj (by rw [map_mul, hx', hy', hxy, map_zero])
    rcases mul_eq_zero.mp h0 with h | h
    · left; rw [← hx', h, map_zero]
    · right; rw [← hy', h, map_zero]
  exact NoZeroDivisors.to_isDomain _

end Algebra

/-! ## §B. Geometry: descent of connectedness along field extensions -/

section Geometry

open CommRingCat

/-- The spectrum of a (commutative) domain is connected. -/
lemma connectedSpace_spec_of_isDomain (R : Type u) [CommRing R] [IsDomain R] :
    ConnectedSpace ↥(Spec (CommRingCat.of R)) := by
  haveI : IrreducibleSpace (PrimeSpectrum R) := PrimeSpectrum.irreducibleSpace
  exact inferInstanceAs (ConnectedSpace (PrimeSpectrum R))

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- For `k` algebraically closed, the projection `X ×ₖ Spec L ⟶ X` is geometrically
connected: its fiber over a `K`-valued point is `Spec (K ⊗[k] L)`, whose ring is a
domain by Stacks 05P3. -/
theorem geometricallyConnected_pullback_fst_of_isAlgClosed [IsAlgClosed k]
    (L : Type u) [Field L] [Algebra k L] (f : X ⟶ Spec (.of k)) :
    GeometricallyConnected
      (pullback.fst f (Spec.map (ofHom (algebraMap k L)))) := by
  set g := Spec.map (ofHom (algebraMap k L)) with hg
  constructor
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (y ≫ f)
  algebraize [φ.hom]
  have hφ' : y ≫ f = Spec.map (ofHom (algebraMap k K)) := by
    rw [← hφ]; congr 1
  haveI : IsDomain (K ⊗[k] L) := Algebra.TensorProduct.isDomain_of_isAlgClosed K L
  -- `pullback (pullback.fst f g) y ≅ Spec (K ⊗[k] L)`.
  let E : pullback (pullback.fst f g) y ≅ Spec (.of (K ⊗[k] L)) :=
    pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g y ≪≫
      pullback.congrHom hφ' rfl ≪≫ pullbackSpecIso k K L
  exact E.hom.homeomorph.connectedSpace_iff.mpr
    (connectedSpace_spec_of_isDomain (K ⊗[k] L))

/-- **Stacks 0363**: over an algebraically closed field `k`, a connected `k`-scheme
stays connected after arbitrary base field extension `L/k`. -/
theorem connectedSpace_pullback_of_isAlgClosed [IsAlgClosed k]
    (L : Type u) [Field L] [Algebra k L] (f : X ⟶ Spec (.of k)) [ConnectedSpace X] :
    ConnectedSpace ↥(pullback f (Spec.map (ofHom (algebraMap k L)))) := by
  set g := Spec.map (ofHom (algebraMap k L)) with hg
  haveI : IsIntegral (Spec (CommRingCat.of k)) := inferInstance
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : UniversallyOpen g := inferInstance
  haveI := geometricallyConnected_pullback_fst_of_isAlgClosed L f
  exact GeometricallyConnected.connectedSpace (f := pullback.fst f g)
    (pullback.fst f g).isOpenMap

/-- **Stacks 04KV, algebraic step**: a connected `k`-scheme with a `k`-rational
section stays connected after base change to the algebraic closure `k̄/k`. The
projection is open, closed and surjective, and the fiber over the section point is
a singleton, which forbids nontrivial clopen partitions upstairs. -/
theorem connectedSpace_pullback_algebraicClosure
    (f : X ⟶ Spec (.of k)) (s : Spec (.of k) ⟶ X) (hsf : s ≫ f = 𝟙 _)
    [ConnectedSpace X] :
    ConnectedSpace
      ↥(pullback f (Spec.map (ofHom (algebraMap k (AlgebraicClosure k))))) := by
  set kb := AlgebraicClosure k
  set g := Spec.map (ofHom (algebraMap k kb)) with hg
  set p := pullback.fst f g with hp
  -- `p` is open.
  haveI : IsIntegral (Spec (CommRingCat.of k)) := inferInstance
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : UniversallyOpen g := inferInstance
  have hopen : IsOpenMap p.base := p.isOpenMap
  -- `p` is closed (integral base change).
  haveI : IsIntegralHom g := by
    rw [IsIntegralHom.SpecMap_iff]
    exact Algebra.isIntegral_def.mp inferInstance
  have hclosed : IsClosedMap p.base := p.isClosedMap
  -- `p` is surjective.
  haveI : Nonempty ↥(Spec (CommRingCat.of kb)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum kb))
  haveI : Surjective g := ⟨Function.surjective_to_subsingleton _⟩
  -- The section point and its residue-field retraction.
  set x₀ : X := s.base (IsLocalRing.closedPoint k) with hx₀
  set ψ : X.residueField x₀ ⟶ .of k :=
    X.descResidueField (Scheme.stalkClosedPointTo s) with hψ
  have hsplit : Spec.map ψ ≫ X.fromSpecResidueField x₀ = s :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X s
  obtain ⟨φ₀, hφ₀⟩ := Spec.map_surjective (X.fromSpecResidueField x₀ ≫ f)
  have hretr : φ₀ ≫ ψ = 𝟙 (CommRingCat.of k) := by
    rw [← Spec.map_inj, Spec.map_comp, Spec.map_id, hφ₀, ← Category.assoc,
      hsplit, hsf]
  have hretr' : ∀ a : k, ψ.hom (φ₀.hom a) = a := fun a =>
    congrArg (fun (h : CommRingCat.of k ⟶ CommRingCat.of k) => h.hom a) hretr
  have hbij : Function.Bijective φ₀.hom := by
    refine ⟨RingHom.injective _, fun t => ⟨ψ.hom t, ?_⟩⟩
    have : ψ.hom (φ₀.hom (ψ.hom t)) = ψ.hom t := hretr' (ψ.hom t)
    exact RingHom.injective ψ.hom this
  -- The fiber of `p` over `x₀` is a singleton.
  letI : Algebra k ↥(X.residueField x₀) := φ₀.hom.toAlgebra
  have hφ₀' : X.fromSpecResidueField x₀ ≫ f =
      Spec.map (ofHom (algebraMap k ↥(X.residueField x₀))) := by
    rw [← hφ₀]; congr 1
  haveI : Subsingleton ↥(Spec (.of (↥(X.residueField x₀) ⊗[k] kb))) := by
    let e1 : k ≃ₐ[k] ↥(X.residueField x₀) :=
      AlgEquiv.ofBijective (Algebra.ofId k _) hbij
    let e : (↥(X.residueField x₀) ⊗[k] kb) ≃ₐ[k] kb :=
      (Algebra.TensorProduct.congr e1.symm AlgEquiv.refl).trans
        (Algebra.TensorProduct.lid k kb)
    have hf : IsField (↥(X.residueField x₀) ⊗[k] kb) :=
      e.toMulEquiv.isField (Field.toIsField kb)
    letI := hf.toField
    exact inferInstanceAs (Subsingleton (PrimeSpectrum _))
  have hfibsub : Subsingleton ↥(p.fiber x₀) := by
    let E : p.fiber x₀ ≅ Spec (.of (↥(X.residueField x₀) ⊗[k] kb)) :=
      pullbackSymmetry _ _ ≪≫
        pullbackRightPullbackFstIso f g (X.fromSpecResidueField x₀) ≪≫
        pullback.congrHom hφ₀' rfl ≪≫ pullbackSpecIso k _ kb
    exact E.hom.homeomorph.subsingleton
  have hfib : ∀ z z' : ↥(pullback f g), p.base z = x₀ → p.base z' = x₀ → z = z' := by
    haveI : Subsingleton (p.base ⁻¹' {x₀}) :=
      (p.fiberHomeo x₀).symm.toEquiv.subsingleton
    intro z z' hz hz'
    exact congrArg Subtype.val
      (Subsingleton.elim (α := (p.base ⁻¹' {x₀}))
        ⟨z, by simp [hz]⟩ ⟨z', by simp [hz']⟩)
  -- Nonemptiness: the base-changed section provides a point.
  have hne : Nonempty ↥(pullback f g) := by
    let sK : Spec (.of kb) ⟶ pullback f g :=
      pullback.lift (g ≫ s) (𝟙 _)
        (by rw [Category.assoc, hsf, Category.comp_id, Category.id_comp])
    exact ⟨sK.base (Nonempty.some inferInstance)⟩
  -- Clopen argument.
  have hpre : PreconnectedSpace ↥(pullback f g) := by
    rw [preconnectedSpace_iff_clopen]
    intro T hT
    by_cases hTe : T = ∅
    · exact Or.inl hTe
    right
    by_cases hTc : Tᶜ = ∅
    · rwa [Set.compl_empty_iff] at hTc
    exfalso
    have hTne : T.Nonempty := Set.nonempty_iff_ne_empty.mpr hTe
    have hTcne : Tᶜ.Nonempty := Set.nonempty_iff_ne_empty.mpr hTc
    have hA : IsClopen (p.base '' T) := ⟨hclosed _ hT.isClosed, hopen _ hT.isOpen⟩
    have hB : IsClopen (p.base '' Tᶜ) :=
      ⟨hclosed _ hT.compl.isClosed, hopen _ hT.compl.isOpen⟩
    have hAu : p.base '' T = Set.univ := hA.eq_univ (hTne.image _)
    have hBu : p.base '' Tᶜ = Set.univ := hB.eq_univ (hTcne.image _)
    obtain ⟨z, hzT, hz⟩ : x₀ ∈ p.base '' T := hAu ▸ Set.mem_univ x₀
    obtain ⟨z', hz'T, hz'⟩ : x₀ ∈ p.base '' Tᶜ := hBu ▸ Set.mem_univ x₀
    exact hz'T (hfib z z' hz hz' ▸ hzT)
  exact { toPreconnectedSpace := hpre, toNonempty := hne }

/-- **Stacks 04KV / EGA IV₂ 4.5.14**: a connected `k`-scheme with a `k`-rational
section is geometrically connected. -/
theorem geometricallyConnected_of_connectedSpace_of_section
    (f : X ⟶ Spec (.of k)) (s : Spec (.of k) ⟶ X) (hsf : s ≫ f = 𝟙 _)
    [ConnectedSpace X] : GeometricallyConnected f := by
  constructor
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro L _ _
  -- Set up the tower `k ⊆ k̄ ⊆ L̄ ⊇ L`.
  set kb := AlgebraicClosure k
  set Lb := AlgebraicClosure L
  let ι : kb →ₐ[k] Lb := IsAlgClosed.lift
  letI : Algebra kb Lb := ι.toRingHom.toAlgebra
  -- Step 1: `X ×ₖ Spec k̄` is connected (algebraic step, uses the section).
  haveI hZ : ConnectedSpace ↥(pullback f (Spec.map (ofHom (algebraMap k kb)))) :=
    connectedSpace_pullback_algebraicClosure f s hsf
  -- Step 2: base change from `k̄` to `L̄` (algebraically closed base).
  haveI hW : ConnectedSpace
      ↥(pullback (pullback.snd f (Spec.map (ofHom (algebraMap k kb))))
        (Spec.map (ofHom (algebraMap kb Lb)))) :=
    connectedSpace_pullback_of_isAlgClosed (k := kb) Lb _
  -- Step 3: transfer along the pasting isomorphism to `X ×ₖ Spec L̄`.
  have hcomp : Spec.map (ofHom (algebraMap kb Lb)) ≫
      Spec.map (ofHom (algebraMap k kb)) = Spec.map (ofHom (algebraMap k Lb)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ι.comp_algebraMap
  haveI hLb : ConnectedSpace ↥(pullback f (Spec.map (ofHom (algebraMap k Lb)))) :=
    ((pullbackLeftPullbackSndIso f (Spec.map (ofHom (algebraMap k kb)))
        (Spec.map (ofHom (algebraMap kb Lb))) ≪≫
      pullback.congrHom rfl hcomp).hom.homeomorph.connectedSpace_iff).mp hW
  -- Step 4: descend along the surjection `X ×ₖ Spec L̄ ⟶ X ×ₖ Spec L`.
  have hLL : Spec.map (ofHom (algebraMap L Lb)) ≫
      Spec.map (ofHom (algebraMap k L)) = Spec.map (ofHom (algebraMap k Lb)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  haveI hW' : ConnectedSpace
      ↥(pullback (pullback.snd f (Spec.map (ofHom (algebraMap k L))))
        (Spec.map (ofHom (algebraMap L Lb)))) :=
    ((pullbackLeftPullbackSndIso f (Spec.map (ofHom (algebraMap k L)))
        (Spec.map (ofHom (algebraMap L Lb))) ≪≫
      pullback.congrHom rfl hLL).hom.homeomorph.connectedSpace_iff).mpr hLb
  haveI : Nonempty ↥(Spec (CommRingCat.of Lb)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum Lb))
  haveI : Subsingleton ↥(Spec (CommRingCat.of L)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum L))
  haveI : Surjective (Spec.map (ofHom (algebraMap L Lb))) :=
    ⟨Function.surjective_to_subsingleton _⟩
  set π := pullback.fst (pullback.snd f (Spec.map (ofHom (algebraMap k L))))
    (Spec.map (ofHom (algebraMap L Lb))) with hπ
  haveI : Surjective π := inferInstance
  have hsurj : Function.Surjective π.base := π.surjective
  have hpre : _root_.IsPreconnected
      (Set.univ : Set ↥(pullback f (Spec.map (ofHom (algebraMap k L))))) := by
    have h1 := connectedSpace_iff_univ.mp hW'
    have h2 := h1.isPreconnected.image π.base
      (Continuous.continuousOn (by fun_prop))
    rwa [Set.image_univ, Set.range_eq_univ.mpr hsurj] at h2
  exact { toPreconnectedSpace := ⟨hpre⟩,
          toNonempty := ⟨π.base (Nonempty.some hW'.toNonempty)⟩ }

end Geometry

end AlgebraicGeometry
