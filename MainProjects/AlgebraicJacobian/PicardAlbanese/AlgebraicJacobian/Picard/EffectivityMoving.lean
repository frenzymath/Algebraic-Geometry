/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.EffectivityInvertibleAvoid
import AlgebraicJacobian.Picard.EffectivityPieces
import AlgebraicJacobian.Picard.CechPicToPicNaturality
import AlgebraicJacobian.Picard.CechPicSurjective

/-!
# The moving lemma: pieces on which the class trivializes ((C2) effectivity, brick E4)

**Piece selection** for the (C2) effectivity splice: for a *module-finite* faithfully
flat cover `A → B`, every point `x` of the base curve `X_A` admits an affine open
`V ∋ x` such that any prescribed Čech Picard class `L` on `X_B` restricts trivially to
the open subscheme `cg⁻¹ V` of the cover curve.

The route is pure commutative algebra — no integrality of the curve, no divisors:

* the class of `L` on a `cg`-saturated affine piece `O₀ = cg⁻¹ V₀ ∋ cg⁻¹(x)` is an
  invertible module `N` over `Γ(X_B, O₀)` (`Scheme.Opens.cechPicClass`, the affine
  dictionary `toPic` conjugated by `topIso`);
* the fiber of `Spec Γ(O₀) → Spec Γ(V₀)` over the germ prime of `x` is **finite** —
  the piece ring is module-finite over the base piece by E0's identification
  `Γ(O₀) ≅ Γ(V₀) ⊗[A] B` and `[Module.Finite A B]`, so the algebra is quasi-finite
  (`Algebra.QuasiFinite.finite_comap_preimage_singleton`);
* the **avoidance brick** (`Module.Invertible.exists_notMem_isUnit_free`) produces
  `f ∈ Γ(O₀)` avoiding every fiber prime with `N` free wherever `f` is inverted;
* the **algebraic tube** (`Algebra.exists_notMem_algebraMap_eq_mul`, going-up for the
  module-finite piece map) produces `g ∉ p_x` with `cg^♯ g = f · h`, so
  `V := X_A.basicOpen g ∋ x` has `cg⁻¹ V = X_B.basicOpen (cg^♯ g) ≤ X_B.basicOpen f`;
* freeness of `N` over `Γ(X_B, X_B.basicOpen f)` (where `f` restricts to a unit) makes
  the class trivial there (`Scheme.Opens.cechPicClass_basicOpen_eq_one_of_free`), and
  restriction triviality is monotone (`Scheme.cechPicMap_ι_eq_one_of_le`).

The conversion of this class-level triviality into the trimmed trivializing cochain
(`Over.PieceTrivialization`) that the landed per-piece descent consumes is
`AlgebraicJacobian.Picard.EffectivityTrivialization`.

## Why module-finiteness

For a merely étale (quasi-finite, non-finite) cover the statement is **false**: the
bare restricted class need not trivialize on any saturated neighbourhood of a fiber
(e.g. `B = A_u × A_v` over a two-dimensional normal local `A` with nontrivial local
class group).  The general-cover effectivity therefore genuinely needs the descent
data, and is reached in the close through covers refined to module-finite ones (over a
field test every étale cover is refined by a finite separable field extension).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry

namespace Scheme

variable {Z : Scheme.{u}}

/-! ## The class of a Čech Picard class on an affine open, and its calculus -/

/-- Monotonicity of restriction triviality: a Čech Picard class trivial on an open
subscheme is trivial on every smaller open subscheme. -/
theorem cechPicMap_ι_eq_one_of_le {O O' : Z.Opens} (h : O' ≤ O) (L : Z.CechPic)
    (hL : Scheme.CechPic.map O.ι L = 1) :
    Scheme.CechPic.map O'.ι L = 1 := by
  rw [← Z.homOfLE_ι h, Scheme.CechPic.map_comp, MonoidHom.comp_apply, hL, map_one]

/-- The identification of the sections of an open subscheme with the ambient sections,
as pullback along the inclusion: an isomorphism (`Restrict.lean`). -/
noncomputable abbrev Opens.ιTop (O : Z.Opens) : Γ(Z, O) ⟶ Γ(O, ⊤) :=
  O.ι.appLE O ⊤ O.ι_preimage_self.ge

/-- The Picard class over the ambient sections `Γ(Z, O)` of the restriction of a Čech
Picard class to an affine open subscheme: the affine dictionary `toPic` conjugated by
the section identification. -/
noncomputable def Opens.cechPicClass (O : Z.Opens) (hO : IsAffineOpen O)
    (L : Z.CechPic) : CommRing.Pic Γ(Z, O) :=
  haveI : IsAffine (O : Scheme.{u}) := hO
  CommRing.Pic.mapRingHom (inv O.ιTop).hom
    (Scheme.CechPic.toPic O.toScheme (Scheme.CechPic.map O.ι L))

/-- Transport along a ring homomorphism with a left inverse reflects triviality in the
Picard group. -/
private lemma pic_eq_one_of_mapRingHom {R S : Type u} [CommRing R] [CommRing S]
    {φ : R →+* S} {ψ : S →+* R} (hψφ : ψ.comp φ = RingHom.id R) {M : CommRing.Pic R}
    (h : CommRing.Pic.mapRingHom φ M = 1) : M = 1 := by
  have h2 := congrArg (CommRing.Pic.mapRingHom ψ) h
  rw [map_one, CommRing.Pic.mapRingHom_mapRingHom, hψφ,
    ← Algebra.algebraMap_self (R := R), CommRing.Pic.mapRingHom_algebraMap,
    CommRing.Pic.mapAlgebra_self_apply] at h2
  exact h2

/-- Triviality of the affine-open class detects restriction triviality. -/
theorem Opens.cechPicMap_ι_eq_one_of_cechPicClass_eq_one {O : Z.Opens}
    (hO : IsAffineOpen O) {L : Z.CechPic} (h : O.cechPicClass hO L = 1) :
    Scheme.CechPic.map O.ι L = 1 := by
  haveI : IsAffine (O : Scheme.{u}) := hO
  apply Scheme.CechPic.toPic_injective (X := O.toScheme)
  rw [map_one]
  refine pic_eq_one_of_mapRingHom (φ := (inv O.ιTop).hom) (ψ := O.ιTop.hom) ?_ h
  have : inv O.ιTop ≫ O.ιTop = 𝟙 _ := IsIso.inv_hom_id _
  have h2 := congrArg CommRingCat.Hom.hom this
  rwa [CommRingCat.hom_comp] at h2

/-- Congruence in the morphism for `appLE`, at the `CommRingCat` level. -/
private lemma appLE_hom_congr {X Y : Scheme.{u}} {f f' : X ⟶ Y} (hf : f = f')
    {V : Y.Opens} {O : X.Opens} (e : O ≤ f ⁻¹ᵁ V) (e' : O ≤ f' ⁻¹ᵁ V) :
    f.appLE V O e = f'.appLE V O e' := by
  subst hf; rfl

/-- **The restriction seam of the affine-open class**: for affine opens `O' ≤ O`, the
class of the restriction to `O'` is the image of the class on `O` under the restriction
map of ambient sections — the `appLE` square of the two inclusions. -/
theorem Opens.cechPicClass_of_le {O O' : Z.Opens} (hO : IsAffineOpen O)
    (hO' : IsAffineOpen O') (h : O' ≤ O) (L : Z.CechPic) :
    O'.cechPicClass hO' L
      = CommRing.Pic.mapRingHom (Z.presheaf.map (homOfLE h).op).hom
          (O.cechPicClass hO L) := by
  haveI : IsAffine (O : Scheme.{u}) := hO
  haveI : IsAffine (O' : Scheme.{u}) := hO'
  -- the `appLE` square of the two inclusions
  have hsq : O.ιTop ≫ (Z.homOfLE h).appTop = Z.presheaf.map (homOfLE h).op ≫ O'.ιTop := by
    have hle : (⊤ : (O' : Scheme.{u}).Opens) ≤ O'.ι ⁻¹ᵁ O :=
      O'.ι_preimage_self.ge.trans (O'.ι.preimage_mono h)
    have h1 : O.ιTop ≫ (Z.homOfLE h).appTop
        = (Z.homOfLE h ≫ O.ι).appLE O ⊤ (by rw [Z.homOfLE_ι]; exact hle) := by
      rw [show (Z.homOfLE h).appTop = (Z.homOfLE h).appLE ⊤ ⊤
          (Scheme.Hom.preimage_top (Z.homOfLE h)).ge from
          (Scheme.Hom.appLE_eq_app (Z.homOfLE h)).symm]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    have h2 : Z.presheaf.map (homOfLE h).op ≫ O'.ιTop = O'.ι.appLE O ⊤ hle :=
      Scheme.Hom.map_appLE _ _ _
    rw [h1, h2]
    exact appLE_hom_congr (Z.homOfLE_ι h) _ _
  -- unfold both classes and chase the square
  rw [Opens.cechPicClass, Opens.cechPicClass, ← Z.homOfLE_ι h,
    Scheme.CechPic.map_comp, MonoidHom.comp_apply,
    Scheme.CechPic.toPic_map (Z.homOfLE h), CommRing.Pic.mapRingHom_mapRingHom,
    CommRing.Pic.mapRingHom_mapRingHom]
  -- turn the square into the inverse form
  have hinv : (Z.homOfLE h).appTop ≫ inv O'.ιTop
      = inv O.ιTop ≫ Z.presheaf.map (homOfLE h).op := by
    rw [IsIso.comp_inv_eq, Category.assoc, ← hsq, IsIso.inv_hom_id_assoc]
  refine congrArg (fun ψ => CommRing.Pic.mapRingHom ψ
    (Scheme.CechPic.toPic O.toScheme (Scheme.CechPic.map O.ι L))) ?_
  have h3 := congrArg CommRingCat.Hom.hom hinv
  rwa [CommRingCat.hom_comp, CommRingCat.hom_comp] at h3

/-- **Freeness trivializes the class on a basic open**: if the invertible module of the
class on an affine `O` becomes free over every algebra inverting `f`, the class on the
basic open of `f` is trivial. -/
theorem Opens.cechPicClass_basicOpen_eq_one_of_free {O : Z.Opens}
    (hO : IsAffineOpen O) (L : Z.CechPic) (f : Γ(Z, O))
    (hfree : ∀ (S : Type u) [CommRing S] [Algebra Γ(Z, O) S],
      IsUnit (algebraMap Γ(Z, O) S f) →
        Module.Free S (S ⊗[Γ(Z, O)] (O.cechPicClass hO L).AsModule)) :
    (Z.basicOpen f).cechPicClass (hO.basicOpen f) L = 1 := by
  rw [Opens.cechPicClass_of_le hO (hO.basicOpen f) (Z.basicOpen_le f) L]
  letI := (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom.toAlgebra
  have hres : CommRing.Pic.mapRingHom
        (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom (O.cechPicClass hO L)
      = CommRing.Pic.mapAlgebra Γ(Z, O) Γ(Z, Z.basicOpen f) (O.cechPicClass hO L) :=
    rfl
  have hunit : IsUnit (algebraMap Γ(Z, O) Γ(Z, Z.basicOpen f) f) :=
    Z.toRingedSpace.isUnit_res_basicOpen f
  haveI := hfree Γ(Z, Z.basicOpen f) hunit
  rw [hres, CommRing.Pic.mapAlgebra_apply]
  exact CommRing.Pic.mk_eq_one _ _

end Scheme

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]
variable (C : Over (Spec (.of k)))

set_option quotPrecheck false in
local notation "XA" => (C ⊗ overSpec k A).left
set_option quotPrecheck false in
local notation "XB" => (C ⊗ overSpec k B).left
set_option quotPrecheck false in
local notation "cg" => (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left

namespace Over

-- The base-piece `A`-algebra structure and the cover-piece `Γ(V)`-algebra structure.
attribute [local instance] Over.sectionsAlgebraA Over.pieceCoverAlgebra

/-- **Module-finiteness of the cover piece over the base piece**: for a module-finite
`A → B`, the piece ring `Γ(cg⁻¹ V) ≅ Γ(V) ⊗[A] B` is module-finite over `Γ(V)`. -/
theorem finite_pieceCover [Module.Finite A B] {V : (XA).Opens} (hV : IsAffineOpen V) :
    Module.Finite Γ(XA, V) Γ(XB, (cg) ⁻¹ᵁ V) := by
  haveI : Module.Finite Γ(XA, V) (Γ(XA, V) ⊗[A] B) := inferInstance
  exact Module.Finite.equiv (R := Γ(XA, V)) (M := Γ(XA, V) ⊗[A] B)
    (Over.pieceTensorAlgEquiv C hV).toLinearEquiv

/-- **The moving lemma** ((C2) effectivity, brick E4 piece selection): for a
module-finite cover `A → B`, every point of the base curve has an affine open
neighbourhood `V` on which a prescribed Čech Picard class of the cover curve
restricts trivially to `cg⁻¹ V`. -/
theorem exists_isAffineOpen_cechPicMap_preimage_eq_one [Module.Finite A B]
    (L : (XB).CechPic) (x : XA) :
    ∃ V : (XA).Opens, IsAffineOpen V ∧ x ∈ V ∧
      Scheme.CechPic.map (Scheme.Opens.ι ((cg) ⁻¹ᵁ V)) L = 1 := by
  classical
  -- the ambient `cg`-saturated affine piece
  obtain ⟨V₀, hV₀, hpre₀, hx₀, -⟩ :=
    Over.exists_isAffineOpen_cg_le (A := A) (B := B) C x
      (V := (⊤ : (XA).Opens)) trivial
  -- the piece ring is module-finite, hence quasi-finite, over the base piece
  haveI := finite_pieceCover (B := B) C hV₀
  haveI : Algebra.QuasiFinite Γ(XA, V₀) Γ(XB, (cg) ⁻¹ᵁ V₀) := inferInstance
  -- the germ prime of `x` on the base piece
  set p : Ideal Γ(XA, V₀) :=
    Ideal.comap ((XA).presheaf.germ V₀ x hx₀).hom
      (IsLocalRing.maximalIdeal ((XA).presheaf.stalk x)) with hp
  haveI : p.IsPrime := Ideal.IsPrime.comap _
  -- the fiber primes over `p` form a finite set
  set pP : PrimeSpectrum Γ(XA, V₀) := ⟨p, inferInstance⟩
  have hfib : (PrimeSpectrum.comap
      (algebraMap Γ(XA, V₀) Γ(XB, (cg) ⁻¹ᵁ V₀)) ⁻¹' {pP}).Finite :=
    Algebra.QuasiFinite.finite_comap_preimage_singleton pP
  haveI := hfib.to_subtype
  -- the avoidance brick at the fiber primes
  haveI : ∀ Q : ↥(PrimeSpectrum.comap
      (algebraMap Γ(XA, V₀) Γ(XB, (cg) ⁻¹ᵁ V₀)) ⁻¹' {pP}),
      (Q.1.asIdeal).IsPrime := fun Q => Q.1.2
  obtain ⟨f, hfq, hfree⟩ := Module.Invertible.exists_notMem_isUnit_free
    (((cg) ⁻¹ᵁ V₀).cechPicClass hpre₀ L).AsModule
    (fun Q : ↥(PrimeSpectrum.comap
      (algebraMap Γ(XA, V₀) Γ(XB, (cg) ⁻¹ᵁ V₀)) ⁻¹' {pP}) => Q.1.asIdeal)
  -- the algebraic tube: `f` divides the image of some `g ∉ p`
  obtain ⟨g, hgp, h, hgh⟩ := Algebra.exists_notMem_algebraMap_eq_mul
    (R := Γ(XB, (cg) ⁻¹ᵁ V₀)) p (f := f) (fun Q hQ hQc => by
      refine hfq ⟨⟨Q, hQ⟩, ?_⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact PrimeSpectrum.ext (by rw [PrimeSpectrum.comap_asIdeal]; exact hQc))
  refine ⟨(XA).basicOpen g, hV₀.basicOpen g, ?_, ?_⟩
  · -- `x` lies in the tube: `g ∉ p` means the germ of `g` at `x` is a unit
    rw [Scheme.mem_basicOpen (XA) g x hx₀]
    by_contra hnu
    exact hgp (by
      rw [hp, Ideal.mem_comap]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu))
  · -- triviality on the preimage: `cg⁻¹ D(g) = D(cg^♯ g) ≤ D(f)`
    have hpre : (cg) ⁻¹ᵁ ((XA).basicOpen g) = (XB).basicOpen (f * h) := by
      rw [Scheme.preimage_basicOpen]
      congr 1
      rw [← hgh]
      change ((cg).app V₀).hom g = ((cg).appLE V₀ ((cg) ⁻¹ᵁ V₀) le_rfl).hom g
      rw [Scheme.Hom.appLE_eq_app]
    have hle : (XB).basicOpen (f * h) ≤ (XB).basicOpen f := by
      rw [Scheme.basicOpen_mul]
      exact inf_le_left
    rw [hpre]
    refine Scheme.cechPicMap_ι_eq_one_of_le hle L ?_
    exact Scheme.Opens.cechPicMap_ι_eq_one_of_cechPicClass_eq_one (hpre₀.basicOpen f)
      (Scheme.Opens.cechPicClass_basicOpen_eq_one_of_free hpre₀ L f hfree)

end Over

end AlgebraicGeometry
