/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Std.Tactic.BVDecide.LRAT.Internal.Clause

/-!
# Universal global sections of a proper geometrically integral curve (campaign `B0`)

This file supplies the **field of constants** substrate for the FGA Picard-scheme
representability campaign (`instHasPicScheme`, milestone `B0` of
`informal/pic-representability-campaign.md`).

For a curve `C` over a field `k` that is **proper** and **geometrically integral**,
the ring of global sections `Γ(C, 𝒪_C)` is:

* a **field** (`isField_globalSections`, Stacks `0BUG`(1); Mathlib
  `isField_of_universallyClosed`), because a proper morphism is universally closed
  and `C` is integral;
* **finite-dimensional** over `k` (`finiteDimensional_globalSections`; Mathlib
  `finite_appTop_of_universallyClosed`), because a proper morphism is locally of
  finite type — so `Γ(C, 𝒪_C)` is a *finite field extension* of `k`.

The sharp statement that this finite field extension is **trivial** — i.e.
`Γ(C, 𝒪_C) = k` — is the content Kleiman/Milne use to build canonical divisors and
rigidified representatives (campaign `B1`, `B3`-corollary, `B6`, `J1`, `G3`).  Over
`k` it is equivalent to `k` being the *field of constants* of `C`.  We isolate the
content in the `Prop`-class `HasTrivialConstants` and prove the `k`-algebra
isomorphism `Γ(C, 𝒪_C) ≃ₐ[k] k` from it (`globalSectionsAlgEquivBase`).

**`HasTrivialConstants` is now UNCONDITIONAL** (`instHasTrivialConstants`, this file):
the honest input — degree-zero H⁰ flat base change `Γ(C_{k̄}, 𝒪) ≅ k̄ ⊗_k Γ(C, 𝒪)` —
is already provided by Mathlib v4.31 as the qcqs `pushoutSection` engine
(`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`, `Morphisms/Flat.lean`).
Over the field base the base-change morphism `Spec k̄ → Spec k` is automatically flat
and `C` is qcqs (proper), so base change to the algebraically closed `k̄` (where
`Γ(C_{k̄}, 𝒪) = k̄`, `instHasTrivialConstants_of_isAlgClosed`) plus a `finrank` count
forces `Γ(C, 𝒪_C) = k`.  Consequently `globalSectionsAlgEquivBase` is now
**unconditional** (the `[HasTrivialConstants C]` binder auto-synthesises from
`[IsProper C.hom] [GeometricallyIntegral C.hom]`).

Campaign reference: milestone `B0` of `informal/pic-representability-campaign.md`
(Part V wave landing; Kleiman §2 uses `Γ(C, 𝒪) = k` implicitly throughout the
rigidification of `Pic^♯`).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-! ## The `k`-algebra structure on the global sections `Γ(C, 𝒪_C)` -/

/-- The structural ring map `k → Γ(C, 𝒪_C)` of a `k`-curve `C`, obtained from the
structure morphism `C.hom : C ⟶ Spec k` on global sections, transported across
`Γ(Spec k, ⊤) ≅ k`. -/
noncomputable def constMap (C : Over (Spec (CommRingCat.of k))) :
    CommRingCat.of k ⟶ Γ(C.left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.hom.appTop

/-- The `k`-algebra structure on `Γ(C, 𝒪_C)` induced by the structure morphism. -/
noncomputable scoped instance globalSectionsAlgebra (C : Over (Spec (CommRingCat.of k))) :
    Algebra k Γ(C.left, ⊤) :=
  (constMap C).hom.toAlgebra

lemma algebraMap_globalSections (C : Over (Spec (CommRingCat.of k))) :
    algebraMap k Γ(C.left, ⊤) = (constMap C).hom := rfl

/-! ## `Γ(C, 𝒪_C)` is a finite field extension of `k` -/

/-- `C` proper + geometrically integral over the one-point base `Spec k` is an
integral scheme. -/
instance isIntegral_left_of_geometricallyIntegral (C : Over (Spec (CommRingCat.of k)))
    [GeometricallyIntegral C.hom] : IsIntegral C.left := by
  haveI : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : IsIntegral (Spec (CommRingCat.of k)) :=
    haveI : IsDomain ↑(CommRingCat.of k) := inferInstanceAs (IsDomain k)
    inferInstance
  exact GeometricallyIntegral.isIntegral_of_subsingleton C.hom

/-- **`Γ(C, 𝒪_C)` is a field.**  For a proper geometrically integral curve `C/k`,
the ring of global sections is a field (Stacks `0BUG`; Mathlib
`isField_of_universallyClosed`, valid because proper ⟹ universally closed and `C`
is integral). -/
theorem isField_globalSections (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom] :
    IsField Γ(C.left, ⊤) :=
  isField_of_universallyClosed k C.hom

/-- The structure map `k → Γ(C, 𝒪_C)` is module-finite (Mathlib
`finite_appTop_of_universallyClosed`, valid because proper ⟹ locally of finite
type).  `constMap C = (ΓSpecIso).inv ≫ appTop` and both factors are finite (the
first is an isomorphism). -/
theorem finite_constMap (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom] :
    (constMap C).hom.Finite := by
  have hf : (C.hom.appTop.hom).Finite :=
    AlgebraicGeometry.finite_appTop_of_universallyClosed k C.hom
  have hbij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv
  have hiso : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).Finite :=
    RingHom.Finite.of_surjective _ hbij.2
  have hcomp : (constMap C).hom
      = (C.hom.appTop.hom).comp ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) := by
    simp [constMap]
  rw [hcomp]; exact hf.comp hiso

/-- **`Γ(C, 𝒪_C)` is finite-dimensional over `k`.**  Combined with
`isField_globalSections`, this exhibits `Γ(C, 𝒪_C)` as a *finite field extension*
of `k`. -/
theorem finiteDimensional_globalSections (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom] :
    Module.Finite k Γ(C.left, ⊤) :=
  finite_constMap C

/-! ## `Γ(C, 𝒪_C) = k` under the field-of-constants gate -/

/-- **Field-of-constants gate** (`B0`).  The structure map `k → Γ(C, 𝒪_C)`
is surjective — equivalently, `k` is the field of constants of `C`.  Together with
`isField_globalSections` this is `Γ(C, 𝒪_C) = k`.

The global instance `instHasTrivialConstants` (below) discharges this
**unconditionally** for proper geometrically integral `C/k`, via H⁰ flat base change
to `k̄`.  The class is kept as the reusable interface (mirroring `IsConstantField`),
and for the geometric semantics: `C_{k̄}` integral (geometric integrality) forces the
finite extension `Γ(C, 𝒪)/k` to be both separable — from geometric reducedness — and
to remain a domain after `⊗ k̄` — from geometric irreducibility — hence trivial. -/
class HasTrivialConstants (C : Over (Spec (CommRingCat.of k))) : Prop where
  surjective_constMap : Function.Surjective (constMap C).hom

/-- **`Γ(C, 𝒪_C) ≃ₐ[k] k`.**  Under the field-of-constants gate, the finite field
extension `Γ(C, 𝒪_C)/k` is trivial: the structure map is a `k`-algebra
isomorphism.  (Injectivity is automatic — `k` is a field and `Γ(C, 𝒪_C)` is
nonzero.) -/
noncomputable def globalSectionsAlgEquivBase (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom] [HasTrivialConstants C] :
    Γ(C.left, ⊤) ≃ₐ[k] k := by
  haveI : Nontrivial Γ(C.left, ⊤) := (isField_globalSections C).nontrivial
  have hinj : Function.Injective (algebraMap k Γ(C.left, ⊤)) :=
    (algebraMap k Γ(C.left, ⊤)).injective
  have hsurj : Function.Surjective (algebraMap k Γ(C.left, ⊤)) :=
    HasTrivialConstants.surjective_constMap
  exact (AlgEquiv.ofBijective (Algebra.ofId k Γ(C.left, ⊤)) ⟨hinj, hsurj⟩).symm

/-- **The field-of-constants gate is unconditional over an algebraically closed
base.**  A finite field extension of an algebraically closed field is trivial, so
`Γ(C, 𝒪_C) = k` needs no extra hypothesis when `k = k̄`
(`IsAlgClosed.algebraMap_bijective_of_isIntegral`).  This discharges
`HasTrivialConstants` in the geometric case `C_{k̄}` that the Milne route reduces
to (campaign `J`-cluster works over separably/algebraically closed `k'`). -/
instance instHasTrivialConstants_of_isAlgClosed (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom] [IsAlgClosed k] :
    HasTrivialConstants C := by
  letI : Field Γ(C.left, ⊤) := (isField_globalSections C).toField
  haveI : Module.Finite k Γ(C.left, ⊤) := finiteDimensional_globalSections C
  haveI : Algebra.IsIntegral k Γ(C.left, ⊤) := Algebra.IsIntegral.of_finite k _
  exact ⟨(IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
    (K := Γ(C.left, ⊤))).2⟩

/-! ## `Γ(C, 𝒪_C) = k` unconditionally, via H⁰ flat base change

The field-of-constants gate `HasTrivialConstants` is discharged **unconditionally** for a
proper geometrically integral curve `C/k` by base change to an algebraically closed
extension `K/k` (e.g. `K = k̄`) together with Mathlib's qcqs `H⁰` flat base-change engine
`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` (`Morphisms/Flat.lean`):

* the base-change morphism `Spec K → Spec k` is automatically flat (the base `Spec k` is a
  subsingleton integral scheme), and `C` is qcqs (proper), so the canonical map
  `Γ(Spec K, 𝒪) ⊗_{Γ(Spec k,𝒪)} Γ(C, 𝒪) → Γ(C_K, 𝒪)` is an isomorphism;
* over the algebraically closed `K`, `Γ(C_K, 𝒪) = K` (the already-available
  `instHasTrivialConstants_of_isAlgClosed`), so a `finrank` count over `Γ(Spec K, 𝒪)`
  forces `Γ(Spec k, 𝒪) → Γ(C, 𝒪)` to be an isomorphism, i.e. `Γ(C, 𝒪) = k`.

This is the campaign `B0`/wave-1 degree-zero H⁰ flat base-change brick (reused across `B2`,
`B3`, `B4`, `B5`, `D2'`); see `informal/pic-representability-campaign.md` Part III `C3`. -/

open TensorProduct Limits in
set_option backward.isDefEq.respectTransparency false in
/-- **H⁰ flat base change over a field base (structure sheaf).**  For a qcqs `k`-scheme `X`
(e.g. proper) and **any** `k`-algebra `A`, the canonical base-change map is a
`Γ(Spec A, 𝒪)`-algebra isomorphism
`Γ(Spec A, 𝒪) ⊗_{Γ(Spec k,𝒪)} Γ(X, 𝒪) ≅ Γ(X ×_k Spec A, 𝒪)`.

Over the field base `Spec k` the base-change morphism `Spec A → Spec k` is automatically flat
(`Spec k` is subsingleton integral), so Mathlib's qcqs `pushoutSection` engine
(`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`) applies; the `≃ₐ` is assembled from
`CommRingCat.isPushout_tensorProduct` exactly as `Mathlib/AlgebraicGeometry/Normalization.lean`.
The three source-ring `Algebra` instances (non-canonical — they come from the `appTop`/`appLE`
section maps) are supplied via `letI` in the return type.  Campaign `B0`/wave-1 item (iv). -/
noncomputable def globalSectionsBaseChangeAlgEquiv
    {X : Scheme.{u}} (iX : X ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type u) [CommRing A] [Algebra k A] :
    letI : Algebra ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(Spec (CommRingCat.of A), ⊤) :=
      ((Spec.map (CommRingCat.ofHom (algebraMap k A))).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Algebra ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(X, ⊤) := (iX.appTop).hom.toAlgebra
    letI : Algebra ↥Γ(Spec (CommRingCat.of A), ⊤)
        ↥Γ(pullback iX (Spec.map (CommRingCat.ofHom (algebraMap k A))), ⊤) :=
      ((pullback.snd iX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop).hom.toAlgebra
    ↥Γ(Spec (CommRingCat.of A), ⊤) ⊗[↥Γ(Spec (CommRingCat.of k), ⊤)] ↥Γ(X, ⊤)
      ≃ₐ[↥Γ(Spec (CommRingCat.of A), ⊤)]
      ↥Γ(pullback iX (Spec.map (CommRingCat.ofHom (algebraMap k A))), ⊤) := by
  let g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k A))
  have hU : IsAffineOpen (⊤ : (Spec (CommRingCat.of k)).Opens) := isAffineOpen_top _
  have hV : IsAffineOpen (⊤ : (Spec (CommRingCat.of A)).Opens) := isAffineOpen_top _
  have hthis := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback iX g) (le_top) (le_refl _) (UY := pullback.snd iX g ⁻¹ᵁ ⊤)
    (by simp) hU hV (iX.isCompact_preimage hU.isCompact)
    (iX.isQuasiSeparated_preimage hU.isQuasiSeparated)
  algebraize [(iX.appTop).hom, (g.appLE ⊤ ⊤ le_top).hom,
    ((pullback.snd iX g).appTop).hom]
  let e₀ := (CommRingCat.isPushout_tensorProduct
      (↥Γ(Spec (CommRingCat.of k), ⊤)) (↥Γ(Spec (CommRingCat.of A), ⊤))
      (↥Γ(X, ⊤))).flip.isoPushout ≪≫
    (pushout.congrHom iX.app_eq_appLE rfl ≪≫ @asIso _ _ _ _ _ hthis :)
  exact
    { toRingEquiv := e₀.commRingCatIsoToRingEquiv
      commutes' := fun r => by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e₀.hom) r =
          ((pullback.snd iX g).app ⊤) r
        congr 2
        simp [e₀, pushout.inr_desc_assoc, Scheme.Hom.app_eq_appLE] }

open TensorProduct Limits in
set_option backward.isDefEq.respectTransparency false in
/-- **Surjectivity of the field-of-constants map via base change to an algebraically closed
extension.**  For a proper geometrically integral curve `C/k` and any algebraically closed
field extension `K/k`, the structure map `k → Γ(C, 𝒪_C)` is surjective.  Proof: H⁰ flat base
change gives `Γ(Spec K, 𝒪) ⊗_{Γ(Spec k,𝒪)} Γ(C, 𝒪) ≅ Γ(C_K, 𝒪)`, and `Γ(C_K, 𝒪) = K` over
the algebraically closed `K` forces the `Γ(Spec k,𝒪)`-dimension of `Γ(C, 𝒪)` to be `1`. -/
theorem surjective_constMap_of_isAlgClosed_baseChange
    (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom]
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K] :
    Function.Surjective (constMap C).hom := by
  classical
  let g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  haveI hpq : IsProper (pullback.snd C.hom g) := inferInstance
  haveI hgiq : GeometricallyIntegral (pullback.snd C.hom g) := inferInstance
  haveI : IsProper (Over.mk (pullback.snd C.hom g)).hom := hpq
  haveI : GeometricallyIntegral (Over.mk (pullback.snd C.hom g)).hom := hgiq
  have hVU : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤ g ⁻¹ᵁ ⊤ := le_top
  have hU : IsAffineOpen (⊤ : (Spec (CommRingCat.of k)).Opens) := isAffineOpen_top _
  have hV : IsAffineOpen (⊤ : (Spec (CommRingCat.of K)).Opens) := isAffineOpen_top _
  have hthis := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback C.hom g) hVU (le_refl _) (UY := pullback.snd C.hom g ⁻¹ᵁ ⊤)
    (by simp) hU hV (C.hom.isCompact_preimage hU.isCompact)
    (C.hom.isQuasiSeparated_preimage hU.isQuasiSeparated)
  algebraize [(C.hom.appTop).hom, (g.appLE ⊤ ⊤ hVU).hom,
    ((pullback.snd C.hom g).appTop).hom]
  let e₀ := (CommRingCat.isPushout_tensorProduct
      (↥Γ(Spec (CommRingCat.of k), ⊤)) (↥Γ(Spec (CommRingCat.of K), ⊤))
      (↥Γ(C.left, ⊤))).flip.isoPushout ≪≫
    (pushout.congrHom C.hom.app_eq_appLE rfl ≪≫ @asIso _ _ _ _ _ hthis :)
  let e : Γ(Spec (CommRingCat.of K), ⊤) ⊗[Γ(Spec (CommRingCat.of k), ⊤)] Γ(C.left, ⊤)
      ≃ₐ[Γ(Spec (CommRingCat.of K), ⊤)] Γ(pullback C.hom g, ⊤) :=
    { toRingEquiv := e₀.commRingCatIsoToRingEquiv
      commutes' := fun r => by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e₀.hom) r =
          ((pullback.snd C.hom g).app ⊤) r
        congr 2
        simp [e₀, pushout.inr_desc_assoc, Scheme.Hom.app_eq_appLE] }
  -- The section rings of the affine bases `Spec k`, `Spec K` are fields.
  letI : Field ↥Γ(Spec (CommRingCat.of k), ⊤) :=
    (MulEquiv.isField (Field.toIsField k)
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv).toField
  letI : Field ↥Γ(Spec (CommRingCat.of K), ⊤) :=
    (MulEquiv.isField (Field.toIsField K)
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv).toField
  -- `Γ(C_K, 𝒪)` is a field and `Γ(Spec K,𝒪) → Γ(C_K,𝒪)` is bijective (`K` alg. closed).
  haveI : Nontrivial Γ(pullback C.hom g, ⊤) :=
    (isField_globalSections (k := K) (Over.mk (pullback.snd C.hom g))).nontrivial
  have hsurjK : Function.Surjective ⇑((pullback.snd C.hom g).appTop).hom := by
    have hh := (instHasTrivialConstants_of_isAlgClosed (k := K)
      (Over.mk (pullback.snd C.hom g))).surjective_constMap
    rw [show constMap (Over.mk (pullback.snd C.hom g))
        = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (pullback.snd C.hom g).appTop from rfl,
      CommRingCat.hom_comp, RingHom.coe_comp] at hh
    exact hh.of_comp
  have hM1 : Module.finrank ↥Γ(Spec (CommRingCat.of K), ⊤) ↥Γ(pullback C.hom g, ⊤) = 1 := by
    rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
    exact ⟨(algebraMap ↥Γ(Spec (CommRingCat.of K), ⊤)
      ↥Γ(pullback C.hom g, ⊤)).injective, hsurjK⟩
  -- Transport the finrank through base change and the iso `e`.
  have hbc : Module.finrank ↥Γ(Spec (CommRingCat.of K), ⊤)
      (↥Γ(Spec (CommRingCat.of K), ⊤) ⊗[↥Γ(Spec (CommRingCat.of k), ⊤)] ↥Γ(C.left, ⊤))
      = Module.finrank ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(C.left, ⊤) :=
    Module.finrank_baseChange
  have he : Module.finrank ↥Γ(Spec (CommRingCat.of K), ⊤)
      (↥Γ(Spec (CommRingCat.of K), ⊤) ⊗[↥Γ(Spec (CommRingCat.of k), ⊤)] ↥Γ(C.left, ⊤))
      = Module.finrank ↥Γ(Spec (CommRingCat.of K), ⊤) ↥Γ(pullback C.hom g, ⊤) :=
    e.toLinearEquiv.finrank_eq
  have hL1 : Module.finrank ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(C.left, ⊤) = 1 := by
    rw [← hbc, he, hM1]
  rw [Algebra.finrank_eq_one_iff_bijective_algebraMap] at hL1
  -- Conclude: `constMap C = ΓSpecIso.inv ≫ C.hom.appTop` is surjective.
  have hbij : Function.Bijective ⇑(C.hom.appTop).hom := hL1
  change Function.Surjective
    ⇑((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.hom.appTop).hom
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  exact hbij.surjective.comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).surjective

/-- **`Γ(C, 𝒪_C) = k` unconditionally** — the field-of-constants gate `HasTrivialConstants`
is discharged for every proper geometrically integral curve `C/k`, with no
algebraic-closedness or rational-point hypothesis, via H⁰ flat base change to `k̄`
(`surjective_constMap_of_isAlgClosed_baseChange` with `K = AlgebraicClosure k`).  This closes
the campaign `B0` residual, making `globalSectionsAlgEquivBase : Γ(C, 𝒪_C) ≃ₐ[k] k`
unconditional. -/
instance instHasTrivialConstants (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom] : HasTrivialConstants C :=
  ⟨surjective_constMap_of_isAlgClosed_baseChange C (AlgebraicClosure k)⟩

end AlgebraicGeometry.Scheme
