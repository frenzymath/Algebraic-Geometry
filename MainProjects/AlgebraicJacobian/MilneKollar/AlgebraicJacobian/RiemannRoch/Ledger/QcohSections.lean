/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.ModuleKSheaf
import AlgebraicJacobian.RiemannRoch.Ledger.AffineCech

/-!
# Quasi-coherence packaging for sheaves of modules on the small Zariski site

For a scheme `X`, an open `U`, and a sheaf `F` of `k`-modules on the small Zariski site
of `X`, this file packages the two properties of the structure sheaf that drive Serre's
affine degree-one vanishing argument (`AlgebraicJacobian.Cohomology.AffineVanishing`), so
that the argument can be run for general coefficient sheaves
(`AlgebraicJacobian.Cohomology.AffineVanishingQcoh`). The packaging is the class
`AlgebraicGeometry.Scheme.QcohOn F U`, providing:

* **(P1) action** — a scaling operation `QcohOn.qsmul : Γ(X, U) → F(W) → F(W)` for every
  open `W ≤ U`, satisfying the module laws over the fixed ring `Γ(X, U)` and natural
  under restriction of `F`-sections (`QcohOn.secRes_qsmul`). This is a sections-level
  "sheaf of `𝒪`-modules" mixin, deliberately minimized: every scalar consumed by the
  Serre engine is (the restriction of) a section over the ambient affine `U`, so no
  per-open `Γ(X, W)`-module structure is demanded — the action is by the single ring
  `Γ(X, U)`, with the inclusion proof `W ≤ U` an explicit (proof-irrelevant) argument.
* **(P2) localization** — for every affine open `V ≤ U` and every `g ∈ Γ(X, U)`,
  sections of `F` localize away from `g` in the two-lemma form of `IsLocalization.Away`
  used by the partition-of-unity cobounding: a section of `F(V ⊓ D(g))` extends to `V`
  after scaling by a power of `g` (`QcohOn.exists_secRes_eq_qsmul_pow`, denominator
  clearing), and a section of `F(V)` restricting to zero on `V ⊓ D(g)` is killed by a
  power of `g` (`QcohOn.exists_qsmul_pow_eq_zero`, defect annihilation).

The two (P2) axioms are exactly `IsAffineOpen.exists_res_eq_pow_mul` and
`IsAffineOpen.exists_pow_mul_eq_zero_of_res_eq_zero`
(`AlgebraicJacobian.Cohomology.AffineCech`) with structure-sheaf sections replaced by
`F`-sections and multiplication replaced by the (P1) action; consequently the structure
sheaf `Scheme.moduleKSheaf` satisfies the packaging on every open
(`AlgebraicGeometry.Scheme.moduleKSheaf.instQcohOn`), with
`qsmul h r s = X.resHom h r * s`. Sheaves glued from unit cocycles on finite affine
trivializing covers (the twisted line bundles of the Wave-4 datum) satisfy it chartwise
by the same localization facts, transported along the chart trivializations.

The file also provides the public restriction operator `AlgebraicGeometry.secRes` on
sections of a sheaf of `k`-modules (the analogue of the file-local operator of
`AlgebraicJacobian.Cohomology.AffineVanishing`), with its composition and naturality
lemmas — the vocabulary in which both the packaging and the generalized vanishing engine
are stated.

## Implementation notes

The action is a bare operation with explicit module-law fields rather than a per-open
`Module Γ(X, W) F(W)` instance: on the carrier `Sheaf _ (ModuleCat k)` the instance form
generates `HSMul`/`Module` instance towers over the section types that defeat keyed
rewriting (`kabstract`) at `instances` transparency, while the bare form keeps every
rewrite in the engine keyed on the head `QcohOn.qsmul` and elaboration-deterministic.
For `F = X.moduleKSheaf k` the instance form would additionally risk a
`Semiring.toModule` diamond on `Γ(X, W)`. The inclusion-proof argument of `qsmul` is
proof-irrelevant, so terms differing only in the inclusion path are definitionally equal
(`Scheme.QcohOn.qsmul_proof_irrel` is `rfl`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

variable {k : Type u} [CommRing k] {X : Scheme.{u}}

section SecRes

variable (F G : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} k))

/-- Restriction of sections of a sheaf of `k`-modules on the small Zariski site of a
scheme along an inclusion of opens, as a `k`-linear map. The public analogue of the
restriction operator used file-locally in `AlgebraicJacobian.Cohomology.AffineVanishing`;
on the structure sheaf `X.moduleKSheaf k` it is `Scheme.resHom`
(`AlgebraicGeometry.secRes_moduleKSheaf`). -/
noncomputable def secRes {U V : X.Opens} (h : V ≤ U) :
    F.obj.obj (op U) →ₗ[k] F.obj.obj (op V) :=
  (F.obj.map (homOfLE h).op).hom

variable {F G}

@[simp]
lemma secRes_secRes {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : F.obj.obj (op U)) :
    secRes F h₂ (secRes F h₁ s) = secRes F (h₂.trans h₁) s := by
  have hcomp : F.obj.map (homOfLE h₁).op ≫ F.obj.map (homOfLE h₂).op =
      F.obj.map (homOfLE (h₂.trans h₁)).op := by
    rw [← F.obj.map_comp, ← op_comp, homOfLE_comp]
  calc secRes F h₂ (secRes F h₁ s)
      = ((F.obj.map (homOfLE h₁).op ≫ F.obj.map (homOfLE h₂).op)).hom s := rfl
    _ = secRes F (h₂.trans h₁) s := by rw [hcomp]; rfl

/-- Restriction along `U ≤ U` is the identity (for an arbitrary proof, which is
proof-irrelevant). -/
@[simp]
lemma secRes_self {U : X.Opens} (h : U ≤ U) (s : F.obj.obj (op U)) : secRes F h s = s := by
  have hid : (homOfLE h).op = 𝟙 (op U) := rfl
  calc secRes F h s = (F.obj.map (𝟙 (op U))).hom s := by rw [secRes, hid]
    _ = s := by rw [F.obj.map_id]; rfl

/-- Naturality of section restriction in the sheaf: components of a morphism of sheaves
of modules commute with restriction. -/
lemma secRes_naturality (φ : F ⟶ G) {U V : X.Opens} (h : V ≤ U) (s : F.obj.obj (op U)) :
    (φ.hom.app (op V)).hom (secRes F h s) = secRes G h ((φ.hom.app (op U)).hom s) := by
  have hnat := congrArg ModuleCat.Hom.hom (φ.hom.naturality (homOfLE h).op)
  exact DFunLike.congr_fun hnat s

/-- On the structure sheaf as a sheaf of `k`-modules, `secRes` is restriction of scheme
sections. -/
lemma secRes_moduleKSheaf [X.Over (Spec (.of k))] {U V : X.Opens} (h : V ≤ U)
    (s : Γ(X, U)) :
    secRes (X.moduleKSheaf k) h s = X.resHom h s := rfl

end SecRes

/-- **Quasi-coherence packaging** of a sheaf `F` of `k`-modules on an open `U` of a
scheme `X`: an action of the fixed section ring `Γ(X, U)` on the `F`-sections over each
open `W ≤ U`, natural under restriction (the (P1) mixin), together with localization of
`F`-sections away from `g ∈ Γ(X, U)` on affine opens `V ≤ U`, in the two-lemma form of
`IsLocalization.Away` (the (P2) axioms). This is exactly the data consumed by Serre's
affine degree-one vanishing argument
(`IsAffineOpen.subsingleton_hModule'_one_of_qcoh`,
`AlgebraicJacobian.Cohomology.AffineVanishingQcoh`).

The structure sheaf satisfies the packaging on every open
(`Scheme.moduleKSheaf.instQcohOn`); sheaves trivialized on an affine chart `U` (the
Wave-4 twisted line bundles) satisfy it chart by chart. -/
class Scheme.QcohOn (F : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} k))
    (U : X.Opens) where
  /-- The action of an ambient section `r ∈ Γ(X, U)` on `F`-sections over `W ≤ U`. -/
  qsmul {W : X.Opens} (hWU : W ≤ U) : Γ(X, U) → F.obj.obj (op W) → F.obj.obj (op W)
  /-- The action of `1`. -/
  one_qsmul {W : X.Opens} (hWU : W ≤ U) (m : F.obj.obj (op W)) : qsmul hWU 1 m = m
  /-- The action of a product. -/
  mul_qsmul {W : X.Opens} (hWU : W ≤ U) (r s : Γ(X, U)) (m : F.obj.obj (op W)) :
    qsmul hWU (r * s) m = qsmul hWU r (qsmul hWU s m)
  /-- The action distributes over addition of scalars. -/
  add_qsmul {W : X.Opens} (hWU : W ≤ U) (r s : Γ(X, U)) (m : F.obj.obj (op W)) :
    qsmul hWU (r + s) m = qsmul hWU r m + qsmul hWU s m
  /-- The action distributes over addition of sections. -/
  qsmul_add {W : X.Opens} (hWU : W ≤ U) (r : Γ(X, U)) (m n : F.obj.obj (op W)) :
    qsmul hWU r (m + n) = qsmul hWU r m + qsmul hWU r n
  /-- The action is natural under restriction of `F`-sections. -/
  secRes_qsmul {V W : X.Opens} (hVW : V ≤ W) (hWU : W ≤ U) (r : Γ(X, U))
      (m : F.obj.obj (op W)) :
    secRes F hVW (qsmul hWU r m) = qsmul (hVW.trans hWU) r (secRes F hVW m)
  /-- **(P2) denominator clearing** on affine opens of `U`: a section of `F` over
  `V ⊓ D(g)` becomes the restriction of a section over `V` after scaling by a power
  of `g`. -/
  exists_secRes_eq_qsmul_pow {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
      (g : Γ(X, U)) (c : F.obj.obj (op (V ⊓ X.basicOpen g))) :
      ∃ (N : ℕ) (e : F.obj.obj (op V)),
        secRes F inf_le_left e =
          qsmul ((inf_le_left : V ⊓ X.basicOpen g ≤ V).trans hVU) (g ^ N) c
  /-- **(P2) defect annihilation** on affine opens of `U`: a section of `F` over `V`
  restricting to zero on `V ⊓ D(g)` is killed by a power of `g`. -/
  exists_qsmul_pow_eq_zero {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
      (g : Γ(X, U)) (t : F.obj.obj (op V))
      (ht : secRes F (inf_le_left : V ⊓ X.basicOpen g ≤ V) t = 0) :
      ∃ M : ℕ, qsmul hVU (g ^ M) t = 0

namespace Scheme.QcohOn

variable {F : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} k)}
  {U : X.Opens} [Scheme.QcohOn F U] {W : X.Opens}

/-- The inclusion-proof argument of the action is proof-irrelevant. -/
lemma qsmul_proof_irrel (h₁ h₂ : W ≤ U) (r : Γ(X, U)) (m : F.obj.obj (op W)) :
    qsmul h₁ r m = qsmul h₂ r m := rfl

/-- The action of a scalar on the zero section. -/
lemma qsmul_zero (hWU : W ≤ U) (r : Γ(X, U)) :
    qsmul hWU r (0 : F.obj.obj (op W)) = 0 := by
  have h := qsmul_add hWU r (0 : F.obj.obj (op W)) 0
  rw [add_zero] at h
  have h2 : qsmul hWU r (0 : F.obj.obj (op W)) + 0 =
      qsmul hWU r (0 : F.obj.obj (op W)) + qsmul hWU r 0 := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h2).symm

/-- The action distributes over subtraction of sections. -/
lemma qsmul_sub (hWU : W ≤ U) (r : Γ(X, U)) (m n : F.obj.obj (op W)) :
    qsmul hWU r (m - n) = qsmul hWU r m - qsmul hWU r n := by
  rw [eq_sub_iff_add_eq, ← qsmul_add, sub_add_cancel]

/-- The action of a finite sum of scalars. -/
lemma sum_qsmul {ι : Type*} (s : Finset ι) (hWU : W ≤ U) (c : ι → Γ(X, U))
    (m : F.obj.obj (op W)) :
    qsmul hWU (∑ i ∈ s, c i) m = ∑ i ∈ s, qsmul hWU (c i) m :=
  map_sum (AddMonoidHom.mk' (fun r ↦ qsmul hWU r m) fun r r' ↦ add_qsmul hWU r r' m) c s

end Scheme.QcohOn

section StructureSheaf

/-! ### The structure sheaf satisfies the packaging

`Scheme.moduleKSheaf k` carries the tautological action `qsmul h r s = X.resHom h r * s`
of ambient sections, natural under restriction since restriction is a ring homomorphism;
the localization axioms are the landed affine-open localization lemmas of
`AlgebraicJacobian.Cohomology.AffineCech`. This instance recovers the landed
structure-sheaf vanishing (`IsAffineOpen.subsingleton_moduleKSheaf_hModule'_one`) as a
special case of the generalized engine. -/

variable [X.Over (Spec (.of k))]

/-- Reinterpret a section of `X.moduleKSheaf k` over `W` as a scheme section in
`Γ(X, W)`. The two types are definitionally equal; this identity bridge pins the
`Γ`-spelling so that ring operations elaborate without coercion noise. -/
private def moduleKSheafToΓ {W : X.Opens} (s : (X.moduleKSheaf k).obj.obj (op W)) :
    Γ(X, W) := s

/-- The structure sheaf as a sheaf of `k`-modules is quasi-coherently packaged on every
open `U`: ambient sections act by restriction-then-multiplication, and the localization
axioms are `IsAffineOpen.exists_res_eq_pow_mul` and
`IsAffineOpen.exists_pow_mul_eq_zero_of_res_eq_zero`. -/
noncomputable instance Scheme.moduleKSheaf.instQcohOn (U : X.Opens) :
    Scheme.QcohOn (X.moduleKSheaf k) U where
  qsmul {W} hWU r s := X.resHom hWU r * moduleKSheafToΓ s
  one_qsmul {W} hWU m := by
    change X.resHom hWU 1 * moduleKSheafToΓ m = moduleKSheafToΓ m
    rw [map_one, one_mul]
  mul_qsmul {W} hWU r s m := by
    change X.resHom hWU (r * s) * moduleKSheafToΓ m =
      X.resHom hWU r * (X.resHom hWU s * moduleKSheafToΓ m)
    rw [map_mul, mul_assoc]
  add_qsmul {W} hWU r s m := by
    change X.resHom hWU (r + s) * moduleKSheafToΓ m =
      X.resHom hWU r * moduleKSheafToΓ m + X.resHom hWU s * moduleKSheafToΓ m
    rw [map_add, add_mul]
  qsmul_add {W} hWU r m n :=
    mul_add (X.resHom hWU r) (moduleKSheafToΓ m) (moduleKSheafToΓ n)
  secRes_qsmul {V W} hVW hWU r m := by
    change X.resHom hVW (X.resHom hWU r * moduleKSheafToΓ m) =
      X.resHom (hVW.trans hWU) r * X.resHom hVW (moduleKSheafToΓ m)
    rw [map_mul, Scheme.resHom_resHom]
  exists_secRes_eq_qsmul_pow {V} hV hVU g c := by
    obtain ⟨N, e, he⟩ := hV.exists_res_eq_pow_mul hVU g (moduleKSheafToΓ c)
    refine ⟨N, e, ?_⟩
    change X.resHom inf_le_left e =
      X.resHom (inf_le_left.trans hVU) (g ^ N) * moduleKSheafToΓ c
    rw [map_pow]
    exact he
  exists_qsmul_pow_eq_zero {V} hV hVU g t ht := by
    obtain ⟨M, hM⟩ := hV.exists_pow_mul_eq_zero_of_res_eq_zero hVU g
      (moduleKSheafToΓ t) ht
    refine ⟨M, ?_⟩
    change X.resHom hVU (g ^ M) * moduleKSheafToΓ t = 0
    rw [map_pow]
    exact hM

/-- On the structure sheaf, the packaged action is restriction-then-multiplication. -/
lemma Scheme.moduleKSheaf_qsmul_eq {U W : X.Opens} (hWU : W ≤ U) (r : Γ(X, U))
    (s : Γ(X, W)) :
    Scheme.QcohOn.qsmul (F := X.moduleKSheaf k) hWU r s = X.resHom hWU r * s := rfl

end StructureSheaf

end AlgebraicGeometry
