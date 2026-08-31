/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowDirectLimit
import AlgebraicJacobian.Picard.DivSchemeHighWindowMulCompatibility

/-!
# Side-preserving transitions between high theta windows

The canonical sections `(1,t₁^s)` and `(t₀^s,1)` give transitions between
successive relative theta windows.  Their selected pinned-chart component is
`1`, so the corresponding chart readings are unchanged.  This file records
the linear maps and their directed-system identities; relation-submodule
compatibility is intentionally kept as a separate hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 8000

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section RelativeTransition

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

noncomputable local instance instOverCleftHighWindowTransitions :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

/-- Multiplication on the left by a fixed relative theta section is linear in
the second factor. -/
noncomputable def relThetaSectionsMulLeft (a b : Nat)
    (s : relThetaSections C R pi a) :
    relThetaSections C R pi b →ₗ[R] relThetaSections C R pi (a + b) :=
  { toFun := fun t => relThetaSectionsMul C R pi a b s t
    map_add' := by
      intro x y
      apply Subtype.ext
      ext <;> simp [relThetaSectionsMul] <;> ring
    map_smul' := by
      intro r x
      apply Subtype.ext
      ext <;> simp [relThetaSectionsMul, Scheme.overModule_smul_def] <;> ring }

@[simp]
theorem relThetaSectionsMulLeft_apply (a b : Nat)
    (s : relThetaSections C R pi a)
    (x : relThetaSections C R pi b) :
    relThetaSectionsMulLeft C R pi a b s x =
      relThetaSectionsMul C R pi a b s x := rfl

/-- The canonical theta section whose component on the selected pinned chart is
`1`: `(1,t₁^a)` on chart `0`, and `(t₀^a,1)` on chart `1`. -/
noncomputable def relThetaSideUnitSection (side : Bool) (a : Nat) :
    relThetaSections C R pi a :=
  match side with
  | false => relThetaSectionSnd C R pi a
  | true => relThetaSectionFst C R pi a

@[simp]
theorem relThetaResSide_relThetaSideUnit (side : Bool) (a : Nat) :
    relThetaResSide a side le_rfl (relThetaSideUnitSection C R pi side a) = 1 := by
  cases side
  · change relThetaResFst a (le_inf le_top le_rfl)
      (relThetaSectionSnd C R pi a) = 1
    exact relThetaResFst_relThetaSectionSnd C R pi a
  · change relThetaResSnd a (le_inf le_top le_rfl)
      (relThetaSectionFst C R pi a) = 1
    exact relThetaResSnd_relThetaSectionFst C R pi a

/-- Multiply a theta section by the selected-side unit section. -/
noncomputable def relThetaSideTransition (side : Bool) (p s : Nat) :
    relThetaSections C R pi p →ₗ[R] relThetaSections C R pi (s + p) :=
  relThetaSectionsMulLeft C R pi s p (relThetaSideUnitSection C R pi side s)

@[simp]
theorem relThetaResSide_relThetaSideTransition (side : Bool) (p s : Nat)
    (x : relThetaSections C R pi p) :
    relThetaResSide (s + p) side le_rfl
        (relThetaSideTransition C R pi side p s x) =
      relThetaResSide p side le_rfl x := by
  rw [relThetaSideTransition, relThetaSectionsMulLeft_apply,
    relThetaResSide_relThetaSectionsMul]
  rw [relThetaResSide_relThetaSideUnit]
  simp

end RelativeTransition

namespace HighWindowTransitionKit

section IteratedSuccessor

variable {R : Type u} [Semiring R]
variable (G : Nat → Type u) [∀ n, AddCommMonoid (G n)]
  [∀ n, Module R (G n)]
variable (step : ∀ n, G n →ₗ[R] G (n + 1))
variable {B : Type u}

/-- Transport along an equality of indices in an arbitrary family of modules. -/
def reindex (i j : Nat) (h : i = j) : G i ≃ₗ[R] G j := by
  subst j
  exact LinearEquiv.refl R (G i)

@[simp]
theorem reindex_self (i : Nat) (h : i = i) :
    reindex (R := R) G i i h = LinearEquiv.refl R (G i) := by
  have hproof : h = rfl := Subsingleton.elim _ _
  rw [hproof]
  rfl

/-- Transport commutes with one successor map. -/
theorem step_comp_reindex (a j : Nat) (h : a = j) :
    (step j).comp (reindex (R := R) G a j h).toLinearMap =
      (reindex (R := R) G (a + 1) (j + 1)
        (congrArg Nat.succ h)).toLinearMap.comp (step a) := by
  subst j
  simp [reindex]

/-- Iteration of a successor-indexed family of linear maps. -/
def iterateSuccessor : (n d : Nat) → G n →ₗ[R] G (n + d)
  | _, 0 => LinearMap.id
  | n, d + 1 => (step (n + d)).comp (iterateSuccessor n d)

@[simp]
theorem iterateSuccessor_zero (n : Nat) :
    iterateSuccessor G step n 0 = LinearMap.id := rfl

@[simp]
theorem iterateSuccessor_succ (n d : Nat) :
    iterateSuccessor G step n (d + 1) =
      (step (n + d)).comp (iterateSuccessor G step n d) := rfl

/-- Reindexing an iterated successor map is independent of the chosen equal
distance expression. -/
theorem reindexedIterate_congr (i j d e : Nat) (hde : d = e)
    (hd : i + d = j) (he : i + e = j) (x : G i) :
    reindex (R := R) G (i + d) j hd (iterateSuccessor G step i d x) =
      reindex (R := R) G (i + e) j he (iterateSuccessor G step i e x) := by
  subst e
  have hproof : hd = he := Subsingleton.elim _ _
  rw [hproof]

/-- The transition between arbitrary comparable indices, obtained by iterating
successor maps through the distance and transporting to the target index. -/
noncomputable def transitionOfLE (i j : Nat) (h : i ≤ j) : G i →ₗ[R] G j :=
  (reindex (R := R) G (i + (j - i)) j (Nat.add_sub_of_le h)).toLinearMap.comp
    (iterateSuccessor G step i (j - i))

@[simp]
theorem transitionOfLE_self (i : Nat) (x : G i) :
    transitionOfLE G step i i le_rfl x = x := by
  unfold transitionOfLE
  rw [LinearMap.comp_apply]
  calc
    _ = reindex (R := R) G (i + 0) i (Nat.add_zero i)
        (iterateSuccessor G step i 0 x) :=
      reindexedIterate_congr (R := R) G step i i (i - i) 0
        (Nat.sub_self i) (Nat.add_sub_of_le le_rfl) (Nat.add_zero i) x
    _ = x := by
      change reindex (R := R) G i i _ x = x
      rw [reindex_self, LinearEquiv.refl_apply]

/-- Extending the target by one composes the transition with its successor map. -/
theorem transitionOfLE_succ (i j : Nat) (h : i ≤ j) :
    transitionOfLE G step i (j + 1) (Nat.le.step h) =
      (step j).comp (transitionOfLE G step i j h) := by
  apply LinearMap.ext
  intro x
  have hdist : j + 1 - i = (j - i) + 1 := by omega
  have htarget : i + ((j - i) + 1) = j + 1 := by omega
  have hnatural := LinearMap.congr_fun
    (step_comp_reindex (R := R) G step (i + (j - i)) j
      (Nat.add_sub_of_le h))
    (iterateSuccessor G step i (j - i) x)
  unfold transitionOfLE
  simp only [LinearMap.comp_apply]
  calc
    _ = reindex (R := R) G (i + ((j - i) + 1)) (j + 1) htarget
        (iterateSuccessor G step i ((j - i) + 1) x) :=
      reindexedIterate_congr (R := R) G step i (j + 1)
        (j + 1 - i) ((j - i) + 1) hdist
        (Nat.add_sub_of_le (Nat.le.step h)) htarget x
    _ = _ := by
      change reindex (R := R) G (i + (j - i) + 1) (j + 1) _
          (step (i + (j - i))
            (iterateSuccessor G step i (j - i) x)) =
        step j
          (reindex (R := R) G (i + (j - i)) j _
            (iterateSuccessor G step i (j - i) x))
      exact hnatural.symm

theorem transitionOfLE_read
    (read : ∀ n, G n → B)
    (hread : ∀ n (x : G n), read (n + 1) (step n x) = read n x)
    (i j : Nat) (h : i ≤ j) (x : G i) :
    read j (transitionOfLE G step i j h x) = read i x := by
  induction h with
  | refl =>
      rw [transitionOfLE_self]
  | @step m h ih =>
      rw [transitionOfLE_succ G step i m h, LinearMap.comp_apply, hread]
      exact ih

theorem transitionOfLE_map_map (i j l : Nat) (hij : i ≤ j) (hjl : j ≤ l)
    (x : G i) :
    transitionOfLE G step j l hjl
        (transitionOfLE G step i j hij x) =
      transitionOfLE G step i l (hij.trans hjl) x := by
  induction hjl with
  | refl =>
      have hproof : hij.trans Nat.le.refl = hij := Subsingleton.elim _ _
      rw [hproof, transitionOfLE_self]
  | @step m hjl ih =>
      rw [transitionOfLE_succ G step j m hjl, LinearMap.comp_apply, ih]
      have hproof :
          hij.trans (Nat.le.step hjl) = Nat.le.step (hij.trans hjl) :=
        Subsingleton.elim _ _
      rw [hproof, transitionOfLE_succ G step i m (hij.trans hjl),
        LinearMap.comp_apply]

theorem transitionOfLE_mem
    (K : (n : Nat) → Submodule R (G n))
    (hK : ∀ n (x : G n), x ∈ K n → step n x ∈ K (n + 1))
    (i j : Nat) (h : i ≤ j) (x : G i) (hx : x ∈ K i) :
    transitionOfLE G step i j h x ∈ K j := by
  induction h with
  | refl =>
      simpa only [transitionOfLE_self] using hx
  | @step m h ih =>
      rw [transitionOfLE_succ G step i m h, LinearMap.comp_apply]
      exact hK m _ ih

theorem map_transitionOfLE_le
    (K : (n : Nat) → Submodule R (G n))
    (hK : ∀ n (x : G n), x ∈ K n → step n x ∈ K (n + 1))
    (i j : Nat) (h : i ≤ j) :
    Submodule.map (transitionOfLE G step i j h) (K i) ≤ K j := by
  rintro _ ⟨x, hx, rfl⟩
  exact transitionOfLE_mem G step K hK i j h x hx

noncomputable instance directedSystem_transitionOfLE :
    DirectedSystem G (transitionOfLE G step · · ·) where
  map_self i x := transitionOfLE_self G step i x
  map_map k j i hij hjk x := transitionOfLE_map_map G step i j k hij hjk x

end IteratedSuccessor

end HighWindowTransitionKit

end AlgebraicGeometry
