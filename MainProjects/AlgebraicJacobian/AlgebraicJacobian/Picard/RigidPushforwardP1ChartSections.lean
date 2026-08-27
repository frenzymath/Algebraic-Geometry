/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RigidPushforwardP1ChartRing

/-!
# The chart section rings of `ℙ¹_k` are polynomial rings

Let `k` be a field and `ℙ¹_k = ℙ(ULift (Fin 2); Spec k)` the concrete projective line of
`Picard/ProjectiveSpace.lean` (the `Proj`-pullback model), with its two standard charts
`Vᵢ = p1Chart k i = toProjInt ⁻¹ᵁ D₊(Xᵢ)` and chart coordinates `x = X₁/X₀ ∈ Γ(V₀)`,
`y = X₀/X₁ ∈ Γ(V₁)` (`Adelic.p1XSection`, `Adelic.p1YSection` of
`RiemannRoch/Adelic/P1ChartData.lean`).  This file upgrades the *spanning* statements
`Adelic.span_pow_p1XSection_scaffold`/`span_pow_p1YSection_scaffold` — the powers of the
coordinate `k`-span the chart ring — to the *freeness* statement

`AlgebraicGeometry.Adelic.p1ChartSectionsAlgEquivX : Γ(ℙ¹_k, V₀) ≃ₐ[k] k[T]`, `x ↦ T`

and its `⟨1⟩`-mirror `p1ChartSectionsAlgEquivY`.

## The argument

Write `s := Polynomial.aeval x : k[T] →ₐ[k] Γ(V₀)`.

* **`s` is surjective** — this is exactly `span_pow_p1XSection_scaffold`: every section is a
  finite `k`-combination of powers of `x`, i.e. a value of `s`.
* **`s` is injective** — the new content.  It is exhibited as a *split* monomorphism by
  constructing a retraction `r : Γ(V₀) → k[T]` out of the `CommRingCat` pushout square

  ```
  Γ(⊤_Scheme, ⊤)  ──→  Γ(Proj ℤ[X₀,X₁], D₊(X₀))
        │                        │
        ↓                        ↓
  Γ(Spec k, ⊤)     ──→        Γ(ℙ¹_k, V₀)
  ```

  (`isPushout_p1ChartSections`, the affine fibre-product square of
  `AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen` applied to the defining pullback
  of `ℙ¹_k`, exactly as in `span_pow_p1XSection_scaffold`).  The two legs of `r` are
  * `p1ProjLeg`: `Γ(D₊(X₀)) ≅ (ℤ[X₀,X₁]_{X₀})₀ ≃ₐ ℤ[T] → k[T]`, using the *integral*
    chart-ring identification `Adelic.p1AwayAlgEquiv` of
    `AlgebraicJacobian.Picard.RigidPushforwardP1ChartRing`;
  * `p1SpecLeg`: `Γ(Spec k, ⊤) ≅ k → k[T]`, the constant embedding.

  They agree on the shared corner `Γ(⊤_Scheme, ⊤)` for free, because that ring is *initial*
  in `CommRingCat` (`gammaTerminalIsInitial`: it is `Γ(Spec (ULift ℤ), ⊤) ≅ ULift ℤ`).
  Then `r ∘ s = id` by `Polynomial.ringHom_ext`: `r` sends the coordinate `x` to `T` (it is
  the image of the away fraction `X₁/X₀` along the `Proj` leg, and
  `p1AwayAlgEquiv_p1CoordAway` computes it) and constants to constants (the `Spec k` leg).

Freeness is what the rigid-pushforward chart computations need: over a *free* rank-one module
there is no room for the correction terms a merely spanning family would allow, and `k[T]` is
a PID, which makes the fibre-chart classification of line bundles on `ℙ¹` available.

## Main results

* `AlgebraicGeometry.Adelic.isPushout_p1ChartSections` — the chart-section pushout square;
* `AlgebraicGeometry.Adelic.gammaTerminalIsInitial` — `Γ(⊤_Scheme, ⊤)` is initial;
* `AlgebraicGeometry.Adelic.p1ChartRetraction` — the retraction `Γ(ℙ¹_k, Vᵢ) ⟶ k[T]`;
* `AlgebraicGeometry.Adelic.p1ChartSectionsAlgEquivX`, `…AlgEquivY` — the chart identifications;
* `AlgebraicGeometry.Adelic.instIsDomainP1ChartSectionsX`, `…Y` — the chart rings are domains;
* `AlgebraicGeometry.Adelic.not_isNilpotent_p1XSection`, `…Y` — the coordinates are not
  nilpotent;
* `AlgebraicGeometry.Adelic.p1Chart_inf_ne_bot` — the two charts genuinely overlap.

## Implementation notes

The `k`-algebra structure on `Γ(ℙ¹_k, Vᵢ)` is the `Scheme.toModuleKSheaf.algebraSection`
structure, declared here as the `local` instance `instAlgebraΓp1Chart` in exactly the form used
by the `local` instances `instAlgebraΓV0`/`instAlgebraΓV1` of `P1ChartData.lean`, so that the
spanning scaffolds apply verbatim.

Everything except the two final identifications is stated generically in a pair of distinct
indices `i ≠ j`, so the `y`-chart costs no duplication.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.Adelic

section Initial

/-- `Γ(⊤_Scheme, ⊤)` is initial in `CommRingCat`. -/
noncomputable def gammaTerminalIsInitial :
    IsInitial Γ(⊤_ Scheme.{u}, (⊤ : (⊤_ Scheme.{u}).Opens)) :=
  CommRingCat.isInitial.ofIso
    ((Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).symm ≪≫
      Scheme.Γ.mapIso (terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal.{u}).op)

end Initial

section Pushout

open ProjectiveSpace

variable (k : Type u) [Field k]

set_option maxHeartbeats 800000 in
-- the affine-pushout machinery unifies the `ℙ¹` pullback through `MvPolynomial`; expensive
theorem isPushout_p1ChartSections (i : ULift.{u} (Fin 2)) :
    IsPushout
      ((terminal.from (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)))).appLE
        ⊤ (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)) le_top)
      ((terminal.from (Spec (CommRingCat.of k))).appLE ⊤ ⊤ (Scheme.Hom.preimage_top _).ge)
      ((toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).appLE
        (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i))
        (p1Chart k i) (le_refl _))
      ((ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).appLE
        ⊤ (p1Chart k i) le_top) := by
  have H : IsPullback
      (toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)))
      (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
      (terminal.from (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))))
      (terminal.from (Spec (CommRingCat.of k))) :=
    (IsPullback.of_hasPullback (terminal.from (Spec (CommRingCat.of k)))
      (terminal.from (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))))).flip
  have hUY : p1Chart k i
      = toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)) ⁻¹ᵁ
          Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)
        ⊓ (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) ⁻¹ᵁ ⊤ := by
    simp only [Scheme.Hom.preimage_top, inf_top_eq]
    rfl
  have hUST : (⊤ : (Spec (CommRingCat.of k)).Opens) ≤
      terminal.from (Spec (CommRingCat.of k)) ⁻¹ᵁ ⊤ := (Scheme.Hom.preimage_top _).ge
  have hUSX : Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i) ≤
      terminal.from (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))) ⁻¹ᵁ ⊤ :=
    le_top
  have hUS : IsAffineOpen (⊤ : (⊤_ Scheme.{u}).Opens) := isAffineOpen_top _
  have hUT : IsAffineOpen (⊤ : (Spec (CommRingCat.of k)).Opens) := isAffineOpen_top _
  have hUX : IsAffineOpen
      (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)) :=
    Proj.isAffineOpen_basicOpen _ _ (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) i) one_pos
  have hIso : IsIso (pushoutSection H hUST hUSX hUY) :=
    isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hUS hUT hUX
  exact (isIso_pushoutSection_iff H hUST hUSX hUY).mp hIso

/-- The `algebraSection` `k`-algebra structure on `Γ(ℙ¹, Vᵢ)`, re-declared exactly as the
`local` instance of `RiemannRoch/Adelic/P1ChartData.lean` so that the spanning scaffolds
`span_pow_p1XSection_scaffold`/`span_pow_p1YSection_scaffold` apply verbatim. -/
noncomputable local instance instAlgebraΓp1Chart (i : ULift.{u} (Fin 2)) :
    Algebra k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k i) :=
  Scheme.toModuleKSheaf.algebraSection
    (Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
    (op (p1Chart k i))

/-- The chart coordinate `Xⱼ/Xᵢ ∈ Γ(ℙ¹, Vᵢ)`, generic in the pair of indices:
`p1XSection = p1CoordSection ⟨0⟩ ⟨1⟩` and `p1YSection = p1CoordSection ⟨1⟩ ⟨0⟩`. -/
noncomputable def p1CoordSection (i j : ULift.{u} (Fin 2)) :
    Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k i) :=
  ((toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).app
      (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i))).hom
    ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (X i)).hom (p1CoordAway (ULift.{u} (Fin 2)) i j))

/-- The generic chart coordinate at `⟨0⟩, ⟨1⟩` is the `x`-coordinate `p1XSection`. -/
theorem p1CoordSection_zero_one : p1CoordSection k ⟨0⟩ ⟨1⟩ = p1XSection k := rfl

/-- The generic chart coordinate at `⟨1⟩, ⟨0⟩` is the `y`-coordinate `p1YSection`. -/
theorem p1CoordSection_one_zero : p1CoordSection k ⟨1⟩ ⟨0⟩ = p1YSection k := rfl

/-- **`aeval` at the chart coordinate is surjective**, given the spanning statement: an element
of the `k`-span of the powers of `Xⱼ/Xᵢ` is a `k`-combination of them, hence a polynomial in it.
The spanning hypothesis is `Adelic.span_pow_p1XSection_scaffold` (resp. its `y`-mirror). -/
theorem surjective_aeval_p1CoordSection {i j : ULift.{u} (Fin 2)}
    (hspan : (⊤ : Submodule k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k i)) ≤
      Submodule.span k (Set.range fun n : ℕ => p1CoordSection k i j ^ n)) :
    Function.Surjective (Polynomial.aeval (p1CoordSection k i j) :
      Polynomial k →ₐ[k] Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k i)) := by
  intro z
  have hz := hspan (Submodule.mem_top : z ∈ ⊤)
  induction hz using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨n, rfl⟩ := hw
      exact ⟨Polynomial.X ^ n, by rw [map_pow, Polynomial.aeval_X]⟩
  | zero => exact ⟨0, map_zero _⟩
  | add u v _ _ hu hv =>
      obtain ⟨p, rfl⟩ := hu
      obtain ⟨q, rfl⟩ := hv
      exact ⟨p + q, map_add _ _ _⟩
  | smul c u _ hu =>
      obtain ⟨p, rfl⟩ := hu
      exact ⟨c • p, map_smul _ _ _⟩

/-- The unique ring map `ULift ℤ → k`. -/
noncomputable def uliftIntCast : ULift.{u} ℤ →+* k :=
  (Int.castRingHom k).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom

/-- The `Proj`-leg of the retraction: `Γ(Proj ℤ[X₀,X₁], D₊(Xᵢ)) → k[T]`, the composite of the
affine chart identification `Γ(D₊(Xᵢ)) ≅ (ℤ[X₀,X₁]_{Xᵢ})₀`, the chart-ring identification
`p1AwayAlgEquiv : (ℤ[X₀,X₁]_{Xᵢ})₀ ≃ₐ[ℤ] ℤ[T]` and the coefficient map `ℤ[T] → k[T]`. -/
noncomputable def p1ProjLeg {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) :
    Γ(Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)),
        Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)) ⟶
      CommRingCat.of (Polynomial k) :=
  (Proj.basicOpenIsoAway (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)
      (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) i) one_pos).inv ≫
    CommRingCat.ofHom ((Polynomial.mapRingHom (uliftIntCast k)).comp
      (p1AwayAlgEquiv (ULift.{u} ℤ) hij : Away (homogeneousSubmodule (ULift.{u} (Fin 2))
        (ULift.{u} ℤ)) (X i) ≃ₐ[ULift.{u} ℤ] Polynomial (ULift.{u} ℤ)).toRingEquiv.toRingHom)

/-- The `Spec k`-leg of the retraction: `Γ(Spec k, ⊤) → k[T]`, the constant embedding. -/
noncomputable def p1SpecLeg :
    Γ(Spec (CommRingCat.of k), (⊤ : (Spec (CommRingCat.of k)).Opens)) ⟶
      CommRingCat.of (Polynomial k) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
    CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)

/-- **The retraction `Γ(ℙ¹, Vᵢ) → k[T]`.**  The two legs `p1ProjLeg`, `p1SpecLeg` agree on the
initial corner `Γ(⊤_Scheme, ⊤)` of the pushout square `isPushout_p1ChartSections` (any two ring
maps out of an initial object agree), so they descend. -/
noncomputable def p1ChartRetraction {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) :
    Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k i) ⟶
      CommRingCat.of (Polynomial k) :=
  (isPushout_p1ChartSections k i).desc (p1ProjLeg k hij) (p1SpecLeg k)
    (gammaTerminalIsInitial.hom_ext _ _)

/-- **The retraction kills the chart coordinate to the variable.**  `p1CoordSection i j` is the
image of the away fraction `Xⱼ/Xᵢ` under the `Proj`-leg of the pushout, which the chart-ring
identification `p1AwayAlgEquiv` sends to `T`. -/
theorem p1ChartRetraction_p1CoordSection {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) :
    (p1ChartRetraction k hij).hom (p1CoordSection k i j) = Polynomial.X := by
  have hbridge : (toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).appLE
        (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i))
        (p1Chart k i) (le_refl _)
      = (toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).app
          (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)) :=
    Scheme.Hom.appLE_eq_app _
  have hinl : (toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).appLE
        (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i))
        (p1Chart k i) (le_refl _) ≫ p1ChartRetraction k hij
      = p1ProjLeg k hij :=
    (isPushout_p1ChartSections k i).inl_desc _ _ _
  have h1 : (p1ChartRetraction k hij).hom (p1CoordSection k i j)
      = (p1ProjLeg k hij).hom
          ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
            (X i)).hom (p1CoordAway (ULift.{u} (Fin 2)) i j)) := by
    change (p1ChartRetraction k hij).hom
        (((toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).app
            (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i))).hom
          ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
            (X i)).hom (p1CoordAway (ULift.{u} (Fin 2)) i j))) = _
    rw [← hbridge, ← hinl]
    rfl
  have hiso : (Proj.basicOpenIsoAway (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (X i) (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) i) one_pos).inv.hom
        ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (X i)).hom (p1CoordAway (ULift.{u} (Fin 2)) i j))
      = p1CoordAway (ULift.{u} (Fin 2)) i j := by
    rw [← Proj.basicOpenIsoAway_hom (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
      (X i) (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) i) one_pos]
    exact (Proj.basicOpenIsoAway (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
      (X i) (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) i) one_pos).hom_inv_id_apply _
  rw [h1]
  change (Polynomial.mapRingHom (uliftIntCast k))
      ((p1AwayAlgEquiv (ULift.{u} ℤ) hij)
        ((Proj.basicOpenIsoAway (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (X i) (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) i) one_pos).inv.hom
          ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
            (X i)).hom (p1CoordAway (ULift.{u} (Fin 2)) i j)))) = Polynomial.X
  rw [hiso, p1AwayAlgEquiv_p1CoordAway hij]
  exact Polynomial.map_X _

/-- The `k`-algebra structure map of `Γ(ℙ¹, Vᵢ)` is the `Spec k`-leg of the pushout square,
precomposed with `ΓSpecIso.inv` (the `algebraSection` structure is by definition the
structure-morphism pullback). -/
theorem algebraMap_p1ChartSections (i : ULift.{u} (Fin 2)) (c : k) :
    algebraMap k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k i) c
      = ((ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).appLE
          ⊤ (p1Chart k i) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) := by
  have hcomp : Scheme.toModuleKSheaf.kToSection
        (Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
        (op (p1Chart k i))
      = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          Scheme.Hom.appLE
            (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
            ⊤ (p1Chart k i) le_top := rfl
  have e1 : algebraMap k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k i) c
      = (Scheme.toModuleKSheaf.kToSection
          (Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
          (op (p1Chart k i))).hom c := rfl
  rw [e1, hcomp]
  rfl

/-- **The retraction is `k`-linear on constants.** -/
theorem p1ChartRetraction_algebraMap {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) (c : k) :
    (p1ChartRetraction k hij).hom
        (algebraMap k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k i) c)
      = Polynomial.C c := by
  have hinr : (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).appLE
        ⊤ (p1Chart k i) le_top ≫ p1ChartRetraction k hij = p1SpecLeg k :=
    (isPushout_p1ChartSections k i).inr_desc _ _ _
  have h2 : ∀ z : Γ(Spec (CommRingCat.of k), (⊤ : (Spec (CommRingCat.of k)).Opens)),
      (p1ChartRetraction k hij).hom
          (((ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).appLE
            ⊤ (p1Chart k i) le_top).hom z)
        = (p1SpecLeg k).hom z :=
    fun z => congrArg (fun φ : Γ(Spec (CommRingCat.of k), (⊤ : (Spec (CommRingCat.of k)).Opens)) ⟶
      CommRingCat.of (Polynomial k) => φ.hom z) hinr
  rw [algebraMap_p1ChartSections, h2]
  change Polynomial.C ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) = Polynomial.C c
  rw [(Scheme.ΓSpecIso (CommRingCat.of k)).inv_hom_id_apply]

/-- **The retraction is a left inverse of `aeval (Xⱼ/Xᵢ)`.**  Two ring maps `k[T] → k[T]` agreeing
on constants and on `T` are equal. -/
theorem p1ChartRetraction_aeval {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) (p : Polynomial k) :
    (p1ChartRetraction k hij).hom
        (Polynomial.aeval (p1CoordSection k i j) p) = p := by
  have h : (p1ChartRetraction k hij).hom.comp
      ((Polynomial.aeval (p1CoordSection k i j) :
        Polynomial k →ₐ[k] Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)),
          p1Chart k i)) : Polynomial k →+* _) = RingHom.id (Polynomial k) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simpa only [RingHom.comp_apply, RingHom.id_apply, RingHom.coe_coe, Polynomial.aeval_C]
        using p1ChartRetraction_algebraMap k hij a
    · simpa only [RingHom.comp_apply, RingHom.id_apply, RingHom.coe_coe, Polynomial.aeval_X]
        using p1ChartRetraction_p1CoordSection k hij
  exact RingHom.congr_fun h p

/-! ### The chart identifications -/

/-- The two homogeneous coordinate indices of `ℙ¹` are distinct. -/
theorem p1Index_zero_ne_one : (⟨0⟩ : ULift.{u} (Fin 2)) ≠ ⟨1⟩ := by
  intro h
  simpa using congrArg ULift.down h

/-- The two homogeneous coordinate indices of `ℙ¹` are distinct (the other order). -/
theorem p1Index_one_ne_zero : (⟨1⟩ : ULift.{u} (Fin 2)) ≠ ⟨0⟩ := by
  intro h
  simpa using congrArg ULift.down h

/-- **`k[T] → Γ(ℙ¹_k, V₀)`, `T ↦ x`, is bijective**: surjective by the spanning scaffold,
injective because `p1ChartRetraction` is a left inverse. -/
theorem bijective_aeval_p1XSection :
    Function.Bijective (Polynomial.aeval (p1XSection k) :
      Polynomial k →ₐ[k] Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨0⟩)) := by
  rw [← p1CoordSection_zero_one]
  refine ⟨Function.LeftInverse.injective
    (g := ⇑(p1ChartRetraction k p1Index_zero_ne_one).hom)
    (p1ChartRetraction_aeval k p1Index_zero_ne_one), ?_⟩
  exact surjective_aeval_p1CoordSection k
    (by rw [p1CoordSection_zero_one]; exact span_pow_p1XSection_scaffold k)

/-- **`k[T] → Γ(ℙ¹_k, V₁)`, `T ↦ y`, is bijective** (mirror of `bijective_aeval_p1XSection`). -/
theorem bijective_aeval_p1YSection :
    Function.Bijective (Polynomial.aeval (p1YSection k) :
      Polynomial k →ₐ[k] Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨1⟩)) := by
  rw [← p1CoordSection_one_zero]
  refine ⟨Function.LeftInverse.injective
    (g := ⇑(p1ChartRetraction k p1Index_one_ne_zero).hom)
    (p1ChartRetraction_aeval k p1Index_one_ne_zero), ?_⟩
  exact surjective_aeval_p1CoordSection k
    (by rw [p1CoordSection_one_zero]; exact span_pow_p1YSection_scaffold k)

/-- **The first chart ring of `ℙ¹_k` is a polynomial ring.**  `Γ(ℙ¹_k, V₀) ≃ₐ[k] k[T]`, sending
the chart coordinate `x = X₁/X₀ = p1XSection k` to the variable `T`. -/
noncomputable def p1ChartSectionsAlgEquivX :
    Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨0⟩) ≃ₐ[k] Polynomial k :=
  (AlgEquiv.ofBijective (Polynomial.aeval (p1XSection k)) (bijective_aeval_p1XSection k)).symm

/-- **The second chart ring of `ℙ¹_k` is a polynomial ring.**  `Γ(ℙ¹_k, V₁) ≃ₐ[k] k[T]`, sending
the chart coordinate `y = X₀/X₁ = p1YSection k` to the variable `T`. -/
noncomputable def p1ChartSectionsAlgEquivY :
    Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨1⟩) ≃ₐ[k] Polynomial k :=
  (AlgEquiv.ofBijective (Polynomial.aeval (p1YSection k)) (bijective_aeval_p1YSection k)).symm

/-- The inverse chart identification sends the variable to the coordinate `x`. -/
@[simp]
theorem p1ChartSectionsAlgEquivX_symm_X :
    (p1ChartSectionsAlgEquivX k).symm Polynomial.X = p1XSection k := by
  rw [p1ChartSectionsAlgEquivX, AlgEquiv.symm_symm]
  exact Polynomial.aeval_X _

/-- The inverse chart identification sends the variable to the coordinate `y`. -/
@[simp]
theorem p1ChartSectionsAlgEquivY_symm_X :
    (p1ChartSectionsAlgEquivY k).symm Polynomial.X = p1YSection k := by
  rw [p1ChartSectionsAlgEquivY, AlgEquiv.symm_symm]
  exact Polynomial.aeval_X _

/-- **The chart identification pins the coordinate**: `x ↦ T`. -/
@[simp]
theorem p1ChartSectionsAlgEquivX_p1XSection :
    p1ChartSectionsAlgEquivX k (p1XSection k) = Polynomial.X := by
  rw [← p1ChartSectionsAlgEquivX_symm_X k, AlgEquiv.apply_symm_apply]

/-- **The chart identification pins the coordinate**: `y ↦ T`. -/
@[simp]
theorem p1ChartSectionsAlgEquivY_p1YSection :
    p1ChartSectionsAlgEquivY k (p1YSection k) = Polynomial.X := by
  rw [← p1ChartSectionsAlgEquivY_symm_X k, AlgEquiv.apply_symm_apply]

/-! ### Corollaries -/

/-- The first chart ring of `ℙ¹_k` is a domain, being a polynomial ring over a field. -/
instance instIsDomainP1ChartSectionsX :
    IsDomain Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨0⟩) :=
  Function.Injective.isDomain (p1ChartSectionsAlgEquivX k).toRingEquiv.toRingHom
    (p1ChartSectionsAlgEquivX k).injective

/-- The second chart ring of `ℙ¹_k` is a domain, being a polynomial ring over a field. -/
instance instIsDomainP1ChartSectionsY :
    IsDomain Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨1⟩) :=
  Function.Injective.isDomain (p1ChartSectionsAlgEquivY k).toRingEquiv.toRingHom
    (p1ChartSectionsAlgEquivY k).injective

/-- The chart coordinate `x` is a nonzero section: it is the variable of `k[T]`. -/
theorem p1XSection_ne_zero : p1XSection k ≠ 0 := by
  intro h
  have h' := congrArg (p1ChartSectionsAlgEquivX k) h
  rw [p1ChartSectionsAlgEquivX_p1XSection, map_zero] at h'
  exact Polynomial.X_ne_zero h'

/-- The chart coordinate `y` is a nonzero section. -/
theorem p1YSection_ne_zero : p1YSection k ≠ 0 := by
  intro h
  have h' := congrArg (p1ChartSectionsAlgEquivY k) h
  rw [p1ChartSectionsAlgEquivY_p1YSection, map_zero] at h'
  exact Polynomial.X_ne_zero h'

/-- The chart coordinate `x` is not nilpotent: it is the variable of a polynomial ring. -/
theorem not_isNilpotent_p1XSection : ¬ IsNilpotent (p1XSection k) := by
  rintro ⟨n, hn⟩
  have h' := congrArg (p1ChartSectionsAlgEquivX k) hn
  rw [map_pow, p1ChartSectionsAlgEquivX_p1XSection, map_zero] at h'
  exact pow_ne_zero n (Polynomial.X_ne_zero (R := k)) h'

/-- The chart coordinate `y` is not nilpotent. -/
theorem not_isNilpotent_p1YSection : ¬ IsNilpotent (p1YSection k) := by
  rintro ⟨n, hn⟩
  have h' := congrArg (p1ChartSectionsAlgEquivY k) hn
  rw [map_pow, p1ChartSectionsAlgEquivY_p1YSection, map_zero] at h'
  exact pow_ne_zero n (Polynomial.X_ne_zero (R := k)) h'

/-- **The two standard charts of `ℙ¹_k` genuinely overlap.**  Their intersection is the
non-vanishing locus of `x` (`p1LaurentChartData.inf_eq_basicOpen_x`), which is empty only if
`x` is nilpotent — and it is not, since `Γ(V₀) = k[x]`. -/
theorem p1Chart_inf_ne_bot : p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩ ≠ ⊥ := by
  have hinf : p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩
      = (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k))).basicOpen (p1XSection k) :=
    (p1LaurentChartData k).inf_eq_basicOpen_x
  rw [hinf]
  intro h
  exact not_isNilpotent_p1XSection k
    ((Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact
      (isAffineOpen_p1Chart k ⟨0⟩).isCompact (p1XSection k)).mpr h)

end Pushout

end AlgebraicGeometry.Adelic
