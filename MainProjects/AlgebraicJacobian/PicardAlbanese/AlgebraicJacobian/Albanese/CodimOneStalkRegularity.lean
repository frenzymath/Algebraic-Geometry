/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Smooth over `k̄` ⟹ regular/free stalk data: the Stacks-00TT scaffolding

Ported from §3/§3.A of `Albanese/CodimOneExtension.lean` of the previous
Algebraic-Jacobian tree (identical toolchain and mathlib pin),
re-kernel-verified here. Second file of the codim-one extension layer.

The Mathlib gap "smooth over `k̄` ⟹ stalk is a regular local ring" (Stacks
tag `00TT`) is structured as a staged pipeline; this file carries the
algebra-side stages:

* **Stages 1–2** — smooth ⟹ flat at every stalk; smooth at a point ⟹
  standard smooth presentation on an affine neighbourhood (Stacks `00T7`,
  `exists_isStandardSmooth_at_of_smooth`).
* **Stages 4–5** — Kähler differentials of a standard-smooth algebra are
  free, of rank the relative dimension, and both transport through
  localisation (Stacks `00RT`).
* **Stage 6.A/6.B** — the closed-point cotangent computation: under a
  bijective residue map `k → κ(m)` the cotangent space `m/m²` of the
  localisation has `κ`-finrank the relative dimension
  (`finrank_cotangentSpace_of_bijective_algebraMap_residue`).

Consumers: `Albanese/CodimOneSmoothReduced.lean` (closed-point regularity,
reducedness of smooth schemes over `k̄`, integrality of the self-product)
and `Albanese/CodimOneDVRStalk.lean` (regular stalks at every point, DVR at
codim-one points). The arbitrary-prime regularity theorem itself lives in
`Algebra/SmoothPrimeRegularity.lean` (Serre-free Stacks `00TT`).

Helpers consumed across the codim-one extension layer's files are public;
the remaining stage-internal steps are `private`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

namespace Scheme

/-! ## §3. Smoothness yields a DVR at every codim-1 point

On a nonsingular variety `X` over `k̄`, the local ring at the generic point
of a prime divisor is a discrete valuation ring with fraction field equal to
the function field `K(X) = X.functionField`. This is Hartshorne II.6's
"regular in codimension one" property combined with the regular-local-ring-of-dim-1
$\Leftrightarrow$ DVR equivalence (Atiyah–Macdonald 9.2; Stacks `00PD`).
This file carries the algebra-side scaffolding; the DVR conclusion
`localRing_dvr_of_codim_one` lives in `Albanese/CodimOneDVRStalk.lean`.

Blueprint pin: `lem:smooth_codim_one_dvr` (Hartshorne II.6 p. 130). -/

/-! ### Stacks 00TT scaffolding (Lane M↓ iter-191 first scaffold)

The Mathlib gap "smooth over `\bar k` ⟹ stalk is a regular local ring"
(Stacks tag `00TT`) is structured here as a four-stage pipeline:

* **Stage 1** — smooth ⟹ flat at every stalk (Mathlib instance
  `AlgebraicGeometry.instFlatOfSmooth` + `Flat.stalkMap`).
* **Stage 2** — smooth at a point ⟹ exists a standard smooth presentation
  on an affine neighbourhood (Stacks tag `00T7`, packaged in Mathlib at
  `AlgebraicGeometry.Smooth.exists_isStandardSmooth`).
* **Stage 3** — the polynomial generators of the standard smooth
  presentation form a regular sequence after localising at any prime
  (Stacks `00RT`/`07BV`; Mathlib gap as of `b80f227`).
* **Stage 4** — a Noetherian local ring whose maximal ideal is generated
  by a regular sequence of length equal to its Krull dimension is a
  regular local ring (`IsRegularLocalRing.of_regularSequence`; Stacks
  `00OE`/Matsumura 19.2; Mathlib gap as of `b80f227`).

Stages 1-2 are landed axiom-clean as named helpers below. Stages 3-4 were
historically a single scoped `sorry` inside the main theorem
`isRegularLocalRing_stalk_of_smooth`; that theorem is now **fully proved**
(no `sorry`) via the Serre-free arbitrary-prime route of
`Albanese/SmoothPrimeRegularity.lean` (conormal identity + Kähler-trdeg
identification + polynomial-ring trdeg–height inequality), which needs
neither Stacks `00OF` nor the `00RT`/`00OE` regular-sequence chain. -/

/-- **Stage 1 (Stacks 00TT, smooth ⟹ flat at stalk).** For a smooth
morphism `X.hom : X.left ⟶ Spec (.of k̄)` with `k̄` algebraically closed,
the induced ring map on stalks at every point `z : X.left` is flat. This
is the smooth ⟹ flat instance applied through the stalk-map flatness
characterisation `AlgebraicGeometry.Flat.iff_flat_stalkMap`.

Axiom-clean: composes the smooth ⟹ flat instance with the stalk-map
flatness lemma. No Mathlib gap. -/
private theorem stalkMap_flat_of_smooth
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (X : Over (Spec (.of kbar)))
    [Smooth X.hom]
    (z : X.left) :
    ((X.hom.stalkMap z).hom).Flat :=
  AlgebraicGeometry.Flat.stalkMap X.hom z

/-- **Stage 2 (Stacks 00T7, smooth ⟹ standard smooth presentation at a
point).** For a smooth morphism `X.hom : X.left ⟶ Spec (.of k̄)`, every
point `z : X.left` admits affine open neighbourhoods `U ⊆ Spec (.of k̄)`,
`V ⊆ X.left` with `z ∈ V` and `V ⊆ X.hom ⁻¹' U` such that the induced
ring map `(X.hom.appLE U V e).hom` is `IsStandardSmooth`.

Axiom-clean: re-exports `AlgebraicGeometry.Smooth.exists_isStandardSmooth`
(the scheme-level packaging of Stacks tag `00T7`) at the project's
`Over (Spec (.of k̄))` calling convention. -/
theorem exists_isStandardSmooth_at_of_smooth
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (X : Over (Spec (.of kbar)))
    [Smooth X.hom]
    (z : X.left) :
    ∃ (U : (Spec (.of kbar)).Opens) (_ : IsAffineOpen U)
      (V : X.left.Opens) (_ : IsAffineOpen V)
      (_hzV : z ∈ V) (e : V ≤ X.hom ⁻¹ᵁ U),
      (X.hom.appLE U V e).hom.IsStandardSmooth :=
  AlgebraicGeometry.Smooth.exists_isStandardSmooth X.hom z

/-- **Stage 3 (Stacks 00TT, scheme-to-algebra bridge for the standard smooth
presentation).** Iter-192 axiom-clean intermediate helper: combines Stage 2's
existence-of-standard-smooth-presentation output with the `RingHom`-to-`Algebra`
bridge `RingHom.IsStandardSmooth.toAlgebra`, plus the affine-open stalk
localisation `IsAffineOpen.isLocalization_stalk`. Returns the full algebra-side
package needed by Stages 4-5 of the regularity proof: an affine neighbourhood
`V ∋ z`, an `Algebra Γ(Spec _, U) Γ(X.left, V)` instance under which
`Γ(X.left, V)` is `Algebra.IsStandardSmooth` over `Γ(Spec _, U)`, plus the
`IsLocalization.AtPrime` witness identifying the stalk at `z` with the
localisation of `Γ(X.left, V)` at the prime ideal of `z`.

Axiom-clean: composition of `exists_isStandardSmooth_at_of_smooth` +
`RingHom.IsStandardSmooth.toAlgebra` + `IsAffineOpen.isLocalization_stalk`.

This is the iter-192 Lane M↓ HARD BAR new axiom-clean helper: it packages the
"smooth ⟹ stalk is localisation of a standard-smooth Γ(Spec, U)-algebra"
content as a standalone declaration that downstream Stages 4-5 (the genuine
Stacks 00RT + 00OE Mathlib-gap chain) can consume directly. -/
private theorem exists_algebra_isStandardSmooth_section_stalk_isLocalization_of_smooth
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (X : Over (Spec (.of kbar)))
    [Smooth X.hom]
    (z : X.left) :
    ∃ (U : (Spec (.of kbar)).Opens) (_hU : IsAffineOpen U)
      (V : X.left.Opens) (hV : IsAffineOpen V)
      (hzV : z ∈ V) (_e : V ≤ X.hom ⁻¹ᵁ U)
      (alg : Algebra Γ(Spec (.of kbar), U) Γ(X.left, V)),
      @Algebra.IsStandardSmooth _ _ _ _ alg ∧
      letI := TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨z, hzV⟩
      IsLocalization.AtPrime
        (X.left.presheaf.stalk z) (hV.primeIdealOf ⟨z, hzV⟩).asIdeal := by
  obtain ⟨U, hU, V, hV, hzV, e, hStdSmooth⟩ :=
    exists_isStandardSmooth_at_of_smooth X z
  refine ⟨U, hU, V, hV, hzV, e, (X.hom.appLE U V e).hom.toAlgebra,
    hStdSmooth.toAlgebra, ?_⟩
  -- Localisation witness: the affine-open stalk is `Aₚ` for `p = primeIdealOf z`.
  letI := TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨z, hzV⟩
  exact hV.isLocalization_stalk ⟨z, hzV⟩

/-- **Stage 4 (Stacks 00T7(2), Kähler-differentials freeness).** Iter-192
axiom-clean intermediate helper: given an algebra-level
`Algebra.IsStandardSmooth R S` instance (typically arising from
`Stage 3 = exists_algebra_isStandardSmooth_section_stalk_isLocalization_of_smooth`),
the module of Kähler differentials `Ω[S⁄R]` is `Module.Free` over `S`. The
basis is the `{d sᵢ}ᵢ` family witnessed by
`Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential`.

Axiom-clean: re-export of `Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential`
+ `Module.Free.of_basis`. -/
theorem module_free_kaehlerDifferential_of_isStandardSmooth
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardSmooth R S] :
    Module.Free S (Ω[S⁄R]) := by
  obtain ⟨_, _, b, _⟩ :=
    (Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential
      (R := R) (S := S)).mp ‹_›
  exact Module.Free.of_basis b

/-- **Stage 5a (Stacks 00RT, freeness transports through localisation, algebra-side).**
Iter-193 Lane M↓ axiom-clean substrate helper: for an `R`-algebra `S` whose Kähler
differentials `Ω[S⁄R]` are `S`-free (e.g.\ when `S` is `R`-standard smooth via
`module_free_kaehlerDifferential_of_isStandardSmooth`), the localisation `Sₘ` at any
submonoid `M ⊆ S` has Kähler differentials `Ω[Sₘ⁄R]` which are `Sₘ`-free.

Axiom-clean: composes `KaehlerDifferential.isLocalizedModule_map` (Mathlib re-export)
with `Module.free_of_isLocalizedModule`. This is the substantive localisation-of-freeness
step that Stage 5 of the smooth ⟹ regular pipeline uses; extracted as a named helper
here so the main proof body of `isRegularLocalRing_stalk_of_smooth` reads as a clean
chain of named lemmas rather than an inline `IsLocalizedModule` + `Module.free_of_*`
maneuver. -/
theorem module_free_kaehlerDifferential_localization
    {R : Type u} [CommRing R]
    {S : Type u} [CommRing S] [Algebra R S]
    [Module.Free S (Ω[S⁄R])]
    (M : Submonoid S)
    (Sₘ : Type u) [CommRing Sₘ] [Algebra R Sₘ] [Algebra S Sₘ]
    [IsScalarTower R S Sₘ] [IsLocalization M Sₘ] :
    Module.Free Sₘ (Ω[Sₘ⁄R]) := by
  haveI : IsLocalizedModule M (KaehlerDifferential.map R R S Sₘ) :=
    KaehlerDifferential.isLocalizedModule_map R S Sₘ M
  exact Module.free_of_isLocalizedModule (R := S) (Rₛ := Sₘ) (S := M)
    (M := Ω[S⁄R]) (Mₛ := Ω[Sₘ⁄R])
    (KaehlerDifferential.map R R S Sₘ)

/-- **Stage 5b (Stacks 00RT + 00T7, rank computation through localisation, algebra-side).**
Iter-193 Lane M↓ axiom-clean substrate helper: for an `R`-algebra `S` that is
`IsStandardSmoothOfRelativeDimension n` over `R` and a localisation `Sₘ` at any
submonoid `M` (with `Sₘ` non-trivial), the `Sₘ`-rank of `Ω[Sₘ⁄R]` equals `n`. This
upgrades Stage 5a's freeness conclusion with a *specific* rank.

Axiom-clean: composes `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`
(Mathlib, gives `rank S Ω[S⁄R] = n`) with `Module.lift_rank_of_isLocalizedModule_of_free`
(Mathlib, transports module rank through `IsLocalizedModule`). The combination
provides the rank of the stalk-side Kähler differentials, which is one of the two
ingredients of the regularity conclusion at the stalk (the other ingredient is the
Stacks 00OE smooth-algebra dimension formula, still a Mathlib gap). -/
theorem rank_kaehlerDifferential_localization_eq_relativeDimension
    {R : Type u} [CommRing R]
    {S : Type u} [CommRing S] [Nontrivial S] [Algebra R S]
    (n : ℕ) [hS : Algebra.IsStandardSmoothOfRelativeDimension n R S]
    (M : Submonoid S)
    (Sₘ : Type u) [CommRing Sₘ] [Nontrivial Sₘ]
    [Algebra R Sₘ] [Algebra S Sₘ]
    [IsScalarTower R S Sₘ] [IsLocalization M Sₘ] :
    Module.rank Sₘ (Ω[Sₘ⁄R]) = n := by
  haveI : Algebra.IsStandardSmooth R S := hS.isStandardSmooth
  haveI : Module.Free S (Ω[S⁄R]) := Algebra.IsStandardSmooth.free_kaehlerDifferential
  haveI : IsLocalizedModule M (KaehlerDifferential.map R R S Sₘ) :=
    KaehlerDifferential.isLocalizedModule_map R S Sₘ M
  have hrank :
      Cardinal.lift.{u, u} (Module.rank Sₘ (Ω[Sₘ⁄R])) =
      Cardinal.lift.{u, u} (Module.rank S (Ω[S⁄R])) :=
    Module.lift_rank_of_isLocalizedModule_of_free Sₘ M
      (KaehlerDifferential.map R R S Sₘ)
  rw [Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
        (S := S) n] at hrank
  simpa using hrank

/-- **Stage 6.B substrate (Stacks 00RU, RHS of the conormal iso).** Iter-198
Lane COE axiom-clean substrate helper: under the Stage 5a + 5b hypotheses
(`Ω[Sₘ⁄R]` is `Sₘ`-free with `Sₘ`-rank `n`), the residue-field base-change
`κ(mₘ) ⊗_{Sₘ} Ω[Sₘ⁄R]` has `κ(mₘ)`-dimension `n`. This is the *right-hand
side* of the Stacks-00RU cotangent iso
`κ(mₘ) ⊗_{Sₘ} Ω[Sₘ⁄R] ≃ mₘ/mₘ²` (the iso itself is the missing Mathlib
bridge for sub-lemma 6.B); combined with the bridge it gives
`Module.finrank κ (CotangentSpace Sₘ) = n`, the cotangent input of the
regularity criterion `IsRegularLocalRing.iff_finrank_cotangentSpace`.

Axiom-clean: composes `Module.finrank_baseChange` (Mathlib re-export,
`LinearAlgebra/Dimension/Constructions.lean`) with the cardinal-to-natural
cast `Module.finrank_eq_of_rank_eq`. Consumes no Mathlib gap.

The hypothesis pattern (free + rank = n) is exactly the conclusion of
Stages 5a + 5b applied to the stalk of a smooth scheme; the helper is
phrased independently of `IsStandardSmoothOfRelativeDimension` because the
stalk-side localisation is not preserved by that class (Mathlib commit
`b80f227` only provides `localization_away` which collapses to rel-dim 0).
-/
private theorem finrank_residueField_tensor_kaehlerDifferential_of_free_rank_eq
    {R : Type u} [CommRing R]
    {Sₘ : Type u} [CommRing Sₘ] [IsLocalRing Sₘ] [Algebra R Sₘ]
    [Module.Free Sₘ (Ω[Sₘ⁄R])] (n : ℕ) (hrank : Module.rank Sₘ (Ω[Sₘ⁄R]) = n) :
    Module.finrank (IsLocalRing.ResidueField Sₘ)
      (TensorProduct Sₘ (IsLocalRing.ResidueField Sₘ) (Ω[Sₘ⁄R])) = n := by
  rw [Module.finrank_baseChange]
  exact Module.finrank_eq_of_rank_eq hrank

/-- **Stage 6.B substrate (Stacks 00RU, LHS-RHS bridge): formally-smooth residue
gives the cotangent iso.** Iter-199 Lane COE axiom-clean closed-point-style
helper: assuming the source ring `Sₘ` is formally smooth over `R`, its residue
field `κ = ResidueField Sₘ` is formally smooth over `R`, and `Ω[κ⁄R]` is
subsingleton (the three hypotheses combine to model the closed-point case of
Stacks 00RU over an algebraically closed base, where `κ = R` makes both FS
and `Ω[κ⁄R] = 0` automatic), the canonical Mathlib map
`KaehlerDifferential.kerCotangentToTensor R Sₘ κ`
is an `Sₘ`-linear equivalence between
`(maximalIdeal Sₘ).Cotangent` (the `Sₘ`-side packaging of `m/m²`)
and `κ ⊗_Sₘ Ω[Sₘ⁄R]` (the residue-field base-change of the Kähler
differentials).

This is the closed-point case of the Stacks-00RU cotangent ↔ Kähler iso
(sub-gap (ii.A) of the Stage 6 chain in `isRegularLocalRing_stalk_of_smooth`).
The proof is the 3-step recipe from `analogies/coe-stacks02jk.md`:

* **Step 1** — retraction → injection via
  `Algebra.FormallySmooth.iff_split_injection`: under
  `FormallySmooth R κ` and surjectivity of `Sₘ → κ`, the conormal map
  `kerCotangentToTensor R Sₘ κ` admits a left-inverse `l`, hence is injective.
* **Step 2** — `Ω[κ⁄R] = 0` + exactness → surjection: combining
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` with
  `Subsingleton (Ω[κ⁄R])` gives that every element of the tensor space lies
  in the kernel of `mapBaseChange`, hence in the range of `kerCotangentToTensor`.
* **Step 3** — bijective → iso: package as `LinearEquiv.ofBijective`.

The `kerCotangentToTensor` map's domain is
`(RingHom.ker (algebraMap Sₘ κ)).Cotangent`, which equals
`(IsLocalRing.maximalIdeal Sₘ).Cotangent = IsLocalRing.CotangentSpace Sₘ` since
`κ = Sₘ / maximalIdeal Sₘ`; the equivalence is therefore the
Stacks 00RU closed-point cotangent iso
`m/m² ≃ₗ[Sₘ] κ ⊗_Sₘ Ω[Sₘ⁄R]`.

Axiom-clean: composes
`Algebra.FormallySmooth.iff_split_injection` (Mathlib;
`Mathlib/RingTheory/Smooth/Basic.lean`),
`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` (Mathlib;
`Mathlib/RingTheory/Kaehler/Basic.lean`), and `LinearEquiv.ofBijective`. -/
private noncomputable def
    cotangent_iso_residue_tensor_kaehler_of_formallySmooth_residue
    {R Sₘ : Type*} [CommRing R] [CommRing Sₘ] [IsLocalRing Sₘ] [Algebra R Sₘ]
    [Algebra.FormallySmooth R Sₘ]
    [Algebra.FormallySmooth R (IsLocalRing.ResidueField Sₘ)]
    [Subsingleton (Ω[IsLocalRing.ResidueField Sₘ⁄R])] :
    (RingHom.ker (algebraMap Sₘ (IsLocalRing.ResidueField Sₘ))).Cotangent ≃ₗ[Sₘ]
      TensorProduct Sₘ (IsLocalRing.ResidueField Sₘ) Ω[Sₘ⁄R] := by
  -- Surjectivity of `algebraMap Sₘ κ` is the residue surjection.
  have hSurj : Function.Surjective
      (algebraMap Sₘ (IsLocalRing.ResidueField Sₘ)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.residue_surjective
  -- Step 1: retraction → injection via `iff_split_injection`.
  have hInj : Function.Injective
      (KaehlerDifferential.kerCotangentToTensor R Sₘ (IsLocalRing.ResidueField Sₘ)) := by
    obtain ⟨l, hl⟩ :=
      (Algebra.FormallySmooth.iff_split_injection
        (R := R) (P := Sₘ) (A := IsLocalRing.ResidueField Sₘ) hSurj).mp ‹_›
    refine Function.LeftInverse.injective (g := l) (fun x => ?_)
    have h := LinearMap.congr_fun hl x
    simp only [LinearMap.coe_comp, Function.comp_apply] at h
    exact h
  -- Step 2: `Ω[κ⁄R] = 0` + exactness → surjection.
  have hExact :=
    KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R Sₘ
      (IsLocalRing.ResidueField Sₘ) hSurj
  have hSurjMap :
      Function.Surjective
        (KaehlerDifferential.kerCotangentToTensor R Sₘ
          (IsLocalRing.ResidueField Sₘ)) := by
    intro x
    have h0 :
        KaehlerDifferential.mapBaseChange R Sₘ
          (IsLocalRing.ResidueField Sₘ) x = 0 :=
      Subsingleton.elim _ _
    exact (hExact x).mp h0
  -- Step 3: bijective → linear equivalence.
  exact LinearEquiv.ofBijective _ ⟨hInj, hSurjMap⟩

/-- **Stage 6.B substrate (iter-199), maximal-ideal-domain repackaging.** The
same Stacks-00RU closed-point cotangent iso as
`cotangent_iso_residue_tensor_kaehler_of_formallySmooth_residue` above, but
restated with `(IsLocalRing.maximalIdeal Sₘ).Cotangent` (the canonical
`Sₘ/m = κ`-module side of `IsLocalRing.CotangentSpace Sₘ`) as the domain
rather than `(RingHom.ker (algebraMap Sₘ κ)).Cotangent`. The two coincide
through `IsLocalRing.ResidueField.algebraMap_eq + IsLocalRing.ker_residue`,
but the maximal-ideal form is the one Mathlib pre-equips with the κ-module
instance via `IsLocalRing.instModuleResidueFieldCotangentSpace`, so this
repackaging is what downstream κ-finrank computations want to consume.

Axiom-clean: `rw`-transports the iso above along the ideal equality. -/
private noncomputable def
    cotangent_iso_maximalIdeal_residue_tensor_kaehler_of_formallySmooth_residue
    {R Sₘ : Type*} [CommRing R] [CommRing Sₘ] [IsLocalRing Sₘ] [Algebra R Sₘ]
    [Algebra.FormallySmooth R Sₘ]
    [Algebra.FormallySmooth R (IsLocalRing.ResidueField Sₘ)]
    [Subsingleton (Ω[IsLocalRing.ResidueField Sₘ⁄R])] :
    (IsLocalRing.maximalIdeal Sₘ).Cotangent ≃ₗ[Sₘ]
      TensorProduct Sₘ (IsLocalRing.ResidueField Sₘ) Ω[Sₘ⁄R] := by
  have hker : RingHom.ker (algebraMap Sₘ (IsLocalRing.ResidueField Sₘ)) =
      IsLocalRing.maximalIdeal Sₘ := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
  rw [← hker]
  exact cotangent_iso_residue_tensor_kaehler_of_formallySmooth_residue

/-- **Stage 6.B substrate (iter-199), κ-finrank conclusion.** Assemble the
maximal-ideal-side cotangent iso of
`cotangent_iso_maximalIdeal_residue_tensor_kaehler_of_formallySmooth_residue`
with the 6.B-RHS substrate
`finrank_residueField_tensor_kaehlerDifferential_of_free_rank_eq` to compute
the κ-finrank of `IsLocalRing.CotangentSpace Sₘ` (= `m/m²`) explicitly.

Under the closed-point-style hypothesis pattern (`Sₘ` formally smooth over
`R`, residue field `κ` formally smooth over `R`, `Ω[κ⁄R]` subsingleton),
combined with `Module.Free Sₘ Ω[Sₘ⁄R]` of `Sₘ`-rank `n` (the conclusion of
Stages 5a + 5b applied to a standard-smooth localisation), the cotangent
space `m/m²` has `κ`-finrank equal to `n`.

This is the precise conclusion the consumer
`isRegularLocalRing_stalk_of_smooth` needs: combined with the still-open
Stacks-00OE Krull-dim formula (sub-gap (ii.B)) it discharges the regularity
criterion `IsRegularLocalRing.iff_finrank_cotangentSpace`. Sub-gap (ii.A)
(this lemma) is now axiom-clean; sub-gap (ii.B) remains the residual gap.

Axiom-clean: composes the Sₘ-linear iso with `LinearEquiv.extendScalarsOfSurjective`
(promotion to κ-linear via the residue surjection), `LinearEquiv.finrank_eq`,
and the 6.B-RHS substrate `finrank_baseChange + finrank_eq_of_rank_eq`. -/
private theorem finrank_cotangentSpace_of_formallySmooth_residue
    {R Sₘ : Type u} [CommRing R] [CommRing Sₘ] [IsLocalRing Sₘ]
    [Algebra R Sₘ]
    [Algebra.FormallySmooth R Sₘ]
    [Algebra.FormallySmooth R (IsLocalRing.ResidueField Sₘ)]
    [Subsingleton (Ω[IsLocalRing.ResidueField Sₘ⁄R])]
    [Module.Free Sₘ (Ω[Sₘ⁄R])]
    (n : ℕ) (hrank : Module.rank Sₘ (Ω[Sₘ⁄R]) = n) :
    Module.finrank (IsLocalRing.ResidueField Sₘ)
      (IsLocalRing.CotangentSpace Sₘ) = n := by
  -- 6.B-RHS substrate: finrank κ (κ ⊗_Sₘ Ω[Sₘ⁄R]) = n.
  have hRHS :
      Module.finrank (IsLocalRing.ResidueField Sₘ)
        (TensorProduct Sₘ (IsLocalRing.ResidueField Sₘ) (Ω[Sₘ⁄R])) = n :=
    finrank_residueField_tensor_kaehlerDifferential_of_free_rank_eq n hrank
  -- Sₘ-linear iso (maximalIdeal form).
  have hiso :
      (IsLocalRing.maximalIdeal Sₘ).Cotangent ≃ₗ[Sₘ]
        TensorProduct Sₘ (IsLocalRing.ResidueField Sₘ) (Ω[Sₘ⁄R]) :=
    cotangent_iso_maximalIdeal_residue_tensor_kaehler_of_formallySmooth_residue
  -- Promote to κ-linear via the residue surjection.
  have hSurj : Function.Surjective
      (algebraMap Sₘ (IsLocalRing.ResidueField Sₘ)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.residue_surjective
  have hisoκ :
      (IsLocalRing.maximalIdeal Sₘ).Cotangent ≃ₗ[IsLocalRing.ResidueField Sₘ]
        TensorProduct Sₘ (IsLocalRing.ResidueField Sₘ) (Ω[Sₘ⁄R]) :=
    LinearEquiv.extendScalarsOfSurjective hSurj hiso
  rw [hisoκ.finrank_eq, hRHS]

/-- **Stage 6.B substrate (iter-199), bundled bijective-residue-map form.**
Closed-point-friendly bundled variant of
`finrank_cotangentSpace_of_formallySmooth_residue` that replaces the three
typeclass hypotheses `Algebra.FormallySmooth R (ResidueField Sₘ)` and
`Subsingleton (Ω[ResidueField Sₘ⁄R])` with the single hypothesis that
`algebraMap R (ResidueField Sₘ)` is bijective. This is the precise hypothesis
the closed-point case of Stacks 00RU consumes: at a `k̄`-rational closed
point of a smooth `k̄`-algebra, the residue map `k̄ → κ` is the identity
(Nullstellensatz), hence bijective.

The proof:

* `RingHom.FormallySmooth.of_bijective` + `RingHom.formallySmooth_algebraMap`
  upgrade `Bijective` to `Algebra.FormallySmooth R (ResidueField Sₘ)`.
* `KaehlerDifferential.subsingleton_of_surjective` deduces
  `Subsingleton (Ω[ResidueField Sₘ⁄R])` from the surjectivity half of
  bijectivity.
* Then apply the typeclass-hypothesis form
  `finrank_cotangentSpace_of_formallySmooth_residue`.

Axiom-clean: composes Mathlib bridges with the iter-199 helper above. -/
theorem finrank_cotangentSpace_of_bijective_algebraMap_residue
    {R Sₘ : Type u} [CommRing R] [CommRing Sₘ] [IsLocalRing Sₘ]
    [Algebra R Sₘ]
    [Algebra.FormallySmooth R Sₘ]
    [Module.Free Sₘ (Ω[Sₘ⁄R])]
    (hbij : Function.Bijective (algebraMap R (IsLocalRing.ResidueField Sₘ)))
    (n : ℕ) (hrank : Module.rank Sₘ (Ω[Sₘ⁄R]) = n) :
    Module.finrank (IsLocalRing.ResidueField Sₘ)
      (IsLocalRing.CotangentSpace Sₘ) = n := by
  haveI : Algebra.FormallySmooth R (IsLocalRing.ResidueField Sₘ) :=
    RingHom.formallySmooth_algebraMap.mp
      (RingHom.FormallySmooth.of_bijective hbij)
  haveI : Subsingleton (Ω[IsLocalRing.ResidueField Sₘ⁄R]) :=
    KaehlerDifferential.subsingleton_of_surjective R _ hbij.surjective
  exact finrank_cotangentSpace_of_formallySmooth_residue n hrank

end Scheme

end AlgebraicGeometry
