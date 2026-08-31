/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Albanese.CodimOneStalkRegularity
import AlgebraicJacobian.Algebra.ABRegularCM
import AlgebraicJacobian.Algebra.StandardSmoothDimension

/-!
# Smooth over `k̄`: closed-point regularity, reducedness, integral self-product

Ported from §3.B of `Albanese/CodimOneExtension.lean` of the previous
Algebraic-Jacobian tree (identical toolchain and mathlib pin),
re-kernel-verified here. Third file of the codim-one extension layer.

On top of the Stacks-00TT scaffolding of
`Albanese/CodimOneStalkRegularity.lean`:

* **Step B.b/B.c** (`isLocalization_atPrime_stalk_of_affineOpen`,
  `gammaSpecField_ringEquiv`): the affine-open stalk localisation, and the
  `Γ(Spec (.of k̄), U) ≃+* k̄` base identification.
* **Step B.d/B.d′** — Stacks `00TT` at (rational) closed points:
  the localisation of a standard-smooth `k`-algebra at a maximal ideal with
  bijective residue map is a regular local ring
  (`isRegularLocalRing_localization_of_isStandardSmooth_of_bijective_residue`);
  over an algebraically closed field the rationality is automatic
  (`isRegularLocalRing_localizationAtPrime_of_isStandardSmooth_of_isAlgClosed`,
  via Zariski's lemma).
* **Step B.e** — standard-smooth algebras over `k̄` are reduced
  (`isReduced_of_isStandardSmooth_of_isAlgClosed`, Stacks `033B`); hence a
  scheme smooth over `Spec k̄` is reduced
  (`isReduced_of_smooth_of_isAlgClosed`, Stacks `056S`).
* **`isIntegral_pullback_self`** — the self fibre product `X ×_{k̄} X` of a
  smooth geometrically irreducible integral `k̄`-variety is integral. This
  supplies the `[IsIntegral (pullback X.hom X.hom)]` hypothesis of
  `differenceRationalMap` (`Albanese/DifferenceMap.lean`) and the
  integral-surface input to the pole-purity engine
  (`Albanese/PolePurity.lean`).

The regular-local ⟹ domain input is
`RingTheory.CohenMacaulay.isDomain_of_regularLocal`
(`Algebra/ABRegularDomain.lean`, via the `Algebra/ABRegularCM.lean` package);
the dimension lower bound is
`Algebra.IsStandardSmoothOfRelativeDimension.le_ringKrullDim_of_isLocalization_atPrime`
(`Algebra/StandardSmoothDimension.lean`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

namespace Scheme

/-! ### Stacks-00OE Krull-dimension bridge

The smooth-algebra Krull-dimension formula at closed points (Stacks 00OE) is
provided by `AlgebraicJacobian.Albanese.StandardSmoothDimension`
(`MvPolynomial.height_eq_natCard_of_isMaximal` +
`Algebra.IsStandardSmoothOfRelativeDimension.natCast_le_height_of_isMaximal` +
`le_ringKrullDim_of_isLocalization_atPrime`), which replaced an earlier
in-file regular-sequence-witness chain (deleted as dead code). Only the
localization/height translator below remains here. -/

/-- **Stacks 00OE localization/height bridge.** Ergonomic re-export of
`IsLocalization.AtPrime.ringKrullDim_eq_height`: for a prime ideal `m ⊂ R` and
a localization `A = R_m`, `ringKrullDim A = m.height`. This is the boundary
translator between `Scheme.ringKrullDim_stalk_eq_coheight` (the iter-183
CoheightBridge bridge, phrased in `ringKrullDim`) and the
`StandardSmoothDimension` height arithmetic (phrased in `Ideal.height`).

Axiom-clean: 1-line re-export. -/
private theorem ringKrullDim_localization_eq_height_atPrime
    {R : Type*} [CommRing R] (m : Ideal R) [m.IsPrime]
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A m] :
    ringKrullDim A = m.height :=
  IsLocalization.AtPrime.ringKrullDim_eq_height m A

/-- **Stage 6 sub-gap (i) resolution (iter-198).** Axiom-clean substrate helper:
every `Algebra.IsStandardSmooth R S` instance can be promoted to
`Algebra.IsStandardSmoothOfRelativeDimension n R S` for some specific `n : ℕ`
(extracted from the underlying submersive presentation via
`Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension`).

This closes the iter-193 "sub-gap (i): relative-dimension determination"
identified in the docstring of `isRegularLocalRing_stalk_of_smooth` below.
The remaining Stage 6 gap is solely (ii) the Stacks-00OE smooth-algebra
Krull-dimension formula plus the Stacks-00RU cotangent-Kähler bridge over a
field.

Axiom-clean: a 4-line unpacking of `Algebra.IsStandardSmooth.out` via
`Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension`. No
Mathlib gap; the only reason this was a sub-gap iter-191--194 was an
overconservative read of `IsStandardSmooth.relativeDimension`'s
`Classical.choice` apparatus. -/
private theorem exists_isStandardSmoothOfRelativeDimension_of_isStandardSmooth
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [hS : Algebra.IsStandardSmooth R S] :
    ∃ n : ℕ, Algebra.IsStandardSmoothOfRelativeDimension n R S := by
  obtain ⟨iota, sigma, hσ, hι, ⟨P⟩⟩ := hS.out
  exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩

/-! ## §3.B. Project-local Mathlib supplement — Stage 6 scheme-to-algebra bridges (iter-202)

Lane COE Step B substrate: four axiom-clean scheme-to-algebra bridges feeding the
eventual closure of `isRegularLocalRing_stalk_of_smooth` (the L1061 Stacks-00TT
regularity gap). They are deliberately decoupled from Step A1 (the Matsumura
Jacobian-regular-sequence witness, gated on the iter-203 `AuslanderBuchsbaum`
public promotions) so they land independently this iter.

* **B.a** (`exists_submersivePresentation_of_isStandardSmoothOfRelativeDimension`):
  extract the explicit `Algebra.SubmersivePresentation` with `P.dimension = n`
  from `Algebra.IsStandardSmoothOfRelativeDimension n R S` (the relative-dimension
  packaging produced by the iter-198 sub-gap (i) discharger
  `exists_isStandardSmoothOfRelativeDimension_of_isStandardSmooth`).
* **B.b** (`isLocalization_atPrime_stalk_of_affineOpen`): the affine-open
  stalk-localisation `IsLocalization.AtPrime (stalk z) (primeIdealOf z)`, decoupled
  from standard-smoothness, as a named reusable substrate lemma.
* **B.c** (`open_eq_top_of_subsingleton` + `gammaSpecField_ringEquiv`): on a scheme
  whose carrier is a subsingleton (e.g.\ `Spec (.of k̄)` for a field `k̄`), every
  nonempty open is `⊤`; hence the sections of `Spec (.of k̄)` over any nonempty
  open form a ring isomorphic to `k̄`. This is the `Γ(Spec (.of k̄), U) = k̄`
  definitional bridge of the COE recipe, giving the algebraically-closed base ring
  of the standard-smooth presentation a clean `k̄`-identification.

`isLocalization_atPrime_stalk_of_affineOpen` / `gammaSpecField_ringEquiv` are
exposed (non-`private`) since they are generic Mathlib-shaped facts a future
in-file or cross-file consumer may want; the rest are `private` helpers. -/

/-- **Lane COE Step B.a (iter-202).** Extract the explicit
`Algebra.SubmersivePresentation` underlying an
`Algebra.IsStandardSmoothOfRelativeDimension n R S` instance, together with the
witness `P.dimension = n`. This is a forward-ergonomics re-export of the
`Algebra.IsStandardSmoothOfRelativeDimension.out` field, giving Step B.d direct
access to the submersive presentation `P` (whose relations are the input to the
iter-203 Step A1 Jacobian-regular-sequence witness). Axiom-clean: 1-line
re-export of the structure field. -/
private theorem exists_submersivePresentation_of_isStandardSmoothOfRelativeDimension
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {n : ℕ} [h : Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    ∃ (ix sx : Type), ∃ (_ : Finite sx) (_ : Finite ix),
      ∃ P : Algebra.SubmersivePresentation R S ix sx, P.dimension = n :=
  h.out

/-- **Lane COE Step B.b (iter-202).** The affine-open stalk localisation: for an
affine open `V ∋ z` of a scheme `X`, the stalk `X.presheaf.stalk z` is the
localisation of the section ring `Γ(X, V)` at the prime ideal `primeIdealOf z`.
Re-export of `IsAffineOpen.isLocalization_stalk`, decoupled here from
standard-smoothness so downstream regularity computations (Step B.d) can name the
`IsLocalization.AtPrime` instance without re-deriving the Stage-3 algebra package.
Axiom-clean: 1-line re-export. -/
theorem isLocalization_atPrime_stalk_of_affineOpen
    {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V) (z : X) (hzV : z ∈ V) :
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hzV⟩
    IsLocalization.AtPrime (X.presheaf.stalk z) (hV.primeIdealOf ⟨z, hzV⟩).asIdeal :=
  hV.isLocalization_stalk ⟨z, hzV⟩

/-- **Lane COE Step B.c helper (iter-202).** On a scheme whose underlying carrier
is a subsingleton (the topological space has at most one point — e.g.\
`Spec (.of k̄)` for a field `k̄`, which has a unique point by
`PrimeSpectrum.instUnique`), every nonempty open subset equals `⊤`. Axiom-clean:
the unique-point argument via `Subsingleton.elim`. -/
private lemma open_eq_top_of_subsingleton {X : Scheme.{u}} [Subsingleton X]
    (U : X.Opens) (hU : Nonempty U) : U = ⊤ := by
  obtain ⟨⟨x, hx⟩⟩ := hU
  ext y
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  rwa [Subsingleton.elim y x]

/-- **Lane COE Step B.c (iter-202).** The `Γ(Spec (.of k̄), U) = k̄` bridge: for a
field `k̄` and any nonempty open `U` of `Spec (.of k̄)`, the section ring over `U`
is ring-isomorphic to `k̄`. Since `Spec (.of k̄)` has a subsingleton carrier
(`PrimeSpectrum.instUnique`), `U = ⊤` and the sections collapse to the global
sections `Γ(Spec (.of k̄), ⊤) ≅ k̄` (`Scheme.ΓSpecIso`). This supplies the
algebraically-closed base ring of the standard-smooth presentation
(`R = Γ(Spec (.of k̄), U)`) with a clean `k̄`-identification — the geometric input
to the closed-point residue-field bridge `finrank_cotangentSpace_of_bijective_algebraMap_residue`.
Axiom-clean: `subst` of `open_eq_top_of_subsingleton` + `Scheme.ΓSpecIso`. -/
noncomputable def gammaSpecField_ringEquiv (kbar : Type u) [Field kbar]
    (U : (Spec (.of kbar)).Opens) (hU : Nonempty U) :
    Γ(Spec (.of kbar), U) ≃+* kbar := by
  have h : U = ⊤ := open_eq_top_of_subsingleton U hU
  subst h
  exact (Scheme.ΓSpecIso (.of kbar)).commRingCatIsoToRingEquiv

/-- **Lane COE Step B.d — Stacks `00TT` at a rational closed point, algebra
level (this iter).** For a standard-smooth algebra `S` over a field `k`, a
maximal ideal `m ⊆ S` whose induced residue map `k → κ(m)` is bijective (the
`k`-rational-point condition, automatic over an algebraically closed field by
the Nullstellensatz), the localisation `Sₘ` is a regular local ring.

This *closes sub-gap (ii.B) at closed points*: the proof combines
* the iter-199 sub-gap (ii.A) cotangent computation
  `finrank_cotangentSpace_of_bijective_algebraMap_residue`
  (`finrank κ (m/m²) = n`, from formal smoothness + free Kähler differentials
  of rank `n`), with
* the new `StandardSmoothDimension.lean` dimension lower bound
  `Algebra.IsStandardSmoothOfRelativeDimension.le_ringKrullDim_of_isLocalization_atPrime`
  (`n ≤ ringKrullDim Sₘ`, via the polynomial-ring height computation and
  Krull's height theorem — no transcendence-degree theory needed), through
* the generic glue `IsRegularLocalRing.of_finrank_cotangentSpace_le_ringKrullDim`
  (a Noetherian local ring with `dim_κ m/m² ≤ ringKrullDim` is regular).

The consumer `isRegularLocalRing_stalk_of_smooth` quantifies over *all*
points `z`; the non-closed points (where the residue field is a
transcendental extension of `k̄` and the bijectivity hypothesis fails) are
now handled by the Serre-free arbitrary-prime theorem of
`Albanese/SmoothPrimeRegularity.lean`, so the whole pipeline is `sorry`-free
without Stacks `00OF`. This closed-point form is retained as the input to
Step B.e (`isReduced_of_isStandardSmooth_of_isAlgClosed`). Axiom-clean. -/
theorem isRegularLocalRing_localization_of_isStandardSmooth_of_bijective_residue
    {k : Type u} [Field k]
    {S : Type u} [CommRing S] [Nontrivial S] [Algebra k S]
    [Algebra.IsStandardSmooth k S]
    (m : Ideal S) (hm : m.IsMaximal)
    (Sₘ : Type u) [CommRing Sₘ] [IsLocalRing Sₘ] [Algebra k Sₘ] [Algebra S Sₘ]
    [IsScalarTower k S Sₘ] [IsLocalization.AtPrime Sₘ m]
    (hbij : Function.Bijective (algebraMap k (IsLocalRing.ResidueField Sₘ))) :
    IsRegularLocalRing Sₘ := by
  haveI := hm.isPrime
  -- Noetherian structure: standard-smooth ⟹ finite presentation ⟹ Noetherian
  -- over the base field; localisation preserves Noetherianness.
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  haveI : IsNoetherianRing Sₘ := IsLocalization.isNoetherianRing m.primeCompl Sₘ ‹_›
  -- Extract the relative dimension n.
  obtain ⟨n, hn⟩ :=
    exists_isStandardSmoothOfRelativeDimension_of_isStandardSmooth (R := k) (S := S)
  haveI := hn
  -- Kähler package at the localisation (Stages 4, 5a, 5b).
  haveI : Module.Free S (Ω[S⁄k]) := module_free_kaehlerDifferential_of_isStandardSmooth
  haveI : Module.Free Sₘ (Ω[Sₘ⁄k]) :=
    module_free_kaehlerDifferential_localization m.primeCompl Sₘ
  have hrank : Module.rank Sₘ (Ω[Sₘ⁄k]) = n :=
    rank_kaehlerDifferential_localization_eq_relativeDimension n m.primeCompl Sₘ
  -- Formal smoothness of the localisation over k.
  haveI : Algebra.FormallySmooth S Sₘ := Algebra.FormallySmooth.of_isLocalization m.primeCompl
  haveI : Algebra.FormallySmooth k Sₘ := Algebra.FormallySmooth.comp k S Sₘ
  -- (ii.A): cotangent finrank = n at the k-rational closed point.
  have hcot := finrank_cotangentSpace_of_bijective_algebraMap_residue hbij n hrank
  -- (ii.B): dimension lower bound n ≤ dim Sₘ.
  have hdim :=
    Algebra.IsStandardSmoothOfRelativeDimension.le_ringKrullDim_of_isLocalization_atPrime
      (k := k) n m hm Sₘ
  exact IsRegularLocalRing.of_finrank_cotangentSpace_le_ringKrullDim
    (by rw [hcot]; exact_mod_cast hdim)

/-- **Lane COE Step B.d′ — Stacks `00TT` at closed points over an algebraically
closed field, unconditional form.** Over an algebraically closed base field the
`k`-rationality hypothesis of Step B.d is automatic: for any maximal ideal
`m ⊆ S` of the standard-smooth algebra `S`, the residue field `S ⧸ m` is a
finite (Zariski's lemma, `finite_of_finite_type_of_isJacobsonRing`) hence
algebraic extension of `k`, so `k → κ(m)` is bijective
(`IsAlgClosed.algebraMap_bijective_of_isIntegral` composed with
`Ideal.bijective_algebraMap_quotient_residueField`). Hence the local ring of a
standard-smooth `k̄`-algebra at **every** closed point is regular. Stated for
the model localisation `Localization.AtPrime m`; transport to an abstract
localisation (e.g. a scheme stalk) via `IsRegularLocalRing.of_ringEquiv` along
`IsLocalization.algEquiv`. Axiom-clean. -/
theorem isRegularLocalRing_localizationAtPrime_of_isStandardSmooth_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {S : Type u} [CommRing S] [Nontrivial S] [Algebra k S]
    [Algebra.IsStandardSmooth k S]
    (m : Ideal S) (hm : m.IsMaximal) :
    IsRegularLocalRing (Localization.AtPrime m) := by
  haveI := hm.isPrime
  refine isRegularLocalRing_localization_of_isStandardSmooth_of_bijective_residue
    (k := k) m hm (Localization.AtPrime m) ?_
  -- Zariski's lemma: the residue field `S ⧸ m` is module-finite over `k`.
  -- (The `Field` instance must be installed FIRST so all subsequent instance
  -- searches on `S ⧸ m` share its semiring key.)
  letI := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (S ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) Ideal.Quotient.mk_surjective
  haveI : Module.Finite k (S ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ m)
  haveI : Algebra.IsIntegral k (S ⧸ m) := Algebra.IsIntegral.of_finite k (S ⧸ m)
  -- `k → S ⧸ m` is bijective since `k` is algebraically closed.
  have h1 : Function.Bijective (algebraMap k (S ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  -- `S ⧸ m → κ(m)` is bijective since `m` is maximal.
  have h2 := m.bijective_algebraMap_quotient_residueField
  rw [show algebraMap k (IsLocalRing.ResidueField (Localization.AtPrime m))
      = (algebraMap (S ⧸ m) m.ResidueField).comp (algebraMap k (S ⧸ m)) from
    IsScalarTower.algebraMap_eq k (S ⧸ m) m.ResidueField]
  exact h2.comp h1

/-- **Lane COE Step B.e — standard-smooth algebras over an algebraically closed
field are reduced (Stacks `033B`/`00TT` corollary).** For a standard-smooth
algebra `S` over an algebraically closed field `k`, the ring `S` is reduced.

Route: reducedness is checked at localisations at maximal ideals
(`isReduced_ofLocalizationMaximal`); each localisation `Sₘ` is a regular local
ring by the Step B.d′ closed-point theorem
(`isRegularLocalRing_localizationAtPrime_of_isStandardSmooth_of_isAlgClosed`),
regular local rings are domains
(`RingTheory.CohenMacaulay.isDomain_of_regularLocal`, the project-local
Stacks `00NP` from `AuslanderBuchsbaum.lean`), and domains are reduced.
The trivial-ring case is reduced vacuously. Axiom-clean. -/
theorem isReduced_of_isStandardSmooth_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k]
    (S : Type u) [CommRing S] [Algebra k S]
    [Algebra.IsStandardSmooth k S] :
    _root_.IsReduced S := by
  cases subsingleton_or_nontrivial S with
  | inl _ => exact ⟨fun x _ => Subsingleton.elim x 0⟩
  | inr _ =>
    refine isReduced_ofLocalizationMaximal S (fun m hm => ?_)
    haveI := hm.isPrime
    haveI : IsRegularLocalRing (Localization.AtPrime m) :=
      isRegularLocalRing_localizationAtPrime_of_isStandardSmooth_of_isAlgClosed
        (k := k) m hm
    haveI : IsDomain (Localization.AtPrime m) :=
      RingTheory.CohenMacaulay.isDomain_of_regularLocal _
    infer_instance

/-- **Stacks `056S`/`033B` over an algebraically closed field: a scheme smooth
over `Spec k̄` is reduced.** This discharges the former Mathlib-gap helper
`isReduced_of_smooth_over_field` in `Thm32RationalMapExtension.lean` (the
`IsReduced A.left` input to `av_isIntegral_of_smooth_geomIrred`).

Route: reducedness is stalk-local (`isReduced_of_isReduced_stalk`). At each
point `z`, Stage 2 (`exists_isStandardSmooth_at_of_smooth`) produces an affine
chart `V ∋ z` over an affine open `U ⊆ Spec k̄` with
`Γ(X.left, V)` standard-smooth over `Γ(Spec k̄, U)`; the base identification
`Γ(Spec k̄, U) ≃+* k̄` (`gammaSpecField_ringEquiv`, `U` is nonempty since it
contains the image of `z`) transports standard-smoothness to a `k̄`-algebra
structure (`RingHom.isStandardSmooth_respectsIso`), Step B.e above gives
`IsReduced Γ(X.left, V)`, and the stalk — the localisation of `Γ(X.left, V)`
at the prime of `z` (`IsAffineOpen.isLocalization_stalk`) — is reduced by
`isReduced_localizationPreserves`.

Unlike the still-open regularity keystone `isRegularLocalRing_stalk_of_smooth`
(blocked on Stacks `00OF` at non-closed points), reducedness only needs the
maximal-ideal localisations of the chart ring, so the closed-point theorem
B.d′ suffices at EVERY point `z`. Axiom-clean. -/
theorem isReduced_of_smooth_of_isAlgClosed
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (X : Over (Spec (.of kbar)))
    [Smooth X.hom] :
    IsReduced X.left := by
  haveI hstalk : ∀ z : X.left.toPresheafedSpace,
      _root_.IsReduced (X.left.presheaf.stalk z) := by
    intro z
    -- Stage 2: standard-smooth chart at z, RingHom form.
    obtain ⟨U, hU, V, hV, hzV, e, hSS⟩ := exists_isStandardSmooth_at_of_smooth X z
    -- Base identification: U contains the image of z, so Γ(Spec k̄, U) ≃+* k̄.
    let ε : kbar ≃+* Γ(Spec (.of kbar), U) :=
      (gammaSpecField_ringEquiv kbar U ⟨⟨_, e hzV⟩⟩).symm
    -- Transport standard-smoothness along the base iso.
    have hSS' : ((X.hom.appLE U V e).hom.comp ε.toRingHom).IsStandardSmooth :=
      RingHom.isStandardSmooth_respectsIso.2 _ ε hSS
    letI : Algebra kbar Γ(X.left, V) :=
      ((X.hom.appLE U V e).hom.comp ε.toRingHom).toAlgebra
    haveI : Algebra.IsStandardSmooth kbar Γ(X.left, V) := hSS'.toAlgebra
    -- Sections over V are reduced (Step B.e).
    haveI hSred : _root_.IsReduced Γ(X.left, V) :=
      isReduced_of_isStandardSmooth_of_isAlgClosed kbar Γ(X.left, V)
    -- The stalk is a localisation of Γ(X.left, V); reducedness localises.
    letI : Algebra Γ(X.left, V) (X.left.presheaf.stalk z) :=
      TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨z, hzV⟩
    haveI : IsLocalization.AtPrime (X.left.presheaf.stalk z)
        (hV.primeIdealOf ⟨z, hzV⟩).asIdeal := hV.isLocalization_stalk ⟨z, hzV⟩
    exact isReduced_localizationPreserves
      (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl (X.left.presheaf.stalk z) hSred
  exact isReduced_of_isReduced_stalk X.left

/-- **Integrality of the self-product `X ×_{k̄} X`.** For a smooth, geometrically
irreducible, integral scheme `X` over an algebraically closed field `k̄`, the self
fibre product `X ×_{k̄} X` is integral: it is reduced because it is smooth over the
algebraically closed field (`isReduced_of_smooth_of_isAlgClosed` on the composite
structure map `pr₁ ≫ X.hom`) and irreducible because `X.hom` is geometrically
irreducible and universally open (`GeometricallyIrreducible.irreducibleSpace`,
base change of geometric irreducibility along the open projection).

This discharges the `[IsIntegral (pullback X.hom X.hom)]` hypothesis of
`AlgebraicGeometry.Scheme.RationalMap.differenceRationalMap` (Milne Lemma 3.3,
Sub-step 1, `Albanese/DifferenceMap.lean`), and supplies the integral-surface input
to the pole-purity engine of Sub-step 4 (`Albanese/PolePurity.lean`). Axiom-clean. -/
theorem isIntegral_pullback_self
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (X : Over (Spec (.of kbar)))
    [Smooth X.hom] [GeometricallyIrreducible X.hom] [IsIntegral X.left] :
    IsIntegral (pullback X.hom X.hom) := by
  -- The composite structure map `X ×_{k̄} X → Spec k̄` is smooth (`smooth_comp` of
  -- the base-change-smooth projection with `X.hom`); package it as an `Over` object.
  haveI hsm : Smooth (Over.mk (pullback.fst X.hom X.hom ≫ X.hom)).hom := by
    change Smooth (pullback.fst X.hom X.hom ≫ X.hom); infer_instance
  haveI hred : IsReduced (pullback X.hom X.hom) :=
    isReduced_of_smooth_of_isAlgClosed (Over.mk (pullback.fst X.hom X.hom ≫ X.hom))
  -- Irreducibility of `X ×_{k̄} X` from geometric irreducibility of `X.hom` (the
  -- projection is universally open). Drive synthesis through the `Scheme`-typed
  -- application so the `Scheme → Type` coercion on the pullback is inserted (a bare
  -- `IrreducibleSpace (pullback …)` mis-resolves `pullback` in the `Type` category).
  haveI : UniversallyOpen X.hom := inferInstance
  exact isIntegral_of_irreducibleSpace_of_isReduced (pullback X.hom X.hom)


end Scheme

end AlgebraicGeometry
