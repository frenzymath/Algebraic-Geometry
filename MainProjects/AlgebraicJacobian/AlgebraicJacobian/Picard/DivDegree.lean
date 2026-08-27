/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.FGAPicRepresentability

/-!
# Degree slices of the relative-divisor functor + the degree-refined Abel map

Campaign milestones **D1'** (degree-`d` divisor functor `DivFunctorDeg`, clopen
degree decomposition, base-change stability of the fibre degree) and **A2**
(degree-refined Abel map `abelDeg`) of the `instHasPicScheme` campaign
(`informal/pic-representability-campaign.md`), on top of the landed divisor
functor `Scheme.DivFunctor` (Kleiman, "The Picard scheme", §3 Def. `df:div`;
`Picard/DivFunctorDef.lean`).

## The fibre degree

For a family of relative effective divisors `x : DivFamily π T` (the quotient
encoding: `q : O_{X_T} ↠ F = O_D` with invertible kernel ideal `I_D = ker q`),
the **fibre degree** at `t : T` is

  `x.fiberDeg t := dim_{κ(t)} Γ(D_t, O_{D_t}) = dim_{κ(t)} Γ((X_T)_t, F_t)`,

Kleiman §3 Ex. `ex:DivC`'s degree of the fibre divisor `D_t ⊆ X_t` — the
`H⁰`-only, cohomology-free rank.

**AUDIT (encoding choice, D1').** The campaign phrase "rank-`d` of the
finite-flat pushforward of `O_D`" is realized by its *pointwise shadow*: the
in-tree substrate has no `q_* O_D`-as-locally-free-object (that is exactly the
B3 rigid-pushforward engine, unbuilt), and for a finite flat family the rank of
the pushforward at `t` *equals* `dim_{κ(t)} Γ(D_t, O_{D_t})` (pushforward along
an affine morphism is exact and commutes with base change).  The fibre-section
form is honest at full generality (any `π`, any `T`; `Module.finrank` junk
value `0` if the fibre sections are infinite-dimensional, which does not occur
for divisor fibres in the relative-curve regime) and is what Kleiman's
`deg D_t` means.  When B3 lands, `q_* O_D` is locally free of rank
`fiberDeg` and the two vocabularies fuse.

**AUDIT (base change, D1').** `fiberDeg` is stable under arbitrary base change
`ψ : T' ⟶ T` (`fiberDeg_pullbackAlong`): the fibre of `X_{T'}/T'` at `t'` is
the base change of the fibre of `X_T/T` at `t = ψ(t')` along the residue
extension `κ(t) → κ(t')`, and `H⁰` of a finitely presented module with proper
support commutes with base field extension (Stacks 02KH at `i = 0`).  This is
proved **axiom-clean** from the twist-free Γ-fibre core
`Scheme.finrank_gammaTop_baseChange_of_hasProperSupport`
(`Picard/SchematicSupport.lean`) — NOT from the twisted engine
`Scheme.hilbertFunction_quotBaseMap` (`Picard/QuotFunctorDef.lean`), which
still rests on the sorried tensor–pullback leaf
`Modules.pullbackTensorMap_isIso`.  At `m = 0` no twist is needed, so the
degree lane stays sorry-free (recon correction to the campaign plan's
"the 02KE/02KH engine is landed" — only its untwisted core is).

## The clopen degree decomposition — honest form

**AUDIT (coproduct pin, D1').** The naive presheaf-level statement
"`DivFunctor = ⨿_d DivFunctorDeg d`" is FALSE: on a disconnected `T` a family
with non-constant fibre degree lies in no degree piece, and at `T = ∅` every
piece contains the (unique) empty family, so the pieces are not disjoint.  The
honest pins delivered here are:

* every `T`-point decomposes `T` into clopen constant-degree pieces
  (`DivFamily.degLocus`, `DivFamily.hasFiberDeg_pullbackAlong_degLocusHom`,
  `DivFamily.iSup_degLocus`, `DivFamily.degLocus_disjoint`) — this is the form
  the coproduct assembly `G4` (`hom_sigma_decompose`) consumes;
* on a nonempty preconnected `T` the canonical comparison
  `Σ_d (DivFunctorDeg π d)(T) → DivFunctor π (T)` is a bijection
  (`divFunctorDeg_sigma_bijective`);
* degree pieces of a common class agree (`DivFamily.ClassHasFiberDeg.unique`,
  nonempty `T`).

The only non-formal input is **Zariski-local constancy of the fibre degree**.
This is TRUE in the campaign regime (relative curve: `D → T` is
proper + quasi-finite, hence finite, and a finitely presented `T`-flat module
with finite support has finite locally free pushforward — Mumford, *Abelian
Varieties* II §5; Kleiman §3 Ex. `ex:DivC`) but is NOT derivable from the
current in-tree substrate (it needs the finite/rank half of the B3 pushforward
engine plus `D_t` finite from relative dimension 1).  Following the house gate
pattern (`HasPicScheme`), it is pinned as the instance-free Prop-class
`HasLocallyConstantDivDeg C` at the AJC curve regime, and every decomposition
statement is ALSO provided in hypothesis-parametrized form (an explicit
`IsLocallyConstant x.fiberDeg` argument), so the eventual discharge is a
one-line instance.  We deliberately do NOT state the gate for general `π`:
for relative dimension `≥ 2` the fibre rank of `O_{D_t}` can jump (only `χ` is
locally constant), which is why Kleiman filters `Div` by Hilbert polynomials in
general and by the degree only over curves.

## The degree ledger and the Abel-map sign (A2)

**Sign convention (audit item 7-half).** The Abel map is
`abelMapWitness C = abelKernelNatTrans C ≫ picNeg C`, i.e.

  `[D] ↦ [O(D)] = [I_D⁻¹] = -[ker q]`  —

a divisor family maps to the *negative* of the class of its ideal sheaf
(`Picard/FGAPicRepresentability.lean:461`).  The degree-refined Abel map
`abelDeg C d : divFunctorDeg C d ⟶ picSharp C` is the restriction of
`abelMapWitness` along the degree-`d` inclusion; its defining property is
`abelDeg_app_mk`.  It deliberately lands in `picSharp C` — carving out
`picSharpDeg C d` is milestone B4, not this file.

**AUDIT (degree-coherence vocabulary, A2).** "The ideal sheaf `ker q` of a
rank-`d` family has fibre degree `−d`" is stated in the **rank (colength)
vocabulary** — the strongest honestly-provable form today: the χ-ledger
(`deg = χ(I) − χ(O)`, campaign P3) is unbuilt, and the adelic
`RiemannRoch/WeilDivisor` degree cannot yet be attached to the sheaf-theoretic
line bundle `ker q` on a family fibre (that needs the `M ≅ O(div s)`
regular-section bricks, also P3).  What IS proved, per fibre `t`:

* the ideal restricts to the fibre: the kernel–pullback comparison
  `(I_D)_t ≅ ker(q_t)` is an isomorphism (`DivFamily.fiberKernelIso`) and the
  fibre ideal inclusion `(I_D)_t ↪ O_{X_t}` stays monic
  (`DivFamily.mono_fiber_kernel_ι`) with `(I_D)_t` invertible
  (`DivFamily.isLocallyTrivial_fiber_kernel`) — `D_t ⊆ X_t` is an honest
  effective Cartier divisor (Kleiman §3, note after Def. `df:div`);
* its colength is the degree: `O_{X_t}/(I_D)_t ≅ (O_D)_t`
  (`DivFamily.fiberCokernelIso`), so
  `dim_{κ(t)} Γ(coker((I_D)_t ↪ O_{X_t})) = fiberDeg x t = d`
  (`DivFamily.fiberDeg_eq_finrank_fiber_cokernel`,
  `DivFamily.ClassHasFiberDeg.finrank_fiber_cokernel`).

In χ-ledger terms this is exactly `deg_t(ker q) = χ(I_t) − χ(O_{X_t}) = −d`;
the translation becomes a theorem once P3 lands.

## References

Blueprint: to be attached to the campaign's D1'/A2 nodes.
Source: [Kleiman], "The Picard scheme" (arXiv:math/0504020), §3
(Def. `df:div`, Def. `dfn:Abel`, Ex. `ex:DivC`); Mumford, *Abelian Varieties*,
II §5 (finite flat pushforward, for the gate's discharge route);
Stacks 02KH (`i = 0`) for the base-change core.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

variable {S X : Scheme.{u}}

/-! ## §0. Dimension transport for fibre section modules -/

set_option backward.isDefEq.respectTransparency false in
/-- **Transport of the fibre-section dimension along an isomorphism of fibre
modules.**  An isomorphism of sheaves of modules on the scheme-theoretic fibre
`π₀.fiber s` induces a `κ(s)`-linear equivalence on global sections
(evaluation at `⊤` is functorial, and the `κ(s)`-scalar action factors through
`Scheme.Hom.fiberResidueMap`), so the `κ(s)`-dimensions agree.  Twist-free
sibling of `Scheme.hilbertFunction_eq_finrank_of_iso`
(`Picard/QuotFunctorDef.lean`), serving the degree lane where no tensor
operations may enter. -/
lemma finrank_fiberSections_eq_of_iso {W B : Scheme.{u}} (π₀ : W ⟶ B) (s : B)
    {G G' : (π₀.fiber s).Modules} (e : G ≅ G') :
    (letI := π₀.fiberSectionsModule s G
     Module.finrank (B.residueField s) Γ(G, ⊤))
      = (letI := π₀.fiberSectionsModule s G'
         Module.finrank (B.residueField s) Γ(G', ⊤)) := by
  letI := π₀.fiberSectionsModule s G
  letI := π₀.fiberSectionsModule s G'
  have γe := ((Scheme.Modules.toPresheafOfModules (π₀.fiber s) ⋙
    PresheafOfModules.evaluation (π₀.fiber s).ringCatSheaf.obj (Opposite.op ⊤)).mapIso
      e).toLinearEquiv
  exact LinearEquiv.finrank_eq
    { toFun := γe
      map_add' := γe.map_add
      map_smul' := fun c x => γe.map_smul ((π₀.fiberResidueMap s).hom c) x
      invFun := γe.symm
      left_inv := γe.left_inv
      right_inv := γe.right_inv }

/-! ## §1. The fibre degree of a family of relative effective divisors -/

namespace DivFamily

variable {π : X ⟶ S}

/-- The **fibre degree** of a family of relative effective divisors
`x : DivFamily π T` at a point `t : T` (Kleiman §3 Ex. `ex:DivC`):

  `deg D_t := dim_{κ(t)} Γ(D_t, O_{D_t}) = dim_{κ(t)} Γ((X_T)_t, F_t)`,

the `κ(t)`-dimension of the global sections of the restriction of the divisor
structure sheaf `F = O_D` to the scheme-theoretic fibre `(X_T)_t`.  This is
the pointwise shadow of "rank of the finite-flat pushforward `q_* O_D`" (equal
to it whenever the pushforward exists as a locally free module, i.e. in the
relative-curve regime once the B3 engine lands; see the module docstring
audit).  `Module.finrank` junk value `0` in the infinite-dimensional case. -/
noncomputable def fiberDeg {T : Over S} (x : DivFamily π T)
    (t : (T.left : Scheme.{u})) : ℕ :=
  letI := (pullback.snd π T.hom).fiberSectionsModule t
    ((pullback.snd π T.hom).fiberModule t x.F)
  Module.finrank (T.left.residueField t)
    Γ((pullback.snd π T.hom).fiberModule t x.F, ⊤)

/-- **The fibre degree is well defined on divisor classes**: equivalent
families (`DivFamily.Rel`, i.e. same divisor `ker q = ker q'`) have equal
fibre degrees — the target isomorphism restricts to each fibre and transports
the section dimension. -/
theorem Rel.fiberDeg_eq {T : Over S} {x y : DivFamily π T} (h : x.Rel y)
    (t : (T.left : Scheme.{u})) : x.fiberDeg t = y.fiberDeg t := by
  obtain ⟨f, -⟩ := h
  exact finrank_fiberSections_eq_of_iso (pullback.snd π T.hom) t
    ((Scheme.Modules.pullback ((pullback.snd π T.hom).fiberι t)).mapIso f)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Heartbeat headroom: instantiating the Γ-fibre base-change core provisions
-- pullback/pushforward and field instances under binders, as in the sibling
-- engines of `QuotFunctorDef`.
/-- **The fibre degree is stable under base change** (Stacks 02KH at `i = 0`;
Kleiman §3, functoriality of `Div`): for `ψ : T' ⟶ T` and `t' : T'` over
`t := ψ(t')`, the fibre degree of the pulled-back family at `t'` equals the
fibre degree of `x` at `t`.

Route (all inputs axiom-clean): the fibre of `X_{T'}/T'` at `t'` is the base
change of the fibre of `X_T/T` at `t` along `Spec κ(t') → Spec κ(t)`
(`Scheme.isPullback_fiberBaseChange`, the `quotBaseSquare`/residue-field
pasting); the two fibre restrictions of `F` are matched by pseudofunctor
coherence (`Scheme.pullbackSquareIso`); proper support of `F/T` restricts to
the fibre (`Modules.HasProperSupport.of_isPullback` on Mathlib's fibre
square); and the twist-free Γ-fibre flat base-change core
`Scheme.finrank_gammaTop_baseChange_of_hasProperSupport`
(`Picard/SchematicSupport.lean` — support descent `G ≅ i_* i^* G` + the
CLOSED 02KE heart) transports the dimension across the residue extension.
No tensor operations enter, so — unlike the twisted engine
`hilbertFunction_quotBaseMap` — this consumes no sorried leaf. -/
theorem fiberDeg_pullbackAlong {T T' : Over S} (ψ : T' ⟶ T) (x : DivFamily π T)
    (t' : (T'.left : Scheme.{u})) :
    (x.pullbackAlong ψ).fiberDeg t' = x.fiberDeg (ψ.left.base t') := by
  haveI hFqc : x.F.IsQuasicoherent := letI := x.isFinitePresentation; inferInstance
  haveI : ((pullback.snd π T.hom).fiberModule (ψ.left.base t') x.F).IsQuasicoherent :=
    pullback_isQuasicoherent_hom _ x.F hFqc
  have hpsFt : Modules.HasProperSupport
      ((pullback.snd π T.hom).fiberToSpecResidueField (ψ.left.base t'))
      ((pullback.snd π T.hom).fiberModule (ψ.left.base t') x.F) :=
    Modules.HasProperSupport.of_isPullback
      (IsPullback.of_hasPullback (pullback.snd π T.hom)
        (T.left.fromSpecResidueField (ψ.left.base t')))
      x.F x.isFinitePresentation x.properSupport
  have eF : (pullback.snd π T'.hom).fiberModule t'
        ((Scheme.Modules.pullback (quotBaseMap π ψ)).obj x.F)
      ≅ (Scheme.Modules.pullback (fiberBaseChange π ψ t')).obj
          ((pullback.snd π T.hom).fiberModule (ψ.left.base t') x.F) :=
    pullbackSquareIso (fiberBaseChange_fiberι π ψ t').symm x.F
  exact (finrank_fiberSections_eq_of_iso (pullback.snd π T'.hom) t' eF).trans
    (Scheme.finrank_gammaTop_baseChange_of_hasProperSupport
      (Field.toIsField (T.left.residueField (ψ.left.base t')))
      (Field.toIsField (T'.left.residueField t'))
      (isPullback_fiberBaseChange π ψ t')
      ((pullback.snd π T.hom).fiberModule (ψ.left.base t') x.F) hpsFt)

/-! ## §2. The fibre of the ideal sheaf — Cartier fibres and the degree ledger

The `[D] ↦ -[ker q]` sign convention of the Abel map (module docstring) is
anchored fibrewise: on every fibre `X_t` of the family, the ideal sheaf
restricts to an honest invertible ideal `(I_D)_t ↪ O_{X_t}` cutting out the
fibre divisor `D_t`, and its colength `dim_{κ(t)} Γ(O_{X_t}/(I_D)_t)` is
exactly the fibre degree.  In χ-ledger terms (campaign P3, unbuilt):
`deg_t(ker q) = χ((I_D)_t) − χ(O_{X_t}) = −deg D_t = −d` for a degree-`d`
family. -/

/-- **The kernel ideal restricts to an invertible ideal on every fibre**
(Kleiman §3, note after Def. `df:div`, specialised to the fibre inclusion):
the kernel of the fibre restriction `q_t` of the quotient map is locally
trivial of rank one.  Instantiation of the divisor base-change theorem
`Modules.pullback_kernel_isLocallyTrivial`
(`lem:relative_divisor_base_change`) at Mathlib's fibre square. -/
theorem isLocallyTrivial_fiber_kernel {T : Over S} (x : DivFamily π T)
    (t : (T.left : Scheme.{u})) :
    LineBundle.IsLocallyTrivial (Limits.kernel
      ((Scheme.Modules.pullback ((pullback.snd π T.hom).fiberι t)).map x.q)) :=
  Modules.pullback_kernel_isLocallyTrivial
    (IsPullback.of_hasPullback (pullback.snd π T.hom)
      (T.left.fromSpecResidueField t)) x.q x.epi
    (pullback_isQuasicoherent_hom (pullback.fst π T.hom)
      (SheafOfModules.unit X.ringCatSheaf) inferInstance)
    x.isFinitePresentation x.flat x.kerLocallyTrivial

/-- **The ideal inclusion stays monic on every fibre**: `(I_D)_t ↪ O_{X_t}`
— the fibre divisor `D_t ⊆ X_t` is an effective Cartier divisor (its ideal is
an invertible subsheaf, not merely an invertible quotient-kernel).  This is
the flat-base-change monomorphism `Modules.mono_pullback_map_kernel_ι`
(Stacks 00HL affine-locally) at the fibre square: `T`-flatness of `O_D` is
what forbids the ideal from degenerating on special fibres. -/
theorem mono_fiber_kernel_ι {T : Over S} (x : DivFamily π T)
    (t : (T.left : Scheme.{u})) :
    Mono ((Scheme.Modules.pullback ((pullback.snd π T.hom).fiberι t)).map
      (Limits.kernel.ι x.q)) :=
  Modules.mono_pullback_map_kernel_ι
    (IsPullback.of_hasPullback (pullback.snd π T.hom)
      (T.left.fromSpecResidueField t)) x.q x.epi
    (pullback_isQuasicoherent_hom (pullback.fst π T.hom)
      (SheafOfModules.unit X.ringCatSheaf) inferInstance)
    x.isFinitePresentation x.flat x.kerLocallyTrivial

/-- **The fibre of the ideal is the ideal of the fibre**: the kernel–pullback
comparison `(I_D)_t = (ker q)|_{X_t} ⟶ ker(q_t)` is an isomorphism (Kleiman
§3: "Since `D` is `T`-flat, `p^* I` equals the ideal of `D_{T'}`", at
`T' = Spec κ(t)`).  The `IsIso` witness is passed to `asIso` explicitly (the
project `@asIso` idiom), so no instance search runs. -/
noncomputable def fiberKernelIso {T : Over S} (x : DivFamily π T)
    (t : (T.left : Scheme.{u})) :
    (pullback.snd π T.hom).fiberModule t (Limits.kernel x.q)
      ≅ Limits.kernel
          ((Scheme.Modules.pullback ((pullback.snd π T.hom).fiberι t)).map x.q) :=
  @asIso _ _ _ _
    (Modules.pullbackKernelComparison ((pullback.snd π T.hom).fiberι t) x.q)
    (Modules.isIso_pullbackKernelComparison
      (IsPullback.of_hasPullback (pullback.snd π T.hom)
        (T.left.fromSpecResidueField t)) x.q x.epi
      (pullback_isQuasicoherent_hom (pullback.fst π T.hom)
        (SheafOfModules.unit X.ringCatSheaf) inferInstance)
      x.isFinitePresentation x.flat x.kerLocallyTrivial)

set_option backward.isDefEq.respectTransparency false in
/-- **The fibre of the divisor structure sheaf is the cokernel of the fibre
ideal inclusion**: `O_{X_t}/(I_D)_t ≅ (O_D)_t`.  In the abelian category
`(X_T).Modules` the epimorphism `q` is the cokernel of its kernel
(`ShortComplex.Exact.gIsCokernel`), and the module pullback along the fibre
inclusion — a left adjoint (`Modules.pullbackPushforwardAdjunction`) —
preserves the cokernel cofork.  Together with `fiberKernelIso` and
`mono_fiber_kernel_ι` this realizes the fibre short exact sequence
`0 → (I_D)_t → O_{X_t} → O_{D_t} → 0` of an effective Cartier divisor. -/
noncomputable def fiberCokernelIso {T : Over S} (x : DivFamily π T)
    (t : (T.left : Scheme.{u})) :
    Limits.cokernel
        ((Scheme.Modules.pullback ((pullback.snd π T.hom).fiberι t)).map
          (Limits.kernel.ι x.q))
      ≅ (pullback.snd π T.hom).fiberModule t x.F :=
  haveI := x.epi
  haveI : PreservesColimitsOfSize.{0, 0}
      (Scheme.Modules.pullback ((pullback.snd π T.hom).fiberι t)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction
      ((pullback.snd π T.hom).fiberι t)).leftAdjoint_preservesColimits
  haveI : Epi (((ShortComplex.mk (Limits.kernel.ι x.q) x.q
      (Limits.kernel.condition x.q)).map
        (Scheme.Modules.pullback ((pullback.snd π T.hom).fiberι t))).g) :=
    @CategoryTheory.Functor.map_epi _ _ _ _
      (Scheme.Modules.pullback ((pullback.snd π T.hom).fiberι t)) inferInstance
      _ _ x.q x.epi
  ((colimit.isColimit _).coconePointUniqueUpToIso
    (((CategoryTheory.ShortComplex.exact_kernel x.q).map_of_epi_of_preservesCokernel
      (Scheme.Modules.pullback ((pullback.snd π T.hom).fiberι t)) x.epi
      inferInstance).gIsCokernel))

set_option backward.isDefEq.respectTransparency false in
/-- **The degree ledger, rank vocabulary** (the A2 degree-coherence lemma, in
the strongest honestly-provable form today — see the module docstring audit):
the fibre degree of a divisor family is the **colength of its fibre ideal**,

  `fiberDeg x t = dim_{κ(t)} Γ(X_t, coker((I_D)_t ↪ O_{X_t}))`.

In χ-ledger terms this is `deg_t(ker q) = χ((I_D)_t) − χ(O_{X_t}) = −fiberDeg x t`
— "the ideal sheaf of a rank-`d` family has fibre degree `−d`" — pending the
P3 χ-ledger to phrase the left-hand side. -/
theorem fiberDeg_eq_finrank_fiber_cokernel {T : Over S} (x : DivFamily π T)
    (t : (T.left : Scheme.{u})) :
    x.fiberDeg t
      = (letI := (pullback.snd π T.hom).fiberSectionsModule t
          (Limits.cokernel
            ((Scheme.Modules.pullback ((pullback.snd π T.hom).fiberι t)).map
              (Limits.kernel.ι x.q)))
         Module.finrank (T.left.residueField t)
          Γ(Limits.cokernel
              ((Scheme.Modules.pullback ((pullback.snd π T.hom).fiberι t)).map
                (Limits.kernel.ι x.q)), ⊤)) :=
  (finrank_fiberSections_eq_of_iso (pullback.snd π T.hom) t
    (x.fiberCokernelIso t)).symm

/-! ## §3. Constant-degree families -/

/-- A divisor family **has (constant) fibre degree `d`** when every fibre
divisor has degree `d` (Kleiman §3 Ex. `ex:DivC`).  Vacuously true for every
`d` when `T` is empty — which is why the degree pieces of `DivFunctor` are
pairwise disjoint only over nonempty bases (`ClassHasFiberDeg.unique`). -/
def HasFiberDeg {T : Over S} (x : DivFamily π T) (d : ℕ) : Prop :=
  ∀ t : (T.left : Scheme.{u}), x.fiberDeg t = d

/-- Constant fibre degree is invariant under the divisor equivalence
(`DivFamily.Rel`): well-definedness input for the degree slice of the
quotient functor. -/
theorem Rel.hasFiberDeg_iff {T : Over S} {x y : DivFamily π T} (h : x.Rel y)
    (d : ℕ) : x.HasFiberDeg d ↔ y.HasFiberDeg d :=
  forall_congr' fun t => by rw [h.fiberDeg_eq t]

/-- Constant fibre degree is stable under arbitrary base change — the degree
slice `DivFunctorDeg` is a subfunctor, not just a sub-presheaf-of-sets.
Immediate from `fiberDeg_pullbackAlong`. -/
theorem HasFiberDeg.pullbackAlong {T T' : Over S} {x : DivFamily π T} {d : ℕ}
    (hx : x.HasFiberDeg d) (ψ : T' ⟶ T) :
    (x.pullbackAlong ψ).HasFiberDeg d :=
  fun t' => (fiberDeg_pullbackAlong ψ x t').trans (hx (ψ.left.base t'))

/-- Constant fibre degree, descended to the divisor classes
`Quotient (DivFamily.setoid π T)` — the carrier predicate of
`DivFunctorDeg π d`.  Well defined by `Rel.hasFiberDeg_iff`. -/
def ClassHasFiberDeg {T : Over S} (d : ℕ)
    (z : Quotient (DivFamily.setoid π T)) : Prop :=
  Quotient.liftOn z (fun x => x.HasFiberDeg d)
    fun _ _ h => propext (h.hasFiberDeg_iff d)

@[simp]
theorem classHasFiberDeg_mk {T : Over S} (d : ℕ) (x : DivFamily π T) :
    ClassHasFiberDeg d (Quotient.mk (DivFamily.setoid π T) x) ↔ x.HasFiberDeg d :=
  Iff.rfl

/-- Base-change stability of the class-level degree predicate — the
functoriality input of `DivFunctorDeg`. -/
theorem ClassHasFiberDeg.map {T T' : Over S} {d : ℕ}
    {z : Quotient (DivFamily.setoid π T)} (hz : ClassHasFiberDeg d z)
    (ψ : T' ⟶ T) :
    ClassHasFiberDeg d (Quotient.map (DivFamily.pullbackAlong ψ)
      (fun _ _ h => DivFamily.pullbackAlong_rel ψ h) z) := by
  induction z using Quotient.ind with
  | _ x =>
    intro t'
    exact (fiberDeg_pullbackAlong ψ x t').trans (hz (ψ.left.base t'))

/-- **Over a nonempty base the degree of a class is unique** — the degree
pieces of `DivFunctor` are pairwise disjoint on nonempty `T` (and only there:
at `T = ∅` every class has every degree, see the module docstring audit). -/
theorem ClassHasFiberDeg.unique {T : Over S}
    (hne : Nonempty (T.left : Scheme.{u})) {d d' : ℕ}
    {z : Quotient (DivFamily.setoid π T)}
    (h : ClassHasFiberDeg d z) (h' : ClassHasFiberDeg d' z) : d = d' := by
  induction z using Quotient.ind with
  | _ x =>
    obtain ⟨t⟩ := hne
    exact (h t).symm.trans (h' t)

/-- **Degree side of the A2 sign audit** (rank vocabulary — see the module
docstring audit): a representative of a degree-`d` divisor class has, at
every point `t` of `T`, fibre ideal of colength `d`:

  `dim_{κ(t)} Γ(X_t, coker((I_D)_t ↪ O_{X_t})) = d`.

Combined with the sign convention `[D] ↦ -[ker q]` of the Abel map
(`PicScheme.abelDeg_app_mk`) this is the honest content of "the ideal sheaf
`ker q` of a rank-`d` family has fibre degree `−d`" available before the P3
χ-ledger lands. -/
theorem ClassHasFiberDeg.finrank_fiber_cokernel {T : Over S} {d : ℕ}
    (x : DivFamily π T)
    (hx : ClassHasFiberDeg d (Quotient.mk (DivFamily.setoid π T) x))
    (t : (T.left : Scheme.{u})) :
    (letI := (pullback.snd π T.hom).fiberSectionsModule t
        (Limits.cokernel
          ((Scheme.Modules.pullback ((pullback.snd π T.hom).fiberι t)).map
            (Limits.kernel.ι x.q)))
     Module.finrank (T.left.residueField t)
      Γ(Limits.cokernel
          ((Scheme.Modules.pullback ((pullback.snd π T.hom).fiberι t)).map
            (Limits.kernel.ι x.q)), ⊤))
      = d :=
  (x.fiberDeg_eq_finrank_fiber_cokernel t).symm.trans (hx t)

end DivFamily

/-! ## §4. The degree-`d` divisor functor -/

/-- The **degree-`d` relative-divisor functor** `Div^d_{X/S} ⊆ Div_{X/S}`
(Kleiman §3 Ex. `ex:DivC`): the subfunctor of `Scheme.DivFunctor π` of divisor
classes whose every fibre divisor has degree `d`
(`DivFamily.ClassHasFiberDeg`, the rank-`d`-pushforward condition in its
pointwise fibre-section form — see the module docstring audit).  The pullback
action is that of `DivFunctor`, restricted along the base-change stability
`DivFamily.ClassHasFiberDeg.map`; the functor laws are inherited pointwise
from `DivFunctor`.

Kept at full generality (`π : X ⟶ S` arbitrary, matching `DivFunctor`); in
the FGA regime (`π` proper, `[IsProper C.hom]`) the `properSupport` field of
`DivFamily` is automatic, so the `T`-points are honestly Kleiman's degree-`d`
relative effective divisors. -/
noncomputable def DivFunctorDeg (π : X ⟶ S) (d : ℕ) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := { z : Quotient (DivFamily.setoid π T.unop) //
    DivFamily.ClassHasFiberDeg d z }
  map {T T'} g := TypeCat.ofHom fun z =>
    ⟨Quotient.map (DivFamily.pullbackAlong g.unop)
        (fun _ _ h => DivFamily.pullbackAlong_rel g.unop h) z.1,
      z.2.map g.unop⟩
  map_id T := by
    ext z
    exact congrFun (congrArg (fun f => ((TypeCat.Hom.hom f : TypeCat.Fun _ _) : _ → _))
      ((DivFunctor π).map_id T)) z.1
  map_comp {T T' T''} g h := by
    ext z
    exact congrFun (congrArg (fun f => ((TypeCat.Hom.hom f : TypeCat.Fun _ _) : _ → _))
      ((DivFunctor π).map_comp g h)) z.1

/-- The canonical inclusion `Div^d_{X/S} ⟶ Div_{X/S}` — the subfunctor
inclusion of the degree-`d` slice, forgetting the constant-degree witness.
Componentwise injective (`divFunctorDegι_app_injective`). -/
noncomputable def divFunctorDegι (π : X ⟶ S) (d : ℕ) :
    DivFunctorDeg π d ⟶ DivFunctor π where
  app _ := TypeCat.ofHom Subtype.val
  naturality _ _ _ := rfl

/-- The degree-`d` inclusion is componentwise injective: `DivFunctorDeg π d`
is a subfunctor of `DivFunctor π`. -/
theorem divFunctorDegι_app_injective (π : X ⟶ S) (d : ℕ)
    (T : (Over S)ᵒᵖ) :
    Function.Injective ((divFunctorDegι π d).app T : _ → _) :=
  fun _ _ h => Subtype.ext h

/-! ## §5. The clopen degree decomposition -/

namespace DivFamily

variable {π : X ⟶ S}

/-- The **degree-`d` locus** of a divisor family with locally constant fibre
degree: the clopen open subset `{t : T | deg D_t = d}` of the base.  The
local-constancy hypothesis is explicit (its discharge in the relative-curve
regime is the `HasLocallyConstantDivDeg` gate — see the module docstring). -/
def degLocus {T : Over S} (x : DivFamily π T)
    (hlc : IsLocallyConstant x.fiberDeg) (d : ℕ) : (T.left : Scheme.{u}).Opens :=
  ⟨{t | x.fiberDeg t = d}, hlc.isOpen_fiber d⟩

/-- The degree-`d` locus is clopen. -/
theorem isClopen_degLocus {T : Over S} (x : DivFamily π T)
    (hlc : IsLocallyConstant x.fiberDeg) (d : ℕ) :
    IsClopen ((x.degLocus hlc d : TopologicalSpace.Opens (T.left : Scheme.{u})) :
      Set (T.left : Scheme.{u})) :=
  hlc.isClopen_fiber d

/-- The degree loci cover the base: every point lies in the locus of its own
fibre degree. -/
theorem iSup_degLocus {T : Over S} (x : DivFamily π T)
    (hlc : IsLocallyConstant x.fiberDeg) :
    ⨆ d : ℕ, x.degLocus hlc d = ⊤ := by
  rw [eq_top_iff]
  intro t _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x.fiberDeg t, rfl⟩

/-- The degree loci are pairwise disjoint: the fibre degree is a single
natural number at every point. -/
theorem degLocus_disjoint {T : Over S} (x : DivFamily π T)
    (hlc : IsLocallyConstant x.fiberDeg) {d d' : ℕ} (h : d ≠ d') :
    Disjoint (x.degLocus hlc d) (x.degLocus hlc d') := by
  refine disjoint_iff.mpr (TopologicalSpace.Opens.ext ?_)
  ext t
  simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff,
    TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  exact h ((show x.fiberDeg t = d from h1).symm.trans
    (show x.fiberDeg t = d' from h2))

/-- The clopen immersion of the degree-`d` locus, as a morphism of `Over S`:
the piece of the clopen decomposition along which the family restricts to a
constant-degree family (`hasFiberDeg_pullbackAlong_degLocusHom`). -/
noncomputable def degLocusHom {T : Over S} (x : DivFamily π T)
    (hlc : IsLocallyConstant x.fiberDeg) (d : ℕ) :
    Over.mk ((x.degLocus hlc d).ι ≫ T.hom) ⟶ T :=
  Over.homMk (x.degLocus hlc d).ι rfl

/-- **Every `T`-point of `Div` decomposes `T` into clopen constant-degree
pieces** (the honest form of `Div = ∐_d Div^d`, per-family half): the
restriction of the family to its degree-`d` locus has constant fibre degree
`d`.  Together with `iSup_degLocus`/`degLocus_disjoint`/`isClopen_degLocus`
this is the clopen decomposition the coproduct assembly (campaign G4)
consumes. -/
theorem hasFiberDeg_pullbackAlong_degLocusHom {T : Over S} (x : DivFamily π T)
    (hlc : IsLocallyConstant x.fiberDeg) (d : ℕ) :
    (x.pullbackAlong (x.degLocusHom hlc d)).HasFiberDeg d := by
  intro t'
  rw [fiberDeg_pullbackAlong]
  exact t'.2

end DivFamily

/-- **`Div = ∐_d Div^d` on connected bases** (the honest functor-level form of
the degree decomposition — see the module docstring audit for why the
unrestricted presheaf statement is false): over a nonempty preconnected `T`,
the canonical comparison `Σ_d Div^d(T) → Div(T)` is a bijection, granted the
local constancy of fibre degrees (hypothesis-parametrized; in the AJC curve
regime it is the `HasLocallyConstantDivDeg` gate, see
`divFunctorDeg_sigma_bijective_of_gate`).  Injectivity is degree-uniqueness on
a nonempty base; surjectivity is "locally constant on preconnected = constant"
(`IsLocallyConstant.apply_eq_of_preconnectedSpace`). -/
theorem divFunctorDeg_sigma_bijective (π : X ⟶ S) {T : (Over S)ᵒᵖ}
    (hne : Nonempty (T.unop.left : Scheme.{u}))
    (hpc : PreconnectedSpace (T.unop.left : Scheme.{u}))
    (hlc : ∀ x : DivFamily π T.unop, IsLocallyConstant x.fiberDeg) :
    Function.Bijective fun p : (Σ d : ℕ, (DivFunctorDeg π d).obj T) =>
      (p.2.1 : (DivFunctor π).obj T) := by
  constructor
  · rintro ⟨d, z, hz⟩ ⟨d', z', hz'⟩ h
    obtain rfl : z = z' := h
    obtain rfl : d = d' := DivFamily.ClassHasFiberDeg.unique hne hz hz'
    rfl
  · intro z
    induction z using Quotient.ind with
    | _ x =>
      obtain ⟨t₀⟩ := hne
      haveI := hpc
      exact ⟨⟨x.fiberDeg t₀, ⟨Quotient.mk _ x,
        fun t => (hlc x).apply_eq_of_preconnectedSpace t t₀⟩⟩, rfl⟩

/-! ## §6. The local-constancy gate (relative-curve regime) -/

/-- **Gate: divisor families on the curve have locally constant fibre degree**
(instance-free Prop-class, house `HasPicScheme` pattern — the deep heart is
deferred, never sorried).

Mathematical content (TRUE at this pinned generality; Mumford, *Abelian
Varieties* II §5; Kleiman §3 Ex. `ex:DivC`): for a smooth proper relative
curve `C/k` and any `T`, a relative effective divisor `D ⊆ C ×_k T` is finite
flat over `T` (proper + quasi-finite: each `D_t` is the zero scheme of a
regular section of an invertible ideal on the curve `C_t`, hence
`0`-dimensional), so `q_* O_D` is finite locally free and its fibre rank —
`DivFamily.fiberDeg` — is Zariski-locally constant.  Discharge route: the
finiteness/rank half of the campaign's B3 rigid-pushforward engine plus
relative-dimension-1 quasi-finiteness; both are outside the current in-tree
substrate, hence the gate.

Deliberately NOT stated for general `π : X ⟶ S`: in relative dimension `≥ 2`
the fibre rank of `O_{D_t}` can jump (only `χ(O_{D_t})` is locally constant),
which is why Kleiman filters `Div` by Hilbert polynomials in general.  All
decomposition theorems are also available in hypothesis-parametrized form
(explicit `IsLocallyConstant x.fiberDeg` argument), so this class is a pure
convenience pin at the AJC regime. -/
class HasLocallyConstantDivDeg {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] : Prop where
  /-- Every divisor family on the relative curve has Zariski-locally constant
  fibre degree. -/
  isLocallyConstant : ∀ (T : Over (Spec (.of k))) (x : DivFamily C.hom T),
    IsLocallyConstant x.fiberDeg

/-- `Div_{C/k} = ∐_d Div^d_{C/k}` on nonempty connected bases, gated form:
the sigma comparison is bijective for the AJC curve, granted the
`HasLocallyConstantDivDeg` gate. -/
theorem divFunctorDeg_sigma_bijective_of_gate {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [HasLocallyConstantDivDeg C] {T : (Over (Spec (.of k)))ᵒᵖ}
    (hne : Nonempty (T.unop.left : Scheme.{u}))
    (hpc : PreconnectedSpace (T.unop.left : Scheme.{u})) :
    Function.Bijective fun p : (Σ d : ℕ, (DivFunctorDeg C.hom d).obj T) =>
      (p.2.1 : (DivFunctor C.hom).obj T) :=
  divFunctorDeg_sigma_bijective C.hom hne hpc
    (fun x => HasLocallyConstantDivDeg.isLocallyConstant T.unop x)

/-! ## §7. A2 — the degree-refined Abel map -/

namespace PicScheme

variable {k : Type u} [Field k]

/-- The degree-`d` relative-divisor functor of the AJC curve,
`Div^d_{C/k} := DivFunctorDeg C.hom d` — the A.2.c-side avatar of the general
degree slice, mirroring `divFunctor C = DivFunctor C.hom`
(`Picard/FGAPicRepresentability.lean`). -/
noncomputable def divFunctorDeg (C : Over (Spec (.of k))) (d : ℕ) :
    (Over (Spec (.of k)))ᵒᵖ ⥤ Type (u + 1) :=
  DivFunctorDeg C.hom d

/-- **The degree-refined Abel map** `A^d_{C/k} : Div^d_{C/k} ⟶ Pic^♯_{C/k}`
(Kleiman §3 Def. `dfn:Abel`, restricted to the degree-`d` slice): the
composite of the degree-`d` inclusion with the substantive Abel map
`abelMapWitness C`, so on points

  `[D] ↦ [O(D)] = [I_D⁻¹] = -[ker q]`  (defining property `abelDeg_app_mk`).

Sign convention (audit item 7-half): the divisor class maps to the **negative**
of the ideal-sheaf class; the fibre-degree ledger for the ideal side is
`DivFamily.fiberDeg_eq_finrank_fiber_cokernel` ("`ker q` has fibre degree
`−d`" in the rank vocabulary — module docstring audit).  The target is
deliberately the full `picSharp C`: carving out the degree-`d` Picard
subfunctor `picSharpDeg C d` is campaign milestone B4, and refactoring
`abelDeg` to corestrict onto it is part of that milestone, not this one. -/
noncomputable def abelDeg (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] (d : ℕ) :
    divFunctorDeg C d ⟶ picSharp C :=
  divFunctorDegι C.hom d ≫ abelMapWitness C

/-- **Defining property of the degree-refined Abel map** (Kleiman §3
Def. `dfn:Abel`): on the class of a degree-`d` divisor family `⟨F, q⟩` it
returns `[O(D)] = [I_D⁻¹]`, the additive inverse of the class of the ideal
sheaf `I_D = ker q` — the `[D] ↦ -[ker q]` sign convention, verbatim
compatible with `abelMap_app_mk` through the inclusion. -/
theorem abelDeg_app_mk (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] (d : ℕ)
    (T : (Over (Spec (.of k)))ᵒᵖ) (x : DivFamily C.hom T.unop)
    (hx : DivFamily.ClassHasFiberDeg d
      (Quotient.mk (DivFamily.setoid C.hom T.unop) x)) :
    (abelDeg C d).app T ⟨Quotient.mk (DivFamily.setoid C.hom T.unop) x, hx⟩ =
      - Quotient.mk (PicSharp.relPicSetoid C.hom T.unop.hom)
        (⟨kernel x.q, x.kerLocallyTrivial⟩ :
          LineBundle.OnProduct C.hom T.unop.hom) :=
  rfl

/-- The degree-refined Abel map factors the Abel map witness through the
degree-`d` inclusion — definitional, recorded for the blueprint. -/
theorem abelDeg_eq (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] (d : ℕ) :
    abelDeg C d = divFunctorDegι C.hom d ≫ abelMapWitness C :=
  rfl

end PicScheme

end Scheme

end AlgebraicGeometry
