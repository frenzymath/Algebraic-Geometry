/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivDegree
import AlgebraicJacobian.Picard.RepresentableByTerminal

/-!
# The empty divisor: the first inhabitant of `Scheme.DivFamily`

`Scheme.DivFamily π T` (`Picard/DivFunctorDef.lean`) is the carrier of the whole
divisor side of the Milne–Kollár campaign: `Scheme.DivFunctor`, its degree slices
`Scheme.DivFunctorDeg`, the Abel maps `abelDeg` / `abelMapWitness`, the flatness
inputs of `Picard/DivPushforwardFlat.lean`, and `IdentityComponent`'s
`ClassDegreePinned` acceptance test are all quantified over it. Until this file it
had **zero producers**, for any `π`, any base, and any test object including the
trivial one — measured with `exact?` and recorded in its own docstring. The
consequence recorded there: *every* statement quantified over a `DivFamily` was
"true but untested", with no instance to be wrong about.

This file supplies the first inhabitant, unconditionally in `π : X ⟶ S` and
`T : Over S`: the **empty divisor** `D = ∅`, whose structure sheaf `O_D` is the
zero module and whose ideal is all of `O_{X_T}`.

## Why the empty divisor satisfies the divisor condition

The divisor condition of `DivFamily` is that the kernel ideal `I = ker q` be
*invertible* (`LineBundle.IsLocallyTrivial`). For `q : O_{X_T} ⟶ 0` the kernel is
`O_{X_T}` itself (`Limits.kernelZeroIsoSource`), and the structure sheaf is
trivially locally trivial (`Scheme.PicSharp.isLocallyTrivial_unit`, restated here as
`isLocallyTrivial_unit'` because that one is `private`). So the invertible-ideal
condition — the field that makes `DivFamily` a divisor rather than an arbitrary
quotient — holds *for the reason it should*: `O_{X_T}/O_{X_T} = 0` cuts out the
empty subscheme, an effective divisor of degree zero.

The three remaining fields are properties of the zero module, and the file proves
each rather than assuming it:

* `isFinitePresentation` — the zero module is finitely presented. Mathlib has no
  instance for this (measured: `infer_instance` and `exact?` both fail on
  `(0 : Y.Modules).IsFinitePresentation`), so §1 builds the `QuasicoherentData`:
  the singleton family `{⊤}` covers the top of the opens site
  (`coversTop_singleton_top`), the restriction functor preserves zero objects
  (`preservesZeroMorphisms_overFunctor`, proved from `PresheafOfModules` extensionality
  because instance search for it times out), and a zero sheaf of modules has an
  *empty* presentation — no generators and no relations, both trivially finite.
* `flat` — flatness over the base. The section modules of a zero module are
  subsingletons, and a subsingleton module is flat.
* `properSupport` — the schematic support of the zero module is the subscheme cut
  out by the annihilator, which is `⊤`, so the support is **empty**
  (`Scheme.IdealSheafData.instIsEmptyCarrierCarrierCommRingCatSubschemeTop`) and any
  morphism out of it is proper via `IsProper.instOfIsFinite`. It is free here for that
  reason, and in particular with **no properness assumption on `π`**. (An earlier
  revision added "and it is a real hypothesis for a nonempty divisor". That half was
  never measured — nothing here or elsewhere in the project exhibits a divisor where
  `properSupport` fails or is expensive, and `DivFunctorDef.lean` says it is *automatic*
  when `π` is proper. Dropped rather than repaired: the free-here half is what this
  file establishes.)

## What this does and does not buy

**Does**: the divisor cluster is no longer vacuous. `Nonempty (DivFamily π T)` for
every `π` and `T`; `(DivFunctor π).obj (op T)` and `(DivFunctorDeg π 0).obj (op T)`
are inhabited; `HasFiberDeg zero 0`; and the base-change action carries `zero` to
`zero` (`pullbackAlong_zero`), so the classes are a global section of `DivFunctor`
rather than a fibrewise accident. Every theorem in `DivDegree.lean` and
`DivPushforwardFlat.lean` now has a witness to be checked against.

**Does not**: this closes no `sorry` and witnesses no antecedent of
`Scheme.fgaPicardRepresentability`. In particular it is *not* a step of D1′: the
campaign's D1′ wants divisor families of a **prescribed positive degree** `d`
arising from a very ample `O(1)`, which needs the projectivity input
(`AJC.picrep.projectivity`) and P5 uniform `H¹` vanishing. What the empty divisor
does for that programme is remove the possibility that the target type is
uninhabited — a question that had to be settled before any positive-degree producer
could be believed, and which no lane had settled in either direction.

**One caveat, stated because it is the natural over-reading.** The degree-zero slice
being inhabited does *not* make `DivFunctorDeg π 0` representable by the terminal
object `Over.mk (𝟙 S)`. That would need the slice to be a *singleton* at every test
object, and this file proves only the `Nonempty` half. The missing half is
`Subsingleton ((DivFunctorDeg π 0).obj (op T))` — i.e. that the empty divisor is the
*only* relative divisor of degree `0`. That is the expected statement (a degree-`0`
effective divisor on a fibre of a relative curve is empty), but it is a fact about
`fiberDeg`, not a formality: `fiberDeg` is a `finrank` with a junk value at
infinite dimension. Neither direction is proved here.

**Corrected, and the correction is the useful part** (fresh-context audit of this file,
2026-07-30). An earlier revision of this paragraph said "no lane holds it". That is
FALSE: the analogous `Subsingleton` *is* landed, hours earlier, on the **sibling**
project's carrier — `instSubsingletonDivFamZarZero`
(`AJCR Picard/DivisorFamilyDegreeZeroUnique.lean`) and, over an arbitrary test ring,
`instSubsingletonDivFamZarZeroGeneral` plus a full `RepresentableBy` producer
(`AJCR Picard/DivisorFamilyDegreeZeroRep.lean`).

What survives, for a **sharper** reason than the carrier mismatch: their proof is not
portable because it never passes through a `finrank` at all. It runs on `IsCertified`
and `rankAtStalk_eq_zero_iff_subsingleton` over `Away` localisations of section rings,
machinery that exists only on the Zariski-certified carrier `DivFamZar : Type u`. AJC's
`fiberDeg` is a `Module.finrank` of fibre sections. So the honest statement is: nobody
holds it *for `Scheme.DivFamily`*, and the sibling's landed route does not transport.
Their success is also evidence *against* this paragraph's own framing — it shows
degree-zero uniqueness can be reached without any finiteness-of-sections argument on a
suitable carrier, so "needs finiteness of the fibre sections" is a claim about AJC's
chosen `fiberDeg`, not about the mathematics. The row `AJC.picrep.divzero` records it as
the open question this file leaves.

## Main declarations

* `Scheme.DivFamily.zero π T` — the empty divisor family.
* `Scheme.DivFamily.instNonempty` — `Nonempty (DivFamily π T)`, as an instance.
* `Scheme.DivFamily.pullbackAlong_zero` — base change carries `zero` to `zero`.
* `Scheme.DivFamily.fiberDeg_zero` / `hasFiberDeg_zero` — the empty divisor has
  fibre degree `0` at every point.
* `Scheme.DivFunctor.zeroClass` / `Scheme.DivFunctorDeg.zeroClass` — the resulting
  inhabitants of the functor and of its degree-`0` slice, with
  `Scheme.DivFunctor.map_zeroClass` making the first a global section.
* `Scheme.Modules.isFinitePresentation_of_isZero` — reusable: a zero sheaf of
  modules on any scheme is finitely presented. Absent from Mathlib.
* `Scheme.Modules.coversTop_singleton_top`,
  `Scheme.Modules.preservesZeroMorphisms_overFunctor`,
  `Scheme.Modules.isZero_free_pempty` — the other reusable bricks §1 needed.

Every declaration here is `sorry`-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`), measured against
`Scheme.fgaPicardRepresentability` reporting `sorryAx` in the same probe file with the
oleans rebuilt first.

Reference: Kleiman, "The Picard scheme", §3 Def. `df:red`/`df:div`, Ex. `ex:DivC`
(arXiv:math/0504020).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry ZeroObject TopologicalSpace

namespace AlgebraicGeometry

/-! ## §1. A zero sheaf of modules is finitely presented

Mathlib carries no instance for this (`infer_instance` and `exact?` both fail on
`(0 : Y.Modules).IsFinitePresentation`), so the `QuasicoherentData` is built by
hand: one cover member `⊤`, no generators, no relations. -/

namespace Scheme.Modules

variable {Y : Scheme.{u}}

/-- **The singleton family `{⊤}` covers the top of the opens site.**

The one covering datum every "global" presentation needs, and the reason a *global*
presentation of a sheaf of modules on `Y` is already a `QuasicoherentData`: the sieve
`Sieve.ofObjects (fun _ => ⊤) V` is the top sieve at every open `V`, because
`V ≤ ⊤` supplies the required arrow. -/
theorem coversTop_singleton_top :
    (Opens.grothendieckTopology (Y : TopCat)).CoversTop
      (fun _ : PUnit.{u+1} => (⊤ : TopologicalSpace.Opens (Y : TopCat))) := by
  intro V
  have h : Sieve.ofObjects
      (fun _ : PUnit.{u+1} => (⊤ : TopologicalSpace.Opens (Y : TopCat))) V = ⊤ := by
    ext W _
    simp only [Sieve.top_apply, iff_true]
    exact ⟨PUnit.unit, ⟨homOfLE le_top⟩⟩
  rw [h]
  exact GrothendieckTopology.top_mem _ _

set_option synthInstance.maxHeartbeats 1600000 in -- slice-site sheafification blow-up
set_option maxHeartbeats 2000000 in
/-- **The restriction functor to an open preserves zero morphisms.**

`SheafOfModules.overFunctor` is `SheafOfModules.pushforward (𝟙 _)`, which acts as the
identity on section groups, so the statement is `rfl` componentwise. It is proved
rather than synthesized because instance search for
`(overFunctor Y.ringCatSheaf U).PreservesZeroMorphisms` exhausts its heartbeat budget
(measured: `deterministic timeout at typeclass, 20000 heartbeats`) — the
sheafification/slice-site instances it unfolds are the same blow-up
`Scheme.Modules.presentationPullbackιOfQuasicoherentData` documents. -/
theorem preservesZeroMorphisms_overFunctor (U : TopologicalSpace.Opens (Y : TopCat)) :
    (SheafOfModules.overFunctor Y.ringCatSheaf U).PreservesZeroMorphisms := by
  constructor
  intro _ _
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro _
  rfl

/-- **The empty generating sections of a zero sheaf of modules.**

No generators at all: the structure map `free PEmpty ⟶ M` is epi because *every*
morphism into a zero object is, so there is nothing to generate. Stated for a general
sheaf of rings on the opens site so that both `M` and its restrictions `M.over U`
can use it. -/
def zeroGeneratingSections
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    {M : SheafOfModules.{u} R} (hM : IsZero M) : M.GeneratingSections where
  I := PEmpty.{u+1}
  s j := PEmpty.elim j
  epi := ⟨fun {_} g h _ => hM.eq_of_src g h⟩

instance zeroGeneratingSections_isFiniteType
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    {M : SheafOfModules.{u} R} (hM : IsZero M) :
    (zeroGeneratingSections hM).IsFiniteType where
  finite := (inferInstance : Finite PEmpty.{u+1})

/-- **`free PEmpty` is an initial, hence zero, sheaf of modules.**

There is exactly one morphism out of it into any target — `freeHomEquiv` turns a
morphism `free PEmpty ⟶ Z` into a family of sections indexed by `PEmpty`, of which
there is one — so it is initial, and an initial object in a category with zero
morphisms is a zero object. -/
theorem isZero_free_pempty
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] :
    IsZero (SheafOfModules.free (R := R) PEmpty.{u+1}) :=
  IsInitial.isZero <|
    IsInitial.ofUnique (h := fun Z =>
      ⟨⟨(SheafOfModules.freeHomEquiv Z).symm (fun j => PEmpty.elim j)⟩,
        fun _ => (SheafOfModules.freeHomEquiv Z).injective (funext fun j => PEmpty.elim j)⟩)

/-- **A zero sheaf of modules has an empty presentation** — no generators and no
relations.

The relations live in `kernel (zeroGeneratingSections hM).π`, whose source
`free PEmpty` is itself a zero object (`isZero_free_pempty`), so the kernel is zero
too and the empty family generates it for the same reason. -/
theorem isZero_kernel_zeroGeneratingSections
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    {M : SheafOfModules.{u} R} (hM : IsZero M) :
    IsZero (kernel (zeroGeneratingSections hM).π) :=
  haveI : Mono (zeroGeneratingSections hM).π := isZero_free_pempty.mono _
  isZero_kernel_of_mono _

noncomputable def zeroPresentation
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    {M : SheafOfModules.{u} R} (hM : IsZero M) : M.Presentation where
  generators := zeroGeneratingSections hM
  relations := zeroGeneratingSections (isZero_kernel_zeroGeneratingSections hM)

instance zeroPresentation_isFinite
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    {M : SheafOfModules.{u} R} (hM : IsZero M) : (zeroPresentation hM).IsFinite where
  isFiniteType_generators := zeroGeneratingSections_isFiniteType hM
  isFiniteType_relations :=
    zeroGeneratingSections_isFiniteType (isZero_kernel_zeroGeneratingSections hM)

set_option synthInstance.maxHeartbeats 1600000 in -- slice-site sheafification blow-up
set_option maxHeartbeats 2000000 in
/-- **The quasi-coherence datum of a zero sheaf of modules**: the singleton cover
`{⊤}`, with the empty presentation on it.

The restriction `M.over ⊤` of a zero module is zero
(`preservesZeroMorphisms_overFunctor` plus `Functor.map_isZero`), so
`zeroPresentation` applies on the cover member. -/
theorem isZero_over_of_isZero {M : Y.Modules} (hM : IsZero M)
    (U : TopologicalSpace.Opens (Y : TopCat)) : IsZero (M.over U) :=
  haveI := preservesZeroMorphisms_overFunctor (Y := Y) U
  Functor.map_isZero (SheafOfModules.overFunctor Y.ringCatSheaf U) hM

set_option synthInstance.maxHeartbeats 1600000 in -- slice-site `Over top` instances
set_option maxHeartbeats 2000000 in
noncomputable def zeroQuasicoherentData {M : Y.Modules} (hM : IsZero M) :
    M.QuasicoherentData where
  I := PUnit.{u+1}
  X _ := (⊤ : TopologicalSpace.Opens (Y : TopCat))
  coversTop := coversTop_singleton_top
  presentation _ := zeroPresentation (isZero_over_of_isZero hM _)

set_option synthInstance.maxHeartbeats 1600000 in -- as `zeroQuasicoherentData` above
set_option maxHeartbeats 2000000 in
instance zeroQuasicoherentData_isFinitePresentation {M : Y.Modules} (hM : IsZero M) :
    (zeroQuasicoherentData hM).IsFinitePresentation where
  isFinite_presentation _ := zeroPresentation_isFinite (isZero_over_of_isZero hM _)

set_option synthInstance.maxHeartbeats 1600000 in -- `shrink` re-enters slice synthesis
set_option maxHeartbeats 2000000 in
/-- **A zero sheaf of modules on a scheme is finitely presented.**

Absent from Mathlib: measured, `infer_instance` and `exact?` both fail on
`(0 : Y.Modules).IsFinitePresentation`. This is the field of `Scheme.DivFamily` that
had no route at `F = 0`, and it is why the empty divisor needed §1 rather than one
line. Everything else about the empty divisor is a one-lemma citation. -/
theorem isFinitePresentation_of_isZero {M : Y.Modules} (hM : IsZero M) :
    M.IsFinitePresentation where
  exists_quasicoherentData :=
    ⟨(zeroQuasicoherentData hM).shrink,
      { isFinite_presentation := fun _ =>
          zeroPresentation_isFinite (isZero_over_of_isZero hM _) }⟩

/-! ## §2. Flatness and proper support of a zero sheaf of modules -/

/-- **The sections of a zero sheaf of modules over any open form a subsingleton.**

`Scheme.Modules.toPresheaf` is additive, so it carries `M` to a zero presheaf of
abelian groups, whose value at `V` is a zero object of `Ab` and hence a
subsingleton. -/
theorem subsingleton_sections_of_isZero {M : Y.Modules} (hM : IsZero M)
    (V : Y.Opens) : Subsingleton Γ(M, V) :=
  AddCommGrpCat.subsingleton_of_isZero
    ((Functor.map_isZero (Scheme.Modules.toPresheaf Y) hM).obj _)

/-- **A zero sheaf of modules is flat over any base morphism**, with no hypothesis on
the morphism at all.

`CoherentSheafFlat` asks each section module `Γ(M, V)` to be flat over `Γ(S, U)`. The
section modules are subsingletons (`subsingleton_sections_of_isZero`), and a
subsingleton module is flat. -/
theorem coherentSheafFlat_of_isZero {S' : Scheme.{u}} (g : Y ⟶ S') {M : Y.Modules}
    (hM : IsZero M) : Scheme.CoherentSheafFlat g M := by
  intro U _ V _ e
  letI : Module Γ(S', U) Γ(M, V) := Module.compHom _ (g.appLE U V e).hom
  haveI := subsingleton_sections_of_isZero hM V
  exact inferInstance

/-- **The annihilator ideal sheaf of a zero sheaf of modules is `⊤`.**

Each affine-local annihilator is the whole ring (`Module.annihilator_eq_top_iff` at a
subsingleton module), and `ofIdeals` of the constant-`⊤` family is `⊤` because `⊤` is
itself an ideal sheaf below it. -/
theorem annihilator_of_isZero {M : Y.Modules} (hM : IsZero M) :
    Scheme.Modules.annihilator M = ⊤ :=
  top_le_iff.mp (le_sSup (by
    intro U
    haveI := subsingleton_sections_of_isZero hM U.1
    exact le_of_eq (Module.annihilator_eq_top_iff.mpr inferInstance).symm))

/-- **The schematic support of a zero sheaf of modules is empty.**

Its annihilator is `⊤`, and the subscheme cut out by the unit ideal sheaf has empty
carrier. -/
theorem isEmpty_schematicSupport_of_isZero {M : Y.Modules} (hM : IsZero M) :
    IsEmpty (Scheme.Modules.schematicSupport M) := by
  rw [Scheme.Modules.schematicSupport, annihilator_of_isZero hM]
  infer_instance

/-- **A zero sheaf of modules has proper support over any base**, unconditionally.

The support is empty, and a morphism out of an empty scheme is finite, hence proper.
This is the field of `DivFamily` that is a *real* hypothesis for a nonempty divisor —
properness of `D → T` — and it is free for the empty one, with **no** properness
assumption on the ambient morphism. -/
theorem hasProperSupport_of_isZero {S' : Scheme.{u}} (g : Y ⟶ S') {M : Y.Modules}
    (hM : IsZero M) : Scheme.Modules.HasProperSupport g M := by
  haveI := isEmpty_schematicSupport_of_isZero hM
  exact IsProper.instOfIsFinite _

/-- **A sheaf of modules whose sections vanish over every open is zero** — the exact
converse of `subsingleton_sections_of_isZero`, upgrading that forward implication to a
characterisation of the zero sheaf by its sections.

`Scheme.Modules.toPresheaf` is a faithful functor to `TopCat.Presheaf Ab`; if every
section group `Γ(M, V)` is a subsingleton then each value of the underlying presheaf is
a zero object of `Ab` (`AddCommGrpCat.isZero_of_subsingleton`), so the presheaf is a
zero functor (`CategoryTheory.Functor.isZero`), and a faithful additive functor reflects
`𝟙 M = 0`, i.e. `IsZero M`.

Mathlib carries no `IsZero`-from-sections converse for sheaves of modules on a scheme;
this is the reusable vanishing criterion the divisor side needs, and the honest target
for "a family cuts out the empty divisor" — a divisor is empty exactly when its structure
sheaf has no sections anywhere. -/
theorem isZero_of_forall_subsingleton_sections {M : Y.Modules}
    (h : ∀ V : Y.Opens, Subsingleton Γ(M, V)) : IsZero M := by
  have hp : IsZero ((Scheme.Modules.toPresheaf Y).obj M) :=
    CategoryTheory.Functor.isZero _ fun V => by
      have := h V.unop
      exact AddCommGrpCat.isZero_of_subsingleton (M.presheaf.obj V)
  rw [IsZero.iff_id_eq_zero]
  apply (Scheme.Modules.toPresheaf Y).map_injective
  rw [(Scheme.Modules.toPresheaf Y).map_id, (Scheme.Modules.toPresheaf Y).map_zero,
    ← IsZero.iff_id_eq_zero]
  exact hp

/-- **A sheaf of modules is zero iff its sections vanish over every open.** Packages
`subsingleton_sections_of_isZero` (forward) and `isZero_of_forall_subsingleton_sections`
(converse) into the section-level characterisation of the zero sheaf. -/
theorem isZero_iff_forall_subsingleton_sections {M : Y.Modules} :
    IsZero M ↔ ∀ V : Y.Opens, Subsingleton Γ(M, V) :=
  ⟨fun hM V => subsingleton_sections_of_isZero hM V,
    isZero_of_forall_subsingleton_sections⟩

/-- **Every sheaf of modules on an empty scheme is zero.**

On an empty scheme the structure sheaf has a subsingleton (trivial) ring of sections over
*every* open — every open embeds into the empty space — so each section module `Γ(M, V)`, a
module over that trivial ring, is a subsingleton (`Module.subsingleton`). The all-opens
section vanishing then feeds `isZero_of_forall_subsingleton_sections`.

This is the reusable "empty carrier ⟹ zero sheaf" direction, the converse companion of
`isEmpty_schematicSupport_of_isZero`, and the geometric core that turns *emptiness of the
support* into *vanishing of the sheaf* one lemma below (`isZero_of_isEmpty_schematicSupport`). -/
theorem isZero_of_isEmpty {M : Y.Modules} (hY : IsEmpty (Y : Type u)) : IsZero M :=
  isZero_of_forall_subsingleton_sections fun V => by
    haveI := hY
    exact Module.subsingleton Γ(Y, V) Γ(M, V)

/-- **A quasi-coherent sheaf with empty schematic support is zero** — the exact converse of
`isEmpty_schematicSupport_of_isZero`.

`M` is recovered from its restriction to the schematic support by the descent isomorphism
`M ≅ i_*(i^* M)` (`schematicSupportDescentIso`, `i = schematicSupportι M`, valid for a
quasi-coherent `M`). When that support is empty, `i^* M` is a sheaf of modules on an empty
scheme, hence zero (`isZero_of_isEmpty`); its pushforward is therefore zero, and the iso
transports that back to `M`.

This is the geometric half of the section-vanishing characterisation: it reduces "the
structure sheaf of a divisor vanishes" to the topological statement "the divisor is empty",
with no all-opens section computation. -/
theorem isZero_of_isEmpty_schematicSupport {M : Y.Modules} [M.IsQuasicoherent]
    (hM : IsEmpty (Scheme.Modules.schematicSupport M : Type u)) : IsZero M := by
  have hN : IsZero ((Scheme.Modules.pullback (Scheme.Modules.schematicSupportι M)).obj M) :=
    isZero_of_isEmpty hM
  exact IsZero.of_iso
    ((Scheme.Modules.pushforward (Scheme.Modules.schematicSupportι M)).map_isZero hN)
    (Scheme.Modules.schematicSupportDescentIso M)

/-- **A quasi-coherent sheaf is zero iff its schematic support is empty.** Packages the
landed forward `isEmpty_schematicSupport_of_isZero` with the converse
`isZero_of_isEmpty_schematicSupport` into the geometric characterisation of the zero sheaf:
vanishing of the sheaf is exactly emptiness of the closed subscheme it is supported on. The
companion of `isZero_iff_forall_subsingleton_sections`, in support vocabulary. -/
theorem isZero_iff_isEmpty_schematicSupport {M : Y.Modules} [M.IsQuasicoherent] :
    IsZero M ↔ IsEmpty (Scheme.Modules.schematicSupport M : Type u) :=
  ⟨fun hM => isEmpty_schematicSupport_of_isZero hM, isZero_of_isEmpty_schematicSupport⟩

end Scheme.Modules

/-! ## §3. The empty divisor -/

namespace Scheme

variable {S X : Scheme.{u}} (π : X ⟶ S) (T : Over S)

/-- **The structure sheaf is locally trivial of rank one.**

`Scheme.PicSharp.isLocallyTrivial_unit` is `private`, so it is restated here rather
than reused: on any affine open the identity is the required trivialisation. -/
theorem isLocallyTrivial_unit' {Y : Scheme.{u}} :
    LineBundle.IsLocallyTrivial (SheafOfModules.unit Y.ringCatSheaf) := by
  intro x
  obtain ⟨W, hW_aff, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := x) (U := ⊤)
      (show x ∈ (⊤ : Y.Opens) from trivial)
  exact ⟨W, hxW, hW_aff,
    ⟨(Scheme.Modules.restrictFunctorIsoPullback W.ι).app _ ≪≫ Modules.pullbackUnitIso W.ι⟩⟩

/-- **THE EMPTY DIVISOR**, and with it the first inhabitant of `Scheme.DivFamily` for
any `π : X ⟶ S` and any test object `T`.

`F = 0`, `q = 0`. The kernel ideal is then all of `O_{X_T}` — via
`Limits.kernelZeroIsoSource`, since the source of `q` is the pulled-back unit — which
is invertible, so the *divisor condition* holds for the geometric reason it should:
`O_{X_T}/O_{X_T} = 0` cuts out `D = ∅`, an effective relative divisor.

No hypothesis on `π`: not proper, not smooth, not even separated. Compare the general
case, where `properSupport` and `flat` are substantive conditions. -/
noncomputable def DivFamily.zero : DivFamily π T where
  F := 0
  isFinitePresentation := Modules.isFinitePresentation_of_isZero (isZero_zero _)
  flat := Modules.coherentSheafFlat_of_isZero _ (isZero_zero _)
  properSupport := Modules.hasProperSupport_of_isZero _ (isZero_zero _)
  q := 0
  epi := (isZero_zero _).epi _
  kerLocallyTrivial :=
    LineBundle.IsLocallyTrivial.of_iso
      (Limits.kernelZeroIsoSource (X := (Scheme.Modules.pullback
        (Limits.pullback.fst π T.hom)).obj (SheafOfModules.unit X.ringCatSheaf))
        (Y := (0 : (Limits.pullback π T.hom).Modules))).symm
      (LineBundle.IsLocallyTrivial.of_iso
        (Modules.pullbackUnitIso (Limits.pullback.fst π T.hom)).symm
        isLocallyTrivial_unit')

instance DivFamily.instNonempty : Nonempty (DivFamily π T) :=
  ⟨DivFamily.zero π T⟩

/-! ## §4. Base change, fibre degree, and the degree-zero slice

The empty divisor is not just a fibrewise accident: base change carries it to the
empty divisor of the new test object, so its classes assemble into a **global section**
of `DivFunctor`, and its fibre degree is `0` at every point of every base. -/

/-- **The pulled-back empty divisor is the empty divisor**, up to the divisor
equivalence — both `F`-sheaves are zero and any two morphisms into a zero object
agree.

This is what makes `zeroClass` below a genuine global section of `DivFunctor` rather
than an unrelated choice at each test object. -/
theorem DivFamily.pullbackAlong_zero {T' : Over S} (ψ : T' ⟶ T) :
    ((DivFamily.zero π T).pullbackAlong ψ).Rel (DivFamily.zero π T') :=
  ⟨(Functor.map_isZero (Scheme.Modules.pullback (quotBaseMap π ψ))
      (isZero_zero _)).iso (isZero_zero _),
    (isZero_zero _).eq_of_tgt _ _⟩

/-- **The fibre of the empty divisor is zero** — `fiberModule` is a module pullback,
which is additive. -/
theorem DivFamily.isZero_fiberModule_zero (t : (T.left : Scheme.{u})) :
    IsZero ((Limits.pullback.snd π T.hom).fiberModule t (DivFamily.zero π T).F) :=
  Functor.map_isZero _ (isZero_zero _)

/-- **The empty divisor has fibre degree `0`**, at every point of every base.

`deg ∅ = dim_{κ(t)} Γ(∅, O_∅) = 0`: the fibre is the zero module, its global sections
are a subsingleton, and `finrank` of a subsingleton is `0`. -/
theorem DivFamily.fiberDeg_zero (t : (T.left : Scheme.{u})) :
    (DivFamily.zero π T).fiberDeg t = 0 := by
  letI := (Limits.pullback.snd π T.hom).fiberSectionsModule t
    ((Limits.pullback.snd π T.hom).fiberModule t (DivFamily.zero π T).F)
  haveI : Subsingleton
      Γ((Limits.pullback.snd π T.hom).fiberModule t (DivFamily.zero π T).F, ⊤) :=
    Modules.subsingleton_sections_of_isZero (DivFamily.isZero_fiberModule_zero π T t) _
  exact Module.finrank_zero_of_subsingleton

/-- **The empty divisor has constant fibre degree `0`** — `HasFiberDeg zero 0`, the
predicate the degree-`d` subfunctor `DivFunctorDeg` is cut out by. -/
theorem DivFamily.hasFiberDeg_zero : (DivFamily.zero π T).HasFiberDeg 0 :=
  fun t => DivFamily.fiberDeg_zero π T t

/-- **The class of the empty divisor** in `Div_{X/S}(T)`: the first inhabitant of the
relative-divisor functor's value at any test object. -/
noncomputable def DivFunctor.zeroClass : (DivFunctor π).obj (Opposite.op T) :=
  Quotient.mk _ (DivFamily.zero π T)

instance DivFunctor.instNonemptyObj : Nonempty ((DivFunctor π).obj (Opposite.op T)) :=
  ⟨DivFunctor.zeroClass π T⟩

/-- **`DivFunctor` carries the zero class to the zero class**, i.e. `zeroClass` is a
*global section* of `Div_{X/S}` — a compatible family over all test objects, not a
choice per object. -/
theorem DivFunctor.map_zeroClass {T' : Over S} (ψ : T' ⟶ T) :
    (DivFunctor π).map ψ.op (DivFunctor.zeroClass π T) = DivFunctor.zeroClass π T' :=
  Quotient.sound (DivFamily.pullbackAlong_zero π T ψ)

/-- **The empty divisor's class has degree `0`**, in the class-level predicate the
degree slices use. -/
theorem DivFunctor.classHasFiberDeg_zeroClass :
    DivFamily.ClassHasFiberDeg (π := π) 0 (DivFunctor.zeroClass π T) :=
  DivFamily.hasFiberDeg_zero π T

/-- **The degree-`0` slice `Div⁰_{X/S}(T)` is inhabited**, for every `π` and every
test object.

This is the statement that turns the whole degree apparatus of `Picard/DivDegree.lean`
from vacuous into tested. Note what it is *not*: an identification of the slice with a
point. See the file docstring — singleton-ness at every test object is what
representability by the terminal object would need, and that is open. -/
noncomputable def DivFunctorDeg.zeroClass : (DivFunctorDeg π 0).obj (Opposite.op T) :=
  ⟨DivFunctor.zeroClass π T, DivFunctor.classHasFiberDeg_zeroClass π T⟩

instance DivFunctorDeg.instNonemptyObjZero :
    Nonempty ((DivFunctorDeg π 0).obj (Opposite.op T)) :=
  ⟨DivFunctorDeg.zeroClass π T⟩

/-! ## §5. Toward a Div⁰ producer: the terminal representation, modulo `Subsingleton`

The empty divisor makes `Div⁰_{X/S}` *inhabited* at every test object (§4). Being the
**only** degree-`0` relative effective divisor is a separate fact — the
`Subsingleton` half — and it is genuine content, not a formality (see the module
docstring: a fact about `fiberDeg`, a `finrank` with a junk value at infinite
dimension). This section does not prove it. What it does is package the two halves
against the categorical bridge `CategoryTheory.Functor.representableByTerminal`
(`Picard/RepresentableByTerminal.lean`), so that a lane which supplies the
`Subsingleton` gets the project's **first genuine `RepresentableBy` producer on the
divisor side** by a single application, with no `Equiv` plumbing.

The remaining obligation is exhibited as an explicit hypothesis rather than hidden:
`divFunctorDegZero_representableByTerminal` is a true implication whose antecedent
`hss` is the `Subsingleton` and whose conclusion is the terminal representation. The
antecedent is **not** circular — it does not mention `RepresentableBy` — and it is
reduced one step further by `subsingleton_divFunctorDegZero_obj_of_forall_rel_zero`
to the concrete statement "every degree-`0` divisor family cuts out the empty divisor".
-/

/-- **A divisor family with zero structure sheaf is the empty divisor.** If `x.F` is a
zero object then `x` is equivalent (`DivFamily.Rel`) to `DivFamily.zero`: the unique
isomorphism `x.F ≅ 0 = (zero).F` trivially commutes with the quotient maps, both
composites being morphisms into a zero object.

This is the *free* half of the degree-`0` uniqueness question. It reduces the open
obligation of §5 from a statement about `Rel` to the pure coherent-sheaf vanishing
`x.HasFiberDeg 0 → IsZero x.F` — no divisor or quotient vocabulary, just "a relative
effective divisor with everywhere-`0` fibre sections has zero structure sheaf". -/
theorem DivFamily.rel_zero_of_isZero {x : DivFamily π T} (hF : IsZero x.F) :
    x.Rel (DivFamily.zero π T) :=
  ⟨hF.iso (isZero_zero _), (isZero_zero _).eq_of_tgt _ _⟩

/-- **`Subsingleton` of the degree-`0` slice from divisor-level uniqueness.** If every
degree-`0` divisor family over `T` is equivalent (`DivFamily.Rel`, i.e. cuts out the
same closed subscheme) to the empty divisor, then the degree-`0` slice at `T` is a
subsingleton.

This peels the categorical `Subtype`/`Quotient` layer off the open obligation, leaving
the honest geometric statement: *a relative effective divisor of fibre degree `0` is
empty*. The converse direction (`zero` has degree `0`) is `hasFiberDeg_zero`. -/
theorem subsingleton_divFunctorDegZero_obj_of_forall_rel_zero
    (hrel : ∀ x : DivFamily π T, x.HasFiberDeg 0 → x.Rel (DivFamily.zero π T)) :
    Subsingleton ((DivFunctorDeg π 0).obj (Opposite.op T)) := by
  refine ⟨fun a b => Subtype.ext ?_⟩
  obtain ⟨za, ha⟩ := a
  obtain ⟨zb, hb⟩ := b
  induction za using Quotient.ind with
  | _ x =>
    induction zb using Quotient.ind with
    | _ y =>
      have hx : x.Rel (DivFamily.zero π T) := hrel x ha
      have hy : y.Rel (DivFamily.zero π T) := hrel y hb
      exact Quotient.sound (Setoid.trans hx (Setoid.symm hy))

/-- **The Div⁰ producer, modulo divisor-level uniqueness.** Given that every degree-`0`
relative effective divisor over every test object is the empty divisor, `Div⁰_{X/S}` is
represented by the terminal object `Over.mk (𝟙 S)` of `Over S`.

The `Nonempty` half is `DivFunctorDeg.instNonemptyObjZero` (the empty divisor); the
`Subsingleton` half is `subsingleton_divFunctorDegZero_obj_of_forall_rel_zero` applied
to the hypothesis; the terminal object is `CategoryTheory.Over.mkIdTerminal`; and the
bridge is `CategoryTheory.Functor.representableByTerminal`. No hypothesis on `π`
(not proper, not smooth); the antecedent `hrel` is the whole of what remains, and it
mentions no representability. -/
noncomputable def divFunctorDegZero_representableByTerminal
    (hrel : ∀ (T : Over S) (x : DivFamily π T), x.HasFiberDeg 0 →
      x.Rel (DivFamily.zero π T)) :
    (DivFunctorDeg π 0).RepresentableBy (Over.mk (𝟙 S)) :=
  CategoryTheory.Functor.representableByTerminal (DivFunctorDeg π 0)
    CategoryTheory.Over.mkIdTerminal
    (fun T => ⟨DivFunctorDeg.zeroClass π T.unop⟩)
    (fun T => subsingleton_divFunctorDegZero_obj_of_forall_rel_zero π T.unop (hrel T.unop))

/-- **The Div⁰ producer, modulo coherent-sheaf vanishing** — the sharpest form of
`divFunctorDegZero_representableByTerminal`, with the obligation reduced through
`DivFamily.rel_zero_of_isZero` to `x.HasFiberDeg 0 → IsZero x.F`.

This is the honest remaining gap stated in its purest form: *a relative effective
divisor whose fibre sections all have `κ(t)`-dimension `0` has zero structure sheaf.*
It carries no divisor-quotient, representability, or Picard vocabulary — it is a
statement about a finitely presented, base-flat, properly-supported coherent sheaf,
the coherent-sheaf Nakayama fact that AJC's `fiberDeg` (a `Module.finrank` of fibre
sections) makes the natural target. Discharging `hz` closes this producer and, with
it, `AJC.picrep.divzero`. -/
noncomputable def divFunctorDegZero_representableByTerminal_of_isZero
    (hz : ∀ (T : Over S) (x : DivFamily π T), x.HasFiberDeg 0 → IsZero x.F) :
    (DivFunctorDeg π 0).RepresentableBy (Over.mk (𝟙 S)) :=
  divFunctorDegZero_representableByTerminal π
    (fun T x hx => DivFamily.rel_zero_of_isZero π T (hz T x hx))

/-- **The Div⁰ producer, modulo section vanishing** — the purest section-level form of
`divFunctorDegZero_representableByTerminal_of_isZero`, with the coherent-sheaf-vanishing
antecedent `IsZero x.F` unfolded through `Scheme.Modules.isZero_of_forall_subsingleton_sections`
to *"a degree-`0` relative effective divisor has no structure-sheaf sections over any open
of `X_T`."*

This is the honest obligation in the vocabulary of sections alone — no `IsZero`, no
`finrank`, no representability. It exposes precisely the gap that `HasFiberDeg 0` (a
`finrank` of the *fibre* sections at each point) does **not** close on its own: the
finrank-`0` datum lives over each residue field, while zeroing `x.F` needs subsingleton
sections over *every* open, which is the fibrewise-finiteness geometry of the divisor
support (`Picard/DivSupportQuasiFinite.lean`), not a formality. Landing that geometric
step in the `hss`-shape below discharges this producer and, with it,
`AJC.picrep.divzero`. -/
noncomputable def divFunctorDegZero_representableByTerminal_of_forall_subsingleton_sections
    (hss : ∀ (T : Over S) (x : DivFamily π T), x.HasFiberDeg 0 →
      ∀ V : (Limits.pullback π T.hom).Opens, Subsingleton Γ(x.F, V)) :
    (DivFunctorDeg π 0).RepresentableBy (Over.mk (𝟙 S)) :=
  divFunctorDegZero_representableByTerminal_of_isZero π
    (fun T x hx => Scheme.Modules.isZero_of_forall_subsingleton_sections (hss T x hx))

/-- **The Div⁰ producer, in support vocabulary** — the same open obligation as
`divFunctorDegZero_representableByTerminal_of_isZero` and
`..._of_forall_subsingleton_sections`, restated with the coherent-sheaf-vanishing antecedent
`IsZero x.F` rephrased through `Scheme.Modules.isZero_of_isEmpty_schematicSupport` as
*"a degree-`0` relative effective divisor has empty schematic support."* The quasi-coherence
of `x.F` needed by that converse is free from its `isFinitePresentation` field, so the
antecedent carries only divisor data.

**This is a re-spelling, NOT a reduction.** Because `x.F` is quasi-coherent, the three
antecedents `IsZero x.F`, `∀ V, Subsingleton Γ(x.F, V)` (the sibling above), and
`IsEmpty (schematicSupport x.F)` are interderivable at every site — the converses
`isZero_iff_forall_subsingleton_sections` and `isZero_iff_isEmpty_schematicSupport` are both
in this file. This variant only offers a downstream lane the antecedent in the vocabulary
its own argument produces; it moves none of the difficulty. The genuine remaining distance is
documented at `Picard/DivSupportQuasiFinite.lean`'s `isFinite_support_of_fibers`: the
fibre-of-support vs support-of-fibre carrier bridge (the reverse annihilator inclusion, absent
in the tree) and the degree-`0`-fibre ⟹ empty-fibre step. `HasFiberDeg 0` is a `finrank` with a
junk value at infinite dimension, so it does not force vanishing by the naive route; a producer
of this antecedent must gate on fibre finiteness (the quasi-finite / relative-curve regime). -/
noncomputable def divFunctorDegZero_representableByTerminal_of_forall_isEmpty_schematicSupport
    (hemp : ∀ (T : Over S) (x : DivFamily π T), x.HasFiberDeg 0 →
      IsEmpty (Scheme.Modules.schematicSupport x.F : Type u)) :
    (DivFunctorDeg π 0).RepresentableBy (Over.mk (𝟙 S)) :=
  divFunctorDegZero_representableByTerminal_of_isZero π
    (fun T x hx =>
      letI := x.isFinitePresentation
      Scheme.Modules.isZero_of_isEmpty_schematicSupport (hemp T x hx))

end Scheme

end AlgebraicGeometry
