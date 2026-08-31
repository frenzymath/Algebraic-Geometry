/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.StableAffineCover
import AlgebraicJacobian.Albanese.GrpObjFoldSum

/-!
# The `G`-stable affine cover for a bare finite group action

`Sym^n C` is a quotient of `C^n` by `S_n`, and the route to it that
`Albanese/SymPowColimit.lean` §6 identifies — explicit `Scheme.GlueData` from affine charts —
needs one geometric input above all others: **every point has an affine open neighbourhood
stable under the whole group**. Without it the charts cannot be chosen compatibly and the
quotient exists only as an algebraic space (the Hironaka trap recorded in
`Picard/FiniteGaloisQuotient.lean`).

That input was believed missing for `S_n`. It is not: `Picard/StableAffineCover.lean` proves
it, sorry-free, and its proof **never uses the Galois structure it is stated over**.

## What was actually going on

`Picard/StableAffineCover.lean`'s `exists_stable_affineOpen_of_orbitsInAffineOpen` is stated
for a `SemilinearGalAction K L X f` — a group homomorphism `Gal(L/K) →* Aut X` *together with*
a field `compat`, the commuting square over `Spec γ` that makes the action semilinear. Reading
the proof, the only things it consumes are `ρ.act` and the two one-line consequences
`act_one_hom` / `act_mul_hom`, which are `map_one` and `map_mul` of the underlying
`MonoidHom`. `compat` — all of the semilinearity — is never mentioned, and
`[FiniteDimensional K L]` is spent only on getting a `Fintype` for `Finset.univ`.

So the theorem is about a **finite group acting on a scheme by automorphisms**; the Galois
data decorates the statement. This file states that version. It is a re-derivation, not a
generalisation of the original in place: `Picard/` belongs to another lane, so the proof is
copied here with the binder replaced (`G →* Aut X` plus `Fintype G`) rather than the original
being weakened. The two files should eventually be one, and the note below says which
direction that should go.

## Main results

* `StableGroupAction.OrbitsInAffineOpen` — the EGA II 4.5.4 hypothesis, for a bare action:
  every orbit lies in an affine open. Essential, not technical — see the Hironaka trap.
* `StableGroupAction.IsStableOpen` — a `G`-stable open.
* `exists_stable_affineOpen_of_orbits` — **the theorem**: under that hypothesis every point
  has a `G`-stable affine open neighbourhood. Prime avoidance puts the orbit in a basic open
  `D(s)` inside `⋂_g g⁻¹U`, and the norm `N = ∏_g g(s)` cuts out a stable affine basic open.
* `exists_stable_affineOpen_perm` — **the `S_n` instantiation**: for `C` a `k̄`-scheme, every
  point of `C^n` has an `S_n`-stable affine open neighbourhood, given the orbit hypothesis.

**Correction (2026-07-29): the `S_n` producer exists and this file's scope note said it did
not.** Two earlier revisions ran in opposite directions and both were wrong. One advertised a
`permAction : Equiv.Perm (Fin n) →* Aut (C^n)` that did not exist; the correction then
recorded building it as blocked, on the grounds that `MonObj.permAut` "is a bare morphism
never shown to be an isomorphism" and `SymPowColimit.permEnd` "lands in `End`, not `Aut`".
Both grounds were accurate statements about the tree and the inference from them was not:
`permAut C σ⁻¹` is a two-sided inverse of `permAut C σ`, because
`permAut C σ ≫ permAut C τ = permAut C (σ * τ)`. That is `MonObj.permAut_comp`, and the
action is `MonObj.permAutHom`, both now in `Albanese/GrpObjFoldSum.lean` — four lines, no
construction. The lesson is the `permEnd` convention: the inverse `permEnd` carries is forced
by `End`'s reversed multiplication, and reading it as a fact about `permAut` is what made an
isomorphism look absent.

## Why the proof needs no averaging, and so no characteristic hypothesis

The norm `∏_g g(s)` is a *product*, not an average: it needs no `1/|G|` and works in every
characteristic. That matters here for the same reason it matters in
`Albanese/SymPowTensorAction.lean` — `g!` may vanish in `k̄` when `char k̄ ≤ g`, so any route
through averaging would exclude exactly the cases the challenge is stated over.

## Scope — what this does and does not give

**Does**: prove the stable-cover statement at the generality a glue-data construction wants —
a *finite group acting on a scheme by automorphisms*, with no Galois hypothesis and no
characteristic hypothesis.

**Does** now also apply it to `S_n` acting on `C^n`: `exists_stable_affineOpen_perm` for the
product in `Scheme`, and `exists_stable_affineOpen_perm_over` for the underlying scheme of the
`Over (Spec k̄)`-product — **which is the one the leg uses**, and is a different object (see
that theorem's docstring; `Over.forget` does not preserve binary products).

**Does not**: build the glue data. `HasColimit (permDiagram C g)` remains open and
`AlbaneseUP.lean`'s six sorries are unchanged.

**The count, in one place, because three places in this tree disagreed about it.** A glue-data
assembly needs *four* things:

1. ✓ a `G`-stable affine cover — below, with both `S_n` instantiations.
2. ✓ the `Aut`-valued `S_n`-action — `MonObj.permAutHom` (`Albanese/GrpObjFoldSum.lean`).
3. ✓ **(completed run 0069 r7; this entry read "Partly" until then.)** The `n`-ary coproduct of
   commutative algebras = `n`-fold tensor power, with the permutation action matched to
   `PiTensorProduct.permAlgHom`. The algebra level is `Albanese/TensorPowerCoproduct.lean`
   (`existsUnique_coprodLift`, `coprodLift_permAlgHom`, `permAlgHom_comp_singleAlgHom`); the
   `Cofan`/`IsColimit` packaging in `Under k` that was the missing half is
   `Albanese/TensorPowerCofan.lean` (`tensorPowerCofanIsColimit`, with
   `tensorPowerFanIsLimit` for the `(Under k)ᵒᵖ` variance and
   `tensorPowerCofan_inj_permAlgHom` for the equivariance on coprojections).
4. **Open, and the honest wall.** The cocycle/overlap agreement of the chart quotients, plus
   `OrbitsInAffineOpen` **for the curve** — where quasi-projectivity would enter, and mathlib
   has no quasi-projectivity vocabulary at this pin.

So: **3 supplied, 1 open.** A fresh-context review of run 0069 r6 found the roadmap saying
"3 of 4", the team thread saying "2 of 4", and this header asserting both at once — which is why
the count lives here and nowhere else. It is now 3 for a different reason than that stale row
gave, so do not read the two as having agreed.

**Consumption, which is the part to read sceptically.** Item 3's packaging *is* consumed, by
`Albanese/SymPowAffineCarrier.lean` and then `Albanese/SymPowAffineQuotient.lean`, which
together prove that the colimit `SymPowColimit.symPowData_affineAlgebra` takes is
`op ((A^{⊗ n})^{S_n})` (`colimitPermDiagramIsoFixed`) — the first time anything in this cone
consumed a layer this lane built. But the honest scope of that chain is *within* the affine
story: `symPowData_affineAlgebra` itself was **not rewritten** to consume the named carrier, and
nothing in `AlbaneseUP.lean` / `AlbaneseFromData.lean` / `AlbaneseFromColimit.lean` mentions any
of it, because those are about the curve and item 4 is what stands between. Five rounds of this
lane shipped layers with no consumer; this is one consumer inside the same subject, not
integration with the capstone.

## References

Milne, *Abelian Varieties*, §III.3 Proposition 3.1, p. 94. EGA II 4.5.4 for the
orbit-in-affine hypothesis. The original proof is
`AlgebraicJacobian.GaloisDescent.SemilinearGalAction.exists_stable_affineOpen_of_orbitsInAffineOpen`
(`Picard/StableAffineCover.lean:193`), whose supporting lemmas
(`exists_basicOpen_le_of_finite`, `mem_finset_inf`, `preimage_finset_inf`,
`basicOpen_finset_prod`) are imported and reused unchanged.
-/

set_option autoImplicit false

universe w u

open CategoryTheory AlgebraicJacobian.GaloisDescent

namespace AlgebraicGeometry

namespace StableGroupAction

-- The group's universe `w` is **independent** of the scheme's universe `u`. The proof only
-- ever indexes a `Finset.univ` by `G`, and the underlying prime-avoidance lemma
-- `exists_basicOpen_le_of_finite` is already polymorphic in its index type (`{ι : Type*}`), so
-- nothing forces `G : Type u`. Keeping them tied — as the first draft did, copying the Galois
-- statement where `G = Gal(L/K)` happens to live in `Type u` — makes the theorem inapplicable
-- to `Equiv.Perm (Fin n) : Type 0`, which is precisely the group the symmetric power needs.
variable {G : Type w} [Group G] [Finite G] {X : Scheme.{u}} (act : G →* Aut X)

/-- **Orbit-in-affine hypothesis for a bare action** (EGA II 4.5.4): every orbit is contained
in an affine open. This hypothesis is *essential*, not a convenience — without it the
quotient need only be an algebraic space (Hironaka; see `Picard/FiniteGaloisQuotient.lean`'s
module docstring). It holds for quasi-projective `X`, but mathlib has no quasi-projectivity
at this pin, so for the curve it must be supplied by hand. -/
def OrbitsInAffineOpen : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, ∀ g : G, (act g).hom.base x ∈ U.1

/-- A `G`-stable open of `X`. -/
def IsStableOpen (U : X.Opens) : Prop :=
  ∀ g : G, (act g).hom ⁻¹ᵁ U = U

omit [Finite G] in
/-- The identity acts as the identity. This and `act_mul_hom` are the *only* structural facts
the main theorem uses about the action — both are `map_one`/`map_mul` of the `MonoidHom`,
which is why no semilinearity is needed. -/
lemma act_one_hom : (act 1).hom = 𝟙 X := by rw [map_one]; rfl

omit [Finite G] in
/-- Multiplicativity, in the composition order `Aut` gives. -/
lemma act_mul_hom (g t : G) : (act (g * t)).hom = (act t).hom ≫ (act g).hom := by
  rw [map_mul]; rfl

/-- **The `G`-stable affine neighbourhood theorem, for a bare finite group action.**

Under the orbit-in-affine hypothesis, every point has a `G`-stable affine open neighbourhood.

The argument, in three moves: prime avoidance (`exists_basicOpen_le_of_finite`) puts the whole
orbit of `x` inside a basic open `D(s)` contained in `W = ⋂_g (act g)⁻¹U`; the **norm**
`N = ∏_g g(s)|_W` then satisfies `D(N) = ⋂_g (act g)⁻¹ D(s)`, which is `G`-stable by
reindexing the intersection; and `D(N) ⊆ D(s) ⊆ U` is affine as a basic open of an affine.
Stability is proved at the level of *opens*, which is what avoids transporting sections along
the action isomorphisms.

The norm is a product, so no `1/|G|` appears and the statement is characteristic-free.

**Provenance.** This is `Picard/StableAffineCover.lean:193` with its `SemilinearGalAction`
binder replaced by `G →* Aut X` and `[Fintype G]`; the proof term is otherwise unchanged, which
is the evidence that the semilinearity field was never load-bearing. See the module header. -/
theorem exists_stable_affineOpen_of_orbits (h : OrbitsInAffineOpen act) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ IsStableOpen act U := by
  classical
  -- `[Finite G]` is the honest binder; the `Fintype` is an artefact of `Finset.univ`.
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨U, hxU⟩ := h x
  -- the whole orbit meets every translated chart: `g(t(x)) = (g*t)(x) ∈ U`.
  have horb : ∀ t g : G, (act g).hom.base ((act t).hom.base x) ∈ U.1 := by
    intro t g
    have hh : (act g).hom.base ((act t).hom.base x) = (act (g * t)).hom.base x := by
      rw [act_mul_hom act g t]; rfl
    rw [hh]; exact hxU (g * t)
  -- prime avoidance: `orbit ⊆ D(s) ⊆ W := ⋂_g (act g)⁻¹ U`.
  obtain ⟨s, hs_mem, hs_le⟩ := exists_basicOpen_le_of_finite U.2
    (fun g : G => (act g).hom.base x) hxU
    (V := Finset.univ.inf fun g : G => (act g).hom ⁻¹ᵁ U.1)
    (fun t => mem_finset_inf.mpr fun g _ => horb t g)
  have hWle : ∀ g : G,
      (Finset.univ.inf fun d : G => (act d).hom ⁻¹ᵁ U.1) ≤ (act g).hom ⁻¹ᵁ U.1 :=
    fun g => Finset.inf_le (Finset.mem_univ g)
  -- the norm `N = ∏_g g(s)|_W` and its factors
  set t : G → Γ(X, Finset.univ.inf fun d : G => (act d).hom ⁻¹ᵁ U.1) :=
    fun g => X.presheaf.map (homOfLE (hWle g)).op ((act g).hom.app U.1 s) with ht
  set N : Γ(X, Finset.univ.inf fun d : G => (act d).hom ⁻¹ᵁ U.1) := ∏ g : G, t g with hN
  -- each factor cuts out the corresponding translate of `D(s)` inside `W`
  have hbo_t : ∀ g : G, X.basicOpen (t g) =
      (Finset.univ.inf fun d : G => (act d).hom ⁻¹ᵁ U.1) ⊓ (act g).hom ⁻¹ᵁ X.basicOpen s := by
    intro g
    rw [ht, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
  -- the `g = 1` translate is `D(s)` itself
  have hP1 : (act (1 : G)).hom ⁻¹ᵁ X.basicOpen s = X.basicOpen s := by
    rw [act_one_hom act]; rfl
  -- `D(N) = ⋂_g (act g)⁻¹ D(s)`
  have hbo_N : X.basicOpen N = Finset.univ.inf fun g : G => (act g).hom ⁻¹ᵁ X.basicOpen s := by
    rw [hN, basicOpen_finset_prod ⟨1, Finset.mem_univ 1⟩,
      Finset.inf_congr rfl fun g _ => hbo_t g]
    refine le_antisymm
      (Finset.le_inf fun g _ => (Finset.inf_le (Finset.mem_univ g)).trans inf_le_right)
      (Finset.le_inf fun g _ => le_inf (le_trans ?_ hs_le)
        (Finset.inf_le (Finset.mem_univ g)))
    exact le_of_le_of_eq (Finset.inf_le (Finset.mem_univ 1)) hP1
  -- `D(N) ⊆ D(s)` (the `g = 1` factor)
  have hNs : X.basicOpen N ≤ X.basicOpen s := by
    rw [hbo_N]
    exact le_of_le_of_eq (Finset.inf_le (Finset.mem_univ 1)) hP1
  refine ⟨X.basicOpen N, ?_, ?_, ?_⟩
  · -- affineness: `D(N)` is a basic open of the affine `D(s)`
    have heq : X.basicOpen (X.presheaf.map (homOfLE hs_le).op N) = X.basicOpen N := by
      rw [Scheme.basicOpen_res]
      exact inf_eq_right.mpr hNs
    rw [← heq]
    exact (U.2.basicOpen s).basicOpen _
  · -- membership: prime avoidance put the whole orbit in `D(s)`
    rw [hbo_N, mem_finset_inf]
    intro g _
    change (act g).hom.base x ∈ X.basicOpen s
    exact hs_mem g
  · -- stability, at the level of opens: preimage functoriality plus reindexing
    intro tau
    rw [hbo_N, preimage_finset_inf]
    have hPt : ∀ g : G, (act tau).hom ⁻¹ᵁ ((act g).hom ⁻¹ᵁ X.basicOpen s)
        = (act (g * tau)).hom ⁻¹ᵁ X.basicOpen s := by
      intro g
      rw [act_mul_hom act]; rfl
    rw [Finset.inf_congr rfl fun g _ => hPt g]
    refine le_antisymm (Finset.le_inf fun d _ => ?_) (Finset.le_inf fun d _ => ?_)
    · have hh := Finset.inf_le (s := Finset.univ)
        (f := fun g : G => (act (g * tau)).hom ⁻¹ᵁ X.basicOpen s)
        (Finset.mem_univ (d * tau⁻¹))
      rwa [inv_mul_cancel_right] at hh
    · exact Finset.inf_le (Finset.mem_univ (d * tau))

end StableGroupAction

/-! ## The `S_n` instantiation

The theorem above is stated for a bare `G →* Aut X`. The producer for `G = S_n`,
`X = C^n` is `MonObj.permAutHom` (`Albanese/GrpObjFoldSum.lean`), so the instantiation is
a one-line application. `Scheme` is cartesian monoidal with finite products
(`AlgebraicGeometry.Limits`), which is what lets `∏ᶜ (fun _ : Fin n => C)` and `permAut` be
formed here at all.

This is item 2 of the four-item glue-data bill in the module header.

**Two instantiations, and the ambient category is the whole difference.**
`exists_stable_affineOpen_perm` is about the product in `Scheme`;
`exists_stable_affineOpen_perm_over` is about `(∏ᶜ fun _ => C).left` for
`C : Over (Spec k̄)`, which is what the Albanese leg actually forms. `Over.forget` does not
preserve binary products, so the first does **not** give the second — see
`exists_stable_affineOpen_perm`'s docstring.

An earlier version of this paragraph added that the action "being available is what makes
item 1 consumable rather than free-standing". That is retracted: nothing outside this file
consumes either theorem, and availability of the action was never what stood between them and
a consumer. -/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

/-- **Every point of `C^n` has an `S_n`-stable affine open neighbourhood** — for `C` a
plain scheme and `C^n` the product *in `Scheme`*.

The `S_n`-equivariant form of `exists_stable_affineOpen_of_orbits`, obtained by feeding it
the action `MonObj.permAutHom C n`. The orbit hypothesis is unchanged and still has to be
supplied for the curve — item 4 of the glue-data bill, where quasi-projectivity would
enter — but the *equivariance* half is discharged.

**Read the ambient category, and do not assume it is the leg's.** `∏ᶜ` here is formed in
`Scheme`, whereas the Albanese connector forms it in `Over (Spec k̄)`: `SymPowData.proj` is
instantiated at `K = Over (Spec k̄)` by `AlbaneseUP`, `AlbaneseFromData` and
`SymPowColimit`. Those two objects are **not** the same — `Over.forget` does not preserve
binary products (`PreservesLimitsOfShape (Discrete (Fin 2)) (Over.forget _)` does not
synthesize; one product is the fibre product over `Spec k̄`, the other over the terminal
scheme). So this theorem does *not* by itself apply to the leg's `C^n`; use
`exists_stable_affineOpen_perm_over` below, which acts on the object the leg uses.

An earlier version of this docstring said the availability of the action "is what makes
item 1 consumable". That was false for exactly this reason, and it is the second time on
this leg that a correct fix at one layer (there: a universe binder) was reported as if it
had fixed the layer above. -/
theorem exists_stable_affineOpen_perm (C : Scheme.{u}) (n : ℕ)
    (h : StableGroupAction.OrbitsInAffineOpen (MonObj.permAutHom C n))
    (x : (∏ᶜ (fun _ : Fin n => C) : Scheme.{u})) :
    ∃ U : (∏ᶜ (fun _ : Fin n => C) : Scheme.{u}).Opens,
      IsAffineOpen U ∧ x ∈ U ∧ StableGroupAction.IsStableOpen (MonObj.permAutHom C n) U :=
  StableGroupAction.exists_stable_affineOpen_of_orbits (MonObj.permAutHom C n) h x

/-- **The `S_n`-action on the underlying scheme of the `Over (Spec k̄)`-product.**

This is the action on the object the Albanese leg actually uses. `MonObj.permAutHom C n` for
`C : Over (Spec k̄)` is valued in `Aut` of the *over-category* product; pushing it along
`Over.forget` with `Functor.mapAut` gives an action on `(∏ᶜ fun _ => C).left`, a genuine
`Scheme`, which is what the stable-cover theorem consumes.

Note this is a transport of the action, not a comparison of the two products: it makes no
claim that `(∏ᶜ fun _ => C).left` agrees with the `Scheme`-product of `C.left`, which is
false in general. -/
noncomputable def permAutHomOverLeft {kbar : Type u} [Field kbar]
    (C : Over (Spec (CommRingCat.of kbar))) (n : ℕ) :
    Equiv.Perm (Fin n) →* Aut ((∏ᶜ (fun _ : Fin n => C)).left) :=
  (Functor.mapAut _ (Over.forget (Spec (CommRingCat.of kbar)))).comp (MonObj.permAutHom C n)

/-- **The stable-cover theorem at the object the Albanese leg uses.**

Same statement as `exists_stable_affineOpen_perm`, but for `(∏ᶜ fun _ : Fin n => C).left`
with `C : Over (Spec k̄)` — the underlying scheme of the *over-category* product, which is
what `SymPowData C n` is about. This is the form a `Scheme.GlueData` for `Sym^n C` would
consume.

The orbit hypothesis remains the open geometric input (item 4). -/
theorem exists_stable_affineOpen_perm_over {kbar : Type u} [Field kbar]
    (C : Over (Spec (CommRingCat.of kbar))) (n : ℕ)
    (h : StableGroupAction.OrbitsInAffineOpen (permAutHomOverLeft C n))
    (x : ((∏ᶜ (fun _ : Fin n => C)).left)) :
    ∃ U : ((∏ᶜ (fun _ : Fin n => C)).left).Opens,
      IsAffineOpen U ∧ x ∈ U ∧ StableGroupAction.IsStableOpen (permAutHomOverLeft C n) U :=
  StableGroupAction.exists_stable_affineOpen_of_orbits (permAutHomOverLeft C n) h x

end AlgebraicGeometry
