/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.SetNotationForOrder
import Std.Tactic.BVDecide.LRAT.Internal.Clause

/-!
# Zariski descent of representability (`thm:representability_zariski_descent`)

This file proves **Zariski descent of representability** (EGA 0_I 4.5.4;
cf. Stacks 01JJ): a presheaf `F : (Sch/S)ᵒᵖ ⥤ Type 1` satisfying the Zariski
sheaf axiom (`Scheme.IsZariskiSheafOver`, stated against open covers of the
total space of each `T : Over S`) that is representable over every member of
an open cover of `S` is representable by an `S`-scheme
(`Scheme.representable_of_openCover`).

The definitions `overRes` / `overResHom` / `overResLE` / `IsZariskiSheafOver`
and the statement of the descent theorem previously lived in
`GrassmannianRepresentability.lean` (where the theorem was a typed `sorry`
leaf); they are moved here so the Grassmannian file can consume the proof.

## Proof architecture

The heavy gluing content (cocycle conditions, `Scheme.GlueData`, the
locally-bijective sheaf comparison) is **not** redone by hand: it is delegated
to mathlib's `AlgebraicGeometry.Scheme.LocalRepresentability.representableBy`
(Stacks 01JJ), which applies to a `Type 0`-valued Zariski *sheaf* on the
absolute category `Scheme.{0}` equipped with a jointly surjective family of
relatively representable open immersions from representables.  The work done
here is the translation layer:

1. **Size reduction / total functor** (`ZariskiDescent.GluedPoint`,
   `ZariskiDescent.gluedFunctor`): the values of `F` live in `Type 1`, so `F`
   cannot be fed to the mathlib theorem directly.  Instead we encode a point
   of the would-be total space over `T : Scheme` as a `Type 0` datum: a base
   morphism `a : T ⟶ S` together with a family of *classifying morphisms*
   `γ i : T|_{a⁻¹ U i} ⟶ Y i` into the local representing objects, compatible
   on overlaps as classified `F`-sections.  The bespoke sheaf axiom for `F`
   shows `GluedPoint T ≃ Σ (a : T ⟶ S), F(T, a)` (`ZariskiDescent.totalEquiv`),
   identifying `gluedFunctor` with the (large) total functor of `F`.
2. **Sheaf axiom** (`ZariskiDescent.isSheaf`): `gluedFunctor` is a sheaf for
   the big Zariski topology.  Covers by arbitrary jointly surjective open
   immersions are reduced to covers by opens of the target (the generated
   sieves agree), where the claim follows from the sheaf axiom of `F` through
   `totalEquiv`.
3. **Charts** (`ZariskiDescent.chart`): each `Y i` maps to `gluedFunctor` by
   sending `t : T ⟶ (Y i).left` to the point classified by the `F`-section
   that `t` represents; these are relatively representable open immersions
   (the pullback against a point `(a, x)` of `gluedFunctor` is the open
   subscheme `a⁻¹ U i ⊆ T`) and jointly surjective.
4. **Conclusion**: mathlib glues a scheme `Ŷ` with `gluedFunctor ≅ Hom(-, Ŷ)`;
   the tautological point of `Ŷ` gives the structure morphism `â : Ŷ ⟶ S`,
   and `totalEquiv` converts the absolute representability into
   `F.RepresentableBy (Over.mk â)`.

## References

Blueprint: `thm:representability_zariski_descent`, `def:zariski_sheaf_over`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
Source: EGA 0_I 4.5.4; Stacks 01JJ; [Nitsure] §1 (FGA Explained Ch. 5).
-/

set_option autoImplicit false

universe w v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

/-! ## §1. Zariski-local presheaves on `Sch/S` (moved from
`GrassmannianRepresentability.lean`) -/

/-- The restriction of `T : Over S` to an open `W ⊆ T.left`, as an object of
`Over S`. -/
noncomputable def overRes {S : Scheme.{0}} (T : Over S) (W : T.left.Opens) :
    Over S :=
  Over.mk (W.ι ≫ T.hom)

/-- The restriction morphism `T|_W ⟶ T` in `Over S`. -/
noncomputable def overResHom {S : Scheme.{0}} (T : Over S) (W : T.left.Opens) :
    overRes T W ⟶ T :=
  Over.homMk W.ι rfl

/-- The inclusion `T|_{W'} ⟶ T|_W` in `Over S` attached to `W' ≤ W`. -/
noncomputable def overResLE {S : Scheme.{0}} (T : Over S)
    {W' W : T.left.Opens} (h : W' ≤ W) : overRes T W' ⟶ overRes T W :=
  Over.homMk (T.left.homOfLE h)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ T.hom) (T.left.homOfLE_ι h)))

/-- **The Zariski sheaf axiom for a presheaf on `Sch/S`**: for every
`T : Over S` and every open cover `{W k}` of the total space `T.left`, a
family of sections of `F` over the restrictions `T|_{W k}` that agree on the
pairwise intersections glues to a unique section over `T`.  This is the sheaf
condition for the (big) Zariski site of `S`, stated concretely against open
covers of the total space; representable presheaves satisfy it, and it is the
hypothesis under which local representability descends
(`Scheme.representable_of_openCover`). -/
def IsZariskiSheafOver {S : Scheme.{0}} (F : (Over S)ᵒᵖ ⥤ Type 1) : Prop :=
  ∀ (T : Over S) {κ : Type} (W : κ → T.left.Opens), (⨆ k, W k = ⊤) →
    ∀ x : ∀ k, F.obj (Opposite.op (overRes T (W k))),
    (∀ k l : κ, F.map (overResLE T (inf_le_left : W k ⊓ W l ≤ W k)).op (x k)
      = F.map (overResLE T (inf_le_right : W k ⊓ W l ≤ W l)).op (x l)) →
    ∃! x₀ : F.obj (Opposite.op T), ∀ k, F.map (overResHom T (W k)).op x₀ = x k

/-! ## §2. Generic helpers -/

/-- A commutative square of `Type`-valued presheaves that is a pointwise
pullback is a pullback square (evaluation functors jointly reflect limits). -/
lemma isPullback_of_app {C : Type u} [Category.{v} C]
    {P X Y Z : Cᵒᵖ ⥤ Type w} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : ∀ c : Cᵒᵖ, IsPullback (fst.app c) (snd.app c) (f.app c) (g.app c)) :
    IsPullback fst snd f g := by
  have w : fst ≫ f = snd ≫ g := by
    apply NatTrans.ext; funext c
    rw [NatTrans.comp_app, NatTrans.comp_app]
    exact (h c).w
  exact
    { w := w
      isLimit' := ⟨evaluationJointlyReflectsLimits _ fun c => by
        refine IsLimit.equivOfNatIsoOfIso
          (cospanCompIso ((CategoryTheory.evaluation Cᵒᵖ (Type w)).obj c) f g).symm
          _ _ ?_ ((h c).isLimit)
        refine Cone.ext (Iso.refl _) ?_
        rintro (_ | (_ | _)) <;> cat_disch⟩ }

/-- The open cover of a scheme attached to a family of opens with `⨆ = ⊤`. -/
@[simps I₀ X f]
noncomputable def opensCover (T : Scheme.{0}) {κ : Type} (W : κ → T.Opens)
    (hW : ⨆ k, W k = ⊤) : T.OpenCover where
  I₀ := κ
  X k := (W k).toScheme
  f k := (W k).ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    have : x ∈ ⨆ k, W k := by rw [hW]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp this
    exact ⟨k, ⟨x, hk⟩, rfl⟩

namespace ZariskiDescent

variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type 1}
  {ι : Type} {U : ι → S.Opens}

/-! ## §3. Glued points: the small total functor

A *glued point* of the would-be total space over `T : Scheme` is a base
morphism `a : T ⟶ S` together with classifying morphisms
`γ i : T|_{a⁻¹ U i} ⟶ Y i` over each `U i`, whose classified `F`-sections
agree on the pairwise overlaps.  Through the sheaf axiom of `F` this is
equivalent to a morphism `a` plus a section of `F` over `(T, a)`
(`totalEquiv` below), but in contrast to the latter it is a `Type 0` datum. -/

variable (U) in
/-- The preimage of `U i` in the parameter scheme. -/
abbrev pre {T : Scheme.{0}} (a : T ⟶ S) (i : ι) : T.Opens := a ⁻¹ᵁ U i

variable (U) in
/-- The restriction `T|_{a⁻¹ U i} ⟶ U i` of `a`. -/
noncomputable abbrev preRes {T : Scheme.{0}} (a : T ⟶ S) (i : ι) :
    (pre U a i).toScheme ⟶ (U i).toScheme :=
  a.resLE (U i) (pre U a i) le_rfl

variable (U) in
/-- The comparison in `Over S` between the open restriction
`overRes (Over.mk a) (a⁻¹ U i)` and the image under `Over.map (U i).ι` of the
`Over (U i)`-object `Over.mk (a.resLE …)`: the identity on total spaces. -/
noncomputable def classifyHom {T : Scheme.{0}} (a : T ⟶ S) (i : ι) :
    overRes (Over.mk a) (pre U a i) ⟶
      (Over.map (U i).ι).obj (Over.mk (preRes U a i)) :=
  Over.homMk (𝟙 (pre U a i).toScheme)
    (by simp only [overRes, Over.mk_hom, Over.map_obj_hom]
        exact Scheme.Hom.resLE_comp_ι _ _)

/-- The `F`-section over `T|_{a⁻¹ U i}` classified by a morphism
`γ : T|_{a⁻¹ U i} ⟶ Y i` over `U i`. -/
noncomputable def classify {Y : ∀ i, Over (U i).toScheme}
    (R : ∀ i, ((Over.map (U i).ι).op ⋙ F).RepresentableBy (Y i))
    {T : Scheme.{0}} {a : T ⟶ S} {i : ι}
    (g : Over.mk (preRes U a i) ⟶ Y i) :
    F.obj (op (overRes (Over.mk a) (pre U a i))) :=
  F.map (classifyHom U a i).op ((R i).homEquiv g)

variable (F) in
/-- A point of the glued total space over `T`: a base morphism `a : T ⟶ S`
together with classifying morphisms into the local representing objects,
compatible on overlaps as classified `F`-sections. -/
structure GluedPoint (Y : ∀ i, Over (U i).toScheme)
    (R : ∀ i, ((Over.map (U i).ι).op ⋙ F).RepresentableBy (Y i))
    (T : Scheme.{0}) : Type where
  /-- The base morphism. -/
  a : T ⟶ S
  /-- The classifying morphism over `U i`. -/
  γ : ∀ i, Over.mk (preRes U a i) ⟶ Y i
  compat : ∀ i j : ι,
    F.map (overResLE (Over.mk a)
      (inf_le_left : pre U a i ⊓ pre U a j ≤ pre U a i)).op (classify R (γ i))
    = F.map (overResLE (Over.mk a)
      (inf_le_right : pre U a i ⊓ pre U a j ≤ pre U a j)).op (classify R (γ j))

variable {Y : ∀ i, Over (U i).toScheme}
  {R : ∀ i, ((Over.map (U i).ι).op ⋙ F).RepresentableBy (Y i)}

/-- An `eqToHom` between restrictions to equal opens commutes with the
inclusions. -/
lemma eqToHom_comp_ι {T : Scheme.{0}} {V V' : T.Opens} (hV : V = V')
    (h : V.toScheme = V'.toScheme) : eqToHom h ≫ V'.ι = V.ι := by
  subst hV
  simp

/-- Reassociated form of `eqToHom_comp_ι`. -/
lemma eqToHom_comp_ι_assoc {T : Scheme.{0}} {V V' : T.Opens} (hV : V = V')
    (h : V.toScheme = V'.toScheme) {Z : Scheme.{0}} (g : T ⟶ Z) :
    eqToHom h ≫ V'.ι ≫ g = V.ι ≫ g := by
  subst hV
  simp

/-- Morphisms into a classifying source `Over.mk (a.resLE …)` are determined
by their composition with the ambient open inclusion. -/
lemma hom_ext_of_ι {T : Scheme.{0}} {a : T ⟶ S} {i : ι}
    {A : Over (U i).toScheme} {g₁ g₂ : A ⟶ Over.mk (preRes U a i)}
    (h : g₁.left ≫ (pre U a i).ι = g₂.left ≫ (pre U a i).ι) : g₁ = g₂ := by
  apply CommaMorphism.ext
  · exact (cancel_mono (pre U a i).ι).mp h
  · apply Subsingleton.elim

variable (U) in
/-- Restriction of the classifying source along `b : V ⟶ T`, as a morphism in
`Over (U i)`. -/
noncomputable def restrictHom {V T : Scheme.{0}} (b : V ⟶ T) (a : T ⟶ S) (i : ι) :
    Over.mk (preRes U (b ≫ a) i) ⟶ Over.mk (preRes U a i) :=
  Over.homMk (b.resLE (pre U a i) (pre U (b ≫ a) i) le_rfl)
    (by simp only [Over.mk_hom]
        exact Scheme.Hom.resLE_comp_resLE _ _ _ _)

variable (U) in
/-- Restriction of the ambient `Over S`-objects along `b : V ⟶ T`. -/
noncomputable def overResRestrict {V T : Scheme.{0}} (b : V ⟶ T) (a : T ⟶ S) (i : ι) :
    overRes (Over.mk (b ≫ a)) (pre U (b ≫ a) i) ⟶ overRes (Over.mk a) (pre U a i) :=
  Over.homMk (b.resLE (pre U a i) (pre U (b ≫ a) i) le_rfl)
    (by simp only [overRes, Over.mk_hom]
        exact Scheme.Hom.resLE_comp_ι_assoc _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Coherence of the classified sections under restriction: restricting the
classifying morphism restricts the classified section. -/
lemma classify_restrictHom {V T : Scheme.{0}} (b : V ⟶ T) {a : T ⟶ S} {i : ι}
    (g : Over.mk (preRes U a i) ⟶ Y i) :
    classify R (restrictHom U b a i ≫ g)
      = F.map (overResRestrict U b a i).op (classify R g) := by
  unfold classify
  rw [(R i).homEquiv_comp]
  change F.map _ (F.map _ _) = F.map _ (F.map _ _)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  congr 2

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- Functoriality of glued points: restriction along `b : V ⟶ T`. -/
noncomputable def GluedPoint.res {V T : Scheme.{0}} (b : V ⟶ T)
    (p : GluedPoint F Y R T) : GluedPoint F Y R V where
  a := b ≫ p.a
  γ i := restrictHom U b p.a i ≫ p.γ i
  compat i j := by
    rw [classify_restrictHom, classify_restrictHom,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp, ← op_comp]
    have hsq : ∀ (k : ι) (hk : pre U (b ≫ p.a) i ⊓ pre U (b ≫ p.a) j ≤ pre U (b ≫ p.a) k)
        (hk' : pre U p.a i ⊓ pre U p.a j ≤ pre U p.a k),
        overResLE (Over.mk (b ≫ p.a)) hk ≫ overResRestrict U b p.a k
          = (Over.homMk (b.resLE (pre U p.a i ⊓ pre U p.a j)
                (pre U (b ≫ p.a) i ⊓ pre U (b ≫ p.a) j) le_rfl)
              (by simp [overRes]) :
              overRes (Over.mk (b ≫ p.a)) (pre U (b ≫ p.a) i ⊓ pre U (b ≫ p.a) j) ⟶
                overRes (Over.mk p.a) (pre U p.a i ⊓ pre U p.a j))
            ≫ overResLE (Over.mk p.a) hk' := by
      intro k hk hk'
      apply CommaMorphism.ext
      · simp only [overResLE, overResRestrict, Over.comp_left, Over.homMk_left,
          Scheme.Hom.map_resLE]
        exact (Scheme.Hom.resLE_map _ _ _).symm
      · apply Subsingleton.elim
    rw [hsq i inf_le_left inf_le_left, hsq j inf_le_right inf_le_right,
      op_comp, op_comp, Functor.map_comp_apply,
      Functor.map_comp_apply, p.compat i j]

/-- Extensionality for glued points: equal base morphisms and classifying
morphisms agreeing up to the induced identification of sources. -/
lemma GluedPoint.ext' {T : Scheme.{0}} {p q : GluedPoint F Y R T}
    (ha : p.a = q.a)
    (hγ : ∀ i, p.γ i = eqToHom (by rw [ha]) ≫ q.γ i) : p = q := by
  obtain ⟨a, γ, c⟩ := p
  obtain ⟨a', γ', c'⟩ := q
  dsimp only at ha
  subst ha
  simp only [eqToHom_refl, Category.id_comp] at hγ
  obtain rfl : γ = γ' := funext hγ
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (F Y R) in
/-- The small total functor of glued points on the absolute category of
schemes. -/
noncomputable def gluedFunctor : Scheme.{0}ᵒᵖ ⥤ Type where
  obj T := GluedPoint F Y R T.unop
  map := fun b => TypeCat.ofHom fun p => GluedPoint.res R b.unop p
  map_id T := by
    ext p
    change GluedPoint.res R (𝟙 (unop T)) p = p
    refine GluedPoint.ext' (p := GluedPoint.res R (𝟙 (unop T)) p) (q := p)
      (Category.id_comp p.a) fun i => ?_
    change restrictHom U (𝟙 (unop T)) p.a i ≫ p.γ i = eqToHom _ ≫ p.γ i
    refine congrArg (· ≫ p.γ i) ?_
    refine hom_ext_of_ι ?_
    simp only [restrictHom, Over.homMk_left, Scheme.Hom.resLE_id,
      Scheme.homOfLE_ι, Over.eqToHom_left]
    exact (eqToHom_comp_ι (by rw [Category.id_comp]) _).symm
  map_comp {T V W} b c := by
    ext p
    change GluedPoint.res R (c.unop ≫ b.unop) p
      = GluedPoint.res R c.unop (GluedPoint.res R b.unop p)
    refine GluedPoint.ext' (p := GluedPoint.res R (c.unop ≫ b.unop) p)
      (q := GluedPoint.res R c.unop (GluedPoint.res R b.unop p))
      (Category.assoc _ _ _) fun i => ?_
    change restrictHom U (c.unop ≫ b.unop) p.a i ≫ p.γ i
      = eqToHom _ ≫ restrictHom U c.unop (b.unop ≫ p.a) i ≫
        restrictHom U b.unop p.a i ≫ p.γ i
    rw [← Category.assoc, ← Category.assoc]
    refine congrArg (· ≫ p.γ i) ?_
    refine hom_ext_of_ι ?_
    simp only [restrictHom, Over.comp_left, Over.homMk_left, Category.assoc,
      Over.eqToHom_left, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc]
    exact (eqToHom_comp_ι_assoc (by rw [Category.assoc]) _ _).symm

/-! ## §4. Glued points are sections of `F`

The sheaf axiom of `F` identifies a glued point `p` over `T` with the pair of
its base morphism `p.a` and a section of `F` over `Over.mk p.a`: the
classified local sections glue uniquely (`GluedPoint.sect`), and conversely a
section restricts to a compatible family of classified sections
(`ZariskiDescent.ofSect`). -/

variable (U) in
/-- Inverse comparison to `classifyHom` (the identity on total spaces). -/
noncomputable def classifyInv {T : Scheme.{0}} (a : T ⟶ S) (i : ι) :
    (Over.map (U i).ι).obj (Over.mk (preRes U a i)) ⟶
      overRes (Over.mk a) (pre U a i) :=
  Over.homMk (𝟙 (pre U a i).toScheme)
    (by simp only [overRes, Over.mk_hom, Over.map_obj_hom]
        exact (Scheme.Hom.resLE_comp_ι _ _).symm)

lemma classifyHom_comp_inv {T : Scheme.{0}} (a : T ⟶ S) (i : ι) :
    classifyHom U a i ≫ classifyInv U a i = 𝟙 _ := by
  apply CommaMorphism.ext
  · simp only [classifyHom, classifyInv, Over.comp_left, Over.homMk_left]
    exact Category.id_comp _
  · apply Subsingleton.elim

lemma classifyInv_comp_hom {T : Scheme.{0}} (a : T ⟶ S) (i : ι) :
    classifyInv U a i ≫ classifyHom U a i = 𝟙 _ := by
  apply CommaMorphism.ext
  · simp only [classifyHom, classifyInv, Over.comp_left, Over.homMk_left]
    exact Category.id_comp _
  · apply Subsingleton.elim

/-- The restriction inclusions compose with the full restriction morphism. -/
lemma overResLE_comp_overResHom {S' : Scheme.{0}} (T : Over S')
    {W' W : T.left.Opens} (h : W' ≤ W) :
    overResLE T h ≫ overResHom T W = overResHom T W' := by
  apply CommaMorphism.ext
  · simp only [overResLE, overResHom, Over.comp_left, Over.homMk_left]
    exact T.left.homOfLE_ι h
  · apply Subsingleton.elim

/-- The base-restriction morphism `Over.mk (b ≫ a) ⟶ Over.mk a` in `Over S`. -/
noncomputable def resSecHom {V T : Scheme.{0}} (b : V ⟶ T) (a : T ⟶ S) :
    Over.mk (b ≫ a) ⟶ Over.mk a :=
  Over.homMk b rfl

set_option backward.isDefEq.respectTransparency false in
/-- The square relating restriction of the ambient objects to the full
restriction morphisms. -/
lemma overResRestrict_comp_overResHom {V T : Scheme.{0}} (b : V ⟶ T)
    (a : T ⟶ S) (i : ι) :
    overResRestrict U b a i ≫ overResHom (Over.mk a) (pre U a i)
      = overResHom (Over.mk (b ≫ a)) (pre U (b ≫ a) i) ≫ resSecHom b a := by
  apply CommaMorphism.ext
  · simp only [overResRestrict, overResHom, resSecHom, Over.comp_left,
      Over.homMk_left]
    exact Scheme.Hom.resLE_comp_ι _ _
  · apply Subsingleton.elim

variable (hF : IsZariskiSheafOver F) (hU : ⨆ i, U i = ⊤)

include hF hU in
/-- The unique-existence content of the sheaf axiom at the covering family
`a⁻¹ U i` of the base morphism of a glued point. -/
lemma exists_sect {T : Scheme.{0}} (p : GluedPoint F Y R T) :
    ∃! x₀ : F.obj (op (Over.mk p.a)),
      ∀ i, F.map (overResHom (Over.mk p.a) (pre U p.a i)).op x₀
        = classify R (p.γ i) :=
  hF (Over.mk p.a) (pre U p.a) (p.a.iSup_preimage_eq_top hU)
    (fun i => classify R (p.γ i)) p.compat

/-- The section of `F` over `Over.mk p.a` glued from the classified local
sections of a glued point. -/
noncomputable def GluedPoint.sect {T : Scheme.{0}} (p : GluedPoint F Y R T) :
    F.obj (op (Over.mk p.a)) :=
  (exists_sect hF hU p).exists.choose

lemma GluedPoint.sect_spec {T : Scheme.{0}} (p : GluedPoint F Y R T) (i : ι) :
    F.map (overResHom (Over.mk p.a) (pre U p.a i)).op (p.sect hF hU)
      = classify R (p.γ i) :=
  (exists_sect hF hU p).exists.choose_spec i

lemma GluedPoint.sect_unique {T : Scheme.{0}} (p : GluedPoint F Y R T)
    {x : F.obj (op (Over.mk p.a))}
    (hx : ∀ i, F.map (overResHom (Over.mk p.a) (pre U p.a i)).op x
      = classify R (p.γ i)) : x = p.sect hF hU :=
  (exists_sect hF hU p).unique hx fun i => p.sect_spec hF hU i


/-- Application form of the functoriality of `F` on abstract objects of
`Over S` (avoids dependent-motive failures when rewriting under
applications). -/
lemma map_map {A B C : Over S} (f : A ⟶ B) (g : B ⟶ C) (x : F.obj (op C)) :
    F.map f.op (F.map g.op x) = F.map (f ≫ g).op x := by
  rw [op_comp, Functor.map_comp_apply]

/-- Application form of `F.map`-congruence. -/
lemma map_congr {A B : Over S} {f g : A ⟶ B} (h : f = g) (x : F.obj (op B)) :
    F.map f.op x = F.map g.op x := by rw [h]

/-- Application form of `F.map_id`. -/
lemma map_id_apply {A : Over S} (x : F.obj (op A)) : F.map (𝟙 A).op x = x := by
  rw [op_id, F.map_id]
  rfl

/-- The classified section of the classifying morphism attached to a section
of `F`: restriction of the section. -/
lemma classify_homEquiv_symm {Y : ∀ i, Over (U i).toScheme}
    (R : ∀ i, ((Over.map (U i).ι).op ⋙ F).RepresentableBy (Y i))
    {T : Scheme.{0}} (a : T ⟶ S) (x : F.obj (op (Over.mk a))) (k : ι) :
    classify R ((R k).homEquiv.symm
      (F.map (classifyInv U a k ≫ overResHom (Over.mk a) (pre U a k)).op x))
      = F.map (overResHom (Over.mk a) (pre U a k)).op x := by
  refine (congrArg (fun z => F.map (classifyHom U a k).op z)
    ((R k).homEquiv.apply_symm_apply _)).trans ?_
  refine (map_map _ _ _).trans ?_
  refine map_congr ?_ x
  rw [← Category.assoc, classifyHom_comp_inv, Category.id_comp]

variable (Y R) in
/-- The glued point attached to a base morphism `a` and a section of `F` over
`Over.mk a`: the classifying morphisms of the restricted sections. -/
noncomputable def ofSect {T : Scheme.{0}} (a : T ⟶ S)
    (x : F.obj (op (Over.mk a))) : GluedPoint F Y R T where
  a := a
  γ i := (R i).homEquiv.symm
    (F.map (classifyInv U a i ≫ overResHom (Over.mk a) (pre U a i)).op x)
  compat i j :=
    calc F.map (overResLE (Over.mk a)
          (inf_le_left : pre U a i ⊓ pre U a j ≤ pre U a i)).op
            (classify R ((R i).homEquiv.symm
              (F.map (classifyInv U a i ≫
                overResHom (Over.mk a) (pre U a i)).op x)))
        = F.map (overResLE (Over.mk a)
            (inf_le_left : pre U a i ⊓ pre U a j ≤ pre U a i)).op
            (F.map (overResHom (Over.mk a) (pre U a i)).op x) :=
          congrArg (fun z => F.map (overResLE (Over.mk a)
            (inf_le_left : pre U a i ⊓ pre U a j ≤ pre U a i)).op z)
            (classify_homEquiv_symm R a x i)
      _ = F.map (overResLE (Over.mk a)
            (inf_le_left : pre U a i ⊓ pre U a j ≤ pre U a i) ≫
            overResHom (Over.mk a) (pre U a i)).op x := map_map _ _ _
      _ = F.map (overResLE (Over.mk a)
            (inf_le_right : pre U a i ⊓ pre U a j ≤ pre U a j) ≫
            overResHom (Over.mk a) (pre U a j)).op x :=
          map_congr ((overResLE_comp_overResHom _ _).trans
            (overResLE_comp_overResHom _ _).symm) x
      _ = F.map (overResLE (Over.mk a)
            (inf_le_right : pre U a i ⊓ pre U a j ≤ pre U a j)).op
            (F.map (overResHom (Over.mk a) (pre U a j)).op x) :=
          (map_map _ _ _).symm
      _ = F.map (overResLE (Over.mk a)
            (inf_le_right : pre U a i ⊓ pre U a j ≤ pre U a j)).op
              (classify R ((R j).homEquiv.symm
                (F.map (classifyInv U a j ≫
                  overResHom (Over.mk a) (pre U a j)).op x))) :=
          (congrArg (fun z => F.map (overResLE (Over.mk a)
            (inf_le_right : pre U a i ⊓ pre U a j ≤ pre U a j)).op z)
            (classify_homEquiv_symm R a x j)).symm

@[simp]
lemma ofSect_a {T : Scheme.{0}} (a : T ⟶ S) (x : F.obj (op (Over.mk a))) :
    (ofSect Y R a x).a = a := rfl

/-- The classified sections of `ofSect` are the restrictions of the given
section. -/
lemma classify_ofSect {T : Scheme.{0}} (a : T ⟶ S)
    (x : F.obj (op (Over.mk a))) (i : ι) :
    classify R ((ofSect Y R a x).γ i)
      = F.map (overResHom (Over.mk a) (pre U a i)).op x :=
  classify_homEquiv_symm R a x i

lemma sect_ofSect {T : Scheme.{0}} (a : T ⟶ S) (x : F.obj (op (Over.mk a))) :
    (ofSect Y R a x).sect hF hU = x :=
  ((ofSect Y R a x).sect_unique hF hU fun i => (classify_ofSect a x i).symm).symm

set_option backward.isDefEq.respectTransparency false in
lemma ofSect_sect {T : Scheme.{0}} (p : GluedPoint F Y R T) :
    ofSect Y R p.a (p.sect hF hU) = p := by
  refine GluedPoint.ext' (p := ofSect Y R p.a (p.sect hF hU)) (q := p)
    rfl fun i => ?_
  simp only [eqToHom_refl, Category.id_comp]
  apply (R i).homEquiv.injective
  calc (R i).homEquiv ((ofSect Y R p.a (p.sect hF hU)).γ i)
      = F.map (classifyInv U p.a i ≫
          overResHom (Over.mk p.a) (pre U p.a i)).op (p.sect hF hU) :=
        (R i).homEquiv.apply_symm_apply _
    _ = F.map (classifyInv U p.a i).op
          (F.map (overResHom (Over.mk p.a) (pre U p.a i)).op (p.sect hF hU)) :=
        (map_map _ _ _).symm
    _ = F.map (classifyInv U p.a i).op (classify R (p.γ i)) :=
        congrArg (fun z => F.map (classifyInv U p.a i).op z)
          (p.sect_spec hF hU i)
    _ = F.map (classifyInv U p.a i ≫ classifyHom U p.a i).op
          ((R i).homEquiv (p.γ i)) := map_map _ _ _
    _ = F.map (𝟙 _).op ((R i).homEquiv (p.γ i)) :=
        map_congr (classifyInv_comp_hom p.a i) _
    _ = (R i).homEquiv (p.γ i) := map_id_apply _

set_option backward.isDefEq.respectTransparency false in
include hF hU in
/-- **Naturality of the glued section**: the section of the restricted glued
point is the restriction of the section. -/
lemma sect_res {V T : Scheme.{0}} (b : V ⟶ T) (p : GluedPoint F Y R T) :
    (GluedPoint.res R b p).sect hF hU
      = F.map (resSecHom b p.a).op (p.sect hF hU) := by
  refine ((GluedPoint.res R b p).sect_unique hF hU fun i => ?_).symm
  calc F.map (overResHom (Over.mk (b ≫ p.a)) (pre U (b ≫ p.a) i)).op
        (F.map (resSecHom b p.a).op (p.sect hF hU))
      = F.map (overResHom (Over.mk (b ≫ p.a)) (pre U (b ≫ p.a) i) ≫
          resSecHom b p.a).op (p.sect hF hU) := map_map _ _ _
    _ = F.map (overResRestrict U b p.a i ≫
          overResHom (Over.mk p.a) (pre U p.a i)).op (p.sect hF hU) :=
        (map_congr (overResRestrict_comp_overResHom b p.a i) _).symm
    _ = F.map (overResRestrict U b p.a i).op
          (F.map (overResHom (Over.mk p.a) (pre U p.a i)).op (p.sect hF hU)) :=
        (map_map _ _ _).symm
    _ = F.map (overResRestrict U b p.a i).op (classify R (p.γ i)) :=
        congrArg (fun z => F.map (overResRestrict U b p.a i).op z)
          (p.sect_spec hF hU i)
    _ = classify R (restrictHom U b p.a i ≫ p.γ i) :=
        (classify_restrictHom b (p.γ i)).symm

/-! ## §5. The glued functor is a Zariski sheaf

Sections of `gluedFunctor` glue along open covers: the base morphisms glue by
`Scheme.Cover.glueMorphisms`, and the `F`-components glue by the sheaf axiom
of `F`.  Covers by arbitrary jointly surjective open immersions reduce to
covers by opens of the target (the generated sieves agree). -/

/-- Transport of a glued point's section along an equality of glued points. -/
lemma sect_congr {T : Scheme.{0}} {p q : GluedPoint F Y R T} (h : p = q) :
    p.sect hF hU = F.map (eqToHom (by rw [h])).op (q.sect hF hU) := by
  subst h
  exact (map_id_apply _).symm

/-- Transport of `ofSect` along an equality of base morphisms. -/
lemma ofSect_congr {T : Scheme.{0}} {c d : T ⟶ S} (h : c = d)
    (x : F.obj (op (Over.mk d))) :
    ofSect Y R c (F.map (eqToHom (by rw [h])).op x) = ofSect Y R d x := by
  subst h
  exact congrArg (ofSect Y R c) (map_id_apply x)

/-- Glued points with equal base morphisms and equal (transported) sections
are equal. -/
lemma GluedPoint.eq_of_sect {T : Scheme.{0}} {p q : GluedPoint F Y R T}
    (ha : p.a = q.a)
    (hs : p.sect hF hU = F.map (eqToHom (by rw [ha])).op (q.sect hF hU)) :
    p = q := by
  rw [← ofSect_sect hF hU p, ← ofSect_sect hF hU q, hs]
  exact ofSect_congr ha (q.sect hF hU)

set_option backward.isDefEq.respectTransparency false in
include hF hU in
/-- Restriction of `ofSect` is `ofSect` of the restricted section. -/
lemma res_ofSect {V T : Scheme.{0}} (b : V ⟶ T) (a : T ⟶ S)
    (x : F.obj (op (Over.mk a))) :
    GluedPoint.res R b (ofSect Y R a x)
      = ofSect Y R (b ≫ a) (F.map (resSecHom b a).op x) := by
  refine GluedPoint.eq_of_sect hF hU rfl ?_
  rw [sect_res hF hU, sect_ofSect hF hU, sect_ofSect hF hU]
  exact (map_id_apply _).symm

set_option backward.isDefEq.respectTransparency false in
include hF hU in
/-- Restriction of any glued point along `b` in terms of `ofSect`. -/
lemma res_eq_ofSect {V T : Scheme.{0}} (b : V ⟶ T) (p : GluedPoint F Y R T) :
    GluedPoint.res R b p
      = ofSect Y R (b ≫ p.a) (F.map (resSecHom b p.a).op (p.sect hF hU)) := by
  conv_lhs => rw [← ofSect_sect hF hU p]
  exact res_ofSect hF hU b p.a (p.sect hF hU)

/-- Composition of transports along object equalities. -/
lemma map_eqToHom_trans {A B C : Over S} (h : A = B) (h' : B = C)
    (x : F.obj (op C)) :
    F.map (eqToHom h).op (F.map (eqToHom h').op x)
      = F.map (eqToHom (h.trans h')).op x := by
  subst h
  subst h'
  exact map_id_apply _

/-- Squares of `eqToHom`s in `Over S`: two morphisms with heterogeneously
equal total-space components intertwine the object identifications. -/
lemma homMk_eqToHom_square {A A' B B' : Over S} (hA : A = A') (hB : B = B')
    (m : A ⟶ B) (m' : A' ⟶ B') (hm : HEq m.left m'.left) :
    m ≫ eqToHom hB = eqToHom hA ≫ m' := by
  subst hA
  subst hB
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  apply CommaMorphism.ext
  · exact eq_of_heq hm
  · apply Subsingleton.elim

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- transport-heavy defeq checks through `Over.mk`/`overRes` identifications
include hF hU in
/-- Restriction (along an open inclusion of the total space) of the
transported section of a glued point is the transported section of the
restricted glued point. -/
lemma sect_overResLE {T : Scheme.{0}} (a : T ⟶ S) {V' V'' : T.Opens}
    (h : V' ≤ V'') (p : GluedPoint F Y R V''.toScheme)
    (hOb : overRes (Over.mk a) V'' = Over.mk p.a)
    (q : overRes (Over.mk a) V' = Over.mk (T.homOfLE h ≫ p.a)) :
    F.map (overResLE (Over.mk a) h).op (F.map (eqToHom hOb).op (p.sect hF hU))
      = F.map (eqToHom q).op
          ((GluedPoint.res R (T.homOfLE h) p).sect hF hU) := by
  have hm : (overResLE (Over.mk a) h).left
      = (resSecHom (T.homOfLE h) p.a).left := by
    simp only [overResLE, resSecHom, Over.homMk_left]
    rfl
  have hsq : overResLE (Over.mk a) h ≫ eqToHom hOb
      = eqToHom q ≫ resSecHom (T.homOfLE h) p.a :=
    homMk_eqToHom_square q hOb _ _ (heq_of_eq hm)
  calc F.map (overResLE (Over.mk a) h).op
        (F.map (eqToHom hOb).op (p.sect hF hU))
      = F.map (overResLE (Over.mk a) h ≫ eqToHom hOb).op (p.sect hF hU) :=
        map_map _ _ _
    _ = F.map (eqToHom q ≫ resSecHom (T.homOfLE h) p.a).op (p.sect hF hU) :=
        map_congr hsq _
    _ = F.map (eqToHom q).op
          (F.map (resSecHom (T.homOfLE h) p.a).op (p.sect hF hU)) :=
        (map_map _ _ _).symm
    _ = F.map (eqToHom q).op
          ((GluedPoint.res R (T.homOfLE h) p).sect hF hU) :=
        congrArg (fun z => F.map (eqToHom q).op z) (sect_res hF hU _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- transport-heavy defeq checks through `Over.mk`/`overRes` identifications
include hF hU in
/-- **The glued functor satisfies the sheaf condition at covers by opens.** -/
lemma isSheafFor_opens (T : Scheme.{0}) {κ : Type} (W : κ → T.Opens)
    (hW : ⨆ k, W k = ⊤) :
    Presieve.IsSheafFor (gluedFunctor F Y R)
      (Presieve.ofArrows (fun k => (W k).toScheme) (fun k => (W k).ι)) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  -- Glue the base morphisms.
  have hcompat : ∀ k l : κ,
      pullback.fst ((W k).ι) ((W l).ι) ≫ (x k).a
        = pullback.snd ((W k).ι) ((W l).ι) ≫ (x l).a := fun k l =>
    congrArg GluedPoint.a
      (hx k l (pullback ((W k).ι) ((W l).ι)) (pullback.fst _ _)
        (pullback.snd _ _) pullback.condition)
  obtain ⟨a, ha⟩ : ∃ a : T ⟶ S, ∀ k, (W k).ι ≫ a = (x k).a :=
    ⟨(opensCover T W hW).glueMorphisms (fun k => (x k).a) hcompat, fun k =>
      (opensCover T W hW).ι_glueMorphisms (fun k => (x k).a) hcompat k⟩
  have hOb : ∀ k, overRes (Over.mk a) (W k) = Over.mk ((x k).a) :=
    fun k => congrArg Over.mk (ha k)
  -- The compatibility of the family of restrictions on the overlaps.
  have hres : ∀ k l, GluedPoint.res R (T.homOfLE
        (inf_le_left : W k ⊓ W l ≤ W k)) (x k)
      = GluedPoint.res R (T.homOfLE inf_le_right) (x l) := by
    intro k l
    refine hx k l ((W k ⊓ W l).toScheme) (T.homOfLE inf_le_left)
      (T.homOfLE inf_le_right) ?_
    rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  have hq : ∀ (k l m : κ) (hm : W k ⊓ W l ≤ W m),
      overRes (Over.mk a) (W k ⊓ W l) = Over.mk (T.homOfLE hm ≫ (x m).a) :=
    fun k l m hm => congrArg Over.mk
      (show (W k ⊓ W l).ι ≫ a = T.homOfLE hm ≫ (x m).a by
        rw [← ha m, ← Category.assoc, Scheme.homOfLE_ι])
  -- Glue the `F`-sections via the sheaf axiom of `F`.
  have hsheaf := hF (Over.mk a) W (by change ⨆ k, W k = ⊤; exact hW)
    (fun k => F.map (eqToHom (hOb k)).op ((x k).sect hF hU))
    (by
      intro k l
      calc F.map (overResLE (Over.mk a)
            (inf_le_left : W k ⊓ W l ≤ W k)).op
              (F.map (eqToHom (hOb k)).op ((x k).sect hF hU))
          = F.map (eqToHom (hq k l k inf_le_left)).op
              ((GluedPoint.res R (T.homOfLE inf_le_left) (x k)).sect hF hU) :=
            sect_overResLE hF hU a inf_le_left (x k) (hOb k) _
        _ = F.map (eqToHom (hq k l k inf_le_left)).op
              (F.map (eqToHom (congrArg (fun p => Over.mk p.a) (hres k l))).op
                ((GluedPoint.res R (T.homOfLE inf_le_right) (x l)).sect hF hU)) :=
            congrArg (fun z => F.map (eqToHom (hq k l k inf_le_left)).op z)
              (sect_congr hF hU (hres k l))
        _ = F.map (eqToHom ((hq k l k inf_le_left).trans
              (congrArg (fun p => Over.mk p.a) (hres k l)))).op
              ((GluedPoint.res R (T.homOfLE inf_le_right) (x l)).sect hF hU) :=
            map_eqToHom_trans _ _ _
        _ = F.map (eqToHom (hq k l l inf_le_right)).op
              ((GluedPoint.res R (T.homOfLE inf_le_right) (x l)).sect hF hU) :=
            rfl
        _ = F.map (overResLE (Over.mk a)
            (inf_le_right : W k ⊓ W l ≤ W l)).op
              (F.map (eqToHom (hOb l)).op ((x l).sect hF hU)) :=
            (sect_overResLE hF hU a inf_le_right (x l) (hOb l) _).symm)
  obtain ⟨x₀, hx₀, hx₀uniq⟩ := hsheaf
  refine ⟨ofSect Y R a x₀, fun k => ?_, fun t' ht' => ?_⟩
  · -- The amalgamation restricts to the given family.
    change GluedPoint.res R ((W k).ι) (ofSect Y R a x₀) = x k
    rw [res_ofSect hF hU]
    have : F.map (resSecHom ((W k).ι) a).op x₀
        = F.map (eqToHom (by rw [ha k] :
            Over.mk ((W k).ι ≫ a) = Over.mk ((x k).a))).op
          ((x k).sect hF hU) := hx₀ k
    rw [this]
    exact (ofSect_congr (ha k) _).trans (ofSect_sect hF hU (x k))
  · -- Uniqueness.
    have haT : t'.a = a := by
      refine (opensCover T W hW).hom_ext _ _ fun k => ?_
      change (W k).ι ≫ t'.a = (W k).ι ≫ a
      rw [ha k]
      exact congrArg GluedPoint.a (ht' k)
    have hz : F.map (eqToHom (congrArg Over.mk haT.symm :
        Over.mk a = Over.mk t'.a)).op (t'.sect hF hU) = x₀ := by
      refine hx₀uniq _ fun k => ?_
      have hOb' : overRes (Over.mk a) (W k) = Over.mk ((W k).ι ≫ t'.a) :=
        congrArg Over.mk (show (W k).ι ≫ a = (W k).ι ≫ t'.a by rw [haT])
      calc F.map (overResHom (Over.mk a) (W k)).op
            (F.map (eqToHom (congrArg Over.mk haT.symm :
              Over.mk a = Over.mk t'.a)).op (t'.sect hF hU))
          = F.map (eqToHom hOb').op
              (F.map (resSecHom ((W k).ι) t'.a).op (t'.sect hF hU)) := by
            rw [map_map, map_map]
            refine map_congr (homMk_eqToHom_square hOb'
              (congrArg Over.mk haT.symm) (overResHom (Over.mk a) (W k))
              (resSecHom ((W k).ι) t'.a) (heq_of_eq ?_)) _
            simp only [overResHom, resSecHom, Over.homMk_left]
        _ = F.map (eqToHom hOb').op
              ((GluedPoint.res R ((W k).ι) t').sect hF hU) :=
            congrArg (fun z => F.map (eqToHom hOb').op z)
              (sect_res hF hU _ _).symm
        _ = F.map (eqToHom hOb').op
              (F.map (eqToHom (congrArg (fun p => Over.mk p.a) (ht' k))).op
                ((x k).sect hF hU)) :=
            congrArg (fun z => F.map (eqToHom hOb').op z)
              (sect_congr hF hU (ht' k))
        _ = F.map (eqToHom (hOb k)).op ((x k).sect hF hU) :=
            map_eqToHom_trans _ _ _
    calc t' = ofSect Y R t'.a (t'.sect hF hU) := (ofSect_sect hF hU t').symm
      _ = ofSect Y R a x₀ := by
          rw [← hz]
          exact (ofSect_congr haT.symm (t'.sect hF hU)).symm

set_option backward.isDefEq.respectTransparency false in
include hF hU in
/-- **The glued functor is a sheaf for the big Zariski topology.** -/
lemma isSheaf_gluedFunctor :
    Presieve.IsSheaf Scheme.zariskiTopology (gluedFunctor F Y R) := by
  rw [zariskiTopology_eq, Presieve.isSheaf_pretopology]
  rintro T Rp hRp
  obtain ⟨𝓤, rfl⟩ := exists_cover_of_mem_pretopology hRp
  -- Reduce to the cover by the image opens: both presieves generate the
  -- same sieve, since each factors through the other.
  let κ : Type := {V : T.Opens // ∃ j, (𝓤.f j).opensRange = V}
  let W : κ → T.Opens := Subtype.val
  have hW : ⨆ k, W k = ⊤ := by
    rw [eq_top_iff]
    rintro t -
    obtain ⟨j, y, hy⟩ := 𝓤.exists_eq t
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨(𝓤.f j).opensRange, j, rfl⟩, ⟨y, hy⟩⟩
  have hgen : Sieve.generate (Presieve.ofArrows 𝓤.X 𝓤.f)
      = Sieve.generate
          (Presieve.ofArrows (fun k => (W k).toScheme) (fun k => (W k).ι)) := by
    apply le_antisymm
    · rw [Sieve.generate_le_iff]
      rintro Z g ⟨j⟩
      refine ⟨((𝓤.f j).opensRange).toScheme,
        IsOpenImmersion.lift ((𝓤.f j).opensRange).ι (𝓤.f j)
          (by rw [Scheme.Opens.range_ι]; exact subset_rfl),
        ((𝓤.f j).opensRange).ι,
        Presieve.ofArrows.mk (⟨(𝓤.f j).opensRange, j, rfl⟩ : κ),
        IsOpenImmersion.lift_fac _ _ _⟩
    · rw [Sieve.generate_le_iff]
      rintro Z g ⟨k⟩
      obtain ⟨j, hj⟩ := k.2
      refine ⟨𝓤.X j, IsOpenImmersion.lift (𝓤.f j) ((k.1).ι)
        (by rw [Scheme.Opens.range_ι, ← hj]; exact subset_rfl), 𝓤.f j,
        Presieve.ofArrows.mk j, IsOpenImmersion.lift_fac _ _ _⟩
  rw [Presieve.isSheafFor_iff_generate, hgen,
    ← Presieve.isSheafFor_iff_generate]
  exact isSheafFor_opens hF hU T W hW

/-! ## §6. The charts

Each local representing object `Y i` maps to the glued functor: a morphism
`t : T ⟶ (Y i).left` classifies an `F`-section over
`T → U i → S`, whose glued point is the chart image of `t`. -/

include hF hU in
/-- The classifying morphism of a glued point classifies the restriction of
its section. -/
lemma homEquiv_gamma {T : Scheme.{0}} (p : GluedPoint F Y R T) (i : ι) :
    (R i).homEquiv (p.γ i)
      = F.map (classifyInv U p.a i ≫
          overResHom (Over.mk p.a) (pre U p.a i)).op (p.sect hF hU) :=
  calc (R i).homEquiv (p.γ i)
      = F.map (𝟙 _).op ((R i).homEquiv (p.γ i)) := (map_id_apply _).symm
    _ = F.map (classifyInv U p.a i ≫ classifyHom U p.a i).op
          ((R i).homEquiv (p.γ i)) :=
        (map_congr (classifyInv_comp_hom p.a i) _).symm
    _ = F.map (classifyInv U p.a i).op
          (F.map (classifyHom U p.a i).op ((R i).homEquiv (p.γ i))) :=
        (map_map _ _ _).symm
    _ = F.map (classifyInv U p.a i).op
          (F.map (overResHom (Over.mk p.a) (pre U p.a i)).op (p.sect hF hU)) :=
        (congrArg (fun z => F.map (classifyInv U p.a i).op z)
          (p.sect_spec hF hU i)).symm
    _ = F.map (classifyInv U p.a i ≫
          overResHom (Over.mk p.a) (pre U p.a i)).op (p.sect hF hU) :=
        map_map _ _ _

variable (Y R) in
/-- The underlying function of the chart attached to `i`: a morphism
`t : T ⟶ (Y i).left` yields the glued point of the `F`-section it
classifies. -/
noncomputable def chartFun (i : ι) {T : Scheme.{0}} (t : T ⟶ (Y i).left) :
    GluedPoint F Y R T :=
  ofSect Y R ((t ≫ (Y i).hom) ≫ (U i).ι)
    ((R i).homEquiv (Over.homMk t rfl : Over.mk (t ≫ (Y i).hom) ⟶ Y i))

@[simp]
lemma chartFun_a (i : ι) {T : Scheme.{0}} (t : T ⟶ (Y i).left) :
    (chartFun Y R i t).a = (t ≫ (Y i).hom) ≫ (U i).ι := rfl

set_option backward.isDefEq.respectTransparency false in
include hF hU in
/-- Naturality of the chart function. -/
lemma chartFun_natural (i : ι) {V T : Scheme.{0}} (b : V ⟶ T)
    (t : T ⟶ (Y i).left) :
    chartFun Y R i (b ≫ t) = GluedPoint.res R b (chartFun Y R i t) := by
  have hOb : Over.mk (((b ≫ t) ≫ (Y i).hom) ≫ (U i).ι)
      = Over.mk (b ≫ (t ≫ (Y i).hom) ≫ (U i).ι) :=
    congrArg Over.mk (by simp only [Category.assoc])
  refine Eq.trans ?_
    (res_ofSect hF hU b ((t ≫ (Y i).hom) ≫ (U i).ι)
      ((R i).homEquiv (Over.homMk t rfl : Over.mk (t ≫ (Y i).hom) ⟶ Y i))).symm
  have hmor : (Over.homMk (b ≫ t) rfl :
        Over.mk ((b ≫ t) ≫ (Y i).hom) ⟶ Y i)
      = (Over.homMk b (Category.assoc b t (Y i).hom).symm :
          Over.mk ((b ≫ t) ≫ (Y i).hom) ⟶ Over.mk (t ≫ (Y i).hom))
        ≫ (Over.homMk t rfl : Over.mk (t ≫ (Y i).hom) ⟶ Y i) := by
    apply CommaMorphism.ext
    · simp only [Over.comp_left, Over.homMk_left]
    · apply Subsingleton.elim
  have hsq : (Over.map (U i).ι).map
        (Over.homMk b (Category.assoc b t (Y i).hom).symm :
          Over.mk ((b ≫ t) ≫ (Y i).hom) ⟶ Over.mk (t ≫ (Y i).hom))
      = eqToHom hOb ≫ resSecHom b ((t ≫ (Y i).hom) ≫ (U i).ι) := by
    have h := homMk_eqToHom_square hOb rfl
      ((Over.map (U i).ι).map
        (Over.homMk b (Category.assoc b t (Y i).hom).symm :
          Over.mk ((b ≫ t) ≫ (Y i).hom) ⟶ Over.mk (t ≫ (Y i).hom)))
      (resSecHom b ((t ≫ (Y i).hom) ≫ (U i).ι))
      (heq_of_eq (by simp only [resSecHom, Over.homMk_left, Over.map_map_left]))
    rwa [eqToHom_refl, Category.comp_id] at h
  calc chartFun Y R i (b ≫ t)
      = ofSect Y R (((b ≫ t) ≫ (Y i).hom) ≫ (U i).ι)
          ((R i).homEquiv
            ((Over.homMk b (Category.assoc b t (Y i).hom).symm :
              Over.mk ((b ≫ t) ≫ (Y i).hom) ⟶ Over.mk (t ≫ (Y i).hom))
             ≫ (Over.homMk t rfl : Over.mk (t ≫ (Y i).hom) ⟶ Y i))) := by
        rw [chartFun, hmor]
    _ = ofSect Y R (((b ≫ t) ≫ (Y i).hom) ≫ (U i).ι)
          (F.map (eqToHom hOb ≫
            resSecHom b ((t ≫ (Y i).hom) ≫ (U i).ι)).op
            ((R i).homEquiv
              (Over.homMk t rfl : Over.mk (t ≫ (Y i).hom) ⟶ Y i))) := by
        refine congrArg (ofSect Y R _) ?_
        refine ((R i).homEquiv_comp _ _).trans ?_
        exact map_congr hsq _
    _ = ofSect Y R (((b ≫ t) ≫ (Y i).hom) ≫ (U i).ι)
          (F.map (eqToHom hOb).op
            (F.map (resSecHom b ((t ≫ (Y i).hom) ≫ (U i).ι)).op
              ((R i).homEquiv
                (Over.homMk t rfl : Over.mk (t ≫ (Y i).hom) ⟶ Y i)))) :=
        congrArg (ofSect Y R _) (map_map _ _ _).symm
    _ = ofSect Y R (b ≫ (t ≫ (Y i).hom) ≫ (U i).ι)
          (F.map (resSecHom b ((t ≫ (Y i).hom) ≫ (U i).ι)).op
            ((R i).homEquiv
              (Over.homMk t rfl : Over.mk (t ≫ (Y i).hom) ⟶ Y i))) :=
        ofSect_congr (by simp only [Category.assoc]) _

variable (F Y R) in
/-- The chart natural transformation attached to `i`. -/
noncomputable def chart (hF : IsZariskiSheafOver F) (hU : ⨆ i, U i = ⊤)
    (i : ι) : yoneda.obj (Y i).left ⟶ gluedFunctor F Y R where
  app T := TypeCat.ofHom fun t => chartFun Y R i t
  naturality {T V} b := by
    ext t
    change chartFun Y R i (b.unop ≫ t)
      = GluedPoint.res R b.unop (chartFun Y R i t)
    exact chartFun_natural hF hU i b.unop t

/-! ## §7. The charts are relatively representable open immersions

The pullback of the chart `chart i` against a point `p` of the glued functor
over `A` is the open subscheme `p.a⁻¹(U i) ⊆ A`, with structure morphism the
total-space component of the classifying morphism `p.γ i`. -/

set_option backward.isDefEq.respectTransparency false in
include hF hU in
/-- Compatibility of the chart function with restriction to the preimage
open: the chart image of `w ≫ (p.γ i).left` is the restriction of `p`. -/
lemma chartFun_comp {A V : Scheme.{0}} (p : GluedPoint F Y R A) (i : ι)
    (w : V ⟶ (pre U p.a i).toScheme) :
    chartFun Y R i (w ≫ (p.γ i).left)
      = GluedPoint.res R (w ≫ (pre U p.a i).ι) p := by
  have htri : (w ≫ (p.γ i).left) ≫ (Y i).hom
      = w ≫ (Over.mk (preRes U p.a i)).hom :=
    (Category.assoc w _ _).trans
      (congrArg (fun z => w ≫ z) (Over.w (p.γ i)))
  have ha' : ((w ≫ (p.γ i).left) ≫ (Y i).hom) ≫ (U i).ι
      = (w ≫ (pre U p.a i).ι) ≫ p.a := by
    rw [htri]
    change (w ≫ p.a.resLE (U i) (pre U p.a i) le_rfl) ≫ (U i).ι = _
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Category.assoc]
  have hOb : Over.mk (((w ≫ (p.γ i).left) ≫ (Y i).hom) ≫ (U i).ι)
      = Over.mk ((w ≫ (pre U p.a i).ι) ≫ p.a) :=
    congrArg Over.mk ha' 
  have hmor : (Over.homMk (w ≫ (p.γ i).left) rfl :
        Over.mk ((w ≫ (p.γ i).left) ≫ (Y i).hom) ⟶ Y i)
      = (Over.homMk w htri.symm :
          Over.mk ((w ≫ (p.γ i).left) ≫ (Y i).hom) ⟶
            Over.mk (preRes U p.a i)) ≫ p.γ i := by
    apply CommaMorphism.ext
    · simp only [Over.comp_left, Over.homMk_left]
    · apply Subsingleton.elim
  have hsq : (Over.map (U i).ι).map
        (Over.homMk w htri.symm :
          Over.mk ((w ≫ (p.γ i).left) ≫ (Y i).hom) ⟶
            Over.mk (preRes U p.a i))
      ≫ (classifyInv U p.a i ≫ overResHom (Over.mk p.a) (pre U p.a i))
      = eqToHom hOb ≫ resSecHom (w ≫ (pre U p.a i).ι) p.a := by
    have h := homMk_eqToHom_square hOb rfl
      ((Over.map (U i).ι).map
        (Over.homMk w htri.symm :
          Over.mk ((w ≫ (p.γ i).left) ≫ (Y i).hom) ⟶
            Over.mk (preRes U p.a i))
        ≫ (classifyInv U p.a i ≫ overResHom (Over.mk p.a) (pre U p.a i)))
      (resSecHom (w ≫ (pre U p.a i).ι) p.a)
      (heq_of_eq (by
        simp only [Over.comp_left, Over.homMk_left, Over.map_map_left,
          classifyInv, overResHom, resSecHom]
        exact congrArg (fun z => w ≫ z) (Category.id_comp _)))
    rwa [eqToHom_refl, Category.comp_id] at h
  calc chartFun Y R i (w ≫ (p.γ i).left)
      = ofSect Y R (((w ≫ (p.γ i).left) ≫ (Y i).hom) ≫ (U i).ι)
          ((R i).homEquiv
            ((Over.homMk w htri.symm :
              Over.mk ((w ≫ (p.γ i).left) ≫ (Y i).hom) ⟶
                Over.mk (preRes U p.a i)) ≫ p.γ i)) := by
        rw [chartFun, hmor]
    _ = ofSect Y R (((w ≫ (p.γ i).left) ≫ (Y i).hom) ≫ (U i).ι)
          (F.map ((Over.map (U i).ι).map
            (Over.homMk w htri.symm :
              Over.mk ((w ≫ (p.γ i).left) ≫ (Y i).hom) ⟶
                Over.mk (preRes U p.a i))).op
            ((R i).homEquiv (p.γ i))) :=
        congrArg (ofSect Y R _) ((R i).homEquiv_comp _ _)
    _ = ofSect Y R (((w ≫ (p.γ i).left) ≫ (Y i).hom) ≫ (U i).ι)
          (F.map ((Over.map (U i).ι).map
            (Over.homMk w htri.symm :
              Over.mk ((w ≫ (p.γ i).left) ≫ (Y i).hom) ⟶
                Over.mk (preRes U p.a i))).op
            (F.map (classifyInv U p.a i ≫
              overResHom (Over.mk p.a) (pre U p.a i)).op (p.sect hF hU))) :=
        congrArg (ofSect Y R _)
          (congrArg (fun z => F.map ((Over.map (U i).ι).map
            (Over.homMk w htri.symm :
              Over.mk ((w ≫ (p.γ i).left) ≫ (Y i).hom) ⟶
                Over.mk (preRes U p.a i))).op z) (homEquiv_gamma hF hU p i))
    _ = ofSect Y R (((w ≫ (p.γ i).left) ≫ (Y i).hom) ≫ (U i).ι)
          (F.map (eqToHom hOb ≫
            resSecHom (w ≫ (pre U p.a i).ι) p.a).op (p.sect hF hU)) :=
        congrArg (ofSect Y R _) ((map_map _ _ _).trans (map_congr hsq _))
    _ = ofSect Y R (((w ≫ (p.γ i).left) ≫ (Y i).hom) ≫ (U i).ι)
          (F.map (eqToHom hOb).op
            (F.map (resSecHom (w ≫ (pre U p.a i).ι) p.a).op
              (p.sect hF hU))) :=
        congrArg (ofSect Y R _) (map_map _ _ _).symm
    _ = ofSect Y R ((w ≫ (pre U p.a i).ι) ≫ p.a)
          (F.map (resSecHom (w ≫ (pre U p.a i).ι) p.a).op (p.sect hF hU)) :=
        ofSect_congr ha' _
    _ = GluedPoint.res R (w ≫ (pre U p.a i).ι) p :=
        (res_eq_ofSect hF hU (w ≫ (pre U p.a i).ι) p).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- transport-heavy defeq checks through `Over.mk`/`overRes` identifications
include hF hU in
/-- **The chart pullback square**: the pullback of `chart i` against the
point `p : yoneda.obj A ⟶ gluedFunctor` is the open subscheme
`p.a⁻¹(U i) ⊆ A`. -/
lemma chart_isPullback (i : ι) {A : Scheme.{0}} (p : GluedPoint F Y R A) :
    IsPullback (yoneda.map (p.γ i).left) (yoneda.map (pre U p.a i).ι)
      (chart F Y R hF hU i) (yonedaEquiv.symm p) := by
  refine isPullback_of_app fun c => ?_
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext w
    change chartFun Y R i (w ≫ (p.γ i).left)
      = GluedPoint.res R (w ≫ (pre U p.a i).ι) p
    exact chartFun_comp hF hU p i w
  · intro w₁ w₂ hw
    have h₂ : w₁ ≫ (pre U p.a i).ι = w₂ ≫ (pre U p.a i).ι := hw.2
    exact (cancel_mono _).mp h₂
  · intro s v hsv
    have hsv' : chartFun Y R i s = GluedPoint.res R v p := hsv
    have ha' : (s ≫ (Y i).hom) ≫ (U i).ι = v ≫ p.a :=
      congrArg GluedPoint.a hsv'
    have hrange : Set.range v.base ⊆ Set.range ((pre U p.a i).ι).base := by
      rw [Scheme.Opens.range_ι]
      rintro pt ⟨q, rfl⟩
      have h1 : (v ≫ p.a).base q ∈ Set.range ((U i).ι).base := by
        rw [← ha']
        exact ⟨(s ≫ (Y i).hom).base q, rfl⟩
      rw [Scheme.Opens.range_ι] at h1
      exact h1
    refine ⟨IsOpenImmersion.lift ((pre U p.a i).ι) v hrange, ?_, ?_⟩
    swap
    · exact IsOpenImmersion.lift_fac _ _ _
    -- first coordinate: w ≫ (p.γ i).left = s
    · set w := IsOpenImmersion.lift ((pre U p.a i).ι) v hrange with hw_def
      have hw : w ≫ (pre U p.a i).ι = v := IsOpenImmersion.lift_fac _ _ _
      have htri : w ≫ (Over.mk (preRes U p.a i)).hom = s ≫ (Y i).hom := by
        rw [← cancel_mono ((U i).ι)]
        change w ≫ p.a.resLE (U i) (pre U p.a i) le_rfl ≫ (U i).ι = _
        rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, hw, ← ha',
          Category.assoc]
      have hOb : Over.mk ((s ≫ (Y i).hom) ≫ (U i).ι) = Over.mk (v ≫ p.a) :=
        congrArg Over.mk ha'
      have hsq : (Over.map (U i).ι).map
            (Over.homMk w htri :
              Over.mk (s ≫ (Y i).hom) ⟶ Over.mk (preRes U p.a i))
          ≫ (classifyInv U p.a i ≫ overResHom (Over.mk p.a) (pre U p.a i))
          = eqToHom hOb ≫ resSecHom v p.a := by
        have h := homMk_eqToHom_square hOb rfl
          ((Over.map (U i).ι).map
            (Over.homMk w htri :
              Over.mk (s ≫ (Y i).hom) ⟶ Over.mk (preRes U p.a i))
            ≫ (classifyInv U p.a i ≫
              overResHom (Over.mk p.a) (pre U p.a i)))
          (resSecHom v p.a)
          (heq_of_eq (by
            simp only [Over.comp_left, Over.homMk_left, Over.map_map_left,
              classifyInv, overResHom, resSecHom]
            refine Eq.trans (congrArg (fun z => w ≫ z)
              (Category.id_comp _)) hw))
        rwa [eqToHom_refl, Category.comp_id] at h
      have hkey : (Over.homMk s rfl : Over.mk (s ≫ (Y i).hom) ⟶ Y i)
          = (Over.homMk w htri :
              Over.mk (s ≫ (Y i).hom) ⟶ Over.mk (preRes U p.a i)) ≫ p.γ i := by
        apply (R i).homEquiv.injective
        calc (R i).homEquiv (Over.homMk s rfl :
              Over.mk (s ≫ (Y i).hom) ⟶ Y i)
            = (chartFun Y R i s).sect hF hU := (sect_ofSect hF hU _ _).symm
          _ = F.map (eqToHom hOb).op
                ((GluedPoint.res R v p).sect hF hU) := by
              refine (sect_congr hF hU hsv').trans ?_
              rfl
          _ = F.map (eqToHom hOb).op
                (F.map (resSecHom v p.a).op (p.sect hF hU)) :=
              congrArg (fun z => F.map (eqToHom hOb).op z)
                (sect_res hF hU v p)
          _ = F.map (eqToHom hOb ≫ resSecHom v p.a).op (p.sect hF hU) :=
              map_map _ _ _
          _ = F.map ((Over.map (U i).ι).map
                (Over.homMk w htri :
                  Over.mk (s ≫ (Y i).hom) ⟶ Over.mk (preRes U p.a i))
                ≫ (classifyInv U p.a i ≫
                  overResHom (Over.mk p.a) (pre U p.a i))).op
                (p.sect hF hU) := (map_congr hsq _).symm
          _ = F.map ((Over.map (U i).ι).map
                (Over.homMk w htri :
                  Over.mk (s ≫ (Y i).hom) ⟶ Over.mk (preRes U p.a i))).op
                (F.map (classifyInv U p.a i ≫
                  overResHom (Over.mk p.a) (pre U p.a i)).op
                  (p.sect hF hU)) := (map_map _ _ _).symm
          _ = F.map ((Over.map (U i).ι).map
                (Over.homMk w htri :
                  Over.mk (s ≫ (Y i).hom) ⟶ Over.mk (preRes U p.a i))).op
                ((R i).homEquiv (p.γ i)) :=
              (congrArg (fun z => F.map ((Over.map (U i).ι).map
                (Over.homMk w htri :
                  Over.mk (s ≫ (Y i).hom) ⟶ Over.mk (preRes U p.a i))).op z)
                (homEquiv_gamma hF hU p i)).symm
          _ = (R i).homEquiv ((Over.homMk w htri :
                Over.mk (s ≫ (Y i).hom) ⟶ Over.mk (preRes U p.a i))
                ≫ p.γ i) := ((R i).homEquiv_comp _ _).symm
      have hleft : s = w ≫ (p.γ i).left := by
        simpa only [Over.homMk_left, Over.comp_left] using
          congrArg CommaMorphism.left hkey
      change w ≫ (p.γ i).left = s
      exact hleft.symm

include hF hU in
/-- **The charts are relatively representable open immersions.** -/
lemma chart_presheaf (i : ι) :
    IsOpenImmersion.presheaf (chart F Y R hF hU i) := by
  refine MorphismProperty.relative.of_exists ?_
  intro A g
  refine ⟨(pre U (yonedaEquiv g).a i).toScheme,
    yoneda.map (((yonedaEquiv g).γ i).left),
    (pre U (yonedaEquiv g).a i).ι, ?_, inferInstance⟩
  have h := chart_isPullback hF hU i (yonedaEquiv g)
  rwa [Equiv.symm_apply_apply] at h

set_option backward.isDefEq.respectTransparency false in
include hF hU in
/-- **The charts are jointly locally surjective.** -/
lemma isLocallySurjective_chart :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (fun i => chart F Y R hF hU i)) := by
  constructor
  intro A p
  have hmem : ∀ (i : ι) (V : Scheme.{0}) (g' : V ⟶ (pre U p.a i).toScheme),
      (Presheaf.imageSieve (Sigma.desc fun j => chart F Y R hF hU j) p).arrows
        (g' ≫ (pre U p.a i).ι) := by
    intro i V g'
    refine ⟨yonedaEquiv (yoneda.map (g' ≫ (p.γ i).left) ≫
      Sigma.ι (fun j : ι => yoneda.obj (Y j).left) i), ?_⟩
    change yonedaEquiv ((yoneda.map (g' ≫ (p.γ i).left) ≫
      Sigma.ι (fun j : ι => yoneda.obj (Y j).left) i) ≫
        Sigma.desc fun j => chart F Y R hF hU j) = _
    rw [Category.assoc, Sigma.ι_desc, ← yonedaEquiv_naturality]
    change GluedPoint.res R (g' ≫ (p.γ i).left)
      (chartFun Y R i (𝟙 (Y i).left)) = _
    rw [← chartFun_natural hF hU, Category.comp_id]
    exact chartFun_comp hF hU p i g'
  refine GrothendieckTopology.superset_covering _ ?_
    ((opensCover A (pre U p.a) (p.a.iSup_preimage_eq_top hU)).mem_grothendieckTopology)
  intro V f hf
  obtain ⟨Z', g', f', hR, rfl⟩ := hf
  revert g'
  obtain ⟨i⟩ := hR
  intro g'
  exact hmem i V g'

/-! ## §8. From absolute representability back to `Over S`

Given a representation of the glued functor by an absolute scheme `Ŷ`
(produced by mathlib's Stacks 01JJ), the tautological glued point of `Ŷ`
yields the structure morphism `â : Ŷ ⟶ S`, and the section machinery
identifies `Hom_{Over S}(T, (Ŷ, â))` with `F(T)`. -/

set_option backward.isDefEq.respectTransparency false in
include hF hU in
/-- Composition of restrictions of glued points. -/
lemma res_res {V' V T : Scheme.{0}} (b : V' ⟶ V) (c : V ⟶ T)
    (p : GluedPoint F Y R T) :
    GluedPoint.res R b (GluedPoint.res R c p) = GluedPoint.res R (b ≫ c) p := by
  refine GluedPoint.eq_of_sect hF hU (Category.assoc b c p.a).symm ?_
  have hsq : resSecHom b (c ≫ p.a) ≫ resSecHom c p.a
      = eqToHom (congrArg Over.mk (Category.assoc b c p.a).symm) ≫
        resSecHom (b ≫ c) p.a := by
    have h := homMk_eqToHom_square
      (congrArg Over.mk (Category.assoc b c p.a).symm) rfl
      (resSecHom b (c ≫ p.a) ≫ resSecHom c p.a) (resSecHom (b ≫ c) p.a)
      (heq_of_eq (by simp only [resSecHom, Over.comp_left, Over.homMk_left]))
    rwa [eqToHom_refl, Category.comp_id] at h
  calc (GluedPoint.res R b (GluedPoint.res R c p)).sect hF hU
      = F.map (resSecHom b (c ≫ p.a)).op
          ((GluedPoint.res R c p).sect hF hU) := sect_res hF hU b _
    _ = F.map (resSecHom b (c ≫ p.a)).op
          (F.map (resSecHom c p.a).op (p.sect hF hU)) :=
        congrArg (fun z => F.map (resSecHom b (c ≫ p.a)).op z)
          (sect_res hF hU c p)
    _ = F.map (resSecHom b (c ≫ p.a) ≫ resSecHom c p.a).op (p.sect hF hU) :=
        map_map _ _ _
    _ = F.map (eqToHom (congrArg Over.mk (Category.assoc b c p.a).symm) ≫
          resSecHom (b ≫ c) p.a).op (p.sect hF hU) := map_congr hsq _
    _ = F.map (eqToHom (congrArg Over.mk (Category.assoc b c p.a).symm)).op
          (F.map (resSecHom (b ≫ c) p.a).op (p.sect hF hU)) :=
        (map_map _ _ _).symm
    _ = F.map (eqToHom (congrArg Over.mk (Category.assoc b c p.a).symm)).op
          ((GluedPoint.res R (b ≫ c) p).sect hF hU) :=
        congrArg (fun z => F.map (eqToHom (congrArg Over.mk
          (Category.assoc b c p.a).symm)).op z) (sect_res hF hU (b ≫ c) p).symm

section Assemble

variable {Ŷ : Scheme.{0}} (RepG : (gluedFunctor F Y R).RepresentableBy Ŷ)

/-- The representation of the glued functor in restriction form. -/
lemma repG_eq {V : Scheme.{0}} (t : V ⟶ Ŷ) :
    RepG.homEquiv t = GluedPoint.res R t (RepG.homEquiv (𝟙 Ŷ)) := by
  conv_lhs => rw [← Category.comp_id t]
  exact RepG.homEquiv_comp t (𝟙 Ŷ)

set_option backward.isDefEq.respectTransparency false in
/-- The structure-morphism triangle for the inverse construction. -/
lemma symm_ofSect_w {T : Over S} (x : F.obj (op T)) :
    RepG.homEquiv.symm (ofSect Y R T.hom
        (F.map (eqToHom (CostructuredArrow.eq_mk T).symm).op x)) ≫
      (RepG.homEquiv (𝟙 Ŷ)).a = T.hom := by
  have h2 := repG_eq RepG (RepG.homEquiv.symm (ofSect Y R T.hom
    (F.map (eqToHom (CostructuredArrow.eq_mk T).symm).op x)))
  rw [Equiv.apply_symm_apply] at h2
  exact congrArg GluedPoint.a h2.symm

set_option backward.isDefEq.respectTransparency false in
/-- The object identification for the forward construction. -/
lemma repG_obj_eq {T : Over S} (φ : T ⟶ Over.mk ((RepG.homEquiv (𝟙 Ŷ)).a)) :
    T = Over.mk ((RepG.homEquiv φ.left).a) := by
  have h1 : (RepG.homEquiv φ.left).a = T.hom := by
    rw [repG_eq RepG φ.left]
    exact Over.w φ
  exact (CostructuredArrow.eq_mk T).trans (congrArg Over.mk h1.symm)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- transport-heavy defeq checks through `Over.mk`/`overRes` identifications
variable (F Y R) in
include hF hU in
/-- **The representing object over `S`**: transport of the absolute
representation of the glued functor to a representation of `F` by the
`S`-scheme `(Ŷ, â)`. -/
noncomputable def overRepresentableBy :
    F.RepresentableBy (Over.mk ((RepG.homEquiv (𝟙 Ŷ)).a)) where
  homEquiv {T} :=
    { toFun := fun φ => F.map (eqToHom (repG_obj_eq RepG φ)).op
        ((RepG.homEquiv φ.left).sect hF hU)
      invFun := fun x => Over.homMk
        (RepG.homEquiv.symm (ofSect Y R T.hom
          (F.map (eqToHom (CostructuredArrow.eq_mk T).symm).op x)))
        (symm_ofSect_w RepG x)
      left_inv := fun φ => by
        apply CommaMorphism.ext
        swap
        · apply Subsingleton.elim
        change RepG.homEquiv.symm (ofSect Y R T.hom _) = φ.left
        apply RepG.homEquiv.injective
        rw [Equiv.apply_symm_apply]
        refine Eq.trans ?_ (ofSect_sect hF hU (RepG.homEquiv φ.left))
        refine Eq.trans (congrArg (ofSect Y R T.hom)
          (map_eqToHom_trans _ _ _)) ?_
        refine Eq.trans ?_ (ofSect_congr (c := T.hom)
          (d := (RepG.homEquiv φ.left).a) (by
            rw [repG_eq RepG φ.left]
            exact (Over.w φ).symm) ((RepG.homEquiv φ.left).sect hF hU))
        rfl
      right_inv := fun x => by
        have hres := Equiv.apply_symm_apply RepG.homEquiv
          (ofSect Y R T.hom
            (F.map (eqToHom (CostructuredArrow.eq_mk T).symm).op x))
        refine Eq.trans (congrArg
          (fun z => F.map (eqToHom (repG_obj_eq RepG _)).op z)
          ((sect_congr hF hU hres).trans
            (congrArg (fun z => F.map (eqToHom (congrArg
              (fun p => Over.mk p.a) hres)).op z)
              (sect_ofSect hF hU T.hom _)))) ?_
        refine Eq.trans (map_eqToHom_trans _ _ _) ?_
        refine Eq.trans (map_eqToHom_trans _ _ _) ?_
        exact map_id_apply x }
  homEquiv_comp {T T'} f g := by
    change F.map (eqToHom (repG_obj_eq RepG (f ≫ g))).op
        ((RepG.homEquiv (f ≫ g).left).sect hF hU)
      = F.map f.op (F.map (eqToHom (repG_obj_eq RepG g)).op
        ((RepG.homEquiv g.left).sect hF hU))
    have hcomp : RepG.homEquiv (f ≫ g).left
        = GluedPoint.res R f.left (RepG.homEquiv g.left) := by
      refine (repG_eq RepG (f ≫ g).left).trans ?_
      refine Eq.trans ?_
        (congrArg (GluedPoint.res R f.left) (repG_eq RepG g.left)).symm
      exact (res_res hF hU f.left g.left (RepG.homEquiv (𝟙 Ŷ))).symm
    have hOb₁ : T = Over.mk ((GluedPoint.res R f.left
        (RepG.homEquiv g.left)).a) :=
      (repG_obj_eq RepG (f ≫ g)).trans
        (congrArg (fun p => Over.mk p.a) hcomp)
    have hsq : f ≫ eqToHom (repG_obj_eq RepG g)
        = eqToHom hOb₁ ≫ resSecHom f.left ((RepG.homEquiv g.left).a) :=
      homMk_eqToHom_square hOb₁ (repG_obj_eq RepG g) f
        (resSecHom f.left ((RepG.homEquiv g.left).a))
        (heq_of_eq (by simp only [resSecHom, Over.homMk_left]))
    calc F.map (eqToHom (repG_obj_eq RepG (f ≫ g))).op
          ((RepG.homEquiv (f ≫ g).left).sect hF hU)
        = F.map (eqToHom (repG_obj_eq RepG (f ≫ g))).op
            (F.map (eqToHom (congrArg (fun p => Over.mk p.a) hcomp)).op
              ((GluedPoint.res R f.left (RepG.homEquiv g.left)).sect hF hU)) :=
          congrArg (fun z => F.map (eqToHom
            (repG_obj_eq RepG (f ≫ g))).op z) (sect_congr hF hU hcomp)
      _ = F.map (eqToHom hOb₁).op
            ((GluedPoint.res R f.left (RepG.homEquiv g.left)).sect hF hU) :=
          map_eqToHom_trans _ _ _
      _ = F.map (eqToHom hOb₁).op
            (F.map (resSecHom f.left ((RepG.homEquiv g.left).a)).op
              ((RepG.homEquiv g.left).sect hF hU)) :=
          congrArg (fun z => F.map (eqToHom hOb₁).op z)
            (sect_res hF hU f.left (RepG.homEquiv g.left))
      _ = F.map (eqToHom hOb₁ ≫
            resSecHom f.left ((RepG.homEquiv g.left).a)).op
            ((RepG.homEquiv g.left).sect hF hU) := map_map _ _ _
      _ = F.map (f ≫ eqToHom (repG_obj_eq RepG g)).op
            ((RepG.homEquiv g.left).sect hF hU) := (map_congr hsq _).symm
      _ = F.map f.op (F.map (eqToHom (repG_obj_eq RepG g)).op
            ((RepG.homEquiv g.left).sect hF hU)) := (map_map _ _ _).symm

end Assemble

end ZariskiDescent

/-! ## §9. Zariski descent of representability -/

set_option backward.isDefEq.respectTransparency false in
/-- **Zariski descent of representability** (EGA 0_I 4.5.4; cf. Stacks 01JJ):
a Zariski-local presheaf `F` on `Sch/S` that is representable over every
member of an open cover of `S` is representable by an `S`-scheme.

The proof glues the local representing objects through mathlib's
`AlgebraicGeometry.Scheme.LocalRepresentability` (Stacks 01JJ), applied to
the small total functor `ZariskiDescent.gluedFunctor` of `F`. -/
theorem representable_of_openCover {S : Scheme.{0}} (F : (Over S)ᵒᵖ ⥤ Type 1)
    (hF : IsZariskiSheafOver F) {ι : Type} (U : ι → S.Opens)
    (hU : ⨆ i, U i = ⊤)
    (hloc : ∀ i, ∃ Y : Over (U i).toScheme,
      Nonempty (((Over.map (U i).ι).op ⋙ F).RepresentableBy Y)) :
    ∃ Y : Over S, Nonempty (F.RepresentableBy Y) := by
  choose Y hY using hloc
  have R : ∀ i, ((Over.map (U i).ι).op ⋙ F).RepresentableBy (Y i) :=
    fun i => (hY i).some
  haveI := ZariskiDescent.isLocallySurjective_chart hF hU (Y := Y) (R := R)
  have hf : ∀ i, IsOpenImmersion.presheaf
      (ZariskiDescent.chart F Y R hF hU i) :=
    ZariskiDescent.chart_presheaf hF hU
  let Fsheaf : Sheaf Scheme.zariskiTopology (Type 0) :=
    ⟨ZariskiDescent.gluedFunctor F Y R,
      (isSheaf_iff_isSheaf_of_type _ _).mpr
        (ZariskiDescent.isSheaf_gluedFunctor hF hU)⟩
  have RepG : (ZariskiDescent.gluedFunctor F Y R).RepresentableBy
      (Scheme.LocalRepresentability.glueData hf).glued :=
    Scheme.LocalRepresentability.representableBy (F := Fsheaf) hf
  exact ⟨Over.mk ((RepG.homEquiv (𝟙 _)).a),
    ⟨ZariskiDescent.overRepresentableBy F Y R hF hU RepG⟩⟩

end Scheme

end AlgebraicGeometry
