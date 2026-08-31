/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Divisor

/-!
# The sheaf `𝒪(D)` associated to a Weil divisor on a curve

For the curve bundle `X`, integral and smooth of relative dimension one over a field `K`, and a
Weil divisor `D : X.CurveDivisor`, this file constructs the sheaf of `K`-modules `𝒪(D)` whose
sections over an open `U` are the rational functions with poles bounded by `D` on `U`:

* `AlgebraicGeometry.Scheme.functionFieldOverAlgebraMap` / `functionFieldOverModule`: the
  `K`-structure on the function field `K(X)` through the structure morphism, mirroring
  `Scheme.residueOverAlgebraMap` (deliberately *not* a global instance).
* `AlgebraicGeometry.Scheme.divisorSections`: the `K`-submodule of `K(X)` of sections of `𝒪(D)`
  over `U`, and `Scheme.divisorSheaf`: the resulting sheaf of `K`-modules on the small Zariski
  site of `X`.
* `AlgebraicGeometry.Scheme.divisorSheafLE`: the monomorphism of sheaves `𝒪(D) ↪ 𝒪(D')` induced
  by `D ≤ D'`.
* `AlgebraicGeometry.Scheme.divisorSheafZeroIso`: the identification `𝒪(0) ≅ 𝒪_X` of the
  divisor sheaf of the zero divisor with the structure sheaf (as a sheaf of `K`-modules).

## Sign convention

For `g : K(X)` and a closed point `x`, "the pole order of `g` at `x` is bounded by `D x`" reads
`ord_x g ≤ ofAdd (D x)` in `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`: a uniformizer has valuation
`ofAdd (-1) < 1`, `g = 0` has valuation `0 = ⊥`, and at `D = 0` the bound is `≤ 1`, i.e. "`g`
lies in the valuation subring at every closed point", which is exactly the statement identifying
`𝒪(0)` with `𝒪_X`.

## The empty-open corner

The empty sieve covers `⊥` in `Opens.grothendieckTopology`, so a sheaf must have terminal (zero)
sections over `⊥`. The naive predicate "`∀ x ∈ U, ord_x g ≤ …`" is *vacuously* all of `K(X)` over
`⊥`, hence is *not* a sheaf. We therefore guard the definition: `divisorSections D U` is the naive
bounded submodule when `U` is nonempty and `⊥` (the zero submodule) when `U` is empty, sealed
behind `divisorSections_of_nonempty` / `divisorSections_of_empty`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The `K`-algebra structure map on the function field `K(X)` of a scheme over `Spec K`, through
the structure morphism: `K →+* Γ(X, ⊤) →+* K(X)` (the germ at the generic point of a global
section). Deliberately *not* a global `Algebra` instance, mirroring `Scheme.overModule`. -/
noncomputable def Scheme.functionFieldOverAlgebraMap (K : Type u) [Field K] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of K))] [IsIntegral X] : K →+* X.functionField :=
  (X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp (X.overAlgebraMap K ⊤)

/-- The `K`-module structure on the function field `K(X)`, by restriction of scalars along
`Scheme.functionFieldOverAlgebraMap`. Activate with `attribute [local instance]` where needed. -/
@[reducible] noncomputable def Scheme.functionFieldOverModule (K : Type u) [Field K]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] [IsIntegral X] :
    Module K X.functionField :=
  (Scheme.functionFieldOverAlgebraMap K X).toModule

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

namespace Scheme

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] in
lemma functionFieldOverModule_smul_def (r : K) (g : X.functionField) :
    r • g = Scheme.functionFieldOverAlgebraMap K X r * g := rfl

/-- **The order of an integral element is nonnegative.** The order valuation at a closed point of
the image in `K(X)` of any element of the stalk `𝒪_{X,x}` is `≤ 1`: integral elements have no
pole. This is the heart of the `𝒪(D)`-submodule property and of the `𝒪(0) ≅ 𝒪_X` identification. -/
lemma ord_algebraMap_stalk_le_one {x : X} (hx : x ≠ genericPoint X)
    (y : X.presheaf.stalk x) :
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx
        (algebraMap (X.presheaf.stalk x) X.functionField y) ≤ 1 := by
  letI := isDiscreteValuationRing_stalk (X ↘ Spec (CommRingCat.of K)) hx
  letI := isDedekindDomain_stalk (X ↘ Spec (CommRingCat.of K)) hx
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ y

/-- **The `K`-structure map lands in every valuation subring.** The image of `r : K` in `K(X)`
is the germ at the generic point of a global section; its germ at any closed point `x` realises
it as an element of `𝒪_{X,x}`, hence it has no pole there: `ord_x (r · 1) ≤ 1`. -/
lemma ord_functionFieldOverAlgebraMap_le_one {x : X} (hx : x ≠ genericPoint X) (r : K) :
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (functionFieldOverAlgebraMap K X r) ≤ 1 := by
  set t : Γ(X, ⊤) := X.overAlgebraMap K ⊤ r with ht
  have hspec : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hcomp := X.presheaf.germ_stalkSpecializes (U := ⊤) (y := x) trivial hspec
  have happ := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) t
  rw [CommRingCat.hom_comp, RingHom.comp_apply] at happ
  have hrw : functionFieldOverAlgebraMap K X r
      = algebraMap (X.presheaf.stalk x) X.functionField
          ((X.presheaf.germ ⊤ x trivial).hom t) := happ.symm
  rw [hrw]
  exact ord_algebraMap_stalk_le_one K hx _

/-- The valuation upper bound imposed by a divisor `D` at a closed point `x`, in `ℤᵐ⁰`.
The pole order of `g` at `x` is bounded by `D` iff `ord_x g ≤ divisorBound D hx`. -/
noncomputable def divisorBound (D : X.CurveDivisor) {x : X} (hx : x ≠ genericPoint X) :
    WithZero (Multiplicative ℤ) :=
  letI D' : {x : X // x ≠ genericPoint X} →₀ ℤ := D
  ((Multiplicative.ofAdd (D' ⟨x, hx⟩) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))

@[simp] lemma divisorBound_zero {x : X} (hx : x ≠ genericPoint X) :
    divisorBound (0 : X.CurveDivisor) hx = 1 := by
  rw [divisorBound]; rfl

lemma divisorBound_mono {D D' : X.CurveDivisor} (h : D ≤ D') {x : X}
    (hx : x ≠ genericPoint X) : divisorBound D hx ≤ divisorBound D' hx := by
  simp only [divisorBound, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
  exact (Finsupp.le_def.mp h) ⟨x, hx⟩

/-- The **naive bounded submodule**: rational functions `g : K(X)` whose pole order at every
closed point of `U` is bounded by `D`. Over `⊥` this is (vacuously) all of `K(X)`; the
sheaf-correct `divisorSections` guards the empty open. -/
noncomputable def boundedSections (D : X.CurveDivisor) (U : X.Opens) :
    Submodule K X.functionField where
  carrier := {g | ∀ (x : X) (hx : x ≠ genericPoint X), x ∈ U →
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g ≤ divisorBound D hx}
  zero_mem' := fun _ _ _ => by rw [map_zero]; exact zero_le
  add_mem' := fun {g₁ g₂} h₁ h₂ x hx hxU =>
    le_trans (Valuation.map_add _ g₁ g₂) (max_le (h₁ x hx hxU) (h₂ x hx hxU))
  smul_mem' := fun r g hg x hx hxU => by
    rw [functionFieldOverModule_smul_def, map_mul]
    calc Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (functionFieldOverAlgebraMap K X r)
            * Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g
        ≤ 1 * Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g := by
          gcongr; exact ord_functionFieldOverAlgebraMap_le_one K hx r
      _ = Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g := one_mul _
      _ ≤ _ := hg x hx hxU

lemma mem_boundedSections {D : X.CurveDivisor} {U : X.Opens} {g : X.functionField} :
    g ∈ boundedSections K D U ↔ ∀ (x : X) (hx : x ≠ genericPoint X), x ∈ U →
      Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g ≤ divisorBound D hx :=
  Iff.rfl

/-- Sections over a larger open satisfy more constraints: `boundedSections` is antitone in `U`. -/
lemma boundedSections_le_of_le {D : X.CurveDivisor} {U V : X.Opens} (h : V ≤ U) :
    boundedSections K D U ≤ boundedSections K D V :=
  fun _ hg x hx hxV => hg x hx (h hxV)

/-- `boundedSections` is monotone in the divisor. -/
lemma boundedSections_mono {D D' : X.CurveDivisor} (h : D ≤ D') (U : X.Opens) :
    boundedSections K D U ≤ boundedSections K D' U :=
  fun _ hg x hx hxU => le_trans (hg x hx hxU) (divisorBound_mono h hx)

/-- **Sections of `𝒪(D)` over `U`.** The bounded submodule for nonempty `U`, and the zero
submodule over the empty open — the guard forced by the sheaf condition at `⊥` (see the module
docstring). -/
noncomputable def divisorSections (D : X.CurveDivisor) (U : X.Opens) :
    Submodule K X.functionField :=
  ⨆ (_ : (U : Set X).Nonempty), boundedSections K D U

lemma divisorSections_of_nonempty {D : X.CurveDivisor} {U : X.Opens}
    (hU : (U : Set X).Nonempty) : divisorSections K D U = boundedSections K D U :=
  iSup_pos hU

@[simp] lemma divisorSections_of_empty {D : X.CurveDivisor} {U : X.Opens}
    (hU : ¬ (U : Set X).Nonempty) : divisorSections K D U = ⊥ :=
  iSup_neg hU

lemma divisorSections_subsingleton_of_empty {D : X.CurveDivisor} {U : X.Opens}
    (hU : ¬ (U : Set X).Nonempty) : Subsingleton (divisorSections K D U) := by
  rw [divisorSections_of_empty K hU]; infer_instance

/-- Membership in `𝒪(D)(U)` for a nonempty open: bounded pole orders at every closed point. -/
lemma mem_divisorSections_of_nonempty {D : X.CurveDivisor} {U : X.Opens}
    (hU : (U : Set X).Nonempty) {g : X.functionField} :
    g ∈ divisorSections K D U ↔ ∀ (x : X) (hx : x ≠ genericPoint X), x ∈ U →
      Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g ≤ divisorBound D hx := by
  rw [divisorSections_of_nonempty K hU]; exact mem_boundedSections K

/-- Sections over a larger open satisfy more constraints: `divisorSections` is antitone in `U`
(for nonempty targets). -/
lemma divisorSections_antitone {D : X.CurveDivisor} {U V : X.Opens} (h : V ≤ U)
    (hV : (V : Set X).Nonempty) : divisorSections K D U ≤ divisorSections K D V := by
  rw [divisorSections_of_nonempty K (hV.mono h), divisorSections_of_nonempty K hV]
  exact boundedSections_le_of_le K h

open Classical in
/-- **Restriction of `𝒪(D)`-sections** along `V ≤ U`: the inclusion when `V` is nonempty
(restriction only relaxes the pole bounds), the zero map into the terminal sections when `V`
is empty. -/
noncomputable def divisorSectionsRes (D : X.CurveDivisor) {U V : X.Opens} (h : V ≤ U) :
    divisorSections K D U →ₗ[K] divisorSections K D V :=
  if hV : (V : Set X).Nonempty then Submodule.inclusion (divisorSections_antitone K h hV) else 0

lemma divisorSectionsRes_coe {D : X.CurveDivisor} {U V : X.Opens} (h : V ≤ U)
    (hV : (V : Set X).Nonempty) (s : divisorSections K D U) :
    ((divisorSectionsRes K D h s : divisorSections K D V) : X.functionField)
      = (s : X.functionField) := by
  classical rw [divisorSectionsRes, dif_pos hV, Submodule.coe_inclusion]

lemma divisorSectionsRes_id {D : X.CurveDivisor} {U : X.Opens} (h : U ≤ U) :
    divisorSectionsRes K D h = LinearMap.id := by
  apply LinearMap.ext; intro s
  by_cases hU : (U : Set X).Nonempty
  · exact Subtype.ext (divisorSectionsRes_coe K h hU s)
  · haveI := divisorSections_subsingleton_of_empty K (D := D) hU
    exact Subsingleton.elim _ _

lemma divisorSectionsRes_comp {D : X.CurveDivisor} {U V W : X.Opens} (hWV : W ≤ V) (hVU : V ≤ U) :
    divisorSectionsRes K D (le_trans hWV hVU)
      = (divisorSectionsRes K D hWV).comp (divisorSectionsRes K D hVU) := by
  apply LinearMap.ext; intro s
  by_cases hW : (W : Set X).Nonempty
  · have hV : (V : Set X).Nonempty := hW.mono hWV
    apply Subtype.ext
    rw [LinearMap.comp_apply, divisorSectionsRes_coe K (le_trans hWV hVU) hW,
      divisorSectionsRes_coe K hWV hW, divisorSectionsRes_coe K hVU hV]
  · haveI := divisorSections_subsingleton_of_empty K (D := D) hW
    exact Subsingleton.elim _ _

/-- The presheaf `U ↦ 𝒪(D)(U)` of `K`-modules on the small Zariski site of `X`. -/
noncomputable def divisorPresheaf (D : X.CurveDivisor) : (X.Opens)ᵒᵖ ⥤ ModuleCat.{u} K where
  obj U := ModuleCat.of K (divisorSections K D U.unop)
  map {U V} i := ModuleCat.ofHom (divisorSectionsRes K D (leOfHom i.unop))
  map_id U := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id, divisorSectionsRes_id K (leOfHom (𝟙 U.unop))]
  map_comp {U V W} i j := by
    apply ModuleCat.hom_ext
    have hcomp : divisorSectionsRes K D (leOfHom (i ≫ j).unop) =
          (divisorSectionsRes K D (leOfHom j.unop)).comp
            (divisorSectionsRes K D (leOfHom i.unop)) :=
      divisorSectionsRes_comp K (leOfHom j.unop) (leOfHom i.unop)
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, hcomp]

/-- The underlying rational function of a section of the presheaf `𝒪(D)`. -/
def divisorVal {D : X.CurveDivisor} {W : X.Opens}
    (s : (divisorPresheaf K D).obj (op W)) : X.functionField :=
  have s' : divisorSections K D W := s
  (s' : X.functionField)

lemma divisorVal_coe {D : X.CurveDivisor} {W : X.Opens} (s : divisorSections K D W) :
    divisorVal K (D := D) (W := W) s = (s : X.functionField) := rfl

lemma divisorVal_mem {D : X.CurveDivisor} {W : X.Opens}
    (s : (divisorPresheaf K D).obj (op W)) : divisorVal K s ∈ divisorSections K D W :=
  Subtype.property s

/-- The underlying function-field value of a restricted section (nonempty target) is unchanged. -/
lemma divisorPresheaf_map_val {D : X.CurveDivisor} {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V)
    (hV : (V.unop : Set X).Nonempty) (s : (divisorPresheaf K D).obj U) :
    divisorVal K ((divisorPresheaf K D).map i s) = divisorVal K s :=
  divisorSectionsRes_coe K (leOfHom i.unop) hV s

/-- Two sections of `𝒪(D)` over the same open agreeing as rational functions are equal. -/
lemma divisorSection_ext {D : X.CurveDivisor} {W : X.Opens}
    {a b : (divisorPresheaf K D).obj (op W)} (h : divisorVal K a = divisorVal K b) : a = b :=
  Subtype.ext h

/-- Sections of `𝒪(D)` over an empty open form a subsingleton. -/
lemma divisorPresheaf_obj_subsingleton {D : X.CurveDivisor} {W : X.Opens}
    (hW : ¬ (W : Set X).Nonempty) :
    Subsingleton (ToType ((divisorPresheaf K D).obj (op W))) :=
  divisorSections_subsingleton_of_empty K hW

/-- **Two nonempty opens of an irreducible space meet.** -/
lemma opens_inf_nonempty {U V : X.Opens} (hU : (U : Set X).Nonempty)
    (hV : (V : Set X).Nonempty) : (↑(U ⊓ V) : Set X).Nonempty := by
  rw [Opens.coe_inf]
  have h := PreirreducibleSpace.isPreirreducible_univ (↑U : Set X) (↑V : Set X) U.isOpen V.isOpen
    (by simpa using hU) (by simpa using hV)
  simpa using h

/-- **The presheaf `𝒪(D)` is a sheaf.** On the irreducible space `X` a compatible family of
sections over a cover shares a single underlying rational function (any two nonempty members
agree, since their opens meet), which then satisfies the pole bound at every point of the union;
over the empty open all sections are terminal. -/
lemma isSheaf_divisorPresheaf (D : X.CurveDivisor) :
    Presheaf.IsSheaf (Opens.grothendieckTopology (X : TopCat)) (divisorPresheaf K D) := by
  have hsh : TopCat.Presheaf.IsSheaf (divisorPresheaf K D) := by
    rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
    intro ι U sf hcompat
    have hval : ∀ i j, (U i : Set X).Nonempty → (U j : Set X).Nonempty →
        divisorVal K (sf i) = divisorVal K (sf j) := by
      intro i j hi hj
      have hmeet := opens_inf_nonempty hi hj
      have e1 := divisorPresheaf_map_val K (Opens.infLELeft (U i) (U j)).op hmeet (sf i)
      have e2 := divisorPresheaf_map_val K (Opens.infLERight (U i) (U j)).op hmeet (sf j)
      rw [← e1, ← e2, hcompat i j]
    by_cases hsup : (↑(iSup U) : Set X).Nonempty
    · obtain ⟨i₀, hi₀⟩ : ∃ i₀, (U i₀ : Set X).Nonempty := by
        rw [Opens.coe_iSup] at hsup
        obtain ⟨x, hx⟩ := hsup
        obtain ⟨i₀, hxi⟩ := Set.mem_iUnion.mp hx
        exact ⟨i₀, ⟨x, hxi⟩⟩
      have hg₀ : divisorVal K (sf i₀) ∈ divisorSections K D (iSup U) := by
        rw [mem_divisorSections_of_nonempty K hsup]
        intro x hx hxmem
        obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hxmem
        have hjne : (U j : Set X).Nonempty := ⟨x, hxj⟩
        rw [hval i₀ j hi₀ hjne]
        exact (mem_divisorSections_of_nonempty K hjne).mp (divisorVal_mem K (sf j)) x hx hxj
      refine ⟨⟨_, hg₀⟩, ?_, ?_⟩
      · intro i
        by_cases hUi : (U i : Set X).Nonempty
        · apply divisorSection_ext K
          rw [divisorPresheaf_map_val K (Opens.leSupr U i).op hUi]
          exact hval i₀ i hi₀ hUi
        · haveI := divisorPresheaf_obj_subsingleton K (D := D) hUi
          exact Subsingleton.elim _ _
      · intro y hy
        refine divisorSection_ext K ?_
        change divisorVal K y = divisorVal K (sf i₀)
        rw [← divisorPresheaf_map_val K (Opens.leSupr U i₀).op hi₀ y, hy i₀]
    · refine ⟨0, ?_, ?_⟩
      · intro i
        have hUi : ¬ (U i : Set X).Nonempty := fun hne => hsup (hne.mono (le_iSup U i))
        haveI := divisorPresheaf_obj_subsingleton K (D := D) hUi
        exact Subsingleton.elim _ _
      · intro y _
        haveI := divisorPresheaf_obj_subsingleton K (D := D) hsup
        exact Subsingleton.elim _ _
  exact hsh

/-- **The sheaf `𝒪(D)`** of `K`-modules on the small Zariski site of `X`: rational functions with
poles bounded by `D`. -/
noncomputable def divisorSheaf (D : X.CurveDivisor) :
    Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} K) :=
  ⟨divisorPresheaf K D, isSheaf_divisorPresheaf K D⟩

@[simp] lemma divisorSheaf_obj (D : X.CurveDivisor) (U : X.Opens) :
    (divisorSheaf K D).obj.obj (op U) = ModuleCat.of K (divisorSections K D U) := rfl

/-- `𝒪(D)(U) ⊆ 𝒪(D')(U)` when `D ≤ D'`: a larger divisor allows larger pole orders. -/
lemma divisorSections_mono {D D' : X.CurveDivisor} (h : D ≤ D') (U : X.Opens) :
    divisorSections K D U ≤ divisorSections K D' U :=
  iSup_mono (fun _ => boundedSections_mono K h U)

/-- The presheaf inclusion `𝒪(D) ↪ 𝒪(D')` induced by `D ≤ D'`. -/
noncomputable def divisorPresheafLE {D D' : X.CurveDivisor} (h : D ≤ D') :
    divisorPresheaf K D ⟶ divisorPresheaf K D' where
  app U := ModuleCat.ofHom (Submodule.inclusion (divisorSections_mono K h U.unop))
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    by_cases hV : (V.unop : Set X).Nonempty
    · apply Subtype.ext
      change ((Submodule.inclusion (divisorSections_mono K h V.unop))
          (divisorSectionsRes K D (leOfHom i.unop) s) : X.functionField)
        = (divisorSectionsRes K D' (leOfHom i.unop)
          (Submodule.inclusion (divisorSections_mono K h U.unop) s) : X.functionField)
      rw [Submodule.coe_inclusion, divisorSectionsRes_coe K (leOfHom i.unop) hV,
        divisorSectionsRes_coe K (leOfHom i.unop) hV, Submodule.coe_inclusion]
    · haveI := divisorPresheaf_obj_subsingleton K (D := D') (W := V.unop) hV
      exact Subsingleton.elim _ _

/-- **The monomorphism `𝒪(D) ↪ 𝒪(D')`** of sheaves induced by `D ≤ D'`. -/
noncomputable def divisorSheafLE {D D' : X.CurveDivisor} (h : D ≤ D') :
    divisorSheaf K D ⟶ divisorSheaf K D' :=
  (fullyFaithfulSheafToPresheaf _ _).preimage (divisorPresheafLE K h)

instance divisorSheafLE_mono {D D' : X.CurveDivisor} (h : D ≤ D') :
    Mono (divisorSheafLE K h) := by
  haveI happ : ∀ U, Mono ((divisorPresheafLE K h).app U) := fun U => by
    rw [ModuleCat.mono_iff_injective]
    exact Submodule.inclusion_injective (divisorSections_mono K h U.unop)
  haveI hpre : Mono (divisorPresheafLE K h) := NatTrans.mono_of_mono_app _
  have hmap : (sheafToPresheaf _ _).map (divisorSheafLE K h) = divisorPresheafLE K h :=
    (fullyFaithfulSheafToPresheaf _ _).map_preimage
      (X := divisorSheaf K D) (Y := divisorSheaf K D') (divisorPresheafLE K h)
  apply (sheafToPresheaf _ _).mono_of_mono_map
  rw [hmap]
  exact hpre

/-- **Order `≤ 1` means integral at `x`.** A rational function with nonnegative order at a closed
point `x` lies in the image of the stalk `𝒪_{X,x}`: the DVR has a unique height-one prime (its
maximal ideal), so the single bound `ord_x g ≤ 1` controls every adic valuation. -/
lemma exists_stalk_of_ord_le_one {x : X} (hx : x ≠ genericPoint X) {g : X.functionField}
    (hg : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g ≤ 1) :
    ∃ y : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField y = g := by
  letI := isDiscreteValuationRing_stalk (X ↘ Spec (CommRingCat.of K)) hx
  letI := isDedekindDomain_stalk (X ↘ Spec (CommRingCat.of K)) hx
  set v₀ : IsDedekindDomain.HeightOneSpectrum (X.presheaf.stalk x) :=
    ⟨IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).isPrime,
      IsDiscreteValuationRing.not_a_field (X.presheaf.stalk x)⟩ with hv0
  have hord : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx = v₀.valuation X.functionField := rfl
  have hall : ∀ v : IsDedekindDomain.HeightOneSpectrum (X.presheaf.stalk x),
      v.valuation X.functionField g ≤ 1 := by
    intro v
    have hvv : v = v₀ :=
      IsDedekindDomain.HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal v.isMaximal)
    rw [hvv, ← hord]; exact hg
  exact RingHom.mem_range.mp
    (IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one X.functionField g hall)

end Scheme

end AlgebraicGeometry
