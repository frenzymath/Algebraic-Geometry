/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.LocalizationCocycle
import AlgebraicJacobian.Descent.UnitDescentBaseChange

/-!
# Base change of a finite localization cover cocycle along `A → A'`

Continuation of `AlgebraicJacobian.Algebra.LocalizationCocycle`: for a ring map `A → A'` and
a finite family `f : ι → A`, the pushed family `f' i := algebraMap A A' (f i)` is a finite
family in `A'`.  Fixing `A'`-side localization models `S' i = A'[1/f' i]`,
`T' i j = A'[1/(f' i · f' j)]`, `W' i j k = A'[1/(f' i · f' j · f' k)]` — each also carrying
the `A`-algebra structure of the tower `A → A' → ·` — the canonical `A`-algebra maps
`mapAway i : S i →ₐ[A] S' i`, `mapOverlap i j : T i j →ₐ[A] T' i j`,
`mapTriple i j k : W i j k →ₐ[A] W' i j k` (existing because `f i` etc. become units of the
primed models) transport the whole Čech picture:

* `IsCoverCocycle.baseChange` — a cover cocycle `γ` for `f` pushes to a cover cocycle for
  `f'`.  Every naturality square between the restriction maps commutes by `Subsingleton` of
  `A`-algebra maps out of a localization of `A` (`IsLocalization.algHom_subsingleton`).
* `cocycleUnit_baseChange` — **the keystone**: the descent unit of the pushed cocycle is the
  image of `cocycleUnit f S T γ` under `Module.tensorSqBaseChange` followed by
  `Algebra.TensorProduct.map j j`, where `j : A' ⊗[A] (∏ i, S i) →ₐ[A'] ∏ i, S' i` is the
  base-change map of cover algebras.  Proved by the pi-ext principle
  (`AlgHom.ext_of_isLocalization_pi`) on the coordinate idempotents.
* `span_range_algebraMap_eq_top`, `faithfullyFlat_tensor` — the faithful-flatness bookkeeping
  needed to chain the Picard-class naturality (`Module.IsDescentCocycle.picClass_baseChange`
  and `Module.IsDescentCocycle.picClass_map`).
* `pic_baseChange` — the composite corollary consumed by the scheme layer: the Picard class
  of the descended module of the pushed cocycle is the image under `CommRing.Pic.mapAlgebra`
  of the Picard class of the original.
-/

universe u

open TensorProduct

-- The tower setup `A → A' → S'/T'/W'` makes many single-/double-/triple-overlap lemmas
-- independent of the finiteness of `ι`; those finiteness hypotheses are genuinely needed only
-- where the pi-ext principle over the finite index set is invoked (the keystone).
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace IsLocalization.AwayCover

variable {A : Type u} [CommRing A] (A' : Type u) [CommRing A'] [Algebra A A']
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (f : ι → A)
variable (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
  [∀ i, IsLocalization.Away (f i) (S i)]
variable (S' : ι → Type u) [∀ i, CommRing (S' i)] [∀ i, Algebra A' (S' i)]
  [∀ i, Algebra A (S' i)] [∀ i, IsScalarTower A A' (S' i)]
  [∀ i, IsLocalization.Away (algebraMap A A' (f i)) (S' i)]
variable (T : ι → ι → Type u) [∀ i j, CommRing (T i j)] [∀ i j, Algebra A (T i j)]
  [∀ i j, IsLocalization.Away (f i * f j) (T i j)]
variable (T' : ι → ι → Type u) [∀ i j, CommRing (T' i j)] [∀ i j, Algebra A' (T' i j)]
  [∀ i j, Algebra A (T' i j)] [∀ i j, IsScalarTower A A' (T' i j)]
  [∀ i j, IsLocalization.Away (algebraMap A A' (f i) * algebraMap A A' (f j)) (T' i j)]
variable (W : ι → ι → ι → Type u) [∀ i j k, CommRing (W i j k)] [∀ i j k, Algebra A (W i j k)]
  [∀ i j k, IsLocalization.Away (f i * (f j * f k)) (W i j k)]
variable (W' : ι → ι → ι → Type u) [∀ i j k, CommRing (W' i j k)] [∀ i j k, Algebra A' (W' i j k)]
  [∀ i j k, Algebra A (W' i j k)] [∀ i j k, IsScalarTower A A' (W' i j k)]
  [∀ i j k, IsLocalization.Away
    (algebraMap A A' (f i) * (algebraMap A A' (f j) * algebraMap A A' (f k))) (W' i j k)]

/-! ## The canonical base-change maps between localization models -/

/-- The canonical `A`-algebra map `S i = A[1/f i] →ₐ[A] S' i = A'[1/f' i]`: `f i` becomes a
unit of `S' i` through the tower `A → A' → S' i`. -/
noncomputable def mapAway (i : ι) : S i →ₐ[A] S' i :=
  IsLocalization.Away.algHomOfIsUnit (S := S i) (S' i) (f i) <| by
    rw [IsScalarTower.algebraMap_apply A A' (S' i)]
    exact IsLocalization.Away.algebraMap_isUnit (S := S' i) (algebraMap A A' (f i))

/-- The canonical `A`-algebra map on double overlaps `T i j →ₐ[A] T' i j`. -/
noncomputable def mapOverlap (i j : ι) : T i j →ₐ[A] T' i j :=
  IsLocalization.Away.algHomOfIsUnit (S := T i j) (T' i j) (f i * f j) <| by
    rw [IsScalarTower.algebraMap_apply A A' (T' i j), map_mul (algebraMap A A')]
    exact IsLocalization.Away.algebraMap_isUnit (S := T' i j)
      (algebraMap A A' (f i) * algebraMap A A' (f j))

/-- The canonical `A`-algebra map on triple overlaps `W i j k →ₐ[A] W' i j k`. -/
noncomputable def mapTriple (i j k : ι) : W i j k →ₐ[A] W' i j k :=
  IsLocalization.Away.algHomOfIsUnit (S := W i j k) (W' i j k) (f i * (f j * f k)) <| by
    rw [IsScalarTower.algebraMap_apply A A' (W' i j k), map_mul (algebraMap A A'),
      map_mul (algebraMap A A')]
    exact IsLocalization.Away.algebraMap_isUnit (S := W' i j k)
      (algebraMap A A' (f i) * (algebraMap A A' (f j) * algebraMap A A' (f k)))

/-! ## Naturality of the restriction maps under base change

Each square commutes because both composites are `A`-algebra maps out of a localization of
`A`, hence equal by `IsLocalization.algHom_subsingleton`. -/

/-- Base-change naturality of the diagonal identification. -/
lemma diag_naturality_apply (i : ι) (x : T i i) :
    diag (A := A') (fun i => algebraMap A A' (f i)) S' T' i (mapOverlap A' f T T' i i x)
      = mapAway A' f S S' i (diag f S T i x) := by
  have h : ((diag (A := A') (fun i => algebraMap A A' (f i)) S' T' i).restrictScalars A).comp
        (mapOverlap A' f T T' i i)
      = (mapAway A' f S S' i).comp (diag f S T i) :=
    Subsingleton.elim (h := IsLocalization.algHom_subsingleton (Submonoid.powers (f i * f i))) _ _
  exact DFunLike.congr_fun h x

/-- Base-change naturality of the `(2,3)`-face. -/
lemma face₂₃_naturality_apply (i j k : ι) (x : T j k) :
    face₂₃ (A := A') (fun i => algebraMap A A' (f i)) T' W' i j k (mapOverlap A' f T T' j k x)
      = mapTriple A' f W W' i j k (face₂₃ f T W i j k x) := by
  have h : ((face₂₃ (A := A') (fun i => algebraMap A A' (f i)) T' W' i j k).restrictScalars A).comp
        (mapOverlap A' f T T' j k)
      = (mapTriple A' f W W' i j k).comp (face₂₃ f T W i j k) :=
    Subsingleton.elim (h := IsLocalization.algHom_subsingleton (Submonoid.powers (f j * f k))) _ _
  exact DFunLike.congr_fun h x

/-- Base-change naturality of the `(1,2)`-face. -/
lemma face₁₂_naturality_apply (i j k : ι) (x : T i j) :
    face₁₂ (A := A') (fun i => algebraMap A A' (f i)) T' W' i j k (mapOverlap A' f T T' i j x)
      = mapTriple A' f W W' i j k (face₁₂ f T W i j k x) := by
  have h : ((face₁₂ (A := A') (fun i => algebraMap A A' (f i)) T' W' i j k).restrictScalars A).comp
        (mapOverlap A' f T T' i j)
      = (mapTriple A' f W W' i j k).comp (face₁₂ f T W i j k) :=
    Subsingleton.elim (h := IsLocalization.algHom_subsingleton (Submonoid.powers (f i * f j))) _ _
  exact DFunLike.congr_fun h x

/-- Base-change naturality of the `(1,3)`-face. -/
lemma face₁₃_naturality_apply (i j k : ι) (x : T i k) :
    face₁₃ (A := A') (fun i => algebraMap A A' (f i)) T' W' i j k (mapOverlap A' f T T' i k x)
      = mapTriple A' f W W' i j k (face₁₃ f T W i j k x) := by
  have h : ((face₁₃ (A := A') (fun i => algebraMap A A' (f i)) T' W' i j k).restrictScalars A).comp
        (mapOverlap A' f T T' i k)
      = (mapTriple A' f W W' i j k).comp (face₁₃ f T W i j k) :=
    Subsingleton.elim (h := IsLocalization.algHom_subsingleton (Submonoid.powers (f i * f k))) _ _
  exact DFunLike.congr_fun h x

/-! ## Base change of a cover cocycle -/

/-- **Base change of a Čech 1-cocycle of units.** Pushing a cover cocycle for `f` forward
along `A → A'` yields a cover cocycle for the pushed family `f' i = algebraMap A A' (f i)`. -/
theorem IsCoverCocycle.baseChange {γ : ∀ i j, (T i j)ˣ}
    (hγ : IsCoverCocycle (f := f) (S := S) (W := W) γ) :
    IsCoverCocycle (A := A') (f := fun i => algebraMap A A' (f i)) (S := S') (W := W')
      (fun i j => Units.map (mapOverlap A' f T T' i j).toRingHom.toMonoidHom (γ i j)) where
  diag_eq_one i := by
    change diag (A := A') (fun i => algebraMap A A' (f i)) S' T' i
        (mapOverlap A' f T T' i i (γ i i).val) = 1
    rw [diag_naturality_apply A' f S S' T T' i (γ i i).val, hγ.diag_eq_one i, map_one]
  cocycle i j k := by
    change face₂₃ (A := A') (fun i => algebraMap A A' (f i)) T' W' i j k
          (mapOverlap A' f T T' j k (γ j k).val)
        * face₁₂ (A := A') (fun i => algebraMap A A' (f i)) T' W' i j k
          (mapOverlap A' f T T' i j (γ i j).val)
      = face₁₃ (A := A') (fun i => algebraMap A A' (f i)) T' W' i j k
          (mapOverlap A' f T T' i k (γ i k).val)
    rw [face₂₃_naturality_apply A' f T T' W W' i j k (γ j k).val,
      face₁₂_naturality_apply A' f T T' W W' i j k (γ i j).val,
      face₁₃_naturality_apply A' f T T' W W' i j k (γ i k).val, ← map_mul, hγ.cocycle i j k]

/-! ## The base-change map of cover algebras and the keystone -/

/-- The componentwise base change of the cover algebra: `(∏ i, S i) →ₐ[A] (∏ i, S' i)`. -/
noncomputable def piMapAway : (∀ i, S i) →ₐ[A] ∀ i, S' i :=
  Pi.algHom _ _ fun i => (mapAway A' f S S' i).comp (Pi.evalAlgHom _ _ i)

lemma piMapAway_single (i : ι) :
    piMapAway A' f S S' (Pi.single i (1 : S i)) = Pi.single i (1 : S' i) := by
  funext k
  change mapAway A' f S S' k ((Pi.single i (1 : S i)) k) = (Pi.single i (1 : S' i)) k
  by_cases h : k = i
  · subst h; rw [Pi.single_eq_same, map_one, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, map_zero, Pi.single_eq_of_ne h]

/-- The canonical `A'`-algebra base-change map of cover algebras
`A' ⊗[A] (∏ i, S i) →ₐ[A'] ∏ i, S' i`, `a ⊗ s ↦ a • (mapAway · (s ·))`. -/
noncomputable def piBaseChangeLift : (A' ⊗[A] ∀ i, S i) →ₐ[A'] ∀ i, S' i :=
  Algebra.TensorProduct.lift (Algebra.ofId A' (∀ i, S' i)) (piMapAway A' f S S')
    fun _ _ => Commute.all _ _

lemma piBaseChangeLift_one_tmul (s : ∀ i, S i) :
    piBaseChangeLift A' f S S' ((1 : A') ⊗ₜ[A] s) = piMapAway A' f S S' s := by
  change Algebra.TensorProduct.lift (Algebra.ofId A' (∀ i, S' i)) (piMapAway A' f S S')
      (fun _ _ => Commute.all _ _) ((1 : A') ⊗ₜ[A] s) = piMapAway A' f S S' s
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]

/-- **The keystone**: the descent unit of the base-changed cocycle is the image of
`cocycleUnit f S T γ` under `Module.tensorSqBaseChange` followed by the tensor square of the
base-change map `piBaseChangeLift`. -/
theorem cocycleUnit_baseChange (γ : ∀ i j, (T i j)ˣ) :
    Units.map (Algebra.TensorProduct.map (piBaseChangeLift A' f S S')
        (piBaseChangeLift A' f S S')).toRingHom.toMonoidHom
      (Units.map (Module.tensorSqBaseChange A A' (∀ i, S i)).toRingHom.toMonoidHom
        (cocycleUnit f S T γ))
      = cocycleUnit (A := A') (fun i => algebraMap A A' (f i)) S' T'
        (fun i j => Units.map (mapOverlap A' f T T' i j).toRingHom.toMonoidHom (γ i j)) := by
  have key :
      ((piDoubleEquiv (A := A') (fun i => algebraMap A A' (f i)) S' T').toAlgHom.restrictScalars
          A).comp
        (((Algebra.TensorProduct.map (piBaseChangeLift A' f S S')
            (piBaseChangeLift A' f S S')).restrictScalars A).comp
          ((Module.tensorSqBaseChange A A' (∀ i, S i)).comp
            (piDoubleEquiv f S T).symm.toAlgHom))
      = Pi.algHom _ _ fun p : ι × ι =>
          (mapOverlap A' f T T' p.1 p.2).comp (Pi.evalAlgHom _ _ p) := by
    apply AlgHom.ext_of_isLocalization_pi
      (fun p : ι × ι => Submonoid.powers (f p.1 * f p.2))
    intro q
    obtain ⟨i, j⟩ := q
    change piDoubleEquiv (A := A') (fun i => algebraMap A A' (f i)) S' T'
        (Algebra.TensorProduct.map (piBaseChangeLift A' f S S') (piBaseChangeLift A' f S S')
          (Module.tensorSqBaseChange A A' (∀ i, S i)
            ((piDoubleEquiv f S T).symm (Pi.single (i, j) 1))))
      = fun p : ι × ι => mapOverlap A' f T T' p.1 p.2
          ((Pi.single (i, j) 1 : ∀ q : ι × ι, T q.1 q.2) p)
    rw [piDoubleEquiv_symm_single f S T i j, Module.tensorSqBaseChange_tmul,
      Algebra.TensorProduct.map_tmul, piBaseChangeLift_one_tmul, piBaseChangeLift_one_tmul,
      piMapAway_single, piMapAway_single,
      piDoubleEquiv_single_tmul_single (A := A') (fun i => algebraMap A A' (f i)) S' T' i j]
    funext p
    obtain ⟨a, b⟩ := p
    dsimp only
    by_cases ha : a = i
    · subst ha
      by_cases hb : b = j
      · subst hb
        rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
      · rw [Pi.single_eq_of_ne (fun hh => hb (congrArg Prod.snd hh)),
          Pi.single_eq_of_ne (fun hh => hb (congrArg Prod.snd hh)), map_zero]
    · rw [Pi.single_eq_of_ne (fun hh => ha (congrArg Prod.fst hh)),
        Pi.single_eq_of_ne (fun hh => ha (congrArg Prod.fst hh)), map_zero]
  apply Units.ext
  apply (piDoubleEquiv (A := A') (fun i => algebraMap A A' (f i)) S' T').injective
  rw [piDoubleEquiv_cocycleUnit_val (A := A') (fun i => algebraMap A A' (f i)) S' T']
  exact DFunLike.congr_fun key (piUnit T γ).val

/-! ## Faithful flatness bookkeeping -/

omit [Fintype ι] [DecidableEq ι] in
/-- A covering family stays covering after base change: `span (range f) = ⊤` implies
`span (range f') = ⊤` for `f' i = algebraMap A A' (f i)`. -/
theorem span_range_algebraMap_eq_top (hspan : Ideal.span (Set.range f) = ⊤) :
    Ideal.span (Set.range fun i => algebraMap A A' (f i)) = ⊤ := by
  have h : Ideal.span (Set.range fun i => algebraMap A A' (f i))
      = Ideal.map (algebraMap A A') (Ideal.span (Set.range f)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [h, hspan, Ideal.map_top]

/-- The base change `A' ⊗[A] (∏ i, S i)` of a covering product of localizations is a
faithfully flat `A'`-algebra: transport the faithful flatness of `∏ i, A' ⊗[A] S i` (each
factor an `A'[1/f' i]` localization) along `TensorProduct.piRight`. -/
theorem faithfullyFlat_tensor (hspan : Ideal.span (Set.range f) = ⊤) :
    Module.FaithfullyFlat A' (A' ⊗[A] ∀ i, S i) := by
  haveI : ∀ i, IsLocalization.Away (algebraMap A A' (f i)) (A' ⊗[A] S i) := fun _ => inferInstance
  haveI : Module.FaithfullyFlat A' (∀ i, A' ⊗[A] S i) :=
    Module.FaithfullyFlat.pi_of_span_eq_top (fun i => algebraMap A A' (f i))
      (span_range_algebraMap_eq_top A' f hspan)
  exact Module.FaithfullyFlat.of_linearEquiv _ _ (TensorProduct.piRight A A' A' S)

/-! ## Naturality of the descent Picard class in the base ring -/

/-- **Naturality of the descent Picard class under base change of the base ring.** The
Picard class of the descended module of the pushed cocycle is the image, under
`CommRing.Pic.mapAlgebra`, of the Picard class of the original. -/
theorem pic_baseChange [Module.FaithfullyFlat A (∀ i, S i)]
    [Module.FaithfullyFlat A' (∀ i, S' i)] {γ : ∀ i j, (T i j)ˣ}
    (hγ : IsCoverCocycle (f := f) (S := S) (W := W) γ)
    (hspan : Ideal.span (Set.range f) = ⊤) :
    (isDescentCocycle_cocycleUnit (A := A') (fun i => algebraMap A A' (f i)) S' T' W'
        (IsCoverCocycle.baseChange A' f S S' T T' W W' hγ)).picClass
      = CommRing.Pic.mapAlgebra A A' (isDescentCocycle_cocycleUnit f S T W hγ).picClass := by
  haveI : Module.FaithfullyFlat A' (A' ⊗[A] ∀ i, S i) := faithfullyFlat_tensor A' f S hspan
  set hu := isDescentCocycle_cocycleUnit f S T W hγ with hu_def
  have step1 : (isDescentCocycle_cocycleUnit (A := A') (fun i => algebraMap A A' (f i)) S' T' W'
        (IsCoverCocycle.baseChange A' f S S' T T' W W' hγ)).picClass
      = ((hu.baseChange (A' := A')).map (piBaseChangeLift A' f S S')).picClass :=
    Module.IsDescentCocycle.picClass_congr _ _
      (cocycleUnit_baseChange A' f S S' T T' γ).symm
  rw [step1,
    Module.IsDescentCocycle.picClass_map (piBaseChangeLift A' f S S') (hu.baseChange (A' := A'))]
  exact hu.picClass_baseChange

end IsLocalization.AwayCover
