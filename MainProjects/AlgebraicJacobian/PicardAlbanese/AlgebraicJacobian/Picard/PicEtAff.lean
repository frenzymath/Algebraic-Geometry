/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RelPicAlgebra
import AlgebraicJacobian.Algebra.EtaleCover

/-!
# The étale plus construction of the relative Picard functor on affine tests

For a curve `C` over `k` and an affine test scheme `Spec A`, the étale-sheafified relative
Picard group is computed by a *single* plus construction (the relative Picard presheaf is
étale-separated, by descent — proved separately): a class of the plus is represented by a
relative Picard class on an étale cover `Spec B → Spec A` equipped with a *descent
condition* — equal pullbacks along the two projections of the double cover
`Spec (B ⊗[A] B)` — and two representatives are identified when they agree on a common
refinement.

* `AlgebraicGeometry.descentClasses C E`: the subgroup of `relPic C (Spec B)` of classes
  satisfying the descent condition on the cover `E` with carrier `B`.
* `AlgebraicGeometry.descentMap C h`: transport of descent classes along a refinement map
  `h` of covers.
* `AlgebraicGeometry.relPicAlgMap_congr` (**the keystone**): a descent class restricts
  equally along any two `A`-algebra maps out of the cover carrier — the pair `(j₁, j₂)`
  factors through the double cover, where the descent condition kills the difference.
  Specialized to refinement maps as `AlgebraicGeometry.descentMap_congr`, this is what
  makes the colimit below independent of all choices; applied across base rings
  (`Picard/PicEtAffMap.lean`), it is also what makes the plus functorial in the test
  algebra.
* `AlgebraicGeometry.PicEtAff C A`: the one-step plus — descent classes on some cover,
  modulo agreement on a common refinement — with its `CommGroup` structure and the
  constructor/eliminator API `PicEtAff.mk`, `PicEtAff.ind`, `PicEtAff.mk_eq_mk_iff`,
  `PicEtAff.mk_descentMap`.
* `AlgebraicGeometry.PicEtAff.unit`: the unit `relPic C (Spec A) →* PicEtAff C A` of the
  plus construction — a class pulled back to the trivial cover with its tautological
  descent datum.

The functoriality of `PicEtAff` in `A` (restriction along test maps, via base change of
covers) and the comparison theorems (injectivity of the unit = separatedness; bijectivity
under a section = rigidification) are subsequent layers, consuming only this interface.
-/

set_option autoImplicit false

universe u

open CategoryTheory

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable {A : Type u} [CommRing A] [Algebra k A]

noncomputable section

/-! ## Descent classes on an étale cover -/

/-- The first coprojection from the carrier of a cover into its self-tensor product over
the base — the algebra face of the first projection of the double cover
`Spec (B ⊗[A] B) → Spec B` — as a `k`-algebra map. -/
def doubleInl (E : Algebra.EtaleCover A) :
    E.Carrier →ₐ[k] E.Carrier ⊗[A] E.Carrier :=
  Algebra.TensorProduct.includeLeft

/-- The second coprojection into the self-tensor product; see `doubleInl`. -/
def doubleInr (E : Algebra.EtaleCover A) :
    E.Carrier →ₐ[k] E.Carrier ⊗[A] E.Carrier :=
  (Algebra.TensorProduct.includeRight).restrictScalars k

/-- The subgroup of relative Picard classes on an étale cover of the test algebra
satisfying the descent condition: equal pullbacks along the two projections of the double
cover. -/
def descentClasses (E : Algebra.EtaleCover A) :
    Subgroup (relPic C (overSpec k E.Carrier)) :=
  MonoidHom.eqLocus
    (relPicAlgMap (B := E.Carrier ⊗[A] E.Carrier) C (doubleInl E))
    (relPicAlgMap (B := E.Carrier ⊗[A] E.Carrier) C (doubleInr E))

lemma mem_descentClasses_iff {E : Algebra.EtaleCover A}
    {x : relPic C (overSpec k E.Carrier)} :
    x ∈ descentClasses C E ↔
      relPicAlgMap (B := E.Carrier ⊗[A] E.Carrier) C (doubleInl E) x
        = relPicAlgMap (B := E.Carrier ⊗[A] E.Carrier) C (doubleInr E) x :=
  Iff.rfl

/-! ## Transport along refinement maps -/

private lemma doubleInl_comp {E F : Algebra.EtaleCover A} (h : E.Carrier →ₐ[A] F.Carrier) :
    (doubleInl F).comp (h.restrictScalars k)
      = ((Algebra.TensorProduct.map h h).restrictScalars k).comp (doubleInl E) := by
  ext x
  simp [doubleInl]

private lemma doubleInr_comp {E F : Algebra.EtaleCover A} (h : E.Carrier →ₐ[A] F.Carrier) :
    (doubleInr F).comp (h.restrictScalars k)
      = ((Algebra.TensorProduct.map h h).restrictScalars k).comp (doubleInr E) := by
  ext x
  simp [doubleInr]

/-- The descent condition is natural in the cover: pullback along a refinement map sends
descent classes to descent classes. -/
lemma relPicAlgMap_mem_descentClasses {E F : Algebra.EtaleCover A}
    (h : E.Carrier →ₐ[A] F.Carrier) {x : relPic C (overSpec k E.Carrier)}
    (hx : x ∈ descentClasses C E) :
    relPicAlgMap C (h.restrictScalars k) x ∈ descentClasses C F := by
  rw [mem_descentClasses_iff] at hx ⊢
  calc relPicAlgMap C (doubleInl F) (relPicAlgMap C (h.restrictScalars k) x)
      = relPicAlgMap C ((doubleInl F).comp (h.restrictScalars k)) x :=
        (relPicAlgMap_comp C _ _ x).symm
    _ = relPicAlgMap C (((Algebra.TensorProduct.map h h).restrictScalars k).comp
          (doubleInl E)) x := by rw [doubleInl_comp h]
    _ = relPicAlgMap C ((Algebra.TensorProduct.map h h).restrictScalars k)
          (relPicAlgMap C (doubleInl E) x) := relPicAlgMap_comp C _ _ x
    _ = relPicAlgMap C ((Algebra.TensorProduct.map h h).restrictScalars k)
          (relPicAlgMap C (doubleInr E) x) := by rw [hx]
    _ = relPicAlgMap C (((Algebra.TensorProduct.map h h).restrictScalars k).comp
          (doubleInr E)) x := (relPicAlgMap_comp C _ _ x).symm
    _ = relPicAlgMap C ((doubleInr F).comp (h.restrictScalars k)) x := by
        rw [doubleInr_comp h]
    _ = relPicAlgMap C (doubleInr F) (relPicAlgMap C (h.restrictScalars k) x) :=
        relPicAlgMap_comp C _ _ x

/-- Transport of descent classes along a refinement map of covers. -/
def descentMap {E F : Algebra.EtaleCover A} (h : E.Carrier →ₐ[A] F.Carrier) :
    descentClasses C E →* descentClasses C F :=
  ((relPicAlgMap C (h.restrictScalars k)).comp (descentClasses C E).subtype).codRestrict _
    fun x => relPicAlgMap_mem_descentClasses C h x.2

@[simp]
lemma descentMap_coe {E F : Algebra.EtaleCover A} (h : E.Carrier →ₐ[A] F.Carrier)
    (x : descentClasses C E) :
    (descentMap C h x : relPic C (overSpec k F.Carrier))
      = relPicAlgMap C (h.restrictScalars k) (x : relPic C (overSpec k E.Carrier)) :=
  rfl

@[simp]
lemma descentMap_id {E : Algebra.EtaleCover A} (x : descentClasses C E) :
    descentMap C (AlgHom.id A E.Carrier) x = x := by
  ext
  rw [descentMap_coe,
    show (AlgHom.id A E.Carrier).restrictScalars k = AlgHom.id k E.Carrier from rfl]
  exact relPicAlgMap_id C _

lemma descentMap_comp {E F G : Algebra.EtaleCover A} (h : E.Carrier →ₐ[A] F.Carrier)
    (h' : F.Carrier →ₐ[A] G.Carrier) (x : descentClasses C E) :
    descentMap C (h'.comp h) x = descentMap C h' (descentMap C h x) := by
  ext
  rw [descentMap_coe, descentMap_coe, descentMap_coe,
    show (h'.comp h).restrictScalars k
      = (h'.restrictScalars k).comp (h.restrictScalars k) from rfl]
  exact relPicAlgMap_comp C _ _ _

/-- **Generalized refinement-map independence**, the keystone of the plus construction:
a class satisfying the descent condition restricts equally along any two `A`-algebra maps
out of the cover carrier — into an arbitrary test algebra, not merely another cover.  The
pair `(j₁, j₂)` factors jointly through the double cover of the source, where the descent
condition identifies the two pullbacks. -/
theorem relPicAlgMap_congr {E : Algebra.EtaleCover A} {R : Type u} [CommRing R]
    [Algebra k R] [Algebra A R] [IsScalarTower k A R] (j₁ j₂ : E.Carrier →ₐ[A] R)
    {x : relPic C (overSpec k E.Carrier)} (hx : x ∈ descentClasses C E) :
    relPicAlgMap C (j₁.restrictScalars k) x = relPicAlgMap C (j₂.restrictScalars k) x := by
  set H : E.Carrier ⊗[A] E.Carrier →ₐ[A] R :=
    Algebra.TensorProduct.lift j₁ j₂ fun _ _ => Commute.all _ _ with hH
  have key₁ : (H.restrictScalars k).comp (doubleInl E) = j₁.restrictScalars k := by
    ext y
    simp [hH, doubleInl]
  have key₂ : (H.restrictScalars k).comp (doubleInr E) = j₂.restrictScalars k := by
    ext y
    simp [hH, doubleInr]
  calc relPicAlgMap C (j₁.restrictScalars k) x
      = relPicAlgMap C ((H.restrictScalars k).comp (doubleInl E)) x := by rw [key₁]
    _ = relPicAlgMap C (H.restrictScalars k) (relPicAlgMap C (doubleInl E) x) :=
        relPicAlgMap_comp C _ _ _
    _ = relPicAlgMap C (H.restrictScalars k) (relPicAlgMap C (doubleInr E) x) := by
        have hx' : relPicAlgMap (B := E.Carrier ⊗[A] E.Carrier) C (doubleInl E) x
            = relPicAlgMap (B := E.Carrier ⊗[A] E.Carrier) C (doubleInr E) x := hx
        rw [hx']
    _ = relPicAlgMap C ((H.restrictScalars k).comp (doubleInr E)) x :=
        (relPicAlgMap_comp C _ _ _).symm
    _ = relPicAlgMap C (j₂.restrictScalars k) x := by rw [key₂]

/-- **Refinement-map independence**: any two refinement maps between the same covers
transport descent classes identically — what makes the plus construction independent of
all choices. -/
theorem descentMap_congr {E F : Algebra.EtaleCover A}
    (h₁ h₂ : E.Carrier →ₐ[A] F.Carrier) (x : descentClasses C E) :
    descentMap C h₁ x = descentMap C h₂ x :=
  Subtype.ext (relPicAlgMap_congr C h₁ h₂ x.2)

/-! ## The plus construction -/

/-- Two descent-class representatives are identified when they agree after transport to a
common refinement.  By `descentMap_congr` the choice of transport maps is immaterial, so
the relation is an equivalence (directedness of covers gives transitivity). -/
instance picEtAffSetoid : Setoid (Σ E : Algebra.EtaleCover A, descentClasses C E) where
  r p q := ∃ (F : Algebra.EtaleCover A) (f : p.1.Carrier →ₐ[A] F.Carrier)
    (g : q.1.Carrier →ₐ[A] F.Carrier), descentMap C f p.2 = descentMap C g q.2
  iseqv := by
    constructor
    · exact fun p => ⟨p.1, AlgHom.id A _, AlgHom.id A _, rfl⟩
    · rintro p q ⟨F, f, g, hfg⟩
      exact ⟨F, g, f, hfg.symm⟩
    · rintro p q r ⟨F, f, g, hfg⟩ ⟨G, f', g', hfg'⟩
      refine ⟨F.prod G, (F.prodInl G).comp f, (F.prodInr G).comp g', ?_⟩
      rw [descentMap_comp, descentMap_comp, hfg, ← descentMap_comp, ← descentMap_comp,
        descentMap_congr C ((F.prodInl G).comp g) ((F.prodInr G).comp f') q.2,
        descentMap_comp, hfg', ← descentMap_comp]

variable (A) in
/-- The one-step étale plus of the relative Picard functor at the affine test `Spec A`:
relative Picard classes on some presented étale cover satisfying the descent condition,
modulo agreement on a common refinement.  On affine tests this *is* the étale
sheafification of the relative Picard presheaf (one plus suffices because the presheaf is
étale-separated — proved separately). -/
def PicEtAff : Type u :=
  Quotient (picEtAffSetoid C (A := A))

namespace PicEtAff

/-- The plus class of a relative Picard class with a descent condition on a cover. -/
def mk (E : Algebra.EtaleCover A) (x : descentClasses C E) : PicEtAff C A :=
  Quotient.mk _ ⟨E, x⟩

@[elab_as_elim]
theorem ind {motive : PicEtAff C A → Prop}
    (mk : ∀ (E : Algebra.EtaleCover A) (x : descentClasses C E), motive (mk C E x)) :
    ∀ q, motive q := by
  intro q
  induction q using Quotient.ind with
  | _ p => exact mk p.1 p.2

theorem mk_eq_mk_iff {E F : Algebra.EtaleCover A} {x : descentClasses C E}
    {y : descentClasses C F} :
    mk C E x = mk C F y ↔
      ∃ (G : Algebra.EtaleCover A) (f : E.Carrier →ₐ[A] G.Carrier)
        (g : F.Carrier →ₐ[A] G.Carrier), descentMap C f x = descentMap C g y :=
  Quotient.eq

/-- Transporting the representative to a finer cover does not change the plus class. -/
@[simp]
theorem mk_descentMap {E F : Algebra.EtaleCover A} (h : E.Carrier →ₐ[A] F.Carrier)
    (x : descentClasses C E) : mk C F (descentMap C h x) = mk C E x :=
  Quotient.sound ⟨F, AlgHom.id A F.Carrier, h, by rw [descentMap_id]⟩

/-! ### The group structure -/

/-- Transport through a `prodLift` collapses on the left factor. -/
lemma descentMap_prodLift_inl {E F H : Algebra.EtaleCover A}
    (f : E.Carrier →ₐ[A] H.Carrier) (g : F.Carrier →ₐ[A] H.Carrier)
    (x : descentClasses C E) :
    descentMap C (Algebra.EtaleCover.prodLift f g) (descentMap C (E.prodInl F) x)
      = descentMap C f x := by
  rw [← descentMap_comp, Algebra.EtaleCover.prodLift_comp_prodInl]

/-- Transport through a `prodLift` collapses on the right factor. -/
lemma descentMap_prodLift_inr {E F H : Algebra.EtaleCover A}
    (f : E.Carrier →ₐ[A] H.Carrier) (g : F.Carrier →ₐ[A] H.Carrier)
    (y : descentClasses C F) :
    descentMap C (Algebra.EtaleCover.prodLift f g) (descentMap C (E.prodInr F) y)
      = descentMap C g y := by
  rw [← descentMap_comp, Algebra.EtaleCover.prodLift_comp_prodInr]

set_option maxHeartbeats 4000000 in
-- The `rw` chain unifies `descentMap` nests whose `AlgHom` instance arguments run through
-- quotient and tensor-product carriers; the unifications are heartbeat-hungry.
private lemma mulLift_compat (p q p' q' : Σ E : Algebra.EtaleCover A, descentClasses C E)
    (hp : p ≈ p') (hq : q ≈ q') :
    mk C (p.1.prod q.1)
        (descentMap C (p.1.prodInl q.1) p.2 * descentMap C (p.1.prodInr q.1) q.2)
      = mk C (p'.1.prod q'.1)
        (descentMap C (p'.1.prodInl q'.1) p'.2
          * descentMap C (p'.1.prodInr q'.1) q'.2) := by
  obtain ⟨F, f, f', hf⟩ := hp
  obtain ⟨G, g, g', hg⟩ := hq
  refine (mk_eq_mk_iff C).mpr ⟨F.prod G,
    Algebra.EtaleCover.prodLift ((F.prodInl G).comp f) ((F.prodInr G).comp g),
    Algebra.EtaleCover.prodLift ((F.prodInl G).comp f') ((F.prodInr G).comp g'), ?_⟩
  rw [map_mul, map_mul, descentMap_prodLift_inl, descentMap_prodLift_inr,
    descentMap_prodLift_inl, descentMap_prodLift_inr, descentMap_comp, descentMap_comp,
    descentMap_comp, descentMap_comp, hf, hg]

instance : Mul (PicEtAff C A) :=
  ⟨fun a b => Quotient.liftOn₂ a b
    (fun p q => mk C (p.1.prod q.1)
      (descentMap C (p.1.prodInl q.1) p.2 * descentMap C (p.1.prodInr q.1) q.2))
    fun p q p' q' hp hq => mulLift_compat C p q p' q' hp hq⟩

lemma mk_mul_mk (E F : Algebra.EtaleCover A) (x : descentClasses C E)
    (y : descentClasses C F) :
    mk C E x * mk C F y
      = mk C (E.prod F)
          (descentMap C (E.prodInl F) x * descentMap C (E.prodInr F) y) :=
  rfl

/-- Multiplication of two classes represented on the *same* cover is represented by the
product on that cover — the descent condition makes the two transports to the common
refinement agree. -/
theorem mk_mul_mk_same (E : Algebra.EtaleCover A) (x y : descentClasses C E) :
    mk C E x * mk C E y = mk C E (x * y) := by
  have h : descentMap C (E.prodInl E) x * descentMap C (E.prodInl E) y
      = descentMap C (E.prodInl E) (x * y) :=
    (map_mul _ x y).symm
  rw [mk_mul_mk, descentMap_congr C (E.prodInr E) (E.prodInl E) y, h, mk_descentMap]

instance : One (PicEtAff C A) :=
  ⟨mk C (.self A) 1⟩

lemma one_def : (1 : PicEtAff C A) = mk C (.self A) 1 :=
  rfl

/-- The identity class is represented by the identity on every cover. -/
theorem mk_one (E : Algebra.EtaleCover A) : mk C E 1 = 1 :=
  (Quotient.sound ⟨E, AlgHom.id A E.Carrier, E.fromSelf, by
    rw [map_one, map_one]⟩ : mk C E 1 = mk C (.self A) 1)

private def invSig (p : Σ E : Algebra.EtaleCover A, descentClasses C E) :
    Σ E : Algebra.EtaleCover A, descentClasses C E :=
  ⟨p.1, p.2⁻¹⟩

private lemma invSig_compat {p q : Σ E : Algebra.EtaleCover A, descentClasses C E}
    (h : p ≈ q) : invSig C p ≈ invSig C q := by
  obtain ⟨F, f, g, hfg⟩ := h
  have key : descentMap C f p.2⁻¹ = descentMap C g q.2⁻¹ := by
    rw [map_inv, map_inv, hfg]
  exact ⟨F, f, g, key⟩

instance : Inv (PicEtAff C A) :=
  ⟨Quotient.map (invSig C) fun _ _ h => invSig_compat C h⟩

lemma mk_inv (E : Algebra.EtaleCover A) (x : descentClasses C E) :
    (mk C E x)⁻¹ = mk C E x⁻¹ :=
  rfl

instance : CommGroup (PicEtAff C A) where
  mul_assoc a b c := by
    induction a using ind with | _ E x =>
    induction b using ind with | _ F y =>
    induction c using ind with | _ G z =>
    rw [← mk_descentMap C (((E.prod F).prodInl G).comp (E.prodInl F)) x,
      ← mk_descentMap C (((E.prod F).prodInl G).comp (E.prodInr F)) y,
      ← mk_descentMap C ((E.prod F).prodInr G) z, mk_mul_mk_same, mk_mul_mk_same,
      mk_mul_mk_same, mk_mul_mk_same, mul_assoc]
  one_mul a := by
    induction a using ind with | _ E x =>
    rw [one_def, mk_mul_mk, map_one, one_mul, mk_descentMap]
  mul_one a := by
    induction a using ind with | _ E x =>
    rw [one_def, mk_mul_mk, map_one, mul_one, mk_descentMap]
  inv_mul_cancel a := by
    induction a using ind with | _ E x =>
    rw [mk_inv, mk_mul_mk_same, inv_mul_cancel, mk_one]
  mul_comm a b := by
    induction a using ind with | _ E x =>
    induction b using ind with | _ F y =>
    rw [← mk_descentMap C (E.prodInl F) x, ← mk_descentMap C (E.prodInr F) y,
      mk_mul_mk_same, mk_mul_mk_same, mul_comm]

/-! ### The unit of the plus construction -/

/-- Every class pulled back from the base carries the tautological descent datum: the two
composites `A → B ⇉ B ⊗[A] B` coincide. -/
lemma tautological_mem_descentClasses (E : Algebra.EtaleCover A)
    (x : relPic C (overSpec k A)) :
    relPicAlgMap C ((Algebra.ofId A E.Carrier).restrictScalars k) x
      ∈ descentClasses C E := by
  rw [mem_descentClasses_iff, ← relPicAlgMap_comp, ← relPicAlgMap_comp]
  congr 2
  ext a
  simp [doubleInl, doubleInr, Algebra.ofId_apply]

variable (A) in
/-- The unit of the plus construction: a relative Picard class of the affine test,
pulled back to the trivial cover with its tautological descent datum. -/
def unit : relPic C (overSpec k A) →* PicEtAff C A where
  toFun x := mk C (.self A)
    ⟨_, tautological_mem_descentClasses C (.self A) x⟩
  map_one' := by
    rw [show (⟨_, tautological_mem_descentClasses C (.self A) 1⟩ :
        descentClasses C (.self A)) = 1 from Subtype.ext (map_one _), mk_one]
  map_mul' x y := by
    rw [show (⟨_, tautological_mem_descentClasses C (.self A) (x * y)⟩ :
        descentClasses C (.self A))
        = ⟨_, tautological_mem_descentClasses C (.self A) x⟩
          * ⟨_, tautological_mem_descentClasses C (.self A) y⟩ from
      Subtype.ext (map_mul _ x y), ← mk_mul_mk_same]

end PicEtAff

end

end AlgebraicGeometry
