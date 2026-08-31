/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.QcohSections
import AlgebraicJacobian.RiemannRoch.Ledger.AffineVanishing

/-!
# Twisted affine Serre vanishing: degree-one cohomology of quasi-coherently packaged sheaves

The Wave-4 keystone (G-CBC-3(ii)): for a scheme `X`, an affine open `U`, and a sheaf `F`
of `k`-modules on the small Zariski site carrying the quasi-coherence packaging
`Scheme.QcohOn F U` of `AlgebraicJacobian.Cohomology.QcohSections` (ambient-section
action + localization on affine opens of `U`), the degree-one cohomology of `U` with
coefficients in `F` vanishes:
`Subsingleton (Sheaf.HModule' F U 1)`
(`AlgebraicGeometry.IsAffineOpen.subsingleton_hModule'_one_of_qcoh`); and for `X` itself
affine, the degree-one cohomology of the site vanishes:
`Subsingleton (Sheaf.HModule F 1)`
(`AlgebraicGeometry.Scheme.subsingleton_hModule_one_of_qcoh`).

This generalizes the landed structure-sheaf engine of
`AlgebraicJacobian.Cohomology.AffineVanishing` /
`AlgebraicJacobian.Cohomology.AffineCech` off the structure sheaf: taking
`F = X.moduleKSheaf k` (whose packaging instance lives in
`AlgebraicJacobian.Cohomology.QcohSections`) recovers
`IsAffineOpen.subsingleton_moduleKSheaf_hModule'_one`. The intended coefficients are the
twisted line bundles of the Wave-4 representability route — sheaves glued from unit
cocycles on finite affine trivializing covers — for which the packaging holds chartwise.

## Proof architecture

Verbatim Serre, as in `AlgebraicJacobian.Cohomology.AffineVanishing`, with the packaging
axioms in place of the structure-sheaf localization lemmas:

* `IsAffineOpen.exists_cech_cobounding_of_qcoh` — every Čech 1-cocycle for `F` on a
  finite basic-open cover of `U` is a coboundary: clear denominators with one uniform
  exponent (packaging axiom `QcohOn.exists_secRes_eq_qsmul_pow`), annihilate the
  triple-overlap defects (`QcohOn.exists_qsmul_pow_eq_zero`), and assemble along a
  partition of unity `1 = ∑ h l · f l ^ (N + M)` of the affine `U` — the assembly needs
  only that ambient sections act on `F`-sections compatibly with restriction (the (P1)
  mixin).
* `IsAffineOpen.cokernel_app_surjective_of_qcoh` — for a monomorphism `ι : F ⟶ G`,
  sections of `cokernel ι` over `U` lift to `G`: local lifts on a finite basic cover
  differ by an `F`-valued 1-cocycle, which cobounds; the corrected lifts glue.
* `IsAffineOpen.subsingleton_hModule'_one_of_qcoh` — `H¹'(U, F) = Ext¹(k[U], F) = 0` by
  `Abelian.Ext.subsingleton_one_of_injective_of_surjective` applied to `Injective.ι F`,
  with the section surjectivity above; `Scheme.subsingleton_hModule_one_of_qcoh`
  transports along `Sheaf.HModule.linearEquivHModule'` for affine `X`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

namespace IsAffineOpen

open Scheme.QcohOn

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {U : X.Opens}
variable {F : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} k)}

/-- **Degree-one Čech cobounding for a quasi-coherently packaged sheaf on an affine
open.** Let `U` be an affine open of a scheme `X`, covered by finitely many basic opens
`D(f i)`, and let `F` be a sheaf of `k`-modules with the quasi-coherence packaging on `U`.
Every 1-cocycle `a i j` of `F`-sections on the pairwise intersections is a coboundary:
there are sections `b i` of `F` on `D(f i)` with `a i j = b i - b j` on `D(f i) ⊓ D(f j)`.

This is `IsAffineOpen.exists_cech_cobounding` with structure-sheaf coefficients replaced
by `F` (Serre's partition-of-unity argument, run through the packaging axioms). -/
theorem exists_cech_cobounding_of_qcoh (hU : IsAffineOpen U) [Scheme.QcohOn F U] {n : ℕ}
    (f : Fin n → Γ(X, U)) (hcov : ⨆ i, X.basicOpen (f i) = U)
    (a : ∀ i j, F.obj.obj (op (X.basicOpen (f i) ⊓ X.basicOpen (f j))))
    (hc : ∀ i j l,
      secRes F (inf_le_inf_right (X.basicOpen (f l)) inf_le_left) (a i l) =
        secRes F inf_le_left (a i j) +
          secRes F (inf_le_inf_right (X.basicOpen (f l)) inf_le_right) (a j l)) :
    ∃ b : ∀ i, F.obj.obj (op (X.basicOpen (f i))),
      ∀ i j, a i j = secRes F inf_le_left (b i) - secRes F inf_le_right (b j) := by
  classical
  have haff : ∀ i : Fin n, IsAffineOpen (X.basicOpen (f i)) := fun i ↦ hU.basicOpen (f i)
  have haff2 : ∀ i j : Fin n, IsAffineOpen (X.basicOpen (f i) ⊓ X.basicOpen (f j)) := by
    intro i j
    rw [← X.basicOpen_mul]
    exact hU.basicOpen _
  -- Step 1: clear denominators, with a uniform exponent `N`.
  choose N₀ e₀ he₀ using fun i j ↦
    exists_secRes_eq_qsmul_pow (U := U) (haff i) (X.basicOpen_le (f i)) (f j) (a i j)
  obtain ⟨N, hN⟩ : ∃ N, ∀ i j, N₀ i j ≤ N :=
    ⟨Finset.univ.sup fun p : Fin n × Fin n ↦ N₀ p.1 p.2,
      fun i j ↦ Finset.le_sup (f := fun p : Fin n × Fin n ↦ N₀ p.1 p.2)
        (Finset.mem_univ (i, j))⟩
  obtain ⟨e, he⟩ : ∃ e : ∀ i : Fin n, Fin n → F.obj.obj (op (X.basicOpen (f i))),
      ∀ i j, secRes F inf_le_left (e i j) =
        qsmul (inf_le_left.trans (X.basicOpen_le (f i))) (f j ^ N) (a i j) := by
    refine ⟨fun i j ↦ qsmul (X.basicOpen_le (f i)) (f j ^ (N - N₀ i j)) (e₀ i j),
      fun i j ↦ ?_⟩
    rw [secRes_qsmul, he₀ i j, ← mul_qsmul, ← pow_add, Nat.sub_add_cancel (hN i j)]
  -- Step 2: the defects vanish on triple intersections, hence are killed by powers.
  obtain ⟨t, ht_def⟩ : ∃ t : ∀ i j : Fin n, Fin n →
        F.obj.obj (op (X.basicOpen (f i) ⊓ X.basicOpen (f j))),
      ∀ i j l, t i j l =
        secRes F inf_le_left (e i l) - secRes F inf_le_right (e j l) -
          qsmul (inf_le_left.trans (X.basicOpen_le (f i))) (f l ^ N) (a i j) :=
    ⟨fun i j l ↦
      secRes F inf_le_left (e i l) - secRes F inf_le_right (e j l) -
        qsmul (inf_le_left.trans (X.basicOpen_le (f i))) (f l ^ N) (a i j),
      fun _ _ _ ↦ rfl⟩
  have ht0 : ∀ i j l, secRes F
      (inf_le_left : (X.basicOpen (f i) ⊓ X.basicOpen (f j)) ⊓ X.basicOpen (f l) ≤ _)
      (t i j l) = 0 := by
    intro i j l
    have hil := congrArg
      (secRes F (inf_le_inf_right (X.basicOpen (f l)) inf_le_left :
        X.basicOpen (f i) ⊓ X.basicOpen (f j) ⊓ X.basicOpen (f l) ≤
          X.basicOpen (f i) ⊓ X.basicOpen (f l))) (he i l)
    have hjl := congrArg
      (secRes F (inf_le_inf_right (X.basicOpen (f l)) inf_le_right :
        X.basicOpen (f i) ⊓ X.basicOpen (f j) ⊓ X.basicOpen (f l) ≤
          X.basicOpen (f j) ⊓ X.basicOpen (f l))) (he j l)
    rw [secRes_secRes, secRes_qsmul] at hil hjl
    rw [ht_def i j l, map_sub, map_sub, secRes_qsmul, secRes_secRes, secRes_secRes,
      hil, hjl, hc i j l, qsmul_add]
    abel
  choose M₀ hM₀ using fun i j l ↦
    exists_qsmul_pow_eq_zero (U := U) (haff2 i j)
      ((inf_le_left.trans (X.basicOpen_le (f i))) :
        X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ U)
      (f l) (t i j l) (ht0 i j l)
  obtain ⟨M, hM⟩ : ∃ M, ∀ i j l, M₀ i j l ≤ M :=
    ⟨Finset.univ.sup fun p : Fin n × Fin n × Fin n ↦ M₀ p.1 p.2.1 p.2.2,
      fun i j l ↦ Finset.le_sup (f := fun p : Fin n × Fin n × Fin n ↦ M₀ p.1 p.2.1 p.2.2)
        (Finset.mem_univ (i, j, l))⟩
  have hMt : ∀ i j l, qsmul ((inf_le_left.trans (X.basicOpen_le (f i))) :
      X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ U) (f l ^ M) (t i j l) = 0 := by
    intro i j l
    have h0 : qsmul ((inf_le_left.trans (X.basicOpen_le (f i))) :
        X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ U) (f l ^ (M - M₀ i j l))
        (qsmul (inf_le_left.trans (X.basicOpen_le (f i))) (f l ^ M₀ i j l)
          (t i j l)) = 0 := by
      rw [hM₀ i j l, qsmul_zero]
    rwa [← mul_qsmul, ← pow_add, Nat.sub_add_cancel (hM i j l)] at h0
  -- Step 3: partition of unity for the exponent `N + M`.
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    rw [← hU.iSup_basicOpen_eq_self_iff]
    rw [iSup_range' (fun g ↦ X.basicOpen g) f]
    exact hcov
  have hspanK : Ideal.span (Set.range fun i ↦ f i ^ (N + M)) = ⊤ := by
    have hpow := Ideal.span_pow_eq_top (Set.range f) hspan (N + M)
    rwa [← Set.range_comp] at hpow
  have hone : (1 : Γ(X, U)) ∈ Ideal.span (Set.range fun i ↦ f i ^ (N + M)) := by
    rw [hspanK]; trivial
  rw [Ideal.mem_span_range_iff_exists_fun] at hone
  obtain ⟨h, hh⟩ := hone
  -- Step 4: assemble the cobounding.
  refine ⟨fun i ↦ ∑ l, qsmul (X.basicOpen_le (f i)) (h l * f l ^ M) (e i l),
    fun i j ↦ ?_⟩
  have key : ∀ l : Fin n,
      secRes F (inf_le_left : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ _)
          (qsmul (X.basicOpen_le (f i)) (h l * f l ^ M) (e i l)) -
        secRes F (inf_le_right : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ _)
          (qsmul (X.basicOpen_le (f j)) (h l * f l ^ M) (e j l)) =
      qsmul (inf_le_left.trans (X.basicOpen_le (f i))) (h l * f l ^ (N + M)) (a i j) := by
    intro l
    have hkill := hMt i j l
    rw [ht_def i j l, qsmul_sub, sub_eq_zero, ← mul_qsmul, ← pow_add,
      Nat.add_comm M N] at hkill
    rw [secRes_qsmul, secRes_qsmul, ← qsmul_sub, mul_qsmul, hkill, ← mul_qsmul]
  rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun l _ ↦ key l]
  calc a i j
      = qsmul ((inf_le_left : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ _).trans
          (X.basicOpen_le (f i))) 1 (a i j) := (one_qsmul _ _).symm
    _ = qsmul (inf_le_left.trans (X.basicOpen_le (f i)))
          (∑ l, h l * f l ^ (N + M)) (a i j) := by rw [hh]
    _ = ∑ l, qsmul (inf_le_left.trans (X.basicOpen_le (f i)))
          (h l * f l ^ (N + M)) (a i j) :=
        sum_qsmul Finset.univ _ _ _

/-- **Sections surjectivity over an affine open, quasi-coherent coefficients.** For a
monomorphism `ι : F ⟶ G` out of a sheaf of `k`-modules with the quasi-coherence
packaging on an affine open `U`, every section of `cokernel ι` over `U` lifts to a
section of `G` over `U`.

This is the geometric heart of the twisted degree-one vanishing
(`IsAffineOpen.cokernel_app_surjective` with the structure sheaf replaced by `F`): local
lifts on a finite basic cover of `U` differ by a Čech 1-cocycle valued in `F`, which is a
coboundary by `IsAffineOpen.exists_cech_cobounding_of_qcoh`; the corrected lifts glue. -/
theorem cokernel_app_surjective_of_qcoh (hU : IsAffineOpen U)
    {G : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} k)}
    [Scheme.QcohOn F U] (ι : F ⟶ G) [Mono ι]
    (q : (cokernel ι).obj.obj (op U)) :
    ∃ s : G.obj.obj (op U),
      ((cokernel.π ι).hom.app (op U)).hom s = q := by
  classical
  -- (a) `cokernel.π ι` is an epimorphism, hence locally surjective.
  have hls : Presheaf.IsLocallySurjective (Opens.grothendieckTopology (X : TopCat))
      (cokernel.π ι).hom :=
    (Sheaf.isLocallySurjective_iff_epi' (A := ModuleCat.{u} k) (cokernel.π ι)).mpr
      inferInstance
  -- (b) each point of `U` has a basic open neighbourhood carrying a local lift of `q`.
  have hloc : ∀ x : (U : Set X), ∃ f₀ : Γ(X, U), ↑x ∈ X.basicOpen f₀ ∧
      ∃ s : G.obj.obj (op (X.basicOpen f₀)),
        ((cokernel.π ι).hom.app (op (X.basicOpen f₀))).hom s =
          secRes (cokernel ι) (X.basicOpen_le f₀) q := by
    intro x
    obtain ⟨V, g, hg, hxV⟩ := Presheaf.imageSieve_mem
      (Opens.grothendieckTopology (X : TopCat)) (cokernel.π ι).hom q x x.2
    obtain ⟨s, hs⟩ := hg
    obtain ⟨f₀, hle, hxf₀⟩ := hU.exists_basicOpen_le (⟨(x : X), hxV⟩ : V) x.2
    refine ⟨f₀, hxf₀, secRes G hle s, ?_⟩
    have hnat := secRes_naturality (cokernel.π ι) hle s
    rw [hnat]
    have hs' : ((cokernel.π ι).hom.app (op V)).hom s = secRes (cokernel ι) g.le q := hs
    rw [hs', secRes_secRes]
  choose f₀ hmem s₀ hs₀ using hloc
  -- (c) finite subcover by quasi-compactness of the affine open.
  obtain ⟨FS, hFS⟩ := hU.isCompact.elim_finite_subcover
    (fun x : (U : Set X) ↦ (X.basicOpen (f₀ x) : Set X))
    (fun x ↦ (X.basicOpen (f₀ x)).isOpen)
    (fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩)
  let f : Fin FS.card → Γ(X, U) := fun i ↦ f₀ (FS.equivFin.symm i)
  have hcov : ⨆ i, X.basicOpen (f i) = U := by
    apply le_antisymm (iSup_le fun i ↦ X.basicOpen_le (f i))
    intro x hx
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hFS hx)
    simp only [Set.mem_iUnion] at hy
    obtain ⟨hyF, hxy⟩ := hy
    exact Opens.mem_iSup.mpr ⟨FS.equivFin ⟨y, hyF⟩, by simpa [f] using hxy⟩
  let s : ∀ i, G.obj.obj (op (X.basicOpen (f i))) := fun i ↦ s₀ (FS.equivFin.symm i)
  have hs : ∀ i, ((cokernel.π ι).hom.app (op (X.basicOpen (f i)))).hom (s i) =
      secRes (cokernel ι) (X.basicOpen_le (f i)) q := fun i ↦ hs₀ (FS.equivFin.symm i)
  -- (d) the differences of the local lifts come from `F`.
  have hker : ∀ i j, ((cokernel.π ι).hom.app
      (op (X.basicOpen (f i) ⊓ X.basicOpen (f j)))).hom
      (secRes G inf_le_left (s i) - secRes G inf_le_right (s j)) = 0 := by
    intro i j
    have h1 := secRes_naturality (cokernel.π ι)
      (inf_le_left : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ X.basicOpen (f i)) (s i)
    have h2 := secRes_naturality (cokernel.π ι)
      (inf_le_right : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ X.basicOpen (f j)) (s j)
    rw [map_sub, h1, h2, hs i, hs j, secRes_secRes, secRes_secRes, sub_self]
  choose a ha using fun i j ↦ Sheaf.exists_app_eq_of_cokernelπ_app_eq_zero ι
    (op (X.basicOpen (f i) ⊓ X.basicOpen (f j))) _ (hker i j)
  -- (e) the `a i j` form a Čech 1-cocycle valued in `F`.
  have hcoc : ∀ i j l,
      secRes F (inf_le_inf_right (X.basicOpen (f l)) inf_le_left) (a i l) =
        secRes F inf_le_left (a i j) +
          secRes F (inf_le_inf_right (X.basicOpen (f l)) inf_le_right) (a j l) := by
    intro i j l
    apply Sheaf.app_injective_of_mono ι
      (op (X.basicOpen (f i) ⊓ X.basicOpen (f j) ⊓ X.basicOpen (f l)))
    have h1 := secRes_naturality ι
      (inf_le_inf_right (X.basicOpen (f l)) inf_le_left :
        X.basicOpen (f i) ⊓ X.basicOpen (f j) ⊓ X.basicOpen (f l) ≤
          X.basicOpen (f i) ⊓ X.basicOpen (f l)) (a i l)
    have h2 := secRes_naturality ι
      (inf_le_left : X.basicOpen (f i) ⊓ X.basicOpen (f j) ⊓ X.basicOpen (f l) ≤
        X.basicOpen (f i) ⊓ X.basicOpen (f j)) (a i j)
    have h3 := secRes_naturality ι
      (inf_le_inf_right (X.basicOpen (f l)) inf_le_right :
        X.basicOpen (f i) ⊓ X.basicOpen (f j) ⊓ X.basicOpen (f l) ≤
          X.basicOpen (f j) ⊓ X.basicOpen (f l)) (a j l)
    rw [map_add, h1, h2, h3, ha i l, ha i j, ha j l]
    simp only [map_sub, secRes_secRes]
    abel
  -- (f) cobound the cocycle and correct the local lifts.
  obtain ⟨b, hb⟩ := hU.exists_cech_cobounding_of_qcoh f hcov a hcoc
  let tloc : ∀ i, G.obj.obj (op (X.basicOpen (f i))) :=
    fun i ↦ s i - (ι.hom.app (op (X.basicOpen (f i)))).hom (b i)
  have hcompat : TopCat.Presheaf.IsCompatible G.obj (fun i ↦ X.basicOpen (f i)) tloc := by
    intro i j
    change secRes G (inf_le_left : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ _) (tloc i) =
      secRes G inf_le_right (tloc j)
    have h1 := secRes_naturality ι
      (inf_le_left : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ X.basicOpen (f i)) (b i)
    have h2 := secRes_naturality ι
      (inf_le_right : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ X.basicOpen (f j)) (b j)
    change secRes G _ (s i - (ι.hom.app (op (X.basicOpen (f i)))).hom (b i)) =
      secRes G _ (s j - (ι.hom.app (op (X.basicOpen (f j)))).hom (b j))
    rw [map_sub, map_sub, ← h1, ← h2, sub_eq_sub_iff_sub_eq_sub, ← map_sub, ← hb i j]
    exact (ha i j).symm
  obtain ⟨gl, hgl, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (X := (X : TopCat)) (C := ModuleCat.{u} k) G (fun i ↦ X.basicOpen (f i)) U
    (fun i ↦ homOfLE (X.basicOpen_le (f i))) (le_of_eq hcov.symm) tloc hcompat
  refine ⟨gl, ?_⟩
  -- (g) the glued section maps to `q` by separation.
  apply TopCat.Sheaf.eq_of_locally_eq' (X := (X : TopCat)) (C := ModuleCat.{u} k)
    (cokernel ι) (fun i ↦ X.basicOpen (f i)) U (fun i ↦ homOfLE (X.basicOpen_le (f i)))
    (le_of_eq hcov.symm)
  intro i
  change secRes (cokernel ι) (X.basicOpen_le (f i))
      (((cokernel.π ι).hom.app (op U)).hom gl) =
    secRes (cokernel ι) (X.basicOpen_le (f i)) q
  have h1 := secRes_naturality (cokernel.π ι) (X.basicOpen_le (f i)) gl
  rw [← h1]
  have hgl' : secRes G (X.basicOpen_le (f i)) gl = tloc i := hgl i
  rw [hgl']
  change ((cokernel.π ι).hom.app (op (X.basicOpen (f i)))).hom
    (s i - (ι.hom.app (op (X.basicOpen (f i)))).hom (b i)) = _
  have hπι : ((cokernel.π ι).hom.app (op (X.basicOpen (f i)))).hom
      ((ι.hom.app (op (X.basicOpen (f i)))).hom (b i)) = 0 :=
    congrArg (fun m : F ⟶ cokernel ι ↦
      (m.hom.app (op (X.basicOpen (f i)))).hom (b i)) (cokernel.condition ι)
  rw [map_sub, hs i, hπι, sub_zero]

/-- **Twisted affine Serre vanishing in degree one** (G-CBC-3(ii)): for a scheme `X`, an
affine open `U`, and a sheaf `F` of `k`-modules on the small Zariski site of `X` carrying
the quasi-coherence packaging `Scheme.QcohOn F U`, the degree-one cohomology of `U` with
coefficients in `F` vanishes (in the sense of `Sheaf.HModule'`, cohomology of an object
of the site).

Taking `F = X.moduleKSheaf k` recovers the landed structure-sheaf vanishing
`IsAffineOpen.subsingleton_moduleKSheaf_hModule'_one`. -/
theorem subsingleton_hModule'_one_of_qcoh (hU : IsAffineOpen U)
    (F : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} k))
    [Scheme.QcohOn F U] :
    Subsingleton (Sheaf.HModule' F U 1) := by
  apply Abelian.Ext.subsingleton_one_of_injective_of_surjective (Injective.ι F)
  intro φ
  obtain ⟨sglob, hsglob⟩ := hU.cokernel_app_surjective_of_qcoh (Injective.ι F)
    (Sheaf.freeModuleSheafHomEquiv (cokernel (Injective.ι F)) φ)
  refine ⟨(Sheaf.freeModuleSheafHomEquiv (Injective.under F)).symm sglob, ?_⟩
  apply (Sheaf.freeModuleSheafHomEquiv (cokernel (Injective.ι F))).injective
  rw [Sheaf.freeModuleSheafHomEquiv_comp, LinearEquiv.apply_symm_apply]
  exact hsglob

end IsAffineOpen

/-- **Twisted affine Serre vanishing, affine schemes** (G-CBC-3(ii), site form): for an
affine scheme `X` and a sheaf `F` of `k`-modules on its small Zariski site carrying the
quasi-coherence packaging on `⊤`, the degree-one cohomology of the site vanishes.
Transport of `IsAffineOpen.subsingleton_hModule'_one_of_qcoh` along
`Sheaf.HModule.linearEquivHModule'`. -/
theorem Scheme.subsingleton_hModule_one_of_qcoh {k : Type u} [CommRing k] {X : Scheme.{u}}
    [IsAffine X] (F : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} k))
    [Scheme.QcohOn F (⊤ : X.Opens)] :
    Subsingleton (Sheaf.HModule F 1) :=
  haveI := (isAffineOpen_top X).subsingleton_hModule'_one_of_qcoh F
  (Sheaf.HModule.linearEquivHModule' (isTerminalTop : IsTerminal (⊤ : X.Opens))
    F 1).toEquiv.subsingleton

section StructureSheafSpecialCase

variable {k : Type u} [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))] {U : X.Opens}

/-- The generalized engine recovers the landed structure-sheaf vanishing
(`IsAffineOpen.subsingleton_moduleKSheaf_hModule'_one`) through the packaging instance of
`AlgebraicJacobian.Cohomology.QcohSections`. -/
example (hU : IsAffineOpen U) : Subsingleton (Sheaf.HModule' (X.moduleKSheaf k) U 1) :=
  hU.subsingleton_hModule'_one_of_qcoh (X.moduleKSheaf k)

/-- The generalized engine recovers the landed structure-sheaf site vanishing
(`Scheme.subsingleton_moduleKSheaf_hModule_one`). -/
example [IsAffine X] : Subsingleton (Sheaf.HModule (X.moduleKSheaf k) 1) :=
  Scheme.subsingleton_hModule_one_of_qcoh (X.moduleKSheaf k)

end StructureSheafSpecialCase

end AlgebraicGeometry
