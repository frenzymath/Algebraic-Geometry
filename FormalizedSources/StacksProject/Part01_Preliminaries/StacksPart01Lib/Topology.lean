import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Rel

/-!
# Quasi-compactness and separation

This module records the terminology used in the Stacks Project's topology
chapter.  Mathlib calls a quasi-compact subset `IsCompact`; the definitions
below keep the source terminology while exposing the existing API.
-/

namespace StacksPart01

open Set

/-- A subset is quasi-compact when every open cover has a finite subcover.

This is the Stacks Project's `topology-definition-quasi-compact` terminology;
the proposition is definitionally Mathlib's `IsCompact`.
-/
def IsQuasiCompact {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  IsCompact s

/-- A space is quasi-compact when its underlying set is quasi-compact. -/
def QuasiCompactSpace (X : Type*) [TopologicalSpace X] : Prop :=
  IsQuasiCompact (Set.univ : Set X)

/-- The Stacks notion of a quasi-compact continuous map. -/
def IsQuasiCompactMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  Continuous f ∧
    ∀ ⦃V : Set Y⦄, IsOpen V → IsQuasiCompact V →
      IsQuasiCompact (f ⁻¹' V)

/-- A subset is retrocompact when its intersection with every
quasi-compact open is quasi-compact. -/
def Retrocompact {Y : Type*} [TopologicalSpace Y] (s : Set Y) : Prop :=
  ∀ ⦃V : Set Y⦄, IsOpen V → IsQuasiCompact V → IsQuasiCompact (s ∩ V)

/-- Quasi-compact maps are closed under composition (Stacks, Tag 005B). -/
theorem isQuasiCompactMap_comp {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z} (hf : IsQuasiCompactMap f)
    (hg : IsQuasiCompactMap g) :
    IsQuasiCompactMap (g ∘ f) := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  intro V hV hVcompact
  have hgp : IsCompact (g ⁻¹' V) := hg.2 hV hVcompact
  have hopen : IsOpen (g ⁻¹' V) := hV.preimage hg.1
  have hfp : IsCompact (f ⁻¹' (g ⁻¹' V)) := hf.2 hopen hgp
  simpa [IsQuasiCompact, Function.comp_def, Set.preimage_preimage] using hfp

/-- The image of a quasi-compact map is retrocompact (Stacks, Tag 04Z9). -/
theorem image_retrocompact {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsQuasiCompactMap f) :
    Retrocompact (Set.range f) := by
  intro V hV hVcompact
  have hpre : IsCompact (f ⁻¹' V) := hf.2 hV hVcompact
  have himage : IsCompact (f '' (f ⁻¹' V)) := hpre.image hf.1
  simpa [IsQuasiCompact, Set.image_preimage_eq_inter_range, Set.inter_comm] using himage

/-- The continuous image of a quasi-compact space is quasi-compact
(Stacks, Tag 04Z9, part (1)). -/
theorem image_quasiCompact {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hX : QuasiCompactSpace X) (hf : Continuous f) :
    IsQuasiCompact (Set.range f) := by
  have hX' : IsCompact (Set.univ : Set X) := hX
  have h' := hX'.image hf
  simpa [IsQuasiCompact, Set.image_univ] using h'

/-- A closed subset of a quasi-compact subset is quasi-compact
(Stacks, Tag 005C). -/
theorem closed_subset_quasiCompact {X : Type*} [TopologicalSpace X]
    {s t : Set X} (hs : IsQuasiCompact s) (ht : IsClosed t) (hsub : t ⊆ s) :
    IsQuasiCompact t := by
  exact hs.of_isClosed_subset ht hsub

/-- A closed subset of a quasi-compact space is quasi-compact. -/
theorem closed_subset_of_quasiCompact_space {X : Type*} [TopologicalSpace X]
    (hX : QuasiCompactSpace X) {t : Set X} (ht : IsClosed t) :
    IsQuasiCompact t := by
  exact closed_subset_quasiCompact hX ht (Set.subset_univ t)

/-- A family of closed subsets of a quasi-compact space with the finite
intersection property has nonempty total intersection (Stacks, Tag 005D). -/
theorem iInter_nonempty_of_closed_finite_intersections {X : Type*}
    [TopologicalSpace X] (hX : QuasiCompactSpace X) {ι : Type*}
    (Z : ι → Set X) (hZ : ∀ i, IsClosed (Z i))
    (hfinite : ∀ s : Finset ι, (⋂ i ∈ s, Z i).Nonempty) :
    (⋂ i, Z i).Nonempty := by
  letI : CompactSpace X := ⟨hX⟩
  exact CompactSpace.iInter_nonempty hZ hfinite

/-- In a compact Hausdorff space, quasi-compact subsets are exactly closed
subsets (Stacks, Tag 08YC). -/
theorem quasiCompact_iff_closed {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {s : Set X} :
    IsQuasiCompact s ↔ IsClosed s := by
  constructor
  · intro hs
    exact hs.isClosed
  · intro hs
    exact hs.isCompact

/-- Quasi-compact subsets of a Hausdorff space are closed (Stacks, Tag 08YB). -/
theorem quasiCompact_isClosed {X : Type*} [TopologicalSpace X]
    [T2Space X] {s : Set X} (hs : IsQuasiCompact s) : IsClosed s := by
  exact hs.isClosed

/-- Disjoint quasi-compact subsets of a Hausdorff space admit disjoint
neighbourhoods (Stacks, Tag 08YB). -/
theorem separatedNhds_of_disjoint_quasiCompact {X : Type*}
    [TopologicalSpace X] [T2Space X] {s t : Set X}
    (hs : IsQuasiCompact s) (ht : IsQuasiCompact t)
    (hdis : Disjoint s t) : SeparatedNhds s t := by
  exact SeparatedNhds.of_isCompact_isCompact hs ht hdis

/-- Finite unions of quasi-compact subsets are quasi-compact. -/
theorem quasiCompact_union {X : Type*} [TopologicalSpace X]
    {s t : Set X} (hs : IsQuasiCompact s) (ht : IsQuasiCompact t) :
    IsQuasiCompact (s ∪ t) := by
  exact hs.union ht

/-- Finite products of quasi-compact subsets are quasi-compact. -/
theorem quasiCompact_prod {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {t : Set Y} (hs : IsQuasiCompact s) (ht : IsQuasiCompact t) :
    IsQuasiCompact (s ×ˢ t) := by
  exact hs.prod ht

/-- Compact subsets of a product admit product neighbourhoods inside any open
neighbourhood of their product (Stacks, Tag 005N). -/
theorem quasiCompact_tube {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {s : Set X} {t : Set Y}
    {n : Set (X × Y)} (hs : IsQuasiCompact s) (ht : IsQuasiCompact t)
    (hn : IsOpen n) (hst : s ×ˢ t ⊆ n) :
    ∃ u : Set X, ∃ v : Set Y,
      IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ u ×ˢ v ⊆ n := by
  exact generalized_tube_lemma hs ht hn hst

/- A subbasis cover criterion for quasi-compactness (Stacks, Tag 08ZP). -/
def IsSubbase {X : Type*} [TopologicalSpace X] (B : Set (Set X)) : Prop :=
  ‹TopologicalSpace X› = TopologicalSpace.generateFrom B

theorem compactSpace_of_subbase {X : Type*} [TopologicalSpace X]
    {B : Set (Set X)} (hB : IsSubbase B)
    (hcover : ∀ P ⊆ B, ⋃₀ P = Set.univ →
      ∃ Q ⊆ P, Q.Finite ∧ ⋃₀ Q = Set.univ) : CompactSpace X := by
  exact compactSpace_generateFrom hB hcover

/-- In a Hausdorff space, intersections of quasi-compact subsets are quasi-compact. -/
theorem quasiCompact_inter {X : Type*} [TopologicalSpace X] [T2Space X]
    {s t : Set X} (hs : IsQuasiCompact s) (ht : IsQuasiCompact t) :
    IsQuasiCompact (s ∩ t) := by
  exact hs.inter ht

/-- Hausdorffness is equivalent to closedness of the diagonal
(Stacks, Tag 08ZE). -/
theorem hausdorff_iff_closed_diagonal (X : Type*) [TopologicalSpace X] :
    T2Space X ↔ IsClosed (Set.diagonal X) :=
  t2_iff_isClosed_diagonal

/-- The graph of a continuous map into a Hausdorff space is closed
(Stacks, Tag 08ZF). -/
theorem isClosed_graph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} (hf : Continuous f) :
    IsClosed (Function.graph f) := by
  rw [show Function.graph f = {p : X × Y | f p.1 = p.2} by
    ext p
    exact Function.mem_graph]
  exact isClosed_eq (hf.comp continuous_fst) continuous_snd

/-- The image of a continuous section is closed when the source of the
section is Hausdorff (Stacks, Tag 08ZG). -/
theorem isClosed_section_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] (f : X → Y) (s : Y → X) (hf : Continuous f) (hs : Continuous s)
    (hfs : f ∘ s = id) : IsClosed (s '' (Set.univ : Set Y)) := by
  have heq : IsClosed {x : X | id x = s (f x)} :=
    isClosed_eq continuous_id (hs.comp hf)
  have himage : s '' (Set.univ : Set Y) = {x : X | id x = s (f x)} := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      have hy : f (s y) = y := by
        simpa [Function.comp_def] using congrFun hfs y
      change s y = s (f (s y))
      rw [hy]
    · intro hx
      refine ⟨f x, Set.mem_univ _, ?_⟩
      change x = s (f x) at hx
      exact hx.symm
  rw [himage]
  exact heq

/-- The fiber-product locus of two maps into a Hausdorff space is closed in
the product (Stacks, Tag 08ZH). -/
def fiberProductSet {X Y Z : Type*} (f : X → Z) (g : Y → Z) : Set (X × Y) :=
  {p | f p.1 = g p.2}

theorem isClosed_fiberProductSet {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Z]
    (f : X → Z) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) :
    IsClosed (fiberProductSet f g) := by
  exact isClosed_eq (hf.comp continuous_fst) (hg.comp continuous_snd)

/-- Continuous images of connected sets are connected. -/
theorem isConnected_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (hs : IsConnected s) (f : X → Y) (hf : ContinuousOn f s) :
    IsConnected (f '' s) :=
  hs.image f hf

/-- The image of a connected space under a continuous map is connected. -/
theorem isConnected_range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ConnectedSpace X] (f : X → Y) (hf : Continuous f) :
    IsConnected (Set.range f) := by
  simpa only [Set.image_univ] using
    (isConnected_univ.image f hf.continuousOn)

/-- The closure of a connected set is connected (Stacks, Tag 004T). -/
theorem isConnected_closure {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsConnected s) : IsConnected (closure s) :=
  hs.closure

/-- Two connected sets with a common point have connected union. -/
theorem isConnected_union {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hinter : (s ∩ t).Nonempty) (hs : IsConnected s) (ht : IsConnected t) :
    IsConnected (s ∪ t) :=
  hs.union hinter ht

end StacksPart01
