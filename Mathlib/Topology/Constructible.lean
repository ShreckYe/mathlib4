/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Topology.Spectral.Hom

/-!
# Constructible sets

This file defines constructible sets, which are morally sets in a topological space which we can
make out of finite unions and intersections of open and closed sets.

Precisely, constructible sets are the boolean subalgebra generated by open retrocompact sets,
where a set is retrocompact if its intersection with every compact open set is compact.
In a locally noetherian space, all sets are retrocompact, in which case this boolean subalgebra is
simply the one generated by the open sets.

Constructible sets are useful because the image of a constructible set under a finitely presented
morphism of schemes is a constructible set (and this is *not* true at the level of varieties).

## Main declarations

* `IsRetrocompact`: Predicate for a set to be retrocompact, namely to have its intersection with
  every compact open be compact.
* `IsConstructible`: Predicate for a set to be constructible, namely to belong to the boolean
  subalgebra generated by open retrocompact sets.
* `IsLocallyConstructible`: Predicate for a set to be locally constructible, namely to be
  partitionable along an open cover such that each of its parts is constructible in the
  respective open subspace.
-/

open Set TopologicalSpace Topology
open scoped Set.Notation

variable {ι : Sort*} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
  {s t U : Set X} {a : X}

/-! ### retrocompact sets -/

/-- A retrocompact set is a set whose intersection with every compact open is compact. -/
@[stacks 005A]
def IsRetrocompact (s : Set X) : Prop := ∀ ⦃U⦄, IsCompact U → IsOpen U → IsCompact (s ∩ U)

@[simp] lemma IsRetrocompact.empty : IsRetrocompact (∅ : Set X) := by simp [IsRetrocompact]
@[simp] lemma IsRetrocompact.univ : IsRetrocompact (univ : Set X) := by
  simp +contextual [IsRetrocompact]

@[simp] lemma IsRetrocompact.singleton : IsRetrocompact {a} :=
  fun _ _ _ ↦ Subsingleton.singleton_inter.isCompact

lemma IsRetrocompact.union (hs : IsRetrocompact s) (ht : IsRetrocompact t) :
    IsRetrocompact (s ∪ t : Set X) :=
  fun _U hUcomp hUopen ↦ union_inter_distrib_right .. ▸ (hs hUcomp hUopen).union (ht hUcomp hUopen)

private lemma supClosed_isRetrocompact : SupClosed {s : Set X | IsRetrocompact s} :=
  fun _s hs _t ht ↦ hs.union ht

lemma IsRetrocompact.finsetSup {ι : Type*} {s : Finset ι} {t : ι → Set X}
    (ht : ∀ i ∈ s, IsRetrocompact (t i)) : IsRetrocompact (s.sup t) := by
  induction' s using Finset.cons_induction with i s ih hi
  · simp
  · rw [Finset.sup_cons]
    exact (ht _ <| by simp).union <| hi <| Finset.forall_of_forall_cons ht

set_option linter.docPrime false in
lemma IsRetrocompact.finsetSup' {ι : Type*} {s : Finset ι} {hs} {t : ι → Set X}
    (ht : ∀ i ∈ s, IsRetrocompact (t i)) : IsRetrocompact (s.sup' hs t) := by
  rw [Finset.sup'_eq_sup]; exact .finsetSup ht

lemma IsRetrocompact.iUnion [Finite ι] {f : ι → Set X} (hf : ∀ i, IsRetrocompact (f i)) :
    IsRetrocompact (⋃ i, f i) := supClosed_isRetrocompact.iSup_mem .empty hf

lemma IsRetrocompact.sUnion {S : Set (Set X)} (hS : S.Finite) (hS' : ∀ s ∈ S, IsRetrocompact s) :
    IsRetrocompact (⋃₀ S) := supClosed_isRetrocompact.sSup_mem hS .empty hS'

lemma IsRetrocompact.biUnion {ι : Type*} {f : ι → Set X} {t : Set ι} (ht : t.Finite)
    (hf : ∀ i ∈ t, IsRetrocompact (f i)) : IsRetrocompact (⋃ i ∈ t, f i) :=
  supClosed_isRetrocompact.biSup_mem ht .empty hf

section T2Space
variable [T2Space X]

lemma IsRetrocompact.inter (hs : IsRetrocompact s) (ht : IsRetrocompact t) :
    IsRetrocompact (s ∩ t : Set X) :=
  fun _U hUcomp hUopen ↦ inter_inter_distrib_right .. ▸ (hs hUcomp hUopen).inter (ht hUcomp hUopen)

private lemma infClosed_isRetrocompact : InfClosed {s : Set X | IsRetrocompact s} :=
  fun _s hs _t ht ↦ hs.inter ht

lemma IsRetrocompact.finsetInf {ι : Type*} {s : Finset ι} {t : ι → Set X}
    (ht : ∀ i ∈ s, IsRetrocompact (t i)) : IsRetrocompact (s.inf t) := by
  induction' s using Finset.cons_induction with i s ih hi
  · simp
  · rw [Finset.inf_cons]
    exact (ht _ <| by simp).inter <| hi <| Finset.forall_of_forall_cons ht

set_option linter.docPrime false in
lemma IsRetrocompact.finsetInf' {ι : Type*} {s : Finset ι} {hs} {t : ι → Set X}
    (ht : ∀ i ∈ s, IsRetrocompact (t i)) : IsRetrocompact (s.inf' hs t) := by
  rw [Finset.inf'_eq_inf]; exact .finsetInf ht

lemma IsRetrocompact.iInter [Finite ι] {f : ι → Set X} (hf : ∀ i, IsRetrocompact (f i)) :
    IsRetrocompact (⋂ i, f i) := infClosed_isRetrocompact.iInf_mem .univ hf

lemma IsRetrocompact.sInter {S : Set (Set X)} (hS : S.Finite) (hS' : ∀ s ∈ S, IsRetrocompact s) :
    IsRetrocompact (⋂₀ S) := infClosed_isRetrocompact.sInf_mem hS .univ hS'

lemma IsRetrocompact.biInter {ι : Type*} {f : ι → Set X} {t : Set ι} (ht : t.Finite)
    (hf : ∀ i ∈ t, IsRetrocompact (f i)) : IsRetrocompact (⋂ i ∈ t, f i) :=
  infClosed_isRetrocompact.biInf_mem ht .univ hf

end T2Space

lemma IsRetrocompact.inter_isOpen (hs : IsRetrocompact s) (ht : IsRetrocompact t)
    (htopen : IsOpen t) : IsRetrocompact (s ∩ t : Set X) :=
  fun _U hUcomp hUopen ↦ inter_assoc .. ▸ hs (ht hUcomp hUopen) (htopen.inter hUopen)

lemma IsRetrocompact.isOpen_inter (hs : IsRetrocompact s) (ht : IsRetrocompact t)
    (hsopen : IsOpen s) : IsRetrocompact (s ∩ t : Set X) :=
  inter_comm .. ▸ ht.inter_isOpen hs hsopen

lemma IsRetrocompact_iff_isSpectralMap_subtypeVal :
    IsRetrocompact s ↔ IsSpectralMap (Subtype.val : s → X) := by
  refine ⟨fun hs ↦ ⟨continuous_subtype_val, fun t htopen htcomp ↦ ?_⟩, fun hs t htcomp htopen ↦ ?_⟩
  · rw [IsEmbedding.subtypeVal.isCompact_iff, image_preimage_eq_inter_range,
      Subtype.range_coe_subtype, setOf_mem_eq, inter_comm]
    exact hs htcomp htopen
  · simpa using (hs.isCompact_preimage_of_isOpen htopen htcomp).image continuous_subtype_val

@[stacks 005B]
lemma IsRetrocompact.image_of_isEmbedding (hs : IsRetrocompact s) (hfemb : IsEmbedding f)
    (hfcomp : IsRetrocompact (range f)) : IsRetrocompact (f '' s) := by
  rintro U hUcomp hUopen
  rw [← image_inter_preimage, ← hfemb.isCompact_iff]
  refine hs ?_ <| hUopen.preimage hfemb.continuous
  rw [hfemb.isCompact_iff, image_preimage_eq_inter_range, inter_comm]
  exact hfcomp hUcomp hUopen

@[stacks 005J "Extracted from the proof"]
lemma IsRetrocompact.preimage_of_isOpenEmbedding {s : Set Y} (hf : IsOpenEmbedding f)
    (hs : IsRetrocompact s) : IsRetrocompact (f ⁻¹' s) := by
  rintro U hUcomp hUopen
  rw [hf.isCompact_iff, image_preimage_inter]
  exact hs (hUcomp.image hf.continuous) <| hf.isOpenMap _ hUopen

@[stacks 09YE "Extracted from the proof"]
lemma IsRetrocompact.preimage_of_isClosedEmbedding {s : Set Y} (hf : IsClosedEmbedding f)
    (hf' : IsCompact (range f)ᶜ) (hs : IsRetrocompact s) : IsRetrocompact (f ⁻¹' s) := by
  rintro U hUcomp hUopen
  have hfUopen : IsOpen (f '' U ∪ (range f)ᶜ) := by
    simpa [← range_diff_image hf.injective, sdiff_eq, compl_inter, union_comm]
      using (hf.isClosedMap _ hUopen.isClosed_compl).isOpen_compl
  have hfUcomp : IsCompact (f '' U ∪ (range f)ᶜ) := (hUcomp.image hf.continuous).union hf'
  simpa [inter_union_distrib_left, inter_left_comm, inter_eq_right.2 (image_subset_range ..),
    hf.isCompact_iff, image_preimage_inter] using (hs hfUcomp hfUopen).inter_left hf.isClosed_range

/-! ### Constructible sets -/

namespace Topology

/-- A constructible set is a set that can be written as the
finite union/finite intersection/complement of open retrocompact sets.

In other words, constructible sets form the boolean subalgebra generated by open retrocompact sets.
-/
def IsConstructible (s : Set X) : Prop :=
  s ∈ BooleanSubalgebra.closure {U | IsOpen U ∧ IsRetrocompact U}

@[simp]
protected lemma IsConstructible.empty : IsConstructible (∅ : Set X) := BooleanSubalgebra.bot_mem

@[simp]
protected lemma IsConstructible.univ : IsConstructible (univ : Set X) := BooleanSubalgebra.top_mem

lemma IsConstructible.union : IsConstructible s → IsConstructible t → IsConstructible (s ∪ t) :=
  BooleanSubalgebra.sup_mem

lemma IsConstructible.inter : IsConstructible s → IsConstructible t → IsConstructible (s ∩ t) :=
  BooleanSubalgebra.inf_mem

lemma IsConstructible.sdiff : IsConstructible s → IsConstructible t → IsConstructible (s \ t) :=
  BooleanSubalgebra.sdiff_mem

lemma IsConstructible.himp : IsConstructible s → IsConstructible t → IsConstructible (s ⇨ t) :=
  BooleanSubalgebra.himp_mem

@[simp] lemma isConstructible_compl : IsConstructible sᶜ ↔ IsConstructible s :=
  BooleanSubalgebra.compl_mem_iff

alias ⟨IsConstructible.of_compl, IsConstructible.compl⟩ := isConstructible_compl

lemma IsConstructible.iUnion [Finite ι] {f : ι → Set X} (hf : ∀ i, IsConstructible (f i)) :
    IsConstructible (⋃ i, f i) := BooleanSubalgebra.iSup_mem hf

lemma IsConstructible.iInter [Finite ι] {f : ι → Set X} (hf : ∀ i, IsConstructible (f i)) :
    IsConstructible (⋂ i, f i) := BooleanSubalgebra.iInf_mem hf

lemma IsConstructible.sUnion {S : Set (Set X)} (hS : S.Finite) (hS' : ∀ s ∈ S, IsConstructible s) :
    IsConstructible (⋃₀ S) := BooleanSubalgebra.sSup_mem hS hS'

lemma IsConstructible.sInter {S : Set (Set X)} (hS : S.Finite) (hS' : ∀ s ∈ S, IsConstructible s) :
    IsConstructible (⋂₀ S) := BooleanSubalgebra.sInf_mem hS hS'

lemma IsConstructible.biUnion {ι : Type*} {f : ι → Set X} {t : Set ι} (ht : t.Finite)
    (hf : ∀ i ∈ t, IsConstructible (f i)) : IsConstructible (⋃ i ∈ t, f i) :=
  BooleanSubalgebra.biSup_mem ht hf

lemma IsConstructible.biInter {ι : Type*} {f : ι → Set X} {t : Set ι} (ht : t.Finite)
    (hf : ∀ i ∈ t, IsConstructible (f i)) : IsConstructible (⋂ i ∈ t, f i) :=
  BooleanSubalgebra.biInf_mem ht hf

lemma _root_.IsRetrocompact.isConstructible (hUopen : IsOpen U) (hUcomp : IsRetrocompact U) :
    IsConstructible U := BooleanSubalgebra.subset_closure ⟨hUopen, hUcomp⟩

/-- An induction principle for constructible sets. If `p` holds for all open retrocompact
sets, and is preserved under union and complement, then `p` holds for all constructible sets. -/
@[elab_as_elim]
lemma IsConstructible.empty_union_induction {p : ∀ s : Set X, IsConstructible s → Prop}
    (open_retrocompact : ∀ U (hUopen : IsOpen U) (hUcomp : IsRetrocompact U),
      p U (BooleanSubalgebra.subset_closure ⟨hUopen, hUcomp⟩))
    (union : ∀ s hs t ht, p s hs → p t ht → p (s ∪ t) (hs.union ht))
    (compl : ∀ s hs, p s hs → p sᶜ hs.compl) {s} (hs : IsConstructible s) : p s hs := by
  induction hs using BooleanSubalgebra.closure_bot_sup_induction with
  | mem U hU => exact open_retrocompact _ hU.1 hU.2
  | bot => exact open_retrocompact _ isOpen_empty .empty
  | sup s hs t ht hs' ht' => exact union _ _ _ _ hs' ht'
  | compl s hs hs' => exact compl _ _ hs'

/-- If `f` is continuous and is such that preimages of retrocompact sets are retrocompact, then
preimages of constructible sets are constructible. -/
@[stacks 005I]
lemma IsConstructible.preimage {s : Set Y} (hfcont : Continuous f)
    (hf : ∀ s, IsRetrocompact s → IsRetrocompact (f ⁻¹' s)) (hs : IsConstructible s) :
    IsConstructible (f ⁻¹' s) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUcomp =>
    exact (hf _ hUcomp).isConstructible <| hUopen.preimage hfcont
  | union s hs t ht hs' ht' => rw [preimage_union]; exact hs'.union ht'
  | compl s hs hs' => rw [preimage_compl]; exact hs'.compl

@[stacks 005J]
lemma IsConstructible.preimage_of_isOpenEmbedding {s : Set Y} (hf : IsOpenEmbedding f)
    (hs : IsConstructible s) : IsConstructible (f ⁻¹' s) :=
  hs.preimage hf.continuous fun _t ht ↦ ht.preimage_of_isOpenEmbedding hf

@[stacks 09YE]
lemma IsConstructible.preimage_of_isClosedEmbedding {s : Set Y} (hf : IsClosedEmbedding f)
    (hf' : IsCompact (range f)ᶜ) (hs : IsConstructible s) : IsConstructible (f ⁻¹' s) :=
  hs.preimage hf.continuous fun _t ht ↦ ht.preimage_of_isClosedEmbedding hf hf'

@[stacks 09YD]
lemma IsConstructible.image_of_isOpenEmbedding (hfopen : IsOpenEmbedding f)
    (hfcomp : IsRetrocompact (range f)) (hs : IsConstructible s) : IsConstructible (f '' s) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUcomp =>
    exact (hUcomp.image_of_isEmbedding hfopen.isEmbedding hfcomp).isConstructible <|
      hfopen.isOpenMap _ hUopen
  | union s hs t ht hs' ht' => rw [image_union]; exact hs'.union ht'
  | compl s hs hs' =>
    rw [← range_diff_image hfopen.injective]
    exact (hfcomp.isConstructible hfopen.isOpen_range).sdiff hs'

@[stacks 09YG]
lemma IsConstructible.image_of_isClosedEmbedding (hf : IsClosedEmbedding f)
    (hfcomp : IsRetrocompact (range f)ᶜ) (hs : IsConstructible s) : IsConstructible (f '' s) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUcomp =>
    have hfU : IsOpen (f '' U ∪ (range f)ᶜ) := by
      simpa [← range_diff_image hf.injective, sdiff_eq, compl_inter, union_comm]
        using (hf.isClosedMap _ hUopen.isClosed_compl).isOpen_compl
    suffices h : IsRetrocompact (f '' U ∪ (range f)ᶜ) by
      simpa [union_inter_distrib_right, inter_eq_left.2 (image_subset_range ..)]
        using (h.isConstructible hfU).sdiff (hfcomp.isConstructible hf.isClosed_range.isOpen_compl)
    rintro V hVcomp hVopen
    rw [union_inter_distrib_right, ← image_inter_preimage]
    exact ((hUcomp (hf.isCompact_preimage hVcomp) (hVopen.preimage hf.continuous)).image
      hf.continuous).union <| hfcomp hVcomp hVopen
  | union s hs t ht hs' ht' => rw [image_union]; exact hs'.union ht'
  | compl s hs hs' =>
    rw [← range_diff_image hf.injective]
    exact (hfcomp.isConstructible hf.isClosed_range.isOpen_compl).of_compl.sdiff hs'

lemma isConstructible_preimage_iff_of_isOpenEmbedding {s : Set Y} (hf : IsOpenEmbedding f)
    (hfcomp : IsRetrocompact (range f)) (hsf : s ⊆ range f) :
    IsConstructible (f ⁻¹' s) ↔ IsConstructible s where
  mp hs := by simpa [image_preimage_eq_range_inter, inter_eq_right.2 hsf]
    using hs.image_of_isOpenEmbedding hf hfcomp
  mpr := .preimage_of_isOpenEmbedding hf

section CompactSpace
variable [CompactSpace X] {P : ∀ s : Set X, IsConstructible s → Prop} {B : Set (Set X)}
  {b : ι → Set X}

lemma _root_.IsRetrocompact.isCompact (hs : IsRetrocompact s) : IsCompact s := by
  simpa using hs CompactSpace.isCompact_univ

/-- Variant of `TopologicalSpace.IsTopologicalBasis.isRetrocompact_iff_isCompact` for a
non-indexed topological basis. -/
lemma _root_.TopologicalSpace.IsTopologicalBasis.isRetrocompact_iff_isCompact'
    (basis : IsTopologicalBasis B) (compact_inter : ∀ U ∈ B, ∀ V ∈ B, IsCompact (U ∩ V))
    (hU : IsOpen U) : IsRetrocompact U ↔ IsCompact U := by
  refine ⟨IsRetrocompact.isCompact, fun hU' {V} hV' hV ↦ ?_⟩
  obtain ⟨s, rfl⟩ := eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open _ basis _ hU' hU
  obtain ⟨t, rfl⟩ := eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open _ basis _ hV' hV
  rw [Set.sUnion_inter_sUnion]
  refine ((s.finite_toSet.image _).prod (t.finite_toSet.image _)).isCompact_biUnion ?_
  simp only [mem_prod, mem_image, Finset.mem_coe, Subtype.exists, exists_and_right, exists_eq_right,
    and_imp, forall_exists_index, Prod.forall]
  exact fun u v hu _ hv _ ↦ compact_inter _ hu _ hv

lemma _root_.TopologicalSpace.IsTopologicalBasis.isRetrocompact_iff_isCompact
    (basis : IsTopologicalBasis (range b)) (compact_inter : ∀ i j, IsCompact (b i ∩ b j))
    (hU : IsOpen U) : IsRetrocompact U ↔ IsCompact U :=
  basis.isRetrocompact_iff_isCompact' (by simpa using compact_inter) hU

/-- Variant of `TopologicalSpace.IsTopologicalBasis.isRetrocompact` for a non-indexed topological
basis. -/
lemma _root_.TopologicalSpace.IsTopologicalBasis.isRetrocompact' (basis : IsTopologicalBasis B)
    (compact_inter : ∀ U ∈ B, ∀ V ∈ B, IsCompact (U ∩ V)) (hU : U ∈ B) : IsRetrocompact U :=
  (basis.isRetrocompact_iff_isCompact' compact_inter <| basis.isOpen hU).2 <| by
    simpa using compact_inter _ hU _ hU

lemma _root_.TopologicalSpace.IsTopologicalBasis.isRetrocompact
    (basis : IsTopologicalBasis (range b)) (compact_inter : ∀ i j, IsCompact (b i ∩ b j)) (i : ι) :
    IsRetrocompact (b i) :=
  (basis.isRetrocompact_iff_isCompact compact_inter <| basis.isOpen <| mem_range_self _).2 <| by
    simpa using compact_inter i i

/-- Variant of `TopologicalSpace.IsTopologicalBasis.isConstructible` for a non-indexed topological
basis. -/
lemma _root_.TopologicalSpace.IsTopologicalBasis.isConstructible' (basis : IsTopologicalBasis B)
    (compact_inter : ∀ U ∈ B, ∀ V ∈ B, IsCompact (U ∩ V)) (hU : U ∈ B) : IsConstructible U :=
  (basis.isRetrocompact' compact_inter hU).isConstructible <| basis.isOpen hU

lemma _root_.TopologicalSpace.IsTopologicalBasis.isConstructible
    (basis : IsTopologicalBasis (range b)) (compact_inter : ∀ i j, IsCompact (b i ∩ b j)) (i : ι) :
    IsConstructible (b i) :=
  (basis.isRetrocompact compact_inter _).isConstructible <| basis.isOpen <| mem_range_self _

@[elab_as_elim]
lemma IsConstructible.induction_of_isTopologicalBasis {ι : Type*} [Nonempty ι] (b : ι → Set X)
    (basis : IsTopologicalBasis (range b)) (compact_inter : ∀ i j, IsCompact (b i ∩ b j))
    (sdiff : ∀ i s (hs : Set.Finite s), P (b i \ ⋃ j ∈ s, b j)
      ((basis.isConstructible compact_inter _).sdiff <| .biUnion hs fun _ _ ↦
        basis.isConstructible compact_inter _))
    (union : ∀ s hs t ht, P s hs → P t ht → P (s ∪ t) (hs.union ht))
    (s : Set X) (hs : IsConstructible s) : P s hs := by
  induction s, hs using BooleanSubalgebra.closure_sdiff_sup_induction with
  | isSublattice =>
    exact ⟨fun s hs t ht ↦ ⟨hs.1.union ht.1, hs.2.union ht.2⟩,
      fun s hs t ht ↦ ⟨hs.1.inter ht.1, hs.2.inter_isOpen ht.2 ht.1⟩⟩
  | bot_mem => exact ⟨isOpen_empty, .empty⟩
  | top_mem => exact ⟨isOpen_univ, .univ⟩
  | sdiff U hU V hV =>
    have := isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis _ basis
        fun i ↦ by simpa using compact_inter i i
    obtain ⟨s, hs, rfl⟩ := (this _).1 ⟨hU.2.isCompact, hU.1⟩
    obtain ⟨t, ht, rfl⟩ := (this _).1 ⟨hV.2.isCompact, hV.1⟩
    simp_rw [iUnion_diff]
    induction s, hs using Set.Finite.induction_on with
    | empty => simpa using sdiff (Classical.arbitrary _) {Classical.arbitrary _}
    | @insert i s hi hs ih =>
      simp_rw [biUnion_insert]
      exact union _ _ _
        (.biUnion hs fun i _ ↦ (basis.isConstructible compact_inter _).sdiff <|
          .biUnion ht fun j _ ↦ basis.isConstructible compact_inter _)
        (sdiff _ _ ht)
        (ih ⟨isOpen_biUnion fun  _ _ ↦ basis.isOpen ⟨_, rfl⟩, .biUnion hs
          fun i _ ↦ basis.isRetrocompact compact_inter _⟩)
  | sup s _ t _ hs' ht' => exact union _ _ _ _ hs' ht'

end CompactSpace

/-! ### Locally constructible sets -/

/-- A set in a topological space is locally constructible, if every point has a neighborhood on
which the set is constructible. -/
@[stacks 005G]
def IsLocallyConstructible (s : Set X) : Prop := ∀ x, ∃ U ∈ 𝓝 x, IsOpen U ∧ IsConstructible (U ↓∩ s)

lemma IsConstructible.isLocallyConstructible (hs : IsConstructible s) : IsLocallyConstructible s :=
  fun _ ↦ ⟨univ, by simp, by simp,
    (isConstructible_preimage_iff_of_isOpenEmbedding isOpen_univ.isOpenEmbedding_subtypeVal
      (by simp) (by simp)).2 hs⟩

lemma _root_.IsRetrocompact.isLocallyConstructible (hUopen : IsOpen U) (hUcomp : IsRetrocompact U) :
    IsLocallyConstructible U := (hUcomp.isConstructible hUopen).isLocallyConstructible

@[simp] protected lemma IsLocallyConstructible.empty : IsLocallyConstructible (∅ : Set X) :=
  IsConstructible.empty.isLocallyConstructible

@[simp] protected lemma IsLocallyConstructible.univ : IsLocallyConstructible (univ : Set X) :=
  IsConstructible.univ.isLocallyConstructible

lemma IsLocallyConstructible.inter (hs : IsLocallyConstructible s) (ht : IsLocallyConstructible t) :
    IsLocallyConstructible (s ∩ t) := by
  rintro x
  obtain ⟨U, hxU, hU, hsU⟩ := hs x
  obtain ⟨V, hxV, hV, htV⟩ := ht x
  refine ⟨U ∩ V, Filter.inter_mem hxU hxV, hU.inter hV, ?_⟩
  change IsConstructible
    (inclusion inter_subset_left ⁻¹' (U ↓∩ s) ∩ inclusion inter_subset_right ⁻¹' (V ↓∩ t))
  exact .inter (hsU.preimage_of_isOpenEmbedding <| .inclusion _ <|
      .preimage continuous_subtype_val <| hU.inter hV)
    (htV.preimage_of_isOpenEmbedding <| .inclusion _ <|
      .preimage continuous_subtype_val <| hU.inter hV )

lemma IsLocallyConstructible.finsetInf {ι : Type*} {s : Finset ι} {t : ι → Set X}
    (ht : ∀ i ∈ s, IsLocallyConstructible (t i)) : IsLocallyConstructible (s.inf t) := by
  induction' s using Finset.cons_induction with i s ih hi
  · simp
  · rw [Finset.inf_cons]
    exact (ht _ <| by simp).inter <| hi <| Finset.forall_of_forall_cons ht

set_option linter.docPrime false in
lemma IsLocallyConstructible.finsetInf' {ι : Type*} {s : Finset ι} {hs} {t : ι → Set X}
    (ht : ∀ i ∈ s, IsLocallyConstructible (t i)) : IsLocallyConstructible (s.inf' hs t) := by
  rw [Finset.inf'_eq_inf]; exact .finsetInf ht

private lemma infClosed_isLocallyConstructible : InfClosed {s : Set X | IsLocallyConstructible s} :=
  fun _s hs _t ht ↦ hs.inter ht

lemma IsLocallyConstructible.iInter [Finite ι] {f : ι → Set X}
    (hf : ∀ i, IsLocallyConstructible (f i)) : IsLocallyConstructible (⋂ i, f i) :=
  infClosed_isLocallyConstructible.iInf_mem .univ hf

lemma IsLocallyConstructible.sInter {S : Set (Set X)} (hS : S.Finite)
    (hS' : ∀ s ∈ S, IsLocallyConstructible s) : IsLocallyConstructible (⋂₀ S) :=
  infClosed_isLocallyConstructible.sInf_mem hS .univ hS'

end Topology
