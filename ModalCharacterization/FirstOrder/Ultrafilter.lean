/-
Modal Characterization in Lean 4. Released under Apache-2.0; see LICENSE.
Reuses mathlib filter APIs by Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
and the countable-intersection API by Yury Kudryashov.
-/
module

public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Order.Filter.CountableInter

@[expose] public section

namespace ModalCharacterization.FirstOrder

open Filter Set

/-- Witness calculation for Blue Book Example 2.72 (2010 fourth corrected
printing, p. 106): the complements of all singleton subsets of ℕ have empty
intersection. These are the book's literal witnesses, not decreasing tails. -/
theorem iInter_nat_singleton_compl : (⋂ n : ℕ, ({n} : Set ℕ)ᶜ) = ∅ := by
  ext n
  simp

/-- Blue Book Example 2.72 (2010 fourth corrected printing, p. 106): an
ultrafilter on ℕ containing no singleton is not closed under countable
intersections. Reuses the negation of mathlib's `CountableInterFilter` rather
than introducing another completeness predicate. -/
theorem not_countableInterFilter_of_no_singleton (U : Ultrafilter ℕ)
    (hU : ∀ n, ({n} : Set ℕ) ∉ U) : ¬ CountableInterFilter (U : Filter ℕ) := by
  intro h
  let := h
  have hm : ∀ n : ℕ, ({n} : Set ℕ)ᶜ ∈ (U : Filter ℕ) :=
    fun n => U.compl_mem_iff_notMem.mpr (hU n)
  have hi := countable_iInter_mem.mpr hm
  rw [iInter_nat_singleton_compl] at hi
  exact Filter.empty_notMem (U : Filter ℕ) hi

/-- Concrete existence input for Blue Book Example 2.72 / Thm. 2.74
(2010 printing, p. 106). Mathlib's `hyperfilter ℕ` extends the cofinite filter
and contains no finite set, so it is countably incomplete. This reuses the
existing ultrafilter existence construction underlying Exercise 2.5.4. -/
theorem nat_hyperfilter_not_countableInterFilter :
    ¬ CountableInterFilter (Filter.hyperfilter ℕ : Filter ℕ) := by
  apply not_countableInterFilter_of_no_singleton
  intro n
  exact (Set.finite_singleton n).notMem_hyperfilter

/-- Auxiliary for Chang–Keisler, Model Theory, third edition (1990), third
impression (1992), Thm. 6.1.1, p. 385: extract the descending empty-intersection
sequence used in the diagonal construction. Supports Blue Book Lemma 2.73. -/
theorem exists_antitone_empty_inter_of_not_countableInterFilter
    {I : Type*} (U : Ultrafilter I)
    (hU : ¬ CountableInterFilter (U : Filter I)) :
    ∃ s : ℕ → Set I, s 0 = univ ∧ Antitone s ∧
      (∀ n, s n ∈ (U : Filter I)) ∧ (⋂ n, s n) = ∅ := by
  classical
  have hex : ∃ S : Set (Set I), S.Countable ∧
      (∀ s ∈ S, s ∈ (U : Filter I)) ∧ ⋂₀ S ∉ (U : Filter I) := by
    by_contra hn
    push Not at hn
    exact hU ⟨fun S hS hm => hn S hS hm⟩
  obtain ⟨S, hS, hm, hi⟩ := hex
  have hne : S.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn, sInter_empty] at hi
    exact hi Filter.univ_mem
  obtain ⟨f, hf⟩ := hS.exists_eq_range hne
  have hfm : ∀ n, f n ∈ (U : Filter I) := by
    intro n
    apply hm
    rw [hf]
    exact mem_range_self n
  have hc : (⋂₀ S)ᶜ ∈ (U : Filter I) := U.compl_mem_iff_notMem.mpr hi
  let s : ℕ → Set I := fun n => (⋂ k ∈ Finset.range n, f k ∩ (⋂₀ S)ᶜ)
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · simp [s]
  · intro n m hnm x hx
    simp only [s, mem_iInter] at hx ⊢
    intro k hk
    exact hx k (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hnm))
  · intro n
    apply (Filter.biInter_mem (Finset.finite_toSet (Finset.range n))).mpr
    intro k hk
    exact inter_mem (hfm k) hc
  · apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hall : ∀ k, x ∈ f k ∩ (⋂₀ S)ᶜ := by
      intro k
      have h := mem_iInter.mp hx (k + 1)
      exact mem_iInter.mp (mem_iInter.mp h k) (Finset.mem_range.mpr (Nat.lt_succ_self k))
    apply (hall 0).2
    rw [hf, sInter_range]
    exact mem_iInter.mpr (fun k => (hall k).1)

/-- Auxiliary finite-cutoff step of Chang–Keisler Thm. 6.1.1 (third edition,
1990; third impression, 1992), p. 385: every index has a greatest level in a
descending sequence starting at the whole space and having empty intersection.
This is the book's n(i); no ultrafilter assumption is needed for this step. -/
theorem exists_greatest_mem_of_antitone_empty_inter
    {I : Type*} (s : ℕ → Set I) (hzero : s 0 = univ)
    (hanti : Antitone s) (hempty : (⋂ n, s n) = ∅) (i : I) :
    ∃ n, i ∈ s n ∧ ∀ m, i ∈ s m → m ≤ n := by
  classical
  have hex : ∃ n, i ∉ s n := by
    by_contra hn
    push Not at hn
    have hi := mem_iInter.mpr hn
    rw [hempty] at hi
    exact hi
  have hpos : 0 < Nat.find hex := by
    apply (Nat.find_pos hex).mpr
    simp [hzero]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  refine ⟨n, ?_, ?_⟩
  · have hlt : n < Nat.find hex := by omega
    exact not_not.mp (Nat.find_min hex hlt)
  · intro m hm
    by_contra h
    have hle : Nat.find hex ≤ m := by omega
    exact Nat.find_spec hex (hanti hle hm)


end ModalCharacterization.FirstOrder
