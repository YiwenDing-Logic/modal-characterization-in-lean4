/- Modal Characterization in Lean 4. Released under Apache-2.0; see LICENSE.
Reuses mathlib model theory and Los semantics by Aaron Anderson. -/
module
public import ModalCharacterization.FirstOrder.Ultrafilter
public import ModalCharacterization.FirstOrder.Ultrapower
public import ModalCharacterization.FirstOrder.Saturation
public import Mathlib.ModelTheory.Encoding
@[expose] public section
open Filter Set
open _root_.FirstOrder _root_.FirstOrder.Language
namespace ModalCharacterization.FirstOrder
/-- Auxiliary diagonal selection for Chang–Keisler Thm. 6.1.1, third edition
(1990), third impression (1992), p. 385. Local solutions of finite prefixes on
large sets yield one function satisfying each constraint almost everywhere.
This is the selection step underlying Blue Book Lemma 2.73, not saturation itself. -/
theorem exists_eventually_all_of_eventually_finite
    {I : Type*} {M : I → Type*} [∀ i, Nonempty (M i)]
    (U : Ultrafilter I) (hU : ¬ CountableInterFilter (U : Filter I))
    (P : ℕ → (i : I) → M i → Prop)
    (hP : ∀ n, ∀ᶠ i in U, ∃ x, ∀ k < n, P k i x) :
    ∃ f : ∀ i, M i, ∀ k, ∀ᶠ i in U, P k i (f i) := by
  classical
  obtain ⟨s, hs0, hsa, hsm, hse⟩ :=
    exists_antitone_empty_inter_of_not_countableInterFilter U hU
  let t : ℕ → Set I := fun n => s n ∩ {i | ∃ x, ∀ k < n, P k i x}
  have ht0 : t 0 = univ := by
    ext i
    simp [t, hs0]
  have hta : Antitone t := by
    intro n m hnm i hi
    obtain ⟨hs, x, hx⟩ := hi
    exact ⟨hsa hnm hs, x, fun k hk => hx k (lt_of_lt_of_le hk hnm)⟩
  have htm : ∀ n, t n ∈ (U : Filter I) := fun n => inter_mem (hsm n) (hP n)
  have hte : (⋂ n, t n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have : i ∈ ⋂ n, s n := mem_iInter.mpr (fun n => (mem_iInter.mp hi n).1)
    rw [hse] at this
    exact this
  choose level hlevel hmax using
    (fun i => exists_greatest_mem_of_antitone_empty_inter t ht0 hta hte i)
  choose f hf using (fun i => (hlevel i).2)
  refine ⟨f, fun k => ?_⟩
  filter_upwards [htm (k + 1)] with i hi
  exact hf i k (lt_of_lt_of_le (Nat.lt_succ_self k) (hmax i (k + 1) hi))

/-- Formula-sequence realization step of Chang–Keisler Thm. 6.1.1 (third edition
1990, third impression1992, pp. 384–385). Reuses mathlib's formula-level Los
 theorem in both directions. Finite prefixes are realized in the ultraproduct;
no countability of the entire language or bound on factor sizes is needed here.
Parameters and conversion of a countable set to a sequence are later steps. -/
theorem ultraproduct_realizes_sequence
    {L : Language} {I : Type*} (M : I → Type*)
    [∀ i, L.Structure (M i)] [∀ i, Nonempty (M i)]
    (U : Ultrafilter I) (hU : ¬ CountableInterFilter (U : Filter I))
    {β : Type*} (φ : ℕ → L.Formula β)
    (hφ : ∀ n, ∃ v : β → (U : Filter I).Product M,
      ∀ k < n, (φ k).Realize v) :
    ∃ v : β → (U : Filter I).Product M, ∀ k, (φ k).Realize v := by
  classical
  choose v hv using hφ
  let f : ℕ → β → ∀ i, M i := fun n b => Quotient.out (v n b)
  have hf : ∀ n b, (f n b : (U : Filter I).Product M) = v n b :=
    fun n b => Quotient.out_eq (v n b)
  have hlocal : ∀ n, ∀ᶠ i in U, ∃ x : β → M i,
      ∀ k < n, (φ k).Realize x := by
    intro n
    have hk : ∀ k ∈ Finset.range n, ∀ᶠ i in U,
        (φ k).Realize (fun b => f n b i) := by
      intro k hk
      apply (Ultraproduct.realize_formula_cast (M := M) (u := U) (φ k) (f n)).mp
      have he : (fun b => (f n b : (U : Filter I).Product M)) = v n := funext (hf n)
      rw [he]
      exact hv n k (Finset.mem_range.mp hk)
    have hall := (Filter.eventually_all_finset (Finset.range n)).mpr hk
    filter_upwards [hall] with i hi
    exact ⟨fun b => f n b i, fun k hk => hi k (Finset.mem_range.mpr hk)⟩
  obtain ⟨g, hg⟩ := exists_eventually_all_of_eventually_finite
    (M := fun i => β → M i) U hU (fun k i x => (φ k).Realize x) hlocal
  refine ⟨fun b => ((fun i => g i b) : (U : Filter I).Product M), fun k => ?_⟩
  exact (Ultraproduct.realize_formula_cast (M := M) (u := U) (φ k) (fun b i => g i b)).mpr (hg k)

/-- Countable-set version of the realization step in Chang–Keisler Thm. 6.1.1
(third edition1990, third impression1992, p. 385). Empty and finite sets are
included. Parameter interpretations are handled separately. -/
theorem ultraproduct_realizes_countable
    {L : Language} {I : Type*} (M : I → Type*)
    [∀ i, L.Structure (M i)] [∀ i, Nonempty (M i)]
    (U : Ultrafilter I) (hU : ¬ CountableInterFilter (U : Filter I))
    (Γ : Set (L.Formula (Fin 1))) (hc : Γ.Countable)
    (hΓ : FinitelyRealized ((U : Filter I).Product M) Γ) :
    ∃ v : Fin 1 → (U : Filter I).Product M, ∀ φ ∈ Γ, φ.Realize v := by
  classical
  by_cases hn : Γ.Nonempty
  · obtain ⟨φ, hφ⟩ := hc.exists_eq_range hn
    have hprefix : ∀ n, ∃ v : Fin 1 → (U : Filter I).Product M,
        ∀ k < n, (φ k).Realize v := by
      intro n
      obtain ⟨v, hv⟩ := hΓ ((Finset.range n).image φ) (by
        intro ψ hψ
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hψ
        rw [hφ]
        exact Set.mem_range_self k)
      exact ⟨v, fun k hk => hv _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩)⟩
    obtain ⟨v, hv⟩ := ultraproduct_realizes_sequence M U hU φ hprefix
    refine ⟨v, ?_⟩
    intro ψ hψ
    rw [hφ] at hψ
    obtain ⟨k, rfl⟩ := hψ
    exact hv k
  · refine ⟨fun _ => Classical.choice inferInstance, ?_⟩
    intro φ hφ
    exact (hn ⟨φ, hφ⟩).elim

/-- Auxiliary parameter encoding for Chang–Keisler Thm. 6.1.1 (third edition
1990, third impression 1992, p. 384), the expansion-by-parameters step.
A parameter formula is translated to an original-language formula whose extra
free variables are assigned fixed representatives of the parameters. This is
an encoding lemma, not the saturation conclusion. Reuses mathlib's
`constantsVarsEquiv` semantics and formula-level Łoś theorem (Aaron Anderson). -/
theorem ultraproduct_realize_parameters_cast
    {L : Language} {I : Type*} (M : I → Type*)
    [∀ i, L.Structure (M i)] [∀ i, Nonempty (M i)]
    (U : Ultrafilter I) (A : Set ((U : Filter I).Product M))
    (r : A → ∀ i, M i)
    (hr : ∀ a, (r a : (U : Filter I).Product M) = (a : (U : Filter I).Product M))
    {β : Type*} (φ : L[[A]].Formula β) (x : β → ∀ i, M i) :
    (φ.Realize (M := (U : Filter I).Product M) fun b => (x b : (U : Filter I).Product M)) ↔
      ∀ᶠ i in U, Formula.Realize (BoundedFormula.constantsVarsEquiv φ)
        (Sum.elim (fun a => r a i) (fun b => x b i)) := by
  have hsem := BoundedFormula.realize_constantsVarsEquiv
    (M := (U : Filter I).Product M) (φ := φ)
    (v := fun b => (x b : (U : Filter I).Product M)) (xs := Fin.elim0)
  have heq :
      (fun z => ((Sum.elim r x z : ∀ i, M i) : (U : Filter I).Product M)) =
        Sum.elim (fun a : A => (L.con a : (U : Filter I).Product M))
          (fun b => (x b : (U : Filter I).Product M)) := by
    funext z
    cases z with
    | inl a =>
      change (r a : (U : Filter I).Product M) = (a : (U : Filter I).Product M)
      exact hr a
    | inr b => rfl
  have hlos := Ultraproduct.realize_formula_cast (M := M) (u := U)
    (BoundedFormula.constantsVarsEquiv φ) (Sum.elim r x)
  rw [heq] at hlos
  change Formula.Realize (BoundedFormula.constantsVarsEquiv φ) _ ↔ φ.Realize _ at hsem
  have hassign : ∀ i, (fun z => Sum.elim r x z i) =
      Sum.elim (fun a => r a i) (fun b => x b i) := by
    intro i
    funext z
    cases z <;> rfl
  simp_rw [hassign] at hlos
  exact hsem.symm.trans hlos


/-- Parameter-preserving sequence realization for Chang–Keisler Thm. 6.1.1
(third edition1990, third impression1992, pp. 384–385). Representatives of the
parameters remain fixed throughout the diagonal construction. -/
theorem ultraproduct_realizes_parameter_sequence
    {L : Language} {I : Type*} (M : I → Type*)
    [∀ i, L.Structure (M i)] [∀ i, Nonempty (M i)]
    (U : Ultrafilter I) (hU : ¬ CountableInterFilter (U : Filter I))
    (A : Set ((U : Filter I).Product M))
    (φ : ℕ → L[[A]].Formula (Fin 1))
    (hφ : ∀ n, ∃ v : Fin 1 → (U : Filter I).Product M,
      ∀ k < n, (φ k).Realize v) :
    ∃ v : Fin 1 → (U : Filter I).Product M, ∀ k, (φ k).Realize v := by
  classical
  let r : A → ∀ i, M i := fun a => Quotient.out (a : (U : Filter I).Product M)
  have hr : ∀ a, (r a : (U : Filter I).Product M) = (a : (U : Filter I).Product M) :=
    fun a => Quotient.out_eq _
  choose v hv using hφ
  let f : ℕ → Fin 1 → ∀ i, M i := fun n b => Quotient.out (v n b)
  have hf : ∀ n b, (f n b : (U : Filter I).Product M) = v n b :=
    fun n b => Quotient.out_eq (v n b)
  let P := fun k i (x : Fin 1 → M i) =>
    Formula.Realize (BoundedFormula.constantsVarsEquiv (φ k))
      (Sum.elim (fun a => r a i) x)
  have hlocal : ∀ n, ∀ᶠ i in U, ∃ x : Fin 1 → M i, ∀ k < n, P k i x := by
    intro n
    have hk : ∀ k ∈ Finset.range n, ∀ᶠ i in U, P k i (fun b => f n b i) := by
      intro k hk
      apply (ultraproduct_realize_parameters_cast M U A r hr (φ k) (f n)).mp
      have he : (fun b => (f n b : (U : Filter I).Product M)) = v n := funext (hf n)
      rw [he]
      exact hv n k (Finset.mem_range.mp hk)
    have hall := (Filter.eventually_all_finset (Finset.range n)).mpr hk
    filter_upwards [hall] with i hi
    exact ⟨fun b => f n b i, fun k hk => hi k (Finset.mem_range.mpr hk)⟩
  obtain ⟨g, hg⟩ := exists_eventually_all_of_eventually_finite
    (M := fun i => Fin 1 → M i) U hU P hlocal
  refine ⟨fun b => ((fun i => g i b) : (U : Filter I).Product M), fun k => ?_⟩
  exact (ultraproduct_realize_parameters_cast M U A r hr (φ k)
    (fun b i => g i b)).mpr (hg k)

/-- Countable partial-type realization with the original parameters, auxiliary
for Chang–Keisler Thm. 6.1.1 (third edition1990, third impression1992, pp384–385).
Only the formula SET is countable here; no bound on the whole parameter set
or language is needed. This does not claim saturation for uncountable types. -/
theorem ultraproduct_realizes_countable_parameters
    {L : Language} {I : Type*} (M : I → Type*)
    [∀ i, L.Structure (M i)] [∀ i, Nonempty (M i)]
    (U : Ultrafilter I) (hU : ¬ CountableInterFilter (U : Filter I))
    (A : Set ((U : Filter I).Product M))
    (Γ : Set (L[[A]].Formula (Fin 1))) (hc : Γ.Countable)
    (hΓ : FinitelyRealized ((U : Filter I).Product M) Γ) :
    ∃ v : Fin 1 → (U : Filter I).Product M, ∀ φ ∈ Γ, φ.Realize v := by
  classical
  by_cases hn : Γ.Nonempty
  · obtain ⟨φ, hφ⟩ := hc.exists_eq_range hn
    have hprefix : ∀ n, ∃ v : Fin 1 → (U : Filter I).Product M,
        ∀ k < n, (φ k).Realize v := by
      intro n
      obtain ⟨v, hv⟩ := hΓ ((Finset.range n).image φ) (by
        intro ψ hψ
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hψ
        rw [hφ]
        exact Set.mem_range_self k)
      exact ⟨v, fun k hk => hv _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩)⟩
    obtain ⟨v, hv⟩ := ultraproduct_realizes_parameter_sequence M U hU A φ hprefix
    refine ⟨v, ?_⟩
    intro ψ hψ
    rw [hφ] at hψ
    obtain ⟨k, rfl⟩ := hψ
    exact hv k
  · refine ⟨fun _ => Classical.choice inferInstance, ?_⟩
    intro φ hφ
    exact (hn ⟨φ, hφ⟩).elim

/-- Finite-parameter consequence of Chang–Keisler Thm. 6.1.1 (third edition1990,
third impression1992, pp384–385): a countably incomplete ultraproduct in a
countable language is omega-saturated. The book proves the stronger omega_1
saturation assertion; this declaration uses the project's finite-parameter
complete-one-type definition and is sufficient for Blue Book Lemma 2.73. -/
theorem ultraproduct_isOmegaSaturated
    (L : Language) [Countable L.Symbols] {I : Type*} (M : I → Type*)
    [∀ i, L.Structure (M i)] [∀ i, Nonempty (M i)]
    (U : Ultrafilter I) (hU : ¬ CountableInterFilter (U : Filter I)) :
    IsOmegaSaturated L ((U : Filter I).Product M) := by
  rw [isOmegaSaturated_iff_realizes_finitelyRealized]
  intro A hA Γ hΓ
  let := hA.fintype
  exact ultraproduct_realizes_countable_parameters M U hU A Γ (Set.to_countable Γ) hΓ

/-- Blue Book Lemma 2.73 (2010 fourth corrected printing, p106), proved by
specializing Chang–Keisler Thm. 6.1.1 (third edition1990, third impression1992,
pp384–385) to a constant family. Arbitrary domain and index universes; countable
language and countable incompleteness are explicit. No saturation hypothesis. -/
theorem ultrapower_isOmegaSaturated
    (L : Language) [Countable L.Symbols] (M : Type*)
    [L.Structure M] [Nonempty M] {I : Type*}
    (U : Ultrafilter I) (hU : ¬ CountableInterFilter (U : Filter I)) :
    IsOmegaSaturated L ((U : Filter I).Product (fun _ : I => M)) :=
  ultraproduct_isOmegaSaturated L (fun _ : I => M) U hU

end ModalCharacterization.FirstOrder
