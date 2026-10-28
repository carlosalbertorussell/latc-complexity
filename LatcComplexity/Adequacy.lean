import LatcComplexity.General

/-!
# Adequacy: the word-encoded problems are latc-check's `Finset` problems

An instance `I = (d, S, T)` of `LatcComplexity.General` denotes a table in the model of
`LatcFormal.Basic` (Paper A, Section 3):

* attributes `Fin n`, with `n = d.length`, and declared domains `Fin dᵢ`;
* the constraint predicate `I.con`: a tuple satisfies every clause of `S`, a condition `(i, v)`
  holding when attribute `i` exists and takes the value `v` (`con_cond_iff`);
* the condition set `I.table`: the tuples whose list of values is a row of `T` (rows of other
  lengths or with values outside the domains denote no tuple).

Main results:

* `mem_MissingNonempty_iff`: `I ∈ MissingNonempty ↔ (missing I.con I.table).Nonempty`.
* `mem_Complete_iff`: `I ∈ Complete ↔ missing I.con I.table = ∅`.
* `missingNonempty_finset_npComplete`, `complete_finset_coNPComplete`: Proposition 5, stated on
  latc-check's `Latc.missing`.
-/

namespace Latc.PaperD.General

open Cslib.Complexity

/-! ### The tuple of a state -/

/-- The number of attributes. -/
abbrev Inst.n (I : Inst) : ℕ := I.1.length

/-- The declared domain of attribute `i`: the values `0, …, dᵢ - 1`. -/
abbrev Inst.Dom (I : Inst) (i : Fin I.n) : Type := Fin (I.1.get i)

/-- The list of values of a condition tuple. -/
def Inst.toList (I : Inst) (x : ∀ i, I.Dom i) : List ℕ := List.ofFn fun i => (x i).val

@[simp] lemma Inst.length_toList (I : Inst) (x : ∀ i, I.Dom i) : (I.toList x).length = I.n := by
  simp [Inst.toList]

lemma Inst.getElem?_toList (I : Inst) (x : ∀ i, I.Dom i) (i : ℕ) :
    (I.toList x)[i]? = if h : i < I.n then some (x ⟨i, h⟩).val else none := by
  split_ifs with h
  · simp [Inst.toList, h]
  · simp [Inst.toList, h]

lemma Inst.toList_injective (I : Inst) : Function.Injective I.toList := by
  intro x y h
  funext i
  have := congrArg (·[i.val]?) h
  simp only [Inst.getElem?_toList, i.isLt, dite_true, Option.some.injEq] at this
  exact Fin.ext this

/-- The list of values of a tuple is a state of the declared domains. -/
lemma Inst.inDomains_toList (I : Inst) (x : ∀ i, I.Dom i) : InDomains I.1 (I.toList x) := by
  refine List.forall₂_iff_get.2 ⟨by simp, fun i h₁ h₂ => ?_⟩
  simp [Inst.toList]

/-- Every state of the declared domains is the list of values of a tuple. -/
lemma Inst.exists_toList_eq (I : Inst) {s : List ℕ} (hs : InDomains I.1 s) :
    ∃ x : ∀ i, I.Dom i, I.toList x = s := by
  obtain ⟨hlen, hlt⟩ := List.forall₂_iff_get.1 hs
  refine ⟨fun i => ⟨s.get ⟨i, hlen ▸ i.isLt⟩, hlt _ _ i.isLt⟩, ?_⟩
  refine List.ext_get (by simp [hlen]) fun i h₁ h₂ => ?_
  simp [Inst.toList]

/-! ### The table denoted by an instance -/

/-- The constraint predicate of the instance, on condition tuples. -/
def Inst.con (I : Inst) (x : ∀ i, I.Dom i) : Prop := Valid I.2.1 (I.toList x)

instance (I : Inst) : DecidablePred I.con := fun x =>
  decidable_of_iff (I.2.1.all fun c => c.any (condHoldsB (I.toList x))) (by
    simp [Inst.con, Valid, condHoldsB_iff])

/-- The condition set of T₀: the tuples whose list of values is a row of `T`. -/
def Inst.table (I : Inst) : Finset (∀ i, I.Dom i) :=
  Finset.univ.filter fun x => I.toList x ∈ I.2.2

/-- A condition `(i, v)` is the condition Aᵢ = v of Paper A: attribute `i` exists and the tuple
takes the value `v` there. -/
theorem con_cond_iff (I : Inst) (x : ∀ i, I.Dom i) (a : Cond) :
    CondHolds (I.toList x) a ↔ ∃ h : a.1 < I.n, (x ⟨a.1, h⟩).val = a.2 := by
  simp only [CondHolds, Inst.getElem?_toList]
  split_ifs with h <;> simp [h]

/-- The constraint predicate is the conjunction of the clause constraints of `S`, each a
disjunction of conditions Aᵢ = v. -/
theorem con_iff (I : Inst) (x : ∀ i, I.Dom i) :
    I.con x ↔ ∀ c ∈ I.2.1, ∃ a ∈ c, ∃ h : a.1 < I.n, (x ⟨a.1, h⟩).val = a.2 := by
  simp only [Inst.con, Valid, con_cond_iff]

lemma mem_missing_iff (I : Inst) (x : ∀ i, I.Dom i) :
    x ∈ missing I.con I.table ↔ Valid I.2.1 (I.toList x) ∧ I.toList x ∉ I.2.2 := by
  simp [missing, validSpace, Inst.table, Inst.con]

/-! ### Adequacy -/

/-- **Adequacy, non-emptiness.** An instance is in `MissingNonempty` exactly when the missing set
M(T₀) of the table it denotes is non-empty. -/
theorem mem_MissingNonempty_iff (I : Inst) :
    I ∈ MissingNonempty ↔ (missing I.con I.table).Nonempty := by
  constructor
  · rintro ⟨s, hs, hv, hT⟩
    obtain ⟨x, rfl⟩ := I.exists_toList_eq hs
    exact ⟨x, (mem_missing_iff I x).2 ⟨hv, hT⟩⟩
  · rintro ⟨x, hx⟩
    rw [mem_missing_iff] at hx
    exact ⟨I.toList x, I.inDomains_toList x, hx.1, hx.2⟩

/-- **Adequacy, completeness.** An instance is in `Complete` exactly when the table it denotes is
complete: M(T₀) = ∅. -/
theorem mem_Complete_iff (I : Inst) : I ∈ Complete ↔ missing I.con I.table = ∅ := by
  rw [Complete, Set.mem_compl_iff, mem_MissingNonempty_iff, Finset.not_nonempty_iff_eq_empty]

/-- The tuples of M(T₀) correspond one to one (`Inst.toList_injective`) to the witnesses of
`MissingNonempty`: their lists of values are exactly the valid states of the declared domains that
are not rows of T₀. -/
theorem coe_missing_map_toList (I : Inst) :
    (((missing I.con I.table).map ⟨I.toList, I.toList_injective⟩ : Finset (List ℕ)) :
      Set (List ℕ)) = {s | InDomains I.1 s ∧ Valid I.2.1 s ∧ s ∉ I.2.2} := by
  ext s
  simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Function.Embedding.coeFn_mk,
    Set.mem_ofPred_eq, mem_missing_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨I.inDomains_toList x, hx⟩
  · rintro ⟨hs, hx⟩
    obtain ⟨x, rfl⟩ := I.exists_toList_eq hs
    exact ⟨x, hx, rfl⟩

/-! ### Proposition 5 on latc-check's `Finset` model -/

/-- **Proposition 5, NP part:** deciding whether the missing set `Latc.missing` of a table with
clause constraints over finite domains is non-empty is NP-complete. -/
theorem missingNonempty_finset_npComplete :
    NPComplete encInst {I : Inst | (missing I.con I.table).Nonempty} := by
  have : {I : Inst | (missing I.con I.table).Nonempty} = MissingNonempty :=
    Set.ext fun I => (mem_MissingNonempty_iff I).symm
  rw [this]
  exact MissingNonempty_npComplete

/-- **Proposition 5, coNP part:** deciding whether a table with clause constraints over finite
domains is complete (`Latc.missing = ∅`) is coNP-complete. -/
theorem complete_finset_coNPComplete :
    coNPComplete encInst {I : Inst | missing I.con I.table = ∅} := by
  have : {I : Inst | missing I.con I.table = ∅} = Complete :=
    Set.ext fun I => (mem_Complete_iff I).symm
  rw [this]
  exact Complete_coNPComplete

end Latc.PaperD.General
