import LatcComplexity.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith

/-!
# The tractable side: no constraints, or a fixed number of attributes

The hardness theorems reduce SAT to instances with constraints (one clause per clause of the
formula) and as many attributes as the formula has variables. Dropping either ingredient makes the
problems polynomial-time. All statements are on latc-check's `Latc.missing` and use the binary
encoding `encInstBin`; the unary-index versions follow (`mem_P_of_mem_P_bin`).

(a) No constraints (`S = []`), any number of attributes:

* `missingCount_eq_of_noConstraints`: |M(T₀)| = ∏ dᵢ − (distinct rows of T₀ inside the domains).
* `missingCountNoConstraints_polyTime`: this count is polynomial-time computable. ∏ dᵢ may be
  exponential in the input length, but its binary encoding is no longer than those of the dᵢ
  together (`length_encNat_mul_le`), so it is computed exactly in binary.
* `completeNoConstraints_mem_P`, `missingNonemptyNoConstraints_mem_P`: the decision problems.

(b) At most `k` attributes, any clause constraints, domain sizes in binary:

* `exists_missing_candidate_iff`: a missing state exists iff one exists whose values are among
  `0, …, N` and the values written in the instance (`N` = their number), inside the domains.
* `length_candidateStates_le`: there are at most `(2N + 1)ᵏ` such states.
* `completeFixedAttrs_mem_P`, `missingNonemptyFixedAttrs_mem_P`: for every fixed `k`, the decision
  problems are in `P`. The degree grows with `k`: the search visits at most `(2N + 1)ᵏ` states.

With binary domain sizes, |𝒟| = ∏ dᵢ is not polynomial even for `k = 1`; the candidate values
replace the enumeration of 𝒟.
-/

namespace Latc.PaperD.General

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### (a) No constraints -/

/-- The rows of T₀ inside the declared domains. -/
def domRows (I : Inst) : List (List ℕ) := I.2.2.filter (inDomainsB I.1)

/-- The entries of a list that do not occur earlier, with their positions. -/
def firstOcc (L : List (List ℕ)) : List (List ℕ × ℕ) :=
  L.zipIdx.filter fun p => !decide (p.1 ∈ L.take p.2)

/-- The number of distinct rows of T₀ inside the declared domains. -/
def distinctRows (I : Inst) : ℕ := (firstOcc (domRows I)).length

/-- |𝒟| = ∏ dᵢ. -/
def domProd (I : Inst) : ℕ := I.1.foldl (· * ·) 1

lemma length_firstOcc (L : List (List ℕ)) : (firstOcc L).length = L.toFinset.card := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L a ih =>
    have hpre : (L.zipIdx.filter fun p => !decide (p.1 ∈ (L ++ [a]).take p.2)) = firstOcc L := by
      unfold firstOcc
      refine List.filter_congr fun p hp => ?_
      have := (List.mem_zipIdx hp).2.1
      rw [List.take_append_of_le_length (by omega)]
    rw [firstOcc, List.zipIdx_append, List.filter_append, List.length_append, hpre, ih,
      List.toFinset_append]
    simp only [List.zipIdx_singleton, zero_add, List.take_left', List.filter_cons,
      List.filter_nil]
    by_cases ha : a ∈ L
    · simp [ha, Finset.insert_eq_of_mem]
    · simp [ha, Finset.card_insert_of_notMem]


lemma map_table (I : Inst) :
    I.table.map ⟨I.toList, I.toList_injective⟩ = (domRows I).toFinset := by
  ext s
  simp only [Finset.mem_map, Inst.table, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, List.mem_toFinset, domRows, List.mem_filter, inDomainsB_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, I.inDomains_toList x⟩
  · rintro ⟨hs, hd⟩
    obtain ⟨x, rfl⟩ := I.exists_toList_eq hd
    exact ⟨x, hs, rfl⟩

lemma card_table (I : Inst) : I.table.card = distinctRows I := by
  rw [distinctRows, length_firstOcc, ← map_table, Finset.card_map]

lemma card_univ (I : Inst) : (Finset.univ : Finset (∀ i, I.Dom i)).card = domProd I := by
  rw [Finset.card_univ, Fintype.card_pi]
  simp only [Fintype.card_fin, domProd, ← List.prod_eq_foldl]
  exact Fin.prod_univ_getElem I.1

/-- **|M(T₀)| without constraints:** ∏ dᵢ minus the number of distinct rows of T₀ inside the
declared domains. -/
theorem missingCount_eq_of_noConstraints (I : Inst) (h : I.2.1 = []) :
    missingCount I = domProd I - distinctRows I := by
  have hv : validSpace I.con = Finset.univ := by
    ext x
    simp [validSpace, Inst.con, Valid, h]
  rw [missingCount, missing, hv, Finset.card_sdiff_of_subset (Finset.subset_univ _), card_univ,
    card_table]


/-! ### Polynomial time -/

lemma length_encNat_le_of_mem {l : List ℕ} {v : ℕ} (h : v ∈ l) :
    (encNat v).length ≤ (encList encNat l).length := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [encList_cons, List.length_append, length_frame]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h
      omega

theorem domProd_polyTime : ComputableInPolyTime domProd encInstBin encNat := by
  refine .of_tidy ?_
  unfold domProd
  refine ComputableTidilyInPolyTime.foldlWithInput_of_bounded_growth (encA := encNat)
    (encL := encList encNat) (step := fun _ a b => a * b) (growth := fun I => (encInstBin I).length)
    (by fun_prop) ⟨by fun_prop, by fun_prop, inferInstance, inferInstance⟩
    ⟨PolyBounded.of_forall_le 1 1 fun I => by simp, fun I a b hb => ?_⟩
  exact (length_encNat_mul_le a b).trans (by
    have := (length_encNat_le_of_mem hb).trans (length_domains_le_bin I)
    omega)

theorem distinctRows_polyTime : ComputableInPolyTime distinctRows encInstBin encNat := by
  have hd : ComputableTidilyInPolyTime domRows encInstBin (encList (encList encNat)) := by
    unfold domRows inDomainsB
    fun_prop
  have ht : ComputableTidilyInPolyTime
      (fun p : List (List ℕ) × (List ℕ × ℕ) => !decide (p.2.1 ∈ p.1.take p.2.2))
      (encPair (encList (encList encNat)) (encPair (encList encNat) encUnary)) encBool := by
    fun_prop
  have hf : ComputableTidilyInPolyTime firstOcc (encList (encList encNat))
      (encList (encPair (encList encNat) encUnary)) := by
    unfold firstOcc
    exact ComputableTidilyInPolyTime.filterWithInput (by fun_prop) ht
  have hl : ComputableTidilyInPolyTime (fun I => (firstOcc (domRows I)).length) encInstBin
      encUnary :=
    (ComputableTidilyInPolyTime.length (encPair (encList encNat) encUnary)).comp (hf.comp hd)
  exact .of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp hl)

/-- |M(T₀)| when there are no constraints: ∏ dᵢ minus the distinct in-domain rows. -/
def countNoCon (I : Inst) : ℕ := domProd I - distinctRows I

theorem countNoCon_polyTime : ComputableInPolyTime countNoCon encInstBin encNat := by
  have h1 := domProd_polyTime.tidy
  have h2 := distinctRows_polyTime.tidy
  refine .of_tidy ?_
  unfold countNoCon
  fun_prop

/-- **(a), counting: without constraints, |M(T₀)| is polynomial-time computable** (zero on
instances with constraints). -/
theorem missingCountNoConstraints_polyTime :
    ComputableInPolyTime (fun I : Inst => if I.2.1 = [] then missingCount I else 0)
      encInstBin encNat := by
  have h := countNoCon_polyTime.tidy
  have heq : (fun I : Inst => if I.2.1 = [] then missingCount I else 0) =
      fun I => if I.2.1.isEmpty then countNoCon I else 0 := by
    funext I
    by_cases hI : I.2.1 = []
    · simp [hI, countNoCon, missingCount_eq_of_noConstraints I hI]
    · simp [hI]
  rw [heq]
  refine .of_tidy ?_
  fun_prop

lemma missing_eq_empty_iff_of_noConstraints (I : Inst) (h : I.2.1 = []) :
    missing I.con I.table = ∅ ↔ domProd I ≤ distinctRows I := by
  rw [← Finset.card_eq_zero, ← missingCount, missingCount_eq_of_noConstraints I h,
    Nat.sub_eq_zero_iff_le]

/-- The decider for (a): no constraints and ∏ dᵢ at most the distinct in-domain rows. -/
def completeNoConB (I : Inst) : Bool := I.2.1.isEmpty && decide (domProd I ≤ distinctRows I)

theorem completeNoConB_polyTime : ComputableInPolyTime completeNoConB encInstBin encBool := by
  have h1 := domProd_polyTime.tidy
  have h2 := distinctRows_polyTime.tidy
  refine .of_tidy ?_
  unfold completeNoConB
  fun_prop

/-- **(a): without constraints, completeness is decidable in polynomial time,** on latc-check's
`Latc.missing`. -/
theorem completeNoConstraints_mem_P :
    {I : Inst | I.2.1 = [] ∧ missing I.con I.table = ∅} ∈ P encInstBin := by
  refine ⟨completeNoConB, completeNoConB_polyTime, fun I => ?_⟩
  simp only [Set.mem_ofPred_eq, completeNoConB, Bool.and_eq_true, List.isEmpty_iff,
    decide_eq_true_eq]
  constructor
  · rintro ⟨h, hm⟩
    exact ⟨h, (missing_eq_empty_iff_of_noConstraints I h).1 hm⟩
  · rintro ⟨h, hm⟩
    exact ⟨h, (missing_eq_empty_iff_of_noConstraints I h).2 hm⟩

/-- **(a): without constraints, M(T₀) ≠ ∅ is decidable in polynomial time.** -/
theorem missingNonemptyNoConstraints_mem_P :
    {I : Inst | I.2.1 = [] ∧ (missing I.con I.table).Nonempty} ∈ P encInstBin := by
  refine ⟨fun I => I.2.1.isEmpty && !decide (domProd I ≤ distinctRows I), ?_, fun I => ?_⟩
  · have h1 := domProd_polyTime.tidy
    have h2 := distinctRows_polyTime.tidy
    refine .of_tidy ?_
    fun_prop
  · simp only [Set.mem_ofPred_eq, Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true',
      decide_eq_false_iff_not]
    constructor
    · rintro ⟨h, hm⟩
      exact ⟨h, fun hle => (Finset.nonempty_iff_ne_empty.1 hm)
        ((missing_eq_empty_iff_of_noConstraints I h).2 hle)⟩
    · rintro ⟨h, hm⟩
      exact ⟨h, Finset.nonempty_iff_ne_empty.2 fun he =>
        hm ((missing_eq_empty_iff_of_noConstraints I h).1 he)⟩

/-! ### (b) A fixed number of attributes -/

/-- The values written in the instance: in the conditions and in the rows of T₀. -/
def writtenVals (I : Inst) : List ℕ := I.2.1.flatten.map Prod.snd ++ I.2.2.flatten

/-- The number of values written in the instance. -/
def Inst.numVals (I : Inst) : ℕ := (writtenVals I).length

/-- The candidate values of an attribute with domain size `di`: `0, …, N` and the written values,
inside the domain. -/
def candVals (I : Inst) (di : ℕ) : List ℕ :=
  (List.range (I.numVals + 1) ++ writtenVals I).filter fun v => decide (v < di)

/-- The candidate values of every attribute. -/
def candLists (I : Inst) : List (List ℕ) := I.1.map (candVals I)

/-- The choices of one element from each list, for at most `k` lists (none for more). -/
def boundedSections : ℕ → List (List ℕ) → List (List ℕ)
  | 0, L => if L.isEmpty then [[]] else []
  | k + 1, L => if L.isEmpty then [[]] else
      (L.headD []).flatMap fun a => (boundedSections k L.tail).map (a :: ·)

/-- The candidate states for at most `k` attributes. -/
def candidateStates (k : ℕ) (I : Inst) : List (List ℕ) := boundedSections k (candLists I)

lemma mem_boundedSections {k : ℕ} {L : List (List ℕ)} (hL : L.length ≤ k) (s : List ℕ) :
    s ∈ boundedSections k L ↔ List.Forall₂ (· ∈ ·) s L := by
  induction k generalizing L s with
  | zero =>
    rcases L with _ | ⟨l, L⟩
    · simp [boundedSections]
    · simp at hL
  | succ k ih =>
    rcases L with _ | ⟨l, L⟩
    · simp [boundedSections]
    · simp only [boundedSections, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        List.headD_cons, List.tail_cons, List.mem_flatMap, List.mem_map,
        List.forall₂_cons_right_iff]
      have hL' : L.length ≤ k := by simp at hL; omega
      constructor
      · rintro ⟨a, ha, t, ht, rfl⟩
        exact ⟨a, t, ha, (ih hL' t).1 ht, rfl⟩
      · rintro ⟨a, t, ha, ht, rfl⟩
        exact ⟨a, ha, t, (ih hL' t).2 ht, rfl⟩

lemma length_boundedSections_le {M : ℕ} (hM : 1 ≤ M) (k : ℕ) {L : List (List ℕ)}
    (hL : ∀ l ∈ L, l.length ≤ M) : (boundedSections k L).length ≤ M ^ k := by
  induction k generalizing L with
  | zero =>
    rcases L with _ | ⟨l, L⟩ <;> simp [boundedSections]
  | succ k ih =>
    rcases L with _ | ⟨l, L⟩
    · simpa [boundedSections] using Nat.one_le_pow _ _ hM
    · simp only [boundedSections, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        List.headD_cons, List.tail_cons, List.length_flatMap, List.length_map]
      have h1 := ih fun l' hl' => hL l' (List.mem_cons_of_mem _ hl')
      have h2 := hL l List.mem_cons_self
      rw [List.map_const', List.sum_replicate, smul_eq_mul, pow_succ]
      calc l.length * (boundedSections k L).length ≤ M * M ^ k := Nat.mul_le_mul h2 h1
        _ = M ^ k * M := Nat.mul_comm _ _

lemma length_candVals_le (I : Inst) (di : ℕ) : (candVals I di).length ≤ 2 * I.numVals + 1 := by
  refine (List.length_filter_le _ _).trans ?_
  simp [Inst.numVals]
  omega

/-- **The search space of (b):** with at most `k` attributes there are at most `(2N + 1)ᵏ`
candidate states, `N` the number of values written in the instance. -/
theorem length_candidateStates_le (k : ℕ) (I : Inst) :
    (candidateStates k I).length ≤ (2 * I.numVals + 1) ^ k :=
  length_boundedSections_le (by omega) k fun l hl => by
    obtain ⟨di, -, rfl⟩ := List.mem_map.1 hl
    exact length_candVals_le I di

/-! ### Polynomial time for each fixed `k` -/

lemma boundedSections_zero :
    boundedSections 0 = fun L => if L.isEmpty then [[]] else [] := by
  funext L
  rfl

lemma boundedSections_succ (k : ℕ) : boundedSections (k + 1) = fun L =>
    if L.isEmpty then [[]] else
      (L.headD []).flatMap fun a => (boundedSections k L.tail).map (a :: ·) := by
  funext L
  rfl

theorem boundedSections_polyTime (k : ℕ) : ComputableTidilyInPolyTime (boundedSections k)
    (encList (encList encNat)) (encList (encList encNat)) := by
  induction k with
  | zero =>
    rw [boundedSections_zero]
    fun_prop
  | succ k ih =>
    have hb : ComputableTidilyInPolyTime
        (fun p : List (List ℕ) × ℕ => (boundedSections k p.1.tail).map (p.2 :: ·))
        (encPair (encList (encList encNat)) encNat) (encList (encList encNat)) := by
      fun_prop
    have hf : ComputableTidilyInPolyTime
        (fun L : List (List ℕ) =>
          (L.headD []).flatMap fun a => (boundedSections k L.tail).map (a :: ·))
        (encList (encList encNat)) (encList (encList encNat)) :=
      ComputableTidilyInPolyTime.flatMapWithInput (by fun_prop) hb
    rw [boundedSections_succ]
    fun_prop

/-- The candidate values before restriction to a domain. -/
def candPool (I : Inst) : List ℕ := (List.range (I.numVals + 1)).map id ++ writtenVals I

theorem candPool_polyTime : ComputableTidilyInPolyTime candPool encInstBin (encList encNat) := by
  have hu := ComputableTidilyInPolyTime.unary_to_binary
  have hS : ComputableTidilyInPolyTime (fun I : Inst => I.2.1) encInstBin
      (encList (encList (encPair encNat encNat))) := by fun_prop
  have hT : ComputableTidilyInPolyTime (fun I : Inst => I.2.2) encInstBin
      (encList (encList encNat)) := by fun_prop
  have hw : ComputableTidilyInPolyTime writtenVals encInstBin (encList encNat) :=
    ComputableTidilyInPolyTime.listAppend'
      ((ComputableTidilyInPolyTime.map (ComputableTidilyInPolyTime.snd encNat encNat)).comp
        ((ComputableTidilyInPolyTime.flatten _).comp hS))
      ((ComputableTidilyInPolyTime.flatten _).comp hT)
  have hn : ComputableTidilyInPolyTime (fun I : Inst => I.numVals + 1) encInstBin encUnary := by
    unfold Inst.numVals
    have hl := (ComputableTidilyInPolyTime.length encNat).comp hw
    simp only [Function.comp_def] at hl
    fun_prop
  have hr : ComputableTidilyInPolyTime (fun I : Inst => (List.range (I.numVals + 1)).map id)
      encInstBin (encList encNat) :=
    (ComputableTidilyInPolyTime.map hu).comp (ComputableTidilyInPolyTime.range.comp hn)
  exact ComputableTidilyInPolyTime.listAppend' hr hw

lemma candLists_eq (I : Inst) :
    candLists I = I.1.map fun di => (candPool I).filter fun v => decide (v < di) := by
  simp [candLists, candVals, candPool]

theorem candidateStates_polyTime (k : ℕ) :
    ComputableTidilyInPolyTime (candidateStates k) encInstBin (encList (encList encNat)) := by
  have hp := candPool_polyTime
  have hf : ComputableTidilyInPolyTime
      (fun p : Inst × ℕ => (candPool p.1).filter fun v => decide (v < p.2))
      (encPair encInstBin encNat) (encList encNat) :=
    ComputableTidilyInPolyTime.filterWithInput (hp.comp (by fun_prop)) (by fun_prop)
  have hc : ComputableTidilyInPolyTime candLists encInstBin (encList (encList encNat)) := by
    have h := ComputableTidilyInPolyTime.mapWithInput (encIn := encInstBin)
      (list := fun I : Inst => I.1) (f := fun I di => (candPool I).filter fun v => decide (v < di))
      (ComputableTidilyInPolyTime.fst (encList encNat)
        (encPair (encList (encList (encPair encNat encNat))) (encList (encList encNat)))) hf
    simpa only [← candLists_eq] using h
  exact (boundedSections_polyTime k).comp hc

/-! ### Correctness: a missing state can be taken among the candidates -/

lemma exists_unwritten (I : Inst) : ∃ g, g ≤ I.numVals ∧ g ∉ writtenVals I := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hsub : Finset.range (I.numVals + 1) ⊆ (writtenVals I).toFinset := fun g hg =>
    List.mem_toFinset.2 (h g (Nat.lt_add_one_iff.1 (Finset.mem_range.1 hg)))
  have := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  simp [Inst.numVals] at this

lemma mem_candidateStates_iff {k : ℕ} {I : Inst} (hk : I.n ≤ k) (s : List ℕ) :
    s ∈ candidateStates k I ↔
      List.Forall₂ (fun v di => v < di ∧ (v ≤ I.numVals ∨ v ∈ writtenVals I)) s I.1 := by
  rw [candidateStates, mem_boundedSections (by simpa [candLists] using hk), candLists,
    List.forall₂_map_right_iff]
  have key : ∀ v di, v ∈ candVals I di ↔ (v < di ∧ (v ≤ I.numVals ∨ v ∈ writtenVals I)) := by
    intro v di
    simp only [candVals, List.mem_filter, List.mem_append, List.mem_range, decide_eq_true_eq,
      Nat.lt_add_one_iff]
    tauto
  exact ⟨fun h => h.imp fun v di h => (key v di).1 h, fun h => h.imp fun v di h => (key v di).2 h⟩

/-- **A missing state exists iff one exists among the candidates.** A value written nowhere in the
instance can be replaced by another one `≤ N` written nowhere: no condition holds on either, and a
state with such a value is not a row of T₀. -/
theorem exists_missing_candidate_iff {k : ℕ} {I : Inst} (hk : I.n ≤ k) :
    I ∈ MissingNonempty ↔ ∃ s ∈ candidateStates k I, check (I, s) = true := by
  constructor
  · rintro ⟨s, hd, hv, hT⟩
    obtain ⟨g, hgN, hgW⟩ := exists_unwritten I
    let W := writtenVals I
    let φ : ℕ → ℕ := fun v => if v ≤ I.numVals ∨ v ∈ W then v else g
    have hφW : ∀ u ∈ W, ∀ v, φ v = u ↔ v = u := by
      intro u hu v
      by_cases hv : v ≤ I.numVals ∨ v ∈ W
      · simp [φ, hv]
      · simp only [φ, hv, ↓reduceIte]
        constructor
        · rintro rfl; exact absurd hu hgW
        · rintro rfl; exact absurd (Or.inr hu) hv
    have hcand : List.Forall₂ (fun v di => v < di ∧ (v ≤ I.numVals ∨ v ∈ W))
        (s.map φ) I.1 := by
      rw [List.forall₂_map_left_iff]
      refine hd.imp fun v di hvd => ?_
      by_cases hv : v ≤ I.numVals ∨ v ∈ W
      · have : φ v = v := by simp [φ, hv]
        rw [this]
        exact ⟨hvd, hv⟩
      · simp only [φ, hv, ↓reduceIte]
        simp only [not_or, not_le] at hv
        exact ⟨by omega, Or.inl hgN⟩
    refine ⟨s.map φ, (mem_candidateStates_iff hk _).2 hcand, (check_iff I _).2 ⟨?_, ?_, ?_⟩⟩
    · exact hcand.imp fun _ _ h => h.1
    · intro c hc
      obtain ⟨a, ha, hholds⟩ := hv c hc
      have haW : a.2 ∈ W :=
        List.mem_append_left _ (List.mem_map.2 ⟨a, List.mem_flatten.2 ⟨c, hc, ha⟩, rfl⟩)
      refine ⟨a, ha, ?_⟩
      simp only [CondHolds] at hholds ⊢
      rw [List.getElem?_map, hholds, Option.map_some, (hφW _ haW _).2 rfl]
    · intro hmem
      apply hT
      have hfix : ∀ v ∈ s, φ v = v := by
        intro v hv
        have hW : φ v ∈ W := List.mem_append_right _
          (List.mem_flatten.2 ⟨_, hmem, List.mem_map_of_mem hv⟩)
        exact ((hφW _ hW v).1 rfl).symm
      have : s.map φ = s := by
        conv_rhs => rw [← List.map_id s]
        exact List.map_congr_left hfix
      exact this ▸ hmem
  · rintro ⟨s, -, hs⟩
    exact ⟨s, (check_iff I s).1 hs⟩

/-! ### A fixed number of attributes -/

/-- Some candidate state is missing. -/
def someCandidateMissing (k : ℕ) (I : Inst) : Bool :=
  (candidateStates k I).any fun s => check (I, s)

theorem someCandidateMissing_polyTime (k : ℕ) :
    ComputableTidilyInPolyTime (someCandidateMissing k) encInstBin encBool := by
  have hc := candidateStates_polyTime k
  have hk := checkBin_polyTime.tidy
  unfold someCandidateMissing
  fun_prop

lemma someCandidateMissing_iff {k : ℕ} {I : Inst} (hk : I.n ≤ k) :
    someCandidateMissing k I = true ↔ (missing I.con I.table).Nonempty := by
  rw [← mem_MissingNonempty_iff, exists_missing_candidate_iff hk, someCandidateMissing,
    List.any_eq_true]

/-- **(b): with at most `k` attributes, M(T₀) ≠ ∅ is decidable in polynomial time,** for every
fixed `k`, constraints arbitrary and domain sizes in binary. -/
theorem missingNonemptyFixedAttrs_mem_P (k : ℕ) :
    {I : Inst | I.n ≤ k ∧ (missing I.con I.table).Nonempty} ∈ P encInstBin := by
  refine ⟨fun I => decide (I.1.length ≤ k) && someCandidateMissing k I, ?_, fun I => ?_⟩
  · have h := someCandidateMissing_polyTime k
    refine .of_tidy ?_
    fun_prop
  · simp only [Set.mem_ofPred_eq, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨hk, h⟩ => ⟨hk, (someCandidateMissing_iff hk).2 h⟩,
      fun ⟨hk, h⟩ => ⟨hk, (someCandidateMissing_iff hk).1 h⟩⟩

/-- **(b): with at most `k` attributes, completeness is decidable in polynomial time,** for every
fixed `k`, constraints arbitrary and domain sizes in binary. -/
theorem completeFixedAttrs_mem_P (k : ℕ) :
    {I : Inst | I.n ≤ k ∧ missing I.con I.table = ∅} ∈ P encInstBin := by
  refine ⟨fun I => decide (I.1.length ≤ k) && !someCandidateMissing k I, ?_, fun I => ?_⟩
  · have h := someCandidateMissing_polyTime k
    refine .of_tidy ?_
    fun_prop
  · simp only [Set.mem_ofPred_eq, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    constructor
    · rintro ⟨hk, h⟩
      refine ⟨hk, Bool.eq_false_iff.2 fun h' => ?_⟩
      rw [someCandidateMissing_iff hk, h] at h'
      exact Finset.not_nonempty_empty h'
    · rintro ⟨hk, h⟩
      refine ⟨hk, Finset.not_nonempty_iff_eq_empty.1 fun h' => ?_⟩
      rw [← someCandidateMissing_iff hk, h] at h'
      exact Bool.false_ne_true h'

/-! ### The unary attribute index -/

/-- A problem in `P` for the binary attribute index is in `P` for the unary one. -/
theorem mem_P_of_mem_P_bin {A : Set Inst} (h : A ∈ P encInstBin) : A ∈ P encInst := by
  obtain ⟨f, hf, hA⟩ := h
  exact ⟨f, hf.comp encInst_to_encInstBin_polyTime, hA⟩

theorem completeNoConstraints_mem_P_unary :
    {I : Inst | I.2.1 = [] ∧ missing I.con I.table = ∅} ∈ P encInst :=
  mem_P_of_mem_P_bin completeNoConstraints_mem_P

theorem missingNonemptyNoConstraints_mem_P_unary :
    {I : Inst | I.2.1 = [] ∧ (missing I.con I.table).Nonempty} ∈ P encInst :=
  mem_P_of_mem_P_bin missingNonemptyNoConstraints_mem_P

theorem missingCountNoConstraints_polyTime_unary :
    ComputableInPolyTime (fun I : Inst => if I.2.1 = [] then missingCount I else 0)
      encInst encNat :=
  missingCountNoConstraints_polyTime.comp encInst_to_encInstBin_polyTime

theorem completeFixedAttrs_mem_P_unary (k : ℕ) :
    {I : Inst | I.n ≤ k ∧ missing I.con I.table = ∅} ∈ P encInst :=
  mem_P_of_mem_P_bin (completeFixedAttrs_mem_P k)

theorem missingNonemptyFixedAttrs_mem_P_unary (k : ℕ) :
    {I : Inst | I.n ≤ k ∧ (missing I.con I.table).Nonempty} ∈ P encInst :=
  mem_P_of_mem_P_bin (missingNonemptyFixedAttrs_mem_P k)

end Latc.PaperD.General
