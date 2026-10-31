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

(b), counting, at most `k` attributes:

* `missingCount_eq_weighted_of_le`: |M(T₀)| is a weighted sum over class vectors. The values of an
  attribute with domain size `dᵢ` fall into classes: each written value is its own class, and the
  unwritten values form one more class (represented by `unwritten I`, of size `dᵢ` minus the
  written values below `dᵢ`). Validity depends only on the class vector, and a state with an
  unwritten value is not a row of T₀, so each valid class vector that is not a row of T₀
  contributes ∏ᵢ |cᵢ| (`classStateWeight`).
* `length_classStates_le`: there are at most `(N + 1)ᵏ` class vectors.
* `missingCountFixedAttrs_polyTime`: for every fixed `k`, |M(T₀)| is polynomial-time computable.
  Each weight is at most ∏ dᵢ, so the binary sum has bounded growth.
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

/-! ### (b), counting: weighted class vectors -/

/-- The entries of a list that do not occur earlier: the list without repetitions. -/
def distinctVals (L : List ℕ) : List ℕ :=
  (L.zipIdx.filter fun p => !decide (p.1 ∈ L.take p.2)).map Prod.fst

lemma distinctVals_append_singleton (L : List ℕ) (a : ℕ) :
    distinctVals (L ++ [a]) = distinctVals L ++ if a ∈ L then [] else [a] := by
  have hpre : (L.zipIdx.filter fun p => !decide (p.1 ∈ (L ++ [a]).take p.2)) =
      L.zipIdx.filter fun p => !decide (p.1 ∈ L.take p.2) := by
    refine List.filter_congr fun p hp => ?_
    have := (List.mem_zipIdx hp).2.1
    rw [List.take_append_of_le_length (by omega)]
  rw [distinctVals, List.zipIdx_append, List.filter_append, hpre, List.map_append, ← distinctVals]
  simp only [List.zipIdx_singleton, zero_add, List.take_left', List.filter_cons,
    List.filter_nil]
  by_cases ha : a ∈ L <;> simp [ha]

lemma mem_distinctVals {L : List ℕ} {v : ℕ} : v ∈ distinctVals L ↔ v ∈ L := by
  induction L using List.reverseRecOn with
  | nil => simp [distinctVals]
  | append_singleton L a ih =>
    rw [distinctVals_append_singleton]
    by_cases ha : a ∈ L
    · simp only [ha, ↓reduceIte, List.append_nil, ih, List.mem_append, List.mem_singleton]
      constructor
      · exact Or.inl
      · rintro (h | rfl)
        · exact h
        · exact ha
    · simp [ha, ih]

lemma nodup_distinctVals (L : List ℕ) : (distinctVals L).Nodup := by
  induction L using List.reverseRecOn with
  | nil => simp [distinctVals]
  | append_singleton L a ih =>
    rw [distinctVals_append_singleton]
    by_cases ha : a ∈ L
    · simpa [ha] using ih
    · simp only [ha, ↓reduceIte]
      rw [List.nodup_append]
      refine ⟨ih, List.nodup_singleton a, fun x hx y hy => ?_⟩
      rw [List.mem_singleton] at hy
      rintro rfl
      exact ha (hy ▸ mem_distinctVals.1 hx)

/-- A value `≤ N` written nowhere in the instance: the representative of the unwritten values. -/
def unwritten (I : Inst) : ℕ :=
  ((List.range (I.numVals + 1)).filter fun v => !decide (v ∈ writtenVals I)).headD 0

lemma unwritten_not_mem (I : Inst) : unwritten I ∉ writtenVals I := by
  obtain ⟨g, hg, hgW⟩ := exists_unwritten I
  have key : ∀ l : List ℕ, g ∈ l → (∀ x ∈ l, x ∉ writtenVals I) → l.headD 0 ∉ writtenVals I := by
    rintro (_ | ⟨h, t⟩) hm hl
    · simp at hm
    · exact hl h List.mem_cons_self
  refine key _ ?_ fun x hx => ?_
  · simp only [List.mem_filter, List.mem_range, hgW, decide_false, Bool.not_false, and_true]
    omega
  · simpa using (List.mem_filter.1 hx).2

/-- The class of a value: itself if it is written in the instance, the representative
`unwritten I` otherwise. -/
def cls (I : Inst) (v : ℕ) : ℕ := if v ∈ writtenVals I then v else unwritten I

lemma cls_of_mem {I : Inst} {v : ℕ} (h : v ∈ writtenVals I) : cls I v = v := by
  simp [cls, h]

lemma cls_of_not_mem {I : Inst} {v : ℕ} (h : v ∉ writtenVals I) : cls I v = unwritten I := by
  simp [cls, h]

lemma cls_cls (I : Inst) (v : ℕ) : cls I (cls I v) = cls I v := by
  by_cases h : v ∈ writtenVals I
  · rw [cls_of_mem h, cls_of_mem h]
  · rw [cls_of_not_mem h, cls_of_not_mem (unwritten_not_mem I)]

lemma cls_eq_iff_of_mem {I : Inst} {c : ℕ} (hc : c ∈ writtenVals I) (v : ℕ) :
    cls I v = c ↔ v = c := by
  by_cases h : v ∈ writtenVals I
  · rw [cls_of_mem h]
  · rw [cls_of_not_mem h]
    constructor
    · rintro rfl; exact absurd hc (unwritten_not_mem I)
    · rintro rfl; exact absurd hc h

lemma mem_of_cls_mem {I : Inst} {v : ℕ} (h : cls I v ∈ writtenVals I) : v ∈ writtenVals I := by
  by_contra hv
  rw [cls_of_not_mem hv] at h
  exact unwritten_not_mem I h

/-- The classes of values: each written value, and the unwritten values (represented by
`unwritten I`). -/
def classVals (I : Inst) : List ℕ := distinctVals (writtenVals I) ++ [unwritten I]

lemma nodup_classVals (I : Inst) : (classVals I).Nodup := by
  rw [classVals, List.nodup_append]
  refine ⟨nodup_distinctVals _, List.nodup_singleton _, fun x hx y hy => ?_⟩
  rw [List.mem_singleton] at hy
  rintro rfl
  exact unwritten_not_mem I (hy ▸ mem_distinctVals.1 hx)

lemma cls_mem_classVals (I : Inst) (v : ℕ) : cls I v ∈ classVals I := by
  by_cases h : v ∈ writtenVals I
  · rw [cls_of_mem h]
    exact List.mem_append_left _ (mem_distinctVals.2 h)
  · rw [cls_of_not_mem h]
    exact List.mem_append_right _ List.mem_cons_self

/-- The number of values of `{0, …, d - 1}` in the class of `v`: one or none for a written value,
`d` minus the written values below `d` for the unwritten class. -/
def classWeight (I : Inst) (d v : ℕ) : ℕ :=
  if decide (v ∈ writtenVals I) then (if decide (v < d) then 1 else 0)
  else d - ((distinctVals (writtenVals I)).filter fun u => decide (u < d)).length

lemma classWeight_le (I : Inst) (d v : ℕ) : classWeight I d v ≤ d := by
  unfold classWeight
  split_ifs with h1 h2
  · simp only [decide_eq_true_eq] at h2
    omega
  · exact Nat.zero_le _
  · exact Nat.sub_le _ _

lemma card_fiber (I : Inst) (d : ℕ) {c : ℕ} (hc : c ∈ classVals I) :
    ((Finset.range d).filter fun v => cls I v = c).card = classWeight I d c := by
  by_cases hW : c ∈ writtenVals I
  · have : ((Finset.range d).filter fun v => cls I v = c) = (Finset.range d).filter (· = c) :=
      Finset.filter_congr fun v _ => cls_eq_iff_of_mem hW v
    rw [this, Finset.filter_eq', classWeight]
    by_cases hd : c < d <;> simp [hd, hW]
  · have hg : c = unwritten I := by
      rcases List.mem_append.1 hc with h | h
      · exact absurd (mem_distinctVals.1 h) hW
      · simpa using h
    have : ((Finset.range d).filter fun v => cls I v = c) =
        (Finset.range d).filter fun v => v ∉ writtenVals I := by
      refine Finset.filter_congr fun v _ => ?_
      rw [hg]
      constructor
      · intro h hv
        rw [cls_of_mem hv] at h
        exact unwritten_not_mem I (h ▸ hv)
      · exact cls_of_not_mem
    have hW' : ((Finset.range d).filter fun v => v ∈ writtenVals I) =
        ((distinctVals (writtenVals I)).filter fun u => decide (u < d)).toFinset := by
      ext x
      simp [mem_distinctVals, and_comm]
    have hsum := Finset.card_filter_add_card_filter_not (s := Finset.range d)
      (fun v => v ∈ writtenVals I)
    rw [this, classWeight]
    simp only [hW, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [← List.toFinset_card_of_nodup
      ((nodup_distinctVals _).filter _), ← hW']
    simp only [Finset.card_range] at hsum
    omega

/-- **One attribute.** A function of the values that depends only on their classes sums over
`{0, …, d - 1}` as the sum over the classes weighted by their sizes. -/
lemma sum_range_eq_classes (I : Inst) (d : ℕ) (G : ℕ → ℕ) (hG : ∀ v, G v = G (cls I v)) :
    ((List.range d).map G).sum = ((classVals I).map fun c => classWeight I d c * G c).sum := by
  rw [← List.sum_toFinset _ List.nodup_range, ← List.sum_toFinset _ (nodup_classVals I),
    List.toFinset_range, Finset.sum_congr rfl fun v _ => hG v,
    ← Finset.sum_fiberwise_of_maps_to (g := cls I) (t := (classVals I).toFinset)
      fun v _ => List.mem_toFinset.2 (cls_mem_classVals I v)]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Finset.sum_congr rfl fun v hv => by rw [(Finset.mem_filter.1 hv).2], Finset.sum_const,
    smul_eq_mul, card_fiber I d (List.mem_toFinset.1 hc)]

/-! ### The states of the declared domains -/

/-- The states of the declared domains `d`, listed. -/
def domStates : List ℕ → List (List ℕ)
  | [] => [[]]
  | a :: d => (List.range a).flatMap fun v => (domStates d).map (v :: ·)

lemma mem_domStates (d s : List ℕ) : s ∈ domStates d ↔ InDomains d s := by
  induction d generalizing s with
  | nil => simp [domStates, InDomains]
  | cons a d ih =>
    simp only [domStates, List.mem_flatMap, List.mem_range, List.mem_map, InDomains,
      List.forall₂_cons_right_iff]
    constructor
    · rintro ⟨v, hv, t, ht, rfl⟩
      exact ⟨v, t, hv, (ih t).1 ht, rfl⟩
    · rintro ⟨v, t, hv, ht, rfl⟩
      exact ⟨v, hv, t, (ih t).2 ht, rfl⟩

lemma nodup_domStates (d : List ℕ) : (domStates d).Nodup := by
  induction d with
  | nil => simp [domStates]
  | cons a d ih =>
    rw [domStates, List.nodup_flatMap]
    refine ⟨fun v _ => ih.map (List.cons_injective), List.nodup_range.pairwise_of_forall_ne
      fun v _ w _ hvw => ?_⟩
    simp only [Function.onFun]
    rw [List.disjoint_left]
    rintro s hs ht
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hs
    obtain ⟨t', -, h⟩ := List.mem_map.1 ht
    exact hvw (List.cons.inj h).1.symm

/-- The validity test of a class vector: every clause holds and the vector is not a row of T₀
(domains are not tested; the weights account for them). -/
def validB (p : Inst × List ℕ) : Bool :=
  p.1.2.1.all (fun c => c.any (condHoldsB p.2)) && !decide (p.2 ∈ p.1.2.2)

lemma validB_iff (I : Inst) (s : List ℕ) :
    validB (I, s) = true ↔ Valid I.2.1 s ∧ s ∉ I.2.2 := by
  simp [validB, Valid, condHoldsB_iff]

lemma missingCount_eq_length_filter (I : Inst) :
    missingCount I = ((domStates I.1).filter fun s => validB (I, s)).length := by
  have hset := coe_missing_map_toList I
  have heq : (missing I.con I.table).map ⟨I.toList, I.toList_injective⟩ =
      ((domStates I.1).filter fun s => validB (I, s)).toFinset := by
    ext s
    have := Set.ext_iff.1 hset s
    simp only [Finset.mem_coe, Set.mem_ofPred_eq] at this
    rw [this, List.mem_toFinset, List.mem_filter, mem_domStates, validB_iff]
  rw [missingCount, ← Finset.card_map ⟨I.toList, I.toList_injective⟩, heq,
    List.toFinset_card_of_nodup ((nodup_domStates _).filter _)]

/-- Validity of a state depends only on its class vector. -/
lemma validB_map_cls (I : Inst) (s : List ℕ) : validB (I, s.map (cls I)) = validB (I, s) := by
  rw [Bool.eq_iff_iff, validB_iff, validB_iff]
  have hcond : ∀ c ∈ I.2.1, ∀ a ∈ c, CondHolds (s.map (cls I)) a ↔ CondHolds s a := by
    intro c hc a ha
    have haW : a.2 ∈ writtenVals I :=
      List.mem_append_left _ (List.mem_map.2 ⟨a, List.mem_flatten.2 ⟨c, hc, ha⟩, rfl⟩)
    simp only [CondHolds, List.getElem?_map]
    rcases s[a.1]? with _ | u
    · simp
    · simp [cls_eq_iff_of_mem haW]
  have hfix : ∀ t : List ℕ, (∀ v ∈ t, v ∈ writtenVals I) → t.map (cls I) = t := fun t ht => by
    conv_rhs => rw [← List.map_id t]
    exact List.map_congr_left fun v hv => cls_of_mem (ht v hv)
  have hrow : ∀ t ∈ I.2.2, ∀ v ∈ t, v ∈ writtenVals I := fun t ht v hv =>
    List.mem_append_right _ (List.mem_flatten.2 ⟨t, ht, hv⟩)
  have hT : s.map (cls I) ∈ I.2.2 ↔ s ∈ I.2.2 := by
    constructor
    · intro h
      have : s.map (cls I) = s := hfix s fun v hv =>
        mem_of_cls_mem (hrow _ h _ (List.mem_map_of_mem hv))
      exact this ▸ h
    · intro h
      rwa [hfix s (hrow s h)]
  constructor
  · rintro ⟨hv, ht⟩
    exact ⟨fun c hc => (hv c hc).imp fun a ⟨ha, h⟩ => ⟨ha, (hcond c hc a ha).1 h⟩,
      fun h => ht (hT.2 h)⟩
  · rintro ⟨hv, ht⟩
    exact ⟨fun c hc => (hv c hc).imp fun a ⟨ha, h⟩ => ⟨ha, (hcond c hc a ha).2 h⟩,
      fun h => ht (hT.1 h)⟩

/-- The weight of a class vector: the number of states of the domains it stands for. -/
def classStateWeight (p : Inst × List ℕ) : ℕ :=
  (p.2.zip p.1.1).foldl (fun acc q => acc * classWeight p.1 q.2 q.1) 1

lemma foldl_mul_eq {α : Type*} (f : α → ℕ) (l : List α) (a : ℕ) :
    l.foldl (fun acc q => acc * f q) a = a * (l.map f).prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, mul_assoc]

lemma foldl_add_eq {α : Type*} (f : α → ℕ) (l : List α) (a : ℕ) :
    l.foldl (fun acc q => acc + f q) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, add_assoc]

lemma boundedSections_cons (k : ℕ) (l : List ℕ) (L : List (List ℕ)) :
    boundedSections (k + 1) (l :: L) = l.flatMap fun a => (boundedSections k L).map (a :: ·) := by
  simp [boundedSections]

lemma boundedSections_of_le {k : ℕ} {L : List (List ℕ)} (h : L.length ≤ k) :
    boundedSections k L = boundedSections L.length L := by
  induction L generalizing k with
  | nil => cases k <;> rfl
  | cons l L ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at h; omega⟩
    rw [List.length_cons, boundedSections_cons, boundedSections_cons,
      ih (by simp at h; omega)]

lemma length_of_mem_boundedSections {k : ℕ} {L : List (List ℕ)} {c : List ℕ}
    (h : c ∈ boundedSections k L) : c.length = L.length := by
  induction k generalizing L c with
  | zero =>
    rcases L with _ | ⟨l, L⟩ <;> simp_all [boundedSections]
  | succ k ih =>
    rcases L with _ | ⟨l, L⟩
    · simp_all [boundedSections]
    · rw [boundedSections_cons] at h
      obtain ⟨a, -, h⟩ := List.mem_flatMap.1 h
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
      simp [ih ht]

lemma sum_flatMap {α : Type*} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- **Every attribute.** A Boolean function of the states that depends only on their class vectors
counts over the states of the domains `d` as the sum, over the class vectors, of their weights. -/
lemma length_filter_domStates (I : Inst) (p : List ℕ → Bool)
    (hp : ∀ s, p (s.map (cls I)) = p s) (d : List ℕ) :
    ((domStates d).filter p).length =
      ((boundedSections d.length (d.map fun _ => classVals I)).map fun c =>
        if p c then ((c.zip d).map fun q => classWeight I q.2 q.1).prod else 0).sum := by
  induction d generalizing p with
  | nil =>
    simp only [domStates, List.length_nil, List.map_nil, boundedSections, List.isEmpty_nil,
      ↓reduceIte]
    cases h : p [] <;> simp [h]
  | cons a d ih =>
    -- `p (v :: s)` depends only on the class of `v` and on the classes of `s`
    have hcons : ∀ v s, p (v :: s) = p (cls I v :: s.map (cls I)) := fun v s => by
      rw [← hp (v :: s), List.map_cons]
    have hpv : ∀ v s, p (v :: s.map (cls I)) = p (v :: s) := fun v s => by
      rw [hcons, hcons v s, List.map_map]
      exact congrArg (fun t => p (cls I v :: t)) (List.map_congr_left fun u _ => cls_cls I u)
    have hcls : ∀ v s, p (v :: s) = p (cls I v :: s) := fun v s => by
      rw [hcons v s, hcons (cls I v) s, cls_cls]
    rw [List.length_cons, List.map_cons, boundedSections_cons, domStates, List.filter_flatMap,
      List.length_flatMap]
    simp only [List.filter_map, List.length_map, Function.comp_def]
    rw [List.map_congr_left fun v _ => ih (fun s => p (v :: s)) (hpv v),
      sum_range_eq_classes I a _ fun v => by simp only [hcls v], List.map_flatMap, sum_flatMap]
    refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
    rw [List.map_map, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    simp only [Function.comp_apply, List.zip_cons_cons, List.map_cons, List.prod_cons]
    split_ifs <;> simp

/-- The class vectors for at most `k` attributes. -/
def classStates (k : ℕ) (I : Inst) : List (List ℕ) := boundedSections k (I.1.map fun _ => classVals I)

/-- The weighted count of the valid class vectors. -/
def countClasses (k : ℕ) (I : Inst) : ℕ :=
  (classStates k I).foldl (fun acc c => acc + if validB (I, c) then classStateWeight (I, c) else 0) 0

/-- **|M(T₀)| with at most `k` attributes, as a weighted sum.** Each class vector `c` (a written
value or the unwritten class per attribute) that is valid and not a row of T₀ contributes the
number of states of the domains in it, ∏ᵢ |cᵢ|. -/
theorem missingCount_eq_weighted_of_le {k : ℕ} {I : Inst} (hk : I.n ≤ k) :
    missingCount I = ((classStates k I).map fun c =>
      if validB (I, c) then classStateWeight (I, c) else 0).sum := by
  rw [missingCount_eq_length_filter, length_filter_domStates I _ (validB_map_cls I) I.1,
    classStates, boundedSections_of_le (k := k) (L := I.1.map fun _ => classVals I)
      (by simpa using hk), List.length_map]
  refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
  simp only [classStateWeight, foldl_mul_eq, one_mul]

lemma countClasses_eq (k : ℕ) (I : Inst) : countClasses k I = ((classStates k I).map fun c =>
      if validB (I, c) then classStateWeight (I, c) else 0).sum := by
  rw [countClasses, foldl_add_eq, zero_add]

theorem missingCount_eq_countClasses {k : ℕ} {I : Inst} (hk : I.n ≤ k) :
    missingCount I = countClasses k I := by
  rw [missingCount_eq_weighted_of_le hk, countClasses_eq]

lemma length_classStates_le (k : ℕ) (I : Inst) :
    (classStates k I).length ≤ (I.numVals + 1) ^ k := by
  refine length_boundedSections_le (by omega) k fun l hl => ?_
  obtain ⟨_, -, rfl⟩ := List.mem_map.1 hl
  rw [classVals, List.length_append, List.length_singleton]
  have := (List.toFinset_card_of_nodup (nodup_distinctVals (writtenVals I))).symm
  have h2 : (distinctVals (writtenVals I)).toFinset = (writtenVals I).toFinset := by
    ext; simp [mem_distinctVals]
  rw [h2] at this
  have := List.toFinset_card_le (writtenVals I)
  simp only [Inst.numVals]
  omega

/-! ### Polynomial time of the weighted count -/

theorem writtenVals_polyTime : ComputableTidilyInPolyTime writtenVals encInstBin (encList encNat) := by
  have hS : ComputableTidilyInPolyTime (fun I : Inst => I.2.1) encInstBin
      (encList (encList (encPair encNat encNat))) := by fun_prop
  have hT : ComputableTidilyInPolyTime (fun I : Inst => I.2.2) encInstBin
      (encList (encList encNat)) := by fun_prop
  exact ComputableTidilyInPolyTime.listAppend'
    ((ComputableTidilyInPolyTime.map (ComputableTidilyInPolyTime.snd encNat encNat)).comp
      ((ComputableTidilyInPolyTime.flatten _).comp hS))
    ((ComputableTidilyInPolyTime.flatten _).comp hT)

theorem distinctVals_polyTime :
    ComputableTidilyInPolyTime distinctVals (encList encNat) (encList encNat) := by
  have ht : ComputableTidilyInPolyTime
      (fun p : List ℕ × (ℕ × ℕ) => !decide (p.2.1 ∈ p.1.take p.2.2))
      (encPair (encList encNat) (encPair encNat encUnary)) encBool := by
    fun_prop
  have hf : ComputableTidilyInPolyTime
      (fun L : List ℕ => L.zipIdx.filter fun p => !decide (p.1 ∈ L.take p.2))
      (encList encNat) (encList (encPair encNat encUnary)) :=
    ComputableTidilyInPolyTime.filterWithInput (by fun_prop) ht
  unfold distinctVals
  exact (ComputableTidilyInPolyTime.map (ComputableTidilyInPolyTime.fst encNat encUnary)).comp hf

theorem unwritten_polyTime : ComputableTidilyInPolyTime unwritten encInstBin encNat := by
  have hu := ComputableTidilyInPolyTime.unary_to_binary
  have hw := writtenVals_polyTime
  have hn : ComputableTidilyInPolyTime (fun I : Inst => I.numVals + 1) encInstBin encUnary := by
    unfold Inst.numVals
    have hl := (ComputableTidilyInPolyTime.length encNat).comp hw
    simp only [Function.comp_def] at hl
    fun_prop
  have hr : ComputableTidilyInPolyTime (fun I : Inst => (List.range (I.numVals + 1)).map id)
      encInstBin (encList encNat) :=
    (ComputableTidilyInPolyTime.map hu).comp (ComputableTidilyInPolyTime.range.comp hn)
  have hf : ComputableTidilyInPolyTime
      (fun I : Inst => ((List.range (I.numVals + 1)).map id).filter
        fun v => !decide (v ∈ writtenVals I)) encInstBin (encList encNat) :=
    ComputableTidilyInPolyTime.filterWithInput hr (by fun_prop)
  have h : ComputableTidilyInPolyTime
      (fun I : Inst => (((List.range (I.numVals + 1)).map id).filter
        fun v => !decide (v ∈ writtenVals I)).headD 0) encInstBin encNat := by
    fun_prop
  have e : unwritten = fun I : Inst => (((List.range (I.numVals + 1)).map id).filter
      fun v => !decide (v ∈ writtenVals I)).headD 0 := by
    funext I
    rw [List.map_id]
    rfl
  rw [e]
  exact h

theorem classVals_polyTime : ComputableTidilyInPolyTime classVals encInstBin (encList encNat) := by
  have hd := distinctVals_polyTime.comp writtenVals_polyTime
  have hg := unwritten_polyTime
  unfold classVals
  simp only [Function.comp_def] at hd
  fun_prop

theorem classStates_polyTime (k : ℕ) :
    ComputableTidilyInPolyTime (classStates k) encInstBin (encList (encList encNat)) := by
  have hc := classVals_polyTime
  have hf : ComputableTidilyInPolyTime (fun p : Inst × ℕ => classVals p.1)
      (encPair encInstBin encNat) (encList encNat) := hc.comp (by fun_prop)
  have h := ComputableTidilyInPolyTime.mapWithInput (encIn := encInstBin)
    (list := fun I : Inst => I.1) (f := fun I _ => classVals I)
    (ComputableTidilyInPolyTime.fst (encList encNat)
      (encPair (encList (encList (encPair encNat encNat))) (encList (encList encNat)))) hf
  exact (boundedSections_polyTime k).comp h

theorem classWeight_polyTime :
    ComputableTidilyInPolyTime (fun p : Inst × (ℕ × ℕ) => classWeight p.1 p.2.1 p.2.2)
      (encPair encInstBin (encPair encNat encNat)) encNat := by
  have hu := ComputableTidilyInPolyTime.unary_to_binary
  have hw := writtenVals_polyTime
  have hd := distinctVals_polyTime.comp writtenVals_polyTime
  simp only [Function.comp_def] at hd
  have hf : ComputableTidilyInPolyTime
      (fun p : Inst × (ℕ × ℕ) => (distinctVals (writtenVals p.1)).filter
        fun u => decide (u < p.2.1))
      (encPair encInstBin (encPair encNat encNat)) (encList encNat) :=
    ComputableTidilyInPolyTime.filterWithInput (hd.comp (by fun_prop)) (by fun_prop)
  have hl := (ComputableTidilyInPolyTime.length encNat).comp hf
  simp only [Function.comp_def] at hl
  unfold classWeight
  fun_prop

/-- The binary validity test of a class vector (conditions read at binary indices). -/
def validBin (p : Inst × List ℕ) : Bool :=
  p.1.2.1.all (fun c => c.any (condHoldsBin p.2)) && !decide (p.2 ∈ p.1.2.2)

theorem validB_polyTime :
    ComputableTidilyInPolyTime validB (encPair encInstBin (encList encNat)) encBool := by
  have h := condHoldsBin_polyTime.tidy
  have he : validBin = validB := by
    have h : condHoldsBin = condHoldsB := funext fun s => funext fun a => condHoldsBin_eq s a
    funext p
    simp only [validBin, validB, h]
  rw [← he]
  unfold validBin
  fun_prop

lemma length_encNat_le_of_mem_domains {I : Inst} {d : ℕ} (h : d ∈ I.1) :
    (encNat d).length ≤ (encInstBin I).length :=
  (length_encNat_le_of_mem h).trans (length_domains_le_bin I)

theorem classStateWeight_polyTime :
    ComputableTidilyInPolyTime classStateWeight (encPair encInstBin (encList encNat)) encNat := by
  have hw := classWeight_polyTime
  have hlist : ComputableTidilyInPolyTime (fun x : Inst × List ℕ => x.2.zip x.1.1)
      (encPair encInstBin (encList encNat)) (encList (encPair encNat encNat)) := by fun_prop
  have hstep : ComputableTidilyInPolyTime
      (fun p : ((Inst × List ℕ) × ℕ) × (ℕ × ℕ) => p.1.2 * classWeight p.1.1.1 p.2.2 p.2.1)
      (encPair (encPair (encPair encInstBin (encList encNat)) encNat) (encPair encNat encNat))
      encNat := by
    have hpair : ComputableTidilyInPolyTime
        (fun p : ((Inst × List ℕ) × ℕ) × (ℕ × ℕ) => (p.1.1.1, (p.2.2, p.2.1)))
        (encPair (encPair (encPair encInstBin (encList encNat)) encNat) (encPair encNat encNat))
        (encPair encInstBin (encPair encNat encNat)) := by fun_prop
    have h := hw.comp hpair
    simp only [Function.comp_def] at h
    fun_prop
  have hinit : ComputableTidilyInPolyTime (fun _ : Inst × List ℕ => 1)
      (encPair encInstBin (encList encNat)) encNat := by fun_prop
  have e : classStateWeight = fun x : Inst × List ℕ =>
      (x.2.zip x.1.1).foldl (fun acc q => acc * classWeight x.1 q.2 q.1) 1 := rfl
  rw [e]
  refine ComputableTidilyInPolyTime.foldlWithInput_of_bounded_growth
    (encIn := encPair encInstBin (encList encNat)) (encB := encNat)
    (encA := encPair encNat encNat) (encL := encList (encPair encNat encNat))
    (list := fun x : Inst × List ℕ => x.2.zip x.1.1) (init := fun _ => 1)
    (step := fun (x : Inst × List ℕ) (acc : ℕ) (q : ℕ × ℕ) => acc * classWeight x.1 q.2 q.1)
    (growth := fun x => (encPair encInstBin (encList encNat) x).length)
    hinit ⟨hlist, hstep, inferInstance, inferInstance⟩
    ⟨PolyBounded.self, fun x a q hq => ?_⟩
  refine (length_encNat_mul_le a _).trans (Nat.add_le_add_left ?_ _)
  refine (ComputableTidilyInO.length_encNat_mono (classWeight_le _ _ _)).trans ?_
  refine (length_encNat_le_of_mem_domains (List.of_mem_zip hq).2).trans ?_
  exact length_le_encPair_left _ _ x

lemma prod_classWeight_le (I : Inst) (d : List ℕ) {c : List ℕ} (h : c.length = d.length) :
    ((c.zip d).map fun q => classWeight I q.2 q.1).prod ≤ d.prod := by
  induction d generalizing c with
  | nil => simp
  | cons a d ih =>
    rcases c with _ | ⟨v, c⟩
    · simp at h
    · simp only [List.zip_cons_cons, List.map_cons, List.prod_cons]
      exact Nat.mul_le_mul (classWeight_le I a v) (ih (by simpa using h))

lemma classStateWeight_le_domProd {k : ℕ} {I : Inst} {c : List ℕ} (hc : c ∈ classStates k I) :
    classStateWeight (I, c) ≤ domProd I := by
  have hlen := length_of_mem_boundedSections hc
  rw [List.length_map] at hlen
  rw [classStateWeight, foldl_mul_eq, one_mul, domProd, ← List.prod_eq_foldl]
  exact prod_classWeight_le I I.1 hlen

theorem countClasses_polyTime (k : ℕ) :
    ComputableTidilyInPolyTime (countClasses k) encInstBin encNat := by
  have hc := classStates_polyTime k
  have hv := validB_polyTime
  have hw := classStateWeight_polyTime
  have hp := domProd_polyTime.tidy.polyBounded_length
  unfold countClasses
  refine ComputableTidilyInPolyTime.foldlWithInput_of_bounded_growth (encA := encList encNat)
    (encL := encList (encList encNat))
    (step := fun I acc c => acc + if validB (I, c) then classStateWeight (I, c) else 0)
    (growth := fun I => (encNat (domProd I)).length + 1)
    (by fun_prop) ⟨hc, by fun_prop, inferInstance, inferInstance⟩
    ⟨hp.add (.const 1), fun I a c hc => ?_⟩
  refine (length_encNat_add_le_add a _).trans ?_
  have : (encNat (if validB (I, c) then classStateWeight (I, c) else 0)).length ≤
      (encNat (domProd I)).length := by
    refine ComputableTidilyInO.length_encNat_mono ?_
    split_ifs
    · exact classStateWeight_le_domProd hc
    · exact Nat.zero_le _
  omega

/-- **(b), counting: with at most `k` attributes, |M(T₀)| is polynomial-time computable,** for
every fixed `k`, constraints arbitrary and domain sizes in binary (zero on instances with more
attributes). -/
theorem missingCountFixedAttrs_polyTime (k : ℕ) :
    ComputableInPolyTime (fun I : Inst => if I.n ≤ k then missingCount I else 0)
      encInstBin encNat := by
  have h := countClasses_polyTime k
  have heq : (fun I : Inst => if I.n ≤ k then missingCount I else 0) =
      fun I => if decide (I.1.length ≤ k) then countClasses k I else 0 := by
    funext I
    by_cases hI : I.n ≤ k
    · simp [hI, missingCount_eq_countClasses hI]
    · simp [hI]
  rw [heq]
  refine .of_tidy ?_
  fun_prop

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

theorem missingCountFixedAttrs_polyTime_unary (k : ℕ) :
    ComputableInPolyTime (fun I : Inst => if I.n ≤ k then missingCount I else 0)
      encInst encNat :=
  (missingCountFixedAttrs_polyTime k).comp encInst_to_encInstBin_polyTime

end Latc.PaperD.General
