import LatcComplexity.Valiant.Gadget

/-!
# The one-call reduction from `#SAT` to `#Monotone-2SAT`: counting

Facts on the vertex codes and the clause lists of `LatcComplexity/Valiant/Gadget.lean`; the
conflict graph's vertices fall into `n + m` cliques (one per variable, one per clause), so an
independent set has at most `n + m` vertices (`card_le_of_indep`); and the independent sets with
exactly `n + m` vertices are in bijection with the models of `φ` (`modelCount_eq_card`): a model
`σ` gives the vertices `(i, σ i)` and the first true literal of each clause (`setOf`).
-/

namespace Latc.PaperD.Valiant

open Cslib.Complexity Cslib.Logic.PL

/-! ### Codes -/

theorem vv_mod (i : ℕ) (b : Bool) : vv i b % 3 = 0 := by simp [vv]

theorem cv_mod (o : Occurrence ℕ) : cv o % 3 = 1 := by simp [cv, Nat.add_mod]

theorem lv_mod (u q : ℕ) : lv u q % 3 = 2 := by simp [lv, Nat.add_mod]

theorem vv_ne_cv (i : ℕ) (b : Bool) (o : Occurrence ℕ) : vv i b ≠ cv o := fun h => by
  have := congrArg (· % 3) h
  simp only [vv_mod, cv_mod] at this
  omega

theorem lv_ne_vv (u q i : ℕ) (b : Bool) : lv u q ≠ vv i b := fun h => by
  have := congrArg (· % 3) h
  simp only [vv_mod, lv_mod] at this
  omega

theorem lv_ne_cv (u q : ℕ) (o : Occurrence ℕ) : lv u q ≠ cv o := fun h => by
  have := congrArg (· % 3) h
  simp only [cv_mod, lv_mod] at this
  omega

theorem vv_inj {i j : ℕ} {b c : Bool} : vv i b = vv j c ↔ i = j ∧ b = c := by
  constructor
  · intro h
    simp only [vv, Nat.mul_left_cancel_iff (by norm_num : 0 < 3), Nat.pair_eq_pair] at h
    exact ⟨h.1, by cases b <;> cases c <;> simp_all⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem lv_inj {u u' q q' : ℕ} : lv u q = lv u' q' ↔ u = u' ∧ q = q' := by
  constructor
  · intro h
    simp only [lv, Nat.add_right_cancel_iff, Nat.mul_left_cancel_iff (by norm_num : 0 < 3),
      Nat.pair_eq_pair] at h
    exact h
  · rintro ⟨rfl, rfl⟩
    rfl

theorem cv_eq {o o' : Occurrence ℕ} (h : cv o = cv o') : o.1 = o'.1 ∧ o.2.1 = o'.2.1 := by
  simp only [cv, Nat.add_right_cancel_iff, Nat.mul_left_cancel_iff (by norm_num : 0 < 3),
    Nat.pair_eq_pair] at h
  exact h

/-- Two occurrences with the same clause and position are equal. -/
theorem occ_ext {φ : CNF ℕ} {o o' : Occurrence ℕ} (ho : o ∈ occurrences φ)
    (ho' : o' ∈ occurrences φ) (h1 : o.1 = o'.1) (h2 : o.2.1 = o'.2.1) : o = o' := by
  obtain ⟨a, b, l⟩ := o
  obtain ⟨a', b', l'⟩ := o'
  simp only at h1 h2
  subst h1 h2
  obtain ⟨_, _, hl⟩ := mem_occurrences.1 ho
  obtain ⟨_, _, hl'⟩ := mem_occurrences.1 ho'
  simp only at hl hl'
  rw [hl, hl']

theorem cv_inj {φ : CNF ℕ} {o o' : Occurrence ℕ} (ho : o ∈ occurrences φ)
    (ho' : o' ∈ occurrences φ) : cv o = cv o' ↔ o = o' :=
  ⟨fun h => occ_ext ho ho' (cv_eq h).1 (cv_eq h).2, fun h => h ▸ rfl⟩

/-! ### Membership -/

variable {φ : CNF ℕ} {n : ℕ}

theorem mem_verts {x : ℕ} : x ∈ verts φ n ↔
    (∃ i < n, ∃ b, x = vv i b) ∨ ∃ o ∈ occurrences φ, x = cv o := by
  simp only [verts, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map]
  constructor
  · rintro (⟨i, hi, h | h⟩ | ⟨o, ho, rfl⟩)
    · exact Or.inl ⟨i, hi, true, h⟩
    · exact Or.inl ⟨i, hi, false, h⟩
    · exact Or.inr ⟨o, ho, rfl⟩
  · rintro (⟨i, hi, b, rfl⟩ | ⟨o, ho, rfl⟩)
    · cases b
      · exact Or.inl ⟨i, hi, Or.inr rfl⟩
      · exact Or.inl ⟨i, hi, Or.inl rfl⟩
    · exact Or.inr ⟨o, ho, rfl⟩

theorem mem_graphClauses {c : Clause ℕ} : c ∈ graphClauses φ n ↔
    (∃ i < n, c = edge (vv i true) (vv i false)) ∨ ∃ o ∈ occurrences φ,
      (c = edge (cv o) (vv o.2.2.1 (!o.2.2.2)) ∨ ∃ o' ∈ occurrences φ, o'.1 = o.1 ∧
        o'.2.1 < o.2.1 ∧ (c = edge (cv o) (cv o') ∨ c = edge (cv o) (vv o'.2.2.1 o'.2.2.2))) := by
  simp only [graphClauses, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_cons, List.mem_filter, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.not_mem_nil, or_false]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨o, ho, h | ⟨o', ⟨ho', h1, h2⟩, h⟩⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨o, ho, Or.inl h⟩
    · exact Or.inr ⟨o, ho, Or.inr ⟨o', ho', h1, h2, h⟩⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨o, ho, h | ⟨o', ho', h1, h2, h⟩⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨o, ho, Or.inl h⟩
    · exact Or.inr ⟨o, ho, Or.inr ⟨o', ⟨ho', h1, h2⟩, h⟩⟩

theorem mem_leafClauses {t : ℕ} {c : Clause ℕ} : c ∈ leafClauses φ n t ↔
    ∃ u ∈ verts φ n, ∃ q < t, c = edge u (lv u q) := by
  simp only [leafClauses, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨u, hu, q, hq, rfl⟩
    exact ⟨u, hu, q, hq, rfl⟩
  · rintro ⟨u, hu, q, hq, rfl⟩
    exact ⟨u, hu, q, hq, rfl⟩

theorem eval_edge (σ : ℕ → Bool) (a b : ℕ) : Clause.eval σ (edge a b) = (σ a || σ b) := by
  simp [edge, Clause.eval, Literal.eval]

theorem mem_edge {a b : ℕ} {l : Literal ℕ} : l ∈ edge a b ↔ l = (a, true) ∨ l = (b, true) := by
  simp [edge]

/-! ### Independent sets of the conflict graph -/

/-- `S` is independent in the conflict graph: every edge has an end outside `S`. -/
def Indep (φ : CNF ℕ) (n : ℕ) (S : Finset ℕ) : Prop :=
  (graphClauses φ n).eval (fun x => decide (x ∉ S)) = true

instance (φ : CNF ℕ) (n : ℕ) : DecidablePred (Indep φ n) := fun _ => by
  unfold Indep
  infer_instance

theorem eval_edge_not_mem (S : Finset ℕ) (a b : ℕ) :
    Clause.eval (fun x => decide (x ∉ S)) (edge a b) = true ↔ ¬(a ∈ S ∧ b ∈ S) := by
  rw [eval_edge]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  tauto

theorem indep_iff {S : Finset ℕ} : Indep φ n S ↔
    (∀ i < n, ¬(vv i true ∈ S ∧ vv i false ∈ S)) ∧
    (∀ o ∈ occurrences φ, ¬(cv o ∈ S ∧ vv o.2.2.1 (!o.2.2.2) ∈ S)) ∧
    (∀ o ∈ occurrences φ, ∀ o' ∈ occurrences φ, o'.1 = o.1 → o'.2.1 < o.2.1 →
      ¬(cv o ∈ S ∧ cv o' ∈ S) ∧ ¬(cv o ∈ S ∧ vv o'.2.2.1 o'.2.2.2 ∈ S)) := by
  unfold Indep CNF.eval
  rw [List.all_eq_true]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun o ho => ?_, fun o ho o' ho' h1 h2 => ⟨?_, ?_⟩⟩
    · exact (eval_edge_not_mem S _ _).1 (h _ (mem_graphClauses.2 (Or.inl ⟨i, hi, rfl⟩)))
    · exact (eval_edge_not_mem S _ _).1 (h _ (mem_graphClauses.2 (Or.inr ⟨o, ho, Or.inl rfl⟩)))
    · exact (eval_edge_not_mem S _ _).1
        (h _ (mem_graphClauses.2 (Or.inr ⟨o, ho, Or.inr ⟨o', ho', h1, h2, Or.inl rfl⟩⟩)))
    · exact (eval_edge_not_mem S _ _).1
        (h _ (mem_graphClauses.2 (Or.inr ⟨o, ho, Or.inr ⟨o', ho', h1, h2, Or.inr rfl⟩⟩)))
  · rintro ⟨hv, hn, hc⟩ c hc'
    rcases mem_graphClauses.1 hc' with ⟨i, hi, rfl⟩ | ⟨o, ho, rfl | ⟨o', ho', h1, h2, rfl | rfl⟩⟩
    · exact (eval_edge_not_mem S _ _).2 (hv i hi)
    · exact (eval_edge_not_mem S _ _).2 (hn o ho)
    · exact (eval_edge_not_mem S _ _).2 (hc o ho o' ho' h1 h2).1
    · exact (eval_edge_not_mem S _ _).2 (hc o ho o' ho' h1 h2).2

/-- The part of a vertex: its variable, or the clause of its occurrence. -/
def part (x : ℕ) : ℕ ⊕ ℕ :=
  if x % 3 = 0 then .inl (Nat.unpair (x / 3)).1 else .inr (Nat.unpair (x / 3)).1

theorem part_vv (i : ℕ) (b : Bool) : part (vv i b) = .inl i := by
  simp [part, vv]

theorem part_cv (o : Occurrence ℕ) : part (cv o) = .inr o.1 := by
  have h : cv o / 3 = Nat.pair o.1 o.2.1 := by unfold cv; omega
  simp [part, cv_mod, h]

/-- Two vertices of an independent set lie in different parts. -/
theorem part_injOn {S : Finset ℕ} (hS : ∀ x ∈ S, x ∈ verts φ n) (hI : Indep φ n S) :
    Set.InjOn part S := by
  obtain ⟨hv, -, hc⟩ := indep_iff.1 hI
  intro x hx y hy hxy
  have hx' := hS x hx
  have hy' := hS y hy
  rw [Finset.mem_coe] at hx hy
  rcases mem_verts.1 hx' with ⟨i, hi, b, rfl⟩ | ⟨o, ho, rfl⟩ <;>
    rcases mem_verts.1 hy' with ⟨j, hj, c, rfl⟩ | ⟨o', ho', rfl⟩
  · rw [part_vv, part_vv, Sum.inl.injEq] at hxy
    subst hxy
    rw [vv_inj]
    refine ⟨rfl, ?_⟩
    by_contra hbc
    cases b <;> cases c
    · exact hbc rfl
    · exact hv i hi ⟨hy, hx⟩
    · exact hv i hi ⟨hx, hy⟩
    · exact hbc rfl
  · rw [part_vv, part_cv] at hxy
    exact absurd hxy Sum.inl_ne_inr
  · rw [part_vv, part_cv] at hxy
    exact absurd hxy Sum.inr_ne_inl
  · rw [part_cv, part_cv, Sum.inr.injEq] at hxy
    rw [cv_inj ho ho']
    rcases lt_trichotomy o.2.1 o'.2.1 with h | h | h
    · exact absurd ⟨hy, hx⟩ (hc o' ho' o ho hxy h).1
    · exact occ_ext ho ho' hxy h
    · exact absurd ⟨hx, hy⟩ (hc o ho o' ho' hxy.symm h).1

theorem part_mapsTo {x : ℕ} (hx : x ∈ verts φ n) :
    part x ∈ (Finset.range n).disjSum (Finset.range φ.length) := by
  rcases mem_verts.1 hx with ⟨i, hi, b, rfl⟩ | ⟨o, ho, rfl⟩
  · simp [part_vv, hi]
  · obtain ⟨h1, -, -⟩ := mem_occurrences.1 ho
    simp [part_cv, h1]

/-- **An independent set has at most `n + m` vertices**: one per part. -/
theorem card_le_of_indep {S : Finset ℕ} (hS : ∀ x ∈ S, x ∈ verts φ n) (hI : Indep φ n S) :
    S.card ≤ n + φ.length := by
  have := Finset.card_le_card_of_injOn part (fun x hx => part_mapsTo (hS x hx))
    (part_injOn hS hI)
  simpa using this

/-! ### Maximum independent sets are satisfying assignments -/

/-- The occurrence `o` holds the first true literal of its clause under `σ`. -/
def firstTrue (φ : CNF ℕ) (σ : ℕ → Bool) (o : Occurrence ℕ) : Bool :=
  Literal.eval σ o.2.2 && (occurrences φ).all fun o' =>
    !(o'.1 == o.1 && decide (o'.2.1 < o.2.1)) || !Literal.eval σ o'.2.2

theorem firstTrue_iff {σ : ℕ → Bool} {o : Occurrence ℕ} : firstTrue φ σ o = true ↔
    Literal.eval σ o.2.2 = true ∧ ∀ o' ∈ occurrences φ, o'.1 = o.1 → o'.2.1 < o.2.1 →
      Literal.eval σ o'.2.2 = false := by
  simp only [firstTrue, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq, decide_eq_false_iff_not]
  refine and_congr_right fun _ => forall₂_congr fun o' _ => ?_
  tauto

theorem literal_eval_iff {σ : ℕ → Bool} {l : Literal ℕ} :
    Literal.eval σ l = true ↔ σ l.1 = l.2 := by
  simp [Literal.eval]

/-- The independent set of an assignment: the vertices `(i, σ i)` and the first true literal of
each clause. -/
def setOf (φ : CNF ℕ) (n : ℕ) (σ : ℕ → Bool) : Finset ℕ :=
  ((Finset.range n).image fun i => vv i (σ i)) ∪
    (((occurrences φ).toFinset.filter fun o => firstTrue φ σ o).image cv)

theorem vv_mem_setOf {σ : ℕ → Bool} {i : ℕ} {b : Bool} :
    vv i b ∈ setOf φ n σ ↔ i < n ∧ σ i = b := by
  simp only [setOf, Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_filter,
    List.mem_toFinset]
  constructor
  · rintro (⟨j, hj, h⟩ | ⟨o, -, h⟩)
    · obtain ⟨rfl, rfl⟩ := vv_inj.1 h
      exact ⟨hj, rfl⟩
    · exact absurd h.symm (vv_ne_cv _ _ _)
  · rintro ⟨hi, rfl⟩
    exact Or.inl ⟨i, hi, rfl⟩

theorem cv_mem_setOf {σ : ℕ → Bool} {o : Occurrence ℕ} (ho : o ∈ occurrences φ) :
    cv o ∈ setOf φ n σ ↔ firstTrue φ σ o = true := by
  simp only [setOf, Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_filter,
    List.mem_toFinset]
  constructor
  · rintro (⟨j, -, h⟩ | ⟨o', ⟨ho', h⟩, he⟩)
    · exact absurd h (vv_ne_cv _ _ _)
    · rwa [← (cv_inj ho' ho).1 he]
  · intro h
    exact Or.inr ⟨o, ⟨ho, h⟩, rfl⟩

theorem setOf_subset (σ : ℕ → Bool) :
    ∀ x ∈ setOf φ n σ, x ∈ verts φ n := by
  intro x hx
  simp only [setOf, Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_filter,
    List.mem_toFinset] at hx
  rcases hx with ⟨i, hi, rfl⟩ | ⟨o, ⟨ho, -⟩, rfl⟩
  · exact mem_verts.2 (Or.inl ⟨i, hi, _, rfl⟩)
  · exact mem_verts.2 (Or.inr ⟨o, ho, rfl⟩)

/-- Two first true literals of the same clause are the same occurrence. -/
theorem firstTrue_unique {σ : ℕ → Bool} {o o' : Occurrence ℕ} (ho : o ∈ occurrences φ)
    (ho' : o' ∈ occurrences φ) (h1 : o.1 = o'.1) (h : firstTrue φ σ o = true)
    (h' : firstTrue φ σ o' = true) : o = o' := by
  rw [firstTrue_iff] at h h'
  rcases lt_trichotomy o.2.1 o'.2.1 with hlt | heq | hlt
  · have := h'.2 o ho h1 hlt
    rw [h.1] at this
    exact absurd this (by decide)
  · exact occ_ext ho ho' h1 heq
  · have := h.2 o' ho' h1.symm hlt
    rw [h'.1] at this
    exact absurd this (by decide)

/-- A satisfied clause has a first true literal. -/
theorem exists_firstTrue {σ : ℕ → Bool} (hσ : φ.eval σ = true) {j : ℕ} (hj : j < φ.length) :
    ∃ o ∈ occurrences φ, o.1 = j ∧ firstTrue φ σ o = true := by
  have hc : Clause.eval σ φ[j] = true := by
    simp only [CNF.eval, List.all_eq_true] at hσ
    exact hσ _ (List.getElem_mem hj)
  have hex : ∃ p, ∃ hp : p < φ[j].length, Literal.eval σ φ[j][p] = true := by
    obtain ⟨l, hl, hlt⟩ := List.any_eq_true.1 hc
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hl
    exact ⟨p, hp, hlt⟩
  classical
  let p := Nat.find hex
  obtain ⟨hp, hpt⟩ := Nat.find_spec hex
  refine ⟨(j, p, φ[j][p]), mem_occurrences.2 ⟨hj, hp, rfl⟩, rfl, firstTrue_iff.2 ⟨hpt, ?_⟩⟩
  intro o' ho' h1 h2
  obtain ⟨hj', hp', hl'⟩ := mem_occurrences.1 ho'
  have hmin := Nat.find_min hex h2
  simp only at h1
  subst h1
  rw [hl']
  by_contra hne
  exact hmin ⟨hp', by simpa using hne⟩

/-- The set of an assignment is independent. -/
theorem indep_setOf (σ : ℕ → Bool) : Indep φ n (setOf φ n σ) := by
  refine indep_iff.2 ⟨fun i _ ⟨h1, h2⟩ => ?_, fun o ho ⟨h1, h2⟩ => ?_,
    fun o ho o' ho' h1 h2 => ⟨fun ⟨h3, h4⟩ => ?_, fun ⟨h3, h4⟩ => ?_⟩⟩
  · rw [vv_mem_setOf] at h1 h2
    rw [h1.2] at h2
    exact absurd h2.2 (by decide)
  · rw [cv_mem_setOf ho, firstTrue_iff, literal_eval_iff] at h1
    rw [vv_mem_setOf] at h2
    have h3 := h2.2
    rw [h1.1] at h3
    revert h3
    cases o.2.2.2 <;> decide
  · rw [cv_mem_setOf ho] at h3
    rw [cv_mem_setOf ho'] at h4
    have := firstTrue_unique ho ho' h1.symm h3 h4
    subst this
    exact absurd h2 (lt_irrefl _)
  · rw [cv_mem_setOf ho, firstTrue_iff] at h3
    rw [vv_mem_setOf] at h4
    have := h3.2 o' ho' h1 h2
    simp [Literal.eval, h4.2] at this

theorem card_disjSum_parts : ((Finset.range n).disjSum (Finset.range φ.length)).card =
    n + φ.length := by
  simp

/-- The set of a satisfying assignment has `n + m` vertices. -/
theorem card_setOf {σ : ℕ → Bool} (hσ : φ.eval σ = true) :
    (setOf φ n σ).card = n + φ.length := by
  refine le_antisymm (card_le_of_indep (setOf_subset σ) (indep_setOf σ)) ?_
  rw [← card_disjSum_parts]
  refine Finset.card_le_card_of_surjOn part ?_
  intro y hy
  rw [Finset.mem_coe, Finset.mem_disjSum] at hy
  rcases hy with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [Finset.mem_range] at hi
    exact ⟨vv i (σ i), Finset.mem_coe.2 (vv_mem_setOf.2 ⟨hi, rfl⟩), part_vv _ _⟩
  · rw [Finset.mem_range] at hj
    obtain ⟨o, ho, rfl, hf⟩ := exists_firstTrue hσ hj
    exact ⟨cv o, Finset.mem_coe.2 ((cv_mem_setOf ho).2 hf), part_cv _⟩

/-- An independent set of `n + m` vertices is the set of a satisfying assignment. -/
theorem exists_of_indep (hd : ∀ o ∈ occurrences φ, o.2.2.1 < n) {S : Finset ℕ}
    (hS : ∀ x ∈ S, x ∈ verts φ n) (hI : Indep φ n S) (hcard : S.card = n + φ.length) :
    ∃ σ, φ.eval σ = true ∧ setOf φ n σ = S := by
  obtain ⟨hv, hn, hc⟩ := indep_iff.1 hI
  have hsurj : ∀ y ∈ (Finset.range n).disjSum (Finset.range φ.length), ∃ x ∈ S, part x = y := by
    intro y hy
    obtain ⟨x, hx, h⟩ := Finset.surj_on_of_inj_on_of_card_le (fun x _ => part x)
      (fun x hx => part_mapsTo (hS x hx)) (fun a b ha hb h => part_injOn hS hI ha hb h)
      (by rw [card_disjSum_parts, hcard]) y hy
    exact ⟨x, hx, h.symm⟩
  classical
  let σ : ℕ → Bool := fun i => decide (vv i true ∈ S)
  have ha : ∀ i < n, ∀ b, vv i b ∈ S ↔ σ i = b := by
    intro i hi b
    obtain ⟨x, hx, hpx⟩ := hsurj (.inl i) (by simp [hi])
    rcases mem_verts.1 (hS x hx) with ⟨j, -, c, rfl⟩ | ⟨o, -, rfl⟩
    · rw [part_vv, Sum.inl.injEq] at hpx
      subst hpx
      cases b
      · simp only [σ, decide_eq_false_iff_not]
        constructor
        · exact fun h h' => hv j hi ⟨h', h⟩
        · intro h
          cases c
          · exact hx
          · exact absurd hx h
      · simp [σ]
    · rw [part_cv] at hpx
      exact absurd hpx Sum.inr_ne_inl
  have hlit : ∀ o ∈ occurrences φ, cv o ∈ S → Literal.eval σ o.2.2 = true := by
    intro o ho hx
    rw [literal_eval_iff]
    have h1 : vv o.2.2.1 (!o.2.2.2) ∉ S := fun h => hn o ho ⟨hx, h⟩
    rw [ha _ (hd o ho)] at h1
    cases h : σ o.2.2.1 <;> cases h' : o.2.2.2 <;> simp_all
  have hfirst : ∀ o ∈ occurrences φ, cv o ∈ S → firstTrue φ σ o = true := by
    intro o ho hx
    refine firstTrue_iff.2 ⟨hlit o ho hx, fun o' ho' h1 h2 => ?_⟩
    have h3 : vv o'.2.2.1 o'.2.2.2 ∉ S := fun h => (hc o ho o' ho' h1 h2).2 ⟨hx, h⟩
    rw [ha _ (hd o' ho')] at h3
    simpa [Literal.eval] using h3
  have hcl : ∀ j < φ.length, ∃ o ∈ occurrences φ, o.1 = j ∧ cv o ∈ S := by
    intro j hj
    obtain ⟨x, hx, hpx⟩ := hsurj (.inr j) (by simp [hj])
    rcases mem_verts.1 (hS x hx) with ⟨i, -, c, rfl⟩ | ⟨o, ho, rfl⟩
    · rw [part_vv] at hpx
      exact absurd hpx Sum.inl_ne_inr
    · rw [part_cv, Sum.inr.injEq] at hpx
      exact ⟨o, ho, hpx, hx⟩
  refine ⟨σ, ?_, ?_⟩
  · simp only [CNF.eval, List.all_eq_true]
    intro c hc'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc'
    obtain ⟨o, ho, rfl, hx⟩ := hcl j hj
    obtain ⟨h1, hp, hl⟩ := mem_occurrences.1 ho
    refine List.any_eq_true.2 ⟨o.2.2, ?_, hlit o ho hx⟩
    rw [hl]
    exact List.getElem_mem hp
  · ext x
    constructor
    · intro hx
      simp only [setOf, Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_filter,
        List.mem_toFinset] at hx
      rcases hx with ⟨i, hi, rfl⟩ | ⟨o, ⟨ho, hf⟩, rfl⟩
      · exact (ha i hi _).2 rfl
      · obtain ⟨o0, ho0, h1, hx0⟩ := hcl o.1 (mem_occurrences.1 ho).1
        rwa [firstTrue_unique ho ho0 h1.symm hf (hfirst o0 ho0 hx0)]
    · intro hx
      rcases mem_verts.1 (hS x hx) with ⟨i, hi, b, rfl⟩ | ⟨o, ho, rfl⟩
      · exact vv_mem_setOf.2 ⟨hi, (ha i hi b).1 hx⟩
      · exact (cv_mem_setOf ho).2 (hfirst o ho hx)

/-- Two assignments have the same set exactly when they agree on the variables. -/
theorem setOf_eq_iff (hd : ∀ o ∈ occurrences φ, o.2.2.1 < n) (hn : ∀ i < n, i ∈ φ.vars)
    {σ τ : ℕ → Bool} : setOf φ n σ = setOf φ n τ ↔ ∀ v ∈ φ.vars, σ v = τ v := by
  have hvars : ∀ v ∈ φ.vars, v < n := by
    intro v hv
    rw [← map_occurrences] at hv
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hv
    exact hd o ho
  constructor
  · intro h v hv
    have : vv v (σ v) ∈ setOf φ n τ := h ▸ vv_mem_setOf.2 ⟨hvars v hv, rfl⟩
    exact ((vv_mem_setOf.1 this).2).symm
  · intro h
    have hag : ∀ i < n, σ i = τ i := fun i hi => h i (hn i hi)
    have hl : ∀ o ∈ occurrences φ, Literal.eval σ o.2.2 = Literal.eval τ o.2.2 := by
      intro o ho
      simp only [Literal.eval, hag _ (hd o ho)]
    have hf : ∀ o ∈ occurrences φ, firstTrue φ σ o = firstTrue φ τ o := by
      intro o ho
      apply Bool.eq_iff_iff.2
      rw [firstTrue_iff, firstTrue_iff, hl o ho]
      refine and_congr_right fun _ => forall₂_congr fun o' ho' => ?_
      rw [hl o' ho']
    unfold setOf
    congr 1
    · exact Finset.image_congr fun i hi => by rw [hag i (Finset.mem_range.1 hi)]
    · congr 1
      exact Finset.filter_congr fun o ho => by rw [hf o (List.mem_toFinset.1 ho)]

/-! ### Counting through assignments of the vertices -/

/-- The vertices of the conflict graph, as a type. -/
abbrev V0 (φ : CNF ℕ) (n : ℕ) : Type := {x // x ∈ (verts φ n).toFinset}

/-- The vertices that an assignment of the vertices sets to `false`. -/
def falseSet (g : V0 φ n → Bool) : Finset ℕ :=
  (Finset.univ.filter fun x => g x = false).map (Function.Embedding.subtype _)

theorem mem_falseSet {g : V0 φ n → Bool} {x : ℕ} :
    x ∈ falseSet g ↔ ∃ h : x ∈ (verts φ n).toFinset, g ⟨x, h⟩ = false := by
  simp [falseSet]

theorem falseSet_subset (g : V0 φ n → Bool) : ∀ x ∈ falseSet g, x ∈ verts φ n := by
  intro x hx
  obtain ⟨h, -⟩ := mem_falseSet.1 hx
  exact List.mem_toFinset.1 h

/-- **Maximum independent sets count the models.** -/
theorem modelCount_eq_card (hd : ∀ o ∈ occurrences φ, o.2.2.1 < n)
    (hn : ∀ i < n, i ∈ φ.vars) :
    φ.modelCount = (Finset.univ.filter fun g : V0 φ n → Bool =>
      Indep φ n (falseSet g) ∧ (falseSet g).card = n + φ.length).card := by
  classical
  let f : (ℕ → Bool) → (V0 φ n → Bool) := fun σ x => decide (x.1 ∉ setOf φ n σ)
  have hfS : ∀ σ, falseSet (f σ) = setOf φ n σ := by
    intro σ
    ext x
    rw [mem_falseSet]
    simp only [f, decide_eq_false_iff_not, not_not]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨List.mem_toFinset.2 (setOf_subset σ x h), h⟩⟩
  have hfeq : ∀ σ τ, f σ = f τ ↔ setOf φ n σ = setOf φ n τ := by
    intro σ τ
    constructor
    · intro h
      rw [← hfS σ, ← hfS τ, h]
    · intro h
      funext x
      simp only [f, h]
  refine CNF.modelCount_eq_card_filter f _ (fun σ τ _ _ => (hfeq σ τ).trans
    (setOf_eq_iff hd hn)) fun g => ⟨fun ⟨hI, hc⟩ => ?_, ?_⟩
  · obtain ⟨σ, hσ, hS⟩ := exists_of_indep hd (falseSet_subset g) hI hc
    refine ⟨σ, hσ, funext fun x => ?_⟩
    simp only [f, hS]
    cases hx : g x
    · simp only [decide_eq_false_iff_not, not_not]
      exact mem_falseSet.2 ⟨x.2, hx⟩
    · simp only [decide_eq_true_eq]
      intro h
      obtain ⟨_, h'⟩ := mem_falseSet.1 h
      rw [hx] at h'
      exact absurd h' (by decide)
  · rintro ⟨σ, hσ, rfl⟩
    rw [hfS]
    exact ⟨indep_setOf σ, card_setOf hσ⟩

end Latc.PaperD.Valiant
