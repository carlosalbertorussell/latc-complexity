import LatcComplexity.Valiant.Counting

/-!
# The pendant leaves

The models of `graphClauses φ n ++ leafClauses φ n t` are counted by the independent sets of the
conflict graph: an independent set `S` (the vertices set to `false`) forces the leaves of its
vertices to `true` and leaves the `t` leaves of every other vertex free, so it contributes
`2^(t · (N − |S|))`.
-/

namespace Latc.PaperD.Valiant

open Cslib.Complexity Cslib.Logic.PL

variable {φ : CNF ℕ} {n : ℕ}

theorem mem_vars_iff {ψ : CNF ℕ} {v : ℕ} : v ∈ ψ.vars ↔ ∃ c ∈ ψ, ∃ l ∈ c, l.1 = v := by
  simp only [CNF.vars, List.mem_map, List.mem_flatten]
  constructor
  · rintro ⟨l, ⟨c, hc, hl⟩, rfl⟩
    exact ⟨c, hc, l, hl, rfl⟩
  · rintro ⟨c, hc, l, hl, rfl⟩
    exact ⟨l, ⟨c, hc, hl⟩, rfl⟩

theorem graph_vars_mem (hd : ∀ o ∈ occurrences φ, o.2.2.1 < n) {c : Clause ℕ}
    (hc : c ∈ graphClauses φ n) {l : Literal ℕ} (hl : l ∈ c) : l.1 ∈ verts φ n := by
  have hvv : ∀ i < n, ∀ b, vv i b ∈ verts φ n := fun i hi b => mem_verts.2 (Or.inl ⟨i, hi, b, rfl⟩)
  have hcv : ∀ o ∈ occurrences φ, cv o ∈ verts φ n := fun o ho => mem_verts.2 (Or.inr ⟨o, ho, rfl⟩)
  rcases mem_graphClauses.1 hc with ⟨i, hi, rfl⟩ | ⟨o, ho, rfl | ⟨o', ho', -, -, rfl | rfl⟩⟩ <;>
    rcases mem_edge.1 hl with rfl | rfl
  · exact hvv i hi _
  · exact hvv i hi _
  · exact hcv o ho
  · exact hvv _ (hd o ho) _
  · exact hcv o ho
  · exact hcv o' ho'
  · exact hcv o ho
  · exact hvv _ (hd o' ho') _

theorem mem_vars_psi (hd : ∀ o ∈ occurrences φ, o.2.2.1 < n) {t : ℕ} (ht : 0 < t) {v : ℕ} :
    v ∈ (graphClauses φ n ++ leafClauses φ n t).vars ↔
      v ∈ verts φ n ∨ ∃ u ∈ verts φ n, ∃ q < t, v = lv u q := by
  rw [mem_vars_iff]
  constructor
  · rintro ⟨c, hc, l, hl, rfl⟩
    rcases List.mem_append.1 hc with hc | hc
    · exact Or.inl (graph_vars_mem hd hc hl)
    · obtain ⟨u, hu, q, hq, rfl⟩ := mem_leafClauses.1 hc
      rcases mem_edge.1 hl with rfl | rfl
      · exact Or.inl hu
      · exact Or.inr ⟨u, hu, q, hq, rfl⟩
  · rintro (hv | ⟨u, hu, q, hq, rfl⟩)
    · exact ⟨edge v (lv v 0), List.mem_append.2 (Or.inr (mem_leafClauses.2 ⟨v, hv, 0, ht, rfl⟩)),
        (v, true), mem_edge.2 (Or.inl rfl), rfl⟩
    · exact ⟨edge u (lv u q), List.mem_append.2 (Or.inr (mem_leafClauses.2 ⟨u, hu, q, hq, rfl⟩)),
        (lv u q, true), mem_edge.2 (Or.inr rfl), rfl⟩

theorem lv_not_mem_verts {u q : ℕ} : lv u q ∉ verts φ n := by
  intro h
  rcases mem_verts.1 h with ⟨i, -, b, h⟩ | ⟨o, -, h⟩
  · exact lv_ne_vv _ _ _ _ h
  · exact lv_ne_cv _ _ _ h

theorem eval_append (σ : ℕ → Bool) (a b : CNF ℕ) : (a ++ b).eval σ = (a.eval σ && b.eval σ) := by
  simp [CNF.eval, List.all_append]

/-- `Indep` of the false set of `g`, read on any assignment that extends `g`. -/
theorem graph_eval_iff (hd : ∀ o ∈ occurrences φ, o.2.2.1 < n) (σ : ℕ → Bool) :
    (graphClauses φ n).eval σ = true ↔ Indep φ n (falseSet (fun x : V0 φ n => σ x.1)) := by
  unfold Indep
  rw [CNF.eval_congr (τ := fun x => decide (x ∉ falseSet (fun x : V0 φ n => σ x.1)))]
  intro v hv
  obtain ⟨c, hc, l, hl, rfl⟩ := mem_vars_iff.1 hv
  have hm := List.mem_toFinset.2 (graph_vars_mem hd hc hl)
  have key : l.1 ∈ falseSet (fun x : V0 φ n => σ x.1) ↔ σ l.1 = false := by
    rw [mem_falseSet]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hm, h⟩⟩
  cases h : σ l.1 <;> simp [key, h]

theorem lv_div (u q : ℕ) : lv u q / 3 = Nat.pair u q := by
  unfold lv
  omega

/-- The leaf assignments allowed by `g`: the leaves of a vertex set to `false` are `true`. -/
theorem card_leaves (g : V0 φ n → Bool) (t : ℕ) :
    (Finset.univ.filter fun l : V0 φ n → Fin t → Bool =>
      ∀ x q, g x = false → l x q = true).card =
      2 ^ (t * (Finset.univ.filter fun x => g x = true).card) := by
  classical
  have h : (Finset.univ.filter fun l : V0 φ n → Fin t → Bool =>
      ∀ x q, g x = false → l x q = true) =
      Fintype.piFinset (fun x => if g x then Finset.univ else {fun _ => true}) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hl x
      cases hx : g x
      · simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_singleton]
        exact funext fun q => hl x q hx
      · simp
    · intro hl x q hx
      have := hl x
      simp only [hx, Bool.false_eq_true, ↓reduceIte, Finset.mem_singleton] at this
      rw [this]
  rw [h, Fintype.card_piFinset]
  have h2 : ∀ x : V0 φ n, (if g x then (Finset.univ : Finset (Fin t → Bool))
      else {fun _ => true}).card = if g x = true then 2 ^ t else 1 := by
    intro x
    cases g x <;> simp
  rw [Finset.prod_congr rfl fun x _ => h2 x, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const_one, mul_one, ← pow_mul]

/-- **The pendant count.** -/
theorem modelCount_psi (hd : ∀ o ∈ occurrences φ, o.2.2.1 < n) {t : ℕ} (ht : 0 < t) :
    (graphClauses φ n ++ leafClauses φ n t).modelCount =
      ∑ g : V0 φ n → Bool, if Indep φ n (falseSet g) then
        2 ^ (t * (Finset.univ.filter fun x => g x = true).card) else 0 := by
  classical
  let f : (ℕ → Bool) → (V0 φ n → Bool) × (V0 φ n → Fin t → Bool) :=
    fun σ => (fun x => σ x.1, fun x q => σ (lv x.1 q))
  let P : (V0 φ n → Bool) × (V0 φ n → Fin t → Bool) → Prop :=
    fun p => Indep φ n (falseSet p.1) ∧ ∀ x q, p.1 x = false → p.2 x q = true
  have hleaf : ∀ σ : ℕ → Bool, (leafClauses φ n t).eval σ = true →
      ∀ u ∈ verts φ n, ∀ q < t, σ u = false → σ (lv u q) = true := by
    intro σ h u hu q hq hσu
    simp only [CNF.eval, List.all_eq_true] at h
    have := h _ (mem_leafClauses.2 ⟨u, hu, q, hq, rfl⟩)
    rw [eval_edge, hσu, Bool.false_or] at this
    exact this
  rw [CNF.modelCount_eq_card_filter f P (fun σ τ _ _ => ?_) fun p => ?_]
  · rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hI : Indep φ n (falseSet g)
    · simp only [hI, true_and, ↓reduceIte]
      rw [← Finset.card_filter, card_leaves]
    · simp [hI]
  · constructor
    · intro h v hv
      rcases (mem_vars_psi hd ht).1 hv with hv | ⟨u, hu, q, hq, rfl⟩
      · exact congrFun (congrArg Prod.fst h) ⟨v, List.mem_toFinset.2 hv⟩
      · exact congrFun (congrFun (congrArg Prod.snd h) ⟨u, List.mem_toFinset.2 hu⟩) ⟨q, hq⟩
    · intro h
      refine Prod.ext (funext fun x => h _ ((mem_vars_psi hd ht).2
        (Or.inl (List.mem_toFinset.1 x.2)))) (funext fun x => funext fun q => h _
          ((mem_vars_psi hd ht).2 (Or.inr ⟨x.1, List.mem_toFinset.1 x.2, q.1, q.2, rfl⟩)))
  · obtain ⟨g, l⟩ := p
    constructor
    · rintro ⟨hI, hl⟩
      let σ : ℕ → Bool := fun y =>
        if h : y ∈ (verts φ n).toFinset then g ⟨y, h⟩ else
          if h' : (Nat.unpair (y / 3)).1 ∈ (verts φ n).toFinset ∧ (Nat.unpair (y / 3)).2 < t
          then l ⟨_, h'.1⟩ ⟨_, h'.2⟩ else false
      have hσv : ∀ x : V0 φ n, σ x.1 = g x := fun x => by
        simp only [σ]
        rw [dite_eq_left_of_eq_true (eq_true x.2)]
      have hσl : ∀ (x : V0 φ n) (q : Fin t), σ (lv x.1 q) = l x q := by
        intro x q
        have hn : lv x.1 q ∉ (verts φ n).toFinset := fun h =>
          lv_not_mem_verts (List.mem_toFinset.1 h)
        have hm : (Nat.unpair (lv x.1 q / 3)).1 ∈ (verts φ n).toFinset ∧
            (Nat.unpair (lv x.1 q / 3)).2 < t := by
          rw [lv_div, Nat.unpair_pair]
          exact ⟨x.2, q.2⟩
        simp only [σ]
        rw [dite_eq_right_of_eq_false (eq_false hn), dite_eq_left_of_eq_true (eq_true hm)]
        congr 1 <;> simp [lv_div]
      have hfg : falseSet (fun x : V0 φ n => σ x.1) = falseSet g := by
        congr 1
        exact funext hσv
      refine ⟨σ, ?_, Prod.ext (funext hσv) (funext fun x => funext fun q => hσl x q)⟩
      rw [eval_append, Bool.and_eq_true]
      refine ⟨(graph_eval_iff hd σ).2 (hfg ▸ hI), ?_⟩
      simp only [CNF.eval, List.all_eq_true]
      intro c hc
      obtain ⟨u, hu, q, hq, rfl⟩ := mem_leafClauses.1 hc
      rw [eval_edge]
      have hσu := hσv ⟨u, List.mem_toFinset.2 hu⟩
      have hσq := hσl ⟨u, List.mem_toFinset.2 hu⟩ ⟨q, hq⟩
      simp only at hσu hσq
      rw [hσu, hσq]
      cases hgu : g ⟨u, List.mem_toFinset.2 hu⟩
      · have := hl _ ⟨q, hq⟩ hgu
        simp only at this
        rw [this]
        rfl
      · rfl
    · rintro ⟨σ, hσ, he⟩
      simp only [f, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [eval_append, Bool.and_eq_true] at hσ
      refine ⟨(graph_eval_iff hd σ).1 hσ.1, fun x q hx => ?_⟩
      exact hleaf σ hσ.2 x.1 (List.mem_toFinset.1 x.2) q q.2 hx

end Latc.PaperD.Valiant
