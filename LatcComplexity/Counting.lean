import LatcComplexity.Bridge

/-!
# Counting |M(T₀)| is #P-complete (Boolean domains)

`countMissing (φ, T)` (`LatcComplexity/Bridge.lean`) is |M(T₀)|: the states of the attributes of
the clause constraints `φ` that satisfy `φ` and whose condition tuple is not a row of `T`. It is
`#P`-hard by the parsimonious Cook–Levin theorem (`countMissing_sharpPHard`). This file shows that it
belongs to `#P`, by a parsimonious reduction to `#SAT`: each row `r` of T₀ of the right length
becomes the clause "the condition tuple differs from `r` somewhere" (`rowClause`), and the
satisfying assignments of the resulting formula are the states of M(T₀).

* `countMissing_eq_sharpSAT`: |M(T₀)| = #SAT(`toSharpSAT (φ, T)`).
* `countMissing_mem_SharpP`: counting |M(T₀)| is in `#P`.
* `countMissing_sharpPComplete`: counting |M(T₀)| is `#P`-complete.
-/

namespace Latc.PaperD

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### The reduction -/

/-- The clause stating that the condition tuple differs from the row `r` at some attribute. -/
def rowClause (φ : CNF ℕ) (r : List Bool) : Clause ℕ :=
  (φ.distinctVars.zip r).map fun p => (p.1, !p.2)

/-- The constraints of `φ` together with one `rowClause` per row of T₀ of the right length; rows of
another length are condition tuples of no state and are dropped. -/
def toSharpSAT (I : Inst) : CNF ℕ :=
  I.1 ++ (I.2.filter fun r => r.length == I.1.numVars).map (rowClause I.1)

theorem rowClause_polyTime :
    ComputableInPolyTime (fun p : CNF ℕ × List Bool => rowClause p.1 p.2)
      (encPair encCNF (encList encBool)) (encList (encPair encNat encBool)) := by
  have hv := SAT.computableInPolyTime_distinctVars.tidy
  refine .of_tidy ?_
  unfold rowClause
  fun_prop

theorem toSharpSAT_polyTime : ComputableInPolyTime toSharpSAT encInst encCNF := by
  have hv := SAT.computableInPolyTime_numVars.tidy
  have hr := rowClause_polyTime.tidy
  refine .of_tidy ?_
  unfold toSharpSAT
  fun_prop

/-! ### Correctness -/

/-- The row clauses add no variable. -/
theorem mem_vars_toSharpSAT (I : Inst) (v : ℕ) : v ∈ (toSharpSAT I).vars ↔ v ∈ I.1.vars := by
  constructor
  · intro hv
    simp only [toSharpSAT, CNF.vars, List.flatten_append, List.map_append, List.mem_append] at hv
    rcases hv with hv | hv
    · exact hv
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hv
      obtain ⟨c, hc, hlc⟩ := List.mem_flatten.1 hl
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hlc
      exact CNF.mem_distinctVars.1 (List.of_mem_zip hp).1
  · intro hv
    simp only [toSharpSAT, CNF.vars, List.flatten_append, List.map_append, List.mem_append]
    exact Or.inl hv

/-- On lists of equal length, a clause of literals `(v, !b)` holds exactly when the values differ
from the bits somewhere. -/
lemma any_zip_iff (σ : ℕ → Bool) : ∀ (l : List ℕ) (r : List Bool), l.length = r.length →
    (((l.zip r).map fun p => ((p.1, !p.2) : Literal ℕ)).any (Literal.eval σ) = true ↔
      l.map σ ≠ r)
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | v :: l, b :: r, h => by
    have ih := any_zip_iff σ l r (by simpa using h)
    simp only [List.zip_cons_cons, List.map_cons, List.any_cons, Bool.or_eq_true, ih,
      Literal.eval, ne_eq, List.cons.injEq, not_and_or]
    cases σ v <;> cases b <;> simp

lemma length_tuple (φ : CNF ℕ) (σ : ℕ → Bool) : (tuple φ σ).length = φ.numVars := by
  simp [tuple, CNF.length_distinctVars]

/-- The formula holds exactly when the constraints hold and the condition tuple is not a row of
T₀. -/
theorem eval_toSharpSAT (I : Inst) (σ : ℕ → Bool) :
    (toSharpSAT I).eval σ = true ↔ I.1.eval σ = true ∧ tuple I.1 σ ∉ I.2 := by
  have hrow : ∀ r ∈ I.2, r.length = I.1.numVars →
      (Clause.eval σ (rowClause I.1 r) = true ↔ tuple I.1 σ ≠ r) := fun r _ hr =>
    any_zip_iff σ _ r (by rw [CNF.length_distinctVars, hr])
  simp only [toSharpSAT, CNF.eval, List.all_append, Bool.and_eq_true, List.all_map,
    List.all_filter, List.all_eq_true, Function.comp_apply]
  refine and_congr Iff.rfl ⟨fun h hmem => ?_, fun h r hr => ?_⟩
  · have := h _ hmem
    rw [length_tuple, beq_self_eq_true, Bool.not_true, Bool.false_or] at this
    exact (hrow _ hmem (length_tuple _ _)).1 this rfl
  · by_cases hlen : r.length = I.1.numVars
    · rw [show (r.length == I.1.numVars) = true from beq_iff_eq.2 hlen, Bool.not_true,
        Bool.false_or]
      exact (hrow r hr hlen).2 fun he => h (he ▸ hr)
    · simp [hlen]

/-- **The reduction is parsimonious:** |M(T₀)| is the number of satisfying assignments of
`toSharpSAT (φ, T)`. -/
theorem countMissing_eq_sharpSAT (I : Inst) : countMissing I = SharpSAT (toSharpSAT I) := by
  symm
  unfold SharpSAT countMissing
  refine Eq.trans (CNF.modelCount_eq_card_filter (φ := toSharpSAT I)
    (fun σ (v : I.1.vars.toFinset) => σ v)
    (fun τ => I.1.eval (I.1.extendAssignment τ) = true ∧
      tuple I.1 (I.1.extendAssignment τ) ∉ I.2) (fun σ τ _ _ => ⟨fun h v hv => ?_,
      fun h => funext fun ⟨v, hv⟩ => ?_⟩) fun τ => ⟨fun hτ => ?_, ?_⟩) ?_
  · exact congrFun h ⟨v, List.mem_toFinset.2 ((mem_vars_toSharpSAT I v).1 hv)⟩
  · exact h v ((mem_vars_toSharpSAT I v).2 (List.mem_toFinset.1 hv))
  · refine ⟨I.1.extendAssignment τ, (eval_toSharpSAT I _).2 hτ, funext fun ⟨v, hv⟩ => ?_⟩
    exact CNF.extendAssignment_of_mem τ (List.mem_toFinset.1 hv)
  · rintro ⟨σ, hσ, rfl⟩
    have htuple : tuple I.1 (I.1.extendAssignment fun v => σ v) = tuple I.1 σ :=
      List.map_congr_left fun v hv =>
        CNF.extendAssignment_of_mem _ (CNF.mem_distinctVars.1 hv)
    rw [htuple, CNF.eval_extendAssignment_restrict]
    exact (eval_toSharpSAT I σ).1 hσ
  · rfl

/-! ### #P-completeness -/

/-- Counting |M(T₀)| reduces parsimoniously to `#SAT`. -/
theorem countMissing_reduces_sharpSAT :
    ParsimoniousReducible encInst encCNF countMissing SharpSAT :=
  ⟨toSharpSAT, toSharpSAT_polyTime, countMissing_eq_sharpSAT⟩

/-- **Counting |M(T₀)| is in #P.** -/
theorem countMissing_mem_SharpP : countMissing ∈ SharpP encInst :=
  countMissing_reduces_sharpSAT.mem_SharpP SharpSAT.mem_SharpP

/-- **Proposition 5, counting part (Boolean domains):** counting |M(T₀)| is `#P`-complete under
parsimonious reductions; with T₀ = ∅ this is |𝒱|. -/
theorem countMissing_sharpPComplete : SharpPComplete encInst countMissing :=
  ⟨countMissing_mem_SharpP, countMissing_sharpPHard⟩

end Latc.PaperD
