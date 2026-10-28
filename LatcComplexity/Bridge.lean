import LatcFormal.Prop5Reduction
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Logics.Propositional.CNF.ModelCount
import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Tactic.PolyTime
import Complexity.Computability.Complexity.CookLevin.Counting

/-!
# Paper D feasibility: bridging the Proposition 5 reduction to Complexitylib

Proof of concept. Boolean attributes are numbered by `ℕ`; a set of clause constraints is a
Complexitylib `CNF ℕ` (a condition Aᵢ = v is the literal `(i, v)`); the table T₀ lists its
condition tuples as bit vectors indexed by the distinct attributes of the constraints.
-/

namespace Latc.PaperD

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Bridge from `Latc.Prop5` to Complexitylib's CNF -/

/-- A condition Aᵢ = v is the Complexitylib literal `(i, v)`. -/
def condToLiteral (a : Prop5.Cond ℕ) : Literal ℕ := (a.attr, a.val)

/-- A set of clause constraints as a Complexitylib CNF formula. -/
def toCNF (S : Prop5.ConSet ℕ) : CNF ℕ := S.map (List.map condToLiteral)

/-- Same satisfying states. -/
theorem holdsAll_eq_eval (S : Prop5.ConSet ℕ) (x : ℕ → Bool) :
    Prop5.holdsAll S x = (toCNF S).eval x := by
  simp [Prop5.holdsAll, Prop5.holdsClause, Prop5.Cond.holds, toCNF, CNF.eval, Clause.eval,
    Literal.eval, condToLiteral, List.all_map, List.any_map, Function.comp_def]

/-- Satisfiability in our model is satisfiability in Complexitylib's. -/
theorem satisfiable_decode_iff (S : Prop5.ConSet ℕ) :
    Prop5.Satisfiable (Prop5.decode S) ↔ (toCNF S).Satisfiable := by
  simp [Prop5.Satisfiable, CNF.Satisfiable, holdsAll_eq_eval]

/-! ### The decision problems, with Complexitylib encodings -/

/-- An instance: clause constraints over Boolean attributes and the condition tuples of T₀. -/
abbrev Inst := CNF ℕ × List (List Bool)

/-- Instances are encoded as a pair of the CNF encoding and a list of lists of bits. -/
abbrev encInst : Inst ↪ List Bool := encPair encCNF (encList (encList encBool))

/-- The condition tuple of a state, over the distinct attributes of the constraints. -/
def tuple (φ : CNF ℕ) (x : ℕ → Bool) : List Bool := φ.distinctVars.map x

/-- M(T₀) is non-empty: some valid state is not a condition tuple of T₀. -/
def MissingNonempty : Set Inst := {I | ∃ x : ℕ → Bool, I.1.eval x = true ∧ tuple I.1 x ∉ I.2}

/-- T₀ is complete: M(T₀) = ∅. -/
def Complete : Set Inst := MissingNonemptyᶜ

/-- The Proposition 5 reduction: a formula becomes its own clause constraints with T₀ = ∅. -/
def fromSAT (φ : CNF ℕ) : Inst := (φ, [])

theorem fromSAT_polyTime : ComputableInPolyTime fromSAT encCNF encInst := by
  unfold fromSAT
  polytime

theorem SAT_reduces : PolyTimeReducible encCNF encInst SAT MissingNonempty :=
  ⟨fromSAT, fromSAT_polyTime, fun φ => by
    simp [SAT, MissingNonempty, fromSAT, CNF.Satisfiable]⟩

/-- **NP-hardness of non-emptiness**, end to end from Cook–Levin. -/
theorem MissingNonempty_npHard : NPHard encInst MissingNonempty :=
  CookLevin.SAT_npHard.trans SAT_reduces

/-- **coNP-hardness of completeness**, end to end from Cook–Levin. -/
theorem Complete_coNPHard : coNPHard encInst Complete :=
  CookLevin.UNSAT_coNPComplete.2.trans (compl_SAT ▸ SAT_reduces.compl)

/-! ### Membership: the certificate check of Proposition 5 as a Complexitylib verifier -/

/-- The condition tuple of the state that a certificate describes, as in `SAT.assignment`. -/
def tupleOf (q : CNF ℕ × List Bool) : List Bool := q.1.distinctVars.map (SAT.assignment q.1 q.2)

@[fun_prop] theorem tupleOf_polyTime :
    ComputableInPolyTime tupleOf (encPair encCNF encBits) (encList encBool) := by
  have hv := SAT.computableInPolyTime_distinctVars.tidy
  have ha := SAT.computableInPolyTime_assignment.tidy
  refine .of_tidy ?_
  unfold tupleOf
  fun_prop

/-- The verifier: accept when the state described by the certificate satisfies every constraint
(the SAT verifier) and its condition tuple is not a row of T₀. -/
def verifier (p : Inst × List Bool) : Bool :=
  SAT.verifier (p.1.1, p.2) && !decide (tupleOf (p.1.1, p.2) ∈ p.1.2)

theorem verifier_polyTime : ComputableInPolyTime verifier (encPair encInst encBits) encBool := by
  have h1 := SAT.computableInPolyTime_verifier.tidy
  have h2 := tupleOf_polyTime.tidy
  refine .of_tidy ?_
  unfold verifier
  fun_prop

/-- The certificate assignment agrees with x on the variables of φ. -/
lemma assignment_pad (φ : CNF ℕ) (x : ℕ → Bool) (k : ℕ) {v : ℕ} (hv : v ∈ φ.vars) :
    SAT.assignment φ (φ.vars.map x ++ List.replicate k false) v = x v := by
  have hlt : φ.vars.idxOf v < φ.vars.length := List.idxOf_lt_length_iff.2 hv
  have hlt' : φ.vars.idxOf v < (φ.vars.map x).length := by simpa using hlt
  rw [SAT.assignment, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt',
    List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
  rfl

lemma length_encCNF_le (I : Inst) : (encCNF I.1).length ≤ (encInst I).length := by
  rw [encPair_apply, List.length_append, length_frame]
  omega

theorem isVerifier : IsVerifier encInst Polynomial.X verifier MissingNonempty := by
  refine IsVerifier.of_padding (fun I w _ h => ?_) fun I ⟨x, hx, hT⟩ => ?_
  · simp only [verifier, SAT.verifier, tupleOf, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨_, h.1, of_decide_eq_false h.2⟩
  · refine ⟨I.1.vars.map x, ?_, fun k => ?_⟩
    · simpa using (SAT.length_vars_le I.1).trans (length_encCNF_le I)
    have hagree : ∀ v ∈ I.1.vars, SAT.assignment I.1 (I.1.vars.map x ++ List.replicate k false) v
        = x v := fun v hv => assignment_pad I.1 x k hv
    have htuple : I.1.distinctVars.map
        (SAT.assignment I.1 (I.1.vars.map x ++ List.replicate k false)) = tuple I.1 x :=
      List.map_congr_left fun v hv => hagree v (CNF.mem_distinctVars.1 hv)
    simp only [verifier, SAT.verifier, tupleOf, htuple, (CNF.eval_congr hagree).trans hx, Bool.true_and,
      Bool.not_eq_true', decide_eq_false_iff_not]
    exact hT

theorem MissingNonempty_mem_NP : MissingNonempty ∈ NP encInst :=
  ⟨Polynomial.X, verifier, verifier_polyTime, isVerifier⟩

/-- **Proposition 5 (Boolean domains), NP part, end to end:** deciding M(T₀) ≠ ∅ for clause
constraints is NP-complete. -/
theorem MissingNonempty_npComplete : NPComplete encInst MissingNonempty :=
  ⟨MissingNonempty_mem_NP, MissingNonempty_npHard⟩

/-- **Proposition 5 (Boolean domains), coNP part, end to end:** deciding completeness is
coNP-complete. -/
theorem Complete_coNPComplete : coNPComplete encInst Complete :=
  MissingNonempty_npComplete.compl

/-! ### Counting: |M(T₀)| over the states of the attributes that occur -/

/-- |M(T₀)|: the states of the occurring attributes that satisfy every constraint and whose
condition tuple is not a row of T₀ (the convention of `CNF.modelCount`). -/
noncomputable def countMissing (I : Inst) : ℕ :=
  (Finset.univ.filter fun τ : I.1.vars.toFinset → Bool =>
    I.1.eval (I.1.extendAssignment τ) = true ∧ tuple I.1 (I.1.extendAssignment τ) ∉ I.2).card

/-- With T₀ = ∅, |M(T₀)| = |𝒱| is the number of satisfying assignments. -/
theorem countMissing_fromSAT (φ : CNF ℕ) : SharpSAT φ = countMissing (fromSAT φ) := by
  simp only [SharpSAT, CNF.modelCount, countMissing, fromSAT, List.not_mem_nil, not_false_eq_true,
    and_true]
  congr

/-- **#P-hardness of counting |M(T₀)|** (and |𝒱|), end to end from the parsimonious
Cook–Levin theorem. -/
theorem countMissing_sharpPHard : SharpPHard encInst countMissing :=
  CookLevin.SharpSAT_sharpPHard.trans ⟨fromSAT, fromSAT_polyTime, countMissing_fromSAT⟩

end Latc.PaperD
