import LatcComplexity.Bridge
import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import Complexity.Logics.Propositional.CNF.ModelCount.DenseRelabel
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Proposition 5 over general finite domains, in Complexitylib's model

An instance lists the declared domain sizes `d = [|D₀|, …, |Dₙ₋₁|]` (attribute `i` takes the values
`0, …, dᵢ - 1`), a set of clause constraints (a clause is a list of conditions `(i, v)`, read
Aᵢ = v), and the condition tuples of T₀ (lists of values). Numbers are binary, except the attribute
index `i` of a condition, which is unary: it names a position among the declared attributes, and
Complexitylib reads list positions in unary. A state is a list `s` with
`s.length = n` and `sᵢ < dᵢ`; it satisfies `(i, v)` when `sᵢ = v`, so a condition on an attribute
outside `0, …, n - 1` never holds.

* `MissingNonempty_npComplete`: deciding M(T₀) ≠ ∅ is NP-complete.
* `Complete_coNPComplete`: deciding completeness (M(T₀) = ∅) is coNP-complete.

Membership uses the missing state itself as the witness (`mem_NP_of_witness`); its encoding is no
longer than the encoded domain sizes. Hardness reduces SAT: the variables are renumbered densely
(`CNF.denseRelabel`) and become attributes with domain {0, 1}.
-/

namespace Latc.PaperD.General

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Instances and their semantics -/

/-- A condition Aᵢ = v, as the pair `(i, v)`. -/
abbrev Cond := ℕ × ℕ

/-- An instance: domain sizes, clause constraints, and the condition tuples of T₀. -/
abbrev Inst := List ℕ × (List (List Cond) × List (List ℕ))

/-- Instances: binary domain sizes, values and rows; unary attribute indices. -/
abbrev encInst : Inst ↪ List Bool :=
  encPair (encList encNat) (encPair (encList (encList (encPair encUnary encNat)))
    (encList (encList encNat)))

/-- `s` is a state of the declared domains `d`: one value per attribute, inside its domain. -/
def InDomains (d s : List ℕ) : Prop := List.Forall₂ (· < ·) s d

/-- The state `s` satisfies the condition Aᵢ = v. -/
def CondHolds (s : List ℕ) (a : Cond) : Prop := s[a.1]? = some a.2

/-- The state `s` satisfies every clause constraint of `S`. -/
def Valid (S : List (List Cond)) (s : List ℕ) : Prop := ∀ c ∈ S, ∃ a ∈ c, CondHolds s a

/-- M(T₀) is non-empty: some valid state of the declared domains is not a condition tuple
of T₀. -/
def MissingNonempty : Set Inst :=
  {I | ∃ s, InDomains I.1 s ∧ Valid I.2.1 s ∧ s ∉ I.2.2}

/-- T₀ is complete: M(T₀) = ∅. -/
def Complete : Set Inst := MissingNonemptyᶜ

/-! ### The certificate check -/

/-- Boolean test of `InDomains`. -/
def inDomainsB (d s : List ℕ) : Bool :=
  s.length == d.length && (s.zip d).all fun p => decide (p.1 < p.2)

/-- Boolean test of `CondHolds`: an index out of range reads `v + 1 ≠ v`. -/
def condHoldsB (s : List ℕ) (a : Cond) : Bool := s[a.1]?.getD (a.2 + 1) == a.2

/-- The check of a candidate missing state `s` against an instance. -/
def check (p : Inst × List ℕ) : Bool :=
  inDomainsB p.1.1 p.2 && p.1.2.1.all (fun c => c.any (condHoldsB p.2)) &&
    !decide (p.2 ∈ p.1.2.2)

theorem inDomainsB_iff (d s : List ℕ) : inDomainsB d s = true ↔ InDomains d s := by
  simp [inDomainsB, InDomains, List.forall₂_iff_zip]

theorem condHoldsB_iff (s : List ℕ) (a : Cond) : condHoldsB s a = true ↔ CondHolds s a := by
  rcases h : s[a.1]? with _ | x <;> simp [condHoldsB, CondHolds, h]

theorem check_iff (I : Inst) (s : List ℕ) :
    check (I, s) = true ↔ InDomains I.1 s ∧ Valid I.2.1 s ∧ s ∉ I.2.2 := by
  simp [check, inDomainsB_iff, Valid, condHoldsB_iff, and_assoc]

/-- Reading a value at a unary position is polynomial-time. -/
theorem lookup_polyTime : ComputableTidilyInPolyTime (fun p : List ℕ × Cond => p.1[p.2.1]?)
    (encPair (encList encNat) (encPair encUnary encNat)) (encOption encNat) := by
  apply ComputableTidilyInPolyTime.getElem? (encA := encNat) (encL := encList encNat)
  · fun_prop
  · fun_prop

theorem condHoldsB_polyTime : ComputableInPolyTime (fun p : List ℕ × Cond => condHoldsB p.1 p.2)
    (encPair (encList encNat) (encPair encUnary encNat)) encBool := by
  have hd : ComputableTidilyInPolyTime (fun p : List ℕ × Cond => p.1[p.2.1]?.getD (p.2.2 + 1))
      (encPair (encList encNat) (encPair encUnary encNat)) encNat :=
    ComputableTidilyInPolyTime.optionGetDWithInput lookup_polyTime (by fun_prop)
  refine .of_tidy ?_
  unfold condHoldsB
  fun_prop

theorem check_polyTime : ComputableInPolyTime check (encPair encInst (encList encNat)) encBool := by
  have h := condHoldsB_polyTime.tidy
  refine .of_tidy ?_
  unfold check inDomainsB
  fun_prop

/-- A state of the declared domains is encoded in no more bits than the domain sizes. -/
theorem length_encList_le_of_inDomains {d s : List ℕ} (h : InDomains d s) :
    (encList encNat s).length ≤ (encList encNat d).length := by
  induction h with
  | nil => simp
  | cons hab _ ih =>
    simp only [encList_cons, List.length_append, length_frame]
    have := ComputableTidilyInO.length_encNat_mono hab.le
    omega

theorem length_domains_le (I : Inst) : (encList encNat I.1).length ≤ (encInst I).length := by
  rw [encPair_apply, List.length_append, length_frame]
  omega

/-- **Membership in NP.** -/
theorem MissingNonempty_mem_NP : MissingNonempty ∈ NP encInst := by
  have h := mem_NP_of_witness (p := Polynomial.X) (Decoder.list Decoder.nat) check_polyTime
    (R := fun I s => InDomains I.1 s ∧ Valid I.2.1 s ∧ s ∉ I.2.2) (fun I s => check_iff I s)
    (fun I s hs => ⟨s, hs, by
      simpa using (length_encList_le_of_inDomains hs.1).trans (length_domains_le I)⟩)
  exact h

/-! ### Hardness: SAT with dense variables, over domains {0, 1} -/

/-- A literal (i, b) becomes the condition Aᵢ = 1 if b, Aᵢ = 0 otherwise. -/
def toCond (l : Literal ℕ) : Cond := (l.1, if l.2 then 1 else 0)

/-- The reduction: renumber the variables densely and give each attribute the domain {0, 1};
T₀ = ∅. -/
def fromSAT (φ : CNF ℕ) : Inst :=
  (List.replicate φ.numVars 2, (φ.denseRelabel.map (List.map toCond), []))

theorem fromSAT_polyTime : ComputableInPolyTime fromSAT encCNF encInst := by
  have h1 := (CNF.computableInPolyTime_denseRelabel_unary encNat).tidy
  have h2 := SAT.computableInPolyTime_numVars.tidy
  refine .of_tidy ?_
  unfold fromSAT toCond
  fun_prop

/-- Satisfiability of a formula whose variables are below `n` is non-emptiness of M(∅) for its
conditions over `n` attributes with domain {0, 1}. -/
theorem satisfiable_iff (ψ : CNF ℕ) (n : ℕ) (hψ : ∀ v ∈ ψ.vars, v < n) :
    ψ.Satisfiable ↔ ∃ s, InDomains (List.replicate n 2) s ∧
      Valid (ψ.map (List.map toCond)) s := by
  constructor
  · rintro ⟨σ, hσ⟩
    let f : ℕ → ℕ := fun i => if σ i then 1 else 0
    refine ⟨(List.range n).map f, ?_, ?_⟩
    · refine List.forall₂_iff_zip.2 ⟨by simp, fun {a b} hab => ?_⟩
      obtain ⟨ha, hb⟩ := List.of_mem_zip hab
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
      rw [List.eq_of_mem_replicate hb]
      dsimp only [f]
      split <;> omega
    · intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      have hev : Clause.eval σ c' = true := by
        simp only [CNF.eval, List.all_eq_true] at hσ
        exact hσ c' hc'
      obtain ⟨l, hl, hlt⟩ := List.any_eq_true.1 hev
      have hlv : l.1 < n := hψ l.1 (List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨c', hc', hl⟩, rfl⟩)
      refine ⟨toCond l, List.mem_map.2 ⟨l, hl, rfl⟩, ?_⟩
      have hσl : σ l.1 = l.2 := by simpa [Literal.eval] using hlt
      simp [CondHolds, toCond, hlv, f, hσl]
  · rintro ⟨s, -, hs⟩
    refine ⟨fun i => s.getD i 0 == 1, ?_⟩
    simp only [CNF.eval, List.all_eq_true]
    intro c hc
    obtain ⟨a, ha, hholds⟩ := hs _ (List.mem_map.2 ⟨c, hc, rfl⟩)
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 ha
    refine List.any_eq_true.2 ⟨l, hl, ?_⟩
    have hget : s.getD l.1 0 = if l.2 then 1 else 0 := by
      simp only [CondHolds, toCond] at hholds
      simp [List.getD_eq_getElem?_getD, hholds]
    cases hb : l.2 <;> simp_all [Literal.eval]

theorem SAT_reduces : PolyTimeReducible encCNF encInst SAT MissingNonempty :=
  ⟨fromSAT, fromSAT_polyTime, fun φ => by
    rw [mem_SAT, ← CNF.satisfiable_denseRelabel,
      satisfiable_iff _ φ.numVars fun v hv => CNF.mem_vars_denseRelabel_lt φ hv]
    simp [MissingNonempty, fromSAT]⟩

theorem MissingNonempty_npHard : NPHard encInst MissingNonempty :=
  CookLevin.SAT_npHard.trans SAT_reduces

/-- **Proposition 5, NP part, general finite domains:** deciding M(T₀) ≠ ∅ for clause
constraints is NP-complete. -/
theorem MissingNonempty_npComplete : NPComplete encInst MissingNonempty :=
  ⟨MissingNonempty_mem_NP, MissingNonempty_npHard⟩

/-- **Proposition 5, coNP part, general finite domains:** deciding completeness is
coNP-complete. -/
theorem Complete_coNPComplete : coNPComplete encInst Complete :=
  MissingNonempty_npComplete.compl

end Latc.PaperD.General
