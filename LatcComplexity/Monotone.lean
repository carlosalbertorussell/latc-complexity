import LatcComplexity.CountingGeneral
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime

/-!
# The monotone two-literal case of Proposition 5's counting statement

Paper A states that computing |𝒱| stays `#P`-complete when every constraint is a clause of two
conditions Aᵢ = 1, Aⱼ = 1 over domains {0, 1}, citing Valiant (1979) for `#Monotone-2SAT`.
Deciding such instances is trivial (the all-ones state is valid), so no parsimonious reduction
from `#SAT` exists unless P = NP; hardness needs a weaker reduction. This file formalises the part
of the argument that belongs to Paper A and states Valiant's theorem as an explicit hypothesis.

* `OneCallReducible`: a one-call counting reduction in Complexitylib's model; a polynomial-time map
  `r` and a polynomial-time post-processing `post` with `f a = post a (g (r a))`. Parsimonious
  reductions are one-call reductions (`ParsimoniousReducible.oneCallReducible`), so `#P`-hardness
  implies one-call `#P`-hardness (`SharpPHard.oneCallSharpPHard`).
* `SharpMonotone2SAT`: `#SAT` on monotone two-literal formulas, count zero on other syntax (the
  convention of Complexitylib's `SharpThreeSAT`).
* `countValidMonotone2`: |𝒱| = |M(∅)| of latc-check's model on instances with domains {0, 1},
  clauses of two conditions Aᵢ = 1, Aⱼ = 1 and T₀ = ∅; count zero on other syntax.
* `sharpMonotone2SAT_reduces`: `#Monotone-2SAT` reduces parsimoniously to `countValidMonotone2`.
* `countValidMonotone2_mem_SharpP`: membership in `#P`.
* `countValidMonotone2_oneCallSharpPComplete`: **if** `#Monotone-2SAT` is one-call `#P`-hard (the
  hypothesis `hValiant`), then `countValidMonotone2` is one-call `#P`-complete.

The hypothesis is not proved in Complexitylib's model. Valiant proved `#Monotone-2SAT` `#P`-complete
under polynomial-time Turing reductions; its one-call form is machine-checked in another model as
`sharpMonotoneTwoSat_sharpP_oneCallComplete` of Senellart's descriptive-complexity library.
-/

namespace Latc.PaperD.General

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### One-call counting reductions -/

section OneCall

variable {α β γ : Type}

/-- `f` reduces to `g` with one oracle call: `f a = post a (g (r a))` for polynomial-time `r` and
`post`, the oracle answer read in binary. -/
def OneCallReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (f : α → ℕ) (g : β → ℕ) :
    Prop :=
  ∃ (r : α → β) (post : α → ℕ → ℕ), ComputableInPolyTime r encA encB ∧
    ComputableInPolyTime (fun p : α × ℕ => post p.1 p.2) (encPair encA encNat) encNat ∧
      ∀ a, f a = post a (g (r a))

/-- Every function in `#P`, with any encoding of its instances, reduces to `g` with one call. -/
def OneCallSharpPHard (encB : β ↪ List Bool) (g : β → ℕ) : Prop :=
  ∀ ⦃α : Type⦄ (enc : α ↪ List Bool) (f : α → ℕ), f ∈ SharpP enc → OneCallReducible enc encB f g

/-- `g` is in `#P` and one-call `#P`-hard. -/
def OneCallSharpPComplete (encB : β ↪ List Bool) (g : β → ℕ) : Prop :=
  g ∈ SharpP encB ∧ OneCallSharpPHard encB g

/-- A parsimonious reduction is a one-call reduction whose post-processing returns the answer. -/
theorem ParsimoniousReducible.oneCallReducible {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {f : α → ℕ} {g : β → ℕ} (h : ParsimoniousReducible encA encB f g) :
    OneCallReducible encA encB f g := by
  obtain ⟨r, hr, hfg⟩ := h
  exact ⟨r, fun _ n => n, hr, by fun_prop, hfg⟩

/-- `#P`-hardness under parsimonious reductions implies one-call `#P`-hardness. -/
theorem SharpPHard.oneCallSharpPHard {encB : β ↪ List Bool} {g : β → ℕ}
    (h : SharpPHard encB g) : OneCallSharpPHard encB g := fun _ enc f hf =>
  ParsimoniousReducible.oneCallReducible (h enc f hf)

/-- A one-call reduction followed by a parsimonious one is a one-call reduction. -/
theorem OneCallReducible.trans_parsimonious {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : α → ℕ} {g : β → ℕ} {h : γ → ℕ}
    (hfg : OneCallReducible encA encB f g) (hgh : ParsimoniousReducible encB encC g h) :
    OneCallReducible encA encC f h := by
  obtain ⟨r, post, hr, hpost, hf⟩ := hfg
  obtain ⟨s, hs, hg⟩ := hgh
  exact ⟨s ∘ r, post, hs.comp hr, hpost, fun a => (hf a).trans (by rw [hg (r a)]; rfl)⟩

/-- One-call hardness transfers along a parsimonious reduction. -/
theorem OneCallSharpPHard.trans_parsimonious {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {g : β → ℕ} {h : γ → ℕ} (hg : OneCallSharpPHard encB g)
    (hgh : ParsimoniousReducible encB encC g h) : OneCallSharpPHard encC h := fun _ enc f hf =>
  OneCallReducible.trans_parsimonious (hg enc f hf) hgh

end OneCall

/-- Sanity check: `#SAT` is one-call `#P`-hard, so the notion is not vacuous. -/
theorem sharpSAT_oneCallSharpPHard : OneCallSharpPHard encCNF SharpSAT :=
  SharpPHard.oneCallSharpPHard CookLevin.SharpSAT_sharpPHard

/-! ### The restricted problems -/

/-- Every clause has two literals, both positive: `xᵢ ∨ xⱼ`. -/
def monotone2B (φ : CNF ℕ) : Bool := φ.all fun c => c.length == 2 && c.all (·.2)

/-- `#Monotone-2SAT`: the model count of a monotone two-literal formula; zero on other syntax. -/
def SharpMonotone2SAT (φ : CNF ℕ) : ℕ := if monotone2B φ then SharpSAT φ else 0

/-- Domains {0, 1}, clauses of two conditions with value 1, and T₀ = ∅. -/
def pos2B (I : Inst) : Bool :=
  I.1.all (· == 2) && I.2.1.all (fun c => c.length == 2 && c.all (·.2 == 1)) && I.2.2.isEmpty

/-- |𝒱| for clause constraints of two conditions Aᵢ = 1, Aⱼ = 1 over domains {0, 1}, in
latc-check's model (`missingCount` with T₀ = ∅); zero on other syntax. -/
noncomputable def countValidMonotone2 (I : Inst) : ℕ := if pos2B I then missingCount I else 0

/-- On its instances `countValidMonotone2` is |𝒱| = |`Latc.validSpace`| of latc-check's model. -/
theorem countValidMonotone2_eq_card_validSpace (I : Inst) (h : pos2B I = true) :
    countValidMonotone2 I = (Latc.validSpace I.con).card := by
  have hT : I.2.2 = [] := by
    simp only [pos2B, Bool.and_eq_true, List.isEmpty_iff] at h
    exact h.2
  have htab : I.table = ∅ := by
    ext x
    simp [Inst.table, hT]
  simp only [countValidMonotone2, h, ↓reduceIte, missingCount, htab, Latc.missing,
    Finset.sdiff_empty]

/-! ### The reduction -/

theorem pos2B_polyTime : ComputableInPolyTime pos2B encInst encBool := by
  refine .of_tidy ?_
  unfold pos2B
  fun_prop

theorem monotone2B_polyTime : ComputableInPolyTime monotone2B encCNF encBool := by
  refine .of_tidy ?_
  unfold monotone2B
  fun_prop

/-- A fixed instance with an empty clause: no state is valid, and it is not of the restricted
shape. -/
def emptyClauseInst : Inst := ([], ([[]], []))

/-- The reduction: monotone two-literal formulas go through `fromSAT`; other syntax goes to an
instance counted zero. -/
def fromMonotone2 (φ : CNF ℕ) : Inst := if monotone2B φ then fromSAT φ else emptyClauseInst

theorem fromMonotone2_polyTime : ComputableInPolyTime fromMonotone2 encCNF encInst := by
  have hm := monotone2B_polyTime.tidy
  have hf := fromSAT_polyTime.tidy
  refine .of_tidy ?_
  unfold fromMonotone2
  fun_prop

/-- `fromSAT` keeps a monotone two-literal formula of that shape. -/
theorem pos2B_fromSAT (φ : CNF ℕ) (h : monotone2B φ = true) : pos2B (fromSAT φ) = true := by
  simp only [monotone2B, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  unfold pos2B fromSAT
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_nil, and_true]
  refine ⟨fun x hx => List.eq_of_mem_replicate hx, fun c' hc' => ?_⟩
  obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 hc'
  simp only [CNF.denseRelabel, CNF.relabel] at hc₁
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc₁
  refine ⟨by simp [Clause.relabel, (h c hc).1], fun a ha => ?_⟩
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 ha
  obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
  simp [toCond, (h c hc).2 l₀ hl₀]

theorem pos2B_emptyClauseInst : pos2B emptyClauseInst = false := by decide

/-- **The reduction is parsimonious.** -/
theorem sharpMonotone2SAT_eq (φ : CNF ℕ) :
    SharpMonotone2SAT φ = countValidMonotone2 (fromMonotone2 φ) := by
  unfold SharpMonotone2SAT countValidMonotone2 fromMonotone2
  cases h : monotone2B φ
  · simp [pos2B_emptyClauseInst]
  · simp only [↓reduceIte, pos2B_fromSAT φ h]
    exact sharpSAT_eq_missingCount φ

theorem sharpMonotone2SAT_reduces :
    ParsimoniousReducible encCNF encInst SharpMonotone2SAT countValidMonotone2 :=
  ⟨fromMonotone2, fromMonotone2_polyTime, sharpMonotone2SAT_eq⟩

/-! ### Membership and conditional completeness -/

/-- **Counting |𝒱| for monotone two-condition clauses is in #P.** -/
theorem countValidMonotone2_mem_SharpP : countValidMonotone2 ∈ SharpP encInst := by
  have h := SharpP.ite_mem pos2B_polyTime missingCount_mem_SharpP (SharpP.zero_mem (enc := encInst))
  convert h using 1
  funext I
  rfl

/-- **Proposition 5, monotone two-literal case, conditional on Valiant's theorem:** if
`#Monotone-2SAT` is one-call `#P`-hard (`hValiant`), then counting |𝒱| for clauses of two
conditions Aᵢ = 1, Aⱼ = 1 over domains {0, 1} is one-call `#P`-complete. -/
theorem countValidMonotone2_oneCallSharpPComplete
    (hValiant : OneCallSharpPHard encCNF SharpMonotone2SAT) :
    OneCallSharpPComplete encInst countValidMonotone2 :=
  ⟨countValidMonotone2_mem_SharpP, hValiant.trans_parsimonious sharpMonotone2SAT_reduces⟩

end Latc.PaperD.General
