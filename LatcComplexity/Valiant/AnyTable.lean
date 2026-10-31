import LatcComplexity.Valiant.OneCall

/-!
# Missing combinations of monotone-shaped tables, any T₀

`countValidMonotone2` counts |𝒱| = |M(∅)| and requires T₀ = ∅. This file drops that requirement:
`countMissingMonotone2` counts |M(T₀)| for any table T₀, on instances with domains {0, 1} and
clauses of two conditions Aᵢ = 1, Aⱼ = 1 (`pos2AnyB`), zero on other syntax.

* `countMissingMonotone2_mem_SharpP(_bin)`: membership in `#P`, via `SharpP.ite_mem`.
* `sharpMonotone2SAT_reduces_countMissing`: the reduction `fromMonotone2` of `Monotone.lean` is
  also parsimonious to `countMissingMonotone2`, since it produces instances with T₀ = ∅ or
  instances that are of neither shape (`countMissingMonotone2_fromMonotone2`).
* `countMissingMonotone2_sharpPComplete_oneCall(_unary)`: one-call `#P`-completeness, from
  Valiant's theorem `sharpMonotone2SAT_oneCallSharpPHard`.
* `countMissingMonotone2_eq_card_missing`: on its instances `countMissingMonotone2` is
  `(Latc.missing I.con I.table).card` of latc-check's model.
-/

namespace Latc.PaperD.Valiant

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM Latc.PaperD.General

/-- Domains {0, 1} and clauses of two conditions with value 1; any table T₀. -/
def pos2AnyB (I : General.Inst) : Bool :=
  I.1.all (· == 2) && I.2.1.all (fun c => c.length == 2 && c.all (·.2 == 1))

/-- |M(T₀)| for clause constraints of two conditions Aᵢ = 1, Aⱼ = 1 over domains {0, 1}, any
table T₀, in latc-check's model; zero on other syntax. -/
noncomputable def countMissingMonotone2 (I : General.Inst) : ℕ :=
  if pos2AnyB I then missingCount I else 0

/-- On its instances `countMissingMonotone2` is latc-check's `(missing I.con I.table).card`. -/
theorem countMissingMonotone2_eq_card_missing (I : General.Inst) (h : pos2AnyB I = true) :
    countMissingMonotone2 I = (Latc.missing I.con I.table).card := by
  simp only [countMissingMonotone2, h, ↓reduceIte, missingCount]

/-- `pos2B` is `pos2AnyB` together with T₀ = ∅. -/
theorem pos2B_eq (I : General.Inst) : pos2B I = (pos2AnyB I && I.2.2.isEmpty) := rfl

theorem pos2AnyB_of_pos2B {I : General.Inst} (h : pos2B I = true) : pos2AnyB I = true := by
  rw [pos2B_eq, Bool.and_eq_true] at h
  exact h.1

/-- Where T₀ = ∅ the two counts agree. -/
theorem countMissingMonotone2_eq_countValidMonotone2 {I : General.Inst} (h : pos2B I = true) :
    countMissingMonotone2 I = countValidMonotone2 I := by
  simp only [countMissingMonotone2, countValidMonotone2, h, pos2AnyB_of_pos2B h, ↓reduceIte]

theorem pos2AnyB_emptyClauseInst : pos2AnyB emptyClauseInst = false := by decide

/-- On the instances `fromMonotone2` produces, the two counts agree. -/
theorem countMissingMonotone2_fromMonotone2 (φ : CNF ℕ) :
    countMissingMonotone2 (fromMonotone2 φ) = countValidMonotone2 (fromMonotone2 φ) := by
  unfold fromMonotone2
  cases h : monotone2B φ
  · simp [countMissingMonotone2, countValidMonotone2, pos2AnyB_emptyClauseInst,
      pos2B_emptyClauseInst]
  · exact countMissingMonotone2_eq_countValidMonotone2 (pos2B_fromSAT φ h)

/-- **`#Monotone-2SAT` reduces parsimoniously to `countMissingMonotone2`.** -/
theorem sharpMonotone2SAT_reduces_countMissing :
    ParsimoniousReducible encCNF General.encInst SharpMonotone2SAT countMissingMonotone2 :=
  ⟨fromMonotone2, fromMonotone2_polyTime, fun φ =>
    (sharpMonotone2SAT_eq φ).trans (countMissingMonotone2_fromMonotone2 φ).symm⟩

/-! ### Membership -/

theorem pos2AnyB_polyTime : ComputableInPolyTime pos2AnyB General.encInst encBool := by
  refine .of_tidy ?_
  unfold pos2AnyB
  fun_prop

theorem pos2AnyB_polyTime_bin : ComputableInPolyTime pos2AnyB encInstBin encBool := by
  refine .of_tidy ?_
  unfold pos2AnyB
  fun_prop

theorem countMissingMonotone2_mem_SharpP : countMissingMonotone2 ∈ SharpP General.encInst := by
  have h := SharpP.ite_mem pos2AnyB_polyTime missingCount_mem_SharpP
    (SharpP.zero_mem (enc := General.encInst))
  convert h using 1
  funext I
  rfl

theorem countMissingMonotone2_mem_SharpP_bin : countMissingMonotone2 ∈ SharpP encInstBin := by
  have h := SharpP.ite_mem pos2AnyB_polyTime_bin missingCount_mem_SharpP_bin
    (SharpP.zero_mem (enc := encInstBin))
  convert h using 1
  funext I
  rfl

/-! ### One-call completeness -/

/-- **Counting the missing combinations of a monotone-shaped table, any T₀, is one-call
`#P`-complete**, attribute indices in binary. -/
theorem countMissingMonotone2_sharpPComplete_oneCall :
    OneCallSharpPComplete encInstBin countMissingMonotone2 :=
  ⟨countMissingMonotone2_mem_SharpP_bin,
    (sharpMonotone2SAT_oneCallSharpPHard.trans_parsimonious
      sharpMonotone2SAT_reduces_countMissing).trans_parsimonious (idParsimonious _)⟩

/-- The same, attribute indices in unary (`encInst`). -/
theorem countMissingMonotone2_sharpPComplete_oneCall_unary :
    OneCallSharpPComplete General.encInst countMissingMonotone2 :=
  ⟨countMissingMonotone2_mem_SharpP,
    sharpMonotone2SAT_oneCallSharpPHard.trans_parsimonious sharpMonotone2SAT_reduces_countMissing⟩

end Latc.PaperD.Valiant
