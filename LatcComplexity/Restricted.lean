import LatcComplexity.Binary
import Complexity.Computability.Complexity.Classes.Promise.Reduction

/-!
# Hardness already on Boolean domains with T₀ = ∅

The reduction `fromSAT` of `LatcComplexity.General` produces only instances whose declared domains
all have size 2 and whose table T₀ has no rows (`fromSAT_mem_boolEmpty`). So the hardness of
`General` and `CountingGeneral` holds already on that subclass, `BoolEmpty`. This file states it,
for the binary encoding `encInstBin`:

* `MissingNonemptyBoolEmpty_npHard_bin`: deciding M(T₀) ≠ ∅ on `BoolEmpty` instances (the set
  `MissingNonempty ∩ BoolEmpty`) is NP-hard.
* `CompleteBoolEmpty_coNPHard_bin`: deciding completeness on `BoolEmpty` instances
  (`Complete ∩ BoolEmpty`) is coNP-hard.
* `missingNonemptyPromise_npHard_bin`: the promise version, whose yes-instances are the
  `BoolEmpty` instances with M(T₀) ≠ ∅ and whose no-instances are the `BoolEmpty` instances with
  M(T₀) = ∅, is NP-hard as a promise problem (Complexitylib's `PromiseProblem.NPHard`).
* `missingCountBoolEmpty_sharpPHard_bin`: counting |M(T₀)| on `BoolEmpty` instances (and `0` on
  the others) is #P-hard under parsimonious reductions.

The restricted sets contain their restriction: a decider for `MissingNonempty ∩ BoolEmpty` also
checks that the instance is in `BoolEmpty`. The promise version leaves the instances outside
`BoolEmpty` unconstrained.
-/

namespace Latc.PaperD.General

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-- Boolean domains and an empty table: every declared domain size is 2 and T₀ has no rows. -/
def BoolEmpty : Set Inst := {I | (∀ d ∈ I.1, d = 2) ∧ I.2.2 = []}

instance (I : Inst) : Decidable (I ∈ BoolEmpty) :=
  inferInstanceAs (Decidable ((∀ d ∈ I.1, d = 2) ∧ I.2.2 = []))

/-- **The shape of `fromSAT`:** its instances have Boolean domains and an empty table. -/
theorem fromSAT_mem_boolEmpty (φ : CNF ℕ) : fromSAT φ ∈ BoolEmpty :=
  ⟨fun _ hd => List.eq_of_mem_replicate hd, rfl⟩

/-- `fromSAT` is polynomial-time into the binary encoding. -/
theorem fromSAT_polyTime_bin : ComputableInPolyTime fromSAT encCNF encInstBin :=
  encInst_to_encInstBin_polyTime.comp fromSAT_polyTime

/-- `φ` is satisfiable iff its instance has a missing state. -/
theorem mem_SAT_iff_fromSAT (φ : CNF ℕ) : φ ∈ SAT ↔ fromSAT φ ∈ MissingNonempty := by
  rw [mem_SAT, ← CNF.satisfiable_denseRelabel,
    satisfiable_iff _ φ.numVars fun v hv => CNF.mem_vars_denseRelabel_lt φ hv]
  simp [MissingNonempty, fromSAT]

/-- M(T₀) ≠ ∅, on Boolean domains with T₀ = ∅. -/
def MissingNonemptyBoolEmpty : Set Inst := MissingNonempty ∩ BoolEmpty

/-- M(T₀) = ∅, on Boolean domains with T₀ = ∅. -/
def CompleteBoolEmpty : Set Inst := Complete ∩ BoolEmpty

theorem SAT_reduces_boolEmpty :
    PolyTimeReducible encCNF encInstBin SAT MissingNonemptyBoolEmpty :=
  ⟨fromSAT, fromSAT_polyTime_bin, fun φ => by
    rw [mem_SAT_iff_fromSAT]
    exact ⟨fun h => ⟨h, fromSAT_mem_boolEmpty φ⟩, fun h => h.1⟩⟩

theorem UNSAT_reduces_boolEmpty :
    PolyTimeReducible encCNF encInstBin UNSAT CompleteBoolEmpty :=
  ⟨fromSAT, fromSAT_polyTime_bin, fun φ => by
    change φ ∉ SAT ↔ fromSAT φ ∉ MissingNonempty ∧ fromSAT φ ∈ BoolEmpty
    rw [mem_SAT_iff_fromSAT]
    exact ⟨fun h => ⟨h, fromSAT_mem_boolEmpty φ⟩, fun h => h.1⟩⟩

/-- **NP-hardness on Boolean domains with T₀ = ∅.** -/
theorem MissingNonemptyBoolEmpty_npHard_bin : NPHard encInstBin MissingNonemptyBoolEmpty :=
  CookLevin.SAT_npHard.trans SAT_reduces_boolEmpty

/-- **coNP-hardness on Boolean domains with T₀ = ∅.** -/
theorem CompleteBoolEmpty_coNPHard_bin : coNPHard encInstBin CompleteBoolEmpty :=
  CookLevin.UNSAT_coNPComplete.2.trans UNSAT_reduces_boolEmpty

/-- The promise problem: on Boolean domains with T₀ = ∅, tell M(T₀) ≠ ∅ from M(T₀) = ∅. -/
def missingNonemptyPromise : PromiseProblem Inst :=
  (PromiseProblem.ofSet MissingNonempty).restrict BoolEmpty

/-- **The promise version is NP-hard.** -/
theorem missingNonemptyPromise_npHard_bin :
    PromiseProblem.NPHard encInstBin missingNonemptyPromise :=
  PromiseProblem.npHard_of_polyTimeReducible_SAT ⟨fromSAT, fromSAT_polyTime_bin,
    fun φ h => ⟨(mem_SAT_iff_fromSAT φ).1 h, fromSAT_mem_boolEmpty φ⟩,
    fun φ h => ⟨fun h' => h ((mem_SAT_iff_fromSAT φ).2 h'), fromSAT_mem_boolEmpty φ⟩⟩

/-- |M(T₀)| on Boolean domains with T₀ = ∅, and `0` on other instances. -/
def missingCountBoolEmpty (I : Inst) : ℕ := if I ∈ BoolEmpty then missingCount I else 0

theorem sharpSAT_reduces_boolEmpty :
    ParsimoniousReducible encCNF encInstBin SharpSAT missingCountBoolEmpty :=
  ⟨fromSAT, fromSAT_polyTime_bin, fun φ => by
    simp only [missingCountBoolEmpty, fromSAT_mem_boolEmpty φ, ↓reduceIte]
    exact sharpSAT_eq_missingCount φ⟩

/-- **#P-hardness on Boolean domains with T₀ = ∅**, under parsimonious reductions. -/
theorem missingCountBoolEmpty_sharpPHard_bin : SharpPHard encInstBin missingCountBoolEmpty :=
  CookLevin.SharpSAT_sharpPHard.trans sharpSAT_reduces_boolEmpty

end Latc.PaperD.General
