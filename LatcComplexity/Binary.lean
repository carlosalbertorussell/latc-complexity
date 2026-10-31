import LatcComplexity.Monotone

/-!
# A binary attribute index

`encInst` writes the attribute index `i` of a condition `(i, v)` in unary. `encInstBin` writes it
in binary, like every other number of an instance. The problems are the same sets of instances;
only the encoding changes.

* `condHoldsBin_polyTime`, `checkBin_polyTime`: the certificate check reads a value at a binary
  position, with Complexitylib's `listGetD_binary` (the index is capped at the length of the list
  while it is read, so it is never expanded to unary).
* `encInst_to_encInstBin_polyTime`: the identity is polynomial-time from `encInst` to
  `encInstBin`, so hardness for `encInst` transfers to `encInstBin` (`idReduction`).
* `MissingNonempty_npComplete_bin`, `Complete_coNPComplete_bin`,
  `missingNonempty_finset_npComplete_bin`, `complete_finset_coNPComplete_bin`,
  `missingCount_sharpPComplete_bin`, `countValidMonotone2_oneCallSharpPComplete_bin`: the theorems
  of `General`, `Adequacy`, `CountingGeneral` and `Monotone` for `encInstBin`.
-/

namespace Latc.PaperD.General

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-- Instances with every number in binary, the attribute index of a condition included. -/
abbrev encInstBin : Inst ↪ List Bool :=
  encPair (encList encNat) (encPair (encList (encList (encPair encNat encNat)))
    (encList (encList encNat)))

/-- The identity is polynomial-time from the unary-index encoding to the binary one. -/
theorem encInst_to_encInstBin_polyTime :
    ComputableInPolyTime (fun I : Inst => I) encInst encInstBin := by
  have hu := ComputableTidilyInPolyTime.unary_to_binary
  refine .of_tidy ?_
  have h : ComputableTidilyInPolyTime
      (fun I : Inst => (I.1, (I.2.1.map (List.map fun a : Cond => (a.1, a.2)), I.2.2)))
      encInst encInstBin := by fun_prop
  simpa using h

/-- The identity reduces a problem in the unary-index encoding to the same problem in the binary
one. -/
theorem idReduction (A : Set Inst) : PolyTimeReducible encInst encInstBin A A :=
  ⟨fun I => I, encInst_to_encInstBin_polyTime, fun _ => Iff.rfl⟩

/-- The identity is a parsimonious reduction from the unary-index encoding to the binary one. -/
theorem idParsimonious (f : Inst → ℕ) : ParsimoniousReducible encInst encInstBin f f :=
  ⟨fun I => I, encInst_to_encInstBin_polyTime, fun _ => rfl⟩

/-! ### The certificate check at a binary index -/

/-- Shift the values by one, so that the default `0` of an out-of-range lookup matches no value. -/
def condHoldsBin (s : List ℕ) (a : Cond) : Bool := (s.map (· + 1)).getD a.1 0 == a.2 + 1

theorem condHoldsBin_eq (s : List ℕ) (a : Cond) : condHoldsBin s a = condHoldsB s a := by
  unfold condHoldsBin condHoldsB
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases s[a.1]? with _ | x <;> simp

theorem condHoldsBin_polyTime :
    ComputableInPolyTime (fun p : List ℕ × Cond => condHoldsBin p.1 p.2)
    (encPair (encList encNat) (encPair encNat encNat)) encBool := by
  have hl : ComputableTidilyInPolyTime (fun p : List ℕ × Cond => p.1.map (· + 1))
      (encPair (encList encNat) (encPair encNat encNat)) (encList encNat) := by fun_prop
  have hd := ComputableTidilyInPolyTime.listGetD_binary (encA := encNat) (encL := encList encNat)
    (i := fun p : List ℕ × Cond => p.2.1) 0 hl (by fun_prop)
  refine .of_tidy ?_
  unfold condHoldsBin
  fun_prop

/-- The check of a candidate missing state, reading conditions at binary indices. -/
def checkBin (p : Inst × List ℕ) : Bool :=
  inDomainsB p.1.1 p.2 && p.1.2.1.all (fun c => c.any (condHoldsBin p.2)) &&
    !decide (p.2 ∈ p.1.2.2)

theorem checkBin_eq : checkBin = check := by
  have h : condHoldsBin = condHoldsB := funext fun s => funext fun a => condHoldsBin_eq s a
  funext p
  simp only [checkBin, check, h]

theorem checkBin_polyTime :
    ComputableInPolyTime check (encPair encInstBin (encList encNat)) encBool := by
  have h := condHoldsBin_polyTime.tidy
  rw [← checkBin_eq]
  refine .of_tidy ?_
  unfold checkBin inDomainsB
  fun_prop

theorem length_domains_le_bin (I : Inst) :
    (encList encNat I.1).length ≤ (encInstBin I).length := by
  rw [encPair_apply, List.length_append, length_frame]
  omega

/-! ### NP- and coNP-completeness -/

theorem MissingNonempty_mem_NP_bin : MissingNonempty ∈ NP encInstBin := by
  have h := mem_NP_of_witness (p := Polynomial.X) (Decoder.list Decoder.nat) checkBin_polyTime
    (R := fun I s => InDomains I.1 s ∧ Valid I.2.1 s ∧ s ∉ I.2.2) (fun I s => check_iff I s)
    (fun I s hs => ⟨s, hs, by
      simpa using (length_encList_le_of_inDomains hs.1).trans (length_domains_le_bin I)⟩)
  exact h

/-- **Proposition 5, NP part, binary attribute index.** -/
theorem MissingNonempty_npComplete_bin : NPComplete encInstBin MissingNonempty :=
  ⟨MissingNonempty_mem_NP_bin, MissingNonempty_npHard.trans (idReduction _)⟩

/-- **Proposition 5, coNP part, binary attribute index.** -/
theorem Complete_coNPComplete_bin : coNPComplete encInstBin Complete :=
  MissingNonempty_npComplete_bin.compl

/-- **Proposition 5, NP part, on latc-check's `Latc.missing`, binary attribute index.** -/
theorem missingNonempty_finset_npComplete_bin :
    NPComplete encInstBin {I : Inst | (missing I.con I.table).Nonempty} := by
  have : {I : Inst | (missing I.con I.table).Nonempty} = MissingNonempty :=
    Set.ext fun I => (mem_MissingNonempty_iff I).symm
  rw [this]
  exact MissingNonempty_npComplete_bin

/-- **Proposition 5, coNP part, on latc-check's `Latc.missing`, binary attribute index.** -/
theorem complete_finset_coNPComplete_bin :
    coNPComplete encInstBin {I : Inst | missing I.con I.table = ∅} := by
  have : {I : Inst | missing I.con I.table = ∅} = Complete :=
    Set.ext fun I => (mem_Complete_iff I).symm
  rw [this]
  exact Complete_coNPComplete_bin

/-! ### #P-completeness of counting -/

theorem certState_polyTime_bin :
    ComputableInPolyTime (fun p : Inst × List Bool => certState p.1 p.2)
      (encPair encInstBin encBits) (encList encNat) := by
  have hd : ComputableTidilyInPolyTime
      (fun p : Inst × List Bool => (Decoder.list Decoder.nat).decode p.2)
      (encPair encInstBin encBits) (encList encNat) :=
    (Decoder.list Decoder.nat).computableInPolyTime.tidy.comp (by fun_prop)
  have hn : ComputableTidilyInPolyTime (fun p : Inst × List Bool => p.1.1.length)
      (encPair encInstBin encBits) encUnary := by fun_prop
  exact .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput hd hn)

theorem cverifier_polyTime_bin :
    ComputableInPolyTime cverifier (encPair encInstBin encBits) encBool := by
  have hc := checkBin_polyTime.tidy
  have hs := certState_polyTime_bin.tidy
  have he := encList_polyTime.tidy
  refine .of_tidy ?_
  unfold cverifier certWord
  fun_prop

theorem certLen_polyTime_bin : ComputableInPolyTime certLen encInstBin encUnary := by
  have he := encList_polyTime.tidy
  refine .of_tidy ?_
  unfold certLen
  fun_prop

theorem missingCount_mem_SharpP_bin : missingCount ∈ SharpP encInstBin := by
  have h := mem_SharpP_of_polyTime_length cverifier_polyTime_bin certLen_polyTime_bin
  rwa [show (fun a => acceptCount cverifier a (certLen a)) = missingCount from
    funext fun a => (missingCount_eq_acceptCount a).symm] at h

/-- **Proposition 5, counting part, binary attribute index:** counting |M(T₀)| is `#P`-complete
under parsimonious reductions. -/
theorem missingCount_sharpPComplete_bin : SharpPComplete encInstBin missingCount :=
  ⟨missingCount_mem_SharpP_bin, missingCount_sharpPHard.trans (idParsimonious _)⟩

/-! ### The monotone two-literal case -/

/-- The clause part of `pos2B` and `pos2AnyB`, binary attribute index: the index is compared with
the number of attributes in binary. -/
theorem pos2Clauses_polyTime_bin : ComputableTidilyInPolyTime (fun I : Inst => I.2.1.all fun c =>
    c.length == 2 && c.all fun a => decide (a.1 < I.1.length) && a.2 == 1) encInstBin encBool := by
  have hlen : ComputableTidilyInPolyTime (fun I : Inst => I.1.length) encInstBin encNat :=
    ComputableTidilyInPolyTime.unary_to_binary.comp (by fun_prop)
  have hcond : ComputableTidilyInPolyTime
      (fun q : ℕ × Cond => decide (q.2.1 < q.1) && q.2.2 == 1)
      (encPair encNat (encPair encNat encNat)) encBool :=
    ComputableTidilyInPolyTime.bool_and'
      (ComputableTidilyInPolyTime.binary_lt' (by fun_prop) (by fun_prop)) (by fun_prop)
  have hclause : ComputableTidilyInPolyTime
      (fun p : ℕ × List Cond =>
        p.2.length == 2 && p.2.all fun a => decide (a.1 < p.1) && a.2 == 1)
      (encPair encNat (encList (encPair encNat encNat))) encBool :=
    ComputableTidilyInPolyTime.bool_and' (by fun_prop)
      (ComputableTidilyInPolyTime.allWith hcond (by fun_prop) (by fun_prop))
  exact ComputableTidilyInPolyTime.allWith hclause hlen (by fun_prop)

theorem pos2B_polyTime_bin : ComputableInPolyTime pos2B encInstBin encBool := by
  refine .of_tidy ?_
  unfold pos2B
  exact ComputableTidilyInPolyTime.bool_and'
    (ComputableTidilyInPolyTime.bool_and' (by fun_prop) pos2Clauses_polyTime_bin) (by fun_prop)

theorem countValidMonotone2_mem_SharpP_bin : countValidMonotone2 ∈ SharpP encInstBin := by
  have h := SharpP.ite_mem pos2B_polyTime_bin missingCount_mem_SharpP_bin
    (SharpP.zero_mem (enc := encInstBin))
  convert h using 1
  funext I
  rfl

/-- **The monotone two-literal case, binary attribute index, conditional on Valiant's theorem.** -/
theorem countValidMonotone2_oneCallSharpPComplete_bin
    (hValiant : OneCallSharpPHard encCNF SharpMonotone2SAT) :
    OneCallSharpPComplete encInstBin countValidMonotone2 :=
  ⟨countValidMonotone2_mem_SharpP_bin,
    (hValiant.trans_parsimonious sharpMonotone2SAT_reduces).trans_parsimonious
      (idParsimonious _)⟩

end Latc.PaperD.General
