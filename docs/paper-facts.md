# Paper D: fact check of theorem names and references

Checked 2026-10-29 against commit `011cd1a` of latc-complexity, for Paper D, "Machine-Checked
Complexity of Decision-Table Completeness in Lean" (ITP 2027). No Lean file was changed.
Updated 2026-10-31 for commit `242311b` (counting with a fixed number of attributes, Gap 2 of
`docs/gaps-plan.md`): line numbers in `Tractable.lean`, the §6 entries, the audit count and the
line counts.

## Summary

* **Theorems: 52/52 found.** These are the 52 rows of the README's theorem tables (50 names;
  `MissingNonempty_npComplete` and `Complete_coNPComplete` each appear twice, once for Boolean domains in
  `Latc.PaperD` and once for general domains in `Latc.PaperD.General`). The 49th,
  `countValidMonotone2_mem_SharpP_bin`, was added to the README on 2026-10-31, and so were the
  last three, the counting result of commit `242311b` (`missingCount_eq_weighted_of_le`,
  `length_classStates_le`, `missingCountFixedAttrs_polyTime`); §6 below also records its `_unary`
  corollary, which the paper draft cites. They include all 24
  theorems the outline's section table now cites, marked "(outline)" below.
* **Wrong names in the outline: none.** Every name it cites exists exactly as written: the 22
  first checked, and the 24 its section table cites after the edits of 2026-10-30 and 31. Of four
  cautions in the next section, two were resolved in the outline and two still apply.
* **References: 12/15 confirmed.** Three are not found as asked: the Coq Library of Complexity
  Theory has no paper of its own, Karp21 has no Isabelle paper or AFP entry, and complexitylib
  states no preferred citation. (complexitylib was later resolved from the repository itself:
  cite it as software by Samuel Schlesinger and the Complexitylib contributors; see reference
  13.) BibTeX is in `docs/paper-refs.bib`.
* **Novelty:** the search found no paper or formalisation proving *decision-table* completeness NP-, coNP- or
  #P-complete. Hardness of rule-set coverage is known in adjacent settings, and Paper D should
  cite it:
  * firewall completeness (Elmallah and Gouda, IEEE TDSC 2017);
  * quasi-reducibility and pattern completeness (Kapur et al. 1991; Thiemann and Yamada);
  * unions of boxes (Chan; Bringmann and Friedrich);
  * a claim without proof in a GE patent (Jolly).

  Paper D can claim the first such result for decision tables, with domain constraints, counting
  and a Lean proof, but not the first hardness result for coverage in general. Vu and Demetrovics
  (Algorithms, 2026), on decision tables with labelled nulls, still need reading in full (see
  Novelty, item 6).
* **Axiom audit:** the axiom lines below are copied from the audit recorded in the README (build of
  2026-10-29, `LatcComplexity/Axioms.lean`). The audit was **not re-run** in this session: the
  sandbox refused to install the Lean toolchain. A whole-word search of every `.lean` file for
  `sorry`, `admit`, `native_decide` and `axiom` was re-run and finds them only in `#print axioms`
  commands.

## Outline names: check and cautions

**As first checked (2026-10-29).** The task's outline list held 19 explicit names plus "the main
theorems of `Adequacy.lean`", which is not a Lean name; it reads as `mem_MissingNonempty_iff`,
`mem_Complete_iff` and `coe_missing_map_toList`. All 22 existed exactly as written.

**As the outline stands now (updated 2026-10-31).** After the edits of 2026-10-30, the outline's
section table cites the 24 names below, by paper section; all exist exactly as written. Compared
with the first list:

* three names were added: `missingNonempty_finset_npComplete_bin` (replacing the unary
  `missingNonempty_finset_npComplete` in §4), and `missingCount_eq_acceptCount` and
  `sharpSAT_eq_missingCount`, the general-domain counting lemmas, in §5;
* two names of the first list are no longer cited: `missingNonempty_finset_npComplete` and
  `complete_finset_coNPComplete`, the unary-index forms (both still exist, `Adequacy.lean:136`
  and `:145`);
* on 2026-10-31 the monotone case in §5 moved to the all-binary encoding too:
  `countValidMonotone2_mem_SharpP_bin` and `countValidMonotone2_oneCallSharpPComplete_bin`
  replace their unary forms (`Monotone.lean:177` and `:186`, both still present).
  `sharpMonotone2SAT_reduces` has no `_bin` form; it reduces to `encInst`, and hardness for
  `encInstBin` follows by composing with the identity re-encoding, as the proof of
  `countValidMonotone2_oneCallSharpPComplete_bin` does. The count stays at 23;
* also on 2026-10-31, §4 added `complete_finset_coNPComplete_bin`, the binary form of the
  completeness result on `Latc.missing`, beside its non-emptiness counterpart: 24 names.

| § | Outline name | Full name | File:line | Status |
|---|---|---|---|---|
| 2 | `holdsAll_eq_eval` | `Latc.PaperD.holdsAll_eq_eval` | `LatcComplexity/Bridge.lean:29` | exists, exact name |
| 2 | `satisfiable_decode_iff` | `Latc.PaperD.satisfiable_decode_iff` | `LatcComplexity/Bridge.lean:35` | exists, exact name |
| 3 | `encInst_to_encInstBin_polyTime` | `Latc.PaperD.General.encInst_to_encInstBin_polyTime` | `LatcComplexity/Binary.lean:31` | exists, exact name |
| 3 | `mem_MissingNonempty_iff` | `Latc.PaperD.General.mem_MissingNonempty_iff` | `LatcComplexity/Adequacy.lean:101` | exists, exact name |
| 3 | `mem_Complete_iff` | `Latc.PaperD.General.mem_Complete_iff` | `LatcComplexity/Adequacy.lean:113` | exists, exact name |
| 3 | `coe_missing_map_toList` | `Latc.PaperD.General.coe_missing_map_toList` | `LatcComplexity/Adequacy.lean:119` | exists, exact name |
| 4 | `MissingNonempty_npComplete_bin` | `Latc.PaperD.General.MissingNonempty_npComplete_bin` | `LatcComplexity/Binary.lean:103` | exists, exact name |
| 4 | `Complete_coNPComplete_bin` | `Latc.PaperD.General.Complete_coNPComplete_bin` | `LatcComplexity/Binary.lean:107` | exists, exact name |
| 4 | `missingNonempty_finset_npComplete_bin` | `Latc.PaperD.General.missingNonempty_finset_npComplete_bin` | `LatcComplexity/Binary.lean:111` | exists, exact name (added 2026-10-30) |
| 4 | `complete_finset_coNPComplete_bin` | `Latc.PaperD.General.complete_finset_coNPComplete_bin` | `LatcComplexity/Binary.lean:119` | exists, exact name (added 2026-10-31) |
| 5 | `missingCount_sharpPComplete_bin` | `Latc.PaperD.General.missingCount_sharpPComplete_bin` | `LatcComplexity/Binary.lean:161` | exists, exact name |
| 5 | `missingCount_eq_acceptCount` | `Latc.PaperD.General.missingCount_eq_acceptCount` | `LatcComplexity/CountingGeneral.lean:128` | exists, exact name (added 2026-10-30) |
| 5 | `sharpSAT_eq_missingCount` | `Latc.PaperD.General.sharpSAT_eq_missingCount` | `LatcComplexity/CountingGeneral.lean:205` | exists, exact name (added 2026-10-30) |
| 5 | `countMissing_eq_sharpSAT` | `Latc.PaperD.countMissing_eq_sharpSAT` | `LatcComplexity/Counting.lean:104` | exists, exact name |
| 5 | `countValidMonotone2_mem_SharpP_bin` | `Latc.PaperD.General.countValidMonotone2_mem_SharpP_bin` | `LatcComplexity/Binary.lean:171` | exists, exact name (added 2026-10-31) |
| 5 | `sharpMonotone2SAT_reduces` | `Latc.PaperD.General.sharpMonotone2SAT_reduces` | `LatcComplexity/Monotone.lean:170` | exists, exact name; targets `encInst`, no `_bin` form |
| 5 | `countValidMonotone2_oneCallSharpPComplete_bin` | `Latc.PaperD.General.countValidMonotone2_oneCallSharpPComplete_bin` | `LatcComplexity/Binary.lean:179` | exists, exact name (added 2026-10-31) |
| 6 | `completeNoConstraints_mem_P` | `Latc.PaperD.General.completeNoConstraints_mem_P` | `LatcComplexity/Tractable.lean:196` | exists, exact name |
| 6 | `missingNonemptyNoConstraints_mem_P` | `Latc.PaperD.General.missingNonemptyNoConstraints_mem_P` | `LatcComplexity/Tractable.lean:208` | exists, exact name |
| 6 | `missingCountNoConstraints_polyTime` | `Latc.PaperD.General.missingCountNoConstraints_polyTime` | `LatcComplexity/Tractable.lean:165` | exists, exact name |
| 6 | `missingCount_eq_of_noConstraints` | `Latc.PaperD.General.missingCount_eq_of_noConstraints` | `LatcComplexity/Tractable.lean:103` | exists, exact name |
| 6 | `completeFixedAttrs_mem_P` | `Latc.PaperD.General.completeFixedAttrs_mem_P` | `LatcComplexity/Tractable.lean:480` | exists, exact name |
| 6 | `missingNonemptyFixedAttrs_mem_P` | `Latc.PaperD.General.missingNonemptyFixedAttrs_mem_P` | `LatcComplexity/Tractable.lean:468` | exists, exact name |
| 6 | `length_candidateStates_le` | `Latc.PaperD.General.length_candidateStates_le` | `LatcComplexity/Tractable.lean:293` | exists, exact name |

Cautions. None of these is a wrong name. Cautions 2 and 3 were resolved in the outline on
2026-10-30; 1 and 4 still apply.

1. **Namespaces.** `MissingNonempty_npComplete`, `Complete_coNPComplete`, `MissingNonempty_mem_NP`,
   `SAT_reduces` and `fromSAT_polyTime` exist both in `Latc.PaperD` (Boolean domains, `Bridge.lean`)
   and in `Latc.PaperD.General` (general domains, `General.lean`). These are different theorems
   about different `Inst` types. If the paper cites one of them, give the namespace.
2. **Resolved: `countMissing_eq_sharpSAT` is about Boolean domains** (`Latc.PaperD`,
   `Counting.lean`), stated for `countMissing` on a CNF with bit-vector rows. The outline's §5 now
   cites the general-domain lemmas `missingCount_eq_acceptCount` and `sharpSAT_eq_missingCount`
   and marks this one "(Boolean domains)". The contributions list was corrected to match:
   over general domains, membership is by counting certificates and hardness by a parsimonious
   reduction *from* #SAT; only the Boolean case reduces *to* #SAT.
3. **Resolved: the outline mixed encodings.** §4 now cites the all-binary
   `missingNonempty_finset_npComplete_bin` beside `MissingNonempty_npComplete_bin` and
   `Complete_coNPComplete_bin`, and §5's monotone case cites the `_bin` forms (2026-10-31). The tractable theorems are stated for `encInstBin`; their
   `encInst` versions carry the suffix `_unary`.
4. **`countValidMonotone2_oneCallSharpPComplete(_bin)` is conditional.** Valiant's theorem is its
   hypothesis `hValiant`, not an axiom, so it does not appear in the axiom audit. Hardness is under
   one-call reductions, defined in `Monotone.lean`, and is not Complexitylib's parsimonious
   `SharpPHard`.

A side note on the audit file: it prints 174 of the 191 `theorem`/`lemma` declarations in
`LatcComplexity/` (130 of 147 at `011cd1a`; commit `242311b` added 44 declarations to
`Tractable.lean`, all printed). The other 17 are helper lemmas: `Inst.getElem?_toList`, `Inst.length_toList`,
`assignment_pad`, `condHoldsB_polyTime`, `encList_polyTime`, `fromSAT_get`, `fromSAT_n`,
`getElem?_toList_boolTuple`, `length_certWord`, `length_domains_le`, `length_encCNF_le`,
`length_tuple`, `lookup_polyTime`, `mem_vars_denseRelabel_iff`, `ofFn_certFun`, `ofFn_getD` and
`pos2B_emptyClauseInst`. The README says the file covers "every theorem", which is not literally
true. All 53 theorems below are printed.

## Theorems by paper section

For each theorem below: the full name; whether it exists and where (`(outline)` marks a name the
outline's section table cites as of 2026-10-31); a one-sentence reading; its axiom line; and the Lean statement, copied verbatim
from the source up to `:=`. The statements are written inside the theorem's namespace, under
`open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM` (`Adequacy.lean` opens only
`Cslib.Complexity`).

Notation: an instance `I = (d, S, T)` has domain sizes `I.1`, clauses `I.2.1` and rows of T₀
`I.2.2`. `I.n = I.1.length` is the number of attributes. `missing I.con I.table` is latc-check's
M(T₀) for the table `I` denotes, and `missingCount I` is its cardinality.

### §2. Setting: latc-check's Boolean model agrees with Complexitylib

#### `Latc.PaperD.holdsAll_eq_eval` (outline)

- Exists: yes, `LatcComplexity/Bridge.lean:29`
- Reading: A Boolean state satisfies a set of clause constraints in latc-check's sense (Paper A's `Latc.Prop5`) exactly when it satisfies the corresponding Complexitylib CNF formula `toCNF S`.
- Axioms: `[propext, Quot.sound]`

```lean
theorem holdsAll_eq_eval (S : Prop5.ConSet ℕ) (x : ℕ → Bool) :
    Prop5.holdsAll S x = (toCNF S).eval x
```

#### `Latc.PaperD.satisfiable_decode_iff` (outline)

- Exists: yes, `LatcComplexity/Bridge.lean:35`
- Reading: Paper A's satisfiability of the decoded constraint set coincides with Complexitylib's satisfiability of `toCNF S`, so the two libraries' notions of SAT agree on clause constraints.
- Axioms: `[propext, Quot.sound]`

```lean
theorem satisfiable_decode_iff (S : Prop5.ConSet ℕ) :
    Prop5.Satisfiable (Prop5.decode S) ↔ (toCNF S).Satisfiable
```

### §3. Encoding and adequacy

#### `Latc.PaperD.General.check_polyTime`

- Exists: yes, `LatcComplexity/General.lean:104`
- Reading: Checking whether a list of numbers is a missing state of an instance (in the domains, satisfies every clause, not a row of T₀) is computable in polynomial time under `encInst`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem check_polyTime : ComputableInPolyTime check (encPair encInst (encList encNat)) encBool
```

#### `Latc.PaperD.General.checkBin_polyTime`

- Exists: yes, `LatcComplexity/Binary.lean:80`
- Reading: The same certificate check is polynomial-time when the attribute index of a condition is also written in binary (`encInstBin`).
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem checkBin_polyTime :
    ComputableInPolyTime check (encPair encInstBin (encList encNat)) encBool
```

#### `Latc.PaperD.General.encInst_to_encInstBin_polyTime` (outline)

- Exists: yes, `LatcComplexity/Binary.lean:31`
- Reading: Re-encoding an instance from the unary-index encoding `encInst` to the all-binary encoding `encInstBin` is polynomial-time, so lower bounds for `encInst` transfer to `encInstBin`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem encInst_to_encInstBin_polyTime :
    ComputableInPolyTime (fun I : Inst => I) encInst encInstBin
```

#### `Latc.PaperD.General.mem_MissingNonempty_iff` (outline)

- Exists: yes, `LatcComplexity/Adequacy.lean:101`
- Reading: An encoded instance lies in the word problem `MissingNonempty` exactly when the missing set `Latc.missing` of the table it denotes in latc-check's model is non-empty.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem mem_MissingNonempty_iff (I : Inst) :
    I ∈ MissingNonempty ↔ (missing I.con I.table).Nonempty
```

#### `Latc.PaperD.General.mem_Complete_iff` (outline)

- Exists: yes, `LatcComplexity/Adequacy.lean:113`
- Reading: An encoded instance lies in `Complete` exactly when the missing set of the table it denotes is empty, i.e. the table is complete.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem mem_Complete_iff (I : Inst) : I ∈ Complete ↔ missing I.con I.table = ∅
```

#### `Latc.PaperD.General.coe_missing_map_toList` (outline)

- Exists: yes, `LatcComplexity/Adequacy.lean:119`
- Reading: Read as lists of values, the tuples of the missing set M(T₀) are exactly the in-domain, constraint-satisfying lists that are not rows of T₀, i.e. exactly the witnesses of `MissingNonempty`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem coe_missing_map_toList (I : Inst) :
    (((missing I.con I.table).map ⟨I.toList, I.toList_injective⟩ : Finset (List ℕ)) :
      Set (List ℕ)) = {s | InDomains I.1 s ∧ Valid I.2.1 s ∧ s ∉ I.2.2}
```

### §4. Decision problems

#### `Latc.PaperD.General.MissingNonempty_mem_NP`

- Exists: yes, `LatcComplexity/General.lean:125`
- Reading: Deciding whether a table over general finite domains has a missing state is in NP under `encInst`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem MissingNonempty_mem_NP : MissingNonempty ∈ NP encInst
```

#### `Latc.PaperD.General.fromSAT_polyTime`

- Exists: yes, `LatcComplexity/General.lean:142`
- Reading: The reduction from SAT (dense renumbering of variables, Boolean domains, empty T₀) is polynomial-time.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem fromSAT_polyTime : ComputableInPolyTime fromSAT encCNF encInst
```

#### `Latc.PaperD.General.satisfiable_iff`

- Exists: yes, `LatcComplexity/General.lean:151`
- Reading: A CNF formula whose variables are below `n` is satisfiable iff its clauses, read as conditions, have a valid state over `n` attributes with domain {0, 1}.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem satisfiable_iff (ψ : CNF ℕ) (n : ℕ) (hψ : ∀ v ∈ ψ.vars, v < n) :
    ψ.Satisfiable ↔ ∃ s, InDomains (List.replicate n 2) s ∧
      Valid (ψ.map (List.map toCond)) s
```

#### `Latc.PaperD.General.SAT_reduces`

- Exists: yes, `LatcComplexity/General.lean:186`
- Reading: SAT polynomial-time reduces to non-emptiness of the missing set.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem SAT_reduces : PolyTimeReducible encCNF encInst SAT MissingNonempty
```

#### `Latc.PaperD.General.MissingNonempty_npComplete`

- Exists: yes, `LatcComplexity/General.lean:197`
- Reading: Non-emptiness of the missing set, for clause constraints over general finite domains, is NP-complete under `encInst`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem MissingNonempty_npComplete : NPComplete encInst MissingNonempty
```

#### `Latc.PaperD.General.Complete_coNPComplete`

- Exists: yes, `LatcComplexity/General.lean:202`
- Reading: Completeness of a decision table with clause constraints over general finite domains is coNP-complete under `encInst`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem Complete_coNPComplete : coNPComplete encInst Complete
```

#### `Latc.PaperD.General.missingNonempty_finset_npComplete`

- Exists: yes, `LatcComplexity/Adequacy.lean:136`
- Reading: Stated directly on latc-check's `Latc.missing`: deciding whether the missing set of the denoted table is non-empty is NP-complete under `encInst`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingNonempty_finset_npComplete :
    NPComplete encInst {I : Inst | (missing I.con I.table).Nonempty}
```

#### `Latc.PaperD.General.complete_finset_coNPComplete`

- Exists: yes, `LatcComplexity/Adequacy.lean:145`
- Reading: Stated directly on latc-check's `Latc.missing`: deciding whether the denoted table is complete is coNP-complete under `encInst`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem complete_finset_coNPComplete :
    coNPComplete encInst {I : Inst | missing I.con I.table = ∅}
```

#### `Latc.PaperD.General.MissingNonempty_npComplete_bin` (outline)

- Exists: yes, `LatcComplexity/Binary.lean:103`
- Reading: Non-emptiness of the missing set remains NP-complete when every number, attribute indices included, is encoded in binary.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem MissingNonempty_npComplete_bin : NPComplete encInstBin MissingNonempty
```

#### `Latc.PaperD.General.Complete_coNPComplete_bin` (outline)

- Exists: yes, `LatcComplexity/Binary.lean:107`
- Reading: Completeness remains coNP-complete under the all-binary encoding `encInstBin`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem Complete_coNPComplete_bin : coNPComplete encInstBin Complete
```

#### `Latc.PaperD.General.missingNonempty_finset_npComplete_bin` (outline)

- Exists: yes, `LatcComplexity/Binary.lean:111`
- Reading: The `Latc.missing` form of NP-completeness of non-emptiness, under `encInstBin`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingNonempty_finset_npComplete_bin :
    NPComplete encInstBin {I : Inst | (missing I.con I.table).Nonempty}
```

#### `Latc.PaperD.General.complete_finset_coNPComplete_bin` (outline)

- Exists: yes, `LatcComplexity/Binary.lean:119`
- Reading: The `Latc.missing` form of coNP-completeness of completeness, under `encInstBin`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem complete_finset_coNPComplete_bin :
    coNPComplete encInstBin {I : Inst | missing I.con I.table = ∅}
```

#### `Latc.PaperD.MissingNonempty_npComplete`

- Exists: yes, `LatcComplexity/Bridge.lean:133`
- Reading: Boolean-domain version: for a CNF of constraints and T₀ given as bit vectors, non-emptiness of the missing set is NP-complete.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem MissingNonempty_npComplete : NPComplete encInst MissingNonempty
```

#### `Latc.PaperD.Complete_coNPComplete`

- Exists: yes, `LatcComplexity/Bridge.lean:138`
- Reading: Boolean-domain version: completeness is coNP-complete.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem Complete_coNPComplete : coNPComplete encInst Complete
```

### §5. Counting and the monotone case

#### `Latc.PaperD.countMissing_sharpPHard`

- Exists: yes, `LatcComplexity/Bridge.lean:157`
- Reading: Boolean domains: counting the missing states (and, with T₀ = ∅, the valid states) is #P-hard under parsimonious reductions.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem countMissing_sharpPHard : SharpPHard encInst countMissing
```

#### `Latc.PaperD.toSharpSAT_polyTime`

- Exists: yes, `LatcComplexity/Counting.lean:41`
- Reading: The translation of a Boolean instance into a single CNF (one extra clause per row of T₀) is polynomial-time.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem toSharpSAT_polyTime : ComputableInPolyTime toSharpSAT encInst encCNF
```

#### `Latc.PaperD.countMissing_eq_sharpSAT` (outline)

- Exists: yes, `LatcComplexity/Counting.lean:104`
- Reading: Boolean domains: the number of missing states equals the number of satisfying assignments of the formula `toSharpSAT I`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem countMissing_eq_sharpSAT (I : Inst) : countMissing I = SharpSAT (toSharpSAT I)
```

#### `Latc.PaperD.countMissing_reduces_sharpSAT`

- Exists: yes, `LatcComplexity/Counting.lean:127`
- Reading: Boolean domains: counting missing states reduces parsimoniously to #SAT.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem countMissing_reduces_sharpSAT :
    ParsimoniousReducible encInst encCNF countMissing SharpSAT
```

#### `Latc.PaperD.countMissing_mem_SharpP`

- Exists: yes, `LatcComplexity/Counting.lean:132`
- Reading: Boolean domains: counting missing states is in #P.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem countMissing_mem_SharpP : countMissing ∈ SharpP encInst
```

#### `Latc.PaperD.countMissing_sharpPComplete`

- Exists: yes, `LatcComplexity/Counting.lean:137`
- Reading: Boolean domains: counting missing states is #P-complete under parsimonious reductions.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem countMissing_sharpPComplete : SharpPComplete encInst countMissing
```

#### `Latc.PaperD.General.missingCount_eq_acceptCount` (outline)

- Exists: yes, `LatcComplexity/CountingGeneral.lean:128`
- Reading: General domains: |M(T₀)| equals the number of certificates of length `certLen I` that the verifier `cverifier` accepts, one canonical certificate per missing tuple.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingCount_eq_acceptCount (I : Inst) :
    missingCount I = acceptCount cverifier I (certLen I)
```

#### `Latc.PaperD.General.missingCount_mem_SharpP`

- Exists: yes, `LatcComplexity/CountingGeneral.lean:154`
- Reading: General domains: counting |M(T₀)| of the denoted table is in #P.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingCount_mem_SharpP : missingCount ∈ SharpP encInst
```

#### `Latc.PaperD.General.sharpSAT_eq_missingCount` (outline)

- Exists: yes, `LatcComplexity/CountingGeneral.lean:205`
- Reading: The SAT reduction preserves counts: #SAT of φ equals |M(T₀)| of the instance `fromSAT φ`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem sharpSAT_eq_missingCount (φ : CNF ℕ) : SharpSAT φ = missingCount (fromSAT φ)
```

#### `Latc.PaperD.General.missingCount_sharpPHard`

- Exists: yes, `LatcComplexity/CountingGeneral.lean:254`
- Reading: General domains: counting |M(T₀)| is #P-hard under parsimonious reductions.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingCount_sharpPHard : SharpPHard encInst missingCount
```

#### `Latc.PaperD.General.missingCount_sharpPComplete`

- Exists: yes, `LatcComplexity/CountingGeneral.lean:259`
- Reading: General domains: counting |M(T₀)| (with T₀ = ∅, the number |𝒱| of valid states) is #P-complete under parsimonious reductions, under `encInst`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingCount_sharpPComplete : SharpPComplete encInst missingCount
```

#### `Latc.PaperD.General.missingCount_sharpPComplete_bin` (outline)

- Exists: yes, `LatcComplexity/Binary.lean:161`
- Reading: Counting |M(T₀)| is #P-complete under parsimonious reductions also for the all-binary encoding `encInstBin`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingCount_sharpPComplete_bin : SharpPComplete encInstBin missingCount
```

#### `Latc.PaperD.General.countValidMonotone2_eq_card_validSpace`

- Exists: yes, `LatcComplexity/Monotone.lean:107`
- Reading: On instances of the monotone shape (domains {0,1}, every clause two conditions with value 1, T₀ = ∅), `countValidMonotone2` is the number of valid states |𝒱| in latc-check's model.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem countValidMonotone2_eq_card_validSpace (I : Inst) (h : pos2B I = true) :
    countValidMonotone2 I = (Latc.validSpace I.con).card
```

#### `Latc.PaperD.General.sharpMonotone2SAT_reduces` (outline)

- Exists: yes, `LatcComplexity/Monotone.lean:170`
- Reading: Unconditionally, #Monotone-2SAT reduces parsimoniously to counting valid states of monotone two-condition tables.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem sharpMonotone2SAT_reduces :
    ParsimoniousReducible encCNF encInst SharpMonotone2SAT countValidMonotone2
```

#### `Latc.PaperD.General.countValidMonotone2_mem_SharpP`

- Exists: yes, `LatcComplexity/Monotone.lean:177`
- Reading: Unconditionally, counting valid states of monotone two-condition tables is in #P.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem countValidMonotone2_mem_SharpP : countValidMonotone2 ∈ SharpP encInst
```

#### `Latc.PaperD.General.countValidMonotone2_mem_SharpP_bin` (outline)

- Exists: yes, `LatcComplexity/Binary.lean:171` (added 2026-10-31, when the README's binary table first listed it)
- Reading: Unconditionally, counting valid states of monotone two-condition tables is in #P under the all-binary encoding.
- Axioms: `[propext, Classical.choice, Quot.sound]` (audited in `LatcComplexity/Axioms.lean:117`; not among the README's exceptions)

```lean
theorem countValidMonotone2_mem_SharpP_bin : countValidMonotone2 ∈ SharpP encInstBin
```

#### `Latc.PaperD.General.countValidMonotone2_oneCallSharpPComplete`

- Exists: yes, `LatcComplexity/Monotone.lean:186`
- Reading: Assuming Valiant's theorem in the form that #Monotone-2SAT is #P-hard under one-call reductions, counting valid states of monotone two-condition tables is #P-complete under one-call reductions.
- Axioms: `[propext, Classical.choice, Quot.sound]` (Valiant's theorem enters as the explicit hypothesis `hValiant`, not as an axiom)

```lean
theorem countValidMonotone2_oneCallSharpPComplete
    (hValiant : OneCallSharpPHard encCNF SharpMonotone2SAT) :
    OneCallSharpPComplete encInst countValidMonotone2
```

#### `Latc.PaperD.General.countValidMonotone2_oneCallSharpPComplete_bin` (outline)

- Exists: yes, `LatcComplexity/Binary.lean:179`
- Reading: The same conditional one-call #P-completeness under the all-binary encoding.
- Axioms: `[propext, Classical.choice, Quot.sound]` (hypothesis `hValiant`, as above)

```lean
theorem countValidMonotone2_oneCallSharpPComplete_bin
    (hValiant : OneCallSharpPHard encCNF SharpMonotone2SAT) :
    OneCallSharpPComplete encInstBin countValidMonotone2
```

### §6. Tractable side

#### `Latc.PaperD.General.missingCount_eq_of_noConstraints` (outline)

- Exists: yes, `LatcComplexity/Tractable.lean:103`
- Reading: Without constraints, |M(T₀)| equals the product of the domain sizes minus the number of distinct rows of T₀ inside the declared domains.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingCount_eq_of_noConstraints (I : Inst) (h : I.2.1 = []) :
    missingCount I = domProd I - distinctRows I
```

#### `Latc.PaperD.General.missingCountNoConstraints_polyTime` (outline)

- Exists: yes, `LatcComplexity/Tractable.lean:165`
- Reading: Without constraints, |M(T₀)| is computable exactly in polynomial time under `encInstBin` (the function is zero on instances with constraints).
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingCountNoConstraints_polyTime :
    ComputableInPolyTime (fun I : Inst => if I.2.1 = [] then missingCount I else 0)
      encInstBin encNat
```

#### `Latc.PaperD.General.completeNoConstraints_mem_P` (outline)

- Exists: yes, `LatcComplexity/Tractable.lean:196`
- Reading: Deciding completeness of tables without constraints is in P, for any number of attributes and binary domain sizes.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem completeNoConstraints_mem_P :
    {I : Inst | I.2.1 = [] ∧ missing I.con I.table = ∅} ∈ P encInstBin
```

#### `Latc.PaperD.General.missingNonemptyNoConstraints_mem_P` (outline)

- Exists: yes, `LatcComplexity/Tractable.lean:208`
- Reading: Deciding non-emptiness of the missing set for tables without constraints is in P.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingNonemptyNoConstraints_mem_P :
    {I : Inst | I.2.1 = [] ∧ (missing I.con I.table).Nonempty} ∈ P encInstBin
```

#### `Latc.PaperD.General.length_candidateStates_le` (outline)

- Exists: yes, `LatcComplexity/Tractable.lean:293`
- Reading: With `N` the number of values written in the instance, at most (2N + 1)ᵏ candidate states are searched for `k` attributes.
- Axioms: `[propext, Quot.sound]`

```lean
theorem length_candidateStates_le (k : ℕ) (I : Inst) :
    (candidateStates k I).length ≤ (2 * I.numVals + 1) ^ k
```

#### `Latc.PaperD.General.candidateStates_polyTime`

- Exists: yes, `LatcComplexity/Tractable.lean:359`
- Reading: For each fixed `k`, the list of candidate states is computable in polynomial time under `encInstBin`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem candidateStates_polyTime (k : ℕ) :
    ComputableTidilyInPolyTime (candidateStates k) encInstBin (encList (encList encNat))
```

#### `Latc.PaperD.General.exists_missing_candidate_iff`

- Exists: yes, `LatcComplexity/Tractable.lean:399`
- Reading: With at most `k` attributes, a missing state exists iff some candidate state (values among 0..N and the written values) passes the check.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem exists_missing_candidate_iff {k : ℕ} {I : Inst} (hk : I.n ≤ k) :
    I ∈ MissingNonempty ↔ ∃ s ∈ candidateStates k I, check (I, s) = true
```

#### `Latc.PaperD.General.missingNonemptyFixedAttrs_mem_P` (outline)

- Exists: yes, `LatcComplexity/Tractable.lean:468`
- Reading: For each fixed `k`, deciding non-emptiness of the missing set for tables with at most `k` attributes (any clause constraints, binary domain sizes) is in P.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingNonemptyFixedAttrs_mem_P (k : ℕ) :
    {I : Inst | I.n ≤ k ∧ (missing I.con I.table).Nonempty} ∈ P encInstBin
```

#### `Latc.PaperD.General.completeFixedAttrs_mem_P` (outline)

- Exists: yes, `LatcComplexity/Tractable.lean:480`
- Reading: For each fixed `k`, deciding completeness of tables with at most `k` attributes is in P.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem completeFixedAttrs_mem_P (k : ℕ) :
    {I : Inst | I.n ≤ k ∧ missing I.con I.table = ∅} ∈ P encInstBin
```

#### `Latc.PaperD.General.missingCount_eq_weighted_of_le`

- Exists: yes, `LatcComplexity/Tractable.lean:840`
- Reading: With at most `k` attributes, |M(T₀)| is the sum, over the class vectors (each written value alone, or the unwritten class, per attribute) that are valid and not rows of T₀, of the number of states each stands for.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingCount_eq_weighted_of_le {k : ℕ} {I : Inst} (hk : I.n ≤ k) :
    missingCount I = ((classStates k I).map fun c =>
      if validB (I, c) then classStateWeight (I, c) else 0).sum
```

#### `Latc.PaperD.General.length_classStates_le`

- Exists: yes, `LatcComplexity/Tractable.lean:857` (declared `lemma`)
- Reading: With `N` the number of values written in the instance, at most (N + 1)ᵏ class vectors are summed for `k` attributes.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
lemma length_classStates_le (k : ℕ) (I : Inst) :
    (classStates k I).length ≤ (I.numVals + 1) ^ k
```

#### `Latc.PaperD.General.missingCountFixedAttrs_polyTime`

- Exists: yes, `LatcComplexity/Tractable.lean:1052`
- Reading: For each fixed `k`, |M(T₀)| for tables with at most `k` attributes (any clause constraints, binary domain sizes) is computable exactly in polynomial time under `encInstBin` (the function is zero on instances with more attributes).
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingCountFixedAttrs_polyTime (k : ℕ) :
    ComputableInPolyTime (fun I : Inst => if I.n ≤ k then missingCount I else 0)
      encInstBin encNat
```

#### `Latc.PaperD.General.missingCountFixedAttrs_polyTime_unary`

- Exists: yes, `LatcComplexity/Tractable.lean:1094`
- Reading: The same under `encInst`, by composing with `encInst_to_encInstBin_polyTime`. Not a row of the README's tables; cited by the paper draft.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingCountFixedAttrs_polyTime_unary (k : ℕ) :
    ComputableInPolyTime (fun I : Inst => if I.n ≤ k then missingCount I else 0)
      encInst encNat
```

Axiom lines for these four: the README's audit (build of 2026-10-31, commit `242311b`) lists every
theorem that prints fewer than all three axioms, and none of the four is among them.

## Line counts

Counted with `wc -l` (every line, including blank lines and comments) at `242311b`.

| File | Lines | Theorems/lemmas |
|---|---|---|
| `LatcComplexity/Bridge.lean` | 160 | 16 |
| `LatcComplexity/General.lean` | 205 | 15 |
| `LatcComplexity/Adequacy.lean` | 152 | 13 |
| `LatcComplexity/Counting.lean` | 140 | 10 |
| `LatcComplexity/CountingGeneral.lean` | 262 | 20 |
| `LatcComplexity/Monotone.lean` | 191 | 15 |
| `LatcComplexity/Binary.lean` | 186 | 21 |
| `LatcComplexity/Tractable.lean` | 1099 | 81 |
| `LatcComplexity/Axioms.lean` | 203 | 0 (174 `#print axioms`) |
| **`LatcComplexity/` total** | **2598** | **191** |
| `LatcComplexity/` without `Axioms.lean` | 2395 | 191 |
| `LatcComplexity.lean` (root import file) | 9 | |
| `LatcFormal/Basic.lean` | 114 | |
| `LatcFormal/Thm1.lean` | 130 | |
| `LatcFormal/Prop1.lean` | 287 | |
| `LatcFormal/Prop2.lean` | 85 | |
| `LatcFormal/Prop3.lean` | 95 | |
| `LatcFormal/Prop4.lean` | 160 | |
| `LatcFormal/Prop5Reduction.lean` | 461 | |
| `LatcFormal/Prop6.lean` | 133 | |
| `LatcFormal/Prop7.lean` | 121 | |
| `LatcFormal/Examples.lean` | 96 | |
| `LatcFormal/Axioms.lean` | 95 | |
| **`LatcFormal/` total** (copied unchanged from latc-check) | **1777** | |
| `LatcFormal.lean` (root import file) | 11 | |
| **Repository total, all `.lean` files** | **4395** | |

Paper D's new development is `LatcComplexity/`: 2598 lines, or 2395 without the audit file (1966
and 1809 at `011cd1a`, before the counting result).

## References

How the records were checked. DBLP served a bot-check page, so no DBLP keys or DBLP BibTeX were
obtained. ScienceDirect, SIAM, the ACM DL and SpringerLink also refused automated access. Records
were therefore taken from:

* the DOI registration itself (doi.org content negotiation and the Crossref API, which carry the
  publisher's deposited metadata);
* Dagstuhl DROPS, the AFP, arXiv and Cambridge Core pages;
* repository files, read through raw.githubusercontent.com.

Each BibTeX entry in `docs/paper-refs.bib` holds only verified fields.

| # | Item | Status | Record |
|---|---|---|---|
| 1 | Gäher and Kunze | confirmed | Lennard Gäher, Fabian Kunze. "Mechanising Complexity Theory: The Cook-Levin Theorem in Coq". ITP 2021, LIPIcs 193, 20:1–20:18, 2021. [doi:10.4230/LIPIcs.ITP.2021.20](https://doi.org/10.4230/LIPIcs.ITP.2021.20) (DROPS) |
| 2 | Balbach, AFP | confirmed | Frank J. Balbach. "The Cook-Levin theorem". Archive of Formal Proofs, January 2023 (entry dated 8 January 2023), ISSN 2150-914x. <https://isa-afp.org/entries/Cook_Levin.html> (the AFP's own "Cite" BibTeX) |
| 3 | Gamboa and Cowles | confirmed | Ruben Gamboa, John Cowles. "A Mechanical Proof of the Cook-Levin Theorem". TPHOLs 2004, LNCS 3223, Springer, pp. 99–116, 2004. [doi:10.1007/978-3-540-30142-4_8](https://doi.org/10.1007/978-3-540-30142-4_8). The proof is in ACL2. Crossref and Springer's citation export give everything except the volume number; 3223 comes from the preface of the TPHOLs 2004 emerging-trends report (Utah UUCS-05-004) and from the reference list Springer deposited for a citing paper (doi:10.1007/978-3-540-89439-1_43), not from a Springer page. |
| 4 | Coq Library of Complexity Theory | **not found** (no paper on the library) | The repository README (<https://github.com/uds-psl/coq-library-complexity>) has no CITATION file and no "how to cite" section. Under "Published work" it lists Gäher and Kunze, ITP 2021 (item 1), and Forster, Kunze, Smolka and Wuttke, "A Mechanised Proof of the Time Invariance Thesis for the Weak Call-By-Value λ-Calculus", ITP 2021, LIPIcs 193, 19:1–19:20, [doi:10.4230/LIPIcs.ITP.2021.19](https://doi.org/10.4230/LIPIcs.ITP.2021.19). Cite item 1, or the repository by URL. |
| 5 | Karp21 in Isabelle | **no paper or AFP entry; resolved 2026-10-30** | There is no AFP entry and no paper. The project is now <https://github.com/rosskopfs/poly-reductions> ("Automatic Refinements and Polynomial-Time Reductions in Isabelle/HOL", Isabelle2025), the successor of `wimmers/poly-reductions` and formerly called Karp21. At commit `d741d95`, `Karp21/All_Reductions_Poly.thy` lists polynomial-time reductions from SAT to all 21 of Karp's problems, with three marked "TODO: missing space bound". Running times are accounted for in NREST: the `Karp21` session depends on NREST (`Karp21/ROOT`), and `Karp21/Polynomial_Reductions.thy` defines a polynomial reduction (`ispolyred`) as a program that refines a specification of the reduction function under a time bound `p` applied to the size of the input. SAT's NP-hardness is not part of that tree; the repository's separate `Cook_Levin_IMP` folder is not imported by it. Relation to Paper D: prior machine-checked reductions between Karp's problems in Isabelle/HOL, without a paper to cite; the outline lists it in its Related work table, in the row after descriptive-complexity's Karp results. Its README names no authors. For machine-checked NP-completeness of all 21, cite instead Senellart and Gnatenko (item 11): at commit `fc068f6`, descriptive-complexity has one unconditional theorem `NP.Complete X` per Karp problem (e.g. `knapsack_NP_complete`), with NP defined logically and hardness by first-order reductions from its own Cook–Levin (`SAT_NP_complete`). Neither library was built here. |
| 6 | Carneiro | confirmed | Mario Carneiro. "Formalizing Computability Theory via Partial Recursive Functions". ITP 2019, LIPIcs 141, 12:1–12:17, 2019. [doi:10.4230/LIPIcs.ITP.2019.12](https://doi.org/10.4230/LIPIcs.ITP.2019.12) (DROPS) |
| 7 | Valiant, permanent | confirmed | Leslie G. Valiant. "The complexity of computing the permanent". Theoretical Computer Science 8(2):189–201, 1979. [doi:10.1016/0304-3975(79)90044-6](https://doi.org/10.1016/0304-3975(79)90044-6) |
| 8 | Valiant, enumeration | confirmed | Leslie G. Valiant. "The Complexity of Enumeration and Reliability Problems". SIAM J. Comput. 8(3):410–421, 1979. [doi:10.1137/0208032](https://doi.org/10.1137/0208032) |
| 9 | Provan and Ball | confirmed | J. Scott Provan, Michael O. Ball. "The Complexity of Counting Cuts and of Computing the Probability that a Graph is Connected". SIAM J. Comput. 12(4):777–788, 1983. [doi:10.1137/0212053](https://doi.org/10.1137/0212053) |
| 10 | Cook | confirmed | Stephen A. Cook. "The complexity of theorem-proving procedures". Proceedings of the Third Annual ACM Symposium on Theory of Computing (STOC '71), ACM, pp. 151–158, 1971. [doi:10.1145/800157.805047](https://doi.org/10.1145/800157.805047) |
| 11 | Senellart and Gnatenko | confirmed | Pierre Senellart, Anton Gnatenko. "Descriptive Complexity in Lean: Completeness by First-Order Reductions". arXiv:2609.18261 [cs.LO], v1, 16 September 2026, 25 pages. <https://arxiv.org/abs/2609.18261>. The library's README says: "To cite the library, cite this paper". The software also has its own concept DOI, [10.5281/zenodo.21678423](https://doi.org/10.5281/zenodo.21678423) (v1.4.0, 2026-10-20). The software's `CITATION.cff` lists Senellart as its only author. **Results checked in the code at commit `fc068f6`** (read, not built): (a) Karp's 21 problems, each an unconditional `NP.Complete X` theorem — `SAT_NP_complete`, `zeroOneIP_NP_complete`, `clique_NP_complete`, `setPacking_NP_complete`, `vertexCover_NP_complete`, `setCover_NP_complete`, `feedbackVertexSet_NP_complete`, `feedbackArcSet_NP_complete`, `dirHamCircuit_NP_complete`, `hamCircuit_NP_complete`, `threeSat_NP_complete`, `chromaticNumber_NP_complete`, `cliqueCover_NP_complete`, `exactCover_NP_complete`, `hittingSet_NP_complete`, `steinerTree_NP_complete`, `threeDimMatching_NP_complete`, `knapsack_NP_complete`, `jobSequencing_NP_complete`, `partition_NP_complete`, `maxCut_NP_complete` — with NP defined logically and hardness by first-order reductions from its own Cook–Levin (`SAT_NP_complete`); (b) `DescriptiveComplexity.sharpMonotoneTwoSat_sharpP_oneCallComplete : SharpP.OneCallComplete SharpMonotoneTwoSAT` (`Problems/Sat/CountingRestricted.lean:567`) and `sharpCycleCover_sharpP_oneCallComplete` for the permanent. No `sorry` or `axiom` declaration in its sources. Relation to Paper D: prior machine-checked NP-completeness in Lean, in a logical model rather than complexitylib's Turing machines, so Paper D claims its problem, not the method; and the one-call form of the hypothesis `hValiant`, in another model. |
| 12 | CSLib | confirmed | Clark Barrett, Swarat Chaudhuri, Fabrizio Montesi, Jim Grundy, Pushmeet Kohli, Leonardo de Moura, Alexandre Rademaker, Sorrachai Yingchareonthawornchai. "CSLib: The Lean Computer Science Library". arXiv:2602.04846 [cs.LO], v1, 4 February 2026. <https://arxiv.org/abs/2602.04846> |
| 13 | complexitylib | **resolved 2026-10-30** (no citation file; authorship from the repository) | Samuel Schlesinger and the Complexitylib contributors, *Complexitylib*, Lean 4 library built on CSLib, <https://github.com/cslib-community/complexitylib>, commit `b7acfc2310217697a892e791d318a5e127fadfd9` (28 October 2026). There is no CITATION file at that commit. The Cook–Levin files Paper D uses carry the header "Authors: Samuel Schlesinger", and the README says "Source headers retain authorship". It is version 2, begun 14 October 2026; the README calls it "the canonical CSLib-based Complexitylib". The pre-CSLib version 1, <https://github.com/SamuelSchlesinger/complexitylib-v1>, has a different API. Its `CITATION.cff` (at its last commit, `1d31cd7`, 21 October 2026) gives the authors as "Samuel Schlesinger" and "The Complexitylib contributors". Paper A cites v1 at `1d31cd7` for Cook–Levin in Lean 4, which v1 does contain. Paper D builds on v2, so it cites v2; the two citations differ because the code does. |
| 14 | Calvanese et al. | confirmed | Diego Calvanese, Marlon Dumas, Ülari Laurson, Fabrizio M. Maggi, Marco Montali, Irene Teinemaa. "Semantics and Analysis of DMN Decision Tables". BPM 2016, LNCS 9850, Springer, pp. 217–233, 2016. [doi:10.1007/978-3-319-45348-4_13](https://doi.org/10.1007/978-3-319-45348-4_13). Crossref has no volume number; 9850 is given by a library catalogue and by three citing papers' Springer-deposited reference lists (e.g. doi:10.1007/978-3-030-30429-4_9). The rest is from Crossref. |
| 15 | Arora and Barak | confirmed | Sanjeev Arora, Boaz Barak. *Computational Complexity: A Modern Approach*. Cambridge University Press, 2009. ISBN 978-0-521-42426-4. [doi:10.1017/CBO9780511804090](https://doi.org/10.1017/CBO9780511804090) (Cambridge Core) |

### What Provan and Ball prove, and what Valiant proves

The full texts of the two SIAM papers could not be opened, so no theorem numbers are given. What
follows rests on the abstracts (from Crossref) and on Briquel and Koiran, "A Dichotomy Theorem for
Polynomial Evaluation" (arXiv:0902.2300, Theorem 10, Remark 2 and its proof), which says who proved
what.

* **Provan and Ball (1983)** prove #P-completeness, under polynomial-time oracle (Turing)
  reductions, of counting:
  * vertex covers, and so independent sets, in general graphs and in **bipartite graphs**;
  * antichains and ideals of a partial order;
  * minimum (s,t)-cuts;
  * and computing the probability that a graph is connected.

  The abstract says: "Also shown to be #P-complete are counting vertex covers in a bipartite graph,
  counting antichains in a partial order, …". Counting independent sets in a bipartite graph
  (#BIS) is the same problem, since independent sets are the complements of vertex covers.
* **Provan and Ball do not prove #Monotone-2SAT #P-complete.** Briquel and Koiran credit them only
  with a many-one reduction from #Vertex Cover to Positive 2-SAT. They credit the #P-completeness of
  Positive, Negative and Implicative 2-SAT to **Valiant, SIAM J. Comput. 1979**, under oracle
  reductions.
* **For Paper D:** cite Valiant (SIAM 1979) for #Monotone-2SAT being #P-complete under Turing
  reductions. Cite Provan and Ball for bipartite independent sets / vertex covers (equivalently,
  #Monotone-2SAT on a bipartite variable graph), if the paper needs that problem. The README's
  `hValiant` asks for one-call hardness. That is stronger than the Turing-reduction statement
  either paper proves, which matches the README's remark that the one-call form is
  machine-checked only in Senellart and Gnatenko's model.

### Calvanese et al. (BPM 2016) states no complexity result

The arXiv version (1603.07466) gives a formal semantics and geometric sweep-line algorithms for
overlapping and missing rules, with run-time experiments. It proves no NP-, coNP- or #P-hardness.
Do not cite it for a hardness claim.

## Novelty

**Finding** (as the outline now states it). Hardness of rule-set coverage is known in adjacent
settings:

* firewall completeness (Elmallah and Gouda, item 1);
* quasi-reducibility and pattern completeness (Kapur et al.; Thiemann and Yamada, item 2);
* unions of boxes (Chan; Bringmann and Friedrich, item 3);
* a coNP-completeness claim, without proof, for covered rules in a GE patent (Jolly, item 4).

No source found proves *decision-table* completeness NP-, coNP- or #P-complete. That holds for
DMN, expert-system rule bases and decision tables in Vanthienen's sense, with or without domain
constraints. None of the related hardness results is checked in Lean. Paper D can claim that, but
not the first hardness result for coverage in general.

Against the two closest results, as the outline's contributions paragraph puts it:

* Elmallah and Gouda prove firewall completeness NP-hard, with no membership result.
* Thiemann and Yamada prove pattern completeness co-NP hard and verify their algorithm in
  Isabelle, but their hardness proof is on paper.
* Neither handles domain constraints or counts missing states. Paper D adds both, plus the
  tractable side, with every hardness proof machine-checked in Lean. The tractable side has a
  firewall parallel: Hamilton, Roughan and Nguyen give polynomial-time algorithms when the number
  of fields is fixed (item 1).

Machine-checked NP-completeness in Lean is not itself new, so Paper D's claim is about the
problem, not the method:

* Senellart and Gnatenko's descriptive-complexity (references, item 11) proves all 21 of Karp's
  problems NP-complete in Lean 4: one unconditional `NP.Complete` theorem each, checked at
  commit `fc068f6` (e.g. `knapsack_NP_complete`, `exactCover_NP_complete`). These rest on its
  own Cook–Levin, `SAT_NP_complete`. Its NP is defined logically and its hardness uses
  first-order reductions, not complexitylib's Turing machines.
* The same library proves #Monotone-2SAT and the permanent one-call #P-complete
  (`sharpMonotoneTwoSat_sharpP_oneCallComplete`, `sharpCycleCover_sharpP_oneCallComplete`).
  That is the substance of Paper D's hypothesis `hValiant`, though in another model.
* complexitylib, which Paper D builds on, has Cook–Levin, SAT, 3SAT and #SAT; Paper A cites its
  earlier version for Cook–Levin in Lean 4 (references, item 13).
* In Isabelle/HOL, poly-reductions (formerly Karp21) reduces SAT to all 21 problems, without
  proving SAT NP-hard (references, item 5). In Coq, Gäher and Kunze proved Cook–Levin
  (item 1).

So Paper D is not the first machine-checked NP-completeness proof in Lean, nor the first for a
Karp-style problem. What this search supports is narrower: it is the first machine-checked
complexity result found for decision-table completeness, and it covers counting and a
tractable side, composed with complexitylib's Turing-machine Cook–Levin. Whether other projects
already build on complexitylib was not searched, so the paper should not claim to be the first
to do so.

Two checks remain before submission:

* read Vu and Demetrovics (2026, item 6) in full;
* read the "input completeness" constraints of Levy and Rousset's 1998 journal version (see
  "Works cited by Paper A" below), which the open 1996 version does not contain.

Close prior work:

1. **Firewall completeness: proved, on paper.** Ehab Elmallah and Mohamed Gouda, "Hardness of
   Firewall Analysis", IEEE Transactions on Dependable and Secure Computing 14(3):339–349,
   May–June 2017, [doi:10.1109/TDSC.2015.2455532](https://doi.org/10.1109/TDSC.2015.2455532). This
   is the version to cite.
   * Volume, issue, pages and issue date were read from IEEE Xplore by the author on 2026-10-30 (the
     Xplore page refuses automated access). Crossref holds only the 2015 early-access record (pages
     "1–1"). The values agree with Hamilton, Roughan and Nguyen's citation and with Semantic
     Scholar (volume 14, pages 339–349).
   * Earlier versions: Technical Report TR13-08, University of Alberta, 2013,
     [doi:10.7939/R3H12V84G](https://doi.org/10.7939/R3H12V84G); and *Networked Systems* (NETYS
     2014), LNCS 8593, Springer, pp. 153–168,
     [doi:10.1007/978-3-319-09581-3_11](https://doi.org/10.1007/978-3-319-09581-3_11). Crossref
     gives no LNCS volume number; 8593 is from four citing papers' Springer-deposited reference lists (e.g. doi:10.1007/978-3-319-21741-3_8). The novelty search had missed both published versions.
   * The quotes below are from the 2013 report; the journal's theorem numbering was not checked.
   * They define "A firewall F is called complete iff every packet matches" it, and prove
     "Theorem 5. Problem FC is NP-hard" by reduction from 3-SAT.
   * The setting has packets with d integer-interval fields, rules that are conjunctions of
     intervals, and no constraints. The number of fields is unbounded.
   * They call the problem "NP-hard"; by its form it is coNP-hard. There is no membership proof and
     no counting result.
   * Adam Hamilton, Matthew Roughan and Giang T. Nguyen, "Boolean Expressions in Firewall
     Analysis", arXiv:2205.04210 [cs.CR], v1, 3 May 2022 (no journal reference on arXiv; the
     IEEE TNSM header on the PDF is not a publication record),
     note that the hardness needs an arbitrary number of header fields. With the number of fields
     fixed they give polynomial-time algorithms. This parallels Paper D's fixed-attribute result.
2. **Pattern completeness: proved on paper; an Isabelle-verified algorithm.** René Thiemann and
   Akihisa Yamada, "A verified algorithm for deciding pattern completeness with optimal asymptotic
   complexity", J. Log. Algebraic Methods Program. 151 (2026) 101129,
   [doi:10.1016/j.jlamp.2026.101129](https://doi.org/10.1016/j.jlamp.2026.101129). The conference
   version, under the shorter title "A Verified Algorithm for Deciding Pattern Completeness", is
   FSCD 2024, LIPIcs 299, 27:1–27:17,
   [doi:10.4230/LIPIcs.FSCD.2024.27](https://doi.org/10.4230/LIPIcs.FSCD.2024.27) (confirmed from
   the DOI's DataCite record, which points to Dagstuhl DROPS).
   * "Theorem 9. Deciding pattern completeness is co-NP hard for both TRSs and pattern problems,
     even in the linear case."
   * The reduction turns each CNF clause into a row of true/false/wildcard patterns, so in effect
     it is a reduction to completeness of a limited-entry decision table.
   * The Isabelle formalisation verifies the algorithm. It is the AFP entry
     [`Pattern_Completeness`](https://isa-afp.org/entries/Pattern_Completeness.html), "Verifying a
     Decision Procedure for Pattern Completeness", May 2024 (confirmed on the AFP page), building on
     the entry `Sorted_Terms`. The
     paper says "we did not formally prove that every abstract step can be executed in polynomial
     time", and the hardness proof is on paper.
   * Older related work: Deepak Kapur, Paliath Narendran, Daniel J. Rosenkrantz and Hantao Zhang,
     "Sufficient-completeness, ground-reducibility and their complexity", Acta Informatica
     28(4):311–350, 1991, [doi:10.1007/BF01893885](https://doi.org/10.1007/BF01893885) (record
     from Crossref; full text not read). Thiemann and Yamada cite it for "deciding
     quasi-reducibility is co-NP complete [17]".
3. **Box unions: proved.** Karl Bringmann and Tobias Friedrich, "Approximating the volume of
   unions and intersections of high-dimensional geometric objects", Computational Geometry
   43(6–7):601–610, 2010, [doi:10.1016/j.comgeo.2010.03.004](https://doi.org/10.1016/j.comgeo.2010.03.004)
   (record from Crossref; quotes from arXiv:0809.0835).
   * They quote as known that deciding whether some point lies outside a union of boxes is NP-hard,
     citing Timothy M. Chan, "A (slightly) faster algorithm for Klee's measure problem",
     Computational Geometry 43(3):243–250, 2010,
     [doi:10.1016/j.comgeo.2009.01.007](https://doi.org/10.1016/j.comgeo.2009.01.007) (record from
     Crossref; full text not read).
   * "Theorem 1. KMP is #P-hard", for the volume of a union of boxes, by reduction from #MON-CNF.
     They add: "there is no published result that explicitly states that KMP is #P-hard."
   * This is the geometric analogue of non-emptiness and counting of M(T₀). Calvanese et al. use
     the same geometric reading of decision tables.
4. **A claim without proof.** US Patent 5,592,590, Christopher H. Jolly, assigned to General
   Electric, filed 1 July 1994, granted 7 January 1997, "Method for efficiently detecting covered
   rules in a knowledge base" (front page and column 2 read from the patent scan). It says: "Determining
   whether a rule in a knowledge base is covered, is a Co-NP-complete problem." Here "covered"
   means redundancy of a prioritised rule, not table completeness, and no proof is given.
5. **DMN: upper bounds only.**
   * Calvanese, Dumas, Laurson, Maggi, Montali and Teinemaa, "Semantics, Analysis and
     Simplification of DMN Decision Tables", Information Systems 78:112–125, 2018,
     [doi:10.1016/j.is.2018.01.010](https://doi.org/10.1016/j.is.2018.01.010) (PDF read):
     exponential algorithms, with no completeness hardness.
   * Calvanese, Montali, Dumas and Maggi (Crossref's author order), "Semantic DMN: Formalizing and
     Reasoning About Decisions in the Presence of Background Knowledge", TPLP 19(4):536–573, 2019,
     [doi:10.1017/S1471068418000479](https://doi.org/10.1017/S1471068418000479): reasoning tasks,
     completeness included, are decidable in ExpTime over ALCH(D) knowledge bases. That is an
     upper bound only.
6. **Abstract read; full text not accessible (checked 2026-10-30).** Duc Nghia Vu and Janos
   Demetrovics, "Labeled Null Semantics for Incomplete Decision Tables: Certain, Possible, and
   Conditional Decision Reasoning", Algorithms 19(9):725, published 27 August 2026,
   [doi:10.3390/a19090725](https://doi.org/10.3390/a19090725). The record and abstract come from
   the publisher's Crossref deposit (`api.crossref.org/works/10.3390/a19090725`). The MDPI
   article, HTML and PDF pages all returned HTTP 403 to automated access. OpenAlex
   (`any_repository_has_fulltext: false`) and Semantic Scholar list no copy other than MDPI's.
   * **What the paper is about** (from the abstract). The setting is decision tables whose
     *condition values are incomplete*: missing values are labelled nulls, where equal labels
     denote the same unknown value. A possible world is a valuation of the nulls. On that
     semantics the authors define "certain, possible, and conditional decisions", "develop
     symbolic algorithms that avoid explicit enumeration of possible worlds, analyze their
     computational complexity, and establish precise relationships with rough set
     approximations". Constraints appear as "labeled null identities and constraints" that rule
     out tolerant rules that "cannot match in any admissible possible world". The evaluation is a
     synthetic benchmark (105 instances, up to 500 rules and 32 labelled nulls).
   * **Relation to Paper D.** The problem differs, on the abstract's evidence. The question there
     is which decision a table with unknown entries yields for a given input, across valuations
     of the nulls. Paper D's question is whether the rules of a fully specified table cover every
     state allowed by the domain constraints (completeness, non-emptiness and counting of M(T₀)).
     The abstract mentions no hardness of table completeness, no counting result and no proof
     assistant.
   * **Not verified.** The abstract does not say which complexity bounds the paper proves. An
     earlier search-engine summary claimed coNP-completeness results for certain decisions and
     for being "complete for an input" (some rule matches in every admissible possible world).
     That summary is still unconfirmed. If those results exist, they concern coverage of a single
     input under null valuations, which is a coNP-style universal check close in spirit to Paper
     D's. Paper D should therefore cite this paper as related work on decision tables. Before
     claiming that *no* decision-table hardness result exists, someone with browser or
     institutional access should read its complexity section; it is open access (CC BY).

Not searched directly: Semantic Scholar (rate-limited), DBLP and the ACM DL (bot checks). Coverage
of those indexes rests on general web search.

### Process soundness (added 2026-10-30)

Decision-table completeness also appears inside process models, as "conditional completeness":
some rule can fire from every reachable state where the table is enabled. No hardness result for
it was found.

* Massimiliano de Leoni, Paolo Felli and Marco Montali, "A Holistic Approach for Soundness
  Verification of Decision-Aware Process Models", ER 2018, LNCS 11157, Springer, pp. 219–235,
  [doi:10.1007/978-3-030-00847-5_17](https://doi.org/10.1007/978-3-030-00847-5_17) (Crossref;
  arXiv:1804.02316 read). Soundness of general Data Petri nets is undecidable; they verify a
  decidable class by translation to coloured Petri nets.
* Kimon Batoulis, Stephan Haarmann and Mathias Weske, "Various Notions of Soundness for
  Decision-Aware Business Processes", ER 2017, LNCS 10650, Springer, pp. 403–418,
  [doi:10.1007/978-3-319-69904-2_31](https://doi.org/10.1007/978-3-319-69904-2_31) (Crossref;
  full text not read). The source of conditional completeness, per de Leoni et al.
* Kimon Batoulis and Mathias Weske, "Soundness of Decision-Aware Business Processes", BPM Forum
  2017, LNBIP 297, Springer, pp. 106–124,
  [doi:10.1007/978-3-319-65015-9_7](https://doi.org/10.1007/978-3-319-65015-9_7) (Crossref; full
  text not read).
* Kimon Batoulis and Mathias Weske, "Disambiguation of DMN Decision Tables", BIS 2018, LNBIP 320,
  Springer, pp. 236–249, [doi:10.1007/978-3-319-93931-5_17](https://doi.org/10.1007/978-3-319-93931-5_17)
  (Crossref; full text not read). Paper A cites it for removing overlapping rules; it concerns
  overlap, not completeness.

The three series volumes (LNCS 11157, LNCS 10650, LNBIP 297) are not in Crossref, and Springer's
book pages sit behind a cookie wall. They come from reference lists deposited with Crossref by
Springer: de Leoni et al.'s chapter for 10650 and 297, and three later papers citing it for 11157.

### Works cited by Paper A (added 2026-10-30)

Paper A's draft (the author's Claude Doc, revision 3420) cites 103 works. These 13 bear on Paper
D and were missing from the outline; each record was checked against Crossref, the publisher's
page or the OMG page, and all are in `docs/paper-refs.bib`.

* **Rule-base and decision-table verification:** Suwa, Scott and Shortliffe 1982 (AI Magazine
  3(4)); Nguyen, Perkins, Laffey and Pecora 1987 (AI Magazine 8(2)); Cragun and Steudel 1987
  (IJMMS 26(5)); Preece, Shinghal and Batarekh 1992 (KER 7(2)); Vanthienen, Mues and Aerts 1998
  (DKE 27(3)); Levy and Rousset 1998 (Artificial Intelligence 101).
* **Tabular specifications:** Parnas, Madey and Iglewski 1994 (IEEE TSE 20(12)); Heitmeyer,
  Jeffords and Labaw 1996 (ACM TOSEM 5(3)); Heimdahl and Leveson 1996 (IEEE TSE 22(6)); Owre,
  Rushby and Shankar 1997 (TACAS '97, LNCS 1217), where PVS checks table disjointness and
  coverage as proof obligations, the closest precedent in a proof assistant.
* **DMN and domains:** OMG DMN 1.4 (formal/23-03-01, April 2023); Vandevelde, Aerts and
  Vennekens, cDMN (TPLP 23(3), 2023); Reiter 1980 (JACM 27(2)), domain closure.

Two points for the novelty claim:

* **Levy and Rousset: checked 2026-10-30, not a completeness result.** Read in the AAAI-96
  version, "Verification of Knowledge Bases Based on Containment Checking", pp. 585–590
  (https://aaai.org/Papers/AAAI/1996/AAAI96-087.pdf). A Horn-rule knowledge base is *verified*
  if every set of ground facts that entails the input predicate P_in also entails the output
  predicate P_out (Definition 1). They show this is query containment (Theorem 1). Theorem 2
  (no interpreted predicates): NP-complete if the rules for both predicates are non-recursive;
  doubly exponential time if one side is recursive; undecidable if both are. Theorem 3 (with
  ≤, <, =, ≠): Π₂ᵖ-complete when non-recursive, and when only the input rules are recursive;
  undecidable when the output rules are. This is output correctness on valid inputs. No theorem
  there decides whether the rules cover every valid input, so it does not anticipate Paper D's
  result. It is the earliest complexity analysis of rule-base verification and should be cited
  as such. The 1998 journal version was not read; a search summary says it adds "input
  completeness" constraints, which should be checked before submission.
* Paper A also states that with compact rules, as in DMN, "deciding whether the rules cover 𝒟 is
  the tautology problem for formulas in disjunctive normal form, coNP-complete", citing Cook.
  Paper D's tractable side (no constraints, in P) is about explicit condition tuples, not compact
  rules, so the two agree. Paper D should say so, or a reader may see a contradiction.
