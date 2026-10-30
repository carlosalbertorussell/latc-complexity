# Paper D: fact check of theorem names and references

Checked 2026-10-29 against commit `011cd1a` of latc-complexity, for Paper D, "Machine-Checked
Complexity of Decision-Table Completeness in Lean" (ITP 2027). No Lean file was changed.

## Summary

* **Theorems: 48/48 found.** These are the 48 rows of the README's theorem tables (46 names;
  `MissingNonempty_npComplete` and `Complete_coNPComplete` each appear twice, once for Boolean domains in
  `Latc.PaperD` and once for general domains in `Latc.PaperD.General`). They include all 22
  theorems the outline names: its 19 explicit names, plus the 3 main theorems of `Adequacy.lean`.
* **Wrong names in the outline: none.** Every name it cites exists exactly as written. Four
  cautions follow in the next section.
* **References: 12/15 confirmed.** Three are not found as asked: the Coq Library of Complexity
  Theory has no paper of its own, Karp21 has no Isabelle paper or AFP entry, and complexitylib
  states no preferred citation. BibTeX is in `docs/paper-refs.bib`.
* **Novelty:** the search found no paper or formalisation that proves *decision-table* completeness
  NP-, coNP- or #P-complete. It did find close prior hardness results that the paper should cite:
  firewall completeness (Elmallah and Gouda), pattern completeness (Thiemann and Yamada) and
  box-union coverage (Chan; Bringmann and Friedrich). Vu and Demetrovics (Algorithms, 2026)
  study per-input decisions in decision tables with labelled nulls. Their abstract mentions a
  complexity analysis, but their full text could not be accessed (see Novelty, item 6).
* **Axiom audit:** the axiom lines below are copied from the audit recorded in the README (build of
  2026-10-29, `LatcComplexity/Axioms.lean`). The audit was **not re-run** in this session: the
  sandbox refused to install the Lean toolchain. A whole-word search of every `.lean` file for
  `sorry`, `admit`, `native_decide` and `axiom` was re-run and finds them only in `#print axioms`
  commands.

## Outline names: check and cautions

All 19 explicit names exist, at the file and line given below. "The main theorems of
`Adequacy.lean`" is not a Lean name. Read it as `mem_MissingNonempty_iff`, `mem_Complete_iff`
and `coe_missing_map_toList`; the outline already lists the two `_finset_` theorems separately.

| Outline name | Full name | File:line | Status |
|---|---|---|---|
| `holdsAll_eq_eval` | `Latc.PaperD.holdsAll_eq_eval` | `LatcComplexity/Bridge.lean:29` | exists, exact name |
| `satisfiable_decode_iff` | `Latc.PaperD.satisfiable_decode_iff` | `LatcComplexity/Bridge.lean:35` | exists, exact name |
| `encInst_to_encInstBin_polyTime` | `Latc.PaperD.General.encInst_to_encInstBin_polyTime` | `LatcComplexity/Binary.lean:31` | exists, exact name |
| (main theorem of `Adequacy.lean`) | `Latc.PaperD.General.mem_MissingNonempty_iff` | `LatcComplexity/Adequacy.lean:101` | exists, exact name |
| (main theorem of `Adequacy.lean`) | `Latc.PaperD.General.mem_Complete_iff` | `LatcComplexity/Adequacy.lean:113` | exists, exact name |
| (main theorem of `Adequacy.lean`) | `Latc.PaperD.General.coe_missing_map_toList` | `LatcComplexity/Adequacy.lean:119` | exists, exact name |
| `MissingNonempty_npComplete_bin` | `Latc.PaperD.General.MissingNonempty_npComplete_bin` | `LatcComplexity/Binary.lean:103` | exists, exact name |
| `Complete_coNPComplete_bin` | `Latc.PaperD.General.Complete_coNPComplete_bin` | `LatcComplexity/Binary.lean:107` | exists, exact name |
| `missingNonempty_finset_npComplete` | `Latc.PaperD.General.missingNonempty_finset_npComplete` | `LatcComplexity/Adequacy.lean:136` | exists, exact name |
| `complete_finset_coNPComplete` | `Latc.PaperD.General.complete_finset_coNPComplete` | `LatcComplexity/Adequacy.lean:145` | exists, exact name |
| `missingCount_sharpPComplete_bin` | `Latc.PaperD.General.missingCount_sharpPComplete_bin` | `LatcComplexity/Binary.lean:161` | exists, exact name |
| `countMissing_eq_sharpSAT` | `Latc.PaperD.countMissing_eq_sharpSAT` | `LatcComplexity/Counting.lean:104` | exists, exact name |
| `countValidMonotone2_mem_SharpP` | `Latc.PaperD.General.countValidMonotone2_mem_SharpP` | `LatcComplexity/Monotone.lean:177` | exists, exact name |
| `sharpMonotone2SAT_reduces` | `Latc.PaperD.General.sharpMonotone2SAT_reduces` | `LatcComplexity/Monotone.lean:170` | exists, exact name |
| `countValidMonotone2_oneCallSharpPComplete` | `Latc.PaperD.General.countValidMonotone2_oneCallSharpPComplete` | `LatcComplexity/Monotone.lean:186` | exists, exact name |
| `completeNoConstraints_mem_P` | `Latc.PaperD.General.completeNoConstraints_mem_P` | `LatcComplexity/Tractable.lean:184` | exists, exact name |
| `missingNonemptyNoConstraints_mem_P` | `Latc.PaperD.General.missingNonemptyNoConstraints_mem_P` | `LatcComplexity/Tractable.lean:196` | exists, exact name |
| `missingCountNoConstraints_polyTime` | `Latc.PaperD.General.missingCountNoConstraints_polyTime` | `LatcComplexity/Tractable.lean:153` | exists, exact name |
| `missingCount_eq_of_noConstraints` | `Latc.PaperD.General.missingCount_eq_of_noConstraints` | `LatcComplexity/Tractable.lean:91` | exists, exact name |
| `completeFixedAttrs_mem_P` | `Latc.PaperD.General.completeFixedAttrs_mem_P` | `LatcComplexity/Tractable.lean:468` | exists, exact name |
| `missingNonemptyFixedAttrs_mem_P` | `Latc.PaperD.General.missingNonemptyFixedAttrs_mem_P` | `LatcComplexity/Tractable.lean:456` | exists, exact name |
| `length_candidateStates_le` | `Latc.PaperD.General.length_candidateStates_le` | `LatcComplexity/Tractable.lean:281` | exists, exact name |

Cautions. None of these is a wrong name.

1. **Namespaces.** `MissingNonempty_npComplete`, `Complete_coNPComplete`, `MissingNonempty_mem_NP`,
   `SAT_reduces` and `fromSAT_polyTime` exist both in `Latc.PaperD` (Boolean domains, `Bridge.lean`)
   and in `Latc.PaperD.General` (general domains, `General.lean`). These are different theorems
   about different `Inst` types. If the paper cites one of them, give the namespace.
2. **`countMissing_eq_sharpSAT` is about Boolean domains** (`Latc.PaperD`, `Counting.lean`). It is
   stated for `countMissing` on a CNF with bit-vector rows, not for `missingCount` over general
   domains. The general-domain #P results are `missingCount_eq_acceptCount`,
   `sharpSAT_eq_missingCount` and `missingCount_sharpPComplete(_bin)`. If §5 means general domains,
   cite those, or say that this lemma is the Boolean case.
3. **The outline mixes encodings.** It cites `missingNonempty_finset_npComplete` and
   `complete_finset_coNPComplete`, which use the unary attribute index `encInst`, next to
   `MissingNonempty_npComplete_bin` and `Complete_coNPComplete_bin`, which use the all-binary
   `encInstBin`. The `encInstBin` versions of the first two also exist
   (`missingNonempty_finset_npComplete_bin`, `complete_finset_coNPComplete_bin`). The tractable
   theorems are stated for `encInstBin`; their `encInst` versions carry the suffix `_unary`.
4. **`countValidMonotone2_oneCallSharpPComplete` is conditional.** Valiant's theorem is its
   hypothesis `hValiant`, not an axiom, so it does not appear in the axiom audit. Hardness is under
   one-call reductions, defined in `Monotone.lean`, and is not Complexitylib's parsimonious
   `SharpPHard`.

A side note on the audit file: it prints 130 of the 147 `theorem`/`lemma` declarations in
`LatcComplexity/`. The other 17 are helper lemmas: `Inst.getElem?_toList`, `Inst.length_toList`,
`assignment_pad`, `condHoldsB_polyTime`, `encList_polyTime`, `fromSAT_get`, `fromSAT_n`,
`getElem?_toList_boolTuple`, `length_certWord`, `length_domains_le`, `length_encCNF_le`,
`length_tuple`, `lookup_polyTime`, `mem_vars_denseRelabel_iff`, `ofFn_certFun`, `ofFn_getD` and
`pos2B_emptyClauseInst`. The README says the file covers "every theorem", which is not literally
true. All 48 theorems below are printed.

## Theorems by paper section

For each theorem below: the full name; whether it exists and where (`(outline)` marks a name the
outline cites); a one-sentence reading; its axiom line; and the Lean statement, copied verbatim
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

#### `Latc.PaperD.General.missingNonempty_finset_npComplete` (outline)

- Exists: yes, `LatcComplexity/Adequacy.lean:136`
- Reading: Stated directly on latc-check's `Latc.missing`: deciding whether the missing set of the denoted table is non-empty is NP-complete under `encInst`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingNonempty_finset_npComplete :
    NPComplete encInst {I : Inst | (missing I.con I.table).Nonempty}
```

#### `Latc.PaperD.General.complete_finset_coNPComplete` (outline)

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

#### `Latc.PaperD.General.missingNonempty_finset_npComplete_bin`

- Exists: yes, `LatcComplexity/Binary.lean:111`
- Reading: The `Latc.missing` form of NP-completeness of non-emptiness, under `encInstBin`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingNonempty_finset_npComplete_bin :
    NPComplete encInstBin {I : Inst | (missing I.con I.table).Nonempty}
```

#### `Latc.PaperD.General.complete_finset_coNPComplete_bin`

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

#### `Latc.PaperD.General.missingCount_eq_acceptCount`

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

#### `Latc.PaperD.General.sharpSAT_eq_missingCount`

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

#### `Latc.PaperD.General.countValidMonotone2_mem_SharpP` (outline)

- Exists: yes, `LatcComplexity/Monotone.lean:177`
- Reading: Unconditionally, counting valid states of monotone two-condition tables is in #P.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem countValidMonotone2_mem_SharpP : countValidMonotone2 ∈ SharpP encInst
```

#### `Latc.PaperD.General.countValidMonotone2_oneCallSharpPComplete` (outline)

- Exists: yes, `LatcComplexity/Monotone.lean:186`
- Reading: Assuming Valiant's theorem in the form that #Monotone-2SAT is #P-hard under one-call reductions, counting valid states of monotone two-condition tables is #P-complete under one-call reductions.
- Axioms: `[propext, Classical.choice, Quot.sound]` (Valiant's theorem enters as the explicit hypothesis `hValiant`, not as an axiom)

```lean
theorem countValidMonotone2_oneCallSharpPComplete
    (hValiant : OneCallSharpPHard encCNF SharpMonotone2SAT) :
    OneCallSharpPComplete encInst countValidMonotone2
```

#### `Latc.PaperD.General.countValidMonotone2_oneCallSharpPComplete_bin`

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

- Exists: yes, `LatcComplexity/Tractable.lean:91`
- Reading: Without constraints, |M(T₀)| equals the product of the domain sizes minus the number of distinct rows of T₀ inside the declared domains.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingCount_eq_of_noConstraints (I : Inst) (h : I.2.1 = []) :
    missingCount I = domProd I - distinctRows I
```

#### `Latc.PaperD.General.missingCountNoConstraints_polyTime` (outline)

- Exists: yes, `LatcComplexity/Tractable.lean:153`
- Reading: Without constraints, |M(T₀)| is computable exactly in polynomial time under `encInstBin` (the function is zero on instances with constraints).
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingCountNoConstraints_polyTime :
    ComputableInPolyTime (fun I : Inst => if I.2.1 = [] then missingCount I else 0)
      encInstBin encNat
```

#### `Latc.PaperD.General.completeNoConstraints_mem_P` (outline)

- Exists: yes, `LatcComplexity/Tractable.lean:184`
- Reading: Deciding completeness of tables without constraints is in P, for any number of attributes and binary domain sizes.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem completeNoConstraints_mem_P :
    {I : Inst | I.2.1 = [] ∧ missing I.con I.table = ∅} ∈ P encInstBin
```

#### `Latc.PaperD.General.missingNonemptyNoConstraints_mem_P` (outline)

- Exists: yes, `LatcComplexity/Tractable.lean:196`
- Reading: Deciding non-emptiness of the missing set for tables without constraints is in P.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingNonemptyNoConstraints_mem_P :
    {I : Inst | I.2.1 = [] ∧ (missing I.con I.table).Nonempty} ∈ P encInstBin
```

#### `Latc.PaperD.General.length_candidateStates_le` (outline)

- Exists: yes, `LatcComplexity/Tractable.lean:281`
- Reading: With `N` the number of values written in the instance, at most (2N + 1)ᵏ candidate states are searched for `k` attributes.
- Axioms: `[propext, Quot.sound]`

```lean
theorem length_candidateStates_le (k : ℕ) (I : Inst) :
    (candidateStates k I).length ≤ (2 * I.numVals + 1) ^ k
```

#### `Latc.PaperD.General.candidateStates_polyTime`

- Exists: yes, `LatcComplexity/Tractable.lean:347`
- Reading: For each fixed `k`, the list of candidate states is computable in polynomial time under `encInstBin`.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem candidateStates_polyTime (k : ℕ) :
    ComputableTidilyInPolyTime (candidateStates k) encInstBin (encList (encList encNat))
```

#### `Latc.PaperD.General.exists_missing_candidate_iff`

- Exists: yes, `LatcComplexity/Tractable.lean:387`
- Reading: With at most `k` attributes, a missing state exists iff some candidate state (values among 0..N and the written values) passes the check.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem exists_missing_candidate_iff {k : ℕ} {I : Inst} (hk : I.n ≤ k) :
    I ∈ MissingNonempty ↔ ∃ s ∈ candidateStates k I, check (I, s) = true
```

#### `Latc.PaperD.General.missingNonemptyFixedAttrs_mem_P` (outline)

- Exists: yes, `LatcComplexity/Tractable.lean:456`
- Reading: For each fixed `k`, deciding non-emptiness of the missing set for tables with at most `k` attributes (any clause constraints, binary domain sizes) is in P.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem missingNonemptyFixedAttrs_mem_P (k : ℕ) :
    {I : Inst | I.n ≤ k ∧ (missing I.con I.table).Nonempty} ∈ P encInstBin
```

#### `Latc.PaperD.General.completeFixedAttrs_mem_P` (outline)

- Exists: yes, `LatcComplexity/Tractable.lean:468`
- Reading: For each fixed `k`, deciding completeness of tables with at most `k` attributes is in P.
- Axioms: `[propext, Classical.choice, Quot.sound]`

```lean
theorem completeFixedAttrs_mem_P (k : ℕ) :
    {I : Inst | I.n ≤ k ∧ missing I.con I.table = ∅} ∈ P encInstBin
```

## Line counts

Counted with `wc -l` (every line, including blank lines and comments) at `011cd1a`.

| File | Lines | Theorems/lemmas |
|---|---|---|
| `LatcComplexity/Bridge.lean` | 160 | 16 |
| `LatcComplexity/General.lean` | 205 | 15 |
| `LatcComplexity/Adequacy.lean` | 152 | 13 |
| `LatcComplexity/Counting.lean` | 140 | 10 |
| `LatcComplexity/CountingGeneral.lean` | 262 | 20 |
| `LatcComplexity/Monotone.lean` | 191 | 15 |
| `LatcComplexity/Binary.lean` | 186 | 21 |
| `LatcComplexity/Tractable.lean` | 513 | 37 |
| `LatcComplexity/Axioms.lean` | 157 | 0 (130 `#print axioms`) |
| **`LatcComplexity/` total** | **1966** | **147** |
| `LatcComplexity/` without `Axioms.lean` | 1809 | 147 |
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
| **`LatcFormal/` total** (copied unchanged from latc-check) | **1786** | |
| `LatcFormal.lean` (root import file) | 11 | |
| **Repository total, all `.lean` files** | **3763** | |

Paper D's new development is `LatcComplexity/`: 1966 lines, or 1809 without the audit file.

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
| 3 | Gamboa and Cowles | confirmed | Ruben Gamboa, John Cowles. "A Mechanical Proof of the Cook-Levin Theorem". TPHOLs 2004, LNCS 3223, Springer, pp. 99–116, 2004. [doi:10.1007/978-3-540-30142-4_8](https://doi.org/10.1007/978-3-540-30142-4_8). The proof is in ACL2. Crossref and Springer's citation export give everything except the volume number; 3223 comes from the preface of the TPHOLs 2004 emerging-trends report (Utah UUCS-05-004), not from a Springer page. |
| 4 | Coq Library of Complexity Theory | **not found** (no paper on the library) | The repository README (<https://github.com/uds-psl/coq-library-complexity>) has no CITATION file and no "how to cite" section. Under "Published work" it lists Gäher and Kunze, ITP 2021 (item 1), and Forster, Kunze, Smolka and Wuttke, "A Mechanised Proof of the Time Invariance Thesis for the Weak Call-By-Value λ-Calculus", ITP 2021, LIPIcs 193, 19:1–19:20, [doi:10.4230/LIPIcs.ITP.2021.19](https://doi.org/10.4230/LIPIcs.ITP.2021.19). Cite item 1, or the repository by URL. |
| 5 | Karp21 in Isabelle | **not found** (no paper or AFP entry) | `isa-afp.org/entries/Karp21.html` returns 404, and no AFP entry covers Karp's 21 problems. What exists is a repository, <https://github.com/wimmers/poly-reductions> ("Polynomial-Time Reductions in Isabelle/HOL", Isabelle2021, with a `Karp21/` folder and some of the 21 reductions). Its README names neither authors nor a paper. A successor, `rosskopfs/poly-reductions`, also has no published paper that could be found. If cited, cite it as a repository; do not attribute authors. |
| 6 | Carneiro | confirmed | Mario Carneiro. "Formalizing Computability Theory via Partial Recursive Functions". ITP 2019, LIPIcs 141, 12:1–12:17, 2019. [doi:10.4230/LIPIcs.ITP.2019.12](https://doi.org/10.4230/LIPIcs.ITP.2019.12) (DROPS) |
| 7 | Valiant, permanent | confirmed | Leslie G. Valiant. "The complexity of computing the permanent". Theoretical Computer Science 8(2):189–201, 1979. [doi:10.1016/0304-3975(79)90044-6](https://doi.org/10.1016/0304-3975(79)90044-6) |
| 8 | Valiant, enumeration | confirmed | Leslie G. Valiant. "The Complexity of Enumeration and Reliability Problems". SIAM J. Comput. 8(3):410–421, 1979. [doi:10.1137/0208032](https://doi.org/10.1137/0208032) |
| 9 | Provan and Ball | confirmed | J. Scott Provan, Michael O. Ball. "The Complexity of Counting Cuts and of Computing the Probability that a Graph is Connected". SIAM J. Comput. 12(4):777–788, 1983. [doi:10.1137/0212053](https://doi.org/10.1137/0212053) |
| 10 | Cook | confirmed | Stephen A. Cook. "The complexity of theorem-proving procedures". Proceedings of the Third Annual ACM Symposium on Theory of Computing (STOC '71), ACM, pp. 151–158, 1971. [doi:10.1145/800157.805047](https://doi.org/10.1145/800157.805047) |
| 11 | Senellart and Gnatenko | confirmed | Pierre Senellart, Anton Gnatenko. "Descriptive Complexity in Lean: Completeness by First-Order Reductions". arXiv:2609.18261 [cs.LO], v1, 16 September 2026, 25 pages. <https://arxiv.org/abs/2609.18261>. The library's README says: "To cite the library, cite this paper". The software also has its own concept DOI, [10.5281/zenodo.21678423](https://doi.org/10.5281/zenodo.21678423) (v1.4.0, 2026-10-20). |
| 12 | CSLib | confirmed | Clark Barrett, Swarat Chaudhuri, Fabrizio Montesi, Jim Grundy, Pushmeet Kohli, Leonardo de Moura, Alexandre Rademaker, Sorrachai Yingchareonthawornchai. "CSLib: The Lean Computer Science Library". arXiv:2602.04846 [cs.LO], v1, 4 February 2026. <https://arxiv.org/abs/2602.04846> |
| 13 | complexitylib | **not found** (no preferred citation) | The README of <https://github.com/cslib-community/complexitylib> contains no citation text, and `CITATION.cff`, `CITATION.bib` and `CITATION` all return 404. No authors could be verified. Cite it as software, by URL and the pinned commit `b7acfc2310217697a892e791d318a5e127fadfd9`. |
| 14 | Calvanese et al. | confirmed | Diego Calvanese, Marlon Dumas, Ülari Laurson, Fabrizio M. Maggi, Marco Montali, Irene Teinemaa. "Semantics and Analysis of DMN Decision Tables". BPM 2016, LNCS 9850, Springer, pp. 217–233, 2016. [doi:10.1007/978-3-319-45348-4_13](https://doi.org/10.1007/978-3-319-45348-4_13). The volume number comes from a library catalogue (Crossref has none); the rest is from Crossref. |
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

**Finding.** No paper or formalisation was found that proves completeness of decision tables
NP-, coNP- or #P-complete or -hard. This covers DMN, expert-system rule bases and decision tables
in Vanthienen's sense, with or without domain constraints. No Lean formalisation of any related
hardness result was found either. Prior work does prove the same kind of hardness for very close
problems, and Paper D should cite it. On this evidence:

* coNP-hardness of *unconstrained* table completeness is close to known results (items 1 and 2
  below);
* still new are:
  * the constrained version stated for decision tables;
  * #P-completeness of counting missing states;
  * the tractable side, which is no constraints, or a fixed number of attributes (item 1's
    follow-up has a similar fixed-field result for firewalls);
  * the machine checking.

Close prior work:

1. **Firewall completeness: proved, on paper.** Ehab S. Elmallah and Mohamed G. Gouda, "Hardness
   of Firewall Analysis", Technical Report TR13-08, University of Alberta, 2013,
   [doi:10.7939/R3H12V84G](https://doi.org/10.7939/R3H12V84G).
   * They define "A firewall F is called complete iff every packet matches" it, and prove
     "Theorem 5. Problem FC is NP-hard" by reduction from 3-SAT.
   * The setting has packets with d integer-interval fields, rules that are conjunctions of
     intervals, and no constraints. The number of fields is unbounded.
   * They call the problem "NP-hard"; by its form it is coNP-hard. There is no membership proof and
     no counting result.
   * A journal version in IEEE TDSC 14(3):339–349, 2017 is cited by Hamilton, Roughan and Nguyen,
     but was not verified on the publisher's page.
   * Adam Hamilton, Matthew Roughan and Giang T. Nguyen, "Boolean Expressions in Firewall
     Analysis", arXiv:2205.04210 [cs.CR], v1, 3 May 2022 (no journal reference on arXiv; the
     IEEE TNSM header on the PDF is not a publication record),
     note that the hardness needs an arbitrary number of header fields. With the number of fields
     fixed they give polynomial-time algorithms. This parallels Paper D's fixed-attribute result.
2. **Pattern completeness: proved on paper; an Isabelle-verified algorithm.** René Thiemann and
   Akihisa Yamada, "A verified algorithm for deciding pattern completeness with optimal asymptotic
   complexity", J. Log. Algebraic Methods Program. 151 (2026) 101129,
   [doi:10.1016/j.jlamp.2026.101129](https://doi.org/10.1016/j.jlamp.2026.101129). The conference
   version is FSCD 2024, LIPIcs 299, 27:1–27:17,
   [doi:10.4230/LIPIcs.FSCD.2024.27](https://doi.org/10.4230/LIPIcs.FSCD.2024.27).
   * "Theorem 9. Deciding pattern completeness is co-NP hard for both TRSs and pattern problems,
     even in the linear case."
   * The reduction turns each CNF clause into a row of true/false/wildcard patterns, so in effect
     it is a reduction to completeness of a limited-entry decision table.
   * The Isabelle formalisation (AFP entry `Pattern_Completeness`) verifies the algorithm. The
     paper says "we did not formally prove that every abstract step can be executed in polynomial
     time", and the hardness proof is on paper.
   * Older related work: Kapur, Narendran, Rosenkrantz and Zhang (Acta Informatica 1991) show
     sufficient completeness co-NP-complete for left-linear systems. This was seen only in search
     snippets.
3. **Box unions: proved.** Karl Bringmann and Tobias Friedrich, "Approximating the volume of
   unions and intersections of high-dimensional geometric objects", Computational Geometry 43
   (2010) (arXiv:0809.0835).
   * They quote as known that deciding whether some point lies outside a union of boxes is NP-hard
     (citing Chan).
   * "Theorem 1. KMP is #P-hard", for the volume of a union of boxes, by reduction from #MON-CNF.
     They add: "there is no published result that explicitly states that KMP is #P-hard."
   * This is the geometric analogue of non-emptiness and counting of M(T₀). Calvanese et al. use
     the same geometric reading of decision tables.
4. **A claim without proof.** US Patent 5,592,590 (C. H. Jolly, General Electric, 1997),
   "Method for efficiently detecting covered rules in a knowledge base". It says: "Determining
   whether a rule in a knowledge base is covered, is a Co-NP-complete problem." Here "covered"
   means redundancy of a prioritised rule, not table completeness, and no proof is given.
5. **DMN: upper bounds only.**
   * Calvanese et al., Information Systems 2018: exponential algorithms, with no completeness
     hardness.
   * Calvanese, Dumas, Maggi and Montali, "Semantic DMN", TPLP 19 (2019),
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
