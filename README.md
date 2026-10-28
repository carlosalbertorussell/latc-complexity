# latc-complexity

Proposition 5 of Paper A (the LATC re-examination, "Where Declared Domains Are Lost"),
composed with the Cook–Levin theorems of
[Complexitylib](https://github.com/cslib-community/complexitylib) and machine-checked end to end in
Lean 4. Completeness of a decision table whose constraints are clauses is coNP-complete, and
non-emptiness of its missing set M(T₀) is NP-complete, for general finite domains. These are
theorems about Turing machines with explicit encodings and polynomial-time bounds, not citations.

## Versions

| Component | Version (pinned in) |
|---|---|
| Lean | `leanprover/lean4:v4.36.0-rc1` (`lean-toolchain`) |
| Complexitylib | commit `b7acfc2310217697a892e791d318a5e127fadfd9` (`lakefile.toml`, `lake-manifest.json`) |
| CSLib | commit `f4a472560f78c59bbedd795fe041ec507f7d0582` (through Complexitylib) |
| Mathlib | commit `625d8914199bc567cca9b91f90e8e5afafa5ae51`, tag `v4.36.0-rc1` (through CSLib) |
| Paper A formalisation | `LatcFormal/`, copied unchanged from latc-check commit `b9f8273` (folder `formal/`) |

The Lean toolchain must equal Complexitylib's at the pinned commit; bump the two together.

## Build

Install [elan](https://github.com/leanprover/elan), then run from this folder:

```bash
lake exe cache get
```

```bash
lake build
```

`lake exe cache get` downloads the precompiled Mathlib. CSLib and the Complexitylib modules that
are imported are then compiled from source, which takes a while on the first build.

Verification status (2026-10-28, Linux cloud machine, x86_64, 4 cores): Lean 4.36.0-rc1 (commit
`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`, Lake 5.0.0), with the dependencies above,
`lake build` ended with `Build completed successfully (18613 jobs)` and exit code 0, with no
warnings and no errors. The 20 modules of this repository (`LatcFormal`, its 11 files,
`LatcComplexity`, `Bridge`, `General`, `Adequacy`, `Counting`, `CountingGeneral`, `Monotone` and
`Axioms`)
were compiled; the other jobs were the dependencies, whose build outputs came from a checkout of
the same commits built earlier on the same machine (Mathlib from `lake exe cache get`, CSLib and
Complexitylib compiled there).

Cold build (2026-10-28, same machine type, commit `a2ab2f8`, fresh clone, no `~/.elan`, `.lake` or
Mathlib cache): elan install 1 s; `lake exe cache get` 160 s, including the toolchain download (all
9047 Mathlib files came from the cache); `lake build` 241 s, `Build completed successfully (18603
jobs)`, no warnings, no errors, compiling from source 27 CSLib, 200 Complexitylib and the 18
repository modules. About 7 minutes in all; 12 GB of disk (the repository with `.lake`, `~/.elan`
with Lake's artifact cache, and `~/.cache/mathlib`). Its axiom audit agreed with the one below on
the 46 theorems audited at that commit.

## Layout

| Library | Contents |
|---|---|
| `LatcFormal` | Theorem 1, Corollaries 1, 3, 4, Propositions 1–4, 6, 7, and the combinatorial reduction behind Proposition 5, unchanged from latc-check (documented in latc-check's `formal/README.md`) |
| `LatcComplexity.Bridge` | Boolean domains: our clause constraints are Complexitylib CNF formulas; NP-/coNP-completeness and #P-hardness |
| `LatcComplexity.General` | General finite domains: NP-/coNP-completeness |
| `LatcComplexity.Adequacy` | The word-encoded problems are latc-check's `Latc.missing` on the tables they denote |
| `LatcComplexity.Counting` | Boolean domains: counting \|M(T₀)\| is in #P, hence #P-complete |
| `LatcComplexity.CountingGeneral` | General finite domains: counting \|M(T₀)\| of latc-check's model is #P-complete |
| `LatcComplexity.Monotone` | Clauses of two conditions Aᵢ = 1, Aⱼ = 1: counting \|𝒱\| is in #P and, assuming Valiant's theorem as a hypothesis, one-call #P-complete |
| `LatcComplexity.Axioms` | `#print axioms` on every theorem of the two files above |

## Theorems

Classes, reductions and encodings are Complexitylib's (`Cslib.Complexity.NP`, `coNP`,
`PolyTimeReducible`, `NPComplete`, `coNPComplete`, `SharpPHard`; Turing machines with a binary
alphabet; `ComputableInPolyTime`). Hardness comes from Complexitylib's `CookLevin.SAT_npHard`,
`CookLevin.UNSAT_coNPComplete` and the parsimonious `CookLevin.SharpSAT_sharpPHard`.

### General finite domains (`LatcComplexity/General.lean`, namespace `Latc.PaperD.General`)

An instance is `(d, S, T)`: the domain sizes `d = [|D₀|, …, |Dₙ₋₁|]` (attribute `i` takes the values
`0, …, dᵢ − 1`), the clause constraints `S` (each clause a list of conditions `(i, v)`, read
Aᵢ = v), and the condition tuples `T` of T₀. A state is a list `s` with `s.length = n` and
`sᵢ < dᵢ`. Numbers are encoded in binary, except the attribute index `i` of a condition, which is
unary: it names a position among the declared attributes, and Complexitylib reads list positions
in unary.

| Theorem | Statement |
|---|---|
| `MissingNonempty_npComplete` | `NPComplete encInst MissingNonempty`: deciding M(T₀) ≠ ∅ is NP-complete |
| `Complete_coNPComplete` | `coNPComplete encInst Complete`: deciding M(T₀) = ∅ is coNP-complete |
| `MissingNonempty_mem_NP` | membership: the missing state is the witness, and its encoding is no longer than the encoded domain sizes (`length_encList_le_of_inDomains`) |
| `check_polyTime` | the certificate check is polynomial-time |
| `SAT_reduces` | SAT reduces to M(T₀) ≠ ∅: variables renumbered densely (`CNF.denseRelabel`), domains {0, 1}, T₀ = ∅ |
| `fromSAT_polyTime` | the reduction is polynomial-time |
| `satisfiable_iff` | a formula over variables `< n` is satisfiable iff its conditions have a valid state over `n` attributes with domain {0, 1} |

### Adequacy to latc-check's model (`LatcComplexity/Adequacy.lean`, namespace `Latc.PaperD.General`)

An instance `I = (d, S, T)` denotes a table in the model of `LatcFormal/Basic.lean`: attributes
`Fin n` with declared domains `Fin dᵢ`; the constraint predicate `I.con`, under which a tuple
satisfies every clause of `S` and a condition `(i, v)` holds when attribute `i` exists and takes the
value `v` (`con_cond_iff`, `con_iff`); and the condition set `I.table`, the tuples whose list of
values is a row of `T` (rows of another length or with values outside the domains denote no
tuple).

| Theorem | Statement |
|---|---|
| `mem_MissingNonempty_iff` | `I ∈ MissingNonempty ↔ (Latc.missing I.con I.table).Nonempty` |
| `mem_Complete_iff` | `I ∈ Complete ↔ Latc.missing I.con I.table = ∅` |
| `coe_missing_map_toList` | the tuples of M(T₀), as lists of values (injectively, `Inst.toList_injective`), are exactly the witnesses of `MissingNonempty` |
| `missingNonempty_finset_npComplete` | `NPComplete encInst {I \| (Latc.missing I.con I.table).Nonempty}` |
| `complete_finset_coNPComplete` | `coNPComplete encInst {I \| Latc.missing I.con I.table = ∅}` |

### Boolean domains (`LatcComplexity/Bridge.lean`, namespace `Latc.PaperD`)

An instance is a pair of a Complexitylib `CNF ℕ` (a condition Aᵢ = v is the literal `(i, v)`) and
the condition tuples of T₀ as bit vectors over the distinct attributes of the constraints.

| Theorem | Statement |
|---|---|
| `holdsAll_eq_eval`, `satisfiable_decode_iff` | latc-check's `Latc.Prop5` clause constraints and satisfiability agree with Complexitylib's |
| `MissingNonempty_npComplete` | `NPComplete encInst MissingNonempty` |
| `Complete_coNPComplete` | `coNPComplete encInst Complete` |
| `countMissing_sharpPHard` | `SharpPHard encInst countMissing`: counting \|M(T₀)\| (and \|𝒱\|, with T₀ = ∅) is #P-hard under parsimonious reductions |

### Counting (`LatcComplexity/Counting.lean`, namespace `Latc.PaperD`)

`countMissing (φ, T)` counts the states of the attributes occurring in `φ` that satisfy `φ` and
whose condition tuple is not a row of `T` (the convention of Complexitylib's `CNF.modelCount`).

| Theorem | Statement |
|---|---|
| `countMissing_sharpPComplete` | `SharpPComplete encInst countMissing`: counting \|M(T₀)\| is #P-complete under parsimonious reductions |
| `countMissing_mem_SharpP` | `countMissing ∈ SharpP encInst` |
| `countMissing_reduces_sharpSAT` | a parsimonious reduction to #SAT: each row of T₀ of the right length becomes a clause saying the condition tuple differs from it somewhere (`rowClause`, `toSharpSAT`) |
| `countMissing_eq_sharpSAT` | \|M(T₀)\| = #SAT(`toSharpSAT (φ, T)`) |
| `toSharpSAT_polyTime` | the reduction is polynomial-time |

### Counting over general finite domains (`LatcComplexity/CountingGeneral.lean`, namespace `Latc.PaperD.General`)

`missingCount I` is `(Latc.missing I.con I.table).card`: |M(T₀)| for the table an instance denotes
in latc-check's model (see the adequacy section).

| Theorem | Statement |
|---|---|
| `missingCount_sharpPComplete` | `SharpPComplete encInst missingCount`: counting \|M(T₀)\| is #P-complete under parsimonious reductions; with T₀ = ∅ this is \|𝒱\| |
| `missingCount_mem_SharpP` | `missingCount ∈ SharpP encInst` |
| `missingCount_eq_acceptCount` | a certificate is the encoding of a state padded with `false` to the length of the encoded domain sizes; the verifier `cverifier` accepts only these canonical certificates of states of M(T₀), one per tuple |
| `sharpSAT_eq_missingCount` | the SAT reduction of `LatcComplexity.General` (dense variables, domains {0, 1}, T₀ = ∅) preserves counts |
| `missingCount_sharpPHard` | `SharpPHard encInst missingCount` |

### The monotone two-literal case (`LatcComplexity/Monotone.lean`, namespace `Latc.PaperD.General`)

Paper A states that counting |𝒱| stays #P-complete when every clause is two conditions
Aᵢ = 1, Aⱼ = 1 over domains {0, 1}, citing Valiant (1979). Deciding such instances is trivial (the
all-ones state is valid), so no parsimonious reduction from #SAT exists unless P = NP, and hardness
needs a weaker reduction. The file defines one-call counting reductions in Complexitylib's model
(`OneCallReducible`: polynomial-time `r` and `post` with `f a = post a (g (r a))`), and
`OneCallSharpPHard`, `OneCallSharpPComplete` from them. Parsimonious reductions are one-call
reductions, so #SAT is one-call #P-hard (`sharpSAT_oneCallSharpPHard`).

**Valiant's theorem is a hypothesis here, not a proof.** It is not proved in Complexitylib's model.
Valiant proved #Monotone-2SAT #P-complete under polynomial-time Turing reductions; its one-call form
is machine-checked in another model (first-order reductions, #P via existential second-order logic)
as `sharpMonotoneTwoSat_sharpP_oneCallComplete` of
[descriptive-complexity](https://github.com/PierreSenellart/descriptive-complexity).

| Theorem | Statement |
|---|---|
| `countValidMonotone2_oneCallSharpPComplete` | `(hValiant : OneCallSharpPHard encCNF SharpMonotone2SAT) → OneCallSharpPComplete encInst countValidMonotone2` |
| `countValidMonotone2_mem_SharpP` | `countValidMonotone2 ∈ SharpP encInst` (unconditional) |
| `sharpMonotone2SAT_reduces` | #Monotone-2SAT reduces parsimoniously to `countValidMonotone2` (unconditional) |
| `countValidMonotone2_eq_card_validSpace` | on instances of the restricted shape, `countValidMonotone2 I = (Latc.validSpace I.con).card` |

`SharpMonotone2SAT` is #SAT on formulas whose clauses are `xᵢ ∨ xⱼ`, and zero on other syntax;
`countValidMonotone2` is |𝒱| on instances with domains {0, 1}, clauses of two conditions with value 1
and T₀ = ∅, and zero on other syntax. This is the convention of Complexitylib's `SharpThreeSAT`.

## Axiom audit

Each theorem should depend only on `propext`, `Classical.choice` and `Quot.sound`; `sorry`
(`sorryAx`) and custom axioms would show up here. In the build above:

* `LatcComplexity/Axioms.lean`, 72 theorems: 65 print `[propext, Classical.choice, Quot.sound]`;
  `Latc.PaperD.holdsAll_eq_eval`, `Latc.PaperD.satisfiable_decode_iff`,
  `Latc.PaperD.General.Inst.toList_injective`, `Latc.PaperD.General.Inst.exists_toList_eq` and
  `Latc.PaperD.General.con_iff` print `[propext, Quot.sound]`; and
  `Latc.PaperD.General.Inst.inDomains_toList` and `Latc.PaperD.General.con_cond_iff` print
  `[propext]`. `countValidMonotone2_oneCallSharpPComplete` takes Valiant's theorem as its argument
  `hValiant`; an argument is not an axiom, so it does not appear in this list.
* `LatcFormal/Axioms.lean`, 69 theorems: 66 print `[propext, Classical.choice, Quot.sound]` and
  `Latc.Prop5.decode_encode`, `Latc.Prop5.encode_decode` and `Latc.Prop5.encode_size` print
  `[propext, Quot.sound]`, as in latc-check.

`sorryAx` appears in neither. A whole-word search of the `.lean` files for `sorry`, `admit`,
`native_decide` and `axiom` finds them only in the `#print axioms` commands.

## Not yet formalised

* Valiant's theorem in Complexitylib's model: that #Monotone-2SAT is one-call #P-hard. It is the
  hypothesis `hValiant` of `countValidMonotone2_oneCallSharpPComplete`. Proving it needs Valiant's
  chain (or one through counting independent sets, as descriptive-complexity does) with
  polynomial-time certificates for every step.

## Licence

MIT (see `LICENSE`), as latc-check. Complexitylib, CSLib and Mathlib are dependencies under
Apache 2.0 and are not redistributed here.
