# latc-complexity

Proposition 5 of Paper A (the LATC re-examination, "Where Declared Domains Are Lost"),
composed with the Cook–Levin theorems of
[Complexitylib](https://github.com/cslib-community/complexitylib) and machine-checked end to end in
Lean 4. Completeness of a decision table whose constraints are clauses is coNP-complete, and
non-emptiness of its missing set M(T₀) is NP-complete, for general finite domains. Both become
polynomial-time without constraints, or with a fixed number of attributes, and so does counting
|M(T₀)|; the hardness needs constraints and an unbounded number of attributes together. Counting
|M(T₀)| stays #P-complete, under one-call reductions, for monotone two-literal constraints and any
T₀: Valiant's theorem
is proved here in Complexitylib's model, not assumed. These are
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

The steps for the v1.0 release are in `RELEASE.md`. Steps 0–3 (preconditions, the cold build and the
full audit at commit `6a008ef`, and the tag `v1.0` on the commit that records them, with the same
Lean files) were done on 2026-11-01; the
repository is not public yet and has no Zenodo archive yet.

`lake exe cache get` downloads the precompiled Mathlib. CSLib and the Complexitylib modules that
are imported are then compiled from source, which takes a while on the first build.

Verification at commit `6a008ef` (2026-11-01; the tag `v1.0` has the same Lean files): cold build on a Linux cloud
machine, x86_64, 4 cores, 15 GB RAM, Ubuntu 24.04, in a fresh clone with an empty `HOME` (no
`~/.elan`, `.lake` or Mathlib cache), following `RELEASE.md` §2–3 and timed with `date` stamps.
Lean 4.36.0-rc1 (commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`), Lake 5.0.0, elan 4.2.4.
Clone 1 s; elan install 1 s; `lake exe cache get` 97 s, including the toolchain download (all 9047
Mathlib files from the cache); `lake build` 213 s, `Build completed successfully (18651 jobs)`,
exit code 0, no warnings, no errors, compiling from source 27 CSLib and 212 Complexitylib modules
and the 30 repository modules; the full axiom audit (below) 14 s. About 5.5 minutes in all. Disk:
the clone with `.lake` 7.8 GB, `~/.elan` 3.1 GB, `~/.cache/mathlib` 453 MB, 11.4 GB in all. The
Lean files and the pins of `6a008ef` are those of `0ea3170`, the build the JAR version of Paper D
reports.

### History of builds

The builds below are the development's history, moved here from the paper. The pin `b7acfc2` was
kept throughout; Complexitylib had just been rewritten on CSLib, and its earlier version, which
Paper A cites, is a separate repository with a different API.

JAR revision (2026-11-01): cold build of commit `0ea3170` on 2026-11-01,
Linux cloud machine, x86_64, 4 cores, in a fresh clone with an empty `HOME` (no `~/.elan`, `.lake`
or Mathlib cache), Lean 4.36.0-rc1 (commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`), Lake 5.0.0,
elan 4.2.4. elan install 1 s; `lake exe cache get` 103 s, including the toolchain (all 9047 Mathlib
files from the cache); `lake build` 217 s, `Build completed successfully (18651 jobs)`, exit code 0,
no warnings, no errors, compiling from source 239 CSLib and Complexitylib modules and the 30
repository modules; the audit (below) 13 s. Disk: the clone with `.lake` 8.0 GB, `~/.elan` 3.1 GB,
`~/.cache/mathlib` 453 MB. This is the build the JAR version of Paper D reports.

Verification status (2026-10-31, Linux cloud machine, x86_64): Lean 4.36.0-rc1 (commit
`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`, Lake 5.0.0, elan 4.2.4), with the dependencies above,
in a fresh checkout with no `~/.elan`, `.lake` or Mathlib cache. `lake exe cache get` took 123 s
(all 9047 Mathlib files from the cache). A first `lake build` of commit `8985f38` (before the
counting result of (b)) ended with `Build completed successfully (18625 jobs)` in 217 s, no
warnings, no errors, compiling CSLib and Complexitylib from source and the 22 modules of this
repository (`LatcFormal`, its 11 files, `LatcComplexity`, `Bridge`, `General`, `Adequacy`,
`Counting`, `CountingGeneral`, `Monotone`, `Binary`, `Tractable` and `Axioms`). With the counting
result added to `Tractable`, `lake build` recompiled `Tractable`, `Axioms` and `LatcComplexity` and
again ended with `Build completed successfully (18625 jobs)` and exit code 0, with no warnings and
no errors.

Gap 1 (Valiant's theorem, `LatcComplexity/Valiant/`) was built on its branch, at commit `3bb09ae`
on top of `fcdf0ef` (before the counting result of (b)): `Build completed successfully (18643
jobs)`, no warnings, no errors. It was merged into `main` (`43d7e25`) without conflicts; it adds
new files and import lines only. Gap 3 (`LatcComplexity/ExplicitDegree.lean`) was built on its
branch (`d6980bb`, on top of `242311b`: `Build completed successfully (18627 jobs)`) and merged onto
`43d7e25` in a scratch checkout, where `lake build` ended with `Build completed successfully (18645
jobs)`, exit code 0, no warnings, no errors. That merge is `cbf016b` on `main`; the commits between
`43d7e25` and it change documentation only, so its Lean files are those of that build.
The any-T₀ monotone result (`LatcComplexity/Valiant/AnyTable.lean`) was built on its branch on top
of `0b9b734`: `Build completed successfully (18647 jobs)`, no warnings, no errors; it was merged
into `main` (`a21b85f`) without conflicts, adding one file, one import line and audit lines.

Cold build at the final commit (2026-10-31, Linux cloud machine, x86_64, 4 cores, commit `6603497`,
whose Lean files are those of `cbf016b`; fresh clone, no `~/.elan`, `.lake` or Mathlib cache):
elan install 1.2 s; `lake exe cache get` 173 s, including the toolchain download (all 9047 Mathlib
files from the cache); `lake build` 361 s, `Build completed successfully (18645 jobs)`, exit code 0,
no warnings, no errors, compiling from source 27 CSLib, 211 Complexitylib and the 28 repository
modules. About 9 minutes in all (timed with `date` stamps); 12 GB of disk: the repository with
`.lake` 7.7 GB, `~/.elan` with Lake's artifact cache 3.1 GB, `~/.cache/mathlib` 453 MB. The later
merge `42b9977` changes only comments in `Monotone.lean`.

Upstream test (2026-10-31, branch `claude/upstream-complexitylib-test`, not merged): with
Complexitylib at its then-current main `b9e6241` (2026-10-31 15:57 UTC), Lean `v4.36.0-rc2`, and the
CSLib (`254e30e`) and Mathlib (`6955275`) that `lake update complexitylib` brings, the development
builds with no Lean file changed: `Build completed successfully (18717 jobs)`, no warnings, no
errors, and the same axiom audit. `main` keeps the pin `b7acfc2`, against which everything was
proved.

Earlier cold build (2026-10-28, same machine type, commit `a2ab2f8`, fresh clone, no `~/.elan`, `.lake` or
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
| `LatcComplexity.Monotone` | Clauses of two conditions Aᵢ = 1, Aⱼ = 1: counting \|𝒱\| is in #P, and one-call #P-complete given Valiant's theorem as a hypothesis |
| `LatcComplexity.Valiant` | Valiant's theorem in its one-call form, proved: #Monotone-2SAT is one-call #P-hard, so the monotone case is unconditional, for counting valid states and for counting \|M(T₀)\| with any T₀ (`Gadget`, `Counting`, `Pendant`, `OneCall`, `AnyTable`, `Axioms`) |
| `LatcComplexity.Binary` | The attribute index of a condition in binary: every theorem above for the encoding `encInstBin` |
| `LatcComplexity.Restricted` | Hardness already on Boolean domains with T₀ = ∅: the shape of `fromSAT`, NP- and coNP-hardness of the restricted sets, NP-hardness of the promise version, #P-hardness of the restricted count |
| `LatcComplexity.Tractable` | The tractable side: no constraints, or at most `k` attributes, in polynomial time |
| `LatcComplexity.ExplicitDegree` | The fixed-attribute bounds with an explicit degree, uniform in `k`: time and space `c · (\|x\| + 1) ^ (d · n + d)` |
| `LatcComplexity.Axioms` | `#print axioms` on every main theorem of the `LatcComplexity` files (17 helper lemmas are not printed) (`LatcComplexity.Valiant.Axioms` for `Valiant/`) |

## Theorems

Classes, reductions and encodings are Complexitylib's (`Cslib.Complexity.NP`, `coNP`,
`PolyTimeReducible`, `NPComplete`, `coNPComplete`, `SharpPHard`; Turing machines with a binary
alphabet; `ComputableInPolyTime`). Hardness comes from Complexitylib's `CookLevin.SAT_npHard`,
`CookLevin.UNSAT_coNPComplete` and the parsimonious `CookLevin.SharpSAT_sharpPHard`.

### General finite domains (`LatcComplexity/General.lean`, namespace `Latc.PaperD.General`)

An instance is `(d, S, T)`: the domain sizes `d = [|D₀|, …, |Dₙ₋₁|]` (attribute `i` takes the values
`0, …, dᵢ − 1`), the clause constraints `S` (each clause a list of conditions `(i, v)`, read
Aᵢ = v), and the condition tuples `T` of T₀. A state is a list `s` with `s.length = n` and
`sᵢ < dᵢ`. In `encInst`, numbers are encoded in binary, except the attribute index `i` of a
condition, which is unary. The encoding `encInstBin` of `LatcComplexity/Binary.lean` writes the
index in binary too; every theorem of this section and the next three holds for both encodings
(see the binary section).

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

In this file Valiant's theorem is the hypothesis `hValiant`; `LatcComplexity/Valiant/` (next
section) proves it, so the monotone case holds unconditionally. Valiant proved #Monotone-2SAT
#P-complete under polynomial-time Turing reductions; its one-call form is also machine-checked in
another model (first-order reductions, #P via existential second-order logic) as
`sharpMonotoneTwoSat_sharpP_oneCallComplete` of
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

The shape tests (`pos2B`, and `pos2AnyB` below) also require every condition to name an existing
attribute (`a.1 < I.1.length`), so on their instances the all-ones state is valid
(`valid_replicate_one_of_pos2B`, `valid_replicate_one_of_pos2AnyB`) and a missing state always
exists (`mem_missingNonempty_of_pos2B`): deciding is trivial, which is why hardness needs one-call
reductions. (Added at `3b6f523`; the theorem statements are unchanged.)

### Valiant's theorem (`LatcComplexity/Valiant/`, namespace `Latc.PaperD.Valiant`)

One reduction from #SAT to #Monotone-2SAT with a single oracle call, so the hypothesis `hValiant`
above is a theorem. After dense relabelling, a conflict graph has a vertex for each variable and
value and one per literal occurrence, read "the first true literal of its clause"; its vertices
split into `n + m` cliques, and its independent sets of size `n + m` are in bijection with the
models (`modelCount_eq_card`), for any CNF. Each vertex gets `t = n + 1` pendant leaves and each
edge `{u, w}` becomes the clause `x_u ∨ x_w`, so the models of the monotone formula number
Σ over independent sets `S` of `2^(t(N − |S|))` (`modelCount_psi`). The post-processing reads
#SAT off as one digit, `x · 2^(tK) / 2^(tN) mod 2^t`. The only composition needed is parsimonious
then one-call (`ParsimoniousReducible.trans_oneCall`), from Complexitylib's
`CookLevin.SharpSAT_sharpPHard`. Details and the route are in `docs/gap1-progress.md`.

| Theorem | Statement |
|---|---|
| `sharpMonotone2SAT_oneCallSharpPHard` | `OneCallSharpPHard encCNF SharpMonotone2SAT` |
| `countValidMonotone2_sharpPComplete_oneCall` | `OneCallSharpPComplete encInstBin countValidMonotone2` |
| `countValidMonotone2_sharpPComplete_oneCall_unary` | `OneCallSharpPComplete General.encInst countValidMonotone2` |
| `countMissingMonotone2_eq_card_missing` | `pos2AnyB I = true → countMissingMonotone2 I = (Latc.missing I.con I.table).card` |
| `sharpMonotone2SAT_reduces_countMissing` | `ParsimoniousReducible encCNF General.encInst SharpMonotone2SAT countMissingMonotone2` |
| `countMissingMonotone2_sharpPComplete_oneCall` | `OneCallSharpPComplete encInstBin countMissingMonotone2` |
| `countMissingMonotone2_sharpPComplete_oneCall_unary` | `OneCallSharpPComplete General.encInst countMissingMonotone2` |
| `sharpSAT_oneCallReducible` | `OneCallReducible encCNF encCNF SharpSAT SharpMonotone2SAT` |
| `sharpSAT_eq_post` | `SharpSAT φ = post φ (SharpMonotone2SAT (toMonotone φ))` |
| `toMonotone_polyTime` | `ComputableInPolyTime toMonotone encCNF encCNF` |
| `post_polyTime` | `ComputableInPolyTime (fun p : CNF ℕ × ℕ => post p.1 p.2) (encPair encCNF encNat) encNat` |

`countMissingMonotone2` (`Valiant/AnyTable.lean`) is |M(T₀)| on instances with domains {0, 1} and
clauses of two conditions with value 1, any T₀ (`pos2AnyB`, which is `pos2B` without its `T₀ = ∅`
test), and zero on other syntax. Its hardness needs no new reduction: the reduction from
#Monotone-2SAT produces either a monotone instance with T₀ = ∅, where it agrees with
`countValidMonotone2`, or `emptyClauseInst`, which fails both shape tests.

### The binary attribute index (`LatcComplexity/Binary.lean`, namespace `Latc.PaperD.General`)

`encInstBin` encodes an instance with every number in binary, the attribute index of a condition
included. The problems are the same sets of instances; only the encoding changes. The check of a
candidate state reads `s[i]` at a binary `i` with Complexitylib's
`ComputableTidilyInPolyTime.listGetD_binary`, which caps the index at the length of the list while
reading its bits, so a large index is never expanded to unary (`condHoldsBin`, shifting the values
by one so that the default `0` of an out-of-range lookup matches no value). Hardness transfers
because the identity is polynomial-time from `encInst` to `encInstBin`.

| Theorem | Statement |
|---|---|
| `checkBin_polyTime` | `ComputableInPolyTime check (encPair encInstBin (encList encNat)) encBool` |
| `encInst_to_encInstBin_polyTime` | `ComputableInPolyTime (fun I => I) encInst encInstBin` (`idReduction`, `idParsimonious`) |
| `MissingNonempty_npComplete_bin` | `NPComplete encInstBin MissingNonempty` |
| `Complete_coNPComplete_bin` | `coNPComplete encInstBin Complete` |
| `missingNonempty_finset_npComplete_bin` | `NPComplete encInstBin {I \| (Latc.missing I.con I.table).Nonempty}` |
| `complete_finset_coNPComplete_bin` | `coNPComplete encInstBin {I \| Latc.missing I.con I.table = ∅}` |
| `missingCount_sharpPComplete_bin` | `SharpPComplete encInstBin missingCount` |
| `countValidMonotone2_mem_SharpP_bin` | `countValidMonotone2 ∈ SharpP encInstBin` (unconditional) |
| `countValidMonotone2_oneCallSharpPComplete_bin` | `(hValiant : OneCallSharpPHard encCNF SharpMonotone2SAT) → OneCallSharpPComplete encInstBin countValidMonotone2` |

### Boolean domains with T₀ = ∅ (`LatcComplexity/Restricted.lean`, namespace `Latc.PaperD.General`)

`fromSAT` produces only instances whose domains all have size 2 and whose table is empty, the class
`BoolEmpty`. Hardness therefore holds already on that class. A restricted set contains its
restriction (`MissingNonempty ∩ BoolEmpty`), and the promise version leaves instances outside
`BoolEmpty` unconstrained. All for `encInstBin`.

| Theorem | Statement |
|---|---|
| `fromSAT_mem_boolEmpty` | `fromSAT φ ∈ BoolEmpty` |
| `MissingNonemptyBoolEmpty_npHard_bin` | `NPHard encInstBin MissingNonemptyBoolEmpty` |
| `CompleteBoolEmpty_coNPHard_bin` | `coNPHard encInstBin CompleteBoolEmpty` |
| `missingNonemptyPromise_npHard_bin` | `PromiseProblem.NPHard encInstBin missingNonemptyPromise` (yes: `BoolEmpty` with M(T₀) ≠ ∅; no: `BoolEmpty` with M(T₀) = ∅) |
| `missingCountBoolEmpty_sharpPHard_bin` | `SharpPHard encInstBin missingCountBoolEmpty` (|M(T₀)| on `BoolEmpty`, 0 elsewhere) |

### The tractable side (`LatcComplexity/Tractable.lean`, namespace `Latc.PaperD.General`)

`P` is Complexitylib's class (`Cslib.Complexity.P`: a Boolean decider computable in polynomial
time). A restricted problem contains its restriction, as Complexitylib's `SharpThreeSAT` does: a
decider also checks the shape of the instance. All statements are on latc-check's `Latc.missing`,
for `encInstBin`; each also holds for `encInst` (suffix `_unary`, from `mem_P_of_mem_P_bin`, or
for the counting statements by composing with `encInst_to_encInstBin_polyTime`).

**(a) No constraints** (`S = []`), any number of attributes, T₀ arbitrary. |M(T₀)| is
∏ dᵢ minus the number of distinct rows of T₀ inside the declared domains. ∏ dᵢ can be exponential
in the input length, but its binary encoding is no longer than those of the dᵢ together
(Complexitylib's `length_encNat_mul_le`), so it is computed exactly, in binary, by a fold with
bounded growth (`domProd_polyTime`); the distinct rows are counted as the rows that do not occur
earlier in the list (`firstOcc`, `length_firstOcc`).

| Theorem | Statement |
|---|---|
| `missingCount_eq_of_noConstraints` | `I.2.1 = [] → missingCount I = domProd I - distinctRows I` |
| `missingCountNoConstraints_polyTime` | `ComputableInPolyTime (fun I => if I.2.1 = [] then missingCount I else 0) encInstBin encNat` |
| `completeNoConstraints_mem_P` | `{I \| I.2.1 = [] ∧ Latc.missing I.con I.table = ∅} ∈ P encInstBin` |
| `missingNonemptyNoConstraints_mem_P` | `{I \| I.2.1 = [] ∧ (Latc.missing I.con I.table).Nonempty} ∈ P encInstBin` |

**(b) At most `k` attributes**, any clause constraints, domain sizes in binary. With binary domain
sizes |𝒟| = ∏ dᵢ is not polynomial even for `k = 1`, so 𝒟 is not enumerated. Let `N` be the number
of values written in the instance (in the conditions and the rows of T₀, `Inst.numVals`). The
candidate values of attribute `i` are `0, …, N` and the written values, inside the domain. A value
written nowhere can be replaced by one `≤ N` written nowhere (one exists by counting) without
changing which conditions hold, and a state with such a value is not a row of T₀; so a missing
state exists iff a candidate one does. The candidate states are enumerated for at most `k` lists
(`boundedSections`), whose polynomial time is proved by induction on `k`.

| Theorem | Statement |
|---|---|
| `exists_missing_candidate_iff` | `I.n ≤ k → (I ∈ MissingNonempty ↔ ∃ s ∈ candidateStates k I, check (I, s) = true)` |
| `length_candidateStates_le` | `(candidateStates k I).length ≤ (2 * I.numVals + 1) ^ k` |
| `candidateStates_polyTime` | for each `k`, `ComputableTidilyInPolyTime (candidateStates k) encInstBin (encList (encList encNat))` |
| `missingNonemptyFixedAttrs_mem_P` | `∀ k, {I \| I.n ≤ k ∧ (Latc.missing I.con I.table).Nonempty} ∈ P encInstBin` |
| `completeFixedAttrs_mem_P` | `∀ k, {I \| I.n ≤ k ∧ Latc.missing I.con I.table = ∅} ∈ P encInstBin` |
| `missingCount_eq_weighted_of_le` | `I.n ≤ k → missingCount I = ((classStates k I).map fun c => if validB (I, c) then classStateWeight (I, c) else 0).sum` |
| `length_classStates_le` | `(classStates k I).length ≤ (I.numVals + 1) ^ k` |
| `missingCountFixedAttrs_polyTime` | for each `k`, `ComputableInPolyTime (fun I => if I.n ≤ k then missingCount I else 0) encInstBin encNat` |

**Counting with at most `k` attributes.** The values `0, …, dᵢ − 1` of attribute `i` fall into
classes: each written value (`distinctVals (writtenVals I)`) is its own class, of size one if it is
below `dᵢ` and zero otherwise, and the unwritten values form one more class, of size `dᵢ` minus the
written values below `dᵢ`, represented by `unwritten I`, a value `≤ N` written nowhere
(`classVals`, `classWeight`). Mapping each value to its class (`cls`) changes neither which
conditions hold nor membership in T₀ (`validB_map_cls`: a state with an unwritten value is not a
row of T₀). So |M(T₀)| is the sum, over the class vectors `c` (`classStates`, at most `(N + 1)ᵏ`
of them) that satisfy the constraints and are not rows of T₀ (`validB`), of the number ∏ᵢ |cᵢ| of
states they stand for (`classStateWeight`); the partition is proved one attribute at a time
(`sum_range_eq_classes`, `length_filter_domStates`). Each weight is at most ∏ dᵢ
(`classStateWeight_le_domProd`), so the sum is computed in binary by a fold with bounded growth,
as in (a) (`countClasses_polyTime`).

**An explicit degree in `k`** (`LatcComplexity/ExplicitDegree.lean`). The theorems above give a
polynomial for each `k`, with no relation between them. This file makes the degree explicit and
uniform, in time and in space, with Complexitylib's `ComputableTidilyInO`, which keeps explicit
bound functions and one constant through composition, case splits and folds; the enumeration of
candidate values is a left fold with explicitly bounded intermediate results. Below, `|x|` is
`(encInstBin I).length` and `n = I.n`; each line holds for the non-emptiness decider, the
completeness decider and the counter (`missingNonempty_…`, `complete_…`, `missingCount_…`).

| Theorems | Statement |
|---|---|
| `missingNonempty_explicitDegree`, `complete_explicitDegree`, `missingCount_explicitDegree` | `∃ c d`, one machine on every instance, time and space `c * (\|x\| + 1) ^ (d * I.n + d)` |
| `missingNonemptyFixedAttrs_uniform`, `completeFixedAttrs_uniform`, `missingCountFixedAttrs_uniform` | `∃ c d₀ d₁, ∀ k`, on `{I : Inst // I.n ≤ k}`, time and space `c * (\|x\| + 1) ^ (d₀ * k + d₁)` |
| `missingNonemptyWithBound_explicitDegree`, `completeWithBound_explicitDegree`, `missingCountWithBound_explicitDegree` | `∃ c d`, one machine on pairs `(k, I)` (`k` in unary) computing the fixed-`k` set or function of (b) (`I.n ≤ k ∧ …`, or `if I.n ≤ k then missingCount I else 0`), within `c * (\|(k, x)\| + 1) ^ (d * k + d)` |

Not proved: for each `k`, a machine with `k` built in that rejects instances with more than `k`
attributes, with constants independent of `k`. The constants of Complexitylib's constant-output and
case-split lemmas depend on the machine. The second and third lines cover the same ground.
Statements verbatim and details: `docs/gap3-progress.md`.

### Where the hardness comes from

| | constraints | attributes | complexity |
|---|---|---|---|
| SAT reduction (`fromSAT`) | clauses | `φ.numVars`, unbounded | NP-, coNP-, #P-complete |
| (a) | none | unbounded | in P; counting \|M(T₀)\| polynomial-time |
| (b) | clauses | at most `k` | in P for each `k`; counting \|M(T₀)\| polynomial-time for each `k` |

The reduction from SAT needs both ingredients: removing the constraints or bounding the number of
attributes makes deciding completeness and non-emptiness, and counting |M(T₀)|, polynomial-time.
The planning note `docs/boundary.md` lists the same statements.

## Axiom audit

Each theorem should depend only on `propext`, `Classical.choice` and `Quot.sound`; `sorry`
(`sorryAx`) and custom axioms would show up here.

Full audit at commit `6a008ef` (whose Lean files are those of `0ea3170` and of the tag `v1.0`),
2026-11-01, in the cold build above; the same counts as at the JAR revision. Run as
`lake env lean` on each audit file: 397 answers. `LatcComplexity/Axioms.lean` 234: 202 print
`[propext, Classical.choice, Quot.sound]`, 17 `[propext, Quot.sound]`, 13 `[propext]`,
2 `[Quot.sound]` (the ten theorems of `Restricted.lean` print all three).
`LatcComplexity/Valiant/Axioms.lean` 94: 76 all three, 9 `[propext, Quot.sound]`, 7 `[propext]`,
2 none. `LatcFormal/Axioms.lean` 69: 66 all three, 3 `[propext, Quot.sound]`. None mentions
`sorryAx` or any other axiom. In `LatcComplexity/`, 328 of the 345 theorem and lemma declarations
are printed; the other 17 are helper lemmas. The counts below are from earlier builds.

Full audit at the cold build of `6603497`: 300 theorems. `LatcComplexity/Axioms.lean`, 220:
188 print `[propext, Classical.choice, Quot.sound]`, 17 `[propext, Quot.sound]`, 13 `[propext]`,
2 `[Quot.sound]`. `LatcComplexity/Valiant/Axioms.lean`, 80: 65 print all three, 9
`[propext, Quot.sound]`, 6 `[propext]`. None mentions `sorryAx` or any other axiom. The any-T₀
monotone result (`Valiant/AnyTable.lean`, branch build `8d3cb97`, merged in `a21b85f`) adds 13
lines to `Valiant/Axioms.lean`: 10 print all three, `pos2AnyB_of_pos2B` prints `[propext]`, and
`pos2B_eq` and `pos2AnyB_emptyClauseInst` depend on no axioms; 313 in all. The tightened shape
tests (`3b6f523`, branch build `574b4ee`, 18647 jobs, clean) add 5 more: `LatcComplexity/Axioms.lean`
224 (192 all three, 17 `[propext, Quot.sound]`, 13 `[propext]`, 2 `[Quot.sound]`) and
`LatcComplexity/Valiant/Axioms.lean` 94 (76 all three, 9 `[propext, Quot.sound]`, 7 `[propext]`,
2 none); 318 in all, none with `sorryAx`. The per-name lists below
are from the earlier builds:

* `LatcComplexity/Axioms.lean`, 220 theorems (72 as before, 21 of `Binary`, 81 of `Tractable`, 46 of
  `ExplicitDegree`). The 46 of `ExplicitDegree` (Gap 3 build, `d6980bb`) each print a subset of
  `[propext, Classical.choice, Quot.sound]`; the per-name breakdown below covers the other 174:
  152 print `[propext, Classical.choice, Quot.sound]`; `Latc.PaperD.holdsAll_eq_eval`,
  `Latc.PaperD.satisfiable_decode_iff`, and, in `Latc.PaperD.General`, `Inst.toList_injective`,
  `Inst.exists_toList_eq`, `con_iff`, `length_domains_le_bin`, `length_encNat_le_of_mem`,
  `length_boundedSections_le`, `length_candVals_le`, `length_candidateStates_le`,
  `candLists_eq`, `mem_domStates`, `length_of_mem_boundedSections` and
  `length_encNat_le_of_mem_domains` print `[propext, Quot.sound]`;
  `Latc.PaperD.General.Inst.inDomains_toList`, `Latc.PaperD.General.con_cond_iff`, and, in
  `Latc.PaperD.General`, `foldl_mul_eq`, `foldl_add_eq`, `boundedSections_cons` and `sum_flatMap`
  print `[propext]`; and
  `Latc.PaperD.General.boundedSections_zero` and `Latc.PaperD.General.boundedSections_succ` print
  `[Quot.sound]`. `countValidMonotone2_oneCallSharpPComplete` takes Valiant's theorem as its argument
  `hValiant`; an argument is not an axiom, so it does not appear in this list.
* `LatcComplexity/Valiant/Axioms.lean`, 80 theorems, in the build of the Gap 1 branch (`3bb09ae`):
  each prints a subset of `[propext, Classical.choice, Quot.sound]`, and the three main theorems
  (`sharpMonotone2SAT_oneCallSharpPHard` and the two `countValidMonotone2_sharpPComplete_oneCall`
  forms) print all three. `hValiant` is discharged there by proof, not by an axiom.
* `LatcFormal/Axioms.lean`, 69 theorems: 66 print `[propext, Classical.choice, Quot.sound]` and
  `Latc.Prop5.decode_encode`, `Latc.Prop5.encode_decode` and `Latc.Prop5.encode_size` print
  `[propext, Quot.sound]`, as in latc-check.

`sorryAx` appears in neither. A whole-word search of the `.lean` files for `sorry`, `admit`,
`native_decide` and `axiom` finds them only in the `#print axioms` commands.

## Not yet formalised

The three gaps of `docs/gaps-plan.md` are closed: counting with at most `k` attributes (`242311b`),
Valiant's theorem (`43d7e25`) and an explicit degree in `k` (`cbf016b`). What stays outside the
development: a per-`k` machine with `k` built in and constants independent of `k` (see the
explicit-degree paragraph above). The pin stays at `b7acfc2`; the development also builds unchanged
against Complexitylib `b9e6241` (see Build).

## Licence

MIT (see `LICENSE`), as latc-check. Complexitylib, CSLib and Mathlib are dependencies under
Apache 2.0 and are not redistributed here.
