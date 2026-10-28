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
`lake build` ended with `Build completed successfully (18599 jobs)` and exit code 0, with no
warnings and no errors. The 16 modules of this repository (`LatcFormal`, its 11 files,
`LatcComplexity`, `Bridge`, `General` and `Axioms`) were compiled; the other jobs were the
dependencies, whose build outputs came from a checkout of the same commits built earlier on the
same machine (Mathlib from `lake exe cache get`, CSLib and Complexitylib compiled there).

## Layout

| Library | Contents |
|---|---|
| `LatcFormal` | Theorem 1, Corollaries 1, 3, 4, Propositions 1–4, 6, 7, and the combinatorial reduction behind Proposition 5, unchanged from latc-check (documented in latc-check's `formal/README.md`) |
| `LatcComplexity.Bridge` | Boolean domains: our clause constraints are Complexitylib CNF formulas; NP-/coNP-completeness and #P-hardness |
| `LatcComplexity.General` | General finite domains: NP-/coNP-completeness |
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

### Boolean domains (`LatcComplexity/Bridge.lean`, namespace `Latc.PaperD`)

An instance is a pair of a Complexitylib `CNF ℕ` (a condition Aᵢ = v is the literal `(i, v)`) and
the condition tuples of T₀ as bit vectors over the distinct attributes of the constraints.

| Theorem | Statement |
|---|---|
| `holdsAll_eq_eval`, `satisfiable_decode_iff` | latc-check's `Latc.Prop5` clause constraints and satisfiability agree with Complexitylib's |
| `MissingNonempty_npComplete` | `NPComplete encInst MissingNonempty` |
| `Complete_coNPComplete` | `coNPComplete encInst Complete` |
| `countMissing_sharpPHard` | `SharpPHard encInst countMissing`: counting \|M(T₀)\| (and \|𝒱\|, with T₀ = ∅) is #P-hard under parsimonious reductions |

## Axiom audit

Each theorem should depend only on `propext`, `Classical.choice` and `Quot.sound`; `sorry`
(`sorryAx`) and custom axioms would show up here. In the build above:

* `LatcComplexity/Axioms.lean`, 26 theorems: 24 print `[propext, Classical.choice, Quot.sound]` and
  `Latc.PaperD.holdsAll_eq_eval` and `Latc.PaperD.satisfiable_decode_iff` print
  `[propext, Quot.sound]`.
* `LatcFormal/Axioms.lean`, 69 theorems: 66 print `[propext, Classical.choice, Quot.sound]` and
  `Latc.Prop5.decode_encode`, `Latc.Prop5.encode_decode` and `Latc.Prop5.encode_size` print
  `[propext, Quot.sound]`, as in latc-check.

`sorryAx` appears in neither. A whole-word search of the `.lean` files for `sorry`, `admit`,
`native_decide` and `axiom` finds them only in the `#print axioms` commands.

## Not yet formalised

* An adequacy theorem linking the word-encoded problems to latc-check's `Finset` model
  (`Latc.missing`, `Latc.validSpace` over `Fin n` attributes).
* #P membership of counting |M(T₀)|, which with `countMissing_sharpPHard` gives #P-completeness.
* The monotone two-literal case (Valiant 1979) of the counting statement. It is formalised in
  Lean, in another model, as `sharpMonotoneTwoSat_sharpP_oneCallComplete` of
  [descriptive-complexity](https://github.com/PierreSenellart/descriptive-complexity).

## Licence

MIT (see `LICENSE`), as latc-check. Complexitylib, CSLib and Mathlib are dependencies under
Apache 2.0 and are not redistributed here.
