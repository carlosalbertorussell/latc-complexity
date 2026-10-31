# Closing the three open gaps

Plan of 2026-10-31 for the three results the README lists under "Not yet formalised", and that
Paper D's Section 7 names as what remains. It rests on what this repository (Lean files at
`011cd1a`), Complexitylib (pinned at `b7acfc2`) and Senellart and Gnatenko's
descriptive-complexity (`fc068f6`) contain on that date.

| Gap | What it closes | Size | Order |
|---|---|---|---|
| 1. Valiant's theorem in Complexitylib's model | the hypothesis `hValiant`; the monotone case becomes unconditional | large | second; **done** (`3bb09ae`, merged in `43d7e25`) |
| 2. Counting with a fixed number of attributes | the counting half of the tractable side | moderate | first; **done** (`242311b`) |
| 3. An explicit degree in k | uniformity of the fixed-attribute bounds | small maths, heavy bookkeeping | last; started 2026-10-31 |

None of them blocks the ITP 2027 submission. Gaps 1 and 2 are closed; the draft states Gap 3 as open.

## Gap 1: Valiant's theorem in Complexitylib's model

**Goal.** Prove `OneCallSharpPHard encCNF SharpMonotone2SAT`. Applying
`countValidMonotone2_oneCallSharpPComplete(_bin)` to it makes the monotone case unconditional,
with no change to `Monotone.lean`.

**What exists.** Complexitylib has parsimonious #P-completeness of #SAT and #3SAT
(`CookLevin.SharpSAT_sharpPComplete`, `SharpThreeSAT_sharpPComplete`) and a decision problem
`IndependentSet`, but no counting version of independent sets and no #P-hardness beyond the SAT
family. This repository has one-call reductions (`OneCallReducible`, `OneCallSharpPHard`) and
their composition with parsimonious ones (`OneCallSharpPHard.trans_parsimonious`).

**Route.** Valiant's own proof interpolates over many oracle calls. Port instead the one-call
chain of descriptive-complexity (`Problems/CliqueFamily/CountingAll.lean`,
`Problems/Sat/CountingRestricted.lean`, `Numbers/DigitExtract.lean`):

1. **#SAT → #IS_k, parsimonious:** counting independent sets of exactly size k. A parsimonious
   gadget from 3SAT is needed; not every textbook reduction is parsimonious, so follow
   descriptive-complexity's `SharpIndependentSet`, which that library proves parsimoniously
   complete.
2. **#IS_k → #AllIS, one call (pendant gadget):** attach n pendant leaves to each of the n
   vertices. The oracle answer is Σ_S (2ⁿ)^(n−|S|), so the number of independent sets of size k
   is its digit of rank n−k in base 2ⁿ: `oracle / 2^(n(n−k)) % 2^n`. Needs the digit lemma
   (descriptive-complexity's `sum_pow_div_mod`), polynomial-time division, remainder and powers of
   two on binary numbers, and the polynomial time of the graph construction.
3. **#AllIS → #Monotone-2SAT, one call:** independent sets are complements of vertex covers; each
   edge {u, v} becomes the clause xᵤ ∨ xᵥ, whose models are the vertex covers of the non-isolated
   vertices; the post-processing multiplies by 2 to the number of isolated vertices. The formula
   must pass `monotone2B` (exactly two positive literals per clause), which holds for simple
   graphs.
4. **Glue:** a transitivity lemma for two one-call reductions (only one-call followed by
   parsimonious exists so far).

**Status.** Done on 2026-10-31 on branch `claude/gap1-valiant` (`3bb09ae`, clean build of 18643
jobs, 80 audited theorems on the standard axioms), merged into `main` in `43d7e25`. The proof took
a shorter route than steps 1–4: one one-call reduction from #SAT that fuses them (a parsimonious
"first true literal" conflict graph for any CNF, pendant leaves, one digit), so neither #IS_k
nor #AllIS nor a one-call ∘ one-call lemma was needed; only `ParsimoniousReducible.trans_oneCall`.
Main theorem: `Latc.PaperD.Valiant.sharpMonotone2SAT_oneCallSharpPHard`. Details in
`docs/gap1-progress.md`.

**Risk (as planned).** The largest gap: a new development of graph counting problems in Complexitylib's
model. Step 1 is the hardest. The result arguably belongs upstream in Complexitylib; done here
first, it can be offered upstream later.

## Gap 2: counting with a fixed number of attributes

**Goal.** For each k,
`ComputableInPolyTime (fun I => if I.n ≤ k then missingCount I else 0) encInstBin encNat`, and the
`_unary` corollary.

**Mathematics.** For attribute i with domain size dᵢ, split {0, …, dᵢ−1} into classes: each
written value below dᵢ alone, and one unwritten class of size dᵢ − #{written values < dᵢ}
(possibly 0). Which conditions a state satisfies depends only on its vector of classes, since an
unwritten value matches no condition, and a state with an unwritten value is never a row of T₀.
So

  |𝒱| = Σ over valid class vectors c of ∏ᵢ |cᵢ|,
  |M(T₀)| = |𝒱| − #{distinct in-domain rows of T₀ that are valid},

over at most (N+1)ᵏ class vectors, N the number of written values.

**Lean steps.** The class map, with a representative of the unwritten class from
`exists_unwritten`; the partition and validity invariance (`Finset.card_eq_sum_card_fiberwise`);
the weights in binary, reusing the bounded-growth fold of `domProd_polyTime` (every partial sum is
at most ∏ dᵢ); polynomial time by the induction on k of `candidateStates_polyTime`.

**Status.** Done on 2026-10-31, commit `242311b`, pushed to `main` after a clean build and axiom
audit (174 theorems, each on a subset of the three standard axioms):
`missingCount_eq_weighted_of_le`, `length_classStates_le`, `missingCountFixedAttrs_polyTime` and
`missingCountFixedAttrs_polyTime_unary`, in `Tractable.lean`. The weights are summed by
`countClasses`, a bounded-growth fold (`countClasses_polyTime`).

## Gap 3: an explicit degree in k

**Goal.** Uniformity in k: ∃ c d₀ d₁, ∀ k, the fixed-k decider runs within
c·(|x|+1)^(d₀·k + d₁). The current proof gives a polynomial for each k separately, with no
relation between them; the search space is bounded by (2N+1)ᵏ with N ≤ |x|.

**How.** Complexitylib exposes explicit bounds under polynomial time:
`ComputableTidilyInPolyTime` is ∃ t s with `PolyBounded` bounds and
`ComputableTidilyInTimeAndSpace f … t s`, and `PolyBounded.of_forall_le c d` takes an explicit
constant and degree. Redo `boundedSections_polyTime` and the fixed-k decider with explicit time
bounds through each composition, since the library's composition lemmas are existential.

**Scope.** Both fixed-attribute bounds: the decider (search space (2N+1)ᵏ) and, since Gap 2, the
counter (at most (N+1)ᵏ class vectors).

**Priority.** Lowest. For the paper, polynomial time for each k plus these bounds suffices.

**Status.** Started on 2026-10-31 in a separate cloud session, on branch
`claude/gap3-explicit-degree` (new file `LatcComplexity/ExplicitDegree.lean` preferred), with
progress in `docs/gap3-progress.md` on that branch. It merges to `main` only after a clean build
and axiom audit.
