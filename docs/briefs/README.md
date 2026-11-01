# Task descriptions of the Paper D sessions

These are the task descriptions (briefs) of the cloud sessions that were started from the author's planning session, each drafted by an AI assistant (Claude Opus 5.5, in Claude Code) at the author's direction and approved by the author before the session started. Each entry gives the date, the repository, the session title, a one-line summary of the background paragraph that accompanied the brief, and the brief itself, shortened for length where it set out long lists (the full text is in each session's transcript). Sessions the author steered directly in their own chat are recorded in their commit messages (`Claude-Session:` lines) and are not listed here.

## 1. Feasibility check (2026-10-28, latc-check)

**Title:** Paper D: Lean feasibility check. **Background:** Paper D was only an idea; latc-check's Lean proofs of Paper A's results and the plan to compose its Proposition 5 reduction with complexitylib's Cook–Levin, possibly adding #P; push nothing, keep everything in the session.

**Brief:**

> Run a feasibility check for Paper D. Push nothing, commit nothing to any remote, and open no issues or pull requests; report everything in your final message.
>
> 1. Inventory: on `main`, `formal-lean-more` and `formal-lean-prop5` of latc-check, list the Lean files, the toolchain, the Mathlib version, the statements proved, and any `sorry`/`axiom`. Build each branch as it stands and report the result.
> 2. Version alignment: clone complexitylib-v1 (and check for a newer complexitylib repository by the same author), report its Lean and Mathlib versions and whether it builds, and determine the smallest set of changes needed to build our three branches and complexitylib in one Lake project on one toolchain (try upgrading ours or downgrading to theirs); actually attempt it and report how many files needed changes and which errors remain.
> 3. Composability: read complexitylib's definitions of SAT, NP, polynomial-time reductions and its Cook–Levin statement, and our Proposition 5 reduction. Report whether our reduction can be stated as a reduction in complexitylib's model (machine model, encodings, polynomial-time bound), what is missing, and a sketch of the theorem statements Paper D would prove. If easy, prove one small bridging lemma as a proof of concept.
> 4. #P literature check: search the web, Lean Zulip archives, Mathlib, Isabelle AFP, Coq/Rocq and HOL libraries for any formalisation of #P, #P-completeness, Valiant's theorem, or parsimonious reductions from SAT, published or announced after early 2025. Report what exists, with links and dates, and whether the #P part would still be new.
> 5. Estimate: give an effort estimate for (a) NP/coNP-completeness end to end and (b) adding #P-completeness, with the main risks. Say plainly if the composition looks impractical.
>
> Final message: a concise report with sections 1–5 and a recommendation (go / go with a reduced scope / no-go).

## 2. Cold-build test (2026-10-28, latc-complexity)

**Title:** latc-complexity: cold-clone build test. **Background:** the project at 676d7a9 had only been built in a session that reused compiled dependencies; a cold build was untested.

**Brief:**

> Test a cold build of this repository exactly as its README instructs, starting from nothing.
>
> 1. Start from a fresh clone in an empty directory, with no existing `.lake`, Mathlib cache or other build products. Install the toolchain the README names.
> 2. Follow the README's build steps literally. Record each command, its wall-clock time, and the disk used at the end.
> 3. Report whether `lake exe cache get` fetches Mathlib from the cache, which packages compile from source and how long each takes, the final `lake build` result, and the axiom audit output (the standard three axioms only, no `sorryAx`).
> 4. If the build fails or a README step is wrong or missing, find the minimal fix and verify it by a clean rebuild. Do not change any Lean file.
> 5. You may commit and push to `main` only a README update (corrected build steps if needed, plus the measured cold-build time and disk use).

## 3. Tractable cases and binary index (2026-10-28, latc-complexity)

**Title:** Paper D: tractable cases and binary index. **Background:** the project at d632d01 with its hardness, adequacy, #P and conditional monotone results; the author approved (1) the tractable side and (3) removing the unary attribute index.

**Brief:**

> Prove the tractable cases and remove the unary attribute index, keep the build clean, and push to `main`.
>
> 1. Tractable cases in complexitylib's Turing-machine model, each with an adequacy statement to `Latc.missing`: (a) no constraints: deciding completeness (and M(T₀) ≠ ∅) is in polynomial time, with ∏ dᵢ handled carefully since it can be exponential in the input length; (b) a fixed number k of attributes: deciding completeness is in polynomial time, stating the degree's dependence on k; (c) if cheap, the counting versions. Write the theorem statements in a short note first and check them against the hardness theorems, so the boundary is visible in one place.
> 2. Binary attribute index: encode the attribute index in binary and re-prove polynomial time for the lookups, keeping the unary theorems and adding binary versions. If the binary lookup cannot be certified, stop and report the missing lemma.
> 3. Update the axiom audit and the README; full `lake build` with 0 errors and warnings, standard axioms only.
> 4. Commit and push to `main`.

## 4. Fact-check of theorems and references (2026-10-29, latc-complexity)

**Title:** Paper D: fact-check theorems and references. **Background:** the paper's outline named theorems and references to verify before drafting.

**Brief:**

> Fact-check Paper D's theorem names and references, write the results to `docs/paper-facts.md`, and push to `main`.
>
> 1. Theorems: for every name the outline cites and every theorem the README's tables cite, report whether it exists under that name (file, line), its exact Lean statement, a one-sentence plain-English reading, and its axiom audit line; flag wrong names; group by the paper's sections; give line counts.
> 2. References: for each listed work (Gäher and Kunze; Balbach; Gamboa and Cowles; the Coq Library of Complexity Theory; Karp21; Carneiro; Valiant 1979, both papers; Provan and Ball 1983; Cook 1971; Senellart and Gnatenko; CSLib; complexitylib; Calvanese et al. 2016; Arora and Barak), find the authoritative record from the publisher, DBLP, AFP or arXiv page, with a BibTeX entry, marked confirmed or not found; never guess a field.
> 3. Novelty: search for any work proving decision-table completeness, or rule-set coverage under domain constraints, NP-, coNP- or #P-complete; report it with links, or say plainly that none was found.
> 4. Commit `docs/paper-facts.md` and `docs/paper-refs.bib` and push to `main`.

## 5. Port to the JAR template (2026-10-31, latc-complexity)

**Title:** Paper D: port the draft to JAR's template. **Background:** the author changed the target from ITP 2027 to the Journal of Automated Reasoning; a format port only.

**Brief:**

> Port Paper D to the Journal of Automated Reasoning's LaTeX template with no change of content, and push to `main`.
>
> 1. JAR's requirements: read its submission guidelines and report the template, reference style, length limit, review model, preprint policy, mandatory statements and title page, quoting the guidelines; never guess a rule.
> 2. Port: create `paper/jar/` with the Springer Nature template and a `main.tex` ported from `paper/main.tex`, keeping every sentence, theorem statement, listing, table, figure and reference; add the mandatory statements as `[AUTHOR TO APPROVE]` placeholders prefilled from the existing draft.
> 3. Build, fixing layout only, and write `paper/jar/FIDELITY.md` comparing both PDFs' text.
> 4. Update `paper/README.md`; commit and push to `main`.

## 6. JAR revision after the referee read (2026-11-01, latc-complexity)

**Title:** Paper D: JAR revision after the referee read. **Background:** an independent referee read recommended a major revision, approved in full by the author; JAR's guidelines as read on 2026-11-01.

**Brief (summary of its items; the full text set out each item in detail):**

> Revise Paper D's JAR version on a new branch `jar-revision` and list every new or changed sentence for the author's approval; do not merge into `main`. Lean: prove a `fromSAT` shape lemma (Boolean domains, empty T₀) and state hardness on that class; record every cited name with its qualified name; full build and audit. Text: D1, a full engineering section including how the AI system was used; D2, an appendix of trusted definitions verbatim; D3, the restricted-problem convention; D4, release preparation (`RELEASE.md`, data availability, a single build); D5, informal claims marked uniformly; D6, the abstract credits the earlier paper argument; D7, attribution of the amplification technique and comparison with Senellart and Gnatenko; minor items 1–13; Statements and Declarations as placeholders. Then build, write `paper/jar/CHANGES-FOR-APPROVAL.md`, and push the branch.
