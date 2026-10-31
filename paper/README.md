# Paper D, first draft

"Machine-Checked Complexity of Decision-Table Completeness in Lean", planned as an ITP 2027
short paper. `main.tex` is the first full draft (2026-10-31), in the LIPIcs class
`lipics-v2021`, written from this repository at commit `011cd1a` and from
`../docs/paper-facts.md`, which records the statement, file and line of every theorem it cites.

## Build

With a TeX Live installation that includes `lipics-v2021` (TeX Live 2021 or later):

```bash
latexmk -pdf main.tex
```

The bibliography is `../docs/paper-refs.bib` (the verified references) plus `extra.bib`.

## Not yet checked

* The draft has **not been compiled**: no TeX installation was available in the session that
  wrote it. Expect small LaTeX fixes, in particular to the Unicode-to-math mapping of the Lean
  listings (`literate=` in the preamble).
* `../docs/paper-refs.bib` uses `@software` for two entries, which BibTeX's `plainurl` style does
  not know; it falls back to `@misc` with a warning.
* Page count against the ITP 2027 short-paper limit, once the call is out.
* The open items listed at the top of `main.tex`.
