# Paper D, first draft

"Machine-Checked Complexity of Decision-Table Completeness in Lean", planned as an ITP 2027
paper. `main.tex` is the revised draft (2026-10-31), restructured as a regular paper after
four referee reports, in the LIPIcs class
`lipics-v2021`, written from this repository at commit `242311b` and from
`../docs/paper-facts.md`, which records the statement, file and line of every theorem it cites.

## Build

With a TeX Live installation that includes `lipics-v2021` (TeX Live 2021 or later):

```bash
latexmk -pdf main.tex
```

The bibliography is `../docs/paper-refs.bib` (the verified references) plus `extra.bib`.

## Reading copy

`draft.md` is a Markdown rendering of `main.tex` for reading on screen, made with pandoc
(citations resolved from the same bibliography). Regenerate it after editing `main.tex`:

```bash
python3 tomd.py
```

`main.tex` is the source; do not edit `draft.md` by hand.

## Not yet checked

* **Compiled** on 2026-10-31 with pdfTeX 1.40.25 (TeX Live 2023/Debian; packages
  `texlive-latex-extra`, `texlive-publishers`, `texlive-science`, `texlive-fonts-extra`,
  `texlive-plain-generic`, `lmodern`, `cm-super`) and `lipics-v2021.cls` v3.1.3 (2023/05/12) from
  Dagstuhl's [styles repository](https://github.com/dagstuhl-publishing/styles), which Debian's
  `texlive-publishers` lacks; put it on `TEXINPUTS`. `latexmk -pdf main.tex` gives 13 pages
  (10 sections, references, two appendices) with no errors, no undefined references or
  citations, and no overfull boxes. BibTeX warns that `plainurl` does not know `@software`.
* `../docs/paper-refs.bib` uses `@software` for two entries, which BibTeX's `plainurl` style does
  not know; it falls back to `@misc` with a warning.
* Page count against the ITP 2027 short-paper limit, once the call is out.
* The open items listed at the top of `main.tex`.
