# Paper D, revised draft

"Machine-Checked Complexity of Decision-Table Completeness in Lean", planned as an ITP 2027
paper. `main.tex` is the revised draft (2026-10-31), restructured as a regular paper after
four referee reports, in the LIPIcs class
`lipics-v2021`, written from this repository at commit `3b6f523` and from
`../docs/paper-facts.md`, which records the statement, file and line of every theorem it cites.

## Build

With a TeX Live installation that includes `lipics-v2021` (TeX Live 2021 or later):

```bash
latexmk -pdf main.tex
```

The bibliography is `../docs/paper-refs.bib` (the verified references) plus `extra.bib`.

## Journal of Automated Reasoning version

On 2026-10-31 the target became the Journal of Automated Reasoning (Springer). `jar/` holds
the same paper in the Springer Nature LaTeX template (`sn-jnl.cls` and `sn-mathphys-num.bst`
from the December 2024 template package, downloaded from
<https://www.springernature.com/gp/authors/campaigns/latex-author-support>):

* `jar/main.tex` was first generated from `main.tex` by `jar/port.py`. Since the JAR revision of
  2026-11-01 (branch `jar-revision`) the two versions diverge: `jar/main.tex` is edited directly,
  and `port.py`, `fidelity.py` and `FIDELITY.md` describe only the earlier, generated version.
* `jar/CHANGES-FOR-APPROVAL.md` lists every change of the JAR revision (item, location, old and
  new text) and every open `[AUTHOR: …]` question. In `jar/main.tex`, a comment `% [rev X]` marks
  each changed paragraph.
* The Statements and Declarations at the end of `jar/main.tex` are placeholders marked
  `[AUTHOR TO APPROVE]`.

Build (the template files are in `jar/`, so no extra `TEXINPUTS` is needed):

```bash
cd jar && latexmk -pdf main.tex
```

On 2026-11-01, with the TeX Live 2023/Debian packages listed below plus `texlive-bibtex-extra`,
the revised `jar/main.tex` gives 32 pages (main text to page 20, Statements and Declarations on page 21, appendices 21 to 27, references 28 to 32) with no errors, no undefined references or citations
and no overfull boxes. BibTeX warns that the style does not know `@software` (two entries). JAR's
guidelines (read 2026-11-01): single-blind review, no page limit stated, an abstract of 150–250
words, 4–6 keywords, a Statements and Declarations section, use of LLMs documented in the methods,
a data availability statement, numbered references with DOIs, LaTeX source and PDF.

To redo the fidelity check of the earlier, generated version, build the LIPIcs version as below and run

```bash
python3 jar/fidelity.py <directory of the built LIPIcs main.tex, main.bbl, main.pdf> jar
```

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
  `texlive-publishers` lacks; put it on `TEXINPUTS`. `latexmk -pdf main.tex` gives 16 pages
  (10 sections, references, two appendices) with no errors, no undefined references or
  citations, and no overfull boxes. BibTeX warns that `plainurl` does not know `@software`.
* `../docs/paper-refs.bib` uses `@software` for two entries, which BibTeX's `plainurl` style does
  not know; it falls back to `@misc` with a warning.
* Page count against the ITP 2027 short-paper limit, once the call is out.
* The open items listed at the top of `main.tex`.
