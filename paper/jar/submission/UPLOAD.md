# Paper D: upload to the Journal of Automated Reasoning

The files to submit Paper D, "Machine-Checked Complexity of Decision-Table Completeness in Lean",
to the Journal of Automated Reasoning (Springer, single-blind review), built on 2026-11-01 from
`paper/jar/main.tex` at commit `c76fbfc` (the approved text, unchanged).

## Files

| File | What it is |
|---|---|
| `PaperD-JAR.pdf` | The compiled manuscript, 32 pages (main text pp. 1–20, Statements and Declarations p. 21, appendices pp. 21–27, references pp. 28–32). |
| `PaperD-JAR-source.zip` | The self-contained LaTeX source: `main.tex`, `sn-jnl.cls`, `sn-mathphys-num.bst`, `paper-refs.bib`, `extra.bib`, `main.bbl`. The paper has no figure or listing files. The only difference from `paper/jar/main.tex` is the `\bibliography` line, which names the two `.bib` files in the same directory (`\bibliography{paper-refs,extra}`). |
| Cover letter | Supplied by the author separately. It is not in this repository. |

Build of the zip: unzip into an empty directory and run `pdflatex main` two or three times.
`main.bbl` is included, so BibTeX is not needed. A third pass clears the "Label(s) may have
changed" warning left after the second pass. Running `latexmk -pdf main` without `main.bbl` also
works, because BibTeX regenerates the same file. Tested with pdfTeX 1.40.25 (TeX Live 2023).

SHA-256:

```
252babd517ec2d96f675f66cb3b54bc6e9c753c1ec4db1b05b6e8c594c225238  PaperD-JAR.pdf
1ad2ca92a0431c1a3f88acc47e13653e9dd1a17291e86acedb0a541c54178261  PaperD-JAR-source.zip
```

## What to upload where

Start from "Submit manuscript" on the journal's Springer page. The file-type names below are the
usual ones in Springer's submission systems; choose the nearest item the form offers.

1. **Manuscript**: `PaperD-JAR.pdf`. This is the PDF of the compiled output that JAR's guidelines ask for.
2. **LaTeX source files**: `PaperD-JAR-source.zip`. Some systems unpack the zip and compile it. If the
   system asks which file is the main one, choose `main.tex`.
3. **Cover letter**: the letter the author prepared separately.

Article type: original research article. Review is single-blind, so the manuscript keeps the
author's name.

## Metadata for the form

**Title**

Machine-Checked Complexity of Decision-Table Completeness in Lean

(Running title in the manuscript: Machine-Checked Complexity of Decision-Table Completeness.)

**Author**

Carlos A. Russell (corresponding author)
- Email: carlos.a.russell@gmail.com
- ORCID: 0009-0003-3741-0230 (enter it in the form, because the `sn-jnl` class does not print ORCIDs)
- Affiliation: Independent Researcher, Buenos Aires, Argentina

**Abstract** (225 words in the source, 227 in the PDF text, depending on how the inline formula splits; the LaTeX is converted to plain text here)

A decision table is complete when every combination of its declared condition values that the
domain constraints allow is covered by a row. We prove in Lean 4, over multi-tape Turing
machines and with no unproved assumptions beyond the definitions themselves, that for
finite-domain decision tables with clause constraints and rows that are complete condition
tuples, deciding whether some combination is missing is NP-complete, deciding completeness is
coNP-complete, and counting the missing combinations is #P-complete, all already for Boolean
domains and empty tables. An adequacy theorem ties these word problems to the set-based
definitions of an existing formalisation of decision-table completion, so the results speak
about the original objects. Complementary polynomial-time results locate the hardness: all three
problems are polynomial without constraints, and with a fixed number of attributes, where one
machine runs within c (|x|+1)^(en+e) on instances with n attributes, for some constants c and e.
For monotone two-literal constraints, counting the missing combinations remains #P-complete
under reductions with a single oracle call; for this we give a new formal proof, in the same
Turing-machine model, of a one-call version of Valiant's theorem on #Monotone-2SAT. We also
report how the development was engineered and how an AI system was used to write it. The
classification was first argued on paper in the author's earlier work, which is under review;
every proof here is self-contained.

**Keywords** (6)

decision tables; completeness; coNP-completeness; #P-completeness; Lean 4; Cook–Levin theorem

If the form asks for a classification, the manuscript's source comment gives the ACM 2012 classes
Theory of computation → Problems, reductions and completeness; Theory of computation → Logic and
verification.

**Funding**

No funding was received for this work.

**Competing interests** (as in the paper's Statements and Declarations; the reference numbers are
the paper's)

The author is a co-author of the 2021 paper that introduced the LATC decision-table completion
method, which the author's earlier work [4] re-examines. The author has no other competing
interests to declare. (The 2021 paper is [45].)

- [4] Russell, C.A.: Where Declared Domains Are Lost: LATC, DMN Analysers and Public DMN Models.
  Under review at Data & Knowledge Engineering (2026).
- [45] Raggio, R.A., Russell, C.A.: Business rules (BR); expert systems (KBS); LATC algorithm: A
  proposal for functional integration. International Journal of Scientific & Engineering
  Research 12(1), 576–596 (2021).

**Author contribution** (as in the paper)

C.A.R. is the sole author, set the research questions and the task descriptions, reviewed the
definitions and the text, and is responsible for the whole work; the Lean proofs and the text
were drafted with an AI system, as described in Section 10.6.

**Ethics approval, consent to participate, consent for publication, materials availability**

Not applicable.

**Data availability**

No data were generated or analysed beyond the Lean source code described under Code
availability. The decision-table model it builds on is archived as latc-check 0.1.0
(https://doi.org/10.5281/zenodo.23646699).

**Code availability**

latc-complexity 1.0, MIT licence: https://github.com/carlosalbertorussell/latc-complexity,
archived on Zenodo with **DOI 10.5281/zenodo.23860668** (https://doi.org/10.5281/zenodo.23860668).

**Use of generative AI**

Documented in Section 10.6 of the manuscript ("How an AI system was used").
