# Paper D (JAR version): changes for the author's approval

Branch `jar-revision`, 2026-11-01. Every change to `paper/jar/main.tex` made by the JAR revision is listed below, by item of the referee read of 2026-10-31 (D1–D7 major, m1–m13 minor, SD for the Statements and Declarations). Nothing is approved yet. In `main.tex`, a comment `% [rev X]` precedes each changed paragraph; it can be deleted after approval.

The list was generated from a paragraph-level comparison of `main.tex` before the revision (commit `c609312`) and after it, and then checked by hand. For a changed paragraph, only the sentences that differ are shown: **Old** is the text removed, **New** the text that replaces it (an empty side means a pure deletion or addition). New and deleted paragraphs are shown in full. Text is LaTeX source.

Other files changed by the revision (not paper text, listed for completeness): `LatcComplexity/Restricted.lean` (new), `LatcComplexity.lean`, `LatcComplexity/Axioms.lean` (D5, Lean); `docs/paper-facts.md` (m3, m13, sources of m2); `README.md` (m9, new module, audit); `RELEASE.md` (D4, new); `paper/extra.bib` (three entries: m7, m13, D7); `paper/README.md`.

**Number of changes: 72** (paragraphs or headings), grouped as follows.

| Item | Subject | Changes |
|---|---|---|
| D1 | Engineering section (effort, Complexitylib gaps, fun_prop, instance-dependent bound, reusable lemmas, module table, listings, AI use) | 15 |
| D2 | Appendix of trusted definitions, verbatim | 4 |
| D3 | Convention: a restricted problem contains its restriction; promise versions | 3 |
| D4 | Release preparation, data availability, single build in the paper | 7 |
| D5 | Informal claims marked the same way in text and Table 2; new Lean lemma cited | 9 |
| D6 | Abstract: earlier paper argument acknowledged; proofs self-contained; length and keywords | 2 |
| D7 | Pendant-leaf technique, comparison with Senellart and Gnatenko, contribution as a new formal proof | 4 |
| m1 | Notation clashes (d, x, S, V) | 6 |
| m2 | Primary sources read; citations corrected | 1 |
| m6 | The _unary forms listed; claim about both encodings narrowed | 2 |
| m8 | Boolean model moved to the artifact appendix | 4 |
| m10 | Generative-AI statement adapted to Springer's policy | 2 |
| m12 | Sentences reworked (style rule; referee sentences) | 4 |
| m13 | LatcFormal/ checked against Zenodo 0.1.0; Mathlib TM2ComputableInPolyTime cited | 1 |
| SD | Statements and Declarations placeholders | 8 |
| m3 | Fact-file names (Lean step; `docs/paper-facts.md`) | no paper text |

## Open questions for the author

Every `[AUTHOR: …]` question and `[AUTHOR TO APPROVE …]` placeholder in `main.tex`, in order, with its line:

1. (line 532, Monotone two-literal constraints and Valiant's theorem) [AUTHOR: the full text of Creignou and Hermann could not be read; this sentence rests on Hermann's CP~2001 survey.]
2. (line 540, Monotone two-literal constraints and Valiant's theorem) [AUTHOR: attribute pendant-leaf amplification. Neither Senellart and Gnatenko's library nor any source we could read credits it to anyone; Provan and Ball (1983), Vadhan (2001) and Greenhill (2000) could not be read.]
3. (line 705, Where the hardness comes from) [AUTHOR: the JCSS version could not be read; this rests on the PODS~1997 version, whose Theorem~1 states it.]
4. (line 773, Related work) [AUTHOR: read in the 2013 University of Alberta technical report of the same title; the TDSC version could not be read.]
5. (line 779, Related work) [AUTHOR: only the abstract of Kapur et al.\ could be read.]
6. (line 882, Engineering the development) [AUTHOR: the repository records no working hours; give the person-hours, or confirm that only lines, commits and dates are reported.]
7. (line 918, Size and effort per part) [AUTHOR: confirm that the three parts were developed in parallel sessions.]
8. (line 1015, Polynomial time by automation) [AUTHOR: confirm the timeouts; the repository records the remedy and is silent on the failure.]
9. (line 1108, How an AI system was used) [AUTHOR: model version and dates of use]
10. (line 1115, How an AI system was used) [AUTHOR: state what you wrote or edited yourself, if anything.]
11. (line 1121, How an AI system was used) [AUTHOR: confirm that you set every task description; are they archived, and may they be published with the artifact?]
12. (line 1125, How an AI system was used) [AUTHOR: describe how you reviewed the definitions, for example line by line against latc-check's model.]
13. (line 1130, How an AI system was used) [AUTHOR: say who found it.]
14. (line 1133, How an AI system was used) [AUTHOR: state which of these reports were produced by the AI system and which by people.]
15. (line 1136, How an AI system was used) [AUTHOR: confirm that you verified every reference yourself.]
16. (line 1139, How an AI system was used) [AUTHOR TO APPROVE]
17. (line 1173, Funding) [AUTHOR TO APPROVE: No funding was received for this work.]
18. (line 1176, Competing interests) [AUTHOR TO APPROVE: The author is a co-author of the 2021 paper that introduced the LATC decision-table completion method, which the author's earlier work~\cite{PaperA} re-examines. The author has no other competing interests to declare.]
19. (line 1178, Competing interests) [AUTHOR: give the full reference of the 2021 LATC paper, which the repository does not contain.]
20. (line 1182, Ethics approval and consent to participate) [AUTHOR TO APPROVE: Not applicable.]
21. (line 1185, Consent for publication) [AUTHOR TO APPROVE: Not applicable.]
22. (line 1189, Data availability) [AUTHOR TO APPROVE: No data were generated or analysed beyond the Lean source code described under Code availability. The decision-table model it builds on is archived as latc-check~0.1.0 (\url{https://doi.org/10.5281/zenodo.23646699}).]
23. (line 1194, Materials availability) [AUTHOR TO APPROVE: Not applicable.]
24. (line 1198, Code availability) [AUTHOR TO APPROVE: The Lean development latc-complexity, described in \Cref{app:artifact}, will be released as version~1.0 under the MIT licence at \url{https://github.com/carlosalbertorussell/latc-complexity} and archived on Zenodo with the DOI [DOI at release]. The release follows the steps of \texttt{RELEASE.md} in the repository.]
25. (line 1204, Author contribution) [AUTHOR TO APPROVE: C.A.R. is the sole author. He set the research questions and the task descriptions, reviewed the definitions and the text, and is responsible for the whole work; the Lean proofs and the text were drafted with an AI system, as described in \Cref{sec:ai}.]
26. (line 1209, Use of generative AI) [AUTHOR TO APPROVE: The use of an AI system is documented in \Cref{sec:ai}.]
27. (m12) The referee's report named sentences to rework; the prompt of this revision listed only the item. The revision reworked every sentence of the forms "not X but Y" and "X, not Y" and the sentences it touched for other items (marked m12). Which sentences did the referee name, if others?
28. (m5) The item says "§6 Statement 2". In the JAR numbering Statement 2 of the explicit degree is in Section 7 ("Where the hardness comes from"); Section 6 is the monotone section. The revision aligned Statement 2 in Section 7 and put the convention of D3 in Section 6. Confirm that this is what was meant.
29. (D4) `[DOI at release]` stands for the Zenodo DOI of v1.0 in the Code availability statement and Appendix C; `RELEASE.md` says how to obtain it. Nothing has been released.
30. (m2) Sources not read in full: Creignou and Hermann 1996 (not reached; a survey by Hermann was read); Kapur et al. 1991 (abstract only); the JCSS version of Krentel 1988 (the 1985 technical report was read); the TDSC version of Elmallah and Gouda (the 2013 technical report was read); the JCSS version of Papadimitriou and Yannakakis 1999 (the PODS 1997 version was read); the origin of pendant-leaf amplification (Provan and Ball 1983, Vadhan 2001, Greenhill 2000 not reached). Details in `docs/paper-facts.md`, section "Sources read for the JAR revision".

## Index: where each item is addressed

A paragraph can serve several items; it is listed once below, under its first item, and here under all of them.

- **D1** (Engineering section (effort, Complexitylib gaps, fun_prop, instance-dependent bound, reusable lemmas, module table, listings, AI use)): D5.30, D1.1, D1.2, D1.3, D1.4, D1.5, D1.6, D1.7, D1.8, D1.9, D1.10, D1.11, D1.12, D1.13, D1.14, D1.15
- **D2** (Appendix of trusted definitions, verbatim): D2.16, D2.17, D2.18, D2.19
- **D3** (Convention: a restricted problem contains its restriction; promise versions): D3.20, D3.21, D3.22
- **D4** (Release preparation, data availability, single build in the paper): D4.23, D4.24, D4.25, D4.26, D4.27, D4.28, D4.29
- **D5** (Informal claims marked the same way in text and Table 2; new Lean lemma cited): D5.30, D2.16, D5.31, D5.32, D5.33, D5.34, m1.45, D5.35, D5.36, D5.37, D5.38
- **D6** (Abstract: earlier paper argument acknowledged; proofs self-contained; length and keywords): D6.39, D6.40
- **D7** (Pendant-leaf technique, comparison with Senellart and Gnatenko, contribution as a new formal proof): D5.30, D7.41, D7.42, D7.43, D7.44
- **m1** (Notation clashes (d, x, S, V)): m1.45, m1.46, m1.47, m1.48, m1.49, m1.50
- **m2** (Primary sources read; citations corrected): D5.36, D7.42, m2.51
- **m4** (How the two bound-framework names relate): m1.45
- **m5** (Statement 2 aligned with its Lean statement): m1.45
- **m6** (The _unary forms listed; claim about both encodings narrowed): m6.52, m6.53
- **m7** (Classical W[1]-hardness cited): m1.45
- **m8** (Boolean model moved to the artifact appendix): m8.54, m8.55, m8.56, m8.57
- **m9** (Development history moved to the README): D4.26
- **m10** (Generative-AI statement adapted to Springer's policy): D1.11, m10.58, m10.59
- **m11** ("coNP" throughout): D5.36, m2.51
- **m12** (Sentences reworked (style rule; referee sentences)): D5.32, m1.45, D5.36, m6.52, m8.54, m12.60, m12.61, m12.62, m13.64, m12.63
- **m13** (LatcFormal/ checked against Zenodo 0.1.0; Mathlib TM2ComputableInPolyTime cited): D1.12, m13.64
- **SD** (Statements and Declarations placeholders): SD.65, SD.66, SD.67, SD.68, SD.69, SD.70, SD.71, SD.72
- **m3** (fact-file names): no paper text; `docs/paper-facts.md`, section "JAR revision". See also m4.

## Changes

### D1: Engineering section (effort, Complexitylib gaps, fun_prop, instance-dependent bound, reusable lemmas, module table, listings, AI use)

**D1.1** — changed, location: Introduction

- Old: «\Cref{sec:prelim} recalls Complexitylib and latc-check, \Cref{sec:encoding} fixes the input language, \Cref{sec:decision,sec:counting,sec:monotone,sec:boundary} prove the results, \Cref{sec:related} discusses related work and \Cref{sec:formal} the formalisation. \Cref{app:statements} lists the main Lean statements and \Cref{app:artifact} the artifact.»
- New: «\Cref{sec:prelim} recalls Complexitylib and latc-check, \Cref{sec:encoding} fixes the input language, \Cref{sec:decision,sec:counting,sec:monotone,sec:boundary} prove the results, \Cref{sec:related} discusses related work, \Cref{sec:formal} the trusted base and \Cref{sec:engineering} the engineering of the development. \Cref{app:statements} lists the main Lean statements, \Cref{app:definitions} the trusted definitions and \Cref{app:artifact} the artifact.»

**D1.2** — new, location: Engineering the development

- Old: `(none)`
- New:

```latex
\label{sec:engineering}

This section reports what the formalisation took and what it taught. Its figures come from the
repository at the commit described in \Cref{app:artifact} and from the commit history, which is
summarised in the repository's README. [AUTHOR: the repository records no working hours; give
the person-hours, or confirm that only lines, commits and dates are reported.]
```

**D1.3** — new, location: Size and effort per part

- Old: `(none)`
- New:

```latex
\label{sec:effort}

\Cref{tab:modules} lists the modules. The development has 4\,520 lines of Lean in 15 files,
besides the two axiom-audit files (383 lines), with 345 theorem and lemma declarations; it sits
on latc-check's model, copied unchanged into \texttt{LatcFormal/}. By lines, the effort fell
unevenly on four parts:
\begin{itemize}
\item \emph{Encodings and the decision problems}, 411 lines (\texttt{General.lean} with the unary
  index, \texttt{Binary.lean} with the binary one). Most of it is the certificate check and its
  polynomial time; the binary index cost 206 lines, mainly the re-encoding and the shifted lookup
  of \Cref{sec:encoding}.
\item \emph{Adequacy}, 152 lines (\texttt{Adequacy.lean}): the map from a state to a tuple of
  \lstinline{Fin} values, its injectivity and the two adequacy theorems.
\item \emph{The explicit degree}, 692 lines (\texttt{ExplicitDegree.lean}), for a statement that
  is a corollary on paper: almost as much as the 825 lines of encodings, adequacy and counting
  together (\texttt{General}, \texttt{Binary}, \texttt{Adequacy}, \texttt{CountingGeneral}).
  The cost is bookkeeping: every composition step must carry an explicit bound
  (\Cref{sec:instance-bounds}).
\item \emph{Valiant's theorem}, 1\,140 lines in four files, the largest part; 518 of them
  (\texttt{Valiant/Counting.lean}) prove the bijection between models and independent sets of
  size~$K$.
\end{itemize}
The tractable side (\texttt{Tractable.lean}, 1\,099 lines) is the largest single file: the
enumeration of candidate states needs an induction on $k$ for its polynomial time, and the
counting with classes adds the partition of each domain. The repository records commits, not
hours. Its first Lean commit (28 October 2026) holds the Boolean model and the general NP- and
coNP-completeness; adequacy, the two counting files and the conditional monotone case followed
the same day, the binary index and the tractable side on 29 October, and the three remaining
results on 31 October, after a written plan (\texttt{docs/gaps-plan.md}): counting with at most
$k$ attributes, Valiant's theorem and the explicit degree, committed 14, 31 and 35 minutes after
the plan. Commit times bound neither when the work on a part began nor the author's time
reviewing it. [AUTHOR: confirm that the three parts were developed in parallel sessions.]
```

**D1.4** — new, location: Size and effort per part

- Old: `(none)`
- New:

```latex
\begin{table}[t]
\caption{The modules of \texttt{LatcComplexity/}: lines, theorem and lemma declarations, and
definitions (\texttt{def}, \texttt{abbrev}, \texttt{instance}). The two audit files
are not counted in the total.}
\label{tab:modules}
\centering\small
\begin{tabular}{L{0.27\textwidth}R{0.07\textwidth}R{0.08\textwidth}R{0.06\textwidth}L{0.36\textwidth}}
\hline
file & lines & thms & defs & contents \\
\hline
\texttt{Bridge.lean} & 160 & 16 & 11 & Boolean model; agreement with latc-check's clauses \\
\texttt{General.lean} & 205 & 15 & 13 & instances, \texttt{encInst}, NP- and coNP-completeness \\
\texttt{Adequacy.lean} & 152 & 13 & 6 & the table an instance denotes; adequacy \\
\texttt{Counting.lean} & 140 & 10 & 2 & Boolean model: counting in \#P \\
\texttt{CountingGeneral.lean} & 262 & 20 & 7 & \textit{missingCount}: \#P-completeness \\
\texttt{Monotone.lean} & 238 & 18 & 10 & one-call reductions; monotone shape, conditional case \\
\texttt{Binary.lean} & 206 & 22 & 3 & \texttt{encInstBin}; every result above for it \\
\texttt{Tractable.lean} & 1\,099 & 81 & 26 & no constraints; at most $k$ attributes \\
\texttt{ExplicitDegree.lean} & 692 & 46 & 7 & explicit degree, uniform in $k$ \\
\texttt{Restricted.lean} & 102 & 10 & 6 & hardness on Boolean domains, $T_0 = \emptyset$ \\
\texttt{Valiant/Gadget.lean} & 227 & 19 & 14 & the graph, $\psi$, \textit{post}; polynomial time \\
\texttt{Valiant/Counting.lean} & 518 & 38 & 7 & models and independent sets of size $K$ \\
\texttt{Valiant/Pendant.lean} & 195 & 9 & 0 & the model count of $\psi$ \\
\texttt{Valiant/OneCall.lean} & 200 & 14 & 0 & the digit; one-call Valiant \\
\texttt{Valiant/AnyTable.lean} & 124 & 14 & 2 & \textit{countMissingMonotone2} \\
\hline
total & 4\,520 & 345 & 114 & \\
\hline
\end{tabular}
\end{table}
```

**D1.5** — new, location: What Complexitylib provided and what it lacked

- Old: `(none)`
- New:

```latex
\label{sec:gaps}

Complexitylib provided the machine model, the encodings, the classes, the Cook--Levin theorem
with its parsimonious form, and a large stock of polynomial-time lemmas, among them binary
arithmetic (multiplication, division, remainder, powers of two), list folds, the binary list
lookup \lstinline{listGetD_binary}, a fold whose intermediate results grow boundedly
(\lstinline{foldlWithInput_of_bounded_growth}, used for the binary product of the domain sizes),
the padding lemma \lstinline{mem_SharpP_of_polyTime_length}, the bound framework
\lstinline{ComputableTidilyInO} and promise problems. The development needed five things the
library did not have, and worked around each:
\begin{enumerate}
\item \emph{Reductions with one oracle call.} The library has many-one, parsimonious and
  Turing reductions. \Cref{def:onecall} is defined in \texttt{Monotone.lean}, with its
  composition with parsimonious reductions on either side
  (\lstinline{ParsimoniousReducible.trans_oneCall},
  \lstinline{OneCallSharpPHard.trans_parsimonious}).
\item \emph{\#P-hardness beyond the SAT family.} The library has \#SAT and \#3SAT, a decision
  problem for independent sets, and no counting problem on graphs. The plan was to port
  Senellart and Gnatenko's chain of three reductions through counting problems on graphs; the
  proof instead builds the graph of \Cref{sec:monotone} directly as a CNF over numbered vertices
  and needs no graph library.
\item \emph{Explicit bounds.} The composition lemmas for polynomial time are existential: a
  composed bound exists, but its degree is not visible. The explicit degree goes through
  \lstinline{ComputableTidilyInO} instead (\Cref{sec:instance-bounds}).
\item \emph{Uniform constants.} The constants of the case-split and constant-output lemmas depend
  on the machines involved, which is why the per-$k$ machine with constants independent of~$k$
  is not proved (\Cref{sec:boundary}).
\item \emph{Reading a list at a binary index.} The first encoding wrote the attribute index in
  unary, because the list lookup used for the certificate check
  (\lstinline{ComputableTidilyInPolyTime.getElem?}) takes a unary position. The binary encoding
  then used the library's \lstinline{listGetD_binary}, with the values shifted by one so that
  the default of an out-of-range lookup matches no value.
\end{enumerate}
The library changes daily and sits on a release-candidate toolchain, so the development pins
one commit and one toolchain (\Cref{app:artifact}).
```

**D1.6** — new, location: Polynomial time by automation

- Old: `(none)`
- New:

```latex
\label{sec:funprop}

Complexitylib registers its polynomial-time lemmas with Mathlib's \lstinline{fun_prop} tactic,
which proves a polynomial-time claim for a term built from registered functions by composing
their lemmas. The library's documentation asks that local definitions be unfolded so that
\lstinline{fun_prop} can see their bodies. Most polynomial-time proofs of the development are
then three lines, as for the reduction from SAT (\Cref{lst:fromsat}). The \lstinline{tidy}
forms are machines that restore their tapes, which composition needs; \lstinline{.of_tidy}
returns to the plain notion.

\begin{lstlisting}[float=t,caption={The polynomial time of the SAT reduction (\texttt{General.lean}). The two \texttt{have} lines bring library lemmas for the dense relabelling and the number of variables into the context; \texttt{fun\_prop} composes them with the lemmas for pairs, lists, \texttt{replicate}, \texttt{map} and \texttt{if}.},label={lst:fromsat}]
theorem fromSAT_polyTime : ComputableInPolyTime fromSAT encCNF encInst := by
  have h1 := (CNF.computableInPolyTime_denseRelabel_unary encNat).tidy
  have h2 := SAT.computableInPolyTime_numVars.tidy
  refine .of_tidy ?_
  unfold fromSAT toCond
  fun_prop
\end{lstlisting}
```

**D1.7** — new, location: Polynomial time by automation

- Old: `(none)`
- New:

```latex
Unfolding everything does not scale. For the graph of \Cref{sec:monotone}, whose vertices are
numbered by Cantor pairing ($3\cdot\mathrm{pair}(i,b)$ for the value vertices, and similar codes
for occurrences and leaves), \lstinline{fun_prop} timed out on the unfolded
construction. [AUTHOR: confirm the timeouts; the repository records the remedy and is
silent on the failure.] The remedy was to give each helper, the three vertex codes and the edge, a lemma
in two forms: one for the helper itself, proved by unfolding, and a composable one, registered
with \lstinline{fun_prop}, for the helper applied to any polynomial-time arguments
(\Cref{lst:vv}). \lstinline{fun_prop} then stops at the helper and never unfolds it again.

\begin{lstlisting}[float=t,caption={A helper with its composable lemma (\texttt{Valiant/Gadget.lean}). The attribute \texttt{@[fun\_prop]} registers the second theorem, so that \texttt{fun\_prop} treats \texttt{vv} as a primitive.},label={lst:vv}]
theorem vv_polyTime : ComputableTidilyInPolyTime (fun p : ℕ × Bool => vv p.1 p.2)
    (encPair encUnary encBool) encUnary := by
  unfold vv
  fun_prop

@[fun_prop]
theorem vv_polyTime' {α : Type} {input : α ↪ List Bool} {f : α → ℕ} {g : α → Bool}
    (hf : ComputableTidilyInPolyTime f input encUnary)
    (hg : ComputableTidilyInPolyTime g input encBool) :
    ComputableTidilyInPolyTime (fun a => vv (f a) (g a)) input encUnary :=
  vv_polyTime.comp (hf.prod hg)
\end{lstlisting}
```

**D1.8** — new, location: Polynomial time by automation

- Old: `(none)`
- New:

```latex
Automation stops where the size of intermediate values matters. Proofs by hand were needed for
the binary product of the domain sizes (a fold whose intermediate products are bounded by the
input, through \lstinline{foldlWithInput_of_bounded_growth}), the enumeration of candidate
states (by induction on~$k$), the explicit bounds, and the arithmetic of Valiant's
post-processing.
```

**D1.9** — new, location: An instance-dependent time bound

- Old: `(none)`
- New:

```latex
\label{sec:instance-bounds}

The bound $c\,(|x|+1)^{en+e}$ of \Cref{sec:boundary} depends on the instance through its number
of attributes~$n$, which is not a function of $|x|$ alone. It is built in three steps.
\begin{enumerate}
\item \emph{A class of bounds.} \lstinline{XPBounded size n T} says that
  $T(a) \le c\,(\mathit{size}(a)+1)^{e\,(n(a)+1)}$ for some constants (\Cref{lst:xp}). It is
  closed under sums, constant factors and fixed powers, and constant factors are absorbed into
  the exponent, since $|x| \ge 1$ (\lstinline{mul_pow_le_pow_add}).
\item \emph{An explicitly bounded enumeration.} All candidate states of $n$ lists are built by a
  left fold, \lstinline{allSections}, whose intermediate states have encodings of length at most
  $4\,(|L|+1)^{n+2}$ (\lstinline{length_state_le}); Complexitylib's fold lemma for
  \lstinline{ComputableTidilyInO} then gives \lstinline{allSections_inO}. Each polynomial-time
  piece enters with a bound $(|x|+1)^{e}$ (\lstinline{inO_pow_of_polyTime}), and
  \lstinline{pipeline_inO} composes a polynomial-time list builder, the enumeration and a
  polynomial-time test into one \lstinline{ComputableTidilyInO} statement with
  \lstinline{XPBounded} time and space.
\item \emph{Explicit constants.} \lstinline{timeAndSpace_of_inO_xp} turns such a statement into
  \lstinline{ComputableTidilyInTimeAndSpace} with the bound $c\,(|x|+1)^{e n + e}$, the form of
  the theorems.
\end{enumerate}

\begin{lstlisting}[float=t,caption={The class of bounds, and the step to explicit constants (\texttt{ExplicitDegree.lean}; statements only). The hypothesis \texttt{h} has a hidden constant factor; the conclusion has none.},label={lst:xp}]
def XPBounded {α : Type} (size n T : α → ℕ) : Prop :=
  ∃ c e, ∀ a, T a ≤ c * (size a + 1) ^ (e * (n a + 1))

theorem timeAndSpace_of_inO_xp {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} {T S n : α → ℕ} (h : ComputableTidilyInO f encIn encOut T S)
    (hT : XPBounded (fun a => (encIn a).length) n T)
    (hS : XPBounded (fun a => (encIn a).length) n S) :
    ∃ c d, ComputableTidilyInTimeAndSpace f encIn encOut
      (fun a => c * ((encIn a).length + 1) ^ (d * n a + d))
      (fun a => c * ((encIn a).length + 1) ^ (d * n a + d))
\end{lstlisting}
```

**D1.10** — new, location: Reusable lemmas

- Old: `(none)`
- New:

```latex
\label{sec:reusable}

Some results are independent of decision tables and could serve other developments on
Complexitylib, or be offered upstream; apart from \Cref{def:onecall} they use only
Complexitylib's notions.
\begin{itemize}
\item One-call reductions and their compositions with parsimonious ones
  (\lstinline{OneCallReducible}, \lstinline{ParsimoniousReducible.trans_oneCall},
  \lstinline{OneCallSharpPHard.trans_parsimonious}, \lstinline{SharpPHard.oneCallSharpPHard}).
\item One-call \#P-hardness of \#Monotone-2SAT (\lstinline{sharpMonotone2SAT_oneCallSharpPHard}),
  with the parsimonious encoding of the models of any CNF as the independent sets of size $K$ of
  a graph (\lstinline{modelCount_eq_card}) and the digit lemma for sums of powers
  (\lstinline{digit}).
\item The explicit-bound toolkit: \lstinline{XPBounded} with its closure lemmas,
  \lstinline{inO_pow_of_polyTime}, \lstinline{timeAndSpace_of_inO_xp}, and the bounded
  enumeration of all sections of a list of lists (\lstinline{allSections_inO}).
\item Size facts for encodings, such as \lstinline{length_encList_le_of_inDomains}: a list
  bounded entrywise by another is encoded in no more bits.
\end{itemize}
```

**D1.11** — new, location: How an AI system was used (also m10)

- Old: `(none)`
- New:

```latex
\label{sec:ai}

The development and this paper were written with an AI system, Claude (Anthropic), used through
Claude Code [AUTHOR: model version and dates of use]. This subsection records how, from the
repository's history; JAR asks that such use be documented in the methods of the paper.
\begin{itemize}
\item \emph{Who wrote what.} All 80 commits of the repository up to the revision of this paper
  were made by the AI system, in ten sessions, each commit message naming its session. Every
  Lean file of \texttt{LatcComplexity/}, every document of the repository and the text of this
  paper were drafted by it; \texttt{LatcFormal/} is copied from latc-check.
  [AUTHOR: state what you wrote or edited yourself, if anything.]
\item \emph{Briefs.} Each part of the development was done in its own session from a written
  task description set by the author: the initial development (one session, from the Boolean
  model to the conditional monotone case), the binary index with the tractable side, each of the
  three results of the plan \texttt{docs/gaps-plan.md}, the monotone count for arbitrary tables,
  the tightened shape tests, and the shape lemma of \Cref{sec:decision}. The plan is in the
  repository; the task descriptions are not. [AUTHOR: confirm that you set every task
  description; are they archived, and may they be published with the artifact?]
\item \emph{Review of definitions.} Lean checks every proof, so the human review that matters is
  the review of the trusted definitions, which \Cref{app:definitions} collects.
  [AUTHOR: describe how you reviewed the definitions, for example line by line against
  latc-check's model.] One defect of a definition was found and fixed: the first monotone shape
  tests accepted conditions on attributes that do not exist, so that a clause $[(0,1),(0,1)]$
  over zero attributes passed the test with count~$0$ and the statement ``the all-ones state is
  valid'' failed; the tests now require every attribute index to be declared, and no theorem
  statement changed. [AUTHOR: say who found it.]
\item \emph{Iterations on the paper.} The commit messages record four referee reports on an
  early draft, an independent audit and two further referee reads, each followed by a revision,
  and a referee read of the JAR version that led to the present revision. [AUTHOR: state which
  of these reports were produced by the AI system and which by people.] The AI system also
  searched for related work and checked bibliographic records against the publishers' records.
  [AUTHOR: confirm that you verified every reference yourself.]
\item \emph{Accountability.} The author takes responsibility for the content of the paper and of
  the development. An AI system does not meet the criteria for authorship and is not an author.
  [AUTHOR TO APPROVE]
\end{itemize}
```

**D1.12** — changed, location: Artifact and reproducibility (also m13)

- Old: «\subparagraph*{Contents.} The development is the directory \texttt{LatcComplexity/} of the repository latc-complexity: 4\,788 lines of Lean in 16 files, 4\,418 without the two axiom-audit files, on top of latc-check's model, copied unchanged into \texttt{LatcFormal/}. The README lists every main theorem with its statement, and \texttt{docs/paper-facts.md} records the file and line of every theorem this paper cites.»
- New: «\subparagraph*{Contents.} The development is the directory \texttt{LatcComplexity/} of the repository latc-complexity: 4\,903 lines of Lean in 17 files, 4\,520 without the two axiom-audit files (\Cref{tab:modules}), on top of latc-check's model in \texttt{LatcFormal/}. The eleven files of \texttt{LatcFormal/} and its root file are byte-identical to the folder \texttt{formal/} of the archived release latc-check~0.1.0~\cite{latc_check_0_1_0}. The README lists every main theorem with its statement, and \texttt{docs/paper-facts.md} records the fully qualified name, file and line of every name this paper cites.»

**D1.13** — deleted, location: The formalisation

- Old:

```latex
\subparagraph*{Engineering.}
The development has 4\,418 lines of Lean, besides the audit files. Mathlib's
\lstinline{fun_prop} tactic, with Complexitylib's polynomial-time lemmas, discharged most composition steps of polynomial-time proofs. Proofs by hand
were needed where the size of intermediate values matters: the binary product of the domain
sizes, the enumeration of candidate states (by induction on~$k$), the explicit bounds of
\Cref{sec:boundary}, and the arithmetic of Valiant's post-processing. For the graph of
\Cref{sec:monotone}, \lstinline{fun_prop} timed out until each vertex-numbering and edge helper
had its own composable polynomial-time lemma. Reading a list at a binary index needed a library
lemma, \lstinline{listGetD_binary}, rather than a new proof. The development pins one commit of
Complexitylib, a library that changes daily on a release-candidate toolchain; a version of the
development taken before the last two monotone changes also built unchanged against a later
commit on the next toolchain (\Cref{app:artifact}).
```
- New: `(deleted)`

**D1.14** — changed, location: Section 9 heading

- Old: «\section{The formalisation}»
- New: «\section{Trusted base and audit}»

**D1.15** — new, location: New Section 10 and its subsections

- Old: `(none)`
- New:

```latex
\section{Engineering the development}; \subsection{Size and effort per part}; \subsection{What Complexitylib provided and what it lacked}; \subsection{Polynomial time by automation}; \subsection{An instance-dependent time bound}; \subsection{Reusable lemmas}; \subsection{How an AI system was used}
```

### D2: Appendix of trusted definitions, verbatim

**D2.16** — changed, location: Trusted base and audit (also D5)

- Old: «\subparagraph*{Trust.} The axiom audit prints the axioms of 318 of the development's 335 theorem and lemma declarations, among them every theorem this paper cites (the other 17 are helper lemmas used by audited theorems); each uses only \lstinline{propext}, \lstinline{Classical.choice} and \lstinline{Quot.sound}, or fewer, and none uses \lstinline{sorryAx}.»
- New: «\subparagraph*{Trust.} The axiom audit prints the axioms of 328 of the development's 345 theorem and lemma declarations, among them every theorem this paper cites (the other 17 are helper lemmas used by audited theorems); each uses only \lstinline{propext}, \lstinline{Classical.choice} and \lstinline{Quot.sound}, or fewer, and none uses \lstinline{sorryAx}.»
- Old: «Complexitylib's definitions of machines, running time and space (\lstinline{ComputableTidilyInTimeAndSpace}, which carries the explicit-degree claims), encodings, the classes P, NP, coNP and \#P, the reductions and the notions of completeness built on them, and its CNF semantics and \#SAT; our encodings of instances; \Cref{def:onecall}; and the problem definitions themselves: \textit{MissingNonempty} with \lstinline{InDomains}, \lstinline{CondHolds} and \lstinline{Valid}, \textit{missingCount}, the monotone shape tests and \textit{SharpMonotone2SAT}.»
- New: «Complexitylib's definitions of machines, running time and space (\lstinline{ComputableTidilyInTimeAndSpace}, which carries the explicit-degree claims), encodings, the classes P, NP, coNP and \#P, the reductions, promise problems and the notions of completeness built on them, and its CNF semantics and \#SAT; our encodings of instances; \Cref{def:onecall}; and the problem definitions themselves: \textit{MissingNonempty} with \lstinline{InDomains}, \lstinline{CondHolds} and \lstinline{Valid}, \textit{missingCount}, the monotone shape tests, \textit{SharpMonotone2SAT} and \textit{BoolEmpty}. \Cref{app:definitions} copies every one of our trusted definitions verbatim from the source.»

**D2.17** — new, location: Trusted definitions

- Old: `(none)`
- New:

```latex
\label{app:definitions}

The definitions below are the ones a reader must trust beyond Complexitylib, CSLib and Mathlib
(\Cref{sec:formal}). They are copied verbatim from the source, with their documentation
comments, file by file. Namespaces: \lstinline{Latc} for latc-check's model,
\lstinline{Latc.PaperD.General} for the rest except \lstinline{pos2AnyB} and
\lstinline{countMissingMonotone2}, which are in \lstinline{Latc.PaperD.Valiant}.

\subparagraph*{latc-check's model (\texttt{LatcFormal/Basic.lean}).}
Here \lstinline{ι} is a finite type of attributes, \lstinline{D i} a finite domain for each, and
\lstinline{C} a decidable predicate on tuples.
\begin{lstlisting}
/-- The valid space 𝒱 = {x ∈ 𝒟 : c(x) for all c ∈ C} (Section 3.1). -/
def validSpace : Finset (∀ i, D i) := univ.filter C

/-- The missing set M(T₀) = 𝒱 ∖ cond(T₀) (Section 3.2). -/
def missing (T : Finset (∀ i, D i)) : Finset (∀ i, D i) := validSpace C \ T
\end{lstlisting}

\subparagraph*{Instances and the decision problems (\texttt{General.lean}).}
\begin{lstlisting}
/-- A condition Aᵢ = v, as the pair `(i, v)`. -/
abbrev Cond := ℕ × ℕ

/-- An instance: domain sizes, clause constraints, and the condition tuples of T₀. -/
abbrev Inst := List ℕ × (List (List Cond) × List (List ℕ))

/-- Instances: binary domain sizes, values and rows; unary attribute indices. -/
abbrev encInst : Inst ↪ List Bool :=
  encPair (encList encNat) (encPair (encList (encList (encPair encUnary encNat)))
    (encList (encList encNat)))

/-- `s` is a state of the declared domains `d`: one value per attribute, inside its domain. -/
def InDomains (d s : List ℕ) : Prop := List.Forall₂ (· < ·) s d

/-- The state `s` satisfies the condition Aᵢ = v. -/
def CondHolds (s : List ℕ) (a : Cond) : Prop := s[a.1]? = some a.2

/-- The state `s` satisfies every clause constraint of `S`. -/
def Valid (S : List (List Cond)) (s : List ℕ) : Prop := ∀ c ∈ S, ∃ a ∈ c, CondHolds s a

/-- M(T₀) is non-empty: some valid state of the declared domains is not a condition tuple
of T₀. -/
def MissingNonempty : Set Inst :=
  {I | ∃ s, InDomains I.1 s ∧ Valid I.2.1 s ∧ s ∉ I.2.2}

/-- T₀ is complete: M(T₀) = ∅. -/
def Complete : Set Inst := MissingNonemptyᶜ
\end{lstlisting}

\subparagraph*{The binary encoding (\texttt{Binary.lean}).}
\begin{lstlisting}
/-- Instances with every number in binary, the attribute index of a condition included. -/
abbrev encInstBin : Inst ↪ List Bool :=
  encPair (encList encNat) (encPair (encList (encList (encPair encNat encNat)))
    (encList (encList encNat)))
\end{lstlisting}

\subparagraph*{The table an instance denotes (\texttt{Adequacy.lean}).}
\begin{lstlisting}
/-- The number of attributes. -/
abbrev Inst.n (I : Inst) : ℕ := I.1.length

/-- The declared domain of attribute `i`: the values `0, …, dᵢ - 1`. -/
abbrev Inst.Dom (I : Inst) (i : Fin I.n) : Type := Fin (I.1.get i)

/-- The list of values of a condition tuple. -/
def Inst.toList (I : Inst) (x : ∀ i, I.Dom i) : List ℕ := List.ofFn fun i => (x i).val

/-- The constraint predicate of the instance, on condition tuples. -/
def Inst.con (I : Inst) (x : ∀ i, I.Dom i) : Prop := Valid I.2.1 (I.toList x)

/-- The condition set of T₀: the tuples whose list of values is a row of `T`. -/
def Inst.table (I : Inst) : Finset (∀ i, I.Dom i) :=
  Finset.univ.filter fun x => I.toList x ∈ I.2.2
\end{lstlisting}

\subparagraph*{Counting (\texttt{CountingGeneral.lean}).}
\begin{lstlisting}
def missingCount (I : Inst) : ℕ := (missing I.con I.table).card
\end{lstlisting}

\subparagraph*{One-call reductions and the monotone problems (\texttt{Monotone.lean}).}
\begin{lstlisting}
/-- `f` reduces to `g` with one oracle call: `f a = post a (g (r a))` for polynomial-time `r` and
`post`, the oracle answer read in binary. -/
def OneCallReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (f : α → ℕ) (g : β → ℕ) :
    Prop :=
  ∃ (r : α → β) (post : α → ℕ → ℕ), ComputableInPolyTime r encA encB ∧
    ComputableInPolyTime (fun p : α × ℕ => post p.1 p.2) (encPair encA encNat) encNat ∧
      ∀ a, f a = post a (g (r a))

/-- Every function in `#P`, with any encoding of its instances, reduces to `g` with one call. -/
def OneCallSharpPHard (encB : β ↪ List Bool) (g : β → ℕ) : Prop :=
  ∀ ⦃α : Type⦄ (enc : α ↪ List Bool) (f : α → ℕ), f ∈ SharpP enc → OneCallReducible enc encB f g

/-- `g` is in `#P` and one-call `#P`-hard. -/
def OneCallSharpPComplete (encB : β ↪ List Bool) (g : β → ℕ) : Prop :=
  g ∈ SharpP encB ∧ OneCallSharpPHard encB g

/-- Every clause has two literals, both positive: `xᵢ ∨ xⱼ`. -/
def monotone2B (φ : CNF ℕ) : Bool := φ.all fun c => c.length == 2 && c.all (·.2)

/-- `#Monotone-2SAT`: the model count of a monotone two-literal formula; zero on other syntax. -/
def SharpMonotone2SAT (φ : CNF ℕ) : ℕ := if monotone2B φ then SharpSAT φ else 0

/-- Domains {0, 1}, clauses of two conditions with value 1 on declared attributes (index below
the number of attributes), and T₀ = ∅. -/
def pos2B (I : Inst) : Bool :=
  I.1.all (· == 2) &&
      I.2.1.all (fun c =>
        c.length == 2 && c.all (fun a => decide (a.1 < I.1.length) && a.2 == 1)) &&
    I.2.2.isEmpty

/-- |𝒱| for clause constraints of two conditions Aᵢ = 1, Aⱼ = 1 over domains {0, 1}, in
latc-check's model (`missingCount` with T₀ = ∅); zero on other syntax. -/
noncomputable def countValidMonotone2 (I : Inst) : ℕ := if pos2B I then missingCount I else 0
\end{lstlisting}

\subparagraph*{The monotone count for any table (\texttt{Valiant/AnyTable.lean}).}
\begin{lstlisting}
/-- Domains {0, 1} and clauses of two conditions with value 1 on declared attributes (index below
the number of attributes); any table T₀. -/
def pos2AnyB (I : General.Inst) : Bool :=
  I.1.all (· == 2) &&
    I.2.1.all (fun c =>
      c.length == 2 && c.all (fun a => decide (a.1 < I.1.length) && a.2 == 1))

/-- |M(T₀)| for clause constraints of two conditions Aᵢ = 1, Aⱼ = 1 over domains {0, 1}, any
table T₀, in latc-check's model; zero on other syntax. -/
noncomputable def countMissingMonotone2 (I : General.Inst) : ℕ :=
  if pos2AnyB I then missingCount I else 0
\end{lstlisting}

\subparagraph*{Boolean domains with empty tables (\texttt{Restricted.lean}).}
\begin{lstlisting}
/-- Boolean domains and an empty table: every declared domain size is 2 and T₀ has no rows. -/
def BoolEmpty : Set Inst := {I | (∀ d ∈ I.1, d = 2) ∧ I.2.2 = []}

/-- M(T₀) ≠ ∅, on Boolean domains with T₀ = ∅. -/
def MissingNonemptyBoolEmpty : Set Inst := MissingNonempty ∩ BoolEmpty

/-- M(T₀) = ∅, on Boolean domains with T₀ = ∅. -/
def CompleteBoolEmpty : Set Inst := Complete ∩ BoolEmpty

/-- The promise problem: on Boolean domains with T₀ = ∅, tell M(T₀) ≠ ∅ from M(T₀) = ∅. -/
def missingNonemptyPromise : PromiseProblem Inst :=
  (PromiseProblem.ofSet MissingNonempty).restrict BoolEmpty

/-- |M(T₀)| on Boolean domains with T₀ = ∅, and `0` on other instances. -/
def missingCountBoolEmpty (I : Inst) : ℕ := if I ∈ BoolEmpty then missingCount I else 0
\end{lstlisting}
```

**D2.18** — deleted, location: Main Lean statements

- Old:

```latex
\subparagraph*{Instances.}
\begin{lstlisting}
abbrev Cond := ℕ × ℕ
abbrev Inst := List ℕ × (List (List Cond) × List (List ℕ))
def InDomains (d s : List ℕ) : Prop := List.Forall₂ (· < ·) s d
def CondHolds (s : List ℕ) (a : Cond) : Prop := s[a.1]? = some a.2
def Valid (S : List (List Cond)) (s : List ℕ) : Prop := ∀ c ∈ S, ∃ a ∈ c, CondHolds s a
def MissingNonempty : Set Inst :=
  {I | ∃ s, InDomains I.1 s ∧ Valid I.2.1 s ∧ s ∉ I.2.2}
def Complete : Set Inst := MissingNonemptyᶜ
\end{lstlisting}
```
- New: `(deleted)`

**D2.19** — new, location: New Appendix B heading (the artifact appendix becomes C)

- Old: `(none)`
- New:

```latex
\section{Trusted definitions}
```

### D3: Convention: a restricted problem contains its restriction; promise versions

**D3.20** — new, location: Monotone two-literal constraints and Valiant's theorem

- Old: `(none)`
- New:

```latex
\subparagraph*{Restricted problems.}
A problem restricted to a class $K$ of instances is stated in this development as a problem on
all instances that contains its restriction. A restricted decision problem is the set
$\{I : I \in K \land I \in A\}$, so that its decider also checks $I \in K$, and a restricted
count returns $0$ outside~$K$, as Complexitylib's \#3SAT does. The counts of this section follow
the convention, and so do the restricted sets of \Cref{sec:decision,sec:boundary}. It is
harmless because every class used is decidable in polynomial time: the shape tests below
(\lstinline{pos2B_polyTime_bin}, \lstinline{pos2AnyB_polyTime_bin}), \textit{BoolEmpty}, ``no
constraints'' and ``at most $k$ attributes'', the last three plain comparisons on the input. The
\emph{promise version} of a restricted problem asks for the right answer only on the instances
of~$K$. A polynomial-time decider for the restricted set solves the promise version, so the
upper bounds of \Cref{sec:boundary} hold for both forms; conversely, a solver for the promise
version, run after the test for~$K$, decides the restricted set\informal. The hardness proofs
map their inputs into~$K$, so they show the promise versions hard as well. Lean states promise
versions in two places: \lstinline{missingNonemptyPromise_npHard_bin} (\Cref{sec:decision}),
and Statement~2 of the explicit degree (\Cref{sec:boundary}), whose input type is the subtype of
instances with at most $k$ attributes. For the counts below, the promise version is the count
on the instances that pass the shape test; the reduction leaves that class only on formulas
where both sides are~$0$ by the convention, and the promise versions of the counts are not
stated separately in Lean\informal.
```

**D3.21** — changed, location: Monotone two-literal constraints and Valiant's theorem

- Old: «As with Complexitylib's \#3SAT, the three functions are total and return~$0$ on inputs of any other shape; the shape tests are polynomial-time.»
- New: «As with Complexitylib's \#3SAT, the three functions are total and return~$0$ on inputs of any other shape.»

**D3.22** — changed, location: Where the hardness comes from

- Old: `(none)`
- New: «As in \Cref{sec:monotone}, each restricted problem below contains its restriction.»

### D4: Release preparation, data availability, single build in the paper

**D4.23** — changed, location: Conclusion

- Old: «\bmhead{Supplementary information} The Lean development, latc-complexity.»
- New: «\bmhead{Supplementary information} The Lean development, latc-complexity, described in \Cref{app:artifact}.»

**D4.24** — new, location: Statements and Declarations

- Old: `(none)`
- New:

```latex
\bmhead{Data availability}
[AUTHOR TO APPROVE: No data were generated or analysed beyond the Lean source code described
under Code availability. The decision-table model it builds on is archived as latc-check~0.1.0
(\url{https://doi.org/10.5281/zenodo.23646699}).]
```

**D4.25** — changed, location: Statements and Declarations

- Old: «\bmhead{Code availability} The Lean development, latc-complexity, described in \Cref{app:artifact}. [AUTHOR TO APPROVE: repository URL and archive DOI (Zenodo), or an anonymous mirror for review.]»
- New: «\bmhead{Code availability} [AUTHOR TO APPROVE: The Lean development latc-complexity, described in \Cref{app:artifact}, will be released as version~1.0 under the MIT licence at \url{https://github.com/carlosalbertorussell/latc-complexity} and archived on Zenodo with the DOI [DOI at release]. The release follows the steps of \texttt{RELEASE.md} in the repository.]»

**D4.26** — changed, location: Artifact and reproducibility (also m9)

- Old: «The pin was kept throughout the development. Complexitylib had just been rewritten on CSLib; the earlier version, which Russell~\cite{PaperA} cites, is a separate repository with a different API.»
- New: «The earlier, pre-CSLib version of Complexitylib, which Russell~\cite{PaperA} cites, is a separate repository with a different API.»

**D4.27** — new, location: Artifact and reproducibility

- Old: `(none)`
- New:

```latex
\subparagraph*{Build and audit.}
The build reported here is a cold build of commit \texttt{0ea3170}, whose Lean files are
those of this paper, made on 1 November 2026 on a Linux x86-64 machine with four cores, in a
fresh clone with no \texttt{\textasciitilde/.elan}, \texttt{.lake} or Mathlib cache, with Lean
\texttt{4.36.0-rc1}, Lake 5.0.0 and elan 4.2.4. \texttt{lake exe cache get} downloaded the
toolchain and all 9\,047 precompiled Mathlib files in 103~s. \texttt{lake build} compiled 239
modules of CSLib and Complexitylib and the 30 modules of the repository in 217~s and ended with
\texttt{Build completed successfully (18651 jobs)}, exit code~0, no warnings and no errors; the
checkout, toolchain and caches took 11.5~GB of disk. The axiom audit, \texttt{lake env lean} on
the three audit files (\texttt{LatcComplexity/Axioms.lean}, \texttt{LatcComplexity/Valiant/Axioms.lean}
and \texttt{LatcFormal/Axioms.lean}), took 13~s and printed 397 answers: 344 use all three
standard axioms, 51 use one or two of them, 2 use none, and none uses \lstinline{sorryAx}. A
whole-word search of the \texttt{.lean} files finds \lstinline{sorry}, \texttt{admit},
\texttt{native\_decide} and \texttt{axiom} only in the \texttt{\#print axioms} commands.
```

**D4.28** — new, location: Artifact and reproducibility

- Old: `(none)`
- New:

```latex
\subparagraph*{Release.}
The repository is private during review. The file \texttt{RELEASE.md} lists the steps of the
release: tagging version~1.0, a cold build and the full audit at the tag, making the repository
public, and archiving the tag on Zenodo, whose DOI will be cited here [DOI at release]. The
commit-by-commit history of earlier builds is in the README.
```

**D4.29** — deleted, location: Artifact and reproducibility

- Old:

```latex
\subparagraph*{Build and audit.}
From a fresh clone, downloading precompiled Mathlib, \texttt{lake build} completed 18\,645 jobs
with no warnings or errors in about nine minutes on four cores, using 12\,GB of disk, at the
commit before the last theorem file was added; with that file, and with the monotone shape tests
tightened, branch builds of 18\,647 jobs were again clean (the Lean files at those branch heads
are identical to the final ones). The axiom audit (the two files \texttt{Axioms.lean} of \texttt{LatcComplexity/} and of
its subdirectory \texttt{Valiant/}) prints 318 theorems: 268 use all three standard axioms, 50
fewer, none \lstinline{sorryAx}. The development as of commit \texttt{6603497}, before the
monotone result for arbitrary rows and the tightened shape tests, also built without any change
against Complexitylib commit \texttt{b9e6241} on Lean \texttt{v4.36.0-rc2} (18\,717 jobs); the
final version was not re-tested against it. The artifact is published with the pin above,
against which the results were proved.
```
- New: `(deleted)`

### D5: Informal claims marked the same way in text and Table 2; new Lean lemma cited

**D5.30** — changed, location: Introduction (also D7, D1)

- Old: «The reductions produce only instances with Boolean domains and empty tables, so hardness holds already there (by inspection of the reduction, not as a separate Lean theorem).»
- New: «Hardness holds already for instances with Boolean domains and empty tables, a Lean theorem about the shape of the reduction (\Cref{sec:decision}).»
- Old: «\item \textbf{One-call hardness for monotone two-literal counting} (\Cref{sec:monotone}): a definition of one-call reductions in Complexitylib's model, and a one-call version of Valiant's theorem, from which counting the missing combinations stays \#P-complete under one-call reductions when every constraint is $A_i = 1 \lor A_j = 1$, for tables with arbitrary rows (hard already with none).»
- New: «\item \textbf{One-call hardness for monotone two-literal counting} (\Cref{sec:monotone}): a definition of one-call reductions in Complexitylib's model, and a new formal proof in that model of a one-call version of Valiant's theorem, by classical techniques. From it, counting the missing combinations stays \#P-complete under one-call reductions when every constraint is $A_i = 1 \lor A_j = 1$, for tables with arbitrary rows (hard already with none).»
- Old: `(none)`
- New: «\item \textbf{An account of the engineering} (\Cref{sec:engineering}): the size of each part, what Complexitylib provided and lacked, how the polynomial-time proofs were automated, how the instance-dependent bounds were kept explicit, the lemmas that could be reused, and how an AI system was used.»

**D5.31** — new, location: Introduction

- Old: `(none)`
- New:

```latex
\emph{Informal claims.} A few claims are argued on paper only and are not theorems of the
development. They are marked with a dagger, as in ``P\informal'', both in the text and in
\Cref{tab:boundary}. Every other result is a Lean theorem, cited by its name.
```

**D5.32** — changed, location: Preliminaries (also m12)

- Old: «The third is defined in this development; it is the polynomial-time metric reduction attributed to Krentel~\cite{Krentel1988}: \begin{definition}[one-call reduction] \label{def:onecall} $f$ reduces to $g$ with one call if there are polynomial-time functions $r$ and $\mathit{post}$ with $f(a) = \mathit{post}(a, g(r(a)))$ for every~$a$, where $\mathit{post}$ reads $a$ and the answer $g(r(a))$ written in binary.»
- New: «The third is defined in this development; it is the polynomial-time \emph{metric reduction} that Krentel defines between functions into $\mathbb{N}$ for optimisation problems~\cite{Krentel1988}: \begin{definition}[one-call reduction] \label{def:onecall} $f$ reduces to $g$ with one call if there are polynomial-time functions $r$ and $\mathit{post}$ with $f(a) = \mathit{post}(a, g(r(a)))$ for every~$a$, where $\mathit{post}$ reads $a$ and the answer $g(r(a))$ written in binary.»
- Old: «For a target $g$ whose values have polynomially many bits, as for every function in \#P, a one-call reduction is a polynomial-time Turing reduction making exactly one oracle query, whose answer is post-processed together with the input, and one-call hardness implies hardness under polynomial-time Turing reductions, the notion of Valiant~\cite{Valiant1979enumeration}.»
- New: «For a target $g$ whose values have polynomially many bits, as for every function in \#P, a one-call reduction is a polynomial-time Turing reduction making exactly one oracle query, whose answer is post-processed together with the input, and one-call hardness implies hardness under polynomial-time Turing reductions\informal, the notion of Valiant~\cite{Valiant1979enumeration}.»
- Old: «We use one-call hardness only for \#Monotone-2SAT, whose value is at most $2^{\#\text{variables}}$, and for a target proved to be in \#P.) Parsimonious reductions are one-call, with $\mathit{post}(a, y) = y$; so \#P-hardness implies one-call \#P-hardness, and a parsimonious reduction followed by a one-call reduction is one-call.»
- New: «We use one-call hardness only for \#Monotone-2SAT, whose value is at most $2^{\#\text{variables}}$, and for a target proved to be in \#P.) Parsimonious reductions are one-call, with $\mathit{post}(a, y) = y$ (\lstinline{ParsimoniousReducible.oneCallReducible}); so \#P-hardness implies one-call \#P-hardness (\lstinline{SharpPHard.oneCallSharpPHard}), and a parsimonious reduction followed by a one-call reduction is one-call (\lstinline{ParsimoniousReducible.trans_oneCall}).»
- Old: «One-call hardness is weaker than parsimonious hardness, which matters below: a problem whose decision version is trivial cannot be parsimoniously \#P-hard unless P~=~NP, but can be one-call \#P-hard.»
- New: «One-call hardness is weaker than parsimonious hardness, which matters below: a problem whose decision version is trivial cannot be parsimoniously \#P-hard unless P~=~NP, and can still be one-call \#P-hard.»

**D5.33** — new, location: The decision problems

- Old: `(none)`
- New:

```latex
\subparagraph*{Hardness on Boolean domains with empty tables.}
The reduction produces only instances whose domains are all $\{0,1\}$ and whose table is empty:
writing \textit{BoolEmpty} for the class of such instances, \lstinline{fromSAT_mem_boolEmpty}
states that every $\mathit{fromSAT}(\varphi)$ is in it. Hardness therefore holds already on
that class, and Lean states it under \lstinline{encInstBin}, with the convention of
\Cref{sec:monotone} that a restricted problem contains its restriction:
$\textit{MissingNonempty} \cap \textit{BoolEmpty}$ is NP-hard
(\lstinline{MissingNonemptyBoolEmpty_npHard_bin}) and $\textit{Complete} \cap
\textit{BoolEmpty}$ coNP-hard (\lstinline{CompleteBoolEmpty_coNPHard_bin}). The promise
version, which asks to tell the instances of \textit{BoolEmpty} with $M(T_0) \neq \emptyset$
from those with $M(T_0) = \emptyset$ and allows any answer elsewhere, is NP-hard as a promise
problem in Complexitylib's sense (\lstinline{missingNonemptyPromise_npHard_bin}). The counting
reduction of \Cref{thm:counting} is the same map, and gives the same for counting
(\lstinline{missingCountBoolEmpty_sharpPHard_bin}).
```

**D5.34** — changed, location: Monotone two-literal constraints and Valiant's theorem

- Old: «With rows, deciding is still polynomial, by an argument we have not formalised: a partial assignment to a positive two-literal CNF extends to a model if and only if no clause has both literals set to~$0$ (set the rest to~$1$), so backtracking lists the valid states with polynomial delay, and listing $|T|+1$ of them decides whether one is missing. So neither count can be \#P-hard under parsimonious reductions unless P~=~NP, and the right notion is the one-call reduction of \Cref{def:onecall}.»
- New: «With rows, deciding is still polynomial\informal: a partial assignment to a positive two-literal CNF extends to a model if and only if no clause has both literals set to~$0$ (set the rest to~$1$), so backtracking lists the valid states with polynomial delay, and listing $|T|+1$ of them decides whether one is missing. So neither count can be \#P-hard under parsimonious reductions unless P~=~NP\informal, and the right notion is the one-call reduction of \Cref{def:onecall}.»

**D5.35** — changed, location: Where the hardness comes from

- Old: «\begin{table}[t] \caption{Where the hardness comes from.} \label{tab:boundary} \centering\small \setlength{\tabcolsep}{5pt}% layout only (FIDELITY.md) \begin{tabular}{L{0.11\textwidth}L{0.13\textwidth}L{0.12\textwidth}L{0.15\textwidth}L{0.16\textwidth}L{0.14\textwidth}} \hline rows & constraints & attributes & deciding & counting & hardness via \\ \hline tuples & clauses & unbounded & NP-, coNP-complete & \#P-complete & many-one, parsimonious \\ tuples & none & unbounded & P & polynomial-time & -- \\ tuples & clauses & at most $k$ & P, degree $O(k)$ & polynomial-time, degree $O(k)$ & -- \\ tuples & monotone two-literal & unbounded & P (trivial if $T_0 = \emptyset$) & one-call \#P-complete & one-call \\ compact (wildcards) & none & unbounded & coNP-complete (on paper) & \#P-complete (on paper) & DNF tautology, \#SAT \\ \hline \end{tabular} \end{table}»
- New: «\begin{table}[t] \caption{Where the hardness comes from. A dagger marks a claim argued on paper only; every other entry is a Lean theorem. The hardness of the first row holds already on Boolean domains with $T_0 = \emptyset$.} \label{tab:boundary} \centering\small \setlength{\tabcolsep}{5pt}% layout only \begin{tabular}{L{0.11\textwidth}L{0.13\textwidth}L{0.12\textwidth}L{0.15\textwidth}L{0.16\textwidth}L{0.14\textwidth}} \hline rows & constraints & attributes & deciding & counting & hardness via \\ \hline tuples & clauses & unbounded & NP-, coNP-complete & \#P-complete & many-one, parsimonious \\ tuples & none & unbounded & P & polynomial-time & -- \\ tuples & clauses & at most $k$ & P, degree $O(k)$ & polynomial-time, degree $O(k)$ & -- \\ tuples & monotone two-literal & unbounded & P\informal{} (trivial if $T_0 = \emptyset$) & one-call \#P-complete & one-call \\ compact (wildcards) & none & unbounded & coNP-complete\informal & \#P-complete\informal & DNF tautology, \#SAT \\ \hline \end{tabular} \end{table}»

**D5.36** — changed, location: Related work (also m11, m12, m2)

- Old: «Both directions hold: any CNF $\varphi$ arises this way, from the wildcard rows given by the terms of $\neg\varphi$, with the uncovered tuples exactly the models of~$\varphi$.»
- New: «Both directions hold\informal: any CNF $\varphi$ arises this way, from the wildcard rows given by the terms of $\neg\varphi$, with the uncovered tuples exactly the models of~$\varphi$.»
- Old: «Elmallah and Gouda's firewall rules are compact rows over integer ranges~\cite{ElmallahGouda2017}. Thiemann and Yamada's co-NP-hardness reduction turns each clause into a row of true, false and wildcard patterns, so it already shows coNP-hardness for decision tables with wildcard rows~\cite{ThiemannYamada2026}; what this paper adds is the case of rows that are complete tuples, constraints, counting and the mechanisation. With complete tuples as rows, as here, the rows are not the source of hardness: the constraints are (\Cref{sec:boundary}).»
- New: «Elmallah and Gouda's firewall rules are compact rows of this kind: each rule tests every field against an interval of integers~\cite{ElmallahGouda2017}. Thiemann and Yamada's coNP-hardness reduction turns each clause into a row of true, false and wildcard patterns, so it already shows coNP-hardness for decision tables with wildcard rows~\cite{ThiemannYamada2026}; what this paper adds is the case of rows that are complete tuples, constraints, counting and the mechanisation. With complete tuples as rows, as here, the hardness comes from the constraints (\Cref{sec:boundary}).»

**D5.37** — new, location: Main Lean statements

- Old: `(none)`
- New:

```latex
\subparagraph*{Boolean domains with empty tables.}
\begin{lstlisting}
theorem fromSAT_mem_boolEmpty (φ : CNF ℕ) : fromSAT φ ∈ BoolEmpty
theorem MissingNonemptyBoolEmpty_npHard_bin : NPHard encInstBin MissingNonemptyBoolEmpty
theorem CompleteBoolEmpty_coNPHard_bin : coNPHard encInstBin CompleteBoolEmpty
theorem missingNonemptyPromise_npHard_bin :
    PromiseProblem.NPHard encInstBin missingNonemptyPromise
theorem missingCountBoolEmpty_sharpPHard_bin : SharpPHard encInstBin missingCountBoolEmpty
\end{lstlisting}
```

**D5.38** — deleted, location: The decision problems

- Old:

```latex
\emph{Remark.} The reduction produces only instances with domains $\{0,1\}$ and
$T_0 = \emptyset$, so hardness holds already for them; this follows from the definition of
\lstinline{fromSAT} and is not stated as a separate Lean theorem. The same holds for the counting
reduction of \Cref{thm:counting}.
```
- New: `(deleted)`

### D6: Abstract: earlier paper argument acknowledged; proofs self-contained; length and keywords

**D6.39** — changed, location: front matter

- Old: «We prove in Lean~4, over multi-tape Turing machines and with no unproved assumptions beyond the definitions themselves, that for finite-domain decision tables with clause constraints and rows that are complete condition tuples, deciding whether some combination is missing is NP-complete, deciding completeness is coNP-complete, and counting the missing combinations is \#P-complete.»
- New: «The classification below was argued on paper in the author's earlier work, which is under review; every proof here is self-contained. We prove in Lean~4, over multi-tape Turing machines and with no unproved assumptions beyond the definitions themselves, that for finite-domain decision tables with clause constraints and rows that are complete condition tuples, deciding whether some combination is missing is NP-complete, deciding completeness is coNP-complete, and counting the missing combinations is \#P-complete, all already for Boolean domains and empty tables.»
- Old: «Complementary polynomial-time results locate the hardness: all three problems are polynomial without constraints, and with a fixed number of attributes, where one machine runs within $c\,(|x|+1)^{dn+d}$ on instances with $n$ attributes, for some constants $c$ and~$d$. For monotone two-literal constraints, counting the missing combinations remains \#P-complete under reductions with a single oracle call; for this we prove a one-call version of Valiant's theorem on \#Monotone-2SAT in the same Turing-machine model.}»
- New: «Complementary polynomial-time results locate the hardness: all three problems are polynomial without constraints, and with a fixed number of attributes, where one machine runs within $c\,(|x|+1)^{en+e}$ on instances with $n$ attributes, for some constants $c$ and~$e$. For monotone two-literal constraints, counting the missing combinations remains \#P-complete under reductions with a single oracle call; for this we give a new formal proof, in the same Turing-machine model, of a one-call version of Valiant's theorem on \#Monotone-2SAT. We also report how the development was engineered and how an AI system was used to write it.}»

**D6.40** — changed, location: Introduction

- Old: «Russell~\cite{PaperA} re-examined a decision-table completion method over declared finite domains and argued, on paper, that completeness under clause constraints is coNP-complete and that counting $|M(T_0)|$ is \#P-complete (Proposition~5 there). The accompanying Lean development, latc-check~\cite{latc_check_0_1_0}, formalised the decision-table model and a combinatorial reduction from its own propositional formulas, but not the complexity classes: those need a model of computation, polynomial-time bounds and encodings, which latc-check did not have.»
- New: «Russell~\cite{PaperA}, in a paper under review, re-examined a decision-table completion method over declared finite domains and argued, on paper, that completeness under clause constraints is coNP-complete and that counting $|M(T_0)|$ is \#P-complete (Proposition~5 there). The present paper does not depend on that argument: every proof it gives is its own. The accompanying Lean development, latc-check~\cite{latc_check_0_1_0}, formalised the decision-table model and a combinatorial reduction from its own propositional formulas. It did not formalise the complexity classes, which need a model of computation, polynomial-time bounds and encodings.»

### D7: Pendant-leaf technique, comparison with Senellart and Gnatenko, contribution as a new formal proof

**D7.41** — changed, location: Introduction

- Old: «Senellart--Gnatenko (logical model) & new in Complexitylib's model \\ \hline \end{tabular} \end{table}»
- New: «Senellart--Gnatenko (one call, logical model, Lean library) & new formal proof in Complexitylib's model \\ \hline \end{tabular} \end{table}»

**D7.42** — new, location: Monotone two-literal constraints and Valiant's theorem (also m2)

- Old: `(none)`
- New:

```latex
Valiant proved \#Monotone-2SAT \#P-complete under polynomial-time Turing
reductions~\cite{Valiant1979enumeration}. Its relation $x \lor y$ is not affine, so it also lies
on the hard side of Creignou and Hermann's dichotomy for counting generalised
satisfiability~\cite{CreignouHermann1996}; the hard cases of that dichotomy are themselves
obtained from Valiant's result, so it gives no second proof. [AUTHOR: the full text of Creignou
and Hermann could not be read; this sentence rests on Hermann's CP~2001 survey.] Senellart and
Gnatenko's Lean library~\cite{DescriptiveComplexityLib} machine-checks a one-call form in its
descriptive-complexity setting, by a chain of four reductions: from \#1-in-SAT to counting
cliques, to counting independent sets of a given size, to counting all independent sets with one
call, by attaching pendant leaves to every vertex and reading one digit of the answer, and to
\#Monotone-2SAT. Our proof uses the same two devices, a parsimonious encoding of models as
independent sets of a fixed size, and pendant-leaf amplification followed by digit extraction.
[AUTHOR: attribute pendant-leaf amplification. Neither Senellart and Gnatenko's library nor any
source we could read credits it to anyone; Provan and Ball (1983), Vadhan (2001) and Greenhill
(2000) could not be read.] It differs from theirs in fusing the chain into one reduction from
\#SAT, through the ``first true literal'' graph below, which handles any CNF and needs no
counting problem on graphs. What it adds is a new formal proof in Complexitylib's model, where
every step is a polynomial-time Turing-machine computation; it claims no new mathematics. Since
\#SAT is \#P-hard under parsimonious reductions, by \Cref{def:onecall} it suffices to reduce
\#SAT to \#Monotone-2SAT with one call.
```

**D7.43** — changed, location: Conclusion

- Old: «For decision tables whose rows are complete tuples, completeness under clause constraints is coNP-complete, finding a missing combination NP-complete, and counting them \#P-complete, with machine-checked proofs on Turing machines that apply to latc-check's set-based definitions.»
- New: «For decision tables whose rows are complete tuples, completeness under clause constraints is coNP-complete, finding a missing combination NP-complete, and counting them \#P-complete, with machine-checked proofs on Turing machines that apply to latc-check's set-based definitions and hold already for Boolean domains and empty tables.»
- Old: «For monotone two-literal constraints, counting the missing combinations stays \#P-complete under one-call reductions, on tables with arbitrary rows and already with none, by a one-call version of Valiant's theorem proved in the same model.»
- New: «For monotone two-literal constraints, counting the missing combinations stays \#P-complete under one-call reductions, on tables with arbitrary rows and already with none, by a new formal proof of a one-call version of Valiant's theorem in the same model.»

**D7.44** — deleted, location: Monotone two-literal constraints and Valiant's theorem

- Old:

```latex
Valiant proved \#Monotone-2SAT \#P-complete under polynomial-time Turing reductions,
interpolating over many oracle calls; since its relation $x \lor y$ is not affine, it also lies on
the hard side of Creignou and Hermann's dichotomy for counting generalised
satisfiability~\cite{CreignouHermann1996}. Senellart and Gnatenko machine-check the one-call form in their
descriptive-complexity setting~\cite{SenellartGnatenko2026}. We prove it in
Complexitylib's model by one reduction from \#SAT, which is \#P-hard parsimoniously, so by
\Cref{def:onecall} it suffices to reduce \#SAT to \#Monotone-2SAT with one call.
```
- New: `(deleted)`

### m1: Notation clashes (d, x, S, V)

**m1.45** — changed, location: Where the hardness comes from (also m4, m12, m5, m7, D5)

- Old: «We bound its form: the exponent is linear in the number of attributes, with constants that are proved to exist but not computed. We use Complexitylib's \lstinline{ComputableTidilyInO}, which keeps explicit bound functions and a single constant through composition, case splits and folds. The following are proved, each for non-emptiness, completeness and counting, each for time and space, under \lstinline{encInstBin}: \begin{enumerate} \item \emph{One machine for all instances.} There are $c, d$ such that one machine decides non-emptiness on every instance within $c\,(|x|+1)^{dn+d}$, where $n$ is the instance's number of attributes (\lstinline{missingNonempty_explicitDegree};»
- New: «We bound its form: the exponent is linear in the number of attributes, with constants that are proved to exist and are not computed. The constants are written $c$, $e$, $e_0$ and~$e_1$ below; the Lean statements call the exponent constants \lstinline{d}, \lstinline{d₀} and \lstinline{d₁}. Two names of bound frameworks occur. The statements use \lstinline{ComputableTidilyInTimeAndSpace} \lstinline{f encIn encOut t s} (from CSLib), which says that one machine computes $f$ on every input $a$ within exactly the time $t(a)$ and the space $s(a)$. The proofs use Complexitylib's \lstinline{ComputableTidilyInO} \lstinline{f encIn encOut T S}, which is defined from it: for some constant~$c$, the bounds $c\,(T(a)+1)$ and $c\,(S(a)+1)$ hold and the output has length at most $c\,(S(a)+1)$. The second form keeps explicit bound functions and a single constant through composition, case splits and folds; the lemma \lstinline{timeAndSpace_of_inO_xp} converts it to the first at the end (\Cref{sec:engineering}). The following are proved, each for non-emptiness, completeness and counting, each for time and space, under \lstinline{encInstBin}: \begin{enumerate} \item \emph{One machine for all instances.} There are $c, e$ such that one machine decides non-emptiness on every instance within $c\,(|x|+1)^{en+e}$, where $n$ is the instance's number of attributes (\lstinline{missingNonempty_explicitDegree};»
- Old: «\item \emph{Uniform constants in $k$}, a direct corollary of~1 (\lstinline{missingNonemptyFixedAttrs_uniform}). There are $c, d_0, d_1$ such that for every $k$, on instances with at most $k$ attributes, the problem is decided within $c\,(|x|+1)^{d_0 k + d_1}$ (the machine is the one of~1, restricted). \item \emph{$k$ in the input.} There are $c, d$ such that one machine, given $k$ in unary and an instance, decides ``at most $k$ attributes and $M(T_0) \neq \emptyset$'' within $c\,(|(k,x)|+1)^{dk+d}$ (\lstinline{missingNonemptyWithBound_explicitDegree}).»
- New: «\item \emph{Uniform constants in $k$} (\lstinline{missingNonemptyFixedAttrs_uniform}). There are $c, e_0, e_1$ such that for every $k$ some machine decides the problem within $c\,(|x|+1)^{e_0 k + e_1}$ on every instance with at most $k$ attributes. Its inputs are the instances with at most $k$ attributes, encoded by \lstinline{encInstBin}: the Lean input type is the subtype \lstinline|{I : Inst // I.n ≤ k}|, so nothing is claimed about other inputs, and the statement is a promise version in the sense of \Cref{sec:monotone}. The proof takes the machine of~1 for every~$k$; the statement asserts only that a machine exists for each~$k$. \item \emph{$k$ in the input.} There are $c, e$ such that one machine, given $k$ in unary and an instance, decides ``at most $k$ attributes and $M(T_0) \neq \emptyset$'' within $c\,(|(k,x)|+1)^{ek+e}$ (\lstinline{missingNonemptyWithBound_explicitDegree}).»
- Old: «This is an XP bound, $|x|^{O(k)}$, not fixed-parameter tractability, $f(k) \cdot |x|^{O(1)}$, and FPT is unlikely: an argument we have not formalised reduces Multicoloured Clique, which is W[1]-hard (\cite[Chapter~13]{CyganEtAl2015}), to non-emptiness with $k$ attributes.»
- New: «This is an XP bound, $|x|^{O(k)}$; fixed-parameter tractability would need $f(k) \cdot |x|^{O(1)}$, and it is unlikely\informal. With $k$ attributes, non-emptiness is a constraint satisfaction problem with $k$ variables, and such problems are W[1]-hard with the number of variables as parameter: Papadimitriou and Yannakakis prove it for conjunctive queries, by a reduction from Clique~\cite{PapadimitriouYannakakis1999}. [AUTHOR: the JCSS version could not be read; this rests on the PODS~1997 version, whose Theorem~1 states it.] An argument we have not formalised reduces Multicolored Clique, which is W[1]-complete~\cite[Theorem~13.25]{CyganEtAl2015}, to non-emptiness with $k$ attributes directly\informal.»

**m1.46** — changed, location: Preliminaries

- Old: «The valid space is $\mathcal{V} = \{x \in \mathcal{D} : C(x)\}$, the missing set is $M(T_0) = \mathcal{V} \setminus T_0$, and the table is complete when $M(T_0) = \emptyset$. In Lean these are \lstinline{validSpace C} and \lstinline{missing C T}, both \lstinline{Finset}s, so duplicate rows play no role; this model, not latc-check's own reduction, is what the present development reuses.»
- New: «The valid space is $\mathcal{V} = \{\tau \in \mathcal{D} : C(\tau)\}$, the missing set is $M(T_0) = \mathcal{V} \setminus T_0$, and the table is complete when $M(T_0) = \emptyset$. In Lean these are \lstinline{validSpace C} and \lstinline{missing C T}, both \lstinline{Finset}s, so duplicate rows play no role. The present development reuses this model; it does not use latc-check's own reduction.»

**m1.47** — changed, location: Instances, encoding and adequacy

- Old: «The input size $|x|$ in every polynomial bound below is the length of this encoding.»
- New: «The input size $|x|$ in every polynomial bound below is the length of this encoding of the instance~$x$.»

**m1.48** — changed, location: Monotone two-literal constraints and Valiant's theorem

- Old: «\subparagraph*{Step 2: a monotone formula.} Let $V$ be the number of vertices of $G$, and give every vertex $t = n + 1$ fresh pendant leaves.»
- New: «\subparagraph*{Step 2: a monotone formula.} Let $\nu$ be the number of vertices of $G$, and give every vertex $t = n + 1$ fresh pendant leaves.»
- Old: «An independent set of the graph with leaves consists of an independent set $S$ of $G$ together with any subset of the leaves of the $V - |S|$ vertices outside~$S$, so \[ x \;=\;»
- New: «An independent set of the graph with leaves consists of an independent set $J$ of $G$ together with any subset of the leaves of the $\nu - |J|$ vertices outside~$J$, so \[ y \;=\;»
- Old: «\sum_{S \text{ independent in } G} 2^{\,t\,(V - |S|)} \qquad (\text{\lstinline{modelCount_psi}}).»
- New: «\sum_{J \text{ independent in } G} 2^{\,t\,(\nu - |J|)} \qquad (\text{\lstinline{modelCount_psi}}).»

**m1.49** — changed, location: Monotone two-literal constraints and Valiant's theorem

- Old: «\subparagraph*{Step 3: one digit.} Write $x$ in base $2^t$. Multiply by $2^{tK}$ and divide by $2^{tV}$: \[ \Bigl\lfloor \frac{x \cdot 2^{tK}}{2^{tV}} \Bigr\rfloor = \Bigl\lfloor \sum_{S} 2^{\,t\,(K - |S|)} \Bigr\rfloor . \] Since $|S| \le K$, every exponent is a nonnegative multiple of $t$, so the sum is an integer and the floor is exact. Sets with $|S| < K$ contribute multiples of $2^t$, and sets with $|S| = K$ contribute $1$ each.»
- New: «\subparagraph*{Step 3: one digit.} Write $y$ in base $2^t$. Multiply by $2^{tK}$ and divide by $2^{t\nu}$: \[ \Bigl\lfloor \frac{y \cdot 2^{tK}}{2^{t\nu}} \Bigr\rfloor = \Bigl\lfloor \sum_{J} 2^{\,t\,(K - |J|)} \Bigr\rfloor . \] Since $|J| \le K$, every exponent is a nonnegative multiple of $t$, so the sum is an integer and the floor is exact. Sets with $|J| < K$ contribute multiples of $2^t$, and sets with $|J| = K$ contribute $1$ each.»
- Old: «\Bigl\lfloor \frac{x \cdot 2^{tK}}{2^{tV}} \Bigr\rfloor \bmod 2^t \qquad (\text{\lstinline{sharpSAT_eq_post}}). \] Multiplying before dividing avoids computing $V - K$, which can be negative when $\varphi$ has empty clauses ($K$ counts them, $V$ does not). Then every term $2^{t(K-|S|)}$ has $|S| < K$, so the quotient is a multiple of $2^t$ and the digit is $0$, which is correct.»
- New: «\Bigl\lfloor \frac{y \cdot 2^{tK}}{2^{t\nu}} \Bigr\rfloor \bmod 2^t \qquad (\text{\lstinline{sharpSAT_eq_post}}). \] Multiplying before dividing avoids computing $\nu - K$, which can be negative when $\varphi$ has empty clauses ($K$ counts them, $\nu$ does not). Then every term $2^{t(K-|J|)}$ has $|J| < K$, so the quotient is a multiple of $2^t$ and the digit is $0$, which is correct.»

**m1.50** — changed, location: Where the hardness comes from

- Old: «Which conditions a state satisfies, and whether it is a row, depend only on its vector of classes, so \[ |M(T_0)| = \sum_{\substack{c \text{ a class vector,}\\ \text{valid and not a row}}}\ \prod_{i} |c_i| \qquad (\text{\lstinline{missingCount_eq_weighted_of_le}}), \] over at most $(N+1)^k$ class vectors (\lstinline{length_classStates_le}).»
- New: «Which conditions a state satisfies, and whether it is a row, depend only on its vector of classes, so \[ |M(T_0)| = \sum_{\substack{\gamma \text{ a class vector,}\\ \text{valid and not a row}}}\ \prod_{i} |\gamma_i| \qquad (\text{\lstinline{missingCount_eq_weighted_of_le}}), \] over at most $(N+1)^k$ class vectors (\lstinline{length_classStates_le}).»

### m2: Primary sources read; citations corrected

**m2.51** — changed, location: Related work (also m11)

- Old: «Elmallah and Gouda prove firewall completeness hard by reduction from 3-SAT (stated as NP-hard; by its form it is coNP-hard), with no membership result~\cite{ElmallahGouda2017}. Thiemann and Yamada prove pattern completeness co-NP hard and verify their decision procedure in Isabelle, the hardness proof being on paper~\cite{ThiemannYamada2026}. Kapur et al.\ showed quasi-reducibility co-NP complete~\cite{KapurNRZ1991}, as cited by Thiemann and Yamada. Deciding whether a point lies outside a union of boxes is NP-hard~\cite{Chan2010}, and computing the volume of the union is \#P-hard~\cite{BringmannFriedrich2010}.»
- New: «Elmallah and Gouda prove firewall completeness NP-hard, by a reduction from a slice-probing problem that they reduce from 3-SAT~\cite{ElmallahGouda2017}. The reduction maps to the complement of completeness, so by its form it shows coNP-hardness; for membership they only remark that some of their problems can be shown to be in NP and the others in coNP. [AUTHOR: read in the 2013 University of Alberta technical report of the same title; the TDSC version could not be read.] Thiemann and Yamada prove pattern completeness coNP-hard and verify their decision procedure in Isabelle, the hardness proof being on paper~\cite{ThiemannYamada2026}. Kapur et al.\ show sufficient completeness coNP-complete for term rewriting systems with free constructors, and state that their complexity results also apply to ground reducibility~\cite{KapurNRZ1991}; Thiemann and Yamada cite the paper for the coNP-completeness of quasi-reducibility. [AUTHOR: only the abstract of Kapur et al.\ could be read.] Deciding whether a point lies outside a union of boxes is NP-hard~\cite{Chan2010}, and computing the volume of the union is \#P-hard~\cite{BringmannFriedrich2010}.»

### m6: The _unary forms listed; claim about both encodings narrowed

**m6.52** — changed, location: Instances, encoding and adequacy (also m12)

- Old: «We use Complexitylib's \lstinline{listGetD_binary}, which walks the list while reading the bits of the index and returns a default when the list ends, so the cost is polynomial in the lengths of the list and of the index's binary encoding, not in the index's value, which is never written in unary.»
- New: «We use Complexitylib's \lstinline{listGetD_binary}, which walks the list while reading the bits of the index and returns a default when the list ends, so the cost is polynomial in the lengths of the list and of the index's binary encoding; the index is never expanded to unary.»
- Old: «The identity is polynomial-time from \lstinline{encInst} to \lstinline{encInstBin}, so hardness for the unary encoding transfers to the binary one; every result below holds for both, except the explicit-degree bounds of \Cref{sec:boundary}, which are stated for \lstinline{encInstBin} only.»
- New: «The identity is polynomial-time from \lstinline{encInst} to \lstinline{encInstBin} (\lstinline{encInst_to_encInstBin_polyTime}), so hardness for the unary encoding transfers to the binary one. The NP-, coNP- and \#P-completeness results of \Cref{sec:decision,sec:counting,sec:monotone} are proved for both encodings, and the polynomial-time results of \Cref{sec:boundary} for \lstinline{encInstBin}, each with a \lstinline{_unary} form for \lstinline{encInst} (\Cref{app:statements}). The hardness results on the Boolean subclass (\Cref{sec:decision}) and the explicit-degree bounds of \Cref{sec:boundary} are stated for \lstinline{encInstBin} only.»

**m6.53** — new, location: Main Lean statements

- Old: `(none)`
- New:

```latex
\subparagraph*{The unary forms.}
Each polynomial-time result of \Cref{sec:boundary} also holds for \lstinline{encInst}:
\lstinline{completeNoConstraints_mem_P_unary}, \lstinline{missingNonemptyNoConstraints_mem_P_unary},
\lstinline{missingCountNoConstraints_polyTime_unary}, \lstinline{completeFixedAttrs_mem_P_unary},
\lstinline{missingNonemptyFixedAttrs_mem_P_unary} and \lstinline{missingCountFixedAttrs_polyTime_unary},
the first five through \lstinline{mem_P_of_mem_P_bin} or the re-encoding of \Cref{sec:encoding}.
The hardness results have their unary forms without the suffix \lstinline{_bin}
(\lstinline{MissingNonempty_npComplete}, \lstinline{Complete_coNPComplete},
\lstinline{missingNonempty_finset_npComplete}, \lstinline{complete_finset_coNPComplete},
\lstinline{missingCount_sharpPComplete}), and the monotone ones with the suffix
\lstinline{_unary} (\lstinline{countValidMonotone2_sharpPComplete_oneCall_unary},
\lstinline{countMissingMonotone2_sharpPComplete_oneCall_unary}).
```

### m8: Boolean model moved to the artifact appendix

**m8.54** — changed, location: The decision problems (also m12)

- Old: «The empty table shows where the hardness lies: in the constraints, not in the rows. With $T_0 = \emptyset$, completeness is unsatisfiability of the constraints.»
- New: «The empty table shows that the hardness lies in the constraints: with $T_0 = \emptyset$, completeness is unsatisfiability of the constraints.»
- Old: «The development also has a separate Boolean model, whose attributes are the variables of a Complexitylib CNF formula used as the constraints and whose rows are bit vectors; NP-, coNP- and \#P-completeness are proved for it too (\Cref{app:statements}), without an adequacy theorem.»
- New: `(deleted)`

**m8.55** — new, location: Artifact and reproducibility

- Old: `(none)`
- New:

```latex
\subparagraph*{The Boolean model.}
The repository also contains the first form of the development, a Boolean model
(\texttt{Bridge.lean}, \texttt{Counting.lean}): its attributes are the variables of a
Complexitylib CNF formula used as the constraints, and its rows are bit vectors. NP-, coNP- and
\#P-completeness are proved for it too (\lstinline{Latc.PaperD.MissingNonempty_npComplete},
\lstinline{Latc.PaperD.Complete_coNPComplete}, \lstinline{Latc.PaperD.countMissing_sharpPComplete}),
the last with a parsimonious reduction \emph{to} \#SAT (\lstinline{countMissing_eq_sharpSAT}).
It has no adequacy theorem, and the results of this paper do not use it.
```

**m8.56** — deleted, location: Counting

- Old:

```latex
In the separate Boolean model there is also a parsimonious reduction \emph{to} \#SAT: add to the
constraints, for each row of the right length, the clause stating that the tuple differs from
that row (\lstinline{countMissing_eq_sharpSAT}).
```
- New: `(deleted)`

**m8.57** — deleted, location: Main Lean statements

- Old:

```latex
\subparagraph*{The Boolean model (namespace \lstinline{Latc.PaperD}).}
\begin{lstlisting}
theorem MissingNonempty_npComplete : NPComplete encInst MissingNonempty
theorem Complete_coNPComplete : coNPComplete encInst Complete
theorem countMissing_sharpPComplete : SharpPComplete encInst countMissing
\end{lstlisting}
Here \lstinline{Inst}, \lstinline{encInst} and \lstinline{MissingNonempty} are those of the
Boolean model, a different namespace from the general one below.
```
- New: `(deleted)`

### m10: Generative-AI statement adapted to Springer's policy

**m10.58** — deleted, location: Use of generative AI

- Old:

```latex
Claude (Anthropic) [model and dates of use] was used as follows.
\begin{itemize}
\item \emph{Formalisation.} It wrote the Lean proofs of the counting result with a fixed number of
  attributes, the one-call Valiant theorem, the explicit degree, and the monotone results for
  tables with arbitrary rows and the tightened shape tests, in separate sessions from written task
  descriptions [that the author set and approved]. Lean checks every proof; the builds and the
  axiom audit are in \Cref{app:artifact}.
\item \emph{Writing.} It drafted the text of this paper, which [the author reviewed and revised].
\item \emph{Literature.} It searched for related work and checked bibliographic records against
  the publishers' records; [the author verified every reference].
\item \emph{Checking.} It checked the paper against the Lean source and produced draft referee
  reports, which led to revisions.
\end{itemize}
[The author] remain[s] responsible for all content.
```
- New: `(deleted)`

**m10.59** — deleted, location: Unnumbered section before the back matter

- Old:

```latex
\section*{Use of generative AI}
```
- New: `(deleted)`

### m12: Sentences reworked (style rule; referee sentences)

**m12.60** — changed, location: Instances, encoding and adequacy

- Old: «The first three are rows, so $M(T_0) = \{(2,1)\}$: the instance is in \textit{MissingNonempty}, not complete, and $\textit{missingCount}(I) = 1$.»
- New: «The first three are rows, so $M(T_0) = \{(2,1)\}$: the instance is in \textit{MissingNonempty}, it is incomplete, and $\textit{missingCount}(I) = 1$.»

**m12.61** — changed, location: Where the hardness comes from

- Old: «\emph{What is not proved.} For each fixed $k$, a separate machine with $k$ built in that rejects instances with more than $k$ attributes, with constants independent of~$k$.»
- New: «\emph{What is not proved.} For each fixed $k$, a separate machine with $k$ built in that rejects instances with more than $k$ attributes, with constants independent of~$k$, is not proved.»

**m12.62** — changed, location: Related work

- Old: «PVS generates coverage and disjointness obligations for tabular specifications~\cite{OwreRushbyShankar1997}: proof obligations about given tables, not complexity results.»
- New: «PVS generates coverage and disjointness obligations for tabular specifications~\cite{OwreRushbyShankar1997}; these are proof obligations about given tables, and come with no complexity results.»

**m12.63** — changed, location: Trusted base and audit

- Old: «For tables whose rows are complete tuples, few attributes or the absence of constraints give the polynomial regimes of \Cref{sec:boundary}, and the difficulty comes from constraints across many attributes, not from the size of the domains or of the table.»
- New: «For tables whose rows are complete tuples, few attributes or the absence of constraints give the polynomial regimes of \Cref{sec:boundary}, and the difficulty comes from constraints across many attributes; neither the size of the domains nor that of the table makes the problems hard.»

### m13: LatcFormal/ checked against Zenodo 0.1.0; Mathlib TM2ComputableInPolyTime cited

**m13.64** — changed, location: Related work (also m12)

- Old: «\subparagraph*{Mechanised computability and complexity.} Cook--Levin has been mechanised in ACL2~\cite{GamboaCowles2004}, Coq~\cite{GaeherKunze2021} and Isabelle~\cite{Cook_Levin-AFP}; reductions between Karp's problems are verified in Isabelle~\cite{PolyReductionsIsabelle}; and Senellart and Gnatenko prove all 21 of Karp's problems NP-complete in Lean~\cite{SenellartGnatenko2026}, with NP defined in descriptive-complexity terms and first-order reductions, and also prove \#Monotone-2SAT one-call \#P-complete in their setting. Mathlib~\cite{mathlib2020} itself defines polynomial-time computability for its stack-based Turing machines (\lstinline{TM2ComputableInPolyTime}, by Spelier and van Gent).»
- New: «\subparagraph*{Mechanised computability and complexity.} Cook--Levin has been mechanised in ACL2~\cite{GamboaCowles2004}, Coq~\cite{GaeherKunze2021} and Isabelle~\cite{Cook_Levin-AFP}; reductions between Karp's problems are verified in Isabelle~\cite{PolyReductionsIsabelle}; and Senellart and Gnatenko prove all 21 of Karp's problems NP-complete in Lean~\cite{SenellartGnatenko2026}, with NP defined in descriptive-complexity terms and first-order reductions; their library also proves \#Monotone-2SAT one-call \#P-complete in that setting~\cite{DescriptiveComplexityLib}. Mathlib~\cite{mathlib2020} itself defines polynomial-time computability for its stack-based Turing machines: \lstinline{TM2ComputableInPolyTime}, in the file \texttt{Mathlib/Computability/TuringMachine/Computable.lean} by Spelier and van Gent~\cite{MathlibTMComputable}.»
- Old: «Our setting needs explicit encodings and running times, but its classes are the textbook ones on Turing machines, so polynomial time, binary encodings of numbers and the size of the input, the quantities the tractability results of \Cref{sec:boundary} are about, are first-class.»
- New: «Our setting needs explicit encodings and running times; in exchange its classes are the textbook ones on Turing machines, so polynomial time, binary encodings of numbers and the size of the input, the quantities the tractability results of \Cref{sec:boundary} are about, are first-class.»

### SD: Statements and Declarations placeholders

**SD.65** — changed, location: Statements and Declarations

- Old: «\bmhead{Funding} [AUTHOR TO APPROVE: the LIPIcs draft has no funding statement.]»
- New: «\bmhead{Funding} [AUTHOR TO APPROVE: No funding was received for this work.]»

**SD.66** — new, location: Statements and Declarations

- Old: `(none)`
- New:

```latex
\bmhead{Competing interests}
[AUTHOR TO APPROVE: The author is a co-author of the 2021 paper that introduced the LATC
decision-table completion method, which the author's earlier work~\cite{PaperA} re-examines.
The author has no other competing interests to declare.] [AUTHOR: give the full reference of the
2021 LATC paper, which the repository does not contain.]
```

**SD.67** — new, location: Statements and Declarations

- Old: `(none)`
- New:

```latex
\bmhead{Author contribution}
[AUTHOR TO APPROVE: C.A.R. is the sole author. He set the research questions and the task
descriptions, reviewed the definitions and the text, and is responsible for the whole work;
the Lean proofs and the text were drafted with an AI system, as described in \Cref{sec:ai}.]

\bmhead{Use of generative AI}
[AUTHOR TO APPROVE: The use of an AI system is documented in \Cref{sec:ai}.]
```

**SD.68** — deleted, location: Declarations

- Old:

```latex
\bmhead{Competing interests}
[AUTHOR TO APPROVE: the LIPIcs draft has no competing-interests statement.]
```
- New: `(deleted)`

**SD.69** — deleted, location: Declarations

- Old:

```latex
\bmhead{Data availability}
[AUTHOR TO APPROVE: Not applicable.]
```
- New: `(deleted)`

**SD.70** — deleted, location: Declarations

- Old:

```latex
\bmhead{Author contribution}
[AUTHOR TO APPROVE: the paper has a single author; the LIPIcs draft has no contribution statement.]
```
- New: `(deleted)`

**SD.71** — deleted, location: Declarations

- Old:

```latex
\bmhead{Use of generative AI}
See the section ``Use of generative AI'' above. [AUTHOR TO APPROVE: its bracketed parts, and
whether JAR wants this statement in the Declarations, in the Methods or elsewhere.]
```
- New: `(deleted)`

**SD.72** — changed, location: Back matter heading

- Old: «\section*{Declarations}»
- New: «\section*{Statements and Declarations}»

