# Machine-Checked Complexity of Decision-Table Completeness in Lean

Carlos A. Russell, Independent Researcher, Buenos Aires, Argentina
(carlos.a.russell@gmail.com, ORCID 0009-0003-3741-0230)

> First draft, generated from `paper/main.tex` with pandoc for reading on screen. The LaTeX file
> is the source; edit it, not this file. Not compiled with LaTeX yet.

**Abstract.** A decision table is complete when every combination of its declared
condition values is covered by a row. Checking completeness under domain
constraints, and counting the missing combinations, arise when tables
are completed or audited in practice. We give a machine-checked proof in
Lean 4 that deciding whether a table has a missing combination is
NP-complete, that deciding completeness is coNP-complete, and that
counting the missing combinations is \#P-complete, over general finite
domains. The proofs compose a reduction from an existing formalisation
of decision-table completion with the Cook–Levin theorem and its
parsimonious form in Complexitylib, a library of complexity theory on
multi-tape Turing machines. An adequacy theorem ties the encoded
problems to the original set-based definitions, and matching
tractability results show where the hardness comes from: without domain
constraints all three problems are solvable in polynomial time, and they
remain so with a fixed number of attributes. For tables whose
constraints are monotone two-literal clauses, counting is in \#P and
\#Monotone-2SAT reduces to it; its \#P-hardness is stated conditionally
on Valiant’s theorem.

## 1 Introduction

Decision tables state business rules, regulations and clinical
guidelines as rows of condition values. A table is *complete* when every
combination of declared condition values that the domain constraints
allow is covered by some row; the uncovered combinations form its
*missing set* $M(T_0)$. Completeness checking is a staple of
decision-table practice, from early expert-system checkers ([Suwa,
Scott, and Shortliffe 1982](#ref-SuwaScottShortliffe1982)) to the
analysers of the DMN standard ([Calvanese et al.
2016](#ref-CalvaneseDLMMT2016)), which find missing rules but state no
complexity result.

Russell ([Russell 2026a](#ref-PaperA)) re-examined a decision-table
completion method over declared finite domains and proved, on paper,
that completeness under clause constraints is coNP-complete and that
counting $|M(T_0)|$ is \#P-complete (Proposition 5 there). The
accompanying Lean development, latc-check ([Russell
2026b](#ref-latc_check_0_1_0)), formalised the model and the
combinatorial reduction, but not the complexity classes: those need a
model of computation, polynomial-time bounds and encodings, which
latc-check did not have.

This paper closes that gap. We compose latc-check’s model with the
Cook–Levin theorem of Complexitylib ([Schlesinger and The Complexitylib
contributors 2026](#ref-Complexitylib)), a Lean 4 library of complexity
theory on multi-tape Turing machines built on CSLib ([Barrett et al.
2026](#ref-CSLib2026)) and Mathlib, and obtain the following, all with
only the three standard axioms of Lean.

1.  **NP- and coNP-completeness, end to end,** of the existence of a
    missing combination and of completeness, over general finite
    domains, in Complexitylib’s Turing-machine model, with every number
    in the encoding written in binary; a unary-index variant is kept
    (Sections 3 and 4).

2.  **\#P-completeness** of counting the missing combinations, over
    general finite domains: membership by counting accepted
    certificates, hardness by a parsimonious reduction from \#SAT
    (Section 5).

3.  **The tractable side:** without domain constraints, completeness and
    non-emptiness are in P and the count is computable in polynomial
    time; with at most $k$ attributes, both decision problems are in P
    and the count is computable in polynomial time, for each $k$.
    Hardness needs both constraints and an unbounded number of
    attributes (Section 6).

4.  **An adequacy theorem** linking the word-encoded problems to
    latc-check’s set-based definitions, so that the theorems speak about
    the original objects (Section 3).

5.  **The monotone two-literal case:** membership in \#P and a
    parsimonious reduction from \#Monotone-2SAT, unconditionally;
    \#P-hardness under one-call reductions, conditional on Valiant’s
    theorem as an explicit hypothesis (Section 5).

#### Related work.

Hardness of rule coverage is not new in itself. Elmallah and Gouda prove
firewall completeness NP-hard by reduction from 3-SAT, with no
membership result ([Elmallah and Gouda 2017](#ref-ElmallahGouda2017));
Thiemann and Yamada prove pattern completeness co-NP hard and verify
their decision procedure in Isabelle, the hardness proof being on
paper ([Thiemann and Yamada 2026](#ref-ThiemannYamada2026)); Kapur et
al. showed quasi-reducibility co-NP complete ([Kapur et al.
1991](#ref-KapurNRZ1991)); and the volume of a union of boxes is
\#P-hard ([Bringmann and Friedrich 2010](#ref-BringmannFriedrich2010)).
Levy and Rousset gave the first complexity results for verifying rule
bases, for output correctness rather than coverage ([Levy and Rousset
1996](#ref-LevyRousset1996)). None of these handles domain constraints
together with counting, and none of the hardness proofs is checked in a
proof assistant. Machine-checked NP-completeness is not new either:
Cook–Levin has been mechanised in ACL2 ([Gamboa and Cowles
2004](#ref-GamboaCowles2004)), Coq ([Gäher and Kunze
2021](#ref-GaeherKunze2021)) and Isabelle ([Balbach
2023](#ref-Cook_Levin-AFP)), and Senellart and Gnatenko prove all 21 of
Karp’s problems NP-complete in Lean, in a logical model with first-order
reductions ([Senellart and Gnatenko 2026](#ref-SenellartGnatenko2026)).
Our contribution is the problem, decision-table completeness under
constraints, with counting and a tractable side, on Complexitylib’s
Turing machines. The closest precedent for tables in a proof assistant
is PVS, which generates coverage and disjointness obligations for
tabular specifications ([Owre, Rushby, and Shankar
1997](#ref-OwreRushbyShankar1997)); those are proof obligations about
given tables, not complexity results.

## 2 Setting

#### latc-check’s model.

Attributes are indexed by a finite type $\iota$, attribute $i$ having
the declared finite domain $D_i$; condition tuples are dependent
functions $x : \forall i, D_i$, so the product space
$\mathcal{D} = D_1 \times \dots \times D_n$ is a finite type. The
constraints are one decidable predicate $C$ on tuples, and a table is
represented by its set $T_0$ of condition tuples. The valid space and
the missing set are

    def validSpace : Finset (∀ i, D i) := univ.filter C
    def missing (T : Finset (∀ i, D i)) : Finset (∀ i, D i) := validSpace C \ T

The table is complete when `missing C T = ∅`.

#### Complexitylib.

A type is encoded by an injection `α ↪ List Bool`; encodings of pairs,
lists and natural numbers (in binary, `encNat`, or in unary, `encUnary`)
are provided. `ComputableInPolyTime f encA encB` says that a multi-tape
Turing machine with a binary alphabet computes $f$ between the encodings
in polynomial time. The classes `P`, `NP`, `coNP` and `SharpP` are
defined from such machines, hardness from polynomial-time many-one
reductions and, for counting, from parsimonious reductions
(`ParsimoniousReducible`). Our hardness proofs start from
`CookLevin.SAT_npHard`, `CookLevin.UNSAT_coNPComplete` and the
parsimonious `CookLevin.SharpSAT_sharpPHard`.

#### The two libraries agree on SAT.

latc-check’s reduction is stated for its own propositional formulas. Two
lemmas identify its clause constraints and satisfiability with
Complexitylib’s CNF formulas:

    theorem holdsAll_eq_eval (S : Prop5.ConSet ℕ) (x : ℕ → Bool) :
        Prop5.holdsAll S x = (toCNF S).eval x
    theorem satisfiable_decode_iff (S : Prop5.ConSet ℕ) :
        Prop5.Satisfiable (Prop5.decode S) ↔ (toCNF S).Satisfiable

## 3 Encoding and adequacy

An instance is a triple $(d, S, T)$: the domain sizes
$d = [|D_0|, \dots, |D_{n-1}|]$, the clause constraints $S$, each clause
a list of conditions $(i, v)$ read $A_i = v$, and the rows $T$ of $T_0$.
A state is a list $s$ of values with $s_i < d_i$; it is valid when every
clause has a condition it satisfies.

    abbrev Cond := ℕ × ℕ
    abbrev Inst := List ℕ × (List (List Cond) × List (List ℕ))
    def Valid (S : List (List Cond)) (s : List ℕ) : Prop := ∀ c ∈ S, ∃ a ∈ c, CondHolds s a
    def MissingNonempty : Set Inst :=
      {I | ∃ s, InDomains I.1 s ∧ Valid I.2.1 s ∧ s ∉ I.2.2}
    def Complete : Set Inst := MissingNonemptyᶜ

#### Binary throughout.

The main encoding `encInstBin` writes every number in binary, the
attribute index of a condition included. Checking a condition then reads
$s_i$ at a binary index $i$, which we do with Complexitylib’s
`listGetD_binary`: it caps the index at the length of the list while
reading its bits, so a large index is never expanded to unary. The
values are shifted by one, so that the default $0$ of an out-of-range
lookup matches no value. An earlier encoding, `encInst`, writes the
index in unary; the identity is polynomial-time from it to `encInstBin`
(`encInst_to_encInstBin_polyTime`), so hardness for the unary encoding
transfers to the binary one, and every result holds for both.

#### Adequacy.

An instance $I$ denotes a table in latc-check’s model: attributes
`Fin n`, domains `Fin dᵢ`, the constraint predicate `I.con` and the
condition set `I.table` (rows of another length, or with values outside
the domains, denote no tuple). The word problems are exactly
latc-check’s:

    theorem mem_MissingNonempty_iff (I : Inst) :
        I ∈ MissingNonempty ↔ (missing I.con I.table).Nonempty
    theorem mem_Complete_iff (I : Inst) : I ∈ Complete ↔ missing I.con I.table = ∅

A third theorem, `coe_missing_map_toList`, shows that the tuples of
$M(T_0)$, read as lists of values, are exactly the witnesses of
`MissingNonempty`. Every complexity result below is therefore also a
statement about `Latc.missing`.

## 4 Decision problems

#### Membership.

The certificate is the missing state itself. The check verifies that the
state lies in the domains, satisfies every clause and is not a row
of $T_0$; it is polynomial-time (`checkBin_polyTime`), and the encoding
of a state in the domains is no longer than the encoded domain sizes,
which bounds the certificate.

#### Hardness.

A CNF formula $\varphi$ becomes the instance with one attribute per
variable, after renumbering the variables densely, domain $\{0,1\}$ for
each, one clause per clause of $\varphi$ (a literal becomes $A_i = 1$ or
$A_i = 0$), and $T_0 = \emptyset$. Satisfying assignments are then
exactly the missing states, which gives the reductions from SAT and from
UNSAT. Composed with Section 3:

    theorem MissingNonempty_npComplete_bin : NPComplete encInstBin MissingNonempty
    theorem Complete_coNPComplete_bin : coNPComplete encInstBin Complete
    theorem missingNonempty_finset_npComplete_bin :
        NPComplete encInstBin {I : Inst | (missing I.con I.table).Nonempty}
    theorem complete_finset_coNPComplete_bin :
        coNPComplete encInstBin {I : Inst | missing I.con I.table = ∅}

The same results hold for Boolean domains, with Complexitylib’s CNF
formulas as constraints (namespace `Latc.PaperD`).

## 5 Counting

Let `missingCount I` be `(missing I.con I.table).card`, the size of the
missing set of the denoted table.

#### Membership in \#P.

A certificate is the encoding of a state, padded with `false` to the
length of the encoded domain sizes. The verifier accepts a certificate
only when the state it describes is missing *and* the certificate is the
canonical one for that state, so each missing tuple is counted once
(`missingCount_eq_acceptCount`).

#### Hardness.

The reduction of Section 4 preserves counts:
`SharpSAT φ = missingCount (fromSAT φ)` (`sharpSAT_eq_missingCount`).
Composing with the parsimonious Cook–Levin theorem gives

    theorem missingCount_sharpPComplete_bin : SharpPComplete encInstBin missingCount

For Boolean domains there is also a reduction *to* \#SAT, adding to the
constraints one clause per row of $T_0$ of the right length that says
the tuple differs from that row (`countMissing_eq_sharpSAT`).

#### The monotone two-literal case.

Russell ([Russell 2026a](#ref-PaperA)) notes that counting the valid
states stays \#P-complete when every clause is $A_i = 1 \lor A_j = 1$
over domains $\{0,1\}$, citing Valiant ([Valiant
1979](#ref-Valiant1979enumeration)). As with Complexitylib’s
`SharpThreeSAT`, both counting functions are total: `SharpMonotone2SAT`
and `countValidMonotone2` return $0$ on inputs of any other shape.
Deciding such instances is trivial, since the all-ones state is valid,
so no parsimonious reduction from \#SAT exists unless P = NP, and
hardness needs a weaker reduction. We define one-call reductions in
Complexitylib’s model, $f(a) = \mathit{post}(a, g(r(a)))$ for
polynomial-time $r$ and $\mathit{post}$, and prove membership in \#P
(`countValidMonotone2_mem_SharpP_bin`) and a parsimonious reduction from
\#Monotone-2SAT (`sharpMonotone2SAT_reduces`, to the unary-index
encoding; the binary form follows by re-encoding) unconditionally.
Hardness takes Valiant’s theorem as an explicit hypothesis:

    theorem countValidMonotone2_oneCallSharpPComplete_bin
        (hValiant : OneCallSharpPHard encCNF SharpMonotone2SAT) :
        OneCallSharpPComplete encInstBin countValidMonotone2

Valiant proved the result under polynomial-time Turing reductions;
`hValiant` asks for the stronger one-call form. That form is
machine-checked by Senellart and Gnatenko ([Senellart and Gnatenko
2026](#ref-SenellartGnatenko2026)), in a model where \#P is defined
logically and reductions are first-order, so the link to our hypothesis
is informal. A hypothesis is not an axiom, so Lean’s axiom audit does
not show it; we therefore state it wherever the theorem appears.

## 6 Where the hardness comes from

The SAT reduction uses clause constraints and as many attributes as the
formula has variables. Removing either ingredient makes the problems
polynomial-time (Table 1).

#### No constraints.

Then $|M(T_0)| = \prod_i d_i - r$, where $r$ is the number of distinct
rows of $T_0$ inside the declared domains
(`missingCount_eq_of_noConstraints`). The product can be exponential in
the input length, but its binary encoding is no longer than those of the
factors together, so it is computed exactly in binary by a fold with
bounded growth, and the count is polynomial-time
(`missingCountNoConstraints_polyTime`); completeness and non-emptiness
are in P (`completeNoConstraints_mem_P`,
`missingNonemptyNoConstraints_mem_P`).

#### At most $k$ attributes.

With binary domain sizes, $|\mathcal{D}|$ is not polynomial even for
$k = 1$, so $\mathcal{D}$ cannot be enumerated. Let $N$ be the number of
values written in the instance. A value written nowhere can be replaced
by one at most $N$ that is also written nowhere, without changing which
conditions hold, and a state with such a value is not a row of $T_0$. A
missing state therefore exists if and only if one exists whose values
are among $0, \dots, N$ and the written values; there are at most
$(2N+1)^k$ such states (`length_candidateStates_le`), and both decision
problems are in P for each $k$ (`completeFixedAttrs_mem_P`,
`missingNonemptyFixedAttrs_mem_P`).

Counting needs more, since a candidate state with an unwritten value
stands for all the unwritten values of that attribute. For each
attribute, split its domain into classes: each written value in the
domain alone, and one class of the unwritten values (possibly empty).
Which conditions a state satisfies depends only on its vector of
classes, so $|\mathcal{V}|$ is the sum, over valid class vectors, of the
product of the class sizes (`missingCount_eq_weighted_of_le`). There are
at most $(N+1)^k$ class vectors (`length_classStates_le`); the weights
are products of domain sizes, computed in binary by the bounded-growth
fold of the no-constraint case. Subtracting the valid distinct rows
of $T_0$, the count is polynomial-time for each $k$, with binary or
unary attribute indices (`missingCountFixedAttrs_polyTime`,
`missingCountFixedAttrs_polyTime_unary`).

<div id="tab:boundary">

|                | constraints | attributes  | complexity                                |
|:---------------|:------------|:------------|:------------------------------------------|
| SAT reduction  | clauses     | unbounded   | NP-, coNP-, \#P-complete                  |
| no constraints | none        | unbounded   | in P; count polynomial-time               |
| fixed $k$      | clauses     | at most $k$ | in P; count polynomial-time, for each $k$ |

Where the hardness comes from.

</div>

## 7 Experience and conclusion

#### Effort.

The development is 2 598 lines of Lean in the nine files of
`LatcComplexity/`, 2 395 without the axiom-audit file. Its first seven
commits ran from 28 October 2026, 14:16, to 29 October, 00:18, over
about ten hours, building on latc-check’s model and reduction; an
eighth, on 31 October, added counting with a fixed number of attributes.

#### Automation.

Complexitylib’s `fun_prop` discharged many polynomial-time obligations:
it occurs in 66 lines of the development, often directly after unfolding
a definition. Proofs by hand were needed where the size of intermediate
values matters: the product of the domain sizes, whose bounded growth
rests on Complexitylib’s `length_encNat_mul_le`, and the enumeration of
candidate states, whose polynomial time is proved by induction on $k$.
Reading a list at a binary index needed a library lemma,
`listGetD_binary`, rather than a new proof.

#### Following a moving library.

Complexitylib changes daily on a release-candidate Lean toolchain. We
pinned commit `b7acfc2` (28 October 2026) and the matching toolchain
`v4.36.0-rc1` when the development began, and kept that pin throughout,
so we met no upstream breakage: the price is falling behind. Three days
later the library’s main branch was 481 commits ahead, had moved to Lean
`v4.36.0-rc2`, advanced CSLib and Mathlib with it, and repaired
`fun_prop` clients broken by the move. Whether our development builds
against it is untested, so we publish the artifact with its pin. The
library had also just been reorganised: two weeks before we started, a
CSLib-based rewrite replaced its earlier version, which
Russell ([Russell 2026a](#ref-PaperA)) cites and which now lives on as a
separate repository with a different API.

#### Trust.

`LatcComplexity/Axioms.lean` prints the axioms of 174 theorems, among
them every theorem of this development that the paper cites; each
depends only on `propext`, `Classical.choice` and `Quot.sound`, or
fewer. A cold build, from a fresh clone downloading precompiled Mathlib,
took about seven minutes and 12 GB of disk at an earlier commit; it will
be re-measured at the final one.

#### What remains.

Valiant’s theorem in Complexitylib’s model, which would discharge
`hValiant`; and an explicit formula in $k$ for the degree of the
fixed-attribute bounds, which we prove polynomial for each $k$ without
extracting the degree.

## References

<div id="refs" class="references csl-bib-body hanging-indent">

<div id="ref-Cook_Levin-AFP" class="csl-entry">

Balbach, Frank J. 2023. “The Cook-Levin Theorem.” *Archive of Formal
Proofs*.

</div>

<div id="ref-CSLib2026" class="csl-entry">

Barrett, Clark, Swarat Chaudhuri, Fabrizio Montesi, Jim Grundy, Pushmeet
Kohli, Leonardo de Moura, Alexandre Rademaker, and Sorrachai
Yingchareonthawornchai. 2026. “CSLib: The Lean Computer Science
Library.” <https://arxiv.org/abs/2602.04846>.

</div>

<div id="ref-BringmannFriedrich2010" class="csl-entry">

Bringmann, Karl, and Tobias Friedrich. 2010. “Approximating the Volume
of Unions and Intersections of High-Dimensional Geometric Objects.”
*Computational Geometry* 43 (6–7): 601–10.
<https://doi.org/10.1016/j.comgeo.2010.03.004>.

</div>

<div id="ref-CalvaneseDLMMT2016" class="csl-entry">

Calvanese, Diego, Marlon Dumas, Ülari Laurson, Fabrizio M. Maggi, Marco
Montali, and Irene Teinemaa. 2016. “Semantics and Analysis of DMN
Decision Tables.” In *Business Process Management – 14th International
Conference, BPM 2016, Rio de Janeiro, Brazil, September 18–22, 2016,
Proceedings*, edited by Marcello La Rosa, Peter Loos, and Oscar Pastor,
9850:217–33. Lecture Notes in Computer Science. Springer.
<https://doi.org/10.1007/978-3-319-45348-4_13>.

</div>

<div id="ref-ElmallahGouda2017" class="csl-entry">

Elmallah, Ehab S., and Mohamed G. Gouda. 2017. “Hardness of Firewall
Analysis.” *IEEE Transactions on Dependable and Secure Computing* 14
(3): 339–49. <https://doi.org/10.1109/TDSC.2015.2455532>.

</div>

<div id="ref-GaeherKunze2021" class="csl-entry">

Gäher, Lennard, and Fabian Kunze. 2021.
“<span class="nocase">Mechanising Complexity Theory: The Cook-Levin
Theorem in Coq</span>.” In *12th International Conference on Interactive
Theorem Proving (ITP 2021)*, edited by Liron Cohen and Cezary Kaliszyk,
193:20:1–18. Leibniz International Proceedings in Informatics (LIPIcs).
Dagstuhl, Germany: Schloss Dagstuhl – Leibniz-Zentrum für Informatik.
<https://doi.org/10.4230/LIPIcs.ITP.2021.20>.

</div>

<div id="ref-GamboaCowles2004" class="csl-entry">

Gamboa, Ruben, and John Cowles. 2004. “A Mechanical Proof of the
Cook-Levin Theorem.” In *Theorem Proving in Higher Order Logics, 17th
International Conference, TPHOLs 2004, Park City, Utah, USA, September
14-17, 2004, Proceedings*, edited by Konrad Slind, Annette Bunker, and
Ganesh Gopalakrishnan, 3223:99–116. Lecture Notes in Computer Science.
Springer. <https://doi.org/10.1007/978-3-540-30142-4_8>.

</div>

<div id="ref-KapurNRZ1991" class="csl-entry">

Kapur, Deepak, Paliath Narendran, Daniel J. Rosenkrantz, and Hantao
Zhang. 1991. “Sufficient-Completeness, Ground-Reducibility and Their
Complexity.” *Acta Informatica* 28 (4): 311–50.
<https://doi.org/10.1007/BF01893885>.

</div>

<div id="ref-LevyRousset1996" class="csl-entry">

Levy, Alon Y., and Marie-Christine Rousset. 1996. “Verification of
Knowledge Bases Based on Containment Checking.” In *Proceedings of the
Thirteenth National Conference on Artificial Intelligence (AAAI-96)*,
585–90. AAAI Press. <https://aaai.org/Papers/AAAI/1996/AAAI96-087.pdf>.

</div>

<div id="ref-OwreRushbyShankar1997" class="csl-entry">

Owre, Sam, John Rushby, and Natarajan Shankar. 1997. “Integration in
PVS: Tables, Types, and Model Checking.” In *Tools and Algorithms for
the Construction and Analysis of Systems (TACAS ’97)*, 1217:366–83.
Lecture Notes in Computer Science. Springer.
<https://doi.org/10.1007/BFb0035400>.

</div>

<div id="ref-PaperA" class="csl-entry">

Russell, Carlos A. 2026a. “Where Declared Domains Are Lost: LATC, DMN
Analysers and Public DMN Models.”

</div>

<div id="ref-latc_check_0_1_0" class="csl-entry">

———. 2026b. “Latc_check: Independent Checks for Finite-Domain
Decision-Table Completion.” Zenodo.
<https://doi.org/10.5281/zenodo.23646699>.

</div>

<div id="ref-Complexitylib" class="csl-entry">

Schlesinger, Samuel, and The Complexitylib contributors. 2026.
“Complexitylib.” <https://github.com/cslib-community/complexitylib>.

</div>

<div id="ref-SenellartGnatenko2026" class="csl-entry">

Senellart, Pierre, and Anton Gnatenko. 2026. “Descriptive Complexity in
Lean: Completeness by First-Order Reductions.”
<https://arxiv.org/abs/2609.18261>.

</div>

<div id="ref-SuwaScottShortliffe1982" class="csl-entry">

Suwa, Motoi, A. Carlisle Scott, and Edward H. Shortliffe. 1982. “An
Approach to Verifying Completeness and Consistency in a Rule-Based
Expert System.” *AI Magazine* 3 (4): 16–21.
<https://doi.org/10.1609/aimag.v3i4.377>.

</div>

<div id="ref-ThiemannYamada2026" class="csl-entry">

Thiemann, René, and Akihisa Yamada. 2026. “A Verified Algorithm for
Deciding Pattern Completeness with Optimal Asymptotic Complexity.”
*Journal of Logical and Algebraic Methods in Programming* 151: 101129.
<https://doi.org/10.1016/j.jlamp.2026.101129>.

</div>

<div id="ref-Valiant1979enumeration" class="csl-entry">

Valiant, Leslie G. 1979. “The Complexity of Enumeration and Reliability
Problems.” *SIAM Journal on Computing* 8 (3): 410–21.
<https://doi.org/10.1137/0208032>.

</div>

</div>
