# Machine-Checked Complexity of Decision-Table Completeness in Lean

Carlos A. Russell, Independent Researcher, Buenos Aires, Argentina
(carlos.a.russell@gmail.com, ORCID 0009-0003-3741-0230)

> First draft, generated from `paper/main.tex` with pandoc for reading on screen. The LaTeX file
> is the source; edit it, not this file. Not compiled with LaTeX yet.

**Abstract.** A decision table is complete when every combination of its declared
condition values that the domain constraints allow is covered by a row.
We prove in Lean 4, over multi-tape Turing machines and with no unproved
assumptions, that for finite-domain decision tables with clause
constraints, deciding whether a combination is missing is NP-complete,
deciding completeness is coNP-complete, and counting the missing
combinations is \#P-complete. An adequacy theorem ties these word
problems to the set-based definitions of an existing formalisation of
decision-table completion, so the results speak about the original
objects. Complementary polynomial-time results locate the hardness: all
three problems are polynomial without constraints, and with a fixed
number of attributes, where one machine runs within $c\,(|x|+1)^{dn+d}$
on instances with $n$ attributes. For monotone two-literal constraints,
counting remains \#P-complete under reductions with a single oracle
call; for this we prove a one-call version of Valiant’s theorem on
\#Monotone-2SAT in the same Turing-machine model.

## 1 Introduction

Decision tables state business rules, regulations and clinical
guidelines as rows of condition values. A table is *complete* when every
combination of declared condition values that the domain constraints
allow is covered by some row; the uncovered combinations form its
*missing set* $M(T_0)$. Completeness checking is a staple of
decision-table practice, from early expert-system checkers ([Suwa,
Scott, and Shortliffe 1982](#ref-SuwaScottShortliffe1982)) to the
analysers of the DMN standard ([Calvanese et al.
2016](#ref-CalvaneseDLMMT2016)), which report missing rules. Counting
them matters too: one missing edge case and a table that misses half of
its valid inputs are both “incomplete”, and $|M(T_0)|$ is what tells
them apart.

Russell ([Russell 2026a](#ref-PaperA)) re-examined a decision-table
completion method over declared finite domains and argued, on paper,
that completeness under clause constraints is coNP-complete and that
counting $|M(T_0)|$ is \#P-complete (Proposition 5 there). The
accompanying Lean development, latc-check ([Russell
2026b](#ref-latc_check_0_1_0)), formalised the decision-table model and
the combinatorial reduction, but not the complexity classes: those need
a model of computation, polynomial-time bounds and encodings, which
latc-check did not have.

This paper supplies them. We compose latc-check’s model with
Complexitylib ([Schlesinger and The Complexitylib contributors
2026](#ref-Complexitylib)), a Lean 4 library of complexity theory on
multi-tape Turing machines with a machine-checked Cook–Levin theorem,
and prove the classification end to end, together with results that
neither earlier development contains. Every theorem depends only on
Lean’s three standard axioms, and none on `sorry`.

#### Contributions.

Table 1 separates what this paper adds from what it reuses.

1.  **The classification, machine-checked end to end** (Sections 4 and
    5): non-emptiness of $M(T_0)$ is NP-complete, completeness
    coNP-complete and counting \#P-complete, for finite domains with
    clause constraints, with every number of the input written in
    binary. Hardness holds already for Boolean domains and empty tables.

2.  **Adequacy** (Section 3): the encoded problems are exactly
    latc-check’s set-based ones.

3.  **The tractability boundary** (Section 7): polynomial time without
    constraints, and with a fixed number of attributes, for both
    decision problems and for counting, with an explicit degree linear
    in the number of attributes.

4.  **One-call hardness for monotone two-literal counting** (Section 6):
    a definition of one-call reductions in Complexitylib’s model, and a
    one-call version of Valiant’s theorem, from which counting the
    missing combinations stays \#P-complete under one-call reductions
    when every constraint is $A_i = 1 \lor A_j = 1$.

<div class="tabular">

L0.38L0.26L0.26 result & before this paper & here  
decision-table model, missing set & latc-check (Lean) & reused  
SAT to missing states, combinatorially & latc-check (Lean) & reused  
NP/coNP-completeness, \#P-completeness & on paper ([Russell
2026a](#ref-PaperA), Prop. 5) & Turing machines, in Lean  
adequacy of the encoded problems & – & new  
polynomial cases: no constraints, fixed $k$ & – & new  
explicit degree in the number of attributes & – & new  
one-call reductions, one-call Valiant & Valiant, Turing reductions & new
in this model  

</div>

Section 2 recalls Complexitylib and latc-check, Section 3 fixes the
input language, Sections 4 and 5 and 6 and 7 prove the results, Section
8 discusses related work and Section 9 the formalisation. Appendix A
lists the main Lean statements and Appendix B the artifact.

## 2 Preliminaries

#### Machines, encodings and classes.

Complexitylib works with multi-tape Turing machines over a binary
alphabet. A type $\alpha$ is given an encoding, an injection
$\alpha \hookrightarrow \{0,1\}^*$; pairs, lists and natural numbers
have standard encodings, numbers in binary (`encNat`) or in unary
(`encUnary`). A function $f$ is computable in polynomial time between
two encodings when some machine maps the encoding of every $a$ to the
encoding of $f(a)$ within a polynomial in the input length. A language
is in P when its characteristic function is; in NP when it is the set of
inputs having a certificate of polynomially bounded length accepted by a
polynomial-time verifier; and coNP is the class of complements. A
function $f$ into $\mathbb{N}$ is in \#P when $f(a)$ is the number of
certificates of a polynomially bounded length that a polynomial-time
verifier accepts on $a$.

#### Reductions.

Three notions are used. A *many-one* reduction from $A$ to $B$ is a
polynomial-time $r$ with $a \in A \iff r(a) \in B$; NP-, coNP-hardness
and completeness are defined with it. A *parsimonious* reduction from
$f$ to $g$ is a polynomial-time $r$ with $f(a) = g(r(a))$; Complexitylib
defines \#P-hardness with it. These two are Complexitylib’s. The third
is ours:

<div class="definition">

<span id="def:onecall" label="def:onecall"></span> $f$ reduces to $g$
with one call if there are polynomial-time functions $r$ and
$\mathit{post}$ with $f(a) = \mathit{post}(a, g(r(a)))$ for every $a$,
where $\mathit{post}$ reads $a$ and the answer $g(r(a))$ written in
binary. $g$ is *one-call \#P-hard* if every function in \#P, under any
encoding, reduces to it with one call, and *one-call \#P-complete* if it
is moreover in \#P.

</div>

A one-call reduction is a polynomial-time Turing reduction that makes
exactly one oracle query, whose answer is post-processed together with
the input. Parsimonious reductions are one-call, with
$\mathit{post}(a, y) = y$; so \#P-hardness implies one-call
\#P-hardness, and a parsimonious reduction followed by a one-call
reduction is one-call. One-call hardness implies hardness under
polynomial-time Turing reductions, the notion of Valiant ([Valiant
1979](#ref-Valiant1979enumeration)). It is weaker than parsimonious
hardness, which matters below: a problem whose decision version is
trivial cannot be parsimoniously \#P-hard unless P = NP, but can be
one-call \#P-hard. Our hardness proofs start from Complexitylib’s
Cook–Levin theorem and its parsimonious form: SAT is NP-hard, UNSAT
coNP-complete, and \#SAT \#P-hard under parsimonious reductions.

#### latc-check’s model.

Attributes are indexed by a finite type $\iota$, attribute $i$ having
the declared finite domain $D_i$, so the space of condition tuples
$\mathcal{D} = \prod_i D_i$ is finite. Constraints are a decidable
predicate $C$ on tuples, and a table is represented by its set $T_0$ of
condition tuples. The valid space is
$\mathcal{V} = \{x \in \mathcal{D} : C(x)\}$, the missing set is
$M(T_0) = \mathcal{V} \setminus T_0$, and the table is complete when
$M(T_0) = \emptyset$. In Lean these are `validSpace C` and
`missing C T`, both `Finset`s, so duplicate rows play no role. Two
lemmas identify latc-check’s clause constraints and satisfiability with
Complexitylib’s CNF formulas (`holdsAll_eq_eval`,
`satisfiable_decode_iff`), which lets the two developments share the SAT
reduction.

## 3 Instances, encoding and adequacy

#### Instances.

An instance is a triple $I = (d, S, T)$ of lists of natural numbers:

- $d = [d_0, \dots, d_{n-1}]$, the domain sizes; attribute $i$ ranges
  over $\{0, \dots, d_i - 1\}$, and $n$, the number of attributes, is
  the length of $d$;

- $S$, the clause constraints: a list of clauses, each a list of
  conditions $(i, v)$, read $A_i = v$;

- $T$, the rows of $T_0$: a list of lists of values.

A *state* is a list $s$ of length $n$ with $s_i < d_i$. It satisfies the
condition $(i, v)$ when $i < n$ and $s_i = v$, and it is *valid* when
every clause of $S$ has a condition it satisfies. Every triple is an
instance; nothing is rejected as malformed, and the semantics settles
each degenerate case. A condition on a nonexistent attribute, or with a
value outside the domain, is never satisfied; an empty clause makes
every state invalid; a domain of size zero leaves no states; a row of
the wrong length or with an out-of-domain value covers no state; and
repeated rows or conditions change nothing. Then $$\begin{aligned}
\textit{MissingNonempty} &= \{I : \text{some valid state is not a row of } T\},\\
\textit{Complete} &= \overline{\textit{MissingNonempty}},
\end{aligned}$$ and $\textit{missingCount}(I)$ is the number of valid
states that are not rows.

#### A running example.

Take two attributes with $d = [3, 2]$, the constraint
$A_0 = 0 \lor A_1 = 1$, and the rows $(0,0)$, $(0,1)$, $(1,1)$:
$$I = \bigl([3, 2],\ [[(0,0), (1,1)]],\ [[0,0], [0,1], [1,1]]\bigr).$$
Of the six states, four are valid: $(0,0)$, $(0,1)$, $(1,1)$ and
$(2,1)$. The first three are rows, so $M(T_0) = \{(2,1)\}$: the instance
is in *MissingNonempty*, not complete, and
$\textit{missingCount}(I) = 1$.

#### Encoding and input size.

The main encoding, `encInstBin`, writes the triple with Complexitylib’s
encodings of pairs and lists and every number in binary: the domain
sizes, the attribute index and value of each condition, and the values
of each row. The number of attributes is not written separately; it is
the length of the list $d$. The input size $|x|$ in every polynomial
bound below is the length of this encoding. With binary domain sizes,
$|\mathcal{D}| = \prod_i d_i$ can be exponential in $|x|$ even for one
attribute.

Checking a condition $(i, v)$ against a state reads $s_i$ at a binary
index $i$. We use Complexitylib’s `listGetD_binary`, which walks the
list while reading the bits of the index and returns a default when the
list ends, so the cost is polynomial in the lengths of the list and of
the index’s binary encoding, not in the index’s value, which is never
written in unary. The values are shifted by one before the lookup, so
that the default $0$ matches no value: an out-of-range attribute fails
the condition, as the semantics requires. A second encoding, `encInst`,
writes the attribute index in unary. The identity is polynomial-time
from `encInst` to `encInstBin`, so hardness for the unary encoding
transfers to the binary one; every result below holds for both.

#### Adequacy.

An instance denotes a table in latc-check’s model: attributes `Fin n`,
domains `Fin dᵢ`, the constraint predicate given by the clauses, and as
$T_0$ the tuples whose list of values is a row. The word problems are
exactly latc-check’s:

    theorem mem_MissingNonempty_iff (I : Inst) :
        I ∈ MissingNonempty ↔ (missing I.con I.table).Nonempty
    theorem mem_Complete_iff (I : Inst) : I ∈ Complete ↔ missing I.con I.table = ∅

A third theorem, `coe_missing_map_toList`, shows that the tuples of
$M(T_0)$, read as lists, are exactly the witnesses of *MissingNonempty*,
and *missingCount* is defined as the cardinality of latc-check’s missing
set. Every complexity result below is therefore a statement about
latc-check’s `missing` on clause-constrained tables; it says nothing
about constraint languages other than clauses.

## 4 The decision problems

<div class="theorem">

<span id="thm:decision" label="thm:decision"></span> Under `encInstBin`,
*MissingNonempty* is NP-complete and *Complete* is coNP-complete. Both
remain hard on instances with domains $\{0,1\}$ and $T_0 = \emptyset$.

</div>

<div class="proof">

*Proof sketch.* *Membership.* The certificate is a missing state. The
verifier checks that it lies in the domains, satisfies every clause and
is not a row; it runs in polynomial time (`checkBin_polyTime`). A state
in the domains has $s_i < d_i$ for every $i$, so its encoding is no
longer than that of $d$, which bounds the certificate length by $|x|$.
*Hardness.* Given a CNF formula $\varphi$, renumber its variables
densely as $0, \dots, n-1$ and build the instance with $n$ attributes of
domain $\{0,1\}$, one clause per clause of $\varphi$ (the literal $x_i$
becomes $A_i = 1$, and $\lnot x_i$ becomes $A_i = 0$), and no rows. Its
valid states are the satisfying assignments of $\varphi$, and with no
rows they are all missing. So $\varphi$ is satisfiable iff the instance
is in *MissingNonempty*, and unsatisfiable iff it is complete: a
reduction from SAT and from UNSAT, polynomial-time (`fromSAT_polyTime`).
Composed with Complexitylib’s Cook–Levin theorems and with the identity
re-encoding, this gives the theorem (`MissingNonempty_npComplete_bin`,
`Complete_coNPComplete_bin`). By adequacy the same holds for
$\{I : M(T_0) \neq \emptyset\}$ and $\{I : M(T_0) = \emptyset\}$ stated
with latc-check’s `missing`. ◻

</div>

The empty table shows where the hardness lies: in the constraints, not
in the rows. With $T_0 = \emptyset$, completeness is unsatisfiability of
the constraints. Rows only remove states, and Section 7 shows that
without constraints they cannot make the problems hard. The same results
hold with Boolean domains and Complexitylib’s CNF formulas as
constraints (Appendix A).

## 5 Counting

<div class="theorem">

<span id="thm:counting" label="thm:counting"></span> Under `encInstBin`,
*missingCount* is \#P-complete under parsimonious reductions, and
remains \#P-hard on instances with domains $\{0,1\}$ and
$T_0 = \emptyset$.

</div>

<div class="proof">

*Proof sketch.* *Membership.* Membership needs every missing state to
have exactly one accepted certificate. Let $L$ be the length of the
encoding of the domain sizes $d$. A certificate is a bit string of
length $L$. The verifier decodes the first $n$ numbers from it into a
state $s$ and accepts when $s$ is missing *and* the certificate equals
the canonical certificate of $s$: the encoding of $s$ followed by zeros
up to length $L$. The encoding of a state in the domains is no longer
than that of $d$, so every missing state has a canonical certificate of
length $L$; the canonical certificate determines the state; and any
other string decoding to $s$ is rejected. So the accepted certificates
of length $L$ are in bijection with $M(T_0)$
(`missingCount_eq_acceptCount`), and both the verifier and $L$ are
polynomial-time. Without the canonicity test, a state could have several
accepted certificates (different padding) and the count would be wrong.

*Hardness.* The reduction of Theorem 2 is parsimonious: the satisfying
assignments of $\varphi$ and the missing states of its instance are in
bijection, so
$\#\mathrm{SAT}(\varphi) = \textit{missingCount}(\mathit{fromSAT}(\varphi))$
(`sharpSAT_eq_missingCount`). Composition with Complexitylib’s
parsimonious Cook–Levin theorem gives
`missingCount_sharpPComplete_bin`. ◻

</div>

For Boolean domains there is also a parsimonious reduction *to* \#SAT:
add to the constraints, for each row of the right length, the clause
stating that the tuple differs from that row
(`countMissing_eq_sharpSAT`).

## 6 Monotone two-literal constraints and Valiant’s theorem

Russell ([Russell 2026a](#ref-PaperA)) notes that counting the valid
states stays \#P-complete when every clause is $A_i = 1 \lor A_j = 1$
over domains $\{0,1\}$, citing Valiant ([Valiant
1979](#ref-Valiant1979enumeration)). Deciding such instances is trivial:
with domains $\{0,1\}$ and only positive two-literal clauses, the
all-ones state is valid. So counting cannot be \#P-hard under
parsimonious reductions unless P = NP, and the right notion is the
one-call reduction of Definition 1.

Let *SharpMonotone2SAT* be the number of models of a CNF formula whose
clauses are all $x_i \lor x_j$, and *countValidMonotone2* the number of
valid states of an instance with domains $\{0,1\}$, clauses of two
conditions with value 1, and no rows. As with Complexitylib’s \#3SAT,
both functions are total and return $0$ on inputs of any other shape;
the shape tests are polynomial-time. Counting valid states of such
instances is in \#P, and \#Monotone-2SAT reduces to it parsimoniously
(`countValidMonotone2_mem_SharpP_bin`, `sharpMonotone2SAT_reduces`).
What remains is the hardness of \#Monotone-2SAT itself.

<div class="theorem">

<span id="thm:valiant" label="thm:valiant"></span> \#Monotone-2SAT is
one-call \#P-hard. Hence *countValidMonotone2* is one-call \#P-complete
under `encInstBin` and `encInst`.

</div>

Valiant proved \#Monotone-2SAT \#P-complete under polynomial-time Turing
reductions, interpolating over many oracle calls. Senellart and Gnatenko
machine-check the one-call form in a logical model of \#P with
first-order reductions ([Senellart and Gnatenko
2026](#ref-SenellartGnatenko2026)). We prove it in Complexitylib’s model
by one reduction from \#SAT, which is \#P-hard parsimoniously, so by
Definition 1 it suffices to reduce \#SAT to \#Monotone-2SAT with one
call.

#### Step 1: models as independent sets.

Let $\varphi$ have variables $0, \dots, n-1$ (after dense renumbering)
and clauses $c_1, \dots, c_m$. Build a graph $G$ with a vertex $(i, b)$
for each variable $i$ and value $b$, and a vertex $o$ for each literal
occurrence, read “$o$ is the first true literal of its clause”. Edges
join $(i, 0)$ and $(i, 1)$; any two occurrences of the same clause; an
occurrence and the value of its variable that falsifies it; and an
occurrence and each value that makes an *earlier* literal of its clause
true. The vertices fall into $K = n + m$ cliques, $\{(i,0),(i,1)\}$ for
each variable and the occurrences of each clause, so every independent
set has at most $K$ vertices. An independent set of exactly $K$ vertices
picks a value for each variable, which is an assignment $\sigma$, and an
occurrence in each clause that $\sigma$ makes true, with every earlier
literal false. That occurrence is unique given $\sigma$, so these
independent sets are in bijection with the models of $\varphi$
(`modelCount_eq_card`). The “first true literal” choice is what makes
the correspondence exact, for any CNF: repeated and complementary
literals need no special case. An empty clause has no vertex, so no
independent set reaches $K$, and the count is $0$, as it should be.

For example, $\varphi = x_0 \lor x_1$ has $n = 2$, $m = 1$, $K = 3$,
vertices $(0,0)$, $(0,1)$, $(1,0)$, $(1,1)$, $o_1$ for $x_0$, $o_2$ for
$x_1$. The edges at $o_1$ go to $o_2$ and $(0,0)$; those at $o_2$ go to
$o_1$, $(1,0)$ and $(0,1)$. The independent sets of size 3 are
$\{(0,1), (1,0), o_1\}$, $\{(0,1), (1,1), o_1\}$ and
$\{(0,0), (1,1), o_2\}$: three, one per model.

#### Step 2: a monotone formula.

Let $N$ be the number of vertices of $G$, and give every vertex
$t = n + 1$ fresh pendant leaves. The monotone formula $\psi$ has a
variable per vertex and leaf, and a clause $x_u \lor
x_w$ per edge $\{u, w\}$ of the graph with leaves. Its models are the
vertex covers, the complements of the independent sets. An independent
set of the graph with leaves consists of an independent set $S$ of $G$
together with any subset of the leaves of the $N - |S|$ vertices
outside $S$, so
$$x \;=\; \#\mathrm{SAT}(\psi) \;=\; \sum_{S \text{ independent in } G} 2^{\,t\,(N - |S|)}
\qquad (\text{\texttt{modelCount_psi}}).$$ Every vertex has leaves, so
no vertex of the formula is isolated, and $\psi$ has exactly two
positive literals per clause.

#### Step 3: one digit.

Write $x$ in base $2^t$. Multiply by $2^{tK}$ and divide by $2^{tN}$:
$$\Bigl\lfloor \frac{x \cdot 2^{tK}}{2^{tN}} \Bigr\rfloor
= \Bigl\lfloor \sum_{S} 2^{\,t\,(K - |S|)} \Bigr\rfloor .$$ Since
$|S| \le K$, every exponent is a nonnegative multiple of $t$, so the sum
is an integer and the floor is exact. Sets with $|S| < K$ contribute
multiples of $2^t$, and sets with $|S| = K$ contribute $1$ each. Their
number is $\#\mathrm{SAT}(\varphi) \le 2^n < 2^t$. So
$$\#\mathrm{SAT}(\varphi) \;=\; \Bigl\lfloor \frac{x \cdot 2^{tK}}{2^{tN}} \Bigr\rfloor \bmod 2^t
\qquad (\text{\texttt{sharpSAT_eq_post}}).$$ Multiplying before dividing
avoids computing $N - K$, which is negative when $\varphi$ has empty
clauses ($K$ counts them, $N$ does not); then the quotient is $0$, which
is correct. The post-processing needs only binary multiplication,
division, remainder and powers of two on numbers of polynomially many
bits, all polynomial-time in Complexitylib; the construction of $\psi$
is polynomial-time; and the oracle is called once, on $\psi$
(`toMonotone_polyTime`, `post_polyTime`, `sharpSAT_oneCallReducible`).
Composing with the parsimonious \#P-hardness of \#SAT gives
`sharpMonotone2SAT_oneCallSharpPHard`, and with the reduction to
*countValidMonotone2*, the second half of Theorem 4. The development
also keeps the conditional form,
`countValidMonotone2_oneCallSharpPComplete_bin`, which takes
\#Monotone-2SAT’s hardness as a hypothesis; Theorem 4 discharges it.

## 7 Where the hardness comes from

The reductions of Sections 4 and 5 use clause constraints and as many
attributes as the formula has variables. Removing either ingredient
makes all three problems polynomial-time (Table 2).

#### No constraints.

Then every state is valid and $|M(T_0)| = \prod_i d_i - r$, where $r$ is
the number of *distinct* rows that are states
(`missingCount_eq_of_noConstraints`). The product can be exponential in
$|x|$, but its binary encoding is no longer than those of the factors
together, so a fold that multiplies in binary stays polynomial: each
intermediate product has at most $|x|$ bits. The count is therefore
polynomial-time, and so are completeness and non-emptiness, which
compare $\prod_i d_i$ with $r$ (`missingCountNoConstraints_polyTime`,
`completeNoConstraints_mem_P`, `missingNonemptyNoConstraints_mem_P`).

#### At most $k$ attributes: deciding.

With binary domain sizes, $\mathcal{D}$ cannot be enumerated even for
$k = 1$. Let $N$ be the number of value entries written in the instance,
in conditions and in rows, and call a number *unwritten* if it occurs in
none of them. An unwritten value satisfies no condition, and a state
containing one is not a row; so in a missing state, an unwritten value
can be replaced by any other unwritten value of the same domain, and the
state stays missing. At most $N$ of the numbers $0, \dots, N$ are
written, so one of them, $u$, is unwritten. If a missing state uses an
unwritten value $v > N$ in attribute $i$, then $d_i > v > u$, so $u$ is
in the domain and can replace $v$. Hence if a missing state exists, one
exists whose values lie among $0, \dots, N$ and the written values: at
most $2N+1$ candidates per attribute and $(2N+1)^k$ candidate states
(`length_candidateStates_le`, `exists_missing_candidate_iff`). Checking
each candidate is polynomial, so both decision problems are in P for
each $k$ (`missingNonemptyFixedAttrs_mem_P`,
`completeFixedAttrs_mem_P`).

#### At most $k$ attributes: counting.

A candidate state stands for all the states obtained by replacing its
unwritten values, so counting must weigh it. For each attribute, split
its domain into classes: each written value inside the domain alone, and
one class holding all the unwritten values of the domain (possibly
empty), represented by $u$. Which conditions a state satisfies, and
whether it is a row, depend only on its vector of classes, so
$$|M(T_0)| = \sum_{\substack{c \text{ a class vector,}\\ \text{valid and not a row}}}\
\prod_{i} |c_i|
\qquad (\text{\texttt{missingCount_eq_weighted_of_le}}),$$ over at most
$(N+1)^k$ class vectors (`length_classStates_le`). Each product is at
most $\prod_i d_i$, so the sum is computed in binary by the
bounded-growth fold of the no-constraint case, and the count is
polynomial-time for each $k$ (`missingCountFixedAttrs_polyTime`).

#### An explicit degree.

“Polynomial time for each $k$” allows the polynomial to depend on $k$
arbitrarily. We bound it with Complexitylib’s `ComputableTidilyInO`,
which keeps explicit bound functions and a single constant through
composition, case splits and folds. Three statements are proved, each
for non-emptiness, completeness and counting, each for time and space:

1.  *One machine for all instances.* There are $c, d$ such that one
    machine decides non-emptiness on every instance within
    $c\,(|x|+1)^{dn+d}$, where $n$ is the instance’s number of
    attributes (`missingNonempty_explicitDegree`; Appendix A).

2.  *Uniform in $k$* (`missingNonemptyFixedAttrs_uniform`). There are
    $c, d_0, d_1$ such that for every $k$, on instances with at most $k$
    attributes, one machine decides the problem within
    $c\,(|x|+1)^{d_0 k + d_1}$.

3.  *$k$ in the input.* There are $c, d$ such that one machine, given
    $k$ in unary and an instance, decides “at most $k$ attributes and
    $M(T_0) \neq \emptyset$” within $c\,(|(k,x)|+1)^{dk+d}$
    (`missingNonemptyWithBound_explicitDegree`).

The degree grows linearly with the number of attributes. This is an XP
bound, $|x|^{O(k)}$, not fixed-parameter tractability,
$f(k) \cdot |x|^{O(1)}$; we claim no FPT result.

*What is not proved.* For each fixed $k$, a separate machine with $k$
built in that rejects instances with more than $k$ attributes, with
constants independent of $k$. Testing $n \le k$ inside the machine goes
through Complexitylib’s case-split and constant-output lemmas, whose
constants depend on the machine, and making them uniform would need
changes to the library. Statements 2 and 3 cover the same ground: the
first on the instances where the answer can be positive, the second on
all instances with $k$ given as input.

<div class="tabular">

L0.15L0.11L0.17L0.2L0.17 constraints & attributes & deciding & counting
& hardness via  
clauses & unbounded & NP-, coNP-complete & \#P-complete & many-one,
parsimonious  
none & unbounded & P & polynomial-time & –  
clauses & at most $k$ & P, degree $O(k)$ & polynomial-time, degree
$O(k)$ & –  
monotone two-literal & unbounded & trivial & one-call \#P-complete &
one-call  

</div>

## 8 Related work

#### Hardness of coverage.

Hardness of rule coverage is not new in itself. Elmallah and Gouda prove
firewall completeness NP-hard by reduction from 3-SAT, with no
membership result ([Elmallah and Gouda 2017](#ref-ElmallahGouda2017)).
Thiemann and Yamada prove pattern completeness co-NP hard and verify
their decision procedure in Isabelle, the hardness proof being on
paper ([Thiemann and Yamada 2026](#ref-ThiemannYamada2026)). Kapur et
al. showed quasi-reducibility co-NP complete ([Kapur et al.
1991](#ref-KapurNRZ1991)), and the volume of a union of boxes is
\#P-hard ([Bringmann and Friedrich 2010](#ref-BringmannFriedrich2010)).

#### Rule bases and tables.

Levy and Rousset gave the first complexity results for verifying rule
bases ([Levy and Rousset 1996](#ref-LevyRousset1996),
[1998](#ref-LevyRousset1998)): whether no legal input derives a bad
output, for relational inputs and Horn rules, NP-complete to undecidable
depending on recursion, and $\Pi_2^p$-complete with order predicates and
negation. Their “input completeness” constraints restrict which inputs
are legal, and they leave output completeness open. Coverage of a
propositional table could be phrased in their framework, but its
complexity is lower: coNP for completeness, as shown here, with NP for
non-emptiness and \#P for counting. Menghi et al. prove completeness of
Simulink Requirements Tables undecidable, by reduction from Hilbert’s
tenth problem, because their conditions range over real-valued signals,
and check it with SMT ([Menghi et al. 2025](#ref-MenghiEtAl2025);
[Zanenga et al. 2025](#ref-ZanengaEtAl2025)). Vu and Demetrovics study
decision tables whose entries may be unknown: for one given input,
deciding its possible and certain decisions is NP- and coNP-complete,
and counting the valuations yielding a decision \#P-hard, all by
encoding a formula in the constraints on the unknowns ([Vu and
Demetrovics 2026](#ref-VuDemetrovics2026)). They define completeness for
a single input but state no complexity for deciding it. Their model asks
what a partly unknown table says about one input; ours asks whether a
fully specified table covers every input its declared domains and
constraints allow, which is the check a DMN analyser performs. The
closest precedent for tables in a proof assistant is PVS, which
generates coverage and disjointness obligations for tabular
specifications ([Owre, Rushby, and Shankar
1997](#ref-OwreRushbyShankar1997)): proof obligations about given
tables, not complexity results. To our knowledge, none of these works
classifies the completeness of decision tables over declared finite
domains, or counts their missing combinations, and none of the hardness
proofs is machine-checked.

#### Mechanised complexity.

Cook–Levin has been mechanised in ACL2 ([Gamboa and Cowles
2004](#ref-GamboaCowles2004)), Coq ([Gäher and Kunze
2021](#ref-GaeherKunze2021)) and Isabelle ([Balbach
2023](#ref-Cook_Levin-AFP)), and Senellart and Gnatenko prove all 21 of
Karp’s problems NP-complete in Lean ([Senellart and Gnatenko
2026](#ref-SenellartGnatenko2026)), with NP defined in
descriptive-complexity terms and first-order reductions. Our setting
needs explicit encodings and running times, but its classes are the
textbook ones on Turing machines, so polynomial time, binary encodings
of numbers and the size of the input, the quantities the tractability
results of Section 7 are about, are first-class.

## 9 The formalisation

#### Trust.

The axiom audit prints the axioms of 300 theorems, among them every
theorem this paper cites; each uses only `propext`, `Classical.choice`
and `Quot.sound`, or fewer, and none uses `sorryAx`. This shows that no
proof is left unfinished and no axiom is added. It does not show that
the definitions are the intended ones. The trusted base is Lean’s
kernel; Complexitylib’s definitions of machines, running time, encodings
and the classes P, NP, coNP and \#P; our encoding of instances; and
Definition 1. The adequacy theorems remove one item from that list: the
encoded problems are proved equal to latc-check’s, so a reader need
trust only latc-check’s definition of the missing set and our map from
an instance to the table it denotes, each a few lines (Sections 2 and
3).

#### Engineering.

The development has 4 227 lines of Lean, besides the audit files.
Complexitylib’s `fun_prop` discharged most composition steps of
polynomial-time proofs. Proofs by hand were needed where the size of
intermediate values matters: the binary product of the domain sizes, the
enumeration of candidate states (by induction on $k$), the explicit
bounds of Section 7, and the arithmetic of Valiant’s post-processing.
For the graph of Section 6, `fun_prop` timed out until each
vertex-numbering and edge helper had its own composable polynomial-time
lemma. Reading a list at a binary index needed a library lemma,
`listGetD_binary`, rather than a new proof. The development pins one
commit of Complexitylib, a library that changes daily on a
release-candidate toolchain; it also builds unchanged against a later
commit on the next toolchain (Appendix B).

#### Worst case and practice.

NP-hardness does not make real DMN tables slow to check. Their
constraints are often absent or sparse, and their number of input
columns is small: exactly the regimes of Section 7. What the
classification rules out is a polynomial algorithm for all tables with
clause constraints, unless P = NP; what the tractable cases show is that
the difficulty comes from the constraints across many attributes, not
from the size of the domains or of the table.

## 10 Conclusion

Decision-table completeness under clause constraints is coNP-complete,
finding a missing combination NP-complete, and counting them
\#P-complete, with machine-checked proofs on Turing machines that apply
to latc-check’s set-based definitions; without constraints, or with a
fixed number of attributes, all three are polynomial, with a degree
linear in the number of attributes. For monotone two-literal constraints
counting stays \#P-complete under one-call reductions, by a one-call
version of Valiant’s theorem proved in the same model. What remains open
in the formalisation is the per-$k$ machine with constants independent
of $k$. The one-call reductions and the Valiant reduction use only
Complexitylib’s notions and could be offered upstream.

## Appendix A: Main Lean statements

The statements below are copied from the source up to `:=`. Unless
noted, they are in the namespace `Latc.PaperD.General`; `Inst` is the
type of instances of Section 3.

#### Bridge (namespace `Latc.PaperD`).

    theorem holdsAll_eq_eval (S : Prop5.ConSet ℕ) (x : ℕ → Bool) :
        Prop5.holdsAll S x = (toCNF S).eval x
    theorem satisfiable_decode_iff (S : Prop5.ConSet ℕ) :
        Prop5.Satisfiable (Prop5.decode S) ↔ (toCNF S).Satisfiable

#### Instances.

    abbrev Cond := ℕ × ℕ
    abbrev Inst := List ℕ × (List (List Cond) × List (List ℕ))
    def Valid (S : List (List Cond)) (s : List ℕ) : Prop := ∀ c ∈ S, ∃ a ∈ c, CondHolds s a
    def MissingNonempty : Set Inst :=
      {I | ∃ s, InDomains I.1 s ∧ Valid I.2.1 s ∧ s ∉ I.2.2}
    def Complete : Set Inst := MissingNonemptyᶜ

#### Decision problems and counting.

    theorem MissingNonempty_npComplete_bin : NPComplete encInstBin MissingNonempty
    theorem Complete_coNPComplete_bin : coNPComplete encInstBin Complete
    theorem missingNonempty_finset_npComplete_bin :
        NPComplete encInstBin {I : Inst | (missing I.con I.table).Nonempty}
    theorem complete_finset_coNPComplete_bin :
        coNPComplete encInstBin {I : Inst | missing I.con I.table = ∅}
    theorem missingCount_eq_acceptCount (I : Inst) :
        missingCount I = acceptCount cverifier I (certLen I)
    theorem sharpSAT_eq_missingCount (φ : CNF ℕ) : SharpSAT φ = missingCount (fromSAT φ)
    theorem missingCount_sharpPComplete_bin : SharpPComplete encInstBin missingCount

#### One-call reductions and Valiant (namespace `Latc.PaperD.Valiant` for the last two).

    def OneCallReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (f : α → ℕ) (g : β → ℕ) :
        Prop :=
      ∃ (r : α → β) (post : α → ℕ → ℕ), ComputableInPolyTime r encA encB ∧
        ComputableInPolyTime (fun p : α × ℕ => post p.1 p.2) (encPair encA encNat) encNat ∧
          ∀ a, f a = post a (g (r a))
    theorem sharpMonotone2SAT_oneCallSharpPHard :
        OneCallSharpPHard encCNF SharpMonotone2SAT
    theorem countValidMonotone2_sharpPComplete_oneCall :
        OneCallSharpPComplete encInstBin countValidMonotone2

#### Tractability.

    theorem missingCount_eq_of_noConstraints (I : Inst) (h : I.2.1 = []) :
        missingCount I = domProd I - distinctRows I
    theorem missingCountFixedAttrs_polyTime (k : ℕ) :
        ComputableInPolyTime (fun I : Inst => if I.n ≤ k then missingCount I else 0)
          encInstBin encNat
    theorem missingNonempty_explicitDegree :
        ∃ c d, ComputableTidilyInTimeAndSpace
          (fun I : Inst => decide (missing I.con I.table).Nonempty) encInstBin encBool
          (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d))
          (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d))
    theorem missingNonemptyFixedAttrs_uniform :
        ∃ c d₀ d₁, ∀ k, ComputableTidilyInTimeAndSpace
          (fun I : {I : Inst // I.n ≤ k} => decide (missing I.1.con I.1.table).Nonempty)
          ((Function.Embedding.subtype _).trans encInstBin) encBool
          (fun I => c * ((encInstBin I.1).length + 1) ^ (d₀ * k + d₁))
          (fun I => c * ((encInstBin I.1).length + 1) ^ (d₀ * k + d₁))

## Appendix B: Artifact and reproducibility

#### Contents.

The development is the directory `LatcComplexity/` of the repository
latc-complexity: 4 577 lines of Lean in 15 files, 4 227 without the two
axiom-audit files, on top of latc-check’s model, copied unchanged into
`LatcFormal/`. The README lists every theorem with its statement, and
`docs/paper-facts.md` records the file and line of every theorem this
paper cites.

#### Versions.

Lean `v4.36.0-rc1`; Complexitylib at commit `b7acfc2` (28 October 2026),
with the CSLib and Mathlib it pins. The pin was kept throughout the
development. Complexitylib had just been rewritten on CSLib; the earlier
version, which Russell ([Russell 2026a](#ref-PaperA)) cites, is a
separate repository with a different API.

#### Build and audit.

From a fresh clone, downloading precompiled Mathlib, `lake build`
completed 18 645 jobs with no warnings or errors in about nine minutes
on four cores, using 12 GB of disk. The axiom audit (the two files
`Axioms.lean` of `LatcComplexity/` and of its subdirectory `Valiant/`)
prints 300 theorems: 253 use all three standard axioms, 47 fewer, none
`sorryAx`. The development also builds without any change against
Complexitylib commit `b9e6241` on Lean `v4.36.0-rc2` (18 717 jobs), but
the artifact is published with the pin above, against which the results
were proved.

#### History.

The core results took seven commits over about ten hours on 28–29
October 2026. On 31 October, counting with a fixed number of attributes,
the Valiant reduction (1 238 lines) and the explicit degree (692 lines)
were added, the last two in parallel and merged without conflicts.

## References

<div id="refs" class="references csl-bib-body hanging-indent">

<div id="ref-Cook_Levin-AFP" class="csl-entry">

Balbach, Frank J. 2023. “The Cook-Levin Theorem.” *Archive of Formal
Proofs*.

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

<div id="ref-LevyRousset1998" class="csl-entry">

———. 1998. “Verification of Knowledge Bases Based on Containment
Checking.” *Artificial Intelligence* 101 (1–2): 227–50.
<https://doi.org/10.1016/S0004-3702(98)00021-6>.

</div>

<div id="ref-MenghiEtAl2025" class="csl-entry">

Menghi, Claudio, Eugene Balai, Darren Valovcin, Christoph Sticksel, and
Akshay Rajhans. 2025. “Completeness and Consistency of Tabular
Requirements: An SMT-Based Verification Approach.” *IEEE Transactions on
Software Engineering* 51 (2): 595–620.
<https://doi.org/10.1109/TSE.2025.3530820>.

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

<div id="ref-VuDemetrovics2026" class="csl-entry">

Vu, Duc Nghia, and Janos Demetrovics. 2026. “Labeled Null Semantics for
Incomplete Decision Tables: Certain, Possible, and Conditional Decision
Reasoning.” *Algorithms* 19 (9): 725.
<https://doi.org/10.3390/a19090725>.

</div>

<div id="ref-ZanengaEtAl2025" class="csl-entry">

Zanenga, Aurora Francesca, Nunzio Marco Bisceglia, Benedetta Ippoliti,
Andrea Bombarda, Angelo Gargantini, Akshay Rajhans, and Claudio Menghi.
2025. “Theano: A Tool for Verifying the Consistency and Completeness in
Tabular Requirements.” In *Proceedings of the 33rd ACM International
Conference on the Foundations of Software Engineering (FSE Companion
’25)*, 1148–52. ACM. <https://doi.org/10.1145/3696630.3728599>.

</div>

</div>
