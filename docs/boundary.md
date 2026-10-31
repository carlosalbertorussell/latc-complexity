# Where the hardness comes from: theorem statements

Planning note for the tractable side and the binary attribute index (Paper D), written before the
proofs and updated to the names proved in `LatcComplexity/Tractable.lean` and
`LatcComplexity/Binary.lean`; the README holds the final tables.

## Instances and encodings

An instance is `I = (d, S, T) : Inst` (`LatcComplexity/General.lean`): domain sizes `d`, clauses
`S` of conditions `(i, v)`, rows `T` of T₀. It denotes the table `I.con`, `I.table` of
latc-check's model (`LatcComplexity/Adequacy.lean`); `missingCount I = (missing I.con I.table).card`.

* `encInst` (existing): numbers binary, the attribute index `i` of a condition unary.
* `encInstBin` (new): every number binary, the attribute index included. The identity is
  polynomial-time from `encInst` to `encInstBin` (`encInst_to_encInstBin_polyTime`), so a
  polynomial-time upper bound for `encInstBin` gives one for `encInst`, and hardness for `encInst`
  transfers to `encInstBin`.

## Hardness (existing, and new binary versions)

The SAT reduction `fromSAT` produces instances with **constraints** (one clause per clause of φ)
and **φ.numVars attributes**, unbounded; T₀ = ∅.

| Statement | Unary index (existing) | Binary index (new) |
|---|---|---|
| M(T₀) ≠ ∅ is NP-complete | `MissingNonempty_npComplete` | `MissingNonempty_npComplete_bin` |
| completeness is coNP-complete | `Complete_coNPComplete` | `Complete_coNPComplete_bin` |
| same, on `Latc.missing` | `missingNonempty_finset_npComplete`, `complete_finset_coNPComplete` | `..._bin` |
| counting \|M(T₀)\| is #P-complete | `missingCount_sharpPComplete` | `missingCount_sharpPComplete_bin` |

## Tractable side (new), all under `encInstBin`, adequacy to `Latc.missing` built in

Restricted problems follow Complexitylib's convention for `SharpThreeSAT`: the restriction is part
of the problem, so a decider also checks the shape.

(a) No constraints (`S = []`), any number of attributes, T₀ arbitrary:

* `completeNoConstraints_mem_P : {I | I.2.1 = [] ∧ missing I.con I.table = ∅} ∈ P encInstBin`
* `missingNonemptyNoConstraints_mem_P :
  {I | I.2.1 = [] ∧ (missing I.con I.table).Nonempty} ∈ P encInstBin`
* (c) `missingCountNoConstraints_polyTime :
  ComputableInPolyTime (fun I => if I.2.1 = [] then missingCount I else 0) encInstBin encNat`
* `missingCount_eq_of_noConstraints : I.2.1 = [] → missingCount I = domProd I - distinctRows I`,
  where `domProd I = ∏ dᵢ` and `distinctRows I` is the number of distinct rows of T₀ inside the
  declared domains.

∏ dᵢ can be exponential in the input length but its binary encoding is no longer than the
encodings of the dᵢ together (`length_encNat_mul_le`), so it is computed exactly in binary and
compared (subtracted) in binary: no unary blow-up.

(b) At most `k` attributes, constraints arbitrary, domains given in binary in the input:

* `completeFixedAttrs_mem_P (k : ℕ) : {I | I.n ≤ k ∧ missing I.con I.table = ∅} ∈ P encInstBin`
* `missingNonemptyFixedAttrs_mem_P (k : ℕ) :
  {I | I.n ≤ k ∧ (missing I.con I.table).Nonempty} ∈ P encInstBin`
* `length_candidateStates_le : (candidateStates k I).length ≤ (2 * I.numVals + 1) ^ k`, with
  `I.numVals` the number of values written in `S` and `T`.
* Each also for `encInst`, with the suffix `_unary`.

With binary domain sizes |𝒟| = ∏ dᵢ is *not* polynomial even for k = 1 (a single domain of size
2ᵐ). The algorithm searches instead, for each attribute, the values `0, …, N` and the values
written in the instance (`N` = number of written values), restricted to the domain: a missing
state exists iff one exists among these candidates (`exists_missing_candidate_iff`), because a
value not written anywhere can be replaced by an unwritten value `≤ N` without changing which
conditions hold or whether the state is a row. The search space has at most `(2N + 1)ᵏ` states,
so, informally, the running time is polynomial of degree growing linearly in `k`; the theorem certifies polynomial time for each fixed
`k`, and the bound on the search space is the formal statement of the `k`-dependence.

(c) for (b), counting with a fixed number of attributes:

* `missingCountFixedAttrs_polyTime (k : ℕ) :
  ComputableInPolyTime (fun I => if I.n ≤ k then missingCount I else 0) encInstBin encNat`
  (and `_unary` for `encInst`).
* `missingCount_eq_weighted_of_le : I.n ≤ k → missingCount I = ((classStates k I).map fun c =>
  if validB (I, c) then classStateWeight (I, c) else 0).sum`: each written value is its own class
  and the unwritten values form one class of size `dᵢ − #written values below dᵢ`; a valid class
  vector that is not a row of T₀ counts with the product of its class sizes.
* `length_classStates_le : (classStates k I).length ≤ (I.numVals + 1) ^ k`.

## The boundary

| | constraints | attributes | complexity |
|---|---|---|---|
| hardness (`fromSAT`) | yes (CNF clauses) | unbounded | NP-/coNP-/#P-complete |
| (a) | none | unbounded | P, counting in FP |
| (b) | any clauses | ≤ k | P for each k, counting in FP for each k |

Hardness needs both constraints and an unbounded number of attributes.
