# Gap 3: an explicit degree in k (progress)

Branch `claude/gap3-explicit-degree`, from `main` at `242311b`. New file
`LatcComplexity/ExplicitDegree.lean`; `#print axioms` lines for its 46 theorems and lemmas
appended to `LatcComplexity/Axioms.lean` (which now imports it). No existing statement, pin or
other file changed.

## Status

Done. Uniformity in k is proved for the non-emptiness decider, the completeness decider and the
counter, in time and in space. `lake build` ends with `Build completed successfully (18627 jobs)`,
no warnings, no errors; every new name prints a subset of `[propext, Classical.choice, Quot.sound]`.

## What is proved

Here `Inst.n I = I.1.length` (the number of attributes) and `|x| = (encInstBin I).length`.

1. **One machine for all instances** (`*_explicitDegree`): time and space
   `c · (|x| + 1) ^ (d · n + d)`, for constants `c` and `d`.
2. **Uniform in k on the instances with at most k attributes** (`*FixedAttrs_uniform`):
   `∃ c d₀ d₁, ∀ k`, the bound `c · (|x| + 1) ^ (d₀ · k + d₁)`, the form asked for in the plan.
3. **The fixed-k procedures on every instance, k in the input** (`*WithBound_explicitDegree`): the
   sets of `missingNonemptyFixedAttrs_mem_P` and `completeFixedAttrs_mem_P` and the function of
   `missingCountFixedAttrs_polyTime`, as one machine on pairs `(k, I)` (`k` in unary), within
   `c · (|(k, x)| + 1) ^ (d · k + d)`.

Statements, verbatim:

```lean
theorem missingNonempty_explicitDegree :
    ∃ c d, ComputableTidilyInTimeAndSpace
      (fun I : Inst => decide (missing I.con I.table).Nonempty) encInstBin encBool
      (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d))
      (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d))
```

```lean
theorem complete_explicitDegree :
    ∃ c d, ComputableTidilyInTimeAndSpace
      (fun I : Inst => decide (missing I.con I.table = ∅)) encInstBin encBool
      (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d))
      (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d))
```

```lean
theorem missingCount_explicitDegree :
    ∃ c d, ComputableTidilyInTimeAndSpace (fun I : Inst => missingCount I) encInstBin encNat
      (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d))
      (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d))
```

```lean
theorem missingNonemptyFixedAttrs_uniform :
    ∃ c d₀ d₁, ∀ k, ComputableTidilyInTimeAndSpace
      (fun I : {I : Inst // I.n ≤ k} => decide (missing I.1.con I.1.table).Nonempty)
      ((Function.Embedding.subtype _).trans encInstBin) encBool
      (fun I => c * ((encInstBin I.1).length + 1) ^ (d₀ * k + d₁))
      (fun I => c * ((encInstBin I.1).length + 1) ^ (d₀ * k + d₁))
```

```lean
theorem completeFixedAttrs_uniform :
    ∃ c d₀ d₁, ∀ k, ComputableTidilyInTimeAndSpace
      (fun I : {I : Inst // I.n ≤ k} => decide (missing I.1.con I.1.table = ∅))
      ((Function.Embedding.subtype _).trans encInstBin) encBool
      (fun I => c * ((encInstBin I.1).length + 1) ^ (d₀ * k + d₁))
      (fun I => c * ((encInstBin I.1).length + 1) ^ (d₀ * k + d₁))
```

```lean
theorem missingCountFixedAttrs_uniform :
    ∃ c d₀ d₁, ∀ k, ComputableTidilyInTimeAndSpace
      (fun I : {I : Inst // I.n ≤ k} => missingCount I.1)
      ((Function.Embedding.subtype _).trans encInstBin) encNat
      (fun I => c * ((encInstBin I.1).length + 1) ^ (d₀ * k + d₁))
      (fun I => c * ((encInstBin I.1).length + 1) ^ (d₀ * k + d₁))
```

```lean
theorem missingNonemptyWithBound_explicitDegree :
    ∃ c d, ComputableTidilyInTimeAndSpace
      (fun p : ℕ × Inst => decide (p.2.n ≤ p.1 ∧ (missing p.2.con p.2.table).Nonempty))
      (encPair encUnary encInstBin) encBool
      (fun p => c * ((encPair encUnary encInstBin p).length + 1) ^ (d * p.1 + d))
      (fun p => c * ((encPair encUnary encInstBin p).length + 1) ^ (d * p.1 + d))
```

```lean
theorem completeWithBound_explicitDegree :
    ∃ c d, ComputableTidilyInTimeAndSpace
      (fun p : ℕ × Inst => decide (p.2.n ≤ p.1 ∧ missing p.2.con p.2.table = ∅))
      (encPair encUnary encInstBin) encBool
      (fun p => c * ((encPair encUnary encInstBin p).length + 1) ^ (d * p.1 + d))
      (fun p => c * ((encPair encUnary encInstBin p).length + 1) ^ (d * p.1 + d))
```

```lean
theorem missingCountWithBound_explicitDegree :
    ∃ c d, ComputableTidilyInTimeAndSpace
      (fun p : ℕ × Inst => if p.2.n ≤ p.1 then missingCount p.2 else 0)
      (encPair encUnary encInstBin) encNat
      (fun p => c * ((encPair encUnary encInstBin p).length + 1) ^ (d * p.1 + d))
      (fun p => c * ((encPair encUnary encInstBin p).length + 1) ^ (d * p.1 + d))
```

```lean
theorem allSections_inO : ∃ D, ComputableTidilyInO allSections encLL encLL
    (fun L => ((encLL L).length + 1) ^ (D * (L.length + 1)))
    (fun L => ((encLL L).length + 1) ^ (D * (L.length + 1)))
```

```lean
theorem pipeline_inO {β : Type} {encOut : β ↪ List Bool} {lists : Inst → List (List ℕ)}
    {test : Inst × List (List ℕ) → β}
    (hlists : ComputableTidilyInPolyTime lists encInstBin encLL)
    (hlen : ∀ I, (lists I).length = I.n)
    (htest : ComputableTidilyInPolyTime test (encPair encInstBin encLL) encOut) :
    ∃ T S, ComputableTidilyInO (fun I => test (I, allSections (lists I))) encInstBin encOut T S ∧
      XPBounded instSize Inst.n T ∧ XPBounded instSize Inst.n S
```

```lean
theorem someCandidateMissing_inO : ∃ T S,
    ComputableTidilyInO (fun I : Inst => someCandidateMissing I.n I) encInstBin encBool T S ∧
      XPBounded instSize Inst.n T ∧ XPBounded instSize Inst.n S
```

```lean
theorem missingCount_inO : ∃ T S,
    ComputableTidilyInO (fun I : Inst => missingCount I) encInstBin encNat T S ∧
      XPBounded instSize Inst.n T ∧ XPBounded instSize Inst.n S
```

## Method

`ComputableTidilyInPolyTime` hides its bounds; Complexitylib's `ComputableTidilyInO f encIn encOut
T S` keeps explicit bound functions `T`, `S` with a single existential constant, and its `comp`,
`ite`, `prod` and `foldl` compute the bounds. Polynomial-time pieces enter through
`inO_pow_of_polyTime` (bounds `(|x| + 1) ^ d`). All sections of `n` lists are a left fold
(`allSections`, equal to `boundedSections n` by `allSections_eq`) whose states have encoding at most
`4 · (|L| + 1) ^ (n + 2)` (`length_state_le`), giving `allSections_inO`. `pipeline_inO` composes a
polynomial-time list builder (`candLists`, or `classVals` per attribute), `allSections` and a
polynomial-time test (`anyCheck`, or `countTest`). `XPBounded size n T` (`T ≤ c · (size + 1) ^
(e · (n + 1))`) is closed under sums, constant factors and fixed powers; constants are absorbed
into the exponent since `|x| ≥ 1` (`mul_pow_le_pow_add`). `timeAndSpace_of_inO_xp` gives the final
`ComputableTidilyInTimeAndSpace`.

## What remains, and why

Nothing of the plan. One formulation is not proved: for each fixed `k`, the fixed-`k` decider on
*all* instances (rejecting when `n > k`), with `x` alone as input and constants independent of `k`.
Its machine must test `n ≤ k` with `k` built into the machine, and Complexitylib's constant
machine (`computableInTimeAndSpace_of_const`) and case distinction carry constants that depend on
the machines, so they cannot be made uniform from outside the library. The two proved
formulations cover it: (2) on the instances where the decider can answer yes, and (3) with `k`
read from the input.

## Next step

None needed. If wanted: mention the three formulations in README.md and Paper D Section 7 (not
edited on this branch, as instructed).
