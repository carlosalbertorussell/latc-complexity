# Gap 1: Valiant's theorem in Complexitylib's model — progress

Status (2026-10-31, branch `claude/gap1-valiant`): **done**. The hypothesis `hValiant` is proved,
and the monotone case of Proposition 5 is unconditional. Nothing on `main` was edited: the new
code is in `LatcComplexity/Valiant/` and imported from `LatcComplexity.lean` on this branch.

## What is proved (namespace `Latc.PaperD.Valiant`)

```lean
theorem sharpMonotone2SAT_oneCallSharpPHard : OneCallSharpPHard encCNF SharpMonotone2SAT

theorem countValidMonotone2_sharpPComplete_oneCall :
    OneCallSharpPComplete encInstBin countValidMonotone2

theorem countValidMonotone2_sharpPComplete_oneCall_unary :
    OneCallSharpPComplete General.encInst countValidMonotone2
```

`OneCallSharpPHard`, `OneCallSharpPComplete`, `SharpMonotone2SAT`, `countValidMonotone2`,
`encInst` and `encInstBin` are those of `LatcComplexity/Monotone.lean`, `General.lean` and
`Binary.lean`, unchanged. The corollaries are `countValidMonotone2_oneCallSharpPComplete(_bin)`
applied to the first theorem. The main intermediate results:

```lean
theorem sharpSAT_oneCallReducible :
    OneCallReducible encCNF encCNF SharpSAT SharpMonotone2SAT

theorem sharpSAT_eq_post (φ : CNF ℕ) : SharpSAT φ = post φ (SharpMonotone2SAT (toMonotone φ))

theorem toMonotone_polyTime : ComputableInPolyTime toMonotone encCNF encCNF

theorem post_polyTime : ComputableInPolyTime (fun p : CNF ℕ × ℕ => post p.1 p.2)
    (encPair encCNF encNat) encNat

theorem ParsimoniousReducible.trans_oneCall {α β γ : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {f : α → ℕ} {g : β → ℕ} {h : γ → ℕ}
    (hfg : ParsimoniousReducible encA encB f g) (hgh : OneCallReducible encB encC g h) :
    OneCallReducible encA encC f h
```

Axiom audit: `LatcComplexity/Valiant/Axioms.lean`, 80 `#print axioms`, each a subset of
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `native_decide`, `axiom` or
`set_option`.

## The route actually taken

The plan (`docs/gaps-plan.md`) chains #SAT → #IS_k → #AllIS → #Monotone-2SAT. The proof here
fuses the chain into **one** reduction `#SAT → #Monotone-2SAT` with one oracle call, which needs
neither a separate counting problem for independent sets nor a transitivity lemma for two
one-call reductions (only parsimonious ∘ one-call, `ParsimoniousReducible.trans_oneCall`, to
start from Complexitylib's `CookLevin.SharpSAT_sharpPHard`). The mathematics is the same:

1. **Parsimonious SAT → maximum independent sets** (`Counting.lean`). After dense relabelling
   (variables `0, …, n−1`), the conflict graph has a vertex `(i, b)` for each variable and value,
   and a vertex per literal occurrence, read "the first true literal of its clause". Edges:
   `(i, true)–(i, false)`; two occurrences of one clause; an occurrence and the opposite value of
   its variable; an occurrence and the value making an earlier literal of its clause true. The
   vertices split into `n + m` cliques, so independent sets have at most `K = n + m` vertices
   (`card_le_of_indep`), and those of size `K` are in bijection with the models
   (`modelCount_eq_card`). The "first true literal" gadget is what makes it parsimonious for
   arbitrary CNF (no 3-CNF restriction, repeated and complementary literals allowed).
2. **Pendant leaves** (`Pendant.lean`): `t = n + 1` leaves per vertex; each edge `{u, w}` becomes
   the clause `x_u ∨ x_w` (so `monotone2B` holds, `monotone2B_psi`). Models are complements of
   independent sets of the graph with leaves, and
   `modelCount = Σ_{S indep} 2^(t (N − |S|))` (`modelCount_psi`), `N` the number of vertices
   (`card_V0 : N = 2n + |occurrences|`). Every vertex has a leaf, so no vertex is isolated and
   no post-multiplication by `2^(#isolated)` is needed.
3. **The digit** (`OneCall.lean`, `digit`): with `#SAT φ ≤ 2^n < 2^t`,
   `#SAT φ = x · 2^(tK) / 2^(tN) mod 2^t`, `x` the oracle answer. Multiplying by `2^(tK)` before
   dividing avoids a truncated subtraction `N − K`, which matters when `φ` has empty clauses
   (`K > N` is possible; then no independent set has size `K` and the digit is 0).

## Encodings and representation

Vertices are natural numbers: `vv i b = 3·pair(i, b)`, `cv o = 3·pair(clause, position) + 1`,
leaf `lv u q = 3·pair(u, q) + 2` (Cantor pairing). The construction `psi` works on the unary
encoding of the densely relabelled formula (`CNF.computableInPolyTime_denseRelabel_unary`) and
is converted to `encCNF` by `CNF.relabel id`, as Complexitylib's `computableInPolyTime_denseRelabel`
does. Polynomial time is by `fun_prop`, with compositional lemmas `vv_polyTime'`, `cv_polyTime'`,
`lv_polyTime'`, `edge_polyTime'`; `post` uses Complexitylib's `binary_two_pow`, `binary_mul'`,
`binary_div'`, `binary_mod'`.

## Files

| File | Contents |
|---|---|
| `LatcComplexity/Valiant/Gadget.lean` | `vv`, `cv`, `lv`, `edge`, `graphClauses`, `verts`, `leafClauses`, `psi`, `toMonotone`, `post`; polynomial time |
| `LatcComplexity/Valiant/Counting.lean` | codes, membership, `Indep`, the clique bound, `setOf`, `modelCount_eq_card` |
| `LatcComplexity/Valiant/Pendant.lean` | `modelCount_psi` |
| `LatcComplexity/Valiant/OneCall.lean` | `digit`, `sharpSAT_eq_post`, the hardness theorem and corollaries |
| `LatcComplexity/Valiant/Axioms.lean` | the axiom audit |

## Build

`lake build` on this branch: `Build completed successfully (18643 jobs)`, no warnings, no errors
(Lean 4.36.0-rc1, Complexitylib `b7acfc2`, Linux cloud machine, 4 cores). Commands:

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o elan-init.sh
sh elan-init.sh -y --default-toolchain none
lake exe cache get
lake build
```

## What remains

Nothing for Gap 1 itself. After merging (to be done on `main`, outside this branch's scope):

* `README.md`, `docs/paper-facts.md` and the Paper D draft still describe `hValiant` as an open
  hypothesis; they should cite `sharpMonotone2SAT_oneCallSharpPHard` and the two corollaries.
* The module docstring of `LatcComplexity/Monotone.lean` says the hypothesis is not proved in
  Complexitylib's model; it can point to `LatcComplexity/Valiant/OneCall.lean`.
* `LatcComplexity/Axioms.lean` on `main` may absorb `Valiant/Axioms.lean`.
* Optionally, offer the reduction upstream to Complexitylib (it only uses Complexitylib names
  apart from `OneCallReducible`).
