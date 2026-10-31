import LatcComplexity.Monotone
import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Logics.Propositional.CNF.ModelCount.DenseRelabel

/-!
# The one-call reduction from `#SAT` to `#Monotone-2SAT`: construction and polynomial time

The formula `φ` is first relabelled densely (`CNF.denseRelabel`), variables `0, …, n - 1`.
Its conflict graph has a vertex `(i, b)` for each variable `i < n` and value `b`, and a vertex for
each literal occurrence `o` (clause `o.1`, position `o.2.1`), read "this literal is the first
true one of its clause". Edges: `(i, true)`–`(i, false)`; two occurrences of the same clause;
an occurrence and the vertex of the opposite value of its variable; an occurrence and the vertex
making an earlier literal of its clause true. Every vertex gets `t = n + 1` pendant leaves. Each
edge `{u, w}` is the monotone clause `x_u ∨ x_w`; its models are the complements of the
independent sets of the graph with leaves.

Vertices are natural numbers: `vv i b = 3·⟨i, b⟩`, `cv o = 3·⟨o.1, o.2.1⟩ + 1`, and the leaf
`lv u q = 3·⟨u, q⟩ + 2`, with Cantor pairing `⟨·, ·⟩` (`Nat.pair`).
-/

namespace Latc.PaperD.Valiant

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-- Code of the variable vertex `(i, b)`. -/
def vv (i : ℕ) (b : Bool) : ℕ := 3 * Nat.pair i b.toNat

/-- Code of the clause vertex of an occurrence. -/
def cv (o : Occurrence ℕ) : ℕ := 3 * Nat.pair o.1 o.2.1 + 1

/-- Code of the `q`-th pendant leaf of the vertex coded `u`. -/
def lv (u q : ℕ) : ℕ := 3 * Nat.pair u q + 2

/-- The monotone clause `x_a ∨ x_b`. -/
def edge (a b : ℕ) : Clause ℕ := [(a, true), (b, true)]

/-- The edges of the conflict graph, as monotone clauses. -/
def graphClauses (φ : CNF ℕ) (n : ℕ) : CNF ℕ :=
  (List.range n).map (fun i => edge (vv i true) (vv i false)) ++
    (occurrences φ).flatMap fun o =>
      edge (cv o) (vv o.2.2.1 (!o.2.2.2)) ::
        ((occurrences φ).filter fun o' => o'.1 == o.1 && decide (o'.2.1 < o.2.1)).flatMap
          fun o' => [edge (cv o) (cv o'), edge (cv o) (vv o'.2.2.1 o'.2.2.2)]

/-- The vertices of the conflict graph. -/
def verts (φ : CNF ℕ) (n : ℕ) : List ℕ :=
  (List.range n).flatMap (fun i => [vv i true, vv i false]) ++ (occurrences φ).map cv

/-- The pendant edges: `t` leaves on every vertex. -/
def leafClauses (φ : CNF ℕ) (n t : ℕ) : CNF ℕ :=
  (verts φ n).flatMap fun u => (List.range t).map fun q => edge u (lv u q)

/-- The monotone formula of a formula with dense variables `0, …, n - 1`. -/
def psi (φ : CNF ℕ) (n : ℕ) : CNF ℕ := graphClauses φ n ++ leafClauses φ n (n + 1)

/-- The reduction. -/
def toMonotone (φ : CNF ℕ) : CNF ℕ := psi φ.denseRelabel φ.numVars

/-- Leaves per vertex: `t = n + 1`. -/
def leaves (φ : CNF ℕ) : ℕ := φ.numVars + 1

/-- The size of a maximum independent set of the conflict graph: one vertex per variable and per
clause. -/
def maxSize (φ : CNF ℕ) : ℕ := φ.numVars + φ.length

/-- The number of vertices of the conflict graph. -/
def numVerts (φ : CNF ℕ) : ℕ := 2 * φ.numVars + φ.vars.length

/-- The post-processing: digit of rank `N − K` in base `2^t` of the oracle answer, computed as
`x · 2^(tK) / 2^(tN) mod 2^t` so that no truncated subtraction appears. -/
def post (φ : CNF ℕ) (x : ℕ) : ℕ :=
  x * 2 ^ (leaves φ * maxSize φ) / 2 ^ (leaves φ * numVerts φ) % 2 ^ leaves φ

section PolyTime

/-- Formulas with unary variable indices. -/
abbrev encCNFu : CNF ℕ ↪ List Bool := encList (encList (encPair encUnary encBool))

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

theorem cv_polyTime : ComputableTidilyInPolyTime cv (encOccurrence encUnary) encUnary := by
  unfold cv encOccurrence
  fun_prop

@[fun_prop]
theorem cv_polyTime' {α : Type} {input : α ↪ List Bool} {f : α → Occurrence ℕ}
    (hf : ComputableTidilyInPolyTime f input (encOccurrence encUnary)) :
    ComputableTidilyInPolyTime (fun a => cv (f a)) input encUnary :=
  cv_polyTime.comp hf

theorem lv_polyTime : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => lv p.1 p.2)
    (encPair encUnary encUnary) encUnary := by
  unfold lv
  fun_prop

@[fun_prop]
theorem lv_polyTime' {α : Type} {input : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableTidilyInPolyTime f input encUnary)
    (hg : ComputableTidilyInPolyTime g input encUnary) :
    ComputableTidilyInPolyTime (fun a => lv (f a) (g a)) input encUnary :=
  lv_polyTime.comp (hf.prod hg)

theorem edge_polyTime : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => edge p.1 p.2)
    (encPair encUnary encUnary) (encList (encPair encUnary encBool)) := by
  unfold edge
  fun_prop

@[fun_prop]
theorem edge_polyTime' {α : Type} {input : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableTidilyInPolyTime f input encUnary)
    (hg : ComputableTidilyInPolyTime g input encUnary) :
    ComputableTidilyInPolyTime (fun a => edge (f a) (g a)) input
      (encList (encPair encUnary encBool)) :=
  edge_polyTime.comp (hf.prod hg)

attribute [local fun_prop] ComputableInPolyTime.tidy in
theorem verts_polyTime : ComputableTidilyInPolyTime (fun p : CNF ℕ × ℕ => verts p.1 p.2)
    (encPair encCNFu encUnary) (encList encUnary) := by
  have hocc := (computableInPolyTime_occurrences encUnary).tidy
  unfold verts
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
theorem leafClauses_polyTime : ComputableTidilyInPolyTime
    (fun p : (CNF ℕ × ℕ) × ℕ => leafClauses p.1.1 p.1.2 p.2)
    (encPair (encPair encCNFu encUnary) encUnary) encCNFu := by
  have hv := verts_polyTime
  unfold leafClauses
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
theorem graphClauses_polyTime : ComputableTidilyInPolyTime
    (fun p : CNF ℕ × ℕ => graphClauses p.1 p.2) (encPair encCNFu encUnary) encCNFu := by
  have hocc := (computableInPolyTime_occurrences encUnary).tidy
  unfold graphClauses
  fun_prop

theorem psi_polyTime : ComputableTidilyInPolyTime (fun p : CNF ℕ × ℕ => psi p.1 p.2)
    (encPair encCNFu encUnary) encCNFu := by
  have hg := graphClauses_polyTime
  have hl : ComputableTidilyInPolyTime (fun p : CNF ℕ × ℕ => leafClauses p.1 p.2 (p.2 + 1))
      (encPair encCNFu encUnary) encCNFu :=
    leafClauses_polyTime.comp (show ComputableTidilyInPolyTime
      (fun p : CNF ℕ × ℕ => ((p.1, p.2), p.2 + 1)) (encPair encCNFu encUnary)
        (encPair (encPair encCNFu encUnary) encUnary) by fun_prop)
  unfold psi
  fun_prop

/-- **The reduction is polynomial-time.** -/
theorem toMonotone_polyTime : ComputableInPolyTime toMonotone encCNF encCNF := by
  have h1 := (CNF.computableInPolyTime_denseRelabel_unary encNat).tidy
  have h2 := SAT.computableInPolyTime_numVars.tidy
  have h3 : ComputableTidilyInPolyTime (CNF.relabel (id : ℕ → ℕ)) encCNFu encCNF :=
    (CNF.computableInPolyTime_relabel (encV := encUnary) (encW := encNat)
      (.of_tidy ComputableTidilyInPolyTime.unary_to_binary)).tidy
  have hp := psi_polyTime
  have heq : toMonotone = fun φ => (psi φ.denseRelabel φ.numVars).relabel id := by
    funext φ
    exact (CNF.relabel_id _).symm
  rw [heq]
  refine .of_tidy ?_
  fun_prop

theorem numClauses_polyTime :
    ComputableTidilyInPolyTime (fun φ : CNF ℕ => φ.length) encCNF encUnary :=
  ComputableTidilyInPolyTime.length_list _

theorem numOcc_polyTime :
    ComputableTidilyInPolyTime (fun φ : CNF ℕ => φ.vars.length) encCNF encUnary :=
  (ComputableTidilyInPolyTime.length_list _).comp
    ((ComputableTidilyInPolyTime.map (encB := encNat) (by fun_prop)).comp
      (ComputableTidilyInPolyTime.flatten _))

theorem leaves_polyTime : ComputableTidilyInPolyTime leaves encCNF encUnary := by
  have h2 := SAT.computableInPolyTime_numVars.tidy
  unfold leaves
  fun_prop

theorem expK_polyTime :
    ComputableTidilyInPolyTime (fun φ => leaves φ * maxSize φ) encCNF encUnary := by
  have h2 := SAT.computableInPolyTime_numVars.tidy
  have h3 := numClauses_polyTime
  have h4 := leaves_polyTime
  unfold maxSize
  fun_prop

theorem expN_polyTime :
    ComputableTidilyInPolyTime (fun φ => leaves φ * numVerts φ) encCNF encUnary := by
  have h2 := SAT.computableInPolyTime_numVars.tidy
  have h3 := numOcc_polyTime
  have h4 := leaves_polyTime
  unfold numVerts
  fun_prop

/-- **The post-processing is polynomial-time.** -/
theorem post_polyTime : ComputableInPolyTime (fun p : CNF ℕ × ℕ => post p.1 p.2)
    (encPair encCNF encNat) encNat := by
  have hfst : ComputableTidilyInPolyTime (fun p : CNF ℕ × ℕ => p.1) (encPair encCNF encNat)
      encCNF := by fun_prop
  have hK : ComputableTidilyInPolyTime (fun p : CNF ℕ × ℕ => 2 ^ (leaves p.1 * maxSize p.1))
      (encPair encCNF encNat) encNat :=
    ComputableTidilyInPolyTime.binary_two_pow.comp (expK_polyTime.comp hfst)
  have hN : ComputableTidilyInPolyTime (fun p : CNF ℕ × ℕ => 2 ^ (leaves p.1 * numVerts p.1))
      (encPair encCNF encNat) encNat :=
    ComputableTidilyInPolyTime.binary_two_pow.comp (expN_polyTime.comp hfst)
  have ht : ComputableTidilyInPolyTime (fun p : CNF ℕ × ℕ => 2 ^ leaves p.1)
      (encPair encCNF encNat) encNat :=
    ComputableTidilyInPolyTime.binary_two_pow.comp (leaves_polyTime.comp hfst)
  have hx : ComputableTidilyInPolyTime (fun p : CNF ℕ × ℕ => p.2) (encPair encCNF encNat)
      encNat := by fun_prop
  exact .of_tidy (ComputableTidilyInPolyTime.binary_mod'
    (ComputableTidilyInPolyTime.binary_div' (ComputableTidilyInPolyTime.binary_mul' hx hK) hN) ht)

end PolyTime

end Latc.PaperD.Valiant
