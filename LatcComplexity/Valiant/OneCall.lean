import LatcComplexity.Valiant.Pendant
import LatcComplexity.Binary
import Complexity.Logics.Propositional.CNF.Occurrence

/-!
# Valiant's theorem in its one-call form

`#Monotone-2SAT` is one-call `#P`-hard (`sharpMonotone2SAT_oneCallSharpPHard`), so the hypothesis
`hValiant` of `countValidMonotone2_oneCallSharpPComplete(_bin)` holds and the monotone case of
Proposition 5 is unconditional (`countValidMonotone2_sharpPComplete_oneCall`).

The reduction from `#SAT` makes one oracle call: `toMonotone φ` is the monotone formula of the
conflict graph of `φ` with `t = n + 1` pendant leaves per vertex (`LatcComplexity/Valiant/Gadget.lean`).
Its model count is `Σ_S 2^(t (N − |S|))` over the independent sets `S` of the conflict graph
(`modelCount_psi`), every independent set has at most `K = n + m` vertices (`card_le_of_indep`),
and those with `K` vertices are as many as the models of `φ` (`modelCount_eq_card`), fewer than
`2^t`. So `#SAT φ` is the digit of rank `N − K` in base `2^t` of the oracle answer, read by
`post` (`digit`).
-/

namespace Latc.PaperD.Valiant

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM Latc.PaperD.General

/-! ### The digit -/

/-- Reading the digit: a sum of powers `2^(t (N − sᵢ))` with `sᵢ ≤ K`, `sᵢ ≤ N`, and fewer than
`2^t` indices with `sᵢ = K`, has that number as its digit of rank `N − K` in base `2^t`. -/
theorem digit {ι : Type*} (s : Finset ι) (P : ι → Prop) [DecidablePred P] (sz : ι → ℕ)
    {t K N : ℕ} (ht : 0 < t) (hK : ∀ i ∈ s, P i → sz i ≤ K) (hN : ∀ i ∈ s, sz i ≤ N)
    (ha : (s.filter fun i => P i ∧ sz i = K).card < 2 ^ t) :
    (∑ i ∈ s, if P i then 2 ^ (t * (N - sz i)) else 0) * 2 ^ (t * K) / 2 ^ (t * N) % 2 ^ t =
      (s.filter fun i => P i ∧ sz i = K).card := by
  have e : (∑ i ∈ s, if P i then 2 ^ (t * (N - sz i)) else 0) * 2 ^ (t * K) =
      2 ^ (t * N) * ∑ i ∈ s, if P i then 2 ^ (t * (K - sz i)) else 0 := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases hP : P i
    · simp only [hP, ↓reduceIte, ← pow_add, ← mul_add]
      have h1 := hK i hi hP
      have h2 := hN i hi
      congr 2
      omega
    · simp [hP]
  rw [e, Nat.mul_div_cancel_left _ (by positivity), Finset.sum_nat_mod]
  have h1 : ∀ i ∈ s, (if P i then 2 ^ (t * (K - sz i)) else 0) % 2 ^ t =
      if P i ∧ sz i = K then 1 else 0 := by
    intro i hi
    by_cases hP : P i
    · by_cases hs : sz i = K
      · simp only [hP, hs, ↓reduceIte, and_self, Nat.sub_self, mul_zero, pow_zero]
        exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow ht.ne')
      · simp only [hP, ↓reduceIte, hs, and_false]
        have hlt : sz i < K := lt_of_le_of_ne (hK i hi hP) hs
        apply Nat.mod_eq_zero_of_dvd
        apply Nat.pow_dvd_pow
        exact Nat.le_mul_of_pos_right t (by omega)
    · simp [hP]
  rw [Finset.sum_congr rfl h1, Finset.sum_boole, Nat.cast_id]
  exact Nat.mod_eq_of_lt ha

/-! ### Dense formulas -/

variable {φ : CNF ℕ} {n : ℕ}

theorem verts_toFinset :
    (verts φ n).toFinset = ((Finset.range n ×ˢ (Finset.univ : Finset Bool)).image
      fun p => vv p.1 p.2) ∪ (occurrences φ).toFinset.image cv := by
  ext x
  rw [List.mem_toFinset, mem_verts, Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro (⟨i, hi, b, rfl⟩ | ⟨o, ho, rfl⟩)
    · exact Or.inl ⟨(i, b), Finset.mem_product.2 ⟨Finset.mem_range.2 hi, Finset.mem_univ _⟩, rfl⟩
    · exact Or.inr ⟨o, List.mem_toFinset.2 ho, rfl⟩
  · rintro (⟨⟨i, b⟩, hp, rfl⟩ | ⟨o, ho, rfl⟩)
    · exact Or.inl ⟨i, Finset.mem_range.1 (Finset.mem_product.1 hp).1, b, rfl⟩
    · exact Or.inr ⟨o, List.mem_toFinset.1 ho, rfl⟩

/-- The conflict graph has `2n` variable vertices and one vertex per literal occurrence. -/
theorem card_V0 : Fintype.card (V0 φ n) = 2 * n + φ.vars.length := by
  rw [Fintype.card_coe, verts_toFinset, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ (fun p q h => Prod.ext (vv_inj.1 h).1 (vv_inj.1 h).2),
      Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_bool,
      Finset.card_image_of_injOn (fun o ho o' ho' h => (cv_inj (List.mem_toFinset.1 ho)
        (List.mem_toFinset.1 ho')).1 h), List.toFinset_card_of_nodup (occurrences_nodup φ),
      length_occurrences]
    ring
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_image] at hx hx'
    obtain ⟨p, -, rfl⟩ := hx
    obtain ⟨o, -, h⟩ := hx'
    exact vv_ne_cv _ _ _ h.symm

theorem card_falseSet (g : V0 φ n → Bool) :
    (falseSet g).card = (Finset.univ.filter fun x => g x = false).card := by
  simp [falseSet]

theorem card_true (g : V0 φ n → Bool) : (Finset.univ.filter fun x => g x = true).card =
    Fintype.card (V0 φ n) - (falseSet g).card := by
  rw [card_falseSet, ← Finset.card_univ,
    ← Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun x => g x = true)]
  simp

/-- At most `2^(numVars)` models. -/
theorem modelCount_le (ψ : CNF ℕ) : ψ.modelCount ≤ 2 ^ ψ.numVars := by
  unfold CNF.modelCount
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  rfl

/-- **The digit identity for dense formulas.** -/
theorem modelCount_eq_post (hd : ∀ o ∈ occurrences φ, o.2.2.1 < n) (hn : ∀ i < n, i ∈ φ.vars)
    (hc : φ.modelCount < 2 ^ (n + 1)) :
    φ.modelCount = (psi φ n).modelCount * 2 ^ ((n + 1) * (n + φ.length)) /
      2 ^ ((n + 1) * (2 * n + φ.vars.length)) % 2 ^ (n + 1) := by
  classical
  unfold psi
  rw [modelCount_psi hd (Nat.succ_pos n), ← card_V0]
  simp_rw [card_true]
  rw [digit Finset.univ (fun g => Indep φ n (falseSet g)) (fun g => (falseSet g).card)
    (Nat.succ_pos n) (fun g _ hI => card_le_of_indep (falseSet_subset g) hI)
    (fun g _ => by rw [card_falseSet]; exact Finset.card_le_univ _)
    (by rw [← modelCount_eq_card hd hn]; exact hc)]
  exact modelCount_eq_card hd hn

/-! ### The reduction -/

theorem monotone2B_psi (φ : CNF ℕ) (n : ℕ) : monotone2B (psi φ n) = true := by
  have hedge : ∀ a b, (edge a b).length == 2 && (edge a b).all (·.2) := fun _ _ => rfl
  simp only [monotone2B, List.all_eq_true]
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · rcases mem_graphClauses.1 hc with ⟨i, -, rfl⟩ | ⟨o, -, rfl | ⟨o', -, -, -, rfl | rfl⟩⟩ <;>
      exact hedge _ _
  · obtain ⟨u, -, q, -, rfl⟩ := mem_leafClauses.1 hc
    exact hedge _ _

/-- **`#SAT` is the digit of the one oracle answer.** -/
theorem sharpSAT_eq_post (φ : CNF ℕ) : SharpSAT φ = post φ (SharpMonotone2SAT (toMonotone φ)) := by
  set ψ := φ.denseRelabel
  have hvars : ∀ v, v ∈ ψ.vars ↔ v < φ.numVars := by
    intro v
    rw [← List.mem_toFinset, CNF.vars_denseRelabel_toFinset, Finset.mem_range]
  have hd : ∀ o ∈ occurrences ψ, o.2.2.1 < φ.numVars := by
    intro o ho
    refine (hvars _).1 ?_
    rw [← map_occurrences]
    exact List.mem_map.2 ⟨o, ho, rfl⟩
  have hc : ψ.modelCount < 2 ^ (φ.numVars + 1) := by
    refine (modelCount_le ψ).trans_lt ?_
    rw [CNF.numVars_denseRelabel]
    exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
  have hlen : ψ.vars.length = φ.vars.length := by
    simp [ψ, CNF.denseRelabel, CNF.vars_relabel]
  have hm : ψ.length = φ.length := CNF.length_denseRelabel φ
  unfold SharpSAT SharpMonotone2SAT toMonotone
  simp only [monotone2B_psi, ↓reduceIte]
  rw [SharpSAT, ← CNF.modelCount_denseRelabel,
    modelCount_eq_post hd (fun i hi => (hvars i).2 hi) hc]
  unfold post leaves maxSize numVerts
  rw [hlen, hm]

/-- **`#SAT` reduces to `#Monotone-2SAT` with one oracle call.** -/
theorem sharpSAT_oneCallReducible :
    OneCallReducible encCNF encCNF SharpSAT SharpMonotone2SAT :=
  ⟨toMonotone, post, toMonotone_polyTime, post_polyTime, sharpSAT_eq_post⟩

/-- A parsimonious reduction followed by a one-call reduction is a one-call reduction. -/
theorem ParsimoniousReducible.trans_oneCall {α β γ : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {f : α → ℕ} {g : β → ℕ} {h : γ → ℕ}
    (hfg : ParsimoniousReducible encA encB f g) (hgh : OneCallReducible encB encC g h) :
    OneCallReducible encA encC f h := by
  obtain ⟨s, hs, hf⟩ := hfg
  obtain ⟨r, post, hr, hpost, hg⟩ := hgh
  have hs' := hs.tidy
  have hp : ComputableTidilyInPolyTime (fun p : α × ℕ => (s p.1, p.2)) (encPair encA encNat)
      (encPair encB encNat) := by fun_prop
  exact ⟨r ∘ s, fun a x => post (s a) x, hr.comp hs, .of_tidy (hpost.tidy.comp hp),
    fun a => (hf a).trans (hg (s a))⟩

/-- **Valiant's theorem, one-call form, in Complexitylib's model:** `#Monotone-2SAT` is one-call
`#P`-hard. -/
theorem sharpMonotone2SAT_oneCallSharpPHard : OneCallSharpPHard encCNF SharpMonotone2SAT :=
  fun _ enc f hf => ParsimoniousReducible.trans_oneCall (CookLevin.SharpSAT_sharpPHard enc f hf)
    sharpSAT_oneCallReducible

/-- **Proposition 5, monotone two-literal case, unconditional:** counting |𝒱| for clauses of two
conditions Aᵢ = 1, Aⱼ = 1 over domains {0, 1} is one-call `#P`-complete, attribute indices in
binary. -/
theorem countValidMonotone2_sharpPComplete_oneCall :
    OneCallSharpPComplete encInstBin countValidMonotone2 :=
  countValidMonotone2_oneCallSharpPComplete_bin sharpMonotone2SAT_oneCallSharpPHard

/-- The same, attribute indices in unary (`encInst`). -/
theorem countValidMonotone2_sharpPComplete_oneCall_unary :
    OneCallSharpPComplete General.encInst countValidMonotone2 :=
  countValidMonotone2_oneCallSharpPComplete sharpMonotone2SAT_oneCallSharpPHard

end Latc.PaperD.Valiant
