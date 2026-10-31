import LatcComplexity.Tractable

/-!
# An explicit degree in the number of attributes

`Tractable` proves, for each fixed `k`, that M(T₀) ≠ ∅, completeness and |M(T₀)| are
polynomial-time on instances with at most `k` attributes, with a polynomial that depends on `k` in
an unspecified way. Here the bounds are explicit and uniform in `k`: one machine, for all
instances, runs within time and space `c · (|x| + 1) ^ (d · n + d)`, `n` the number of attributes
and `|x|` the length of the binary encoding `encInstBin`, for constants `c` and `d`.

* `missingNonempty_explicitDegree`, `complete_explicitDegree`, `missingCount_explicitDegree`: one
  machine each, for every instance.
* `missingNonemptyFixedAttrs_uniform`, `completeFixedAttrs_uniform`,
  `missingCountFixedAttrs_uniform`: `∃ c d₀ d₁, ∀ k`, the bound `c · (|x| + 1) ^ (d₀ · k + d₁)` on
  the instances with at most `k` attributes.
* `missingNonemptyWithBound_explicitDegree`, `completeWithBound_explicitDegree`,
  `missingCountWithBound_explicitDegree`: the fixed-`k` procedures of `Tractable` on every
  instance, rejecting (or answering 0) when there are more than `k` attributes, as one machine
  that reads `k` in unary from its input, within `c · (|(k, x)| + 1) ^ (d · k + d)`.

The method: Complexitylib's `ComputableTidilyInO` keeps explicit bound functions with one
existential constant through composition, case distinctions and left folds. All sections of `n`
lists (`allSections`) are computed by a left fold whose states are at most `(|L| + 1) ^ n` partial
sections (`length_state_le`), within `O((|L| + 1) ^ (D · (n + 1)))` (`allSections_inO`). The
procedures are a polynomial-time list of candidate (or class) values per attribute, all its
sections, and a polynomial-time test (`pipeline_inO`). Constants are absorbed into the exponent
because `|x| ≥ 1` (`mul_pow_le_pow_add`, `XPBounded`).
-/

namespace Latc.PaperD.General

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Bounds of the form `c · (size + 1) ^ (e · (n + 1))` -/

/-- `T` is bounded by `c · (size + 1) ^ (e · (n + 1))` for some constants `c` and `e`. -/
def XPBounded {α : Type} (size n T : α → ℕ) : Prop :=
  ∃ c e, ∀ a, T a ≤ c * (size a + 1) ^ (e * (n a + 1))

/-- A constant factor is absorbed into the exponent when the base is at least 2. -/
lemma mul_pow_le_pow_add {X : ℕ} (hX : 2 ≤ X) (c m : ℕ) : c * X ^ m ≤ X ^ (m + c) := by
  have h1 : c ≤ X ^ c := (Nat.lt_two_pow_self (n := c)).le.trans (Nat.pow_le_pow_left hX c)
  calc c * X ^ m ≤ X ^ c * X ^ m := Nat.mul_le_mul_right _ h1
    _ = X ^ (m + c) := by rw [← pow_add, Nat.add_comm]

namespace XPBounded

variable {α : Type} {size n T U : α → ℕ}

lemma of_le (h : XPBounded size n U) (hle : ∀ a, T a ≤ U a) : XPBounded size n T :=
  let ⟨c, e, h⟩ := h
  ⟨c, e, fun a => (hle a).trans (h a)⟩

lemma mono_exp {c e e' : ℕ} (hee : e ≤ e') (a : α) (hT : T a ≤ c * (size a + 1) ^ (e * (n a + 1))) :
    T a ≤ c * (size a + 1) ^ (e' * (n a + 1)) :=
  hT.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _)
    (Nat.mul_le_mul_right _ hee)))

lemma add (hT : XPBounded size n T) (hU : XPBounded size n U) :
    XPBounded size n fun a => T a + U a := by
  obtain ⟨c₁, e₁, h₁⟩ := hT
  obtain ⟨c₂, e₂, h₂⟩ := hU
  refine ⟨c₁ + c₂, max e₁ e₂, fun a => ?_⟩
  have k₁ := mono_exp (le_max_left e₁ e₂) a (h₁ a)
  have k₂ := mono_exp (le_max_right e₁ e₂) a (h₂ a)
  rw [Nat.add_mul]
  exact Nat.add_le_add k₁ k₂

lemma const (k : ℕ) : XPBounded size n fun _ => k :=
  ⟨k, 0, fun a => by simp⟩

/-- A polynomial in the size, of fixed degree. -/
lemma of_poly (c d : ℕ) (h : ∀ a, T a ≤ c * (size a + 1) ^ d) : XPBounded size n T :=
  ⟨c, d, fun a => (h a).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _)
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))))⟩

lemma const_mul (hT : XPBounded size n T) (k : ℕ) : XPBounded size n fun a => k * T a :=
  let ⟨c, e, h⟩ := hT
  ⟨k * c, e, fun a => by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (h a)⟩

lemma size_self : XPBounded size n size :=
  of_poly 1 1 fun a => by simp

/-- Raising to a fixed power, when the size is positive. -/
lemma pow (hs : ∀ a, 1 ≤ size a) (hT : XPBounded size n T) (d : ℕ) :
    XPBounded size n fun a => (T a + 1) ^ d := by
  obtain ⟨c, e, h⟩ := hT
  refine ⟨1, (e + c + 1) * d, fun a => ?_⟩
  have hX : 2 ≤ size a + 1 := by have := hs a; omega
  have h1 : T a + 1 ≤ (size a + 1) ^ (e * (n a + 1) + (c + 1)) := by
    have := mul_pow_le_pow_add hX (c + 1) (e * (n a + 1))
    have h2 : 1 ≤ (size a + 1) ^ (e * (n a + 1)) := Nat.one_le_pow _ _ (Nat.succ_pos _)
    nlinarith [h a]
  rw [one_mul]
  calc (T a + 1) ^ d ≤ ((size a + 1) ^ (e * (n a + 1) + (c + 1))) ^ d := Nat.pow_le_pow_left h1 d
    _ = (size a + 1) ^ ((e * (n a + 1) + (c + 1)) * d) := by rw [← pow_mul]
    _ ≤ (size a + 1) ^ ((e + c + 1) * d * (n a + 1)) := by
      refine Nat.pow_le_pow_right (Nat.succ_pos _) ?_
      have : e * (n a + 1) + (c + 1) ≤ (e + c + 1) * (n a + 1) := by nlinarith
      calc (e * (n a + 1) + (c + 1)) * d ≤ (e + c + 1) * (n a + 1) * d :=
            Nat.mul_le_mul_right _ this
        _ = (e + c + 1) * d * (n a + 1) := by ring

/-- A power with exponent linear in `n`, of a polynomially bounded quantity. -/
lemma pow_mul_succ (hs : ∀ a, 1 ≤ size a) {c m : ℕ} (hU : ∀ a, U a ≤ c * (size a + 1) ^ m)
    (D : ℕ) : XPBounded size n fun a => (U a + 1) ^ (D * (n a + 1)) := by
  refine ⟨1, (m + c + 1) * D, fun a => ?_⟩
  have hX : 2 ≤ size a + 1 := by have := hs a; omega
  have h1 : U a + 1 ≤ (size a + 1) ^ (m + (c + 1)) := by
    have := mul_pow_le_pow_add hX (c + 1) m
    have h2 : 1 ≤ (size a + 1) ^ m := Nat.one_le_pow _ _ (Nat.succ_pos _)
    nlinarith [hU a]
  rw [one_mul]
  calc (U a + 1) ^ (D * (n a + 1)) ≤ ((size a + 1) ^ (m + (c + 1))) ^ (D * (n a + 1)) :=
        Nat.pow_le_pow_left h1 _
    _ = (size a + 1) ^ ((m + c + 1) * D * (n a + 1)) := by rw [← pow_mul]; ring_nf

end XPBounded

/-- Explicit bounds from bounds up to a constant factor. -/
theorem timeAndSpace_of_inO_xp {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} {T S n : α → ℕ} (h : ComputableTidilyInO f encIn encOut T S)
    (hT : XPBounded (fun a => (encIn a).length) n T)
    (hS : XPBounded (fun a => (encIn a).length) n S) :
    ∃ c d, ComputableTidilyInTimeAndSpace f encIn encOut
      (fun a => c * ((encIn a).length + 1) ^ (d * n a + d))
      (fun a => c * ((encIn a).length + 1) ^ (d * n a + d)) := by
  obtain ⟨k, hk, -⟩ := h
  obtain ⟨c, d, hTS⟩ := (hT.add hS).add (XPBounded.const 1)
  have key : ∀ a, T a + S a + 1 ≤ c * ((encIn a).length + 1) ^ (d * n a + d) := fun a => by
    have := hTS a
    simp only at this
    rwa [Nat.mul_add, Nat.mul_one] at this
  refine ⟨k * c, d, hk.mono (fun a => ?_) (fun a => ?_)⟩
  · rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ ((show T a + 1 ≤ T a + S a + 1 by omega).trans (key a))
  · rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ ((show S a + 1 ≤ T a + S a + 1 by omega).trans (key a))

/-- Polynomial time gives explicit bounds of some degree, up to a constant factor. -/
theorem inO_pow_of_polyTime {α β : Type} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} (h : ComputableTidilyInPolyTime f encIn encOut) :
    ∃ d, ComputableTidilyInO f encIn encOut (fun a => ((encIn a).length + 1) ^ d)
      (fun a => ((encIn a).length + 1) ^ d) := by
  obtain ⟨t, s, ht, hs, hf⟩ := h
  obtain ⟨c₁, d₁, h₁⟩ := ht.exists_le
  obtain ⟨c₂, d₂, h₂⟩ := hs.exists_le
  refine ⟨max d₁ d₂, .of_bounds hf (c₁ + c₂) (fun a => ?_) (fun a => ?_) (fun a => ?_)⟩
  all_goals
    have e₁ : c₁ * ((encIn a).length + 1) ^ d₁ ≤
        (c₁ + c₂) * (((encIn a).length + 1) ^ max d₁ d₂ + 1) :=
      Nat.mul_le_mul (by omega) ((Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)).trans
        (Nat.le_succ _))
    have e₂ : c₂ * ((encIn a).length + 1) ^ d₂ ≤
        (c₁ + c₂) * (((encIn a).length + 1) ^ max d₁ d₂ + 1) :=
      Nat.mul_le_mul (by omega) ((Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right _ _)).trans
        (Nat.le_succ _))
  · exact (h₁ a).trans e₁
  · exact (h₂ a).trans e₂
  · exact ((hf.length_le a).trans (h₁ a)).trans e₁

/-! ### All sections, by a left fold with explicit bounds -/

/-- One round: prepend each value of `l` to each partial section. -/
def secStep (acc : List (List ℕ)) (l : List ℕ) : List (List ℕ) :=
  l.flatMap fun a => acc.map (a :: ·)

/-- All choices of one element from each list (every list, however many). -/
def allSections (L : List (List ℕ)) : List (List ℕ) := L.reverse.foldl secStep [[]]

lemma allSections_eq (L : List (List ℕ)) : allSections L = boundedSections L.length L := by
  rw [allSections, List.foldl_reverse]
  induction L with
  | nil => rfl
  | cons l L ih =>
    rw [List.foldr_cons, ih, List.length_cons, boundedSections_cons]
    rfl

/-- The invariant of the fold: few partial sections, short, with small entries. -/
lemma foldl_secStep_invariant {Λ : ℕ} (P : List (List ℕ))
    (hP : ∀ l ∈ P, l.length ≤ Λ ∧ ∀ v ∈ l, (encNat v).length ≤ Λ) (acc : List (List ℕ)) (j : ℕ)
    (hacc : acc.length ≤ (Λ + 1) ^ j ∧
      ∀ s ∈ acc, s.length ≤ j ∧ ∀ v ∈ s, (encNat v).length ≤ Λ) :
    (P.foldl secStep acc).length ≤ (Λ + 1) ^ (j + P.length) ∧
      ∀ s ∈ P.foldl secStep acc, s.length ≤ j + P.length ∧ ∀ v ∈ s, (encNat v).length ≤ Λ := by
  induction P generalizing acc j with
  | nil => simpa using hacc
  | cons l P ih =>
    rw [List.foldl_cons, List.length_cons, show j + (P.length + 1) = (j + 1) + P.length by omega]
    refine ih (fun l' hl' => hP l' (List.mem_cons_of_mem _ hl')) _ _ ⟨?_, ?_⟩
    · have hl := (hP l List.mem_cons_self).1
      simp only [secStep, List.length_flatMap, List.length_map, List.map_const', List.sum_replicate,
        smul_eq_mul, pow_succ]
      calc l.length * acc.length ≤ (Λ + 1) * (Λ + 1) ^ j :=
            Nat.mul_le_mul (by omega) hacc.1
        _ = (Λ + 1) ^ j * (Λ + 1) := Nat.mul_comm _ _
    · intro s hs
      simp only [secStep, List.mem_flatMap, List.mem_map] at hs
      obtain ⟨a, ha, t, ht, rfl⟩ := hs
      obtain ⟨h1, h2⟩ := hacc.2 t ht
      refine ⟨by simp; omega, fun v hv => ?_⟩
      rcases List.mem_cons.1 hv with rfl | hv
      · exact (hP l List.mem_cons_self).2 v ha
      · exact h2 v hv

/-- The encoding of a list of lists of numbers. -/
abbrev encLL : List (List ℕ) ↪ List Bool := encList (encList encNat)

lemma length_encList_reverse {α : Type} (enc : α ↪ List Bool) (l : List α) :
    (encList enc l.reverse).length = (encList enc l).length := by
  show (l.reverse.flatMap (frame ∘ enc)).length = (l.flatMap (frame ∘ enc)).length
  simp [List.length_flatMap, List.map_reverse, List.sum_reverse]

/-- Every round state of the fold, and every list folded over, is small. -/
lemma length_state_le (L : List (List ℕ)) (i : ℕ) (hi : i ≤ L.length) :
    (encLL ((L.reverse.take i).foldl secStep [[]])).length ≤
      4 * ((encLL L).length + 1) ^ (L.length + 2) := by
  set Λ := (encLL L).length
  have hP : ∀ l ∈ L.reverse.take i, l.length ≤ Λ ∧ ∀ v ∈ l, (encNat v).length ≤ Λ := by
    intro l hl
    have hl : l ∈ L := List.mem_reverse.1 (List.mem_of_mem_take hl)
    have h1 := SizedListEncoding.length_elem_le (encA := encList encNat) (encL := encLL) L l hl
    refine ⟨(SizedListEncoding.length_le (encA := encNat) (encL := encList encNat) l).trans h1,
      fun v hv => ?_⟩
    exact (SizedListEncoding.length_elem_le (encA := encNat) (encL := encList encNat) l v hv).trans
      h1
  have hinv := foldl_secStep_invariant (Λ := Λ) _ hP [[]] 0 ⟨by simp, by simp⟩
  have hlen : (L.reverse.take i).length = i := by simp; omega
  rw [hlen, Nat.zero_add] at hinv
  have hn : L.length ≤ Λ := SizedListEncoding.length_le (encA := encList encNat) (encL := encLL) L
  have hs : ∀ s ∈ (L.reverse.take i).foldl secStep [[]],
      (encList encNat s).length ≤ Λ * (2 * Λ + 1) :=
    fun s hs => (length_encList_le encNat s (hinv.2 s hs).2).trans
      (Nat.mul_le_mul_right _ (((hinv.2 s hs).1.trans hi).trans hn))
  refine (length_encList_le (encList encNat) _ hs).trans ?_
  have hc : ((L.reverse.take i).foldl secStep [[]]).length ≤ (Λ + 1) ^ L.length :=
    hinv.1.trans (Nat.pow_le_pow_right (Nat.succ_pos _) hi)
  calc ((L.reverse.take i).foldl secStep [[]]).length * (2 * (Λ * (2 * Λ + 1)) + 1)
      ≤ (Λ + 1) ^ L.length * (4 * (Λ + 1) ^ 2) := Nat.mul_le_mul hc (by nlinarith)
    _ = 4 * (Λ + 1) ^ (L.length + 2) := by ring

theorem secStep_polyTime :
    ComputableTidilyInPolyTime (fun p : List (List ℕ) × List ℕ => secStep p.1 p.2)
    (encPair encLL (encList encNat)) encLL := by
  have hb : ComputableTidilyInPolyTime
      (fun q : (List (List ℕ) × List ℕ) × ℕ => q.1.1.map (q.2 :: ·))
      (encPair (encPair encLL (encList encNat)) encNat) encLL := by
    fun_prop
  exact ComputableTidilyInPolyTime.flatMapWithInput (by fun_prop) hb

theorem reverse_polyTime : ComputableTidilyInPolyTime (fun L : List (List ℕ) => L.reverse)
    encLL encLL := by
  fun_prop

lemma fold_bound_arith (Λ n dl ds R B : ℕ) (hn : n ≤ Λ)
    (hR : R ≤ (10 * (Λ + 1) ^ (n + 2)) ^ ds) (hB : B = 4 * (Λ + 1) ^ (n + 2)) :
    (Λ + 1) ^ dl + Λ + (n + 1) * (R + B + Λ) ≤
        (10 ^ ds + 7) * ((Λ + 1) ^ ((dl + 3 * ds + 3) * (n + 1)) + 1) ∧
      (Λ + 1) ^ dl + Λ + R + B + Λ ≤
        (10 ^ ds + 7) * ((Λ + 1) ^ ((dl + 3 * ds + 3) * (n + 1)) + 1) := by
  have hpow : ∀ m, m ≤ (dl + 3 * ds + 3) * (n + 1) →
      (Λ + 1) ^ m ≤ (Λ + 1) ^ ((dl + 3 * ds + 3) * (n + 1)) :=
    fun m hm => Nat.pow_le_pow_right (Nat.succ_pos _) hm
  have hR' : R ≤ 10 ^ ds * (Λ + 1) ^ ((n + 2) * ds) := by rwa [mul_pow, ← pow_mul] at hR
  have hnR : (n + 1) * R ≤ 10 ^ ds * (Λ + 1) ^ ((dl + 3 * ds + 3) * (n + 1)) := by
    calc (n + 1) * R ≤ (Λ + 1) * (10 ^ ds * (Λ + 1) ^ ((n + 2) * ds)) :=
          Nat.mul_le_mul (by omega) hR'
      _ = 10 ^ ds * (Λ + 1) ^ ((n + 2) * ds + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (hpow _ (by nlinarith))
  have hnB : (n + 1) * B ≤ 4 * (Λ + 1) ^ ((dl + 3 * ds + 3) * (n + 1)) := by
    calc (n + 1) * B ≤ (Λ + 1) * (4 * (Λ + 1) ^ (n + 2)) := Nat.mul_le_mul (by omega) hB.le
      _ = 4 * (Λ + 1) ^ (n + 3) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (hpow _ (by nlinarith))
  have hnL : (n + 1) * Λ ≤ (Λ + 1) ^ ((dl + 3 * ds + 3) * (n + 1)) := by
    calc (n + 1) * Λ ≤ (Λ + 1) ^ 2 := by nlinarith
      _ ≤ _ := hpow _ (by nlinarith)
  have hdl := hpow dl (by nlinarith)
  have hΛ : Λ + 1 ≤ (Λ + 1) ^ ((dl + 3 * ds + 3) * (n + 1)) :=
    (Nat.pow_one _).symm.le.trans (hpow _ (by nlinarith))
  have hR1 : R ≤ (n + 1) * R := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hB1 : B ≤ (n + 1) * B := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  generalize (Λ + 1) ^ ((dl + 3 * ds + 3) * (n + 1)) = P at *
  generalize 10 ^ ds = K at *
  have e : (K + 7) * (P + 1) = K * P + 7 * P + K + 7 := by ring
  rw [e, Nat.mul_add, Nat.mul_add]
  omega

/-- **All sections within explicit bounds:** time and space `O((|L| + 1) ^ (D · (n + 1)))` for
`n` lists, `|L|` the length of their encoding, for one constant `D`. -/
theorem allSections_inO : ∃ D, ComputableTidilyInO allSections encLL encLL
    (fun L => ((encLL L).length + 1) ^ (D * (L.length + 1)))
    (fun L => ((encLL L).length + 1) ^ (D * (L.length + 1))) := by
  obtain ⟨dl, hl⟩ := inO_pow_of_polyTime reverse_polyTime
  obtain ⟨ds, hs⟩ := inO_pow_of_polyTime secStep_polyTime
  have hi := ComputableTidilyInO.const (encIn := encLL) (encMid := encLL) [[]]
  let B : List (List ℕ) → ℕ := fun L => 4 * ((encLL L).length + 1) ^ (L.length + 2)
  let R : List (List ℕ) → ℕ := fun L => (2 * B L + 1 + (encLL L).length + 1) ^ ds
  have hround : ∀ (L : List (List ℕ)) i (hi : i < L.reverse.length),
      ((encPair encLL (encList encNat)
        ((L.reverse.take i).foldl secStep [[]], L.reverse[i])).length + 1) ^ ds ≤ R L := by
    intro L i hi
    refine Nat.pow_le_pow_left ?_ ds
    have h1 := length_state_le L i (by simp at hi; omega)
    have h2 : (encList encNat L.reverse[i]).length ≤ (encLL L).length :=
      SizedListEncoding.length_elem_le (encA := encList encNat) (encL := encLL) L _
        (List.mem_reverse.1 (List.getElem_mem hi))
    rw [length_encPair]
    simp only [B]
    omega
  have hf := ComputableTidilyInO.foldl (encA := encList encNat) (encL := encLL) (encB := encLL)
    (list := fun L : List (List ℕ) => L.reverse) (init := fun _ => [[]]) (step := secStep)
    hl hi hs (R := R) (Q := R) (B := B) hround hround
    (fun L i hi => length_state_le L i (by simpa using hi))
  refine ⟨dl + 3 * ds + 3, (hf.mono (10 ^ ds + 7) (fun L => ?_) (fun L => ?_))⟩
  all_goals
    have hn : L.length ≤ (encLL L).length :=
      SizedListEncoding.length_le (encA := encList encNat) (encL := encLL) L
    have hrev : (encLL L.reverse).length = (encLL L).length := length_encList_reverse _ L
    have hb := fold_bound_arith ((encLL L).length) L.length dl ds (R L) (B L) hn
      (Nat.pow_le_pow_left (by
        have : (encLL L).length + 1 ≤ ((encLL L).length + 1) ^ (L.length + 2) :=
          Nat.le_self_pow (by omega) _
        simp only [B]
        omega) ds) rfl
  · show _ + _ + (L.reverse.length + 1) * (R L + B L + (encLL L.reverse).length) ≤ _
    rw [hrev, List.length_reverse]
    exact hb.1
  · show _ + _ + R L + B L + (encLL L.reverse).length ≤ _
    rw [hrev]
    exact hb.2

/-! ### The pipeline: list of lists, all its sections, a polynomial-time test -/

/-- The size of an instance. -/
abbrev instSize (I : Inst) : ℕ := (encInstBin I).length

lemma one_le_instSize (I : Inst) : 1 ≤ instSize I := by
  simp only [instSize, length_encPair]
  omega

/-- **The pipeline within explicit bounds.** If `lists` is polynomial-time with one list per
attribute and `test` is polynomial-time, then `I ↦ test (I, allSections (lists I))` is computable
within time and space `O((|x| + 1) ^ (e · (n + 1)))`, for constants `e`. -/
theorem pipeline_inO {β : Type} {encOut : β ↪ List Bool} {lists : Inst → List (List ℕ)}
    {test : Inst × List (List ℕ) → β}
    (hlists : ComputableTidilyInPolyTime lists encInstBin encLL)
    (hlen : ∀ I, (lists I).length = I.n)
    (htest : ComputableTidilyInPolyTime test (encPair encInstBin encLL) encOut) :
    ∃ T S, ComputableTidilyInO (fun I => test (I, allSections (lists I))) encInstBin encOut T S ∧
      XPBounded instSize Inst.n T ∧ XPBounded instSize Inst.n S := by
  obtain ⟨dc, hc⟩ := inO_pow_of_polyTime hlists
  obtain ⟨cc, hcl⟩ := hc.length_le
  obtain ⟨D, hs⟩ := allSections_inO
  obtain ⟨dh, hh⟩ := inO_pow_of_polyTime htest
  have h1 := hs.comp hc
  obtain ⟨c1, hl1⟩ := h1.length_le
  have hid : ComputableTidilyInO (fun I : Inst => I) encInstBin encInstBin
      (fun I => (encInstBin I).length) (fun I => (encInstBin I).length) :=
    .of_linear (.of_eq fun _ => rfl)
  have h2 := hid.prod h1
  have h3 := hh.comp h2
  have hpos := one_le_instSize
  -- the bound of the sections, in the size of the instance
  have hU : ∀ I, (encLL (lists I)).length ≤ (2 * cc) * (instSize I + 1) ^ dc := by
    intro I
    have := hcl I
    have : 1 ≤ (instSize I + 1) ^ dc := Nat.one_le_pow _ _ (Nat.succ_pos _)
    simp only [instSize] at *
    nlinarith
  have hsec : XPBounded instSize Inst.n fun I =>
      ((encLL (lists I)).length + 1) ^ (D * ((lists I).length + 1)) := by
    simp only [hlen]
    exact XPBounded.pow_mul_succ hpos hU D
  have hT1 : XPBounded instSize Inst.n fun I => (instSize I + 1) ^ dc +
      ((encLL (lists I)).length + 1) ^ (D * ((lists I).length + 1)) :=
    (XPBounded.of_poly 1 dc fun I => by simp).add hsec
  have hpair : XPBounded instSize Inst.n fun I =>
      (encPair encInstBin encLL (I, allSections (lists I))).length := by
    refine ((XPBounded.size_self.const_mul 2).add (((hT1.add (.const 1)).const_mul c1).add
      (.const 1))).of_le fun I => ?_
    have := hl1 I
    simp only [length_encPair, Function.comp_apply, instSize] at this ⊢
    omega
  refine ⟨_, _, h3, ?_, ?_⟩
  · exact (XPBounded.size_self.add hT1).add (hpair.pow hpos dh)
  · exact (XPBounded.size_self.add hT1).add (hpair.pow hpos dh)

/-! ### The decision procedure and the counter, for all instances at once -/

theorem candLists_polyTime : ComputableTidilyInPolyTime candLists encInstBin encLL := by
  have hp := candPool_polyTime
  have hf : ComputableTidilyInPolyTime
      (fun p : Inst × ℕ => (candPool p.1).filter fun v => decide (v < p.2))
      (encPair encInstBin encNat) (encList encNat) :=
    ComputableTidilyInPolyTime.filterWithInput (hp.comp (by fun_prop)) (by fun_prop)
  have h := ComputableTidilyInPolyTime.mapWithInput (encIn := encInstBin)
    (list := fun I : Inst => I.1) (f := fun I di => (candPool I).filter fun v => decide (v < di))
    (ComputableTidilyInPolyTime.fst (encList encNat)
      (encPair (encList (encList (encPair encNat encNat))) (encList (encList encNat)))) hf
  simpa only [← candLists_eq] using h

/-- The test of the decision procedure: some section is a missing state. -/
def anyCheck (p : Inst × List (List ℕ)) : Bool := p.2.any fun s => check (p.1, s)

theorem anyCheck_polyTime : ComputableTidilyInPolyTime anyCheck (encPair encInstBin encLL)
    encBool := by
  have hk := checkBin_polyTime.tidy
  unfold anyCheck
  fun_prop

lemma anyCheck_allSections (I : Inst) :
    anyCheck (I, allSections (candLists I)) = someCandidateMissing I.n I := by
  rw [anyCheck, someCandidateMissing, candidateStates, allSections_eq]
  simp [candLists]

/-- The search over all candidate states, for every number of attributes, within explicit
bounds. -/
theorem someCandidateMissing_inO : ∃ T S,
    ComputableTidilyInO (fun I : Inst => someCandidateMissing I.n I) encInstBin encBool T S ∧
      XPBounded instSize Inst.n T ∧ XPBounded instSize Inst.n S := by
  obtain ⟨T, S, h, hT, hS⟩ := pipeline_inO candLists_polyTime (by simp [candLists])
    anyCheck_polyTime
  exact ⟨T, S, h.of_enc_eq fun I => by rw [anyCheck_allSections], hT, hS⟩

/-- The test of the counter: the weighted count of the valid class vectors of full length. -/
def countTest (p : Inst × List (List ℕ)) : ℕ :=
  p.2.foldl (fun acc c => acc +
    if validB (p.1, c) && decide (c.length = p.1.1.length) then classStateWeight (p.1, c) else 0) 0

lemma classStateWeight_le_domProd_of_length {I : Inst} {c : List ℕ} (h : c.length = I.1.length) :
    classStateWeight (I, c) ≤ domProd I := by
  rw [classStateWeight, foldl_mul_eq, one_mul, domProd, ← List.prod_eq_foldl]
  exact prod_classWeight_le I I.1 h

theorem countTest_polyTime : ComputableTidilyInPolyTime countTest (encPair encInstBin encLL)
    encNat := by
  have hv := validB_polyTime
  have hw := classStateWeight_polyTime
  have hd := domProd_polyTime.tidy
  have hp : PolyBounded (fun x : Inst × List (List ℕ) => (encPair encInstBin encLL x).length)
      fun x => (encNat (domProd x.1)).length :=
    (hd.comp (ComputableTidilyInPolyTime.fst encInstBin encLL)).polyBounded_length
  unfold countTest
  refine ComputableTidilyInPolyTime.foldlWithInput_of_bounded_growth (encA := encList encNat)
    (encL := encLL) (list := fun x : Inst × List (List ℕ) => x.2)
    (step := fun x acc c => acc + if validB (x.1, c) && decide (c.length = x.1.1.length) then
      classStateWeight (x.1, c) else 0)
    (growth := fun x => (encNat (domProd x.1)).length + 1)
    (by fun_prop) ⟨by fun_prop, by fun_prop, inferInstance, inferInstance⟩
    ⟨hp.add (.const 1), fun x a c _ => ?_⟩
  refine (length_encNat_add_le_add a _).trans ?_
  have : (encNat (if validB (x.1, c) && decide (c.length = x.1.1.length) then
      classStateWeight (x.1, c) else 0)).length ≤ (encNat (domProd x.1)).length := by
    refine ComputableTidilyInO.length_encNat_mono ?_
    split_ifs with h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact classStateWeight_le_domProd_of_length h.2
    · exact Nat.zero_le _
  omega

theorem classLists_polyTime :
    ComputableTidilyInPolyTime (fun I : Inst => I.1.map fun _ => classVals I)
    encInstBin encLL := by
  have hc := classVals_polyTime
  have hf : ComputableTidilyInPolyTime (fun p : Inst × ℕ => classVals p.1)
      (encPair encInstBin encNat) (encList encNat) := hc.comp (by fun_prop)
  exact ComputableTidilyInPolyTime.mapWithInput (encIn := encInstBin)
    (list := fun I : Inst => I.1) (f := fun I _ => classVals I)
    (ComputableTidilyInPolyTime.fst (encList encNat)
      (encPair (encList (encList (encPair encNat encNat))) (encList (encList encNat)))) hf

lemma countTest_allSections (I : Inst) :
    countTest (I, allSections (I.1.map fun _ => classVals I)) = missingCount I := by
  rw [missingCount_eq_countClasses (le_refl I.n), countClasses, countTest, classStates,
    allSections_eq, List.length_map, foldl_add_eq, foldl_add_eq]
  refine congrArg (0 + ·) (congrArg List.sum (List.map_congr_left fun c hc => ?_))
  have hlen := length_of_mem_boundedSections hc
  rw [List.length_map] at hlen
  simp [hlen]

/-- The weighted count over all class vectors, for every number of attributes, within explicit
bounds. -/
theorem missingCount_inO : ∃ T S,
    ComputableTidilyInO (fun I : Inst => missingCount I) encInstBin encNat T S ∧
      XPBounded instSize Inst.n T ∧ XPBounded instSize Inst.n S := by
  obtain ⟨T, S, h, hT, hS⟩ := pipeline_inO classLists_polyTime (by simp) countTest_polyTime
  exact ⟨T, S, h.of_enc_eq fun I => by rw [countTest_allSections], hT, hS⟩

/-! ### Explicit bounds -/

/-- From bounds `O(T)`, `O(S)` of the form of `XPBounded`, a bound `c · (|x| + 1) ^ (d · n + d)`. -/
theorem timeAndSpace_of_xp {β : Type} {encOut : β ↪ List Bool} {f : Inst → β}
    (h : ∃ T S, ComputableTidilyInO f encInstBin encOut T S ∧
      XPBounded instSize Inst.n T ∧ XPBounded instSize Inst.n S) :
    ∃ c d, ComputableTidilyInTimeAndSpace f encInstBin encOut
      (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d))
      (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d)) :=
  let ⟨_, _, h, hT, hS⟩ := h
  timeAndSpace_of_inO_xp h hT hS

/-- Negation, within explicit bounds. -/
theorem not_inO {f : Inst → Bool}
    (h : ∃ T S, ComputableTidilyInO f encInstBin encBool T S ∧
      XPBounded instSize Inst.n T ∧ XPBounded instSize Inst.n S) :
    ∃ T S, ComputableTidilyInO (fun I => !f I) encInstBin encBool T S ∧
      XPBounded instSize Inst.n T ∧ XPBounded instSize Inst.n S := by
  obtain ⟨T, S, h, hT, hS⟩ := h
  obtain ⟨d, hn⟩ := inO_pow_of_polyTime (f := fun b : Bool => !b) (encIn := encBool)
    (encOut := encBool) (by fun_prop)
  have hc : ∀ b : Bool, ((encBool b).length + 1) ^ d = 2 ^ d := fun b => by cases b <;> rfl
  refine ⟨_, _, hn.comp h, hT.add ((XPBounded.const (2 ^ d)).of_le fun I => (hc _).le),
    hS.add ((XPBounded.const (2 ^ d)).of_le fun I => (hc _).le)⟩

/-- A bound for every instance gives, for each `k`, the bound with `k` in place of `n` on the
instances with at most `k` attributes. -/
theorem fixedAttrs_of_timeAndSpace {β : Type} {encOut : β ↪ List Bool} {f : Inst → β}
    (h : ∃ c d, ComputableTidilyInTimeAndSpace f encInstBin encOut
      (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d))
      (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d))) :
    ∃ c d₀ d₁, ∀ k, ComputableTidilyInTimeAndSpace (fun I : {I : Inst // I.n ≤ k} => f I.1)
      ((Function.Embedding.subtype _).trans encInstBin) encOut
      (fun I => c * ((encInstBin I.1).length + 1) ^ (d₀ * k + d₁))
      (fun I => c * ((encInstBin I.1).length + 1) ^ (d₀ * k + d₁)) := by
  obtain ⟨c, d, h⟩ := h
  refine ⟨c, d, d, fun k => (h.restrict _).mono (fun I => ?_) (fun I => ?_)⟩ <;>
  · refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) ?_)
    have := Nat.mul_le_mul_left d I.2
    omega

/-- A bound for every instance gives one machine for the procedure with `k` in the input (in
unary), within `c · (|(k, x)| + 1) ^ (d · k + d)`; it answers `b` on instances with more than `k`
attributes. -/
theorem withBound_timeAndSpace {β : Type} {encOut : β ↪ List Bool} {f : Inst → β} (b : β)
    (h : ∃ T S, ComputableTidilyInO f encInstBin encOut T S ∧
      XPBounded instSize Inst.n T ∧ XPBounded instSize Inst.n S) :
    ∃ c d, ComputableTidilyInTimeAndSpace (fun p : ℕ × Inst => if p.2.n ≤ p.1 then f p.2 else b)
      (encPair encUnary encInstBin) encOut
      (fun p => c * ((encPair encUnary encInstBin p).length + 1) ^ (d * p.1 + d))
      (fun p => c * ((encPair encUnary encInstBin p).length + 1) ^ (d * p.1 + d)) := by
  obtain ⟨T, S, h, ⟨cT, eT, hT⟩, ⟨cS, eS, hS⟩⟩ := h
  have hcond : ComputableTidilyInPolyTime (fun p : ℕ × Inst => decide (p.2.1.length ≤ p.1))
      (encPair encUnary encInstBin) encBool := by fun_prop
  obtain ⟨dq, hq⟩ := inO_pow_of_polyTime hcond
  have hsnd := ComputableTidilyInO.snd encUnary encInstBin
  have hf := h.comp hsnd
  have hg := ComputableTidilyInO.const (encIn := encPair encUnary encInstBin) (encMid := encOut) b
  have hi := ComputableTidilyInO.ite hq hf hg
  let size := fun p : ℕ × Inst => (encPair encUnary encInstBin p).length
  have hpos : ∀ p, 1 ≤ size p := fun p => by simp only [size, length_encPair]; omega
  have hle : ∀ p : ℕ × Inst, instSize p.2 ≤ size p := fun p => by
    simp only [size, instSize, length_encPair]; omega
  have hbranch : ∀ {c e : ℕ} {U : Inst → ℕ},
      (∀ I, U I ≤ c * (instSize I + 1) ^ (e * (I.n + 1))) →
      XPBounded size Prod.fst fun p =>
        (encPair encUnary encInstBin p).length + if decide (p.2.1.length ≤ p.1) then
          (encPair encUnary encInstBin p).length + U p.2 else
          (encPair encUnary encInstBin p).length := by
    intro c e U hU
    refine ⟨c + 2, e + 1, fun p => ?_⟩
    have h1 : size p ≤ (size p + 1) ^ ((e + 1) * (p.1 + 1)) :=
      (Nat.le_succ _).trans ((Nat.pow_one _).symm.le.trans
        (Nat.pow_le_pow_right (Nat.succ_pos _) (by nlinarith)))
    dsimp only
    split_ifs with hk
    · have hk : p.2.n ≤ p.1 := by simpa using hk
      have h2 : U p.2 ≤ c * (size p + 1) ^ ((e + 1) * (p.1 + 1)) :=
        (hU p.2).trans (Nat.mul_le_mul_left _
          ((Nat.pow_le_pow_left (by have := hle p; omega) _).trans
          (Nat.pow_le_pow_right (Nat.succ_pos _) (by nlinarith))))
      simp only [size] at h1 h2
      nlinarith
    · simp only [size] at h1
      nlinarith
  have hpoly : XPBounded size Prod.fst fun p => ((encPair encUnary encInstBin p).length + 1) ^ dq :=
    XPBounded.of_poly 1 dq fun p => by simp [size]
  obtain ⟨c, d, hm⟩ := timeAndSpace_of_inO_xp (n := Prod.fst) hi
    ((hpoly.add (hbranch hT)).of_le fun p => by split_ifs <;> simp)
    ((hpoly.add (hbranch hS)).of_le fun p => by split_ifs <;> simp)
  exact ⟨c, d, hm.of_enc_eq fun p => by simp⟩

lemma decide_nonempty_eq (I : Inst) :
    decide (missing I.con I.table).Nonempty = someCandidateMissing I.n I := by
  by_cases h : (missing I.con I.table).Nonempty
  · rw [decide_eq_true h]
    exact ((someCandidateMissing_iff (le_refl I.n)).2 h).symm
  · rw [decide_eq_false h]
    exact (Bool.eq_false_iff.2 fun h' => h ((someCandidateMissing_iff (le_refl I.n)).1 h')).symm

lemma decide_empty_eq (I : Inst) :
    decide (missing I.con I.table = ∅) = !someCandidateMissing I.n I := by
  rw [← decide_nonempty_eq]
  by_cases h : (missing I.con I.table).Nonempty
  · simp [h, Finset.nonempty_iff_ne_empty.1 h]
  · simp [Finset.not_nonempty_iff_eq_empty.1 h]

/-! ### Main results -/

/-- **One machine decides M(T₀) ≠ ∅ on every instance within `c · (|x| + 1) ^ (d · n + d)`**,
`n` the number of attributes and `|x|` the length of the binary encoding, in time and space. -/
theorem missingNonempty_explicitDegree :
    ∃ c d, ComputableTidilyInTimeAndSpace
      (fun I : Inst => decide (missing I.con I.table).Nonempty) encInstBin encBool
      (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d))
      (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d)) := by
  obtain ⟨c, d, h⟩ := timeAndSpace_of_xp someCandidateMissing_inO
  exact ⟨c, d, h.of_enc_eq fun I => by rw [decide_nonempty_eq]⟩

/-- **One machine decides completeness on every instance within `c · (|x| + 1) ^ (d · n + d)`.** -/
theorem complete_explicitDegree :
    ∃ c d, ComputableTidilyInTimeAndSpace
      (fun I : Inst => decide (missing I.con I.table = ∅)) encInstBin encBool
      (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d))
      (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d)) := by
  obtain ⟨c, d, h⟩ := timeAndSpace_of_xp (not_inO someCandidateMissing_inO)
  exact ⟨c, d, h.of_enc_eq fun I => by rw [decide_empty_eq]⟩

/-- **One machine computes |M(T₀)| on every instance within `c · (|x| + 1) ^ (d · n + d)`.** -/
theorem missingCount_explicitDegree :
    ∃ c d, ComputableTidilyInTimeAndSpace (fun I : Inst => missingCount I) encInstBin encNat
      (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d))
      (fun I => c * ((encInstBin I).length + 1) ^ (d * I.n + d)) :=
  timeAndSpace_of_xp missingCount_inO

/-- **Uniformity in `k`, M(T₀) ≠ ∅:** the same constants `c`, `d₀`, `d₁` for every `k`, on the
instances with at most `k` attributes. -/
theorem missingNonemptyFixedAttrs_uniform :
    ∃ c d₀ d₁, ∀ k, ComputableTidilyInTimeAndSpace
      (fun I : {I : Inst // I.n ≤ k} => decide (missing I.1.con I.1.table).Nonempty)
      ((Function.Embedding.subtype _).trans encInstBin) encBool
      (fun I => c * ((encInstBin I.1).length + 1) ^ (d₀ * k + d₁))
      (fun I => c * ((encInstBin I.1).length + 1) ^ (d₀ * k + d₁)) :=
  fixedAttrs_of_timeAndSpace missingNonempty_explicitDegree

/-- **Uniformity in `k`, completeness.** -/
theorem completeFixedAttrs_uniform :
    ∃ c d₀ d₁, ∀ k, ComputableTidilyInTimeAndSpace
      (fun I : {I : Inst // I.n ≤ k} => decide (missing I.1.con I.1.table = ∅))
      ((Function.Embedding.subtype _).trans encInstBin) encBool
      (fun I => c * ((encInstBin I.1).length + 1) ^ (d₀ * k + d₁))
      (fun I => c * ((encInstBin I.1).length + 1) ^ (d₀ * k + d₁)) :=
  fixedAttrs_of_timeAndSpace complete_explicitDegree

/-- **Uniformity in `k`, counting.** -/
theorem missingCountFixedAttrs_uniform :
    ∃ c d₀ d₁, ∀ k, ComputableTidilyInTimeAndSpace
      (fun I : {I : Inst // I.n ≤ k} => missingCount I.1)
      ((Function.Embedding.subtype _).trans encInstBin) encNat
      (fun I => c * ((encInstBin I.1).length + 1) ^ (d₀ * k + d₁))
      (fun I => c * ((encInstBin I.1).length + 1) ^ (d₀ * k + d₁)) :=
  fixedAttrs_of_timeAndSpace missingCount_explicitDegree

/-- **The fixed-`k` decider of M(T₀) ≠ ∅, with `k` in the input:** one machine, on every pair
`(k, I)` (`k` in unary), decides `I.n ≤ k ∧ M(T₀) ≠ ∅` within `c · (|(k, x)| + 1) ^ (d · k + d)`. -/
theorem missingNonemptyWithBound_explicitDegree :
    ∃ c d, ComputableTidilyInTimeAndSpace
      (fun p : ℕ × Inst => decide (p.2.n ≤ p.1 ∧ (missing p.2.con p.2.table).Nonempty))
      (encPair encUnary encInstBin) encBool
      (fun p => c * ((encPair encUnary encInstBin p).length + 1) ^ (d * p.1 + d))
      (fun p => c * ((encPair encUnary encInstBin p).length + 1) ^ (d * p.1 + d)) := by
  obtain ⟨c, d, h⟩ := withBound_timeAndSpace false someCandidateMissing_inO
  refine ⟨c, d, h.of_enc_eq fun p => ?_⟩
  by_cases hk : p.2.n ≤ p.1
  · simp only [hk, ↓reduceIte, true_and]
    rw [decide_nonempty_eq]
  · simp [hk]

/-- **The fixed-`k` decider of completeness, with `k` in the input.** -/
theorem completeWithBound_explicitDegree :
    ∃ c d, ComputableTidilyInTimeAndSpace
      (fun p : ℕ × Inst => decide (p.2.n ≤ p.1 ∧ missing p.2.con p.2.table = ∅))
      (encPair encUnary encInstBin) encBool
      (fun p => c * ((encPair encUnary encInstBin p).length + 1) ^ (d * p.1 + d))
      (fun p => c * ((encPair encUnary encInstBin p).length + 1) ^ (d * p.1 + d)) := by
  obtain ⟨c, d, h⟩ := withBound_timeAndSpace false (not_inO someCandidateMissing_inO)
  refine ⟨c, d, h.of_enc_eq fun p => ?_⟩
  by_cases hk : p.2.n ≤ p.1
  · simp only [hk, ↓reduceIte, true_and]
    rw [decide_empty_eq]
  · simp [hk]

/-- **The fixed-`k` counter, with `k` in the input:** one machine computes
`if I.n ≤ k then |M(T₀)| else 0` within `c · (|(k, x)| + 1) ^ (d · k + d)`. -/
theorem missingCountWithBound_explicitDegree :
    ∃ c d, ComputableTidilyInTimeAndSpace
      (fun p : ℕ × Inst => if p.2.n ≤ p.1 then missingCount p.2 else 0)
      (encPair encUnary encInstBin) encNat
      (fun p => c * ((encPair encUnary encInstBin p).length + 1) ^ (d * p.1 + d))
      (fun p => c * ((encPair encUnary encInstBin p).length + 1) ^ (d * p.1 + d)) :=
  withBound_timeAndSpace 0 missingCount_inO

end Latc.PaperD.General
