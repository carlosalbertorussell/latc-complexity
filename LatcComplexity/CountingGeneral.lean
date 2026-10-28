import LatcComplexity.Adequacy

/-!
# Counting |M(T₀)| over general finite domains is #P-complete

For an instance `I = (d, S, T)` of `LatcComplexity.General`, `missingCount I` is |M(T₀)| for the table
it denotes in latc-check's model (`LatcComplexity.Adequacy`): the number of tuples of
`Latc.missing I.con I.table`.

* Membership (`missingCount_mem_SharpP`): a certificate is the encoding of a state as a list of
  binary numbers, padded with `false` to the length of the encoded domain sizes (`certWord`); the
  verifier (`cverifier`) decodes the first `n` values, checks them, and accepts only the canonical
  padded encoding. The accepted certificates are in bijection with the tuples of M(T₀)
  (`missingCount_eq_acceptCount`).
* Hardness (`missingCount_sharpPHard`): the SAT reduction of `LatcComplexity.General` (dense
  variables, domains {0, 1}, T₀ = ∅) is parsimonious (`sharpSAT_eq_missingCount`).
* `missingCount_sharpPComplete`: counting |M(T₀)| is `#P`-complete under parsimonious reductions.
-/

namespace Latc.PaperD.General

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-- |M(T₀)| for the table denoted by an instance, in latc-check's model. -/
def missingCount (I : Inst) : ℕ := (missing I.con I.table).card

/-! ### The counting verifier -/

/-- The state described by a certificate: its first `n` decoded numbers. -/
def certState (I : Inst) (w : List Bool) : List ℕ :=
  ((Decoder.list Decoder.nat).decode w).take I.1.length

/-- The canonical certificate of length `L` of a state: its encoding padded with `false`. -/
def certWord (s : List ℕ) (L : ℕ) : List Bool :=
  encList encNat s ++ List.replicate (L - (encList encNat s).length) false

/-- Accept a certificate when the state it describes is in M(T₀) and the certificate is the
canonical one of that state. -/
def cverifier (p : Inst × List Bool) : Bool :=
  check (p.1, certState p.1 p.2) && (p.2 == certWord (certState p.1 p.2) p.2.length)

/-- The certificate length: the length of the encoded domain sizes. -/
def certLen (I : Inst) : ℕ := (encList encNat I.1).length

theorem encList_polyTime : ComputableInPolyTime (encList encNat : List ℕ → List Bool)
    (encList encNat) encBits := .of_eq fun _ => rfl

theorem certState_polyTime :
    ComputableInPolyTime (fun p : Inst × List Bool => certState p.1 p.2)
      (encPair encInst encBits) (encList encNat) := by
  have hd : ComputableTidilyInPolyTime
      (fun p : Inst × List Bool => (Decoder.list Decoder.nat).decode p.2)
      (encPair encInst encBits) (encList encNat) :=
    (Decoder.list Decoder.nat).computableInPolyTime.tidy.comp (by fun_prop)
  have hn : ComputableTidilyInPolyTime (fun p : Inst × List Bool => p.1.1.length)
      (encPair encInst encBits) encUnary := by fun_prop
  exact .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput hd hn)

theorem cverifier_polyTime :
    ComputableInPolyTime cverifier (encPair encInst encBits) encBool := by
  have hc := check_polyTime.tidy
  have hs := certState_polyTime.tidy
  have he := encList_polyTime.tidy
  refine .of_tidy ?_
  unfold cverifier certWord
  fun_prop

theorem certLen_polyTime : ComputableInPolyTime certLen encInst encUnary := by
  have he := encList_polyTime.tidy
  refine .of_tidy ?_
  unfold certLen
  fun_prop

/-! ### Accepted certificates are the tuples of M(T₀) -/

/-- Padding with `false` adds empty frames. -/
lemma frames_encList_append_replicate (s : List ℕ) (k : ℕ) :
    frames (encList encNat s ++ List.replicate k false) = s.map encNat ++ List.replicate k [] := by
  induction s with
  | nil =>
    simp only [encList_nil, List.nil_append, List.map_nil]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.replicate_succ, List.replicate_succ,
        show false :: List.replicate k false = frame [] ++ List.replicate k false by
          simp [frame_nil],
        frames_frame_append, ih]
  | cons a s ih =>
    rw [encList_cons, List.append_assoc, frames_frame_append, ih, List.map_cons, List.cons_append]

/-- The state of a canonical certificate is the state it encodes. -/
lemma certState_certWord (I : Inst) {s : List ℕ} (hs : s.length = I.1.length) (L : ℕ) :
    certState I (certWord s L) = s := by
  have hdec : (Decoder.list Decoder.nat).decode (certWord s L) =
      s ++ List.replicate (L - (encList encNat s).length) (Decoder.nat.decode []) := by
    change (frames (certWord s L)).map Decoder.nat.decode = _
    rw [certWord, frames_encList_append_replicate, List.map_append, List.map_map,
      List.map_replicate]
    congr 1
    conv_rhs => rw [← List.map_id s]
    exact List.map_congr_left fun a _ => Decoder.nat.decode_enc a
  rw [certState, hdec, ← hs, List.take_left']
  rfl

lemma length_certWord {s : List ℕ} {L : ℕ} (h : (encList encNat s).length ≤ L) :
    (certWord s L).length = L := by
  simp only [certWord, List.length_append, List.length_replicate]
  omega

lemma ofFn_getD {l : List Bool} {L : ℕ} (h : l.length = L) :
    List.ofFn (fun j : Fin L => l.getD j false) = l := by
  subst h
  apply List.ext_getElem (by simp)
  intro j h₁ h₂
  simp

/-- The canonical certificate of a tuple, as a function on positions. -/
def certFun (I : Inst) (x : ∀ i, I.Dom i) : Fin (certLen I) → Bool :=
  fun j => (certWord (I.toList x) (certLen I)).getD j false

lemma ofFn_certFun (I : Inst) (x : ∀ i, I.Dom i) :
    List.ofFn (certFun I x) = certWord (I.toList x) (certLen I) :=
  ofFn_getD (length_certWord (length_encList_le_of_inDomains (I.inDomains_toList x)))

/-- **Certificates and tuples:** the certificates of length `certLen I` that `cverifier` accepts
are as many as the tuples of M(T₀). -/
theorem missingCount_eq_acceptCount (I : Inst) :
    missingCount I = acceptCount cverifier I (certLen I) := by
  unfold missingCount acceptCount
  refine Finset.card_bij (fun x _ => certFun I x) (fun x hx => ?_) (fun x₁ _ x₂ _ h => ?_)
    fun w hw => ?_
  · rw [Finset.mem_filter, ofFn_certFun]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hs := certState_certWord I (I.length_toList x) (certLen I)
    simp only [cverifier, hs, Bool.and_eq_true, beq_iff_eq]
    refine ⟨(check_iff I _).2 ⟨I.inDomains_toList x, (mem_missing_iff I x).1 hx⟩, ?_⟩
    rw [length_certWord (L := certLen I) (length_encList_le_of_inDomains (I.inDomains_toList x))]
  · have h' := congrArg List.ofFn h
    rw [ofFn_certFun, ofFn_certFun] at h'
    have := congrArg (certState I) h'
    rw [certState_certWord I (I.length_toList _), certState_certWord I (I.length_toList _)] at this
    exact I.toList_injective this
  · rw [Finset.mem_filter] at hw
    simp only [cverifier, Bool.and_eq_true, beq_iff_eq, List.length_ofFn] at hw
    obtain ⟨hcheck, hcanon⟩ := hw.2
    obtain ⟨hdom, hval, hT⟩ := (check_iff I _).1 hcheck
    obtain ⟨x, hx⟩ := I.exists_toList_eq hdom
    refine ⟨x, (mem_missing_iff I x).2 ⟨hx ▸ hval, hx ▸ hT⟩, ?_⟩
    funext j
    rw [certFun, hx, ← hcanon, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-- **Counting |M(T₀)| is in #P.** -/
theorem missingCount_mem_SharpP : missingCount ∈ SharpP encInst := by
  have h := mem_SharpP_of_polyTime_length cverifier_polyTime certLen_polyTime
  rwa [show (fun a => acceptCount cverifier a (certLen a)) = missingCount from
    funext fun a => (missingCount_eq_acceptCount a).symm] at h

/-! ### Hardness: the SAT reduction preserves counts -/

/-- A clause constraint set from a formula over variables below `n` holds on a state of values in
{0, 1} exactly when the formula holds under the matching assignment. -/
lemma valid_iff_eval (ψ : CNF ℕ) (n : ℕ) (hψ : ∀ v ∈ ψ.vars, v < n) (s : List ℕ)
    (σ : ℕ → Bool) (hs : ∀ i < n, s[i]? = some (if σ i then 1 else 0)) :
    Valid (ψ.map (List.map toCond)) s ↔ ψ.eval σ = true := by
  have hlit : ∀ c ∈ ψ, ∀ l ∈ c, (CondHolds s (toCond l) ↔ Literal.eval σ l = true) := by
    intro c hc l hl
    have hv : l.1 < n := hψ l.1 (List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨c, hc, hl⟩, rfl⟩)
    simp only [CondHolds, toCond, hs _ hv, Option.some.injEq, Literal.eval, beq_iff_eq]
    cases σ l.1 <;> cases l.2 <;> simp
  unfold Valid
  rw [CNF.eval, List.all_eq_true]
  constructor
  · intro h c hc
    obtain ⟨a, ha, hholds⟩ := h _ (List.mem_map.2 ⟨c, hc, rfl⟩)
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 ha
    exact List.any_eq_true.2 ⟨l, hl, (hlit c hc l hl).1 hholds⟩
  · intro h c' hc'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    obtain ⟨l, hl, hev⟩ := List.any_eq_true.1 (h c hc)
    exact ⟨toCond l, List.mem_map.2 ⟨l, hl, rfl⟩, (hlit c hc l hl).2 hev⟩

lemma fromSAT_get (φ : CNF ℕ) (i : Fin (fromSAT φ).n) : (fromSAT φ).1.get i = 2 :=
  List.eq_of_mem_replicate (List.get_mem _ _)

lemma fromSAT_n (φ : CNF ℕ) : (fromSAT φ).n = φ.numVars := by
  simp [Inst.n, fromSAT]

/-- The tuple of an assignment on the instance `fromSAT φ`: 1 for true, 0 for false. -/
def boolTuple (φ : CNF ℕ) (σ : ℕ → Bool) : ∀ i, (fromSAT φ).Dom i :=
  fun i => ⟨if σ i then 1 else 0, by rw [fromSAT_get]; split <;> omega⟩

lemma getElem?_toList_boolTuple (φ : CNF ℕ) (σ : ℕ → Bool) {i : ℕ} (hi : i < φ.numVars) :
    ((fromSAT φ).toList (boolTuple φ σ))[i]? = some (if σ i then 1 else 0) := by
  have hn : i < (fromSAT φ).n := by rw [fromSAT_n]; exact hi
  simp only [Inst.getElem?_toList, hn, ↓reduceDIte]
  rfl

lemma mem_vars_denseRelabel_iff (φ : CNF ℕ) (v : ℕ) :
    v ∈ φ.denseRelabel.vars ↔ v < φ.numVars := by
  rw [← List.mem_toFinset, CNF.vars_denseRelabel_toFinset, Finset.mem_range]

/-- **The reduction is parsimonious:** the satisfying assignments of `φ` are as many as the tuples
of M(T₀) for `fromSAT φ`. -/
theorem sharpSAT_eq_missingCount (φ : CNF ℕ) : SharpSAT φ = missingCount (fromSAT φ) := by
  rw [SharpSAT, ← CNF.modelCount_denseRelabel]
  have hψ : ∀ v ∈ φ.denseRelabel.vars, v < φ.numVars := fun v hv =>
    (mem_vars_denseRelabel_iff φ v).1 hv
  have hlt (i : Fin (fromSAT φ).n) : i.val < φ.numVars := fromSAT_n φ ▸ i.isLt
  refine (CNF.modelCount_eq_card_filter (φ := φ.denseRelabel) (boolTuple φ)
    (fun x => x ∈ missing (fromSAT φ).con (fromSAT φ).table) (fun σ τ _ _ => ⟨fun h v hv => ?_,
      fun h => funext fun i => Fin.ext ?_⟩) fun x => ⟨fun hx => ?_, ?_⟩).trans ?_
  · have := congrArg Fin.val (congrFun h ⟨v, (fromSAT_n φ).symm ▸ hψ v hv⟩)
    simp only [boolTuple] at this
    cases hσ : σ v <;> cases hτ : τ v <;> simp_all
  · simp only [boolTuple]
    rw [h i ((mem_vars_denseRelabel_iff φ i).2 (hlt i))]
  · -- a tuple of M(T₀) comes from the assignment reading its values
    let σ : ℕ → Bool := fun i => ((fromSAT φ).toList x).getD i 0 == 1
    have hbx : boolTuple φ σ = x := by
      funext i
      apply Fin.ext
      have h2 : (x i).val < 2 := fromSAT_get φ i ▸ (x i).isLt
      have hget : ((fromSAT φ).toList x).getD i 0 = (x i).val := by
        rw [List.getD_eq_getElem?_getD, Inst.getElem?_toList]
        split_ifs with h
        · rfl
        · exact absurd i.isLt h
      simp only [boolTuple, σ, hget]
      have h01 : (x i).val = 0 ∨ (x i).val = 1 := by omega
      rcases h01 with h | h <;> simp [h]
    refine ⟨σ, ?_, hbx⟩
    have hval := ((mem_missing_iff _ x).1 hx).1
    rw [← hbx] at hval
    exact (valid_iff_eval _ φ.numVars hψ _ σ fun i hi =>
      getElem?_toList_boolTuple φ σ hi).1 hval
  · rintro ⟨σ, hσ, rfl⟩
    rw [mem_missing_iff]
    refine ⟨(valid_iff_eval _ φ.numVars hψ _ σ fun i hi =>
      getElem?_toList_boolTuple φ σ hi).2 hσ, by simp [fromSAT]⟩
  · unfold missingCount
    congr 1
    ext x
    simp

/-! ### #P-completeness -/

/-- `#SAT` reduces parsimoniously to counting |M(T₀)|. -/
theorem sharpSAT_reduces_missingCount :
    ParsimoniousReducible encCNF encInst SharpSAT missingCount :=
  ⟨fromSAT, fromSAT_polyTime, sharpSAT_eq_missingCount⟩

/-- **Counting |M(T₀)| is #P-hard**, from the parsimonious Cook–Levin theorem. -/
theorem missingCount_sharpPHard : SharpPHard encInst missingCount :=
  CookLevin.SharpSAT_sharpPHard.trans sharpSAT_reduces_missingCount

/-- **Proposition 5, counting part, general finite domains:** counting |M(T₀)| of latc-check's
model is `#P`-complete under parsimonious reductions; with T₀ = ∅ this is |𝒱|. -/
theorem missingCount_sharpPComplete : SharpPComplete encInst missingCount :=
  ⟨missingCount_mem_SharpP, missingCount_sharpPHard⟩

end Latc.PaperD.General
