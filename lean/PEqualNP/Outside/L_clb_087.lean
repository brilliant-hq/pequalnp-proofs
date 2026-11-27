import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_377

namespace PEqualNP.Outside.L_clb_087

def packW (w : ℕ) (state : Fin w → Bool) : ℕ :=
  (List.range w).foldl (fun (acc bit : ℕ) =>
    acc ||| ((if h : bit < w then state ⟨bit, h⟩ else false).toNat <<< bit)) 0

def testRow (w : ℕ) (r : ℕ → Bool) (state : Fin w → Bool) (b : Bool) : Bool :=
  r (packW w state ||| (b.toNat <<< w))

def nx {w : ℕ} (state : Fin w → Bool) (b : Bool) : Fin w → Bool :=
  fun j => if h : j.val + 1 < w then state ⟨j.val + 1, h⟩ else b

def matNat (w : ℕ) (r : ℕ → Bool) : Matrix (Fin w → Bool) (Fin w → Bool) ℕ :=
  Matrix.of fun p q =>
    (Finset.univ.filter fun bit : Bool => testRow w r p bit = true ∧ nx p bit = q).card

def matZ2 (w : ℕ) (r : ℕ → Bool) : Matrix (Fin w → Bool) (Fin w → Bool) (ZMod 2) :=
  (matNat w r).map (Nat.castRingHom (ZMod 2))

def z2ToBool (x : ZMod 2) : Bool := decide (x = 1)

lemma testBit_zero_eq_z2ToBool (m : ℕ) : m.testBit 0 = z2ToBool (m : ZMod 2) := by
  have h1 : m.testBit 0 = decide (m % 2 = 1) := by
    rw [Nat.testBit_zero]
  rw [h1]
  have hmod : (m : ZMod 2) = ((m % 2 : ℕ) : ZMod 2) := by
    rw [← ZMod.natCast_mod]
  rw [hmod]
  have hlt : m % 2 < 2 := Nat.mod_lt m (by decide)
  interval_cases (m % 2) <;> decide

def mulVecZ2 (w : ℕ) (v : (Fin w → Bool) → ZMod 2) (r : ℕ → Bool) : (Fin w → Bool) → ZMod 2 :=
  fun q => ∑ p : Fin w → Bool, v p * matZ2 w r p q

def initVec {w : ℕ} (eD : Fin (2 ^ w) ≃ (Fin w → Bool)) (seed : ℕ) : (Fin w → Bool) → ZMod 2 :=
  if h : seed < 2 ^ w then fun q => if q = eD ⟨seed, h⟩ then 1 else 0 else fun _ => 0

lemma mulVecZ2_eq_vecMul (w : ℕ) (v : (Fin w → Bool) → ZMod 2) (r : ℕ → Bool) :
    mulVecZ2 w v r = Matrix.vecMul v (matZ2 w r) := by
  funext q
  simp [mulVecZ2, Matrix.vecMul, dotProduct]

lemma foldl_mulVecZ2 (w : ℕ) (v : (Fin w → Bool) → ZMod 2) (table : ℕ → ℕ → Bool) (k : ℕ) :
    (List.range k).foldl (fun cur siteId => mulVecZ2 w cur (table siteId)) v =
      Matrix.vecMul v ((List.ofFn (fun i : Fin k => matZ2 w (table i.val))).prod) := by
  induction k with
  | zero =>
    simp [Matrix.vecMul_one]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      mulVecZ2_eq_vecMul, Matrix.vecMul_vecMul]
    congr 1
    rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
    rfl

lemma initVec_vecMul {w : ℕ} (eD : Fin (2 ^ w) ≃ (Fin w → Bool)) (seed : ℕ)
    (M : Matrix (Fin w → Bool) (Fin w → Bool) (ZMod 2)) (q : Fin w → Bool) :
    Matrix.vecMul (initVec eD seed) M q =
      if h : seed < 2 ^ w then M (eD ⟨seed, h⟩) q else 0 := by
  unfold initVec
  split_ifs with h
  · simp [Matrix.vecMul, dotProduct]
  · simp [Matrix.vecMul, dotProduct]

lemma packW_eq_foldl (n w : ℕ) (word site : ℕ) :
    (List.range (w + 1)).foldl (fun (acc bit : ℕ) =>
      acc ||| ((word.testBit ((site + bit) % n)).toNat <<< bit)) 0 =
    packW w (fun pos : Fin w => word.testBit ((site + pos.val) % n)) |||
      ((word.testBit ((site + w) % n)).toNat <<< w) := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  congr 1
  unfold packW
  have hcongr : ∀ (l : List ℕ) (acc : ℕ), (∀ b ∈ l, b < w) →
      l.foldl (fun (acc bit : ℕ) => acc ||| ((word.testBit ((site + bit) % n)).toNat <<< bit)) acc =
      l.foldl (fun (acc bit : ℕ) =>
        acc ||| ((if h : bit < w then word.testBit ((site + bit) % n) else false).toNat <<< bit)) acc := by
    intro l
    induction l with
    | nil => intro acc _; rfl
    | cons b bs ih =>
      intro acc hmem
      simp only [List.foldl_cons]
      have hb : b < w := hmem b (List.mem_cons_self ..)
      rw [dif_pos hb]
      exact ih _ (fun x hx => hmem x (List.mem_cons_of_mem b hx))
  exact hcongr (List.range w) 0 (fun b hb => List.mem_range.mp hb)

def ofWord (n : ℕ) (word : ℕ) : Fin n → Bool :=
  fun i => word.testBit i.val

def toWord {n : ℕ} (v : Fin n → Bool) : ℕ :=
  (BitVec.ofBoolListLE (List.ofFn v)).toNat

lemma toWord_lt {n : ℕ} (v : Fin n → Bool) : toWord v < 2 ^ n := by
  have h := (BitVec.ofBoolListLE (List.ofFn v)).isLt
  simpa [toWord, List.length_ofFn] using h

lemma testBit_toWord {n : ℕ} (v : Fin n → Bool) (k : ℕ) :
    (toWord v).testBit k = if h : k < n then v ⟨k, h⟩ else false := by
  unfold toWord
  rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn]
  split_ifs with h <;> simp

lemma toWord_ofWord {n : ℕ} (word : ℕ) (hw : word < 2 ^ n) : toWord (ofWord n word) = word := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_toWord]
  split_ifs with h
  · rfl
  · symm
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega)))

lemma filter_length_eq_trace (n w : ℕ) (hn : 0 < n) (rows : ℕ → ℕ → Bool) :
    ((List.range (2 ^ n)).filter (fun word => (List.range n).all (fun site =>
      let pat := (List.range (w + 1)).foldl (fun (acc bit : ℕ) =>
        acc ||| ((word.testBit ((site + bit) % n)).toNat <<< bit)) 0
      rows site pat))).length =
    Matrix.trace (List.ofFn (fun i : Fin n => matNat w (rows i.val))).prod := by
  cases n with
  | zero => omega
  | succ t =>
    let test : Fin (t + 1) → (Fin w → Bool) → Bool → Bool :=
      fun i state b => testRow w (rows i.val) state b
    have h377 := PEqualNP.Outside.L_lib_377 t w test
    dsimp only at h377
    change _ = Matrix.trace (List.ofFn (fun i : Fin (t + 1) =>
      (Matrix.of fun p q : Fin w → Bool =>
        (Finset.univ.filter fun bit : Bool =>
          test i p bit = true ∧
            (fun (state : Fin w → Bool) (b : Bool) (j : Fin w) =>
              if h : j.val + 1 < w then state ⟨j.val + 1, h⟩ else b) p bit = q).card :
        Matrix (Fin w → Bool) (Fin w → Bool) ℕ))).prod
    rw [h377]
    have hlen : ((List.range (2 ^ (t + 1))).filter (fun word => (List.range (t + 1)).all (fun site =>
        let pat := (List.range (w + 1)).foldl (fun (acc bit : ℕ) =>
          acc ||| ((word.testBit ((site + bit) % (t + 1))).toNat <<< bit)) 0
        rows site pat))).length =
      ((Finset.range (2 ^ (t + 1))).filter (fun word => (List.range (t + 1)).all (fun site =>
        let pat := (List.range (w + 1)).foldl (fun (acc bit : ℕ) =>
          acc ||| ((word.testBit ((site + bit) % (t + 1))).toNat <<< bit)) 0
        rows site pat) = true)).card := by
      have hnd : (List.range (2 ^ (t + 1))).Nodup := List.nodup_range
      rw [← List.toFinset_card_of_nodup (hnd.filter _)]
      congr 1
      ext x
      simp [Finset.mem_range, List.mem_filter]
    rw [hlen]
    apply Finset.card_nbij' (ofWord (t + 1)) toWord
    · intro word hword
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Finset.mem_univ,
        true_and, List.all_eq_true, List.mem_range] at hword ⊢
      intro a
      have ha := hword.2 a.val a.isLt
      rw [packW_eq_foldl (t + 1) w word a.val] at ha
      exact ha
    · intro v hv
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Finset.mem_univ,
        true_and, List.all_eq_true, List.mem_range] at hv ⊢
      refine ⟨toWord_lt v, ?_⟩
      intro site hsite
      rw [packW_eq_foldl (t + 1) w (toWord v) site]
      have ha := hv ⟨site, hsite⟩
      have hbit' : ∀ m : ℕ, (toWord v).testBit (m % (t + 1)) = v (Fin.ofNat (t + 1) m) := by
        intro m
        have hlt : m % (t + 1) < t + 1 := Nat.mod_lt m (Nat.succ_pos t)
        rw [testBit_toWord]
        simp only [hlt, ↓reduceDIte]
        rfl
      simp only [hbit']
      exact ha
    · intro word hword
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hword
      exact toWord_ofWord word hword.1
    · intro v _
      funext i
      simp only [ofWord, testBit_toWord, i.isLt, ↓reduceDIte]

lemma trace_mod2 (n w : ℕ) (rows : ℕ → ℕ → Bool) :
    ((Matrix.trace (List.ofFn (fun i : Fin n => matNat w (rows i.val))).prod : ℕ) : ZMod 2) =
    Matrix.trace (List.ofFn (fun i : Fin n => matZ2 w (rows i.val))).prod := by
  have hprod : ((List.ofFn (fun i : Fin n => matNat w (rows i.val))).prod).map
      (Nat.castRingHom (ZMod 2)) =
      (List.ofFn (fun i : Fin n => matZ2 w (rows i.val))).prod := by
    have hmap : ∀ (l : List (Matrix (Fin w → Bool) (Fin w → Bool) ℕ)),
        l.prod.map (Nat.castRingHom (ZMod 2)) = (l.map (Matrix.map · (Nat.castRingHom (ZMod 2)))).prod := by
      intro l
      induction l with
      | nil =>
        simp [Matrix.map_one]
      | cons M Ms ih =>
        rw [List.prod_cons, List.map_cons, List.prod_cons, Matrix.map_mul, ih]
    rw [hmap, List.map_ofFn]
    rfl
  rw [← hprod]
  simp [Matrix.trace, Matrix.diag]

def batchDiag {w slots : ℕ} (eD : Fin (2 ^ w) ≃ (Fin w → Bool)) (passId : ℕ)
    (M : Fin slots → (Fin w → Bool) → ZMod 2) : ZMod 2 :=
  ∑ j : Fin slots, if h : passId * slots + j.val < 2 ^ w then M j (eD ⟨passId * slots + j.val, h⟩) else 0

lemma sum_batches_eq_trace {w p : ℕ} (hp : 0 < p) (eD : Fin (2 ^ w) ≃ (Fin w → Bool))
    (A : Matrix (Fin w → Bool) (Fin w → Bool) (ZMod 2)) :
    let slots := (2 ^ w + p - 1) / p
    ∑ passId ∈ Finset.range p,
      ∑ j : Fin slots,
        (if h : passId * slots + j.val < 2 ^ w then
          A (eD ⟨passId * slots + j.val, h⟩) (eD ⟨passId * slots + j.val, h⟩) else 0) =
    Matrix.trace A := by
  intro slots
  have hcov : 2 ^ w ≤ p * slots := by
    have hdm := Nat.div_add_mod (2 ^ w + p - 1) p
    have hml := Nat.mod_lt (2 ^ w + p - 1) hp
    dsimp only [slots]
    omega
  rw [Matrix.trace, ← eD.sum_comp]
  let g : ℕ → ZMod 2 := fun k =>
    if h : k < 2 ^ w then A (eD ⟨k, h⟩) (eD ⟨k, h⟩) else 0
  have hsum_prod : ∑ passId ∈ Finset.range p,
      ∑ j : Fin slots, g (passId * slots + j.val) =
      ∑ k ∈ Finset.range (p * slots), g k := by
    have hsplit : ∀ m : ℕ,
        ∑ passId ∈ Finset.range m, ∑ j : Fin slots, g (passId * slots + j.val) =
        ∑ k ∈ Finset.range (m * slots), g k := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]
        congr 1
        exact Fin.sum_univ_eq_sum_range (fun x => g (m * slots + x)) slots
    exact hsplit p
  change ∑ passId ∈ Finset.range p, ∑ j : Fin slots, g (passId * slots + j.val) = _
  rw [hsum_prod]
  have hsub : Finset.range (2 ^ w) ⊆ Finset.range (p * slots) := Finset.range_mono hcov
  rw [← Finset.sum_subset hsub]
  · symm
    have hdiag : (∑ i : Fin (2 ^ w), A.diag (eD i)) = ∑ i : Fin (2 ^ w), g i.val := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Matrix.diag, g, i.isLt, ↓reduceDIte]
    rw [hdiag, Fin.sum_univ_eq_sum_range g (2 ^ w)]
  · intro k _ hk
    simp only [g, Finset.mem_range] at hk ⊢
    simp [hk]

lemma main_proof (n w p : ℕ) (hn : 0 < n) (hw : 0 < w) (hp : 0 < p) :
    let D := 2 ^ w
    let slots := (D + p - 1) / p
    let Row := ℕ → Bool
    let parity := fun (rows : ℕ → Row) =>
      ((List.range (2 ^ n)).filter (fun word => (List.range n).all (fun site =>
        let pat := (List.range (w + 1)).foldl (fun (acc bit : ℕ) =>
          acc ||| ((word.testBit ((site + bit) % n)).toNat <<< bit)) 0
        rows site pat))).length.testBit 0
    let run := fun (S : ℕ) (start : Fin S)
        (step : ℕ → ℕ → Fin S → Row → Fin S) (table : ℕ → Row) =>
      (List.range p).foldl (fun prev passId =>
        (List.range n).foldl (fun state siteId => step passId siteId state (table siteId)) prev) start
    let S := 2 ^ (D * slots + 1)
    ∃ (start : Fin S) (step : ℕ → ℕ → Fin S → Row → Fin S) (answer : Fin S → Bool),
      ∀ input : ℕ → Row, answer (run S start step input) = parity input := by
  classical
  dsimp only
  let D := 2 ^ w
  let slots := (D + p - 1) / p
  let S := 2 ^ (D * slots + 1)
  let State := ZMod 2 × (Fin slots → (Fin w → Bool) → ZMod 2)
  have hcardState : Fintype.card State = S := by
    simp [State, S, D, Fintype.card_prod, ZMod.card, pow_mul, mul_comm, pow_succ]
  let eS : State ≃ Fin S := Fintype.equivFinOfCardEq hcardState
  let eD : Fin D ≃ (Fin w → Bool) :=
    (Fintype.equivFinOfCardEq (by simp [D] : Fintype.card (Fin w → Bool) = D)).symm
  let initBatch : ℕ → Fin slots → (Fin w → Bool) → ZMod 2 :=
    fun passId j => initVec eD (passId * slots + j.val)
  let startState : State := (0, initBatch 0)
  let stepState : ℕ → ℕ → State → (ℕ → Bool) → State := fun passId siteId st r =>
    let M' : Fin slots → (Fin w → Bool) → ZMod 2 := fun j => mulVecZ2 w (st.2 j) r
    if siteId + 1 = n then
      (st.1 + batchDiag eD passId M', initBatch (passId + 1))
    else
      (st.1, M')
  let start : Fin S := eS startState
  let step : ℕ → ℕ → Fin S → (ℕ → Bool) → Fin S :=
    fun passId siteId st r => eS (stepState passId siteId (eS.symm st) r)
  let answer : Fin S → Bool := fun st => z2ToBool (eS.symm st).1
  refine ⟨start, step, answer, ?_⟩
  intro input
  have hsim_inner : ∀ (passId k : ℕ) (st : State),
      eS.symm ((List.range k).foldl (fun state siteId => step passId siteId state (input siteId)) (eS st)) =
      (List.range k).foldl (fun state siteId => stepState passId siteId state (input siteId)) st := by
    intro passId k st
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      dsimp only [step]
      rw [eS.symm_apply_apply, ih]
  have hsim_outer : ∀ (k : ℕ),
      eS.symm ((List.range k).foldl (fun prev passId =>
        (List.range n).foldl (fun state siteId => step passId siteId state (input siteId)) prev) start) =
      (List.range k).foldl (fun prev passId =>
        (List.range n).foldl (fun state siteId => stepState passId siteId state (input siteId)) prev) startState := by
    intro k
    induction k with
    | zero => simp [start]
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      have h1 : (List.range k).foldl (fun prev passId =>
          (List.range n).foldl (fun state siteId => step passId siteId state (input siteId)) prev) start =
          eS ((List.range k).foldl (fun prev passId =>
          (List.range n).foldl (fun state siteId => stepState passId siteId state (input siteId)) prev) startState) := by
        rw [← ih, eS.apply_symm_apply]
      rw [h1]
      exact hsim_inner k n _
  have hpass_lt : ∀ (passId k : ℕ) (hk : k < n) (acc : ZMod 2) (M0 : Fin slots → (Fin w → Bool) → ZMod 2),
      (List.range k).foldl (fun st siteId => stepState passId siteId st (input siteId)) (acc, M0) =
      (acc, fun j => (List.range k).foldl (fun cur siteId => mulVecZ2 w cur (input siteId)) (M0 j)) := by
    intro passId k hk acc M0
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega)]
      dsimp only [stepState]
      rw [if_neg (by omega)]
      congr 1
      funext j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  let A : Matrix (Fin w → Bool) (Fin w → Bool) (ZMod 2) :=
    (List.ofFn (fun i : Fin n => matZ2 w (input i.val))).prod
  have hpass_full : ∀ (passId : ℕ) (acc : ZMod 2),
      (List.range n).foldl (fun st siteId => stepState passId siteId st (input siteId)) (acc, initBatch passId) =
      (acc + ∑ j : Fin slots,
        (if h : passId * slots + j.val < D then
          A (eD ⟨passId * slots + j.val, h⟩) (eD ⟨passId * slots + j.val, h⟩) else 0),
        initBatch (passId + 1)) := by
    intro passId acc
    have hn1 : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hn1, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hpass_lt passId (n - 1) (by omega) acc (initBatch passId)]
    dsimp only [stepState]
    rw [if_pos (by omega)]
    congr 1
    congr 1
    unfold batchDiag
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with h
    · dsimp only
      have hvec : mulVecZ2 w ((List.range (n - 1)).foldl
          (fun cur siteId => mulVecZ2 w cur (input siteId)) (initBatch passId j)) (input (n - 1)) =
        (List.range n).foldl (fun cur siteId => mulVecZ2 w cur (input siteId)) (initBatch passId j) := by
        conv_rhs => rw [hn1, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hvec, foldl_mulVecZ2]
      dsimp only [initBatch, A]
      rw [initVec_vecMul, dif_pos h]
    · rfl
  have hpasses : ∀ (k : ℕ),
      (List.range k).foldl (fun prev passId =>
        (List.range n).foldl (fun st siteId => stepState passId siteId st (input siteId)) prev) startState =
      (∑ passId ∈ Finset.range k, ∑ j : Fin slots,
        (if h : passId * slots + j.val < D then
          A (eD ⟨passId * slots + j.val, h⟩) (eD ⟨passId * slots + j.val, h⟩) else 0),
        initBatch k) := by
    intro k
    induction k with
    | zero => simp [startState]
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, hpass_full,
        Finset.sum_range_succ]
  dsimp only [answer]
  rw [hsim_outer p, hpasses p]
  dsimp only
  rw [sum_batches_eq_trace hp eD A]
  dsimp only [A]
  rw [← trace_mod2 n w input, ← testBit_zero_eq_z2ToBool, filter_length_eq_trace n w hn input]

end PEqualNP.Outside.L_clb_087

theorem PEqualNP.Outside.L_clb_087 : (∀ (n w p : Nat), 0 < n → 0 < w → 0 < p →
  let D := 2^w
  let slots := (D+p-1)/p
  let Row := Nat → Bool
  let parity := fun (rows : Nat → Row) =>
    ((List.range (2^n)).filter (fun word => (List.range n).all (fun site =>
      let pat := (List.range (w+1)).foldl (fun (acc bit : Nat) =>
        acc ||| ((word.testBit ((site+bit)%n)).toNat <<< bit)) 0
      rows site pat))).length.testBit 0
  let run := fun (S : Nat) (start : Fin S)
      (step : Nat → Nat → Fin S → Row → Fin S) (table : Nat → Row) =>
    (List.range p).foldl (fun prev passId =>
      (List.range n).foldl (fun state siteId => step passId siteId state (table siteId)) prev) start
  let S := 2^(D*slots+1)
  ∃ (start : Fin S) (step : Nat → Nat → Fin S → Row → Fin S) (answer : Fin S → Bool),
    ∀ input : Nat → Row, answer (run S start step input) = parity input) :=
  PEqualNP.Outside.L_clb_087.main_proof
