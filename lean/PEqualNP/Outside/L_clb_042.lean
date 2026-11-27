import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_042

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_stepW_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl stepW acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

private lemma foldl_stepW_getD_lt (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < acc.length) :
    (gs.foldl stepW acc).getD j false = acc.getD j false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepW acc g) (by simp [stepW]; omega)]
    rw [stepW, List.getD_append _ _ _ _ hj]

private lemma getD_snoc_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp

private lemma stepW_getD_len (l : List Bool) (g : Gate) :
    (stepW l g).getD l.length false = g.op.eval (g.inputs.map fun i => l.getD i false) := by
  simp [stepW]

private lemma stepW_getD_lt (l : List Bool) (g : Gate) (i : ℕ) (hi : i < l.length) :
    (stepW l g).getD i false = l.getD i false := by
  rw [stepW, List.getD_append _ _ _ _ hi]

private lemma testBit_add_mul_two_pow (a b m k : ℕ) (ha : a < 2 ^ m) :
    (a + b * 2 ^ m).testBit k = if k < m then a.testBit k else b.testBit (k - m) := by
  split_ifs with hkm
  · have h1 : ((a + b * 2 ^ m) % 2 ^ m).testBit k = (a + b * 2 ^ m).testBit k := by
      rw [Nat.testBit_mod_two_pow, decide_eq_true hkm, Bool.true_and]
    rw [← h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  · simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
    have hpow : 2 ^ k = 2 ^ m * 2 ^ (k - m) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    rw [hpow, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos m),
      Nat.div_eq_of_lt ha, Nat.zero_add]

private lemma bits_sum_spec (g : ℕ → Bool) (m : ℕ) :
    (∑ k ∈ Finset.range m, if g k then 2 ^ k else 0) < 2 ^ m ∧
    ∀ j < m, (∑ k ∈ Finset.range m, if g k then 2 ^ k else 0).testBit j = g j := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨hlt, htb⟩ := ih
    rw [Finset.sum_range_succ]
    set s := ∑ k ∈ Finset.range m, if g k then 2 ^ k else 0
    constructor
    · split_ifs <;> simp only [Nat.pow_succ] <;> omega
    · intro j hj
      split_ifs with hg
      · rw [show 2 ^ m = 1 * 2 ^ m by omega, testBit_add_mul_two_pow s 1 m j hlt]
        split_ifs with hjm
        · exact htb j hjm
        · have heq : j = m := by omega
          subst heq
          simp [hg]
      · simp only [Nat.add_zero]
        by_cases hjm : j < m
        · exact htb j hjm
        · have heq : j = m := by omega
          subst heq
          rw [Nat.testBit_lt_two_pow hlt]
          cases hgj : g j
          · rfl
          · exact absurd hgj hg

private lemma and_eval_two (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

private lemma or_eval_two (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

private def initWire (I S s0 u : ℕ) : ℕ :=
  if s0 = u then I else I + 1

private def layerWire (I S : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, s0, u => initWire I S s0 u
  | t + 1, s0, u => I + 2 + 3 * (t * (S * S) + (s0 * S + u)) + 2

private lemma layerWire_lt (I S t s0 u : ℕ) (hs0 : s0 < S) (hu : u < S) :
    layerWire I S t s0 u < I + 2 + 3 * (t * (S * S)) := by
  cases t with
  | zero =>
    simp only [layerWire, initWire]
    split_ifs <;> omega
  | succ t =>
    simp only [layerWire]
    have hidx : s0 * S + u < S * S := by
      have h1 : (s0 + 1) * S ≤ S * S := Nat.mul_le_mul_right S hs0
      rw [Nat.succ_mul] at h1
      omega
    have hmul : (t + 1) * (S * S) = t * (S * S) + S * S := Nat.succ_mul t (S * S)
    omega

private def cellGates (I S t s0 dst : ℕ) : List Gate :=
  let B := I + 2 + 3 * (t * (S * S) + (s0 * S + dst))
  let w0 := layerWire I S t s0 ((2 * dst) % S)
  let w1 := layerWire I S t s0 ((2 * dst + 1) % S)
  let in0 := t * (2 * S) + 2 * dst
  let in1 := t * (2 * S) + (2 * dst + 1)
  [⟨.and, [w0, in0]⟩, ⟨.and, [w1, in1]⟩, ⟨.or, [B, B + 1]⟩]

private def rowGates (I S t s0 : ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 => rowGates I S t s0 k ++ cellGates I S t s0 k

private def layerGatesAux (I S t : ℕ) : ℕ → List Gate
  | 0 => []
  | r + 1 => layerGatesAux I S t r ++ rowGates I S t r S

private def layerGates (I S t : ℕ) : List Gate :=
  layerGatesAux I S t S

private def propGates (I S : ℕ) : ℕ → List Gate
  | 0 => []
  | t + 1 => propGates I S t ++ layerGates I S t

private def diagGates (I S n : ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 =>
    let base := I + 2 + 3 * (n * (S * S))
    let acc := if k = 0 then I + 1 else base + k - 1
    diagGates I S n k ++ [⟨.or, [acc, layerWire I S n k k]⟩]

private def diagOut (I S n : ℕ) : ℕ → ℕ
  | 0 => I + 1
  | k + 1 => I + 2 + 3 * (n * (S * S)) + k

private def constGates : List Gate :=
  [⟨.and, []⟩, ⟨.or, []⟩]

private def buildCircuit (n w : ℕ) : Circuit :=
  let S := 2 ^ w
  let I := n * 2 ^ (w + 1)
  let gs := constGates ++ propGates I S n ++ diagGates I S n S
  ⟨gs, diagOut I S n S⟩

private lemma rowGates_len (I S t s0 k : ℕ) : (rowGates I S t s0 k).length = 3 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rowGates, cellGates, List.length_append, List.length_cons, List.length_nil, ih]
    omega

private lemma layerGatesAux_len (I S t r : ℕ) : (layerGatesAux I S t r).length = 3 * (r * S) := by
  induction r with
  | zero => simp [layerGatesAux]
  | succ r ih =>
    simp only [layerGatesAux, List.length_append, rowGates_len, ih, Nat.succ_mul]
    omega

private lemma layerGates_len (I S t : ℕ) : (layerGates I S t).length = 3 * (S * S) :=
  layerGatesAux_len I S t S

private lemma propGates_len (I S t : ℕ) : (propGates I S t).length = 3 * (t * (S * S)) := by
  induction t with
  | zero => simp [propGates]
  | succ t ih =>
    simp only [propGates, List.length_append, layerGates_len, ih, Nat.succ_mul]
    omega

private lemma diagGates_len (I S n k : ℕ) : (diagGates I S n k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [diagGates, ih]

private lemma buildCircuit_size (n w : ℕ) :
    (buildCircuit n w).size ≤ 3 * n * 4 ^ w + 2 ^ w + 2 := by
  simp only [buildCircuit, Circuit.size, List.length_append, constGates, List.length_cons,
    List.length_nil, propGates_len, diagGates_len]
  have h4 : 2 ^ w * 2 ^ w = 4 ^ w := by
    rw [← Nat.mul_pow]
  rw [h4, ← Nat.mul_assoc]
  omega

private lemma cellGates_mono (I S t s0 dst : ℕ) (g : Gate) (hg : g ∈ cellGates I S t s0 dst) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  simp only [cellGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

private lemma rowGates_mono (I S t s0 k : ℕ) (g : Gate) (hg : g ∈ rowGates I S t s0 k) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction k with
  | zero => simp [rowGates] at hg
  | succ k ih =>
    rw [rowGates, List.mem_append] at hg
    rcases hg with hg | hg
    · exact ih hg
    · exact cellGates_mono _ _ _ _ _ _ hg

private lemma layerGatesAux_mono (I S t r : ℕ) (g : Gate) (hg : g ∈ layerGatesAux I S t r) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction r with
  | zero => simp [layerGatesAux] at hg
  | succ r ih =>
    rw [layerGatesAux, List.mem_append] at hg
    rcases hg with hg | hg
    · exact ih hg
    · exact rowGates_mono _ _ _ _ _ _ hg

private lemma propGates_mono (I S t : ℕ) (g : Gate) (hg : g ∈ propGates I S t) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction t with
  | zero => simp [propGates] at hg
  | succ t ih =>
    rw [propGates, List.mem_append] at hg
    rcases hg with hg | hg
    · exact ih hg
    · exact layerGatesAux_mono _ _ _ _ _ hg

private lemma diagGates_mono (I S n k : ℕ) (g : Gate) (hg : g ∈ diagGates I S n k) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction k with
  | zero => simp [diagGates] at hg
  | succ k ih =>
    rw [diagGates, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact ih hg
    · simp

private lemma buildCircuit_mono (n w : ℕ) : Monotone2 (buildCircuit n w) := by
  intro g hg
  simp only [buildCircuit, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · simp only [constGates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp
  · exact propGates_mono _ _ _ _ hg
  · exact diagGates_mono _ _ _ _ _ hg

private lemma rb_append {I : ℕ} {a b : List Gate}
    (ha : ∀ j < a.length, ∀ i ∈ (a.getD j ⟨.or, []⟩).inputs, i < I + j)
    (hb : ∀ j < b.length, ∀ i ∈ (b.getD j ⟨.or, []⟩).inputs, i < I + a.length + j) :
    ∀ j < (a ++ b).length, ∀ i ∈ ((a ++ b).getD j ⟨.or, []⟩).inputs, i < I + j := by
  intro j hj i hi
  by_cases hja : j < a.length
  · rw [List.getD_append _ _ _ _ hja] at hi
    exact ha j hja i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    have hj' : j - a.length < b.length := by simp at hj; omega
    have := hb (j - a.length) hj' i hi
    omega

private lemma rb_cellGates (I S t s0 dst : ℕ) (hS : 0 < S) (hs0 : s0 < S) (hdst : dst < S)
    (htI : t * (2 * S) + (2 * dst + 1) < I) :
    ∀ j < (cellGates I S t s0 dst).length,
      ∀ i ∈ ((cellGates I S t s0 dst).getD j ⟨.or, []⟩).inputs,
        i < I + 2 + 3 * (t * (S * S) + (s0 * S + dst)) + j := by
  intro j hj i hi
  have hj3 : j < 3 := by simpa [cellGates] using hj
  have hw0 : layerWire I S t s0 ((2 * dst) % S) < I + 2 + 3 * (t * (S * S)) :=
    layerWire_lt I S t s0 _ hs0 (Nat.mod_lt _ hS)
  have hw1 : layerWire I S t s0 ((2 * dst + 1) % S) < I + 2 + 3 * (t * (S * S)) :=
    layerWire_lt I S t s0 _ hs0 (Nat.mod_lt _ hS)
  interval_cases j
  · simp only [cellGates, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega
  · simp only [cellGates, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega
  · simp only [cellGates, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega

private lemma rb_rowGates (I S t s0 k : ℕ) (hS : 0 < S) (hs0 : s0 < S) (hk : k ≤ S)
    (htI : (t + 1) * (2 * S) ≤ I) :
    ∀ j < (rowGates I S t s0 k).length,
      ∀ i ∈ ((rowGates I S t s0 k).getD j ⟨.or, []⟩).inputs,
        i < I + 2 + 3 * (t * (S * S) + s0 * S) + j := by
  induction k with
  | zero => intro j hj; simp [rowGates] at hj
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 := rb_cellGates I S t s0 k hS hs0 (by omega) (by
      have : (t + 1) * (2 * S) = t * (2 * S) + 2 * S := Nat.succ_mul t (2 * S)
      omega)
    have h3 : ∀ j < (cellGates I S t s0 k).length,
        ∀ i ∈ ((cellGates I S t s0 k).getD j ⟨.or, []⟩).inputs,
          i < I + 2 + 3 * (t * (S * S) + s0 * S) + (rowGates I S t s0 k).length + j := by
      intro j hj i hi
      rw [rowGates_len]
      have := h2 j hj i hi
      omega
    exact rb_append (I := I + 2 + 3 * (t * (S * S) + s0 * S)) h1 h3

private lemma rb_layerGatesAux (I S t r : ℕ) (hS : 0 < S) (hr : r ≤ S)
    (htI : (t + 1) * (2 * S) ≤ I) :
    ∀ j < (layerGatesAux I S t r).length,
      ∀ i ∈ ((layerGatesAux I S t r).getD j ⟨.or, []⟩).inputs,
        i < I + 2 + 3 * (t * (S * S)) + j := by
  induction r with
  | zero => intro j hj; simp [layerGatesAux] at hj
  | succ r ih =>
    have h1 := ih (by omega)
    have h2 := rb_rowGates I S t r S hS (by omega) le_rfl htI
    have h3 : ∀ j < (rowGates I S t r S).length,
        ∀ i ∈ ((rowGates I S t r S).getD j ⟨.or, []⟩).inputs,
          i < I + 2 + 3 * (t * (S * S)) + (layerGatesAux I S t r).length + j := by
      intro j hj i hi
      rw [layerGatesAux_len]
      have := h2 j hj i hi
      omega
    exact rb_append (I := I + 2 + 3 * (t * (S * S))) h1 h3

private lemma rb_propGates (I S t : ℕ) (hS : 0 < S) (htI : t * (2 * S) ≤ I) :
    ∀ j < (propGates I S t).length,
      ∀ i ∈ ((propGates I S t).getD j ⟨.or, []⟩).inputs,
        i < I + 2 + j := by
  induction t with
  | zero => intro j hj; simp [propGates] at hj
  | succ t ih =>
    have h1 := ih (by
      have : (t + 1) * (2 * S) = t * (2 * S) + 2 * S := Nat.succ_mul t (2 * S)
      omega)
    have h2 := rb_layerGatesAux I S t S hS le_rfl htI
    have h3 : ∀ j < (layerGates I S t).length,
        ∀ i ∈ ((layerGates I S t).getD j ⟨.or, []⟩).inputs,
          i < I + 2 + (propGates I S t).length + j := by
      intro j hj i hi
      rw [propGates_len]
      exact h2 j hj i hi
    exact rb_append (I := I + 2) h1 h3

private lemma rb_diagGates (I S n k : ℕ) (hk : k ≤ S) :
    ∀ j < (diagGates I S n k).length,
      ∀ i ∈ ((diagGates I S n k).getD j ⟨.or, []⟩).inputs,
        i < I + 2 + 3 * (n * (S * S)) + j := by
  induction k with
  | zero => intro j hj; simp [diagGates] at hj
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 : ∀ j < ([⟨.or, [if k = 0 then I + 1 else I + 2 + 3 * (n * (S * S)) + k - 1,
        layerWire I S n k k]⟩] : List Gate).length,
        ∀ i ∈ (([⟨.or, [if k = 0 then I + 1 else I + 2 + 3 * (n * (S * S)) + k - 1,
          layerWire I S n k k]⟩] : List Gate).getD j ⟨.or, []⟩).inputs,
          i < I + 2 + 3 * (n * (S * S)) + (diagGates I S n k).length + j := by
      intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [diagGates_len]
      simp only [List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · split_ifs <;> omega
      · have := layerWire_lt I S n k k (by omega) (by omega)
        omega
    exact rb_append (I := I + 2 + 3 * (n * (S * S))) h1 h2

private lemma buildCircuit_readsBack (n w : ℕ) :
    ReadsBack (n * 2 ^ (w + 1)) (buildCircuit n w) := by
  set S := 2 ^ w
  set I := n * 2 ^ (w + 1)
  have hS : 0 < S := Nat.two_pow_pos w
  have hI : n * (2 * S) = I := by
    simp only [I, S, Nat.pow_succ, Nat.mul_comm 2]
  have hconst : ∀ j < constGates.length, ∀ i ∈ (constGates.getD j ⟨.or, []⟩).inputs, i < I + j := by
    intro j hj i hi
    have hj2 : j < 2 := by simpa [constGates] using hj
    interval_cases j <;> simp [constGates] at hi
  have hcp := rb_append (I := I) hconst (by
    intro j hj i hi
    simpa [constGates] using rb_propGates I S n hS (by omega) j hj i hi)
  have hall := rb_append (I := I) hcp (by
    intro j hj i hi
    have hlen : (constGates ++ propGates I S n).length = 2 + 3 * (n * (S * S)) := by
      simp only [List.length_append, constGates, List.length_cons, List.length_nil, propGates_len]
    rw [hlen]
    have := rb_diagGates I S n S le_rfl j hj i hi
    omega)
  intro j hj i hi
  have hget : gateAt (buildCircuit n w) j = (buildCircuit n w).gates.getD j ⟨.or, []⟩ := by
    simp only [gateAt, List.getD_eq_getElem?_getD]
  rw [hget] at hi
  exact hall j hj i hi

private def tableAt (n w : ℕ) (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (t pat : ℕ) : Bool :=
  table ⟨t % n, Nat.mod_lt _ hn⟩ (fun bit => pat.testBit bit.val)

private def dp (n w : ℕ) (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool) :
    ℕ → ℕ → ℕ → Bool
  | 0, s0, u => decide (s0 = u)
  | t + 1, s0, dst =>
    let S := 2 ^ w
    (dp n w hn table t s0 ((2 * dst) % S) && tableAt n w hn table t (2 * dst)) ||
    (dp n w hn table t s0 ((2 * dst + 1) % S) && tableAt n w hn table t (2 * dst + 1))

private lemma input_getD (n w : ℕ) (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (t pat : ℕ) (ht : t < n) (hpat : pat < 2 ^ (w + 1)) :
    let I := n * 2 ^ (w + 1)
    let inputs := List.ofFn (fun j : Fin I =>
      table ⟨(j.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩ (fun bit => j.val.testBit bit.val))
    inputs.getD (t * 2 ^ (w + 1) + pat) false = tableAt n w hn table t pat := by
  intro I inputs
  have hlt : t * 2 ^ (w + 1) + pat < I := by
    have h1 : (t + 1) * 2 ^ (w + 1) ≤ n * 2 ^ (w + 1) := Nat.mul_le_mul_right _ ht
    rw [Nat.succ_mul] at h1
    omega
  have hlen : inputs.length = I := by simp [inputs]
  rw [List.getD_eq_getElem _ _ (by omega)]
  simp only [inputs, List.getElem_ofFn, tableAt]
  congr 1
  · ext
    have hdiv : (t * 2 ^ (w + 1) + pat) / 2 ^ (w + 1) = t := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos (w + 1)),
        Nat.div_eq_of_lt hpat, Nat.zero_add]
    rw [hdiv]
  · funext bit
    have hbit : bit.val < w + 1 := bit.isLt
    rw [Nat.add_comm, testBit_add_mul_two_pow pat t (w + 1) bit.val hpat, if_pos hbit]

private lemma eval_cellGates (n w : ℕ) (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (t s0 dst : ℕ) (ht : t < n) (hs0 : s0 < 2 ^ w) (hdst : dst < 2 ^ w) (acc : List Bool)
    (hacc_len : acc.length = n * 2 ^ (w + 1) + 2 + 3 * (t * (2 ^ w * 2 ^ w) + (s0 * 2 ^ w + dst)))
    (hinp : ∀ p < 2 ^ (w + 1), acc.getD (t * (2 * 2 ^ w) + p) false = tableAt n w hn table t p)
    (hprev : ∀ u < 2 ^ w, acc.getD (layerWire (n * 2 ^ (w + 1)) (2 ^ w) t s0 u) false =
      dp n w hn table t s0 u) :
    ((cellGates (n * 2 ^ (w + 1)) (2 ^ w) t s0 dst).foldl stepW acc).getD
      (layerWire (n * 2 ^ (w + 1)) (2 ^ w) (t + 1) s0 dst) false =
      dp n w hn table (t + 1) s0 dst := by
  set S := 2 ^ w
  set I := n * 2 ^ (w + 1)
  set B := I + 2 + 3 * (t * (S * S) + (s0 * S + dst))
  have hS : 0 < S := Nat.two_pow_pos w
  have hw0_lt : layerWire I S t s0 ((2 * dst) % S) < B := by
    have := layerWire_lt I S t s0 ((2 * dst) % S) hs0 (Nat.mod_lt _ hS)
    omega
  have hw1_lt : layerWire I S t s0 ((2 * dst + 1) % S) < B := by
    have := layerWire_lt I S t s0 ((2 * dst + 1) % S) hs0 (Nat.mod_lt _ hS)
    omega
  have hin0_lt : t * (2 * S) + 2 * dst < B := by
    have h1 : (t + 1) * (2 * S) ≤ I := by
      have : (t + 1) * 2 ^ (w + 1) ≤ n * 2 ^ (w + 1) := Nat.mul_le_mul_right _ ht
      simpa [I, S, Nat.pow_succ, Nat.mul_comm 2] using this
    have : (t + 1) * (2 * S) = t * (2 * S) + 2 * S := Nat.succ_mul t (2 * S)
    omega
  have hin1_lt : t * (2 * S) + (2 * dst + 1) < B := by
    have h1 : (t + 1) * (2 * S) ≤ I := by
      have : (t + 1) * 2 ^ (w + 1) ≤ n * 2 ^ (w + 1) := Nat.mul_le_mul_right _ ht
      simpa [I, S, Nat.pow_succ, Nat.mul_comm 2] using this
    have : (t + 1) * (2 * S) = t * (2 * S) + 2 * S := Nat.succ_mul t (2 * S)
    omega
  simp only [cellGates, List.foldl_cons, List.foldl_nil, layerWire]
  set acc1 := stepW acc ⟨.and, [layerWire I S t s0 ((2 * dst) % S), t * (2 * S) + 2 * dst]⟩
  set acc2 := stepW acc1 ⟨.and, [layerWire I S t s0 ((2 * dst + 1) % S), t * (2 * S) + (2 * dst + 1)]⟩
  have hl1 : acc1.length = B + 1 := by simp [acc1, stepW, hacc_len, B]
  have hl2 : acc2.length = B + 2 := by simp [acc2, stepW, hl1]
  have hv1 : acc1.getD B false =
      (dp n w hn table t s0 ((2 * dst) % S) && tableAt n w hn table t (2 * dst)) := by
    dsimp only [acc1]
    rw [show B = acc.length from hacc_len.symm, stepW_getD_len]
    simp only [List.map_cons, List.map_nil, and_eval_two]
    rw [hprev _ (Nat.mod_lt _ hS), hinp (2 * dst) (by simp [Nat.pow_succ]; omega)]
  have hv2 : acc2.getD (B + 1) false =
      (dp n w hn table t s0 ((2 * dst + 1) % S) && tableAt n w hn table t (2 * dst + 1)) := by
    dsimp only [acc2]
    rw [show B + 1 = acc1.length from hl1.symm, stepW_getD_len]
    simp only [List.map_cons, List.map_nil, and_eval_two]
    rw [stepW_getD_lt _ _ _ (by omega), stepW_getD_lt _ _ _ (by omega)]
    rw [hprev _ (Nat.mod_lt _ hS), hinp (2 * dst + 1) (by simp [Nat.pow_succ]; omega)]
  have hv1' : acc2.getD B false = acc1.getD B false :=
    stepW_getD_lt _ _ _ (by omega)
  change (stepW acc2 ⟨.or, [B, B + 1]⟩).getD (B + 2) false = _
  rw [show B + 2 = acc2.length from hl2.symm, stepW_getD_len]
  simp only [List.map_cons, List.map_nil, or_eval_two, hv1', hv1, hv2, dp, S]

private lemma eval_rowGates (n w : ℕ) (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (t s0 k : ℕ) (ht : t < n) (hs0 : s0 < 2 ^ w) (hk : k ≤ 2 ^ w) (acc : List Bool)
    (hacc_len : acc.length = n * 2 ^ (w + 1) + 2 + 3 * (t * (2 ^ w * 2 ^ w) + s0 * 2 ^ w))
    (hinp : ∀ p < 2 ^ (w + 1), acc.getD (t * (2 * 2 ^ w) + p) false = tableAt n w hn table t p)
    (hprev : ∀ u < 2 ^ w, acc.getD (layerWire (n * 2 ^ (w + 1)) (2 ^ w) t s0 u) false =
      dp n w hn table t s0 u) :
    ∀ dst < k,
      ((rowGates (n * 2 ^ (w + 1)) (2 ^ w) t s0 k).foldl stepW acc).getD
        (layerWire (n * 2 ^ (w + 1)) (2 ^ w) (t + 1) s0 dst) false =
        dp n w hn table (t + 1) s0 dst := by
  induction k with
  | zero => intro dst hdst; omega
  | succ k ih =>
    intro dst hdst
    rw [rowGates, List.foldl_append]
    set acc1 := (rowGates (n * 2 ^ (w + 1)) (2 ^ w) t s0 k).foldl stepW acc
    have hl1 : acc1.length =
        n * 2 ^ (w + 1) + 2 + 3 * (t * (2 ^ w * 2 ^ w) + (s0 * 2 ^ w + k)) := by
      rw [foldl_stepW_len, hacc_len, rowGates_len]
      omega
    by_cases hlt : dst < k
    · have hwl : layerWire (n * 2 ^ (w + 1)) (2 ^ w) (t + 1) s0 dst < acc1.length := by
        simp only [layerWire, hl1]
        omega
      rw [foldl_stepW_getD_lt _ _ _ hwl]
      exact ih (by omega) dst hlt
    · have heq : dst = k := by omega
      subst heq
      have hinp1 : ∀ p < 2 ^ (w + 1),
          acc1.getD (t * (2 * 2 ^ w) + p) false = tableAt n w hn table t p := by
        intro p hp
        have hplt : t * (2 * 2 ^ w) + p < acc.length := by
          have h1 : (t + 1) * (2 * 2 ^ w) ≤ n * 2 ^ (w + 1) := by
            have := Nat.mul_le_mul_right (2 ^ (w + 1)) ht
            simpa [Nat.pow_succ, Nat.mul_comm 2] using this
          have : (t + 1) * (2 * 2 ^ w) = t * (2 * 2 ^ w) + 2 * 2 ^ w := Nat.succ_mul t _
          have : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
          omega
        rw [foldl_stepW_getD_lt _ _ _ hplt, hinp p hp]
      have hprev1 : ∀ u < 2 ^ w,
          acc1.getD (layerWire (n * 2 ^ (w + 1)) (2 ^ w) t s0 u) false =
            dp n w hn table t s0 u := by
        intro u hu
        have hult : layerWire (n * 2 ^ (w + 1)) (2 ^ w) t s0 u < acc.length := by
          have := layerWire_lt (n * 2 ^ (w + 1)) (2 ^ w) t s0 u hs0 hu
          omega
        rw [foldl_stepW_getD_lt _ _ _ hult, hprev u hu]
      exact eval_cellGates n w hn table t s0 dst ht hs0 (by omega) acc1 hl1 hinp1 hprev1

private lemma eval_layerGatesAux (n w : ℕ) (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (t r : ℕ) (ht : t < n) (hr : r ≤ 2 ^ w) (acc : List Bool)
    (hacc_len : acc.length = n * 2 ^ (w + 1) + 2 + 3 * (t * (2 ^ w * 2 ^ w)))
    (hinp : ∀ p < 2 ^ (w + 1), acc.getD (t * (2 * 2 ^ w) + p) false = tableAt n w hn table t p)
    (hprev : ∀ s0 < 2 ^ w, ∀ u < 2 ^ w,
      acc.getD (layerWire (n * 2 ^ (w + 1)) (2 ^ w) t s0 u) false = dp n w hn table t s0 u) :
    ∀ s0 < r, ∀ dst < 2 ^ w,
      ((layerGatesAux (n * 2 ^ (w + 1)) (2 ^ w) t r).foldl stepW acc).getD
        (layerWire (n * 2 ^ (w + 1)) (2 ^ w) (t + 1) s0 dst) false =
        dp n w hn table (t + 1) s0 dst := by
  induction r with
  | zero => intro s0 hs0; omega
  | succ r ih =>
    intro s0 hs0 dst hdst
    rw [layerGatesAux, List.foldl_append]
    set acc1 := (layerGatesAux (n * 2 ^ (w + 1)) (2 ^ w) t r).foldl stepW acc
    have hl1 : acc1.length =
        n * 2 ^ (w + 1) + 2 + 3 * (t * (2 ^ w * 2 ^ w) + r * 2 ^ w) := by
      rw [foldl_stepW_len, hacc_len, layerGatesAux_len]
      omega
    by_cases hlt : s0 < r
    · have hwl : layerWire (n * 2 ^ (w + 1)) (2 ^ w) (t + 1) s0 dst < acc1.length := by
        simp only [layerWire, hl1]
        have h1 : (s0 + 1) * 2 ^ w ≤ r * 2 ^ w := Nat.mul_le_mul_right _ hlt
        rw [Nat.succ_mul] at h1
        omega
      rw [foldl_stepW_getD_lt _ _ _ hwl]
      exact ih (by omega) s0 hlt dst hdst
    · have heq : s0 = r := by omega
      subst heq
      have hinp1 : ∀ p < 2 ^ (w + 1),
          acc1.getD (t * (2 * 2 ^ w) + p) false = tableAt n w hn table t p := by
        intro p hp
        have hplt : t * (2 * 2 ^ w) + p < acc.length := by
          have h1 : (t + 1) * (2 * 2 ^ w) ≤ n * 2 ^ (w + 1) := by
            have := Nat.mul_le_mul_right (2 ^ (w + 1)) ht
            simpa [Nat.pow_succ, Nat.mul_comm 2] using this
          have : (t + 1) * (2 * 2 ^ w) = t * (2 * 2 ^ w) + 2 * 2 ^ w := Nat.succ_mul t _
          have : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
          omega
        rw [foldl_stepW_getD_lt _ _ _ hplt, hinp p hp]
      have hprev1 : ∀ u < 2 ^ w,
          acc1.getD (layerWire (n * 2 ^ (w + 1)) (2 ^ w) t s0 u) false =
            dp n w hn table t s0 u := by
        intro u hu
        have hult : layerWire (n * 2 ^ (w + 1)) (2 ^ w) t s0 u < acc.length := by
          have := layerWire_lt (n * 2 ^ (w + 1)) (2 ^ w) t s0 u (by omega) hu
          omega
        rw [foldl_stepW_getD_lt _ _ _ hult, hprev s0 (by omega) u hu]
      exact eval_rowGates n w hn table t s0 (2 ^ w) ht (by omega) le_rfl acc1 hl1 hinp1 hprev1
        dst hdst

private lemma eval_propGates (n w : ℕ) (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (t : ℕ) (ht : t ≤ n) :
    let I := n * 2 ^ (w + 1)
    let inputs := List.ofFn (fun j : Fin I =>
      table ⟨(j.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩ (fun bit => j.val.testBit bit.val))
    let base := constGates.foldl stepW inputs
    ∀ s0 < 2 ^ w, ∀ u < 2 ^ w,
      ((propGates I (2 ^ w) t).foldl stepW base).getD (layerWire I (2 ^ w) t s0 u) false =
        dp n w hn table t s0 u := by
  intro I inputs base
  have hilen : inputs.length = I := by simp [inputs]
  have hblen : base.length = I + 2 := by
    simp [base, constGates, stepW, hilen]
  have hb_true : base.getD I false = true := by
    have h1 : (stepW inputs ⟨.and, []⟩).length = I + 1 := by simp [stepW, hilen]
    have h2 : (stepW inputs ⟨.and, []⟩).getD I false = true := by
      rw [← hilen, stepW_getD_len]
      rfl
    simp only [base, constGates, List.foldl_cons, List.foldl_nil]
    rw [stepW_getD_lt _ _ _ (by omega), h2]
  have hb_false : base.getD (I + 1) false = false := by
    have h1 : (stepW inputs ⟨.and, []⟩).length = I + 1 := by simp [stepW, hilen]
    simp only [base, constGates, List.foldl_cons, List.foldl_nil]
    rw [← h1, stepW_getD_len]
    rfl
  induction t with
  | zero =>
    intro s0 hs0 u hu
    simp only [propGates, List.foldl_nil, layerWire, initWire, dp]
    split_ifs with h
    · rw [hb_true, decide_eq_true h]
    · rw [hb_false, decide_eq_false h]
  | succ t ih =>
    intro s0 hs0 u hu
    rw [propGates, List.foldl_append]
    set acc1 := (propGates I (2 ^ w) t).foldl stepW base
    have hl1 : acc1.length = I + 2 + 3 * (t * (2 ^ w * 2 ^ w)) := by
      rw [foldl_stepW_len, hblen, propGates_len]
    have hinp1 : ∀ p < 2 ^ (w + 1),
        acc1.getD (t * (2 * 2 ^ w) + p) false = tableAt n w hn table t p := by
      intro p hp
      have hpI : t * (2 * 2 ^ w) + p < I := by
        have h1 : (t + 1) * (2 * 2 ^ w) ≤ I := by
          have := Nat.mul_le_mul_right (2 ^ (w + 1)) ht
          simpa [I, Nat.pow_succ, Nat.mul_comm 2] using this
        have : (t + 1) * (2 * 2 ^ w) = t * (2 * 2 ^ w) + 2 * 2 ^ w := Nat.succ_mul t _
        have : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
        omega
      rw [foldl_stepW_getD_lt _ _ _ (by omega)]
      simp only [base]
      rw [foldl_stepW_getD_lt _ _ _ (by omega)]
      have heq : t * (2 * 2 ^ w) + p = t * 2 ^ (w + 1) + p := by
        rw [Nat.pow_succ, Nat.mul_comm 2]
      rw [heq]
      exact input_getD n w hn table t p (by omega) hp
    exact eval_layerGatesAux n w hn table t (2 ^ w) (by omega) le_rfl acc1 hl1 hinp1
      (ih (by omega)) s0 hs0 u hu

private lemma eval_diagGates (n w : ℕ) (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (k : ℕ) (hk : k ≤ 2 ^ w) (acc : List Bool)
    (hacc_len : acc.length = n * 2 ^ (w + 1) + 2 + 3 * (n * (2 ^ w * 2 ^ w)))
    (hfalse : acc.getD (n * 2 ^ (w + 1) + 1) false = false)
    (hdiag : ∀ s0 < 2 ^ w, acc.getD (layerWire (n * 2 ^ (w + 1)) (2 ^ w) n s0 s0) false =
      dp n w hn table n s0 s0) :
    ((diagGates (n * 2 ^ (w + 1)) (2 ^ w) n k).foldl stepW acc).getD
      (diagOut (n * 2 ^ (w + 1)) (2 ^ w) n k) false = true ↔
      ∃ s0 < k, dp n w hn table n s0 s0 = true := by
  set S := 2 ^ w
  set I := n * 2 ^ (w + 1)
  induction k with
  | zero =>
    simp only [diagGates, diagOut, List.foldl_nil, hfalse, Bool.false_eq_true]
    constructor
    · intro h; exact False.elim h
    · rintro ⟨s0, hs0, _⟩; omega
  | succ k ih =>
    rw [diagGates, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set acc1 := (diagGates I S n k).foldl stepW acc
    have hl1 : acc1.length = I + 2 + 3 * (n * (S * S)) + k := by
      rw [foldl_stepW_len, hacc_len, diagGates_len]
    have hdiag_k : acc1.getD (layerWire I S n k k) false = dp n w hn table n k k := by
      have hlt : layerWire I S n k k < acc.length := by
        have := layerWire_lt I S n k k (by omega) (by omega)
        omega
      rw [foldl_stepW_getD_lt _ _ _ hlt, hdiag k (by omega)]
    have hacc_eq : (if k = 0 then I + 1 else acc1.length - 1) =
        diagOut I S n k := by
      rw [hl1]
      cases k <;> simp [diagOut]
    simp only [diagOut]
    rw [show I + 2 + 3 * (n * (S * S)) + k = acc1.length from hl1.symm, stepW_getD_len]
    simp only [List.map_cons, List.map_nil, or_eval_two, hacc_eq, hdiag_k, Bool.or_eq_true]
    rw [ih (by omega)]
    constructor
    · rintro (⟨s0, hs0, hdp⟩ | hkdp)
      · exact ⟨s0, by omega, hdp⟩
      · exact ⟨k, by omega, hkdp⟩
    · rintro ⟨s0, hs0, hdp⟩
      by_cases hlt : s0 < k
      · exact Or.inl ⟨s0, hlt, hdp⟩
      · have : s0 = k := by omega
        subst this
        exact Or.inr hdp

private lemma eval_buildCircuit (n w : ℕ) (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) :
    let I := n * 2 ^ (w + 1)
    let inputs := List.ofFn (fun j : Fin I =>
      table ⟨(j.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩ (fun bit => j.val.testBit bit.val))
    (buildCircuit n w).eval inputs = true ↔ ∃ s0 < 2 ^ w, dp n w hn table n s0 s0 = true := by
  intro I inputs
  set S := 2 ^ w
  have hilen : inputs.length = I := by simp [inputs]
  set base := constGates.foldl stepW inputs
  have hblen : base.length = I + 2 := by simp [base, constGates, stepW, hilen]
  have hb_false : base.getD (I + 1) false = false := by
    have h1 : (stepW inputs ⟨.and, []⟩).length = I + 1 := by simp [stepW, hilen]
    simp only [base, constGates, List.foldl_cons, List.foldl_nil]
    rw [← h1, stepW_getD_len]
    rfl
  set acc := (propGates I S n).foldl stepW base
  have hacc_len : acc.length = I + 2 + 3 * (n * (S * S)) := by
    rw [foldl_stepW_len, hblen, propGates_len]
  have hacc_false : acc.getD (I + 1) false = false := by
    rw [foldl_stepW_getD_lt _ _ _ (by omega), hb_false]
  have hdiag : ∀ s0 < S, acc.getD (layerWire I S n s0 s0) false = dp n w hn table n s0 s0 :=
    fun s0 hs0 => eval_propGates n w hn table n le_rfl s0 hs0 s0 hs0
  have hev : (buildCircuit n w).eval inputs =
      ((diagGates I S n S).foldl stepW acc).getD (diagOut I S n S) false := by
    simp only [Circuit.eval, Circuit.wires, buildCircuit]
    change ((constGates ++ propGates I S n ++ diagGates I S n S).foldl stepW inputs).getD
      (diagOut I S n S) false = _
    rw [List.foldl_append, List.foldl_append]
  rw [hev]
  exact eval_diagGates n w hn table S le_rfl acc hacc_len hacc_false hdiag

private lemma nat_eq_of_testBit_lt {w a b : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : ∀ k < w, a.testBit k = b.testBit k) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < w
  · exact h k hk
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega)))]

private lemma testBit_two_mul_add_bit (dst b k : ℕ) (hb : b < 2) :
    (2 * dst + b).testBit (k + 1) = dst.testBit k := by
  have h : 2 * dst + b = Nat.bit (b = 1) dst := by
    interval_cases b <;> simp [Nat.bit] <;> omega
  rw [h, Nat.testBit_bit_succ]

private lemma testBit_two_mul_add_bit_zero (dst b : ℕ) (hb : b < 2) :
    (2 * dst + b).testBit 0 = decide (b = 1) := by
  have h : 2 * dst + b = Nat.bit (b = 1) dst := by
    interval_cases b <;> simp [Nat.bit] <;> omega
  rw [h, Nat.testBit_bit_zero]

private lemma dp_iff_seq (n w : ℕ) (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) :
    ∀ t ≤ n, ∀ s0 < 2 ^ w, ∀ u < 2 ^ w,
      dp n w hn table t s0 u = true ↔
        ∃ f : ℕ → Bool,
          (∀ k < w, f k = s0.testBit k) ∧
          (∀ k < w, f (t + k) = u.testBit k) ∧
          (∀ i < t, tableAt n w hn table i (∑ k ∈ Finset.range (w + 1), if f (i + k) then 2 ^ k else 0) = true) := by
  have hbits_sum := bits_sum_spec
  intro t
  induction t with
  | zero =>
    intro _ s0 hs0 u hu
    simp only [dp, decide_eq_true_eq]
    constructor
    · rintro rfl
      refine ⟨fun k => s0.testBit k, fun _ _ => rfl, fun _ _ => by simp, fun i hi => by omega⟩
    · rintro ⟨f, hf0, hfu, _⟩
      exact nat_eq_of_testBit_lt hs0 hu (fun k hk => by rw [← hf0 k hk, ← hfu k hk, Nat.zero_add])
  | succ t ih =>
    intro ht s0 hs0 dst hdst
    simp only [dp, Bool.or_eq_true, Bool.and_eq_true]
    constructor
    · intro h
      have hex : ∃ b < 2, dp n w hn table t s0 ((2 * dst + b) % 2 ^ w) = true ∧
          tableAt n w hn table t (2 * dst + b) = true := by
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨0, by omega, by simpa using h1, by simpa using h2⟩
        · exact ⟨1, by omega, h1, h2⟩
      obtain ⟨b, hb, hdp, htab⟩ := hex
      obtain ⟨f, hf0, hfu, hft⟩ := (ih (by omega) s0 hs0 _ (Nat.mod_lt _ (Nat.two_pow_pos w))).mp hdp
      let f' : ℕ → Bool := fun m => if m = t + w then (2 * dst + b).testBit w else f m
      refine ⟨f', ?_, ?_, ?_⟩
      · intro k hk
        simp only [f', show k ≠ t + w by omega, ↓reduceIte]
        exact hf0 k hk
      · intro k hk
        by_cases hkw : k + 1 < w
        · simp only [f', show t + 1 + k ≠ t + w by omega, ↓reduceIte]
          have h1 := hfu (k + 1) hkw
          rw [show t + 1 + k = t + (k + 1) by omega, h1, Nat.testBit_mod_two_pow,
            decide_eq_true hkw, Bool.true_and, testBit_two_mul_add_bit dst b k hb]
        · have heq : k + 1 = w := by omega
          simp only [f', show t + 1 + k = t + w by omega, ↓reduceIte]
          rw [← heq, testBit_two_mul_add_bit dst b k hb]
      · intro i hi
        by_cases hit : i < t
        · have heq : (∑ k ∈ Finset.range (w + 1), if f' (i + k) then 2 ^ k else 0) =
              (∑ k ∈ Finset.range (w + 1), if f (i + k) then 2 ^ k else 0) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mem_range] at hk
            simp only [f', show i + k ≠ t + w by omega, ↓reduceIte]
          rw [heq]
          exact hft i hit
        · have hi_eq : i = t := by omega
          subst hi_eq
          have hsum_eq : (∑ k ∈ Finset.range (w + 1), if f' (i + k) then 2 ^ k else 0) =
              2 * dst + b := by
            have ⟨hlt, htb⟩ := hbits_sum (fun k => f' (i + k)) (w + 1)
            apply nat_eq_of_testBit_lt hlt (by simp [Nat.pow_succ]; omega)
            intro k hk
            rw [htb k hk]
            by_cases hkw : k < w
            · simp only [f', show i + k ≠ i + w by omega, ↓reduceIte]
              rw [hfu k hkw, Nat.testBit_mod_two_pow, decide_eq_true hkw, Bool.true_and]
            · have : k = w := by omega
              subst this
              simp [f']
          rw [hsum_eq]
          exact htab
    · rintro ⟨f, hf0, hfu, hft⟩
      let b : ℕ := if f t then 1 else 0
      have hb : b < 2 := by dsimp [b]; split_ifs <;> omega
      have hpat_eq : (∑ k ∈ Finset.range (w + 1), if f (t + k) then 2 ^ k else 0) = 2 * dst + b := by
        have ⟨hlt, htb⟩ := hbits_sum (fun k => f (t + k)) (w + 1)
        apply nat_eq_of_testBit_lt hlt (by simp [Nat.pow_succ]; omega)
        intro k hk
        rw [htb k hk]
        cases k with
        | zero =>
          rw [testBit_two_mul_add_bit_zero dst b hb, Nat.add_zero]
          dsimp [b]
          by_cases hft0 : f t = true
          · simp [hft0]
          · simp [hft0]
        | succ k =>
          rw [testBit_two_mul_add_bit dst b k hb, show t + (k + 1) = t + 1 + k by omega]
          exact hfu k (by omega)
      have htab : tableAt n w hn table t (2 * dst + b) = true := by
        rw [← hpat_eq]
        exact hft t (by omega)
      have hdp : dp n w hn table t s0 ((2 * dst + b) % 2 ^ w) = true := by
        apply (ih (by omega) s0 hs0 _ (Nat.mod_lt _ (Nat.two_pow_pos w))).mpr
        refine ⟨f, hf0, ?_, fun i hi => hft i (by omega)⟩
        intro k hk
        rw [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and, ← hpat_eq]
        exact ((hbits_sum (fun j => f (t + j)) (w + 1)).2 k (by omega)).symm
      dsimp only [b] at hdp htab
      cases hft0 : f t
      · simp only [hft0, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hdp htab
        exact Or.inl ⟨hdp, htab⟩
      · simp only [hft0, ↓reduceIte] at hdp htab
        exact Or.inr ⟨hdp, htab⟩

private lemma periodic_eq_mod {n w : ℕ} (hn : 0 < n) (f : ℕ → Bool)
    (hper : ∀ k < w, f (n + k) = f k) : ∀ m < n + w, f m = f (m % n) := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro hm
    by_cases hmn : m < n
    · rw [Nat.mod_eq_of_lt hmn]
    · have hk : m - n < w := by omega
      have h1 : f m = f (m - n) := by
        have := hper (m - n) hk
        rw [show n + (m - n) = m by omega] at this
        exact this
      rw [h1, ih (m - n) (by omega) (by omega)]
      congr 1
      rw [← Nat.add_mod_right (m - n) n, Nat.sub_add_cancel (by omega)]

private lemma dp_diag_iff_word (n w : ℕ) (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) :
    (∃ s0 < 2 ^ w, dp n w hn table n s0 s0 = true) ↔
      ∃ word : Fin n → Bool, ∀ i : Fin n,
        table i (fun bit => word ⟨(i.val + bit.val) % n, Nat.mod_lt _ hn⟩) = true := by
  have hbits_sum := bits_sum_spec
  constructor
  · rintro ⟨s0, hs0, hdp⟩
    obtain ⟨f, hf0, hfn, hft⟩ := (dp_iff_seq n w hn table n le_rfl s0 hs0 s0 hs0).mp hdp
    have hper : ∀ k < w, f (n + k) = f k := fun k hk => (hfn k hk).trans (hf0 k hk).symm
    have hmod := periodic_eq_mod hn f hper
    refine ⟨fun i => f i.val, ?_⟩
    intro i
    have hi := hft i.val i.isLt
    simp only [tableAt] at hi
    have himod : (⟨i.val % n, Nat.mod_lt _ hn⟩ : Fin n) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    rw [himod] at hi
    convert hi using 2
    funext bit
    rw [(hbits_sum (fun k => f (i.val + k)) (w + 1)).2 bit.val bit.isLt]
    exact (hmod (i.val + bit.val) (by omega)).symm
  · rintro ⟨word, hword⟩
    let f : ℕ → Bool := fun m => word ⟨m % n, Nat.mod_lt _ hn⟩
    let s0 : ℕ := ∑ k ∈ Finset.range w, if f k then 2 ^ k else 0
    have ⟨hs0, htb0⟩ := hbits_sum f w
    refine ⟨s0, hs0, (dp_iff_seq n w hn table n le_rfl s0 hs0 s0 hs0).mpr ?_⟩
    refine ⟨f, fun k hk => (htb0 k hk).symm, ?_, ?_⟩
    · intro k hk
      rw [htb0 k hk]
      simp only [f, Nat.add_mod_left]
    · intro i hi
      simp only [tableAt]
      have himod : (⟨i % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨i, hi⟩ := Fin.ext (Nat.mod_eq_of_lt hi)
      rw [himod]
      convert hword ⟨i, hi⟩ using 2
      funext bit
      exact (hbits_sum (fun k => f (i + k)) (w + 1)).2 bit.val bit.isLt

private theorem main_aux : ∀ (n w : ℕ) (hn : 0 < n),
    let I := n * 2 ^ (w + 1)
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧
      C.size ≤ 3 * n * 4 ^ w + 2 ^ w + 2 ∧
      ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
        let inputs := List.ofFn (fun j : Fin I =>
          table ⟨(j.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
            (fun bit => j.val.testBit bit.val))
        C.eval inputs = true ↔
          ∃ word : Fin n → Bool, ∀ i : Fin n,
            table i (fun bit => word ⟨(i.val + bit.val) % n, Nat.mod_lt _ hn⟩) = true := by
  intro n w hn
  refine ⟨buildCircuit n w, buildCircuit_mono n w, buildCircuit_readsBack n w,
    buildCircuit_size n w, ?_⟩
  intro table
  exact (eval_buildCircuit n w hn table).trans (dp_diag_iff_word n w hn table)

end PEqualNP.Outside.L_clb_042

theorem PEqualNP.Outside.L_clb_042 : (∀ (n w : ℕ) (hn : 0 < n),
  let I := n * 2 ^ (w + 1)
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧
    C.size ≤ 3 * n * 4 ^ w + 2 ^ w + 2 ∧
    ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := List.ofFn (fun j : Fin I =>
        table ⟨(j.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
          (fun bit => j.val.testBit bit.val))
      C.eval inputs = true ↔
        ∃ word : Fin n → Bool, ∀ i : Fin n,
          table i (fun bit => word ⟨(i.val + bit.val) % n, Nat.mod_lt _ hn⟩) = true) :=
  PEqualNP.Outside.L_clb_042.main_aux
