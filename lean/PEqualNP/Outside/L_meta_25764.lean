import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25764.Model

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def isAONB : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

def fanInTwoB (C : Circuit) : Bool :=
  C.gates.all fun g => isAONB g.op && decide (g.inputs.length ≤ 2)

theorem fanInTwoB_sound {C : Circuit} (h : fanInTwoB C = true) : FanInTwo C := by
  intro g hg
  have := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨?_, this.2⟩
  have h1 := this.1
  cases hop : g.op <;> rw [hop] at h1 <;> simp_all [isAONB]

def Agree (k : ℕ) (cs : List ℕ) (w : List Bool) : Prop :=
  cs.length = w.length ∧ ∀ j, (cs.getD j 0).testBit k = w.getD j false

theorem agree_snoc {k : ℕ} {cs : List ℕ} {w : List Bool} {c : ℕ} {v : Bool}
    (h : Agree k cs w) (hv : c.testBit k = v) : Agree k (cs ++ [c]) (w ++ [v]) := by
  refine ⟨by simp [h.1], fun j => ?_⟩
  rcases lt_trichotomy j cs.length with hj | hj | hj
  · rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ (h.1 ▸ hj)]
    exact h.2 j
  · subst hj
    rw [List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ h.1.symm.le]
    simp [h.1, hv]
  · have hl := h.1
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp

def mask (n : ℕ) : ℕ := 2 ^ (2 ^ n) - 1

theorem testBit_mask {n k : ℕ} (hk : k < 2 ^ n) : (mask n).testBit k = true := by
  simp [mask, Nat.testBit_two_pow_sub_one, hk]

theorem testBit_foldr_and {k : ℕ} {n : ℕ} (hk : k < 2 ^ n) (l : List ℕ) :
    (l.foldr (· &&& ·) (mask n)).testBit k = (l.map fun c => c.testBit k).all id := by
  induction l with
  | nil => simp [testBit_mask hk]
  | cons c l ih => simp [ih]

theorem testBit_foldr_or {k : ℕ} (l : List ℕ) :
    (l.foldr (· ||| ·) 0).testBit k = (l.map fun c => c.testBit k).any id := by
  induction l with
  | nil => simp
  | cons c l ih => simp [ih]

def gateCol (n : ℕ) (g : Gate) (cs : List ℕ) : ℕ :=
  match g.op with
  | GateOp.and => (g.inputs.map fun a => cs.getD a 0).foldr (· &&& ·) (mask n)
  | GateOp.or => (g.inputs.map fun a => cs.getD a 0).foldr (· ||| ·) 0
  | GateOp.not => mask n ^^^ (g.inputs.map fun a => cs.getD a 0).headD 0
  | _ => 0

theorem gateCol_spec {n k : ℕ} (hk : k < 2 ^ n) {cs : List ℕ} {w : List Bool}
    (h : Agree k cs w) (g : Gate) (hg : isAONB g.op = true) :
    (gateCol n g cs).testBit k = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  have hmap : ((g.inputs.map fun a => cs.getD a 0).map fun c => c.testBit k)
      = g.inputs.map fun i => w.getD i false := by
    rw [List.map_map]; exact List.map_congr_left (fun a _ => h.2 a)
  cases hop : g.op with
  | and => simp only [gateCol, hop, GateOp.eval]; rw [testBit_foldr_and hk, hmap]
  | or => simp only [gateCol, hop, GateOp.eval]; rw [testBit_foldr_or, hmap]
  | not =>
    simp only [gateCol, hop, GateOp.eval]
    rw [Nat.testBit_xor, testBit_mask hk, ← hmap]
    cases g.inputs <;> simp
  | mod m => rw [hop] at hg; simp [isAONB] at hg
  | maj => rw [hop] at hg; simp [isAONB] at hg

theorem agree_foldl {n k : ℕ} (hk : k < 2 ^ n) :
    ∀ (gs : List Gate) (cs : List ℕ) (w : List Bool), (∀ g ∈ gs, isAONB g.op = true) →
      Agree k cs w →
      Agree k (gs.foldl (fun cs g => cs ++ [gateCol n g cs]) cs)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) := by
  intro gs
  induction gs with
  | nil => intro cs w _ h; exact h
  | cons g gs ih =>
    intro cs w hg h
    exact ih _ _ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      (agree_snoc h (gateCol_spec hk h g (hg g List.mem_cons_self)))

def aonB (C : Circuit) : Bool :=
  C.gates.all fun g => isAONB g.op

def lcol (m : ℕ) : ℕ → ℕ
  | 0 => 2 ^ m - 1
  | j + 1 => 2 ^ m * lcol m j

def rcol (m v : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 ^ v + 2 ^ m * rcol m v k

def tcol (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: rs => r + 2 ^ m * tcol m rs

def inCols (n m : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin n => lcol m i) ++ List.ofFn (fun j : Fin m => rcol m j n)

def pcols (N : ℕ) (C : Circuit) (n m : ℕ) : List ℕ :=
  C.gates.foldl (fun cs g => cs ++ [gateCol N g cs]) (inCols n m)

theorem lt_two_pow_of_lt {a b c : ℕ} (h : a < 2 ^ b) (hbc : b ≤ c) : a < 2 ^ c :=
  lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hbc)

theorem bit_lcol {m v : ℕ} (hv : v < m) : ∀ (j u : ℕ), (lcol m j).testBit (u * m + v) = decide (u = j) := by
  intro j
  induction j with
  | zero =>
    intro u
    cases u with
    | zero => simp [lcol, hv]
    | succ u =>
      simp only [lcol, Nat.testBit_two_pow_sub_one]
      have : m ≤ (u + 1) * m := Nat.le_mul_of_pos_left m (Nat.succ_pos u)
      simp; omega
  | succ j ih =>
    intro u
    rw [lcol, Nat.testBit_two_pow_mul]
    cases u with
    | zero => simp; omega
    | succ u =>
      have e : (u + 1) * m + v - m = u * m + v := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * m + v ≥ m := by rw [Nat.succ_mul]; omega
      simp only [ge_iff_le, g, decide_true, Bool.true_and, e, ih u]
      simp

theorem bit_rcol {m v v' : ℕ} (hv : v < m) (hv' : v' < m) :
    ∀ (n u : ℕ), (rcol m v n).testBit (u * m + v') = decide (u < n ∧ v' = v) := by
  intro n
  induction n with
  | zero => intro u; simp [rcol]
  | succ n ih =>
    intro u
    have hlt : 2 ^ v < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hv
    rw [rcol, Nat.add_comm, Nat.two_pow_add_eq_or_of_lt hlt, Nat.testBit_or, Nat.testBit_two_pow_mul,
      Nat.testBit_two_pow]
    cases u with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [show decide (v' ≥ m) = false from decide_eq_false (by omega), Bool.false_and, Bool.false_or]
      by_cases h : v' = v
      · subst h; simp
      · simp only [Nat.succ_pos, true_and, h, decide_false]
        exact decide_eq_false (fun e => h e.symm)
    | succ u =>
      have e : (u + 1) * m + v' - m = u * m + v' := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * m + v' ≥ m := by rw [Nat.succ_mul]; omega
      have ne : v ≠ (u + 1) * m + v' := by rw [Nat.succ_mul]; omega
      simp only [g, decide_true, Bool.true_and, e, ih u, ne, decide_false, Bool.or_false]
      simp

theorem bit_tcol {m v : ℕ} (hv : v < m) :
    ∀ (rows : List ℕ), (∀ r ∈ rows, r < 2 ^ m) → ∀ u : ℕ,
      (tcol m rows).testBit (u * m + v) = (rows.getD u 0).testBit v := by
  intro rows
  induction rows with
  | nil => intro _ u; simp [tcol]
  | cons r rs ih =>
    intro hr u
    have hr0 : r < 2 ^ m := hr r List.mem_cons_self
    rw [tcol, Nat.add_comm, Nat.two_pow_add_eq_or_of_lt hr0, Nat.testBit_or, Nat.testBit_two_pow_mul]
    cases u with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [show decide (v ≥ m) = false from decide_eq_false (by omega), Bool.false_and, Bool.false_or]
      simp
    | succ u =>
      have e : (u + 1) * m + v - m = u * m + v := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * m + v ≥ m := by rw [Nat.succ_mul]; omega
      have hz : r.testBit ((u + 1) * m + v) = false :=
        Nat.testBit_lt_two_pow (lt_two_pow_of_lt hr0 (by rw [Nat.succ_mul]; omega))
      simp only [g, decide_true, Bool.true_and, e, ih (fun x hx => hr x (List.mem_cons_of_mem _ hx)) u, hz,
        Bool.or_false, List.getD_cons_succ]

theorem agree_oneEach {n m : ℕ} (u : Fin n) (v : Fin m) :
    Agree (u.val * m + v.val) (inCols n m) (oneEach u v) := by
  refine ⟨by simp [inCols, oneEach], fun j => ?_⟩
  by_cases hj : j < n
  · rw [inCols, oneEach, List.getD_append _ _ _ _ (by simpa using hj), List.getD_append _ _ _ _ (by simpa using hj)]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj)]
    simp only [List.getElem_ofFn]
    rw [bit_lcol v.isLt j u.val]
    simp [Fin.ext_iff, eq_comm]
  · by_cases hj2 : j < n + m
    · have h1 : (List.ofFn (fun i : Fin n => lcol m i)).length ≤ j := by simp; omega
      have h2 : (List.ofFn (fun i : Fin n => decide (i = u))).length ≤ j := by simp; omega
      rw [inCols, oneEach, List.getD_append_right _ _ _ _ h1, List.getD_append_right _ _ _ _ h2]
      simp only [List.length_ofFn]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
      simp only [List.getElem_ofFn]
      rw [bit_rcol (by omega) v.isLt n u.val]
      simp only [u.isLt, true_and]
      simp [Fin.ext_iff]; omega
    · rw [List.getD_eq_default _ _ (by simp [inCols]; omega), List.getD_eq_default _ _ (by simp [oneEach]; omega)]
      simp

theorem represents_of_pcols {n m N : ℕ} (hN : n * m ≤ 2 ^ N) (C : Circuit) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ m) (hg : aonB C = true)
    (h : ((pcols N C n m).getD C.output 0 == tcol m rows) = true) :
    Represents (fun (u : Fin n) (v : Fin m) => (rows.getD u.val 0).testBit v.val) C := by
  intro u v
  have hk : u.val * m + v.val < 2 ^ N := by
    have : u.val * m + v.val < (u.val + 1) * m := by rw [Nat.succ_mul]; omega
    have : (u.val + 1) * m ≤ n * m := Nat.mul_le_mul_right m u.isLt
    omega
  have hg' : ∀ g ∈ C.gates, isAONB g.op = true := fun g hg2 => List.all_eq_true.mp hg g hg2
  have hA := agree_foldl hk C.gates _ _ hg' (agree_oneEach u v)
  have := hA.2 C.output
  rw [show C.gates.foldl _ (inCols n m) = pcols N C n m from rfl, beq_iff_eq.mp h,
    bit_tcol v.isLt rows hrows u.val] at this
  exact this.symm

end PEqualNP.Outside.L_meta_25764.Model

set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_25764 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 180 ∧
  (C.gates.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => match g.op with | .not => true | _ => false)).length ≤ 1 ∧
  PEqualNP.Represents.Represents (fun u v : Fin 32 => (([0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050] : List ℕ).getD u.val 0).testBit v.val) C := by
  let codes : List (ℕ × ℕ × ℕ) := [
    (1,25,43),(1,47,54),(1,9,39),(1,6,10),(1,15,36),(1,8,40),(1,5,20),(1,13,33),(1,4,58),
    (1,3,41),(1,0,62),(1,28,36),(1,4,61),(1,1,42),(1,29,35),(1,28,50),(1,30,46),(1,19,52),
    (1,25,35),(1,44,52),(1,24,27),(1,18,37),(1,12,55),(1,21,48),(1,2,51),(1,2,18),(1,17,45),
    (1,26,32),(1,16,60),(1,10,23),(1,0,61),(1,21,64),(1,65,94),(1,34,74),(1,55,77),(1,11,80),
    (1,66,76),(1,68,82),(1,53,67),(1,15,79),(1,68,73),(1,54,70),(1,48,65),(1,62,69),(1,60,84),
    (1,72,95),(1,19,31),(1,110,90),(1,111,96),(1,18,38),(1,113,75),(1,114,83),(1,115,86),(1,116,102),
    (1,10,20),(1,118,57),(1,119,71),(1,120,78),(1,41,100),(1,122,103),(1,0,56),(1,124,75),(1,125,78),
    (1,126,92),(1,3,26),(1,128,57),(1,129,76),(1,130,98),(1,1,28),(1,132,46),(1,133,105),(1,134,109),
    (1,66,67),(1,136,88),(1,137,104),(1,6,14),(1,139,32),(1,140,45),(1,141,64),(1,142,87),(1,24,34),
    (1,144,69),(1,145,98),(1,14,39),(1,147,97),(1,148,102),(1,22,37),(1,150,69),(1,151,91),(1,152,92),
    (1,13,27),(1,154,89),(1,38,106),(1,31,59),(1,157,86),(1,158,100),(1,52,75),(1,160,105),(1,161,108),
    (1,14,71),(1,163,72),(1,164,81),(1,11,53),(1,166,91),(1,167,104),(1,83,99),(1,169,107),(1,67,95),
    (1,171,96),(1,45,63),(1,173,88),(1,174,93),(1,33,47),(1,176,58),(1,177,66),(1,178,70),(1,179,74),
    (1,9,78),(1,181,89),(1,182,106),(1,49,63),(1,184,109),(1,24,40),(1,186,90),(1,187,99),(1,42,81),
    (1,189,101),(1,26,50),(1,191,87),(1,192,108),(1,47,85),(1,194,93),(1,195,101),(1,9,24),(1,197,51),
    (1,198,52),(1,199,59),(1,200,85),(1,4,16),(1,202,42),(1,203,73),(1,204,107),(1,7,22),(1,206,59),
    (1,207,64),(1,208,97),(1,44,71),(1,210,77),(1,211,103),(0,112,117),(0,121,123),(0,127,131),(0,135,138),
    (0,143,146),(0,149,153),(0,155,156),(0,159,162),(0,165,168),(0,170,172),(0,175,180),(0,183,185),(0,188,190),
    (0,193,196),(0,201,205),(0,209,212),(1,228,227),(1,226,225),(1,224,223),(1,222,221),(1,220,219),(1,218,217),
    (1,216,215),(1,214,213),(1,229,230),(1,231,232),(1,233,234),(1,235,236),(1,237,238),(1,239,240),(1,241,242)]
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨codes.map (fun (o,a,b) =>
    ⟨if o = 0 then .and else .or, [a,b]⟩), 243⟩
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_25764.Model.fanInTwoB_sound (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · refine PEqualNP.Outside.L_meta_25764.Model.represents_of_pcols (n := 32) (m := 32) (N := 10) (by decide) C ([0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050] : List ℕ) ?_ ?_ ?_
    · decide +kernel
    · decide +kernel
    · decide +kernel
