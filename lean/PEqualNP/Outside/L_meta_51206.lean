import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_51206

open PEqualNP.CircuitLowerBounds

abbrev W := BitVec 6

def roots : List W := [62, 60, 56, 48, 32, 0, 63]
def goals : Finset W := {10, 12, 35}
def missing (bank : List W) : Nat := (goals \ bank.toFinset).card

theorem missing_insert (x : W) (bank : List W) :
    missing bank ≤ missing (x :: bank) + 1 := by
  have sub : goals \ bank.toFinset ⊆ insert x (goals \ (x :: bank).toFinset) := by
    intro y hy
    obtain ⟨hgoal, hy⟩ := Finset.mem_sdiff.mp hy
    by_cases e : y = x
    · exact Finset.mem_insert.mpr (Or.inl e)
    · apply Finset.mem_insert.mpr
      refine Or.inr (Finset.mem_sdiff.mpr ⟨hgoal, ?_⟩)
      simpa [e] using hy
  exact (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)

theorem missing_zero {bank : List W} (done : ∀ w ∈ goals, w ∈ bank) :
    missing bank = 0 := by
  apply Finset.card_eq_zero.mpr
  exact Finset.sdiff_eq_empty_iff_subset.mpr (fun w hw => List.mem_toFinset.mpr (done w hw))

def advance (next : List W → Bool) (bank : List W) (x : W) : Bool :=
  if x ∈ bank then false else next (x :: bank)

def search : Nat → Nat → List W → Bool
  | 0, _, bank => missing bank == 0
  | k + 1, n, bank =>
      if missing bank = 0 then true
      else if k + 1 < missing bank then false
      else search k n bank ||
        (bank.any fun a =>
          (bank.any fun b =>
            advance (search k n) bank (a &&& b) ||
            advance (search k n) bank (a ||| b)) ||
          (match n with
          | 0 => false
          | m + 1 => advance (search k m) bank (~~~a)))

theorem search_done {k n : Nat} {bank : List W} (h : missing bank = 0) :
    search k n bank = true := by
  cases k <;> simp [search, h]

theorem via_stay {k n : Nat} {bank : List W}
    (hle : missing bank ≤ k + 1) (cont : search k n bank = true) :
    search (k + 1) n bank = true := by
  by_cases h : missing bank = 0
  · exact search_done h
  · simp [search, h, Nat.not_lt_of_ge hle, cont]

theorem via_and {k n : Nat} {bank : List W} {a b : W}
    (hle : missing bank ≤ k + 1) (ha : a ∈ bank) (hb : b ∈ bank)
    (hf : a &&& b ∉ bank) (cont : search k n ((a &&& b) :: bank) = true) :
    search (k + 1) n bank = true := by
  by_cases hz : missing bank = 0
  · exact search_done hz
  · simp only [search, hz, ite_false, Nat.not_lt_of_ge hle, Bool.or_eq_true]
    right
    apply List.any_eq_true.mpr
    refine ⟨a, ha, ?_⟩
    rw [Bool.or_eq_true]
    left
    apply List.any_eq_true.mpr
    refine ⟨b, hb, ?_⟩
    rw [Bool.or_eq_true]
    left
    simp [advance, hf, cont]

theorem via_or {k n : Nat} {bank : List W} {a b : W}
    (hle : missing bank ≤ k + 1) (ha : a ∈ bank) (hb : b ∈ bank)
    (hf : a ||| b ∉ bank) (cont : search k n ((a ||| b) :: bank) = true) :
    search (k + 1) n bank = true := by
  by_cases hz : missing bank = 0
  · exact search_done hz
  · simp only [search, hz, ite_false, Nat.not_lt_of_ge hle, Bool.or_eq_true]
    right
    apply List.any_eq_true.mpr
    refine ⟨a, ha, ?_⟩
    rw [Bool.or_eq_true]
    left
    apply List.any_eq_true.mpr
    refine ⟨b, hb, ?_⟩
    rw [Bool.or_eq_true]
    right
    simp [advance, hf, cont]

theorem via_not {k n : Nat} {bank : List W} {a : W}
    (hle : missing bank ≤ k + 1) (ha : a ∈ bank)
    (hf : ~~~a ∉ bank) (cont : search k n (~~~a :: bank) = true) :
    search (k + 1) (n + 1) bank = true := by
  by_cases hz : missing bank = 0
  · exact search_done hz
  · simp only [search, hz, ite_false, Nat.not_lt_of_ge hle, Bool.or_eq_true]
    right
    apply List.any_eq_true.mpr
    refine ⟨a, ha, ?_⟩
    rw [Bool.or_eq_true]
    right
    simp [advance, hf, cont]

def readWord (words : List W) (i : Nat) : W := words.getD i 0

def gateWord (words : List W) (g : Gate) : W :=
  match g.op, g.inputs with
  | .and, [] => 63
  | .and, [i] => readWord words i
  | .and, i :: j :: _ => readWord words i &&& readWord words j
  | .or, [] => 0
  | .or, [i] => readWord words i
  | .or, i :: j :: _ => readWord words i ||| readWord words j
  | .not, [] => 63
  | .not, i :: _ => ~~~readWord words i
  | _, _ => 0

def evalWords (gs : List Gate) (input : List W) : List W :=
  gs.foldl (fun bank g => bank ++ [gateWord bank g]) input

def fit (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def countNot (gs : List Gate) : Nat :=
  (gs.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)).length

theorem read_mem {words bank : List W} (subs : ∀ w ∈ words, w ∈ bank)
    (hzero : 0 ∈ bank) (i : Nat) : readWord words i ∈ bank := by
  unfold readWord
  rw [List.getD_eq_getElem?_getD]
  cases e : words[i]? with
  | none => exact hzero
  | some x => exact subs x (List.mem_of_getElem? e)

theorem shortage (gs : List Gate) (words bank : List W)
    (subs : ∀ w ∈ words, w ∈ bank)
    (hgoal : ∀ w ∈ goals, w ∈ evalWords gs words) :
    missing bank ≤ gs.length := by
  induction gs generalizing words bank with
  | nil => exact Nat.le_of_eq (missing_zero fun w hw => subs w (hgoal w hw))
  | cons g gs ih =>
    let v := gateWord words g
    have hs : ∀ w ∈ words ++ [v], w ∈ v :: bank := by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_cons_of_mem _ (subs w hw)
      · rw [List.mem_singleton.mp hw]
        exact List.mem_cons_self
    have h := ih (words ++ [v]) (v :: bank) hs hgoal
    have h' := missing_insert v bank
    simp only [List.length_cons]
    omega

theorem fits_search (gs : List Gate) (words bank : List W) (k n : Nat)
    (legal : ∀ g ∈ gs, fit g)
    (subs : ∀ w ∈ words, w ∈ bank)
    (hzero : (0 : W) ∈ bank) (hone : (63 : W) ∈ bank)
    (hs : gs.length ≤ k) (hn : countNot gs ≤ n)
    (hgoal : ∀ w ∈ goals, w ∈ evalWords gs words) :
    search k n bank = true := by
  induction gs generalizing words bank k n with
  | nil => exact search_done (missing_zero fun w hw => subs w (hgoal w hw))
  | cons g gs ih =>
    cases k with
    | zero => simp at hs
    | succ k =>
      have hshort : missing bank ≤ k + 1 := by
        have h := shortage (g :: gs) words bank subs hgoal
        omega
      have hfit := legal g List.mem_cons_self
      have rest : ∀ d ∈ gs, fit d := fun d hd => legal d (List.mem_cons_of_mem _ hd)
      have hs' : gs.length ≤ k := by simpa using hs
      let v := gateWord words g
      have targetRest : ∀ w ∈ goals, w ∈ evalWords gs (words ++ [v]) := hgoal
      have takeNew (m : Nat) (hm : countNot gs ≤ m) :
          search k m (v :: bank) = true := by
        apply ih (words ++ [v]) (v :: bank) k m rest ?_
          (List.mem_cons_of_mem _ hzero) (List.mem_cons_of_mem _ hone) hs' hm targetRest
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact List.mem_cons_of_mem _ (subs w hw)
        · rw [List.mem_singleton.mp hw]
          exact List.mem_cons_self
      have hrestNot : countNot gs ≤ n := by
        unfold countNot at *
        by_cases hg : g.op = .not <;> simp [hg] at hn <;> omega
      by_cases hv : v ∈ bank
      · apply via_stay hshort
        apply ih (words ++ [v]) bank k n rest ?_ hzero hone hs' hrestNot targetRest
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact subs w hw
        · rwa [List.mem_singleton.mp hw]
      · have available := read_mem subs hzero
        obtain ⟨hop, hlen⟩ := hfit
        obtain ⟨op, ins⟩ := g
        simp only at hop
        rcases hop with rfl | rfl | rfl
        · rcases ins with _ | ⟨i, _ | ⟨j, tail⟩⟩
          · exact (hv hone).elim
          · exact (hv (available i)).elim
          · exact via_and hshort (available i) (available j) hv (takeNew n hrestNot)
        · rcases ins with _ | ⟨i, _ | ⟨j, tail⟩⟩
          · exact (hv hzero).elim
          · exact (hv (available i)).elim
          · exact via_or hshort (available i) (available j) hv (takeNew n hrestNot)
        · cases ins with
          | nil => exact (hv hone).elim
          | cons i tl =>
            have hn' : countNot gs + 1 ≤ n := by simpa [countNot] using hn
            cases n with
            | zero => omega
            | succ m =>
              exact via_not hshort (available i) hv (takeNew m (by omega))

def bit (t : Fin 6) (w : W) : Bool := w.getLsbD t.val
def boolInputs (t : Fin 6) : List Bool :=
  List.ofFn (fun i : Fin 5 => decide (i.val < t.val)) ++ [false, true]

theorem roots_bits : ∀ t : Fin 6, roots.map (bit t) = boolInputs t := by decide +kernel

theorem map_read (t : Fin 6) (words : List W) (i : Nat) :
    (words.map (bit t)).getD i false = bit t (readWord words i) := by
  simp only [readWord, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases words[i]? <;> simp [bit]

theorem gate_bits (t : Fin 6) (words : List W) (g : Gate) (hg : fit g) :
    bit t (gateWord words g) =
      g.op.eval (g.inputs.map fun i => (words.map (bit t)).getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hn⟩ := hg
  simp only at hop hn
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, tail⟩⟩⟩
    · show (63 : W).getLsbD t.val = true
      have h : ∀ t : Fin 6, (63 : W).getLsbD t.val = true := by decide +kernel
      exact h t
    · simp only [gateWord, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, map_read, id_eq]
    · simp only [gateWord, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, map_read, id_eq]
      exact BitVec.getLsbD_and
    · simp at hn
  · rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, tail⟩⟩⟩
    · simp [gateWord, GateOp.eval, bit]
    · simp only [gateWord, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, map_read, id_eq]
    · simp only [gateWord, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, map_read, id_eq]
      exact BitVec.getLsbD_or
    · simp at hn
  · rcases ins with _ | ⟨i, tail⟩
    · show (63 : W).getLsbD t.val = true
      have h : ∀ t : Fin 6, (63 : W).getLsbD t.val = true := by decide +kernel
      exact h t
    · simp only [gateWord, GateOp.eval, List.map_cons, List.headD_cons, map_read]
      simp [bit, t.isLt]

theorem eval_bits (t : Fin 6) (gs : List Gate) (words : List W)
    (h : ∀ g ∈ gs, fit g) :
    (evalWords gs words).map (bit t) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (words.map (bit t)) := by
  induction gs generalizing words with
  | nil => rfl
  | cons g gs ih =>
    simp only [evalWords, List.foldl_cons]
    rw [show (gs.foldl (fun w d => w ++ [gateWord w d]) (words ++ [gateWord words g])) =
         evalWords gs (words ++ [gateWord words g]) by rfl]
    rw [ih _ (fun d hd => h d (List.mem_cons_of_mem _ hd))]
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [gate_bits _ _ _ (h g List.mem_cons_self)]

theorem read_circuit (D : Circuit) (legal : ∀ g ∈ D.gates, fit g) (t : Fin 6) (i : Nat) :
    bit t (readWord (evalWords D.gates roots) i) = (D.wires (boolInputs t)).getD i false := by
  rw [← map_read, eval_bits _ _ _ legal, roots_bits]
  rfl

theorem recover {a b : W} (h : ∀ t : Fin 6, bit t a = bit t b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact h ⟨i, hi⟩

def binaryMoves (bank : List W) : List W :=
  (bank.flatMap fun a => bank.flatMap fun b => [a &&& b, a ||| b]).eraseDups

def unaryMoves (bank : List W) : List W := (bank.map (fun a => ~~~a)).eraseDups

def compressed : Nat → Nat → List W → Bool
  | 0, _, bank => missing bank == 0
  | k + 1, n, bank =>
      if missing bank = 0 then true
      else if k + 1 < missing bank then false
      else compressed k n bank ||
        ((binaryMoves bank).any (advance (compressed k n) bank) ||
          match n with
          | 0 => false
          | m + 1 => (unaryMoves bank).any (advance (compressed k m) bank))

theorem advance_implication {f g : List W → Bool} {bank : List W} {x : W}
    (imp : f (x :: bank) = true → g (x :: bank) = true)
    (found : advance f bank x = true) : advance g bank x = true := by
  by_cases present : x ∈ bank
  · simp [advance, present] at found
  · simpa only [advance, ite_eq_right present] using imp (by simpa only [advance, ite_eq_right present] using found)

theorem compressed_complete (k n : Nat) (bank : List W) :
    search k n bank = true → compressed k n bank = true := by
  induction k generalizing n bank with
  | zero => exact id
  | succ k ih =>
    intro found
    by_cases done : missing bank = 0
    · simp [compressed, done]
    by_cases impossible : k + 1 < missing bank
    · simp [search, done, impossible] at found
    simp only [search, compressed, done, impossible, ite_false, Bool.or_eq_true, List.any_eq_true] at found ⊢
    rcases found with prev | ⟨a, ha, many | negated⟩
    · exact Or.inl (ih n bank prev)
    · obtain ⟨b, hb, step⟩ := many
      have move (v : W) (hv : v ∈ [a &&& b, a ||| b]) : v ∈ binaryMoves bank := by
        apply List.mem_eraseDups.mpr
        exact List.mem_flatMap.mpr ⟨a, ha, List.mem_flatMap.mpr ⟨b, hb, hv⟩⟩
      rcases step with step | step
      · exact Or.inr (.inl ⟨a &&& b, move _ (by simp), advance_implication (ih n _) step⟩)
      · exact Or.inr (.inl ⟨a ||| b, move _ (by simp), advance_implication (ih n _) step⟩)
    · cases n with
      | zero => contradiction
      | succ n =>
        have move : ~~~a ∈ unaryMoves bank :=
          List.mem_eraseDups.mpr (List.mem_map.mpr ⟨a, ha, rfl⟩)
        exact Or.inr (.inr (List.any_eq_true.mpr ⟨~~~a, move, advance_implication (ih n _) negated⟩))

def addable (bank moves : List W) : List W :=
  moves.filter (fun x => !bank.contains x)

theorem addable_any (bank moves : List W) (next : List W → Bool) :
    (addable bank moves).any (fun x => next (x :: bank)) = moves.any (advance next bank) := by
  induction moves with
  | nil => rfl
  | cons x moves ih =>
    by_cases hx : x ∈ bank
    · simp [addable, advance, hx, ← ih]
    · simp [addable, advance, hx, ← ih]

theorem compressed_step_false {k n : Nat} {bank : List W}
    (notDone : missing bank ≠ 0)
    (skip : compressed k n bank = false)
    (binary : (addable bank (binaryMoves bank)).any (fun x => compressed k n (x :: bank)) = false)
    (unary : match n with
      | 0 => false = false
      | m + 1 => (addable bank (unaryMoves bank)).any (fun x => compressed k m (x :: bank)) = false) :
    compressed (k + 1) n bank = false := by
  by_cases insufficient : k + 1 < missing bank
  · simp [compressed, notDone, insufficient]
  simp only [compressed, notDone, insufficient, ite_false, skip, Bool.false_or]
  rw [← addable_any, binary]
  simp only [Bool.false_or]
  cases n with
  | zero => rfl
  | succ n => exact (addable_any bank (unaryMoves bank) (compressed k n)).symm.trans unary

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_3 : compressed 3 2 [62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_4 : compressed 3 1 [1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_5 : compressed 3 1 [3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_6 : compressed 3 1 [7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_7 : compressed 3 1 [15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_8 : compressed 3 1 [31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_2 : List W := [62, 60, 56, 48, 32, 0, 63]
theorem absent_2 : compressed 4 2 state_2 = false := by
  refine compressed_step_false (k := 3) (n := 2) (bank := state_2)
    (by decide +kernel) absent_3 ?_ ?_
  · have moves : addable state_2 (binaryMoves state_2) = [] := by decide +kernel
    rw [moves]
    rfl
  · have moves : addable state_2 (unaryMoves state_2) = [1, 3, 7, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_4, absent_5, absent_6, absent_7, absent_8, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_10 : compressed 3 1 [61, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_11 : compressed 3 1 [57, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_12 : compressed 3 1 [49, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_13 : compressed 3 1 [33, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_14 : compressed 3 0 [3, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_15 : compressed 3 0 [7, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_16 : compressed 3 0 [15, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_17 : compressed 3 0 [31, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_9 : List W := [1, 62, 60, 56, 48, 32, 0, 63]
theorem absent_9 : compressed 4 1 state_9 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_9)
    (by decide +kernel) absent_4 ?_ ?_
  · have moves : addable state_9 (binaryMoves state_9) = [61, 57, 49, 33] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_10, absent_11, absent_12, absent_13, Bool.false_or]
  · have moves : addable state_9 (unaryMoves state_9) = [3, 7, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_14, absent_15, absent_16, absent_17, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_19 : compressed 3 1 [2, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_20 : compressed 3 1 [59, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_21 : compressed 3 1 [51, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_22 : compressed 3 1 [35, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_23 : compressed 3 0 [1, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_24 : compressed 3 0 [7, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_25 : compressed 3 0 [15, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_26 : compressed 3 0 [31, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_18 : List W := [3, 62, 60, 56, 48, 32, 0, 63]
theorem absent_18 : compressed 4 1 state_18 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_18)
    (by decide +kernel) absent_5 ?_ ?_
  · have moves : addable state_18 (binaryMoves state_18) = [2, 59, 51, 35] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_19, absent_20, absent_21, absent_22, Bool.false_or]
  · have moves : addable state_18 (unaryMoves state_18) = [1, 7, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_23, absent_24, absent_25, absent_26, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_28 : compressed 3 1 [6, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_29 : compressed 3 1 [4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_30 : compressed 3 1 [55, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_31 : compressed 3 1 [39, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_32 : compressed 3 0 [1, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_33 : compressed 3 0 [3, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_34 : compressed 3 0 [15, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_35 : compressed 3 0 [31, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_27 : List W := [7, 62, 60, 56, 48, 32, 0, 63]
theorem absent_27 : compressed 4 1 state_27 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_27)
    (by decide +kernel) absent_6 ?_ ?_
  · have moves : addable state_27 (binaryMoves state_27) = [6, 4, 55, 39] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_28, absent_29, absent_30, absent_31, Bool.false_or]
  · have moves : addable state_27 (unaryMoves state_27) = [1, 3, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_32, absent_33, absent_34, absent_35, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_37 : compressed 3 1 [14, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_38 : compressed 3 1 [12, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_39 : compressed 3 1 [8, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_40 : compressed 3 1 [47, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_41 : compressed 3 0 [1, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_42 : compressed 3 0 [3, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_43 : compressed 3 0 [7, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_44 : compressed 3 0 [31, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_36 : List W := [15, 62, 60, 56, 48, 32, 0, 63]
theorem absent_36 : compressed 4 1 state_36 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_36)
    (by decide +kernel) absent_7 ?_ ?_
  · have moves : addable state_36 (binaryMoves state_36) = [14, 12, 8, 47] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_37, absent_38, absent_39, absent_40, Bool.false_or]
  · have moves : addable state_36 (unaryMoves state_36) = [1, 3, 7, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_41, absent_42, absent_43, absent_44, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_46 : compressed 3 1 [30, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_47 : compressed 3 1 [28, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_48 : compressed 3 1 [24, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_49 : compressed 3 1 [16, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_50 : compressed 3 0 [1, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_51 : compressed 3 0 [3, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_52 : compressed 3 0 [7, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_53 : compressed 3 0 [15, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_45 : List W := [31, 62, 60, 56, 48, 32, 0, 63]
theorem absent_45 : compressed 4 1 state_45 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_45)
    (by decide +kernel) absent_8 ?_ ?_
  · have moves : addable state_45 (binaryMoves state_45) = [30, 28, 24, 16] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_46, absent_47, absent_48, absent_49, Bool.false_or]
  · have moves : addable state_45 (unaryMoves state_45) = [1, 3, 7, 15] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_50, absent_51, absent_52, absent_53, Bool.false_or]

abbrev state_1 : List W := [62, 60, 56, 48, 32, 0, 63]
theorem absent_1 : compressed 5 2 state_1 = false := by
  refine compressed_step_false (k := 4) (n := 2) (bank := state_1)
    (by decide +kernel) absent_2 ?_ ?_
  · have moves : addable state_1 (binaryMoves state_1) = [] := by decide +kernel
    rw [moves]
    rfl
  · have moves : addable state_1 (unaryMoves state_1) = [1, 3, 7, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_9, absent_18, absent_27, absent_36, absent_45, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_56 : compressed 3 1 [57, 61, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_57 : compressed 3 1 [49, 61, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_58 : compressed 3 1 [33, 61, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_59 : compressed 3 0 [2, 61, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_60 : compressed 3 0 [3, 61, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_61 : compressed 3 0 [7, 61, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_62 : compressed 3 0 [15, 61, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_63 : compressed 3 0 [31, 61, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_55 : List W := [61, 1, 62, 60, 56, 48, 32, 0, 63]
theorem absent_55 : compressed 4 1 state_55 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_55)
    (by decide +kernel) absent_10 ?_ ?_
  · have moves : addable state_55 (binaryMoves state_55) = [57, 49, 33] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_56, absent_57, absent_58, Bool.false_or]
  · have moves : addable state_55 (unaryMoves state_55) = [2, 3, 7, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_59, absent_60, absent_61, absent_62, absent_63, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_65 : compressed 3 1 [61, 57, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_66 : compressed 3 1 [49, 57, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_67 : compressed 3 1 [33, 57, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_68 : compressed 3 0 [6, 57, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_69 : compressed 3 0 [3, 57, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_70 : compressed 3 0 [7, 57, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_71 : compressed 3 0 [15, 57, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_72 : compressed 3 0 [31, 57, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_64 : List W := [57, 1, 62, 60, 56, 48, 32, 0, 63]
theorem absent_64 : compressed 4 1 state_64 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_64)
    (by decide +kernel) absent_11 ?_ ?_
  · have moves : addable state_64 (binaryMoves state_64) = [61, 49, 33] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_65, absent_66, absent_67, Bool.false_or]
  · have moves : addable state_64 (unaryMoves state_64) = [6, 3, 7, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_68, absent_69, absent_70, absent_71, absent_72, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_74 : compressed 3 1 [61, 49, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_75 : compressed 3 1 [57, 49, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_76 : compressed 3 1 [33, 49, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_77 : compressed 3 0 [14, 49, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_78 : compressed 3 0 [3, 49, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_79 : compressed 3 0 [7, 49, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_80 : compressed 3 0 [15, 49, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_81 : compressed 3 0 [31, 49, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_73 : List W := [49, 1, 62, 60, 56, 48, 32, 0, 63]
theorem absent_73 : compressed 4 1 state_73 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_73)
    (by decide +kernel) absent_12 ?_ ?_
  · have moves : addable state_73 (binaryMoves state_73) = [61, 57, 33] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_74, absent_75, absent_76, Bool.false_or]
  · have moves : addable state_73 (unaryMoves state_73) = [14, 3, 7, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_77, absent_78, absent_79, absent_80, absent_81, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_83 : compressed 3 1 [61, 33, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_84 : compressed 3 1 [57, 33, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_85 : compressed 3 1 [49, 33, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_86 : compressed 3 0 [30, 33, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_87 : compressed 3 0 [3, 33, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_88 : compressed 3 0 [7, 33, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_89 : compressed 3 0 [15, 33, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_90 : compressed 3 0 [31, 33, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_82 : List W := [33, 1, 62, 60, 56, 48, 32, 0, 63]
theorem absent_82 : compressed 4 1 state_82 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_82)
    (by decide +kernel) absent_13 ?_ ?_
  · have moves : addable state_82 (binaryMoves state_82) = [61, 57, 49] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_83, absent_84, absent_85, Bool.false_or]
  · have moves : addable state_82 (unaryMoves state_82) = [30, 3, 7, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_86, absent_87, absent_88, absent_89, absent_90, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_92 : compressed 3 0 [2, 3, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_93 : compressed 3 0 [59, 3, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_94 : compressed 3 0 [51, 3, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_95 : compressed 3 0 [35, 3, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_96 : compressed 3 0 [61, 3, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_97 : compressed 3 0 [57, 3, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_98 : compressed 3 0 [49, 3, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_99 : compressed 3 0 [33, 3, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_91 : List W := [3, 1, 62, 60, 56, 48, 32, 0, 63]
theorem absent_91 : compressed 4 0 state_91 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_91)
    (by decide +kernel) absent_14 ?_ ?_
  · have moves : addable state_91 (binaryMoves state_91) = [2, 59, 51, 35, 61, 57, 49, 33] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_92, absent_93, absent_94, absent_95, absent_96, absent_97, absent_98, absent_99, Bool.false_or]
  · rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_101 : compressed 3 0 [6, 7, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_102 : compressed 3 0 [4, 7, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_103 : compressed 3 0 [55, 7, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_104 : compressed 3 0 [39, 7, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_105 : compressed 3 0 [61, 7, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_106 : compressed 3 0 [57, 7, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_107 : compressed 3 0 [49, 7, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_108 : compressed 3 0 [33, 7, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_100 : List W := [7, 1, 62, 60, 56, 48, 32, 0, 63]
theorem absent_100 : compressed 4 0 state_100 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_100)
    (by decide +kernel) absent_15 ?_ ?_
  · have moves : addable state_100 (binaryMoves state_100) = [6, 4, 55, 39, 61, 57, 49, 33] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_101, absent_102, absent_103, absent_104, absent_105, absent_106, absent_107, absent_108, Bool.false_or]
  · rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_110 : compressed 3 0 [14, 15, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_111 : compressed 3 0 [12, 15, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_112 : compressed 3 0 [8, 15, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_113 : compressed 3 0 [47, 15, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_114 : compressed 3 0 [61, 15, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_115 : compressed 3 0 [57, 15, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_116 : compressed 3 0 [49, 15, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_117 : compressed 3 0 [33, 15, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_109 : List W := [15, 1, 62, 60, 56, 48, 32, 0, 63]
theorem absent_109 : compressed 4 0 state_109 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_109)
    (by decide +kernel) absent_16 ?_ ?_
  · have moves : addable state_109 (binaryMoves state_109) = [14, 12, 8, 47, 61, 57, 49, 33] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_110, absent_111, absent_112, absent_113, absent_114, absent_115, absent_116, absent_117, Bool.false_or]
  · rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_119 : compressed 3 0 [30, 31, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_120 : compressed 3 0 [28, 31, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_121 : compressed 3 0 [24, 31, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_122 : compressed 3 0 [16, 31, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_123 : compressed 3 0 [61, 31, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_124 : compressed 3 0 [57, 31, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_125 : compressed 3 0 [49, 31, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_126 : compressed 3 0 [33, 31, 1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_118 : List W := [31, 1, 62, 60, 56, 48, 32, 0, 63]
theorem absent_118 : compressed 4 0 state_118 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_118)
    (by decide +kernel) absent_17 ?_ ?_
  · have moves : addable state_118 (binaryMoves state_118) = [30, 28, 24, 16, 61, 57, 49, 33] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_119, absent_120, absent_121, absent_122, absent_123, absent_124, absent_125, absent_126, Bool.false_or]
  · rfl

abbrev state_54 : List W := [1, 62, 60, 56, 48, 32, 0, 63]
theorem absent_54 : compressed 5 1 state_54 = false := by
  refine compressed_step_false (k := 4) (n := 1) (bank := state_54)
    (by decide +kernel) absent_9 ?_ ?_
  · have moves : addable state_54 (binaryMoves state_54) = [61, 57, 49, 33] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_55, absent_64, absent_73, absent_82, Bool.false_or]
  · have moves : addable state_54 (unaryMoves state_54) = [3, 7, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_91, absent_100, absent_109, absent_118, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_129 : compressed 3 1 [58, 2, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_130 : compressed 3 1 [50, 2, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_131 : compressed 3 1 [34, 2, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_132 : compressed 3 1 [59, 2, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_133 : compressed 3 1 [51, 2, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_134 : compressed 3 1 [35, 2, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_135 : compressed 3 0 [61, 2, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_136 : compressed 3 0 [1, 2, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_137 : compressed 3 0 [7, 2, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_138 : compressed 3 0 [15, 2, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_139 : compressed 3 0 [31, 2, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_128 : List W := [2, 3, 62, 60, 56, 48, 32, 0, 63]
theorem absent_128 : compressed 4 1 state_128 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_128)
    (by decide +kernel) absent_19 ?_ ?_
  · have moves : addable state_128 (binaryMoves state_128) = [58, 50, 34, 59, 51, 35] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_129, absent_130, absent_131, absent_132, absent_133, absent_134, Bool.false_or]
  · have moves : addable state_128 (unaryMoves state_128) = [61, 1, 7, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_135, absent_136, absent_137, absent_138, absent_139, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_141 : compressed 3 1 [58, 59, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_142 : compressed 3 1 [2, 59, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_143 : compressed 3 1 [51, 59, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_144 : compressed 3 1 [35, 59, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_145 : compressed 3 0 [4, 59, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_146 : compressed 3 0 [1, 59, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_147 : compressed 3 0 [7, 59, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_148 : compressed 3 0 [15, 59, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_149 : compressed 3 0 [31, 59, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_140 : List W := [59, 3, 62, 60, 56, 48, 32, 0, 63]
theorem absent_140 : compressed 4 1 state_140 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_140)
    (by decide +kernel) absent_20 ?_ ?_
  · have moves : addable state_140 (binaryMoves state_140) = [58, 2, 51, 35] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_141, absent_142, absent_143, absent_144, Bool.false_or]
  · have moves : addable state_140 (unaryMoves state_140) = [4, 1, 7, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_145, absent_146, absent_147, absent_148, absent_149, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_151 : compressed 3 1 [50, 51, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_152 : compressed 3 1 [59, 51, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_153 : compressed 3 1 [2, 51, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_154 : compressed 3 1 [35, 51, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_155 : compressed 3 0 [12, 51, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_156 : compressed 3 0 [1, 51, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_157 : compressed 3 0 [7, 51, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_158 : compressed 3 0 [15, 51, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_159 : compressed 3 0 [31, 51, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_150 : List W := [51, 3, 62, 60, 56, 48, 32, 0, 63]
theorem absent_150 : compressed 4 1 state_150 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_150)
    (by decide +kernel) absent_21 ?_ ?_
  · have moves : addable state_150 (binaryMoves state_150) = [50, 59, 2, 35] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_151, absent_152, absent_153, absent_154, Bool.false_or]
  · have moves : addable state_150 (unaryMoves state_150) = [12, 1, 7, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_155, absent_156, absent_157, absent_158, absent_159, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_161 : compressed 3 1 [34, 35, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_162 : compressed 3 1 [59, 35, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_163 : compressed 3 1 [51, 35, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_164 : compressed 3 1 [2, 35, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_165 : compressed 3 0 [28, 35, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_166 : compressed 3 0 [1, 35, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_167 : compressed 3 0 [7, 35, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_168 : compressed 3 0 [15, 35, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_169 : compressed 3 0 [31, 35, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_160 : List W := [35, 3, 62, 60, 56, 48, 32, 0, 63]
theorem absent_160 : compressed 4 1 state_160 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_160)
    (by decide +kernel) absent_22 ?_ ?_
  · have moves : addable state_160 (binaryMoves state_160) = [34, 59, 51, 2] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_161, absent_162, absent_163, absent_164, Bool.false_or]
  · have moves : addable state_160 (unaryMoves state_160) = [28, 1, 7, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_165, absent_166, absent_167, absent_168, absent_169, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_171 : compressed 3 0 [61, 1, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_172 : compressed 3 0 [57, 1, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_173 : compressed 3 0 [49, 1, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_174 : compressed 3 0 [33, 1, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_175 : compressed 3 0 [2, 1, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_176 : compressed 3 0 [59, 1, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_177 : compressed 3 0 [51, 1, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_178 : compressed 3 0 [35, 1, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_170 : List W := [1, 3, 62, 60, 56, 48, 32, 0, 63]
theorem absent_170 : compressed 4 0 state_170 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_170)
    (by decide +kernel) absent_23 ?_ ?_
  · have moves : addable state_170 (binaryMoves state_170) = [61, 57, 49, 33, 2, 59, 51, 35] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_171, absent_172, absent_173, absent_174, absent_175, absent_176, absent_177, absent_178, Bool.false_or]
  · rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_180 : compressed 3 0 [6, 7, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_181 : compressed 3 0 [4, 7, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_182 : compressed 3 0 [55, 7, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_183 : compressed 3 0 [39, 7, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_184 : compressed 3 0 [2, 7, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_185 : compressed 3 0 [59, 7, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_186 : compressed 3 0 [51, 7, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_187 : compressed 3 0 [35, 7, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_179 : List W := [7, 3, 62, 60, 56, 48, 32, 0, 63]
theorem absent_179 : compressed 4 0 state_179 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_179)
    (by decide +kernel) absent_24 ?_ ?_
  · have moves : addable state_179 (binaryMoves state_179) = [6, 4, 55, 39, 2, 59, 51, 35] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_180, absent_181, absent_182, absent_183, absent_184, absent_185, absent_186, absent_187, Bool.false_or]
  · rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_189 : compressed 3 0 [14, 15, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_190 : compressed 3 0 [12, 15, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_191 : compressed 3 0 [8, 15, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_192 : compressed 3 0 [47, 15, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_193 : compressed 3 0 [2, 15, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_194 : compressed 3 0 [59, 15, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_195 : compressed 3 0 [51, 15, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_196 : compressed 3 0 [35, 15, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_188 : List W := [15, 3, 62, 60, 56, 48, 32, 0, 63]
theorem absent_188 : compressed 4 0 state_188 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_188)
    (by decide +kernel) absent_25 ?_ ?_
  · have moves : addable state_188 (binaryMoves state_188) = [14, 12, 8, 47, 2, 59, 51, 35] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_189, absent_190, absent_191, absent_192, absent_193, absent_194, absent_195, absent_196, Bool.false_or]
  · rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_198 : compressed 3 0 [30, 31, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_199 : compressed 3 0 [28, 31, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_200 : compressed 3 0 [24, 31, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_201 : compressed 3 0 [16, 31, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_202 : compressed 3 0 [2, 31, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_203 : compressed 3 0 [59, 31, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_204 : compressed 3 0 [51, 31, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_205 : compressed 3 0 [35, 31, 3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_197 : List W := [31, 3, 62, 60, 56, 48, 32, 0, 63]
theorem absent_197 : compressed 4 0 state_197 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_197)
    (by decide +kernel) absent_26 ?_ ?_
  · have moves : addable state_197 (binaryMoves state_197) = [30, 28, 24, 16, 2, 59, 51, 35] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_198, absent_199, absent_200, absent_201, absent_202, absent_203, absent_204, absent_205, Bool.false_or]
  · rfl

abbrev state_127 : List W := [3, 62, 60, 56, 48, 32, 0, 63]
theorem absent_127 : compressed 5 1 state_127 = false := by
  refine compressed_step_false (k := 4) (n := 1) (bank := state_127)
    (by decide +kernel) absent_18 ?_ ?_
  · have moves : addable state_127 (binaryMoves state_127) = [2, 59, 51, 35] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_128, absent_140, absent_150, absent_160, Bool.false_or]
  · have moves : addable state_127 (unaryMoves state_127) = [1, 7, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_170, absent_179, absent_188, absent_197, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_208 : compressed 3 1 [4, 6, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_209 : compressed 3 1 [54, 6, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_210 : compressed 3 1 [38, 6, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_211 : compressed 3 1 [55, 6, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_212 : compressed 3 1 [39, 6, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_213 : compressed 3 0 [57, 6, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_214 : compressed 3 0 [1, 6, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_215 : compressed 3 0 [3, 6, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_216 : compressed 3 0 [15, 6, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_217 : compressed 3 0 [31, 6, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_207 : List W := [6, 7, 62, 60, 56, 48, 32, 0, 63]
theorem absent_207 : compressed 4 1 state_207 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_207)
    (by decide +kernel) absent_28 ?_ ?_
  · have moves : addable state_207 (binaryMoves state_207) = [4, 54, 38, 55, 39] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_208, absent_209, absent_210, absent_211, absent_212, Bool.false_or]
  · have moves : addable state_207 (unaryMoves state_207) = [57, 1, 3, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_213, absent_214, absent_215, absent_216, absent_217, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_219 : compressed 3 1 [52, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_220 : compressed 3 1 [36, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_221 : compressed 3 1 [6, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_222 : compressed 3 1 [55, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_223 : compressed 3 1 [39, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_224 : compressed 3 0 [59, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_225 : compressed 3 0 [1, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_226 : compressed 3 0 [3, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_227 : compressed 3 0 [15, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_228 : compressed 3 0 [31, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_218 : List W := [4, 7, 62, 60, 56, 48, 32, 0, 63]
theorem absent_218 : compressed 4 1 state_218 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_218)
    (by decide +kernel) absent_29 ?_ ?_
  · have moves : addable state_218 (binaryMoves state_218) = [52, 36, 6, 55, 39] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_219, absent_220, absent_221, absent_222, absent_223, Bool.false_or]
  · have moves : addable state_218 (unaryMoves state_218) = [59, 1, 3, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_224, absent_225, absent_226, absent_227, absent_228, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_230 : compressed 3 1 [54, 55, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_231 : compressed 3 1 [52, 55, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_232 : compressed 3 1 [6, 55, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_233 : compressed 3 1 [4, 55, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_234 : compressed 3 1 [39, 55, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_235 : compressed 3 0 [8, 55, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_236 : compressed 3 0 [1, 55, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_237 : compressed 3 0 [3, 55, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_238 : compressed 3 0 [15, 55, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_239 : compressed 3 0 [31, 55, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_229 : List W := [55, 7, 62, 60, 56, 48, 32, 0, 63]
theorem absent_229 : compressed 4 1 state_229 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_229)
    (by decide +kernel) absent_30 ?_ ?_
  · have moves : addable state_229 (binaryMoves state_229) = [54, 52, 6, 4, 39] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_230, absent_231, absent_232, absent_233, absent_234, Bool.false_or]
  · have moves : addable state_229 (unaryMoves state_229) = [8, 1, 3, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_235, absent_236, absent_237, absent_238, absent_239, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_241 : compressed 3 1 [38, 39, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_242 : compressed 3 1 [36, 39, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_243 : compressed 3 1 [55, 39, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_244 : compressed 3 1 [6, 39, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_245 : compressed 3 1 [4, 39, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_246 : compressed 3 0 [24, 39, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_247 : compressed 3 0 [1, 39, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_248 : compressed 3 0 [3, 39, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_249 : compressed 3 0 [15, 39, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_250 : compressed 3 0 [31, 39, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_240 : List W := [39, 7, 62, 60, 56, 48, 32, 0, 63]
theorem absent_240 : compressed 4 1 state_240 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_240)
    (by decide +kernel) absent_31 ?_ ?_
  · have moves : addable state_240 (binaryMoves state_240) = [38, 36, 55, 6, 4] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_241, absent_242, absent_243, absent_244, absent_245, Bool.false_or]
  · have moves : addable state_240 (unaryMoves state_240) = [24, 1, 3, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_246, absent_247, absent_248, absent_249, absent_250, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_252 : compressed 3 0 [61, 1, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_253 : compressed 3 0 [57, 1, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_254 : compressed 3 0 [49, 1, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_255 : compressed 3 0 [33, 1, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_256 : compressed 3 0 [6, 1, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_257 : compressed 3 0 [4, 1, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_258 : compressed 3 0 [55, 1, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_259 : compressed 3 0 [39, 1, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_251 : List W := [1, 7, 62, 60, 56, 48, 32, 0, 63]
theorem absent_251 : compressed 4 0 state_251 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_251)
    (by decide +kernel) absent_32 ?_ ?_
  · have moves : addable state_251 (binaryMoves state_251) = [61, 57, 49, 33, 6, 4, 55, 39] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_252, absent_253, absent_254, absent_255, absent_256, absent_257, absent_258, absent_259, Bool.false_or]
  · rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_261 : compressed 3 0 [2, 3, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_262 : compressed 3 0 [59, 3, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_263 : compressed 3 0 [51, 3, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_264 : compressed 3 0 [35, 3, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_265 : compressed 3 0 [6, 3, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_266 : compressed 3 0 [4, 3, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_267 : compressed 3 0 [55, 3, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_268 : compressed 3 0 [39, 3, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_260 : List W := [3, 7, 62, 60, 56, 48, 32, 0, 63]
theorem absent_260 : compressed 4 0 state_260 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_260)
    (by decide +kernel) absent_33 ?_ ?_
  · have moves : addable state_260 (binaryMoves state_260) = [2, 59, 51, 35, 6, 4, 55, 39] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_261, absent_262, absent_263, absent_264, absent_265, absent_266, absent_267, absent_268, Bool.false_or]
  · rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_270 : compressed 3 0 [14, 15, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_271 : compressed 3 0 [12, 15, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_272 : compressed 3 0 [8, 15, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_273 : compressed 3 0 [47, 15, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_274 : compressed 3 0 [6, 15, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_275 : compressed 3 0 [4, 15, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_276 : compressed 3 0 [55, 15, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_277 : compressed 3 0 [39, 15, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_269 : List W := [15, 7, 62, 60, 56, 48, 32, 0, 63]
theorem absent_269 : compressed 4 0 state_269 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_269)
    (by decide +kernel) absent_34 ?_ ?_
  · have moves : addable state_269 (binaryMoves state_269) = [14, 12, 8, 47, 6, 4, 55, 39] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_270, absent_271, absent_272, absent_273, absent_274, absent_275, absent_276, absent_277, Bool.false_or]
  · rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_279 : compressed 3 0 [30, 31, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_280 : compressed 3 0 [28, 31, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_281 : compressed 3 0 [24, 31, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_282 : compressed 3 0 [16, 31, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_283 : compressed 3 0 [6, 31, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_284 : compressed 3 0 [4, 31, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_285 : compressed 3 0 [55, 31, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_286 : compressed 3 0 [39, 31, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_278 : List W := [31, 7, 62, 60, 56, 48, 32, 0, 63]
theorem absent_278 : compressed 4 0 state_278 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_278)
    (by decide +kernel) absent_35 ?_ ?_
  · have moves : addable state_278 (binaryMoves state_278) = [30, 28, 24, 16, 6, 4, 55, 39] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_279, absent_280, absent_281, absent_282, absent_283, absent_284, absent_285, absent_286, Bool.false_or]
  · rfl

abbrev state_206 : List W := [7, 62, 60, 56, 48, 32, 0, 63]
theorem absent_206 : compressed 5 1 state_206 = false := by
  refine compressed_step_false (k := 4) (n := 1) (bank := state_206)
    (by decide +kernel) absent_27 ?_ ?_
  · have moves : addable state_206 (binaryMoves state_206) = [6, 4, 55, 39] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_207, absent_218, absent_229, absent_240, Bool.false_or]
  · have moves : addable state_206 (unaryMoves state_206) = [1, 3, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_251, absent_260, absent_269, absent_278, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_289 : compressed 3 1 [12, 14, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_290 : compressed 3 1 [8, 14, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_291 : compressed 3 1 [46, 14, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_292 : compressed 3 1 [47, 14, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_293 : compressed 3 0 [49, 14, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_294 : compressed 3 0 [1, 14, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_295 : compressed 3 0 [3, 14, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_296 : compressed 3 0 [7, 14, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_297 : compressed 3 0 [31, 14, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_288 : List W := [14, 15, 62, 60, 56, 48, 32, 0, 63]
theorem absent_288 : compressed 4 1 state_288 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_288)
    (by decide +kernel) absent_37 ?_ ?_
  · have moves : addable state_288 (binaryMoves state_288) = [12, 8, 46, 47] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_289, absent_290, absent_291, absent_292, Bool.false_or]
  · have moves : addable state_288 (unaryMoves state_288) = [49, 1, 3, 7, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_293, absent_294, absent_295, absent_296, absent_297, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_299 : compressed 3 1 [8, 12, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_300 : compressed 3 1 [44, 12, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_301 : compressed 3 1 [14, 12, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_302 : compressed 3 1 [47, 12, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_303 : compressed 3 0 [51, 12, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_304 : compressed 3 0 [1, 12, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_305 : compressed 3 0 [3, 12, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_306 : compressed 3 0 [7, 12, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_307 : compressed 3 0 [31, 12, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_298 : List W := [12, 15, 62, 60, 56, 48, 32, 0, 63]
theorem absent_298 : compressed 4 1 state_298 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_298)
    (by decide +kernel) absent_38 ?_ ?_
  · have moves : addable state_298 (binaryMoves state_298) = [8, 44, 14, 47] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_299, absent_300, absent_301, absent_302, Bool.false_or]
  · have moves : addable state_298 (unaryMoves state_298) = [51, 1, 3, 7, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_303, absent_304, absent_305, absent_306, absent_307, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_309 : compressed 3 1 [40, 8, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_310 : compressed 3 1 [14, 8, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_311 : compressed 3 1 [12, 8, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_312 : compressed 3 1 [47, 8, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_313 : compressed 3 0 [55, 8, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_314 : compressed 3 0 [1, 8, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_315 : compressed 3 0 [3, 8, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_316 : compressed 3 0 [7, 8, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_317 : compressed 3 0 [31, 8, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_308 : List W := [8, 15, 62, 60, 56, 48, 32, 0, 63]
theorem absent_308 : compressed 4 1 state_308 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_308)
    (by decide +kernel) absent_39 ?_ ?_
  · have moves : addable state_308 (binaryMoves state_308) = [40, 14, 12, 47] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_309, absent_310, absent_311, absent_312, Bool.false_or]
  · have moves : addable state_308 (unaryMoves state_308) = [55, 1, 3, 7, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_313, absent_314, absent_315, absent_316, absent_317, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_319 : compressed 3 1 [46, 47, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_320 : compressed 3 1 [44, 47, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_321 : compressed 3 1 [40, 47, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_322 : compressed 3 1 [14, 47, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_323 : compressed 3 1 [12, 47, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_324 : compressed 3 1 [8, 47, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_325 : compressed 3 0 [16, 47, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_326 : compressed 3 0 [1, 47, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_327 : compressed 3 0 [3, 47, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_328 : compressed 3 0 [7, 47, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_329 : compressed 3 0 [31, 47, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_318 : List W := [47, 15, 62, 60, 56, 48, 32, 0, 63]
theorem absent_318 : compressed 4 1 state_318 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_318)
    (by decide +kernel) absent_40 ?_ ?_
  · have moves : addable state_318 (binaryMoves state_318) = [46, 44, 40, 14, 12, 8] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_319, absent_320, absent_321, absent_322, absent_323, absent_324, Bool.false_or]
  · have moves : addable state_318 (unaryMoves state_318) = [16, 1, 3, 7, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_325, absent_326, absent_327, absent_328, absent_329, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_331 : compressed 3 0 [61, 1, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_332 : compressed 3 0 [57, 1, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_333 : compressed 3 0 [49, 1, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_334 : compressed 3 0 [33, 1, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_335 : compressed 3 0 [14, 1, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_336 : compressed 3 0 [12, 1, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_337 : compressed 3 0 [8, 1, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_338 : compressed 3 0 [47, 1, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_330 : List W := [1, 15, 62, 60, 56, 48, 32, 0, 63]
theorem absent_330 : compressed 4 0 state_330 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_330)
    (by decide +kernel) absent_41 ?_ ?_
  · have moves : addable state_330 (binaryMoves state_330) = [61, 57, 49, 33, 14, 12, 8, 47] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_331, absent_332, absent_333, absent_334, absent_335, absent_336, absent_337, absent_338, Bool.false_or]
  · rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_340 : compressed 3 0 [2, 3, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_341 : compressed 3 0 [59, 3, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_342 : compressed 3 0 [51, 3, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_343 : compressed 3 0 [35, 3, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_344 : compressed 3 0 [14, 3, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_345 : compressed 3 0 [12, 3, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_346 : compressed 3 0 [8, 3, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_347 : compressed 3 0 [47, 3, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_339 : List W := [3, 15, 62, 60, 56, 48, 32, 0, 63]
theorem absent_339 : compressed 4 0 state_339 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_339)
    (by decide +kernel) absent_42 ?_ ?_
  · have moves : addable state_339 (binaryMoves state_339) = [2, 59, 51, 35, 14, 12, 8, 47] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_340, absent_341, absent_342, absent_343, absent_344, absent_345, absent_346, absent_347, Bool.false_or]
  · rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_349 : compressed 3 0 [6, 7, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_350 : compressed 3 0 [4, 7, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_351 : compressed 3 0 [55, 7, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_352 : compressed 3 0 [39, 7, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_353 : compressed 3 0 [14, 7, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_354 : compressed 3 0 [12, 7, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_355 : compressed 3 0 [8, 7, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_356 : compressed 3 0 [47, 7, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_348 : List W := [7, 15, 62, 60, 56, 48, 32, 0, 63]
theorem absent_348 : compressed 4 0 state_348 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_348)
    (by decide +kernel) absent_43 ?_ ?_
  · have moves : addable state_348 (binaryMoves state_348) = [6, 4, 55, 39, 14, 12, 8, 47] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_349, absent_350, absent_351, absent_352, absent_353, absent_354, absent_355, absent_356, Bool.false_or]
  · rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_358 : compressed 3 0 [30, 31, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_359 : compressed 3 0 [28, 31, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_360 : compressed 3 0 [24, 31, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_361 : compressed 3 0 [16, 31, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_362 : compressed 3 0 [14, 31, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_363 : compressed 3 0 [12, 31, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_364 : compressed 3 0 [8, 31, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_365 : compressed 3 0 [47, 31, 15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_357 : List W := [31, 15, 62, 60, 56, 48, 32, 0, 63]
theorem absent_357 : compressed 4 0 state_357 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_357)
    (by decide +kernel) absent_44 ?_ ?_
  · have moves : addable state_357 (binaryMoves state_357) = [30, 28, 24, 16, 14, 12, 8, 47] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_358, absent_359, absent_360, absent_361, absent_362, absent_363, absent_364, absent_365, Bool.false_or]
  · rfl

abbrev state_287 : List W := [15, 62, 60, 56, 48, 32, 0, 63]
theorem absent_287 : compressed 5 1 state_287 = false := by
  refine compressed_step_false (k := 4) (n := 1) (bank := state_287)
    (by decide +kernel) absent_36 ?_ ?_
  · have moves : addable state_287 (binaryMoves state_287) = [14, 12, 8, 47] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_288, absent_298, absent_308, absent_318, Bool.false_or]
  · have moves : addable state_287 (unaryMoves state_287) = [1, 3, 7, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_330, absent_339, absent_348, absent_357, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_368 : compressed 3 1 [28, 30, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_369 : compressed 3 1 [24, 30, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_370 : compressed 3 1 [16, 30, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_371 : compressed 3 0 [33, 30, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_372 : compressed 3 0 [1, 30, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_373 : compressed 3 0 [3, 30, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_374 : compressed 3 0 [7, 30, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_375 : compressed 3 0 [15, 30, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_367 : List W := [30, 31, 62, 60, 56, 48, 32, 0, 63]
theorem absent_367 : compressed 4 1 state_367 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_367)
    (by decide +kernel) absent_46 ?_ ?_
  · have moves : addable state_367 (binaryMoves state_367) = [28, 24, 16] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_368, absent_369, absent_370, Bool.false_or]
  · have moves : addable state_367 (unaryMoves state_367) = [33, 1, 3, 7, 15] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_371, absent_372, absent_373, absent_374, absent_375, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_377 : compressed 3 1 [24, 28, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_378 : compressed 3 1 [16, 28, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_379 : compressed 3 1 [30, 28, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_380 : compressed 3 0 [35, 28, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_381 : compressed 3 0 [1, 28, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_382 : compressed 3 0 [3, 28, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_383 : compressed 3 0 [7, 28, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_384 : compressed 3 0 [15, 28, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_376 : List W := [28, 31, 62, 60, 56, 48, 32, 0, 63]
theorem absent_376 : compressed 4 1 state_376 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_376)
    (by decide +kernel) absent_47 ?_ ?_
  · have moves : addable state_376 (binaryMoves state_376) = [24, 16, 30] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_377, absent_378, absent_379, Bool.false_or]
  · have moves : addable state_376 (unaryMoves state_376) = [35, 1, 3, 7, 15] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_380, absent_381, absent_382, absent_383, absent_384, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_386 : compressed 3 1 [16, 24, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_387 : compressed 3 1 [30, 24, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_388 : compressed 3 1 [28, 24, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_389 : compressed 3 0 [39, 24, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_390 : compressed 3 0 [1, 24, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_391 : compressed 3 0 [3, 24, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_392 : compressed 3 0 [7, 24, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_393 : compressed 3 0 [15, 24, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_385 : List W := [24, 31, 62, 60, 56, 48, 32, 0, 63]
theorem absent_385 : compressed 4 1 state_385 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_385)
    (by decide +kernel) absent_48 ?_ ?_
  · have moves : addable state_385 (binaryMoves state_385) = [16, 30, 28] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_386, absent_387, absent_388, Bool.false_or]
  · have moves : addable state_385 (unaryMoves state_385) = [39, 1, 3, 7, 15] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_389, absent_390, absent_391, absent_392, absent_393, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_395 : compressed 3 1 [30, 16, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_396 : compressed 3 1 [28, 16, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_397 : compressed 3 1 [24, 16, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_398 : compressed 3 0 [47, 16, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_399 : compressed 3 0 [1, 16, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_400 : compressed 3 0 [3, 16, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_401 : compressed 3 0 [7, 16, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_402 : compressed 3 0 [15, 16, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_394 : List W := [16, 31, 62, 60, 56, 48, 32, 0, 63]
theorem absent_394 : compressed 4 1 state_394 = false := by
  refine compressed_step_false (k := 3) (n := 1) (bank := state_394)
    (by decide +kernel) absent_49 ?_ ?_
  · have moves : addable state_394 (binaryMoves state_394) = [30, 28, 24] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_395, absent_396, absent_397, Bool.false_or]
  · have moves : addable state_394 (unaryMoves state_394) = [47, 1, 3, 7, 15] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_398, absent_399, absent_400, absent_401, absent_402, Bool.false_or]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_404 : compressed 3 0 [61, 1, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_405 : compressed 3 0 [57, 1, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_406 : compressed 3 0 [49, 1, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_407 : compressed 3 0 [33, 1, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_408 : compressed 3 0 [30, 1, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_409 : compressed 3 0 [28, 1, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_410 : compressed 3 0 [24, 1, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_411 : compressed 3 0 [16, 1, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_403 : List W := [1, 31, 62, 60, 56, 48, 32, 0, 63]
theorem absent_403 : compressed 4 0 state_403 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_403)
    (by decide +kernel) absent_50 ?_ ?_
  · have moves : addable state_403 (binaryMoves state_403) = [61, 57, 49, 33, 30, 28, 24, 16] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_404, absent_405, absent_406, absent_407, absent_408, absent_409, absent_410, absent_411, Bool.false_or]
  · rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_413 : compressed 3 0 [2, 3, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_414 : compressed 3 0 [59, 3, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_415 : compressed 3 0 [51, 3, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_416 : compressed 3 0 [35, 3, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_417 : compressed 3 0 [30, 3, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_418 : compressed 3 0 [28, 3, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_419 : compressed 3 0 [24, 3, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_420 : compressed 3 0 [16, 3, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_412 : List W := [3, 31, 62, 60, 56, 48, 32, 0, 63]
theorem absent_412 : compressed 4 0 state_412 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_412)
    (by decide +kernel) absent_51 ?_ ?_
  · have moves : addable state_412 (binaryMoves state_412) = [2, 59, 51, 35, 30, 28, 24, 16] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_413, absent_414, absent_415, absent_416, absent_417, absent_418, absent_419, absent_420, Bool.false_or]
  · rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_422 : compressed 3 0 [6, 7, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_423 : compressed 3 0 [4, 7, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_424 : compressed 3 0 [55, 7, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_425 : compressed 3 0 [39, 7, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_426 : compressed 3 0 [30, 7, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_427 : compressed 3 0 [28, 7, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_428 : compressed 3 0 [24, 7, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_429 : compressed 3 0 [16, 7, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_421 : List W := [7, 31, 62, 60, 56, 48, 32, 0, 63]
theorem absent_421 : compressed 4 0 state_421 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_421)
    (by decide +kernel) absent_52 ?_ ?_
  · have moves : addable state_421 (binaryMoves state_421) = [6, 4, 55, 39, 30, 28, 24, 16] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_422, absent_423, absent_424, absent_425, absent_426, absent_427, absent_428, absent_429, Bool.false_or]
  · rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_431 : compressed 3 0 [14, 15, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_432 : compressed 3 0 [12, 15, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_433 : compressed 3 0 [8, 15, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_434 : compressed 3 0 [47, 15, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_435 : compressed 3 0 [30, 15, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_436 : compressed 3 0 [28, 15, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_437 : compressed 3 0 [24, 15, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem absent_438 : compressed 3 0 [16, 15, 31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

abbrev state_430 : List W := [15, 31, 62, 60, 56, 48, 32, 0, 63]
theorem absent_430 : compressed 4 0 state_430 = false := by
  refine compressed_step_false (k := 3) (n := 0) (bank := state_430)
    (by decide +kernel) absent_53 ?_ ?_
  · have moves : addable state_430 (binaryMoves state_430) = [14, 12, 8, 47, 30, 28, 24, 16] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_431, absent_432, absent_433, absent_434, absent_435, absent_436, absent_437, absent_438, Bool.false_or]
  · rfl

abbrev state_366 : List W := [31, 62, 60, 56, 48, 32, 0, 63]
theorem absent_366 : compressed 5 1 state_366 = false := by
  refine compressed_step_false (k := 4) (n := 1) (bank := state_366)
    (by decide +kernel) absent_45 ?_ ?_
  · have moves : addable state_366 (binaryMoves state_366) = [30, 28, 24, 16] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_367, absent_376, absent_385, absent_394, Bool.false_or]
  · have moves : addable state_366 (unaryMoves state_366) = [1, 3, 7, 15] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_403, absent_412, absent_421, absent_430, Bool.false_or]

abbrev state_0 : List W := [62, 60, 56, 48, 32, 0, 63]
theorem absent_0 : compressed 6 2 state_0 = false := by
  refine compressed_step_false (k := 5) (n := 2) (bank := state_0)
    (by decide +kernel) absent_1 ?_ ?_
  · have moves : addable state_0 (binaryMoves state_0) = [] := by decide +kernel
    rw [moves]
    rfl
  · have moves : addable state_0 (unaryMoves state_0) = [1, 3, 7, 15, 31] := by decide +kernel
    rw [moves]
    simp only [List.any_cons, List.any_nil, absent_54, absent_127, absent_206, absent_287, absent_366, Bool.false_or]

theorem compressed_rejected : compressed 6 2 roots = false := absent_0

theorem rejected : search 6 2 roots = false := by
  cases eq : search 6 2 roots with
  | false => rfl
  | true =>
    have impossible := compressed_complete 6 2 roots eq
    rw [compressed_rejected] at impossible
    exact Bool.noConfusion impossible

end PEqualNP.Outside.L_meta_51206

open PEqualNP.Outside.L_meta_51206 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_51206 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (10 : Nat).testBit t.val ∧
    w.getD q.val false = (12 : Nat).testBit t.val ∧
    w.getD r.val false = (35 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hfan, _, hnot, hsize, hs⟩
  have legal : ∀ g ∈ D.gates, fit g := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    exact ⟨by simpa using hop, hlen⟩
  let words := evalWords D.gates roots
  have one (i : Nat) (w : W) (hw : ∀ t : Fin 6, (D.wires (boolInputs t)).getD i false = bit t w) : readWord words i = w :=
    recover fun t => (read_circuit D legal t i).trans (hw t)
  have hp : readWord words p.val = 10 := one p.val 10 fun t => (hs t).1
  have hq : readWord words q.val = 12 := one q.val 12 fun t => (hs t).2.1
  have hr : readWord words r.val = 35 := one r.val 35 fun t => (hs t).2.2
  have present (i : Nat) (w : W) (hw : w ≠ 0) (eq : readWord words i = w) : w ∈ words := by
    unfold readWord at eq
    rw [List.getD_eq_getElem?_getD] at eq
    cases e : words[i]? with
    | none =>
        have hz : (0 : W) = w := by simpa only [e, Option.getD_none] using eq
        exact (hw hz.symm).elim
    | some x =>
        have h : x = w := by simpa only [e, Option.getD_some] using eq
        exact h ▸ List.mem_of_getElem? e
  have allGoals : ∀ w ∈ goals, w ∈ evalWords D.gates roots := by
    intro w hw
    simp [goals] at hw
    rcases hw with rfl | rfl | rfl
    · exact present p.val 10 (by decide) hp
    · exact present q.val 12 (by decide) hq
    · exact present r.val 35 (by decide) hr
  have actual := fits_search D.gates roots roots 6 2 legal (fun _ h => h)
     (by decide) (by decide) hsize hnot allGoals
  rw [rejected] at actual
  exact Bool.noConfusion actual
