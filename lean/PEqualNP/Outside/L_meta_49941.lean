import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_49941

abbrev Word := BitVec 5

def inputBank : List Word := [30, 28, 24, 16, 0, 31]

def target : List Word := [5, 21, 22]

def extend (bank : List Word) (v : Word) : List Word :=
  if v ∈ bank then bank else v :: bank

def options (bank : List Word) : List Word :=
  (bank ++ bank.map (~~~ ·) ++ bank.flatMap
    (fun a => bank.flatMap fun b => [a &&& b, a ||| b])).eraseDups

def success (bank : List Word) : Bool :=
  target.all fun v => decide (v ∈ bank)

def fresh (bank : List Word) : List Word :=
  (options bank).filter fun v => decide (v ∉ bank)

def missing (bank : List Word) : ℕ :=
  (target.toFinset \ bank.toFinset).card

def scan : ℕ → List Word → Bool
  | 0, bank => success bank
  | n + 1, bank =>
    if missing bank ≤ n + 1 then
      success bank || scan n bank || (fresh bank).any (fun v => scan n (extend bank v))
    else false

def stepWord (w : List Word) (g : Gate) : Word :=
  match g.op, g.inputs with
  | .and, [] => 31
  | .or, [] => 0
  | .and, [i] | .or, [i] => w.getD i 0
  | .and, i :: j :: _ => w.getD i 0 &&& w.getD j 0
  | .or, i :: j :: _ => w.getD i 0 ||| w.getD j 0
  | .not, [] => 31
  | .not, i :: _ => ~~~(w.getD i 0)
  | _, _ => 0

def run (gs : List Gate) (w : List Word) : List Word :=
  gs.foldl (fun w g => w ++ [stepWord w g]) w

def row (t : Fin 5) (w : List Word) : List Bool :=
  w.map (fun v => v.getLsbD t.val)

def binary (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

theorem readDefault (w : List Word) (i : ℕ) :
    w.getD i 0 ∈ w ∨ w.getD i 0 = 0 := by
  simp only [List.getD]
  cases e : w[i]? with
  | none => exact Or.inr rfl
  | some a =>
    exact Or.inl (List.mem_of_getElem? e)

theorem rowGet (t : Fin 5) (w : List Word) (i : ℕ) :
    (row t w).getD i false = (w.getD i 0).getLsbD t.val := by
  simp only [row, List.getD, List.getElem?_map]
  cases w[i]? <;> simp

theorem stepSound (g : Gate) (h : binary g) (w : List Word) (t : Fin 5) :
    (stepWord w g).getLsbD t.val =
      g.op.eval (g.inputs.map fun i => (row t w).getD i false) := by
  rcases g with ⟨op, ins⟩
  obtain ⟨allowed, arity⟩ := h
  change op = .and ∨ op = .or ∨ op = .not at allowed
  change ins.length ≤ 2 at arity
  have hread (i : ℕ) : ((row t w)[i]?).getD false = ((w[i]?).getD 0).getLsbD t.val :=
    rowGet t w i
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, more⟩⟩⟩
  · rcases allowed with rfl | rfl | rfl <;> fin_cases t <;> simp [stepWord, GateOp.eval]
  · rcases allowed with rfl | rfl | rfl <;>
      simp [stepWord, GateOp.eval, hread, t.isLt]
  · rcases allowed with rfl | rfl | rfl <;>
      simp [stepWord, GateOp.eval, hread, t.isLt]
  · simp at arity

theorem runSound (gs : List Gate) (w : List Word) (t : Fin 5)
    (h : ∀ g ∈ gs, binary g) :
    row t (run gs w) = Circuit.wires ⟨gs, 0⟩ (row t w) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [run, Circuit.wires, List.foldl_cons] at ih ⊢
    rw [ih (w ++ [stepWord w g]) (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [row, List.map_append, List.map_cons, List.map_nil, stepSound g (h g (by simp))]

theorem memberInOptions {w bank : List Word} (h : ∀ a ∈ w, a ∈ bank)
    (zero : (0 : Word) ∈ bank) (one : (31 : Word) ∈ bank) (g : Gate) :
    stepWord w g ∈ options bank := by
  have get (i : ℕ) : w.getD i 0 ∈ bank := by
    rcases readDefault w i with hi | hi
    · exact h _ hi
    · simpa only [hi] using zero
  have old (a : Word) (ha : a ∈ bank) : a ∈ options bank := by
    simp [options, ha]
  have invert (a : Word) (ha : a ∈ bank) : (~~~a) ∈ options bank := by
    simp only [options, List.mem_eraseDups, List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨a, ha, rfl⟩)
  have join (a b : Word) (ha : a ∈ bank) (hb : b ∈ bank) :
      (a &&& b) ∈ options bank ∧ (a ||| b) ∈ options bank := by
    simp only [options, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
    exact ⟨Or.inr ⟨a, ha, b, hb, by simp⟩, Or.inr ⟨a, ha, b, hb, by simp⟩⟩
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;>
    simp only [stepWord] <;>
    first | exact old 0 zero | exact old 31 one | exact old _ (get _) |
      exact invert _ (get _) | exact (join _ _ (get _) (get _)).1 |
      exact (join _ _ (get _) (get _)).2

theorem memExtend (bank : List Word) (v x : Word) :
    (x ∈ bank ∨ x = v) → x ∈ extend bank v := by
  by_cases hv : v ∈ bank
  · simp only [extend, if_pos hv]
    rintro (hx | rfl)
    · exact hx
    · exact hv
  · simp only [extend, if_neg hv, List.mem_cons]
    rintro (hx | eq)
    · exact Or.inr hx
    · exact Or.inl eq

theorem runParts (gs : List Gate) (w : List Word) :
    ∃ tail : List Word, run gs w = w ++ tail ∧ tail.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    let v := stepWord w g
    obtain ⟨tail, eq, len⟩ := ih (w ++ [v])
    refine ⟨v :: tail, ?_, by simp [len]⟩
    simpa [run, v, List.append_assoc] using eq

theorem missingLe (gs : List Gate) (w bank : List Word)
    (hw : ∀ a ∈ w, a ∈ bank) (ht : ∀ a ∈ target, a ∈ run gs w) :
    missing bank ≤ gs.length := by
  obtain ⟨tail, eq, len⟩ := runParts gs w
  have subset : target.toFinset \ bank.toFinset ⊆ tail.toFinset := by
    intro v hv
    obtain ⟨vTarget, vMissing⟩ := Finset.mem_sdiff.mp hv
    have h := ht v (List.mem_toFinset.mp vTarget)
    rw [eq, List.mem_append] at h
    exact List.mem_toFinset.mpr
      (h.resolve_left (fun vW => vMissing (List.mem_toFinset.mpr (hw v vW))))
  calc
    missing bank ≤ tail.toFinset.card := Finset.card_le_card subset
    _ ≤ tail.length := List.toFinset_card_le tail
    _ = gs.length := len

theorem scanComplete (fuel : ℕ) (gs : List Gate) (w bank : List Word)
    (hw : ∀ a ∈ w, a ∈ bank) (zero : (0 : Word) ∈ bank) (one : (31 : Word) ∈ bank)
    (sz : gs.length ≤ fuel) (ht : ∀ a ∈ target, a ∈ run gs w) : scan fuel bank = true := by
  induction fuel generalizing gs w bank with
  | zero =>
    have hg : gs = [] := List.length_eq_zero_iff.mp (by omega)
    subst gs
    simp only [scan, success, List.all_eq_true, decide_eq_true_eq]
    exact fun a ha => hw a (ht a ha)
  | succ n ih =>
    have enough := (missingLe gs w bank hw ht).trans sz
    simp only [scan, if_pos enough, Bool.or_eq_true, List.any_eq_true]
    rcases gs with _ | ⟨g, gs⟩
    · exact Or.inl (Or.inl (List.all_eq_true.mpr (fun a ha => decide_eq_true (hw a (ht a ha)))))
    · let v := stepWord w g
      have len : gs.length ≤ n := by simpa using sz
      have ht' : ∀ a ∈ target, a ∈ run gs (w ++ [v]) := ht
      by_cases hv : v ∈ bank
      · left
        right
        refine ih gs (w ++ [v]) bank ?_ zero one len ht'
        intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        exact ha.elim (hw a) (fun h => h.symm ▸ hv)
      · right
        have hf : v ∈ fresh bank := by
          simp [fresh, memberInOptions hw zero one g, hv, v]
        refine ⟨v, hf, ih gs (w ++ [v]) (extend bank v) ?_ ?_ ?_ len ht'⟩
        · intro a ha
          simp only [List.mem_append, List.mem_singleton] at ha
          exact memExtend bank v a (ha.imp (hw a) id)
        · exact memExtend bank v 0 (Or.inl zero)
        · exact memExtend bank v 31 (Or.inl one)

theorem inputRows : ∀ t : Fin 5,
    row t inputBank = List.ofFn (fun i : Fin 4 => decide (i.val < t.val)) ++ [false, true] := by
  decide +kernel

theorem scanNoStep (n : ℕ) (bank : List Word)
    (hEmpty : success bank = false) (hSkip : scan n bank = false)
    (hExtend : ∀ v ∈ fresh bank, scan n (extend bank v) = false) :
    scan (n + 1) bank = false := by
  rw [scan]
  split
  · have hn : (fresh bank).any (fun v => scan n (extend bank v)) = false :=
      List.any_eq_false.mpr (fun v hv => by simp [hExtend v hv])
    simp [hEmpty, hSkip, hn]
  · rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
theorem noFiveAtStart : scan 5 inputBank = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
theorem noFiveAfterOne : scan 5 (extend inputBank 1) = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
theorem noFiveAfterThree : scan 5 (extend inputBank 3) = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
theorem noFiveAfterSeven : scan 5 (extend inputBank 7) = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
theorem noFiveAfterFifteen : scan 5 (extend inputBank 15) = false := by
  decide +kernel

theorem exhaustive : scan 6 inputBank = false := by
  apply scanNoStep
  · decide +kernel
  · exact noFiveAtStart
  · intro v hv
    have hs : fresh inputBank = [1, 3, 7, 15] := by decide +kernel
    rw [hs] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact noFiveAfterOne
    · exact noFiveAfterThree
    · exact noFiveAfterSeven
    · exact noFiveAfterFifteen

theorem noSix (D : Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D) (sz : D.size ≤ 6)
    (p q r : Fin (6 + D.size))
    (eval : ∀ t : Fin 5,
      let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true]
      let w := D.wires xs
      w.getD p.val false = (5 : Nat).testBit t.val ∧
      w.getD q.val false = (21 : Nat).testBit t.val ∧
      w.getD r.val false = (22 : Nat).testBit t.val) : False := by
  have hBinary : ∀ g ∈ D.gates, binary g := by
    intro g hg
    have hh := hD g hg
    simpa [binary] using hh
  have rows : ∀ t : Fin 5,
      row t (run D.gates inputBank) = D.wires (row t inputBank) :=
    fun t => runSound D.gates inputBank t hBinary
  have allTargets : ∀ v ∈ target, v ∈ run D.gates inputBank := by
    intro v hv
    simp only [target, List.mem_cons, List.not_mem_nil, or_false] at hv
    have every (i : ℕ) (v : Word)
        (he : ∀ t : Fin 5, (D.wires (row t inputBank)).getD i false = v.getLsbD t.val)
        (nz : v ≠ 0) : v ∈ run D.gates inputBank := by
      have eq : (run D.gates inputBank).getD i 0 = v := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        let t : Fin 5 := ⟨j, hj⟩
        exact (rowGet t _ i).symm.trans (congrArg (fun l : List Bool => l.getD i false) (rows t) |>.trans (he t))
      rcases readDefault (run D.gates inputBank) i with h | h
      · rwa [eq] at h
      · rw [eq] at h
        exact (nz h).elim
    rcases hv with rfl | rfl | rfl
    · exact every p.val 5 (fun t => by
        rw [inputRows]
        exact (eval t).1) (by decide)
    · exact every q.val 21 (fun t => by
        rw [inputRows]
        exact (eval t).2.1) (by decide)
    · exact every r.val 22 (fun t => by
        rw [inputRows]
        exact (eval t).2.2) (by decide)
  have yes := scanComplete 6 D.gates inputBank inputBank
    (fun _ h => h) (by decide) (by decide) sz allTargets
  rw [exhaustive] at yes
  contradiction

end PEqualNP.Outside.L_meta_49941

theorem PEqualNP.Outside.L_meta_49941 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (5 : Nat).testBit t.val ∧
    w.getD q.val false = (21 : Nat).testBit t.val ∧
    w.getD r.val false = (22 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hD, _, _, hs, heval⟩
  exact PEqualNP.Outside.L_meta_49941.noSix D hD hs p q r heval
