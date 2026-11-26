import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18853_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Terms (n : ℕ) := List (List (Fin n))

def observe (x : Fin n → Bool) (p : Terms n) : Bool := p.any (fun l => l.all x)

def product (p q : Terms n) : Terms n := p.flatMap fun a => q.map fun b => a ++ b

theorem observeAppend (x : Fin n → Bool) (p q : Terms n) :
    observe x (p ++ q) = (observe x p || observe x q) := by
  simp only [observe, List.any_append]

theorem observeRowProduct (x : Fin n → Bool) (a : List (Fin n)) (q : Terms n) :
    observe x (q.map fun b => a ++ b) = (a.all x && observe x q) := by
  induction q with
  | nil => simp [observe]
  | cons b q ih =>
    have step :
        ((a.all x && b.all x) || (a.all x && observe x q)) =
          (a.all x && (b.all x || observe x q)) := by
      cases h : a.all x <;> simp [h]
    calc
      observe x ((b :: q).map fun b => a ++ b) =
          ((a.all x && b.all x) || observe x (q.map fun b => a ++ b)) := by
        simp only [List.map_cons, observe, List.any_cons, List.all_append]
      _ = (a.all x && (b.all x || observe x q)) := by rw [ih]; exact step
      _ = (a.all x && observe x (b :: q)) := rfl

theorem observeProduct (x : Fin n → Bool) (p q : Terms n) :
    observe x (product p q) = (observe x p && observe x q) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change observe x ((q.map fun b => a ++ b) ++ product p q) =
      ((a.all x || observe x p) && observe x q)
    rw [observeAppend, observeRowProduct, ih]
    cases h : observe x q <;> simp [h]

def pureFamily (p : Terms n) : Finset (Finset (Fin n)) := (p.map List.toFinset).toFinset

theorem observe_of_subset (x : Fin n → Bool) (p q : Terms n) (sub : pureFamily p ⊆ pureFamily q)
    (yes : observe x p = true) : observe x q = true := by
  obtain ⟨a, ma, ok⟩ := List.any_eq_true.mp yes
  have ha : a.toFinset ∈ pureFamily p :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ma, rfl⟩)
  obtain ⟨b, mb, eq⟩ := List.mem_map.mp (List.mem_toFinset.mp (sub ha))
  apply List.any_eq_true.mpr
  refine ⟨b, mb, List.all_eq_true.mpr ?_⟩
  intro i mi
  have h : i ∈ b.toFinset := List.mem_toFinset.mpr mi
  rw [eq] at h
  exact List.all_eq_true.mp ok i (List.mem_toFinset.mp h)

theorem observe_same (x : Fin n → Bool) (p q : Terms n) (eq : pureFamily p = pureFamily q) :
    observe x p = observe x q := by
  cases hp : observe x p <;> cases hq : observe x q
  · rfl
  · have hn := observe_of_subset x q p (by rw [eq]) hq
    simp [hp] at hn
  · have hn := observe_of_subset x p q (by rw [eq]) hp
    simp [hq] at hn
  · rfl

def allTerms (xs : List (Terms n)) : Terms n := xs.foldr product [[]]
def anyTerms (xs : List (Terms n)) : Terms n := xs.foldr List.append []

theorem allMatches (x : Fin n → Bool) (xs : List (Terms n)) :
    observe x (allTerms xs) = (xs.map (observe x)).all id := by
  induction xs with
  | nil => rfl
  | cons p tail ih =>
    change observe x (product p (allTerms tail)) =
      (observe x p && (tail.map (observe x)).all id)
    rw [observeProduct, ih]

theorem anyMatches (x : Fin n → Bool) (xs : List (Terms n)) :
    observe x (anyTerms xs) = (xs.map (observe x)).any id := by
  induction xs with
  | nil => rfl
  | cons p tail ih =>
    change observe x (p ++ anyTerms tail) =
      (observe x p || (tail.map (observe x)).any id)
    rw [observeAppend, ih]

theorem observedRead (x : Fin n → Bool) (xs : List (Terms n)) (i : ℕ) :
    observe x (xs.getD i []) = (xs.map (observe x)).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : xs[i]? <;> simp [observe, h]


def termGate {n : ℕ} (op : GateOp) (xs : List (Terms n)) : Terms n :=
  match op with
  | .and => allTerms xs
  | .or => anyTerms xs
  | _ => []

theorem gateMatches (x : Fin n → Bool) (g : Gate) (ws : List (Terms n))
    (ops : g.op = .and ∨ g.op = .or) :
    observe x (termGate g.op (g.inputs.map (fun i => ws.getD i []))) =
      g.op.eval (g.inputs.map (fun i => (ws.map (observe x)).getD i false)) := by
  have reads : (g.inputs.map (fun i => ws.getD i [])).map (observe x) =
      g.inputs.map (fun i => (ws.map (observe x)).getD i false) := by
    rw [List.map_map]
    congr 1
    funext i
    exact observedRead x ws i
  rcases ops with h | h
  · rw [h]
    change observe x (allTerms _) = _
    rw [allMatches, reads]
    rfl
  · rw [h]
    change observe x (anyTerms _) = _
    rw [anyMatches, reads]
    rfl

def symbolicRun {n : ℕ} : List Gate → List (Terms n) → List (Terms n)
  | [], ws => ws
  | g :: gs, ws => symbolicRun gs (ws ++ [termGate g.op (g.inputs.map (fun i => ws.getD i []))])

theorem runMatches (x : Fin n → Bool) (gs : List Gate) (ws : List (Terms n))
    (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    (symbolicRun gs ws).map (observe x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])
        (ws.map (observe x)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [symbolicRun, List.foldl_cons]
    rw [ih _ (fun g' hg' => ops g' (List.mem_cons_of_mem _ hg'))]
    simp only [List.map_append, List.map_singleton]
    rw [gateMatches x g ws (ops g (by simp))]

def termInput {n : ℕ} (i : Fin n) : Terms n := [[i]]

theorem termInputMatches (x : Fin n → Bool) (i : Fin n) :
    observe x (termInput i) = x i := by
  simp [observe, termInput]

def circuitTerms (n : ℕ) (C : Circuit) : Terms n :=
  (symbolicRun C.gates (List.ofFn termInput)).getD C.output []

theorem circuitMatches (C : Circuit) (x : Fin n → Bool)
    (ops : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or) :
    observe x (circuitTerms n C) = C.eval (List.ofFn x) := by
  have inputs : (List.ofFn termInput).map (observe x) = List.ofFn x := by
    rw [List.map_ofFn]
    exact congrArg (fun f : Fin n → Bool => List.ofFn f) (funext (termInputMatches x))
  unfold circuitTerms Circuit.eval Circuit.wires
  rw [observedRead, runMatches x C.gates _ ops, inputs]

def witness : Circuit :=
  ⟨[⟨.and, [0, 7]⟩,⟨.and, [0, 8]⟩,⟨.and, [0, 9]⟩,⟨.and, [1, 5]⟩,⟨.and, [1, 6]⟩,⟨.and, [1, 9]⟩,⟨.and, [2, 4]⟩,⟨.and, [2, 6]⟩,⟨.and, [2, 8]⟩,⟨.and, [3, 4]⟩,⟨.and, [3, 5]⟩,⟨.and, [3, 7]⟩,⟨.and, [4, 9]⟩,⟨.and, [5, 8]⟩,⟨.and, [6, 7]⟩,⟨.or, [12, 22]⟩,⟨.or, [15, 22]⟩,⟨.or, [16, 23]⟩,⟨.or, [19, 24]⟩,⟨.or, [10, 18]⟩,⟨.or, [13, 17]⟩,⟨.or, [16, 24]⟩,⟨.or, [17, 18]⟩,⟨.or, [19, 23]⟩,⟨.or, [20, 21]⟩,⟨.or, [23, 24]⟩,⟨.or, [25, 27]⟩,⟨.or, [25, 28]⟩,⟨.or, [26, 31]⟩,⟨.or, [26, 33]⟩,⟨.or, [27, 28]⟩,⟨.or, [32, 39]⟩,⟨.and, [10, 41]⟩,⟨.or, [30, 34]⟩,⟨.or, [43, 38]⟩,⟨.and, [11, 44]⟩,⟨.or, [12, 15]⟩,⟨.and, [46, 40]⟩,⟨.or, [32, 37]⟩,⟨.and, [13, 48]⟩,⟨.or, [29, 34]⟩,⟨.or, [50, 36]⟩,⟨.and, [14, 51]⟩,⟨.or, [16, 19]⟩,⟨.and, [53, 35]⟩,⟨.and, [17, 39]⟩,⟨.and, [18, 37]⟩,⟨.or, [29, 38]⟩,⟨.and, [20, 57]⟩,⟨.or, [30, 36]⟩,⟨.and, [21, 59]⟩,⟨.or, [42, 45]⟩,⟨.or, [61, 47]⟩,⟨.or, [62, 49]⟩,⟨.or, [63, 52]⟩,⟨.or, [64, 54]⟩,⟨.or, [65, 55]⟩,⟨.or, [66, 56]⟩,⟨.or, [67, 58]⟩,⟨.or, [68, 60]⟩], 69⟩

def expected : Terms 10 := [[0,1,5,8],[0,1,5,9],[0,1,6,7],[0,1,6,9],[0,1,7,9],[0,1,8,9],[0,2,4,8],[0,2,4,9],[0,2,6,7],[0,2,6,8],[0,2,7,8],[0,2,8,9],[0,3,4,7],[0,3,4,9],[0,3,5,7],[0,3,5,8],[0,3,7,8],[0,3,7,9],[0,4,7,9],[0,4,8,9],[0,5,7,8],[0,5,8,9],[0,6,7,8],[0,6,7,9],[1,2,4,6],[1,2,4,9],[1,2,5,6],[1,2,5,8],[1,2,6,8],[1,2,6,9],[1,3,4,5],[1,3,4,9],[1,3,5,6],[1,3,5,7],[1,3,5,9],[1,3,6,7],[1,4,5,9],[1,4,6,9],[1,5,6,7],[1,5,6,8],[1,5,8,9],[1,6,7,9],[2,3,4,5],[2,3,4,6],[2,3,4,7],[2,3,4,8],[2,3,5,8],[2,3,6,7],[2,4,5,8],[2,4,6,7],[2,4,6,9],[2,4,8,9],[2,5,6,8],[2,6,7,8],[3,4,5,8],[3,4,5,9],[3,4,6,7],[3,4,7,9],[3,5,6,7],[3,5,7,8]]

set_option maxRecDepth 8000 in
theorem permitted : ∀ g ∈ witness.gates, g.op = .and ∨ g.op = .or := by
  simp [witness]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 18000000 in
theorem termsMatch : pureFamily (circuitTerms 10 witness) = pureFamily expected := by
  decide +kernel

theorem correctness (x : Fin 10 → Bool) :
    witness.eval (List.ofFn x) = observe x expected :=
  (circuitMatches witness x permitted).symm.trans
    (observe_same x (circuitTerms 10 witness) expected termsMatch)

def officialTerms : Terms 10 := [[0,4,7,9],[0,4,8,9],[0,5,7,8],[0,5,9,8],[0,6,8,7],[0,6,9,7],[1,4,5,9],[1,4,6,9],[1,7,5,6],[1,7,9,6],[1,8,6,5],[1,8,9,5],[2,5,4,8],[2,5,6,8],[2,7,4,6],[2,7,8,6],[2,9,6,4],[2,9,8,4],[3,6,4,7],[3,6,5,7],[3,8,4,5],[3,8,7,5],[3,9,5,4],[3,9,7,4],[0,1,7,9],[0,1,8,9],[0,2,7,8],[0,2,9,8],[0,3,8,7],[0,3,9,7],[4,1,2,9],[4,1,3,9],[4,7,2,3],[4,8,3,2],[5,2,1,8],[5,2,3,8],[5,7,1,3],[5,9,3,1],[6,3,1,7],[6,3,2,7],[6,8,1,2],[6,9,2,1],[1,0,5,9],[1,0,6,9],[1,2,5,6],[1,3,6,5],[4,0,2,9],[4,0,3,9],[4,5,2,3],[4,6,3,2],[7,2,0,6],[7,5,0,3],[8,3,0,5],[8,6,0,2],[2,0,4,8],[2,1,4,6],[5,0,1,8],[5,4,1,3],[7,1,0,6],[7,4,0,3]]

set_option maxRecDepth 12000 in
theorem sameTerms : pureFamily expected = pureFamily officialTerms := by
  decide +kernel

end PEqualNP.Outside.L_meta_18853_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_18853_aux in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.L_meta_18853 : PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => (x 0 && x 4 && x 7 && x 9) || (x 0 && x 4 && x 8 && x 9) || (x 0 && x 5 && x 7 && x 8) || (x 0 && x 5 && x 9 && x 8) || (x 0 && x 6 && x 8 && x 7) || (x 0 && x 6 && x 9 && x 7) || (x 1 && x 4 && x 5 && x 9) || (x 1 && x 4 && x 6 && x 9) || (x 1 && x 7 && x 5 && x 6) || (x 1 && x 7 && x 9 && x 6) || (x 1 && x 8 && x 6 && x 5) || (x 1 && x 8 && x 9 && x 5) || (x 2 && x 5 && x 4 && x 8) || (x 2 && x 5 && x 6 && x 8) || (x 2 && x 7 && x 4 && x 6) || (x 2 && x 7 && x 8 && x 6) || (x 2 && x 9 && x 6 && x 4) || (x 2 && x 9 && x 8 && x 4) || (x 3 && x 6 && x 4 && x 7) || (x 3 && x 6 && x 5 && x 7) || (x 3 && x 8 && x 4 && x 5) || (x 3 && x 8 && x 7 && x 5) || (x 3 && x 9 && x 5 && x 4) || (x 3 && x 9 && x 7 && x 4) || (x 0 && x 1 && x 7 && x 9) || (x 0 && x 1 && x 8 && x 9) || (x 0 && x 2 && x 7 && x 8) || (x 0 && x 2 && x 9 && x 8) || (x 0 && x 3 && x 8 && x 7) || (x 0 && x 3 && x 9 && x 7) || (x 4 && x 1 && x 2 && x 9) || (x 4 && x 1 && x 3 && x 9) || (x 4 && x 7 && x 2 && x 3) || (x 4 && x 8 && x 3 && x 2) || (x 5 && x 2 && x 1 && x 8) || (x 5 && x 2 && x 3 && x 8) || (x 5 && x 7 && x 1 && x 3) || (x 5 && x 9 && x 3 && x 1) || (x 6 && x 3 && x 1 && x 7) || (x 6 && x 3 && x 2 && x 7) || (x 6 && x 8 && x 1 && x 2) || (x 6 && x 9 && x 2 && x 1) || (x 1 && x 0 && x 5 && x 9) || (x 1 && x 0 && x 6 && x 9) || (x 1 && x 2 && x 5 && x 6) || (x 1 && x 3 && x 6 && x 5) || (x 4 && x 0 && x 2 && x 9) || (x 4 && x 0 && x 3 && x 9) || (x 4 && x 5 && x 2 && x 3) || (x 4 && x 6 && x 3 && x 2) || (x 7 && x 2 && x 0 && x 6) || (x 7 && x 5 && x 0 && x 3) || (x 8 && x 3 && x 0 && x 5) || (x 8 && x 6 && x 0 && x 2) || (x 2 && x 0 && x 4 && x 8) || (x 2 && x 1 && x 4 && x 6) || (x 5 && x 0 && x 1 && x 8) || (x 5 && x 4 && x 1 && x 3) || (x 7 && x 1 && x 0 && x 6) || (x 7 && x 4 && x 0 && x 3)) 75 := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · simp [witness, FanInTwo]
  · intro x
    rw [correctness, observe_same x expected officialTerms sameTerms]
    simp only [observe, officialTerms, List.any_cons, List.any_nil, List.all_cons, List.all_nil,
      Bool.and_true, Bool.or_false, Bool.and_assoc, Bool.or_assoc]
