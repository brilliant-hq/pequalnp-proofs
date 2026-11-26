import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9768

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
  ⟨[⟨.or, [26, 28]⟩, ⟨.or, [38, 41]⟩, ⟨.or, [42, 43]⟩, ⟨.and, [0, 44]⟩, ⟨.or, [21, 22]⟩, ⟨.or, [27, 29]⟩, ⟨.or, [46, 47]⟩, ⟨.or, [48, 39]⟩, ⟨.and, [1, 49]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [28, 30]⟩, ⟨.or, [51, 52]⟩, ⟨.or, [53, 40]⟩, ⟨.and, [2, 54]⟩, ⟨.or, [23, 24]⟩, ⟨.or, [29, 31]⟩, ⟨.or, [56, 57]⟩, ⟨.or, [58, 41]⟩, ⟨.and, [3, 59]⟩, ⟨.or, [21, 24]⟩, ⟨.or, [25, 30]⟩, ⟨.or, [61, 62]⟩, ⟨.or, [63, 32]⟩, ⟨.and, [4, 64]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [26, 31]⟩, ⟨.or, [66, 67]⟩, ⟨.or, [68, 33]⟩, ⟨.and, [5, 69]⟩, ⟨.or, [23, 26]⟩, ⟨.or, [27, 32]⟩, ⟨.or, [71, 72]⟩, ⟨.or, [73, 34]⟩, ⟨.and, [6, 74]⟩, ⟨.or, [24, 27]⟩, ⟨.or, [28, 33]⟩, ⟨.or, [76, 77]⟩, ⟨.or, [78, 35]⟩, ⟨.and, [7, 79]⟩, ⟨.or, [25, 28]⟩, ⟨.or, [29, 34]⟩, ⟨.or, [81, 82]⟩, ⟨.or, [83, 36]⟩, ⟨.and, [8, 84]⟩, ⟨.or, [26, 29]⟩, ⟨.or, [30, 35]⟩, ⟨.or, [86, 87]⟩, ⟨.or, [88, 37]⟩, ⟨.and, [9, 89]⟩, ⟨.or, [27, 30]⟩, ⟨.or, [31, 36]⟩, ⟨.or, [91, 92]⟩, ⟨.or, [93, 38]⟩, ⟨.and, [10, 94]⟩, ⟨.or, [28, 31]⟩, ⟨.or, [32, 37]⟩, ⟨.or, [96, 97]⟩, ⟨.or, [98, 39]⟩, ⟨.and, [11, 99]⟩, ⟨.or, [29, 32]⟩, ⟨.or, [33, 38]⟩, ⟨.or, [101, 102]⟩, ⟨.or, [103, 40]⟩, ⟨.and, [12, 104]⟩, ⟨.or, [30, 33]⟩, ⟨.or, [34, 39]⟩, ⟨.or, [106, 107]⟩, ⟨.or, [108, 41]⟩, ⟨.and, [13, 109]⟩, ⟨.or, [21, 31]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [111, 112]⟩, ⟨.or, [113, 40]⟩, ⟨.and, [14, 114]⟩, ⟨.or, [22, 32]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [116, 117]⟩, ⟨.or, [118, 41]⟩, ⟨.and, [15, 119]⟩, ⟨.or, [21, 23]⟩, ⟨.or, [33, 36]⟩, ⟨.or, [121, 122]⟩, ⟨.or, [123, 37]⟩, ⟨.and, [16, 124]⟩, ⟨.or, [22, 24]⟩, ⟨.or, [34, 37]⟩, ⟨.or, [126, 127]⟩, ⟨.or, [128, 38]⟩, ⟨.and, [17, 129]⟩, ⟨.or, [23, 25]⟩, ⟨.or, [35, 38]⟩, ⟨.or, [131, 132]⟩, ⟨.or, [133, 39]⟩, ⟨.and, [18, 134]⟩, ⟨.or, [24, 26]⟩, ⟨.or, [36, 39]⟩, ⟨.or, [136, 137]⟩, ⟨.or, [138, 40]⟩, ⟨.and, [19, 139]⟩, ⟨.or, [25, 27]⟩, ⟨.or, [37, 40]⟩, ⟨.or, [141, 142]⟩, ⟨.or, [143, 41]⟩, ⟨.and, [20, 144]⟩, ⟨.or, [45, 50]⟩, ⟨.or, [55, 60]⟩, ⟨.or, [65, 70]⟩, ⟨.or, [75, 80]⟩, ⟨.or, [85, 90]⟩, ⟨.or, [95, 100]⟩, ⟨.or, [105, 110]⟩, ⟨.or, [115, 120]⟩, ⟨.or, [125, 130]⟩, ⟨.or, [135, 140]⟩, ⟨.or, [146, 147]⟩, ⟨.or, [148, 149]⟩, ⟨.or, [150, 151]⟩, ⟨.or, [152, 153]⟩, ⟨.or, [154, 155]⟩, ⟨.or, [156, 157]⟩, ⟨.or, [158, 159]⟩, ⟨.or, [160, 145]⟩, ⟨.or, [161, 162]⟩, ⟨.or, [164, 163]⟩], 165⟩

def expected : Terms 42 :=
  [[0,26], [0,28], [0,38], [0,41], [1,21], [1,22], [1,27], [1,29], [1,39], [2,22], [2,23], [2,28], [2,30], [2,40], [3,23], [3,24], [3,29], [3,31], [3,41], [4,21], [4,24], [4,25], [4,30], [4,32], [5,22], [5,25], [5,26], [5,31], [5,33], [6,23], [6,26], [6,27], [6,32], [6,34], [7,24], [7,27], [7,28], [7,33], [7,35], [8,25], [8,28], [8,29], [8,34], [8,36], [9,26], [9,29], [9,30], [9,35], [9,37], [10,27], [10,30], [10,31], [10,36], [10,38], [11,28], [11,31], [11,32], [11,37], [11,39], [12,29], [12,32], [12,33], [12,38], [12,40], [13,30], [13,33], [13,34], [13,39], [13,41], [14,21], [14,31], [14,34], [14,35], [14,40], [15,22], [15,32], [15,35], [15,36], [15,41], [16,21], [16,23], [16,33], [16,36], [16,37], [17,22], [17,24], [17,34], [17,37], [17,38], [18,23], [18,25], [18,35], [18,38], [18,39], [19,24], [19,26], [19,36], [19,39], [19,40], [20,25], [20,27], [20,37], [20,40], [20,41]]

set_option maxRecDepth 8000 in
theorem permitted : ∀ g ∈ witness.gates, g.op = .and ∨ g.op = .or := by
  simp [witness]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 18000000 in
theorem termsMatch : pureFamily (circuitTerms 42 witness) = pureFamily expected := by
  decide +kernel

theorem correctness (x : Fin 42 → Bool) :
    witness.eval (List.ofFn x) = observe x expected :=
  (circuitMatches witness x permitted).symm.trans
    (observe_same x (circuitTerms 42 witness) expected termsMatch)


def officialTerms : Terms 42 :=
  [[0,26], [0,28], [0,38], [0,41], [1,21], [1,22], [1,27], [1,29], [1,39], [2,22], [2,23], [2,28], [2,30], [2,40], [3,23], [3,24], [3,29], [3,31], [3,41], [4,21], [4,24], [4,25], [4,30], [4,32], [5,22], [5,25], [5,26], [5,31], [5,33], [6,23], [6,26], [6,27], [6,32], [6,34], [7,24], [7,27], [7,28], [7,33], [7,35], [8,25], [8,28], [8,29], [8,34], [8,36], [9,26], [9,29], [9,30], [9,35], [9,37], [10,27], [10,30], [10,31], [10,36], [10,38], [11,28], [11,31], [11,32], [11,37], [11,39], [12,29], [12,32], [12,33], [12,38], [12,40], [13,30], [13,33], [13,34], [13,39], [13,41], [14,21], [14,31], [14,34], [14,35], [14,40], [15,22], [15,32], [15,35], [15,36], [15,41], [16,21], [16,23], [16,33], [16,36], [16,37], [17,22], [17,24], [17,34], [17,37], [17,38], [18,23], [18,25], [18,35], [18,38], [18,39], [19,24], [19,26], [19,36], [19,39], [19,40], [20,25], [20,27], [20,37], [20,40], [20,41]]

set_option maxRecDepth 12000 in
theorem sameTerms : pureFamily expected = pureFamily officialTerms := by
  decide +kernel

end PEqualNP.Outside.L_meta_9768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9768 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.L_meta_9768 : PEqualNP.MetaComplexity.HasCircuitSize 42 (fun x : Fin 42 → Bool => (x 0 && x 26) || (x 0 && x 28) || (x 0 && x 38) || (x 0 && x 41) || (x 1 && x 21) || (x 1 && x 22) || (x 1 && x 27) || (x 1 && x 29) || (x 1 && x 39) || (x 2 && x 22) || (x 2 && x 23) || (x 2 && x 28) || (x 2 && x 30) || (x 2 && x 40) || (x 3 && x 23) || (x 3 && x 24) || (x 3 && x 29) || (x 3 && x 31) || (x 3 && x 41) || (x 4 && x 21) || (x 4 && x 24) || (x 4 && x 25) || (x 4 && x 30) || (x 4 && x 32) || (x 5 && x 22) || (x 5 && x 25) || (x 5 && x 26) || (x 5 && x 31) || (x 5 && x 33) || (x 6 && x 23) || (x 6 && x 26) || (x 6 && x 27) || (x 6 && x 32) || (x 6 && x 34) || (x 7 && x 24) || (x 7 && x 27) || (x 7 && x 28) || (x 7 && x 33) || (x 7 && x 35) || (x 8 && x 25) || (x 8 && x 28) || (x 8 && x 29) || (x 8 && x 34) || (x 8 && x 36) || (x 9 && x 26) || (x 9 && x 29) || (x 9 && x 30) || (x 9 && x 35) || (x 9 && x 37) || (x 10 && x 27) || (x 10 && x 30) || (x 10 && x 31) || (x 10 && x 36) || (x 10 && x 38) || (x 11 && x 28) || (x 11 && x 31) || (x 11 && x 32) || (x 11 && x 37) || (x 11 && x 39) || (x 12 && x 29) || (x 12 && x 32) || (x 12 && x 33) || (x 12 && x 38) || (x 12 && x 40) || (x 13 && x 30) || (x 13 && x 33) || (x 13 && x 34) || (x 13 && x 39) || (x 13 && x 41) || (x 14 && x 21) || (x 14 && x 31) || (x 14 && x 34) || (x 14 && x 35) || (x 14 && x 40) || (x 15 && x 22) || (x 15 && x 32) || (x 15 && x 35) || (x 15 && x 36) || (x 15 && x 41) || (x 16 && x 21) || (x 16 && x 23) || (x 16 && x 33) || (x 16 && x 36) || (x 16 && x 37) || (x 17 && x 22) || (x 17 && x 24) || (x 17 && x 34) || (x 17 && x 37) || (x 17 && x 38) || (x 18 && x 23) || (x 18 && x 25) || (x 18 && x 35) || (x 18 && x 38) || (x 18 && x 39) || (x 19 && x 24) || (x 19 && x 26) || (x 19 && x 36) || (x 19 && x 39) || (x 19 && x 40) || (x 20 && x 25) || (x 20 && x 27) || (x 20 && x 37) || (x 20 && x 40) || (x 20 && x 41)) 124 := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · simp [witness, FanInTwo]
  · intro x
    rw [correctness, observe_same x expected officialTerms sameTerms]
    simp only [observe, officialTerms, List.any_cons, List.any_nil, List.all_cons, List.all_nil,
      Bool.and_true, Bool.or_false, Bool.and_assoc, Bool.or_assoc]
