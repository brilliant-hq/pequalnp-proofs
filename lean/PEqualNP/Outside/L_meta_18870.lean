import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18870

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

private abbrev Entry := Bool × ℕ × ℕ

private def gate (flip : Bool) (r : Entry) : Gate :=
  ⟨if r.1 = flip then .and else .or, [r.2.1,r.2.2]⟩

private def rule (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def ordered (k : ℕ) : List Entry → Bool
  | [] => true
  | r :: rs => decide (r.2.1 < k ∧ r.2.2 < k) && ordered (k+1) rs

private theorem get_neg (w : List Bool) (i : ℕ) (h : i < w.length) :
    (w.map Bool.not).getD i false = !(w.getD i false) := by
  have h' : i < (w.map Bool.not).length := by simpa using h
  rw [List.getD_eq_getElem _ _ h', List.getElem_map, List.getD_eq_getElem _ _ h]

private theorem next_neg (w : List Bool) (r : Entry) (h : r.2.1 < w.length ∧ r.2.2 < w.length) :
    rule (w.map Bool.not) (gate true r) = (rule w (gate false r)).map Bool.not := by
  rcases r with ⟨b,i,j⟩
  rcases h with ⟨hi,hj⟩
  cases b <;>
    simp [rule, gate, GateOp.eval, get_neg w i hi, get_neg w j hj, Bool.not_and, Bool.not_or, -List.getD_eq_getElem?_getD, -List.getElem?_map]

private theorem fold_neg (rs : List Entry) (w : List Bool) (ok : ordered w.length rs = true) :
    (rs.map (gate true)).foldl rule (w.map Bool.not) =
      ((rs.map (gate false)).foldl rule w).map Bool.not := by
  induction rs generalizing w with
  | nil => rfl
  | cons r rs ih =>
    have ⟨h, rest⟩ : (r.2.1 < w.length ∧ r.2.2 < w.length) ∧
        ordered (w.length + 1) rs = true := by simpa [ordered] using ok
    simp only [List.map_cons, List.foldl_cons]
    rw [next_neg w r h, ih _ (by simpa [rule] using rest)]

private theorem length_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl rule w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [rule, ih, Nat.add_assoc, Nat.add_comm 1]

private def baseCircuit (rs : List Entry) (out : ℕ) : Circuit := ⟨rs.map (gate false),out⟩

private def answer (n : ℕ) (rs : List Entry) (out : ℕ) : Circuit :=
  ⟨rs.map (gate true) ++ [⟨.not, [out]⟩], n+rs.length⟩

private theorem output_matches {n : ℕ} (rs : List Entry) (out : ℕ)
    (well : ordered n rs = true) (live : out < n + rs.length) (x : Fin n → Bool) :
    (answer n rs out).eval (List.ofFn x) =
      (baseCircuit rs out).eval (List.ofFn fun i => !(x i)) := by
  let w := List.ofFn (fun i => !(x i))
  let a := (rs.map (gate false)).foldl rule w
  have inputs : w.map Bool.not = List.ofFn x := by simp [w, List.map_ofFn, Function.comp_def]
  have len : a.length = n + rs.length := by simp [a, length_fold, w]
  have run := fold_neg rs w (by simpa [w] using well)
  rw [inputs] at run
  have stop : (a.map Bool.not).length = n+rs.length := by simp [len]
  have value : (a.map Bool.not).getD out false = !(a.getD out false) :=
    get_neg a out (by omega)
  simp only [answer, Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (rule ((rs.map (gate true)).foldl rule (List.ofFn x)) ⟨.not,[out]⟩).getD
    (n+rs.length) false = a.getD out false
  change _ = a.map Bool.not at run
  rw [run, ← stop]
  -- The last gate reads the original output before appending its negation.
  change ((a.map Bool.not) ++ [!((a.map Bool.not).getD out false)]).getD
    (a.map Bool.not).length false = a.getD out false
  rw [value, Bool.not_not]
  have snoc (ws : List Bool) (y : Bool) : (ws ++ [y]).getD ws.length false = y := by
    simp [List.getD_eq_getElem?_getD]
  exact snoc _ _

private theorem base_ok (rs : List Entry) (out : ℕ) :
    ∀ g ∈ (baseCircuit rs out).gates, g.op = .and ∨ g.op = .or := by
  intro g h
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp h
  cases h : r.1 <;> simp [gate, h]

private theorem answer_ok (n : ℕ) (rs : List Entry) (out : ℕ) :
    FanInTwo (answer n rs out) := by
  intro g h
  change g ∈ rs.map (gate true) ++ _ at h
  rcases List.mem_append.mp h with hp | hs
  · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
    cases h : r.1 <;> simp [gate, h]
  · have same : g = ⟨.not,[out]⟩ := List.mem_singleton.mp hs
    subst g
    simp

private def instructions : List Entry := [
  (false, 1, 5),
  (false, 2, 6),
  (false, 3, 7),
  (false, 4, 8),
  (true, 15, 16),
  (true, 17, 18),
  (true, 19, 20),
  (false, 0, 21),
  (false, 1, 2),
  (false, 5, 6),
  (false, 10, 12),
  (false, 11, 13),
  (true, 23, 24),
  (true, 25, 26),
  (true, 27, 28),
  (false, 9, 29),
  (false, 3, 4),
  (false, 7, 8),
  (false, 10, 11),
  (false, 12, 13),
  (true, 31, 32),
  (true, 33, 34),
  (true, 35, 36),
  (false, 14, 37),
  (false, 3, 10),
  (false, 4, 11),
  (true, 39, 40),
  (false, 1, 41),
  (false, 3, 12),
  (false, 4, 13),
  (true, 43, 44),
  (false, 2, 45),
  (false, 7, 10),
  (false, 8, 11),
  (true, 47, 48),
  (false, 5, 49),
  (false, 7, 12),
  (false, 8, 13),
  (true, 51, 52),
  (false, 6, 53),
  (true, 50, 54),
  (true, 46, 55),
  (true, 42, 56),
  (true, 38, 57),
  (true, 30, 58),
  (true, 22, 59)
]
private def expected : Terms 15 := [[0,1,5],[0,2,6],[0,3,7],[0,4,8],[1,2,9],[1,3,10],[1,4,11],[2,3,12],[2,4,13],[3,4,14],[5,6,9],[5,7,10],[5,8,11],[6,7,12],[6,8,13],[7,8,14],[9,10,12],[9,11,13],[10,11,14],[12,13,14]]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
private theorem correspondence :
    pureFamily (circuitTerms 15 (baseCircuit instructions 60)) = pureFamily expected := by decide +kernel

end PEqualNP.Outside.L_meta_18870

open PEqualNP.Outside.L_meta_18870 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.L_meta_18870 : PEqualNP.MetaComplexity.HasCircuitSize 15 (fun x : Fin 15 → Bool => (!(x 0) && !(x 1) && !(x 5)) || (!(x 0) && !(x 2) && !(x 6)) || (!(x 0) && !(x 3) && !(x 7)) || (!(x 0) && !(x 4) && !(x 8)) || (!(x 1) && !(x 2) && !(x 9)) || (!(x 1) && !(x 3) && !(x 10)) || (!(x 1) && !(x 4) && !(x 11)) || (!(x 2) && !(x 3) && !(x 12)) || (!(x 2) && !(x 4) && !(x 13)) || (!(x 3) && !(x 4) && !(x 14)) || (!(x 5) && !(x 6) && !(x 9)) || (!(x 5) && !(x 7) && !(x 10)) || (!(x 5) && !(x 8) && !(x 11)) || (!(x 6) && !(x 7) && !(x 12)) || (!(x 6) && !(x 8) && !(x 13)) || (!(x 7) && !(x 8) && !(x 14)) || (!(x 9) && !(x 10) && !(x 12)) || (!(x 9) && !(x 11) && !(x 13)) || (!(x 10) && !(x 11) && !(x 14)) || (!(x 12) && !(x 13) && !(x 14))) 49 := by
  refine ⟨answer 15 instructions 60, answer_ok _ _ _, by decide, ?_⟩
  intro x
  rw [output_matches _ _ (by decide) (by decide), ← circuitMatches _ _ (base_ok _ _),
    observe_same _ _ _ correspondence]
  simp only [observe, expected, List.any_cons, List.any_nil, List.all_cons, List.all_nil,
    Bool.and_true, Bool.or_false, Bool.and_assoc, Bool.or_assoc]
