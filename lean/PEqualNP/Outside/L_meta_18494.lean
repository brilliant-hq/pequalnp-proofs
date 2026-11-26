import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18494

open PEqualNP.CircuitLowerBounds

private def wireDominates (xs ys : List Bool) : Prop :=
  xs.length = ys.length ∧ ∀ i, xs.getD i false = true → ys.getD i false = true

private theorem getD_snoc (ws : List Bool) (b : Bool) (i : ℕ) :
    (ws ++ [b]).getD i false = if i = ws.length then b else ws.getD i false := by
  by_cases hi : i < ws.length
  · rw [List.getD_append _ _ _ _ hi, ite_eq_right (ne_of_lt hi)]
  by_cases he : i = ws.length
  · subst i
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right he, List.getD_eq_default _ _ (by simp; omega),
       List.getD_eq_default _ _ (by omega)]

private theorem snoc_extends {xs ys : List Bool} {a b : Bool}
    (h : wireDominates xs ys) (hab : a = true → b = true) :
    wireDominates (xs ++ [a]) (ys ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  rw [getD_snoc, ← h.1]
  rw [getD_snoc] at hi
  split_ifs at hi ⊢
  · exact hab hi
  · exact h.2 i hi

private theorem gate_extends {g : Gate} (hop : g.op = .and ∨ g.op = .or)
    {xs ys : List Bool} (h : wireDominates xs ys) :
    g.op.eval (g.inputs.map (fun i => xs.getD i false)) = true →
    g.op.eval (g.inputs.map (fun i => ys.getD i false)) = true := by
  rcases hop with e | e
  · simpa only [e, GateOp.eval, List.all_map, Function.comp_apply, id_eq, List.all_eq_true]
      using (fun ha (i : ℕ) (hi : i ∈ g.inputs) => h.2 i (ha i hi) :
        (∀ i ∈ g.inputs, xs.getD i false = true) → (∀ i ∈ g.inputs, ys.getD i false = true))
  · simpa only [e, GateOp.eval, List.any_map, Function.comp_apply, id_eq, List.any_eq_true]
      using (fun ⟨i, hi, ha⟩ => ⟨i, hi, h.2 i ha⟩ :
        (∃ i ∈ g.inputs, xs.getD i false = true) → (∃ i ∈ g.inputs, ys.getD i false = true))

private theorem fold_extends (gs : List Gate) {xs ys : List Bool}
    (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (h : wireDominates xs ys) :
    wireDominates (gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) xs)
      (gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun k hk => ops k (List.mem_cons_of_mem _ hk))
      (snoc_extends h (gate_extends (ops g (by simp)) h))

open PEqualNP.MetaComplexity

abbrev Input := Fin 10 → Bool

def yes : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640]
def no : List ℕ := [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]
def yesEven := yes.filter fun m => !m.testBit 0
def clip (m : ℕ) (b : Bool) : Input :=
  Function.update (fun j : Fin 10 => m.testBit j.val) 0 (m.testBit 0 && b)

def goal (x : Input) : Bool := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def lower (x : Input) : Bool := yesEven.any fun m => decide (clip m false ≤ x)
def upper (x : Input) : Bool := no.any fun m => decide (x ≤ clip m false)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 50000000 in
theorem covered (x : Input) (z : x 0 = false) :
    (goal x = true → lower x = true) ∧ (goal x = false → upper x = true) := by
  exact (by decide +kernel : ∀ y : Input, y 0 = false →
    (goal y = true → lower y = true) ∧ (goal y = false → upper y = true)) x z

theorem clipWeak (m : ℕ) (b : Bool) : clip m false ≤ clip m b := by
  intro j
  by_cases e : j = 0
  · subst j
    simp [clip]
  · simp [clip, Function.update_of_ne e]

theorem up {a b : Bool} (le : a ≤ b) (ha : a = true) : b = true := by
  cases a <;> cases b <;> simp_all
  exact (by decide : ¬ (true : Bool) ≤ false) le

theorem upward (C : Circuit) (fit : Monotone2 C) {x y : Input} (le : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  have ops : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (fit g hg).1
  have support : wireDominates (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases ok : i < 10
    · have xOk : i < (List.ofFn x).length := by simpa only [List.length_ofFn] using ok
      have yOk : i < (List.ofFn y).length := by simpa only [List.length_ofFn] using ok
      rw [List.getD_eq_getElem _ _ xOk, List.getElem_ofFn] at hi
      rw [List.getD_eq_getElem _ _ yOk, List.getElem_ofFn]
      exact up (le ⟨i, ok⟩) hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      cases hi
  exact (fold_extends C.gates ops support).2 C.output

end PEqualNP.Outside.L_meta_18494

open PEqualNP.Outside.L_meta_18494 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_18494 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ → Bool), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ x4 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], x1.eval (List.ofFn (Function.update (fun (x6 : Fin (10 : ℕ)) => x4.testBit ↑x6) (0 : Fin (10 : ℕ)) (x4.testBit (0 : ℕ) && x2 x4))) = Bool.true) → (∀ x5 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], x1.eval (List.ofFn (Function.update (fun (x7 : Fin (10 : ℕ)) => x5.testBit ↑x7) (0 : Fin (10 : ℕ)) (x5.testBit (0 : ℕ) && x2 x5))) = Bool.false) → ∀ (x6 : Fin (10 : ℕ) → Bool), x6 (0 : Fin (10 : ℕ)) = Bool.false → x1.eval (List.ofFn x6) = (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x6 := by
  intro C sel fit
  change (∀ m ∈ yes, C.eval (List.ofFn (clip m (sel m))) = true) →
    (∀ m ∈ no, C.eval (List.ofFn (clip m (sel m))) = false) →
    ∀ x : Input, x 0 = false → C.eval (List.ofFn x) = goal x
  intro hy hn x z
  rcases covered x z with ⟨pos, neg⟩
  cases h : goal x
  · obtain ⟨m, mem, cmp⟩ := List.any_eq_true.mp (neg h)
    have le : x ≤ clip m false := of_decide_eq_true cmp
    cases actual : C.eval (List.ofFn x)
    · rfl
    · have larger := upward C fit (le.trans (clipWeak m (sel m))) actual
      cases (hn m mem).symm.trans larger
  · obtain ⟨m, mem, cmp⟩ := List.any_eq_true.mp (pos h)
    have le : clip m false ≤ x := of_decide_eq_true cmp
    obtain ⟨hyM, even⟩ := List.mem_filter.mp mem
    have bit : m.testBit 0 = false := by simpa using even
    have atProbe : C.eval (List.ofFn (clip m false)) = true := by simpa [clip, bit] using hy m hyM
    exact upward C fit le atProbe
