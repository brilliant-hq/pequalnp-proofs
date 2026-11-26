import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25440

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ (n : ℕ) : Circuit :=
  ⟨[⟨.or, [1, n]⟩,
    ⟨.or, [0, n + 1]⟩,
    ⟨.and, [2 * n, 2 * n + 1]⟩,
    ⟨.and, [2, n + 2]⟩,
    ⟨.or, [2 * n + 2, 2 * n + 3]⟩,
    ⟨.not, [2 * n + 4]⟩],
   2 * n + 5⟩

theorem circ_fit (n : ℕ) : FanInTwo (circ n) := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem getD_append_lt {l1 l2 : List Bool} {i : ℕ} (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_ge {l1 l2 : List Bool} {i : ℕ} (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i false = l2.getD (i - l1.length) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

theorem oneEach_len {n : ℕ} (u v : Fin n) : (oneEach u v).length = 2 * n := by
  simp [oneEach]
  omega

theorem oneEach_left {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  rw [getD_append_lt (by simp; omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some,
    Fin.ext_iff]

theorem oneEach_right {n : ℕ} (u v : Fin n) (j : ℕ) (hj : j < n) :
    (oneEach u v).getD (n + j) false = decide (j = v.val) := by
  unfold oneEach
  rw [getD_append_ge (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some, Fin.ext_iff]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

theorem eval_circ {n : ℕ} (hn : 4 ≤ n) (u v : Fin n) :
    (circ n).eval (oneEach u v) =
      !(((decide (1 = u.val) || decide (0 = v.val)) &&
         (decide (0 = u.val) || decide (1 = v.val))) ||
        (decide (2 = u.val) && decide (2 = v.val))) := by
  set w0 := oneEach u v
  have h0 : w0.length = 2 * n := oneEach_len u v
  have hx0 : w0.getD 0 false = decide (0 = u.val) := oneEach_left u v 0 (by omega)
  have hx1 : w0.getD 1 false = decide (1 = u.val) := oneEach_left u v 1 (by omega)
  have hx2 : w0.getD 2 false = decide (2 = u.val) := oneEach_left u v 2 (by omega)
  have hy0 : w0.getD n false = decide (0 = v.val) := by simpa using oneEach_right u v 0 (by omega)
  have hy1 : w0.getD (n + 1) false = decide (1 = v.val) := oneEach_right u v 1 (by omega)
  have hy2 : w0.getD (n + 2) false = decide (2 = v.val) := oneEach_right u v 2 (by omega)
  set a0 := w0.getD 1 false || w0.getD n false
  set w1 := w0 ++ [a0]
  have h1 : w1.length = 2 * n + 1 := by simp [w1, h0]
  have hw1 : step w0 ⟨.or, [1, n]⟩ = w1 := by
    simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, w1, a0]
  have g1_0 : w1.getD 0 false = w0.getD 0 false := getD_append_lt (by omega)
  have g1_1 : w1.getD (n + 1) false = w0.getD (n + 1) false := getD_append_lt (by omega)
  set a1 := w0.getD 0 false || w0.getD (n + 1) false
  set w2 := w1 ++ [a1]
  have h2 : w2.length = 2 * n + 2 := by simp [w2, h1]
  have hw2 : step w1 ⟨.or, [0, n + 1]⟩ = w2 := by
    simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, g1_0, g1_1, w2, a1]
  have g2_0 : w2.getD (2 * n) false = a0 := by
    rw [getD_append_lt (by omega), getD_append_ge (by omega)]
    simp [h0]
  have g2_1 : w2.getD (2 * n + 1) false = a1 := by
    rw [getD_append_ge (by omega)]
    simp [h1]
  set a2 := a0 && a1
  set w3 := w2 ++ [a2]
  have h3 : w3.length = 2 * n + 3 := by simp [w3, h2]
  have hw3 : step w2 ⟨.and, [2 * n, 2 * n + 1]⟩ = w3 := by
    simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, g2_0, g2_1, w3, a2]
  have g3_x2 : w3.getD 2 false = w0.getD 2 false := by
    rw [getD_append_lt (by omega), getD_append_lt (by omega), getD_append_lt (by omega)]
  have g3_y2 : w3.getD (n + 2) false = w0.getD (n + 2) false := by
    rw [getD_append_lt (by omega), getD_append_lt (by omega), getD_append_lt (by omega)]
  set a3 := w0.getD 2 false && w0.getD (n + 2) false
  set w4 := w3 ++ [a3]
  have h4 : w4.length = 2 * n + 4 := by simp [w4, h3]
  have hw4 : step w3 ⟨.and, [2, n + 2]⟩ = w4 := by
    simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, g3_x2, g3_y2, w4, a3]
  have g4_0 : w4.getD (2 * n + 2) false = a2 := by
    rw [getD_append_lt (by omega), getD_append_ge (by omega)]
    simp [h2]
  have g4_1 : w4.getD (2 * n + 3) false = a3 := by
    rw [getD_append_ge (by omega)]
    simp [h3]
  set a4 := a2 || a3
  set w5 := w4 ++ [a4]
  have h5 : w5.length = 2 * n + 5 := by simp [w5, h4]
  have hw5 : step w4 ⟨.or, [2 * n + 2, 2 * n + 3]⟩ = w5 := by
    simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, g4_0, g4_1, w5, a4]
  have g5_0 : w5.getD (2 * n + 4) false = a4 := by
    rw [getD_append_ge (by omega)]
    simp [h4]
  set w6 := w5 ++ [!a4]
  have hw6 : step w5 ⟨.not, [2 * n + 4]⟩ = w6 := by
    simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.headD, g5_0, w6]
  have g6_0 : w6.getD (2 * n + 5) false = !a4 := by
    rw [getD_append_ge (by omega)]
    simp [h5]
  change (step (step (step (step (step (step w0 ⟨.or, [1, n]⟩) ⟨.or, [0, n + 1]⟩) ⟨.and, [2 * n, 2 * n + 1]⟩) ⟨.and, [2, n + 2]⟩) ⟨.or, [2 * n + 2, 2 * n + 3]⟩) ⟨.not, [2 * n + 4]⟩).getD (2 * n + 5) false = _
  rw [hw1, hw2, hw3, hw4, hw5, hw6, g6_0]
  simp only [a4, a3, a2, a1, a0, hx0, hx1, hx2, hy0, hy1, hy2]

theorem formula_eq (a b : ℕ) :
    (!(((decide (1 = a) || decide (0 = b)) &&
        (decide (0 = a) || decide (1 = b))) ||
       (decide (2 = a) && decide (2 = b)))) =
    (64478 : ℕ).testBit (4 * min a 3 + min b 3) := by
  have h1 : ∀ k : ℕ, decide (0 = k + 3) = false := fun _ => by simp
  have h2 : ∀ k : ℕ, decide (1 = k + 3) = false := fun _ => by simp
  have h3 : ∀ k : ℕ, decide (2 = k + 3) = false := fun _ => by simp
  have hm : ∀ k : ℕ, min (k + 3) 3 = 3 := fun k => Nat.min_eq_right (by omega)
  rcases a with _ | _ | _ | a <;> rcases b with _ | _ | _ | b <;>
    simp only [h1, h2, h3, hm] <;> decide

theorem circ_rep {n : ℕ} (hn : 4 ≤ n) :
    Represents (fun (u : Fin n) (v : Fin n) => (64478 : ℕ).testBit (4 * min u.val 3 + min v.val 3)) (circ n) := by
  intro u v
  rw [eval_circ hn u v]
  exact formula_eq u.val v.val

end PEqualNP.Outside.L_meta_25440

theorem PEqualNP.Outside.L_meta_25440 : ∀ n : ℕ, 4 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => (64478 : ℕ).testBit (4 * min u.val 3 + min v.val 3)) C := by
  intro n hn
  exact ⟨PEqualNP.Outside.L_meta_25440.circ n,
    PEqualNP.Outside.L_meta_25440.circ_fit n,
    by simp [PEqualNP.Outside.L_meta_25440.circ, PEqualNP.CircuitLowerBounds.Circuit.size],
    PEqualNP.Outside.L_meta_25440.circ_rep hn⟩
