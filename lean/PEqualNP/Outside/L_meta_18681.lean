import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18681

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.BlindGate

def push (D : Circuit) (op : GateOp) (i j : ℕ) : Circuit :=
  ⟨D.gates ++ [⟨op,[i,j]⟩], D.output⟩

def Good (n : ℕ) (D : Circuit) : Prop :=
  IsAO2 n D ∧ ∀ g ∈ D.gates, g.inputs.Nodup

theorem sz (D : Circuit) (op : GateOp) (i j : ℕ) : (push D op i j).size = D.size+1 := by
  simp [push,Circuit.size]

theorem valid (n : ℕ) (D : Circuit) (op : GateOp) (i j : ℕ) (hD : Good n D)
    (hop : op = .and ∨ op = .or) (hi : i < n+D.size) (hj : j < n+D.size) (hij : i ≠ j) :
    Good n (push D op i j) := by
  obtain ⟨⟨ha,hb,hc⟩,hd⟩ := hD
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro g hg
    simp only [push,List.mem_append,List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact ha g hg
    · exact hop
  · intro t ht u hu
    by_cases het : t < D.gates.length
    · change u ∈ ((D.gates ++ [_]).getD t _).inputs at hu
      rw [getD_ltz _ _ _ _ het] at hu
      exact hb t het u hu
    · have e : t = D.gates.length := by change t < (D.gates ++ [_]).length at ht; simp at ht; omega
      subst t
      change u ∈ ((D.gates ++ [_]).getD D.gates.length _).inputs at hu
      rw [getD_at'] at hu
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
      rcases hu with rfl | rfl
      · exact hi
      · exact hj
  · intro g hg
    simp only [push,List.mem_append,List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hc g hg
    · rfl
  · intro g hg
    simp only [push,List.mem_append,List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hd g hg
    · simpa using hij


end PEqualNP.Outside.L_meta_18681

open PEqualNP.Outside.L_meta_18681 PEqualNP.CircuitLowerBounds PEqualNP.BlindGate in
theorem PEqualNP.Outside.L_meta_18681 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 ∈ x2.gates, x6.inputs.Nodup) → x3 < x1 + x2.size → x4 < x1 + x2.size → x3 ≠ x4 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), x10.size = x2.size + (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 x1 x10 ∧ (∀ x11 ∈ x10.gates, x11.inputs.Nodup) ∧ ∀ (x11 : Fin x1 → Bool), (∀ x12 < x1 + x2.size, PEqualNP.BlindGate.wireValue x10 x1 x11 x12 = PEqualNP.BlindGate.wireValue x2 x1 x11 x12) ∧ PEqualNP.BlindGate.wireValue x10 x1 x11 (x1 + x2.size) = (PEqualNP.BlindGate.wireValue x2 x1 x11 x3 || PEqualNP.BlindGate.wireValue x2 x1 x11 x4) := by
  intro n C i j hc hd hi hj hij
  have ok := valid n C .or i j ⟨hc,hd⟩ (Or.inr rfl) hi hj hij
  refine ⟨push C .or i j, sz C .or i j, ok.1, ok.2, ?_⟩
  intro x
  constructor
  · intro w hw
    change (run (C.gates ++ [_]) (List.ofFn x)).getD w false = (run C.gates (List.ofFn x)).getD w false
    apply run_prefix
    simpa [Circuit.size] using hw
  · change (run (C.gates ++ [_]) (List.ofFn x)).getD (n+C.size) false = _
    rw [run_snoc, show n+C.size = (run C.gates (List.ofFn x)).length by simp [run_length,Circuit.size], getD_at]
    change GateOp.or.eval [wireValue C n x i, wireValue C n x j] = _
    simp [GateOp.eval]
