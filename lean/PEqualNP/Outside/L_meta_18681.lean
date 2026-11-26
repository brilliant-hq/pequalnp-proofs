import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18681

open PEqualNP.CircuitLowerBounds

def WF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len_fold : ∀ (gs : List Gate) (w : List Bool), (gs.foldl WF w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp [WF]; omega

theorem getD_pre (L A : List Bool) (i : ℕ) (h : i < L.length) : (L ++ A).getD i false = L.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

end PEqualNP.Outside.L_meta_18681

open PEqualNP.Outside.L_meta_18681 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18681 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 ∈ x2.gates, x6.inputs.Nodup) → x3 < x1 + x2.size → x4 < x1 + x2.size → x3 ≠ x4 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), x10.size = x2.size + (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 x1 x10 ∧ (∀ x11 ∈ x10.gates, x11.inputs.Nodup) ∧ ∀ (x11 : Fin x1 → Bool), (∀ x12 < x1 + x2.size, PEqualNP.BlindGate.wireValue x10 x1 x11 x12 = PEqualNP.BlindGate.wireValue x2 x1 x11 x12) ∧ PEqualNP.BlindGate.wireValue x10 x1 x11 (x1 + x2.size) = (PEqualNP.BlindGate.wireValue x2 x1 x11 x3 || PEqualNP.BlindGate.wireValue x2 x1 x11 x4) := by
  intro n C a b hC hnd ha hb hab
  let g : Gate := ⟨GateOp.or, [a, b]⟩
  let D : Circuit := ⟨C.gates ++ [g], C.output⟩
  have hw : ∀ x : Fin n → Bool, D.wires (List.ofFn x) = WF (C.wires (List.ofFn x)) g := by
    intro x
    show (C.gates ++ [g]).foldl WF _ = WF (C.gates.foldl WF _) g
    rw [List.foldl_append]; rfl
  have hl : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).length = n + C.size := by
    intro x
    show (C.gates.foldl WF _).length = _
    rw [len_fold]; simp [Circuit.size]
  refine ⟨D, by simp [D, Circuit.size], ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact hC.1 g' h
    · simp at h; subst h; right; rfl
  · intro j hj i hi
    simp only [D, List.length_append, List.length_singleton] at hj
    by_cases hjs : j < C.gates.length
    · have e : PEqualNP.MetaComplexity.NestedCover.gateAt D j = PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, D]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hjs]
      rw [e] at hi
      exact hC.2.1 j hjs i hi
    · have hj' : j = C.gates.length := by omega
      have e : PEqualNP.MetaComplexity.NestedCover.gateAt D j = g := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, D, hj']
        simp
      rw [e] at hi
      simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
      simp only [Circuit.size] at ha hb
      rcases hi with rfl | rfl <;> omega
  · intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact hC.2.2 g' h
    · simp at h; subst h; rfl
  · intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact hnd g' h
    · simp at h; subst h; simp [g, hab]
  · intro x
    refine ⟨?_, ?_⟩
    · intro i hi
      simp only [PEqualNP.BlindGate.wireValue]
      rw [hw x]
      exact getD_pre _ _ i (by rw [hl x]; exact hi)
    · simp only [PEqualNP.BlindGate.wireValue]
      rw [hw x]
      simp only [WF]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hl x])]
      simp [hl x, g, GateOp.eval]
