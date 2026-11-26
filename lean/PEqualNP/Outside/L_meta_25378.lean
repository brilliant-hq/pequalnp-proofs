import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25378

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [5, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [8, 13]⟩], 14⟩

theorem shape : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem nine_gate_bound : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6374551 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨circuit, shape, ?_, ?_⟩
  · decide
  · decide +kernel

end PEqualNP.Outside.L_meta_25378

theorem PEqualNP.Outside.L_meta_25378 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6374551 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  obtain ⟨C, hshape, hsize, hcomputes⟩ := PEqualNP.Outside.L_meta_25378.nine_gate_bound
  exact ⟨C, hshape, Nat.le_trans hsize (by decide), hcomputes⟩
