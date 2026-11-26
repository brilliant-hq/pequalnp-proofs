import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25262

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[⟨GateOp.not, [3]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [2, 1]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [8, 12]⟩, ⟨GateOp.or, [7, 13]⟩], 14⟩

theorem shape : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem nine_gate_bound : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50871 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨circuit, shape, ?_, ?_⟩
  · decide
  · decide +kernel

end PEqualNP.Outside.L_meta_25262

theorem PEqualNP.Outside.L_meta_25262 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50871 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  obtain ⟨C, hshape, hsize, hcomputes⟩ := PEqualNP.Outside.L_meta_25262.nine_gate_bound
  exact ⟨C, hshape, Nat.le_trans hsize (by decide), hcomputes⟩
