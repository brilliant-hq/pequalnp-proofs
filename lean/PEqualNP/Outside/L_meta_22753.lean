import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22753_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 21]⟩], 23⟩

lemma h_ok : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 14 := by decide +kernel

lemma h_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1940151 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22753_aux

theorem PEqualNP.Outside.L_meta_22753 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940151 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22753_aux.circ, PEqualNP.Outside.L_meta_22753_aux.h_ok, PEqualNP.Outside.L_meta_22753_aux.h_sz, PEqualNP.Outside.L_meta_22753_aux.h_rep⟩
