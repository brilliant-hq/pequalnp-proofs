import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22757_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 21]⟩], 22⟩

lemma h_ok : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 14 := by decide +kernel

lemma h_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1940414 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22757_aux

theorem PEqualNP.Outside.L_meta_22757 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940414 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22757_aux.circ, PEqualNP.Outside.L_meta_22757_aux.h_ok, PEqualNP.Outside.L_meta_22757_aux.h_sz, PEqualNP.Outside.L_meta_22757_aux.h_rep⟩
