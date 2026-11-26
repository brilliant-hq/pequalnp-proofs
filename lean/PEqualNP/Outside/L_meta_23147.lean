import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23147_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 17]⟩], 18⟩

lemma h_ok : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 10 := by decide +kernel

lemma h_rep : Represents (fun (u : Fin 3) (v : Fin 6) => (16254 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_23147_aux

theorem PEqualNP.Outside.L_meta_23147 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (16254 : ℕ).testBit (6 * u.val + v.val)) 10)  := by
  exact ⟨PEqualNP.Outside.L_meta_23147_aux.circ, PEqualNP.Outside.L_meta_23147_aux.h_ok, PEqualNP.Outside.L_meta_23147_aux.h_sz, PEqualNP.Outside.L_meta_23147_aux.h_rep⟩
