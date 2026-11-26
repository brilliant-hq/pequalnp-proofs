import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21146_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [1, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [11, 14]⟩, ⟨.and, [9, 15]⟩, ⟨.or, [16, 17]⟩], 18⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 10 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39385 : ℕ).testBit (5 * u.val + v.val)) 10) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21146_aux

theorem PEqualNP.Outside.L_meta_21146 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39385 : ℕ).testBit (5 * u.val + v.val)) 10) := PEqualNP.Outside.L_meta_21146_aux.rep
