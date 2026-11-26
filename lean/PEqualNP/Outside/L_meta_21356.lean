import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21356_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [1, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [12, 15]⟩, ⟨.or, [16, 4]⟩, ⟨.or, [18, 17]⟩], 19⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 11 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241141 : ℕ).testBit (5 * u.val + v.val)) 11) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21356_aux

theorem PEqualNP.Outside.L_meta_21356 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241141 : ℕ).testBit (5 * u.val + v.val)) 11) := PEqualNP.Outside.L_meta_21356_aux.rep
