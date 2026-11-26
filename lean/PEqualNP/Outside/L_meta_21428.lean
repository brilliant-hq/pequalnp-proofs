import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21428_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [15, 16]⟩, ⟨.and, [11, 13]⟩, ⟨.and, [14, 17]⟩, ⟨.or, [18, 19]⟩], 20⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 14 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112382 : ℕ).testBit (5 * u.val + v.val)) 14) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21428_aux

theorem PEqualNP.Outside.L_meta_21428 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112382 : ℕ).testBit (5 * u.val + v.val)) 14) := PEqualNP.Outside.L_meta_21428_aux.rep
