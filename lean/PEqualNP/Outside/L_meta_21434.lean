import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21434_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 15]⟩, ⟨.and, [9, 11]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [3, 14]⟩, ⟨.and, [16, 4]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [22, 20]⟩], 23⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 15 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241598 : ℕ).testBit (5 * u.val + v.val)) 15) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21434_aux

theorem PEqualNP.Outside.L_meta_21434 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241598 : ℕ).testBit (5 * u.val + v.val)) 15) := PEqualNP.Outside.L_meta_21434_aux.rep
