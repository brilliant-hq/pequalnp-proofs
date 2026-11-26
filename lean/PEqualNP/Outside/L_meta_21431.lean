import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21431_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [15, 16]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [3, 6]⟩, ⟨.and, [13, 17]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [21, 20]⟩], 22⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 14 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241565 : ℕ).testBit (5 * u.val + v.val)) 14) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21431_aux

theorem PEqualNP.Outside.L_meta_21431 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241565 : ℕ).testBit (5 * u.val + v.val)) 14) := PEqualNP.Outside.L_meta_21431_aux.rep
