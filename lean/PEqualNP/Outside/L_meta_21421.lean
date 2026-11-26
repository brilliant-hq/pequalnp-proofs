import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21421_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [3, 6]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [9, 16]⟩, ⟨.and, [11, 13]⟩, ⟨.and, [15, 17]⟩, ⟨.or, [18, 19]⟩], 20⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 13 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112348 : ℕ).testBit (5 * u.val + v.val)) 13) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21421_aux

theorem PEqualNP.Outside.L_meta_21421 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112348 : ℕ).testBit (5 * u.val + v.val)) 13) := PEqualNP.Outside.L_meta_21421_aux.rep
