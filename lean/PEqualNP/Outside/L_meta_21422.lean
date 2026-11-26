import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21422_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [7, 15]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [2, 11]⟩, ⟨.and, [14, 16]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [20, 19]⟩], 21⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 13 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112380 : ℕ).testBit (5 * u.val + v.val)) 13) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21422_aux

theorem PEqualNP.Outside.L_meta_21422 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112380 : ℕ).testBit (5 * u.val + v.val)) 13) := PEqualNP.Outside.L_meta_21422_aux.rep
