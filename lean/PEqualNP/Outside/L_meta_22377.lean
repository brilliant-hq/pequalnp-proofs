import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22377_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [12, 16]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [20, 4]⟩, ⟨.or, [21, 19]⟩], 22⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 13 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841717 : ℕ).testBit (6 * u.val + v.val)) 13) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22377_aux

theorem PEqualNP.Outside.L_meta_22377 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841717 : ℕ).testBit (6 * u.val + v.val)) 13) := PEqualNP.Outside.L_meta_22377_aux.rep
