import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21348_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [10, 15]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [14, 16]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 11 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112542 : ℕ).testBit (5 * u.val + v.val)) 11) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21348_aux

theorem PEqualNP.Outside.L_meta_21348 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112542 : ℕ).testBit (5 * u.val + v.val)) 11) := PEqualNP.Outside.L_meta_21348_aux.rep
