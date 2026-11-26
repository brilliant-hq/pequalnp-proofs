import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22253_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [14, 15]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [10, 12]⟩, ⟨.and, [13, 16]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [20, 19]⟩], 21⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 13 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816762 : ℕ).testBit (6 * u.val + v.val)) 13) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22253_aux

theorem PEqualNP.Outside.L_meta_22253 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816762 : ℕ).testBit (6 * u.val + v.val)) 13) := PEqualNP.Outside.L_meta_22253_aux.rep
