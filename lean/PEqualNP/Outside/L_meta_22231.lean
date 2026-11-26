import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22231_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [11, 16]⟩, ⟨.and, [12, 14]⟩, ⟨.and, [15, 17]⟩, ⟨.or, [4, 18]⟩, ⟨.or, [20, 19]⟩], 21⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 12 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849917 : ℕ).testBit (6 * u.val + v.val)) 12) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22231_aux

theorem PEqualNP.Outside.L_meta_22231 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849917 : ℕ).testBit (6 * u.val + v.val)) 12) := PEqualNP.Outside.L_meta_22231_aux.rep
