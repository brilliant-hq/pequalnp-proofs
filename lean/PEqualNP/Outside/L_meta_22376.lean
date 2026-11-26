import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22376_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [5, 15]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [12, 14]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [21, 20]⟩], 22⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 13 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841714 : ℕ).testBit (6 * u.val + v.val)) 13) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22376_aux

theorem PEqualNP.Outside.L_meta_22376 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841714 : ℕ).testBit (6 * u.val + v.val)) 13) := PEqualNP.Outside.L_meta_22376_aux.rep
