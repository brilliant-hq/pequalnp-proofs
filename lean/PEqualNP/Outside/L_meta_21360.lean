import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21360_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [7, 13]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [9, 11]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [18, 17]⟩], 19⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 12 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39293 : ℕ).testBit (5 * u.val + v.val)) 12) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21360_aux

theorem PEqualNP.Outside.L_meta_21360 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39293 : ℕ).testBit (5 * u.val + v.val)) 12) := PEqualNP.Outside.L_meta_21360_aux.rep
