import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21323_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [9, 11]⟩, ⟨.and, [2, 12]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [18, 17]⟩], 19⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 11 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (104283 : ℕ).testBit (5 * u.val + v.val)) 11) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21323_aux

theorem PEqualNP.Outside.L_meta_21323 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (104283 : ℕ).testBit (5 * u.val + v.val)) 11) := PEqualNP.Outside.L_meta_21323_aux.rep
