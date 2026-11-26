import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21320_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [8, 14]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [16, 17]⟩], 18⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 11 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (104219 : ℕ).testBit (5 * u.val + v.val)) 11) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21320_aux

theorem PEqualNP.Outside.L_meta_21320 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (104219 : ℕ).testBit (5 * u.val + v.val)) 11) := PEqualNP.Outside.L_meta_21320_aux.rep
