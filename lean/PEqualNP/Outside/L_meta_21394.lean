import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21394_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [8, 14]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [12, 4]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [19, 18]⟩], 20⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 12 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112093 : ℕ).testBit (5 * u.val + v.val)) 12) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21394_aux

theorem PEqualNP.Outside.L_meta_21394 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112093 : ℕ).testBit (5 * u.val + v.val)) 12) := PEqualNP.Outside.L_meta_21394_aux.rep
