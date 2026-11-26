import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21370_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [19, 18]⟩], 20⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 12 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103678 : ℕ).testBit (5 * u.val + v.val)) 12) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21370_aux

theorem PEqualNP.Outside.L_meta_21370 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103678 : ℕ).testBit (5 * u.val + v.val)) 12) := PEqualNP.Outside.L_meta_21370_aux.rep
