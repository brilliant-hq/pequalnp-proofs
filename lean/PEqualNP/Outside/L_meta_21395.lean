import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21395_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [6, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [14, 15]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [13, 16]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 12 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112124 : ℕ).testBit (5 * u.val + v.val)) 12) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21395_aux

theorem PEqualNP.Outside.L_meta_21395 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112124 : ℕ).testBit (5 * u.val + v.val)) 12) := PEqualNP.Outside.L_meta_21395_aux.rep
