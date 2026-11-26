import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21359_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [7, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [3, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [18, 4]⟩], 19⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 11 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (257917 : ℕ).testBit (5 * u.val + v.val)) 11) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21359_aux

theorem PEqualNP.Outside.L_meta_21359 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (257917 : ℕ).testBit (5 * u.val + v.val)) 11) := PEqualNP.Outside.L_meta_21359_aux.rep
