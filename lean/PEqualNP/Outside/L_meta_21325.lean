import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21325_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [1, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [8, 14]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [16, 17]⟩], 18⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 11 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (104285 : ℕ).testBit (5 * u.val + v.val)) 11) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21325_aux

theorem PEqualNP.Outside.L_meta_21325 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (104285 : ℕ).testBit (5 * u.val + v.val)) 11) := PEqualNP.Outside.L_meta_21325_aux.rep
