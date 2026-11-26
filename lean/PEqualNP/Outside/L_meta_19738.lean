import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19738

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [22, 15]⟩, ⟨.or, [23, 17]⟩, ⟨.and, [0, 24]⟩, ⟨.or, [15, 20]⟩, ⟨.and, [1, 26]⟩, ⟨.or, [11, 20]⟩, ⟨.and, [2, 28]⟩, ⟨.or, [14, 20]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [32, 19]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [8, 21]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [13, 21]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [39, 18]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [25, 27]⟩, ⟨.or, [42, 29]⟩, ⟨.or, [43, 31]⟩, ⟨.or, [44, 34]⟩, ⟨.or, [45, 36]⟩, ⟨.or, [46, 38]⟩, ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 33 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun u v : Fin 8 => (8857115674703410590 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19738

theorem PEqualNP.Outside.L_meta_19738 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8857115674703410590 : ℕ).testBit (8 * u.val + v.val)) 33) :=
  ⟨PEqualNP.Outside.L_meta_19738.witness, PEqualNP.Outside.L_meta_19738.mono, PEqualNP.Outside.L_meta_19738.small, PEqualNP.Outside.L_meta_19738.rep⟩
