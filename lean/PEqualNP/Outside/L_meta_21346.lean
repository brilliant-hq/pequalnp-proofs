import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21346
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.or, [0, 2]⟩,
  ⟨.or, [1, 6]⟩,
  ⟨.or, [10, 5]⟩,
  ⟨.or, [6, 8]⟩,
  ⟨.and, [9, 13]⟩,
  ⟨.or, [14, 4]⟩,
  ⟨.or, [11, 7]⟩,
  ⟨.or, [16, 3]⟩,
  ⟨.and, [12, 17]⟩,
  ⟨.or, [15, 18]⟩], 19⟩

lemma mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21346

open PEqualNP.Outside.L_meta_21346 in
theorem PEqualNP.Outside.L_meta_21346 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112381 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨witness, mono, by decide, by decide +kernel⟩
