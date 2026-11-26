import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20850_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def graph (u v : Fin 5) : Bool := (25957441 : ℕ).testBit (5 * u.val + v.val)

def witness : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [2, 12]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [17, 13]⟩, ⟨.or, [18, 16]⟩], 19⟩

theorem upper : RepSizeAtMost graph 10 := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  simp [Monotone2, witness, Set.mem_insert_iff, Set.mem_singleton_iff]

end PEqualNP.Outside.L_meta_20850_aux

theorem PEqualNP.Outside.L_meta_20850 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (25957441 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact PEqualNP.Outside.L_meta_20850_aux.upper
