import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20854_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def graph (u v : Fin 5) : Bool := (27004993 : ℕ).testBit (5 * u.val + v.val)

def witness : Circuit := ⟨[⟨.and, [6, 1]⟩, ⟨.and, [7, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [17, 13]⟩, ⟨.or, [18, 16]⟩], 19⟩

theorem upper : RepSizeAtMost graph 10 := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  simp [Monotone2, witness, Set.mem_insert_iff, Set.mem_singleton_iff]

end PEqualNP.Outside.L_meta_20854_aux

theorem PEqualNP.Outside.L_meta_20854 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (27004993 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact PEqualNP.Outside.L_meta_20854_aux.upper
